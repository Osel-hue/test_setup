/* $Id$ */


/*
 *   Copyright (c) 2001-2010 Aaron Turner <aturner at synfin dot net>
 *   Copyright (c) 2013-2022 Fred Klassen <tcpreplay at appneta dot com> - AppNeta
 *
 *   The Tcpreplay Suite of tools is free software: you can redistribute it 
 *   and/or modify it under the terms of the GNU General Public License as 
 *   published by the Free Software Foundation, either version 3 of the 
 *   License, or with the authors permission any later version.
 *
 *   The Tcpreplay Suite is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with the Tcpreplay Suite.  If not, see <http://www.gnu.org/licenses/>.
 */
#include <unistd.h> //osel
#include "config.h"
#include "defines.h"
#include "common.h"

#include <sys/time.h>
#include <sys/types.h>
#include <signal.h>
#include <string.h>
#include <netinet/in.h>
#include <errno.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>

#include "tcpreplay_api.h"
#include "timestamp_trace.h"
#include "../lib/sll.h"

#ifdef HAVE_NETMAP
#ifdef HAVE_SYS_POLL_H
#include <sys/poll.h>
#endif
#include <sys/ioctl.h>
#include <net/netmap.h>
#include <net/netmap_user.h>
#endif /* HAVE_NETMAP */

#ifdef TCPREPLAY

#ifdef TCPREPLAY_EDIT
#include "tcpreplay_edit_opts.h"
#include "tcpedit/tcpedit.h"
extern tcpedit_t *tcpedit;
#else
#include "tcpreplay_opts.h"
#endif /* TCPREPLAY_EDIT */

#endif /* TCPREPLAY */

#include "send_packets.h"
#include "sleep.h"

#include <netinet/in.h>
#include <netinet/if_ether.h>


#ifdef DEBUG
extern int debug;
#endif

static void calc_sleep_time(tcpreplay_t *ctx, struct timeval *pkt_time,
        struct timeval *last, COUNTER len,
        sendpacket_t *sp, COUNTER counter, timestamp_t *sent_timestamp,
        COUNTER start_us, COUNTER *skip_length);
static void tcpr_sleep(tcpreplay_t *ctx, sendpacket_t *sp _U_,
        struct timespec *nap_this_time, struct timeval *now);
static u_char *get_next_packet(tcpreplay_t *ctx, pcap_t *pcap,
        struct pcap_pkthdr *pkthdr,
        int file_idx,
        packet_cache_t **prev_packet);
static uint32_t get_user_count(tcpreplay_t *ctx, sendpacket_t *sp, COUNTER counter);

static inline void wake_send_queues(sendpacket_t *sp _U_,
		tcpreplay_opt_t *options _U_)
{
#ifdef HAVE_NETMAP
    if (options->netmap)
        ioctl(sp->handle.fd, NIOCTXSYNC, NULL);   /* flush TX buffer */
#endif
}

static inline int
fast_edit_packet(struct pcap_pkthdr *pkthdr, u_char **pktdata,
        COUNTER iteration, bool cached, int datalink)
{
    uint32_t pkt_len = pkthdr->caplen;
    u_char *packet = *pktdata;
    ipv4_hdr_t *ip_hdr = NULL;
    ipv6_hdr_t *ip6_hdr = NULL;
    uint32_t src_ip, dst_ip;
    uint32_t src_ip_orig, dst_ip_orig;
    uint32_t _U_ vlan_offset;
    uint16_t ether_type;
    uint32_t l2offset;
    uint32_t l2len;
    int res;

   //dbgx(2, "How the packet looks like: %u", packet);

    res = get_l2len_protocol(packet,
                             pkt_len,
                             datalink,
                             &ether_type,
                             &l2len,
                             &l2offset,
                             &vlan_offset);

    if (res < 0)
        return res;

    assert(l2len > 0);

    switch (ether_type) {
    case ETHERTYPE_IP:
        if (pkt_len < (bpf_u_int32)(l2len + sizeof(ipv4_hdr_t))) {
            dbgx(1, "IP packet too short for Unique IP feature: %u", pkthdr->caplen);
            return -1;
        }
        ip_hdr = (ipv4_hdr_t *)(packet + l2len);
        src_ip_orig = src_ip = ntohl(ip_hdr->ip_src.s_addr);
        dst_ip_orig = dst_ip = ntohl(ip_hdr->ip_dst.s_addr);
        break;

    case ETHERTYPE_IP6:
        if (pkt_len < (bpf_u_int32)(l2len + sizeof(ipv6_hdr_t))) {
            dbgx(1, "IP6 packet too short for Unique IP feature: %u", pkthdr->caplen);
            return -1;
        }
        ip6_hdr = (ipv6_hdr_t *)(packet + l2len);
        src_ip_orig = src_ip = ntohl(ip6_hdr->ip_src.__u6_addr.__u6_addr32[3]);
        dst_ip_orig = dst_ip = ntohl(ip6_hdr->ip_dst.__u6_addr.__u6_addr32[3]);
        break;

    default:
        return -1; /* non-IP or packet too short */
    }

    dbgx(2, "Layer 3 protocol type is: 0x%04x", ether_type);

    /* swap src/dst IP's in a manner that does not affect CRC */
    if ((!cached && dst_ip > src_ip) ||
            (cached && (dst_ip - iteration) > (src_ip - 1 - iteration))) {
        if (cached) {
            --src_ip;
            ++dst_ip;
        } else {
            src_ip -= iteration;
            dst_ip += iteration;
        }

        /* CRC compensations  for wrap conditions */
        if (src_ip > src_ip_orig && dst_ip > dst_ip_orig) {
            dbgx(1, "dst_ip > src_ip(" COUNTER_SPEC "): before(1) src_ip=0x%08x dst_ip=0x%08x", iteration, src_ip, dst_ip);
            --src_ip;
            dbgx(1, "dst_ip > src_ip(" COUNTER_SPEC "): after(1)  src_ip=0x%08x dst_ip=0x%08x", iteration, src_ip, dst_ip);
        } else if (dst_ip < dst_ip_orig && src_ip < src_ip_orig) {
            dbgx(1, "dst_ip > src_ip(" COUNTER_SPEC "): before(2) src_ip=0x%08x dst_ip=0x%08x", iteration, src_ip, dst_ip);
            ++dst_ip;
            dbgx(1, "dst_ip > src_ip(" COUNTER_SPEC "): after(2)  src_ip=0x%08x dst_ip=0x%08x", iteration, src_ip, dst_ip);
        }
    } else {
        if (cached) {
            ++src_ip;
            --dst_ip;
        } else {
            src_ip += iteration;
            dst_ip -= iteration;
        }

        /* CRC compensations  for wrap conditions */
        if (dst_ip > dst_ip_orig && src_ip > src_ip_orig) {
            dbgx(1, "src_ip > dst_ip(" COUNTER_SPEC "): before(1) dst_ip=0x%08x src_ip=0x%08x", iteration, dst_ip, src_ip);
            --dst_ip;
            dbgx(1, "src_ip > dst_ip(" COUNTER_SPEC "): after(1)  dst_ip=0x%08x src_ip=0x%08x", iteration, dst_ip, src_ip);
        } else if (src_ip < src_ip_orig && dst_ip < dst_ip_orig) {
            dbgx(1, "src_ip > dst_ip(" COUNTER_SPEC "): before(2) dst_ip=0x%08x src_ip=0x%08x", iteration, dst_ip, src_ip);
            ++src_ip;
            dbgx(1, "src_ip > dst_ip(" COUNTER_SPEC "): after(2)  dst_ip=0x%08x src_ip=0x%08x", iteration, dst_ip, src_ip);
        }
    }

    dbgx(1, "(" COUNTER_SPEC "): final src_ip=0x%08x dst_ip=0x%08x", iteration, src_ip, dst_ip);

    switch (ether_type) {
    case ETHERTYPE_IP:
        ip_hdr->ip_src.s_addr = htonl(src_ip);
        ip_hdr->ip_dst.s_addr = htonl(dst_ip);
        break;

    case ETHERTYPE_IP6:
        ip6_hdr->ip_src.__u6_addr.__u6_addr32[3] = htonl(src_ip);
        ip6_hdr->ip_dst.__u6_addr.__u6_addr32[3] = htonl(dst_ip);
        break;
    }

    return 0;
}

/**
 * \brief Update flow stats
 *
 * Finds out if flow is unique and updates stats.
 */
static inline void update_flow_stats(tcpreplay_t *ctx, sendpacket_t *sp,
        const struct pcap_pkthdr *pkthdr, const u_char *pktdata, int datalink)
{
    flow_entry_type_t res = flow_decode(ctx->flow_hash_table,
            pkthdr, pktdata, datalink, ctx->options->flow_expiry);

    switch (res) {
    case FLOW_ENTRY_NEW:
        ++ctx->stats.flows;
        ++ctx->stats.flows_unique;
        ++ctx->stats.flow_packets;
        if (sp) {
            ++sp->flows;
            ++sp->flows_unique;
            ++sp->flow_packets;
        }
        break;

    case FLOW_ENTRY_EXISTING:
        ++ctx->stats.flow_packets;
        if (sp)
            ++sp->flow_packets;
        break;

    case FLOW_ENTRY_EXPIRED:
        ++ctx->stats.flows_expired;
        ++ctx->stats.flows;
        ++ctx->stats.flow_packets;
        if (sp) {
            ++sp->flows_expired;
            ++sp->flows;
            ++sp->flow_packets;
        }
         break;

    case FLOW_ENTRY_NON_IP:
        ++ctx->stats.flow_non_flow_packets;
        if (sp)
            ++sp->flow_non_flow_packets;
        break;

    case FLOW_ENTRY_INVALID:
        ++ctx->stats.flows_invalid_packets;
        if (sp)
            ++sp->flows_invalid_packets;
        break;
    }
}
/**
 * \brief Preloads the memory cache for the given pcap file_idx 
 *
 * Preloading can be used with or without --loop
 */
void
preload_pcap_file(tcpreplay_t *ctx, int idx)
{
    tcpreplay_opt_t *options = ctx->options;
    char *path = options->sources[idx].filename;
    pcap_t *pcap = NULL;
    char ebuf[PCAP_ERRBUF_SIZE];
    const u_char *pktdata = NULL;
    struct pcap_pkthdr pkthdr;
    packet_cache_t *cached_packet = NULL;
    packet_cache_t **prev_packet = &cached_packet;
    COUNTER packetnum = 0;
    int dlt;

    /* close stdin if reading from it (needed for some OS's) */
    if (strncmp(path, "-", 1) == 0)
        if (close(1) == -1)
            warnx("unable to close stdin: %s", strerror(errno));

    if ((pcap = pcap_open_offline(path, ebuf)) == NULL)
        errx(-1, "Error opening pcap file: %s", ebuf);

    dlt = pcap_datalink(pcap);
    /* loop through the pcap.  get_next_packet() builds the cache for us! */
    while ((pktdata = get_next_packet(ctx, pcap, &pkthdr, idx, prev_packet)) != NULL) {
        packetnum++;
        if (options->flow_stats)
            update_flow_stats(ctx, NULL, &pkthdr, pktdata, dlt);
    }

    /* mark this file as cached */
    options->file_cache[idx].cached = TRUE;
    options->file_cache[idx].dlt = dlt;
    pcap_close(pcap);
}

static void increment_iteration(tcpreplay_t *ctx)
{
    tcpreplay_opt_t *options = ctx->options;

    ctx->last_unique_iteration = ctx->unique_iteration;
    ++ctx->iteration;
    if (options->unique_ip) {
        assert(options->unique_loops > 0.0);
        ctx->unique_iteration =
                ((ctx->iteration * 1000) / (COUNTER)(options->unique_loops * 1000.0))
                + 1;
    }
}


static inline int
add_pkt_timestamp(struct pcap_pkthdr *pkthdr,  u_char *pktdata, int datalink, int send_idx)
{
    u_char *packet = pktdata;
    uint32_t pkt_len = pkthdr->caplen;
    ipv4_hdr_t *ip_hdr = NULL;
    ipv6_hdr_t *ip6_hdr = NULL;
    u_char *udp_hdr = NULL;
    u_char *payload = NULL;
    uint32_t src_ip, dst_ip;
    uint32_t src_ip_orig, dst_ip_orig;
    uint32_t _U_ vlan_offset;
    uint16_t ether_type;
    uint32_t l2offset;
    uint32_t l2len;
    int res;
    int udp_header_length;
    int payload_length;
    res = get_l2len_protocol(packet,
                             pkt_len,
                             datalink,
                             &ether_type,
                             &l2len,
                             &l2offset,
                             &vlan_offset);

    if (res < 0)
        return res;

    assert(l2len > 0);

    switch (ether_type) {
    case ETHERTYPE_IP:
        dbgx(2, "This is an IP packet - Tung: %u", pkthdr->caplen);
        if (pkt_len < (bpf_u_int32)(l2len + sizeof(ipv4_hdr_t))) {
            dbgx(1, "IP packet too short for Unique IP feature: %u", pkthdr->caplen);
            return -1;
        }
        ip_hdr = (ipv4_hdr_t *)(packet + l2len);
        src_ip_orig = src_ip = ntohl(ip_hdr->ip_src.s_addr);
        dst_ip_orig = dst_ip = ntohl(ip_hdr->ip_dst.s_addr);
        //struct in_addr addr = {src_ip_orig};
        //dbgx(2, "Src ip address: %s", inet_ntoa(addr));
        udp_hdr = (u_char *)ip_hdr + (ip_hdr->ip_hl << 2);
        //udp_header_length = ((*(udp_hdr + 4)) & 0xF0) >> 4;
        //udp_header_length = udp_header_length * 4;
        payload_length = pkthdr->caplen - l2len - (ip_hdr->ip_hl << 2) - 8;
        dbgx(2, "Payload len in bytes: %d", pkthdr->caplen - l2len - (ip_hdr->ip_hl << 2) - 8);
        payload = udp_hdr + 8;
        //payload = packet + l2len + (ip_hdr->ip_hl << 2) + 8;
        struct timeval now;
        gettimeofday(&now, NULL);
        uint64_t timestamp = now.tv_sec*(uint64_t)1000000 + now.tv_usec;
        printf("Sender time = %ld and", timestamp); //Osel        
        unsigned char value[sizeof(timestamp)];
        memcpy(value,&timestamp,sizeof(timestamp));

        u_char *temp_pointer = payload;
        int byte_count = 0;
        int MAX_COUNT = 8;
        while (byte_count < MAX_COUNT) {
            //dbgx(2, "byte count: %d", byte_count);
            //dbgx(2, "Payload in value: %c", value[byte_count]);
            temp_pointer[byte_count] = value[byte_count];
            byte_count++;
        }


        //Osel *************************
        unsigned char value_s[sizeof(send_idx)];
        printf(" index = %d\n", send_idx);
        memcpy(value_s,&send_idx,sizeof(send_idx));

        u_char *pointer_s_idx = payload + 8;
        int byte_count_s = 0;
        int MAX_COUNT_s = 4;
        while (byte_count_s < MAX_COUNT_s) {
            pointer_s_idx[byte_count_s] = value_s[byte_count_s];
            byte_count_s++;
        }
        
        //*******************************

        byte_count = 0;
        unsigned char back_value[8];
        while (byte_count < MAX_COUNT) {
            dbgx(2, "Payload: %c", temp_pointer[byte_count]);
            back_value[byte_count] = temp_pointer[byte_count];
            byte_count++;
        }
        
        
        uint64_t rtest = 0;
        memcpy(&rtest, back_value, sizeof(uint64_t));
        
        //dbgx(2, "Test value: %ld", rtest);

        //uint16_t test = 1026;
        //dbgx(2, "Test origin: %lu", test);
        //unsigned char value[sizeof(test)];
        //memcpy(value,&test,sizeof(test));
        //uint16_t rtest = (uint16_t) (value[0] << 8) | (uint16_t) value[1];
        //uint16_t rtest = 0;
        //memcpy(&rtest, value, sizeof(uint16_t));
        //dbgx(2, "Test value: %lu", rtest);
        //payload[0] = 'x';
        //uint64_t *uint64_payload = (uint64_t *) payload;
        //payload[0] = (uint64_t)1681296205754906;
        //dbgx(2, "Time in the payload just added: %ld", payload[0]);
        //payload = (u_char *) payload;

        //payload = (uint64_t *) payload;

        //dbgx(2, "Time in the payload: %ld", payload[0]);

        //const uint64_t *temp_pointer = uint64_payload;
        //int byte_count = 0;
        //while (byte_count++ < payload_length) {
            //dbgx(2, "Payload: %c", *temp_pointer);
            //temp_pointer++;
        //}
        //dbgx(2, "byte count: %d", byte_count);
        break;
     default:
        return -1; /* non-IP or packet too short */
    }


}


static inline int
check_timestamp(struct pcap_pkthdr *pkthdr,  const u_char *pktdata, int datalink)
{
    u_char *packet = pktdata;
    uint32_t pkt_len = pkthdr->caplen;
    ipv4_hdr_t *ip_hdr = NULL;
    ipv6_hdr_t *ip6_hdr = NULL;
    u_char *udp_hdr = NULL;
    u_char *payload = NULL;
    uint32_t src_ip, dst_ip;
    uint32_t src_ip_orig, dst_ip_orig;
    uint32_t _U_ vlan_offset;
    uint16_t ether_type;
    uint32_t l2offset;
    uint32_t l2len;
    int res;
    int udp_header_length;
    int payload_length;
    res = get_l2len_protocol(packet,
                             pkt_len,
                             datalink,
                             &ether_type,
                             &l2len,
                             &l2offset,
                             &vlan_offset);

    if (res < 0)
        return res;

    assert(l2len > 0);

    switch (ether_type) {
    case ETHERTYPE_IP:
        dbgx(2, "AFTER: This is an IP packet - Tung: %u", pkthdr->caplen);
        if (pkt_len < (bpf_u_int32)(l2len + sizeof(ipv4_hdr_t))) {
            dbgx(1, "IP packet too short for Unique IP feature: %u", pkthdr->caplen);
            return -1;
        }
        ip_hdr = (ipv4_hdr_t *)(packet + l2len);
        src_ip_orig = src_ip = ntohl(ip_hdr->ip_src.s_addr);
        dst_ip_orig = dst_ip = ntohl(ip_hdr->ip_dst.s_addr);
        //struct in_addr addr = {src_ip_orig};
        udp_hdr = (u_char *)ip_hdr + (ip_hdr->ip_hl << 2);
        //udp_header_length = ((*(udp_hdr + 4)) & 0xF0) >> 4;
        //udp_header_length = udp_header_length * 4;
        payload_length = pkthdr->caplen - l2len - (ip_hdr->ip_hl << 2) - 8;
        dbgx(2, "AFTER: Payload len in bytes: %d", pkthdr->caplen - l2len - (ip_hdr->ip_hl << 2) - 8);
        payload = udp_hdr + 8;
        const u_char *temp_pointer = payload;
        int byte_count = 0;
        while (byte_count++ < payload_length) {
            dbgx(2, "AFTER: Payload: %c", *temp_pointer);
            temp_pointer++;
        }
        break;
     default:
        return -1; /* non-IP or packet too short */
    }
}




/**
 * the main loop function for tcpreplay.  This is where we figure out
 * what to do with each packet
 */
void
send_packets(tcpreplay_t *ctx, pcap_t *pcap, int idx)
{

    struct timeval print_delta, now, last_pkt_ts;
    tcpreplay_opt_t *options = ctx->options;
    tcpreplay_stats_t *stats = &ctx->stats;
    COUNTER packetnum = 0;
    COUNTER limit_send = options->limit_send;
    struct pcap_pkthdr pkthdr;
    u_char *pktdata = NULL;    
    u_char *extra_pktdata = NULL; //Osel
    sendpacket_t *sp = ctx->intf1;
    COUNTER pktlen;
    packet_cache_t *cached_packet = NULL;
    packet_cache_t **prev_packet = NULL;
#if defined TCPREPLAY && defined TCPREPLAY_EDIT
    struct pcap_pkthdr *pkthdr_ptr;
#endif
    int datalink = options->file_cache[idx].dlt;
    COUNTER skip_length = 0;
    COUNTER end_us;
    bool preload = options->file_cache[idx].cached;
    bool top_speed = (options->speed.mode == speed_topspeed ||
            (options->speed.mode == speed_mbpsrate && options->speed.speed == 0));
    bool now_is_now = true;

    gettimeofday(&now, NULL);
    if (!timerisset(&stats->start_time)) {
        TIMEVAL_SET(&stats->start_time, &now);
        if (ctx->options->stats >= 0) {
            char buf[64];
            if (format_date_time(&stats->start_time, buf, sizeof(buf)) > 0)
                printf("Test start: %s ...\n", buf);
        }
    }

    ctx->skip_packets = 0;
    timerclear(&last_pkt_ts);
    if (options->limit_time > 0)
        end_us = TIMEVAL_TO_MICROSEC(&stats->start_time) +
            SEC_TO_MICROSEC(options->limit_time);
    else
        end_us = 0;

    if (options->preload_pcap) {
        prev_packet = &cached_packet;
    } else {
        prev_packet = NULL;
    }

    /* MAIN LOOP 
     * Keep sending while we have packets or until
     * we've sent enough packets
     */
    
    while (!ctx->abort &&
            (pktdata = get_next_packet(ctx, pcap, &pkthdr, idx, prev_packet)) != NULL) {

        now_is_now = false;
        packetnum++;
#if defined TCPREPLAY || defined TCPREPLAY_EDIT
        /* do we use the snaplen (caplen) or the "actual" packet len? */
        pktlen = options->use_pkthdr_len ? (COUNTER)pkthdr.len : (COUNTER)pkthdr.caplen;
#elif TCPBRIDGE
        pktlen = (COUNTER)pkthdr.caplen;
#else
#error WTF???  We should not be here!
#endif


        //Osel
        int send_idx = packetnum;       
        
        // get tcp header length
        add_pkt_timestamp(&pkthdr, pktdata, datalink, send_idx);
        //check_timestamp(&pkthdr, pktdata, datalink);

        //struct ether_header *eth_header;
        //eth_header = (struct ether_header *) pktdata;
        /*
        u_char *real_pkt = pktdata;
        if ((real_pkt[0] >> 4) == 0) {
           dbgx(2, "This is an IP packet %u", *pktdata);
        }
        if ((real_pkt[0] >> 4) == 6)
          {
              dbgx(2, "This not an IP packet", *pktdata);
          }

        dbgx(2, "How the packet looks like: %u", (real_pkt[0] >> 4));
        dbgx(2, "How the packet looks like: %u", (pktdata[0] >> 4));
        */
        dbgx(2, "packet " COUNTER_SPEC " caplen " COUNTER_SPEC, packetnum, pktlen);

        //dbgx(2, "How the packet looks like: %u", &pktdata);

        //dbgx(2, "How the packet looks like: %u", *pktdata);

        //dbgx(2, "How the packet looks like: %u", **pktdata);

        /* Dual nic processing */
        if (ctx->intf2 != NULL) {
            sp = (sendpacket_t *)cache_mode(ctx, options->cachedata, packetnum);

            /* sometimes we should not send the packet */
            if (sp == TCPR_DIR_NOSEND)
                continue;
        }
        
        //set the data of the extra packet using the 1st original packet, since there is no
        //previous or cached and after the last packet its NULL so we have to store in the start
        if (send_idx==1) {
           extra_pktdata = pktdata; //Osel 
        }

        //dbgx(2, "I am here: %u", &pktdata);
        ///fast_edit_packet(&pkthdr, &pktdata, ctx->unique_iteration - 1, preload, datalink)


#if defined TCPREPLAY && defined TCPREPLAY_EDIT
        pkthdr_ptr = &pkthdr;
        if (tcpedit_packet(tcpedit, &pkthdr_ptr, &pktdata, sp->cache_dir) == -1) {
            errx(-1, "Error editing packet #" COUNTER_SPEC ": %s", packetnum, tcpedit_geterr(tcpedit));
        }
        pktlen = options->use_pkthdr_len ? (COUNTER)pkthdr_ptr->len : (COUNTER)pkthdr_ptr->caplen;
#endif

        if (ctx->options->unique_ip && ctx->unique_iteration &&
                ctx->unique_iteration > ctx->last_unique_iteration) {
            //dbgx(2, "I am here: %u", &pktdata);
            /* edit packet to ensure every pass has unique IP addresses */
            if (fast_edit_packet(&pkthdr, &pktdata, ctx->unique_iteration - 1,
                    preload, datalink) == -1) {
                ++stats->failed;
                continue;
            }
        }

        /* update flow stats */
        if (options->flow_stats && !preload)
            update_flow_stats(ctx,
                    options->cache_packets ? sp : NULL, &pkthdr, pktdata, datalink);

        /*
         * this accelerator improves performance by avoiding expensive
         * time stamps during periods where we have fallen behind in our
         * sending
         */
        if (skip_length && pktlen < skip_length) {
            skip_length -= pktlen;
        } else if (ctx->skip_packets) {
            --ctx->skip_packets;
        } else {
            /*
             * time stamping is expensive, but now is the
             * time to do it.
             */
            dbgx(4, "This packet time: " TIMEVAL_FORMAT, pkthdr.ts.tv_sec,
                    pkthdr.ts.tv_usec);
            skip_length = 0;
            ctx->skip_packets = 0;

            if (options->speed.mode == speed_multiplier) {
                if (!timerisset(&last_pkt_ts)) {
                    TIMEVAL_SET(&last_pkt_ts, &pkthdr.ts);
                } else if (timercmp(&pkthdr.ts, &last_pkt_ts, >)) {
                    struct timeval delta;

                    timersub(&pkthdr.ts, &last_pkt_ts, &delta);
                    timeradd(&stats->pkt_ts_delta, &delta, &stats->pkt_ts_delta);
                    TIMEVAL_SET(&last_pkt_ts, &pkthdr.ts);
                }
            }

            if (!top_speed) {
                now_is_now = true;
                gettimeofday(&now, NULL);
            }

            /*
             * Only if the current packet is not late.
             *
             * This also sets skip_length and skip_packets which will avoid
             * timestamping for a given number of packets.
             */
            calc_sleep_time(ctx, &stats->pkt_ts_delta, &stats->time_delta,
                    pktlen, sp, packetnum, &stats->end_time,
                    TIMEVAL_TO_MICROSEC(&stats->start_time), &skip_length);

            /*
             * Track the time of the "last packet sent".
             *
             * A number of 3rd party tools generate bad timestamps which go backwards
             * in time.  Hence, don't update the "last" unless pkthdr.ts > last
             */
            if (timercmp(&stats->time_delta, &stats->pkt_ts_delta, <))
                TIMEVAL_SET(&stats->time_delta, &stats->pkt_ts_delta);

            /*
             * we know how long to sleep between sends, now do it.
             */
            if (!top_speed)
                tcpr_sleep(ctx, sp, &ctx->nap, &now);
        }

#ifdef ENABLE_VERBOSE
        /* do we need to print the packet via tcpdump? */
        if (options->verbose)
            tcpdump_print(options->tcpdump, &pkthdr, pktdata);
#endif

        dbgx(2, "Sending packet #" COUNTER_SPEC, packetnum);
        /* write packet out on network */
        if (sendpacket(sp, pktdata, pktlen, &pkthdr) < (int)pktlen) {
            warnx("Unable to send packet: %s", sendpacket_geterr(sp));
            break;
        }


        //check_timestamp(&pkthdr, pktdata, datalink);
        //break;

        /*
         * Mark the time when we sent the last packet
         */
        TIMEVAL_SET(&stats->end_time, &now);

#ifdef TIMESTAMP_TRACE
        add_timestamp_trace_entry(pktlen, &stats->end_time, skip_length);
#endif

        //check_timestamp(&pkthdr, pktdata, datalink);


        stats->pkts_sent++;
        stats->bytes_sent += pktlen;

        /* print stats during the run? */
        if (options->stats > 0) {
            if (! timerisset(&stats->last_print)) {
                TIMEVAL_SET(&stats->last_print, &now);
            } else {
                timersub(&now, &stats->last_print, &print_delta);
                if (print_delta.tv_sec >= options->stats) {
                    TIMEVAL_SET(&stats->end_time, &now);
                    packet_stats(stats);
                    TIMEVAL_SET(&stats->last_print, &now);
                }
            }
        }

#if defined HAVE_NETMAP
        if (sp->first_packet || timesisset(&ctx->nap)) {
            wake_send_queues(sp, options);
            sp->first_packet = false;
        }
#endif
        /* stop sending based on the duration limit... */
        if ((end_us > 0 && (COUNTER)TIMEVAL_TO_MICROSEC(&now) > end_us) ||
                /* ... or stop sending based on the limit -L? */
                (limit_send > 0 && stats->pkts_sent >= limit_send)) {
            ctx->abort = true;
        }
        
    } /* while */
    
    
    // Osel, send extra packets after last packet  *********************     
    if (pktdata == NULL) { 
		if (extra_pktdata != NULL) {
            pktdata = extra_pktdata;		
			int send_idx = 123456789;    
			for (int extra = 1; extra <= 128; extra++) {
				//printf("Extra Packets ");
				add_pkt_timestamp(&pkthdr, pktdata, datalink, send_idx);        
				if (sendpacket(sp, pktdata, pktlen, &pkthdr) < (int)pktlen) {
				    warnx("Unable to send packet: %s", sendpacket_geterr(sp));
				    break;
				}
				usleep(1000);
			} //end for loop
		}
    } //end if *********************************************************
    
    

#ifdef HAVE_NETMAP
    /* when completing test, wait until the last packet is sent */
    if (options->netmap && (ctx->abort || options->loop == 1)) {
        while (ctx->intf1 && !netmap_tx_queues_empty(ctx->intf1)) {
            now_is_now = true;
            gettimeofday(&now, NULL);
        }

        while (ctx->intf2 && !netmap_tx_queues_empty(ctx->intf2)) {
            now_is_now = true;
            gettimeofday(&now, NULL);
        }
    }
#endif /* HAVE_NETMAP */

    //check_timestamp(&pkthdr, pktdata, datalink);

    if (!now_is_now)
        gettimeofday(&now, NULL);

    TIMEVAL_SET(&stats->end_time, &now);

    increment_iteration(ctx);
}

/**
 * the alternate main loop function for tcpreplay.  This is where we figure out
 * what to do with each packet when processing two files a the same time
 */
void
send_dual_packets(tcpreplay_t *ctx, pcap_t *pcap1, int cache_file_idx1, pcap_t *pcap2, int cache_file_idx2)
{
    struct timeval print_delta, now, last_pkt_ts;
    tcpreplay_opt_t *options = ctx->options;
    tcpreplay_stats_t *stats = &ctx->stats;
    COUNTER packetnum = 0;
    COUNTER limit_send = options->limit_send;
    int cache_file_idx;
    struct pcap_pkthdr pkthdr1, pkthdr2;
    u_char *pktdata1 = NULL, *pktdata2 = NULL, *pktdata = NULL;
    sendpacket_t *sp;
    COUNTER pktlen;
    packet_cache_t *cached_packet1 = NULL, *cached_packet2 = NULL;
    packet_cache_t **prev_packet1 = NULL, **prev_packet2 = NULL;
    struct pcap_pkthdr *pkthdr_ptr;
    int datalink;
    COUNTER end_us;
    COUNTER skip_length = 0;
    bool top_speed = (options->speed.mode == speed_topspeed ||
            (options->speed.mode == speed_mbpsrate && options->speed.speed == 0));
    bool now_is_now = true;

    gettimeofday(&now, NULL);
    if (!timerisset(&stats->start_time)) {
        TIMEVAL_SET(&stats->start_time, &now);
        if (ctx->options->stats >= 0) {
            char buf[64];
            if (format_date_time(&stats->start_time, buf, sizeof(buf)) > 0)
                printf("Dual test start: %s ...\n", buf);
        }
    }

    ctx->skip_packets = 0;
    timerclear(&last_pkt_ts);
    if (options->limit_time > 0)
        end_us = TIMEVAL_TO_MICROSEC(&stats->start_time) +
            SEC_TO_MICROSEC(options->limit_time);
    else
        end_us = 0;

    if (options->preload_pcap) {
        prev_packet1 = &cached_packet1;
        prev_packet2 = &cached_packet2;
    } else {
        prev_packet1 = NULL;
        prev_packet2 = NULL;
    }

    pktdata1 = get_next_packet(ctx, pcap1, &pkthdr1, cache_file_idx1, prev_packet1);
    pktdata2 = get_next_packet(ctx, pcap2, &pkthdr2, cache_file_idx2, prev_packet2);

    /* MAIN LOOP 
     * Keep sending while we have packets or until
     * we've sent enough packets
     */
    while (!ctx->abort &&
            !(pktdata1 == NULL && pktdata2 == NULL)) {

        now_is_now = false;
        packetnum++;

        /* figure out which pcap file we need to process next 
         * when get_next_packet() returns null for pktdata, the pkthdr 
         * will still have the old values from the previous call.  This
         * means we can't always trust the timestamps to tell us which
         * file to process.
         */
        if (pktdata1 == NULL) {
            /* file 2 is next */
            sp = ctx->intf2;
            datalink = options->file_cache[cache_file_idx2].dlt;
            pkthdr_ptr = &pkthdr2;
            cache_file_idx = cache_file_idx2;
            pktdata = pktdata2;
        } else if (pktdata2 == NULL) {
            /* file 1 is next */
            sp = ctx->intf1;
            datalink = options->file_cache[cache_file_idx1].dlt;
            pkthdr_ptr = &pkthdr1;
            cache_file_idx = cache_file_idx1;
            pktdata = pktdata1;
        } else if (timercmp(&pkthdr1.ts, &pkthdr2.ts, <=)) {
            /* file 1 is next */
            sp = ctx->intf1;
            datalink = options->file_cache[cache_file_idx1].dlt;
            pkthdr_ptr = &pkthdr1;
            cache_file_idx = cache_file_idx1;
            pktdata = pktdata1;
        } else {
            /* file 2 is next */
            sp = ctx->intf2;
            datalink = options->file_cache[cache_file_idx2].dlt;
            pkthdr_ptr = &pkthdr2;
            cache_file_idx = cache_file_idx2;
            pktdata = pktdata2;
        }

#if defined TCPREPLAY || defined TCPREPLAY_EDIT
        /* do we use the snaplen (caplen) or the "actual" packet len? */
        pktlen = options->use_pkthdr_len ? (COUNTER)pkthdr_ptr->len : (COUNTER)pkthdr_ptr->caplen;
#elif TCPBRIDGE
        pktlen = (COUNTER)pkthdr_ptr->caplen;
#else
#error WTF???  We should not be here!
#endif

        dbgx(2, "packet " COUNTER_SPEC " caplen " COUNTER_SPEC, packetnum, pktlen);

#if defined TCPREPLAY && defined TCPREPLAY_EDIT
        if (tcpedit_packet(tcpedit, &pkthdr_ptr, &pktdata, sp->cache_dir) == -1) {
            errx(-1, "Error editing packet #" COUNTER_SPEC ": %s", packetnum, tcpedit_geterr(tcpedit));
        }
        pktlen = options->use_pkthdr_len ? (COUNTER)pkthdr_ptr->len : (COUNTER)pkthdr_ptr->caplen;
#endif

        if (ctx->options->unique_ip && ctx->unique_iteration &&
                ctx->unique_iteration > ctx->last_unique_iteration) {
            /* edit packet to ensure every pass is unique */
            if (fast_edit_packet(pkthdr_ptr, &pktdata, ctx->unique_iteration - 1,
                    options->file_cache[cache_file_idx].cached, datalink) == -1) {
                ++stats->failed;
                continue;
            }
        }

        /* update flow stats */
        if (options->flow_stats && !options->file_cache[cache_file_idx].cached)
            update_flow_stats(ctx, sp, pkthdr_ptr, pktdata, datalink);

        /*
         * this accelerator improves performance by avoiding expensive
         * time stamps during periods where we have fallen behind in our
         * sending
         */
        if (skip_length && pktlen < skip_length) {
            skip_length -= pktlen;
        } else if (ctx->skip_packets) {
            --ctx->skip_packets;
        } else {
            /*
             * time stamping is expensive, but now is the
             * time to do it.
             */
            dbgx(4, "This packet time: " TIMEVAL_FORMAT, pkthdr_ptr->ts.tv_sec,
                    pkthdr_ptr->ts.tv_usec);
            skip_length = 0;
            ctx->skip_packets = 0;

            if (options->speed.mode == speed_multiplier) {
                if (!timerisset(&last_pkt_ts)) {
                    TIMEVAL_SET(&last_pkt_ts, &pkthdr_ptr->ts);
                } else if (timercmp(&pkthdr_ptr->ts, &last_pkt_ts, >)) {
                    struct timeval delta;

                    timersub(&pkthdr_ptr->ts, &last_pkt_ts, &delta);
                    timeradd(&stats->pkt_ts_delta, &delta, &stats->pkt_ts_delta);
                    TIMEVAL_SET(&last_pkt_ts, &pkthdr_ptr->ts);
                }

                if (!timerisset(&stats->time_delta))
                    TIMEVAL_SET(&stats->pkt_ts_delta, &stats->pkt_ts_delta);
            }

            if (!top_speed) {
                gettimeofday(&now, NULL);
                now_is_now = true;
            }

            /*
             * Only if the current packet is not late.
             *
             * This also sets skip_length and skip_packets which will avoid
             * timestamping for a given number of packets.
             */
            calc_sleep_time(ctx, &stats->pkt_ts_delta, &stats->time_delta,
                    pktlen, sp, packetnum, &stats->end_time,
                    TIMEVAL_TO_MICROSEC(&stats->start_time), &skip_length);

            /*
             * Track the time of the "last packet sent".
             *
             * A number of 3rd party tools generate bad timestamps which go backwards
             * in time.  Hence, don't update the "last" unless pkthdr_ptr->ts > last
             */
            if (timercmp(&stats->time_delta, &stats->pkt_ts_delta, <))
                TIMEVAL_SET(&stats->time_delta, &stats->pkt_ts_delta);

            /*
             * we know how long to sleep between sends, now do it.
             */
            if (!top_speed)
                tcpr_sleep(ctx, sp, &ctx->nap, &now);
        }

#ifdef ENABLE_VERBOSE
        /* do we need to print the packet via tcpdump? */
        if (options->verbose)
            tcpdump_print(options->tcpdump, pkthdr_ptr, pktdata);
#endif

        dbgx(2, "Sending packet #" COUNTER_SPEC, packetnum);
        /* write packet out on network */
        if (sendpacket(sp, pktdata, pktlen, pkthdr_ptr) < (int)pktlen) {
            warnx("Unable to send packet: %s", sendpacket_geterr(sp));
            break;
        }

        /*
         * Mark the time when we sent the last packet
         */
        TIMEVAL_SET(&stats->end_time, &now);

        ++stats->pkts_sent;
        stats->bytes_sent += pktlen;

        /* print stats during the run? */
        if (options->stats > 0) {
            if (! timerisset(&stats->last_print)) {
                TIMEVAL_SET(&stats->last_print, &now);
            } else {
                timersub(&now, &stats->last_print, &print_delta);
                if (print_delta.tv_sec >= options->stats) {
                    TIMEVAL_SET(&stats->end_time, &now);
                    packet_stats(stats);
                    TIMEVAL_SET(&stats->last_print, &now);
                }
            }
        }

#if defined HAVE_NETMAP
        if (sp->first_packet || timesisset(&ctx->nap)) {
            wake_send_queues(sp, options);
            sp->first_packet = false;
        }
#endif

        /* get the next packet for this file handle depending on which we last used */
        if (sp == ctx->intf2) {
            pktdata2 = get_next_packet(ctx, pcap2, &pkthdr2, cache_file_idx2, prev_packet2);
        } else {
            pktdata1 = get_next_packet(ctx, pcap1, &pkthdr1, cache_file_idx1, prev_packet1);
        }

        /* stop sending based on the duration limit... */
        if ((end_us > 0 && (COUNTER)TIMEVAL_TO_MICROSEC(&now) > end_us) ||
                /* ... or stop sending based on the limit -L? */
                (limit_send > 0 && stats->pkts_sent >= limit_send)) {
            ctx->abort = true;
        }
    } /* while */

#ifdef HAVE_NETMAP
    /* when completing test, wait until the last packet is sent */
    if (options->netmap && (ctx->abort || options->loop == 1)) {
        while (ctx->intf1 && !netmap_tx_queues_empty(ctx->intf1)) {
            gettimeofday(&now, NULL);
            now_is_now = true;
        }

        while (ctx->intf2 && !netmap_tx_queues_empty(ctx->intf2)) {
            gettimeofday(&now, NULL);
            now_is_now = true;
        }
    }
#endif /* HAVE_NETMAP */

    if (!now_is_now)
        gettimeofday(&now, NULL);

    TIMEVAL_SET(&stats->end_time, &now);

    increment_iteration(ctx);
}



/**
 * Gets the next packet to be sent out. This will either read from the pcap file
 * or will retrieve the packet from the internal cache.
 *
 * The parameter prev_packet is used as the parent of the new entry in the cache list.
 * This should be NULL on the first call to this function for each file and
 * will be updated as new entries are added (or retrieved) from the cache list.
 */
u_char *
get_next_packet(tcpreplay_t *ctx, pcap_t *pcap, struct pcap_pkthdr *pkthdr, int idx, 
    packet_cache_t **prev_packet)
{
    tcpreplay_opt_t *options = ctx->options;
    u_char *pktdata = NULL;
    uint32_t pktlen;

    /* pcap may be null in cache mode! */
    /* packet_cache_t may be null in file read mode! */
    assert(pkthdr);

    /*
     * Check if we're caching files
     */
    if (options->preload_pcap && (prev_packet != NULL)) {
        /*
         * Yes we are caching files - has this one been cached?
         */
        if (options->file_cache[idx].cached) {
            if (*prev_packet == NULL) {
                /*
                 * Get the first packet in the cache list directly from the file
                 */
                *prev_packet = options->file_cache[idx].packet_cache;
            } else {
                /*
                 * Get the next packet in the cache list
                 */
                *prev_packet = (*prev_packet)->next;
            }

            if (*prev_packet != NULL) {
                pktdata = (*prev_packet)->pktdata;
                memcpy(pkthdr, &((*prev_packet)->pkthdr), sizeof(struct pcap_pkthdr));
            }
        } else {
            /*
             * We should read the pcap file, and cache the results
             */
            pktdata = safe_pcap_next(pcap, pkthdr);
            if (pktdata != NULL) {
                if (*prev_packet == NULL) {
                    /*
                     * Create the first packet in the list
                     */
                    *prev_packet = safe_malloc(sizeof(packet_cache_t));
                    options->file_cache[idx].packet_cache = *prev_packet;
                } else {
                    /*
                     * Add a packet to the end of the list
                     */
                    (*prev_packet)->next = safe_malloc(sizeof(packet_cache_t));
                    *prev_packet = (*prev_packet)->next;
                }

                if (*prev_packet != NULL) {
                    (*prev_packet)->next = NULL;
                    pktlen = pkthdr->caplen;

                    (*prev_packet)->pktdata = safe_malloc(pktlen + PACKET_HEADROOM);
                    memcpy((*prev_packet)->pktdata, pktdata, pktlen);
                    memcpy(&((*prev_packet)->pkthdr), pkthdr, sizeof(struct pcap_pkthdr));
                }
            }
        }
    } else {
        /*
         * Read pcap file as normal
         */
        pktdata = safe_pcap_next(pcap, pkthdr);
    }

    /* this gets casted to a const on the way out */
    return pktdata;
}

/**
 * determines based upon the cachedata which interface the given packet 
 * should go out.  Also rewrites any layer 2 data we might need to adjust.
 * Returns a void cased pointer to the ctx->intfX of the corresponding 
 * interface or NULL on error
 */
void *
cache_mode(tcpreplay_t *ctx, char *cachedata, COUNTER packet_num)
{
    tcpreplay_opt_t *options = ctx->options;
    void *sp = NULL;
    int result;

    if (packet_num > options->cache_packets) {
        tcpreplay_seterr(ctx, "%s", "Exceeded number of packets in cache file.");
        return NULL;
    }

    result = check_cache(cachedata, packet_num);
    if (result == TCPR_DIR_NOSEND) {
        dbgx(2, "Cache: Not sending packet " COUNTER_SPEC ".", packet_num);
        return NULL;
    }
    else if (result == TCPR_DIR_C2S) {
        dbgx(2, "Cache: Sending packet " COUNTER_SPEC " out primary interface.", packet_num);
        sp = ctx->intf1;
    }
    else if (result == TCPR_DIR_S2C) {
        dbgx(2, "Cache: Sending packet " COUNTER_SPEC " out secondary interface.", packet_num);
        sp = ctx->intf2;
    }
    else {
        tcpreplay_seterr(ctx, "Invalid cache value: %i", result);
        return NULL;
    }

    return sp;
}


/**
 * Given the timestamp on the current packet and the last packet sent,
 * calculate the appropriate amount of time to sleep. Sleep time
 * will be in ctx->nap.
 */
static void calc_sleep_time(tcpreplay_t *ctx, struct timeval *pkt_ts_delta,
        struct timeval *time_delta, COUNTER len,
        sendpacket_t *sp, COUNTER counter, timestamp_t *sent_timestamp,
        COUNTER start_us, COUNTER *skip_length)
{
    tcpreplay_opt_t *options = ctx->options;
    struct timeval nap_for;
    COUNTER now_us;

    timesclear(&ctx->nap);

    /*
     * pps_multi accelerator.    This uses the existing send accelerator
     * and hence requires the funky math to get the expected timings.
     */
    if (options->speed.mode == speed_packetrate && options->speed.pps_multi) {
        ctx->skip_packets = options->speed.pps_multi - 1;
    }

    /* no last packet sent, just leave */
    if (ctx->first_time) {
        ctx->first_time = false;
        return;
    }

    switch(options->speed.mode) {
    case speed_multiplier:
        /*
         * Replay packets a factor of the time they were originally sent.
         * Make sure the packet is not late.
         */
        if (timercmp(pkt_ts_delta, time_delta, >)) {
            /* pkt_time_delta has increased, so handle normally */
            timersub(pkt_ts_delta, time_delta, &nap_for);
            TIMEVAL_TO_TIMESPEC(&nap_for, &ctx->nap);
            dbgx(3, "original packet delta time: " TIMESPEC_FORMAT,
                    ctx->nap.tv_sec, ctx->nap.tv_nsec);
            timesdiv_float(&ctx->nap, options->speed.multiplier);
            dbgx(3, "original packet delta/div: " TIMESPEC_FORMAT,
                    ctx->nap.tv_sec, ctx->nap.tv_nsec);
        }
        break;

    case speed_mbpsrate:
        /*
         * Ignore the time supplied by the capture file and send data at
         * a constant 'rate' (bytes per second).
         */
        now_us = TIMSTAMP_TO_MICROSEC(sent_timestamp);
        if (now_us) {
            COUNTER next_tx_us;
            COUNTER bps = options->speed.speed;
            COUNTER bits_sent = ((ctx->stats.bytes_sent + len) * 8);
            COUNTER tx_us = now_us - start_us;

            /*
             * bits * 1000000 divided by bps = microseconds
             *
             * ensure there is no overflow in cases where bits_sent is very high
             */
            if (bits_sent > COUNTER_OVERFLOW_RISK && bps > 500000)
                next_tx_us = (bits_sent * 1000) / bps * 1000;
            else
                next_tx_us = (bits_sent * 1000000) / bps;

            if (next_tx_us > tx_us) {
                NANOSEC_TO_TIMESPEC((next_tx_us - tx_us) * 1000, &ctx->nap);
            } else if (tx_us > next_tx_us) {
                tx_us = now_us - start_us;
                *skip_length = ((tx_us - next_tx_us) * bps) / 8000000;
            }

            update_current_timestamp_trace_entry(ctx->stats.bytes_sent +
                    (COUNTER)len, now_us, tx_us, next_tx_us);
        }

        dbgx(3, "packet size=" COUNTER_SPEC "\t\tnap=" TIMESPEC_FORMAT, len,
                ctx->nap.tv_sec, ctx->nap.tv_nsec);
        break;

    case speed_packetrate:
        /*
          * Ignore the time supplied by the capture file and send data at
          * a constant rate (packets per second).
          */
         now_us = TIMSTAMP_TO_MICROSEC(sent_timestamp);
         if (now_us) {
             COUNTER next_tx_us;
             COUNTER pph = ctx->options->speed.speed;
             COUNTER pkts_sent = ctx->stats.pkts_sent;
             COUNTER tx_us = now_us - start_us;
             /*
              * packets * 1000000 divided by pps = microseconds
              * packets per sec (pps) = packets per hour / (60 * 60)
              *
              * Adjust for long running tests with high PPS to prevent overflow.
              * When active, adjusted calculation may add a bit of jitter.
              */
             if ((pkts_sent < COUNTER_OVERFLOW_RISK))
                 next_tx_us = (pkts_sent * 1000000) * (60 * 60) / pph;
             else
                 next_tx_us = ((pkts_sent * 1000000) / pph) * (60 * 60);

             if (next_tx_us > tx_us)
                 NANOSEC_TO_TIMESPEC((next_tx_us - tx_us) * 1000, &ctx->nap);
             else
                 ctx->skip_packets = options->speed.pps_multi;

             update_current_timestamp_trace_entry(ctx->stats.bytes_sent +
                     (COUNTER)len, now_us, tx_us, next_tx_us);
         }

         dbgx(3, "packet count=" COUNTER_SPEC "\t\tnap=" TIMESPEC_FORMAT,
                 ctx->stats.pkts_sent, ctx->nap.tv_sec, ctx->nap.tv_nsec);
        break;

    case speed_oneatatime:
        /* do we skip prompting for a key press? */
        if (ctx->skip_packets == 0) {
            ctx->skip_packets = get_user_count(ctx, sp, counter);
        }

        /* decrement our send counter */
        printf("Sending packet " COUNTER_SPEC " out: %s\n", counter,
               sp == ctx->intf1 ? options->intf1_name : options->intf2_name);
        ctx->skip_packets--;

        /* leave */
        break;

    case speed_topspeed:
        break;

    default:
        errx(-1, "Unknown/supported speed mode: %d", options->speed.mode);
        break;
    }
}

static void tcpr_sleep(tcpreplay_t *ctx, sendpacket_t *sp,
        struct timespec *nap_this_time, struct timeval *now)
{
    tcpreplay_opt_t *options = ctx->options;
    bool flush =
#ifdef HAVE_NETMAP
            true;
#else
            false;
#endif


    /* don't sleep if nap = {0, 0} */
    if (!timesisset(nap_this_time))
        return;

    /* do we need to limit the total time we sleep? */
    if (timesisset(&(options->maxsleep)) && (timescmp(nap_this_time, &(options->maxsleep), >))) {
        dbgx(2, "Was going to sleep for " TIMESPEC_FORMAT " but maxsleeping for " TIMESPEC_FORMAT,
            nap_this_time->tv_sec, nap_this_time->tv_nsec, options->maxsleep.tv_sec,
            options->maxsleep.tv_nsec);
        TIMESPEC_SET(nap_this_time, &options->maxsleep);
    }

    if (flush)
        wake_send_queues(sp, options);

    dbgx(2, "Sleeping:                   " TIMESPEC_FORMAT,
            nap_this_time->tv_sec, nap_this_time->tv_nsec);

    /*
     * Depending on the accurate method & packet rate computation method
     * We have multiple methods of sleeping, pick the right one...
     */
    switch (options->accurate) {
#ifdef HAVE_SELECT
    case accurate_select:
        select_sleep(sp, nap_this_time, now, flush);
        break;
#endif

#if defined HAVE_IOPORT_SLEEP
    case accurate_ioport:
        ioport_sleep(sp, nap_this_time, now, flush);
        break;
#endif

    case accurate_gtod:
        gettimeofday_sleep(sp, nap_this_time, now, flush);
        break;

    case accurate_nanosleep:
        nanosleep_sleep(sp, nap_this_time, now, flush);
        break;

    default:
        errx(-1, "Unknown timer mode %d", options->accurate);
    }
}

/**
 * Ask the user how many packets they want to send.
 */
static uint32_t
get_user_count(tcpreplay_t *ctx, sendpacket_t *sp, COUNTER counter) 
{
    tcpreplay_opt_t *options = ctx->options;
    struct pollfd poller[1];        /* use poll to read from the keyboard */
    char input[EBUF_SIZE];
    unsigned long send = 0;

    printf("**** Next packet #" COUNTER_SPEC " out %s.  How many packets do you wish to send? ",
        counter, (sp == ctx->intf1 ? options->intf1_name : options->intf2_name));
    fflush(NULL);
    poller[0].fd = STDIN_FILENO;
    poller[0].events = POLLIN | POLLPRI | POLLNVAL;
    poller[0].revents = 0;

    if (fcntl(0, F_SETFL, fcntl(0, F_GETFL) & ~O_NONBLOCK)) 
        errx(-1, "Unable to clear non-blocking flag on stdin: %s", strerror(errno));

    /* wait for the input */
    if (poll(poller, 1, -1) < 0)
        errx(-1, "Error reading user input from stdin: %s", strerror(errno));

    /*
     * read to the end of the line or EBUF_SIZE,
     * Note, if people are stupid, and type in more text then EBUF_SIZE
     * then the next fgets() will pull in that data, which will have poor 
     * results.  fuck them.
     */
    if (fgets(input, sizeof(input), stdin) == NULL) {
        errx(-1, "Unable to process user input for fd %d: %s", fileno(stdin), strerror(errno));
    } else if (strlen(input) > 1) {
        send = strtoul(input, NULL, 0);
    }

    /* how many packets should we send? */
    if (send == 0) {
        dbg(1, "Input was less then 1 or non-numeric, assuming 1");

        /* assume send only one packet */
        send = 1;
    }

    return(uint32_t)send;
}
