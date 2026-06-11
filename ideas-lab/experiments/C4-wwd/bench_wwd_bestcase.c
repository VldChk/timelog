#define _POSIX_C_SOURCE 200809L

#include "timelog/timelog.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
static long long ns(void){struct timespec t;clock_gettime(CLOCK_THREAD_CPUTIME_ID,&t);return (long long)t.tv_sec*1000000000LL+t.tv_nsec;}
static int drain(tl_timelog_t* tl){int n=0;while(tl_maint_step(tl)==TL_OK){n++;if(n>5000000)break;}return n;}
int main(int argc,char**argv){
  long long NW=argc>1?atoll(argv[1]):200, PW=argc>2?atoll(argv[2]):5000, WS=1000;
  tl_config_t cfg; tl_config_init_defaults(&cfg);
  cfg.maintenance_mode=TL_MAINT_DISABLED; cfg.window_size=WS; cfg.max_delta_segments=2; cfg.on_drop_handle=NULL;
  tl_timelog_t* tl=NULL; tl_open(&cfg,&tl);
  // build L1 per window
  for(long long w=0;w<NW;w++){for(long long j=0;j<PW;j++)tl_append(tl,w*WS+j,(unsigned long long)(w*WS+j));tl_flush(tl);drain(tl);}
  tl_snapshot_t* s0=NULL;tl_snapshot_acquire(tl,&s0);tl_stats_t a;tl_stats(s0,&a);tl_snapshot_release(s0);
  // delete ALL windows fully (one contiguous tombstone), then a single far L0 record to trigger
  tl_delete_range(tl,0,NW*WS);
  // add one churn record in the LAST window so output is nonempty + selection spans all
  tl_append(tl,(NW-1)*WS+1,(unsigned long long)((NW-1)*WS+1));
  tl_flush(tl);
  long long t0=ns(); tl_compact(tl); int st=drain(tl); for(int i=0;i<4;i++){tl_compact(tl);st+=drain(tl);} long long cpu=ns()-t0;
  tl_snapshot_t* s1=NULL;tl_snapshot_acquire(tl,&s1);tl_stats_t b;tl_stats(s1,&b);
  tl_iter_t* it=NULL; tl_iter_range(s1,0,NW*WS,&it); unsigned long long cnt=0,sum=0; tl_record_t r;
  while(tl_iter_next(it,&r)==TL_OK){cnt++;sum+=(unsigned long long)r.ts;} tl_iter_destroy(it); tl_snapshot_release(s1);
  printf("{\"l1_built\":%llu,\"l1_after\":%llu,\"l1_merged\":%llu,\"pages_after\":%llu,\"cpu_ms\":%.3f,\"qcount\":%llu,\"qsum\":%llu}\n",
    (unsigned long long)a.segments_l1,(unsigned long long)b.segments_l1,
    (unsigned long long)(b.compaction_select_l1_inputs-a.compaction_select_l1_inputs),
    (unsigned long long)b.pages_total,cpu/1e6,cnt,sum);
  tl_close(tl); return 0;
}
