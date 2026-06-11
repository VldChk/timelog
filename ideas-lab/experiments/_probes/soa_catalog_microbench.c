#define _POSIX_C_SOURCE 200809L

/* N18: AoS (32B tl_page_meta) vs SoA (dense int64 max_ts[]) catalog binary search. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
typedef int64_t ts_t; typedef struct page page_t;
typedef struct { ts_t min_ts, max_ts; uint32_t count, flags; page_t* page; } meta_t; /* 32B AoS */
static inline size_t lb_aos(const meta_t* a, size_t n, ts_t x){ const meta_t* f=a; size_t L=n;
    while(L>0){size_t h=L/2; f += (size_t)(f[h].max_ts < x)*(L-h); L=h;} return (size_t)(f-a); }
static inline size_t lb_soa(const ts_t* a, size_t n, ts_t x){ const ts_t* f=a; size_t L=n;
    while(L>0){size_t h=L/2; f += (size_t)(f[h] < x)*(L-h); L=h;} return (size_t)(f-a); }
static long ns(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec*1000000000L+t.tv_nsec;}
static uint64_t xr(uint64_t*s){uint64_t x=*s;x^=x<<13;x^=x>>7;x^=x<<17;return(*s=x);}
int main(void){
  size_t Ns[]={16,64,256,1024,4096,16384}; uint64_t sd=12345; size_t M=1u<<20;
  ts_t* q=malloc(M*sizeof(ts_t));
  printf("%-8s %12s %12s %9s   (catalog entries; SoA=dense max_ts[])\n","N","AoS 32B","SoA 8B","speedup");
  for(size_t ni=0;ni<sizeof(Ns)/sizeof(Ns[0]);ni++){size_t n=Ns[ni];
    meta_t* a=malloc(n*sizeof(meta_t)); ts_t* s=malloc(n*sizeof(ts_t));
    for(size_t i=0;i<n;i++){a[i].max_ts=(ts_t)(2*i);a[i].min_ts=(ts_t)(2*i);a[i].count=4096;a[i].page=0;s[i]=(ts_t)(2*i);}
    for(size_t i=0;i<M;i++)q[i]=(ts_t)(xr(&sd)%(2*n));
    volatile size_t sink=0; double ba=1e30,bs=1e30;
    for(int r=0;r<7;r++){long t=ns();size_t acc=0;for(size_t i=0;i<M;i++)acc+=lb_aos(a,n,q[i]);sink^=acc;double d=(double)(ns()-t)/M;if(d<ba)ba=d;}
    for(int r=0;r<7;r++){long t=ns();size_t acc=0;for(size_t i=0;i<M;i++)acc+=lb_soa(s,n,q[i]);sink^=acc;double d=(double)(ns()-t)/M;if(d<bs)bs=d;}
    printf("%-8zu %12.2f %12.2f %8.2fx\n",n,ba,bs,ba/bs); free(a);free(s);
  }
  return 0;
}
