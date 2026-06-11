# Quick probes (microbenchmarks that resolved an idea without a full experiment dir)

- `soa_catalog_microbench.c` — N18 SoA-vs-AoS page-catalog search. Result: 1.00–1.05× at realistic
  catalog sizes (16–1024 pages, cache-resident), only 1.53× at 4096+ pages (16M-record segments).
  Verdict: not worth the refactor. (gcc -O3 -march=native soa_catalog_microbench.c && ./a.out)
