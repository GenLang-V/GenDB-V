# Storage

The storages the queries read, and the storages whose parts they inherit. A storage that extends another includes the parts it inherits in its stored bytes; together the storages hold 102.70 GB, each part counted once.

| Storage | Added by | Stored bytes | Extends | Read by |
|---|---|---:|---|---|
| [cust_phoneidx](cust_phoneidx/v1/README.md) | q22 agent | 4152261847 | custpart | q22 |
| [custpart](custpart/v1/README.md) | workload agent | 4092261639 | — | q02, q03, q05, q07, q08, q09, q10, q13, q14, q16, q17, q18, q19, q22 |
| [factext](factext/v1/README.md) | workload agent | 29778644472 | — | — (its parts are inherited) |
| [factext_trisig](factext_trisig/v1/README.md) | q13 agent | 32178644472 | factext | — (its parts are inherited) |
| [factext_trislice](factext_trislice/v1/README.md) | q13 agent | 34578644472 | factext_trisig | q13 |
| [facts](facts/v1/README.md) | workload agent | 27153218258 | — | q01, q03, q04, q05, q06, q07, q09, q10, q12, q13, q14, q19, q21 |
| [factsdir](factsdir/v1/README.md) | q08 agent | 29633218294 | facts | q08 |
| [factspk](factspk/v1/README.md) | q09 agent | 27233218270 | facts | q09 |
| [li_bits](li_bits/v1/README.md) | q06 agent | 32178976114 | facts | q06 |
| [li_okmode](li_okmode/v1/README.md) | q12 agent | 28353256230 | li_okruns | q12 |
| [li_okruns](li_okruns/v1/README.md) | q03 agent | 27753218262 | facts | q03, q05, q07, q12 |
| [li_ordruns](li_ordruns/v1/README.md) | q04 agent | 27303218258 | facts | q04, q21 |
| [li_pairmask](li_pairmask/v1/README.md) | q01 agent | 27155562162 | facts | q01 |
| [li_partdir](li_partdir/v1/README.md) | q17 agent | 27233218278 | facts | q19 |
| [li_pkdate](li_pkdate/v1/README.md) | q20 agent | 30833445698 | facts | q20 |
| [li_pkqty](li_pkqty/v1/README.md) | q17 agent | 30833445698 | facts | q17 |
| [li_pkship](li_pkship/v1/README.md) | q19 agent | 30233407788 | facts | q19 |
| [liruns](liruns/v1/README.md) | q18 agent | 28503584522 | facts | q18 |
| [lisupp](lisupp/v1/README.md) | q15 agent | 29553443122 | facts | q15 |
| [orders_custidx](orders_custidx/v1/README.md) | q13 agent | 660000016 | — | q13, q22 |
| [part_bcs](part_bcs/v1/README.md) | q19 agent | 4172461667 | custpart | q17, q19 |
| [part_btsidx](part_btsidx/v1/README.md) | q16 agent | 4173011667 | custpart | q16 |
| [part_nameidx](part_nameidx/v1/README.md) | q20 agent | 4172261639 | custpart | q20 |
| [part_sztyidx](part_sztyidx/v1/README.md) | q02 agent | 80034318 | — | q02 |
| [partsig](partsig/v1/README.md) | q09 agent | 4252261639 | custpart | q09 |
| [ps_suppidx](ps_suppidx/v1/README.md) | q11 agent | 324000020 | — | q11 |
| [psrun](psrun/v1/README.md) | q16 agent | 11801602792 | suppliers | q16 |
| [supp_trisig](supp_trisig/v1/README.md) | q16 agent | 11817593016 | suppliers | q16 |
| [suppliers](suppliers/v1/README.md) | workload agent | 11801593016 | — | q02, q05, q07, q08, q09, q10, q11, q15, q16, q20, q21 |
| [suppliers_psrun](suppliers_psrun/v1/README.md) | q02 agent | 11801593032 | suppliers | q02, q11, q20 |
| [suppliers_rank](suppliers_rank/v1/README.md) | q02 agent | 12129593036 | suppliers | q02 |
