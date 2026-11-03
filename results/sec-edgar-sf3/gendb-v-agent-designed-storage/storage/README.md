# Storage

The storages the queries read, and the storages whose parts they inherit. A storage that extends another includes the parts it inherits in its stored bytes; together the storages hold 2.69 GB, each part counted once.

| Storage | Added by | Stored bytes | Extends | Read by |
|---|---|---:|---|---|
| [num](num/v1/README.md) | workload agent | 1649103650 | — | q3, q4, q6 |
| [num_tvg](num_tvg/v1/README.md) | q24 agent | 1719332734 | num | q24 |
| [num_vord](num_vord/v1/README.md) | q2 agent | 1964317738 | num | q2 |
| [pre](pre/v1/README.md) | workload agent | 492316115 | — | q1, q4, q6, q24 |
| [sub](sub/v1/README.md) | workload agent | 20797305 | — | q2, q6 |
| [sub_fy](sub_fy/v1/README.md) | q3 agent | 22175465 | sub | q3 |
| [sub_sic](sub_sic/v1/README.md) | q4 agent | 22864545 | sub_fy | q4 |
| [tag](tag/v1/README.md) | workload agent | 125473496 | — | — (its parts are inherited) |
| [tag_tv](tag_tv/v1/README.md) | q4 agent | 135625288 | tag | q4 |
