# Storage `li_partdir`

facts unchanged (75 inherited parts), then I64 [mode, kmin] and U32 offsets: in mode 1, positions offs[k - kmin] .. offs[k - kmin + 1] of facts' l_partkey key index hold exactly the stored lineitem rows whose l_partkey is k

Units: keys are bigint l_partkey values; offsets are positions (0 .. rows) in the facts l_partkey key index (LI_KEYIDX codes + bases), U32

## Tables and columns

- `lineitem`: l_partkey, l_quantity, l_extendedprice

## Parts

- lineitem: I64 [mode, kmin]: directory mode (1: dense directory present) and smallest l_partkey
- lineitem: U32 directory offsets into the facts l_partkey key index, nkeys + 1 entries (mode 1)

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
