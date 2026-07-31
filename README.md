# Tree packing conjecture verification code

(Coded for and used within "The tree packing conjecture holds for n ≤ 11")

| file | role |
|---|---|
| `tpc.c` | solver |
| `tpc_twin.py` | second solver (independent, diff order & heuristics) |
| `verify_certs.py` | certificate checker (E1–E6) |
| `count_twin.py` | naive packing counter |
| `tpc_sat.py` | CNF encoding, kissat, drat trim |
| `audit_trees.py` | networkx & OEIS A000055 tree validation |
| `gate.sh` | gate |
| `gen_trees.sh` | gentreeg (nauty) tree generator |

Method, verification protocol and certificate format are specified in my paper.

MIT licence.
