Tarjan and Kosaraju
-------------------

# Main files

## Proofs of Tarjan strongly connected component algorithm (independent from each other)
* `tarjan_rank.v` *(751 sloc)*: proof with rank
* `tarjan_rank_bigmin.v` *(806 sloc)*: same proof but with a `\min_` instead of multiple inequalities on the output rank
* `tarjan_num.v` *(1029 sloc)*: same proof as `tarjan_rank_bigmin.v` but with serial numbers instead of ranks
* `tarjan_nocolor.v` *(548 sloc)*: new proof, with ranks and without colors, less fields in environement and less invariants, preconditions and postconditions.
* `tarjan_nocolor_optim.v` *(560 sloc)*: same proof as `tarjan_nocolor.v`, but with the serial number field of the environement restored, and passing around stack extensions as sets.

## Proof of Kosaraju strongly connected component algorithm
* `Kosaraju.v` *(679 sloc)*: proof of Kosaraju connected component algorithm

## Extra library files
* `bigmin.v` *(137 sloc)*: extra library to deal with \min(i in A) F i
* `extra.v` *(265 sloc)*: naive definitions of strongly connected components and various basic extentions of mathcomp libraries on paths and fintypes.

# Authors:

Cyril Cohen, Jean-Jacques Lévy and Laurent Théry
