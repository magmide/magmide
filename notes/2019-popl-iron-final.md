pretty simple so far, just saying none of the concurrent separation logics enable tracking *obligations*, merely correctness in the sense of not *doing* something incorrect, rather than *incorrectly forgetting to do something necessary*.

this is a problem whenever we're using persistent/duplicable/shareable invariants, which can be copied arbitrarily to be given to different threads. doing this is necessary in fork-style concurrency (vs "structured" concurrency in which the language syntax itself determines where invariants exist).
since they're duplicable, they can be thrown away

the main way they're going to solve this problem is with what they're calling "trackable resources"
the first one is the "trackable points-to connective" `l ->_pi v`, where pi is a rational number describing what fraction of the heap we have control or knowledge of. `pi = 1` means we own the whole thing, and `pi < 1` means someone else has some control

then they define Iron++, which defines "trackable invariants" (rather than resources), and Iron++ is linear rather than affine (it doesn't have the weakening rule, so you can't throw away resources). this means these invariants aren't duplicable, but instead have to be "split"

getting into it, they define some rules, in which the `e_pi` proposition is like an empty heap, equivalent to the permission to allocate.

emp-split:
`e_pi1 ∗ e_pi2 <-> e_(pi1 + pi2)`

pt-split:
`(l -->_pi1 v) * (e_pi2) <-> (l -->_(pi1 + pi2) v)`

since `e_pi` propositions allow us to demonstrate we've deallocated memory, we can prove a program doesn't leak memory by giving it a hoare triple of `{ e_pi } program { e_pi }` where pi is equal in pre and post, for any pi


I got all I needed from this paper I think
