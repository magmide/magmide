this one is actually getting somewhere. it's basically the same paper as `indexing-foundational-proof-carrying-code` but actually gives some intuitions for what they're talking about with recursive types

the important thing it seems is this mu operator

```
µF ≡ {<k, v> | <k, v> ∈ F^(k+1)(⊥)}

µ(F) = λkλv.∀τ. ncomp(F, k + 1, ⊥, τ) ⇒ τ k v

where ncomp(F, k, g, h) means informally that F^k (g) = h

ncomp(f, n, x, y) can be defined as,
  ∀ g.
    (∀z. g(f, 0, z, z))
    ⇒ (∀m, z1, z2 .m > 0 ⇒ g (f, m − 1, z1, z2 ) ⇒ g (f, m, z1, f(z2)))
    ⇒ g (f, n, x, y).
```
