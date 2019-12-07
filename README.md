# A Normed Vector Space over a Nondiscrete Normed Complete Field with Compact Closed Unit Ball is Finite Dimensional

We give a proof of this theorem in lean using [mathlib](https://github.com/leanprover-community/mathlib). This is the precise statement
```lean
theorem compact_unit_ball_implies_finite_dim 
    (Hcomp : compact (closed_ball 0 1 : set V)) : finite_dimensional k V
```

The mathematical proof we formalize goes like this:
Let V be a normed vector space over k and assume its closed unit ball B
is compact. Because the norm on k is nontrivial there exists x in k such that
`0 < |x| < 1` Cover B with finitely many open balls of radius `r = |x|` with 
centers `a_1, ..., a_N`. It suffices to show show that any v in B is in the span of `a_1, ..., a_N`. So let v in B and define a sequence `u n` by 
`u 0 = v` and `u (n+1) = 1/x (u n - b_n)`, where `b_n` is of the `a_1, ..., a_N` such that `|u n - b_n| < r`. Then `v n = b 0 + x b 1 + ... + x^n b n` satisfies
`|v n - v| < r^(n+1)` and hence `v n` converges to `v` and since the span of a finite set is closed over a complete field this implies that `v` is in the span of `a_1, ..., a_N`.
