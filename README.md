# A Normed Real Vector Space with Compact Unit Ball is Finite Dimensional

We give a proof of this theorem in lean using [mathlib](https://github.com/leanprover-community/mathlib). This is the precise statement
```lean
theorem compact_unit_ball_implies_finite_dim : 
    compact (closed_ball 0 1 : set V) → vector_space.dim ℝ V < cardinal.omega
```

The mathematical proof we formalize goes like this:
Let V be a normed real vector space and assume its closed unit ball B
is compact. Cover B with finitely many open balls of radius 1/2 with 
centers `a_1, ..., a_N`. It suffices to show show that any v in B is in the span of `a_1, ..., a_N`. So let v in B and define a sequence `u n` by 
`u 0 = v` and `u (n+1) = 2 (u n - b_n)`, where `b_n` is of the `a_1, ..., a_N` such that `|u n - b_n| < 1/2`. Then `v n = b 0 + 1/2 b 1 + ... + 1/2^n b n` satisfies
`|v n - v| < 1/2^(n+1)` and hence `v n` converges to `v` and since the span of a finite set is closed this implies that `v` is in the span of `a_1, ..., a_N`.
