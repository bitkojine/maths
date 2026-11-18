# Min–max quadratic forms of signs

For each positive integer $n$, define

```math
M_n = \min_{a_{ij}\in\lbrace -1,1\rbrace}\max_{x\in\lbrace -1,1\rbrace^n}
\left|\sum_{1\le i\lt j\le n} a_{ij}x_i x_j\right|.
```

Paata Ivanisvili asks whether $M_n/n^{3/2}$ converges as $n\to\infty$.
These notes record AI-generated partial results. The convergence question remains unresolved here.

- [Original MathOverflow question](https://mathoverflow.net/questions/413935/min-max-of-a-quadratic-form-of-plus-minus-ones)
- [AI challenge on X](https://x.com/PI010101/status/2081070728422752329)

- [Proofs of the asymptotic bounds](bounds.md)
- [Convergence criterion](convergence.md)
- [Exact limit for the semidefinite relaxation](relaxation.md)

## Lean formalization

[Ivanisvili.lean](Ivanisvili.lean) defines the exact normalized sequence and the
proposition `Ivanisvili.LimitExists`. It also proves that the unnormalized
minimum is nondecreasing and gives a convergence criterion using bracketing sizes. Run `lake build` with Elan installed to check it.
