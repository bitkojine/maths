# A criterion for convergence

Let $M_n$ be the unnormalized minimum in the [problem statement](README.md). For $m\le n$, we have $M_m\le M_n$. To see this, take an optimal signing on $n$ vertices and keep the first $m$. Fix the signs on those $m$ vertices and average over independent uniform signs on the other vertices. Terms involving any of the other vertices have zero expectation, so the quadratic form on the retained vertices is the average of the original form. Its absolute value is therefore at most $M_n$. Maximizing over the retained signs and using the definition of $M_m$ gives the claim.

Suppose there is an increasing sequence $n_j$ with $n_{j+1}/n_j\to 1$ and $M_{n_j}/n_j^{3/2}\to L$. For $n_j\le n\le n_{j+1}$, monotonicity gives

```math
\frac{M_{n_j}}{n_{j+1}^{3/2}}\le
\frac{M_n}{n^{3/2}}\le
\frac{M_{n_{j+1}}}{n_j^{3/2}}.
```

Both outer terms converge to $L$, so the full sequence converges to $L$. In particular, it would suffice to find signings at such closely spaced sizes with normalized maxima approaching the liminf. The [conference matrix construction](bounds.md#upper-bound) supplies an upper bound but does not identify the liminf.
