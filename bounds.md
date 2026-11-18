# Bounds on the normalized minimum

Write $M_n$ for the minimum in the [problem statement](README.md). The following estimates bound the normalized sequence:

$$
\frac{2}{3\sqrt{3}}\sqrt{\frac{2}{\pi}}
\le \liminf_{n\to\infty}\frac{M_n}{n^{3/2}}
\le \limsup_{n\to\infty}\frac{M_n}{n^{3/2}}
\le \frac12.
$$

## Lower bound

Fix any coefficient signing and split the vertices into sets $U,V$ with $|U|=k$ and $|V|=n-k$. Choose the signs on $U$ independently and uniformly. For each $v\in V$, choose its sign so that the contribution of edges from $v$ to $U$ is nonnegative. This contribution is the absolute value of a sum of $k$ independent uniform signs, with the distribution of $|S_k|$.

The resulting sum $C$ across the split has expectation $(n-k)\mathbb E|S_k|$. For any such assignment, flipping the signs on all of $V$ changes $C$ to $-C$ and preserves the sum $I$ inside both parts. Since $\max(|I+C|,|I-C|)\ge C$, the maximum absolute value of the quadratic form is at least $\mathbb E C$.

Take $k=\lfloor n/3\rfloor$. The central limit theorem and the bounded second moments of $S_k/\sqrt{k}$ give $\mathbb E|S_k|/\sqrt{k}\to\sqrt{2/\pi}$. Substituting in the estimate proves the lower bound.

## Upper bound

For each prime $q\equiv1\pmod4$, a symmetric Paley conference matrix of order $q+1$ has zero diagonal, signs off the diagonal, and operator norm $\sqrt q$. Its $n\times n$ principal submatrix $A$, for $n\le q+1$, has operator norm at most $\sqrt q$. Taking the entries above the diagonal for the coefficients gives, for every sign vector $x$,

$$
\left|\sum_{i<j} a_{ij}x_ix_j\right|
= \frac12 |x^\top A x|
\le \frac{n\sqrt q}{2}.
$$

The prime number theorem in arithmetic progressions lets us choose such primes with $q+1\ge n$ and $q/n\to1$. This proves the upper bound for the entire sequence.
