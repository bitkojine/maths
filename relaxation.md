# The semidefinite relaxation has a limit

A sign vector $x$ gives a positive semidefinite matrix $xx^\top$ with every diagonal entry equal to one. Relaxing to all such matrices yields a version of the problem whose limit is exactly $1/2$. This result applies to the relaxation. The limit for sign vectors remains open here.

Let $A$ range over symmetric $n\times n$ matrices with zero diagonal and off-diagonal entries in $\lbrace-1,1\rbrace$. Define

```math
R_n=\frac12\min_A\max_{X\succeq0,\ \mathrm{diag}(X)=\mathbf{1}}
|\mathrm{tr}(AX)|.
```

The feasible rank-one matrices give $M_n\le R_n$. We will show

```math
R_n\ge\frac{n\sqrt{n-1}}{2}.
```

Fix $n\ge2$ and $A$. For each sign $\sigma=\pm1$, semidefinite duality gives

```math
\max_{X\succeq0,\ \mathrm{diag}(X)=\mathbf{1}}
\mathrm{tr}(\sigma AX)
=
\min_{D_\sigma\text{ diagonal},\ D_\sigma-\sigma A\succeq0}
\mathrm{tr}(D_\sigma).
```

The primal is strictly feasible at $X=I$, so the dual minimum is attained. Take these minimizing diagonals and put $D=(D_++D_-)/2$ and $E=(D_+-D_-)/2$. The two inequalities become $-D\preceq A-E\preceq D$. The diagonal entries of $D$ are positive. A zero entry would force the corresponding diagonal entry of both positive semidefinite slacks to be zero, and hence their corresponding rows to be zero, contradicting the signed off-diagonal entries.

Write $d_i=D_{ii}$. The symmetric matrix $B=D^{-1/2}(A-E)D^{-1/2}$ satisfies $-I\preceq B\preceq I$, hence $B^2\preceq I$. Its off-diagonal entries have squared magnitudes $1/(d_i d_j)$. Thus each row satisfies

```math
\frac{1}{d_i}\sum_{j\ne i}\frac{1}{d_j}
\le (B^2)_{ii}\le1.
```

Multiplying by $d_i$, summing, and applying Cauchy–Schwarz gives

```math
\sum_i d_i
\ge(n-1)\sum_i\frac{1}{d_i}
\ge\frac{(n-1)n^2}{\sum_i d_i}.
```

It follows that $\mathrm{tr}(D)\ge n\sqrt{n-1}$. The larger of $\mathrm{tr}(D_+)$ and $\mathrm{tr}(D_-)$ is at least their average $\mathrm{tr}(D)$. Taking the minimum over $A$ proves the lower bound.

For the upper bound, the [Paley construction](bounds.md#upper-bound) gives $A$ with $\left\| A\right\|_{\mathrm{op}}\le\sqrt q$, where $q/n\to1$. For every feasible $X$, positivity and $\mathrm{tr}(X)=n$ give $|\mathrm{tr}(AX)|\le n\sqrt q$. Therefore $R_n/n^{3/2}\to1/2$.

This bounds what the relaxation can prove: choosing separate optimal diagonals for the two signs still cannot certify an asymptotic upper bound below $1/2$.
