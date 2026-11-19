# The cost of bounding new cross terms separately

One way to pass from size $n$ to size $n+m$ is to keep an optimal signing on $n$ vertices and choose the signs on the $m$ new vertices and edges between the groups. This yields a size comparison, but bounding the cross terms in isolation has an unavoidable cost.

Define the best rectangular cross bound

```math
B_{n,m}=\min_{C\in\lbrace-1,1\rbrace^{n\times m}}
\max_{x\in\lbrace-1,1\rbrace^n,\ y\in\lbrace-1,1\rbrace^m}
|x^\top C y|.
```

Write $\mu_m=\mathbb E|\varepsilon_1+\cdots+\varepsilon_m|$ for independent uniform signs $\varepsilon_j$. For positive $n,m$ we have

```math
n\mu_m\le B_{n,m}\le n\mu_m+m\sqrt{2n\log 2}.
```

## Lower bound for any cross signing

For fixed $C$ and $y$, the maximum over $x$ is $\sum_{i=1}^n|(Cy)_i|$. If $y$ is a uniform sign vector, the expectation of each summand is $\mu_m$, for every row of $C$. The maximum over $y$ is at least the expected sum $n\mu_m$.

## Upper bound by choosing the cross signs at random

Choose all $nm$ entries of $C$ independently and uniformly. For a fixed sign vector $y$, the function $Z_y(C)=\sum_i|(Cy)_i|$ has expectation $n\mu_m$. Flipping any entry of $C$ changes at most one summand by at most two. The bounded differences inequality gives, for $t\gt0$,

```math
\Pr\{Z_y(C)\ge n\mu_m+t\}\le\exp\left(-\frac{t^2}{2nm}\right).
```

There are $2^{m-1}$ opposite pairs of $y$, and $Z_y=Z_{-y}$. A union bound with $t=m\sqrt{2n\log 2}$ gives probability at most $1/2$ that any pair violates the bound. This proves the existence of a suitable $C$.

Consequently, as $m\to\infty$ and $m/n\to0$,

```math
\frac{B_{n,m}}{n\sqrt m}\ \longrightarrow\ \sqrt{\frac{2}{\pi}}.
```

Here $\mu_m/\sqrt m\to\sqrt{2/\pi}$ by the central limit theorem and bounded second moments, and the error term after division is at most $\sqrt{2m\log 2/n}$.

## What this says about extending a signing

Using optimal signs inside both groups and an optimal cross signing gives

```math
M_{n+m}\le M_n+M_m+B_{n,m}.
```

The square-root cost in this comparison is real for the isolated cross problem. If $m$ grows sublinearly in $n$, its leading term, divided by $n^{3/2}$, is $\sqrt{2/\pi}\sqrt{m/n}$. In contrast, $(n+m)^{3/2}/n^{3/2}-1$ is asymptotic to $3m/(2n)$. Thus replacing the cross estimate by a sharper bound on the same isolated maximum cannot yield a comparison with error of order $m/n$ by this argument.

This does not show that extending an optimal signing must incur that cost in its full maximum. The three maxima in the comparison can occur at different sign vectors. A proof using small extensions would need to control that interaction or use a different size comparison.
