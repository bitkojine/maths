# Comparing sizes through exponential averages

Separate maxima for the old and new edge sets give a square-root cost when a small block is added. Exponential averaging permits a comparison whose cross term is linear in the fraction added, at any fixed averaging parameter.

For a signing $A$, write $Q_A(x)$ for its quadratic score. For $\beta\gt0$, define

```math
F_n(\beta)=\frac1n\log\left(
  \min_A\mathbb E_x \exp\left(\frac{\beta}{\sqrt n}|Q_A(x)|\right)
\right),
```

where the spins are uniform. One maximizer contributes at least $2^{-n}$ of the exponential average, and the average is at most its largest term. Therefore

```math
\frac{M_n}{n^{3/2}}-\frac{\log 2}{\beta}
\le\frac{F_n(\beta)}{\beta}
\le\frac{M_n}{n^{3/2}}.
```

The approximation is uniform in $n$. If $F_n(\beta)$ converges in $n$ for an unbounded set of fixed parameters $\beta$, then the normalized min–max values converge by the Cauchy criterion. Given an error tolerance, first fix a sufficiently large parameter and then compare two sufficiently late terms using this inequality.

## A joint comparison

Let $N=n+m$, $\alpha=n/N$, $\gamma=m/N$, and $t=\beta/\sqrt N$. Then

```math
\max\left\lbrace
  \alpha F_n(\beta\sqrt\alpha),\
  \gamma F_m(\beta\sqrt\gamma)
\right\rbrace
\le F_N(\beta)
\le \alpha F_n(\beta\sqrt\alpha)+\gamma F_m(\beta\sqrt\gamma)
  +\frac{\beta^2\alpha\gamma}{2}+\frac{\log 2}{N}.
```

For the lower bound, fix any signing at size $N$. Conditional on the first group's spins, the mean of all terms involving the second group is zero. The function $s\mapsto e^{t|s|}$ is convex, so Jensen's inequality bounds the conditional exponential average from below by the exponential of the absolute score on the first group. Average over the first group and minimize over the full signing. Interchanging the groups gives the other lower bound.

For the upper bound, choose optimal signings for the two groups at parameters $\beta\sqrt\alpha$ and $\beta\sqrt\gamma$, then choose the cross edges independently and uniformly. Fix spins in both groups. Write $u,v$ for the scores inside the two groups and $w$ for the cross score. The two exponential moments of $w$ at $t$ and $-t$ both equal $(\cosh t)^{nm}$. Since $e^{t|s|}\le e^{ts}+e^{-ts}$,

```math
\mathbb E_{\mathrm{cross}} e^{t|u+v+w|}
\le(\cosh t)^{nm}(e^{t(u+v)}+e^{-t(u+v)})
\le 2(\cosh t)^{nm}e^{t|u|}e^{t|v|}.
```

Average this inequality over both groups' spins, which are independent. Some cross signing attains at most the resulting bound. Taking logarithms, dividing by $N$, and using $\log\cosh t\le t^2/2$ gives the comparison.

## Remaining gap

This controls the cross contribution in the exponential average without assuming that the three individual maxima occur together. For fixed $\beta$, its term $\beta^2\alpha\gamma/2$ scales linearly for a small added group. It remains a positive constant for a proportional split, and it grows as $\beta$ increases. The bound alone does not establish a limit for $F_n(\beta)$ or for the original normalized minima.
