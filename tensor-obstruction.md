# A Hadamard tensor lift can worsen an optimal signing

Let $A$ be a symmetric sign matrix off the diagonal, with zero diagonal. A candidate for enlarging its signing is to replace each edge sign by a signed copy of a symmetric Hadamard matrix and choose the signs inside each vertex block. This operation can increase the normalized maximum even when the starting signing is optimal and the signs inside the vertex blocks can be chosen freely.

## An optimal signing on six vertices

Label the vertices $\star,0,1,2,3,4$. Give the five edges of the cycle on $0,1,2,3,4$ sign $-1$ and all other edges sign $+1$. Let $A$ be the resulting symmetric matrix with zero diagonal. It satisfies $A^2=5I$:

- The diagonal entries of $A^2$ are five. For an entry joining $\star$ to a cycle vertex, the four nonzero terms consist of two of each sign.
- For two cycle vertices, the term through $\star$ is $+1$. Up to rotation, reflection, and exchanging the endpoints, the cycle pair is $(0,1)$ or $(0,2)$. The three remaining cycle vertices contribute products $(-1,+1,-1)$ or $(+1,-1,-1)$, respectively, in increasing order.

Consequently, Cauchy–Schwarz gives $|x^\top A x|/2\le3\sqrt5\lt7$ for each sign vector $x$. The score is a sum of 15 signs, so its absolute value is an odd integer and is at most five. Conversely, for any signing of these 15 edges, a uniform random sign vector produces a mean square score of 15. Distinct edge monomials are orthogonal, since their product has at least one variable to an odd power. An absolute maximum of three or less would give mean square at most nine. Thus $M_6=5$, attained by $A$.

## The enlarged signing

Let $H_4$ be the symmetric matrix

```math
H_4=
\left(\begin{array}{rrrr}
 1&1&1&1\\
 1&-1&1&-1\\
 1&1&-1&-1\\
 1&-1&-1&1
\end{array}\right).
```

It has trace zero. Direct multiplication gives sign eigenvectors $p=(1,1,1,-1)$ and $m=(1,-1,-1,-1)$ with eigenvalues $2$ and $-2$. For any integer $k\ge1$, put $h=4^k$ and $H=H_4^{\otimes k}$. Then $H$ has trace zero and orthogonal sign eigenvectors $z_+=p^{\otimes k}$ and $z_-=m\otimes p^{\otimes(k-1)}$ with eigenvalues $\sqrt h$ and $-\sqrt h$. In particular,

```math
z_+^\top H z_+=h^{3/2},\qquad
z_-^\top H z_-=-h^{3/2},\qquad
z_+^\top H z_-=0.
```

Replace each base vertex by a block of size $h$. Between distinct blocks $i,j$, use the sign matrix $a_{ij}H$. Within each block $i$, choose any signing, with quadratic score $w_i(z)$ at spin assignment $z$.

Partition the six base vertices into two triples. The product of the three edge signs on a triple is its triangle sign. Complementary triples have opposite triangle signs. Indeed, the triple containing $\star$ uses two cycle vertices. If those vertices are adjacent, the triple has one negative edge and its complement has two. If they are nonadjacent, the triple has none and its complement has one.

There are ten positive triangles, and each vertex is in five of them. The vertex $\star$ is in five because there are five nonadjacent pairs on the cycle. The other five vertices are included equally often by rotational symmetry and account for the remaining 25 incidences.

For each positive triangle $S$ with negative complement $T$, choose base signs $u_i$ so that $a_{ij}u_i u_j=+1$ on $S$ and $a_{ij}u_i u_j=-1$ on $T$. This is possible independently on the two triples. Fix one vertex sign and use its two incident edges to determine the other signs. The remaining edge then has the desired sign because the triangle sign is preserved.

First, use $u_i z_+$ in each block $i\in S$ and $u_i z_-$ in each block $i\in T$. All cross terms between $S$ and $T$ vanish. The two triples each contribute three terms of $h^{3/2}$ to the score. Using the same $u_i$ and exchanging $z_+$ and $z_-$ reverses the contribution between distinct blocks. The two full scores are

```math
P(S)=6h^{3/2}+\sum_{i\in S}w_i(z_+)+\sum_{i\in T}w_i(z_-),
```

```math
N(S)=-6h^{3/2}+\sum_{i\in S}w_i(z_-)+\sum_{i\in T}w_i(z_+).
```

The factors $u_i$ do not affect $w_i$, since each term in a block uses two spins. Each vertex appears equally often in $S$ and $T$ as $S$ ranges over positive triangles, so the two scores have identical average contributions from inside the blocks. Averaging $P(S)-N(S)$ gives $12h^{3/2}$. Some pair therefore differs by at least $12h^{3/2}$, and one of its scores has absolute value at least $6h^{3/2}$.

At scale $6h$, the normalized maximum of this lift is therefore at least $6/6^{3/2}$, whereas the optimal base signing has normalized maximum $5/6^{3/2}$. This rules out a general nonincreasing bound for these tensor lifts even when all the signs inside vertex blocks are chosen freely. It does not bound the minimum over other signings at size $6h$.
