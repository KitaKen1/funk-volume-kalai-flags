# Funk volume and Kalai's flag conjecture

The symmetric Funk volume conjecture is the following statement. For a convex body $K\subset\mathbb R^n$ with $K=-K$ and $0\in\operatorname{int}K$, put

$$
V_K(\tau)=\int_{\tau K}\operatorname{vol}_n\bigl((K-x)^\circ\bigr)\,dx,
\qquad
C^\circ=\{y:\langle y,z\rangle\leq1\text{ for all }z\in C\}.
$$

> [!NOTE]
> **Conjecture 1 (Symmetric Funk volume).** For every $n\geq1$, every such $K$, and every $0<\tau<1$,
>
> $$V_K(\tau)\geq\frac{(4\operatorname{artanh}\tau)^n}{n!}.$$

The associated flag conjecture is the following statement. A complete flag of an $n$-dimensional polytope $P$ is a chain of nonempty proper faces $F_0\subsetneq\cdots\subsetneq F_{n-1}$ with $\dim F_i=i$.

> [!NOTE]
> **Conjecture 2 (Kalai's flag conjecture).** Every centrally symmetric $n$-dimensional convex polytope $P$ has at least
>
> $$\#\operatorname{Flags}(P)\geq 2^n n!$$
>
> complete flags.

This repository presents a proof manuscript resolving these conjectures, prepared for submission to [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures).

**Verification status:** this is a mathematical proof manuscript. The accompanying Lean development is in progress; the two complete main theorems have not yet been closed in Lean.

The detailed proof is in **[the PDF](PDF/funk-kalai-proof.pdf)**.

## Proof

Write a symmetric polytope in an irredundant strip representation

$$P=\{X\in\mathbb R^n:|\langle a_j,X\rangle|\leq1,\ 1\leq j\leq m\}.$$

For $0<\tau<1$, the explicit holomorphic lens constructed in the PDF carries a boundary probability measure $\mu_\tau$. For every increasing nonsingular selection $I$ of $n$ rows, let $B_I$ be its row matrix and define

$$E_I=\{w\in(\partial L_\tau)^n:
\langle a_j,B_I^{-1}w\rangle\in L_\tau\text{ for every }j\}.$$

The holomorphic mass estimate gives the boundary probability inequality

$$\tag{C}\sum_I\mu_\tau^{\otimes n}(E_I)\geq1.$$

Here the pairing is extended complex linearly. This is a sum of probabilities, and a pointwise covering claim is not assumed.

The PDF proves (C) using Stokes' theorem, a holomorphic Jacobian mass estimate, and a radial limit on a fixed finite measure space. The branch densities of $\mu_\tau$ are

$$\rho_\varepsilon(t)=\frac{\tau}{4\operatorname{artanh}\tau\,(1-\varepsilon\tau t)},
\qquad \varepsilon\in\{-1,1\},\quad -1<t<1.$$

Changing variables from boundary heights to $X$, and packing the corresponding simplices into $(P-\tau X)^\circ$, gives

$$\sum_I\mu_\tau^{\otimes n}(E_I)
\leq\frac{n!}{(4\operatorname{artanh}\tau)^n}V_P(\tau).$$

Thus (C) implies the conjectured lower bound for every symmetric polytope. For a general symmetric convex body $K$ and $0<\sigma<\tau$, choose a symmetric polytope with

$$K\subseteq P\subseteq(\tau/\sigma)K.$$

Polar inclusion and $\sigma P\subseteq\tau K$ imply $V_P(\sigma)\leq V_K(\tau)$. Letting $\sigma\uparrow\tau$ proves Conjecture 1.

Finally, set $\tau_R=1-e^{-R}$. The flag upper estimate proved in the PDF is

$$\limsup_{R\to\infty}\frac{V_P(\tau_R)}{R^n}
\leq\frac{\#\operatorname{Flags}(P)}{(n!)^2}.$$

Since $4\operatorname{artanh}(1-e^{-R})=2\log(2e^R-1)$, the lower bound gives

$$\frac{2^n}{n!}\leq
\liminf_{R\to\infty}\frac{V_P(\tau_R)}{R^n}
\leq\frac{\#\operatorname{Flags}(P)}{(n!)^2}.$$

Consequently $\#\operatorname{Flags}(P)\geq2^n n!$, proving Conjecture 2. $\square$

