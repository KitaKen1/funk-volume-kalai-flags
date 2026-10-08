# Kalai's full flag conjecture in Lean 4

> **Conjecture (Kalai's full flag conjecture).** Every centrally symmetric
> $n$-dimensional convex polytope $P$, with $n\ge1$, satisfies
>
> $$\#\operatorname{FullFlag}(P)\ge2^n n!.$$

This repository presents a **Lean 4 proof** of this conjecture.

Contributions:

1. **FC-style Lean statement formalization.**
2. **A Lean 4 proof of Kalai's full flag conjecture.**

SubContributions (see appendix):

1. **FC-style Lean formalization of the numerical Funk-volume lower bound.**
2. **A Lean 4 proof of the numerical Funk-volume lower bound.**

**Try it in Lean4Web:** [open the complete proof in one file](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ffunk-volume-kalai-flags%2Fmain%2Flean4web%2FFunkKalaiLean4Web.lean) (Lean **v4.35.0-rc4**).

## Formal Conjectures targets

[KalaiFullFlags.lean](FClikelean/KalaiFullFlags.lean) states **Kalai's full flag
conjecture** in the namespace `Funk.FormalConjectures`:

```lean
@[category research solved, AMS 52,
    formal_proof using lean4 at "https://github.com/KitaKen1/funk-volume-kalai-flags/blob/main/lean/Funk/MainTheorems.lean"]
theorem kalaiFullFlags :
    answer(True) ↔
      ∀ (n : ℕ), 1 ≤ n → ∀ (P : Set (Fin n → ℝ)),
        IsFinitePolytope P → IsSymmetricConvexBody P →
          Finite (FullFlag P) ∧
            2 ^ n * n.factorial ≤ Nat.card (FullFlag P) := by
  sorry
```

[SymmetricFunkVolume.lean](FClikelean/SymmetricFunkVolume.lean) states the
**numerical Funk-volume lower bound** in the namespace `FunkVolume`:

```lean
@[category research solved, AMS 52,
    formal_proof using lean4 at "https://github.com/KitaKen1/funk-volume-kalai-flags/blob/main/lean/Funk/MainTheorems.lean"]
theorem symmetricFunkVolume :
    answer(True) ↔
      ∀ (n : ℕ), 1 ≤ n → ∀ (K : Set (Fin n → ℝ)),
        IsSymmetricConvexBody K → ∀ τ : ℝ, 0 < τ → τ < 1 →
          funkVolume K τ < ⊤ ∧
            ENNReal.ofReal ((4 * Real.artanh τ) ^ n / (n.factorial : ℝ)) ≤
              funkVolume K τ := by
  sorry
```

Both files give explicit geometric definitions and use the official Formal
Conjectures annotations. `by sorry` is the FC problem-statement placeholder.
The complete proofs are in
[MainTheorems.lean](lean/Funk/MainTheorems.lean) and the Lean4Web file.

## Mathematical explanation (AI generated)

Let $n\ge1$, and let $K=-K\subset\mathbb R^n$ be a compact convex body
with $0\in\operatorname{int}K$. We first prove the Funk-volume lower bound
for polytopes, extend it to $K$ by outer approximation, and then compare it
with an upper bound expressed in terms of complete flags. Here
$A^\circ=\{y:\langle y,a\rangle\le1\text{ for every }a\in A\}$, and all
volumes and integrals use ordinary, unnormalized Lebesgue measure.

**1. A probability whose density matches polar volume.** Fix $0<\tau<1$.
A symmetric full-dimensional polytope has a strip presentation

$$P=\{X:|\langle a_j,X\rangle|\le1,\ 1\le j\le m\}.$$

Choose one vertex from each opposite pair of vertices of $P^\circ$ as the
rows $a_j$. This makes the presentation signed irredundant: no $a_j$ belongs
to the convex hull of the other signed rows. The purpose of the following
complex construction is to obtain a boundary probability density containing
the factors $(1-\varepsilon\tau t)^{-1}$ that occur in translated polars.

Put $b=2\operatorname{artanh}\tau/\pi$, $c=\sqrt{1-\tau^2}$ and
$\kappa=4b/(\pi\tau)$. The map

$$F(z)=\kappa\sum_{j=0}^\infty
\frac{(-1)^jz^{2j+1}}{(2j+1)(2j+1-ib)}$$

maps the unit disk biholomorphically onto the interior of a centrally
symmetric convex lens $L_\tau$, and extends to a homeomorphism of the
boundaries. Here is how its geometry is established. Uniform convergence
gives continuity on the closed disk, and differentiation gives
$zF'(z)-ibF(z)=\kappa\arctan z$. On the right semicircle the imaginary part is

$$T(\theta)=\frac{1-ce^{-b\theta}}{\tau},\qquad
-\pi/2\le\theta\le\pi/2,\qquad
T'=\frac b\tau(1-\tau T)>0.$$

The same differential equation shows that the right boundary, as a graph
over its height, is strictly concave; oddness gives the strictly convex
left boundary. These graphs form a convex Jordan curve, and the argument
principle then gives biholomorphy. Write the graphs as $f_\varepsilon(t)+it$,
where $\varepsilon=+1$ or $-1$ and $-1<t<1$. Their second derivatives never
vanish. If $\mu_\tau$ is the image under $F$ of uniform measure on the unit
circle, the change of variable $t=T(\theta)$ gives the joint density

$$\rho_\varepsilon(t)=
\frac{\tau}{4\operatorname{artanh}\tau\,(1-\varepsilon\tau t)}.$$

Each branch has probability $1/2$; branch and height have this joint law.
For an increasing selection $I=(i_1,\ldots,i_n)$ with invertible row matrix
$B_I$, consider the event

$$E_I=\{w\in(\partial L_\tau)^n:
\langle a_j,B_I^{-1}w\rangle\in L_\tau\text{ for all }j\}.$$

Thus $n$ independently sampled boundary values determine a complex point,
and $E_I$ says that every remaining row constraint is satisfied. The two
estimates we need are

$$1\ \le\ \sum_I\mu_\tau^{\otimes n}(E_I)
\ \le\ \frac{n!}{(4\operatorname{artanh}\tau)^n}V_P(\tau).\tag{1}$$

**2. The geometric upper estimate in (1).** Fix signs
$\varepsilon=(\varepsilon_1,\ldots,\varepsilon_n)$. At a point $X\in P$,
the corresponding real part of the interpolant is
$Y=B_I^{-1}(f_{\varepsilon_k}(\langle a_{i_k},X\rangle))_k$.
Let $S_{I,\varepsilon}$ be the set of $X$ for which $Y+iX$ satisfies all
the lens constraints, and form the simplex

$$\Delta_{I,\varepsilon}(X)=\operatorname{conv}\left(0,
\frac{\varepsilon_k a_{i_k}}
{1-\varepsilon_k\tau\langle a_{i_k},X\rangle},\ 1\le k\le n\right).$$

Its vertices lie in $(P-\tau X)^\circ$, and all denominators are positive.
The determinant formula for its volume and the change of variable $t=B_IX$
give, respectively,

$$\operatorname{vol}\Delta_{I,\varepsilon}(X)=
\frac{|\det B_I|}{n!\prod_k(1-\varepsilon_k\tau\langle a_{i_k},X\rangle)},$$

$$\mu_\tau^{\otimes n}(E_I)=
n!\left(\frac{\tau}{4\operatorname{artanh}\tau}\right)^n
\sum_\varepsilon\int_{S_{I,\varepsilon}}
\operatorname{vol}\Delta_{I,\varepsilon}(X)\,dX.\tag{2}$$

The crucial geometric fact is that these feasible simplices have disjoint
interiors for almost every $X$. If two interpolants have different real
parts $Y,Z$, the functional $v\mapsto\langle v,Y-Z\rangle$ separates their
simplices: the selected right or left endpoint of each horizontal lens
slice determines the required sign.

Coincident real parts require an additional row to lie on the lens boundary.
Writing that row as $a_j=\sum_k d_k a_{i_k}$, signed irredundancy forces two
coefficients $d_r,d_s$ with $r\ne s$ to be nonzero. In height coordinates,
the additional boundary equation has the form

$$H(t)=\sum_k d_k f_{\varepsilon_k}(t_k)-f_\delta(d\cdot t)=0,
\qquad \partial_s\partial_r H=-d_sd_r f_\delta''(d\cdot t)\ne0.$$

Where $\partial_rH\ne0$, its zero set is locally a hypersurface. The
remaining part lies in $\{\partial_rH=0\}$, which is also locally a
hypersurface because its $s$-derivative is nonzero. Both parts are null.
Endpoint heights lie in finitely many hyperplanes, so the finitely many
exceptional choices still give a null set. Consequently, the sum of the
feasible simplex volumes is at most the volume of $(P-\tau X)^\circ$ almost
everywhere. Integrating (2) and substituting $x=\tau X$ proves the upper
estimate in (1); the Jacobian $\tau^n$ cancels exactly.

**3. The analytic lower estimate in (1).** Put $g=F^{-1}$ and
$\Omega=\{z\in\mathbb C^n:\langle a_j,z\rangle\in\operatorname{int}L_\tau
\text{ for all }j\}$. For an integer $k\ge1$, set
$f_k(z)=(g(\langle a_j,z\rangle)^k)_j$ and $u_k=|f_k|^2$.
The rows span $\mathbb R^n$, so the common zero is isolated, the leading
homogeneous terms have degree $k$ and no nonzero common zero, and the
sublevels $u_k\le s<1$ are compact in $\Omega$.

These properties yield the holomorphic mass estimate

$$M_k:=n!\sum_I\int_{\{z\in\Omega:u_k(z)<1\}}
|\det D(f_k)_I(z)|^2\,dV_{2n}(z)\ \ge\ (\pi k)^n.\tag{3}$$

To see the reason for this estimate, use
$d^c=\tfrac i2(\bar\partial-\partial)$.
The form $dd^c\log u_k$ is positive semidefinite away from the zero, by
Cauchy–Schwarz. Stokes' theorem on a regular sublevel, with a small ball
around zero removed, therefore bounds its outer boundary flux below by
the inner flux. The latter tends to the flux of the degree-$k$ leading
homogeneous terms. On the sphere, invariance under common phase rotation
makes this flux unchanged by deforming its one-form to
$k\,d^c\log|z|^2$; its value is $(2\pi k)^n$.
Thus $\int_{u_k<s}(dd^cu_k)^n\ge s^n(2\pi k)^n$.
Letting $s\uparrow1$ and using
$(dd^cu_k)^n=2^n n!\sum_I|\det D(f_k)_I|^2dV_{2n}$ proves (3).
For these power maps, every positive level of $u_k$ is regular.

Now use the coordinates $v_\ell=g(\langle a_{i_\ell},z\rangle)$ for a fixed
basis $I$, followed by $v_\ell=t_\ell^{1/(2k)}e^{i\theta_\ell}$.
The radial Jacobian reduces (3) to a probability on the fixed simplex
$\{t_i>0:\sum_i t_i<1\}$, with density $n!$, and independent uniform
angles. Denote this product probability by $\nu$. If $\chi_{I,k}$ indicates
that the reconstructed point
$B_I^{-1}(F(t_i^{1/(2k)}e^{i\theta_i}))_i$ belongs to $\Omega$ and has
$u_k<1$, the exact change of variables is

$$\frac{M_k}{(\pi k)^n}=\sum_I\int\chi_{I,k}\,d\nu\ \ge1.$$

For every positive $t_i$, the radii tend to $1$. If the limiting boundary
interpolant violates a constraint, closedness of $L_\tau$ makes that
constraint fail for all sufficiently large $k$. Hence
$\limsup_k\chi_{I,k}\le\mathbf1_{E_I}$.
The indicators are bounded by $1$ on a fixed probability space, and there
are finitely many bases. Reverse Fatou therefore gives
$1\le\sum_I\mu_\tau^{\otimes n}(E_I)$, completing (1) and proving the
Funk lower bound for $P$.

**4. Passing to a general convex body.** For $0<\sigma<\tau$, symmetric
polytope approximation gives $K\subset P\subset(\tau/\sigma)K$.
Then $\sigma P\subset\tau K$, and polarity reverses
$K-x\subset P-x$. Nonnegativity of the integrand gives

$$\frac{(4\operatorname{artanh}\sigma)^n}{n!}
\le V_P(\sigma)\le V_K(\tau).$$

Let $\sigma\uparrow\tau$; only the scalar lower bound needs continuity.
Finiteness follows directly: if $rB_2\subset K$, convexity gives
$(1-\tau)K\subset K-x$ for $x\in\tau K$. Thus every polar in the integral
is contained in $[r(1-\tau)]^{-1}B_2$, a fixed bounded set.

**5. Comparing volume growth with flag counts.** Let
$N=\#\operatorname{FullFlag}(P)$. Choose a relative-interior point of each
proper face. Each complete flag gives a simplex with those points and
$0$; these simplices cover $P$. Make the same choices for $P^\circ$.
For $x\in\operatorname{int}P$, the projective map
$q\mapsto q/(1-\langle q,x\rangle)$ sends $P^\circ$ onto $(P-x)^\circ$
and sends each polar flag simplex onto a simplex. Summing over the two
finite covers bounds the volume integral above by a sum over flag pairs.
For a pair with vertices $p_0,\ldots,p_{n-1},p_n=0$ and
$q_0,\ldots,q_{n-1}$, the substitution $u_i=1-\langle q_i,x\rangle$
cancels the determinant in the polar simplex volume. Its contribution is
bounded by

$$\frac1{n!}\int_{D_{F,G}(\tau)}\frac{du}{u_0\cdots u_{n-1}},$$

where $D_{F,G}(\tau)$ is the image of the scaled primal flag simplex.
Set $\tau=1-e^{-R}$. The vertices of this domain have coordinates
$e^{-R}+(1-e^{-R})a_{ki}$, where $a_{ki}=1-\langle q_i,p_k\rangle\in[0,2]$.
Contact at a relative-interior point propagates to its whole face. Along
the two face chains this means that the sets $S_i=\{k:a_{ki}>0\}$ are
nested final intervals. Finite coefficient comparison consequently gives
$u_i\le C_i u_{i+1}$ with constants independent of $R$.

In logarithmic coordinates $z_i=\log u_i$, the integral is ordinary
volume. After fixed shifts, the coordinates are ordered inside an interval
of length $R+O(1)$, so this volume is at most $(R+O(1))^n/n!$.
If two supports coincide, a coordinate difference stays bounded; if a
support is the whole index set, one coordinate stays bounded. Either case
has volume $O(R^{n-1})$.
The only possible leading-order pairs therefore have the contact pattern

$$\langle q_i,p_k\rangle=1\quad\Longleftrightarrow\quad k+i<n.$$

For each primal flag this pattern determines at most one polar flag.
Indeed, its $i$-face must lie in the contact face defined by the first
$n-i$ primal points. These points are linearly independent, so that contact
face has dimension at most $i$; containing an $i$-face forces equality.
There are at most $N$ leading-order pairs. Each contributes at most
$1/(n!)^2$ after dividing by $R^n$, and every other pair contributes zero
in the limit. Therefore

$$\limsup_{R\to\infty}\frac{V_P(1-e^{-R})}{R^n}
\le\frac{N}{(n!)^2}.$$

Finally, $4\operatorname{artanh}(1-e^{-R})=2\log(2e^R-1)$ and
$\log(2e^R-1)/R\to1$. The Funk lower bound gives the opposite estimate
$\liminf V_P(1-e^{-R})/R^n\ge2^n/n!$.
Comparing them yields $2^n/n!\le N/(n!)^2$, hence
$\#\operatorname{FullFlag}(P)\ge2^n n!$.

## Files

| Directory | Contents |
|---|---|
| [PDF/](PDF/) | Proof manuscript and OpenTimestamps receipt |
| [lean/](lean/) | Complete modular proof, Lean 4.34.1 |
| [lean4web/](lean4web/) | Complete single-file proof, Lean 4.35.0-rc4 |
| [FClikelean/](FClikelean/) | FC-style statements for Kalai and the Funk-volume lower bound |

The final modular proofs are in [MainTheorems.lean](lean/Funk/MainTheorems.lean).

## Build and verification

```bash
cd lean
lake exe cache get
python3 scripts/build_audit.py
```

Both projects have pinned dependencies. The complete web file passed the public
Lean4Web server on **8 October 2026**, with zero errors and no `sorryAx`.
Both main proof declarations use only `[propext, Classical.choice, Quot.sound]`.
The FC statements are separate from the proof dependencies.
[Verification records](lean/evidence/README.md) include the build, axiom audits
and earlier independent checks.

## References

- Schmitt–Ziegler, [*Ten Problems in Geometry*, p.21](https://www.mi.fu-berlin.de/math/groups/discgeom/ziegler/Preprintfiles/127PREPRINT.pdf#page=21): Kalai's flag conjecture (2008).
- Faifman–Vernicos–Walsh, [*Volume growth of Funk geometry and the flags of polytopes*](https://arxiv.org/abs/2306.09268): the Funk conjecture and its relation to flag counts.
- **OpenAI**, [`OAI.Analysis.Mahler` in `openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler), revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`: the homogeneous-flux, Stokes and holomorphic mass proofs used in step 3. The package includes 228 modules under Apache-2.0; see [source and license details](THIRD_PARTY.md).
- **The Formal Conjectures Authors**, [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/tree/d838afa7a62f66dc034c96fb011c10b9bde3f44c): the official `answer` elaborator and problem attributes used in the FC statements.
- [Lean 4](https://github.com/leanprover/lean4) and the [Lean community's Mathlib](https://github.com/leanprover-community/mathlib4): the proof assistant and mathematical library used for the formalization.

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra and GPT-6.1 sol.

## Appendix: symmetricfunk volume

The symmetric Funk-volume conjecture is the following
([Faifman–Vernicos–Walsh, Conjecture 1.1](https://arxiv.org/pdf/2306.09268#page=2)):

> **Conjecture.** For every origin-symmetric convex body $K\subset\mathbb R^n$,
> an $n$-dimensional Hanner polytope $H$, $n\ge1$ and $0<\tau<1$,
>
> $$V_K(\tau)\ge V_H(\tau)=\frac{(4\operatorname{artanh}\tau)^n}{n!}.$$

Here $V_K(\tau)=\int_{\tau K}\operatorname{vol}((K-x)^\circ)\,dx$ is the
unnormalized Holmes–Thompson Funk volume, using product Lebesgue measure.

We prove the numerical lower bound and finiteness of $V_K(\tau)$, and use
this bound to prove Kalai's full flag conjecture. The Hanner-volume equality
and equality cases are not formalized here.

## Appendix: time line

| Year | Who | Stage | Problem or result |
|---|---|---|---|
| 2008 | [Gil Kalai](https://www.mi.fu-berlin.de/math/groups/discgeom/ziegler/Preprintfiles/127PREPRINT.pdf#page=21) | Problem posed | **Kalai's full flag conjecture:** does every centrally symmetric $n$-polytope have at least $2^n n!$ complete flags? |
| 2023 | [Faifman–Vernicos–Walsh](https://arxiv.org/abs/2306.09268) | Problem posed | **Symmetric Funk-volume conjecture:** for each radius, do Hanner polytopes minimize Funk volume among origin-symmetric convex bodies? |
| 2023 | [Faifman–Vernicos–Walsh](https://arxiv.org/abs/2306.09268) | Partial proof | Proved the Funk-volume conjecture for unconditional bodies and related large-radius volume growth to complete flag counts. |
| 2026 | **This repo (Kenta Kitamura)** | **Lean 4 proof** | **Proves Kalai's full flag conjecture in all positive dimensions.** Includes an [FC-style statement](FClikelean/KalaiFullFlags.lean) and a [complete proof](lean/Funk/MainTheorems.lean). |
| 2026 | **This repo (Kenta Kitamura)** | **Supporting Lean 4 proof** | **Proves the numerical Funk-volume lower bound for all origin-symmetric convex bodies, including finiteness.** Includes an [FC-style statement](FClikelean/SymmetricFunkVolume.lean) and a [complete proof](lean/Funk/MainTheorems.lean). |
