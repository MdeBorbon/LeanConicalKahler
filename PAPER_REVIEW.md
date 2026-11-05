# Review notes: de Borbon–Edwards, *Schauder estimates on products of cones*

This document records discrepancies, gaps and ambiguities in the paper that turned up while
formalising it. It is kept separate from the formalisation. **The target theorem (Theorem 1.1)
has not been altered.** None of the items below changes its statement. They concern typos,
normalisations and steps of the proof that need more detail.

Quotations are verbatim from the arXiv LaTeX source.

## Status legend

| Label | Meaning |
|---|---|
| **Verified (Lean)** | Established by a kernel-checked computation. The declaration is named. Most are in `ConicalKahlerTest/PaperChecks.lean`. |
| **Verified (computation)** | Established by an explicit hand computation recorded here, not yet in Lean. |
| **Verified (text)** | An internal inconsistency of the text, visible by comparing two passages. |
| **Suspected** | A gap, omission or ambiguity that we believe needs repair. Not established as an error. |

---

## A. Verified errors

### V1. Appendix A.2: eigenvalues of the circle (Verified (Lean))

> "The eigenfunctions of the Laplace operator `\beta^{-2}\p^2_{\theta}` of `S^1_{2\pi\beta}` are
> `\cos (k\theta)`, `\sin(k\theta)`, with eigenvalues `k^2\beta^2` for `k\geq 0`."

The eigenvalues are `k²/β²`. the proof of Proposition 3.4 (§3.5) states this correctly ("The other
eigenvalues on `S^1_{2πβ}` are `k^2/\beta^2`"), and the expansion (A.1) uses the matching exponents
`r^{k/β}`.

*Evidence.* `PaperChecks`, section V1: `β⁻² ∂²_θ cos(kθ) = -(k²/β²) cos(kθ)`. The exponent `kβ`
that `k²β²` would give does not yield a harmonic function (explicit value `-15/4` at a point for
`β = 1/2`, `k = 1`). The correct statement is `coneHarmonicCos_polar_eq_zero`.
*Effect on Theorem 1.1:* none.

### V2. §5.1 and Appendix A.2: the complex coordinate (Verified (Lean))

§5.1: "Introducing complex coordinates `z_a = (1/\beta_a)r_a e^{i\theta_a}` on each cone factor,
identifies `\R^m_{(\beta)}` with `\C^{m/2}` endowed with the singular Kähler metric …
`|z_a|^{2\beta_a-2} i dz_a d\bar{z}_a` …"

App. A.2: "We introduce a complex variable, `z = (1/\beta) r^{1/\beta} e^{i\theta}`; … In this
complex coordinate, we have `dr^2 + \beta^2 r^2 d\theta^2 = |z|^{2\beta-2} |dz|^2`. and
`4\Delta = |z|^{2-2\beta} \p^2/\p z\p \bar{z}`."

Problems:

1. §5.1 is missing the power `1/β_a` on `r_a`.
2. With `z = (1/β) r^{1/β} e^{iθ}`, one gets `dr² + β² r² dθ² = β^{2+2β} |z|^{2β-2} |dz|²`, not
   `|z|^{2β-2}|dz|²`. The coordinate that makes the identity exact is
   **`z = (βr)^{1/β} e^{iθ}`**, i.e. `r = |z|^β / β`.
3. The Laplacian of `|z|^{2β-2}|dz|²` is **`Δ = 4 |z|^{2-2β} ∂_z ∂_{z̄}`**. The factor `4` is on the
   wrong side.
4. "`i dz_a d\bar z_a`" does not fix the convention relating the Kähler form to the metric. In this
   project `g(v, v) = ω(v, Jv)` (upstream convention). The Riemannian metric of
   `ω_β = i β² |ζ|^{2β-2} dζ ∧ dζ̄` is twice the paper's metric (see `ROADMAP.md` §1).

*Evidence.*
* `transverseConeMetric_rescale`: under `z = cζ` the metric `β² |ζ|^{2β-2}|dζ|²` becomes
  `β² c^{-2β} |z|^{2β-2}|dz|²`. In our coordinate `ζ`, `r = |ζ|^β`
  (`transverseConeMetric_eq_paperConeMetric`), so the paper's coordinate is `c = 1/β`.
* For `c = β^{1/β}` the coefficient is `1`. For `c = 1/β` it is `β^{2+2β}`, which equals `1/8` at
  `β = 1/2`.
* `coordLaplacian_conePolar` gives `Δ_β = β⁻² |ζ|^{2-2β}(∂_x² + ∂_y²)`. With `c = β^{1/β}` the
  constant `β⁻² c^{2β}` is `1` (checked in Lean), so `Δ_β = |z|^{2-2β}(∂_x² + ∂_y²) = 4|z|^{2-2β}∂_z∂_{z̄}`.

*Effect on Theorem 1.1:* none. §5.1 is a remark, and App. A.2 uses the coordinate only for the
removable-singularity argument, which is insensitive to constant factors.

### V3. §3.4: the sign of the eigenvalue of `L_{0,0}` (Verified (Lean))

> "It is easy to check that `L_{0, 0} f = -\lambda f` with `\lambda = 2(n_1 + n_2 + 2)`."

The paper's eigenvalue equation is `L_{λ₁,λ₂} f = λ f` (§3.3: "the indicial root equation of
`L_{\lambda_1, \lambda_2} f = \lambda f`"). From (3.2) with `λ₁ = λ₂ = 0`, the function
`f = (1/(n₁+1) + 1/(n₂+1)) x - 1/(n₂+1)` satisfies `L_{0,0} f = +2(n₁+n₂+2) f`.

*Evidence.* `PaperChecks`, section V3 (direct computation with `f` affine).
*Effect:* none. The text then uses `λ = 2m > 0` correctly.

### V4. Proof of Proposition 3.4, base case (Verified (Lean) / Verified (text))

> "The operator `L_{0, 0}` gives rise to constants, `(1/2)r^2-(m-3)^{-1}|s|^2` …"

Here `s ∈ ℝ^{m-2}`, `Δ_β r² = 4` and `Δ |s|² = 2(m-2)`. So the harmonic function is
`(1/2) r² - (m-2)⁻¹ |s|²`. The general formula of §3.4,
`(n₁+1)⁻¹ r₁² - (n₂+1)⁻¹ r₂²` with `n₂ = m-3`, gives the same.

> "… the lowest eigenvalue of `L_{\lambda_1, \lambda_2}` gives rise to the homogeneous harmonic
> functions `s_i r^{1/\beta} cos \theta` and `s_i r^{1/\beta} cos \theta`"

The second function should be `s_i r^{1/β} sin θ`.

*Evidence.* `PaperChecks`, section V4: `Δ_β r² = 4` in the paper's normalisation. For `m = 4`,
`(1/2) r² - (m-2)⁻¹|s|²` is harmonic, while `(1/2) r² - (m-3)⁻¹|s|²` has Laplacian `-2`. The
`sin`/`cos` duplicate is textual.
*Effect:* none.

### V5. `β = 1/2`: introduction versus definition of `𝒟₂` (Verified (Lean) + Verified (text))

The definition of `𝒟₂` (p. 2) includes the pure conical operators only "for indices `a` with
`β_a < 1/2`" and adds: "we are excluding the pure conical elements of the Hessian for those angles
`β\geq 1/2`". Introduction, item 1: "`\mathcal{D}_2` contains all entries of the Hessian except for
the terms … for those `\beta_a > 1/2`."

The two passages disagree at `β_a = 1/2`. **The definition is the correct one.** At `β = 1/2` the
harmonic function `r² cos θ` has `∂²_r(r² cos θ) = 2 cos θ`, which is bounded but has no limit at
the vertex. Item 1's "unbounded if `β > 1/2`" is correct as stated. The formalisation follows the
definition (`D2Op.rrPure` etc. require `β_a < 1/2`).

*Evidence.* `not_holderNearVertex_pure_of_half_le` (for `1/2 ≤ β < 1`: `∂²_r` of the harmonic
`r^{1/β} cos θ` is not `α`-Hölder near the vertex for any `α > 0`). `PaperChecks`, section V5, and
the `β = 1/2` test in `ConicalKahlerTest/RealCone.lean`.

### V6. Appendix A.1: the constant `c_β` (Verified (Lean), partially)

> "`B(\tilde{p}, 1)` is isometric to the Euclidean unit disc if `d(\tilde{p}, o)>c_{\beta}`, where
> `c_\beta = \sin(\pi\beta)` if `0 < \beta \leq 1/2`, and `1` if `\beta > 1/2`."

For `β ≤ 1/2`, the distance from `p̃ = (d, 0)` to the ray `{θ = π}` opposite to it (the cut) is
`d sin(πβ)`. The unit ball about `p̃` misses the cut only if `d sin(πβ) ≥ 1`. So the threshold
should be `d(p̃, o) > 1/sin(πβ) = c_β⁻¹`. The scaled statement that follows ("`\rho^{-1}B(p,\rho)
= B_1^E` if `\rho < c_\beta r`") is consistent with `1/c_β`. Lemma 4.1 uses a constant `c > 1` in
the "distance `> c`" form, i.e. `c = 1/c_β`. The conclusions are unaffected.

*Evidence.* `PaperChecks`, section V6: `coneDist_opposite_ray` (distance to the opposite ray in
terms of a hinge), `mul_sin_le_hingeDist` (the hinge is at least `d sin φ`) and `hingeDist_cos`
(equality at `s = d cos φ`). The step "the ball is isometric to a Euclidean disc once it misses the
cut" uses `coneDist_polarMap_eq_developing` locally but is not formalised as a statement about
balls.

### V7. Lemma 4.1 (Finitely many bad scales) (Verified (text))

> "then `B(x_k, 1)` is `\sqrt{d}\epsilon_0`-close to the unit ball in
> `C(S^1_{2\pi\beta_1}) \times \ldots \times C(S^1_{2\pi\beta_n}) \times \R^{m-2n}`."

`d` is not defined. The pattern of the proof (`√2 ε₀` for two factors) and its conclusion ("not
`\sqrt{n}\epsilon_0`-close") show that `√n` is meant. In the first case of the proof, "then
`B(x, 1)` is `\epsilon_0`-close (indeed isometric) to the unit ball in `\R^m`" should read
`B(x_k, 1)`.

### V8. §5 (proof of Theorem 1.1) (Verified (text))

> "the Hölder semi-norm of `D\tilde{P}_j` - is bounded by a uniform constant multiple of
> `\lambda^j r_a(x)`. Therefore, … `\leq C \lambda^{\alpha k} \sum_{j=j_0}^{\infty} \lambda^j r_a(x)^{-1}`"

The text has `λ^j r_a(x)` and the display has `λ^j r_a(x)^{-1}`. The display is correct: rescaling
by `λ^{-j}` puts the disc at distance `λ^{-j} r_a(x)` from the vertex, and the coefficients vary by
`O(1/R)` with `R = λ^{-j} r_a(x)`.

In the display bounding `\|Du_k\|_{B(x, \lambda^k)}`, the set `B_{k-1}` is not defined. Presumably
it is `B(x, λ^{k-1})`.

---

## B. Suspected gaps and omissions (not verified as errors)

### S1. Proposition 2.5 (the `L²` Hessian bound)

* The integration by parts (Bochner formula) on `B_1` drops the boundary terms on `∂B_1`. For
  Dirichlet eigenfunctions on a ball centred at the vertex these terms seem to have a favourable
  sign (the ball is convex and its boundary has positive mean curvature on the regular part). If so,
  the stated equalities `∫|Hess u|² = ∫ f²` should be inequalities `≤`, which still suffice.
* The cut-off functions `χ_ε` with `∫|Δχ_ε| → 0` are asserted without construction. A logarithmic
  cut-off in each `r_a` should work.
* The Lipschitz bound is used up to `∂B_1`, but the cited results are interior estimates or
  statements on closed spaces.
* The version for balls not centred at the vertex (§2.5.1) is asserted only. Such balls need not be
  convex, and for `β < 1/2` they can be annuli (App. A.1). A possible repair: `ηu` has compact
  support, so the argument can be run on a larger ball centred at the vertex.

### S2. Lemma 3.3 (expansion of harmonic functions)

The proof applies the maximum principle (Lemma 3.2), which needs continuity up to the boundary
and `C²` off the singular set, to a `W^{1,2}` function whose boundary trace is only `H^{1/2}`.
Convergence of the series is not discussed. A proof by energy uniqueness in `W^{1,2}_0` plus
separation of variables would avoid the issue.

### S3. Uniformity in Lemma 2.4 and Proposition 5.1

The harmonic approximation constant `δ` must be uniform over centres `x` with `|x| < ε₀` in each of
the finitely many model cones. Lemma 2.4 is stated only for `B_1` (centred at the vertex, by the
paper's convention). Rellich compactness on `W^{1,2}(B_{1/2}(x))` for general geodesic balls also
needs either a regularity argument for the domain or a cut-off into `W^{1,2}_0` of a larger ball.

### S4. "`L²`-orthogonal to `𝓗_{≤2}`" for balls not centred at the vertex (Lemma 4.3, Prop. 5.1)

This must mean that the components of degree `≤ 2` vanish in the expansion about the vertex on
`B(0, 1-ε) ⊂ B(x, 1)`. The bounds on `h_{≤2}` and `h_{>2}` on `B(x, 1/2)` ("Clearly") use that
`𝓗_{≤2}` is finite-dimensional and a comparison of `B(0, 1/2-ε)` with `B(x, 1/2)`. Neither is
spelled out.

### S5. The case `β_a = 1/2` in the proof

Theorem 1.1 formally allows `β_a = 1/2` (then `μ ≤ 1/β_a - 1 = 1`), and Proposition 3.4(2)
includes `r_a² cos θ_a`, `r_a² sin θ_a` for `β_a ≥ 1/2`. §1.4 treats `β = 1/2` separately
("Angles equal to `π`"). But the `m = 3` argument in §3.5.1 assumes `β ≠ 1/2`, and a commented-out
line in the source reads "Our argument is simplified if we exclude the case `\beta = 1/2`". Every
step should be checked at `β_a = 1/2`.

### S6. Lemma 3.1 (spectral theory on the link)

The statement has `0 = λ₀ < λ₁`, but the proof only gives `λ₀ ≤ λ₁`. Strict inequality needs the
link to be connected (multiplicity one of the eigenvalue `0`). This holds here but is not argued.

### S7. Lemma 2.7 and §3.3

The proof of Lemma 2.7 is omitted, and its constant also depends on `m`. The Sturm–Liouville facts
used in §3.3 (multiplicity one, nodal counts, completeness of the separated eigenfunctions) are
invoked as "standard theory" without a reference.

---

## C. Remarks (imprecisions that do not affect correctness)

* **𝒟₂ and "entries of the Hessian".** The paper calls the operators of `𝒟₂` "entries of the
  Hessian", but defines them as **coordinate** operators (p. 2). They differ from the components
  of the covariant Hessian in the orthonormal frame `(∂_r, (βr)⁻¹∂_θ)` by first-order terms and
  factors of `β`. For example, `∇²u(e_θ, e_θ) = (βr)⁻²∂²_θ u + r⁻¹ ∂_r u`. The formalisation uses
  the coordinate operators exactly as defined (`D2Op`).
* **Balls.** `B(x, ρ)` is the geodesic ball and `B_ρ = B(0, ρ)`. Balls centred at the vertex are
  Euclidean balls in the real coordinates (`ConeProduct.ball_of_cone_eq_zero`). The paper takes the
  cone distance to be the geodesic distance of `g`. The formalisation defines it by the standard
  formula for Euclidean cones (`coneDist`). The identification with the length metric is an
  outstanding obligation of the formalisation, not an issue with the paper.
* **`r` is the distance to the apex.** This is consistent with the formal distance
  (`coneDist_vertex`).
