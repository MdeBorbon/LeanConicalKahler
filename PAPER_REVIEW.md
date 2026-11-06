# Review notes: de Borbon–Edwards, *Schauder estimates on products of cones*

This document records discrepancies, gaps and ambiguities in the paper that turned up while
formalising it. It is kept separate from the formalisation. **The target theorem (Theorem 1.1)
has not been altered.** None of the items below changes its statement. They concern typos,
normalisations, and steps of the proof that are wrong as written or need more detail. **No item
claims that a stated result of the paper (in particular Proposition 2.5 or Theorem 1.1) is false.**
Where a step of a proof is wrong (V9, V10), the review records what is confirmed, what remains a
gap (section B), and what is only a proposed repair (section C).

Quotations are verbatim from the LaTeX source of **arXiv:2002.07668v1** (18 February 2020), the
only arXiv version. The published version (Comment. Math. Helv. 96 (2021), 113–148,
DOI 10.4171/CMH/509; submitted 24 March 2020) is behind a subscription and has **not** been
compared. Every item below refers to arXiv v1 only. We do not claim that the journal version
contains these errors.

Proposition 2.5 is treated in more detail in `research_notes/PROPOSITION_2_5_AUDIT.md`
(M. de Borbon, with ChatGPT). Its claims were checked independently for this review: see V9, V10,
the gaps in S1 and the proposed repair in section C. The symbolic computations are reproducible
with `python3 -I research_notes/prop_2_5_checks.py` (sympy).

## Status legend

| Label | Meaning |
|---|---|
| **Verified (Lean)** | Established by a kernel-checked computation. The declaration is named. Most are in `ConicalKahlerTest/PaperChecks.lean`. |
| **Verified (computation)** | Established by an explicit hand computation recorded here, not yet in Lean. |
| **Verified (text)** | An internal inconsistency of the text, visible by comparing two passages. |
| **Verified (symbolic)** | Established by exact symbolic computation (sympy) in `research_notes/prop_2_5_checks.py`. Not kernel-checked. |
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

### V9. Proposition 2.5: a boundary term is missing in the Bochner argument (Verified (symbolic))

The proof applies the Bochner identity to a Dirichlet eigenfunction `u_λ` on `B_1`
(`-Δu_λ = λu_λ`, `u_λ ∈ W^{1,2}_0(B_1)`):

> "Multiply by `\chi_{\epsilon}` and integrate to get
> `\int_{B_1} \chi_{\epsilon} |\mbox{Hess}(u_{\lambda})|^2 = \lambda \int_{B_1} \chi_{\epsilon} |\nabla u_{\lambda}|^2 + \frac{1}{2} \int_{B_1} (\Delta \chi_{\epsilon}) |\nabla u|^2`"

and concludes

> "`\int_{B_1} |\mbox{Hess}(u_{\lambda})|^2 = \lambda \int_{B_1} |\nabla u_{\lambda}|^2 = \lambda^2 \int_{B_1} u_{\lambda}^2 = \int_{B_1} f_{\lambda}^2`",

and the same equality for finite sums of eigenfunctions.

**The error.** `χ_ε` cuts off only near the singular set. It equals `1` near the outer sphere `∂B_1`
away from `S`, so integrating `½ χ_ε Δ|∇u_λ|²` by parts also produces `½∫_{∂B_1} χ_ε ∂_ν|∇u_λ|²`.
This term is omitted. In the smooth part of the boundary we have `u_λ = 0` and `Δu_λ = -λu_λ = 0`
on `∂B_1`. Hence `∇u_λ = (∂_ν u_λ) ν` and `∇²u_λ(ν, ν) = -H ∂_ν u_λ`, where `H` is the mean
curvature. So `½∂_ν|∇u_λ|² = -H (∂_ν u_λ)²`. The unit sphere about the vertex of an
`m`-dimensional metric cone has `H = m − 1` on its smooth part. Formally (see below for what this
needs), the correct identity is

  `∫_{B_1} |Hess u_λ|² = λ² ∫_{B_1} u_λ² − (m − 1) ∫_{∂B_1} (∂_ν u_λ)²`,                   (V9.1)

and for finite sums `v_N = ∑ λ_j⁻¹ f_j`, `F_N = −Δv_N = ∑ f_j`:

  `∫_{B_1} |Hess v_N|² = ∫_{B_1} F_N² − (m − 1) ∫_{∂B_1} (∂_ν v_N)² ≤ ∫_{B_1} F_N²`.        (V9.2)

The paper's display also has `|∇u|²` where `|∇u_λ|²` is meant (a typo).

**The counterexample to the stated equality.**
- Space: `C(S¹_{2πβ}) × ℝ` (`m = 3`, `0 < β < 1`), with `R = (r² + s²)^{1/2}` and `B_1 = {R < 1}`.
- `v = sin(πR)/R` is a Dirichlet eigenfunction with `λ = π²`. It is a smooth function of
  `r² + s²` and Lipschitz across the axis.
- Its integrals:

  | quantity | value |
  |---|---|
  | `∫_{B_1} v² dV_g` | `2πβ` |
  | `∫_{B_1} (Δv)² dV_g` | `2π⁵β` |
  | `∫_{B_1} |Hess v|² dV_g` (`= 4πβ ∫₀¹ (v''² + 2v'²/R²) R² dR`) | `2π³β(π² − 4)` |
  | `(m − 1) ∫_{∂B_1} (∂_ν v)² dA_g` (`v'(1) = −π`, `|∂B_1| = 4πβ`) | `8π³β` |

So `∫|Hess v|² = 2π³β(π² − 4) < 2π⁵β = λ² ∫ v²`, and (V9.1) holds exactly. The same failure
occurs for `β = 1`, i.e. on the Euclidean unit ball of `ℝ³`: the error is in the integration by
parts, not in the conical geometry.

*Evidence.* `research_notes/prop_2_5_checks.py`, sections 1–2:
- the Bochner identity on the regular part (`Ric = 0`), for an arbitrary function, in the
  coordinates `(r, θ, s)` with the Christoffel symbols of `g`;
- the radial eigenfunction, all four integrals, and identity (V9.1);
- the formula `|Hess v|² = v''² + 2(v'/R)²`, recomputed from the Christoffel symbols.

*What this does and does not show.*
- It shows that the displayed **equalities** in the proof of Proposition 2.5 are false. This is a
  confirmed error in the proof.
- It does **not** show that Proposition 2.5 or Theorem 1.1 is false. The omitted term has a
  favourable sign, so (V9.2) gives the inequality `∫|Hess v_N|² ≤ ∫F_N²` that the spectral argument
  needs. It also gives the Cauchy property of `∑ u_λ`, applied to differences of finite sums.
- But (V9.1)–(V9.2) are justified here only in the smooth setting. For the cone they also need
  regularity of eigenfunctions up to `∂B_1` and the control of boundary terms where `∂B_1` meets
  the singular set (S1). A proof that avoids the outer boundary altogether is in section C.

### V10. §2.4: the intrinsic and Euclidean Hessians are not uniformly equivalent (Verified (symbolic))

> "The Hessian of a function with respect to our singular metric, `\mbox{Hess}(u) = \nabla_g^2 u`,
> is uniformly equivalent, as a quadratic form, to the Euclidean Hessian. Same as before, we have
> the usual Sobolev space `W^{2, 2}`, and it is irrelevant whether we use the Euclidean metric or
> `g` to define its norm."

This is false for `β ≠ 1`. Uniform equivalence of the metric tensors (eq. (2.1)) compares first
derivatives. The Christoffel symbols of `g` in the real coordinates are unbounded:
`Γ^r_{θθ} = −β² r` and `Γ^θ_{rθ} = r⁻¹`.

**Counterexample.** On `C(S¹_{2πβ}) × ℝ`, let `u = x = r cos θ`, the first real coordinate of the
cone factor. Its Euclidean Hessian vanishes, so `u ∈ W^{2,2}_{Euc}(B_1)`. Its intrinsic Hessian is
`∇²u(e_θ, e_θ) = (β² − 1) cos θ/(β² r)`, with `e_θ = (βr)⁻¹∂_θ`; the other components vanish. So
`|∇²_g u|² = (β² − 1)² cos²θ/(β⁴ r²)`, and

  `∫_{ε<r<1/2, 0<s<1} |∇²_g u|² dV_g = π (1 − β²)²/β³ · log(1/(2ε)) → ∞`.

So Euclidean `W^{2,2}` does not imply that the intrinsic Hessian is in `L²`, and the two norms are
not equivalent.

*Qualification (agreeing with the audit).* Here `Δ_g u = (1 − 1/β²) cos θ / r ∉ L²` near the axis,
so this `u` does **not** contradict Proposition 2.5, whose hypothesis is `Δu ∈ L²`. What fails is
the identification of the two `W^{2,2}` spaces asserted before the proposition. The proof of
Proposition 2.5 bounds the **intrinsic** Hessian (via Bochner), so its conclusion should be read
intrinsically. Whether intrinsic and Euclidean second derivatives agree for solutions of
`Δ_g u ∈ L²` is open here.

*Evidence.* `research_notes/prop_2_5_checks.py`, section 3: the Christoffel symbols, the Hessian
components, `|∇²_g u|²`, the divergent integral, and `Δ_g u`.

---

## B. Gaps and omissions (not verified as errors)

### S1. Proposition 2.5 (the `L²` Hessian bound): what remains after V9 and V10

The confirmed errors are V9 and V10. The following are gaps, not errors.

* **Boundary terms in the global argument.** Even with the corrected identity (V9.1), the global
  route needs:
  - eigenfunction regularity up to `∂B_1`, including near `∂B_1 ∩ S`, where the sphere is itself
    conical;
  - control of the extra boundary terms `∫_{∂B_1} (χ_ε ∂_ν|∇u|² − |∇u|² ∂_ν χ_ε)` inside the
    tubular neighbourhood of `S`.

  The localised argument (section C) avoids both.
* **Cut-off functions.** The paper asserts `χ_ε` with `∫|Δχ_ε| → 0` without construction.
  Lemma 2.2 provides `∫|∇χ|² → 0`, which is a different condition. A logarithmic cut-off in each
  factor appears to satisfy `∫|∇χ_ε| → 0` and `∫|Δχ_ε| → 0` locally: with `L = log(ε/δ)`, the
  function `rχ'` is `1/L` on `[δ, ε]` after smoothing. Products over several cone factors also seem
  to work. Neither has been written out.
* **Eigenfunction regularity.** The proof uses that eigenfunctions are Lipschitz, citing [Mon17]
  and [BKMR18, Prop. 5.4] (for `β_a < 1`). Whether these cover Dirichlet eigenfunctions on cone
  balls (interior and boundary) has not been checked. The localised argument needs only interior
  bounds.
* **The weak Hessian.** `W^{2,2}` must be defined intrinsically (V10). Examples: an `L²` covariant
  Hessian on the regular part, or the closure used in the proof. The weak limit of the Hessians of
  finite sums must be identified with the Hessian of the solution.
* **From the intrinsic Hessian to `𝒟₂`.** Most operators of `𝒟₂` are fixed multiples of
  orthonormal-frame components of the intrinsic Hessian, or traces:
  - `∂²_r = ∇²(e_r, e_r)`;
  - `∂²_{rs} = ∇²(e_r, ∂_s)`;
  - `r⁻¹∂²_{θs} = β ∇²(e_θ, ∂_s)`;
  - the mixed conical operators, similarly;
  - `Δ_β + Δ_s = tr ∇²`.

  The two remaining pure conical operators (present only for `β_a < 1/2`) differ by first-order
  terms:
  - `r⁻²∂²_θ = β²∇²(e_θ, e_θ) − β² r⁻¹∂_r`;
  - `r⁻¹∂²_{rθ} = β∇²(e_r, e_θ) + r⁻²∂_θ`.

  These are verified symbolically (`prop_2_5_checks.py`, section 5). Bounding these two operators
  from an intrinsic Hessian bound needs separate control of `r⁻¹∂_r u` and `r⁻²∂_θ u`.
* **Uniformity in the centre** (§2.5.1). This is asserted only. Balls `B_1(p)` not centred at the
  vertex need not be convex, and for `β < 1/2` they can be annuli (App. A.1). Cut-offs used in the
  proof must have bounded `Δ_g`. Smooth functions of `(r_a², s)` do, but Euclidean-smooth functions
  that are not even in each cone factor generally do not. For example `Δ_g x = (1 − 1/β²) cos θ / r`
  (V10). So off-centre balls need their own construction.

### S2. Lemma 3.3 (expansion of harmonic functions) (resolved in Lean, Milestone 12)

The proof applies the maximum principle (Lemma 3.2), which needs continuity up to the boundary
and `C²` off the singular set, to a `W^{1,2}` function whose boundary trace is only `H^{1/2}`.
Convergence of the series is not discussed. A proof by energy uniqueness in `W^{1,2}_0` plus
separation of variables would avoid the issue.

**Progress (Milestone 11, kernel-checked).**
- The energy replacement of Lemma 3.2 is proved: a weakly harmonic function in `W^{1,2}_0(Ω)` on a
  bounded `Ω` vanishes, and two weak solutions with the same right-hand side whose difference is in
  `W^{1,2}_0` agree (`eq_zero_of_isWeakSolution_zero_of_mem_H01`,
  `eq_of_isWeakSolution_of_sub_mem_H01`). No continuity up to the boundary is used.
- Separation of variables in one angle `θ_a` is proved for weak solutions on rotation-invariant
  domains: the Fourier modes are weak solutions, transform like `cos kθ_a` and `sin kθ_a`, and
  determine the function (`isWeakSolution_angMode`, `rotLp_cosCoeff`, `eq_zero_of_modes_eq_zero`).
- The explicit homogeneous harmonic functions used in §3 are weakly harmonic on every bounded open
  set, including near the singular set (`IsClassicalHarmonic.isWeakSolution`).
- Still missing for Lemma 3.3 after Milestone 11: the spectral theory of the link (Lemma 3.1), the
  radial ODE for the coefficients and the convergence of the expansion.

**Resolution (Milestone 12, kernel-checked).** Lemma 3.3 is proved without the maximum principle
(`expansion`, `cone_expansion`). For a conical coefficient field and `d ≥ 2`, every weakly harmonic
`u ∈ W^{1,2}(B_1)` is `u = ∑ a_i ρ^{δ_i} φ_i` in `L²(B_1)`, with `{φ_i}` a Hilbert basis of link
eigenfunctions (Lemma 3.1, `link_spectral`), `δ_i ≥ 0` and each term weakly harmonic on `B_1`. The
argument is:
1. `ρ^δ φ` is weakly harmonic on `ℝ^d \ {0}` when `λ = δ(δ + d − 2)` (`homogeneous_harmonic`), and
   the vertex is removable for `d ≥ 2` (`isWeakSolution_of_punctured`).
2. The Wronskian identity `∫ P⟨A∇u, ∇η⟩ = ∫ u⟨A∇P, ∇η⟩` for weakly harmonic `u, P`
   (`wronskian`), tested with radial `η = F(|x|)` that is constant near the vertex, gives
   `(r^{−δ} u_φ)' = 0` weakly on `(0, 1)` (`key_identity`, `rayCoeff_eq`). This step replaces both
   the maximum principle and the Frobenius analysis of the radial ODE: the singular solution
   `r^{2−d−δ}` is excluded because `u` is harmonic across the vertex.
3. Parseval on each sphere gives the coefficients and the `L²(B_1)` convergence (unconditional).
Convergence in `W^{1,2}` or locally uniformly is not proved.

### S3. Uniformity in Lemma 2.4 and Proposition 5.1 (resolved for Lemma 2.4, in Lean)

Proposition 5.1 needs the harmonic approximation constant `δ` to be uniform over centres `x` with
`|x| < ε₀` in each of the finitely many model cones. But Lemma 2.4 is stated only for `B_1`
(centred at the vertex, by the paper's convention), and its compactness proof does not obviously
give this uniformity. Rellich compactness on `W^{1,2}(B_{1/2}(x))` for general geodesic balls also
needs either a regularity argument for the domain or a cut-off into `W^{1,2}_0` of a larger ball.

**Resolution (Milestone 10, kernel-checked).** Lemma 2.4 holds with an explicit `δ` that is
independent of the centre, by a direct argument instead of compactness.
- Let `w ∈ W^{1,2}_0(B(x,1))` solve `-Δw = f` (Lax–Milgram), and set `h = u − w`. Then `h` is weakly
  harmonic on all of `B(x,1)`.
- Friedrichs–Poincaré and the energy estimate give `λ ‖u − h‖_{L²} ≤ 4R² ‖f‖_{L²}`, where `R` is the
  radius of any Euclidean ball containing `B(x,1)`. This gives `δ = λε/(4R²+1)`.
- Every geodesic ball `B(x, 1)` lies in a Euclidean ball of radius `1/lowerConst β`, so `R` (and
  hence `δ`) is uniform in `x`.
- The hypothesis `‖u‖_{L²(B_1)} ≤ 1` of Lemma 2.4 is not needed.
- Lean: `CoeffField.harmonic_approximation`, `cone_harmonic_approximation`.

The paper's compactness argument is also formalised, with the cut-off into `W^{1,2}_0` handled as
above (`exists_tendsto_of_approx_solutions`).
- Applying Caccioppoli to differences `u_i − u_j` gives **strong** `W^{1,2}` convergence on
  compactly contained subdomains, so weak compactness is not needed.
- `harmonic_approximation_of_compactness` derives Lemma 2.4 from it by contradiction.

What remains of S3 concerns Proposition 5.1, not Lemma 2.4: the decomposition
`h = h_{≤2} + h_{>2}` on balls not centred at the vertex and its bounds (S4).

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

**Lean status (Milestone 12).** Lemma 3.1 is proved without the strict inequality
(`link_spectral`): a Hilbert basis of `L²(S)` of eigenfunctions, `λ_i ≥ 0`, finitely many below any
bound, and constants have `λ = 0` (`linkEigen_const`). Multiplicity one of `λ = 0` is not proved,
and Lemma 3.3 does not need it.

### S8. Lemmas 2.7, 4.2, 4.3: indices and strictness (Verified (text), repaired in Lean)

- **Lemma 2.7.** The hypothesis uses `τ_1 + ⋯ + τ_k` at scale `λ^k` (an empty sum for `k = 0`),
  while the conclusion sums from `k = 0`. In Lean the partial sums are `τ_0 + ⋯ + τ_{k−1}`
  (`sum_increments`).
- **Lemma 4.3.** The statement has a strict inequality, which fails for `u = 0`. The proof
  gives `≤`, which is what is used. In the proof, the power `m` in `(1 − ε)^{-m}` should be `m/2`
  for the scaled norm; this does not affect the argument. `B(1, x)` is a typo for `B(x, 1)`.
- **Lemma 4.2** is used in Lemma 4.3 on balls of radius `1 − ε`, i.e. after a dilation. This is
  formalised by dilation invariance of `𝓗_{≤2}` (`cone_vertex_monotone_ball`).

*Effect:* none on the results.

### S7. Lemma 2.7 and §3.3

The proof of Lemma 2.7 is omitted, and its constant also depends on `m`. The Sturm–Liouville facts
used in §3.3 (multiplicity one, nodal counts, completeness of the separated eigenfunctions) are
invoked as "standard theory" without a reference.

**Lean status (Milestone 13).** Proposition 3.4 is proved without these Sturm–Liouville facts
(`prop_3_4`). Completeness of the separated eigenfunctions is replaced by completeness of an
explicit family, the harmonic cone polynomials `∏ r_a^{k_a/β_a} T(k_a θ_a) h(r², s)`:
- their restrictions to the link are dense (Fischer decomposition and Stone–Weierstrass);
- homogeneous harmonic functions of different degrees are orthogonal on the link (from Lemma 3.3).

So the degrees of homogeneous harmonic functions are exactly `∑_a k_a/β_a + m`, and the list of
Prop. 3.4 and the gap `(2, 2 + μ)` follow by enumeration. Multiplicities and nodal counts are not
needed. Lemma 2.7 is proved in Milestone 14 (`sum_increments`).

---

## C. Proposed repair of Proposition 2.5 (not established)

This is the localised Bochner argument of the audit (§5 there). It estimates the **intrinsic**
Hessian on `B_{1/2}` and never integrates over `∂B_1`.

1. **Reduction.** Let `η₀` be radial about the vertex (a smooth function of
   `R² = ∑ r_a² + |s|²`), with `η₀ = 1` on `B_{3/4}` and support in `B_1`. Then
   `Δ_g η₀ = 4R²φ'' + 2mφ'` is bounded. `ũ = η₀u ∈ W^{1,2}_0(B_1)` solves `−Δũ = f̃` with
   `‖f̃‖_{L²} ≤ C(‖f‖ + ‖u‖)`, by Caccioppoli. This is as in the paper.
2. **Spectral sums.** `f̃ = ∑ f_j` (Dirichlet eigenfunctions), `v_N = ∑_{j≤N} λ_j⁻¹ f_j`,
   `F_N = ∑_{j≤N} f_j`. This is as in the paper.
3. **Localised identity.** For `η₁` radial, with `η₁ = 1` on `B_{1/2}` and support in `B_{3/4}`, on
   the regular part:

     `η₁²|Hess v_N|² − η₁²F_N² + 2η₁F_N⟨∇η₁, ∇v_N⟩ − ½Δ(η₁²)|∇v_N|² = div_g W`,

   where `W = ½(η₁²∇|∇v_N|² − |∇v_N|²∇η₁²) + η₁²F_N∇v_N`. This is **verified** as a pointwise
   identity for arbitrary smooth `v`, `η` (`prop_2_5_checks.py`, section 4). Integrating
   (formally) gives the audit's (5.1). There is no outer boundary term, because `η₁` has compact
   support in `B_1`.
4. **Estimate.** Cauchy–Schwarz gives `∫_{B_{1/2}}|Hess v_N|² ≤ C(∫F_N² + ∫|∇v_N|²)`, and
   orthogonality gives `∫|∇v_N|² = ∑ λ_j⁻¹‖f_j‖² ≤ λ₁⁻¹‖F_N‖²`. So the bound is uniform in `N`.
   This step is elementary.

**Remaining obligations** before this proves Proposition 2.5:
- (i) The cut-off lemma (S1): `χ_ε` near all strata `{r_a = 0}`, with `∫|∇χ_ε|`,
  `∫|Δχ_ε| → 0` on compact sets. Both the `Δχ_ε` terms and the `∇χ_ε` terms, from moving the
  derivative off `F_N`, must vanish in the limit.
- (ii) **Interior** boundedness of `v_N`, `F_N`, `∇v_N` on `supp η₁` for each fixed `N`. Check the
  cited Lipschitz results.
- (iii) The weak-compactness and identification step for the intrinsic Hessian (S1).
- (iv) Uniformity in the centre of the ball (S1).
- (v) The passage from the intrinsic Hessian to the operators of `𝒟₂` (S1).

The audit and this review agree: the evidence suggests that the interior Hessian estimate can be
recovered, but a complete repair has **not** been established.

---

## D. Remarks (imprecisions that do not affect correctness)

* **`W^{1,2}` versus `W^{2,2}` (§2.1, §2.4).** The paper's assertion that the `W^{1,2}` norms
  defined by `g` and by the Euclidean metric are equivalent is correct. It is proved in Lean with
  explicit constants: `(∏β) λ ‖·‖² ≤ ∫ (u² + |∇_g u|²_g) dV_g ≤ (∏β) Λ ‖·‖²`
  (`intrinsicNormSq_bounds`). The analogous assertion for `W^{2,2}` is false (V10).
* **The divergence form of `Δ`.** On smooth functions away from the singular set, the operator
  `div(g⁻¹∇u)` of the weak formulation in the real coordinates is the paper's
  `Δ = ∑_a Δ_{β_a} + Δ_s`. This is proved in Lean (`divergence_coneInvOp_gradient`). Moreover, a
  function that is `C²` off the singular set with `u, ∇u ∈ L²` is a weak solution iff it is a
  classical solution off the singular set (`cone_isWeakSolution_of_classical`,
  `cone_classical_of_isWeakSolution`): the paper's tacit identification of the two notions is
  justified for such functions.
* **Corollary 3.5** ("immediate check inspection") is verified in Lean for every element of the
  span of the paper's list in Proposition 3.4, including the bound (3.3) via finite
  dimensionality (`corollary_3_5`). Its application to all of `𝓗_{≤2}` depends on the
  completeness part of Proposition 3.4, which is not yet formalised.

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
