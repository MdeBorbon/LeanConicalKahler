module

public import ConicalKahler.Laplacian.Polar
public import ConicalKahler.Cone.Standard
public import CalabiYau.Geometry.Kahler.Riemannian.Laplacian

/-!
# The Laplace–Beltrami operator of the cone models

## The operator

For a Kähler form `ω₀` on a complex manifold `M`, the Riemannian metric is `g(u, v) = ω₀(u, Jv)`
(upstream `KahlerForm.toRiemannianMetric`). Its **Laplace–Beltrami operator**
`Δ_g f = div_g (∇_g f)` is the upstream `CalabiYau.Riemannian.ΔG`. We do not redefine it:
`laplaceBeltrami ω₀ f` is an abbreviation for `ΔG ω₀.toRiemannianMetric f`. Upstream proves that it is
twice the complex-trace Laplacian, `Δ_g f = 2 tr_ω(i∂∂̄f)` (`laplaceBeltrami_eq_two_mul_laplacian`).
On the open subsets of `ℂⁿ` used here, the complex trace is computed from the coefficient matrix
of `ω₀` and the complex Hessian of `f` (`laplacian_opens`).

## Products of cones and Euclidean factors

For cone weights `θ`, the model `ω_θ = i ∑_j w_j(z) dz_j ∧ dz̄_j` is the product of the
two-dimensional cones (`θ_j = some β_j`, `w_j = β_j² |z_j|^(2β_j-2)`) and Euclidean factors
(`θ_j = none`, `w_j = 1`). Its Laplace–Beltrami operator is the sum of the factor Laplacians
(`laplaceBeltrami_modelConeFormOn`):

  `Δ_g f = ∑_j Δ_{z_j} f / (2 w_j)`,  `Δ_{z_j} = ∂²_{x_j} + ∂²_{y_j}`.

**Normalisation.** The factor `2` is the upstream convention `g = 2 Re h` (README). For the
Euclidean form `i dz ∧ dz̄` it gives `Δ_g = ½(∂²_x + ∂²_y)`, the Laplacian of `g = 2(dx² + dy²)`.

## Polar form of the cone Laplacian

On a cone factor `j` with angle `2πβ`, write `z_j = ρ^{1/β} e^{iθ}` with the other coordinates
frozen, and `F(ρ, θ) = f(z)`. Then (`laplaceBeltrami_modelConeFormOn_conePolar`)

  `Δ_{z_j} f / (2 w_j) = ½ (F_ρρ + ρ⁻¹ F_ρ + (βρ)⁻² F_θθ)`.

For the standard two-dimensional cone (`n = 1`) this is the whole Laplacian
(`laplaceBeltrami_standardCone_polar`). The Hermitian cone metric in these coordinates is
`dρ² + β²ρ² dθ²`, and the Riemannian metric is twice that. This explains the factor `½`:
in the Riemannian radial variable `ρ̃ = √2 ρ` the operator is the usual
`∂²_ρ̃ + ρ̃⁻¹ ∂_ρ̃ + (βρ̃)⁻² ∂²_θ`.

## Harmonic functions

Real and imaginary parts of holomorphic functions have `i∂∂̄f = 0` (`ddbar_re_eq_zero`). They
are therefore harmonic for **every** Kähler form (`laplaceBeltrami_re_eq_zero`). In particular
`Re z_j^k` and `Im z_j^k` are harmonic for every cone model. In the cone coordinates of the
factor `j` they are `ρ^{k/β} cos(kθ)` and `ρ^{k/β} sin(kθ)` (`ConicalKahler.Laplacian.ConeHarmonic`).
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Filter Set ContinuousAlternatingMap

namespace ConicalKahler

variable {n : ℕ}

/-! ### The Laplace–Beltrami operator -/

section General

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (E n) M] [IsManifold 𝓘(ℂ, E n) ω M]

/-- **The Laplace–Beltrami operator** `Δ_g f = div_g ∇_g f` of the Riemannian metric
`g = ω₀(·, J·)` of a Kähler form (upstream `CalabiYau.Riemannian.ΔG`). -/
noncomputable abbrev laplaceBeltrami (ω₀ : KahlerForm n M)
    (f : ContMDiffMap 𝓘(ℝ, E n) 𝓘(ℝ) M ℝ ∞) : M → ℝ :=
  CalabiYau.Riemannian.ΔG (I := 𝓘(ℝ, E n)) ω₀.toRiemannianMetric f

/-- `Δ_g f = 2 tr_ω(i∂∂̄ f)` (upstream). -/
theorem laplaceBeltrami_eq_two_mul_laplacian (ω₀ : KahlerForm n M)
    (f : ContMDiffMap 𝓘(ℝ, E n) 𝓘(ℝ) M ℝ ∞) (x : M) :
    laplaceBeltrami ω₀ f x = 2 * ω₀.laplacian f x :=
  KahlerForm.riemannian_laplacian_eq_two_mul_laplacian ω₀ f f.contMDiff x

end General

/-! ### Open subsets of `ℂⁿ` -/

section Opens

variable {U : TopologicalSpace.Opens (E n)}

/-- On `U ⊆ ℂⁿ`, the complex-trace Laplacian of the restriction of `f` is `tr_ω (i∂∂̄ f)`. -/
theorem laplacian_opens (ω₀ : KahlerForm n U) (f : E n → ℝ) (x : U) :
    ω₀.laplacian (fun y : U => f y) x = relTrace (ω₀ x) (ddbar f x) := by
  unfold KahlerForm.laplacian
  rw [mddbar_opens]

/-- The real part of a diagonal entry of the complex Hessian is a quarter of the flat Laplacian
in that coordinate: `Re ∂²f/∂z_j∂z̄_j = ¼ Δ_{z_j} f`. -/
theorem re_complexHessian_diag {f : E n → ℝ} {z : E n} (hf : ContDiffAt ℝ 2 f z) (j : Fin n) :
    (complexHessian f z j j).re = coordLaplacian j f z / 4 := by
  rw [complexHessian_apply hf j j, coordLaplacian]
  simp

/-- **Pluriharmonic functions are harmonic for every Kähler form.** -/
theorem laplaceBeltrami_eq_zero_of_ddbar_eq_zero (ω₀ : KahlerForm n U) {f : E n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (x : U) (h : ddbar f x = 0) :
    laplaceBeltrami ω₀ (restrictSmooth U hf) x = 0 := by
  rw [laplaceBeltrami_eq_two_mul_laplacian]
  change 2 * ω₀.laplacian (fun y : U => f y) x = 0
  rw [laplacian_opens, h, relTrace_zero, mul_zero]

end Opens

/-! ### Real parts of holomorphic functions -/

section Holomorphic

variable [NeZero n]

/-- **`i∂∂̄ Re P = 0` for holomorphic `P`.** Write `Re P = Re(·)_0 ∘ ψ` with `ψ = P e_0`, which is
holomorphic, and `Re(·)_0` real-linear. -/
theorem ddbar_re_eq_zero {P : E n → ℂ} {z : E n} (hP : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ P w) :
    ddbar (fun w => (P w).re) z = 0 := by
  set e : E n := EuclideanSpace.single 0 1
  set ψ : E n → E n := fun w => P w • e with hψ_def
  set f₀ : E n → ℝ := fun w => (w 0).re with hf₀_def
  have hcomp : (fun w => (P w).re) = f₀ ∘ ψ := by
    funext w
    simp [hf₀_def, hψ_def, e]
  have hψ : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w :=
    hP.mono fun w hw => hw.smul_const e
  -- `f₀` is real-linear, so its `i∂∂̄` vanishes
  set L : E n →L[ℝ] ℝ := Complex.reCLM.comp
    ((EuclideanSpace.proj (0 : Fin n) : E n →L[ℂ] ℂ).restrictScalars ℝ)
  have hL : f₀ = L := by
    funext w
    simp [hf₀_def, L]
  have hf₀ : ContDiffAt ℝ 2 f₀ (ψ z) := by rw [hL]; exact L.contDiff.contDiffAt
  have hdd : ddbar f₀ (ψ z) = 0 := by
    ext v
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv, ddbar_apply hf₀]
    have hd2 : fderiv ℝ (fderiv ℝ f₀) (ψ z) = 0 := by
      have hfd : fderiv ℝ f₀ = fun _ => L := by
        rw [hL]
        funext w
        exact L.fderiv
      rw [hfd]
      exact (hasFDerivAt_const L (ψ z)).fderiv
    simp [hd2]
  rw [hcomp, ddbar_comp_holomorphic hψ hf₀, hdd]
  rfl

/-- `i∂∂̄ Im P = 0` for holomorphic `P`. -/
theorem ddbar_im_eq_zero {P : E n → ℂ} {z : E n} (hP : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ P w) :
    ddbar (fun w => (P w).im) z = 0 := by
  have h := ddbar_re_eq_zero (P := fun w => -Complex.I * P w) (z := z)
    (hP.mono fun w hw => (differentiableAt_const _).mul hw)
  have heq : (fun w => (-Complex.I * P w).re) = fun w => (P w).im := by
    funext w
    simp [Complex.mul_re]
  rwa [heq] at h

variable {U : TopologicalSpace.Opens (E n)}

omit [NeZero n] in
/-- The real part of a smooth holomorphic function is smooth over `ℝ`. -/
theorem contDiffOn_re_of_contDiffOn {P : E n → ℂ} (hP : ContDiffOn ℂ ∞ P U) :
    ContDiffOn ℝ ∞ (fun w => (P w).re) U :=
  Complex.reCLM.contDiff.comp_contDiffOn (hP.restrict_scalars ℝ)

omit [NeZero n] in
theorem contDiffOn_im_of_contDiffOn {P : E n → ℂ} (hP : ContDiffOn ℂ ∞ P U) :
    ContDiffOn ℝ ∞ (fun w => (P w).im) U :=
  Complex.imCLM.contDiff.comp_contDiffOn (hP.restrict_scalars ℝ)

omit [NeZero n] in
theorem eventually_differentiableAt_of_contDiffOn {P : E n → ℂ} (hP : ContDiffOn ℂ ∞ P U)
    (x : U) : ∀ᶠ w in 𝓝 (x : E n), DifferentiableAt ℂ P w :=
  Filter.eventually_of_mem (U.isOpen.mem_nhds x.2) fun w hw =>
    (hP.contDiffAt (U.isOpen.mem_nhds hw)).differentiableAt (by simp)

/-- **Real parts of holomorphic functions are harmonic for every Kähler form** on `U ⊆ ℂⁿ`
(`P` complex-smooth on `U`). -/
theorem laplaceBeltrami_re_eq_zero (ω₀ : KahlerForm n U) {P : E n → ℂ}
    (hP : ContDiffOn ℂ ∞ P U) (x : U) :
    laplaceBeltrami ω₀ (restrictSmooth U (contDiffOn_re_of_contDiffOn hP)) x = 0 :=
  laplaceBeltrami_eq_zero_of_ddbar_eq_zero ω₀ _ x
    (ddbar_re_eq_zero (eventually_differentiableAt_of_contDiffOn hP x))

/-- **Imaginary parts of holomorphic functions are harmonic for every Kähler form.** -/
theorem laplaceBeltrami_im_eq_zero (ω₀ : KahlerForm n U) {P : E n → ℂ}
    (hP : ContDiffOn ℂ ∞ P U) (x : U) :
    laplaceBeltrami ω₀ (restrictSmooth U (contDiffOn_im_of_contDiffOn hP)) x = 0 :=
  laplaceBeltrami_eq_zero_of_ddbar_eq_zero ω₀ _ x
    (ddbar_im_eq_zero (eventually_differentiableAt_of_contDiffOn hP x))

omit [NeZero n] in
/-- `z ↦ z_j^k` is a polynomial, hence smooth and holomorphic. -/
theorem contDiff_coord_pow (j : Fin n) (k : ℕ) : ContDiff ℂ ∞ fun w : E n => w j ^ k :=
  (EuclideanSpace.proj j : E n →L[ℂ] ℂ).contDiff.pow k

/-- **`Re z_j^k` is harmonic for every Kähler form**, in particular for every product of cones and
Euclidean factors. In the cone coordinates of a cone factor it is `ρ^{k/β} cos(kθ)`
(`re_pow_coordSlice_conePolar`). -/
theorem laplaceBeltrami_re_pow_eq_zero (ω₀ : KahlerForm n U) (j : Fin n) (k : ℕ) (x : U) :
    laplaceBeltrami ω₀
      (restrictSmooth U (contDiffOn_re_of_contDiffOn (contDiff_coord_pow j k).contDiffOn)) x =
      0 :=
  laplaceBeltrami_re_eq_zero ω₀ (contDiff_coord_pow j k).contDiffOn x

/-- **`Im z_j^k` is harmonic for every Kähler form**; in cone coordinates it is
`ρ^{k/β} sin(kθ)`. -/
theorem laplaceBeltrami_im_pow_eq_zero (ω₀ : KahlerForm n U) (j : Fin n) (k : ℕ) (x : U) :
    laplaceBeltrami ω₀
      (restrictSmooth U (contDiffOn_im_of_contDiffOn (contDiff_coord_pow j k).contDiffOn)) x =
      0 :=
  laplaceBeltrami_im_eq_zero ω₀ (contDiff_coord_pow j k).contDiffOn x

end Holomorphic

/-! ### The logarithmic barrier -/

section Log

variable {U : TopologicalSpace.Opens (E n)}

/-- `i∂∂̄ log |z_j|² = 0` off `{z_j = 0}`. -/
theorem ddbar_log_coordNormSq_eq_zero (j : Fin n) {z : E n} (hz : z j ≠ 0) :
    ddbar (fun w => Real.log (coordNormSq j w)) z = 0 := by
  have hs : 0 < coordNormSq j z := coordNormSq_pos hz
  have hg : ContDiffAt ℝ 2 Real.log (coordNormSq j z) := Real.contDiffAt_log.mpr hs.ne'
  refine ddbar_eq_zero_of_coeffMatrix_eq_zero (hg.comp z (contDiff_coordNormSq j).contDiffAt) ?_
  rw [coeffMatrix_ddbar_comp_coordNormSq j hg]
  have h0 : radialCoeff Real.log (coordNormSq j z) = 0 := by
    have h := radialCoeff_const_add_mul_log 0 1 hs
    simpa using h
  rw [h0]
  simp

theorem contDiffOn_log_coordNormSq (j : Fin n) (hU : ∀ z ∈ U, z j ≠ 0) :
    ContDiffOn ℝ ∞ (fun w => Real.log (coordNormSq j w)) U := fun z hz =>
  ((Real.contDiffAt_log.mpr (coordNormSq_pos (hU z hz)).ne').comp z
    (contDiff_coordNormSq j).contDiffAt).contDiffWithinAt

/-- **The logarithmic barrier is harmonic:** `log |z_j|²` (hence `log ρ_j = (β_j/2) log |z_j|²`) is
harmonic off `{z_j = 0}` for every Kähler form. This is the barrier `ε ∑_a log r_a` of the maximum
principle in de Borbon–Edwards (Lemma 3.2). -/
theorem laplaceBeltrami_log_coordNormSq_eq_zero (ω₀ : KahlerForm n U) (j : Fin n)
    (hU : ∀ z ∈ U, z j ≠ 0) (x : U) :
    laplaceBeltrami ω₀ (restrictSmooth U (contDiffOn_log_coordNormSq j hU)) x = 0 :=
  laplaceBeltrami_eq_zero_of_ddbar_eq_zero ω₀ _ x (ddbar_log_coordNormSq_eq_zero j (hU x x.2))

end Log

/-! ### Products of cones and Euclidean factors -/

section Model

variable (θ : ConeWeights n) {U : TopologicalSpace.Opens (E n)}
  (hU : (U : Set (E n)) ⊆ modelDomain θ)

theorem modelConeMatrix_inv {z : E n} (hz : z ∈ modelDomain θ) :
    (modelConeMatrix θ z)⁻¹ = Matrix.diagonal fun j => ((modelWeight θ z j)⁻¹ : ℂ) := by
  refine Matrix.inv_eq_left_inv ?_
  rw [modelConeMatrix, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one
  rename_i j
  have h : (modelWeight θ z j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (modelWeight_pos hz j).ne'
  exact inv_mul_cancel₀ h

/-- The complex-trace Laplacian of the model: `tr_ω(i∂∂̄ f) = ∑_j Δ_{z_j} f / (4 w_j)`. -/
theorem laplacian_modelConeFormOn {f : E n → ℝ} (x : U) (hf : ContDiffAt ℝ 2 f x) :
    (modelConeFormOn θ U hU).laplacian (fun y : U => f y) x =
      ∑ j, coordLaplacian j f x / (4 * modelWeight θ x j) := by
  rw [laplacian_opens, relTrace, modelConeFormOn_coeffMatrix, modelConeMatrix_inv θ (hU x.2)]
  change RCLike.re (Matrix.diagonal (fun j => ((modelWeight θ x j)⁻¹ : ℂ)) *
    complexHessian f x).trace = _
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.diagonal_mul, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul, re_complexHessian_diag hf j]
  have hw := (modelWeight_pos (hU x.2) j).ne'
  field_simp

/-- **The Laplace–Beltrami operator of a product of cones and Euclidean factors:**
`Δ_g f = ∑_j Δ_{z_j} f / (2 w_j)`, with `w_j = β_j² |z_j|^(2β_j-2)` on a cone factor and `w_j = 1`
on a Euclidean factor. -/
theorem laplaceBeltrami_modelConeFormOn {f : E n → ℝ} (hf : ContDiffOn ℝ ∞ f U) (x : U) :
    laplaceBeltrami (modelConeFormOn θ U hU) (restrictSmooth U hf) x =
      ∑ j, coordLaplacian j f x / (2 * modelWeight θ x j) := by
  have hf2 : ContDiffAt ℝ 2 f x :=
    (hf.contDiffAt (U.isOpen.mem_nhds x.2)).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  rw [laplaceBeltrami_eq_two_mul_laplacian]
  change 2 * (modelConeFormOn θ U hU).laplacian (fun y : U => f y) x = _
  rw [laplacian_modelConeFormOn θ hU x hf2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hw := (modelWeight_pos (hU x.2) j).ne'
  field_simp
  ring

/-- The same, split into the cone factors and the Euclidean factors:
`Δ_g f = ∑_{cone j} Δ_{z_j} f / (2β_j² |z_j|^(2β_j-2)) + ∑_{Euclidean j} ½ Δ_{z_j} f`. -/
theorem laplaceBeltrami_modelConeFormOn_split {f : E n → ℝ} (hf : ContDiffOn ℝ ∞ f U) (x : U) :
    laplaceBeltrami (modelConeFormOn θ U hU) (restrictSmooth U hf) x =
      ∑ j, (match θ.angle j with
        | none => coordLaplacian j f x / 2
        | some β => coordLaplacian j f x /
            (2 * (β.beta ^ 2 * ‖(x : E n) j‖ ^ (2 * β.beta - 2)))) := by
  rw [laplaceBeltrami_modelConeFormOn θ hU hf x]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases hθ : θ.angle j with
  | none => rw [modelWeight_of_none hθ, mul_one]
  | some β => rw [modelWeight_of_some hθ]

/-- **Polar form on a cone factor.** If `θ_j = some β` and `p = coordSlice j w (ρ^{1/β} e^{iθ})`
lies in `U`, then the `j`-th term of the Laplacian is
`Δ_{z_j} f / (2 w_j) = ½ (F_ρρ + ρ⁻¹ F_ρ + (βρ)⁻² F_θθ)` with `F(ρ, θ) = f(coordSlice j w
(ρ^{1/β} e^{iθ}))`. -/
theorem coordLaplacian_div_modelWeight_conePolar {f : E n → ℝ} {j : Fin n} {β : ConeAngle}
    (hθj : θ.angle j = some β) (w : E n) {ρ φ : ℝ} (hρ : 0 < ρ)
    (hf : ContDiffAt ℝ 2 f (coordSlice j w (polarMap (ρ ^ β.beta⁻¹, φ)))) :
    coordLaplacian j f (coordSlice j w (polarMap (ρ ^ β.beta⁻¹, φ))) /
        (2 * modelWeight θ (coordSlice j w (polarMap (ρ ^ β.beta⁻¹, φ))) j) =
      (deriv (deriv fun s : ℝ => f (coordSlice j w (polarMap (s ^ β.beta⁻¹, φ)))) ρ +
        ρ⁻¹ * deriv (fun s : ℝ => f (coordSlice j w (polarMap (s ^ β.beta⁻¹, φ)))) ρ +
        (β.beta * ρ)⁻¹ ^ 2 *
          deriv (deriv fun t : ℝ => f (coordSlice j w (polarMap (ρ ^ β.beta⁻¹, t)))) φ) / 2 := by
  have hβ := β.pos
  rw [coordLaplacian_conePolar hβ hρ hf, modelWeight_of_some hθj, coordSlice_apply_self,
    norm_polarMap_of_nonneg (Real.rpow_nonneg hρ.le _)]
  -- `(ρ^{1/β})^(2β-2) = ρ^(2 - 2/β)`
  have hpow : (ρ ^ β.beta⁻¹) ^ (2 * β.beta - 2) * ρ ^ (2 * β.beta⁻¹ - 2) = 1 := by
    rw [← Real.rpow_mul hρ.le, ← Real.rpow_add hρ]
    have : β.beta⁻¹ * (2 * β.beta - 2) + (2 * β.beta⁻¹ - 2) = 0 := by
      field_simp
      ring
    rw [this, Real.rpow_zero]
  have hpow' : (ρ ^ β.beta⁻¹) ^ (2 * β.beta - 2) = (ρ ^ (2 * β.beta⁻¹ - 2))⁻¹ :=
    eq_inv_of_mul_eq_one_left hpow
  rw [hpow']
  set C := ρ ^ (2 * β.beta⁻¹ - 2) with hC
  set L := coordLaplacian j f (coordSlice j w (polarMap (ρ ^ β.beta⁻¹, φ)))
  have hCpos : 0 < C := Real.rpow_pos_of_pos hρ _
  have hb := hβ.ne'
  field_simp

/-! ### The potential terms: degree-two functions -/

/-- The `j`-th term of the potential: `ρ_j² = |z_j|^{2β_j}` on a cone factor, `|z_j|²` on a
Euclidean factor. In the coordinates of the paper of de Borbon–Edwards this is `r_a²` (cone) or
`s_1² + s_2²` (Euclidean). -/
noncomputable def potentialTerm (j : Fin n) (z : E n) : ℝ :=
  coordProfile (θ.angle j) (coordNormSq j z)

include hU in
theorem contDiffOn_potentialTerm (j : Fin n) : ContDiffOn ℝ ∞ (potentialTerm θ j) U :=
  fun _ hz => ((contDiffAt_coordProfile (hU hz) j).comp _
    (contDiff_coordNormSq j).contDiffAt).contDiffWithinAt

/-- `tr_ω(i∂∂̄ (ρ_j²)) = 1`: each potential term has complex-trace Laplacian `1`. -/
theorem laplacian_potentialTerm (j : Fin n) (x : U) :
    (modelConeFormOn θ U hU).laplacian (fun y : U => potentialTerm θ j y) x = 1 := by
  rw [laplacian_opens, relTrace, modelConeFormOn_coeffMatrix, modelConeMatrix_inv θ (hU x.2)]
  change RCLike.re (Matrix.diagonal (fun k => ((modelWeight θ x k)⁻¹ : ℂ)) *
    (ddbar (fun w => coordProfile (θ.angle j) (coordNormSq j w)) x).coeffMatrix).trace = 1
  rw [coeffMatrix_ddbar_comp_coordNormSq j (contDiffAt_coordProfile (hU x.2) j),
    radialCoeff_coordProfile (hU x.2) j, Matrix.trace]
  simp only [Matrix.diag, Matrix.diagonal_mul, Matrix.single_apply, RCLike.re_to_complex,
    Complex.re_sum]
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
  simp only [and_self, ite_true]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re,
    inv_mul_cancel₀ (modelWeight_pos (hU x.2) j).ne']

/-- **Each potential term has Laplacian `2`:** `Δ_g ρ_j² = 2` (`Δ_g |z_j|² = 2` on a Euclidean
factor). With the paper's normalisation `g_paper = ½ g` this is `Δ r_a² = 4`. -/
theorem laplaceBeltrami_potentialTerm (j : Fin n) (x : U) :
    laplaceBeltrami (modelConeFormOn θ U hU) (restrictSmooth U (contDiffOn_potentialTerm θ hU j))
      x = 2 := by
  rw [laplaceBeltrami_eq_two_mul_laplacian]
  change 2 * (modelConeFormOn θ U hU).laplacian (fun y : U => potentialTerm θ j y) x = 2
  rw [laplacian_potentialTerm, mul_one]

/-- **Differences of potential terms are harmonic:** `ρ_a² - ρ_b²`, `ρ_a² - |z_j|²`, … (the
degree-two harmonic functions `r_a² - r_b²`, `r_a² - (s_1² + s_2²)` of de Borbon–Edwards,
Prop. 3.4). -/
theorem laplaceBeltrami_potentialTerm_sub (j k : Fin n) (x : U) :
    laplaceBeltrami (modelConeFormOn θ U hU)
      (restrictSmooth U ((contDiffOn_potentialTerm θ hU j).sub (contDiffOn_potentialTerm θ hU k)))
      x = 0 := by
  rw [laplaceBeltrami_eq_two_mul_laplacian]
  change 2 * (modelConeFormOn θ U hU).laplacian
    (fun y : U => potentialTerm θ j y - potentialTerm θ k y) x = 0
  have hj : ContDiffAt ℝ 2 (potentialTerm θ j) x :=
    ((contDiffAt_coordProfile (hU x.2) j).comp _ (contDiff_coordNormSq j).contDiffAt)
  have hk : ContDiffAt ℝ 2 (potentialTerm θ k) x :=
    ((contDiffAt_coordProfile (hU x.2) k).comp _ (contDiff_coordNormSq k).contDiffAt)
  have hsub := laplacian_opens (modelConeFormOn θ U hU)
    (fun w => potentialTerm θ j w - potentialTerm θ k w) x
  have hddbar : ddbar (fun w => potentialTerm θ j w - potentialTerm θ k w) x =
      ddbar (potentialTerm θ j) x - ddbar (potentialTerm θ k) x := ddbar_sub hj hk
  rw [hsub, hddbar, relTrace_sub, ← laplacian_opens, ← laplacian_opens,
    laplacian_potentialTerm, laplacian_potentialTerm, sub_self, mul_zero]

end Model

/-! ### The standard cone -/

section Standard

/-- **The Laplacian of the standard two-dimensional cone in polar coordinates.** For `n = 1`,
`f` smooth on `{z ≠ 0}`, `ρ > 0` and `F(ρ, θ) = f(ρ^{1/β} e^{iθ})`:

  `Δ_g f = ½ (F_ρρ + ρ⁻¹ F_ρ + (βρ)⁻² F_θθ)`,

where `g = ω_β(·, J·) = 2 (dρ² + β²ρ² dθ²)`. -/
theorem laplaceBeltrami_standardCone_polar (β : ConeAngle) {f : E 1 → ℝ}
    (hf : ContDiffOn ℝ ∞ f (modelDomain (singleConeWeights (n := 1) β))) (w : E 1) {ρ φ : ℝ}
    (hρ : 0 < ρ) :
    laplaceBeltrami (standardConeForm (n := 1) β) (restrictSmooth _ hf)
        ⟨coordSlice 0 w (polarMap (ρ ^ β.beta⁻¹, φ)),
          (by rw [mem_modelDomain_single, coordSlice_apply_self]
              exact polarMap_ne_zero (Real.rpow_pos_of_pos hρ _))⟩ =
      (deriv (deriv fun s : ℝ => f (coordSlice 0 w (polarMap (s ^ β.beta⁻¹, φ)))) ρ +
        ρ⁻¹ * deriv (fun s : ℝ => f (coordSlice 0 w (polarMap (s ^ β.beta⁻¹, φ)))) ρ +
        (β.beta * ρ)⁻¹ ^ 2 *
          deriv (deriv fun t : ℝ => f (coordSlice 0 w (polarMap (ρ ^ β.beta⁻¹, t)))) φ) / 2 := by
  set p := coordSlice 0 w (polarMap (ρ ^ β.beta⁻¹, φ))
  have hp : p ∈ modelDomain (singleConeWeights (n := 1) β) := by
    rw [mem_modelDomain_single, coordSlice_apply_self]
    exact polarMap_ne_zero (Real.rpow_pos_of_pos hρ _)
  have hf2 : ContDiffAt ℝ 2 f p :=
    (hf.contDiffAt ((modelDomain _).isOpen.mem_nhds hp)).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  refine (laplaceBeltrami_modelConeFormOn (singleConeWeights β) subset_rfl hf _).trans ?_
  rw [Fin.sum_univ_one]
  exact coordLaplacian_div_modelWeight_conePolar (singleConeWeights β)
    (singleConeWeights_angle_zero β) w hρ hf2

end Standard

end ConicalKahler
