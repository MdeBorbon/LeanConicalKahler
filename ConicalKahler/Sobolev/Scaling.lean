module

public import ConicalKahler.Sobolev.ConeApprox

/-!
# Scaling: dilations of weak solutions and the scaled estimates of §2.5.1

The paper's dilations `λ(r_a, θ_a, s) = (λ r_a, θ_a, λ s)` are scalar multiplication `x ↦ t x` in
the real coordinates. For `t > 0` and a domain `Ω`, write `t⁻¹Ω = {x | t x ∈ Ω}` (`dilDom t Ω`).

## Results

* `map_smul_restrict`, `setIntegral_comp_smul_dilDom`:
  `∫_{t⁻¹Ω} F(t x) dx = t^{-d} ∫_Ω F`.
* `dilLp`, `norm_dilLp_sq`: `u ↦ u(t ·)` maps `L²(Ω)` to `L²(t⁻¹Ω)` with
  `‖u(t ·)‖² = t^{-d} ‖u‖²`.
* `dilate`, `dilate_mem_W12`: `(u, G) ↦ (u(t ·), t G(t ·))` maps `W^{1,2}(Ω)` to `W^{1,2}(t⁻¹Ω)`,
  so `∇(u(t ·)) = t (∇u)(t ·)`. `norm_dilate_snd_sq`: the **Dirichlet energy** scales as
  `‖∇(u(t ·))‖² = t^{2-d} ‖∇u‖²`.
* `CoeffField.IsWeakSolution.dilate`: if `A` is **dilation invariant** (`A(t x) = A(x)`) and
  `-div(A ∇u) = f` on `Ω`, then `-div(A ∇(u(t ·))) = t² f(t ·)` on `t⁻¹Ω`. This is the scaling of
  the Laplacian, `Δ(u(t ·)) = t² (Δu)(t ·)`.
* `coneCoeffA_smul`: the cone coefficients `A = g⁻¹` are dilation invariant (`g` is a cone metric).
* `caccioppoli_ball`: the Caccioppoli inequality on `B(p, 1) ⊂ B(p, 2)` with a constant
  `1 + 4ΛΓ₀²` **independent of the centre `p`** (a translated bump function).
* `caccioppoli_ball_scaled`: **the scaled Caccioppoli inequality** (§2.5.1). For
  dilation-invariant `A` and `B(p, 2ρ) ⊆ Ω`,
  `λ ∫_{B(p,ρ)} |∇u|² ≤ ρ² ∫_{B(p,2ρ)} f² + (1 + 4ΛΓ₀²) ρ⁻² ∫_{B(p,2ρ)} u²`.
  It is obtained from the unit-scale estimate by dilation, as in the paper.
* `dilDom_coneBall`: dilations map cone balls to cone balls, `t⁻¹ B(t p, t ρ) = B(p, ρ)`. With
  `setIntegral_comp_smul_dilDom` this gives the invariance of the scaled norms
  `‖u‖_{B(x,ρ)} = (ρ^{-m} ∫_{B(x,ρ)} u²)^{1/2}` (`scaledNormSq_dilate`).

The balls in `caccioppoli_ball_scaled` are Euclidean balls in the real coordinates. Geodesic
balls are comparable (`coneBall_subset_closedBall`, `ball_subset_coneBall`), so the estimate holds
between geodesic balls `B(p, ρ) ⊂ B(p, Kρ)` with `K = 2 upperConst β / lowerConst β`. The exact
ratio `2` for geodesic balls would need cut-offs that are Lipschitz for `d_g`; this is not done.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set Module
open scoped ContDiff ENNReal ComplexConjugate

namespace ConicalKahler.Sobolev

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The dilated domain `t⁻¹ Ω = {x | t x ∈ Ω}`. -/
def dilDom (t : ℝ) (Ω : Set 𝔼) : Set 𝔼 := (fun x => t • x) ⁻¹' Ω

theorem measurableSet_dilDom {t : ℝ} {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) :
    MeasurableSet (dilDom t Ω) :=
  (measurable_const_smul t) hΩ

theorem isOpen_dilDom {t : ℝ} {Ω : Set 𝔼} (hΩ : IsOpen Ω) : IsOpen (dilDom t Ω) :=
  hΩ.preimage (continuous_const_smul t)

theorem map_smul_restrict {t : ℝ} (ht : 0 < t) {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) :
    Measure.map (fun x : 𝔼 => t • x) (volume.restrict (dilDom t Ω)) =
      ENNReal.ofReal ((t ^ d)⁻¹) • volume.restrict Ω := by
  rw [dilDom, ← Measure.restrict_map (measurable_const_smul t) hΩ,
    Measure.map_addHaar_smul volume ht.ne', finrank_euclideanSpace_fin, Measure.restrict_smul,
    abs_of_pos (by positivity)]

/-- **Change of variables under dilation:** `∫_{t⁻¹Ω} F(t x) dx = t^{-d} ∫_Ω F`. -/
theorem setIntegral_comp_smul_dilDom {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {t : ℝ} (ht : 0 < t) {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) (F : 𝔼 → E) :
    ∫ x in dilDom t Ω, F (t • x) = (t ^ d)⁻¹ • ∫ y in Ω, F y := by
  have h := (Homeomorph.smulOfNeZero t ht.ne' : 𝔼 ≃ₜ 𝔼).measurableEmbedding.integral_map
    (μ := volume.restrict (dilDom t Ω)) F
  have hcoe : ⇑(Homeomorph.smulOfNeZero t ht.ne' : 𝔼 ≃ₜ 𝔼) = fun x => t • x := rfl
  rw [hcoe, map_smul_restrict ht hΩ, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity)] at h
  exact h.symm

theorem memLp_comp_smul {E : Type*} [NormedAddCommGroup E] {t : ℝ} (ht : 0 < t) {Ω : Set 𝔼}
    (hΩ : MeasurableSet Ω) {g : 𝔼 → E} (hg : MemLp g 2 (volume.restrict Ω)) :
    MemLp (fun x => g (t • x)) 2 (volume.restrict (dilDom t Ω)) := by
  have h : MemLp g 2 (Measure.map (fun x : 𝔼 => t • x) (volume.restrict (dilDom t Ω))) := by
    rw [map_smul_restrict ht hΩ]
    exact hg.smul_measure ENNReal.ofReal_ne_top
  exact h.comp_of_map (measurable_const_smul t).aemeasurable

/-- The dilation `u ↦ u(t ·)` from `L²(Ω)` to `L²(t⁻¹Ω)`. -/
def dilLp {E : Type*} [NormedAddCommGroup E] {t : ℝ} (ht : 0 < t) {Ω : Set 𝔼}
    (hΩ : MeasurableSet Ω) (f : Lp E 2 (volume.restrict Ω)) : Lp E 2 (volume.restrict (dilDom t Ω)) :=
  (memLp_comp_smul ht hΩ (Lp.memLp f)).toLp fun x => f (t • x)

theorem dilLp_ae {E : Type*} [NormedAddCommGroup E] {t : ℝ} (ht : 0 < t) {Ω : Set 𝔼}
    (hΩ : MeasurableSet Ω) (f : Lp E 2 (volume.restrict Ω)) :
    dilLp ht hΩ f =ᵐ[volume.restrict (dilDom t Ω)] fun x => f (t • x) :=
  (memLp_comp_smul ht hΩ (Lp.memLp f)).coeFn_toLp

/-- **`‖u(t ·)‖²_{L²(t⁻¹Ω)} = t^{-d} ‖u‖²_{L²(Ω)}`.** -/
theorem norm_dilLp_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {t : ℝ}
    (ht : 0 < t) {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) (f : Lp E 2 (volume.restrict Ω)) :
    ‖dilLp ht hΩ f‖ ^ 2 = (t ^ d)⁻¹ * ‖f‖ ^ 2 := by
  rw [dilLp, norm_toLp_sq, setIntegral_comp_smul_dilDom ht hΩ (fun y => ‖f y‖ ^ 2), smul_eq_mul]
  congr 1
  rw [← norm_toLp_sq (Lp.memLp f), Lp.toLp_coeFn]

/-! ### Test functions under dilation -/

theorem IsTestFn.comp_inv_smul {t : ℝ} (ht : 0 < t) {Ω : Set 𝔼} {φ : 𝔼 → ℝ}
    (hφ : IsTestFn (dilDom t Ω) φ) : IsTestFn Ω fun y => φ (t⁻¹ • y) := by
  refine ⟨hφ.contDiff.comp (contDiff_const_smul _), ?_, ?_⟩
  · exact hφ.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero t⁻¹ (inv_ne_zero ht.ne'))
  · intro y hy
    have h := tsupport_comp_subset_preimage φ
      (continuous_const_smul (t⁻¹ : ℝ) : Continuous fun y : 𝔼 => t⁻¹ • y) hy
    have h2 := hφ.tsupport_subset h
    simpa [dilDom, smul_inv_smul₀ ht.ne'] using h2

theorem IsTestFn.comp_smul {t : ℝ} {Ω : Set 𝔼} {φ : 𝔼 → ℝ} (ht : 0 < t) (hφ : IsTestFn Ω φ) :
    IsTestFn (dilDom t Ω) fun x => φ (t • x) := by
  refine ⟨hφ.contDiff.comp (contDiff_const_smul _), ?_, ?_⟩
  · exact hφ.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero t ht.ne')
  · intro x hx
    exact hφ.tsupport_subset
      (tsupport_comp_subset_preimage φ (continuous_const_smul t : Continuous fun y : 𝔼 => t • y) hx)

theorem fderiv_comp_smul_apply {φ : 𝔼 → ℝ} (hφ : Differentiable ℝ φ) (s : ℝ) (y w : 𝔼) :
    fderiv ℝ (fun y => φ (s • y)) y w = s * fderiv ℝ φ (s • y) w := by
  have h : HasFDerivAt (fun y => φ (s • y))
      ((fderiv ℝ φ (s • y)).comp (s • ContinuousLinearMap.id ℝ 𝔼)) y :=
    (hφ (s • y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul s)
  rw [h.fderiv]
  simp

theorem gradient_comp_smul {φ : 𝔼 → ℝ} (hφ : Differentiable ℝ φ) (s : ℝ) (y : 𝔼) :
    gradient (fun y => φ (s • y)) y = s • gradient φ (s • y) := by
  refine ext_inner_right ℝ fun w => ?_
  rw [inner_gradient, fderiv_comp_smul_apply hφ, real_inner_smul_left, inner_gradient]

/-! ### Dilation of pairs -/

variable [NeZero d]

/-- **The dilation of a pair**: `(u, G) ↦ (u(t ·), t G(t ·))`. -/
def dilate {t : ℝ} (ht : 0 < t) {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) (v : L2Pair volume Ω) :
    L2Pair volume (dilDom t Ω) :=
  WithLp.toLp 2 (dilLp ht hΩ v.fst, t • dilLp ht hΩ v.snd)

@[simp] theorem dilate_fst {t : ℝ} (ht : 0 < t) {Ω : Set 𝔼} (hΩ : MeasurableSet Ω)
    (v : L2Pair volume Ω) : (dilate ht hΩ v).fst = dilLp ht hΩ v.fst := rfl

@[simp] theorem dilate_snd {t : ℝ} (ht : 0 < t) {Ω : Set 𝔼} (hΩ : MeasurableSet Ω)
    (v : L2Pair volume Ω) : (dilate ht hΩ v).snd = t • dilLp ht hΩ v.snd := rfl

/-- **Scaling of the Dirichlet energy:** `‖∇(u(t ·))‖² = t^{2-d} ‖∇u‖²`. -/
theorem norm_dilate_snd_sq {t : ℝ} (ht : 0 < t) {Ω : Set 𝔼} (hΩ : MeasurableSet Ω)
    (v : L2Pair volume Ω) : ‖(dilate ht hΩ v).snd‖ ^ 2 = t ^ 2 * (t ^ d)⁻¹ * ‖v.snd‖ ^ 2 := by
  rw [dilate_snd, norm_smul, mul_pow, norm_dilLp_sq, Real.norm_eq_abs, sq_abs]
  ring

/-- The weak-gradient identity in integral form characterises `W^{1,2}(Ω)`. -/
theorem mem_W12_of_integral {Ω : Set 𝔼} {v : L2Pair volume Ω}
    (h : ∀ (φ : 𝔼 → ℝ) (_ : IsTestFn Ω φ) (w : 𝔼),
      ∫ x in Ω, v.fst x * fderiv ℝ φ x w = -∫ x in Ω, φ x * ⟪v.snd x, w⟫_ℝ) :
    v ∈ W12 volume Ω := by
  intro φ hφ w
  rw [L2.inner_def, L2.inner_def]
  have h1 : ∫ x in Ω, ⟪v.fst x, ((hφ.memLp_fderiv_apply (μ := volume) w 2 Ω).toLp
      (fun x => fderiv ℝ φ x w)) x⟫_ℝ = ∫ x in Ω, v.fst x * fderiv ℝ φ x w := by
    refine integral_congr_ae ?_
    filter_upwards [(hφ.memLp_fderiv_apply (μ := volume) w 2 Ω).coeFn_toLp] with x hx
    rw [hx]
    simp [mul_comm]
  have h2 : ∫ x in Ω, ⟪v.snd x, ((hφ.memLp_smul_vec (μ := volume) w 2 Ω).toLp
      (fun x => φ x • w)) x⟫_ℝ = ∫ x in Ω, φ x * ⟪v.snd x, w⟫_ℝ := by
    refine integral_congr_ae ?_
    filter_upwards [(hφ.memLp_smul_vec (μ := volume) w 2 Ω).coeFn_toLp] with x hx
    rw [hx, real_inner_smul_right]
  rw [h1, h2]
  exact h φ hφ w

/-- **Dilation preserves `W^{1,2}`:** `∇(u(t ·)) = t (∇u)(t ·)` weakly. -/
theorem dilate_mem_W12 {t : ℝ} (ht : 0 < t) {Ω : Set 𝔼} (hΩ : MeasurableSet Ω)
    {v : L2Pair volume Ω} (hv : v ∈ W12 volume Ω) : dilate ht hΩ v ∈ W12 volume (dilDom t Ω) := by
  refine mem_W12_of_integral fun φ hφ w => ?_
  have ht0 := ht.ne'
  have hφt := hφ.comp_inv_smul ht
  have hW := integral_fst_mul_fderiv hv hφt w
  have e1 : ∫ x in dilDom t Ω, (dilate ht hΩ v).fst x * fderiv ℝ φ x w =
      (t ^ d)⁻¹ * (t * ∫ y in Ω, v.fst y * fderiv ℝ (fun y => φ (t⁻¹ • y)) y w) := by
    calc ∫ x in dilDom t Ω, (dilate ht hΩ v).fst x * fderiv ℝ φ x w
        = ∫ x in dilDom t Ω, (fun y => t * (v.fst y * fderiv ℝ (fun y => φ (t⁻¹ • y)) y w))
            (t • x) := by
          refine integral_congr_ae ?_
          filter_upwards [dilLp_ae ht hΩ v.fst] with x hx
          simp only [dilate_fst, hx, fderiv_comp_smul_apply hφ.differentiable, inv_smul_smul₀ ht0]
          field_simp
      _ = (t ^ d)⁻¹ • ∫ y in Ω, t * (v.fst y * fderiv ℝ (fun y => φ (t⁻¹ • y)) y w) :=
          setIntegral_comp_smul_dilDom ht hΩ
            (fun y => t * (v.fst y * fderiv ℝ (fun y => φ (t⁻¹ • y)) y w))
      _ = _ := by rw [integral_const_mul, smul_eq_mul]
  have e2 : ∫ x in dilDom t Ω, φ x * ⟪(dilate ht hΩ v).snd x, w⟫_ℝ =
      (t ^ d)⁻¹ * (t * ∫ y in Ω, φ (t⁻¹ • y) * ⟪v.snd y, w⟫_ℝ) := by
    calc ∫ x in dilDom t Ω, φ x * ⟪(dilate ht hΩ v).snd x, w⟫_ℝ
        = ∫ x in dilDom t Ω, (fun y => t * (φ (t⁻¹ • y) * ⟪v.snd y, w⟫_ℝ)) (t • x) := by
          refine integral_congr_ae ?_
          filter_upwards [Lp.coeFn_smul t (dilLp ht hΩ v.snd), dilLp_ae ht hΩ v.snd] with x h1 h2
          simp only [dilate_snd, h1, Pi.smul_apply, h2, inv_smul_smul₀ ht0, real_inner_smul_left]
          ring
      _ = (t ^ d)⁻¹ • ∫ y in Ω, t * (φ (t⁻¹ • y) * ⟪v.snd y, w⟫_ℝ) :=
          setIntegral_comp_smul_dilDom ht hΩ (fun y => t * (φ (t⁻¹ • y) * ⟪v.snd y, w⟫_ℝ))
      _ = _ := by rw [integral_const_mul, smul_eq_mul]
  rw [e1, e2, hW]
  ring

/-- **Scaling of weak solutions.** Let `A` be dilation invariant, `A(t x) = A(x)`. If
`-div(A ∇u) = f` weakly on `Ω`, then `-div(A ∇(u(t ·))) = t² f(t ·)` weakly on `t⁻¹Ω`. -/
theorem CoeffField.IsWeakSolution.dilate {c : CoeffField 𝔼 volume} {t : ℝ} (ht : 0 < t)
    (hA : ∀ x, c.A (t • x) = c.A x) {Ω : Set 𝔼} (hΩ : MeasurableSet Ω)
    {f : Lp ℝ 2 (volume.restrict Ω)} {v : L2Pair volume Ω} (hv : c.IsWeakSolution f v) :
    c.IsWeakSolution (t ^ 2 • dilLp ht hΩ f) (Sobolev.dilate ht hΩ v) := by
  rw [CoeffField.isWeakSolution_iff] at hv ⊢
  refine ⟨dilate_mem_W12 ht hΩ hv.1, fun φ hφ => ?_⟩
  have ht0 := ht.ne'
  have hφt := hφ.comp_inv_smul ht
  have hE := hv.2 _ hφt
  have e1 : ∫ x in dilDom t Ω, ⟪c.A x ((Sobolev.dilate ht hΩ v).snd x), gradient φ x⟫_ℝ =
      (t ^ d)⁻¹ * (t ^ 2 * ∫ y in Ω, ⟪c.A y (v.snd y), gradient (fun y => φ (t⁻¹ • y)) y⟫_ℝ) := by
    calc ∫ x in dilDom t Ω, ⟪c.A x ((Sobolev.dilate ht hΩ v).snd x), gradient φ x⟫_ℝ
        = ∫ x in dilDom t Ω, (fun y => t ^ 2 * ⟪c.A y (v.snd y),
            gradient (fun y => φ (t⁻¹ • y)) y⟫_ℝ) (t • x) := by
          refine integral_congr_ae ?_
          filter_upwards [Lp.coeFn_smul t (dilLp ht hΩ v.snd), dilLp_ae ht hΩ v.snd] with x h1 h2
          simp only [dilate_snd, h1, Pi.smul_apply, h2, gradient_comp_smul hφ.differentiable,
            inv_smul_smul₀ ht0, hA, map_smul, real_inner_smul_left, real_inner_smul_right]
          field_simp
      _ = (t ^ d)⁻¹ • ∫ y in Ω, t ^ 2 * ⟪c.A y (v.snd y),
            gradient (fun y => φ (t⁻¹ • y)) y⟫_ℝ :=
          setIntegral_comp_smul_dilDom ht hΩ (fun y => t ^ 2 * ⟪c.A y (v.snd y),
            gradient (fun y => φ (t⁻¹ • y)) y⟫_ℝ)
      _ = _ := by rw [integral_const_mul, smul_eq_mul]
  have e2 : ∫ x in dilDom t Ω, (t ^ 2 • dilLp ht hΩ f) x * φ x =
      (t ^ d)⁻¹ * (t ^ 2 * ∫ y in Ω, f y * φ (t⁻¹ • y)) := by
    calc ∫ x in dilDom t Ω, (t ^ 2 • dilLp ht hΩ f) x * φ x
        = ∫ x in dilDom t Ω, (fun y => t ^ 2 * (f y * φ (t⁻¹ • y))) (t • x) := by
          refine integral_congr_ae ?_
          filter_upwards [Lp.coeFn_smul (t ^ 2) (dilLp ht hΩ f), dilLp_ae ht hΩ f] with x h1 h2
          simp only [h1, Pi.smul_apply, h2, inv_smul_smul₀ ht0, smul_eq_mul]
          ring
      _ = (t ^ d)⁻¹ • ∫ y in Ω, t ^ 2 * (f y * φ (t⁻¹ • y)) :=
          setIntegral_comp_smul_dilDom ht hΩ (fun y => t ^ 2 * (f y * φ (t⁻¹ • y)))
      _ = _ := by rw [integral_const_mul, smul_eq_mul]
  rw [e1, e2, hE]

/-! ### The cone coefficients are dilation invariant -/

theorem coneInvFactor_ofReal_mul (b : ℝ) {t : ℝ} (ht : t ≠ 0) (w z : ℂ) :
    coneInvFactor b ((t : ℂ) * w) z = coneInvFactor b w z := by
  by_cases hw : w = 0
  · subst hw; simp
  have hN : (Complex.normSq w : ℂ) ≠ 0 := by exact_mod_cast Complex.normSq_eq_zero.not.mpr hw
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have h1 : conj ((t : ℂ) * w) * z = (t : ℂ) * (conj w * z) := by
    rw [map_mul, Complex.conj_ofReal, mul_assoc]
  simp only [coneInvFactor, Complex.normSq_mul, Complex.normSq_ofReal, h1, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv]
  push_cast
  field_simp

section ConeHomogeneous

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

theorem coneInvOp_smul (β : κ → ConeAngle) {t : ℝ} (ht : t ≠ 0) (p : RealConeModel κ ι) :
    coneInvOp β (t • p) = coneInvOp β p := by
  ext q : 1
  refine RealConeModel.ext_cone_eucl (fun a => ?_) (fun i => ?_)
  · simp only [coneInvOp, LinearMap.coe_toContinuousLinearMap', coneInvOpₗ, LinearMap.coe_mk,
      AddHom.coe_mk, RealConeModel.cone_ofCones, RealConeModel.cone_smul]
    exact coneInvFactor_ofReal_mul _ ht _ _
  · simp [coneInvOp, coneInvOpₗ]

/-- **`g⁻¹` is dilation invariant:** `A(t x) = A(x)` for `t ≠ 0`. -/
theorem coneCoeffA_smul (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) {t : ℝ} (ht : t ≠ 0)
    (x : 𝔼) : coneCoeffA β e (t • x) = coneCoeffA β e x := by
  simp only [coneCoeffA, map_smul, coneInvOp_smul β ht]

/-- **Dilations map cone balls to cone balls:** `t⁻¹ B(t p, t ρ) = B(p, ρ)` for `t > 0`. -/
theorem dilDom_coneBall (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) {t : ℝ} (ht : 0 < t)
    (p : RealConeModel κ ι) (ρ : ℝ) :
    dilDom t (coneBall β e (t • p) (t * ρ)) = coneBall β e p ρ := by
  ext x
  simp only [dilDom, coneBall, Set.mem_preimage, LinearIsometryEquiv.image_eq_preimage_symm,
    map_smul, Metric.mem_ball]
  change dist (ConeProduct.mk (t • (coordIso e).symm x) : ConeProduct β ι)
      (ConeProduct.mk (t • p)) < t * ρ ↔ dist (ConeProduct.mk ((coordIso e).symm x) :
        ConeProduct β ι) (ConeProduct.mk p) < ρ
  rw [ConeProduct.dist_smul ht]
  exact mul_lt_mul_iff_right₀ ht

/-- The scaled `L²` norm `‖u‖²_{B} = ρ^{-d} ∫_B u²` on a set of radius `ρ`. -/
def scaledNormSq (u : 𝔼 → ℝ) (B : Set 𝔼) (ρ : ℝ) : ℝ := (ρ ^ d)⁻¹ * ∫ x in B, u x ^ 2

/-- **The scaled norms are dilation invariant** (paper, §2.5):
`‖u(t ·)‖_{B(p, ρ)} = ‖u‖_{B(t p, t ρ)}` for cone balls. -/
theorem scaledNormSq_dilate (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) {t : ℝ}
    (ht : 0 < t) (u : 𝔼 → ℝ) (p : RealConeModel κ ι) {ρ : ℝ} (hρ : 0 < ρ) :
    scaledNormSq (fun x => u (t • x)) (coneBall β e p ρ) ρ =
      scaledNormSq u (coneBall β e (t • p) (t * ρ)) (t * ρ) := by
  rw [scaledNormSq, scaledNormSq, ← dilDom_coneBall β e ht p ρ,
    setIntegral_comp_smul_dilDom ht (isOpen_coneBall β e _ _).measurableSet (fun y => u y ^ 2),
    smul_eq_mul, mul_pow]
  have : t ^ d ≠ 0 := pow_ne_zero _ ht.ne'
  have : ρ ^ d ≠ 0 := pow_ne_zero _ hρ.ne'
  field_simp

end ConeHomogeneous

/-! ### Scaled Caccioppoli estimates -/

/-- The bump function `η₀` with `η₀ = 1` on `B̄(0, 1)` and support in `B̄(0, 3/2)`. -/
def unitBump : ContDiffBump (0 : 𝔼) where
  rIn := 1
  rOut := 3 / 2
  rIn_pos := one_pos
  rIn_lt_rOut := by norm_num

theorem isTestFn_unitBump_translate (p : 𝔼) :
    IsTestFn (Metric.ball p 2) fun x => (unitBump (d := d)) (x - p) := by
  refine ⟨unitBump.contDiff.comp (contDiff_id.sub contDiff_const), ?_, ?_⟩
  · exact unitBump.hasCompactSupport.comp_homeomorph (Homeomorph.subRight p)
  · intro x hx
    have hx' : x ∈ tsupport ((unitBump (d := d) : 𝔼 → ℝ) ∘ fun x => x - p) := hx
    have h := tsupport_comp_subset_preimage (unitBump (d := d) : 𝔼 → ℝ)
      (continuous_id.sub continuous_const) hx'
    rw [Set.mem_preimage, ContDiffBump.tsupport_eq, Metric.mem_closedBall, dist_zero_right] at h
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖x - p‖ ≤ 3 / 2 at h
    linarith

theorem gradient_unitBump_translate (p x : 𝔼) :
    gradient (fun x => (unitBump (d := d)) (x - p)) x = gradient (unitBump (d := d)) (x - p) := by
  simp only [gradient, fderiv_comp_sub]

/-- **Caccioppoli on unit balls, uniformly in the centre.** There is `Γ` (depending only on `d`)
such that for every coefficient field and every `B(p, 2) ⊆ Ω`:
`λ ∫_{B(p,1)} |∇u|² ≤ ∫_{B(p,2)} f² + (1 + 4ΛΓ²) ∫_{B(p,2)} u²`. -/
theorem exists_caccioppoli_ball : ∃ Γ : ℝ, 0 ≤ Γ ∧ ∀ (c : CoeffField 𝔼 volume) {Ω : Set 𝔼}
    (_ : IsOpen Ω) (p : 𝔼) (_ : Metric.ball p 2 ⊆ Ω) {f : Lp ℝ 2 (volume.restrict Ω)}
    {v : L2Pair volume Ω} (_ : c.IsWeakSolution f v),
    c.lam * ∫ x in Metric.ball p 1, ‖v.snd x‖ ^ 2 ≤
      (∫ x in Metric.ball p 2, f x ^ 2) + (1 + 4 * c.Λ * Γ ^ 2) *
        ∫ x in Metric.ball p 2, v.fst x ^ 2 := by
  obtain ⟨Γ, hΓ0, -, hΓ⟩ := exists_bound_testFn (isTestFn_unitBump_translate (d := d) 0)
  refine ⟨Γ, hΓ0, fun c Ω hΩ p hp f v hv => ?_⟩
  set η : 𝔼 → ℝ := fun x => (unitBump (d := d)) (x - p) with hη_def
  have hηt : IsTestFn Ω η := (isTestFn_unitBump_translate p).mono hp
  have hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1 := fun x => ⟨unitBump.nonneg, unitBump.le_one⟩
  have hη2 : ∀ x, η x ^ 2 ≤ 1 := fun x => by nlinarith [hη01 x]
  have hgη : ∀ x, ‖gradient η x‖ ≤ Γ := fun x => by
    rw [hη_def, gradient_unitBump_translate]
    have := hΓ (x - p)
    rwa [gradient_unitBump_translate, sub_zero] at this
  have hone : ∀ x ∈ Metric.ball p 1, η x = 1 := fun x hx => by
    refine unitBump.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm]
    exact (Metric.mem_ball.mp hx).le
  have hout : ∀ x ∉ Metric.ball p 2, x ∉ tsupport η := fun x hx h =>
    hx ((isTestFn_unitBump_translate p).tsupport_subset h)
  have hB1 : Metric.ball p 1 ⊆ Ω := (Metric.ball_subset_ball (by norm_num)).trans hp
  have hcac := caccioppoli_norm c hΩ hv hηt
  -- the left-hand side
  have hint : Integrable (fun x => η x ^ 2 * ‖v.snd x‖ ^ 2) (volume.restrict Ω) :=
    (Lp.memLp v.snd).norm.integrable_sq.bdd_mul (hηt.continuous.pow 2).aestronglyMeasurable
      (c := 1) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hη2 x)
  have hL : ∫ x in Metric.ball p 1, ‖v.snd x‖ ^ 2 ≤ ∫ x in Ω, η x ^ 2 * ‖v.snd x‖ ^ 2 :=
    calc ∫ x in Metric.ball p 1, ‖v.snd x‖ ^ 2 = ∫ x in Metric.ball p 1, η x ^ 2 * ‖v.snd x‖ ^ 2 :=
          setIntegral_congr_fun Metric.isOpen_ball.measurableSet fun x hx => by
            simp only [hone x hx, one_pow, one_mul]
      _ ≤ ∫ x in Ω, η x ^ 2 * ‖v.snd x‖ ^ 2 :=
          setIntegral_mono_set hint (Eventually.of_forall fun x => by positivity) hB1.eventuallyLE
  -- the right-hand side
  have hf2 : Integrable (fun x => f x ^ 2) (volume.restrict (Metric.ball p 2)) :=
    (Lp.memLp f).integrable_sq.mono_measure (Measure.restrict_mono hp le_rfl)
  have hu2 : Integrable (fun x => v.fst x ^ 2) (volume.restrict (Metric.ball p 2)) :=
    (Lp.memLp v.fst).integrable_sq.mono_measure (Measure.restrict_mono hp le_rfl)
  have hR1 : ∫ x in Ω, η x ^ 2 * f x ^ 2 ≤ ∫ x in Metric.ball p 2, f x ^ 2 := by
    rw [← setIntegral_eq_of_forall_notMem_eq_zero hp fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport (hout x hx)]]
    refine integral_mono (hf2.bdd_mul (hηt.continuous.pow 2).aestronglyMeasurable (c := 1)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hη2 x)) hf2 fun x => ?_
    exact mul_le_of_le_one_left (sq_nonneg _) (hη2 x)
  have hR2 : ∫ x in Ω, (η x ^ 2 + 4 * c.Λ * ‖gradient η x‖ ^ 2) * v.fst x ^ 2 ≤
      (1 + 4 * c.Λ * Γ ^ 2) * ∫ x in Metric.ball p 2, v.fst x ^ 2 := by
    have hΛ := c.Λ_pos
    rw [← setIntegral_eq_of_forall_notMem_eq_zero hp fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport (hout x hx),
        gradient_eq_zero_of_notMem_tsupport (hout x hx)], ← integral_const_mul]
    have hw : ∀ x, η x ^ 2 + 4 * c.Λ * ‖gradient η x‖ ^ 2 ≤ 1 + 4 * c.Λ * Γ ^ 2 := fun x => by
      have := pow_le_pow_left₀ (norm_nonneg _) (hgη x) 2
      nlinarith [hη2 x]
    refine integral_mono (hu2.bdd_mul (c := 1 + 4 * c.Λ * Γ ^ 2) ((hηt.continuous.pow 2).add
      (continuous_const.mul (hηt.continuous_gradient.norm.pow 2))).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hw x))
      (hu2.const_mul _) fun x => ?_
    exact mul_le_mul_of_nonneg_right (hw x) (sq_nonneg _)
  have hl := c.lam_pos
  calc c.lam * ∫ x in Metric.ball p 1, ‖v.snd x‖ ^ 2
      ≤ c.lam * ∫ x in Ω, η x ^ 2 * ‖v.snd x‖ ^ 2 := by gcongr
    _ ≤ _ := hcac
    _ ≤ _ := add_le_add hR1 hR2

theorem dilDom_ball {t : ℝ} (ht : 0 < t) (p : 𝔼) (s : ℝ) :
    dilDom t (Metric.ball p (t * s)) = Metric.ball (t⁻¹ • p) s := by
  ext x
  simp only [dilDom, Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
  have : t • x - p = t • (x - t⁻¹ • p) := by
    rw [smul_sub, smul_inv_smul₀ ht.ne']
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  exact mul_lt_mul_iff_right₀ ht

theorem setIntegral_ball_dilate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {t : ℝ}
    (ht : 0 < t) (p : 𝔼) (s : ℝ) (F : 𝔼 → E) :
    ∫ x in Metric.ball (t⁻¹ • p) s, F (t • x) = (t ^ d)⁻¹ • ∫ y in Metric.ball p (t * s), F y := by
  rw [← dilDom_ball ht p s, setIntegral_comp_smul_dilDom ht Metric.isOpen_ball.measurableSet]

/-- **The scaled Caccioppoli inequality** (paper, §2.5.1). There is `Γ` (depending only on `d`)
such that for every **dilation-invariant** coefficient field (`A(t x) = A(x)`, e.g. the cone
Laplacian, `coneCoeffA_smul`), every `ρ > 0` and every `B(p, 2ρ) ⊆ Ω`:
`λ ∫_{B(p,ρ)} |∇u|² ≤ ρ² ∫_{B(p,2ρ)} f² + (1 + 4ΛΓ²) ρ⁻² ∫_{B(p,2ρ)} u²`.
Proof: dilate by `ρ` (`IsWeakSolution.dilate`) and apply the unit-scale estimate
`exists_caccioppoli_ball` at the centre `ρ⁻¹ p`. -/
theorem exists_caccioppoli_ball_scaled : ∃ Γ : ℝ, 0 ≤ Γ ∧ ∀ (c : CoeffField 𝔼 volume)
    (_ : ∀ t : ℝ, 0 < t → ∀ x, c.A (t • x) = c.A x) {Ω : Set 𝔼} (_ : IsOpen Ω) (p : 𝔼)
    {ρ : ℝ} (_ : 0 < ρ) (_ : Metric.ball p (2 * ρ) ⊆ Ω) {f : Lp ℝ 2 (volume.restrict Ω)}
    {v : L2Pair volume Ω} (_ : c.IsWeakSolution f v),
    c.lam * ∫ x in Metric.ball p ρ, ‖v.snd x‖ ^ 2 ≤
      ρ ^ 2 * (∫ x in Metric.ball p (2 * ρ), f x ^ 2) + (1 + 4 * c.Λ * Γ ^ 2) / ρ ^ 2 *
        ∫ x in Metric.ball p (2 * ρ), v.fst x ^ 2 := by
  obtain ⟨Γ, hΓ0, hcac⟩ := exists_caccioppoli_ball (d := d)
  refine ⟨Γ, hΓ0, fun c hA Ω hΩ p ρ hρ hp f v hv => ?_⟩
  have hΩm := hΩ.measurableSet
  have hdil := hv.dilate hρ (hA ρ hρ) hΩm
  have hsub : Metric.ball (ρ⁻¹ • p) 2 ⊆ dilDom ρ Ω := by
    rw [← dilDom_ball hρ p 2, mul_comm]
    exact Set.preimage_mono hp
  have hsub1 : Metric.ball (ρ⁻¹ • p) 1 ⊆ dilDom ρ Ω :=
    (Metric.ball_subset_ball (by norm_num)).trans hsub
  have key := hcac c (isOpen_dilDom hΩ) (ρ⁻¹ • p) hsub hdil
  -- transform the three integrals back
  have T1 : ∫ x in Metric.ball (ρ⁻¹ • p) 1, ‖(dilate hρ hΩm v).snd x‖ ^ 2 =
      (ρ ^ d)⁻¹ * (ρ ^ 2 * ∫ y in Metric.ball p ρ, ‖v.snd y‖ ^ 2) := by
    calc ∫ x in Metric.ball (ρ⁻¹ • p) 1, ‖(dilate hρ hΩm v).snd x‖ ^ 2
        = ∫ x in Metric.ball (ρ⁻¹ • p) 1, (fun y => ρ ^ 2 * ‖v.snd y‖ ^ 2) (ρ • x) := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub1
            (Lp.coeFn_smul ρ (dilLp hρ hΩm v.snd)),
            ae_restrict_of_ae_restrict_of_subset hsub1 (dilLp_ae hρ hΩm v.snd)] with x h1 h2
          rw [dilate_snd, h1, Pi.smul_apply, h2, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      _ = (ρ ^ d)⁻¹ • ∫ y in Metric.ball p (ρ * 1), ρ ^ 2 * ‖v.snd y‖ ^ 2 :=
          setIntegral_ball_dilate hρ p 1 (fun y => ρ ^ 2 * ‖v.snd y‖ ^ 2)
      _ = _ := by rw [mul_one, integral_const_mul, smul_eq_mul]
  have T2 : ∫ x in Metric.ball (ρ⁻¹ • p) 2, (ρ ^ 2 • dilLp hρ hΩm f) x ^ 2 =
      (ρ ^ d)⁻¹ * (ρ ^ 4 * ∫ y in Metric.ball p (2 * ρ), f y ^ 2) := by
    calc ∫ x in Metric.ball (ρ⁻¹ • p) 2, (ρ ^ 2 • dilLp hρ hΩm f) x ^ 2
        = ∫ x in Metric.ball (ρ⁻¹ • p) 2, (fun y => ρ ^ 4 * f y ^ 2) (ρ • x) := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
            (Lp.coeFn_smul (ρ ^ 2) (dilLp hρ hΩm f)),
            ae_restrict_of_ae_restrict_of_subset hsub (dilLp_ae hρ hΩm f)] with x h1 h2
          rw [h1, Pi.smul_apply, h2, smul_eq_mul]
          ring
      _ = (ρ ^ d)⁻¹ • ∫ y in Metric.ball p (ρ * 2), ρ ^ 4 * f y ^ 2 :=
          setIntegral_ball_dilate hρ p 2 (fun y => ρ ^ 4 * f y ^ 2)
      _ = _ := by rw [mul_comm ρ 2, integral_const_mul, smul_eq_mul]
  have T3 : ∫ x in Metric.ball (ρ⁻¹ • p) 2, (dilate hρ hΩm v).fst x ^ 2 =
      (ρ ^ d)⁻¹ * ∫ y in Metric.ball p (2 * ρ), v.fst y ^ 2 := by
    calc ∫ x in Metric.ball (ρ⁻¹ • p) 2, (dilate hρ hΩm v).fst x ^ 2
        = ∫ x in Metric.ball (ρ⁻¹ • p) 2, (fun y => v.fst y ^ 2) (ρ • x) := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
            (dilLp_ae hρ hΩm v.fst)] with x h1
          rw [dilate_fst, h1]
      _ = (ρ ^ d)⁻¹ • ∫ y in Metric.ball p (ρ * 2), v.fst y ^ 2 :=
          setIntegral_ball_dilate hρ p 2 (fun y => v.fst y ^ 2)
      _ = _ := by rw [mul_comm ρ 2, smul_eq_mul]
  rw [T1, T2, T3] at key
  have hρd : 0 < (ρ ^ d)⁻¹ := by positivity
  have hpos : 0 < ρ ^ 2 * (ρ ^ d)⁻¹ := by positivity
  refine le_of_mul_le_mul_right ?_ hpos
  calc c.lam * (∫ x in Metric.ball p ρ, ‖v.snd x‖ ^ 2) * (ρ ^ 2 * (ρ ^ d)⁻¹)
      = c.lam * ((ρ ^ d)⁻¹ * (ρ ^ 2 * ∫ y in Metric.ball p ρ, ‖v.snd y‖ ^ 2)) := by ring
    _ ≤ _ := key
    _ = _ := by
        have : ρ ^ 2 ≠ 0 := by positivity
        field_simp

end ConicalKahler.Sobolev
