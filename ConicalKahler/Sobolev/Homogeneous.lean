module

public import ConicalKahler.Sobolev.LinkSpectral

/-!
# Homogeneous harmonic functions and link eigenfunctions

Let `c` be a conical coefficient field on `ℝ^d` (`CoeffField.IsConical`). For a link pair
`(φ, Γ)` (`Link.lean`) and `δ ∈ ℝ`, the **homogeneous extension of degree `δ`**

  `P(x) = |x|^δ φ(x/|x|)`

has weak gradient `|x|^{δ-1} (δ φ(x̂) x̂ + Γ(x̂))` on `ℝ^d \ {0}`. The main result is

* `homogeneous_harmonic` (paper, p. 12, the indicial roots): if `(φ, Γ)` is a link eigenfunction
  with eigenvalue `λ = δ (δ + d - 2)`, then `P` is weakly harmonic on `ℝ^d \ {0}`:
  `∫ ⟨A ∇P, ∇ϑ⟩ = 0` for every test function `ϑ` supported away from `0`.

The proof is by polar coordinates. Against a test function `ϑ`, the weak equation reduces to the
link eigenvalue relation tested with the **radial average** `Ψ(x) = ∫ r^{δ+d-3} ϑ(r x) dr`, whose
restriction to the sphere is a link pair (`radAvg`, `contDiff_radAvg`). It also uses an
integration by parts along rays (`integral_ray_deriv`) and the **tangentiality** of link gradients,
`⟨Γ(w), w⟩ = 0` (`ae_inner_linkSnd_eq_zero`).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set Metric
open scoped ContDiff ENNReal Interval

namespace ConicalKahler.Sobolev

variable {d : ℕ} [NeZero d]

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### Radial averages of test functions -/

section RadAvg

variable {U : Set (EuclideanSpace ℝ (Fin d))} {ϑ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- **Radial average** `Ψ(x) = ∫_{r₀}^{r₁} r^k ϑ(r x) dr`. -/
def radAvg (k r₀ r₁ : ℝ) (ϑ : 𝔼 → ℝ) (x : 𝔼) : ℝ := ∫ r in r₀..r₁, r ^ k * ϑ (r • x)

/-- The derivative of the radial average: `∫_{r₀}^{r₁} r^{k+1} Dϑ(r x) dr`. -/
def radAvgD (k r₀ r₁ : ℝ) (ϑ : 𝔼 → ℝ) (x : 𝔼) : 𝔼 →L[ℝ] ℝ :=
  ∫ r in r₀..r₁, (r ^ k * r) • fderiv ℝ ϑ (r • x)

theorem exists_bound_rpow_mul {k r₀ r₁ : ℝ} (hr₀ : 0 < r₀) :
    ∃ C, ∀ r ∈ Icc r₀ r₁, |r ^ k * r| ≤ C := by
  have hcont : ContinuousOn (fun r : ℝ => r ^ k * r) (Icc r₀ r₁) := by
    refine ContinuousOn.mul (fun r hr => ?_) continuousOn_id
    exact (Real.continuousAt_rpow_const r k (Or.inl (hr₀.trans_le hr.1).ne')).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨C, fun r hr => (Real.norm_eq_abs _).symm.trans_le (hC r hr)⟩

theorem hasFDerivAt_rpow_mul_comp_smul (hϑ : IsTestFn U ϑ) (k r : ℝ) (x : 𝔼) :
    HasFDerivAt (fun x => r ^ k * ϑ (r • x)) ((r ^ k * r) • fderiv ℝ ϑ (r • x)) x := by
  have h1 : HasFDerivAt (fun x : 𝔼 => r • x) (r • ContinuousLinearMap.id ℝ 𝔼) x :=
    (hasFDerivAt_id x).const_smul r
  have h2 := ((hϑ.differentiable (r • x)).hasFDerivAt.comp x h1).const_mul (r ^ k)
  refine h2.congr_fderiv ?_
  ext v
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, map_smul]
  ring

theorem hasFDerivAt_radAvg (hϑ : IsTestFn U ϑ) (k : ℝ) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀)
    (hr : r₀ ≤ r₁) (x : 𝔼) : HasFDerivAt (radAvg k r₀ r₁ ϑ) (radAvgD k r₀ r₁ ϑ x) x := by
  obtain ⟨C, hC⟩ := exists_bound_rpow_mul (k := k) (r₁ := r₁) hr₀
  obtain ⟨M, hM⟩ := hϑ.continuous_fderiv.bounded_above_of_compact_support
    hϑ.hasCompactSupport_fderiv
  have hIoc : ∀ r ∈ Ι r₀ r₁, r ∈ Icc r₀ r₁ := fun r hr' => by
    rw [uIoc_of_le hr] at hr'
    exact ⟨hr'.1.le, hr'.2⟩
  show HasFDerivAt (fun x => ∫ r in r₀..r₁, r ^ k * ϑ (r • x))
    (∫ r in r₀..r₁, (r ^ k * r) • fderiv ℝ ϑ (r • x)) x
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (H := 𝔼)
    (E := ℝ) (μ := volume) (F := fun x r => r ^ k * ϑ (r • x))
    (F' := fun x r => (r ^ k * r) • fderiv ℝ ϑ (r • x)) (bound := fun _ => C * M)
    (s := (univ : Set 𝔼)) univ_mem ?_ ?_ ?_ ?_
    (intervalIntegrable_const (μ := (volume : Measure ℝ))) ?_
  · refine Eventually.of_forall fun x => ?_
    exact ((by fun_prop : Measurable fun r : ℝ => r ^ k).mul (hϑ.continuous.measurable.comp
      (by fun_prop : Measurable fun r : ℝ => r • x))).aestronglyMeasurable
  · refine ContinuousOn.intervalIntegrable fun r hr' => ?_
    have hr0 : r ≠ 0 := by
      rw [uIcc_of_le hr] at hr'
      exact (hr₀.trans_le hr'.1).ne'
    exact ((Real.continuousAt_rpow_const r k (Or.inl hr0)).mul
      (hϑ.continuous.continuousAt.comp (continuousAt_id.smul continuousAt_const))).continuousWithinAt
  · exact (((by fun_prop : Measurable fun r : ℝ => r ^ k).mul measurable_id).smul
      (hϑ.continuous_fderiv.measurable.comp
        (by fun_prop : Measurable fun r : ℝ => r • x))).aestronglyMeasurable
  · refine Eventually.of_forall fun r hr' y _ => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hC r (hIoc r hr')) (hM _) (norm_nonneg _)
      ((abs_nonneg _).trans (hC r (hIoc r hr')))
  · exact Eventually.of_forall fun r _ y _ => hasFDerivAt_rpow_mul_comp_smul hϑ k r y

theorem continuous_radAvgD (hϑ : IsTestFn U ϑ) (k : ℝ) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀)
    (hr : r₀ ≤ r₁) : Continuous (radAvgD k r₀ r₁ ϑ) := by
  obtain ⟨C, hC⟩ := exists_bound_rpow_mul (k := k) (r₁ := r₁) hr₀
  obtain ⟨M, hM⟩ := hϑ.continuous_fderiv.bounded_above_of_compact_support
    hϑ.hasCompactSupport_fderiv
  show Continuous fun x => ∫ r in r₀..r₁, (r ^ k * r) • fderiv ℝ ϑ (r • x)
  refine intervalIntegral.continuous_of_dominated_interval (bound := fun _ => C * M) ?_ ?_
    (intervalIntegrable_const (μ := (volume : Measure ℝ))) ?_
  · exact fun x => (((by fun_prop : Measurable fun r : ℝ => r ^ k).mul measurable_id).smul
      (hϑ.continuous_fderiv.measurable.comp
        (by fun_prop : Measurable fun r : ℝ => r • x))).aestronglyMeasurable
  · refine fun x => Eventually.of_forall fun r hr' => ?_
    have hr'' : r ∈ Icc r₀ r₁ := by
      rw [uIoc_of_le hr] at hr'
      exact ⟨hr'.1.le, hr'.2⟩
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hC r hr'') (hM _) (norm_nonneg _) ((abs_nonneg _).trans (hC r hr''))
  · exact Eventually.of_forall fun r _ => Continuous.const_smul
      (hϑ.continuous_fderiv.comp (continuous_const_smul r : Continuous fun x : 𝔼 => r • x))
      (r ^ k * r)

/-- **Radial averages of test functions are `C¹`.** -/
theorem contDiff_radAvg (hϑ : IsTestFn U ϑ) (k : ℝ) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀)
    (hr : r₀ ≤ r₁) : ContDiff ℝ 1 (radAvg k r₀ r₁ ϑ) :=
  contDiff_one_iff_hasFDerivAt.mpr ⟨_, continuous_radAvgD hϑ k hr₀ hr,
    hasFDerivAt_radAvg hϑ k hr₀ hr⟩

theorem fderiv_radAvg_apply (hϑ : IsTestFn U ϑ) (k : ℝ) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀)
    (hr : r₀ ≤ r₁) (x v : 𝔼) :
    fderiv ℝ (radAvg k r₀ r₁ ϑ) x v = ∫ r in r₀..r₁, r ^ k * r * fderiv ℝ ϑ (r • x) v := by
  rw [(hasFDerivAt_radAvg hϑ k hr₀ hr x).fderiv, radAvgD]
  rw [ContinuousLinearMap.intervalIntegral_apply]
  · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  · obtain ⟨C, hC⟩ := exists_bound_rpow_mul (k := k) (r₁ := r₁) hr₀
    refine ContinuousOn.intervalIntegrable fun r hr' => ?_
    have hr0 : r ≠ 0 := by
      rw [uIcc_of_le hr] at hr'
      exact (hr₀.trans_le hr'.1).ne'
    exact (((Real.continuousAt_rpow_const r k (Or.inl hr0)).mul continuousAt_id).smul
      (hϑ.continuous_fderiv.continuousAt.comp
        (continuousAt_id.smul continuousAt_const))).continuousWithinAt

/-- **Integration by parts along a ray.** If `ϑ(r₀ w) = ϑ(r₁ w) = 0` with `0 < r₀ ≤ r₁`, then
`∫_{r₀}^{r₁} r^m ∂_w ϑ(r w) dr = -m ∫_{r₀}^{r₁} r^{m-1} ϑ(r w) dr`. -/
theorem integral_ray_deriv (hϑ : IsTestFn U ϑ) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r₁)
    (w : 𝔼) (h₀ : ϑ (r₀ • w) = 0) (h₁ : ϑ (r₁ • w) = 0) (m : ℝ) :
    ∫ r in r₀..r₁, r ^ m * fderiv ℝ ϑ (r • w) w =
      -(m * ∫ r in r₀..r₁, r ^ (m - 1) * ϑ (r • w)) := by
  have hpos : ∀ r ∈ uIcc r₀ r₁, 0 < r := fun r hr' => by
    rw [uIcc_of_le hr] at hr'
    exact hr₀.trans_le hr'.1
  have hderiv : ∀ r ∈ uIcc r₀ r₁, HasDerivAt (fun r => r ^ m * ϑ (r • w))
      (m * r ^ (m - 1) * ϑ (r • w) + r ^ m * fderiv ℝ ϑ (r • w) w) r := by
    intro r hr'
    have h1 := Real.hasDerivAt_rpow_const (x := r) (p := m) (Or.inl (hpos r hr').ne')
    have h2 : HasDerivAt (fun r : ℝ => ϑ (r • w)) (fderiv ℝ ϑ (r • w) w) r := by
      have h := (hϑ.differentiable (r • w)).hasFDerivAt.comp_hasDerivAt r
        ((hasDerivAt_id r).smul_const w)
      simp only [id, one_smul] at h
      exact h
    exact h1.mul h2
  have hcont1 : ContinuousOn (fun r : ℝ => r ^ (m - 1) * ϑ (r • w)) (uIcc r₀ r₁) := fun r hr' =>
    ((Real.continuousAt_rpow_const r (m - 1) (Or.inl (hpos r hr').ne')).mul
      (hϑ.continuous.continuousAt.comp (continuousAt_id.smul continuousAt_const))).continuousWithinAt
  have hcont2 : ContinuousOn (fun r : ℝ => r ^ m * fderiv ℝ ϑ (r • w) w) (uIcc r₀ r₁) :=
    fun r hr' => ((Real.continuousAt_rpow_const r m (Or.inl (hpos r hr').ne')).mul
      ((hϑ.continuous_fderiv_apply w).continuousAt.comp
        (continuousAt_id.smul continuousAt_const))).continuousWithinAt
  have hint : IntervalIntegrable (fun r => m * r ^ (m - 1) * ϑ (r • w) +
      r ^ m * fderiv ℝ ϑ (r • w) w) volume r₀ r₁ :=
    ((hcont1.intervalIntegrable).const_mul m |>.congr (fun r _ => by ring)).add
      hcont2.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h₀, h₁, mul_zero, mul_zero, sub_zero, intervalIntegral.integral_add
    ((hcont1.intervalIntegrable.const_mul m).congr (fun r _ => by ring))
    hcont2.intervalIntegrable] at hFTC
  have hm : ∫ r in r₀..r₁, m * r ^ (m - 1) * ϑ (r • w) =
      m * ∫ r in r₀..r₁, r ^ (m - 1) * ϑ (r • w) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext r
    ring
  rw [hm] at hFTC
  linarith

end RadAvg

/-! ### Polar coordinates for functions supported in a shell -/

theorem exists_shell_of_isTestFn {ϑ : 𝔼 → ℝ} (hϑ : IsTestFn {0}ᶜ ϑ) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ tsupport ϑ ⊆ shell d a b := by
  have hK := hϑ.hasCompactSupport.isCompact
  have h0 : (0 : 𝔼) ∉ tsupport ϑ := fun h => hϑ.tsupport_subset h rfl
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((isClosed_tsupport ϑ).isOpen_compl.mem_nhds h0)
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨ε / 2, max R ε + 1, by positivity, by linarith [le_max_right R ε], fun x hx => ⟨?_, ?_⟩⟩
  · by_contra h
    exact hball (mem_ball_zero_iff.mpr (by linarith [not_lt.mp h])) hx
  · have := mem_closedBall_zero_iff.mp (hR hx)
    linarith [le_max_left R ε]

theorem rpow_sub_one_eq_pow {r : ℝ} (hr : 0 < r) : r ^ ((d : ℝ) - 1) = r ^ (d - 1) := by
  rw [← Real.rpow_natCast, Nat.cast_pred (Nat.pos_of_ne_zero (NeZero.ne d))]

/-- **Polar coordinates for a function supported in a shell**:
`∫_{ℝ^d} g = ∫_S ∫_a^b r^{d-1} g(r w) dr dσ(w)` if `g` vanishes outside `{a < |x| < b}`. -/
theorem integral_eq_polar_shell {g : 𝔼 → ℝ} (hg : Integrable g) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hsupp : ∀ x, x ∉ shell d a b → g x = 0) :
    ∫ x, g x = ∫ w, (∫ r in a..b, r ^ (d - 1) * g (r • (w : 𝔼))) ∂(sphMeasure d) := by
  rw [integral_polar_iter hg]
  congr 1
  funext w
  rw [intervalIntegral.integral_of_le hab]
  have hzero : ∀ r ∈ Ioi (0 : ℝ) \ Ioc a b, r ^ (d - 1) • g (r • (w : 𝔼)) = 0 := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr.1
    have hnorm : ‖r • (w : 𝔼)‖ = r := by
      rw [norm_smul, norm_eq_of_mem_sphere w, mul_one, Real.norm_eq_abs, abs_of_pos hr0]
    have hnot : r • (w : 𝔼) ∉ shell d a b := by
      intro h
      apply hr.2
      exact ⟨by rw [← hnorm]; exact h.1, by rw [← hnorm]; exact h.2.le⟩
    rw [smul_eq_mul, hsupp _ hnot, mul_zero]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun r hr => ha.trans hr.1) hzero]
  rfl

/-! ### Link pairs tested on `ℝ^d \ {0}` -/

/-- **The weak gradient identity of a link pair on `ℝ^d \ {0}`**: for a test function `ϑ`
supported away from `0`, `∫ φ(x̂) ∂_e ϑ = -∫ ϑ ⟨|x|^{-1} Γ(x̂), e⟩`. -/
theorem linkPair_integral {v : LinkPair d} (hv : v ∈ linkW12 d) {ϑ : 𝔼 → ℝ}
    (hϑ : IsTestFn {0}ᶜ ϑ) (e : 𝔼) :
    ∫ x, homFun 0 v.fst x * fderiv ℝ ϑ x e = -∫ x, ϑ x * ⟪homFun (-1) v.snd x, e⟫_ℝ := by
  obtain ⟨a, b, ha, -, hsupp⟩ := exists_shell_of_isTestFn hϑ
  have hϑΩ : IsTestFn (shell d a b) ϑ := ⟨hϑ.contDiff, hϑ.hasCompactSupport, hsupp⟩
  have hv' := linkEmb_mem_W12 hv ha (subset_refl (shell d a b))
  have h := integral_fst_mul_fderiv hv' hϑΩ e
  have hout : ∀ x ∉ shell d a b, x ∉ tsupport ϑ := fun x hx h => hx (hsupp h)
  have z1 : ∀ x ∉ shell d a b, homFun 0 v.fst x * fderiv ℝ ϑ x e = 0 := fun x hx => by
    rw [fderiv_eq_zero_of_notMem_tsupport (hout x hx), ContinuousLinearMap.zero_apply, mul_zero]
  have z2 : ∀ x ∉ shell d a b, ϑ x * ⟪homFun (-1) v.snd x, e⟫_ℝ = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (hout x hx), zero_mul]
  have e1 : ∫ x in shell d a b, (linkEmb ha (subset_refl (shell d a b)) v).fst x *
      fderiv ℝ ϑ x e = ∫ x, homFun 0 v.fst x * fderiv ℝ ϑ x e := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero z1]
    refine integral_congr_ae ?_
    filter_upwards [linkEmb_fst_ae ha (subset_refl (shell d a b)) v] with x hx
    rw [hx]
  have e2 : ∫ x in shell d a b, ϑ x * ⟪(linkEmb ha (subset_refl (shell d a b)) v).snd x, e⟫_ℝ =
      ∫ x, ϑ x * ⟪homFun (-1) v.snd x, e⟫_ℝ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero z2]
    refine integral_congr_ae ?_
    filter_upwards [linkEmb_snd_ae ha (subset_refl (shell d a b)) v] with x hx
    rw [hx]
  rw [← e1, ← e2]
  exact h

theorem homFun_smul_sph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℝ)
    (Ψ : Sph d → E) {r : ℝ} (hr : 0 < r) (w : Sph d) :
    homFun k Ψ (r • (w : 𝔼)) = r ^ k • Ψ w :=
  homFun_polarMap k Ψ (w, ⟨r, hr⟩)

theorem isFiniteMeasure_shell (a b : ℝ) : IsFiniteMeasure (volume.restrict (shell d a b)) :=
  isFiniteMeasure_restrict.mpr (isBounded_shell a b).measure_lt_top.ne

/-- A homogeneous extension times a bounded function supported in a shell is integrable. -/
theorem integrable_homFun_mul (k : ℝ) {Ψ : Sph d → ℝ} (hΨ : MemLp Ψ 2 (sphMeasure d))
    {g : 𝔼 → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) {a b : ℝ} (ha : 0 < a)
    (hsupp : ∀ x ∉ shell d a b, g x = 0) : Integrable (fun x => homFun k Ψ x * g x) := by
  have := isFiniteMeasure_shell (d := d) a b
  have h2 := memLp_homFun k hΨ ha.le (subset_refl (shell d a b)) (shellWeight_ne_top ha b k)
  have h1 : IntegrableOn (homFun k Ψ) (shell d a b) := h2.integrable one_le_two
  have hon : IntegrableOn (fun x => homFun k Ψ x * g x) (shell d a b) :=
    h1.mul_bdd hg.aestronglyMeasurable.restrict
      (c := C) (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  refine hon.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  rw [hsupp x hx, mul_zero]

theorem ae_ne_zero : ∀ᵐ x : 𝔼, x ≠ 0 := by
  rw [ae_iff]
  simp

/-- The function `w ↦ ⟨Γ(w), w⟩` of a link vector field. -/
def radComp (Γ : Sph d → 𝔼) (w : Sph d) : ℝ := ⟪Γ w, (w : 𝔼)⟫_ℝ

theorem memLp_radComp {Γ : Sph d → 𝔼} (hΓ : MemLp Γ 2 (sphMeasure d)) :
    MemLp (radComp Γ) 2 (sphMeasure d) := by
  refine hΓ.of_le (hΓ.aestronglyMeasurable.inner
    (continuous_subtype_val.aestronglyMeasurable)) (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, radComp]
  exact (abs_real_inner_le_norm _ _).trans (by rw [norm_eq_of_mem_sphere w, mul_one])

theorem inner_homFun_neg_one_self {Γ : Sph d → 𝔼} {x : 𝔼} (hx : x ≠ 0) :
    ⟪homFun (-1) Γ x, x⟫_ℝ = homFun 0 (radComp Γ) x := by
  rw [homFun, homFun, Real.rpow_zero, one_smul, Real.rpow_neg_one, radComp,
    real_inner_smul_left, sphProj_coe hx, inner_smul_right]

/-- **Tangentiality of link gradients**: `⟨Γ(w), w⟩ = 0` for `σ`-almost every `w`. -/
theorem inner_eq_sum_coord (G x : 𝔼) : ⟪G, x⟫_ℝ = ∑ k, G k * x k := by
  simp [PiLp.inner_apply, mul_comm]

theorem fderiv_eq_sum_coord {ϑ : 𝔼 → ℝ} (x v : 𝔼) :
    fderiv ℝ ϑ x v = ∑ k, v k * fderiv ℝ ϑ x (EuclideanSpace.single k 1) := by
  rw [← inner_gradient, inner_eq_sum_coord]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [gradient_apply_single, mul_comm]

/-- `∑_k ∂_k (x_k ϑ) = d ϑ + ∂_x ϑ`. -/
theorem sum_fderiv_coord_mul {U : Set 𝔼} {ϑ : 𝔼 → ℝ} (hϑ : IsTestFn U ϑ) (x : 𝔼) :
    ∑ k, fderiv ℝ (fun y : 𝔼 => y k * ϑ y) x (EuclideanSpace.single k 1) =
      d * ϑ x + fderiv ℝ ϑ x x := by
  have hk : ∀ k : Fin d, fderiv ℝ (fun y : 𝔼 => y k * ϑ y) x (EuclideanSpace.single k 1) =
      ϑ x + x k * fderiv ℝ ϑ x (EuclideanSpace.single k 1) := by
    intro k
    have hp : HasFDerivAt (fun y : 𝔼 => y k) (EuclideanSpace.proj k : 𝔼 →L[ℝ] ℝ) x :=
      (EuclideanSpace.proj k : 𝔼 →L[ℝ] ℝ).hasFDerivAt
    rw [show (fun y : 𝔼 => y k * ϑ y) = (fun y : 𝔼 => y k) * ϑ from rfl,
      (hp.mul (hϑ.differentiable x).hasFDerivAt).fderiv]
    simp
    ring
  simp_rw [hk]
  rw [Finset.sum_add_distrib, fderiv_eq_sum_coord x x]
  simp

/-- **Tangentiality of link gradients**: `⟨Γ(w), w⟩ = 0` for `σ`-almost every `w`. Testing the
weak gradient identity with `x_k ϑ` and summing gives `∫ φ(x̂) (d ϑ + ∂_x ϑ) = -∫ ϑ ⟨Γ̃, x⟩`, and
the left side vanishes in polar coordinates (`∂_r (r^d ϑ(r w))` integrates to `0`). -/
theorem ae_inner_linkSnd_eq_zero {v : LinkPair d} (hv : v ∈ linkW12 d) :
    ∀ᵐ w ∂(sphMeasure d), ⟪v.snd w, (w : 𝔼)⟫_ℝ = 0 := by
  set τ := radComp (fun w => v.snd w)
  have hτ : MemLp τ 2 (sphMeasure d) := memLp_radComp (Lp.memLp v.snd)
  -- Step 1: `∫ ϑ ⟨Γ̃, x⟩ = 0` for every test function supported away from `0`
  have key : ∀ ϑ : 𝔼 → ℝ, IsTestFn {0}ᶜ ϑ → ∫ x, ϑ x • homFun 0 τ x = 0 := by
    intro ϑ hϑ
    obtain ⟨a, b, ha, hab, hsupp⟩ := exists_shell_of_isTestFn hϑ
    have hout : ∀ x ∉ shell d a b, x ∉ tsupport ϑ := fun x hx h => hx (hsupp h)
    have hk : ∀ k : Fin d, IsTestFn {0}ᶜ (fun x : 𝔼 => x k * ϑ x) := fun k =>
      hϑ.smooth_mul (η := fun x : 𝔼 => x k) (by fun_prop)
    obtain ⟨M, hM0, hMϑ, hMg⟩ := exists_bound_testFn hϑ
    -- integrability of the terms
    have hint_lhs : ∀ k : Fin d, Integrable fun x => homFun 0 v.fst x *
        fderiv ℝ (fun y : 𝔼 => y k * ϑ y) x (EuclideanSpace.single k 1) := by
      intro k
      obtain ⟨Mk, -, -, hMk⟩ := exists_bound_testFn (hk k)
      refine integrable_homFun_mul 0 (Lp.memLp v.fst)
        ((hk k).continuous_fderiv_apply _).measurable (C := Mk) (a := a) (b := b) (fun x => ?_) ha
        fun x hx => ?_
      · rw [← Real.norm_eq_abs, ← inner_gradient]
        calc ‖⟪gradient (fun y : 𝔼 => y k * ϑ y) x, EuclideanSpace.single k (1 : ℝ)⟫_ℝ‖
            ≤ ‖gradient (fun y : 𝔼 => y k * ϑ y) x‖ * ‖(EuclideanSpace.single k (1 : ℝ) : 𝔼)‖ :=
              norm_inner_le_norm _ _
          _ ≤ Mk := by simpa using hMk x
      · rw [fderiv_eq_zero_of_notMem_tsupport fun h => hout x hx
          (tsupport_mul_subset_right h), ContinuousLinearMap.zero_apply]
    have hinner : ∀ (e : 𝔼) x, ⟪homFun (-1) (fun w => v.snd w) x, e⟫_ℝ =
        homFun (-1) (fun w => ⟪v.snd w, e⟫_ℝ) x := fun e x => by
      simp [homFun, real_inner_smul_left]
    have hmemLp_e : ∀ e : 𝔼, MemLp (fun w => ⟪v.snd w, e⟫_ℝ) 2 (sphMeasure d) := fun e =>
      (Lp.memLp v.snd).of_le_mul (c := ‖e‖)
        ((Lp.aestronglyMeasurable v.snd).inner aestronglyMeasurable_const)
        (Eventually.of_forall fun w => by
          rw [Real.norm_eq_abs, mul_comm]
          exact abs_real_inner_le_norm _ _)
    have hint_rhs : ∀ k : Fin d, Integrable fun x => (x k * ϑ x) *
        ⟪homFun (-1) (fun w => v.snd w) x, EuclideanSpace.single k 1⟫_ℝ := by
      intro k
      obtain ⟨Mk, -, hMk, -⟩ := exists_bound_testFn (hk k)
      have := integrable_homFun_mul (-1) (hmemLp_e (EuclideanSpace.single k 1))
        (hk k).continuous.measurable (C := Mk) (a := a) (b := b) hMk ha fun x hx => by
          rw [image_eq_zero_of_notMem_tsupport (hout x hx), mul_zero]
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only
      rw [hinner, mul_comm]
    -- the weak gradient identity, summed over the coordinates
    have hsum : ∫ x, homFun 0 v.fst x * (d * ϑ x + fderiv ℝ ϑ x x) =
        -∫ x, ϑ x * ⟪homFun (-1) (fun w => v.snd w) x, x⟫_ℝ := by
      calc ∫ x, homFun 0 v.fst x * (d * ϑ x + fderiv ℝ ϑ x x)
          = ∫ x, ∑ k, homFun 0 v.fst x *
              fderiv ℝ (fun y : 𝔼 => y k * ϑ y) x (EuclideanSpace.single k 1) := by
            congr 1
            funext x
            rw [← Finset.mul_sum, sum_fderiv_coord_mul hϑ x]
        _ = ∑ k, ∫ x, homFun 0 v.fst x *
              fderiv ℝ (fun y : 𝔼 => y k * ϑ y) x (EuclideanSpace.single k 1) :=
            integral_finsetSum _ fun k _ => hint_lhs k
        _ = ∑ k, -∫ x, (x k * ϑ x) *
              ⟪homFun (-1) (fun w => v.snd w) x, EuclideanSpace.single k 1⟫_ℝ :=
            Finset.sum_congr rfl fun k _ => linkPair_integral hv (hk k) _
        _ = -∫ x, ∑ k, (x k * ϑ x) *
              ⟪homFun (-1) (fun w => v.snd w) x, EuclideanSpace.single k 1⟫_ℝ := by
            rw [Finset.sum_neg_distrib, integral_finsetSum _ fun k _ => hint_rhs k]
        _ = -∫ x, ϑ x * ⟪homFun (-1) (fun w => v.snd w) x, x⟫_ℝ := by
            congr 2
            funext x
            rw [inner_eq_sum_coord, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← snd_apply_eq_inner]
            ring
    -- the left side vanishes in polar coordinates
    have hzero : ∫ x, homFun 0 v.fst x * (d * ϑ x + fderiv ℝ ϑ x x) = 0 := by
      have hgc : Continuous fun x => (d : ℝ) * ϑ x + fderiv ℝ ϑ x x :=
        (continuous_const.mul hϑ.continuous).add
          (hϑ.continuous_fderiv.clm_apply continuous_id)
      have hg0 : ∀ x ∉ shell d a b, (d : ℝ) * ϑ x + fderiv ℝ ϑ x x = 0 := fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (hout x hx),
          fderiv_eq_zero_of_notMem_tsupport (hout x hx)]
        simp
      have hgcs : HasCompactSupport fun x => (d : ℝ) * ϑ x + fderiv ℝ ϑ x x :=
        HasCompactSupport.intro hϑ.hasCompactSupport.isCompact fun x hx =>
          by rw [image_eq_zero_of_notMem_tsupport hx, fderiv_eq_zero_of_notMem_tsupport hx]; simp
      obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support hgcs
      have hsupp' : ∀ x ∉ shell d a b,
          homFun 0 (fun w => v.fst w) x * ((d : ℝ) * ϑ x + fderiv ℝ ϑ x x) = 0 :=
        fun x hx => by rw [hg0 x hx, mul_zero]
      rw [integral_eq_polar_shell (integrable_homFun_mul 0 (Lp.memLp v.fst) hgc.measurable
          (C := C) (fun x => (Real.norm_eq_abs _).symm.trans_le (hC x)) ha hg0) ha hab.le
          hsupp']
      refine (integral_congr_ae (Eventually.of_forall fun w => ?_)).trans (integral_zero _ _)
      have hw0 : ∀ r : ℝ, 0 < r → r ∉ Ioo a b → ϑ (r • (w : 𝔼)) = 0 := fun r hr0 hr => by
        refine image_eq_zero_of_notMem_tsupport fun h => hr ?_
        have h' := hsupp h
        have hn : ‖r • (w : 𝔼)‖ = r := by
          rw [norm_smul, norm_eq_of_mem_sphere w, mul_one, Real.norm_eq_abs, abs_of_pos hr0]
        exact ⟨hn ▸ h'.1, hn ▸ h'.2⟩
      have hray := integral_ray_deriv hϑ ha hab.le (w : 𝔼)
        (hw0 a ha fun h => lt_irrefl a h.1) (hw0 b (ha.trans hab) fun h => lt_irrefl b h.2)
        (d : ℝ)
      have hcongr : ∀ r ∈ uIcc a b, r ^ (d - 1) * (homFun 0 (fun w => v.fst w) (r • (w : 𝔼)) *
          ((d : ℝ) * ϑ (r • (w : 𝔼)) + fderiv ℝ ϑ (r • (w : 𝔼)) (r • (w : 𝔼)))) =
          v.fst w * ((d : ℝ) * (r ^ ((d : ℝ) - 1) * ϑ (r • (w : 𝔼))) +
            r ^ (d : ℝ) * fderiv ℝ ϑ (r • (w : 𝔼)) (w : 𝔼)) := by
        intro r hr
        rw [uIcc_of_le hab.le] at hr
        have hr0 : 0 < r := ha.trans_le hr.1
        rw [homFun_smul_sph 0 _ hr0, Real.rpow_zero, one_smul, map_smul, smul_eq_mul,
          ← rpow_sub_one_eq_pow hr0]
        have : r ^ (d : ℝ) = r ^ ((d : ℝ) - 1) * r := by
          rw [← Real.rpow_add_one hr0.ne', sub_add_cancel]
        rw [this]
        ring
      rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul]
      have hI1 : IntervalIntegrable (fun r => (d : ℝ) * (r ^ ((d : ℝ) - 1) * ϑ (r • (w : 𝔼))))
          volume a b := by
        refine (ContinuousOn.intervalIntegrable fun r hr => ?_).const_mul _
        rw [uIcc_of_le hab.le] at hr
        exact ((Real.continuousAt_rpow_const r _ (Or.inl (ha.trans_le hr.1).ne')).mul
          (hϑ.continuous.continuousAt.comp
            (continuousAt_id.smul continuousAt_const))).continuousWithinAt
      have hI2 : IntervalIntegrable (fun r => r ^ (d : ℝ) * fderiv ℝ ϑ (r • (w : 𝔼)) (w : 𝔼))
          volume a b := by
        refine ContinuousOn.intervalIntegrable fun r hr => ?_
        rw [uIcc_of_le hab.le] at hr
        exact ((Real.continuousAt_rpow_const r _ (Or.inl (ha.trans_le hr.1).ne')).mul
          ((hϑ.continuous_fderiv_apply _).continuousAt.comp
            (continuousAt_id.smul continuousAt_const))).continuousWithinAt
      rw [intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul, hray]
      ring
    have hfin : ∫ x, ϑ x * ⟪homFun (-1) (fun w => v.snd w) x, x⟫_ℝ = 0 := by
      linarith
    refine (integral_congr_ae ?_).trans hfin
    filter_upwards [ae_ne_zero] with x hx
    rw [smul_eq_mul, inner_homFun_neg_one_self hx]
  -- Step 2: the fundamental lemma on `ℝ^d \ {0}`
  have hloc : LocallyIntegrableOn (homFun 0 τ) {0}ᶜ volume := by
    intro x hx
    have hx0 : x ≠ 0 := hx
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    refine ⟨shell d (‖x‖ / 2) (2 * ‖x‖), mem_nhdsWithin_of_mem_nhds
      ((isOpen_shell _ _).mem_nhds ⟨by linarith, by linarith⟩), ?_⟩
    have := isFiniteMeasure_shell (d := d) (‖x‖ / 2) (2 * ‖x‖)
    exact (memLp_homFun (Ω := shell d (‖x‖ / 2) (2 * ‖x‖)) 0 hτ (by positivity) (subset_refl _)
      (shellWeight_ne_top (by positivity) _ 0)).integrable one_le_two
  have hae := (isOpen_compl_singleton (x := (0 : 𝔼))).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    hloc fun g hg hgc hgs => key g ⟨hg, hgc, hgs⟩
  -- Step 3: back to the sphere
  refine ae_sphere_of_ae (P := fun w => ⟪v.snd w, (w : 𝔼)⟫_ℝ = 0) ?_
  filter_upwards [hae, ae_ne_zero] with x h hx0
  have := h hx0
  rwa [homFun, Real.rpow_zero, one_smul] at this

end ConicalKahler.Sobolev
