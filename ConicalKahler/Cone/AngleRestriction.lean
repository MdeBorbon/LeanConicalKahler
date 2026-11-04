module

public import ConicalKahler.Cone.Comparison

/-!
# Chart dependence of the cone condition: the shear test (spec §4.1)

On `ℂ²` with `D = {z_0 = 0}` consider the standard cone form
`ω_β = β² |z_0|^(2β-2) |dz_0|² + |dz_1|²` and the **shear** `S(z_0, z_1) = (z_0, z_1 + z_0)`, a
linear biholomorphism preserving `D`; it is an adapted chart (`shearChart`). In shear coordinates
`ζ = S z` the model form becomes (`metricQuadraticInAdaptedChart_shear`)

  `q_shear(ζ; v) = β² |ζ_0|^(2β-2) |v_0|² + |v_1 - v_0|²`,

while the diagonal model in the same coordinates is `β² |ζ_0|^(2β-2) |v_0|² + |v_1|²`.

* For `β > 1` the comparison **fails in every neighbourhood** of every point of `D`
  (`not_coneComparableIn_shear`): on `v = e_0` the ratio is `1 + β⁻² |ζ_0|^(2-2β) → ∞`.
* For `0 < β ≤ 1` the comparison **holds** on `{|z_0| < 1}` with `C = 2 + 2/β²`
  (`coneComparableIn_shear_of_le_one`).

So the quasi-isometric cone condition is genuinely chart dependent above angle `2π`, and
`IsConeAlong` must be read as an existence-of-compatible-chart condition for `β > 1`.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Set Filter

namespace ConicalKahler

/-! ### The shear chart -/

/-- The shear `(z_0, z_1) ↦ (z_0, z_1 + z_0)` of `ℂ²`. -/
noncomputable def shearCLM : E 2 →L[ℂ] E 2 :=
  ContinuousLinearMap.id ℂ (E 2) +
    (EuclideanSpace.proj (0 : Fin 2) : E 2 →L[ℂ] ℂ).smulRight (EuclideanSpace.single 1 1)

/-- The inverse shear `(z_0, z_1) ↦ (z_0, z_1 - z_0)`. -/
noncomputable def unshearCLM : E 2 →L[ℂ] E 2 :=
  ContinuousLinearMap.id ℂ (E 2) -
    (EuclideanSpace.proj (0 : Fin 2) : E 2 →L[ℂ] ℂ).smulRight (EuclideanSpace.single 1 1)

@[simp] theorem shearCLM_apply_zero (z : E 2) : shearCLM z 0 = z 0 := by simp [shearCLM]
@[simp] theorem shearCLM_apply_one (z : E 2) : shearCLM z 1 = z 1 + z 0 := by simp [shearCLM]
@[simp] theorem unshearCLM_apply_zero (z : E 2) : unshearCLM z 0 = z 0 := by simp [unshearCLM]
@[simp] theorem unshearCLM_apply_one (z : E 2) : unshearCLM z 1 = z 1 - z 0 := by
  simp [unshearCLM]

theorem unshearCLM_shearCLM (z : E 2) : unshearCLM (shearCLM z) = z := by
  ext i
  fin_cases i <;> simp

theorem shearCLM_unshearCLM (z : E 2) : shearCLM (unshearCLM z) = z := by
  ext i
  fin_cases i <;> simp

/-- The shear as a continuous linear equivalence. -/
noncomputable def shearEquiv : E 2 ≃L[ℂ] E 2 :=
  ContinuousLinearEquiv.equivOfInverse shearCLM unshearCLM unshearCLM_shearCLM
    shearCLM_unshearCLM

/-- The shear is an adapted chart for the coordinate hyperplane at every point. -/
noncomputable def shearChart (p : E 2) : DivisorChart 2 (E 2) (coordHyperplane 2).carrier p where
  coord := shearEquiv.toHomeomorph.toOpenPartialHomeomorph
  center_mem := mem_univ p
  holomorphic := shearCLM.contMDiff.contMDiffOn
  inverse_holomorphic := unshearCLM.contMDiff.contMDiffOn
  cutsOut x _ := by
    change x 0 = 0 ↔ shearCLM x 0 = 0
    rw [shearCLM_apply_zero]

@[simp] theorem shearChart_coord_apply (p z : E 2) : (shearChart p).coord z = shearCLM z := rfl
@[simp] theorem shearChart_coord_symm_apply (p z : E 2) :
    (shearChart p).coord.symm z = unshearCLM z := rfl

/-! ### The model in shear coordinates -/

/-- The model quadratic form on `ℂ²`. -/
theorem modelConeQuadratic_single_two (β : ConeAngle) (w u : E 2) :
    modelConeQuadratic (singleConeWeights β) w u =
      β.beta ^ 2 * ‖w 0‖ ^ (2 * β.beta - 2) * Complex.normSq (u 0) + Complex.normSq (u 1) := by
  rw [modelConeQuadratic, Fin.sum_univ_two, modelWeight_of_some (singleConeWeights_angle_zero β),
    modelWeight_of_none (singleConeWeights_angle_of_ne β (by decide : (1 : Fin 2) ≠ 0)), one_mul]

variable {β : ConeAngle} {p : E 2} {s : Set (E 2)} {hs : IsOpen s} {hps : p ∈ s}

/-- In (restricted) shear coordinates, the model form is the model quadratic form of the
un-sheared point and vector. -/
theorem metricQuadraticInAdaptedChart_shear {z : E 2}
    (hz : z ∈ ((shearChart p).restrOpen s hs hps).coord.target) (haway : z 0 ≠ 0) (v : E 2) :
    metricQuadraticInAdaptedChart (coordHyperplane 2) (modelOnHyperplane β)
        ((shearChart p).restrOpen s hs hps) z hz haway v =
      modelConeQuadratic (singleConeWeights β) (unshearCLM z) (unshearCLM v) := by
  have hz₂ : unshearCLM z ∈ (coordHyperplaneChart 2 p).coord.target := mem_univ _
  have haway₂ : unshearCLM z 0 ≠ 0 := by rwa [unshearCLM_apply_zero]
  have hsame : ((shearChart p).restrOpen s hs hps).coord.symm z =
      (coordHyperplaneChart 2 p).coord.symm (unshearCLM z) := rfl
  have hΦ : (coordHyperplaneChart 2 p).coord ∘ ((shearChart p).restrOpen s hs hps).coord.symm =
      unshearCLM := rfl
  rw [metricQuadraticInAdaptedChart_change hz haway hz₂ haway₂ hsame, hΦ,
    unshearCLM.fderiv, modelOnHyperplane, metricQuadraticInAdaptedChart_model]

/-- Explicitly: `q_shear(ζ; v) = β² |ζ_0|^(2β-2) |v_0|² + |v_1 - v_0|²`. -/
theorem metricQuadraticInAdaptedChart_shear_eq {z : E 2}
    (hz : z ∈ ((shearChart p).restrOpen s hs hps).coord.target) (haway : z 0 ≠ 0) (v : E 2) :
    metricQuadraticInAdaptedChart (coordHyperplane 2) (modelOnHyperplane β)
        ((shearChart p).restrOpen s hs hps) z hz haway v =
      β.beta ^ 2 * ‖z 0‖ ^ (2 * β.beta - 2) * Complex.normSq (v 0) +
        Complex.normSq (v 1 - v 0) := by
  rw [metricQuadraticInAdaptedChart_shear, modelConeQuadratic_single_two]
  simp

/-! ### `β > 1`: failure in every neighbourhood -/

/-- **For `β > 1` the standard cone form is not quasi-isometric to the diagonal model in the shear
chart, on any neighbourhood of any point of `D` and for any constant.** Hence the naive cone
condition is not invariant under adapted changes of chart above cone angle `2π`. -/
theorem not_coneComparableIn_shear (hβ : 1 < β.beta) (hp : p 0 = 0) (s : Set (E 2))
    (hs : IsOpen s) (hps : p ∈ s) (C : ℝ) :
    ¬ ConeComparableIn (coordHyperplane 2) β (modelOnHyperplane β)
      ((shearChart p).restrOpen s hs hps) C := by
  intro hcomp
  set e₀ : E 2 := EuclideanSpace.single 0 1
  set a : ℝ := 2 * β.beta - 2
  have ha : 0 < a := by simp only [a]; linarith
  -- small positive `t` with `p + t e₀ ∈ s` and `|C| β² t^a < 1`
  have hcont : Continuous fun t : ℝ => p + (t : ℂ) • e₀ := by fun_prop
  have h1 : ∀ᶠ t : ℝ in 𝓝 0, p + (t : ℂ) • e₀ ∈ s :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using hs.mem_nhds hps)
  have hcont2 : ContinuousAt (fun t : ℝ => |C| * β.beta ^ 2 * |t| ^ a) 0 :=
    continuousAt_const.mul ((Real.continuousAt_rpow_const _ _ (Or.inr ha.le)).comp
      continuous_abs.continuousAt)
  have h2 : ∀ᶠ t : ℝ in 𝓝 0, |C| * β.beta ^ 2 * |t| ^ a < 1 :=
    hcont2.eventually_lt continuousAt_const (by simp [Real.zero_rpow ha.ne'])
  obtain ⟨t, ht1, ht2, ht0⟩ :=
    ((h1.filter_mono nhdsWithin_le_nhds).and ((h2.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t))).exists
  -- the test point `z = S(p + t e₀)` and vector `e₀`
  set z : E 2 := shearCLM (p + (t : ℂ) • e₀)
  have hz : z ∈ ((shearChart p).restrOpen s hs hps).coord.target := by
    refine ⟨mem_univ _, ?_⟩
    change unshearCLM z ∈ s
    simpa only [z, unshearCLM_shearCLM] using ht1
  have hz0 : z 0 = t := by simp [z, e₀, hp]
  have haway : z 0 ≠ 0 := by rw [hz0]; exact Complex.ofReal_ne_zero.mpr ht0.ne'
  have hnorm : ‖z 0‖ = |t| := by rw [hz0, Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨-, hupper⟩ := hcomp z hz haway e₀
  rw [metricQuadraticInAdaptedChart_shear_eq, modelConeQuadratic_single_two, hnorm] at hupper
  simp only [e₀, PiLp.single_apply, ite_true, Complex.normSq_one, mul_one,
    show ((1 : Fin 2) = 0) = False from by decide, ite_false, zero_sub, Complex.normSq_neg,
    Complex.normSq_zero, add_zero] at hupper
  -- `β² |t|^a + 1 ≤ C β² |t|^a`, but `C β² |t|^a ≤ |C| β² |t|^a < 1`
  have hpos : 0 ≤ β.beta ^ 2 * |t| ^ a := by positivity
  have hCle : C * (β.beta ^ 2 * |t| ^ a) ≤ |C| * β.beta ^ 2 * |t| ^ a := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self C) hpos
  linarith

/-! ### `β ≤ 1`: the shear chart is admissible -/

/-- `|a - b|² ≤ 2|a|² + 2|b|²`. -/
theorem normSq_sub_le (a b : ℂ) :
    Complex.normSq (a - b) ≤ 2 * Complex.normSq a + 2 * Complex.normSq b := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith [sq_nonneg (a.re + b.re), sq_nonneg (a.im + b.im)]

/-- The unit-disc neighbourhood `{|z_0| < 1}` (in the source coordinates of the shear chart). -/
def unitSlab : Set (E 2) := {z | ‖z 0‖ < 1}

theorem isOpen_unitSlab : IsOpen unitSlab :=
  isOpen_lt (continuous_norm.comp (EuclideanSpace.proj (0 : Fin 2) : E 2 →L[ℂ] ℂ).continuous)
    continuous_const

/-- **For `0 < β ≤ 1` the shear chart is admissible:** on `{|z_0| < 1}` the standard cone form is
comparable to the diagonal model in shear coordinates with constant `2 + 2/β²`. -/
theorem coneComparableIn_shear_of_le_one (hβ : β.beta ≤ 1) (hp : p ∈ unitSlab) :
    ConeComparableIn (coordHyperplane 2) β (modelOnHyperplane β)
      ((shearChart p).restrOpen unitSlab isOpen_unitSlab hp) (2 + 2 / β.beta ^ 2) := by
  intro z hz haway v
  rw [metricQuadraticInAdaptedChart_shear_eq, modelConeQuadratic_single_two]
  have hβ0 := β.pos
  have hb2 : 0 < β.beta ^ 2 := by positivity
  -- `|z_0| < 1` and `β ≤ 1` give `W := β² |z_0|^(2β-2) ≥ β²`
  have hz1 : ‖z 0‖ < 1 := by
    have h := hz.2
    change ‖unshearCLM z 0‖ < 1 at h
    rwa [unshearCLM_apply_zero] at h
  have hr : 1 ≤ ‖z 0‖ ^ (2 * β.beta - 2) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (norm_pos_iff.mpr haway) hz1.le (by linarith)
  set W := β.beta ^ 2 * ‖z 0‖ ^ (2 * β.beta - 2) with hW
  have hWb : β.beta ^ 2 ≤ W := by
    rw [hW]
    nlinarith
  set x0 := Complex.normSq (v 0)
  set x1 := Complex.normSq (v 1)
  set d := Complex.normSq (v 1 - v 0)
  have hx0 : 0 ≤ x0 := Complex.normSq_nonneg _
  have hx1 : 0 ≤ x1 := Complex.normSq_nonneg _
  have hd : 0 ≤ d := Complex.normSq_nonneg _
  have hdle : d ≤ 2 * x1 + 2 * x0 := normSq_sub_le _ _
  have hx1le : x1 ≤ 2 * d + 2 * x0 := by
    have h := normSq_sub_le (v 1 - v 0) (-v 0)
    simp only [sub_neg_eq_add, sub_add_cancel, Complex.normSq_neg] at h
    linarith
  -- `x0 ≤ W x0 / β²`
  have hx0W : x0 ≤ W * x0 / β.beta ^ 2 := by
    rw [le_div_iff₀ hb2]
    nlinarith
  have hC : 0 < 2 + 2 / β.beta ^ 2 := by positivity
  constructor
  · -- lower bound: `W x0 + x1 ≤ C (W x0 + d)`
    rw [inv_mul_le_iff₀ hC]
    have h2W : 2 * x0 ≤ 2 / β.beta ^ 2 * (W * x0) := by
      have := hx0W
      rw [div_mul_eq_mul_div, le_div_iff₀ hb2]
      rw [le_div_iff₀ hb2] at this
      nlinarith
    nlinarith [mul_nonneg hd (by positivity : (0 : ℝ) ≤ 2 / β.beta ^ 2),
      mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ W) hx0) (by positivity : (0:ℝ) ≤ 1)]
  · -- upper bound: `W x0 + d ≤ C (W x0 + x1)`
    have h2W : 2 * x0 ≤ 2 / β.beta ^ 2 * (W * x0) := by
      have := hx0W
      rw [div_mul_eq_mul_div, le_div_iff₀ hb2]
      rw [le_div_iff₀ hb2] at this
      nlinarith
    nlinarith [mul_nonneg hx1 (by positivity : (0 : ℝ) ≤ 2 / β.beta ^ 2),
      mul_nonneg (by positivity : (0:ℝ) ≤ W) hx0]

end ConicalKahler
