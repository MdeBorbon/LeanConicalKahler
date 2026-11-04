module

public import ConicalKahler.Divisors.AdaptedChart
public import ConicalKahler.Cone.Model

/-!
# The metric of a Kähler form on `X \ D` in an arbitrary adapted chart

`KahlerForm.metricInChart` computes `g_{jk̄}` in the chart *selected* by `ChartedSpace`. An
adapted chart `χ : DivisorChart n X D p` is in general a different chart, so we pull the form back
explicitly. For `z ∈ χ.coord.target` with `z_0 ≠ 0` let `y = χ⁻¹(z) ∈ X \ D`. The value `ω y` is a
`2`-form on `ℂⁿ` expressed in the selected chart at `y`; the transition from `χ`-coordinates to
that chart is `τ = extChartAt y ∘ χ⁻¹` (`DivisorChart.toChartAt`), so the form in `χ`-coordinates
is

  `formInAdaptedChart D ω₀ χ z = (ω y) ∘ Dτ(z)`.

## Main declarations

* `formInAdaptedChart`, `metricInAdaptedChart` (its coefficient matrix `g^χ_{jk̄}(z)`), and
  `metricQuadraticInAdaptedChart` `= g^χ(v, v) / 2 = ∑ g^χ_{jk̄} v_j v̄_k`.
* `formInAdaptedChart_isPositive`, `metricInAdaptedChart_posDef`,
  `metricQuadraticInAdaptedChart_pos`: positivity.
* `formInAdaptedChart_change`, `metricQuadraticInAdaptedChart_change`,
  `metricInAdaptedChart_change`: the change-of-adapted-chart law `q₁(z₁; v) = q₂(z₂; DΦ(z₁) v)` with
  `Φ = χ₂ ∘ χ₁⁻¹` holomorphic. In matrix form `g₁ = Aᵀ g₂ Ā`, `A = DΦ(z₁)`, which is the upstream
  index convention (`IsOneOne.coeffMatrix_compContinuousLinearMap`).
* `metricQuadraticInAdaptedChart_model`: for the coordinate hyperplane in `ℂⁿ`, the identity chart
  and the model form, the adapted-chart quadratic form is `modelConeQuadratic`.

The agreement with `KahlerForm.metricInChart` when `χ` is the selected chart is recorded in
`STATUS.md` as an outstanding (non-blocking) obligation.
-/

@[expose] public section

open scoped Manifold ContDiff Topology ComplexOrder
open Set Filter ContinuousAlternatingMap

namespace ConicalKahler

variable {n : ℕ}

/-! ### Pullback of `(1,1)`-forms by injective complex-linear maps -/

/-- Pulling back a positive `(1,1)`-form by an injective `ℂ`-linear map gives a positive form. -/
theorem isPositive_compContinuousLinearMap_of_injective {α : E n [⋀^Fin 2]→L[ℝ] ℝ}
    (hα : α.IsPositive) (A : E n →L[ℂ] E n) (hA : Function.Injective A) :
    (α.compContinuousLinearMap (A.restrictScalars ℝ)).IsPositive := by
  refine ⟨hα.1.compContinuousLinearMap A, fun v hv => ?_⟩
  have hvA : A v ≠ 0 := fun h => hv (hA (h.trans A.map_zero.symm))
  have hEval : (A.restrictScalars ℝ) ∘ ![v, Complex.I • v] = ![A v, Complex.I • A v] := by
    funext i
    fin_cases i <;> simp [map_smul]
  change 0 < α ((A.restrictScalars ℝ) ∘ ![v, Complex.I • v])
  rw [hEval]
  exact hα.2 _ hvA

theorem compContinuousLinearMap_comp' {α : E n [⋀^Fin 2]→L[ℝ] ℝ} (f g : E n →L[ℝ] E n) :
    α.compContinuousLinearMap (f.comp g) =
      (α.compContinuousLinearMap f).compContinuousLinearMap g := by
  ext v
  rfl

/-- `α ∘ A` evaluated on `(v, Jv)` for a `ℂ`-linear `A`. -/
theorem compContinuousLinearMap_apply_I_smul (α : E n [⋀^Fin 2]→L[ℝ] ℝ) (A : E n →L[ℂ] E n)
    (v : E n) :
    α.compContinuousLinearMap (A.restrictScalars ℝ) ![v, Complex.I • v] =
      α ![A v, Complex.I • A v] := by
  rw [compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> simp [map_smul]

/-! ### Transition maps between an adapted chart and the selected charts -/

variable [NeZero n] {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X]
  [IsManifold 𝓘(ℂ, E n) ω X]

namespace DivisorChart

variable {D : Set X} {p : X}

/-- The transition `extChartAt y ∘ χ⁻¹` from adapted coordinates to the selected chart at `y`. -/
noncomputable def toChartAt (χ : DivisorChart n X D p) (y : X) : E n → E n :=
  extChartAt 𝓘(ℂ, E n) y ∘ χ.coord.symm

/-- The transition `χ ∘ (extChartAt y)⁻¹` from the selected chart at `y` to adapted coordinates. -/
noncomputable def fromChartAt (χ : DivisorChart n X D p) (y : X) : E n → E n :=
  χ.coord ∘ (extChartAt 𝓘(ℂ, E n) y).symm

omit [IsManifold 𝓘(ℂ, E n) ω X] in
theorem contDiffAt_toChartAt (χ : DivisorChart n X D p) {z : E n} (hz : z ∈ χ.coord.target) :
    ContDiffAt ℂ ∞ (χ.toChartAt (χ.coord.symm z)) z := by
  have h1 : ContMDiffAt 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ χ.coord.symm z :=
    χ.inverse_holomorphic.contMDiffAt (χ.coord.open_target.mem_nhds hz)
  have h2 : ContMDiffAt 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ (extChartAt 𝓘(ℂ, E n) (χ.coord.symm z))
      (χ.coord.symm z) :=
    contMDiffAt_extChartAt
  exact contMDiffAt_iff_contDiffAt.mp (h2.comp z h1)

theorem contDiffAt_fromChartAt (χ : DivisorChart n X D p) {y : X} (hy : y ∈ χ.coord.source) :
    ContDiffAt ℂ ∞ (χ.fromChartAt y) (extChartAt 𝓘(ℂ, E n) y y) := by
  have h1 : ContMDiffAt 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ (extChartAt 𝓘(ℂ, E n) y).symm
      (extChartAt 𝓘(ℂ, E n) y y) :=
    (contMDiffOn_extChartAt_symm y).contMDiffAt
      ((isOpen_extChartAt_target y).mem_nhds (mem_extChartAt_target y))
  have h2 : ContMDiffAt 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ χ.coord y :=
    χ.holomorphic.contMDiffAt (χ.coord.open_source.mem_nhds hy)
  exact contMDiffAt_iff_contDiffAt.mp
    (h2.comp_of_eq h1 ((extChartAt 𝓘(ℂ, E n) y).left_inv (mem_extChartAt_source y)))

omit [IsManifold 𝓘(ℂ, E n) ω X] in
theorem fromChartAt_comp_toChartAt (χ : DivisorChart n X D p) {z : E n}
    (hz : z ∈ χ.coord.target) :
    χ.fromChartAt (χ.coord.symm z) ∘ χ.toChartAt (χ.coord.symm z) =ᶠ[𝓝 z] id := by
  have hsrc : ∀ᶠ w in 𝓝 z,
      χ.coord.symm w ∈ (extChartAt 𝓘(ℂ, E n) (χ.coord.symm z)).source :=
    (χ.coord.continuousAt_symm hz).preimage_mem_nhds
      ((isOpen_extChartAt_source (χ.coord.symm z)).mem_nhds (mem_extChartAt_source _))
  filter_upwards [hsrc, χ.coord.open_target.mem_nhds hz] with w hw hwt
  simp only [Function.comp_apply, fromChartAt, toChartAt, id]
  rw [(extChartAt 𝓘(ℂ, E n) _).left_inv hw, χ.coord.right_inv hwt]

/-- The derivative of the transition to the selected chart has a left inverse. -/
theorem fderiv_fromChartAt_comp_fderiv_toChartAt (χ : DivisorChart n X D p) {z : E n}
    (hz : z ∈ χ.coord.target) :
    (fderiv ℂ (χ.fromChartAt (χ.coord.symm z))
        (χ.toChartAt (χ.coord.symm z) z)).comp (fderiv ℂ (χ.toChartAt (χ.coord.symm z)) z) =
      ContinuousLinearMap.id ℂ (E n) := by
  have hτ : DifferentiableAt ℂ (χ.toChartAt (χ.coord.symm z)) z :=
    (χ.contDiffAt_toChartAt hz).differentiableAt (by simp)
  have hσ : DifferentiableAt ℂ (χ.fromChartAt (χ.coord.symm z))
      (χ.toChartAt (χ.coord.symm z) z) :=
    (χ.contDiffAt_fromChartAt (χ.coord.map_target hz)).differentiableAt (by simp)
  rw [← fderiv_comp z hσ hτ, (χ.fromChartAt_comp_toChartAt hz).fderiv_eq, fderiv_id]

theorem injective_fderiv_toChartAt (χ : DivisorChart n X D p) {z : E n}
    (hz : z ∈ χ.coord.target) :
    Function.Injective (fderiv ℂ (χ.toChartAt (χ.coord.symm z)) z) := by
  intro a b hab
  have h := congrArg (fderiv ℂ (χ.fromChartAt (χ.coord.symm z))
    (χ.toChartAt (χ.coord.symm z) z)) hab
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
    χ.fderiv_fromChartAt_comp_fderiv_toChartAt hz] at h
  simpa using h

omit [IsManifold 𝓘(ℂ, E n) ω X] in
theorem fderiv_real_toChartAt (χ : DivisorChart n X D p) {z : E n} (hz : z ∈ χ.coord.target) :
    fderiv ℝ (χ.toChartAt (χ.coord.symm z)) z =
      (fderiv ℂ (χ.toChartAt (χ.coord.symm z)) z).restrictScalars ℝ :=
  ((χ.contDiffAt_toChartAt hz).differentiableAt (by simp)).fderiv_restrictScalars ℝ

end DivisorChart

/-! ### Transition between two adapted charts -/

omit [IsManifold 𝓘(ℂ, E n) ω X] in
/-- Two adapted charts are related by a holomorphic transition `χ₂ ∘ χ₁⁻¹` near any common point. -/
theorem contDiffAt_adaptedTransition {D : Set X} {p₁ p₂ : X} (χ₁ : DivisorChart n X D p₁)
    (χ₂ : DivisorChart n X D p₂) {z₁ : E n} (hz₁ : z₁ ∈ χ₁.coord.target)
    (h₂ : χ₁.coord.symm z₁ ∈ χ₂.coord.source) :
    ContDiffAt ℂ ∞ (χ₂.coord ∘ χ₁.coord.symm) z₁ := by
  have h1 : ContMDiffAt 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ χ₁.coord.symm z₁ :=
    χ₁.inverse_holomorphic.contMDiffAt (χ₁.coord.open_target.mem_nhds hz₁)
  have h2 : ContMDiffAt 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ χ₂.coord (χ₁.coord.symm z₁) :=
    χ₂.holomorphic.contMDiffAt (χ₂.coord.open_source.mem_nhds h₂)
  exact contMDiffAt_iff_contDiffAt.mp (h2.comp z₁ h1)

/-! ### The form and metric in an adapted chart -/

section AdaptedMetric

variable (D : SmoothDivisor n X) (ω₀ : KahlerForm n D.complement) {p : X}
  (χ : DivisorChart n X D.carrier p)

/-- The Kähler form `ω` on `X \ D` written in the adapted coordinates of `χ`, at a coordinate
point `z` off `{z_0 = 0}`: `(ω y) ∘ Dτ(z)` with `y = χ⁻¹(z)` and `τ = extChartAt y ∘ χ⁻¹`. -/
noncomputable def formInAdaptedChart (z : E n) (hz : z ∈ χ.coord.target) (haway : z 0 ≠ 0) :
    E n [⋀^Fin 2]→L[ℝ] ℝ :=
  (ω₀ (χ.symmComplement hz haway)).compContinuousLinearMap
    (fderiv ℝ (χ.toChartAt (χ.coord.symm z)) z)

/-- The Hermitian coefficient matrix `g^χ_{jk̄}(z)` of `ω` in the adapted chart `χ`. -/
noncomputable def metricInAdaptedChart (z : E n) (hz : z ∈ χ.coord.target) (haway : z 0 ≠ 0) :
    Matrix (Fin n) (Fin n) ℂ :=
  (formInAdaptedChart D ω₀ χ z hz haway).coeffMatrix

/-- The Hermitian quadratic form `g^χ(v, v) / 2 = ω(v, Jv) / 2 = ∑ g^χ_{jk̄} v_j v̄_k` of `ω` in
the adapted chart `χ` (half the Riemannian length squared, as for `modelConeQuadratic`). -/
noncomputable def metricQuadraticInAdaptedChart (z : E n) (hz : z ∈ χ.coord.target)
    (haway : z 0 ≠ 0) (v : E n) : ℝ :=
  formInAdaptedChart D ω₀ χ z hz haway ![v, Complex.I • v] / 2

variable {D ω₀ χ} {z : E n} (hz : z ∈ χ.coord.target) (haway : z 0 ≠ 0)
include hz

theorem formInAdaptedChart_eq :
    formInAdaptedChart D ω₀ χ z hz haway =
      (ω₀ (χ.symmComplement hz haway)).compContinuousLinearMap
        ((fderiv ℂ (χ.toChartAt (χ.coord.symm z)) z).restrictScalars ℝ) := by
  rw [formInAdaptedChart, χ.fderiv_real_toChartAt hz]

theorem formInAdaptedChart_isPositive : (formInAdaptedChart D ω₀ χ z hz haway).IsPositive := by
  rw [formInAdaptedChart_eq hz]
  exact isPositive_compContinuousLinearMap_of_injective (ω₀.isPositive _) _
    (χ.injective_fderiv_toChartAt hz)

theorem formInAdaptedChart_isOneOne : (formInAdaptedChart D ω₀ χ z hz haway).IsOneOne :=
  (formInAdaptedChart_isPositive hz haway).1

theorem metricInAdaptedChart_posDef : (metricInAdaptedChart D ω₀ χ z hz haway).PosDef :=
  (isPositive_iff.mp (formInAdaptedChart_isPositive hz haway)).2

theorem metricInAdaptedChart_isHermitian : (metricInAdaptedChart D ω₀ χ z hz haway).IsHermitian :=
  (formInAdaptedChart_isOneOne hz haway).isHermitian_coeffMatrix

/-- The adapted quadratic form is the Hermitian form of the adapted coefficient matrix. -/
theorem metricQuadraticInAdaptedChart_eq_sum (v : E n) :
    metricQuadraticInAdaptedChart D ω₀ χ z hz haway v =
      (∑ j, ∑ k, metricInAdaptedChart D ω₀ χ z hz haway j k * v j * star (v k)).re := by
  rw [metricQuadraticInAdaptedChart,
    (formInAdaptedChart_isOneOne (ω₀ := ω₀) hz haway).apply_I_smul]
  simp only [metricInAdaptedChart]
  ring

theorem metricQuadraticInAdaptedChart_pos {v : E n} (hv : v ≠ 0) :
    0 < metricQuadraticInAdaptedChart D ω₀ χ z hz haway v := by
  have h := (formInAdaptedChart_isPositive (ω₀ := ω₀) hz haway).2 v hv
  rw [metricQuadraticInAdaptedChart]
  linarith

theorem metricQuadraticInAdaptedChart_nonneg (v : E n) :
    0 ≤ metricQuadraticInAdaptedChart D ω₀ χ z hz haway v := by
  rcases eq_or_ne v 0 with rfl | hv
  · have h0 : formInAdaptedChart D ω₀ χ z hz haway ![0, Complex.I • 0] = 0 :=
      (formInAdaptedChart D ω₀ χ z hz haway).map_coord_zero 0 rfl
    simp only [metricQuadraticInAdaptedChart, h0, zero_div, le_refl]
  · exact (metricQuadraticInAdaptedChart_pos hz haway hv).le

end AdaptedMetric

/-! ### Change of adapted chart -/

section Change

variable {D : SmoothDivisor n X} {ω₀ : KahlerForm n D.complement} {p₁ p₂ : X}
  {χ₁ : DivisorChart n X D.carrier p₁} {χ₂ : DivisorChart n X D.carrier p₂}
  {z₁ z₂ : E n} (hz₁ : z₁ ∈ χ₁.coord.target) (haway₁ : z₁ 0 ≠ 0)
  (hz₂ : z₂ ∈ χ₂.coord.target) (haway₂ : z₂ 0 ≠ 0)
  (hsame : χ₁.coord.symm z₁ = χ₂.coord.symm z₂)
include hz₁ hz₂ hsame

omit [IsManifold 𝓘(ℂ, E n) ω X] hz₁ in
theorem adaptedTransition_apply : (χ₂.coord ∘ χ₁.coord.symm) z₁ = z₂ := by
  simp only [Function.comp_apply, hsame, χ₂.coord.right_inv hz₂]

omit [IsManifold 𝓘(ℂ, E n) ω X] hz₁ in
theorem adaptedTransition_mem_source : χ₁.coord.symm z₁ ∈ χ₂.coord.source := by
  rw [hsame]
  exact χ₂.coord.map_target hz₂

/-- **Change of adapted chart.** The form in `χ₁`-coordinates is the pullback of the form in
`χ₂`-coordinates by the derivative of the holomorphic transition `Φ = χ₂ ∘ χ₁⁻¹`. -/
theorem formInAdaptedChart_change :
    formInAdaptedChart D ω₀ χ₁ z₁ hz₁ haway₁ =
      (formInAdaptedChart D ω₀ χ₂ z₂ hz₂ haway₂).compContinuousLinearMap
        (fderiv ℝ (χ₂.coord ∘ χ₁.coord.symm) z₁) := by
  have hsrc := adaptedTransition_mem_source hz₂ hsame
  have hΦz := adaptedTransition_apply hz₂ hsame
  have hpt : χ₁.symmComplement hz₁ haway₁ = χ₂.symmComplement hz₂ haway₂ := Subtype.ext hsame
  -- the two transitions to the selected chart at `y = χ₁⁻¹ z₁ = χ₂⁻¹ z₂`
  have hloc : χ₁.toChartAt (χ₁.coord.symm z₁) =ᶠ[𝓝 z₁]
      χ₂.toChartAt (χ₂.coord.symm z₂) ∘ (χ₂.coord ∘ χ₁.coord.symm) := by
    have hev : ∀ᶠ w in 𝓝 z₁, χ₁.coord.symm w ∈ χ₂.coord.source :=
      (χ₁.coord.continuousAt_symm hz₁).preimage_mem_nhds (χ₂.coord.open_source.mem_nhds hsrc)
    filter_upwards [hev] with w hw
    simp only [DivisorChart.toChartAt, Function.comp_apply, hsame, χ₂.coord.left_inv hw]
  have hΦ : DifferentiableAt ℝ (χ₂.coord ∘ χ₁.coord.symm) z₁ :=
    ((contDiffAt_adaptedTransition χ₁ χ₂ hz₁ hsrc).differentiableAt (by simp)).restrictScalars ℝ
  have hτ₂ : DifferentiableAt ℝ (χ₂.toChartAt (χ₂.coord.symm z₂))
      ((χ₂.coord ∘ χ₁.coord.symm) z₁) := by
    rw [hΦz]
    exact ((χ₂.contDiffAt_toChartAt hz₂).differentiableAt (by simp)).restrictScalars ℝ
  rw [formInAdaptedChart, formInAdaptedChart, hpt, hloc.fderiv_eq, fderiv_comp z₁ hτ₂ hΦ, hΦz,
    compContinuousLinearMap_comp']

omit [IsManifold 𝓘(ℂ, E n) ω X] in
theorem fderiv_real_adaptedTransition :
    fderiv ℝ (χ₂.coord ∘ χ₁.coord.symm) z₁ =
      (fderiv ℂ (χ₂.coord ∘ χ₁.coord.symm) z₁).restrictScalars ℝ :=
  ((contDiffAt_adaptedTransition χ₁ χ₂ hz₁
    (adaptedTransition_mem_source hz₂ hsame)).differentiableAt (by simp)).fderiv_restrictScalars ℝ

/-- **Change of adapted chart for the quadratic form:** `q₁(z₁; v) = q₂(z₂; DΦ(z₁) v)`. -/
theorem metricQuadraticInAdaptedChart_change (v : E n) :
    metricQuadraticInAdaptedChart D ω₀ χ₁ z₁ hz₁ haway₁ v =
      metricQuadraticInAdaptedChart D ω₀ χ₂ z₂ hz₂ haway₂
        (fderiv ℂ (χ₂.coord ∘ χ₁.coord.symm) z₁ v) := by
  rw [metricQuadraticInAdaptedChart, formInAdaptedChart_change hz₁ haway₁ hz₂ haway₂ hsame,
    fderiv_real_adaptedTransition hz₁ hz₂ hsame, compContinuousLinearMap_apply_I_smul]
  rfl

/-- **Change of adapted chart for the coefficient matrix:** `g₁ = Aᵀ g₂ Ā` with
`A = clmMatrix (DΦ(z₁))`, in the upstream index convention. -/
theorem metricInAdaptedChart_change :
    metricInAdaptedChart D ω₀ χ₁ z₁ hz₁ haway₁ =
      (EuclideanSpace.clmMatrix (fderiv ℂ (χ₂.coord ∘ χ₁.coord.symm) z₁)).transpose *
        metricInAdaptedChart D ω₀ χ₂ z₂ hz₂ haway₂ *
        (EuclideanSpace.clmMatrix (fderiv ℂ (χ₂.coord ∘ χ₁.coord.symm) z₁)).map star := by
  rw [metricInAdaptedChart, formInAdaptedChart_change hz₁ haway₁ hz₂ haway₂ hsame,
    fderiv_real_adaptedTransition hz₁ hz₂ hsame,
    (formInAdaptedChart_isOneOne (ω₀ := ω₀) hz₂ haway₂).coeffMatrix_compContinuousLinearMap]
  rfl

end Change

/-! ### The model in its own coordinates -/

section Model

/-- For the coordinate hyperplane `D = {z_0 = 0} ⊆ ℂⁿ` with the identity adapted chart, the form
of the model `modelConeFormOn` in adapted coordinates is the model form itself. -/
theorem formInAdaptedChart_model (β : ConeAngle) (p : E n) {z : E n}
    (hz : z ∈ (coordHyperplaneChart n p).coord.target) (haway : z 0 ≠ 0) :
    formInAdaptedChart (coordHyperplane n)
        (modelConeFormOn (singleConeWeights β) (coordHyperplane n).complement
          (coordHyperplane_complement_subset n β))
        (coordHyperplaneChart n p) z hz haway =
      ddbar (modelPotential (singleConeWeights β)) z := by
  have hτ : (coordHyperplaneChart n p).toChartAt ((coordHyperplaneChart n p).coord.symm z) =
      id := by
    funext w
    simp [DivisorChart.toChartAt, coordHyperplaneChart, chartAt_self_eq]
  unfold formInAdaptedChart
  rw [hτ, fderiv_id, modelConeFormOn_apply]
  rfl

/-- For the coordinate hyperplane with the identity adapted chart, the adapted quadratic form of
the model is `modelConeQuadratic`. -/
theorem metricQuadraticInAdaptedChart_model (β : ConeAngle) (p : E n) {z : E n}
    (hz : z ∈ (coordHyperplaneChart n p).coord.target) (haway : z 0 ≠ 0) (v : E n) :
    metricQuadraticInAdaptedChart (coordHyperplane n)
        (modelConeFormOn (singleConeWeights β) (coordHyperplane n).complement
          (coordHyperplane_complement_subset n β))
        (coordHyperplaneChart n p) z hz haway v =
      modelConeQuadratic (singleConeWeights β) z v := by
  unfold metricQuadraticInAdaptedChart
  rw [formInAdaptedChart_model]
  have hzD : z ∈ (coordHyperplane n).complement := haway
  have h := modelConeFormOn_apply_I_smul (singleConeWeights β) (coordHyperplane n).complement
    (coordHyperplane_complement_subset n β) ⟨z, hzD⟩ v
  rw [modelConeFormOn_apply] at h
  simp only at h
  rw [h]
  ring

end Model

end ConicalKahler
