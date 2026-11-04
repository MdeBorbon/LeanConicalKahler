module

public import ConicalKahler.Divisors.AdaptedChart
public import ConicalKahler.Cone.Model

/-!
# The metric of a Kähler form in an arbitrary holomorphic chart

`KahlerForm.metricInChart` computes `g_{jk̄}` in the chart *selected* by `ChartedSpace`. An
adapted chart `χ : DivisorChart n X D p` is in general a different chart, so we pull the form back
explicitly. Let `ω₀` be a Kähler form on an open set `U ⊆ X` and `c` a holomorphic chart of `X`
(`HolChart`). For `z ∈ c.target` with `y = c⁻¹(z) ∈ U`, the value `ω₀ y` is a `2`-form on `ℂⁿ`
expressed in the selected chart at `y`. The transition from `c`-coordinates to that chart is
`τ = extChartAt y ∘ c⁻¹` (`HolChart.toChartAt`), so the form in `c`-coordinates is

  `formInHolChart U ω₀ c z = (ω₀ y) ∘ Dτ(z)`.

For a smooth divisor `D`, `U = X \ D` and an adapted chart `χ`, this is `formInAdaptedChart`
(`z_0 ≠ 0` guarantees `y ∉ D`). SNC charts use `formInHolChart` in the same way, and the selected
chart gives back `KahlerForm.metricInChart` (`ConicalKahler.Cone.SelectedChart`).

## Main declarations

* `formInHolChart`, `metricInHolChart`, `metricQuadraticInHolChart` for any holomorphic chart;
  positivity (`formInHolChart_isPositive`, …) and the change of chart law
  (`formInHolChart_change`, `metricQuadraticInHolChart_change`, `metricInHolChart_change`).

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

The agreement with `KahlerForm.metricInChart` when `χ` is the selected chart, and the general
transformation law between the two, are in `ConicalKahler.Cone.SelectedChart`.
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

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X] [IsManifold 𝓘(ℂ, E n) ω X]

/-! ### The form and metric in an arbitrary holomorphic chart -/

section HolMetric

variable (U : TopologicalSpace.Opens X) (ω₀ : KahlerForm n U) (c : HolChart n X)

/-- The Kähler form `ω₀` on `U` written in the coordinates of the holomorphic chart `c`, at a
coordinate point `z` with `c⁻¹(z) ∈ U`: `(ω₀ y) ∘ Dτ(z)` with `y = c⁻¹(z)` and
`τ = extChartAt y ∘ c⁻¹`. -/
noncomputable def formInHolChart (z : E n) (hU : c.coord.symm z ∈ U) : E n [⋀^Fin 2]→L[ℝ] ℝ :=
  (ω₀ ⟨c.coord.symm z, hU⟩).compContinuousLinearMap (fderiv ℝ (c.toChartAt (c.coord.symm z)) z)

/-- The Hermitian coefficient matrix `g^c_{jk̄}(z)` of `ω₀` in the holomorphic chart `c`. -/
noncomputable def metricInHolChart (z : E n) (hU : c.coord.symm z ∈ U) :
    Matrix (Fin n) (Fin n) ℂ :=
  (formInHolChart U ω₀ c z hU).coeffMatrix

/-- The Hermitian quadratic form `g^c(v, v) / 2 = ∑ g^c_{jk̄} v_j v̄_k` of `ω₀` in the chart `c`. -/
noncomputable def metricQuadraticInHolChart (z : E n) (hU : c.coord.symm z ∈ U) (v : E n) : ℝ :=
  formInHolChart U ω₀ c z hU ![v, Complex.I • v] / 2

/-- The form only depends on the coordinate map of the chart. -/
theorem formInHolChart_congr {c' : HolChart n X} (h : c.coord = c'.coord) {z : E n}
    (hU : c.coord.symm z ∈ U) (hU' : c'.coord.symm z ∈ U) :
    formInHolChart U ω₀ c z hU = formInHolChart U ω₀ c' z hU' := by
  obtain rfl := HolChart.ext' h
  rfl

/-- Transport a Kähler form along an equality of open subsets. -/
def kahlerCast {V : TopologicalSpace.Opens X} (h : U = V) (ω₀ : KahlerForm n U) : KahlerForm n V :=
  h ▸ ω₀

/-- Transporting the form along `U = V` does not change its expression in any chart. -/
theorem formInHolChart_kahlerCast {V : TopologicalSpace.Opens X} (h : U = V) {z : E n}
    (hU : c.coord.symm z ∈ U) (hV : c.coord.symm z ∈ V) :
    formInHolChart V (kahlerCast U h ω₀) c z hV = formInHolChart U ω₀ c z hU := by
  subst h
  rfl

variable {U ω₀ c} {z : E n} (hz : z ∈ c.coord.target) (hU : c.coord.symm z ∈ U)
include hz

theorem formInHolChart_eq :
    formInHolChart U ω₀ c z hU =
      (ω₀ ⟨c.coord.symm z, hU⟩).compContinuousLinearMap
        ((fderiv ℂ (c.toChartAt (c.coord.symm z)) z).restrictScalars ℝ) := by
  rw [formInHolChart, c.fderiv_real_toChartAt hz]

theorem formInHolChart_isPositive : (formInHolChart U ω₀ c z hU).IsPositive := by
  rw [formInHolChart_eq hz]
  exact isPositive_compContinuousLinearMap_of_injective (ω₀.isPositive _) _
    (c.injective_fderiv_toChartAt hz)

theorem formInHolChart_isOneOne : (formInHolChart U ω₀ c z hU).IsOneOne :=
  (formInHolChart_isPositive hz hU).1

theorem metricInHolChart_posDef : (metricInHolChart U ω₀ c z hU).PosDef :=
  (isPositive_iff.mp (formInHolChart_isPositive hz hU)).2

theorem metricInHolChart_isHermitian : (metricInHolChart U ω₀ c z hU).IsHermitian :=
  (formInHolChart_isOneOne hz hU).isHermitian_coeffMatrix

/-- The quadratic form is the Hermitian form of the coefficient matrix. -/
theorem metricQuadraticInHolChart_eq_sum (v : E n) :
    metricQuadraticInHolChart U ω₀ c z hU v =
      (∑ j, ∑ k, metricInHolChart U ω₀ c z hU j k * v j * star (v k)).re := by
  rw [metricQuadraticInHolChart, (formInHolChart_isOneOne (ω₀ := ω₀) hz hU).apply_I_smul]
  simp only [metricInHolChart]
  ring

theorem metricQuadraticInHolChart_pos {v : E n} (hv : v ≠ 0) :
    0 < metricQuadraticInHolChart U ω₀ c z hU v := by
  have h := (formInHolChart_isPositive (ω₀ := ω₀) hz hU).2 v hv
  rw [metricQuadraticInHolChart]
  linarith

theorem metricQuadraticInHolChart_nonneg (v : E n) :
    0 ≤ metricQuadraticInHolChart U ω₀ c z hU v := by
  rcases eq_or_ne v 0 with rfl | hv
  · have h0 : formInHolChart U ω₀ c z hU ![0, Complex.I • 0] = 0 :=
      (formInHolChart U ω₀ c z hU).map_coord_zero 0 rfl
    simp only [metricQuadraticInHolChart, h0, zero_div, le_refl]
  · exact (metricQuadraticInHolChart_pos hz hU hv).le

end HolMetric

/-- In the identity chart of `ℂⁿ`, a Kähler form on an open `U ⊆ ℂⁿ` is its own expression. -/
theorem formInHolChart_refl (U : TopologicalSpace.Opens (E n)) (ω₀ : KahlerForm n U) {z : E n}
    (hU : (HolChart.refl n).coord.symm z ∈ U) :
    formInHolChart U ω₀ (HolChart.refl n) z hU = ω₀ ⟨z, hU⟩ := by
  have hτ : (HolChart.refl n).toChartAt ((HolChart.refl n).coord.symm z) = id := by
    funext w
    simp [HolChart.toChartAt, HolChart.refl, chartAt_self_eq]
  unfold formInHolChart
  rw [hτ, fderiv_id]
  rfl

/-- In the identity chart of `ℂⁿ`, the quadratic form is `ω₀(v, Jv) / 2`. -/
theorem metricQuadraticInHolChart_refl (U : TopologicalSpace.Opens (E n)) (ω₀ : KahlerForm n U)
    {z : E n} (hU : (HolChart.refl n).coord.symm z ∈ U) (v : E n) :
    metricQuadraticInHolChart U ω₀ (HolChart.refl n) z hU v = ω₀ ⟨z, hU⟩ ![v, Complex.I • v] / 2 := by
  rw [metricQuadraticInHolChart, formInHolChart_refl]

section HolChange

variable {U : TopologicalSpace.Opens X} {ω₀ : KahlerForm n U} {c₁ c₂ : HolChart n X}
  {z₁ z₂ : E n} (hz₁ : z₁ ∈ c₁.coord.target) (hU₁ : c₁.coord.symm z₁ ∈ U)
  (hz₂ : z₂ ∈ c₂.coord.target) (hU₂ : c₂.coord.symm z₂ ∈ U)
  (hsame : c₁.coord.symm z₁ = c₂.coord.symm z₂)
include hz₁ hz₂ hsame

omit [IsManifold 𝓘(ℂ, E n) ω X] hz₁ in
theorem holTransition_apply : (c₂.coord ∘ c₁.coord.symm) z₁ = z₂ := by
  simp only [Function.comp_apply, hsame, c₂.coord.right_inv hz₂]

omit [IsManifold 𝓘(ℂ, E n) ω X] hz₁ in
theorem holTransition_mem_source : c₁.coord.symm z₁ ∈ c₂.coord.source := by
  rw [hsame]
  exact c₂.coord.map_target hz₂

/-- **Change of holomorphic chart.** The form in `c₁`-coordinates is the pullback of the form in
`c₂`-coordinates by the derivative of the holomorphic transition `Φ = c₂ ∘ c₁⁻¹`. -/
theorem formInHolChart_change :
    formInHolChart U ω₀ c₁ z₁ hU₁ =
      (formInHolChart U ω₀ c₂ z₂ hU₂).compContinuousLinearMap
        (fderiv ℝ (c₂.coord ∘ c₁.coord.symm) z₁) := by
  have hsrc := holTransition_mem_source hz₂ hsame
  have hΦz := holTransition_apply hz₂ hsame
  have hpt : (⟨c₁.coord.symm z₁, hU₁⟩ : U) = ⟨c₂.coord.symm z₂, hU₂⟩ := Subtype.ext hsame
  have hloc : c₁.toChartAt (c₁.coord.symm z₁) =ᶠ[𝓝 z₁]
      c₂.toChartAt (c₂.coord.symm z₂) ∘ (c₂.coord ∘ c₁.coord.symm) := by
    have hev : ∀ᶠ w in 𝓝 z₁, c₁.coord.symm w ∈ c₂.coord.source :=
      (c₁.coord.continuousAt_symm hz₁).preimage_mem_nhds (c₂.coord.open_source.mem_nhds hsrc)
    filter_upwards [hev] with w hw
    simp only [HolChart.toChartAt, Function.comp_apply, hsame, c₂.coord.left_inv hw]
  have hΦ : DifferentiableAt ℝ (c₂.coord ∘ c₁.coord.symm) z₁ :=
    ((HolChart.contDiffAt_transition c₁ c₂ hz₁ hsrc).differentiableAt
      (by simp)).restrictScalars ℝ
  have hτ₂ : DifferentiableAt ℝ (c₂.toChartAt (c₂.coord.symm z₂))
      ((c₂.coord ∘ c₁.coord.symm) z₁) := by
    rw [hΦz]
    exact ((c₂.contDiffAt_toChartAt hz₂).differentiableAt (by simp)).restrictScalars ℝ
  rw [formInHolChart, formInHolChart, hpt, hloc.fderiv_eq, fderiv_comp z₁ hτ₂ hΦ, hΦz,
    compContinuousLinearMap_comp']

omit [IsManifold 𝓘(ℂ, E n) ω X] in
theorem fderiv_real_holTransition :
    fderiv ℝ (c₂.coord ∘ c₁.coord.symm) z₁ =
      (fderiv ℂ (c₂.coord ∘ c₁.coord.symm) z₁).restrictScalars ℝ :=
  ((HolChart.contDiffAt_transition c₁ c₂ hz₁
    (holTransition_mem_source hz₂ hsame)).differentiableAt (by simp)).fderiv_restrictScalars ℝ

/-- **Change of holomorphic chart for the quadratic form:** `q₁(z₁; v) = q₂(z₂; DΦ(z₁) v)`. -/
theorem metricQuadraticInHolChart_change (v : E n) :
    metricQuadraticInHolChart U ω₀ c₁ z₁ hU₁ v =
      metricQuadraticInHolChart U ω₀ c₂ z₂ hU₂ (fderiv ℂ (c₂.coord ∘ c₁.coord.symm) z₁ v) := by
  rw [metricQuadraticInHolChart, formInHolChart_change hz₁ hU₁ hz₂ hU₂ hsame,
    fderiv_real_holTransition hz₁ hz₂ hsame, compContinuousLinearMap_apply_I_smul]
  rfl

/-- **Change of holomorphic chart for the coefficient matrix:** `g₁ = Aᵀ g₂ Ā` with
`A = clmMatrix (DΦ(z₁))`, in the upstream index convention. -/
theorem metricInHolChart_change :
    metricInHolChart U ω₀ c₁ z₁ hU₁ =
      (EuclideanSpace.clmMatrix (fderiv ℂ (c₂.coord ∘ c₁.coord.symm) z₁)).transpose *
        metricInHolChart U ω₀ c₂ z₂ hU₂ *
        (EuclideanSpace.clmMatrix (fderiv ℂ (c₂.coord ∘ c₁.coord.symm) z₁)).map star := by
  rw [metricInHolChart, formInHolChart_change hz₁ hU₁ hz₂ hU₂ hsame,
    fderiv_real_holTransition hz₁ hz₂ hsame,
    (formInHolChart_isOneOne (ω₀ := ω₀) hz₂ hU₂).coeffMatrix_compContinuousLinearMap]
  rfl

end HolChange

/-! ### Transition maps between an adapted chart and the selected charts -/

variable [NeZero n]

namespace DivisorChart

variable {D : Set X} {p : X}

/-- The transition `extChartAt y ∘ χ⁻¹` from adapted coordinates to the selected chart at `y`
(`HolChart.toChartAt` of `χ.toHolChart`). -/
noncomputable def toChartAt (χ : DivisorChart n X D p) (y : X) : E n → E n :=
  extChartAt 𝓘(ℂ, E n) y ∘ χ.coord.symm

/-- The transition `χ ∘ (extChartAt y)⁻¹` from the selected chart at `y` to adapted coordinates. -/
noncomputable def fromChartAt (χ : DivisorChart n X D p) (y : X) : E n → E n :=
  χ.coord ∘ (extChartAt 𝓘(ℂ, E n) y).symm

omit [IsManifold 𝓘(ℂ, E n) ω X] in
theorem contDiffAt_toChartAt (χ : DivisorChart n X D p) {z : E n} (hz : z ∈ χ.coord.target) :
    ContDiffAt ℂ ∞ (χ.toChartAt (χ.coord.symm z)) z :=
  χ.toHolChart.contDiffAt_toChartAt hz

theorem contDiffAt_fromChartAt (χ : DivisorChart n X D p) {y : X} (hy : y ∈ χ.coord.source) :
    ContDiffAt ℂ ∞ (χ.fromChartAt y) (extChartAt 𝓘(ℂ, E n) y y) :=
  χ.toHolChart.contDiffAt_fromChartAt hy

omit [IsManifold 𝓘(ℂ, E n) ω X] in
theorem fromChartAt_comp_toChartAt (χ : DivisorChart n X D p) {z : E n}
    (hz : z ∈ χ.coord.target) :
    χ.fromChartAt (χ.coord.symm z) ∘ χ.toChartAt (χ.coord.symm z) =ᶠ[𝓝 z] id :=
  χ.toHolChart.fromChartAt_comp_toChartAt hz

/-- The derivative of the transition to the selected chart has a left inverse. -/
theorem fderiv_fromChartAt_comp_fderiv_toChartAt (χ : DivisorChart n X D p) {z : E n}
    (hz : z ∈ χ.coord.target) :
    (fderiv ℂ (χ.fromChartAt (χ.coord.symm z))
        (χ.toChartAt (χ.coord.symm z) z)).comp (fderiv ℂ (χ.toChartAt (χ.coord.symm z)) z) =
      ContinuousLinearMap.id ℂ (E n) :=
  χ.toHolChart.fderiv_fromChartAt_comp_fderiv_toChartAt hz

theorem injective_fderiv_toChartAt (χ : DivisorChart n X D p) {z : E n}
    (hz : z ∈ χ.coord.target) :
    Function.Injective (fderiv ℂ (χ.toChartAt (χ.coord.symm z)) z) :=
  χ.toHolChart.injective_fderiv_toChartAt hz

omit [IsManifold 𝓘(ℂ, E n) ω X] in
theorem fderiv_real_toChartAt (χ : DivisorChart n X D p) {z : E n} (hz : z ∈ χ.coord.target) :
    fderiv ℝ (χ.toChartAt (χ.coord.symm z)) z =
      (fderiv ℂ (χ.toChartAt (χ.coord.symm z)) z).restrictScalars ℝ :=
  χ.toHolChart.fderiv_real_toChartAt hz

end DivisorChart

/-! ### Transition between two adapted charts -/

omit [IsManifold 𝓘(ℂ, E n) ω X] in
/-- Two adapted charts are related by a holomorphic transition `χ₂ ∘ χ₁⁻¹` near any common point. -/
theorem contDiffAt_adaptedTransition {D : Set X} {p₁ p₂ : X} (χ₁ : DivisorChart n X D p₁)
    (χ₂ : DivisorChart n X D p₂) {z₁ : E n} (hz₁ : z₁ ∈ χ₁.coord.target)
    (h₂ : χ₁.coord.symm z₁ ∈ χ₂.coord.source) :
    ContDiffAt ℂ ∞ (χ₂.coord ∘ χ₁.coord.symm) z₁ :=
  HolChart.contDiffAt_transition χ₁.toHolChart χ₂.toHolChart hz₁ h₂

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

/-- The adapted-chart form is the holomorphic-chart form of `χ.toHolChart` on `U = X \ D`. -/
theorem formInAdaptedChart_eq_formInHolChart (z : E n) (hz : z ∈ χ.coord.target)
    (haway : z 0 ≠ 0) :
    formInAdaptedChart D ω₀ χ z hz haway =
      formInHolChart D.complement ω₀ χ.toHolChart z (χ.symm_notMem hz haway) :=
  rfl

theorem metricInAdaptedChart_eq_metricInHolChart (z : E n) (hz : z ∈ χ.coord.target)
    (haway : z 0 ≠ 0) :
    metricInAdaptedChart D ω₀ χ z hz haway =
      metricInHolChart D.complement ω₀ χ.toHolChart z (χ.symm_notMem hz haway) :=
  rfl

theorem metricQuadraticInAdaptedChart_eq_metricQuadraticInHolChart (z : E n)
    (hz : z ∈ χ.coord.target) (haway : z 0 ≠ 0) (v : E n) :
    metricQuadraticInAdaptedChart D ω₀ χ z hz haway v =
      metricQuadraticInHolChart D.complement ω₀ χ.toHolChart z (χ.symm_notMem hz haway) v :=
  rfl

variable {D ω₀ χ} {z : E n} (hz : z ∈ χ.coord.target) (haway : z 0 ≠ 0)
include hz

theorem formInAdaptedChart_eq :
    formInAdaptedChart D ω₀ χ z hz haway =
      (ω₀ (χ.symmComplement hz haway)).compContinuousLinearMap
        ((fderiv ℂ (χ.toChartAt (χ.coord.symm z)) z).restrictScalars ℝ) :=
  formInHolChart_eq (c := χ.toHolChart) hz _

theorem formInAdaptedChart_isPositive : (formInAdaptedChart D ω₀ χ z hz haway).IsPositive :=
  formInHolChart_isPositive (c := χ.toHolChart) hz _

theorem formInAdaptedChart_isOneOne : (formInAdaptedChart D ω₀ χ z hz haway).IsOneOne :=
  (formInAdaptedChart_isPositive hz haway).1

theorem metricInAdaptedChart_posDef : (metricInAdaptedChart D ω₀ χ z hz haway).PosDef :=
  metricInHolChart_posDef (c := χ.toHolChart) hz _

theorem metricInAdaptedChart_isHermitian : (metricInAdaptedChart D ω₀ χ z hz haway).IsHermitian :=
  metricInHolChart_isHermitian (c := χ.toHolChart) hz _

/-- The adapted quadratic form is the Hermitian form of the adapted coefficient matrix. -/
theorem metricQuadraticInAdaptedChart_eq_sum (v : E n) :
    metricQuadraticInAdaptedChart D ω₀ χ z hz haway v =
      (∑ j, ∑ k, metricInAdaptedChart D ω₀ χ z hz haway j k * v j * star (v k)).re :=
  metricQuadraticInHolChart_eq_sum (c := χ.toHolChart) hz _ v

theorem metricQuadraticInAdaptedChart_pos {v : E n} (hv : v ≠ 0) :
    0 < metricQuadraticInAdaptedChart D ω₀ χ z hz haway v :=
  metricQuadraticInHolChart_pos (c := χ.toHolChart) hz _ hv

theorem metricQuadraticInAdaptedChart_nonneg (v : E n) :
    0 ≤ metricQuadraticInAdaptedChart D ω₀ χ z hz haway v :=
  metricQuadraticInHolChart_nonneg (c := χ.toHolChart) hz _ v

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
        (fderiv ℝ (χ₂.coord ∘ χ₁.coord.symm) z₁) :=
  formInHolChart_change (c₁ := χ₁.toHolChart) (c₂ := χ₂.toHolChart) hz₁ _ hz₂ _ hsame

omit [IsManifold 𝓘(ℂ, E n) ω X] in
theorem fderiv_real_adaptedTransition :
    fderiv ℝ (χ₂.coord ∘ χ₁.coord.symm) z₁ =
      (fderiv ℂ (χ₂.coord ∘ χ₁.coord.symm) z₁).restrictScalars ℝ :=
  fderiv_real_holTransition (c₁ := χ₁.toHolChart) (c₂ := χ₂.toHolChart) hz₁ hz₂ hsame

/-- **Change of adapted chart for the quadratic form:** `q₁(z₁; v) = q₂(z₂; DΦ(z₁) v)`. -/
theorem metricQuadraticInAdaptedChart_change (v : E n) :
    metricQuadraticInAdaptedChart D ω₀ χ₁ z₁ hz₁ haway₁ v =
      metricQuadraticInAdaptedChart D ω₀ χ₂ z₂ hz₂ haway₂
        (fderiv ℂ (χ₂.coord ∘ χ₁.coord.symm) z₁ v) :=
  metricQuadraticInHolChart_change (c₁ := χ₁.toHolChart) (c₂ := χ₂.toHolChart) hz₁ _ hz₂ _
    hsame v

/-- **Change of adapted chart for the coefficient matrix:** `g₁ = Aᵀ g₂ Ā` with
`A = clmMatrix (DΦ(z₁))`, in the upstream index convention. -/
theorem metricInAdaptedChart_change :
    metricInAdaptedChart D ω₀ χ₁ z₁ hz₁ haway₁ =
      (EuclideanSpace.clmMatrix (fderiv ℂ (χ₂.coord ∘ χ₁.coord.symm) z₁)).transpose *
        metricInAdaptedChart D ω₀ χ₂ z₂ hz₂ haway₂ *
        (EuclideanSpace.clmMatrix (fderiv ℂ (χ₂.coord ∘ χ₁.coord.symm) z₁)).map star :=
  metricInHolChart_change (c₁ := χ₁.toHolChart) (c₂ := χ₂.toHolChart) hz₁ _ hz₂ _ hsame

end Change

/-! ### The model in its own coordinates -/

section Model

/-- For the coordinate hyperplane `D = {z_0 = 0} ⊆ ℂⁿ` and the identity adapted chart, any Kähler
form on `ℂⁿ \ D` is its own expression in adapted coordinates. -/
theorem formInAdaptedChart_coordHyperplaneChart
    (ω₀ : KahlerForm n (coordHyperplane n).complement) (p : E n) {z : E n}
    (hz : z ∈ (coordHyperplaneChart n p).coord.target) (haway : z 0 ≠ 0) :
    formInAdaptedChart (coordHyperplane n) ω₀ (coordHyperplaneChart n p) z hz haway =
      ω₀ ⟨z, haway⟩ := by
  have hτ : (coordHyperplaneChart n p).toChartAt ((coordHyperplaneChart n p).coord.symm z) =
      id := by
    funext w
    simp [DivisorChart.toChartAt, coordHyperplaneChart, chartAt_self_eq]
  unfold formInAdaptedChart
  rw [hτ, fderiv_id]
  rfl

/-- In the identity chart, the adapted quadratic form is `ω(v, Jv) / 2`. -/
theorem metricQuadraticInAdaptedChart_coordHyperplaneChart
    (ω₀ : KahlerForm n (coordHyperplane n).complement) (p : E n) {z : E n}
    (hz : z ∈ (coordHyperplaneChart n p).coord.target) (haway : z 0 ≠ 0) (v : E n) :
    metricQuadraticInAdaptedChart (coordHyperplane n) ω₀ (coordHyperplaneChart n p) z hz haway v =
      ω₀ ⟨z, haway⟩ ![v, Complex.I • v] / 2 := by
  rw [metricQuadraticInAdaptedChart, formInAdaptedChart_coordHyperplaneChart]

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
