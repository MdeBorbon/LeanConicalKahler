module

public import ConicalKahler.Cone.ChartMetric

/-!
# Compatibility with the upstream `KahlerForm.metricInChart`

Upstream computes the local metric of a Kähler form `ω₀` on a manifold `M` only in the charts
selected by `ChartedSpace`: `ω₀.metricInChart x z = (ω₀.toFormField.chartRep x z).coeffMatrix`.
Here `M = U` is an open subset of `X` (for instance `U = X \ D`), with Mathlib's induced atlas.
The chart of `U` at `x` is the restriction of the chart of `X` at `x`.

This file proves that the pullback along holomorphic charts (`formInHolChart`, and so
`formInAdaptedChart`) extends the upstream construction.

* `chartRep_eq_formInHolChart`, `metricInChart_eq_metricInHolChart`: in the selected chart
  `HolChart.ofChartAt x` (the chart of `X` at `x`), the pullback *is* the upstream coordinate
  expression, on the whole chart target of `U`.
* `metricInAdaptedChart_eq_metricInChart`: **if an adapted chart `χ` of a smooth divisor is the
  selected chart at `x ∈ X \ D`, then `metricInAdaptedChart` and `metricInChart` agree** at every
  coordinate point off `{z_0 = 0}`.
* `metricInChart_eq_metricInHolChart_change`, `metricInChart_eq_metricInAdaptedChart_change` and
  `chartRep_apply_I_smul_eq_metricQuadraticInAdaptedChart`: for an *arbitrary* adapted chart,
  `metricInChart x z = Aᵀ g^χ(w) Ā` with `A = D(χ ∘ (chartAt x)⁻¹)(z)` and
  `w = χ((chartAt x)⁻¹ z)`, in the upstream index convention. Equivalently
  `ω(v, Jv)/2 = q^χ(w; Av)`.

Statements about arbitrary adapted charts must go through `metricInAdaptedChart`. Upstream
`metricInChart` only sees selected charts (spec §3.3). These theorems are the bridge between the
two.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Set Filter ContinuousAlternatingMap

namespace ConicalKahler

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X]

/-! ### Charts of an open subset -/

section Opens

variable (U : TopologicalSpace.Opens X)

/-- The extended chart of `U` at `x` is the chart of `X` at `x`. -/
theorem extChartAt_opens_apply' (x y : U) :
    extChartAt 𝓘(ℝ, E n) x y = chartAt (E n) (x : X) y := by
  simp [extChartAt, TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_def]

/-- The chart target of `U` at `x` is the part of the chart target of `X` at `x` lying over `U`. -/
theorem mem_extChartAt_opens_target (x : U) {z : E n} :
    z ∈ (extChartAt 𝓘(ℝ, E n) x).target ↔
      z ∈ (chartAt (E n) (x : X)).target ∧ (chartAt (E n) (x : X)).symm z ∈ U := by
  simp [extChartAt, TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_def,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]

/-- On the chart target, the inverse chart of `U` is the inverse chart of `X`. -/
theorem extChartAt_opens_symm_coe (x : U) {z : E n}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E n) x).target) :
    (((extChartAt 𝓘(ℝ, E n) x).symm z : U) : X) = (chartAt (E n) (x : X)).symm z := by
  have h := (chartAt (E n) (x : X)).subtypeRestr_symm_apply ⟨x⟩ (y := z) (by
    simpa [extChartAt, TopologicalSpace.Opens.chartAt_eq] using hz)
  simpa [extChartAt, TopologicalSpace.Opens.chartAt_eq] using h

end Opens

variable [IsManifold 𝓘(ℂ, E n) ω X]

/-! ### The selected chart -/

section Selected

variable {U : TopologicalSpace.Opens X}

theorem chartAt_symm_mem_opens (x : U) {z : E n} (hz : z ∈ (extChartAt 𝓘(ℝ, E n) x).target) :
    (HolChart.ofChartAt (n := n) (x : X)).coord.symm z ∈ U :=
  ((mem_extChartAt_opens_target U x).mp hz).2

theorem mem_chartAt_target_of_opens (x : U) {z : E n}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E n) x).target) :
    z ∈ (HolChart.ofChartAt (n := n) (x : X)).coord.target :=
  ((mem_extChartAt_opens_target U x).mp hz).1

/-- **The selected chart gives the upstream coordinate expression.** For `x ∈ U` and `z` in the
chart target of `U` at `x`, the pullback of `ω₀` along the chart of `X` at `x` is
`ω₀.toFormField.chartRep x z`. -/
theorem chartRep_eq_formInHolChart (ω₀ : KahlerForm n U) (x : U) {z : E n}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E n) x).target) :
    ω₀.toFormField.chartRep x z =
      formInHolChart U ω₀ (HolChart.ofChartAt (x : X)) z (chartAt_symm_mem_opens x hz) := by
  set y' : U := (extChartAt 𝓘(ℝ, E n) x).symm z with hy'_def
  have hy' : y' = ⟨(chartAt (E n) (x : X)).symm z, chartAt_symm_mem_opens x hz⟩ :=
    Subtype.ext (extChartAt_opens_symm_coe U x hz)
  have hxz : extChartAt 𝓘(ℝ, E n) x y' = z := (extChartAt 𝓘(ℝ, E n) x).right_inv hz
  -- the upstream tangent coordinate change is the derivative of the transition to the
  -- selected chart at `y'`, computed in the ambient manifold `X`
  have hT : tangentCoordChange 𝓘(ℝ, E n) x y' y' =
      fderiv ℝ ((HolChart.ofChartAt (n := n) (x : X)).toChartAt
        ((chartAt (E n) (x : X)).symm z)) z := by
    rw [tangentCoordChange_def, ModelWithCorners.range_eq_univ, fderivWithin_univ, hxz]
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, E n)) x).mem_nhds hz] with w hw
    simp only [Function.comp_apply, HolChart.toChartAt, HolChart.ofChartAt_coord]
    rw [extChartAt_opens_apply', extChartAt_opens_symm_coe U x hw, hy']
    rfl
  unfold FormField.chartRep formInHolChart
  rw [hT, ← hy'_def, hy']
  rfl

/-- **`metricInChart` is `metricInHolChart` of the selected chart.** -/
theorem metricInChart_eq_metricInHolChart (ω₀ : KahlerForm n U) (x : U) {z : E n}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E n) x).target) :
    ω₀.metricInChart x z =
      metricInHolChart U ω₀ (HolChart.ofChartAt (x : X)) z (chartAt_symm_mem_opens x hz) := by
  rw [KahlerForm.metricInChart, chartRep_eq_formInHolChart ω₀ x hz]
  rfl

/-- **Transformation law between `metricInChart` and an arbitrary holomorphic chart.** Let `c` be
a holomorphic chart whose domain contains `y = (chartAt x)⁻¹ z`. Then
`metricInChart x z = Aᵀ g^c(c y) Ā`, where `A = clmMatrix (D(c ∘ (chartAt x)⁻¹)(z))`. -/
theorem metricInChart_eq_metricInHolChart_change (ω₀ : KahlerForm n U) (x : U) {z : E n}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E n) x).target) (c : HolChart n X)
    (hy : (chartAt (E n) (x : X)).symm z ∈ c.coord.source) :
    ω₀.metricInChart x z =
      (EuclideanSpace.clmMatrix
          (fderiv ℂ (c.coord ∘ (chartAt (E n) (x : X)).symm) z)).transpose *
        metricInHolChart U ω₀ c (c.coord ((chartAt (E n) (x : X)).symm z))
          (by rw [c.coord.left_inv hy]; exact chartAt_symm_mem_opens x hz) *
        (EuclideanSpace.clmMatrix
          (fderiv ℂ (c.coord ∘ (chartAt (E n) (x : X)).symm) z)).map star := by
  rw [metricInChart_eq_metricInHolChart ω₀ x hz]
  exact metricInHolChart_change (c₁ := HolChart.ofChartAt (x : X)) (c₂ := c)
    (mem_chartAt_target_of_opens x hz) _ (c.coord.map_source hy) _ (c.coord.left_inv hy).symm

end Selected

/-! ### Adapted charts of a smooth divisor -/

section Adapted

variable [NeZero n] {D : SmoothDivisor n X} {p : X}

/-- **Agreement with `metricInChart`.** If the adapted chart `χ` is the chart selected at a point
`x ∈ X \ D`, then the metric in the adapted chart equals the upstream local metric
`ω₀.metricInChart x` at every coordinate point off `{z_0 = 0}`. -/
theorem metricInAdaptedChart_eq_metricInChart (ω₀ : KahlerForm n D.complement)
    (χ : DivisorChart n X D.carrier p) (x : D.complement) (hχ : χ.coord = chartAt (E n) (x : X))
    {z : E n} (hz : z ∈ χ.coord.target) (haway : z 0 ≠ 0) :
    metricInAdaptedChart D ω₀ χ z hz haway = ω₀.metricInChart x z := by
  have hz' : z ∈ (extChartAt 𝓘(ℝ, E n) x).target := by
    rw [mem_extChartAt_opens_target]
    refine ⟨hχ ▸ hz, ?_⟩
    rw [← hχ]
    exact χ.symm_notMem hz haway
  rw [metricInChart_eq_metricInHolChart ω₀ x hz', metricInAdaptedChart_eq_metricInHolChart]
  exact congrArg ContinuousAlternatingMap.coeffMatrix
    (formInHolChart_congr D.complement ω₀ χ.toHolChart (c' := HolChart.ofChartAt (x : X)) hχ _ _)

/-- The same agreement for the Hermitian quadratic forms: `q^χ(z; v) = ω₀(v, Jv)/2` in the chart
at `x`. -/
theorem metricQuadraticInAdaptedChart_eq_chartRep (ω₀ : KahlerForm n D.complement)
    (χ : DivisorChart n X D.carrier p) (x : D.complement) (hχ : χ.coord = chartAt (E n) (x : X))
    {z : E n} (hz : z ∈ χ.coord.target) (haway : z 0 ≠ 0) (v : E n) :
    metricQuadraticInAdaptedChart D ω₀ χ z hz haway v =
      ω₀.toFormField.chartRep x z ![v, Complex.I • v] / 2 := by
  have hz' : z ∈ (extChartAt 𝓘(ℝ, E n) x).target := by
    rw [mem_extChartAt_opens_target]
    refine ⟨hχ ▸ hz, ?_⟩
    rw [← hχ]
    exact χ.symm_notMem hz haway
  rw [chartRep_eq_formInHolChart ω₀ x hz', metricQuadraticInAdaptedChart,
    formInAdaptedChart_eq_formInHolChart]
  exact congrArg (fun α : E n [⋀^Fin 2]→L[ℝ] ℝ => α ![v, Complex.I • v] / 2)
    (formInHolChart_congr D.complement ω₀ χ.toHolChart (c' := HolChart.ofChartAt (x : X)) hχ _
      (chartAt_symm_mem_opens x hz'))

/-- The point `w = χ((chartAt x)⁻¹ z)` lies off `{w_0 = 0}`. -/
theorem DivisorChart.coord_chartAt_symm_ne_zero (χ : DivisorChart n X D.carrier p)
    (x : D.complement) {z : E n} (hz : z ∈ (extChartAt 𝓘(ℝ, E n) x).target)
    (hy : (chartAt (E n) (x : X)).symm z ∈ χ.coord.source) :
    χ.coord ((chartAt (E n) (x : X)).symm z) 0 ≠ 0 :=
  χ.coord_ne_zero hy (chartAt_symm_mem_opens x hz)

/-- **Transformation law between `metricInChart` and an arbitrary adapted chart.** For
`y = (chartAt x)⁻¹ z` in the domain of `χ` and `w = χ y`:
`metricInChart x z = Aᵀ g^χ(w) Ā` with `A = clmMatrix (D(χ ∘ (chartAt x)⁻¹)(z))`. -/
theorem metricInChart_eq_metricInAdaptedChart_change (ω₀ : KahlerForm n D.complement)
    (χ : DivisorChart n X D.carrier p) (x : D.complement) {z : E n}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E n) x).target)
    (hy : (chartAt (E n) (x : X)).symm z ∈ χ.coord.source) :
    ω₀.metricInChart x z =
      (EuclideanSpace.clmMatrix
          (fderiv ℂ (χ.coord ∘ (chartAt (E n) (x : X)).symm) z)).transpose *
        metricInAdaptedChart D ω₀ χ (χ.coord ((chartAt (E n) (x : X)).symm z))
          (χ.coord.map_source hy) (χ.coord_chartAt_symm_ne_zero x hz hy) *
        (EuclideanSpace.clmMatrix
          (fderiv ℂ (χ.coord ∘ (chartAt (E n) (x : X)).symm) z)).map star :=
  metricInChart_eq_metricInHolChart_change ω₀ x hz χ.toHolChart hy

/-- **The same law for the quadratic forms:** `ω₀(v, Jv)/2` in the chart at `x` equals
`q^χ(w; A v)`. -/
theorem chartRep_apply_I_smul_eq_metricQuadraticInAdaptedChart (ω₀ : KahlerForm n D.complement)
    (χ : DivisorChart n X D.carrier p) (x : D.complement) {z : E n}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E n) x).target)
    (hy : (chartAt (E n) (x : X)).symm z ∈ χ.coord.source) (v : E n) :
    ω₀.toFormField.chartRep x z ![v, Complex.I • v] / 2 =
      metricQuadraticInAdaptedChart D ω₀ χ (χ.coord ((chartAt (E n) (x : X)).symm z))
        (χ.coord.map_source hy) (χ.coord_chartAt_symm_ne_zero x hz hy)
        (fderiv ℂ (χ.coord ∘ (chartAt (E n) (x : X)).symm) z v) := by
  rw [chartRep_eq_formInHolChart ω₀ x hz]
  exact metricQuadraticInHolChart_change (c₁ := HolChart.ofChartAt (x : X))
    (c₂ := χ.toHolChart) (mem_chartAt_target_of_opens x hz) _ (χ.coord.map_source hy) _
    (χ.coord.left_inv hy).symm v

/-- For the coordinate hyperplane, whose identity chart is the selected chart, `metricInAdaptedChart`
and `metricInChart` agree for every Kähler form on `ℂⁿ \ {z_0 = 0}`. -/
theorem metricInAdaptedChart_coordHyperplane_eq_metricInChart
    (ω₀ : KahlerForm n (coordHyperplane n).complement) (p : E n)
    (x : (coordHyperplane n).complement) {z : E n}
    (hz : z ∈ (coordHyperplaneChart n p).coord.target) (haway : z 0 ≠ 0) :
    metricInAdaptedChart (coordHyperplane n) ω₀ (coordHyperplaneChart n p) z hz haway =
      ω₀.metricInChart x z :=
  metricInAdaptedChart_eq_metricInChart ω₀ _ x (by simp [chartAt_self_eq]) hz haway

end Adapted

end ConicalKahler
