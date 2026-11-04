module

public import ConicalKahler.Cone.Weights
public import CalabiYau.Geometry.Complex.Basic

/-!
# Holomorphic charts not in the selected atlas

A `HolChart n X` is a biholomorphism `coord` between an open subset of `X` and an open subset of
`ℂⁿ`. It is holomorphic with holomorphic inverse, but it need not be the chart selected by
`chartAt`. Divisor charts (`DivisorChart`), SNC charts (`SNCChart`) and the selected charts
themselves (`HolChart.ofChartAt`) are all holomorphic charts. Pulling back a Kähler form along a
`HolChart` (`formInHolChart`, in `ConicalKahler.Cone.ChartMetric`) therefore serves all of them.

## Main declarations

* `HolChart.toChartAt c y = extChartAt y ∘ c⁻¹`: transition to the selected chart at `y`.
  `contDiffAt_toChartAt` says it is holomorphic, and `injective_fderiv_toChartAt` that its
  derivative is injective.
* `HolChart.contDiffAt_transition`: `c₂ ∘ c₁⁻¹` is holomorphic near every common point.
* `HolChart.ofChartAt x`: the selected chart at `x`, as a holomorphic chart.
* `HolChart.restrOpen`: restriction to an open subset.
* `HolChart.transCLE`: post-composition with a complex-linear automorphism of `ℂⁿ`, for example
  the coordinate swap `swapCoord a b`. `HolChart.refl`: the identity chart of `ℂⁿ`.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Set Filter

namespace ConicalKahler

/-- A **holomorphic chart** of `X`: a biholomorphism between an open subset of `X` and an open
subset of `ℂⁿ`. It need not belong to the atlas selected by `ChartedSpace`. -/
structure HolChart (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace (E n) X] where
  /-- The coordinate map. -/
  coord : OpenPartialHomeomorph X (E n)
  holomorphic : ContMDiffOn 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ coord coord.source
  inverse_holomorphic : ContMDiffOn 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ coord.symm coord.target

namespace HolChart

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X]

/-- Holomorphic charts are determined by their coordinate maps. -/
theorem ext' {c₁ c₂ : HolChart n X} (h : c₁.coord = c₂.coord) : c₁ = c₂ := by
  cases c₁
  cases c₂
  subst h
  rfl

/-- Restrict a holomorphic chart to an open subset `s`. -/
noncomputable def restrOpen (c : HolChart n X) (s : Set X) (hs : IsOpen s) : HolChart n X where
  coord := c.coord.restrOpen s hs
  holomorphic := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact c.holomorphic.mono inter_subset_left
  inverse_holomorphic :=
    c.inverse_holomorphic.mono fun _ hz => hz.1

/-- Post-compose a holomorphic chart with a complex-linear automorphism `L` of `ℂⁿ`. -/
noncomputable def transCLE (c : HolChart n X) (L : E n ≃L[ℂ] E n) : HolChart n X where
  coord := c.coord.transHomeomorph L.toHomeomorph
  holomorphic := by
    have hL : ContMDiff 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ L := L.contDiff.contMDiff
    exact hL.comp_contMDiffOn c.holomorphic
  inverse_holomorphic := by
    have hL : ContMDiff 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ L.symm := L.symm.contDiff.contMDiff
    exact c.inverse_holomorphic.comp hL.contMDiffOn (fun _ hz => hz)

@[simp]
theorem transCLE_coord_apply (c : HolChart n X) (L : E n ≃L[ℂ] E n) (x : X) :
    (c.transCLE L).coord x = L (c.coord x) :=
  rfl

@[simp]
theorem transCLE_coord_source (c : HolChart n X) (L : E n ≃L[ℂ] E n) :
    (c.transCLE L).coord.source = c.coord.source :=
  rfl

/-- The transition `extChartAt y ∘ c⁻¹` from `c`-coordinates to the selected chart at `y`. -/
noncomputable def toChartAt (c : HolChart n X) (y : X) : E n → E n :=
  extChartAt 𝓘(ℂ, E n) y ∘ c.coord.symm

/-- The transition `c ∘ (extChartAt y)⁻¹` from the selected chart at `y` to `c`-coordinates. -/
noncomputable def fromChartAt (c : HolChart n X) (y : X) : E n → E n :=
  c.coord ∘ (extChartAt 𝓘(ℂ, E n) y).symm

theorem contDiffAt_toChartAt (c : HolChart n X) {z : E n} (hz : z ∈ c.coord.target) :
    ContDiffAt ℂ ∞ (c.toChartAt (c.coord.symm z)) z := by
  have h1 : ContMDiffAt 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ c.coord.symm z :=
    c.inverse_holomorphic.contMDiffAt (c.coord.open_target.mem_nhds hz)
  have h2 : ContMDiffAt 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ (extChartAt 𝓘(ℂ, E n) (c.coord.symm z))
      (c.coord.symm z) :=
    contMDiffAt_extChartAt
  exact contMDiffAt_iff_contDiffAt.mp (h2.comp z h1)

theorem fromChartAt_comp_toChartAt (c : HolChart n X) {z : E n} (hz : z ∈ c.coord.target) :
    c.fromChartAt (c.coord.symm z) ∘ c.toChartAt (c.coord.symm z) =ᶠ[𝓝 z] id := by
  have hsrc : ∀ᶠ w in 𝓝 z,
      c.coord.symm w ∈ (extChartAt 𝓘(ℂ, E n) (c.coord.symm z)).source :=
    (c.coord.continuousAt_symm hz).preimage_mem_nhds
      ((isOpen_extChartAt_source (c.coord.symm z)).mem_nhds (mem_extChartAt_source _))
  filter_upwards [hsrc, c.coord.open_target.mem_nhds hz] with w hw hwt
  simp only [Function.comp_apply, fromChartAt, toChartAt, id]
  rw [(extChartAt 𝓘(ℂ, E n) _).left_inv hw, c.coord.right_inv hwt]

theorem fderiv_real_toChartAt (c : HolChart n X) {z : E n} (hz : z ∈ c.coord.target) :
    fderiv ℝ (c.toChartAt (c.coord.symm z)) z =
      (fderiv ℂ (c.toChartAt (c.coord.symm z)) z).restrictScalars ℝ :=
  ((c.contDiffAt_toChartAt hz).differentiableAt (by simp)).fderiv_restrictScalars ℝ

/-- Two holomorphic charts are related by a holomorphic transition `c₂ ∘ c₁⁻¹` near any common
point. -/
theorem contDiffAt_transition (c₁ c₂ : HolChart n X) {z₁ : E n} (hz₁ : z₁ ∈ c₁.coord.target)
    (h₂ : c₁.coord.symm z₁ ∈ c₂.coord.source) :
    ContDiffAt ℂ ∞ (c₂.coord ∘ c₁.coord.symm) z₁ := by
  have h1 : ContMDiffAt 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ c₁.coord.symm z₁ :=
    c₁.inverse_holomorphic.contMDiffAt (c₁.coord.open_target.mem_nhds hz₁)
  have h2 : ContMDiffAt 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ c₂.coord (c₁.coord.symm z₁) :=
    c₂.holomorphic.contMDiffAt (c₂.coord.open_source.mem_nhds h₂)
  exact contMDiffAt_iff_contDiffAt.mp (h2.comp z₁ h1)

variable [IsManifold 𝓘(ℂ, E n) ω X]

theorem contDiffAt_fromChartAt (c : HolChart n X) {y : X} (hy : y ∈ c.coord.source) :
    ContDiffAt ℂ ∞ (c.fromChartAt y) (extChartAt 𝓘(ℂ, E n) y y) := by
  have h1 : ContMDiffAt 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ (extChartAt 𝓘(ℂ, E n) y).symm
      (extChartAt 𝓘(ℂ, E n) y y) :=
    (contMDiffOn_extChartAt_symm y).contMDiffAt
      ((isOpen_extChartAt_target y).mem_nhds (mem_extChartAt_target y))
  have h2 : ContMDiffAt 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ c.coord y :=
    c.holomorphic.contMDiffAt (c.coord.open_source.mem_nhds hy)
  exact contMDiffAt_iff_contDiffAt.mp
    (h2.comp_of_eq h1 ((extChartAt 𝓘(ℂ, E n) y).left_inv (mem_extChartAt_source y)))

/-- The derivative of the transition to the selected chart has a left inverse. -/
theorem fderiv_fromChartAt_comp_fderiv_toChartAt (c : HolChart n X) {z : E n}
    (hz : z ∈ c.coord.target) :
    (fderiv ℂ (c.fromChartAt (c.coord.symm z))
        (c.toChartAt (c.coord.symm z) z)).comp (fderiv ℂ (c.toChartAt (c.coord.symm z)) z) =
      ContinuousLinearMap.id ℂ (E n) := by
  have hτ : DifferentiableAt ℂ (c.toChartAt (c.coord.symm z)) z :=
    (c.contDiffAt_toChartAt hz).differentiableAt (by simp)
  have hσ : DifferentiableAt ℂ (c.fromChartAt (c.coord.symm z))
      (c.toChartAt (c.coord.symm z) z) :=
    (c.contDiffAt_fromChartAt (c.coord.map_target hz)).differentiableAt (by simp)
  rw [← fderiv_comp z hσ hτ, (c.fromChartAt_comp_toChartAt hz).fderiv_eq, fderiv_id]

theorem injective_fderiv_toChartAt (c : HolChart n X) {z : E n} (hz : z ∈ c.coord.target) :
    Function.Injective (fderiv ℂ (c.toChartAt (c.coord.symm z)) z) := by
  intro a b hab
  have h := congrArg (fderiv ℂ (c.fromChartAt (c.coord.symm z))
    (c.toChartAt (c.coord.symm z) z)) hab
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
    c.fderiv_fromChartAt_comp_fderiv_toChartAt hz] at h
  simpa using h

/-- **The selected chart at `x` is a holomorphic chart.** -/
noncomputable def ofChartAt (x : X) : HolChart n X where
  coord := chartAt (E n) x
  holomorphic := contMDiffOn_chart
  inverse_holomorphic := contMDiffOn_chart_symm

@[simp]
theorem ofChartAt_coord (x : X) : (ofChartAt (n := n) x).coord = chartAt (E n) x :=
  rfl

end HolChart

/-- The identity chart of `ℂⁿ`. -/
noncomputable def HolChart.refl (n : ℕ) : HolChart n (E n) where
  coord := OpenPartialHomeomorph.refl (E n)
  holomorphic := contMDiffOn_id
  inverse_holomorphic := contMDiffOn_id

/-- The linear automorphism of `ℂⁿ` exchanging the coordinates `a` and `b`. -/
noncomputable def swapCoord {n : ℕ} (a b : Fin n) : E n ≃L[ℂ] E n :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.swap a b)).toContinuousLinearEquiv

@[simp]
theorem swapCoord_apply {n : ℕ} (a b : Fin n) (z : E n) (i : Fin n) :
    swapCoord a b z i = z (Equiv.swap a b i) := by
  simp [swapCoord]

end ConicalKahler
