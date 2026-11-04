module

public import ConicalKahler.Analysis.DDBarLocal
public import CalabiYau.Geometry.Complex.Basic

/-!
# Open subsets of `ℂⁿ` as complex manifolds

An open subset `U : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))` carries Mathlib's induced
open-submanifold atlas (`TopologicalSpace.Opens.instChartedSpace`), whose chart at `x` is the
restriction of the identity chart of `ℂⁿ`. In particular every chart of `U` is the inclusion
`U ↪ ℂⁿ`. This file records the consequences needed to build Kähler forms on `U` out of functions
on `ℂⁿ`:

* `extChartAt_opens_apply`, `extChartAt_opens_symm_val`, `extChartAt_opens_target_subset`;
* `contMDiff_opens_of_contDiffOn`: a function smooth on `U ⊆ ℂⁿ` restricts to a smooth function on
  the manifold `U`;
* `mddbar_opens`, `chartRep_mddbar_opens`: `i∂∂̄` of the restriction of `f` is `ddbar f`, both at
  the centre of the chart and in the coordinate representation on the whole chart target.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Filter Set

namespace ConicalKahler

variable {n : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n)))

/-- The extended chart of `U` at `x` is the inclusion. -/
theorem extChartAt_opens_apply (x y : U) :
    extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y = (y : EuclideanSpace ℂ (Fin n)) := by
  simp [extChartAt, TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq,
    OpenPartialHomeomorph.subtypeRestr_def]

/-- On the chart target, the inverse of the extended chart is the inverse of the inclusion. -/
theorem extChartAt_opens_symm_val (x : U) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z : U) : EuclideanSpace ℂ (Fin n)) =
      z := by
  have h := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).right_inv hz
  rwa [extChartAt_opens_apply] at h

theorem extChartAt_opens_target_subset (x : U) :
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target ⊆ (U : Set _) := by
  intro z hz
  rw [← extChartAt_opens_symm_val U x hz]
  exact ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z).2

/-- A function smooth on the open set `U ⊆ ℂⁿ` restricts to a smooth function on the manifold
`U`. -/
theorem contMDiff_opens_of_contDiffOn {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (fun y : U => f y) := by
  intro x
  apply contMDiffAt_subtype_iff.mpr
  exact contMDiffAt_iff_contDiffAt.mpr (hf.contDiffAt (U.isOpen.mem_nhds x.2))

/-- On `U ⊆ ℂⁿ`, the manifold `i∂∂̄` of the restriction of `f` is `ddbar f`. -/
theorem mddbar_opens (f : EuclideanSpace ℂ (Fin n) → ℝ) (x : U) :
    mddbar n (fun y : U => f y) x = ddbar f x := by
  have hc := U.chartAt_subtype_val_symm_eventuallyEq
    (H := EuclideanSpace ℂ (Fin n)) (x := x)
  have hg :
      (fun y : U => f y) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
      =ᶠ[𝓝 (x : EuclideanSpace ℂ (Fin n))] f := by
    have h := hc.symm.fun_comp f
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
      id_eq] at h
    simpa only [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_def, id_eq]
      using h
  unfold mddbar
  rw [extChartAt_opens_apply]
  exact ddbar_congr hg

variable {U}

/-- The coordinate representation of `i∂∂̄ (f|_U)` on the chart target is `ddbar f`. -/
theorem chartRep_mddbar_opens {f : EuclideanSpace ℂ (Fin n) → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (x : U) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (mddbar n (fun y : U => f y)).chartRep x z = ddbar f z := by
  rw [chartRep_mddbar (contMDiff_opens_of_contDiffOn U hf) x hz]
  apply ddbar_congr
  filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).mem_nhds hz]
    with w hw
  simp only [Function.comp_apply, extChartAt_opens_symm_val U x hw]

end ConicalKahler
