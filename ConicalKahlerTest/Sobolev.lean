module

public import ConicalKahler

/-!
# Tests for Milestone 9: Sobolev spaces and weak solutions on the real cone models

The model `C(S¹_π) × ℝ` (one cone of angle `π`, `β = 1/2`, and one Euclidean line), in the real
coordinates `ℝ³`.
-/

namespace ConicalKahler.Test

open ConicalKahler ConicalKahler.Sobolev MeasureTheory
open scoped Real InnerProductSpace

/-- One cone of angle `π`. -/
noncomputable def halfCone : Fin 1 → ConeAngle := fun _ => ⟨1 / 2, by norm_num⟩

/-- A numbering of the three real coordinates `(x, y, s)`. -/
noncomputable def coords3 : RealConeIndex (Fin 1) (Fin 1) ≃ Fin 3 :=
  Fintype.equivFinOfCardEq (by simp)

/-- The ellipticity constants of `g⁻¹` for `β = 1/2`: `λ = 4/5`, `Λ = 5`. -/
example : coneLam halfCone = 4 / 5 := by norm_num [coneLam, halfCone]
example : coneΛ halfCone = 5 := by norm_num [coneΛ, halfCone]

/-- In the paper's range `β ≤ 1` one can take `λ = 1`: `|v|² ≤ ⟨g⁻¹ v, v⟩` almost everywhere. -/
example : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), ∀ v,
    ‖v‖ ^ 2 ≤ ⟪(coneCoeff halfCone coords3).A x v, v⟫_ℝ :=
  coneCoeff_coercive_of_le_one (fun _ => by norm_num [halfCone]) coords3

/-- The inverse metric is the inverse of the metric: `G(β) G(1/β) = 1` on the regular part. -/
example {p : RealConeModel (Fin 1) (Fin 1)} (hp : ∀ a, p.cone a ≠ 0) :
    productConeGram halfCone p * productConeGram (invAngles halfCone) p = 1 :=
  productConeGram_mul_inv halfCone hp

/-- **Existence and uniqueness** on the unit ball `B_1 ⊆ C(S¹_π) × ℝ` for every `f ∈ L²(B_1)`. -/
example (f : Lp ℝ 2 (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1))) :
    ∃! v : H01 volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1),
      (coneCoeff halfCone coords3).IsWeakSolution f v :=
  cone_existsUnique_H01 halfCone coords3 zero_le_one Metric.ball_subset_closedBall f

/-- The zero function solves the homogeneous problem. -/
example (Ω : Set (EuclideanSpace ℝ (Fin 3))) :
    (coneCoeff halfCone coords3).IsWeakSolution 0 (0 : L2Pair volume Ω) :=
  ⟨(W12 volume Ω).zero_mem, fun φ hφ => by simp⟩

/-- **Friedrichs–Poincaré** on `W^{1,2}_0(B_1)`: `‖u‖ ≤ 2 ‖∇u‖`. -/
example {v : L2Pair volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)}
    (hv : v ∈ H01 volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    ‖v.fst‖ ≤ 2 * 1 * ‖v.snd‖ :=
  norm_fst_le_of_mem_H01 zero_le_one Metric.ball_subset_closedBall hv

/-- **Caccioppoli** for the cone Laplacian on `B_1`. -/
example {f : Lp ℝ 2 (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1))}
    {v : L2Pair volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)}
    (hv : (coneCoeff halfCone coords3).IsWeakSolution f v) {η : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hη : IsTestFn (Metric.ball 0 1) η) :
    ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
        η x ^ 2 * ⟪coneCoeffA halfCone coords3 x (v.snd x), v.snd x⟫_ℝ ≤
      (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1, η x ^ 2 * f x ^ 2) +
        ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
          (η x ^ 2 + 4 * coneΛ halfCone * ‖gradient η x‖ ^ 2) * v.fst x ^ 2 :=
  cone_caccioppoli halfCone coords3 Metric.isOpen_ball hv hη

/-- **Density:** test functions supported off the axis `{r = 0}` are dense in `W^{1,2}_0(B_1)`. -/
example : (testSubmodule volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (Metric.ball 0 1 \ coneSingular coords3)).topologicalClosure =
    H01 volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  dense_testSubmodule_regular coords3 _

/-- The logarithmic cut-offs: `h_n = 0` near `0` and `h_n = 1` for `t ≥ e^{-n}`. -/
example : logCut 3 (Real.exp (-3)) = 1 := logCut_eq_one (by norm_num) (by norm_num)
example : logCut 3 (Real.exp (-7)) = 0 :=
  logCut_eq_zero (by norm_num) (Real.exp_lt_exp.mpr (by norm_num))

end ConicalKahler.Test
