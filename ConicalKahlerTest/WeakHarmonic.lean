module

public import ConicalKahler

/-!
# Tests for Milestone 11: weak harmonic functions on the models

The model `C(S¹_{4π/3}) × ℝ` (`β = 2/3`, so `r^{1/β} cos θ = r^{3/2} cos θ` has degree `≤ 2` and
belongs to the paper's list), with real coordinates `(x, y, s)` of `ℝ³`.
-/

namespace ConicalKahler.Test

open ConicalKahler ConicalKahler.Sobolev MeasureTheory
open scoped Real InnerProductSpace

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- One cone of angle `4π/3` (`β = 2/3`). -/
noncomputable def wCone : Fin 1 → ConeAngle := fun _ => ⟨2 / 3, by norm_num⟩

/-- A numbering of the three real coordinates `(x, y, s)`. -/
noncomputable def wCoords : RealConeIndex (Fin 1) (Fin 1) ≃ Fin 3 :=
  Fintype.equivFinOfCardEq (by simp)

theorem wCone_le_one : ∀ a, (wCone a).beta ≤ 1 := fun _ => by norm_num [wCone]

theorem wCone_half_le : 1 / 2 ≤ (wCone 0).beta := by norm_num [wCone]

/-- **Removability of the singular set**: a function `C¹` off `{r = 0}` with `u, ∇u ∈ L²(B_1)` is
in `W^{1,2}(B_1)`. -/
example {u : ℝ³ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Metric.ball 0 1 \ coneSingular wCoords))
    (hu2 : MemLp u 2 (volume.restrict (Metric.ball (0 : ℝ³) 1)))
    (hg2 : MemLp (gradient u) 2 (volume.restrict (Metric.ball (0 : ℝ³) 1))) :
    classicalPair hu2 hg2 ∈ W12 volume (Metric.ball (0 : ℝ³) 1) :=
  classicalPair_mem_W12 wCoords Metric.isOpen_ball hu hu2 hg2

/-- **Classical solutions are weak solutions** for the cone Laplacian on `B_1`. -/
example {u f : ℝ³ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Metric.ball 0 1 \ coneSingular wCoords))
    (hu2 : MemLp u 2 (volume.restrict (Metric.ball (0 : ℝ³) 1)))
    (hg2 : MemLp (gradient u) 2 (volume.restrict (Metric.ball (0 : ℝ³) 1)))
    (hf : MemLp f 2 (volume.restrict (Metric.ball (0 : ℝ³) 1)))
    (hΔ : ∀ c : PolarPoint (Fin 1) (Fin 1), (∀ a, 0 < c (.r a)) →
      coordIso wCoords c.toModel ∈ Metric.ball 0 1 →
      -paperLaplacian wCone (fun c' => u (coordIso wCoords c'.toModel)) c =
        f (coordIso wCoords c.toModel)) :
    (coneCoeff wCone wCoords).IsWeakSolution (hf.toLp f) (classicalPair hu2 hg2) :=
  cone_isWeakSolution_of_classical wCone wCoords Metric.isOpen_ball hu hu2 hg2 hf hΔ

/-- **Conversely**, a weak solution that is `C²` off the singular set solves the equation
classically on the regular part. -/
example {u f : ℝ³ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Metric.ball 0 1 \ coneSingular wCoords))
    (hu2 : MemLp u 2 (volume.restrict (Metric.ball (0 : ℝ³) 1)))
    (hg2 : MemLp (gradient u) 2 (volume.restrict (Metric.ball (0 : ℝ³) 1)))
    (hf : MemLp f 2 (volume.restrict (Metric.ball (0 : ℝ³) 1)))
    (hfc : ContinuousOn f (Metric.ball 0 1 \ coneSingular wCoords))
    (hw : (coneCoeff wCone wCoords).IsWeakSolution (hf.toLp f) (classicalPair hu2 hg2))
    {c : PolarPoint (Fin 1) (Fin 1)} (hc : ∀ a, 0 < c (.r a))
    (hcB : coordIso wCoords c.toModel ∈ Metric.ball 0 1) :
    -paperLaplacian wCone (fun c' => u (coordIso wCoords c'.toModel)) c =
      f (coordIso wCoords c.toModel) :=
  cone_classical_of_isWeakSolution wCone wCoords Metric.isOpen_ball hu hu2 hg2 hf hfc hw hc hcB

/-- **`r^{3/2} cos θ` is weakly harmonic on `B_1`**, which contains the vertex. -/
example : ∃ (hu : _) (hg : _), (coneCoeff wCone wCoords).IsWeakSolution 0
    (classicalPair (Ω := Metric.ball (0 : ℝ³) 1)
      (u := fun x => harmCosFn (wCone 0).beta 1 0 ((coordIso wCoords).symm x)) hu hg) :=
  have h := isClassicalHarmonic_harmCos wCone (k := 1) (a := 0) (by norm_num [wCone])
  ⟨h.memLp wCoords Metric.isOpen_ball Metric.isBounded_ball,
    h.memLp_gradient wCoords Metric.isOpen_ball Metric.isBounded_ball,
    h.isWeakSolution wCoords Metric.isOpen_ball Metric.isBounded_ball⟩

/-- **`r^3 sin 2θ` (the next mode) is weakly harmonic on `B_2`.** -/
example : ∃ (hu : _) (hg : _), (coneCoeff wCone wCoords).IsWeakSolution 0
    (classicalPair (Ω := Metric.ball (0 : ℝ³) 2)
      (u := fun x => harmSinFn (wCone 0).beta 2 0 ((coordIso wCoords).symm x)) hu hg) :=
  have h := isClassicalHarmonic_harmSin wCone (k := 2) (a := 0) (by norm_num [wCone])
  ⟨h.memLp wCoords Metric.isOpen_ball Metric.isBounded_ball,
    h.memLp_gradient wCoords Metric.isOpen_ball Metric.isBounded_ball,
    h.isWeakSolution wCoords Metric.isOpen_ball Metric.isBounded_ball⟩

/-- **`r² − 2 s²` is in the paper's list and is weakly harmonic** on every bounded open set. -/
example {Ω : Set ℝ³} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∃ (hu : _) (hg : _), (coneCoeff wCone wCoords).IsWeakSolution 0
      (classicalPair (Ω := Ω)
        (u := fun x => (fun y : RealConeModel (Fin 1) (Fin 1) =>
          ‖y.cone 0‖ ^ 2 - 2 * y.eucl 0 ^ 2) ((coordIso wCoords).symm x)) hu hg) :=
  isWeakSolution_of_mem_explicitH2 wCone_le_one (rsq_sub_two_ssq_mem_explicitH2 0 0) wCoords hΩ hb

/-- The paper's list spans a finite-dimensional space. -/
example : FiniteDimensional ℝ (explicitH2 (ι := Fin 1) wCone) := inferInstance

/-- **Corollary 3.5** on `C(S¹_{4π/3}) × ℝ`: the conical Laplacian `Δ_β` of every element of the
paper's list is a constant `τ`, with `|τ| ≤ C ‖P‖_{L²(B_1)}`. -/
example : ∃ C, ∀ P ∈ explicitH2 (ι := Fin 1) wCone, ∃ τ : ℝ,
    (∀ c ∈ regularPolar (Fin 1) (Fin 1), (D2Op.lap (β := wCone) (ι := Fin 1) 0).apply
      (fun c' => P c'.toModel) c = τ) ∧
    |τ| ≤ C * Real.sqrt (∫ y in Metric.ball (0 : RealConeModel (Fin 1) (Fin 1)) 1, P y ^ 2) :=
  corollary_3_5 wCone_le_one _

/-- `∂²_s (r^{3/2} cos θ)`, `∂²/∂r∂s` of it, etc. are constant (zero): the cone factor with
`β ≥ 1/2` is annihilated by `𝒟₂`. -/
example (D : D2Op wCone (Fin 1)) : ∃ τ, ∀ c ∈ regularPolar (Fin 1) (Fin 1),
    D.apply (fun c' => harmCosFn (wCone 0).beta 1 0 c'.toModel) c = τ :=
  corollary_3_5_const (harmCos_mem_explicitH2 wCone_half_le) D

/-- **Energy uniqueness** (the replacement for the maximum principle in Lemma 3.3): a weakly
harmonic function in `W^{1,2}_0(B_1)` vanishes. -/
example {v : L2Pair volume (Metric.ball (0 : ℝ³) 1)}
    (hv : (coneCoeff wCone wCoords).IsWeakSolution 0 v) (h0 : v ∈ H01 volume (Metric.ball 0 1)) :
    v = 0 :=
  eq_zero_of_isWeakSolution_zero_of_mem_H01 _ zero_le_one Metric.ball_subset_closedBall hv h0

/-- **Symmetry of the Dirichlet problem** on `B_1`: if `f` is invariant under the rotation of the
cone factor by `t`, so is the solution in `W^{1,2}_0(B_1)`. -/
example (t : ℝ) {f : Lp ℝ 2 (volume.restrict (Metric.ball (0 : ℝ³) 1))}
    (hf : isoLp (rotE wCoords 0 t) ℝ measurableSet_ball (rotE_preimage_ball wCoords 0 t 1) f = f)
    {v : L2Pair volume (Metric.ball (0 : ℝ³) 1)}
    (hv : (coneCoeff wCone wCoords).IsWeakSolution f v) (h0 : v ∈ H01 volume (Metric.ball 0 1)) :
    (fun x => v.fst (rotE wCoords 0 t x)) =ᵐ[volume.restrict (Metric.ball (0 : ℝ³) 1)] v.fst :=
  cone_dirichlet_rot_invariant_ae wCone wCoords 0 t measurableSet_ball
    (rotE_preimage_ball wCoords 0 t 1) zero_le_one Metric.ball_subset_closedBall hf hv h0

theorem ball_rot_invariant (t : ℝ) :
    rotE wCoords 0 t ⁻¹' Metric.ball (0 : ℝ³) 1 = Metric.ball 0 1 :=
  rotE_preimage_ball wCoords 0 t 1

/-- **The Fourier modes in `θ` of a weakly harmonic function on `B_1` are weakly harmonic.** -/
example (k : ℕ) {v : L2Pair volume (Metric.ball (0 : ℝ³) 1)}
    (hv : (coneCoeff wCone wCoords).IsWeakSolution 0 v) :
    (coneCoeff wCone wCoords).IsWeakSolution 0
      (cosCoeff k fun t => rotPair wCoords 0 measurableSet_ball ball_rot_invariant t v) :=
  isWeakSolution_zero_angMode wCoords 0 measurableSet_ball ball_rot_invariant wCone
    (continuous_cos_mul k) hv

/-- **The modes transform like `cos kθ` and `sin kθ`.** -/
example (k : ℕ) (s : ℝ) (f : Lp ℝ 2 (volume.restrict (Metric.ball (0 : ℝ³) 1))) :
    rotLp wCoords 0 measurableSet_ball ball_rot_invariant ℝ s
        (cosCoeff k fun t => rotLp wCoords 0 measurableSet_ball ball_rot_invariant ℝ t f) =
      Real.cos (k * s) • cosCoeff k (fun t =>
          rotLp wCoords 0 measurableSet_ball ball_rot_invariant ℝ t f) +
        Real.sin (k * s) • sinCoeff k (fun t =>
          rotLp wCoords 0 measurableSet_ball ball_rot_invariant ℝ t f) :=
  rotLp_cosCoeff wCoords 0 measurableSet_ball ball_rot_invariant k s f

/-- **A weakly harmonic function on `B_1` is determined by its Fourier modes in `θ`.** -/
example {v : L2Pair volume (Metric.ball (0 : ℝ³) 1)}
    (hc : ∀ k : ℕ,
      (cosCoeff k fun t => rotPair wCoords 0 measurableSet_ball ball_rot_invariant t v).fst = 0)
    (hs : ∀ k : ℕ,
      (sinCoeff k fun t => rotPair wCoords 0 measurableSet_ball ball_rot_invariant t v).fst = 0) :
    v.fst = 0 :=
  eq_zero_of_harmonic_modes_eq_zero wCoords 0 measurableSet_ball ball_rot_invariant hc hs

/-- `Δ_β (r²) = 4` in the paper's normalisation, and `Δ (s s) = 2`. -/
example {c : PolarPoint (Fin 1) (Fin 1)} (hc : 0 < c (.r 0)) :
    paperLaplacian wCone (fun c' => c' (.r 0) ^ 2) c = 4 :=
  paperLaplacian_r_sq wCone 0 hc

end ConicalKahler.Test
