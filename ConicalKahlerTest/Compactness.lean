module

public import ConicalKahler

/-!
# Tests for Milestone 10: compactness, harmonic approximation, scaling, spectral theory

The model `C(S¹_π) × ℝ` (`piCone`, real coordinates `coordsR3` of `ℝ³`).
-/

namespace ConicalKahler.Test

open ConicalKahler ConicalKahler.Sobolev MeasureTheory
open scoped Real InnerProductSpace

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- One cone of angle `π`. -/
noncomputable def piCone : Fin 1 → ConeAngle := fun _ => ⟨1 / 2, by norm_num⟩

/-- A numbering of the three real coordinates `(x, y, s)`. -/
noncomputable def coordsR3 : RealConeIndex (Fin 1) (Fin 1) ≃ Fin 3 :=
  Fintype.equivFinOfCardEq (by simp)

/-- **Rellich**: `W^{1,2}_0(B_1) ↪ L²(B_1)` is compact. -/
example : IsCompactOperator (H01.fstL (Metric.ball (0 : ℝ³) 1)) :=
  isCompactOperator_H01_fst Metric.isOpen_ball Metric.isBounded_ball

/-- **Lemma 2.4 with an explicit threshold** on `B_1`: `δ = λ ε / 5` (here `R = 1`), for the cone
Laplacian, with no bound on `u` needed. -/
example {ε : ℝ} {f : Lp ℝ 2 (volume.restrict (Metric.ball (0 : ℝ³) 1))}
    {v : L2Pair volume (Metric.ball (0 : ℝ³) 1)}
    (hv : (coneCoeff piCone coordsR3).IsWeakSolution f v)
    (hf : ‖f‖ < coneLam piCone * ε / (4 * 1 ^ 2 + 1)) :
    ∃ h : L2Pair volume (Metric.ball (0 : ℝ³) 1),
      (coneCoeff piCone coordsR3).IsWeakSolution 0 h ∧ ‖v.fst - h.fst‖ < ε :=
  CoeffField.harmonic_approximation zero_le_one Metric.ball_subset_closedBall hv hf

/-- **Lemma 2.4 on cone balls `B(p, 1)`, with `δ` independent of the centre `p`.** -/
example {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (p : RealConeModel (Fin 1) (Fin 1))
      (f : Lp ℝ 2 (volume.restrict (coneBall piCone coordsR3 p 1)))
      (v : L2Pair volume (coneBall piCone coordsR3 p 1)),
      (coneCoeff piCone coordsR3).IsWeakSolution f v → ‖f‖ < δ →
      ∃ h : L2Pair volume (coneBall piCone coordsR3 p 1),
        (coneCoeff piCone coordsR3).IsWeakSolution 0 h ∧ ‖v.fst - h.fst‖ < ε :=
  cone_harmonic_approximation piCone coordsR3 zero_le_one hε

/-- **Compactness of approximate solutions** (the paper's argument for Lemma 2.4): a bounded
sequence of weak solutions on `B_1` with `f_n → 0` has a subsequence converging in
`W^{1,2}(B_{1/2})` to a weakly harmonic function. -/
example {f : ℕ → Lp ℝ 2 (volume.restrict (Metric.ball (0 : ℝ³) 1))}
    {v : ℕ → L2Pair volume (Metric.ball (0 : ℝ³) 1)}
    (hv : ∀ n, (coneCoeff piCone coordsR3).IsWeakSolution (f n) (v n))
    (hM : ∀ n, ‖(v n).fst‖ ≤ 1) (hf : Filter.Tendsto f Filter.atTop (nhds 0)) :
    ∃ hsub : Metric.ball (0 : ℝ³) (1 / 2) ⊆ Metric.ball 0 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ w : L2Pair volume (Metric.ball (0 : ℝ³) (1 / 2)),
        (coneCoeff piCone coordsR3).IsWeakSolution 0 w ∧
        Filter.Tendsto (fun k => L2Pair.restrict hsub (v (φ k))) Filter.atTop (nhds w) := by
  have hcl : closure (Metric.ball (0 : ℝ³) (1 / 2)) ⊆ Metric.ball 0 1 :=
    Metric.closure_ball_subset_closedBall.trans
      (Metric.closedBall_subset_ball (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨φ, hφ, w, hw, hlim⟩ := exists_tendsto_of_approx_solutions (coneCoeff piCone coordsR3)
    Metric.isOpen_ball Metric.isBounded_ball Metric.isOpen_ball
    Metric.isBounded_ball.isCompact_closure hcl hv hM hf
  have h0 : restrictLp (E := ℝ) (μ := volume) (subset_closure.trans hcl) 0 = 0 := map_zero _
  rw [h0] at hw
  exact ⟨subset_closure.trans hcl, φ, hφ, w, hw, hlim⟩

/-- **The divergence-form operator is the paper's Laplacian** at regular points. -/
example {u : RealConeModel (Fin 1) (Fin 1) → ℝ} {c : PolarPoint (Fin 1) (Fin 1)}
    (hc : ∀ a, 0 < c (.r a)) (hu : ContDiffAt ℝ 2 u c.toModel) :
    divergence (fun y => coneInvOp piCone y (gradient u y)) c.toModel =
      paperLaplacian piCone (fun c' => u c'.toModel) c :=
  divergence_coneInvOp_gradient piCone hc hu

/-- **Norm equivalence**: for `β = 1/2 ≤ 1`, `(1/2) ‖(u, G)‖² ≤ ∫ (u² + |∇_g u|²_g) dV_g`. -/
example {Ω : Set ℝ³} (v : L2Pair volume Ω) :
    (∏ a, (piCone a).beta) * ‖v‖ ^ 2 ≤ intrinsicNormSq piCone coordsR3 v :=
  intrinsicNormSq_lower_of_le_one (fun _ => by norm_num [piCone]) coordsR3 v

/-- **The cone coefficients are dilation invariant.** -/
example {t : ℝ} (ht : t ≠ 0) (x : ℝ³) :
    coneCoeffA piCone coordsR3 (t • x) = coneCoeffA piCone coordsR3 x :=
  coneCoeffA_smul piCone coordsR3 ht x

/-- **The scaled Caccioppoli inequality** for the cone Laplacian on Euclidean balls of any centre
and radius (with a universal constant `Γ`). -/
example : ∃ Γ : ℝ, 0 ≤ Γ ∧ ∀ {Ω : Set ℝ³} (_ : IsOpen Ω) (p : ℝ³) {ρ : ℝ} (_ : 0 < ρ)
    (_ : Metric.ball p (2 * ρ) ⊆ Ω) {f : Lp ℝ 2 (volume.restrict Ω)} {v : L2Pair volume Ω}
    (_ : (coneCoeff piCone coordsR3).IsWeakSolution f v),
    coneLam piCone * ∫ x in Metric.ball p ρ, ‖v.snd x‖ ^ 2 ≤
      ρ ^ 2 * (∫ x in Metric.ball p (2 * ρ), f x ^ 2) + (1 + 4 * coneΛ piCone * Γ ^ 2) / ρ ^ 2 *
        ∫ x in Metric.ball p (2 * ρ), v.fst x ^ 2 := by
  obtain ⟨Γ, hΓ, h⟩ := exists_caccioppoli_ball_scaled (d := 3)
  exact ⟨Γ, hΓ, fun hΩ p ρ hρ hp f v hv =>
    h (coneCoeff piCone coordsR3) (fun t ht x => coneCoeffA_smul piCone coordsR3 ht.ne' x) hΩ p
      hρ hp hv⟩

/-- **The spectral theorem for the Dirichlet problem** on `B_1`: the eigenspaces of the solution
operator span a dense subspace of `L²(B_1)`. -/
example : (⨆ μ, Module.End.eigenspace
      (((coneCoeff piCone coordsR3).dirichletG zero_le_one
        (Metric.ball_subset_closedBall (x := (0 : ℝ³)) (ε := 1)) :
        Lp ℝ 2 (volume.restrict (Metric.ball (0 : ℝ³) 1)) →L[ℝ]
          Lp ℝ 2 (volume.restrict (Metric.ball (0 : ℝ³) 1))) :
        Module.End ℝ (Lp ℝ 2 (volume.restrict (Metric.ball (0 : ℝ³) 1)))) μ)ᗮ = ⊥ :=
  (coneCoeff piCone coordsR3).dirichletG_eigenspaces_dense zero_le_one
    Metric.ball_subset_closedBall Metric.isOpen_ball

/-- **Dirichlet eigenvalues on `B_1` are at least `λ/4`.** -/
example {μ : ℝ} {f : Lp ℝ 2 (volume.restrict (Metric.ball (0 : ℝ³) 1))} (hf : f ≠ 0)
    (hGf : (coneCoeff piCone coordsR3).dirichletG zero_le_one Metric.ball_subset_closedBall f =
      μ • f) : 0 < μ ∧ coneLam piCone * μ ≤ 4 * 1 ^ 2 :=
  let h := (coneCoeff piCone coordsR3).dirichletG_eigen zero_le_one Metric.ball_subset_closedBall
    Metric.isOpen_ball hf hGf
  ⟨h.1, h.2.1⟩

end ConicalKahler.Test
