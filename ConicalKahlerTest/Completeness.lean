module

public import ConicalKahler

/-!
# Tests for Milestone 13: completeness of `𝓗_{≤2+α}` (Proposition 3.4)

The model `C(S¹_{4π/3}) × ℝ` (`β = 2/3`), with real coordinates `(x, y, s)` of `ℝ³`. Here
`1/β = 3/2`, so `r^{3/2} cos θ` has degree `3/2 ≤ 2`, the next angular degree is `3/2 + 1 = 5/2`,
and eq. (1.1) gives `μ = 1/β - 1 = 1/2`.
-/

namespace ConicalKahler.Test

open ConicalKahler ConicalKahler.Sobolev MeasureTheory Metric MvPolynomial
open scoped Real InnerProductSpace

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- One cone of angle `4π/3` (`β = 2/3`). -/
noncomputable def pCone : Fin 1 → ConeAngle := fun _ => ⟨2 / 3, by norm_num⟩

/-- A numbering of the three real coordinates `(x, y, s)`. -/
noncomputable def pCoords : RealConeIndex (Fin 1) (Fin 1) ≃ Fin 3 :=
  Fintype.equivFinOfCardEq (by simp)

theorem pCone_lt_one : ∀ a, (pCone a).beta < 1 := fun _ => by norm_num [pCone]

/-- The angular degree of `r^{1/β} cos θ` is `3/2`. -/
example : modeDeg pCone (Pi.single 0 1) = 3 / 2 := by
  rw [modeDeg_single]
  norm_num [pCone]

/-- `μ = 1/2` satisfies the hypotheses of eq. (1.1). -/
theorem pCone_mu : ∀ a, (1 / 2 : ℝ) ≤ holderExponentBound (pCone a).beta := fun _ => by
  norm_num [holderExponentBound, pCone]

/-- **The Fischer identity** `L_q(ρ² p) = ρ² L_q p + (4m + C₀) p`. -/
example (q : Fin 1 → ℝ) {p : MvPolynomial (Fin 1 ⊕ Fin 1) ℝ} {m : ℕ}
    (hp : IsWeightedHomogeneous polyWt p m) :
    formalLap q (rhoSq * p) = rhoSq * formalLap q p + C (4 * m + fischerConst (Fin 1) q) * p :=
  formalLap_rhoSq_mul q hp

/-- **The Fischer decomposition**: every polynomial is a combination of `ρ^{2j} h`, `L_q h = 0`. -/
example (k : Fin 1 → ℕ) (p : MvPolynomial (Fin 1 ⊕ Fin 1) ℝ) :
    p ∈ Submodule.span ℝ (harmonicGen (modeQ pCone k)) :=
  mem_span_harmonicGen _ (fischerConst_modeQ_pos pCone k ⟨Sum.inr 0⟩) p

/-- **Cone polynomials are homogeneous** of degree `∑ k_a/β_a + m`. -/
example (k : Fin 1 → ℕ) (ε : Fin 1 → Bool) {p : MvPolynomial (Fin 1 ⊕ Fin 1) ℝ} {m : ℕ}
    (hp : IsWeightedHomogeneous polyWt p m) {t : ℝ} (ht : 0 < t)
    (y : RealConeModel (Fin 1) (Fin 1)) :
    conePoly pCone k ε p (t • y) = t ^ (modeDeg pCone k + m) * conePoly pCone k ε p y :=
  conePoly_smul_point pCone k ε hp ht y

/-- **Harmonic cone polynomials are weakly harmonic** on `B_1`. -/
example (k : Fin 1 → ℕ) (ε : Fin 1 → Bool) {h : MvPolynomial (Fin 1 ⊕ Fin 1) ℝ}
    (hh : formalLap (modeQ pCone k) h = 0) :
    IsClassicalHarmonic pCone (conePoly (ι := Fin 1) pCone k ε h) :=
  isClassicalHarmonic_conePoly (fun a => (pCone_lt_one a).le) k ε hh

/-- **Cone polynomials are dense in `C(S²)`** (Stone–Weierstrass). -/
example : Dense (linkPolySpan pCone pCoords : Set C(Sph 3, ℝ)) := dense_linkPolySpan pCone pCoords

/-- **The harmonic cone polynomials span a dense subspace of `L²(S²)`.** -/
example : Dense (Submodule.span ℝ (⋃ D, harmConeLink pCone pCoords D) :
    Set (Lp ℝ 2 (sphMeasure 3))) :=
  dense_span_harmConeLink pCone pCoords

/-- **Homogeneous harmonic functions are harmonic cone polynomials.** -/
example {u : L2Pair volume (ball (0 : ℝ³) 1)} (hu : (coneCoeff pCone pCoords).IsWeakSolution 0 u)
    {δ : ℝ} (hδ : 0 ≤ δ) {φ : Lp ℝ 2 (sphMeasure 3)}
    (hφ : (u.fst : ℝ³ → ℝ) =ᵐ[volume.restrict (ball (0 : ℝ³) 1)] homFun δ fun w => φ w) :
    ∃ P ∈ Submodule.span ℝ (harmConePolys pCone δ),
      (u.fst : ℝ³ → ℝ) =ᵐ[volume.restrict (ball (0 : ℝ³) 1)]
        fun x => P ((coordIso pCoords).symm x) :=
  cone_homogeneous_mem_span (by norm_num) pCone (fun a => (pCone_lt_one a).le) pCoords hu hδ hφ

/-- **Proposition 3.4** on `C(S¹_{4π/3}) × ℝ`: homogeneous harmonic functions of degree `≤ 2` are
in the span of the paper's list, and there are none of degree in `(2, 5/2)`. -/
example {u : L2Pair volume (ball (0 : ℝ³) 1)} (hu : (coneCoeff pCone pCoords).IsWeakSolution 0 u)
    {δ : ℝ} (hδ : 0 ≤ δ) {φ : Lp ℝ 2 (sphMeasure 3)}
    (hφ : (u.fst : ℝ³ → ℝ) =ᵐ[volume.restrict (ball (0 : ℝ³) 1)] homFun δ fun w => φ w) :
    (δ ≤ 2 → ∃ P ∈ explicitH2 pCone,
      (u.fst : ℝ³ → ℝ) =ᵐ[volume.restrict (ball (0 : ℝ³) 1)]
        fun x => P ((coordIso pCoords).symm x)) ∧
    (2 < δ → δ < 5 / 2 → u.fst = 0) := by
  have h := prop_3_4 (by norm_num) pCone pCone_lt_one pCoords hu hδ hφ
  exact ⟨h.1, fun h2 h3 => h.2 (1 / 2) (by norm_num) pCone_mu h2 (by linarith)⟩

/-- **Lemma 3.3 with the gap**: every term of the expansion has degree `≤ 2` (and is in the
paper's list) or degree `≥ 5/2`. -/
example {u : L2Pair volume (ball (0 : ℝ³) 1)} (hu : (coneCoeff pCone pCoords).IsWeakSolution 0 u) :
    ∃ (s : Set (Lp ℝ 2 (sphMeasure 3))) (δ a : s → ℝ)
      (P : s → Lp ℝ 2 (volume.restrict (ball (0 : ℝ³) 1))),
      (∀ i, (δ i ≤ 2 ∧ ∃ Pe ∈ explicitH2 pCone,
          (P i : ℝ³ → ℝ) =ᵐ[volume.restrict (ball (0 : ℝ³) 1)]
            fun x => Pe ((coordIso pCoords).symm x)) ∨ 2 + 1 / 2 ≤ δ i) ∧
      HasSum (fun i => a i • P i) u.fst := by
  obtain ⟨s, δ, a, P, -, hgap, -, hsum⟩ :=
    cone_expansion_prop_3_4 (by norm_num) pCone pCone_lt_one pCoords (μ := 1 / 2) (by norm_num)
      pCone_mu hu
  exact ⟨s, δ, a, P, hgap, hsum⟩

/-- **Corollary 3.5 for `𝓗_{≤2}`**: `D P` is constant with `|τ| ≤ C ‖P‖_{L²(B_1)}`. -/
example (D : D2Op pCone (Fin 1)) :
    ∃ C, ∀ {u : L2Pair volume (ball (0 : ℝ³) 1)}, (coneCoeff pCone pCoords).IsWeakSolution 0 u →
      ∀ {δ : ℝ}, 0 ≤ δ → δ ≤ 2 → ∀ {φ : Lp ℝ 2 (sphMeasure 3)},
      ((u.fst : ℝ³ → ℝ) =ᵐ[volume.restrict (ball (0 : ℝ³) 1)] homFun δ fun w => φ w) →
      ∃ P ∈ explicitH2 pCone,
        ((u.fst : ℝ³ → ℝ) =ᵐ[volume.restrict (ball (0 : ℝ³) 1)]
          fun x => P ((coordIso pCoords).symm x)) ∧
        ∃ τ : ℝ, (∀ c ∈ regularPolar (Fin 1) (Fin 1), D.apply (fun c' => P c'.toModel) c = τ) ∧
          |τ| ≤ C * Real.sqrt (∫ y in Metric.ball (0 : RealConeModel (Fin 1) (Fin 1)) 1, P y ^ 2) :=
  corollary_3_5_homogeneous (by norm_num) pCone pCone_lt_one pCoords D

end ConicalKahler.Test
