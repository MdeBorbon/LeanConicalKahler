module

public import ConicalKahler

/-!
# Tests for Milestone 14: decay at the vertex

The model `C(S¹_{4π/3}) × ℝ` (`β = 2/3`, `μ = 1/2`), with real coordinates `(x, y, s)` of `ℝ³`.
-/

namespace ConicalKahler.Test

open ConicalKahler ConicalKahler.Sobolev MeasureTheory Metric
open scoped Real InnerProductSpace

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- One cone of angle `4π/3` (`β = 2/3`). -/
noncomputable def vCone : Fin 1 → ConeAngle := fun _ => ⟨2 / 3, by norm_num⟩

/-- A numbering of the three real coordinates `(x, y, s)`. -/
noncomputable def vCoords : RealConeIndex (Fin 1) (Fin 1) ≃ Fin 3 :=
  Fintype.equivFinOfCardEq (by simp)

theorem vCone_lt_one : ∀ a, (vCone a).beta < 1 := fun _ => by norm_num [vCone]

theorem vCone_mu : ∀ a, (1 / 2 : ℝ) ≤ holderExponentBound (vCone a).beta := fun _ => by
  norm_num [holderExponentBound, vCone]

/-- **Decay at the vertex**: a weakly harmonic `h` minus its projection `P` onto `𝓗_{≤2}` decays
like `ρ^{2 + 1/2}` in the scaled `L²` norm: `∫_{B_ρ} (h − P)² ≤ ρ^{5 + 3} ∫_{B_1} (h − P)²`. -/
example {h : L2Pair volume (ball (0 : ℝ³) 1)} (hh : (coneCoeff vCone vCoords).IsWeakSolution 0 h)
    : ∃ P ∈ explicitH2 vCone,
      ∫ x in ball (0 : ℝ³) 1, (h.fst x - P ((coordIso vCoords).symm x)) ^ 2 ≤
        ∫ x in ball (0 : ℝ³) 1, h.fst x ^ 2 ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        ∫ x in ball (0 : ℝ³) ρ, (h.fst x - P ((coordIso vCoords).symm x)) ^ 2 ≤
          ρ ^ (2 * (2 + 1 / 2) + 3 : ℝ) *
            ∫ x in ball (0 : ℝ³) 1, (h.fst x - P ((coordIso vCoords).symm x)) ^ 2 := by
  obtain ⟨P, hP, -, hnorm, hdec⟩ := cone_vertex_decay (by norm_num) vCone vCone_lt_one vCoords
    (μ := 1 / 2) (by norm_num) vCone_mu hh
  refine ⟨P, hP, hnorm, fun ρ hρ0 hρ1 => ?_⟩
  have := hdec ρ 1 hρ0 hρ1 le_rfl
  simpa using this

/-- **Lemma 4.3 (near the vertex)** with `α = 1/4`, `q = 1/2`. -/
example : ∃ ε₀ > 0, ∀ ε, 0 ≤ ε → ε < ε₀ → ∀ {Ω U : Set ℝ³} {u : L2Pair volume Ω},
    (coneCoeff vCone vCoords).IsWeakSolution 0 u → ball (0 : ℝ³) (1 - ε) ⊆ Ω →
    (∀ P ∈ explicitH2 vCone, ∫ x in ball (0 : ℝ³) (1 - ε),
      u.fst x * P ((coordIso vCoords).symm x) = 0) →
    U ⊆ ball (0 : ℝ³) (1 / 2 + ε) →
    ((1 / 2 : ℝ) ^ 3)⁻¹ * ∫ x in U, u.fst x ^ 2 ≤
      (1 / 2 : ℝ) ^ (2 * (2 + 1 / 4) : ℝ) * ∫ x in Ω, u.fst x ^ 2 :=
  cone_decay_near_vertex (by norm_num) vCone vCone_lt_one vCoords (by norm_num) vCone_mu
    (α := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Lemma 2.7 on Euclidean balls** centred at any point. -/
example (x : ℝ³) {q α C : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hα : 0 < α) (hC : 0 ≤ C)
    {f : ℝ³ → ℝ} (hf : MemLp f 2 (volume.restrict (ball x 1))) (τ : ℕ → ℝ)
    (hτ : ∀ k : ℕ, scaledL2 volume (fun ρ => ball x ρ) 3 (q ^ k)
      (fun y => f y - ∑ j ∈ Finset.range k, τ j) ≤ C * (q ^ α) ^ k) :
    Summable (fun k => |τ k|) ∧ ∀ r, 0 < r → r ≤ 1 →
      scaledL2 volume (fun ρ => ball x ρ) 3 r (fun y => f y - ∑' k, τ k) ≤
        incrementConst q α 3 (volume (ball (0 : ℝ³) 1)).toReal (volume (ball (0 : ℝ³) 1)).toReal *
          C * r ^ α :=
  sum_increments (ballFamily_euclidean x) hq0 hq1 hα hC hf τ hτ

end ConicalKahler.Test
