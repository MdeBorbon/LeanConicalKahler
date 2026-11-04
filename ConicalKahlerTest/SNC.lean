module

public import ConicalKahler

/-!
# Tests for SNC divisors with labelled cone angles

* `n = 2`, `k = 2`: the axes `{z_0 = 0}` and `{z_1 = 0}` with independent angles `2πβ₀`, `2πβ₁`
  (including angles above `2π`). The model matrix is
  `diag(β₀² |z₀|^(2β₀-2), β₁² |z₁|^(2β₁-2))`, and the model is SNC-conical and Ricci-flat.
* Each labelled component is a smooth divisor.
* `k = 1` recovers the single-cone weights, and the smooth cone condition is the one-label SNC
  condition.
-/

namespace ConicalKahler.Test

open ConicalKahler

/-- The two coordinate axes of `ℂ²`, labelled `0` and `1`. -/
noncomputable abbrev axes : SNCDivisor 2 (E 2) (Fin 2) := coordSNC 2 2 le_rfl

/-- Kähler forms on the complement of an SNC divisor make sense. -/
example (x : axes.complement) : (x : E 2) 0 ≠ 0 := by
  have h := SNCDivisor.mem_complement_iff_forall.mp x.2 0
  simpa [coordSNC_components] using h

/-- The complement is `{z₀ z₁ ≠ 0}`. -/
example (z : E 2) : z ∈ axes.complement ↔ z 0 ≠ 0 ∧ z 1 ≠ 0 := by
  rw [SNCDivisor.mem_complement_iff_forall]
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ j
    fin_cases j
    · exact h0
    · exact h1

/-- The SNC model weights, explicitly. -/
example (angle : Fin 2 → ConeAngle) (z : E 2) :
    modelWeight (coordSNCWeights le_rfl angle) z 0 =
        (angle 0).beta ^ 2 * ‖z 0‖ ^ (2 * (angle 0).beta - 2) ∧
      modelWeight (coordSNCWeights le_rfl angle) z 1 =
        (angle 1).beta ^ 2 * ‖z 1‖ ^ (2 * (angle 1).beta - 2) :=
  ⟨(coordSNCChart 2 2 le_rfl 0).modelWeight_localWeights_slot angle z ⟨0, Nat.zero_lt_two⟩,
    (coordSNCChart 2 2 le_rfl 0).modelWeight_localWeights_slot angle z ⟨1, Nat.one_lt_two⟩⟩

/-- The SNC model with angles `π` along `{z₀ = 0}` and `6π` along `{z₁ = 0}` is SNC-conical and
Ricci-flat. -/
example :
    let angle : Fin 2 → ConeAngle := ![⟨1 / 2, by norm_num⟩, ⟨3, by norm_num⟩]
    IsSNCConeAlong axes angle (modelOnCoordSNC le_rfl angle) ∧
      (modelOnCoordSNC le_rfl angle).IsRicciFlat :=
  ⟨modelOnCoordSNC_isSNCConeAlong _ _, modelOnCoordSNC_ricciFlat _ _⟩

/-- Each labelled component is a smooth divisor; the second axis is `{z₁ = 0}`. -/
example (z : E 2) : z ∈ (axes.component 1).carrier ↔ z 1 = 0 :=
  Iff.rfl

/-- One component: the SNC model weights are the single-cone weights. -/
example (β : ConeAngle) :
    coordSNCWeights (n := 3) (k := 1) (by norm_num) (fun _ => β) = singleConeWeights β := by
  unfold coordSNCWeights
  exact localWeights_eq_singleConeWeights (coordSNCChart 3 1 (by norm_num) 0) rfl β

/-- The smooth cone condition is the one-label SNC condition: the standard cone metric along the
coordinate hyperplane is SNC-conical for `D.toSNC`. -/
example (β : ConeAngle) :
    IsSNCConeAlong (coordHyperplane 2).toSNC (fun _ => β)
      ((coordHyperplane 2).toSNCForm (modelOnHyperplane β)) :=
  (isConeAlong_iff_isSNCConeAlong _ β _).mp (modelOnHyperplane_isConeAlong β)

end ConicalKahler.Test
