module

public import ConicalKahler

/-!
# Mathematical tests for the model cone form

Concrete instances from the specification's test list (§5):

* `n = 1`: the model has `g_{zz̄} = β² |z|^(2β-2)` and is flat on `ℂ*`;
* `β = 1`: the model is exactly the Euclidean Kähler form;
* `n = 2`: `diag(β² |z₀|^(2β-2), 1)` and volume factor `det g = β² |z₀|^(2β-2)`;
* `n = 2`, two cone directions: `diag(β₀² |z₀|^(2β₀-2), β₁² |z₁|^(2β₁-2))`, Ricci-flat on
  `{z₀ z₁ ≠ 0}`.
-/

namespace ConicalKahler.Test

open ConicalKahler

/-! ### `n = 1` -/

example (β : ConeAngle) (z : E 1) : z ∈ modelDomain (singleConeWeights β) ↔ z 0 ≠ 0 :=
  mem_modelDomain_single

example (β : ConeAngle) (x : modelDomain (singleConeWeights (n := 1) β)) :
    (standardConeForm β x).coeffMatrix =
      !![((β.beta ^ 2 * ‖(x : E 1) 0‖ ^ (2 * β.beta - 2) : ℝ) : ℂ)] := by
  rw [standardConeForm_coeffMatrix]
  ext i j
  fin_cases i
  fin_cases j
  simp

example (β : ConeAngle) : (standardConeForm (n := 1) β).IsRicciFlat :=
  standardConeForm_ricciFlat β

/-! ### `β = 1` -/

example (x : modelDomain (singleConeWeights (n := 3) ConeAngle.one)) :
    standardConeForm ConeAngle.one x = ddbar (fun w : E 3 => ‖w‖ ^ 2) x :=
  standardConeForm_one x

/-! ### `n = 2`, one cone direction -/

example (β : ConeAngle) (x : modelDomain (singleConeWeights (n := 2) β)) :
    (standardConeForm β x).coeffMatrix =
      !![((β.beta ^ 2 * ‖(x : E 2) 0‖ ^ (2 * β.beta - 2) : ℝ) : ℂ), 0; 0, 1] := by
  rw [standardConeForm_coeffMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The volume factor `ω_βⁿ / ω_eucⁿ = det g = β² |z₀|^(2β-2)`. -/
example (β : ConeAngle) (x : modelDomain (singleConeWeights (n := 2) β)) :
    (standardConeForm β x).coeffMatrix.det =
      ((β.beta ^ 2 * ‖(x : E 2) 0‖ ^ (2 * β.beta - 2) : ℝ) : ℂ) := by
  rw [standardConeForm_coeffMatrix, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

/-! ### `n = 2`, two cone directions (normal crossings) -/

/-- Cone angles `2πβ₀` along `z₀ = 0` and `2πβ₁` along `z₁ = 0`. -/
def twoConeWeights (β₀ β₁ : ConeAngle) : ConeWeights 2 :=
  ⟨![some β₀, some β₁]⟩

example (β₀ β₁ : ConeAngle) (z : E 2) :
    z ∈ modelDomain (twoConeWeights β₀ β₁) ↔ z 0 ≠ 0 ∧ z 1 ≠ 0 := by
  rw [mem_modelDomain]
  constructor
  · intro h
    exact ⟨h 0 β₀ rfl, h 1 β₁ rfl⟩
  · rintro ⟨h0, h1⟩ j β hj
    fin_cases j
    · exact h0
    · exact h1

example (β₀ β₁ : ConeAngle) (x : modelDomain (twoConeWeights β₀ β₁)) :
    (ModelConeForm (twoConeWeights β₀ β₁) x).coeffMatrix =
      !![((β₀.beta ^ 2 * ‖(x : E 2) 0‖ ^ (2 * β₀.beta - 2) : ℝ) : ℂ), 0;
        0, ((β₁.beta ^ 2 * ‖(x : E 2) 1‖ ^ (2 * β₁.beta - 2) : ℝ) : ℂ)] := by
  rw [modelConeMatrix_eq_coeffMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modelConeMatrix, modelWeight, twoConeWeights]

example (β₀ β₁ : ConeAngle) : (ModelConeForm (twoConeWeights β₀ β₁)).IsRicciFlat :=
  modelConeForm_ricciFlat _

/-! ### The smooth weights give the Euclidean metric everywhere -/

example (n : ℕ) (z : E n) : z ∈ modelDomain (ConeWeights.smooth n) :=
  mem_modelDomain_smooth z

example (n : ℕ) (x : modelDomain (ConeWeights.smooth n)) :
    (ModelConeForm (ConeWeights.smooth n) x).coeffMatrix = 1 := by
  rw [modelConeMatrix_eq_coeffMatrix]
  ext i j
  by_cases h : i = j
  · subst h
    simp [modelConeMatrix, modelWeight, ConeWeights.smooth]
  · simp [modelConeMatrix, Matrix.one_apply_ne h, h]

end ConicalKahler.Test
