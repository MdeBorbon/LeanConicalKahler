module

public import ConicalKahler.Cone.Weights

/-!
# Cone dilations of products of cones and Euclidean factors

The product of cones and Euclidean factors with weights `θ` is a metric cone. Its dilations are
`δ_λ(z)_j = λ^{1/β_j} z_j` on a cone factor and `δ_λ(z)_j = λ z_j` on a Euclidean factor
(`coneDilation`). In the cone coordinate `ρ_j = |z_j|^{β_j}` this is `ρ_j ↦ λ ρ_j`, and in the
Euclidean coordinates `s ↦ λ s`.

* `modelConeQuadratic_coneDilation`: `q_θ(δ_λ z; δ_λ v) = λ² q_θ(z; v)`. The dilation is a
  homothety of the model metric with factor `λ²`, i.e. it scales distances by `λ`. This holds for
  all angles and at every point. It is the scaling behind blow-up arguments.
* `coneDilation_mem_modelDomain`: the dilation preserves the model domain.
* `coneDilation_mul`, `coneDilation_one`: it is a one-parameter group.
-/

@[expose] public section

namespace ConicalKahler

variable {n : ℕ}

/-- The scaling factor of the cone dilation on the coordinate `j`: `λ^{1/β}` on a cone factor,
`λ` on a Euclidean factor. -/
noncomputable def coneDilationFactor (θ : ConeWeights n) (lam : ℝ) (j : Fin n) : ℝ :=
  match θ.angle j with
  | none => lam
  | some β => lam ^ β.beta⁻¹

/-- **The cone dilation** `δ_λ(z)_j = coneDilationFactor θ λ j · z_j`. -/
noncomputable def coneDilation (θ : ConeWeights n) (lam : ℝ) (z : E n) : E n :=
  WithLp.toLp 2 fun j => (coneDilationFactor θ lam j : ℂ) * z j

@[simp]
theorem coneDilation_apply (θ : ConeWeights n) (lam : ℝ) (z : E n) (j : Fin n) :
    coneDilation θ lam z j = (coneDilationFactor θ lam j : ℂ) * z j :=
  rfl

theorem coneDilationFactor_pos (θ : ConeWeights n) {lam : ℝ} (hlam : 0 < lam) (j : Fin n) :
    0 < coneDilationFactor θ lam j := by
  unfold coneDilationFactor
  cases θ.angle j with
  | none => exact hlam
  | some β => exact Real.rpow_pos_of_pos hlam _

theorem coneDilationFactor_one (θ : ConeWeights n) (j : Fin n) :
    coneDilationFactor θ 1 j = 1 := by
  unfold coneDilationFactor
  cases θ.angle j with
  | none => rfl
  | some β => exact Real.one_rpow _

theorem coneDilationFactor_mul (θ : ConeWeights n) {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (j : Fin n) :
    coneDilationFactor θ (lam * mu) j = coneDilationFactor θ lam j * coneDilationFactor θ mu j := by
  unfold coneDilationFactor
  cases θ.angle j with
  | none => rfl
  | some β => exact Real.mul_rpow hlam hmu

theorem coneDilation_one (θ : ConeWeights n) (z : E n) : coneDilation θ 1 z = z := by
  ext j
  simp [coneDilationFactor_one]

theorem coneDilation_mul (θ : ConeWeights n) {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (z : E n) : coneDilation θ (lam * mu) z = coneDilation θ lam (coneDilation θ mu z) := by
  ext j
  simp only [coneDilation_apply, coneDilationFactor_mul θ hlam hmu, Complex.ofReal_mul]
  ring

/-- The dilation preserves the model domain. -/
theorem coneDilation_mem_modelDomain (θ : ConeWeights n) {lam : ℝ} (hlam : 0 < lam) {z : E n}
    (hz : z ∈ modelDomain θ) : coneDilation θ lam z ∈ modelDomain θ := by
  intro j β hj
  rw [coneDilation_apply]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (coneDilationFactor_pos θ hlam j).ne') (hz j β hj)

/-- Each term of the model form scales by `λ²` under the dilation. -/
theorem modelWeight_coneDilation (θ : ConeWeights n) {lam : ℝ} (hlam : 0 < lam) (z v : E n)
    (j : Fin n) :
    modelWeight θ (coneDilation θ lam z) j * Complex.normSq (coneDilation θ lam v j) =
      lam ^ 2 * (modelWeight θ z j * Complex.normSq (v j)) := by
  rw [coneDilation_apply, Complex.normSq_mul, Complex.normSq_ofReal]
  cases hθ : θ.angle j with
  | none =>
    have hfac : coneDilationFactor θ lam j = lam := by simp [coneDilationFactor, hθ]
    rw [hfac, modelWeight_of_none hθ, modelWeight_of_none hθ]
    ring
  | some β =>
    have hfac : coneDilationFactor θ lam j = lam ^ β.beta⁻¹ := by
      simp [coneDilationFactor, hθ]
    rw [hfac, modelWeight_of_some hθ, modelWeight_of_some hθ, coneDilation_apply, hfac]
    have hβ := β.pos
    have hlam' : 0 ≤ lam ^ β.beta⁻¹ := Real.rpow_nonneg hlam.le _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam',
      Real.mul_rpow hlam' (norm_nonneg _), ← Real.rpow_mul hlam.le]
    have hexp : lam ^ (β.beta⁻¹ * (2 * β.beta - 2)) * (lam ^ β.beta⁻¹ * lam ^ β.beta⁻¹) =
        lam ^ 2 := by
      rw [← Real.rpow_add hlam, ← Real.rpow_add hlam, ← Real.rpow_two]
      congr 1
      field_simp
      ring
    calc β.beta ^ 2 * (lam ^ (β.beta⁻¹ * (2 * β.beta - 2)) * ‖z j‖ ^ (2 * β.beta - 2)) *
          (lam ^ β.beta⁻¹ * lam ^ β.beta⁻¹ * Complex.normSq (v j))
        = (lam ^ (β.beta⁻¹ * (2 * β.beta - 2)) * (lam ^ β.beta⁻¹ * lam ^ β.beta⁻¹)) *
            (β.beta ^ 2 * ‖z j‖ ^ (2 * β.beta - 2) * Complex.normSq (v j)) := by ring
      _ = _ := by rw [hexp]

/-- **The cone dilation is a homothety of the model:** `q_θ(δ_λ z; δ_λ v) = λ² q_θ(z; v)`. -/
theorem modelConeQuadratic_coneDilation (θ : ConeWeights n) {lam : ℝ} (hlam : 0 < lam)
    (z v : E n) :
    modelConeQuadratic θ (coneDilation θ lam z) (coneDilation θ lam v) =
      lam ^ 2 * modelConeQuadratic θ z v := by
  rw [modelConeQuadratic, modelConeQuadratic, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => modelWeight_coneDilation θ hlam z v j

end ConicalKahler
