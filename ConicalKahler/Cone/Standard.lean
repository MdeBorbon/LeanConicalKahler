module

public import ConicalKahler.Cone.ModelRicci

/-!
# The standard cone metric along a coordinate hyperplane

For `β > 0` the **standard cone metric** with cone angle `2πβ` along `{z_0 = 0}` is

  `ω_β = i β² |z_0|^(2β-2) dz_0 ∧ dz̄_0 + i ∑_{j=1}^{n-1} dz_j ∧ dz̄_j`

on `{z_0 ≠ 0} ⊆ ℂⁿ` (written `z_1` in 1-indexed notation). It is the model form
`ModelConeForm (singleConeWeights β)`.

## Main results

* `standardConeForm β : KahlerForm n (modelDomain (singleConeWeights β))`, for every `β > 0`:
  smooth, closed and positive `(1,1)`-form (the `KahlerForm` structure fields).
* `mem_modelDomain_single`: the domain is exactly `{z | z 0 ≠ 0}`.
* `standardConeForm_apply`: the explicit formula
  `ω_β(u, v) = -2 Im (β² |z_0|^(2β-2) u_0 v̄_0 + ∑_{j ≥ 1} u_j v̄_j)`.
* `standardConeForm_coeffMatrix`: `g_{jk̄} = diag(β² |z_0|^(2β-2), 1, …, 1)`.
* `standardConeForm_ricciFlat`: `Ric(ω_β) = 0` on `{z_0 ≠ 0}`.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Filter ContinuousAlternatingMap

namespace ConicalKahler

variable {n : ℕ}

/-! ### General explicit formula -/

/-- The model form as an explicit real `2`-form: `ω_θ(u, v) = -2 Im ∑ⱼ w_j(z) u_j v̄_j`. -/
theorem modelConeForm_apply_eq (θ : ConeWeights n) (x : modelDomain θ) (u v : E n) :
    ModelConeForm θ x ![u, v] =
      -2 * Complex.im (∑ j, (modelWeight θ x j : ℂ) * u j * star (v j)) := by
  rw [((ModelConeForm θ).isOneOne x).apply_eq, modelConeMatrix_eq_coeffMatrix]
  have hsum : (∑ j, ∑ k, modelConeMatrix θ x j k * u j * star (v k)) =
      ∑ j, (modelWeight θ x j : ℂ) * u j * star (v j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [modelConeMatrix, Ne.symm hk]) (by simp)]
    simp [modelConeMatrix]
  rw [hsum]

/-! ### The single-hyperplane weights -/

variable [NeZero n]

theorem modelWeight_single_zero (β : ConeAngle) (z : E n) :
    modelWeight (singleConeWeights β) z 0 = β.beta ^ 2 * ‖z 0‖ ^ (2 * β.beta - 2) :=
  modelWeight_of_some (singleConeWeights_angle_zero β) z

theorem modelWeight_single_of_ne (β : ConeAngle) (z : E n) {j : Fin n} (hj : j ≠ 0) :
    modelWeight (singleConeWeights β) z j = 1 :=
  modelWeight_of_none (singleConeWeights_angle_of_ne β hj) z

/-- The standard cone weight vector `(β² |z_0|^(2β-2), 1, …, 1)`. -/
theorem modelWeight_single (β : ConeAngle) (z : E n) (j : Fin n) :
    modelWeight (singleConeWeights β) z j =
      if j = 0 then β.beta ^ 2 * ‖z 0‖ ^ (2 * β.beta - 2) else 1 := by
  split_ifs with hj
  · subst hj
    exact modelWeight_single_zero β z
  · exact modelWeight_single_of_ne β z hj

/-! ### The standard cone form -/

/-- **The standard cone Kähler form** with cone angle `2πβ` along `{z_0 = 0}`:
`ω_β = i β² |z_0|^(2β-2) dz_0 ∧ dz̄_0 + i ∑_{j ≥ 1} dz_j ∧ dz̄_j` on `{z_0 ≠ 0}`, for any
`β > 0`. -/
noncomputable abbrev standardConeForm (β : ConeAngle) :
    KahlerForm n (modelDomain (singleConeWeights (n := n) β)) :=
  ModelConeForm (singleConeWeights β)

/-- The standard cone form is a smooth form field. -/
theorem standardConeForm_isSmooth (β : ConeAngle) :
    (standardConeForm (n := n) β).toFormField.IsSmooth :=
  (standardConeForm β).isSmooth

/-- The standard cone form is closed: `dω_β = 0`. -/
theorem standardConeForm_isClosed (β : ConeAngle) :
    (standardConeForm (n := n) β).toFormField.IsClosed :=
  (standardConeForm β).isClosed

/-- The standard cone form is a positive `(1,1)`-form at every point of `{z_0 ≠ 0}`. -/
theorem standardConeForm_isPositive (β : ConeAngle)
    (x : modelDomain (singleConeWeights (n := n) β)) :
    (standardConeForm β x).IsPositive :=
  (standardConeForm β).isPositive x

/-- Explicit formula:
`ω_β(u, v) = -2 Im (β² |z_0|^(2β-2) u_0 v̄_0 + ∑_{j ≥ 1} u_j v̄_j)`. -/
theorem standardConeForm_apply (β : ConeAngle)
    (x : modelDomain (singleConeWeights (n := n) β)) (u v : E n) :
    standardConeForm β x ![u, v] =
      -2 * Complex.im (∑ j,
        ((if j = 0 then β.beta ^ 2 * ‖(x : E n) 0‖ ^ (2 * β.beta - 2) else 1 : ℝ) : ℂ) *
          u j * star (v j)) := by
  rw [modelConeForm_apply_eq]
  simp_rw [modelWeight_single]

/-- Coefficients: `(ω_β)_{jk̄} = diag(β² |z_0|^(2β-2), 1, …, 1)`. -/
theorem standardConeForm_coeffMatrix (β : ConeAngle)
    (x : modelDomain (singleConeWeights (n := n) β)) :
    (standardConeForm β x).coeffMatrix =
      Matrix.diagonal fun j =>
        ((if j = 0 then β.beta ^ 2 * ‖(x : E n) 0‖ ^ (2 * β.beta - 2) else 1 : ℝ) : ℂ) := by
  rw [modelConeMatrix_eq_coeffMatrix]
  simp_rw [modelConeMatrix, modelWeight_single]

/-- **The standard cone form is Ricci-flat on `{z_0 ≠ 0}`**, for every cone angle `2πβ`,
`β > 0`. -/
theorem standardConeForm_ricciFlat (β : ConeAngle) :
    (standardConeForm (n := n) β).IsRicciFlat :=
  modelConeForm_ricciFlat _

/-! ### Sanity check: `β = 1` is the Euclidean metric -/

/-- For `β = 1` (cone angle `2π`) the standard cone form is the Euclidean Kähler form
`i∂∂̄|z|² = i ∑ⱼ dz_j ∧ dz̄_j`, restricted to `{z_0 ≠ 0}`. -/
theorem standardConeForm_one (x : modelDomain (singleConeWeights (n := n) ConeAngle.one)) :
    standardConeForm ConeAngle.one x = ddbar (fun w : E n => ‖w‖ ^ 2) x := by
  let : InnerProductSpace ℝ (E n) := InnerProductSpace.rclikeToReal ℂ (E n)
  have hf : ContDiffAt ℝ 2 (fun w : E n => ‖w‖ ^ 2) x := contDiffAt_id.norm_sq ℝ
  refine ((standardConeForm _).isOneOne x).ext (isOneOne_ddbar hf) ?_
  rw [standardConeForm_coeffMatrix]
  change _ = complexHessian _ _
  rw [complexHessian_normSq]
  ext j k
  by_cases hjk : j = k
  · subst hjk
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    split_ifs <;> simp [ConeAngle.one]
  · simp [Matrix.diagonal_apply_ne _ hjk, Matrix.one_apply_ne hjk]

end ConicalKahler
