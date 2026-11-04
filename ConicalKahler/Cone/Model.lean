module

public import ConicalKahler.Cone.Weights
public import ConicalKahler.Analysis.RadialHessian
public import ConicalKahler.Manifold.OpenSubset
public import CalabiYau.Geometry.Kahler.Basic

/-!
# The model cone Kähler form

For cone weights `θ : ConeWeights n` we construct the Kähler form

  `ω_θ = i ∑_{j cone} β_j² |z_j|^(2β_j-2) dz_j ∧ dz̄_j + i ∑_{j smooth} dz_j ∧ dz̄_j`

on the open manifold `modelDomain θ = {z | z_j ≠ 0 for every cone coordinate j}`, as an honest
upstream `KahlerForm n (modelDomain θ)`. In particular, for `θ = singleConeWeights β` this is the
standard cone metric `ω_β` along `{z_0 = 0}`, for every `β > 0`.

## Construction

`ω_θ = i∂∂̄ Φ_θ` with the potential

  `Φ_θ(z) = ∑_{j cone} |z_j|^(2β_j) + ∑_{j smooth} |z_j|²`  (`modelPotential`),

restricted to the open submanifold `modelDomain θ`. Smoothness and closedness come from the
upstream lemmas `isSmooth_mddbar` and `isClosed_mddbar`; positivity from the explicit diagonal
complex Hessian (`complexHessian_modelPotential`), computed by the separable radial chain rule.

## Main results

* `modelConeFormOn θ U hU : KahlerForm n U` for any open `U ⊆ modelDomain θ`, and
  `ModelConeForm θ : KahlerForm n (modelDomain θ)`.
* `modelConeForm_apply`: `ω_θ x = ddbar Φ_θ x`.
* `modelConeMatrix_eq_coeffMatrix`: the coefficient matrix at `x` is `modelConeMatrix θ x`.
* `modelConeForm_metricInChart`: in the chart at any `x`, `g_{jk̄}(z) = modelConeMatrix θ z` on the
  whole chart target.
* `modelConeForm_apply_I_smul`: `ω_θ(v, Jv) = 2 q_model(v)`.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Filter ContinuousAlternatingMap
open scoped ComplexOrder

namespace ConicalKahler

variable {n : ℕ}

/-! ### The potential -/

/-- The one-variable profile `g`, so that the potential term in direction `j` is `g(|z_j|²)`:
`g(s) = s` for a smooth direction and `g(s) = s^β` (i.e. `|z_j|^(2β)`) for a cone direction. -/
noncomputable def coordProfile : Option ConeAngle → ℝ → ℝ
  | none => fun s => s
  | some β => fun s => s ^ β.beta

/-- The Kähler potential `Φ_θ(z) = ∑_{j cone} |z_j|^(2β_j) + ∑_{j smooth} |z_j|²` of the model. -/
noncomputable def modelPotential (θ : ConeWeights n) (z : E n) : ℝ :=
  ∑ j, coordProfile (θ.angle j) (coordNormSq j z)

theorem coordProfile_some (β : ConeAngle) (z : E n) (j : Fin n) :
    coordProfile (some β) (coordNormSq j z) = ‖z j‖ ^ (2 * β.beta) := by
  simp only [coordProfile, coordNormSq]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  norm_num

theorem contDiffAt_coordProfile {θ : ConeWeights n} {z : E n} (hz : z ∈ modelDomain θ)
    (j : Fin n) {m : WithTop ℕ∞} :
    ContDiffAt ℝ m (coordProfile (θ.angle j)) (coordNormSq j z) := by
  cases hθ : θ.angle j with
  | none => exact contDiffAt_id
  | some β => exact Real.contDiffAt_rpow_const_of_ne (coordNormSq_pos (hz j β hθ)).ne'

/-- The radial coefficient of the profile is the model weight. -/
theorem radialCoeff_coordProfile {θ : ConeWeights n} {z : E n} (hz : z ∈ modelDomain θ)
    (j : Fin n) :
    radialCoeff (coordProfile (θ.angle j)) (coordNormSq j z) = modelWeight θ z j := by
  cases hθ : θ.angle j with
  | none =>
    rw [modelWeight_of_none hθ]
    exact radialCoeff_id _
  | some β =>
    rw [modelWeight_of_some hθ]
    simp only [coordProfile]
    rw [radialCoeff_rpow _ (coordNormSq_pos (hz j β hθ)), coordNormSq]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
    ring_nf

theorem contDiffAt_modelPotential {θ : ConeWeights n} {z : E n} (hz : z ∈ modelDomain θ)
    {m : WithTop ℕ∞} : ContDiffAt ℝ m (modelPotential θ) z :=
  ContDiffAt.sum fun j _ =>
    (contDiffAt_coordProfile hz j).comp z (contDiff_coordNormSq j).contDiffAt

theorem contDiffOn_modelPotential (θ : ConeWeights n) {m : WithTop ℕ∞} :
    ContDiffOn ℝ m (modelPotential θ) (modelDomain θ) := fun _ hz =>
  (contDiffAt_modelPotential hz).contDiffWithinAt

/-- **The model Hessian.** On the model domain, `∂²Φ_θ/∂z_j∂z̄ₖ = δⱼₖ w_j(z)`; in particular
`∂²|z_0|^(2β)/∂z_0∂z̄_0 = β² |z_0|^(2β-2)`. -/
theorem complexHessian_modelPotential {θ : ConeWeights n} {z : E n} (hz : z ∈ modelDomain θ) :
    complexHessian (modelPotential θ) z = modelConeMatrix θ z := by
  unfold complexHessian
  change (ddbar (fun w => ∑ j, coordProfile (θ.angle j) (coordNormSq j w)) z).coeffMatrix = _
  rw [coeffMatrix_ddbar_separable fun j => contDiffAt_coordProfile hz j]
  simp_rw [radialCoeff_coordProfile hz]
  rfl

/-! ### The model Kähler form -/

section On

variable (θ : ConeWeights n) (U : TopologicalSpace.Opens (E n))
  (hU : (U : Set (E n)) ⊆ modelDomain θ)

/-- The model cone form `i∂∂̄ Φ_θ` on an arbitrary open subset `U` of the model domain. This is
used both for `U = modelDomain θ` (`ModelConeForm`) and for `U = D.complement` or small
neighbourhoods. -/
noncomputable def modelConeFormOn : KahlerForm n U where
  toFormField := mddbar n fun x : U => modelPotential θ x
  isSmooth' := isSmooth_mddbar
    (contMDiff_opens_of_contDiffOn _ ((contDiffOn_modelPotential θ).mono hU))
  isPositive' := by
    intro x
    rw [mddbar_opens, isPositive_iff]
    refine ⟨isOneOne_ddbar (contDiffAt_modelPotential (hU x.2)), ?_⟩
    change (complexHessian (modelPotential θ) x).PosDef
    rw [complexHessian_modelPotential (hU x.2)]
    exact modelConeMatrix_posDef (hU x.2)
  isClosed' := isClosed_mddbar
    (contMDiff_opens_of_contDiffOn _ ((contDiffOn_modelPotential θ).mono hU))

theorem modelConeFormOn_toFormField :
    (modelConeFormOn θ U hU).toFormField = mddbar n fun x : U => modelPotential θ x :=
  rfl

/-- At each point, the model form is `i∂∂̄Φ_θ` computed on `ℂⁿ`. -/
theorem modelConeFormOn_apply (x : U) : modelConeFormOn θ U hU x = ddbar (modelPotential θ) x :=
  mddbar_opens _ _ x

/-- The coefficient matrix at every point is `diag(w_j)`. -/
theorem modelConeFormOn_coeffMatrix (x : U) :
    (modelConeFormOn θ U hU x).coeffMatrix = modelConeMatrix θ x := by
  rw [modelConeFormOn_apply]
  exact complexHessian_modelPotential (hU x.2)

/-- In the chart of `U` at any point `x`, the local metric of the model is `diag(w_j(z))` on the
whole chart target. -/
theorem modelConeFormOn_metricInChart (x : U) {z : E n}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E n) x).target) :
    (modelConeFormOn θ U hU).metricInChart x z = modelConeMatrix θ z := by
  change (FormField.chartRep (mddbar n fun x : U => modelPotential θ x) x z).coeffMatrix = _
  rw [chartRep_mddbar_opens ((contDiffOn_modelPotential θ).mono hU) x hz]
  exact complexHessian_modelPotential (hU (extChartAt_opens_target_subset _ x hz))

/-- `ω_θ(v, Jv) = 2 ∑ⱼ w_j(z) |v_j|²`. -/
theorem modelConeFormOn_apply_I_smul (x : U) (v : E n) :
    modelConeFormOn θ U hU x ![v, Complex.I • v] = 2 * modelConeQuadratic θ x v := by
  rw [((modelConeFormOn θ U hU).isOneOne x).apply_I_smul, modelConeFormOn_coeffMatrix,
    ← modelConeQuadratic_eq_sum, Complex.ofReal_re]

end On

/-- **The model cone Kähler form** `ω_θ = i∂∂̄ Φ_θ` on `modelDomain θ`. For
`θ = singleConeWeights β` this is
`i β² |z_0|^(2β-2) dz_0 ∧ dz̄_0 + i ∑_{j ≥ 1} dz_j ∧ dz̄_j` on `{z_0 ≠ 0}`, for any `β > 0`. -/
noncomputable def ModelConeForm (θ : ConeWeights n) : KahlerForm n (modelDomain θ) :=
  modelConeFormOn θ (modelDomain θ) subset_rfl

theorem modelConeForm_toFormField (θ : ConeWeights n) :
    (ModelConeForm θ).toFormField = mddbar n fun x : modelDomain θ => modelPotential θ x :=
  rfl

/-- At each point, the model form is `i∂∂̄Φ_θ` computed on `ℂⁿ`. -/
theorem modelConeForm_apply (θ : ConeWeights n) (x : modelDomain θ) :
    ModelConeForm θ x = ddbar (modelPotential θ) x :=
  modelConeFormOn_apply θ _ _ x

/-- **Coefficient matrix of the model.** At every point of the model domain,
`(ω_θ)_{jk̄} = diag(w_j)`. -/
theorem modelConeMatrix_eq_coeffMatrix (θ : ConeWeights n) (x : modelDomain θ) :
    (ModelConeForm θ x).coeffMatrix = modelConeMatrix θ x :=
  modelConeFormOn_coeffMatrix θ _ _ x

/-- In the chart of `modelDomain θ` at any point `x`, the local metric of the model is
`diag(w_j(z))` on the whole chart target. -/
theorem modelConeForm_metricInChart (θ : ConeWeights n) (x : modelDomain θ) {z : E n}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E n) x).target) :
    (ModelConeForm θ).metricInChart x z = modelConeMatrix θ z :=
  modelConeFormOn_metricInChart θ _ _ x hz

/-- The model form evaluated on `(v, Jv)` is twice the Hermitian model quadratic form:
`ω_θ(v, Jv) = 2 ∑ⱼ w_j(z) |v_j|²`. -/
theorem modelConeForm_apply_I_smul (θ : ConeWeights n) (x : modelDomain θ) (v : E n) :
    ModelConeForm θ x ![v, Complex.I • v] = 2 * modelConeQuadratic θ x v :=
  modelConeFormOn_apply_I_smul θ _ _ x v

end ConicalKahler
