module

public import ConicalKahler.Cone.Model
public import CalabiYau.Geometry.Kahler.Ricci

/-!
# The model cone form is Ricci-flat on the model domain

The upstream Ricci form is `Ric(ω) = -i∂∂̄ log det(g_{jk̄})`, computed at each point in the chart
centred there (`KahlerForm.ricciForm`). For the model `ω_θ` we know `g_{jk̄}(z) = diag(w_j(z))` on
every chart target (`modelConeForm_metricInChart`), so on a neighbourhood of every point

  `log det g = ∑_{j cone} (log β_j² + (β_j - 1) log |z_j|²)`.

Each `log |z_j|²` is pluriharmonic on `{z_j ≠ 0}` (`radialCoeff_const_add_mul_log`), hence
`Ric(ω_θ) = 0` on `modelDomain θ` (`modelConeForm_isRicciFlat`).

This is a statement on the open complement of the singular hyperplanes only. It does **not**
assert anything about the Ricci current on `ℂⁿ`, which is `2π ∑ⱼ (1 - β_j) [z_j = 0]`.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Filter ContinuousAlternatingMap

namespace ConicalKahler

variable {n : ℕ}

/-- The profile of `log w_j`: `0` for a smooth direction and `log β² + (β - 1) log s` for a cone
direction, so that `log w_j(z) = logProfile (θ.angle j) |z_j|²`. -/
noncomputable def logProfile : Option ConeAngle → ℝ → ℝ
  | none => fun _ => 0
  | some β => fun s => Real.log (β.beta ^ 2) + (β.beta - 1) * Real.log s

theorem log_modelWeight {θ : ConeWeights n} {z : E n} (hz : z ∈ modelDomain θ) (j : Fin n) :
    Real.log (modelWeight θ z j) = logProfile (θ.angle j) (coordNormSq j z) := by
  cases hθ : θ.angle j with
  | none => simp [modelWeight_of_none hθ, logProfile]
  | some β =>
    have hzj : 0 < ‖z j‖ := norm_pos_iff.mpr (hz j β hθ)
    have hβ : β.beta ^ 2 ≠ 0 := pow_ne_zero 2 β.pos.ne'
    rw [modelWeight_of_some hθ]
    simp only [logProfile, coordNormSq]
    rw [Real.log_mul hβ (Real.rpow_pos_of_pos hzj _).ne', Real.log_rpow hzj, Real.log_pow,
      Real.log_pow]
    push_cast
    ring

/-- `log det` of the model coefficient matrix is the separable function `∑ⱼ logProfile_j(|z_j|²)`. -/
theorem log_det_modelConeMatrix {θ : ConeWeights n} {z : E n} (hz : z ∈ modelDomain θ) :
    Real.log (RCLike.re (modelConeMatrix θ z).det) =
      ∑ j, logProfile (θ.angle j) (coordNormSq j z) := by
  rw [det_modelConeMatrix]
  rw [RCLike.re_to_complex, Complex.ofReal_re, Real.log_prod (fun j _ => (modelWeight_pos hz j).ne')]
  exact Finset.sum_congr rfl fun j _ => log_modelWeight hz j

theorem contDiffAt_logProfile {θ : ConeWeights n} {z : E n} (hz : z ∈ modelDomain θ) (j : Fin n)
    {m : WithTop ℕ∞} : ContDiffAt ℝ m (logProfile (θ.angle j)) (coordNormSq j z) := by
  cases hθ : θ.angle j with
  | none => exact contDiffAt_const
  | some β =>
    exact contDiffAt_const.add (contDiffAt_const.mul
      (Real.contDiffAt_log.mpr (coordNormSq_pos (hz j β hθ)).ne'))

theorem radialCoeff_logProfile {θ : ConeWeights n} {z : E n} (hz : z ∈ modelDomain θ)
    (j : Fin n) : radialCoeff (logProfile (θ.angle j)) (coordNormSq j z) = 0 := by
  cases hθ : θ.angle j with
  | none => exact radialCoeff_const 0 _
  | some β => exact radialCoeff_const_add_mul_log _ _ (coordNormSq_pos (hz j β hθ))

/-- `log det g_model` is pluriharmonic on the model domain. -/
theorem ddbar_logDet_model_eq_zero {θ : ConeWeights n} {z : E n} (hz : z ∈ modelDomain θ) :
    ddbar (fun w => ∑ j, logProfile (θ.angle j) (coordNormSq j w)) z = 0 := by
  have hg : ∀ j, ContDiffAt ℝ 2 (logProfile (θ.angle j)) (coordNormSq j z) := fun j =>
    contDiffAt_logProfile hz j
  have hcd : ContDiffAt ℝ 2 (fun w => ∑ j, logProfile (θ.angle j) (coordNormSq j w)) z :=
    ContDiffAt.sum fun j _ => (hg j).comp z (contDiff_coordNormSq j).contDiffAt
  refine ddbar_eq_zero_of_coeffMatrix_eq_zero hcd ?_
  rw [coeffMatrix_ddbar_separable hg]
  simp [radialCoeff_logProfile hz]

/-- Near each point, `log det g_{jk̄}` in the chart is the explicit pluriharmonic function. -/
theorem logDetInChart_modelConeFormOn_eventuallyEq (θ : ConeWeights n)
    (U : TopologicalSpace.Opens (E n)) (hU : (U : Set (E n)) ⊆ modelDomain θ) (x : U) :
    (modelConeFormOn θ U hU).logDetInChart x =ᶠ[𝓝 (x : E n)]
      fun w => ∑ j, logProfile (θ.angle j) (coordNormSq j w) := by
  have hmem : (x : E n) ∈ (extChartAt 𝓘(ℝ, E n) x).target := by
    rw [← extChartAt_opens_apply _ x x]
    exact mem_extChartAt_target x
  filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, E n)) x).mem_nhds hmem] with w hw
  unfold KahlerForm.logDetInChart
  rw [modelConeFormOn_metricInChart θ U hU x hw,
    log_det_modelConeMatrix (hU (extChartAt_opens_target_subset _ x hw))]

/-- **The model cone form is Ricci-flat** on any open subset of the model domain. -/
theorem modelConeFormOn_ricciForm (θ : ConeWeights n) (U : TopologicalSpace.Opens (E n))
    (hU : (U : Set (E n)) ⊆ modelDomain θ) : (modelConeFormOn θ U hU).ricciForm = 0 := by
  funext x
  change -ddbar ((modelConeFormOn θ U hU).logDetInChart x) (extChartAt 𝓘(ℝ, E n) x x) = 0
  rw [extChartAt_opens_apply, ddbar_congr (logDetInChart_modelConeFormOn_eventuallyEq θ U hU x),
    ddbar_logDet_model_eq_zero (hU x.2), neg_zero]

theorem modelConeFormOn_ricciFlat (θ : ConeWeights n) (U : TopologicalSpace.Opens (E n))
    (hU : (U : Set (E n)) ⊆ modelDomain θ) : (modelConeFormOn θ U hU).IsRicciFlat :=
  modelConeFormOn_ricciForm θ U hU

/-- **The model cone form is Ricci-flat on the model domain.** -/
theorem modelConeForm_ricciForm (θ : ConeWeights n) : (ModelConeForm θ).ricciForm = 0 :=
  modelConeFormOn_ricciForm θ _ _

/-- **The model cone form is Ricci-flat** (on `modelDomain θ`, for all cone angles `β_j > 0`). -/
theorem modelConeForm_ricciFlat (θ : ConeWeights n) : (ModelConeForm θ).IsRicciFlat :=
  modelConeForm_ricciForm θ

end ConicalKahler
