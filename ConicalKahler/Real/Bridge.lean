module

public import ConicalKahler.Real.Product
public import ConicalKahler.Cone.Model

/-!
# The bridge between the Kähler models and the paper's real model

The project's Kähler model on `ℂ^N` with cone weights `θ` has Hermitian form
`q_θ(z; v) = ∑_j w_j(z) |v_j|²`, where `w_j = β_j² |z_j|^{2β_j - 2}` on a cone direction and
`w_j = 1` on a smooth direction. Its Riemannian metric is `g(v, v) = ω_θ(v, Jv) = 2 q_θ(z; v)`.

The paper's real model has one cone factor for each cone direction of `θ` (`θ.ConeIdx`), and two
real coordinates `(Re z_j, Im z_j)` for each smooth direction (`Fin 2 × θ.SmoothIdx`). The map
`θ.realChart` is

* `z_j ↦ |z_j|^{β_j - 1} z_j` (`realConeChart`, so `r_j = |z_j|^{β_j}` with the same angle) on a
  cone direction;
* `z_j ↦ (Re z_j, Im z_j)` on a smooth direction.

## Main results

* `modelConeQuadratic_eq_productConeMetric`: `q_θ(z; v) = g_paper(Φ z; DΦ(z) v)` on the model
  domain. The Hermitian form of the Kähler model is the pull-back of the paper's metric.
* `modelConeForm_apply_I_smul_eq_two_mul`: the Riemannian metric `ω_θ(v, Jv)` of the Kähler model
  is **twice** the pull-back of the paper's metric. This is the factor of `2` in the normalisation
  dictionary (`ROADMAP.md`).
* `fderiv_realChart_cone`: the cone components of `realChartDeriv` are the derivatives of the cone
  components of `realChart`. The smooth components are `ℝ`-linear (`realChart_eucl`,
  `realChartDeriv_eucl`).
-/

@[expose] public section

namespace ConicalKahler

variable {N : ℕ}

namespace ConeWeights

/-- The cone directions of `θ`. -/
abbrev ConeIdx (θ : ConeWeights N) : Type := {j : Fin N // (θ.angle j).isSome}

/-- The smooth directions of `θ`. -/
abbrev SmoothIdx (θ : ConeWeights N) : Type := {j : Fin N // ¬ (θ.angle j).isSome}

/-- The cone angle of a cone direction. -/
def coneAngleOf (θ : ConeWeights N) (a : θ.ConeIdx) : ConeAngle :=
  (θ.angle a.1).get a.2

theorem angle_coneIdx (θ : ConeWeights N) (a : θ.ConeIdx) :
    θ.angle a.1 = some (θ.coneAngleOf a) :=
  (Option.some_get a.2).symm

theorem angle_smoothIdx (θ : ConeWeights N) (j : θ.SmoothIdx) : θ.angle j.1 = none :=
  Option.not_isSome_iff_eq_none.mp j.2

/-- The paper's real model attached to `θ`. -/
abbrev RealModel (θ : ConeWeights N) : Type := RealConeModel θ.ConeIdx (Fin 2 × θ.SmoothIdx)

/-- **The paper's real coordinates of a point of the Kähler model.** -/
noncomputable def realChart (θ : ConeWeights N) (z : E N) : θ.RealModel :=
  RealConeModel.ofCones (fun a => realConeChart (θ.coneAngleOf a).beta (z a.1))
    fun ij => ![(z ij.2.1).re, (z ij.2.1).im] ij.1

/-- The derivative of `realChart` at `z` in the direction `v`, componentwise. -/
noncomputable def realChartDeriv (θ : ConeWeights N) (z v : E N) : θ.RealModel :=
  RealConeModel.ofCones (fun a => realConeChartDeriv (θ.coneAngleOf a).beta (z a.1) (v a.1))
    fun ij => ![(v ij.2.1).re, (v ij.2.1).im] ij.1

@[simp] theorem realChart_cone (θ : ConeWeights N) (z : E N) (a : θ.ConeIdx) :
    (θ.realChart z).cone a = realConeChart (θ.coneAngleOf a).beta (z a.1) := by
  simp [realChart]

@[simp] theorem realChart_eucl (θ : ConeWeights N) (z : E N) (ij : Fin 2 × θ.SmoothIdx) :
    (θ.realChart z).eucl ij = ![(z ij.2.1).re, (z ij.2.1).im] ij.1 := by
  simp [realChart]

@[simp] theorem realChartDeriv_cone (θ : ConeWeights N) (z v : E N) (a : θ.ConeIdx) :
    (θ.realChartDeriv z v).cone a = realConeChartDeriv (θ.coneAngleOf a).beta (z a.1) (v a.1) := by
  simp [realChartDeriv]

@[simp] theorem realChartDeriv_eucl (θ : ConeWeights N) (z v : E N) (ij : Fin 2 × θ.SmoothIdx) :
    (θ.realChartDeriv z v).eucl ij = ![(v ij.2.1).re, (v ij.2.1).im] ij.1 := by
  simp [realChartDeriv]

/-- The cone components of `realChartDeriv` are derivatives. -/
theorem fderiv_realChart_cone (θ : ConeWeights N) {z : E N} (a : θ.ConeIdx) (hz : z a.1 ≠ 0)
    (v : E N) :
    fderiv ℝ (fun w : E N => (θ.realChart w).cone a) z v = (θ.realChartDeriv z v).cone a := by
  let P : E N →L[ℝ] ℂ := (EuclideanSpace.proj (𝕜 := ℂ) a.1).restrictScalars ℝ
  have hP : HasFDerivAt (fun w : E N => w a.1) P z := P.hasFDerivAt
  have h := (hasFDerivAt_realConeChart (θ.coneAngleOf a).beta hz).comp z hP
  have hfun : (fun w : E N => (θ.realChart w).cone a) =
      realConeChart (θ.coneAngleOf a).beta ∘ fun w : E N => w a.1 := by
    funext w
    simp
  rw [hfun, h.fderiv, ContinuousLinearMap.comp_apply,
    ← (hasFDerivAt_realConeChart (θ.coneAngleOf a).beta hz).fderiv,
    realChartDeriv_cone, ← fderiv_realConeChart_apply _ hz]
  rfl

/-- **The Hermitian form of the Kähler model is the pull-back of the paper's metric:**
`q_θ(z; v) = g_paper(Φ z; DΦ(z) v)` on the model domain. -/
theorem modelConeQuadratic_eq_productConeMetric (θ : ConeWeights N) {z : E N}
    (hz : z ∈ modelDomain θ) (v : E N) :
    modelConeQuadratic θ z v =
      productConeMetric θ.coneAngleOf (θ.realChart z) (θ.realChartDeriv z v) := by
  rw [modelConeQuadratic, productConeMetric,
    ← Fintype.sum_subtype_add_sum_subtype (fun j => (θ.angle j).isSome)]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    have hza : z a.1 ≠ 0 := hz a.1 _ (θ.angle_coneIdx a)
    rw [modelWeight_of_some (θ.angle_coneIdx a), realChart_cone, realChartDeriv_cone,
      ← fderiv_realConeChart_apply _ hza, ← transverseConeMetric_eq_paperConeMetric _ hza,
      transverseConeMetric]
  · rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [modelWeight_of_none (θ.angle_smoothIdx j), one_mul, Fin.sum_univ_two,
      Complex.normSq_apply]
    simp only [realChartDeriv_eucl]
    simp
    ring

/-- **The factor of `2`.** The Riemannian metric `ω_θ(v, Jv)` of the Kähler model is twice the
pull-back of the paper's metric `g = ∑_a (dr_a² + β_a² r_a² dθ_a²) + ds²`. -/
theorem modelConeForm_apply_I_smul_eq_two_mul (θ : ConeWeights N) (x : modelDomain θ)
    (v : E N) :
    ModelConeForm θ x ![v, Complex.I • v] =
      2 * productConeMetric θ.coneAngleOf (θ.realChart x) (θ.realChartDeriv x v) := by
  rw [modelConeForm_apply_I_smul, modelConeQuadratic_eq_productConeMetric θ x.2]

end ConeWeights

end ConicalKahler
