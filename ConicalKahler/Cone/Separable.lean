module

public import ConicalKahler.Analysis.RadialCalculus
public import ConicalKahler.Cone.Weights
public import ConicalKahler.Manifold.OpenSubset
public import CalabiYau.Geometry.Kahler.Ricci

/-!
# Separable radial Kähler forms

For one-variable profiles `g_j` and an open set `U ⊆ ℂⁿ` on which each `g_j` is smooth at
`|z_j|²` and has positive radial coefficient `w_j = g_j'(s) + s g_j''(s)`, the form

  `i∂∂̄ ∑_j g_j(|z_j|²) = i ∑_j w_j(|z_j|²) dz_j ∧ dz̄_j`

is a Kähler form on `U` (`SeparableProfile.kahlerForm`). Its Ricci form is again diagonal:
`Ric = -i ∑_j radialCoeff (log w_j)(|z_j|²) dz_j ∧ dz̄_j` (`SeparableProfile.ricciForm_coeffMatrix`).

The model cone form `ModelConeForm θ` has this shape (`g_j(s) = s^β_j` or `s`). It is kept as its
own definition. This file is used to build *other* metrics, for example metrics that satisfy the
quasi-isometric cone condition without being flat cones
(`ConicalKahler.Cone.QuasiIsometricExample`).
-/

@[expose] public section

open scoped Manifold ContDiff Topology ComplexOrder
open Filter ContinuousAlternatingMap

namespace ConicalKahler

variable {n : ℕ}

/-- The separable potential `∑_j g_j(|z_j|²)`. -/
noncomputable def separablePotential (g : Fin n → ℝ → ℝ) (z : E n) : ℝ :=
  ∑ j, g j (coordNormSq j z)

/-- Profiles `g_j` defining a Kähler form `i∂∂̄ ∑_j g_j(|z_j|²)` on the open set `U`. -/
structure SeparableProfile (n : ℕ) (U : TopologicalSpace.Opens (E n)) where
  /-- The one-variable profiles. -/
  g : Fin n → ℝ → ℝ
  smooth : ∀ z ∈ U, ∀ j, ContDiffAt ℝ ∞ (g j) (coordNormSq j z)
  pos : ∀ z ∈ U, ∀ j, 0 < radialCoeff (g j) (coordNormSq j z)

namespace SeparableProfile

variable {U : TopologicalSpace.Opens (E n)} (P : SeparableProfile n U)

/-- The diagonal coefficients `w_j(z) = radialCoeff g_j (|z_j|²)`. -/
noncomputable def weight (z : E n) (j : Fin n) : ℝ :=
  radialCoeff (P.g j) (coordNormSq j z)

/-- The diagonal Hermitian matrix `diag(w_j(z))`. -/
noncomputable def matrix (z : E n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun j => (P.weight z j : ℂ)

theorem contDiffAt_potential {z : E n} (hz : z ∈ U) :
    ContDiffAt ℝ ∞ (separablePotential P.g) z :=
  ContDiffAt.sum fun j _ => (P.smooth z hz j).comp z (contDiff_coordNormSq j).contDiffAt

theorem contDiffOn_potential : ContDiffOn ℝ ∞ (separablePotential P.g) U := fun _ hz =>
  (P.contDiffAt_potential hz).contDiffWithinAt

theorem complexHessian_potential {z : E n} (hz : z ∈ U) :
    complexHessian (separablePotential P.g) z = P.matrix z := by
  unfold complexHessian
  change (ddbar (fun w => ∑ j, P.g j (coordNormSq j w)) z).coeffMatrix = _
  rw [coeffMatrix_ddbar_separable fun j => (P.smooth z hz j).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))]
  rfl

theorem matrix_posDef {z : E n} (hz : z ∈ U) : (P.matrix z).PosDef :=
  Matrix.PosDef.diagonal fun j => by
    simpa [weight] using P.pos z hz j

/-- **The separable Kähler form** `i∂∂̄ ∑_j g_j(|z_j|²)` on `U`. -/
noncomputable def kahlerForm : KahlerForm n U where
  toFormField := mddbar n fun x : U => separablePotential P.g x
  isSmooth' := isSmooth_mddbar (contMDiff_opens_of_contDiffOn _ P.contDiffOn_potential)
  isPositive' := by
    intro x
    rw [mddbar_opens, isPositive_iff]
    refine ⟨isOneOne_ddbar ((P.contDiffAt_potential x.2).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))), ?_⟩
    change (complexHessian (separablePotential P.g) x).PosDef
    rw [P.complexHessian_potential x.2]
    exact P.matrix_posDef x.2
  isClosed' := isClosed_mddbar (contMDiff_opens_of_contDiffOn _ P.contDiffOn_potential)

theorem kahlerForm_apply (x : U) : P.kahlerForm x = ddbar (separablePotential P.g) x :=
  mddbar_opens _ _ x

theorem kahlerForm_coeffMatrix (x : U) : (P.kahlerForm x).coeffMatrix = P.matrix x := by
  rw [kahlerForm_apply]
  exact P.complexHessian_potential x.2

/-- In the chart of `U` at any point, the local metric is `diag(w_j(z))` on the whole chart
target. -/
theorem kahlerForm_metricInChart (x : U) {z : E n}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E n) x).target) :
    P.kahlerForm.metricInChart x z = P.matrix z := by
  change (FormField.chartRep (mddbar n fun x : U => separablePotential P.g x) x z).coeffMatrix = _
  rw [chartRep_mddbar_opens P.contDiffOn_potential x hz]
  exact P.complexHessian_potential (extChartAt_opens_target_subset _ x hz)

/-- `ω(v, Jv) = 2 ∑_j w_j |v_j|²`. -/
theorem kahlerForm_apply_I_smul (x : U) (v : E n) :
    P.kahlerForm x ![v, Complex.I • v] = 2 * ∑ j, P.weight x j * Complex.normSq (v j) := by
  rw [(P.kahlerForm.isOneOne x).apply_I_smul, kahlerForm_coeffMatrix]
  congr 1
  simp only [matrix, Matrix.diagonal_apply]
  have h : ∀ j, (∑ k, (if j = k then (P.weight x j : ℂ) else 0) * v j * star (v k)) =
      ((P.weight x j * Complex.normSq (v j) : ℝ) : ℂ) := fun j => by
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
    simp only [ite_true, Complex.ofReal_mul]
    rw [Complex.normSq_eq_conj_mul_self, mul_assoc, mul_comm (starRingEnd ℂ (v j))]
    rfl
  simp_rw [h]
  rw [← Complex.ofReal_sum, Complex.ofReal_re]

/-! ### The Ricci form -/

theorem log_det_matrix {z : E n} (hz : z ∈ U) :
    Real.log (RCLike.re (P.matrix z).det) =
      ∑ j, Real.log (radialCoeff (P.g j) (coordNormSq j z)) := by
  have hdet : (P.matrix z).det = ((∏ j, P.weight z j : ℝ) : ℂ) := by
    simp [matrix, Matrix.det_diagonal]
  rw [hdet, RCLike.re_to_complex, Complex.ofReal_re]
  exact Real.log_prod (fun j _ => (P.pos z hz j).ne')

/-- Near each point, `log det g` in the chart is `∑_j log w_j(|z_j|²)`. -/
theorem logDetInChart_eventuallyEq (x : U) :
    P.kahlerForm.logDetInChart x =ᶠ[𝓝 (x : E n)]
      fun w => ∑ j, Real.log (radialCoeff (P.g j) (coordNormSq j w)) := by
  have hmem : (x : E n) ∈ (extChartAt 𝓘(ℝ, E n) x).target := by
    rw [← extChartAt_opens_apply _ x x]
    exact mem_extChartAt_target x
  filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, E n)) x).mem_nhds hmem] with w hw
  unfold KahlerForm.logDetInChart
  rw [P.kahlerForm_metricInChart x hw, P.log_det_matrix (extChartAt_opens_target_subset _ x hw)]

/-- **The Ricci form of a separable Kähler form** is diagonal:
`Ric_{jk̄} = -δ_{jk} radialCoeff (log w_j)(|z_j|²)`. The hypothesis is that each `log w_j` is
`C²` at `|x_j|²`. -/
theorem ricciForm_coeffMatrix (x : U)
    (hlog : ∀ j, ContDiffAt ℝ 2 (fun s => Real.log (radialCoeff (P.g j) s)) (coordNormSq j x)) :
    (P.kahlerForm.ricciForm x).coeffMatrix =
      -Matrix.diagonal fun j =>
        ((radialCoeff (fun s => Real.log (radialCoeff (P.g j) s)) (coordNormSq j x) : ℝ) : ℂ) := by
  change (-ddbar (P.kahlerForm.logDetInChart x) (extChartAt 𝓘(ℝ, E n) x x)).coeffMatrix = _
  rw [extChartAt_opens_apply, ddbar_congr (P.logDetInChart_eventuallyEq x), coeffMatrix_neg,
    coeffMatrix_ddbar_separable hlog]

end SeparableProfile

end ConicalKahler
