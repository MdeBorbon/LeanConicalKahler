module

public import ConicalKahler.Analysis.DDBarLocal
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Complex Hessians of separable radial potentials on `ℂⁿ`

For `j : Fin n` let `coordNormSq j z = |z_j|²`. This file computes the complex Hessian
(the coefficient matrix of `i∂∂̄`, upstream `complexHessian`) of functions of the form

  `Ψ(z) = ∑ⱼ gⱼ(|z_j|²)`,

with each `gⱼ : ℝ → ℝ` of class `C²` near `|z_j|²`. The answer is diagonal:

  `∂²Ψ/∂z_j∂z̄ₖ = δⱼₖ · (gⱼ'(s) + s gⱼ''(s))`,  `s = |z_j|²`

(`coeffMatrix_ddbar_separable`). The scalar `g'(s) + s g''(s)` is `radialCoeff g s`.

The proof uses only upstream identities:

* `complexHessian_normSq` together with `ddbar_comp_holomorphic` for the coordinate projection
  give `∂∂̄|z_j|² = E_{jj}` (`complexHessian_coordNormSq`);
* the coefficients of `i ∂f ∧ ∂̄f` (`coeffMatrix_dWedgeDBar`) give `|z_j|² E_{jj}` for
  `f = |z_j|²` (`coeffMatrix_dWedgeDBar_coordNormSq`);
* the real chain rule `ddbar_comp_real` combines the two.

The two specializations used for the conical model are
`radialCoeff (· ^ β) s = β² s^(β-1)` (so `|z|^(2β)` has Hessian `β² |z|^(2β-2)`) and
`radialCoeff (c + a log ·) s = 0` (so `log |z|²` is pluriharmonic away from `z = 0`).
-/

@[expose] public section

open scoped ContDiff Topology
open Complex Filter ContinuousAlternatingMap Matrix

namespace ConicalKahler

variable {n : ℕ}

/-! ### The coordinate function `|z_j|²` -/

/-- `|z_j|²` as a real function on `ℂⁿ`. -/
noncomputable def coordNormSq (j : Fin n) (z : EuclideanSpace ℂ (Fin n)) : ℝ :=
  ‖z j‖ ^ 2

/-- `Re z_j`, as a real linear functional on `ℂⁿ`. -/
noncomputable def coordRe (j : Fin n) : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ :=
  reCLM.comp ((EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).restrictScalars ℝ)

/-- `Im z_j`, as a real linear functional on `ℂⁿ`. -/
noncomputable def coordIm (j : Fin n) : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ :=
  imCLM.comp ((EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).restrictScalars ℝ)

@[simp]
theorem coordRe_apply (j : Fin n) (z : EuclideanSpace ℂ (Fin n)) : coordRe j z = (z j).re :=
  rfl

@[simp]
theorem coordIm_apply (j : Fin n) (z : EuclideanSpace ℂ (Fin n)) : coordIm j z = (z j).im :=
  rfl

theorem coordNormSq_eq (j : Fin n) (z : EuclideanSpace ℂ (Fin n)) :
    coordNormSq j z = coordRe j z ^ 2 + coordIm j z ^ 2 := by
  simp only [coordNormSq, coordRe_apply, coordIm_apply, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem coordNormSq_nonneg (j : Fin n) (z : EuclideanSpace ℂ (Fin n)) : 0 ≤ coordNormSq j z :=
  sq_nonneg _

theorem coordNormSq_pos {j : Fin n} {z : EuclideanSpace ℂ (Fin n)} (hz : z j ≠ 0) :
    0 < coordNormSq j z := by
  unfold coordNormSq
  positivity

theorem contDiff_coordNormSq (j : Fin n) {m : WithTop ℕ∞} : ContDiff ℝ m (coordNormSq j) := by
  have h : coordNormSq j = fun z => coordRe j z ^ 2 + coordIm j z ^ 2 :=
    funext (coordNormSq_eq j)
  rw [h]
  exact ((coordRe j).contDiff.pow 2).add ((coordIm j).contDiff.pow 2)

theorem hasFDerivAt_coordNormSq (j : Fin n) (z : EuclideanSpace ℂ (Fin n)) :
    HasFDerivAt (coordNormSq j)
      ((2 * coordRe j z) • coordRe j + (2 * coordIm j z) • coordIm j) z := by
  have h : coordNormSq j = fun z => coordRe j z ^ 2 + coordIm j z ^ 2 :=
    funext (coordNormSq_eq j)
  rw [h]
  have hre := (coordRe j).hasFDerivAt.pow 2 (x := z)
  have him := (coordIm j).hasFDerivAt.pow 2 (x := z)
  convert hre.add him using 1
  ext v
  simp

/-! ### `i∂∂̄|z_j|²` -/

/-- The complex-linear projection `z ↦ z_j e_j`. -/
noncomputable def coordProj (j : Fin n) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).smulRight
    (EuclideanSpace.single j 1)

theorem coordProj_apply (j : Fin n) (z : EuclideanSpace ℂ (Fin n)) :
    coordProj j z = z j • EuclideanSpace.single j 1 :=
  rfl

theorem norm_coordProj (j : Fin n) (z : EuclideanSpace ℂ (Fin n)) :
    ‖coordProj j z‖ = ‖z j‖ := by
  rw [coordProj_apply, norm_smul, PiLp.norm_single, norm_one, mul_one]

theorem coordNormSq_eq_comp (j : Fin n) :
    coordNormSq j = (fun w : EuclideanSpace ℂ (Fin n) => ‖w‖ ^ 2) ∘ coordProj j := by
  funext z
  simp [coordNormSq, norm_coordProj]

theorem clmMatrix_coordProj (j : Fin n) :
    EuclideanSpace.clmMatrix (coordProj j) = Matrix.single j j 1 := by
  ext a b
  simp only [EuclideanSpace.clmMatrix, Matrix.of_apply, coordProj_apply, Matrix.single_apply]
  by_cases ha : a = j <;> by_cases hb : b = j
  · subst ha hb; simp
  · subst ha; simp [Ne.symm hb]
  · subst hb; simp [Ne.symm ha]
  · simp [Ne.symm hb, Ne.symm ha]

/-- `i∂∂̄|z_j|² = i dz_j ∧ dz̄_j`: the complex Hessian of `|z_j|²` is the matrix unit `E_{jj}`. -/
theorem complexHessian_coordNormSq (j : Fin n) (z : EuclideanSpace ℂ (Fin n)) :
    complexHessian (coordNormSq j) z = Matrix.single j j 1 := by
  let : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin n)) :=
    InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin n))
  have hf : ContDiffAt ℝ 2 (fun w : EuclideanSpace ℂ (Fin n) => ‖w‖ ^ 2) (coordProj j z) :=
    contDiffAt_id.norm_sq ℝ
  have hψ : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (coordProj j) w :=
    Eventually.of_forall fun w => (coordProj j).differentiableAt
  unfold complexHessian
  rw [coordNormSq_eq_comp, ddbar_comp_holomorphic hψ hf,
    IsOneOne.coeffMatrix_compContinuousLinearMap (isOneOne_ddbar hf)]
  change (EuclideanSpace.clmMatrix (fderiv ℂ (coordProj j) z))ᵀ *
      complexHessian (fun w : EuclideanSpace ℂ (Fin n) => ‖w‖ ^ 2) (coordProj j z) *
      (EuclideanSpace.clmMatrix (fderiv ℂ (coordProj j) z)).map star = _
  rw [complexHessian_normSq, (coordProj j).fderiv, clmMatrix_coordProj, transpose_single,
    mul_one]
  have hmap : (Matrix.single j j (1 : ℂ)).map star = Matrix.single j j 1 := by
    ext a b
    simp only [Matrix.map_apply, Matrix.single_apply]
    split_ifs <;> simp
  rw [hmap, single_mul_single_same, mul_one]

/-- The coefficients of `i ∂f ∧ ∂̄f` for `f = |z_j|²` are `|z_j|² E_{jj}`. -/
theorem coeffMatrix_dWedgeDBar_coordNormSq (j : Fin n) (z : EuclideanSpace ℂ (Fin n)) :
    (dWedgeDBar (fderiv ℝ (coordNormSq j) z)).coeffMatrix =
      Matrix.single j j ((coordNormSq j z : ℝ) : ℂ) := by
  rw [(hasFDerivAt_coordNormSq j z).fderiv, coeffMatrix_dWedgeDBar, coordNormSq_eq]
  ext a b
  simp only [vecMulVec_apply, Matrix.single_apply, _root_.add_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, coordRe_apply, coordIm_apply,
    PiLp.smul_apply, PiLp.single_apply]
  by_cases ha : a = j <;> by_cases hb : b = j
  · subst ha hb
    simp only [ite_true, and_self, mul_one]
    apply Complex.ext <;> simp [pow_two] <;> ring
  · simp [ha, Ne.symm hb]
  · simp [hb, Ne.symm ha]
  · simp [Ne.symm ha]

/-! ### Radial chain rule -/

/-- The radial coefficient `g'(s) + s g''(s)`: the complex Hessian of `z ↦ g(|z|²)` on `ℂ`. -/
noncomputable def radialCoeff (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  deriv g s + s * deriv (deriv g) s

/-- `i∂∂̄ g(|z_j|²) = (g'(s) + s g''(s)) i dz_j ∧ dz̄_j`, `s = |z_j|²`. -/
theorem coeffMatrix_ddbar_comp_coordNormSq {g : ℝ → ℝ} (j : Fin n)
    {z : EuclideanSpace ℂ (Fin n)} (hg : ContDiffAt ℝ 2 g (coordNormSq j z)) :
    (ddbar (fun w => g (coordNormSq j w)) z).coeffMatrix =
      Matrix.single j j ((radialCoeff g (coordNormSq j z) : ℝ) : ℂ) := by
  have hchain := ddbar_comp_real (f := coordNormSq j) hg (contDiff_coordNormSq j).contDiffAt
  change (ddbar (g ∘ coordNormSq j) z).coeffMatrix = _
  rw [hchain, coeffMatrix_add, coeffMatrix_smul, coeffMatrix_smul]
  change deriv g (coordNormSq j z) • complexHessian (coordNormSq j) z + _ = _
  rw [complexHessian_coordNormSq, coeffMatrix_dWedgeDBar_coordNormSq, smul_single, smul_single,
    ← single_add, radialCoeff]
  congr 1
  simp only [Complex.real_smul, mul_one, Complex.ofReal_add, Complex.ofReal_mul]
  ring

/-- **Separable radial potentials.** If `Ψ(z) = ∑ⱼ gⱼ(|z_j|²)` with each `gⱼ` of class `C²` at
`|z_j|²`, then the complex Hessian of `Ψ` at `z` is `diag(gⱼ'(sⱼ) + sⱼ gⱼ''(sⱼ))`. -/
theorem coeffMatrix_ddbar_separable {g : Fin n → ℝ → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hg : ∀ j, ContDiffAt ℝ 2 (g j) (coordNormSq j z)) :
    (ddbar (fun w => ∑ j, g j (coordNormSq j w)) z).coeffMatrix =
      Matrix.diagonal fun j => ((radialCoeff (g j) (coordNormSq j z) : ℝ) : ℂ) := by
  have hF : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      ContDiffAt ℝ 2 (fun w => g j (coordNormSq j w)) z := fun j _ =>
    (hg j).comp z (contDiff_coordNormSq j).contDiffAt
  rw [ddbar_finset_sum Finset.univ hF, coeffMatrix_finset_sum]
  simp_rw [coeffMatrix_ddbar_comp_coordNormSq _ (hg _)]
  exact sum_single_eq_diagonal _

/-! ### Two one-variable computations -/

theorem radialCoeff_id (s : ℝ) : radialCoeff (fun t => t) s = 1 := by
  simp [radialCoeff]

theorem radialCoeff_const (c s : ℝ) : radialCoeff (fun _ => c) s = 0 := by
  simp [radialCoeff]

/-- `(s^β)' + s (s^β)'' = β² s^(β-1)` for `s > 0`. This is the identity
`∂²|z|^(2β)/∂z∂z̄ = β² |z|^(2β-2)`. -/
theorem radialCoeff_rpow (β : ℝ) {s : ℝ} (hs : 0 < s) :
    radialCoeff (fun t => t ^ β) s = β ^ 2 * s ^ (β - 1) := by
  have hd : DifferentiableAt ℝ (fun t : ℝ => t ^ (β - 1)) s :=
    Real.differentiableAt_rpow_const_of_ne _ hs.ne'
  have h2 : deriv (deriv fun t : ℝ => t ^ β) s = β * ((β - 1) * s ^ (β - 1 - 1)) := by
    rw [Real.deriv_rpow_const', deriv_const_mul _ hd, Real.deriv_rpow_const]
  have hpow : s * s ^ (β - 1 - 1) = s ^ (β - 1) := by
    rw [show β - 1 = (β - 1 - 1) + 1 by ring, Real.rpow_add hs, Real.rpow_one]
    ring_nf
  rw [radialCoeff, h2, Real.deriv_rpow_const]
  calc β * s ^ (β - 1) + s * (β * ((β - 1) * s ^ (β - 1 - 1)))
      = β * s ^ (β - 1) + β * (β - 1) * (s * s ^ (β - 1 - 1)) := by ring
    _ = β ^ 2 * s ^ (β - 1) := by rw [hpow]; ring

/-- `c + a log s` has vanishing radial coefficient for `s > 0`: `log |z|²` is pluriharmonic on
`ℂ \ {0}`. -/
theorem radialCoeff_const_add_mul_log (c a : ℝ) {s : ℝ} (hs : 0 < s) :
    radialCoeff (fun t => c + a * Real.log t) s = 0 := by
  have hderiv : deriv (fun t => c + a * Real.log t) =ᶠ[𝓝 s] fun t => a * t⁻¹ := by
    filter_upwards [lt_mem_nhds hs] with t ht
    rw [deriv_const_add, deriv_const_mul _ (Real.differentiableAt_log ht.ne'),
      Real.deriv_log]
  have h1 : deriv (fun t => c + a * Real.log t) s = a * s⁻¹ := hderiv.eq_of_nhds
  have h2 : deriv (deriv fun t => c + a * Real.log t) s = a * -(s ^ 2)⁻¹ := by
    rw [hderiv.deriv_eq, deriv_const_mul _ (differentiableAt_inv hs.ne'), deriv_inv]
  rw [radialCoeff, h1, h2]
  field_simp
  ring

end ConicalKahler
