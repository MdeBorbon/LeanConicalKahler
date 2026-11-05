module

public import ConicalKahler.Sobolev.HarmonicApprox
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The spectral theorem for the Dirichlet problem

Let `Ω ⊆ ℝ^d` be bounded and open, and let `A` be a symmetric, measurable, uniformly elliptic
coefficient field (`CoeffField`; the cone Laplacian is `coneCoeff`). The **Dirichlet solution
operator** `G : L²(Ω) → L²(Ω)` sends `f` to the first component of the unique `u ∈ W^{1,2}_0(Ω)`
with `-div(A ∇u) = f` (Lax–Milgram, `existsUnique_H01_isWeakSolution`).

## Results

* `solutionL`: `f ↦ u`, a bounded linear map `L²(Ω) → W^{1,2}_0(Ω)`.
* `isCompactOperator_dirichletG`: `G` is **compact**. It factors through the compact embedding
  `W^{1,2}_0(Ω) ↪ L²(Ω)` (Rellich, `isCompactOperator_H01_fst`).
* `isSymmetric_dirichletG`: `G` is **symmetric**, since `A` is symmetric.
* `inner_dirichletG_self_nonneg`: `G` is **positive**, and `injective_dirichletG`: `G` is
  **injective** (the fundamental lemma of the calculus of variations).
* **The spectral theorem** (`dirichletG_eigenspaces_dense`, `finiteDimensional_eigenspace_dirichletG`):
  the eigenspaces of `G` span a dense subspace of `L²(Ω)`, and every eigenspace with a nonzero
  eigenvalue is finite-dimensional. This is Mathlib's spectral theorem for compact symmetric
  operators.
* `dirichletG_eigen`: if `G f = μ f` with `f ≠ 0`, then `u = (G f, ∇)` is a **Dirichlet
  eigenfunction**, `u ∈ W^{1,2}_0(Ω)` with `-div(A ∇u) = μ⁻¹ u`. Moreover
  `0 < μ ≤ 4R²/λ`, i.e. the Dirichlet eigenvalue `μ⁻¹` is at least `λ/(4R²)` when
  `Ω ⊆ B̄(x₀, R)`.

So `L²(Ω)` has a complete orthogonal system of Dirichlet eigenfunctions with positive eigenvalues
and finite multiplicities. This is the input used in the paper's Proposition 2.5 (and Lemma 3.1
on the link). The proof of Proposition 2.5 itself is **not** formalised here (see
`PAPER_REVIEW.md` V9 and §C).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set Module
open scoped ContDiff ENNReal

namespace ConicalKahler.Sobolev

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

variable [NeZero d]

variable (c : CoeffField (EuclideanSpace ℝ (Fin d)) volume) {Ω : Set (EuclideanSpace ℝ (Fin d))}
  {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ}

theorem CoeffField.IsWeakSolution.add {f₁ f₂ : Lp ℝ 2 (volume.restrict Ω)} {v₁ v₂ : L2Pair volume Ω}
    (h₁ : c.IsWeakSolution f₁ v₁) (h₂ : c.IsWeakSolution f₂ v₂) :
    c.IsWeakSolution (f₁ + f₂) (v₁ + v₂) := by
  refine ⟨(W12 volume Ω).add_mem h₁.1 h₂.1, fun φ hφ => ?_⟩
  rw [ContinuousLinearMap.map_add₂, h₁.2 φ hφ, h₂.2 φ hφ, inner_add_left]

theorem CoeffField.IsWeakSolution.smul {f : Lp ℝ 2 (volume.restrict Ω)} {v : L2Pair volume Ω}
    (h : c.IsWeakSolution f v) (r : ℝ) : c.IsWeakSolution (r • f) (r • v) := by
  refine ⟨(W12 volume Ω).smul_mem r h.1, fun φ hφ => ?_⟩
  rw [ContinuousLinearMap.map_smul₂, h.2 φ hφ, real_inner_smul_left, smul_eq_mul]

/-- The Dirichlet form is symmetric. -/
theorem CoeffField.dirichletForm_comm (v w : L2Pair volume Ω) :
    c.dirichletForm Ω v w = c.dirichletForm Ω w v := by
  rw [CoeffField.dirichletForm_apply, CoeffField.dirichletForm_apply, CoeffField.inner_mulOp, CoeffField.inner_mulOp]
  exact integral_congr_ae (Eventually.of_forall fun x => by
    change ⟪c.A x (v.snd x), w.snd x⟫_ℝ = ⟪c.A x (w.snd x), v.snd x⟫_ℝ
    rw [c.symm, real_inner_comm])

variable (hR : 0 ≤ R) (hΩ : Ω ⊆ Metric.closedBall x₀ R)
include hR hΩ

/-- The solution of the Dirichlet problem: the unique `u ∈ W^{1,2}_0(Ω)` with
`-div(A ∇u) = f`. -/
def CoeffField.solution (f : Lp ℝ 2 (volume.restrict Ω)) : H01 volume Ω :=
  (c.existsUnique_H01_isWeakSolution hR hΩ f).exists.choose

theorem CoeffField.solution_spec (f : Lp ℝ 2 (volume.restrict Ω)) :
    c.IsWeakSolution f (c.solution hR hΩ f) :=
  (c.existsUnique_H01_isWeakSolution hR hΩ f).exists.choose_spec

theorem CoeffField.eq_solution {f : Lp ℝ 2 (volume.restrict Ω)} {w : H01 volume Ω}
    (hw : c.IsWeakSolution f w) : w = c.solution hR hΩ f :=
  (c.existsUnique_H01_isWeakSolution hR hΩ f).unique hw (c.solution_spec hR hΩ f)

/-- **The solution operator** `f ↦ u` as a bounded linear map `L²(Ω) → W^{1,2}_0(Ω)`. -/
def CoeffField.solutionL : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] H01 volume Ω :=
  LinearMap.mkContinuous
    { toFun := c.solution hR hΩ
      map_add' := fun f g => (c.eq_solution hR hΩ (w := c.solution hR hΩ f + c.solution hR hΩ g)
        ((c.solution_spec hR hΩ f).add c (c.solution_spec hR hΩ g))).symm
      map_smul' := fun r f => (c.eq_solution hR hΩ (w := r • c.solution hR hΩ f)
        ((c.solution_spec hR hΩ f).smul c r)).symm }
    ((4 * R ^ 2 + 2 * R) / c.lam) fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      have h1 := CoeffField.lam_mul_norm_fst_le hR hΩ (c.solution hR hΩ f).2 (c.solution_spec hR hΩ f)
      have h2 := CoeffField.lam_mul_norm_snd_le hR hΩ (c.solution hR hΩ f).2 (c.solution_spec hR hΩ f)
      have h3 := norm_le_norm_fst_add_norm_snd ((c.solution hR hΩ f : L2Pair volume Ω))
      have hl := c.lam_pos
      have hn : ‖c.solution hR hΩ f‖ = ‖(c.solution hR hΩ f : L2Pair volume Ω)‖ := rfl
      rw [hn, div_mul_eq_mul_div, le_div_iff₀ hl]
      nlinarith

theorem CoeffField.solutionL_apply (f : Lp ℝ 2 (volume.restrict Ω)) :
    c.solutionL hR hΩ f = c.solution hR hΩ f := rfl

/-- **The Dirichlet solution operator** `G : L²(Ω) → L²(Ω)`, `f ↦ u`. -/
def CoeffField.dirichletG : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  (H01.fstL Ω).comp (c.solutionL hR hΩ)

theorem CoeffField.dirichletG_apply (f : Lp ℝ 2 (volume.restrict Ω)) :
    c.dirichletG hR hΩ f = (c.solution hR hΩ f : L2Pair volume Ω).fst := rfl

omit hR hΩ in
/-- **`G` is compact** (Rellich). -/
theorem CoeffField.isCompactOperator_dirichletG (hR : 0 ≤ R) (hΩ : Ω ⊆ Metric.closedBall x₀ R)
    (hΩo : IsOpen Ω) : IsCompactOperator (c.dirichletG hR hΩ) :=
  (isCompactOperator_H01_fst hΩo (Metric.isBounded_closedBall.subset hΩ)).comp_clm
    (c.solutionL hR hΩ)

/-- `⟨G f, g⟩ = ∫ ⟨A ∇u, ∇w⟩` for `u = Gf`, `w = Gg`. -/
theorem CoeffField.inner_dirichletG (f g : Lp ℝ 2 (volume.restrict Ω)) :
    ⟪c.dirichletG hR hΩ f, g⟫_ℝ =
      c.dirichletForm Ω (c.solution hR hΩ g) (c.solution hR hΩ f) := by
  rw [dirichletG_apply, real_inner_comm,
    (c.solution_spec hR hΩ g).forall_H01 (c.solution hR hΩ f).2]

/-- **`G` is symmetric.** -/
theorem CoeffField.isSymmetric_dirichletG : (c.dirichletG hR hΩ).IsSymmetric := by
  intro f g
  change ⟪c.dirichletG hR hΩ f, g⟫_ℝ = ⟪f, c.dirichletG hR hΩ g⟫_ℝ
  rw [CoeffField.inner_dirichletG, real_inner_comm (c.dirichletG hR hΩ g) f,
    CoeffField.inner_dirichletG, CoeffField.dirichletForm_comm]

/-- **`G` is positive:** `⟨G f, f⟩ ≥ λ ‖∇u‖² ≥ 0`. -/
theorem CoeffField.lam_mul_norm_sq_le_inner_dirichletG (f : Lp ℝ 2 (volume.restrict Ω)) :
    c.lam * ‖(c.solution hR hΩ f : L2Pair volume Ω).snd‖ ^ 2 ≤ ⟪c.dirichletG hR hΩ f, f⟫_ℝ := by
  rw [CoeffField.inner_dirichletG, CoeffField.dirichletForm_apply]
  exact c.lam_mul_norm_sq_le Ω _

theorem CoeffField.inner_dirichletG_self_nonneg (f : Lp ℝ 2 (volume.restrict Ω)) :
    0 ≤ ⟪c.dirichletG hR hΩ f, f⟫_ℝ :=
  (mul_nonneg c.lam_pos.le (sq_nonneg _)).trans (c.lam_mul_norm_sq_le_inner_dirichletG hR hΩ f)

omit hR hΩ in
/-- An `L²(Ω)` function orthogonal to all test functions vanishes (`Ω` open). -/
theorem CoeffField.eq_zero_of_forall_inner_graph {Ω : Set 𝔼} (hΩo : IsOpen Ω)
    {f : Lp ℝ 2 (volume.restrict Ω)}
    (h : ∀ (φ : 𝔼 → ℝ) (hφ : IsTestFn Ω φ), ⟪f, (graph volume Ω hφ).fst⟫_ℝ = 0) : f = 0 := by
  have hloc : LocallyIntegrable (fun x => f x) (volume.restrict Ω) :=
    (Lp.memLp f).locallyIntegrable (by norm_num)
  have hae : ∀ᵐ x ∂(volume : Measure 𝔼), x ∈ Ω → f x = 0 := by
    apply hΩo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    · exact locallyIntegrableOn_of_locallyIntegrable_restrict hloc
    · intro φ hφs hφc hφΩ
      have hφ : IsTestFn Ω φ := ⟨hφs, hφc, hφΩ⟩
      have h0 := h φ hφ
      rw [CoeffField.inner_graph_fst] at h0
      have hz : ∀ x ∉ Ω, φ x • f x = 0 := fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport (fun h' => hx (hφΩ h'))]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
      simpa [smul_eq_mul, mul_comm] using h0
  refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
  rw [EventuallyEq, ae_restrict_iff' hΩo.measurableSet]
  filter_upwards [hae] with x hx hxΩ
  exact hx hxΩ

/-- **`G` is injective.** -/
theorem CoeffField.injective_dirichletG (hΩo : IsOpen Ω) : Function.Injective (c.dirichletG hR hΩ) := by
  refine (injective_iff_map_eq_zero (c.dirichletG hR hΩ)).mpr fun f hGf => ?_
  have hGf' : (c.solution hR hΩ f : L2Pair volume Ω).fst = 0 := hGf
  set u := c.solution hR hΩ f
  have hE := (c.solution_spec hR hΩ f).forall_H01 u.2
  rw [hGf', inner_zero_right, CoeffField.dirichletForm_apply] at hE
  have hco := c.lam_mul_norm_sq_le Ω (u : L2Pair volume Ω).snd
  rw [hE] at hco
  have hsnd : (u : L2Pair volume Ω).snd = 0 := by
    have : ‖(u : L2Pair volume Ω).snd‖ ^ 2 ≤ 0 :=
      (mul_le_mul_iff_of_pos_left c.lam_pos).mp (by simpa using hco)
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm this (sq_nonneg _)))
  have hu0 : (u : L2Pair volume Ω) = 0 := L2Pair.ext volume hGf' hsnd
  refine eq_zero_of_forall_inner_graph hΩo fun φ hφ => ?_
  rw [← (c.solution_spec hR hΩ f).2 φ hφ]
  change c.dirichletForm Ω (u : L2Pair volume Ω) _ = 0
  rw [hu0, map_zero, _root_.zero_apply]

/-- **The spectral theorem for the Dirichlet problem:** the eigenspaces of the solution operator
span a dense subspace of `L²(Ω)`. -/
theorem CoeffField.dirichletG_eigenspaces_dense (hΩo : IsOpen Ω) :
    (⨆ μ, Module.End.eigenspace
      ((c.dirichletG hR hΩ : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Lp ℝ 2 (volume.restrict Ω)) :
        Module.End ℝ (Lp ℝ 2 (volume.restrict Ω))) μ)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (c.isCompactOperator_dirichletG hR hΩ hΩo) (c.isSymmetric_dirichletG hR hΩ)

/-- **Finite multiplicities:** every eigenspace of `G` with nonzero eigenvalue is
finite-dimensional. -/
theorem CoeffField.finiteDimensional_eigenspace_dirichletG (hΩo : IsOpen Ω) {μ : ℝ} (hμ : μ ≠ 0) :
    FiniteDimensional ℝ (Module.End.eigenspace (c.dirichletG hR hΩ).toLinearMap μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace (c.isCompactOperator_dirichletG hR hΩ hΩo) μ hμ

/-- **Eigenvectors of `G` are Dirichlet eigenfunctions.** If `G f = μ f` with `f ≠ 0`, then
`u = solution f ∈ W^{1,2}_0(Ω)` solves `-div(A ∇u) = μ⁻¹ u`, and `0 < μ` with `λ μ ≤ 4R²`; so the
Dirichlet eigenvalue `μ⁻¹` is at least `λ / (4R²)`. -/
theorem CoeffField.dirichletG_eigen (hΩo : IsOpen Ω) {μ : ℝ} {f : Lp ℝ 2 (volume.restrict Ω)} (hf : f ≠ 0)
    (hGf : c.dirichletG hR hΩ f = μ • f) :
    0 < μ ∧ c.lam * μ ≤ 4 * R ^ 2 ∧
      c.IsWeakSolution (μ⁻¹ • (c.solution hR hΩ f : L2Pair volume Ω).fst) (c.solution hR hΩ f) := by
  set u := c.solution hR hΩ f
  have hfst : (u : L2Pair volume Ω).fst = μ • f := hGf
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hGf
    exact hf (c.injective_dirichletG hR hΩ hΩo (hGf.trans (map_zero _).symm))
  have hf0 : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hinner : ⟪c.dirichletG hR hΩ f, f⟫_ℝ = μ * ‖f‖ ^ 2 := by
    rw [hGf, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hpos := c.lam_mul_norm_sq_le_inner_dirichletG hR hΩ f
  rw [hinner] at hpos
  have hl := c.lam_pos
  have hμpos : 0 < μ := by
    rcases lt_or_gt_of_ne hμ0 with h | h
    · exfalso
      have h1 : μ * ‖f‖ ^ 2 < 0 := mul_neg_of_neg_of_pos h (by positivity)
      have h2 : 0 ≤ c.lam * ‖(u : L2Pair volume Ω).snd‖ ^ 2 := by positivity
      linarith
    · exact h
  refine ⟨hμpos, ?_, ?_⟩
  · have hP := norm_fst_le_of_mem_H01 hR hΩ u.2
    rw [hfst, norm_smul, Real.norm_eq_abs, abs_of_pos hμpos] at hP
    have h1 : (μ * ‖f‖) ^ 2 ≤ 4 * R ^ 2 * ‖(u : L2Pair volume Ω).snd‖ ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hP 2
      nlinarith
    have h2 : c.lam * (μ * ‖f‖) ^ 2 ≤ 4 * R ^ 2 * (μ * ‖f‖ ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left h1 hl.le]
    have h3 : (c.lam * μ) * (μ * ‖f‖ ^ 2) ≤ (4 * R ^ 2) * (μ * ‖f‖ ^ 2) := by nlinarith
    exact le_of_mul_le_mul_right h3 (by positivity)
  · have hf' : f = μ⁻¹ • (u : L2Pair volume Ω).fst := by
      rw [hfst, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    have hsol := c.solution_spec hR hΩ f
    convert hsol using 2
    exact hf'.symm

end ConicalKahler.Sobolev
