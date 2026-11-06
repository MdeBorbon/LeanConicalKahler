module

public import ConicalKahler.Sobolev.Divergence
public import ConicalKahler.Sobolev.Capacity
public import ConicalKahler.Sobolev.HarmonicApprox

/-!
# Classical solutions on the regular part are weak solutions

Let `S = ⋃_a {r_a = 0}` be the singular set of the real cone model (`coneSingular`). A function `u`
that is `C¹` on `Ω \ S` and whose values and classical gradient are square integrable on `Ω`
defines the pair `(u, ∇u)` (`classicalPair`). This file shows:

* `integral_mul_fderiv_eq_neg_of_contDiffOn`: integration by parts against a test function, for
  a function that is only `C¹` on an open set containing the support of the test function.
* `mem_W12_of_regular`: **removability of `S` for `W^{1,2}`.** A pair `(u, G) ∈ L²(Ω) × L²(Ω; ℝ^d)`
  that satisfies the weak-gradient identity against test functions supported in `Ω \ S` satisfies
  it against all test functions on `Ω`. The proof reuses the density of regular test functions
  (`dense_testSubmodule_regular`, logarithmic cut-offs: `S` has codimension two).
* `classicalPair_mem_W12`: hence `(u, ∇u) ∈ W^{1,2}(Ω)`. No condition at `S` is needed beyond
  square integrability.
* `isWeakSolution_of_classical`: for any coefficient field `A`, if the flux `V = A ∇u` is `C¹` on
  `Ω \ S` and `-div V = f` there, then `u` is a weak solution of `-div(A∇u) = f` on `Ω`.
* `cone_isWeakSolution_of_classical`: **for the cone Laplacian**, if `u` is `C²` on `Ω \ S`,
  `(u, ∇u)` is square integrable, and `-Δu = f` on `Ω \ S` for the paper's Laplacian in polar
  coordinates (`paperLaplacian`), then `u` is a weak solution of `-div(g⁻¹ ∇u) = f` on `Ω`. This
  combines the above with `divergence_coneInvOp_gradient` (Milestone 10).
* `classical_of_isWeakSolution`, `cone_classical_of_isWeakSolution`: **the converse for functions
  that are `C²` off `S`**: such a weak solution satisfies the equation pointwise on the regular
  part (fundamental lemma of the calculus of variations). The smoothness off `S` is assumed; interior
  regularity of weak solutions is not proved.
* `eq_of_isWeakSolution_of_sub_mem_H01`: **energy uniqueness.** Two weak solutions with the same
  right-hand side on a bounded domain whose difference lies in `W^{1,2}_0(Ω)` are equal. This is the
  replacement for the maximum principle (paper, Lemma 3.2) in the proof of Lemma 3.3
  (`PAPER_REVIEW.md` S2).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set
open scoped ContDiff ENNReal

namespace ConicalKahler.Sobolev

/-! ### Integration by parts on an open set -/

section General

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {μ : Measure F}

/-- A function continuous on an open set `U`, times a continuous function supported in `U`, is
continuous. -/
theorem continuous_mul_of_continuousOn {U : Set F} (hU : IsOpen U) {g ψ : F → ℝ}
    (hg : ContinuousOn g U) (hψ : Continuous ψ) (hsupp : tsupport ψ ⊆ U) :
    Continuous fun x => g x * ψ x :=
  (hg.mul hψ.continuousOn).continuous_of_tsupport_subset hU (tsupport_mul_subset_right.trans hsupp)

theorem integrable_mul_of_continuousOn [IsFiniteMeasureOnCompacts μ] {U : Set F} (hU : IsOpen U)
    {g ψ : F → ℝ} (hg : ContinuousOn g U) (hψ : Continuous ψ) (hsupp : tsupport ψ ⊆ U)
    (hψc : HasCompactSupport ψ) : Integrable (fun x => g x * ψ x) μ :=
  (continuous_mul_of_continuousOn hU hg hψ hsupp).integrable_of_hasCompactSupport hψc.mul_left

variable [μ.IsAddHaarMeasure]

/-- **Integration by parts for a function that is `C¹` only on an open set `U`**, against a test
function supported in `U`: `∫ u ∂_w φ = -∫ (∂_w u) φ`. -/
theorem integral_mul_fderiv_eq_neg_of_contDiffOn {U : Set F} (hU : IsOpen U) {u : F → ℝ}
    (hu : ContDiffOn ℝ 1 u U) {φ : F → ℝ} (hφ : IsTestFn U φ) (w : F) :
    ∫ x, u x * fderiv ℝ φ x w ∂μ = -∫ x, fderiv ℝ u x w * φ x ∂μ := by
  have hDu : ContinuousOn (fun x => fderiv ℝ u x w) U :=
    (hu.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
  · exact integrable_mul_of_continuousOn hU hDu hφ.continuous hφ.tsupport_subset
      hφ.hasCompactSupport
  · exact integrable_mul_of_continuousOn hU hu.continuousOn (hφ.continuous_fderiv_apply w)
      ((tsupport_fderiv_apply_subset ℝ w).trans hφ.tsupport_subset)
      (hφ.hasCompactSupport_fderiv_apply w)
  · exact integrable_mul_of_continuousOn hU hu.continuousOn hφ.continuous hφ.tsupport_subset
      hφ.hasCompactSupport
  · intro x hx
    exact (hu.differentiableOn one_ne_zero x (hφ.tsupport_subset hx)).differentiableAt
      (hU.mem_nhds (hφ.tsupport_subset hx))
  · exact fun x _ => hφ.differentiable x

/-- The same over a set `Ω ⊇ U`. -/
theorem setIntegral_mul_fderiv_eq_neg_of_contDiffOn {Ω U : Set F} (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    {u : F → ℝ} (hu : ContDiffOn ℝ 1 u U) {φ : F → ℝ} (hφ : IsTestFn U φ) (w : F) :
    ∫ x in Ω, u x * fderiv ℝ φ x w ∂μ = -∫ x in Ω, fderiv ℝ u x w * φ x ∂μ := by
  have hout : ∀ x ∉ Ω, x ∉ tsupport φ := fun x hx h => hx (hUΩ (hφ.tsupport_subset h))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [fderiv_eq_zero_of_notMem_tsupport (hout x hx)]; simp,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (hout x hx), mul_zero]]
  exact integral_mul_fderiv_eq_neg_of_contDiffOn hU hu hφ w

/-- **The pair `(u, ∇u)`** of a function and its classical gradient, when both are square
integrable on `Ω`. -/
def classicalPair {Ω : Set F} {u : F → ℝ} (hu : MemLp u 2 (μ.restrict Ω))
    (hg : MemLp (gradient u) 2 (μ.restrict Ω)) : L2Pair μ Ω :=
  WithLp.toLp 2 (hu.toLp u, hg.toLp (gradient u))

@[simp] theorem classicalPair_fst {Ω : Set F} {u : F → ℝ} (hu : MemLp u 2 (μ.restrict Ω))
    (hg : MemLp (gradient u) 2 (μ.restrict Ω)) : (classicalPair hu hg).fst = hu.toLp u := rfl

@[simp] theorem classicalPair_snd {Ω : Set F} {u : F → ℝ} (hu : MemLp u 2 (μ.restrict Ω))
    (hg : MemLp (gradient u) 2 (μ.restrict Ω)) :
    (classicalPair hu hg).snd = hg.toLp (gradient u) := rfl

/-- The derivative `∂_w φ = ⟨w, ∇φ⟩` of a test function, as the image of its graph under a
bounded operator. -/
theorem compLp_graph_snd (Ω : Set F) {U : Set F} {φ : F → ℝ} (hφ : IsTestFn U φ) (w : F) :
    (innerSL ℝ w).compLp (graph μ Ω hφ).snd =
      (hφ.memLp_fderiv_apply (μ := μ) w 2 Ω).toLp (fun x => fderiv ℝ φ x w) := by
  refine Lp.ext ?_
  filter_upwards [(innerSL ℝ w).coeFn_compLp (graph μ Ω hφ).snd,
    (hφ.memLp_gradient (μ := μ) 2 Ω).coeFn_toLp,
    (hφ.memLp_fderiv_apply (μ := μ) w 2 Ω).coeFn_toLp] with x h1 h2 h3
  rw [h1, h3, graph_snd, h2, innerSL_apply_apply, real_inner_comm, inner_gradient]

/-- `φ w` as the image of the graph of `φ` under a bounded operator. -/
theorem compLp_graph_fst (Ω : Set F) {U : Set F} {φ : F → ℝ} (hφ : IsTestFn U φ) (w : F) :
    ((ContinuousLinearMap.id ℝ ℝ).smulRight w).compLp (graph μ Ω hφ).fst =
      (hφ.memLp_smul_vec (μ := μ) w 2 Ω).toLp (fun x => φ x • w) := by
  refine Lp.ext ?_
  filter_upwards [((ContinuousLinearMap.id ℝ ℝ).smulRight w).coeFn_compLp (graph μ Ω hφ).fst,
    (hφ.memLp (μ := μ) 2 Ω).coeFn_toLp,
    (hφ.memLp_smul_vec (μ := μ) w 2 Ω).coeFn_toLp] with x h1 h2 h3
  rw [h1, h3, graph_fst, h2, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]

/-- **Energy uniqueness.** On a bounded domain, two weak solutions with the same right-hand side
whose difference lies in `W^{1,2}_0(Ω)` are equal. This replaces the maximum principle (paper,
Lemma 3.2) in the uniqueness step of Lemma 3.3: no continuity up to the boundary is needed. -/
theorem eq_of_isWeakSolution_of_sub_mem_H01 [Nontrivial F]
    (c : CoeffField F μ) {Ω : Set F} {x₀ : F} {R : ℝ} (hR : 0 ≤ R)
    (hΩ : Ω ⊆ Metric.closedBall x₀ R) {f : Lp ℝ 2 (μ.restrict Ω)} {v₁ v₂ : L2Pair μ Ω}
    (h₁ : c.IsWeakSolution f v₁) (h₂ : c.IsWeakSolution f v₂) (h : v₁ - v₂ ∈ H01 μ Ω) :
    v₁ = v₂ := by
  obtain ⟨w, -, hw⟩ := c.existsUnique_H01_isWeakSolution hR hΩ 0
  have e1 : (⟨v₁ - v₂, h⟩ : H01 μ Ω) = w := hw _ (CoeffField.isWeakSolution_zero_of_sub h₁ h₂)
  have e2 : (0 : H01 μ Ω) = w := hw _ ⟨(W12 μ Ω).zero_mem, fun φ hφ => by simp⟩
  have := congrArg Subtype.val (e1.trans e2.symm)
  exact sub_eq_zero.mp this

/-- **A weakly harmonic function in `W^{1,2}_0(Ω)` vanishes** (bounded `Ω`). -/
theorem eq_zero_of_isWeakSolution_zero_of_mem_H01 [Nontrivial F]
    (c : CoeffField F μ) {Ω : Set F} {x₀ : F} {R : ℝ} (hR : 0 ≤ R)
    (hΩ : Ω ⊆ Metric.closedBall x₀ R) {v : L2Pair μ Ω} (hv : c.IsWeakSolution 0 v)
    (h : v ∈ H01 μ Ω) : v = 0 :=
  eq_of_isWeakSolution_of_sub_mem_H01 c hR hΩ hv ⟨(W12 μ Ω).zero_mem, fun φ hφ => by simp⟩
    (by rwa [sub_zero])

end General

/-! ### Removability of the singular set -/

section Euclid

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

theorem isClosed_coneSingular (e : RealConeIndex κ ι ≃ Fin d) :
    IsClosed (coneSingular e : Set 𝔼) :=
  isClosed_iUnion_of_finite fun _ => isClosed_planeZero _ _

/-- The singular set is null. -/
theorem ae_notMem_coneSingular (e : RealConeIndex κ ι ≃ Fin d) :
    ∀ᵐ x : 𝔼, x ∉ coneSingular e := by
  simp only [coneSingular, mem_iUnion, not_exists]
  exact ae_all_iff.mpr fun _ => ae_notMem_planeZero _ _

theorem isOpen_regularPart (e : RealConeIndex κ ι ≃ Fin d) {Ω : Set 𝔼} (hΩ : IsOpen Ω) :
    IsOpen (Ω \ coneSingular e) :=
  hΩ.sdiff (isClosed_coneSingular e)

/-- **Removability of the singular set for `W^{1,2}`.** If `G` is the weak gradient of `u`
against test functions supported in `Ω \ S`, it is the weak gradient of `u` on `Ω`. -/
theorem mem_W12_of_regular [NeZero d] (e : RealConeIndex κ ι ≃ Fin d) {Ω : Set 𝔼} {v : L2Pair volume Ω}
    (h : ∀ (φ : 𝔼 → ℝ) (hφ : IsTestFn (Ω \ coneSingular e) φ) (w : 𝔼),
      ⟪v.fst, ((hφ.mono sdiff_subset).memLp_fderiv_apply (μ := volume) w 2 Ω).toLp _⟫_ℝ =
        -⟪v.snd, ((hφ.mono sdiff_subset).memLp_smul_vec (μ := volume) w 2 Ω).toLp _⟫_ℝ) :
    v ∈ W12 volume Ω := by
  intro φ hφ w
  set L₁ : Lp 𝔼 2 (volume.restrict Ω) →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
    (innerSL ℝ w).compLpL 2 _
  set L₂ : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Lp 𝔼 2 (volume.restrict Ω) :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight w).compLpL 2 _
  have hfst : Continuous fun ψ : L2Pair volume Ω => ψ.fst :=
    continuous_fst.comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous
  have hsnd : Continuous fun ψ : L2Pair volume Ω => ψ.snd :=
    continuous_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous
  have hclosed : IsClosed {ψ : L2Pair volume Ω |
      ⟪v.fst, L₁ ψ.snd⟫_ℝ = -⟪v.snd, L₂ ψ.fst⟫_ℝ} :=
    isClosed_eq (continuous_const.inner (L₁.continuous.comp hsnd))
      (continuous_const.inner (L₂.continuous.comp hfst)).neg
  have hsub : (testSubmodule volume Ω (Ω \ coneSingular e) : Set (L2Pair volume Ω)) ⊆
      {ψ : L2Pair volume Ω | ⟪v.fst, L₁ ψ.snd⟫_ℝ = -⟪v.snd, L₂ ψ.fst⟫_ℝ} := by
    rintro _ ⟨ψ, hψ, rfl⟩
    change ⟪v.fst, (innerSL ℝ w).compLp (graph volume Ω hψ).snd⟫_ℝ =
      -⟪v.snd, ((ContinuousLinearMap.id ℝ ℝ).smulRight w).compLp (graph volume Ω hψ).fst⟫_ℝ
    rw [compLp_graph_snd, compLp_graph_fst]
    exact h ψ hψ w
  have hmem : graph volume Ω hφ ∈ closure (testSubmodule volume Ω (Ω \ coneSingular e) :
      Set (L2Pair volume Ω)) := by
    rw [← Submodule.topologicalClosure_coe, dense_testSubmodule_regular e Ω]
    exact graph_mem_H01 Ω hφ
  have h' : ⟪v.fst, (innerSL ℝ w).compLp (graph volume Ω hφ).snd⟫_ℝ =
      -⟪v.snd, ((ContinuousLinearMap.id ℝ ℝ).smulRight w).compLp (graph volume Ω hφ).fst⟫_ℝ :=
    closure_minimal hsub hclosed hmem
  rwa [compLp_graph_snd, compLp_graph_fst] at h'

/-- **A function that is `C¹` off the singular set, with `u` and `∇u` square integrable, lies in
`W^{1,2}(Ω)`**, with weak gradient its classical gradient. -/
theorem classicalPair_mem_W12 [NeZero d] (e : RealConeIndex κ ι ≃ Fin d) {Ω : Set 𝔼} (hΩ : IsOpen Ω)
    {u : 𝔼 → ℝ} (hu : ContDiffOn ℝ 1 u (Ω \ coneSingular e))
    (hu2 : MemLp u 2 (volume.restrict Ω)) (hg2 : MemLp (gradient u) 2 (volume.restrict Ω)) :
    classicalPair hu2 hg2 ∈ W12 volume Ω := by
  refine mem_W12_of_regular e fun φ hφ w => ?_
  rw [classicalPair_fst, classicalPair_snd, inner_toLp_real, inner_toLp,
    setIntegral_mul_fderiv_eq_neg_of_contDiffOn (isOpen_regularPart e hΩ) sdiff_subset hu hφ w]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [inner_smul_right, inner_gradient]
  ring

/-- **Integration by parts for the Dirichlet form of a classical pair.** If the flux `V = A ∇u` is
`C¹` on `Ω \ S`, then against a test function supported in `Ω \ S`,
`∫_Ω ⟨A ∇u, ∇φ⟩ = -∫_Ω (div V) φ`. -/
theorem dirichletForm_classicalPair_graph [NeZero d] (c : CoeffField 𝔼 volume)
    (e : RealConeIndex κ ι ≃ Fin d) {Ω : Set 𝔼} (hΩ : IsOpen Ω) {u : 𝔼 → ℝ}
    (hu2 : MemLp u 2 (volume.restrict Ω)) (hg2 : MemLp (gradient u) 2 (volume.restrict Ω))
    {V : 𝔼 → 𝔼} (hV : ∀ k, ContDiffOn ℝ 1 (fun y => V y k) (Ω \ coneSingular e))
    (hAV : ∀ x ∈ Ω \ coneSingular e, c.A x (gradient u x) = V x) {φ : 𝔼 → ℝ}
    (hφ : IsTestFn (Ω \ coneSingular e) φ) :
    c.dirichletForm Ω (classicalPair hu2 hg2) (graph volume Ω hφ) =
      -∫ x in Ω, divergence V x * φ x := by
  have hU := isOpen_regularPart e hΩ
  have hg : graph volume Ω hφ = graph volume Ω (hφ.mono sdiff_subset) := rfl
  rw [hg, c.dirichletForm_graph _ (hφ.mono sdiff_subset)]
  -- replace `A ∇u` by `V`
  have h1 : ∫ x in Ω, ⟪c.A x ((classicalPair hu2 hg2).snd x), gradient φ x⟫_ℝ =
      ∫ x in Ω, ⟪V x, gradient φ x⟫_ℝ := by
    refine integral_congr_ae ?_
    filter_upwards [hg2.coeFn_toLp, ae_restrict_mem hΩ.measurableSet,
      ae_restrict_of_ae (ae_notMem_coneSingular e)] with x h1 h2 h3
    rw [classicalPair_snd, h1, hAV x ⟨h2, h3⟩]
  rw [h1]
  have hint1 : ∀ k, Integrable (fun x => V x k * fderiv ℝ φ x (EuclideanSpace.single k 1))
      (volume.restrict Ω) := fun k =>
    (integrable_mul_of_continuousOn hU (hV k).continuousOn (hφ.continuous_fderiv_apply _)
      ((tsupport_fderiv_apply_subset ℝ _).trans hφ.tsupport_subset)
      (hφ.hasCompactSupport_fderiv_apply _)).integrableOn
  have hint2 : ∀ k, Integrable
      (fun x => fderiv ℝ (fun y => V y k) x (EuclideanSpace.single k 1) * φ x)
      (volume.restrict Ω) := fun k =>
    (integrable_mul_of_continuousOn hU
      (((hV k).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const)
      hφ.continuous hφ.tsupport_subset hφ.hasCompactSupport).integrableOn
  have h2 : ∫ x in Ω, ⟪V x, gradient φ x⟫_ℝ =
      ∑ k, ∫ x in Ω, V x k * fderiv ℝ φ x (EuclideanSpace.single k 1) := by
    rw [← integral_finsetSum _ fun k _ => hint1 k]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, gradient_apply_single_eq]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [h2]
  simp_rw [setIntegral_mul_fderiv_eq_neg_of_contDiffOn hU sdiff_subset (hV _) hφ]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun k _ => hint2 k]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [divergence, Finset.sum_mul]

/-- **Classical solutions are weak solutions.** Let `u` be `C¹` on `Ω \ S` with `u, ∇u ∈ L²(Ω)`,
and let the flux `V = A ∇u` be `C¹` on `Ω \ S` with `-div V = f` there, where `f ∈ L²(Ω)`. Then `u`
is a weak solution of `-div(A ∇u) = f` on `Ω`. Nothing is assumed at the singular set. -/
theorem isWeakSolution_of_classical [NeZero d] (c : CoeffField 𝔼 volume)
    (e : RealConeIndex κ ι ≃ Fin d) {Ω : Set 𝔼} (hΩ : IsOpen Ω) {u : 𝔼 → ℝ}
    (hu : ContDiffOn ℝ 1 u (Ω \ coneSingular e)) (hu2 : MemLp u 2 (volume.restrict Ω))
    (hg2 : MemLp (gradient u) 2 (volume.restrict Ω)) {V : 𝔼 → 𝔼}
    (hV : ∀ k, ContDiffOn ℝ 1 (fun y => V y k) (Ω \ coneSingular e))
    (hAV : ∀ x ∈ Ω \ coneSingular e, c.A x (gradient u x) = V x) {f : 𝔼 → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω))
    (hdiv : ∀ x ∈ Ω \ coneSingular e, -divergence V x = f x) :
    c.IsWeakSolution (hf.toLp f) (classicalPair hu2 hg2) := by
  have hW := classicalPair_mem_W12 e hΩ hu hu2 hg2
  refine (isWeakSolution_iff_regular c e hW).mpr fun φ hφ => ?_
  rw [dirichletForm_classicalPair_graph c e hΩ hu2 hg2 hV hAV hφ]
  have hg : graph volume Ω hφ = graph volume Ω (hφ.mono sdiff_subset) := rfl
  rw [hg, CoeffField.inner_graph_fst _ (hφ.mono sdiff_subset)]
  have h1' : ∫ x in Ω, (hf.toLp f) x * φ x = ∫ x in Ω, f x * φ x := by
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  rw [h1', ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport φ
  · simp only
    rw [← hdiv x (hφ.tsupport_subset hx), neg_mul]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- **Weak solutions that are classical off `S` solve the equation pointwise.** If `u` is a weak
solution of `-div(A ∇u) = f`, the flux `V = A ∇u` is `C¹` on `Ω \ S` and `f` is continuous there,
then `-div V = f` at every point of `Ω \ S`. (The fundamental lemma of the calculus of
variations.) This is the converse of `isWeakSolution_of_classical`; it is **not** a regularity
theorem: the smoothness of `u` off `S` is assumed. -/
theorem classical_of_isWeakSolution [NeZero d] (c : CoeffField 𝔼 volume)
    (e : RealConeIndex κ ι ≃ Fin d) {Ω : Set 𝔼} (hΩ : IsOpen Ω) {u : 𝔼 → ℝ}
    (hu2 : MemLp u 2 (volume.restrict Ω)) (hg2 : MemLp (gradient u) 2 (volume.restrict Ω))
    {V : 𝔼 → 𝔼} (hV : ∀ k, ContDiffOn ℝ 1 (fun y => V y k) (Ω \ coneSingular e))
    (hAV : ∀ x ∈ Ω \ coneSingular e, c.A x (gradient u x) = V x) {f : 𝔼 → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω)) (hfc : ContinuousOn f (Ω \ coneSingular e))
    (hw : c.IsWeakSolution (hf.toLp f) (classicalPair hu2 hg2)) :
    ∀ x ∈ Ω \ coneSingular e, -divergence V x = f x := by
  set U := Ω \ coneSingular e
  have hU : IsOpen U := isOpen_regularPart e hΩ
  have hdc : ContinuousOn (divergence V) U := by
    have hk : ∀ k, ContinuousOn
        (fun x => fderiv ℝ (fun y => V y k) x (EuclideanSpace.single k 1)) U := fun k =>
      ((hV k).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
    exact continuousOn_finsetSum _ fun k _ => hk k
  set F : 𝔼 → ℝ := fun x => -divergence V x - f x
  have hFc : ContinuousOn F U := hdc.neg.sub hfc
  have hint : ∀ g : 𝔼 → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ x, g x • F x = 0 := by
    intro g hg hgc hgs
    have hφ : IsTestFn U g := ⟨hg, hgc, hgs⟩
    have h2 := hw.2 g (hφ.mono sdiff_subset)
    have hgr : graph volume Ω (hφ.mono sdiff_subset) = graph volume Ω hφ := rfl
    rw [hgr, dirichletForm_classicalPair_graph c e hΩ hu2 hg2 hV hAV hφ, ← hgr,
      CoeffField.inner_graph_fst _ (hφ.mono sdiff_subset)] at h2
    have h1' : ∫ x in Ω, (hf.toLp f) x * g x = ∫ x in Ω, f x * g x := by
      refine integral_congr_ae ?_
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]
    rw [h1'] at h2
    have i1 : Integrable fun x => divergence V x * g x :=
      (continuous_mul_of_continuousOn hU hdc hg.continuous hgs).integrable_of_hasCompactSupport
        hgc.mul_left
    have i2 : Integrable fun x => f x * g x :=
      (continuous_mul_of_continuousOn hU hfc hg.continuous hgs).integrable_of_hasCompactSupport
        hgc.mul_left
    have hout : ∀ x ∉ Ω, g x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hgs h).1
    have e1 : ∫ x in Ω, divergence V x * g x = ∫ x, divergence V x * g x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hout x hx, mul_zero]
    have e2 : ∫ x in Ω, f x * g x = ∫ x, f x * g x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hout x hx, mul_zero]
    rw [e1, e2] at h2
    calc ∫ x, g x • F x = ∫ x, (-(divergence V x * g x) - f x * g x) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [F, smul_eq_mul]
          ring
      _ = -(∫ x, divergence V x * g x) - ∫ x, f x * g x := by
          rw [integral_sub i1.fun_neg i2, integral_neg]
      _ = 0 := by rw [h2, sub_self]
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hFc.locallyIntegrableOn hU.measurableSet) hint
  have heq : EqOn F 0 U := Measure.eqOn_open_of_ae_eq
    ((ae_restrict_iff' hU.measurableSet).mpr hae) hU hFc continuousOn_const
  intro x hx
  have h := heq hx
  simp only [F, Pi.zero_apply] at h
  linarith

end Euclid

/-! ### The cone Laplacian -/

section Cone

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

open RealConeModel

/-- **Polar coordinates of a point** of the real model: `r_a = |y_a|`, `θ_a = arg y_a`,
`s_i = y_i`. -/
def polarOf (y : RealConeModel κ ι) : PolarPoint κ ι
  | .r a => ‖y.cone a‖
  | .θ a => Complex.arg (y.cone a)
  | .s i => y.eucl i

theorem polarOf_toModel (y : RealConeModel κ ι) : (polarOf y).toModel = y :=
  ext_cone_eucl (fun a => by
      rw [PolarPoint.cone_toModel, polarMap]
      exact Complex.norm_mul_exp_arg_mul_I _)
    fun i => by rw [PolarPoint.eucl_toModel]; rfl

theorem polarOf_r_pos {y : RealConeModel κ ι} (hy : ∀ a, y.cone a ≠ 0) (a : κ) :
    0 < polarOf y (.r a) :=
  norm_pos_iff.mpr (hy a)

/-- The components of the flux `g⁻¹ ∇u` are `C¹` where `u` is `C²`, on the regular part. -/
theorem contDiffOn_coneInvOp_gradient_apply (β : κ → ConeAngle) {O : Set (RealConeModel κ ι)}
    (hO : IsOpen O) (hreg : ∀ y ∈ O, ∀ a, y.cone a ≠ 0) {u : RealConeModel κ ι → ℝ}
    (hu : ContDiffOn ℝ 2 u O) (j : RealConeIndex κ ι) :
    ContDiffOn ℝ 1 (fun y => coneInvOp β y (gradient u y) j) O := by
  have hD : ContDiffOn ℝ 1 (fderiv ℝ u) O := hu.fderiv_of_isOpen hO (by norm_num)
  have hang : ∀ a, ContDiffOn ℝ 1 (angularCoeff u a) O := by
    intro a
    have hnum : ContDiffOn ℝ 1 (fun y => fderiv ℝ u y (rotJ a y)) O :=
      hD.clm_apply (rotJ (ι := ι) a).contDiff.contDiffOn
    have hden : ContDiffOn ℝ 1 (fun y : RealConeModel κ ι => ‖y.cone a‖ ^ 2) O :=
      ((contDiff_norm_sq ℝ).comp (coneProj (ι := ι) a).contDiff).contDiffOn
    exact hnum.div hden fun y hy => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hreg y hy a))
  have hformula : ContDiffOn ℝ 1 (fun y => fderiv ℝ u y (EuclideanSpace.single j 1) +
      ∑ a, ((β a).beta⁻¹ ^ 2 - 1) * angularCoeff u a y * rotJ a y j) O := by
    refine (hD.clm_apply contDiffOn_const).add (ContDiffOn.sum fun a _ => ?_)
    exact (contDiffOn_const.mul (hang a)).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp (rotJ (ι := ι) a).contDiff).contDiffOn
  exact hformula.congr fun y hy => coneInvOp_gradient_apply β u (hreg y hy) j

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The gradient of `u ∘ L` for a linear isometry `L`. -/
theorem gradient_comp_linearIsometryEquiv {E G : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] (L : E ≃ₗᵢ[ℝ] G) (u : G → ℝ) (y : E) :
    gradient (fun y => u (L y)) y = L.symm (gradient u (L y)) := by
  refine ext_inner_right ℝ fun v => ?_
  have h := L.toContinuousLinearEquiv.comp_right_fderiv (𝕜 := ℝ) (f := u) (x := y)
  rw [inner_gradient, ← L.inner_map_map, L.apply_symm_apply, inner_gradient]
  have h' : fderiv ℝ (fun y => u (L y)) y = (fderiv ℝ u (L y)).comp
      (L.toContinuousLinearEquiv : E →L[ℝ] G) := h
  rw [h']
  rfl

theorem coordIso_apply (e : RealConeIndex κ ι ≃ Fin d) (y : RealConeModel κ ι) (k : Fin d) :
    coordIso e y k = y (e.symm k) := rfl

theorem coordIso_symm_single (e : RealConeIndex κ ι ≃ Fin d) (k : Fin d) :
    (coordIso e).symm (EuclideanSpace.single k 1) = EuclideanSpace.single (e.symm k) 1 := by
  rw [coordIso, LinearIsometryEquiv.piLpCongrLeft_symm]
  exact LinearIsometryEquiv.piLpCongrLeft_single _ _ _

/-- **The divergence is invariant under renumbering the coordinates.** -/
theorem divergence_coordIso (e : RealConeIndex κ ι ≃ Fin d)
    (W : RealConeModel κ ι → RealConeModel κ ι) (x : 𝔼) :
    divergence (fun x => coordIso e (W ((coordIso e).symm x))) x =
      divergence W ((coordIso e).symm x) := by
  simp only [divergence]
  rw [← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := (coordIso e).symm.toContinuousLinearEquiv.comp_right_fderiv (𝕜 := ℝ)
    (f := fun y => W y (e.symm k)) (x := x)
  have h' : fderiv ℝ (fun x => coordIso e (W ((coordIso e).symm x)) k) x =
      (fderiv ℝ (fun y => W y (e.symm k)) ((coordIso e).symm x)).comp
        ((coordIso e).symm.toContinuousLinearEquiv : 𝔼 →L[ℝ] RealConeModel κ ι) := h
  rw [h']
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, coordIso_symm_single]

/-- **The flux `g⁻¹ ∇u`** of a function on `ℝ^d`, computed in the real model. -/
def coneFlux (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (u : 𝔼 → ℝ) (x : 𝔼) : 𝔼 :=
  coordIso e (coneInvOp β ((coordIso e).symm x)
    (gradient (fun y => u (coordIso e y)) ((coordIso e).symm x)))

theorem coneCoeffA_gradient (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (u : 𝔼 → ℝ)
    (x : 𝔼) : coneCoeffA β e x (gradient u x) = coneFlux β e u x := by
  rw [coneFlux, gradient_comp_linearIsometryEquiv, LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem regular_of_mem_regularPart [NeZero d] (e : RealConeIndex κ ι ≃ Fin d) {Ω : Set 𝔼} {x : 𝔼}
    (hx : x ∈ Ω \ coneSingular e) : ∀ a, ((coordIso e).symm x).cone a ≠ 0 := by
  intro a ha
  refine hx.2 ?_
  rw [coneSingular_eq]
  exact ⟨a, ha⟩

/-- The components of the flux are `C¹` on `Ω \ S` when `u` is `C²` there. -/
theorem contDiffOn_coneFlux [NeZero d] (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) {Ω : Set 𝔼}
    (hΩ : IsOpen Ω) {u : 𝔼 → ℝ} (hu : ContDiffOn ℝ 2 u (Ω \ coneSingular e)) (k : Fin d) :
    ContDiffOn ℝ 1 (fun x => coneFlux β e u x k) (Ω \ coneSingular e) := by
  set L := coordIso (ι := ι) e
  set O : Set (RealConeModel κ ι) := L ⁻¹' (Ω \ coneSingular e) with hOdef
  have hO : IsOpen O := (isOpen_regularPart e hΩ).preimage L.continuous
  have hreg : ∀ y ∈ O, ∀ a, y.cone a ≠ 0 := fun y hy => by
    have := regular_of_mem_regularPart e hy
    rwa [LinearIsometryEquiv.symm_apply_apply] at this
  have hũ : ContDiffOn ℝ 2 (fun y => u (L y)) O := hu.comp L.contDiff.contDiffOn fun y hy => hy
  have h := contDiffOn_coneInvOp_gradient_apply β hO hreg hũ (e.symm k)
  refine h.comp L.symm.contDiff.contDiffOn fun x hx => ?_
  show L (L.symm x) ∈ Ω \ coneSingular e
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact hx

/-- **The divergence of the flux is the paper's Laplacian** in polar coordinates, at regular
points of `Ω`, for `u` of class `C²` off `S`. -/
theorem divergence_coneFlux [NeZero d] (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) {Ω : Set 𝔼}
    (hΩ : IsOpen Ω) {u : 𝔼 → ℝ} (hu : ContDiffOn ℝ 2 u (Ω \ coneSingular e))
    {c : PolarPoint κ ι} (hc : ∀ a, 0 < c (.r a)) (hcΩ : coordIso e c.toModel ∈ Ω) :
    divergence (coneFlux β e u) (coordIso e c.toModel) =
      paperLaplacian β (fun c' => u (coordIso e c'.toModel)) c := by
  set L := coordIso (ι := ι) e
  have hx : L c.toModel ∈ Ω \ coneSingular e := by
    refine ⟨hcΩ, fun hS => ?_⟩
    rw [coneSingular_eq] at hS
    obtain ⟨a, ha⟩ := hS
    rw [LinearIsometryEquiv.symm_apply_apply, PolarPoint.cone_toModel] at ha
    exact polarMap_ne_zero (hc a) ha
  have hũc : ContDiffAt ℝ 2 (fun y => u (L y)) c.toModel :=
    (hu.contDiffAt ((isOpen_regularPart e hΩ).mem_nhds hx)).comp _ L.contDiff.contDiffAt
  have h := divergence_coordIso e (fun y => coneInvOp β y (gradient (fun y => u (L y)) y))
    (L c.toModel)
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  rw [show coneFlux β e u = fun x => L ((fun y => coneInvOp β y
      (gradient (fun y => u (L y)) y)) (L.symm x)) from rfl, h,
    divergence_coneInvOp_gradient β hc hũc]

/-- **Classical solutions of the cone Laplacian are weak solutions.** Let `u` be `C²` on
`Ω \ S`, with `u` and `∇u` square integrable on `Ω`, and let `-Δu = f` on `Ω \ S`, where `Δ` is the
paper's Laplacian `∑_a Δ_{β_a} + Δ_{ℝ^ι}` in polar coordinates and `f ∈ L²(Ω)`. Then `u` is a weak
solution of `-div(g⁻¹ ∇u) = f` on `Ω`. -/
theorem cone_isWeakSolution_of_classical [NeZero d] (β : κ → ConeAngle)
    (e : RealConeIndex κ ι ≃ Fin d) {Ω : Set 𝔼} (hΩ : IsOpen Ω) {u : 𝔼 → ℝ}
    (hu : ContDiffOn ℝ 2 u (Ω \ coneSingular e)) (hu2 : MemLp u 2 (volume.restrict Ω))
    (hg2 : MemLp (gradient u) 2 (volume.restrict Ω)) {f : 𝔼 → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω))
    (hΔ : ∀ c : PolarPoint κ ι, (∀ a, 0 < c (.r a)) → coordIso e c.toModel ∈ Ω →
      -paperLaplacian β (fun c' => u (coordIso e c'.toModel)) c = f (coordIso e c.toModel)) :
    (coneCoeff β e).IsWeakSolution (hf.toLp f) (classicalPair hu2 hg2) := by
  refine isWeakSolution_of_classical (coneCoeff β e) e hΩ (hu.of_le (by norm_num)) hu2 hg2
    (V := coneFlux β e u) (contDiffOn_coneFlux β e hΩ hu)
    (fun x _ => coneCoeffA_gradient β e u x) hf (fun x hx => ?_)
  set c := polarOf ((coordIso e).symm x)
  have hc : ∀ a, 0 < c (.r a) := polarOf_r_pos (regular_of_mem_regularPart e hx)
  have hcx : coordIso e c.toModel = x := by
    rw [polarOf_toModel, LinearIsometryEquiv.apply_symm_apply]
  have h := hΔ c hc (by rw [hcx]; exact hx.1)
  rw [← divergence_coneFlux β e hΩ hu hc (by rw [hcx]; exact hx.1), hcx] at h
  exact h

/-- **Weak solutions of the cone Laplacian that are `C²` off `S` are classical solutions**: if
`u` is a weak solution of `-div(g⁻¹ ∇u) = f` with `u ∈ C²(Ω \ S)` and `f` continuous on `Ω \ S`,
then `-Δu = f` at every regular point, for the paper's Laplacian in polar coordinates. The
smoothness of `u` off `S` is a hypothesis (interior regularity is not proved here). -/
theorem cone_classical_of_isWeakSolution [NeZero d] (β : κ → ConeAngle)
    (e : RealConeIndex κ ι ≃ Fin d) {Ω : Set 𝔼} (hΩ : IsOpen Ω) {u : 𝔼 → ℝ}
    (hu : ContDiffOn ℝ 2 u (Ω \ coneSingular e)) (hu2 : MemLp u 2 (volume.restrict Ω))
    (hg2 : MemLp (gradient u) 2 (volume.restrict Ω)) {f : 𝔼 → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω)) (hfc : ContinuousOn f (Ω \ coneSingular e))
    (hw : (coneCoeff β e).IsWeakSolution (hf.toLp f) (classicalPair hu2 hg2))
    {c : PolarPoint κ ι} (hc : ∀ a, 0 < c (.r a)) (hcΩ : coordIso e c.toModel ∈ Ω) :
    -paperLaplacian β (fun c' => u (coordIso e c'.toModel)) c = f (coordIso e c.toModel) := by
  have hx : coordIso e c.toModel ∈ Ω \ coneSingular e := by
    refine ⟨hcΩ, fun hS => ?_⟩
    rw [coneSingular_eq] at hS
    obtain ⟨a, ha⟩ := hS
    rw [LinearIsometryEquiv.symm_apply_apply, PolarPoint.cone_toModel] at ha
    exact polarMap_ne_zero (hc a) ha
  have h := classical_of_isWeakSolution (coneCoeff β e) e hΩ hu2 hg2 (V := coneFlux β e u)
    (contDiffOn_coneFlux β e hΩ hu) (fun x _ => coneCoeffA_gradient β e u x) hf hfc hw _ hx
  rwa [divergence_coneFlux β e hΩ hu hc hcΩ] at h

end Cone

end ConicalKahler.Sobolev
