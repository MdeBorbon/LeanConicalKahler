module

public import ConicalKahler.Sobolev.Homogeneous
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Lemma 3.3: expansion of harmonic functions in homogeneous harmonic functions

Let `c` be a conical coefficient field on `ℝ^d`, `d ≥ 2`, and let `{φ_i}` be the Hilbert basis of
link eigenfunctions of Lemma 3.1 (`link_spectral`), with eigenvalues `λ_i` and indicial roots
`δ_i ≥ 0`, `δ_i (δ_i + d - 2) = λ_i`. The homogeneous functions `P_i = |x|^{δ_i} φ_i(x/|x|)` are
weakly harmonic on every ball (`homPair_isWeakSolution`). This file proves

* **Lemma 3.3** (`expansion`): every weakly harmonic `u ∈ W^{1,2}(B_1)` is the `L²(B_1)`-sum
  `u = ∑_i c_i P_i`, with `P_i` orthogonal in `L²(B_1)`.

The proof replaces the paper's maximum principle argument (`PAPER_REVIEW.md` S2) by a Wronskian
identity. Testing the equations of `u` and of `P_i` against each other with radial cut-offs gives,
for the ray coefficients `u_i(r) = ∫_S u(r w) φ_i(w) dσ`,
`∫_0^1 r^{-δ_i} u_i(r) h'(r) dr = 0` for all `h ∈ C_c^∞(0, 1)`. Hence `u_i(r) = c_i r^{δ_i}`
(du Bois-Reymond), and Parseval on each sphere gives the expansion.

## Vertex removability

* `dense_testSubmodule_punctured`, `mem_W12_of_punctured`, `isWeakSolution_iff_punctured`: for
  `d ≥ 2` the vertex `{0}` is removable for `W^{1,2}` and for weak solutions (it lies in a
  codimension-two plane, `Capacity.lean`).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set Metric
open scoped ContDiff ENNReal Interval

namespace ConicalKahler.Sobolev

variable {d : ℕ} [NeZero d]

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### Removability of the vertex -/

section Punctured

variable (hd : 2 ≤ d)
include hd

theorem zero_mem_planeZero : (0 : 𝔼) ∈ planeZero (⟨0, by omega⟩ : Fin d) ⟨1, by omega⟩ := by
  simp [planeZero, planeSq]

/-- **Test functions supported away from the vertex are dense in `W^{1,2}_0(Ω)`** (`d ≥ 2`). -/
theorem dense_testSubmodule_punctured (Ω : Set 𝔼) :
    (testSubmodule volume Ω (Ω \ {0})).topologicalClosure = H01 volume Ω := by
  refine le_antisymm (Submodule.topologicalClosure_mono (testSubmodule_mono Ω sdiff_subset))
    (Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _))
  rintro _ ⟨φ, hφ, rfl⟩
  have hne : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h := graph_mem_closure_testSubmodule_diff Ω hφ hne
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  have hsub : Ω \ planeZero (⟨0, by omega⟩ : Fin d) ⟨1, by omega⟩ ⊆ Ω \ {0} := by
    intro x hx
    refine ⟨hx.1, fun h0 => hx.2 ?_⟩
    rw [mem_singleton_iff.mp h0]
    exact zero_mem_planeZero hd
  exact closure_mono (testSubmodule_mono Ω hsub) h

/-- **The vertex is removable for `W^{1,2}`** (`d ≥ 2`). -/
theorem mem_W12_of_punctured {Ω : Set 𝔼} {v : L2Pair volume Ω}
    (h : ∀ (φ : 𝔼 → ℝ) (hφ : IsTestFn (Ω \ {0}) φ) (w : 𝔼),
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
  have hsub : (testSubmodule volume Ω (Ω \ {0}) : Set (L2Pair volume Ω)) ⊆
      {ψ : L2Pair volume Ω | ⟪v.fst, L₁ ψ.snd⟫_ℝ = -⟪v.snd, L₂ ψ.fst⟫_ℝ} := by
    rintro _ ⟨ψ, hψ, rfl⟩
    change ⟪v.fst, (innerSL ℝ w).compLp (graph volume Ω hψ).snd⟫_ℝ =
      -⟪v.snd, ((ContinuousLinearMap.id ℝ ℝ).smulRight w).compLp (graph volume Ω hψ).fst⟫_ℝ
    rw [compLp_graph_snd, compLp_graph_fst]
    exact h ψ hψ w
  have hmem : graph volume Ω hφ ∈ closure (testSubmodule volume Ω (Ω \ {0}) :
      Set (L2Pair volume Ω)) := by
    rw [← Submodule.topologicalClosure_coe, dense_testSubmodule_punctured hd Ω]
    exact graph_mem_H01 Ω hφ
  have h' : ⟪v.fst, (innerSL ℝ w).compLp (graph volume Ω hφ).snd⟫_ℝ =
      -⟪v.snd, ((ContinuousLinearMap.id ℝ ℝ).smulRight w).compLp (graph volume Ω hφ).fst⟫_ℝ :=
    closure_minimal hsub hclosed hmem
  rwa [compLp_graph_snd, compLp_graph_fst] at h'

/-- **The vertex is removable for weak solutions** (`d ≥ 2`): for `v ∈ W^{1,2}(Ω)`, the weak
equation on `Ω` follows from the weak equation against test functions supported in `Ω \ {0}`. -/
theorem isWeakSolution_of_punctured (c : CoeffField 𝔼 volume) {Ω : Set 𝔼}
    {f : Lp ℝ 2 (volume.restrict Ω)} {v : L2Pair volume Ω} (hv : v ∈ W12 volume Ω)
    (h : ∀ (φ : 𝔼 → ℝ) (hφ : IsTestFn (Ω \ {0}) φ),
      c.dirichletForm Ω v (graph volume Ω (hφ.mono sdiff_subset)) =
        ⟪f, (graph volume Ω (hφ.mono sdiff_subset)).fst⟫_ℝ) :
    c.IsWeakSolution f v := by
  refine ⟨hv, fun φ hφ => ?_⟩
  have hfst : Continuous fun v : L2Pair volume Ω => v.fst :=
    continuous_fst.comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous
  have hclosed : IsClosed {ψ : L2Pair volume Ω | c.dirichletForm Ω v ψ = ⟪f, ψ.fst⟫_ℝ} :=
    isClosed_eq (c.dirichletForm Ω v).continuous (continuous_const.inner hfst)
  have hsub : (testSubmodule volume Ω (Ω \ {0}) : Set (L2Pair volume Ω)) ⊆
      {ψ : L2Pair volume Ω | c.dirichletForm Ω v ψ = ⟪f, ψ.fst⟫_ℝ} := by
    rintro _ ⟨ψ, hψ, rfl⟩
    exact h ψ hψ
  have hmem : graph volume Ω hφ ∈ closure (testSubmodule volume Ω (Ω \ {0}) :
      Set (L2Pair volume Ω)) := by
    rw [← Submodule.topologicalClosure_coe, dense_testSubmodule_punctured hd Ω]
    exact graph_mem_H01 Ω hφ
  exact closure_minimal hsub hclosed hmem

end Punctured

/-! ### Homogeneous functions on balls -/

theorem shellWeight_zero_ne_top (R k : ℝ) (h : 0 < 2 * k + d) : shellWeight d k 0 R ≠ ⊤ := by
  have hint : IntegrableOn (fun r : ℝ => r ^ (2 * k + d - 1)) (Ioo 0 R) := by
    rcases le_or_gt R 0 with hR | hR
    · rw [Ioo_eq_empty (not_lt.mpr hR)]
      exact integrableOn_empty
    · have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R)
        (r := 2 * k + d - 1) (by linarith)).1
      exact this.mono_set Ioo_subset_Ioc_self
  refine ne_top_of_le_ne_top hint.2.ne ?_
  refine setLIntegral_mono_ae' measurableSet_Ioo (Eventually.of_forall fun r hr => ?_)
  have hr0 : 0 < r := hr.1
  have heq : (r ^ k) ^ 2 * r ^ (d - 1) = r ^ (2 * k + d - 1) := by
    rw [← rpow_sub_one_eq_pow hr0, ← Real.rpow_natCast (r ^ k) 2, ← Real.rpow_mul hr0.le,
      ← Real.rpow_add hr0]
    congr 1
    push_cast
    ring
  rw [heq]
  exact Real.ofReal_le_enorm _

/-- **Homogeneous extensions are in `L²(B_R)`** when `2k + d > 0`. -/
theorem memLp_homFun_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℝ)
    {Ψ : Sph d → E} (hΨ : MemLp Ψ 2 (sphMeasure d)) (R : ℝ) (h : 0 < 2 * k + d) :
    MemLp (homFun k Ψ) 2 (volume.restrict (ball (0 : 𝔼) R)) := by
  have hsh := memLp_homFun (Ω := shell d 0 R) k hΨ le_rfl (subset_refl _)
    (shellWeight_zero_ne_top R k h)
  refine hsh.mono_measure ?_
  calc volume.restrict (ball (0 : 𝔼) R) ≤ volume.restrict (shell d 0 R ∪ {0}) :=
        Measure.restrict_mono (fun x hx => by
          by_cases hx0 : x = 0
          · exact Or.inr hx0
          · exact Or.inl ⟨norm_pos_iff.mpr hx0, mem_ball_zero_iff.mp hx⟩) le_rfl
    _ ≤ volume.restrict (shell d 0 R) + volume.restrict {0} := Measure.restrict_union_le _ _
    _ = volume.restrict (shell d 0 R) := by
        rw [Measure.restrict_eq_zero.mpr (measure_singleton 0), add_zero]

/-- A link eigenfunction with eigenvalue `0` has `Γ = 0`. -/
theorem IsLinkEigen.snd_eq_zero {c : CoeffField 𝔼 volume} {hc : c.IsConical} {v : LinkPair d}
    (h : IsLinkEigen hc 0 v) : v.snd = 0 := by
  have h1 := h.2 v h.1
  rw [zero_mul] at h1
  have h2 := CoeffField.lam_mul_norm_sq_le_sphMulOp hc v.snd
  rw [h1] at h2
  have h3 : ‖v.snd‖ ^ 2 = 0 :=
    le_antisymm ((mul_le_mul_iff_of_pos_left c.lam_pos).mp (by simpa using h2)) (sq_nonneg _)
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)

/-- The pair `(P, ∇P)` of a homogeneous extension on the ball `B_R`. -/
def homPair (δ : ℝ) (v : LinkPair d) (R : ℝ)
    (hP : MemLp (homP δ v) 2 (volume.restrict (ball (0 : 𝔼) R)))
    (hG : MemLp (homG δ v) 2 (volume.restrict (ball (0 : 𝔼) R))) :
    L2Pair volume (ball (0 : 𝔼) R) :=
  WithLp.toLp 2 (hP.toLp _, hG.toLp _)

section HomPair

variable {δ : ℝ} {v : LinkPair d} {R : ℝ}
  (hP : MemLp (homP δ v) 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) R)))
  (hG : MemLp (homG δ v) 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) R)))

theorem integral_ball_eq_of_isTestFn {f : 𝔼 → ℝ} {φ : 𝔼 → ℝ}
    (hφ : IsTestFn (ball (0 : 𝔼) R \ {0}) φ) (hf : ∀ x, x ∉ tsupport φ → f x = 0) :
    ∫ x in ball (0 : 𝔼) R, f x = ∫ x, f x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
    hf x fun h => hx (hφ.tsupport_subset h).1

/-- **`(P, ∇P)` is a `W^{1,2}` pair on the ball** (`d ≥ 2`), when both are square integrable. -/
theorem homPair_mem_W12 (hd : 2 ≤ d) (hv : v ∈ linkW12 d) :
    homPair δ v R hP hG ∈ W12 volume (ball (0 : 𝔼) R) := by
  refine mem_W12_of_punctured hd fun φ hφ w => ?_
  have hφ0 : IsTestFn {0}ᶜ φ := hφ.mono fun x hx => hx.2
  rw [homPair, WithLp.toLp_fst, WithLp.toLp_snd, inner_toLp_real, inner_toLp]
  have z1 : ∀ x, x ∉ tsupport φ → homP δ v x * fderiv ℝ φ x w = 0 := fun x hx => by
    rw [fderiv_eq_zero_of_notMem_tsupport hx, ContinuousLinearMap.zero_apply, mul_zero]
  have z2 : ∀ x, x ∉ tsupport φ → ⟪homG δ v x, φ x • w⟫_ℝ = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, zero_smul, inner_zero_right]
  rw [integral_ball_eq_of_isTestFn hφ z1, integral_ball_eq_of_isTestFn hφ z2]
  rw [homP_integral hv δ hφ0 w]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [inner_smul_right, mul_comm]

/-- **`P` is weakly harmonic on the ball** (`d ≥ 2`): `P = |x|^δ φ(x/|x|)` with `(φ, Γ)` a link
eigenfunction for `λ = δ(δ + d - 2)`. -/
theorem homPair_isWeakSolution (hd : 2 ≤ d) {c : CoeffField 𝔼 volume} (hc : c.IsConical)
    {lam : ℝ} (hE : IsLinkEigen hc lam v) (hlam : lam = δ * (δ + d - 2)) :
    c.IsWeakSolution 0 (homPair δ v R hP hG) := by
  refine isWeakSolution_of_punctured hd c (homPair_mem_W12 hP hG hd hE.1) fun φ hφ => ?_
  have hφ0 : IsTestFn {0}ᶜ φ := hφ.mono fun x hx => hx.2
  rw [CoeffField.dirichletForm_graph, inner_zero_left]
  rw [show ∫ x in ball (0 : 𝔼) R, ⟪c.A x ((homPair δ v R hP hG).snd x), gradient φ x⟫_ℝ =
      ∫ x in ball (0 : 𝔼) R, ⟪c.A x (homG δ v x), gradient φ x⟫_ℝ from
    integral_congr_ae (by
      filter_upwards [hG.coeFn_toLp] with x hx
      rw [homPair, WithLp.toLp_snd, hx])]
  have z : ∀ x, x ∉ tsupport φ → ⟪c.A x (homG δ v x), gradient φ x⟫_ℝ = 0 := fun x hx => by
    rw [gradient_eq_zero_of_notMem_tsupport hx, inner_zero_right]
  rw [integral_ball_eq_of_isTestFn hφ z]
  exact homogeneous_harmonic hc hE hlam hφ0

end HomPair

/-! ### Products with test functions and the `W^{1,2}`–`W^{1,2}_0` duality -/

section Products

variable {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- **Integration by parts between `W^{1,2}(Ω)` and `W^{1,2}_0(Ω)`**:
`∫ u ⟨∇ζ, e⟩ = -∫ ζ ⟨∇u, e⟩` for `u ∈ W^{1,2}(Ω)` and `ζ ∈ W^{1,2}_0(Ω)`. -/
theorem integral_mul_inner_of_mem_H01 {u ζ : L2Pair volume Ω} (hu : u ∈ W12 volume Ω)
    (hζ : ζ ∈ H01 volume Ω) (e : 𝔼) :
    ∫ x in Ω, u.fst x * ⟪ζ.snd x, e⟫_ℝ = -∫ x in Ω, ζ.fst x * ⟪u.snd x, e⟫_ℝ := by
  set L₁ : Lp 𝔼 2 (volume.restrict Ω) →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
    (innerSL ℝ e).compLpL 2 _
  set L₂ : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Lp 𝔼 2 (volume.restrict Ω) :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight e).compLpL 2 _
  have hfst : Continuous fun ψ : L2Pair volume Ω => ψ.fst :=
    continuous_fst.comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous
  have hsnd : Continuous fun ψ : L2Pair volume Ω => ψ.snd :=
    continuous_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous
  have hclosed : IsClosed {ψ : L2Pair volume Ω |
      ⟪u.fst, L₁ ψ.snd⟫_ℝ = -⟪u.snd, L₂ ψ.fst⟫_ℝ} :=
    isClosed_eq (continuous_const.inner (L₁.continuous.comp hsnd))
      (continuous_const.inner (L₂.continuous.comp hfst)).neg
  have hsub : (testSubmodule volume Ω Ω : Set (L2Pair volume Ω)) ⊆
      {ψ : L2Pair volume Ω | ⟪u.fst, L₁ ψ.snd⟫_ℝ = -⟪u.snd, L₂ ψ.fst⟫_ℝ} := by
    rintro _ ⟨ψ, hψ, rfl⟩
    change ⟪u.fst, (innerSL ℝ e).compLp (graph volume Ω hψ).snd⟫_ℝ =
      -⟪u.snd, ((ContinuousLinearMap.id ℝ ℝ).smulRight e).compLp (graph volume Ω hψ).fst⟫_ℝ
    rw [compLp_graph_snd, compLp_graph_fst]
    exact hu ψ hψ e
  have hmem : ζ ∈ closure (testSubmodule volume Ω Ω : Set (L2Pair volume Ω)) := by
    rwa [H01, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hζ
  have h := closure_minimal hsub hclosed hmem
  simp only [mem_setOf_eq] at h
  rw [L2.inner_def, L2.inner_def] at h
  have e1 : ∫ x in Ω, ⟪u.fst x, (L₁ ζ.snd) x⟫_ℝ = ∫ x in Ω, u.fst x * ⟪ζ.snd x, e⟫_ℝ := by
    refine integral_congr_ae ?_
    filter_upwards [(innerSL ℝ e).coeFn_compLp ζ.snd] with x hx
    change ⟪u.fst x, ((innerSL ℝ e).compLp ζ.snd) x⟫_ℝ = _
    rw [hx, innerSL_apply_apply, real_inner_comm e]
    simp [mul_comm]
  have e2 : ∫ x in Ω, ⟪u.snd x, (L₂ ζ.fst) x⟫_ℝ = ∫ x in Ω, ζ.fst x * ⟪u.snd x, e⟫_ℝ := by
    refine integral_congr_ae ?_
    filter_upwards [((ContinuousLinearMap.id ℝ ℝ).smulRight e).coeFn_compLp ζ.fst] with x hx
    change ⟪u.snd x, (((ContinuousLinearMap.id ℝ ℝ).smulRight e).compLp ζ.fst) x⟫_ℝ = _
    rw [hx, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_right]
  rw [e1, e2] at h
  exact h

theorem gradient_eq_zero_of_eventuallyEq_const {f : 𝔼 → ℝ} {x : 𝔼} {a : ℝ}
    (h : f =ᶠ[𝓝 x] fun _ => a) : gradient f x = 0 := by
  rw [gradient, h.fderiv_eq, fderiv_const_apply, map_zero]

/-- **Products with test functions lie in `W^{1,2}_0`.** For `v = (u, G) ∈ W^{1,2}(Ω)` and a test
function `η` on the open set `Ω`, there is `ζ ∈ W^{1,2}_0(Ω)` with `ζ = (η u, η G + u ∇η)`
almost everywhere. Proof: polarise the cut-off `cutPair` (which multiplies by squares), using
`η = ((χ + η)/2)² - ((χ - η)/2)²` for a cut-off `χ = 1` near the support of `η`. -/
theorem exists_smulPair_mem_H01 (hΩ : IsOpen Ω) {v : L2Pair volume Ω} (hv : v ∈ W12 volume Ω)
    {η : 𝔼 → ℝ} (hη : IsTestFn Ω η) :
    ∃ ζ ∈ H01 volume Ω, (ζ.fst : 𝔼 → ℝ) =ᵐ[volume.restrict Ω] (fun x => η x * v.fst x) ∧
      (ζ.snd : 𝔼 → 𝔼) =ᵐ[volume.restrict Ω]
        (fun x => η x • v.snd x + v.fst x • gradient η x) := by
  obtain ⟨L, hL, hηL, hLΩ⟩ := exists_compact_between hη.hasCompactSupport.isCompact hΩ
    hη.tsupport_subset
  obtain ⟨χ, hχ, -, hχ1⟩ := exists_cutoff hL hΩ hLΩ
  have hg₁ : IsTestFn Ω (fun x => (χ x + η x) / 2) := by
    have := (hχ.add hη).const_smul (1 / 2 : ℝ)
    convert this using 1
    funext x
    simp [div_eq_inv_mul]
  have hg₂ : IsTestFn Ω (fun x => (χ x - η x) / 2) := by
    have := (hχ.add (hη.const_smul (-1 : ℝ))).const_smul (1 / 2 : ℝ)
    convert this using 1
    funext x
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  refine ⟨cutPair hg₁ v - cutPair hg₂ v,
    (H01 volume Ω).sub_mem (cutPair_mem_H01 hΩ hv hg₁) (cutPair_mem_H01 hΩ hv hg₂), ?_, ?_⟩
  · filter_upwards [Lp.coeFn_sub (cutPair hg₁ v).fst (cutPair hg₂ v).fst,
      (memLp_cutFst (v := v) hg₁).coeFn_toLp, (memLp_cutFst (v := v) hg₂).coeFn_toLp] with x h h1 h2
    rw [WithLp.sub_fst, h, Pi.sub_apply, cutPair_fst, cutPair_fst, h1, h2, cutFst, cutFst]
    by_cases hx : x ∈ tsupport η
    · rw [hχ1 x (interior_subset (hηL hx))]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hx]
      ring
  · filter_upwards [Lp.coeFn_sub (cutPair hg₁ v).snd (cutPair hg₂ v).snd,
      (memLp_cutSnd (v := v) hg₁).coeFn_toLp, (memLp_cutSnd (v := v) hg₂).coeFn_toLp] with x h h1 h2
    rw [WithLp.sub_snd, h, Pi.sub_apply, cutPair_snd, cutPair_snd, h1, h2, cutSnd, cutSnd]
    have e1 : (fun y => (χ y + η y) / 2) = (1 / 2 : ℝ) • (χ + η) := by
      funext y
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    have e2 : (fun y => (χ y - η y) / 2) = (1 / 2 : ℝ) • (χ + (-1 : ℝ) • η) := by
      funext y
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    have hdχ := hχ.differentiable
    have hdη := hη.differentiable
    have hG1 : gradient (fun y => (χ y + η y) / 2) x =
        (1 / 2 : ℝ) • (gradient χ x + gradient η x) := by
      rw [e1, gradient_const_smul (hdχ.add hdη), gradient_add hdχ hdη]
    have hG2 : gradient (fun y => (χ y - η y) / 2) x =
        (1 / 2 : ℝ) • (gradient χ x - gradient η x) := by
      rw [e2, gradient_const_smul (hdχ.add (hdη.const_smul _)),
        gradient_add hdχ (hdη.const_smul _), gradient_const_smul hdη, neg_one_smul,
        ← sub_eq_add_neg]
    rw [hG1, hG2]
    by_cases hx : x ∈ tsupport η
    · have hx' : x ∈ interior L := hηL hx
      have hχx : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
        filter_upwards [isOpen_interior.mem_nhds hx'] with y hy
        exact hχ1 y (interior_subset hy)
      rw [gradient_eq_zero_of_eventuallyEq_const hχx, hχ1 x (interior_subset hx')]
      simp only [zero_add, zero_sub, smul_neg, smul_smul, smul_add, smul_sub]
      module
    · have hηx : η =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hx] with y hy
        exact image_eq_zero_of_notMem_tsupport hy
      rw [gradient_eq_zero_of_eventuallyEq_const hηx, image_eq_zero_of_notMem_tsupport hx]
      simp only [add_zero, sub_zero, smul_smul, zero_smul, smul_zero]
      module

/-- **The Wronskian identity.** If `u` and `P` are weakly harmonic on `Ω` and `η` is a test
function on `Ω`, then `∫ P ⟨A ∇u, ∇η⟩ = ∫ u ⟨A ∇P, ∇η⟩`. -/
theorem wronskian (c : CoeffField 𝔼 volume) (hΩ : IsOpen Ω) {u P : L2Pair volume Ω}
    (hu : c.IsWeakSolution 0 u) (hP : c.IsWeakSolution 0 P) {η : 𝔼 → ℝ} (hη : IsTestFn Ω η) :
    ∫ x in Ω, P.fst x * ⟪c.A x (u.snd x), gradient η x⟫_ℝ =
      ∫ x in Ω, u.fst x * ⟪c.A x (P.snd x), gradient η x⟫_ℝ := by
  obtain ⟨ζ₁, hζ₁, hζ₁f, hζ₁s⟩ := exists_smulPair_mem_H01 hΩ hP.1 hη
  obtain ⟨ζ₂, hζ₂, hζ₂f, hζ₂s⟩ := exists_smulPair_mem_H01 hΩ hu.1 hη
  have h1 := hu.forall_H01 hζ₁
  have h2 := hP.forall_H01 hζ₂
  rw [CoeffField.dirichletForm_apply, CoeffField.inner_mulOp, inner_zero_left] at h1 h2
  obtain ⟨M, -, hMη, hMg⟩ := exists_bound_testFn hη
  -- integrability of the four pieces
  have hi : ∀ (a b : L2Pair volume Ω), Integrable (fun x => a.fst x * ⟪c.A x (b.snd x),
      gradient η x⟫_ℝ) (volume.restrict Ω) := fun a b => by
    have hAb : MemLp (fun x => c.A x (b.snd x)) 2 (volume.restrict Ω) := c.memLp_apply Ω b.snd
    refine (integrable_mul_of_memLp_two (Lp.memLp a.fst)
      (hAb.of_le_mul (c := M) ((hAb.aestronglyMeasurable).inner
        hη.continuous_gradient.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)))
    rw [Real.norm_eq_abs, mul_comm]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hMg x) (norm_nonneg _))
  have hj : ∀ (a b : L2Pair volume Ω), Integrable (fun x => η x * ⟪c.A x (a.snd x),
      b.snd x⟫_ℝ) (volume.restrict Ω) := fun a b => by
    have := (L2.integrable_inner (c.mulOp Ω a.snd) b.snd).bdd_mul
      (c := M) hη.continuous.aestronglyMeasurable (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hMη x)
    refine this.congr ?_
    filter_upwards [c.mulOp_ae Ω a.snd] with x hx
    rw [hx]
  have e1 : ∫ x in Ω, ⟪c.A x (u.snd x), ζ₁.snd x⟫_ℝ =
      ∫ x in Ω, (η x * ⟪c.A x (u.snd x), P.snd x⟫_ℝ +
        P.fst x * ⟪c.A x (u.snd x), gradient η x⟫_ℝ) := by
    refine integral_congr_ae ?_
    filter_upwards [hζ₁s] with x hx
    rw [hx, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have e2 : ∫ x in Ω, ⟪c.A x (P.snd x), ζ₂.snd x⟫_ℝ =
      ∫ x in Ω, (η x * ⟪c.A x (u.snd x), P.snd x⟫_ℝ +
        u.fst x * ⟪c.A x (P.snd x), gradient η x⟫_ℝ) := by
    refine integral_congr_ae ?_
    filter_upwards [hζ₂s] with x hx
    rw [hx, inner_add_right, real_inner_smul_right, real_inner_smul_right, c.symm,
      real_inner_comm]
  have h1' : ∫ x in Ω, ⟪c.A x (u.snd x), ζ₁.snd x⟫_ℝ = 0 := h1
  have h2' : ∫ x in Ω, ⟪c.A x (P.snd x), ζ₂.snd x⟫_ℝ = 0 := h2
  rw [e1, integral_add (hj u P) (hi P u)] at h1'
  rw [e2, integral_add (hj u P) (hi u P)] at h2'
  linarith

/-- **Integration by parts against a vector field times `P`.** For `u, P ∈ W^{1,2}(Ω)` and a
vector field `Y` whose components are test functions on `Ω`,
`∫ P ⟨∇u, Y⟩ = -∫ u (P div Y + ⟨∇P, Y⟩)`. -/
theorem integral_mul_inner_vectorField (hΩ : IsOpen Ω) {u P : L2Pair volume Ω}
    (hu : u ∈ W12 volume Ω) (hP : P ∈ W12 volume Ω) {Y : 𝔼 → 𝔼}
    (hY : ∀ k, IsTestFn Ω fun x => Y x k) :
    ∫ x in Ω, P.fst x * ⟪u.snd x, Y x⟫_ℝ =
      -∫ x in Ω, u.fst x * (P.fst x * (∑ k, fderiv ℝ (fun y => Y y k) x
        (EuclideanSpace.single k 1)) + ⟪P.snd x, Y x⟫_ℝ) := by
  -- integrability: an `L²` product times a bounded continuous function
  have hint : ∀ {f g : 𝔼 → ℝ} {m : 𝔼 → ℝ}, MemLp f 2 (volume.restrict Ω) →
      MemLp g 2 (volume.restrict Ω) → Continuous m → (∃ C, ∀ x, |m x| ≤ C) →
      Integrable (fun x => f x * g x * m x) (volume.restrict Ω) := by
    intro f g m hf hg hm ⟨C, hC⟩
    exact (integrable_mul_of_memLp_two hf hg).mul_bdd hm.aestronglyMeasurable
      (c := C) (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hYb : ∀ k, ∃ C, ∀ x, |Y x k| ≤ C := fun k =>
    ⟨_, (exists_bound_testFn (hY k)).choose_spec.2.1⟩
  have hDYb : ∀ k, ∃ C, ∀ x, |fderiv ℝ (fun y => Y y k) x (EuclideanSpace.single k 1)| ≤ C :=
    fun k => by
      obtain ⟨M, -, -, hM⟩ := exists_bound_testFn (hY k)
      refine ⟨M, fun x => ?_⟩
      rw [← Real.norm_eq_abs, ← inner_gradient]
      exact (norm_inner_le_norm _ _).trans (by simpa using hM x)
  -- one coordinate at a time
  have hk : ∀ k : Fin d, ∫ x in Ω, P.fst x * u.snd x k * Y x k =
      -∫ x in Ω, (u.fst x * P.snd x k * Y x k + u.fst x * P.fst x *
        fderiv ℝ (fun y => Y y k) x (EuclideanSpace.single k 1)) := by
    intro k
    obtain ⟨ζ, hζ, hζf, hζs⟩ := exists_smulPair_mem_H01 hΩ hP (hY k)
    have h := integral_mul_inner_of_mem_H01 hu hζ (EuclideanSpace.single k 1)
    have e1 : ∫ x in Ω, u.fst x * ⟪ζ.snd x, EuclideanSpace.single k 1⟫_ℝ =
        ∫ x in Ω, (u.fst x * P.snd x k * Y x k + u.fst x * P.fst x *
          fderiv ℝ (fun y => Y y k) x (EuclideanSpace.single k 1)) := by
      refine integral_congr_ae ?_
      filter_upwards [hζs] with x hx
      rw [hx, inner_add_left, real_inner_smul_left, real_inner_smul_left, ← snd_apply_eq_inner,
        inner_gradient]
      ring
    have e2 : ∫ x in Ω, ζ.fst x * ⟪u.snd x, EuclideanSpace.single k 1⟫_ℝ =
        ∫ x in Ω, P.fst x * u.snd x k * Y x k := by
      refine integral_congr_ae ?_
      filter_upwards [hζf] with x hx
      rw [hx, ← snd_apply_eq_inner]
      ring
    rw [e1, e2] at h
    linarith
  have hsum1 : ∫ x in Ω, P.fst x * ⟪u.snd x, Y x⟫_ℝ =
      ∑ k, ∫ x in Ω, P.fst x * u.snd x k * Y x k := by
    rw [← integral_finsetSum _ fun k _ => hint (Lp.memLp P.fst) (memLp_snd_apply u k)
      ((hY k).continuous) (hYb k)]
    congr 1
    funext x
    rw [inner_eq_sum_coord, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hsum2 : ∫ x in Ω, u.fst x * (P.fst x * (∑ k, fderiv ℝ (fun y => Y y k) x
        (EuclideanSpace.single k 1)) + ⟪P.snd x, Y x⟫_ℝ) =
      ∑ k, ∫ x in Ω, (u.fst x * P.snd x k * Y x k + u.fst x * P.fst x *
        fderiv ℝ (fun y => Y y k) x (EuclideanSpace.single k 1)) := by
    have hI := integral_finsetSum (μ := volume.restrict Ω) Finset.univ
      (f := fun k x => u.fst x * P.snd x k * Y x k + u.fst x * P.fst x *
        fderiv ℝ (fun y => Y y k) x (EuclideanSpace.single k 1)) fun k _ =>
      (hint (Lp.memLp u.fst) (memLp_snd_apply P k) (hY k).continuous (hYb k)).add
        (hint (Lp.memLp u.fst) (Lp.memLp P.fst) ((hY k).continuous_fderiv_apply _) (hDYb k))
    rw [← hI]
    congr 1
    funext x
    rw [inner_eq_sum_coord, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hsum1, hsum2, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => hk k

end Products

/-! ### Radial test functions -/

section Radial

/-- A function smooth on `ℝ^d \ {0}` and constant near `0` is smooth. -/
theorem contDiff_of_contDiffOn_compl_zero {g : 𝔼 → ℝ} (hg : ContDiffOn ℝ ∞ g {0}ᶜ)
    (h0 : ∀ᶠ x in 𝓝 (0 : 𝔼), g x = g 0) : ContDiff ℝ ∞ g := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  by_cases hx : x = 0
  · subst hx
    exact contDiffAt_const.congr_of_eventuallyEq h0
  · exact (hg x hx).contDiffAt (isOpen_compl_singleton.mem_nhds hx)

theorem contDiffOn_norm_compl : ContDiffOn ℝ ∞ (fun x : 𝔼 => ‖x‖) {0}ᶜ := fun x hx =>
  (contDiffAt_norm ℝ hx).contDiffWithinAt

variable {f : ℝ → ℝ} {ε ρ : ℝ}

/-- The radial primitive `F(r) = ∫_1^r f`. -/
def radPrim (f : ℝ → ℝ) (r : ℝ) : ℝ := ∫ t in (1 : ℝ)..r, f t

theorem hasDerivAt_radPrim (hf : Continuous f) (r : ℝ) : HasDerivAt (radPrim f) (f r) r :=
  (hf.integral_hasStrictDerivAt 1 r).hasDerivAt

theorem contDiff_radPrim (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (radPrim f) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun r => (hasDerivAt_radPrim hf.continuous r).differentiableAt, ?_⟩
  have : deriv (radPrim f) = f := funext fun r => (hasDerivAt_radPrim hf.continuous r).deriv
  rw [this]
  exact hf

theorem radPrim_eq_zero (hf : Continuous f) (hρ : ρ ≤ 1)
    (hsupp : ∀ t, t ∉ Ioo ε ρ → f t = 0) {r : ℝ} (hr : ρ ≤ r) : radPrim f r = 0 := by
  rw [radPrim]
  refine intervalIntegral.integral_zero_ae (Eventually.of_forall fun t ht => hsupp t ?_)
  intro h
  rcases le_total 1 r with h1 | h1
  · rw [uIoc_of_le h1] at ht
    linarith [ht.1, h.2]
  · rw [uIoc_of_ge h1] at ht
    linarith [ht.1, h.2]

theorem radPrim_eq_of_le (hsupp : ∀ t, t ∉ Ioo ε ρ → f t = 0) (hf : Continuous f) (hε : 0 ≤ ε)
    {r : ℝ} (hr : r ≤ ε) : radPrim f r = radPrim f 0 := by
  have hzero : ∫ t in (0 : ℝ)..r, f t = 0 :=
    intervalIntegral.integral_zero_ae (Eventually.of_forall fun t ht => hsupp t fun h => by
      rcases le_total 0 r with h0 | h0
      · rw [uIoc_of_le h0] at ht
        linarith [ht.2, h.1]
      · rw [uIoc_of_ge h0] at ht
        linarith [ht.2, h.1, ht.1, hε])
  rw [radPrim, radPrim, ← intervalIntegral.integral_add_adjacent_intervals
    (b := 0) (hf.intervalIntegrable 1 0) (hf.intervalIntegrable 0 r), hzero, add_zero]

/-- **The radial test function** `η(x) = F(|x|)`, `F' = f`, for `f` vanishing outside `(ε, ρ)`,
`0 < ε`, `ρ < 1`. -/
theorem isTestFn_radPrim (hf : ContDiff ℝ ∞ f) (hε : 0 < ε) (hρ : ρ < 1)
    (hsupp : ∀ t, t ∉ Ioo ε ρ → f t = 0) :
    IsTestFn (ball (0 : 𝔼) 1) (fun x => radPrim f ‖x‖) := by
  have hzero : ∀ x : 𝔼, x ∉ closedBall (0 : 𝔼) ρ → radPrim f ‖x‖ = 0 := fun x hx =>
    radPrim_eq_zero hf.continuous hρ.le hsupp (by
      rw [mem_closedBall_zero_iff, not_le] at hx
      exact hx.le)
  refine ⟨contDiff_of_contDiffOn_compl_zero ((contDiff_radPrim hf).comp_contDiffOn
    contDiffOn_norm_compl) ?_, HasCompactSupport.intro (isCompact_closedBall 0 ρ) hzero, ?_⟩
  · filter_upwards [ball_mem_nhds (0 : 𝔼) hε] with x hx
    simp only [norm_zero]
    exact radPrim_eq_of_le hsupp hf.continuous hε.le (mem_ball_zero_iff.mp hx).le
  · refine (closure_minimal (fun x hx => ?_) isClosed_closedBall).trans
      (closedBall_subset_ball hρ)
    by_contra h
    exact hx (hzero x h)

/-- **The radial vector field** `Y(x) = f(|x|) x / |x|`, the gradient of `F(|x|)`. -/
def radField (f : ℝ → ℝ) (x : 𝔼) : 𝔼 := (f ‖x‖ * ‖x‖⁻¹) • x

theorem gradient_radPrim (hf : ContDiff ℝ ∞ f) (hε : 0 < ε)
    (hsupp : ∀ t, t ∉ Ioo ε ρ → f t = 0) (x : 𝔼) :
    gradient (fun y : 𝔼 => radPrim f ‖y‖) x = radField f x := by
  by_cases hx : x = 0
  · subst hx
    have h0 : (fun y : 𝔼 => radPrim f ‖y‖) =ᶠ[𝓝 0] fun _ => radPrim f 0 := by
      filter_upwards [ball_mem_nhds (0 : 𝔼) hε] with y hy
      exact radPrim_eq_of_le hsupp hf.continuous hε.le (mem_ball_zero_iff.mp hy).le
    rw [gradient_eq_zero_of_eventuallyEq_const h0, radField, smul_zero]
  · have h := (hasDerivAt_radPrim hf.continuous ‖x‖).comp_hasFDerivAt x
      (hasFDerivAt_norm_of_ne hx)
    rw [gradient, show (fun y : 𝔼 => radPrim f ‖y‖) = radPrim f ∘ fun y : 𝔼 => ‖y‖ from rfl,
      h.fderiv]
    apply (toDual ℝ 𝔼).injective
    ext v
    simp [radField, real_inner_smul_left, mul_assoc]

theorem radField_eq_zero {x : 𝔼} (hsupp : ∀ t, t ∉ Ioo ε ρ → f t = 0) (hx : ‖x‖ ∉ Ioo ε ρ) :
    radField f x = 0 := by
  rw [radField, hsupp _ hx, zero_mul, zero_smul]

theorem isTestFn_radField (hf : ContDiff ℝ ∞ f) (hε : 0 < ε) (hρ : ρ < 1)
    (hsupp : ∀ t, t ∉ Ioo ε ρ → f t = 0) (k : Fin d) :
    IsTestFn (ball (0 : 𝔼) 1) (fun x => radField f x k) := by
  have hzero : ∀ x : 𝔼, x ∉ closedBall (0 : 𝔼) ρ → radField f x k = 0 := fun x hx => by
    rw [radField_eq_zero hsupp fun h => hx (mem_closedBall_zero_iff.mpr h.2.le), PiLp.zero_apply]
  refine ⟨contDiff_of_contDiffOn_compl_zero ?_ ?_, HasCompactSupport.intro
    (isCompact_closedBall 0 ρ) hzero, ?_⟩
  · have : (fun x : 𝔼 => radField f x k) = fun x => f ‖x‖ * ‖x‖⁻¹ * x k := by
      funext x
      simp [radField]
    rw [this]
    refine ((hf.comp_contDiffOn contDiffOn_norm_compl).mul
      (contDiffOn_norm_compl.inv fun x hx => norm_ne_zero_iff.mpr hx)).mul ?_
    exact (EuclideanSpace.proj k : 𝔼 →L[ℝ] ℝ).contDiff.contDiffOn
  · filter_upwards [ball_mem_nhds (0 : 𝔼) hε] with x hx
    have h1 : ‖x‖ ∉ Ioo ε ρ := fun h => by linarith [mem_ball_zero_iff.mp hx, h.1]
    have h2 : ‖(0 : 𝔼)‖ ∉ Ioo ε ρ := fun h => by
      rw [norm_zero] at h
      linarith [h.1]
    rw [radField_eq_zero hsupp h1, radField_eq_zero hsupp h2]
  · refine (closure_minimal (fun x hx => ?_) isClosed_closedBall).trans
      (closedBall_subset_ball hρ)
    by_contra h
    exact hx (hzero x h)

/-- **The divergence of the radial field**: `div Y = f'(r) + (d - 1) f(r)/r`, `r = |x| ≠ 0`. -/
theorem div_radField (hf : ContDiff ℝ ∞ f) {x : 𝔼} (hx : x ≠ 0) :
    ∑ k, fderiv ℝ (fun y => radField f y k) x (EuclideanSpace.single k 1) =
      deriv f ‖x‖ + (d - 1) * (f ‖x‖ / ‖x‖) := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  -- `Y_k = h · x_k` with `h(y) = f(|y|)/|y|`
  set g : ℝ → ℝ := fun t => f t * t⁻¹
  have hg : HasDerivAt g (deriv f ‖x‖ * ‖x‖⁻¹ + f ‖x‖ * (-(‖x‖ ^ 2)⁻¹)) ‖x‖ :=
    ((hf.differentiable (by simp) ‖x‖).hasDerivAt).mul (hasDerivAt_inv hn)
  have hh : HasFDerivAt (fun y : 𝔼 => g ‖y‖)
      ((deriv f ‖x‖ * ‖x‖⁻¹ + f ‖x‖ * (-(‖x‖ ^ 2)⁻¹)) • (‖x‖⁻¹ • innerSL ℝ x)) x :=
    hg.comp_hasFDerivAt x (hasFDerivAt_norm_of_ne hx)
  have hk : ∀ k : Fin d, fderiv ℝ (fun y => radField f y k) x (EuclideanSpace.single k 1) =
      fderiv ℝ (fun y : 𝔼 => g ‖y‖) x (EuclideanSpace.single k 1) * x k + g ‖x‖ := by
    intro k
    have hp : HasFDerivAt (fun y : 𝔼 => y k) (EuclideanSpace.proj k : 𝔼 →L[ℝ] ℝ) x :=
      (EuclideanSpace.proj k : 𝔼 →L[ℝ] ℝ).hasFDerivAt
    have e : (fun y => radField f y k) = (fun y : 𝔼 => g ‖y‖) * fun y : 𝔼 => y k := by
      funext y
      simp [radField, g]
    rw [e, (hh.mul hp).fderiv, hh.fderiv]
    simp
    ring
  simp_rw [hk]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show ∑ k : Fin d, fderiv ℝ (fun y : 𝔼 => g ‖y‖) x (EuclideanSpace.single k 1) * x k =
      fderiv ℝ (fun y : 𝔼 => g ‖y‖) x x by
    rw [fderiv_eq_sum_coord x x]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _]
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq,
    smul_eq_mul, g]
  field_simp
  ring

end Radial

/-! ### The key identity -/

section Key

variable {c : CoeffField (EuclideanSpace ℝ (Fin d)) volume}

theorem inner_homG_self {δ : ℝ} {v : LinkPair d} {x : 𝔼} (hx : x ≠ 0)
    (htan : ⟪v.snd (sphProj x), ((sphProj x : Sph d) : 𝔼)⟫_ℝ = 0) :
    ⟪homG δ v x, x⟫_ℝ = δ * homP δ v x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hxs : x = ‖x‖ • ((sphProj x : Sph d) : 𝔼) := (norm_smul_sphProj (x := x)).symm
  have hs : ⟪((sphProj x : Sph d) : 𝔼), ((sphProj x : Sph d) : 𝔼)⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere (sphProj x), one_pow]
  have h1 : ‖x‖ ^ (δ - 1) * ‖x‖ = ‖x‖ ^ δ := by
    rw [← Real.rpow_add_one hn]
    ring_nf
  calc ⟪homG δ v x, x⟫_ℝ = ⟪homG δ v x, ‖x‖ • ((sphProj x : Sph d) : 𝔼)⟫_ℝ := by rw [← hxs]
    _ = ‖x‖ * (‖x‖ ^ (δ - 1) * (δ * v.fst (sphProj x) * 1 + 0)) := by
        simp only [homG, homFun, homGradProfile, real_inner_smul_left, real_inner_smul_right,
          inner_add_left, htan, hs, smul_eq_mul]
    _ = δ * ((‖x‖ ^ (δ - 1) * ‖x‖) * v.fst (sphProj x)) := by ring
    _ = δ * homP δ v x := by rw [h1, homP, homFun, smul_eq_mul]

theorem CoeffField.IsConical.inner_A_radField (hc : c.IsConical) (f : ℝ → ℝ) (x G : 𝔼) :
    ⟪c.A x G, radField f x⟫_ℝ = ⟪G, radField f x⟫_ℝ := by
  rw [c.symm, radField, map_smul, hc.radial]

/-- **The key identity.** Let `u` be weakly harmonic on `B_1`, and `P = |x|^δ φ(x/|x|)` with
`(φ, Γ)` a link eigenfunction for `λ = δ(δ + d - 2)`. For every `f ∈ C^∞` vanishing outside
`(ε, ρ) ⊆ (0, 1)`, `∫_{B_1} u P (f'(|x|) + (2δ + d - 1) f(|x|)/|x|) = 0`. -/
theorem key_identity (hd : 2 ≤ d) (hc : c.IsConical) {lam δ : ℝ} {v : LinkPair d}
    (hE : IsLinkEigen hc lam v) (hlam : lam = δ * (δ + d - 2))
    (hP : MemLp (homP δ v) 2 (volume.restrict (ball (0 : 𝔼) 1)))
    (hG : MemLp (homG δ v) 2 (volume.restrict (ball (0 : 𝔼) 1)))
    {u : L2Pair volume (ball (0 : 𝔼) 1)} (hu : c.IsWeakSolution 0 u)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {ε ρ : ℝ} (hε : 0 < ε) (hρ : ρ < 1)
    (hsupp : ∀ t, t ∉ Ioo ε ρ → f t = 0) :
    ∫ x in ball (0 : 𝔼) 1, u.fst x * (homP δ v x *
      (deriv f ‖x‖ + (2 * δ + d - 1) * (f ‖x‖ / ‖x‖))) = 0 := by
  set P := homPair δ v 1 hP hG
  have hPsol : c.IsWeakSolution 0 P := homPair_isWeakSolution hP hG hd hc hE hlam
  have hη := isTestFn_radPrim (d := d) hf hε hρ hsupp
  have hY := isTestFn_radField (d := d) hf hε hρ hsupp
  have hW := wronskian c isOpen_ball hu hPsol hη
  simp_rw [gradient_radPrim hf hε hsupp, hc.inner_A_radField] at hW
  have hI := integral_mul_inner_vectorField isOpen_ball hu.1 hPsol.1 hY
  -- bounds
  obtain ⟨Mf, hMf⟩ : ∃ C, ∀ t, |f t| ≤ C := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hf.continuous.continuousOn (s := Icc ε ρ))
    refine ⟨max C 0, fun t => ?_⟩
    by_cases ht : t ∈ Ioo ε ρ
    · exact ((Real.norm_eq_abs _).symm.trans_le (hC t (Ioo_subset_Icc_self ht))).trans
        (le_max_left _ _)
    · rw [hsupp t ht, abs_zero]
      exact le_max_right _ _
  have hMY : ∀ x : 𝔼, ‖radField f x‖ ≤ Mf := fun x => by
    by_cases hx : x = 0
    · have : radField f x = 0 := by simp [hx, radField]
      rw [this, norm_zero]
      exact (abs_nonneg (f 0)).trans (hMf 0)
    · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have : ‖radField f x‖ = |f ‖x‖| := by
        simp only [radField, norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_norm, mul_assoc,
          inv_mul_cancel₀ hn, mul_one]
      rw [this]
      exact hMf _
  have hMD : ∃ C, ∀ x : 𝔼, |∑ k, fderiv ℝ (fun y : 𝔼 => radField f y k) x
      (EuclideanSpace.single k 1)| ≤ C := by
    choose M hM using fun k => exists_bound_testFn (hY k)
    refine ⟨∑ k, M k, fun x => (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun k _ => ?_)⟩
    rw [← Real.norm_eq_abs, ← inner_gradient]
    exact (norm_inner_le_norm _ _).trans (by simpa using (hM k).2.2 x)
  obtain ⟨MD, hMD⟩ := hMD
  have hYm : Measurable fun x : 𝔼 => radField f x := by
    have := hf.continuous.measurable
    unfold radField
    fun_prop
  have hdivm : Measurable fun x : 𝔼 => ∑ k, fderiv ℝ (fun y : 𝔼 => radField f y k) x
      (EuclideanSpace.single k 1) :=
    Finset.measurable_sum _ fun k _ => ((hY k).continuous_fderiv_apply _).measurable
  have hGY : MemLp (fun x => ⟪P.snd x, radField f x⟫_ℝ) 2 (volume.restrict (ball (0 : 𝔼) 1)) :=
    (Lp.memLp P.snd).of_le_mul (c := Mf) ((Lp.aestronglyMeasurable P.snd).inner
      hYm.aestronglyMeasurable) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, mul_comm]
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (hMY x) (norm_nonneg _)))
  have hint2 : Integrable (fun x => u.fst x * ⟪P.snd x, radField f x⟫_ℝ)
      (volume.restrict (ball (0 : 𝔼) 1)) :=
    integrable_mul_of_memLp_two (Lp.memLp u.fst) hGY
  have hint3 : Integrable (fun x => u.fst x * P.fst x * ∑ k, fderiv ℝ (fun y => radField f y k)
      x (EuclideanSpace.single k 1)) (volume.restrict (ball (0 : 𝔼) 1)) :=
    (integrable_mul_of_memLp_two (Lp.memLp u.fst) (Lp.memLp P.fst)).mul_bdd
      hdivm.aestronglyMeasurable (c := MD) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hMD x)
  have hint1 : Integrable (fun x => u.fst x * (P.fst x * (∑ k, fderiv ℝ (fun y => radField f y k)
      x (EuclideanSpace.single k 1)) + ⟪P.snd x, radField f x⟫_ℝ))
      (volume.restrict (ball (0 : 𝔼) 1)) :=
    (hint3.add hint2).congr (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  -- combine the Wronskian identity and the integration by parts
  have hsum : ∫ x in ball (0 : 𝔼) 1, (u.fst x * (P.fst x * (∑ k, fderiv ℝ
      (fun y => radField f y k) x (EuclideanSpace.single k 1)) + ⟪P.snd x, radField f x⟫_ℝ) +
        u.fst x * ⟪P.snd x, radField f x⟫_ℝ) = 0 := by
    rw [integral_add hint1 hint2]
    linarith
  rw [← hsum]
  refine integral_congr_ae ?_
  filter_upwards [hP.coeFn_toLp, hG.coeFn_toLp, ae_restrict_of_ae ae_ne_zero,
    ae_restrict_of_ae (ae_of_ae_sphere (ae_inner_linkSnd_eq_zero hE.1))] with x hPx hGx hx0 htan
  have hP1 : P.fst x = homP δ v x := hPx
  have hG1 : P.snd x = homG δ v x := hGx
  rw [hP1, hG1, div_radField hf hx0]
  have hY1 : ⟪homG δ v x, radField f x⟫_ℝ = f ‖x‖ * ‖x‖⁻¹ * (δ * homP δ v x) := by
    rw [radField, real_inner_smul_right, inner_homG_self hx0 htan]
  rw [hY1]
  ring

end Key

end ConicalKahler.Sobolev
