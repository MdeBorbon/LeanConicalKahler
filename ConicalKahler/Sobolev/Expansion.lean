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

end ConicalKahler.Sobolev
