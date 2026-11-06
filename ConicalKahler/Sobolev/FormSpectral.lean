module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# The spectral theorem for coercive forms with compact embedding

This is the abstract form of the paper's proof of Lemma 3.1 (and of the Dirichlet spectral theorem
of `Spectral.lean`). Let `V`, `H` be real Hilbert spaces, `ι : V → H` a bounded **compact** map,
and `b` a bounded, symmetric, **coercive** bilinear form on `V`. By Lax–Milgram, for every `f ∈ H`
there is a unique `S f ∈ V` with

  `b(S f, ψ) = ⟨f, ι ψ⟩` for all `ψ ∈ V` (`formSol_spec`),

and `S = T⁻¹ ∘ ι*` where `T` is the operator of `b` (`formSol`). The operator `K = ι ∘ S : H → H`
(`formK`) is compact, symmetric and positive, and injective when `ι` has dense range. An
eigenvector `K f = μ f`, `f ≠ 0`, has `μ > 0`, and `φ = S f` satisfies `b(φ, ψ) = μ⁻¹ ⟨ι φ, ι ψ⟩`
(`formK_eigen`).

`exists_hilbertBasis_eigenvectors`: a compact symmetric operator on a Hilbert space has a **Hilbert
basis of eigenvectors** (Mathlib's spectral theorem plus a choice of Hilbert bases of the
eigenspaces). `HilbertBasis.countable_index`: in a separable space the index set is countable.
-/

@[expose] public section

noncomputable section

open Filter Topology InnerProductSpace Set Module
open scoped ENNReal

namespace ConicalKahler.Sobolev

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section Form

variable (ι : V →L[ℝ] H) {b : V →L[ℝ] V →L[ℝ] ℝ} (hb : IsCoercive b)

/-- **The solution operator of the form `b`**: `b(S f, ψ) = ⟨f, ι ψ⟩` for all `ψ`. -/
def formSol : H →L[ℝ] V :=
  (hb.continuousLinearEquivOfBilin.symm : V →L[ℝ] V) ∘L ContinuousLinearMap.adjoint ι

theorem formSol_spec (f : H) (ψ : V) : b (formSol ι hb f) ψ = ⟪f, ι ψ⟫_ℝ := by
  rw [formSol, ← IsCoercive.continuousLinearEquivOfBilin_apply hb]
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  rw [ContinuousLinearMap.adjoint_inner_left]

theorem eq_formSol {f : H} {φ : V} (h : ∀ ψ, b φ ψ = ⟪f, ι ψ⟫_ℝ) : φ = formSol ι hb f := by
  obtain ⟨C, hC, hcoer⟩ := id hb
  have hz : b (φ - formSol ι hb f) (φ - formSol ι hb f) = 0 := by
    rw [ContinuousLinearMap.map_sub₂, h, formSol_spec, sub_self]
  have h1 := hcoer (φ - formSol ι hb f)
  rw [hz, mul_assoc] at h1
  have h2 : ‖φ - formSol ι hb f‖ * ‖φ - formSol ι hb f‖ ≤ 0 := by
    by_contra hneg
    linarith [mul_pos hC (not_le.mp hneg)]
  exact sub_eq_zero.mp (norm_eq_zero.mp (mul_self_eq_zero.mp (le_antisymm h2 (mul_self_nonneg _))))

/-- **The operator `K = ι ∘ S : H → H`.** -/
def formK : H →L[ℝ] H := ι ∘L formSol ι hb

theorem formK_apply (f : H) : formK ι hb f = ι (formSol ι hb f) := rfl

/-- `⟨K f, g⟩ = b(S g, S f)`. -/
theorem inner_formK (f g : H) : ⟪formK ι hb f, g⟫_ℝ = b (formSol ι hb g) (formSol ι hb f) := by
  rw [formK_apply, real_inner_comm, formSol_spec]

theorem isCompactOperator_formK (hι : IsCompactOperator ι) : IsCompactOperator (formK ι hb) :=
  hι.comp_clm _

theorem isSymmetric_formK (hsymm : ∀ u v, b u v = b v u) : (formK ι hb).IsSymmetric := by
  intro f g
  change ⟪formK ι hb f, g⟫_ℝ = ⟪f, formK ι hb g⟫_ℝ
  rw [inner_formK, real_inner_comm (formK ι hb g) f, inner_formK, hsymm]

theorem inner_formK_self_nonneg (f : H) : 0 ≤ ⟪formK ι hb f, f⟫_ℝ := by
  rw [inner_formK]
  obtain ⟨C, hC, hcoer⟩ := id hb
  exact le_trans (by positivity) (hcoer _)

/-- `K` is injective when `ι` has dense range. -/
theorem injective_formK (hdense : DenseRange ι) : Function.Injective (formK ι hb) := by
  refine (injective_iff_map_eq_zero (formK ι hb)).mpr fun f hKf => ?_
  have h0 : b (formSol ι hb f) (formSol ι hb f) = 0 := by
    rw [← inner_formK, hKf, inner_zero_left]
  have hS : formSol ι hb f = 0 := by
    obtain ⟨C, hC, hcoer⟩ := id hb
    have h1 := hcoer (formSol ι hb f)
    rw [h0, mul_assoc] at h1
    have h2 : ‖formSol ι hb f‖ * ‖formSol ι hb f‖ ≤ 0 := by
      by_contra hneg
      linarith [mul_pos hC (not_le.mp hneg)]
    exact norm_eq_zero.mp (mul_self_eq_zero.mp (le_antisymm h2 (mul_self_nonneg _)))
  -- `f` is orthogonal to the range of `ι`
  have horth : ∀ ψ, ⟪f, ι ψ⟫_ℝ = 0 := fun ψ => by
    rw [← formSol_spec ι hb, hS, map_zero, zero_apply]
  have hcl : IsClosed {g : H | ⟪f, g⟫_ℝ = 0} := isClosed_eq (continuous_const.inner continuous_id)
    continuous_const
  have hall : ∀ g, ⟪f, g⟫_ℝ = 0 := fun g =>
    hdense.induction_on (p := fun g => ⟪f, g⟫_ℝ = 0) g hcl horth
  exact inner_self_eq_zero.mp (hall f)

/-- **Eigenvectors of `K` solve the eigenvalue problem of the form.** If `K f = μ f` with `f ≠ 0`
and `ι` has dense range, then `μ > 0`, and `φ = S f` satisfies `ι φ = μ f` and
`b(φ, ψ) = μ⁻¹ ⟨ι φ, ι ψ⟩` for all `ψ`. -/
theorem formK_eigen (hdense : DenseRange ι) {μ : ℝ} {f : H} (hf : f ≠ 0)
    (hKf : formK ι hb f = μ • f) :
    0 < μ ∧ ι (formSol ι hb f) = μ • f ∧
      ∀ ψ, b (formSol ι hb f) ψ = μ⁻¹ * ⟪ι (formSol ι hb f), ι ψ⟫_ℝ := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hKf
    exact hf (injective_formK ι hb hdense (hKf.trans (map_zero _).symm))
  have hpos := inner_formK_self_nonneg ι hb f
  rw [hKf, real_inner_smul_left, real_inner_self_eq_norm_sq] at hpos
  have hn : 0 < ‖f‖ ^ 2 := by positivity
  have hμpos : 0 < μ := lt_of_le_of_ne (nonneg_of_mul_nonneg_left hpos hn) (Ne.symm hμ0)
  refine ⟨hμpos, hKf, fun ψ => ?_⟩
  rw [formSol_spec, ← formK_apply, hKf, real_inner_smul_left, ← mul_assoc, inv_mul_cancel₀ hμ0,
    one_mul]

end Form

/-! ### Hilbert bases of eigenvectors -/

section Eigenbasis

/-- The eigenspace of `T` for the eigenvalue `μ`. -/
abbrev eigSp (T : H →L[ℝ] H) (μ : ℝ) : Submodule ℝ H :=
  Module.End.eigenspace (T : Module.End ℝ H) μ

omit [CompleteSpace H] in
theorem mem_eigSp {T : H →L[ℝ] H} {μ : ℝ} {v : H} : v ∈ eigSp T μ ↔ T v = μ • v :=
  Module.End.mem_eigenspace_iff

omit [CompleteSpace H] in
theorem isClosed_eigSp (T : H →L[ℝ] H) (μ : ℝ) : IsClosed (eigSp T μ : Set H) := by
  have : (eigSp T μ : Set H) = {v | T v = μ • v} := by
    ext v
    exact mem_eigSp
  rw [this]
  exact isClosed_eq T.continuous (continuous_const.smul continuous_id)

instance (T : H →L[ℝ] H) (μ : ℝ) : CompleteSpace (eigSp T μ) :=
  (isClosed_eigSp T μ).completeSpace_coe

variable {T : H →L[ℝ] H}

/-- **A compact symmetric operator has a Hilbert basis of eigenvectors.** The basis is indexed by
a set `s ⊆ H` of eigenvectors. -/
theorem exists_hilbertBasis_eigenvectors (hT : IsCompactOperator T) (hsym : T.IsSymmetric) :
    ∃ (s : Set H) (B : HilbertBasis s ℝ H), ⇑B = ((↑) : s → H) ∧
      ∀ v ∈ s, ∃ μ : ℝ, T v = μ • v := by
  classical
  choose w Bw hBw using fun μ : ℝ => exists_hilbertBasis ℝ (eigSp T μ)
  let s : Set H := ⋃ μ, Subtype.val '' w μ
  have hmem : ∀ v ∈ s, ∃ μ, ∃ x ∈ w μ, (x : H) = v := fun v hv => by
    obtain ⟨μ, hμ⟩ := mem_iUnion.mp hv
    obtain ⟨x, hx, rfl⟩ := hμ
    exact ⟨μ, x, hx, rfl⟩
  have hBmem : ∀ μ (i : w μ), (((i : eigSp T μ)) : H) ∈ s := fun μ i =>
    mem_iUnion.mpr ⟨μ, ⟨i, i.2, rfl⟩⟩
  have hBi : ∀ μ (i : w μ), Bw μ i = i := fun μ i => by rw [hBw μ]
  -- orthonormality
  have hortho : Orthonormal ℝ ((↑) : s → H) := by
    refine ⟨fun v => ?_, fun v v' hvv' => ?_⟩
    · obtain ⟨μ, x, hx, hxv⟩ := hmem v v.2
      have h1 := (Bw μ).orthonormal.1 ⟨x, hx⟩
      rw [hBi] at h1
      rw [← hxv]
      exact h1
    · obtain ⟨μ, x, hx, hxv⟩ := hmem v v.2
      obtain ⟨μ', x', hx', hxv'⟩ := hmem v' v'.2
      by_cases hμ : μ = μ'
      · subst hμ
        have hne : (⟨x, hx⟩ : w μ) ≠ ⟨x', hx'⟩ := by
          intro h
          apply hvv'
          apply Subtype.ext
          rw [← hxv, ← hxv']
          exact congrArg (fun y : w μ => ((y : eigSp T μ) : H)) h
        have h2 : ⟪Bw μ ⟨x, hx⟩, Bw μ ⟨x', hx'⟩⟫_ℝ = 0 := (Bw μ).orthonormal.2 hne
        rw [hBi, hBi] at h2
        rw [← hxv, ← hxv']
        exact h2
      · have h2 := hsym.orthogonalFamily_eigenspaces hμ x x'
        rw [← hxv, ← hxv']
        exact h2
  -- completeness
  have hsp : (Submodule.span ℝ (Set.range ((↑) : s → H)))ᗮ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzs : ∀ v ∈ s, ⟪z, v⟫_ℝ = 0 := fun v hv => by
      rw [real_inner_comm]
      exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self (⟨v, hv⟩ : s))) hz
    have hzE : ∀ μ, ∀ y ∈ eigSp T μ, ⟪z, y⟫_ℝ = 0 := by
      intro μ y hy
      let g : eigSp T μ →L[ℝ] ℝ := (innerSL ℝ z).comp (eigSp T μ).subtypeL
      have hg : g = 0 := by
        refine ContinuousLinearMap.ext_on
          ((Submodule.dense_iff_topologicalClosure_eq_top).mpr (Bw μ).dense_span) ?_
        rintro _ ⟨i, rfl⟩
        change ⟪z, ((Bw μ i : eigSp T μ) : H)⟫_ℝ = 0
        rw [hBi]
        exact hzs _ (hBmem μ i)
      have := congrArg (fun L : eigSp T μ →L[ℝ] ℝ => L ⟨y, hy⟩) hg
      simpa [g] using this
    have hz' : z ∈ (⨆ μ, eigSp T μ)ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro y hy
      exact Submodule.iSup_induction _ (motive := fun y => ⟪z, y⟫_ℝ = 0) hy
        (fun μ y hy => hzE μ y hy) (inner_zero_right _)
        (fun y₁ y₂ h₁ h₂ => by rw [inner_add_right, h₁, h₂, add_zero])
    rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hsym] at hz'
    exact hz'
  refine ⟨s, HilbertBasis.mkOfOrthogonalEqBot hortho hsp, ?_, ?_⟩
  · exact HilbertBasis.coe_mkOfOrthogonalEqBot hortho hsp
  · intro v hv
    obtain ⟨μ, x, -, rfl⟩ := hmem v hv
    exact ⟨μ, mem_eigSp.mp x.2⟩

omit [CompleteSpace H] in
/-- In a separable inner product space, an orthonormal family is countable. -/
theorem Orthonormal.countable_of_separable [TopologicalSpace.SeparableSpace H] {ι : Type*}
    {v : ι → H} (hv : Orthonormal ℝ v) : Countable ι := by
  have hdisj : Pairwise (Function.onFun Disjoint fun i => Metric.ball (v i) (1 / 2)) := by
    intro i j hij
    refine Metric.ball_disjoint_ball ?_
    rw [dist_eq_norm]
    have h2 : ‖v i - v j‖ ^ 2 = 2 := by
      rw [norm_sub_sq_real, hv.1 i, hv.1 j, hv.2 hij]
      norm_num
    nlinarith [norm_nonneg (v i - v j)]
  exact hdisj.countable_of_isOpen_disjoint (fun i => Metric.isOpen_ball)
    (fun i => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)

end Eigenbasis

/-- **Domination by a compact operator.** If `J` is compact and `‖T x‖ ≤ C ‖J x‖` for all `x`,
then `T` is compact. -/
theorem isCompactOperator_of_norm_le {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [CompleteSpace Z] {J : X →L[ℝ] Y} (hJ : IsCompactOperator J) {T : X →L[ℝ] Z} {C : ℝ}
    (hC : 0 < C) (h : ∀ x, ‖T x‖ ≤ C * ‖J x‖) : IsCompactOperator T := by
  obtain ⟨K, hK, hKU⟩ := hJ
  set U := J ⁻¹' K
  rw [isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image]
  refine ⟨U, hKU, TotallyBounded.isCompact_of_isClosed ?_ isClosed_closure⟩
  refine TotallyBounded.closure ?_
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hJU : TotallyBounded (J '' U) :=
    hK.totallyBounded.subset (image_subset_iff.mpr subset_rfl)
  obtain ⟨t, htU, htf, hcov⟩ := Metric.finite_approx_of_totallyBounded hJU (ε / C) (by positivity)
  choose! x hxU hxJ using fun y (hy : y ∈ t) => htU hy
  refine ⟨(fun y => T (x y)) '' t, htf.image _, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp (hcov ⟨z, hz, rfl⟩)
  refine mem_iUnion₂.mpr ⟨T (x y), mem_image_of_mem _ hy, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, ← map_sub]
  calc ‖T (z - x y)‖ ≤ C * ‖J (z - x y)‖ := h _
    _ = C * dist (J z) y := by rw [map_sub, hxJ y hy, dist_eq_norm]
    _ < C * (ε / C) := by gcongr; exact hzy
    _ = ε := by field_simp


end ConicalKahler.Sobolev
