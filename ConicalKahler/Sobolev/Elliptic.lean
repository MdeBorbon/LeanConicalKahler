module

public import ConicalKahler.Sobolev.H1
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Divergence-form equations with bounded measurable coefficients

A `CoeffField` is a field `x ↦ A(x)` of symmetric operators on `F`, measurable, with
`λ |v|² ≤ ⟨A(x) v, v⟩ ≤ Λ |v|²` for almost every `x`. In the paper's real coordinates the cone
Laplacian is of this form, with `A = g⁻¹` (`ConicalKahler.Sobolev.ConeLaplacian`).

* `mulOp c Ω : L²(Ω; F) →L L²(Ω; F)`, `G ↦ A G`, with `‖A G‖ ≤ Λ ‖G‖`.
* `dirichletForm c Ω (u, G) (v, H) = ∫_Ω ⟨A G, H⟩`, a bounded bilinear form on `L²(Ω) × L²(Ω; F)`.
* `IsWeakSolution c f v`: `v = (u, ∇u) ∈ W^{1,2}(Ω)` and `∫_Ω ⟨A ∇u, ∇φ⟩ = ∫_Ω f φ` for every test
  function `φ` on `Ω`, i.e. `-div(A ∇u) = f` weakly. `IsWeakSolution.forall_H01`: the identity then
  holds for every test pair `ψ ∈ W^{1,2}_0(Ω)`.
* **Existence and uniqueness** (`existsUnique_H01_isWeakSolution`): on a bounded `Ω` and for every
  `f ∈ L²(Ω)`, there is exactly one weak solution in `W^{1,2}_0(Ω)`. The proof is the Lax–Milgram
  theorem (Mathlib) for the Dirichlet form, which is coercive on `W^{1,2}_0(Ω)` by the
  Friedrichs–Poincaré inequality.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff ENNReal

namespace ConicalKahler.Sobolev

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-! ### Symmetric non-negative operators -/

/-- Cauchy–Schwarz for a symmetric non-negative operator:
`⟨T v, w⟩² ≤ ⟨T v, v⟩ ⟨T w, w⟩`. -/
theorem inner_sq_le_of_symm (T : F →L[ℝ] F) (hsymm : ∀ v w, ⟪T v, w⟫_ℝ = ⟪v, T w⟫_ℝ)
    (hpos : ∀ v, 0 ≤ ⟪T v, v⟫_ℝ) (v w : F) : ⟪T v, w⟫_ℝ ^ 2 ≤ ⟪T v, v⟫_ℝ * ⟪T w, w⟫_ℝ := by
  have hwv : ⟪T w, v⟫_ℝ = ⟪T v, w⟫_ℝ := by rw [hsymm, real_inner_comm]
  have h := discrim_le_zero (K := ℝ) (a := ⟪T w, w⟫_ℝ) (b := 2 * ⟪T v, w⟫_ℝ)
    (c := ⟪T v, v⟫_ℝ) fun t => by
      have := hpos (v + t • w)
      simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hwv] at this
      linarith
  unfold discrim at h
  nlinarith

/-- A symmetric operator with `0 ≤ ⟨T v, v⟩ ≤ Λ |v|²` has `|T v| ≤ Λ |v|`. -/
theorem norm_apply_le_of_symm (T : F →L[ℝ] F) (hsymm : ∀ v w, ⟪T v, w⟫_ℝ = ⟪v, T w⟫_ℝ)
    (hpos : ∀ v, 0 ≤ ⟪T v, v⟫_ℝ) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ v, ⟪T v, v⟫_ℝ ≤ Λ * ‖v‖ ^ 2)
    (v : F) : ‖T v‖ ≤ Λ * ‖v‖ := by
  set u := T v
  have h1 := inner_sq_le_of_symm T hsymm hpos v u
  have h2 : ⟪T v, u⟫_ℝ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
  rw [h2] at h1
  have h3 : ‖u‖ ^ 2 * ‖u‖ ^ 2 ≤ (Λ * ‖v‖ ^ 2) * (Λ * ‖u‖ ^ 2) := by
    calc ‖u‖ ^ 2 * ‖u‖ ^ 2 = (‖u‖ ^ 2) ^ 2 := by ring
      _ ≤ ⟪T v, v⟫_ℝ * ⟪T u, u⟫_ℝ := h1
      _ ≤ (Λ * ‖v‖ ^ 2) * (Λ * ‖u‖ ^ 2) :=
          mul_le_mul (hΛ v) (hΛ u) (hpos u) (by positivity)
  rcases (norm_nonneg u).eq_or_lt with h | h
  · rw [← h]
    positivity
  · have h4 : ‖u‖ ^ 2 ≤ (Λ * ‖v‖) ^ 2 := by
      have hu2 : 0 < ‖u‖ ^ 2 := by positivity
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg u) (by positivity) two_ne_zero).mp h4

/-- An operator field is strongly measurable once its matrix coefficients are measurable. -/
theorem stronglyMeasurable_of_inner [MeasurableSpace F] {A : F → F →L[ℝ] F}
    (hA : ∀ v w, Measurable fun x => ⟪A x v, w⟫_ℝ) : StronglyMeasurable A := by
  let b := stdOrthonormalBasis ℝ F
  have hexp : A = fun x => ∑ i, ∑ j, ⟪A x (b i), b j⟫_ℝ • ((innerSL ℝ (b i)).smulRight (b j)) := by
    funext x
    ext v
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
    rw [Finset.sum_comm]
    calc A x v = ∑ j, ⟪b j, A x v⟫_ℝ • b j := (b.sum_repr' (A x v)).symm
      _ = ∑ j, ∑ i, (⟪A x (b i), b j⟫_ℝ * ⟪b i, v⟫_ℝ) • b j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_smul]
          congr 1
          conv_lhs => rw [← b.sum_repr' v]
          rw [map_sum, inner_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul, real_inner_smul_right, real_inner_comm (b j) (A x (b i))]
          ring
  rw [hexp]
  have h := Finset.stronglyMeasurable_sum Finset.univ fun i _ =>
    Finset.stronglyMeasurable_sum Finset.univ fun j _ =>
      (hA (b i) (b j)).stronglyMeasurable.smul_const ((innerSL ℝ (b i)).smulRight (b j))
  convert h using 1
  funext x
  simp [Finset.sum_apply]

/-! ### Coefficient fields -/

variable [MeasurableSpace F] [BorelSpace F]

/-- A **symmetric, measurable, uniformly elliptic coefficient field** on `F`. -/
structure CoeffField (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] (μ : Measure F) where
  /-- The operator field. -/
  A : F → F →L[ℝ] F
  /-- Its matrix coefficients are measurable. -/
  measurable_inner : ∀ v w, Measurable fun x => ⟪A x v, w⟫_ℝ
  /-- It is symmetric. -/
  symm : ∀ x v w, ⟪A x v, w⟫_ℝ = ⟪v, A x w⟫_ℝ
  /-- Ellipticity constant. -/
  lam : ℝ
  /-- Upper bound. -/
  Λ : ℝ
  lam_pos : 0 < lam
  lam_le : lam ≤ Λ
  /-- Uniform ellipticity, almost everywhere. -/
  coercive : ∀ᵐ x ∂μ, ∀ v, lam * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ
  /-- Upper bound, almost everywhere. -/
  bounded : ∀ᵐ x ∂μ, ∀ v, ⟪A x v, v⟫_ℝ ≤ Λ * ‖v‖ ^ 2

namespace CoeffField

variable {μ : Measure F} (c : CoeffField F μ)

theorem Λ_pos : 0 < c.Λ := c.lam_pos.trans_le c.lam_le

theorem stronglyMeasurable : StronglyMeasurable c.A :=
  stronglyMeasurable_of_inner c.measurable_inner

/-- `|A(x) v| ≤ Λ |v|` for almost every `x`. -/
theorem ae_norm_apply_le : ∀ᵐ x ∂μ, ∀ v, ‖c.A x v‖ ≤ c.Λ * ‖v‖ := by
  filter_upwards [c.coercive, c.bounded] with x hc hb v
  exact norm_apply_le_of_symm (c.A x) (c.symm x)
    (fun w => (mul_nonneg c.lam_pos.le (sq_nonneg ‖w‖)).trans (hc w)) c.Λ_pos.le hb v

theorem aestronglyMeasurable_apply {ν : Measure F} {G : F → F} (hG : AEStronglyMeasurable G ν) :
    AEStronglyMeasurable (fun x => c.A x (G x)) ν :=
  (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).aestronglyMeasurable_comp₂
    c.stronglyMeasurable.aestronglyMeasurable hG

theorem memLp_apply (Ω : Set F) (G : Lp F 2 (μ.restrict Ω)) :
    MemLp (fun x => c.A x (G x)) 2 (μ.restrict Ω) := by
  refine MemLp.of_le ((Lp.memLp G).const_smul c.Λ)
    (c.aestronglyMeasurable_apply (Lp.aestronglyMeasurable G)) ?_
  filter_upwards [ae_restrict_of_ae c.ae_norm_apply_le] with x hx
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos c.Λ_pos]
  exact hx _

/-- **Multiplication by the coefficient field**, `G ↦ A G`, on `L²(Ω; F)`. -/
def mulOp (Ω : Set F) : Lp F 2 (μ.restrict Ω) →L[ℝ] Lp F 2 (μ.restrict Ω) :=
  LinearMap.mkContinuous
    { toFun := fun G => (c.memLp_apply Ω G).toLp _
      map_add' := fun G H => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [Lp.coeFn_add G H] with x hx
        rw [hx, Pi.add_apply, map_add, Pi.add_apply]
      map_smul' := fun r G => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [Lp.coeFn_smul r G] with x hx
        rw [hx, Pi.smul_apply, map_smul, Pi.smul_apply] }
    c.Λ fun G => by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [(c.memLp_apply Ω G).coeFn_toLp,
        ae_restrict_of_ae c.ae_norm_apply_le] with x h1 h2
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [h1]
      exact h2 _

theorem mulOp_ae (Ω : Set F) (G : Lp F 2 (μ.restrict Ω)) :
    c.mulOp Ω G =ᵐ[μ.restrict Ω] fun x => c.A x (G x) :=
  (c.memLp_apply Ω G).coeFn_toLp

theorem inner_mulOp (Ω : Set F) (G H : Lp F 2 (μ.restrict Ω)) :
    ⟪c.mulOp Ω G, H⟫_ℝ = ∫ x in Ω, ⟪c.A x (G x), H x⟫_ℝ ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [c.mulOp_ae Ω G] with x hx
  rw [hx]

theorem norm_sq_eq_integral (Ω : Set F) (G : Lp F 2 (μ.restrict Ω)) :
    ‖G‖ ^ 2 = ∫ x in Ω, ‖G x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (Eventually.of_forall fun x => real_inner_self_eq_norm_sq (G x))

/-- **Coercivity of `A` on `L²`:** `λ ‖G‖² ≤ ⟨A G, G⟩`. -/
theorem lam_mul_norm_sq_le (Ω : Set F) (G : Lp F 2 (μ.restrict Ω)) :
    c.lam * ‖G‖ ^ 2 ≤ ⟪c.mulOp Ω G, G⟫_ℝ := by
  rw [norm_sq_eq_integral, ← integral_const_mul, inner_mulOp]
  refine integral_mono_ae ?_ ?_ ?_
  · exact ((L2.integrable_inner G G).congr (Eventually.of_forall fun x =>
      real_inner_self_eq_norm_sq (G x))).const_mul _
  · exact (L2.integrable_inner (c.mulOp Ω G) G).congr (by
      filter_upwards [c.mulOp_ae Ω G] with x hx
      rw [hx])
  · filter_upwards [ae_restrict_of_ae c.coercive] with x hx
    exact hx _

/-! ### The Dirichlet form -/

theorem norm_snd_le {Ω : Set F} (v : L2Pair μ Ω) : ‖v.snd‖ ≤ ‖v‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 v
  have h0 := sq_nonneg ‖v.fst‖
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by linarith)

theorem norm_fst_le {Ω : Set F} (v : L2Pair μ Ω) : ‖v.fst‖ ≤ ‖v‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 v
  have h0 := sq_nonneg ‖v.snd‖
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by linarith)

/-- **The Dirichlet form** `((u, G), (v, H)) ↦ ∫_Ω ⟨A G, H⟩` on `L²(Ω) × L²(Ω; F)`. -/
def dirichletForm (Ω : Set F) : L2Pair μ Ω →L[ℝ] L2Pair μ Ω →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun v w : L2Pair μ Ω => ⟪c.mulOp Ω v.snd, w.snd⟫_ℝ)
      (fun v₁ v₂ w => by simp only [WithLp.add_snd, map_add, inner_add_left])
      (fun r v w => by simp only [WithLp.smul_snd, map_smul, real_inner_smul_left, smul_eq_mul])
      (fun v w₁ w₂ => by simp only [WithLp.add_snd, inner_add_right])
      (fun r v w => by simp only [WithLp.smul_snd, real_inner_smul_right, smul_eq_mul]))
    c.Λ fun v w => by
      simp only [LinearMap.mk₂_apply, Real.norm_eq_abs]
      calc |⟪c.mulOp Ω v.snd, w.snd⟫_ℝ| ≤ ‖c.mulOp Ω v.snd‖ * ‖w.snd‖ := abs_real_inner_le_norm _ _
        _ ≤ (c.Λ * ‖v.snd‖) * ‖w.snd‖ := by
            gcongr
            exact (c.mulOp Ω).le_of_opNorm_le (LinearMap.mkContinuous_norm_le _ c.Λ_pos.le _) _
        _ ≤ c.Λ * ‖v‖ * ‖w‖ := by
            have := c.Λ_pos
            gcongr
            · exact norm_snd_le v
            · exact norm_snd_le w

@[simp] theorem dirichletForm_apply (Ω : Set F) (v w : L2Pair μ Ω) :
    c.dirichletForm Ω v w = ⟪c.mulOp Ω v.snd, w.snd⟫_ℝ := rfl

variable [μ.IsAddHaarMeasure]

/-- The Dirichlet form against a test function: `∫_Ω ⟨A G, ∇φ⟩`. -/
theorem dirichletForm_graph {Ω : Set F} (v : L2Pair μ Ω) {φ : F → ℝ}
    (hφ : IsTestFn Ω φ) :
    c.dirichletForm Ω v (graph μ Ω hφ) = ∫ x in Ω, ⟪c.A x (v.snd x), gradient φ x⟫_ℝ ∂μ := by
  rw [dirichletForm_apply, inner_mulOp, graph_snd]
  refine integral_congr_ae ?_
  filter_upwards [(hφ.memLp_gradient (μ := μ) 2 Ω).coeFn_toLp] with x hx
  rw [hx]

/-! ### Weak solutions -/

/-- **Weak solution** of `-div(A ∇u) = f` on `Ω`: `v = (u, ∇u) ∈ W^{1,2}(Ω)` and
`∫_Ω ⟨A ∇u, ∇φ⟩ = ∫_Ω f φ` for every test function `φ` on `Ω`. -/
def IsWeakSolution {Ω : Set F} (f : Lp ℝ 2 (μ.restrict Ω)) (v : L2Pair μ Ω) : Prop :=
  v ∈ W12 μ Ω ∧ ∀ (φ : F → ℝ) (hφ : IsTestFn Ω φ),
    c.dirichletForm Ω v (graph μ Ω hφ) = ⟪f, (graph μ Ω hφ).fst⟫_ℝ

/-- The right-hand side against a test function: `∫_Ω f φ`. -/
theorem inner_graph_fst {Ω : Set F} (f : Lp ℝ 2 (μ.restrict Ω)) {φ : F → ℝ} (hφ : IsTestFn Ω φ) :
    ⟪f, (graph μ Ω hφ).fst⟫_ℝ = ∫ x in Ω, f x * φ x ∂μ := by
  rw [graph_fst, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(hφ.memLp (μ := μ) 2 Ω).coeFn_toLp] with x hx
  rw [hx]
  simp [mul_comm]

/-- The weak equation in integral form. -/
theorem isWeakSolution_iff {Ω : Set F} (f : Lp ℝ 2 (μ.restrict Ω)) (v : L2Pair μ Ω) :
    c.IsWeakSolution f v ↔ v ∈ W12 μ Ω ∧ ∀ (φ : F → ℝ) (_ : IsTestFn Ω φ),
      ∫ x in Ω, ⟪c.A x (v.snd x), gradient φ x⟫_ℝ ∂μ = ∫ x in Ω, f x * φ x ∂μ := by
  unfold IsWeakSolution
  refine and_congr_right fun _ => forall_congr' fun φ => forall_congr' fun hφ => ?_
  rw [dirichletForm_graph, inner_graph_fst]

/-- **Test pairs in `W^{1,2}_0(Ω)`.** A weak solution satisfies the weak equation against every
`ψ ∈ W^{1,2}_0(Ω)`, not only against test functions. -/
theorem IsWeakSolution.forall_H01 {c : CoeffField F μ} {Ω : Set F} {f : Lp ℝ 2 (μ.restrict Ω)}
    {v : L2Pair μ Ω} (hv : c.IsWeakSolution f v) {ψ : L2Pair μ Ω} (hψ : ψ ∈ H01 μ Ω) :
    c.dirichletForm Ω v ψ = ⟪f, ψ.fst⟫_ℝ := by
  have hfst : Continuous fun v : L2Pair μ Ω => v.fst :=
    continuous_fst.comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous
  have hclosed : IsClosed {ψ : L2Pair μ Ω | c.dirichletForm Ω v ψ = ⟪f, ψ.fst⟫_ℝ} :=
    isClosed_eq (c.dirichletForm Ω v).continuous (continuous_const.inner hfst)
  have hsub : (testSubmodule μ Ω Ω : Set (L2Pair μ Ω)) ⊆
      {ψ : L2Pair μ Ω | c.dirichletForm Ω v ψ = ⟪f, ψ.fst⟫_ℝ} := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact hv.2 φ hφ
  have hψ' : ψ ∈ closure (testSubmodule μ Ω Ω : Set (L2Pair μ Ω)) := by
    rwa [H01, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hψ
  exact closure_minimal hsub hclosed hψ'

/-- The restriction of the Dirichlet form to `W^{1,2}_0(Ω)`. -/
def dirichletForm₀ (Ω : Set F) : H01 μ Ω →L[ℝ] H01 μ Ω →L[ℝ] ℝ :=
  (c.dirichletForm Ω).bilinearComp (H01 μ Ω).subtypeL (H01 μ Ω).subtypeL

@[simp] theorem dirichletForm₀_apply (Ω : Set F) (u w : H01 μ Ω) :
    c.dirichletForm₀ Ω u w = c.dirichletForm Ω u w := rfl

/-- **Coercivity on `W^{1,2}_0(Ω)`** for bounded `Ω`, via Friedrichs–Poincaré:
`λ/(1 + 4R²) ‖v‖² ≤ ∫_Ω ⟨A ∇u, ∇u⟩`. -/
theorem isCoercive_dirichletForm₀ [Nontrivial F] {Ω : Set F} {x₀ : F} {R : ℝ} (hR : 0 ≤ R)
    (hΩ : Ω ⊆ Metric.closedBall x₀ R) : IsCoercive (c.dirichletForm₀ Ω) := by
  refine ⟨c.lam / (1 + 4 * R ^ 2), by have := c.lam_pos; positivity, fun u => ?_⟩
  have h1 := norm_sq_le_of_mem_H01 hR hΩ u.2
  have h2 := c.lam_mul_norm_sq_le Ω (u : L2Pair μ Ω).snd
  rw [dirichletForm₀_apply, dirichletForm_apply]
  have hpos : 0 < 1 + 4 * R ^ 2 := by positivity
  have hnorm : ‖u‖ = ‖(u : L2Pair μ Ω)‖ := rfl
  rw [hnorm]
  calc c.lam / (1 + 4 * R ^ 2) * ‖(u : L2Pair μ Ω)‖ * ‖(u : L2Pair μ Ω)‖
      = c.lam / (1 + 4 * R ^ 2) * ‖(u : L2Pair μ Ω)‖ ^ 2 := by ring
    _ ≤ c.lam / (1 + 4 * R ^ 2) * ((1 + 4 * R ^ 2) * ‖(u : L2Pair μ Ω).snd‖ ^ 2) := by
        have := c.lam_pos
        gcongr
    _ = c.lam * ‖(u : L2Pair μ Ω).snd‖ ^ 2 := by field_simp
    _ ≤ _ := h2

/-- **Existence and uniqueness of weak solutions** (Lax–Milgram). Let `Ω ⊆ B̄(x₀, R)`. For every
`f ∈ L²(Ω)` there is exactly one `v ∈ W^{1,2}_0(Ω)` with `-div(A ∇v) = f` weakly. -/
theorem existsUnique_H01_isWeakSolution [Nontrivial F] {Ω : Set F} {x₀ : F} {R : ℝ} (hR : 0 ≤ R)
    (hΩ : Ω ⊆ Metric.closedBall x₀ R) (f : Lp ℝ 2 (μ.restrict Ω)) :
    ∃! v : H01 μ Ω, c.IsWeakSolution f v := by
  have hcoer := c.isCoercive_dirichletForm₀ hR hΩ
  -- the functional `ψ ↦ ∫ f ψ` on `W^{1,2}_0(Ω)` and its Riesz representative
  let ℓ : StrongDual ℝ (H01 μ Ω) :=
    (innerSL ℝ f).comp ((WithLp.fstL 2 ℝ _ _).comp (H01 μ Ω).subtypeL)
  have hℓ : ∀ ψ : H01 μ Ω, ℓ ψ = ⟪f, (ψ : L2Pair μ Ω).fst⟫_ℝ := fun ψ => rfl
  let Fℓ : H01 μ Ω := (toDual ℝ (H01 μ Ω)).symm ℓ
  let v : H01 μ Ω := hcoer.continuousLinearEquivOfBilin.symm Fℓ
  have hv : ∀ ψ : H01 μ Ω, c.dirichletForm₀ Ω v ψ = ⟪f, (ψ : L2Pair μ Ω).fst⟫_ℝ := by
    intro ψ
    rw [← IsCoercive.continuousLinearEquivOfBilin_apply hcoer, ContinuousLinearEquiv.apply_symm_apply,
      toDual_symm_apply, hℓ]
  refine ⟨v, ⟨H01_le_W12 _ v.2, fun φ hφ => hv ⟨_, graph_mem_H01 Ω hφ⟩⟩, ?_⟩
  intro w hw
  have hw' : ∀ ψ : H01 μ Ω, c.dirichletForm₀ Ω w ψ = ⟪f, (ψ : L2Pair μ Ω).fst⟫_ℝ :=
    fun ψ => hw.forall_H01 ψ.2
  obtain ⟨C, hC, hcoer'⟩ := hcoer
  have hzero : c.dirichletForm₀ Ω (w - v) (w - v) = 0 := by
    rw [ContinuousLinearMap.map_sub₂, hw', hv, sub_self]
  have h1 := hcoer' (w - v)
  rw [hzero, mul_assoc] at h1
  have h2 : ‖w - v‖ * ‖w - v‖ ≤ 0 := by
    by_contra h
    linarith [mul_pos hC (not_le.mp h)]
  have hn : ‖w - v‖ = 0 := mul_self_eq_zero.mp (le_antisymm h2 (mul_self_nonneg _))
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end CoeffField

end ConicalKahler.Sobolev
