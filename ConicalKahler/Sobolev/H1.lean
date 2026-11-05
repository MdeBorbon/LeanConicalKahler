module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# `W^{1,2}(Ω)` and `W^{1,2}_0(Ω)` as Hilbert spaces

Let `F` be a finite-dimensional real inner product space with an additive Haar measure `μ`
(for us `F = ℝ^d` with Lebesgue measure; the paper's real coordinates). For `Ω ⊆ F` we work in the
Hilbert space

  `L2Pair μ Ω = L²(Ω) × L²(Ω; F)`

of pairs `(u, G)` of a function and a vector field, with the `L²` product norm
`‖(u, G)‖² = ‖u‖² + ‖G‖²`.

* `IsTestFn U φ`: `φ` is smooth with compact support in `U`.
* `graph μ Ω hφ = (φ, ∇φ)`; `testSubmodule μ Ω U` is the space of graphs of test functions
  supported in `U`.
* `H01 μ Ω`, **the Sobolev space `W^{1,2}_0(Ω)`**, is the closure of `testSubmodule μ Ω Ω`. It is a
  closed subspace of a Hilbert space, hence a Hilbert space.
* `W12 μ Ω`, **the Sobolev space `W^{1,2}(Ω)`**, is the closed subspace of pairs `(u, G)` such that
  `G` is the weak gradient of `u`: `∫ u ∂_w φ = -∫ ⟨G, w⟩ φ` for all test functions `φ` and all `w`
  (`IsWeakGradPair`). `H01_le_W12`: every element of `H01` is such a pair.
* **Friedrichs–Poincaré inequality** (`norm_fst_le_of_mem_H01`): if `Ω ⊆ B̄(0, R)`, then
  `‖u‖_{L²} ≤ 2R ‖G‖_{L²}` for `(u, G) ∈ H01 μ Ω`. For test functions it is proved by one
  integration by parts, `∫ φ² = -2 ∫ ⟨e, x⟩ φ ∂_e φ` for a unit vector `e`, and it passes to the
  closure.
-/

@[expose] public section

noncomputable section

-- The typeclass context is shared by many small lemmas; not every lemma uses all of it.
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff ENNReal

namespace ConicalKahler.Sobolev

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### Test functions -/

/-- `φ` is a **test function on `U`**: smooth, compactly supported, with `tsupport φ ⊆ U`. -/
structure IsTestFn (U : Set F) (φ : F → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ φ
  hasCompactSupport : HasCompactSupport φ
  tsupport_subset : tsupport φ ⊆ U

namespace IsTestFn

variable {U V : Set F} {φ ψ : F → ℝ}

theorem zero : IsTestFn U (0 : F → ℝ) :=
  ⟨contDiff_const, HasCompactSupport.zero, by simp⟩

theorem add (hφ : IsTestFn U φ) (hψ : IsTestFn U ψ) : IsTestFn U (φ + ψ) :=
  ⟨hφ.contDiff.add hψ.contDiff, hφ.hasCompactSupport.add hψ.hasCompactSupport,
    (tsupport_add φ ψ).trans (Set.union_subset hφ.tsupport_subset hψ.tsupport_subset)⟩

theorem const_smul (hφ : IsTestFn U φ) (c : ℝ) : IsTestFn U (c • φ) :=
  ⟨hφ.contDiff.const_smul c, hφ.hasCompactSupport.smul_left,
    (tsupport_smul_subset_right (fun _ => c) φ).trans hφ.tsupport_subset⟩

/-- Multiplying a test function by a smooth function gives a test function. -/
theorem smooth_mul (hφ : IsTestFn U φ) {η : F → ℝ} (hη : ContDiff ℝ ∞ η) :
    IsTestFn U (η * φ) :=
  ⟨hη.mul hφ.contDiff, hφ.hasCompactSupport.mul_left,
    (tsupport_mul_subset_right).trans hφ.tsupport_subset⟩

theorem mono (hφ : IsTestFn U φ) (h : U ⊆ V) : IsTestFn V φ :=
  ⟨hφ.contDiff, hφ.hasCompactSupport, hφ.tsupport_subset.trans h⟩

theorem continuous (hφ : IsTestFn U φ) : Continuous φ := hφ.contDiff.continuous

theorem differentiable (hφ : IsTestFn U φ) : Differentiable ℝ φ :=
  hφ.contDiff.differentiable (by simp)

theorem continuous_fderiv (hφ : IsTestFn U φ) : Continuous (fderiv ℝ φ) :=
  hφ.contDiff.continuous_fderiv (by simp)

theorem hasCompactSupport_fderiv (hφ : IsTestFn U φ) : HasCompactSupport (fderiv ℝ φ) :=
  hφ.hasCompactSupport.fderiv (𝕜 := ℝ)

theorem continuous_fderiv_apply (hφ : IsTestFn U φ) (w : F) :
    Continuous fun x => fderiv ℝ φ x w :=
  hφ.continuous_fderiv.clm_apply continuous_const

theorem hasCompactSupport_fderiv_apply (hφ : IsTestFn U φ) (w : F) :
    HasCompactSupport fun x => fderiv ℝ φ x w :=
  hφ.hasCompactSupport_fderiv.comp_left (g := fun L : F →L[ℝ] ℝ => L w) rfl

variable [FiniteDimensional ℝ F]

theorem continuous_gradient (hφ : IsTestFn U φ) : Continuous (gradient φ) :=
  (toDual ℝ F).symm.continuous.comp hφ.continuous_fderiv

theorem hasCompactSupport_gradient (hφ : IsTestFn U φ) : HasCompactSupport (gradient φ) :=
  hφ.hasCompactSupport_fderiv.comp_left (g := (toDual ℝ F).symm) (map_zero _)

end IsTestFn

variable [FiniteDimensional ℝ F]

theorem inner_gradient (φ : F → ℝ) (x w : F) : ⟪gradient φ x, w⟫_ℝ = fderiv ℝ φ x w :=
  toDual_symm_apply

theorem gradient_add {φ ψ : F → ℝ} (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) (x : F) :
    gradient (φ + ψ) x = gradient φ x + gradient ψ x := by
  simp only [gradient, fderiv_add (hφ x) (hψ x), map_add]

theorem gradient_const_smul {φ : F → ℝ} (hφ : Differentiable ℝ φ) (c : ℝ) (x : F) :
    gradient (c • φ) x = c • gradient φ x := by
  simp only [gradient, fderiv_const_smul (hφ x) c, map_smul]

theorem gradient_zero (x : F) : gradient (0 : F → ℝ) x = 0 := by
  unfold gradient
  simp

variable [MeasurableSpace F] [BorelSpace F]

/-! ### `L²` facts -/

section L2

variable {ν : Measure F}

theorem inner_toLp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f g : F → E}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ x, ⟪f x, g x⟫_ℝ ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

theorem inner_toLp_real {f g : F → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ x, f x * g x ∂ν := by
  rw [inner_toLp]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [mul_comm]

theorem norm_toLp_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : F → E}
    (hf : MemLp f 2 ν) : ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp]
  exact integral_congr_ae (Eventually.of_forall fun x => real_inner_self_eq_norm_sq (f x))

end L2

/-! ### The Hilbert space of pairs and the graphs of test functions -/

/-- `L²(Ω) × L²(Ω; F)`, the Hilbert space of pairs (function, vector field). -/
abbrev L2Pair (μ : Measure F) (Ω : Set F) : Type _ :=
  WithLp 2 (Lp ℝ 2 (μ.restrict Ω) × Lp F 2 (μ.restrict Ω))

variable (μ : Measure F) [μ.IsAddHaarMeasure]

/-- Extensionality for pairs. -/
theorem L2Pair.ext {Ω : Set F} {v w : L2Pair μ Ω} (h₁ : v.fst = w.fst) (h₂ : v.snd = w.snd) :
    v = w :=
  WithLp.ofLp_injective _ (Prod.ext h₁ h₂)

namespace IsTestFn

variable {μ} {U : Set F} {φ : F → ℝ}

theorem memLp (hφ : IsTestFn U φ) (p : ℝ≥0∞) (Ω : Set F) : MemLp φ p (μ.restrict Ω) :=
  (hφ.continuous.memLp_of_hasCompactSupport (μ := μ) hφ.hasCompactSupport).restrict Ω

theorem memLp_gradient (hφ : IsTestFn U φ) (p : ℝ≥0∞) (Ω : Set F) :
    MemLp (gradient φ) p (μ.restrict Ω) :=
  (hφ.continuous_gradient.memLp_of_hasCompactSupport (μ := μ)
    hφ.hasCompactSupport_gradient).restrict Ω

theorem memLp_fderiv_apply (hφ : IsTestFn U φ) (w : F) (p : ℝ≥0∞) (Ω : Set F) :
    MemLp (fun x => fderiv ℝ φ x w) p (μ.restrict Ω) :=
  ((hφ.continuous_fderiv_apply w).memLp_of_hasCompactSupport (μ := μ)
    (hφ.hasCompactSupport_fderiv_apply w)).restrict Ω

theorem memLp_smul_vec (hφ : IsTestFn U φ) (w : F) (p : ℝ≥0∞) (Ω : Set F) :
    MemLp (fun x => φ x • w) p (μ.restrict Ω) :=
  ((hφ.continuous.smul continuous_const).memLp_of_hasCompactSupport (μ := μ)
    (hφ.hasCompactSupport.smul_right)).restrict Ω

end IsTestFn

/-- The **graph** `(φ, ∇φ)` of a test function in `L²(Ω) × L²(Ω; F)`. -/
def graph (Ω : Set F) {U : Set F} {φ : F → ℝ} (hφ : IsTestFn U φ) : L2Pair μ Ω :=
  WithLp.toLp 2 ((hφ.memLp (μ := μ) 2 Ω).toLp φ, (hφ.memLp_gradient (μ := μ) 2 Ω).toLp (gradient φ))

variable {μ}

@[simp] theorem graph_fst (Ω : Set F) {U : Set F} {φ : F → ℝ} (hφ : IsTestFn U φ) :
    (graph μ Ω hφ).fst = (hφ.memLp (μ := μ) 2 Ω).toLp φ := rfl

@[simp] theorem graph_snd (Ω : Set F) {U : Set F} {φ : F → ℝ} (hφ : IsTestFn U φ) :
    (graph μ Ω hφ).snd = (hφ.memLp_gradient (μ := μ) 2 Ω).toLp (gradient φ) := rfl

theorem graph_zero (Ω U : Set F) : graph μ Ω (IsTestFn.zero (U := U)) = 0 := by
  have h0 : MemLp (0 : F → ℝ) 2 (μ.restrict Ω) := MemLp.zero
  have h0' : MemLp (0 : F → F) 2 (μ.restrict Ω) := MemLp.zero
  refine L2Pair.ext μ ?_ ?_
  · rw [graph_fst, WithLp.zero_fst]
    exact MemLp.toLp_zero h0
  · rw [graph_snd, WithLp.zero_snd]
    calc _ = h0'.toLp (0 : F → F) := MemLp.toLp_congr _ _ (Eventually.of_forall gradient_zero)
      _ = 0 := MemLp.toLp_zero h0'

theorem graph_add (Ω : Set F) {U : Set F} {φ ψ : F → ℝ} (hφ : IsTestFn U φ) (hψ : IsTestFn U ψ) :
    graph μ Ω (hφ.add hψ) = graph μ Ω hφ + graph μ Ω hψ := by
  refine L2Pair.ext μ ?_ ?_
  · rw [WithLp.add_fst, graph_fst, graph_fst, graph_fst, ← MemLp.toLp_add]
  · rw [WithLp.add_snd, graph_snd, graph_snd, graph_snd, ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _
      (Eventually.of_forall (gradient_add hφ.differentiable hψ.differentiable))

theorem graph_const_smul (Ω : Set F) {U : Set F} {φ : F → ℝ} (hφ : IsTestFn U φ) (c : ℝ) :
    graph μ Ω (hφ.const_smul c) = c • graph μ Ω hφ := by
  refine L2Pair.ext μ ?_ ?_
  · rw [WithLp.smul_fst, graph_fst, graph_fst, ← MemLp.toLp_const_smul]
  · rw [WithLp.smul_snd, graph_snd, graph_snd, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _
      (Eventually.of_forall (gradient_const_smul hφ.differentiable c))

variable (μ) in
/-- The graphs of test functions supported in `U`, as a subspace of `L²(Ω) × L²(Ω; F)`. -/
def testSubmodule (Ω U : Set F) : Submodule ℝ (L2Pair μ Ω) where
  carrier := {v | ∃ φ : F → ℝ, ∃ hφ : IsTestFn U φ, graph μ Ω hφ = v}
  zero_mem' := ⟨0, IsTestFn.zero, graph_zero Ω U⟩
  add_mem' := by
    rintro _ _ ⟨φ, hφ, rfl⟩ ⟨ψ, hψ, rfl⟩
    exact ⟨φ + ψ, hφ.add hψ, graph_add Ω hφ hψ⟩
  smul_mem' := by
    rintro c _ ⟨φ, hφ, rfl⟩
    exact ⟨c • φ, hφ.const_smul c, graph_const_smul Ω hφ c⟩

theorem graph_mem_testSubmodule (Ω : Set F) {U : Set F} {φ : F → ℝ} (hφ : IsTestFn U φ) :
    graph μ Ω hφ ∈ testSubmodule μ Ω U :=
  ⟨φ, hφ, rfl⟩

theorem testSubmodule_mono (Ω : Set F) {U V : Set F} (h : U ⊆ V) :
    testSubmodule μ Ω U ≤ testSubmodule μ Ω V := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact ⟨φ, hφ.mono h, rfl⟩

variable (μ) in
/-- **The Sobolev space `W^{1,2}_0(Ω)`**: the closure of the graphs of test functions on `Ω`. -/
def H01 (Ω : Set F) : Submodule ℝ (L2Pair μ Ω) :=
  (testSubmodule μ Ω Ω).topologicalClosure

theorem graph_mem_H01 (Ω : Set F) {φ : F → ℝ} (hφ : IsTestFn Ω φ) : graph μ Ω hφ ∈ H01 μ Ω :=
  Submodule.le_topologicalClosure _ (graph_mem_testSubmodule Ω hφ)

theorem isClosed_H01 (Ω : Set F) : IsClosed (H01 μ Ω : Set (L2Pair μ Ω)) :=
  Submodule.isClosed_topologicalClosure _

instance (Ω : Set F) : CompleteSpace (H01 μ Ω) :=
  (isClosed_H01 Ω).completeSpace_coe

/-! ### Weak gradients and `W^{1,2}(Ω)` -/

/-- `v = (u, G)` with `G` the **weak gradient** of `u` on `Ω`:
`∫_Ω u ∂_w φ = -∫_Ω ⟨G, w⟩ φ` for every test function `φ` on `Ω` and every vector `w`. -/
def IsWeakGradPair {Ω : Set F} (v : L2Pair μ Ω) : Prop :=
  ∀ (φ : F → ℝ) (hφ : IsTestFn Ω φ) (w : F),
    ⟪v.fst, (hφ.memLp_fderiv_apply (μ := μ) w 2 Ω).toLp _⟫_ℝ =
      -⟪v.snd, (hφ.memLp_smul_vec (μ := μ) w 2 Ω).toLp _⟫_ℝ

variable (μ) in
/-- **The Sobolev space `W^{1,2}(Ω)`**: pairs `(u, G)` in `L²(Ω) × L²(Ω; F)` such that `G` is the
weak gradient of `u`. -/
def W12 (Ω : Set F) : Submodule ℝ (L2Pair μ Ω) where
  carrier := {v | IsWeakGradPair v}
  zero_mem' := fun φ hφ w => by simp
  add_mem' := by
    intro v₁ v₂ h₁ h₂ φ hφ w
    simp only [WithLp.add_fst, WithLp.add_snd, inner_add_left, h₁ φ hφ w, h₂ φ hφ w, neg_add]
  smul_mem' := by
    intro c v h φ hφ w
    simp only [WithLp.smul_fst, WithLp.smul_snd, real_inner_smul_left, h φ hφ w, mul_neg]

theorem mem_W12 {Ω : Set F} {v : L2Pair μ Ω} : v ∈ W12 μ Ω ↔ IsWeakGradPair v := Iff.rfl

theorem isClosed_W12 (Ω : Set F) : IsClosed (W12 μ Ω : Set (L2Pair μ Ω)) := by
  have : (W12 μ Ω : Set (L2Pair μ Ω)) = ⋂ (φ : F → ℝ) (hφ : IsTestFn Ω φ) (w : F),
      {v : L2Pair μ Ω | ⟪v.fst, (hφ.memLp_fderiv_apply (μ := μ) w 2 Ω).toLp _⟫_ℝ =
        -⟪v.snd, (hφ.memLp_smul_vec (μ := μ) w 2 Ω).toLp _⟫_ℝ} := by
    ext v
    simp [mem_W12, IsWeakGradPair]
  rw [this]
  refine isClosed_iInter fun φ => isClosed_iInter fun hφ => isClosed_iInter fun w => ?_
  exact isClosed_eq
    ((continuous_fst.comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous).inner
      continuous_const)
    ((continuous_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous).inner
      continuous_const).neg

/-- Integration by parts for test functions over `Ω`: `∫_Ω ψ ∂_w φ = -∫_Ω (∂_w ψ) φ`. -/
theorem integral_mul_fderiv_eq_neg {Ω : Set F} {φ ψ : F → ℝ} (hφ : IsTestFn Ω φ)
    (hψ : IsTestFn Ω ψ) (w : F) :
    ∫ x in Ω, ψ x * fderiv ℝ φ x w ∂μ = -∫ x in Ω, fderiv ℝ ψ x w * φ x ∂μ := by
  have hzero1 : ∀ x ∉ Ω, ψ x * fderiv ℝ φ x w = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hψ.tsupport_subset h)), zero_mul]
  have hzero2 : ∀ x ∉ Ω, fderiv ℝ ψ x w * φ x = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.tsupport_subset h)), mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero1,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero2]
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun x _ => hψ.differentiable x) (fun x _ => hφ.differentiable x)
  · exact ((hψ.continuous_fderiv_apply w).mul hφ.continuous).integrable_of_hasCompactSupport
      hφ.hasCompactSupport.mul_left
  · exact (hψ.continuous.mul (hφ.continuous_fderiv_apply w)).integrable_of_hasCompactSupport
      hψ.hasCompactSupport.mul_right
  · exact (hψ.continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      hψ.hasCompactSupport.mul_right

/-- Graphs of test functions are in `W^{1,2}(Ω)`. -/
theorem graph_mem_W12 (Ω : Set F) {ψ : F → ℝ} (hψ : IsTestFn Ω ψ) : graph μ Ω hψ ∈ W12 μ Ω := by
  intro φ hφ w
  rw [graph_fst, graph_snd, inner_toLp_real, inner_toLp, integral_mul_fderiv_eq_neg hφ hψ w]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [inner_smul_right, inner_gradient]
  ring

theorem testSubmodule_le_W12 (Ω : Set F) : testSubmodule μ Ω Ω ≤ W12 μ Ω := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact graph_mem_W12 Ω hφ

/-- **`W^{1,2}_0(Ω) ⊆ W^{1,2}(Ω)`**: every element of `H01` is a pair `(u, ∇u)`. -/
theorem H01_le_W12 (Ω : Set F) : H01 μ Ω ≤ W12 μ Ω :=
  Submodule.topologicalClosure_minimal _ (testSubmodule_le_W12 Ω) (isClosed_W12 Ω)

/-! ### The Friedrichs–Poincaré inequality -/

/-- Cauchy–Schwarz in `L²`: `∫ |f| ‖G‖ ≤ ‖f‖_{L²} ‖G‖_{L²}`. -/
theorem integral_abs_mul_norm_le {ν : Measure F} {f : F → ℝ} {G : F → F} (hf : MemLp f 2 ν)
    (hG : MemLp G 2 ν) : ∫ x, |f x| * ‖G x‖ ∂ν ≤ ‖hf.toLp f‖ * ‖hG.toLp G‖ := by
  have hf' := hf.norm
  have hG' := hG.norm
  have h1 : ‖hf'.toLp (fun x => ‖f x‖)‖ = ‖hf.toLp f‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm]
    exact hf.aestronglyMeasurable
  have h2 : ‖hG'.toLp (fun x => ‖G x‖)‖ = ‖hG.toLp G‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm]
    exact hG.aestronglyMeasurable
  calc ∫ x, |f x| * ‖G x‖ ∂ν = ⟪hf'.toLp _, hG'.toLp _⟫_ℝ := by
        rw [inner_toLp_real]
        rfl
    _ ≤ ‖hf'.toLp (fun x => ‖f x‖)‖ * ‖hG'.toLp (fun x => ‖G x‖)‖ := real_inner_le_norm _ _
    _ = _ := by rw [h1, h2]

theorem norm_graph_fst_sq (Ω : Set F) {U : Set F} {φ : F → ℝ} (hφ : IsTestFn U φ) :
    ‖(graph μ Ω hφ).fst‖ ^ 2 = ∫ x in Ω, φ x ^ 2 ∂μ := by
  rw [graph_fst, norm_toLp_sq]
  simp

theorem norm_graph_snd_sq (Ω : Set F) {U : Set F} {φ : F → ℝ} (hφ : IsTestFn U φ) :
    ‖(graph μ Ω hφ).snd‖ ^ 2 = ∫ x in Ω, ‖gradient φ x‖ ^ 2 ∂μ := by
  rw [graph_snd, norm_toLp_sq]

/-- **Friedrichs inequality for test functions.** If `Ω ⊆ B̄(0, R)`, then
`‖φ‖_{L²(Ω)} ≤ 2R ‖∇φ‖_{L²(Ω)}`. Proof: for a unit vector `e`, integration by parts gives
`∫ φ² = -2 ∫ ⟨e, x⟩ φ ∂_e φ`, and `|⟨e, x⟩| ≤ R` on the support. -/
theorem norm_graph_fst_le [Nontrivial F] {Ω : Set F} {R : ℝ} (hR : 0 ≤ R)
    (hΩ : Ω ⊆ Metric.closedBall 0 R) {φ : F → ℝ} (hφ : IsTestFn Ω φ) :
    ‖(graph μ Ω hφ).fst‖ ≤ 2 * R * ‖(graph μ Ω hφ).snd‖ := by
  obtain ⟨e, he⟩ := exists_norm_eq F zero_le_one
  set ℓ : F →L[ℝ] ℝ := innerSL ℝ e
  set a := ‖(graph μ Ω hφ).fst‖ with ha_def
  set b := ‖(graph μ Ω hφ).snd‖ with hb_def
  have hout : ∀ x ∉ Ω, φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hφ.tsupport_subset h)
  have hdφ : ∀ x, HasFDerivAt φ (fderiv ℝ φ x) x := fun x => (hφ.differentiable x).hasFDerivAt
  have hsq : ∀ x, fderiv ℝ (fun y => φ y * φ y) x e = 2 * (φ x * fderiv ℝ φ x e) := fun x => by
    rw [show (fun y => φ y * φ y) = φ * φ from rfl, ((hdφ x).mul (hdφ x)).fderiv]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  have hℓ : ∀ x, fderiv ℝ ℓ x e = 1 := fun x => by
    rw [ContinuousLinearMap.fderiv]
    simp [ℓ, he]
  have hcs : HasCompactSupport fun x => φ x * fderiv ℝ φ x e := hφ.hasCompactSupport.mul_right
  have hcont : Continuous fun x => φ x * fderiv ℝ φ x e :=
    hφ.continuous.mul (hφ.continuous_fderiv_apply e)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ) (f := ℓ)
    (g := fun y => φ y * φ y) (v := e) ?_ ?_ ?_ (fun x _ => ℓ.differentiableAt)
    (fun x _ => ((hdφ x).mul (hdφ x)).differentiableAt)
  rotate_left
  · simp only [hℓ, one_mul]
    exact (hφ.continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      hφ.hasCompactSupport.mul_right
  · simp only [hsq]
    exact (ℓ.continuous.mul (continuous_const.mul hcont)).integrable_of_hasCompactSupport
      (hcs.mul_left.mul_left)
  · exact (ℓ.continuous.mul (hφ.continuous.mul hφ.continuous)).integrable_of_hasCompactSupport
      hφ.hasCompactSupport.mul_right.mul_left
  simp only [hsq, hℓ, one_mul] at hibp
  -- pointwise bound
  have hpt : ∀ x, -(ℓ x * (2 * (φ x * fderiv ℝ φ x e))) ≤ 2 * R * (|φ x| * ‖gradient φ x‖) := by
    intro x
    by_cases hx : φ x = 0
    · simp [hx]
    have hxΩ : x ∈ Ω := by
      by_contra h
      exact hx (hout x h)
    have hxR : ‖x‖ ≤ R := by simpa using hΩ hxΩ
    have hℓx : |ℓ x| ≤ R := by
      calc |ℓ x| = |⟪e, x⟫_ℝ| := rfl
        _ ≤ ‖e‖ * ‖x‖ := abs_real_inner_le_norm e x
        _ ≤ R := by rw [he, one_mul]; exact hxR
    have hde : |fderiv ℝ φ x e| ≤ ‖gradient φ x‖ := by
      rw [← inner_gradient]
      calc |⟪gradient φ x, e⟫_ℝ| ≤ ‖gradient φ x‖ * ‖e‖ := abs_real_inner_le_norm _ _
        _ = ‖gradient φ x‖ := by rw [he, mul_one]
    calc -(ℓ x * (2 * (φ x * fderiv ℝ φ x e)))
        ≤ |ℓ x * (2 * (φ x * fderiv ℝ φ x e))| := neg_le_abs _
      _ = 2 * (|ℓ x| * (|φ x| * |fderiv ℝ φ x e|)) := by
          rw [abs_mul, abs_mul, abs_mul, abs_two]
          ring
      _ ≤ 2 * (R * (|φ x| * ‖gradient φ x‖)) := by
          gcongr
      _ = 2 * R * (|φ x| * ‖gradient φ x‖) := by ring
  have hint_rhs : Integrable (fun x => 2 * R * (|φ x| * ‖gradient φ x‖)) μ :=
    (continuous_const.mul (hφ.continuous.abs.mul hφ.continuous_gradient.norm)).integrable_of_hasCompactSupport
      (hφ.hasCompactSupport.abs.mul_right.mul_left)
  have hint_lhs : Integrable (fun x => -(ℓ x * (2 * (φ x * fderiv ℝ φ x e)))) μ :=
    ((ℓ.continuous.mul (continuous_const.mul hcont)).integrable_of_hasCompactSupport
      (hcs.mul_left.mul_left)).neg
  have hmain : ∫ x, φ x * φ x ∂μ ≤ ∫ x, 2 * R * (|φ x| * ‖gradient φ x‖) ∂μ := by
    rw [show ∫ x, φ x * φ x ∂μ = ∫ x, -(ℓ x * (2 * (φ x * fderiv ℝ φ x e))) ∂μ by
      rw [integral_neg, hibp, neg_neg]]
    exact integral_mono hint_lhs hint_rhs hpt
  -- back to integrals over `Ω`
  have hΩ1 : ∫ x in Ω, φ x ^ 2 ∂μ = ∫ x, φ x * φ x ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hout x hx])]
    simp [sq]
  have hΩ2 : ∫ x in Ω, |φ x| * ‖gradient φ x‖ ∂μ = ∫ x, |φ x| * ‖gradient φ x‖ ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hout x hx])
  have hCS := integral_abs_mul_norm_le (hφ.memLp (μ := μ) 2 Ω) (hφ.memLp_gradient (μ := μ) 2 Ω)
  have ha2 : a ^ 2 ≤ 2 * R * (a * b) := by
    rw [ha_def, norm_graph_fst_sq, hΩ1]
    calc ∫ x, φ x * φ x ∂μ ≤ ∫ x, 2 * R * (|φ x| * ‖gradient φ x‖) ∂μ := hmain
      _ = 2 * R * ∫ x in Ω, |φ x| * ‖gradient φ x‖ ∂μ := by rw [integral_const_mul, hΩ2]
      _ ≤ 2 * R * (a * b) := by gcongr; exact hCS
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  rcases ha.eq_or_lt with h | h
  · rw [← h]
    positivity
  · nlinarith

/-- **Friedrichs–Poincaré inequality on `W^{1,2}_0(Ω)`.** If `Ω ⊆ B̄(0, R)`, then
`‖u‖_{L²(Ω)} ≤ 2R ‖G‖_{L²(Ω)}` for every `(u, G) ∈ H01 μ Ω`. -/
theorem norm_fst_le_of_mem_H01 [Nontrivial F] {Ω : Set F} {R : ℝ} (hR : 0 ≤ R)
    (hΩ : Ω ⊆ Metric.closedBall 0 R) {v : L2Pair μ Ω} (hv : v ∈ H01 μ Ω) :
    ‖v.fst‖ ≤ 2 * R * ‖v.snd‖ := by
  have hfst : Continuous fun v : L2Pair μ Ω => v.fst :=
    continuous_fst.comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous
  have hsnd : Continuous fun v : L2Pair μ Ω => v.snd :=
    continuous_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous
  have hclosed : IsClosed {v : L2Pair μ Ω | ‖v.fst‖ ≤ 2 * R * ‖v.snd‖} :=
    isClosed_le hfst.norm (continuous_const.mul hsnd.norm)
  have hsub : (testSubmodule μ Ω Ω : Set (L2Pair μ Ω)) ⊆
      {v : L2Pair μ Ω | ‖v.fst‖ ≤ 2 * R * ‖v.snd‖} := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact norm_graph_fst_le hR hΩ hφ
  have hv' : v ∈ closure (testSubmodule μ Ω Ω : Set (L2Pair μ Ω)) := by
    rwa [H01, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hv
  exact closure_minimal hsub hclosed hv'

/-- The norm of a pair: `‖(u, G)‖² = ‖u‖² + ‖G‖²`. -/
theorem norm_sq_L2Pair {Ω : Set F} (v : L2Pair μ Ω) : ‖v‖ ^ 2 = ‖v.fst‖ ^ 2 + ‖v.snd‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 v

/-- On `W^{1,2}_0(Ω)` the gradient controls the full norm:
`‖(u, G)‖² ≤ (1 + 4R²) ‖G‖²`. -/
theorem norm_sq_le_of_mem_H01 [Nontrivial F] {Ω : Set F} {R : ℝ} (hR : 0 ≤ R)
    (hΩ : Ω ⊆ Metric.closedBall 0 R) {v : L2Pair μ Ω} (hv : v ∈ H01 μ Ω) :
    ‖v‖ ^ 2 ≤ (1 + 4 * R ^ 2) * ‖v.snd‖ ^ 2 := by
  have h := norm_fst_le_of_mem_H01 hR hΩ hv
  have h0 := norm_nonneg v.fst
  rw [norm_sq_L2Pair]
  nlinarith [mul_self_le_mul_self h0 h]

end ConicalKahler.Sobolev
