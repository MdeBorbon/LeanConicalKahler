module

public import ConicalKahler.Sobolev.Elliptic
public import CalabiYau.Analysis.Sobolev.Euclidean.W1p.Approximation

/-!
# Cut-offs in `W^{1,2}_0` and the Caccioppoli inequality

From here on the space is `ℝ^d = EuclideanSpace ℝ (Fin d)` with Lebesgue measure, as in the paper's
real coordinates. That is where the upstream Sobolev library (`Sobolev.Euclidean`) works.

* `cutPair hv hη`: for `v = (u, G) ∈ W^{1,2}(Ω)` and a test function `η` on `Ω`, the pair
  `(η² u, η² G + 2 η u ∇η)`. `cutPair_mem_H01`: it lies in `W^{1,2}_0(Ω)`. The proof shows that
  `η² u ∈ W^{1,p}(Ω)` in the upstream sense, with this weak gradient, and that it has compact support
  in `Ω`. Upstream's mollification lemma `memW01p_of_memW1p_of_tsupport_subset` then provides smooth
  approximations, whose graphs converge to the pair.
* **Caccioppoli inequality** (`caccioppoli`): if `-div(A ∇u) = f` weakly on `Ω` and `η` is a test
  function on `Ω`, then

    `∫_Ω η² ⟨A ∇u, ∇u⟩ ≤ ∫_Ω η² f² + ∫_Ω (η² + 4Λ |∇η|²) u²`.

  This is the paper's Lemma 2.3, for general bounded measurable coefficients (`A = g⁻¹` for the
  cone).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff ENNReal

namespace ConicalKahler.Sobolev

variable {d : ℕ}

/-! ### `L²` products -/

section L2

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
  {ν : Measure F}

theorem integrable_mul_of_memLp_two {f g : F → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    Integrable (fun x => f x * g x) ν := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

/-- Multiplying an `L²` function by a bounded continuous function stays in `L²`. -/
theorem memLp_two_mul_bounded {f : F → ℝ} {η : F → ℝ} (hf : MemLp f 2 ν) (hη : Continuous η)
    {M : ℝ} (hM : ∀ x, ‖η x‖ ≤ M) [OpensMeasurableSpace F] : MemLp (fun x => η x * f x) 2 ν :=
  hf.of_le_mul (hη.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))

end L2

/-! ### The cut-off pair -/

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

variable [NeZero d]

open Sobolev.Euclidean in
/-- The weak-gradient identity of `v ∈ W^{1,2}(Ω)` in integral form. -/
theorem integral_fst_mul_fderiv {Ω : Set 𝔼} {v : L2Pair volume Ω} (hv : v ∈ W12 volume Ω)
    {φ : 𝔼 → ℝ} (hφ : IsTestFn Ω φ) (w : 𝔼) :
    ∫ x in Ω, v.fst x * fderiv ℝ φ x w = -∫ x in Ω, φ x * ⟪v.snd x, w⟫_ℝ := by
  have h := hv φ hφ w
  rw [L2.inner_def, L2.inner_def] at h
  have h1 : ∫ x in Ω, ⟪v.fst x, ((hφ.memLp_fderiv_apply (μ := volume) w 2 Ω).toLp
      (fun x => fderiv ℝ φ x w)) x⟫_ℝ = ∫ x in Ω, v.fst x * fderiv ℝ φ x w := by
    refine integral_congr_ae ?_
    filter_upwards [(hφ.memLp_fderiv_apply (μ := volume) w 2 Ω).coeFn_toLp] with x hx
    rw [hx]
    simp [mul_comm]
  have h2 : ∫ x in Ω, ⟪v.snd x, ((hφ.memLp_smul_vec (μ := volume) w 2 Ω).toLp
      (fun x => φ x • w)) x⟫_ℝ = ∫ x in Ω, φ x * ⟪v.snd x, w⟫_ℝ := by
    refine integral_congr_ae ?_
    filter_upwards [(hφ.memLp_smul_vec (μ := volume) w 2 Ω).coeFn_toLp] with x hx
    rw [hx, real_inner_smul_right]
  rw [h1, h2] at h
  exact h

section Cut

/-- `η² u`. -/
def cutFst {Ω : Set 𝔼} (v : L2Pair volume Ω) (η : 𝔼 → ℝ) (x : 𝔼) : ℝ := η x ^ 2 * v.fst x

/-- `η² G + 2 η u ∇η`, the gradient of `η² u`. -/
def cutSnd {Ω : Set 𝔼} (v : L2Pair volume Ω) (η : 𝔼 → ℝ) (x : 𝔼) : 𝔼 :=
  η x ^ 2 • v.snd x + (2 * η x * v.fst x) • gradient η x

theorem exists_bound_testFn {U : Set 𝔼} {η : 𝔼 → ℝ} (hη : IsTestFn U η) :
    ∃ M, 0 ≤ M ∧ (∀ x, |η x| ≤ M) ∧ ∀ x, ‖gradient η x‖ ≤ M := by
  obtain ⟨M₁, hM₁⟩ := hη.continuous.bounded_above_of_compact_support hη.hasCompactSupport
  obtain ⟨M₂, hM₂⟩ := hη.continuous_gradient.bounded_above_of_compact_support
    hη.hasCompactSupport_gradient
  refine ⟨max (max M₁ M₂) 0, le_max_right _ _, fun x => ?_, fun x => ?_⟩
  · exact (hM₁ x).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hM₂ x).trans ((le_max_right _ _).trans (le_max_left _ _))

theorem memLp_cutFst {Ω : Set 𝔼} {v : L2Pair volume Ω} {η : 𝔼 → ℝ} (hη : IsTestFn Ω η) : MemLp (cutFst v η) 2 (volume.restrict Ω) := by
  obtain ⟨M, -, hM, -⟩ := exists_bound_testFn hη
  refine memLp_two_mul_bounded (Lp.memLp v.fst) (hη.continuous.pow 2) (M := M ^ 2) fun x => ?_
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2

theorem memLp_cutSnd {Ω : Set 𝔼} {v : L2Pair volume Ω} {η : 𝔼 → ℝ} (hη : IsTestFn Ω η) : MemLp (cutSnd v η) 2 (volume.restrict Ω) := by
  obtain ⟨M, hM0, hM, hM'⟩ := exists_bound_testFn hη
  have h1 : MemLp (fun x => η x ^ 2 • v.snd x) 2 (volume.restrict Ω) := by
    refine (Lp.memLp v.snd).of_le_mul (c := M ^ 2)
      ((hη.continuous.pow 2).aestronglyMeasurable.smul (Lp.aestronglyMeasurable v.snd))
      (Eventually.of_forall fun x => ?_)
    rw [norm_smul, norm_pow, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hM x) 2) (norm_nonneg _)
  have h2 : MemLp (fun x => (2 * η x * v.fst x) • gradient η x) 2 (volume.restrict Ω) := by
    refine (Lp.memLp v.fst).of_le_mul (c := 2 * M * M)
      (((continuous_const.mul hη.continuous).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable v.fst)).smul hη.continuous_gradient.aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [norm_smul, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_two]
    calc 2 * |η x| * |v.fst x| * ‖gradient η x‖ ≤ 2 * M * |v.fst x| * M := by
          gcongr
          · exact hM x
          · exact hM' x
      _ = 2 * M * M * |v.fst x| := by ring
  exact h1.add h2

/-- **The cut-off pair** `(η² u, η² G + 2 η u ∇η)`. -/
def cutPair {Ω : Set 𝔼} {η : 𝔼 → ℝ} (hη : IsTestFn Ω η) (v : L2Pair volume Ω) : L2Pair volume Ω :=
  WithLp.toLp 2 ((memLp_cutFst (v := v) hη).toLp _, (memLp_cutSnd (v := v) hη).toLp _)

theorem cutPair_fst {Ω : Set 𝔼} {η : 𝔼 → ℝ} (hη : IsTestFn Ω η) (v : L2Pair volume Ω) :
    (cutPair hη v).fst = (memLp_cutFst (v := v) hη).toLp _ := rfl

theorem cutPair_snd {Ω : Set 𝔼} {η : 𝔼 → ℝ} (hη : IsTestFn Ω η) (v : L2Pair volume Ω) :
    (cutPair hη v).snd = (memLp_cutSnd (v := v) hη).toLp _ := rfl

theorem gradient_apply_single (φ : 𝔼 → ℝ) (x : 𝔼) (i : Fin d) :
    gradient φ x i = fderiv ℝ φ x (EuclideanSpace.single i 1) := by
  rw [← inner_gradient, EuclideanSpace.inner_single_right]
  simp

theorem snd_apply_eq_inner (G : 𝔼) (i : Fin d) : G i = ⟪G, EuclideanSpace.single i 1⟫_ℝ := by
  rw [EuclideanSpace.inner_single_right]
  simp

theorem norm_le_sum_abs (X : 𝔼) : ‖X‖ ≤ ∑ i, |X i| := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ i, ‖X i‖ ^ 2) ≤ √((∑ i, |X i|) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        simpa [Real.norm_eq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
          (f := fun i => |X i|) (fun i _ => abs_nonneg _)
    _ = ∑ i, |X i| := Real.sqrt_sq (Finset.sum_nonneg fun i _ => abs_nonneg _)

theorem norm_le_norm_fst_add_norm_snd {Ω : Set 𝔼} (w : L2Pair volume Ω) :
    ‖w‖ ≤ ‖w.fst‖ + ‖w.snd‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 w
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [h]
  nlinarith [norm_nonneg w.fst, norm_nonneg w.snd]

open Sobolev.Euclidean in
/-- `η² u` has the weak partial derivatives `(η² G + 2 η u ∇η)_i` on `Ω`. -/
theorem hasWeakPartialDeriv_cutFst {Ω : Set 𝔼} {v : L2Pair volume Ω} {η : 𝔼 → ℝ}
    (hv : v ∈ W12 volume Ω) (hη : IsTestFn Ω η) (i : Fin d) :
    HasWeakPartialDeriv i (fun x => cutSnd v η x i) (cutFst v η) Ω := by
  intro φ hφs hφc hφΩ
  have hφ : IsTestFn Ω φ := ⟨hφs, hφc, hφΩ⟩
  have hψ : IsTestFn Ω (fun x => η x ^ 2 * φ x) := hφ.smooth_mul (hη.contDiff.pow 2)
  have hdψ : ∀ x, fderiv ℝ (fun x => η x ^ 2 * φ x) x (EuclideanSpace.single i 1) =
      η x ^ 2 * fderiv ℝ φ x (EuclideanSpace.single i 1) +
        φ x * (2 * η x * fderiv ℝ η x (EuclideanSpace.single i 1)) := by
    intro x
    have h2 := ((hη.differentiable x).hasFDerivAt).pow 2
    have hφx := (hφ.differentiable x).hasFDerivAt
    rw [show (fun x => η x ^ 2 * φ x) = (fun x => η x ^ 2) * φ from rfl, (h2.mul hφx).fderiv]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, nsmul_eq_mul]
    norm_num
  have hW := integral_fst_mul_fderiv hv hψ (EuclideanSpace.single i 1)
  have hu := Lp.memLp v.fst
  have hGe : MemLp (fun x => ⟪v.snd x, EuclideanSpace.single i 1⟫_ℝ) 2 (volume.restrict Ω) := by
    refine (Lp.memLp v.snd).of_le_mul (c := 1) ?_ (Eventually.of_forall fun x => ?_)
    · exact (Lp.aestronglyMeasurable v.snd).inner aestronglyMeasurable_const
    · rw [Real.norm_eq_abs, one_mul]
      calc |⟪v.snd x, EuclideanSpace.single i 1⟫_ℝ|
          ≤ ‖v.snd x‖ * ‖(EuclideanSpace.single i 1 : 𝔼)‖ := abs_real_inner_le_norm _ _
        _ = ‖v.snd x‖ := by simp
  have hK : MemLp (fun x => 2 * η x * fderiv ℝ η x (EuclideanSpace.single i 1) * φ x) 2
      (volume.restrict Ω) := by
    refine (Continuous.memLp_of_hasCompactSupport (μ := volume) ?_ ?_).restrict Ω
    · exact ((continuous_const.mul hη.continuous).mul
        (hη.continuous_fderiv_apply _)).mul hφ.continuous
    · exact hφ.hasCompactSupport.mul_left
  have I1 := integrable_mul_of_memLp_two hu (hψ.memLp_fderiv_apply (μ := volume)
    (EuclideanSpace.single i 1) 2 Ω)
  have I2 := integrable_mul_of_memLp_two hu hK
  have I3 := integrable_mul_of_memLp_two (hψ.memLp (μ := volume) 2 Ω) hGe
  have hLHS : ∫ x in Ω, cutFst v η x * fderiv ℝ φ x (EuclideanSpace.single i 1) =
      (∫ x in Ω, v.fst x * fderiv ℝ (fun x => η x ^ 2 * φ x) x (EuclideanSpace.single i 1)) -
        ∫ x in Ω, v.fst x * (2 * η x * fderiv ℝ η x (EuclideanSpace.single i 1) * φ x) := by
    rw [← integral_sub I1 I2]
    congr 1
    funext x
    rw [hdψ]
    simp only [cutFst]
    ring
  have hRHS : ∫ x in Ω, cutSnd v η x i * φ x =
      (∫ x in Ω, (η x ^ 2 * φ x) * ⟪v.snd x, EuclideanSpace.single i 1⟫_ℝ) +
        ∫ x in Ω, v.fst x * (2 * η x * fderiv ℝ η x (EuclideanSpace.single i 1) * φ x) := by
    rw [← integral_add I3 I2]
    congr 1
    funext x
    simp only [cutSnd, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [gradient_apply_single, snd_apply_eq_inner (v.snd x) i]
    ring
  show ∫ x in Ω, cutFst v η x * fderiv ℝ φ x (EuclideanSpace.single i 1) =
    -∫ x in Ω, cutSnd v η x i * φ x
  rw [hLHS, hRHS, hW]
  ring

open Sobolev.Euclidean in
/-- **Cut-offs of `W^{1,2}(Ω)` functions are in `W^{1,2}_0(Ω)`.** For `v = (u, G) ∈ W^{1,2}(Ω)`
and a test function `η` on `Ω` (open), `(η² u, η² G + 2 η u ∇η) ∈ W^{1,2}_0(Ω)`. The smooth
approximations come from upstream's `memW01p_of_memW1p_of_tsupport_subset`. -/
theorem cutPair_mem_H01 {Ω : Set 𝔼} (hΩ : IsOpen Ω) {v : L2Pair volume Ω} {η : 𝔼 → ℝ}
    (hv : v ∈ W12 volume Ω) (hη : IsTestFn Ω η) : cutPair hη v ∈ H01 volume Ω := by
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  set ν := volume.restrict Ω
  have hcomp : ∀ i, MemLp (fun x => cutSnd v η x i) 2 ν := fun i =>
    (memLp_cutSnd (v := v) hη).of_le_mul (c := 1)
      (((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).comp_aestronglyMeasurable
        (memLp_cutSnd (v := v) hη).aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [one_mul]
        exact PiLp.norm_apply_le _ i)
  have hmem : MemW1p (ENNReal.ofReal 2) (cutFst v η) Ω := by
    rw [h2]
    exact ⟨memLp_cutFst hη, fun i => ⟨fun x => cutSnd v η x i, hcomp i,
      hasWeakPartialDeriv_cutFst hv hη i⟩⟩
  have hη2 : HasCompactSupport (fun x => η x ^ 2) :=
    hη.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hcs : HasCompactSupport (cutFst v η) := hη2.mul_right
  have hsub : tsupport (cutFst v η) ⊆ Ω :=
    (tsupport_mul_subset_left).trans ((tsupport_comp_subset (g := fun t : ℝ => t ^ 2)
      (by norm_num) η).trans hη.tsupport_subset)
  obtain ⟨-, hw, φs, hsmooth, hcpt, hsupp, hconv, hgrad⟩ :=
    memW01p_of_memW1p_of_tsupport_subset hΩ (by norm_num : (1 : ℝ) < 2) hmem hcs hsub
  simp only [h2] at hconv hgrad
  have htest : ∀ n, IsTestFn Ω (φs n) := fun n => ⟨hsmooth n, hcpt n, hsupp n⟩
  -- the upstream weak gradient is ours, almost everywhere
  have hae : ∀ i, (fun x => hw.weakGrad x i) =ᵐ[ν] fun x => cutSnd v η x i := fun i =>
    HasWeakPartialDeriv.ae_eq hΩ (hw.isWeakGrad i) (hasWeakPartialDeriv_cutFst hv hη i)
      ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
      ((hcomp i).locallyIntegrable (by norm_num))
  have haeall : ∀ᵐ x ∂ν, ∀ i, hw.weakGrad x i = cutSnd v η x i := ae_all_iff.mpr hae
  -- convergence of the first components
  have hfst : Tendsto (fun n => ‖(graph volume Ω (htest n)).fst - (cutPair hη v).fst‖) atTop
      (𝓝 0) := by
    have heq : ∀ n, ‖(graph volume Ω (htest n)).fst - (cutPair hη v).fst‖ =
        (eLpNorm (fun x => φs n x - cutFst v η x) 2 ν).toReal := fun n => by
      rw [graph_fst, cutPair_fst, ← MemLp.toLp_sub, Lp.norm_toLp]
      rfl
    simp_rw [heq]
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
    rw [ENNReal.toReal_zero] at h
    exact h
  -- convergence of the second components
  have hcompw : ∀ i, MemLp (fun x => hw.weakGrad x i) 2 ν := fun i => by
    simpa [h2] using hw.weakGrad_component_memLp i
  have hdiff : ∀ n i, MemLp (fun x => fderiv ℝ (φs n) x (EuclideanSpace.single i 1) -
      hw.weakGrad x i) 2 ν := fun n i =>
    ((htest n).memLp_fderiv_apply (μ := volume) _ 2 Ω).sub (hcompw i)
  have hbound : ∀ n, ‖(graph volume Ω (htest n)).snd - (cutPair hη v).snd‖ ≤
      (∑ i, eLpNorm (fun x => fderiv ℝ (φs n) x (EuclideanSpace.single i 1) - hw.weakGrad x i)
        2 ν).toReal := fun n => by
    rw [graph_snd, cutPair_snd, ← MemLp.toLp_sub, Lp.norm_toLp]
    refine ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun i _ => (hdiff n i).eLpNorm_ne_top) ?_
    calc eLpNorm (gradient (φs n) - cutSnd v η) 2 ν
        ≤ eLpNorm (fun x => ∑ i, |fderiv ℝ (φs n) x (EuclideanSpace.single i 1) -
            hw.weakGrad x i|) 2 ν := by
          refine eLpNorm_mono_ae_real
            (((htest n).memLp_gradient (μ := volume) 2 Ω).sub
              (memLp_cutSnd (v := v) hη)).aestronglyMeasurable ?_
          filter_upwards [haeall] with x hx
          refine (norm_le_sum_abs _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
          rw [Pi.sub_apply, PiLp.sub_apply, gradient_apply_single, hx i]
      _ = eLpNorm (∑ i, fun x => |fderiv ℝ (φs n) x (EuclideanSpace.single i 1) -
            hw.weakGrad x i|) 2 ν := by
          congr 1
          funext x
          simp [Finset.sum_apply]
      _ ≤ ∑ i, eLpNorm (fun x => |fderiv ℝ (φs n) x (EuclideanSpace.single i 1) -
            hw.weakGrad x i|) 2 ν := eLpNorm_sum_le (by norm_num)
      _ = ∑ i, eLpNorm (fun x => fderiv ℝ (φs n) x (EuclideanSpace.single i 1) -
            hw.weakGrad x i) 2 ν := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp_rw [← Real.norm_eq_abs]
          exact eLpNorm_norm _ (hdiff n i).aestronglyMeasurable
  have hsnd : Tendsto (fun n => ‖(graph volume Ω (htest n)).snd - (cutPair hη v).snd‖) atTop
      (𝓝 0) := by
    refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ => hgrad i
    rw [Finset.sum_const_zero] at hsum
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsum
    rw [ENNReal.toReal_zero] at h
    exact h
  have hlim : Tendsto (fun n => graph volume Ω (htest n)) atTop (𝓝 (cutPair hη v)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsum2 := hfst.add hsnd
    rw [add_zero] at hsum2
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsum2
    exact (norm_le_norm_fst_add_norm_snd _).trans_eq (by rw [WithLp.sub_fst, WithLp.sub_snd])
  have hcl : cutPair hη v ∈ closure (testSubmodule volume Ω Ω : Set (L2Pair volume Ω)) :=
    mem_closure_of_tendsto hlim (Eventually.of_forall fun n => graph_mem_testSubmodule Ω _)
  rwa [H01, ← SetLike.mem_coe, Submodule.topologicalClosure_coe]

end Cut

/-! ### The Caccioppoli inequality -/

/-- **Caccioppoli inequality** (paper, Lemma 2.3, for any bounded measurable coefficients).
If `v = (u, ∇u)` solves `-div(A ∇u) = f` weakly on the open set `Ω` and `η` is a test function on
`Ω`, then
`∫_Ω η² ⟨A ∇u, ∇u⟩ ≤ ∫_Ω η² f² + ∫_Ω (η² + 4Λ |∇η|²) u²`. -/
theorem caccioppoli (c : CoeffField 𝔼 volume) {Ω : Set 𝔼} (hΩ : IsOpen Ω)
    {f : Lp ℝ 2 (volume.restrict Ω)} {v : L2Pair volume Ω} (hv : c.IsWeakSolution f v)
    {η : 𝔼 → ℝ} (hη : IsTestFn Ω η) :
    ∫ x in Ω, η x ^ 2 * ⟪c.A x (v.snd x), v.snd x⟫_ℝ ≤
      (∫ x in Ω, η x ^ 2 * f x ^ 2) +
        ∫ x in Ω, (η x ^ 2 + 4 * c.Λ * ‖gradient η x‖ ^ 2) * v.fst x ^ 2 := by
  obtain ⟨M, hM0, hMη, hMg⟩ := exists_bound_testFn hη
  have hΛ := c.Λ_pos
  have hu := Lp.memLp v.fst
  have hG := Lp.memLp v.snd
  have hf := Lp.memLp f
  have hGm := Lp.aestronglyMeasurable v.snd
  have hAGm := c.aestronglyMeasurable_apply (ν := volume.restrict Ω) hGm
  have hηc := hη.continuous
  have hgc := hη.continuous_gradient
  -- the weak equation tested with the cut-off pair
  have key := hv.forall_H01 (cutPair_mem_H01 hΩ hv.1 hη)
  rw [CoeffField.dirichletForm_apply, CoeffField.inner_mulOp, cutPair_snd, cutPair_fst, L2.inner_def] at key
  let a : 𝔼 → ℝ := fun x => η x ^ 2 * ⟪c.A x (v.snd x), v.snd x⟫_ℝ
  let b : 𝔼 → ℝ := fun x => 2 * η x * v.fst x * ⟪c.A x (v.snd x), gradient η x⟫_ℝ
  let r : 𝔼 → ℝ := fun x => f x * (η x ^ 2 * v.fst x)
  have e1 : ∫ x in Ω, ⟪c.A x (v.snd x), (memLp_cutSnd (v := v) hη).toLp (cutSnd v η) x⟫_ℝ =
      ∫ x in Ω, (a x + b x) := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_cutSnd (v := v) hη).coeFn_toLp] with x hx
    rw [hx]
    simp only [a, b, cutSnd, inner_add_right, real_inner_smul_right]
  have e2 : ∫ x in Ω, ⟪f x, (memLp_cutFst (v := v) hη).toLp (cutFst v η) x⟫_ℝ =
      ∫ x in Ω, r x := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_cutFst (v := v) hη).coeFn_toLp] with x hx
    rw [hx]
    simp only [r, cutFst, RCLike.inner_apply', conj_trivial]
  have hkey : ∫ x in Ω, (a x + b x) = ∫ x in Ω, r x := e1.symm.trans (key.trans e2)
  have hη2 : ∀ x, η x ^ 2 ≤ M ^ 2 := fun x => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hMη x) 2
  have hg2 : ∀ x, ‖gradient η x‖ ^ 2 ≤ M ^ 2 := fun x =>
    pow_le_pow_left₀ (norm_nonneg _) (hMg x) 2
  have hG2 : Integrable (fun x => ‖v.snd x‖ ^ 2) (volume.restrict Ω) := hG.norm.integrable_sq
  have Ia : Integrable a (volume.restrict Ω) := by
    refine Integrable.mono' (hG2.const_mul (M ^ 2 * c.Λ)) ((hηc.pow 2).aestronglyMeasurable.mul
      (hAGm.inner hGm)) ?_
    filter_upwards [ae_restrict_of_ae c.ae_norm_apply_le] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have h1 : |⟪c.A x (v.snd x), v.snd x⟫_ℝ| ≤ c.Λ * ‖v.snd x‖ ^ 2 :=
      (abs_real_inner_le_norm _ _).trans (by nlinarith [hx (v.snd x), norm_nonneg (v.snd x)])
    calc |η x| ^ 2 * |⟪c.A x (v.snd x), v.snd x⟫_ℝ| ≤ M ^ 2 * (c.Λ * ‖v.snd x‖ ^ 2) := by
          gcongr
          exact hMη x
      _ = M ^ 2 * c.Λ * ‖v.snd x‖ ^ 2 := by ring
  have Iuy : Integrable (fun x => |v.fst x| * ‖v.snd x‖) (volume.restrict Ω) :=
    integrable_mul_of_memLp_two hu.abs hG.norm
  have Ib : Integrable b (volume.restrict Ω) := by
    refine Integrable.mono' (Iuy.const_mul (2 * M * c.Λ * M))
      ((((continuous_const.mul hηc).aestronglyMeasurable.mul hu.aestronglyMeasurable)).mul
        (hAGm.inner hgc.aestronglyMeasurable)) ?_
    filter_upwards [ae_restrict_of_ae c.ae_norm_apply_le] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_two]
    have h1 : |⟪c.A x (v.snd x), gradient η x⟫_ℝ| ≤ c.Λ * ‖v.snd x‖ * M :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul (hx _) (hMg x) (norm_nonneg _) (by positivity))
    calc 2 * |η x| * |v.fst x| * |⟪c.A x (v.snd x), gradient η x⟫_ℝ|
        ≤ 2 * M * |v.fst x| * (c.Λ * ‖v.snd x‖ * M) := by
          gcongr
          exact hMη x
      _ = 2 * M * c.Λ * M * (|v.fst x| * ‖v.snd x‖) := by ring
  have Ifu : Integrable (fun x => |f x| * |v.fst x|) (volume.restrict Ω) := integrable_mul_of_memLp_two hf.abs hu.abs
  have Ir : Integrable r (volume.restrict Ω) := by
    refine Integrable.mono' (Ifu.const_mul (M ^ 2))
      (hf.aestronglyMeasurable.mul ((hηc.pow 2).aestronglyMeasurable.mul hu.aestronglyMeasurable))
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    calc |f x| * (|η x| ^ 2 * |v.fst x|) ≤ |f x| * (M ^ 2 * |v.fst x|) := by
          gcongr
          exact hMη x
      _ = M ^ 2 * (|f x| * |v.fst x|) := by ring
  have If2 : Integrable (fun x => η x ^ 2 * f x ^ 2) (volume.restrict Ω) := by
    refine Integrable.mono' (hf.integrable_sq.const_mul (M ^ 2))
      ((hηc.pow 2).aestronglyMeasurable.mul (hf.aestronglyMeasurable.pow 2))
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (hη2 x) (sq_nonneg _)
  have Iu2 : Integrable (fun x => η x ^ 2 * v.fst x ^ 2) (volume.restrict Ω) := by
    refine Integrable.mono' (hu.integrable_sq.const_mul (M ^ 2))
      ((hηc.pow 2).aestronglyMeasurable.mul (hu.aestronglyMeasurable.pow 2))
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (hη2 x) (sq_nonneg _)
  have Ig2 : Integrable (fun x => ‖gradient η x‖ ^ 2 * v.fst x ^ 2) (volume.restrict Ω) := by
    refine Integrable.mono' (hu.integrable_sq.const_mul (M ^ 2))
      ((hgc.norm.pow 2).aestronglyMeasurable.mul (hu.aestronglyMeasurable.pow 2))
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (hg2 x) (sq_nonneg _)
  -- the pointwise inequality
  have hpt : ∀ᵐ x ∂(volume.restrict Ω), r x - b x ≤ (1 / 2) * (η x ^ 2 * f x ^ 2) + (1 / 2) * (η x ^ 2 * v.fst x ^ 2)
      + (1 / 2) * a x + 2 * c.Λ * (‖gradient η x‖ ^ 2 * v.fst x ^ 2) := by
    filter_upwards [ae_restrict_of_ae c.coercive, ae_restrict_of_ae c.bounded] with x hc hb
    have hpos : ∀ w, 0 ≤ ⟪c.A x w, w⟫_ℝ := fun w =>
      (mul_nonneg c.lam_pos.le (sq_nonneg ‖w‖)).trans (hc w)
    have hcs := inner_sq_le_of_symm (c.A x) (c.symm x) hpos (v.snd x) (gradient η x)
    have hbη := hb (gradient η x)
    have hGG := hpos (v.snd x)
    have hP : 0 ≤ (1 / 2) * a x := by
      simp only [a]
      exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) hGG)
    have hQ : 0 ≤ 2 * c.Λ * (‖gradient η x‖ ^ 2 * v.fst x ^ 2) := by positivity
    have hb2 : (b x) ^ 2 ≤ 4 * ((1 / 2) * a x) * (2 * c.Λ * (‖gradient η x‖ ^ 2 * v.fst x ^ 2)) := by
      simp only [a, b]
      have h1 : ⟪c.A x (v.snd x), gradient η x⟫_ℝ ^ 2 ≤
          ⟪c.A x (v.snd x), v.snd x⟫_ℝ * (c.Λ * ‖gradient η x‖ ^ 2) :=
        hcs.trans (mul_le_mul_of_nonneg_left hbη hGG)
      calc (2 * η x * v.fst x * ⟪c.A x (v.snd x), gradient η x⟫_ℝ) ^ 2
          = 4 * η x ^ 2 * v.fst x ^ 2 * ⟪c.A x (v.snd x), gradient η x⟫_ℝ ^ 2 := by ring
        _ ≤ 4 * η x ^ 2 * v.fst x ^ 2 *
            (⟪c.A x (v.snd x), v.snd x⟫_ℝ * (c.Λ * ‖gradient η x‖ ^ 2)) := by
            gcongr
        _ = 4 * (1 / 2 * (η x ^ 2 * ⟪c.A x (v.snd x), v.snd x⟫_ℝ)) *
            (2 * c.Λ * (‖gradient η x‖ ^ 2 * v.fst x ^ 2)) := by ring
    have hbPQ : -b x ≤ (1 / 2) * a x + 2 * c.Λ * (‖gradient η x‖ ^ 2 * v.fst x ^ 2) := by
      nlinarith [sq_nonneg ((1 / 2) * a x - 2 * c.Λ * (‖gradient η x‖ ^ 2 * v.fst x ^ 2)),
        sq_nonneg (b x)]
    have hr : r x ≤ (1 / 2) * (η x ^ 2 * f x ^ 2) + (1 / 2) * (η x ^ 2 * v.fst x ^ 2) := by
      simp only [r]
      nlinarith [mul_nonneg (sq_nonneg (η x)) (sq_nonneg (f x - v.fst x))]
    linarith
  -- integrate
  have hab : ∫ x in Ω, a x = (∫ x in Ω, r x) - ∫ x in Ω, b x := by
    rw [← hkey, integral_add Ia Ib]
    ring
  have J1 : Integrable (fun x => (1 / 2) * (η x ^ 2 * f x ^ 2) +
      (1 / 2) * (η x ^ 2 * v.fst x ^ 2)) (volume.restrict Ω) :=
    (If2.const_mul _).add (Iu2.const_mul _)
  have J2 : Integrable (fun x => (1 / 2) * (η x ^ 2 * f x ^ 2) +
      (1 / 2) * (η x ^ 2 * v.fst x ^ 2) + (1 / 2) * a x) (volume.restrict Ω) :=
    J1.add (Ia.const_mul _)
  have J3 : Integrable (fun x => (1 / 2) * (η x ^ 2 * f x ^ 2) +
      (1 / 2) * (η x ^ 2 * v.fst x ^ 2) + (1 / 2) * a x +
        2 * c.Λ * (‖gradient η x‖ ^ 2 * v.fst x ^ 2)) (volume.restrict Ω) :=
    J2.add (Ig2.const_mul _)
  have hmono : ∫ x in Ω, (r x - b x) ≤ ∫ x in Ω, ((1 / 2) * (η x ^ 2 * f x ^ 2) +
      (1 / 2) * (η x ^ 2 * v.fst x ^ 2) + (1 / 2) * a x +
        2 * c.Λ * (‖gradient η x‖ ^ 2 * v.fst x ^ 2)) :=
    integral_mono_ae (Ir.sub Ib) J3 hpt
  rw [integral_sub Ir Ib, integral_add J2 (Ig2.const_mul _), integral_add J1 (Ia.const_mul _),
    integral_add (If2.const_mul _) (Iu2.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, ← hab] at hmono
  have hsplit : ∫ x in Ω, (η x ^ 2 + 4 * c.Λ * ‖gradient η x‖ ^ 2) * v.fst x ^ 2 =
      (∫ x in Ω, η x ^ 2 * v.fst x ^ 2) + 4 * c.Λ * ∫ x in Ω, ‖gradient η x‖ ^ 2 * v.fst x ^ 2 := by
    rw [← integral_const_mul, ← integral_add Iu2 (Ig2.const_mul _)]
    congr 1
    funext x
    ring
  rw [hsplit]
  linarith

end ConicalKahler.Sobolev
