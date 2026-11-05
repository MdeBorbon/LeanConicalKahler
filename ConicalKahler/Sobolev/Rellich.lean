module

public import ConicalKahler.Sobolev.Caccioppoli
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Rellich.Basic

/-!
# Rellich compactness for `W^{1,2}_0(Ω)`

We reuse upstream's Rellich–Kondrachov theorem `Sobolev.rellich_kondrachov_W01p_seq`, which is
stated for functions with upstream's `W^{1,p}_0` membership `Sobolev.Euclidean.MemW01p`
(approximation by smooth compactly supported functions in function and gradient `L^p` norms).

## Compatibility

* `hasWeakPartialDeriv_of_mem_W12`: for `(u, G) ∈ W^{1,2}(Ω)` (our `W12`), the components `G_i`
  are upstream weak partial derivatives of `u`.
* `memW01p_of_mem_H01`: every `(u, G) ∈ W^{1,2}_0(Ω)` (our `H01`, the closure of graphs of test
  functions) gives `u ∈ MemW01p 2 Ω`, with weak gradient `G`.
* `ae_eq_snd_of_witness`: upstream weak gradients of `u` agree with `G` almost everywhere, so the
  norm bounds transfer.

## Results

* `rellich_H01`: on a bounded open `Ω ⊆ ℝ^d`, every bounded sequence in `W^{1,2}_0(Ω)` has a
  subsequence whose first components converge in `L²(Ω)`.
* `isCompactOperator_H01_fst`: the embedding `W^{1,2}_0(Ω) → L²(Ω)`, `(u, G) ↦ u`, is a compact
  operator.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set
open scoped ContDiff ENNReal

namespace ConicalKahler.Sobolev

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

variable [NeZero d]

open Sobolev.Euclidean

theorem memLp_snd_apply {Ω : Set 𝔼} (v : L2Pair volume Ω) (i : Fin d) :
    MemLp (fun x => v.snd x i) 2 (volume.restrict Ω) :=
  (Lp.memLp v.snd).of_le_mul (c := 1)
    (((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable v.snd))
    (Eventually.of_forall fun x => by
      rw [one_mul]
      exact PiLp.norm_apply_le _ i)

/-- **Our weak gradients are upstream weak partial derivatives.** -/
theorem hasWeakPartialDeriv_of_mem_W12 {Ω : Set 𝔼} {v : L2Pair volume Ω}
    (hv : v ∈ W12 volume Ω) (i : Fin d) :
    HasWeakPartialDeriv i (fun x => v.snd x i) (v.fst : 𝔼 → ℝ) Ω := by
  intro φ hφs hφc hφΩ
  rw [integral_fst_mul_fderiv hv ⟨hφs, hφc, hφΩ⟩ (EuclideanSpace.single i 1)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [← snd_apply_eq_inner]
  ring

/-- `W^{1,2}(Ω)` in upstream's sense. -/
theorem memW1p_of_mem_W12 {Ω : Set 𝔼} {v : L2Pair volume Ω} (hv : v ∈ W12 volume Ω) :
    MemW1p 2 (v.fst : 𝔼 → ℝ) Ω :=
  ⟨Lp.memLp v.fst, fun i => ⟨_, memLp_snd_apply v i, hasWeakPartialDeriv_of_mem_W12 hv i⟩⟩

/-- The upstream witness of `(u, G) ∈ W^{1,2}(Ω)` with weak gradient `G`. -/
def witnessOfMemW12 {Ω : Set 𝔼} {v : L2Pair volume Ω} (hv : v ∈ W12 volume Ω) :
    MemW1pWitness 2 (v.fst : 𝔼 → ℝ) Ω where
  memLp := Lp.memLp v.fst
  weakGrad := fun x => v.snd x
  weakGrad_component_memLp := memLp_snd_apply v
  isWeakGrad := hasWeakPartialDeriv_of_mem_W12 hv

/-- **Upstream weak gradients agree with ours** almost everywhere on `Ω`. -/
theorem ae_eq_snd_of_witness {Ω : Set 𝔼} (hΩ : IsOpen Ω) {v : L2Pair volume Ω}
    (hv : v ∈ W12 volume Ω) (hw : MemW1pWitness 2 (v.fst : 𝔼 → ℝ) Ω) (i : Fin d) :
    (fun x => hw.weakGrad x i) =ᵐ[volume.restrict Ω] fun x => v.snd x i :=
  HasWeakPartialDeriv.ae_eq hΩ (hw.isWeakGrad i) (hasWeakPartialDeriv_of_mem_W12 hv i)
    ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    ((memLp_snd_apply v i).locallyIntegrable (by norm_num))

theorem eLpNorm_eq_ofReal_norm {E : Type*} [NormedAddCommGroup E] {ν : Measure 𝔼}
    (f : Lp E 2 ν) : eLpNorm f 2 ν = ENNReal.ofReal ‖f‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]

/-- **`W^{1,2}_0(Ω)` in our sense is `W^{1,2}_0(Ω)` in upstream's sense.** -/
theorem memW01p_of_mem_H01 {Ω : Set 𝔼} {v : L2Pair volume Ω} (hv : v ∈ H01 volume Ω) :
    MemW01p 2 (v.fst : 𝔼 → ℝ) Ω := by
  have hv12 := H01_le_W12 Ω hv
  refine ⟨memW1p_of_mem_W12 hv12, witnessOfMemW12 hv12, ?_⟩
  have hcl : v ∈ closure (testSubmodule volume Ω Ω : Set (L2Pair volume Ω)) := by
    rwa [H01, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hv
  obtain ⟨vs, hvs_mem, hvs_lim⟩ := mem_closure_iff_seq_limit.mp hcl
  choose φ hφ hgraph using hvs_mem
  have hlim0 : Tendsto (fun n => ‖graph volume Ω (hφ n) - v‖) atTop (𝓝 0) := by
    simp_rw [hgraph]
    exact tendsto_iff_norm_sub_tendsto_zero.mp hvs_lim
  have hfst : Tendsto (fun n => ‖(graph volume Ω (hφ n)).fst - v.fst‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _)
      (fun n => by
        have h := CoeffField.norm_fst_le (graph volume Ω (hφ n) - v)
        rwa [WithLp.sub_fst] at h)
      hlim0
  have hsnd : Tendsto (fun n => ‖(graph volume Ω (hφ n)).snd - v.snd‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _)
      (fun n => by
        have h := CoeffField.norm_snd_le (graph volume Ω (hφ n) - v)
        rwa [WithLp.sub_snd] at h)
      hlim0
  refine ⟨φ, fun n => (hφ n).contDiff, fun n => (hφ n).hasCompactSupport,
    fun n => (hφ n).tsupport_subset, ?_, fun i => ?_⟩
  · have heq : ∀ n, eLpNorm (fun x => φ n x - v.fst x) 2 (volume.restrict Ω) =
        ENNReal.ofReal ‖(graph volume Ω (hφ n)).fst - v.fst‖ := fun n => by
      rw [← eLpNorm_eq_ofReal_norm]
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (graph volume Ω (hφ n)).fst v.fst,
        ((hφ n).memLp (μ := volume) 2 Ω).coeFn_toLp] with x h1 h2
      rw [h1, Pi.sub_apply, graph_fst, h2]
    simp_rw [heq]
    simpa using ENNReal.tendsto_ofReal hfst
  · have hle : ∀ n, eLpNorm (fun x => fderiv ℝ (φ n) x (EuclideanSpace.single i 1) -
        (witnessOfMemW12 hv12).weakGrad x i) 2 (volume.restrict Ω) ≤
        ENNReal.ofReal ‖(graph volume Ω (hφ n)).snd - v.snd‖ := fun n => by
      rw [← eLpNorm_eq_ofReal_norm]
      refine eLpNorm_mono_ae (((hφ n).memLp_fderiv_apply (μ := volume) _ 2 Ω).sub
        ((witnessOfMemW12 hv12).weakGrad_component_memLp i)).aestronglyMeasurable ?_
      filter_upwards [Lp.coeFn_sub (graph volume Ω (hφ n)).snd v.snd,
        ((hφ n).memLp_gradient (μ := volume) 2 Ω).coeFn_toLp] with x h1 h2
      rw [h1, Pi.sub_apply, graph_snd, h2, ← gradient_apply_single]
      exact PiLp.norm_apply_le (gradient (φ n) x - v.snd x) i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le)
      hle
    simpa using ENNReal.tendsto_ofReal hsnd

/-- **Rellich compactness on `W^{1,2}_0(Ω)`.** On a bounded open `Ω ⊆ ℝ^d`, every bounded
sequence in `W^{1,2}_0(Ω)` has a subsequence whose first components converge in `L²(Ω)`. -/
theorem rellich_H01 {Ω : Set 𝔼} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {v : ℕ → L2Pair volume Ω} (hv : ∀ n, v n ∈ H01 volume Ω) {M : ℝ} (hM : ∀ n, ‖v n‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : Lp ℝ 2 (volume.restrict Ω),
      Tendsto (fun k => (v (φ k)).fst) atTop (𝓝 g) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hmem := fun n => memW01p_of_mem_H01 (hv n)
  have hfun : ∀ n, eLpNorm ((v n).fst : 𝔼 → ℝ) 2 (volume.restrict Ω) ≤
      ENNReal.ofReal ((d + 1) * M) := fun n => by
    rw [eLpNorm_eq_ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((CoeffField.norm_fst_le (v n)).trans ((hM n).trans ?_))
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hgrad : ∀ n, ∑ i : Fin d, eLpNorm (fun x => (Classical.choose (hmem n).2).weakGrad x i)
      2 (volume.restrict Ω) ≤ ENNReal.ofReal ((d + 1) * M) := fun n => by
    have hi : ∀ i, eLpNorm (fun x => (Classical.choose (hmem n).2).weakGrad x i) 2
        (volume.restrict Ω) ≤ ENNReal.ofReal M := fun i => by
      rw [eLpNorm_congr_ae (ae_eq_snd_of_witness hΩ (H01_le_W12 Ω (hv n)) _ i)]
      calc eLpNorm (fun x => (v n).snd x i) 2 (volume.restrict Ω)
          ≤ eLpNorm ((v n).snd : 𝔼 → 𝔼) 2 (volume.restrict Ω) :=
            eLpNorm_mono (memLp_snd_apply (v n) i).aestronglyMeasurable
              fun x => PiLp.norm_apply_le _ i
        _ = ENNReal.ofReal ‖(v n).snd‖ := eLpNorm_eq_ofReal_norm _
        _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal ((CoeffField.norm_snd_le (v n)).trans (hM n))
    calc ∑ i : Fin d, eLpNorm (fun x => (Classical.choose (hmem n).2).weakGrad x i) 2
          (volume.restrict Ω) ≤ ∑ _i : Fin d, ENNReal.ofReal M := Finset.sum_le_sum fun i _ => hi i
      _ = ENNReal.ofReal (d * M) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((d + 1) * M) := ENNReal.ofReal_le_ofReal (by nlinarith)
  obtain ⟨φ, hφ, u, hu, hlim⟩ := Sobolev.rellich_kondrachov_W01p_seq hΩ hb (by norm_num)
    (by norm_num) hmem hfun hgrad
  refine ⟨φ, hφ, hu.toLp u, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have heq : ∀ k, ‖(v (φ k)).fst - hu.toLp u‖ =
      (eLpNorm (fun x => (v (φ k)).fst x - u x) 2 (volume.restrict Ω)).toReal := fun k => by
    rw [Lp.norm_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (v (φ k)).fst (hu.toLp u), hu.coeFn_toLp] with x h1 h2
    rw [h1, Pi.sub_apply, h2]
  simp_rw [heq]
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  rw [ENNReal.toReal_zero] at h
  exact h

/-- The embedding `W^{1,2}_0(Ω) → L²(Ω)`, `(u, G) ↦ u`. -/
def H01.fstL (Ω : Set 𝔼) : H01 volume Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  (WithLp.fstL 2 ℝ (Lp ℝ 2 (volume.restrict Ω)) (Lp 𝔼 2 (volume.restrict Ω))).comp
    (H01 volume Ω).subtypeL

@[simp] theorem H01.fstL_apply (Ω : Set 𝔼) (v : H01 volume Ω) :
    H01.fstL Ω v = (v : L2Pair volume Ω).fst := rfl

/-- **The embedding `W^{1,2}_0(Ω) ↪ L²(Ω)` is compact** for bounded open `Ω ⊆ ℝ^d`. -/
theorem isCompactOperator_H01_fst {Ω : Set 𝔼} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    IsCompactOperator (H01.fstL Ω) := by
  refine (isCompactOperator_iff_isCompact_closure_image_ball
    (H01.fstL Ω : H01 volume Ω →ₗ[ℝ] Lp ℝ 2 (volume.restrict Ω)) one_pos).mpr ?_
  refine IsSeqCompact.isCompact fun y hy => ?_
  -- approximate each `y n` by an image point
  have hpick : ∀ n, ∃ w ∈ Metric.ball (0 : H01 volume Ω) 1,
      dist (H01.fstL Ω w) (y n) < 1 / (n + 1) := fun n => by
    have h := Metric.mem_closure_iff.mp (hy n) (1 / (n + 1)) Nat.one_div_pos_of_nat
    obtain ⟨_, ⟨w, hw, rfl⟩, hd⟩ := h
    exact ⟨w, hw, by rw [dist_comm]; exact hd⟩
  choose w hw hwd using hpick
  obtain ⟨φ, hφ, g, hg⟩ := rellich_H01 hΩ hb (v := fun n => (w n : L2Pair volume Ω))
    (fun n => (w n).2) (M := 1) fun n => by
      have := hw n
      rw [Metric.mem_ball, dist_zero_right] at this
      exact this.le
  have hgw : Tendsto (fun k => H01.fstL Ω (w (φ k))) atTop (𝓝 g) := hg
  have hdist : Tendsto (fun k => dist (H01.fstL Ω (w (φ k))) (y (φ k))) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => dist_nonneg) (fun k => (hwd (φ k)).le) ?_
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact h1.comp hφ.tendsto_atTop
  have hyg : Tendsto (fun k => y (φ k)) atTop (𝓝 g) :=
    tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun k => dist_nonneg)
      (fun k => dist_triangle_left (y (φ k)) g (H01.fstL Ω (w (φ k))))
      (by simpa using hdist.add (tendsto_iff_dist_tendsto_zero.mp hgw)))
  refine ⟨g, ?_, φ, hφ, hyg⟩
  exact mem_closure_of_tendsto hgw
    (Eventually.of_forall fun k => Set.mem_image_of_mem _ (hw (φ k)))

end ConicalKahler.Sobolev
