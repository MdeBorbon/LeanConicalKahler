module

public import ConicalKahler.Analysis.HyperplaneMaps
public import ConicalKahler.Cone.Weights

/-!
# Comparison of cone models under hyperplane-matching coordinate changes

Let `θ₂` and `θ₁` be cone weights on two coordinate systems, and let `Φ` be a holomorphic map
from `θ₂`-coordinates to `θ₁`-coordinates near `ζ₀`, with holomorphic local inverse `Φ'`. The
hypothesis `WeightsMatch θ₁ θ₂ Φ Φ' ζ₀` says: every singular coordinate `k` of `θ₁` whose
hyperplane passes through `Φ ζ₀` is matched with a singular coordinate `j` of `θ₂` **of the same
cone angle**, whose hyperplane passes through `ζ₀`, such that `Φ` maps `{ζ_j = 0}` into
`{z_k = 0}` and `Φ'` maps `{z_k = 0}` into `{ζ_j = 0}`. The indices `j` and `k` may differ, so the
matching may permute coordinates.

If all cone angles of `θ₂` are `≤ 1`, then near `ζ₀` (`exists_weighted_upper_bound`)

  `q_{θ₁}(Φ ζ; DΦ(ζ) v) ≤ K q_{θ₂}(ζ; v)`,

and with matchings in both directions and all angles `≤ 1` the comparison is two-sided
(`exists_weighted_model_comparison`). This is the analytic core of chart invariance, both for
smooth divisors (`ConicalKahler.Cone.ChartInvariance`) and for SNC divisors
(`ConicalKahler.Cone.SNCChartInvariance`).

## Where `β ≤ 1` is used

* `norm_sq_le_modelConeQuadratic`: on `{|ζ_j| ≤ R}`, a weight `β² |ζ_j|^(2β-2)` with `β ≤ 1` is
  at least `β² R^(2β-2) > 0`. So the unweighted norm `|v|²` is controlled by `q_{θ₂}(ζ; v)`.
  Derivatives of `Φ` may mix singular directions into the others (as the shear does), and this
  is harmless exactly in this regime.
* `cone_term_le`: `|z_k| ≥ c |ζ_j|` gives `|z_k|^(2β-2) ≤ c^(2β-2) |ζ_j|^(2β-2)` because the exponent
  is `≤ 0`.

Coordinates of `θ₁` whose hyperplane does *not* pass through `Φ ζ₀` need no matching. Their
weight is bounded near `Φ ζ₀`.
-/

@[expose] public section

open scoped ContDiff Topology
open Filter Set

namespace ConicalKahler

variable {n : ℕ}

/-! ### A scalar inequality -/

/-- **The one-term weighted inequality** (uses `β ≤ 1`). If `0 < x ≤ 1`, `y ≥ c x` and
`X ≤ L u + L₂ x V`, then
`β² y^(2β-2) X² ≤ 2 L² c^(2β-2) (β² x^(2β-2) u²) + 2 L₂² c^(2β-2) β² V²`. -/
theorem cone_term_le {β c L L₂ x y X u V : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1) (hc : 0 < c) (hx : 0 < x)
    (hx1 : x ≤ 1) (hy : c * x ≤ y) (hX0 : 0 ≤ X) (hX : X ≤ L * u + L₂ * x * V) :
    β ^ 2 * y ^ (2 * β - 2) * X ^ 2 ≤
      2 * L ^ 2 * c ^ (2 * β - 2) * (β ^ 2 * x ^ (2 * β - 2) * u ^ 2) +
        2 * L₂ ^ 2 * c ^ (2 * β - 2) * β ^ 2 * V ^ 2 := by
  set a := 2 * β - 2 with ha_def
  have ha : a ≤ 0 := by rw [ha_def]; linarith
  have hya : y ^ a ≤ c ^ a * x ^ a := by
    calc y ^ a ≤ (c * x) ^ a := Real.rpow_le_rpow_of_nonpos (mul_pos hc hx) hy ha
      _ = c ^ a * x ^ a := Real.mul_rpow hc.le hx.le
  have hxa : x ^ a * x ^ 2 ≤ 1 := by
    have h : x ^ a * x ^ 2 = x ^ (a + 2) := by rw [Real.rpow_add hx, Real.rpow_two]
    rw [h]
    exact Real.rpow_le_one hx.le hx1 (by rw [ha_def]; linarith)
  have hX2 : X ^ 2 ≤ 2 * L ^ 2 * u ^ 2 + 2 * L₂ ^ 2 * x ^ 2 * V ^ 2 := by
    have hsq : X ^ 2 ≤ (L * u + L₂ * x * V) ^ 2 := pow_le_pow_left₀ hX0 hX 2
    nlinarith [sq_nonneg (L * u - L₂ * x * V)]
  have hca : 0 ≤ c ^ a := (Real.rpow_pos_of_pos hc a).le
  have hxa0 : 0 ≤ x ^ a := (Real.rpow_pos_of_pos hx a).le
  calc β ^ 2 * y ^ a * X ^ 2 ≤ β ^ 2 * (c ^ a * x ^ a) * X ^ 2 := by gcongr
    _ ≤ β ^ 2 * (c ^ a * x ^ a) * (2 * L ^ 2 * u ^ 2 + 2 * L₂ ^ 2 * x ^ 2 * V ^ 2) := by
        gcongr
    _ = 2 * L ^ 2 * c ^ a * (β ^ 2 * x ^ a * u ^ 2) +
          2 * L₂ ^ 2 * c ^ a * β ^ 2 * V ^ 2 * (x ^ a * x ^ 2) := by ring
    _ ≤ 2 * L ^ 2 * c ^ a * (β ^ 2 * x ^ a * u ^ 2) +
          2 * L₂ ^ 2 * c ^ a * β ^ 2 * V ^ 2 * 1 := by gcongr
    _ = _ := by ring

/-! ### The model controls the Euclidean norm when all angles are `≤ 1` -/

/-- The inverse of the lower bound `β² R^(2β-2)` for a cone weight on `{|z_j| ≤ R}` (and `1` for a
smooth direction). -/
noncomputable def invWeightBound (θ : ConeWeights n) (R : ℝ) (j : Fin n) : ℝ :=
  match θ.angle j with
  | none => 1
  | some β => (β.beta ^ 2 * R ^ (2 * β.beta - 2))⁻¹

theorem invWeightBound_nonneg (θ : ConeWeights n) {R : ℝ} (hR : 0 < R) (j : Fin n) :
    0 ≤ invWeightBound θ R j := by
  unfold invWeightBound
  cases θ.angle j with
  | none => exact zero_le_one
  | some β =>
    have := Real.rpow_pos_of_pos hR (2 * β.beta - 2)
    have := β.pos
    positivity

/-- On `{|z_j| ≤ R}`, `|w|² ≤ B_j w_j(z) |w|²` with `B_j = invWeightBound θ R j`, provided the cone
angle of the coordinate is `≤ 1`. -/
theorem normSq_le_invWeightBound_mul {θ : ConeWeights n}
    (hθ : ∀ j β, θ.angle j = some β → β.beta ≤ 1) {z : E n} (hz : z ∈ modelDomain θ) {R : ℝ}
    (hR : ∀ j, ‖z j‖ ≤ R) (j : Fin n) (w : ℂ) :
    Complex.normSq w ≤ invWeightBound θ R j * (modelWeight θ z j * Complex.normSq w) := by
  unfold invWeightBound
  cases hθj : θ.angle j with
  | none => simp [modelWeight_of_none hθj]
  | some β =>
    rw [modelWeight_of_some hθj]
    have hx : 0 < ‖z j‖ := norm_pos_iff.mpr (hz j β hθj)
    have hR0 : 0 < R := lt_of_lt_of_le hx (hR j)
    have hβ0 := β.pos
    have ha : 2 * β.beta - 2 ≤ 0 := by linarith [hθ j β hθj]
    have hle : R ^ (2 * β.beta - 2) ≤ ‖z j‖ ^ (2 * β.beta - 2) :=
      Real.rpow_le_rpow_of_nonpos hx (hR j) ha
    have hRa : 0 < R ^ (2 * β.beta - 2) := Real.rpow_pos_of_pos hR0 _
    have hw := Complex.normSq_nonneg w
    have hB : 0 < β.beta ^ 2 * R ^ (2 * β.beta - 2) := by positivity
    calc Complex.normSq w
        = (β.beta ^ 2 * R ^ (2 * β.beta - 2))⁻¹ *
            (β.beta ^ 2 * R ^ (2 * β.beta - 2) * Complex.normSq w) := by
          field_simp
      _ ≤ (β.beta ^ 2 * R ^ (2 * β.beta - 2))⁻¹ *
            (β.beta ^ 2 * ‖z j‖ ^ (2 * β.beta - 2) * Complex.normSq w) := by
          gcongr

/-- A single term of the model quadratic form is bounded by the whole form. -/
theorem modelWeight_mul_normSq_le (θ : ConeWeights n) (z v : E n) (j : Fin n) :
    modelWeight θ z j * Complex.normSq (v j) ≤ modelConeQuadratic θ z v :=
  Finset.single_le_sum (f := fun j => modelWeight θ z j * Complex.normSq (v j))
    (fun k _ => mul_nonneg (modelWeight_nonneg θ z k) (Complex.normSq_nonneg _))
    (Finset.mem_univ j)

/-- **The model controls the Euclidean norm** on `{|z_j| ≤ R}` when all cone angles are `≤ 1`:
`|v|² ≤ (∑_j B_j) q_θ(z; v)`. -/
theorem norm_sq_le_modelConeQuadratic {θ : ConeWeights n}
    (hθ : ∀ j β, θ.angle j = some β → β.beta ≤ 1) {z : E n} (hz : z ∈ modelDomain θ) {R : ℝ}
    (hR0 : 0 < R) (hR : ∀ j, ‖z j‖ ≤ R) (v : E n) :
    ‖v‖ ^ 2 ≤ (∑ j, invWeightBound θ R j) * modelConeQuadratic θ z v := by
  rw [EuclideanSpace.norm_sq_eq, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← Complex.normSq_eq_norm_sq]
  exact (normSq_le_invWeightBound_mul hθ hz hR j (v j)).trans
    (mul_le_mul_of_nonneg_left (modelWeight_mul_normSq_le θ z v j)
      (invWeightBound_nonneg θ hR0 j))

/-! ### Matching of singular hyperplanes -/

/-- Every singular coordinate `k` of `θ₁` with `(Φ ζ₀)_k = 0` is matched with a singular coordinate
`j` of `θ₂` of the **same** cone angle with `ζ₀_j = 0`, such that `Φ` maps `{ζ_j = 0}` into
`{z_k = 0}` near `ζ₀` and `Φ'` maps `{z_k = 0}` into `{ζ_j = 0}` near `Φ ζ₀`. -/
def WeightsMatch (θ₁ θ₂ : ConeWeights n) (Φ Φ' : E n → E n) (ζ₀ : E n) : Prop :=
  ∀ k β, θ₁.angle k = some β → Φ ζ₀ k = 0 → ∃ j, θ₂.angle j = some β ∧ ζ₀ j = 0 ∧
    (∀ᶠ ζ in 𝓝 ζ₀, ζ j = 0 → Φ ζ k = 0) ∧ (∀ᶠ z in 𝓝 (Φ ζ₀), z k = 0 → Φ' z j = 0)

/-! ### The upper bound -/

section Bound

variable {θ₁ θ₂ : ConeWeights n} {Φ Φ' : E n → E n} {ζ₀ : E n}

/-- **One coordinate of the target.** For each coordinate `k`, the `k`-th term of
`q_{θ₁}(Φ ζ; DΦ(ζ) v)` is bounded by a multiple of `q_{θ₂}(ζ; v)` near `ζ₀`, and `(Φ ζ)_k ≠ 0` if
`k` is singular for `θ₁`. -/
theorem exists_weighted_term_bound (hθ₂ : ∀ j β, θ₂.angle j = some β → β.beta ≤ 1)
    (hΦ : ContDiffAt ℂ 2 Φ ζ₀) (hΦ' : ContDiffAt ℂ 2 Φ' (Φ ζ₀))
    (hinv : ∀ᶠ ζ in 𝓝 ζ₀, Φ' (Φ ζ) = ζ) (hmatch : WeightsMatch θ₁ θ₂ Φ Φ' ζ₀) (k : Fin n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ ζ in 𝓝 ζ₀, ζ ∈ modelDomain θ₂ →
      (∀ β, θ₁.angle k = some β → Φ ζ k ≠ 0) ∧
      ∀ v, modelWeight θ₁ (Φ ζ) k * Complex.normSq (fderiv ℂ Φ ζ v k) ≤
        K * modelConeQuadratic θ₂ ζ v := by
  -- the Euclidean norm is controlled by `q_{θ₂}` on a ball around `ζ₀`
  set R := ‖ζ₀‖ + 1 with hR_def
  have hR : 0 < R := by positivity
  set A := ∑ j, invWeightBound θ₂ R j with hA_def
  have hA : 0 ≤ A := Finset.sum_nonneg fun j _ => invWeightBound_nonneg θ₂ hR j
  have hnear : ∀ᶠ ζ in 𝓝 ζ₀, ‖ζ - ζ₀‖ < 1 := by
    filter_upwards [Metric.ball_mem_nhds ζ₀ one_pos] with ζ hζ
    rwa [Metric.mem_ball, dist_eq_norm] at hζ
  have hRb : ∀ ζ : E n, ‖ζ - ζ₀‖ < 1 → ∀ j, ‖ζ j‖ ≤ R := fun ζ hζ j => by
    calc ‖ζ j‖ ≤ ‖ζ‖ := norm_apply_le ζ j
      _ = ‖(ζ - ζ₀) + ζ₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖ζ - ζ₀‖ + ‖ζ₀‖ := norm_add_le _ _
      _ ≤ R := by rw [hR_def]; linarith
  have hsmall : ∀ ζ : E n, ‖ζ - ζ₀‖ < 1 → ∀ j, ζ₀ j = 0 → ‖ζ j‖ ≤ 1 := fun ζ hζ j hj => by
    have h := norm_apply_le (ζ - ζ₀) j
    rw [PiLp.sub_apply, hj, sub_zero] at h
    linarith
  have hvq : ∀ ζ : E n, ‖ζ - ζ₀‖ < 1 → ζ ∈ modelDomain θ₂ → ∀ v : E n,
      ‖v‖ ^ 2 ≤ A * modelConeQuadratic θ₂ ζ v := fun ζ hζ hdom v =>
    norm_sq_le_modelConeQuadratic hθ₂ hdom hR (hRb ζ hζ) v
  -- the derivative of `Φ` is bounded near `ζ₀`
  set L := ‖fderiv ℂ Φ ζ₀‖ + 1 with hL_def
  have hDΦ : ∀ᶠ ζ in 𝓝 ζ₀, ‖fderiv ℂ Φ ζ‖ ≤ L :=
    ((hΦ.fderiv_right (m := 1) (by norm_num)).continuousAt.norm.eventually_lt continuousAt_const
      (lt_add_one _)).mono fun _ h => h.le
  have hξ : ∀ ζ : E n, ‖ζ - ζ₀‖ < 1 → ζ ∈ modelDomain θ₂ → ‖fderiv ℂ Φ ζ‖ ≤ L → ∀ v : E n,
      Complex.normSq (fderiv ℂ Φ ζ v k) ≤ L ^ 2 * A * modelConeQuadratic θ₂ ζ v := by
    intro ζ hζ hdom hD v
    have h1 : ‖fderiv ℂ Φ ζ v k‖ ≤ L * ‖v‖ :=
      (norm_apply_le _ k).trans (((fderiv ℂ Φ ζ).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hD (norm_nonneg _)))
    rw [Complex.normSq_eq_norm_sq]
    calc ‖fderiv ℂ Φ ζ v k‖ ^ 2 ≤ (L * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = L ^ 2 * ‖v‖ ^ 2 := by ring
      _ ≤ L ^ 2 * (A * modelConeQuadratic θ₂ ζ v) :=
        mul_le_mul_of_nonneg_left (hvq ζ hζ hdom v) (sq_nonneg _)
      _ = L ^ 2 * A * modelConeQuadratic θ₂ ζ v := by ring
  cases hθk : θ₁.angle k with
  | none =>
    -- a smooth direction: weight `1`
    refine ⟨L ^ 2 * A, by positivity, ?_⟩
    filter_upwards [hnear, hDΦ] with ζ hζ hD hdom
    refine ⟨fun β h => by simp at h, fun v => ?_⟩
    rw [modelWeight_of_none hθk, one_mul]
    exact hξ ζ hζ hdom hD v
  | some β =>
    by_cases hz0 : Φ ζ₀ k = 0
    · -- a singular hyperplane through `Φ ζ₀`: use the matching
      obtain ⟨j, hθj, hζ₀j, hpres, hpres'⟩ := hmatch k β hθk hz0
      have hβ := hθ₂ j β hθj
      obtain ⟨L₁, L₂, -, -, hest⟩ := exists_coordHyperplane_estimates hζ₀j hΦ hpres
      obtain ⟨L', _L₂', hL', -, hest'⟩ := exists_coordHyperplane_estimates hz0 hΦ' hpres'
      have hest'' : ∀ᶠ ζ in 𝓝 ζ₀, ‖Φ' (Φ ζ) j‖ ≤ L' * ‖Φ ζ k‖ :=
        hΦ.continuousAt.tendsto.eventually (Filter.Eventually.mono hest' fun _ h => h.1)
      set c := 1 / L' with hc_def
      have hc : 0 < c := by positivity
      set a := 2 * β.beta - 2
      have hca : 0 ≤ c ^ a := (Real.rpow_pos_of_pos hc a).le
      refine ⟨2 * L₁ ^ 2 * c ^ a + 2 * L₂ ^ 2 * c ^ a * β.beta ^ 2 * A, by positivity, ?_⟩
      filter_upwards [hest, hest'', hinv, hnear] with ζ h1 h2 h3 hζ hdom
      rw [h3] at h2
      have hx : 0 < ‖ζ j‖ := norm_pos_iff.mpr (hdom j β hθj)
      have hy : c * ‖ζ j‖ ≤ ‖Φ ζ k‖ := by
        rw [hc_def, div_mul_eq_mul_div, one_mul, div_le_iff₀ hL']
        linarith
      have hΦk : Φ ζ k ≠ 0 := by
        intro h
        rw [h, norm_zero] at hy
        exact absurd hy (not_le.mpr (mul_pos hc hx))
      refine ⟨fun _ _ => hΦk, fun v => ?_⟩
      rw [modelWeight_of_some hθk, Complex.normSq_eq_norm_sq]
      have hterm := cone_term_le (V := ‖v‖) β.pos.le hβ hc hx (hsmall ζ hζ j hζ₀j) hy (norm_nonneg _)
        (h1.2.2 v)
      have hq₁ : β.beta ^ 2 * ‖ζ j‖ ^ a * ‖v j‖ ^ 2 ≤ modelConeQuadratic θ₂ ζ v := by
        have h := modelWeight_mul_normSq_le θ₂ ζ v j
        rwa [modelWeight_of_some hθj, Complex.normSq_eq_norm_sq] at h
      have hq₂ := hvq ζ hζ hdom v
      calc β.beta ^ 2 * ‖Φ ζ k‖ ^ a * ‖fderiv ℂ Φ ζ v k‖ ^ 2
          ≤ 2 * L₁ ^ 2 * c ^ a * (β.beta ^ 2 * ‖ζ j‖ ^ a * ‖v j‖ ^ 2) +
              2 * L₂ ^ 2 * c ^ a * β.beta ^ 2 * ‖v‖ ^ 2 := hterm
        _ ≤ 2 * L₁ ^ 2 * c ^ a * modelConeQuadratic θ₂ ζ v +
              2 * L₂ ^ 2 * c ^ a * β.beta ^ 2 * (A * modelConeQuadratic θ₂ ζ v) := by
            gcongr
        _ = (2 * L₁ ^ 2 * c ^ a + 2 * L₂ ^ 2 * c ^ a * β.beta ^ 2 * A) *
              modelConeQuadratic θ₂ ζ v := by ring
    · -- a singular hyperplane missing `Φ ζ₀`: the weight is bounded nearby
      have hg : ContinuousAt (fun ζ => ‖Φ ζ k‖) ζ₀ :=
        ((EuclideanSpace.proj k : E n →L[ℂ] ℂ).continuous.continuousAt.comp
          hΦ.continuousAt).norm
      have hg0 : ‖Φ ζ₀ k‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
      set W : E n → ℝ := fun ζ => β.beta ^ 2 * ‖Φ ζ k‖ ^ (2 * β.beta - 2) with hW_def
      have hWc : ContinuousAt W ζ₀ := continuousAt_const.mul (hg.rpow_const (Or.inl hg0))
      have hW0 : 0 ≤ W ζ₀ := by
        have := Real.rpow_nonneg (norm_nonneg (Φ ζ₀ k)) (2 * β.beta - 2)
        positivity
      have hWev : ∀ᶠ ζ in 𝓝 ζ₀, W ζ < W ζ₀ + 1 :=
        hWc.eventually_lt continuousAt_const (lt_add_one _)
      have hne : ∀ᶠ ζ in 𝓝 ζ₀, Φ ζ k ≠ 0 :=
        ((EuclideanSpace.proj k : E n →L[ℂ] ℂ).continuous.continuousAt.comp
          hΦ.continuousAt).eventually_ne hz0
      refine ⟨(W ζ₀ + 1) * (L ^ 2 * A), by positivity, ?_⟩
      filter_upwards [hnear, hDΦ, hWev, hne] with ζ hζ hD hW hk hdom
      refine ⟨fun _ _ => hk, fun v => ?_⟩
      rw [modelWeight_of_some hθk]
      have hWnn : 0 ≤ W ζ := by
        have := Real.rpow_nonneg (norm_nonneg (Φ ζ k)) (2 * β.beta - 2)
        simp only [hW_def]
        positivity
      calc β.beta ^ 2 * ‖Φ ζ k‖ ^ (2 * β.beta - 2) * Complex.normSq (fderiv ℂ Φ ζ v k)
          = W ζ * Complex.normSq (fderiv ℂ Φ ζ v k) := rfl
        _ ≤ (W ζ₀ + 1) * (L ^ 2 * A * modelConeQuadratic θ₂ ζ v) :=
            mul_le_mul hW.le (hξ ζ hζ hdom hD v) (Complex.normSq_nonneg _) (by linarith)
        _ = (W ζ₀ + 1) * (L ^ 2 * A) * modelConeQuadratic θ₂ ζ v := by ring

/-- **Upper bound for the model under a hyperplane-matching coordinate change** (all angles of
`θ₂` at most `1`): near `ζ₀`, `Φ` maps the model domain of `θ₂` into that of `θ₁` and
`q_{θ₁}(Φ ζ; DΦ(ζ) v) ≤ K q_{θ₂}(ζ; v)`. -/
theorem exists_weighted_upper_bound (hθ₂ : ∀ j β, θ₂.angle j = some β → β.beta ≤ 1)
    (hΦ : ContDiffAt ℂ 2 Φ ζ₀) (hΦ' : ContDiffAt ℂ 2 Φ' (Φ ζ₀))
    (hinv : ∀ᶠ ζ in 𝓝 ζ₀, Φ' (Φ ζ) = ζ) (hmatch : WeightsMatch θ₁ θ₂ Φ Φ' ζ₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ ζ in 𝓝 ζ₀, ζ ∈ modelDomain θ₂ → Φ ζ ∈ modelDomain θ₁ ∧ ∀ v,
      modelConeQuadratic θ₁ (Φ ζ) (fderiv ℂ Φ ζ v) ≤ K * modelConeQuadratic θ₂ ζ v := by
  choose K hK0 hK using fun k => exists_weighted_term_bound hθ₂ hΦ hΦ' hinv hmatch k
  have hsum : 0 ≤ ∑ k, K k := Finset.sum_nonneg fun k _ => hK0 k
  refine ⟨1 + ∑ k, K k, by positivity, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hK] with ζ hζ hdom
  refine ⟨fun k β hk => (hζ k hdom).1 β hk, fun v => ?_⟩
  have hq := modelConeQuadratic_nonneg θ₂ ζ v
  calc modelConeQuadratic θ₁ (Φ ζ) (fderiv ℂ Φ ζ v)
      = ∑ k, modelWeight θ₁ (Φ ζ) k * Complex.normSq (fderiv ℂ Φ ζ v k) := rfl
    _ ≤ ∑ k, K k * modelConeQuadratic θ₂ ζ v :=
        Finset.sum_le_sum fun k _ => (hζ k hdom).2 v
    _ = (∑ k, K k) * modelConeQuadratic θ₂ ζ v := by rw [Finset.sum_mul]
    _ ≤ (1 + ∑ k, K k) * modelConeQuadratic θ₂ ζ v := by nlinarith

/-- **Two-sided comparison of cone models under a hyperplane-matching biholomorphism** (all angles
`≤ 1`): near `ζ₀`, `K⁻¹ q_{θ₂}(ζ; v) ≤ q_{θ₁}(Φ ζ; DΦ(ζ) v) ≤ K q_{θ₂}(ζ; v)`. -/
theorem exists_weighted_model_comparison (hθ₁ : ∀ k β, θ₁.angle k = some β → β.beta ≤ 1)
    (hθ₂ : ∀ j β, θ₂.angle j = some β → β.beta ≤ 1)
    (hΦ : ContDiffAt ℂ 2 Φ ζ₀) (hΦ' : ContDiffAt ℂ 2 Φ' (Φ ζ₀))
    (hinv : ∀ᶠ ζ in 𝓝 ζ₀, Φ' (Φ ζ) = ζ) (hinv' : ∀ᶠ z in 𝓝 (Φ ζ₀), Φ (Φ' z) = z)
    (hmatch : WeightsMatch θ₁ θ₂ Φ Φ' ζ₀) (hmatch' : WeightsMatch θ₂ θ₁ Φ' Φ (Φ ζ₀)) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ ζ in 𝓝 ζ₀, ζ ∈ modelDomain θ₂ → Φ ζ ∈ modelDomain θ₁ ∧ ∀ v,
      K⁻¹ * modelConeQuadratic θ₂ ζ v ≤ modelConeQuadratic θ₁ (Φ ζ) (fderiv ℂ Φ ζ v) ∧
        modelConeQuadratic θ₁ (Φ ζ) (fderiv ℂ Φ ζ v) ≤ K * modelConeQuadratic θ₂ ζ v := by
  have hΦ'Φ : Φ' (Φ ζ₀) = ζ₀ := hinv.self_of_nhds
  obtain ⟨K₁, hK₁, hup⟩ := exists_weighted_upper_bound hθ₂ hΦ hΦ' hinv hmatch
  have hΦ'' : ContDiffAt ℂ 2 Φ (Φ' (Φ ζ₀)) := by rwa [hΦ'Φ]
  obtain ⟨K₂, hK₂, hdown⟩ := exists_weighted_upper_bound hθ₁ hΦ' hΦ'' hinv' hmatch'
  have hdown' := hΦ.continuousAt.tendsto.eventually hdown
  have hdΦ : ∀ᶠ ζ in 𝓝 ζ₀, DifferentiableAt ℂ Φ ζ :=
    (hΦ.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have hdΦ' : ∀ᶠ ζ in 𝓝 ζ₀, DifferentiableAt ℂ Φ' (Φ ζ) :=
    hΦ.continuousAt.tendsto.eventually
      ((hΦ'.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num))
  have hloc : ∀ᶠ ζ in 𝓝 ζ₀, ∀ᶠ x in 𝓝 ζ, Φ' (Φ x) = x := hinv.eventually_nhds
  set K := max (max K₁ K₂) 1 with hK_def
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hK₁K : K₁ ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hK₂K : K₂ ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨K, hK1, ?_⟩
  filter_upwards [hup, hdown', hdΦ, hdΦ', hloc, hinv] with ζ h1 h2 h3 h4 h5 h6
  intro hdom
  obtain ⟨hΦdom, hupper⟩ := h1 hdom
  obtain ⟨-, hlower⟩ := h2 hΦdom
  have hq := modelConeQuadratic_nonneg θ₂ ζ
  refine ⟨hΦdom, fun v => ⟨?_, ?_⟩⟩
  · have hcomp : fderiv ℂ (Φ' ∘ Φ) ζ = (fderiv ℂ Φ' (Φ ζ)).comp (fderiv ℂ Φ ζ) :=
      fderiv_comp ζ h4 h3
    have hidf : fderiv ℂ (Φ' ∘ Φ) ζ = ContinuousLinearMap.id ℂ (E n) := by
      have h5' : (Φ' ∘ Φ) =ᶠ[𝓝 ζ] id := h5
      rw [h5'.fderiv_eq, fderiv_id]
    have hid : fderiv ℂ Φ' (Φ ζ) (fderiv ℂ Φ ζ v) = v := by
      have := congrArg (fun A : E n →L[ℂ] E n => A v) (hcomp.symm.trans hidf)
      simpa using this
    have hlow := hlower (fderiv ℂ Φ ζ v)
    rw [hid, h6] at hlow
    rw [inv_mul_le_iff₀ hK0]
    exact hlow.trans (mul_le_mul_of_nonneg_right hK₂K
      (modelConeQuadratic_nonneg θ₁ (Φ ζ) _))
  · exact (hupper v).trans (mul_le_mul_of_nonneg_right hK₁K (hq _))

end Bound

end ConicalKahler
