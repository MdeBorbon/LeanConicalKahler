module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Summing increments over geometric scales (Lemma 2.7)

The paper's Lemma 2.7 (proof omitted there as "elementary") is proved for an abstract family of
"balls" `B ρ` (`0 < ρ ≤ 1`) in a measure space. The family is only required to be increasing,
with `v₀ ρ^m ≤ μ(B ρ) ≤ v₁ ρ^m` (`BallFamily`). This covers Euclidean balls and the geodesic balls of
the cone, which are uniformly comparable. The scaled norm is

  `‖g‖_{B ρ} = (ρ^{-m} ∫_{B ρ} g²)^{1/2}`        (`scaledL2`).

**Lemma 2.7** (`sum_increments`). Let `0 < q < 1`, `α > 0`, `C ≥ 0`, and let `f` be square
integrable on `B 1`. Suppose there are numbers `τ_0, τ_1, …` with

  `‖f − (τ_0 + ⋯ + τ_{k-1})‖_{B(q^k)} ≤ C (q^α)^k`   for all `k ≥ 0`.

Then `∑_k |τ_k| < ∞`, and with `τ = ∑_k τ_k`,

  `‖f − τ‖_{B r} ≤ κ C r^α`   for all `0 < r ≤ 1`,

with `κ = κ(q, α, m, v₀, v₁)` explicit. The paper's hypothesis is written with `τ_1 + ⋯ + τ_k` at
scale `λ^k`, and its conclusion sums from `k = 0`. Indexing the partial sums from `0`, as here, makes
the two consistent.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Finset
open scoped ENNReal

namespace ConicalKahler.Sobolev

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-! ### `L²` norms on sets -/

/-- `(∫_S g²)^{1/2}`. -/
def l2On (μ : Measure X) (S : Set X) (g : X → ℝ) : ℝ := (eLpNorm g 2 (μ.restrict S)).toReal

theorem l2On_nonneg (S : Set X) (g : X → ℝ) : 0 ≤ l2On μ S g := ENNReal.toReal_nonneg

theorem l2On_add_le {S : Set X} {f g : X → ℝ} (hf : MemLp f 2 (μ.restrict S))
    (hg : MemLp g 2 (μ.restrict S)) : l2On μ S (f + g) ≤ l2On μ S f + l2On μ S g := by
  unfold l2On
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩)
    (eLpNorm_add_le (by norm_num))

theorem l2On_sub_le {S : Set X} {f g : X → ℝ} (hf : MemLp f 2 (μ.restrict S))
    (hg : MemLp g 2 (μ.restrict S)) : l2On μ S (f - g) ≤ l2On μ S f + l2On μ S g := by
  unfold l2On
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩)
    (eLpNorm_sub_le (by norm_num))

theorem l2On_mono {S T : Set X} (hST : S ⊆ T) {g : X → ℝ} (hg : MemLp g 2 (μ.restrict T)) :
    l2On μ S g ≤ l2On μ T g :=
  ENNReal.toReal_mono hg.eLpNorm_ne_top
    (eLpNorm_mono_measure _ (Measure.restrict_mono hST le_rfl))

theorem l2On_const {S : Set X} (c : ℝ) :
    l2On μ S (fun _ => c) = |c| * Real.sqrt (μ S).toReal := by
  unfold l2On
  rw [eLpNorm_const' c (by norm_num) (by norm_num), Measure.restrict_apply_univ,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Real.sqrt_eq_rpow]
  simp [Real.norm_eq_abs]

/-! ### Families of balls and the scaled norm -/

/-- An increasing family of sets `B ρ`, `0 < ρ ≤ 1`, with `v₀ ρ^m ≤ μ(B ρ) ≤ v₁ ρ^m`. -/
structure BallFamily (μ : Measure X) (B : ℝ → Set X) (m : ℕ) (v₀ v₁ : ℝ) : Prop where
  mono : ∀ ρ ρ', 0 < ρ → ρ ≤ ρ' → B ρ ⊆ B ρ'
  lt_top : ∀ ρ, 0 < ρ → ρ ≤ 1 → μ (B ρ) < ⊤
  lower : ∀ ρ, 0 < ρ → ρ ≤ 1 → v₀ * ρ ^ m ≤ (μ (B ρ)).toReal
  upper : ∀ ρ, 0 < ρ → ρ ≤ 1 → (μ (B ρ)).toReal ≤ v₁ * ρ ^ m
  pos : 0 < v₀

/-- **The scaled norm** `‖g‖_{B ρ} = (ρ^{-m} ∫_{B ρ} g²)^{1/2}`. -/
def scaledL2 (μ : Measure X) (B : ℝ → Set X) (m : ℕ) (ρ : ℝ) (g : X → ℝ) : ℝ :=
  (Real.sqrt (ρ ^ m))⁻¹ * l2On μ (B ρ) g

variable {B : ℝ → Set X} {m : ℕ} {v₀ v₁ : ℝ}

theorem scaledL2_nonneg (ρ : ℝ) (g : X → ℝ) : 0 ≤ scaledL2 μ B m ρ g :=
  mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (l2On_nonneg _ _)

theorem scaledL2_add_le {ρ : ℝ} {f g : X → ℝ} (hf : MemLp f 2 (μ.restrict (B ρ)))
    (hg : MemLp g 2 (μ.restrict (B ρ))) :
    scaledL2 μ B m ρ (f + g) ≤ scaledL2 μ B m ρ f + scaledL2 μ B m ρ g := by
  unfold scaledL2
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (l2On_add_le hf hg) (inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem scaledL2_sub_le {ρ : ℝ} {f g : X → ℝ} (hf : MemLp f 2 (μ.restrict (B ρ)))
    (hg : MemLp g 2 (μ.restrict (B ρ))) :
    scaledL2 μ B m ρ (f - g) ≤ scaledL2 μ B m ρ f + scaledL2 μ B m ρ g := by
  unfold scaledL2
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (l2On_sub_le hf hg) (inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem BallFamily.memLp_const (hB : BallFamily μ B m v₀ v₁) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (c : ℝ) : MemLp (fun _ : X => c) 2 (μ.restrict (B ρ)) := by
  have : IsFiniteMeasure (μ.restrict (B ρ)) :=
    isFiniteMeasure_restrict.mpr (hB.lt_top ρ hρ0 hρ1).ne
  exact MeasureTheory.memLp_const c

theorem BallFamily.memLp_restrict (hB : BallFamily μ B m v₀ v₁) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) {f : X → ℝ} (hf : MemLp f 2 (μ.restrict (B 1))) :
    MemLp f 2 (μ.restrict (B ρ)) :=
  hf.mono_measure (Measure.restrict_mono (hB.mono ρ 1 hρ0 hρ1) le_rfl)

/-- The scaled norm of a constant: `|c| (μ(B ρ)/ρ^m)^{1/2}`, between `|c| √v₀` and `|c| √v₁`. -/
theorem BallFamily.scaledL2_const (hB : BallFamily μ B m v₀ v₁) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) (c : ℝ) :
    |c| * Real.sqrt v₀ ≤ scaledL2 μ B m ρ (fun _ => c) ∧
      scaledL2 μ B m ρ (fun _ => c) ≤ |c| * Real.sqrt v₁ := by
  have hpos : 0 < ρ ^ m := pow_pos hρ0 m
  have hsq : 0 < Real.sqrt (ρ ^ m) := Real.sqrt_pos.mpr hpos
  have hval : scaledL2 μ B m ρ (fun _ => c) = |c| * Real.sqrt ((μ (B ρ)).toReal / ρ ^ m) := by
    rw [scaledL2, l2On_const, Real.sqrt_div' _ hpos.le]
    field_simp
  rw [hval]
  constructor
  · refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (abs_nonneg c)
    rw [le_div_iff₀ hpos]
    exact hB.lower ρ hρ0 hρ1
  · refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (abs_nonneg c)
    rw [div_le_iff₀ hpos]
    exact hB.upper ρ hρ0 hρ1

/-- Comparison of scales: for `0 < ρ' ≤ ρ ≤ 1`,
`‖g‖_{B ρ'} ≤ (ρ/ρ')^{m/2} ‖g‖_{B ρ}`, written as `√(ρ^m) / √(ρ'^m)`. -/
theorem BallFamily.scaledL2_le_of_le (hB : BallFamily μ B m v₀ v₁) {ρ' ρ : ℝ} (h0 : 0 < ρ')
    (h' : ρ' ≤ ρ) {g : X → ℝ} (hg : MemLp g 2 (μ.restrict (B ρ))) :
    scaledL2 μ B m ρ' g ≤ Real.sqrt (ρ ^ m) / Real.sqrt (ρ' ^ m) * scaledL2 μ B m ρ g := by
  have hρ : 0 < ρ := h0.trans_le h'
  have hs : 0 < Real.sqrt (ρ ^ m) := Real.sqrt_pos.mpr (pow_pos hρ m)
  have hs' : 0 < Real.sqrt (ρ' ^ m) := Real.sqrt_pos.mpr (pow_pos h0 m)
  rw [scaledL2, scaledL2]
  calc (Real.sqrt (ρ' ^ m))⁻¹ * l2On μ (B ρ') g ≤ (Real.sqrt (ρ' ^ m))⁻¹ * l2On μ (B ρ) g :=
        mul_le_mul_of_nonneg_left (l2On_mono (hB.mono ρ' ρ h0 h') hg)
          (inv_nonneg.mpr hs'.le)
    _ = Real.sqrt (ρ ^ m) / Real.sqrt (ρ' ^ m) * ((Real.sqrt (ρ ^ m))⁻¹ * l2On μ (B ρ) g) := by
        field_simp

/-! ### Lemma 2.7 -/

/-- The constant of Lemma 2.7. -/
def incrementConst (q α : ℝ) (m : ℕ) (v₀ v₁ : ℝ) : ℝ :=
  (Real.sqrt (q ^ m))⁻¹ * q ^ (-α) *
    (1 + ((Real.sqrt (q ^ m))⁻¹ + 1) / Real.sqrt v₀ * Real.sqrt v₁ / (1 - q ^ α))

/-- **Lemma 2.7 (summing increments over geometric scales).** -/
theorem sum_increments (hB : BallFamily μ B m v₀ v₁) {q α C : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hα : 0 < α) (hC : 0 ≤ C) {f : X → ℝ} (hf : MemLp f 2 (μ.restrict (B 1))) (τ : ℕ → ℝ)
    (hτ : ∀ k : ℕ, scaledL2 μ B m (q ^ k) (fun x => f x - ∑ j ∈ range k, τ j) ≤ C * (q ^ α) ^ k) :
    Summable (fun k => |τ k|) ∧ ∀ r, 0 < r → r ≤ 1 →
      scaledL2 μ B m r (fun x => f x - ∑' k, τ k) ≤ incrementConst q α m v₀ v₁ * C * r ^ α := by
  set s : ℕ → ℝ := fun k => ∑ j ∈ range k, τ j
  set σ : ℝ := (Real.sqrt (q ^ m))⁻¹
  have hqm : 0 < q ^ m := pow_pos hq0 m
  have hσ0 : 0 < σ := inv_pos.mpr (Real.sqrt_pos.mpr hqm)
  have hσ1 : 1 ≤ σ := by
    rw [le_inv_comm₀ one_pos (Real.sqrt_pos.mpr hqm), inv_one]
    exact Real.sqrt_le_one.mpr (pow_le_one₀ hq0.le hq1.le)
  set r₀ : ℝ := q ^ α
  have hr₀0 : 0 < r₀ := Real.rpow_pos_of_pos hq0 α
  have hr₀1 : r₀ < 1 := Real.rpow_lt_one hq0.le hq1 hα
  have hv₀ := Real.sqrt_pos.mpr hB.pos
  have hqk0 : ∀ k : ℕ, 0 < q ^ k := fun k => pow_pos hq0 k
  have hqk1 : ∀ k : ℕ, q ^ k ≤ 1 := fun k => pow_le_one₀ hq0.le hq1.le
  -- memberships
  have hmem : ∀ k : ℕ, ∀ ρ, 0 < ρ → ρ ≤ 1 → ∀ c : ℝ, MemLp (fun x => f x - c) 2 (μ.restrict (B ρ)) :=
    fun _ ρ h0 h1 c => (hB.memLp_restrict h0 h1 hf).sub (hB.memLp_const h0 h1 c)
  -- one scale down costs `σ`
  have hstep : ∀ (k : ℕ) (g : X → ℝ), MemLp g 2 (μ.restrict (B (q ^ k))) →
      scaledL2 μ B m (q ^ (k + 1)) g ≤ σ * scaledL2 μ B m (q ^ k) g := by
    intro k g hg
    have h := hB.scaledL2_le_of_le (hqk0 (k + 1)) (pow_le_pow_of_le_one hq0.le hq1.le
      (Nat.le_succ k)) hg
    have hratio : Real.sqrt ((q ^ k) ^ m) / Real.sqrt ((q ^ (k + 1)) ^ m) = σ := by
      rw [pow_succ, mul_pow, Real.sqrt_mul (pow_nonneg (pow_nonneg hq0.le _) _), div_mul_eq_div_div,
        div_self (Real.sqrt_pos.mpr (pow_pos (hqk0 k) m)).ne', one_div]
    rwa [hratio] at h
  -- (1) the increments are geometrically small
  set A : ℝ := (σ + 1) / Real.sqrt v₀
  have hA : 0 ≤ A := div_nonneg (by linarith) hv₀.le
  have hτk : ∀ k, |τ k| ≤ A * C * r₀ ^ k := by
    intro k
    have hconst := (hB.scaledL2_const (hqk0 (k + 1)) (hqk1 (k + 1)) (τ k)).1
    have heq : (fun _ : X => τ k) =
        (fun x => f x - s k) - (fun x => f x - s (k + 1)) := by
      funext x
      simp only [Pi.sub_apply, s, Finset.sum_range_succ]
      ring
    have h1 : scaledL2 μ B m (q ^ (k + 1)) (fun _ => τ k) ≤
        scaledL2 μ B m (q ^ (k + 1)) (fun x => f x - s k) +
          scaledL2 μ B m (q ^ (k + 1)) (fun x => f x - s (k + 1)) := by
      rw [heq]
      exact scaledL2_sub_le (hmem k _ (hqk0 _) (hqk1 _) _) (hmem k _ (hqk0 _) (hqk1 _) _)
    have h2 := hstep k _ (hmem k _ (hqk0 k) (hqk1 k) (s k))
    have h3 := hτ k
    have h4 := hτ (k + 1)
    have hrk : 0 ≤ r₀ ^ k := pow_nonneg hr₀0.le k
    have h5 : |τ k| * Real.sqrt v₀ ≤ (σ + 1) * C * r₀ ^ k := by
      calc |τ k| * Real.sqrt v₀ ≤ σ * (C * r₀ ^ k) + C * r₀ ^ (k + 1) := by
            nlinarith [mul_le_mul_of_nonneg_left h3 hσ0.le]
        _ ≤ (σ + 1) * C * r₀ ^ k := by
            rw [pow_succ]
            nlinarith [mul_le_mul_of_nonneg_left hr₀1.le (mul_nonneg hC hrk)]
    rw [show A * C * r₀ ^ k = (σ + 1) * C * r₀ ^ k / Real.sqrt v₀ by
      simp only [A]
      ring]
    rw [le_div_iff₀ hv₀]
    exact h5
  have hgeom : Summable fun k : ℕ => A * C * r₀ ^ k :=
    (summable_geometric_of_lt_one hr₀0.le hr₀1).mul_left (A * C)
  have hsum : Summable fun k => |τ k| :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hτk hgeom
  refine ⟨hsum, fun r hr0 hr1 => ?_⟩
  set T := ∑' k, τ k
  have hsumτ : Summable τ := hsum.of_abs
  -- (2) the tails
  have htail : ∀ k, |s k - T| ≤ A * C * r₀ ^ k / (1 - r₀) := by
    intro k
    have h := (hsumτ.sum_add_tsum_nat_add k).symm
    have hT : s k - T = -∑' j, τ (j + k) := by
      simp only [T, s]
      rw [h]
      ring
    rw [hT, abs_neg]
    have hle : ∀ j, |τ (j + k)| ≤ A * C * r₀ ^ k * r₀ ^ j := fun j => by
      have := hτk (j + k)
      rwa [pow_add, mul_comm (r₀ ^ j), ← mul_assoc] at this
    have hsk : Summable fun j => |τ (j + k)| := (summable_nat_add_iff k).mpr hsum
    calc |∑' j, τ (j + k)| = ‖∑' j, τ (j + k)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' j, ‖τ (j + k)‖ := norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hsk)
      _ = ∑' j, |τ (j + k)| := by simp only [Real.norm_eq_abs]
      _ ≤ ∑' j, A * C * r₀ ^ k * r₀ ^ j :=
          Summable.tsum_le_tsum hle ((summable_nat_add_iff k).mpr hsum)
            ((summable_geometric_of_lt_one hr₀0.le hr₀1).mul_left _)
      _ = A * C * r₀ ^ k / (1 - r₀) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hr₀0.le hr₀1, div_eq_mul_inv]
  -- (3) the estimate at the scales `q^k`
  have hscale : ∀ k : ℕ, scaledL2 μ B m (q ^ k) (fun x => f x - T) ≤
      (1 + A * Real.sqrt v₁ / (1 - r₀)) * C * r₀ ^ k := by
    intro k
    have heq : (fun x => f x - T) = (fun x => f x - s k) + fun _ => s k - T := by
      funext x
      simp only [Pi.add_apply]
      ring
    rw [heq]
    refine (scaledL2_add_le (hmem k _ (hqk0 k) (hqk1 k) _)
      (hB.memLp_const (hqk0 k) (hqk1 k) _)).trans ?_
    have hc := (hB.scaledL2_const (hqk0 k) (hqk1 k) (s k - T)).2
    have ht := htail k
    have hr1 : 0 < 1 - r₀ := by linarith
    have hv1 : 0 ≤ Real.sqrt v₁ := Real.sqrt_nonneg _
    calc scaledL2 μ B m (q ^ k) (fun x => f x - s k) +
          scaledL2 μ B m (q ^ k) (fun _ => s k - T)
        ≤ C * r₀ ^ k + A * C * r₀ ^ k / (1 - r₀) * Real.sqrt v₁ :=
          add_le_add (hτ k) (hc.trans (mul_le_mul_of_nonneg_right ht hv1))
      _ = (1 + A * Real.sqrt v₁ / (1 - r₀)) * C * r₀ ^ k := by
          field_simp
  -- (4) interpolation between scales
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one hr0 hr1 hq0 hq1
  have hcomp := hB.scaledL2_le_of_le hr0 hk2 (hmem k _ (hqk0 k) (hqk1 k) T)
  have hratio : Real.sqrt ((q ^ k) ^ m) / Real.sqrt (r ^ m) ≤ σ := by
    rw [← Real.sqrt_div' _ (pow_nonneg hr0.le m)]
    simp only [σ]
    rw [← Real.sqrt_inv]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ (pow_pos hr0 m)]
    calc (q ^ k) ^ m = (q ^ m)⁻¹ * (q ^ (k + 1)) ^ m := by
          rw [pow_succ, mul_pow, mul_comm ((q ^ k) ^ m), ← mul_assoc, inv_mul_cancel₀ hqm.ne',
            one_mul]
      _ ≤ (q ^ m)⁻¹ * r ^ m :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hqk0 _).le hk1.le m)
            (inv_nonneg.mpr hqm.le)
  have hrk : r₀ ^ k ≤ q ^ (-α) * r ^ α := by
    have h1 : r₀ ^ k = q ^ (-α) * (q ^ (k + 1)) ^ α := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast q, ← Real.rpow_mul hq0.le,
        ← Real.rpow_mul hq0.le, ← Real.rpow_add hq0]
      push_cast
      ring_nf
    rw [h1]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (pow_nonneg hq0.le _) hk1.le hα.le)
      (Real.rpow_nonneg hq0.le _)
  have hK : 0 ≤ 1 + A * Real.sqrt v₁ / (1 - r₀) :=
    add_nonneg zero_le_one (div_nonneg (mul_nonneg hA (Real.sqrt_nonneg _)) (by linarith))
  calc scaledL2 μ B m r (fun x => f x - T)
      ≤ Real.sqrt ((q ^ k) ^ m) / Real.sqrt (r ^ m) *
          scaledL2 μ B m (q ^ k) (fun x => f x - T) := hcomp
    _ ≤ σ * ((1 + A * Real.sqrt v₁ / (1 - r₀)) * C * r₀ ^ k) :=
        mul_le_mul hratio (hscale k) (scaledL2_nonneg _ _) hσ0.le
    _ ≤ σ * ((1 + A * Real.sqrt v₁ / (1 - r₀)) * C * (q ^ (-α) * r ^ α)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrk
          (mul_nonneg hK hC)) hσ0.le
    _ = incrementConst q α m v₀ v₁ * C * r ^ α := by
        simp only [incrementConst, A, σ, r₀]
        ring

end ConicalKahler.Sobolev
