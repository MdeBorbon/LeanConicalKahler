module

public import ConicalKahler.Sobolev.Rellich
public import ConicalKahler.Sobolev.Restrict

/-!
# Harmonic approximation (paper, Lemma 2.4) and compactness of approximate solutions

**Lemma 2.4 of the paper.** *For every `ε > 0` there is `δ > 0` such that: if `u ∈ W^{1,2}(B_1)`
satisfies `Δu = f` with `‖u‖_{L²(B_1)} ≤ 1` and `‖f‖_{L²(B_1)} < δ`, then there is a weakly
harmonic `h ∈ W^{1,2}(B_{1/2})` with `‖u - h‖_{L²(B_{1/2})} < ε`.*

The paper proves this by contradiction, with Caccioppoli and Rellich. Here it is proved in two
ways.

1. **Harmonic replacement (direct, explicit and uniform).** Let `w ∈ W^{1,2}_0(Ω)` solve
   `-div(A ∇w) = f` (Lax–Milgram) and `h = u - w`. Then `h` is weakly `A`-harmonic on all of `Ω`,
   and the energy estimate with Friedrichs–Poincaré gives
   `λ ‖u - h‖_{L²(Ω)} ≤ 4R² ‖f‖_{L²(Ω)}` whenever `Ω ⊆ B̄(x₀, R)`
   (`exists_harmonic_replacement`). Hence Lemma 2.4 holds with the explicit
   `δ = λ ε / (4R² + 1)` (`harmonic_approximation`). This `δ` depends only on `λ`, `R` and `ε`,
   **not on the centre `x₀` or the shape of `Ω`**, and the hypothesis `‖u‖ ≤ 1` is not needed.
   For the cone this gives Lemma 2.4 on every geodesic ball `B(x, ρ)` with a `δ` independent of
   `x` (`cone_harmonic_approximation`), which is the uniformity required in Proposition 5.1.
2. **Compactness of approximate solutions** (the paper's argument). Let `v_n` be weak solutions
   of `-div(A ∇u_n) = f_n` on a bounded open `Ω ⊆ ℝ^d`, with `‖u_n‖_{L²(Ω)}` bounded and
   `f_n → f` in `L²(Ω)`. Let `U` be open with compact closure in `Ω`. Then a subsequence
   converges **in `W^{1,2}(U)`** (strongly, function and gradient) to a weak solution of
   `-div(A ∇u) = f` on `U` (`exists_tendsto_of_approx_solutions`).

   The proof combines Rellich (`rellich_H01`, applied to the cut-off pairs `η₁² u_n`) with the
   Caccioppoli inequality applied to the **differences** `u_n - u_m`. So weak compactness in
   `W^{1,2}` is not needed. `harmonic_approximation_of_compactness` derives Lemma 2.4 from it by
   the paper's contradiction argument.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set
open scoped ContDiff ENNReal

namespace ConicalKahler.Sobolev

/-! ### Harmonic replacement -/

section General

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {μ : Measure F} [μ.IsAddHaarMeasure]

namespace CoeffField

variable {c : CoeffField F μ} {Ω : Set F}

theorem IsWeakSolution.sub {f₁ f₂ : Lp ℝ 2 (μ.restrict Ω)} {v₁ v₂ : L2Pair μ Ω}
    (h₁ : c.IsWeakSolution f₁ v₁) (h₂ : c.IsWeakSolution f₂ v₂) :
    c.IsWeakSolution (f₁ - f₂) (v₁ - v₂) := by
  refine ⟨(W12 μ Ω).sub_mem h₁.1 h₂.1, fun φ hφ => ?_⟩
  rw [ContinuousLinearMap.map_sub₂, h₁.2 φ hφ, h₂.2 φ hφ, inner_sub_left]

theorem isWeakSolution_zero_of_sub {f : Lp ℝ 2 (μ.restrict Ω)} {v w : L2Pair μ Ω}
    (hv : c.IsWeakSolution f v) (hw : c.IsWeakSolution f w) : c.IsWeakSolution 0 (v - w) := by
  have h := hv.sub hw
  rwa [sub_self] at h

variable [Nontrivial F]

/-- **Energy estimate on `W^{1,2}_0(Ω)`.** If `w ∈ W^{1,2}_0(Ω)` solves `-div(A ∇w) = f` and
`Ω ⊆ B̄(x₀, R)`, then `λ ‖∇w‖ ≤ 2R ‖f‖`. -/
theorem lam_mul_norm_snd_le {x₀ : F} {R : ℝ} (hR : 0 ≤ R) (hΩ : Ω ⊆ Metric.closedBall x₀ R)
    {f : Lp ℝ 2 (μ.restrict Ω)} {w : L2Pair μ Ω} (hw : w ∈ H01 μ Ω)
    (hsol : c.IsWeakSolution f w) : c.lam * ‖w.snd‖ ≤ 2 * R * ‖f‖ := by
  have hP := norm_fst_le_of_mem_H01 hR hΩ hw
  have hE := hsol.forall_H01 hw
  have hco := c.lam_mul_norm_sq_le Ω w.snd
  rw [dirichletForm_apply] at hE
  have hcs : ⟪f, w.fst⟫_ℝ ≤ ‖f‖ * ‖w.fst‖ := real_inner_le_norm _ _
  have h1 : c.lam * ‖w.snd‖ ^ 2 ≤ ‖f‖ * (2 * R * ‖w.snd‖) := by
    calc c.lam * ‖w.snd‖ ^ 2 ≤ ⟪c.mulOp Ω w.snd, w.snd⟫_ℝ := hco
      _ = ⟪f, w.fst⟫_ℝ := hE
      _ ≤ ‖f‖ * ‖w.fst‖ := hcs
      _ ≤ ‖f‖ * (2 * R * ‖w.snd‖) := by gcongr
  rcases (norm_nonneg w.snd).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    positivity
  · have : c.lam * ‖w.snd‖ * ‖w.snd‖ ≤ 2 * R * ‖f‖ * ‖w.snd‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos

/-- `λ ‖w‖_{L²} ≤ 4R² ‖f‖` for the solution `w ∈ W^{1,2}_0(Ω)` of `-div(A ∇w) = f`. -/
theorem lam_mul_norm_fst_le {x₀ : F} {R : ℝ} (hR : 0 ≤ R) (hΩ : Ω ⊆ Metric.closedBall x₀ R)
    {f : Lp ℝ 2 (μ.restrict Ω)} {w : L2Pair μ Ω} (hw : w ∈ H01 μ Ω)
    (hsol : c.IsWeakSolution f w) : c.lam * ‖w.fst‖ ≤ 4 * R ^ 2 * ‖f‖ := by
  have hP := norm_fst_le_of_mem_H01 hR hΩ hw
  have hE := lam_mul_norm_snd_le hR hΩ hw hsol
  have hl := c.lam_pos
  calc c.lam * ‖w.fst‖ ≤ c.lam * (2 * R * ‖w.snd‖) := by gcongr
    _ = 2 * R * (c.lam * ‖w.snd‖) := by ring
    _ ≤ 2 * R * (2 * R * ‖f‖) := by gcongr
    _ = 4 * R ^ 2 * ‖f‖ := by ring

/-- **Harmonic replacement.** Let `Ω ⊆ B̄(x₀, R)` and let `v = (u, ∇u) ∈ W^{1,2}(Ω)` solve
`-div(A ∇u) = f` weakly. Then there is a weakly `A`-harmonic `h ∈ W^{1,2}(Ω)` with
`v - h ∈ W^{1,2}_0(Ω)` (the same boundary values) and
`λ ‖∇(u - h)‖ ≤ 2R ‖f‖`, `λ ‖u - h‖ ≤ 4R² ‖f‖` in `L²(Ω)`. -/
theorem exists_harmonic_replacement {x₀ : F} {R : ℝ} (hR : 0 ≤ R)
    (hΩ : Ω ⊆ Metric.closedBall x₀ R) {f : Lp ℝ 2 (μ.restrict Ω)} {v : L2Pair μ Ω}
    (hv : c.IsWeakSolution f v) :
    ∃ h : L2Pair μ Ω, c.IsWeakSolution 0 h ∧ v - h ∈ H01 μ Ω ∧
      c.lam * ‖(v - h).snd‖ ≤ 2 * R * ‖f‖ ∧ c.lam * ‖(v - h).fst‖ ≤ 4 * R ^ 2 * ‖f‖ := by
  obtain ⟨w, hw, -⟩ := c.existsUnique_H01_isWeakSolution hR hΩ f
  refine ⟨v - w, isWeakSolution_zero_of_sub hv hw, ?_, ?_, ?_⟩
  · rw [sub_sub_cancel]
    exact w.2
  · rw [sub_sub_cancel]
    exact lam_mul_norm_snd_le hR hΩ w.2 hw
  · rw [sub_sub_cancel]
    exact lam_mul_norm_fst_le hR hΩ w.2 hw

/-- **Lemma 2.4 (harmonic approximation), with an explicit and uniform `δ`.** Let
`Ω ⊆ B̄(x₀, R)`. If `-div(A ∇u) = f` weakly on `Ω` and `‖f‖_{L²(Ω)} < λ ε / (4R² + 1)`, then
there is a weakly `A`-harmonic `h` on `Ω` with `‖u - h‖_{L²(Ω)} < ε`. The threshold depends only
on `λ`, `R` and `ε`: not on `x₀`, not on `Ω`, and no bound on `u` is needed. -/
theorem harmonic_approximation {x₀ : F} {R : ℝ} (hR : 0 ≤ R) (hΩ : Ω ⊆ Metric.closedBall x₀ R)
    {ε : ℝ} {f : Lp ℝ 2 (μ.restrict Ω)} {v : L2Pair μ Ω}
    (hv : c.IsWeakSolution f v) (hf : ‖f‖ < c.lam * ε / (4 * R ^ 2 + 1)) :
    ∃ h : L2Pair μ Ω, c.IsWeakSolution 0 h ∧ ‖v.fst - h.fst‖ < ε := by
  obtain ⟨h, hh, -, -, hfst⟩ := exists_harmonic_replacement hR hΩ hv
  refine ⟨h, hh, ?_⟩
  rw [WithLp.sub_fst] at hfst
  have hl := c.lam_pos
  have hden : 0 < 4 * R ^ 2 + 1 := by positivity
  have h1 : 4 * R ^ 2 * ‖f‖ < c.lam * ε := by
    have h2 : ‖f‖ * (4 * R ^ 2 + 1) < c.lam * ε := (lt_div_iff₀ hden).mp hf
    nlinarith [norm_nonneg f]
  have h3 : c.lam * ‖v.fst - h.fst‖ < c.lam * ε := hfst.trans_lt h1
  exact lt_of_mul_lt_mul_left h3 hl.le

/-- **Lemma 2.4 in the paper's form**: the approximation on a smaller domain `U ⊆ Ω` (the paper
takes `U = B_{1/2}`, `Ω = B_1`). -/
theorem harmonic_approximation_restrict {x₀ : F} {R : ℝ} (hR : 0 ≤ R)
    (hΩ : Ω ⊆ Metric.closedBall x₀ R) {U : Set F} (hUΩ : U ⊆ Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (f : Lp ℝ 2 (μ.restrict Ω)) (v : L2Pair μ Ω), c.IsWeakSolution f v → ‖f‖ < δ →
      ∃ h : L2Pair μ U, c.IsWeakSolution 0 h ∧ ‖restrictLp hUΩ v.fst - h.fst‖ < ε := by
  refine ⟨c.lam * ε / (4 * R ^ 2 + 1), by have := c.lam_pos; positivity, fun f v hv hf => ?_⟩
  obtain ⟨h, hh, hlt⟩ := harmonic_approximation hR hΩ hv hf
  refine ⟨L2Pair.restrict hUΩ h, ?_, ?_⟩
  · have := hh.restrict hUΩ
    rwa [map_zero] at this
  · rw [L2Pair.restrict_fst, ← map_sub]
    exact (norm_restrictLp_le hUΩ _).trans_lt hlt

end CoeffField

end General

/-! ### Compactness of approximate solutions -/

section Compactness

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

variable [NeZero d]

theorem norm_sq_eq_integral_real {Ω : Set 𝔼} (u : Lp ℝ 2 (volume.restrict Ω)) :
    ‖u‖ ^ 2 = ∫ x in Ω, u x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (Eventually.of_forall fun x => by simp [sq])

/-- `∫_Ω w u² ≤ C ‖u‖²` for a continuous weight `0 ≤ w ≤ C`. -/
theorem integral_weight_mul_sq_le {Ω : Set 𝔼} (u : Lp ℝ 2 (volume.restrict Ω)) {w : 𝔼 → ℝ}
    (hw : Continuous w) {C : ℝ} (hw0 : ∀ x, 0 ≤ w x) (hwC : ∀ x, w x ≤ C) :
    ∫ x in Ω, w x * u x ^ 2 ≤ C * ‖u‖ ^ 2 := by
  have hu := (Lp.memLp u).integrable_sq
  rw [norm_sq_eq_integral_real, ← integral_const_mul]
  refine integral_mono (hu.bdd_mul hw.aestronglyMeasurable (c := C) (Eventually.of_forall
    fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]; exact hwC x)) (hu.const_mul C)
    fun x => ?_
  exact mul_le_mul_of_nonneg_right (hwC x) (sq_nonneg _)

theorem integrable_weight_mul_inner {Ω : Set 𝔼} (c : CoeffField 𝔼 volume)
    (G : Lp 𝔼 2 (volume.restrict Ω)) {w : 𝔼 → ℝ} (hw : Continuous w) {C : ℝ}
    (hwC : ∀ x, |w x| ≤ C) :
    Integrable (fun x => w x * ⟪c.A x (G x), G x⟫_ℝ) (volume.restrict Ω) := by
  have hI : Integrable (fun x => ⟪c.A x (G x), G x⟫_ℝ) (volume.restrict Ω) :=
    (L2.integrable_inner (c.mulOp Ω G) G).congr (by
      filter_upwards [c.mulOp_ae Ω G] with x hx
      rw [hx])
  exact hI.bdd_mul hw.aestronglyMeasurable (c := C) (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hwC x)

/-- **Caccioppoli, gradient form:**
`λ ∫_Ω η² |∇u|² ≤ ∫_Ω η² f² + ∫_Ω (η² + 4Λ |∇η|²) u²`. -/
theorem caccioppoli_norm (c : CoeffField 𝔼 volume) {Ω : Set 𝔼} (hΩ : IsOpen Ω)
    {f : Lp ℝ 2 (volume.restrict Ω)} {v : L2Pair volume Ω} (hv : c.IsWeakSolution f v)
    {η : 𝔼 → ℝ} (hη : IsTestFn Ω η) :
    c.lam * ∫ x in Ω, η x ^ 2 * ‖v.snd x‖ ^ 2 ≤
      (∫ x in Ω, η x ^ 2 * f x ^ 2) +
        ∫ x in Ω, (η x ^ 2 + 4 * c.Λ * ‖gradient η x‖ ^ 2) * v.fst x ^ 2 := by
  obtain ⟨M, -, hM, -⟩ := exists_bound_testFn hη
  have hη2 : ∀ x, |η x ^ 2| ≤ M ^ 2 := fun x => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
  have hG2 : Integrable (fun x => ‖v.snd x‖ ^ 2) (volume.restrict Ω) :=
    (Lp.memLp v.snd).norm.integrable_sq
  refine le_trans ?_ (caccioppoli c hΩ hv hη)
  rw [← integral_const_mul]
  refine integral_mono_ae ((hG2.bdd_mul (hη.continuous.pow 2).aestronglyMeasurable (c := M ^ 2)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hη2 x)).const_mul _)
    (integrable_weight_mul_inner c v.snd (hη.continuous.pow 2) hη2) ?_
  filter_upwards [ae_restrict_of_ae c.coercive] with x hx
  have := hx (v.snd x)
  calc c.lam * (η x ^ 2 * ‖v.snd x‖ ^ 2) = η x ^ 2 * (c.lam * ‖v.snd x‖ ^ 2) := by ring
    _ ≤ η x ^ 2 * ⟪c.A x (v.snd x), v.snd x⟫_ℝ := by gcongr

/-- The first component of the cut-off pair: `‖η² u‖ ≤ ‖u‖` for `0 ≤ η ≤ 1`. -/
theorem norm_cutPair_fst_le {Ω : Set 𝔼} {η : 𝔼 → ℝ} (hη : IsTestFn Ω η)
    (h01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1) (v : L2Pair volume Ω) :
    ‖(cutPair hη v).fst‖ ≤ ‖v.fst‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [(memLp_cutFst (v := v) hη).coeFn_toLp] with x hx
  rw [cutPair_fst, hx, cutFst, norm_mul]
  have : ‖η x ^ 2‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [h01 x]
  calc ‖η x ^ 2‖ * ‖v.fst x‖ ≤ 1 * ‖v.fst x‖ := by gcongr
    _ = ‖v.fst x‖ := one_mul _

/-- The second component of the cut-off pair:
`‖η² G + 2 η u ∇η‖² ≤ 2 ∫ η² |G|² + 8 Γ² ‖u‖²` for `0 ≤ η ≤ 1`, `|∇η| ≤ Γ`. -/
theorem norm_cutPair_snd_sq_le {Ω : Set 𝔼} {η : 𝔼 → ℝ} (hη : IsTestFn Ω η)
    (h01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1) {Γ : ℝ} (hΓ : ∀ x, ‖gradient η x‖ ≤ Γ) (v : L2Pair volume Ω) :
    ‖(cutPair hη v).snd‖ ^ 2 ≤
      2 * (∫ x in Ω, η x ^ 2 * ‖v.snd x‖ ^ 2) + 8 * Γ ^ 2 * ‖v.fst‖ ^ 2 := by
  have hΓ0 : 0 ≤ Γ := (norm_nonneg _).trans (hΓ 0)
  have hG2 : Integrable (fun x => ‖v.snd x‖ ^ 2) (volume.restrict Ω) :=
    (Lp.memLp v.snd).norm.integrable_sq
  have hu2 : Integrable (fun x => v.fst x ^ 2) (volume.restrict Ω) :=
    (Lp.memLp v.fst).integrable_sq
  have I1 : Integrable (fun x => η x ^ 2 * ‖v.snd x‖ ^ 2) (volume.restrict Ω) :=
    hG2.bdd_mul (hη.continuous.pow 2).aestronglyMeasurable (c := 1) (Eventually.of_forall
      fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [h01 x])
  rw [cutPair_snd, CoeffField.norm_sq_eq_integral Ω, norm_sq_eq_integral_real, ← integral_const_mul,
    ← integral_const_mul, ← integral_add (I1.const_mul _) (hu2.const_mul _)]
  have hint : Integrable (fun x => ‖((memLp_cutSnd (v := v) hη).toLp (cutSnd v η)) x‖ ^ 2)
      (volume.restrict Ω) := (Lp.memLp _).norm.integrable_sq
  refine integral_mono_ae hint ((I1.const_mul _).add (hu2.const_mul _)) ?_
  filter_upwards [(memLp_cutSnd (v := v) hη).coeFn_toLp] with x hx
  rw [hx, cutSnd]
  have hηx := h01 x
  have hgx := hΓ x
  have h1 : ‖η x ^ 2 • v.snd x + (2 * η x * v.fst x) • gradient η x‖ ≤
      η x * ‖v.snd x‖ + 2 * Γ * |v.fst x| := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
    · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_two, abs_of_nonneg hηx.1]
      calc 2 * η x * |v.fst x| * ‖gradient η x‖ ≤ 2 * 1 * |v.fst x| * Γ :=
            mul_le_mul (mul_le_mul_of_nonneg_right (by linarith [hηx.2]) (abs_nonneg _)) hgx
              (norm_nonneg _) (by positivity)
        _ = 2 * Γ * |v.fst x| := by ring
  have h2 : (η x * ‖v.snd x‖ + 2 * Γ * |v.fst x|) ^ 2 ≤
      2 * (η x ^ 2 * ‖v.snd x‖ ^ 2) + 8 * Γ ^ 2 * v.fst x ^ 2 := by
    nlinarith [sq_nonneg (η x * ‖v.snd x‖ - 2 * Γ * |v.fst x|), sq_abs (v.fst x)]
  calc ‖η x ^ 2 • v.snd x + (2 * η x * v.fst x) • gradient η x‖ ^ 2
      ≤ (η x * ‖v.snd x‖ + 2 * Γ * |v.fst x|) ^ 2 := by gcongr
    _ ≤ _ := h2

/-- **A bound for the cut-off pair** of a weak solution, in terms of `‖u‖` and `‖f‖`. -/
theorem norm_cutPair_sq_le (c : CoeffField 𝔼 volume) {Ω : Set 𝔼} (hΩ : IsOpen Ω)
    {f : Lp ℝ 2 (volume.restrict Ω)} {v : L2Pair volume Ω} (hv : c.IsWeakSolution f v)
    {η : 𝔼 → ℝ} (hη : IsTestFn Ω η) (h01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1) {Γ : ℝ}
    (hΓ : ∀ x, ‖gradient η x‖ ≤ Γ) :
    ‖cutPair hη v‖ ^ 2 ≤
      ‖v.fst‖ ^ 2 + 2 / c.lam * (‖f‖ ^ 2 + (1 + 4 * c.Λ * Γ ^ 2) * ‖v.fst‖ ^ 2) +
        8 * Γ ^ 2 * ‖v.fst‖ ^ 2 := by
  have hl := c.lam_pos
  have hΛ := c.Λ_pos
  have hcac := caccioppoli_norm c hΩ hv hη
  have hf2 : ∫ x in Ω, η x ^ 2 * f x ^ 2 ≤ 1 * ‖f‖ ^ 2 :=
    integral_weight_mul_sq_le f (w := fun x => η x ^ 2) (hη.continuous.pow 2) (fun x => sq_nonneg _)
      fun x => by nlinarith [h01 x]
  have hu2 : ∫ x in Ω, (η x ^ 2 + 4 * c.Λ * ‖gradient η x‖ ^ 2) * v.fst x ^ 2 ≤
      (1 + 4 * c.Λ * Γ ^ 2) * ‖v.fst‖ ^ 2 :=
    integral_weight_mul_sq_le v.fst (w := fun x => η x ^ 2 + 4 * c.Λ * ‖gradient η x‖ ^ 2)
      ((hη.continuous.pow 2).add
      (continuous_const.mul (hη.continuous_gradient.norm.pow 2))) (fun x => by positivity)
      fun x => by
        have h1 : η x ^ 2 ≤ 1 := by nlinarith [h01 x]
        have h2 : ‖gradient η x‖ ^ 2 ≤ Γ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hΓ x) 2
        nlinarith
  have hint : ∫ x in Ω, η x ^ 2 * ‖v.snd x‖ ^ 2 ≤
      1 / c.lam * (‖f‖ ^ 2 + (1 + 4 * c.Λ * Γ ^ 2) * ‖v.fst‖ ^ 2) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hl, mul_comm]
    linarith
  have hfst := norm_cutPair_fst_le hη h01 v
  have hsnd := norm_cutPair_snd_sq_le hη h01 hΓ v
  rw [norm_sq_L2Pair]
  have : ‖(cutPair hη v).fst‖ ^ 2 ≤ ‖v.fst‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hfst 2
  have h2 : 2 / c.lam * (‖f‖ ^ 2 + (1 + 4 * c.Λ * Γ ^ 2) * ‖v.fst‖ ^ 2) =
      2 * (1 / c.lam * (‖f‖ ^ 2 + (1 + 4 * c.Λ * Γ ^ 2) * ‖v.fst‖ ^ 2)) := by ring
  rw [h2]
  linarith

/-- A sequence `x` is Cauchy if `dist(x_k, x_l)² ≤ C (dist(a_k, a_l)² + dist(b_k, b_l)²)` for
Cauchy sequences `a`, `b`. -/
theorem cauchySeq_of_sq_le {X A B : Type*} [PseudoMetricSpace X] [PseudoMetricSpace A]
    [PseudoMetricSpace B] {x : ℕ → X} {a : ℕ → A} {b : ℕ → B} (ha : CauchySeq a)
    (hb : CauchySeq b) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ k l, dist (x k) (x l) ^ 2 ≤ C * (dist (a k) (a l) ^ 2 + dist (b k) (b l) ^ 2)) :
    CauchySeq x := by
  rw [Metric.cauchySeq_iff] at ha hb ⊢
  intro ε hε
  set δ := ε / (2 * (C + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨N₁, hN₁⟩ := ha δ hδ0
  obtain ⟨N₂, hN₂⟩ := hb δ hδ0
  refine ⟨max N₁ N₂, fun m hm n hn => ?_⟩
  have h1 := hN₁ m (le_of_max_le_left hm) n (le_of_max_le_left hn)
  have h2 := hN₂ m (le_of_max_le_right hm) n (le_of_max_le_right hn)
  have h3 := h m n
  have hsq1 : dist (a m) (a n) ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ dist_nonneg h1.le 2
  have hsq2 : dist (b m) (b n) ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ dist_nonneg h2.le 2
  have hδε : C * (2 * δ ^ 2) < ε ^ 2 := by
    rw [hδ, div_pow, mul_pow]
    have hC1 : 0 < C + 1 := by linarith
    rw [show C * (2 * (ε ^ 2 / (2 ^ 2 * (C + 1) ^ 2))) = ε ^ 2 * (C / (2 * (C + 1) ^ 2)) by
      field_simp]
    have : C / (2 * (C + 1) ^ 2) < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith
    nlinarith [sq_pos_of_pos hε]
  have hlt : dist (x m) (x n) ^ 2 < ε ^ 2 := by
    calc dist (x m) (x n) ^ 2 ≤ C * (dist (a m) (a n) ^ 2 + dist (b m) (b n) ^ 2) := h3
      _ ≤ C * (2 * δ ^ 2) := by gcongr; linarith
      _ < ε ^ 2 := hδε
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt

/-- **Local energy of a difference of solutions.** Let `z = (u, ∇u)` solve `-div(A ∇u) = g` on
`Ω`, and let `η₂ = 1` on `U`, `η₁ = 1` on `supp η₂`. Then
`‖z|_U‖²_{W^{1,2}(U)} ≤ (1 + (1 + 4ΛΓ₂²)/λ) ‖η₁² u‖² + λ⁻¹ ‖g‖²`. -/
theorem norm_restrict_sq_le_of_cutoff (c : CoeffField 𝔼 volume) {Ω U : Set 𝔼} (hΩ : IsOpen Ω)
    (hU : IsOpen U) (hUΩ : U ⊆ Ω) {η₁ η₂ : 𝔼 → ℝ} (hη₂ : IsTestFn Ω η₂)
    (h01₂ : ∀ x, 0 ≤ η₂ x ∧ η₂ x ≤ 1) (hone₂ : ∀ x ∈ U, η₂ x = 1)
    (hone₁ : ∀ x ∈ tsupport η₂, η₁ x = 1) {Γ₂ : ℝ} (hΓ₂ : ∀ x, ‖gradient η₂ x‖ ≤ Γ₂)
    {g : Lp ℝ 2 (volume.restrict Ω)} {z : L2Pair volume Ω} (hz : c.IsWeakSolution g z)
    {W : Lp ℝ 2 (volume.restrict Ω)} (hWz : W =ᵐ[volume.restrict Ω] fun y => η₁ y ^ 2 * z.fst y) :
    ‖L2Pair.restrict hUΩ z‖ ^ 2 ≤
      (1 + (1 + 4 * c.Λ * Γ₂ ^ 2) / c.lam) * ‖W‖ ^ 2 + 1 / c.lam * ‖g‖ ^ 2 := by
  have hl := c.lam_pos
  have hΛ := c.Λ_pos
  have hUsupp : ∀ y ∈ U, y ∈ tsupport η₂ := fun y hy =>
    subset_tsupport _ (by rw [Function.mem_support, hone₂ y hy]; norm_num)
  have hC₂ : 0 ≤ 1 + 4 * c.Λ * Γ₂ ^ 2 := by positivity
  have hW : ‖W‖ ^ 2 = ∫ y in Ω, (η₁ y ^ 2 * z.fst y) ^ 2 := by
    rw [norm_sq_eq_integral_real]
    exact integral_congr_ae (by filter_upwards [hWz] with y hy; rw [hy])
  have hIW : Integrable (fun y => (η₁ y ^ 2 * z.fst y) ^ 2) (volume.restrict Ω) :=
    (Lp.memLp W).integrable_sq.congr (by filter_upwards [hWz] with y hy; rw [hy])
  have hη2 : ∀ y, η₂ y ^ 2 ≤ 1 := fun y => by nlinarith [h01₂ y]
  have hg2 : ∀ y, ‖gradient η₂ y‖ ^ 2 ≤ Γ₂ ^ 2 := fun y =>
    pow_le_pow_left₀ (norm_nonneg _) (hΓ₂ y) 2
  -- Caccioppoli
  have hcac := caccioppoli_norm c hΩ hz hη₂
  have hfz : ∫ y in Ω, η₂ y ^ 2 * g y ^ 2 ≤ 1 * ‖g‖ ^ 2 :=
    integral_weight_mul_sq_le g (w := fun y => η₂ y ^ 2) (hη₂.continuous.pow 2)
      (fun y => sq_nonneg _) hη2
  have hcont : Continuous fun y => η₂ y ^ 2 + 4 * c.Λ * ‖gradient η₂ y‖ ^ 2 :=
    (hη₂.continuous.pow 2).add (continuous_const.mul (hη₂.continuous_gradient.norm.pow 2))
  have hu2 : ∫ y in Ω, (η₂ y ^ 2 + 4 * c.Λ * ‖gradient η₂ y‖ ^ 2) * z.fst y ^ 2 ≤
      (1 + 4 * c.Λ * Γ₂ ^ 2) * ‖W‖ ^ 2 := by
    rw [hW, ← integral_const_mul]
    have hI2 : Integrable (fun y => (η₂ y ^ 2 + 4 * c.Λ * ‖gradient η₂ y‖ ^ 2) * z.fst y ^ 2)
        (volume.restrict Ω) :=
      (Lp.memLp z.fst).integrable_sq.bdd_mul (c := 1 + 4 * c.Λ * Γ₂ ^ 2)
        hcont.aestronglyMeasurable (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          nlinarith [hη2 y, hg2 y])
    refine integral_mono hI2 (hIW.const_mul _) fun y => ?_
    by_cases hy : y ∈ tsupport η₂
    · rw [hone₁ y hy, one_pow, one_mul]
      exact mul_le_mul_of_nonneg_right (by nlinarith [hη2 y, hg2 y]) (sq_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hy, gradient_eq_zero_of_notMem_tsupport hy]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, norm_zero, mul_zero,
        add_zero, zero_mul]
      positivity
  have hgrad : ∫ y in Ω, η₂ y ^ 2 * ‖z.snd y‖ ^ 2 ≤
      1 / c.lam * (‖g‖ ^ 2 + (1 + 4 * c.Λ * Γ₂ ^ 2) * ‖W‖ ^ 2) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hl, mul_comm]
    linarith
  -- the gradient part on `U`
  have hint : Integrable (fun y => η₂ y ^ 2 * ‖z.snd y‖ ^ 2) (volume.restrict Ω) :=
    (Lp.memLp z.snd).norm.integrable_sq.bdd_mul (hη₂.continuous.pow 2).aestronglyMeasurable
      (c := 1) (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hη2 y)
  have hsnd : ‖(L2Pair.restrict hUΩ z).snd‖ ^ 2 ≤ ∫ y in Ω, η₂ y ^ 2 * ‖z.snd y‖ ^ 2 := by
    rw [L2Pair.restrict_snd, CoeffField.norm_sq_eq_integral U]
    have hae : ∀ᵐ y ∂(volume.restrict U), ‖restrictLp hUΩ z.snd y‖ ^ 2 = ‖z.snd y‖ ^ 2 := by
      filter_upwards [restrictLp_ae hUΩ z.snd] with y hy
      rw [hy]
    rw [integral_congr_ae hae]
    calc ∫ y in U, ‖z.snd y‖ ^ 2 = ∫ y in U, η₂ y ^ 2 * ‖z.snd y‖ ^ 2 :=
          setIntegral_congr_fun hU.measurableSet fun y hy => by
            simp only [hone₂ y hy, one_pow, one_mul]
      _ ≤ ∫ y in Ω, η₂ y ^ 2 * ‖z.snd y‖ ^ 2 :=
          setIntegral_mono_set hint (Eventually.of_forall fun y => by positivity)
            hUΩ.eventuallyLE
  -- the function part on `U`
  have hfst : ‖(L2Pair.restrict hUΩ z).fst‖ ^ 2 ≤ ‖W‖ ^ 2 := by
    rw [L2Pair.restrict_fst, norm_sq_eq_integral_real, hW]
    have hae : ∀ᵐ y ∂(volume.restrict U), restrictLp hUΩ z.fst y ^ 2 = z.fst y ^ 2 := by
      filter_upwards [restrictLp_ae hUΩ z.fst] with y hy
      rw [hy]
    rw [integral_congr_ae hae]
    calc ∫ y in U, z.fst y ^ 2 = ∫ y in U, (η₁ y ^ 2 * z.fst y) ^ 2 :=
          setIntegral_congr_fun hU.measurableSet fun y hy => by
            simp only [hone₁ y (hUsupp y hy), one_pow, one_mul]
      _ ≤ ∫ y in Ω, (η₁ y ^ 2 * z.fst y) ^ 2 :=
          setIntegral_mono_set hIW (Eventually.of_forall fun y => by positivity)
            hUΩ.eventuallyLE
  rw [norm_sq_L2Pair]
  have e1 : 1 / c.lam * (‖g‖ ^ 2 + (1 + 4 * c.Λ * Γ₂ ^ 2) * ‖W‖ ^ 2) =
      (1 + 4 * c.Λ * Γ₂ ^ 2) / c.lam * ‖W‖ ^ 2 + 1 / c.lam * ‖g‖ ^ 2 := by ring
  rw [e1] at hgrad
  nlinarith

/-- **Compactness of approximate solutions.** Let `Ω ⊆ ℝ^d` be bounded and open, and let `U` be
open with compact closure `closure U ⊆ Ω`. Let `v_n = (u_n, ∇u_n)` be weak solutions of
`-div(A ∇u_n) = f_n` on `Ω` with `‖u_n‖_{L²(Ω)} ≤ M` and `f_n → f` in `L²(Ω)`. Then a subsequence
of `v_n|_U` converges in `W^{1,2}(U)` (function **and** gradient in `L²(U)`) to a weak solution of
`-div(A ∇u) = f` on `U`. -/
theorem exists_tendsto_of_approx_solutions (c : CoeffField 𝔼 volume) {Ω U : Set 𝔼}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) {f : ℕ → Lp ℝ 2 (volume.restrict Ω)} {v : ℕ → L2Pair volume Ω}
    (hv : ∀ n, c.IsWeakSolution (f n) (v n)) {M : ℝ} (hM : ∀ n, ‖(v n).fst‖ ≤ M)
    {f₀ : Lp ℝ 2 (volume.restrict Ω)} (hf : Tendsto f atTop (𝓝 f₀)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : L2Pair volume U,
      c.IsWeakSolution (restrictLp (subset_closure.trans hUΩ) f₀) w ∧
      Tendsto (fun k => L2Pair.restrict (subset_closure.trans hUΩ) (v (φ k))) atTop (𝓝 w) := by
  have hUΩ' : U ⊆ Ω := subset_closure.trans hUΩ
  have hl := c.lam_pos
  have hΛ := c.Λ_pos
  -- the cut-off functions: `η₂ = 1` on `U`, `η₁ = 1` on `supp η₂`
  obtain ⟨η₂, hη₂, h01₂, hone₂⟩ := exists_cutoff hUc hΩ hUΩ
  obtain ⟨η₁, hη₁, h01₁, hone₁⟩ := exists_cutoff hη₂.hasCompactSupport.isCompact hΩ
    hη₂.tsupport_subset
  obtain ⟨Γ₁, hΓ₁0, -, hΓ₁⟩ := exists_bound_testFn hη₁
  obtain ⟨Γ₂, hΓ₂0, -, hΓ₂⟩ := exists_bound_testFn hη₂
  -- bounds on the data
  obtain ⟨Mf, hMf⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto f hf)
  have hMf' : ∀ n, ‖f n‖ ≤ Mf := fun n => hMf _ (Set.mem_range_self n)
  -- the cut-off pairs `η₁² u_n` are bounded in `W^{1,2}_0(Ω)`
  have hwH : ∀ n, cutPair hη₁ (v n) ∈ H01 volume Ω := fun n => cutPair_mem_H01 hΩ (hv n).1 hη₁
  have hwB : ∀ n, ‖cutPair hη₁ (v n)‖ ≤
      √(M ^ 2 + 2 / c.lam * (Mf ^ 2 + (1 + 4 * c.Λ * Γ₁ ^ 2) * M ^ 2) + 8 * Γ₁ ^ 2 * M ^ 2) :=
    fun n => by
      refine Real.le_sqrt_of_sq_le ((norm_cutPair_sq_le c hΩ (hv n) hη₁ h01₁ hΓ₁).trans ?_)
      have h1 : ‖(v n).fst‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM n) 2
      have h2 : ‖f n‖ ^ 2 ≤ Mf ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hMf' n) 2
      have h3 : 0 ≤ 1 + 4 * c.Λ * Γ₁ ^ 2 := by positivity
      have h4 : 0 ≤ 2 / c.lam := by positivity
      gcongr
  -- Rellich
  obtain ⟨φ, hφ, g, hg⟩ := rellich_H01 hΩ hb hwH hwB
  -- the restricted subsequence is Cauchy in `W^{1,2}(U)`
  have hkey : ∀ k l, dist (L2Pair.restrict hUΩ' (v (φ k))) (L2Pair.restrict hUΩ' (v (φ l))) ^ 2 ≤
      (1 + (1 + 4 * c.Λ * Γ₂ ^ 2) / c.lam + 1 / c.lam) *
        (dist ((cutPair hη₁ (v (φ k))).fst) ((cutPair hη₁ (v (φ l))).fst) ^ 2 +
          dist (f (φ k)) (f (φ l)) ^ 2) := by
    intro k l
    have hcut : (cutPair hη₁ (v (φ k))).fst - (cutPair hη₁ (v (φ l))).fst =ᵐ[volume.restrict Ω]
        fun y => η₁ y ^ 2 * (v (φ k) - v (φ l)).fst y := by
      filter_upwards [Lp.coeFn_sub (cutPair hη₁ (v (φ k))).fst (cutPair hη₁ (v (φ l))).fst,
        (memLp_cutFst (v := v (φ k)) hη₁).coeFn_toLp,
        (memLp_cutFst (v := v (φ l)) hη₁).coeFn_toLp,
        Lp.coeFn_sub (v (φ k)).fst (v (φ l)).fst] with y h1 h2 h3 h4
      rw [h1, Pi.sub_apply, cutPair_fst, cutPair_fst, h2, h3, cutFst, cutFst,
        WithLp.sub_fst, h4, Pi.sub_apply]
      ring
    have h := norm_restrict_sq_le_of_cutoff c hΩ hU hUΩ' hη₂ h01₂
      (fun y hy => hone₂ y (subset_closure hy)) hone₁ hΓ₂ ((hv (φ k)).sub (hv (φ l))) hcut
    rw [map_sub] at h
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
    have hC : 0 ≤ (1 + 4 * c.Λ * Γ₂ ^ 2) / c.lam := by positivity
    have hil : 0 ≤ 1 / c.lam := by positivity
    nlinarith [sq_nonneg ‖(cutPair hη₁ (v (φ k))).fst - (cutPair hη₁ (v (φ l))).fst‖,
      sq_nonneg ‖f (φ k) - f (φ l)‖]
  have hcauchy : CauchySeq fun k => L2Pair.restrict hUΩ' (v (φ k)) :=
    cauchySeq_of_sq_le (hg.cauchySeq) ((hf.comp hφ.tendsto_atTop).cauchySeq)
      (by positivity) hkey
  obtain ⟨w₀, hw₀⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨φ, hφ, w₀, ⟨?_, fun ψ hψ => ?_⟩, hw₀⟩
  · exact (isClosed_W12 U).mem_of_tendsto hw₀
      (Eventually.of_forall fun k => restrict_mem_W12 hUΩ' (hv (φ k)).1)
  · have hsol : ∀ k, c.dirichletForm U (L2Pair.restrict hUΩ' (v (φ k))) (graph volume U hψ) =
        ⟪restrictLp hUΩ' (f (φ k)), (graph volume U hψ).fst⟫_ℝ := fun k =>
      ((hv (φ k)).restrict hUΩ').2 ψ hψ
    have hL : Tendsto (fun k => c.dirichletForm U (L2Pair.restrict hUΩ' (v (φ k)))
        (graph volume U hψ)) atTop (𝓝 (c.dirichletForm U w₀ (graph volume U hψ))) :=
      (((c.dirichletForm U).flip (graph volume U hψ)).continuous.tendsto w₀).comp hw₀
    have hR : Tendsto (fun k => ⟪restrictLp hUΩ' (f (φ k)), (graph volume U hψ).fst⟫_ℝ) atTop
        (𝓝 ⟪restrictLp hUΩ' f₀, (graph volume U hψ).fst⟫_ℝ) :=
      ((((restrictLp hUΩ').continuous.tendsto f₀).comp (hf.comp hφ.tendsto_atTop)).inner
        tendsto_const_nhds)
    simp_rw [hsol] at hL
    exact tendsto_nhds_unique hL hR

/-- **Lemma 2.4 by the paper's compactness argument.** Let `Ω` be bounded and open, and let `U` be
open with compact closure in `Ω`. For every `ε > 0` there is `δ > 0` such that every weak
solution of `-div(A ∇u) = f` on `Ω` with `‖u‖_{L²(Ω)} ≤ 1` and `‖f‖_{L²(Ω)} < δ` is `ε`-close in
`L²(U)` to a weakly `A`-harmonic function on `U`. (The direct proof `harmonic_approximation`
gives more: an explicit `δ`, and no bound on `u`.) -/
theorem harmonic_approximation_of_compactness (c : CoeffField 𝔼 volume) {Ω U : Set 𝔼}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (f : Lp ℝ 2 (volume.restrict Ω)) (v : L2Pair volume Ω), c.IsWeakSolution f v →
      ‖v.fst‖ ≤ 1 → ‖f‖ < δ → ∃ h : L2Pair volume U, c.IsWeakSolution 0 h ∧
        ‖restrictLp (subset_closure.trans hUΩ) v.fst - h.fst‖ < ε := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ f : Lp ℝ 2 (volume.restrict Ω), ∃ v : L2Pair volume Ω,
      c.IsWeakSolution f v ∧ ‖v.fst‖ ≤ 1 ∧ ‖f‖ < 1 / (n + 1) ∧
        ∀ h : L2Pair volume U, c.IsWeakSolution 0 h →
          ε ≤ ‖restrictLp (subset_closure.trans hUΩ) v.fst - h.fst‖ := fun n =>
    hcon (1 / (n + 1)) Nat.one_div_pos_of_nat
  choose f v hv hv1 hf hfar using hseq
  have hf0 : Tendsto f atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hf n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, -, w, hw, hlim⟩ := exists_tendsto_of_approx_solutions c hΩ hb hU hUc hUΩ hv hv1 hf0
  rw [map_zero] at hw
  have hfst : Tendsto (fun k => restrictLp (subset_closure.trans hUΩ) (v (φ k)).fst) atTop
      (𝓝 w.fst) :=
    ((WithLp.fstL 2 ℝ (Lp ℝ 2 (volume.restrict U)) (Lp 𝔼 2 (volume.restrict U))).continuous.tendsto
      w).comp hlim
  have hsmall := (tendsto_iff_norm_sub_tendsto_zero.mp hfst).eventually (gt_mem_nhds hε)
  obtain ⟨k, hk⟩ := hsmall.exists
  exact absurd (hfar (φ k) w hw) (not_le.mpr hk)

end Compactness

end ConicalKahler.Sobolev
