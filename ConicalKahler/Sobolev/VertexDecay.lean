module

public import ConicalKahler.Sobolev.Completeness

/-!
# Decay at the vertex (Lemma 4.2 and the projection onto `𝓗_{≤2}`)

**Monotonicity at the vertex** (paper, Lemma 4.2). Let `c` be a conical coefficient field and
`d ≥ 2`. Let `u ∈ W^{1,2}(B_1)` be weakly harmonic and `L²(B_1)`-orthogonal to every homogeneous
harmonic function `ρ^{δ'} ψ` of degree `δ' < D` (link eigenfunction `ψ`). Then, for
`0 < ρ₁ ≤ ρ₂ ≤ 1`,

  `∫_{B_{ρ₁}} u² ≤ (ρ₁/ρ₂)^{2D + d} ∫_{B_{ρ₂}} u²`        (`vertex_monotone`),

i.e. `‖u‖_{B_{ρ₁}} ≤ (ρ₁/ρ₂)^D ‖u‖_{B_{ρ₂}}` for the scaled norms `‖u‖_{B_ρ} = (ρ^{-d} ∫_{B_ρ} u²)^{1/2}`.
The proof uses the ray coefficients of Lemma 3.3: `u_{φ_i}(r) = C_i r^{δ_i}`, `C_i = 0` for
`δ_i < D`, and `∫_{B_ρ} u² = ∑_i C_i² ρ^{2δ_i + d}/(2δ_i + d)` (Parseval on spheres).

**For the cone** (`0 < β_a < 1`, `μ` as in eq. (1.1)), Proposition 3.4 identifies the homogeneous
harmonic functions of degree `< 2 + μ` with `𝓗_{≤2}` (`explicitH2`). Hence
(`cone_vertex_monotone`) a weakly harmonic `u` that is `L²(B_1)`-orthogonal to `𝓗_{≤2}` satisfies
`‖u‖_{B_{ρ₁}} ≤ (ρ₁/ρ₂)^{2+μ} ‖u‖_{B_{ρ₂}}`. Every weakly harmonic `h` splits as `h = P + (h − P)`
with `P` the `L²(B_1)`-orthogonal projection onto `𝓗_{≤2}` (`cone_vertex_decay`), so

  `‖h − P‖_{B_ρ} ≤ ρ^{2+μ} ‖h − P‖_{B_1} ≤ ρ^{2+μ} ‖h‖_{B_1}`.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set Metric
open scoped ContDiff ENNReal

namespace ConicalKahler.Sobolev

variable {d : ℕ} [NeZero d]

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### Parseval on balls of any radius -/

theorem ballR_ae_eq_shell (R : ℝ) :
    (ball (0 : 𝔼) R : Set 𝔼) =ᵐ[volume] shell d 0 R := by
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null (fun x hx => ?_) (measure_singleton (0 : 𝔼))
    by_contra h0
    exact hx.2 ⟨norm_pos_iff.mpr h0, mem_ball_zero_iff.mp hx.1⟩
  · refine measure_mono_null (fun x hx => ?_) (measure_empty (μ := (volume : Measure 𝔼)))
    exact hx.2 (mem_ball_zero_iff.mpr hx.1.2)

theorem restrict_ballR_eq_shell (R : ℝ) :
    (volume.restrict (ball (0 : 𝔼) R)) = volume.restrict (shell d 0 R) :=
  Measure.restrict_congr_set (ballR_ae_eq_shell R)

/-- **`L²(B_R)` norms in terms of ray coefficients** (Parseval on each sphere). -/
theorem lintegral_ballR_eq_tsum {ι : Type*} [Countable ι]
    (B : HilbertBasis ι ℝ (Lp ℝ 2 (sphMeasure d))) {f : 𝔼 → ℝ} (hf : StronglyMeasurable f)
    {R : ℝ} (hf2 : ∫⁻ x in ball (0 : 𝔼) R, ‖f x‖ₑ ^ 2 < ⊤) :
    ∫⁻ x in ball (0 : 𝔼) R, ‖f x‖ₑ ^ 2 =
      ∑' i, ∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal (r ^ (d - 1)) *
        ENNReal.ofReal (rayCoeff f (fun w => B i w) r ^ 2) := by
  have hmeasG : Measurable fun r : ℝ => ∫⁻ w, ‖f (r • (w : 𝔼))‖ₑ ^ 2 ∂(sphMeasure d) :=
    Measurable.lintegral_prod_right (f := fun r (w : Sph d) => ‖f (r • (w : 𝔼))‖ₑ ^ 2)
      ((hf.measurable.comp (measurable_fst.smul (measurable_subtype_coe.comp
        measurable_snd))).enorm.pow_const 2)
  rw [restrict_ballR_eq_shell R, lintegral_shell_polar (hf.measurable.enorm.pow_const 2) le_rfl]
    at hf2 ⊢
  have hfin : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      ∫⁻ w, ‖f (r • (w : 𝔼))‖ₑ ^ 2 ∂(sphMeasure d) < ⊤ := by
    filter_upwards [ae_lt_top ((by fun_prop : Measurable fun r : ℝ =>
      ENNReal.ofReal (r ^ (d - 1))).mul hmeasG) hf2.ne,
      ae_restrict_mem measurableSet_Ioo] with r hr hr01
    have hpos : ENNReal.ofReal (r ^ (d - 1)) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact pow_pos hr01.1 _
    rcases ENNReal.mul_lt_top_iff.mp hr with h | h | h
    · exact h.2
    · exact (hpos h).elim
    · simp only at h
      rw [h]
      exact ENNReal.zero_lt_top
  have hT := lintegral_tsum (μ := volume.restrict (Ioo (0 : ℝ) R))
    (f := fun i r => ENNReal.ofReal (r ^ (d - 1)) *
      ENNReal.ofReal (rayCoeff f (fun w => B i w) r ^ 2)) fun i =>
      ((by fun_prop : Measurable fun r : ℝ => ENNReal.ofReal (r ^ (d - 1))).mul
        (ENNReal.measurable_ofReal.comp
          ((stronglyMeasurable_rayCoeff hf (Lp.stronglyMeasurable (B i))).measurable.pow_const
            2))).aemeasurable
  rw [← hT]
  refine lintegral_congr_ae ?_
  filter_upwards [hfin] with r hr
  rw [ENNReal.tsum_mul_left, lintegral_slice_eq_tsum B hf hr]

theorem integral_Ioo_rpow' {p ρ : ℝ} (hp : -1 < p) (hρ : 0 ≤ ρ) :
    ∫ r in Ioo (0 : ℝ) ρ, r ^ p = ρ ^ (p + 1) / (p + 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ,
    integral_rpow (Or.inl hp), Real.zero_rpow (by linarith), sub_zero]

/-- `∫_0^ρ r^{d-1} (a r^δ)² dr = a² ρ^{2δ + d}/(2δ + d)` for `ρ ≤ 1`, if `f = a r^δ` a.e. on
`(0, 1)`. -/
theorem lintegral_Ioo_sq_of_ae_eq_rpow {f : ℝ → ℝ} {a δ ρ : ℝ} (hδ : 0 ≤ δ) (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hf : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)), f r = a * r ^ δ) :
    ∫⁻ r in Ioo (0 : ℝ) ρ, ENNReal.ofReal (r ^ (d - 1)) * ENNReal.ofReal (f r ^ 2) =
      ENNReal.ofReal (a ^ 2 * ρ ^ (2 * δ + d) / (2 * δ + d)) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hp : -1 < 2 * δ + d - 1 := by linarith
  have hsub : Ioo (0 : ℝ) ρ ⊆ Ioo 0 1 := Ioo_subset_Ioo_right hρ1
  have hf' : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) ρ)), f r = a * r ^ δ :=
    ae_restrict_of_ae_restrict_of_subset hsub hf
  have hint : IntegrableOn (fun r : ℝ => a ^ 2 * r ^ (2 * δ + d - 1)) (Ioo 0 ρ) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ρ)
      (r := 2 * δ + d - 1) hp).1
    exact (this.mono_set Ioo_subset_Ioc_self).const_mul _
  calc ∫⁻ r in Ioo (0 : ℝ) ρ, ENNReal.ofReal (r ^ (d - 1)) * ENNReal.ofReal (f r ^ 2)
      = ∫⁻ r in Ioo (0 : ℝ) ρ, ENNReal.ofReal (a ^ 2 * r ^ (2 * δ + d - 1)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hf', ae_restrict_mem measurableSet_Ioo] with r hr hr01
        have hr0 : 0 < r := hr01.1
        have h1 : r ^ (d - 1) = r ^ ((d : ℝ) - 1) := (rpow_sub_one_eq_pow).symm
        have h2 : (r ^ δ) ^ 2 = r ^ (2 * δ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
          ring_nf
        have h3 : r ^ ((d : ℝ) - 1) * r ^ (2 * δ) = r ^ (2 * δ + d - 1) := by
          rw [← Real.rpow_add hr0]
          ring_nf
        have hreal : r ^ (d - 1) * (a * r ^ δ) ^ 2 = a ^ 2 * r ^ (2 * δ + d - 1) := by
          rw [mul_pow, h1, h2, ← h3]
          ring
        rw [hr, ← ENNReal.ofReal_mul (pow_nonneg hr0.le _), hreal]
    _ = ENNReal.ofReal (a ^ 2 * ρ ^ (2 * δ + d) / (2 * δ + d)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint (by
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
          exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hr.1.le _)),
          integral_const_mul, integral_Ioo_rpow' hp hρ0.le]
        congr 1
        rw [show 2 * δ + d - 1 + 1 = 2 * δ + d by ring]
        ring

theorem enorm_sq_eq_ofReal (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- The real integral of `f²` over a set is the `toReal` of the lintegral of `‖f‖ₑ²`. -/
theorem setIntegral_sq_eq_toReal {S : Set 𝔼} {f : 𝔼 → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict S)) :
    ∫ x in S, f x ^ 2 = (∫⁻ x in S, ‖f x‖ₑ ^ 2).toReal := by
  simp_rw [enorm_sq_eq_ofReal]
  exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
    (hf.pow 2)

/-! ### Lemma 4.2: monotonicity at the vertex -/

section Monotone

variable {c : CoeffField (EuclideanSpace ℝ (Fin d)) volume}

/-- **Lemma 4.2 (monotonicity at the vertex)**, two-radii form. If `u ∈ W^{1,2}(B_1)` is weakly
harmonic for a conical field and `L²(B_1)`-orthogonal to every homogeneous harmonic function
`ρ^{δ'} ψ` of degree `δ' < D`, then `∫_{B_{ρ₁}} u² ≤ (ρ₁/ρ₂)^{2D + d} ∫_{B_{ρ₂}} u²` for
`0 < ρ₁ ≤ ρ₂ ≤ 1`. -/
theorem vertex_monotone_lintegral (hd : 2 ≤ d) (hc : c.IsConical)
    {u : L2Pair volume (ball (0 : 𝔼) 1)} (hu : c.IsWeakSolution 0 u) {D : ℝ}
    (horth : ∀ (lam δ' : ℝ) (v : LinkPair d), IsLinkEigen hc lam v → lam = δ' * (δ' + d - 2) →
      0 ≤ δ' → δ' < D → ∫ x in ball (0 : 𝔼) 1, u.fst x * homP δ' v x = 0)
    {ρ₁ ρ₂ : ℝ} (h1 : 0 < ρ₁) (h12 : ρ₁ ≤ ρ₂) (h2 : ρ₂ ≤ 1) :
    ∫⁻ x in ball (0 : 𝔼) ρ₁, ‖u.fst x‖ₑ ^ 2 ≤
      ENNReal.ofReal ((ρ₁ / ρ₂) ^ (2 * D + d)) * ∫⁻ x in ball (0 : 𝔼) ρ₂, ‖u.fst x‖ₑ ^ 2 := by
  classical
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  obtain ⟨s, B, Γ, lam, hB, heig, -⟩ := link_spectral hc
  have := separableSpace_sph (d := d)
  have hcount : Countable s :=
    Orthonormal.countable_of_separable
      (hB ▸ B.orthonormal : Orthonormal ℝ (Subtype.val : s → Lp ℝ 2 (sphMeasure d)))
  set v : s → LinkPair d := fun i => WithLp.toLp 2 ((i : Lp ℝ 2 (sphMeasure d)), Γ i)
  set δ : s → ℝ := fun i => indicialRoot d (lam i)
  have hδ0 : ∀ i, 0 ≤ δ i := fun i => indicialRoot_nonneg hd (heig i).1
  have hroot : ∀ i, lam i = δ i * (δ i + d - 2) := fun i => indicialRoot_spec _ (heig i).1
  have hP : ∀ i, MemLp (homP (δ i) (v i)) 2 (volume.restrict (ball (0 : 𝔼) 1)) := fun i =>
    memLp_homFun_ball (δ i) (Lp.memLp (v i).fst) 1 (by linarith [hδ0 i])
  have hG : ∀ i, MemLp (homG (δ i) (v i)) 2 (volume.restrict (ball (0 : 𝔼) 1)) := fun i =>
    memLp_homG_of_isLinkEigen hd (heig i).2 (hroot i) (hδ0 i)
  choose C hC using fun i => rayCoeff_eq hd hc (heig i).2 (hroot i) (hP i) (hG i) hu
  -- the coefficients of degree `< D` vanish
  have hzero : ∀ i, δ i < D → C i = 0 := by
    intro i hi
    have h := integral_ball_mul_homP_of_rayCoeff (Lp.memLp u.fst) (hδ0 i) (v i) (hC i)
    rw [horth _ _ _ (heig i).2 (hroot i) (hδ0 i) hi, eq_comm,
      div_eq_zero_iff] at h
    rcases h with h | h
    · exact h
    · exact absurd h (by linarith [hδ0 i])
  -- `∫_{B_ρ} u² = ∑_i C_i² ρ^{2δ_i + d}/(2δ_i + d)`
  have hfinB : ∀ ρ, ρ ≤ 1 → ∫⁻ x in ball (0 : 𝔼) ρ, ‖u.fst x‖ₑ ^ 2 < ⊤ := fun ρ hρ =>
    lt_of_le_of_lt (lintegral_mono_set (ball_subset_ball hρ)) (lintegral_sq_lt_top u.fst)
  have hball : ∀ ρ, 0 < ρ → ρ ≤ 1 → ∫⁻ x in ball (0 : 𝔼) ρ, ‖u.fst x‖ₑ ^ 2 =
      ∑' i, ENNReal.ofReal (C i ^ 2 * ρ ^ (2 * δ i + d) / (2 * δ i + d)) := by
    intro ρ hρ0 hρ1
    rw [lintegral_ballR_eq_tsum B (Lp.stronglyMeasurable u.fst) (hfinB ρ hρ1), hB]
    exact tsum_congr fun i => lintegral_Ioo_sq_of_ae_eq_rpow (hδ0 i) hρ0 hρ1 (hC i)
  have hρ2 : 0 < ρ₂ := h1.trans_le h12
  rw [hball ρ₁ h1 (h12.trans h2), hball ρ₂ hρ2 h2, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (div_nonneg h1.le hρ2.le) _)]
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hi : δ i < D
  · rw [hzero i hi]
    simp
  · have hden : 0 < 2 * δ i + d := by linarith [hδ0 i]
    have hq : 0 < ρ₁ / ρ₂ := div_pos h1 hρ2
    have hq1 : ρ₁ / ρ₂ ≤ 1 := (div_le_one hρ2).mpr h12
    have hsplit : ρ₁ ^ (2 * δ i + d) = (ρ₁ / ρ₂) ^ (2 * δ i + d) * ρ₂ ^ (2 * δ i + d) := by
      rw [← Real.mul_rpow hq.le hρ2.le, div_mul_cancel₀ _ hρ2.ne']
    have hmono : (ρ₁ / ρ₂) ^ (2 * δ i + d) ≤ (ρ₁ / ρ₂) ^ (2 * D + d) :=
      Real.rpow_le_rpow_of_exponent_ge hq hq1 (by linarith [not_lt.mp hi])
    have hX : 0 ≤ C i ^ 2 * ρ₂ ^ (2 * δ i + d) / (2 * δ i + d) :=
      div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hρ2.le _)) hden.le
    rw [hsplit]
    calc C i ^ 2 * ((ρ₁ / ρ₂) ^ (2 * δ i + d) * ρ₂ ^ (2 * δ i + d)) / (2 * δ i + d)
        = (ρ₁ / ρ₂) ^ (2 * δ i + d) * (C i ^ 2 * ρ₂ ^ (2 * δ i + d) / (2 * δ i + d)) := by ring
      _ ≤ (ρ₁ / ρ₂) ^ (2 * D + d) * (C i ^ 2 * ρ₂ ^ (2 * δ i + d) / (2 * δ i + d)) :=
        mul_le_mul_of_nonneg_right hmono hX

/-- **Lemma 4.2 (monotonicity at the vertex)**, with real integrals:
`∫_{B_{ρ₁}} u² ≤ (ρ₁/ρ₂)^{2D + d} ∫_{B_{ρ₂}} u²`. -/
theorem vertex_monotone (hd : 2 ≤ d) (hc : c.IsConical)
    {u : L2Pair volume (ball (0 : 𝔼) 1)} (hu : c.IsWeakSolution 0 u) {D : ℝ}
    (horth : ∀ (lam δ' : ℝ) (v : LinkPair d), IsLinkEigen hc lam v → lam = δ' * (δ' + d - 2) →
      0 ≤ δ' → δ' < D → ∫ x in ball (0 : 𝔼) 1, u.fst x * homP δ' v x = 0)
    {ρ₁ ρ₂ : ℝ} (h1 : 0 < ρ₁) (h12 : ρ₁ ≤ ρ₂) (h2 : ρ₂ ≤ 1) :
    ∫ x in ball (0 : 𝔼) ρ₁, u.fst x ^ 2 ≤
      (ρ₁ / ρ₂) ^ (2 * D + d) * ∫ x in ball (0 : 𝔼) ρ₂, u.fst x ^ 2 := by
  have hm : ∀ ρ, AEStronglyMeasurable (u.fst : 𝔼 → ℝ) (volume.restrict (ball (0 : 𝔼) ρ)) :=
    fun ρ => (Lp.stronglyMeasurable u.fst).aestronglyMeasurable
  have hfin : ∫⁻ x in ball (0 : 𝔼) ρ₂, ‖u.fst x‖ₑ ^ 2 < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set (ball_subset_ball h2)) (lintegral_sq_lt_top u.fst)
  rw [setIntegral_sq_eq_toReal (hm ρ₁), setIntegral_sq_eq_toReal (hm ρ₂)]
  have h := vertex_monotone_lintegral hd hc hu horth h1 h12 h2
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg
    (div_nonneg h1.le (h1.trans_le h12).le) _)] at h'

end Monotone

end ConicalKahler.Sobolev
