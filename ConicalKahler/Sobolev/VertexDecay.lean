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

open RealConeModel

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

/-! ### The cone: decay of harmonic functions orthogonal to `𝓗_{≤2}` -/

section Cone

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

/-- **Lemma 4.2 for the cone, with the gap of Proposition 3.4.** Let `0 < β_a < 1`, `μ` as in
eq. (1.1), and let `u ∈ W^{1,2}(B_1)` be weakly harmonic and `L²(B_1)`-orthogonal to `𝓗_{≤2}` (the
span of the paper's list). Then `∫_{B_{ρ₁}} u² ≤ (ρ₁/ρ₂)^{2(2+μ) + d} ∫_{B_{ρ₂}} u²`, i.e.
`‖u‖_{B_{ρ₁}} ≤ (ρ₁/ρ₂)^{2+μ} ‖u‖_{B_{ρ₂}}`, for `0 < ρ₁ ≤ ρ₂ ≤ 1`. -/
theorem cone_vertex_monotone (hd : 2 ≤ d) (β : κ → ConeAngle) (hβ : ∀ a, (β a).beta < 1)
    (e : RealConeIndex κ ι ≃ Fin d) {μ : ℝ} (hμ1 : μ ≤ 1)
    (hμ : ∀ a, μ ≤ holderExponentBound (β a).beta) {u : L2Pair volume (ball (0 : 𝔼) 1)}
    (hu : (coneCoeff β e).IsWeakSolution 0 u)
    (horth : ∀ P ∈ explicitH2 β, ∫ x in ball (0 : 𝔼) 1, u.fst x * P ((coordIso e).symm x) = 0)
    {ρ₁ ρ₂ : ℝ} (h1 : 0 < ρ₁) (h12 : ρ₁ ≤ ρ₂) (h2 : ρ₂ ≤ 1) :
    ∫ x in ball (0 : 𝔼) ρ₁, u.fst x ^ 2 ≤
      (ρ₁ / ρ₂) ^ (2 * (2 + μ) + d) * ∫ x in ball (0 : 𝔼) ρ₂, u.fst x ^ 2 := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  refine vertex_monotone hd (coneCoeff_isConical β e) hu
    (fun lam δ' v hE hlam hδ' hlt => ?_) h1 h12 h2
  have hP : MemLp (homP δ' v) 2 (volume.restrict (ball (0 : 𝔼) 1)) :=
    memLp_homFun_ball δ' (Lp.memLp v.fst) 1 (by linarith)
  have hG := memLp_homG_of_isLinkEigen hd hE hlam hδ'
  have hQ := homPair_isWeakSolution hP hG hd (coneCoeff_isConical β e) hE hlam (R := 1)
  have hQφ : ((homPair δ' v 1 hP hG).fst : 𝔼 → ℝ) =ᵐ[volume.restrict (ball (0 : 𝔼) 1)]
      homFun δ' fun w => v.fst w := hP.coeFn_toLp
  have h34 := prop_3_4 hd β hβ e hQ hδ' hQφ
  by_cases h2' : δ' ≤ 2
  · obtain ⟨Pe, hPe, hPe'⟩ := h34.1 h2'
    calc ∫ x in ball (0 : 𝔼) 1, u.fst x * homP δ' v x
        = ∫ x in ball (0 : 𝔼) 1, u.fst x * Pe ((coordIso e).symm x) := by
          refine integral_congr_ae ?_
          filter_upwards [hQφ, hPe'] with x hx hx'
          rw [← hx', hx]
      _ = 0 := horth Pe hPe
  · have h0 := h34.2 μ hμ1 hμ (not_le.mp h2') hlt
    refine integral_eq_zero_of_ae ?_
    have hz : ((homPair δ' v 1 hP hG).fst : 𝔼 → ℝ) =ᵐ[volume.restrict (ball (0 : 𝔼) 1)] 0 := by
      rw [h0]
      exact Lp.coeFn_zero ℝ 2 _
    filter_upwards [hQφ, hz] with x hx hx'
    have : homP δ' v x = 0 := by
      have h' : homFun δ' (fun w => v.fst w) x = 0 := by
        rw [← hx, hx']
        rfl
      exact h'
    simp [this]

/-- The span of the paper's list in `L²(B_1)` (`β_a ≤ 1`). -/
def h2ToLp {β : κ → ConeAngle} (hβ : ∀ a, (β a).beta ≤ 1) (e : RealConeIndex κ ι ≃ Fin d) :
    explicitH2 (ι := ι) β →ₗ[ℝ] Lp ℝ 2 (volume.restrict (ball (0 : 𝔼) 1)) where
  toFun P := ((explicitH2_le_classicalHarmonic hβ P.2).memLp e isOpen_ball isBounded_ball).toLp _
  map_add' P Q := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp ((explicitH2_le_classicalHarmonic hβ (P + Q).2).memLp e
      isOpen_ball isBounded_ball), MemLp.coeFn_toLp ((explicitH2_le_classicalHarmonic hβ P.2).memLp
      e isOpen_ball isBounded_ball), MemLp.coeFn_toLp ((explicitH2_le_classicalHarmonic hβ
      Q.2).memLp e isOpen_ball isBounded_ball), Lp.coeFn_add (((explicitH2_le_classicalHarmonic hβ
      P.2).memLp e isOpen_ball isBounded_ball).toLp _) (((explicitH2_le_classicalHarmonic hβ
      Q.2).memLp e isOpen_ball isBounded_ball).toLp _)] with x h h₁ h₂ h₃
    rw [h, h₃, Pi.add_apply, h₁, h₂]
    rfl
  map_smul' r P := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp ((explicitH2_le_classicalHarmonic hβ (r • P).2).memLp e
      isOpen_ball isBounded_ball), MemLp.coeFn_toLp ((explicitH2_le_classicalHarmonic hβ P.2).memLp
      e isOpen_ball isBounded_ball), Lp.coeFn_smul r (((explicitH2_le_classicalHarmonic hβ
      P.2).memLp e isOpen_ball isBounded_ball).toLp _)] with x h h₁ h₂
    rw [h, RingHom.id_apply, h₂, Pi.smul_apply, h₁]
    rfl

theorem h2ToLp_ae {β : κ → ConeAngle} (hβ : ∀ a, (β a).beta ≤ 1) (e : RealConeIndex κ ι ≃ Fin d)
    (P : explicitH2 (ι := ι) β) :
    (h2ToLp hβ e P : 𝔼 → ℝ) =ᵐ[volume.restrict (ball (0 : 𝔼) 1)]
      fun x => (P : RealConeModel κ ι → ℝ) ((coordIso e).symm x) :=
  MemLp.coeFn_toLp ((explicitH2_le_classicalHarmonic hβ P.2).memLp e isOpen_ball isBounded_ball)

/-- **Decay at the vertex.** Let `0 < β_a < 1`, `d ≥ 2`, `μ` as in eq. (1.1), and let
`h ∈ W^{1,2}(B_1)` be weakly harmonic. Let `P ∈ 𝓗_{≤2}` be the `L²(B_1)`-orthogonal projection of
`h` onto the span of the paper's list. Then `h − P` is orthogonal to `𝓗_{≤2}`,
`‖h − P‖_{L²(B_1)} ≤ ‖h‖_{L²(B_1)}`, and
`∫_{B_{ρ₁}} (h − P)² ≤ (ρ₁/ρ₂)^{2(2+μ) + d} ∫_{B_{ρ₂}} (h − P)²` for `0 < ρ₁ ≤ ρ₂ ≤ 1`. -/
theorem cone_vertex_decay (hd : 2 ≤ d) (β : κ → ConeAngle) (hβ : ∀ a, (β a).beta < 1)
    (e : RealConeIndex κ ι ≃ Fin d) {μ : ℝ} (hμ1 : μ ≤ 1)
    (hμ : ∀ a, μ ≤ holderExponentBound (β a).beta) {h : L2Pair volume (ball (0 : 𝔼) 1)}
    (hh : (coneCoeff β e).IsWeakSolution 0 h) :
    ∃ P ∈ explicitH2 β,
      (∀ Q ∈ explicitH2 β, ∫ x in ball (0 : 𝔼) 1,
        (h.fst x - P ((coordIso e).symm x)) * Q ((coordIso e).symm x) = 0) ∧
      ∫ x in ball (0 : 𝔼) 1, (h.fst x - P ((coordIso e).symm x)) ^ 2 ≤
        ∫ x in ball (0 : 𝔼) 1, h.fst x ^ 2 ∧
      ∀ ρ₁ ρ₂ : ℝ, 0 < ρ₁ → ρ₁ ≤ ρ₂ → ρ₂ ≤ 1 →
        ∫ x in ball (0 : 𝔼) ρ₁, (h.fst x - P ((coordIso e).symm x)) ^ 2 ≤
          (ρ₁ / ρ₂) ^ (2 * (2 + μ) + d) *
            ∫ x in ball (0 : 𝔼) ρ₂, (h.fst x - P ((coordIso e).symm x)) ^ 2 := by
  have hβ' : ∀ a, (β a).beta ≤ 1 := fun a => (hβ a).le
  set K := LinearMap.range (h2ToLp (ι := ι) hβ' e)
  have : FiniteDimensional ℝ K := LinearMap.finiteDimensional_range _
  have : CompleteSpace K := FiniteDimensional.complete ℝ K
  set p := K.starProjection h.fst
  obtain ⟨P', hP'⟩ := LinearMap.mem_range.mp (K.starProjection_apply_mem h.fst)
  set P : RealConeModel κ ι → ℝ := (P' : RealConeModel κ ι → ℝ)
  have hP : P ∈ explicitH2 β := P'.2
  obtain ⟨hu', hg', hPw⟩ := isWeakSolution_of_mem_explicitH2 hβ' hP e isOpen_ball isBounded_ball
  have hpP : (p : 𝔼 → ℝ) =ᵐ[volume.restrict (ball (0 : 𝔼) 1)] fun x => P ((coordIso e).symm x) := by
    have h0 := h2ToLp_ae hβ' e P'
    rw [hP'] at h0
    exact h0
  -- the remainder `u = h − P`
  set u := h - classicalPair hu' hg'
  have hu : (coneCoeff β e).IsWeakSolution 0 u := by
    have := hh.sub hPw
    rwa [sub_zero] at this
  have hufst : (u.fst : 𝔼 → ℝ) =ᵐ[volume.restrict (ball (0 : 𝔼) 1)]
      fun x => h.fst x - P ((coordIso e).symm x) := by
    have e1 : u.fst = h.fst - hu'.toLp _ := rfl
    filter_upwards [Lp.coeFn_sub h.fst (hu'.toLp (fun x => P ((coordIso e).symm x))),
      MemLp.coeFn_toLp hu'] with x hx hx'
    rw [e1, hx, Pi.sub_apply, hx']
  have hperp : h.fst - p ∈ Kᗮ := K.sub_starProjection_mem_orthogonal _
  have horth : ∀ Q ∈ explicitH2 β, ∫ x in ball (0 : 𝔼) 1,
      (h.fst x - P ((coordIso e).symm x)) * Q ((coordIso e).symm x) = 0 := by
    intro Q hQ
    have h0 := (Submodule.mem_orthogonal' K _).mp hperp (h2ToLp hβ' e ⟨Q, hQ⟩)
      (LinearMap.mem_range_self _ _)
    rw [L2.inner_def] at h0
    rw [← h0]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub h.fst p, hpP, h2ToLp_ae hβ' e ⟨Q, hQ⟩] with x hx hx' hx''
    rw [hx, Pi.sub_apply, hx', hx'', RCLike.inner_apply, conj_trivial, mul_comm]
  refine ⟨P, hP, horth, ?_, fun ρ₁ ρ₂ h1 h12 h2 => ?_⟩
  · -- `‖h − P‖ ≤ ‖h‖`
    have hpyth : ‖h.fst‖ ^ 2 = ‖h.fst - p‖ ^ 2 + ‖p‖ ^ 2 := by
      have hi : ⟪h.fst - p, p⟫_ℝ = 0 :=
        (Submodule.mem_orthogonal' K _).mp hperp p (K.starProjection_apply_mem h.fst)
      have := norm_add_sq_eq_norm_sq_add_norm_sq_real hi
      rw [sub_add_cancel] at this
      nlinarith [this]
    have hle : ‖h.fst - p‖ ^ 2 ≤ ‖h.fst‖ ^ 2 := by
      rw [hpyth]
      exact le_add_of_nonneg_right (sq_nonneg _)
    rw [norm_sq_eq_integral_L2, norm_sq_eq_integral_L2] at hle
    calc ∫ x in ball (0 : 𝔼) 1, (h.fst x - P ((coordIso e).symm x)) ^ 2
        = ∫ x in ball (0 : 𝔼) 1, ‖(h.fst - p) x‖ ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [Lp.coeFn_sub h.fst p, hpP] with x hx hx'
          rw [hx, Pi.sub_apply, hx', Real.norm_eq_abs, sq_abs]
      _ ≤ ∫ x in ball (0 : 𝔼) 1, ‖h.fst x‖ ^ 2 := hle
      _ = ∫ x in ball (0 : 𝔼) 1, h.fst x ^ 2 := by
          simp_rw [Real.norm_eq_abs, sq_abs]
  · -- the decay of the remainder
    have hdec := cone_vertex_monotone hd β hβ e hμ1 hμ hu (fun Q hQ => by
      rw [← horth Q hQ]
      refine integral_congr_ae ?_
      filter_upwards [hufst] with x hx
      rw [hx]) h1 h12 h2
    have hcongr : ∀ ρ, ρ ≤ 1 → ∫ x in ball (0 : 𝔼) ρ, u.fst x ^ 2 =
        ∫ x in ball (0 : 𝔼) ρ, (h.fst x - P ((coordIso e).symm x)) ^ 2 := fun ρ hρ =>
      integral_congr_ae (by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hρ) hufst]
          with x hx
        rw [hx])
    rwa [hcongr ρ₁ (h12.trans h2), hcongr ρ₂ h2] at hdec

end Cone

/-! ### Balls of any radius -/

section Scale

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

/-- **`𝓗_{≤2}` is invariant under dilations**: `P ∈ explicitH2 ⇒ P(t ·) ∈ explicitH2`, `t > 0`. -/
theorem comp_smul_mem_explicitH2 {β : κ → ConeAngle} {t : ℝ} (ht : 0 < t)
    {P : RealConeModel κ ι → ℝ} (hP : P ∈ explicitH2 β) :
    (fun y => P (t • y)) ∈ explicitH2 β := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    rcases hP with ((rfl | ⟨i, rfl⟩) | ⟨a, ha, rfl | rfl⟩) | ⟨cc, Q, hcQ, rfl⟩
    · exact one_mem_explicitH2
    · have : (fun y : RealConeModel κ ι => (t • y).eucl i) = t • fun y => y.eucl i := by
        funext y
        simp
      rw [this]
      exact Submodule.smul_mem _ t (eucl_mem_explicitH2 i)
    · have : (fun y : RealConeModel κ ι => harmCosFn (β a).beta 1 a (t • y)) =
          t ^ ((1 : ℕ) / (β a).beta) • harmCosFn (ι := ι) (β a).beta 1 a := by
        funext y
        simp only [harmCosFn, cone_smul, Pi.smul_apply, smul_eq_mul]
        rw [← Complex.real_smul, harmCosC_smul _ 1 ht]
      rw [this]
      exact Submodule.smul_mem _ _ (harmCos_mem_explicitH2 ha)
    · have : (fun y : RealConeModel κ ι => harmSinFn (β a).beta 1 a (t • y)) =
          t ^ ((1 : ℕ) / (β a).beta) • harmSinFn (ι := ι) (β a).beta 1 a := by
        funext y
        simp only [harmSinFn, cone_smul, Pi.smul_apply, smul_eq_mul]
        rw [← Complex.real_smul, harmSinC_smul _ 1 ht]
      rw [this]
      exact Submodule.smul_mem _ _ (harmSin_mem_explicitH2 ha)
    · have : (fun y : RealConeModel κ ι => quadFn cc Q (t • y)) = t ^ 2 • quadFn cc Q := by
        funext y
        simp only [quadFn, cone_smul, eucl_smul, Pi.smul_apply, smul_eq_mul, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun a _ => by ring
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      rw [this]
      exact Submodule.smul_mem _ _ (quadFn_mem_explicitH2 hcQ)
  | zero => exact Submodule.zero_mem _
  | add P Q _ _ hP hQ => exact Submodule.add_mem _ hP hQ
  | smul r P _ hP => exact Submodule.smul_mem _ r hP

theorem dilLp_zero {t : ℝ} (ht : 0 < t) {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) :
    dilLp ht hΩ (0 : Lp ℝ 2 (volume.restrict Ω)) = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have h0 : ∀ᵐ y ∂(Measure.map (fun x : 𝔼 => t • x) (volume.restrict (dilDom t Ω))),
      (0 : Lp ℝ 2 (volume.restrict Ω)) y = 0 := by
    rw [map_smul_restrict ht hΩ]
    exact Measure.ae_smul_measure (Lp.coeFn_zero ℝ 2 _) _
  filter_upwards [dilLp_ae ht hΩ (0 : Lp ℝ 2 (volume.restrict Ω)),
    ae_of_ae_map (measurable_const_smul t).aemeasurable h0] with x hx hx'
  rw [hx, hx', Pi.zero_apply]

theorem cone_vertex_monotone_of_eq (hd : 2 ≤ d) (β : κ → ConeAngle) (hβ : ∀ a, (β a).beta < 1)
    (e : RealConeIndex κ ι ≃ Fin d) {μ : ℝ} (hμ1 : μ ≤ 1)
    (hμ : ∀ a, μ ≤ holderExponentBound (β a).beta) {Ω : Set 𝔼} (hΩ : Ω = ball (0 : 𝔼) 1)
    {u : L2Pair volume Ω} (hu : (coneCoeff β e).IsWeakSolution 0 u)
    (horth : ∀ P ∈ explicitH2 β, ∫ x in Ω, u.fst x * P ((coordIso e).symm x) = 0)
    {ρ₁ ρ₂ : ℝ} (h1 : 0 < ρ₁) (h12 : ρ₁ ≤ ρ₂) (h2 : ρ₂ ≤ 1) :
    ∫ x in ball (0 : 𝔼) ρ₁, u.fst x ^ 2 ≤
      (ρ₁ / ρ₂) ^ (2 * (2 + μ) + d) * ∫ x in ball (0 : 𝔼) ρ₂, u.fst x ^ 2 := by
  subst hΩ
  exact cone_vertex_monotone hd β hβ e hμ1 hμ hu horth h1 h12 h2

/-- **Lemma 4.2 for the cone on `B_R`.** Let `u ∈ W^{1,2}(B_R)` be weakly harmonic and
`L²(B_R)`-orthogonal to `𝓗_{≤2}`. Then `∫_{B_{ρ₁}} u² ≤ (ρ₁/ρ₂)^{2(2+μ)+d} ∫_{B_{ρ₂}} u²` for
`0 < ρ₁ ≤ ρ₂ ≤ R`. (Dilate to `B_1`; `𝓗_{≤2}` is dilation invariant.) -/
theorem cone_vertex_monotone_ball (hd : 2 ≤ d) (β : κ → ConeAngle) (hβ : ∀ a, (β a).beta < 1)
    (e : RealConeIndex κ ι ≃ Fin d) {μ : ℝ} (hμ1 : μ ≤ 1)
    (hμ : ∀ a, μ ≤ holderExponentBound (β a).beta) {R : ℝ} (hR : 0 < R)
    {u : L2Pair volume (ball (0 : 𝔼) R)} (hu : (coneCoeff β e).IsWeakSolution 0 u)
    (horth : ∀ P ∈ explicitH2 β, ∫ x in ball (0 : 𝔼) R, u.fst x * P ((coordIso e).symm x) = 0)
    {ρ₁ ρ₂ : ℝ} (h1 : 0 < ρ₁) (h12 : ρ₁ ≤ ρ₂) (h2 : ρ₂ ≤ R) :
    ∫ x in ball (0 : 𝔼) ρ₁, u.fst x ^ 2 ≤
      (ρ₁ / ρ₂) ^ (2 * (2 + μ) + d) * ∫ x in ball (0 : 𝔼) ρ₂, u.fst x ^ 2 := by
  have hmeas : MeasurableSet (ball (0 : 𝔼) R) := measurableSet_ball
  have hdom : dilDom R (ball (0 : 𝔼) R) = ball (0 : 𝔼) 1 := by
    have := dilDom_ball hR (0 : 𝔼) 1
    rwa [mul_one, smul_zero] at this
  set v := Sobolev.dilate hR hmeas u
  have hv : (coneCoeff β e).IsWeakSolution 0 v := by
    have := hu.dilate hR (fun x => coneCoeffA_smul β e hR.ne' x) hmeas
    rwa [dilLp_zero hR hmeas, smul_zero] at this
  have hvfst : (v.fst : 𝔼 → ℝ) =ᵐ[volume.restrict (dilDom R (ball (0 : 𝔼) R))]
      fun x => u.fst (R • x) := dilLp_ae hR hmeas u.fst
  -- orthogonality after dilation
  have hvorth : ∀ P ∈ explicitH2 β, ∫ x in dilDom R (ball (0 : 𝔼) R),
      v.fst x * P ((coordIso e).symm x) = 0 := by
    intro P hP
    have hP' := comp_smul_mem_explicitH2 (inv_pos.mpr hR) hP
    calc ∫ x in dilDom R (ball (0 : 𝔼) R), v.fst x * P ((coordIso e).symm x)
        = ∫ x in dilDom R (ball (0 : 𝔼) R), (fun y => u.fst y * P (R⁻¹ • (coordIso e).symm y))
            (R • x) := by
          refine integral_congr_ae ?_
          filter_upwards [hvfst] with x hx
          rw [hx, map_smul, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
      _ = (R ^ d)⁻¹ • ∫ y in ball (0 : 𝔼) R, u.fst y * P (R⁻¹ • (coordIso e).symm y) := by
          convert setIntegral_comp_smul_dilDom hR hmeas
            (fun y => u.fst y * P (R⁻¹ • (coordIso e).symm y)) using 1
      _ = 0 := by rw [horth _ hP', smul_zero]
  have hρ : ∀ ρ, 0 < ρ → ρ ≤ R → ∫ x in ball (0 : 𝔼) (ρ / R), v.fst x ^ 2 =
      (R ^ d)⁻¹ * ∫ x in ball (0 : 𝔼) ρ, u.fst x ^ 2 := by
    intro ρ hρ0 hρR
    have hsub : ball (0 : 𝔼) (ρ / R) ⊆ dilDom R (ball (0 : 𝔼) R) := by
      rw [hdom]
      exact ball_subset_ball ((div_le_one hR).mpr hρR)
    calc ∫ x in ball (0 : 𝔼) (ρ / R), v.fst x ^ 2
        = ∫ x in ball (R⁻¹ • (0 : 𝔼)) (ρ / R), (fun y => u.fst y ^ 2) (R • x) := by
          rw [smul_zero]
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hvfst] with x hx
          rw [hx]
      _ = (R ^ d)⁻¹ • ∫ y in ball (0 : 𝔼) (R * (ρ / R)), u.fst y ^ 2 := by
          convert setIntegral_ball_dilate hR (0 : 𝔼) (ρ / R) (fun y => u.fst y ^ 2) using 1
      _ = (R ^ d)⁻¹ * ∫ x in ball (0 : 𝔼) ρ, u.fst x ^ 2 := by
          rw [mul_div_cancel₀ _ hR.ne', smul_eq_mul]
  have hmain := cone_vertex_monotone_of_eq hd β hβ e hμ1 hμ hdom hv hvorth
    (div_pos h1 hR) (div_le_div_of_nonneg_right h12 hR.le) ((div_le_one hR).mpr h2)
  rw [hρ ρ₁ h1 (h12.trans h2), hρ ρ₂ (h1.trans_le h12) h2,
    div_div_div_cancel_right₀ hR.ne'] at hmain
  have hRd : 0 < (R ^ d)⁻¹ := inv_pos.mpr (pow_pos hR d)
  rw [mul_left_comm] at hmain
  exact le_of_mul_le_mul_left hmain hRd

end Scale

end ConicalKahler.Sobolev
