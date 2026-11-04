module

public import ConicalKahler.Analysis.RadialHessian
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Holomorphic maps preserving coordinate hyperplanes

Let `Ψ : ℂⁿ → ℂⁿ` be holomorphic (`C²` over `ℂ` suffices) near a point `ζ₀` with `ζ₀_a = 0`, and
suppose `Ψ` maps the coordinate hyperplane `{ζ_a = 0}` into `{z_b = 0}` near `ζ₀`. The indices
`a` and `b` may differ: a change of SNC charts may permute the active components. Then near `ζ₀`
(`exists_coordHyperplane_estimates`):

* `|Ψ(ζ)_b| ≤ L |ζ_a|` (`Ψ_b` vanishes on the hyperplane; mean value inequality);
* `‖DΨ(ζ)‖ ≤ L`;
* `|(DΨ(ζ) v)_b| ≤ L |v_a| + L₂ |ζ_a| |v|` (the tangential derivatives of `Ψ_b` vanish on the
  hyperplane, `fderiv_apply_eq_zero_of_tangent`, and are Lipschitz).

These are the analytic inputs to the chart invariance of the cone conditions for angles `β ≤ 1`
(`ConicalKahler.Cone.WeightedComparison`). The smooth-divisor statement is the case `a = b = 0`
(`exists_hyperplane_estimates`). No factorization `Ψ_b = u ζ_a` (a several-variables Hadamard
lemma) is needed.
-/

@[expose] public section

open scoped ContDiff Topology
open Filter Metric Set

namespace ConicalKahler

variable {n : ℕ}

/-! ### Projection onto a coordinate hyperplane -/

/-- The projection `w ↦ w - w_a e_a` onto the coordinate hyperplane `{z_a = 0}`. -/
noncomputable def coordHypProj (a : Fin n) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  ContinuousLinearMap.id ℂ _ - coordProj a

theorem coordHypProj_apply (a : Fin n) (w : EuclideanSpace ℂ (Fin n)) :
    coordHypProj a w = w - w a • EuclideanSpace.single a 1 :=
  rfl

@[simp]
theorem coordHypProj_apply_self (a : Fin n) (w : EuclideanSpace ℂ (Fin n)) :
    coordHypProj a w a = 0 := by
  simp [coordHypProj_apply]

theorem coordHypProj_apply_of_ne (a : Fin n) (w : EuclideanSpace ℂ (Fin n)) {j : Fin n}
    (hj : j ≠ a) : coordHypProj a w j = w j := by
  simp [coordHypProj_apply, hj]

theorem sub_coordHypProj (a : Fin n) (w : EuclideanSpace ℂ (Fin n)) :
    w - coordHypProj a w = w a • EuclideanSpace.single a 1 := by
  simp [coordHypProj_apply]

theorem norm_sub_coordHypProj (a : Fin n) (w : EuclideanSpace ℂ (Fin n)) :
    ‖w - coordHypProj a w‖ = ‖w a‖ := by
  rw [sub_coordHypProj, norm_smul, PiLp.norm_single, norm_one, mul_one]

theorem coordHypProj_of_apply_self {a : Fin n} {w : EuclideanSpace ℂ (Fin n)} (hw : w a = 0) :
    coordHypProj a w = w := by
  simp [coordHypProj_apply, hw]

theorem norm_coordHypProj_le (a : Fin n) (w : EuclideanSpace ℂ (Fin n)) :
    ‖coordHypProj a w‖ ≤ ‖w‖ := by
  have hsq : ‖coordHypProj a w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j = a
    · subst hj
      simp
    · rw [coordHypProj_apply_of_ne a w hj]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

theorem norm_apply_le (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ‖w j‖ ≤ ‖w‖ :=
  PiLp.norm_apply_le w j

theorem norm_apply_zero_le [NeZero n] (w : EuclideanSpace ℂ (Fin n)) : ‖w 0‖ ≤ ‖w‖ :=
  norm_apply_le w 0

/-! ### Local estimates -/

/-- Tangential derivatives of `Ψ_b` vanish on the hyperplane: if `Ψ_b = 0` on `{ζ_a = 0}` near
`w` (with `w_a = 0`) and `u_a = 0`, then `(DΨ(w) u)_b = 0`. -/
theorem fderiv_apply_eq_zero_of_tangent {a b : Fin n}
    {Ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {w u : EuclideanSpace ℂ (Fin n)} (hΨ : DifferentiableAt ℂ Ψ w) (hw : w a = 0) (hu : u a = 0)
    (hpres : ∀ᶠ ζ in 𝓝 w, ζ a = 0 → Ψ ζ b = 0) : fderiv ℂ Ψ w u b = 0 := by
  let g : ℂ → ℂ := fun t => Ψ (w + t • u) b
  have hline : HasDerivAt (fun t : ℂ => w + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const u).const_add w
  have hΨ' : HasFDerivAt Ψ (fderiv ℂ Ψ w) (w + (0 : ℂ) • u) := by
    simpa using hΨ.hasFDerivAt
  have hcomp := hΨ'.comp_hasDerivAt (0 : ℂ) hline
  have hg : HasDerivAt g (fderiv ℂ Ψ w u b) 0 :=
    (EuclideanSpace.proj b : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).hasFDerivAt.comp_hasDerivAt
      (0 : ℂ) hcomp
  have hcont : Continuous fun t : ℂ => w + t • u := by fun_prop
  have htend : Tendsto (fun t : ℂ => w + t • u) (𝓝 0) (𝓝 w) := by
    simpa using hcont.tendsto (0 : ℂ)
  have hev : ∀ᶠ t : ℂ in 𝓝 0, g t = 0 := by
    filter_upwards [htend.eventually hpres] with t ht
    exact ht (by simp [hw, hu])
  have hg0 : HasDerivAt g 0 0 :=
    (hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hev
  exact hg.unique hg0

/-- The case `a = b = 0`. -/
theorem fderiv_apply_zero_eq_zero_of_tangent [NeZero n]
    {Ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {w u : EuclideanSpace ℂ (Fin n)} (hΨ : DifferentiableAt ℂ Ψ w) (hw : w 0 = 0) (hu : u 0 = 0)
    (hpres : ∀ᶠ ζ in 𝓝 w, ζ 0 = 0 → Ψ ζ 0 = 0) : fderiv ℂ Ψ w u 0 = 0 :=
  fderiv_apply_eq_zero_of_tangent hΨ hw hu hpres

/-- **Local estimates for maps sending `{ζ_a = 0}` into `{z_b = 0}`.** -/
theorem exists_coordHyperplane_estimates {a b : Fin n}
    {Ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {ζ₀ : EuclideanSpace ℂ (Fin n)} (hζ₀ : ζ₀ a = 0) (hΨ : ContDiffAt ℂ 2 Ψ ζ₀)
    (hpres : ∀ᶠ ζ in 𝓝 ζ₀, ζ a = 0 → Ψ ζ b = 0) :
    ∃ L L₂ : ℝ, 0 < L ∧ 0 ≤ L₂ ∧ ∀ᶠ ζ in 𝓝 ζ₀,
      ‖Ψ ζ b‖ ≤ L * ‖ζ a‖ ∧ ‖fderiv ℂ Ψ ζ‖ ≤ L ∧
        ∀ v, ‖fderiv ℂ Ψ ζ v b‖ ≤ L * ‖v a‖ + L₂ * ‖ζ a‖ * ‖v‖ := by
  obtain ⟨K₂, t₂, ht₂, hlip⟩ :=
    (hΨ.fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
  set L := ‖fderiv ℂ Ψ ζ₀‖ + 1 with hLdef
  set L₂ : ℝ := (K₂ : ℝ) with hL₂def
  have hL : 0 < L := by positivity
  have hL₂ : 0 ≤ L₂ := K₂.2
  refine ⟨L, L₂, hL, hL₂, ?_⟩
  have hev : ∀ᶠ ζ in 𝓝 ζ₀, ContDiffAt ℂ 2 Ψ ζ := hΨ.eventually (by simp)
  have hd1 : ContinuousAt (fderiv ℂ Ψ) ζ₀ :=
    (hΨ.fderiv_right (m := 1) (by norm_num)).continuousAt
  have hb1 : ∀ᶠ ζ in 𝓝 ζ₀, ‖fderiv ℂ Ψ ζ‖ < L :=
    hd1.norm.eventually_lt continuousAt_const (lt_add_one _)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (((hev.and hb1).and (eventually_mem_nhds_iff.mpr ht₂)).and
      (eventually_eventually_nhds.mpr hpres))
  rw [Metric.eventually_nhds_iff_ball]
  refine ⟨ε, hε, fun ζ hζ => ?_⟩
  -- facts on the ball
  have hdiff : ∀ x ∈ ball ζ₀ ε, DifferentiableAt ℂ Ψ x := fun x hx =>
    (hball x hx).1.1.1.differentiableAt (by norm_num)
  have hbd1 : ∀ x ∈ ball ζ₀ ε, ‖fderiv ℂ Ψ x‖ ≤ L := fun x hx => (hball x hx).1.1.2.le
  have hmem₂ : ∀ x ∈ ball ζ₀ ε, x ∈ t₂ := fun x hx => mem_of_mem_nhds (hball x hx).1.2
  -- the projection of `ζ` stays in the ball
  have hPζ : coordHypProj a ζ ∈ ball ζ₀ ε := by
    rw [mem_ball, dist_eq_norm] at hζ ⊢
    calc ‖coordHypProj a ζ - ζ₀‖ = ‖coordHypProj a (ζ - ζ₀)‖ := by
          rw [map_sub, coordHypProj_of_apply_self hζ₀]
      _ ≤ ‖ζ - ζ₀‖ := norm_coordHypProj_le a _
      _ < ε := hζ
  have hconv := convex_ball ζ₀ ε
  refine ⟨?_, hbd1 ζ hζ, fun v => ?_⟩
  · -- `|Ψ(ζ)_b| ≤ L |ζ_a|`
    have hzero : Ψ (coordHypProj a ζ) b = 0 :=
      (hball _ hPζ).2.self_of_nhds (coordHypProj_apply_self a ζ)
    have hmv := hconv.norm_image_sub_le_of_norm_fderiv_le hdiff hbd1 hPζ hζ
    calc ‖Ψ ζ b‖ = ‖(Ψ ζ - Ψ (coordHypProj a ζ)) b‖ := by simp [hzero]
      _ ≤ ‖Ψ ζ - Ψ (coordHypProj a ζ)‖ := norm_apply_le _ b
      _ ≤ L * ‖ζ - coordHypProj a ζ‖ := hmv
      _ = L * ‖ζ a‖ := by rw [norm_sub_coordHypProj]
  · -- `|(DΨ(ζ) v)_b| ≤ L |v_a| + L₂ |ζ_a| |v|`
    have hsplit : v = v a • EuclideanSpace.single a 1 + coordHypProj a v := by
      rw [← sub_coordHypProj]
      abel
    have htan : fderiv ℂ Ψ (coordHypProj a ζ) (coordHypProj a v) b = 0 :=
      fderiv_apply_eq_zero_of_tangent (hdiff _ hPζ) (coordHypProj_apply_self a ζ)
        (coordHypProj_apply_self a v) (hball _ hPζ).2
    have hmv : ‖fderiv ℂ Ψ ζ - fderiv ℂ Ψ (coordHypProj a ζ)‖ ≤
        L₂ * ‖ζ - coordHypProj a ζ‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact hlip.dist_le_mul ζ (hmem₂ ζ hζ) (coordHypProj a ζ) (hmem₂ _ hPζ)
    have h1 : ‖fderiv ℂ Ψ ζ (v a • EuclideanSpace.single a 1) b‖ ≤ L * ‖v a‖ := by
      calc ‖fderiv ℂ Ψ ζ (v a • EuclideanSpace.single a 1) b‖
          ≤ ‖fderiv ℂ Ψ ζ (v a • EuclideanSpace.single a 1)‖ := norm_apply_le _ b
        _ ≤ ‖fderiv ℂ Ψ ζ‖ * ‖v a • EuclideanSpace.single a (1 : ℂ)‖ :=
          (fderiv ℂ Ψ ζ).le_opNorm _
        _ ≤ L * ‖v a‖ := by
          rw [norm_smul, PiLp.norm_single, norm_one, mul_one]
          exact mul_le_mul_of_nonneg_right (hbd1 ζ hζ) (norm_nonneg _)
    have h2 : ‖fderiv ℂ Ψ ζ (coordHypProj a v) b‖ ≤ L₂ * ‖ζ a‖ * ‖v‖ := by
      calc ‖fderiv ℂ Ψ ζ (coordHypProj a v) b‖
          = ‖(fderiv ℂ Ψ ζ - fderiv ℂ Ψ (coordHypProj a ζ)) (coordHypProj a v) b‖ := by
            simp [htan]
        _ ≤ ‖(fderiv ℂ Ψ ζ - fderiv ℂ Ψ (coordHypProj a ζ)) (coordHypProj a v)‖ :=
          norm_apply_le _ b
        _ ≤ ‖fderiv ℂ Ψ ζ - fderiv ℂ Ψ (coordHypProj a ζ)‖ * ‖coordHypProj a v‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ (L₂ * ‖ζ - coordHypProj a ζ‖) * ‖v‖ :=
          mul_le_mul hmv (norm_coordHypProj_le a v) (norm_nonneg _) (by positivity)
        _ = L₂ * ‖ζ a‖ * ‖v‖ := by rw [norm_sub_coordHypProj]
    calc ‖fderiv ℂ Ψ ζ v b‖
        = ‖fderiv ℂ Ψ ζ (v a • EuclideanSpace.single a 1) b +
            fderiv ℂ Ψ ζ (coordHypProj a v) b‖ := by
          conv_lhs => rw [hsplit]
          rw [map_add, PiLp.add_apply]
      _ ≤ ‖fderiv ℂ Ψ ζ (v a • EuclideanSpace.single a 1) b‖ +
          ‖fderiv ℂ Ψ ζ (coordHypProj a v) b‖ := norm_add_le _ _
      _ ≤ L * ‖v a‖ + L₂ * ‖ζ a‖ * ‖v‖ := add_le_add h1 h2

/-- **Local estimates for hyperplane-preserving maps**: the case `a = b = 0`. -/
theorem exists_hyperplane_estimates [NeZero n]
    {Ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {ζ₀ : EuclideanSpace ℂ (Fin n)} (hζ₀ : ζ₀ 0 = 0) (hΨ : ContDiffAt ℂ 2 Ψ ζ₀)
    (hpres : ∀ᶠ ζ in 𝓝 ζ₀, ζ 0 = 0 → Ψ ζ 0 = 0) :
    ∃ L L₂ : ℝ, 0 < L ∧ 0 ≤ L₂ ∧ ∀ᶠ ζ in 𝓝 ζ₀,
      ‖Ψ ζ 0‖ ≤ L * ‖ζ 0‖ ∧ ‖fderiv ℂ Ψ ζ‖ ≤ L ∧
        ∀ v, ‖fderiv ℂ Ψ ζ v 0‖ ≤ L * ‖v 0‖ + L₂ * ‖ζ 0‖ * ‖v‖ :=
  exists_coordHyperplane_estimates hζ₀ hΨ hpres

end ConicalKahler
