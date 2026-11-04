module

public import ConicalKahler.Analysis.RadialHessian
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Holomorphic maps preserving the hyperplane `{z_0 = 0}`

Let `Ψ : ℂⁿ → ℂⁿ` be holomorphic (`C²` over `ℂ` suffices) near a point `ζ₀` with `ζ₀_0 = 0`, and
suppose `Ψ` maps the hyperplane `{ζ_0 = 0}` into `{z_0 = 0}` near `ζ₀`. Then near `ζ₀`
(`exists_hyperplane_estimates`):

* `|Ψ(ζ)_0| ≤ L |ζ_0|`  (`Ψ_0` vanishes on the hyperplane; mean value inequality);
* `‖DΨ(ζ)‖ ≤ L`;
* `|(DΨ(ζ) v)_0| ≤ L |v_0| + L₂ |ζ_0| |v|`  (the tangential derivatives of `Ψ_0` vanish on the
  hyperplane, `fderiv_apply_zero_eq_zero_of_tangent`, and are Lipschitz).

These are the analytic inputs to the chart invariance of the cone condition for `β ≤ 1`.
No factorization `Ψ_0 = u ζ_0` (a several-variables Hadamard lemma) is needed.
-/

@[expose] public section

open scoped ContDiff Topology
open Filter Metric Set

namespace ConicalKahler

variable {n : ℕ} [NeZero n]

/-! ### Projection onto the hyperplane -/

/-- The projection `w ↦ w - w_0 e_0` onto the hyperplane `{z_0 = 0}`. -/
noncomputable def hypProj : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  ContinuousLinearMap.id ℂ _ - coordProj 0

theorem hypProj_apply (w : EuclideanSpace ℂ (Fin n)) :
    hypProj w = w - w 0 • EuclideanSpace.single 0 1 :=
  rfl

@[simp]
theorem hypProj_apply_zero (w : EuclideanSpace ℂ (Fin n)) : hypProj w 0 = 0 := by
  simp [hypProj_apply]

theorem hypProj_apply_of_ne (w : EuclideanSpace ℂ (Fin n)) {j : Fin n} (hj : j ≠ 0) :
    hypProj w j = w j := by
  simp [hypProj_apply, hj]

theorem sub_hypProj (w : EuclideanSpace ℂ (Fin n)) :
    w - hypProj w = w 0 • EuclideanSpace.single 0 1 := by
  simp [hypProj_apply]

theorem norm_sub_hypProj (w : EuclideanSpace ℂ (Fin n)) : ‖w - hypProj w‖ = ‖w 0‖ := by
  rw [sub_hypProj, norm_smul, PiLp.norm_single, norm_one, mul_one]

theorem hypProj_of_apply_zero {w : EuclideanSpace ℂ (Fin n)} (hw : w 0 = 0) : hypProj w = w := by
  simp [hypProj_apply, hw]

theorem norm_hypProj_le (w : EuclideanSpace ℂ (Fin n)) : ‖hypProj w‖ ≤ ‖w‖ := by
  have hsq : ‖hypProj w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j = 0
    · subst hj
      simp
    · rw [hypProj_apply_of_ne w hj]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

theorem norm_apply_zero_le (w : EuclideanSpace ℂ (Fin n)) : ‖w 0‖ ≤ ‖w‖ :=
  PiLp.norm_apply_le w 0

/-! ### Local estimates -/

/-- Tangential derivatives of `Ψ_0` vanish on the hyperplane: if `Ψ_0 = 0` on `{ζ_0 = 0}` near
`w` (with `w_0 = 0`) and `u_0 = 0`, then `(DΨ(w) u)_0 = 0`. -/
theorem fderiv_apply_zero_eq_zero_of_tangent {Ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {w u : EuclideanSpace ℂ (Fin n)} (hΨ : DifferentiableAt ℂ Ψ w) (hw : w 0 = 0) (hu : u 0 = 0)
    (hpres : ∀ᶠ ζ in 𝓝 w, ζ 0 = 0 → Ψ ζ 0 = 0) : fderiv ℂ Ψ w u 0 = 0 := by
  let g : ℂ → ℂ := fun t => Ψ (w + t • u) 0
  have hline : HasDerivAt (fun t : ℂ => w + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const u).const_add w
  have hΨ' : HasFDerivAt Ψ (fderiv ℂ Ψ w) (w + (0 : ℂ) • u) := by
    simpa using hΨ.hasFDerivAt
  have hcomp := hΨ'.comp_hasDerivAt (0 : ℂ) hline
  have hg : HasDerivAt g (fderiv ℂ Ψ w u 0) 0 :=
    (EuclideanSpace.proj (0 : Fin n) : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).hasFDerivAt.comp_hasDerivAt
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

/-- **Local estimates for hyperplane-preserving maps.** -/
theorem exists_hyperplane_estimates {Ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {ζ₀ : EuclideanSpace ℂ (Fin n)} (hζ₀ : ζ₀ 0 = 0) (hΨ : ContDiffAt ℂ 2 Ψ ζ₀)
    (hpres : ∀ᶠ ζ in 𝓝 ζ₀, ζ 0 = 0 → Ψ ζ 0 = 0) :
    ∃ L L₂ : ℝ, 0 < L ∧ 0 ≤ L₂ ∧ ∀ᶠ ζ in 𝓝 ζ₀,
      ‖Ψ ζ 0‖ ≤ L * ‖ζ 0‖ ∧ ‖fderiv ℂ Ψ ζ‖ ≤ L ∧
        ∀ v, ‖fderiv ℂ Ψ ζ v 0‖ ≤ L * ‖v 0‖ + L₂ * ‖ζ 0‖ * ‖v‖ := by
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
  have hPζ : hypProj ζ ∈ ball ζ₀ ε := by
    rw [mem_ball, dist_eq_norm] at hζ ⊢
    calc ‖hypProj ζ - ζ₀‖ = ‖hypProj (ζ - ζ₀)‖ := by
          rw [map_sub, hypProj_of_apply_zero hζ₀]
      _ ≤ ‖ζ - ζ₀‖ := norm_hypProj_le _
      _ < ε := hζ
  have hconv := convex_ball ζ₀ ε
  refine ⟨?_, hbd1 ζ hζ, fun v => ?_⟩
  · -- `|Ψ(ζ)_0| ≤ L |ζ_0|`
    have hzero : Ψ (hypProj ζ) 0 = 0 :=
      (hball _ hPζ).2.self_of_nhds (hypProj_apply_zero ζ)
    have hmv := hconv.norm_image_sub_le_of_norm_fderiv_le hdiff hbd1 hPζ hζ
    calc ‖Ψ ζ 0‖ = ‖(Ψ ζ - Ψ (hypProj ζ)) 0‖ := by simp [hzero]
      _ ≤ ‖Ψ ζ - Ψ (hypProj ζ)‖ := norm_apply_zero_le _
      _ ≤ L * ‖ζ - hypProj ζ‖ := hmv
      _ = L * ‖ζ 0‖ := by rw [norm_sub_hypProj]
  · -- `|(DΨ(ζ) v)_0| ≤ L |v_0| + L₂ |ζ_0| |v|`
    have hsplit : v = v 0 • EuclideanSpace.single 0 1 + hypProj v := by
      rw [← sub_hypProj]
      abel
    have htan : fderiv ℂ Ψ (hypProj ζ) (hypProj v) 0 = 0 :=
      fderiv_apply_zero_eq_zero_of_tangent (hdiff _ hPζ) (hypProj_apply_zero ζ)
        (hypProj_apply_zero v) (hball _ hPζ).2
    have hmv : ‖fderiv ℂ Ψ ζ - fderiv ℂ Ψ (hypProj ζ)‖ ≤ L₂ * ‖ζ - hypProj ζ‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact hlip.dist_le_mul ζ (hmem₂ ζ hζ) (hypProj ζ) (hmem₂ _ hPζ)
    have h1 : ‖fderiv ℂ Ψ ζ (v 0 • EuclideanSpace.single 0 1) 0‖ ≤ L * ‖v 0‖ := by
      calc ‖fderiv ℂ Ψ ζ (v 0 • EuclideanSpace.single 0 1) 0‖
          ≤ ‖fderiv ℂ Ψ ζ (v 0 • EuclideanSpace.single 0 1)‖ := norm_apply_zero_le _
        _ ≤ ‖fderiv ℂ Ψ ζ‖ * ‖v 0 • EuclideanSpace.single (0 : Fin n) (1 : ℂ)‖ :=
          (fderiv ℂ Ψ ζ).le_opNorm _
        _ ≤ L * ‖v 0‖ := by
          rw [norm_smul, PiLp.norm_single, norm_one, mul_one]
          exact mul_le_mul_of_nonneg_right (hbd1 ζ hζ) (norm_nonneg _)
    have h2 : ‖fderiv ℂ Ψ ζ (hypProj v) 0‖ ≤ L₂ * ‖ζ 0‖ * ‖v‖ := by
      calc ‖fderiv ℂ Ψ ζ (hypProj v) 0‖
          = ‖(fderiv ℂ Ψ ζ - fderiv ℂ Ψ (hypProj ζ)) (hypProj v) 0‖ := by simp [htan]
        _ ≤ ‖(fderiv ℂ Ψ ζ - fderiv ℂ Ψ (hypProj ζ)) (hypProj v)‖ := norm_apply_zero_le _
        _ ≤ ‖fderiv ℂ Ψ ζ - fderiv ℂ Ψ (hypProj ζ)‖ * ‖hypProj v‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ (L₂ * ‖ζ - hypProj ζ‖) * ‖v‖ :=
          mul_le_mul hmv (norm_hypProj_le v) (norm_nonneg _) (by positivity)
        _ = L₂ * ‖ζ 0‖ * ‖v‖ := by rw [norm_sub_hypProj]
    calc ‖fderiv ℂ Ψ ζ v 0‖
        = ‖fderiv ℂ Ψ ζ (v 0 • EuclideanSpace.single 0 1) 0 + fderiv ℂ Ψ ζ (hypProj v) 0‖ := by
          conv_lhs => rw [hsplit]
          rw [map_add, PiLp.add_apply]
      _ ≤ ‖fderiv ℂ Ψ ζ (v 0 • EuclideanSpace.single 0 1) 0‖ +
          ‖fderiv ℂ Ψ ζ (hypProj v) 0‖ := norm_add_le _ _
      _ ≤ L * ‖v 0‖ + L₂ * ‖ζ 0‖ * ‖v‖ := add_le_add h1 h2

end ConicalKahler
