module

public import ConicalKahler.Analysis.RadialHessian
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Calculus of the radial coefficient

`radialCoeff g s = g'(s) + s g''(s)` is the coefficient of `i∂∂̄ g(|z|²) = radialCoeff g (|z|²)
i dz ∧ dz̄` (`coeffMatrix_ddbar_comp_coordNormSq`). This file records the rules needed to compute
it for explicit profiles:

* `radialCoeff_congr`: it only depends on the germ of `g` at `s`;
* `radialCoeff_add`: it is additive on `C²` profiles;
* `radialCoeff_eq_deriv`: `g' + s g'' = (s g')'`;
* `radialCoeff_log_one_add_mul_rpow`: for `c ≥ 0`, `β, s > 0`, the profile `log(1 + c s^β)` has
  radial coefficient `c β² s^(β-1) / (1 + c s^β)²`.
-/

@[expose] public section

open scoped Topology ContDiff
open Filter

namespace ConicalKahler

/-- The radial coefficient only depends on the germ of the profile. -/
theorem radialCoeff_congr {f g : ℝ → ℝ} {s : ℝ} (h : f =ᶠ[𝓝 s] g) :
    radialCoeff f s = radialCoeff g s := by
  have hd : deriv f =ᶠ[𝓝 s] deriv g := h.deriv
  rw [radialCoeff, radialCoeff, hd.eq_of_nhds, hd.deriv_eq]

/-- A `C²` function has a `C¹` derivative. -/
theorem contDiffAt_deriv_of_two {f : ℝ → ℝ} {s : ℝ} (hf : ContDiffAt ℝ 2 f s) :
    ContDiffAt ℝ 1 (deriv f) s := by
  have h : ContDiffAt ℝ 1 (fderiv ℝ f) s := hf.fderiv_right (by norm_num)
  exact h.clm_apply contDiffAt_const

theorem differentiableAt_deriv_of_two {f : ℝ → ℝ} {s : ℝ} (hf : ContDiffAt ℝ 2 f s) :
    DifferentiableAt ℝ (deriv f) s :=
  (contDiffAt_deriv_of_two hf).differentiableAt (by norm_num)

theorem eventually_differentiableAt_of_two {f : ℝ → ℝ} {s : ℝ} (hf : ContDiffAt ℝ 2 f s) :
    ∀ᶠ t in 𝓝 s, DifferentiableAt ℝ f t :=
  (hf.eventually (by simp)).mono fun _ ht => ht.differentiableAt (by norm_num)

/-- The radial coefficient is additive on `C²` profiles. -/
theorem radialCoeff_add {f g : ℝ → ℝ} {s : ℝ} (hf : ContDiffAt ℝ 2 f s)
    (hg : ContDiffAt ℝ 2 g s) :
    radialCoeff (fun t => f t + g t) s = radialCoeff f s + radialCoeff g s := by
  have hd : deriv (fun t => f t + g t) =ᶠ[𝓝 s] fun t => deriv f t + deriv g t := by
    filter_upwards [eventually_differentiableAt_of_two hf, eventually_differentiableAt_of_two hg]
      with t h1 h2
    exact deriv_add h1 h2
  rw [radialCoeff, radialCoeff, radialCoeff, hd.eq_of_nhds, hd.deriv_eq,
    deriv_fun_add (differentiableAt_deriv_of_two hf) (differentiableAt_deriv_of_two hg)]
  ring

/-- `g' + s g'' = (s g')'`. -/
theorem radialCoeff_eq_deriv {g : ℝ → ℝ} {s : ℝ} (hg : DifferentiableAt ℝ (deriv g) s) :
    radialCoeff g s = deriv (fun t => t * deriv g t) s := by
  rw [radialCoeff, (show HasDerivAt (fun t => t * deriv g t) _ s from
    (hasDerivAt_id' s).mul hg.hasDerivAt).deriv]
  ring

/-- `s^β + s^(2β)` has radial coefficient `β² s^(β-1) (1 + 4 s^β)` for `s > 0`. In terms of
`w = z^β` this is `i∂∂̄(|w|² + |w|⁴)`. -/
theorem radialCoeff_rpow_add_rpow_two_mul {β s : ℝ} (hs : 0 < s) :
    radialCoeff (fun t => t ^ β + t ^ (2 * β)) s = β ^ 2 * s ^ (β - 1) * (1 + 4 * s ^ β) := by
  rw [radialCoeff_add (Real.contDiffAt_rpow_const_of_ne hs.ne')
    (Real.contDiffAt_rpow_const_of_ne hs.ne'), radialCoeff_rpow β hs, radialCoeff_rpow _ hs]
  have h : s ^ (2 * β - 1) = s ^ (β - 1) * s ^ β := by
    rw [← Real.rpow_add hs]
    ring_nf
  rw [h]
  ring

/-- **The radial coefficient of `log(1 + c s^β)`** is `c β² s^(β-1) / (1 + c s^β)²` for
`c ≥ 0`, `s > 0`. -/
theorem radialCoeff_log_one_add_mul_rpow {c β s : ℝ} (hc : 0 ≤ c) (hs : 0 < s) :
    radialCoeff (fun t => Real.log (1 + c * t ^ β)) s =
      c * β ^ 2 * s ^ (β - 1) / (1 + c * s ^ β) ^ 2 := by
  -- the derivative on a neighbourhood of `s`
  have hpos : ∀ t : ℝ, 0 < t → 0 < 1 + c * t ^ β := fun t ht =>
    add_pos_of_pos_of_nonneg one_pos (mul_nonneg hc (Real.rpow_nonneg ht.le _))
  have hder : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun t => Real.log (1 + c * t ^ β))
        (c * (β * t ^ (β - 1)) / (1 + c * t ^ β)) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => 1 + c * t ^ β) (c * (β * t ^ (β - 1))) t :=
      ((Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul c).const_add 1
    exact h1.log (hpos t ht).ne'
  have hev : deriv (fun t => Real.log (1 + c * t ^ β)) =ᶠ[𝓝 s]
      fun t => c * (β * t ^ (β - 1)) / (1 + c * t ^ β) := by
    filter_upwards [lt_mem_nhds hs] with t ht
    exact (hder t ht).deriv
  -- `t * deriv g t = c β t^β / (1 + c t^β)` near `s`
  have hev' : (fun t => t * deriv (fun t => Real.log (1 + c * t ^ β)) t) =ᶠ[𝓝 s]
      fun t => c * β * t ^ β / (1 + c * t ^ β) := by
    filter_upwards [hev, lt_mem_nhds hs] with t h ht
    rw [h]
    have : t * t ^ (β - 1) = t ^ β := by
      rw [mul_comm, ← Real.rpow_add_one ht.ne']
      ring_nf
    rw [mul_div_assoc', ← this]
    ring
  have hdiff : DifferentiableAt ℝ (deriv fun t => Real.log (1 + c * t ^ β)) s := by
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    refine DifferentiableAt.div ?_ ?_ (hpos s hs).ne'
    · exact (((Real.hasDerivAt_rpow_const (Or.inl hs.ne')).const_mul β).const_mul c).differentiableAt
    · exact ((Real.hasDerivAt_rpow_const (Or.inl hs.ne')).const_mul c).const_add 1
        |>.differentiableAt
  rw [radialCoeff_eq_deriv hdiff, hev'.deriv_eq]
  have hu : HasDerivAt (fun t => c * β * t ^ β) (c * β * (β * s ^ (β - 1))) s :=
    (Real.hasDerivAt_rpow_const (Or.inl hs.ne')).const_mul (c * β)
  have hv : HasDerivAt (fun t => 1 + c * t ^ β) (c * (β * s ^ (β - 1))) s :=
    ((Real.hasDerivAt_rpow_const (Or.inl hs.ne')).const_mul c).const_add 1
  rw [(show HasDerivAt (fun t => c * β * t ^ β / (1 + c * t ^ β)) _ s from
    hu.div hv (hpos s hs).ne').deriv]
  have hne := (hpos s hs).ne'
  field_simp
  ring

end ConicalKahler
