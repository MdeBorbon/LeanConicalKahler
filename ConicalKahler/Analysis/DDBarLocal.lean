module

public import CalabiYau.Geometry.Complex.Forms.ComplexHessian

/-!
# Elementary algebraic properties of `ddbar` on `ℂⁿ`

Small general facts about the upstream operator `ddbar f z = i∂∂̄f (z)` that are needed for the
conical model but are either private upstream or not stated there:

* `ConicalKahler.ddbar_congr`: `ddbar` only depends on the germ of `f` at `z`.
  (Upstream proves the same fact as a `private` lemma in
  `CalabiYau.Geometry.Complex.DDBar.ScalarPotential.Componentwise`; we re-prove it.)
* `ConicalKahler.ddbar_finset_sum`: `ddbar` of a finite sum of `C²` functions.
* `ConicalKahler.coeffMatrix_finset_sum`: the coefficient matrix is additive over finite sums.
* `ConicalKahler.ddbar_eq_zero_of_coeffMatrix_eq_zero`: a `C²` function whose complex Hessian
  vanishes at `z` has `i∂∂̄f (z) = 0` (as a real `2`-form, not merely its coefficients).
-/

@[expose] public section

open scoped ContDiff Topology
open Filter ContinuousAlternatingMap

namespace ConicalKahler

variable {n : ℕ}

/-- `i∂∂̄f (z)` depends only on the germ of `f` at `z`. -/
theorem ddbar_congr {f g : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (h : f =ᶠ[𝓝 z] g) : ddbar f z = ddbar g z := by
  have hform :
      (fun w => ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
        ((fderiv ℝ f w).comp (EuclideanSpace.complexStructure n))) =ᶠ[𝓝 z]
      (fun w => ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
        ((fderiv ℝ g w).comp (EuclideanSpace.complexStructure n))) := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with w hw
    rw [hw]
  unfold ddbar
  rw [hform.extDeriv_eq]

/-- `i∂∂̄` of a finite sum of `C²` functions is the sum of the `i∂∂̄`'s. -/
theorem ddbar_finset_sum {ι : Type*} (s : Finset ι)
    {F : ι → EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hF : ∀ i ∈ s, ContDiffAt ℝ 2 (F i) z) :
    ddbar (fun w => ∑ i ∈ s, F i w) z = ∑ i ∈ s, ddbar (F i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hFa : ContDiffAt ℝ 2 (F a) z := hF a (Finset.mem_insert_self a s)
    have hFs : ∀ i ∈ s, ContDiffAt ℝ 2 (F i) z := fun i hi =>
      hF i (Finset.mem_insert_of_mem hi)
    have hsum : ContDiffAt ℝ 2 (fun w => ∑ i ∈ s, F i w) z :=
      ContDiffAt.sum fun i hi => hFs i hi
    have hfun : (fun w => ∑ i ∈ insert a s, F i w) = F a + fun w => ∑ i ∈ s, F i w := by
      funext w
      simp [Finset.sum_insert ha]
    rw [hfun, ddbar_add hFa hsum, ih hFs, Finset.sum_insert ha]

/-- The coefficient matrix is additive over finite sums. -/
theorem coeffMatrix_finset_sum {ι : Type*} (s : Finset ι)
    (α : ι → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) :
    (∑ i ∈ s, α i).coeffMatrix = ∑ i ∈ s, (α i).coeffMatrix := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, coeffMatrix_add, ih, Finset.sum_insert ha]

/-- A `(1,1)`-form `i∂∂̄f (z)` with vanishing coefficient matrix is zero. -/
theorem ddbar_eq_zero_of_coeffMatrix_eq_zero {f : EuclideanSpace ℂ (Fin n) → ℝ}
    {z : EuclideanSpace ℂ (Fin n)} (hf : ContDiffAt ℝ 2 f z)
    (h : (ddbar f z).coeffMatrix = 0) : ddbar f z = 0 :=
  (isOneOne_ddbar hf).ext isOneOne_zero (by rw [h, coeffMatrix_zero])

end ConicalKahler
