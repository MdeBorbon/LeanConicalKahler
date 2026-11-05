module

public import ConicalKahler.Sobolev.HarmonicApprox
public import ConicalKahler.Sobolev.ConeLaplacian

/-!
# Harmonic approximation on cone balls, uniformly in the centre

The paper's Proposition 5.1 applies Lemma 2.4 on geodesic balls `B(x, 1)` whose centres `x` vary
(`|x| < ε₀`), and needs a `δ` independent of `x` (`PAPER_REVIEW.md` S3). Lemma 2.4 itself is
stated only for `B_1` centred at the vertex.

Here the harmonic replacement argument (`CoeffField.harmonic_approximation`) is applied on the
geodesic balls `B(p, ρ)` of the product cone distance (`ConeProduct`), written in the coordinates
of `ℝ^d` (`coneBall`). Every such ball lies in the Euclidean ball `B̄(p, ρ / lowerConst β)`
(`coneBall_subset_closedBall`). So Lemma 2.4 holds on `B(p, ρ)` with the explicit threshold
`δ = λ ε / (4 (ρ / lowerConst β)² + 1)`, the **same for every centre `p`**
(`cone_harmonic_approximation`). No regularity of the ball is needed (balls off the vertex are
not convex in general, and for `β < 1/2` they can be annuli, App. A.1). The compactness argument
on such balls is no longer needed for this uniformity.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set
open scoped ContDiff ENNReal

namespace ConicalKahler.Sobolev

open RealConeModel

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **The geodesic ball** `B(p, ρ)` of the product cone distance, in the coordinates of `ℝ^d`
numbered by `e`. -/
def coneBall (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (p : RealConeModel κ ι)
    (ρ : ℝ) : Set 𝔼 :=
  coordIso e '' (ConeProduct.mk ⁻¹' Metric.ball (ConeProduct.mk p : ConeProduct β ι) ρ)

theorem upperConst_pos (β : κ → ConeAngle) : 0 < ConeProduct.upperConst β :=
  zero_lt_one.trans_le (ConeProduct.one_le_upperConst β)

/-- **Cone balls lie in Euclidean balls** with a radius independent of the centre:
`B(p, ρ) ⊆ B̄_E(p, ρ / lowerConst β)`. -/
theorem coneBall_subset_closedBall (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d)
    (p : RealConeModel κ ι) (ρ : ℝ) :
    coneBall β e p ρ ⊆ Metric.closedBall (coordIso e p) (ρ / ConeProduct.lowerConst β) := by
  rintro _ ⟨q, hq, rfl⟩
  have h := (ConeProduct.ball_subset (ConeProduct.lowerConst_pos β) (upperConst_pos β)
    ConeProduct.dist_bounds_uniform p ρ).2 hq
  rw [Metric.mem_ball] at h
  rw [Metric.mem_closedBall, LinearIsometryEquiv.dist_map]
  exact h.le

/-- **Euclidean balls lie in cone balls:** `B_E(p, ρ / upperConst β) ⊆ B(p, ρ)`. -/
theorem ball_subset_coneBall (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d)
    (p : RealConeModel κ ι) (ρ : ℝ) :
    Metric.ball (coordIso e p) (ρ / ConeProduct.upperConst β) ⊆ coneBall β e p ρ := by
  intro y hy
  refine ⟨(coordIso e).symm y, ?_, (coordIso e).apply_symm_apply y⟩
  refine (ConeProduct.ball_subset (ConeProduct.lowerConst_pos β) (upperConst_pos β)
    ConeProduct.dist_bounds_uniform p ρ).1 ?_
  rw [Metric.mem_ball, ← (coordIso e).dist_map, (coordIso e).apply_symm_apply]
  exact hy

/-- Cone balls are open. -/
theorem isOpen_coneBall (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d)
    (p : RealConeModel κ ι) (ρ : ℝ) : IsOpen (coneBall β e p ρ) := by
  exact (coordIso e).toHomeomorph.isOpenMap _
    (Metric.isOpen_ball.preimage (ConeProduct.homeomorph β ι).continuous)

variable [NeZero d]

/-- **Lemma 2.4 on cone balls, uniformly in the centre.** For the cone Laplacian
`-div(g⁻¹ ∇u) = f` on the geodesic ball `B(p, ρ)`: if
`‖f‖_{L²} < λ ε / (4 (ρ / lowerConst β)² + 1)`, there is a weakly harmonic `h` on `B(p, ρ)` with
`‖u - h‖_{L²(B(p, ρ))} < ε`. The threshold does not depend on `p`. -/
theorem cone_harmonic_approximation (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d)
    {ρ : ℝ} (hρ : 0 ≤ ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (p : RealConeModel κ ι) (f : Lp ℝ 2 (volume.restrict (coneBall β e p ρ)))
      (v : L2Pair volume (coneBall β e p ρ)), (coneCoeff β e).IsWeakSolution f v → ‖f‖ < δ →
      ∃ h : L2Pair volume (coneBall β e p ρ), (coneCoeff β e).IsWeakSolution 0 h ∧
        ‖v.fst - h.fst‖ < ε := by
  have hR : 0 ≤ ρ / ConeProduct.lowerConst β := div_nonneg hρ (ConeProduct.lowerConst_pos β).le
  refine ⟨coneLam β * ε / (4 * (ρ / ConeProduct.lowerConst β) ^ 2 + 1),
    by have := coneLam_pos β; positivity, fun p f v hv hf => ?_⟩
  exact CoeffField.harmonic_approximation (c := coneCoeff β e) hR
    (coneBall_subset_closedBall β e p ρ) hv hf

end ConicalKahler.Sobolev
