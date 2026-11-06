module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity

/-!
# Formal cone polynomials and the Fischer decomposition

On a product of cones `C(β_1) × ⋯ × C(β_n) × ℝ^ι`, a function in the angular mode
`k = (k_a)` (that is, `∏_a r_a^{k_a/β_a} cos/sin(k_a θ_a)` times a function of `r_a` and `s_i`) whose
remaining factor is a polynomial `p(r_1², …, r_n², s)` is a **cone polynomial**. The Laplacian
acts on the polynomial factor as the formal operator

  `L_q = ∑_a (4 t_a ∂²_{t_a} + 4 q_a ∂_{t_a}) + ∑_i ∂²_{s_i}`,   `q_a = 1 + k_a/β_a`,

in the variables `t_a = r_a²` (weight `2`) and `s_i` (weight `1`). Multiplication by
`ρ² = ∑_a t_a + ∑_i s_i²` raises the weighted degree by `2`, and

  `L_q(ρ² p) = ρ² L_q p + (4m + C₀) p`   for `p` of weighted degree `m`, `C₀ = 4 ∑ q_a + 2 #ι`
  (`formalLap_rhoSq_mul`, using Mathlib's weighted Euler identity).

This gives the **Fischer decomposition** (`fischer`): every weighted homogeneous `p` of degree `m`
is `∑_j ρ^{2j} h_j` with `L_q h_j = 0` and `h_j` weighted homogeneous of degree `m - 2j`. Hence
every polynomial lies in the span of the `ρ^{2j} h` with `h` harmonic and weighted homogeneous
(`mem_span_harmonicGen`).

Everything in this file is formal algebra in `MvPolynomial (κ ⊕ ι) ℝ`; the analytic meaning is
established in `ConePolyFn.lean`.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MvPolynomial Finset

namespace ConicalKahler.Sobolev

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

/-- The weights of the polynomial variables: `t_a = r_a²` has weight `2`, `s_i` weight `1`. -/
def polyWt : κ ⊕ ι → ℕ := Sum.elim (fun _ => 2) fun _ => 1

@[simp] theorem polyWt_inl (a : κ) : polyWt (κ := κ) (ι := ι) (Sum.inl a) = 2 := rfl

@[simp] theorem polyWt_inr (i : ι) : polyWt (κ := κ) (ι := ι) (Sum.inr i) = 1 := rfl

/-- `ρ² = ∑_a t_a + ∑_i s_i²`. -/
def rhoSq : MvPolynomial (κ ⊕ ι) ℝ :=
  ∑ a : κ, X (Sum.inl a : κ ⊕ ι) + ∑ i : ι, X (Sum.inr i : κ ⊕ ι) ^ 2

theorem rhoSq_isWeightedHomogeneous :
    IsWeightedHomogeneous (polyWt (κ := κ) (ι := ι)) (rhoSq (κ := κ) (ι := ι)) 2 := by
  refine IsWeightedHomogeneous.add (IsWeightedHomogeneous.sum (Finset.univ : Finset κ)
    (fun a => (X (Sum.inl a : κ ⊕ ι) : MvPolynomial (κ ⊕ ι) ℝ)) 2 fun a _ => ?_)
    (IsWeightedHomogeneous.sum (Finset.univ : Finset ι)
      (fun i => (X (Sum.inr i : κ ⊕ ι) : MvPolynomial (κ ⊕ ι) ℝ) ^ 2) 2 fun i _ => ?_)
  · exact isWeightedHomogeneous_X _ _ _
  · have := (isWeightedHomogeneous_X ℝ (polyWt (κ := κ) (ι := ι)) (Sum.inr i)).pow 2
    simpa using this

theorem pderiv_inl_rhoSq (a : κ) :
    pderiv (Sum.inl a) (rhoSq (κ := κ) (ι := ι)) = 1 := by
  simp [rhoSq, map_sum, pderiv_X, Pi.single_apply]

theorem pderiv_inr_rhoSq (i : ι) :
    pderiv (Sum.inr i) (rhoSq (κ := κ) (ι := ι)) = C 2 * X (Sum.inr i) := by
  simp [rhoSq, map_sum, pderiv_X, Pi.single_apply, map_ofNat]

/-- **The formal Laplacian** in the mode with constants `q_a = 1 + k_a/β_a`:
`L_q = ∑_a (4 t_a ∂²_{t_a} + 4 q_a ∂_{t_a}) + ∑_i ∂²_{s_i}`. -/
def formalLap (q : κ → ℝ) : MvPolynomial (κ ⊕ ι) ℝ →ₗ[ℝ] MvPolynomial (κ ⊕ ι) ℝ :=
  (∑ a, ((4 : ℝ) • (LinearMap.mulLeft ℝ (X (Sum.inl a)) ∘ₗ
      ((pderiv (Sum.inl a)).toLinearMap ∘ₗ (pderiv (Sum.inl a)).toLinearMap)) +
    (4 * q a) • (pderiv (Sum.inl a)).toLinearMap)) +
  ∑ i, (pderiv (Sum.inr i)).toLinearMap ∘ₗ (pderiv (Sum.inr i)).toLinearMap

theorem formalLap_apply (q : κ → ℝ) (p : MvPolynomial (κ ⊕ ι) ℝ) :
    formalLap q p = ∑ a, (C 4 * (X (Sum.inl a) * pderiv (Sum.inl a) (pderiv (Sum.inl a) p)) +
      C (4 * q a) * pderiv (Sum.inl a) p) +
      ∑ i, pderiv (Sum.inr i) (pderiv (Sum.inr i) p) := by
  simp [formalLap, LinearMap.sum_apply, smul_eq_C_mul]

/-! ### Weighted degrees -/

/-- A partial derivative of a polynomial of weighted degree `< w_v` vanishes. -/
theorem pderiv_eq_zero_of_lt {p : MvPolynomial (κ ⊕ ι) ℝ} {n : ℕ}
    (hp : IsWeightedHomogeneous polyWt p n) {v : κ ⊕ ι} (hv : n < polyWt v) : pderiv v p = 0 := by
  ext m
  rw [coeff_pderiv]
  have h0 : (0 : MvPolynomial (κ ⊕ ι) ℝ).coeff m = 0 := by simp
  rw [h0]
  by_contra h
  have hne : p.coeff (m + Finsupp.single v 1) ≠ 0 := left_ne_zero_of_mul h
  have hw := hp hne
  rw [map_add, Finsupp.weight_single, one_smul] at hw
  omega

theorem formalLap_isWeightedHomogeneous (q : κ → ℝ) {p : MvPolynomial (κ ⊕ ι) ℝ} {n : ℕ}
    (hp : IsWeightedHomogeneous polyWt p (n + 2)) :
    IsWeightedHomogeneous polyWt (formalLap q p) n := by
  rw [formalLap_apply]
  refine IsWeightedHomogeneous.add (IsWeightedHomogeneous.sum _ _ _ fun a _ => ?_)
    (IsWeightedHomogeneous.sum _ _ _ fun i _ => ?_)
  · have h1 : IsWeightedHomogeneous polyWt (pderiv (Sum.inl a) p) n := hp.pderiv rfl
    refine IsWeightedHomogeneous.add ?_ (h1.C_mul _)
    refine IsWeightedHomogeneous.C_mul ?_ _
    rcases Nat.lt_or_ge n 2 with hn | hn
    · rw [pderiv_eq_zero_of_lt h1 (by simpa using hn), mul_zero]
      exact isWeightedHomogeneous_zero _ _ _
    · obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le' hn
      have h2 : IsWeightedHomogeneous polyWt (pderiv (Sum.inl a) (pderiv (Sum.inl a) p)) n' :=
        h1.pderiv rfl
      have := (isWeightedHomogeneous_X ℝ polyWt (Sum.inl a)).mul h2
      simpa [add_comm] using this
  · have h1 : IsWeightedHomogeneous polyWt (pderiv (Sum.inr i) p) (n + 1) := hp.pderiv rfl
    exact h1.pderiv rfl

theorem formalLap_eq_zero_of_lt_two (q : κ → ℝ) {p : MvPolynomial (κ ⊕ ι) ℝ} {n : ℕ}
    (hp : IsWeightedHomogeneous polyWt p n) (hn : n < 2) : formalLap q p = 0 := by
  rw [formalLap_apply]
  have ha : ∀ a : κ, pderiv (Sum.inl a) p = 0 := fun a =>
    pderiv_eq_zero_of_lt hp (by simpa using hn)
  have hi : ∀ i : ι, pderiv (Sum.inr i) (pderiv (Sum.inr i) p) = 0 := by
    intro i
    rcases Nat.lt_or_ge n 1 with h1 | h1
    · rw [pderiv_eq_zero_of_lt hp (by simpa using h1), map_zero]
    · have hn1 : n = 1 := by omega
      subst hn1
      have h0 : IsWeightedHomogeneous polyWt (pderiv (Sum.inr i) p) 0 := hp.pderiv rfl
      exact pderiv_eq_zero_of_lt h0 (by simp)
  simp [ha, hi]

/-! ### The Fischer identity -/

/-- The constant `C₀ = 4 ∑_a q_a + 2 #ι` of the Fischer identity. -/
def fischerConst (ι : Type) [Fintype ι] (q : κ → ℝ) : ℝ := 4 * ∑ a, q a + 2 * (Fintype.card ι : ℝ)

theorem euler_split {p : MvPolynomial (κ ⊕ ι) ℝ} {n : ℕ} (hp : IsWeightedHomogeneous polyWt p n) :
    ∑ a : κ, 2 * (X (Sum.inl a) * pderiv (Sum.inl a) p) +
      ∑ i : ι, X (Sum.inr i) * pderiv (Sum.inr i) p = (n : MvPolynomial (κ ⊕ ι) ℝ) * p := by
  have h := hp.sum_weight_X_mul_pderiv
  rw [Fintype.sum_sum_type] at h
  simp only [polyWt_inl, polyWt_inr, one_smul, nsmul_eq_mul, Nat.cast_ofNat] at h
  exact h

/-- **The Fischer identity** `L_q(ρ² p) = ρ² L_q p + (4m + C₀) p` for `p` of weighted degree
`m`. -/
theorem formalLap_rhoSq_mul (q : κ → ℝ) {p : MvPolynomial (κ ⊕ ι) ℝ} {n : ℕ}
    (hp : IsWeightedHomogeneous polyWt p n) :
    formalLap q (rhoSq * p) = rhoSq * formalLap q p + C (4 * n + fischerConst ι q) * p := by
  have hA : ∀ a : κ, C 4 * (X (Sum.inl a) * pderiv (Sum.inl a) (pderiv (Sum.inl a) (rhoSq * p))) +
      C (4 * q a) * pderiv (Sum.inl a) (rhoSq * p) =
      rhoSq * (C 4 * (X (Sum.inl a) * pderiv (Sum.inl a) (pderiv (Sum.inl a) p)) +
        C (4 * q a) * pderiv (Sum.inl a) p) +
      4 * (2 * (X (Sum.inl a) * pderiv (Sum.inl a) p)) + 4 * C (q a) * p := by
    intro a
    have h1 : pderiv (Sum.inl a) (rhoSq * p) = p + rhoSq * pderiv (Sum.inl a) p := by
      rw [pderiv_mul, pderiv_inl_rhoSq, one_mul]
    have h2 : pderiv (Sum.inl a) (pderiv (Sum.inl a) (rhoSq * p)) =
        2 * pderiv (Sum.inl a) p + rhoSq * pderiv (Sum.inl a) (pderiv (Sum.inl a) p) := by
      rw [h1, map_add, pderiv_mul, pderiv_inl_rhoSq, one_mul]
      ring
    rw [h2, h1]
    simp only [map_mul, map_ofNat]
    ring
  have hI : ∀ i : ι, pderiv (Sum.inr i) (pderiv (Sum.inr i) (rhoSq * p)) =
      rhoSq * pderiv (Sum.inr i) (pderiv (Sum.inr i) p) +
      4 * (X (Sum.inr i) * pderiv (Sum.inr i) p) + 2 * p := by
    intro i
    have h1 : pderiv (Sum.inr i) (rhoSq * p) =
        C 2 * X (Sum.inr i) * p + rhoSq * pderiv (Sum.inr i) p := by
      rw [pderiv_mul, pderiv_inr_rhoSq]
    rw [h1]
    simp only [map_add, pderiv_mul, pderiv_C, pderiv_X_self, pderiv_inr_rhoSq]
    simp only [map_ofNat]
    ring
  have hE := euler_split hp
  rw [formalLap_apply, formalLap_apply, Finset.sum_congr rfl fun a _ => hA a,
    Finset.sum_congr rfl fun i _ => hI i]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hE ⊢
  rw [fischerConst]
  simp only [map_add, map_mul, map_sum, map_natCast, map_ofNat]
  linear_combination 4 * hE

/-- Iterating the Fischer identity on a harmonic `h` of degree `m`:
`L_q(ρ^{2(j+1)} h) = (j+1)(4m + C₀ + 4j) ρ^{2j} h`. -/
theorem formalLap_rhoSq_pow_mul (q : κ → ℝ) {h : MvPolynomial (κ ⊕ ι) ℝ} {m : ℕ}
    (hh : formalLap q h = 0) (hm : IsWeightedHomogeneous polyWt h m) (j : ℕ) :
    formalLap q (rhoSq ^ (j + 1) * h) =
      C (((j : ℝ) + 1) * (4 * m + fischerConst ι q + 4 * j)) * (rhoSq ^ j * h) := by
  induction j with
  | zero =>
    rw [pow_one, formalLap_rhoSq_mul q hm, hh, mul_zero, zero_add, pow_zero, one_mul]
    congr 2
    push_cast
    ring
  | succ j ih =>
    have hdeg : IsWeightedHomogeneous polyWt (rhoSq ^ (j + 1) * h) (2 * (j + 1) + m) := by
      have := (rhoSq_isWeightedHomogeneous (κ := κ) (ι := ι)).pow (j + 1)
      simpa [mul_comm] using this.mul hm
    rw [pow_succ', mul_assoc, formalLap_rhoSq_mul q hdeg, ih]
    rw [show rhoSq * (C (((j : ℝ) + 1) * (4 * m + fischerConst ι q + 4 * j)) * (rhoSq ^ j * h)) =
      C (((j : ℝ) + 1) * (4 * m + fischerConst ι q + 4 * j)) * (rhoSq ^ (j + 1) * h) by ring,
      ← add_mul, ← map_add]
    congr 2
    push_cast
    ring

/-- **The Fischer decomposition.** If `C₀ > 0`, every weighted homogeneous `p` of degree `n` is
`∑_{j ≤ n/2} ρ^{2j} h_j` with `L_q h_j = 0` and `h_j` weighted homogeneous of degree `n - 2j`. -/
theorem fischer (q : κ → ℝ) (hq : 0 < fischerConst ι q) :
    ∀ (n : ℕ) (p : MvPolynomial (κ ⊕ ι) ℝ), IsWeightedHomogeneous polyWt p n →
      ∃ h : ℕ → MvPolynomial (κ ⊕ ι) ℝ,
        (∀ j ∈ range (n / 2 + 1), formalLap q (h j) = 0 ∧
          IsWeightedHomogeneous polyWt (h j) (n - 2 * j)) ∧
        p = ∑ j ∈ range (n / 2 + 1), rhoSq ^ j * h j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hp
  rcases Nat.lt_or_ge n 2 with hn | hn
  · refine ⟨fun _ => p, fun j hj => ?_, ?_⟩
    · have hj0 : j = 0 := by
        rw [mem_range] at hj
        omega
      subst hj0
      exact ⟨formalLap_eq_zero_of_lt_two q hp hn, by simpa using hp⟩
    · have : n / 2 = 0 := by omega
      rw [this, sum_range_one, pow_zero, one_mul]
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨h', hh', hsum⟩ := ih n' (by omega) (formalLap q p) (formalLap_isWeightedHomogeneous q hp)
  -- the coefficients `A_{j+1}(n' - 2j)`
  set A : ℕ → ℝ := fun j => ((j : ℝ) + 1) * (4 * ((n' - 2 * j : ℕ) : ℝ) + fischerConst ι q + 4 * j)
  have hA : ∀ j, 0 < A j := fun j => by
    simp only [A]
    positivity
  set h0 := p - ∑ j ∈ range (n' / 2 + 1), rhoSq ^ (j + 1) * (C (A j)⁻¹ * h' j)
  refine ⟨fun j => Nat.casesOn j h0 fun j => C (A j)⁻¹ * h' j, fun j hj => ?_, ?_⟩
  · rcases j with _ | j
    · refine ⟨?_, ?_⟩
      · show formalLap q h0 = 0
        rw [map_sub, map_sum]
        rw [Finset.sum_congr rfl fun j hj => (show formalLap q (rhoSq ^ (j + 1) * (C (A j)⁻¹ * h' j))
            = rhoSq ^ j * h' j by
          rw [show rhoSq ^ (j + 1) * (C (A j)⁻¹ * h' j) = C (A j)⁻¹ * (rhoSq ^ (j + 1) * h' j) by
            ring, show C (A j)⁻¹ * (rhoSq ^ (j + 1) * h' j) = (A j)⁻¹ • (rhoSq ^ (j + 1) * h' j) by
            rw [smul_eq_C_mul], map_smul, formalLap_rhoSq_pow_mul q (hh' j hj).1 (hh' j hj).2,
            smul_eq_C_mul, ← mul_assoc, ← map_mul]
          simp only [A]
          rw [inv_mul_cancel₀ (hA j).ne', map_one, one_mul])]
        rw [← hsum, sub_self]
      · show IsWeightedHomogeneous polyWt h0 (n' + 2 - 2 * 0)
        rw [mul_zero, Nat.sub_zero]
        refine hp.sub (IsWeightedHomogeneous.sum _ _ _ fun j hj => ?_)
        have h1 := ((rhoSq_isWeightedHomogeneous (κ := κ) (ι := ι)).pow (j + 1)).mul
          ((hh' j hj).2.C_mul (A j)⁻¹)
        have hj' : 2 * j ≤ n' := by
          rw [mem_range] at hj
          omega
        convert h1 using 1
        simp only [smul_eq_mul]
        omega
    · have hj' : j ∈ range (n' / 2 + 1) := by
        rw [mem_range] at hj ⊢
        omega
      refine ⟨?_, ?_⟩
      · show formalLap q (C (A j)⁻¹ * h' j) = 0
        rw [← smul_eq_C_mul, map_smul, (hh' j hj').1, smul_zero]
      · show IsWeightedHomogeneous polyWt (C (A j)⁻¹ * h' j) (n' + 2 - 2 * (j + 1))
        convert (hh' j hj').2.C_mul (A j)⁻¹ using 1
        omega
  · show p = ∑ j ∈ range ((n' + 2) / 2 + 1),
      rhoSq ^ j * Nat.casesOn (motive := fun _ => MvPolynomial (κ ⊕ ι) ℝ) j h0
        (fun j => C (A j)⁻¹ * h' j)
    rw [show (n' + 2) / 2 + 1 = n' / 2 + 1 + 1 by omega, sum_range_succ']
    simp only [Nat.rec_zero, pow_zero, one_mul, h0]
    ring

/-! ### The span of the harmonic generators -/

/-- The polynomials `ρ^{2j} h` with `L_q h = 0` and `h` weighted homogeneous of degree `m`,
recorded with `m`. -/
def harmonicGen (q : κ → ℝ) : Set (MvPolynomial (κ ⊕ ι) ℝ) :=
  {p | ∃ (j m : ℕ) (h : MvPolynomial (κ ⊕ ι) ℝ), formalLap q h = 0 ∧
    IsWeightedHomogeneous polyWt h m ∧ p = rhoSq ^ j * h}

/-- **Every polynomial is a combination of `ρ^{2j} h` with `h` harmonic and weighted
homogeneous.** -/
theorem mem_span_harmonicGen (q : κ → ℝ) (hq : 0 < fischerConst ι q)
    (p : MvPolynomial (κ ⊕ ι) ℝ) : p ∈ Submodule.span ℝ (harmonicGen q) := by
  classical
  have hp := sum_weightedHomogeneousComponent (w := polyWt (κ := κ) (ι := ι)) (φ := p)
  rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp p)] at hp
  rw [← hp]
  refine Submodule.sum_mem _ fun n _ => ?_
  obtain ⟨h, hh, hsum⟩ := fischer q hq n _
    (weightedHomogeneousComponent_isWeightedHomogeneous n p)
  rw [hsum]
  exact Submodule.sum_mem _ fun j hj =>
    Submodule.subset_span ⟨j, n - 2 * j, h j, (hh j hj).1, (hh j hj).2, rfl⟩

end ConicalKahler.Sobolev
