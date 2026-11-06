module

public import ConicalKahler.Real.D2
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Locality and linearity of the coordinate operators `pd` and `𝒟₂`

The coordinate partial derivatives `pd k U c` are one-variable derivatives along the coordinate
lines `t ↦ c[k := t]` (`D2.lean`). Here:

* **locality**: `pd`, `coneLaplacian`, `paperLaplacian` and the operators `D ∈ 𝒟₂` at `c` only
  depend on the germ of `U` at `c` (`pd_congr`, `D2Op.apply_congr`, `paperLaplacian_congr`);
* **derivatives**: `pd k U c = DU(c) e_k` for `U` differentiable at `c`, and
  `pd k (pd l U) c = D²U(c)(e_k, e_l)` for `U` of class `C²` at `c` (`pd_eq_fderiv`,
  `pd_pd_eq_fderiv`);
* **linearity** on `C²` germs: `D2Op.apply_add`, `D2Op.apply_const_smul`, `paperLaplacian_add`;
* the coordinate derivatives of constants, coordinates and quadratic monomials.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open Filter Topology
open scoped ContDiff

namespace ConicalKahler

variable {κ ι : Type}

/-- The polar coordinate variables are `κ ⊕ κ ⊕ ι`. -/
def ConeVar.equivSum : ConeVar κ ι ≃ κ ⊕ κ ⊕ ι where
  toFun
    | .r a => .inl a
    | .θ a => .inr (.inl a)
    | .s i => .inr (.inr i)
  invFun
    | .inl a => .r a
    | .inr (.inl a) => .θ a
    | .inr (.inr i) => .s i
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with a | a | i <;> rfl

instance [Fintype κ] [Fintype ι] : Fintype (ConeVar κ ι) :=
  Fintype.ofEquiv _ ConeVar.equivSum.symm

variable [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

/-! ### Smoothness of the polar coordinate map -/

theorem contDiff_polarMap {n : WithTop ℕ∞} : ContDiff ℝ n polarMap := by
  unfold polarMap
  exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).mul
    (Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const))

/-- **The polar coordinate map `(r_a, θ_a, s_i) ↦ (r_a e^{iθ_a}, s_i)` is smooth.** -/
theorem PolarPoint.contDiff_toModel {n : WithTop ℕ∞} :
    ContDiff ℝ n (PolarPoint.toModel (κ := κ) (ι := ι)) := by
  refine (contDiff_piLp 2).mpr fun k => ?_
  have hp : ∀ a : κ, ContDiff ℝ n fun c : PolarPoint κ ι => polarMap (c (.r a), c (.θ a)) :=
    fun a => contDiff_polarMap.comp ((contDiff_apply ℝ ℝ _).prodMk (contDiff_apply ℝ ℝ _))
  rcases k with ⟨i, a⟩ | j
  · fin_cases i
    · simpa [PolarPoint.toModel, RealConeModel.ofCones, Function.comp_def] using
        Complex.reCLM.contDiff.comp (hp a)
    · simpa [PolarPoint.toModel, RealConeModel.ofCones, Function.comp_def] using
        Complex.imCLM.contDiff.comp (hp a)
  · simpa [PolarPoint.toModel, RealConeModel.ofCones] using contDiff_apply ℝ ℝ (ConeVar.s j)

/-- The regular part `{r_a > 0}` of the polar coordinates. -/
def regularPolar (κ ι : Type) : Set (PolarPoint κ ι) := {c | ∀ a, 0 < c (.r a)}

theorem isOpen_regularPolar : IsOpen (regularPolar κ ι) := by
  rw [regularPolar, Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun a => isOpen_lt continuous_const (continuous_apply _)

theorem toModel_cone_ne_zero {c : PolarPoint κ ι} (hc : c ∈ regularPolar κ ι) (a : κ) :
    c.toModel.cone a ≠ 0 := by
  rw [PolarPoint.cone_toModel]
  exact polarMap_ne_zero (hc a)

/-! ### Locality -/

section Locality

variable {U V : PolarPoint κ ι → ℝ} {c : PolarPoint κ ι}

theorem pd_congr (h : U =ᶠ[𝓝 c] V) (k : ConeVar κ ι) : pd k U c = pd k V c := by
  unfold pd
  refine Filter.EventuallyEq.deriv_eq ?_
  have hc : Function.update c k (c k) = c := Function.update_eq_self k c
  rw [← hc] at h
  exact (hasDerivAt_update c k (c k)).continuousAt.tendsto.eventually h

theorem pd_eventuallyEq (h : U =ᶠ[𝓝 c] V) (k : ConeVar κ ι) : pd k U =ᶠ[𝓝 c] pd k V :=
  h.eventuallyEq_nhds.mono fun _ hc' => pd_congr hc' k

theorem pd_pd_congr (h : U =ᶠ[𝓝 c] V) (k l : ConeVar κ ι) :
    pd k (pd l U) c = pd k (pd l V) c :=
  pd_congr (pd_eventuallyEq h l) k

theorem coneLaplacian_congr (h : U =ᶠ[𝓝 c] V) (b : ℝ) (a : κ) :
    coneLaplacian b a U c = coneLaplacian b a V c := by
  simp only [coneLaplacian, pd_pd_congr h, pd_congr h]

theorem paperLaplacian_congr (β : κ → ConeAngle) (h : U =ᶠ[𝓝 c] V) :
    paperLaplacian β U c = paperLaplacian β V c := by
  simp only [paperLaplacian, coneLaplacian_congr h, pd_pd_congr h]

theorem D2Op.apply_congr {β : κ → ConeAngle} (h : U =ᶠ[𝓝 c] V) (D : D2Op β ι) :
    D.apply U c = D.apply V c := by
  cases D <;> simp only [D2Op.apply, pd_pd_congr h, coneLaplacian_congr h]

end Locality

/-! ### Coordinate derivatives as Fréchet derivatives -/

section Fderiv

variable {U V : PolarPoint κ ι → ℝ} {c : PolarPoint κ ι}

/-- `∂U/∂x_k (c) = DU(c) e_k`. -/
theorem pd_eq_fderiv (hU : DifferentiableAt ℝ U c) (k : ConeVar κ ι) :
    pd k U c = fderiv ℝ U c (Pi.single k 1) :=
  (hU.hasFDerivAt.comp_hasDerivAt_of_eq (c k) (hasDerivAt_update c k (c k))
    (Function.update_eq_self k c).symm).deriv

/-- `∂²U/∂x_k∂x_l (c) = D²U(c)(e_k, e_l)` for `U` of class `C²` at `c`. -/
theorem pd_pd_eq_fderiv (hU : ContDiffAt ℝ 2 U c) (k l : ConeVar κ ι) :
    pd k (pd l U) c = fderiv ℝ (fderiv ℝ U) c (Pi.single k 1) (Pi.single l 1) := by
  have hev : pd l U =ᶠ[𝓝 c] fun c' => fderiv ℝ U c' (Pi.single l 1) := by
    filter_upwards [hU.eventually (by simp)] with c' hc'
    exact pd_eq_fderiv (hc'.differentiableAt (by norm_num)) l
  have hD : DifferentiableAt ℝ (fderiv ℝ U) c :=
    (hU.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [pd_congr hev, pd_eq_fderiv (hD.clm_apply (differentiableAt_const _)),
    fderiv_clm_apply hD (differentiableAt_const _)]
  simp

theorem pd_add (hU : DifferentiableAt ℝ U c) (hV : DifferentiableAt ℝ V c) (k : ConeVar κ ι) :
    pd k (U + V) c = pd k U c + pd k V c := by
  rw [pd_eq_fderiv (hU.add hV), pd_eq_fderiv hU, pd_eq_fderiv hV, fderiv_add hU hV]
  rfl

theorem pd_const_smul (hU : DifferentiableAt ℝ U c) (a : ℝ) (k : ConeVar κ ι) :
    pd k (a • U) c = a * pd k U c := by
  rw [pd_eq_fderiv (hU.const_smul a), pd_eq_fderiv hU, fderiv_const_smul hU a]
  rfl

theorem pd_pd_add (hU : ContDiffAt ℝ 2 U c) (hV : ContDiffAt ℝ 2 V c) (k l : ConeVar κ ι) :
    pd k (pd l (U + V)) c = pd k (pd l U) c + pd k (pd l V) c := by
  rw [pd_pd_eq_fderiv (show ContDiffAt ℝ 2 (U + V) c from hU.add hV), pd_pd_eq_fderiv hU,
    pd_pd_eq_fderiv hV]
  have hev : fderiv ℝ (U + V) =ᶠ[𝓝 c] fderiv ℝ U + fderiv ℝ V := by
    filter_upwards [hU.eventually (by simp), hV.eventually (by simp)] with c' h1 h2
    exact fderiv_add (h1.differentiableAt (by norm_num)) (h2.differentiableAt (by norm_num))
  have hDU : DifferentiableAt ℝ (fderiv ℝ U) c :=
    (hU.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDV : DifferentiableAt ℝ (fderiv ℝ V) c :=
    (hV.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [hev.fderiv_eq, fderiv_add hDU hDV]
  rfl

theorem pd_pd_const_smul (hU : ContDiffAt ℝ 2 U c) (a : ℝ) (k l : ConeVar κ ι) :
    pd k (pd l (a • U)) c = a * pd k (pd l U) c := by
  rw [pd_pd_eq_fderiv (show ContDiffAt ℝ 2 (a • U) c from hU.const_smul a), pd_pd_eq_fderiv hU]
  have hev : fderiv ℝ (a • U) =ᶠ[𝓝 c] a • fderiv ℝ U := by
    filter_upwards [hU.eventually (by simp)] with c' h1
    exact fderiv_const_smul (h1.differentiableAt (by norm_num)) a
  have hDU : DifferentiableAt ℝ (fderiv ℝ U) c :=
    (hU.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [hev.fderiv_eq, fderiv_const_smul hDU a]
  rfl

theorem coneLaplacian_add (hU : ContDiffAt ℝ 2 U c) (hV : ContDiffAt ℝ 2 V c) (b : ℝ) (a : κ) :
    coneLaplacian b a (U + V) c = coneLaplacian b a U c + coneLaplacian b a V c := by
  simp only [coneLaplacian, pd_pd_add hU hV,
    pd_add (hU.differentiableAt (by norm_num)) (hV.differentiableAt (by norm_num))]
  ring

theorem coneLaplacian_const_smul (hU : ContDiffAt ℝ 2 U c) (r b : ℝ) (a : κ) :
    coneLaplacian b a (r • U) c = r * coneLaplacian b a U c := by
  simp only [coneLaplacian, pd_pd_const_smul hU, pd_const_smul (hU.differentiableAt (by norm_num))]
  ring

theorem paperLaplacian_add (β : κ → ConeAngle) (hU : ContDiffAt ℝ 2 U c)
    (hV : ContDiffAt ℝ 2 V c) :
    paperLaplacian β (U + V) c = paperLaplacian β U c + paperLaplacian β V c := by
  simp only [paperLaplacian, coneLaplacian_add hU hV, pd_pd_add hU hV, Finset.sum_add_distrib]
  ring

theorem paperLaplacian_const_smul (β : κ → ConeAngle)
    (hU : ContDiffAt ℝ 2 U c) (r : ℝ) :
    paperLaplacian β (r • U) c = r * paperLaplacian β U c := by
  simp only [paperLaplacian, coneLaplacian_const_smul hU, pd_pd_const_smul hU, mul_add,
    Finset.mul_sum]

/-- **The operators of `𝒟₂` are additive on `C²` germs.** -/
theorem D2Op.apply_add {β : κ → ConeAngle} (hU : ContDiffAt ℝ 2 U c) (hV : ContDiffAt ℝ 2 V c)
    (D : D2Op β ι) : D.apply (U + V) c = D.apply U c + D.apply V c := by
  cases D <;> simp only [D2Op.apply, pd_pd_add hU hV, coneLaplacian_add hU hV] <;> ring

theorem D2Op.apply_const_smul {β : κ → ConeAngle} (hU : ContDiffAt ℝ 2 U c) (r : ℝ)
    (D : D2Op β ι) : D.apply (r • U) c = r * D.apply U c := by
  cases D <;> simp only [D2Op.apply, pd_pd_const_smul hU, coneLaplacian_const_smul hU] <;> ring

end Fderiv

/-! ### Constants, coordinates and quadratic monomials -/

section Monomials

@[simp] theorem pd_const (k : ConeVar κ ι) (a : ℝ) :
    pd k (fun _ : PolarPoint κ ι => a) = fun _ => 0 := by
  funext c
  simp [pd]

@[simp] theorem pd_zero (k : ConeVar κ ι) : pd k (0 : PolarPoint κ ι → ℝ) = 0 :=
  pd_const k 0

theorem D2Op.apply_zero {β : κ → ConeAngle} (D : D2Op β ι) (c : PolarPoint κ ι) :
    D.apply 0 c = 0 := by
  cases D <;> simp [D2Op.apply, coneLaplacian]

theorem pd_coord (k j : ConeVar κ ι) :
    pd k (fun c : PolarPoint κ ι => c j) = fun _ => if j = k then 1 else 0 := by
  funext c
  unfold pd
  by_cases h : j = k
  · subst h
    simp
  · simp [h]

theorem pd_coord_mul (k i j : ConeVar κ ι) :
    pd k (fun c : PolarPoint κ ι => c i * c j) =
      fun c => (if i = k then c j else 0) + (if j = k then c i else 0) := by
  funext c
  have hi : HasDerivAt (fun t => Function.update c k t i) (if i = k then 1 else 0) (c k) := by
    by_cases h : i = k
    · subst h
      simpa using hasDerivAt_id' (c i)
    · simpa [Function.update_of_ne h, h] using hasDerivAt_const (c k) (c i)
  have hj : HasDerivAt (fun t => Function.update c k t j) (if j = k then 1 else 0) (c k) := by
    by_cases h : j = k
    · subst h
      simpa using hasDerivAt_id' (c j)
    · simpa [Function.update_of_ne h, h] using hasDerivAt_const (c k) (c j)
  unfold pd
  convert (hi.mul hj).deriv using 1
  simp only [Function.update_eq_self]
  split_ifs <;> ring

theorem pd_coord_sq (k j : ConeVar κ ι) :
    pd k (fun c : PolarPoint κ ι => c j ^ 2) = fun c => if j = k then 2 * c j else 0 := by
  have h := pd_coord_mul k j j
  simp only [← sq] at h
  rw [h]
  funext c
  split_ifs <;> ring

theorem pd_ite_coord (k j : ConeVar κ ι) (P : Prop) [Decidable P] (c : PolarPoint κ ι) :
    pd k (fun c : PolarPoint κ ι => if P then c j else 0) c = if P ∧ j = k then 1 else 0 := by
  by_cases h : P
  · simp only [h, ↓reduceIte, true_and, pd_coord]
  · simp [h]

theorem differentiableAt_ite_coord (j : ConeVar κ ι) (P : Prop) [Decidable P] (c : PolarPoint κ ι) :
    DifferentiableAt ℝ (fun c : PolarPoint κ ι => if P then c j else 0) c := by
  by_cases h : P
  · simpa [h] using differentiableAt_apply (𝕜 := ℝ) j c
  · simp [h]

/-- Second coordinate derivatives of `x_i x_j`. -/
theorem pd_pd_coord_mul (k l i j : ConeVar κ ι) (c : PolarPoint κ ι) :
    pd k (pd l fun c : PolarPoint κ ι => c i * c j) c =
      (if i = l ∧ j = k then 1 else 0) + (if j = l ∧ i = k then 1 else 0) := by
  rw [pd_coord_mul]
  have h := pd_add (differentiableAt_ite_coord j (i = l) c) (differentiableAt_ite_coord i (j = l) c) k
  simp only [Pi.add_def] at h
  rw [h, pd_ite_coord, pd_ite_coord]

theorem pd_pd_coord_sq (k l j : ConeVar κ ι) (c : PolarPoint κ ι) :
    pd k (pd l fun c : PolarPoint κ ι => c j ^ 2) c = if j = l ∧ j = k then 2 else 0 := by
  have h := pd_pd_coord_mul k l j j c
  simp only [← sq] at h
  rw [h]
  split_ifs <;> norm_num

end Monomials

/-! ### Finite sums and the harmonic functions `r^{k/β} sin kθ` -/

section Sums

variable {c : PolarPoint κ ι}

theorem paperLaplacian_sum (β : κ → ConeAngle) {α : Type*} (s : Finset α)
    {U : α → PolarPoint κ ι → ℝ} (hU : ∀ j ∈ s, ContDiffAt ℝ 2 (U j) c) :
    paperLaplacian β (fun c' => ∑ j ∈ s, U j c') c = ∑ j ∈ s, paperLaplacian β (U j) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [paperLaplacian, coneLaplacian]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have h1 : ContDiffAt ℝ 2 (U a) c := hU a (Finset.mem_insert_self a s)
    have h2 : ContDiffAt ℝ 2 (fun c' => ∑ j ∈ s, U j c') c :=
      ContDiffAt.sum fun j hj => hU j (Finset.mem_insert_of_mem hj)
    rw [show (fun c' => U a c' + ∑ j ∈ s, U j c') = U a + fun c' => ∑ j ∈ s, U j c' from rfl,
      paperLaplacian_add β h1 h2, ih fun j hj => hU j (Finset.mem_insert_of_mem hj)]

theorem paperLaplacian_const_mul (β : κ → ConeAngle) {U : PolarPoint κ ι → ℝ}
    (hU : ContDiffAt ℝ 2 U c) (r : ℝ) :
    paperLaplacian β (fun c' => r * U c') c = r * paperLaplacian β U c :=
  paperLaplacian_const_smul β hU r

theorem D2Op.apply_sum {β : κ → ConeAngle} (D : D2Op β ι) {α : Type*} (s : Finset α)
    {U : α → PolarPoint κ ι → ℝ} (hU : ∀ j ∈ s, ContDiffAt ℝ 2 (U j) c) :
    D.apply (fun c' => ∑ j ∈ s, U j c') c = ∑ j ∈ s, D.apply (U j) c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    cases D <;> simp [D2Op.apply, coneLaplacian]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have h1 : ContDiffAt ℝ 2 (U a) c := hU a (Finset.mem_insert_self a s)
    have h2 : ContDiffAt ℝ 2 (fun c' => ∑ j ∈ s, U j c') c :=
      ContDiffAt.sum fun j hj => hU j (Finset.mem_insert_of_mem hj)
    rw [show (fun c' => U a c' + ∑ j ∈ s, U j c') = U a + fun c' => ∑ j ∈ s, U j c' from rfl,
      D2Op.apply_add h1 h2, ih fun j hj => hU j (Finset.mem_insert_of_mem hj)]

theorem paperLaplacian_r_sq (β : κ → ConeAngle) (b : κ) {c : PolarPoint κ ι} (hc : 0 < c (.r b)) :
    paperLaplacian β (fun c' => c' (.r b) ^ 2) c = 4 := by
  simp only [paperLaplacian, coneLaplacian, pd_pd_coord_sq]
  simp only [pd_coord_sq]
  simp only [ConeVar.r.injEq, reduceCtorEq, and_self, ↓reduceIte, mul_zero, add_zero,
    Finset.sum_const_zero]
  rw [Finset.sum_eq_single b (fun a _ hab => by simp [Ne.symm hab]) (by simp)]
  simp only [↓reduceIte]
  field_simp
  norm_num

theorem paperLaplacian_s_mul (β : κ → ConeAngle) (i j : ι) (c : PolarPoint κ ι) :
    paperLaplacian β (fun c' => c' (.s i) * c' (.s j)) c = if i = j then 2 else 0 := by
  simp only [paperLaplacian, coneLaplacian, pd_pd_coord_mul]
  simp only [pd_coord_mul]
  simp only [reduceCtorEq, and_false, ↓reduceIte, add_zero, mul_zero,
    Finset.sum_const_zero, zero_add, ConeVar.s.injEq]
  by_cases h : i = j
  · subst h
    simp only [and_self, ↓reduceIte]
    rw [Finset.sum_eq_single i (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
    norm_num
  · simp only [h, ↓reduceIte]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : i = l
    · subst hl
      simp [Ne.symm h]
    · simp [hl]

/-- **`r_a^{k/β_a} sin(kθ_a)` is harmonic** for the paper's Laplacian on the regular part. -/
theorem paperLaplacian_harmonicSin (β : κ → ConeAngle) (k : ℕ) (a : κ) {c : PolarPoint κ ι}
    (hr : 0 < c (.r a)) : paperLaplacian β (harmonicSin (β a).beta k a) c = 0 := by
  have hs : ∑ i, pd (.s i) (pd (.s i) (harmonicSin (β a).beta k a)) c = 0 :=
    Finset.sum_eq_zero fun i _ => by simp [pd, harmonicSin]
  rw [paperLaplacian, hs, add_zero, Finset.sum_eq_single a]
  · exact coneLaplacian_harmonicSin (β a).pos k a hr
  · exact fun b _ hb =>
      coneLaplacian_factor_of_ne (fun x y => coneHarmonicSin (β a).beta k x y) a c _ hb
  · simp

end Sums

end ConicalKahler
