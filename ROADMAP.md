# Roadmap: Schauder estimates on products of cones

Long-term target: a formal proof of the main theorem of

> M. de Borbon and G. Edwards, *Schauder estimates on products of cones*,
> Comment. Math. Helv. **96** (2021), 113–148; arXiv:2002.07668.

All references below are to **arXiv:2002.07668v1** (18 Feb 2020; the only arXiv version), with
its page numbers. The journal version was not consulted, and its numbering may differ.

**Status legend.**
- **Proved**: a kernel-checked Lean declaration exists in this repository. The name is given.
- **Planned**: not formalised. It is an intended application or a future milestone.

Only the Proved entries are theorems of this repository.

---

## 1. Dictionary between the paper and this project

The paper and this project normalise differently. Every entry below is backed by a Lean statement.

| Paper | This project | Lean evidence |
|---|---|---|
| cone factor `C(S¹_{2πβ})` with metric `dr² + β²r² dθ²`, `r` = distance to the apex | complex coordinate `z_j`, Hermitian form `q = β² \|z_j\|^{2β-2} \|dz_j\|²`, with `r = ρ = \|z_j\|^β` | `transverseConeMetric_polar` (`q = dρ² + β²ρ² dθ²`) |
| `g = ∑_a (dr_a² + β_a² r_a² dθ_a²) + ds²` | `q = modelConeQuadratic θ`, i.e. **half** the Riemannian metric `g = ω_θ(·, J·)` of `ModelConeForm θ` | `modelConeForm_apply_I_smul` (`ω(v, Jv) = 2q`) |
| `Δ = ∑_a Δ_{β_a} + Δ_{ℝ^{m-2n}}`, `Δ_β = ∂_r² + r⁻¹∂_r + (βr)⁻²∂_θ²` | `laplaceBeltrami (ModelConeForm θ) = ½ Δ_paper` | `laplaceBeltrami_modelConeFormOn`, `coordLaplacian_div_modelWeight_conePolar`, `laplaceBeltrami_standardCone_polar` |
| `Δ_β r² = 4` | `Δ_g ρ_j² = 2` | `laplaceBeltrami_potentialTerm` |
| harmonic functions `r^{k/β} cos kθ`, `r^{k/β} sin kθ` | `coneHarmonicCos β k ρ θ`, `coneHarmonicSin` = `Re z^k`, `Im z^k` | `coneHarmonicCos_polar_eq_zero`, `re_pow_coordSlice_conePolar`, `laplaceBeltrami_re_pow_eq_zero` |
| dilations `λ(r_a, θ_a, s) = (λr_a, θ_a, λs)`, homothety of `g` | `coneDilation θ λ` (`z_j ↦ λ^{1/β_j} z_j` or `λ z_j`) | `modelConeQuadratic_coneDilation` (`q ↦ λ² q`) |
| Euclidean coordinates `s ∈ ℝ^{m-2n}` | complex Euclidean factors `z_j` (`θ_j = none`) | |
| the identification with `ℝ^m` reading `(r_a, θ_a)` as polar coordinates (eq. (2.1)) | the radial change `(r, θ) ↦ (r^β, βθ)` / `w = \|z\|^{β-1} z` | `coneRadialChange`, `coneRadialChangeHomeomorph` |
| complex coordinate `z = (βr)^{1/β} e^{iθ}` (corrected; §5.1 and App. A.2 contain typos) | ours is `z_ours = β^{-1/β} z_paper`: `ρ = \|z_ours\|^β` and `q = β² \|z_ours\|^{2β-2}\|dz_ours\|²` | |
| angles `0 < β_a < 1` | models for all `β > 0`; chart invariance for `β ≤ 1` | `IsQuasiIsometricSNCCone.forall_chart_of_le_one` |

**Two scope differences that matter.**
1. **Dimension.** The paper allows any `m ≥ 3`, including odd `m` (e.g. `m = 3`, `C(S¹_{2πβ}) × ℝ`).
   This project works on `ℂⁿ`, so `m = 2n` is even and Euclidean factors come in complex pairs.
   Odd `m`, and the paper's alternative `m = 3` proof (§3.5.1, which needs De Giorgi–Nash–Moser),
   are outside the current framework.
2. **Hölder spaces.** The paper's `C^α` is Hölder for the cone distance `d_g`. That is Euclidean
   Hölder in the coordinates `(r_a cos θ_a, r_a sin θ_a)`, **not** in the complex coordinate `z`.
   Function spaces must therefore be set up in the `w = |z|^{β-1} z` coordinates (or intrinsically).

---

## 2. The target theorem (paper, Theorem 1.1, p. 2)

**Exponent** (eq. (1.1)):

  `μ = min{ 1;  1/β_a − 1 for β_a ≥ 1/2;  1/β_a − 2 for β_a < 1/2 }`.

**Operators `𝒟₂`** (p. 2):
- pure Euclidean: `∂²_{s_i s_j}`;
- mixed conical–Euclidean: `∂²_{r_a s_i}` and `r_a⁻¹ ∂²_{θ_a s_i}`;
- mixed conical, `a ≠ b`: `∂²_{r_a r_b}`, `(r_a r_b)⁻¹ ∂²_{θ_a θ_b}` and `r_b⁻¹ ∂²_{r_a θ_b}`;
- the conical Laplacians `Δ_{β_a}`;
- pure conical, **only if `β_a < 1/2`**: `∂²_{r_a}`, `r_a⁻² ∂²_{θ_a}` and `r_a⁻¹ ∂²_{r_a θ_a}`.

**Theorem 1.1.** Let `0 < α < μ`. There is `C = C(α, β_a, m)` such that the following holds. Let
`u ∈ W^{1,2}(B_2)` be a weak solution of `Δu = f` with `f ∈ C^α(B_2)`. Then for every `x ∈ B_1`
and `D ∈ 𝒟₂` there are `τ ∈ ℝ` and `K > 0` with

  `(ρ^{-m} ∫_{B(x,ρ)} |Du − τ|²)^{1/2} ≤ K ρ^α`  for all `0 < ρ < 1`,

and `|τ| + K ≤ C (|f(x)| + |f|_{C^α(x)} + ‖u‖_{L²(B_2)})`.

Here `B_r` are balls centred at the vertex, `B(x, ρ)` is a `d_g`-ball, and integrals are taken
against `dV_g = (∏ β_a) · Lebesgue` in the paper's coordinates. The pointwise Hölder coefficient is
`|f|_{C^α(x)} = sup_{d(x,y)<1} |f(y) − f(x)| / d(x,y)^α`.

**Formalisation decisions to make before stating it in Lean** (all **Planned**):
- **Meaning of the pure conical operators.** Coordinate derivatives and orthonormal-frame Hessian
  components differ by first-order terms. The paper does not say which is meant (extraction §2.3).
  Recommended: frame Hessian components plus `Δ_{β_a}`.
- **Hölder exponent.** State the estimate in the Campanato form above, and derive Hölder
  continuity of `Du` separately (Lemma 2.6).
- **Coordinates.** Work in the paper's real coordinates. In this project those are reached
  through `coneRadialChange` on each cone factor.

---

## 3. Ingredients of the proof and their status

Paper labels are given as `[P]` (proved in the paper), `[P*]` (proved with a gap), `[O]` (proof
omitted) and `[C]` (cited from the literature).

### 3.1 Elementary harmonic analysis on the model

| Ingredient (paper) | Status |
|---|---|
| Model metric, its Laplacian, product structure (§1.1, p. 2) | **Proved**: `laplaceBeltrami_modelConeFormOn`, `laplaceBeltrami_modelConeFormOn_split` |
| `Δ_β` in polar coordinates | **Proved**: `coordLaplacian_conePolar`, `laplaceBeltrami_standardCone_polar` |
| `r^{k/β} cos kθ`, `r^{k/β} sin kθ` harmonic (App. A.2, (A.1)) | **Proved**: `coneHarmonicCos_polar_eq_zero`, `coneHarmonicSin_polar_eq_zero`, `laplaceBeltrami_re_pow_eq_zero`, `laplaceBeltrami_im_pow_eq_zero` |
| homogeneity and dilations (§2.5) | **Proved**: `coneHarmonicCos_homogeneous`, `re_pow_coneDilate`, `modelConeQuadratic_coneDilation` |
| derivative bounds `|∂_r u| ≲ r^{k/β-1}` etc. (used for the optimality examples, p. 3) | **Proved**: `coneHarmonicCos_bounds`, `coneHarmonicSin_bounds`, `coneHarmonicCos_gradNormSq` |
| degree-2 functions `r_a² − r_b²`, `r_a² − (s_1² + s_2²)` harmonic (Prop. 3.4(3)) | **Proved**: `laplaceBeltrami_potentialTerm_sub` |
| `1`, `s_i`, `r_a^{1/β_a} cos θ_a` (Prop. 3.4(1)–(2)) harmonic | **Proved** as `Re`/`Im` of `z_j` (`k = 1`) |
| barrier `ε ∑_a log r_a` harmonic off `S` (Lemma 3.2) | **Proved**: `laplaceBeltrami_log_coordNormSq_eq_zero` |
| pluriharmonic functions are harmonic for every Kähler form | **Proved**: `laplaceBeltrami_eq_zero_of_ddbar_eq_zero`, `laplaceBeltrami_re_eq_zero` |
| **completeness**: `𝓗_{≤2}` is *exactly* the list of Prop. 3.4, and there is no homogeneous harmonic function of degree in `(2, 2+μ)` | Planned. This is the hard part of §3: the spectral theorem on the link (Lemma 3.1), Sturm–Liouville and Frobenius theory for (3.2) (§§3.3–3.4), and induction on `n`. A Fourier decomposition in each `θ_a` may be a more elementary route. |
| Corollary 3.5: `DP` is constant for `D ∈ 𝒟₂`, `P ∈ 𝓗_{≤2}` | Planned (explicit computation once `𝒟₂` is fixed) |
| Lemma 2.2: log cut-off with small Dirichlet energy | Planned (explicit) |
| Lemma 4.2, monotonicity at the vertex | Planned (elementary given the expansion) |

### 3.2 Metric geometry

| Ingredient | Status |
|---|---|
| distance `d_g`, balls `B(x,ρ)`, `(min β)² g_ℝ^m ≤ g ≤ g_ℝ^m` (eq. (2.1)) | Planned. Only tensor-level facts are proved (`ConicalKahler.Cone.FlatCone`). No metric space is constructed. |
| geometry of balls in the 2D cone after cuts (App. A.1; the constant `c_β` has a typo) | Planned |
| Lemma 4.1: finitely many bad scales | Planned (elementary given App. A.1) |
| `dV_g = (∏ β_a) dx` | Planned |

### 3.3 Sobolev spaces and weak solutions

| Ingredient | Status | Possible source |
|---|---|---|
| `W^{1,2}`, `W^{1,2}_0` on balls, weak formulation (2.2) | Planned | upstream `Sobolev.Euclidean.MemW1p`, `MemH01` (in the paper's real coordinates) |
| density of `C_c^∞(reg)` (codim-2 capacity) | Planned | Lemma 2.2 |
| Poincaré, existence by Riesz/Lax–Milgram, uniqueness | Planned | upstream `poincare_unitBall_W1p_public`; Lax–Milgram is in EllipticPDE (see §4) |
| Lemma 2.3, Caccioppoli | Planned | EllipticPDE `Regularity.caccioppoli` (bounded measurable coefficients) |
| Lemma 2.4, harmonic approximation (Rellich and weak limits) | Planned | upstream `rellich_kondrachov_W01p_seq` |
| Lemma 3.1, spectral theorem on the link | Planned | |
| Lemma 3.3, expansion of `W^{1,2}` harmonic functions (gap: continuity up to the boundary) | Planned | energy-uniqueness repair suggested in extraction §6 |
| **Prop. 2.5**, interior `L²` Hessian bound; uses the cited Lipschitz bound for Dirichlet eigenfunctions [Mon17], [BKMR18, Prop. 5.4] | Planned. **The heaviest analytic input**, and the only deep external regularity result on the main line. Boundary terms are dropped in the paper (its equalities should be `≤`). | |
| local `C^{2,α}` regularity off the singular set | Planned | upstream `interiorSchauderEstimate_all` (interior Schauder on `ℂⁿ`) |

### 3.4 Campanato theory and the iteration

| Ingredient | Status | Possible source |
|---|---|---|
| Lemma 2.6, Campanato ⇒ Hölder (uses doubling of `g`-balls) | Planned | EllipticPDE `Campanato.Haar.campanato_holderOnWith` (Euclidean balls). It needs transport to `d_g`-balls. |
| Lemma 2.7, summing increments over geometric scales | Planned (elementary) | |
| Lemma 4.3, monotonicity off the vertex | Planned | |
| Prop. 5.1, key step; iteration of §5 | Planned | |

---

## 4. Reuse of existing Lean libraries

**calabi-yau (our dependency, pinned).** Checked at the pinned commit, all usable now:
- Laplacian:
  - `CalabiYau.Riemannian.ΔG` (Laplace–Beltrami), already used here as `laplaceBeltrami`;
  - `KahlerForm.riemannian_laplacian_eq_two_mul_laplacian`.
- Euclidean Sobolev, vendored from DeGiorgi:
  - `Sobolev.Euclidean.MemW1p p f Ω μ` (with weights), `MemW01p`, `MemH01`;
  - `poincare_unitBall_W1p_public`, `sobolev_poincare_unitBall`, `rellich_kondrachov_W01p_seq`.
- Hölder spaces: `HolderBoundOn`.
- Interior Schauder on `ℂⁿ`: `InteriorSchauderEstimate`, proved as `interiorSchauderEstimate_all`.
- Coordinates: `complexToRealCoordinateEquiv : E n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n × Fin 2)`.
- Absent: Campanato spaces, Caccioppoli, De Giorgi–Nash–Moser, and the mean-value property.

**EllipticPDE** (github.com/alejandro-soto-franco/EllipticPDE, Apache-2.0, commit `0ccb4cf9`,
2026-10-28; surveyed, not built).

*Contents:*
- No `sorry` or axioms in the library.
- `H¹₀(μ)` for general measures.
- Lax–Milgram (`lax_milgram`), Gårding and Fredholm for bounded measurable coefficients.
- Caccioppoli (`Regularity.caccioppoli`).
- `L²` order-0 Campanato ⇔ Hölder (`Campanato.Haar.campanato_holderOnWith`, `campanatoOn_of_holderOnWith`).
- Interior `H²`/`C^∞` regularity, for Lipschitz or smooth coefficients only.
- **No** De Giorgi–Nash–Moser, Harnack, Schauder estimates or mean-value property.

*Compatibility:* **it cannot be added as a Lake dependency.*
- It pins Lean `v4.35.0-rc3` and Mathlib `c55e6e78`.
- Lake keeps a single Mathlib, so it would be compiled against our `v4.34.1` without ever having been tested there.
- Porting this project to v4.35 is blocked because calabi-yau has no v4.35 version.

*Options:*
- (a) vendor selected files under Apache-2.0 with a NOTICE, as calabi-yau did for DeGiorgi. The likely candidates are the Campanato files and the Lax–Milgram/Caccioppoli files;
- (b) fork and backport to v4.34.1. The name-level scan found only 3 call sites of lemmas newer than v4.34.1, but this is unverified without a build.

*Caveat for weighted spaces:* its `W12 μ` integrates by parts against `μ`, so it is not the
weighted Sobolev space. Upstream's `MemW1p … μ` is. In the paper's real coordinates the cone
Laplacian has bounded measurable, uniformly elliptic coefficients, so Lebesgue measure suffices.

No incompatible dependency has been added.

---

## 5. Proposed milestones

1. **Real coordinates and the cone distance.**
   - The paper's coordinates `(r_a cos θ_a, r_a sin θ_a, s)` as a global homeomorphism of the
     model, built from `coneRadialChange` on each factor.
   - The metric comparison (2.1) and `dV_g`.
   - The cone distance `d_g` with its comparison to the Euclidean distance.
2. **`𝒟₂` and `𝓗_{≤2}` (explicit part).**
   - Fix the meaning of `𝒟₂`.
   - Prove Corollary 3.5 for the explicit list.
   - Prove the optimality examples of p. 3: `r^{1/β} s cos θ` is harmonic and its `∂_r∂_s` is
     exactly `C^{1/β-1}`.
3. **Weak solutions** on balls centred at the vertex. Use upstream `MemW1p` in real coordinates,
   plus Poincaré, existence and uniqueness, Caccioppoli, and the density of `C_c^∞(reg)`.
4. **Completeness of `𝓗_{≤2+α}`** (Prop. 3.4) by separation of variables.
5. **The `L²` Hessian bound** (Prop. 2.5): decide between formalising or assuming the Lipschitz
   bound for eigenfunctions.
6. **Campanato iteration** (Lemmas 2.6, 2.7, 4.1, 4.3, Prop. 5.1, §5).

**Known issues in the paper to handle** (details in the extraction):
- Complex-coordinate normalisation typos (§5.1, App. A.2): `k²β²` should be `k²/β²`, a sign in
  `L_{0,0}`, `(m−3)⁻¹` should be `(m−2)⁻¹`, and `c_β = sin πβ` should be its reciprocal.
- Boundary terms dropped in Prop. 2.5.
- A continuity gap in Lemma 3.3.
- Uniformity in the centre in Lemma 2.4 and Prop. 5.1.
- The case `β_a = 1/2`.
