/-
# O'Meara §82F–§82G: the dual of a lattice and modular lattices over a Dedekind domain

**Setting.** $R$ is a Dedekind domain with fraction field $F$, $2 \in F^\times$, and $(V, Q)$ a quadratic space over
$F$ with O'Meara's bilinear form $B$ = `bil Q` ($B(x, x) = Q(x)$). Lattices, fractional ideals, $\mathfrak aL$
(`a • L`) and $\mathfrak a^{-1}$ (`1 / a`) are as in `Sec81.lean`; scale, norm, volume, regular and
$\mathfrak a$-modular lattices are the definitions of `Sec82.lean`.

**Defines** the dual $L^\# = \{x \in FL : B(x, L) \subseteq \mathfrak o\}$ of a lattice (`dual`, §82F, p. 230).
(The library has the dual of a lattice over $\mathbb Z$ in coordinates, `Lattices.omearaDual`, and the unimodularity
condition at a place of a number field, `IsUnimodularAt`; `dual` is the general definition.)

**Proves** (O'Meara 1963, §82F–§82G, pp. 230–233):
* `dual_eq_of_adapted` ($L = \sum\mathfrak a_ix_i$ gives $L^\# = \sum\mathfrak a_i^{-1}y_i$, $y$ the dual base),
  `span_dual`, `dual_dual`, `dual_smul`, `volume_dual_mul`, `IsOrthSum.dual`, `dual_anti`, `dual_sup` (§82F,
  pp. 230–231);
* `isUnimodular_iff_gram` (**82:13**);
* `isModular_iff_smul_dual` (**82:14**), `Dedekind.mem_of_isModular` (**82:14a**), `isUnimodular_iff_dual_eq`
  (**82:14b**);
* `Dedekind.splits_iff_of_isModular` (**82:15**), `Dedekind.splits_of_isModular_of_scale_eq` (**82:15a**);
* `exists_binary_split_of_isModular` (**82:16**);
* `isModular_iff_forall_isMaxVec` (**82:17**, $\mathfrak o$ a principal ideal domain).
-/
import QuadFormsKB.Literature.OMeara.Sec82Volume
import QuadFormsKB.Literature.OMeara.Sec82Radical

open QuadraticMap Submodule Module
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Defs

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **The dual of a lattice** $L^\# = \{x \in FL : B(x, L) \subseteq \mathfrak o\}$ (O'Meara 1963, §82F, p. 230;
O'Meara defines it for regular $L$). -/
@[kb "omeara1963" "§82F, p. 230 (the dual L#)"]
def dual (L : Submodule R V) : Submodule R V where
  carrier := {x | x ∈ span F (L : Set V) ∧ ∀ y ∈ L, bil Q x y ∈ (1 : Submodule R F)}
  add_mem' := by
    rintro x x' ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨add_mem hx hy, fun z hz => ?_⟩
    rw [bil_add_left]; exact add_mem (hx' z hz) (hy' z hz)
  zero_mem' := ⟨zero_mem _, fun z _ => by simp [bil]⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    refine ⟨?_, fun z hz => ?_⟩
    · rw [← algebraMap_smul F c x]; exact smul_mem _ _ hx
    · rw [bil_rsmul_left, ← Algebra.smul_def]; exact smul_mem _ c (hx' z hz)

theorem mem_dual {L : Submodule R V} {x : V} :
    x ∈ dual Q L ↔ x ∈ span F (L : Set V) ∧ ∀ y ∈ L, bil Q x y ∈ (1 : Submodule R F) := Iff.rfl

end Defs

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- Squares of non-zero fractional ideals determine them (unique factorization in a Dedekind domain). -/
theorem sq_inj_of_fg {p q : Submodule R F} (hp : p.FG) (hp0 : p ≠ ⊥) (hq : q.FG) (hq0 : q ≠ ⊥)
    (h : p ^ 2 = q ^ 2) : p = q := by
  let P : FractionalIdeal (nonZeroDivisors R) F := ⟨p, FractionalIdeal.isFractional_of_fg hp⟩
  let Q : FractionalIdeal (nonZeroDivisors R) F := ⟨q, FractionalIdeal.isFractional_of_fg hq⟩
  have hP : P ≠ 0 := by
    intro h0; apply hp0
    have := congrArg (fun J : FractionalIdeal (nonZeroDivisors R) F => (J : Submodule R F)) h0
    simpa [P] using this
  have hQ : Q ≠ 0 := by
    intro h0; apply hq0
    have := congrArg (fun J : FractionalIdeal (nonZeroDivisors R) F => (J : Submodule R F)) h0
    simpa [Q] using this
  have h2 : P ^ 2 = Q ^ 2 := by
    apply FractionalIdeal.coeToSubmodule_injective
    show ((P ^ 2 : FractionalIdeal (nonZeroDivisors R) F) : Submodule R F) =
      ((Q ^ 2 : FractionalIdeal (nonZeroDivisors R) F) : Submodule R F)
    rw [FractionalIdeal.coe_pow, FractionalIdeal.coe_pow]
    exact h
  have key : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      FractionalIdeal.count F v P = FractionalIdeal.count F v Q := by
    intro v
    have := congrArg (FractionalIdeal.count F v) h2
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_pow] at this
    push_cast at this
    omega
  have : P = Q := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' F hP,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' F hQ]
    exact finprod_congr fun v => by rw [key v]
  have h3 := congrArg (fun J : FractionalIdeal (nonZeroDivisors R) F => (J : Submodule R F)) this
  exact h3

/-- If $I \le \mathfrak a$ and $I^r = \mathfrak a^r$ with $r \ge 1$, then $I = \mathfrak a$ (fractional ideal $\mathfrak a$). -/
theorem eq_of_le_of_pow_eq {I a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {r : ℕ} (hr : 1 ≤ r)
    (hle : I ≤ a) (hpow : I ^ r = a ^ r) : I = a := by
  have h1 := mul_one_div_cancel_of_fg ha ha0
  set J : Submodule R F := I * (1 / a) with hJ
  have hJ1 : J ≤ 1 := h1 ▸ mul_le_mul' hle le_rfl
  have hJr : J ^ r = 1 := by
    rw [hJ, mul_pow, hpow, ← mul_pow, h1, one_pow]
  have hJle : J ^ r ≤ J := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    calc J ^ (s + 1) = J ^ s * J := pow_succ J s
      _ ≤ 1 * J := mul_le_mul' (pow_le_one' hJ1 s) le_rfl
      _ = J := one_mul J
  have hJeq : J = 1 := le_antisymm hJ1 (hJr ▸ hJle)
  calc I = I * (1 / a) * a := by
        rw [mul_assoc, mul_comm (1 / a) a, h1, mul_one]
    _ = a := by rw [← hJ, hJeq, one_mul]

/-- $1/(1/\mathfrak a) = \mathfrak a$ for a fractional ideal. -/
theorem one_div_one_div {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) : 1 / (1 / a) = a := by
  obtain ⟨hf, hn⟩ := one_div_fg ha ha0
  have h1 := mul_one_div_cancel_of_fg ha ha0
  have h2 := mul_one_div_cancel_of_fg hf hn
  calc 1 / (1 / a) = (a * (1 / a)) * (1 / (1 / a)) := by rw [h1, one_mul]
    _ = a * ((1 / a) * (1 / (1 / a))) := by ring
    _ = a := by rw [h2, mul_one]

/-- $1/(\mathfrak a\mathfrak b) = (1/\mathfrak a)(1/\mathfrak b)$ for fractional ideals. -/
theorem one_div_mul {a b : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) (hb : b.FG) (hb0 : b ≠ ⊥) :
    1 / (a * b) = (1 / a) * (1 / b) := by
  have hab0 : a * b ≠ ⊥ := by
    rw [← Submodule.zero_eq_bot] at *
    exact mul_ne_zero ha0 hb0
  have h1 := mul_one_div_cancel_of_fg (ha.mul hb) hab0
  have h2 := mul_one_div_cancel_of_fg ha ha0
  have h3 := mul_one_div_cancel_of_fg hb hb0
  refine mul_left_cancel_of_fg (ha.mul hb) hab0 ?_
  rw [h1]
  calc (1 : Submodule R F) = (a * (1 / a)) * (b * (1 / b)) := by rw [h2, h3, mul_one]
    _ = _ := by ring

/-- $B(\sum_i c_iy_i, \gamma x_j) = c_j\gamma$ for biorthogonal families. -/
theorem bil_biorth_smul {r : ℕ} (x y : Fin r → V)
    (hxy : ∀ i j, bil Q (x i) (y j) = if i = j then 1 else 0) (c : Fin r → F) (γ : F) (i : Fin r) :
    bil Q (∑ j, c j • y j) (γ • x i) = c i * γ := by
  rw [bil_sum_left]
  simp only [bil_smul_left, bil_smul_right]
  have : ∀ j, bil Q (y j) (x i) = if i = j then 1 else 0 := fun j => by rw [bil_comm]; exact hxy i j
  simp [this, mul_comm]

/-- $B(\sum_i c_iy_i, \sum_j \gamma_jx_j) = \sum_i c_i\gamma_i$ for biorthogonal families. -/
theorem bil_sum_biorth {r : ℕ} (x y : Fin r → V)
    (hxy : ∀ i j, bil Q (x i) (y j) = if i = j then 1 else 0) (c γ : Fin r → F) :
    bil Q (∑ i, c i • y i) (∑ j, γ j • x j) = ∑ i, c i * γ i := by
  rw [bil_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bil_biorth_smul Q x y hxy c (γ j) j, mul_comm]

/-- A family biorthogonal to another is linearly independent. -/
theorem linearIndependent_of_biorth {r : ℕ} (x y : Fin r → V)
    (hxy : ∀ i j, bil Q (x i) (y j) = if i = j then 1 else 0) : LinearIndependent F y := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have := congrArg (bil Q (x i)) hc
  rw [bil_sum_right] at this
  simpa [bil_smul_right, hxy] using this

/-- A family with non-zero discriminant has a biorthogonal family in its span. -/
theorem exists_biorth {r : ℕ} (x : Fin r → V) (hdet : (gram Q x).det ≠ 0) :
    ∃ y : Fin r → V, (∀ j, y j ∈ span F (Set.range x)) ∧
      ∀ i j, bil Q (x i) (y j) = if i = j then 1 else 0 := by
  have hU : IsUnit (gram Q x).det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨fun j => ∑ k, (gram Q x)⁻¹ j k • x k, fun j => sum_mem fun k _ =>
    smul_mem _ _ (subset_span ⟨k, rfl⟩), fun i j => ?_⟩
  simp only [bil_sum_right, bil_smul_right]
  have h1 : (gram Q x)⁻¹ * gram Q x = 1 := Matrix.nonsing_inv_mul _ hU
  have h2 := congrFun (congrFun h1 j) i
  rw [Matrix.mul_apply] at h2
  rw [Matrix.one_apply] at h2
  have : ∀ k, bil Q (x i) (x k) = gram Q x k i := fun k => by simp [gram, bil_comm Q (x k)]
  simp only [this]
  rw [h2]
  by_cases h : i = j <;> simp [h, eq_comm]

/-- Discriminants of biorthogonal families multiply to $1$. -/
theorem det_gram_biorth_mul {r : ℕ} (x y : Fin r → V) (hy : ∀ j, y j ∈ span F (Set.range x))
    (hxy : ∀ i j, bil Q (x i) (y j) = if i = j then 1 else 0) :
    (gram Q y).det * (gram Q x).det = 1 := by
  choose M hM using fun j => (mem_span_range_iff_exists_fun F).1 (hy j)
  have hy' : y = fun j => ∑ k, Matrix.of M j k • x k := funext fun j => by simp [hM j]
  have hGM : gram Q x * (Matrix.of M)ᵀ = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have := hxy i j
    rw [← hM j] at this
    simp only [bil_sum_right, bil_smul_right] at this
    rw [show (∑ k, gram Q x i k * (Matrix.of M)ᵀ k j) = ∑ k, M j k * bil Q (x i) (x k) from
      Finset.sum_congr rfl fun k _ => by simp [gram, mul_comm], this]
  have hdet : (gram Q x).det * (Matrix.of M).det = 1 := by
    rw [← Matrix.det_transpose (Matrix.of M), ← Matrix.det_mul, hGM, Matrix.det_one]
  rw [hy', gram_comb_F, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  calc (Matrix.of M).det * (gram Q x).det * (Matrix.of M).det * (gram Q x).det
      = ((gram Q x).det * (Matrix.of M).det) ^ 2 := by ring
    _ = 1 := by rw [hdet, one_pow]

/-- **A lattice with an adaptation and a dual family**: a regular lattice $L$ is
$\mathfrak a_1x_1 + \cdots + \mathfrak a_rx_r$ with $x$ a base of $FL$, and there is a dual family $y$. -/
theorem exists_dual_adapted [FiniteDimensional F V] {L : Submodule R V} (hL : L.FG) (hreg : IsRegular Q L) :
    ∃ (r : ℕ) (x y : Fin r → V) (a : Fin r → Submodule R F), LinearIndependent F x ∧
      span F (Set.range x) = span F (L : Set V) ∧ (∀ i, (a i).FG ∧ a i ≠ ⊥) ∧
      L = ⨆ i, a i • span R {x i} ∧ (∀ j, y j ∈ span F (Set.range x)) ∧
      ∀ i j, bil Q (x i) (y j) = if i = j then 1 else 0 := by
  obtain ⟨r, x, hx, hxs, a, ha, hLeq⟩ := exists_adapted (F := F) hL
  have hreg' : IsRegular Q (⨆ i, a i • span R {x i}) := hLeq ▸ hreg
  have hdet := (isRegular_adapted_iff Q x hx a fun i => (ha i).2).1 hreg'
  obtain ⟨y, hy, hxy⟩ := exists_biorth Q x hdet
  exact ⟨r, x, y, a, hx, hxs, ha, hLeq, hy, hxy⟩

/-- A biorthogonal family in the span of an independent family spans the same space. -/
theorem span_biorth_eq {r : ℕ} (x y : Fin r → V) (hx : LinearIndependent F x)
    (hy : ∀ j, y j ∈ span F (Set.range x))
    (hxy : ∀ i j, bil Q (x i) (y j) = if i = j then 1 else 0) :
    span F (Set.range y) = span F (Set.range x) := by
  have hyi : LinearIndependent F y := linearIndependent_of_biorth Q x y hxy
  have : FiniteDimensional F (span F (Set.range x)) := FiniteDimensional.span_of_finite F (Set.finite_range x)
  exact Submodule.eq_of_le_of_finrank_eq (span_le.2 (by rintro _ ⟨j, rfl⟩; exact hy j))
    (by rw [finrank_span_eq_card hyi, finrank_span_eq_card hx])

/-- Biorthogonality is symmetric. -/
theorem biorth_symm {r : ℕ} (x y : Fin r → V)
    (hxy : ∀ i j, bil Q (x i) (y j) = if i = j then 1 else 0) :
    ∀ i j, bil Q (y i) (x j) = if i = j then 1 else 0 := fun i j => by
  rw [bil_comm, hxy]
  by_cases h : i = j <;> simp [h, eq_comm]

/-- A product of non-zero submodules of $F$ is non-zero. -/
theorem mul_ne_bot' {p q : Submodule R F} (hp : p ≠ ⊥) (hq : q ≠ ⊥) : p * q ≠ ⊥ :=
  fun h => (Submodule.mul_eq_bot.1 h).elim hp hq

/-- $\mathfrak b\cdot\mathfrak c N = (\mathfrak b\mathfrak c) N$. -/
theorem mul_smul_submodule (b c : Submodule R F) (N : Submodule R V) : (b * c) • N = b • c • N :=
  Submodule.smul_assoc b c N

/-- $\mathfrak c(\sum \mathfrak a_i x_i) = \sum (\mathfrak c\mathfrak a_i) x_i$. -/
theorem smul_adapted (c : Submodule R F) {r : ℕ} (a : Fin r → Submodule R F) (x : Fin r → V) :
    c • (⨆ i, a i • span R {x i} : Submodule R V) = ⨆ i, (c * a i) • span R {x i} := by
  rw [Submodule.smul_iSup]
  exact iSup_congr fun i => (mul_smul_submodule c (a i) _).symm

/-- $\mathfrak b\,Rx$ is the image of $\mathfrak b$ under $\alpha \mapsto \alpha x$. -/
theorem smul_span_singleton_eq_map (b : Submodule R F) (y : V) :
    b • span R {y} = b.map ((LinearMap.toSpanSingleton F V y).restrictScalars R) := by
  ext v
  rw [mem_smul_span_singleton_iff', Submodule.mem_map]
  constructor
  · rintro ⟨γ, hγ, rfl⟩; exact ⟨γ, hγ, rfl⟩
  · rintro ⟨γ, hγ, rfl⟩; exact ⟨γ, hγ, rfl⟩

/-- An adaptation by finitely generated ideals is finitely generated. -/
theorem fg_adapted {r : ℕ} (a : Fin r → Submodule R F) (ha : ∀ i, (a i).FG) (x : Fin r → V) :
    (⨆ i, a i • span R {x i} : Submodule R V).FG :=
  Submodule.fg_iSup _ fun i => by rw [smul_span_singleton_eq_map]; exact (ha i).map _

/-- **The dual in an adapted base** (O'Meara 1963, §82F, p. 230). If $L = \mathfrak a_1x_1 + \cdots + \mathfrak a_rx_r$
with $x_1, \dots, x_r$ a base of $FL$ and fractional ideals $\mathfrak a_i$, and $y_1, \dots, y_r \in FL$ is the dual
base ($B(x_i, y_j) = \delta_{ij}$), then $L^\# = \mathfrak a_1^{-1}y_1 + \cdots + \mathfrak a_r^{-1}y_r$. -/
@[kb "omeara1963" "§82F, p. 230 (L# = a₁⁻¹y₁ + ⋯ + a_r⁻¹y_r)"]
theorem dual_eq_of_adapted {r : ℕ} (x : Fin r → V) (hx : LinearIndependent F x) (a : Fin r → Submodule R F)
    (ha : ∀ i, (a i).FG ∧ a i ≠ ⊥) (y : Fin r → V)
    (hy : ∀ j, y j ∈ span F (Set.range x)) (hxy : ∀ i j, bil Q (x i) (y j) = if i = j then 1 else 0) :
    dual Q (⨆ i, a i • span R {x i}) = ⨆ i, (1 / a i) • span R {y i} := by
  have hyi : LinearIndependent F y := linearIndependent_of_biorth Q x y hxy
  have hspan : span F (Set.range y) = span F (Set.range x) := span_biorth_eq Q x y hx hy hxy
  have hLspan : span F ((⨆ i, a i • span R {x i} : Submodule R V) : Set V) = span F (Set.range y) := by
    rw [span_adapted a (fun i => (ha i).2) x, hspan]
  ext z
  rw [mem_dual, hLspan, mem_iSup_smul_span_iff_exists]
  constructor
  · rintro ⟨hz, hB⟩
    obtain ⟨β, rfl⟩ := (mem_span_range_iff_exists_fun F).1 hz
    refine ⟨β, fun i => ?_, rfl⟩
    rw [Submodule.mem_div_iff_forall_mul_mem]
    intro γ hγ
    have hmem : γ • x i ∈ (⨆ i, a i • span R {x i} : Submodule R V) :=
      mem_iSup_of_mem i (smul_mem_smul hγ (mem_span_singleton_self _))
    have := hB _ hmem
    rwa [bil_biorth_smul Q x y hxy β γ i] at this
  · rintro ⟨c, hc, rfl⟩
    refine ⟨sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩), fun l hl => ?_⟩
    obtain ⟨γ, hγ, rfl⟩ := (mem_iSup_smul_span_iff_exists a x l).1 hl
    rw [bil_sum_biorth Q x y hxy]
    exact sum_mem fun i _ => (Submodule.mem_div_iff_forall_mul_mem.1 (hc i)) _ (hγ i)

/-- **$FL^\# = FL$** (O'Meara 1963, §82F, p. 231), for a regular lattice $L$. -/
@[kb "omeara1963" "§82F, p. 231 (FL# = FL)"]
theorem span_dual [FiniteDimensional F V] {L : Submodule R V} (hL : L.FG) (hreg : IsRegular Q L) :
    span F (dual Q L : Set V) = span F (L : Set V) := by
  obtain ⟨r, x, y, a, hx, hxs, ha, hLeq, hy, hxy⟩ := exists_dual_adapted Q hL hreg
  have hd : dual Q L = ⨆ i, (1 / a i) • span R {y i} := by
    rw [hLeq]; exact dual_eq_of_adapted Q x hx a ha y hy hxy
  rw [hd, span_adapted (fun i => 1 / a i) (fun i => (one_div_fg (ha i).1 (ha i).2).2) y,
    span_biorth_eq Q x y hx hy hxy, hxs]

/-- **The dual is a lattice** (O'Meara 1963, §82F, p. 231). -/
theorem dual_fg [FiniteDimensional F V] {L : Submodule R V} (hL : L.FG) (hreg : IsRegular Q L) :
    (dual Q L).FG := by
  obtain ⟨r, x, y, a, hx, hxs, ha, hLeq, hy, hxy⟩ := exists_dual_adapted Q hL hreg
  have hd : dual Q L = ⨆ i, (1 / a i) • span R {y i} := by
    rw [hLeq]; exact dual_eq_of_adapted Q x hx a ha y hy hxy
  rw [hd]
  exact fg_adapted _ (fun i => (one_div_fg (ha i).1 (ha i).2).1) y

/-- **$L^{\#\#} = L$** (O'Meara 1963, §82F, p. 231), for a regular lattice $L$. -/
@[kb "omeara1963" "§82F, p. 231 (L## = L)"]
theorem dual_dual [FiniteDimensional F V] {L : Submodule R V} (hL : L.FG) (hreg : IsRegular Q L) :
    dual Q (dual Q L) = L := by
  obtain ⟨r, x, y, a, hx, hxs, ha, hLeq, hy, hxy⟩ := exists_dual_adapted Q hL hreg
  have hyi : LinearIndependent F y := linearIndependent_of_biorth Q x y hxy
  have hspan := span_biorth_eq Q x y hx hy hxy
  have hd : dual Q L = ⨆ i, (1 / a i) • span R {y i} := by
    rw [hLeq]; exact dual_eq_of_adapted Q x hx a ha y hy hxy
  rw [hd, dual_eq_of_adapted Q y hyi (fun i => 1 / a i) (fun i => one_div_fg (ha i).1 (ha i).2) x
    (fun j => hspan ▸ subset_span ⟨j, rfl⟩) (biorth_symm Q x y hxy), hLeq]
  exact iSup_congr fun i => by rw [one_div_one_div (ha i).1 (ha i).2]

/-- **$(\mathfrak aL)^\# = \mathfrak a^{-1}L^\#$** (O'Meara 1963, §82F, p. 231) for a fractional ideal
$\mathfrak a$ and a regular lattice $L$. -/
@[kb "omeara1963" "§82F, p. 231 ((aL)# = a⁻¹L#)"]
theorem dual_smul [FiniteDimensional F V] {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {L : Submodule R V}
    (hL : L.FG) (hreg : IsRegular Q L) : dual Q (a • L) = (1 / a) • dual Q L := by
  obtain ⟨r, x, y, b, hx, hxs, hb, hLeq, hy, hxy⟩ := exists_dual_adapted Q hL hreg
  have hab : ∀ i, (a * b i).FG ∧ a * b i ≠ ⊥ := fun i => ⟨ha.mul (hb i).1, mul_ne_bot' ha0 (hb i).2⟩
  have h1 : a • L = ⨆ i, (a * b i) • span R {x i} := by rw [hLeq, smul_adapted]
  have hd : dual Q L = ⨆ i, (1 / b i) • span R {y i} := by
    rw [hLeq]; exact dual_eq_of_adapted Q x hx b hb y hy hxy
  rw [h1, dual_eq_of_adapted Q x hx (fun i => a * b i) hab y hy hxy, hd, smul_adapted]
  exact iSup_congr fun i => by rw [one_div_mul ha ha0 (hb i).1 (hb i).2]

/-- **$\mathfrak vL^\# = (\mathfrak vL)^{-1}$** (O'Meara 1963, §82F, p. 231), stated as
$\mathfrak vL^\# \cdot \mathfrak vL = \mathfrak o$, for a regular lattice $L$ (by Example 42:5,
$d(x_1, \dots, x_r)\,d(y_1, \dots, y_r) = 1$ for dual bases). -/
@[kb "omeara1963" "§82F, p. 231 (vL# = (vL)⁻¹)"]
theorem volume_dual_mul [FiniteDimensional F V] {L : Submodule R V} (hL : L.FG) (hreg : IsRegular Q L) :
    volume Q (dual Q L) * volume Q L = 1 := by
  obtain ⟨r, x, y, a, hx, hxs, ha, hLeq, hy, hxy⟩ := exists_dual_adapted Q hL hreg
  have hyi : LinearIndependent F y := linearIndependent_of_biorth Q x y hxy
  have hd : dual Q L = ⨆ i, (1 / a i) • span R {y i} := by
    rw [hLeq]; exact dual_eq_of_adapted Q x hx a ha y hy hxy
  rw [hd, hLeq, volume_eq_of_adapted Q y hyi (fun i => 1 / a i)
    (fun i => one_div_fg (ha i).1 (ha i).2), volume_eq_of_adapted Q x hx a ha]
  have hprod : (∏ i, 1 / a i) * ∏ i, a i = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => by rw [mul_comm]; exact mul_one_div_cancel_of_fg (ha i).1 (ha i).2
  have hspan : span R {(gram Q y).det} * span R {(gram Q x).det} = 1 := by
    rw [span_mul_span, Set.singleton_mul_singleton, det_gram_biorth_mul Q x y hy hxy,
      ← Submodule.one_eq_span]
  calc (∏ i, 1 / a i) ^ 2 * span R {(gram Q y).det} * ((∏ i, a i) ^ 2 * span R {(gram Q x).det})
      = ((∏ i, 1 / a i) * ∏ i, a i) ^ 2 * (span R {(gram Q y).det} * span R {(gram Q x).det}) := by ring
    _ = 1 := by rw [hprod, hspan]; simp

/-- **$(J \perp K)^\# = J^\# \perp K^\#$** (O'Meara 1963, §82F, p. 231), for regular lattices $J$, $K$ (only the
regularity of $J$ is used). -/
@[kb "omeara1963" "§82F, p. 231 ((J ⊥ K)# = J# ⊥ K#)"]
theorem IsOrthSum.dual [FiniteDimensional F V] {L J K : Submodule R V} (h : IsOrthSum Q L J K)
    (hJreg : IsRegular Q J) :
    IsOrthSum Q (dual Q L) (dual Q J) (dual Q K) := by
  have hL := h.sup_eq
  subst hL
  have step1 : ∀ u ∈ J, ∀ v ∈ span F (K : Set V), bil Q u v = 0 := fun u hu v hv =>
    bil_zero_of_mem_span_F Q (fun k hk => h.orth u hu k hk) hv
  have step2 : ∀ v ∈ span F (K : Set V), ∀ u ∈ span F (J : Set V), bil Q v u = 0 := fun v hv u hu =>
    bil_zero_of_mem_span_F Q (fun j hj => by rw [bil_comm]; exact step1 j hj v hv) hu
  have hperp : ∀ u ∈ span F (J : Set V), ∀ v ∈ span F (K : Set V), bil Q u v = 0 := fun u hu v hv => by
    rw [bil_comm]; exact step2 v hv u hu
  have hJs : span F (J : Set V) ≤ span F ((J ⊔ K : Submodule R V) : Set V) := span_mono (le_sup_left : J ≤ J ⊔ K)
  have hKs : span F (K : Set V) ≤ span F ((J ⊔ K : Submodule R V) : Set V) := span_mono (le_sup_right : K ≤ J ⊔ K)
  refine ⟨fun x hx y hy => hperp x hx.1 y hy.1, ?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    rintro z ⟨⟨hzJ, -⟩, ⟨hzK, -⟩⟩
    have h0 : z = 0 := (isRegular_iff_span Q J).1 hJreg z hzJ fun w hw =>
      by rw [bil_comm]; exact hperp w hw z hzK
    exact (mem_bot R).2 h0
  · apply le_antisymm
    · refine sup_le ?_ ?_
      · rintro z ⟨hz, hB⟩
        refine ⟨hJs hz, fun l hl => ?_⟩
        obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hl
        rw [bil_add_right, hperp z hz k (subset_span hk), add_zero]
        exact hB j hj
      · rintro z ⟨hz, hB⟩
        refine ⟨hKs hz, fun l hl => ?_⟩
        obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hl
        rw [bil_add_right, bil_comm Q z j, hperp j (subset_span hj) z hz, zero_add]
        exact hB k hk
    · rintro z ⟨hz, hB⟩
      have hz' : z ∈ span F (J : Set V) ⊔ span F (K : Set V) := by
        refine (span_le.2 ?_ : span F ((J ⊔ K : Submodule R V) : Set V) ≤ _) hz
        intro v hv
        obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hv
        exact add_mem (mem_sup_left (subset_span hj)) (mem_sup_right (subset_span hk))
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_sup.mp hz'
      refine mem_sup.mpr ⟨u, ⟨hu, fun j hj => ?_⟩, v, ⟨hv, fun k hk => ?_⟩, rfl⟩
      · have := hB j (mem_sup_left hj)
        rwa [bil_add_left, bil_comm Q v j, hperp j (subset_span hj) v hv, add_zero] at this
      · have := hB k (mem_sup_right hk)
        rwa [bil_add_left, hperp u hu k (subset_span hk), zero_add] at this

/-- **$L \supseteq K \Rightarrow L^\# \subseteq K^\#$** (O'Meara 1963, §82F, p. 231), for lattices on the same
space. -/
@[kb "omeara1963" "§82F, p. 231 (L ⊇ K ⇒ L# ⊆ K#)"]
theorem dual_anti {K L : Submodule R V} (hspan : span F (K : Set V) = span F (L : Set V)) (h : K ≤ L) :
    dual Q L ≤ dual Q K := by
  rintro z ⟨hz, hB⟩
  exact ⟨by rw [hspan]; exact hz, fun k hk => hB k (h hk)⟩

/-- **$(J + K)^\# = J^\# \cap K^\#$** (O'Meara 1963, §82F, p. 231), for lattices on the same space. -/
@[kb "omeara1963" "§82F, p. 231 ((J + K)# = J# ∩ K#)"]
theorem dual_sup {J K : Submodule R V} (hspan : span F (J : Set V) = span F (K : Set V)) :
    dual Q (J ⊔ K) = dual Q J ⊓ dual Q K := by
  have hJK : span F ((J ⊔ K : Submodule R V) : Set V) = span F (J : Set V) := by
    apply le_antisymm
    · rw [span_le]
      intro v hv
      obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hv
      exact add_mem (subset_span hj) (by rw [hspan]; exact subset_span hk)
    · exact span_mono (le_sup_left : J ≤ J ⊔ K)
  ext z
  constructor
  · rintro ⟨hz, hB⟩
    rw [hJK] at hz
    exact ⟨⟨hz, fun j hj => hB j (mem_sup_left hj)⟩,
      ⟨by rw [← hspan]; exact hz, fun k hk => hB k (mem_sup_right hk)⟩⟩
  · rintro ⟨⟨hz, hJ⟩, ⟨-, hK⟩⟩
    refine ⟨by rw [hJK]; exact hz, fun l hl => ?_⟩
    obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hl
    rw [bil_add_right]
    exact add_mem (hJ j hj) (hK k hk)

/-- **Proposition 82:13** (O'Meara 1963, pp. 231–232). A free lattice $L$ with base $b$ and matrix
$M = (B(b_i, b_j))$ is unimodular if and only if $M$ is a unimodular matrix (integral with unit determinant); here
$L \ne 0$ is part of being unimodular, so the base is required to be non-empty. -/
@[kb "omeara1963" "§82G, 82:13, pp. 231–232"]
theorem isUnimodular_iff_gram {L : Submodule R V} {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι R L) :
    IsUnimodular Q L ↔ Nonempty ι ∧ ∃ U : Matrix ι ι R, IsUnit U.det ∧
      gram Q (fun i => (b i : V)) = U.map (algebraMap R F) := by
  have := isModular_iff_gram Q b (one_ne_zero (α := F))
  simp only [one_smul] at this
  rw [IsUnimodular, Submodule.one_eq_span]
  exact this

/-- The dual of a regular lattice is regular. -/
theorem isRegular_dual [FiniteDimensional F V] {L : Submodule R V} (hL : L.FG) (hreg : IsRegular Q L) :
    IsRegular Q (dual Q L) :=
  (isRegular_iff_span Q (dual Q L)).2 (by
    rw [span_dual Q hL hreg]; exact (isRegular_iff_span Q L).1 hreg)

/-- The dual of a regular lattice has the same rank. -/
theorem finrank_dual [FiniteDimensional F V] {L : Submodule R V} (hL : L.FG) (hreg : IsRegular Q L) :
    finrank R (dual Q L) = finrank R L := by
  rw [finrank_eq_finrank_span (F := F) (dual Q L), finrank_eq_finrank_span (F := F) L, span_dual Q hL hreg]

/-- $\mathfrak v(\mathfrak cL) = \mathfrak c^{2r}\,\mathfrak vL$ for a fractional ideal $\mathfrak c$ and a lattice of
rank $r$. -/
theorem volume_smul [FiniteDimensional F V] {c : Submodule R F} (hc : c.FG) (hc0 : c ≠ ⊥) {L : Submodule R V}
    (hL : L.FG) : volume Q (c • L) = c ^ (2 * finrank R L) * volume Q L := by
  obtain ⟨r, x, hx, -, a, ha, hLeq⟩ := exists_adapted (F := F) hL
  have hca : ∀ i, (c * a i).FG ∧ c * a i ≠ ⊥ := fun i => ⟨hc.mul (ha i).1, mul_ne_bot' hc0 (ha i).2⟩
  have hfr : finrank R L = r := by
    rw [hLeq, finrank_adapted a (fun i => (ha i).2) x hx, Fintype.card_fin]
  rw [hfr, hLeq, smul_adapted, volume_eq_of_adapted Q x hx _ hca, volume_eq_of_adapted Q x hx a ha,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← pow_mul]
  rw [mul_comm r 2]
  ring

/-- A modular lattice is regular (over a Dedekind domain). -/
theorem isRegular_of_isModular [FiniteDimensional F V] {a : Submodule R F} {L : Submodule R V}
    (hL : IsModular Q a L) (hLfg : L.FG) : IsRegular Q L := by
  by_contra h
  have h0 := (volume_eq_bot_iff Q hLfg).2 h
  rw [hL.2.2] at h0
  have hne : a ^ finrank R L ≠ 0 := pow_ne_zero _ (by rw [Submodule.zero_eq_bot]; exact hL.1)
  exact hne (by rw [Submodule.zero_eq_bot]; exact h0)

/-- For an $\mathfrak a$-modular lattice, $L^\# = \mathfrak a^{-1}L$ (the easy half of 82:14, with its proof). -/
theorem dual_eq_of_isModular [FiniteDimensional F V] {a : Submodule R F} {L : Submodule R V}
    (hL : IsModular Q a L) (hLfg : L.FG) : dual Q L = (1 / a) • L := by
  have hreg := isRegular_of_isModular Q hL hLfg
  have ha0 := hL.1
  have haf : a.FG := hL.2.1 ▸ scale_fg Q hLfg
  obtain ⟨hif, hin⟩ := one_div_fg haf ha0
  have h1 : (1 / a) * a = 1 := by rw [mul_comm]; exact mul_one_div_cancel_of_fg haf ha0
  have h2 : a * (1 / a) = 1 := mul_one_div_cancel_of_fg haf ha0
  have hKle : (1 / a) • L ≤ dual Q L := by
    rw [Submodule.smul_le]
    intro β hβ l hl
    refine ⟨smul_mem _ _ (subset_span hl), fun l' hl' => ?_⟩
    rw [bil_smul_left]
    have := mul_mem_mul hβ (show bil Q l l' ∈ a by rw [← hL.2.1]; exact bil_mem_scale Q hl hl')
    rwa [h1] at this
  have hDfg := dual_fg Q hLfg hreg
  have hKfg : ((1 / a) • L).FG := fg_of_le_aux hDfg hKle
  have hspan : span F (((1 / a) • L : Submodule R V) : Set V) = span F (dual Q L : Set V) := by
    apply le_antisymm (span_mono hKle)
    rw [span_dual Q hLfg hreg, span_le]
    intro l hl
    obtain ⟨γ, hγ, hγ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hin
    have : γ • l ∈ ((1 / a) • L : Submodule R V) := smul_mem_smul hγ hl
    rw [SetLike.mem_coe]
    have h3 : l = γ⁻¹ • (γ • l) := by rw [smul_smul, inv_mul_cancel₀ hγ0, one_smul]
    rw [h3]
    exact smul_mem _ _ (subset_span this)
  refine (eq_of_le_of_volume_eq Q hKfg hDfg hspan (isRegular_dual Q hLfg hreg) hKle ?_).symm
  -- volumes
  rw [volume_smul Q hif hin hLfg, hL.2.2]
  have hv := volume_dual_mul Q hLfg hreg
  rw [hL.2.2] at hv
  have hr : (a ^ finrank R L).FG := haf.pow _
  have hr0 : a ^ finrank R L ≠ ⊥ := by
    have : a ^ finrank R L ≠ 0 := pow_ne_zero _ (by rw [Submodule.zero_eq_bot]; exact ha0)
    rwa [Submodule.zero_eq_bot] at this
  refine mul_left_cancel_of_fg hr hr0 ?_
  calc a ^ finrank R L * ((1 / a) ^ (2 * finrank R L) * a ^ finrank R L)
      = (a * (1 / a)) ^ (2 * finrank R L) := by
        rw [mul_pow, pow_mul' a, pow_mul' (1 / a)]; ring
    _ = 1 := by rw [h2, one_pow]
    _ = volume Q (dual Q L) * a ^ finrank R L := hv.symm
    _ = _ := mul_comm _ _

/-- **Proposition 82:14** (O'Meara 1963, p. 232). Let $L$ be a non-zero regular lattice and $\mathfrak a$ a fractional
ideal. Then $L$ is $\mathfrak a$-modular if and only if $\mathfrak aL^\# = L$. -/
@[kb "omeara1963" "§82G, 82:14, p. 232"]
theorem isModular_iff_smul_dual [FiniteDimensional F V] {L : Submodule R V} (hL : L.FG) (hL0 : L ≠ ⊥)
    (hreg : IsRegular Q L) {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) :
    IsModular Q a L ↔ a • dual Q L = L := by
  have h2 : a * (1 / a) = 1 := mul_one_div_cancel_of_fg ha ha0
  constructor
  · intro h
    rw [dual_eq_of_isModular Q h hL, ← mul_smul_submodule, h2, Submodule.one_smul]
  · intro h
    have hsc : scale Q L ≤ a := by
      rw [scale, span_le]
      rintro _ ⟨l, hl, l', hl', rfl⟩
      show bil Q l l' ∈ a
      rw [← h] at hl
      refine Submodule.smul_induction_on (p := fun l => bil Q l l' ∈ a) hl
        (fun α hα m hm => ?_) (fun u v hu hv => ?_)
      · rw [bil_smul_left]
        have := mul_mem_mul hα (hm.2 l' hl')
        rwa [mul_one] at this
      · rw [bil_add_left]; exact add_mem hu hv
    have hr1 : 1 ≤ finrank R L := by
      rw [finrank_eq_finrank_span (F := F) L]
      refine Submodule.one_le_finrank_iff.2 fun hb => hL0 ?_
      rw [eq_bot_iff]
      intro l hl
      have := subset_span (R := F) hl
      rw [hb] at this
      exact (mem_bot R).2 ((mem_bot F).1 this)
    have h3 := volume_smul Q ha ha0 (dual_fg Q hL hreg)
    rw [h, finrank_dual Q hL hreg] at h3
    have hv := volume_dual_mul Q hL hreg
    have hvfg := volume_fg Q (F := F) hL
    have hv0 : volume Q L ≠ ⊥ := fun h0 => ((volume_eq_bot_iff Q hL).1 h0) hreg
    have hsq : volume Q L ^ 2 = (a ^ finrank R L) ^ 2 := by
      calc volume Q L ^ 2 = volume Q L * volume Q L := sq _
        _ = (a ^ (2 * finrank R L) * volume Q (dual Q L)) * volume Q L := by rw [← h3]
        _ = a ^ (2 * finrank R L) * (volume Q (dual Q L) * volume Q L) := by ring
        _ = a ^ (2 * finrank R L) := by rw [hv, mul_one]
        _ = (a ^ finrank R L) ^ 2 := by rw [pow_mul']
    have hr0 : a ^ finrank R L ≠ ⊥ := by
      have : a ^ finrank R L ≠ 0 := pow_ne_zero _ (by rw [Submodule.zero_eq_bot]; exact ha0)
      rwa [Submodule.zero_eq_bot] at this
    have hvol : volume Q L = a ^ finrank R L := sq_inj_of_fg hvfg hv0 (ha.pow _) hr0 hsq
    refine ⟨ha0, ?_, hvol⟩
    refine eq_of_le_of_pow_eq ha ha0 hr1 hsc (le_antisymm (pow_le_pow_left' hsc _) ?_)
    have := volume_le_scale_pow Q L
    rwa [hvol] at this

/-- **Corollary 82:14a** (O'Meara 1963, p. 232), over a Dedekind domain. If $L$ is $\mathfrak a$-modular then
$L = \{x \in FL : B(x, L) \subseteq \mathfrak a\}$. -/
@[kb "omeara1963" "§82G, 82:14a, p. 232"]
theorem Dedekind.mem_of_isModular [FiniteDimensional F V] {a : Submodule R F} {L : Submodule R V}
    (hL : IsModular Q a L) (hLfg : L.FG) {x : V} (hx : x ∈ span F (L : Set V))
    (hB : ∀ z ∈ L, bil Q x z ∈ a) : x ∈ L := by
  have hreg := isRegular_of_isModular Q hL hLfg
  have haf : a.FG := hL.2.1 ▸ scale_fg Q hLfg
  have h1 : (1 / a) * a = 1 := by rw [mul_comm]; exact mul_one_div_cancel_of_fg haf hL.1
  have hd := dual_eq_of_isModular Q hL hLfg
  rw [← dual_dual Q hLfg hreg]
  refine ⟨by rw [span_dual Q hLfg hreg]; exact hx, fun m hm => ?_⟩
  rw [hd] at hm
  refine Submodule.smul_induction_on (p := fun m => bil Q x m ∈ (1 : Submodule R F)) hm
    (fun β hβ l hl => ?_) (fun u v hu hv => ?_)
  · rw [bil_smul_right]
    have := mul_mem_mul hβ (hB l hl)
    rwa [h1] at this
  · rw [bil_add_right]; exact add_mem hu hv

/-- **Corollary 82:14b** (O'Meara 1963, p. 232): a non-zero regular lattice $L$ is unimodular if and only if
$L^\# = L$. -/
@[kb "omeara1963" "§82G, 82:14b, p. 232"]
theorem isUnimodular_iff_dual_eq [FiniteDimensional F V] {L : Submodule R V} (hL : L.FG) (hL0 : L ≠ ⊥)
    (hreg : IsRegular Q L) : IsUnimodular Q L ↔ dual Q L = L := by
  have h1fg : (1 : Submodule R F).FG := by rw [Submodule.one_eq_span]; exact fg_span_singleton _
  have h10 : (1 : Submodule R F) ≠ ⊥ := fun h =>
    one_ne_zero ((Submodule.mem_bot R).1 (h ▸ (Submodule.one_le.1 le_rfl : (1 : F) ∈ (1 : Submodule R F))))
  rw [IsUnimodular, isModular_iff_smul_dual Q hL hL0 hreg h1fg h10, Submodule.one_smul]

/-- Orthogonal projection onto $FJ$ for a regular lattice $J$: every $v$ has the same products with $FJ$ as some
$y \in FJ$. -/
theorem exists_proj [FiniteDimensional F V] {J : Submodule R V} (hJ : J.FG) (hreg : IsRegular Q J) (v : V) :
    ∃ y ∈ span F (J : Set V), ∀ w ∈ span F (J : Set V), bil Q y w = bil Q v w := by
  obtain ⟨r, x, y, a, hx, hxs, ha, hLeq, hy, hxy⟩ := exists_dual_adapted Q hJ hreg
  refine ⟨∑ j, bil Q v (x j) • y j, ?_, fun w hw => ?_⟩
  · rw [← hxs]; exact sum_mem fun j _ => smul_mem _ _ (hy j)
  · rw [← hxs] at hw
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun F).1 hw
    rw [bil_sum_right, bil_sum_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bil_smul_right, bil_smul_right, bil_sum_left]
    simp only [bil_smul_left]
    simp [biorth_symm Q x y hxy]

/-- **Proposition 82:15** (O'Meara 1963, pp. 232–233), over a Dedekind domain. An $\mathfrak a$-modular sublattice $J$
of $L$ splits $L$ if and only if $B(J, L) \subseteq \mathfrak a$. -/
@[kb "omeara1963" "§82G, 82:15, pp. 232–233"]
theorem Dedekind.splits_iff_of_isModular [FiniteDimensional F V] {a : Submodule R F} {L J : Submodule R V}
    (hJL : J ≤ L) (hJ : IsModular Q a J) (hJfg : J.FG) :
    (∃ K, IsOrthSum Q L J K) ↔ ∀ x ∈ J, ∀ y ∈ L, bil Q x y ∈ a := by
  constructor
  · rintro ⟨K, hK⟩ x hx y hy
    rw [← hK.sup_eq] at hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := mem_sup.mp hy
    rw [bil_add_right, hK.orth x hx y₂ hy₂, add_zero, ← hJ.2.1]
    exact bil_mem_scale Q hx hy₁
  · intro h
    have hreg := isRegular_of_isModular Q hJ hJfg
    refine ⟨splitComp Q L J, ⟨fun _ hx _ hy => by rw [bil_comm]; exact hy.2 _ hx, ?_, ?_⟩⟩
    · rw [disjoint_iff, eq_bot_iff]
      rintro x ⟨hxJ, hxK⟩
      exact (mem_bot R).mpr (hreg x hxJ fun y hy => hxK.2 y hy)
    · apply le_antisymm
      · exact sup_le hJL fun x hx => hx.1
      · intro x hx
        obtain ⟨y, hyJ, hxy⟩ := exists_proj Q hJfg hreg x
        have hyJ' : y ∈ J := Dedekind.mem_of_isModular Q hJ hJfg hyJ fun z hz => by
          rw [hxy z (subset_span hz), bil_comm]; exact h z hz x hx
        refine mem_sup.mpr ⟨y, hyJ', x - y, ⟨L.sub_mem hx (hJL hyJ'), fun z hz => ?_⟩, by abel⟩
        rw [bil_sub_left, hxy z (subset_span hz), sub_self]

/-- **Corollary 82:15a** (O'Meara 1963, p. 233), over a Dedekind domain: an $\mathfrak a$-modular sublattice $J$ of a
lattice $L$ with $\mathfrak sL = \mathfrak a$ splits $L$. -/
@[kb "omeara1963" "§82G, 82:15a, p. 233"]
theorem Dedekind.splits_of_isModular_of_scale_eq [FiniteDimensional F V] {a : Submodule R F}
    {L J : Submodule R V} (hJL : J ≤ L) (hJ : IsModular Q a J) (hJfg : J.FG) (hL : scale Q L = a) :
    ∃ K, IsOrthSum Q L J K :=
  (Dedekind.splits_iff_of_isModular Q hJL hJ hJfg).mpr fun _ hx _ hy => hL ▸ bil_mem_scale Q (hJL hx) hy

/-- An adaptation $L = \sum \mathfrak b_iy_i$ whose first vector is a non-zero multiple of a given non-zero vector
$x \in FL$ (Theorem 81:3 for a base of $FL$ starting with $x$). -/
theorem exists_adapted_first [FiniteDimensional F V] {L : Submodule R V} (hL : L.FG) {x : V}
    (hxL : x ∈ span F (L : Set V)) (hx0 : x ≠ 0) :
    ∃ (n : ℕ) (y : Fin (n + 1) → V) (b : Fin (n + 1) → Submodule R F) (c : F), LinearIndependent F y ∧
      (∀ i, (b i).FG ∧ b i ≠ ⊥) ∧ L = ⨆ i, b i • span R {y i} ∧ c ≠ 0 ∧ y 0 = c • x := by
  set W : Submodule F V := span F (L : Set V) with hW
  let v : W := ⟨x, hxL⟩
  have hv0 : v ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (F ∙ v)
  let cb := Module.finBasis F C
  have hli : ∀ (c : F), ∀ z ∈ C, c • v + z = 0 → c = 0 := by
    intro c z hz h
    have h1 : c • v ∈ F ∙ v := smul_mem _ _ (mem_span_singleton_self v)
    have h2 : c • v ∈ C := by
      have : c • v = -z := eq_neg_of_add_eq_zero_left h
      rw [this]; exact neg_mem hz
    have := Submodule.disjoint_def.1 hC.disjoint _ h1 h2
    exact (smul_eq_zero.1 this).resolve_right hv0
  have hsp : ∀ z : W, ∃ c : F, z + c • v ∈ C := by
    intro z
    have : z ∈ (F ∙ v) ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨u, hu, k, hk, rfl⟩ := mem_sup.1 this
    obtain ⟨t, rfl⟩ := mem_span_singleton.1 hu
    exact ⟨-t, by simpa using hk⟩
  let bW := Basis.mkFinCons v cb hli hsp
  have hbW : (bW : Fin (finrank F C + 1) → W) = Fin.cons v ((↑) ∘ cb) := Basis.coe_mkFinCons v cb hli hsp
  let x' : Fin (finrank F C + 1) → V := fun i => (bW i : V)
  have hx'0 : x' 0 = x := by
    show ((bW 0 : W) : V) = x
    rw [show (bW 0 : W) = v from by rw [show (bW 0 : W) = (bW : Fin _ → W) 0 from rfl, hbW]; rfl]
  have hx'i : LinearIndependent F x' := bW.linearIndependent.map' W.subtype (ker_subtype W)
  have hx's : span F (Set.range x') = W := by
    have h1 : Submodule.map W.subtype (span F (Set.range bW)) = span F (W.subtype '' Set.range bW) :=
      Submodule.map_span _ _
    rw [bW.span_eq, Submodule.map_top, Submodule.range_subtype] at h1
    refine Eq.trans ?_ h1.symm
    congr 1
    rw [← Set.range_comp]; rfl
  obtain ⟨y, hy, hyf, b, hb, hLeq⟩ := exists_adapted_flag hL x' hx'i hx's
  have h0 : y 0 ∈ span F {x} := by
    refine span_mono ?_ (hyf 0)
    rintro _ ⟨i, hi, rfl⟩
    have : i = 0 := le_antisymm hi (Fin.zero_le _)
    subst this
    exact Set.mem_singleton_iff.2 hx'0
  obtain ⟨c, hc⟩ := mem_span_singleton.1 h0
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hy.ne_zero 0 (by rw [← hc, zero_smul])
  exact ⟨_, y, b, c, hy, hb, hLeq, hc0, hc.symm⟩

/-- **Proposition 82:16** (O'Meara 1963, p. 233). Let $L$ be an $\mathfrak a$-modular lattice and $x$ an isotropic
vector in $L$. Then there is a binary lattice $J$ (of rank $2$) which splits $L$ and contains $x$; it is
$\mathfrak a$-modular. -/
@[kb "omeara1963" "§82G, 82:16, p. 233"]
theorem exists_binary_split_of_isModular [FiniteDimensional F V] {a : Submodule R F} {L : Submodule R V}
    (hL : IsModular Q a L) (hLfg : L.FG) {x : V} (hxL : x ∈ L) (hx0 : x ≠ 0) (hQx : Q x = 0) :
    ∃ J : Submodule R V, J ≤ L ∧ x ∈ J ∧ finrank R J = 2 ∧ IsModular Q a J ∧ ∃ K, IsOrthSum Q L J K := by
  have hL0 : L ≠ ⊥ := fun h => hx0 (by rw [h] at hxL; exact (mem_bot R).1 hxL)
  have hreg := isRegular_of_isModular Q hL hLfg
  have ha0 := hL.1
  have haf : a.FG := hL.2.1 ▸ scale_fg Q hLfg
  obtain ⟨n, y, b, c, hy, hb, hLeq, hc0, hy0⟩ := exists_adapted_first (F := F) hLfg (subset_span hxL) hx0
  have hdet := (isRegular_adapted_iff Q y hy b fun i => (hb i).2).1 (hLeq ▸ hreg)
  obtain ⟨z, hz, hyz⟩ := exists_biorth Q y hdet
  have hdual : dual Q L = ⨆ i, (1 / b i) • span R {z i} := by
    rw [hLeq]; exact dual_eq_of_adapted Q y hy b hb z hz hyz
  have hmod : a • dual Q L = L := (isModular_iff_smul_dual Q hLfg hL0 hreg haf ha0).1 hL
  obtain ⟨hb0f, hb0n⟩ := hb 0
  obtain ⟨hif, hin⟩ := one_div_fg hb0f hb0n
  have hb0inv : b 0 * (1 / b 0) = 1 := mul_one_div_cancel_of_fg hb0f hb0n
  have hAfg : ∀ i, (![b 0, a * (1 / b 0)] i).FG ∧ ![b 0, a * (1 / b 0)] i ≠ ⊥ :=
    Fin.forall_fin_two.2 ⟨hb 0, haf.mul hif, mul_ne_bot' ha0 hin⟩
  have hyy : bil Q (y 0) (y 0) = 0 := by rw [bil_self, hy0, Q_smul, hQx, mul_zero]
  have hyz0 : bil Q (y 0) (z 0) = 1 := by rw [hyz 0 0]; simp
  have hwi : LinearIndependent F ![y 0, z 0] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (bil Q (y 0)) hst
    simp [bil_add_right, hyy, hyz0] at h1
    subst h1
    simp only [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right (hy.ne_zero 0), rfl⟩
  have hgram : (gram Q ![y 0, z 0]).det = -1 := by
    rw [Matrix.det_fin_two]
    simp [gram, hyy, hyz0, bil_comm Q (z 0) (y 0)]
  set J : Submodule R V := ⨆ i, (![b 0, a * (1 / b 0)] i) • span R {(![y 0, z 0] : Fin 2 → V) i} with hJ
  have hm1 : span R {(-1 : F)} = 1 := by
    rw [Submodule.one_eq_span]
    apply le_antisymm
    · rw [span_le, Set.singleton_subset_iff]
      exact neg_mem (mem_span_singleton_self 1)
    · rw [span_le, Set.singleton_subset_iff]
      have := neg_mem (mem_span_singleton_self (-1 : F) (R := R))
      rwa [neg_neg] at this
  have hvolJ : volume Q J = a ^ 2 := by
    rw [hJ, volume_eq_of_adapted Q _ hwi _ hAfg, Fin.prod_univ_two, hgram, hm1, mul_one]
    show (b 0 * (a * (1 / b 0))) ^ 2 = a ^ 2
    rw [show b 0 * (a * (1 / b 0)) = a * (b 0 * (1 / b 0)) by ring, hb0inv, mul_one]
  have hrkJ : finrank R J = 2 := by
    rw [hJ, finrank_adapted _ (fun i => (hAfg i).2) _ hwi]; simp
  have hb0le : b 0 • span R {y 0} ≤ L := by
    rw [hLeq]; exact le_iSup (fun i => b i • span R {y i}) 0
  have hb1le : (a * (1 / b 0)) • span R {z 0} ≤ L := by
    calc (a * (1 / b 0)) • span R {z 0} = a • ((1 / b 0) • span R {z 0}) := mul_smul_submodule _ _ _
      _ ≤ a • dual Q L := Submodule.smul_mono le_rfl (by
          rw [hdual]; exact le_iSup (fun i => (1 / b i) • span R {z i}) 0)
      _ = L := hmod
  have hJle : J ≤ L := iSup_le (Fin.forall_fin_two.2 ⟨hb0le, hb1le⟩)
  have hxJ : x ∈ J := by
    have hcinv : c⁻¹ ∈ b 0 := by
      have hxe : x = ∑ i, (Pi.single 0 c⁻¹ : Fin (n + 1) → F) i • y i := by
        simp [Pi.single_apply, hy0, smul_smul, hc0]
      have hmem : ∑ i, (Pi.single 0 c⁻¹ : Fin (n + 1) → F) i • y i ∈
          (⨆ i, b i • span R {y i} : Submodule R V) := by
        rw [← hxe, ← hLeq]; exact hxL
      have := coord_mem_of_mem b y hy _ hmem 0
      simpa using this
    refine mem_iSup_of_mem (0 : Fin 2) ((mem_smul_span_singleton_iff' _ _ _).2 ⟨c⁻¹, hcinv, ?_⟩)
    show x = c⁻¹ • y 0
    rw [hy0, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hJfg : J.FG := fg_adapted _ (fun i => (hAfg i).1) _
  have hscale : scale Q J = a := by
    have hle : scale Q J ≤ a := (scale_mono Q hJle).trans hL.2.1.le
    have hv2 := volume_le_scale_pow Q J
    rw [hvolJ, hrkJ] at hv2
    exact eq_of_le_of_pow_eq haf ha0 (by norm_num : 1 ≤ 2) hle
      (le_antisymm (pow_le_pow_left' hle 2) hv2)
  have hJmod : IsModular Q a J := ⟨ha0, hscale, by rw [hvolJ, hrkJ]⟩
  exact ⟨J, hJle, hxJ, hrkJ, hJmod, Dedekind.splits_of_isModular_of_scale_eq Q hJle hJmod hJfg hL.2.1⟩

/-- Over a principal ideal domain every finitely generated submodule of $F$ is principal. -/
theorem exists_eq_span_of_fg [IsPrincipalIdealRing R] (a : Submodule R F) (ha : a.FG) :
    ∃ α : F, a = span R {α} := by
  let I : FractionalIdeal (nonZeroDivisors R) F := ⟨a, FractionalIdeal.isFractional_of_fg ha⟩
  obtain ⟨α, hα⟩ := (FractionalIdeal.isPrincipal I).principal
  exact ⟨α, hα⟩

/-- If every maximal vector $x$ of $L$ has $B(x, L) = \mathfrak a$ and $z \in FL$ has $B(z, L) \subseteq \mathfrak a$,
then $z \in L$ (the key step of 82:17). -/
theorem mem_of_bil_mem_of_forall_isMaxVec [IsPrincipalIdealRing R] [FiniteDimensional F V] {L : Submodule R V}
    (hL : L.FG) {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥)
    (hmax : ∀ x, x ≠ 0 → IsMaxVec F L x → span R (bil Q x '' (L : Set V)) = a)
    {z : V} (hz : z ∈ span F (L : Set V)) (hB : ∀ l ∈ L, bil Q z l ∈ a) : z ∈ L := by
  by_cases hz0 : z = 0
  · rw [hz0]; exact zero_mem _
  obtain ⟨c, hc0, hcm⟩ := exists_isMaxVec_of_principal (fun a ha => exists_eq_span_of_fg a ha) hL hz hz0
  have h1 := hmax _ (smul_ne_zero hc0 hz0) hcm
  have hle : a ≤ span R {c} * a := by
    have : span R (bil Q (c • z) '' (L : Set V)) ≤ span R {c} * a := by
      rw [span_le]
      rintro _ ⟨l, hl, rfl⟩
      show bil Q (c • z) l ∈ _
      rw [bil_smul_left]
      exact mul_mem_mul (mem_span_singleton_self c) (hB l hl)
    calc a = _ := h1.symm
      _ ≤ _ := this
  have h2 := mul_one_div_cancel_of_fg ha ha0
  have h3 : (1 : Submodule R F) ≤ span R {c} :=
    calc (1 : Submodule R F) = a * (1 / a) := h2.symm
      _ ≤ (span R {c} * a) * (1 / a) := mul_le_mul' hle le_rfl
      _ = span R {c} * (a * (1 / a)) := mul_assoc _ _ _
      _ = span R {c} := by rw [h2, mul_one]
  obtain ⟨r, hr⟩ := mem_span_singleton.1 (h3 (Submodule.mem_one.mpr ⟨1, map_one _⟩))
  have : z = r • (c • z) := by
    rw [← algebraMap_smul F r, smul_smul, ← Algebra.smul_def, hr, one_smul]
  rw [this]
  exact L.smul_mem r hcm.1

/-- **Proposition 82:17** (O'Meara 1963, p. 233). Suppose $\mathfrak o$ is a principal ideal domain. A non-zero lattice
$L$ is $\mathfrak a$-modular ($\mathfrak a$ a fractional ideal) if and only if $B(x, L) = \mathfrak a$ for every
maximal vector $x$ of $L$. (Maximal vectors are non-zero, as O'Meara's coefficients are defined for non-zero
vectors; `IsMaxVec` alone would admit $x = 0$ when $\mathfrak o$ is a field.) -/
@[kb "omeara1963" "§82G, 82:17, p. 233"]
theorem isModular_iff_forall_isMaxVec [IsPrincipalIdealRing R] [FiniteDimensional F V] {L : Submodule R V}
    (hL : L.FG) (hL0 : L ≠ ⊥) {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) :
    IsModular Q a L ↔ ∀ x, x ≠ 0 → IsMaxVec F L x → span R (bil Q x '' (L : Set V)) = a := by
  have h2 : a * (1 / a) = 1 := mul_one_div_cancel_of_fg ha ha0
  constructor
  · intro h x hx0 hxm
    have hreg := isRegular_of_isModular Q h hL
    have hmod : a • dual Q L = L := (isModular_iff_smul_dual Q hL hL0 hreg ha ha0).1 h
    apply le_antisymm
    · rw [span_le]
      rintro _ ⟨l, hl, rfl⟩
      show bil Q x l ∈ a
      rw [← h.2.1]; exact bil_mem_scale Q hxm.1 hl
    · obtain ⟨n, y, b, c, hy, hb, hLeq, hc0, hy0⟩ :=
        exists_adapted_first (F := F) hL (subset_span hxm.1) hx0
      have hdet := (isRegular_adapted_iff Q y hy b fun i => (hb i).2).1 (hLeq ▸ hreg)
      obtain ⟨z, hz, hyz⟩ := exists_biorth Q y hdet
      have hdual : dual Q L = ⨆ i, (1 / b i) • span R {z i} := by
        rw [hLeq]; exact dual_eq_of_adapted Q y hy b hb z hz hyz
      have hcb : c ∈ 1 / b 0 := by
        rw [Submodule.mem_div_iff_forall_mul_mem]
        intro β hβ
        have hm : β • y 0 ∈ L := by
          rw [hLeq]; exact mem_iSup_of_mem 0 (smul_mem_smul hβ (mem_span_singleton_self _))
        rw [hy0, smul_smul] at hm
        obtain ⟨r, hr⟩ := hxm.2 (β * c) hm
        exact Submodule.mem_one.mpr ⟨r, by rw [hr]; ring⟩
      have hczmem : c • z 0 ∈ dual Q L := by
        rw [hdual]
        exact mem_iSup_of_mem 0 (smul_mem_smul hcb (mem_span_singleton_self _))
      intro α hα
      have hm : α • (c • z 0) ∈ L := by rw [← hmod]; exact smul_mem_smul hα hczmem
      refine subset_span ⟨_, hm, ?_⟩
      have hxe : x = c⁻¹ • y 0 := by rw [hy0, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      show bil Q x (α • c • z 0) = α
      rw [hxe, bil_smul_left, bil_smul_right, bil_smul_right, hyz 0 0]
      simp only [↓reduceIte]
      field_simp
  · intro hmax
    have hP : ∀ a : Submodule R F, a.FG → ∃ α : F, a = span R {α} := fun a ha => exists_eq_span_of_fg a ha
    have hexist : ∀ y ∈ L, y ≠ 0 → ∃ c : F, c ≠ 0 ∧ IsMaxVec F L (c • y) ∧
        ∃ r : R, algebraMap R F r = c⁻¹ := by
      intro y hy hy0
      obtain ⟨c, hc0, hcm⟩ := exists_isMaxVec_of_principal hP hL (subset_span hy) hy0
      refine ⟨c, hc0, hcm, hcm.2 c⁻¹ ?_⟩
      rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]; exact hy
    have hbil : ∀ y ∈ L, ∀ l ∈ L, bil Q y l ∈ a := by
      intro y hy l hl
      by_cases hy0 : y = 0
      · rw [hy0]; simp [bil]
      obtain ⟨c, hc0, hcm, r, hr⟩ := hexist y hy hy0
      have h1 : bil Q (c • y) l ∈ a :=
        hmax _ (smul_ne_zero hc0 hy0) hcm ▸ subset_span ⟨l, hl, rfl⟩
      have h3 : bil Q y l = algebraMap R F r * bil Q (c • y) l := by
        rw [hr, bil_smul_left, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
      rw [h3, ← Algebra.smul_def]; exact a.smul_mem r h1
    have hreg : IsRegular Q L := by
      intro y hy hB
      by_contra hy0
      obtain ⟨c, hc0, hcm, -⟩ := hexist y hy hy0
      have := hmax _ (smul_ne_zero hc0 hy0) hcm
      apply ha0
      rw [← this, Submodule.span_eq_bot]
      rintro _ ⟨l, hl, rfl⟩
      show bil Q (c • y) l = 0
      rw [bil_smul_left, hB l hl, mul_zero]
    have hscale : scale Q L = a := by
      apply le_antisymm
      · rw [scale, span_le]
        rintro _ ⟨l, hl, l', hl', rfl⟩
        exact hbil l hl l' hl'
      · obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL0
        obtain ⟨c, hc0, hcm, -⟩ := hexist y hy hy0
        have := hmax _ (smul_ne_zero hc0 hy0) hcm
        rw [← this, span_le]
        rintro _ ⟨l, hl, rfl⟩
        exact subset_span ⟨c • y, hcm.1, l, hl, rfl⟩
    refine (isModular_iff_smul_dual Q hL hL0 hreg ha ha0).2 (le_antisymm ?_ ?_)
    · rw [Submodule.smul_le]
      intro α hα z hz
      refine mem_of_bil_mem_of_forall_isMaxVec Q hL ha ha0 hmax (smul_mem _ _ hz.1) fun l hl => ?_
      rw [bil_smul_left]
      have := mul_mem_mul hα (hz.2 l hl)
      rwa [mul_one] at this
    · have hKle : (1 / a) • L ≤ dual Q L := by
        rw [Submodule.smul_le]
        intro β hβ l hl
        refine ⟨smul_mem _ _ (subset_span hl), fun l' hl' => ?_⟩
        rw [bil_smul_left]
        have := mul_mem_mul hβ (show bil Q l l' ∈ a by rw [← hscale]; exact bil_mem_scale Q hl hl')
        rwa [mul_comm, h2] at this
      calc L = (a * (1 / a)) • L := by rw [h2, Submodule.one_smul]
        _ = a • ((1 / a) • L) := mul_smul_submodule _ _ _
        _ ≤ a • dual Q L := Submodule.smul_mono le_rfl hKle

end Dedekind

end QuadFormsKB.OMeara
