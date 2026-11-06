/-
# Cassels, Chapter 7: supplementary items (units, scaled lattices, sublattices, coprimality, the example as printed)

**Setting.** Cassels, *Rational Quadratic Forms*, Chapter 7 (p. 102): $k$ is a field, $I \subseteq k$ a subring
containing $1$, and $U$ its group of units. Indices are 0-based (`Fin n`).

**Proves**
* `isUnit_iff_inv_mem` (p. 102): $U = \{u \in I : u^{-1} \in I\}$;
* `unit_smul_lattice` (p. 104): $l\Lambda$ depends only on the class of $l$ in $k^\times/U$;
* `IsSublattice` (footnote, p. 104) with `IsSublattice.refl`, `IsSublattice.trans`, `isSublattice_smul`;
* `coprime_iff_exists_sum`, `coprime_iff_common_divisor` (Note to (i), p. 107): coprime elements generate the unit
  ideal, equivalently (in a principal ideal domain) have only unit common divisors;
* `sqrtNegFivePrinted`, `not_equiv_one_var_printed` (p. 109): the example over $\mathbb Z[\sqrt{-5}]$ with the
  formula as printed, $\{(1 + 2\sqrt{-5})x_0 + 3x_1\}^{2}$ (Cassels: $x_1, x_2$). The earlier
  `not_equiv_one_var_zsqrtd` (`Singular.lean`) treats a second example, reconstructed before the page image was read.

**Comparisons.** `isPrimitiveVec_iff_coprime` (`Thm31.lean`) already uses "coprime" in the form
`Ideal.span (Set.range f) = ⊤`, the left side of `coprime_iff_exists_sum`; no separate comparison is needed.
`QuadFormsKB.Binary.Rel.smulLat` is the scaled lattice for the ring of integers of a number field inside a field
extension; `unit_smul_lattice` is the same statement at the generality of Cassels' setting (it is not restated for
`smulLat`, which is cited for $l\Lambda$ only in that special case).
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.Cassels

open Matrix

/-! ### The example over $\mathbb Z[\sqrt{-5}]$, as printed -/

/-- The symmetric matrix of Cassels' example as printed, $f(x_0, x_1) = \{(1 + 2\sqrt{-5})x_0 + 3x_1\}^{2}$ over
$\mathbb Z[\sqrt{-5}]$ (`ℤ√-5`): $F = vv^{t}$ with $v = (1 + 2\sqrt{-5}, 3)$. -/
def sqrtNegFivePrinted : Matrix (Fin 2) (Fin 2) (ℤ√(-5)) :=
  Matrix.vecMulVec ![⟨1, 2⟩, 3] ![⟨1, 2⟩, 3]

/-- **Cassels, Ch. 7, §4, p. 109 (7.r4, formula as printed)**: *the conclusion of Lemma 4.1 does not necessarily hold
if $I$ is not a principal ideal domain, e.g. $I = \mathbb Z[\sqrt{-5}]$: the form
$\{(1 + 2\sqrt{-5})x_1 + 3x_2\}^{2}$ is not $\mathbb Z[\sqrt{-5}]$-equivalent to a form in 1 variable.* The form
`sqrtNegFivePrinted` is singular (`det = 0`), and there are no $T \in \mathrm{GL}_2(\mathbb Z[\sqrt{-5}])$ and
$a \in \mathbb Z[\sqrt{-5}]$ with $T^{t}FT = \begin{pmatrix} a & 0 \\ 0 & 0\end{pmatrix}$. The reason: the values
$(1 + 2\sqrt{-5})x_0 + 3x_1$ fill the non-principal ideal $(3, 1 + 2\sqrt{-5})$, every element $z = r + s\sqrt{-5}$
of which has $r + s \equiv 0 \pmod 3$, hence norm divisible by $3$; a generator $w$ would divide $3$ (norm $9$) and
$1 + 2\sqrt{-5}$ (norm $21$), so $N(w) = 3$, but $r^{2} + 5s^{2} = 3$ has no solution. Indices 0-based. -/
@[kb "cassels1978" "Ch. 7, §4, p. 109 (example over ℤ[√−5], as printed)"]
theorem not_equiv_one_var_printed :
    sqrtNegFivePrinted.det = 0 ∧
      ¬ ∃ (T : GL (Fin 2) (ℤ√(-5))) (a : ℤ√(-5)),
          T.valᵀ * sqrtNegFivePrinted * T.val = !![a, 0; 0, 0] := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_fin_two]
    simp [sqrtNegFivePrinted, vecMulVec_apply]
    ring
  · rintro ⟨T, a, h⟩
    have h11 := congrFun (congrFun h 1) 1
    have hTU : T.val * (T⁻¹).val = 1 := by simp
    have e00 := congrFun (congrFun hTU 0) 0
    have e10 := congrFun (congrFun hTU 1) 0
    have e01 := congrFun (congrFun hTU 0) 1
    have e11 := congrFun (congrFun hTU 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne,
      ne_eq, one_ne_zero, not_false_eq_true, zero_ne_one, Fin.isValue] at e00 e10 e01 e11
    simp [Matrix.mul_apply, Fin.sum_univ_two, sqrtNegFivePrinted] at h11
    set t00 := T.val 0 0
    set t01 := T.val 0 1
    set t10 := T.val 1 0
    set t11 := T.val 1 1
    set U00 := (T⁻¹).val 0 0
    set U01 := (T⁻¹).val 0 1
    set U10 := (T⁻¹).val 1 0
    set U11 := (T⁻¹).val 1 1
    set w0 : ℤ√(-5) := t00 * ⟨1, 2⟩ + t10 * 3 with hw0
    set w1 : ℤ√(-5) := t01 * ⟨1, 2⟩ + t11 * 3 with hw1
    have hw1z : w1 * w1 = 0 := by rw [hw1]; linear_combination h11
    have hw1' : w1 = 0 := by
      have r := congrArg Zsqrtd.re hw1z
      have i := congrArg Zsqrtd.im hw1z
      simp at r i
      have hxy : w1.re * w1.im = 0 := by linarith
      rcases mul_eq_zero.mp hxy with h0 | h1
      · have h1 : w1.im = 0 := by rw [h0] at r; nlinarith [mul_self_nonneg w1.im]
        exact Zsqrtd.ext h0 h1
      · have h0 : w1.re = 0 := by rw [h1] at r; nlinarith [mul_self_nonneg w1.re]
        exact Zsqrtd.ext h0 h1
    have hv0 : (⟨1, 2⟩ : ℤ√(-5)) = U00 * w0 := by
      have : (⟨1, 2⟩ : ℤ√(-5)) = U00 * w0 + U10 * w1 := by
        rw [hw0, hw1]; linear_combination (-(⟨1, 2⟩ : ℤ√(-5))) * e00 - 3 * e10
      rw [this, hw1']; ring
    have hv1 : (3 : ℤ√(-5)) = U01 * w0 := by
      have : (3 : ℤ√(-5)) = U01 * w0 + U11 * w1 := by
        rw [hw0, hw1]; linear_combination (-(⟨1, 2⟩ : ℤ√(-5))) * e01 - 3 * e11
      rw [this, hw1']; ring
    have n1 : w0.norm ∣ 21 := by
      have := congrArg Zsqrtd.norm hv0
      rw [Zsqrtd.norm_mul] at this
      exact ⟨U00.norm, by rw [mul_comm]; simpa [Zsqrtd.norm_def] using this⟩
    have n2 : w0.norm ∣ 9 := by
      have := congrArg Zsqrtd.norm hv1
      rw [Zsqrtd.norm_mul] at this
      exact ⟨U01.norm, by rw [mul_comm]; simpa [Zsqrtd.norm_def] using this⟩
    have n3 : w0.norm ∣ 3 := by
      have := dvd_sub n1 (dvd_mul_of_dvd_right n2 2)
      simpa using this
    have hre : w0.re = t00.re - 10 * t00.im + 3 * t10.re := by
      simp [hw0]; ring
    have him : w0.im = 2 * t00.re + t00.im + 3 * t10.im := by
      simp [hw0]; ring
    have hN : w0.norm = w0.re * w0.re - (-5) * w0.im * w0.im := by
      simp [Zsqrtd.norm_def]
    have hnn : 0 ≤ w0.norm := by
      rw [hN]; nlinarith [mul_self_nonneg w0.re, mul_self_nonneg w0.im]
    have hle := Int.le_of_dvd (by norm_num) n3
    have hev : 3 ∣ w0.norm := by
      obtain ⟨k, hk⟩ : ∃ k, w0.re = -w0.im + 3 * k := ⟨(w0.re + w0.im) / 3, by omega⟩
      exact ⟨3 * k * k - 2 * k * w0.im + 2 * w0.im * w0.im, by rw [hN, hk]; ring⟩
    have h2 : w0.norm = 3 := by
      rcases (show w0.norm = 0 ∨ w0.norm = 1 ∨ w0.norm = 2 ∨ w0.norm = 3 by omega) with h | h | h | h
      · rw [h] at n3; simp at n3
      · rw [h] at hev; omega
      · rw [h] at hev; omega
      · exact h
    rw [hN] at h2
    have hy : w0.im = 0 ∨ w0.im ≠ 0 := em _
    rcases hy with hy | hy
    · rw [hy] at h2
      rcases (show w0.re ≤ -2 ∨ (-1 ≤ w0.re ∧ w0.re ≤ 1) ∨ 2 ≤ w0.re by omega) with h | h | h <;>
        nlinarith
    · nlinarith [mul_self_pos.mpr hy, mul_self_nonneg w0.re]

/-! ### Units of a subring -/

/-- **Cassels, Ch. 7, §1, p. 102**: *$U = \{u \in I : u^{-1} \in I\}$ is the group of units of $I$.* For a field $k$,
a subring `I` of `k` and `u : I`: `u` is a unit of `I` if and only if its image in `k` is non-zero and its inverse
in `k` lies in `I`. -/
@[kb "cassels1978" "Ch. 7, §1, p. 102 (U = {u ∈ I : u⁻¹ ∈ I}, the group of units of I)"]
theorem isUnit_iff_inv_mem {k : Type*} [Field k] (I : Subring k) (u : I) :
    IsUnit u ↔ (u : k) ≠ 0 ∧ (u : k)⁻¹ ∈ I := by
  constructor
  · rintro ⟨v, rfl⟩
    have h : ((v : I) : k) * (((v⁻¹ : Iˣ) : I) : k) = 1 := by
      rw [← Subring.coe_mul]; simp
    have hne : ((v : I) : k) ≠ 0 := left_ne_zero_of_mul_eq_one h
    refine ⟨hne, ?_⟩
    have : ((v : I) : k)⁻¹ = (((v⁻¹ : Iˣ) : I) : k) := by
      rw [inv_eq_of_mul_eq_one_right h]
    rw [this]; exact (((v⁻¹ : Iˣ) : I)).2
  · rintro ⟨h0, hinv⟩
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.ext
    simp [h0]

/-! ### Scaling a lattice -/

/-- **Cassels, Ch. 7, §3, p. 104**: *$l\Lambda$ depends only on the class of $l$ in $k^\times/U$.* Here `I` is a
commutative ring with an algebra structure over the field `k`, `V` a `k`-vector space which is also an `I`-module
(compatibly), `Λ` an `I`-submodule of `V` (a lattice), `l : k` and `u : Iˣ` a unit: the set
$\{x : x = (ul)a,\ a \in \Lambda\}$ equals $\{x : x = la,\ a \in \Lambda\}$, i.e. $(ul)\Lambda = l\Lambda$. -/
@[kb "cassels1978" "Ch. 7, §3, p. 104 (lΛ depends only on the class of l in k^×/U)"]
theorem unit_smul_lattice {I k V : Type*} [CommRing I] [Field k] [Algebra I k] [AddCommGroup V] [Module k V]
    [Module I V] [IsScalarTower I k V] (Λ : Submodule I V) (l : k) (u : Iˣ) :
    {x : V | ∃ a ∈ Λ, x = (algebraMap I k u * l) • a} = {x : V | ∃ a ∈ Λ, x = l • a} := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(u : I) • a, Λ.smul_mem _ ha, ?_⟩
    rw [mul_smul, ← algebraMap_smul k (u : I) a, smul_comm]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨((u⁻¹ : Iˣ) : I) • a, Λ.smul_mem _ ha, ?_⟩
    rw [← algebraMap_smul k ((u⁻¹ : Iˣ) : I) a, smul_smul]
    congr 1
    rw [mul_right_comm, ← map_mul]
    simp

/-! ### Sublattices -/

/-- **Cassels, Ch. 7, §3, p. 104 (footnote)**: *$\Gamma$ is a sublattice of $\Lambda$ if $\Gamma \subseteq \Lambda$ and
both span the same $k$-vector space.* Here `Γ` and `Λ` are $I$-submodules of the $k$-vector space `V` (with `I`
acting compatibly), and `k` is the field of scalars of the spanned vector spaces (given explicitly). -/
@[kb "cassels1978" "Ch. 7, §3, p. 104 (footnote: sublattice)"]
def IsSublattice (k : Type*) {I V : Type*} [CommRing I] [Field k] [Algebra I k] [AddCommGroup V] [Module k V]
    [Module I V] [IsScalarTower I k V] (Γ Λ : Submodule I V) : Prop :=
  Γ ≤ Λ ∧ Submodule.span k (Γ : Set V) = Submodule.span k (Λ : Set V)

section Sublattice

variable {I k V : Type*} [CommRing I] [Field k] [Algebra I k] [AddCommGroup V] [Module k V] [Module I V]
  [IsScalarTower I k V]

/-- Helper: every lattice is a sublattice of itself. -/
theorem IsSublattice.refl (Λ : Submodule I V) : IsSublattice k Λ Λ := ⟨le_rfl, rfl⟩

/-- Helper: a sublattice of a sublattice is a sublattice (arguments: `Γ` sublattice of `Δ`, `Δ` sublattice of `Λ`). -/
theorem IsSublattice.trans {Γ Δ Λ : Submodule I V} (h₁ : IsSublattice k Γ Δ) (h₂ : IsSublattice k Δ Λ) :
    IsSublattice k Γ Λ :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

open Pointwise in
/-- Helper: for $l \in I$ whose image in $k$ is non-zero, $l\Lambda$ is a sublattice of $\Lambda$ (the typical
sublattice; arguments: the lattice `Λ` and the scalar `l : I`). -/
theorem isSublattice_smul (Λ : Submodule I V) (l : I) (hl : algebraMap I k l ≠ 0) :
    IsSublattice k (l • Λ) Λ := by
  have hle : l • Λ ≤ Λ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact Λ.smul_mem _ hy
  refine ⟨hle, le_antisymm (Submodule.span_mono hle) ?_⟩
  refine Submodule.span_le.2 fun x hx => ?_
  have hx' : l • x ∈ l • Λ := Submodule.smul_mem_pointwise_smul _ _ _ hx
  have : x = (algebraMap I k l)⁻¹ • (l • x) := by
    rw [← algebraMap_smul k l x, smul_smul, inv_mul_cancel₀ hl, one_smul]
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hx')

end Sublattice

/-! ### Coprime elements -/

/-- **Cassels, Ch. 7, §3, p. 107 (Note to (i))**: *$f_1, \dots, f_L$ are coprime if they generate the unit ideal*,
i.e. (Bézout form) iff $\sum_l f_lg_l = 1$ for some $g_0, \dots, g_{L-1}$. Here `J` is a commutative ring and
`f : Fin L → J`. -/
@[kb "cassels1978" "Ch. 7, §3, p. 107 (Note to (i): f₁, …, f_L coprime: they generate the unit ideal)"]
theorem coprime_iff_exists_sum {J : Type*} [CommRing J] {L : ℕ} (f : Fin L → J) :
    Ideal.span (Set.range f) = ⊤ ↔ ∃ g : Fin L → J, ∑ l, f l * g l = 1 := by
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, by simpa [mul_comm] using hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, by simpa [mul_comm] using hg⟩

/-- **Cassels, Ch. 7, §3, p. 107 (Note to (i))**, over a principal ideal domain `J`: $f_0, \dots, f_{L-1}$ generate
the unit ideal if and only if every common divisor $d$ of all the $f_l$ is a unit. -/
@[kb "cassels1978" "Ch. 7, §3, p. 107 (Note to (i): coprime iff only unit common divisors, over a PID)"]
theorem coprime_iff_common_divisor {J : Type*} [CommRing J] [IsDomain J] [IsPrincipalIdealRing J] {L : ℕ}
    (f : Fin L → J) :
    Ideal.span (Set.range f) = ⊤ ↔ ∀ d : J, (∀ l, d ∣ f l) → IsUnit d := by
  constructor
  · intro h d hd
    have hle : Ideal.span (Set.range f) ≤ Ideal.span {d} :=
      Ideal.span_le.2 (by rintro _ ⟨l, rfl⟩; exact Ideal.mem_span_singleton.2 (hd l))
    rw [h, top_le_iff, Ideal.span_singleton_eq_top] at hle
    exact hle
  · intro h
    obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (Ideal.span (Set.range f))).principal
    have hgd : ∀ l, g ∣ f l := fun l => by
      have : f l ∈ Ideal.span (Set.range f) := Ideal.subset_span ⟨l, rfl⟩
      rw [hg] at this
      exact Ideal.mem_span_singleton.1 this
    have hu := h g hgd
    rw [hg]
    exact Ideal.span_singleton_eq_top.2 hu

end QuadFormsKB.Cassels
