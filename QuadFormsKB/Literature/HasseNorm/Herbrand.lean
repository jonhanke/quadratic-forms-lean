/-
# Hasse norm theorem, step 1: index algebra for an involution (Herbrand quotient of order 2)

This file is the first module of our own proof of the Hasse norm theorem for quadratic extensions
$L = F(\sqrt a)$ of a number field $F$, which replaces the imported
Yamaguchi-based proof (archived in `archive/yamaguchi/`); the result is
`HasseNorm.hilbert_eq_one_of_everywhere` in `HasseNorm/Main.lean`.

## The route (Chevalley's algebraic proof, specialised to $n = 2$, written with $S$-units)

Let $G = \{1, \sigma\}$ act on an abelian group $M$. For $G$ of order 2 the only "cohomology" needed
is the pair of indices
$$h^0(M) = [M^{\sigma} : (1+\sigma)M], \qquad h^{-1}(M) = [M^{1+\sigma = 0} : (1-\sigma)M].$$
The proof avoids idèles: every idèlic index of Milne, *Class Field Theory*, Ch. VII §§4–6 is
rewritten, using a finite set $S$ of places with trivial $S$-class group, as an index between
groups of $S$-units and finite products of local groups $\prod_{v \in S} F_v^\times/(\cdot)$.

1. **(this file)** For $M$ finitely generated: $h^0(M)\,2^{\operatorname{rk} M^-} = h^{-1}(M)\,2^{\operatorname{rk} M^+}$
   (`herbrand_formula`), where $M^+ = \ker(1-\sigma)$, $M^- = \ker(1+\sigma)$; and
   $\operatorname{rk} M = \operatorname{rk} M^+ + \operatorname{rk} M^-$ (`finrank_fixed_add_anti`). The proof is a
   direct count ($[M^+ : 2M^+] = 2^{\operatorname{rk}}|M^+[2]|$, `index_range_two`, and $M^+[2] = M^-[2]$),
   so no long exact hexagon is needed.
2. $S$-units: $F_S^\times$ is finitely generated of rank $|S| - 1$ with cyclic torsion of even order,
   so $[F_S^\times : F_S^{\times 2}] = 2^{|S|}$ (from Mathlib's unit theorem and class group finiteness).
3. Global count ("first inequality", $S$-unit form, Milne VII §3 + Lemma 4.5): if $\mathrm{Cl}_S(F) = 1$
   and $S$ contains the infinite places and the places ramified in $L$, then Hilbert 90 gives
   $h^{-1}(L_S^\times) = 1$, and step 1 gives $[F_S^\times : N L_S^\times] = 2^{s'-1}$, $s'$ the number of
   places of $S$ with only one place of $L$ above them.
4. Local inputs: $|F_v^\times / F_v^{\times 2}| = 4\,|\mathcal O_v/2\mathcal O_v|$ at finite $v$ (with $2$, $1$ at real,
   complex $v$), hence $\prod_{v \in S} |F_v^\times/F_v^{\times2}| = 4^{|S|}$ (product formula); units are norms
   at unramified non-dyadic places; and $[F_v^\times : N L_w^\times] \ge 2$ when $v$ does not split
   (from the square-class counts of $F_v$ and $L_w$: $N$ factors through $L_w^\times/F_v^\times L_w^{\times 2}$,
   of order $|F_v^\times/F_v^{\times 2}|/2$).
5. Second inequality, Kummer case $n = 2$ (Milne VII Lemmas 6.2–6.9, Prop. 6.10): choose a set $T$ of
   $|S| - 1$ places split in $L$ such that $F_S^\times/\langle a\rangle F_S^{\times2} \to \prod_{t \in T} U_t/U_t^2$ is an
   isomorphism (primes exist by `SqLG.not_almost_all_split` over $L$); then an $(S \cup T)$-unit that is a
   square at every $v \in S$ is a square (by step 3 applied to $F(\sqrt b)$), so the image of
   $F_{S \cup T}^\times$ in $\prod_{v \in S} F_v^\times / N L_w^\times$ has index $\le 2$.
6. Hasse norm: for $b$ a local norm everywhere, with $S$ large and $T$ as in step 5, steps 3–5 give
   $[F_{S\cup T}^\times : N L_{S\cup T}^\times] = 2^{s'-1} \le [F_{S\cup T}^\times : \text{local norms}]$, so local norms
   in $F_{S \cup T}^\times$ are global norms; this is `hilbert_eq_one_of_everywhere`.

Why this route: it needs no idèles, no Artin map and no local class field theory (for $n = 2$,
squares are norms trivially, which replaces Milne's use of local CFT in Lemma 6.4); the only
cohomology is the index identity of step 1.

Locators are from memory and still `[unverified]`.
-/
import Mathlib
import QuadFormsKB.Citation

open Module

namespace QuadFormsKB.HN

variable {A : Type*} [AddCommGroup A]

/-- **Index of $2A$ in a finitely generated abelian group:** $[A : 2A] = 2^{\operatorname{rk} A}\,|A[2]|$, where
$\operatorname{rk} A$ is the $\mathbb{Z}$-rank (`finrank ℤ A`) and $A[2] = \ker(x \mapsto 2x)$.

*Proof.* With $T$ the (finite) torsion subgroup, $[A : 2A] = [A : 2A + T]\,[2A + T : 2A]$. The first
factor is $[A/T : 2(A/T)] = 2^{\operatorname{rk}}$ ($A/T$ is free of the same rank); the second is
$[T : T \cap 2A] = [T : 2T] = |T[2]| = |A[2]|$ (if $2y \in T$ then $y \in T$). -/
@[kb "milne2020cft" "Ch. II §3 (Herbrand quotient) [unverified]"]
theorem index_range_two [Module.Finite ℤ A] :
    (nsmulAddMonoidHom (α := A) 2).range.index =
      2 ^ finrank ℤ A * Nat.card (nsmulAddMonoidHom (α := A) 2).ker := by
  classical
  set f := nsmulAddMonoidHom (α := A) 2 with hf
  set Tm := Submodule.torsion ℤ A with hTm
  set T : AddSubgroup A := Tm.toAddSubgroup with hT
  set R := f.range with hR
  have hTfin : Finite T := by
    have : Module.Finite ℤ Tm := Module.Finite.of_injective Tm.subtype Subtype.val_injective
    exact Module.finite_of_fg_torsion Tm (Submodule.torsion_isTorsion)
  have memT : ∀ y : A, 2 • y ∈ T → y ∈ T := by
    intro y hy
    obtain ⟨⟨n, hn⟩, hn'⟩ := hy
    refine ⟨⟨2 * n, ?_⟩, ?_⟩
    · exact mul_mem (mem_nonZeroDivisors_of_ne_zero (by norm_num)) hn
    · simp only [Submonoid.mk_smul] at hn' ⊢
      rw [mul_smul, two_zsmul, ← two_nsmul, smul_comm]; exact hn'
  let Q := A ⧸ Tm
  let π : A →+ Q := (Tm.mkQ).toAddMonoidHom
  have hπ : Function.Surjective π := Tm.mkQ_surjective
  have hsup : R ⊔ T = (nsmulAddMonoidHom (α := Q) 2).range.comap π := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · rintro _ ⟨y, rfl⟩
        exact ⟨π y, by simp [π, f]⟩
      · intro t ht
        refine ⟨0, ?_⟩
        simp only [nsmulAddMonoidHom_apply, smul_zero]
        exact ((Submodule.Quotient.mk_eq_zero Tm).mpr ht).symm
    · rintro x ⟨q, hq⟩
      obtain ⟨y, rfl⟩ := hπ q
      have : x - 2 • y ∈ T := by
        show x - 2 • y ∈ Tm
        rw [← Submodule.Quotient.mk_eq_zero]
        simp only [π, nsmulAddMonoidHom_apply] at hq
        change 2 • (Submodule.Quotient.mk y : Q) = Submodule.Quotient.mk x at hq
        rw [Submodule.Quotient.mk_sub, ← hq, Submodule.Quotient.mk_smul, sub_self]
      have hx : x = 2 • y + (x - 2 • y) := by abel
      rw [hx]
      exact AddSubgroup.add_mem_sup ⟨y, rfl⟩ this
  have h1 : (R ⊔ T).index = 2 ^ finrank ℤ A := by
    rw [hsup, AddSubgroup.index_comap_of_surjective _ hπ]
    have : Module.Free ℤ Q := Module.free_of_finite_type_torsion_free'
    rw [AddSubgroup.index_range_nsmul, finrank_quotient_eq_of_le_torsion le_rfl]
  have h2 : R.relIndex (R ⊔ T) = Nat.card f.ker := by
    rw [AddSubgroup.relIndex_sup_left]
    let g : T →+ T := nsmulAddMonoidHom 2
    have hker : Nat.card g.ker = Nat.card f.ker := by
      refine Nat.card_congr ⟨fun x => ⟨x.1.1, ?_⟩, fun x => ⟨⟨x.1, ?_⟩, ?_⟩,
        fun x => rfl, fun x => rfl⟩
      · have := x.2
        rw [AddMonoidHom.mem_ker] at this ⊢
        simpa [g, f] using congrArg Subtype.val this
      · have := x.2
        rw [AddMonoidHom.mem_ker] at this
        exact memT _ (by simp only [f, nsmulAddMonoidHom_apply] at this; rw [this]; exact zero_mem _)
      · rw [AddMonoidHom.mem_ker]
        have := x.2
        rw [AddMonoidHom.mem_ker] at this
        ext; simpa [g, f] using this
    have hrange : g.range = R.addSubgroupOf T := by
      ext x
      simp only [AddMonoidHom.mem_range, AddSubgroup.mem_addSubgroupOf, hR, f,
        nsmulAddMonoidHom_apply]
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨y.1, rfl⟩
      · rintro ⟨y, hy⟩
        have hyT : y ∈ T := memT y (by rw [hy]; exact x.2)
        exact ⟨⟨y, hyT⟩, by ext; simpa [g] using hy⟩
    have hcard := AddSubgroup.card_mul_index (R.addSubgroupOf T)
    rw [← hrange] at hcard
    have e := (QuotientAddGroup.quotientKerEquivRange g).toEquiv
    have hq := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker
    rw [Nat.card_congr e] at hq
    rw [AddSubgroup.relIndex, ← hrange, ← hker]
    have hpos : 0 < Nat.card g.range := Nat.card_pos
    have : Nat.card g.range * g.range.index = Nat.card g.range * Nat.card g.ker := by
      rw [hcard, hq]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  rw [← AddSubgroup.relIndex_mul_index (le_sup_left : R ≤ R ⊔ T), h1, h2, mul_comm]

/-- The $2$-torsion of a finitely generated abelian group is finite (nonzero cardinality). -/
theorem card_ker_two_ne_zero [Module.Finite ℤ A] :
    Nat.card (nsmulAddMonoidHom (α := A) 2).ker ≠ 0 := by
  have : Module.Finite ℤ (Submodule.torsion ℤ A) :=
    Module.Finite.of_injective (Submodule.torsion ℤ A).subtype Subtype.val_injective
  have hT : Finite (Submodule.torsion ℤ A) :=
    Module.finite_of_fg_torsion _ (Submodule.torsion_isTorsion)
  have : Finite (nsmulAddMonoidHom (α := A) 2).ker := by
    refine Finite.of_injective (β := Submodule.torsion ℤ A)
      (fun x => ⟨x.1, ⟨⟨2, mem_nonZeroDivisors_of_ne_zero (by norm_num)⟩, ?_⟩⟩) ?_
    · have := x.2
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at this
      simp only [Submonoid.mk_smul, two_zsmul, ← two_nsmul]; exact this
    · intro x y h; ext; simpa using congrArg Subtype.val h
  exact Nat.card_pos.ne'

/-- A finite-index subgroup of a f.g. abelian group has the same rank. -/
theorem finrank_eq_of_relIndex_ne_zero {M : Type*} [AddCommGroup M] [Module.Finite ℤ M]
    {H K : AddSubgroup M} (hHK : H ≤ K) (h : H.relIndex K ≠ 0) :
    finrank ℤ H = finrank ℤ K := by
  have : Module.Finite ℤ K :=
    Module.Finite.of_injective K.subtype.toIntLinearMap Subtype.val_injective
  let H' : Submodule ℤ K := (H.addSubgroupOf K).toIntSubmodule
  have hfin : (H.addSubgroupOf K).FiniteIndex := ⟨h⟩
  have htors : Module.IsTorsion ℤ (K ⧸ H') := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective H' x
    refine ⟨⟨((H.addSubgroupOf K).index : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast h)⟩, ?_⟩
    simp only [Submonoid.mk_smul]
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have := (H.addSubgroupOf K).nsmul_index_mem y
    rw [natCast_zsmul]; exact this
  have h0 : finrank ℤ (K ⧸ H') = 0 := (Module.finrank_eq_zero_iff_isTorsion).mpr htors
  have := H'.finrank_quotient_add_finrank
  rw [h0, zero_add] at this
  rw [← this]
  exact ((AddSubgroup.addSubgroupOfEquivOfLe hHK).toIntLinearEquiv.finrank_eq).symm



variable {M : Type*} [AddCommGroup M] (σ : M →+ M)

/-- The **norm map** $N = 1 + \sigma$ of the involution $\sigma$ (additive notation). -/
def normHom : M →+ M := AddMonoidHom.id M + σ
/-- The map $1 - \sigma$. -/
def diffHom : M →+ M := AddMonoidHom.id M - σ

@[simp] lemma normHom_apply (x : M) : normHom σ x = x + σ x := rfl
@[simp] lemma diffHom_apply (x : M) : diffHom σ x = x - σ x := rfl

/-- **$|\hat H^0|$ for $G = \{1, \sigma\}$:** the index $[M^{+} : (1 + \sigma) M]$ of the norms in the fixed
points $M^+ = \ker(1 - \sigma)$ (`0` if infinite). -/
noncomputable def herbrand0 : ℕ := (normHom σ).range.relIndex (diffHom σ).ker
/-- **$|\hat H^{-1}|$ for $G = \{1, \sigma\}$:** the index $[M^{-} : (1 - \sigma) M]$ in $M^- = \ker(1 + \sigma)$
(`0` if infinite). -/
noncomputable def herbrandM1 : ℕ := (diffHom σ).range.relIndex (normHom σ).ker

variable {σ}

lemma mem_fixed {x : M} : x ∈ (diffHom σ).ker ↔ σ x = x := by
  rw [AddMonoidHom.mem_ker, diffHom_apply, sub_eq_zero, eq_comm]
lemma mem_anti {x : M} : x ∈ (normHom σ).ker ↔ σ x = -x := by
  rw [AddMonoidHom.mem_ker, normHom_apply, add_eq_zero_iff_eq_neg', eq_comm]

variable (hσ : ∀ x, σ (σ x) = x)
include hσ

lemma range_norm_le : (normHom σ).range ≤ (diffHom σ).ker := by
  rintro _ ⟨x, rfl⟩; rw [mem_fixed]; simp [hσ, add_comm]
lemma range_diff_le : (diffHom σ).range ≤ (normHom σ).ker := by
  rintro _ ⟨x, rfl⟩; rw [mem_anti]; simp [hσ]

omit hσ in
/-- `{x | N x ∈ 2P} = P ⊔ Q` -/
lemma comap_norm (P Q : AddSubgroup M) (hP : P = (diffHom σ).ker) (hQ : Q = (normHom σ).ker) :
    (P.map (nsmulAddMonoidHom 2)).comap (normHom σ) = P ⊔ Q := by
  subst hP hQ
  apply le_antisymm
  · rintro x ⟨p, hp, hpx⟩
    have hp' : σ p = p := mem_fixed.mp hp
    have hq : x - p ∈ (normHom σ).ker := by
      rw [mem_anti, map_sub, hp']
      simp only [nsmulAddMonoidHom_apply, normHom_apply, two_nsmul] at hpx
      rw [neg_sub, ← sub_eq_zero]
      have e : σ x - p - (p - x) = (x + σ x) - (p + p) := by abel
      rw [e, hpx, sub_self]
    have : x = p + (x - p) := by abel
    rw [this]; exact AddSubgroup.add_mem_sup hp hq
  · rw [sup_le_iff]; constructor
    · intro p hp
      exact ⟨p, hp, by simp [mem_fixed.mp hp, two_nsmul]⟩
    · intro q hq
      exact ⟨0, zero_mem _, by simp [(AddMonoidHom.mem_ker).mp hq]⟩


omit hσ in
lemma comap_diff (P Q : AddSubgroup M) (hP : P = (diffHom σ).ker) (hQ : Q = (normHom σ).ker) :
    (Q.map (nsmulAddMonoidHom 2)).comap (diffHom σ) = P ⊔ Q := by
  subst hP hQ
  apply le_antisymm
  · rintro x ⟨q, hq, hqx⟩
    have hq' : σ q = -q := mem_anti.mp hq
    have hp : x - q ∈ (diffHom σ).ker := by
      rw [mem_fixed, map_sub, hq']
      simp only [nsmulAddMonoidHom_apply, diffHom_apply, two_nsmul] at hqx
      rw [← sub_eq_zero]
      have e : σ x - -q - (x - q) = -((x - σ x) - (q + q)) := by abel
      rw [e, hqx, sub_self, neg_zero]
    have : x = (x - q) + q := by abel
    rw [this]; exact AddSubgroup.add_mem_sup hp hq
  · rw [sup_le_iff]; constructor
    · intro p hp
      exact ⟨0, zero_mem _, by simp [(AddMonoidHom.mem_ker).mp hp]⟩
    · intro q hq
      exact ⟨q, hq, by simp [mem_anti.mp hq, two_nsmul]⟩

omit hσ in
/-- relative index of `H` in the range of `f` as the index of its preimage -/
lemma relIndex_range_eq_index_comap (f : M →+ M) (H : AddSubgroup M) :
    H.relIndex f.range = (H.comap f).index := by
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ f.rangeRestrict_surjective]
  congr 1

omit hσ in
lemma map_two_addSubgroupOf (P : AddSubgroup M) :
    (P.map (nsmulAddMonoidHom 2)).addSubgroupOf P = (nsmulAddMonoidHom (α := P) 2).range := by
  ext x
  simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, AddMonoidHom.mem_range,
    nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩; exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hyx)⟩
  · rintro ⟨y, rfl⟩; exact ⟨y.1, y.2, by simp⟩

omit hσ in
lemma finite_of_addSubgroup [Module.Finite ℤ M] (P : AddSubgroup M) : Module.Finite ℤ P :=
  Module.Finite.of_injective P.subtype.toIntLinearMap Subtype.val_injective

/-- **Herbrand quotient of an involution (order-2 index identity).** Let $M$ be a finitely generated
abelian group with an involution $\sigma$ ($\sigma^2 = 1$), $M^+ = \ker(1 - \sigma)$, $M^- = \ker(1 + \sigma)$. Then
both indices $h^0 = [M^+ : (1+\sigma)M]$ (`herbrand0`) and $h^{-1} = [M^- : (1-\sigma)M]$ (`herbrandM1`) are finite
(nonzero) and
$$h^0 \cdot 2^{\operatorname{rk} M^-} = h^{-1} \cdot 2^{\operatorname{rk} M^+},$$
i.e. the Herbrand quotient is $h^0/h^{-1} = 2^{\operatorname{rk} M^+ - \operatorname{rk} M^-}$.

*Proof.* For $p \in M^+$, $(1+\sigma)p = 2p$; and $(1+\sigma)x \in 2M^+$ iff $x \in M^+ + M^-$. So
$[M^+ : 2M^+] = h^0 \cdot [M : M^+ + M^-]$; likewise $[M^- : 2M^-] = h^{-1} \cdot [M : M^+ + M^-]$, and the
index $[M : M^+ + M^-]$ is finite since $2M \subseteq M^+ + M^-$. By `index_range_two`,
$[M^\pm : 2M^\pm] = 2^{\operatorname{rk} M^\pm} |M^\pm[2]|$, and $M^+[2] = M^-[2]$ ($-x = x$ when $2x = 0$). -/
@[kb "milne2020cft" "Ch. II §3 (Herbrand quotient), Ch. VII §3 [unverified]"]
theorem herbrand_formula [Module.Finite ℤ M] :
    herbrand0 σ * 2 ^ finrank ℤ (normHom σ).ker = herbrandM1 σ * 2 ^ finrank ℤ (diffHom σ).ker ∧
      herbrand0 σ ≠ 0 ∧ herbrandM1 σ ≠ 0 := by
  classical
  set P := (diffHom σ).ker with hP
  set Q := (normHom σ).ker with hQ
  have : Module.Finite ℤ P := finite_of_addSubgroup P
  have : Module.Finite ℤ Q := finite_of_addSubgroup Q
  -- index of P ⊔ Q
  set I := (P ⊔ Q).index with hI
  have hI0 : I ≠ 0 := by
    have h2M : (nsmulAddMonoidHom (α := M) 2).range ≤ P ⊔ Q := by
      rintro _ ⟨x, rfl⟩
      have e : nsmulAddMonoidHom 2 x = (x + σ x) + (x - σ x) := by
        simp only [nsmulAddMonoidHom_apply, two_nsmul]; abel
      rw [e]
      refine AddSubgroup.add_mem_sup ?_ ?_
      · rw [hP, mem_fixed]; simp [hσ, add_comm]
      · rw [hQ, mem_anti]; simp [hσ]
    have := AddSubgroup.index_dvd_of_le h2M
    rw [index_range_two] at this
    intro h0; rw [show (P ⊔ Q).index = 0 from h0, zero_dvd_iff] at this
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) card_ker_two_ne_zero this
  -- 2P ≤ N(M) ≤ P
  have h2P : P.map (nsmulAddMonoidHom 2) ≤ (normHom σ).range := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, by simp [(mem_fixed).mp hp, two_nsmul]⟩
  have h2Q : Q.map (nsmulAddMonoidHom 2) ≤ (diffHom σ).range := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨q, by simp [(mem_anti).mp hq, two_nsmul]⟩
  have hNP := range_norm_le hσ
  have hDQ := range_diff_le hσ
  have eP : (P.map (nsmulAddMonoidHom 2)).relIndex P =
      2 ^ finrank ℤ P * Nat.card (nsmulAddMonoidHom (α := P) 2).ker := by
    rw [AddSubgroup.relIndex, map_two_addSubgroupOf, index_range_two]
  have eQ : (Q.map (nsmulAddMonoidHom 2)).relIndex Q =
      2 ^ finrank ℤ Q * Nat.card (nsmulAddMonoidHom (α := Q) 2).ker := by
    rw [AddSubgroup.relIndex, map_two_addSubgroupOf, index_range_two]
  have tP := AddSubgroup.relIndex_mul_relIndex _ _ _ h2P hNP
  have tQ := AddSubgroup.relIndex_mul_relIndex _ _ _ h2Q hDQ
  rw [relIndex_range_eq_index_comap, comap_norm P Q hP hQ, eP] at tP
  rw [relIndex_range_eq_index_comap, comap_diff P Q hP hQ, eQ] at tQ
  have hc : Nat.card (nsmulAddMonoidHom (α := P) 2).ker =
      Nat.card (nsmulAddMonoidHom (α := Q) 2).ker := by
    have key : ∀ x : M, 2 • x = 0 → (σ x = x ↔ σ x = -x) := by
      intro x hx
      have : -x = x := by rw [neg_eq_iff_add_eq_zero, ← two_nsmul, hx]
      rw [this]
    refine Nat.card_congr ⟨fun x => ⟨⟨x.1.1, ?_⟩, ?_⟩, fun x => ⟨⟨x.1.1, ?_⟩, ?_⟩, fun x => rfl,
      fun x => rfl⟩
    · have h2 : 2 • x.1.1 = 0 := by
        have := x.2; rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at this
        exact congrArg Subtype.val this
      rw [hQ, mem_anti, ← key _ h2, ← mem_fixed]; exact x.1.2
    · rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]; ext
      have := x.2; rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at this
      simpa using congrArg Subtype.val this
    · have h2 : 2 • x.1.1 = 0 := by
        have := x.2; rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at this
        exact congrArg Subtype.val this
      rw [hP, mem_fixed, key _ h2, ← mem_anti]; exact x.1.2
    · rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]; ext
      have := x.2; rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at this
      simpa using congrArg Subtype.val this
  have hc0 : Nat.card (nsmulAddMonoidHom (α := Q) 2).ker ≠ 0 := card_ker_two_ne_zero
  rw [hc] at tP
  have h0' : herbrand0 σ ≠ 0 := by
    intro h; unfold herbrand0 at h; rw [h, mul_zero] at tP
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) hc0 tP.symm
  have hm' : herbrandM1 σ ≠ 0 := by
    intro h; unfold herbrandM1 at h; rw [h, mul_zero] at tQ
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) hc0 tQ.symm
  refine ⟨?_, h0', hm'⟩
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hI0)
  unfold herbrand0 herbrandM1
  calc I * ((normHom σ).range.relIndex P * 2 ^ finrank ℤ Q)
      = (I * (normHom σ).range.relIndex P) * 2 ^ finrank ℤ Q := by ring
    _ = 2 ^ finrank ℤ P * Nat.card (nsmulAddMonoidHom (α := Q) 2).ker * 2 ^ finrank ℤ Q := by
        rw [tP]
    _ = 2 ^ finrank ℤ Q * Nat.card (nsmulAddMonoidHom (α := Q) 2).ker * 2 ^ finrank ℤ P := by ring
    _ = (I * (diffHom σ).range.relIndex Q) * 2 ^ finrank ℤ P := by rw [tQ]
    _ = I * ((diffHom σ).range.relIndex Q * 2 ^ finrank ℤ P) := by ring


omit hσ in
/-- **Rank–nullity for an endomorphism of a finitely generated abelian group:**
$\operatorname{rk} M = \operatorname{rk} \ker f + \operatorname{rk} f(M)$. -/
theorem finrank_eq_finrank_ker_add_range [Module.Finite ℤ M] (f : M →+ M) :
    finrank ℤ M = finrank ℤ f.ker + finrank ℤ f.range := by
  let g := f.toIntLinearMap
  have h1 := (LinearMap.ker g).finrank_quotient_add_finrank
  rw [g.quotKerEquivRange.finrank_eq] at h1
  rw [← h1, add_comm]
  congr 1

/-- **Ranks of the $\pm$ parts add up:** $\operatorname{rk} M = \operatorname{rk} M^+ + \operatorname{rk} M^-$ for a finitely
generated abelian group with an involution. (*Proof.* $1 - \sigma$ has kernel $M^+$ and image of finite
index $h^{-1}$ in $M^-$; apply rank–nullity and `finrank_eq_of_relIndex_ne_zero`.) -/
@[kb "milne2020cft" "Ch. VII §3 [unverified]"]
theorem finrank_fixed_add_anti [Module.Finite ℤ M] :
    finrank ℤ M = finrank ℤ (diffHom σ).ker + finrank ℤ (normHom σ).ker := by
  rw [finrank_eq_finrank_ker_add_range (diffHom σ)]
  congr 1
  exact finrank_eq_of_relIndex_ne_zero (range_diff_le hσ) (herbrand_formula hσ).2.2

end QuadFormsKB.HN
