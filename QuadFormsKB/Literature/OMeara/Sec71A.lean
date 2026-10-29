/-
# O'Meara §71A, §71C: cyclotomic preliminaries (71:1–71:5, 71:7–71:9, 71:14)

**Setting.** $F$ a field and $K$ an extension field of $F$ (`[Field K] [Algebra F K]`). O'Meara works over an
algebraic number field $F$; the definitions and 71:3–71:5 hold over any field in which $m \ne 0$, and are stated so.
A *primitive $m$-th root of unity* is Mathlib's `IsPrimitiveRoot ζ m` (O'Meara: $\zeta$ has period $m$).

**Proves**
* `IsAbsCyclotomic` (**71:1**, definition): $K/F$ is an *absolute $m$-cyclotomic extension* if $K = F(\zeta)$ for a
  primitive $m$-th root of unity $\zeta \in K$; `isAbsCyclotomic_iff_isCyclotomicExtension`: for $m \ge 1$ this is
  Mathlib's `IsCyclotomicExtension {m} F K`;
* `IsMCyclotomic` (**71:2**, definition): $K/F$ is *$m$-cyclotomic* if it is a subextension of an absolute
  $m$-cyclotomic extension (an $F$-algebra embedding of $K$ into one);
* `isAbsCyclotomic_iff_isSplittingField`, `exists_isAbsCyclotomic` (**71:3**): $K/F$ is absolute $m$-cyclotomic if and
  only if $K$ is a splitting field of $x^m - 1$ over $F$ (assuming $m \ne 0$ in $F$); such an extension exists;
* `isPrimitiveRoot_mul_of_coprime`, `adjoin_pair_eq_adjoin_mul` (**71:4**): for coprime $m, n$, $\zeta_m\zeta_n$ is a
  primitive $mn$-th root of unity and $F(\zeta_m, \zeta_n) = F(\zeta_m\zeta_n)$;
* `isAbsCyclotomic_sup` (**71:5**): inside a common extension $H$, the compositum of an absolute $m$-cyclotomic and an
  absolute $n$-cyclotomic extension, $m, n$ coprime, is absolute $mn$-cyclotomic;
* `finite_setOf_ramified_rat` (**71:7**, special case $F = \mathbb Q$): a number field $H$ is unramified over
  $\mathbb Q$ at all but finitely many primes $p$ (the general case is `finite_setOf_ramificationIdx_ne_one` in
  `Sec71C.lean`);
* `finrank_isAbsCyclotomic_prime` (**71:8**): for a number field $F$ and every prime $p \nmid \operatorname{disc} F$
  (almost all $p$), an absolute $p$-cyclotomic extension of $F$ has degree $p - 1$; `finrank_isAbsCyclotomic_prime_rat`
  is the case $F = \mathbb Q$ (every prime);
* `finrank_sup_of_le_adjoin_primitiveRoot` (**71:9**): for a finite extension $H/F$ of number fields in a field $C$ and
  every prime $p \nmid \operatorname{disc} H$, a subextension $K \subseteq F(\zeta_p)$ satisfies $[KH : F] = [K:F][H:F]$
  (equivalently $[KH : H] = [K : F]$); proved, as in the book, from 71:8 for $F$ and for $H$;
* `infinite_setOf_even_orderOf` (**71:14**): for a natural number $a \ge 2$ there are infinitely many primes $p$ such
  that $a$ has even period modulo $p$.

**Proof notes.** 71:1–71:5 and the cases $F = \mathbb Q$ of 71:7, 71:8 are short derivations from Mathlib's cyclotomic theory
(`IsCyclotomicExtension`, `CyclotomicField`, `IsPrimitiveRoot.adjoin_pair_eq`, `NumberField.discr`); 71:8 is proved by linear
disjointness of $\mathbb Q(\zeta_p)$ and $F$ when $p \nmid \operatorname{disc} F$ (coprime discriminants), not by
O'Meara's local Eisenstein argument. 71:14 follows
O'Meara's proof: an odd prime $p$ dividing $a^{2^k} + 1$ (which exists, as $a^{2^k}+1 > 2$ is not divisible by $4$)
gives $a$ of order exactly $2^{k+1}$ mod $p$; since this order divides $p - 1$, these primes are unbounded.
-/
import Mathlib
import QuadFormsKB.Citation

open Polynomial

noncomputable section

namespace QuadFormsKB.OMeara

section Cyclotomic

universe u v

variable (m : ℕ) (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K]

/-- **Definition 71:1** (O'Meara 1963, p. 191): $K/F$ is an *absolute $m$-cyclotomic extension* if $K = F(\zeta)$ for
some primitive $m$-th root of unity $\zeta \in K$. -/
@[kb "omeara1963" "§71A, 71:1, p. 191"]
def IsAbsCyclotomic : Prop :=
  ∃ ζ : K, IsPrimitiveRoot ζ m ∧ IntermediateField.adjoin F {ζ} = ⊤

/-- **Definition 71:2** (O'Meara 1963, p. 191): $K/F$ is an *$m$-cyclotomic extension* if it is a subextension of an
absolute $m$-cyclotomic extension $L/F$, i.e. there is an $F$-algebra embedding $K \to L$. -/
@[kb "omeara1963" "§71A, 71:2, p. 191"]
def IsMCyclotomic : Prop :=
  ∃ (L : Type v) (_ : Field L) (_ : Algebra F L), IsAbsCyclotomic m F L ∧ Nonempty (K →ₐ[F] L)

/-- An absolute $m$-cyclotomic extension is $m$-cyclotomic (O'Meara 1963, 71:2, p. 191). -/
theorem IsAbsCyclotomic.isMCyclotomic {m : ℕ} {F : Type u} {K : Type v} [Field F] [Field K] [Algebra F K]
    (h : IsAbsCyclotomic m F K) : IsMCyclotomic m F K :=
  ⟨K, inferInstance, inferInstance, h, ⟨AlgHom.id F K⟩⟩

variable {m F K}

/-- For $m \ge 1$, O'Meara's absolute $m$-cyclotomic extensions (71:1) are Mathlib's `IsCyclotomicExtension {m} F K`. -/
@[kb "omeara1963" "§71A, 71:1, p. 191 (as IsCyclotomicExtension)"]
theorem isAbsCyclotomic_iff_isCyclotomicExtension [NeZero m] :
    IsAbsCyclotomic m F K ↔ IsCyclotomicExtension {m} F K := by
  constructor
  · rintro ⟨ζ, hζ, htop⟩
    have hint : IsIntegral F ζ := (hζ.isIntegral (NeZero.pos m)).tower_top
    have hadj : Algebra.adjoin F {ζ} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, htop,
        IntermediateField.top_toSubalgebra]
    rw [IsCyclotomicExtension.iff_singleton]
    refine ⟨⟨ζ, hζ⟩, fun x => ?_⟩
    have hx : x ∈ Algebra.adjoin F {ζ} := hadj ▸ Algebra.mem_top
    have hsub : ({ζ} : Set K) ⊆ {b : K | b ^ m = 1} := by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hζ.pow_eq_one
    exact Algebra.adjoin_mono (R := F) hsub hx
  · intro h
    obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot F K (Set.mem_singleton m) (NeZero.ne m)
    refine ⟨ζ, hζ, ?_⟩
    have hint : IsIntegral F ζ := (hζ.isIntegral (NeZero.pos m)).tower_top
    rw [← IntermediateField.toSubalgebra_inj,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ, IntermediateField.top_toSubalgebra]

/-- **Example 71:3** (O'Meara 1963, p. 191): if $m \ne 0$ in $F$, then $K/F$ is an absolute $m$-cyclotomic extension if
and only if $K$ is a splitting field of $x^m - 1$ over $F$. -/
@[kb "omeara1963" "§71A, 71:3, p. 191"]
theorem isAbsCyclotomic_iff_isSplittingField [NeZero m] [NeZero (m : F)] :
    IsAbsCyclotomic m F K ↔ IsSplittingField F K (X ^ m - 1) := by
  rw [isAbsCyclotomic_iff_isCyclotomicExtension]
  constructor
  · intro h; exact IsCyclotomicExtension.isSplittingField_X_pow_sub_one m F K
  · intro h
    have := IsCyclotomicExtension.isSplittingField_X_pow_sub_one m F (CyclotomicField m F)
    have e : K ≃ₐ[F] CyclotomicField m F :=
      (IsSplittingField.algEquiv K (X ^ m - 1 : F[X])).trans
        (IsSplittingField.algEquiv (CyclotomicField m F) (X ^ m - 1 : F[X])).symm
    exact IsCyclotomicExtension.equiv {m} F (CyclotomicField m F) e.symm

/-- **Example 71:3, existence** (O'Meara 1963, p. 191): if $m \ne 0$ in $F$, then $F$ has an absolute $m$-cyclotomic
extension (`CyclotomicField m F`). -/
@[kb "omeara1963" "§71A, 71:3, p. 191 (existence)"]
theorem exists_isAbsCyclotomic [NeZero m] [NeZero (m : F)] :
    IsAbsCyclotomic m F (CyclotomicField m F) :=
  isAbsCyclotomic_iff_isCyclotomicExtension.mpr inferInstance

end Cyclotomic

section Compositum

variable {F H : Type*} [Field F] [Field H] [Algebra F H]

/-- **Example 71:4, first part** (O'Meara 1963, p. 191): if $\zeta_m$, $\zeta_n$ are primitive $m$-th and $n$-th roots
of unity in a field $H$ with $m, n$ coprime, then $\zeta_m\zeta_n$ is a primitive $mn$-th root of unity. -/
@[kb "omeara1963" "§71A, 71:4, p. 191 (ζ_m ζ_n is a primitive mn-th root)"]
theorem isPrimitiveRoot_mul_of_coprime {m n : ℕ} {ζm ζn : H} (hm : IsPrimitiveRoot ζm m)
    (hn : IsPrimitiveRoot ζn n) (hmn : m.Coprime n) : IsPrimitiveRoot (ζm * ζn) (m * n) := by
  rw [IsPrimitiveRoot.iff_orderOf, (Commute.all ζm ζn).orderOf_mul_eq_mul_orderOf_of_coprime,
    ← hm.eq_orderOf, ← hn.eq_orderOf]
  rwa [← hm.eq_orderOf, ← hn.eq_orderOf]

/-- **Example 71:4, second part** (O'Meara 1963, p. 191): for coprime $m, n \ge 1$ and primitive roots
$\zeta_m, \zeta_n \in H$, $F(\zeta_m, \zeta_n) = F(\zeta_m\zeta_n)$. -/
@[kb "omeara1963" "§71A, 71:4, p. 191 (F(ζ_m, ζ_n) = F(ζ_m ζ_n))"]
theorem adjoin_pair_eq_adjoin_mul {m n : ℕ} [NeZero m] [NeZero n] {ζm ζn : H} (hm : IsPrimitiveRoot ζm m)
    (hn : IsPrimitiveRoot ζn n) (hmn : m.Coprime n) :
    IntermediateField.adjoin F {ζm, ζn} = IntermediateField.adjoin F {ζm * ζn} := by
  have hmul := isPrimitiveRoot_mul_of_coprime hm hn hmn
  have hlcm : m.lcm n = m * n := hmn.lcm_eq_mul
  have hmul' : IsPrimitiveRoot (ζm * ζn) (m.lcm n) := hlcm ▸ hmul
  have h := hm.adjoin_pair_eq F hn (NeZero.ne m) (NeZero.ne n) hmul'
  have hi : ∀ x ∈ ({ζm, ζn} : Set H), IsAlgebraic F x := by
    rintro x (rfl | rfl)
    · exact (hm.isIntegral (NeZero.pos m)).tower_top.isAlgebraic
    · exact (hn.isIntegral (NeZero.pos n)).tower_top.isAlgebraic
  have hi' : ∀ x ∈ ({ζm * ζn} : Set H), IsAlgebraic F x := by
    rintro x rfl
    exact (hmul.isIntegral (Nat.pos_of_ne_zero (mul_ne_zero (NeZero.ne m) (NeZero.ne n)))).tower_top.isAlgebraic
  rw [← IntermediateField.toSubalgebra_inj, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic hi,
    IntermediateField.adjoin_toSubalgebra_of_isAlgebraic hi', h]

/-- **Example 71:5** (O'Meara 1963, p. 191): if $K_1 = F(\zeta_m)$ and $K_2 = F(\zeta_n)$ are absolute $m$- and
$n$-cyclotomic subextensions of $H/F$ with $m, n$ coprime, their compositum $K_1K_2$ is an absolute $mn$-cyclotomic
extension of $F$ (generated by $\zeta_m\zeta_n$). -/
@[kb "omeara1963" "§71A, 71:5, p. 191"]
theorem isAbsCyclotomic_sup {m n : ℕ} [NeZero m] [NeZero n] {ζm ζn : H} (hm : IsPrimitiveRoot ζm m)
    (hn : IsPrimitiveRoot ζn n) (hmn : m.Coprime n) :
    IntermediateField.adjoin F {ζm} ⊔ IntermediateField.adjoin F {ζn} =
      IntermediateField.adjoin F {ζm * ζn} ∧ IsPrimitiveRoot (ζm * ζn) (m * n) := by
  refine ⟨?_, isPrimitiveRoot_mul_of_coprime hm hn hmn⟩
  rw [← adjoin_pair_eq_adjoin_mul hm hn hmn, ← IntermediateField.adjoin_union, Set.singleton_union]

end Compositum

section Rat

open NumberField

/-- **Proposition 71:7, the case $F = \mathbb Q$** (O'Meara 1963, p. 192): a number field $H$ is unramified over
$\mathbb Q$ at almost all primes: the set of primes $p$ such that $p\mathcal O_H$ is ramified is finite (they divide
the discriminant of $H$). -/
@[kb "omeara1963" "§71A, 71:7, p. 192 (special case F = ℚ)"]
theorem finite_setOf_ramified_rat (H : Type*) [Field H] [NumberField H] :
    {p : ℕ | p.Prime ∧ ¬ Algebra.IsUnramifiedIn (𝓞 H) (Ideal.span {(p : ℤ)})}.Finite := by
  refine ((discr H).natAbs.primeFactors.finite_toSet).subset ?_
  rintro p ⟨hp, hram⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdvd : (p : ℤ) ∣ discr H := by
    by_contra h
    exact hram ((NumberField.not_dvd_discr_iff_isUnramifiedIn H (𝓞 H) hpZ).mp h)
  simp only [Finset.mem_coe, Nat.mem_primeFactors]
  exact ⟨hp, Int.natCast_dvd.mp hdvd, Int.natAbs_ne_zero.mpr (discr_ne_zero H)⟩

/-- **Proposition 71:8, the case $F = \mathbb Q$** (O'Meara 1963, p. 192): for every prime $p$, an absolute
$p$-cyclotomic extension $K$ of $\mathbb Q$ has degree $[K : \mathbb Q] = p - 1$. -/
@[kb "omeara1963" "§71A, 71:8, p. 192 (special case F = ℚ)"]
theorem finrank_isAbsCyclotomic_prime_rat {p : ℕ} (hp : p.Prime) (K : Type*) [Field K] [CharZero K]
    (h : IsAbsCyclotomic p ℚ K) : Module.finrank ℚ K = p - 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have := isAbsCyclotomic_iff_isCyclotomicExtension.mp h
  rw [IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat hp.pos), Nat.totient_prime hp]

/-- **Proposition 71:8** (O'Meara 1963, p. 192): for a number field $F$ and every prime $p$ not dividing the
discriminant of $F$ (so for almost all primes $p$, as $\operatorname{disc} F \ne 0$), an absolute $p$-cyclotomic extension $K/F$ has degree
$[K : F] = p - 1$. *Proof* (differs from the book's local Eisenstein argument): inside $K$, $\mathbb Q(\zeta)$ is Galois
over $\mathbb Q$ with discriminant $\pm p^{p-2}$, prime to the discriminant of $F$, so $\mathbb Q(\zeta)$ and $F$ are
linearly disjoint over $\mathbb Q$ (`NumberField.linearDisjoint_of_isGalois_isCoprime_discr`), whence
$[K:\mathbb Q] = [\mathbb Q(\zeta):\mathbb Q]\,[F:\mathbb Q] = (p-1)[F:\mathbb Q]$. -/
@[kb "omeara1963" "§71A, 71:8, p. 192"]
theorem finrank_isAbsCyclotomic_prime (F : Type*) [Field F] [NumberField F] {p : ℕ} (hp : p.Prime)
    (hdisc : ¬ (p : ℤ) ∣ discr F) (K : Type*) [Field K] [Algebra F K]
    (h : IsAbsCyclotomic p F K) : Module.finrank F K = p - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ, htop⟩ := h
  have hintF : IsIntegral F ζ := (hζ.isIntegral hp.pos).tower_top
  have : FiniteDimensional F (⊤ : IntermediateField F K) := by
    rw [← htop]; exact IntermediateField.adjoin.finiteDimensional hintF
  have : FiniteDimensional F K := (IntermediateField.topEquiv (F := F) (E := K)).toLinearEquiv.finiteDimensional
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have : NumberField K := NumberField.of_module_finite F K
  let K₁ : IntermediateField ℚ K := IntermediateField.adjoin ℚ {ζ}
  have : IsCyclotomicExtension {p} ℚ K₁ := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : IsGalois ℚ K₁ := IsCyclotomicExtension.isGalois {p} ℚ K₁
  let K₂ : IntermediateField ℚ K := (IsScalarTower.toAlgHom ℚ F K).fieldRange
  let e : F ≃ₐ[ℚ] K₂ := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ F K)
  have hd₂ : discr K₂ = discr F := (discr_eq_discr_of_algEquiv F e).symm
  have hd₁ : discr K₁ = (-1) ^ ((p - 1) / 2) * p ^ (p - 2) := IsCyclotomicExtension.Rat.discr_prime p K₁
  have hcop : IsCoprime (discr K₁) (discr K₂) := by
    rw [hd₁, hd₂]
    refine IsCoprime.mul_left ?_ (IsCoprime.pow_left ((Prime.coprime_iff_not_dvd
      (Nat.prime_iff_prime_int.mp hp)).mpr hdisc))
    rcases neg_one_pow_eq_or ℤ ((p - 1) / 2) with h | h <;> rw [h]
    · exact isCoprime_one_left
    · exact isCoprime_one_left.neg_left
  have hdisj := linearDisjoint_of_isGalois_isCoprime_discr K K₁ K₂ hcop
  have hsup : K₁ ⊔ K₂ = ⊤ := by
    let M : IntermediateField F K :=
      { (K₁ ⊔ K₂).toSubfield with
        algebraMap_mem' := fun f => (le_sup_right : K₂ ≤ K₁ ⊔ K₂) ⟨f, rfl⟩ }
    have hζM : ζ ∈ M := (le_sup_left : K₁ ≤ K₁ ⊔ K₂) (IntermediateField.mem_adjoin_simple_self ℚ ζ)
    have hle : IntermediateField.adjoin F {ζ} ≤ M :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hζM)
    rw [htop] at hle
    exact eq_top_iff.mpr fun x _ => hle (IntermediateField.mem_top (x := x))
  have h1 : Module.finrank ℚ K₁ = p - 1 := by
    rw [IsCyclotomicExtension.finrank K₁ (Polynomial.cyclotomic.irreducible_rat hp.pos), Nat.totient_prime hp]
  have h2 : Module.finrank ℚ K₂ = Module.finrank ℚ F := e.toLinearEquiv.finrank_eq.symm
  have h3 := hdisj.finrank_sup
  rw [hsup, IntermediateField.finrank_top', h1, h2] at h3
  have h4 := Module.finrank_mul_finrank ℚ F K
  rw [h3] at h4
  have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  rw [mul_comm (p - 1)] at h4
  exact Nat.eq_of_mul_eq_mul_left hpos h4

/-- 71:8 in the form used for 71:9: if $p \nmid \operatorname{disc} H$ and $\zeta$ is a primitive $p$-th root of unity
in an extension field $C$ of the number field $H$, then $[H(\zeta) : H] = p - 1$. -/
theorem finrank_adjoin_primitiveRoot (H : Type*) [Field H] [NumberField H] {p : ℕ} (hp : p.Prime)
    (hdisc : ¬ (p : ℤ) ∣ discr H) {C : Type*} [Field C] [Algebra H C] {ζ : C} (hζ : IsPrimitiveRoot ζ p) :
    Module.finrank H (IntermediateField.adjoin H {ζ}) = p - 1 := by
  apply finrank_isAbsCyclotomic_prime H hp hdisc
  refine ⟨IntermediateField.AdjoinSimple.gen H ζ, ?_, ?_⟩
  · refine IsPrimitiveRoot.of_map_of_injective (f := algebraMap (IntermediateField.adjoin H {ζ}) C) ?_
      (RingHom.injective (algebraMap (IntermediateField.adjoin H {ζ}) C))
    rwa [IntermediateField.AdjoinSimple.algebraMap_gen]
  · apply IntermediateField.map_injective (IntermediateField.val (IntermediateField.adjoin H {ζ}))
    rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.coe_val,
      IntermediateField.AdjoinSimple.coe_gen, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]

/-- **Proposition 71:9** (O'Meara 1963, pp. 192–193): let $H/F$ be a finite extension of number fields inside a field
$C$. For every prime $p$ not dividing $\operatorname{disc} H$ (so for almost all $p$), every $p$-cyclotomic subextension
$K \subseteq F(\zeta_p)$ of $C/F$ ($\zeta_p \in C$ a primitive $p$-th root of unity) is linearly disjoint from $H$:
$[KH : F] = [K : F]\,[H : F]$, i.e. $[KH : H] = [K : F]$. -/
@[kb "omeara1963" "§71A, 71:9, pp. 192–193"]
theorem finrank_sup_of_le_adjoin_primitiveRoot {F : Type*} [Field F] [NumberField F] {C : Type*} [Field C]
    [Algebra F C] (H : IntermediateField F C) [FiniteDimensional F H] [NumberField H] {p : ℕ} (hp : p.Prime)
    (hdisc : ¬ (p : ℤ) ∣ discr H) {ζ : C} (hζ : IsPrimitiveRoot ζ p) (K : IntermediateField F C)
    (hK : K ≤ IntermediateField.adjoin F {ζ}) :
    Module.finrank F ↥(K ⊔ H) = Module.finrank F K * Module.finrank F H := by
  have hFdisc : ¬ (p : ℤ) ∣ discr F := fun h => hdisc (h.trans (NumberField.discr_dvd_discr F H))
  have hE := finrank_adjoin_primitiveRoot F hp hFdisc hζ
  have hHE := finrank_adjoin_primitiveRoot H hp hdisc hζ
  have hint : IsIntegral F ζ := (hζ.isIntegral hp.pos).tower_top
  have : FiniteDimensional F (IntermediateField.adjoin F {ζ}) := IntermediateField.adjoin.finiteDimensional hint
  have hsup : Module.finrank F ↥(IntermediateField.adjoin F {ζ} ⊔ H) =
      Module.finrank F (IntermediateField.adjoin F {ζ}) * Module.finrank F H := by
    rw [sup_comm, ← IntermediateField.restrictScalars_adjoin_eq_sup, hE]
    have : Module.Free H (IntermediateField.adjoin H {ζ}) := Module.Free.of_divisionRing _ _
    have h := Module.finrank_mul_finrank F H (IntermediateField.adjoin H {ζ})
    rw [hHE] at h
    rw [mul_comm]
    exact h.symm
  exact ((IntermediateField.LinearDisjoint.of_finrank_sup hsup).of_le_left hK).finrank_sup

end Rat

section Period

/-- An odd prime $p$ dividing $a^{2^k} + 1$: then $a$ has order $2^{k+1}$ modulo $p$. -/
private theorem exists_prime_orderOf (a k : ℕ) (ha : 2 ≤ a) (hk : 1 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ((a : ZMod p) ≠ 0) ∧ orderOf (a : ZMod p) = 2 ^ (k + 1) := by
  -- `a ^ (2 ^ k) + 1` is not divisible by `4`
  have h4 : ¬ 4 ∣ a ^ (2 ^ k) + 1 := by
    have hb : a ^ (2 ^ k) = (a ^ (2 ^ (k - 1))) ^ 2 := by
      rw [← pow_mul, ← pow_succ]; congr 2; omega
    rw [hb]
    rcases Nat.even_or_odd (a ^ (2 ^ (k - 1))) with ⟨c, hc⟩ | ⟨c, hc⟩ <;> rw [hc] <;> ring_nf <;> omega
  have hgt : 2 < a ^ (2 ^ k) + 1 := by
    have : 2 ≤ a ^ (2 ^ k) := le_trans ha (Nat.le_self_pow (by positivity) a)
    omega
  -- so it has an odd prime factor
  obtain ⟨p, hp, hpd, hp2⟩ : ∃ p, p.Prime ∧ p ∣ a ^ (2 ^ k) + 1 ∧ p ≠ 2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨e, hpow⟩ : ∃ e, a ^ (2 ^ k) + 1 = 2 ^ e :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) fun hp hd => hcon _ hp hd⟩
    have he : 2 ≤ e := by
      by_contra he; push Not at he
      interval_cases e <;> omega
    exact h4 (hpow ▸ (pow_dvd_pow 2 he))
  have : Fact p.Prime := ⟨hp⟩
  have hx : (a : ZMod p) ^ (2 ^ k) = -1 := by
    have := (ZMod.natCast_eq_zero_iff (a ^ (2 ^ k) + 1) p).mpr hpd
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have hne : (-1 : ZMod p) ≠ 1 := fun h =>
    hp2 (by rw [← ZMod.ringChar_zmod_n p]; exact neg_one_eq_one_iff.mp h)
  refine ⟨p, hp, hp2, ?_, orderOf_eq_prime_pow (by rw [hx]; exact hne) ?_⟩
  · intro h0
    rw [h0, zero_pow (by positivity)] at hx
    exact neg_ne_zero.mpr one_ne_zero hx.symm
  · rw [pow_succ, pow_mul, hx]; norm_num

/-- **Lemma 71:14** (O'Meara 1963, p. 197): for a natural number $a \ge 2$ there are infinitely many primes $p$ such that
$a$ has even period modulo $p$, i.e. $p \nmid a$ and the multiplicative order of $a$ in $(\mathbb Z/p\mathbb Z)^\times$
is even. -/
@[kb "omeara1963" "§71C, 71:14, p. 197"]
theorem infinite_setOf_even_orderOf (a : ℕ) (ha : 2 ≤ a) :
    {p : ℕ | p.Prime ∧ ¬ p ∣ a ∧ Even (orderOf (a : ZMod p))}.Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨N, hN⟩ => ?_
  obtain ⟨p, hp, hp2, ha0, hord⟩ := exists_prime_orderOf a (N + 1) ha (by omega)
  have : Fact p.Prime := ⟨hp⟩
  have hmem : p ∈ {p : ℕ | p.Prime ∧ ¬ p ∣ a ∧ Even (orderOf (a : ZMod p))} := by
    refine ⟨hp, fun h => ha0 ((ZMod.natCast_eq_zero_iff a p).mpr h), ?_⟩
    rw [hord]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hle := hN hmem
  have hdvd : orderOf (a : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one ha0
  rw [hord] at hdvd
  have h1 := Nat.le_of_dvd (by have := hp.two_le; omega) hdvd
  have h2 : N < 2 ^ (N + 1 + 1) := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
  omega

end Period

end QuadFormsKB.OMeara
