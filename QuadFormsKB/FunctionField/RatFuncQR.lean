/-
# Quadratic reciprocity in $\mathbb{F}_q[t]$

For a finite field $k = \mathbb{F}_q$ of odd characteristic and a monic irreducible $P \in k[t]$, the
**Legendre symbol** $\left(\frac{a}{P}\right)$ of $a \in k[t]$ is $0$ if $P \mid a$, $1$ if $a$ is a nonzero
square modulo $P$, and $-1$ otherwise (`legendreSym`; Rosen, *Number Theory in Function Fields*, Ch. 3). It is the
quadratic character of the residue field $k[t]/(P) \cong \mathbb{F}_{q^{\deg P}}$ evaluated at $a \bmod P$.

**Quadratic reciprocity** (`legendreSym_mul_legendreSym`; Rosen Thm. 3.3, due to Dedekind and Artin): for distinct
monic irreducibles $P, Q \in k[t]$,
$$\left(\frac{Q}{P}\right)\left(\frac{P}{Q}\right) = \chi(-1)^{\deg P \deg Q}
  = (-1)^{\frac{q-1}{2} \deg P \deg Q},$$
with $\chi$ the quadratic character of $k$. The supplementary law for constants is
$\left(\frac{c}{P}\right) = \chi(c)^{\deg P}$ (`legendreSym_C`).

*Proof* (the resultant proof, as in Rosen's proof of Thm. 3.3, which computes $\left(\frac{Q}{P}\right)$ through the
roots of $P$): let $F = k[t]/(P)$ and $\alpha$ the class of $t$. The norm $N_{F/k}(Q(\alpha))$ is the product of
$Q(\beta)$ over the roots $\beta$ of $P$, which is the resultant $\operatorname{Res}(P, Q)$
(`norm_mk_eq_resultant`). By Euler's criterion in $F$ and $N_{F/k}(x) = x^{(q^d - 1)/(q - 1)}$,
$\left(\frac{Q}{P}\right) = Q(\alpha)^{(q^d-1)/2} = N_{F/k}(Q(\alpha))^{(q-1)/2} = \chi(\operatorname{Res}(P,Q))$
(`legendreSym_eq_quadraticChar_resultant`). Reciprocity is then
$\operatorname{Res}(P, Q) = (-1)^{\deg P \deg Q} \operatorname{Res}(Q, P)$ (Mathlib's `Polynomial.resultant_comm`).

Indices are 0-based.
-/
import Mathlib
import QuadFormsKB.Citation

open Polynomial

namespace QuadFormsKB.RatFuncQR

variable {k : Type} [Field k]

open scoped Classical in
/-- **The Legendre symbol $\left(\frac{a}{P}\right)$ in $k[t]$** (Rosen, Ch. 3, p. 24): $0$ if $P \mid a$; $1$ if
$a \equiv r^2 \pmod P$ for some $r \in k[t]$ (and $P \nmid a$); $-1$ otherwise. Meaningful for $P$ irreducible. -/
@[kb "rosen2002" "Ch. 3, p. 24 (definition of the Legendre symbol (a/P)) [unverified]"]
noncomputable def legendreSym (P a : k[X]) : ℤ :=
  if P ∣ a then 0 else if ∃ r : k[X], P ∣ r ^ 2 - a then 1 else -1

section Norm

variable (P : k[X]) [hP : Fact (Irreducible P)]

/-- The residue field $k[t]/(P)$ (as `AdjoinRoot P`) is finite-dimensional over $k$. -/
instance : FiniteDimensional k (AdjoinRoot P) :=
  (AdjoinRoot.powerBasis hP.out.ne_zero).finite

/-- **The norm of $a \bmod P$ is the resultant** $\operatorname{Res}(P, a)$, for $P$ monic irreducible and separable
(e.g. over a perfect field): $N_{(k[t]/(P))/k}(a(\alpha)) = \prod_{P(\beta) = 0} a(\beta) = \operatorname{Res}(P, a)$. -/
theorem norm_mk_eq_resultant (hPm : P.Monic) [Algebra.IsSeparable k (AdjoinRoot P)] (a : k[X]) :
    Algebra.norm k (AdjoinRoot.mk P a) = resultant P a := by
  classical
  set Ω := AlgebraicClosure k
  apply (algebraMap k Ω).injective
  rw [Algebra.norm_eq_prod_embeddings k Ω]
  have hP0 : P ≠ 0 := hP.out.ne_zero
  have hsep : (P.map (algebraMap k Ω)).Separable := by
    have : (minpoly k (AdjoinRoot.root P)).Separable := Algebra.IsSeparable.isSeparable k _
    rw [AdjoinRoot.minpoly_root hP0, hPm.leadingCoeff, inv_one, C_1, mul_one] at this
    exact this.map
  -- the product over embeddings is a product over the roots of `P` in `Ω`
  have hσ : ∀ σ : AdjoinRoot P →ₐ[k] Ω, σ (AdjoinRoot.mk P a) = aeval (σ (AdjoinRoot.root P)) a := by
    intro σ
    rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_algHom_apply]
  rw [Fintype.prod_equiv (AdjoinRoot.equiv Ω k P hP0) _ (fun x => aeval (x : Ω) a)
    (fun σ => by rw [hσ]; rfl)]
  rw [Finset.prod_mem_multiset _ _ (fun x => aeval x a) (fun _ => rfl), Finset.prod_eq_multiset_prod,
    Multiset.toFinset_val, Multiset.dedup_eq_self.mpr (nodup_roots hsep)]
  have hres := resultant_eq_prod_eval (P.map (algebraMap k Ω)) (a.map (algebraMap k Ω))
    (a.map (algebraMap k Ω)).natDegree le_rfl (IsAlgClosed.splits _)
  rw [natDegree_map, natDegree_map, resultant_map_map, (hPm.map _).leadingCoeff, one_pow,
    one_mul] at hres
  rw [show P.resultant a = P.resultant a P.natDegree a.natDegree from rfl, hres]
  congr 1
  refine Multiset.map_congr rfl fun x _ => ?_
  rw [eval_map_algebraMap]

/-- **Squares modulo $P$**: $a$ is a square in $k[t]/(P)$ iff $a \equiv r^2 \pmod P$ for some $r \in k[t]$. -/
lemma isSquare_mk_iff (a : k[X]) :
    IsSquare (AdjoinRoot.mk P a) ↔ ∃ r : k[X], P ∣ r ^ 2 - a := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective s
    refine ⟨r, ?_⟩
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, hs, sq, sub_self]
  · rintro ⟨r, hr⟩
    rw [← AdjoinRoot.mk_eq_zero, map_sub, sub_eq_zero, map_pow] at hr
    exact ⟨AdjoinRoot.mk P r, by rw [← hr, sq]⟩

/-- The Legendre symbol is the quadratic character of the residue field $k[t]/(P)$ at $a \bmod P$. -/
lemma legendreSym_eq_quadraticChar [Fintype (AdjoinRoot P)] [DecidableEq (AdjoinRoot P)] (a : k[X]) :
    legendreSym P a = quadraticChar (AdjoinRoot P) (AdjoinRoot.mk P a) := by
  classical
  rw [quadraticChar_apply, quadraticCharFun, legendreSym]
  by_cases h : P ∣ a
  · rw [if_pos h, if_pos (AdjoinRoot.mk_eq_zero.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (AdjoinRoot.mk_eq_zero.mp h'))]
    by_cases h' : ∃ r : k[X], P ∣ r ^ 2 - a
    · rw [if_pos h', if_pos ((isSquare_mk_iff P a).mpr h')]
    · rw [if_neg h', if_neg (fun h'' => h' ((isSquare_mk_iff P a).mp h''))]

end Norm

/-- Arithmetic: for odd $q$ and $Q = q^d$, $\lfloor Q/2 \rfloor = \frac{Q-1}{q-1} \lfloor q/2 \rfloor$. -/
lemma half_card_eq (q d : ℕ) (hq : Odd q) (hq1 : 1 < q) :
    q ^ d / 2 = (q ^ d - 1) / (q - 1) * (q / 2) := by
  obtain ⟨m, hm⟩ : q - 1 ∣ q ^ d - 1 := by simpa using Nat.sub_dvd_pow_sub_pow q 1 d
  have hQ : Odd (q ^ d) := hq.pow
  obtain ⟨j, hj⟩ := hq
  obtain ⟨i, hi⟩ := hQ
  have hq0 : 0 < q - 1 := by omega
  rw [hm, Nat.mul_div_cancel_left _ hq0]
  have h1 : q ^ d / 2 = i := by omega
  have h2 : q / 2 = j := by omega
  rw [h1, h2]
  have h3 : 2 * i = 2 * j * m := by
    have : q ^ d - 1 = 2 * i := by omega
    rw [← this, hm]; congr 1; omega
  have h4 : i = j * m := by
    have := h3; rw [mul_assoc] at this; omega
  rw [h4, mul_comm]

/-- The quadratic character takes values in $\{0, 1, -1\}$. -/
lemma quadraticChar_mem {F : Type*} [Field F] [Fintype F] [DecidableEq F] (x : F) :
    quadraticChar F x ∈ ({0, 1, -1} : Set ℤ) := by
  by_cases hx : x = 0
  · simp [hx]
  · rcases quadraticChar_dichotomy hx with h | h <;> simp [h]

variable [Fintype k]

/-- **The Legendre symbol is the quadratic character of the resultant** (Euler's criterion in
$k[t]/(P) \cong \mathbb{F}_{q^d}$ and $N(x) = x^{(q^d-1)/(q-1)}$): for $P$ monic irreducible and $q$ odd,
$\left(\frac{a}{P}\right) = \chi(\operatorname{Res}(P, a))$, $\chi$ the quadratic character of $k$. -/
@[kb "rosen2002" "Ch. 3, proof of Thm. 3.3 [unverified]"]
theorem legendreSym_eq_quadraticChar_resultant [DecidableEq k] (hk : ringChar k ≠ 2) (P : k[X])
    (hP : Irreducible P) (hPm : P.Monic) (a : k[X]) :
    legendreSym P a = quadraticChar k (resultant P a) := by
  classical
  have : Fact (Irreducible P) := ⟨hP⟩
  set F := AdjoinRoot P
  have : Finite F := Module.finite_of_finite k
  let : Fintype F := Fintype.ofFinite F
  have hF : ringChar F ≠ 2 := by rwa [← Algebra.ringChar_eq k F]
  rw [legendreSym_eq_quadraticChar P a, ← norm_mk_eq_resultant P hPm a]
  set x := AdjoinRoot.mk P a
  apply Int.cast_injOn_of_ringChar_ne_two hF
  · exact quadraticChar_mem x
  · exact quadraticChar_mem _
  rw [quadraticChar_eq_pow_of_char_ne_two' hF, ← map_intCast (algebraMap k F),
    quadraticChar_eq_pow_of_char_ne_two' hk, map_pow, FiniteField.algebraMap_norm_eq_pow, ← pow_mul]
  congr 1
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := k) (V := F)]
  exact half_card_eq _ _ (Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hk)) Fintype.one_lt_card

/-- **The supplementary law for constants** (Rosen, Ch. 3): for $P$ monic irreducible and $c \in k$,
$\left(\frac{c}{P}\right) = \chi(c)^{\deg P}$. -/
@[kb "rosen2002" "Ch. 3, Prop. 3.2 [unverified]"]
theorem legendreSym_C [DecidableEq k] (hk : ringChar k ≠ 2) (P : k[X]) (hP : Irreducible P)
    (hPm : P.Monic) (c : k) :
    legendreSym P (C c) = quadraticChar k c ^ P.natDegree := by
  rw [legendreSym_eq_quadraticChar_resultant hk P hP hPm,
    show resultant P (C c) = resultant P (C c) P.natDegree 0 by rw [natDegree_C],
    resultant_C_zero_right, map_pow]

/-- **Quadratic reciprocity in $\mathbb{F}_q[t]$** (Rosen, Thm. 3.3; Dedekind, Artin), $q$ odd: for distinct monic
irreducibles $P, Q \in k[t]$,
$\left(\frac{Q}{P}\right)\left(\frac{P}{Q}\right) = \chi(-1)^{\deg P \deg Q}$, where $\chi(-1) = (-1)^{(q-1)/2}$ is
the quadratic character of $k$ at $-1$ (`legendreSym_mul_legendreSym'`). -/
@[kb "rosen2002" "Ch. 3, Thm. 3.3 (quadratic reciprocity law) [unverified]"]
theorem legendreSym_mul_legendreSym [DecidableEq k] (hk : ringChar k ≠ 2) (P Q : k[X])
    (hP : Irreducible P) (hPm : P.Monic) (hQ : Irreducible Q) (hQm : Q.Monic) (hPQ : P ≠ Q) :
    legendreSym P Q * legendreSym Q P = quadraticChar k (-1) ^ (P.natDegree * Q.natDegree) := by
  rw [legendreSym_eq_quadraticChar_resultant hk P hP hPm,
    legendreSym_eq_quadraticChar_resultant hk Q hQ hQm, resultant_comm, map_mul, map_pow,
    mul_assoc]
  have hcop : IsCoprime Q P := by
    rw [hQ.coprime_iff_not_dvd]
    intro hdvd
    apply hPQ
    exact (eq_of_monic_of_associated hQm hPm (hQ.associated_of_dvd hP hdvd)).symm
  have hne : resultant Q P ≠ 0 := resultant_ne_zero Q P hcop
  rw [← sq, quadraticChar_sq_one hne, mul_one]

/-- **Quadratic reciprocity in $\mathbb{F}_q[t]$, classical form** (Rosen, Thm. 3.3): for distinct monic irreducibles
$P, Q$ and $q = |k|$ odd, $\left(\frac{Q}{P}\right)\left(\frac{P}{Q}\right) = (-1)^{\frac{q-1}{2} \deg P \deg Q}$. -/
@[kb "rosen2002" "Ch. 3, Thm. 3.3 (quadratic reciprocity law) [unverified]"]
theorem legendreSym_mul_legendreSym' [DecidableEq k] (hk : ringChar k ≠ 2) (P Q : k[X])
    (hP : Irreducible P) (hPm : P.Monic) (hQ : Irreducible Q) (hQm : Q.Monic) (hPQ : P ≠ Q) :
    legendreSym P Q * legendreSym Q P =
      (-1) ^ ((Fintype.card k - 1) / 2 * P.natDegree * Q.natDegree) := by
  have hq := FiniteField.odd_card_of_char_ne_two hk
  rw [legendreSym_mul_legendreSym hk P Q hP hPm hQ hQm hPQ, quadraticChar_neg_one hk,
    ZMod.χ₄_eq_neg_one_pow hq, ← pow_mul, mul_assoc]
  congr 2
  omega

/-! ### The Jacobi symbol -/

open UniqueFactorizationMonoid in
/-- **The Jacobi symbol $\left(\frac{a}{b}\right)$** in $k[t]$ (Rosen, Ch. 3): for $b = \prod_i P_i$ (monic
irreducible $P_i$, with multiplicity), $\left(\frac{a}{b}\right) = \prod_i \left(\frac{a}{P_i}\right)$. -/
@[kb "rosen2002" "Ch. 3, p. 26 (Jacobi symbol) [unverified]"]
noncomputable def jacobiSym [DecidableEq k] (b a : k[X]) : ℤ :=
  ((normalizedFactors b).map fun P => legendreSym P a).prod

omit [Fintype k] in
lemma resultant_multiset_prod (m : Multiset k[X]) (hm : ∀ P ∈ m, P ≠ 0) (a : k[X]) :
    resultant m.prod a = (m.map fun P => resultant P a).prod := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [Multiset.prod_zero, Multiset.map_zero]
    rw [show (1 : k[X]) = C 1 from C_1.symm, show resultant (C (1 : k)) a = resultant (C 1) a 0 a.natDegree
      by rw [natDegree_C], resultant_C_zero_left, one_pow]
  | cons P m ih =>
    have hP : P ≠ 0 := hm P (Multiset.mem_cons_self _ _)
    have hm0 : m.prod ≠ 0 := Multiset.prod_ne_zero fun h => hm 0 (Multiset.mem_cons_of_mem h) rfl
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
      ← ih fun Q hQ => hm Q (Multiset.mem_cons_of_mem hQ),
      show resultant (P * m.prod) a = resultant (P * m.prod) a (P.natDegree + m.prod.natDegree) a.natDegree
        by rw [natDegree_mul hP hm0], resultant_mul_left _ _ _ _ le_rfl]

open UniqueFactorizationMonoid in
/-- **The Jacobi symbol is the quadratic character of the resultant:** for $b$ monic,
$\left(\frac{a}{b}\right) = \chi(\operatorname{Res}(b, a))$. -/
theorem jacobiSym_eq_quadraticChar_resultant [DecidableEq k] (hk : ringChar k ≠ 2) {b : k[X]}
    (hb : b.Monic) (a : k[X]) : jacobiSym b a = quadraticChar k (resultant b a) := by
  classical
  have hmon : ∀ P ∈ normalizedFactors b, P.Monic := fun P hP => by
    rw [← normalize_normalized_factor P hP]
    exact monic_normalize (ne_zero_of_mem_normalizedFactors hP)
  have hprodm : (normalizedFactors b).prod.Monic := by
    simpa using monic_multiset_prod_of_monic (normalizedFactors b) (fun P => P) hmon
  have hprod : (normalizedFactors b).prod = b :=
    eq_of_monic_of_associated hprodm hb (prod_normalizedFactors hb.ne_zero)
  conv_rhs => rw [← hprod]
  rw [resultant_multiset_prod _ (fun P hP => ne_zero_of_mem_normalizedFactors hP),
    map_multiset_prod, Multiset.map_map, jacobiSym]
  congr 1
  refine Multiset.map_congr rfl fun P hP => ?_
  exact legendreSym_eq_quadraticChar_resultant hk P (irreducible_of_normalized_factor P hP) (hmon P hP) a

/-- **Quadratic reciprocity for Jacobi symbols in $\mathbb{F}_q[t]$** (Rosen, Thm. 3.5): for coprime monic
$a, b \in k[t]$, $\left(\frac{a}{b}\right)\left(\frac{b}{a}\right) = \chi(-1)^{\deg a \deg b}
= (-1)^{\frac{q-1}{2}\deg a \deg b}$. -/
@[kb "rosen2002" "Ch. 3, Thm. 3.5 (reciprocity for Jacobi symbols) [unverified]"]
theorem jacobiSym_mul_jacobiSym [DecidableEq k] (hk : ringChar k ≠ 2) {a b : k[X]} (ha : a.Monic)
    (hb : b.Monic) (hab : IsCoprime a b) :
    jacobiSym b a * jacobiSym a b = quadraticChar k (-1) ^ (a.natDegree * b.natDegree) := by
  rw [jacobiSym_eq_quadraticChar_resultant hk hb, jacobiSym_eq_quadraticChar_resultant hk ha,
    resultant_comm, map_mul, map_pow, mul_assoc, mul_comm b.natDegree, ← sq,
    quadraticChar_sq_one (resultant_ne_zero a b hab), mul_one]
