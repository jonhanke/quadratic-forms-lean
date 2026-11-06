/-
# Cassels, Chapter 1, §1: local conditions, primitive solutions, and the integral Hasse principle

**Setting.** Integral forms `Q : QuadForm ℤ n` ($Q(\vec x) = \sum_{i \le j} c_{ij}x_ix_j$, $c_{ij} \in \mathbb Z$),
indices $0$-based ($x_0, \dots, x_{n-1}$; Cassels' $x_1, \dots, x_n$).

**Proves** (Cassels, *Rational Quadratic Forms*, Ch. 1, §1, pp. 2–3)
* (1.10): $x^2 + 82y^2 = 2$ has no integral solution, has a real solution, and $x^2 + 82y^2 \equiv 2 \pmod M$ is
  soluble for every $M \ge 1$ (`not_exists_int_eq_two`, `exists_real_eq_two`, `exists_int_modEq_two`); the
  congruences come from solutions in every $\mathbb Z_p$ by reduction modulo $p^e$ and the Chinese remainder theorem
  (`exists_zmod_root_of_padic`, for any integer polynomial).
* (1.12)–(1.14): primitive solutions. `IsPrimitiveMod M x` is $\gcd(x_0, \dots, x_{n-1}, M) = 1$; for $M = 0$ it says
  that $\vec x$ is primitive. A non-trivial integral zero can be made primitive by dividing by the greatest common
  divisor (`exists_primitive_zero`); $x^2 + y^2 \equiv 0 \pmod 9$ has a non-trivial solution but no primitive one
  (`sq_add_sq_mod_nine`).
* The integral form of the Hasse principle announced on p. 3 (Theorem 1.1 of Chapter 6): $Q(\vec x) = 0$ has a
  non-trivial integral solution if and only if it has a non-trivial real solution and a primitive solution modulo
  every $M \ge 1$ (`exists_int_zero_iff`). The proof reduces to the library's Hasse–Minkowski theorem
  (`QuadFormsKB.hasseMinkowski`): primitive solutions modulo all $p^e$ give a non-trivial zero in $\mathbb Z_p^n$ by
  compactness. Cassels states it for integral forms without assuming regularity; a singular form always has a
  non-trivial rational zero (a vector in the kernel of its matrix), so no hypothesis is needed.

* The second example on p. 3 ("has a real solution and is soluble as a congruence to every modulus, but, rather
  less trivially, there are no integral solutions (cf. Chapter 13, Section 3)"): the equation, read from the page
  image, is $x^2 - 82y^2 = 2$ (`exists_real_sq_sub_82_sq`, `exists_int_modEq_sq_sub_82_sq`,
  `not_exists_int_sq_sub_82_sq`; the last by descent with the unit $163 + 18\sqrt{82}$ of norm $1$).
* Not an item of Cassels: an earlier reconstruction read this example as the negative Pell equation
  $x^2 - 34y^2 = -1$ (`exists_real_sq_sub_34_sq`, `exists_int_modEq_sq_sub_34_sq`, `not_exists_int_sq_sub_34_sq`);
  the theorems are true and kept as a worked example, without a source tag.
-/
import QuadFormsKB.Literature.Cassels.Ch1Sec2
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Siegel.UnimodularPadic
import QuadFormsKB.Binary.GenusLocal

open Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels

/-! ### From $p$-adic solutions to congruences -/

/-- Evaluating an integer polynomial commutes with ring homomorphisms. -/
theorem aeval_ringHom_apply {n : ℕ} {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (x : Fin n → A) (F : MvPolynomial (Fin n) ℤ) :
    φ (MvPolynomial.aeval x F) = MvPolynomial.aeval (fun i => φ (x i)) F :=
  MvPolynomial.comp_aeval_apply (f := x) φ.toIntAlgHom F

/-- **Solutions in every $\mathbb Z_p$ give solutions modulo every $M \ge 1$**: if an integer polynomial $F$ in $n$
variables has a zero in $\mathbb Z_p^n$ for every prime $p$, then $F(\vec x) \equiv 0 \pmod M$ is soluble in integers
for every $M \ge 1$ (reduce modulo $p^e$, `PadicInt.toZModPow`, and glue by the Chinese remainder theorem). -/
theorem exists_zmod_root_of_padic {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (h : ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin n → ℤ_[p], MvPolynomial.aeval x F = 0)
    (M : ℕ) (hM : M ≠ 0) : ∃ x : Fin n → ℤ, (M : ℤ) ∣ MvPolynomial.eval x F := by
  have key : ∀ M : ℕ, M ≠ 0 → ∃ x : Fin n → ZMod M, MvPolynomial.aeval x F = 0 := by
    intro M
    induction M using Nat.recOnPosPrimePosCoprime with
    | zero => intro h0; exact absurd rfl h0
    | one =>
      intro _
      exact ⟨fun _ => 0, Subsingleton.elim _ _⟩
    | prime_pow p e hp he =>
      intro _
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨x, hx⟩ := h p
      refine ⟨fun i => PadicInt.toZModPow e (x i), ?_⟩
      rw [← aeval_ringHom_apply, hx, map_zero]
    | coprime a b ha hb hab iha ihb =>
      intro _
      obtain ⟨x1, h1⟩ := iha (by omega)
      obtain ⟨x2, h2⟩ := ihb (by omega)
      let e := ZMod.chineseRemainder hab
      refine ⟨fun i => e.symm (x1 i, x2 i), ?_⟩
      apply e.injective
      rw [map_zero]
      have h3 : e (MvPolynomial.aeval (fun i => e.symm (x1 i, x2 i)) F)
          = MvPolynomial.aeval (fun i => (x1 i, x2 i)) F := by
        have := aeval_ringHom_apply (e : ZMod (a * b) →+* ZMod a × ZMod b)
          (fun i => e.symm (x1 i, x2 i)) F
        simp only [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at this
        exact this
      rw [h3]
      have hf := aeval_ringHom_apply (RingHom.fst (ZMod a) (ZMod b)) (fun i => (x1 i, x2 i)) F
      have hs := aeval_ringHom_apply (RingHom.snd (ZMod a) (ZMod b)) (fun i => (x1 i, x2 i)) F
      refine Prod.ext ?_ ?_
      · exact hf.trans h1
      · exact hs.trans h2
  obtain ⟨x, hx⟩ := key M hM
  have : NeZero M := ⟨hM⟩
  refine ⟨fun i => ((x i).val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h4 := aeval_ringHom_apply (Int.castRingHom (ZMod M)) (fun i => ((x i).val : ℤ)) F
  have h5 : MvPolynomial.eval (fun i => ((x i).val : ℤ)) F
      = MvPolynomial.aeval (fun i => ((x i).val : ℤ)) F := rfl
  rw [h5]
  have h6 : (fun i => (Int.castRingHom (ZMod M)) ((x i).val : ℤ)) = x := by
    funext i; simp
  rw [h6, hx] at h4
  exact h4

/-! ### The example $x^2 + 82y^2 = 2$ (1.10) -/

/-- **(1.10) has no integral solution** (Cassels, Ch. 1, §1, p. 3): $x^2 + 82y^2 \ne 2$ for $x, y \in \mathbb Z$. -/
@[kb "cassels1978" "Ch. 1, §1, (1.10), p. 3 (no integral representation)"]
theorem not_exists_int_eq_two : ¬ ∃ x y : ℤ, x ^ 2 + 82 * y ^ 2 = 2 := by
  rintro ⟨x, y, h⟩
  by_cases hy : y = 0
  · subst hy
    have h1 : x ≤ 1 := by nlinarith
    have h2 : -1 ≤ x := by nlinarith
    interval_cases x <;> omega
  · have : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg x]

/-- **(1.10) has a real solution** (Cassels, Ch. 1, §1, p. 3): $(\sqrt 2)^2 + 82\cdot 0^2 = 2$. -/
@[kb "cassels1978" "Ch. 1, §1, (1.10), p. 3 (real representation)"]
theorem exists_real_eq_two : ∃ x y : ℝ, x ^ 2 + 82 * y ^ 2 = 2 :=
  ⟨Real.sqrt 2, 0, by rw [Real.sq_sqrt (by norm_num)]; ring⟩

/-- **The congruence $x^2 + 82y^2 \equiv 2 \pmod M$ is soluble for every $M \ge 1$** (Cassels, Ch. 1, §1, p. 3,
"it can be shown"). Proof: a solution in every $\mathbb Z_p$ — $(0, 1/\sqrt{41})$ for $p = 2$ ($41 \equiv 1 \bmod 8$),
$(\sqrt 2, 0)$ for $p = 41$ ($2 \equiv 17^2 \bmod 41$), and a solution modulo $p$ lifted by Hensel's lemma for the other
$p$ — and `exists_zmod_root_of_padic`. -/
@[kb "cassels1978" "Ch. 1, §1, p. 3 (x² + 82y² ≡ 2 mod M is soluble for every M)"]
theorem exists_int_modEq_two (M : ℕ) (hM : M ≠ 0) : ∃ x y : ℤ, (M : ℤ) ∣ x ^ 2 + 82 * y ^ 2 - 2 := by
  have key : ∀ (p : ℕ) [Fact p.Prime], ∃ a b : ℤ_[p], a ^ 2 + 82 * b ^ 2 = 2 := by
    intro p _
    have hp := (Fact.out : p.Prime)
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨z, hz⟩ := QuadFormsKB.Binary.exists_sq_padic_two (c := 41) (by decide)
      push_cast at hz
      have h41 : IsUnit (41 : ℤ_[2]) := by
        apply Siegel.Kneser.isUnit_of_toZMod_ne_zero
        rw [map_ofNat]; decide +revert
      have hu : IsUnit z := (isUnit_pow_iff two_ne_zero).mp (hz ▸ h41)
      obtain ⟨w, hw⟩ := hu.exists_right_inv
      exact ⟨0, w, by linear_combination (-2 * w ^ 2) * hz + (2 * (z * w + 1)) * hw⟩
    by_cases hp41 : p = 41
    · subst hp41
      obtain ⟨z, hz⟩ := Siegel.Kneser.exists_sq_eq_of_toZMod (p := 41) (by norm_num) (2 : ℤ_[41])
        (s := 17) (by decide +revert) (by rw [map_ofNat]; decide +revert)
      exact ⟨z, 0, by linear_combination hz⟩
    have h82 : (82 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((82 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      have : p ∣ 2 * 41 := h'
      rcases (Nat.Prime.dvd_mul hp).mp this with h2 | h2
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      · exact hp41 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h2)
    have h2' : (2 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
    have hodd : Fintype.card (ZMod p) % 2 = 1 := by
      rw [ZMod.card]
      exact Nat.odd_iff.mp (hp.eq_two_or_odd.resolve_left hp2 |> fun h => Nat.odd_iff.mpr h)
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
      (f := (Polynomial.X ^ 2 : Polynomial (ZMod p)))
      (g := Polynomial.C (82 : ZMod p) * Polynomial.X ^ 2 - Polynomial.C 2)
      (by rw [Polynomial.degree_X_pow]; rfl)
      (by
        rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;>
        rw [Polynomial.degree_C_mul_X_pow _ h82] <;> simp [Polynomial.degree_C h2'])
      hodd
    simp at hab
    have hab' : a ^ 2 + 82 * b ^ 2 = 2 := by linear_combination hab
    have h82u : IsUnit (82 : ℤ_[p]) := by
      apply Siegel.Kneser.isUnit_of_toZMod_ne_zero
      rw [map_ofNat]; exact h82
    by_cases ha : a = 0
    · subst ha
      have hb : b ≠ 0 := by
        rintro rfl
        apply h2'
        linear_combination -hab'
      obtain ⟨w, hw⟩ := h82u.exists_left_inv
      have hw' : PadicInt.toZMod w * 82 = 1 := by
        have := congrArg PadicInt.toZMod hw
        rw [map_mul, map_ofNat, map_one] at this
        exact this
      obtain ⟨z, hz⟩ := Siegel.Kneser.exists_sq_eq_of_toZMod hp2 (2 * w) (s := b) hb (by
        rw [map_mul, map_ofNat]
        linear_combination (-(PadicInt.toZMod w)) * hab' + b ^ 2 * hw')
      exact ⟨0, z, by linear_combination 82 * hz + 2 * hw⟩
    · set bt : ℤ_[p] := (b.val : ℤ_[p])
      have hbt : PadicInt.toZMod bt = b := by simp [bt]
      obtain ⟨z, hz⟩ := Siegel.Kneser.exists_sq_eq_of_toZMod hp2 (2 - 82 * bt ^ 2) (s := a) ha (by
        rw [map_sub, map_mul, map_pow, hbt, map_ofNat, map_ofNat]
        linear_combination -hab')
      exact ⟨z, bt, by linear_combination hz⟩
  have hF := exists_zmod_root_of_padic
    (MvPolynomial.X 0 ^ 2 + 82 * MvPolynomial.X 1 ^ 2 - 2 : MvPolynomial (Fin 2) ℤ)
    (fun p _ => by
      obtain ⟨a, b, hab⟩ := key p
      exact ⟨![a, b], by simp; linear_combination hab⟩) M hM
  obtain ⟨x, hx⟩ := hF
  exact ⟨x 0, x 1, by simpa using hx⟩

/-! ### Primitive solutions (1.12)–(1.14) -/

/-- **Primitive modulo $M$** (Cassels, Ch. 1, §1, (1.14), p. 3): $\gcd(x_0, \dots, x_{n-1}, M) = 1$, i.e. every common
divisor of $x_0, \dots, x_{n-1}$ and $M$ is a unit. For $M = 0$ this says that $\vec x$ is primitive,
$\gcd(x_0, \dots, x_{n-1}) = 1$ (Cassels (1.12)). -/
@[kb "cassels1978" "Ch. 1, §1, (1.12) and (1.14), p. 3"]
def IsPrimitiveMod {n : ℕ} (M : ℤ) (x : Fin n → ℤ) : Prop :=
  ∀ d : ℤ, d ∣ M → (∀ i, d ∣ x i) → IsUnit d

/-- A primitive vector is primitive modulo every $M$. -/
theorem IsPrimitiveMod.of_zero {n : ℕ} {x : Fin n → ℤ} (h : IsPrimitiveMod 0 x) (M : ℤ) : IsPrimitiveMod M x :=
  fun d _ hd => h d (dvd_zero d) hd

/-- **A non-trivial integral zero can be made primitive** (Cassels, Ch. 1, §1, (1.12), p. 3): if $Q(\vec x) = 0$ with
$\vec x \in \mathbb Z^n$, $\vec x \ne 0$, dividing by $\gcd(x_0, \dots, x_{n-1})$ gives a primitive zero. -/
@[kb "cassels1978" "Ch. 1, §1, (1.12), p. 3"]
theorem exists_primitive_zero {n : ℕ} (Q : QuadForm ℤ n) {x : Fin n → ℤ} (hx : x ≠ 0) (hQ : Q.eval x = 0) :
    ∃ y : Fin n → ℤ, IsPrimitiveMod 0 y ∧ Q.eval y = 0 := by
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (funext hcon)
  obtain ⟨y, hy, hg⟩ := Finset.extract_gcd x (⟨i0, Finset.mem_univ i0⟩ : (Finset.univ : Finset (Fin n)).Nonempty)
  set G := Finset.univ.gcd x with hG
  have hG0 : G ≠ 0 := by
    intro h0
    have := (Finset.gcd_eq_zero_iff.mp h0) i0 (Finset.mem_univ _)
    exact hi0 this
  have hxy : x = G • y := by
    funext i; simpa using hy i (Finset.mem_univ i)
  refine ⟨y, ?_, ?_⟩
  · intro d _ hd
    have : d ∣ Finset.univ.gcd y := Finset.dvd_gcd (fun i _ => hd i)
    rw [hg] at this
    exact isUnit_of_dvd_one this
  · rw [hxy] at hQ
    have h2 : Q.eval (G • y) = G ^ 2 * Q.eval y := by
      unfold QuadForm.eval
      rw [QuadForm.evalIn_eq_dotProduct, QuadForm.evalIn_eq_dotProduct, Matrix.mulVec_smul, dotProduct_smul,
        smul_dotProduct, smul_eq_mul, smul_eq_mul]
      ring
    rw [h2] at hQ
    exact (mul_eq_zero.mp hQ).resolve_left (pow_ne_zero 2 hG0)

/-- **Cassels' example** (Ch. 1, §1, p. 3): $x^2 + y^2 \equiv 0 \pmod 9$ has a non-trivial solution ($(3, 0)$, not
$\equiv (0, 0) \bmod 9$) but no primitive solution. -/
@[kb "cassels1978" "Ch. 1, §1, p. 3 (x² + y² ≡ 0 mod 9)"]
theorem sq_add_sq_mod_nine :
    (∃ x y : ℤ, ¬ ((9 : ℤ) ∣ x ∧ (9 : ℤ) ∣ y) ∧ (9 : ℤ) ∣ x ^ 2 + y ^ 2) ∧
      ¬ ∃ x : Fin 2 → ℤ, IsPrimitiveMod 9 x ∧ (9 : ℤ) ∣ x 0 ^ 2 + x 1 ^ 2 := by
  refine ⟨⟨3, 0, by decide, by decide⟩, ?_⟩
  rintro ⟨x, hp, hd⟩
  have h3 : (3 : ℤ) ∣ x 0 ^ 2 + x 1 ^ 2 := dvd_trans (by norm_num) hd
  have hz : ((x 0 ^ 2 + x 1 ^ 2 : ℤ) : ZMod 3) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h3
  push_cast at hz
  have hcase : ∀ a b : ZMod 3, a ^ 2 + b ^ 2 = 0 → a = 0 ∧ b = 0 := by decide
  obtain ⟨h0, h1⟩ := hcase _ _ hz
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0 h1
  have := hp 3 (by norm_num) (by
    intro i
    fin_cases i
    · exact_mod_cast h0
    · exact_mod_cast h1)
  exact absurd this (by decide)

/-! ### The integral Hasse principle (Theorem 1.1 of Chapter 6, announced on p. 3) -/

/-- **Primitive solutions modulo every power of $p$ give a non-trivial $p$-adic zero** (compactness of
$\mathbb Z_p^n$). -/
theorem exists_padic_zero_of_primitive {n : ℕ} (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime]
    (h : ∀ e : ℕ, ∃ x : Fin n → ℤ, IsPrimitiveMod ((p : ℤ) ^ (e + 1)) x ∧ (p : ℤ) ^ (e + 1) ∣ Q.eval x) :
    ∃ x : Fin n → ℤ_[p], x ≠ 0 ∧ (Q.map (Int.castRingHom ℤ_[p])).eval x = 0 := by
  have hp : Nat.Prime p := Fact.out
  set f : (Fin n → ℤ_[p]) → ℤ_[p] := fun x => (Q.map (Int.castRingHom ℤ_[p])).eval x with hf
  have fcont : Continuous f := by
    simp only [hf, QuadForm.eval, QuadForm.evalIn]
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    split_ifs
    · fun_prop
    · exact continuous_const
  set t : ℕ → Set (Fin n → ℤ_[p]) := fun e =>
    {x | (∃ i, ‖x i‖ = 1) ∧ ‖f x‖ ≤ (p : ℝ) ^ (-((e + 1 : ℕ) : ℤ))} with ht
  have hclosedA : IsClosed {x : Fin n → ℤ_[p] | ∃ i, ‖x i‖ = 1} := by
    simp only [Set.setOf_exists]
    exact isClosed_iUnion_of_finite fun i => isClosed_eq (by fun_prop) continuous_const
  have hcl : ∀ e, IsClosed (t e) := fun e =>
    hclosedA.inter (isClosed_le (continuous_norm.comp fcont) continuous_const)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hdec : ∀ e, t (e + 1) ⊆ t e := by
    intro e x hx
    refine ⟨hx.1, hx.2.trans ?_⟩
    apply zpow_le_zpow_right₀ hp1
    push_cast
    omega
  have hne : ∀ e, (t e).Nonempty := by
    intro e
    obtain ⟨x, hprim, hdvd⟩ := h e
    have hi : ∃ i, ¬ (p : ℤ) ∣ x i := by
      by_contra hcon
      push_neg at hcon
      have := hprim p (dvd_pow_self _ (Nat.succ_ne_zero e)) hcon
      rw [Int.isUnit_iff] at this
      rcases this with h1 | h1
      · have := hp.one_lt; omega
      · omega
    obtain ⟨i, hi⟩ := hi
    refine ⟨fun i => ((x i : ℤ) : ℤ_[p]), ⟨i, ?_⟩, ?_⟩
    · have h1 : ‖((x i : ℤ) : ℤ_[p])‖ < 1 ↔ _ := PadicInt.norm_int_lt_one_iff_dvd (p := p) (x i)
      have h2 := PadicInt.norm_le_one ((x i : ℤ) : ℤ_[p])
      rcases h2.lt_or_eq with h2 | h2
      · exact absurd (h1.mp h2) hi
      · exact h2
    · have := eval_map_apply (Int.castRingHom ℤ_[p]) Q x
      show ‖f (fun i => ((x i : ℤ) : ℤ_[p]))‖ ≤ _
      rw [show f (fun i => ((x i : ℤ) : ℤ_[p])) = ((Q.eval x : ℤ) : ℤ_[p]) from this]
      rw [PadicInt.norm_int_le_pow_iff_dvd]
      simpa using hdvd
  have hcpt : IsCompact (t 0) := (hcl 0).isCompact
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hdec hne hcpt hcl
  rw [Set.mem_iInter] at hx
  obtain ⟨i, hi⟩ := (hx 0).1
  refine ⟨x, ?_, ?_⟩
  · intro h0
    rw [h0] at hi
    simp at hi
  · change f x = 0
    by_contra hne0
    have hpos : 0 < ‖f x‖ := norm_pos_iff.mpr hne0
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos
      (show ((p : ℝ)⁻¹) < 1 from inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt))
    have := (hx m).2
    have e2 : (p : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) ≤ ((p : ℝ)⁻¹) ^ m := by
      rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
      apply pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hp1)
      omega
    linarith

/-- **The integral Hasse principle** (Cassels, Ch. 1, §1, p. 3, announcing Theorem 1.1 of Chapter 6). For an
integral quadratic form $Q$ in $n$ variables, $Q(\vec x) = 0$ (1.11) has a non-trivial integral solution if and only
if it has a non-trivial real solution and, for every $M \ge 1$, the congruence $Q(\vec x) \equiv 0 \pmod M$ (1.13)
has a primitive solution (1.14). No regularity is assumed (as in Cassels' statement): a singular form has a
non-trivial rational zero. -/
@[kb "cassels1978" "Ch. 1, §1, p. 3 (Theorem 1.1 of Chapter 6, announced)"]
theorem exists_int_zero_iff {n : ℕ} (Q : QuadForm ℤ n) :
    (∃ x : Fin n → ℤ, x ≠ 0 ∧ Q.eval x = 0) ↔
      (∃ x : Fin n → ℝ, x ≠ 0 ∧ (Q.map (Int.castRingHom ℝ)).eval x = 0) ∧
        ∀ M : ℕ, M ≠ 0 → ∃ x : Fin n → ℤ, IsPrimitiveMod (M : ℤ) x ∧ (M : ℤ) ∣ Q.eval x := by
  constructor
  · rintro ⟨x, hx, hQ⟩
    refine ⟨⟨fun i => (x i : ℝ), ?_, ?_⟩, fun M _ => ?_⟩
    · intro h
      apply hx
      funext i
      have := congrFun h i
      simpa using this
    · have := eval_map_apply (Int.castRingHom ℝ) Q x
      simpa [hQ] using this
    · obtain ⟨y, hy, hyq⟩ := exists_primitive_zero Q hx hQ
      exact ⟨y, hy.of_zero _, by rw [hyq]; exact dvd_zero _⟩
  · rintro ⟨⟨r, hr, hrq⟩, hM⟩
    set R : RatQF n := Q.map (Int.castRingHom ℚ) with hR
    have key : ∃ v : Fin n → ℚ, v ≠ 0 ∧ R.eval v = 0 := by
      by_cases hnd : R.Nondegenerate
      · have H := (QuadFormsKB.hasseMinkowski R hnd).mpr (by
          intro v
          cases v with
          | infinite =>
            refine ⟨r, hr, ?_⟩
            rw [← hrq]
            simp [QuadForm.evalIn, QuadForm.map, hR]
          | finite p =>
            haveI : Fact p.1.Prime := ⟨p.2⟩
            show R.IsotropicIn ℚ_[p.1]
            obtain ⟨z, hz, hz0⟩ := exists_padic_zero_of_primitive Q p.1 (fun e => by
              simpa using hM (p.1 ^ (e + 1)) (pow_ne_zero _ p.2.ne_zero))
            refine ⟨fun i => ((z i : ℤ_[p.1]) : ℚ_[p.1]), ?_, ?_⟩
            · intro h0
              apply hz
              funext i
              have := congrFun h0 i
              exact Subtype.ext (by simpa using this)
            · have := congrArg (PadicInt.Coe.ringHom (p := p.1)) hz0
              simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.map, hR, map_sum, apply_ite,
                map_mul, map_zero] at this ⊢
              simpa using this)
        exact H
      · have hdet : R.hessian.det = 0 := by
          unfold QuadForm.Nondegenerate at hnd
          exact not_not.mp hnd
        obtain ⟨v, hv, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
        refine ⟨v, hv, ?_⟩
        have := two_mul_eval R v
        rw [hmv, dotProduct_zero] at this
        simpa using this
    obtain ⟨v, hv, hv0⟩ := key
    set D : ℕ := ∏ i, (v i).den with hD
    have hDpos : 0 < D := Finset.prod_pos fun i _ => (v i).den_pos
    set y : Fin n → ℤ := fun i => (v i).num * ((D / (v i).den : ℕ) : ℤ) with hy
    have hyv : ∀ i, (y i : ℚ) = (D : ℚ) * v i := by
      intro i
      obtain ⟨k, hk⟩ : (v i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      have hk' : D / (v i).den = k := by
        rw [hk]; exact Nat.mul_div_cancel_left _ (v i).den_pos
      simp only [hy, hk']
      push_cast
      have h1 : ((v i).den : ℚ) * v i = (v i).num := Rat.den_mul_eq_num _
      rw [hk]
      push_cast
      calc ((v i).num : ℚ) * k = ((v i).den * v i) * k := by rw [h1]
        _ = _ := by ring
    have hscale : ∀ (c : ℚ) (w : Fin n → ℚ), R.eval (c • w) = c ^ 2 * R.eval w := by
      intro c w
      rw [eval_eq_dotProduct, eval_eq_dotProduct, mulVec_smul, dotProduct_smul, smul_dotProduct]
      simp only [smul_eq_mul]
      ring
    have hyeq : (fun i => (y i : ℚ)) = (D : ℚ) • v := by
      funext i; simp [hyv]
    refine ⟨y, ?_, ?_⟩
    · intro h0
      apply hv
      funext i
      have := congrFun h0 i
      have h2 : (y i : ℚ) = 0 := by simp [this]
      rw [hyv] at h2
      have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
      simpa [hD0] using h2
    · have h1 := eval_map_apply (Int.castRingHom ℚ) Q y
      have h2 : R.eval (fun i => (Int.castRingHom ℚ) (y i)) = 0 := by
        have : (fun i => (Int.castRingHom ℚ) (y i)) = (D : ℚ) • v := by
          rw [← hyeq]; rfl
        rw [this, hscale, hv0, mul_zero]
      rw [← hR] at h1
      rw [h1] at h2
      simpa using h2

/-! ### The second example of p. 3: $x^2 - 82y^2 = 2$ -/

/-- **$x^2 - 82y^2 = 2$ has a real solution** (Cassels, Ch. 1, §1, p. 3, second example; the equation was read from the
page image): $x = \sqrt 2$, $y = 0$. -/
@[kb "cassels1978" "Ch. 1, §1, p. 3 (x² − 82y² = 2: real solution)"]
theorem exists_real_sq_sub_82_sq : ∃ x y : ℝ, x ^ 2 - 82 * y ^ 2 = 2 :=
  ⟨Real.sqrt 2, 0, by rw [Real.sq_sqrt (by norm_num)]; ring⟩

/-- **$x^2 - 82y^2 \equiv 2 \pmod M$ is soluble for every $M \ge 1$** (Cassels, Ch. 1, §1, p. 3, second example; the
equation was read from the page image). Proof: a solution in every $\mathbb Z_p$ — $(2z, 3)$ with $z^2 = 185 \equiv 1
\bmod 8$ for $p = 2$, $(\sqrt 2, 0)$ for $p = 41$ ($2 \equiv 17^2 \bmod 41$), and a solution modulo $p$ lifted by
Hensel's lemma for the other $p$ — and `exists_zmod_root_of_padic`. -/
@[kb "cassels1978" "Ch. 1, §1, p. 3 (x² − 82y² ≡ 2 mod M is soluble for every M)"]
theorem exists_int_modEq_sq_sub_82_sq (M : ℕ) (hM : M ≠ 0) :
    ∃ x y : ℤ, (M : ℤ) ∣ x ^ 2 - 82 * y ^ 2 - 2 := by
  have key : ∀ (p : ℕ) [Fact p.Prime], ∃ a b : ℤ_[p], a ^ 2 - 82 * b ^ 2 = 2 := by
    intro p _
    have hp := (Fact.out : p.Prime)
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨z, hz⟩ := QuadFormsKB.Binary.exists_sq_padic_two (c := 185) (by decide)
      push_cast at hz
      exact ⟨2 * z, 3, by linear_combination 4 * hz⟩
    by_cases hp41 : p = 41
    · subst hp41
      obtain ⟨z, hz⟩ := Siegel.Kneser.exists_sq_eq_of_toZMod (p := 41) (by norm_num) (2 : ℤ_[41])
        (s := 17) (by decide +revert) (by rw [map_ofNat]; decide +revert)
      exact ⟨z, 0, by linear_combination hz⟩
    have h82 : (82 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((82 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      have : p ∣ 2 * 41 := h'
      rcases (Nat.Prime.dvd_mul hp).mp this with h2 | h2
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      · exact hp41 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h2)
    have h2' : (2 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
    have hodd : Fintype.card (ZMod p) % 2 = 1 := by
      rw [ZMod.card]
      exact Nat.odd_iff.mp (hp.eq_two_or_odd.resolve_left hp2 |> fun h => Nat.odd_iff.mpr h)
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
      (f := (Polynomial.X ^ 2 : Polynomial (ZMod p)))
      (g := Polynomial.C (-82 : ZMod p) * Polynomial.X ^ 2 - Polynomial.C 2)
      (by rw [Polynomial.degree_X_pow]; rfl)
      (by
        rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;>
        rw [Polynomial.degree_C_mul_X_pow _ (neg_ne_zero.mpr h82)] <;> simp [Polynomial.degree_C h2'])
      hodd
    simp at hab
    have hab' : a ^ 2 - 82 * b ^ 2 = 2 := by linear_combination hab
    have h82u : IsUnit (82 : ℤ_[p]) := by
      apply Siegel.Kneser.isUnit_of_toZMod_ne_zero
      rw [map_ofNat]; exact h82
    by_cases ha : a = 0
    · subst ha
      have hb : b ≠ 0 := by
        rintro rfl
        apply h2'
        linear_combination -hab'
      obtain ⟨w, hw⟩ := h82u.exists_left_inv
      have hw' : PadicInt.toZMod w * 82 = 1 := by
        have := congrArg PadicInt.toZMod hw
        rw [map_mul, map_ofNat, map_one] at this
        exact this
      obtain ⟨z, hz⟩ := Siegel.Kneser.exists_sq_eq_of_toZMod hp2 (-(2 * w)) (s := b) hb (by
        rw [map_neg, map_mul, map_ofNat]
        linear_combination (PadicInt.toZMod w) * hab' + b ^ 2 * hw')
      exact ⟨0, z, by linear_combination (-82) * hz + 2 * hw⟩
    · set bt : ℤ_[p] := (b.val : ℤ_[p])
      have hbt : PadicInt.toZMod bt = b := by simp [bt]
      obtain ⟨z, hz⟩ := Siegel.Kneser.exists_sq_eq_of_toZMod hp2 (2 + 82 * bt ^ 2) (s := a) ha (by
        rw [map_add, map_mul, map_pow, hbt, map_ofNat, map_ofNat]
        linear_combination -hab')
      exact ⟨z, bt, by linear_combination hz⟩
  have hF := exists_zmod_root_of_padic
    (MvPolynomial.X 0 ^ 2 - 82 * MvPolynomial.X 1 ^ 2 - 2 : MvPolynomial (Fin 2) ℤ)
    (fun p _ => by
      obtain ⟨a, b, hab⟩ := key p
      exact ⟨![a, b], by simp; linear_combination hab⟩) M hM
  obtain ⟨x, hx⟩ := hF
  exact ⟨x 0, x 1, by simpa using hx⟩

/-- Descent for $x^2 - 82y^2 = 2$: there is no solution with $x, y \ge 0$ and $y < n$. -/
theorem no_nonneg_sq_sub_82_sq_aux (n : ℕ) :
    ∀ x y : ℤ, 0 ≤ x → 0 ≤ y → y < n → x ^ 2 - 82 * y ^ 2 ≠ 2 := by
  induction n with
  | zero => intro x y _ hy hn; push_cast at hn; omega
  | succ n ih =>
    intro x y hx hy hn h
    by_cases hy26 : y < 26
    · have hx' : x < 228 := by nlinarith
      lift x to ℕ using hx
      lift y to ℕ using hy
      have key : ∀ y < 26, ∀ x < 228, x ^ 2 ≠ 82 * y ^ 2 + 2 := by decide +kernel
      exact key y (by exact_mod_cast hy26) x (by exact_mod_cast hx')
        (by exact_mod_cast (by linarith : (x : ℤ) ^ 2 = 82 * (y : ℤ) ^ 2 + 2))
    · push Not at hy26
      have h9 : 9 * y < x := by nlinarith
      have h1 : 18 * x ≤ 163 * y := by nlinarith
      have h2 : 1476 * y ≤ 163 * x := by nlinarith
      refine ih (163 * x - 1476 * y) (163 * y - 18 * x) (by linarith) (by linarith) ?_ (by linear_combination h)
      push_cast at hn
      omega

/-- **$x^2 - 82y^2 = 2$ has no integral solution** (Cassels, Ch. 1, §1, p. 3, second example, "rather less
trivially"; the equation was read from the page image; cf. his Ch. 13, §3). Proof by descent with the unit
$163 + 18\sqrt{82}$ of norm $1$: for a solution with $x, y \ge 0$ and $y \ge 26$, $(163x - 1476y,\ 163y - 18x)$ is a
solution with $0 \le y' < y$; for $y < 26$ a finite check shows $82y^2 + 2$ is not a square. -/
@[kb "cassels1978" "Ch. 1, §1, p. 3 (x² − 82y² = 2 has no integral solution)"]
theorem not_exists_int_sq_sub_82_sq : ¬ ∃ x y : ℤ, x ^ 2 - 82 * y ^ 2 = 2 := by
  rintro ⟨x, y, h⟩
  exact no_nonneg_sq_sub_82_sq_aux ((|y|).toNat + 1) |x| |y| (abs_nonneg x) (abs_nonneg y)
    (by push_cast; rw [Int.toNat_of_nonneg (abs_nonneg y)]; omega) (by rw [sq_abs, sq_abs]; exact h)

/-! ### The negative Pell equation $x^2 - 34y^2 = -1$ (worked example, not an item of Cassels) -/

/-- **The negative Pell equation $x^2 - 34y^2 = -1$ has a real solution**: $x = 0$, $y = 1/\sqrt{34}$.

Not an item of Cassels: an earlier reconstruction of the second example on p. 3 read it as x² − 34y² = −1; the
page image shows x² − 82y² = 2 (see `not_exists_int_sq_sub_82_sq`). Kept as a worked example of the negative Pell
equation. -/
theorem exists_real_sq_sub_34_sq : ∃ x y : ℝ, x ^ 2 - 34 * y ^ 2 = -1 := by
  refine ⟨0, 1 / Real.sqrt 34, ?_⟩
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- $(35, 6)$ is the fundamental solution of $x^2 - 34y^2 = 1$. -/
theorem pell34_fund : Pell.IsFundamental (Pell.Solution₁.mk 35 6 (by norm_num) : Pell.Solution₁ 34) := by
  refine ⟨by simp, by simp, ?_⟩
  intro b hb
  rw [Pell.Solution₁.x_mk]
  by_contra hlt
  push Not at hlt
  have h := b.prop_x
  have hy : b.y ^ 2 ≤ 33 := by nlinarith
  have hb' : b.x ≤ 34 := by omega
  have hy2 : b.y ≤ 5 := by nlinarith
  have hy3 : -5 ≤ b.y := by nlinarith
  generalize b.x = X at *
  generalize b.y = Y at *
  interval_cases Y <;> (have : X ^ 2 ≤ 34 ^ 2 := by nlinarith) <;>
    (have : X ≤ 34 := by nlinarith) <;> interval_cases X <;> omega

/-- The step of the descent: a solution of norm $-1$ divided by a power of the fundamental unit. -/
theorem pell34_aux (x y : ℤ) (h : x ^ 2 - 34 * y ^ 2 = -1) (s u : Pell.Solution₁ 34)
    (hsx : s.x = x ^ 2 + 34 * y ^ 2) (hsy : s.y = 2 * x * y) :
    ∃ a b : ℤ, a ^ 2 - 34 * b ^ 2 = -1 ∧ (s * u⁻¹ * u⁻¹).x = a ^ 2 + 34 * b ^ 2 := by
  refine ⟨x * u.x - 34 * y * u.y, y * u.x - x * u.y, ?_, ?_⟩
  · linear_combination (u.x ^ 2 - 34 * u.y ^ 2) * h - u.prop
  · simp only [Pell.Solution₁.x_mul, Pell.Solution₁.y_mul, Pell.Solution₁.x_inv, Pell.Solution₁.y_inv,
      hsx, hsy]
    ring

/-- **$x^2 - 34y^2 = -1$ has no integral solution.** Proof: otherwise $(x + y\sqrt{34})^2$ is a power $\eta^m$ of the fundamental solution
$\eta = 35 + 6\sqrt{34}$ of Pell's equation; dividing by $\eta^{\lfloor m/2 \rfloor}$ gives an element of norm $-1$
whose square is $1$ or $\eta$, which is impossible.

Not an item of Cassels: an earlier reconstruction of the second example on p. 3 read it as x² − 34y² = −1; the
page image shows x² − 82y² = 2 (see `not_exists_int_sq_sub_82_sq`). Kept as a worked example of the negative Pell
equation. -/
theorem not_exists_int_sq_sub_34_sq : ¬ ∃ x y : ℤ, x ^ 2 - 34 * y ^ 2 = -1 := by
  rintro ⟨x0, y0, h0⟩
  set x := |x0| with hx
  set y := |y0| with hy
  have h : x ^ 2 - 34 * y ^ 2 = -1 := by rw [hx, hy, sq_abs, sq_abs]; exact h0
  have hx0 : 0 < x := by
    rcases (abs_nonneg x0).lt_or_eq with h1 | h1
    · exact h1
    · exfalso; have h2 : x = 0 := h1.symm; rw [h2] at h; have h3 : (0:ℤ) ^ 2 = 0 := by norm_num
      rw [h3] at h; generalize y ^ 2 = Y at h; omega
  have hy0 : 0 ≤ y := abs_nonneg y0
  let s : Pell.Solution₁ 34 := Pell.Solution₁.mk (x ^ 2 + 34 * y ^ 2) (2 * x * y) (by
    linear_combination (x ^ 2 - 34 * y ^ 2 - 1) * h)
  have hsx : s.x = x ^ 2 + 34 * y ^ 2 := Pell.Solution₁.x_mk _ _ _
  have hsy : s.y = 2 * x * y := Pell.Solution₁.y_mk _ _ _
  have hfund := pell34_fund
  obtain ⟨n, hn⟩ := hfund.eq_pow_of_nonneg (a := s) (by rw [hsx]; positivity) (by rw [hsy]; positivity)
  set η : Pell.Solution₁ 34 := Pell.Solution₁.mk 35 6 (by norm_num) with hη
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · have h1 : s * (η ^ k)⁻¹ * (η ^ k)⁻¹ = 1 := by
      rw [hn, hk, two_mul, pow_add]; simp
    obtain ⟨a, b, hab, hxx⟩ := pell34_aux x y h s (η ^ k) hsx hsy
    rw [h1, Pell.Solution₁.x_one] at hxx
    generalize a ^ 2 = A at *
    generalize b ^ 2 = B at *
    omega
  · have h1 : s * (η ^ k)⁻¹ * (η ^ k)⁻¹ = η := by
      rw [hn, hk, pow_succ, two_mul, pow_add]; group
    obtain ⟨a, b, hab, hxx⟩ := pell34_aux x y h s (η ^ k) hsx hsy
    rw [h1, hη, Pell.Solution₁.x_mk] at hxx
    generalize a ^ 2 = A at *
    generalize b ^ 2 = B at *
    omega

/-- **$x^2 - 34y^2 \equiv -1 \pmod M$ is soluble for every $M \ge 1$**: solutions in every $\mathbb Z_p$ ($p = 2$:
$y = 1$, $x^2 = 33$; $p = 17$: $x^2 = -1$; other $p$: a solution modulo $p$ and Hensel's lemma) and
`exists_zmod_root_of_padic`.

Not an item of Cassels: an earlier reconstruction of the second example on p. 3 read it as x² − 34y² = −1; the
page image shows x² − 82y² = 2 (see `not_exists_int_sq_sub_82_sq`). Kept as a worked example of the negative Pell
equation. -/
theorem exists_int_modEq_sq_sub_34_sq (M : ℕ) (hM : M ≠ 0) :
    ∃ x y : ℤ, (M : ℤ) ∣ x ^ 2 - 34 * y ^ 2 + 1 := by
  have key : ∀ (p : ℕ) [Fact p.Prime], ∃ a b : ℤ_[p], a ^ 2 - 34 * b ^ 2 = -1 := by
    intro p _
    have hp := (Fact.out : p.Prime)
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨z, hz⟩ := QuadFormsKB.Binary.exists_sq_padic_two (c := 33) (by decide)
      push_cast at hz
      exact ⟨z, 1, by linear_combination hz⟩
    by_cases hp17 : p = 17
    · subst hp17
      obtain ⟨z, hz⟩ := Siegel.Kneser.exists_sq_eq_of_toZMod (p := 17) (by norm_num) (-1 : ℤ_[17])
        (s := 4) (by decide +revert) (by rw [map_neg, map_one]; decide +revert)
      exact ⟨z, 0, by linear_combination hz⟩
    have h34 : (34 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((34 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      have : p ∣ 2 * 17 := h'
      rcases (Nat.Prime.dvd_mul hp).mp this with h2 | h2
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      · exact hp17 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h2)
    have h1' : (1 : ZMod p) ≠ 0 := one_ne_zero
    have hodd : Fintype.card (ZMod p) % 2 = 1 := by
      rw [ZMod.card]
      exact Nat.odd_iff.mp (hp.eq_two_or_odd.resolve_left hp2 |> fun h => Nat.odd_iff.mpr h)
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
      (f := (Polynomial.X ^ 2 : Polynomial (ZMod p)))
      (g := Polynomial.C (-34 : ZMod p) * Polynomial.X ^ 2 + Polynomial.C 1)
      (by rw [Polynomial.degree_X_pow]; rfl)
      (by
        rw [Polynomial.degree_add_eq_left_of_degree_lt] <;>
        rw [Polynomial.degree_C_mul_X_pow _ (neg_ne_zero.mpr h34)] <;> simp [Polynomial.degree_C h1'])
      hodd
    simp at hab
    have hab' : a ^ 2 - 34 * b ^ 2 = -1 := by linear_combination hab
    by_cases ha : a = 0
    · subst ha
      have hb : b ≠ 0 := by
        rintro rfl
        have : (1 : ZMod p) = 0 := by linear_combination hab'
        exact h1' this
      have h34u : IsUnit (34 : ℤ_[p]) := by
        apply Siegel.Kneser.isUnit_of_toZMod_ne_zero
        rw [map_ofNat]; exact h34
      obtain ⟨w, hw⟩ := h34u.exists_left_inv
      have hw' : PadicInt.toZMod w * 34 = 1 := by
        have := congrArg PadicInt.toZMod hw
        rw [map_mul, map_ofNat, map_one] at this
        exact this
      obtain ⟨z, hz⟩ := Siegel.Kneser.exists_sq_eq_of_toZMod hp2 w (s := b) hb (by
        linear_combination (PadicInt.toZMod w) * hab' + b ^ 2 * hw')
      exact ⟨0, z, by linear_combination (-34) * hz - hw⟩
    · set bt : ℤ_[p] := (b.val : ℤ_[p])
      have hbt : PadicInt.toZMod bt = b := by simp [bt]
      obtain ⟨z, hz⟩ := Siegel.Kneser.exists_sq_eq_of_toZMod hp2 (34 * bt ^ 2 - 1) (s := a) ha (by
        rw [map_sub, map_mul, map_pow, hbt, map_ofNat, map_one]
        linear_combination -hab')
      exact ⟨z, bt, by linear_combination hz⟩
  have hF := Cassels.exists_zmod_root_of_padic
    (MvPolynomial.X 0 ^ 2 - 34 * MvPolynomial.X 1 ^ 2 + 1 : MvPolynomial (Fin 2) ℤ)
    (fun p _ => by
      obtain ⟨a, b, hab⟩ := key p
      exact ⟨![a, b], by simp; linear_combination hab⟩) M hM
  obtain ⟨x, hx⟩ := hF
  exact ⟨x 0, x 1, by simpa using hx⟩

end QuadFormsKB.Cassels
