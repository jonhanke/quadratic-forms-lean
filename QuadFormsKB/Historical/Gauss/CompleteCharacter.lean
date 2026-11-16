import QuadFormsKB.Historical.Gauss.CharacteristicNumbers
import QuadFormsKB.Historical.Gauss.SectionSix
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Complete characters and counting the values of $\sqrt{M(a, b, c)}$ (Disquisitiones Arithmeticae, Art. 233 IV, V, VII)

(Art. 233 IV) (Art. 233 V) and (Art. 233 VII).

Write $f(x, y) = a x^2 + 2 b x y + c y^2$ for Gauss's form $(a, b, c)$ and $D = b^2 - ac$ for its determinant.

* Art. 233 IV (`art233_four`): if $M(a, b, c)$ is a quadratic residue of $D$ (`IsResidueForm`) and $M$ is prime to
  $D$, then every odd prime $p \mid D$ has $\left(\frac{f(x,y)}{p}\right) = \left(\frac{M}{p}\right)$ for all values
  $f(x, y)$ prime to $p$; if $4 \mid D$ every odd value is $\equiv M \pmod 4$; if $8 \mid D$ every odd value is
  $\equiv M \pmod 8$. So all particular characters of $(a, b, c)$ are determined by $M$. Gauss's example
  $3(20, 10, 27)$, $D = -440$, value $(150, 9)$, complete character $3, 8; N5; R11$ is checked in
  `art233_four_example`.
* Art. 233 V (`art233_five`), the converse: if $D \ne 0$, $M$ is prime to $D$ and $M$ has all the particular
  characters of $(a, b, c)$ (those for $4$, $8$ only when they divide $D$), then $M(a, b, c)$ is a quadratic residue of
  $D$. Proved from Art. 233 III prime power by prime power and the Chinese remainder theorem
  (`isResidueForm_mul`).
* Art. 233 VII: the number of values of $\sqrt{M(a, b, c)} \pmod m$, counted as pairs $(g, h)$ in
  $\mathbb{Z}/m \times \mathbb{Z}/m$ (`sqrtValues`), is $2$ for $m = p^\kappa$ with $p$ an odd prime
  (`art233_seven_prime_power`) and for $m = 4$ (`art233_seven_four`), $4$ for $m = 2^k$, $k \ge 3$
  (`art233_seven_two_power`), and $1$ for $m = 2$ (`art233_seven_two`), given that one value exists. The values are
  closed under $v \mapsto -v$ (`IsSqrtValue.neg`).

Everything is proved unconditionally.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-- If $M(a, b, c)$ is a quadratic residue of $m$ it is one of every divisor $n$ of $m$. -/
theorem IsResidueForm.of_dvd {M a b c m n : ℤ} (h : IsResidueForm M a b c m) (hd : n ∣ m) :
    IsResidueForm M a b c n := by
  obtain ⟨g, k, h1, h2, h3⟩ := h
  exact ⟨g, k, h1.of_dvd hd, h2.of_dvd hd, h3.of_dvd hd⟩

/-- Being a quadratic residue modulo $m$ is the same as modulo $-m$. -/
theorem isResidueForm_neg_modulus {M a b c m : ℤ} (h : IsResidueForm M a b c m) :
    IsResidueForm M a b c (-m) := by
  obtain ⟨g, k, h1, h2, h3⟩ := h
  exact ⟨g, k, Int.modEq_neg.mpr h1, Int.modEq_neg.mpr h2, Int.modEq_neg.mpr h3⟩

private theorem not_dvd_of_coprime_aux{M D : ℤ} {n : ℕ} (hn : 2 ≤ n) (hM : IsCoprime M D)
    (hD : (n : ℤ) ∣ D) : ¬ (n : ℤ) ∣ M := by
  intro h
  have := hM.isUnit_of_dvd' h hD
  rw [Int.isUnit_iff] at this
  omega

private theorem odd_of_coprime_aux {M D : ℤ} (hM : IsCoprime M D) (hD : (2 : ℤ) ∣ D) : Odd M := by
  rw [← Int.not_even_iff_odd, even_iff_two_dvd]
  exact_mod_cast not_dvd_of_coprime_aux (n := 2) le_rfl hM (by exact_mod_cast hD)

private instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- **Art. 233 IV: the particular characters of $(a, b, c)$ are determined by $M$.**
Let $M(a, b, c)$ be a quadratic residue of its determinant $D = b^2 - ac$ and $M$ prime to $D$. Then
(i) for every odd prime $p \mid D$ and all $x, y$ with $f(x, y) = a x^2 + 2 b x y + c y^2$ prime to $p$,
$\left(\frac{f(x, y)}{p}\right) = \left(\frac{M}{p}\right)$; (ii) if $4 \mid D$, every odd value $f(x, y)$ is
$\equiv M \pmod 4$; (iii) if $8 \mid D$, every odd value is $\equiv M \pmod 8$. Proved from Art. 233 II
(`art233_two_prime_power`, `art233_two_four`, `art233_two_two_power`) because a residue modulo $D$ is a residue modulo
each divisor of $D$. Statement as in Gauss (the hypothesis `IsResidueForm M a b c D` is modulo $D$ itself, which may be
negative; congruences modulo $D$ and $-D$ agree). -/
@[kb "gauss1801" "Art. 233 IV"]
theorem art233_four {M a b c : ℤ} (hres : IsResidueForm M a b c (gaussDet a b c))
    (hM : IsCoprime M (gaussDet a b c)) :
    (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → (p : ℤ) ∣ gaussDet a b c → ∀ x y : ℤ,
      ¬ (p : ℤ) ∣ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 →
        legendreSym p (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) = legendreSym p M) ∧
    ((4 : ℤ) ∣ gaussDet a b c → ∀ x y : ℤ, Odd (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) →
      a * x ^ 2 + 2 * b * x * y + c * y ^ 2 ≡ M [ZMOD 4]) ∧
    ((8 : ℤ) ∣ gaussDet a b c → ∀ x y : ℤ, Odd (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) →
      a * x ^ 2 + 2 * b * x * y + c * y ^ 2 ≡ M [ZMOD 8]) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p _ _ hpD x y hf
    exact art233_two_prime_power (μ := 1) le_rfl (by simpa using hres.of_dvd hpD)
      (not_dvd_of_coprime_aux (Fact.out : p.Prime).two_le hM hpD) x y hf
  · intro h4 x y hf
    have hMo := odd_of_coprime_aux hM (dvd_trans (by norm_num) h4)
    exact art233_two_four (hres.of_dvd h4) hMo x y hf
  · intro h8 x y hf
    have hMo := odd_of_coprime_aux hM (dvd_trans (by norm_num) h8)
    exact art233_two_two_power (k := 3) le_rfl (by simpa using hres.of_dvd h8) hMo x y hf

/-- **Gauss's example for Art. 233 IV:** $3(20, 10, 27)$ has determinant
$10^2 - 20 \cdot 27 = -440$ and is a quadratic residue of $440$ (hence of $-440$) with value $(150, 9)$. Since
$440 = 8 \cdot 5 \cdot 11$, the complete character is: $3 \equiv 3 \pmod 8$ for $8$,
$\left(\frac{3}{5}\right) = -1$ (character $N5$), $\left(\frac{3}{11}\right) = 1$ (character $R11$), i.e.
"$3, 8; N5; R11$". As a consistency check the value $f(0, 1) = 27$ is $\equiv 3 \pmod 8$. -/
@[kb "gauss1801" "Art. 233 IV"]
theorem art233_four_example :
    gaussDet 20 10 27 = -440 ∧ IsResidueForm 3 20 10 27 440 ∧
      IsResidueForm 3 20 10 27 (gaussDet 20 10 27) ∧ (8 : ℤ) ∣ 440 ∧
      legendreSym 5 3 = -1 ∧ legendreSym 11 3 = 1 ∧
      (20 * 0 ^ 2 + 2 * 10 * 0 * 1 + 27 * 1 ^ 2 : ℤ) ≡ 3 [ZMOD 8] := by
  have h440 : IsResidueForm 3 20 10 27 440 := ⟨150, 9, by decide, by decide, by decide⟩
  refine ⟨by decide, h440, ?_, by norm_num, ?_, ?_, by decide⟩
  · have : gaussDet 20 10 27 = -440 := by decide
    rw [this]; exact isResidueForm_neg_modulus h440
  · refine (legendreSym.eq_neg_one_iff 5).mpr ?_
    rintro ⟨r, hr⟩
    have : ∀ r : ZMod 5, ((3 : ℤ) : ZMod 5) ≠ r * r := by decide
    exact this r hr
  · refine (legendreSym.eq_one_iff 11 (by decide)).mpr ⟨5, by decide⟩

private theorem crt_aux {m₁ m₂ : ℤ} (hc : IsCoprime m₁ m₂) (x y : ℤ) :
    ∃ g : ℤ, g ≡ x [ZMOD m₁] ∧ g ≡ y [ZMOD m₂] := by
  obtain ⟨u, v, huv⟩ := hc
  refine ⟨x * (v * m₂) + y * (u * m₁), Int.modEq_iff_dvd.mpr ⟨u * (x - y), ?_⟩,
    Int.modEq_iff_dvd.mpr ⟨v * (y - x), ?_⟩⟩
  · linear_combination (-x) * huv
  · linear_combination (-y) * huv

private theorem modEq_mul_aux {m₁ m₂ x y : ℤ} (hc : IsCoprime m₁ m₂) (h₁ : x ≡ y [ZMOD m₁])
    (h₂ : x ≡ y [ZMOD m₂]) : x ≡ y [ZMOD m₁ * m₂] :=
  Int.modEq_iff_dvd.mpr (hc.mul_dvd (Int.modEq_iff_dvd.mp h₁) (Int.modEq_iff_dvd.mp h₂))

/-- **Chinese remainder theorem for residue forms:** if $M(a, b, c)$ is a quadratic residue modulo each of two
coprime moduli $m_1, m_2$, it is one modulo $m_1 m_2$. -/
theorem isResidueForm_mul {M a b c m₁ m₂ : ℤ} (hc : IsCoprime m₁ m₂)
    (h₁ : IsResidueForm M a b c m₁) (h₂ : IsResidueForm M a b c m₂) :
    IsResidueForm M a b c (m₁ * m₂) := by
  obtain ⟨g₁, k₁, a1, a2, a3⟩ := h₁
  obtain ⟨g₂, k₂, b1, b2, b3⟩ := h₂
  obtain ⟨g, hg1, hg2⟩ := crt_aux hc g₁ g₂
  obtain ⟨k, hk1, hk2⟩ := crt_aux hc k₁ k₂
  exact ⟨g, k, modEq_mul_aux hc ((hg1.pow 2).trans a1) ((hg2.pow 2).trans b1),
    modEq_mul_aux hc ((hg1.mul hk1).trans a2) ((hg2.mul hk2).trans b2),
    modEq_mul_aux hc ((hk1.pow 2).trans a3) ((hk2.pow 2).trans b3)⟩

private theorem zmod_two_aux : ∀ A B C : ZMod 2, B ^ 2 - A * C = 0 →
    A ^ 2 = 1 * A ∧ A * C = 1 * B ∧ C ^ 2 = 1 * C := by decide

private theorem residueForm_two {M a b c : ℤ} (hM : Odd M) (hD : (2 : ℤ) ∣ gaussDet a b c) :
    IsResidueForm M a b c 2 := by
  have hM2 : (M : ZMod 2) = 1 := by
    obtain ⟨j, hj⟩ := hM
    rw [hj]; push_cast
    have : (2 : ZMod 2) = 0 := by decide
    rw [this]; simp
  have hD2 : ((gaussDet a b c : ℤ) : ZMod 2) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (by exact_mod_cast hD)
  simp only [gaussDet] at hD2
  push_cast at hD2
  obtain ⟨e1, e2, e3⟩ := zmod_two_aux _ _ _ hD2
  refine ⟨a, c, ?_, ?_, ?_⟩
  · apply (ZMod.intCast_eq_intCast_iff _ _ 2).mp; push_cast; rw [hM2]; exact e1
  · apply (ZMod.intCast_eq_intCast_iff _ _ 2).mp; push_cast; rw [hM2]; exact e2
  · apply (ZMod.intCast_eq_intCast_iff _ _ 2).mp; push_cast; rw [hM2]; exact e3

private theorem art233_five_prime_power {M a b c : ℤ} (hM : IsCoprime M (gaussDet a b c))
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → (p : ℤ) ∣ gaussDet a b c →
      ∃ x y : ℤ, ¬ (p : ℤ) ∣ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 ∧
        legendreSym p (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) = legendreSym p M)
    (h4 : (4 : ℤ) ∣ gaussDet a b c → ¬ (8 : ℤ) ∣ gaussDet a b c →
      ∃ x y : ℤ, Odd (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) ∧
        a * x ^ 2 + 2 * b * x * y + c * y ^ 2 ≡ M [ZMOD 4])
    (h8 : (8 : ℤ) ∣ gaussDet a b c →
      ∃ x y : ℤ, Odd (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) ∧
        a * x ^ 2 + 2 * b * x * y + c * y ^ 2 ≡ M [ZMOD 8])
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hdvd : p ^ k ∣ (gaussDet a b c).natAbs) :
    IsResidueForm M a b c ((p ^ k : ℕ) : ℤ) := by
  have hdvdZ : (p : ℤ) ^ k ∣ gaussDet a b c := by
    have := Int.natCast_dvd.mpr hdvd
    exact_mod_cast this
  have hpD : (p : ℤ) ∣ gaussDet a b c := dvd_trans (dvd_pow_self _ hk.ne') hdvdZ
  by_cases hp2 : p = 2
  · subst hp2
    have hMo : Odd M := odd_of_coprime_aux hM (by exact_mod_cast hpD)
    rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk3
    · simpa using residueForm_two hMo (by exact_mod_cast hpD)
    · have h4D : (4 : ℤ) ∣ gaussDet a b c := by exact_mod_cast hdvdZ
      have := art233_three_four h4D hMo (by
        by_cases h8D : (8 : ℤ) ∣ gaussDet a b c
        · obtain ⟨x, y, hx, hxM⟩ := h8 h8D
          exact ⟨x, y, hx, hxM.of_dvd (by norm_num)⟩
        · exact h4 h4D h8D)
      simpa using this
    · have h8D : (8 : ℤ) ∣ gaussDet a b c := by
        refine dvd_trans ?_ hdvdZ
        have : (2 : ℤ) ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 hk3
        simpa using this
      have := art233_three_two_power hk3 (by exact_mod_cast hdvdZ) hMo (h8 h8D)
      simpa using this
  · have : Fact p.Prime := ⟨hp⟩
    have hMp : ¬ (p : ℤ) ∣ M := not_dvd_of_coprime_aux hp.two_le hM hpD
    have := art233_three_prime_power (M := M) hp2 hk hdvdZ hMp (hodd p hp2 hpD)
    simpa using this

/-- **Art. 233 V, converse of Art. 233 IV: a number with all the particular characters
is a residue.** Let $D = b^2 - ac \ne 0$ and $M$ prime to $D$. Suppose $M$ has the particular characters of
$(a, b, c)$: for every odd prime $p \mid D$ some value $f(x, y)$ prime to $p$ has $\left(\frac{f(x, y)}{p}\right) =
\left(\frac{M}{p}\right)$; if $4 \mid D$ but $8 \nmid D$ some odd value is $\equiv M \pmod 4$; if $8 \mid D$ some odd
value is $\equiv M \pmod 8$. Then $M(a, b, c)$ is a quadratic residue of $D$. Proof: Art. 233 III
(`art233_three_prime_power`, `art233_three_four`, `art233_three_two_power`) on each prime power dividing $D$,
the case $2 \,\|\, D$ being automatic ($g \equiv a$, $h \equiv c \pmod 2$), then the Chinese remainder theorem
(`isResidueForm_mul`) by induction over the factorization of $|D|$. Statement as in Gauss; no extra hypotheses
beyond $D \ne 0$ (needed so that $|D|$ has a factorization; for $D = 0$ the conclusion is a different matter). -/
@[kb "gauss1801" "Art. 233 V"]
theorem art233_five {M a b c : ℤ} (hD : gaussDet a b c ≠ 0) (hM : IsCoprime M (gaussDet a b c))
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → (p : ℤ) ∣ gaussDet a b c →
      ∃ x y : ℤ, ¬ (p : ℤ) ∣ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 ∧
        legendreSym p (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) = legendreSym p M)
    (h4 : (4 : ℤ) ∣ gaussDet a b c → ¬ (8 : ℤ) ∣ gaussDet a b c →
      ∃ x y : ℤ, Odd (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) ∧
        a * x ^ 2 + 2 * b * x * y + c * y ^ 2 ≡ M [ZMOD 4])
    (h8 : (8 : ℤ) ∣ gaussDet a b c →
      ∃ x y : ℤ, Odd (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) ∧
        a * x ^ 2 + 2 * b * x * y + c * y ^ 2 ≡ M [ZMOD 8]) :
    IsResidueForm M a b c (gaussDet a b c) := by
  set N := (gaussDet a b c).natAbs with hN
  have hN0 : N ≠ 0 := Int.natAbs_ne_zero.mpr hD
  have key : ∀ n : ℕ, n ∣ N → IsResidueForm M a b c (n : ℤ) := by
    intro n
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero =>
      intro h; exact absurd (zero_dvd_iff.mp h) hN0
    | one => intro _; exact ⟨0, 0, by simp [Int.ModEq], by simp [Int.ModEq], by simp [Int.ModEq]⟩
    | prime_pow p k hp hk =>
      intro h
      exact art233_five_prime_power hM hodd h4 h8 hp hk h
    | coprime a' b' ha hb hcop iha ihb =>
      intro h
      have := isResidueForm_mul (Nat.isCoprime_iff_coprime.mpr hcop)
        (iha (dvd_trans (dvd_mul_right _ _) h)) (ihb (dvd_trans (dvd_mul_left _ _) h))
      simpa using this
  have h1 := key N dvd_rfl
  rcases Int.natAbs_eq (gaussDet a b c) with h | h
  · rw [h]; exact h1
  · rw [h]; exact isResidueForm_neg_modulus h1

/-! ### Art. 233 VII: counting the values of $\sqrt{M(a, b, c)}$ -/

/-- **A value of $\sqrt{M(a, b, c)} \pmod m$** (Gauss, *Disq. Arith.* Art. 233), as a pair $v = (g, h)$ in
$\mathbb{Z}/m \times \mathbb{Z}/m$: $g^2 = Ma$, $g h = Mb$, $h^2 = Mc$ in $\mathbb{Z}/m$. Values are counted modulo $m$. -/
def IsSqrtValue (M a b c : ℤ) (m : ℕ) (v : ZMod m × ZMod m) : Prop :=
  v.1 ^ 2 = ((M * a : ℤ) : ZMod m) ∧ v.1 * v.2 = ((M * b : ℤ) : ZMod m) ∧
    v.2 ^ 2 = ((M * c : ℤ) : ZMod m)

/-- **The set of values of $\sqrt{M(a, b, c)} \pmod m$**, a subset of $\mathbb{Z}/m \times \mathbb{Z}/m$. -/
def sqrtValues (M a b c : ℤ) (m : ℕ) : Set (ZMod m × ZMod m) := {v | IsSqrtValue M a b c m v}

/-- The values of $\sqrt{M(a, b, c)}$ come in opposite pairs: if $(g, h)$ is a value so is $(-g, -h)$. -/
theorem IsSqrtValue.neg {M a b c : ℤ} {m : ℕ} {v : ZMod m × ZMod m} (h : IsSqrtValue M a b c m v) :
    IsSqrtValue M a b c m (-v) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp [h1, h2, h3]

/-- A residue form (integer congruences) has a value in `ZMod m`. -/
theorem sqrtValues_nonempty_of_isResidueForm {M a b c : ℤ} {m : ℕ}
    (h : IsResidueForm M a b c (m : ℤ)) : (sqrtValues M a b c m).Nonempty := by
  obtain ⟨g, k, h1, h2, h3⟩ := h
  refine ⟨((g : ZMod m), (k : ZMod m)), ?_, ?_, ?_⟩
  · have := (ZMod.intCast_eq_intCast_iff _ _ m).mpr h1; push_cast at this ⊢; exact this
  · have := (ZMod.intCast_eq_intCast_iff _ _ m).mpr h2; push_cast at this ⊢; exact this
  · have := (ZMod.intCast_eq_intCast_iff _ _ m).mpr h3; push_cast at this ⊢; exact this

private theorem card_values_unit_left {R : Type*} [CommRing R] {α β γ : R} (hα : IsUnit α)
    (hβ : β ^ 2 = α * γ) :
    Nat.card {v : R × R // v.1 ^ 2 = α ∧ v.1 * v.2 = β ∧ v.2 ^ 2 = γ} =
      Nat.card {g : R // g ^ 2 = α} := by
  apply Nat.card_eq_of_bijective (fun v => ⟨v.1.1, v.2.1⟩)
  constructor
  · rintro ⟨⟨g, h⟩, hg, hgh, hh⟩ ⟨⟨g', h'⟩, hg', hgh', hh'⟩ heq
    simp only [Subtype.mk.injEq] at heq
    subst heq
    have hu : IsUnit g := (isUnit_pow_iff two_ne_zero).mp (hg ▸ hα)
    have : h = h' := (hu.mul_right_inj).mp (hgh.trans hgh'.symm)
    subst this
    rfl
  · rintro ⟨g, hg⟩
    have hu : IsUnit g := (isUnit_pow_iff two_ne_zero).mp (hg ▸ hα)
    obtain ⟨u, rfl⟩ := hu
    refine ⟨⟨(↑u, β * ↑u⁻¹), hg, ?_, ?_⟩, rfl⟩
    · show (u : R) * (β * ↑u⁻¹) = β
      rw [mul_left_comm, Units.mul_inv, mul_one]
    · show (β * (↑u⁻¹ : R)) ^ 2 = γ
      have E3 : (u : R) * ↑u⁻¹ = 1 := u.mul_inv
      linear_combination (↑u⁻¹ : R) ^ 2 * hβ - γ * (↑u⁻¹ : R) ^ 2 * hg +
        γ * ((u : R) * ↑u⁻¹ + 1) * E3

private theorem card_values_unit_right {R : Type*} [CommRing R] {α β γ : R} (hγ : IsUnit γ)
    (hβ : β ^ 2 = α * γ) :
    Nat.card {v : R × R // v.1 ^ 2 = α ∧ v.1 * v.2 = β ∧ v.2 ^ 2 = γ} =
      Nat.card {g : R // g ^ 2 = γ} := by
  rw [← card_values_unit_left (α := γ) (β := β) (γ := α) hγ (by rw [hβ, mul_comm])]
  refine Nat.card_congr ((Equiv.prodComm R R).subtypeEquiv fun v => ?_)
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  rw [mul_comm v.2 v.1]
  tauto

private theorem card_sqrt_of_root {R : Type*} [CommRing R] {r g0 : R} (hg : IsUnit g0)
    (h0 : g0 ^ 2 = r) : Nat.card {g : R // g ^ 2 = r} = Nat.card {t : R // t ^ 2 = 1} := by
  symm
  apply Nat.card_eq_of_bijective (fun t => ⟨g0 * t.1, by rw [mul_pow, h0, t.2, mul_one]⟩)
  constructor
  · intro t t' h
    have := congrArg Subtype.val h
    exact Subtype.ext ((hg.mul_right_inj).mp this)
  · rintro ⟨g, hgr⟩
    obtain ⟨u, rfl⟩ := hg
    refine ⟨⟨↑u⁻¹ * g, ?_⟩, Subtype.ext ?_⟩
    · have E3 : (u : R) * ↑u⁻¹ = 1 := u.mul_inv
      show ((↑u⁻¹ : R) * g) ^ 2 = 1
      linear_combination (↑u⁻¹ : R) ^ 2 * hgr - (↑u⁻¹ : R) ^ 2 * h0 + ((u : R) * ↑u⁻¹ + 1) * E3
    · show (u : R) * (↑u⁻¹ * g) = g
      rw [← mul_assoc, u.mul_inv, one_mul]

private theorem isUnit_cast_of_isCoprime {x : ℤ} {m : ℕ} (h : IsCoprime x (m : ℤ)) :
    IsUnit (x : ZMod m) := by
  obtain ⟨u, v, huv⟩ := h
  refine IsUnit.of_mul_eq_one (u : ZMod m) ?_
  have := congrArg (Int.cast : ℤ → ZMod m) huv
  push_cast at this
  simpa [ZMod.natCast_self, mul_comm] using this

private theorem beta_sq {M a b c : ℤ} {m : ℕ} {v : ZMod m × ZMod m} (h : IsSqrtValue M a b c m v) :
    ((M * b : ℤ) : ZMod m) ^ 2 = ((M * a : ℤ) : ZMod m) * ((M * c : ℤ) : ZMod m) := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [← h2, ← h1, ← h3]; ring

private theorem card_left {M a b c : ℤ} {m : ℕ} (hne : (sqrtValues M a b c m).Nonempty)
    (hα : IsUnit ((M * a : ℤ) : ZMod m)) :
    Nat.card (sqrtValues M a b c m) = Nat.card {g : ZMod m // g ^ 2 = ((M * a : ℤ) : ZMod m)} := by
  obtain ⟨v, hv⟩ := hne
  exact card_values_unit_left hα (beta_sq hv)

private theorem card_right {M a b c : ℤ} {m : ℕ} (hne : (sqrtValues M a b c m).Nonempty)
    (hγ : IsUnit ((M * c : ℤ) : ZMod m)) :
    Nat.card (sqrtValues M a b c m) = Nat.card {g : ZMod m // g ^ 2 = ((M * c : ℤ) : ZMod m)} := by
  obtain ⟨v, hv⟩ := hne
  exact card_values_unit_right hγ (beta_sq hv)

private theorem two_pow_sq_one_cases {j : ℕ} {x : ℤ} (hx : x ^ 2 ≡ 1 [ZMOD 2 ^ (j + 3)]) :
    x ≡ 1 [ZMOD 2 ^ (j + 3)] ∨ x ≡ -1 [ZMOD 2 ^ (j + 3)] ∨
      x ≡ 1 + 2 ^ (j + 2) [ZMOD 2 ^ (j + 3)] ∨ x ≡ -1 + 2 ^ (j + 2) [ZMOD 2 ^ (j + 3)] := by
  have hd : (2 : ℤ) ^ (j + 3) ∣ x ^ 2 - 1 := Int.modEq_iff_dvd.mp hx.symm
  have h2 : (2 : ℤ) ∣ x ^ 2 - 1 := dvd_trans ⟨2 ^ (j + 2), by ring⟩ hd
  obtain ⟨s, hs⟩ : ∃ s, x = 2 * s + 1 := by
    rcases Int.even_or_odd' x with ⟨s, hs | hs⟩
    · exfalso
      rw [hs] at h2
      have : (2 : ℤ) ∣ 4 * s ^ 2 - 1 := by convert h2 using 1; ring
      generalize s ^ 2 = t at this
      omega
    · exact ⟨s, hs⟩
  subst hs
  have hP : (2 : ℤ) ^ (j + 1) ∣ s * (s + 1) := by
    have : (4 : ℤ) * 2 ^ (j + 1) ∣ 4 * (s * (s + 1)) := by
      convert hd using 1 <;> ring
    exact (mul_dvd_mul_iff_left (by norm_num)).mp this
  rcases Int.even_or_odd s with hse | hso
  · have hc : IsCoprime ((2 : ℤ) ^ (j + 1)) (s + 1) :=
      (isCoprime_two_pow_of_odd (hse.add_one) (j + 1)).symm
    obtain ⟨q, hq⟩ := hc.dvd_of_dvd_mul_right hP
    subst hq
    rcases Int.even_or_odd' q with ⟨q', rfl | rfl⟩
    · left; exact Int.modEq_iff_dvd.mpr ⟨-q', by ring⟩
    · right; right; left; exact Int.modEq_iff_dvd.mpr ⟨-q', by ring⟩
  · have hc : IsCoprime ((2 : ℤ) ^ (j + 1)) s :=
      (isCoprime_two_pow_of_odd hso (j + 1)).symm
    obtain ⟨q, hq⟩ := hc.dvd_of_dvd_mul_left hP
    have hs' : s = 2 ^ (j + 1) * q - 1 := by linarith
    subst hs'
    rcases Int.even_or_odd' q with ⟨q', rfl | rfl⟩
    · right; left; exact Int.modEq_iff_dvd.mpr ⟨-q', by ring⟩
    · right; right; right; exact Int.modEq_iff_dvd.mpr ⟨-q', by ring⟩

private theorem zmod_two_pow_eq_iff (j : ℕ) (x y : ℤ) :
    (x : ZMod (2 ^ (j + 3))) = y ↔ x ≡ y [ZMOD 2 ^ (j + 3)] := by
  have := ZMod.intCast_eq_intCast_iff x y (2 ^ (j + 3))
  simpa using this

private theorem card_sq_one_two_pow (j : ℕ) :
    Nat.card {t : ZMod (2 ^ (j + 3)) // t ^ 2 = 1} = 4 := by
  have hz : (2 : ZMod (2 ^ (j + 3))) ^ (j + 3) = 0 := by
    have := ZMod.natCast_self (2 ^ (j + 3)); exact_mod_cast this
  have hne : ∀ y : ℤ, ¬ ((2 : ℤ) ^ (j + 3) ∣ y) → (y : ZMod (2 ^ (j + 3))) ≠ 0 := by
    intro y hy h0
    apply hy
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd y (2 ^ (j + 3))).mp h0
    simpa using this
  have hX : (0 : ℤ) < 2 ^ j := by positivity
  have e3 : (2 : ℤ) ^ (j + 3) = 8 * 2 ^ j := by ring
  have e2 : (2 : ℤ) ^ (j + 2) = 4 * 2 ^ j := by ring
  have d2 : ¬ ((2 : ℤ) ^ (j + 3) ∣ 2) := by
    intro hd
    have := Int.le_of_dvd (by norm_num) hd
    omega
  have dh : ¬ ((2 : ℤ) ^ (j + 3) ∣ 2 ^ (j + 2)) := by
    intro hd
    have := Int.le_of_dvd (by positivity) hd
    omega
  have dm : ¬ ((2 : ℤ) ^ (j + 3) ∣ 2 ^ (j + 2) - 2) := by
    intro hd
    have : (4 : ℤ) ∣ 2 ^ (j + 2) - 2 := dvd_trans ⟨2 ^ (j + 1), by ring⟩ hd
    rw [e2] at this
    omega
  have dp : ¬ ((2 : ℤ) ^ (j + 3) ∣ 2 ^ (j + 2) + 2) := by
    intro hd
    have : (4 : ℤ) ∣ 2 ^ (j + 2) + 2 := dvd_trans ⟨2 ^ (j + 1), by ring⟩ hd
    rw [e2] at this
    omega
  have hz2 : (2 : ZMod (2 ^ (j + 3))) ≠ 0 := by exact_mod_cast hne 2 d2
  have hzh : (2 : ZMod (2 ^ (j + 3))) ^ (j + 2) ≠ 0 := by exact_mod_cast hne _ dh
  have hzm : (2 : ZMod (2 ^ (j + 3))) ^ (j + 2) - 2 ≠ 0 := by exact_mod_cast hne _ dm
  have hzp : (2 : ZMod (2 ^ (j + 3))) ^ (j + 2) + 2 ≠ 0 := by exact_mod_cast hne _ dp
  have key : (Finset.univ.filter fun t : ZMod (2 ^ (j + 3)) => t ^ 2 = 1) =
      {1, -1, 1 + 2 ^ (j + 2), -1 + 2 ^ (j + 2)} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro ht
      obtain ⟨x, rfl⟩ := ZMod.intCast_surjective t
      have hx : x ^ 2 ≡ 1 [ZMOD 2 ^ (j + 3)] := by
        have := (zmod_two_pow_eq_iff j (x ^ 2) 1).mp (by push_cast; exact ht)
        exact this
      rcases two_pow_sq_one_cases hx with h1 | h1 | h1 | h1
      · left
        have := (zmod_two_pow_eq_iff j x 1).mpr h1
        simpa using this
      · right; left
        have := (zmod_two_pow_eq_iff j x (-1)).mpr h1
        simpa using this
      · right; right; left
        have := (zmod_two_pow_eq_iff j x (1 + 2 ^ (j + 2))).mpr h1
        push_cast at this; exact this
      · right; right; right
        have := (zmod_two_pow_eq_iff j x (-1 + 2 ^ (j + 2))).mpr h1
        push_cast at this; exact this
    · rintro (rfl | rfl | rfl | rfl)
      · simp
      · simp
      · linear_combination (1 + 2 ^ (j + 1) : ZMod (2 ^ (j + 3))) * hz
      · linear_combination (2 ^ (j + 1) - 1 : ZMod (2 ^ (j + 3))) * hz
  have p1 : (1 : ZMod (2 ^ (j + 3))) ∉
      ({-1, 1 + 2 ^ (j + 2), -1 + 2 ^ (j + 2)} : Finset (ZMod (2 ^ (j + 3)))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun e => hz2 (by linear_combination e), fun e => hzh (by linear_combination -e),
      fun e => hzm (by linear_combination -e)⟩
  have p2 : (-1 : ZMod (2 ^ (j + 3))) ∉
      ({1 + 2 ^ (j + 2), -1 + 2 ^ (j + 2)} : Finset (ZMod (2 ^ (j + 3)))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun e => hzp (by linear_combination -e), fun e => hzh (by linear_combination -e)⟩
  have p3 : (1 + 2 ^ (j + 2) : ZMod (2 ^ (j + 3))) ∉
      ({-1 + 2 ^ (j + 2)} : Finset (ZMod (2 ^ (j + 3)))) := by
    simp only [Finset.mem_singleton]
    exact fun e => hz2 (by linear_combination e)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, key, Finset.card_insert_of_notMem p1,
    Finset.card_insert_of_notMem p2, Finset.card_insert_of_notMem p3, Finset.card_singleton]

private theorem card_sqrt_two_pow_aux (j : ℕ) {r : ℤ} (hr : Odd r) (g0 : ZMod (2 ^ (j + 3)))
    (h0 : g0 ^ 2 = (r : ZMod (2 ^ (j + 3)))) :
    Nat.card {g : ZMod (2 ^ (j + 3)) // g ^ 2 = (r : ZMod (2 ^ (j + 3)))} = 4 := by
  have hu : IsUnit (r : ZMod (2 ^ (j + 3))) :=
    isUnit_cast_of_isCoprime (by have := isCoprime_two_pow_of_odd hr (j + 3); simpa using this)
  have hg : IsUnit g0 := (isUnit_pow_iff two_ne_zero).mp (h0 ▸ hu)
  rw [card_sqrt_of_root hg h0, card_sq_one_two_pow]

private theorem card_sq_one_four : Nat.card {t : ZMod 4 // t ^ 2 = 1} = 2 := by
  rw [Nat.card_eq_fintype_card]; decide

private theorem card_sqrt_four_aux {r : ℤ} (hr : Odd r) (g0 : ZMod 4) (h0 : g0 ^ 2 = (r : ZMod 4)) :
    Nat.card {g : ZMod 4 // g ^ 2 = (r : ZMod 4)} = 2 := by
  have hu : IsUnit (r : ZMod 4) :=
    isUnit_cast_of_isCoprime (by have := isCoprime_two_pow_of_odd hr 2; simpa using this)
  have hg : IsUnit g0 := (isUnit_pow_iff two_ne_zero).mp (h0 ▸ hu)
  rw [card_sqrt_of_root hg h0, card_sq_one_four]

private theorem odd_or_odd_of_prim {a b c : ℤ}
    (hprim : ¬ ((2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ 2 * b ∧ (2 : ℤ) ∣ c)) : Odd a ∨ Odd c := by
  by_contra h
  push_neg at h
  apply hprim
  refine ⟨?_, dvd_mul_right 2 b, ?_⟩
  · have := h.1; rw [Int.not_odd_iff_even, even_iff_two_dvd] at this; exact this
  · have := h.2; rw [Int.not_odd_iff_even, even_iff_two_dvd] at this; exact this

/-- **Art. 233 VII for an odd prime power: exactly two values.** Let $p$ be an odd prime,
$\kappa \ge 1$, $M$ prime to $p$, $(a, b, c)$ properly primitive modulo $p$ (not all of $a, 2b, c$ divisible by $p$),
and suppose $M(a, b, c)$ is a quadratic residue of $p^\kappa$ (so $\sqrt{M(a, b, c)} \pmod{p^\kappa}$ has a value).
Then it has exactly two values as pairs in $\mathbb{Z}/p^\kappa \times \mathbb{Z}/p^\kappa$; they are opposites
(`IsSqrtValue.neg`). Gauss's "at most two values" is sharpened to exactly two since a value exists. The condition
$p^\kappa \mid D$ is not needed (it follows from the existing value, Art. 233 I). Proof: one of $a, c$ is prime to $p$
(if $p \mid a$, $p \mid c$ then $p \mid g$, $p \mid Mb$), the other coordinate is determined by the first, and the
number of square roots of a unit modulo $p^\kappa$ is $2$ (`art333_prime_power_card`). -/
@[kb "gauss1801" "Art. 233 VII"]
theorem art233_seven_prime_power {M a b c : ℤ} {p κ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hκ : 1 ≤ κ)
    (hM : ¬ (p : ℤ) ∣ M) (hprim : ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ 2 * b ∧ (p : ℤ) ∣ c))
    (hres : IsResidueForm M a b c ((p ^ κ : ℕ) : ℤ)) :
    Nat.card (sqrtValues M a b c (p ^ κ)) = 2 := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hne := sqrtValues_nonempty_of_isResidueForm hres
  obtain ⟨v, hv⟩ := hne
  have hv' : IsSqrtValue M a b c (p ^ κ) v := hv
  have hac : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ c := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hpa, hpc⟩ := hcon
    obtain ⟨g, k, h1, h2, h3⟩ := hres
    have hpp : (p : ℤ) ∣ ((p ^ κ : ℕ) : ℤ) := by
      exact_mod_cast dvd_pow_self p (by omega : κ ≠ 0)
    have h1' := Int.modEq_iff_dvd.mp (h1.of_dvd hpp)
    have hg : (p : ℤ) ∣ g := hpz.dvd_of_dvd_pow (n := 2) (by
      have := dvd_sub (dvd_mul_of_dvd_right hpa M) h1'
      simpa using this)
    have h2' := Int.modEq_iff_dvd.mp (h2.of_dvd hpp)
    have hMb : (p : ℤ) ∣ M * b := by
      have := dvd_add h2' (dvd_mul_of_dvd_left hg k)
      simpa using this
    rcases hpz.dvd_or_dvd hMb with h | h
    · exact hM h
    · exact hprim ⟨hpa, dvd_mul_of_dvd_right h 2, hpc⟩
  have hpr : ∀ r : ℤ, ¬ (p : ℤ) ∣ r → IsUnit ((r : ℤ) : ZMod (p ^ κ)) := by
    intro r hr
    apply isUnit_cast_of_isCoprime
    have : IsCoprime (p : ℤ) r := (Irreducible.coprime_iff_not_dvd hpz.irreducible).mpr hr
    push_cast
    exact this.symm.pow_right
  have hsq : ∀ (r : ℤ) (g0 : ZMod (p ^ κ)), ¬ (p : ℤ) ∣ r → g0 ^ 2 = (r : ZMod (p ^ κ)) →
      Nat.card {g : ZMod (p ^ κ) // g ^ 2 = (r : ZMod (p ^ κ))} = 2 := by
    intro r g0 hr h0
    rw [art333_prime_power_card hp hp2 (by omega) hr, if_pos]
    refine ⟨ZMod.castHom (dvd_pow_self p (by omega : κ ≠ 0)) (ZMod p) g0, ?_⟩
    have := congrArg (ZMod.castHom (dvd_pow_self p (by omega : κ ≠ 0)) (ZMod p)) h0
    rw [map_pow, map_intCast] at this
    rw [← this]; ring
  rcases hac with ha | hc
  · have hMa : ¬ (p : ℤ) ∣ M * a := fun h => (hpz.dvd_or_dvd h).elim hM ha
    rw [card_left ⟨v, hv⟩ (hpr _ hMa)]
    exact hsq _ v.1 hMa hv'.1
  · have hMc : ¬ (p : ℤ) ∣ M * c := fun h => (hpz.dvd_or_dvd h).elim hM hc
    rw [card_right ⟨v, hv⟩ (hpr _ hMc)]
    exact hsq _ v.2 hMc hv'.2.2

/-- **Art. 233 VII for the modulus $4$: exactly two values.** For $M$ odd,
$(a, b, c)$ properly primitive modulo $2$ (not all of $a, 2b, c$ even, i.e. $a$ or $c$ odd) and $M(a, b, c)$ a
quadratic residue of $4$, $\sqrt{M(a, b, c)} \pmod 4$ has exactly two values as pairs in
$\mathbb{Z}/4 \times \mathbb{Z}/4$, the opposites $\pm(g, h)$. -/
@[kb "gauss1801" "Art. 233 VII"]
theorem art233_seven_four {M a b c : ℤ} (hM : Odd M)
    (hprim : ¬ ((2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ 2 * b ∧ (2 : ℤ) ∣ c)) (hres : IsResidueForm M a b c 4) :
    Nat.card (sqrtValues M a b c 4) = 2 := by
  have hne := sqrtValues_nonempty_of_isResidueForm (m := 4) (by exact_mod_cast hres)
  obtain ⟨v, hv⟩ := hne
  have hv' : IsSqrtValue M a b c 4 v := hv
  rcases odd_or_odd_of_prim hprim with ha | hc
  · have hr := hM.mul ha
    have hu : IsUnit ((M * a : ℤ) : ZMod 4) :=
      isUnit_cast_of_isCoprime (by have := isCoprime_two_pow_of_odd hr 2; simpa using this)
    rw [card_left ⟨v, hv⟩ hu]
    exact card_sqrt_four_aux hr v.1 hv'.1
  · have hr := hM.mul hc
    have hu : IsUnit ((M * c : ℤ) : ZMod 4) :=
      isUnit_cast_of_isCoprime (by have := isCoprime_two_pow_of_odd hr 2; simpa using this)
    rw [card_right ⟨v, hv⟩ hu]
    exact card_sqrt_four_aux hr v.2 hv'.2.2

/-- **Art. 233 VII for $m = 2^k \ge 8$: exactly four values.** For $M$ odd,
$(a, b, c)$ properly primitive modulo $2$ ($a$ or $c$ odd), $k \ge 3$ and $M(a, b, c)$ a quadratic residue of $2^k$,
$\sqrt{M(a, b, c)} \pmod{2^k}$ has exactly four values as pairs in $\mathbb{Z}/2^k \times \mathbb{Z}/2^k$. -/
@[kb "gauss1801" "Art. 233 VII"]
theorem art233_seven_two_power {M a b c : ℤ} {k : ℕ} (hk : 3 ≤ k) (hM : Odd M)
    (hprim : ¬ ((2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ 2 * b ∧ (2 : ℤ) ∣ c))
    (hres : IsResidueForm M a b c ((2 ^ k : ℕ) : ℤ)) :
    Nat.card (sqrtValues M a b c (2 ^ k)) = 4 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  have hne := sqrtValues_nonempty_of_isResidueForm hres
  obtain ⟨v, hv⟩ := hne
  have hv' : IsSqrtValue M a b c (2 ^ (j + 3)) v := hv
  rcases odd_or_odd_of_prim hprim with ha | hc
  · have hr := hM.mul ha
    have hu : IsUnit ((M * a : ℤ) : ZMod (2 ^ (j + 3))) :=
      isUnit_cast_of_isCoprime (by have := isCoprime_two_pow_of_odd hr (j + 3); simpa using this)
    rw [card_left ⟨v, hv⟩ hu]
    exact card_sqrt_two_pow_aux j hr v.1 hv'.1
  · have hr := hM.mul hc
    have hu : IsUnit ((M * c : ℤ) : ZMod (2 ^ (j + 3))) :=
      isUnit_cast_of_isCoprime (by have := isCoprime_two_pow_of_odd hr (j + 3); simpa using this)
    rw [card_right ⟨v, hv⟩ hu]
    exact card_sqrt_two_pow_aux j hr v.2 hv'.2.2

/-- **Art. 233 VII for $m = 2$: exactly one value.** If $M(a, b, c)$ is a quadratic residue
of $2$, then $\sqrt{M(a, b, c)} \pmod 2$ has exactly one value $(g, h)$ in $\mathbb{Z}/2 \times \mathbb{Z}/2$
(namely $g = Ma$, $h = Mc$ since $x^2 = x$ in $\mathbb{Z}/2$); so $(g, h) = (-g, -h)$, as Gauss says. -/
@[kb "gauss1801" "Art. 233 VII"]
theorem art233_seven_two {M a b c : ℤ} (hres : IsResidueForm M a b c 2) :
    Nat.card (sqrtValues M a b c 2) = 1 := by
  have hne := sqrtValues_nonempty_of_isResidueForm (m := 2) (by exact_mod_cast hres)
  have hsq : ∀ x : ZMod 2, x ^ 2 = x := by decide
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun ⟨v, hv⟩ ⟨w, hw⟩ => ?_⟩, hne.to_subtype⟩
  have hv' : IsSqrtValue M a b c 2 v := hv
  have hw' : IsSqrtValue M a b c 2 w := hw
  refine Subtype.ext (Prod.ext ?_ ?_)
  · calc v.1 = v.1 ^ 2 := (hsq _).symm
      _ = _ := hv'.1
      _ = w.1 ^ 2 := hw'.1.symm
      _ = w.1 := hsq _
  · calc v.2 = v.2 ^ 2 := (hsq _).symm
      _ = _ := hv'.2.2
      _ = w.2 ^ 2 := hw'.2.2.symm
      _ = w.2 := hsq _

end QuadFormsKB.Historical.Gauss
