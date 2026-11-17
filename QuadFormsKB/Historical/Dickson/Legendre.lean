/-
# Legendre's theorem on $ax^2 + by^2 + cz^2 = 0$ (Dickson, *Studies*, 1930) and the Hasse–Minkowski and Meyer theorems (Dickson, *History* III)

**Library** `QuadFormsKB.Historical.Dickson` (historical library, not imported by `QuadFormsKB`).  Targets
:

* (Dickson, *Studies in the Theory of Numbers* (1930), ch. II): Legendre's theorem. For nonzero integers $a, b, c$ with $abc$ squarefree,
  $ax^2 + by^2 + cz^2 = 0$ has a nontrivial integral solution iff $a, b, c$ are not all of one sign and $-bc$, $-ca$,
  $-ab$ are quadratic residues modulo $\lvert a\rvert$, $\lvert b\rvert$, $\lvert c\rvert$ respectively; the solution may then
  be taken with $x, y, z$ pairwise coprime (`legendre_iff`, `legendre_exists_pairwise_coprime`).
  *Update (candidate, missing hypothesis):* the historical sources say "pairwise coprime" $a, b, c$; with only pairwise coprimality the
  "only if" direction is false: $-x^2 - y^2 + 4z^2 = 0$ has the primitive solution $(0, 2, 1)$ but $-ab = -1$ is not a
  square modulo $4$ (`legendre_counterexample_not_squarefree`). The classical hypothesis is that $abc$ is squarefree
  (which implies pairwise coprimality); this is the form proved here. Whether the printed text has "squarefree" was
  not checked against the book (loose end).
* (Dickson, *History* III (1923)): the Hasse–Minkowski
  theory of rational quadratic forms. Formalized here: the local–global principle for isotropy
  (`hasse_minkowski_isotropy`, a wrapper of `QuadFormsKB.hasseMinkowski`), the local–global principle for
  equivalence (`hasse_minkowski_equivalence`, a wrapper of `QuadFormsKB.isometric_iff_everywhere`), and Meyer's
  theorem: every indefinite nondegenerate rational form in at least $5$ variables represents $0$ nontrivially
  (`meyer_five`, a wrapper of `QuadFormsKB.Cassels.Ch6.meyer`). **Partial:** the explicit list of complete invariants
  (determinant modulo squares, number of negative terms, Hasse invariants $C_p$) as a single global statement is
  not formalized; the $p$-adic part is `QuadFormsKB.isometric_padic_iff_invariants` in the core library (loose end).

*Proof of Legendre's theorem.* Sufficiency: the residue conditions give condition (i) of Cassels' Theorem 4.1 at
every odd prime (for $p \mid a$, $b$ is invertible modulo $p$ and $r = s b^{-1}$ with $s^2 \equiv -bc$ gives
$br^2 + c \equiv 0$), and `QuadFormsKB.Cassels.Ch6.legendre_indefinite` (Legendre's form of the theorem, with the
exceptional place $2$) gives a nontrivial zero. Necessity: from a primitive zero, a prime $p \mid a$ cannot divide $y$
(else $p \mid cz^2$, so $p \mid z$, so $p^2 \mid ax^2$ and squarefreeness gives $p \mid x$), and then $-bc \equiv (cz/y)^2$.
-/
import QuadFormsKB.Literature.Cassels.Ch6.LegendreIndefinite
import QuadFormsKB.Literature.Cassels.Ch6.Sec1

namespace QuadFormsKB.Historical.Dickson

open QuadFormsKB.RatPlace

/-! ### Legendre's theorem -/

private theorem no_sq_dvd {p : ℕ} (hp : p.Prime) {m : ℤ} (hm : Squarefree m) (h : (p : ℤ) * p ∣ m) :
    False := by
  have := hm (p : ℤ) h
  exact hp.ne_one (by simpa using Int.isUnit_iff_natAbs_eq.1 this)

private theorem pair_div {a b c x y z : ℤ} (hc : Squarefree c) (h : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0)
    {p : ℕ} (hp : p.Prime) (hx : (p : ℤ) ∣ x) (hy : (p : ℤ) ∣ y) : (p : ℤ) ∣ z := by
  by_contra hz
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h1 : (p : ℤ) ^ 2 ∣ c * z ^ 2 := by
    have : c * z ^ 2 = -(a * x ^ 2 + b * y ^ 2) := by linarith
    rw [this]
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    exact ⟨-(a * u ^ 2 + b * v ^ 2), by ring⟩
  have h2 : (p : ℤ) ^ 2 ∣ c :=
    hpp.pow_dvd_of_dvd_mul_right 2 (fun hh => hz (hpp.dvd_of_dvd_pow hh)) h1
  exact no_sq_dvd hp hc (by simpa [sq] using h2)

private theorem exists_prime_of_not_coprime {u v : ℤ} (h : ¬ IsCoprime u v) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ u ∧ (p : ℤ) ∣ v := by
  have : Int.gcd u v ≠ 1 := fun h' => h (Int.isCoprime_iff_gcd_eq_one.2 h')
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd this
  exact ⟨p, hp, (Int.natCast_dvd_natCast.2 hpd).trans (Int.gcd_dvd_left u v),
    (Int.natCast_dvd_natCast.2 hpd).trans (Int.gcd_dvd_right u v)⟩

private theorem exists_pc (a b c : ℤ) (hsq : Squarefree (a * b * c)) :
    ∀ N : ℕ, ∀ x y z : ℤ, x.natAbs + y.natAbs + z.natAbs = N → (x, y, z) ≠ (0, 0, 0) →
      a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 →
      ∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 ∧
        IsCoprime x y ∧ IsCoprime y z ∧ IsCoprime x z := by
  have hc : Squarefree c := hsq.of_mul_right
  have ha : Squarefree a := hsq.of_mul_left.of_mul_left
  have hb : Squarefree b := hsq.of_mul_left.of_mul_right
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro x y z hN hne h
    have red : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ x → (p : ℤ) ∣ y → (p : ℤ) ∣ z →
        ∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 ∧
          IsCoprime x y ∧ IsCoprime y z ∧ IsCoprime x z := by
      intro p hp ⟨x', hx'⟩ ⟨y', hy'⟩ ⟨z', hz'⟩
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have h' : a * x' ^ 2 + b * y' ^ 2 + c * z' ^ 2 = 0 := by
        subst hx' hy' hz'
        have : (p : ℤ) ^ 2 * (a * x' ^ 2 + b * y' ^ 2 + c * z' ^ 2) = 0 := by linarith
        rcases mul_eq_zero.1 this with h0 | h0
        · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h0) hp0
        · exact h0
      have hne' : (x', y', z') ≠ (0, 0, 0) := by
        intro h0
        simp only [Prod.mk.injEq] at h0
        obtain ⟨h1, h2, h3⟩ := h0
        apply hne; simp [hx', hy', hz', h1, h2, h3]
      refine ih (x'.natAbs + y'.natAbs + z'.natAbs) ?_ x' y' z' rfl hne' h'
      have e : N = p * (x'.natAbs + y'.natAbs + z'.natAbs) := by
        rw [← hN, hx', hy', hz']
        simp [Int.natAbs_mul, mul_add]
      have hpos : 0 < x'.natAbs + y'.natAbs + z'.natAbs := by
        by_contra h0
        apply hne'
        have : x'.natAbs = 0 := by omega
        have : y'.natAbs = 0 := by omega
        have : z'.natAbs = 0 := by omega
        simp_all
      have := hp.two_le
      nlinarith
    by_cases hxy : IsCoprime x y
    · by_cases hyz : IsCoprime y z
      · by_cases hxz : IsCoprime x z
        · exact ⟨x, y, z, hne, h, hxy, hyz, hxz⟩
        · obtain ⟨p, hp, h1, h2⟩ := exists_prime_of_not_coprime hxz
          exact red p hp h1 (pair_div (a := a) (b := c) (c := b) (x := x) (y := z) (z := y) hb
            (by linarith) hp h1 h2) h2
      · obtain ⟨p, hp, h1, h2⟩ := exists_prime_of_not_coprime hyz
        exact red p hp (pair_div (a := b) (b := c) (c := a) (x := y) (y := z) (z := x) ha
          (by linarith) hp h1 h2) h1 h2
    · obtain ⟨p, hp, h1, h2⟩ := exists_prime_of_not_coprime hxy
      exact red p hp h1 h2 (pair_div hc h hp h1 h2)

private theorem isSquare_zmod_of_primes (m : ℤ) : ∀ n : ℕ, Squarefree n →
    (∀ p : ℕ, p.Prime → p ∣ n → IsSquare ((m : ℤ) : ZMod p)) → IsSquare ((m : ℤ) : ZMod n) := by
  intro n
  induction n using Nat.recOnPrimeCoprime with
  | zero => intro h; exact absurd h not_squarefree_zero
  | prime_pow p k hp =>
    intro hsq h
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · rw [pow_zero]; exact ⟨0, Subsingleton.elim _ _⟩
      · rw [pow_one]; exact h p hp (by simp)
    · exfalso
      have h2 : p * p ∣ p ^ k := by
        rw [← sq]; exact pow_dvd_pow p hk
      have := hsq p h2
      exact hp.ne_one (Nat.isUnit_iff.1 this)
  | coprime a b ha hb hab iha ihb =>
    intro hsq h
    obtain ⟨s, hs⟩ := iha (Nat.squarefree_mul_iff.1 hsq).2.1
      (fun p hp hpd => h p hp (hpd.mul_right b))
    obtain ⟨t, ht⟩ := ihb (Nat.squarefree_mul_iff.1 hsq).2.2
      (fun p hp hpd => h p hp (hpd.mul_left a))
    let e := ZMod.chineseRemainder hab
    refine ⟨e.symm (s, t), ?_⟩
    apply e.injective
    rw [map_mul, map_intCast, RingEquiv.apply_symm_apply]
    ext <;> simp [hs, ht]

private theorem res_of_primitive {a b c x y z : ℤ}
    (h : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) {p : ℕ} (hp : p.Prime) (hpa : (p : ℤ) ∣ a)
    (hpc : ¬ (p : ℤ) ∣ c) (hyz : IsCoprime y z) : IsSquare ((-(b * c) : ℤ) : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpa' : ((a : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hpa
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hy' : ((y : ℤ) : ZMod p) ≠ 0 := by
    intro hy0
    have hpy : (p : ℤ) ∣ y := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hy0
    have hcz : (p : ℤ) ∣ c * z ^ 2 := by
      have : c * z ^ 2 = -(a * x ^ 2 + b * y ^ 2) := by linarith
      rw [this]
      exact (dvd_neg).2 (dvd_add (hpa.mul_right _) ((dvd_pow hpy two_ne_zero).mul_left b))
    have hpz : (p : ℤ) ∣ z := by
      rcases hpp.dvd_or_dvd hcz with h1 | h1
      · exact absurd h1 hpc
      · exact hpp.dvd_of_dvd_pow h1
    exact hpp.not_isUnit (hyz.isUnit_of_dvd' hpy hpz)
  have hz : (a : ZMod p) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 := by
    have := congrArg (Int.cast : ℤ → ZMod p) h
    push_cast at this
    exact this
  rw [hpa', zero_mul, zero_add] at hz
  refine ⟨c * z * (y : ZMod p)⁻¹, ?_⟩
  push_cast
  field_simp
  linear_combination (-(c : ZMod p)) * hz

private theorem no_two {a b c : ℤ} (hsq : Squarefree (a * b * c)) {p : ℕ} (hp : p.Prime) :
    ¬((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b) ∧ ¬((p : ℤ) ∣ a ∧ (p : ℤ) ∣ c) ∧ ¬((p : ℤ) ∣ b ∧ (p : ℤ) ∣ c) := by
  refine ⟨fun ⟨h1, h2⟩ => no_sq_dvd hp hsq ((mul_dvd_mul h1 h2).mul_right c),
    fun ⟨h1, h2⟩ => no_sq_dvd hp hsq ?_, fun ⟨h1, h2⟩ => no_sq_dvd hp hsq ?_⟩
  · rw [show a * b * c = a * c * b by ring]; exact (mul_dvd_mul h1 h2).mul_right b
  · rw [show a * b * c = b * c * a by ring]; exact (mul_dvd_mul h1 h2).mul_right a

private theorem cond_of_square {a b c : ℤ} (hb : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → ¬ (p : ℤ) ∣ b)
    (hsqr : IsSquare ((-(b * c) : ℤ) : ZMod a.natAbs)) {p : ℕ} (hp : p.Prime) (hpa : (p : ℤ) ∣ a) :
    ∃ r : ℤ, (p : ℤ) ∣ b * r ^ 2 + c := by
  have : Fact p.Prime := ⟨hp⟩
  have hd : p ∣ a.natAbs := Int.natCast_dvd.1 hpa
  obtain ⟨s, hs⟩ := hsqr
  have hs' : (((-(b * c)) : ℤ) : ZMod p) = ZMod.castHom hd (ZMod p) s * ZMod.castHom hd (ZMod p) s := by
    rw [← map_mul, ← hs, map_intCast]
  have hb' : (b : ZMod p) ≠ 0 := fun hh => hb p hp hpa ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hh)
  refine ⟨((ZMod.castHom hd (ZMod p) s * (b : ZMod p)⁻¹ : ZMod p).val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val]
  push_cast at hs'
  field_simp
  linear_combination (-1 : ZMod p) * hs'

private theorem nosol {a b c x y z : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) : (x, y, z) = (0, 0, 0) := by
  have h1 := mul_nonneg ha.le (sq_nonneg x)
  have h2 := mul_nonneg hb.le (sq_nonneg y)
  have h3 := mul_nonneg hc.le (sq_nonneg z)
  have e1 : a * x ^ 2 = 0 := by linarith
  have e2 : b * y ^ 2 = 0 := by linarith
  have e3 : c * z ^ 2 = 0 := by linarith
  simp [ha.ne', hb.ne', hc.ne'] at e1 e2 e3
  simp [e1, e2, e3]

private theorem signs_of_ne_zero {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : ¬ (0 < a ∧ 0 < b ∧ 0 < c)) (h2 : ¬ (a < 0 ∧ b < 0 ∧ c < 0)) :
    (∃ i, 0 < (![a, b, c] : Fin 3 → ℤ) i) ∧ (∃ j, (![a, b, c] : Fin 3 → ℤ) j < 0) := by
  rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb' <;>
    rcases lt_or_gt_of_ne hc with hc' | hc'
  · exact absurd ⟨ha', hb', hc'⟩ h2
  · exact ⟨⟨2, hc'⟩, ⟨0, ha'⟩⟩
  · exact ⟨⟨1, hb'⟩, ⟨0, ha'⟩⟩
  · exact ⟨⟨1, hb'⟩, ⟨0, ha'⟩⟩
  · exact ⟨⟨0, ha'⟩, ⟨1, hb'⟩⟩
  · exact ⟨⟨0, ha'⟩, ⟨1, hb'⟩⟩
  · exact ⟨⟨0, ha'⟩, ⟨2, hc'⟩⟩
  · exact absurd ⟨ha', hb', hc'⟩ h1

/-- Legendre's conditions on $(a, b, c)$: not all of one sign, and $-bc$, $-ca$, $-ab$ are squares modulo $\lvert a\rvert$,
$\lvert b\rvert$, $\lvert c\rvert$ respectively (as elements of `ZMod`; modulo $1$ every integer is a square). -/
def LegendreConditions (a b c : ℤ) : Prop :=
  ¬ (0 < a ∧ 0 < b ∧ 0 < c) ∧ ¬ (a < 0 ∧ b < 0 ∧ c < 0) ∧
    IsSquare ((-(b * c) : ℤ) : ZMod a.natAbs) ∧ IsSquare ((-(c * a) : ℤ) : ZMod b.natAbs) ∧
      IsSquare ((-(a * b) : ℤ) : ZMod c.natAbs)

/-- (Dickson, *Studies* (1930)), **Legendre's
theorem** (corrected form: $abc$ squarefree, see the module docstring): for integers $a, b, c$ with $abc$ squarefree
(hence nonzero and pairwise coprime), $ax^2 + by^2 + cz^2 = 0$ has a solution $(x, y, z) \ne (0, 0, 0)$ in integers iff
$a, b, c$ are not all of one sign and $-bc$, $-ca$, $-ab$ are quadratic residues modulo $\lvert a\rvert$, $\lvert b\rvert$,
$\lvert c\rvert$. -/
@[kb "dickson1930" "[unverified locator]"]
theorem legendre_iff (a b c : ℤ) (hsq : Squarefree (a * b * c)) :
    (∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) ↔ LegendreConditions a b c := by
  have hne0 := hsq.ne_zero
  have ha : a ≠ 0 := fun h => hne0 (by simp [h])
  have hb : b ≠ 0 := fun h => hne0 (by simp [h])
  have hc : c ≠ 0 := fun h => hne0 (by simp [h])
  have hsa : Squarefree a := hsq.of_mul_left.of_mul_left
  have hsb : Squarefree b := hsq.of_mul_left.of_mul_right
  have hsc : Squarefree c := hsq.of_mul_right
  constructor
  · rintro ⟨x, y, z, hne, h⟩
    obtain ⟨x, y, z, hne, h, hxy, hyz, hxz⟩ := exists_pc a b c hsq _ x y z rfl hne h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨h1, h2, h3⟩; exact hne (nosol h1 h2 h3 h)
    · rintro ⟨h1, h2, h3⟩
      exact hne (nosol (a := -a) (b := -b) (c := -c) (by linarith) (by linarith) (by linarith)
        (by linarith))
    · exact isSquare_zmod_of_primes _ a.natAbs (Int.squarefree_natAbs.2 hsa) (fun p hp hpd =>
        res_of_primitive h hp (Int.natCast_dvd.2 hpd) (fun hh => (no_two hsq hp).2.1 ⟨Int.natCast_dvd.2 hpd, hh⟩) hyz)
    · exact isSquare_zmod_of_primes _ b.natAbs (Int.squarefree_natAbs.2 hsb) (fun p hp hpd =>
        res_of_primitive (a := b) (b := c) (c := a) (x := y) (y := z) (z := x) (by linarith) hp
          (Int.natCast_dvd.2 hpd) (fun hh => (no_two hsq hp).1 ⟨hh, Int.natCast_dvd.2 hpd⟩) hxz.symm)
    · exact isSquare_zmod_of_primes _ c.natAbs (Int.squarefree_natAbs.2 hsc) (fun p hp hpd =>
        res_of_primitive (a := c) (b := a) (c := b) (x := z) (y := x) (z := y) (by linarith) hp
          (Int.natCast_dvd.2 hpd) (fun hh => (no_two hsq hp).2.2 ⟨hh, Int.natCast_dvd.2 hpd⟩) hxy)
  · rintro ⟨h1, h2, s1, s2, s3⟩
    have hi : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ j : Fin 3, (p : ℤ) ∣ (![a, b, c] : Fin 3 → ℤ) j →
        ∃ r : ℤ, (p : ℤ) ∣ (![a, b, c] : Fin 3 → ℤ) (j + 1) * r ^ 2 + (![a, b, c] : Fin 3 → ℤ) (j + 2) := by
      intro p hp _ j hj
      fin_cases j
      · exact cond_of_square (fun q hq hqa hqb => (no_two hsq hq).1 ⟨hqa, hqb⟩) s1 hp hj
      · exact cond_of_square (a := b) (b := c) (c := a)
          (fun q hq hqa hqb => (no_two hsq hq).2.2 ⟨hqa, hqb⟩) s2 hp hj
      · exact cond_of_square (a := c) (b := a) (c := b)
          (fun q hq hqa hqb => (no_two hsq hq).2.1 ⟨hqb, hqa⟩) s3 hp hj
    obtain ⟨v, hv, hv0⟩ := QuadFormsKB.Cassels.Ch6.legendre_indefinite ![a, b, c]
      (by simpa using hsq) hi (signs_of_ne_zero ha hb hc h1 h2)
    refine ⟨v 0, v 1, v 2, ?_, ?_⟩
    · intro h0
      apply hv
      simp only [Prod.mk.injEq] at h0
      funext i; fin_cases i <;> simp [h0]
    · simpa [Fin.sum_univ_three] using hv0

/-- last clause: under Legendre's conditions the solution may be taken with $x, y, z$
pairwise coprime (and not all $0$). -/
@[kb "dickson1930" "[unverified locator]"]
theorem legendre_exists_pairwise_coprime (a b c : ℤ) (hsq : Squarefree (a * b * c))
    (h : LegendreConditions a b c) :
    ∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 ∧
      IsCoprime x y ∧ IsCoprime y z ∧ IsCoprime x z := by
  obtain ⟨x, y, z, hne, h⟩ := (legendre_iff a b c hsq).2 h
  exact exists_pc a b c hsq _ x y z rfl hne h

/-- The hypothesis "pairwise coprime" stated in the historical sources is not enough for the "only if" direction:
$-x^2 - y^2 + 4z^2 = 0$ (coefficients $-1, -1, 4$, pairwise coprime) has the primitive solution $(0, 2, 1)$, but
$-ab = -1$ is not a square modulo $\lvert c\rvert = 4$. -/
theorem legendre_counterexample_not_squarefree :
    (-1 : ℤ) * 0 ^ 2 + (-1) * 2 ^ 2 + 4 * 1 ^ 2 = 0 ∧ ¬ IsSquare ((-((-1) * (-1)) : ℤ) : ZMod (4 : ℤ).natAbs) := by
  refine ⟨by norm_num, ?_⟩
  show ¬ IsSquare ((-((-1) * (-1)) : ℤ) : ZMod 4)
  rintro ⟨r, hr⟩
  revert r
  decide

/-! ### Hasse–Minkowski and Meyer -/

/-- (Dickson, *History* III), the local–global
principle for isotropy (Hasse–Minkowski): a nondegenerate quadratic form $Q$ over $\mathbb Q$ represents $0$
nontrivially over $\mathbb Q$ iff it does over $\mathbb R$ and over every $\mathbb Q_p$. **Wrapper** of
`QuadFormsKB.hasseMinkowski`. -/
@[kb "dickson1923" "[unverified locator]"]
theorem hasse_minkowski_isotropy {n : ℕ} (Q : RatQF n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn ℚ ↔ Everywhere fun K _ _ => Q.IsotropicIn K :=
  hasseMinkowski Q hQ

/-- the local–global principle for equivalence (Hasse): two nondegenerate rational
quadratic forms $Q, R$ in $n$ variables are equivalent over $\mathbb Q$ iff they are equivalent over $\mathbb R$ and over
every $\mathbb Q_p$. **Wrapper** of `QuadFormsKB.isometric_iff_everywhere`. -/
@[kb "dickson1923" "[unverified locator]"]
theorem hasse_minkowski_equivalence {n : ℕ} (Q R : RatQF n) (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.IsometricIn ℚ R ↔ Everywhere fun K _ _ => Q.IsometricIn K R :=
  isometric_iff_everywhere Q R hQ hR

/-- last clause (Meyer, 1884): every indefinite nondegenerate rational quadratic form
in $n \ge 5$ variables represents $0$ nontrivially over $\mathbb Q$. **Wrapper** of `QuadFormsKB.Cassels.Ch6.meyer`. -/
@[kb "dickson1923" "[unverified locator]"]
theorem meyer_five {n : ℕ} (Q : RatQF n) (hn : 5 ≤ n) (hQ : Q.Nondegenerate)
    (hpos : ∃ x : Fin n → ℝ, 0 < Q.evalIn ℝ x) (hneg : ∃ y : Fin n → ℝ, Q.evalIn ℝ y < 0) : Q.IsotropicIn ℚ :=
  QuadFormsKB.Cassels.Ch6.meyer Q hn hQ hpos hneg

end QuadFormsKB.Historical.Dickson
