/-
# Cassels, Chapter 11: four remarks (pp. 202, 232, 235, 236)

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11: the remark after Theorem 1.3 (p. 202),
the notation $\mathbb Z^{[p]}$ (p. 232), the reductions at the start of §9 (p. 235) and the remark on the finite set
$P$ of primes (p. 236).

**Conventions.** Forms are `QuadForm ℤ n` (integer-valued), $Q$ is the form, $n$ the number of variables, indices are
0-based ($x_0, \dots, x_{n-1}$). The Hessian is $H = C + C^{\mathsf T}$ (`QuadForm.hessian`); Cassels' determinant is
$d = \det(Q_{ij}) = \det H/2^n$, so for an *odd* prime $p$, $p \mid d$ if and only if $p \mid \det H$; statements about
odd primes are given with $\det H$. "Primitively represented over $\mathbb Z_p$" is `Cassels.PrimRepZp` (some
coordinate is a $p$-adic unit), over $\mathbb Z$ it is `Cassels.PrimRepZ` (coordinates with greatest common divisor $1$).

**Formalized (proved).**
* Remark 11.r14 (p. 202: the conditions (i), (ii) of Theorem 1.3 are not sufficient for more than one spinor genus):
  the explicit lattice $\mathbb Z^3$ with the form $x_0^2 + x_1^2 + 27x_2^2$ satisfies (i) ($p = 3$,
  $p^{n(n-1)/2} = 27 \mid \det H/8$) while its genus consists of exactly one proper spinor genus
  (`properSpinorGenusNumber_diag_one_one_odd`, `not_sufficient_theorem13`). The proof is Cassels' own route (Lemma 3.6
  Corollary, `sameProperSpinorGenus_of_sameGenus_rat`): at every odd prime the lattice has an orthogonal basis with two
  vectors of the same norm (Lemma 3.7), and at $2$ the negation of (ii) holds (Lemma 3.8 Corollary).
* Notation 11.r33 (p. 232): the ring $\mathbb Z^{[p]} = \mathbb Z[1/p]$ as the subring of $\mathbb Q$ that is the image of
  Mathlib's `Localization.Away (p : ℤ)` (`invPSubring`), with the characterizations "denominator a power of $p$"
  (`mem_invPSubring_iff`), "$\operatorname{ord}_\ell \ge 0$ for every prime $\ell \ne p$" (`mem_invPSubring_iff_padicValRat`)
  and "$\lvert a\rvert_\ell \le 1$ for every prime $\ell \ne p$" (`mem_invPSubring_iff_padicNorm`); the archimedean
  place is not constrained, as in the book ("$v \ne p, \infty$").
* Remark 11.r34 (p. 235): the scaling $N(cQ) = cN(Q)$ (`tartakowskyConstant_smul`) and the consequence that classical
  integrality versus integer-valuedness does not matter (`tartakowskyClassicalAt_iff`, using
  `primRepZ_smul_iff`, `primRepZp_smul_iff`). The sentence "we could have assumed only rational coefficients" is not
  formalized (the library's `TartakowskyAt` is about `QuadForm ℤ n`).
* Remark 11.r37 (p. 236): for a prime $p \notin P$, where $P$ is any set of primes containing $2$ and every prime
  dividing $\det H$, every integer $a$ is primitively represented over $\mathbb Z_p$ (`primRepZp_of_not_dvd_hessian_det`,
  `primRepZp_of_notMem`). *Update:* the proof gives this for every $n \ge 3$, not only $n \ge 4$ as in Theorem 1.6;
  for $n = 2$ it is false (the form $x_0^2 + x_1^2$ does not represent $3$ over $\mathbb Z_3$).
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec9
import QuadFormsKB.Literature.Cassels.Ch11Thm13
import QuadFormsKB.Siegel.UnimodularPadic
import QuadFormsKB.Binary.SiegelNonPrimitive
import QuadFormsKB.Equiv.Integral

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11Wave6

/-! ### 11.r33: the ring $\mathbb Z^{[p]} = \mathbb Z[1/p]$ -/

section InvP

variable (p : ℕ) [Fact p.Prime]

/-- Helper: $p$ becomes a unit in $\mathbb Q$ under `Int.castRingHom ℚ` on the powers of $p$ (the hypothesis of
`IsLocalization.lift` used to define `invPSubring`). -/
theorem isUnit_cast_powers : ∀ y : Submonoid.powers (p : ℤ), IsUnit ((Int.castRingHom ℚ) (y : ℤ)) := by
  rintro ⟨y, k, rfl⟩
  simp only [eq_intCast, map_pow, Int.cast_natCast]
  exact IsUnit.mk0 _ (pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero))

/-- **The ring $\mathbb Z^{[p]} = \mathbb Z[1/p]$** (Cassels, Ch. 11, p. 232): the subring of $\mathbb Q$ consisting of
the rationals whose only denominators are powers of $p$. It is the image in $\mathbb Q$ of Mathlib's localization
`Localization.Away (p : ℤ)` of $\mathbb Z$ at the powers of $p$, under the unique ring homomorphism extending the
inclusion $\mathbb Z \to \mathbb Q$. Argument `p`: a prime number. -/
@[kb "cassels1978" "Ch. 11, p. 232 (notation Z^[p] = Z[1/p])"]
def invPSubring : Subring ℚ :=
  (IsLocalization.lift (M := Submonoid.powers (p : ℤ)) (S := Localization.Away (p : ℤ))
    (g := Int.castRingHom ℚ) (isUnit_cast_powers p)).range

/-- **$\mathbb Z[1/p]$ is the set of $z/p^k$:** a rational $q$ lies in `invPSubring p` iff $q = z/p^k$ for some integer
$z$ and natural number $k$. Arguments: `p` the prime, `q` the rational. -/
theorem mem_invPSubring_iff (q : ℚ) : q ∈ invPSubring p ↔ ∃ (z : ℤ) (k : ℕ), q = z / (p : ℚ) ^ k := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨⟨z, ⟨m, ⟨k, rfl⟩⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (p : ℤ)) x
    refine ⟨z, k, ?_⟩
    have h2 := congrArg (IsLocalization.lift (M := Submonoid.powers (p : ℤ)) (S := Localization.Away (p : ℤ))
      (g := Int.castRingHom ℚ) (isUnit_cast_powers p)) h
    simp only [map_mul, IsLocalization.lift_eq] at h2
    simp at h2
    rw [eq_div_iff (pow_ne_zero _ hp0)]
    exact h2
  · rintro ⟨z, k, rfl⟩
    refine ⟨IsLocalization.mk' (Localization.Away (p : ℤ)) z
      ⟨(p : ℤ) ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers _) k⟩, ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    simp
    field_simp

/-- Helper: a prime $\ell$ dividing the denominator of a rational $q$ (in lowest terms) gives $\operatorname{ord}_\ell q < 0$.
Arguments: `ℓ` the prime, `q` the rational, `hdvd` the divisibility of the denominator. -/
theorem padicValRat_neg_of_dvd_den (ℓ : ℕ) [Fact ℓ.Prime] (q : ℚ) (hdvd : ℓ ∣ q.den) : padicValRat ℓ q < 0 := by
  have hℓ := (Fact.out : ℓ.Prime)
  rw [padicValRat_def]
  have hcop : ¬ ℓ ∣ q.num.natAbs := fun hd =>
    (Nat.Prime.not_dvd_one hℓ) (by
      have := Nat.dvd_gcd hd hdvd
      rwa [q.reduced] at this)
  have hn : padicValInt ℓ q.num = 0 := by
    unfold padicValInt; exact padicValNat.eq_zero_of_not_dvd hcop
  have hd : 0 < padicValNat ℓ q.den := one_le_padicValNat_of_dvd q.den_nz hdvd
  rw [hn]
  omega

/-- **Characterization by $\ell$-adic valuations** (Cassels, Ch. 11, p. 232: "$\lvert a\rvert_v \le 1$ for all
$v \ne p, \infty$"): a rational $q$ lies in $\mathbb Z[1/p]$ iff `padicValRat ℓ q ≥ 0` for every prime $\ell \ne p$.
(`padicValRat ℓ 0 = 0`, so $q = 0$ is allowed.) Arguments: `p` the prime, `q` the rational. -/
@[kb "cassels1978" "Ch. 11, p. 232 (Z^[p]: valuations at v ≠ p, ∞)"]
theorem mem_invPSubring_iff_padicValRat (q : ℚ) :
    q ∈ invPSubring p ↔ ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → 0 ≤ padicValRat ℓ q := by
  have hp := (Fact.out : p.Prime)
  rw [mem_invPSubring_iff]
  constructor
  · rintro ⟨z, k, rfl⟩ ℓ hℓ hne
    have : Fact ℓ.Prime := ⟨hℓ⟩
    by_cases hz : z = 0
    · simp [hz]
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [padicValRat.div (by exact_mod_cast hz) (pow_ne_zero _ hp0), padicValRat.pow (p : ℚ)]
    have : padicValRat ℓ (p : ℚ) = 0 := by
      rw [padicValRat.of_nat]
      have : ¬ ℓ ∣ p := fun h => hne ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h)
      simp [padicValNat.eq_zero_of_not_dvd this]
    rw [this]
    simp [padicValRat.of_int]
  · intro h
    by_cases hq : q = 0
    · exact ⟨0, 0, by simp [hq]⟩
    have hden : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ q.den → ℓ = p := by
      intro ℓ hℓ hdvd
      by_contra hne
      have : Fact ℓ.Prime := ⟨hℓ⟩
      exact absurd (h ℓ hℓ hne) (not_le.2 (padicValRat_neg_of_dvd_den ℓ q hdvd))
    obtain ⟨k, hk⟩ : ∃ k, q.den = p ^ k := by
      by_cases h1 : q.den = 1
      · exact ⟨0, by simp [h1]⟩
      · obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd h1
        have := hden ℓ hℓ hdvd
        subst this
        exact (Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz (fun {d} hd hdd => hden d hd hdd)) |> fun h => ⟨_, h⟩
    refine ⟨q.num, k, ?_⟩
    rw [← Nat.cast_pow, ← hk]
    exact (Rat.num_div_den q).symm

/-- Helper: $\lvert q\rvert_\ell \le 1$ iff $\operatorname{ord}_\ell q \ge 0$ for a rational $q$ and prime $\ell$. -/
theorem padicNorm_le_one_iff (ℓ : ℕ) [Fact ℓ.Prime] (q : ℚ) : padicNorm ℓ q ≤ 1 ↔ 0 ≤ padicValRat ℓ q := by
  by_cases hq : q = 0
  · simp [hq]
  rw [padicNorm.eq_zpow_of_nonzero hq]
  have hℓ : (1 : ℚ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  rw [zpow_le_one_iff_right₀ hℓ]
  exact neg_nonpos

/-- **Characterization by $\ell$-adic absolute values** (Cassels, Ch. 11, p. 232): a rational $q$ lies in
$\mathbb Z[1/p]$ iff $\lvert q\rvert_\ell \le 1$ (`padicNorm`) for every prime $\ell \ne p$. The archimedean absolute
value is not constrained. Arguments: `p` the prime, `q` the rational. -/
@[kb "cassels1978" "Ch. 11, p. 232 (Z^[p]: |a|_v ≤ 1 for v ≠ p, ∞)"]
theorem mem_invPSubring_iff_padicNorm (q : ℚ) :
    q ∈ invPSubring p ↔ ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → padicNorm ℓ q ≤ 1 := by
  rw [mem_invPSubring_iff_padicValRat]
  refine forall_congr' fun ℓ => forall_congr' fun hℓ => forall_congr' fun _ => ?_
  have : Fact ℓ.Prime := ⟨hℓ⟩
  exact (padicNorm_le_one_iff ℓ q).symm

/-- Helper: a rational with $\lvert q\rvert_\ell \le 1$ for every prime $\ell$ is an integer. Argument `q`: the rational. -/
theorem exists_int_of_forall_padicNorm_le_one (q : ℚ) (h : ∀ ℓ : ℕ, ℓ.Prime → padicNorm ℓ q ≤ 1) :
    ∃ z : ℤ, q = z := by
  have hden : q.den = 1 := by
    by_contra h1
    obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd h1
    have : Fact ℓ.Prime := ⟨hℓ⟩
    exact absurd ((padicNorm_le_one_iff ℓ q).1 (h ℓ hℓ)) (not_le.2 (padicValRat_neg_of_dvd_den ℓ q hdvd))
  exact ⟨q.num, (Rat.den_eq_one_iff q).1 hden |>.symm⟩

end InvP

/-! ### 11.r34: scaling and the choice of integrality (p. 235) -/

section Scaling

variable {n : ℕ}

/-- **Scaling preserves primitive representation over $\mathbb Z$.** For an integer $c \ne 0$, the form $cQ$
primitively represents $ca$ over $\mathbb Z$ iff $Q$ primitively represents $a$. Arguments: `c` the scalar, `hc` its
non-vanishing, `Q` the form, `a` the represented integer. -/
theorem primRepZ_smul_iff {c : ℤ} (hc : c ≠ 0) (Q : QuadForm ℤ n) (a : ℤ) :
    PrimRepZ (c • Q) (c * a) ↔ PrimRepZ Q a := by
  unfold PrimRepZ
  simp only [Binary.eval_smul, mul_right_inj' hc]

/-- **Scaling preserves primitive representation over $\mathbb Z_p$.** For an integer $c \ne 0$, the form $cQ$
primitively represents $ca$ over $\mathbb Z_p$ iff $Q$ primitively represents $a$. Arguments: `p` the prime, `c` the
scalar, `hc` its non-vanishing, `Q` the form, `a` the represented integer. -/
theorem primRepZp_smul_iff (p : ℕ) [Fact p.Prime] {c : ℤ} (hc : c ≠ 0) (Q : QuadForm ℤ n) (a : ℤ) :
    PrimRepZp p (c • Q) (c * a) ↔ PrimRepZp p Q a := by
  unfold PrimRepZp
  have hc' : (c : ℤ_[p]) ≠ 0 := by exact_mod_cast hc
  simp only [Binary.evalIn_smul, Int.cast_mul, mul_right_inj' hc']

/-- **Helper: a number represented over every $\mathbb Z_\ell$ by $cQ$ is divisible by $c$.** If, for every prime
$\ell$, $a = cQ(x_\ell)$ with $x_\ell \in \mathbb Z_\ell^n$, then $c \mid a$ (for $c \ne 0$): $a/c$ has
$\ell$-adic absolute value at most $1$ for every $\ell$. Arguments: `c` the scalar, `hc` its non-vanishing, `Q` the
form, `a` the integer, `h` the local representations by $cQ$ (primitive or not; only the equation is used). -/
theorem dvd_of_primRepZp_smul {c : ℤ} (hc : c ≠ 0) (Q : QuadForm ℤ n) (a : ℤ)
    (h : ∀ (p : ℕ) [Fact p.Prime], PrimRepZp p (c • Q) a) : c ∣ a := by
  have key : ∀ ℓ : ℕ, ℓ.Prime → padicNorm ℓ ((a : ℚ) / c) ≤ 1 := by
    intro ℓ hℓ
    have : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨x, -, hx⟩ := h ℓ
    rw [Binary.evalIn_smul] at hx
    have e : ∀ z : ℤ, ‖(z : ℤ_[ℓ])‖ = padicNorm ℓ (z : ℚ) := fun z => by
      rw [PadicInt.norm_intCast_eq_padic_norm]
      simpa using Padic.eq_padicNorm (p := ℓ) (z : ℚ)
    have hn : padicNorm ℓ (a : ℚ) ≤ padicNorm ℓ (c : ℚ) := by
      have h1 : ‖(a : ℤ_[ℓ])‖ ≤ ‖(c : ℤ_[ℓ])‖ := by
        rw [← hx, norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
      rw [e, e] at h1
      exact_mod_cast h1
    rw [padicNorm.div]
    have hc0 : 0 < padicNorm ℓ (c : ℚ) := by
      exact lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.nonzero (by exact_mod_cast hc)))
    rw [div_le_one hc0]
    exact hn
  obtain ⟨z, hz⟩ := exists_int_of_forall_padicNorm_le_one _ key
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  refine ⟨z, ?_⟩
  have : (a : ℚ) = c * z := by rw [← hz]; field_simp
  exact_mod_cast this

/-- **The constant of Theorem 1.6 scales: $N(cQ) = cN(Q)$** (Cassels, Ch. 11, p. 235). If $N$ is a constant as in
Theorem 1.6 for $Q$ (every integer $a \ge N$ primitively represented by $Q$ over all $\mathbb Z_p$ is primitively
represented over $\mathbb Z$) and $c > 0$, then $cN$ is such a constant for $cQ$. Arguments: `c` the positive scalar,
`Q` the form, `N` the constant for $Q$, `hN` its defining property. -/
@[kb "cassels1978" "Ch. 11, p. 235 (N(cf) = cN(f))"]
theorem tartakowskyConstant_smul {c : ℤ} (hc : 0 < c) (Q : QuadForm ℤ n) {N : ℤ}
    (hN : ∀ a : ℤ, N ≤ a → (∀ (p : ℕ) [Fact p.Prime], PrimRepZp p Q a) → PrimRepZ Q a) :
    ∀ a : ℤ, c * N ≤ a → (∀ (p : ℕ) [Fact p.Prime], PrimRepZp p (c • Q) a) → PrimRepZ (c • Q) a := by
  intro a ha hloc
  obtain ⟨b, rfl⟩ := dvd_of_primRepZp_smul hc.ne' Q a hloc
  have hb : N ≤ b := le_of_mul_le_mul_left ha hc
  exact (primRepZ_smul_iff hc.ne' Q b).2 (hN b hb fun p _ => (primRepZp_smul_iff p hc.ne' Q b).1 (hloc p))

/-- Helper: scaling by a positive integer preserves positive definiteness. Arguments: `c` the positive scalar, `Q` the
positive definite form. -/
theorem posDef_smul {c : ℤ} (hc : 0 < c) {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) : IntQF.PosDef (c • Q) := by
  intro x hx
  rw [Binary.eval_smul]
  exact mul_pos hc (hQ x hx)

/-- **Classical integrality versus integer-valuedness does not matter for Theorem 1.6** (Cassels, Ch. 11, p. 235:
"since we can take $N(cf) = cN(f)$ for any integer $c > 0$"): Theorem 1.6 in $n$ variables for classically integral
positive definite forms is equivalent to Theorem 1.6 in $n$ variables for integer-valued positive definite forms.
The direction from integer-valued to classical is `TartakowskyAt.classical`; for the converse apply the classical
statement to $2Q$ (always classically integral, `two_smul_isClassicallyIntegral`) and rescale. Argument `n`: the number
of variables. -/
@[kb "cassels1978" "Ch. 11, p. 235 (classical integrality vs integer-valued does not matter)"]
theorem tartakowskyClassicalAt_iff (n : ℕ) : TartakowskyClassicalAt n ↔ TartakowskyAt n := by
  refine ⟨fun hcl Q hQ => ?_, fun h => h.classical⟩
  obtain ⟨N', hN'⟩ := hcl ((2 : ℤ) • Q) (posDef_smul (by norm_num) hQ) (two_smul_isClassicallyIntegral Q)
  refine ⟨max N' 0, fun a ha hloc => ?_⟩
  have ha0 : 0 ≤ a := (le_max_right _ _).trans ha
  have ha' : N' ≤ a := (le_max_left _ _).trans ha
  have h2 := hN' (2 * a) (by omega) fun p _ => (primRepZp_smul_iff p (by norm_num) Q a).2 (hloc p)
  exact (primRepZ_smul_iff (by norm_num) Q a).1 h2

end Scaling

/-! ### 11.r37: every integer is primitively represented away from $P$ (p. 236) -/

section OutsideP

open QuadFormsKB.Siegel.Kneser

variable {p : ℕ} [hp : Fact p.Prime]

/-- Helper: a binary unit form over $\mathbb Z_p$ ($p$ odd) represents every $p$-adic unit. For units $a, b$ and a unit
$T$ there are $x, y \in \mathbb Z_p$ with $ax^2 + by^2 = T$ (a solution modulo $p$ from the binary count of Table 1,
lifted by Hensel's lemma; the case $T = 1$ is `Siegel.Kneser.exists_binary_one`). -/
theorem exists_binary_unit (hp2 : p ≠ 2) {a b : ℤ_[p]} (ha : IsUnit a) (hb : IsUnit b) {T : ℤ_[p]}
    (hT : IsUnit T) : ∃ x y : ℤ_[p], a * x ^ 2 + b * y ^ 2 = T := by
  set A := PadicInt.toZMod a with hAd
  set B := PadicInt.toZMod b with hBd
  set T' := PadicInt.toZMod T with hTd
  have hA : A ≠ 0 := toZMod_ne_zero_of_isUnit ha
  have hB : B ≠ 0 := toZMod_ne_zero_of_isUnit hb
  have hT0 : T' ≠ 0 := toZMod_ne_zero_of_isUnit hT
  have hcount := LocalDensity.binary_count_modP hp2 A B hA hB T'
  obtain ⟨s, t, hst⟩ : ∃ s t : ZMod p, A * s ^ 2 + B * t ^ 2 = T' := by
    by_contra h
    push Not at h
    have : (∑ y : ZMod p, ∑ z : ZMod p, (if A * y ^ 2 + B * z ^ 2 = T' then 1 else 0 : ℤ)) = 0 :=
      Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun z _ => by simp [h y z]
    rw [this] at hcount
    simp only [hT0, ite_false, mul_zero, add_zero] at hcount
    have hχ : quadraticChar (ZMod p) (-(A * B)) ≤ 1 := by
      rcases quadraticChar_dichotomy (F := ZMod p)
        (neg_ne_zero.mpr (mul_ne_zero hA hB)) with h | h <;> simp [h]
    have := hp.out.two_le
    have : (2 : ℤ) ≤ p := by exact_mod_cast this
    linarith
  have hinv : ∀ {u : ℤ_[p]} (hu : IsUnit u), PadicInt.toZMod (↑hu.unit⁻¹ : ℤ_[p]) = (PadicInt.toZMod u)⁻¹ := by
    intro u hu
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  by_cases hs : s = 0
  · subst hs
    have hBt : B * t ^ 2 = T' := by simpa using hst
    have ht : t ≠ 0 := by rintro rfl; simp at hBt; exact hT0 hBt.symm
    obtain ⟨y, hy⟩ := exists_sq_eq_of_toZMod hp2 (↑hb.unit⁻¹ * T : ℤ_[p]) ht (by
      rw [map_mul, hinv hb, ← hBd, ← hTd]
      rw [← hBt]; field_simp)
    refine ⟨0, y, ?_⟩
    rw [hy]
    simp only [zero_pow two_ne_zero, mul_zero, zero_add]
    rw [← mul_assoc, mul_comm b, IsUnit.val_inv_mul hb, one_mul]
  · set y : ℤ_[p] := (t.val : ℤ_[p])
    have hy : PadicInt.toZMod y = t := by simp [y]
    obtain ⟨x, hx⟩ := exists_sq_eq_of_toZMod hp2 ((T - b * y ^ 2) * ↑ha.unit⁻¹) hs (by
      rw [map_mul, map_sub, map_mul, map_pow, hy, hinv ha, ← hAd, ← hBd, ← hTd,
        show T' - B * t ^ 2 = A * s ^ 2 by linear_combination -hst]
      field_simp)
    refine ⟨x, y, ?_⟩
    rw [hx, mul_comm, mul_assoc, IsUnit.val_inv_mul, mul_one]; ring

/-- Helper: a unit diagonal form in at least three variables over $\mathbb Z_p$ ($p$ odd) primitively represents every
$p$-adic integer $m$. If $m$ is a unit, use two coordinates (`exists_binary_unit`); otherwise set the third coordinate
to $1$ and represent the unit $m - a_2$ with the first two. Arguments: `a` the unit diagonal coefficients
($k + 3$ of them), `ha` their unit property, `m` the represented element. -/
theorem exists_diag_primRep (hp2 : p ≠ 2) {k : ℕ} (a : Fin (k + 3) → ℤ_[p]) (ha : ∀ i, IsUnit (a i))
    (m : ℤ_[p]) : ∃ y : Fin (k + 3) → ℤ_[p], (∃ i, IsUnit (y i)) ∧ (QuadForm.diag a).eval y = m := by
  have key : ∀ x y z : ℤ_[p], (QuadForm.diag a).eval (Fin.cons x (Fin.cons y (Fin.cons z (fun _ => 0))) :
      Fin (k + 3) → ℤ_[p]) = a 0 * x ^ 2 + a 1 * y ^ 2 + a 2 * z ^ 2 := by
    intro x y z
    rw [eval_diag]
    simp [Fin.sum_univ_succ]
    ring
  by_cases hm : IsUnit m
  · obtain ⟨x, y, hxy⟩ := exists_binary_unit hp2 (ha 0) (ha 1) hm
    refine ⟨Fin.cons x (Fin.cons y (Fin.cons 0 (fun _ => 0))), ?_, by rw [key]; simpa using hxy⟩
    by_contra hcon
    push Not at hcon
    have hx := hcon 0
    have hy := hcon 1
    simp at hx hy
    have h1 : a 0 * x ^ 2 + a 1 * y ^ 2 ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
      add_mem (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hx 2 (by norm_num)))
        (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hy 2 (by norm_num)))
    rw [hxy] at h1
    exact (IsLocalRing.mem_maximalIdeal _).1 h1 hm
  · have hT : IsUnit (m - a 2) := by
      by_contra hT
      have h1 : m ∈ IsLocalRing.maximalIdeal ℤ_[p] := hm
      have h2 : m - a 2 ∈ IsLocalRing.maximalIdeal ℤ_[p] := hT
      have : a 2 ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
        have := sub_mem h1 h2
        simpa using this
      exact (IsLocalRing.mem_maximalIdeal _).1 this (ha 2)
    obtain ⟨x, y, hxy⟩ := exists_binary_unit hp2 (ha 0) (ha 1) hT
    refine ⟨Fin.cons x (Fin.cons y (Fin.cons 1 (fun _ => 0))), ⟨Fin.succ (Fin.succ 0),
      by rw [Fin.cons_succ, Fin.cons_succ, Fin.cons_zero]; exact isUnit_one⟩, ?_⟩
    rw [key]
    linear_combination hxy

/-- **Every integer is primitively represented over $\mathbb Z_p$ at a prime of good reduction** (Cassels, Ch. 11,
p. 236: "any $a \in \mathbb Z$ is represented primitively over $\mathbb Z_p$ for all $p \notin P$"). Let $p$ be an odd
prime not dividing $\det H$ ($H$ the Hessian of $Q$, `QuadForm.hessian`; for odd $p$ this is $p \nmid d$ for Cassels'
determinant $d = \det H/2^n$) and $Q$ an integer-valued form in $n \ge 3$ variables. Then every integer $a$ is
represented by $Q$ over $\mathbb Z_p$ by a vector with a $p$-adic unit coordinate. *Proof:* $Q$ is
$\mathrm{GL}_n(\mathbb Z_p)$-equivalent to a unit diagonal form (`DVR.exists_diag_of_unimodular`), which primitively
represents everything (`exists_diag_primRep`), and $\mathrm{GL}_n(\mathbb Z_p)$ preserves "some coordinate is a unit"
(`Cassels.exists_unit_mulVec`). *Update:* Cassels states this in the context of Theorem 1.6 ($n \ge 4$); the proof needs
only $n \ge 3$, and the statement is false for $n = 2$ (the form $x_0^2 + x_1^2$ does not represent $3$ over $\mathbb Z_3$).
Arguments: `hp2` the oddness of $p$, `hn` the bound $n \ge 3$, `Q` the form, `hdet` the non-divisibility, `a` the
integer. -/
@[kb "cassels1978" "Ch. 11, p. 236 (every a primitively represented over Z_p for p not in P)"]
theorem primRepZp_of_not_dvd_hessian_det (hp2 : p ≠ 2) {n : ℕ} (hn : 3 ≤ n) (Q : QuadForm ℤ n)
    (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (a : ℤ) : PrimRepZp p Q a := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  set Q' := Q.map (Int.castRingHom ℤ_[p]) with hQ'
  have hdet' : ¬ (p : ℤ_[p]) ∣ Q'.hessian.det := by
    have hh : Q'.hessian = Q.hessian.map (Int.castRingHom ℤ_[p]) := by
      ext i j; simp [hQ', QuadForm.hessian, QuadForm.map, Matrix.map_apply]
    have hd : (Q.hessian.map (Int.castRingHom ℤ_[p])).det = ((Q.hessian.det : ℤ) : ℤ_[p]) :=
      (RingHom.map_det (Int.castRingHom ℤ_[p]) Q.hessian).symm
    rw [hh, hd]
    intro h
    apply hdet
    have h1 : ((p : ℤ) : ℤ_[p]) ^ 1 ∣ ((Q.hessian.det : ℤ) : ℤ_[p]) := by simpa using h
    simpa using (LocalDensity.padic_pow_dvd_int_iff p 1 _).1 h1
  have hπ : Irreducible (p : ℤ_[p]) := PadicInt.irreducible_p
  obtain ⟨b, hb, hE, -⟩ := LocalDensity.DVR.exists_diag_of_unimodular Q' _ hπ (not_p_dvd_two hp2) hdet'
  have hbU : ∀ i, IsUnit (b i) := fun i => LocalDensity.DVR.isUnit_of_not_dvd _ hπ _ (hb i)
  obtain ⟨y, hy, hyv⟩ := exists_diag_primRep hp2 b hbU (a : ℤ_[p])
  obtain ⟨U, hU, hUQ⟩ := hE
  refine ⟨U *ᵥ y, exists_unit_mulVec p (M := U) (N := U⁻¹) (Matrix.nonsing_inv_mul U hU) hy, ?_⟩
  rw [← LocalDensity.evalIn_map_intCast ℤ_[p] Q, ← hQ']
  exact (hUQ y).symm.trans hyv

/-- **The set $P$ of Cassels' proof of Theorem 1.6** (Ch. 11, p. 236): let $P$ be a set of primes with $2 \in P$ and
containing every prime dividing the determinant of $Q$ (here $\det H$, the Hessian determinant; for odd primes this is
Cassels' $d$, see the module docstring). Then for every prime $p \notin P$ and every integer $a$, $a$ is primitively
represented by $Q$ over $\mathbb Z_p$, so the hypotheses of Theorem 1.6 only constrain the primes in $P$. Needs
$n \ge 3$ (Cassels: $n \ge 4$). Arguments: `P` the set of primes, `h2` its contains $2$, `hP` its contains the primes
dividing the determinant, `hn` the bound on $n$, `Q` the form, `p` a prime outside $P$, `a` the integer. -/
@[kb "cassels1978" "Ch. 11, p. 236 (set P of primes; only p in P matter)"]
theorem primRepZp_of_notMem (P : Set ℕ) (h2 : 2 ∈ P) {n : ℕ} (hn : 3 ≤ n) (Q : QuadForm ℤ n)
    (hP : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ Q.hessian.det → q ∈ P) (p : ℕ) [Fact p.Prime] (hpP : p ∉ P) (a : ℤ) :
    PrimRepZp p Q a :=
  primRepZp_of_not_dvd_hessian_det (fun h => hpP (by rw [h]; exact h2)) hn Q (fun hd => hpP (hP p (Fact.out) hd)) a

end OutsideP

/-! ### 11.r14: the conditions (i), (ii) of Theorem 1.3 are not sufficient (p. 202) -/

section NotSufficient

open QuadFormsKB.Lattices

/-- Helper: the Hessian of a diagonal form $\langle a_0, \dots, a_{n-1}\rangle$ is the diagonal matrix with entries
$2a_i$. Argument `a`: the diagonal coefficients. -/
theorem hessian_diag {n : ℕ} (a : Fin n → ℤ) :
    (QuadForm.diag a).hessian = Matrix.diagonal fun i => 2 * a i := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [QuadForm.hessian, QuadForm.diag]
    ring
  · simp [QuadForm.hessian, QuadForm.diag, h]

/-- Helper: the Hessian determinant of $\langle 1, 1, c\rangle$ is $8c$. Argument `c`: the third coefficient. -/
theorem hessian_det_diag_one_one (c : ℤ) : (QuadForm.diag ![1, 1, c]).hessian.det = 8 * c := by
  rw [hessian_diag, Matrix.det_diagonal, Fin.prod_univ_three]
  simp
  ring

/-- Helper (Cassels, Lemma 3.8, Corollary, at $p = 2$, as in the proof of Theorem 1.3, p. 215): if the integer-valued
form $f$ does not satisfy "classically integral and $2^{n(n-3)/2 + [(n+1)/2]} \mid d$" (the negation of (ii), stated for
$\det H = 2^n d$), then $U_2 \subseteq \theta(\Lambda_2)$ for $\Lambda = \mathbb Z^n$. This is the dyadic half of
`units_mem_localSpinorNormGroup_of_det`, which asks for the negation of (i) at *all* odd primes as well; the odd
primes are handled separately in the example below. Arguments: `f` the form, `hQ` its non-degeneracy, `hii` the
negation of (ii), `v` a prime of $\mathbb Q$ above $2$ (`h2`), `u` a unit of the completion (`hu`: of valuation $1$). -/
theorem units_mem_localSpinorNormGroup_two {n : ℕ} (f : QuadForm ℤ n)
    (hQ : (f.map (Int.castRingHom ℚ)).Nondegenerate)
    (hii : ¬ (IsClassicallyIntegral f ∧ (2 : ℤ) ^ (casselsExpTwo n + n).toNat ∣ f.hessian.det))
    (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (u : (v.adicCompletion ℚ)ˣ) (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    u ∈ localSpinorNormGroup (f.map (Int.castRingHom ℚ)) hQ v stdLat := by
  set Q := f.map (Int.castRingHom ℚ) with hQdef
  have hL : loc v (stdLat : Lat ℚ n).1 = std v := loc_intVec v
  have hγ : loc v (stdLat : Lat ℚ n).1 = locAct v (1 : GL (Fin n) (v.adicCompletion ℚ)) (std v) := by
    rw [locAct_one]; exact hL
  have hint : ∀ x ∈ loc v (stdLat : Lat ℚ n).1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1 := by
    intro x hx; rw [hL] at hx; exact valued_evalIn_le_one_int v f hx
  revert u hu
  by_contra hnot
  have hp2 := (two_mem_iff_natGenerator v).mp h2
  have hv2 := valued_two_dyadic v h2
  apply hii
  refine ⟨?_, ?_⟩
  · have hci := classicallyIntegral_of_not_units_mem_two Q hQ h2 stdLat hint hnot
    have hmem : ∀ i, (Pi.single i 1 : Fin n → v.adicCompletion ℚ) ∈ loc v (stdLat : Lat ℚ n).1 :=
      fun i => by rw [hL]; exact single_mem_std i (by simp)
    have hG : ∀ i j, Valued.v (locGram Q v 1 i j) ≤ Valued.v (2 : v.adicCompletion ℚ) := fun i j => by
      have := hci _ (hmem i) _ (hmem j)
      rw [← locGram_apply_eq]
      simp only [Units.val_one, Matrix.one_mulVec]
      convert this using 3
      exact Subsingleton.elim _ _
    rw [isClassicallyIntegral_iff]
    intro i j hij
    have h := hG i j
    rw [locGram_one_int, hv2, show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, valued_intCast_le_iff, hp2] at h
    have hH : f.hessian i j = f.coeff i j := by
      simp [QuadForm.hessian, f.upper hij]
    rw [hH] at h
    exact even_iff_two_dvd.mpr (by simpa using h)
  · have hd := valued_det_le_of_not_units_mem_two Q hQ h2 stdLat hint hnot 1 hγ
    have hT : 0 ≤ casselsExpTwo n + n := by rw [casselsExpTwo_eq]; positivity
    rw [locGram_one_int_det, ← Int.toNat_of_nonneg hT, valued_intCast_le_iff, hp2] at hd
    exact_mod_cast hd

/-- **Helper: units are spinor norms at an odd prime for $\langle 1, 1, c\rangle$** (Cassels, Lemma 3.7 and the remark
before it, p. 213): for the lattice $\mathbb Z^3$ with the form $x_0^2 + x_1^2 + cx_2^2$ and an odd prime $v$ of
$\mathbb Q$, every unit of the completion lies in $\theta(\Lambda_v)$, because the standard basis is orthogonal and
$x_0, x_1$ have the same norm. Arguments: `c` the third coefficient, `hQ` non-degeneracy, `v` the prime (`h2`: not above
$2$), `u` a unit of the completion (`hu`: valuation $1$). -/
theorem units_mem_localSpinorNormGroup_odd_diag (c : ℤ)
    (hQ : ((QuadForm.diag ![1, 1, c]).map (Int.castRingHom ℚ)).Nondegenerate)
    (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal)
    (u : (v.adicCompletion ℚ)ˣ) (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    u ∈ localSpinorNormGroup ((QuadForm.diag ![1, 1, c]).map (Int.castRingHom ℚ)) hQ v stdLat := by
  have hγ : loc v (stdLat : Lat ℚ 3).1 = locAct v (1 : GL (Fin 3) (v.adicCompletion ℚ)) (std v) := by
    rw [locAct_one]; exact loc_intVec v
  refine units_mem_localSpinorNormGroup_of_orthogonal _ v hQ h2 stdLat 1 hγ ?_ (i := 0) (j := 1)
    (by decide) ?_ u hu
  · intro k l hkl
    rw [locGram_one_int, hessian_diag, Matrix.diagonal_apply_ne _ hkl]
    simp
  · rw [locGram_one_int, locGram_one_int, hessian_diag]
    simp

/-- Helper: if $U_v \subseteq \theta(\Lambda_v)$ at every prime $v$ of $\mathbb Q$ for $\Lambda = \mathbb Z^n$ ($n \ge 3$), then
the genus of $\Lambda$ is a single proper spinor genus (Lemma 3.6, Corollary: `sameProperSpinorGenus_of_sameGenus_rat`).
Arguments: `Q` the non-degenerate rational form, `hQ` non-degeneracy, `hn` the bound $n \ge 3$, `hloc` the local
statement at every prime. -/
theorem properSpinorGenusNumber_eq_one_of_units {n : ℕ} {Q : QuadForm ℚ n} (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (hloc : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ), Valued.v (u : v.adicCompletion ℚ) = 1 →
      u ∈ localSpinorNormGroup Q hQ v (stdLat : Lat ℚ n)) :
    properSpinorGenusNumber Q (stdLat : Lat ℚ n) = 1 := by
  have hset : genusProperSpinorGenera Q (stdLat : Lat ℚ n) = {Quotient.mk (properSpnSetoid Q) stdLat} := by
    ext x
    constructor
    · rintro ⟨M, rfl, hM⟩
      exact Quotient.sound (SameProperSpinorGenus.symm Q
        (sameProperSpinorGenus_of_sameGenus_rat Q hQ hn stdLat hloc hM))
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨stdLat, rfl, QuadFormsKB.Lattices.SameGenus.refl Q _⟩
  show (genusProperSpinorGenera Q (stdLat : Lat ℚ n)).ncard = 1
  rw [hset, Set.ncard_singleton]

/-- **A genus with one proper spinor genus although (i) holds** (Cassels, Ch. 11, remark after Theorem 1.3, p. 202):
for an odd integer $c$, the lattice $\mathbb Z^3$ with the integer-valued form $x_0^2 + x_1^2 + cx_2^2$ has a genus
consisting of exactly one proper spinor genus. For $c = 27$ condition (i) of Theorem 1.3 holds (`p = 3`, $3^{3} \mid 27$)
even though there is only one spinor genus (`not_sufficient_theorem13`). *Proof:* by the Corollary to Lemma 3.6
(`sameProperSpinorGenus_of_sameGenus_rat`) it suffices that $U_v \subseteq \theta(\Lambda_v)$ at every prime $v$:
at odd $v$ by `units_mem_localSpinorNormGroup_odd_diag` (Lemma 3.7), at $v = 2$ by
`units_mem_localSpinorNormGroup_two` (Lemma 3.8 Corollary), whose hypothesis holds since $\det H = 8c$ with $c$ odd
and $2^{n(n-3)/2 + [(n+1)/2] + n} = 2^5 \nmid 8c$. Argument `hc`: the oddness of $c$. -/
@[kb "cassels1978" "Ch. 11, p. 202 (remark: (i), (ii) of Thm. 1.3 not sufficient); Lemma 3.6, Cor."]
theorem properSpinorGenusNumber_diag_one_one_odd {c : ℤ} (hc : Odd c) :
    properSpinorGenusNumber ((QuadForm.diag ![1, 1, c]).map (Int.castRingHom ℚ)) (stdLat : Lat ℚ 3) = 1 := by
  set f : QuadForm ℤ 3 := QuadForm.diag ![1, 1, c] with hf
  have hdet : f.hessian.det = 8 * c := hessian_det_diag_one_one c
  have h8 : (8 * c : ℤ) ≠ 0 := by obtain ⟨m, rfl⟩ := hc; omega
  have hh : (f.map (Int.castRingHom ℚ)).hessian = f.hessian.map (Int.castRingHom ℚ) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map, Matrix.map_apply]
  have hQ : (f.map (Int.castRingHom ℚ)).Nondegenerate := by
    unfold QuadForm.Nondegenerate
    rw [hh, show (f.hessian.map (Int.castRingHom ℚ)).det = ((f.hessian.det : ℤ) : ℚ) from
      (RingHom.map_det (Int.castRingHom ℚ) f.hessian).symm, hdet]
    exact_mod_cast h8
  have hii : ¬ (IsClassicallyIntegral f ∧ (2 : ℤ) ^ (casselsExpTwo 3 + 3).toNat ∣ f.hessian.det) := by
    rintro ⟨-, hd⟩
    have h5 : (casselsExpTwo 3 + 3).toNat = 5 := by
      unfold casselsExpTwo
      norm_num
    rw [h5, hdet] at hd
    obtain ⟨m, rfl⟩ := hc
    norm_num at hd
    omega
  have hloc : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ), Valued.v (u : v.adicCompletion ℚ) = 1 →
      u ∈ localSpinorNormGroup (f.map (Int.castRingHom ℚ)) hQ v (stdLat : Lat ℚ 3) := by
    intro v u hu
    by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
    · exact units_mem_localSpinorNormGroup_two f hQ hii v h2 u hu
    · exact units_mem_localSpinorNormGroup_odd_diag c hQ v h2 u hu
  exact properSpinorGenusNumber_eq_one_of_units hQ le_rfl hloc

/-- **Conditions (i), (ii) of Theorem 1.3 are not sufficient for more than one spinor genus** (Cassels, Ch. 11, p. 202:
"Note that the conditions (i), (ii) are not in general sufficient for the genus to contain more than one spinor genus").
Explicit example: the integer-valued form $f = x_0^2 + x_1^2 + 27x_2^2$ in $n = 3$ variables (lattice $\mathbb Z^3$) is
non-degenerate and satisfies condition (i) of Theorem 1.3 (with $p = 3$: $p^{n(n-1)/2} = 27$ divides $\det H = 216 = 2^3 d$,
$d = 27$), yet the genus of $\mathbb Z^3$ contains exactly one proper spinor genus (`properSpinorGenusNumber_diag_one_one_odd`).
The conclusion of Theorem 1.3 (`exists_dvd_det_of_one_lt_properSpinorGenusNumber`) is therefore necessary but not
sufficient. -/
@[kb "cassels1978" "Ch. 11, p. 202 (remark after Thm. 1.3: (i), (ii) not sufficient)"]
theorem not_sufficient_theorem13 :
    ∃ f : QuadForm ℤ 3, (f.map (Int.castRingHom ℚ)).Nondegenerate ∧
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (p : ℤ) ^ (3 * (3 - 1) / 2) ∣ f.hessian.det) ∧
      properSpinorGenusNumber (f.map (Int.castRingHom ℚ)) (stdLat : Lat ℚ 3) = 1 := by
  refine ⟨QuadForm.diag ![1, 1, 27], ?_, ⟨3, Nat.prime_three, by norm_num, ?_⟩,
    properSpinorGenusNumber_diag_one_one_odd (by decide)⟩
  · have hh : ((QuadForm.diag ![1, 1, (27 : ℤ)]).map (Int.castRingHom ℚ)).hessian =
        (QuadForm.diag ![1, 1, (27 : ℤ)]).hessian.map (Int.castRingHom ℚ) := by
      ext i j; simp [QuadForm.hessian, QuadForm.map, Matrix.map_apply]
    unfold QuadForm.Nondegenerate
    rw [hh, show ((QuadForm.diag ![1, 1, (27 : ℤ)]).hessian.map (Int.castRingHom ℚ)).det =
      (((QuadForm.diag ![1, 1, (27 : ℤ)]).hessian.det : ℤ) : ℚ) from
      (RingHom.map_det (Int.castRingHom ℚ) _).symm, hessian_det_diag_one_one]
    norm_num
  · rw [hessian_det_diag_one_one]
    norm_num

end NotSufficient

end QuadFormsKB.Cassels.Ch11Wave6
