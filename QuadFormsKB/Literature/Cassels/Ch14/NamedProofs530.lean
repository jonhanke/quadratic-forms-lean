/-
# Cassels, Chapter 14: proofs of some named statements

Cassels, *Rational Quadratic Forms* (1978), Ch. 14.

* `fourRSRepresentation_holds`: the representation (6.24), §6, p. 351, proved from the principal genus: the form
  $[r, 0, -s]$ of discriminant $4rs$ is locally equivalent to the principal form $[1, 0, -rs]$ at every place
  (the local computations are done by hand: $4rs$ is not a fundamental discriminant, so the genus characters of
  `Binary.sameGenus_iff_formChar_eq` do not apply), and then `exists_eval_sq_of_inPrincipalGenus` (Theorem 3.1, Lemma 2.5).
-/
import QuadFormsKB.Literature.Cassels.Ch14.NamedStatements

namespace QuadFormsKB.Composition

open BinQF Binary FormClass Siegel

/-- Helper: a primitively represented value $m = f(x, y)$ prime to $p$ which is a $p$-adic square, where
$g$ has $a_g = 1$ and the same discriminant as $f$, gives $f \cong g$ over $\mathbb Z_p$. -/
lemma padic_equiv_of_value {p : ℕ} [Fact p.Prime] {f g : BinQF} (hd : f.disc = g.disc) (hg1 : g.a = 1)
    {x y : ℤ} (hxy : IsCoprime x y) (hm : ¬ (p : ℤ) ∣ f.eval x y) {z : ℤ_[p]}
    (hz : z ^ 2 = ((f.eval x y : ℤ) : ℤ_[p])) :
    IsometricGL (f.map (Int.castRingHom ℤ_[p])) (g.map (Int.castRingHom ℤ_[p])) := by
  obtain ⟨f', hI, ha, hdf⟩ := exists_intEquiv_a_eq f hxy
  have hg : ¬ (p : ℤ) ∣ g.a := by
    rw [hg1]; intro h
    have := Int.eq_one_of_dvd_one (by positivity) h
    have := (Fact.out : p.Prime).one_lt
    omega
  have key := isometricGL_padic_of_sq (p := p) (f := f') (g := g) (by rw [hdf, hd]) (by rw [ha]; exact hm) hg
    (z := z) (by rw [ha, hg1]; simpa using hz)
  exact (hI.map (Int.castRingHom ℤ_[p])).trans key

/-- Helper: the form $[r, 0, -s]$. -/
def fourRSForm (r s : ℕ) : BinQF := BinQF.mk r 0 (-(s : ℤ))

/-- Helper: the discriminant of $[r, 0, -s]$ is $4rs$. -/
lemma disc_fourRSForm (r s : ℕ) : (fourRSForm r s).disc = 4 * r * s := by
  simp [fourRSForm, BinQF.disc]

/-- Helper: $[r, 0, -s](x, y) = rx^2 - sy^2$. -/
lemma eval_fourRSForm (r s : ℕ) (x y : ℤ) : (fourRSForm r s).eval x y = r * x ^ 2 - s * y ^ 2 := by
  rw [eval_eq]; simp [fourRSForm]; ring

/-- Helper: $[r, 0, -s]$ is in the principal genus for primes $r \equiv s \equiv 1 \pmod 4$, $r \ne s$,
$(s/r) = 1$ (Cassels, Ch. 14, §6, p. 351). -/
theorem inPrincipalGenus_fourRSForm (r s : ℕ) [Fact r.Prime] [Fact s.Prime] (hr : r % 4 = 1) (hs : s % 4 = 1)
    (hrs : r ≠ s) (hη : legendreSym s r = 1) : InPrincipalGenus (fourRSForm r s) := by
  have hrp : r.Prime := Fact.out
  have hsp : s.Prime := Fact.out
  have hdisc := disc_fourRSForm r s
  have hmod : (4 * (r : ℤ) * s) % 4 = 0 ∨ (4 * (r : ℤ) * s) % 4 = 1 := by left; rw [mul_assoc]; exact Int.mul_emod_right _ _
  have hspec := principalForm_spec hmod
  have hg1 : (principalForm (4 * (r : ℤ) * s)).a = 1 := rfl
  have hdd : (fourRSForm r s).disc = (principalForm (4 * (r : ℤ) * s)).disc := by rw [hdisc, hspec.2]
  have hrs' : legendreSym r s = 1 := by
    rw [← legendreSym.quadratic_reciprocity_one_mod_four hr (by rintro rfl; omega)]; exact hη
  unfold InPrincipalGenus
  rw [hdisc]
  refine ⟨fun p hp => ?_, ?_⟩
  · by_cases h2 : p = 2
    · subst h2
      have h8 : r % 8 = 1 ∨ r % 8 = 5 := by omega
      rcases h8 with h8 | h8
      · obtain ⟨z, hz⟩ := exists_sq_padic_two (c := (fourRSForm r s).eval 1 0) (by
          rw [eval_fourRSForm]
          have := zmod8_eq_of_dvd (t := (r : ℤ) * 1 ^ 2 - s * 0 ^ 2) (m := 1) (by omega)
          simpa using this)
        exact padic_equiv_of_value (hdd.trans rfl) hg1 (isCoprime_one_left) (by rw [eval_fourRSForm]; omega) hz
      · obtain ⟨z, hz⟩ := exists_sq_padic_two (c := (fourRSForm r s).eval 1 2) (by
          rw [eval_fourRSForm]
          have := zmod8_eq_of_dvd (t := (r : ℤ) * 1 ^ 2 - s * 2 ^ 2) (m := 1) (by omega)
          simpa using this)
        exact padic_equiv_of_value (hdd.trans rfl) hg1 (by
          exact ⟨1, 0, by norm_num⟩) (by rw [eval_fourRSForm]; omega) hz
    · by_cases hpr : p = r
      · subst hpr
        obtain ⟨z, hz⟩ := exists_sq_padic_odd (p := p) h2 (c := (fourRSForm p s).eval 0 1) (by
          rw [eval_fourRSForm]
          intro h
          have h' : (p : ℤ) ∣ (s : ℤ) := by simpa using h
          have := (Nat.prime_dvd_prime_iff_eq hrp hsp).mp (Int.natCast_dvd_natCast.mp h')
          exact hrs this) (by
          rw [eval_fourRSForm, ← jacobiSym.legendreSym.to_jacobiSym]
          have : ((p : ℤ) * 0 ^ 2 - s * 1 ^ 2) = (-1) * s := by ring
          rw [this, legendreSym.mul, legendreSym.at_neg_one h2, ZMod.χ₄_nat_one_mod_four hr, hrs']
          rfl)
        exact padic_equiv_of_value (hdd.trans rfl) hg1 (by exact ⟨0, 1, by norm_num⟩) (by
          rw [eval_fourRSForm]
          intro h
          have h' : (p : ℤ) ∣ (s : ℤ) := by simpa using h
          have := (Nat.prime_dvd_prime_iff_eq hrp hsp).mp (Int.natCast_dvd_natCast.mp h')
          exact hrs this) hz
      · by_cases hps : p = s
        · subst hps
          obtain ⟨z, hz⟩ := exists_sq_padic_odd (p := p) h2 (c := (fourRSForm r p).eval 1 0) (by
            rw [eval_fourRSForm]
            intro h
            have h' : (p : ℤ) ∣ (r : ℤ) := by simpa using h
            have := (Nat.prime_dvd_prime_iff_eq hsp hrp).mp (Int.natCast_dvd_natCast.mp h')
            exact hpr this) (by
            rw [eval_fourRSForm, ←jacobiSym.legendreSym.to_jacobiSym]
            simpa using hη)
          exact padic_equiv_of_value (hdd.trans rfl) hg1 (isCoprime_one_left) (by
            rw [eval_fourRSForm]
            intro h
            have h' : (p : ℤ) ∣ (r : ℤ) := by simpa using h
            have := (Nat.prime_dvd_prime_iff_eq hsp hrp).mp (Int.natCast_dvd_natCast.mp h')
            exact hpr this) hz
        · refine isometricGL_padic_of_not_dvd h2 hdd ?_
          rw [hdisc]
          intro h
          have h' : p ∣ 4 * r * s := by exact_mod_cast h
          have hpp : p.Prime := Fact.out
          rcases (Nat.Prime.dvd_mul hpp).mp h' with h4 | h4
          · rcases (Nat.Prime.dvd_mul hpp).mp h4 with h4 | h4
            · have : p ∣ 2 * 2 := by simpa using h4
              rcases (Nat.Prime.dvd_mul hpp).mp this with h5 | h5 <;>
                exact h2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h5)
            · exact hpr ((Nat.prime_dvd_prime_iff_eq hpp hrp).mp h4)
          · exact hps ((Nat.prime_dvd_prime_iff_eq hpp hsp).mp h4)
  · have hrpos : (0 : ℝ) < r := by exact_mod_cast hrp.pos
    have hsq : Real.sqrt (1 / (r : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    refine isometricGL_map_of_sq two_ne_zero _ hdd (by simpa [fourRSForm] using hrp.ne_zero) (Units.mk0 _ hsq) ?_
    simp only [Units.val_mk0, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 / r), hg1, fourRSForm, a_mk]
    simp

/-- **The representation (6.24) holds** (Cassels, Ch. 14, §6, p. 351): for distinct primes $r \equiv s \equiv 1
\pmod 4$ with $(s/r) = 1$ there are coprime integers $x, y$ and $w$ prime to $2rs$ with $rx^2 - sy^2 = w^2$.
Proof: $[r, 0, -s]$ is in the principal genus (`inPrincipalGenus_fourRSForm`), so by Theorem 3.1 / Lemma 2.5
(`exists_eval_sq_of_inPrincipalGenus`) it primitively represents a square $w^2$ with $w$ prime to $2\cdot 4rs$. -/
@[kb "cassels1978" "Ch. 14, §6, (6.24), p. 351 (proved)"]
theorem fourRSRepresentation_holds : FourRSRepresentation := by
  refine ⟨fun r s _ _ hr hs hrs hη => ?_⟩
  have hD : (fourRSForm r s).disc ≠ 0 := by
    rw [disc_fourRSForm]
    have := (Fact.out : r.Prime).pos
    have := (Fact.out : s.Prime).pos
    positivity
  obtain ⟨w, x, y, hxy, hw, h⟩ :=
    exists_eval_sq_of_inPrincipalGenus hD (inPrincipalGenus_fourRSForm r s hr hs hrs hη)
  rw [disc_fourRSForm] at hw
  refine ⟨x, y, w, hxy, ?_, by rw [← eval_fourRSForm]; exact h⟩
  refine IsCoprime.of_isCoprime_of_dvd_right hw ?_
  exact ⟨4, by ring⟩

/-! ### Ex. 5 (i): a class of order exactly $N$ -/

/-- Helper: the form $[2^j, 1, 2^{N-j}]$ (of discriminant $1 - 4\cdot 2^N$ when $j \le N$). -/
def nagellForm (N j : ℕ) : BinQF := BinQF.mk ((2 : ℤ) ^ j) 1 ((2 : ℤ) ^ (N - j))

/-- Helper: the discriminant of `nagellForm N j` is $1 - 4\cdot 2^N$ for $j \le N$. -/
lemma disc_nagellForm {N j : ℕ} (hj : j ≤ N) : (nagellForm N j).disc = 1 - 4 * 2 ^ N := by
  have : (2 : ℤ) ^ N = 2 ^ j * 2 ^ (N - j) := by rw [← pow_add, Nat.add_sub_cancel' hj]
  simp only [nagellForm, BinQF.disc, a_mk, b_mk, c_mk]
  rw [this]; ring

/-- Helper: `nagellForm N j` as a primitive form of discriminant $1 - 4\cdot 2^N$. -/
def nagellPrim (N j : ℕ) (hj : j ≤ N) : PrimForm (1 - 4 * 2 ^ N) :=
  ⟨nagellForm N j, fun d _ h2 _ => isUnit_of_dvd_one (by simpa [nagellForm] using h2), disc_nagellForm hj⟩

/-- Helper: $\mathfrak E$-class of $[2^0, 1, 2^N]$ and $[2^N, 1, 1]$ are trivial; in general
`mk (nagellPrim N 0) = 1`. -/
lemma mk_nagellPrim_zero {N : ℕ} [NonzeroDisc (1 - 4 * 2 ^ N)] : mk (nagellPrim N 0 (Nat.zero_le N)) = 1 :=
  (mk_eq_one_iff _).2 ⟨1, 0, by rw [eval_eq]; simp [nagellPrim, nagellForm]⟩

/-- Helper: `mk (nagellPrim N N) = 1` (it represents $1$ at $(0, 1)$). -/
lemma mk_nagellPrim_self {N : ℕ} [NonzeroDisc (1 - 4 * 2 ^ N)] : mk (nagellPrim N N le_rfl) = 1 :=
  (mk_eq_one_iff _).2 ⟨0, 1, by rw [eval_eq]; simp [nagellPrim, nagellForm]⟩

/-- Helper (Cassels, Ch. 14, Lemma 2.5 style): $[2,1,*] \cdot [2^j, 1, *] = [2^{j+1}, 1, *]$, because the forms are
concordant ($4\cdot 2\cdot 2^j \mid 1 - D = 4\cdot 2^N$ when $j + 1 \le N$). -/
lemma mk_nagellPrim_one_mul {N : ℕ} [NonzeroDisc (1 - 4 * 2 ^ N)] (h1 : 1 ≤ N) {j : ℕ} (hj : j + 1 ≤ N) :
    mk (nagellPrim N 1 h1) * mk (nagellPrim N j (by omega)) = mk (nagellPrim N (j + 1) hj) := by
  have hN : (2 : ℤ) ^ N = 2 ^ (j + 1) * 2 ^ (N - (j + 1)) := by rw [← pow_add, Nat.add_sub_cancel' hj]
  have hc : Concordant (nagellPrim N 1 h1).1 (nagellPrim N j (by omega)).1 := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · simp [nagellPrim, nagellForm]
    · rw [(nagellPrim N 1 h1).2.2, (nagellPrim N j (by omega)).2.2]
    · refine ⟨2 ^ (N - (j + 1)), ?_⟩
      rw [(nagellPrim N 1 h1).2.2]
      simp only [nagellPrim, nagellForm, a_mk, b_mk]
      rw [hN]; ring
  rw [mk_mul_mk _ _ hc]
  congr 1
  refine Subtype.ext (ext_abc ?_ ?_ ?_)
  · show (Composition.comp (nagellForm N 1) (nagellForm N j)).a = (nagellForm N (j + 1)).a
    simp [nagellForm, pow_succ]; ring
  · show (Composition.comp (nagellForm N 1) (nagellForm N j)).b = (nagellForm N (j + 1)).b
    simp [nagellForm]
  · show (Composition.comp (nagellForm N 1) (nagellForm N j)).c = (nagellForm N (j + 1)).c
    unfold Composition.comp
    rw [c_mk, disc_nagellForm h1]
    simp only [nagellForm, a_mk, b_mk, c_mk]
    rw [Int.ediv_eq_of_eq_mul_right (by positivity)]
    rw [hN]; ring

/-- Helper: $[2,1,*]^j = [2^j, 1, *]$ for $0 \le j \le N$. -/
lemma pow_nagellPrim {N : ℕ} [NonzeroDisc (1 - 4 * 2 ^ N)] (h1 : 1 ≤ N) :
    ∀ j (hj : j ≤ N), mk (nagellPrim N 1 h1) ^ j = mk (nagellPrim N j hj) := by
  intro j
  induction j with
  | zero => intro hj; rw [pow_zero]; exact mk_nagellPrim_zero.symm
  | succ j ih =>
    intro hj
    rw [pow_succ, ih (by omega)]
    exact (mul_comm _ _).trans (mk_nagellPrim_one_mul h1 hj)

/-- Helper: for $0 < m < N$ the form $[2^m, 1, 2^{N-m}]$ does not represent $1$ (it is positive definite with
$4\cdot 2^m = (2\cdot 2^m x + y)^2 + (2^{N+2} - 1) y^2$ and $2^{N+2} - 1 > 2^{m+2}$). -/
lemma not_represents_one_nagell {N m : ℕ} (hm : 0 < m) (hmN : m < N) : ¬ (nagellForm N m).Represents 1 := by
  rintro ⟨x, y, h⟩
  rw [eval_eq] at h
  simp only [nagellForm, a_mk, b_mk, c_mk] at h
  have hN : (2 : ℤ) ^ N = 2 ^ m * 2 ^ (N - m) := by rw [← pow_add, Nat.add_sub_cancel' hmN.le]
  have ha : (2 : ℤ) ≤ 2 ^ m := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hc : (2 : ℤ) ≤ 2 ^ (N - m) := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (N - m) := pow_le_pow_right₀ (by norm_num) (by omega)
  generalize (2 : ℤ) ^ m = a at *
  generalize (2 : ℤ) ^ (N - m) = c at *
  have key : 4 * a = (2 * a * x + y) ^ 2 + (4 * a * c - 1) * y ^ 2 := by
    linear_combination (-4 * a) * h
  by_cases hy : y = 0
  · subst hy
    have : a * x ^ 2 = 1 := by linarith
    by_cases hx : x = 0
    · subst hx; norm_num at this
    · have : 1 ≤ x ^ 2 := by
        have := sq_pos_of_ne_zero hx
        omega
      nlinarith
  · have hy2 : 1 ≤ y ^ 2 := by
      have := sq_pos_of_ne_zero hy
      omega
    have hac : 2 * a ≤ a * c := by nlinarith
    have h4 : 0 ≤ (4 * a * c - 1) * (y ^ 2 - 1) := mul_nonneg (by nlinarith) (by linarith)
    nlinarith [sq_nonneg (2 * a * x + y)]

/-- **Ex. 5 (i) holds** (Cassels, Ch. 14, p. 359; Nagell 1922): for every $N > 1$ the discriminant
$D = 1 - 4\cdot 2^N < 0$ has a class of order exactly $N$, namely the class of $[2, 1, 2^{N-1}]$. Its $j$-th power is
the class of $[2^j, 1, 2^{N-j}]$ (concordant composition), which is trivial for $j = N$ (it represents $1$) and
non-trivial for $0 < j < N$ (positive definiteness: $4\cdot 2^j = u^2 + (2^{N+2} - 1) y^2$ has only $y = 0$). -/
@[kb "cassels1978" "Ch. 14, Ex. 5 (i), p. 359 (proved)"]
theorem nagellOrderN_holds : NagellOrderN := by
  refine ⟨fun N hN => ?_⟩
  have h2N : (4 : ℤ) ≤ 2 ^ N := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hnz : NonzeroDisc (1 - 4 * 2 ^ N : ℤ) := ⟨by omega, by right; omega⟩
  refine ⟨1 - 4 * 2 ^ N, hnz, by omega, mk (nagellPrim N 1 hN.le), ?_⟩
  rw [orderOf_eq_iff (by omega)]
  refine ⟨by rw [pow_nagellPrim hN.le N le_rfl]; exact mk_nagellPrim_self, fun m hmN hm0 => ?_⟩
  rw [pow_nagellPrim hN.le m hmN.le, Ne, mk_eq_one_iff]
  exact not_represents_one_nagell hm0 hmN

/-- **The genus character of $\mathfrak C_r$ is $[s/r]_4$, unconditionally** (Cassels, Ch. 14, §6, pp. 351–352): for
distinct primes $r \equiv s \equiv 1 \pmod 4$ (`hr`, `hs`, `hrs`) with $(s/r) = 1$ (`hη`) there are coprime $x, y$ and
$w$ prime to $2rs$ with $rx^2 - sy^2 = w^2$ and $(w/r) = [s/r]_4$: `exists_rep_legendreSym_eq_condBiquadSym` with its
hypothesis (6.24) discharged by `fourRSRepresentation_holds`. -/
@[kb "cassels1978" "Ch. 14, §6, p. 352 (ε_r = [s/r]₄; unconditional)"]
theorem exists_rep_legendreSym_eq_condBiquadSym_uncond {r s : ℕ} [Fact r.Prime] [Fact s.Prime] (hr : r % 4 = 1)
    (hs : s % 4 = 1) (hrs : r ≠ s) (hη : legendreSym s r = 1) :
    ∃ x y w : ℤ, IsCoprime x y ∧ IsCoprime w (2 * r * s) ∧ (r : ℤ) * x ^ 2 - s * y ^ 2 = w ^ 2 ∧
      legendreSym r w = condBiquadSym r s :=
  exists_rep_legendreSym_eq_condBiquadSym fourRSRepresentation_holds hr hs hrs hη

end QuadFormsKB.Composition
