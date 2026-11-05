/-
# Cassels, Chapter 11, Examples 11, 12, 13 (pp. 253-254): the exercises on the proof of Theorem 1.6

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, Examples at the end of the chapter,
Ex. 11 (p. 253), Ex. 12 (pp. 253-254), Ex. 13 (p. 254). They concern §9, the proof of Theorem 1.6
(Tartakowsky's theorem, `Ch11Sec9.lean`). Indices are 0-based; capital $Q$ is the quadratic form (Cassels' $\phi$ or $f$),
$n$ the dimension.

**Ex. 11** (`Ex11Statement`, *named statement, not proved*). Let $\Lambda$ be a lattice in a regular rational quadratic space
$(V, Q)$ of dimension $3$ with $Q$ integer-valued on $\Lambda$; let $q$ be a prime with $Q$ isotropic over $\mathbb Q_q$; let $P^*$
be a set of odd primes at which $Q$ is anisotropic and the determinant of $\Lambda$ is divisible by $p$ but not by $p^2$; let
$b \in \Lambda$ with $|Q(b)|_p = p^{-1}$ for $p \in P^*$ and let $\eta_p = \pm 1$ be given. Then there is $\alpha \in O^+(V)$ with
$\alpha b \equiv \eta_p b \pmod{p\Lambda}$ for $p \in P^*$ and $\alpha \in O^+(\Lambda_p)$ for all primes $p \ne q$.
Formalization: primes are `HeightOneSpectrum (𝓞 ℚ)`; $\mathfrak p\Lambda$ is `v.asIdeal • L.1`; "$\alpha \in O^+(\Lambda_p)$" is
`locAct w α (loc w L.1) = loc w L.1`; the hypothesis "the determinant of the form induced on $\Lambda$ is divisible by $p$ but not
by $p^2$" is read, as in Chapter 10 Example 1 (`localSpinorNormGroup_eq_top_of_det`), as: for a basis $\gamma$ of $\Lambda_p$ the
Gram matrix `locGram Q v γ` (of the bilinear form $2Q$; $2$ is a unit as $p \ne 2$) has determinant of valuation $e^{-1}$.
*Reading of the scan:* the condition "$\alpha \in O^+(\Lambda_p)$ (all $p \ne q$)" is garbled in the machine text; the page image
shows it. Chapter 10 Example 3, of which this is the "analogue in the sense of Section 8", is not itself in the library.
*What a proof needs:* Chapter 10 Example 1 (all spinor norms of $O^+(\Lambda_p)$ occur) refined to the subgroup of $O^+(\Lambda_p)$
that acts on $b$ modulo $p$ by $\eta_p$ (this uses (i), anisotropy, to control the action on $b$), adjustment of the spinor norms by a
local element at $q$ (there $Q$ is isotropic, so every spinor norm occurs), and strong approximation away from $q$
(`strongApproximationSpinAt`, used as in Theorem 8.3, `exists_soSub_locAct_eq_of_sameProperSpinorGenus`).

**Ex. 12** (`ex12_exists_choice`, *proved*). The exercise asks to free the proof of Theorem 1.6 in §9 from Dirichlet's theorem on
primes in arithmetic progressions (the printed text says "Theorem 1.5", which is the statement for indefinite forms and has no
use of Dirichlet's theorem; it is Theorem 1.6, the subject of §9, that is meant; the hint refers to (9.39)-(9.41)). Dirichlet's
theorem is used (p. 246) to find $g_1 > 0$ in prescribed $p$-adic square classes at the primes of $P \cup \{q\}$, a unit at the
auxiliary prime $\pi$, and $g_1 = g\,p(0)$ with $p(0)$ prime. The hint replaces this by an *integer $g_1 > 0$ that satisfies the
class conditions (9.39) and is not divisible by the square of any prime outside the finite set*. That mathematical
content is `ex12_exists_choice`, proved with an elementary argument (Chinese remainder theorem, Hensel's lemma for the square
class, and removal of prime-to-$S$ square factors); no Dirichlet theorem. The remaining part of the hint (apply Example 11 at the
primes $p \notin P$, $p \mid g$, at which $V^{(p)}$ is anisotropic, then choose the coefficients as for $p(0)$) is a rewriting of
the proof of Lemma 9.2 and is recorded only through Example 11 (`Ex11Statement`) and Lemma 9.2 (`Lemma92` in `Ch11Sec9.lean`);
the full Dirichlet-free proof of Lemma 9.2 is not formalized.

**Ex. 13** (`Lemma93Primitive`, *named statement, not proved*). In Lemma 9.3, for $p \ne 2$ the vector $t$ may be chosen primitive
in $\mathbb Z_p^4$. Formalized as the statement that the data of `Lemma93` can be chosen with $t$ having a unit coordinate;
`Lemma93Primitive.toLemma93Odd` records that it implies Lemma 9.3 for odd $p$. *What a proof needs:* the hint (diagonalize the form
over $\mathbb Z_p$, $p$ odd) and then a repetition of the construction of Lemma 9.3 starting from a diagonal basis; it needs the
$\mathbb Z_p$ spinor norm of the ternary lattice (property (iii)), which the library lacks (see `Ch11Sec9.lean`).

**Corollary to Lemma 9.3** (p. 245), checked against the page image: "For every $z \in \mathbb Z_p$ with $|z|_p < |f(t)|_p$ there is
$c \in \Delta_p$ such that $f(t + c) = z$"; this agrees with the reconstruction `Lemma93Cor` in `Ch11Sec9.lean`.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec9
import QuadFormsKB.Literature.Cassels.Ch11Sec8
import QuadFormsKB.Literature.Cassels.Ch11Sec3Local

open Polynomial Matrix NumberField IsDedekindDomain WithZero

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Cassels

/-! ### Example 12: the choice of $g_1$ without Dirichlet's theorem -/

/-- **Helper:** $1 + p^3y$ is the square of a $p$-adic unit, for every $y \in \mathbb Z_p$ (Hensel's lemma at $a = 1$, valid
also for $p = 2$). Arguments: `p` the prime, `y` the $p$-adic integer. -/
theorem sq_of_one_add_cube (p : ℕ) [Fact p.Prime] (y : ℤ_[p]) :
    ∃ u : ℤ_[p], IsUnit u ∧ u ^ 2 = 1 + (p : ℤ_[p]) ^ 3 * y := by
  set F : Polynomial ℤ_[p] := X ^ 2 - C (1 + (p : ℤ_[p]) ^ 3 * y) with hF
  have h1 : F.aeval (1 : ℤ_[p]) = -((p : ℤ_[p]) ^ 3 * y) := by
    simp [hF]
  have h2 : F.derivative.aeval (1 : ℤ_[p]) = 2 := by
    rw [hF, derivative_sub, derivative_X_pow, derivative_C]
    simp
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hn2 : (1 : ℝ) / 2 ≤ ‖(2 : ℤ_[p])‖ := by
    by_cases h2p : p = 2
    · subst h2p
      have := PadicInt.norm_p (p := 2)
      simp at this
      rw [this]; norm_num
    · have : ‖(((2 : ℤ)) : ℤ_[p])‖ = 1 := by
        refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp ?_)
        rw [PadicInt.norm_int_lt_one_iff_dvd]
        intro hd
        have : p ∣ 2 := by exact_mod_cast hd
        exact h2p ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp this)
      simp at this
      rw [this]; norm_num
  have hnorm : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    rw [h1, h2, norm_neg, norm_mul, norm_pow, PadicInt.norm_p]
    have hy := PadicInt.norm_le_one y
    have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    have h8 : (8 : ℝ) ≤ (p : ℝ) ^ 3 := by nlinarith [sq_nonneg (p : ℝ)]
    have hlt : ((p : ℝ)⁻¹) ^ 3 ≤ 1 / 8 := by
      rw [inv_pow, one_div]
      exact inv_anti₀ (by norm_num) h8
    calc ((p : ℝ)⁻¹) ^ 3 * ‖y‖ ≤ ((p : ℝ)⁻¹) ^ 3 * 1 := by gcongr
      _ ≤ 1 / 8 := by simpa using hlt
      _ < (1 / 2) ^ 2 := by norm_num
      _ ≤ ‖(2 : ℤ_[p])‖ ^ 2 := by gcongr
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  have hz' : z ^ 2 = 1 + (p : ℤ_[p]) ^ 3 * y := by
    simp [hF] at hz
    linear_combination hz
  refine ⟨z, ?_, hz'⟩
  have hu : IsUnit (z ^ 2) := by
    rw [hz', PadicInt.isUnit_iff]
    have h3 : ‖(p : ℤ_[p]) ^ 3 * y‖ < 1 := by
      rw [norm_mul, norm_pow, PadicInt.norm_p]
      have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      have : ((p : ℝ)⁻¹) ^ 3 < 1 :=
        pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ (by linarith)) (by norm_num)
      calc ((p : ℝ)⁻¹) ^ 3 * ‖y‖ ≤ ((p : ℝ)⁻¹) ^ 3 * 1 := by gcongr; exact PadicInt.norm_le_one y
        _ < 1 := by simpa using this
    by_contra hne
    have hlt : ‖1 + (p : ℤ_[p]) ^ 3 * y‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one _) hne
    have h4 : ‖(1 : ℤ_[p])‖ ≤ max ‖1 + (p : ℤ_[p]) ^ 3 * y‖ ‖(p : ℤ_[p]) ^ 3 * y‖ := by
      have := PadicInt.nonarchimedean (1 + (p : ℤ_[p]) ^ 3 * y) (-((p : ℤ_[p]) ^ 3 * y))
      simpa [norm_neg] using this
    rw [norm_one] at h4
    exact absurd h4 (not_le.mpr (max_lt hlt h3))
  exact (isUnit_pow_iff two_ne_zero).1 hu

/-- **Helper: integers approximating a $p$-adic square class.** For a nonzero $p$-adic integer $c$ there are $n, k$ such that every
integer $g \equiv n \pmod{p^k}$ lies in $c\,U_p^2$ ($g = c u^2$ with $u$ a $p$-adic unit). Arguments: `p` the prime, `c` the
nonzero $p$-adic integer. -/
theorem local_class_approx (p : ℕ) [Fact p.Prime] {c : ℤ_[p]} (hc : c ≠ 0) :
    ∃ n k : ℕ, ∀ g : ℤ, g ≡ n [ZMOD (p : ℤ) ^ k] → ∃ u : ℤ_[p], IsUnit u ∧ (g : ℤ_[p]) = c * u ^ 2 := by
  set v := c.valuation with hv
  set e := PadicInt.unitCoeff hc with he
  refine ⟨PadicInt.appr c (v + 3), v + 3, fun g hg => ?_⟩
  have h1 : ((p : ℤ) ^ (v + 3)) ∣ g - (PadicInt.appr c (v + 3) : ℤ) := (Int.modEq_iff_dvd.mp hg.symm)
  obtain ⟨m, hm⟩ := h1
  have h2 := PadicInt.appr_spec (p := p) (v + 3) c
  rw [Ideal.mem_span_singleton] at h2
  obtain ⟨z, hz⟩ := h2
  have hg' : (g : ℤ_[p]) = c + (p : ℤ_[p]) ^ (v + 3) * (m - z) := by
    have : (g : ℤ_[p]) = (PadicInt.appr c (v + 3) : ℤ_[p]) + (p : ℤ_[p]) ^ (v + 3) * m := by
      have := congrArg (fun t : ℤ => (t : ℤ_[p])) hm
      push_cast at this
      linear_combination this
    rw [this]
    linear_combination (-1 : ℤ_[p]) * hz
  have hcs := PadicInt.unitCoeff_spec hc
  rw [← hv, ← he] at hcs
  obtain ⟨u, hu, hu2⟩ := sq_of_one_add_cube p (((e⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (m - z))
  refine ⟨u, hu, ?_⟩
  have hee : ((e : ℤ_[p])) * ((e⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by simp
  have hX : c * ((e⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = (p : ℤ_[p]) ^ v := by
    rw [hcs]; linear_combination ((p : ℤ_[p]) ^ v) * hee
  linear_combination hg' - c * hu2 - ((p : ℤ_[p]) ^ 3 * (m - z)) * hX

/-- **Helper: removing square factors prime to a finite set of primes.** For a positive integer $n$ and a finite set $S$ of primes
there are $w, g$ with $n = w^2 g$, $g > 0$, no prime of $S$ dividing $w$, and no prime outside $S$ dividing $g$ twice. Arguments:
`S` the finite set of primes, `n` the integer. -/
theorem exists_sq_split (S : Finset ℕ) :
    ∀ n : ℕ, 0 < n → ∃ w g : ℕ, n = w ^ 2 * g ∧ 0 < g ∧ (∀ p ∈ S, p.Prime → ¬ p ∣ w) ∧
      ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ^ 2 ∣ g := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h : ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ p ^ 2 ∣ n
    · obtain ⟨p, hp, hpS, n', hn'⟩ := h
      have hn'0 : 0 < n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn'; omega)
      have hlt : n' < n := by
        rw [hn']
        have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
        nlinarith
      obtain ⟨w, g, hwg, hg0, hw, hg⟩ := ih n' hlt hn'0
      refine ⟨p * w, g, by rw [hn', hwg]; ring, hg0, fun r hr hrp hd => ?_, hg⟩
      rcases (Nat.Prime.dvd_mul hrp).mp hd with h1 | h1
      · exact hpS (by rw [(Nat.prime_dvd_prime_iff_eq hrp hp).mp h1] at hr; exact hr)
      · exact hw r hr hrp h1
    · push Not at h
      exact ⟨1, n, by simp, hn, fun p _ hp hd => hp.one_lt.ne' (Nat.dvd_one.mp hd), fun p hp hpS hd => h p hp hpS hd⟩

/-- **Cassels, Ch. 11, Example 12** (pp. 253-254): the choice of the integer $g_1$ in the proof of Theorem 1.6 (§9, (9.39)-(9.41))
*without Dirichlet's theorem on primes in arithmetic progressions*. Let $S$ be a finite set of primes (Cassels' $P \cup \{q\}$),
for each $p \in S$ let $c_p \in \mathbb Z_p$ be nonzero (Cassels' $f(u_{j}(p))$, the value of the form at a primitive vector, which is
integral), and let $\pi \notin S$ be a prime (the auxiliary prime). Then there is a positive integer $g_1$ with
(i) $g_1 \in c_p U_p^2$ (i.e. $g_1 = c_p u^2$ for a $p$-adic unit $u$) for every $p \in S$ [(9.39$_1$)];
(ii) $\pi \nmid g_1$ [(9.39$_2$), "$g_1 \in U_\pi$"]; and
(iii) $g_1$ is not divisible by the square of any prime outside $S$ (the hint: "not divisible by the square of a $p \notin P$").
No Dirichlet theorem is used (the version of Cassels' text produces in addition a prime factor $p(0)$, which this version does not
need: the hint takes $g = g_1$ with the primes of $S$ left). Arguments: `S` the finite set of primes with proof `hS` that its
elements are prime, `c` the target values (a family indexed by the prime, with a $p$-adic integer for each prime), `hc` that
they are nonzero on $S$, `π` the auxiliary prime with `hπ` primality and `hπS` that it is outside $S$. *Proof:* Chinese remainder
theorem on the moduli from `local_class_approx` and $\pi$, then removal of square factors prime to $S$ (`exists_sq_split`); a unit square
factor does not change the square class. -/
@[kb "cassels1978" "Ch. 11, Ex. 12, pp. 253-254 (choice of g₁ without Dirichlet's theorem)"]
theorem ex12_exists_choice (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (c : ∀ (p : ℕ) [Fact p.Prime], ℤ_[p])
    (hc : ∀ (p : ℕ) [Fact p.Prime], p ∈ S → c p ≠ 0) (π : ℕ) (hπ : π.Prime) (hπS : π ∉ S) :
    ∃ g : ℕ, 0 < g ∧
      (∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∃ u : ℤ_[p], IsUnit u ∧ (g : ℤ_[p]) = c p * u ^ 2) ∧
      ¬ π ∣ g ∧ ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ^ 2 ∣ g := by
  have hloc : ∀ (p : ℕ) (hp : p ∈ S), ∃ n k : ℕ, ∀ g : ℤ, g ≡ n [ZMOD (p : ℤ) ^ k] →
      haveI : Fact p.Prime := ⟨hS p hp⟩
      ∃ u : ℤ_[p], IsUnit u ∧ (g : ℤ_[p]) = c p * u ^ 2 := by
    intro p hp
    haveI : Fact p.Prime := ⟨hS p hp⟩
    exact local_class_approx p (hc p hp)
  choose! n k hnk using hloc
  set t : Finset ℕ := insert π S with ht
  have htp : ∀ i ∈ t, i.Prime := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hπ
    · exact hS i hi
  set e : ℕ → ℕ := fun i => if i ∈ S then k i else 1 with he
  obtain ⟨k0, hk0⟩ := Nat.chineseRemainderOfFinset (fun i => if i ∈ S then n i else 1) (fun i => i ^ e i) t
    (fun i hi => pow_ne_zero _ (htp i hi).ne_zero)
    (fun i hi j hj hij => Nat.Coprime.pow _ _ ((Nat.coprime_primes (htp i hi) (htp j hj)).mpr hij))
  set N : ℕ := ∏ i ∈ t, i ^ e i with hN
  have hNpos : 0 < N := Finset.prod_pos fun i hi => pow_pos (htp i hi).pos _
  set g0 : ℕ := k0 + N with hg0
  have hg0pos : 0 < g0 := by omega
  have hg0mod : ∀ i ∈ t, g0 ≡ (if i ∈ S then n i else 1) [MOD i ^ e i] := by
    intro i hi
    have h1 : N ≡ 0 [MOD i ^ e i] := (Nat.modEq_zero_iff_dvd).mpr (Finset.dvd_prod_of_mem (fun i => i ^ e i) hi)
    have := (hk0 i hi).add h1
    simpa [hg0] using this
  have hπg : ¬ π ∣ g0 := by
    have h := hg0mod π (Finset.mem_insert_self _ _)
    simp only [hπS, ite_false, he] at h
    intro hd
    have h2 : g0 ≡ 0 [MOD π ^ 1] := by simpa using (Nat.modEq_zero_iff_dvd.mpr hd)
    have h3 : (1 : ℕ) ≡ 0 [MOD π ^ 1] := h.symm.trans h2
    have := (Nat.modEq_zero_iff_dvd.mp h3)
    simp at this
    exact hπ.one_lt.ne' (by omega)
  obtain ⟨w, g, hwg, hgpos, hw, hg⟩ := exists_sq_split S g0 hg0pos
  refine ⟨g, hgpos, ?_, fun hd => hπg ?_, hg⟩
  · intro p _ hpS
    haveI : Fact p.Prime := ⟨hS p hpS⟩
    have hmod := hg0mod p (Finset.mem_insert_of_mem hpS)
    simp only [hpS, ite_true, he] at hmod
    have hz : ((g0 : ℤ)) ≡ (n p : ℤ) [ZMOD (p : ℤ) ^ k p] := by
      have := (Int.natCast_modEq_iff (a := g0) (b := n p) (n := p ^ k p)).mpr hmod
      simpa using this
    obtain ⟨u, hu, hgu⟩ := hnk p hpS g0 hz
    have hw' : IsUnit (w : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp ?_)
      have := PadicInt.norm_int_lt_one_iff_dvd (p := p) (w : ℤ)
      simp only [Int.cast_natCast] at this
      rw [this]
      intro hd
      exact hw p hpS (hS p hpS) (by exact_mod_cast hd)
    obtain ⟨wu, hwu⟩ := hw'
    have hwi : (w : ℤ_[p]) * ((wu⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by rw [← hwu]; simp
    have hg0' : c p * u ^ 2 = (w : ℤ_[p]) ^ 2 * g := by
      rw [← hgu]
      have := congrArg (fun t : ℕ => (t : ℤ_[p])) hwg
      simpa using this
    refine ⟨u * ((wu⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), hu.mul (Units.isUnit _), ?_⟩
    linear_combination (-(((wu⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ^ 2)) * hg0' -
      ((g : ℤ_[p]) * (1 + (w : ℤ_[p]) * ((wu⁻¹ : ℤ_[p]ˣ) : ℤ_[p]))) * hwi
  · rw [hwg]
    exact Dvd.dvd.mul_left hd _

/-! ### Example 13: a primitive vector in Lemma 9.3 -/

/-- **Cassels, Ch. 11, Example 13** (p. 254), named statement: *in Lemma 9.3, if $p \ne 2$, then $t$ can always be chosen to be a
primitive element of $\mathbb Z_p^4$.* Formalized as: for every odd prime $p$ and every nondegenerate quaternary form $Q$ over
$\mathbb Z_p$ that is isotropic over $\mathbb Q_p$, the data $(t, B, g)$ of Lemma 9.3 (`Lemma93Data`) can be chosen with some
coordinate of $t$ a $p$-adic unit. *Not proved:* see the module docstring (diagonalize over $\mathbb Z_p$, then repeat the construction
of Lemma 9.3, which needs the spinor norm of ternary $\mathbb Z_p$-lattices for (iii)). -/
@[kb "cassels1978" "Ch. 11, Ex. 13, p. 254"]
structure Lemma93Primitive : Prop where
  /-- Lemma 9.3 with $t$ primitive, for odd $p$. -/
  holds : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ Q : QuadForm ℤ_[p] 4, Q.Nondegenerate →
    (Q.map PadicInt.Coe.ringHom).IsotropicIn ℚ_[p] →
    ∃ (t : Fin 4 → ℤ_[p]) (B : Matrix (Fin 4) (Fin 3) ℤ_[p]) (g : QuadForm ℤ_[p] 3),
      Lemma93Data p Q t B g ∧ ∃ i, IsUnit (t i)

/-- **Example 13 implies Lemma 9.3 for odd $p$:** forgetting that $t$ is primitive. Arguments: `h` the statement of Example 13. -/
theorem Lemma93Primitive.toLemma93Odd (h : Lemma93Primitive) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (Q : QuadForm ℤ_[p] 4) (hQ : Q.Nondegenerate) (hiso : (Q.map PadicInt.Coe.ringHom).IsotropicIn ℚ_[p]) :
    ∃ (t : Fin 4 → ℤ_[p]) (B : Matrix (Fin 4) (Fin 3) ℤ_[p]) (g : QuadForm ℤ_[p] 3), Lemma93Data p Q t B g := by
  obtain ⟨t, B, g, hd, -⟩ := h.holds p hp Q hQ hiso
  exact ⟨t, B, g, hd⟩

/-! ### Example 11: the analogue of Chapter 10, Example 3 -/

open QuadFormsKB.Lattices

/-- **Cassels, Ch. 11, Example 11** (p. 253), named statement; see the module docstring for the formalization and for what a
proof needs. Let $Q$ be a nondegenerate ternary rational form, $L$ a lattice (`Lat ℚ 3`) on which $Q$ takes integer values, $q$ a
prime at which $Q$ is isotropic, $P^*$ a set of odd primes (`Pstar`) at each of which $Q$ is anisotropic and $\Lambda_p$ has
determinant of valuation exactly one (`locGram`), $b \in L$ with $|Q(b)|_p = p^{-1}$ at the primes of $P^*$, and $\eta_p = \pm 1$
(`η`). Then there is a rotation $\alpha \in O^+(V)$ (`Tamagawa.soSub Q ℚ`) with $\alpha b - \eta_p b \in p\Lambda$ for $p \in P^*$ and
$\alpha\Lambda_p = \Lambda_p$ for all primes $p \ne q$. Fields: `holds` is the statement, with arguments in the order `Q` (form),
`hQ` (regular), `L` (lattice), `hint` ($Q$ integer-valued on $L$), `q` (the prime), `hq` ($Q$ isotropic at $q$), `Pstar`, `h2`
(odd primes), `hani` (anisotropy), `hdet` (determinant valuation, via a basis $\gamma$ of $\Lambda_p$), `b`, `hb` ($b \in L$),
`hbv` ($|Q(b)|_p = p^{-1}$), `η`, `hη` ($\eta_p = \pm 1$). -/
@[kb "cassels1978" "Ch. 11, Ex. 11, p. 253 (analogue of Ch. 10, Ex. 3)"]
structure Ex11Statement : Prop where
  /-- Example 11. -/
  holds : ∀ (Q : QuadForm ℚ 3), Q.Nondegenerate → ∀ (L : Lat ℚ 3), (∀ x ∈ L.1, ∃ z : ℤ, Q.eval x = z) →
    ∀ (q : HeightOneSpectrum (𝓞 ℚ)), Q.IsotropicIn (q.adicCompletion ℚ) →
    ∀ (Pstar : Set (HeightOneSpectrum (𝓞 ℚ))),
      (∀ v ∈ Pstar, (2 : 𝓞 ℚ) ∉ v.asIdeal) →
      (∀ v ∈ Pstar, ¬ Q.IsotropicIn (v.adicCompletion ℚ)) →
      (∀ v ∈ Pstar, ∃ γ : GL (Fin 3) (v.adicCompletion ℚ), loc v L.1 = locAct v γ (std v) ∧
        Valued.v (locGram Q v γ).det = exp (-1 : ℤ)) →
      ∀ b ∈ L.1, (∀ v ∈ Pstar, Valued.v (Q.evalIn (v.adicCompletion ℚ) (locVec v b)) = exp (-1 : ℤ)) →
      ∀ η : HeightOneSpectrum (𝓞 ℚ) → ℚ, (∀ v ∈ Pstar, η v = 1 ∨ η v = -1) →
      ∃ α ∈ Tamagawa.soSub Q ℚ,
        (∀ v ∈ Pstar, ((α : orthGroup Q ℚ) : GL (Fin 3) ℚ).val.mulVec b - η v • b ∈ v.asIdeal • L.1) ∧
        ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ q →
          locAct w ((orthMap Q (w.adicCompletion ℚ) α : orthGroup Q _) : GL (Fin 3) (w.adicCompletion ℚ))
            (loc w L.1) = loc w L.1

end QuadFormsKB.Cassels
