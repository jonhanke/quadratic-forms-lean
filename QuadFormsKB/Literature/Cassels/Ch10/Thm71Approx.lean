/-
# Cassels, Chapter 10, proof of Theorem 7.1: the two approximation inputs for $n \ge 4$

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 10, §7, Lemma 7.1 (p. 187, a reformulation of Ch. 9,
Theorem 1.5) and the proof of Theorem 7.1 (pp. 188-189).

**Proves** (the two approximation inputs of Cassels' proof of Theorem 7.1 for $n \ge 4$):
* `exists_rat_approx`: weak approximation for $\mathbb Q$ at finitely many primes: for a finite set $P$ of primes, local
  targets $z_p \in \mathbb Q_p$ and $K \in \mathbb N$ there is $y \in \mathbb Q$ with $|y - z_p|_p \le p^{-K}$ for $p \in P$;
* `lemma71`: Cassels' Lemma 7.1 in coordinates: if $f$ is a regular indefinite integral form in $n \ge 4$ variables, $P$ a finite
  set of primes containing $2$ and all primes dividing $\det f$, $m \in \mathbb Q^\times$ is $p$-integral for $p \notin P$, and
  $z^{(p)} \in \mathbb Q_p^n$ ($p \in P$) satisfy $f(z^{(p)}) = m$, then for every $K$ there is $\mathbf x \in \mathbb Q^n$ with
  $f(\mathbf x) = m$, $|x_i - z^{(p)}_i|_p \le p^{-K}$ for $p \in P$ and $\mathbf x$ $p$-integral for $p \notin P$.

All indices are 0-based ($x_0, \dots, x_{n-1}$; Cassels' $x_1, \dots, x_n$ are `x 0, …, x (n-1)`).

*Proof of Lemma 7.1* (Cassels, p. 188): choose $s$ with $p^s z^{(p)} \in \mathbb Z_p^n$ for $p \in P$ and with
$a := M^2 m \in \mathbb Z$, where $M = \prod_{p \in P} p^s$. The integer $a$ is represented over every $\mathbb Z_p$: at
$p \in P$ by $M z^{(p)}$, at $p \notin P$ by the unimodularity of $f$ at the odd prime $p$ (`exists_primitive_padic_of_unimodular`).
Ch. 9, Theorem 1.5 with approximation (`Siegel.exists_rep_approx`) gives $X \in \mathbb Z^n$ with $f(X) = a$ and
$X \equiv M z^{(p)} \pmod{p^{K+s}}$ for $p \in P$; then $\mathbf x = X/M$.

*Proof of weak approximation:* rescale by $M$, approximate $M z_p \in \mathbb Z_p$ by an integer modulo $p^{K+s}$
(`PadicInt.appr`), combine by the Chinese remainder theorem, divide by $M$.
-/
import QuadFormsKB.Literature.Cassels.Ch10.Thm71Ternary
import QuadFormsKB.Literature.Cassels.Ch11Sec9Steps

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels.Thm71Approx

open QuadFormsKB.Cassels.Thm71Ternary

section Helpers

/-- Helper: a vector over $\mathbb Q_p$ is bounded by a power of $p$. Arguments: `p` the prime, `x` the vector. -/
theorem exists_pow_bound {p : ℕ} [Fact p.Prime] {n : ℕ} (x : Fin n → ℚ_[p]) :
    ∃ s : ℕ, ∀ i, ‖x i‖ ≤ (p : ℝ) ^ (s : ℤ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt ‖x‖ hp1
  exact ⟨s, fun i => (norm_le_pi_norm x i).trans (by rw [zpow_natCast]; exact hs.le)⟩

/-- Helper: $|M\,y|_p \le 1$ for $p \in P$ when $|y|_p \le p^s$ and $M = \prod_{q \in P} q^s$. Arguments: `hp` membership,
`hy` the bound on `y`. -/
theorem norm_mul_le_one {P : Finset Nat.Primes} {s : ℕ} {p : Nat.Primes} (hp : p ∈ P) {y : ℚ_[(p : ℕ)]}
    (hy : ‖y‖ ≤ ((p : ℕ) : ℝ) ^ (s : ℤ)) : ‖(((∏ q ∈ P, (q : ℕ) ^ s : ℕ)) : ℚ_[(p : ℕ)]) * y‖ ≤ 1 := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  rw [norm_mul, norm_prod_pow_of_mem P s p hp]
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hpos : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (-(s : ℤ)) := by positivity
  calc ((p : ℕ) : ℝ) ^ (-(s : ℤ)) * ‖y‖ ≤ ((p : ℕ) : ℝ) ^ (-(s : ℤ)) * ((p : ℕ) : ℝ) ^ (s : ℤ) :=
        mul_le_mul_of_nonneg_left hy hpos.le
    _ = 1 := by rw [← zpow_add₀ hp0.ne', neg_add_cancel, zpow_zero]

/-- Helper (rescaling back): if $|X - b|_p \le p^{-(K+s)}$ with $b = Mz$ in $\mathbb Q_p$, $M = \prod_{q \in P} q^s$ and
$p \in P$, then $|X/M - z|_p \le p^{-K}$. Arguments: `hp` membership, `X` the integer, `b` the local integer,
`z` the target, `hb` $b = Mz$, `h` the closeness. -/
theorem norm_div_sub_le {P : Finset Nat.Primes} {s K : ℕ} {p : Nat.Primes} (hp : p ∈ P) (X : ℤ)
    (b : ℤ_[(p : ℕ)]) (z : ℚ_[(p : ℕ)]) (hb : (b : ℚ_[(p : ℕ)]) = (∏ q ∈ P, (q : ℕ) ^ s : ℕ) * z)
    (h : ‖((X : ℤ_[(p : ℕ)]) - b : ℤ_[(p : ℕ)])‖ ≤ ((p : ℕ) : ℝ) ^ (-((K + s : ℕ) : ℤ))) :
    ‖(((X : ℚ) / (∏ q ∈ P, (q : ℕ) ^ s : ℕ) : ℚ) : ℚ_[(p : ℕ)]) - z‖ ≤ ((p : ℕ) : ℝ) ^ (-(K : ℤ)) := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  have hMpos : 0 < ∏ q ∈ P, (q : ℕ) ^ s := Finset.prod_pos fun q _ => pow_pos q.2.pos _
  have hM' : ((∏ q ∈ P, (q : ℕ) ^ s : ℕ) : ℚ_[(p : ℕ)]) ≠ 0 := by exact_mod_cast hMpos.ne'
  have heq : (((X : ℚ) / (∏ q ∈ P, (q : ℕ) ^ s : ℕ) : ℚ) : ℚ_[(p : ℕ)]) - z =
      (((X : ℤ_[(p : ℕ)]) - b : ℤ_[(p : ℕ)]) : ℚ_[(p : ℕ)]) / ((∏ q ∈ P, (q : ℕ) ^ s : ℕ) : ℚ_[(p : ℕ)]) := by
    rw [PadicInt.coe_sub, hb, PadicInt.coe_intCast, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    field_simp
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  rw [heq, norm_div, PadicInt.norm_coe, norm_prod_pow_of_mem P s p hp, div_le_iff₀ (zpow_pos hp0 _)]
  calc ‖((X : ℤ_[(p : ℕ)]) - b : ℤ_[(p : ℕ)])‖ ≤ ((p : ℕ) : ℝ) ^ (-((K + s : ℕ) : ℤ)) := h
    _ = ((p : ℕ) : ℝ) ^ (-(K : ℤ)) * ((p : ℕ) : ℝ) ^ (-(s : ℤ)) := by
        rw [← zpow_add₀ hp0.ne']; push_cast; ring_nf

/-- Helper: $|X/M|_p \le 1$ for $p \notin P$, $X \in \mathbb Z$, $M = \prod_{q \in P} q^s$. Arguments: `hp`, `X`. -/
theorem norm_div_le_one {P : Finset Nat.Primes} {s : ℕ} {p : Nat.Primes} (hp : p ∉ P) (X : ℤ) :
    ‖(((X : ℚ) / (∏ q ∈ P, (q : ℕ) ^ s : ℕ) : ℚ) : ℚ_[(p : ℕ)])‖ ≤ 1 := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  have hMp := norm_prod_pow_of_not_mem P s p hp
  rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, norm_div, hMp, div_one]
  exact Padic.norm_int_le_one _

/-- Helper: if $m \in \mathbb Q$ is $p$-integral for all primes $p \notin P$, its denominator divides
$\prod_{q \in P} q^{\mathrm{den}(m)}$. Arguments: `P`, `m`, `hmint`. -/
theorem den_dvd_prod (P : Finset Nat.Primes) (m : ℚ)
    (hmint : ∀ p : Nat.Primes, p ∉ P → ‖(m : ℚ_[(p : ℕ)])‖ ≤ 1) :
    m.den ∣ ∏ q ∈ P, (q : ℕ) ^ m.den := by
  have hsub : m.den.primeFactors ⊆ P.image (fun q : Nat.Primes => (q : ℕ)) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    haveI : Fact p.Prime := ⟨hpp⟩
    rw [Finset.mem_image]
    refine ⟨⟨p, hpp⟩, ?_, rfl⟩
    by_contra hnot
    have hu := PadicInt.isUnit_den m (hmint ⟨p, hpp⟩ hnot)
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff] at hu
    exact (Nat.Prime.coprime_iff_not_dvd hpp).1 hu (Nat.dvd_of_mem_primeFactors hp)
  have h1 : m.den ∣ ∏ p ∈ m.den.primeFactors, p ^ m.den := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self m.den_ne_zero]
    rw [Finsupp.prod, Nat.support_factorization]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => pow_dvd_pow _ ?_
    exact (Nat.factorization_lt p m.den_ne_zero).le
  refine h1.trans ?_
  have : ∏ q ∈ P, (q : ℕ) ^ m.den = ∏ p ∈ P.image (fun q : Nat.Primes => (q : ℕ)), p ^ m.den := by
    rw [Finset.prod_image]
    intro a _ b _ hab
    exact Subtype.ext hab
  rw [this]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hsub

/-- Helper: $Q(cx) = c^2 Q(x)$ for an integer form over a commutative ring. Arguments: `Q`, `c`, `x`. -/
theorem evalIn_smul' {n : ℕ} {A : Type*} [CommRing A] (Q : QuadForm ℤ n) (c : A) (x : Fin n → A) :
    Q.evalIn A (c • x) = c ^ 2 * Q.evalIn A x := by
  simp only [QuadForm.evalIn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

end Helpers

/-- **Weak approximation for $\mathbb Q$ at finitely many primes** (Cassels, Ch. 10, proof of Thm. 7.1, p. 189). For a finite
set `P` of primes, local targets `z p` $\in \mathbb Q_p$ and `K`, there is a rational $y$ with $|y - z_p|_p \le p^{-K}$ for all
$p \in P$. Proof: rescale by $M = \prod_{p \in P} p^s$, approximate $M z_p \in \mathbb Z_p$ by integers modulo $p^{K+s}$
(`PadicInt.appr`), Chinese remainder theorem, divide by $M$. -/
@[kb "cassels1978" "Ch. 10, proof of Thm. 7.1, p. 189 (weak approximation of rationals)"]
theorem exists_rat_approx (P : Finset Nat.Primes) (z : ∀ p : Nat.Primes, ℚ_[(p : ℕ)]) (K : ℕ) :
    ∃ y : ℚ, ∀ p ∈ P, ‖(y : ℚ_[(p : ℕ)]) - z p‖ ≤ ((p : ℕ) : ℝ) ^ (-(K : ℤ)) := by
  classical
  have hb : ∀ p : Nat.Primes, ∃ s : ℕ, ‖z p‖ ≤ ((p : ℕ) : ℝ) ^ (s : ℤ) := by
    intro p
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    obtain ⟨s, hs⟩ := exists_pow_bound (n := 1) (fun _ => z p)
    exact ⟨s, hs 0⟩
  choose sp hsp using hb
  set s : ℕ := P.sup sp with hs
  have hint : ∀ p ∈ P, ‖(((∏ q ∈ P, (q : ℕ) ^ s : ℕ)) : ℚ_[(p : ℕ)]) * z p‖ ≤ 1 := by
    intro p hp
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.one_lt.le
    exact norm_mul_le_one hp ((hsp p).trans (zpow_le_zpow_right₀ hp1
      (by exact_mod_cast Finset.le_sup (f := sp) hp)))
  set w : ∀ p : Nat.Primes, ℤ_[(p : ℕ)] :=
    fun p => toZp (((∏ q ∈ P, (q : ℕ) ^ s : ℕ) : ℚ_[(p : ℕ)]) * z p) with hw
  set r : ℕ → ℤ := fun q => if h : q.Prime then
      haveI : Fact q.Prime := ⟨h⟩
      ((PadicInt.appr (w ⟨q, h⟩) (K + s) : ℕ) : ℤ) else 0 with hr
  obtain ⟨X, hX⟩ := Cassels.Ch11Sec9Steps.exists_int_modEq_primePow (P.image (fun q : Nat.Primes => (q : ℕ)))
    (by intro p hp; obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hp; exact q.2) (fun _ => K + s) r
  refine ⟨(X : ℚ) / (∏ q ∈ P, (q : ℕ) ^ s : ℕ), fun p hp => ?_⟩
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  refine norm_div_sub_le hp X (w p) (z p) (coe_toZp (hint p hp)) ?_
  have hrp : r (p : ℕ) = ((PadicInt.appr (w p) (K + s) : ℕ) : ℤ) := by
    simp only [hr]
    rw [dif_pos p.2]
    rfl
  have hmod := hX (p : ℕ) (Finset.mem_image_of_mem _ hp)
  rw [hrp] at hmod
  have hdvd : (((p : ℕ) ^ (K + s) : ℕ) : ℤ) ∣ X - ((PadicInt.appr (w p) (K + s) : ℕ) : ℤ) :=
    (Int.modEq_iff_dvd.1 hmod.symm)
  have h1 : ((p : ℕ) : ℤ_[(p : ℕ)]) ^ (K + s) ∣ ((X : ℤ_[(p : ℕ)]) - (PadicInt.appr (w p) (K + s) : ℕ)) := by
    have := map_dvd (Int.castRingHom ℤ_[(p : ℕ)]) hdvd
    simpa using this
  have h2 := PadicInt.appr_spec (K + s) (w p)
  rw [Ideal.mem_span_singleton] at h2
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
  have h3 := dvd_sub h1 h2
  convert h3 using 1
  ring

/-- Helper: the $\mathbb Z_p$-evaluation of an integer form, viewed in $\mathbb Q_p$, is the $\mathbb Q_p$-evaluation at the
coerced vector. Arguments: `f`, `p`, `x`. -/
theorem coe_eval_padic {n : ℕ} (f : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (x : Fin n → ℤ_[p]) :
    (((f.map (Int.castRingHom ℤ_[p])).eval x : ℤ_[p]) : ℚ_[p]) = f.evalIn ℚ_[p] (fun i => (x i : ℚ_[p])) := by
  have := Lattices.hom_eval_castHom f PadicInt.Coe.ringHom x
  rw [show ((f.map (Int.castRingHom ℤ_[p])).eval x : ℚ_[p]) =
    PadicInt.Coe.ringHom ((f.map (Int.castRingHom ℤ_[p])).eval x) from rfl, this]
  simp [QuadForm.evalIn, QuadForm.map, QuadForm.eval]

/-- **Cassels' Lemma 7.1 (coordinate form)** (Ch. 10, p. 187; a reformulation of Ch. 9, Theorem 1.5). Let `f` be an integral form in
`n` $\ge 4$ variables with $\det$ of its Hessian nonzero (`hf`) and indefinite over $\mathbb R$ (`hind`). Let `P` be a finite set of
primes containing $2$ (`h2`) and every prime dividing the determinant (`hdet`). Let $m \in \mathbb Q^\times$ (`m`, `hm`) be
$p$-integral for $p \notin P$ (`hmint`), and for $p \in P$ let `z p` $\in \mathbb Q_p^n$ satisfy $f(z_p) = m$ (`hz`). Then for every
`K` there is $\mathbf x \in \mathbb Q^n$ with $f(\mathbf x) = m$, $|x_i - (z_p)_i|_p \le p^{-K}$ for $p \in P$, and
$|x_i|_p \le 1$ for $p \notin P$. Proof: Cassels' rescaling by $M = \prod_{p \in P} p^s$ and `Siegel.exists_rep_approx`
(module docstring). -/
@[kb "cassels1978" "Ch. 10, Lemma 7.1, p. 187 (coordinate form)"]
theorem lemma71 {n : ℕ} (f : QuadForm ℤ n) (hn : 4 ≤ n) (hf : f.hessian.det ≠ 0)
    (hind : ∃ x y : Fin n → ℝ, f.evalIn ℝ x < 0 ∧ 0 < f.evalIn ℝ y)
    (P : Finset Nat.Primes) (h2 : ∀ p : Nat.Primes, p ∉ P → (p : ℕ) ≠ 2)
    (hdet : ∀ p : Nat.Primes, p ∉ P → ¬ ((p : ℕ) : ℤ) ∣ f.hessian.det)
    (m : ℚ) (hm : m ≠ 0) (hmint : ∀ p : Nat.Primes, p ∉ P → ‖(m : ℚ_[(p : ℕ)])‖ ≤ 1)
    (z : ∀ p : Nat.Primes, Fin n → ℚ_[(p : ℕ)]) (hz : ∀ p ∈ P, f.evalIn ℚ_[(p : ℕ)] (z p) = m) (K : ℕ) :
    ∃ x : Fin n → ℚ, f.evalIn ℚ x = m ∧
      (∀ p ∈ P, ∀ i, ‖(x i : ℚ_[(p : ℕ)]) - z p i‖ ≤ ((p : ℕ) : ℝ) ^ (-(K : ℤ))) ∧
      ∀ p : Nat.Primes, p ∉ P → ∀ i, ‖(x i : ℚ_[(p : ℕ)])‖ ≤ 1 := by
  classical
  have hb : ∀ p : Nat.Primes, ∃ s : ℕ, ∀ i, ‖z p i‖ ≤ ((p : ℕ) : ℝ) ^ (s : ℤ) := by
    intro p
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    exact exists_pow_bound (z p)
  choose sp hsp using hb
  set s : ℕ := max (P.sup sp) m.den with hs
  set M : ℕ := ∏ q ∈ P, (q : ℕ) ^ s with hM
  have hMpos : 0 < M := Finset.prod_pos fun q _ => pow_pos q.2.pos _
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hMpos.ne'
  have hden : m.den ∣ M := (den_dvd_prod P m hmint).trans
    (Finset.prod_dvd_prod_of_dvd _ _ fun q _ => pow_dvd_pow _ (le_max_right _ _))
  obtain ⟨c, hc⟩ := hden
  set a : ℤ := (M : ℤ) * c * m.num with ha_def
  have haq : (a : ℚ) = (M : ℚ) ^ 2 * m := by
    have h1 : (M : ℚ) = m.den * c := by exact_mod_cast hc
    have h2' : (m.den : ℚ) * m = m.num := by rw [mul_comm]; exact Rat.mul_den_eq_num m
    calc (a : ℚ) = M * c * m.num := by simp only [ha_def]; push_cast; ring
      _ = M * c * (m.den * m) := by rw [h2']
      _ = M * (m.den * c) * m := by ring
      _ = (M : ℚ) ^ 2 * m := by rw [← h1]; ring
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at haq
    exact (mul_ne_zero (pow_ne_zero 2 hMq) hm) haq.symm
  have hbint : ∀ p ∈ P, ∀ i, ‖(M : ℚ_[(p : ℕ)]) * z p i‖ ≤ 1 := by
    intro p hp i
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.one_lt.le
    exact norm_mul_le_one hp ((hsp p i).trans (zpow_le_zpow_right₀ hp1
      (by exact_mod_cast (Finset.le_sup (f := sp) hp).trans (le_max_left _ _))))
  set b : ∀ p : Nat.Primes, Fin n → ℤ_[(p : ℕ)] := fun p i => toZp ((M : ℚ_[(p : ℕ)]) * z p i) with hbdef
  have hbval : ∀ p ∈ P, ∀ i, ((b p i : ℤ_[(p : ℕ)]) : ℚ_[(p : ℕ)]) = M * z p i := by
    intro p hp i
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    exact coe_toZp (hbint p hp i)
  have hbeval : ∀ p ∈ P, (f.map (Int.castRingHom ℤ_[(p : ℕ)])).eval (b p) = a := by
    intro p hp
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    apply Subtype.ext
    rw [coe_eval_padic]
    have : (fun i => ((b p i : ℤ_[(p : ℕ)]) : ℚ_[(p : ℕ)])) = (M : ℚ_[(p : ℕ)]) • z p := by
      funext i; rw [hbval p hp i]; rfl
    rw [this, evalIn_smul', hz p hp]
    have h3 : ((a : ℚ) : ℚ_[(p : ℕ)]) = (((M : ℚ) ^ 2 * m : ℚ) : ℚ_[(p : ℕ)]) := by rw [haq]
    rw [Rat.cast_intCast] at h3
    push_cast at h3
    rw [PadicInt.coe_intCast, h3]
  have hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin n → ℤ_[p],
      (f.map (Int.castRingHom ℤ_[p])).eval x = a := by
    intro p _
    obtain ⟨pp, hpp⟩ : ∃ pp : Nat.Primes, (pp : ℕ) = p := ⟨⟨p, Fact.out⟩, rfl⟩
    subst hpp
    by_cases hpP : pp ∈ P
    · exact ⟨b pp, hbeval pp hpP⟩
    · obtain ⟨x, -, hx⟩ := Lattices.exists_primitive_padic_of_unimodular (pp : ℕ) (h2 pp hpP) f
        (hdet pp hpP) (by omega) a
      exact ⟨x, hx⟩
  obtain ⟨X, hX, hXc⟩ := Siegel.exists_rep_approx f hn hf hind ha hloc P b hbeval (K + s)
  refine ⟨fun i => (X i : ℚ) / M, ?_, ?_, ?_⟩
  · have : (fun i => (X i : ℚ) / M) = (M : ℚ)⁻¹ • (fun i => (X i : ℚ)) := by
      funext i; simp [div_eq_inv_mul]
    rw [this, evalIn_smul', Siegel.evalIn_intCast, hX, haq, inv_pow]
    exact inv_mul_cancel_left₀ (pow_ne_zero 2 hMq) m
  · intro p hp i
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    refine norm_div_sub_le (s := s) (K := K) hp (X i) (b p i) (z p i) (hbval p hp i) ?_
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    exact hXc p hp i
  · intro p hp i
    exact norm_div_le_one (s := s) hp (X i)

end QuadFormsKB.Cassels.Thm71Approx
