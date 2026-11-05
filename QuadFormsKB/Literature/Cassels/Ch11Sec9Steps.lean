/-
# Cassels, Chapter 11, §9: the proof of Theorem 1.6 for $n \ge 5$ and the lemmas behind it

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, proof of Theorem 1.6 for $n \ge 5$
(pp. 236–241) and, for the special prime, the choice of $q$ on p. 240. Companion to `Ch11Sec9.lean`, which has the
statement of Theorem 1.6 (`TartakowskyAt`) and the case $n = 4$.

**Conventions.** Indices are 0-based. A dimension $n \ge 5$ is written $n = m + 2$ with $m \ge 3$: the first two variables
$y_0, y_1$ of Cassels' substitution are the variables of the binary form $g$ (his $y_1, y_2$), the remaining $m$
variables are those of $h$ (his $y_3, \dots, y_n$). The finite set $P$ of primes is a `Finset ℕ`. "Integral form" is an
integer-valued form `QuadForm ℤ n`; the determinant $d(f)$ of the text only enters through "$p \mid d(f)$", read as
$p \mid \det H$ for the Hessian $H$ of $f$ (this is the same set of primes, since $2 \in P$ anyway).

**Formalized (proved).**
* `tartakowskyAt_of_main_step`: Theorem 1.6 for $n \ge 5$ *given* the family of substitutions of the "key step"
  (p. 236), with the final deduction of p. 237 including the constant $N = \sup g^\psi(b)$ of (9.7).
* `exists_special_prime`: existence of the special prime $q$ of (9.19), (9.20) (p. 240, footnote); no Dirichlet theorem.
* `primRepZp_unit_smul`: if $f$ represents $a_p$ primitively over $\mathbb Z_p$, then also $u^2 a_p$ for every unit $u$
  (the remark before (9.9), p. 237).
* The elementary congruence arguments of the final stage (p. 241): the Chinese remainder theorem for prime powers
  (`exists_int_modEq_primePow`), lifting a primitive residue pair to a coprime integer pair
  (`exists_coprime_pair_congr`), the condition $C_3$ (`exists_unit_class_mod`) and their combination
  (`exists_pair_conditions`).

**Named statement (not proved).**
* `Thm16MainStep`: the existence of the finite family of substitutions $x = \psi(y)$ with properties $(\alpha)$–$(\delta)$
  (p. 236). Its proof is the construction of pp. 237–241: the local discussion at the primes of $P$ (isotropic primitive
  vectors $u_p, v_p$, the classes of $\mathbb Z_p / U_p^2$, Theorem 2.1 of Chapter 9 for a global primitive pair), the
  lattice $\Gamma$ with prescribed localizations $\Gamma_p$ (three kinds of prime; Theorem 1.1 of Chapter 9, Lemma 3.6 and
  its Corollary), the special prime $q$ with Theorem 8.3 for $(\gamma)$, and the neighbourhoods $D_p$ and the finite set
  $B$ for $(\delta)$. Rows of the coverage table: the whole structure is item r38; the contents of r39, r40, r42 are
  what is needed to *prove* its fields and appear here only through the elementary lemmas above.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec9

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11Sec9Steps

open QuadFormsKB.Cassels Function

/-! ### The family of substitutions and its properties $(\alpha)$–$(\delta)$ -/

/-- **A substitution $x = \psi(y)$ of Cassels' key step** (Ch. 11, pp. 236–237), as data: an integer matrix `S` (the
coefficients $s_{ij}$ of (9.3)), the binary form `g` $= g^\psi$ and the $m$-ary form `h` $= h^\psi$ of (9.5). Argument `m`:
the number of variables of $h$ (the dimension of $f$ is $m + 2$). -/
structure Subst (m : ℕ) where
  /-- The matrix $(s_{ij})$ of the substitution (9.3). -/
  S : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ
  /-- The binary form $g = g^\psi$ in the variables $y_0, y_1$. -/
  g : QuadForm ℤ 2
  /-- The $m$-ary form $h = h^\psi$ in the variables $y_2, \dots, y_{m+1}$. -/
  h : QuadForm ℤ m

/-- **Helper: the vector $(b_0, b_1, z_0, \dots, z_{m-1}) \in \mathbb Z^{m+2}$.** Arguments: `b₀ b₁` the first two
coordinates, `z` the remaining $m$. -/
def joinVec {m : ℕ} (b₀ b₁ : ℤ) (z : Fin m → ℤ) : Fin (m + 2) → ℤ :=
  Fin.cons (α := fun _ => ℤ) b₀ (Fin.cons (α := fun _ => ℤ) b₁ z)

/-- **(9.3)–(9.5):** `ψ` has $\det(s_{ij}) \ne 0$ and $f(\psi(y)) = g^\psi(y_0, y_1) + h^\psi(y_2, \dots, y_{m+1})$ for all
integer vectors $y$. Arguments: `f` the form, `ψ` the substitution. -/
def IsSplitting {m : ℕ} (f : QuadForm ℤ (m + 2)) (ψ : Subst m) : Prop :=
  ψ.S.det ≠ 0 ∧ ∀ (b₀ b₁ : ℤ) (z : Fin m → ℤ),
    f.eval (ψ.S *ᵥ joinVec b₀ b₁ z) = ψ.g.eval ![b₀, b₁] + ψ.h.eval z

/-- **"$a$ is primitively represented by $Q$ over $\mathbb Z_p$ for every $p \in P$"** (the hypothesis in $(\alpha)$ and
$(\delta)$). Arguments: `P` the finite set of primes, `Q` the form, `a` the integer. -/
def PrimRepZpOn {k : ℕ} (P : Finset ℕ) (Q : QuadForm ℤ k) (a : ℤ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ∈ P → PrimRepZp p Q a

/-- **"$c$ is representable by $Q$ over every $\mathbb Z_p$"** (hypothesis of $(\gamma)$; note that there is no
restriction to $p \in P$ and no primitivity, Cassels' footnote p. 236). Arguments: `Q` the form, `c` the integer. -/
def RepZpAll {k : ℕ} (Q : QuadForm ℤ k) (c : ℤ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], Q.RepresentsIn ℤ_[p] c

/-- **Property $(\gamma)$** (Cassels, Ch. 11, p. 236) for the form $h$: `q` is a prime not in $P$ and $k$ (Cassels' $m$)
is such that every positive integer $c$ divisible by $q^{2k}$ and representable by $h$ over every $\mathbb Z_p$ is
representable by $h$ over $\mathbb Z$. Arguments: `P` the finite set of primes, `h` the form, `q` the prime, `k` the exponent. -/
def GammaHolds {m : ℕ} (P : Finset ℕ) (h : QuadForm ℤ m) (q k : ℕ) : Prop :=
  q.Prime ∧ q ∉ P ∧ ∀ c : ℤ, 0 < c → (q : ℤ) ^ (2 * k) ∣ c → RepZpAll h c → ∃ z : Fin m → ℤ, h.eval z = c

/-- **Property $(\delta)$** (Cassels, Ch. 11, p. 236) for `ψ`, with the prime `q` and exponent `k` of $(\gamma)$: there is a
finite set $B$ of coprime pairs $(b_0, b_1)$ such that for every integer $a$ primitively represented by $g^\psi$ over every
$\mathbb Z_p$, $p \in P$, some pair in $B$ makes $c = a - g^\psi(b_0, b_1)$ satisfy all hypotheses of $(\gamma)$ except
possibly positivity, i.e. $q^{2k} \mid c$ and $c$ is representable by $h^\psi$ over every $\mathbb Z_p$. -/
def DeltaHolds {m : ℕ} (P : Finset ℕ) (ψ : Subst m) (q k : ℕ) : Prop :=
  ∃ B : Finset (ℤ × ℤ), (∀ b ∈ B, Int.gcd b.1 b.2 = 1) ∧ ∀ a : ℤ, PrimRepZpOn P ψ.g a →
    ∃ b ∈ B, (q : ℤ) ^ (2 * k) ∣ a - ψ.g.eval ![b.1, b.2] ∧ RepZpAll ψ.h (a - ψ.g.eval ![b.1, b.2])

/-- **The properties $(\alpha)$–$(\delta)$ of a finite family $\Psi$ of substitutions** (Cassels, Ch. 11, p. 236) for the form
`f` in $m + 2$ variables and the finite set `P` of primes. Fields: `split` each $\psi \in \Psi$ satisfies (9.3)–(9.5);
`alpha` $(\alpha)$: an integer primitively represented by $f$ over all $\mathbb Z_p$, $p \in P$, is so represented by $g^\psi$
for some $\psi \in \Psi$; `beta` $(\beta)$: if $\gcd(b_0, b_1) = 1$ then $\psi(b)$ is a primitive vector of $\mathbb Z^{m+2}$
for every $b = (b_0, b_1, z)$; `special` $(\gamma)$ and $(\delta)$: for each $\psi$ a prime $q \notin P$ and an exponent
with `GammaHolds` and `DeltaHolds`. -/
structure FamilyProps {m : ℕ} (f : QuadForm ℤ (m + 2)) (P : Finset ℕ) (Ψ : Finset (Subst m)) : Prop where
  /-- (9.3)–(9.5) for every member of the family. -/
  split : ∀ ψ ∈ Ψ, IsSplitting f ψ
  /-- Property $(\alpha)$. -/
  alpha : ∀ a : ℤ, PrimRepZpOn P f a → ∃ ψ ∈ Ψ, PrimRepZpOn P ψ.g a
  /-- Property $(\beta)$. -/
  beta : ∀ ψ ∈ Ψ, ∀ (b₀ b₁ : ℤ) (z : Fin m → ℤ), Int.gcd b₀ b₁ = 1 →
    Finset.univ.gcd (ψ.S *ᵥ joinVec b₀ b₁ z) = 1
  /-- Properties $(\gamma)$ and $(\delta)$. -/
  special : ∀ ψ ∈ Ψ, ∃ q k : ℕ, GammaHolds P ψ.h q k ∧ DeltaHolds P ψ q k

/-- **The key step of the proof of Theorem 1.6 for $n \ge 5$** (Cassels, Ch. 11, pp. 236–241), named statement: for every
positive definite integral form $f$ in $n = m + 2 \ge 5$ variables and every finite set $P$ of primes with $2 \in P$ and
containing every prime dividing the determinant of $f$, there is a finite family $\Psi$ of substitutions with the
properties $(\alpha)$–$(\delta)$ (`FamilyProps`). *Not proved:* see the module docstring for what the proof (pp. 237–241)
needs. The deduction of Theorem 1.6 from it is `tartakowskyAt_of_main_step`. It is proved from the smaller named statement
`Ch11Sec9Gamma.Thm16FamilyStep` (without $(\gamma)$, which is proved there from Theorem 8.3, Corollary):
`Ch11Sec9Gamma.thm16MainStep_of_familyStep`. -/
@[kb "cassels1978" "Ch. 11, proof of Thm. 1.6 for n ≥ 5, key step (α)–(δ), pp. 236–241"]
structure Thm16MainStep : Prop where
  /-- The family of substitutions exists. -/
  holds : ∀ m : ℕ, 3 ≤ m → ∀ f : QuadForm ℤ (m + 2), IntQF.PosDef f → ∀ P : Finset ℕ,
    (∀ p ∈ P, p.Prime) → 2 ∈ P → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ f.hessian.det → p ∈ P) →
    ∃ Ψ : Finset (Subst m), FamilyProps f P Ψ

/-- **Helper: the constant of (9.7) for one substitution.** If `ψ` has the data of $(\gamma)$, $(\delta)$ then there is $M$ such
that every integer $a \ge M$ primitively represented by $g^\psi$ over every $\mathbb Z_p$, $p \in P$, has the form
$a = g^\psi(b_0, b_1) + h^\psi(z)$ with $\gcd(b_0, b_1) = 1$. *Proof:* $M = 1 + \sum_{b \in B} |g^\psi(b)|$ makes
$c = a - g^\psi(b)$ positive for the pair $b \in B$ of $(\delta)$, and $(\gamma)$ applies. -/
theorem exists_bound_of_special {m : ℕ} {P : Finset ℕ} {ψ : Subst m} {q k : ℕ} (hγ : GammaHolds P ψ.h q k)
    (hδ : DeltaHolds P ψ q k) :
    ∃ M : ℤ, ∀ a : ℤ, M ≤ a → PrimRepZpOn P ψ.g a →
      ∃ (b₀ b₁ : ℤ) (z : Fin m → ℤ), Int.gcd b₀ b₁ = 1 ∧ ψ.g.eval ![b₀, b₁] + ψ.h.eval z = a := by
  obtain ⟨B, hB, hBa⟩ := hδ
  refine ⟨1 + ∑ b ∈ B, |ψ.g.eval ![b.1, b.2]|, fun a ha hloc => ?_⟩
  obtain ⟨b, hb, hdvd, hrep⟩ := hBa a hloc
  have hle : |ψ.g.eval ![b.1, b.2]| ≤ ∑ b ∈ B, |ψ.g.eval ![b.1, b.2]| :=
    Finset.single_le_sum (f := fun b : ℤ × ℤ => |ψ.g.eval ![b.1, b.2]|) (fun _ _ => abs_nonneg _) hb
  have hpos : 0 < a - ψ.g.eval ![b.1, b.2] := by
    have := le_abs_self (ψ.g.eval ![b.1, b.2])
    linarith
  obtain ⟨z, hz⟩ := hγ.2.2 _ hpos hdvd hrep
  exact ⟨b.1, b.2, z, hB b hb, by rw [hz]; ring⟩

/-- **Theorem 1.6 for $n \ge 5$ from the key step** (Cassels, Ch. 11, p. 237: "Once we have established $(\alpha)$, $(\beta)$,
$(\gamma)$, $(\delta)$ we are done"): if `Thm16MainStep` holds then `TartakowskyAt (m + 2)` for every $m \ge 3$.
*Proof* (Cassels'): take $P$ = $\{2\}$ together with the primes dividing $\det H$; for $a \ge N$ (the maximum of the constants
$M_\psi$ of (9.7) over $\psi \in \Psi$) primitively represented over all $\mathbb Z_p$, $(\alpha)$ gives $\psi$ with $a$ primitively
represented by $g^\psi$ over $P$, $(\delta)$ and $(\gamma)$ give $a = g^\psi(b_0, b_1) + h^\psi(z)$, and
$x = \psi(b_0, b_1, z)$ is primitive by $(\beta)$ with $f(x) = a$ by (9.5). Arguments: `hmain` the key step, `hm` the bound $3 \le m$. -/
@[kb "cassels1978" "Ch. 11, Thm. 1.6 for n ≥ 5 from the key step, p. 237"]
theorem tartakowskyAt_of_main_step (hmain : Thm16MainStep) {m : ℕ} (hm : 3 ≤ m) : TartakowskyAt (m + 2) := by
  classical
  intro f hpd
  have hdet : f.hessian.det ≠ 0 := IntQF.PosDef.nondegenerate hpd
  set P : Finset ℕ := insert 2 f.hessian.det.natAbs.primeFactors with hP
  have hPp : ∀ p ∈ P, p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Nat.prime_two
    · exact (Nat.mem_primeFactors.mp hp).1
  have hP2 : 2 ∈ P := Finset.mem_insert_self _ _
  have hPd : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ f.hessian.det → p ∈ P := by
    intro p hp hd
    refine Finset.mem_insert_of_mem (Nat.mem_primeFactors.mpr ⟨hp, ?_, Int.natAbs_ne_zero.mpr hdet⟩)
    exact Int.natCast_dvd.mp hd
  obtain ⟨Ψ, hΨ⟩ := hmain.holds m hm f hpd P hPp hP2 hPd
  have hM : ∀ ψ : Subst m, ∃ M : ℤ, ψ ∈ Ψ → ∀ a : ℤ, M ≤ a → PrimRepZpOn P ψ.g a →
      ∃ (b₀ b₁ : ℤ) (z : Fin m → ℤ), Int.gcd b₀ b₁ = 1 ∧ ψ.g.eval ![b₀, b₁] + ψ.h.eval z = a := by
    intro ψ
    by_cases hψ : ψ ∈ Ψ
    · obtain ⟨q, k, hγ, hδ⟩ := hΨ.special ψ hψ
      obtain ⟨M, hM⟩ := exists_bound_of_special hγ hδ
      exact ⟨M, fun _ => hM⟩
    · exact ⟨0, fun h => absurd h hψ⟩
  choose M hM using hM
  obtain ⟨N, hN⟩ := Finset.exists_le (Ψ.image M)
  refine ⟨N, fun a ha hloc => ?_⟩
  have hPa : PrimRepZpOn P f a := fun p _ _ => hloc p
  obtain ⟨ψ, hψ, hg⟩ := hΨ.alpha a hPa
  obtain ⟨b₀, b₁, z, hgcd, hsum⟩ := hM ψ hψ a (le_trans (hN _ (Finset.mem_image_of_mem M hψ)) ha) hg
  refine ⟨ψ.S *ᵥ joinVec b₀ b₁ z, hΨ.beta ψ hψ b₀ b₁ z hgcd, ?_⟩
  rw [(hΨ.split ψ hψ).2, hsum]

/-- **Theorem 1.6 for every $n \ge 5$ from the key step** (Cassels, Ch. 11, p. 237): corollary of
`tartakowskyAt_of_main_step`, written with the dimension $n$ instead of $m + 2$. Arguments: `hmain` the key step, `n` the
dimension, `hn` the bound $5 \le n$. -/
@[kb "cassels1978" "Ch. 11, Thm. 1.6 for n ≥ 5 from the key step, p. 237"]
theorem tartakowskyAt_of_main_step' (hmain : Thm16MainStep) (n : ℕ) (hn : 5 ≤ n) : TartakowskyAt n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact tartakowskyAt_of_main_step hmain (by omega)

/-! ### The special prime $q$ (p. 240, (9.19), (9.20)) -/

/-- **Helper: a unit square is not divisible by the prime.** If $D$ is the square of a $q$-adic unit then
$q \nmid D$. Arguments: `q` the prime, `D` the integer. -/
theorem not_dvd_of_isUnitSquareAt (q : ℕ) [Fact q.Prime] (D : ℤ) (h : IsUnitSquareAt q (D : ℚ)) : ¬ (q : ℤ) ∣ D := by
  obtain ⟨u, hu, hsq⟩ := h
  intro hd
  have h1 : ‖(D : ℤ_[q])‖ < 1 := (PadicInt.norm_int_lt_one_iff_dvd D).mpr hd
  have h2 : ‖u‖ = 1 := PadicInt.isUnit_iff.mp hu
  have h3 : ((D : ℤ) : ℚ_[q]) = (u : ℚ_[q]) ^ 2 := by rw [hsq]; simp
  have h4 : ‖(D : ℤ_[q])‖ = ‖u‖ ^ 2 := by
    rw [PadicInt.norm_def, PadicInt.norm_def, ← norm_pow]
    push_cast
    rw [h3]
  rw [h4, h2] at h1
  norm_num at h1

/-- **The special prime $q$ of Cassels, Ch. 11, p. 240, (9.19)–(9.20).** For nonzero integers $d_g$ (Cassels' $d(g)$) and
$d_h$ (his $d(h)$) and a finite set $P$ of primes there is a prime $q \notin P$ with $q \nmid d_h$, $q \ne 2$, and
$-d_g \in U_q^2$ (the negative of $d_g$ is the square of a $q$-adic unit); also $q \nmid d_g$. No Dirichlet theorem is needed (Cassels'
footnote uses the values of $x^2 + d(g) y$; here the primes dividing $-d_g k^2 - 1$ are used, `exists_prime_isUnitSquareAt`).
Arguments: `dg dh` the two determinants, `hg hh` their non-vanishing, `P` the finite set. -/
@[kb "cassels1978" "Ch. 11, existence of the special prime q, (9.19)–(9.20), p. 240"]
theorem exists_special_prime (dg dh : ℤ) (hg : dg ≠ 0) (hh : dh ≠ 0) (P : Finset ℕ) :
    ∃ (q : ℕ) (hq : q.Prime), q ∉ P ∧ ¬ (q : ℤ) ∣ dh ∧ ¬ (q : ℤ) ∣ dg ∧ q ≠ 2 ∧
      @IsUnitSquareAt q ⟨hq⟩ ((-dg : ℤ) : ℚ) := by
  obtain ⟨q, hq, hqB, hsq⟩ := exists_prime_isUnitSquareAt (-dg) (by simpa using hg) (P.sup id + dh.natAbs)
  have : Fact q.Prime := ⟨hq⟩
  refine ⟨q, hq, ?_, ?_, ?_, by omega, hsq⟩
  · intro hqP
    have := Finset.le_sup (f := id) hqP
    simp only [id] at this
    omega
  · intro hd
    have h1 : q ∣ dh.natAbs := Int.natCast_dvd.mp hd
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hh) h1
    omega
  · intro hd
    exact not_dvd_of_isUnitSquareAt q (-dg) hsq ((dvd_neg).mpr hd)

/-! ### The local scaling remark (p. 237, before (9.9)) -/

/-- **Scaling by a unit** (Cassels, Ch. 11, p. 237: "if $f(z)$ represents some element $a_p$ primitively then it represents
primitively all elements of $a_pU_p^2$"): if $x \in \mathbb Z_p^n$ has a unit coordinate then so does $ux$, and
$Q(ux) = u^2Q(x)$, for a $p$-adic unit $u$. Arguments: `p` the prime, `Q` the form, `x` the vector, `u` the unit. -/
@[kb "cassels1978" "Ch. 11, p. 237: primitive values come in classes of Z_p / U_p^2"]
theorem primRepZp_unit_smul (p : ℕ) [Fact p.Prime] {k : ℕ} (Q : QuadForm ℤ k) {x : Fin k → ℤ_[p]}
    (hx : ∃ i, IsUnit (x i)) {u : ℤ_[p]} (hu : IsUnit u) :
    (∃ i, IsUnit ((fun j => u * x j) i)) ∧
      Q.evalIn ℤ_[p] (fun j => u * x j) = u ^ 2 * Q.evalIn ℤ_[p] x := by
  refine ⟨?_, LocalDensity.evalIn_const_mul Q u x⟩
  obtain ⟨i, hi⟩ := hx
  exact ⟨i, hu.mul hi⟩

/-! ### Elementary congruence arguments of the final stage (pp. 240–241) -/

/-- **Helper: the Chinese remainder theorem for prime powers over $\mathbb Z$.** For a finite set `t` of primes, exponents
`k` and prescribed residues `r p` there is an integer $x$ with $x \equiv r_p \pmod{p^{k_p}}$ for all $p \in t$. -/
theorem exists_int_modEq_primePow (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (k : ℕ → ℕ) (r : ℕ → ℤ) :
    ∃ x : ℤ, ∀ p ∈ t, x ≡ r p [ZMOD ((p ^ k p : ℕ) : ℤ)] := by
  have hs : ∀ p ∈ t, p ^ k p ≠ 0 := fun p hp => pow_ne_zero _ (ht p hp).ne_zero
  have pp : Set.Pairwise (t : Set ℕ) (Nat.Coprime on fun p => p ^ k p) := by
    intro p hp p' hp' hne
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (ht p hp) (ht p' hp')).mpr hne)
  obtain ⟨x, hx⟩ := Nat.chineseRemainderOfFinset (fun p => (r p % ((p ^ k p : ℕ) : ℤ)).toNat)
    (fun p => p ^ k p) t hs pp
  refine ⟨(x : ℤ), fun p hp => ?_⟩
  have h1 := (Int.natCast_modEq_iff).mpr (hx p hp)
  have hpos : (0 : ℤ) ≤ r p % ((p ^ k p : ℕ) : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast hs p hp)
  have h2 : (((r p % ((p ^ k p : ℕ) : ℤ)).toNat : ℕ) : ℤ) = r p % ((p ^ k p : ℕ) : ℤ) := Int.toNat_of_nonneg hpos
  rw [h2] at h1
  exact h1.trans (Int.mod_modEq _ _)

/-- **Lifting a primitive residue pair to a coprime pair** (the assertion "clearly these conditions can be satisfied
simultaneously" for condition $C_1$, Cassels p. 241). Let `t` be a finite set of primes, `k p ≥ 1` exponents and
$(r_{0,p}, r_{1,p})$ residues, not both divisible by $p$. Then there are integers $b_0, b_1$ with $\gcd(b_0, b_1) = 1$ and
$b_i \equiv r_{i,p} \pmod{p^{k_p}}$ for all $p \in t$. *Proof:* take $b_0 \ne 0$ by the Chinese remainder theorem, and
$b_1 = x_1 + M\prod \ell$ with $M = \prod p^{k_p}$ and $\ell$ running over the primes dividing $b_0$ but not $x_1$. -/
theorem exists_coprime_pair_congr (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (k : ℕ → ℕ) (hk : ∀ p ∈ t, 1 ≤ k p)
    (r₀ r₁ : ℕ → ℤ) (hprim : ∀ p ∈ t, ¬ (p : ℤ) ∣ r₀ p ∨ ¬ (p : ℤ) ∣ r₁ p) :
    ∃ b₀ b₁ : ℤ, Int.gcd b₀ b₁ = 1 ∧ ∀ p ∈ t,
      b₀ ≡ r₀ p [ZMOD ((p ^ k p : ℕ) : ℤ)] ∧ b₁ ≡ r₁ p [ZMOD ((p ^ k p : ℕ) : ℤ)] := by
  classical
  set M : ℤ := ∏ p ∈ t, ((p ^ k p : ℕ) : ℤ) with hM
  have hMpos : 0 < M := Finset.prod_pos fun p hp => by
    have := (ht p hp).pos
    positivity
  have hdvdM : ∀ p ∈ t, ((p ^ k p : ℕ) : ℤ) ∣ M := fun p hp => Finset.dvd_prod_of_mem _ hp
  obtain ⟨x₀, hx₀⟩ := exists_int_modEq_primePow t ht k r₀
  obtain ⟨x₁, hx₁⟩ := exists_int_modEq_primePow t ht k r₁
  obtain ⟨b₀, hb₀ne, hb₀⟩ : ∃ b₀ : ℤ, b₀ ≠ 0 ∧ ∀ p ∈ t, b₀ ≡ r₀ p [ZMOD ((p ^ k p : ℕ) : ℤ)] := by
    by_cases h0 : x₀ = 0
    · refine ⟨M, hMpos.ne', fun p hp => ?_⟩
      have h1 : M ≡ 0 [ZMOD ((p ^ k p : ℕ) : ℤ)] := (Int.modEq_zero_iff_dvd).mpr (hdvdM p hp)
      have h2 := hx₀ p hp
      rw [h0] at h2
      exact h1.trans h2
    · exact ⟨x₀, h0, hx₀⟩
  set S : Finset ℕ := b₀.natAbs.primeFactors.filter (fun ℓ => ¬ (ℓ : ℤ) ∣ x₁) with hS
  set T : ℤ := ∏ ℓ ∈ S, (ℓ : ℤ) with hT
  -- a prime dividing `M * T` either lies in `t` or in `S`
  have hMT : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ M * T → (ℓ ∈ t ∨ ℓ ∈ S) := by
    intro ℓ hℓ hd
    have hpz : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
    rcases hpz.dvd_or_dvd hd with h | h
    · left
      obtain ⟨p, hp, hpd⟩ := (hpz.dvd_finsetProd_iff _).mp h
      have h1 : ℓ ∣ p ^ k p := Int.natCast_dvd_natCast.mp hpd
      have h2 : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ (ht p hp)).mp (hℓ.dvd_of_dvd_pow h1)
      rwa [h2]
    · right
      obtain ⟨s, hs, hsd⟩ := (hpz.dvd_finsetProd_iff _).mp h
      have hsp : s.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hs).1).1
      have h2 : ℓ = s := (Nat.prime_dvd_prime_iff_eq hℓ hsp).mp (Int.natCast_dvd_natCast.mp hsd)
      rwa [h2]
  refine ⟨b₀, x₁ + M * T, ?_, fun p hp => ⟨hb₀ p hp, ?_⟩⟩
  · by_contra hne
    obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd hne
    have hd0 : (ℓ : ℤ) ∣ b₀ :=
      (Int.natCast_dvd_natCast.mpr hℓd).trans (Int.gcd_dvd_left _ _)
    have hd1 : (ℓ : ℤ) ∣ x₁ + M * T :=
      (Int.natCast_dvd_natCast.mpr hℓd).trans (Int.gcd_dvd_right _ _)
    have hℓS : ¬ (ℓ : ℤ) ∣ x₁ → ℓ ∈ S := fun hx =>
      Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hℓ, Int.natCast_dvd.mp hd0, Int.natAbs_ne_zero.mpr hb₀ne⟩, hx⟩
    by_cases hx : (ℓ : ℤ) ∣ x₁
    · -- then ℓ ∣ M * T
      have hdMT : (ℓ : ℤ) ∣ M * T := (dvd_add_right hx).mp hd1
      rcases hMT ℓ hℓ hdMT with hlt | hlS
      · have hkℓ : (ℓ : ℤ) ∣ ((ℓ ^ k ℓ : ℕ) : ℤ) := by
          rw [Nat.cast_pow]
          exact dvd_pow_self _ (by have := hk ℓ hlt; omega)
        have hb0ℓ : b₀ ≡ r₀ ℓ [ZMOD (ℓ : ℤ)] := Int.ModEq.of_dvd hkℓ (hb₀ ℓ hlt)
        have e1 : x₁ ≡ r₁ ℓ [ZMOD (ℓ : ℤ)] := Int.ModEq.of_dvd hkℓ (hx₁ ℓ hlt)
        have c0 : (ℓ : ℤ) ∣ r₀ ℓ :=
          Int.modEq_zero_iff_dvd.mp (hb0ℓ.symm.trans (Int.modEq_zero_iff_dvd.mpr hd0))
        have c1 : (ℓ : ℤ) ∣ r₁ ℓ :=
          Int.modEq_zero_iff_dvd.mp (e1.symm.trans (Int.modEq_zero_iff_dvd.mpr hx))
        rcases hprim ℓ hlt with h | h
        · exact h c0
        · exact h c1
      · exact (Finset.mem_filter.mp hlS).2 hx
    · have hlS := hℓS hx
      have hdT : (ℓ : ℤ) ∣ M * T := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hlS) M
      exact hx ((dvd_add_left hdT).mp hd1)
  · have hdv : ((p ^ k p : ℕ) : ℤ) ∣ M * T := dvd_mul_of_dvd_left (hdvdM p hp) T
    have h1 : x₁ + M * T ≡ x₁ [ZMOD ((p ^ k p : ℕ) : ℤ)] := by
      simpa using (Int.ModEq.refl x₁).add (Int.modEq_zero_iff_dvd.mpr hdv)
    exact h1.trans (hx₁ p hp)

/-- **Helper: a binary form as a polynomial.** $g(x, y) = c_{00}x^2 + c_{01}xy + c_{11}y^2$ for the coefficients
$c_{ij}$ of `g`. Arguments: `g` the form, `x y` the integers. -/
theorem binary_eval (g : QuadForm ℤ 2) (x y : ℤ) :
    g.eval ![x, y] = g.coeff 0 0 * x ^ 2 + g.coeff 0 1 * (x * y) + g.coeff 1 1 * y ^ 2 := by
  have h10 : g.coeff 1 0 = 0 := g.upper (show (0 : Fin 2) < 1 by decide)
  simp [QuadForm.evalIn, Fin.sum_univ_two]
  ring

/-- **Condition $C_3$ of the final stage** (Cassels, Ch. 11, p. 241: "this is always possible since we have arranged that not
all the coefficients of $g$ are divisible by $p$"). Let $p \ne 2$ be a prime not dividing all the coefficients of the binary
form `g` and `a` an integer. Then there is a residue pair $(s_0, s_1)$, not both divisible by $p$, such that
$a - g(b_0, b_1)$ is not divisible by $p$ whenever $b_i \equiv s_i \pmod p$. -/
theorem exists_unit_class_mod (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (g : QuadForm ℤ 2)
    (hg : ¬ ∀ i j, (p : ℤ) ∣ g.coeff i j) (a : ℤ) :
    ∃ s₀ s₁ : ℤ, (¬ (p : ℤ) ∣ s₀ ∨ ¬ (p : ℤ) ∣ s₁) ∧ ∀ b₀ b₁ : ℤ, b₀ ≡ s₀ [ZMOD (p : ℤ)] →
      b₁ ≡ s₁ [ZMOD (p : ℤ)] → ¬ (p : ℤ) ∣ a - g.eval ![b₀, b₁] := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have key : ∃ s : ℤ × ℤ, (¬ (p : ℤ) ∣ s.1 ∨ ¬ (p : ℤ) ∣ s.2) ∧ ¬ (p : ℤ) ∣ a - g.eval ![s.1, s.2] := by
    by_contra hcon
    push Not at hcon
    have e1 := hcon (1, 0) (Or.inl (by simpa using hpz.not_dvd_one))
    have e2 := hcon (1, 1) (Or.inl (by simpa using hpz.not_dvd_one))
    have e3 := hcon (1, -1) (Or.inl (by simpa using hpz.not_dvd_one))
    have e4 := hcon (0, 1) (Or.inr (by simpa using hpz.not_dvd_one))
    simp only [binary_eval] at e1 e2 e3 e4
    apply hg
    have hsum : (p : ℤ) ∣ 2 * (a - g.coeff 0 0 - g.coeff 1 1) := by
      have := dvd_add e2 e3
      convert this using 1
      ring
    have hs : (p : ℤ) ∣ a - g.coeff 0 0 - g.coeff 1 1 := by
      rcases hpz.dvd_or_dvd hsum with h | h
      · exact absurd h h2
      · exact h
    have c00a : (p : ℤ) ∣ a - g.coeff 0 0 := by convert e1 using 1; ring
    have c11 : (p : ℤ) ∣ g.coeff 1 1 := by
      have := dvd_sub c00a hs
      convert this using 1
      ring
    have ha : (p : ℤ) ∣ a := by
      have := dvd_add (by convert e4 using 1; ring : (p : ℤ) ∣ a - g.coeff 1 1) c11
      convert this using 1
      ring
    have c00 : (p : ℤ) ∣ g.coeff 0 0 := by
      have := dvd_sub ha c00a
      convert this using 1
      ring
    have c01 : (p : ℤ) ∣ g.coeff 0 1 := by
      have := dvd_sub (dvd_sub (dvd_sub ha e2) c00) c11
      convert this using 1
      ring
    have h10 : g.coeff 1 0 = 0 := g.upper (show (0 : Fin 2) < 1 by decide)
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h10, c00, c01, c11]
  obtain ⟨⟨s₀, s₁⟩, hprim, hs⟩ := key
  refine ⟨s₀, s₁, hprim, fun b₀ b₁ h₀ h₁ hd => hs ?_⟩
  have hv : g.eval ![b₀, b₁] ≡ g.eval ![s₀, s₁] [ZMOD (p : ℤ)] := by
    rw [binary_eval, binary_eval]
    exact ((((Int.ModEq.refl _).mul (h₀.pow 2)).add ((Int.ModEq.refl _).mul (h₀.mul h₁))).add
      ((Int.ModEq.refl _).mul (h₁.pow 2)))
  have : a - g.eval ![s₀, s₁] ≡ a - g.eval ![b₀, b₁] [ZMOD (p : ℤ)] := (Int.ModEq.refl a).sub hv.symm
  exact (Int.modEq_zero_iff_dvd.mp (this.trans (Int.modEq_zero_iff_dvd.mpr hd)))

/-- **The congruence conditions $C_1$–$C_4$ combined** (Cassels, Ch. 11, p. 241: "clearly these conditions can be satisfied
simultaneously"). Let `g` be a binary form, `a` an integer, `t₂` a finite set of primes at which a residue class
$(r_{0,p}, r_{1,p}) \bmod p^{k_p}$ (primitive modulo $p$) is prescribed (conditions $C_2$ and $C_4$: closeness to $c_p$, and
$a - g(b_0, b_1) \equiv 0 \bmod q^{2m}$ once a class solving it modulo $q^{2m}$ is given), and `t₃` a disjoint finite set of odd
primes not dividing all coefficients of $g$ (condition $C_3$). Then there are $b_0, b_1$ with $\gcd(b_0, b_1) = 1$ ($C_1$), lying
in the prescribed classes at the primes of `t₂`, with $a - g(b_0, b_1)$ a $p$-adic unit at every $p \in$ `t₃`. -/
@[kb "cassels1978" "Ch. 11, final stage of proof of Thm. 1.6 (n ≥ 5), conditions C1–C4, p. 241"]
theorem exists_pair_conditions (g : QuadForm ℤ 2) (a : ℤ) (t₂ t₃ : Finset ℕ) (h₂ : ∀ p ∈ t₂, p.Prime)
    (h₃ : ∀ p ∈ t₃, p.Prime ∧ p ≠ 2 ∧ ¬ ∀ i j, (p : ℤ) ∣ g.coeff i j) (hd : Disjoint t₂ t₃) (k : ℕ → ℕ)
    (hk : ∀ p ∈ t₂, 1 ≤ k p) (r₀ r₁ : ℕ → ℤ) (hprim : ∀ p ∈ t₂, ¬ (p : ℤ) ∣ r₀ p ∨ ¬ (p : ℤ) ∣ r₁ p) :
    ∃ b₀ b₁ : ℤ, Int.gcd b₀ b₁ = 1 ∧
      (∀ p ∈ t₂, b₀ ≡ r₀ p [ZMOD ((p ^ k p : ℕ) : ℤ)] ∧ b₁ ≡ r₁ p [ZMOD ((p ^ k p : ℕ) : ℤ)]) ∧
      ∀ p ∈ t₃, ¬ (p : ℤ) ∣ a - g.eval ![b₀, b₁] := by
  classical
  have hs : ∀ p : ℕ, ∃ s : ℤ × ℤ, p ∈ t₃ → (¬ (p : ℤ) ∣ s.1 ∨ ¬ (p : ℤ) ∣ s.2) ∧ ∀ b₀ b₁ : ℤ,
      b₀ ≡ s.1 [ZMOD (p : ℤ)] → b₁ ≡ s.2 [ZMOD (p : ℤ)] → ¬ (p : ℤ) ∣ a - g.eval ![b₀, b₁] := by
    intro p
    by_cases hp : p ∈ t₃
    · obtain ⟨s₀, s₁, h1, h2⟩ := exists_unit_class_mod p (h₃ p hp).1 (h₃ p hp).2.1 g (h₃ p hp).2.2 a
      exact ⟨(s₀, s₁), fun _ => ⟨h1, h2⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hp⟩
  choose s hs using hs
  obtain ⟨b₀, b₁, hgcd, hcong⟩ := exists_coprime_pair_congr (t₂ ∪ t₃)
    (fun p hp => by
      rcases Finset.mem_union.mp hp with h | h
      · exact h₂ p h
      · exact (h₃ p h).1)
    (fun p => if p ∈ t₂ then k p else 1)
    (fun p hp => by
      by_cases h : p ∈ t₂
      · simpa [h] using hk p h
      · simp [h])
    (fun p => if p ∈ t₂ then r₀ p else (s p).1) (fun p => if p ∈ t₂ then r₁ p else (s p).2)
    (fun p hp => by
      by_cases h : p ∈ t₂
      · simpa [h] using hprim p h
      · have h3 : p ∈ t₃ := (Finset.mem_union.mp hp).resolve_left h
        simpa [h] using (hs p h3).1)
  refine ⟨b₀, b₁, hgcd, fun p hp => ?_, fun p hp => ?_⟩
  · have := hcong p (Finset.mem_union_left _ hp)
    simpa [hp] using this
  · have hp2 : p ∉ t₂ := Finset.disjoint_right.mp hd hp
    have := hcong p (Finset.mem_union_right _ hp)
    simp only [hp2, ite_false, pow_one] at this
    exact (hs p hp).2 b₀ b₁ this.1 this.2

end QuadFormsKB.Cassels.Ch11Sec9Steps
