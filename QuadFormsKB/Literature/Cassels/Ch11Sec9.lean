/-
# Cassels, Chapter 11, Theorem 1.6 and §9: representation by definite forms (Tartakowsky's theorem)

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11: Theorem 1.6 (statement p. 204, proof
§9, pp. 235–249), Lemmas 9.1, 9.2, 9.3 and the Corollary to Lemma 9.3.

**Conventions.** Forms are `QuadForm ℤ n` ("integer-valued": $Q(x) = \sum_{i \le j} c_{ij}x_ix_j$ with $c_{ij} \in \mathbb Z$);
a form is *classically integral* (`IsClassicallyIntegral`) when $Q(x) = x^{\mathsf T}Ax$ with $A$ a symmetric integer matrix.
Cassels remarks (p. 235) that for Theorem 1.6 it does not matter which of the two notions is used; the library states
Theorem 1.6 for integer-valued forms (`TartakowskyAt`, the more general reading) and, separately, for classically
integral forms (`TartakowskyClassicalAt`). The determinant is Cassels' $d(Q) = \det(Q_{ij})$ with $Q(x) = \sum Q_{ij}x_ix_j$,
$Q_{ij} = Q_{ji}$, i.e. $d(Q) = \det H/2^n$ for the Hessian $H$ (`cassDet`). Indices are 0-based. Capital $Q$ is the form,
$n$ the number of variables. A vector is *primitive* when the coordinates have greatest common divisor $1$ (over $\mathbb Z$, as in
`Siegel.primRepSet`) or some coordinate is a unit (over $\mathbb Z_p$); comparison with Chapter 7's `IsPrimitiveVec` is
`isPrimitiveVec_int_iff`, `isPrimitiveVec_padic_iff_isUnit`. `PrimRepZ Q a`, `PrimRepZp p Q a` are "$a$ is primitively represented by $Q$
over $\mathbb Z$, over $\mathbb Z_p$".

**Formalized (proved).**
* Comparison of primitive vectors with the library's `Lattices.LatPrimitive` (`gcd_eq_one_iff_latPrimitive`); the
  local analogue `Lattices.LocPrimitive` over $\mathfrak o_p$ for $\mathbb Q_p$ is not compared (`isPrimitiveVec_padic_iff_isUnit`
  is the elementary form).
* Unprimitive version, even $n \ge 6$ (`tartakowskyUnprimitiveAt_of_even`): there is $N$ such that every $a \ge N$
  represented by $Q$ over every $\mathbb Z_p$ is represented over $\mathbb Z$. This is the version of Theorem 1.6 with the word
  "primitively" omitted, which Cassels (p. 235) says holds for forms isotropic at all $\mathbb Q_p$ (in particular $n \ge 5$);
  here it is derived unconditionally from `Siegel.thm_6_4_even_uncond` (Hanke 2004, Thm 6.4, the Hecke-bound proof of
  Tartakowsky's theorem over $\mathbb Q$; the library variant over a totally real number field with class number $1$ is
  `HilbertModular.tartakowsky_nf'`, which gives the same over $\mathbb Q$ and is not needed separately).
* Primitive version for squarefree $a$, even $n \ge 6$ (`tartakowskyPrimitive_squarefree_of_even`): for squarefree $a$
  every representation is primitive, so this part of Theorem 1.6 follows from the previous item. The general primitive
  version does *not* follow from the unprimitive one without Cassels' proof (Theorem 1.6 asks for a primitive
  representation of numbers that may be divisible by high powers of the bad primes).
* The reduction of the case $n = 4$ (`tartakowskyClassicalAt_four`, pp. 242–243): Lemmas 9.1 and 9.2 imply Theorem 1.6 for
  classically integral positive definite quaternary forms. This is Cassels' deduction: choose two odd primes $q_1 \ne q_2$
  with $d \in U_{q_i}^2$ (primes dividing $dk^2 - 1$, no Dirichlet theorem needed; `exists_prime_isUnitSquareAt`), take
  the maximum of the constants of Lemma 9.2 over the finitely many classes of determinant $d$ (Chapter 9, Theorem 1.1,
  `Siegel.finite_classes_of_det`; invariance of the statement $\mathcal R(Q,a)$ under $\mathrm{GL}_4(\mathbb Z)$,
  `locGlobal_of_isometricGL`), and split $a = a_1q_1^{m_1}q_2^{m_2}$.

**Named statements (not proved).**
* `TartakowskyStatement` (Theorem 1.6 in full, $n \ge 4$), with `TartakowskyAt n` for one dimension. A full proof is
  Cassels' §9: for $n \ge 5$ substitutions $x = \psi(y)$ splitting $Q$ into a binary form $g$ and an $(n-2)$-ary form $h$ with
  properties $(\alpha)$–$(\delta)$ (p. 236), the local lattices $\Gamma_p$ (three cases), the special prime $q$, Theorem 8.3 and
  its Corollary (formalized as `Lattices.exists_pow_represents_of_isotropic_four`, `Ch11Sec8Rep.lean`), Theorem 7.1
  (`Lattices.exists_sameProperSpinorGenus_primitive_rat`) and Chapter 9, Theorem 2.1 (weak approximation). For $n = 4$ one
  needs Lemmas 9.1, 9.2 (below), a Dirichlet-type choice of a prime (Cassels' footnote p. 246 says it can be avoided).
* `TartakowskyUnprimitiveRemark`: the remark (p. 235) that for $n \ge 5$ Theorem 1.6 holds with "primitively" omitted
  (proved here for even $n$). Cassels leaves the local lemma behind it "to the reader".
* `TartakowskyFailsAtThree`, `TartakowskyUnprimitiveFailsAtFour`: the two failures of Theorem 1.6 asserted on p. 235.
  The first follows from Lemma 7.1 and Note 2 to Theorem 7.1 (exceptional numbers of a ternary spinor genus,
  `Lattices.isExceptional_iff_mul_sq`). The second is Cassels' form (9.1), whose coefficients are lost in the
  machine-read text, so no concrete counterexample is stated here.
* `Lemma91`, `Lemma92` (quaternary case, with the reconstructions noted in their docstrings) and `Lemma93`,
  `Lemma93Cor` (local lemma on a regular isotropic quaternary form over $\mathbb Z_p$).

**Reconstructed (text lost or garbled).** The hypotheses of Lemma 9.1 (conditions on $a$, $q$, $d$, p. 241: "$a \in U_q$",
"$d \in U_q^2$", "$q \ne 2$"). The statement of the Corollary to Lemma 9.3 (p. 245), lost in the machine-read text, was
read from the page image: "for every $z \in \mathbb Z_p$ with $|z|_p < |Q(t)|_p$ there is $c \in \Delta_p$ with $Q(t + c) = z$"
($\Delta_p$ is Cassels' name for the lattice of Lemma 9.3). The spinor norm group in Lemma 9.3 (iii) is defined elementarily
(`UnitsInSpinorNorm`: products of an even number of reflections) because the library's spinor norm is for forms over
number fields, not over $\mathbb Q_p$ with $\mathbb Z_p$-coefficients.
-/
import QuadFormsKB.Siegel.Tartakowsky
import QuadFormsKB.Literature.Universal.Basic
import QuadFormsKB.Literature.Cassels.Ch9Sec3Finite
import QuadFormsKB.Literature.Cassels.Ch1Sec3
import QuadFormsKB.Literature.Cassels.Ch11Sec7
import QuadFormsKB.Literature.Cassels.Ch7.Thm31

open Matrix NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels

open QuadFormsKB.Siegel

variable {n : ℕ}

/-! ### Primitive vectors and primitive representations

The library convention (Chapter 9, Theorem 5.1, `Siegel.primRepSet`) is used: an integer vector is primitive when the
greatest common divisor of its coordinates is $1$, a $p$-adic vector when some coordinate is a unit. Comparison lemmas with
Cassels' Chapter 7 notion `IsPrimitiveVec` (member of a basis) are `isPrimitiveVec_int_iff`, `isPrimitiveVec_padic_iff_isUnit`, and with
`Lattices.LatPrimitive` `gcd_eq_one_iff_latPrimitive`. -/

/-- **Helper:** $\gcd(x_0, \dots, x_{m-1}) = 1$ exactly when every common divisor of the coordinates is a unit. Argument `x`. -/
theorem gcd_eq_one_iff_forall_dvd {m : ℕ} (x : Fin m → ℤ) :
    Finset.univ.gcd x = 1 ↔ ∀ e : ℤ, (∀ i, e ∣ x i) → IsUnit e := by
  constructor
  · intro h e he
    have : e ∣ Finset.univ.gcd x := Finset.dvd_gcd fun i _ => he i
    rw [h] at this
    exact isUnit_of_dvd_one this
  · intro h
    have hu : IsUnit (Finset.univ.gcd x) := h _ fun i => Finset.gcd_dvd (Finset.mem_univ i)
    have := Finset.normalize_gcd (s := (Finset.univ : Finset (Fin m))) (f := x)
    rw [normalize_eq_one.mpr hu] at this
    exact this.symm

/-- **Helper:** $\gcd(x_0, \dots, x_{m-1}) = 1$ exactly when the coordinates generate the unit ideal of $\mathbb Z$. -/
theorem gcd_eq_one_iff_span_eq_top {m : ℕ} (x : Fin m → ℤ) :
    Finset.univ.gcd x = 1 ↔ Ideal.span (Set.range x) = ⊤ := by
  rw [gcd_eq_one_iff_forall_dvd]
  constructor
  · intro h
    set I : Ideal ℤ := Ideal.span (Set.range x) with hIdef
    have hI := Submodule.IsPrincipal.span_singleton_generator I
    set g := Submodule.IsPrincipal.generator I
    have hgd : ∀ i, g ∣ x i := fun i => by
      have h1 : x i ∈ I := Ideal.subset_span ⟨i, rfl⟩
      rw [← hI] at h1
      exact Ideal.mem_span_singleton.mp h1
    have hu := h g hgd
    rw [← hI]
    exact Ideal.span_singleton_eq_top.mpr hu
  · intro h e he
    have h1 : (1 : ℤ) ∈ Ideal.span (Set.range x) := by rw [h]; exact Submodule.mem_top
    have h2 : Ideal.span (Set.range x) ≤ Ideal.span {e} := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact Ideal.mem_span_singleton.mpr (he i)
    exact isUnit_of_dvd_one (Ideal.mem_span_singleton.mp (h2 h1))

/-- **Comparison with Cassels' Chapter 7 notion** `IsPrimitiveVec ℤ` (member of a basis of $\mathbb Z^m$): an integer vector is a
member of a basis exactly when the greatest common divisor of its coordinates is $1$ (Chapter 7, Corollary to Theorem 3.1,
`isPrimitiveVec_iff_coprime`, with the standard basis). Argument `x`. -/
theorem isPrimitiveVec_int_iff {m : ℕ} (x : Fin m → ℤ) : IsPrimitiveVec ℤ x ↔ Finset.univ.gcd x = 1 := by
  rw [isPrimitiveVec_iff_coprime (Pi.basisFun ℤ (Fin m)) x, gcd_eq_one_iff_span_eq_top]
  have : Set.range ((Pi.basisFun ℤ (Fin m)).repr x) = Set.range x := by
    congr 1
  rw [this]

/-- **Helper: a $p$-adic integer is a unit exactly when $p$ does not divide it.** -/
theorem isUnit_padic_iff_not_dvd (p : ℕ) [Fact p.Prime] (z : ℤ_[p]) : IsUnit z ↔ ¬ (p : ℤ_[p]) ∣ z := by
  rw [PadicInt.isUnit_iff, ← PadicInt.norm_lt_one_iff_dvd]
  have := PadicInt.norm_le_one z
  constructor
  · intro h h2; linarith
  · intro h; exact le_antisymm this (not_lt.mp h)

/-- **Comparison with Cassels' Chapter 7 notion** `IsPrimitiveVec ℤ_[p]` (member of a basis of $\mathbb Z_p^m$): a $p$-adic vector is
a member of a basis exactly when some coordinate is a unit. Arguments: `p` the prime, `x` the vector. -/
theorem isPrimitiveVec_padic_iff_isUnit (p : ℕ) [Fact p.Prime] {m : ℕ} (x : Fin m → ℤ_[p]) :
    IsPrimitiveVec ℤ_[p] x ↔ ∃ i, IsUnit (x i) := by
  rw [isPrimitiveVec_iff_coprime (Pi.basisFun ℤ_[p] (Fin m)) x]
  have hr : Set.range ((Pi.basisFun ℤ_[p] (Fin m)).repr x) = Set.range x := by
    congr 1
  rw [hr]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have h2 : Ideal.span (Set.range x) ≤ Ideal.span {(p : ℤ_[p])} := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact Ideal.mem_span_singleton.mpr (by
        by_contra hd
        exact hne i ((isUnit_padic_iff_not_dvd p _).mpr hd))
    rw [h, top_le_iff, Ideal.span_singleton_eq_top] at h2
    exact (isUnit_padic_iff_not_dvd p _).mp h2 (dvd_refl _)
  · rintro ⟨i, hi⟩
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hi

/-- **$a$ is primitively represented by $Q$ over $\mathbb Z$** (Cassels, Ch. 11, p. 204): $a = Q(x)$ for some
$x \in \mathbb Z^n$ with coprime coordinates ($\gcd = 1$). This is `(Siegel.primRepSet Q a).Nonempty`
(`primRepZ_iff_nonempty`). Arguments: `Q` the form, `a` the represented integer. -/
def PrimRepZ (Q : QuadForm ℤ n) (a : ℤ) : Prop :=
  ∃ x : Fin n → ℤ, Finset.univ.gcd x = 1 ∧ Q.eval x = a

/-- `PrimRepZ` is non-emptiness of the library's set of primitive representations `Siegel.primRepSet`. -/
theorem primRepZ_iff_nonempty (Q : QuadForm ℤ n) (a : ℤ) : PrimRepZ Q a ↔ (primRepSet Q a).Nonempty :=
  ⟨fun ⟨x, h1, h2⟩ => ⟨x, h1, h2⟩, fun ⟨x, h1, h2⟩ => ⟨x, h1, h2⟩⟩

/-- **$a$ is primitively represented by $Q$ over $\mathbb Z_p$** (Cassels, Ch. 11, p. 204): $a = Q(x)$ for some
$x \in \mathbb Z_p^n$ with some coordinate a $p$-adic unit (the hypothesis form of Chapter 9, Theorem 5.1, `exists_sameGenus_primRep`;
`primRepZp_iff` compares with it). Arguments: `p` the prime, `Q` the form, `a` the integer. -/
def PrimRepZp (p : ℕ) [Fact p.Prime] (Q : QuadForm ℤ n) (a : ℤ) : Prop :=
  ∃ x : Fin n → ℤ_[p], (∃ i, IsUnit (x i)) ∧ Q.evalIn ℤ_[p] x = (a : ℤ_[p])

/-- `PrimRepZp` is the hypothesis shape used in Chapter 9, Theorem 5.1: $Q \otimes \mathbb Z_p$ evaluated at a vector with a unit
coordinate. -/
theorem primRepZp_iff (p : ℕ) [Fact p.Prime] (Q : QuadForm ℤ n) (a : ℤ) :
    PrimRepZp p Q a ↔
      ∃ x : Fin n → ℤ_[p], (∃ i, IsUnit (x i)) ∧ (Q.map (Int.castRingHom ℤ_[p])).eval x = a := by
  unfold PrimRepZp
  simp only [show ∀ y : Fin n → ℤ_[p], (Q.map (Int.castRingHom ℤ_[p])).eval y = Q.evalIn ℤ_[p] y from
    fun y => LocalDensity.evalIn_map_intCast ℤ_[p] Q y]

/-- **Helper: the image of $\mathcal O_{\mathbb Q}$ in $\mathbb Q$ is $\mathbb Z$.** Argument `q`: a rational number. -/
theorem mem_range_algebraMap_rat_iff (q : ℚ) :
    q ∈ (algebraMap (𝓞 ℚ) ℚ).range ↔ ∃ z : ℤ, (z : ℚ) = q := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp a.2
    refine ⟨y, ?_⟩
    exact (eq_intCast (algebraMap ℤ ℚ) y).symm.trans hy
  · rintro ⟨z, rfl⟩
    exact ⟨(z : 𝓞 ℚ), by simp⟩

/-- **Comparison with the library's `Lattices.LatPrimitive`** (Cassels, Ch. 11, p. 227): an integer vector $x$ has $\gcd = 1$
exactly when it is a primitive vector of the standard lattice $\mathbb Z^n$ (`Lattices.intVec` over $\mathcal O_{\mathbb Q}$) in the
sense of `Lattices.LatPrimitive`: $tx \in \mathbb Z^n$, $t \in \mathbb Q$, forces $t \in \mathbb Z$. Argument `x`: the integer vector. -/
theorem gcd_eq_one_iff_latPrimitive {n : ℕ} (x : Fin n → ℤ) :
    Finset.univ.gcd x = 1 ↔
      Lattices.LatPrimitive (Lattices.intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) (fun i => (x i : ℚ)) := by
  rw [gcd_eq_one_iff_forall_dvd]
  constructor
  · intro hx
    refine ⟨fun i => ⟨(x i : 𝓞 ℚ), by simp⟩, fun t ht => ?_⟩
    rw [mem_range_algebraMap_rat_iff]
    have hz : ∀ i, ∃ z : ℤ, (z : ℚ) = t * x i := fun i => by
      have := (mem_range_algebraMap_rat_iff _).mp (ht i)
      simpa using this
    choose z hz using hz
    have hdvd : ∀ i, (t.den : ℤ) ∣ x i := by
      intro i
      have h1 : (t.num : ℚ) * x i = (z i : ℚ) * t.den := by
        rw [hz i]
        have := Rat.mul_den_eq_num t
        rw [← this]; ring
      have h2 : t.num * x i = z i * t.den := by exact_mod_cast h1
      have hcop : IsCoprime (t.den : ℤ) t.num := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        have := t.reduced
        rw [Int.gcd_comm]
        simpa [Int.gcd, Nat.Coprime] using this
      refine hcop.dvd_of_dvd_mul_left ⟨z i, ?_⟩
      rw [h2]; ring
    have hu := hx _ hdvd
    have hden : t.den = 1 := by
      rcases Int.isUnit_iff.mp hu with h | h
      · exact_mod_cast h
      · have := t.den_pos; omega
    exact ⟨t.num, Rat.coe_int_num_of_den_eq_one hden⟩
  · rintro ⟨-, hprim⟩ e he
    choose y hy using he
    by_cases he0 : e = 0
    · exfalso
      subst he0
      have hx0 : ∀ i, x i = 0 := fun i => by simpa using hy i
      have := hprim (1 / 2 : ℚ) (by
        intro i
        refine ⟨0, ?_⟩
        simp [hx0 i])
      obtain ⟨z, hz⟩ := (mem_range_algebraMap_rat_iff _).mp this
      have : (2 : ℚ) * z = 1 := by rw [hz]; norm_num
      have : (2 : ℤ) * z = 1 := by exact_mod_cast this
      omega
    · have := hprim (1 / (e : ℚ)) (by
        intro i
        refine ⟨(y i : 𝓞 ℚ), ?_⟩
        have he' : (e : ℚ) ≠ 0 := by exact_mod_cast he0
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hy i]
        push_cast
        field_simp
        simp)
      obtain ⟨z, hz⟩ := (mem_range_algebraMap_rat_iff _).mp this
      have he' : (e : ℚ) ≠ 0 := by exact_mod_cast he0
      have h1 : (e : ℚ) * z = 1 := by rw [hz]; field_simp
      have h2 : e * z = 1 := by exact_mod_cast h1
      exact ⟨⟨e, z, h2, by rw [mul_comm]; exact h2⟩, rfl⟩

/-- **Helper: an invertible integer matrix preserves $\gcd = 1$.** If $NM = 1$ and $\gcd(x) = 1$ then $\gcd(Mx) = 1$. -/
theorem gcd_mulVec_eq_one {m : ℕ} {x : Fin m → ℤ} {M N : Matrix (Fin m) (Fin m) ℤ} (h : N * M = 1)
    (hx : Finset.univ.gcd x = 1) : Finset.univ.gcd (M *ᵥ x) = 1 := by
  rw [gcd_eq_one_iff_forall_dvd] at hx ⊢
  intro e he
  apply hx e
  intro j
  have hj : x j = (N *ᵥ (M *ᵥ x)) j := by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  rw [hj]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (he k) _

/-- **Helper: an invertible $p$-adic matrix preserves "some coordinate is a unit".** If $NM = 1$ and $x$ has a unit coordinate then so
does $Mx$. -/
theorem exists_unit_mulVec (p : ℕ) [Fact p.Prime] {m : ℕ} {x : Fin m → ℤ_[p]} {M N : Matrix (Fin m) (Fin m) ℤ_[p]}
    (h : N * M = 1) (hx : ∃ i, IsUnit (x i)) : ∃ i, IsUnit ((M *ᵥ x) i) := by
  by_contra hne
  push Not at hne
  obtain ⟨j, hj⟩ := hx
  have hd : (p : ℤ_[p]) ∣ x j := by
    have hj' : x j = (N *ᵥ (M *ᵥ x)) j := by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
    rw [hj']
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.dvd_sum fun k _ =>
      Dvd.dvd.mul_left (by by_contra hnd; exact hne k ((isUnit_padic_iff_not_dvd p _).mpr hnd)) _
  exact (isUnit_padic_iff_not_dvd p _).mp hj hd

/-- **Helper: $\mathbb Z$-equivalent forms primitively represent the same numbers over $\mathbb Z$.** If
$Q(Tx) = Q'(x)$ with $T \in \mathrm{GL}_n(\mathbb Z)$ and $Q'$ primitively represents $a$ then so does $Q$. -/
theorem primRepZ_of_isometricGL {Q Q' : QuadForm ℤ n} (h : IsometricGL Q Q') {a : ℤ} (hQ' : PrimRepZ Q' a) :
    PrimRepZ Q a := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨x, hx, hxa⟩ := hQ'
  exact ⟨T.val *ᵥ x, gcd_mulVec_eq_one (N := (T⁻¹).val) (Units.inv_mul T) hx, by rw [hT, hxa]⟩

/-- **Helper: $\mathbb Z$-equivalent forms primitively represent the same numbers over $\mathbb Z_p$.** -/
theorem primRepZp_of_isometricGL (p : ℕ) [Fact p.Prime] {Q Q' : QuadForm ℤ n} (h : IsometricGL Q Q') {a : ℤ}
    (hQ' : PrimRepZp p Q' a) : PrimRepZp p Q a := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨x, hx, hxa⟩ := hQ'
  set φ : ℤ →+* ℤ_[p] := Int.castRingHom ℤ_[p]
  refine ⟨T.val.map φ *ᵥ x, exists_unit_mulVec p (N := (T⁻¹).val.map φ) ?_ hx, ?_⟩
  · rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  · have h1 := eval_mulVec_map φ hT x
    have e1 : ∀ (R : QuadForm ℤ n) (y : Fin n → ℤ_[p]), (R.map φ).eval y = R.evalIn ℤ_[p] y :=
      fun R y => LocalDensity.evalIn_map_intCast ℤ_[p] R y
    rw [e1, e1] at h1
    rw [h1, hxa]

/-! ### The statements $\mathcal R(Q, a)$ and Theorem 1.6 -/

/-- **The proposition $\mathcal R(Q, a)$** (Cassels, Ch. 11, p. 241): *if $a$ is primitively represented by $Q$ over every
$\mathbb Z_p$, then $a$ is primitively represented by $Q$ over $\mathbb Z$.* Arguments: `Q` the form, `a` the integer. -/
def LocGlobal (Q : QuadForm ℤ n) (a : ℤ) : Prop :=
  (∀ (p : ℕ) [Fact p.Prime], PrimRepZp p Q a) → PrimRepZ Q a

/-- **Helper: $\mathcal R(Q, a)$ is invariant under $\mathbb Z$-equivalence of $Q$.** -/
theorem locGlobal_of_isometricGL {Q Q' : QuadForm ℤ n} (h : IsometricGL Q Q') {a : ℤ} (hQ' : LocGlobal Q' a) :
    LocGlobal Q a := fun hloc =>
  primRepZ_of_isometricGL h (hQ' fun p _ => primRepZp_of_isometricGL p (IsometricGL.symm h) (hloc p))

/-- **Theorem 1.6 for $n$ variables** (Cassels, Ch. 11, p. 204 and p. 235; Tartakowsky): for every positive definite
integer-valued form $Q$ in $n$ variables there is an integer $N$ such that every integer $a \ge N$ that is primitively
represented by $Q$ over $\mathbb Z_p$ for every prime $p$ is primitively represented by $Q$ over $\mathbb Z$.
Argument `n`: the number of variables (Cassels asserts it for $n \ge 4$). -/
@[kb "cassels1978" "Ch. 11, Thm. 1.6, p. 204 (proof §9, pp. 235–249), one dimension"]
def TartakowskyAt (n : ℕ) : Prop :=
  ∀ Q : QuadForm ℤ n, IntQF.PosDef Q → ∃ N : ℤ, ∀ a : ℤ, N ≤ a →
    (∀ (p : ℕ) [Fact p.Prime], PrimRepZp p Q a) → PrimRepZ Q a

/-- **Theorem 1.6 for classically integral forms in $n$ variables:** `TartakowskyAt` for the classically integral positive
definite forms only. `TartakowskyAt n` implies it (`TartakowskyAt.classical`). -/
@[kb "cassels1978" "Ch. 11, Thm. 1.6, p. 204 (classically integral forms), one dimension"]
def TartakowskyClassicalAt (n : ℕ) : Prop :=
  ∀ Q : QuadForm ℤ n, IntQF.PosDef Q → IsClassicallyIntegral Q → ∃ N : ℤ, ∀ a : ℤ, N ≤ a →
    (∀ (p : ℕ) [Fact p.Prime], PrimRepZp p Q a) → PrimRepZ Q a

/-- The integer-valued statement implies the classically integral one. -/
theorem TartakowskyAt.classical {n : ℕ} (h : TartakowskyAt n) : TartakowskyClassicalAt n :=
  fun Q hQ _ => h Q hQ

/-- **Cassels, Chapter 11, Theorem 1.6 (Tartakowsky), named statement.** For every $n \ge 4$ and every positive definite
integral form $Q$ in $n$ variables there is $N$ such that every $a \ge N$ primitively represented by $Q$ over all
$\mathbb Z_p$ is primitively represented over $\mathbb Z$. *Not proved* in the library for general $n$ (see the module
docstring for what a proof needs); the cases proved are `tartakowskyPrimitive_squarefree_of_even` and
`tartakowskyClassicalAt_four` (from Lemmas 9.1, 9.2). -/
@[kb "cassels1978" "Ch. 11, Thm. 1.6, p. 204 (proof §9, pp. 235–249)"]
structure TartakowskyStatement : Prop where
  /-- Theorem 1.6 in every dimension $n \ge 4$. -/
  holds : ∀ n : ℕ, 4 ≤ n → TartakowskyAt n

/-! ### The unprimitive version and the remark of p. 235 -/

/-- **Theorem 1.6 with "primitively" omitted, $n$ variables:** there is $N$ such that every $a \ge N$ represented by $Q$
over every $\mathbb Z_p$ is represented over $\mathbb Z$. -/
@[kb "cassels1978" "Ch. 11, remark after Thm. 1.6 (p. 235): 'primitively' omitted, one dimension"]
def TartakowskyUnprimitiveAt (n : ℕ) : Prop :=
  ∀ Q : QuadForm ℤ n, IntQF.PosDef Q → ∃ N : ℤ, ∀ a : ℤ, N ≤ a →
    (∀ (p : ℕ) [Fact p.Prime], Q.RepresentsIn ℤ_[p] a) → ∃ x : Fin n → ℤ, Q.eval x = a

/-- **The remark on p. 235, named statement.** For forms isotropic over all $\mathbb Q_p$, in particular for every
$n \ge 5$, Theorem 1.6 remains true with "primitively" omitted (Cassels leaves the local lemma "to the reader"). Proved here
for even $n$ (`tartakowskyUnprimitiveAt_of_even`). -/
@[kb "cassels1978" "Ch. 11, remark after Thm. 1.6 (p. 235), n ≥ 5"]
structure TartakowskyUnprimitiveRemark : Prop where
  /-- The unprimitive statement for every $n \ge 5$. -/
  holds : ∀ n : ℕ, 5 ≤ n → TartakowskyUnprimitiveAt n

/-- **Helper: representation over $\mathbb Z_p$ gives local representability** in the sense of Hanke 2004, Def. 3.5
(solvability modulo $p^k$ for all large $k$). Arguments: `p` the prime, `h` the representation. -/
theorem isLocallyRepresentedAt_of_representsIn (p : ℕ) [Fact p.Prime] {Q : QuadForm ℤ n} {m : ℤ}
    (h : Q.RepresentsIn ℤ_[p] m) : LocalDensity.IsLocallyRepresentedAt Q p m := by
  obtain ⟨x, hx⟩ := h
  refine Filter.Eventually.of_forall fun k => ?_
  have h1 := LocalDensity.evalIn_intForm_map (PadicInt.toZModPow (p := p) k) Q x
  rw [hx] at h1
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  unfold LocalDensity.repCount
  have hne : Nonempty {x : Fin n → ZMod (p ^ k) // Q.evalIn (ZMod (p ^ k)) x = (m : ZMod (p ^ k))} :=
    ⟨⟨_, by simpa using h1.symm⟩⟩
  exact Nat.card_pos

/-- **Cassels' remark after Theorem 1.6, proved for even $n \ge 6$** (p. 235): for a positive definite integral form $Q$ in
an even number $n \ge 6$ of variables there is $N$ such that every $a \ge N$ represented by $Q$ over every $\mathbb Z_p$
is represented over $\mathbb Z$. *Proof:* a representation over $\mathbb Z_p$ gives solvability modulo every $p^k$
(`isLocallyRepresentedAt_of_representsIn`), and `Siegel.thm_6_4_even_uncond` (Tartakowsky's theorem, Hanke 2004, Thm 6.4)
gives the bound; no input. -/
@[kb "cassels1978" "Ch. 11, remark after Thm. 1.6 (p. 235), n even ≥ 6 (via Hanke 2004, Thm 6.4)"]
theorem tartakowskyUnprimitiveAt_of_even (hn : 6 ≤ n) (heven : Even n) : TartakowskyUnprimitiveAt n := by
  intro Q hQ
  obtain ⟨M, hM⟩ := thm_6_4_even_uncond Q hQ hn heven
  refine ⟨M, fun a ha hloc => ?_⟩
  have ha0 : 0 ≤ a := le_trans (Int.natCast_nonneg M) ha
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  exact hM m (by exact_mod_cast ha) fun p hp =>
    haveI := Fact.mk hp
    isLocallyRepresentedAt_of_representsIn p (hloc p)

/-- **Helper: every representation of a squarefree integer is primitive.** If $a$ is squarefree and $Q(x) = a$ with
$x \in \mathbb Z^n$, then $x$ is primitive: a common divisor $e$ of the coordinates gives $e^2 \mid Q(x) = a$. -/
theorem primRepZ_of_squarefree {Q : QuadForm ℤ n} {a : ℤ} (ha : Squarefree a)
    (h : ∃ x : Fin n → ℤ, Q.eval x = a) : PrimRepZ Q a := by
  obtain ⟨x, hx⟩ := h
  refine ⟨x, (gcd_eq_one_iff_forall_dvd x).mpr fun e he => ha e ?_, hx⟩
  choose y hy using he
  have hxy : x = fun i => e * y i := funext hy
  have h2 := LocalDensity.evalIn_const_mul Q e y
  have h3 : Q.eval x = e ^ 2 * Q.eval y := by rw [hxy]; exact h2
  exact ⟨Q.eval y, by rw [← hx, h3]; ring⟩

/-- **Theorem 1.6 for squarefree $a$, even $n \ge 6$** (Cassels, Ch. 11, p. 204): for a positive definite integral form $Q$
in an even number $n \ge 6$ of variables there is $N$ such that every squarefree $a \ge N$ primitively represented by $Q$ over
every $\mathbb Z_p$ is primitively represented over $\mathbb Z$. Unconditional; the general (non-squarefree) case is
`TartakowskyStatement`. *Proof:* `tartakowskyUnprimitiveAt_of_even` and `primRepZ_of_squarefree`. -/
@[kb "cassels1978" "Ch. 11, Thm. 1.6, p. 204: squarefree a, n even ≥ 6 (via Hanke 2004, Thm 6.4)"]
theorem tartakowskyPrimitive_squarefree_of_even (hn : 6 ≤ n) (heven : Even n) (Q : QuadForm ℤ n)
    (hQ : IntQF.PosDef Q) : ∃ N : ℤ, ∀ a : ℤ, N ≤ a → Squarefree a →
      (∀ (p : ℕ) [Fact p.Prime], PrimRepZp p Q a) → PrimRepZ Q a := by
  obtain ⟨N, hN⟩ := tartakowskyUnprimitiveAt_of_even hn heven Q hQ
  refine ⟨N, fun a ha hsq hloc => primRepZ_of_squarefree hsq (hN a ha fun p _ => ?_)⟩
  obtain ⟨x, -, hx⟩ := hloc p
  exact ⟨x, by rw [hx]; simp⟩

/-! ### The failures asserted on p. 235 -/

/-- **Theorem 1.6 fails for $n = 3$** (Cassels, p. 235, "follows at once from Lemma 7.1 and Note 2 to Theorem 7.1"), named
statement: there is a positive definite ternary form $Q$ such that for every $N$ there is an integer $a \ge N$ primitively
represented by $Q$ over every $\mathbb Z_p$ but not over $\mathbb Z$. *Not proved:* a proof needs a ternary genus with an
exceptional spinor genus (`Lattices.isExceptional_iff_mul_sq`) and infinitely many exceptional numbers. -/
@[kb "cassels1978" "Ch. 11, p. 235: Thm. 1.6 fails for n = 3 (from Lemma 7.1 and Note 2 to Thm. 7.1)"]
def TartakowskyFailsAtThree : Prop :=
  ∃ Q : QuadForm ℤ 3, IntQF.PosDef Q ∧ ∀ N : ℤ, ∃ a : ℤ, N ≤ a ∧
    (∀ (p : ℕ) [Fact p.Prime], PrimRepZp p Q a) ∧ ¬ PrimRepZ Q a

/-- **Theorem 1.6 fails for $n = 4$ if "primitively" is omitted** (Cassels, p. 235, example (9.1), a form anisotropic over
$\mathbb Q_2$ with $3 \cdot 2^{2m}$ represented over every $\mathbb Z_p$ but not over $\mathbb Z$), named statement: there is a
positive definite quaternary form $Q$ such that for every $N$ there is an integer $a \ge N$ represented by $Q$ over every
$\mathbb Z_p$ but not over $\mathbb Z$. The coefficients of (9.1) are lost in the machine-read text. -/
@[kb "cassels1978" "Ch. 11, p. 235: Thm. 1.6 fails for n = 4 without 'primitively' (example (9.1))"]
def TartakowskyUnprimitiveFailsAtFour : Prop :=
  ∃ Q : QuadForm ℤ 4, IntQF.PosDef Q ∧ ∀ N : ℤ, ∃ a : ℤ, N ≤ a ∧
    (∀ (p : ℕ) [Fact p.Prime], Q.RepresentsIn ℤ_[p] a) ∧ ¬ ∃ x : Fin 4 → ℤ, Q.eval x = a

/-! ### Lemmas 9.1 and 9.2 (quaternary case) and the deduction of Theorem 1.6 for $n = 4$ -/

/-- **Cassels' determinant** $d(Q) = \det(Q_{ij})$, $Q(x) = \sum Q_{ij}x_ix_j$ with $Q_{ij} = Q_{ji}$: the determinant of
the Hessian divided by $2^n$, as a rational number. Argument `Q`: the form. -/
def cassDet (Q : QuadForm ℤ n) : ℚ := (Q.hessian.det : ℚ) / 2 ^ n

/-- **Comparison:** `cassDet` is the library's `Siegel.gramDet` (real-valued) with values in $\mathbb Q$. Argument `Q`: the form. -/
theorem cassDet_cast (Q : QuadForm ℤ n) : ((cassDet Q : ℚ) : ℝ) = gramDet Q := by
  unfold cassDet gramDet
  push_cast
  rfl

/-- **"$d \in U_q^2$"** (Cassels, Ch. 11, p. 241): the rational number $d$ is the square of a $q$-adic unit. Arguments: `q`
the prime, `d` the rational number. -/
def IsUnitSquareAt (q : ℕ) [Fact q.Prime] (d : ℚ) : Prop :=
  ∃ u : ℤ_[q], IsUnit u ∧ ((u : ℚ_[q])) ^ 2 = (d : ℚ_[q])

/-- **Lemma 9.1** (Cassels, Ch. 11, p. 241), named statement, quaternary case. Let $Q$ be a positive definite classically
integral form in $4$ variables of determinant $d = d(Q)$, $a > 0$ an integer, $q \ne 2$ a prime with $q \nmid a$ and
$d \in U_q^2$. Suppose $\mathcal R(Q', a)$ holds for all positive definite classically integral quaternary forms $Q'$ with
$d(Q') = d$. Then $\mathcal R(Q, q^ma)$ holds for every $m \ge 0$.

*Reconstruction:* the hypotheses of the printed statement are partly lost; "$a \in U_q$" is read as $q \nmid a$ and "$d \in U_q^2$"
as `IsUnitSquareAt`, as used in the proof (p. 241: $Q$ is $\mathbb Z_q$-equivalent to $2x_1x_2 + 2\delta x_3x_4$, $\delta^2 = d$).
"Integral" is read as classically integral, as in Chapter 9 (Theorem 1.1 there, finitely many classes of determinant $d$, is used in
the deduction of Theorem 1.6).
*Proved* in `Ch11Lemma91.lean` (`Ch11Lemma91.lemma91_holds`). The proof (pp. 241–242) replaces $Q$ by a $\mathbb Z$-equivalent form with $Q_{ij} \equiv 0 \pmod{q^m}$ in the
blocks lost in (9.24), and applies the hypothesis to $g(x) = q^{-m}Q(x_0, x_1, q^mx_2, q^mx_3)$ (integral of determinant $d$); a
formal proof needs the $q$-adic normal form of a unimodular quaternary lattice and approximation of a $\mathbb Z_q$-equivalence by a
$\mathbb Z$-equivalence (Chapter 9, Theorem 2.1). -/
@[kb "cassels1978" "Ch. 11, Lemma 9.1, p. 241"]
structure Lemma91 : Prop where
  /-- The statement of Lemma 9.1. -/
  holds : ∀ Q : QuadForm ℤ 4, IntQF.PosDef Q → IsClassicallyIntegral Q → ∀ a : ℤ, 0 < a →
    ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → ¬ (q : ℤ) ∣ a → IsUnitSquareAt q (cassDet Q) →
    (∀ Q' : QuadForm ℤ 4, IntQF.PosDef Q' → IsClassicallyIntegral Q' → cassDet Q' = cassDet Q → LocGlobal Q' a) →
    ∀ m : ℕ, LocGlobal Q ((q : ℤ) ^ m * a)

/-- **Lemma 9.2** (Cassels, Ch. 11, p. 242), named statement, quaternary case. Let $Q$ be a positive definite classically
integral form in $4$ variables of determinant $d$ and $q \ne 2$ a prime with $d \in U_q^2$. Then there is a constant
$N_1 = N_1(Q, q)$ such that $\mathcal R(Q, a)$ holds for all integers $a > N_1$ with $q \nmid a$.
*Proved* in `Ch11Lemma92Final.lean` (`Ch11L92.lemma92_holds`), unconditionally. The proof (pp. 243–249) follows the case
$n \ge 5$ with a one-dimensional $g$: local analysis at primes of the finite set $P$ using Lemma 9.3 and its Corollary at isotropic
primes, an auxiliary prime found by Dirichlet's theorem (footnote p. 246), Theorem 8.1 to produce a primitive vector with
prescribed $p$-adic approximations, the lattice $\Gamma$ of one spinor genus (Lemma 3.6, Corollary), Theorem 8.3 and its
Corollary (`Lattices.exists_pow_represents_of_isotropic_four`). -/
@[kb "cassels1978" "Ch. 11, Lemma 9.2, p. 242"]
structure Lemma92 : Prop where
  /-- The statement of Lemma 9.2. -/
  holds : ∀ Q : QuadForm ℤ 4, IntQF.PosDef Q → IsClassicallyIntegral Q →
    ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → IsUnitSquareAt q (cassDet Q) →
    ∃ N : ℤ, ∀ a : ℤ, N < a → ¬ (q : ℤ) ∣ a → LocGlobal Q a

/-- **Helper: primes $q$ with $D \in U_q^2$, with no Dirichlet theorem.** For a nonzero integer $D$ and a bound $B$ there is a prime
$q > B + 2$ such that $D$ is the square of a $q$-adic unit. *Proof:* any prime divisor $q$ of $Dk^2 - 1$, $k = (B+2)!$, does not divide
$k$, hence $q > B + 2$, and $D \equiv k^{-2}$ is a square modulo $q$; Hensel's lemma (`exists_sq_padic_of_isSquare`) lifts it. -/
theorem exists_prime_isUnitSquareAt (D : ℤ) (hD : D ≠ 0) (B : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime), B + 2 < q ∧ @IsUnitSquareAt q ⟨hq⟩ (D : ℚ) := by
  set k : ℕ := (B + 2).factorial with hk
  have hk2 : 2 ≤ k := by
    have : 2 ≤ B + 2 := by omega
    exact le_trans this (Nat.self_le_factorial _)
  set X : ℤ := D * (k : ℤ) ^ 2 - 1 with hX
  have hX1 : X.natAbs ≠ 1 := by
    intro h1
    have hk4 : (4 : ℤ) ≤ (k : ℤ) ^ 2 := by nlinarith [(by exact_mod_cast hk2 : (2 : ℤ) ≤ k)]
    have hDk : (4 : ℤ) ≤ |D * (k : ℤ) ^ 2| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (k : ℤ) ^ 2)]
      have : (1 : ℤ) ≤ |D| := Int.one_le_abs hD
      nlinarith
    rcases Int.natAbs_eq X with h | h
    · rw [h1] at h
      have h5 : D * (k : ℤ) ^ 2 = 2 := by simp at h; linarith
      rw [h5] at hDk
      norm_num at hDk
    · rw [h1] at h
      have h5 : D * (k : ℤ) ^ 2 = 0 := by simp at h; linarith
      rw [h5] at hDk
      norm_num at hDk
  set q : ℕ := X.natAbs.minFac with hq
  have hqp : q.Prime := Nat.minFac_prime hX1
  have hqX : (q : ℤ) ∣ X := Int.natCast_dvd.mpr (Nat.minFac_dvd _)
  have hqk : ¬ q ∣ k := by
    intro hdvd
    have h1 : (q : ℤ) ∣ D * (k : ℤ) ^ 2 := Dvd.dvd.mul_left (dvd_pow (Int.natCast_dvd_natCast.mpr hdvd) two_ne_zero) _
    have h2 : (q : ℤ) ∣ 1 := by
      have := dvd_sub h1 hqX
      simpa [hX] using this
    exact hqp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h2)
  have hqB : B + 2 < q := by
    by_contra hle
    push Not at hle
    exact hqk (Nat.dvd_factorial hqp.pos hle)
  refine ⟨q, hqp, hqB, ?_⟩
  have : Fact q.Prime := ⟨hqp⟩
  have hq2 : q ≠ 2 := by omega
  have hmod : (D : ZMod q) * (k : ZMod q) ^ 2 = 1 := by
    have h0 : ((X : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd X q).mpr hqX
    simp only [hX] at h0
    push_cast at h0
    linear_combination h0
  have hk0 : (k : ZMod q) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    simp at hmod
  have hD0 : (D : ZMod q) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    simp at hmod
  have hsq : IsSquare (D : ZMod q) := ⟨(k : ZMod q)⁻¹, by field_simp; linear_combination hmod⟩
  obtain ⟨z, hz⟩ := exists_sq_padic_of_isSquare hq2 hD0 hsq
  have hzu : IsUnit z := (isUnit_pow_iff two_ne_zero).1 (hz ▸ isUnit_intCast_padic' hD0)
  refine ⟨z, hzu, ?_⟩
  have : ((z ^ 2 : ℤ_[q]) : ℚ_[q]) = ((D : ℤ_[q]) : ℚ_[q]) := by rw [hz]
  simpa using this

/-- **Helper: a classically integral form has integral Cassels' determinant.** If $Q$ is classically integral, then
$d(Q) = D$ for the integer $D = \det A$ and $\det H = 2^n D$. -/
theorem exists_cassDet_eq {Q : QuadForm ℤ n} (hQ : IsClassicallyIntegral Q) :
    ∃ D : ℤ, cassDet Q = (D : ℚ) ∧ Q.hessian.det = 2 ^ n * D := by
  obtain ⟨A, -, -, hH⟩ := exists_symm_of_classicallyIntegral hQ
  refine ⟨A.det, ?_, by rw [hH, det_add_self]⟩
  rw [cassDet, hH, det_add_self]
  push_cast
  field_simp

/-- **Helper: a uniform constant for Lemma 9.2 over all forms of the same determinant.** Assuming Lemma 9.2, for a nonzero
integer $D$ and a prime $q \ne 2$ with $D \in U_q^2$ there is $N$ such that $\mathcal R(Q', a)$ holds for every positive definite
classically integral quaternary $Q'$ with $d(Q') = D$ and every $a > N$, $q \nmid a$. *Proof:* Cassels' maximum over the finitely many
classes (Chapter 9, Theorem 1.1): the constant of a representative serves the whole class (`locGlobal_of_isometricGL`). -/
theorem exists_uniform_bound (h2 : Lemma92) {D : ℤ} (hD : D ≠ 0) (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (hsq : IsUnitSquareAt q (D : ℚ)) :
    ∃ N : ℤ, ∀ Q : QuadForm ℤ 4, IntQF.PosDef Q → IsClassicallyIntegral Q → cassDet Q = (D : ℚ) →
      ∀ a : ℤ, N < a → ¬ (q : ℤ) ∣ a → LocGlobal Q a := by
  classical
  have key : ∀ c : QClass 4, ∃ N : ℤ, ∀ Q : QuadForm ℤ 4, classOf Q = c → IntQF.PosDef Q → IsClassicallyIntegral Q →
      cassDet Q = (D : ℚ) → ∀ a : ℤ, N < a → ¬ (q : ℤ) ∣ a → LocGlobal Q a := by
    intro c
    by_cases hex : ∃ Q₁ : QuadForm ℤ 4, classOf Q₁ = c ∧ IntQF.PosDef Q₁ ∧ IsClassicallyIntegral Q₁ ∧
        cassDet Q₁ = (D : ℚ)
    · obtain ⟨Q₁, hc, hpd, hci, hd⟩ := hex
      obtain ⟨N, hN⟩ := h2.holds Q₁ hpd hci q hq2 (by rw [hd]; exact hsq)
      refine ⟨N, fun Q hQc _ _ _ a ha hqa => ?_⟩
      have : IsometricGL Q Q₁ := classOf_eq_classOf_iff.mp (hQc.trans hc.symm)
      exact locGlobal_of_isometricGL this (hN a ha hqa)
    · exact ⟨0, fun Q hQc hpd hci hd => absurd ⟨Q, hQc, hpd, hci, hd⟩ hex⟩
  choose Nc hNc using key
  have hS := finite_classes_of_det 4 (by norm_num) hD
  obtain ⟨M, hM⟩ := (hS.image Nc).bddAbove
  refine ⟨M, fun Q hpd hci hd a ha hqa => ?_⟩
  have hmem : classOf Q ∈ {c : QClass 4 | ∃ f : QuadForm ℤ 4, classOf f = c ∧ IsClassicallyIntegral f ∧
      f.hessian.det = 2 ^ 4 * D} := by
    refine ⟨Q, rfl, hci, ?_⟩
    obtain ⟨D', hD', hdet⟩ := exists_cassDet_eq hci
    rw [hdet]
    have : (D' : ℚ) = D := by rw [← hD', hd]
    rw [show D' = D by exact_mod_cast this]
  exact hNc (classOf Q) Q rfl hpd hci hd a (lt_of_le_of_lt (hM ⟨classOf Q, hmem, rfl⟩) ha) hqa

/-- **Theorem 1.6 for $n = 4$ from Lemmas 9.1 and 9.2** (Cassels, Ch. 11, pp. 242–243; classically integral forms): for a positive
definite classically integral form $Q$ in $4$ variables there is $N$ such that every $a \ge N$ primitively represented over all
$\mathbb Z_p$ is primitively represented over $\mathbb Z$, *provided* Lemmas 9.1 and 9.2 hold (the named statements `Lemma91`,
`Lemma92`). Cassels' deduction: two odd primes $q_1 \ne q_2$ with $d \in U_{q_i}^2$, the constant $N_1(d, q_i)$ of Lemma 9.2 uniform
over the classes of determinant $d$, $N(Q) = N_1(d,q_1)N_1(d,q_2)$ (here with $+1$'s for the strict inequality), and for
$a = a_1q_1^{m_1}q_2^{m_2}$, $q_i \nmid a_1$, one of $a_1q_2^{m_2} > N_1(d,q_1)$, $a_1q_1^{m_1} > N_1(d,q_2)$ holds; then Lemma 9.2
gives $\mathcal R(\cdot, a_1q_2^{m_2})$ for all forms of determinant $d$ and Lemma 9.1 propagates it to $a$. -/
@[kb "cassels1978" "Ch. 11, Thm. 1.6 for n = 4 from Lemmas 9.1, 9.2, pp. 242–243"]
theorem tartakowskyClassicalAt_four (h1 : Lemma91) (h2 : Lemma92) : TartakowskyClassicalAt 4 := by
  intro Q hpd hci
  obtain ⟨D, hDQ, hdet⟩ := exists_cassDet_eq hci
  have hD : D ≠ 0 := by
    intro h0
    have := IntQF.PosDef.nondegenerate hpd
    exact this (by rw [QuadForm.Nondegenerate] at this; simp [hdet, h0])
  obtain ⟨q₁, hq₁, hB₁, hu₁⟩ := exists_prime_isUnitSquareAt D hD 0
  obtain ⟨q₂, hq₂, hB₂, hu₂⟩ := exists_prime_isUnitSquareAt D hD q₁
  have : Fact q₁.Prime := ⟨hq₁⟩
  have : Fact q₂.Prime := ⟨hq₂⟩
  have hne : q₁ ≠ q₂ := by omega
  obtain ⟨N₁, hN₁⟩ := exists_uniform_bound h2 hD q₁ (by omega) hu₁
  obtain ⟨N₂, hN₂⟩ := exists_uniform_bound h2 hD q₂ (by omega) hu₂
  set n₁ : ℕ := N₁.toNat with hn₁
  set n₂ : ℕ := N₂.toNat with hn₂
  refine ⟨(((n₁ + 1) * (n₂ + 1) : ℕ) : ℤ), fun a ha hloc => ?_⟩
  have ha0 : 0 ≤ a := le_trans (Int.natCast_nonneg _) ha
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  have hm : (n₁ + 1) * (n₂ + 1) ≤ m := by exact_mod_cast ha
  have hm0 : m ≠ 0 := by
    have : 0 < (n₁ + 1) * (n₂ + 1) := by positivity
    omega
  obtain ⟨e₁, b, hb1, hmb⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 q₁ hq₁.one_lt.ne'
  have hb0 : b ≠ 0 := by rintro rfl; simp at hmb; exact hm0 hmb
  obtain ⟨e₂, c, hc2, hbc⟩ := Nat.exists_eq_pow_mul_and_not_dvd hb0 q₂ hq₂.one_lt.ne'
  have hc0 : c ≠ 0 := by rintro rfl; simp at hbc; exact hb0 hbc
  have hc1 : ¬ q₁ ∣ c := fun h => hb1 (hbc ▸ Dvd.dvd.mul_left h _)
  have hq₁q₂ : ¬ q₁ ∣ q₂ ^ e₂ := fun h =>
    hne ((Nat.prime_dvd_prime_iff_eq hq₁ hq₂).mp (hq₁.dvd_of_dvd_pow h))
  have hq₂q₁ : ¬ q₂ ∣ q₁ ^ e₁ := fun h =>
    hne ((Nat.prime_dvd_prime_iff_eq hq₂ hq₁).mp (hq₂.dvd_of_dvd_pow h)).symm
  have hmeq : m = q₁ ^ e₁ * (q₂ ^ e₂ * c) := by rw [hmb, hbc]
  have hmeq' : m = q₂ ^ e₂ * (q₁ ^ e₁ * c) := by rw [hmeq]; ring
  have hdQ : IsUnitSquareAt q₁ (cassDet Q) := by rw [hDQ]; exact hu₁
  have hdQ' : IsUnitSquareAt q₂ (cassDet Q) := by rw [hDQ]; exact hu₂
  by_cases hcase : n₁ < q₂ ^ e₂ * c
  · have hpos : (0 : ℤ) < ((q₂ ^ e₂ * c : ℕ) : ℤ) := by
      have : 0 < q₂ ^ e₂ * c := Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ hq₂.ne_zero) hc0)
      exact_mod_cast this
    have hnd : ¬ (q₁ : ℤ) ∣ ((q₂ ^ e₂ * c : ℕ) : ℤ) := by
      rw [Int.natCast_dvd_natCast]
      intro h
      rcases (Nat.Prime.dvd_mul hq₁).mp h with h | h
      · exact hq₁q₂ h
      · exact hc1 h
    have hall : ∀ Q' : QuadForm ℤ 4, IntQF.PosDef Q' → IsClassicallyIntegral Q' → cassDet Q' = cassDet Q →
        LocGlobal Q' ((q₂ ^ e₂ * c : ℕ) : ℤ) := fun Q' hp' hc' hd' =>
      hN₁ Q' hp' hc' (by rw [hd', hDQ]) _ (lt_of_le_of_lt (Int.self_le_toNat N₁) (by exact_mod_cast hcase)) hnd
    have := h1.holds Q hpd hci _ hpos q₁ (by omega) hnd hdQ hall e₁
    have hcast : ((q₁ : ℤ) ^ e₁ * ((q₂ ^ e₂ * c : ℕ) : ℤ)) = (m : ℤ) := by rw [hmeq]; push_cast; ring
    rw [hcast] at this
    exact this hloc
  · have hcase' : q₂ ^ e₂ * c ≤ n₁ := not_lt.mp hcase
    have hlt : n₂ < q₁ ^ e₁ * c := by
      by_contra hle
      push Not at hle
      have h1 : m ≤ (q₂ ^ e₂ * c) * (q₁ ^ e₁ * c) := by
        have : (q₂ ^ e₂ * c) * (q₁ ^ e₁ * c) = m * c := by rw [hmeq']; ring
        rw [this]
        exact Nat.le_mul_of_pos_right m (Nat.pos_of_ne_zero hc0)
      have h2 : (q₂ ^ e₂ * c) * (q₁ ^ e₁ * c) ≤ n₁ * n₂ := Nat.mul_le_mul hcase' hle
      nlinarith
    have hpos : (0 : ℤ) < ((q₁ ^ e₁ * c : ℕ) : ℤ) := by
      have : 0 < q₁ ^ e₁ * c := Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ hq₁.ne_zero) hc0)
      exact_mod_cast this
    have hnd : ¬ (q₂ : ℤ) ∣ ((q₁ ^ e₁ * c : ℕ) : ℤ) := by
      rw [Int.natCast_dvd_natCast]
      intro h
      rcases (Nat.Prime.dvd_mul hq₂).mp h with h | h
      · exact hq₂q₁ h
      · exact hc2 h
    have hall : ∀ Q' : QuadForm ℤ 4, IntQF.PosDef Q' → IsClassicallyIntegral Q' → cassDet Q' = cassDet Q →
        LocGlobal Q' ((q₁ ^ e₁ * c : ℕ) : ℤ) := fun Q' hp' hc' hd' =>
      hN₂ Q' hp' hc' (by rw [hd', hDQ]) _ (lt_of_le_of_lt (Int.self_le_toNat N₂) (by exact_mod_cast hlt)) hnd
    have := h1.holds Q hpd hci _ hpos q₂ (by omega) hnd hdQ' hall e₂
    have hcast : ((q₂ : ℤ) ^ e₂ * ((q₁ ^ e₁ * c : ℕ) : ℤ)) = (m : ℤ) := by rw [hmeq']; push_cast; ring
    rw [hcast] at this
    exact this hloc

/-! ### Lemma 9.3 and its Corollary (local lemma on a regular isotropic quaternary form) -/

/-- **Helper: reflection** (the same map as `Lattices.symm`/`symmGL`, O'Meara §42E, which are defined only for forms over a number field
with values in a completion; here the form has coefficients in $\mathbb Z_p$ and the field is $\mathbb Q_p$, so the formula is restated) $\tau_v(x) = x - \frac{Q(x+v) - Q(x) - Q(v)}{Q(v)}\,v$ in a vector $v$ with $Q(v) \ne 0$, for a form
$Q$ over a field $K$. Arguments: `Q` the form, `v` the vector, `x` the argument. -/
def reflectionBy {K : Type*} [Field K] {m : ℕ} (Q : QuadForm K m) (v x : Fin m → K) : Fin m → K :=
  x - ((Q.eval (x + v) - Q.eval x - Q.eval v) / Q.eval v) • v

/-- **Helper: product of reflections** $\tau_{v_0} \circ \tau_{v_1} \circ \cdots$ for a list of vectors. Arguments: `Q` the
form, `vs` the list of vectors. -/
def rotationBy {K : Type*} [Field K] {m : ℕ} (Q : QuadForm K m) (vs : List (Fin m → K)) : (Fin m → K) → (Fin m → K) :=
  (vs.map (reflectionBy Q)).foldr (· ∘ ·) id

/-- **$\theta(\Delta) \supseteq U_p$ for the lattice $\mathbb Z_p^m$ with Gram form $Q$** (Cassels, Ch. 11, Lemma 9.3 (iii), via
Ch. 10): for every unit $u \in \mathbb Z_p^\times$ there are an even number of vectors $v_i \in \mathbb Q_p^m$ with $Q(v_i) \ne 0$ whose
product of reflections $\sigma$ (a rotation of the quadratic space) maps the lattice $\mathbb Z_p^m$ onto itself and has spinor norm
$\prod Q(v_i) \equiv u$ modulo squares of $\mathbb Q_p^\times$. (A rotation is a product of an even number of reflections, and the spinor
norm of such a product is $\prod Q(v_i)$ modulo squares; so this says every $p$-adic unit lies in $\theta(O^{+}(\Delta))$.) Arguments:
`p` the prime, `Q` the Gram form over $\mathbb Z_p$. -/
def UnitsInSpinorNorm (p : ℕ) [Fact p.Prime] {m : ℕ} (Q : QuadForm ℤ_[p] m) : Prop :=
  ∀ u : ℤ_[p], IsUnit u → ∃ vs : List (Fin m → ℚ_[p]), Even vs.length ∧
    (∀ v ∈ vs, (Q.map PadicInt.Coe.ringHom).eval v ≠ 0) ∧
    (∀ x : Fin m → ℚ_[p], (∀ i, ‖x i‖ ≤ 1) ↔ (∀ i, ‖rotationBy (Q.map PadicInt.Coe.ringHom) vs x i‖ ≤ 1)) ∧
    ∃ c : ℚ_[p], c ≠ 0 ∧ (vs.map (Q.map PadicInt.Coe.ringHom).eval).prod = (u : ℚ_[p]) * c ^ 2

/-- **The data and properties (i)–(iii) of Lemma 9.3** (Cassels, Ch. 11, p. 243). Let $Q$ be a quaternary form over $\mathbb Z_p$,
$t \in \mathbb Z_p^4$, $B$ a $4 \times 3$ matrix over $\mathbb Z_p$ whose columns $b_0, b_1, b_2$ are a basis of a lattice $\Delta$
in the $3$-dimensional space normal to $t$, and $g$ the Gram form of $\Delta$ ($g(y) = Q(By)$). Fields: `ne` $Q(t) \ne 0$;
`orth` each $b_j \perp t$; `indep` the columns are linearly independent over $\mathbb Q_p$ (so they span the normal space);
`gram` the definition of $g$; `rep` (i) $-Q(t)$ is represented by $Q$ on $\Delta$; `prim` (ii) if $c \in \Delta$ and
$|Q(t+c)|_p < |Q(t)|_p$ then $t + c$ is primitive in $\mathbb Z_p^4$; `units` (iii) $\theta(\Delta) \supseteq U_p$. -/
structure Lemma93Data (p : ℕ) [Fact p.Prime] (Q : QuadForm ℤ_[p] 4) (t : Fin 4 → ℤ_[p])
    (B : Matrix (Fin 4) (Fin 3) ℤ_[p]) (g : QuadForm ℤ_[p] 3) : Prop where
  ne : Q.eval t ≠ 0
  orth : ∀ j : Fin 3, Q.eval (t + fun i => B i j) = Q.eval t + Q.eval (fun i => B i j)
  indep : LinearIndependent ℚ_[p] (fun j : Fin 3 => fun i : Fin 4 => ((B i j : ℤ_[p]) : ℚ_[p]))
  gram : ∀ y : Fin 3 → ℤ_[p], g.eval y = Q.eval (B *ᵥ y)
  rep : ∃ y : Fin 3 → ℤ_[p], g.eval y = - Q.eval t
  prim : ∀ y : Fin 3 → ℤ_[p], ‖Q.eval (t + B *ᵥ y)‖ < ‖Q.eval t‖ → ∃ i, IsUnit ((t + B *ᵥ y) i)
  units : UnitsInSpinorNorm p g

/-- **Lemma 9.3** (Cassels, Ch. 11, p. 243), named statement: *let $Q$ be a regular isotropic quaternary form over $\mathbb Z_p$.
Then there are $t \in \mathbb Z_p^4$ with $Q(t) \ne 0$ and a lattice $\Delta = \Delta_p$ in the $3$-dimensional space normal to $t$ with
(i) $-Q(t)$ represented by $Q$ on $\Delta$; (ii) if $|Q(t+c)|_p < |Q(t)|_p$, $c \in \Delta$, then $t + c$ is a primitive element of
$\mathbb Z_p^4$; (iii) $\theta(\Delta) \supseteq U_p$.* "Regular" is `Nondegenerate`, "isotropic" is isotropic over $\mathbb Q_p$; see
`Lemma93Data` for the formal reading of (i)–(iii). *Not proved:* the proof (pp. 243–245) chooses a basis $e_0, \dots, e_3$ of $\mathbb Z_p^4$
with $Q(e_0) = 0$, rescales to totally isotropic-adapted vectors $r_i$ and a lattice with a hyperbolic basis, and verifies (ii) by a
congruence; formalizing (iii) needs the spinor norm of the binary and ternary lattices over $\mathbb Z_p$ (the library has it for
number fields only, Chapter 11 §3). -/
@[kb "cassels1978" "Ch. 11, Lemma 9.3, p. 243"]
structure Lemma93 : Prop where
  /-- The statement of Lemma 9.3. -/
  holds : ∀ (p : ℕ) [Fact p.Prime] (Q : QuadForm ℤ_[p] 4), Q.Nondegenerate →
    (Q.map PadicInt.Coe.ringHom).IsotropicIn ℚ_[p] →
    ∃ (t : Fin 4 → ℤ_[p]) (B : Matrix (Fin 4) (Fin 3) ℤ_[p]) (g : QuadForm ℤ_[p] 3), Lemma93Data p Q t B g

/-- **Corollary to Lemma 9.3** (Cassels, Ch. 11, p. 245), named statement (the displayed equation, lost in the machine-read
text, was read from the page image: $f(t + c) = z$ with $c \in \Delta_p$): for the vector $t$ and lattice $\Delta$ of Lemma 9.3, for every $z \in \mathbb Z_p$ with $|z|_p < |Q(t)|_p$ there
is $c \in \Delta$ with $Q(t + c) = z$. Formally: the data of Lemma 9.3 can be chosen so that this also holds. (It follows from the proof
of Lemma 9.3: $Q$ represents all of $Q(t)\,\mathbb Z_p^\times$ on $\Delta$, and $Q(t + c) = Q(t) + Q(c)$ for $c \perp t$.)
Cassels' proof of the Corollary is "Clear". *Not proved,* for the reasons of `Lemma93`. -/
@[kb "cassels1978" "Ch. 11, Corollary to Lemma 9.3, p. 245"]
structure Lemma93Cor : Prop where
  /-- The Corollary, together with the data of Lemma 9.3. -/
  holds : ∀ (p : ℕ) [Fact p.Prime] (Q : QuadForm ℤ_[p] 4), Q.Nondegenerate →
    (Q.map PadicInt.Coe.ringHom).IsotropicIn ℚ_[p] →
    ∃ (t : Fin 4 → ℤ_[p]) (B : Matrix (Fin 4) (Fin 3) ℤ_[p]) (g : QuadForm ℤ_[p] 3), Lemma93Data p Q t B g ∧
      ∀ z : ℤ_[p], ‖z‖ < ‖Q.eval t‖ → ∃ y : Fin 3 → ℤ_[p], Q.eval (t + B *ᵥ y) = z

end QuadFormsKB.Cassels
