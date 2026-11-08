/-
# Cassels, Chapter 14, §6: the case $D = 4rs$

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §6, pp. 351–353.
-/
import QuadFormsKB.Literature.Cassels.Ch14.NamedProofs530
import QuadFormsKB.Literature.Cassels.Ch14.Thm51Groups530
import QuadFormsKB.Literature.Cassels.Ch14.Pell
import QuadFormsKB.Literature.Cassels.Ch14.Ambiguous

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Composition

open BinQF Binary FormClass Siegel

/-! ### The genus character at a prime dividing $D$ -/

section Char

variable (p : ℕ) [Fact p.Prime]

/-- Helper: the quadratic character of the residue of a $p$-adic unit, as a homomorphism $\mathbb Z_p^\times \to
\{\pm1\}$. -/
noncomputable def legUnit : ℤ_[p]ˣ →* ℤˣ :=
  (MulChar.toUnitHom (quadraticChar (ZMod p))).comp (Units.map (PadicInt.toZMod (p := p)).toMonoidHom)

theorem coe_legUnit (u : ℤ_[p]ˣ) :
    ((legUnit p u : ℤˣ) : ℤ) = quadraticChar (ZMod p) (PadicInt.toZMod (p := p) (u : ℤ_[p])) := by
  simp [legUnit]

variable (D : ℤ) [NonzeroDisc D]

/-- Helper: a unit represented by the principal form of a discriminant divisible by the odd prime $p$ is a square
modulo $p$. -/
theorem legUnit_norm (hp2 : p ≠ 2) (hpD : (p : ℤ) ∣ D) (u : ℤ_[p]ˣ)
    (hu : u ∈ (principalData ℤ_[p] D).subgroup) : legUnit p u = 1 := by
  obtain ⟨x, y, hxy⟩ := hu
  set φ := (PadicInt.toZMod (p := p)) with hφ
  have hD0 : (D : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hpD
  have hh := (principalData ℤ_[p] D).h
  have hh' := congrArg φ hh
  simp only [map_sub, map_pow, map_mul, map_ofNat, map_intCast] at hh'
  have hnorm := congrArg φ hxy
  simp only [PrinData.norm, map_add, map_mul, map_pow] at hnorm
  have hunit : φ (u : ℤ_[p]) ≠ 0 := by
    have : IsUnit (φ (u : ℤ_[p])) := u.isUnit.map φ
    exact this.ne_zero
  set X := φ x
  set Y := φ y
  set B := φ (principalData ℤ_[p] D).β
  set C := φ (principalData ℤ_[p] D).c
  have key : (4 : ZMod p) * φ (u : ℤ_[p]) = (2 * X + B * Y) ^ 2 := by
    rw [← hnorm]
    have : B ^ 2 - 4 * C = 0 := by
      have e : (principalData ℤ_[p] D).β ^ 2 - 4 * (principalData ℤ_[p] D).c = (D : ℤ_[p]) := hh
      have := congrArg φ e
      simp only [map_sub, map_pow, map_mul, map_ofNat, map_intCast] at this
      rw [hD0] at this
      exact this
    linear_combination (-(Y ^ 2)) * this
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h2
    have h2' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at h2'
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h2'
    exact hp2 this
  have h4 : (4 : ZMod p) * φ (u : ℤ_[p]) ≠ 0 :=
    mul_ne_zero (by rw [show (4 : ZMod p) = 2 ^ 2 by norm_num]; exact pow_ne_zero 2 h2) hunit
  have hZ : (2 * X + B * Y) ≠ 0 := by
    intro h; apply h4; rw [key, h]; ring
  have : quadraticChar (ZMod p) ((4 : ZMod p) * φ (u : ℤ_[p])) = 1 := by
    rw [key]; exact quadraticChar_sq_one' hZ
  rw [map_mul, show (4 : ZMod p) = 2 ^ 2 by norm_num, quadraticChar_sq_one' h2, one_mul] at this
  apply Units.ext
  rw [coe_legUnit, this]; rfl

/-- **The genus character at $p$:** for an odd prime $p \mid D$, the homomorphism $\mathcal G \to \{\pm1\}$ sending a
class to the Legendre symbol of a value of the class prime to $p$ (`charHom_mk`): the natural map
$\mathcal G \to \mathcal G_p = \mathbb Z_p^\times/N$ followed by the quadratic character of the residue. -/
noncomputable def charHom (hp2 : p ≠ 2) (hpD : (p : ℤ) ∣ D) : FormClass D →* ℤˣ :=
  (QuotientGroup.lift (principalData ℤ_[p] D).subgroup (legUnit p)
    (fun u hu => (MonoidHom.mem_ker).2 (legUnit_norm p D hp2 hpD u hu))).comp (localHom p D)

/-- **The genus character is the Legendre symbol of any value prime to $p$:** if a form $f$ of the class takes the
value $f(x, y)$ with $p \nmid f(x, y)$, then $\chi_p(\mathfrak C) = (f(x, y)/p)$. -/
theorem charHom_mk (hp2 : p ≠ 2) (hpD : (p : ℤ) ∣ D) (f : PrimForm D) (x y : ℤ)
    (h : ¬ (p : ℤ) ∣ f.1.eval x y) :
    ((charHom p D hp2 hpD (mk f) : ℤˣ) : ℤ) = legendreSym p (f.1.eval x y) := by
  have hv : IsUnit ((f.1.map (Int.castRingHom ℤ_[p])).eval ![x, y]) := by
    rw [eval_map_two, BinQF.eval_eq] at *
    have := isUnit_intCast_of_not_dvd p h
    simpa using this
  have hex : ∃ v, IsUnit ((f.1.map (Int.castRingHom ℤ_[p])).eval v) :=
    exists_unit_value (isPrimitiveZp_map p f.1 f.2.1)
  have h1 : localHom p D (mk f) = QuotientGroup.mk hv.unit := by
    show cosetOf (principalData ℤ_[p] D) (f.1.map (Int.castRingHom ℤ_[p])) _ = _
    exact cosetOf_eq _ four_ne_zero_padic (halfProp_padic p) (by rw [disc2_map_int, f.2.2]) _ hv
  have h2 : charHom p D hp2 hpD (mk f) = legUnit p hv.unit := by
    unfold charHom
    rw [MonoidHom.comp_apply, h1, QuotientGroup.lift_mk]
  rw [h2, coe_legUnit]
  unfold legendreSym
  congr 1
  rw [IsUnit.unit_spec, eval_map_two]
  simp [BinQF.eval_eq]

end Char

/-! ### The ambiguous forms $[a, 0, c]$ with $ac = -rs$ -/

section Amb

variable {r s : ℕ} [Fact r.Prime] [Fact s.Prime]

theorem rs_mod4 (hr : r % 4 = 1) (hs : s % 4 = 1) : ((r : ℤ) * s) % 4 = 1 := by
  have h1 : (r : ℤ) % 4 = 1 := by omega
  have h2 : (s : ℤ) % 4 = 1 := by omega
  rw [Int.mul_emod, h1, h2]; norm_num

theorem rs_pos : (0 : ℤ) < (r : ℤ) * s := by
  have := (Fact.out : r.Prime).pos
  have := (Fact.out : s.Prime).pos
  positivity

theorem nonzeroDisc_fourRS {D : ℤ} (hD : D = 4 * r * s) : NonzeroDisc D :=
  ⟨by rw [hD]; have := rs_pos (r := r) (s := s); nlinarith, by left; rw [hD, mul_assoc]; exact Int.mul_emod_right _ _⟩

/-- Helper: if $ac = -rs$ for distinct primes $r, s$, then $a$ and $c$ are coprime. -/
theorem isCoprime_of_mul_eq (hrs : r ≠ s) {a c : ℤ} (h : a * c = -((r : ℤ) * s)) : IsCoprime a c := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
  have hqa : (q : ℤ) ∣ a := (Int.natCast_dvd_natCast.mpr hqd).trans (Int.gcd_dvd_left ..)
  have hqc : (q : ℤ) ∣ c := (Int.natCast_dvd_natCast.mpr hqd).trans (Int.gcd_dvd_right ..)
  have hq2 : (q : ℤ) * q ∣ ((r * s : ℕ) : ℤ) := by
    have : (q : ℤ) * q ∣ a * c := mul_dvd_mul hqa hqc
    rw [h] at this
    push_cast
    exact (dvd_neg).1 this
  have hq2' : q * q ∣ r * s := by exact_mod_cast hq2
  have hsq : Squarefree (r * s) :=
    Nat.squarefree_mul_iff.2 ⟨(Nat.coprime_primes (Fact.out : r.Prime) (Fact.out : s.Prime)).2 hrs,
      (Fact.out : r.Prime).squarefree, (Fact.out : s.Prime).squarefree⟩
  exact hq.not_isUnit (hsq q hq2')

/-- Helper: the primitive form $[a, 0, c]$ of discriminant $D = 4rs$, for $ac = -rs$. -/
def amb0 (hrs : r ≠ s) {D : ℤ} (hD : D = 4 * r * s) (a c : ℤ) (h : a * c = -((r : ℤ) * s)) : PrimForm D :=
  ⟨BinQF.mk a 0 c, fun d h1 _ h3 => (isCoprime_of_mul_eq hrs h).isUnit_of_dvd' (by simpa using h1) (by simpa using h3),
    by simp only [BinQF.disc, a_mk, b_mk, c_mk]; rw [hD]; linear_combination (-4) * h⟩

@[simp] theorem amb0_a (hrs : r ≠ s) {D : ℤ} (hD : D = 4 * r * s) (a c : ℤ) (h : a * c = -((r : ℤ) * s)) :
    (amb0 hrs hD a c h).1.a = a := by simp [amb0]

@[simp] theorem amb0_b (hrs : r ≠ s) {D : ℤ} (hD : D = 4 * r * s) (a c : ℤ) (h : a * c = -((r : ℤ) * s)) :
    (amb0 hrs hD a c h).1.b = 0 := by simp [amb0]

@[simp] theorem amb0_c (hrs : r ≠ s) {D : ℤ} (hD : D = 4 * r * s) (a c : ℤ) (h : a * c = -((r : ℤ) * s)) :
    (amb0 hrs hD a c h).1.c = c := by simp [amb0]

variable {D : ℤ}

/-- Helper: two primitive forms $[a, 0, c]$ and $[a', 0, c']$ with $(a', c') = (a, c)$ or $(c, a)$ are properly
equivalent (the substitution $(x, y) \mapsto (y, -x)$ of determinant $1$ exchanges $a$ and $c$). -/
theorem mk_eq_of_b_zero (f g : PrimForm D) (hf : f.1.b = 0) (hg : g.1.b = 0)
    (h : (f.1.a = g.1.a ∧ f.1.c = g.1.c) ∨ (f.1.a = g.1.c ∧ f.1.c = g.1.a)) : mk f = mk g := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact congrArg FormClass.mk (Subtype.ext (ext_abc h1 (hf.trans hg.symm) h2))
  · refine mk_eq_mk.2 ((Binary.sLEquiv_iff _ _).2 ⟨0, 1, -1, 0, by norm_num, ext_abc ?_ ?_ ?_⟩)
    · simp [BinQF.subst, h2]
    · simp [BinQF.subst, hf, hg]
    · simp [BinQF.subst, h1]

end Amb

/-! ### The classes of $f(-1), f(r), f(s)$ -/

section Classes

variable {r s : ℕ} [Fact r.Prime] [Fact s.Prime] (hrs : r ≠ s) {D : ℤ} [NonzeroDisc D] (hD : D = 4 * r * s)

/-- The form $f(-1) = [-1, 0, rs]$ of discriminant $4rs$ (Cassels' (6.21)). -/
def formM : PrimForm D := amb0 hrs hD (-1) (r * s) (by ring)

/-- The form $f(r) = [r, 0, -s]$ of discriminant $4rs$ (Cassels' (6.22)). -/
def formR : PrimForm D := amb0 hrs hD r (-s) (by ring)

/-- The form $f(s) = [s, 0, -r]$ of discriminant $4rs$ (Cassels' (6.23)). -/
def formS : PrimForm D := amb0 hrs hD s (-r) (by ring)

theorem formM_one_iff : mk (formM hrs hD) = 1 ↔ ∃ x y : ℤ, x ^ 2 - ((r : ℤ) * s) * y ^ 2 = -1 := by
  rw [mk_eq_one_iff]
  constructor
  · rintro ⟨x, y, h⟩
    refine ⟨x, y, ?_⟩
    rw [BinQF.eval_eq] at h
    simp only [formM, amb0_a, amb0_b, amb0_c] at h
    linear_combination -h
  · rintro ⟨x, y, h⟩
    refine ⟨x, y, ?_⟩
    rw [BinQF.eval_eq]
    simp only [formM, amb0_a, amb0_b, amb0_c]
    linear_combination -h

theorem formR_one_iff : mk (formR hrs hD) = 1 ↔ ∃ x y : ℤ, (r : ℤ) * x ^ 2 - s * y ^ 2 = 1 := by
  rw [mk_eq_one_iff]
  constructor
  · rintro ⟨x, y, h⟩
    refine ⟨x, y, ?_⟩
    rw [BinQF.eval_eq] at h
    simp only [formR, amb0_a, amb0_b, amb0_c] at h
    linear_combination h
  · rintro ⟨x, y, h⟩
    refine ⟨x, y, ?_⟩
    rw [BinQF.eval_eq]
    simp only [formR, amb0_a, amb0_b, amb0_c]
    linear_combination h

theorem formS_one_iff : mk (formS hrs hD) = 1 ↔ ∃ x y : ℤ, (s : ℤ) * x ^ 2 - r * y ^ 2 = 1 := by
  rw [mk_eq_one_iff]
  constructor
  · rintro ⟨x, y, h⟩
    refine ⟨x, y, ?_⟩
    rw [BinQF.eval_eq] at h
    simp only [formS, amb0_a, amb0_b, amb0_c] at h
    linear_combination h
  · rintro ⟨x, y, h⟩
    refine ⟨x, y, ?_⟩
    rw [BinQF.eval_eq]
    simp only [formS, amb0_a, amb0_b, amb0_c]
    linear_combination h

/-- If $x^2 - rsy^2 = -1$ is soluble, then $f(r) \sim f(s)$ (properly): the substitution
$(x', y') \mapsto (sv\,x' + u\,y',\ u\,x' + rv\,y')$ of determinant $rsv^2 - u^2 = 1$. -/
theorem mk_formR_eq_formS_of_neg {u v : ℤ} (h : u ^ 2 - ((r : ℤ) * s) * v ^ 2 = -1) :
    mk (formR hrs hD) = mk (formS hrs hD) := by
  refine mk_eq_mk.2 ((Binary.sLEquiv_iff _ _).2 ⟨s * v, u, u, r * v, by linear_combination -h, ?_⟩)
  refine ext_abc ?_ ?_ ?_ <;> simp only [BinQF.subst, formR, formS, a_mk, b_mk, c_mk, amb0_a, amb0_b, amb0_c]
  · linear_combination (-(s : ℤ)) * h
  · ring
  · linear_combination (r : ℤ) * h

/-- If $ru^2 - sv^2 = 1$ is soluble, then $f(s) \sim f(-1)$: the substitution
$(x', y') \mapsto (v\,x' + ru\,y',\ -u\,x' - sv\,y')$. -/
theorem mk_formS_eq_formM_of_R {u v : ℤ} (h : (r : ℤ) * u ^ 2 - s * v ^ 2 = 1) :
    mk (formS hrs hD) = mk (formM hrs hD) := by
  refine mk_eq_mk.2 ((Binary.sLEquiv_iff _ _).2 ⟨v, r * u, -u, -(s * v), by linear_combination h, ?_⟩)
  refine ext_abc ?_ ?_ ?_ <;> simp only [BinQF.subst, formS, formM, a_mk, b_mk, c_mk, amb0_a, amb0_b, amb0_c]
  · linear_combination -h
  · ring
  · linear_combination ((r : ℤ) * s) * h

/-- If $sa^2 - rb^2 = 1$ is soluble, then $f(r) \sim f(-1)$: the substitution
$(x', y') \mapsto (b\,x' + sa\,y',\ -a\,x' - rb\,y')$. -/
theorem mk_formR_eq_formM_of_S {a b : ℤ} (h : (s : ℤ) * a ^ 2 - r * b ^ 2 = 1) :
    mk (formR hrs hD) = mk (formM hrs hD) := by
  refine mk_eq_mk.2 ((Binary.sLEquiv_iff _ _).2 ⟨b, s * a, -a, -(r * b), by linear_combination h, ?_⟩)
  refine ext_abc ?_ ?_ ?_ <;> simp only [BinQF.subst, formR, formM, a_mk, b_mk, c_mk, amb0_a, amb0_b, amb0_c]
  · linear_combination -h
  · ring
  · linear_combination ((r : ℤ) * s) * h

/-- One of $f(-1), f(r), f(s)$ is equivalent to the principal form (Legendre's descent, `negPell_trichotomy`). -/
theorem one_of_three (hr : r % 4 = 1) (hs : s % 4 = 1) :
    mk (formM hrs hD) = 1 ∨ mk (formR hrs hD) = 1 ∨ mk (formS hrs hD) = 1 := by
  rcases negPell_trichotomy (Fact.out : r.Prime) (Fact.out : s.Prime) hr hs hrs with h | h | h
  · exact Or.inl ((formM_one_iff hrs hD).2 h)
  · exact Or.inr (Or.inl ((formR_one_iff hrs hD).2 h))
  · exact Or.inr (Or.inr ((formS_one_iff hrs hD).2 h))

/-- **The classes of order at most $2$** (Cassels, Ch. 14, §6, p. 351: "there are eight forms in $\mathcal B$ … they
can be represented by $f(1), f(-1), f(r), f(s)$" modulo $\{e, e'\}$): every class $\mathfrak A$ of $\mathcal G_{4rs}$ with
$\mathfrak A^2 = 1$ is the class of $f(1) = [1, 0, -rs]$, $f(-1)$, $f(r)$ or $f(s)$. The ambiguous forms
$[a, a, c]$ do not occur because $4rs \equiv 4 \pmod{16}$ is of the shape $4d$, $d \equiv 1 \pmod 4$. -/
theorem amb_classes (hr : r % 4 = 1) (hs : s % 4 = 1) (A : FormClass D) (hA : A ^ 2 = 1) :
    A = 1 ∨ A = mk (formM hrs hD) ∨ A = mk (formR hrs hD) ∨ A = mk (formS hrs hD) := by
  have hrp : r.Prime := Fact.out
  have hsp : s.Prime := Fact.out
  obtain ⟨f, rfl, hamb⟩ := exists_ambiguousForm A hA
  have hdisc : f.1.b ^ 2 - 4 * f.1.a * f.1.c = 4 * r * s := by
    have h1 : f.1.b ^ 2 - 4 * f.1.a * f.1.c = D := f.2.2
    rw [h1, hD]
  have hrs4 := rs_mod4 hr hs
  rcases hamb with hb | hb
  · have hac : f.1.a * f.1.c = -((r : ℤ) * s) := by rw [hb] at hdisc; linarith
    have hrs0 : ((r : ℤ) * s) ≠ 0 := (rs_pos (r := r) (s := s)).ne'
    have hdvd : f.1.a.natAbs ∣ r * s := by
      have h1 : f.1.a ∣ (r : ℤ) * s := ⟨-f.1.c, by linear_combination hac⟩
      have h2 := Int.natAbs_dvd_natAbs.2 h1
      simpa [Int.natAbs_mul] using h2
    obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.mp hdvd
    have key : (f.1.a.natAbs : ℤ) = 1 ∨ (f.1.a.natAbs : ℤ) = r ∨ (f.1.a.natAbs : ℤ) = s ∨
        (f.1.a.natAbs : ℤ) = (r : ℤ) * s := by
      rw [← hk]
      rcases (Nat.dvd_prime hrp).mp hk₁ with rfl | rfl <;> rcases (Nat.dvd_prime hsp).mp hk₂ with rfl | rfl <;>
        simp
    have h8 : f.1.a = 1 ∨ f.1.a = -1 ∨ f.1.a = r ∨ f.1.a = -r ∨ f.1.a = s ∨ f.1.a = -s ∨
        f.1.a = (r : ℤ) * s ∨ f.1.a = -((r : ℤ) * s) := by
      rcases Int.natAbs_eq f.1.a with ha | ha <;> rcases key with h | h | h | h <;> omega
    have hc : ∀ α γ : ℤ, f.1.a = α → α * γ = -((r : ℤ) * s) → α ≠ 0 → f.1.c = γ := by
      intro α γ ha hγ h0
      apply mul_left_cancel₀ h0
      calc α * f.1.c = f.1.a * f.1.c := by rw [ha]
        _ = -((r : ℤ) * s) := hac
        _ = α * γ := hγ.symm
    have hr0 : (r : ℤ) ≠ 0 := by exact_mod_cast hrp.ne_zero
    have hs0 : (s : ℤ) ≠ 0 := by exact_mod_cast hsp.ne_zero
    rcases h8 with ha | ha | ha | ha | ha | ha | ha | ha
    · left
      exact (mk_eq_one_iff f).2 ⟨1, 0, by rw [BinQF.eval_eq, ha]; simp⟩
    · right; left
      have hc' := hc (-1) (r * s) ha (by ring) (by norm_num)
      exact mk_eq_of_b_zero f _ hb (amb0_b ..) (Or.inl ⟨by simp [formM, ha], by simp [formM, hc']⟩)
    · right; right; left
      have hc' := hc r (-s) ha (by ring) hr0
      exact mk_eq_of_b_zero f _ hb (amb0_b ..) (Or.inl ⟨by simp [formR, ha], by simp [formR, hc']⟩)
    · right; right; right
      have hc' := hc (-r) s ha (by ring) (neg_ne_zero.2 hr0)
      exact mk_eq_of_b_zero f _ hb (amb0_b ..) (Or.inr ⟨by simp [formS, ha], by simp [formS, hc']⟩)
    · right; right; right
      have hc' := hc s (-r) ha (by ring) hs0
      exact mk_eq_of_b_zero f _ hb (amb0_b ..) (Or.inl ⟨by simp [formS, ha], by simp [formS, hc']⟩)
    · right; right; left
      have hc' := hc (-s) r ha (by ring) (neg_ne_zero.2 hs0)
      exact mk_eq_of_b_zero f _ hb (amb0_b ..) (Or.inr ⟨by simp [formR, ha], by simp [formR, hc']⟩)
    · right; left
      have hc' := hc ((r : ℤ) * s) (-1) ha (by ring) hrs0
      exact mk_eq_of_b_zero f _ hb (amb0_b ..) (Or.inr ⟨by simp [formM, ha], by simp [formM, hc']⟩)
    · left
      have hc' := hc (-((r : ℤ) * s)) 1 ha (by ring) (neg_ne_zero.2 hrs0)
      exact (mk_eq_one_iff f).2 ⟨0, 1, by rw [BinQF.eval_eq, hc']; simp⟩
  · exfalso
    rw [hb] at hdisc
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' f.1.a
    · have hc_odd : f.1.c % 2 = 1 := by
        by_contra hne
        have hc2 : (2 : ℤ) ∣ f.1.c := by omega
        have h2 : IsUnit (2 : ℤ) := f.2.1 2 ⟨k, hk⟩ ⟨k, by rw [hb, hk]⟩ hc2
        rcases Int.isUnit_iff.mp h2 with h | h <;> omega
      obtain ⟨n, hn⟩ : ∃ n, f.1.c = 2 * n + 1 := ⟨f.1.c / 2, by omega⟩
      have hE : k ^ 2 - 2 * k * f.1.c = (r : ℤ) * s := by
        rw [hk] at hdisc
        have : 4 * (k ^ 2 - 2 * k * f.1.c - (r : ℤ) * s) = 0 := by linear_combination hdisc
        omega
      rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
      · have e : (r : ℤ) * s = 4 * (m ^ 2 - m * f.1.c) := by rw [← hE, hm]; ring
        omega
      · have e : (r : ℤ) * s = 4 * (m ^ 2 - 2 * m * n - n) - 1 := by rw [← hE, hm, hn]; ring
        omega
    · have : 4 * (k ^ 2 + k - (2 * k + 1) * f.1.c - (r : ℤ) * s) = -1 := by
        rw [hk] at hdisc; linear_combination hdisc
      omega

end Classes

end QuadFormsKB.Composition
