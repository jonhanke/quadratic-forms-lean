import QuadFormsKB.Binary.GenusLocal

/-!
# The number of genera: $2^{t-1}$

Let $D < 0$ be a fundamental discriminant with $t$ distinct prime factors. The genera of primitive positive
definite forms of discriminant $D$ (classes of `Siegel.SameGenus`, i.e. local equivalence everywhere) are in
bijection with the sign vectors $(e_p)_{p \mid D} \in \{\pm 1\}^t$ with $\prod_p e_p = 1$
(`range_genusVec`), so there are exactly $2^{t-1}$ of them (`card_genera`).

* **Injectivity** is genus = local equivalence (`sameGenus_iff_formChar_eq`, local).
* **Product one** is the product relation `prod_formChar_eq_one` (quadratic reciprocity).
* **Every such vector occurs** (`exists_form_of_signs`): choose residues with the prescribed characters (Chinese
  remainder theorem), a prime $q$ in that residue class (**Dirichlet's theorem**, Mathlib's
  `Nat.forall_exists_prime_gt_and_eq_mod`), and $b$ with $b^2 \equiv D \pmod{4q}$ (possible since
  $\chi_D(q) = \prod_p \psi_p(q) = 1$); then $[q, b, (b^2 - D)/4q]$ has the given characters.

*Route.* The existence step is the only global input, and it is Dirichlet's theorem on primes in progressions,
which is **proved** in Mathlib (so the count is unconditional). A purely local construction would need, in place of
the prime $q$, an integer $a$ in the residue class all of whose prime factors split in $\mathbb{Q}(\sqrt D)$; that
is itself a Dirichlet-type statement, so Dirichlet is the cleanest correct route here.

Sources: Gauss, *Disq. Arith.* §§261, 287 (exactly half of the assignable characters occur); Cox, Theorem 3.15 and
Theorem 6.1; Buell, Theorem 4.1; Cassels, *Rational Quadratic Forms*, Ch. 14, Lemma 3.4, p. 340 (the order of $\prod_p \mathcal G_p$), and Thm. 5.1,
p. 343 (the image of the class group has index $2$; proved by counting ambiguous classes).
-/

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Binary

open BinQF Siegel

variable {D : ℤ}

/-! ### Primitive positive definite forms and their genera -/

/-- **The primitive positive definite forms of discriminant $D$**: $f$ primitive, $\operatorname{disc} f = D$,
$a > 0$ and $D < 0$ (`PosDef'`). -/
def PosForms (D : ℤ) : Type := {f : BinQF // Primitive f ∧ f.disc = D ∧ f.PosDef'}

/-- **Same genus** as a setoid on `PosForms D` (`Siegel.SameGenus`: equivalent over every $\mathbb{Z}_p$ and over
$\mathbb{R}$). -/
def genusSetoid (D : ℤ) : Setoid (PosForms D) where
  r f g := SameGenus f.1 g.1
  iseqv := ⟨fun _ => SameGenus.refl _, fun h => h.symm, fun h h' => h.trans h'⟩

/-- **The genera of primitive positive definite forms of discriminant $D$**: `PosForms D` modulo
`Siegel.SameGenus`. -/
def Genera (D : ℤ) : Type := Quotient (genusSetoid D)

/-! ### Sign vectors -/

/-- $\pm 1 \in \mathbb{Z}$ as a unit: $1$ if $z = 1$, else $-1$. -/
def toSign (z : ℤ) : ℤˣ := if z = 1 then 1 else -1

theorem coe_toSign {z : ℤ} (h : z = 1 ∨ z = -1) : ((toSign z : ℤˣ) : ℤ) = z := by
  rcases h with rfl | rfl <;> simp [toSign]

/-- **$\chi_p(f) = \pm 1$** for primitive $f$ and $p \mid D$. -/
theorem formChar_eq_one_or [IsQuadDisc D] {f : BinQF} (hf : Primitive f) (hD : f.disc = D) {p : ℕ}
    (hp : p.Prime) (hpD : (p : ℤ) ∣ D) : formChar f p = 1 ∨ formChar f p = -1 := by
  have h := genusChar_sq f.disc hp (not_dvd_charCoeff hf hp (hD ▸ hpD))
  rw [sq] at h
  exact mul_self_eq_one_iff.mp h

/-- **The genus vector** $(\chi_p(f))_{p \mid D} \in \{\pm 1\}^{t}$ of a form, indexed by the prime factors of
$|D|$. -/
def genusVec (D : ℤ) (f : BinQF) : D.natAbs.primeFactors → ℤˣ := fun p => toSign (formChar f p)

theorem coe_genusVec [IsQuadDisc D] {f : BinQF} (hf : Primitive f) (hD : f.disc = D)
    (p : D.natAbs.primeFactors) : ((genusVec D f p : ℤˣ) : ℤ) = formChar f p :=
  coe_toSign (formChar_eq_one_or hf hD (Nat.prime_of_mem_primeFactors p.2)
    (Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors p.2)))

/-- **The genus vector has product one** (`prod_formChar_eq_one`). -/
theorem prod_genusVec [IsQuadDisc D] {f : BinQF} (hf : Primitive f) (hD : f.disc = D) (hpos : f.PosDef') :
    ∏ p, genusVec D f p = 1 := by
  apply Units.ext
  rw [Units.coe_prod, Units.val_one]
  simp_rw [coe_genusVec hf hD]
  rw [Finset.prod_coe_sort D.natAbs.primeFactors (formChar f)]
  exact prod_formChar_eq_one hf hD hpos

/-- **Same genus iff same genus vector** (`sameGenus_iff_formChar_eq`). -/
theorem sameGenus_iff_genusVec_eq [IsQuadDisc D] {f g : BinQF} (hf : Primitive f) (hg : Primitive g)
    (hfD : f.disc = D) (hgD : g.disc = D) (hfpos : f.PosDef') (hgpos : g.PosDef') :
    SameGenus f g ↔ genusVec D f = genusVec D g := by
  rw [sameGenus_iff_formChar_eq hf hg hfD hgD hfpos hgpos]
  constructor
  · intro h; funext p; unfold genusVec; rw [h p p.2]
  · intro h p hp
    have := congrArg (fun e => ((e ⟨p, hp⟩ : ℤˣ) : ℤ)) h
    rwa [coe_genusVec hf hfD, coe_genusVec hg hgD] at this

/-! ### Counting sign vectors of product one -/

/-- **There are $2^{n-1}$ sign vectors of product one** in $\{\pm 1\}^n$, $n \ge 1$: the kernel of the surjective
product map $\{\pm 1\}^n \to \{\pm 1\}$. -/
theorem card_signVec_prod_one {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Nat.card {e : ι → ℤˣ // ∏ i, e i = 1} = 2 ^ (Fintype.card ι - 1) := by
  let P : (ι → ℤˣ) →* ℤˣ :=
    { toFun := fun e => ∏ i, e i
      map_one' := by simp
      map_mul' := fun a b => by simp [Finset.prod_mul_distrib] }
  have hsurj : Function.Surjective P := by
    intro u
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine ⟨Pi.mulSingle i₀ u, ?_⟩
    simp [P, Finset.prod_pi_mulSingle']
  have hidx : P.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  have hcard := Subgroup.card_mul_index P.ker
  rw [hidx, Nat.card_eq_fintype_card (α := ι → ℤˣ), Fintype.card_fun, Fintype.card_units_int] at hcard
  have hk : Nat.card P.ker = Nat.card {e : ι → ℤˣ // ∏ i, e i = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun e => MonoidHom.mem_ker)
  rw [← hk]
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card ι = n + 1 := ⟨Fintype.card ι - 1, by
    have := Fintype.card_pos (α := ι); omega⟩
  rw [hn, pow_succ] at hcard
  rw [hn, Nat.add_sub_cancel]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) hcard

/-! ### Every product-one sign vector occurs -/

/-- `charMod p` is a power of $p$: $8 = 2^3$, $p = p^1$. -/
theorem charMod_eq_pow (p : ℕ) : charMod p = p ^ (if p = 2 then 3 else 1) := by
  unfold charMod; split_ifs with h <;> simp [h]

/-- **Residues with prescribed characters:** for $p \mid D$ and $e = \pm 1$ there is $t \ge 0$, $p \nmid t$, with
$\psi_p(t) = e$ (a quadratic nonresidue for odd $p$; $3$ or $5$ at $p = 2$). -/
theorem exists_residue [IsQuadDisc D] {p : ℕ} (hp : p.Prime) (hpD : (p : ℤ) ∣ D) {e : ℤ}
    (he : e = 1 ∨ e = -1) : ∃ t : ℕ, genusChar D p t = e ∧ ¬ (p : ℤ) ∣ t := by
  rcases he with rfl | rfl
  · refine ⟨1, ?_, ?_⟩
    · simpa using (genusChar_mul D p 1 1 ▸ (by
        unfold genusChar; split_ifs <;> simp [jacobiSym.one_left]) : genusChar D p 1 = 1)
    · intro h
      have h1 : p ∣ 1 := by exact_mod_cast h
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  · by_cases hp2 : p = 2
    · subst hp2
      have hc := (two_dvd_iff_of_fund (D := D)).mp (by exact_mod_cast hpD)
      by_cases h24 : D % 32 = 24
      · refine ⟨5, ?_, by norm_num⟩
        rw [genusChar_two_eq, ite_eq_right (by omega), ite_eq_left h24]; decide
      · refine ⟨3, ?_, by norm_num⟩
        rw [genusChar_two_eq]
        split_ifs <;> decide
    · have : Fact p.Prime := ⟨hp⟩
      obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
      refine ⟨a.val, ?_, ?_⟩
      · rw [genusChar_of_ne_two D hp2, ← jacobiSym.legendreSym.to_jacobiSym p]
        rw [legendreSym.eq_neg_one_iff' p (a := a.val)]
        simpa using ha
      · intro h
        apply ha
        have : ((a.val : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
        rw [Int.cast_natCast, ZMod.natCast_zmod_val] at this
        rw [this]; exact ⟨0, by simp⟩

/-- **Every sign vector of product one is a genus vector** (Gauss, *Disq. Arith.* §287; Cox, Theorem 6.1 via
Dirichlet; Buell, Theorem 4.1): for a fundamental $D < 0$ and signs $(e_p)_{p \mid D}$ with $\prod_p e_p = 1$ there
is a primitive positive definite form $f$ of discriminant $D$ with $\chi_p(f) = e_p$ for all $p \mid D$.

Choose $k$ with $\psi_p(k) = e_p$ for all $p \mid D$ (Chinese remainder theorem, moduli $p$ and $8$), a prime
$q > |D|$ with $q \equiv k$ (**Dirichlet**, `Nat.forall_exists_prime_gt_and_eq_mod`), and $b \equiv D \pmod 2$ with
$b^2 \equiv D \pmod q$: possible as $\chi_D(q) = \prod_p \psi_p(q) = \prod_p e_p = 1$. Then
$f = [q, b, (b^2 - D)/4q]$. -/
@[kb "cox2013" "§6.A, Thm. 6.1 [unverified]; cassels1978 Ch. 14, Thm. 5.1, p. 343"]
theorem exists_form_of_signs [IsQuadDisc D] (hD : D < 0) (e : ℕ → ℤ)
    (he : ∀ p ∈ D.natAbs.primeFactors, e p = 1 ∨ e p = -1)
    (hprod : ∏ p ∈ D.natAbs.primeFactors, e p = 1) :
    ∃ f : BinQF, Primitive f ∧ f.disc = D ∧ f.PosDef' ∧ ∀ p ∈ D.natAbs.primeFactors, formChar f p = e p := by
  set S := D.natAbs.primeFactors
  have hN : D.natAbs ≠ 0 := by omega
  -- 1. residues with the prescribed characters
  have hres : ∀ p : ℕ, ∃ t : ℕ, p ∈ S → genusChar D p t = e p ∧ ¬ (p : ℤ) ∣ t := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨t, ht⟩ := exists_residue (Nat.prime_of_mem_primeFactors hp)
        (Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)) (he p hp)
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose t ht using hres
  -- 2. the Chinese remainder theorem
  have hS0 : ∀ p ∈ S, charMod p ≠ 0 := fun p hp => by
    rw [charMod_eq_pow]; exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hScop : (S : Set ℕ).Pairwise (Function.onFun Nat.Coprime charMod) := by
    intro p hp q hq hpq
    simp only [Function.onFun, charMod_eq_pow]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset t charMod S hS0 hScop
  set M := ∏ p ∈ S, charMod p
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr hS0
  have : NeZero M := ⟨hM0⟩
  have hkcop : Nat.Coprime k M := by
    refine Nat.Coprime.prod_right fun p hp => ?_
    rw [charMod_eq_pow]
    refine Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd
      (Nat.prime_of_mem_primeFactors hp)).mpr fun hpk => ?_).symm
    apply (ht p hp).2
    have h1 : (charMod p : ℤ) ∣ (t p : ℤ) - k := (Nat.modEq_iff_dvd.mp (hk p hp))
    have h2 : (p : ℤ) ∣ (charMod p : ℤ) := by
      rw [charMod_eq_pow]; push_cast; exact dvd_pow_self _ (by split_ifs <;> norm_num)
    have := dvd_add (h2.trans h1) (Int.natCast_dvd_natCast.mpr hpk)
    simpa using this
  -- 3. Dirichlet's theorem
  obtain ⟨q, hqD, hq, hqk⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    ((ZMod.isUnit_iff_coprime k M).mpr hkcop) D.natAbs
  have hqk' : q ≡ k [MOD M] := (ZMod.natCast_eq_natCast_iff q k M).mp hqk
  have hq2 : q ≠ 2 := by have := three_le_natAbs (D := D); omega
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hqndvd : ¬ (q : ℤ) ∣ D := by
    intro h
    have := Nat.le_of_dvd (by omega) (Int.natCast_dvd.mp h)
    omega
  have hqcop : Nat.Coprime q D.natAbs :=
    (Nat.Prime.coprime_iff_not_dvd hq).mpr fun h => hqndvd (Int.natCast_dvd.mpr h)
  have hqchar : ∀ p ∈ S, genusChar D p q = e p := by
    intro p hp
    rw [← (ht p hp).1]
    apply genusChar_congr
    have h1 : q ≡ t p [MOD charMod p] :=
      (Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem _ hp) hqk').trans (hk p hp)
    have := Nat.modEq_iff_dvd.mp h1.symm
    exact_mod_cast this
  -- 4. `χ_D(q) = 1`, so `D` is a square mod `q`
  have hkron : kronZ D (q : ZMod D.natAbs) = 1 := by
    rw [← prod_genusChar_eq_kronZ q hqcop, ← hprod]
    exact Finset.prod_congr rfl hqchar
  have : Fact q.Prime := ⟨hq⟩
  rw [kronZ_odd_prime q hq2] at hkron
  have hD0 : (D : ZMod q) ≠ 0 := fun h => hqndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd D q).mp h)
  obtain ⟨y, hy⟩ := (legendreSym.eq_one_iff q hD0).mp hkron
  set b₀ : ℤ := (y.val : ℤ)
  have hb₀ : (q : ℤ) ∣ b₀ ^ 2 - D := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [b₀, hy, sq]
  -- 5. adjust the parity of `b`
  obtain ⟨b, hbq, hb2⟩ : ∃ b : ℤ, (q : ℤ) ∣ b ^ 2 - D ∧ (2 : ℤ) ∣ b - D := by
    by_cases h : (2 : ℤ) ∣ b₀ - D
    · exact ⟨b₀, hb₀, h⟩
    · refine ⟨b₀ + q, ?_, ?_⟩
      · have e1 : (b₀ + q) ^ 2 - D = (b₀ ^ 2 - D) + q * (2 * b₀ + q) := by ring
        rw [e1]; exact dvd_add hb₀ (dvd_mul_right _ _)
      · obtain ⟨j, hj⟩ := hqodd
        have : (q : ℤ) = 2 * j + 1 := by exact_mod_cast hj
        omega
  have hb4 : (4 : ℤ) ∣ b ^ 2 - D := by
    obtain ⟨j, hj⟩ := hb2
    have hb : b = D + 2 * j := by omega
    rcases hD.le.lt_or_eq |>.elim (fun _ => (IsQuadDisc.fund (D := D)).1) (fun h => absurd h hD.ne)
      with h0 | h1
    · obtain ⟨i, hi⟩ : ∃ i, D = 4 * i := ⟨D / 4, by omega⟩
      exact ⟨4 * i ^ 2 + 4 * i * j + j ^ 2 - i, by rw [hb, hi]; ring⟩
    · obtain ⟨i, hi⟩ : ∃ i, D = 4 * i + 1 := ⟨D / 4, by omega⟩
      exact ⟨4 * i ^ 2 + i + 4 * i * j + j + j ^ 2, by rw [hb, hi]; ring⟩
  have h4q : IsCoprime (4 : ℤ) q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime 4 q := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hqodd)
    simpa [Int.gcd] using this
  obtain ⟨c, hc⟩ := h4q.mul_dvd hb4 hbq
  -- 6. the form `[q, b, c]`
  set f := BinQF.mk q b c
  have hfD : f.disc = D := by simp only [f, disc, a_mk, b_mk, c_mk]; linear_combination hc
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
  refine ⟨f, ?_, hfD, ⟨by simpa [f] using hq0, hfD ▸ hD⟩, fun p hp => ?_⟩
  · rw [primitive_iff]
    rintro r hr ⟨hra, hrb, -⟩
    simp only [f, a_mk, b_mk] at hra hrb
    have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp (Int.natCast_dvd_natCast.mp hra)
    subst hrq
    apply hqndvd
    have : D = b ^ 2 - 4 * r * c := by linear_combination -hc
    rw [this]
    exact dvd_sub (dvd_pow hrb two_ne_zero) (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hra _) _)
  · have hpp := Nat.prime_of_mem_primeFactors hp
    have hpD : (p : ℤ) ∣ D := Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)
    have hev : f.eval 1 0 = q := by simp [f, eval_eq]
    have hpq : ¬ (p : ℤ) ∣ f.eval 1 0 := by
      rw [hev]
      intro h
      have hpq := (Nat.prime_dvd_prime_iff_eq hpp hq).mp (Int.natCast_dvd_natCast.mp h)
      have := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
      omega
    rw [← genusChar_eval_eq_formChar (D := D) (by
      rw [primitive_iff]
      rintro r hr ⟨hra, hrb, -⟩
      simp only [f, a_mk, b_mk] at hra hrb
      have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp (Int.natCast_dvd_natCast.mp hra)
      subst hrq
      apply hqndvd
      have : D = b ^ 2 - 4 * r * c := by linear_combination -hc
      rw [this]
      exact dvd_sub (dvd_pow hrb two_ne_zero) (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hra _) _))
      hfD hpp hpD 1 0 hpq, hev]
    exact hqchar p hp

/-! ### The count -/

/-- **The genus vector of a genus**, with its product-one proof (well defined by `sameGenus_iff_genusVec_eq`). -/
noncomputable def generaVec [IsQuadDisc D] : Genera D → {e : D.natAbs.primeFactors → ℤˣ // ∏ p, e p = 1} :=
  Quotient.lift (s := genusSetoid D) (fun f => ⟨genusVec D f.1, prod_genusVec f.2.1 f.2.2.1 f.2.2.2⟩)
    (fun f g h => Subtype.ext ((sameGenus_iff_genusVec_eq f.2.1 g.2.1 f.2.2.1 g.2.2.1 f.2.2.2 g.2.2.2).mp h))

/-- **Genera ↔ product-one sign vectors** (Gauss §§261, 287; Cox, Theorem 6.1): the genus vector is a bijection from
the genera of primitive positive definite forms of fundamental discriminant $D < 0$ onto
$\{(e_p)_{p \mid D} \in \{\pm 1\}^t : \prod_p e_p = 1\}$. Injective by genus = local equivalence, onto by
`exists_form_of_signs` (Dirichlet). -/
@[kb "gauss1801" "§287 [unverified]; cassels1978 Ch. 14, Thm. 5.1, p. 343"]
theorem generaVec_bijective [IsQuadDisc D] (hD : D < 0) : Function.Bijective (generaVec (D := D)) := by
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with | h f => ?_
    induction y using Quotient.inductionOn with | h g => ?_
    apply Quotient.sound
    exact (sameGenus_iff_genusVec_eq f.2.1 g.2.1 f.2.2.1 g.2.2.1 f.2.2.2 g.2.2.2).mpr
      (congrArg Subtype.val hxy)
  · rintro ⟨e, he⟩
    let e' : ℕ → ℤ := fun p => if h : p ∈ D.natAbs.primeFactors then ((e ⟨p, h⟩ : ℤˣ) : ℤ) else 1
    have he' : ∀ p : D.natAbs.primeFactors, e' p = ((e p : ℤˣ) : ℤ) := fun p => by
      simp only [e']; rw [dite_eq_left p.2]
    have he1 : ∀ p ∈ D.natAbs.primeFactors, e' p = 1 ∨ e' p = -1 := fun p hp => by
      rw [he' ⟨p, hp⟩]
      rcases Int.units_eq_one_or (e ⟨p, hp⟩) with h | h <;> simp [h]
    have hprod : ∏ p ∈ D.natAbs.primeFactors, e' p = 1 := by
      rw [← Finset.prod_coe_sort D.natAbs.primeFactors e']
      simp_rw [he']
      rw [← Units.coe_prod, he, Units.val_one]
    obtain ⟨f, hf, hfD, hfpos, hchar⟩ := exists_form_of_signs hD e' he1 hprod
    refine ⟨Quotient.mk (genusSetoid D) ⟨f, hf, hfD, hfpos⟩, Subtype.ext (funext fun p => Units.ext ?_)⟩
    show ((genusVec D f p : ℤˣ) : ℤ) = _
    rw [coe_genusVec hf hfD, hchar p p.2, he']

/-- **The number of genera is $2^{t-1}$** (Gauss, *Disq. Arith.* §§261, 287; Cox, Theorem 6.1; Buell, Theorem 4.1):
for a fundamental discriminant $D < 0$ with $t$ distinct prime factors, the primitive positive definite forms of
discriminant $D$ fall into exactly $2^{t-1}$ genera, where a genus is a class of `Siegel.SameGenus` (equivalence
over every $\mathbb{Z}_p$ and over $\mathbb{R}$). Unconditional; the only global input is Dirichlet's theorem
(proved in Mathlib). -/
@[kb "gauss1801" "§287 [unverified]"]
theorem card_genera [IsQuadDisc D] (hD : D < 0) :
    Nat.card (Genera D) = 2 ^ (D.natAbs.primeFactors.card - 1) := by
  have hne : (D.natAbs.primeFactors).Nonempty :=
    Nat.nonempty_primeFactors.mpr (by have := three_le_natAbs (D := D); omega)
  have : Nonempty D.natAbs.primeFactors := hne.coe_sort
  rw [Nat.card_congr (Equiv.ofBijective _ (generaVec_bijective hD)), card_signVec_prod_one,
    Fintype.card_coe]

end QuadFormsKB.Binary
