/-
# Conway–Sloane, Ch. 15, §9.3: Theorem 16 as printed is false

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.3, p. 390
(`conwaysloane1999`).

**The printed statement.** "We call $r \in \mathbb Q$ *automorphous* if it is the spinor norm of a proper integral
automorphism of $f$." **Theorem 16.** "The spinor kernel consists of the spinor operators $\Delta(r)$ for which the
positive integer $r$ is an automorphous number not divisible by any prime divisor of $2d$." Here a spinor operator is
named by a family of unit square classes indexed by the primes of $\Pi$, $\Delta(r) = (r, r, \dots)$ (37), and the
spinor kernel is the set of operators acting trivially on spinor genera.

**Formal reading** (`Theorem16Printed`). For a symmetric nonsingular Gram matrix $A$ of dimension $n \ge 3$, $P$ = the
primes dividing $2\det H = 2^{n+1}\det A$ (`primeSet`; Conway–Sloane's $\Pi$ without $-1$), and a family $x$ of
$p$-adic units ($p \in P$): $x$ is in the spinor kernel (Cassels' $ST$, `casselsST`) if and only if there is a
positive integer $r$ coprime to $2\det A$ which is automorphous (`Lattices.latSpinorNormGroup`, Cassels (1.20): $r$ is
the spinor norm of a proper automorphism of the lattice $\mathbb Z^n$) such that $x$ and $\Delta(r)$ are the same
operator, i.e. have the same square class at every $p \in P$.

**Erratum** (`not_theorem16Printed`). The "only if" direction fails for $f = x^2 + y^2 + z^2$ ($A = I_3$, $d = 1$,
$\Pi = \{-1, 2\}$). Every $2$-adic unit is $2$-adically automorphous (Cassels, Lemma 3.8 (ii)), so every operator
$\Delta(3)$, in particular, lies in the kernel. But an odd positive automorphous $r$ has even order at every odd prime
(the spinor norm of a proper automorphism of $\mathbb Z^3$ is a unit class at every odd prime, Cassels, Lemma 3.3 /
O'Meara 92:5), hence is a perfect square, hence $\Delta(r)$ is trivial at $2$, whereas $3$ is not a square in
$\mathbb Q_2$.

**Proves**
* `not_theorem16Printed`: the printed Theorem 16, read as above, is false.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorems
import QuadFormsKB.Literature.Cassels.Ch11Sec3Dyadic
import QuadFormsKB.Literature.Cassels.Ch11Thm13Int
import QuadFormsKB.Literature.Cassels.Ch11Sec1

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

open scoped Classical

/-! ### The printed statement -/

/-- **Conway–Sloane, Theorem 16, as printed** (§9.3, p. 390): *the spinor kernel consists of the spinor operators
$\Delta(r)$ for which the positive integer $r$ is an automorphous number not divisible by any prime divisor of $2d$.*

Formal reading. For every symmetric nonsingular integer Gram matrix $A$ ($A^{\mathsf T} = A$, $\det A \ne 0$, so
$d = \det A$) of dimension $n \ge 3$, with $P$ = `primeSet (2 * det H)` the finite set of primes dividing $2\det H =
2^{n+1}\det A$ (Conway–Sloane's $\Pi$ without $-1$), and for every family $x \in X = \prod_{p \in P} U_p$ of
$p$-adic units (`casselsX`; operators are named by families of unit square classes): $x$ lies in the spinor kernel
(Cassels' $ST$, `casselsST (csQ A) _ stdLat P`) if and only if there is a positive integer $r$ (a natural number
$r \ne 0$) with
* $\gcd(r, 2d) = 1$ (`IsCoprime`): $r$ is not divisible by any prime divisor of $2d$;
* $r$ automorphous: $r \in \theta(\Lambda)$, `latSpinorNormGroup (csQ A) _ stdLat` (Cassels (1.20)): the square class
  of $r$ is the spinor norm of a proper automorphism $\sigma \in O^+(\mathbb Z^n)$ of $f$;
* $x = \Delta(r)$ as operators: `SqClass.mk (x p) = SqClass.mk (deltaR P r p)` for every $p \in P$
  (`deltaR`, (37)).

*Erratum:* this is false, see `not_theorem16Printed`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.3, Thm. 16, p. 390 (as printed; refuted, see not_theorem16Printed)"]
def Theorem16Printed : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hA : Aᵀ = A) (hd : A.det ≠ 0), 3 ≤ n →
    ∀ P : Finset (HeightOneSpectrum (𝓞 ℚ)), P = primeSet (2 * (Cassels.Ch8Ex2.gramForm A).hessian.det) →
      ∀ x ∈ casselsX P,
        (x ∈ casselsST (csQ A) (csQ_nondegenerate hA hd) stdLat P ↔
          ∃ (r : ℕ) (hr : (r : ℚ) ≠ 0), IsCoprime (r : ℤ) (2 * A.det) ∧
            Units.mk0 (r : ℚ) hr ∈ latSpinorNormGroup (csQ A) (csQ_nondegenerate hA hd) stdLat ∧
            ∀ p : P, SqClass.mk (x p) = SqClass.mk (deltaR P (Units.mk0 (r : ℚ) hr) p))

/-! ### The identity form -/

/-- The Gram matrix of $f = x^2 + y^2 + z^2$. -/
abbrev I3 : Matrix (Fin 3) (Fin 3) ℤ := 1

theorem I3_det : I3.det = 1 := Matrix.det_one

theorem I3_hessian_det : (Cassels.Ch8Ex2.gramForm I3).hessian.det = 8 := by
  rw [hessian_det_csForm (Matrix.transpose_one), I3_det]; norm_num

theorem I3_nondeg : (csQ I3).Nondegenerate :=
  csQ_nondegenerate (Matrix.transpose_one) (by rw [I3_det]; exact one_ne_zero)

theorem I3_hessian_apply (k l : Fin 3) :
    (Cassels.Ch8Ex2.gramForm I3).hessian k l = if k = l then 2 else 0 := by
  rw [hessian_csForm (Matrix.transpose_one)]
  by_cases h : k = l <;> simp [h]

theorem prime_dvd_sixteen {p : ℕ} (hp : p.Prime) (h : p ∣ 16) : p = 2 :=
  (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow (n := 4) (by norm_num; exact h))

/-- The primes of $P$ = `primeSet (2 * det H)` for $f = x^2+y^2+z^2$ are the place of $2$ only. -/
theorem primeOf_eq_two_of_mem {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : v ∈ primeSet (2 * (Cassels.Ch8Ex2.gramForm I3).hessian.det)) : primeOf v = 2 := by
  rw [primeSet, Finset.mem_preimage, Nat.mem_primeFactors, I3_hessian_det] at hv
  exact prime_dvd_sixteen hv.1 (by simpa using hv.2.1)

/-- The place of $\mathbb Q$ above the prime $2$. -/
def v2 : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨2, Nat.prime_two⟩

theorem primeOf_v2 : primeOf v2 = 2 :=
  congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨2, Nat.prime_two⟩)

theorem v2_mem : v2 ∈ primeSet (2 * (Cassels.Ch8Ex2.gramForm I3).hessian.det) := by
  rw [primeSet, Finset.mem_preimage, Nat.mem_primeFactors, I3_hessian_det]
  exact ⟨by rw [show Rat.HeightOneSpectrum.natGenerator v2 = 2 from primeOf_v2]; exact Nat.prime_two,
    by rw [show Rat.HeightOneSpectrum.natGenerator v2 = 2 from primeOf_v2]; norm_num, by norm_num⟩

/-! ### Global automorphous numbers are local ones -/

theorem latSpinorNormGroup_le_local {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n)
    (v : HeightOneSpectrum (𝓞 ℚ)) {a : ℚˣ} (ha : a ∈ latSpinorNormGroup Q hQ L) :
    Units.map (algebraMap ℚ (v.adicCompletion ℚ) : ℚ →* v.adicCompletion ℚ) a ∈
      localSpinorNormGroup Q hQ v L := by
  obtain ⟨σ, hσ, hθ⟩ := (mem_latSpinorNormGroup Q hQ L).mp ha
  have ha' : spinorNorm Q ℚ σ = sqClassOf (a : ℚ) := by
    rw [hθ, sqClassOf_of_ne_zero a.ne_zero]; exact congrArg SqClass.mk (Units.ext rfl)
  rw [Subgroup.mem_inf] at hσ
  refine (mem_localSpinorNormGroup Q hQ v L).mpr ⟨orthMap Q _ σ, ⟨?_, orthMap_mem_soSub Q _ hσ.2⟩, ?_⟩
  · change locAct v (GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) (σ : GL (Fin n) ℚ))
      (loc v L.1) = loc v L.1
    have h1 := loc_glImage v (σ : GL (Fin n) ℚ) L.1
    rw [(mem_autLat Q).mp hσ.1] at h1
    exact h1.symm
  · rw [spinorNorm_orthMap_of hQ v σ a.ne_zero ha', sqClassOf_of_ne_zero ((map_ne_zero _).mpr a.ne_zero)]
    exact congrArg SqClass.mk (Units.ext rfl)

/-- For $f = x^2+y^2+z^2$, an automorphous rational has even order at every odd prime (O'Meara 92:5 / Cassels,
Lemma 3.3: $\theta(\mathbb Z_p^3)$ consists of the unit classes). -/
theorem even_val_of_mem_latSpinorNormGroup_I3 {r : ℚˣ} (hr : r ∈ latSpinorNormGroup (csQ I3) I3_nondeg stdLat)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : primeOf v ≠ 2) :
    ∃ m : ℤ, Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (r : ℚ)) = exp (2 * m) := by
  have hloc := latSpinorNormGroup_le_local (csQ I3) I3_nondeg stdLat v hr
  have hnd : ¬ ((primeOf v : ℕ) : ℤ) ∣ 2 * (Cassels.Ch8Ex2.gramForm I3).hessian.det := by
    rw [I3_hessian_det]
    intro h
    have h16 : primeOf v ∣ 16 := by exact_mod_cast (show ((primeOf v : ℕ) : ℤ) ∣ 16 by simpa using h)
    exact hv (prime_dvd_sixteen (Rat.HeightOneSpectrum.prime_natGenerator v) h16)
  have h := (mem_localSpinorNormGroup_std_iff_of_not_dvd (by norm_num) (Cassels.Ch8Ex2.gramForm I3) I3_nondeg v
    hnd _).mp hloc
  refine exists_valued_eq_exp_two_mul v ((map_ne_zero _).mpr r.ne_zero) ?_
  rw [sqClassOf_of_ne_zero ((map_ne_zero _).mpr r.ne_zero)]
  have e : Units.mk0 (algebraMap ℚ (v.adicCompletion ℚ) (r : ℚ)) ((map_ne_zero _).mpr r.ne_zero) =
      Units.map (algebraMap ℚ (v.adicCompletion ℚ) : ℚ →* v.adicCompletion ℚ) r := Units.ext rfl
  rw [e]
  exact h

/-! ### Elementary number theory -/

/-- An odd natural number of even order at every odd prime is a perfect square. -/
theorem isSquare_of_even_val {r : ℕ} (hr0 : r ≠ 0) (hodd : ¬ 2 ∣ r)
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), primeOf v ≠ 2 →
      ∃ m : ℤ, Valued.v ((r : ℕ) : v.adicCompletion ℚ) = exp (2 * m)) : IsSquare r := by
  obtain ⟨b, a, hab, hsq⟩ := exists_sq_mul_squarefree r
  have ha1 : a = 1 := by
    by_contra ha1
    obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd ha1
    have ha0 : a ≠ 0 := fun h0 => hr0 (by rw [← hab, h0, mul_zero])
    have hb0 : b ≠ 0 := fun h0 => hr0 (by rw [← hab, h0]; simp)
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hodd (hpa.trans (Dvd.intro_left (b ^ 2) hab))
    set v := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩ with hv
    have hvp : primeOf v = p :=
      congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, hp⟩)
    obtain ⟨m, hm⟩ := h v (by rw [hvp]; exact hp2)
    have h1 : Valued.v ((a : ℕ) : v.adicCompletion ℚ) ≤ exp (-1) := by
      have := (valued_intCast_le_iff v a 1).2 (by
        rw [show Rat.HeightOneSpectrum.natGenerator v = p from hvp]; exact_mod_cast (by simpa using hpa))
      simpa using this
    have h2 : ¬ Valued.v ((a : ℕ) : v.adicCompletion ℚ) ≤ exp (-2) := by
      intro h'
      have := (valued_intCast_le_iff v a 2).1 (by simpa using h')
      rw [show Rat.HeightOneSpectrum.natGenerator v = p from hvp] at this
      have h3 : p * p ∣ a := by
        have : ((p * p : ℕ) : ℤ) ∣ (a : ℤ) := by simpa [sq] using this
        exact_mod_cast this
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq _ h3))
    have ha0' : Valued.v ((a : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact_mod_cast ha0
    have hb0' : Valued.v ((b : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact_mod_cast hb0
    obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v ((a : ℕ) : v.adicCompletion ℚ) = exp k := ⟨log _, (exp_log ha0').symm⟩
    obtain ⟨j, hj⟩ : ∃ j : ℤ, Valued.v ((b : ℕ) : v.adicCompletion ℚ) = exp j := ⟨log _, (exp_log hb0').symm⟩
    rw [hk, exp_le_exp] at h1
    rw [hk, exp_le_exp] at h2
    have hr : ((r : ℕ) : v.adicCompletion ℚ) = (b : v.adicCompletion ℚ) * b * a := by
      rw [← hab]; push_cast; ring
    rw [hr, map_mul, map_mul, hj, hk, ← exp_add, ← exp_add, exp_inj] at hm
    omega
  subst ha1
  exact ⟨b, by rw [← hab]; ring⟩

/-- $3$ is not a square in $\mathbb Q_2$ (the completion at a place with $p = 2$): $(z-1)(z+1) = 2$ with both
factors integral forces one of them to be a unit, but they differ by $2$. -/
theorem not_exists_sq_three {v : HeightOneSpectrum (𝓞 ℚ)} (hv : primeOf v = 2) (z : v.adicCompletion ℚ)
    (hz : z ^ 2 = 3) : False := by
  have h3 : Valued.v (3 : v.adicCompletion ℚ) = 1 := by
    have := valued_intCast_eq_one v 3 (by rw [show Rat.HeightOneSpectrum.natGenerator v = 2 from hv]; norm_num)
    simpa using this
  have h2le : Valued.v (2 : v.adicCompletion ℚ) ≤ exp (-1) := by
    have := (valued_intCast_le_iff v 2 1).2 (by rw [show Rat.HeightOneSpectrum.natGenerator v = 2 from hv]; norm_num)
    simpa using this
  have h2nle : ¬ Valued.v (2 : v.adicCompletion ℚ) ≤ exp (-2) := by
    intro h'
    have := (valued_intCast_le_iff v 2 2).1 (by simpa using h')
    rw [show Rat.HeightOneSpectrum.natGenerator v = 2 from hv] at this
    norm_num at this
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have hwz : Valued.v z = 1 := by
    have h' : Valued.v z ^ 2 = 1 := by rw [← map_pow, hz, h3]
    obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v z = exp k := ⟨log _, (exp_log (by simpa using hz0)).symm⟩
    rw [hk, ← WithZero.exp_nsmul,← exp_zero, exp_inj] at h'
    rw [hk, show k = 0 by simpa using h', exp_zero]
  have hm1 : z - 1 ≠ 0 := fun h0 => by
    have : z = 1 := by linear_combination h0
    rw [this] at hz; norm_num at hz
  have hp1 : z + 1 ≠ 0 := fun h0 => by
    have : z = -1 := by linear_combination h0
    rw [this] at hz; norm_num at hz
  have hprod : (z - 1) * (z + 1) = 2 := by linear_combination hz
  have ha : Valued.v (z - 1) ≤ 1 := Valuation.map_sub_le _ hwz.le (by simp)
  have hb : Valued.v (z + 1) ≤ 1 := Valuation.map_add_le _ hwz.le (by simp)
  obtain ⟨i, hi⟩ : ∃ i : ℤ, Valued.v (z - 1) = exp i := ⟨log _, (exp_log (by simpa using hm1)).symm⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, Valued.v (z + 1) = exp j := ⟨log _, (exp_log (by simpa using hp1)).symm⟩
  obtain ⟨t, ht⟩ : ∃ t : ℤ, Valued.v (2 : v.adicCompletion ℚ) = exp t :=
    ⟨log _, (exp_log (by simp)).symm⟩
  have hij : i + j = t := by
    have : Valued.v ((z - 1) * (z + 1)) = Valued.v (2 : v.adicCompletion ℚ) := by rw [hprod]
    rw [map_mul, hi, hj, ht, ← exp_add, exp_inj] at this
    exact this
  rw [ht, exp_le_exp] at h2le h2nle
  rw [hi, ← exp_zero, exp_le_exp] at ha
  rw [hj, ← exp_zero, exp_le_exp] at hb
  have h2lt : Valued.v (2 : v.adicCompletion ℚ) < 1 := by
    rw [ht, ← exp_zero, exp_lt_exp]; omega
  by_cases hi0 : i = 0
  · have : Valued.v (z + 1) = 1 := by
      have e : z + 1 = (z - 1) + 2 := by ring
      rw [e, Valuation.map_add_eq_of_lt_left _ (by rw [hi, hi0, exp_zero]; exact h2lt), hi, hi0, exp_zero]
    rw [hj, ← exp_zero, exp_inj] at this
    omega
  · by_cases hj0 : j = 0
    · have : Valued.v (z - 1) = 1 := by
        have e : z - 1 = (z + 1) - 2 := by ring
        rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [hj, hj0, exp_zero]; exact h2lt), hj, hj0, exp_zero]
      rw [hi, ← exp_zero, exp_inj] at this
      omega
    · omega

/-! ### The refutation -/

/-- $3$ as a rational unit. -/
def three : ℚˣ := Units.mk0 3 (by norm_num)

/-- **Erratum to Conway–Sloane, Theorem 16** (§9.3, p. 390): the theorem as printed (`Theorem16Printed`) is false.
Counterexample $f = x^2 + y^2 + z^2$ ($A = I_3$, $d = 1$, $P = \{2\}$, i.e. $\Pi = \{-1, 2\}$) and $x = \Delta(3)$. Every
$2$-adic unit is $2$-adically automorphous (Cassels, Lemma 3.8 (ii)), so $\Delta(3)$ is in the spinor kernel
(indeed the kernel is all of $X$). But if $r > 0$ is odd and automorphous, then at every odd prime the spinor norm of
a proper automorphism of $\mathbb Z_p^3$ is a unit class (Cassels, Lemma 3.3), so $r$ has even order at every odd
prime and is a perfect square, hence $\Delta(r)$ is trivial at $2$, whereas $3$ is not a square in $\mathbb Q_2$.
The "if" direction of the printed theorem (automorphous $r$ prime to $2d$ gives an operator in the kernel) is not
affected; what fails is that the kernel is *only* such operators. -/
@[kb "conwaysloane1999" "Ch. 15, §9.3, Thm. 16, p. 390 (erratum: false for x²+y²+z²)"]
theorem not_theorem16Printed : ¬ Theorem16Printed := by
  intro h
  set P := primeSet (2 * (Cassels.Ch8Ex2.gramForm I3).hessian.det) with hP
  have hprime : ∀ p : P, primeOf p.1 = 2 := fun p => primeOf_eq_two_of_mem p.2
  -- Δ(3) is a family of units
  have hX : deltaR P three ∈ casselsX P := by
    refine casselsDiag_mem_casselsX fun p => ?_
    have := valued_intCast_eq_one p.1 3 (by rw [show Rat.HeightOneSpectrum.natGenerator p.1 = 2 from hprime p]; norm_num)
    simpa [three] using this
  -- Δ(3) is in the spinor kernel: every unit is 2-adically automorphous
  have hker : deltaR P three ∈ casselsST (csQ I3) I3_nondeg stdLat P := by
    refine casselsX_le_of_isTractable (csQ I3) I3_nondeg stdLat P (fun p => ?_) hX
    have h2 : (2 : 𝓞 ℚ) ∈ p.1.asIdeal := (two_mem_iff_natGenerator p.1).mpr (hprime p)
    refine isTractable_of_units_mem (csQ I3) I3_nondeg stdLat P p fun u hu => ?_
    have hGv : ∀ k l, locGram (csQ I3) p.1 1 k l = (((if k = l then 2 else 0 : ℤ)) : p.1.adicCompletion ℚ) := by
      intro k l
      rw [show csQ I3 = (Cassels.Ch8Ex2.gramForm I3).map (Int.castRingHom ℚ) from rfl, locGram_one_int,
        I3_hessian_apply]
    refine units_mem_localSpinorNormGroup_two_ternary (csQ I3) I3_nondeg h2 stdLat 1
      (loc_std_eq_locAct_one p.1) (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)
      (fun l m hlm _ => by rw [hGv]; simp [hlm]) ?_ (Or.inl ?_) u hu
    · rw [hGv, hGv]; simp
    · rw [hGv, hGv]; simp
  obtain ⟨r, hr, hcop, haut, hcls⟩ :=
    (h 3 I3 Matrix.transpose_one (by rw [I3_det]; exact one_ne_zero) le_rfl P hP _ hX).mp hker
  -- r is odd
  have hodd : ¬ 2 ∣ r := by
    intro h2
    rw [I3_det, mul_one] at hcop
    have h2' : (2 : ℤ) ∣ (r : ℤ) := by exact_mod_cast h2
    have := hcop.isUnit_of_dvd' h2' (dvd_refl 2)
    rcases Int.isUnit_iff.mp this with h | h <;> omega
  -- r is a perfect square
  have hsq : IsSquare r := by
    refine isSquare_of_even_val (fun h0 => hr (by simp [h0])) hodd fun v hv => ?_
    obtain ⟨m, hm⟩ := even_val_of_mem_latSpinorNormGroup_I3 haut v hv
    exact ⟨m, by simpa using hm⟩
  obtain ⟨b, hb⟩ := hsq
  have hb0 : (b : v2.adicCompletion ℚ) ≠ 0 := by
    have : b ≠ 0 := fun h0 => hr (by rw [hb, h0]; simp)
    exact_mod_cast this
  -- the classes at the place of 2 agree, so 3 is a square in Q_2
  have hc := hcls ⟨v2, v2_mem⟩
  have hone : SqClass.mk (deltaR P three ⟨v2, v2_mem⟩ * deltaR P (Units.mk0 (r : ℚ) hr) ⟨v2, v2_mem⟩) = 1 := by
    rw [SqClass.mk_mul, hc, SqClass.mul_self]
  obtain ⟨y, hy⟩ := (SqClass.mk_eq_one_iff _).mp hone
  have hy' : ((y : v2.adicCompletion ℚ)) ^ 2 = 3 * ((b : v2.adicCompletion ℚ) * b) := by
    have := congrArg (fun u : (v2.adicCompletion ℚ)ˣ => (u : v2.adicCompletion ℚ)) hy
    simp only [Units.val_pow_eq_pow_val, Units.val_mul] at this
    rw [this]
    show algebraMap ℚ _ ((three : ℚˣ) : ℚ) * algebraMap ℚ _ ((Units.mk0 (r : ℚ) hr : ℚˣ) : ℚ) = _
    simp only [three, Units.val_mk0, hb]
    push_cast
    simp
  exact not_exists_sq_three primeOf_v2 ((y : v2.adicCompletion ℚ) / b) (by
    rw [div_pow, hy']; field_simp)

end QuadFormsKB.ConwaySloane
