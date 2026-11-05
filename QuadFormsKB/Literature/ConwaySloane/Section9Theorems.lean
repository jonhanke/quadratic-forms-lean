/-
# Conway–Sloane, Ch. 15, §9.7: when is there only one class in the genus?

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.7, pp. 393–396
(`conwaysloane1999`).

**Layer.** A form is its symmetric integer Gram matrix $A$ (classically integral, $f(x) = xAx^{\mathsf T}$, as in the
book), with the library form `Cassels.Ch8Ex2.gramForm A` (Hessian $2A$, so $\det H = 2^n\det A$), the rational form
`csQ A`, the lattice $\Lambda = \mathbb Z^n$ (`stdLat`), and a finite set $P$ of primes containing every prime
dividing $2\det A$ (`hPd`; Conway–Sloane's $\Pi$ without $-1$). Spinor operators, the spinor kernel and tractable
primes are as in `Section9Kernel.lean` (Cassels' group $G = R/ST$).

**Proves**
* `exists_not_isTractable`: if an indefinite form of dimension $n \ge 3$ has more than one class in its genus, some
  prime of $P$ is intractable (Eichler's theorem, Thm. 14, and the one-spinor-genus criterion).
* **Theorem 20 (a)** (`theorem20a`, (40)): if an odd prime $p$ is intractable, then $p^{\binom n2} \mid d$.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Kernel

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

variable {n : ℕ}

/-! ### Gram matrices -/

/-- The rational quadratic form $f(x) = xAx^{\mathsf T}$ of a Gram matrix $A$. -/
abbrev csQ (A : Matrix (Fin n) (Fin n) ℤ) : QuadForm ℚ n :=
  (Cassels.Ch8Ex2.gramForm A).map (Int.castRingHom ℚ)

theorem hessian_csForm {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) :
    (Cassels.Ch8Ex2.gramForm A).hessian = (2 : ℤ) • A := by
  rw [Cassels.Ch8Ex2.hessian_gramForm, hA, two_smul]

theorem hessian_det_csForm {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) :
    (Cassels.Ch8Ex2.gramForm A).hessian.det = 2 ^ n * A.det := by
  rw [hessian_csForm hA, det_smul, Fintype.card_fin]

theorem hessian_det_csForm_ne_zero {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hd : A.det ≠ 0) :
    (Cassels.Ch8Ex2.gramForm A).hessian.det ≠ 0 := by
  rw [hessian_det_csForm hA]; exact mul_ne_zero (pow_ne_zero _ two_ne_zero) hd

theorem csQ_nondegenerate {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hd : A.det ≠ 0) :
    (csQ A).Nondegenerate :=
  nondegenerate_map_of_det_ne_zero _ (hessian_det_csForm_ne_zero hA hd)

/-! ### The set of primes dividing $2\det A$ -/

/-- The finite places of $\mathbb Q$ whose prime divides the nonzero integer $m$. -/
def primeSet (m : ℤ) : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  m.natAbs.primeFactors.preimage (fun v => Rat.HeightOneSpectrum.natGenerator v)
    (Set.injOn_of_injective fun _ _ h => natGen_injective' h)

theorem not_dvd_of_not_mem_primeSet {m : ℤ} (hm : m ≠ 0) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ primeSet m) :
    ¬ ((primeOf v : ℕ) : ℤ) ∣ m := by
  intro h
  apply hv
  rw [primeSet, Finset.mem_preimage, Nat.mem_primeFactors]
  exact ⟨Rat.HeightOneSpectrum.prime_natGenerator v, Int.natCast_dvd.mp h, Int.natAbs_ne_zero.mpr hm⟩

/-- Conway–Sloane's $\Pi$ (without $-1$) for the Gram matrix $A$: the primes dividing $2\det A$, i.e. those dividing
$2\det H = 2^{n+1}\det A$. -/
theorem primeSet_spec {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hd : A.det ≠ 0) :
    ∀ v, v ∉ primeSet (2 * (Cassels.Ch8Ex2.gramForm A).hessian.det) →
      ¬ ((primeOf v : ℕ) : ℤ) ∣ 2 * (Cassels.Ch8Ex2.gramForm A).hessian.det :=
  fun _ hv => not_dvd_of_not_mem_primeSet (mul_ne_zero two_ne_zero (hessian_det_csForm_ne_zero hA hd)) hv

/-! ### More than one class gives an intractable prime -/

/-- **An intractable prime exists** (Conway–Sloane, proof of Thm. 19, p. 393: "we now quote Eichler's theorem
(Theorem 14) to see that the class coincides with the spinor genus and there must therefore be an intractable prime
$p$"): if an indefinite form of dimension $n \ge 3$ has more than one class in its genus, then for every admissible
$P$ some $p \in P$ is intractable. -/
theorem exists_not_isTractable (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hd : A.det ≠ 0)
    (hind : IsIndefinite (csQ A)) (P : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hPd : ∀ v, v ∉ P → ¬ ((primeOf v : ℕ) : ℤ) ∣ 2 * (Cassels.Ch8Ex2.gramForm A).hessian.det)
    (h : MoreThanOneClass A) :
    ∃ p : P, ¬ IsTractable (csQ A) (csQ_nondegenerate hA hd) stdLat P p := by
  by_contra hall
  push Not at hall
  obtain ⟨B, -, hB, hne⟩ := h
  exact hne (intEquiv_of_sameGenus_of_casselsX_le hn _ (hessian_det_csForm_ne_zero hA hd) hind P hPd
    (casselsX_le_of_isTractable _ _ _ P hall) _ hB)

/-! ### Theorem 20 (a) -/

/-- At an odd prime: if $p$ is intractable, then not every $p$-adic unit is $p$-adically automorphous. -/
theorem not_units_mem_of_not_isTractable {Q : QuadForm ℚ n} {hQ : Q.Nondegenerate} {L : Lat ℚ n}
    {P : Finset (HeightOneSpectrum (𝓞 ℚ))} {p : P} (h : ¬ IsTractable Q hQ L P p) :
    ¬ ∀ u : (p.1.adicCompletion ℚ)ˣ, Valued.v (u : p.1.adicCompletion ℚ) = 1 →
      u ∈ localSpinorNormGroup Q hQ p.1 L :=
  fun hu => h (isTractable_of_units_mem Q hQ L P p hu)

/-- The values of an integer-valued form on $\mathbb Z_p^n$ are $p$-adic integers. -/
theorem hint_std (f : QuadForm ℤ n) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ x ∈ loc v (stdLat : Lat ℚ n).1,
      Valued.v ((f.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) x) ≤ 1 := by
  have hL : loc v (stdLat : Lat ℚ n).1 = std v := loc_intVec v
  intro x hx; rw [hL] at hx; exact valued_evalIn_le_one_int v f hx

theorem loc_std_eq_locAct_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    loc v (stdLat : Lat ℚ n).1 = locAct v (1 : GL (Fin n) (v.adicCompletion ℚ)) (std v) := by
  rw [locAct_one]; exact loc_intVec v

/-- **Conway–Sloane, Theorem 20 (a)** (§9.7, p. 393, (40)): *if $p \ge 3$ is an intractable prime, then $d$ is
divisible by $p^{\binom n2}$.* Here $d = \det A$ for the Gram matrix $A$, $p \in P$ odd, and "intractable" is
`IsTractable` (the spinor kernel does not contain every $\Delta_p(u)$). Conway–Sloane assume $f$ indefinite; the
divisibility holds for every form. *Proof* (as in the book, via part (i) of the algorithm, i.e. Cassels' Lemma 3.7 and
its Corollary): an intractable prime has a $p$-adic unit that is not automorphous, so the $p$-adic diagonal entries
involve distinct powers $p^0, p^1, p^2, \dots$ at least. -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, Thm. 20 (a), (40), p. 393"]
theorem theorem20a {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hd : A.det ≠ 0)
    (P : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : P) (hp2 : primeOf p.1 ≠ 2)
    (hnt : ¬ IsTractable (csQ A) (csQ_nondegenerate hA hd) stdLat P p) :
    ((primeOf p.1 : ℕ) : ℤ) ^ n.choose 2 ∣ A.det := by
  have h2 : (2 : 𝓞 ℚ) ∉ p.1.asIdeal := by rw [two_mem_iff_natGenerator]; exact hp2
  have hdet := valued_det_le_of_not_units_mem (csQ A) p.1 (csQ_nondegenerate hA hd) h2 stdLat
    (by convert hint_std (Cassels.Ch8Ex2.gramForm A) p.1; exact Subsingleton.elim _ _)
    (not_units_mem_of_not_isTractable hnt) 1 (loc_std_eq_locAct_one p.1)
  rw [locGram_one_int_det, valued_intCast_le_iff, hessian_det_csForm hA, ← Nat.choose_two_right] at hdet
  have hpr := Rat.HeightOneSpectrum.prime_natGenerator p.1
  have hcop : IsCoprime (((primeOf p.1 : ℕ) : ℤ) ^ n.choose 2) ((2 : ℤ) ^ n) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime (primeOf p.1) 2 := (Nat.coprime_primes hpr Nat.prime_two).mpr hp2
    exact_mod_cast this
  exact hcop.dvd_of_dvd_mul_left hdet

end QuadFormsKB.ConwaySloane
