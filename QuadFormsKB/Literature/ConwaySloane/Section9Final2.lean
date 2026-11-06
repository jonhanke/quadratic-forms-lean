/-
# Conway–Sloane, Ch. 15, §9.7: Theorems 19, 20 (d) and 21

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.7, pp. 393–395
(`conwaysloane1999`).

**Layer.** As in `Section9Final.lean`.

**Proves** (all unconditional; axioms: `propext`, `Classical.choice`, `Quot.sound`)
* `five_not_mem_of_not_isTractable`: if every odd prime of $P$ is tractable but $2$ is not, then $5$ is not
  $2$-adically automorphous (with $-1$, $5$ would give every unit class).
* **Theorem 20 (d)** (`theorem20d`, (42)): if $2$ is the only intractable prime, $8^{\binom n2} \mid 4^{[n/2]}d$.
* **Theorem 19** (`theorem19`): an indefinite form of dimension $n \ge 3$ with more than one class in its genus can be
  $p$-adically diagonalized, for some prime $p$, with diagonal entries involving distinct powers of $p$ (for $n \le 2$
  the book's $p = -1$ case).
* **Theorem 21** (`theorem21 : Theorem21Statement`), for every $n$.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Final
import QuadFormsKB.Literature.ConwaySloane.Section9DyadicOdd

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

open scoped Classical

variable {n : ℕ}

/-- If every prime of $P$ other than the place $p$ of $2$ is tractable, and $5$ is $2$-adically automorphous, then $2$
is tractable (Conway–Sloane, proof of Thm. 20 (d), p. 394: $(u_7)_2$ is in the kernel since $-1$ is
$(-1)$-adically automorphous, and $(u_5)_2$; "these generate all the possibilities"). -/
theorem isTractable_two_of_five_mem (hn : 3 ≤ n) {Q : QuadForm ℚ n} (hQ : Q.Nondegenerate) (hind : IsIndefinite Q)
    (L : Lat ℚ n) (P : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : P) (hp2 : primeOf p.1 = 2)
    (hoth : ∀ q : P, q ≠ p → IsTractable Q hQ L P q)
    (h5 : Units.mk0 (5 : p.1.adicCompletion ℚ) (by norm_num) ∈ localSpinorNormGroup Q hQ p.1 L) :
    IsTractable Q hQ L P p := by
  have h2 : (2 : 𝓞 ℚ) ∈ p.1.asIdeal := (two_mem_iff_natGenerator p.1).mpr hp2
  intro u hu
  rcases units_mem_or_neg_of_five_mem hQ L h2 h5 u hu with h | h
  · exact Subgroup.mem_sup_left (mulSingle_mem_casselsS p h)
  · have e : u = -1 * (-u) := by simp
    rw [e, Pi.mulSingle_mul]
    exact (casselsST Q hQ L P).mul_mem (mulSingle_neg_one_mem_of_isTractable Q hQ L P hn hind p hoth)
      (Subgroup.mem_sup_left (mulSingle_mem_casselsS p h))

theorem hint_std' (A : Matrix (Fin n) (Fin n) ℤ) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), ∀ x ∈ loc v (stdLat : Lat ℚ n).1,
      Valued.v ((csQ A).evalIn (v.adicCompletion ℚ) x) ≤ 1 := fun v =>
  hint_std (Cassels.Ch8Ex2.gramForm A) v

/-- **Conway–Sloane, Theorem 20 (d)** (§9.7, p. 394, (42)): *if $2$ is the only intractable prime then $4^{[n/2]}d$ is
divisible by $8^{\binom n2}$* (for an indefinite form of dimension $n \ge 3$). *Proof* (the book's): $5$ is not
$2$-adically automorphous (else $2$ would be tractable), so by rule (ii) of the algorithm no two powers of $2$ in the
diagonal have ratio $1$, $4$ or $16$ (`valued_det_le_of_five_not_mem_two`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, Thm. 20 (d), (42), p. 394"]
theorem theorem20d (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hd : A.det ≠ 0)
    (hind : IsIndefinite (csQ A)) (P : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : P) (hp2 : primeOf p.1 = 2)
    (hoth : ∀ q : P, q ≠ p → IsTractable (csQ A) (csQ_nondegenerate hA hd) stdLat P q)
    (hnt : ¬ IsTractable (csQ A) (csQ_nondegenerate hA hd) stdLat P p) :
    (8 : ℤ) ^ n.choose 2 ∣ 4 ^ (n / 2) * A.det := by
  have h2 : (2 : 𝓞 ℚ) ∈ p.1.asIdeal := (two_mem_iff_natGenerator p.1).mpr hp2
  have h5 : Units.mk0 (5 : p.1.adicCompletion ℚ) (by norm_num) ∉
      localSpinorNormGroup (csQ A) (csQ_nondegenerate hA hd) p.1 stdLat := fun h5 =>
    hnt (isTractable_two_of_five_mem hn _ hind stdLat P p hp2 hoth h5)
  have hdet := valued_det_le_of_five_not_mem_two (csQ_nondegenerate hA hd) h2 stdLat (hint_std' A p.1) h5 1
    (loc_std_eq_locAct_one p.1)
  have := two_pow_dvd_det_of_valued hA hp2 _ hdet
  rw [eight_pow_choose_eq]
  exact mul_dvd_mul_left _ this

/-- **Conway–Sloane, Theorem 19** (§9.7, p. 393): *if $f$ is indefinite and the genus of $f$ contains more than one
class, then for some $p$ (possibly $-1$), $f$ can be $p$-adically diagonalized and the diagonal entries all involve
distinct powers of $p$.* For dimension $n \ge 3$ (the book's proof: otherwise $p = -1$ and $n \le 2$): some finite
prime $p$ and a basis $\gamma$ of $\mathbb Z_p^n$ in which the Gram matrix is diagonal with diagonal entries of pairwise
different absolute values. -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, Thm. 19, p. 393"]
theorem theorem19 (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hd : A.det ≠ 0)
    (hind : IsIndefinite (csQ A)) (h : MoreThanOneClass A) :
    ∃ (v : HeightOneSpectrum (𝓞 ℚ)) (γ : GL (Fin n) (v.adicCompletion ℚ)),
      loc v (stdLat : Lat ℚ n).1 = locAct v γ (std v) ∧
      (∀ k l, k ≠ l → locGram (csQ A) v γ k l = 0) ∧
      Function.Injective (fun k => Valued.v (locGram (csQ A) v γ k k)) := by
  set P := primeSet (2 * (Cassels.Ch8Ex2.gramForm A).hessian.det)
  have hQ := csQ_nondegenerate hA hd
  by_cases hodd : ∃ q : P, primeOf q.1 ≠ 2 ∧ ¬ IsTractable (csQ A) hQ stdLat P q
  · obtain ⟨q, hq2, hq⟩ := hodd
    have h2q : (2 : 𝓞 ℚ) ∉ q.1.asIdeal := by rw [two_mem_iff_natGenerator]; exact hq2
    have hnot := not_units_mem_of_not_isTractable hq
    obtain ⟨γ', ν, hγ', horth, hval, -⟩ := exists_diag_basis hQ h2q stdLat 1
      (loc_std_eq_locAct_one q.1) (by convert hint_std' A q.1; exact Subsingleton.elim _ _)
    refine ⟨q.1, γ', hγ', horth, fun i j hij => ?_⟩
    by_contra hne
    exact hnot fun u hu =>
      units_mem_localSpinorNormGroup_of_orthogonal (csQ A) q.1 hQ h2q stdLat γ' hγ' horth hne hij u hu
  · push Not at hodd
    obtain ⟨p, hp⟩ := exists_not_isTractable hn hA hd hind P (primeSet_spec hA hd) h
    have hp2 : primeOf p.1 = 2 := by
      by_contra h2; exact hp (hodd p h2)
    have hoth : ∀ q : P, q ≠ p → IsTractable (csQ A) hQ stdLat P q := fun q hqp =>
      hodd q fun e => hqp (Subtype.ext (primeOf_injective (e.trans hp2.symm)))
    have h2 : (2 : 𝓞 ℚ) ∈ p.1.asIdeal := (two_mem_iff_natGenerator p.1).mpr hp2
    have h5 : Units.mk0 (5 : p.1.adicCompletion ℚ) (by norm_num) ∉ localSpinorNormGroup (csQ A) hQ p.1 stdLat :=
      fun h5 => hp (isTractable_two_of_five_mem hn hQ hind stdLat P p hp2 hoth h5)
    obtain ⟨γ', ν, hγ', -, horth, hval, hinj, -⟩ :=
      exists_diag_basis_two_of_five_not_mem hQ h2 stdLat (hint_std' A p.1) h5 1 (loc_std_eq_locAct_one p.1)
    refine ⟨p.1, γ', hγ', horth, fun i j hij => hinj ?_⟩
    have := hij
    simp only [hval, exp_inj] at this
    omega

/-- **Conway–Sloane, Theorem 21** (§9.7, p. 395, (43)): *if $f$ is an indefinite form of dimension $n$ and determinant
$d$, with more than one class in its genus, then $4^{[n/2]}d$ is divisible by $k^{\binom n2}$ for some nonsquare natural
number $k \equiv 0$ or $1 \pmod 4$.* Proved for every $n$: $n \le 2$ by `theorem21_small`, $n \ge 3$ by the book's case
analysis (`theorem21_core`) from Thm. 20 (a)–(d). -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, Thm. 21, (43), p. 395"]
theorem theorem21 : Theorem21Statement := by
  intro n A hA hd hind h
  rcases le_or_gt n 2 with hn | hn
  · exact theorem21_small hn hA hd hind h
  · exact theorem21_core (by omega) hA hd hind _ (primeSet_spec hA hd)
      (fun p hp2 hnt => theorem20c hA hd _ p hp2 hnt)
      (fun p hp2 hoth hnt => theorem20d (by omega) hA hd hind _ p hp2 hoth hnt) h

end QuadFormsKB.ConwaySloane
