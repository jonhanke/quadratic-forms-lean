import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Berkovich2012.Final
import QuadFormsKB.Binary.GenusComposition
import QuadFormsKB.Binary.FormsIdeals

/-!
# Berkovich–Hanke–Jagy, Lemma 3.3 (proved), and Theorem 6.1, Corollary 6.2 unconditionally

Source: A. Berkovich, J. Hanke and W. Jagy, *A proof of the S-genus identities for ternary quadratic
forms*, arXiv:1010.1926v2 (bib key `berkovich2012`), §3, Lemma 3.3, p. 3; §6, Theorem 6.1 and
Corollary 6.2, p. 7.

Let $S$ be odd and squarefree. Then $D = -8S$ is a fundamental discriminant (`isQuadDisc_neg_eight_mul`),
every integral binary form of discriminant $-8S$ is primitive (`primitive_of_disc`), and the prime factors of
$D$ are $2$ and the primes $p \mid S$ (`primeFactors_neg_eight_mul`).

* `epsP_sForm`: for $p \mid S$, $\varepsilon_p(B(x,y) + 2Sz^2) = \left(\frac{-1}{p}\right)\chi_p(B)$, where
  $\chi_p$ is the genus character of the binary form $B$ (`Binary.formChar`): the values of
  $B(x, y) + 2Sz^2$ prime to $p$ are $\equiv$ values of $B$ prime to $p$ modulo $p$, on which
  $\left(\frac{\cdot}{p}\right) = \chi_p(B)$ (Gauss, `genusChar_eval_eq_formChar`).
* `sameGenus_sForm`: if $B$, $B'$ are in one genus (as binary forms), so are $B + 2Sz^2$ and $B' + 2Sz^2$.
* `lemma_3_3` (**Lemma 3.3**): there are binary forms $B_\sigma$, one per sign vector, with
  `SGenusParam S B`. *Existence* of $B_\sigma$: the genus characters
  $\chi_p(B_\sigma) = \left(\frac{-1}{p}\right)\sigma_p$ ($p \mid S$), $\chi_2(B_\sigma) = \prod_{p \mid S} \chi_p$,
  have product one, so a form with these characters exists (`Binary.exists_form_of_signs`: Gauss's existence
  of genera, via Dirichlet's theorem, proved in Mathlib). *Covering*: a binary form $B'$ of discriminant $-8S$
  has the genus characters of $B_\sigma$ for $\sigma_p = \varepsilon_p(B' + 2Sz^2)$ (at $p = 2$ by the product
  formula), so $B' \sim B_\sigma$ in genus (`Binary.sameGenus_iff_genusVec_eq`) and hence
  $B' + 2Sz^2$ and $B_\sigma + 2Sz^2$ are in one genus.
* `theorem_6_1`, `corollary_6_2`: the S-genus identities, **unconditional**.

*Route.* The source proves Lemma 3.3 by citing the genus theory of binary forms (Gauss; Cassels, Ch. 14) for
the forms of discriminant $-8S$; the proof here is exactly that: the library's genus characters of binary forms
and Gauss's theorem that every product-one character vector occurs. The 2-adic place needs no separate
Hasse-invariant computation: the binary genus is determined by the characters at the odd $p \mid S$ alone.
-/

namespace QuadFormsKB.Berkovich2012

open QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.Binary Matrix

variable {S : ℕ}

/-! ### The discriminant $-8S$ -/

/-- For $S$ odd and squarefree, $-8S$ is a fundamental discriminant. -/
theorem isQuadDisc_neg_eight_mul (hSodd : Odd S) (hSsf : Squarefree S) : IsQuadDisc (-8 * (S : ℤ)) := by
  obtain ⟨k, hk⟩ := hSodd
  refine ⟨⟨by omega, fun x hx => by omega, fun p hp hpo hdvd => ?_⟩, by omega⟩
  have h1 : (p : ℤ) ^ 2 ∣ 8 * (S : ℤ) := by
    have := dvd_neg.mpr hdvd; rwa [show -(-8 * (S : ℤ)) = 8 * S by ring] at this
  have h2 : p ^ 2 ∣ 8 * S := by exact_mod_cast h1
  have hcop : Nat.Coprime (p ^ 2) 8 := by
    apply Nat.Coprime.pow_left
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    apply Nat.Coprime.pow_right
    exact (Nat.coprime_primes hp Nat.prime_two).mpr (by rintro rfl; exact (Nat.not_even_iff_odd.mpr hpo) even_two)
  have h3 : p * p ∣ S := by rw [← sq]; exact hcop.dvd_of_dvd_mul_left h2
  exact hp.not_isUnit (Nat.isUnit_iff.mpr (by have := hSsf p h3; simpa using this))

/-- For $S$ odd and squarefree, every binary form of discriminant $-8S$ is primitive. -/
theorem primitive_of_disc (hSodd : Odd S) (hSsf : Squarefree S) {B : BinQF} (hd : B.disc = -8 * S) :
    Primitive B :=
  haveI := isQuadDisc_neg_eight_mul hSodd hSsf
  (primitive_iff_isPrimitive B).2 (isPrimitive_of_fund IsQuadDisc.fund hd)

/-- The prime factors of $8S$ ($S \neq 0$) are $2$ and those of $S$. -/
theorem primeFactors_neg_eight_mul (hS : S ≠ 0) :
    (-8 * (S : ℤ)).natAbs.primeFactors = insert 2 S.primeFactors := by
  have e : (-8 * (S : ℤ)).natAbs = 2 ^ 3 * S := by
    rw [Int.natAbs_mul]; simp
  rw [e, Nat.primeFactors_mul (by norm_num) hS, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
  rfl

/-! ### $\varepsilon_p$ and the genus characters -/

/-- $B(x,y) + 2Sz^2$ in coordinates, over any commutative ring. -/
theorem eval_map_sForm {K : Type*} [CommRing K] (φ : ℤ →+* K) (B : BinQF) (v : Fin 3 → K) :
    ((sForm S B).map φ).eval v = (B.map φ).eval ![v 0, v 1] + φ (2 * S) * v 2 ^ 2 := by
  simp [sForm, QuadForm.map, QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_three,
    Fin.sum_univ_two, BinQF.a, BinQF.b, BinQF.c, B.upper (show (1 : Fin 2) > 0 by decide)]
  ring

/-- $B(x,y) + 2Sz^2$ in coordinates. -/
theorem eval_sForm (B : BinQF) (v : Fin 3 → ℤ) :
    (sForm S B).eval v = B.eval (v 0) (v 1) + 2 * S * v 2 ^ 2 := by
  rw [BinQF.eval_eq]
  simp [sForm, QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_three]
  ring

/-- **$\varepsilon_p$ from the genus character.** For $S$ odd squarefree, $p \mid S$ and $B$ of discriminant
$-8S$: $\varepsilon_p(B(x,y) + 2Sz^2) = \left(\frac{-1}{p}\right)\chi_p(B)$. -/
theorem epsP_sForm (hSodd : Odd S) (hSsf : Squarefree S) {B : BinQF} (hd : B.disc = -8 * S)
    {p : ℕ} [hp : Fact p.Prime] (hpS : p ∣ S) :
    epsP p (sForm S B) = legendreSym p (-1) * formChar B p := by
  classical
  haveI := isQuadDisc_neg_eight_mul hSodd hSsf
  have hprim := primitive_of_disc hSodd hSsf hd
  have hp2 : p ≠ 2 := by
    rintro rfl; exact absurd (hSodd.of_dvd_nat hpS) (by decide)
  have hpD : (p : ℤ) ∣ -8 * (S : ℤ) := Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hpS) _
  have hp2S : (p : ℤ) ∣ 2 * (S : ℤ) := Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hpS) _
  have hval : ∀ v : Fin 3 → ℤ, ¬ (p : ℤ) ∣ (sForm S B).eval v →
      legendreSym p (-(sForm S B).eval v) = legendreSym p (-1) * formChar B p := by
    intro v hv
    rw [eval_sForm] at hv ⊢
    have hm : ¬ (p : ℤ) ∣ B.eval (v 0) (v 1) := fun h =>
      hv (dvd_add h (Dvd.dvd.mul_right hp2S _))
    have e1 : legendreSym p (-(B.eval (v 0) (v 1) + 2 * S * v 2 ^ 2)) =
        legendreSym p (-1 * B.eval (v 0) (v 1)) := by
      unfold legendreSym
      congr 1
      have h0 : ((2 * (S : ℤ) : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hp2S
      push_cast at h0 ⊢
      rw [h0]; ring
    rw [e1, legendreSym.mul]
    congr 1
    have := genusChar_eval_eq_formChar hprim hd hp.out hpD (v 0) (v 1) hm
    rw [← this]
    unfold genusChar
    rw [if_neg hp2, jacobiSym.legendreSym.to_jacobiSym]
  have hex : ∃ v : Fin 3 → ℤ, ¬ (p : ℤ) ∣ (sForm S B).eval v := by
    have hr := not_dvd_charCoeff hprim hp.out (hd ▸ hpD)
    unfold charCoeff at hr
    split_ifs at hr
    · refine ⟨![0, 1, 0], ?_⟩
      rw [eval_sForm, BinQF.eval_eq]; simpa using hr
    · refine ⟨![1, 0, 0], ?_⟩
      rw [eval_sForm, BinQF.eval_eq]; simpa using hr
  unfold epsP
  split_ifs with h
  · obtain ⟨v, hv, h1⟩ := h
    rw [← hval v hv, h1]
  · obtain ⟨v, hv⟩ := hex
    rw [← hval v hv]
    have hne : ((-(sForm S B).eval v : ℤ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, dvd_neg]; exact hv
    rcases legendreSym.eq_one_or_neg_one p hne with h1 | h1
    · exact absurd ⟨v, hv, h1⟩ h
    · exact h1.symm

/-! ### Same binary genus gives the same ternary genus -/

/-- The $3 \times 3$ block matrix $\begin{pmatrix} g & 0 \\ 0 & 1\end{pmatrix}$. -/
def blockOne {K : Type*} [CommRing K] (g : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![g 0 0, g 0 1, 0; g 1 0, g 1 1, 0; 0, 0, 1]

theorem blockOne_mul {K : Type*} [CommRing K] (g h : Matrix (Fin 2) (Fin 2) K) :
    blockOne g * blockOne h = blockOne (g * h) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockOne, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem blockOne_one {K : Type*} [CommRing K] : blockOne (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockOne]

/-- **Adding $2Sz^2$ preserves isometry over any ring:** if $B \cong B'$ over $K$, then
$B + 2Sz^2 \cong B' + 2Sz^2$ over $K$. -/
theorem isometricGL_sForm {K : Type*} [CommRing K] (φ : ℤ →+* K) {B B' : BinQF}
    (h : IsometricGL (B.map φ) (B'.map φ)) :
    IsometricGL ((sForm S B).map φ) ((sForm S B').map φ) := by
  obtain ⟨g, hg⟩ := h
  let G : GL (Fin 3) K := ⟨blockOne g.val, blockOne (g⁻¹).val,
    by rw [blockOne_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, blockOne_one],
    by rw [blockOne_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, blockOne_one]⟩
  refine ⟨G, fun v => ?_⟩
  rw [eval_map_sForm, eval_map_sForm, ← hg]
  have e : ![(G.val *ᵥ v) 0, (G.val *ᵥ v) 1] = g.val *ᵥ ![v 0, v 1] := by
    ext i; fin_cases i <;>
      simp [G, blockOne, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]
  have e2 : (G.val *ᵥ v) 2 = v 2 := by
    simp [G, blockOne, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [e, e2]

/-- **Same binary genus gives the same ternary genus:** if $B$ and $B'$ are in one genus, so are
$B(x,y) + 2Sz^2$ and $B'(x,y) + 2Sz^2$. -/
theorem sameGenus_sForm {B B' : BinQF} (h : SameGenus B B') : SameGenus (sForm S B) (sForm S B') :=
  ⟨fun p _ => isometricGL_sForm _ (h.1 p), isometricGL_sForm _ h.2⟩

/-! ### Lemma 3.3 -/

/-- The prescribed genus character at an odd prime: $\left(\frac{-1}{p}\right)\sigma_p$ for $p \mid S$. -/
def tSign (σ : Signs S) (p : ℕ) : ℤ :=
  if h : p ∈ S.primeFactors then jacobiSym (-1) p * sgnB (σ ⟨p, h⟩) else 1

/-- The prescribed genus characters: $\chi_p = $ `tSign σ p` for $p \mid S$ and
$\chi_2 = \prod_{p \mid S} \chi_p$. -/
def eSign (σ : Signs S) (p : ℕ) : ℤ :=
  if p = 2 then ∏ q ∈ S.primeFactors, tSign σ q else tSign σ p

theorem tSign_sq (σ : Signs S) (p : ℕ) : tSign σ p * tSign σ p = 1 := by
  unfold tSign
  split_ifs with h
  · have hp := Nat.prime_of_mem_primeFactors h
    have hj : jacobiSym (-1) p = 1 ∨ jacobiSym (-1) p = -1 :=
      jacobiSym.eq_one_or_neg_one (by simp)
    unfold sgnB
    rcases hj with hj | hj <;> cases σ ⟨p, h⟩ <;> simp [hj]
  · rfl

theorem tSign_pm (σ : Signs S) (p : ℕ) : tSign σ p = 1 ∨ tSign σ p = -1 :=
  Int.eq_one_or_neg_one_of_mul_eq_one (tSign_sq σ p)

theorem eSign_prod (hSodd : Odd S) (σ : Signs S) :
    ∏ p ∈ insert 2 S.primeFactors, eSign σ p = 1 := by
  have h2 : 2 ∉ S.primeFactors := fun h =>
    absurd (hSodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors h)) (by decide)
  rw [Finset.prod_insert h2]
  have : ∏ p ∈ S.primeFactors, eSign σ p = ∏ p ∈ S.primeFactors, tSign σ p :=
    Finset.prod_congr rfl fun p hp => by
      unfold eSign; rw [if_neg (by rintro rfl; exact h2 hp)]
  rw [this]
  unfold eSign; rw [if_pos rfl, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun p _ => tSign_sq σ p

/-- **Lemma 3.3** (Berkovich–Hanke–Jagy): for $S$ odd and squarefree there are positive definite binary forms
$B_\sigma$ of discriminant $-8S$, one for each sign vector $\sigma = (\sigma_p)_{p \mid S}$, such that the genera
of $B_\sigma(x,y) + 2Sz^2$ exhaust the S-genus and $\varepsilon_p(B_\sigma + 2Sz^2) = \sigma_p$ (`SGenusParam`;
the genera are pairwise distinct by `SGenusParam.disjoint`). Proved from the genus theory of binary forms
(Gauss's characters and existence of genera, `Binary.exists_form_of_signs`), as the source indicates. -/
@[kb "berkovich2012" "§3, Lemma 3.3, p. 3"]
theorem lemma_3_3 (hSodd : Odd S) (hSsf : Squarefree S) : ∃ B : Signs S → BinQF, SGenusParam S B := by
  classical
  haveI hQD := isQuadDisc_neg_eight_mul hSodd hSsf
  have hS0 : S ≠ 0 := by rintro rfl; exact absurd hSodd (by decide)
  have hD : -8 * (S : ℤ) < 0 := by have : (0 : ℤ) < S := by exact_mod_cast Nat.pos_of_ne_zero hS0
                                   omega
  have hPF := primeFactors_neg_eight_mul hS0
  have h2 : 2 ∉ S.primeFactors := fun h =>
    absurd (hSodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors h)) (by decide)
  have hex : ∀ σ : Signs S, ∃ f : BinQF, Primitive f ∧ f.disc = -8 * S ∧ f.PosDef' ∧
      ∀ p ∈ (-8 * (S : ℤ)).natAbs.primeFactors, formChar f p = eSign σ p := fun σ =>
    exists_form_of_signs hD (eSign σ)
      (fun p _ => by unfold eSign; split_ifs
                     · exact Int.eq_one_or_neg_one_of_mul_eq_one
                         (by rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun q _ => tSign_sq σ q)
                     · exact tSign_pm σ p)
      (by rw [hPF]; exact eSign_prod hSodd σ)
  choose B hBprim hBd hBpos hBchar using hex
  -- the characters of `B σ` at odd `p ∣ S`
  have hcharS : ∀ σ (p : {p // p ∈ S.primeFactors}),
      formChar (B σ) p = jacobiSym (-1) p * sgnB (σ p) := by
    intro σ p
    rw [hBchar σ p (by rw [hPF]; exact Finset.mem_insert_of_mem p.2)]
    unfold eSign tSign
    rw [if_neg (by intro h; exact h2 (h ▸ p.2)), dif_pos p.2]
  -- the signs
  have hsign : ∀ σ (p : {p // p ∈ S.primeFactors}),
      haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
      epsP p (sForm S (B σ)) = sgnB (σ p) := by
    intro σ p
    haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    rw [epsP_sForm hSodd hSsf (hBd σ) (Nat.dvd_of_mem_primeFactors p.2), hcharS,
      ← jacobiSym.legendreSym.to_jacobiSym, ← mul_assoc, ← sq, legendreSym.sq_one]
    · ring
    · simp
  refine ⟨B, hBpos, hBd, ?_, hsign⟩
  -- covering
  rintro c ⟨B', hB'pos, hB'd, hc⟩
  have hB'prim := primitive_of_disc hSodd hSsf hB'd
  let σ : Signs S := fun p =>
    haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    decide (epsP p (sForm S B') = 1)
  -- the characters agree at odd p
  have hodd : ∀ p ∈ S.primeFactors, formChar B' p = formChar (B σ) p := by
    intro p hp
    haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    have hl : legendreSym p (-1) * legendreSym p (-1) = 1 := by
      rw [← sq, legendreSym.sq_one]; simp
    have e1 := epsP_sForm hSodd hSsf hB'd (Nat.dvd_of_mem_primeFactors hp)
    have e2 := hsign σ ⟨p, hp⟩
    rw [epsP_sForm hSodd hSsf (hBd σ) (Nat.dvd_of_mem_primeFactors hp)] at e2
    have hσ : sgnB (σ ⟨p, hp⟩) = epsP p (sForm S B') := by
      have hpm : epsP p (sForm S B') = 1 ∨ epsP p (sForm S B') = -1 := by
        unfold epsP; split_ifs <;> simp
      rcases hpm with h | h <;> simp [σ, sgnB, h]
    rw [hσ, e1] at e2
    calc formChar B' p = legendreSym p (-1) * legendreSym p (-1) * formChar B' p := by rw [hl, one_mul]
      _ = legendreSym p (-1) * legendreSym p (-1) * formChar (B σ) p := by rw [mul_assoc, ← e2, ← mul_assoc]
      _ = formChar (B σ) p := by rw [hl, one_mul]
  -- and at 2, by the product formula
  have hall : ∀ p ∈ (-8 * (S : ℤ)).natAbs.primeFactors, formChar B' p = formChar (B σ) p := by
    rw [hPF]
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · have p1 := prod_formChar_eq_one hB'prim hB'd hB'pos
      have p2 := prod_formChar_eq_one (hBprim σ) (hBd σ) (hBpos σ)
      rw [hPF, Finset.prod_insert h2] at p1 p2
      rw [Finset.prod_congr rfl hodd] at p1
      exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one p2) (p1.trans p2.symm)
    · exact hodd p hp
  have hgen : SameGenus B' (B σ) :=
    (sameGenus_iff_formChar_eq hB'prim (hBprim σ) hB'd (hBd σ) hB'pos (hBpos σ)).2 hall
  obtain ⟨Q', rfl, hQ'⟩ := hc
  exact Set.mem_iUnion.2 ⟨σ, ⟨Q', rfl, (sameGenus_sForm hgen).symm.trans hQ'⟩⟩

/-- **Theorem 6.1 (the twisted S-genus identity), unconditional.** Let $S$ be an odd squarefree natural
number, $W \mid S$, and $m \in \mathbb{N}$ with $W \mid m$ and $m \equiv 1, 2 \pmod 4$. Then
$$\sum_{Q \in S\text{-genus}} \epsilon_W(Q)\, \frac{r_Q(m)}{|\mathrm{Aut}(Q)|} =
W\, \frac{r_{x^2+y^2+z^2}(m/W^2)}{48},$$
where the right side is $0$ if $W^2 \nmid m$. The sum is over the classes of the S-genus (`SGenus`),
$\epsilon_W = \prod_{p \mid W} \varepsilon_p$ (`QClass.epsW`). -/
@[kb "berkovich2012" "§6, Theorem 6.1, p. 7"]
theorem theorem_6_1 {S : ℕ} (hSodd : Odd S) (hSsf : Squarefree S) {W : ℕ} (hW : W ∣ S)
    {m : ℕ} (hWm : W ∣ m) (hm4 : m % 4 = 1 ∨ m % 4 = 2) :
    ∑ᶠ c ∈ SGenus S, (QClass.epsW W c : ℝ) * c.repNum m / c.autCard =
      W * (if W ^ 2 ∣ m then (repNum (sumSq 3) ((m / W ^ 2 : ℕ) : ℤ) : ℝ) else 0) / 48 :=
  have ⟨_, hP⟩ := lemma_3_3 hSodd hSsf
  theorem_6_1_of_param hSodd hSsf hP hW hWm hm4

/-- **Corollary 6.2 (the S-genus identity), unconditional.** For $S$ odd squarefree and
$m \equiv 1, 2 \pmod 4$,
$$\sum_{Q \in S\text{-genus}} \frac{r_Q(m)}{|\mathrm{Aut}(Q)|} = \frac{r_{x^2+y^2+z^2}(m)}{48}.$$ -/
@[kb "berkovich2012" "§6, Corollary 6.2, p. 7"]
theorem corollary_6_2 {S : ℕ} (hSodd : Odd S) (hSsf : Squarefree S) {m : ℕ} (hm4 : m % 4 = 1 ∨ m % 4 = 2) :
    ∑ᶠ c ∈ SGenus S, (c.repNum m : ℝ) / c.autCard = (repNum (sumSq 3) (m : ℤ) : ℝ) / 48 :=
  have ⟨_, hP⟩ := lemma_3_3 hSodd hSsf
  corollary_6_2_of_param hSodd hSsf hP hm4

end QuadFormsKB.Berkovich2012
