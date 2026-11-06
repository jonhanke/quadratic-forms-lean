import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Berkovich2012.Mass
import QuadFormsKB.Literature.ConwaySloane.OddClassification

/-!
# Berkovich–Hanke–Jagy, Lemma 3.1 at the primes $p \mid S$

Source: A. Berkovich, J. Hanke and W. Jagy, *A proof of the S-genus identities for ternary quadratic
forms*, arXiv:1010.1926v2 (bib key `berkovich2012`), §3, Lemma 3.1 and its proof, pp. 2–3.

For $B = ax^2 + bxy + cy^2$ of discriminant $-8S$ ($b = 2k$, $ac - k^2 = 2S$) the integral substitution
with columns $e_0$, $-k e_0 + a e_1$, $e_2$ (determinant $a$) takes the Gram matrix of $B(x,y) + 2Sz^2$ to
$\mathrm{diag}(a, 2aS, 2S)$ (`diagT_congr`); the columns $e_1$, $c e_0 - k e_1$, $e_2$ (determinant $-c$)
give $\mathrm{diag}(c, 2cS, 2S)$. This is the source's diagonalization "$Q \sim_{\mathbb Z_p} \alpha x^2 + 2S\alpha y^2
+ 2Sz^2$", made explicit. For an odd prime $p \mid S$, $S$ squarefree, $p$ divides at most one of $a$, $c$,
and with $\alpha \in \{a, c\}$ a $p$-adic unit, $\mathrm{diag}(\alpha, 2\alpha S, 2S)$ and
$\mathrm{diag}(\alpha, \alpha p, p)$ have the same $p$-adic symbol $1^{\pm1}p^{\pm2}$, hence are
$\mathbb Z_p$-equivalent (`zpEquiv_of_oddSymbol_eq`, Conway–Sloane Thm. 9). This is `local_odd_of_disc`.
-/

namespace QuadFormsKB.Berkovich2012

open QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass
  QuadFormsKB.LocalDensity Finset

/-- The substitution with columns $e_0$, $-k e_0 + a e_1$, $e_2$. -/
def diagT (a k : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![1, -k, 0; 0, a, 0; 0, 0, 1]

/-- The substitution with columns $e_1$, $c e_0 - k e_1$, $e_2$. -/
def diagT' (c k : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![0, c, 0; 1, -k, 0; 0, 0, 1]

lemma diagT_congr {S : ℕ} {B : BinQF} (hd : B.disc = -8 * S) :
    (diagT B.a (B.b / 2)).transpose * sGram S B * diagT B.a (B.b / 2) =
      Matrix.diagonal ![B.a, 2 * B.a * S, 2 * S] := by
  obtain ⟨k, hk⟩ := even_b_of_disc hd
  have hk2 : B.b / 2 = k := by omega
  unfold BinQF.disc at hd
  rw [hk] at hd
  have h2S : B.a * B.c - k * k = 2 * S := by nlinarith
  rw [hk2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagT, sGram, hk2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal] <;>
    first | ring1 | linear_combination B.a * h2S | linear_combination (-B.a) * h2S

lemma diagT'_congr {S : ℕ} {B : BinQF} (hd : B.disc = -8 * S) :
    (diagT' B.c (B.b / 2)).transpose * sGram S B * diagT' B.c (B.b / 2) =
      Matrix.diagonal ![B.c, 2 * B.c * S, 2 * S] := by
  obtain ⟨k, hk⟩ := even_b_of_disc hd
  have hk2 : B.b / 2 = k := by omega
  unfold BinQF.disc at hd
  rw [hk] at hd
  have h2S : B.a * B.c - k * k = 2 * S := by nlinarith
  rw [hk2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagT', sGram, hk2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal] <;>
    first | ring1 | linear_combination B.c * h2S | linear_combination (-B.c) * h2S

lemma diagT_det (a k : ℤ) : (diagT a k).det = a := by
  simp [diagT, Matrix.det_fin_three]

lemma diagT'_det (c k : ℤ) : (diagT' c k).det = -c := by
  simp [diagT', Matrix.det_fin_three]

/-- Over $\mathbb Z_p$, $B(x,y) + 2Sz^2 \cong \mathrm{diag}(\alpha, 2\alpha S, 2S)$ for $\alpha \in \{a, c\}$ prime
to $p$. -/
lemma zpEquiv_sGram_diag {p : ℕ} [Fact p.Prime] {S : ℕ} {B : BinQF} (hd : B.disc = -8 * S) :
    (¬ (p : ℤ) ∣ B.a → Cassels.ZpEquiv ((sGram S B).map (Int.cast : ℤ → ℚ_[p]))
      ((Matrix.diagonal ![B.a, 2 * B.a * S, 2 * S]).map (Int.cast : ℤ → ℚ_[p]))) ∧
    (¬ (p : ℤ) ∣ B.c → Cassels.ZpEquiv ((sGram S B).map (Int.cast : ℤ → ℚ_[p]))
      ((Matrix.diagonal ![B.c, 2 * B.c * S, 2 * S]).map (Int.cast : ℤ → ℚ_[p]))) := by
  refine ⟨fun ha => ?_, fun hc => ?_⟩
  · have h := Cassels.Ch9Ex6.zpEquiv_of_unit_det (p := p) (sGram S B) (diagT B.a (B.b / 2))
      (by rw [diagT_det]; exact ha)
    rwa [diagT_congr hd] at h
  · have h := Cassels.Ch9Ex6.zpEquiv_of_unit_det (p := p) (sGram S B) (diagT' B.c (B.b / 2))
      (by rw [diagT'_det, dvd_neg]; exact hc)
    rwa [diagT'_congr hd] at h

/-- The $p$-adic symbol of $\mathrm{diag}(u_0, pu_1, pu_2)$ ($u_i$ prime to $p$) is $1^{\pm1}p^{\pm2}$ with both
signs those of $u_0$, provided $u_1u_2$ and $u_0$ have the same square class. -/
lemma isOddSymbolOf_diag3 {p : ℕ} [Fact p.Prime] {u₀ u₁ u₂ : ℤ} (h₀ : ¬ (p : ℤ) ∣ u₀) (h₁ : ¬ (p : ℤ) ∣ u₁)
    (h₂ : ¬ (p : ℤ) ∣ u₂) (hs : IsSquare ((u₁ : ℚ_[p]) * u₂) ↔ IsSquare (u₀ : ℚ_[p])) :
    IsOddSymbolOf p ((Matrix.diagonal ![u₀, p * u₁, p * u₂]).map (Int.cast : ℤ → ℚ_[p]))
      (oddSym (sqSign (p := p) u₀)) := by
  classical
  have hn : ∀ {w : ℤ}, ¬ (p : ℤ) ∣ w → ‖(w : ℚ_[p])‖ = 1 := fun {w} hw =>
    le_antisymm (Padic.norm_int_le_one w) (not_lt.1 fun h' => hw (Padic.norm_intCast_lt_one_iff.1 h'))
  refine ⟨![0, 1, 1], ![(u₀ : ℚ_[p]), (u₁ : ℚ_[p]), (u₂ : ℚ_[p])], ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [hn h₀, hn h₁, hn h₂]
  · have : (Matrix.diagonal ![u₀, p * u₁, p * u₂]).map (Int.cast : ℤ → ℚ_[p]) =
        Matrix.diagonal fun i => (p : ℚ_[p]) ^ (![0, 1, 1] i) *
          ![(u₀ : ℚ_[p]), (u₁ : ℚ_[p]), (u₂ : ℚ_[p])] i := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
    rw [this]; exact Cassels.ZpEquiv.refl _
  · have hp0 : ∏ i : {i : Fin 3 // (![0, 1, 1] : Fin 3 → ℕ) i = 0},
        ![(u₀ : ℚ_[p]), (u₁ : ℚ_[p]), (u₂ : ℚ_[p])] i.1 = u₀ := by
      rw [← Finset.prod_subtype ({0} : Finset (Fin 3)) (fun x => by fin_cases x <;> simp)]
      simp
    have hp1 : ∏ i : {i : Fin 3 // (![0, 1, 1] : Fin 3 → ℕ) i = 1},
        ![(u₀ : ℚ_[p]), (u₁ : ℚ_[p]), (u₂ : ℚ_[p])] i.1 = (u₁ : ℚ_[p]) * u₂ := by
      rw [← Finset.prod_subtype ({1, 2} : Finset (Fin 3)) (fun x => by fin_cases x <;> simp)]
      simp
    funext k
    simp only [oddSym, oddSymbolOfDiag]
    rcases k with _ | _ | k
    · rw [hp0]
      simp only [if_pos rfl, sqSign]
      congr 1
    · rw [hp1]
      simp only [show (0 + 1 : ℕ) ≠ 0 by omega, ite_false, if_pos rfl, sqSign, hs]
      congr 1
    · simp only [show k + 1 + 1 ≠ 0 by omega, show k + 1 + 1 ≠ 1 by omega, ite_false, OddFactor.trivial,
        OddFactor.mk.injEq]
      have hc : Fintype.card {i : Fin 3 // (![0, 1, 1] : Fin 3 → ℕ) i = k + 1 + 1} = 0 := by
        rw [Fintype.card_eq_zero_iff]
        constructor
        rintro ⟨i, hi⟩
        fin_cases i <;> simp at hi <;> omega
      have hp : (∏ i : {i : Fin 3 // (![0, 1, 1] : Fin 3 → ℕ) i = k + 1 + 1},
          ![(u₀ : ℚ_[p]), (u₁ : ℚ_[p]), (u₂ : ℚ_[p])] i.1) = 1 := by
        have : IsEmpty {i : Fin 3 // (![0, 1, 1] : Fin 3 → ℕ) i = k + 1 + 1} := Fintype.card_eq_zero_iff.1 hc
        exact Finset.prod_of_isEmpty _
      rw [hc, hp, if_pos IsSquare.one]
      simp

lemma isSquare_mul_sq_iff {K : Type*} [Field K] {x y : K} (hy : y ≠ 0) :
    IsSquare (x * y * y) ↔ IsSquare x := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z / y, by field_simp; linear_combination hz⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w * y, by ring⟩

/-- **Lemma 3.1 at $p \mid S$** (Berkovich–Hanke–Jagy, §3, pp. 2–3): for $S$ odd squarefree, $B$ of
discriminant $-8S$ and an odd prime $p \mid S$,
$B(x,y) + 2Sz^2 \sim_{\mathbb Z_p} \alpha x^2 + \alpha p y^2 + p z^2$ for some $\alpha$ prime to $p$ (one of the
outer coefficients $a$, $c$ of $B$). -/
@[kb "berkovich2012" "§3, Lemma 3.1, p. 2 (p | S)"]
theorem local_odd_of_disc {S : ℕ} (hSodd : Odd S) (hSsf : Squarefree S) {B : BinQF}
    (hd : B.disc = -8 * S) {p : ℕ} [hp : Fact p.Prime] (hpS : p ∣ S) :
    ∃ α : ℤ, ¬ (p : ℤ) ∣ α ∧ IsometricGL ((sForm S B).map (Int.castRingHom ℤ_[p]))
      ((QuadForm.diag ![α, α * p, (p : ℤ)]).map (Int.castRingHom ℤ_[p])) := by
  classical
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd (hSodd.of_dvd_nat hpS) (by decide)
  obtain ⟨t, rfl⟩ := hpS
  have hpt : ¬ p ∣ t := by
    intro h
    obtain ⟨t', rfl⟩ := h
    have := hSsf p ⟨t', by ring⟩
    exact hp.out.one_lt.ne' (Nat.isUnit_iff.1 this)
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.out
  have hs : ¬ (p : ℤ) ∣ 2 * t := by
    intro h
    rcases hpZ.dvd_or_dvd h with h | h
    · have : p ∣ 2 := by exact_mod_cast h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)
    · exact hpt (by exact_mod_cast h)
  -- one of `a`, `c` is prime to `p`
  have hac : ¬ (p : ℤ) ∣ B.a ∨ ¬ (p : ℤ) ∣ B.c := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨k, hk⟩ := even_b_of_disc hd
    have hd' := hd
    unfold BinQF.disc at hd'
    rw [hk] at hd'
    have hk2 : (k : ℤ) * k = B.a * B.c - 2 * (p * t : ℕ) := by push_cast at hd' ⊢; linarith
    have hpk : (p : ℤ) ∣ k := by
      have : (p : ℤ) ∣ k * k := by
        rw [hk2]; push_cast
        exact dvd_sub (dvd_mul_of_dvd_left hcon.1 _) ⟨2 * t, by ring⟩
      rcases hpZ.dvd_or_dvd this with h | h <;> exact h
    obtain ⟨a', ha'⟩ := hcon.1
    obtain ⟨c', hc'⟩ := hcon.2
    obtain ⟨k', hk'⟩ := hpk
    have : (p : ℤ) * (2 * t) = p * p * (a' * c' - k' * k') := by
      push_cast at hk2
      rw [ha', hc', hk'] at hk2
      linear_combination hk2
    have h2 : (2 * t : ℤ) = p * (a' * c' - k' * k') := by
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
      apply mul_left_cancel₀ hp0
      linear_combination this
    exact hs ⟨_, h2⟩
  -- the target and its symbol
  have key : ∀ α : ℤ, ¬ (p : ℤ) ∣ α →
      Cassels.ZpEquiv ((sGram (p * t) B).map (Int.cast : ℤ → ℚ_[p]))
        ((Matrix.diagonal ![α, 2 * α * (p * t : ℕ), 2 * (p * t : ℕ)]).map (Int.cast : ℤ → ℚ_[p])) →
      ∃ α : ℤ, ¬ (p : ℤ) ∣ α ∧ IsometricGL ((sForm (p * t) B).map (Int.castRingHom ℤ_[p]))
        ((QuadForm.diag ![α, α * p, (p : ℤ)]).map (Int.castRingHom ℤ_[p])) := by
    intro α hα h1
    refine ⟨α, hα, ?_⟩
    have e1 : Matrix.diagonal ![α, 2 * α * (p * t : ℕ), 2 * (p * t : ℕ)] =
        Matrix.diagonal ![α, p * (α * (2 * t)), p * (2 * t)] := by
      congr 1; funext i; fin_cases i <;> simp <;> push_cast <;> ring
    have hs1 := isOddSymbolOf_diag3 (p := p) hα (u₁ := α * (2 * t)) (u₂ := 2 * t)
      (fun h => (hpZ.dvd_or_dvd h).elim hα hs) hs (by
        have hy : ((2 * t : ℤ) : ℚ_[p]) ≠ 0 := by
          intro h0
          apply hs
          have : (2 * t : ℤ) = 0 := by exact_mod_cast h0
          rw [this]; exact dvd_zero _
        rw [Int.cast_mul]
        exact isSquare_mul_sq_iff hy)
    have hs2 := isOddSymbolOf_diag3 (p := p) hα (u₁ := α) (u₂ := 1) hα
      (fun h => hpZ.not_unit (isUnit_of_dvd_one h)) (by simp)
    rw [e1] at h1
    have h3 := h1.trans (zpEquiv_of_oddSymbol_eq hp2 hs1 hs2)
    have e2 : Matrix.diagonal ![α, (p : ℤ) * α, p * 1] = Matrix.diagonal ![α, α * p, (p : ℤ)] := by
      congr 1; funext i; fin_cases i <;> simp; ring
    rw [e2] at h3
    rw [sForm_eq_ofMatrixZ hd, diag_eq_ofMatrixZ]
    refine (isometricGL_padic_iff (sGram_transpose _ B) (Matrix.diagonal_transpose _)).2 ?_
    exact h3
  rcases hac with ha | hc
  · exact key B.a ha ((zpEquiv_sGram_diag hd).1 ha)
  · exact key B.c hc ((zpEquiv_sGram_diag hd).2 hc)

end QuadFormsKB.Berkovich2012
