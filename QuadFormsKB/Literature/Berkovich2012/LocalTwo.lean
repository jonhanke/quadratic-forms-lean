import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Berkovich2012.Lemma31Local
import QuadFormsKB.Literature.ConwaySloane.TwoAdicClassification

/-!
# Berkovich–Hanke–Jagy, Lemma 3.1 at $p = 2$: $B(x,y) + 2Sz^2 \sim_{\mathbb Z_2} ux^2 + 2uy^2 + 2z^2$

Source: A. Berkovich, J. Hanke and W. Jagy, arXiv:1010.1926v2 (bib key `berkovich2012`), §3, proof of Lemma 3.1,
p. 2 ("$Q \sim_{\mathbb Z_p} \alpha x^2 + 2S\alpha y^2 + 2Sz^2$" for every prime $p$), and §4, Lemma 4.3, p. 5, where
the genera of the S-genus are used in the 2-adic shape $ux^2 + 2uy^2 + 2z^2$, $u$ odd.

The source states the 2-adic shape without proof. Here: $B(x,y) + 2Sz^2 \cong_{\mathbb Z_2} \mathrm{diag}(\alpha, 2\alpha S,
2S)$ with $\alpha \in \{a, c\}$ odd (`odd_a_or_c`, `zpEquiv_sGram_diag`), and
$\mathrm{diag}(\alpha, 2\alpha S, 2S) \cong_{\mathbb Z_2} \mathrm{diag}(u, 2u, 2)$ for a suitable odd $u$ by Conway–Sloane's
Theorem 10 (*Sphere Packings, Lattices and Groups* Ch. 15, §7.5: `TwoAdic.zpEquiv_iff_theorem10Cond`): the two forms have 2-adic symbols
$1^{\pm1}_{\alpha}2^{\pm2}_{t}$ with one compartment, and $u$ is chosen (`exists_u_t10`, a check over the residues
of $\alpha$, $S$ mod 8) so that the signs agree at both scales with equal total oddity, or differ at both scales with
total oddity differing by $4$ (`theorem10Cond_two`). Example: $S = 3$, $B = x^2 + 6y^2$: $x^2 + 6y^2 + 6z^2
\cong_{\mathbb Z_2} 5x^2 + 10y^2 + 2z^2$ ($u = 1$ does not work: the signs agree, but the total oddities are $1 + 3 + 3 = 7$ and $1 + 1 + 1 = 3$).
-/

namespace QuadFormsKB.Berkovich2012

open QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass
  QuadFormsKB.LocalDensity Finset

/-- The blocks $\langle a\rangle \perp 2\langle b\rangle \perp 2\langle s\rangle$. -/
def threeBlocks (a b s : ℤ) : List Cassels.DyBlock := [.sq 0 a, .sq 1 b, .sq 1 s]

/-- **Theorem 10 for two adjacent type I constituents.** If two 2-adic symbols vanish from the scale $4$ on,
agree in dimensions and types with $f_1$, $f_2$ of type I, and either the signs agree at both scales and the total
oddities agree, or the signs differ at both scales and the total oddities differ by $4$, then Theorem 10's
condition holds. -/
lemma theorem10Cond_two (σ τ : TwoSymbol)
    (hdim : ∀ k, (σ k).dim = (τ k).dim ∧ (σ k).type = (τ k).type)
    (hI0 : IsTypeI σ 0) (hI1 : IsTypeI σ 1)
    (hsign : (σ 0).sign ≠ (τ 0).sign ↔ (σ 1).sign ≠ (τ 1).sign)
    (hodd : (σ 0).oddity - (τ 0).oddity + ((σ 1).oddity - (τ 1).oddity) =
      if (σ 1).sign ≠ (τ 1).sign then 4 else 0) :
    Theorem10Cond σ τ 2 := by
  refine ⟨hdim, fun m hm => ?_⟩
  rcases hm with hm | hm
  · have hL : (range 2).filter (fun k : ℕ => (k : ℤ) < m) = ∅ := by
      ext k; simp; omega
    rw [hL, Finset.sum_empty]
    simp only [Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have h0 : min ((0 : ℕ) : ℤ) m = m := min_eq_right (by omega)
    have h1 : min ((1 : ℕ) : ℤ) m = m := min_eq_right (by omega)
    rw [h0, h1]
    by_cases hs : (σ 1).sign ≠ (τ 1).sign
    · rw [if_pos (hsign.2 hs), if_pos hs, ← two_mul, ← mul_assoc]
      have : (4 * 2 : ZMod 8) = 0 := by decide
      rw [this, zero_mul]
    · rw [if_neg (fun h => hs (hsign.1 h)), if_neg hs]; simp
  · have hm2 : 2 ≤ m := by
      by_contra hlt
      apply hm
      have : m.toNat = 0 ∨ m.toNat = 1 := by omega
      rcases this with h | h <;> rw [h] <;> assumption
    have hL : (range 2).filter (fun k : ℕ => (k : ℤ) < m) = range 2 := by
      ext k; simp; omega
    rw [hL]
    simp only [Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have h0 : min ((0 : ℕ) : ℤ) m = 0 := min_eq_left (by omega)
    have h1 : min ((1 : ℕ) : ℤ) m = 1 := min_eq_left (by omega)
    rw [h0, h1, hodd]
    by_cases hs : (σ 1).sign ≠ (τ 1).sign
    · rw [if_pos (hsign.2 hs), if_pos hs, if_pos hs]; simp
    · rw [if_neg (fun h => hs (hsign.1 h)), if_neg hs, if_neg hs]; simp

/-- Theorem 10's sign and oddity conditions for $\langle a\rangle \perp 2\langle as\rangle \perp 2\langle s\rangle$ against
$\langle u\rangle \perp 2\langle u\rangle \perp 2\langle 1\rangle$ (residues mod 8). -/
def T10Ok (a s u : ℤ) : Prop :=
  ((blockSymbol (threeBlocks a (a * s % 8) s) 0).sign ≠ (blockSymbol (twoBlocks u) 0).sign ↔
    (blockSymbol (threeBlocks a (a * s % 8) s) 1).sign ≠ (blockSymbol (twoBlocks u) 1).sign) ∧
  (blockSymbol (threeBlocks a (a * s % 8) s) 0).oddity - (blockSymbol (twoBlocks u) 0).oddity +
      ((blockSymbol (threeBlocks a (a * s % 8) s) 1).oddity - (blockSymbol (twoBlocks u) 1).oddity) =
    if (blockSymbol (threeBlocks a (a * s % 8) s) 1).sign ≠ (blockSymbol (twoBlocks u) 1).sign then 4 else 0

instance (a s u : ℤ) : Decidable (T10Ok a s u) := by unfold T10Ok; infer_instance

/-- The finite check: for all residues $a, s \in \{1,3,5,7\}$ some $u \in \{1,3,5,7\}$ satisfies Theorem 10's
conditions. -/
lemma exists_u_t10 : ∀ a ∈ ({1, 3, 5, 7} : Finset ℤ), ∀ s ∈ ({1, 3, 5, 7} : Finset ℤ),
    ∃ u ∈ ({1, 3, 5, 7} : Finset ℤ), T10Ok a s u := by
  decide

lemma odd_mod8 {x : ℤ} (hx : Odd x) : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by
  obtain ⟨k, rfl⟩ := hx; omega

lemma mem_odd_res {x : ℤ} (hx : x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 7) : x ∈ ({1, 3, 5, 7} : Finset ℤ) := by
  rcases hx with rfl | rfl | rfl | rfl <;> decide

lemma odd_res_of_mem {x : ℤ} (hx : x ∈ ({1, 3, 5, 7} : Finset ℤ)) : x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 7 := by
  simpa using hx

/-- The 2-adic symbol of $\mathrm{diag}(\alpha, 2\alpha s, 2s)$, $\alpha$, $s$ odd. -/
lemma isTwoSymbolOf_threeDiag {α t : ℤ} (hα : Odd α) (ht : Odd t) :
    IsTwoSymbolOf ((Matrix.diagonal ![α, 2 * α * t, 2 * t]).map (Int.cast : ℤ → ℚ_[2]))
      (blockSymbol (threeBlocks (α % 8) (α % 8 * (t % 8) % 8) (t % 8))) := by
  have hb : α % 8 * (t % 8) % 8 = (α * t) % 8 := (Int.mul_emod α t 8).symm
  rw [hb]
  have hαt : Odd (α * t) := hα.mul ht
  have h1 := odd_mod8 hα
  have h2 := odd_mod8 hαt
  have h3 := odd_mod8 ht
  refine ⟨threeBlocks (α % 8) (α * t % 8) (t % 8), ?_, ?_, rfl, ?_, rfl⟩
  · intro b hb
    simp only [threeBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp [Cassels.DyBlock.Valid, h1, h2, h3]
  · intro b hb
    simp only [threeBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp [blockExp]
  · have hD : ∀ h : Cassels.dyDim (threeBlocks (α % 8) (α * t % 8) (t % 8)) = 3,
        (Cassels.dyMat (threeBlocks (α % 8) (α * t % 8) (t % 8))).submatrix (Fin.cast h.symm) (Fin.cast h.symm) =
        Matrix.diagonal ![((α % 8 : ℤ) : ℚ_[2]), 2 * ((α * t % 8 : ℤ) : ℚ_[2]), 2 * ((t % 8 : ℤ) : ℚ_[2])] := by
      intro h
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [threeBlocks, Cassels.dyMat, Cassels.orthSumMat, Cassels.DyBlock.mat, Matrix.diagonal,
          Matrix.fromBlocks, finSumFinEquiv] <;> rfl
    rw [hD (by simp [threeBlocks, Cassels.dyDim, Cassels.DyBlock.dim]), Matrix.diagonal_map Int.cast_zero]
    apply zpEquiv_diagonal
    intro i
    obtain ⟨t₁, ht₁, he₁⟩ := unitSq_of_mod8 α (α % 8) hα ⟨α / 8, by omega⟩
    obtain ⟨t₂, ht₂, he₂⟩ := unitSq_of_mod8 (α * t) (α * t % 8) hαt ⟨α * t / 8, by omega⟩
    obtain ⟨t₃, ht₃, he₃⟩ := unitSq_of_mod8 t (t % 8) ht ⟨t / 8, by omega⟩
    fin_cases i
    · exact ⟨t₁, ht₁, by simpa using he₁⟩
    · refine ⟨t₂, ht₂, ?_⟩
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [← he₂]; push_cast; ring
    · refine ⟨t₃, ht₃, ?_⟩
      simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_zero]
      rw [← he₃]; push_cast; ring

/-- The 2-adic symbol of $\mathrm{diag}(u, 2u, 2)$, $u \in \{1, 3, 5, 7\}$. -/
lemma isTwoSymbolOf_twoDiag {u : ℤ} (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) :
    IsTwoSymbolOf ((Matrix.diagonal ![u, 2 * u, 2]).map (Int.cast : ℤ → ℚ_[2])) (blockSymbol (twoBlocks u)) := by
  refine ⟨twoBlocks u, ?_, ?_, rfl, ?_, rfl⟩
  · intro b hb
    simp only [twoBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp [Cassels.DyBlock.Valid, hu]
  · intro b hb
    simp only [twoBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp [blockExp]
  · have hD : ∀ h : Cassels.dyDim (twoBlocks u) = 3,
        (Cassels.dyMat (twoBlocks u)).submatrix (Fin.cast h.symm) (Fin.cast h.symm) =
        (Matrix.diagonal ![u, 2 * u, 2]).map (Int.cast : ℤ → ℚ_[2]) := by
      intro h
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [twoBlocks, Cassels.dyMat, Cassels.orthSumMat, Cassels.DyBlock.mat, Matrix.diagonal,
          Matrix.fromBlocks, finSumFinEquiv] <;> rfl
    rw [hD (by simp [twoBlocks, Cassels.dyDim, Cassels.DyBlock.dim])]
    exact Cassels.ZpEquiv.refl _

/-- Over $\mathbb Z_2$, $\langle \alpha, 2\alpha t, 2t\rangle \cong \langle u, 2u, 2\rangle$ for some odd $u$
($\alpha$, $t$ odd): Conway–Sloane's Theorem 10 (sign walking and oddity fusion between the two adjacent type I
constituents $f_1$, $f_2$). -/
theorem zpEquiv_two_diag {α t : ℤ} (hα : Odd α) (ht : Odd t) :
    ∃ u : ℤ, Odd u ∧ Cassels.ZpEquiv
      ((Matrix.diagonal ![α, 2 * α * t, 2 * t]).map (Int.cast : ℤ → ℚ_[2]))
      ((Matrix.diagonal ![u, 2 * u, 2]).map (Int.cast : ℤ → ℚ_[2])) := by
  obtain ⟨u, hu, hok⟩ := exists_u_t10 (α % 8) (mem_odd_res (odd_mod8 hα)) (t % 8) (mem_odd_res (odd_mod8 ht))
  have hu' := odd_res_of_mem hu
  refine ⟨u, by rcases hu' with rfl | rfl | rfl | rfl <;> decide, ?_⟩
  have hF := isTwoSymbolOf_threeDiag hα ht
  have hG := isTwoSymbolOf_twoDiag hu'
  set a := α % 8
  set s := t % 8
  have ha := odd_mod8 hα
  have hs := odd_mod8 ht
  have hsupp1 : (blockSymbol (threeBlocks a (a * s % 8) s)).SupportedBelow 2 := by
    intro k hk
    have hk' : (k : ℤ) ≠ 0 ∧ (k : ℤ) ≠ 1 := by omega
    have hf : List.filter (fun b => decide (blockExp b = (k : ℤ))) (threeBlocks a (a * s % 8) s) = [] := by
      simp [threeBlocks, blockExp, Ne.symm hk'.1, Ne.symm hk'.2]
    unfold blockSymbol
    simp only [hf]
    rfl
  refine (TwoAdic.zpEquiv_iff_theorem10Cond hF hG hsupp1 (blockSymbol_twoBlocks_supported u)).2 ?_
  refine theorem10Cond_two _ _ ?_ ?_ ?_ hok.1 hok.2
  · intro k
    rcases k with _ | _ | k
    · simp [blockSymbol, threeBlocks, twoBlocks, blockExp, Cassels.DyBlock.dim, IsSqBlock]
    · simp [blockSymbol, threeBlocks, twoBlocks, blockExp, Cassels.DyBlock.dim, IsSqBlock]
    · rw [hsupp1 (k + 2) (by omega), blockSymbol_twoBlocks_supported u (k + 2) (by omega)]
      exact ⟨rfl, rfl⟩
  · simp [IsTypeI, blockSymbol, threeBlocks, blockExp, IsSqBlock]
  · simp [IsTypeI, blockSymbol, threeBlocks, blockExp, IsSqBlock]

/-- For $S$ odd and $B = ax^2 + bxy + cy^2$ of discriminant $-8S$, one of $a$, $c$ is odd. -/
lemma odd_a_or_c {S : ℕ} (hSodd : Odd S) {B : BinQF} (hd : B.disc = -8 * S) : Odd B.a ∨ Odd B.c := by
  by_contra hcon
  push Not at hcon
  rw [Int.not_odd_iff_even, Int.not_odd_iff_even] at hcon
  obtain ⟨a', ha'⟩ := hcon.1
  obtain ⟨c', hc'⟩ := hcon.2
  obtain ⟨k, hk⟩ := even_b_of_disc hd
  unfold BinQF.disc at hd
  rw [hk, ha', hc'] at hd
  obtain ⟨S', hS'⟩ := hSodd
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    have : (m + m + (m + m)) ^ 2 - 4 * (a' + a') * (c' + c') = 16 * (m * m) - 16 * (a' * c') := by ring
    rw [this] at hd
    have hS'' : (S : ℤ) = 2 * S' + 1 := by exact_mod_cast hS'
    omega
  · subst hm
    have : (2 * m + 1 + (2 * m + 1)) ^ 2 - 4 * (a' + a') * (c' + c') =
        16 * (m * m) + 16 * m + 4 - 16 * (a' * c') := by ring
    rw [this] at hd
    have hS'' : (S : ℤ) = 2 * S' + 1 := by exact_mod_cast hS'
    omega

/-- **The 2-adic structure of the S-genus** (Berkovich–Hanke–Jagy, proof of Lemma 3.1, p. 2, and the form
used in Lemma 4.3, p. 5): for $S$ odd and $B$ of discriminant $-8S$,
$B(x,y) + 2Sz^2 \sim_{\mathbb Z_2} u x^2 + 2u y^2 + 2z^2$ for some odd $u$. -/
@[kb "berkovich2012" "§3, Lemma 3.1 and its proof, p. 2 (p = 2); §4, Lemma 4.3, p. 5"]
theorem local_two_of_disc {S : ℕ} (hSodd : Odd S) {B : BinQF} (hd : B.disc = -8 * S) :
    ∃ u : ℤ, Odd u ∧ IsometricGL ((sForm S B).map (Int.castRingHom ℤ_[2]))
      ((QuadForm.diag ![u, 2 * u, 2]).map (Int.castRingHom ℤ_[2])) := by
  have hSo : Odd (S : ℤ) := by exact_mod_cast hSodd
  have key : ∀ α : ℤ, Odd α → Cassels.ZpEquiv ((sGram S B).map (Int.cast : ℤ → ℚ_[2]))
      ((Matrix.diagonal ![α, 2 * α * S, 2 * S]).map (Int.cast : ℤ → ℚ_[2])) →
      ∃ u : ℤ, Odd u ∧ IsometricGL ((sForm S B).map (Int.castRingHom ℤ_[2]))
        ((QuadForm.diag ![u, 2 * u, 2]).map (Int.castRingHom ℤ_[2])) := by
    intro α hα h1
    obtain ⟨u, hu, h2⟩ := zpEquiv_two_diag hα hSo
    refine ⟨u, hu, ?_⟩
    rw [sForm_eq_ofMatrixZ hd, diag_eq_ofMatrixZ]
    exact (isometricGL_padic_iff (sGram_transpose _ B) (Matrix.diagonal_transpose _)).2 (h1.trans h2)
  have h2 : ∀ x : ℤ, Odd x → ¬ ((2 : ℕ) : ℤ) ∣ x := fun x hx h => by
    obtain ⟨k, rfl⟩ := hx; omega
  rcases odd_a_or_c hSodd hd with ha | hc
  · exact key B.a ha ((zpEquiv_sGram_diag (p := 2) hd).1 (h2 _ ha))
  · exact key B.c hc ((zpEquiv_sGram_diag (p := 2) hd).2 (h2 _ hc))

end QuadFormsKB.Berkovich2012
