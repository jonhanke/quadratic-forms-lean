/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Odd7Symbol

/-!
# Paper 7 at odd primes: the local genera are the tuples of Lemma 2.1

For a place $v \nmid 2$ of $\mathbb Q$ ($p = p_v$ odd) and a fixed integer non-residue $c$ modulo $p$
(`hc : jacobiSym c p = -1`), this file proves the classification half of paper 7's Lemma 2.1 for the *true*
local genera `LocGenus v 3`:

* `exists_tuple`: every nondegenerate primitive local genus is `tupG v c a b e₁ e₂ e₃` for a tuple
  $(a, b; u_1, u_2, u_3)$ satisfying the constraints (1)–(3) of Lemma 2.1 (`IsJordanTuple`);
* `tupG_inj`: distinct such tuples give distinct genera.

*Proof.* $\mathrm{GL}_3(\mathfrak o_v)$-equivalence is $\mathbb Z_p$-equivalence of the Gram matrices $\tfrac12 H$
(`isometricGL_iff_zpEquiv_gram`). Conway–Sloane's classification (`ConwaySloane.theorem9`, with the existence and
uniqueness of the $p$-adic symbol) reduces a genus to its symbol; for the diagonal form $\operatorname{diag}(p^{z_i}w_i)$
this is `symC z (χ(w_i))` (`oddSymbolOfDiag_eq_symC`). Sorting the exponents (`Tuple.sort`), primitivity forces the
smallest exponent to be $0$, and `normT` normalizes the characters to a Jordan tuple with the same symbol.
-/

open IsDedekindDomain NumberField Matrix Finset

namespace QuadFormsKB.Odd7

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Ternary QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.HilbertLocal QuadFormsKB.Siegel QuadFormsKB.Tamagawa

noncomputable section

section AtV

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- The diagonal form $\sum_i p^{z_i}w_i\,x_i^2$ over $\mathfrak o_v$ ($w_i \in \mathbb Z_p^\times$). -/
def dformZ (z : Fin 3 → ℕ) (w : Fin 3 → ℤ_[pv v]ˣ) : QuadForm 𝔬 3 :=
  dform v (fun i => (pv v : ℤ_[pv v]) ^ z i * ((w i : ℤ_[pv v]ˣ) : ℤ_[pv v]))

theorem gramQp_dformZ (z : Fin 3 → ℕ) (w : Fin 3 → ℤ_[pv v]ˣ) :
    gramQp (eInt v) (dformZ v z w) =
      Matrix.diagonal (fun i => (pv v : ℚ_[pv v]) ^ z i * (((w i : ℤ_[pv v]ˣ) : ℤ_[pv v]) : ℚ_[pv v])) := by
  unfold dformZ dform
  rw [gramQp_diag]
  congr 1

/-- **The $p$-adic symbol of the diagonal form** $\sum_i p^{z_i}w_ix_i^2$: its Gram matrix is $\operatorname{diag}(p^{z_i}w_i)$. -/
theorem isOddSymbolOf_dformZ (z : Fin 3 → ℕ) (w : Fin 3 → ℤ_[pv v]ˣ) :
    IsOddSymbolOf (pv v) (gramQp (eInt v) (dformZ v z w))
      (oddSymbolOfDiag (pv v) z (fun i => (((w i : ℤ_[pv v]ˣ) : ℤ_[pv v]) : ℚ_[pv v]))) := by
  refine ⟨z, fun i => (((w i : ℤ_[pv v]ˣ) : ℤ_[pv v]) : ℚ_[pv v]), fun i => ?_, ?_, rfl⟩
  · rw [PadicInt.norm_coe]
    exact PadicInt.isUnit_iff.1 (w i).isUnit
  · rw [gramQp_dformZ]
    exact ZpEquiv.refl _

theorem tupG_eq_dformZ {c : ℤ} (hc : jacobiSym c (pv v) = -1) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) :
    tupG v c a b e₁ e₂ e₃ =
      LocGenus.mk (dformZ v ![0, a, b] ![repU hc e₁, repU hc e₂, repU hc e₃]) := by
  rw [tupG_eq]
  congr 1
  unfold dformZ
  congr 1
  funext i
  fin_cases i <;> simp [tupleVec, repU_val]

/-- **Distinct tuples give distinct genera** (Lemma 2.1, uniqueness): if two tuples $(a,b;u_1,u_2,u_3)$ satisfying
(1)–(3) of Lemma 2.1 give the same local genus, they are equal. -/
@[kb "hanke2011ternary" "§2, Lemma 2.1, pp. 4–5 (distinct tuples, distinct genera)"]
theorem tupG_inj (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {c : ℤ} (hc : jacobiSym c (pv v) = -1) {a b a' b' : ℕ}
    {e₁ e₂ e₃ e₁' e₂' e₃' : ℤˣ} (h : IsJordanTuple a b e₁ e₂ e₃) (h' : IsJordanTuple a' b' e₁' e₂' e₃')
    (hg : tupG v c a b e₁ e₂ e₃ = tupG v c a' b' e₁' e₂' e₃') :
    a = a' ∧ b = b' ∧ e₁ = e₁' ∧ e₂ = e₂' ∧ e₃ = e₃' := by
  have hp2 := pv_ne_two v hv
  rw [tupG_eq_dformZ v hc, tupG_eq_dformZ v hc, LocGenus.mk_eq_mk,
    isometricGL_iff_zpEquiv_gram (eInt v)] at hg
  have h1 := isOddSymbolOf_dformZ v ![0, a, b] ![repU hc e₁, repU hc e₂, repU hc e₃]
  have h2 := isOddSymbolOf_dformZ v ![0, a', b'] ![repU hc e₁', repU hc e₂', repU hc e₃']
  have hσ := oddSymbol_eq_of_zpEquiv hp2 hg h1 h2
  rw [oddSymbolOfDiag_eq_symC hp2, oddSymbolOfDiag_eq_symC hp2] at hσ
  have k1 : (fun i => chiU (![repU hc e₁, repU hc e₂, repU hc e₃] i)) = ![e₁, e₂, e₃] := by
    funext i; fin_cases i <;> simp [chiU_repU]
  have k2 : (fun i => chiU (![repU hc e₁', repU hc e₂', repU hc e₃'] i)) = ![e₁', e₂', e₃'] := by
    funext i; fin_cases i <;> simp [chiU_repU]
  rw [k1, k2, symC_three, symC_three] at hσ
  exact symT_inj h h' hσ

theorem exists_exp_zero_of_prim (z : Fin 3 → ℕ) (w : Fin 3 → ℤ_[pv v]ˣ)
    (hP : Hanke2011Structure.IsPrimitiveForm (dformZ v z w)) : ∃ i, z i = 0 := by
  by_contra hnot
  push_neg at hnot
  unfold Hanke2011Structure.IsPrimitiveForm at hP
  have hle : Ideal.span (Set.range fun q : Fin 3 × Fin 3 => (dformZ v z w).coeff q.1 q.2) ≤
      Ideal.span {eInt v (pv v : ℤ_[pv v])} := by
    rw [Ideal.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    by_cases hij : i = j
    · subst hij
      show (Matrix.diagonal (fun k => eInt v ((pv v : ℤ_[pv v]) ^ z k * ((w k : ℤ_[pv v]ˣ) : ℤ_[pv v]))) i i) ∈ _
      rw [Matrix.diagonal_apply_eq, SetLike.mem_coe, Ideal.mem_span_singleton]
      exact map_dvd (eInt v) (dvd_mul_of_dvd_left (dvd_pow_self _ (hnot i)) _)
    · show (Matrix.diagonal (fun k => eInt v ((pv v : ℤ_[pv v]) ^ z k * ((w k : ℤ_[pv v]ˣ) : ℤ_[pv v]))) i j) ∈ _
      rw [Matrix.diagonal_apply_ne _ hij]
      exact Ideal.zero_mem _
  rw [hP, top_le_iff, Ideal.span_singleton_eq_top] at hle
  exact PadicInt.irreducible_p.not_isUnit ((MulEquiv.isUnit_map (eInt v).toMulEquiv).1 hle)

/-- **Every nondegenerate primitive local genus at $v \nmid 2$ is the genus of a tuple of Lemma 2.1**
(Hanke 2011, Lemma 2.1, pp. 4–5; O'Meara §92:1–2): for $G$ a nondegenerate primitive ternary local genus there is
$(a, b; u_1, u_2, u_3)$ with $0 \le a \le b$ and the constraints (1)–(3) such that $G$ is the class of
$u_1x^2 + p^au_2y^2 + p^bu_3z^2$. Unconditional. -/
@[kb "hanke2011ternary" "§2, Lemma 2.1, pp. 4–5 (genera as tuples)"]
theorem exists_tuple (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {c : ℤ} (hc : jacobiSym c (pv v) = -1) (G : LocGenus v 3)
    (hN : G.Nondeg) (hP : G.Prim) :
    ∃ a b e₁ e₂ e₃, IsJordanTuple a b e₁ e₂ e₃ ∧ G = tupG v c a b e₁ e₂ e₃ := by
  have hp2 := pv_ne_two v hv
  induction G using Quotient.inductionOn with
  | _ T =>
  have hT : T.hessian.det ≠ 0 := (LocGenus.nondeg_mk T).1 hN
  have hPT : Hanke2011Structure.IsPrimitiveForm T := (LocGenus.prim_mk T).1 hP
  obtain ⟨σ, hσ⟩ := exists_isOddSymbolOf hp2 (gramQp_symm (eInt v) T) (gramQp_det (eInt v) T hT)
    (gramQp_norm hp2 (eInt v) T)
  obtain ⟨z, u, hu, hZ, rfl⟩ := hσ
  have hunit : ∀ i, IsUnit (⟨u i, (PadicInt.mem_subring_iff (pv v)).2 (hu i).le⟩ : ℤ_[pv v]) := fun i => by
    refine PadicInt.isUnit_iff.2 ?_
    exact hu i
  set w : Fin 3 → ℤ_[pv v]ˣ := fun i => (hunit i).unit with hw
  have hZ' : ZpEquiv (gramQp (eInt v) T) (gramQp (eInt v) (dformZ v z w)) := by
    rw [gramQp_dformZ]
    exact hZ
  have hiso : IsometricGL T (dformZ v z w) := (isometricGL_iff_zpEquiv_gram (eInt v) _ _).2 hZ'
  have hPT' : Hanke2011Structure.IsPrimitiveForm (dformZ v z w) := isPrimitiveForm_of_isometricGL hiso hPT
  obtain ⟨i0, hi0⟩ := exists_exp_zero_of_prim v z w hPT'
  -- sort the exponents
  set s : Equiv.Perm (Fin 3) := Tuple.sort z with hs
  have hmono : Monotone (fun i => z (s i)) := Tuple.monotone_sort z
  have hz0 : z (s 0) = 0 := by
    have h1 : z (s 0) ≤ z (s (s.symm i0)) := hmono (Fin.zero_le _)
    rw [Equiv.apply_symm_apply, hi0] at h1
    omega
  set a : ℕ := z (s 1) with ha
  set b : ℕ := z (s 2) with hb
  have hab : a ≤ b := hmono (by decide : (1 : Fin 3) ≤ 2)
  have hzfun : (fun i => z (s i)) = ![0, a, b] := by
    funext i
    fin_cases i <;> simp [ha, hb, hz0]
  set x0 : ℤˣ := chiU (w (s 0)) with hx0
  set x1 : ℤˣ := chiU (w (s 1)) with hx1
  set x2 : ℤˣ := chiU (w (s 2)) with hx2
  have e1 : (fun i => chiU (w (s i))) = ![x0, x1, x2] := by
    funext i
    fin_cases i <;> first | rfl | simp [hx0, hx1, hx2]
  have hperm : symC (fun i => z (s i)) (fun i => chiU (w (s i))) = symC z (fun i => chiU (w i)) :=
    symC_perm z (fun i => chiU (w i)) s
  rw [hzfun, e1] at hperm
  set e : ℤˣ × ℤˣ × ℤˣ := normT a b x0 x1 x2 with he
  have k2 : (fun i => chiU (![repU hc e.1, repU hc e.2.1, repU hc e.2.2] i)) = ![e.1, e.2.1, e.2.2] := by
    funext i; fin_cases i <;> simp [chiU_repU]
  have hsym : oddSymbolOfDiag (pv v) z (fun i => (((w i : ℤ_[pv v]ˣ) : ℤ_[pv v]) : ℚ_[pv v])) =
      oddSymbolOfDiag (pv v) ![0, a, b]
        (fun i => (((![repU hc e.1, repU hc e.2.1, repU hc e.2.2] i : ℤ_[pv v]ˣ) : ℤ_[pv v]) : ℚ_[pv v])) := by
    rw [oddSymbolOfDiag_eq_symC hp2, oddSymbolOfDiag_eq_symC hp2, k2, ← hperm, symC_three, symC_three]
    exact symT_normT a b x0 x1 x2
  have hF := isOddSymbolOf_dformZ v z w
  have hG := isOddSymbolOf_dformZ v ![0, a, b] ![repU hc e.1, repU hc e.2.1, repU hc e.2.2]
  rw [← hsym] at hG
  have hE := zpEquiv_of_oddSymbol_eq hp2 hF hG
  have hiso2 : IsometricGL (dformZ v z w) (dformZ v ![0, a, b] ![repU hc e.1, repU hc e.2.1, repU hc e.2.2]) :=
    (isometricGL_iff_zpEquiv_gram (eInt v) _ _).2 hE
  refine ⟨a, b, e.1, e.2.1, e.2.2, isJordanTuple_normT hab _ _ _, ?_⟩
  rw [tupG_eq_dformZ v hc]
  exact LocGenus.mk_eq_mk.2 (hiso.trans hiso2)

end AtV

end

end QuadFormsKB.Odd7
