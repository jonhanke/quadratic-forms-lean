/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Dyadic7Classify
import QuadFormsKB.Tamagawa.Dyadic7Units

/-!
# Paper 6 at $p = 2$: finitely many local genera of a given determinant, every rank

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), §4 (the local sums $A^*_{\mathfrak p;n}(S)$, $B^*_{\mathfrak p;n}(S)$ are finite
sums), at the dyadic place of $\mathbb Q$.

For $v$ the prime of $\mathbb Q$ above $2$, every rank $n$ and every class $S \in \mathrm{SqCl}(\mathbb Q_2^\times,
\mathbb Z_2^\times)$, the set of nondegenerate $\mathbb Z_2$-genera $G$ in $n$ variables with $\det_H(G) = S$ is finite
(`gen_det_finite_two`), hence so is the set of nondegenerate primitive ones (`admGen_finite_two`).

*Proof.* Every nondegenerate genus is the genus of $Q_D = \tfrac12 x^{\mathsf T}H_Dx$ for a list $D$ of Cassels' blocks
$2^eux^2$, $2^e\cdot 2xy$, $2^e(2x^2+2xy+2y^2)$ with $e \ge 0$, $u \in \{1,3,5,7\}$ (`Dyadic7.exists_genusOf`, from
Conway–Sloane's 2-adic Jordan decompositions). Its determinant class is $[2^{h}w]$, $h = \sum_b \dim(b)\,e_b$
(`Dyadic7.det_genusOf`), so $h = \operatorname{ord}_2 S$ is fixed; hence every exponent is at most $h$, and $D$ has at most
$n$ blocks. These lists form a finite set (`Dyadic7.alphabet`), whose image under $D \mapsto$ genus contains the set.

Indices are 0-based.
-/

open IsDedekindDomain NumberField

namespace QuadFormsKB.Hanke2011Structure.RatTwo

open QuadFormsKB.Dyadic7 QuadFormsKB.ConwaySloane Cassels

noncomputable section

theorem length_le_dyDim : ∀ D : List DyBlock, D.length ≤ dyDim D
  | [] => le_rfl
  | b :: D => by
    have h1 : 1 ≤ b.dim := by cases b <;> simp [DyBlock.dim]
    have := length_le_dyDim D
    simp only [List.length_cons, dyDim]
    omega

theorem exp_le_valSum {D : List DyBlock} {b : DyBlock} (hb : b ∈ D) : (blockExp b).toNat ≤ valSum D := by
  have h1 : 1 ≤ b.dim := by cases b <;> simp [DyBlock.dim]
  have hmem : b.dim * (blockExp b).toNat ∈ D.map fun b => b.dim * (blockExp b).toNat := List.mem_map_of_mem hb
  have := List.le_sum_of_mem hmem
  unfold valSum
  calc (blockExp b).toNat ≤ b.dim * (blockExp b).toNat := Nat.le_mul_of_pos_left _ h1
    _ ≤ _ := this

theorem mem_alphabet {h : ℕ} {b : DyBlock} (hv : b.Valid) (h0 : 0 ≤ blockExp b) (hle : (blockExp b).toNat ≤ h) :
    b ∈ alphabet h := by
  classical
  unfold alphabet
  cases b with
  | sq e u =>
    simp only [blockExp] at h0 hle
    refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(e.toNat, u), ?_, ?_⟩))
    · refine Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), ?_⟩
      simp only [DyBlock.Valid] at hv
      simp only [sqUnits, Finset.mem_insert, Finset.mem_singleton]
      exact hv
    · simp [Int.toNat_of_nonneg h0]
  | hyp e =>
    simp only [blockExp] at h0 hle
    refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨e, ?_, rfl⟩))
    · simp
      exact ⟨e.toNat, by omega, by omega⟩
  | ell e =>
    simp only [blockExp] at h0 hle
    refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨e, ?_, rfl⟩)
    · simp
      exact ⟨e.toNat, by omega, by omega⟩

/-- The lists of length at most $n$ with entries in a finite set are finitely many. -/
theorem finite_lists {α : Type*} (A : Finset α) (n : ℕ) :
    {l : List α | l.length ≤ n ∧ ∀ x ∈ l, x ∈ A}.Finite := by
  refine ((List.finite_length_le A n).image (List.map Subtype.val)).subset ?_
  rintro l ⟨hl, hA⟩
  refine ⟨l.pmap Subtype.mk hA, ?_, ?_⟩
  · simp only [Set.mem_ofPred_eq, List.length_pmap]; exact hl
  · simp [List.map_pmap]

variable {v : HeightOneSpectrum (𝓞 ℚ)}

/-- **Finitely many nondegenerate $\mathbb Z_2$-genera of a given determinant class, every rank.**  For $v$ the prime
of $\mathbb Q$ above $2$ (`h2`), every number of variables $n$ and every class $S \in \mathrm{SqCl}(\mathbb Q_2^\times,
\mathbb Z_2^\times)$, the set of nondegenerate local genera $G$ in $n$ variables with $\det_H(G) = S$ is finite. -/
@[kb "hanke2011structure" "§4, Def. 4.6, p. 16 (finiteness of the local sums, F_p = Q_2, every n)"]
theorem gen_det_finite_two (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (n : ℕ) (S : LocalSqCl v) :
    {G : LocGenus v n | G.Nondeg ∧ G.det = S}.Finite := by
  classical
  set h : ℕ := (SqCl.ordZ (localOrd v) (localUnits_le_ker v) S).toNat
  refine ((finite_lists (alphabet h) n).image (fun D => genusOf v n D)).subset ?_
  rintro G ⟨hN, hS⟩
  obtain ⟨D, hD, h0, hn, hev, rfl⟩ := exists_genusOf v h2 G hN
  have hodd : Odd (unitProd D) := Int.not_even_iff_odd.mp fun he => odd_unitProd D hD (even_iff_two_dvd.mp he)
  have hval : valSum D = h := by
    have := congrArg (SqCl.ordZ (localOrd v) (localUnits_le_ker v)) hS
    rw [det_genusOf v hD h0 hn hev, ordZ_zSqCl v h2 _ hodd] at this
    simp only [h, ← this, Int.toNat_natCast]
  refine ⟨D, ⟨hn ▸ length_le_dyDim D, fun b hb => mem_alphabet (hD b hb) (h0 b hb) ?_⟩, rfl⟩
  rw [← hval]; exact exp_le_valSum hb

/-- **Finitely many nondegenerate primitive $\mathbb Z_2$-genera of a given determinant class, every rank** (the index
set of $A^*_{2;n}(S)$, $B^*_{2;n}(S)$).  For $v$ the prime of $\mathbb Q$ above $2$ (`h2`), every $n$ and every
$S \in \mathrm{SqCl}(\mathbb Q_2^\times, \mathbb Z_2^\times)$, the set of nondegenerate primitive local genera $G$ in
$n$ variables with $\det_H(G) = S$ is finite. -/
@[kb "hanke2011structure" "§4, Def. 4.6, p. 16 (finiteness of Gen*_2(S; n), F_p = Q_2, every n)"]
theorem admGen_finite_two (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (n : ℕ) (S : LocalSqCl v) :
    {G : LocGenus v n | G.Nondeg ∧ G.Prim ∧ G.det = S}.Finite :=
  (gen_det_finite_two h2 n S).subset fun _ hG => ⟨hG.1, hG.2.2⟩

end

end QuadFormsKB.Hanke2011Structure.RatTwo
