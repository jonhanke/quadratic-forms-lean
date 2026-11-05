/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Dyadic7Blocks
import QuadFormsKB.Literature.Hanke2011Structure.Lemma37
import QuadFormsKB.Literature.Cassels.Ch14.ExistenceImage
import QuadFormsKB.Literature.Cassels.Ch8.Ex5
import QuadFormsKB.Literature.LocalGlobal.HasseConventionsNF
import QuadFormsKB.Literature.ConwaySloane.Mass.StdForm
import QuadFormsKB.Siegel.NeighborGenus

/-!
# Paper 7 at $p = 2$: the Hasse invariant of a block decomposition

For a list $D$ of Cassels blocks (`Cassels.DyBlock`) with even Hessian, the integral form $Q_D$ (`formZ n D`) has
Hessian $H_D$ = `hessZ n D`, the block diagonal matrix of $D$, and $Q_D(x) = \tfrac12 x^{\mathsf T} H_D x$.
This file proves that its local Hasse invariant at the prime $2$ (Serre's convention, `LocGenus.hasse`) is the
explicit sign `hasseQ D` of `Dyadic7Blocks.lean`.

**Proof.**
* *Diagonalization over $\mathbb Q$* (`dy_cong`, `formZ_isometric`): block by block, with explicit change of variables,
  $Q_D \cong \langle a_0, \dots, a_{n-1}\rangle$ over $\mathbb Q$, where the block $2^e u x^2$ gives $2^{e+1}u$
  ($x = 2s$), the block $2^e\cdot 2xy$ gives $2^e, -2^e$ ($x = s+t$, $y = s-t$) and the block
  $2^e(2x^2+2xy+2y^2)$ gives $2^e, 3\cdot2^e$ ($x = s-t$, $y = 2t$). These entries are $2^\alpha w$ with $(\alpha, w)$
  the pairs of `blockPairs`, i.e. `blockDiag` before reduction of $w$ mod $8$.
* *Base change* to $\mathbb Q_v$ (`Composition.isometricIn_map_base`), the isometry invariance of
  `Composition.hasseC` and its value on diagonal forms (`hasseC_diag`) reduce `hasse` to
  $\prod_{i<j}(a_i, a_j)_v$, which for $v \mid 2$ is the place $2$ of $\mathbb Q$ (`pv_eq_two_of_two_mem`).
* *The Hilbert symbol at $2$* of $2^\alpha w$, $2^\beta w'$ ($w, w'$ odd) is `hilb2`
  (`HilbertLocal.hilbertSymbol_two_formula`), `hilbert_pairs`; the product over pairs is computed on lists
  (`hasseVec_eq_hasseL`, `hasseL_map`).

**Defines** auxiliary data `blockPairs`, `blockVec`, `dyVec`, `blockP`, `hasseL`.
**Proves** `hasse_genusOf` (unconditional), `hasseQ_eq_one_or_neg_one`.

Indices are 0-based.
-/

open IsDedekindDomain NumberField Matrix Finset

namespace QuadFormsKB.Dyadic7

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Ternary QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.HilbertLocal

noncomputable section

/-! ### Integer pairs $(\alpha, w)$ standing for $2^\alpha w$ -/

/-- The pairs $(\alpha, w)$, $w \in \mathbb Z$, of the diagonalization of one block: `blockDiag` before reducing $w$
modulo $8$. -/
def blockPairs : DyBlock → List (ℕ × ℤ)
  | .sq e u => [(e.toNat + 1, u)]
  | .hyp e => [(e.toNat, 1), (e.toNat, -1)]
  | .ell e => [(e.toNat, 1), (e.toNat, 3)]

/-- Reduction of the unit part modulo $8$: $(\alpha, w) \mapsto (\alpha, w \bmod 8)$. -/
def z8 (p : ℕ × ℤ) : ℕ × ZMod 8 := (p.1, (p.2 : ZMod 8))

theorem blockDiag_eq (b : DyBlock) : blockDiag b = (blockPairs b).map z8 := by
  cases b <;> simp [blockDiag, blockPairs, z8]

theorem flatMap_blockDiag (D : List DyBlock) : D.flatMap blockDiag = (D.flatMap blockPairs).map z8 := by
  induction D with
  | nil => rfl
  | cons b D ih => simp [List.flatMap_cons, ih, blockDiag_eq]

/-- The rational number $2^\alpha w$ of a pair $(\alpha, w)$. -/
def pairQ (p : ℕ × ℤ) : ℚ := 2 ^ p.1 * p.2

theorem blockPairs_odd (b : DyBlock) (hb : b.Valid) : ∀ p ∈ blockPairs b, Odd p.2 := by
  cases b with
  | sq e u =>
    intro p hp
    simp only [blockPairs, List.mem_singleton] at hp
    subst hp
    rcases hb with h | h | h | h <;> subst h <;> exact Int.odd_iff.2 (by norm_num)
  | hyp e =>
    intro p hp
    simp only [blockPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact Int.odd_iff.2 (by norm_num)
  | ell e =>
    intro p hp
    simp only [blockPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact Int.odd_iff.2 (by norm_num)

theorem flatMap_odd (D : List DyBlock) (hD : ∀ b ∈ D, b.Valid) : ∀ p ∈ D.flatMap blockPairs, Odd p.2 := by
  intro p hp
  rw [List.mem_flatMap] at hp
  obtain ⟨b, hb, hp⟩ := hp
  exact blockPairs_odd b (hD b hb) p hp

/-! ### The Hasse invariant of a list over $\mathbb Q_2$ -/

/-- $\prod_{i<j}(x_i, x_j)_{\mathbb Q_2}$ for a list $x$ of elements of $\mathbb Q_2$. -/
def hasseL : List ℚ_[2] → ℤ
  | [] => 1
  | x :: l => (l.map (hilbertSymbol ℚ_[2] x)).prod * hasseL l

theorem hasseVec_eq_hasseL : ∀ {n : ℕ} (a : Fin n → ℚ_[2]), PadicClass.hasseVec a = hasseL (List.ofFn a)
  | 0, a => by simp [PadicClass.hasseVec, hasseL]
  | n + 1, a => by
    have h : a = Fin.cons (a 0) (fun i => a i.succ) := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [h, PadicClass.hasseVec_cons_prod, hasseVec_eq_hasseL, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, hasseL]
    congr 1
    rw [List.map_ofFn, List.prod_ofFn]
    rfl

/-- The 2-adic Hilbert symbol of $2^\alpha w$, $2^\beta w'$ with $w, w'$ odd integers is `hilb2` of the reduced pairs. -/
theorem hilbert_pairs (p q : ℕ × ℤ) (hp : Odd p.2) (hq : Odd q.2) :
    hilbertSymbol ℚ_[2] ((pairQ p : ℚ) : ℚ_[2]) ((pairQ q : ℚ) : ℚ_[2]) = hilb2 (z8 p) (z8 q) := by
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[2]ˣ, (u : ℤ_[2]) = (p.2 : ℤ_[2]) :=
    ⟨(dyadic_isUnit_int_cast_of_odd hp).unit, IsUnit.unit_spec _⟩
  obtain ⟨v, hv⟩ : ∃ v : ℤ_[2]ˣ, (v : ℤ_[2]) = (q.2 : ℤ_[2]) :=
    ⟨(dyadic_isUnit_int_cast_of_odd hq).unit, IsUnit.unit_spec _⟩
  have hx : ((pairQ p : ℚ) : ℚ_[2]) = (2 : ℚ_[2]) ^ p.1 * ((u : ℤ_[2]) : ℚ_[2]) := by
    rw [hu]; simp [pairQ]
  have hy : ((pairQ q : ℚ) : ℚ_[2]) = (2 : ℚ_[2]) ^ q.1 * ((v : ℤ_[2]) : ℚ_[2]) := by
    rw [hv]; simp [pairQ]
  rw [hx, hy, hilbertSymbol_two_formula]
  simp only [hu, hv, map_intCast, hilb2, z8]

theorem hasseL_map (l : List (ℕ × ℤ)) (hl : ∀ p ∈ l, Odd p.2) :
    hasseL (l.map fun p => ((pairQ p : ℚ) : ℚ_[2])) = hasseList (l.map z8) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hl' : ∀ q ∈ l, Odd q.2 := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    simp only [List.map_cons, hasseL, hasseList, ih hl']
    congr 1
    rw [List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun q hq => ?_
    simp only [Function.comp]
    exact hilbert_pairs p q (hl p (List.mem_cons_self ..)) (hl' q hq)

theorem hasseList_pm : ∀ l : List (ℕ × ZMod 8), hasseList l = 1 ∨ hasseList l = -1
  | [] => Or.inl rfl
  | a :: l => by
    have hp : ∀ m : List (ℕ × ZMod 8), ((m.map (hilb2 a)).prod = 1 ∨ (m.map (hilb2 a)).prod = -1) := by
      intro m
      induction m with
      | nil => exact Or.inl rfl
      | cons b m ih =>
        simp only [List.map_cons, List.prod_cons]
        have : hilb2 a b = 1 ∨ hilb2 a b = -1 := by
          unfold hilb2; exact neg_one_pow_eq_or ℤ _
        rcases this with h | h <;> rcases ih with h' | h' <;> rw [h, h'] <;> simp
    simp only [hasseList]
    rcases hp l with h | h <;> rcases hasseList_pm l with h' | h' <;> rw [h, h'] <;> simp

/-- **The Hasse invariant of a block decomposition is $\pm 1$.** -/
theorem hasseQ_eq_one_or_neg_one (D : List DyBlock) : hasseQ D = 1 ∨ hasseQ D = -1 :=
  hasseList_pm _

/-! ### The diagonalization over $\mathbb Q$ -/

/-- The diagonal entries (in $\mathbb Q$) of the diagonalization of one block, as in `blockPairs`. -/
def blockVec : (b : DyBlock) → Fin b.dim → ℚ
  | .sq e u => fun _ => 2 ^ (e.toNat + 1) * u
  | .hyp e => ![2 ^ e.toNat, -2 ^ e.toNat]
  | .ell e => ![2 ^ e.toNat, 3 * 2 ^ e.toNat]

/-- The diagonal entries of the diagonalization of the block decomposition `D`. -/
def dyVec : (D : List DyBlock) → Fin (dyDim D) → ℚ
  | [] => Fin.elim0
  | b :: D => Fin.append (blockVec b) (dyVec D)

theorem ofFn_blockVec (b : DyBlock) : List.ofFn (blockVec b) = (blockPairs b).map pairQ := by
  cases b <;> simp [blockVec, blockPairs, pairQ, List.ofFn_succ, DyBlock.dim] <;> ring

theorem ofFn_dyVec : ∀ D : List DyBlock, List.ofFn (dyVec D) = (D.flatMap blockPairs).map pairQ
  | [] => rfl
  | b :: D => by
    show List.ofFn (Fin.append (blockVec b) (dyVec D)) = _
    rw [List.ofFn_fin_append, ofFn_blockVec, ofFn_dyVec D]
    simp [List.flatMap_cons]

theorem dyVec_ne (D : List DyBlock) (hD : ∀ b ∈ D, b.Valid) (i : Fin (dyDim D)) : dyVec D i ≠ 0 := by
  have hm : dyVec D i ∈ List.ofFn (dyVec D) := List.mem_ofFn.2 ⟨i, rfl⟩
  rw [ofFn_dyVec, List.mem_map] at hm
  obtain ⟨p, hp, hpe⟩ := hm
  rw [← hpe]
  obtain ⟨k, hk⟩ := flatMap_odd D hD p hp
  unfold pairQ
  rw [hk]
  push_cast
  have h1 : ((2 * k + 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (show (2 * k + 1 : ℤ) ≠ 0 by omega)
  push_cast at h1
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero) h1

section OS
variable {R : Type*} [CommRing R] {a b : ℕ}

theorem orth_mul (A A' : Matrix (Fin a) (Fin a) R) (B B' : Matrix (Fin b) (Fin b) R) :
    orthSumMat A B * orthSumMat A' B' = orthSumMat (A * A') (B * B') := by
  simp only [dyadic_orthSumMat_eq]
  rw [Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv.symm _]
  simp [Matrix.fromBlocks_multiply]

theorem orth_transpose (A : Matrix (Fin a) (Fin a) R) (B : Matrix (Fin b) (Fin b) R) :
    (orthSumMat A B)ᵀ = orthSumMat Aᵀ Bᵀ := by
  simp only [dyadic_orthSumMat_eq]
  rw [Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]
  simp

end OS

/-- The change of variables $x = Ps$ diagonalizing one block (see the module docstring). -/
def blockP : (b : DyBlock) → Matrix (Fin b.dim) (Fin b.dim) ℚ
  | .sq _ _ => !![2]
  | .hyp _ => !![1, 1; 1, -1]
  | .ell _ => !![1, -1; 0, 2]

theorem blockP_det (b : DyBlock) : (blockP b).det ≠ 0 := by
  cases b with
  | sq e u =>
    show Matrix.det (!![(2 : ℚ)]) ≠ 0
    rw [Matrix.det_fin_one_of]; norm_num
  | hyp e =>
    show Matrix.det (!![(1 : ℚ), 1; 1, -1]) ≠ 0
    rw [Matrix.det_fin_two_of]; norm_num
  | ell e =>
    show Matrix.det (!![(1 : ℚ), -1; 0, 2]) ≠ 0
    rw [Matrix.det_fin_two_of]; norm_num

theorem block_cong (b : DyBlock) :
    (blockP b)ᵀ * (blockMatInt b).map (Int.castRingHom ℚ) * blockP b =
      Matrix.diagonal (fun i => 2 * blockVec b i) := by
  cases b with
  | sq e u =>
    show (!![(2 : ℚ)])ᵀ * (!![(2 : ℤ) ^ e.toNat * u] : Matrix (Fin 1) (Fin 1) ℤ).map (Int.castRingHom ℚ) *
      !![(2 : ℚ)] = Matrix.diagonal (fun _ : Fin 1 => 2 * (2 ^ (e.toNat + 1) * (u : ℚ)))
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply]
    ring
  | hyp e =>
    show (!![(1 : ℚ), 1; 1, -1])ᵀ *
      (!![0, 2 ^ e.toNat; 2 ^ e.toNat, 0] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) *
      !![(1 : ℚ), 1; 1, -1] = Matrix.diagonal (fun i : Fin 2 => 2 * (![2 ^ e.toNat, -2 ^ e.toNat] : Fin 2 → ℚ) i)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] <;> ring
  | ell e =>
    show (!![(1 : ℚ), -1; 0, 2])ᵀ *
      (!![2 ^ (e.toNat + 1), 2 ^ e.toNat; 2 ^ e.toNat, 2 ^ (e.toNat + 1)] : Matrix (Fin 2) (Fin 2) ℤ).map
        (Int.castRingHom ℚ) * !![(1 : ℚ), -1; 0, 2] =
      Matrix.diagonal (fun i : Fin 2 => 2 * (![2 ^ e.toNat, 3 * 2 ^ e.toNat] : Fin 2 → ℚ) i)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ] <;> ring

/-- **Congruence diagonalization of the Hessian of a block decomposition over $\mathbb Q$:**
$P^{\mathsf T} H_D P = \mathrm{diag}(2 a_i)$ with $a$ = `dyVec D` and $P$ invertible. -/
theorem dy_cong : ∀ D : List DyBlock, ∃ P : Matrix (Fin (dyDim D)) (Fin (dyDim D)) ℚ, P.det ≠ 0 ∧
    Pᵀ * (dyMatInt D).map (Int.castRingHom ℚ) * P = Matrix.diagonal (fun i => 2 * dyVec D i)
  | [] => ⟨1, by simp, by ext i; exact i.elim0⟩
  | b :: D => by
    obtain ⟨P, hP, hPe⟩ := dy_cong D
    refine ⟨orthSumMat (blockP b) P, ?_, ?_⟩
    · intro h0
      exact mul_ne_zero (blockP_det b) hP ((Ex5.det_orthSum (blockP b) P).symm.trans h0)
    · show (orthSumMat (blockP b) P)ᵀ * (orthSumMat (blockMatInt b) (dyMatInt D)).map (Int.castRingHom ℚ) *
        orthSumMat (blockP b) P = Matrix.diagonal (fun i => 2 * Fin.append (blockVec b) (dyVec D) i)
      rw [Ex5.map_orthSum, orth_transpose, orth_mul, orth_mul, block_cong, hPe, Ex5.orthSum_diagonal]
      congr 1
      funext i
      refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;> simp

theorem hessZ_self (D : List DyBlock) : hessZ (dyDim D) D = dyMatInt D := by
  rw [hessZ_of rfl]; ext i j; rfl

/-- **$Q_D \cong \langle a_0, \dots, a_{n-1}\rangle$ over $\mathbb Q$** with $a$ = `dyVec D`. -/
theorem formZ_isometric (D : List DyBlock) (h0 : ∀ b ∈ D, 0 ≤ blockExp b)
    (hev : ∀ b ∈ D, ¬ IsOddUnimodBlock b) :
    ((formZ (dyDim D) D).map (Int.castRingHom ℚ)).IsometricIn ℚ (QuadForm.diag (dyVec D)) := by
  obtain ⟨P, hP, hPe⟩ := dy_cong D
  refine ⟨P, isUnit_iff_ne_zero.2 hP, fun x => ?_⟩
  have h2 := Siegel.Kneser.two_mul_evalIn ((formZ (dyDim D) D).map (Int.castRingHom ℚ)) (P *ᵥ x)
  have e : ∀ N : Matrix (Fin (dyDim D)) (Fin (dyDim D)) ℚ, N.map (algebraMap ℚ ℚ) = N := fun N => by
    ext; simp
  rw [QuadForm.hessian_map, hessian_formZ rfl h0 hev, hessZ_self, e] at h2
  rw [QuadForm.evalIn_diag]
  have key : (P *ᵥ x) ⬝ᵥ (((dyMatInt D).map (Int.castRingHom ℚ)) *ᵥ (P *ᵥ x)) =
      x ⬝ᵥ ((Pᵀ * (dyMatInt D).map (Int.castRingHom ℚ) * P) *ᵥ x) := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec x Pᵀ, Matrix.vecMul_transpose]
  rw [hPe] at key
  have hd : x ⬝ᵥ (Matrix.diagonal (fun i => 2 * dyVec D i) *ᵥ x) = 2 * ∑ i, dyVec D i * x i ^ 2 := by
    simp only [dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine mul_left_cancel₀ (two_ne_zero : (2 : ℚ) ≠ 0) ?_
  rw [h2, key, hd]
  simp

/-- **The Hasse invariant of the local genus of $Q_D$ at the prime $2$** (Hanke 2011, Lemma 4.6 and Remark 4.3): for a
prime $v$ of $\mathbb Q$ with $2 \in v$ (so $v$ is the prime $2$), a list $D$ of Cassels blocks, valid
(`hD`: every `sq e u` has $u \in \{1,3,5,7\}$), with exponents $e \ge 0$ (`h0`), $n = \dim D$ (`hn`) variables and even
Hessian, i.e. no block $2^0 u x^2$ (`hev`), the Hasse invariant $c_v(G)$ of the local genus $G$ = `genusOf v n D` of the
integral form $Q_D = \tfrac12 x^{\mathsf T} H_D x$ is $\prod_{i<j} (a_i, a_j)_2$ for the diagonal entries $a_i$ of
`blockDiag`, i.e. `hasseQ D`:
$$c_v(\texttt{genusOf}\ v\ n\ D) = \prod_{i<j} (a_i, a_j)_2 = \texttt{hasseQ}\ D.$$
Unconditional (no assumed inputs). -/
@[kb "hanke2011ternary" "§4, Lemma 4.6 and Remark 4.3, pp. 10–11 (Hasse invariant of a block decomposition)"]
theorem hasse_genusOf (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {n : ℕ} {D : List DyBlock}
    (hD : ∀ b ∈ D, b.Valid) (h0 : ∀ b ∈ D, 0 ≤ blockExp b) (hn : dyDim D = n)
    (hev : ∀ b ∈ D, ¬ IsOddUnimodBlock b) :
    (genusOf v n D).hasse = hasseQ D := by
  subst hn
  classical
  have hnz : ∀ i, algebraMap ℚ (v.adicCompletion ℚ) (dyVec D i) ≠ 0 :=
    fun i => (map_ne_zero _).2 (dyVec_ne D hD i)
  have hiso : ((formZ (dyDim D) D).map (Int.castRingHom ℚ)).map (algebraMap ℚ (v.adicCompletion ℚ)) |>.IsometricIn
      (v.adicCompletion ℚ) (QuadForm.diag fun i => algebraMap ℚ (v.adicCompletion ℚ) (dyVec D i)) := by
    rw [← OMeara.map_diag']
    exact Composition.isometricIn_map_base _ (formZ_isometric D h0 hev)
  unfold genusOf
  rw [LocGenus.hasse_mk, hasseForm]
  have e1 : ((formZ (dyDim D) D).map (algebraMap ℤ (v.adicCompletionIntegers ℚ))).map
      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) =
      ((formZ (dyDim D) D).map (Int.castRingHom ℚ)).map (algebraMap ℚ (v.adicCompletion ℚ)) := by
    rw [Lattices.QuadForm.map_map, Lattices.QuadForm.map_map]
    congr 1
    exact Subsingleton.elim _ _
  rw [e1, hasseC_eq_of_isometricIn hiso, hasseC_diag v _ hnz]
  have e2 : PadicClass.hasseVec (fun i => algebraMap ℚ (v.adicCompletion ℚ) (dyVec D i)) =
      (NFPlace.finite v).hasseSerre (dyVec D) := by
    unfold NFPlace.hasseSerre PadicClass.hasseVec
    simp only [NFPlace.hilbert, eq_ratCast]
    try rfl
  rw [e2, NFPlace.hasseSerre_rat]
  have hp : (NFPlace.finite v).toRatPlace = RatPlace.finite ⟨2, Nat.prime_two⟩ := by
    simp only [NFPlace.toRatPlace]
    congr 1
    exact Subtype.ext (pv_eq_two_of_two_mem v h2)
  rw [hp, show (RatPlace.finite ⟨2, Nat.prime_two⟩).hasseSerre (dyVec D) = hasseInvariant ℚ_[2] (dyVec D) from
    RatPlace.hasseSerre_finite ⟨2, Nat.prime_two⟩ _]
  have e3 : hasseInvariant ℚ_[2] (dyVec D) = PadicClass.hasseVec (fun i => ((dyVec D i : ℚ) : ℚ_[2])) := rfl
  have e4 : List.ofFn (fun i => ((dyVec D i : ℚ) : ℚ_[2])) =
      (List.ofFn (dyVec D)).map (fun q : ℚ => (q : ℚ_[2])) := List.map_ofFn.symm
  rw [e3, hasseVec_eq_hasseL, e4, ofFn_dyVec, List.map_map]
  refine (hasseL_map _ (flatMap_odd D hD)).trans ?_
  rw [hasseQ, flatMap_blockDiag]

end

end QuadFormsKB.Dyadic7

#print axioms QuadFormsKB.Dyadic7.hasse_genusOf
#print axioms QuadFormsKB.Dyadic7.hasseQ_eq_one_or_neg_one
