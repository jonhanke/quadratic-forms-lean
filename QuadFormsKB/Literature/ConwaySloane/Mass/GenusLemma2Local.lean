/-
# Conway–Sloane, LDL IV, §11, Lemma 2 at $p = 2$: the local step, proved

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §11, Lemma 2, p. 280 (stated there without proof, after Kneser–Puppe); the 2-adic symbols
and Theorem 10 are from Conway–Sloane, *Sphere Packings, Lattices and Groups*, Ch. 15, §7 (`conwaysloane1999`).

**Theorem** (`lemma2IfDyadicRational`, proving the former named statement `Lemma2IfDyadicRationalStatement`). Let
$A, B \in M_n(\mathbb Z)$ be symmetric with $\det A, \det B \ne 0$, of the same type $T$ (`gramType`: $2$ if all
$A_{ii}$ are even, else $1$), with an isomorphism of discriminant groups $\mathbb Z^n/A\mathbb Z^n \cong
\mathbb Z^n/B\mathbb Z^n$ preserving the norms $y^{\mathsf T}A^{-1}y$ modulo $T$ (`DiscIso`), and congruent over
$\mathbb Q_2$. Then $x^{\mathsf T}Ax$ and $x^{\mathsf T}Bx$ are $\mathrm{GL}_n(\mathbb Z_2)$-equivalent.

Consequently `Lemma2Statement` and `Lemma4Statement` (LDL IV §11, Lemmas 2 and 4) hold unconditionally
(`lemma2Statement_holds`, `lemma4Statement_holds`, `lemma2IfDyadicStatement_holds`).

**Proof (Gauss sums of the discriminant form).** Take Jordan decompositions $A \sim D$, $B \sim D'$ over $\mathbb Z_2$
(`exists_isTwoSymbolOf`), with 2-adic symbols $\sigma$, $\tau$. The isomorphism of discriminant forms becomes matrix
data over $\mathbb Z_2$ (`admissible_of_discIso`), which induces a bijection of the discriminant groups preserving the
norms modulo $T$ (`GenusLemma2GaussCore.lean`). Hence:
1. the numbers of $2^k$-torsion elements agree, so the dimensions $n_{2^k}$ agree (`dim_eq_of_sum_min`);
2. for $m \ge 1$, and for $m = 0$ when $T = 2$, the Gauss sums
   $G_m = \sum_{r}\mathrm{ch}(2^m r^{\mathsf T}D^{-1}r)$ agree; $G_m = \prod_{\text{blocks}} g_b$ (`gaussSum_bmat`),
   $G_m = 0$ iff the constituent of scale $2^m$ is odd (`GenusLemma2GaussBlocks.lean`), so the types agree (at scale
   $1$ the type is the type of $A$, `isTypeI_zero_iff`); otherwise $G_m$ is a positive multiple of $\zeta_8^{\Omega_m}$,
   $\Omega_m = \sum_{q > 2^m}(t_q + 4\log_2(q/2^m)[\varepsilon_q = -1])$, so $\Omega_m(\sigma) = \Omega_m(\tau)$;
3. the $\mathbb Q_2$-class gives the same total oddity and total sign (`ratIso_iff`);
4. these give Theorem 10's conditions (i), (ii) (`prefix_eq_of_phase`, `theorem10Cond_iff_prefix`), so
   $A \sim B$ over $\mathbb Z_2$ (`zpEquiv_iff_theorem10Cond`).

Indices are 0-based. No erratum: a computer check of all 2-adic forms of rank $\le 3$ with scales $\le 8$ found no
counterexample (a computer calculation outside Lean), as the theorem predicts.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma2GaussSymbol
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma2GaussBlocks
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma2GaussTransport
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma2Dyadic
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma3

set_option linter.unusedSectionVars false

open Matrix QuadFormsKB QuadFormsKB.Cassels Finset QuadFormsKB.ConwaySloane.TwoAdic

namespace QuadFormsKB.ConwaySloane.Mass.Gauss2

/-! ### Powers of $\zeta_8$ -/

theorem zeta8_pow_mod (k : ℕ) : zeta8 ^ (k % 8) = zeta8 ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k 8, pow_add, pow_mul, zeta8_pow_eight, one_pow, mul_one]

theorem zeta8_pow_val_add (a b : ZMod 8) : zeta8 ^ a.val * zeta8 ^ b.val = zeta8 ^ (a + b).val := by
  rw [← pow_add, ZMod.val_add, zeta8_pow_mod]

/-- A positive multiple of a power of $\zeta_8$ determines the exponent. -/
theorem phase_eq {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') {a b : ZMod 8}
    (h : (r : ℂ) * zeta8 ^ a.val = (r' : ℂ) * zeta8 ^ b.val) : a = b := by
  have hn := congrArg norm h
  simp only [norm_mul, norm_pow, norm_zeta8, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr, abs_of_pos hr'] at hn
  subst hn
  have h2 : zeta8 ^ a.val = zeta8 ^ b.val := mul_left_cancel₀ (by exact_mod_cast hr.ne') h
  exact ZMod.val_injective _ (zeta8_pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h2)

/-! ### The Gauss sum of a block decomposition: zero or a positive multiple of $\zeta_8^{\Omega}$ -/

variable (D : List DyBlock)

theorem gauss_zero_iff (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) {m : ℕ} (hm : 1 ≤ m) :
    ∏ j, blockGauss (D.get j) m = 0 ↔ ∃ j, bexp D j = m ∧ IsSqBlock (D.get j) := by
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, -, hj⟩
    by_contra hno
    have hb : ¬ (IsSqBlock (D.get j) ∧ bex (D.get j) = m ∧ 1 ≤ m) := fun ⟨hsq, he, _⟩ => hno ⟨j, he, hsq⟩
    obtain ⟨r, hr, hg⟩ := blockGauss_eq _ (hD _ (List.get_mem _ _)) (hD0 _ (List.get_mem _ _)) m hb
    rw [hg] at hj
    exact mul_ne_zero (by exact_mod_cast hr.ne') (pow_ne_zero _ zeta8_ne_zero) hj
  · rintro ⟨j, hj, hsq⟩
    refine ⟨j, mem_univ _, ?_⟩
    have hv := hD _ (List.get_mem D j)
    have he := hD0 _ (List.get_mem D j)
    have hj' : bex (D.get j) = m := hj
    obtain ⟨e, u, hju⟩ : ∃ e u, D.get j = DyBlock.sq e u := by
      cases hb : D.get j with
      | sq e u => exact ⟨e, u, rfl⟩
      | hyp e => rw [hb] at hsq; exact absurd hsq (by simp [IsSqBlock])
      | ell e => rw [hb] at hsq; exact absurd hsq (by simp [IsSqBlock])
    rw [hju] at hv he hj' ⊢
    exact blockGauss_sq_eq_zero e u hv he hm hj'

theorem gauss_phase (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) (m : ℕ)
    (hno : ∀ j, ¬ (IsSqBlock (D.get j) ∧ bex (D.get j) = m ∧ 1 ≤ m)) :
    ∃ r : ℝ, 0 < r ∧ ∏ j, blockGauss (D.get j) m = (r : ℂ) * zeta8 ^ (∑ j, blockPhase (D.get j) m).val := by
  classical
  suffices H : ∀ s : Finset (Fin D.length), ∃ r : ℝ, 0 < r ∧
      ∏ j ∈ s, blockGauss (D.get j) m = (r : ℂ) * zeta8 ^ (∑ j ∈ s, blockPhase (D.get j) m).val from H univ
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨r, hr, hs⟩ := ih
    obtain ⟨r', hr', ha'⟩ := blockGauss_eq _ (hD _ (List.get_mem _ _)) (hD0 _ (List.get_mem _ _)) m (hno a)
    refine ⟨r' * r, mul_pos hr' hr, ?_⟩
    rw [prod_insert ha, sum_insert ha, hs, ha', ← zeta8_pow_val_add]
    push_cast; ring

/-! ### The local theorem -/

theorem gramType_eq_two_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : gramType A = 2 ↔ EvenGram A := by
  classical
  unfold gramType; split_ifs with h <;> simp [h]

theorem noSq_zero_of_even {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hsA : Aᵀ = A) {D : List DyBlock}
    (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) (h : dyDim D = n)
    (hAD : ZpEquiv (A.map (Int.castRingHom ℚ_[2])) (castMat D h)) (hE : EvenGram A) :
    ∀ j, ¬ (IsSqBlock (D.get j) ∧ bexp D j = 0) := by
  intro j ⟨hsq, hj⟩
  exact (isTypeI_zero_iff hsA hD hD0 h hAD).1 ((isTypeI_blockSymbol D hD0 0).2 ⟨j, hj, hsq⟩) hE

/-- **Lemma 2 ("if") at $p = 2$, the local step** (LDL IV §11, Lemma 2, p. 280; proved here, see the module
docstring): symmetric nondegenerate integer $A$, $B$ of the same type with an isomorphism of discriminant forms
preserving norms modulo the type, congruent over $\mathbb Q_2$, are $\mathrm{GL}_n(\mathbb Z_2)$-equivalent. -/
@[kb "conwaysloane1988" "§11, Lemma 2, p. 280 (if, at p = 2, given the Q_2-class; proved)"]
theorem lemma2IfDyadicRational : Lemma2IfDyadicRationalStatement where
  imp n A B hsA hsB hdA hdB ht hi hQ := by
    rw [isometricGL_padic_iff hsA hsB]
    set T := gramType A with hTdef
    set FA := A.map (Int.castRingHom ℚ_[2]) with hFA
    set FB := B.map (Int.castRingHom ℚ_[2]) with hFB
    have hFAs : FAᵀ = FA := by rw [hFA, ← Matrix.transpose_map, hsA]
    have hFBs : FBᵀ = FB := by rw [hFB, ← Matrix.transpose_map, hsB]
    obtain ⟨σ, hσ⟩ := exists_isTwoSymbolOf FA hFAs (det_map_ne hdA) (isClassIntegral_map A)
    obtain ⟨τ, hτ⟩ := exists_isTwoSymbolOf FB hFBs (det_map_ne hdB) (isClassIntegral_map B)
    have hσ' := hσ
    have hτ' := hτ
    obtain ⟨D, hD, hD0, h, hFD, rfl⟩ := hσ'
    obtain ⟨D', hD', hD'0, h', hFD', rfl⟩ := hτ'
    obtain ⟨N₁, hN₁⟩ := blockSymbol_supported D hD0
    obtain ⟨N₂, hN₂⟩ := blockSymbol_supported D' hD'0
    set N := max N₁ N₂
    have hNσ : (blockSymbol D).SupportedBelow N := fun k hk => hN₁ k (le_trans (le_max_left _ _) hk)
    have hNτ : (blockSymbol D').SupportedBelow N := fun k hk => hN₂ k (le_trans (le_max_right _ _) hk)
    have hbN := bexp_lt_of_supported hD0 hNσ
    have hbN' := bexp_lt_of_supported hD'0 hNτ
    have adm := admissible_of_discIso hsA hsB hdA hdB hi h h' hFD hFD'
    have S := shape_bmat D hD hD0
    have S' := shape_bmat D' hD' hD'0
    have hEven : EvenGram A ↔ EvenGram B := evenGram_iff_of_gramType_eq ht
    -- dimensions
    have hdim : ∀ k, (blockSymbol D' k).dim = (blockSymbol D k).dim :=
      dim_eq_of_sum_min hD0 hD'0 (h.trans h'.symm) (sum_min_eq S S' adm)
    -- Gauss sums
    have hG : ∀ m, (1 ≤ m ∨ EvenGram A) → ∏ j, blockGauss (D.get j) m = ∏ j, blockGauss (D'.get j) m := by
      intro m hm
      rw [← gaussSum_bmat D hD hD0, ← gaussSum_bmat D' hD' hD'0]
      refine gauss_eq_of_admissible S S' adm (norm_two_pow_le m) ?_ ?_
      · rcases hm with hm | hE
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
          rw [show (2 : ℚ_[2]) ^ (1 + k) * (T : ℚ_[2]) / 2 = (2 : ℚ_[2]) ^ k * ((T : ℤ) : ℚ_[2]) by
            rw [pow_add]; push_cast; field_simp]
          exact norm_mul_le_one' (norm_two_pow_le k) (Padic.norm_int_le_one _)
        · have hT2 : T = 2 := (gramType_eq_two_iff A).2 hE
          rw [hT2, show (2 : ℚ_[2]) ^ m * ((2 : ℕ) : ℚ_[2]) / 2 = (2 : ℚ_[2]) ^ m by push_cast; field_simp]
          exact norm_two_pow_le m
      · refine qv_bmat_half D' hD'0 m ?_
        rcases hm with hm | hE
        · exact Or.inl hm
        · exact Or.inr (noSq_zero_of_even hsB hD' hD'0 h' hFD' (hEven.1 hE))
    -- types
    have htype : ∀ k, IsTypeI (blockSymbol D) k ↔ IsTypeI (blockSymbol D') k := by
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [isTypeI_zero_iff hsA hD hD0 h hFD, isTypeI_zero_iff hsB hD' hD'0 h' hFD', hEven]
      · rw [isTypeI_blockSymbol D hD0, isTypeI_blockSymbol D' hD'0, ← gauss_zero_iff D hD hD0 hk,
          ← gauss_zero_iff D' hD' hD'0 hk, hG k (Or.inl hk)]
    have hshape : ∀ k, (blockSymbol D' k).dim = (blockSymbol D k).dim ∧
        (blockSymbol D' k).type = (blockSymbol D k).type := fun k =>
      ⟨hdim k, type_eq_of_isTypeI_iff (htype k)⟩
    -- the `ℚ_2`-class
    have hC : CongrIn ℚ_[2] (castMat D h) (castMat D' h') :=
      (congrIn_of_zpEquiv hFD).symm.trans (hQ.trans (congrIn_of_zpEquiv hFD'))
    obtain ⟨g, hg⟩ := hC
    obtain ⟨hU, hO⟩ := (ratIso_iff h h' hD hD0 hD' hD'0 hshape hbN hbN').1
      ⟨g.val, (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit, hg⟩
    have hT10 := setting_of_shape hD hD' hshape hNσ hNτ
    have hex := blockSymbol_exists D hD
    have hex' := blockSymbol_exists D' hD'
    have hS4 : 4 * signCnt (blockSymbol D) (blockSymbol D') N = 0 := by
      have hsq := unitPre_sq (blockSymbol D') N
      have h1 : unitPre (blockSymbol D) N * unitPre (blockSymbol D') N = 1 := by rw [hU, hsq]
      have hXN : oddDiff (blockSymbol D) (blockSymbol D') N = 0 := by unfold oddDiff; rw [hO, sub_self]
      rwa [unitPre_mul_eq hT10 hex hex' N, hXN, unitOf_zero_eq_one_iff] at h1
    refine (zpEquiv_iff_theorem10Cond hσ hτ hNσ hNτ).2 ((theorem10Cond_iff_prefix hT10).2 ⟨?_, ?_⟩)
    · rw [four_mul_signDiffBelow]; unfold signCnt at hS4; rw [← mul_add]; exact hS4
    · intro m hII
      have hII' : ¬ IsTypeI (blockSymbol D') m := (htype m).not.1 hII
      have hm : 1 ≤ m ∨ EvenGram A := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · right
          by_contra hE
          exact hII ((isTypeI_zero_iff hsA hD hD0 h hFD).2 hE)
        · exact Or.inl hm
      have hno : ∀ (E : List DyBlock), (∀ b ∈ E, 0 ≤ blockExp b) → ¬ IsTypeI (blockSymbol E) m →
          ∀ j, ¬ (IsSqBlock (E.get j) ∧ bex (E.get j) = m ∧ 1 ≤ m) :=
        fun E hE0 hI j ⟨hsq, he, _⟩ => hI ((isTypeI_blockSymbol E hE0 m).2 ⟨j, he, hsq⟩)
      obtain ⟨r, hr, hgD⟩ := gauss_phase D hD hD0 m (hno D hD0 hII)
      obtain ⟨r', hr', hgD'⟩ := gauss_phase D' hD' hD'0 m (hno D' hD'0 hII')
      have hP := phase_eq hr hr' (hgD.symm.trans ((hG m hm).trans hgD'))
      have key := prefix_eq_of_phase hD hD0 hD' hD'0 hbN hbN' m hII hII' hO hS4 hP
      have e := prefix_sub_eq (blockSymbol D) (blockSymbol D') m
      rw [key] at e
      exact (sub_eq_zero.1 e).symm

/-- **LDL IV §11, Lemma 2 at $p = 2$** (`Lemma2IfDyadicStatement`), now unconditional. -/
theorem lemma2IfDyadicStatement_holds : Lemma2IfDyadicStatement :=
  lemma2IfDyadic_of_rational lemma2IfDyadicRational

/-- **LDL IV §11, Lemma 2**, unconditional. -/
@[kb "conwaysloane1988" "§11, Lemma 2, p. 280 (proved)"]
theorem lemma2Statement_holds : Lemma2Statement :=
  lemma2Statement_of_dyadicRational lemma2IfDyadicRational

/-- **LDL IV §11, Lemma 4**, unconditional. -/
@[kb "conwaysloane1988" "§11, Lemma 4, p. 280 (proved)"]
theorem lemma4Statement_holds : Lemma4Statement :=
  lemma4_of_dyadicRational lemma2IfDyadicRational

end QuadFormsKB.ConwaySloane.Mass.Gauss2
