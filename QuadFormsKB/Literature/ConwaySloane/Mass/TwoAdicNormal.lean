/-
# A normal form for one 2-adic constituent

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Ch. 15, §7.5, Thm. 10, p. 381
(bibliography key `conwaysloane1999`), used for the mass formula of Conway–Sloane 1988 at $p = 2$.

The symbol of a block decomposition depends only on the multiset of its blocks, constituent by constituent
(`blockF`). Three blocks $2^e u_0x^2$, $2^e u_1x^2$, $2^e u_2x^2$ have the same contribution to the symbol as
$2^e dx^2 \perp 2^e b$ with $d \equiv u_0 + u_1 + u_2 \pmod 8$ and $b$ the block $2xy$ or $2x^2 + 2xy + 2y^2$ of the
right sign (`three_to_one`), so every list of blocks of exponent $e$ has the same contribution as one with at most two
blocks $2^e ux^2$ (`exists_normal`). By Theorem 10 (`zpEquiv_castMat_iff`), two block decompositions with the same
symbol are $\mathbb Z_2$-equivalent, so they have the same 2-adic density (`alphaP_eq_of_blockSymbol_eq`,
`pMassDensity_eq_of_blockSymbol_eq`). Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicRhoOdd
import QuadFormsKB.Literature.ConwaySloane.TwoAdicClassification

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix QuadFormsKB.Cassels QuadFormsKB.ConwaySloane

/-! ### The contribution of a list of blocks to one constituent -/

/-- The constituent formed by all the blocks of a list (dimension, sign, type, oddity), as in `blockSymbol`. -/
def blockF (B : List DyBlock) : TwoFactor :=
  { dim := (B.map DyBlock.dim).sum
    sign := Sign.prodList (B.map blockSign)
    type := if B.any fun b => decide (IsSqBlock b) then .I else .II
    oddity := (B.map blockOddity).sum }

theorem blockSymbol_eq_blockF (D : List DyBlock) (k : ℕ) :
    blockSymbol D k = blockF (D.filter fun b => blockExp b = k) := rfl

theorem sign_mul_assoc (a b c : Sign) : (a.mul b).mul c = a.mul (b.mul c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem sign_mul_comm (a b : Sign) : a.mul b = b.mul a := by cases a <;> cases b <;> rfl

theorem sign_mul_plus (a : Sign) : a.mul .plus = a := by cases a <;> rfl

theorem prodList_append (l₁ l₂ : List Sign) :
    Sign.prodList (l₁ ++ l₂) = (Sign.prodList l₁).mul (Sign.prodList l₂) := by
  induction l₁ with
  | nil => rfl
  | cons s l ih => simp only [List.cons_append, Sign.prodList, ih, sign_mul_assoc]

theorem prodList_perm {l₁ l₂ : List Sign} (h : l₁.Perm l₂) : Sign.prodList l₁ = Sign.prodList l₂ := by
  induction h with
  | nil => rfl
  | cons s _ ih => simp only [Sign.prodList, ih]
  | swap a b l =>
    simp only [Sign.prodList]
    rw [← sign_mul_assoc, ← sign_mul_assoc, sign_mul_comm b a]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem blockF_perm {B B' : List DyBlock} (h : B.Perm B') : blockF B = blockF B' := by
  unfold blockF
  rw [(h.map _).sum_eq, prodList_perm (h.map _), (h.map _).sum_eq, h.any_eq]

/-- The constituent of an orthogonal sum. -/
def TwoFactor.comb (f g : TwoFactor) : TwoFactor :=
  { dim := f.dim + g.dim
    sign := f.sign.mul g.sign
    type := if f.type = .I ∨ g.type = .I then .I else .II
    oddity := f.oddity + g.oddity }

theorem blockF_append (B B' : List DyBlock) : blockF (B ++ B') = TwoFactor.comb (blockF B) (blockF B') := by
  unfold blockF TwoFactor.comb
  simp only [List.map_append, List.sum_append, prodList_append, List.any_append]
  congr 1
  by_cases h1 : B.any (fun b => decide (IsSqBlock b)) = true <;>
    by_cases h2 : B'.any (fun b => decide (IsSqBlock b)) = true <;> simp_all

theorem blockF_congr_append {P P' : List DyBlock} (h : blockF P = blockF P') (R : List DyBlock) :
    blockF (P ++ R) = blockF (P' ++ R) := by
  rw [blockF_append, blockF_append, h]

/-- Replacing a sublist of blocks of one exponent $e$ by another with the same contribution does not change the
symbol. -/
theorem blockSymbol_congr_prefix {e : ℤ} {P P' : List DyBlock} (hP : ∀ b ∈ P, blockExp b = e)
    (hP' : ∀ b ∈ P', blockExp b = e) (h : blockF P = blockF P') (R : List DyBlock) :
    blockSymbol (P ++ R) = blockSymbol (P' ++ R) := by
  funext k
  rw [blockSymbol_eq_blockF, blockSymbol_eq_blockF, List.filter_append, List.filter_append]
  by_cases hk : e = k
  · have h1 : P.filter (fun b => decide (blockExp b = k)) = P :=
      List.filter_eq_self.mpr (fun b hb => by simp [hP b hb, hk])
    have h2 : P'.filter (fun b => decide (blockExp b = k)) = P' :=
      List.filter_eq_self.mpr (fun b hb => by simp [hP' b hb, hk])
    rw [h1, h2]
    exact blockF_congr_append h _
  · have h1 : P.filter (fun b => decide (blockExp b = k)) = [] :=
      List.filter_eq_nil_iff.mpr (fun b hb => by simp [hP b hb, hk])
    have h2 : P'.filter (fun b => decide (blockExp b = k)) = [] :=
      List.filter_eq_nil_iff.mpr (fun b hb => by simp [hP' b hb, hk])
    rw [h1, h2]

theorem blockSymbol_perm {D D' : List DyBlock} (h : D.Perm D') : blockSymbol D = blockSymbol D' := by
  funext k
  rw [blockSymbol_eq_blockF, blockSymbol_eq_blockF]
  exact blockF_perm (h.filter _)

/-! ### Three odd blocks -/

theorem jacobiTwo_cases {u : ℤ} (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) :
    (jacobiTwo u = .plus ∧ (u = 1 ∨ u = 7)) ∨ (jacobiTwo u = .minus ∧ (u = 3 ∨ u = 5)) := by
  rcases hu with rfl | rfl | rfl | rfl <;> simp [jacobiTwo]

/-- **Three blocks $2^e u x^2$ against one such block and a binary block.** -/
theorem three_to_one (e : ℤ) {u₀ u₁ u₂ : ℤ} (h₀ : u₀ = 1 ∨ u₀ = 3 ∨ u₀ = 5 ∨ u₀ = 7)
    (h₁ : u₁ = 1 ∨ u₁ = 3 ∨ u₁ = 5 ∨ u₁ = 7) (h₂ : u₂ = 1 ∨ u₂ = 3 ∨ u₂ = 5 ∨ u₂ = 7) :
    ∃ d b, (d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 7) ∧ (b = DyBlock.hyp e ∨ b = DyBlock.ell e) ∧
      blockF [.sq e u₀, .sq e u₁, .sq e u₂] = blockF [.sq e d, b] := by
  set d := (u₀ + u₁ + u₂) % 8 with hd
  have hdv : d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 7 := by omega
  have hdc : ((d : ℤ) : ZMod 8) = (u₀ : ZMod 8) + u₁ + u₂ := by
    rw [hd, show ((((u₀ + u₁ + u₂) % 8 : ℤ)) : ZMod 8) = ((u₀ + u₁ + u₂ : ℤ) : ZMod 8) by
      exact_mod_cast ZMod.intCast_mod (u₀ + u₁ + u₂) 8]
    push_cast; ring
  set s := (jacobiTwo u₀).mul ((jacobiTwo u₁).mul ((jacobiTwo u₂).mul .plus))
  by_cases hs : s = (jacobiTwo d).mul (Sign.plus.mul .plus)
  · refine ⟨d, .hyp e, hdv, Or.inl rfl, ?_⟩
    unfold blockF
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Sign.prodList, blockSign, blockOddity,
      DyBlock.dim, List.any_cons, List.any_nil, IsSqBlock]
    refine TwoFactor.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, ?_, by simp, ?_⟩
    · exact hs
    · rw [hdc]; ring
  · refine ⟨d, .ell e, hdv, Or.inr rfl, ?_⟩
    unfold blockF
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Sign.prodList, blockSign, blockOddity,
      DyBlock.dim, List.any_cons, List.any_nil, IsSqBlock]
    refine TwoFactor.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, ?_, by simp, ?_⟩
    · show s = (jacobiTwo d).mul (Sign.minus.mul .plus)
      revert hs
      cases s <;> cases jacobiTwo d <;> decide
    · rw [hdc]; ring

/-! ### The normal form -/

/-- The blocks $2^e ux^2$ with the units of a list. -/
def sqList (e : ℤ) (us : List ℤ) : List DyBlock := us.map (DyBlock.sq e)

/-- A list of binary blocks $2^e\cdot 2xy$, $2^e(2x^2 + 2xy + 2y^2)$. -/
def IsEvenList (e : ℤ) (E : List DyBlock) : Prop := ∀ c ∈ E, blockExp c = e ∧ ¬ IsSqBlock c

theorem exists_normal_aux (e : ℤ) : ∀ (n : ℕ) (us : List ℤ) (E : List DyBlock), us.length = n →
    (∀ u ∈ us, u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) → IsEvenList e E →
    ∃ (us' : List ℤ) (E' : List DyBlock), (∀ u ∈ us', u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) ∧ IsEvenList e E' ∧
      us'.length ≤ 2 ∧ us'.length % 2 = us.length % 2 ∧ (us ≠ [] → us' ≠ []) ∧
      blockF (sqList e us ++ E) = blockF (sqList e us' ++ E') := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro us E hn hus hE
    match us, hn with
    | [], _ => exact ⟨[], E, by simp, hE, by simp, rfl, by simp, rfl⟩
    | [a], _ => exact ⟨[a], E, hus, hE, by simp, rfl, by simp, rfl⟩
    | [a, b], _ => exact ⟨[a, b], E, hus, hE, by simp, rfl, by simp, rfl⟩
    | a :: b :: c :: rest, hn =>
      obtain ⟨d, bb, hd, hbb, hF⟩ := three_to_one e (hus a (by simp)) (hus b (by simp)) (hus c (by simp))
      have hE' : IsEvenList e (bb :: E) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rcases hbb with rfl | rfl <;> exact ⟨rfl, id⟩
        · exact hE x hx
      have hus' : ∀ u ∈ d :: rest, u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7 := by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hd
        · exact hus u (by simp [hu])
      obtain ⟨us', E', h1, h2, h3, h4, h5, h6⟩ :=
        ih (rest.length + 1) (by simp at hn; omega) (d :: rest) (bb :: E) rfl hus' hE'
      refine ⟨us', E', h1, h2, h3, by rw [h4]; simp only [List.length_cons]; omega, fun _ => h5 (by simp), ?_⟩
      · rw [← h6]
        -- reorder: [a, b, c] ++ rest ++ E  ~  [sq d, bb] ++ rest ++ E
        have p1 : (sqList e (a :: b :: c :: rest) ++ E) =
            [DyBlock.sq e a, .sq e b, .sq e c] ++ (sqList e rest ++ E) := by simp [sqList]
        have p2 : (sqList e (d :: rest) ++ bb :: E).Perm ([DyBlock.sq e d, bb] ++ (sqList e rest ++ E)) := by
          simp only [sqList, List.map_cons, List.cons_append]
          exact List.Perm.cons _ (List.perm_middle.trans (List.Perm.refl _))
        rw [p1, blockF_perm p2, blockF_congr_append hF]

/-- **Normal form of one constituent**: every list of blocks of exponent $e$ has the same contribution to the symbol as
a list of at most two blocks $2^e ux^2$ followed by binary blocks, with as many blocks $2^e ux^2$ modulo $2$, and at least
one if the original has one. -/
theorem exists_normal (e : ℤ) (L : List DyBlock) (hv : ∀ c ∈ L, c.Valid) (he : ∀ c ∈ L, blockExp c = e) :
    ∃ (us : List ℤ) (E : List DyBlock), (∀ u ∈ us, u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) ∧ IsEvenList e E ∧
      us.length ≤ 2 ∧ ((∃ c ∈ L, IsSqBlock c) → us ≠ []) ∧ blockF L = blockF (sqList e us ++ E) := by
  classical
  -- split `L` into its square blocks and the others
  set S := L.filter fun c => decide (IsSqBlock c)
  set T := L.filter fun c => !decide (IsSqBlock c)
  have hperm : L.Perm (S ++ T) := (List.filter_append_perm _ L).symm
  let unit : DyBlock → ℤ := fun c => match c with
    | .sq _ u => u
    | _ => 0
  have hS : S = sqList e (S.map unit) := by
    unfold sqList
    rw [List.map_map]
    conv_lhs => rw [← List.map_id S]
    refine List.map_congr_left fun c hc => ?_
    have hc' := List.mem_filter.mp hc
    have hce := he c hc'.1
    cases c with
    | sq e' u => simp only [blockExp] at hce; simp [hce, unit]
    | hyp e' => simp [IsSqBlock] at hc'
    | ell e' => simp [IsSqBlock] at hc'
  have hT : IsEvenList e T := by
    intro c hc
    have hc' := List.mem_filter.mp hc
    exact ⟨he c hc'.1, by simpa using hc'.2⟩
  have hus : ∀ u ∈ S.map unit, u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7 := by
    intro u hu
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hu
    have hc' := List.mem_filter.mp hc
    have := hv c hc'.1
    cases c with
    | sq e' u => exact this
    | hyp e' => simp [IsSqBlock] at hc'
    | ell e' => simp [IsSqBlock] at hc'
  obtain ⟨us', E', h1, h2, h3, -, h5, h6⟩ := exists_normal_aux e _ (S.map unit) T rfl hus hT
  refine ⟨us', E', h1, h2, h3, fun ⟨c, hc, hsq⟩ => h5 ?_, ?_⟩
  · intro h0
    have : c ∈ S := List.mem_filter.mpr ⟨hc, by simpa using hsq⟩
    rw [List.map_eq_nil_iff] at h0
    rw [h0] at this
    simp at this
  · rw [blockF_perm hperm, ← h6, ← hS]

/-! ### Equal symbols give equal densities (Theorem 10) -/

theorem theorem10Cond_refl (σ : TwoSymbol) (N : ℕ) : Theorem10Cond σ σ N := by
  refine ⟨fun k => ⟨rfl, rfl⟩, fun m _ => ?_⟩
  simp

/-- **Block decompositions with the same symbol are $\mathbb Z_2$-equivalent** (Theorem 10). -/
theorem zpEquiv_of_blockSymbol_eq {D D' : List DyBlock} (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b)
    (hD' : ∀ b ∈ D', b.Valid) (hD'0 : ∀ b ∈ D', 0 ≤ blockExp b) (hn : dyDim D' = dyDim D)
    (hσ : blockSymbol D = blockSymbol D') :
    ZpEquiv ((intMat D).map (Int.cast : ℤ → ℚ_[2]))
      (((intMat D').submatrix (Fin.cast hn.symm) (Fin.cast hn.symm)).map (Int.cast : ℤ → ℚ_[2])) := by
  obtain ⟨N, hN⟩ := TwoAdic.blockSymbol_supported D hD0
  have hN' : (blockSymbol D').SupportedBelow N := hσ ▸ hN
  have h := (TwoAdic.zpEquiv_castMat_iff (n := dyDim D) rfl hn hD hD0 hD' hD'0 hN hN').mpr
    (hσ ▸ theorem10Cond_refl _ N)
  have e1 : TwoAdic.castMat D (rfl : dyDim D = dyDim D) = (intMat D).map (Int.cast : ℤ → ℚ_[2]) := by
    unfold TwoAdic.castMat; rw [intMat_map D hD0]; ext i j; rfl
  have e2 : TwoAdic.castMat D' hn =
      ((intMat D').submatrix (Fin.cast hn.symm) (Fin.cast hn.symm)).map (Int.cast : ℤ → ℚ_[2]) := by
    unfold TwoAdic.castMat; rw [← intMat_map D' hD'0]; rfl
  rw [← e1, ← e2]
  exact h

theorem reidx_cast {m n : ℕ} (h : m = n) (N : Matrix (Fin n) (Fin n) ℤ) :
    Reidx (N.submatrix (Fin.cast h) (Fin.cast h)) N := ⟨finCongr h, rfl⟩

theorem alphaP_eq_of_blockSymbol_eq {D D' : List DyBlock} (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b)
    (hD' : ∀ b ∈ D', b.Valid) (hD'0 : ∀ b ∈ D', 0 ≤ blockExp b) (hn : dyDim D' = dyDim D)
    (hσ : blockSymbol D = blockSymbol D') : alphaP 2 (intMat D) = alphaP 2 (intMat D') := by
  rw [← alphaP_eq_of_zpEquiv (zpEquiv_of_blockSymbol_eq hD hD0 hD' hD'0 hn hσ),
    alphaP_reidx (reidx_cast hn.symm _)]

theorem pMassDensity_eq_of_blockSymbol_eq {D D' : List DyBlock} (hD : ∀ b ∈ D, b.Valid)
    (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) (hD' : ∀ b ∈ D', b.Valid) (hD'0 : ∀ b ∈ D', 0 ≤ blockExp b)
    (hn : dyDim D' = dyDim D) (hσ : blockSymbol D = blockSymbol D') :
    pMassDensity 2 (intMat D) = pMassDensity 2 (intMat D') := by
  have hdet : (intMat D).det ≠ 0 := det_intMat_ne _ hD
  have hdet' : ((intMat D').submatrix (Fin.cast hn.symm) (Fin.cast hn.symm)).det ≠ 0 := by
    rw [show (Fin.cast hn.symm : Fin (dyDim D) → Fin (dyDim D')) = (finCongr hn.symm) from rfl,
      Matrix.det_submatrix_equiv_self]
    exact det_intMat_ne _ hD'
  rw [← pMassDensity_eq_of_zpEquiv (zpEquiv_of_blockSymbol_eq hD hD0 hD' hD'0 hn hσ) hdet hdet',
    pMassDensity_reidx (reidx_cast hn.symm _) (det_intMat_ne _ hD')]

end QuadFormsKB.ConwaySloane.Mass.Two
