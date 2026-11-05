/-
# O'Meara 93:28, sufficiency over a 2-adic field: the step-4 move inside $K$

**Setting** (as in `Sec93FCoreTwo.lean`): $R$ a discrete valuation ring with finite residue field and fraction field
$F$, Henselian, $2 \in F^\times$, $2$ not a unit of $R$ (dyadic), $F$ a local Hilbert field.

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 4, p. 274)
* `shift_keep`: 93:19 inside a Jordan splitting that *keeps* the other components;
* `move`: the move $\langle A(0,0)\rangle \perp K_1 \perp K_2 \cong \langle A(-\lambda,0)\rangle \perp K_1 \perp K_2
  \cong \langle A(-\lambda, a_2)\rangle \perp K_1 \perp K_2' \cong \langle A(0,0)\rangle \perp K_1' \perp K_2'$, done
  inside $K$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FCore8
import QuadFormsKB.Literature.OMeara.Sec93FCoreTwo
import QuadFormsKB.Literature.OMeara.Sec93FTransfer
import QuadFormsKB.Literature.OMeara.Sec93D18Five
import QuadFormsKB.Literature.OMeara.Sec93DEng

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.CoreMove

section Shift

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open D18 Sat93 CoreSplit CoreTwo

/-- **93:19 inside a Jordan splitting, keeping the other components** (O'Meara 1963, §93D, 93:19, p. 262, as used
in §93F, step 4, p. 274). Hypotheses as in `CoreTwo.exists_shift_first`: $K = K_1 \perp \cdots \perp K_{t+2}$ a Jordan
splitting (`Ks 0`, `Ks 1`, … are $K_1, K_2, \dots$) with $K_1$ unimodular (`hs0`), $K_1 = J \perp C$ with
$J = \mathfrak ox + \mathfrak oy$ (`hJC`), $Q(x) = \alpha \in \mathfrak p$ (`hα`), $B(x, y) = 1$, $Q(y) = \beta$,
$\operatorname{rank} K_2 \ge 3$ (`hrk1`), $\gamma_0 \in \mathfrak g K_2$ (`hγ`) and $(\alpha + \gamma_0)\beta - 1$ a
unit (`hdet`). Conclusion: there are $x', y' \in V$ and a lattice $K''$ with $Q(x') = \alpha + \gamma_0$,
$B(x', y') = 1$, $Q(y') = \beta$, such that replacing $K_1$ by $J' \perp C$ ($J' = \mathfrak ox' + \mathfrak oy'$) and
$K_2$ by $K''$ gives again a Jordan splitting of $K$, with $\mathfrak gK_2 \subseteq \mathfrak gK''$, and $K''$ has
the scale and rank of $K_2$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 4, p. 274 (93:13, 93:19 inside K)"]
theorem shift_keep (hHil : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {K : Submodule R V}
    (hKfg : K.FG) {t : ℕ} {Ks : Fin (t + 2) → Submodule R V} (hK : IsJordanSplitting Q K Ks)
    (hs0 : scale Q (Ks 0) = 1) {x y : V} {C : Submodule R V} (hJC : IsOrthSum Q (Ks 0) (span R {x, y}) C)
    {α β : R} (hQx : Q x = algebraMap R F α) (hxy : bil Q x y = 1) (hQy : Q y = algebraMap R F β)
    (hα : α ∈ maximalIdeal R) (hrk1 : 3 ≤ finrank R (Ks 1)) {γ₀ : R}
    (hγ : algebraMap R F γ₀ ∈ normGroup Q (Ks 1)) (hdet : IsUnit ((α + γ₀) * β - 1 * 1)) :
    ∃ x' y' : V, ∃ K'' : Submodule R V, Q x' = algebraMap R F (α + γ₀) ∧ bil Q x' y' = 1 ∧
      Q y' = algebraMap R F β ∧
      IsJordanSplitting Q K (Function.update (Function.update Ks 0 (span R {x', y'} ⊔ C)) 1 K'') ∧
      IsOrthSum Q (span R {x', y'} ⊔ C) (span R {x', y'}) C ∧
      normGroup Q (Ks 1) ≤ normGroup Q K'' ∧ scale Q K'' = scale Q (Ks 1) ∧
      finrank R K'' = finrank R (Ks 1) := by
  set J : Submodule R V := span R {x, y} with hJdef
  have hle : ∀ j, Ks j ≤ K := fun j => hK.split.iSup_eq ▸ le_iSup Ks j
  have hK0fg : (Ks 0).FG := FG.of_le hKfg (hle 0)
  have hK1fg : (Ks 1).FG := FG.of_le hKfg (hle 1)
  have hJK0 : J ≤ Ks 0 := hJC.sup_eq ▸ le_sup_left
  have hCK0 : C ≤ Ks 0 := hJC.sup_eq ▸ le_sup_right
  have h01 : (0 : Fin (t + 2)) ≠ 1 := by simp [Fin.ext_iff]
  have hαβ : IsUnit (α * β - 1 * 1) := by
    have : α * β - 1 * 1 = -(1 - α * β) := by ring
    rw [this, IsUnit.neg_iff]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right _ _ hα))
  have hJmod := span_pair_isModular Q one_ne_zero hαβ (by rw [hQx, one_mul]) (by rw [hQy, one_mul])
    (by rw [hxy, map_one, mul_one])
  rw [← Submodule.one_eq_span] at hJmod
  have horthJ1 : ∀ u ∈ J, ∀ v ∈ Ks 1, bil Q u v = 0 := fun u hu v hv =>
    hK.split.orth 0 1 h01 u (hJK0 hu) v hv
  have hJfg : J.FG := FG.of_le hK0fg hJK0
  have hJreg : IsRegular Q J := hJmod.1.isRegular Q hJfg
  have hM : IsOrthSum Q (J ⊔ Ks 1) J (Ks 1) := ⟨horthJ1, disjoint_of_orth Q hJreg horthJ1, rfl⟩
  have hs1lt : scale Q (Ks 1) < 1 := hs0 ▸ hK.scale_strictAnti (show (0 : Fin (t + 2)) < 1 by simp [Fin.lt_def])
  have ha := le_maximal_of_lt_one (scale_fg Q hK1fg) (hK.modular 1).1 hs1lt
  have hαβ' : IsUnit (-1 + α * β) := by
    have : -1 + α * β = α * β - 1 * 1 := by ring
    rw [this]; exact hαβ
  obtain ⟨x', y', K'', hQx', hx'y', hQy', hM', hnorm⟩ :=
    omeara93_19 Q hHil h2p hM rfl hQx hxy hQy hαβ' hK1fg (hK.modular 1) ha hrk1 hγ
  have hJ'mod := span_pair_isModular Q one_ne_zero hdet (by rw [hQx', one_mul, map_add])
    (by rw [hQy', one_mul]) (by rw [hx'y', map_one, mul_one])
  rw [← Submodule.one_eq_span] at hJ'mod
  set J' : Submodule R V := span R {x', y'} with hJ'def
  have hCfg : C.FG := FG.of_le hK0fg hCK0
  have hJ0 : J ≠ ⊥ := by
    intro h
    have := hJmod.2
    rw [← hJdef, h, finrank_bot] at this
    exact absurd this (by norm_num)
  have hJ'M : J' ≤ J ⊔ Ks 1 := hM'.sup_eq ▸ le_sup_left
  have hK''M : K'' ≤ J ⊔ Ks 1 := hM'.sup_eq ▸ le_sup_right
  have horthCM : ∀ u ∈ C, ∀ v ∈ J ⊔ Ks 1, bil Q u v = 0 := by
    intro u hu v hv
    obtain ⟨a, ha', b, hb, rfl⟩ := mem_sup.mp hv
    rw [bil_add_right, bil_comm Q u a, hJC.orth a ha' u hu, hK.split.orth 0 1 h01 u (hCK0 hu) b hb, add_zero]
  set A : Submodule R V := J' ⊔ C with hAdef
  have horthJ'C : ∀ u ∈ J', ∀ v ∈ C, bil Q u v = 0 := fun u hu v hv => by
    rw [bil_comm]; exact horthCM v hv u (hJ'M hu)
  have hJ'fg : J'.FG := Submodule.fg_span (Set.toFinite _)
  have hAmod : IsModular Q 1 A ∧ finrank R A = finrank R J' + finrank R C := by
    by_cases hC0 : C = ⊥
    · rw [hAdef, hC0, sup_bot_eq, finrank_bot, add_zero]
      exact ⟨hJ'mod.1, rfl⟩
    · have hCmod : IsModular Q 1 C :=
        ((Dedekind.isModular_iff_of_isOrthSum Q hJC hJfg hCfg hJ0 hC0).mp (hs0 ▸ hK.modular 0)).2
      exact isModular_sup Q hJ'mod.1 hCmod hJ'fg hCfg horthJ'C
  set T : Submodule R V := ⨆ j : Fin t, Ks j.succ.succ with hTdef
  have horthT : ∀ i : Fin (t + 2), i = 0 ∨ i = 1 → ∀ u ∈ Ks i, ∀ v ∈ T, bil Q u v = 0 := by
    intro i hi u hu v hv
    refine iSup_induction (fun j : Fin t => Ks j.succ.succ) (motive := fun v => bil Q u v = 0) hv ?_
      (by simp [bil]) (fun a b ha hb => by rw [bil_add_right, ha, hb, add_zero])
    intro j w hw
    refine hK.split.orth i j.succ.succ ?_ u hu w hw
    rcases hi with rfl | rfl <;> simp [Fin.ext_iff]
  set C' : Submodule R V := K'' ⊔ T with hC'def
  have horthAC' : ∀ u ∈ A, ∀ v ∈ C', bil Q u v = 0 := by
    intro u hu v hv
    obtain ⟨a, ha', c, hc, rfl⟩ := mem_sup.mp hu
    obtain ⟨k, hk, w, hw, rfl⟩ := mem_sup.mp hv
    have hJ'T : ∀ a ∈ J', bil Q a w = 0 := by
      intro a ha'
      obtain ⟨j, hj, k1, hk1, hjk⟩ := mem_sup.mp (hJ'M ha')
      rw [← hjk, bil_add_left, horthT 0 (Or.inl rfl) j (hJK0 hj) w hw, horthT 1 (Or.inr rfl) k1 hk1 w hw,
        add_zero]
    rw [bil_add_left, bil_add_right, bil_add_right, hM'.orth a ha' k hk, hJ'T a ha', horthCM c hc k (hK''M hk),
      horthT 0 (Or.inl rfl) c (hCK0 hc) w hw]
    ring
  have hAreg : IsRegular Q A := hAmod.1.isRegular Q (hJ'fg.sup hCfg)
  have h2 : (⨆ i, Ks i) = Ks 0 ⊔ (Ks 1 ⊔ T) := by
    rw [SuffStep.iSup_eq_zero_sup, SuffStep.tailLat, SuffStep.iSup_eq_zero_sup (fun k : Fin (t + 1) => Ks k.succ),
      SuffStep.tailLat]
    rfl
  have hsupK : A ⊔ C' = K := by
    have h1 : J' ⊔ K'' = J ⊔ Ks 1 := hM'.sup_eq
    rw [← hK.split.iSup_eq, h2, ← hJC.sup_eq, hAdef, hC'def]
    calc J' ⊔ C ⊔ (K'' ⊔ T) = (J' ⊔ K'') ⊔ C ⊔ T := by ac_rfl
      _ = (J ⊔ Ks 1) ⊔ C ⊔ T := by rw [h1]
      _ = J ⊔ C ⊔ (Ks 1 ⊔ T) := by ac_rfl
  have hrk0 : finrank R A = finrank R (Ks 0) := by
    rw [hAmod.2, hJ'mod.2, isOrthSum_finrank Q hJC hK0fg, hJmod.2]
  -- `K''` is `𝔰K₂`-modular of the rank of `K₂` (91:9 applied to `J ⊥ K₂`)
  have hJK1fg : (J ⊔ Ks 1).FG := hJfg.sup hK1fg
  have hJ1 : IsJordanSplitting Q (Ks 1) (fun _ : Fin 1 => Ks 1) := by
    refine ⟨⟨fun i j hij => absurd (Subsingleton.elim i j) hij, ?_, ?_⟩, fun _ => hK.modular 1, ?_⟩
    · exact iSupIndep_of_orth Q (fun i j hij => absurd (Subsingleton.elim i j) hij)
        (fun _ => (hK.modular 1).isRegular Q hK1fg)
    · exact iSup_const
    · intro i j hij
      exact absurd (Subsingleton.elim i j) hij.ne
  have hJs : IsJordanSplitting Q (J ⊔ Ks 1) (Fin.cons J (fun _ : Fin 1 => Ks 1) : Fin (1 + 1) → Submodule R V) :=
    isJordanSplitting_cons Q hJK1fg hM (by rw [hJmod.1.2.1]; exact hJmod.1) hJ1
      (fun _ => by rw [hJmod.1.2.1]; exact hs1lt)
  obtain ⟨Cs, hCsJ, -, hCs⟩ := exists_jordan_cons_of_compl Q hJK1fg hJs hM'
    (by simp only [Fin.cons_zero]; rw [hJmod.1.2.1]; exact hJ'mod.1)
    (by show finrank R J' = finrank R J; rw [hJ'mod.2, hJmod.2])
  have hCs0 : Cs 0 = K'' := by
    rw [← hCsJ.split.iSup_eq]
    exact le_antisymm (le_iSup Cs 0) (iSup_le fun i => by rw [Subsingleton.elim i 0])
  have hK''sc : scale Q K'' = scale Q (Ks 1) := by
    rw [← hCs0]; exact (hCs 0).1
  have hK''rk : finrank R K'' = finrank R (Ks 1) := by
    rw [← hCs0]; exact (hCs 0).2
  have hK''mod : IsModular Q (scale Q (Ks 1)) K'' := by
    have := hCsJ.modular 0
    rw [hCs0, hK''sc] at this
    exact this
  -- the new family
  set N : Fin (t + 2) → Submodule R V := Function.update (Function.update Ks 0 A) 1 K'' with hNdef
  have hN0 : N 0 = A := by
    simp [hNdef, Function.update_of_ne h01]
  have hN1 : N 1 = K'' := by
    simp [hNdef]
  have hNj : ∀ j : Fin t, N j.succ.succ = Ks j.succ.succ := by
    intro j
    have e1 : j.succ.succ ≠ 1 := fun h => by
      have := congrArg Fin.val h; simp at this
    have e0 : j.succ.succ ≠ 0 := Fin.succ_ne_zero _
    simp [hNdef, Function.update_of_ne e1, Function.update_of_ne e0]
  have cls : ∀ i : Fin (t + 2), i = 0 ∨ i = 1 ∨ ∃ j : Fin t, i = j.succ.succ := fun i =>
    Fin.cases (Or.inl rfl) (fun i => Fin.cases (Or.inr (Or.inl rfl))
      (fun j => Or.inr (Or.inr ⟨j, rfl⟩)) i) i
  have hTle : ∀ j : Fin t, Ks j.succ.succ ≤ T := fun j => le_iSup (fun j : Fin t => Ks j.succ.succ) j
  have f01 : ∀ u ∈ A, ∀ v ∈ K'', bil Q u v = 0 := fun u hu v hv =>
    horthAC' u hu v (mem_sup_left hv)
  have f0T : ∀ u ∈ A, ∀ v ∈ T, bil Q u v = 0 := fun u hu v hv =>
    horthAC' u hu v (mem_sup_right hv)
  have f1T : ∀ u ∈ K'', ∀ v ∈ T, bil Q u v = 0 := by
    intro u hu v hv
    obtain ⟨a, ha', b, hb, rfl⟩ := mem_sup.mp (hK''M hu)
    rw [bil_add_left, horthT 0 (Or.inl rfl) a (hJK0 ha') v hv, horthT 1 (Or.inr rfl) b hb v hv, add_zero]
  have horthN : ∀ i j, i ≠ j → ∀ x ∈ N i, ∀ y ∈ N j, bil Q x y = 0 := by
    intro i j hij x hx y hy
    rcases cls i with rfl | rfl | ⟨a, rfl⟩ <;> rcases cls j with rfl | rfl | ⟨b, rfl⟩
    · exact absurd rfl hij
    · rw [hN0] at hx; rw [hN1] at hy; exact f01 x hx y hy
    · rw [hN0] at hx; rw [hNj] at hy; exact f0T x hx y (hTle b hy)
    · rw [hN1] at hx; rw [hN0] at hy; rw [bil_comm]; exact f01 y hy x hx
    · exact absurd rfl hij
    · rw [hN1] at hx; rw [hNj] at hy; exact f1T x hx y (hTle b hy)
    · rw [hNj] at hx; rw [hN0] at hy; rw [bil_comm]; exact f0T y hy x (hTle a hx)
    · rw [hNj] at hx; rw [hN1] at hy; rw [bil_comm]; exact f1T y hy x (hTle a hx)
    · rw [hNj] at hx hy; exact hK.split.orth _ _ hij x hx y hy
  have hNle : ∀ i, N i ≤ K := by
    intro i
    rcases cls i with rfl | rfl | ⟨a, rfl⟩
    · rw [hN0]; exact hsupK ▸ le_sup_left
    · rw [hN1]; exact hsupK ▸ (le_sup_left.trans le_sup_right : K'' ≤ A ⊔ C')
    · rw [hNj]; exact hle _
  have hNmod : ∀ i, IsModular Q (scale Q (Ks i)) (N i) := by
    intro i
    rcases cls i with rfl | rfl | ⟨a, rfl⟩
    · rw [hN0, hs0]; exact hAmod.1
    · rw [hN1]; exact hK''mod
    · rw [hNj]; exact hK.modular _
  have hNreg : ∀ i, IsRegular Q (N i) := fun i => (hNmod i).isRegular Q (FG.of_le hKfg (hNle i))
  have hNsup : (⨆ i, N i) = K := by
    have e1 : N (0 : Fin (t + 1)).succ = K'' := by rw [Fin.succ_zero_eq_one]; exact hN1
    have : (⨆ i, N i) = A ⊔ (K'' ⊔ T) := by
      rw [SuffStep.iSup_eq_zero_sup, SuffStep.tailLat, SuffStep.iSup_eq_zero_sup (fun k : Fin (t + 1) => N k.succ),
        SuffStep.tailLat, hN0]
      show A ⊔ (N (0 : Fin (t + 1)).succ ⊔ ⨆ j : Fin t, N j.succ.succ) = _
      rw [e1]
      simp only [hNj]
      rfl
    rw [this]; exact hsupK
  have hNsplit : IsOrthSplit Q K N := ⟨horthN, iSupIndep_of_orth Q horthN hNreg, hNsup⟩
  have hNJ : IsJordanSplitting Q K N :=
    NecI.isJordanSplitting_of_scales Q hNsplit hK.scale_strictAnti hNmod
  refine ⟨x', y', K'', by rw [hQx', map_add], hx'y', hQy', hNJ, ?_, hnorm, hK''sc, hK''rk⟩
  exact ⟨horthJ'C, disjoint_of_orth Q (hJ'mod.1.isRegular Q hJ'fg) horthJ'C, rfl⟩

omit [FiniteDimensional F V] [CharZero F] [HenselianLocalRing R] [Finite (ResidueField R)] in
/-- The discriminant of a pair: $\det\begin{pmatrix}Q(x) & B(x,y)\\ B(x,y) & Q(y)\end{pmatrix} = Q(x)Q(y) - B(x,y)^2$. -/
theorem det_gram_pair (x y : V) : (gram Q ![x, y]).det = Q x * Q y - bil Q x y ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [gram, bil_comm Q y x]
  ring

omit [FiniteDimensional F V] [CharZero F] [HenselianLocalRing R] [Finite (ResidueField R)] in
/-- A pair with non-zero discriminant is a base of $\mathfrak ox + \mathfrak oy$ (indexed by `Fin 2`). -/
theorem exists_basis_pair {x y : V} (hdet : Q x * Q y - bil Q x y ^ 2 ≠ 0) :
    ∃ b : Basis (Fin 2) R (span R {x, y}), ∀ i, (b i : V) = ![x, y] i := by
  have hli : LinearIndependent R ![x, y] :=
    linearIndependent_of_det_gram_ne_zero Q (by rw [det_gram_pair]; exact hdet)
  have hspan : span R (Set.range ![x, y]) = span R {x, y} := by
    congr 1; ext w; simp [or_comm]
  exact ⟨(Basis.span hli).map (LinearEquiv.ofEq _ _ hspan), fun i => by simp [Basis.span_apply]⟩

/-- **The step-4 move inside $K$** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 4, p. 274:
"$\langle A(0,0)\rangle \perp K_1 \perp K_2 \cong \langle A(-\lambda,0)\rangle \perp K_1 \perp K_2 \cong
\langle A(-\lambda, a_2)\rangle \perp K_1 \perp K_2' \cong \langle A(0,0)\rangle \perp K_1' \perp K_2'$").
Let $K = K_1 \perp \cdots \perp K_{t+2}$ be a Jordan splitting (`Ks 0`, `Ks 1`, … are $K_1, K_2, \dots$) with $K_1$
unimodular (`hs0`) of rank $\ge 5$ (`hrk0`), $\operatorname{rank} K_2 \ge 3$ (`hrk1`), and $K_1 = (\mathfrak ox +
\mathfrak oy) \perp D$ with $Q(x) = Q(y) = 0$, $B(x, y) = 1$ (`hPD`, `hQx`, `hQy`, `hxy`). Let $\lambda_0 \in
\mathfrak gD$ (`hl`, written `l₀`) and $\gamma_0 \in \mathfrak gK_2$ (`hγ`). Then $K$ has a Jordan splitting
`Ks'` with the scales and ranks of the $K_i$ (the components $K_i$, $i \ge 3$ in O'Meara's numbering, i.e.
`Ks i` for `2 ≤ i`, are unchanged) and $\mathfrak gK_2 \subseteq \mathfrak gK_2'$, such that $K_1' = (\mathfrak ox' +
\mathfrak oy') \perp D'$ with $Q(x') = Q(y') = 0$, $B(x', y') = 1$, $\mathfrak gD \subseteq \mathfrak gD'$, and $D'$
has a base `bD'` (indexed like the given base `bD` of $D$) with discriminant
$dD' = u^2 (1 - \gamma_0\lambda_0)\,dD$ for a unit $u$ of $\mathfrak o$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 4, p. 274 (93:13, 93:19 inside K)"]
theorem move (hHil : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {K : Submodule R V} (hKfg : K.FG)
    {t : ℕ} {Ks : Fin (t + 2) → Submodule R V} (hK : IsJordanSplitting Q K Ks) (hs0 : scale Q (Ks 0) = 1)
    (hrk0 : 5 ≤ finrank R (Ks 0)) (hrk1 : 3 ≤ finrank R (Ks 1)) {x y : V} {D : Submodule R V}
    (hPD : IsOrthSum Q (Ks 0) (span R {x, y}) D) (hQx : Q x = 0) (hQy : Q y = 0) (hxy : bil Q x y = 1)
    {l₀ γ₀ : R} (hl : algebraMap R F l₀ ∈ normGroup Q D) (hγ : algebraMap R F γ₀ ∈ normGroup Q (Ks 1))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bD : Basis ι R D) :
    ∃ Ks' : Fin (t + 2) → Submodule R V, IsJordanSplitting Q K Ks' ∧
      (∀ i : Fin (t + 2), 2 ≤ (i : ℕ) → Ks' i = Ks i) ∧
      normGroup Q (Ks 1) ≤ normGroup Q (Ks' 1) ∧
      (∀ i, scale Q (Ks' i) = scale Q (Ks i) ∧ finrank R (Ks' i) = finrank R (Ks i)) ∧
      ∃ x' y' : V, ∃ D' : Submodule R V, Q x' = 0 ∧ Q y' = 0 ∧ bil Q x' y' = 1 ∧
        IsOrthSum Q (Ks' 0) (span R {x', y'}) D' ∧ normGroup Q D ≤ normGroup Q D' ∧
        ∃ bD' : Basis ι R D', ∃ u : R, IsUnit u ∧
          (gram Q fun i => (bD' i : V)).det =
            algebraMap R F u ^ 2 * (1 - algebraMap R F γ₀ * algebraMap R F l₀) *
              (gram Q fun i => (bD i : V)).det := by
  set J : Submodule R V := span R {x, y} with hJdef
  have hle : ∀ j, Ks j ≤ K := fun j => hK.split.iSup_eq ▸ le_iSup Ks j
  have hK0fg : (Ks 0).FG := FG.of_le hKfg (hle 0)
  have hK1fg : (Ks 1).FG := FG.of_le hKfg (hle 1)
  have hJK0 : J ≤ Ks 0 := hPD.sup_eq ▸ le_sup_left
  have hDK0 : D ≤ Ks 0 := hPD.sup_eq ▸ le_sup_right
  have hDfg : D.FG := FG.of_le hK0fg hDK0
  have h01 : (0 : Fin (t + 2)) ≠ 1 := by simp [Fin.ext_iff]
  have hinj := IsFractionRing.injective R F
  -- (a) 93:13: `Ks 0 = ox₁ + oy₁ ⊥ C₁` with `Q x₁ = l₀`
  obtain ⟨z, hzD, c, hc, hzc⟩ := hl
  have hsD : scale Q D ≤ R ∙ (1 : F) := by
    rw [← Submodule.one_eq_span, ← hs0]; exact scale_mono Q hDK0
  have hsubD : subA Q (R ∙ (1 : F)) D = D :=
    le_antisymm (fun _ hx => hx.1) fun w hw => ⟨hw, fun l hl' => hsD (bil_mem_scale Q hw hl')⟩
  obtain ⟨x₁, y₁, α', hα', hQx₁, hx₁y₁, hQy₁, hOrth, hiso⟩ :=
    exists_isOrthSum_matA Q hPD (ξ := 1) one_ne_zero (α := 0) rfl (by rw [hQx]; simp)
      hxy hQy (z := z) (by rw [hsubD]; exact hzD) (c := c) (by rw [hsubD]; exact hc)
  have hQx₁' : Q x₁ = algebraMap R F l₀ := by
    rw [hQx₁, one_mul]
    have : algebraMap R F α' = algebraMap R F l₀ := by rw [hα', hzc]; simp
    exact this
  set C₁ := splitComp Q (Ks 0) (span R {x₁, y₁}) with hC₁def
  have hC₁K0 : C₁ ≤ Ks 0 := fun w hw => hw.1
  have hC₁fg : C₁.FG := FG.of_le hK0fg hC₁K0
  -- ranks of the pair `x₁, y₁`
  have hdet₁ : IsUnit (l₀ * 0 - 1 * 1 : R) := by simp
  have hJ₁ := D18.span_pair_isModular Q (one_ne_zero (α := F)) (p := l₀) (q := 0) (e := 1) hdet₁
    (by rw [hQx₁', one_mul]) (by rw [hQy₁]; simp) (by rw [hx₁y₁, map_one, mul_one])
  -- (b) 93:19 keeping the other components, with `x := y₁`, `y := x₁`
  have hγm : γ₀ ∈ maximalIdeal R := by
    have hs1lt : scale Q (Ks 1) < 1 := hs0 ▸ hK.scale_strictAnti (show (0 : Fin (t + 2)) < 1 by simp [Fin.lt_def])
    have ha := le_maximal_of_lt_one (scale_fg Q hK1fg) (hK.modular 1).1 hs1lt
    obtain ⟨w, hw, c', hc', hwc⟩ := id hγ
    have hQw : Q w ∈ scale Q (Ks 1) := by rw [← bil_self]; exact bil_mem_scale Q hw hw
    obtain ⟨r, hr, hr'⟩ := ha hQw
    obtain ⟨s, hs, hs'⟩ := ha hc'
    rw [Algebra.linearMap_apply] at hr' hs'
    have : algebraMap R F γ₀ = algebraMap R F (r + 2 * s) := by
      rw [hwc, map_add, map_mul, map_ofNat, hr', hs']
    rw [hinj this]
    exact add_mem hr (Ideal.mul_mem_left _ _ hs)
  have hdetS : IsUnit ((0 + γ₀) * l₀ - 1 * 1) := by
    have : (0 + γ₀) * l₀ - 1 * 1 = -(1 - γ₀ * l₀) := by ring
    rw [this, IsUnit.neg_iff]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right _ _ hγm))
  have hOrth' : IsOrthSum Q (Ks 0) (span R {y₁, x₁}) C₁ := by
    rw [Set.pair_comm]; exact hOrth
  obtain ⟨x'', y'', K'', hQx'', hx''y'', hQy'', hJS, hOS, hnorm, hsc, hrk⟩ :=
    shift_keep Q hHil h2p hKfg hK hs0 hOrth' (α := 0) (β := l₀) (by rw [hQy₁, map_zero])
      (by rw [bil_comm, hx₁y₁]) hQx₁' (zero_mem _) hrk1 hγ hdetS
  set J'' : Submodule R V := span R {x'', y''} with hJ''def
  have hJ''mod := D18.span_pair_isModular Q (one_ne_zero (α := F)) hdetS
    (by rw [hQx'', one_mul]) (by rw [hQy'', one_mul]) (by rw [hx''y'', map_one, mul_one])
  rw [← Submodule.one_eq_span] at hJ''mod
  set A : Submodule R V := J'' ⊔ C₁ with hAdef
  have hJ''fg : J''.FG := Submodule.fg_span (Set.toFinite _)
  have hAfg : A.FG := hJ''fg.sup hC₁fg
  have hscA : scale Q A = 1 := by
    rw [hAdef, scale_sup_of_orth Q hOS.orth, hJ''mod.1.2.1]
    exact sup_eq_left.mpr ((scale_mono Q hC₁K0).trans hs0.le)
  have hKs0 : (Function.update (Function.update Ks 0 A) 1 K'') 0 = A := by
    simp [Function.update_of_ne h01]
  have hKs1 : (Function.update (Function.update Ks 0 A) 1 K'') 1 = K'' := by simp
  have hAmod : IsModular Q 1 A := by
    have := hJS.modular 0
    rwa [hKs0, hscA] at this
  have hrkA : finrank R A = finrank R (Ks 0) := by
    rw [isOrthSum_finrank Q hOS hAfg, hJ''mod.2, isOrthSum_finrank Q hOrth hK0fg, hJ₁.2]
  -- (c) 93:18 (v)
  obtain ⟨xs, ys, D', hQxs, hQys, hxys, hOS2⟩ :=
    D18.omeara93_18_v_splitting Q hHil h2p hAfg hAmod (hrkA ▸ hrk0)
  set Js : Submodule R V := span R {xs, ys} with hJsdef
  have hJsfg : Js.FG := Submodule.fg_span (Set.toFinite _)
  have hD'A : D' ≤ A := hOS2.sup_eq ▸ le_sup_right
  have hD'fg : D'.FG := FG.of_le hAfg hD'A
  have hJsA : Js ≤ A := hOS2.sup_eq ▸ le_sup_left
  have hJsrk : IsUnit (0 * 0 - 1 * 1 : R) := by simp
  have hJs := D18.span_pair_isModular Q (one_ne_zero (α := F)) (p := 0) (q := 0) (e := 1) hJsrk
    (by rw [hQxs]; simp) (by rw [hQys]; simp) (by rw [hxys]; simp)
  rw [← Submodule.one_eq_span] at hJs
  -- ranks
  have hDrk : finrank R D = Fintype.card ι := finrank_eq_card_basis bD
  have hKrk : finrank R (Ks 0) = 2 + finrank R D := by
    rw [isOrthSum_finrank Q hPD hK0fg]
    have := D18.span_pair_isModular Q (one_ne_zero (α := F)) (p := 0) (q := 0) (e := 1) hJsrk
      (by rw [hQx]; simp) (by rw [hQy]; simp) (by rw [hxy]; simp)
    rw [hJdef, this.2]
  have hC₁D : finrank R C₁ = finrank R D := by
    obtain ⟨f, -⟩ := hiso
    exact (LinearEquiv.finrank_eq f).symm
  have hD'rk : finrank R D' = Fintype.card ι := by
    have h1 := isOrthSum_finrank Q hOS2 hAfg
    rw [hJs.2, hrkA, hKrk, hDrk] at h1
    omega
  have hJs0 : Js ≠ ⊥ := by
    intro h
    have := hJs.2
    rw [← hJsdef, h, finrank_bot] at this
    exact absurd this (by norm_num)
  have hD'0 : D' ≠ ⊥ := by
    intro h
    have h1 := isOrthSum_finrank Q hOS2 hAfg
    rw [h, finrank_bot, hJs.2, hrkA] at h1
    omega
  have hD'mod : IsModular Q 1 D' :=
    ((Dedekind.isModular_iff_of_isOrthSum Q hOS2 hJsfg hD'fg hJs0 hD'0).mp hAmod).2
  -- norm groups
  have hnormD : normGroup Q D ≤ normGroup Q D' := by
    have e1 : normGroup Q D = normGroup Q C₁ := adj_normGroup_eq Q Q hiso
    have e2 : normGroup Q C₁ ≤ normGroup Q A := normGroup_mono Q le_sup_right
    have e3 : normGroup Q A = normGroup Q Js ⊔ normGroup Q D' := by
      rw [← hOS2.sup_eq]; exact normGroup_sup_of_orth Q hOS2.orth
    have e4 : normGroup Q Js ≤ normGroup Q D' := by
      rintro _ ⟨w, hw, c', hc', rfl⟩
      obtain ⟨a, b, rfl⟩ := mem_span_pair.mp hw
      have hc'1 : c' ∈ (1 : Submodule R F) := by
        rw [← hscA]; exact scale_mono Q hJsA hc'
      obtain ⟨s, rfl⟩ := Submodule.mem_one.mp hc'1
      have hQw : Q (a • xs + b • ys) = 2 * algebraMap R F (a * b) := by
        rw [Q_add, bil_rsmul_left, bil_rsmul_right, hxys, Q_rsmul, Q_rsmul, hQxs, hQys]
        simp only [map_mul]; ring
      rw [hQw]
      refine ⟨0, zero_mem _, algebraMap R F (a * b + s), ?_, ?_⟩
      · rw [hD'mod.2.1]; exact Submodule.mem_one.mpr ⟨_, rfl⟩
      · simp only [map_zero, map_add, QuadraticMap.map_zero]; ring
    rw [e1]
    exact e2.trans (by rw [e3]; exact sup_le e4 le_rfl)
  -- (d) determinants
  have hdetJ'' : Q x'' * Q y'' - bil Q x'' y'' ^ 2 = algebraMap R F ((0 + γ₀) * l₀ - 1 * 1) := by
    rw [hQx'', hQy'', hx''y'']
    simp only [map_sub, map_mul, map_one, one_pow, mul_one]
  obtain ⟨bJ'', hbJ''⟩ := exists_basis_pair (R := R) Q (x := x'') (y := y'')
    (by rw [hdetJ'']; exact (map_ne_zero_iff _ hinj).2 hdetS.ne_zero)
  have hdetJs : Q xs * Q ys - bil Q xs ys ^ 2 = -1 := by
    rw [hQxs, hQys, hxys]; ring
  obtain ⟨bJs, hbJs⟩ := exists_basis_pair (R := R) Q (x := xs) (y := ys)
    (by rw [hdetJs]; exact neg_ne_zero.2 one_ne_zero)
  obtain ⟨bC, hbC⟩ := Eng93.exists_basis_of_isometricLat Q (adj_isometricLat_symm Q Q hiso) bD
  obtain ⟨b0⟩ := exists_basis (R := R) (F := F) hD'fg
  let bD' : Basis ι R D' :=
    b0.reindex (Fintype.equivOfCardEq (by rw [Fintype.card_fin, hD'rk]))
  obtain ⟨e1, he1⟩ := Transfer28.exists_basis_isOrthSum Q hOS bJ'' bC
  obtain ⟨e2, he2⟩ := Transfer28.exists_basis_isOrthSum Q hOS2 bJs bD'
  obtain ⟨u, hu, hdu⟩ := Transfer28.det_gram_change Q e1 e2
  have d1 : (gram Q fun i => (e1 i : V)).det =
      (gram Q fun i => (bJ'' i : V)).det * (gram Q fun i => (bC i : V)).det := by
    have : (fun i => (e1 i : V)) = Sum.elim (fun i => (bJ'' i : V)) (fun k => (bC k : V)) := funext he1
    rw [this]
    exact Transfer28.det_gram_sumElim Q (fun a ha b hb => hOS.orth a ha b hb) _ _ (fun i => (bJ'' i).2)
      (fun k => (bC k).2)
  have d2 : (gram Q fun i => (e2 i : V)).det =
      (gram Q fun i => (bJs i : V)).det * (gram Q fun i => (bD' i : V)).det := by
    have : (fun i => (e2 i : V)) = Sum.elim (fun i => (bJs i : V)) (fun k => (bD' k : V)) := funext he2
    rw [this]
    exact Transfer28.det_gram_sumElim Q (fun a ha b hb => hOS2.orth a ha b hb) _ _ (fun i => (bJs i).2)
      (fun k => (bD' k).2)
  have d3 : (gram Q fun i => (bJ'' i : V)).det = algebraMap R F ((0 + γ₀) * l₀ - 1 * 1) := by
    have : (fun i => (bJ'' i : V)) = ![x'', y''] := funext hbJ''
    rw [this, det_gram_pair, hdetJ'']
  have d4 : (gram Q fun i => (bJs i : V)).det = -1 := by
    have : (fun i => (bJs i : V)) = ![xs, ys] := funext hbJs
    rw [this, det_gram_pair, hdetJs]
  have d5 : (gram Q fun i => (bC i : V)).det = (gram Q fun i => (bD i : V)).det := by rw [hbC]
  have key := hdu
  rw [d2, d1, d3, d4, d5] at key
  simp only [map_sub, map_mul, map_add, map_zero, map_one, zero_add, mul_one] at key
  refine ⟨Function.update (Function.update Ks 0 A) 1 K'', hJS, ?_, ?_, ?_, xs, ys, D', hQxs, hQys, hxys, ?_,
    hnormD, bD', u, hu, ?_⟩
  · intro i hi
    have e1' : i ≠ 1 := fun h => by subst h; simp at hi
    have e0' : i ≠ 0 := fun h => by subst h; simp at hi
    rw [Function.update_of_ne e1', Function.update_of_ne e0']
  · rw [hKs1]; exact hnorm
  · intro i
    rcases Fin.cases (Or.inl rfl) (fun i => Fin.cases (Or.inr (Or.inl rfl))
      (fun j => Or.inr (Or.inr ⟨j, rfl⟩)) i) i with
      (rfl | rfl | ⟨j, rfl⟩ : i = 0 ∨ i = 1 ∨ ∃ j : Fin t, i = j.succ.succ)
    · rw [hKs0, hscA, hs0]; exact ⟨rfl, hrkA⟩
    · rw [hKs1]; exact ⟨hsc, hrk⟩
    · have e1' : j.succ.succ ≠ 1 := fun h => by
        have := congrArg Fin.val h; simp at this
      have e0' : j.succ.succ ≠ 0 := Fin.succ_ne_zero _
      rw [Function.update_of_ne e1', Function.update_of_ne e0']
      exact ⟨rfl, rfl⟩
  · rw [hKs0]; exact hOS2
  · linear_combination (-1) * key

end Shift

end QuadFormsKB.OMeara.CoreMove
