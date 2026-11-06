/-
# O'Meara 93:29 over a 2-adic field: the core of the sufficiency

**Setting** (as in `Sec93G29Good.lean`): $R$ a 2-adic Henselian DVR with finite residue field, $F$ its fraction field.

**Proves** (O'Meara 1963, §93G, proof of 93:29, sufficiency, pp. 278--279)
* `hasBlk_isotropic_plane`: a lattice with a base of matrix $A(a, 0) \perp A(0, 0)$ spans a space containing a totally
  isotropic plane;
* `hyperbolic_residual`: the case $\mathfrak n_1 = 2\mathfrak o$, $\mathfrak n_2 = 4\mathfrak o$: $dL_1/dK_1 \cong 1 \bmod
  8\mathfrak o$ gives $dK_1 = 1$, and 93:18 (vi) (even case) gives $FK_1$ hyperbolic;
* `finish29`, `core29_one_four`: the case $\mathfrak n_1 = \mathfrak o$, $\mathfrak n_2 = 4\mathfrak o$ with conditions (i), (ii)
  of 93:29 (copies of `CoreTwoLast.finish`, `twoAdicCoreRest4` using `resplit29` and (ii) instead of (iii) of 93:28);
* `core29`: the core with conditions (i), (ii), all cases ($\mathfrak n_2 \ni 2$; $\mathfrak n_2 = 4\mathfrak o$ with
  $\mathfrak n_1 = \mathfrak o$ or $2\mathfrak o$; $\mathfrak n_2 \subseteq 8\mathfrak o$ via `exists_lagrangian_of_cond`).
-/
import QuadFormsKB.Literature.OMeara.Sec93G29Dim4
import QuadFormsKB.Literature.OMeara.Sec93D18Six
import QuadFormsKB.Literature.OMeara.Sec93DSub

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.G29

universe u v

section Residual

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open Sat93 Adjoin28 NecI Suff28 SuffRed SuffGood SuffStep SuffMain Nec93 CoreTwoLast CoreHyp NecBlock Merge28 Uni93

/-- **A lattice with matrix $A(\alpha, 0) \perp A(\gamma, 0)$ contains a totally isotropic plane** (the vectors $y_1$, $y_2$
of the two blocks), so $FL$ is hyperbolic. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 279 (K₁ ≅ A(a,0) ⊥ A(0,0) is hyperbolic)"]
theorem hasBlk_isotropic_plane {N : Submodule R V} {α γ : F} (h : D18.HasBlk Q N α 0 γ 0) :
    ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (N : Set V)) ∧ finrank R N ≤ 2 * finrank F T := by
  classical
  obtain ⟨e, he⟩ := h
  have hg : ∀ i j, bil Q (e i : V) (e j : V) = D18.blk2 α 0 γ 0 i j := fun i j => by
    rw [← he]; rfl
  have hdet : (gram Q fun i => (e i : V)).det ≠ 0 := by
    rw [he, D18.det_blk2]; simp
  have hli : LinearIndependent F (fun i => (e i : V)) := linearIndependent_of_det_gram_ne_zero (R := F) Q hdet
  have h13 : LinearIndependent F (fun i : Fin 2 => (e (![1, 3] i) : V)) :=
    hli.comp _ (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
  refine ⟨span F (Set.range fun i : Fin 2 => (e (![1, 3] i) : V)), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, q, rfl⟩ : ∃ p q : F, x = p • (e 1 : V) + q • (e 3 : V) := by
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hx
      refine ⟨c 0, c 1, ?_⟩
      rw [← hc]; simp [Fin.sum_univ_two]
    have h11 : Q (e 1 : V) = 0 := by
      have := hg 1 1; rw [bil_self] at this; simpa [D18.blk2] using this
    have h33 : Q (e 3 : V) = 0 := by
      have := hg 3 3; rw [bil_self] at this; simpa [D18.blk2] using this
    have h13' : bil Q (e 1 : V) (e 3 : V) = 0 := by simpa [D18.blk2] using hg 1 3
    rw [Q_add, QuadraticMap.map_smul, QuadraticMap.map_smul, bil_smul_left, bil_smul_right, h11, h33, h13']
    simp
  · intro x hx
    refine (span_le.mpr ?_ : span F (Set.range fun i : Fin 2 => (e (![1, 3] i) : V)) ≤ span F (N : Set V)) hx
    rintro _ ⟨i, rfl⟩
    exact subset_span (e _).2
  · rw [finrank_span_eq_card h13, Fintype.card_fin, finrank_eq_card_basis e, Fintype.card_fin]

/-- **The case $\mathfrak n_1 = 2\mathfrak o$, $\mathfrak n_2 = 4\mathfrak o$** (O'Meara 1963, §93G, proof of 93:29, p. 278: "If
$\mathfrak n_1 = 2\mathfrak o$, then $dL_1/dK_1 \cong 1 \bmod 8\mathfrak o$, hence $dK_1 = dL_1 = 1$"): let $M$, $N$ be
unimodular lattices of rank $4$, $FM$ hyperbolic, $\mathfrak n N = 2\mathfrak o$ and $dM/dN \cong 1 \bmod 8\mathfrak o$. Then
$FN$ is hyperbolic. Proof: $dM = 1$ (block base); $dN = \eta^{-2}$ for a unit $\eta$ ($1 + 8x$ is a square); so $N$ has
a base of discriminant $1$ and 93:18 (vi) (even case, on the subspace $FN$) gives $N \cong A(2, 0) \perp A(0,0)$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = 2o, n₂ = 4o)"]
theorem hyperbolic_residual (hHil : PadicClass.LocalHilbertField F) (h2 : IsTwoAdic R)
    {M N : Submodule R V} (hMfg : M.FG) (hNfg : N.FG) (hMU : IsUnimodular Q M) (hNU : IsUnimodular Q N)
    (hMrk : finrank R M = 4) (hNrk : finrank R N = 4)
    (hT : ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (M : Set V)) ∧ finrank R M ≤ 2 * finrank F T)
    (hnN : normIdeal Q N = R ∙ (2 : F)) (hd : DiscQuotSqEquivMod Q M N (R ∙ (8 : F))) :
    ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (N : Set V)) ∧ finrank R N ≤ 2 * finrank F T := by
  classical
  have hπ := twoAdic_irreducible h2
  have h2p : ¬ IsUnit (2 : R) := hπ.not_isUnit
  have hMreg : IsRegular Q M := IsModular.isRegular Q hMU hMfg
  have hNreg : IsRegular Q N := IsModular.isRegular Q hNU hNfg
  have hsc : scale Q M = 1 := hMU.2.1
  obtain ⟨T, hTiso, hTL, hTdim⟩ := hT
  obtain ⟨B, hMB, hBM, hBfg, hBU, hgB, hrB, mB, xB, hxB⟩ :=
    exists_unimodular_blocks Q hMfg hMreg hsc hTiso hTL hTdim
  have hmB : mB = 2 := by
    have := finrank_of_blockBase Q hxB
    omega
  subst hmB
  have hspanB : span F (B : Set V) = span F (M : Set V) :=
    le_antisymm (span_le.mpr fun b hb => hBM b hb) (span_mono hMB)
  have hiso : IsometricLat Q Q M B :=
    isometricLat_of_normGroup_eq_of_span Q hMfg hBfg hspanB hMU hBU hgB.symm
  obtain ⟨bB, hbB⟩ := exists_basis_det_one_of_blockBase Q hxB
  have h1B := Transfer28.discQuot_of_isometricLat Q Q hiso ⟨LinearEquiv.refl R _, fun x => rfl⟩ hd
  obtain ⟨bK0⟩ := exists_basis (R := R) (F := F) hNfg
  let bK : Basis (Fin 4) R N := bK0.reindex (finCongr hNrk)
  have hdK := Transfer28.det_gram_ne_zero_of_isRegular Q hNreg bK
  have hsq := Transfer28.discQuot_bases Q h1B bB bK hdK
  rw [hbB] at hsq
  obtain ⟨⟨w, hw, hwe⟩, ε, hε, hmem⟩ := hsq
  rw [mul_one] at hwe
  have hdKw : (gram Q fun i => (bK i : V)).det = (algebraMap R F w)⁻¹ := by
    rw [← hwe, one_div, inv_inv]
  obtain ⟨c, hc⟩ := mem_span_singleton.mp hmem
  have hwe' : w = ε ^ 2 + 8 * c := by
    apply IsFractionRing.injective R F
    rw [map_add, map_pow, map_mul, map_ofNat, ← hwe]
    have : (1 : F) / (gram Q fun i => (bK i : V)).det = 1 / (gram Q fun i => (bK i : V)).det - 1 * algebraMap R F ε ^ 2 +
        algebraMap R F ε ^ 2 := by ring
    rw [this, ← hc, Algebra.smul_def]; ring
  -- `w = (ε r)²`
  obtain ⟨εi, hεi⟩ := hε.exists_right_inv
  have h2m : (2 : R) ∈ maximalIdeal R := two_mem_maximal h2
  obtain ⟨r, hr⟩ := isSquare_one_add_four_mul (R := R) (α := 2 * (c * εi ^ 2))
    (Ideal.mul_mem_right _ _ h2m)
  have hwr : w = (ε * r) ^ 2 := by
    have : w = ε ^ 2 * (1 + 4 * (2 * (c * εi ^ 2))) := by
      rw [hwe']; linear_combination (-(8 * c) * (ε * εi + 1)) * hεi
    rw [this, hr]; ring
  have hηu : IsUnit (ε * r) := by
    have : IsUnit ((ε * r) ^ 2) := hwr ▸ hw
    exact (isUnit_pow_iff (by norm_num)).mp this
  obtain ⟨bK', hbK'⟩ := exists_basis_det_scale Q bK hηu
  have hdet1 : (gram Q fun i => (bK' i : V)).det = 1 := by
    rw [hbK', hdKw, hwr, map_pow]
    have : algebraMap R F (ε * r) ≠ 0 := fun h0 =>
      hηu.ne_zero (IsFractionRing.injective R F (h0.trans (map_zero _).symm))
    field_simp
  -- 93:18 (vi) on `FN`
  have hne : N ≠ ⊥ := Uni93.ne_bot_of_isUnimodular Q hNU
  have hset := normGroup_eq_normIdeal_twoAdic Q h2 hNfg hNreg hne
  have hnorm : IsNormGenerator Q N (2 : F) := by
    refine ⟨?_, hnN.symm⟩
    rw [← SetLike.mem_coe, hset, hnN]; exact mem_span_singleton_self _
  have hweight : IsWeightGenerator Q N (2 : F) := by
    unfold IsWeightGenerator
    rw [weight_eq_two_smul_scale_twoAdic Q h2 hNfg hNreg hne, hNU.2.1, Submodule.one_eq_span,
      FIdealAux.smul_span_singleton, mul_one]
  have hev : Even (dord hπ (2 : F) + dord hπ (2 : F)) := ⟨dord hπ (2 : F), rfl⟩
  have hV : finrank F (D18.spanF F N) = 4 := D18.finrank_spanF_of_isUnimodular Q hNfg hNU hNrk
  obtain ⟨-, hblk, -⟩ := D18.omeara93_18_vi_even (D18.subQ Q N) hHil h2p hπ hV (L := D18.subLat F N)
    (D18.fg_subLat N hNfg) ((D18.isUnimodular_subLat Q N).mpr hNU) (by rw [D18.finrank_subLat]; exact hNrk)
    ((D18.isNormGenerator_subLat Q N).mpr hnorm) ((D18.isWeightGenerator_subLat Q N).mpr hweight) hev
    ((D18.exists_det_subLat Q N).mpr ⟨bK', hdet1⟩)
  exact hasBlk_isotropic_plane Q (α := 2) (γ := 0) ((D18.hasBlk_subLat Q N).mp hblk)

/-- Over a 2-adic field the same fundamental invariants give the same Jordan invariants. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (same fundamental invariants = same Jordan invariants)"]
theorem sameJordan_of_sameFund (h2 : IsTwoAdic R) {L K : Submodule R V} (hLfg : L.FG) (hKfg : K.FG) {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} {a : Fin t → F} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q K Ks) (hS : SameFundamentalInvariants Q Q L K Ls Ks a) :
    SameJordanInvariants Q Q Ls Ks := by
  obtain ⟨⟨h0, hT⟩, -, -⟩ := id hS
  refine ⟨h0, fun i => ⟨(hT i).1, (hT i).2.1, ?_⟩⟩
  rw [show Fin.cast h0 i = i from Fin.ext rfl]
  exact (normIdeal_eq_of_sameFund Q h2 hLfg hKfg hL hK hS i).symm

/-- **The final step of the case $\mathfrak n_1 = \mathfrak o$, $\mathfrak n_2 = 4\mathfrak o$** (O'Meara 1963, §93G, p. 278): if
$K_1$ has a base with matrix $A(1, \varepsilon) \perp A(2, \delta)$, $\varepsilon \in 4\mathfrak o$,
$\delta = 0$ or $\delta = 2\rho$ ($X^2 + X + \rho$ without root mod $\mathfrak p$), then $K$ has a saturated splitting
with $FK_1'$ hyperbolic. The first block is moved to $A(1, 0)$ by 93:19 (`exists_shift_first`, $\varepsilon \in
\mathfrak gK_2 = 4\mathfrak o$); if $\delta = 2\rho$, condition (iii) at the first index
gives $FL_1 \to FK_1' \perp \langle a_1\rangle$ with $FK_1' = H \perp F\!A(2, 2\rho)$ and $FL_1$ hyperbolic, which is
impossible (`no_rep_aniso`). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o, with conditions (i), (ii))"]
theorem finish29 (hHil : PadicClass.LocalHilbertField F) (h2 : IsTwoAdic R) (Q : QuadraticForm F V)
    (h2p : ¬ IsUnit (2 : R)) (hQ : (QuadraticMap.associated Q).Nondegenerate) (L K : Submodule R V)
    [hLl : L.IsLattice F] [hKl : K.IsLattice F] (m : ℕ) (Ls Ks : Fin (m + 2) → Submodule R V)
    (a : Fin (m + 2) → F) (hLs : IsSaturated Q L Ls) (hKs : IsSaturated Q K Ks)
    (hd : ∀ k, finrank R (Ls k) = 4)
    (hT : ∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
      finrank R (Ls k) ≤ 2 * finrank F T)
    (hsc : scale Q (Ls 0) = 1) (hDC : DyadicClassification R Q)
    (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hC : Cond29 Q Ls Ks)
    (ha0 : R ∙ a 0 = 1) (ha1 : R ∙ a 1 = R ∙ (4 : F))
    (e : Basis (Fin 4) R (Ks 0)) {ε δ : R} (hε : ∃ c : R, ε = 4 * c)
    (hg : gram Q (fun i => (e i : V)) = D18.blk2 (1 : F) (algebraMap R F ε) (2 : F) (algebraMap R F δ))
    (hδ : δ = 0 ∨ ∃ ρ : R, δ = 2 * ρ ∧ ∀ t : R, t ^ 2 + t + ρ ∉ maximalIdeal R) :
    ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧
      ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ks' 0 : Set V)) ∧
        finrank R (Ks' 0) ≤ 2 * finrank F T := by
  classical
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hKreg : IsRegular Q K := isRegular_of_lattice_max Q hQ hKl
  have hLreg : IsRegular Q L := isRegular_of_lattice_max Q hQ hLl
  have hKle : ∀ k, Ks k ≤ K := fun k => hKs.1.split.iSup_eq ▸ le_iSup Ks k
  have hLle : ∀ k, Ls k ≤ L := fun k => hLs.1.split.iSup_eq ▸ le_iSup Ls k
  obtain ⟨⟨h0, hTy⟩, -, -⟩ := id hS
  have hc0 : ∀ k : Fin (m + 2), Fin.cast h0 k = k := fun k => Fin.ext rfl
  have hs0K : scale Q (Ks 0) = 1 := by
    have := (hTy 0).2.1; rw [hc0] at this; rw [← this]; exact hsc
  have hrk4K : ∀ k, finrank R (Ks k) = 4 := fun k => by
    have := (hTy k).1; rw [hc0] at this; rw [← this]; exact hd k
  have hK1fg : (Ks 1).FG := FG.of_le hKfg (hKle 1)
  have haK : ∀ i, R ∙ a i = normIdeal Q (Ks i) := fun i => by
    rw [(hS.2.2 i).2, ← fundNormIdeal_eq_normIdeal_twoAdic Q h2 hKfg hKs.1 i]; rfl
  have haL : ∀ i, R ∙ a i = normIdeal Q (Ls i) := fun i => by
    rw [(hS.2.1 i).2, ← fundNormIdeal_eq_normIdeal_twoAdic Q h2 hLfg hLs.1 i]; rfl
  obtain ⟨x, y, u, v, hxM, hyM, huM, hvM, hQx, hQy, hxy, hQu, hQv, huv, ⟨hxu, hxv, hyu, hyv⟩, hdecomp⟩ :=
    blk2_facts Q e hg
  obtain ⟨c, hc⟩ := hε
  have hεm : ε ∈ maximalIdeal R := by
    rw [hc]
    exact Ideal.mul_mem_right _ _ (by
      have : (4 : R) = 2 * 2 := by norm_num
      rw [this]; exact Ideal.mul_mem_right _ _ (two_mem_maximal h2))
  have hK0fg : (Ks 0).FG := FG.of_le hKfg (hKle 0)
  have hαβ : IsUnit (ε * 1 - 1 * 1) := by
    have : ε * 1 - 1 * 1 = -(1 - ε) := by ring
    rw [this, IsUnit.neg_iff]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((IsLocalRing.mem_maximalIdeal _).mp hεm)
  have hJmod := D18.span_pair_isModular Q (R := R) (one_ne_zero : (1 : F) ≠ 0) hαβ
    (by rw [hQx, one_mul]) (by rw [hQy, one_mul, map_one]) (by rw [hxy, one_mul, map_one])
  have hJfg : (span R {x, y} : Submodule R V).FG := Submodule.fg_span (Set.toFinite _)
  have hJreg : IsRegular Q (span R {x, y}) := IsModular.isRegular Q hJmod.1 hJfg
  have horthJC : ∀ w ∈ span R {x, y}, ∀ z ∈ span R {u, v}, bil Q w z = 0 := fun w hw z hz =>
    bil_zero_span_pair Q ⟨hxu, hxv, hyu, hyv⟩ hw hz
  have hJC : IsOrthSum Q (Ks 0) (span R {x, y}) (span R {u, v}) :=
    ⟨horthJC, disjoint_of_orth Q hJreg horthJC, hdecomp.symm⟩
  have hrk1 : 3 ≤ finrank R (Ks 1) := by rw [hrk4K]; norm_num
  have hn1 : normIdeal Q (Ks 1) = R ∙ (4 : F) := (haK 1).symm.trans ha1
  have hset := normGroup_eq_normIdeal_twoAdic Q h2 hK1fg ((hKs.1.modular 1).isRegular Q hK1fg)
    (CoreTwo.ne_bot_of_isModular (R := R) Q (hKs.1.modular 1))
  have hγ : algebraMap R F (-ε) ∈ normGroup Q (Ks 1) := by
    rw [← SetLike.mem_coe, hset, hn1]
    refine mem_span_singleton.mpr ⟨-c, ?_⟩
    rw [hc, Algebra.smul_def]; simp only [map_neg, map_mul, map_ofNat]; ring
  have hdet : IsUnit ((ε + -ε) * 1 - 1 * 1) := by simp
  obtain ⟨Ks', hKs'J, hsame, x', y', hQx', hx'y', hQy', hJ'C⟩ :=
    CoreTwo.exists_shift_first Q hHil h2p hKfg hKs.1 hs0K hJC (α := ε) (β := 1) hQx hxy
      (by rw [hQy, map_one]) hεm hrk1 hγ hdet
  have hKs'sat : IsSaturated Q K Ks' := isSaturated_of_twoAdic Q h2 hKfg hKreg hKs'J
  have hQx'0 : Q x' = 0 := by rw [hQx']; simp
  refine ⟨Ks', hKs'sat, ?_⟩
  have hK'0fg : (Ks' 0).FG := FG.of_le hKfg (hKs'J.split.iSup_eq ▸ le_iSup Ks' 0)
  have hK'0reg : IsRegular Q (Ks' 0) := (hKs'J.modular 0).isRegular Q hK'0fg
  have hPK : span R {x', y'} ≤ Ks' 0 := hJ'C.sup_eq ▸ le_sup_left
  have hCK : span R {u, v} ≤ Ks' 0 := hJ'C.sup_eq ▸ le_sup_right
  have hx'K : x' ∈ Ks' 0 := hPK (subset_span (by simp))
  have hy'K : y' ∈ Ks' 0 := hPK (subset_span (by simp))
  have hyx : bil Q y' x' = 1 := by rw [bil_comm]; exact hx'y'
  have hpair : span R {y', x'} = span R {x', y'} := by rw [Set.pair_comm]
  rcases hδ with hδ0 | ⟨ρ, hδρ, hno⟩
  · subst hδ0
    have hQv0 : Q v = 0 := by rw [hQv, map_zero]
    have hb0 : IsBlockBase Q (⊥ : Submodule R V) (Fin.elim0 : Fin 0 → V × V) :=
      ⟨by simp [pairSpan], fun k => k.elim0, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0,
        fun k => k.elim0⟩
    have hC1 := CoreTwo.isBlockBase_cons Q hb0 hQv0 huv
      (by intro w _ z hz; rw [(mem_bot R).1 hz]; simp [bil])
    have horth : ∀ w ∈ span R {y', x'}, ∀ z ∈ span R {u, v} ⊔ ⊥, bil Q w z = 0 := by
      intro w hw z hz
      rw [sup_bot_eq] at hz
      rw [hpair] at hw
      exact hJ'C.orth w hw z hz
    have hJ1 := CoreTwo.isBlockBase_cons Q hC1 hQx'0 hyx horth
    have hset' : span R {y', x'} ⊔ (span R {u, v} ⊔ ⊥) = Ks' 0 := by
      rw [sup_bot_eq, hpair]; exact hJ'C.sup_eq
    rw [hset'] at hJ1
    exact CoreTwo.exists_lagrangian_of_blockBase Q hJ1
  · exfalso
    have hC' := resplit29 Q hHil hDC h2 hQ hLs.1 hKs.1 hKs'J
      (sameJordan_of_sameFund Q h2 hLfg hKfg hLs.1 hKs.1 hS) hC
    have hn0 : normIdeal Q (Ls 0) = 1 := (haL 0).symm.trans ha0
    have hn1L : normIdeal Q (Ls 1) = R ∙ (4 : F) := (haL 1).symm.trans ha1
    have hle : normIdeal Q (Ls 1) ≤ (4 : F) • normIdeal Q (Ls 0) := by
      rw [hn0, hn1L, Submodule.one_eq_span, FIdealAux.smul_span_singleton, mul_one]
    have hrep := (hC' 0 1 (by simp)).2 hle 0 (by rw [zpow_zero, hn0, Submodule.one_eq_span])
    rw [jordanChain_zero Ls 0 rfl, jordanChain_zero Ks' 0 rfl, zpow_zero] at hrep
    have hL0fg : (Ls 0).FG := FG.of_le hLfg (hLle 0)
    have hL0reg : IsRegular Q (Ls 0) := (hLs.1.modular 0).isRegular Q hL0fg
    obtain ⟨T, hT0, hTL, hrk⟩ := hT 0
    have hspan : ∀ k ∈ span F ((Ks' 0 : Submodule R V) : Set V),
        ∃ p q s' r' : F, k = p • x' + q • y' + s' • u + r' • v := by
      have hsup : span F ((Ks' 0 : Submodule R V) : Set V) ≤
          span F {x', y'} ⊔ span F {u, v} := by
        refine span_le.mpr fun z hz => ?_
        rw [← hJ'C.sup_eq] at hz
        obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup.mp hz
        exact add_mem (mem_sup_left (Submodule.span_le_restrictScalars R F _ hp))
          (mem_sup_right (Submodule.span_le_restrictScalars R F _ hq))
      intro k hk
      obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup.mp (hsup hk)
      obtain ⟨a₁, b₁, rfl⟩ := Submodule.mem_span_pair.mp hp
      obtain ⟨c₁, d₁, rfl⟩ := Submodule.mem_span_pair.mp hq
      exact ⟨a₁, b₁, c₁, d₁, by abel⟩
    have hxu' := hJ'C.orth x' (subset_span (by simp)) u (subset_span (by simp))
    have hxv' := hJ'C.orth x' (subset_span (by simp)) v (subset_span (by simp))
    have hyu' := hJ'C.orth y' (subset_span (by simp)) u (subset_span (by simp))
    have hyv' := hJ'C.orth y' (subset_span (by simp)) v (subset_span (by simp))
    refine no_rep_aniso Q h2 hL0fg hL0reg hK'0reg hx'K hy'K hQx'0 hx'y' hQu huv ?_ hxu' hxv' hyu' hyv' hspan hno
      (isUnit_one (M := R)) T hT0 hTL (hd 0) hrk ?_
    · rw [hQv, hδρ, map_mul, map_ofNat]
    · rw [map_one]; exact hrep


/-- **The core of 93:29 over a 2-adic field, case $\mathfrak n_1 = \mathfrak o$, $\mathfrak n_2 = 4\mathfrak o$** (O'Meara
1963, §93G, proof of 93:29, sufficiency, p. 278), with conditions (i), (ii) of 93:29 in place of those of 93:28
(`CoreTwoLast.twoAdicCoreRest4`): here $\mathfrak f_1 = 4\mathfrak o$ is also the modulus $\mathfrak n_1\mathfrak n_2$ of (i), and
(ii) applies since $\mathfrak n_2 = 4\mathfrak o \subseteq 4\mathfrak n_1$ (non-strict reading of (ii)). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o, with conditions (i), (ii))"]
theorem core29_one_four (hHil : PadicClass.LocalHilbertField F) (h2 : IsTwoAdic R) (Q : QuadraticForm F V)
    (h2p : ¬ IsUnit (2 : R)) (hQ : (QuadraticMap.associated Q).Nondegenerate) (L K : Submodule R V)
    [hLl : L.IsLattice F] [hKl : K.IsLattice F] (m : ℕ) (Ls Ks : Fin (m + 2) → Submodule R V)
    (a : Fin (m + 2) → F) (hLs : IsSaturated Q L Ls) (hKs : IsSaturated Q K Ks)
    (hd : ∀ k, finrank R (Ls k) = 4)
    (hT : ∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
      finrank R (Ls k) ≤ 2 * finrank F T)
    (hsc : scale Q (Ls 0) = 1) (hDC : DyadicClassification R Q)
    (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hC : Cond29 Q Ls Ks)
    (ha0 : R ∙ a 0 = 1) (ha1 : R ∙ a 1 = R ∙ (4 : F)) :
    ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧
      ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ks' 0 : Set V)) ∧
        finrank R (Ks' 0) ≤ 2 * finrank F T := by
  classical
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hKreg : IsRegular Q K := isRegular_of_lattice_max Q hQ ‹K.IsLattice F›
  have hLreg : IsRegular Q L := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
  have hKle : ∀ k, Ks k ≤ K := fun k => hKs.1.split.iSup_eq ▸ le_iSup Ks k
  have hLle : ∀ k, Ls k ≤ L := fun k => hLs.1.split.iSup_eq ▸ le_iSup Ls k
  obtain ⟨⟨h0, hTy⟩, -, -⟩ := id hS
  have hc0 : ∀ k : Fin (m + 2), Fin.cast h0 k = k := fun k => Fin.ext rfl
  have hs0K : scale Q (Ks 0) = 1 := by
    have := (hTy 0).2.1; rw [hc0] at this; rw [← this]; exact hsc
  have hrk4K : ∀ k, finrank R (Ks k) = 4 := fun k => by
    have := (hTy k).1; rw [hc0] at this; rw [← this]; exact hd k
  have haK : ∀ i, R ∙ a i = normIdeal Q (Ks i) := fun i => by
    rw [(hS.2.2 i).2, ← fundNormIdeal_eq_normIdeal_twoAdic Q h2 hKfg hKs.1 i]; rfl
  have haL : ∀ i, R ∙ a i = normIdeal Q (Ls i) := fun i => by
    rw [(hS.2.1 i).2, ← fundNormIdeal_eq_normIdeal_twoAdic Q h2 hLfg hLs.1 i]; rfl
  have hK0fg : (Ks 0).FG := FG.of_le hKfg (hKle 0)
  have hK0reg : IsRegular Q (Ks 0) := (hKs.1.modular 0).isRegular Q hK0fg
  have hK0U : IsUnimodular Q (Ks 0) := by have := hKs.1.modular 0; rwa [hs0K] at this
  have hL0fg : (Ls 0).FG := FG.of_le hLfg (hLle 0)
  have hL0reg : IsRegular Q (Ls 0) := (hLs.1.modular 0).isRegular Q hL0fg
  have hLU : IsUnimodular Q (Ls 0) := by have := hLs.1.modular 0; rwa [hsc] at this
  have hn0 : normIdeal Q (Ls 0) = 1 := (haL 0).symm.trans ha0
  have hn1L : normIdeal Q (Ls 1) = R ∙ (4 : F) := (haL 1).symm.trans ha1
  -- `L₁` has a block base: `dL₁ = 1`
  obtain ⟨T, hTiso, hTL, hTdim⟩ := hT 0
  obtain ⟨B, hMB, hBM, hBfg, hBU, hgB, hrB, mB, xB, hxB⟩ :=
    exists_unimodular_blocks Q hL0fg hL0reg hsc hTiso hTL hTdim
  have hmB : mB = 2 := by
    have := finrank_of_blockBase Q hxB
    have := hd 0
    omega
  subst hmB
  have hspanB : span F (B : Set V) = span F (Ls 0 : Set V) :=
    le_antisymm (span_le.mpr fun b hb => hBM b hb) (span_mono hMB)
  have hiso : IsometricLat Q Q (Ls 0) B :=
    isometricLat_of_normGroup_eq_of_span Q hL0fg hBfg hspanB hLU hBU hgB.symm
  obtain ⟨bB, hbB⟩ := exists_basis_det_one_of_blockBase Q hxB
  -- condition (i)
  have h1 := (hC 0 1 (by simp)).1
  have hmod : normIdeal Q (Ls 0) * normIdeal Q (Ls 1) / (scale Q (Ls 0) * scale Q (Ls 0)) = R ∙ (4 : F) := by
    rw [hn0, hn1L, hsc, mul_one, Submodule.one_eq_span]
    exact mul_div_span_cancel (R := R) (one_ne_zero : (1 : F) ≠ 0) _
  rw [jordanChain_zero Ls 0 rfl, jordanChain_zero Ks 0 rfl, hmod] at h1
  have h1B := Transfer28.discQuot_of_isometricLat Q Q hiso ⟨LinearEquiv.refl R _, fun x => rfl⟩ h1
  obtain ⟨bK0⟩ := exists_basis (R := R) (F := F) hK0fg
  let bK : Basis (Fin 4) R (Ks 0) := bK0.reindex (finCongr (hrk4K 0))
  have hdK := Transfer28.det_gram_ne_zero_of_isRegular Q hK0reg bK
  have hsq := Transfer28.discQuot_bases Q h1B bB bK hdK
  rw [hbB] at hsq
  obtain ⟨⟨w, hw, hwe⟩, ε, hε, hmem⟩ := hsq
  rw [mul_one] at hwe
  have hdKw : (gram Q fun i => (bK i : V)).det = (algebraMap R F w)⁻¹ := by
    rw [← hwe, one_div, inv_inv]
  obtain ⟨c, hc⟩ := mem_span_singleton.mp hmem
  have hwe' : w = ε ^ 2 + 4 * c := by
    apply IsFractionRing.injective R F
    rw [map_add, map_pow, map_mul, map_ofNat, ← hwe]
    have : (1 : F) / (gram Q fun i => (bK i : V)).det = 1 / (gram Q fun i => (bK i : V)).det - 1 * algebraMap R F ε ^ 2 +
        algebraMap R F ε ^ 2 := by ring
    rw [this, ← hc, Algebra.smul_def]; ring
  obtain ⟨α, ⟨c', hc'⟩, ⟨b', hb'⟩, hdef⟩ := exists_alpha Q h2 bK hw hε hwe' hdKw
  -- 93:18 (iii)
  have hπ := twoAdic_irreducible h2
  have h2R : (2 : R) ≠ 0 := hπ.ne_zero
  have hn0K : normIdeal Q (Ks 0) = 1 := (haK 0).symm.trans ha0
  have hne0 : Ks 0 ≠ ⊥ := CoreTwo.ne_bot_of_isModular (R := R) Q (hKs.1.modular 0)
  have hset := normGroup_eq_normIdeal_twoAdic Q h2 hK0fg hK0reg hne0
  have hnorm : IsNormGenerator Q (Ks 0) (1 : F) := by
    refine ⟨?_, ?_⟩
    · rw [← SetLike.mem_coe, hset, hn0K]; exact ⟨1, by simp⟩
    · rw [hn0K, Submodule.one_eq_span]
  have hweight : IsWeightGenerator Q (Ks 0) (2 : F) := by
    unfold IsWeightGenerator
    rw [weight_eq_two_smul_scale_twoAdic Q h2 hK0fg hK0reg hne0, hs0K, Submodule.one_eq_span,
      FIdealAux.smul_span_singleton, mul_one]
  have hodd : Odd (dord hπ (1 : F) + dord hπ (2 : F)) := by
    have h1' : dord hπ (1 : F) = 0 := by simpa using dord_unit (F := F) hπ (u := (1 : R)) isUnit_one
    rw [h1', twoAdic_dord_two h2]; exact ⟨0, by norm_num⟩
  obtain ⟨ρ, -, hρ⟩ := G93.exists_delta (F := F) h2R h2p hπ
  obtain ⟨-, hX⟩ := D18.omeara93_18_iii_sub Q hHil h2p hπ hK0fg hK0U (hrk4K 0) hnorm hweight hodd ⟨b', hb'⟩ hdef hρ
  rcases hX with ⟨⟨e, he⟩, -⟩ | ⟨⟨e, he⟩, -⟩
  · refine finish29 hHil h2 Q h2p hQ L K m Ls Ks a hLs hKs hd hT hsc hDC hS hC ha0 ha1 e (ε := -α) (δ := 0)
      ⟨-c', by rw [hc']; ring⟩ ?_ (Or.inl rfl)
    rw [he, map_neg, map_zero, div_one]
  · refine finish29 hHil h2 Q h2p hQ L K m Ls Ks a hLs hKs hd hT hsc hDC hS hC ha0 ha1 e (ε := -(α - 4 * ρ)) (δ := 2 * ρ)
      ⟨ρ - c', by rw [hc']; ring⟩ ?_ (Or.inr ⟨ρ, rfl, no_root_of_defect h2 hρ⟩)
    rw [he]
    have h2F : (2 : F) ≠ 0 := two_ne_zero' F
    simp only [map_neg, map_sub, map_mul, map_ofNat, div_one]
    congr 2
    field_simp
    ring


/-- The modulus of condition (i) of 93:29 for unimodular $L_1$ and norms $x\mathfrak o$, $y\mathfrak o$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the modulus n₁n₂ of condition (i))"]
theorem modulus_eq {A B : Submodule R F} {x y : F} (_hx : x ≠ 0) (hA : A = R ∙ x) (hB : B = R ∙ y)
    {S : Submodule R F} (hS : S = 1) : A * B / (S * S) = R ∙ (x * y) := by
  rw [hA, hB, hS, mul_one, Submodule.one_eq_span, FIdealAux.span_mul_span']
  have h := mul_div_span_cancel (R := R) (one_ne_zero : (1 : F) ≠ 0) (R ∙ (x * y))
  rwa [FIdealAux.span_mul_span', one_mul] at h

omit [Invertible (2 : F)] in
/-- $2 \in 2^k\mathfrak o \iff k \le 1$ over a 2-adic field. -/
theorem two_mem_span_iff (h2 : IsTwoAdic R) (k : ℤ) : (2 : F) ∈ R ∙ ((2 : F) ^ k) ↔ k ≤ 1 := by
  rw [mem_span_two_zpow_iff h2 (two_ne_zero' F), twoAdic_dord_two h2]

/-- **The core of 93:29 over a 2-adic field** (O'Meara 1963, §93G, proof of 93:29, sufficiency, pp. 278–279), with
conditions (i), (ii) of 93:29: for saturated splittings in dimension $4$ with hyperbolic $FL_k$ and unimodular $L_1$,
$K$ has a saturated splitting with $FK_1'$ hyperbolic. Cases (by $u_i = \operatorname{ord}\mathfrak n_i$,
$u_1 \in \{0, 1\}$): $\mathfrak n_2 \ni 2$ (`CoreTwo.core_twoAdic_two`); $\mathfrak n_2 = 4\mathfrak o$, $\mathfrak n_1 = \mathfrak o$
(`core29_one_four`); $\mathfrak n_2 = 4\mathfrak o$, $\mathfrak n_1 = 2\mathfrak o$ (`hyperbolic_residual`); $\mathfrak n_2
\subseteq 8\mathfrak o$ (then $\mathfrak n_2 \subseteq 8\mathfrak o \subseteq 4\mathfrak n_1$ and (i), (ii) give $FL_1 \cong FK_1$,
`CoreCases.exists_lagrangian_of_cond`). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 278–279 (the core, all cases)"]
theorem core29 (hHil : PadicClass.LocalHilbertField F) (h2 : IsTwoAdic R) (Q : QuadraticForm F V)
    (h2p : ¬ IsUnit (2 : R)) (hQ : (QuadraticMap.associated Q).Nondegenerate) (L K : Submodule R V)
    [hLl : L.IsLattice F] [hKl : K.IsLattice F] (m : ℕ) (Ls Ks : Fin (m + 2) → Submodule R V)
    (a : Fin (m + 2) → F) (hLs : IsSaturated Q L Ls) (hKs : IsSaturated Q K Ks)
    (hd : ∀ k, finrank R (Ls k) = 4)
    (hT : ∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
      finrank R (Ls k) ≤ 2 * finrank F T)
    (hsc : scale Q (Ls 0) = 1) (hDC : DyadicClassification R Q)
    (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hC : Cond29 Q Ls Ks) :
    ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧
      ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ks' 0 : Set V)) ∧
        finrank R (Ks' 0) ≤ 2 * finrank F T := by
  classical
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hKreg : IsRegular Q K := isRegular_of_lattice_max Q hQ ‹K.IsLattice F›
  have hLreg : IsRegular Q L := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
  have hKle : ∀ k, Ks k ≤ K := fun k => hKs.1.split.iSup_eq ▸ le_iSup Ks k
  have hLle : ∀ k, Ls k ≤ L := fun k => hLs.1.split.iSup_eq ▸ le_iSup Ls k
  obtain ⟨⟨h0, hTy⟩, -, -⟩ := id hS
  have hc0 : ∀ k : Fin (m + 2), Fin.cast h0 k = k := fun k => Fin.ext rfl
  have hs0K : scale Q (Ks 0) = 1 := by
    have := (hTy 0).2.1; rw [hc0] at this; rw [← this]; exact hsc
  have hrk4K : ∀ k, finrank R (Ks k) = 4 := fun k => by
    have := (hTy k).1; rw [hc0] at this; rw [← this]; exact hd k
  have haL : ∀ i, R ∙ a i = normIdeal Q (Ls i) := fun i => by
    rw [(hS.2.1 i).2, ← fundNormIdeal_eq_normIdeal_twoAdic Q h2 hLfg hLs.1 i]; rfl
  obtain ⟨u, hu⟩ : ∃ u : Fin (m + 2) → ℤ, ∀ k, R ∙ ((2 : F) ^ u k) = normIdeal Q (Ls k) :=
    ⟨fun k => (exists_two_pow_eq Q h2 hLfg hLs.1 k).choose,
      fun k => (exists_two_pow_eq Q h2 hLfg hLs.1 k).choose_spec⟩
  have z2 : ∀ w : ℤ, (2 : F) ^ w ≠ 0 := fun w => two_zpow_ne_zero w
  have hK0fg : (Ks 0).FG := FG.of_le hKfg (hKle 0)
  have hL0fg : (Ls 0).FG := FG.of_le hLfg (hLle 0)
  have hK0reg : IsRegular Q (Ks 0) := (hKs.1.modular 0).isRegular Q hK0fg
  have hL0reg : IsRegular Q (Ls 0) := (hLs.1.modular 0).isRegular Q hL0fg
  -- `u 0 ∈ {0, 1}`
  have hu0a : 0 ≤ u 0 := by
    have h : (2 : F) ^ (u 0) ∈ R ∙ ((2 : F) ^ (0 : ℤ)) := by
      rw [zpow_zero, ← Submodule.one_eq_span, ← hsc]
      exact normIdeal_le_scale Q (Ls 0) (by rw [← hu 0]; exact mem_span_singleton_self _)
    rwa [mem_span_two_zpow_iff h2 (z2 _), dord_two_zpow h2] at h
  have hu0b : u 0 ≤ 1 := by
    have h1 : (1 : F) ∈ scale Q (Ls 0) := by rw [hsc]; exact Submodule.one_le.mp le_rfl
    have h := two_mul_mem_normIdeal Q h1
    rw [mul_one, ← hu 0] at h
    exact (two_mem_span_iff h2 _).1 h
  have hmod := modulus_eq (R := R) (z2 (u 0)) (hu 0).symm (hu 1).symm hsc
  have hd1 := (hC 0 1 (by simp)).1
  rw [jordanChain_zero Ls 0 rfl, jordanChain_zero Ks 0 rfl, hmod] at hd1
  by_cases h1 : u 1 ≤ 1
  · refine CoreTwo.core_twoAdic_two hHil h2 Q h2p hQ L K m Ls Ks a hLs hKs (fun k => (hd k).symm ▸ by norm_num) hT hsc hS ?_
    rw [haL 1, ← hu 1]; exact (two_mem_span_iff h2 _).2 h1
  by_cases h2' : u 1 = 2
  · by_cases hz : u 0 = 0
    · refine core29_one_four hHil h2 Q h2p hQ L K m Ls Ks a hLs hKs hd hT hsc hDC hS hC ?_ ?_
      · rw [haL 0, ← hu 0, hz, zpow_zero, ← Submodule.one_eq_span]
      · rw [haL 1, ← hu 1, h2']; norm_num
    · have hz1 : u 0 = 1 := by omega
      have hMU : IsUnimodular Q (Ls 0) := by have := hLs.1.modular 0; rwa [hsc] at this
      have hNU : IsUnimodular Q (Ks 0) := by have := hKs.1.modular 0; rwa [hs0K] at this
      have hnN : normIdeal Q (Ks 0) = R ∙ (2 : F) := by
        rw [normIdeal_eq_of_sameFund Q h2 hLfg hKfg hLs.1 hKs.1 hS 0, ← hu 0, hz1, zpow_one]
      have e : (2 : F) ^ (u 0) * (2 : F) ^ (u 1) = 8 := by rw [hz1, h2']; norm_num
      rw [e] at hd1
      exact ⟨Ks, hKs, hyperbolic_residual Q hHil h2 hL0fg hK0fg hMU hNU (hd 0) (hrk4K 0) (hT 0) hnN hd1⟩
  · have h3 : 3 ≤ u 1 := by omega
    have hprod : (2 : F) ^ (u 0) * (2 : F) ^ (u 1) = (2 : F) ^ (u 0 + u 1) := (zpow_add₀ (two_ne_zero' F) _ _).symm
    have hX : ∀ x ∈ R ∙ ((2 : F) ^ (u 0) * (2 : F) ^ (u 1)),
        ∃ μ ∈ maximalIdeal R, x = 4 * algebraMap R F μ := by
      intro x hx
      by_cases hx0 : x = 0
      · exact ⟨0, zero_mem _, by simp [hx0]⟩
      rw [hprod, mem_span_two_zpow_iff h2 hx0] at hx
      have h8 : x ∈ R ∙ ((2 : F) ^ (3 : ℤ)) := (mem_span_two_zpow_iff h2 hx0 3).2 (by omega)
      rw [show ((2 : F) ^ (3 : ℤ)) = 8 by norm_num] at h8
      obtain ⟨r, rfl⟩ := mem_span_singleton.mp h8
      refine ⟨2 * r, Ideal.mul_mem_right _ _ (two_mem_maximal h2), ?_⟩
      rw [Algebra.smul_def, map_mul, map_ofNat]; ring
    have hle : normIdeal Q (Ls 1) ≤ (4 : F) • normIdeal Q (Ls 0) := by
      rw [← hu 0, ← hu 1, FIdealAux.smul_span_singleton, four_mul_two_zpow, Submodule.span_singleton_le_iff_mem,
        mem_span_two_zpow_iff h2 (z2 _), dord_two_zpow h2]
      omega
    have hrep := (hC 0 1 (by simp)).2 hle (u 0) (hu 0)
    rw [jordanChain_zero Ls 0 rfl, jordanChain_zero Ks 0 rfl] at hrep
    exact ⟨Ks, hKs, CoreCases.exists_lagrangian_of_cond Q hL0fg hK0fg hL0reg hK0reg
      (by rw [hd 0, hrk4K 0]) hX hd1 (z2 _) hrep (hT 0)⟩

end Residual

end QuadFormsKB.OMeara.G29
