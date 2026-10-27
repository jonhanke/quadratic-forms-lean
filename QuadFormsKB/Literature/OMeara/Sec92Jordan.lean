/-
# O'Meara §92: classification of lattices over non-dyadic local fields (Theorem 92:2)

**Setting** (as in `Sec92.lean`): $R$ a complete discrete valuation ring with finite residue field, $2$ a unit of
$R$ (non-dyadic), fraction field $F$, a quadratic space $(V, Q)$ over $F$, lattices = `Submodule R V`.

**Proves**
* `cls_eq_of_mem`: classes partition the lattices on $V$ (§82C, p. 222);
* `IsometricLat.isModular`, `isJordanSplitting_latMap`: isometries carry modular lattices and Jordan splittings to
  modular lattices and Jordan splittings;
* `isometricLat_of_isOrthSplit`: componentwise isometric orthogonal splittings give isometric lattices (§82D);
* `sameDisc_of_isJordanSplitting` (step 1 of the proof of 92:2, pp. 247–248): corresponding components of two Jordan
  splittings of the same lattice have the same discriminant in $F/\mathfrak u^2$;
* `cls_eq_iff_sameDisc` (**Theorem 92:2**, p. 247): lattices $L$, $K$ of the same Jordan type on $V$, with Jordan
  splittings $L = L_1 \perp \cdots \perp L_t$, $K = K_1 \perp \cdots \perp K_t$, are in the same class if and only if
  $dL_i = dK_i$ for $1 \le i \le t$.
-/
import QuadFormsKB.Literature.OMeara.Sec92Class

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Field

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

theorem latMap_mul (σ τ : V ≃ₗ[F] V) (L : Submodule R V) : latMap (σ * τ) L = latMap σ (latMap τ L) := by
  simp only [latMap]
  rw [← Submodule.map_comp]
  rfl

theorem latMap_one (L : Submodule R V) : latMap (1 : V ≃ₗ[F] V) L = L := by
  ext x; simp [latMap]

theorem mem_cls_self (L : Submodule R V) : L ∈ cls Q L := ⟨1, (orth Q).one_mem, (latMap_one L).symm⟩

/-- **Classes partition the lattices** (O'Meara 1963, §82C, p. 222): if $K \in \operatorname{cls} L$ then
$\operatorname{cls} K = \operatorname{cls} L$. -/
theorem cls_eq_of_mem {L K : Submodule R V} (h : K ∈ cls Q L) : cls Q K = cls Q L := by
  obtain ⟨σ, hσ, rfl⟩ := h
  ext J
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨τ * σ, (orth Q).mul_mem hτ hσ, (latMap_mul τ σ L).symm⟩
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨τ * σ⁻¹, (orth Q).mul_mem hτ ((orth Q).inv_mem hσ), ?_⟩
    rw [latMap_mul, ← latMap_mul σ⁻¹ σ, inv_mul_cancel, latMap_one]

/-- An isometry of $V$ preserves $B$. -/
theorem bil_orth {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (x y : V) : bil Q (σ x) (σ y) = bil Q x y := by
  rw [bil_eq_half, bil_eq_half, ← map_add, hσ, hσ, hσ]

/-- $\sigma J \cong J$ for $\sigma \in O(V)$. -/
theorem isometricLat_latMap {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (J : Submodule R V) :
    IsometricLat Q Q J (latMap σ J) :=
  ⟨Submodule.equivMapOfInjective ((σ : V →ₗ[F] V).restrictScalars R) σ.injective J, fun x => hσ x⟩

end Field

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- **Isometric lattices have the same scale.** -/
theorem IsometricLat.scale_eq {J : Submodule R V} {K : Submodule R V'} (h : IsometricLat Q Q' J K)
    (hJ : J.FG) : scale Q' K = scale Q J := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨b⟩ := exists_basis (R := R) (F := F) hJ
  let b' := b.map f
  rw [← span_basis_eq b, ← span_basis_eq b', scale_span, scale_span]
  congr 1
  ext c
  simp only [Set.mem_range, b', Basis.map_apply]
  constructor
  · rintro ⟨p, rfl⟩; exact ⟨p, (bil_eq_of_isometricLat Q Q' f hf _ _).symm⟩
  · rintro ⟨p, rfl⟩; exact ⟨p, bil_eq_of_isometricLat Q Q' f hf _ _⟩

/-- **Isometric lattices are modular together.** -/
theorem IsometricLat.isModular {a : Submodule R F} {J : Submodule R V} {K : Submodule R V'}
    (h : IsometricLat Q Q' J K) (hJ : J.FG) (hmod : IsModular Q a J) : IsModular Q' a K := by
  obtain ⟨α, hα, rfl, b, U, hU, hG⟩ := exists_gram_of_isModular Q hmod hJ
  obtain ⟨f, hf⟩ := h
  have hne : Nonempty (Fin (finrank R J)) := by
    rcases (isModular_iff_gram Q b hα).mp hmod with ⟨hn, -⟩; exact hn
  refine (isModular_iff_gram Q' (b.map f) hα).mpr ⟨hne, U, hU, ?_⟩
  rw [← hG]
  ext i j
  simp only [gram, Matrix.of_apply, Basis.map_apply]
  exact bil_eq_of_isometricLat Q Q' f hf _ _

/-- **Isometries carry Jordan splittings to Jordan splittings** (O'Meara 1963, §91C, p. 245: isometric lattices are
of the same Jordan type). -/
theorem isJordanSplitting_latMap {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) {L : Submodule R V} (hfg : L.FG)
    {t : ℕ} {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) :
    IsJordanSplitting Q (latMap σ L) (fun i => latMap σ (Ls i)) := by
  have hfgi : ∀ i, (Ls i).FG := fun i => FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls i)
  have hsc : ∀ i, scale Q (latMap σ (Ls i)) = scale Q (Ls i) :=
    fun i => (isometricLat_latMap Q hσ (Ls i)).scale_eq Q Q (hfgi i)
  have hmod : ∀ i, IsModular Q (scale Q (latMap σ (Ls i))) (latMap σ (Ls i)) := by
    intro i; rw [hsc]; exact (isometricLat_latMap Q hσ (Ls i)).isModular Q Q (hfgi i) (hL.modular i)
  have horth : ∀ i j, i ≠ j → ∀ x ∈ latMap σ (Ls i), ∀ y ∈ latMap σ (Ls j), bil Q x y = 0 := by
    rintro i j hij _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [bil_orth Q hσ]; exact hL.split.orth i j hij x hx y hy
  refine ⟨⟨horth, iSupIndep_of_orth Q horth fun i => (hmod i).isRegular Q ?_, ?_⟩, hmod, ?_⟩
  · exact (hfgi i).map _
  · rw [← hL.split.iSup_eq, latMap, Submodule.map_iSup]
  · intro i j hij; simp only [hsc]; exact hL.scale_strictAnti hij

/-- **Gluing isometries of components** (O'Meara 1963, §82D, p. 224): if $L = L_1 \perp \cdots \perp L_t$ and
$K = K_1 \perp \cdots \perp K_t$ with $L_i \cong K_i$ for all $i$, then $L \cong K$. -/
theorem isometricLat_of_isOrthSplit {t : ℕ} {L : Submodule R V} {K : Submodule R V'}
    {Ls : Fin t → Submodule R V} {Ks : Fin t → Submodule R V'} (hL : IsOrthSplit Q L Ls)
    (hK : IsOrthSplit Q' K Ks) (hfg : ∀ i, (Ls i).FG) (h : ∀ i, IsometricLat Q Q' (Ls i) (Ks i)) :
    IsometricLat Q Q' L K := by
  choose f hf using h
  have hb := fun i => exists_basis (R := R) (F := F) (hfg i)
  let b : ∀ i, Basis (Fin (finrank R (Ls i))) R (Ls i) := fun i => (hb i).some
  let x : (Σ i, Fin (finrank R (Ls i))) → V := fun p => (b p.1 p.2 : V)
  let x' : (Σ i, Fin (finrank R (Ls i))) → V' := fun p => (f p.1 (b p.1 p.2) : V')
  have hspanx : ∀ i, span R (Set.range fun k => (b i k : V)) = Ls i := fun i => span_basis_eq (b i)
  have hspanx' : ∀ i, span R (Set.range fun k => (f i (b i k) : V')) = Ks i :=
    fun i => span_basis_eq ((b i).map (f i))
  have hli : LinearIndependent R x := by
    refine linearIndependent_iUnion_finite (f := fun i k => (b i k : V)) (fun i => ?_) ?_
    · exact (b i).linearIndependent.map' (Ls i).subtype (ker_subtype _)
    · intro i s _ his
      show Disjoint (span R (Set.range fun k => (b i k : V)))
        (⨆ j ∈ s, span R (Set.range fun k => (b j k : V)))
      simp only [hspanx]
      exact hL.indep.disjoint_biSup his
  have hli' : LinearIndependent R x' := by
    refine linearIndependent_iUnion_finite (f := fun i k => (f i (b i k) : V')) (fun i => ?_) ?_
    · exact ((b i).map (f i)).linearIndependent.map' (Ks i).subtype (ker_subtype _)
    · intro i s _ his
      show Disjoint (span R (Set.range fun k => (f i (b i k) : V')))
        (⨆ j ∈ s, span R (Set.range fun k => (f j (b j k) : V')))
      simp only [hspanx']
      exact hK.indep.disjoint_biSup his
  have hsx : span R (Set.range x) = L := by
    rw [Set.range_sigma_eq_iUnion_range, span_iUnion]
    have e : ∀ i, span R (Set.range fun k => x ⟨i, k⟩) = Ls i := hspanx
    simp only [e]; exact hL.iSup_eq
  have hsx' : span R (Set.range x') = K := by
    rw [Set.range_sigma_eq_iUnion_range, span_iUnion]
    have e : ∀ i, span R (Set.range fun k => x' ⟨i, k⟩) = Ks i := hspanx'
    simp only [e]; exact hK.iSup_eq
  let B := (Basis.span hli).map (LinearEquiv.ofEq _ _ hsx)
  let B' := (Basis.span hli').map (LinearEquiv.ofEq _ _ hsx')
  refine isometricLat_of_gram_eq Q Q' B B' ?_
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [gram, Matrix.of_apply, B, B', Basis.map_apply, Basis.span_apply, LinearEquiv.coe_ofEq_apply,
    x, x']
  by_cases hij : i = j
  · subst hij; exact (bil_eq_of_isometricLat Q Q' (f i) (hf i) _ _).symm
  · rw [hL.orth i j hij _ (b i k).2 _ (b j l).2, hK.orth i j hij _ (f i (b i k)).2 _ (f j (b j l)).2]

/-- `SameDisc` is transitive. -/
theorem SameDisc.trans {V'' : Type*} [AddCommGroup V''] [Module F V''] [Module R V''] [IsScalarTower R F V'']
    {Q'' : QuadraticForm F V''} {L : Submodule R V} {J : Submodule R V'} {K : Submodule R V''}
    (h₁ : SameDisc Q Q' L J) (h₂ : SameDisc Q' Q'' J K) : SameDisc Q Q'' L K := by
  obtain ⟨b, c, ε, hε, h1⟩ := h₁
  have h₂' := h₂
  obtain ⟨_, e, _, _, _⟩ := h₂'
  obtain ⟨δ, hδ, h2⟩ := SameDisc.forall Q' Q'' h₂ c e
  exact ⟨b, e, ε * δ, hε.mul hδ, by rw [h1, h2]; simp only [map_mul]; ring⟩

/-- O'Meara's projection $\varphi$ (proof of 91:9, step 2, and of 92:2, step 1, pp. 244–247): if $M_1 \subseteq M$
has a base $b$ with matrix $\alpha U$ and $M = N_1 \perp N'$ with $\mathfrak sN' \subsetneq \alpha\mathfrak o$, the
$N_1$-components $y_i$ of the $b_i$ have matrix $\alpha(U - m)$ with $m$ an integral matrix with entries in
$\mathfrak p$. -/
theorem exists_family_of_isOrthSum {α : F} {M M₁ N₁ N' : Submodule R V} (hM₁M : M₁ ≤ M)
    (hN : IsOrthSum Q M N₁ N') (hαN' : α ∉ scale Q N') {ι : Type*} [Fintype ι] (b : Basis ι R M₁)
    {U : Matrix ι ι R} (hG : gram Q (fun i => (b i : V)) = α • U.map (algebraMap R F)) :
    ∃ y : ι → V, (∀ i, y i ∈ N₁) ∧ ∃ m : Matrix ι ι R, (∀ i j, m i j ∈ maximalIdeal R) ∧
      gram Q y = α • (U - m).map (algebraMap R F) := by
  have hsmall : ∀ c ∈ scale Q N', ∃ m ∈ maximalIdeal R, c = algebraMap R F m * α :=
    fun c hc => exists_maximalIdeal_mul_of_mem_of_notMem (R := R) hc hαN'
  have hdec : ∀ x ∈ M, ∃ y ∈ N₁, ∃ z ∈ N', x = y + z := by
    intro x hx
    rw [← hN.sup_eq] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hx
    exact ⟨y, hy, z, hz, rfl⟩
  have horth' : ∀ z ∈ N', ∀ y ∈ N₁, bil Q z y = 0 := fun z hz y hy => by
    rw [bil_comm]; exact hN.orth y hy z hz
  choose y hy z hz hyz using fun i => hdec (b i) (hM₁M (b i).2)
  have hentry : ∀ i j, ∃ m ∈ maximalIdeal R, bil Q (y i) (y j) = α * algebraMap R F (U i j - m) := by
    intro i j
    have h1 : bil Q (y i) (y j) = bil Q (b i : V) (b j : V) - bil Q (z i) (z j) := by
      rw [hyz i, hyz j, bil_add_left, bil_add_right, bil_add_right,
        hN.orth _ (hy i) _ (hz j), horth' _ (hz i) _ (hy j)]
      ring
    obtain ⟨m, hm, hm'⟩ := hsmall _ (bil_mem_scale Q (hz i) (hz j))
    refine ⟨m, hm, ?_⟩
    have hGij : bil Q (b i : V) (b j : V) = α * algebraMap R F (U i j) := by
      simpa [gram] using congrFun (congrFun hG i) j
    rw [h1, hGij, hm', map_sub]; ring
  choose m hm hm' using hentry
  refine ⟨y, hy, Matrix.of m, hm, ?_⟩
  ext i j
  simp only [gram, Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.sub_apply]
  exact hm' i j

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Perturbing an invertible matrix by entries in $\mathfrak p$ keeps the determinant modulo $\mathfrak p$. -/
theorem residue_det_sub [IsLocalRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] (U m : Matrix ι ι R)
    (hm : ∀ i j, m i j ∈ maximalIdeal R) : residue R (U - m).det = residue R U.det := by
  have hres : (residue R).mapMatrix (U - m) = (residue R).mapMatrix U := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, map_sub,
      (residue_eq_zero_iff _).mpr (hm i j), sub_zero]
  rw [RingHom.map_det, RingHom.map_det, hres]

omit [Invertible (2 : F)] in
theorem isUnit_det_sub {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Matrix ι ι R} (hU : IsUnit U.det)
    {m : Matrix ι ι R} (hm : ∀ i j, m i j ∈ maximalIdeal R) : IsUnit (U - m).det := by
  by_contra hcon
  have h2 : residue R U.det = 0 := by
    rw [← residue_det_sub U m hm]; exact (residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hcon)
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h2
  exact h2 hU

/-- **A modular sublattice of full rank is everything**: if $J \subseteq N$ are $\mathfrak a$-modular of the same rank
then $J = N$ (by 82:15a, $N = J \perp K$ with $K$ of rank $0$). -/
theorem eq_of_isModular_of_le {a : Submodule R F} {J N : Submodule R V} (hJN : J ≤ N) (hJ : IsModular Q a J)
    (hN : IsModular Q a N) (hJfg : J.FG) (hNfg : N.FG) (hrk : finrank R J = finrank R N) : J = N := by
  obtain ⟨K, hK⟩ := splits_of_isModular_of_scale_eq Q hJN hJ hJfg hN.2.1
  have hr := isOrthSum_finrank Q hK hNfg
  have hK0 : finrank R K = 0 := by omega
  have hKfg : K.FG := FG.of_le hNfg (hK.sup_eq ▸ le_sup_right)
  obtain ⟨bK⟩ := exists_basis (R := R) (F := F) hKfg
  have : K = ⊥ := by
    rw [← span_basis_eq bK, span_eq_bot]
    rintro _ ⟨k, rfl⟩; exact Fin.elim0 (hK0 ▸ k)
  rw [← hK.sup_eq, this, sup_bot_eq]

end DVR

section LocalNonDyadic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (ResidueField R)] [DecidableEq (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

omit [Invertible (2 : F)] in
include F in
/-- Over a complete non-dyadic discrete valuation ring with finite residue field, a unit $\equiv 1 \bmod \mathfrak p$
is the square of a unit (Local Square Theorem, O'Meara 1963, 63:1, p. 159). -/
theorem exists_unit_sq_of_residue_eq_one (h2 : IsUnit (2 : R)) {w : R} (hw : residue R w = 1) :
    ∃ z : R, IsUnit z ∧ z ^ 2 = w := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have h2' : ¬ π ∣ 2 := fun h => hπ.not_isUnit (isUnit_of_dvd_unit h h2)
  obtain ⟨z, hz⟩ := Lattices.Nbr.exists_sq_eq_of_residue hπ h2' w one_ne_zero (by rw [hw, one_pow])
  refine ⟨z, ?_, hz⟩
  have hwu : IsUnit w := by
    by_contra h
    have := (residue_eq_zero_iff w).mpr ((mem_maximalIdeal _).mpr h)
    rw [hw] at this; exact one_ne_zero this
  rw [← hz] at hwu
  exact (isUnit_pow_iff two_ne_zero).mp hwu

/-- **Step 1 of the proof of Theorem 92:2** (O'Meara 1963, pp. 247–248): over a non-dyadic local field,
corresponding components of two Jordan splittings $M = L_1 \perp \cdots \perp L_t = K_1 \perp \cdots \perp K_t$ of the
same lattice have the same discriminant: $dL_i = dK_i$ in $F/\mathfrak u^2$. *Proof:* O'Meara's projection
$\varphi$ maps a base of $L_i$ to a base of $K_i$ whose matrix is congruent to that of $L_i$ modulo
$\alpha\mathfrak p$, so the discriminants differ by a unit $\equiv 1 \bmod \mathfrak p$, a square. -/
@[kb "omeara1963" "§92, proof of 92:2, step 1, pp. 247–248"]
theorem sameDisc_of_isJordanSplitting (h2 : IsUnit (2 : R)) {M : Submodule R V} (hfg : M.FG) {t t' : ℕ}
    {Ls : Fin t → Submodule R V} {Ks : Fin t' → Submodule R V} (hL : IsJordanSplitting Q M Ls)
    (hK : IsJordanSplitting Q M Ks) (i : Fin t) (j : Fin t') (hij : (i : ℕ) = j) :
    SameDisc Q Q (Ls i) (Ks j) := by
  obtain ⟨htt, hall⟩ := hL.sameJordanType Q hfg hK
  have hj : j = Fin.cast htt i := Fin.ext (by simp [hij])
  subst hj
  obtain ⟨hsc, hrk, -⟩ := hall i
  have hfgi : (Ls i).FG := FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls i)
  have hfgj : (Ks (Fin.cast htt i)).FG := FG.of_le hfg (hK.split.iSup_eq ▸ le_iSup Ks _)
  obtain ⟨α, hα, haα, b, U, hU, hG⟩ := exists_gram_of_isModular Q (hL.modular i) hfgi
  obtain ⟨hMi, -⟩ := isOrthSum_subA Q hfg hL i
  obtain ⟨hNj, hNj'⟩ := isOrthSum_subA Q hfg hK (Fin.cast htt i)
  rw [← hsc] at hNj hNj'
  have hLiM : Ls i ≤ subA Q (scale Q (Ls i)) M := hMi.sup_eq ▸ le_sup_left
  have hαN' : α ∉ scale Q (⨆ k : {k // k ≠ Fin.cast htt i}, subA Q (scale Q (Ls i)) (Ks k)) :=
    fun h => hNj' (haα.trans_le ((span_singleton_le_iff_mem _ _).mpr h))
  obtain ⟨y, hy, m, hm, hGy⟩ := exists_family_of_isOrthSum Q hLiM hNj hαN' b hG
  have hU' := isUnit_det_sub hU hm
  have hpos := finrank_pos_of_isModular Q hfgi (hL.modular i)
  have : Nonempty (Fin (finrank R (Ls i))) := ⟨⟨0, hpos⟩⟩
  obtain ⟨hmod, hrky⟩ := isModular_span_of_gram Q hα hU' hGy
  have hle : span R (Set.range y) ≤ Ks (Fin.cast htt i) := by
    rw [span_le]; rintro _ ⟨k, rfl⟩; exact hy k
  have hmodK : IsModular Q (R ∙ α) (Ks (Fin.cast htt i)) := by
    rw [← haα, hsc]; exact hK.modular _
  have hspan := eq_of_isModular_of_le Q hle hmod hmodK (fg_span (Set.finite_range y)) hfgj
    (by rw [hrky, Fintype.card_fin, hrk])
  have hdety : (gram Q y).det ≠ 0 := by
    rw [hGy, Matrix.det_smul, show ((U - m).map (algebraMap R F)).det = algebraMap R F (U - m).det from
      (RingHom.map_det _ _).symm]
    refine mul_ne_zero (pow_ne_zero _ hα) fun h0 => hU'.ne_zero ?_
    exact (IsFractionRing.injective R F) (h0.trans (map_zero _).symm)
  obtain ⟨hm', b', hb'⟩ := exists_basis_of_family (linearIndependent_of_det_gram_ne_zero (R := R) Q hdety) hspan
  -- the ratio of the discriminants is a unit `≡ 1 mod 𝔭`
  obtain ⟨z, hz, hzw⟩ := exists_unit_sq_of_residue_eq_one (F := F) h2
    (w := U.det * ↑hU'.unit⁻¹) (by
      rw [map_mul, ← residue_det_sub U m hm, ← map_mul, IsUnit.mul_val_inv, map_one])
  refine ⟨b, b', z, hz, ?_⟩
  have hgb' : (gram Q fun k => (b' k : V)) = (gram Q y).submatrix (finCongr hm') (finCongr hm') := by
    ext k l; simp [gram, hb']
  rw [hgb', Matrix.det_submatrix_equiv_self, hG, hGy, Matrix.det_smul, Matrix.det_smul,
    show (U.map (algebraMap R F)).det = algebraMap R F U.det from (RingHom.map_det _ _).symm,
    show ((U - m).map (algebraMap R F)).det = algebraMap R F (U - m).det from (RingHom.map_det _ _).symm,
    ← map_pow, hzw, map_mul]
  have : algebraMap R F (↑hU'.unit⁻¹ : R) * algebraMap R F (U - m).det = 1 := by
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  linear_combination (-(α ^ Fintype.card (Fin (finrank R (Ls i)))) * algebraMap R F U.det) * this

/-- **Theorem 92:2** (O'Meara 1963, p. 247): let $L$ and $K$ be lattices of the same Jordan type on a quadratic space
$V$ over a non-dyadic local field, with Jordan splittings $L = L_1 \perp \cdots \perp L_t$ and
$K = K_1 \perp \cdots \perp K_t$. Then $\operatorname{cls} L = \operatorname{cls} K$ if and only if $dL_i = dK_i$ (in
$F/\mathfrak u^2$) for $1 \le i \le t$. *Reconstruction:* the condition "$dL_i = dK_i$ for $1 \le i \le t$" is lost
in the machine-read text of p. 247 and is restored from step 2 of O'Meara's proof ("Conversely suppose that
$dL_i = dK_i$ for $1 \le i \le t$"). -/
@[kb "omeara1963" "§92, 92:2, p. 247"]
theorem cls_eq_iff_sameDisc (h2 : IsUnit (2 : R)) {L K : Submodule R V} [L.IsLattice F] [K.IsLattice F]
    {t t' : ℕ} {Ls : Fin t → Submodule R V} {Ks : Fin t' → Submodule R V} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q K Ks) (htype : SameJordanType Q Q Ls Ks) :
    cls Q L = cls Q K ↔ ∀ (i : Fin t) (j : Fin t'), (i : ℕ) = j → SameDisc Q Q (Ls i) (Ks j) := by
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  constructor
  · intro hcls i j hij
    have hKL : K ∈ cls Q L := hcls ▸ mem_cls_self Q K
    obtain ⟨σ, hσ, hKσ⟩ := hKL
    have hσL := isJordanSplitting_latMap Q hσ hLfg hL
    rw [← hKσ] at hσL
    have hfgi : (Ls i).FG := FG.of_le hLfg (hL.split.iSup_eq ▸ le_iSup Ls i)
    exact ((isometricLat_latMap Q hσ (Ls i)).sameDisc Q Q hfgi).trans Q Q
      (sameDisc_of_isJordanSplitting Q h2 hKfg hσL hK i j hij)
  · intro hd
    obtain ⟨rfl, hty⟩ := htype
    have hfgi : ∀ i, (Ls i).FG := fun i => FG.of_le hLfg (hL.split.iSup_eq ▸ le_iSup Ls i)
    have hfgk : ∀ i, (Ks i).FG := fun i => FG.of_le hKfg (hK.split.iSup_eq ▸ le_iSup Ks i)
    have hiso : ∀ i, IsometricLat Q Q (Ls i) (Ks i) := by
      intro i
      obtain ⟨hsc, hrk, -⟩ := hty i
      simp only [Fin.cast_eq_self] at hsc hrk
      have hmodK : IsModular Q (scale Q (Ls i)) (Ks i) := by rw [hsc]; exact hK.modular i
      exact (isometricLat_iff_sameDisc_of_isModular Q Q h2 (hfgi i) (hfgk i) (hL.modular i) hmodK hrk).mpr
        (hd i i rfl)
    have hLK := isometricLat_of_isOrthSplit Q Q hL.split hK.split hfgi hiso
    exact (cls_eq_of_mem Q (mem_cls_of_isometricLat Q hLK)).symm

end LocalNonDyadic

end QuadFormsKB.OMeara
