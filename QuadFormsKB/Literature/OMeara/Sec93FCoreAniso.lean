/-
# O'Meara 93:28, sufficiency over a 2-adic field: killing the anisotropic parts and discriminants

**Setting** (as in `Sec93FCoreMove.lean`): $R$ a discrete valuation ring with finite residue field and fraction field
$F$, Henselian, $2 \in F^\times$, $2$ not a unit of $R$ (dyadic), $F$ a local Hilbert field.

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 4–7, pp. 274–275)
* `kill_aniso`: $K_1 \supseteq \langle A(a,q)\rangle \perp \langle A(b,s)\rangle$ with $q, s \in \mathfrak p$ and
  $-q, -s \in \mathfrak gK_2$ is changed, by two applications of 93:19 (`CoreMove.shift_keep`), into
  $\langle A(a,0)\rangle \perp \langle A(b,0)\rangle$;
* `exists_basis_det_of_hyp`: a unimodular lattice on a hyperbolic space has a base of discriminant
  $(-1)^{\operatorname{rank}/2}$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FCoreMove

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.CoreAniso

section Hyp

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open NecBlock Merge28 CoreHyp Uni93

/-- **A unimodular lattice on a hyperbolic space has discriminant $(-1)^{\operatorname{rank}/2}$** (O'Meara 1963,
§93F, proof of 93:28, sufficiency, steps 4–7, pp. 274–275, the discriminant of $\langle A(a_1,0)\rangle \perp \cdots$).
If $M$ is a unimodular lattice (`hMU`) such that $FM$ contains a totally isotropic subspace $T$ with
$\operatorname{rank} M \le 2\dim T$ (`hT`), then $M$ has a base $b$ with $\det(B(b_i, b_j)) = (-1)^{\operatorname{rank}M/2}$.
By 93:3 (`exists_unimodular_blocks`) $M \cong B = \perp_k (\mathfrak oe_k + \mathfrak of_k)$ with $Q(f_k) = 0$,
$B(e_k, f_k) = 1$, each block of determinant $-1$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 4–7, pp. 274–275 (a unimodular lattice on a hyperbolic space has discriminant (−1)^(rank/2))"]
theorem exists_basis_det_of_hyp (hQ : (QuadraticMap.associated Q).Nondegenerate) {M : Submodule R V} (hMfg : M.FG)
    (hMU : IsUnimodular Q M)
    (hT : ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (M : Set V)) ∧
      finrank R M ≤ 2 * finrank F T) :
    ∃ b : Basis (Fin (finrank R M)) R M, (gram Q fun i => (b i : V)).det = (-1) ^ (finrank R M / 2) := by
  obtain ⟨T, hTiso, hTM, hTdim⟩ := hT
  obtain ⟨B, hMB, hBM, hBfg, hBU, hgB, hrB, m, x, hx⟩ :=
    exists_unimodular_blocks Q hMfg (hMU.isRegular Q hMfg) hMU.2.1 hTiso hTM hTdim
  have hspan : span F (B : Set V) = span F (M : Set V) :=
    le_antisymm (span_le.mpr fun b hb => hBM b hb) (span_mono hMB)
  have hiso : IsometricLat Q Q M B :=
    isometricLat_of_normGroup_eq_of_span Q hMfg hBfg hspan hMU hBU hgB.symm
  have hrk : finrank R M = 2 * m := hrB ▸ finrank_of_blockBase Q hx
  obtain ⟨hxB, hf, hef, hee, hefo, hff⟩ := hx
  -- the vectors `(e_k, f_k)` indexed by `Fin 2 × Fin m`
  let w : Fin 2 × Fin m → V := fun p => ![(x p.2).1, (x p.2).2] p.1
  have hgram : gram Q w = Matrix.blockDiagonal (fun k : Fin m => !![Q (x k).1, 1; 1, 0]) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    simp only [gram, Matrix.of_apply, w, Matrix.blockDiagonal_apply]
    by_cases hkl : k = l
    · subst hkl
      simp only [↓reduceIte]
      fin_cases i <;> fin_cases j <;> simp [bil_comm Q (x k).2 (x k).1, hef, hf]
    · simp only [hkl, ↓reduceIte]
      fin_cases i <;> fin_cases j <;> simp [hee k l hkl, hefo k l hkl, hff k l hkl,
        bil_comm Q (x k).2 (x l).1, hefo l k (Ne.symm hkl)]
  have hdet : (gram Q w).det = (-1) ^ m := by
    rw [hgram, Matrix.det_blockDiagonal]
    simp [Matrix.det_fin_two_of]
  have hli : LinearIndependent R w :=
    linearIndependent_of_det_gram_ne_zero (R := R) Q (by rw [hdet]; exact pow_ne_zero _ (by simp))
  have hspanw : span R (Set.range w) = B := by
    rw [← hxB, pairSpan]
    congr 1
    ext v
    constructor
    · rintro ⟨⟨i, k⟩, rfl⟩
      fin_cases i
      · exact Or.inl ⟨k, rfl⟩
      · exact Or.inr ⟨k, rfl⟩
    · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
      · exact ⟨(0, k), rfl⟩
      · exact ⟨(1, k), rfl⟩
  let bB : Basis (Fin 2 × Fin m) R B := (Basis.span hli).map (LinearEquiv.ofEq _ _ hspanw)
  have hbB : ∀ i, (bB i : V) = w i := fun i => by simp [bB, Basis.span_apply]
  obtain ⟨bM, hbM⟩ := Eng93.exists_basis_of_isometricLat Q hiso bB
  have hcard : Fintype.card (Fin 2 × Fin m) = finrank R M := by simp [hrk]
  let σ : (Fin 2 × Fin m) ≃ Fin (finrank R M) := Fintype.equivFinOfCardEq hcard
  refine ⟨bM.reindex σ, ?_⟩
  have h1 : (gram Q fun i => ((bM.reindex σ) i : V)) = (gram Q fun i => (bM i : V)).submatrix σ.symm σ.symm := by
    ext i j; simp [gram]
  have h2 : (gram Q fun i => (bM i : V)) = gram Q w := by
    rw [hbM]; congr 1; exact funext hbB
  rw [h1, Matrix.det_submatrix_equiv_self, h2, hdet, hrk]
  congr 2
  omega

end Hyp

section Kill

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open D18 Sat93 CoreSplit CoreTwo

/-- **One application of 93:19 killing an anisotropic entry** (O'Meara 1963, §93F, proof of 93:28, sufficiency,
step 4, p. 274): in a Jordan splitting with $K_1$ unimodular (`hs0`), $K_1 = (\mathfrak oy_0 + \mathfrak ox_0) \perp C$
(`Ks 0`, `hJC`, written with `x := y₀`, `y := x₀`), $Q(y_0) = q \in \mathfrak p$, $B(y_0, x_0) = 1$, $Q(x_0) = a$,
$\operatorname{rank} K_2 \ge 3$ and $-q \in \mathfrak gK_2$, there are $x', y'$ with $Q(x') = 0$, $B(x', y') = 1$,
$Q(y') = a$, such that $K_1$ becomes $(\mathfrak ox' + \mathfrak oy') \perp C$ (unimodular, of the same rank) and $K_2$
becomes a lattice $K_2''$ with the same scale and rank and $\mathfrak gK_2 \subseteq \mathfrak gK_2''$. -/
theorem step (hHil : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {K : Submodule R V}
    (hKfg : K.FG) {t : ℕ} {Ks : Fin (t + 2) → Submodule R V} (hK : IsJordanSplitting Q K Ks)
    (hs0 : scale Q (Ks 0) = 1) (hrk1 : 3 ≤ finrank R (Ks 1)) {x y : V} {C : Submodule R V}
    (hJC : IsOrthSum Q (Ks 0) (span R {x, y}) C) {q a : R} (hQx : Q x = algebraMap R F q)
    (hxy : bil Q x y = 1) (hQy : Q y = algebraMap R F a) (hq : q ∈ maximalIdeal R)
    (hqg : -algebraMap R F q ∈ normGroup Q (Ks 1)) :
    ∃ x' y' : V, ∃ K'' : Submodule R V, Q x' = 0 ∧ bil Q x' y' = 1 ∧ Q y' = algebraMap R F a ∧
      IsJordanSplitting Q K (Function.update (Function.update Ks 0 (span R {x', y'} ⊔ C)) 1 K'') ∧
      IsOrthSum Q (span R {x', y'} ⊔ C) (span R {x', y'}) C ∧ IsModular Q 1 (span R {x', y'}) ∧
      normGroup Q (Ks 1) ≤ normGroup Q K'' ∧ scale Q K'' = scale Q (Ks 1) ∧
      finrank R K'' = finrank R (Ks 1) ∧ scale Q (span R {x', y'} ⊔ C) = 1 ∧
      finrank R ↥(span R {x', y'} ⊔ C) = finrank R (Ks 0) := by
  have hle : ∀ j, Ks j ≤ K := fun j => hK.split.iSup_eq ▸ le_iSup Ks j
  have hK0fg : (Ks 0).FG := FG.of_le hKfg (hle 0)
  have hCK0 : C ≤ Ks 0 := hJC.sup_eq ▸ le_sup_right
  have hCfg : C.FG := FG.of_le hK0fg hCK0
  have hdet0 : IsUnit (q * a - 1 * 1) := by
    have : q * a - 1 * 1 = -(1 - q * a) := by ring
    rw [this, IsUnit.neg_iff]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right _ _ hq))
  have hdet : IsUnit ((q + -q) * a - 1 * 1) := by
    rw [show (q + -q) * a - 1 * 1 = -1 by ring]; exact isUnit_one.neg
  have hJ := span_pair_isModular Q (one_ne_zero (α := F)) hdet0 (by rw [hQx, one_mul])
    (by rw [hQy, one_mul]) (by rw [hxy, map_one, mul_one])
  obtain ⟨x', y', K'', hQx', hx'y', hQy', hJS, hOS, hnorm, hsc, hrk⟩ :=
    CoreMove.shift_keep Q hHil h2p hKfg hK hs0 hJC hQx hxy hQy hq hrk1 (γ₀ := -q)
      (by rw [map_neg]; exact hqg) hdet
  have hQx0 : Q x' = 0 := by rw [hQx']; simp
  have hdet'' : IsUnit ((0 : R) * a - 1 * 1) := by
    rw [show (0 : R) * a - 1 * 1 = -1 by ring]; exact isUnit_one.neg
  have hJ'mod := span_pair_isModular Q (one_ne_zero (α := F)) (p := 0) (q := a) (e := 1) hdet''
    (by rw [hQx0]; simp) (by rw [hQy', one_mul]) (by rw [hx'y', map_one, mul_one])
  rw [← Submodule.one_eq_span] at hJ'mod
  have hJ'fg : (span R {x', y'}).FG := Submodule.fg_span (Set.toFinite _)
  refine ⟨x', y', K'', hQx0, hx'y', hQy', hJS, hOS, hJ'mod.1, hnorm, hsc, hrk, ?_, ?_⟩
  · rw [scale_sup_of_orth Q hOS.orth, hJ'mod.1.2.1]
    exact sup_eq_left.mpr ((scale_mono Q hCK0).trans hs0.le)
  · rw [isOrthSum_finrank Q hOS (hJ'fg.sup hCfg), hJ'mod.2, isOrthSum_finrank Q hJC hK0fg, hJ.2]

/-- **Killing the anisotropic parts** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 4, p. 274: "there is a
splitting $K_1 \perp K_2 \cong \langle A(a_1,0)\rangle \perp \langle A(b_1,0)\rangle \perp K_2'$"). Let
$K = K_1 \perp \cdots \perp K_{t+2}$ be a Jordan splitting (`Ks 0`, `Ks 1`, … are $K_1, K_2, \dots$) with $K_1$
unimodular (`hs0`), $\operatorname{rank} K_2 \ge 3$ (`hrk1`), and $K_1 = M \perp C$ (`hMC`) where $M$ has a base
$x_1, y_1, x_2, y_2$ with Gram matrix $A(a,q) \perp A(b,s)$ (`hg`; `e 0 = x₁`, `e 1 = y₁`, `e 2 = x₂`, `e 3 = y₂`),
$q, s \in \mathfrak p$ and $-q, -s \in \mathfrak gK_2$ (`hqg`, `hsg`). Then $K$ has a Jordan splitting `Ks'` with
the scales and ranks of the $K_i$ (the components `Ks i`, $2 \le i$, unchanged), $\mathfrak gK_2 \subseteq
\mathfrak gK_2'$, and $K_1' = M' \perp C$ where $M'$ has a base with Gram matrix $A(a,0) \perp A(b,0)$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 4–7, pp. 274–275 (K₁ ⊥ K₂ ≅ ⟨A(a₁,0)⟩ ⊥ ⟨A(b₁,0)⟩ ⊥ K₂')"]
theorem kill_aniso (hHil : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {K : Submodule R V}
    (hKfg : K.FG) {t : ℕ} {Ks : Fin (t + 2) → Submodule R V} (hK : IsJordanSplitting Q K Ks)
    (hs0 : scale Q (Ks 0) = 1) (hrk1 : 3 ≤ finrank R (Ks 1)) {M C : Submodule R V}
    (hMC : IsOrthSum Q (Ks 0) M C) (e : Basis (Fin 4) R M) {a b q s : R}
    (hg : gram Q (fun i => (e i : V)) =
      D18.blk2 (algebraMap R F a) (algebraMap R F q) (algebraMap R F b) (algebraMap R F s))
    (hq : q ∈ maximalIdeal R) (hs : s ∈ maximalIdeal R)
    (hqg : -algebraMap R F q ∈ normGroup Q (Ks 1)) (hsg : -algebraMap R F s ∈ normGroup Q (Ks 1)) :
    ∃ Ks' : Fin (t + 2) → Submodule R V, IsJordanSplitting Q K Ks' ∧
      (∀ i : Fin (t + 2), 2 ≤ (i : ℕ) → Ks' i = Ks i) ∧
      normGroup Q (Ks 1) ≤ normGroup Q (Ks' 1) ∧
      (∀ i, scale Q (Ks' i) = scale Q (Ks i) ∧ finrank R (Ks' i) = finrank R (Ks i)) ∧
      ∃ M' : Submodule R V, IsOrthSum Q (Ks' 0) M' C ∧
        ∃ e' : Basis (Fin 4) R M',
          gram Q (fun i => (e' i : V)) = D18.blk2 (algebraMap R F a) 0 (algebraMap R F b) 0 := by
  have h01 : (0 : Fin (t + 2)) ≠ 1 := by simp [Fin.ext_iff]
  have hle : ∀ j, Ks j ≤ K := fun j => hK.split.iSup_eq ▸ le_iSup Ks j
  have hK0fg : (Ks 0).FG := FG.of_le hKfg (hle 0)
  have hMK0 : M ≤ Ks 0 := hMC.sup_eq ▸ le_sup_left
  have hCK0 : C ≤ Ks 0 := hMC.sup_eq ▸ le_sup_right
  have hCfg : C.FG := FG.of_le hK0fg hCK0
  -- the entries of the Gram matrix
  have hb : ∀ i j, bil Q (e i : V) (e j : V) = D18.blk2 (algebraMap R F a) (algebraMap R F q)
      (algebraMap R F b) (algebraMap R F s) i j := fun i j => by
    have := congrFun (congrFun hg i) j
    simpa [gram] using this
  have hQ0 : Q (e 0 : V) = algebraMap R F a := by simpa [D18.blk2] using hb 0 0
  have hB01 : bil Q (e 0 : V) (e 1 : V) = 1 := by simpa [D18.blk2] using hb 0 1
  have hQ1 : Q (e 1 : V) = algebraMap R F q := by simpa [D18.blk2] using hb 1 1
  have hQ2 : Q (e 2 : V) = algebraMap R F b := by simpa [D18.blk2] using hb 2 2
  have hB23 : bil Q (e 2 : V) (e 3 : V) = 1 := by simpa [D18.blk2] using hb 2 3
  have hQ3 : Q (e 3 : V) = algebraMap R F s := by simpa [D18.blk2] using hb 3 3
  have h02 : bil Q (e 0 : V) (e 2 : V) = 0 := by simpa [D18.blk2] using hb 0 2
  have h03 : bil Q (e 0 : V) (e 3 : V) = 0 := by simpa [D18.blk2] using hb 0 3
  have h12 : bil Q (e 1 : V) (e 2 : V) = 0 := by simpa [D18.blk2] using hb 1 2
  have h13 : bil Q (e 1 : V) (e 3 : V) = 0 := by simpa [D18.blk2] using hb 1 3
  have h10 : bil Q (e 1 : V) (e 0 : V) = 1 := by rw [bil_comm]; exact hB01
  have h32 : bil Q (e 3 : V) (e 2 : V) = 1 := by rw [bil_comm]; exact hB23
  have hmem : ∀ i, (e i : V) ∈ M := fun i => (e i).2
  -- `M = P₁ ⊔ P₂`
  set P₁ : Submodule R V := span R {(e 1 : V), (e 0 : V)} with hP₁
  set P₂ : Submodule R V := span R {(e 3 : V), (e 2 : V)} with hP₂
  have hP₁M : P₁ ≤ M := span_le.mpr (by
    rintro v (rfl | rfl)
    · exact hmem 1
    · exact hmem 0)
  have hP₂M : P₂ ≤ M := span_le.mpr (by
    rintro v (rfl | rfl)
    · exact hmem 3
    · exact hmem 2)
  have hMsp : P₁ ⊔ P₂ = M := by
    refine le_antisymm (sup_le hP₁M hP₂M) ?_
    intro m hm
    have hsum := congrArg Subtype.val (e.sum_repr ⟨m, hm⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    rw [← hsum, Fin.sum_univ_four]
    have m0 : (e 0 : V) ∈ P₁ ⊔ P₂ := mem_sup_left (subset_span (by simp))
    have m1 : (e 1 : V) ∈ P₁ ⊔ P₂ := mem_sup_left (subset_span (by simp))
    have m2 : (e 2 : V) ∈ P₁ ⊔ P₂ := mem_sup_right (subset_span (by simp))
    have m3 : (e 3 : V) ∈ P₁ ⊔ P₂ := mem_sup_right (subset_span (by simp))
    exact add_mem (add_mem (add_mem (smul_mem _ _ m0) (smul_mem _ _ m1)) (smul_mem _ _ m2)) (smul_mem _ _ m3)
  have hP₁fg : P₁.FG := Submodule.fg_span (Set.toFinite _)
  have hP₂fg : P₂.FG := Submodule.fg_span (Set.toFinite _)
  have horth12 : ∀ u ∈ P₁, ∀ v ∈ P₂, bil Q u v = 0 := by
    refine orth_span_pair Q ?_ ?_ ?_ ?_
    · exact h13
    · exact h12
    · exact h03
    · exact h02
  have horthC : ∀ u ∈ M, ∀ v ∈ C, bil Q u v = 0 := hMC.orth
  -- regularity of the planes
  have hqa : IsUnit (q * a - 1 * 1) := by
    have : q * a - 1 * 1 = -(1 - q * a) := by ring
    rw [this, IsUnit.neg_iff]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right _ _ hq))
  have hP₁mod := span_pair_isModular Q (one_ne_zero (α := F)) hqa (by rw [hQ1, one_mul])
    (by rw [hQ0, one_mul]) (by rw [h10, map_one, mul_one])
  have hsb : IsUnit (s * b - 1 * 1) := by
    have : s * b - 1 * 1 = -(1 - s * b) := by ring
    rw [this, IsUnit.neg_iff]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right _ _ hs))
  have hP₂mod := span_pair_isModular Q (one_ne_zero (α := F)) hsb (by rw [hQ3, one_mul])
    (by rw [hQ2, one_mul]) (by rw [h32, map_one, mul_one])
  have hP₁reg : IsRegular Q P₁ := hP₁mod.1.isRegular Q hP₁fg
  have hP₂reg : IsRegular Q P₂ := hP₂mod.1.isRegular Q hP₂fg
  -- step 1
  have hJC₁ : IsOrthSum Q (Ks 0) P₁ (P₂ ⊔ C) := by
    have ho : ∀ u ∈ P₁, ∀ v ∈ P₂ ⊔ C, bil Q u v = 0 := by
      intro u hu v hv
      obtain ⟨p, hp, c, hc, rfl⟩ := mem_sup.mp hv
      rw [bil_add_right, horth12 u hu p hp, horthC u (hP₁M hu) c hc, add_zero]
    refine ⟨ho, disjoint_of_orth Q hP₁reg ho, ?_⟩
    rw [← hMC.sup_eq, ← hMsp]; ac_rfl
  obtain ⟨x', y', K₁, hQx', hx'y', hQy', hK₁, hOS₁, hmod₁, hnorm₁, hsc₁, hrk₁, hscJ₁, hfr₁⟩ :=
    step Q hHil h2p hKfg hK hs0 hrk1 hJC₁ hQ1 h10 hQ0 hq hqg
  set J' : Submodule R V := span R {x', y'} with hJ'
  set Ks₁ : Fin (t + 2) → Submodule R V := Function.update (Function.update Ks 0 (J' ⊔ (P₂ ⊔ C))) 1 K₁
    with hKs₁
  have hKs₁0 : Ks₁ 0 = J' ⊔ (P₂ ⊔ C) := by simp [hKs₁, Function.update_of_ne h01]
  have hKs₁1 : Ks₁ 1 = K₁ := by simp [hKs₁]
  -- step 2
  have hs0₁ : scale Q (Ks₁ 0) = 1 := by rw [hKs₁0]; exact hscJ₁
  have hrk₁' : 3 ≤ finrank R (Ks₁ 1) := by rw [hKs₁1, hrk₁]; exact hrk1
  have hsg₁ : -algebraMap R F s ∈ normGroup Q (Ks₁ 1) := by rw [hKs₁1]; exact hnorm₁ hsg
  have hJ'fg : J'.FG := Submodule.fg_span (Set.toFinite _)
  have hJ'C : ∀ u ∈ J', ∀ v ∈ C, bil Q u v = 0 := fun u hu v hv =>
    hOS₁.orth u hu v (mem_sup_right hv)
  have hJC₂ : IsOrthSum Q (Ks₁ 0) P₂ (J' ⊔ C) := by
    have ho : ∀ u ∈ P₂, ∀ v ∈ J' ⊔ C, bil Q u v = 0 := by
      intro u hu v hv
      obtain ⟨p, hp, c, hc, rfl⟩ := mem_sup.mp hv
      rw [bil_add_right, bil_comm Q u p, hOS₁.orth p hp u (mem_sup_left hu), horthC u (hP₂M hu) c hc, add_zero]
    refine ⟨ho, disjoint_of_orth Q hP₂reg ho, ?_⟩
    rw [hKs₁0]; ac_rfl
  obtain ⟨x'', y'', K₂, hQx'', hx''y'', hQy'', hK₂, hOS₂, hmod₂, hnorm₂, hsc₂, hrk₂, hscJ₂, hfr₂⟩ :=
    step Q hHil h2p hKfg hK₁ hs0₁ hrk₁' hJC₂ hQ3 h32 hQ2 hs hsg₁
  set J'' : Submodule R V := span R {x'', y''} with hJ''
  set Ks₂ : Fin (t + 2) → Submodule R V :=
    Function.update (Function.update Ks₁ 0 (J'' ⊔ (J' ⊔ C))) 1 K₂ with hKs₂
  have hKs₂0 : Ks₂ 0 = J'' ⊔ (J' ⊔ C) := by simp [hKs₂, Function.update_of_ne h01]
  have hKs₂1 : Ks₂ 1 = K₂ := by simp [hKs₂]
  have hKs₂i : ∀ i : Fin (t + 2), i ≠ 0 → i ≠ 1 → Ks₂ i = Ks i := by
    intro i h0 h1
    rw [hKs₂, Function.update_of_ne h1, Function.update_of_ne h0, hKs₁, Function.update_of_ne h1,
      Function.update_of_ne h0]
  have hJ''fg : J''.FG := Submodule.fg_span (Set.toFinite _)
  have hc : ∀ u ∈ J', ∀ v ∈ J'', bil Q u v = 0 := fun u hu v hv => by
    rw [bil_comm]; exact hOS₂.orth v hv u (mem_sup_left hu)
  have hJ''C : ∀ u ∈ J'', ∀ v ∈ C, bil Q u v = 0 := fun u hu v hv =>
    hOS₂.orth u hu v (mem_sup_right hv)
  have hM'mod := isModular_sup Q hmod₁ hmod₂ hJ'fg hJ''fg hc
  have hM'reg : IsRegular Q (J' ⊔ J'') := hM'mod.1.isRegular Q (hJ'fg.sup hJ''fg)
  have hM'C : ∀ u ∈ J' ⊔ J'', ∀ v ∈ C, bil Q u v = 0 := by
    intro u hu v hv
    obtain ⟨p, hp, r, hr, rfl⟩ := mem_sup.mp hu
    rw [bil_add_left, hJ'C p hp v hv, hJ''C r hr v hv, add_zero]
  refine ⟨Ks₂, hK₂, ?_, ?_, ?_, J' ⊔ J'', ⟨hM'C, disjoint_of_orth Q hM'reg hM'C, ?_⟩, ?_⟩
  · intro i hi
    exact hKs₂i i (fun h => by subst h; simp at hi) (fun h => by subst h; simp at hi)
  · rw [hKs₂1]; exact hnorm₁.trans (by simpa [hKs₁1] using hnorm₂)
  · intro i
    by_cases i0 : i = 0
    · subst i0
      rw [hKs₂0, hs0]
      refine ⟨hscJ₂, ?_⟩
      rw [hfr₂]
      rw [hKs₁0]; exact hfr₁
    · by_cases i1 : i = 1
      · subst i1
        rw [hKs₂1]
        refine ⟨?_, ?_⟩
        · rw [hsc₂, hKs₁1, hsc₁]
        · rw [hrk₂, hKs₁1, hrk₁]
      · rw [hKs₂i i i0 i1]; exact ⟨rfl, rfl⟩
  · rw [hKs₂0]; ac_rfl
  -- the base `(y', x', y'', x'')`
  · set v : Fin 4 → V := ![y', x', y'', x''] with hvdef
    have mx' : x' ∈ J' := subset_span (by simp)
    have my' : y' ∈ J' := subset_span (by simp)
    have mx'' : x'' ∈ J'' := subset_span (by simp)
    have my'' : y'' ∈ J'' := subset_span (by simp)
    have c1 := hc y' my' y'' my''
    have c2 := hc y' my' x'' mx''
    have c3 := hc x' mx' y'' my''
    have c4 := hc x' mx' x'' mx''
    have c1' : bil Q y'' y' = 0 := by rw [bil_comm]; exact c1
    have c2' : bil Q x'' y' = 0 := by rw [bil_comm]; exact c2
    have c3' : bil Q y'' x' = 0 := by rw [bil_comm]; exact c3
    have c4' : bil Q x'' x' = 0 := by rw [bil_comm]; exact c4
    have d1 : bil Q y' x' = 1 := by rw [bil_comm]; exact hx'y'
    have d2 : bil Q y'' x'' = 1 := by rw [bil_comm]; exact hx''y''
    have hv : gram Q v = D18.blk2 (algebraMap R F a) 0 (algebraMap R F b) 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [gram, D18.blk2, hvdef, c1, c2, c3, c4, c1', c2', c3', c4', d1, d2, hx'y', hx''y'', hQx',
          hQy', hQx'', hQy'']
    have hli : LinearIndependent R v :=
      linearIndependent_of_det_gram_ne_zero (R := R) Q (by rw [hv, D18.det_blk2]; simp)
    have hspan : span R (Set.range v) = J' ⊔ J'' := by
      apply le_antisymm
      · rw [span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact mem_sup_left my'
        · exact mem_sup_left mx'
        · exact mem_sup_right my''
        · exact mem_sup_right mx''
      · refine sup_le (span_le.mpr ?_) (span_le.mpr ?_)
        · rintro w (rfl | rfl)
          · exact subset_span ⟨1, rfl⟩
          · exact subset_span ⟨0, rfl⟩
        · rintro w (rfl | rfl)
          · exact subset_span ⟨3, rfl⟩
          · exact subset_span ⟨2, rfl⟩
    refine ⟨(Basis.span hli).map (LinearEquiv.ofEq _ _ hspan), ?_⟩
    rw [← hv]
    congr 1
    funext i
    simp [Basis.span_apply]

end Kill

end QuadFormsKB.OMeara.CoreAniso
