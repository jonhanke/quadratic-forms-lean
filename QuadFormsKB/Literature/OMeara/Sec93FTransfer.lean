/-
# O'Meara 93:28: transfer of the conditions (i)–(iii) along isometries and orthogonal sums

**Setting** (as in `Sec93E.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$; lattices
`Submodule R V`. The condition $dM/dN \cong 1 \bmod \mathfrak a$ is `DiscQuotSqEquivMod Q M N 𝔞` (bases indexed by
`Fin (finrank R M)`).

**Proves** (the bookkeeping behind the reductions in the proof of 93:28, O'Meara 1963, pp. 268–276)
* `det_gram_change`: two bases of a lattice have discriminants differing by the square of a unit;
* `discQuot_of_bases`: $dM/dN \cong 1$ can be checked on any pair of bases (any index types);
* `discQuot_iff_of_isometricLat`: the condition is invariant under isometries of $M$ and of $N$;
* `discQuot_of_isOrthSum`: $d(M \perp H)/d(N \perp H') \cong 1$ and $H \cong H'$ give $dM/dN \cong 1$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FArith
import QuadFormsKB.Literature.OMeara.Sec93D18

open QuadraticMap Submodule Module IsLocalRing
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Transfer28

open Arith28

variable {R : Type*} [CommRing R] [IsDomain R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- **Change of base** (O'Meara 1963, §82B): two bases of a lattice have discriminants differing by the square of a
unit of $\mathfrak o$. -/
theorem det_gram_change {M : Submodule R V} {ι : Type*} [Fintype ι] [DecidableEq ι] (e e' : Basis ι R M) :
    ∃ u : R, IsUnit u ∧ (gram Q fun i => (e' i : V)).det = algebraMap R F u ^ 2 * (gram Q fun i => (e i : V)).det := by
  set P : Matrix ι ι R := Matrix.of fun i j => e.repr (e' i) j with hP
  have hcomb : (fun i => (e' i : V)) = fun i => ∑ j, (P.map (algebraMap R F)) i j • (e j : V) := by
    funext i
    have h := e.sum_repr (e' i)
    conv_lhs => rw [← h]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hP, Matrix.map_apply, algebraMap_smul]
  have hdet : IsUnit P.det := by
    have : P = (e.toMatrix e')ᵀ := by ext i j; simp [hP, Basis.toMatrix_apply]
    rw [this, Matrix.det_transpose, ← Basis.det_apply]
    exact Basis.isUnit_det e e'
  refine ⟨P.det, hdet, ?_⟩
  rw [hcomb, D18.gram_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det]
  ring

/-- Multiplying by squares of units preserves $\cong 1 \bmod \mathfrak a$. -/
theorem sqEquivMod_one_of_unit_sq {X : Submodule R F} {x : F} {u : R} (hu : IsUnit u)
    (h : SqEquivMod X x 1) : SqEquivMod X (algebraMap R F u ^ 2 * x) 1 :=
  sqEquivMod_sq_mul_one h hu

/-- The ratio $dM/dN$ for two pairs of bases differs by a unit square. -/
theorem ratio_change {M N : Submodule R V} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e₁ e₂ : Basis ι R M) (f₁ f₂ : Basis κ R N) (hN : (gram Q fun i => (f₁ i : V)).det ≠ 0) :
    ∃ u : R, IsUnit u ∧ (gram Q fun i => (e₂ i : V)).det / (gram Q fun i => (f₂ i : V)).det =
      algebraMap R F u ^ 2 * ((gram Q fun i => (e₁ i : V)).det / (gram Q fun i => (f₁ i : V)).det) := by
  obtain ⟨u, hu, h1⟩ := det_gram_change Q e₁ e₂
  obtain ⟨w, hw, h2⟩ := det_gram_change Q f₁ f₂
  obtain ⟨w', hw'⟩ := hw.exists_left_inv
  have hw'F : algebraMap R F w' * algebraMap R F w = 1 := by rw [← map_mul, hw', map_one]
  have hwF : algebraMap R F w ≠ 0 := fun h => by rw [h, mul_zero] at hw'F; exact zero_ne_one hw'F
  have hw'inv : algebraMap R F w' = (algebraMap R F w)⁻¹ := eq_inv_of_mul_eq_one_left hw'F
  refine ⟨u * w', hu.mul (IsUnit.of_mul_eq_one w hw'), ?_⟩
  rw [h1, h2, map_mul, hw'inv]
  field_simp

/-- **$dM/dN \cong 1 \bmod \mathfrak a$ on any bases**: if bases $e$ of $M$ and $f$ of $N$ (any finite index types)
have $d(e)/d(f) \cong 1 \bmod \mathfrak a$, then `DiscQuotSqEquivMod Q M N 𝔞`. -/
theorem discQuot_of_bases {M N : Submodule R V} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : Basis ι R M) (f : Basis κ R N)
    {X : Submodule R F} (h : SqEquivMod X ((gram Q fun i => (e i : V)).det / (gram Q fun i => (f i : V)).det) 1) :
    DiscQuotSqEquivMod Q M N X := by
  classical
  have hM : finrank R M = Fintype.card ι := finrank_eq_card_basis e
  have hNr : finrank R N = Fintype.card κ := finrank_eq_card_basis f
  let e' : Basis (Fin (finrank R M)) R M := e.reindex (Fintype.equivFinOfCardEq hM.symm)
  let f' : Basis (Fin (finrank R N)) R N := f.reindex (Fintype.equivFinOfCardEq hNr.symm)
  refine ⟨e', f', ?_⟩
  have he : (gram Q fun i => (e' i : V)).det = (gram Q fun i => (e i : V)).det := by
    simp only [e', Basis.reindex_apply]
    exact Matrix.det_submatrix_equiv_self (Fintype.equivFinOfCardEq hM.symm).symm (gram Q fun i => (e i : V))
  have hf : (gram Q fun i => (f' i : V)).det = (gram Q fun i => (f i : V)).det := by
    simp only [f', Basis.reindex_apply]
    exact Matrix.det_submatrix_equiv_self (Fintype.equivFinOfCardEq hNr.symm).symm (gram Q fun i => (f i : V))
  rw [he, hf]; exact h

/-- **The condition does not depend on the bases**: if `DiscQuotSqEquivMod Q M N 𝔞` holds then every pair of bases
satisfies $d(e)/d(f) \cong 1 \bmod \mathfrak a$ (provided $dN \ne 0$). -/
theorem discQuot_bases {M N : Submodule R V} {X : Submodule R F} (h : DiscQuotSqEquivMod Q M N X) {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : Basis ι R M) (f : Basis κ R N)
    (hN : (gram Q fun i => (f i : V)).det ≠ 0) :
    SqEquivMod X ((gram Q fun i => (e i : V)).det / (gram Q fun i => (f i : V)).det) 1 := by
  classical
  obtain ⟨e₀, f₀, h0⟩ := h
  have hM : Fintype.card ι = finrank R M := (finrank_eq_card_basis e).symm
  have hNr : Fintype.card κ = finrank R N := (finrank_eq_card_basis f).symm
  let e₁ : Basis ι R M := e₀.reindex (Fintype.equivFinOfCardEq hM).symm
  let f₁ : Basis κ R N := f₀.reindex (Fintype.equivFinOfCardEq hNr).symm
  have he₁ : (gram Q fun i => (e₁ i : V)).det = (gram Q fun i => (e₀ i : V)).det := by
    simp only [e₁, Basis.reindex_apply]
    exact Matrix.det_submatrix_equiv_self (Fintype.equivFinOfCardEq hM).symm.symm (gram Q fun i => (e₀ i : V))
  have hf₁ : (gram Q fun i => (f₁ i : V)).det = (gram Q fun i => (f₀ i : V)).det := by
    simp only [f₁, Basis.reindex_apply]
    exact Matrix.det_submatrix_equiv_self (Fintype.equivFinOfCardEq hNr).symm.symm (gram Q fun i => (f₀ i : V))
  have hf₁0 : (gram Q fun i => (f₁ i : V)).det ≠ 0 := by
    obtain ⟨w, hw, h2⟩ := det_gram_change Q f₁ f
    intro h0'
    rw [h2, h0', mul_zero] at hN; exact hN rfl
  obtain ⟨u, hu, hr⟩ := ratio_change Q e₁ e f₁ f hf₁0
  rw [hr, he₁, hf₁]
  exact sqEquivMod_sq_mul_one h0 hu

/-- **A regular lattice has non-zero discriminant**: the matrix of a base of a regular lattice is invertible. -/
theorem det_gram_ne_zero_of_isRegular {L : Submodule R V} (hreg : IsRegular Q L) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (e : Basis ι R L) : (gram Q fun i => (e i : V)).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  -- clear denominators
  choose n d hd using fun i => IsFractionRing.div_surjective (A := R) (v i)
  set D : R := ∏ i, d i with hD
  have hdF : ∀ i, algebraMap R F (d i) ≠ 0 := fun i =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hd i).1
  have hDF : algebraMap R F D ≠ 0 := by
    rw [hD, map_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hdF i
  have hint : ∀ i, ∃ c : R, algebraMap R F c = algebraMap R F D * v i := by
    intro i
    refine ⟨n i * ∏ j ∈ Finset.univ.erase i, d j, ?_⟩
    rw [← (hd i).2, hD, ← Finset.mul_prod_erase Finset.univ (fun j => d j) (Finset.mem_univ i)]
    have hdi := hdF i
    simp only [map_mul, map_prod]
    field_simp
  choose c hc using hint
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hv0
    funext i
    have := hc i
    rw [hc0, Pi.zero_apply, map_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hDF
  set x : L := ∑ i, c i • e i with hx
  have hx0 : x ≠ 0 := by
    intro h
    apply hc0
    funext i
    have := congrArg (e.repr) h
    simpa [hx, Finsupp.single_apply] using congrFun (congrArg DFunLike.coe this) i
  -- `B(x, e_j) = 0`
  have hBe : ∀ j, bil Q (x : V) (e j : V) = 0 := by
    intro j
    rw [hx, Submodule.coe_sum, bil_sum_left]
    have hj := congrFun hv j
    simp only [Matrix.mulVec, dotProduct, gram, Matrix.of_apply] at hj
    have : ∑ i, bil Q ((c i • e i : L) : V) (e j : V) = algebraMap R F D * ∑ i, v i * bil Q (e j : V) (e i : V) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.coe_smul, bil_rsmul_left, hc i, bil_comm]; ring
    rw [this, show ∑ i, v i * bil Q (e j : V) (e i : V) = ∑ i, bil Q (e j : V) (e i : V) * v i from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, hj, Pi.zero_apply, mul_zero]
  apply hx0
  refine Subtype.ext (hreg (x : V) x.2 fun l hl => ?_)
  have hsum := e.sum_repr ⟨l, hl⟩
  have : (l : V) = ∑ j, (e.repr ⟨l, hl⟩ j) • (e j : V) := by
    have := congrArg Subtype.val hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  rw [this, bil_sum_right]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [bil_rsmul_right, hBe j, mul_zero]

/-- **Isometries preserve the condition $dM/dN \cong 1 \bmod \mathfrak a$**: if $M \cong M'$ and $N \cong N'$ (possibly
in another space) then `DiscQuotSqEquivMod Q M N 𝔞 → DiscQuotSqEquivMod Q' M' N' 𝔞`. -/
theorem discQuot_of_isometricLat {M N : Submodule R V} {M' N' : Submodule R V'} (hM : IsometricLat Q Q' M M')
    (hN : IsometricLat Q Q' N N') {X : Submodule R F} (h : DiscQuotSqEquivMod Q M N X) :
    DiscQuotSqEquivMod Q' M' N' X := by
  classical
  obtain ⟨f, hf⟩ := hM
  obtain ⟨g, hg⟩ := hN
  obtain ⟨e, e', he⟩ := h
  refine discQuot_of_bases Q' (e.map f) (e'.map g) ?_
  have h1 : (gram Q' fun i => ((e.map f) i : V')) = gram Q fun i => (e i : V) := by
    ext i j; simp [gram, Basis.map_apply, bil_eq_of_isometricLat Q Q' f hf]
  have h2 : (gram Q' fun i => ((e'.map g) i : V')) = gram Q fun i => (e' i : V) := by
    ext i j; simp [gram, Basis.map_apply, bil_eq_of_isometricLat Q Q' g hg]
  rw [h1, h2]; exact he

/-- **A base of an orthogonal sum**: bases of $M$ and $H$ give a base of $M \perp H$ indexed by `ι ⊕ κ`. -/
theorem exists_basis_isOrthSum {X M H : Submodule R V} (h : IsOrthSum Q X M H) {ι κ : Type*}
    (eM : Basis ι R M) (eH : Basis κ R H) :
    ∃ e : Basis (ι ⊕ κ) R X, ∀ s, (e s : V) = Sum.elim (fun i => (eM i : V)) (fun k => (eH k : V)) s := by
  set v : ι ⊕ κ → V := Sum.elim (fun i => (eM i : V)) (fun k => (eH k : V)) with hv
  have hliM : LinearIndependent R fun i => (eM i : V) := eM.linearIndependent.map' M.subtype (ker_subtype M)
  have hliH : LinearIndependent R fun k => (eH k : V) := eH.linearIndependent.map' H.subtype (ker_subtype H)
  have hli : LinearIndependent R v := by
    refine hliM.sum_type hliH ?_
    rw [span_basis_eq, span_basis_eq]; exact h.disjoint
  have hspan : span R (Set.range v) = X := by
    rw [hv, Set.Sum.elim_range, span_union, span_basis_eq, span_basis_eq, h.sup_eq]
  refine ⟨(Basis.span hli).map (LinearEquiv.ofEq _ _ hspan), fun s => ?_⟩
  simp [Basis.span_apply]

/-- The matrix of a base of an orthogonal sum is block diagonal: $d(M \perp H) = dM \cdot dH$. -/
theorem det_gram_sumElim {M H : Submodule R V} (horth : ∀ x ∈ M, ∀ y ∈ H, bil Q x y = 0) {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (a : ι → V) (b : κ → V) (ha : ∀ i, a i ∈ M)
    (hb : ∀ k, b k ∈ H) : (gram Q (Sum.elim a b)).det = (gram Q a).det * (gram Q b).det := by
  have : gram Q (Sum.elim a b) = Matrix.fromBlocks (gram Q a) 0 0 (gram Q b) := by
    ext (i | k) (j | l)
    · simp [gram]
    · simp [gram, horth _ (ha i) _ (hb l)]
    · simp [gram, bil_comm Q (b k) (a j), horth _ (ha j) _ (hb k)]
    · simp [gram]
  rw [this, Matrix.det_fromBlocks_zero₂₁]

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Cancelling a common orthogonal summand** (the bookkeeping of the adjunctions in O'Meara's proof of 93:28,
p. 270): if $\tilde M = M \perp H$, $\tilde N = N \perp H'$ with $H \cong H'$, all finitely generated and $\tilde N$,
$H$ regular, then $d\tilde M/d\tilde N \cong 1 \bmod \mathfrak a$ implies $dM/dN \cong 1 \bmod \mathfrak a$; and
conversely. -/
theorem discQuot_isOrthSum_iff {M₁ N₁ M N H H' : Submodule R V} (hM : IsOrthSum Q M₁ M H)
    (hN : IsOrthSum Q N₁ N H') (hHH : IsometricLat Q Q H H') (hMfg : M.FG) (hNfg : N.FG) (hHfg : H.FG)
    (hNreg : IsRegular Q N) (hHreg : IsRegular Q H) (hH'reg : IsRegular Q H') {X : Submodule R F} :
    DiscQuotSqEquivMod Q M₁ N₁ X ↔ DiscQuotSqEquivMod Q M N X := by
  classical
  obtain ⟨eM⟩ := exists_basis (R := R) (F := F) hMfg
  obtain ⟨eN⟩ := exists_basis (R := R) (F := F) hNfg
  obtain ⟨eH⟩ := exists_basis (R := R) (F := F) hHfg
  obtain ⟨f, hf⟩ := hHH
  set eH' := eH.map f
  obtain ⟨e₁, he₁⟩ := exists_basis_isOrthSum Q hM eM eH
  obtain ⟨f₁, hf₁⟩ := exists_basis_isOrthSum Q hN eN eH'
  have hd₁ : (gram Q fun s => (e₁ s : V)).det = (gram Q fun i => (eM i : V)).det * (gram Q fun k => (eH k : V)).det := by
    rw [show (fun s => (e₁ s : V)) = Sum.elim (fun i => (eM i : V)) (fun k => (eH k : V)) from funext he₁]
    exact det_gram_sumElim Q hM.orth _ _ (fun i => (eM i).2) (fun k => (eH k).2)
  have hd₂ : (gram Q fun s => (f₁ s : V)).det = (gram Q fun i => (eN i : V)).det * (gram Q fun k => (eH' k : V)).det := by
    rw [show (fun s => (f₁ s : V)) = Sum.elim (fun i => (eN i : V)) (fun k => (eH' k : V)) from funext hf₁]
    exact det_gram_sumElim Q hN.orth _ _ (fun i => (eN i).2) (fun k => (eH' k).2)
  have hHH' : (gram Q fun k => (eH' k : V)) = gram Q fun k => (eH k : V) := by
    ext i j; simp [gram, eH', Basis.map_apply, bil_eq_of_isometricLat Q Q f hf]
  have hN0 := det_gram_ne_zero_of_isRegular Q hNreg eN
  have hH0 := det_gram_ne_zero_of_isRegular Q hHreg eH
  have hN₁0 : (gram Q fun s => (f₁ s : V)).det ≠ 0 := by
    rw [hd₂, hHH']; exact mul_ne_zero hN0 hH0
  have hratio : (gram Q fun s => (e₁ s : V)).det / (gram Q fun s => (f₁ s : V)).det =
      (gram Q fun i => (eM i : V)).det / (gram Q fun i => (eN i : V)).det := by
    rw [hd₁, hd₂, hHH']; field_simp
  constructor
  · intro h
    have := discQuot_bases Q h e₁ f₁ hN₁0
    rw [hratio] at this
    exact discQuot_of_bases Q eM eN this
  · intro h
    have := discQuot_bases Q h eM eN hN0
    rw [← hratio] at this
    exact discQuot_of_bases Q e₁ f₁ this

/-- **Complements in the same lattice** (O'Meara 1963, p. 271: "$dL_{(t-1)}\cdot dL_t = dK_{(t-1)}\cdot dK_t$"): if
$L = A \perp B = A' \perp B'$ are two splittings of the same lattice (regular pieces), then $dB/dB' \cong 1 \bmod
\mathfrak a$ implies $dA/dA' \cong 1 \bmod \mathfrak a$. -/
theorem discQuot_of_compl {L A B A' B' : Submodule R V} (hLfg : L.FG) (h : IsOrthSum Q L A B)
    (h' : IsOrthSum Q L A' B') (hA'reg : IsRegular Q A') (hBreg : IsRegular Q B) (hB'reg : IsRegular Q B')
    {X : Submodule R F} (hB : DiscQuotSqEquivMod Q B B' X) : DiscQuotSqEquivMod Q A A' X := by
  classical
  have fg : ∀ {M : Submodule R V}, M ≤ L → M.FG := fun hM => FG.of_le hLfg hM
  obtain ⟨eA⟩ := exists_basis (R := R) (F := F) (fg (h.sup_eq ▸ le_sup_left))
  obtain ⟨eB⟩ := exists_basis (R := R) (F := F) (fg (h.sup_eq ▸ le_sup_right))
  obtain ⟨eA'⟩ := exists_basis (R := R) (F := F) (fg (h'.sup_eq ▸ le_sup_left))
  obtain ⟨eB'⟩ := exists_basis (R := R) (F := F) (fg (h'.sup_eq ▸ le_sup_right))
  obtain ⟨e₁, he₁⟩ := exists_basis_isOrthSum Q h eA eB
  obtain ⟨e₂, he₂⟩ := exists_basis_isOrthSum Q h' eA' eB'
  -- `e₁`, `e₂` are bases of the same lattice; reindex `e₂` along an equivalence of index types
  have hcard : Fintype.card (Fin (finrank R A') ⊕ Fin (finrank R B')) =
      Fintype.card (Fin (finrank R A) ⊕ Fin (finrank R B)) := by
    rw [← finrank_eq_card_basis e₁, ← finrank_eq_card_basis e₂]
  set σ := Fintype.equivOfCardEq hcard
  obtain ⟨u, hu, hu'⟩ := det_gram_change Q e₁ (e₂.reindex σ)
  have hd₂ : (gram Q fun s => ((e₂.reindex σ) s : V)).det = (gram Q fun s => (e₂ s : V)).det := by
    simp only [Basis.reindex_apply]
    exact Matrix.det_submatrix_equiv_self σ.symm (gram Q fun s => (e₂ s : V))
  have hd₁' : (gram Q fun s => (e₁ s : V)).det = (gram Q fun i => (eA i : V)).det * (gram Q fun i => (eB i : V)).det := by
    rw [show (fun s => (e₁ s : V)) = Sum.elim (fun i => (eA i : V)) (fun k => (eB k : V)) from funext he₁]
    exact det_gram_sumElim Q h.orth _ _ (fun i => (eA i).2) (fun k => (eB k).2)
  have hd₂' : (gram Q fun s => (e₂ s : V)).det = (gram Q fun i => (eA' i : V)).det * (gram Q fun i => (eB' i : V)).det := by
    rw [show (fun s => (e₂ s : V)) = Sum.elim (fun i => (eA' i : V)) (fun k => (eB' k : V)) from funext he₂]
    exact det_gram_sumElim Q h'.orth _ _ (fun i => (eA' i).2) (fun k => (eB' k).2)
  rw [hd₂, hd₂', hd₁'] at hu'
  have hB0 := det_gram_ne_zero_of_isRegular Q hBreg eB
  have hB'0 := det_gram_ne_zero_of_isRegular Q hB'reg eB'
  have hA'0 := det_gram_ne_zero_of_isRegular Q hA'reg eA'
  have hBB := sqEquivMod_inv_one (discQuot_bases Q hB eB eB' hB'0)
  obtain ⟨w, hw⟩ := hu.exists_left_inv
  have hwF : algebraMap R F w * algebraMap R F u = 1 := by rw [← map_mul, hw, map_one]
  have key := sqEquivMod_sq_mul_one hBB (IsUnit.of_mul_eq_one u hw)
  refine discQuot_of_bases Q eA eA' ?_
  convert key using 1
  have huF : algebraMap R F u ≠ 0 := fun h0 => by rw [h0, mul_zero] at hwF; exact zero_ne_one hwF
  have hw' : algebraMap R F w = (algebraMap R F u)⁻¹ := eq_inv_of_mul_eq_one_left hwF
  rw [hw']
  field_simp
  linear_combination -hu'

end DVR

end QuadFormsKB.OMeara.Transfer28
