/-
# Eichler's mass formula for every class number

**Layer:** $F$ totally real (any class number $h_F$), $D = (a,b)_F$ totally definite, $\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$ a maximal order,
given by a presentation $\mathcal O = \{\sum_i\xi_if^{\mathcal O}_i : \xi_i \in \mathfrak a^{\mathcal O}_i\}$ (Steinitz; `exists_presentation_sub`; no basis of $\mathcal O$).

**Eichler's mass formula** (`eichler_mass_formula_nf`): with $\Lambda_{\mathcal O} = \frac{\rho_F}2\,c_{\mathcal O}/K$ (`massConstNF`; $c_{\mathcal O}$ the lattice constant of
the presented lattice $(\mathcal O, \operatorname{nrd})$, $K$ = `epsteinConst F 4 0`),
$$\Lambda_{\mathcal O}\sum_{[J]\ne0}\frac1{[\Gamma_J:\mathcal O_F^\times]} = h_F\,\rho_F\,\zeta_F(2)\prod_{\mathfrak p\in\operatorname{Ram}_f(D)}(1-N\mathfrak p^{-1}).$$
For $h_F = 1$ this is `eichler_mass_formula`; the factor $h_F$ is Voight's (Thm. 26.1.5 / 26.5.4 in general form).

*Proof (the class-group averaging).* The residue of a single class term $N(\operatorname{nrd}J)^{-s}E_J(s)$ is not available for $h_F > 1$
(only the class-weighted Epstein sum `epsteinClsSum` is controlled). $\mathrm{Cl}(F)$ acts on the finite set of left ideal classes by
$[J] \mapsto [\mathfrak a_cJ]$ ($\mathfrak a_c$ an integral ideal in the class $c$; `classScale`, injective), so for the class zeta functions
$G([J]) = \sum_{J'\sim J}N(\operatorname{nrd}J')^{-s}$,
$$h_F\sum_{x}G(x) = \sum_x\sum_{c}G(c\cdot x) = \sum_{[J]}[\Gamma_J:\mathcal O_F^\times]^{-1}N(\operatorname{nrd}J)^{-s}\sum_cN(\mathfrak c_c)^{-2s}E_{\mathfrak c_c^{-1}(\mathcal O:J)}(s),$$
using $N(\operatorname{nrd}\mathfrak aJ) = N\mathfrak a^2N(\operatorname{nrd}J)$, $(\mathcal O:\mathfrak aJ) = \mathfrak a^{-1}(\mathcal O:J)$, $\Gamma_{\mathfrak aJ} = \Gamma_J$ (`QuatIdealScaleNF`) and
representative independence $N(\lambda\mathfrak c)^{-2s}E_{(\lambda\mathfrak c)^{-1}L} = N(\mathfrak c)^{-2s}E_{\mathfrak c^{-1}L}$ (`epsteinLat_twist_principal`).
The inner sum is `epsteinClsSum`, with residue $\frac{\rho_F}2c_{(\mathcal O:J)}/K$ (`tendsto_sub_mul_epsteinClsSum`), and
$c_{(\mathcal O:J)} = N(\operatorname{nrd}J)^2c_{\mathcal O}$ (`latConst_colon`): $(\mathcal O:J) = \operatorname{nrd}(J)^{-1}\bar J$ (`mem_colon_iff_star`, from `Gen.mul_star_mem`),
$[\mathcal O:J] = N(\operatorname{nrd}J)^2$ (`Gen.card_quot_ideal`) and the covolume calculus of `LatCovolNF`.

Source: Voight, *Quaternion Algebras* (2021), Thm. 26.5.4 and (26.5.5)–(26.5.10) (right ideals, general $h_F$); the closed form
$2^{1-d}|\zeta_F(-1)|h_F\prod(N\mathfrak p-1)$ (Thm. 26.1.5 [unverified]) needs the functional equation and $\operatorname{disc}\mathcal O$ and is not formalized.
-/
import QuadFormsKB.Tamagawa.QuatIdealScaleNF
import QuadFormsKB.Tamagawa.LatCovolNF

open NumberField NumberField.InfinitePlace Quaternion Matrix Filter Topology
open scoped ENNReal Real nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.HilbertModular QuadFormsKB.AdditiveZeta QuadFormsKB.SphericalUnfold
  QuadFormsKB.IdeleClass QuadFormsKB.NFEuler QuadFormsKB.LatCovol

attribute [-instance] NumberField.RingOfIntegers.instAlgebra

namespace Gen

/-! ### Fractional-ideal bookkeeping -/

section FracBook

variable {F : Type} [Field F] [NumberField F]

/-- A nonzero integral ideal as an invertible fractional ideal. -/
def idealUnit (𝔫 : Ideal (𝓞 F)) (h𝔫 : 𝔫 ≠ ⊥) : FracIdeal F :=
  Units.mk0 (𝔫 : FractionalIdeal (𝓞 F)⁰ F) (FractionalIdeal.coeIdeal_ne_zero.2 h𝔫)

theorem coe_idealUnit (𝔫 : Ideal (𝓞 F)) (h𝔫 : 𝔫 ≠ ⊥) :
    ((idealUnit 𝔫 h𝔫 : FracIdeal F) : FractionalIdeal (𝓞 F)⁰ F) = (𝔫 : FractionalIdeal (𝓞 F)⁰ F) := rfl

theorem idealNorm_idealUnit (𝔫 : Ideal (𝓞 F)) (h𝔫 : 𝔫 ≠ ⊥) :
    idealNorm F (idealUnit 𝔫 h𝔫) = (Ideal.absNorm 𝔫 : ℝ) := by
  rw [idealNorm, coe_idealUnit, FractionalIdeal.coeIdeal_absNorm]; push_cast; rfl

/-- **$t \in \mathfrak n^{-1}\mathfrak b \iff \mathfrak nt \subseteq \mathfrak b$.** -/
theorem mem_inv_mul_iff (𝔫 : Ideal (𝓞 F)) (h𝔫 : 𝔫 ≠ ⊥) (𝔟 : FracIdeal F) (t : F) :
    t ∈ (((idealUnit 𝔫 h𝔫)⁻¹ * 𝔟 : FracIdeal F) : FractionalIdeal (𝓞 F)⁰ F) ↔
      ∀ r ∈ 𝔫, algebraMap (𝓞 F) F r * t ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
  set N : FractionalIdeal (𝓞 F)⁰ F := (𝔫 : FractionalIdeal (𝓞 F)⁰ F)
  have hN : N ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔫
  have hval : (((idealUnit 𝔫 h𝔫)⁻¹ * 𝔟 : FracIdeal F) : FractionalIdeal (𝓞 F)⁰ F) = N⁻¹ * 𝔟 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, coe_idealUnit]
  rw [hval]
  constructor
  · intro ht r hr
    have hrN : algebraMap (𝓞 F) F r ∈ N := FractionalIdeal.mem_coeIdeal_of_mem _ hr
    have := FractionalIdeal.mul_mem_mul hrN ht
    rwa [← mul_assoc, mul_inv_cancel₀ hN, one_mul] at this
  · intro h
    have hle : FractionalIdeal.spanSingleton (𝓞 F)⁰ t * N ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [FractionalIdeal.mul_le]
      intro i hi j hj
      obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
      rw [smul_mul_assoc, mul_comm]
      exact Submodule.smul_mem _ c (h r hr)
    have h2 : FractionalIdeal.spanSingleton (𝓞 F)⁰ t ≤ N⁻¹ * 𝔟 := by
      calc FractionalIdeal.spanSingleton (𝓞 F)⁰ t = FractionalIdeal.spanSingleton (𝓞 F)⁰ t * N * N⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hN, mul_one]
        _ ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) * N⁻¹ := mul_le_mul_left hle _
        _ = N⁻¹ * 𝔟 := mul_comm _ _
    exact h2 (FractionalIdeal.mem_spanSingleton_self _ t)

theorem latMem_twist_iff (𝔫 : Ideal (𝓞 F)) (h𝔫 : 𝔫 ≠ ⊥) {n : ℕ} (I : Fin n → FracIdeal F) (ξ : Fin n → F) :
    LatMem (twist (idealUnit 𝔫 h𝔫) I) ξ ↔ ∀ r ∈ 𝔫, LatMem I (algebraMap (𝓞 F) F r • ξ) := by
  unfold LatMem twist
  simp only [SetLike.mem_coe, mem_inv_mul_iff, Pi.smul_apply, smul_eq_mul]
  exact ⟨fun h r hr i => h i r hr, fun h i r hr => h r hr i⟩

end FracBook

/-! ### Presentations of lattices in $D$ -/

section Presentation

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a b : 𝓞 F}

theorem tup_sum_smul (ξ : Fin 4 → F) (f : Fin 4 → QuatF F a b) :
    tup (∑ i, ξ i • f i) = coordMat f *ᵥ ξ := by
  rw [← tupEquiv_apply, map_sum]
  ext r
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, coordMat,
    Matrix.of_apply, tupEquiv_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; rfl

/-- **Uniqueness of coordinates** in a linearly independent family. -/
theorem coord_unique {f : Fin 4 → QuatF F a b} (hli : LinearIndependent F f) {ξ η : Fin 4 → F}
    (h : ∑ i, ξ i • f i = ∑ i, η i • f i) : ξ = η := by
  funext i
  have h0 : ∑ j, (ξ j - η j) • f j = 0 := by simp only [sub_smul, Finset.sum_sub_distrib]; rw [h, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 i)

/-- Every element is a combination of a linearly independent 4-family. -/
theorem exists_coord {f : Fin 4 → QuatF F a b} (hli : LinearIndependent F f) (x : QuatF F a b) :
    ∃ ξ : Fin 4 → F, x = ∑ i, ξ i • f i := by
  have hcard : Fintype.card (Fin 4) = Module.finrank F (QuatF F a b) := by
    rw [Fintype.card_fin, QuaternionAlgebra.finrank_eq_four]
  set bf := basisOfLinearIndependentOfCardEqFinrank hli hcard
  refine ⟨fun i => bf.repr x i, ?_⟩
  conv_lhs => rw [← bf.sum_repr x]
  simp [bf]

/-- **The scaled presentation**: if $S = \{\sum\xi_if_i : \xi \in \bigoplus\mathfrak a_i\}$, then
$\{x : \mathfrak nx \subseteq S\} = \{\sum\xi_if_i : \xi \in \mathfrak n^{-1}\bigoplus\mathfrak a_i\}$. -/
theorem forall_smul_mem_iff_twist {S : Set (QuatF F a b)} {f : Fin 4 → QuatF F a b} {𝔞 : Fin 4 → FracIdeal F}
    (hmem : ∀ x, x ∈ S ↔ ∃ ξ : Fin 4 → F, LatMem 𝔞 ξ ∧ x = ∑ i, ξ i • f i) (hli : LinearIndependent F f)
    {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≠ ⊥) (x : QuatF F a b) :
    (∀ r ∈ 𝔫, r • x ∈ S) ↔ ∃ ξ : Fin 4 → F, LatMem (twist (idealUnit 𝔫 h𝔫) 𝔞) ξ ∧ x = ∑ i, ξ i • f i := by
  obtain ⟨ξ, rfl⟩ := exists_coord hli x
  have hsm : ∀ r : 𝓞 F, r • ∑ i, ξ i • f i = ∑ i, (algebraMap (𝓞 F) F r • ξ) i • f i := fun r => by
    rw [← algebraMap_smul F r, Finset.smul_sum]
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
  constructor
  · intro h
    refine ⟨ξ, (latMem_twist_iff 𝔫 h𝔫 𝔞 ξ).2 fun r hr => ?_, rfl⟩
    obtain ⟨η, hη, he⟩ := (hmem _).1 (h r hr)
    rw [hsm] at he
    rwa [coord_unique hli he]
  · rintro ⟨η, hη, he⟩ r hr
    rw [hsm, coord_unique hli he]
    exact (hmem _).2 ⟨_, (latMem_twist_iff 𝔫 h𝔫 𝔞 η).1 hη r hr, rfl⟩

/-- The submodule of $F^4$ given by an $\mathcal O_F$-submodule of $D$ in coordinates $1, i, j, k$. -/
def coordSub (M : Submodule (𝓞 F) (QuatF F a b)) : Submodule (𝓞 F) (Fin 4 → F) :=
  M.map ((tupEquiv a b).toLinearMap.restrictScalars (𝓞 F))

/-- **A Steinitz presentation of any $\mathcal O_F$-lattice in $D$** (generalizing `exists_presentation`). -/
theorem exists_presentation_sub {M : Submodule (𝓞 F) (QuatF F a b)} (hlat : (coordSub M).IsLattice F) :
    ∃ (f : Fin 4 → QuatF F a b) (𝔞 : Fin 4 → FracIdeal F), LinearIndependent F f ∧
      ∀ x : QuatF F a b, x ∈ M ↔ ∃ ξ : Fin 4 → F, LatMem 𝔞 ξ ∧ x = ∑ i, ξ i • f i := by
  classical
  obtain ⟨γ, 𝔠, hγ⟩ := Lattices.Steinitz.exists_eq_glImage_steinitzLat (m := 3) hlat
  obtain ⟨I, hI⟩ := exists_fracIdeal_of_steinitz hlat hγ
  let col : Fin 4 → (Fin 4 → F) := fun i => γ.val *ᵥ Pi.single i 1
  have hmemS : ∀ y : Fin 4 → F, y ∈ coordSub M ↔ ∃ x ∈ M, tup x = y := fun y => by
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  refine ⟨fun i => (tupEquiv a b).symm (col i), steinitzIdeals I, ?_, fun x => ?_⟩
  · have hli1 : LinearIndependent F col := by
      have := (Pi.basisFun F (Fin 4)).linearIndependent.map' (Matrix.mulVecLin γ.val) (by
        rw [LinearMap.ker_eq_bot]
        intro u v huv
        have h2 := congrArg (fun z => γ⁻¹.val *ᵥ z) huv
        simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using h2)
      convert this using 1
      funext i
      simp [col, Pi.basisFun_apply]
    exact hli1.map' (tupEquiv a b).symm.toLinearMap (by simp)
  · have hsum : ∀ ξ : Fin 4 → F, tupEquiv a b (∑ i, ξ i • (tupEquiv a b).symm (col i)) = γ.val *ᵥ ξ := by
      intro ξ
      simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply, col]
      have hξ : ξ = ∑ i, ξ i • (Pi.single i (1 : F) : Fin 4 → F) := by
        ext j; simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [hξ]
      rw [Matrix.mulVec_sum]
      exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_smul _ _ _).symm
    constructor
    · intro hx
      have h1 : tup x ∈ coordSub M := (hmemS _).2 ⟨x, hx, rfl⟩
      rw [hγ] at h1
      obtain ⟨y, hy, hyx⟩ := Lattices.mem_glImage.1 h1
      refine ⟨y, (latMem_steinitzIdeals_iff hI).2 hy, ?_⟩
      apply (tupEquiv a b).injective
      rw [hsum]; exact hyx.symm
    · rintro ⟨ξ, hξ, rfl⟩
      have hy := (latMem_steinitzIdeals_iff hI).1 hξ
      have h1 : γ.val *ᵥ ξ ∈ coordSub M := by
        rw [hγ]; exact Lattices.mulVec_mem_glImage hy
      obtain ⟨x', hx', hxx⟩ := (hmemS _).1 h1
      have : x' = ∑ i, ξ i • (tupEquiv a b).symm (col i) := by
        apply (tupEquiv a b).injective
        rw [hsum]; exact hxx
      rw [← this]; exact hx'

end Presentation

/-! ### Covolumes of presented lattices in $D$ -/

section CovolD

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a b : 𝓞 F}

/-- The Gram matrix $\operatorname{diag}(1,-a,-b,ab)$ of $\operatorname{nrd}$ in the coordinates $1, i, j, k$. -/
abbrev nrdGram (a b : 𝓞 F) : Matrix (Fin 4) (Fin 4) F := Matrix.diagonal (nrdDiag a b)

theorem isTotPosGram_nrdGram (hdef : IsTotDefinite a b) : IsTotPosGram (nrdGram (F := F) a b) := by
  intro v
  obtain ⟨ha, hb⟩ := hdef (realEmb F v)
  rw [Matrix.diagonal_map (map_zero _), Matrix.posDef_diagonal_iff]
  intro r
  fin_cases r <;> simp [nrdDiag]
  · linarith
  · linarith
  · exact mul_pos_of_neg_of_neg ha hb

theorem gramMat_eq_nrdGram (f : Fin 4 → QuatF F a b) :
    gramMat f = (coordMat f)ᵀ * nrdGram a b * coordMat f := gramMat_eq_coordMat f

/-- The coordinate image of a presented set is the presented lattice of `LatCovolNF`. -/
theorem mem_presGrp_coordMat {S : Set (QuatF F a b)} {f : Fin 4 → QuatF F a b} {𝔞 : Fin 4 → FracIdeal F}
    (hmem : ∀ x, x ∈ S ↔ ∃ ξ : Fin 4 → F, LatMem 𝔞 ξ ∧ x = ∑ i, ξ i • f i) (y : Fin 4 → F) :
    y ∈ presGrp (coordMat f) 𝔞 ↔ ∃ x ∈ S, tup x = y := by
  rw [mem_presGrp]
  constructor
  · rintro ⟨ξ, hξ, rfl⟩
    exact ⟨_, (hmem _).2 ⟨ξ, hξ, rfl⟩, tup_sum_smul ξ f⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨ξ, hξ, rfl⟩ := (hmem x).1 hx
    exact ⟨ξ, hξ, tup_sum_smul ξ f⟩

/-- **Monotonicity of the lattice constant**: for presented sets $S \subseteq S'$,
$c_{S'} = c_S\,[S':S]$ (index of the coordinate lattices). -/
theorem latConst_eq_mul_relIndex_D (hdef : IsTotDefinite a b) {S S' : Set (QuatF F a b)}
    {f f' : Fin 4 → QuatF F a b} {𝔞 𝔞' : Fin 4 → FracIdeal F}
    (hmem : ∀ x, x ∈ S ↔ ∃ ξ : Fin 4 → F, LatMem 𝔞 ξ ∧ x = ∑ i, ξ i • f i)
    (hmem' : ∀ x, x ∈ S' ↔ ∃ ξ : Fin 4 → F, LatMem 𝔞' ξ ∧ x = ∑ i, ξ i • f' i)
    (hli : LinearIndependent F f) (hli' : LinearIndependent F f') (hSS : S ⊆ S') :
    latConst (gramMat f') 𝔞' =
      latConst (gramMat f) 𝔞 * ((presGrp (coordMat f) 𝔞).relIndex (presGrp (coordMat f') 𝔞') : ℝ) := by
  have hle : presGrp (coordMat f) 𝔞 ≤ presGrp (coordMat f') 𝔞' := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_presGrp_coordMat hmem y).1 hy
    exact (mem_presGrp_coordMat hmem' _).2 ⟨x, hSS hx, rfl⟩
  rw [gramMat_eq_nrdGram, gramMat_eq_nrdGram]
  exact latConst_eq_mul_relIndex (isTotPosGram_nrdGram hdef) (det_coordMat_ne_zero hli) (det_coordMat_ne_zero hli') hle

/-- **Two presentations of the same set have the same lattice constant.** -/
theorem latConst_eq_of_pres (hdef : IsTotDefinite a b) {S : Set (QuatF F a b)}
    {f f' : Fin 4 → QuatF F a b} {𝔞 𝔞' : Fin 4 → FracIdeal F}
    (hmem : ∀ x, x ∈ S ↔ ∃ ξ : Fin 4 → F, LatMem 𝔞 ξ ∧ x = ∑ i, ξ i • f i)
    (hmem' : ∀ x, x ∈ S ↔ ∃ ξ : Fin 4 → F, LatMem 𝔞' ξ ∧ x = ∑ i, ξ i • f' i)
    (hli : LinearIndependent F f) (hli' : LinearIndependent F f') :
    latConst (gramMat f') 𝔞' = latConst (gramMat f) 𝔞 := by
  rw [latConst_eq_mul_relIndex_D hdef hmem hmem' hli hli' subset_rfl]
  have : presGrp (coordMat f) 𝔞 = presGrp (coordMat f') 𝔞' := by
    ext y; rw [mem_presGrp_coordMat hmem, mem_presGrp_coordMat hmem']
  rw [this, AddSubgroup.relIndex_self, Nat.cast_one, mul_one]

theorem nrdBil_star (x y : QuatF F a b) : nrdBil (star x) (star y) = nrdBil x y := by
  simp only [nrdBil, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
    QuaternionAlgebra.imK_star]
  ring

theorem gramMat_star (g : Fin 4 → QuatF F a b) : gramMat (fun i => star (g i)) = gramMat g := by
  ext i j; simp only [gramMat, Matrix.of_apply, nrdBil_star]

theorem linearIndependent_star {g : Fin 4 → QuatF F a b} (hli : LinearIndependent F g) :
    LinearIndependent F fun i => star (g i) := by
  let σ : QuatF F a b ≃ₗ[F] QuatF F a b :=
    { toFun := star
      invFun := star
      map_add' := star_add
      map_smul' := fun c x => QuaternionAlgebra.star_smul c x
      left_inv := star_star
      right_inv := star_star }
  exact hli.map' σ.toLinearMap σ.ker

end CovolD

/-! ### The colon lattice $(\mathcal O:J) = \operatorname{nrd}(J)^{-1}\bar J$ and its lattice constant -/

section Colon

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]}

/-- **$(\mathcal O : J) = \{x : \operatorname{nrd}(J)\,\bar x \subseteq J\}$** for a maximal order (i.e. $(\mathcal O:J) = \overline{\operatorname{nrd}(J)^{-1}J}$).
($\Rightarrow$) $\operatorname{nrd}(y)\bar x = \overline{yx}\,y$; ($\Leftarrow$) $1 \in \operatorname{nrd}(J)^{-1}\operatorname{nrd}(J)$ and `Gen.mul_star_mem`. -/
theorem mem_colon_iff_star (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O}
    (hJ : leftNrdIdeal J ≠ ⊥) (x : QuatF F a b) :
    x ∈ colon J ↔ ∀ m ∈ leftNrdIdeal J, m • star x ∈ idealSet J := by
  constructor
  · intro hx m hm
    induction hm using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨y, hyJ, hr⟩ := hr
      have hyx : (y : QuatF F a b) * x ∈ O := hx _ (coe_mem_idealSet.2 hyJ)
      have key : r • star x = star ((y : QuatF F a b) * x) * y := by
        rw [star_mul, mul_assoc, star_mul_eq_nrd, ← hr, QuaternionAlgebra.mul_coe_eq_smul,
          algebraMap_smul]
      rw [key]
      exact mul_mem_idealSet (star_mem_of_isOrder hO.1 hyx) (coe_mem_idealSet.2 hyJ)
    | zero => rw [zero_smul]; exact zero_mem_idealSet J
    | add m m' _ _ h h' => rw [add_smul]; exact add_mem_idealSet h h'
    | smul c m _ h => rw [smul_eq_mul, mul_smul]; exact (idealSub J).smul_mem c h
  · intro h y hy
    set N : FractionalIdeal (𝓞 F)⁰ F := (leftNrdIdeal J : FractionalIdeal (𝓞 F)⁰ F)
    have hN : N ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hJ
    have h1 : (1 : F) ∈ N⁻¹ * N := by
      rw [inv_mul_cancel₀ hN]; exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
    have key : ∀ z ∈ N⁻¹ * N, z • (y * x) ∈ O := by
      intro z hz
      refine FractionalIdeal.mul_induction_on (C := fun z => z • (y * x) ∈ O) hz ?_ ?_
      · intro i hi j hj
        obtain ⟨m, hm, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
        have hc : ∀ m' ∈ leftNrdIdeal J, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = i * algebraMap (𝓞 F) F m' := by
          intro m' hm'
          have : i * algebraMap (𝓞 F) F m' ∈ N⁻¹ * N :=
            FractionalIdeal.mul_mem_mul hi (FractionalIdeal.mem_coeIdeal_of_mem _ hm')
          rw [inv_mul_cancel₀ hN] at this
          exact (FractionalIdeal.mem_one_iff _).1 this
        have hw := h m hm
        have := mul_star_mem ha hb hO hJ hc hw hy
        have e : star (m • star x) = algebraMap (𝓞 F) F m • x := by
          rw [← algebraMap_smul F m (star x), QuaternionAlgebra.star_smul, star_star]
        rw [e, mul_smul_comm, smul_smul] at this
        exact this
      · intro u w hu hw
        rw [add_smul]; exact O.add_mem hu hw
    simpa using key 1 h1

variable [IsTotallyReal F]

/-- **The colon lattice in a presentation of $J$**: $(\mathcal O:J) = \{\sum\xi_i\bar g_i : \xi \in \mathfrak n^{-1}\bigoplus\mathfrak b_i\}$ if
$J = \{\sum\xi_ig_i : \xi \in \bigoplus\mathfrak b_i\}$, $\mathfrak n = \operatorname{nrd}J$. -/
theorem colon_pres_star (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O}
    (hJ : leftNrdIdeal J ≠ ⊥) {g : Fin 4 → QuatF F a b} {𝔟 : Fin 4 → FracIdeal F}
    (hmemJ : ∀ x, x ∈ idealSet J ↔ ∃ ξ : Fin 4 → F, LatMem 𝔟 ξ ∧ x = ∑ i, ξ i • g i)
    (hliJ : LinearIndependent F g) (x : QuatF F a b) :
    x ∈ colon J ↔ ∃ ξ : Fin 4 → F, LatMem (twist (idealUnit _ hJ) 𝔟) ξ ∧ x = ∑ i, ξ i • star (g i) := by
  rw [mem_colon_iff_star ha hb hO hJ, forall_smul_mem_iff_twist hmemJ hliJ hJ]
  have hst : ∀ ξ : Fin 4 → F, star (∑ i, ξ i • g i) = ∑ i, ξ i • star (g i) := fun ξ => by
    rw [star_sum]; exact Finset.sum_congr rfl fun i _ => QuaternionAlgebra.star_smul _ _
  refine exists_congr fun ξ => and_congr_right fun _ => ?_
  constructor
  · intro h; rw [← hst, ← h, star_star]
  · intro h; rw [h, ← hst, star_star]

theorem isLattice_coordSub_ideal (hO : IsOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥) :
    (coordSub (idealSub J)).IsLattice F where
  fg := by
    refine Submodule.FG.map _ ?_
    have hN : IsNoetherian (𝓞 F) (Subalgebra.toSubmodule O) := isNoetherian_of_fg_of_noetherian _ hO.fg
    exact @Submodule.FG.of_le_of_isNoetherian _ _ _ _ _ _ _ hN (fun x hx => idealSet_subset J hx)
  span_eq_top := by
    obtain ⟨n, hn𝔫, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    have hnJ : algebraMap (𝓞 F) O n ∈ J := algebraMap_mem_of_mem_leftNrdIdeal hO J hn𝔫
    have hnF : algebraMap (𝓞 F) F n ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hn
    have h1 := (isLattice_orderSub (O := O) hO).span_eq_top
    refine eq_top_iff.2 (h1.ge.trans (Submodule.span_le.2 ?_))
    rintro _ ⟨x, hx, rfl⟩
    have hmem : n • x ∈ idealSub J := by
      have h1 : ((⟨x, hx⟩ * algebraMap (𝓞 F) O n : O) : QuatF F a b) ∈ idealSet J :=
        coe_mem_idealSet.2 (J.mul_mem_left _ hnJ)
      have h2 : ((⟨x, hx⟩ * algebraMap (𝓞 F) O n : O) : QuatF F a b) = n • x := by
        rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ← Algebra.commutes, ← Algebra.smul_def]
      rw [← h2]; exact h1
    have h2 : (tupEquiv a b).toLinearMap.restrictScalars (𝓞 F) (n • x) ∈ Submodule.span F (coordSub (idealSub J) : Set (Fin 4 → F)) :=
      Submodule.subset_span ⟨n • x, hmem, rfl⟩
    have h3 : (tupEquiv a b).toLinearMap.restrictScalars (𝓞 F) x =
        (algebraMap (𝓞 F) F n)⁻¹ • (tupEquiv a b).toLinearMap.restrictScalars (𝓞 F) (n • x) := by
      simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
      rw [← algebraMap_smul F n x, map_smul, smul_smul, inv_mul_cancel₀ hnF, one_smul]
    rw [SetLike.mem_coe, h3]
    exact Submodule.smul_mem _ _ h2

/-- **The index of $J$ in $\mathcal O$ in coordinates**: the relative index of the presented lattices of $J \subseteq \mathcal O$ is
$\#(\mathcal O/J)$. -/
theorem relIndex_ideal_order {fO : Fin 4 → QuatF F a b} {𝔞O : Fin 4 → FracIdeal F}
    (hmemO : ∀ x, x ∈ (O : Set (QuatF F a b)) ↔ ∃ ξ : Fin 4 → F, LatMem 𝔞O ξ ∧ x = ∑ i, ξ i • fO i)
    {J : Ideal O} {g : Fin 4 → QuatF F a b} {𝔟 : Fin 4 → FracIdeal F}
    (hmemJ : ∀ x, x ∈ idealSet J ↔ ∃ ξ : Fin 4 → F, LatMem 𝔟 ξ ∧ x = ∑ i, ξ i • g i) :
    (presGrp (coordMat g) 𝔟).relIndex (presGrp (coordMat fO) 𝔞O) = Nat.card (O ⧸ J) := by
  let φ : O →+ (Fin 4 → F) :=
    ((tupEquiv a b).toLinearMap.toAddMonoidHom).comp (Subalgebra.val O).toAddMonoidHom
  have hφ : ∀ z : O, φ z = tup (z : QuatF F a b) := fun z => rfl
  have hinj : Function.Injective φ := fun z z' h => by
    rw [hφ, hφ, ← tupEquiv_apply, ← tupEquiv_apply] at h
    exact Subtype.ext ((tupEquiv a b).injective h)
  have h1 : presGrp (coordMat g) 𝔟 = J.toAddSubgroup.map φ := by
    ext y
    rw [mem_presGrp_coordMat hmemJ, AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, ⟨hxO, hxJ⟩, rfl⟩; exact ⟨⟨x, hxO⟩, hxJ, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, coe_mem_idealSet.2 hz, rfl⟩
  have h2 : presGrp (coordMat fO) 𝔞O = (⊤ : AddSubgroup O).map φ := by
    ext y
    rw [mem_presGrp_coordMat hmemO, AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, trivial, rfl⟩
    · rintro ⟨z, -, rfl⟩; exact ⟨z, z.2, rfl⟩
  rw [h1, h2, AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_top_right]
  rfl

/-- **The lattice constant of the colon lattice**: $c_{(\mathcal O:J)} = N(\operatorname{nrd}J)^2\,c_{\mathcal O}$, for any presentations of
$(\mathcal O:J)$ and of $\mathcal O$ ($\mathcal O$ maximal, $D$ totally definite). -/
theorem latConst_colon (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) (hO : IsMaximalOrder (𝓞 F) F O)
    {fO : Fin 4 → QuatF F a b} {𝔞O : Fin 4 → FracIdeal F} (hliO : LinearIndependent F fO)
    (hmemO : ∀ x, x ∈ (O : Set (QuatF F a b)) ↔ ∃ ξ : Fin 4 → F, LatMem 𝔞O ξ ∧ x = ∑ i, ξ i • fO i)
    {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥) {f : Fin 4 → QuatF F a b} {𝔞 : Fin 4 → FracIdeal F}
    (hli : LinearIndependent F f) (hmem : ∀ x, x ∈ colon J ↔ ∃ ξ : Fin 4 → F, LatMem 𝔞 ξ ∧ x = ∑ i, ξ i • f i) :
    latConst (gramMat f) 𝔞 = (Ideal.absNorm (leftNrdIdeal J) : ℝ) ^ 2 * latConst (gramMat fO) 𝔞O := by
  obtain ⟨g, 𝔟, hliJ, hmemJ⟩ := exists_presentation_sub (isLattice_coordSub_ideal hO.1 hJ)
  have hmemJ' : ∀ x, x ∈ idealSet J ↔ ∃ ξ : Fin 4 → F, LatMem 𝔟 ξ ∧ x = ∑ i, ξ i • g i := hmemJ
  -- (O : J) = nrd(J)⁻¹ J̄
  have h1 : latConst (gramMat f) 𝔞 = latConst (gramMat fun i => star (g i)) (twist (idealUnit _ hJ) 𝔟) :=
    (latConst_eq_of_pres hdef (colon_pres_star ha hb hO hJ hmemJ' hliJ) hmem (linearIndependent_star hliJ) hli)
  rw [gramMat_star, latConst_twist, idealNorm_idealUnit] at h1
  -- J ⊆ O with index N(nrd J)²
  have h2 := latConst_eq_mul_relIndex_D hdef hmemJ' hmemO hliJ hliO (idealSet_subset J)
  have hc : Nat.card (O ⧸ J) = Ideal.absNorm (leftNrdIdeal J) ^ 2 := card_quot_ideal ha hb hO hJ
  rw [relIndex_ideal_order hmemO hmemJ', hc] at h2
  have hN : (0 : ℝ) < Ideal.absNorm (leftNrdIdeal J) := by
    exact_mod_cast Nat.pos_of_ne_zero fun h => hJ (Ideal.absNorm_eq_zero_iff.1 h)
  rw [h1, h2]
  push_cast
  field_simp

end Colon

/-! ### Representative independence of the class terms -/

section RepIndep

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-- $\eta \mapsto \lambda\eta$, $(\lambda\mathfrak c)^{-1}L \setminus 0 \to \mathfrak c^{-1}L \setminus 0$. -/
def latPtScale (I : Fin n → FracIdeal F) (l : Fˣ) (𝔠 : FracIdeal F) :
    LatPt (twist (principalSMulFin F l 𝔠) I) ≃ LatPt (twist 𝔠 I) where
  toFun η := ⟨(l : F) • η.1, smul_ne_zero l.ne_zero η.2.1, (latMem_twist_principal I l 𝔠 η.1).1 η.2.2⟩
  invFun ζ := ⟨(l : F)⁻¹ • ζ.1, smul_ne_zero (inv_ne_zero l.ne_zero) ζ.2.1,
    (latMem_twist_principal I l 𝔠 _).2 (by rw [smul_smul, mul_inv_cancel₀ l.ne_zero, one_smul]; exact ζ.2.2)⟩
  left_inv η := Subtype.ext (by simp only; rw [smul_smul, inv_mul_cancel₀ l.ne_zero, one_smul])
  right_inv ζ := Subtype.ext (by simp only; rw [smul_smul, mul_inv_cancel₀ l.ne_zero, one_smul])

theorem latPtScale_val (I : Fin n → FracIdeal F) (l : Fˣ) (𝔠 : FracIdeal F)
    (η : LatPt (twist (principalSMulFin F l 𝔠) I)) : (latPtScale I l 𝔠 η).1 = (l : F) • η.1 := rfl

/-- The orbit spaces correspond. -/
def latPtScaleOrbit (I : Fin n → FracIdeal F) (l : Fˣ) (𝔠 : FracIdeal F) :
    MulAction.orbitRel.Quotient (unitsF F) (LatPt (twist (principalSMulFin F l 𝔠) I)) ≃
      MulAction.orbitRel.Quotient (unitsF F) (LatPt (twist 𝔠 I)) :=
  Quotient.congr (latPtScale I l 𝔠) fun η η' => by
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨u, Subtype.ext ?_⟩
      have hu' : u • η' = η := hu
      rw [smul_latPt_val, latPtScale_val, latPtScale_val, ← hu', smul_latPt_val, smul_comm]
    · rintro ⟨u, hu⟩
      refine ⟨u, Subtype.ext ?_⟩
      have hu' : u • latPtScale I l 𝔠 η' = latPtScale I l 𝔠 η := hu
      have h1 : (l : F) • (((u : Fˣ) : F) • η'.1) = (l : F) • η.1 := by
        have := congrArg Subtype.val hu'
        rw [smul_latPt_val, latPtScale_val, latPtScale_val, smul_comm] at this
        exact this
      rw [smul_latPt_val]
      exact smul_right_injective _ l.ne_zero h1

theorem abs_norm_unitsF (u : unitsF F) : |((Algebra.norm ℚ ((u : Fˣ) : F) : ℚ) : ℝ)| = 1 := by
  obtain ⟨w, hw⟩ := u.2
  rw [← hw]
  exact abs_norm_unit_cls w

/-- **$E_{\mathfrak c^{-1}L}(t) = |N\lambda|^{-2t}E_{(\lambda\mathfrak c)^{-1}L}(t)$.** -/
theorem epsteinLat_twist_principal (A : Matrix (Fin n) (Fin n) F) (I : Fin n → FracIdeal F) (l : Fˣ)
    (𝔠 : FracIdeal F) (t : ℝ) :
    epsteinLat A (twist 𝔠 I) t = ENNReal.ofReal (|((Algebra.norm ℚ (l : F) : ℚ) : ℝ)| ^ (-(2 * t))) *
      epsteinLat A (twist (principalSMulFin F l 𝔠) I) t := by
  set e := latPtScaleOrbit I l 𝔠
  unfold epsteinLat
  rw [← e.tsum_eq, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun q => ?_
  obtain ⟨u, hu⟩ : ∃ u : unitsF F, u • latPtScale I l 𝔠 q.out = (e q).out := by
    have : (Quotient.mk _ (e q).out : MulAction.orbitRel.Quotient (unitsF F) (LatPt (twist 𝔠 I))) =
        Quotient.mk _ (latPtScale I l 𝔠 q.out) := by
      rw [Quotient.out_eq]
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    exact Quotient.exact this
  have hN : |((Algebra.norm ℚ (l : F) : ℚ) : ℝ)| ≠ 0 :=
    abs_ne_zero.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℚ)).2 l.ne_zero)
  have h1 : |((Algebra.norm ℚ (qv A (e q).out.1) : ℚ) : ℝ)| =
      |((Algebra.norm ℚ (l : F) : ℚ) : ℝ)| ^ 2 * |((Algebra.norm ℚ (qv A q.out.1) : ℚ) : ℝ)| := by
    rw [← hu, smul_latPt_val, latPtScale_val, abs_norm_qv_smul_cls, abs_norm_qv_smul_cls, abs_norm_unitsF,
      one_pow, one_mul]
  rw [h1, Real.mul_rpow (pow_nonneg (abs_nonneg _) 2) (abs_nonneg _),
    ENNReal.ofReal_mul (Real.rpow_nonneg (pow_nonneg (abs_nonneg _) 2) _)]
  congr 2
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  push_cast
  ring_nf

/-- **Representative independence**: $N(\lambda\mathfrak c)^{-2t}E_{(\lambda\mathfrak c)^{-1}L}(t) = N(\mathfrak c)^{-2t}E_{\mathfrak c^{-1}L}(t)$. -/
theorem idealNorm_mul_epsteinLat_principal (A : Matrix (Fin n) (Fin n) F) (I : Fin n → FracIdeal F) (l : Fˣ)
    (𝔠 : FracIdeal F) (t : ℝ) :
    ENNReal.ofReal (idealNorm F (principalSMulFin F l 𝔠) ^ (-(2 * t))) *
        epsteinLat A (twist (principalSMulFin F l 𝔠) I) t =
      ENNReal.ofReal (idealNorm F 𝔠 ^ (-(2 * t))) * epsteinLat A (twist 𝔠 I) t := by
  rw [epsteinLat_twist_principal A I l 𝔠 t, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (idealNorm_pos F 𝔠).le _), idealNorm_principalSMulFin, Real.mul_rpow (abs_nonneg _) (idealNorm_pos F 𝔠).le]
  congr 2
  ring

end RepIndep

/-! ### Class zeta functions and the class-group action -/

section ClassZeta

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]}

/-- **The class zeta function** $G_x(s) = \sum_{J'\in x}N(\operatorname{nrd}J')^{-s}$ of a left ideal class $x$. -/
def classZeta (x : Quotient (idealSetoid O)) (s : ℝ) : ℝ≥0∞ :=
  ∑' J' : {J' : Ideal O // IdealRel x.out J'}, nrdTerm J'.1 s

theorem classZeta_mk (J : Ideal O) (s : ℝ) :
    classZeta (Quotient.mk (idealSetoid O) J) s = ∑' J' : {J' : Ideal O // IdealRel J J'}, nrdTerm J'.1 s := by
  have hrel : IdealRel (Quotient.mk (idealSetoid O) J).out J :=
    Quotient.exact (s := idealSetoid O) (Quotient.out_eq (Quotient.mk (idealSetoid O) J))
  unfold classZeta
  exact (Equiv.subtypeEquivRight fun J' => ⟨fun h => hrel.symm.trans h, fun h => hrel.trans h⟩).tsum_eq
    (fun J' => nrdTerm J'.1 s)

theorem nrdTerm_bot_nf {s : ℝ} (hs : s ≠ 0) : nrdTerm (⊥ : Ideal O) s = 0 := by
  unfold nrdTerm
  have h : leftNrdIdeal (⊥ : Ideal O) = ⊥ := by
    unfold leftNrdIdeal
    rw [eq_bot_iff, Ideal.span_le]
    rintro r ⟨x, hx, hr⟩
    rw [(Submodule.mem_bot _).1 hx] at hr
    simp only [SetLike.mem_coe, Submodule.mem_bot]
    have : algebraMap (𝓞 F) F r = 0 := by rw [hr]; simp [nrd]
    exact (map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 this
  rw [h, Ideal.absNorm_bot, Nat.cast_zero, Real.zero_rpow (neg_ne_zero.2 hs), ENNReal.ofReal_zero]

theorem idealSet_bot_nf : idealSet (⊥ : Ideal O) = {0} := by
  ext x
  simp only [idealSet, Set.mem_ofPred_eq, Submodule.mem_bot, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, h⟩; exact congrArg Subtype.val h
  · rintro rfl; exact ⟨O.zero_mem, rfl⟩

theorem eq_bot_of_idealRel_bot_nf {J' : Ideal O} (h : IdealRel (⊥ : Ideal O) J') : J' = ⊥ := by
  obtain ⟨β, hβ⟩ := h
  apply idealSet_injective
  rw [hβ, idealSet_bot_nf]
  ext x
  simp [rTrans]

theorem classZeta_mk_bot {s : ℝ} (hs : s ≠ 0) : classZeta (Quotient.mk (idealSetoid O) (⊥ : Ideal O)) s = 0 := by
  rw [classZeta_mk]
  refine ENNReal.tsum_eq_zero.2 fun J' => ?_
  rw [eq_bot_of_idealRel_bot_nf J'.2]; exact nrdTerm_bot_nf hs

theorem scaleIdeal_bot (𝔞 : Ideal (𝓞 F)) : scaleIdeal 𝔞 (⊥ : Ideal O) = ⊥ := by
  apply idealSet_injective
  rw [idealSet_scaleIdeal, idealSet_bot_nf]
  have : scaleSet 𝔞 ({0} : Set (QuatF F a b)) = ⊥ := by
    rw [scaleSet, Submodule.span_eq_bot]
    rintro _ ⟨r, -, y, hy, rfl⟩
    rw [Set.mem_singleton_iff.1 hy, smul_zero]
  rw [this]; rfl

/-- The class $N(\operatorname{nrd}\mathfrak aJ)^{-s} = N\mathfrak a^{-2s}N(\operatorname{nrd}J)^{-s}$. -/
theorem nrdTerm_scaleIdeal (hO : IsOrder (𝓞 F) F O) {𝔞 : Ideal (𝓞 F)} (h𝔞 : 𝔞 ≠ ⊥) (J : Ideal O) (s : ℝ) :
    nrdTerm (scaleIdeal 𝔞 J) s =
      ENNReal.ofReal (idealNorm F (idealUnit 𝔞 h𝔞) ^ (-(2 * s))) * nrdTerm J s := by
  unfold nrdTerm
  rw [absNorm_leftNrdIdeal_scaleIdeal hO, idealNorm_idealUnit, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  push_cast
  ring_nf

variable [IsTotallyReal F]

/-- **The class zeta function of $\mathfrak aJ$** in terms of the presented colon lattice of $J$:
$G_{[\mathfrak aJ]}(s) = [\Gamma_J:\mathcal O_F^\times]^{-1}N(\operatorname{nrd}J)^{-s}\cdot N\mathfrak a^{-2s}E_{\mathfrak a^{-1}(\mathcal O:J)}(s)$. -/
theorem classZeta_scaleIdeal (hdef : IsTotDefinite a b) (hO : IsOrder (𝓞 F) F O) (hstd : stdOrder F a b ≤ O)
    {𝔞 : Ideal (𝓞 F)} (h𝔞 : 𝔞 ≠ ⊥) {J : Ideal O} (hJ : J ≠ ⊥) {f : Fin 4 → QuatF F a b}
    {𝔞s : Fin 4 → FracIdeal F} (hli : LinearIndependent F f)
    (hmem : ∀ x, x ∈ colon J ↔ ∃ ξ : Fin 4 → F, LatMem 𝔞s ξ ∧ x = ∑ i, ξ i • f i) (s : ℝ) :
    classZeta (Quotient.mk (idealSetoid O) (scaleIdeal 𝔞 J)) s =
      (((centralUnitsIn (R := 𝓞 F) J).index : ℝ≥0∞))⁻¹ * (nrdTerm J s *
        (ENNReal.ofReal (idealNorm F (idealUnit 𝔞 h𝔞) ^ (-(2 * s))) *
          epsteinLat (gramMat f) (twist (idealUnit 𝔞 h𝔞) 𝔞s) s)) := by
  have hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0 := fun x hx => eq_zero_of_nrd_eq_zero hdef hx
  have hJ' : leftNrdIdeal J ≠ ⊥ := leftNrdIdeal_ne_bot hO hdiv hJ
  have h𝔞J : scaleIdeal 𝔞 J ≠ ⊥ := fun h => by
    have := leftNrdIdeal_scaleIdeal_ne_bot hO h𝔞 hJ'
    rw [h] at this
    exact this (by
      unfold leftNrdIdeal; rw [eq_bot_iff, Ideal.span_le]
      rintro r ⟨x, hx, hr⟩
      rw [(Submodule.mem_bot _).1 hx] at hr
      simp only [SetLike.mem_coe, Submodule.mem_bot]
      have : algebraMap (𝓞 F) F r = 0 := by rw [hr]; simp [nrd]
      exact (map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 this)
  have hfin : (centralUnitsIn (R := 𝓞 F) (scaleIdeal 𝔞 J)).FiniteIndex :=
    finiteIndex_centralUnitsIn (O := O) hdef hO hstd h𝔞J
  have hmem' : ∀ x, x ∈ colon (scaleIdeal 𝔞 J) ↔
      ∃ ξ : Fin 4 → F, LatMem (twist (idealUnit 𝔞 h𝔞) 𝔞s) ξ ∧ x = ∑ i, ξ i • f i := fun x => by
    rw [colon_scaleIdeal]; exact forall_smul_mem_iff_twist hmem hli h𝔞 x
  have h1 := index_mul_tsum_class_nrd hO (scaleIdeal 𝔞 J) s
  rw [epsteinSum_eq_epsteinLat hmem' hli hdiv s, nrdTerm_scaleIdeal hO h𝔞, index_centralUnitsIn_scaleIdeal h𝔞]
    at h1
  have hi0 : ((centralUnitsIn (R := 𝓞 F) J).index : ℝ≥0∞) ≠ 0 := by
    rw [← index_centralUnitsIn_scaleIdeal h𝔞]; exact_mod_cast hfin.index_ne_zero
  rw [classZeta_mk]
  calc _ = (((centralUnitsIn (R := 𝓞 F) J).index : ℝ≥0∞))⁻¹ * (((centralUnitsIn (R := 𝓞 F) J).index : ℝ≥0∞) *
        ∑' J' : {J' : Ideal O // IdealRel (scaleIdeal 𝔞 J) J'}, nrdTerm J'.1 s) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hi0 (ENNReal.natCast_ne_top _), one_mul]
    _ = _ := by rw [h1]; ring

end ClassZeta

/-! ### Eichler's mass formula with the class number -/

section Mass

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]}

/-- **The mass constant of a presented maximal order**: $\Lambda_{\mathcal O} = \frac{\rho_F}2\,c_{\mathcal O}/K$, $c_{\mathcal O}$ the lattice constant of
$\mathcal O = \bigoplus_i\mathfrak a_if_i$ with the Gram matrix of $\operatorname{nrd}$ in $f$, $K$ = `epsteinConst F 4 0`. -/
def massConstNF (f : Fin 4 → QuatF F a b) (𝔞 : Fin 4 → FracIdeal F) : ℝ :=
  dedekindZeta_residue F / 2 * latConst (gramMat f) 𝔞 / epsteinConst F 4 0

/-- A chosen integral ideal in each ideal class. -/
def clsIdeal (c : ClassGroup (𝓞 F)) : (Ideal (𝓞 F))⁰ := (ClassGroup.mk0_surjective c).choose

theorem clsIdeal_ne_bot (c : ClassGroup (𝓞 F)) : ((clsIdeal c : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F)) ≠ ⊥ :=
  mem_nonZeroDivisors_iff_ne_zero.1 (clsIdeal c).2

theorem mk_idealUnit_clsIdeal (c : ClassGroup (𝓞 F)) :
    ClassGroup.mk F (idealUnit ((clsIdeal c : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F)) (clsIdeal_ne_bot c)) = c := by
  have h : idealUnit ((clsIdeal c : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F)) (clsIdeal_ne_bot c) =
      FractionalIdeal.mk0 F (clsIdeal c) := Units.ext rfl
  rw [h, ClassGroup.mk_mk0]
  exact (ClassGroup.mk0_surjective c).choose_spec

/-- **The class sum of the scaled class terms** is the class-weighted Epstein sum:
$\sum_cN\mathfrak a_c^{-2s}E_{\mathfrak a_c^{-1}L}(s) = \sum_cN(\mathfrak c_c)^{-2s}E_{\mathfrak c_c^{-1}L}(s)$. -/
theorem sum_cls_eq_epsteinClsSum (A : Matrix (Fin 4) (Fin 4) F) (I : Fin 4 → FracIdeal F) (s : ℝ) :
    ∑ c : ClassGroup (𝓞 F), ENNReal.ofReal (idealNorm F (idealUnit _ (clsIdeal_ne_bot c)) ^ (-(2 * s))) *
        epsteinLat A (twist (idealUnit _ (clsIdeal_ne_bot c)) I) s = Gen.epsteinClsSum A I s := by
  rw [Gen.epsteinClsSum, tsum_fintype]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨γ, hγ⟩ := exists_principalSMulFin_classRep F (idealUnit _ (clsIdeal_ne_bot c))
  rw [mk_idealUnit_clsIdeal] at hγ
  rw [← hγ, idealNorm_mul_epsteinLat_principal]

/-- **The averaged class decomposition** ($s > 2$): $h_F\,\zeta_{\mathcal O}(s) = \sum_{[J]\ne0}[\Gamma_J:\mathcal O_F^\times]^{-1}N(\operatorname{nrd}J)^{-s}
\sum_cN(\mathfrak c_c)^{-2s}E_{\mathfrak c_c^{-1}(\mathcal O:J)}(s)$, for chosen presentations $(f_x,\mathfrak a_x)$ of the colon lattices. -/
theorem classNumber_mul_zetaO_eq (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) (hO : IsMaximalOrder (𝓞 F) F O)
    (hstd : stdOrder F a b ≤ O) [Fintype (Quotient (idealSetoid O))]
    (pf : {x : Quotient (idealSetoid O) // x.out ≠ ⊥} → Fin 4 → QuatF F a b)
    (pa : {x : Quotient (idealSetoid O) // x.out ≠ ⊥} → Fin 4 → FracIdeal F)
    (hli : ∀ x, LinearIndependent F (pf x))
    (hmem : ∀ x, ∀ y, y ∈ colon x.1.out ↔ ∃ ξ : Fin 4 → F, LatMem (pa x) ξ ∧ y = ∑ i, ξ i • pf x i)
    {s : ℝ} (hs : 2 < s) :
    (NumberField.classNumber F : ℝ≥0∞) * ENNReal.ofReal (∑' 𝔫 : Ideal (𝓞 F), (idealCountO O 𝔫 : ℝ) * (Ideal.absNorm 𝔫 : ℝ) ^ (-s)) =
      ∑ x : {x : Quotient (idealSetoid O) // x.out ≠ ⊥}, (((centralUnitsIn (R := 𝓞 F) x.1.out).index : ℝ≥0∞))⁻¹ *
        (nrdTerm x.1.out s * Gen.epsteinClsSum (gramMat (pf x)) (pa x) s) := by
  classical
  have hs0 : s ≠ 0 := by linarith
  have hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0 := fun x hx => eq_zero_of_nrd_eq_zero hdef hx
  -- ζ_O as the sum of the class zeta functions
  have hZ : ENNReal.ofReal (∑' 𝔫 : Ideal (𝓞 F), (idealCountO O 𝔫 : ℝ) * (Ideal.absNorm 𝔫 : ℝ) ^ (-s)) =
      ∑ x : Quotient (idealSetoid O), classZeta x s := by
    rw [← tsum_nrdTerm_eq ha hb hO hs, tsum_ideal_eq_tsum_class, tsum_fintype]; rfl
  rw [hZ]
  -- the class map of each ideal class is a bijection
  have hbij : ∀ c : ClassGroup (𝓞 F), Function.Bijective
      (classScale (O := O) ((clsIdeal c : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F))) := fun c =>
    Finite.injective_iff_bijective.1 (classScale_injective (clsIdeal_ne_bot c))
  have h1 : (NumberField.classNumber F : ℝ≥0∞) * ∑ x : Quotient (idealSetoid O), classZeta x s =
      ∑ c : ClassGroup (𝓞 F), ∑ x : Quotient (idealSetoid O),
        classZeta (classScale ((clsIdeal c : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F)) x) s := by
    rw [NumberField.classNumber, ← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact (Equiv.sum_comp (Equiv.ofBijective _ (hbij c)) (fun x => classZeta x s)).symm
  rw [h1, Finset.sum_comm]
  -- split off the zero class
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x : Quotient (idealSetoid O) => x.out ≠ ⊥)]
  have h0 : ∑ x : {x : Quotient (idealSetoid O) // ¬ x.out ≠ ⊥}, ∑ c : ClassGroup (𝓞 F),
      classZeta (classScale ((clsIdeal c : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F)) x.1) s = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun c _ => ?_
    have hx : x.1 = Quotient.mk (idealSetoid O) ⊥ := by
      rw [← Quotient.out_eq x.1, not_not.1 x.2]
    rw [hx, classScale_mk, scaleIdeal_bot]
    exact classZeta_mk_bot hs0
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hJ : x.1.out ≠ ⊥ := x.2
  have hx : x.1 = Quotient.mk (idealSetoid O) x.1.out := (Quotient.out_eq x.1).symm
  have h2 : ∀ c : ClassGroup (𝓞 F), classZeta (classScale ((clsIdeal c : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F)) x.1) s =
      (((centralUnitsIn (R := 𝓞 F) x.1.out).index : ℝ≥0∞))⁻¹ * (nrdTerm x.1.out s *
        (ENNReal.ofReal (idealNorm F (idealUnit _ (clsIdeal_ne_bot c)) ^ (-(2 * s))) *
          epsteinLat (gramMat (pf x)) (twist (idealUnit _ (clsIdeal_ne_bot c)) (pa x)) s)) := fun c => by
    conv_lhs => rw [hx]
    rw [classScale_mk]
    exact classZeta_scaleIdeal hdef hO.1 hstd (clsIdeal_ne_bot c) hJ (hli x) (hmem x) s
  rw [Finset.sum_congr rfl fun c _ => h2 c, ← Finset.mul_sum, ← Finset.mul_sum, sum_cls_eq_epsteinClsSum]

/-- **Eichler's mass formula for every class number** (Voight 2021, Thm. 26.5.4 with $h_F$): for a maximal order
$\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$ of a totally definite quaternion algebra over a totally real field, presented as
$\mathcal O = \bigoplus_i\mathfrak a_if_i$ (no basis),
$$\Lambda_{\mathcal O}\sum_{[J]\ne0}\frac1{[\Gamma_J:\mathcal O_F^\times]} = h_F\,\rho_F\,\zeta_F(2)\prod_{\mathfrak p\in\operatorname{Ram}_f(D)}(1-N\mathfrak p^{-1}),$$
$\Lambda_{\mathcal O}$ = `massConstNF`, the sum over the (finitely many) classes of nonzero left ideals, $\Gamma_J$ the unit group of the right order. -/
@[kb "voight2021" "Thm. 26.5.4; (26.5.5)–(26.5.10)"]
theorem eichler_mass_formula_nf (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) (hO : IsMaximalOrder (𝓞 F) F O)
    (hstd : stdOrder F a b ≤ O) {fO : Fin 4 → QuatF F a b} {𝔞O : Fin 4 → FracIdeal F}
    (hliO : LinearIndependent F fO)
    (hmemO : ∀ x, x ∈ (O : Set (QuatF F a b)) ↔ ∃ ξ : Fin 4 → F, LatMem 𝔞O ξ ∧ x = ∑ i, ξ i • fO i) :
    massConstNF fO 𝔞O * ∑' c : {c : Quotient (idealSetoid O) // c.out ≠ ⊥},
        (((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℕ) : ℝ)⁻¹ =
      (NumberField.classNumber F : ℝ) *
        (dedekindZeta_residue F * dedekindZetaR F 2 * ∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(1 : ℝ)))) := by
  classical
  have hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0 := fun x hx => eq_zero_of_nrd_eq_zero hdef hx
  have : Finite (Quotient (idealSetoid O)) := finite_classes ha hb hO hdiv
  let _ : Fintype (Quotient (idealSetoid O)) := Fintype.ofFinite _
  set C := {c : Quotient (idealSetoid O) // c.out ≠ ⊥}
  have hnrd : ∀ c : C, leftNrdIdeal c.1.out ≠ ⊥ := fun c => leftNrdIdeal_ne_bot hO.1 hdiv c.2
  choose pf pa hli hpos hmem _ using fun c : C => epsteinSum_eq_epstein_presented hdef hdiv hO.1 (hnrd c)
  have hfin : ∀ c : C, (centralUnitsIn (R := 𝓞 F) c.1.out).FiniteIndex := fun c =>
    finiteIndex_centralUnitsIn (O := O) hdef hO.1 hstd c.2
  set idx : C → ℝ := fun c => (((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℕ) : ℝ)
  have hidx : ∀ c, 0 < idx c := fun c => by
    have := (hfin c).index_ne_zero
    simp only [idx]; exact_mod_cast Nat.pos_of_ne_zero this
  set N : C → ℝ := fun c => (Ideal.absNorm (leftNrdIdeal c.1.out) : ℝ)
  have hN : ∀ c, 0 < N c := fun c => by
    simp only [N]; exact_mod_cast Nat.pos_of_ne_zero fun h => hnrd c (Ideal.absNorm_eq_zero_iff.1 h)
  set Z : ℝ → ℝ := fun s => ∑' 𝔫 : Ideal (𝓞 F), (idealCountO O 𝔫 : ℝ) * (Ideal.absNorm 𝔫 : ℝ) ^ (-s)
  -- the averaged decomposition, in ℝ
  have hdec : ∀ s : ℝ, 2 < s → (NumberField.classNumber F : ℝ) * Z s =
      ∑ c : C, (idx c)⁻¹ * (N c ^ (-s) * (Gen.epsteinClsSum (gramMat (pf c)) (pa c) s).toReal) := by
    intro s hs
    have h := classNumber_mul_zetaO_eq ha hb hdef hO hstd pf pa hli hmem hs
    have hZ0 : 0 ≤ Z s := tsum_nonneg fun 𝔫 => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hlt : ∀ c : C, Gen.epsteinClsSum (gramMat (pf c)) (pa c) s < ⊤ := fun c =>
      Gen.epsteinClsSum_lt_top (hpos c) (pa c) (by norm_num) (by push_cast; linarith)
    have h5 := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hZ0, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun c _ => ENNReal.mul_ne_top (ENNReal.inv_ne_top.2
        (Nat.cast_ne_zero.2 (hfin c).index_ne_zero)) (ENNReal.mul_ne_top (by unfold nrdTerm; exact ENNReal.ofReal_ne_top)
          (hlt c).ne))] at h5
    rw [h5]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, nrdTerm,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  -- the limit of the right side
  have hlimc : ∀ c : C, Tendsto (fun s : ℝ => (s - 2) * ((idx c)⁻¹ * (N c ^ (-s) *
      (Gen.epsteinClsSum (gramMat (pf c)) (pa c) s).toReal))) (𝓝[>] 2) (𝓝 ((idx c)⁻¹ * massConstNF fO 𝔞O)) := by
    intro c
    have h := Gen.tendsto_sub_mul_epsteinClsSum (hpos c) (pa c) (n := 4) (by norm_num)
    have h42 : ((4 : ℕ) : ℝ) / 2 = 2 := by norm_num
    rw [h42] at h
    have hpow : Tendsto (fun s : ℝ => N c ^ (-s)) (𝓝[>] 2) (𝓝 (N c ^ (-(2 : ℝ)))) :=
      ((continuous_const.rpow continuous_neg fun _ => Or.inl (hN c).ne').tendsto 2).mono_left nhdsWithin_le_nhds
    have h2 := (hpow.mul h).const_mul (idx c)⁻¹
    have hlat := latConst_colon ha hb hdef hO hliO hmemO (hnrd c) (hli c) (hmem c)
    have hlim : (idx c)⁻¹ * (N c ^ (-(2 : ℝ)) * (dedekindZeta_residue F / 2 * latConst (gramMat (pf c)) (pa c) /
        epsteinConst F 4 0)) = (idx c)⁻¹ * massConstNF fO 𝔞O := by
      rw [hlat, massConstNF, Real.rpow_neg (hN c).le, Real.rpow_two]
      have := (hN c).ne'
      field_simp
      simp only [N]; ring
    rw [hlim] at h2
    exact h2.congr fun s => by ring
  have hL : Tendsto (fun s : ℝ => (s - 2) * ((NumberField.classNumber F : ℝ) * Z s)) (𝓝[>] 2)
      (𝓝 (∑ c : C, (idx c)⁻¹ * massConstNF fO 𝔞O)) := by
    have h := tendsto_finsetSum (Finset.univ : Finset C) fun c _ => hlimc c
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hdec s hs, Finset.mul_sum]
  have hR : Tendsto (fun s : ℝ => (s - 2) * ((NumberField.classNumber F : ℝ) * Z s)) (𝓝[>] 2)
      (𝓝 ((NumberField.classNumber F : ℝ) * (dedekindZeta_residue F * dedekindZetaR F 2 *
        ∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(1 : ℝ)))))) := by
    have h := (tendsto_sub_mul_zetaO ha hb hO).const_mul (NumberField.classNumber F : ℝ)
    exact h.congr fun s => by simp only [Z]; ring
  have huniq := tendsto_nhds_unique hL hR
  rw [← huniq, tsum_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- $K = $ `epsteinConst F 4 0` $= |d_F|^{-1/2}\pi^{-2d}$, $d$ the number of real places. -/
theorem epsteinConst_four_zero :
    epsteinConst F 4 0 = (NumberField.discr F : ℝ) ^ (-(1 / 2 : ℝ)) * (π ^ (2 * Fintype.card (InfinitePlace F)))⁻¹ := by
  have hd : (0 : ℝ) < NumberField.discr F := AdditiveZeta.discr_pos
  unfold epsteinConst
  rw [SphericalFibration.ideleConst_eq, abs_of_pos hd]
  have h2 : ((4 : ℕ) : ℝ) + 2 * 0 = 4 := by norm_num
  rw [h2, show (4 : ℝ) / 2 = 2 by norm_num, Real.Gamma_two, mul_one, show -(4 : ℝ) / 2 = -2 by norm_num,
    Real.rpow_neg Real.pi_pos.le, inv_pow, Real.rpow_two, ← pow_mul]

/-- **Eichler's mass formula, closed form, every class number**:
$$\sum_{[J]\ne0}\frac1{[\Gamma_J:\mathcal O_F^\times]} = \frac{2\,h_F\,\zeta_F(2)\prod_{\mathfrak p\in\operatorname{Ram}_f}(1-N\mathfrak p^{-1})}{c_{\mathcal O}\,|d_F|^{1/2}\,\pi^{2d}},$$
$c_{\mathcal O}$ the lattice constant of the presented lattice $(\mathcal O,\operatorname{nrd})$ ($= (\prod_v\sqrt{\det\sigma_vA_{\mathcal O}})^{-1}|d_F|^{-2}$ when $\mathcal O$ is
free with Gram matrix $A_{\mathcal O}$, recovering `eichler_mass_formula'`). -/
@[kb "voight2021" "Thm. 26.5.4"]
theorem eichler_mass_formula_nf' (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) (hO : IsMaximalOrder (𝓞 F) F O)
    (hstd : stdOrder F a b ≤ O) {fO : Fin 4 → QuatF F a b} {𝔞O : Fin 4 → FracIdeal F}
    (hliO : LinearIndependent F fO)
    (hmemO : ∀ x, x ∈ (O : Set (QuatF F a b)) ↔ ∃ ξ : Fin 4 → F, LatMem 𝔞O ξ ∧ x = ∑ i, ξ i • fO i) :
    ∑' c : {c : Quotient (idealSetoid O) // c.out ≠ ⊥}, (((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℕ) : ℝ)⁻¹ =
      2 * (NumberField.classNumber F : ℝ) * dedekindZetaR F 2 * (∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(1 : ℝ)))) /
        (latConst (gramMat fO) 𝔞O * (NumberField.discr F : ℝ) ^ (1 / 2 : ℝ) *
          π ^ (2 * Fintype.card (InfinitePlace F))) := by
  have h := eichler_mass_formula_nf ha hb hdef hO hstd hliO hmemO
  have hρ := dedekindZeta_residue_pos F
  have hd : (0 : ℝ) < NumberField.discr F := AdditiveZeta.discr_pos
  have hc : 0 < latConst (gramMat fO) 𝔞O := by
    unfold AdditiveZeta.latConst
    refine mul_pos (inv_pos.2 (Finset.prod_pos fun v _ => Real.sqrt_pos.2
      ((isTotPosGram_gramMat hdef hliO) v).det_pos)) (inv_pos.2 (Finset.prod_pos fun i _ => ?_))
    rw [AdditiveZeta.embDet_eq]
    exact mul_pos (idealNorm_pos F (𝔞O i)) (Real.sqrt_pos.2 hd)
  have hK : epsteinConst F 4 0 ≠ 0 := (epsteinConst_pos (F := F) (by norm_num) le_rfl).ne'
  have hM : massConstNF fO 𝔞O ≠ 0 := by
    unfold massConstNF; exact div_ne_zero (mul_ne_zero (by positivity) hc.ne') hK
  have hS : ∑' c : {c : Quotient (idealSetoid O) // c.out ≠ ⊥}, (((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℕ) : ℝ)⁻¹ =
      (NumberField.classNumber F : ℝ) * (dedekindZeta_residue F * dedekindZetaR F 2 *
        ∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(1 : ℝ)))) / massConstNF fO 𝔞O := by
    rw [eq_div_iff hM, mul_comm]; exact h
  rw [hS, massConstNF, epsteinConst_four_zero, Real.rpow_neg hd.le]
  have hsq : 0 < (NumberField.discr F : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hd _
  have hπ : 0 < π ^ (2 * Fintype.card (InfinitePlace F)) := pow_pos Real.pi_pos _
  field_simp

end Mass

end Gen

end QuadFormsKB.QuatOrder
