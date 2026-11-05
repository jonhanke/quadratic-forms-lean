/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Dyadic7Blocks
import QuadFormsKB.Tamagawa.Dyadic7Units
import QuadFormsKB.Tamagawa.Measure.Weil.ThetaPoissonSO

/-!
# Paper 7 at $p = 2$: local genera and 2-adic symbols

Transfers Conway–Sloane's classification of $\mathbb Z_2$-classes by 2-adic symbols
(`ConwaySloane.TwoAdic.zpEquiv_iff_moveEquiv`, `exists_isTwoSymbolOf`) to local genera `LocGenus v n` at the prime
$v \mid 2$ of $\mathbb Q$.

**Proves.**
* `isometricGL_iff_zpEquiv`: for a ring $R \cong \mathbb Z_2$ (`e : ℤ_[2] ≃+* R`), $\mathrm{GL}_n(R)$-equivalence of forms is
  $\mathbb Z_2$-equivalence (`Cassels.ZpEquiv`) of their Hessian matrices viewed over $\mathbb Q_2$ (`hessQ2`);
* `genusOf_eq_iff`: two even block decompositions give the same local genus iff their 2-adic symbols are related by
  sign walking and oddity fusion (`MoveEquiv`);
* `exists_genusOf`: every nondegenerate local genus at 2 is the genus of an even block decomposition.

Indices are 0-based.
-/

open IsDedekindDomain NumberField Matrix Finset

namespace QuadFormsKB.Dyadic7

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Ternary QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.HilbertLocal QuadFormsKB.Siegel

noncomputable section

section Generic

variable {R : Type*} [CommRing R] (e : ℤ_[2] ≃+* R) {n : ℕ}

include e

/-- The ring homomorphism `R → ℚ_[2]`. -/
def toQ2 : R →+* ℚ_[2] := PadicInt.Coe.ringHom.comp e.symm.toRingHom

theorem toQ2_injective : Function.Injective (toQ2 e) := by
  intro a b h
  have : (e.symm a : ℚ_[2]) = e.symm b := h
  exact e.symm.injective (Subtype.ext this)

theorem toQ2_e (x : ℤ_[2]) : toQ2 e (e x) = (x : ℚ_[2]) := by
  show PadicInt.Coe.ringHom (e.symm (e x)) = _
  rw [RingEquiv.symm_apply_apply]; rfl

/-- The Hessian of a form over `R`, as a matrix over `ℚ_[2]`. -/
def hessQ2 (T : QuadForm R n) : Matrix (Fin n) (Fin n) ℚ_[2] := T.hessian.map (toQ2 e)

theorem two_mul_cancel {a b : R} (h : 2 * a = 2 * b) : a = b := by
  have h' := congrArg e.symm h
  rw [map_mul, map_mul, map_ofNat] at h'
  have h0 : (2 : ℤ_[2]) ≠ 0 := two_ne_zero
  exact e.symm.injective (mul_left_cancel₀ h0 h')

theorem hessian_inj {T T' : QuadForm R n} (h : T.hessian = T'.hessian) : T = T' := by
  have hc : ∀ i j, T.coeff i j = T'.coeff i j := by
    intro i j
    have hij := congrFun (congrFun h i) j
    simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply] at hij
    rcases lt_trichotomy i j with hl | rfl | hl
    · have h1 : T.coeff j i = 0 := T.upper (show id i < id j from hl)
      have h2 : T'.coeff j i = 0 := T'.upper (show id i < id j from hl)
      simpa [h1, h2] using hij
    · have : 2 * T.coeff i i = 2 * T'.coeff i i := by rw [two_mul, two_mul]; exact hij
      exact two_mul_cancel e this
    · have h1 : T.coeff i j = 0 := T.upper (show id j < id i from hl)
      have h2 : T'.coeff i j = 0 := T'.upper (show id j < id i from hl)
      rw [h1, h2]
  exact QuadForm.ext (Matrix.ext hc)

/-- units transport -/
def glMap (g : GL (Fin n) R) : GL (Fin n) ℤ_[2] :=
  Units.map (RingHom.mapMatrix e.symm.toRingHom).toMonoidHom g

theorem glMap_val (g : GL (Fin n) R) : (glMap e g).val = g.val.map e.symm := rfl

def glMap' (g : GL (Fin n) ℤ_[2]) : GL (Fin n) R :=
  Units.map (RingHom.mapMatrix e.toRingHom).toMonoidHom g

theorem glMap'_val (g : GL (Fin n) ℤ_[2]) : (glMap' e g).val = g.val.map e := rfl

theorem hessQ2_compMat (T : QuadForm R n) (g : Matrix (Fin n) (Fin n) R) :
    hessQ2 e (T.compMat g) = (g.map (toQ2 e))ᵀ * hessQ2 e T * g.map (toQ2 e) := by
  unfold hessQ2
  rw [QuadForm.hessian_compMat, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

theorem isometricGL_iff_zpEquiv (T T' : QuadForm R n) :
    IsometricGL T T' ↔ ZpEquiv (hessQ2 e T) (hessQ2 e T') := by
  rw [isometricGL_iff_compMat]
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨glMap e g, ?_⟩
    rw [hessQ2_compMat, glMap_val]
    have : (g.val.map e.symm).map (PadicInt.Coe.ringHom) = g.val.map (toQ2 e) := by
      rw [Matrix.map_map]; rfl
    rw [this]
  · rintro ⟨T0, hT0⟩
    refine ⟨glMap' e T0, ?_⟩
    have hmap : (T0.val.map e).map (toQ2 e) = T0.val.map (PadicInt.Coe.ringHom) := by
      rw [Matrix.map_map]; congr 1; ext x; exact toQ2_e e x
    apply hessian_inj e
    apply Matrix.ext; intro i j
    apply toQ2_injective e
    have := congrFun (congrFun (hessQ2_compMat e T (glMap' e T0).val) i) j
    unfold hessQ2 at this hT0
    show (T'.hessian.map (toQ2 e)) i j = ((T.compMat (glMap' e T0).val).hessian.map (toQ2 e)) i j
    rw [this, glMap'_val, hmap]
    exact (congrFun (congrFun hT0 i) j).symm

theorem hessQ2_formZ {n : ℕ} {D : List DyBlock} (hn : dyDim D = n) (h0 : ∀ b ∈ D, 0 ≤ blockExp b)
    (hev : ∀ b ∈ D, ¬ IsOddUnimodBlock b) :
    hessQ2 e ((formZ n D).map (algebraMap ℤ R)) =
      (dyMat D).submatrix (Fin.cast hn.symm) (Fin.cast hn.symm) := by
  unfold hessQ2
  rw [Tamagawa.Measure.Weil.hessian_map', hessian_formZ hn h0 hev, Matrix.map_map]
  have : (toQ2 e).comp (algebraMap ℤ R) = Int.castRingHom ℚ_[2] := RingHom.ext_int _ _
  rw [← RingHom.coe_comp, this, hessZ_of hn, ← map_dyMatInt D h0]
  ext i j; simp

theorem isTwoSymbolOf_formZ {n : ℕ} {D : List DyBlock} (hD : ∀ b ∈ D, b.Valid) (hn : dyDim D = n)
    (h0 : ∀ b ∈ D, 0 ≤ blockExp b) (hev : ∀ b ∈ D, ¬ IsOddUnimodBlock b) :
    IsTwoSymbolOf (hessQ2 e ((formZ n D).map (algebraMap ℤ R))) (blockSymbol D) :=
  ⟨D, hD, h0, hn, by rw [hessQ2_formZ e hn h0 hev]; exact ZpEquiv.refl _, rfl⟩

theorem hessQ2_symm (T : QuadForm R n) : (hessQ2 e T)ᵀ = hessQ2 e T := by
  unfold hessQ2
  rw [← Matrix.transpose_map]
  congr 1
  simp [QuadForm.hessian, add_comm]

theorem hessQ2_det (T : QuadForm R n) (h : T.hessian.det ≠ 0) : (hessQ2 e T).det ≠ 0 := by
  unfold hessQ2
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact fun h' => h (toQ2_injective e (by simpa using h'))

theorem hessQ2_norm (T : QuadForm R n) (i j : Fin n) : ‖hessQ2 e T i j‖ ≤ 1 :=
  (e.symm (T.hessian i j)).2

theorem hessQ2_diag_small (T : QuadForm R n) (X : Matrix (Fin n) (Fin n) R) (k : Fin n) :
    ‖((X.map (toQ2 e))ᵀ * hessQ2 e T * X.map (toQ2 e)) k k‖ < 1 := by
  have h1 : (X.map (toQ2 e))ᵀ * hessQ2 e T * X.map (toQ2 e) = hessQ2 e (T.compMat X) :=
    (hessQ2_compMat e T X).symm
  rw [h1]
  unfold hessQ2
  rw [Matrix.map_apply]
  have h2 : (T.compMat X).hessian k k = 2 * (T.compMat X).coeff k k := by
    simp [QuadForm.hessian, two_mul]
  rw [h2]
  have h3 : toQ2 e (2 * (T.compMat X).coeff k k) =
      ((2 * e.symm ((T.compMat X).coeff k k) : ℤ_[2]) : ℚ_[2]) := by
    show PadicInt.Coe.ringHom (e.symm _) = _
    rw [map_mul, map_ofNat]; rfl
  rw [h3, PadicInt.norm_coe, PadicInt.norm_lt_one_iff_dvd]
  simp

end Generic

theorem odd_of_not_even_blocks : ∀ (D : List DyBlock), (∀ b ∈ D, b.Valid) →
    (∀ i, Even (dyMatInt D i i)) → ∀ b ∈ D, ¬ IsOddUnimodBlock b
  | [], _, _, b, hb => by simp at hb
  | b :: D, hv, H, c, hc => by
    have hA : ∀ k : Fin b.dim, Even (blockMatInt b k k) := by
      intro k
      have := H (Fin.castAdd _ k)
      simpa [dyMatInt, orthSumMat, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁] using this
    have hB : ∀ k, Even (dyMatInt D k k) := by
      intro k
      have := H (Fin.natAdd _ k)
      simpa [dyMatInt, orthSumMat, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂] using this
    rcases List.mem_cons.1 hc with rfl | hc
    · intro hodd
      cases c with
      | sq e u =>
        have he : e = 0 := hodd
        subst he
        have h1 := hA (0 : Fin 1)
        have hu := hv _ (List.mem_cons_self ..)
        change Even ((!![2 ^ (0:ℤ).toNat * u] : Matrix (Fin 1) (Fin 1) ℤ) 0 0) at h1
        simp at h1
        simp only [DyBlock.Valid] at hu
        rcases h1 with ⟨m, hm⟩
        omega
      | hyp e => exact hodd
      | ell e => exact hodd
    · exact odd_of_not_even_blocks D (fun c hc => hv c (List.mem_cons_of_mem _ hc)) hB c hc

/-- **Local genera at 2 and 2-adic symbols** (Conway–Sloane, Ch. 15, §7.5, Thm. 10). Let $v$ be the prime of $\mathbb Q$
above $2$ (`h2`), $n$ the number of variables, and $D$, $D'$ lists of blocks (`DyBlock`), each with valid units
(`hD`, `hD'`), nonnegative exponents (`h0`, `h0'`), total dimension $n$ (`hn`, `hn'`) and no block $2^0 u x^2$ (`hev`,
`hev'`, so the Hessians are even). Then the local genera at $v$ of the forms $Q_D$, $Q_{D'}$ coincide iff the 2-adic
symbols of $D$ and $D'$ are related by sign walking and oddity fusion. -/
@[kb "conwaysloane1999" "Ch. 15, §7.3–7.5, Thm. 10, pp. 380–382 (local genera at 2 by 2-adic symbols)"]
theorem genusOf_eq_iff (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {n : ℕ}
    {D D' : List DyBlock}
    (hD : ∀ b ∈ D, b.Valid) (h0 : ∀ b ∈ D, 0 ≤ blockExp b) (hn : dyDim D = n)
    (hev : ∀ b ∈ D, ¬ IsOddUnimodBlock b)
    (hD' : ∀ b ∈ D', b.Valid) (h0' : ∀ b ∈ D', 0 ≤ blockExp b) (hn' : dyDim D' = n)
    (hev' : ∀ b ∈ D', ¬ IsOddUnimodBlock b) :
    genusOf v n D = genusOf v n D' ↔ MoveEquiv (blockSymbol D) (blockSymbol D') := by
  unfold genusOf
  rw [LocGenus.mk_eq_mk, isometricGL_iff_zpEquiv (e2 v h2)]
  exact TwoAdic.zpEquiv_iff_moveEquiv (isTwoSymbolOf_formZ (e2 v h2) hD hn h0 hev)
    (isTwoSymbolOf_formZ (e2 v h2) hD' hn' h0' hev')

/-- **Every nondegenerate local genus at 2 comes from an even block decomposition.** Let $v$ be the prime above $2$
(`h2`) and $G$ a local genus in $n$ variables with nonzero Hessian determinant (`hG`). Then there is a list $D$ of valid
blocks with nonnegative exponents, dimension $n$, no block $2^0 u x^2$, and $G$ is the genus of $Q_D$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.3–7.5, Thm. 10, pp. 380–382 (local genera at 2 by 2-adic symbols)"]
theorem exists_genusOf (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {n : ℕ}
    (G : LocGenus v n) (hG : G.Nondeg) :
    ∃ D : List DyBlock, (∀ b ∈ D, b.Valid) ∧ (∀ b ∈ D, 0 ≤ blockExp b) ∧ dyDim D = n ∧
      (∀ b ∈ D, ¬ IsOddUnimodBlock b) ∧ G = genusOf v n D := by
  induction G using Quotient.inductionOn with
  | _ T =>
  have hT : T.hessian.det ≠ 0 := hG
  set e := e2 v h2
  obtain ⟨σ, D, hD, h0, hn, ⟨T0, hT0⟩, -⟩ := TwoAdic.exists_isTwoSymbolOf (hessQ2 e T)
    (hessQ2_symm e T) (hessQ2_det e T hT) (hessQ2_norm e T)
  have hev : ∀ b ∈ D, ¬ IsOddUnimodBlock b := by
    refine odd_of_not_even_blocks D hD fun i => ?_
    by_contra hodd
    have hz : ¬ (2 : ℤ) ∣ dyMatInt D i i := fun h => hodd (even_iff_two_dvd.2 h)
    have hM : ((dyMat D).submatrix (Fin.cast hn.symm) (Fin.cast hn.symm)) (Fin.cast hn i) (Fin.cast hn i) =
        ((dyMatInt D i i : ℤ) : ℚ_[2]) := by
      rw [← map_dyMatInt D h0]; simp
    have hX : (T0.val.map PadicInt.Coe.ringHom) = (T0.val.map e).map (toQ2 e) := by
      rw [Matrix.map_map]; congr 1; ext x; exact (toQ2_e e x).symm
    have hlt := hessQ2_diag_small e T (T0.val.map e) (Fin.cast hn i)
    rw [← hX, hT0, hM] at hlt
    have hn1 : ‖((dyMatInt D i i : ℤ) : ℚ_[2])‖ = ‖((dyMatInt D i i : ℤ) : ℤ_[2])‖ := by
      rw [← PadicInt.norm_coe]; simp
    rw [hn1, PadicInt.norm_int_lt_one_iff_dvd] at hlt
    exact hz (by exact_mod_cast hlt)
  refine ⟨D, hD, h0, hn, hev, ?_⟩
  unfold genusOf
  show LocGenus.mk T = _
  rw [LocGenus.mk_eq_mk, isometricGL_iff_zpEquiv e, hessQ2_formZ e hn h0 hev]
  exact ⟨T0, hT0⟩

/-! ### Nondegeneracy and primitivity of `genusOf` -/

/-- **Nondegeneracy of $Q_D$.** Let $v$ be a place of $\mathbb Q$, `hD` all blocks of $D$ valid, `h0` all exponents
nonnegative, `hn` $\dim D = n$, `hev` no block $2^0 u x^2$. Then the Hessian of the form $Q_D$ over $\mathbb Z_v$ has
nonzero determinant $2^{\mathrm{val}}\cdot\mathrm{unit}$ (`det_hessZ`), i.e. the local genus is nondegenerate. -/
@[kb "hanke2011ternary" "§4, Lemma 4.2, p. 10 (primitive ternary 2-adic genera)"]
theorem nondeg_genusOf (v : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} {D : List DyBlock} (hD : ∀ b ∈ D, b.Valid)
    (h0 : ∀ b ∈ D, 0 ≤ blockExp b) (hn : dyDim D = n) (hev : ∀ b ∈ D, ¬ IsOddUnimodBlock b) :
    (genusOf v n D).Nondeg := by
  unfold genusOf
  rw [LocGenus.nondeg_mk, Tamagawa.Measure.Weil.hessian_map', hessian_formZ hn h0 hev]
  have hdet : (hessZ n D).det = 2 ^ valSum D * unitProd D := det_hessZ hn h0
  have hne : (hessZ n D).det ≠ 0 := by
    rw [hdet]
    refine mul_ne_zero (pow_ne_zero _ two_ne_zero) ?_
    intro h
    exact odd_unitProd D hD (by rw [h]; exact dvd_zero _)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact fun h => hne (RingHom.injective_int (algebraMap ℤ (v.adicCompletionIntegers ℚ)) (by simpa using h))

/-- **Primitivity of $Q_D$ at 2.** Let $v$ be the prime of $\mathbb Q$ above $2$ (`h2`) and `hn` $\dim D = n$. The local
genus of $Q_D$ is primitive (its coefficients generate $\mathbb Z_2$) iff some coefficient of $Q_D$ is odd
(`IsPrimBlocks D`). -/
@[kb "hanke2011ternary" "§4, Lemma 4.2, p. 10 (primitive ternary 2-adic genera)"]
theorem prim_genusOf_iff (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {n : ℕ} {D : List DyBlock}
    (hn : dyDim D = n) : (genusOf v n D).Prim ↔ IsPrimBlocks D := by
  subst hn
  unfold genusOf
  rw [LocGenus.prim_mk]
  unfold Hanke2011Structure.IsPrimitiveForm IsPrimBlocks
  have hcoef : ∀ i j, ((formZ (dyDim D) D).map (algebraMap ℤ (v.adicCompletionIntegers ℚ))).coeff i j =
      algebraMap ℤ (v.adicCompletionIntegers ℚ) ((formZ (dyDim D) D).coeff i j) := fun _ _ => rfl
  constructor
  · intro htop
    by_contra hnot
    push Not at hnot
    have hle : Ideal.span (Set.range fun p : Fin (dyDim D) × Fin (dyDim D) =>
        ((formZ (dyDim D) D).map (algebraMap ℤ (v.adicCompletionIntegers ℚ))).coeff p.1 p.2) ≤
        Ideal.span {(2 : v.adicCompletionIntegers ℚ)} := by
      rw [Ideal.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      obtain ⟨d, hd⟩ := hnot i j
      beta_reduce
      rw [hcoef, hd]
      exact Ideal.mem_span_singleton.2 ⟨algebraMap ℤ _ d, by simp⟩
    rw [htop, top_le_iff, Ideal.span_singleton_eq_top] at hle
    have h22 : e2 v h2 (2 : ℤ_[2]) = 2 := map_ofNat _ 2
    rw [← h22] at hle
    have hu : IsUnit (2 : ℤ_[2]) := (MulEquiv.isUnit_map (e2 v h2).toMulEquiv).1 hle
    rw [PadicInt.isUnit_iff] at hu
    have hlt : ‖(2 : ℤ_[2])‖ < 1 := (PadicInt.norm_lt_one_iff_dvd (2 : ℤ_[2])).2 (by simp)
    rw [hu] at hlt
    exact lt_irrefl _ hlt
  · rintro ⟨i, j, hij⟩
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨(i, j), rfl⟩) ?_
    beta_reduce
    rw [hcoef]
    have hodd : Odd ((formZ (dyDim D) D).coeff i j) := by
      rw [← Int.not_even_iff_odd, even_iff_two_dvd]; exact hij
    have := (Cassels.dyadic_isUnit_int_cast_of_odd hodd).map (e2 v h2)
    rw [map_intCast] at this
    rwa [eq_intCast (algebraMap ℤ (v.adicCompletionIntegers ℚ))]

/-! ### Admissible lists -/

theorem exp_le_valSum : ∀ (D : List DyBlock), ∀ b ∈ D, (blockExp b).toNat ≤ valSum D
  | [], b, hb => by simp at hb
  | c :: D, b, hb => by
    simp only [valSum, List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hb with rfl | hb
    · have : 1 ≤ b.dim := by cases b <;> simp [DyBlock.dim]
      nlinarith [Nat.zero_le (List.map (fun b => b.dim * (blockExp b).toNat) D).sum]
    · have := exp_le_valSum D b hb
      simp only [valSum] at this
      omega

theorem mem_alphabet {h : ℕ} {b : DyBlock} (hv : b.Valid) (h0 : 0 ≤ blockExp b)
    (hle : (blockExp b).toNat ≤ h) : b ∈ alphabet h := by
  classical
  cases b with
  | sq e u =>
    simp only [DyBlock.Valid] at hv
    simp only [blockExp] at h0 hle
    simp only [alphabet, sqUnits, Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_range,
      Finset.mem_insert, Finset.mem_singleton]
    left; left
    exact ⟨(e.toNat, u), ⟨by omega, by tauto⟩, by simp [Int.toNat_of_nonneg h0]⟩
  | hyp e =>
    simp only [blockExp] at h0 hle
    simp only [alphabet, Finset.mem_union]
    refine Or.inl (Or.inr (Finset.mem_image.2 ⟨e, ?_, rfl⟩))
    simp
    exact ⟨e.toNat, by omega, by simp [Int.toNat_of_nonneg h0]⟩
  | ell e =>
    simp only [blockExp] at h0 hle
    simp only [alphabet, Finset.mem_union]
    refine Or.inr (Finset.mem_image.2 ⟨e, ?_, rfl⟩)
    simp
    exact ⟨e.toNat, by omega, by simp [Int.toNat_of_nonneg h0]⟩

theorem dim_bounds (b : DyBlock) : 1 ≤ b.dim ∧ b.dim ≤ 2 := by cases b <;> simp [DyBlock.dim]

/-- **Block lists of dimension 3 are among the finitely many lists `lists3 h`.** If all blocks of $D$ are valid (`hD`),
have nonnegative exponents (`h0`), $\dim D = 3$ (`hn`) and $\sum \dim(b)\,e_b = h$ (`hval`), then $D$ has two or three
blocks, each in `alphabet h`, i.e. $D \in$ `lists3 h`. -/
theorem mem_lists3 {h : ℕ} {D : List DyBlock} (hD : ∀ b ∈ D, b.Valid) (h0 : ∀ b ∈ D, 0 ≤ blockExp b)
    (hn : dyDim D = 3) (hval : valSum D = h) : D ∈ lists3 h := by
  have hb : ∀ b ∈ D, b ∈ alphabet h := fun b hb =>
    mem_alphabet (hD b hb) (h0 b hb) (hval ▸ exp_le_valSum D b hb)
  rcases D with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩
  · simp [dyDim] at hn
  · have := dim_bounds a
    simp [dyDim] at hn
    omega
  · have ha := hb a (by simp)
    have hb' := hb b (by simp)
    simp only [lists3, Finset.mem_union, Finset.mem_image, Finset.mem_product]
    left; right
    exact ⟨(a, b), ⟨ha, hb'⟩, rfl⟩
  · have ha := hb a (by simp)
    have hb' := hb b (by simp)
    have hc := hb c (by simp)
    simp only [lists3, Finset.mem_union, Finset.mem_image, Finset.mem_product]
    right
    exact ⟨(a, b, c), ⟨ha, hb', hc⟩, rfl⟩
  · have := dim_bounds a
    have := dim_bounds b
    have := dim_bounds c
    have := dim_bounds d
    simp [dyDim] at hn
    omega

theorem mem_admSet_iff {h : ℕ} {u : ℤ} {D : List DyBlock} : D ∈ admSet h u ↔ IsAdm h u D := by
  classical
  unfold admSet
  rw [Finset.mem_filter]
  exact ⟨fun H => H.2, fun H => ⟨mem_lists3 H.1 H.2.1 H.2.2.1 H.2.2.2.2.2.1, H⟩⟩

/-! ### Supports of block symbols and the base decomposition -/

/-- **The symbol of a block list with exponents $< N$ is supported below $N$:** for $k \ge N$ the constituent of scale
$2^k$ is trivial (dimension $0$, sign $+$, type II, oddity $0$). Hypotheses: `h0` all exponents of $D$ are nonnegative
and `hN` all satisfy $e_b < N$. -/
theorem blockSymbol_supportedBelow {D : List DyBlock} {N : ℕ} (h0 : ∀ b ∈ D, 0 ≤ blockExp b)
    (hN : ∀ b ∈ D, (blockExp b).toNat < N) : (blockSymbol D).SupportedBelow N := by
  intro k hk
  have hnil : D.filter (fun b => blockExp b = (k : ℤ)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro b hb hbk
    have := hN b hb
    simp only [decide_eq_true_eq] at hbk
    omega
  simp only [blockSymbol, hnil]
  simp [TwoFactor.trivial, Sign.prodList]

/-- **Admissible lists have symbols supported below $h + 1$** (exponents are $\le h$, `exp_le_valSum`). -/
theorem supportedBelow_of_mem_admSet {h : ℕ} {u : ℤ} {D : List DyBlock} (hD : D ∈ admSet h u) :
    (blockSymbol D).SupportedBelow (h + 1) := by
  obtain ⟨_, h0, _, _, _, hval, _⟩ := mem_admSet_iff.1 hD
  exact blockSymbol_supportedBelow h0 fun b hb => by have := exp_le_valSum D b hb; omega

/-- **Properties of the base decomposition** $D_0(u) = 2xy \perp 2(-u)z^2$ for $u \in \{1,3,5,7\}$ (`sqUnits`): valid
blocks, nonnegative exponents, dimension $3$, no block $2^0 u x^2$, primitive, $\sum \dim\cdot e = 1$, unit part
$\equiv u \pmod 8$, and symbol supported below $2$. -/
theorem baseList_props {u : ℤ} (hu : u ∈ sqUnits) :
    (∀ b ∈ baseList u, b.Valid) ∧ (∀ b ∈ baseList u, 0 ≤ blockExp b) ∧ dyDim (baseList u) = 3 ∧
      (∀ b ∈ baseList u, ¬ IsOddUnimodBlock b) ∧ IsPrimBlocks (baseList u) ∧ valSum (baseList u) = 1 ∧
      unitProd (baseList u) % 8 = u % 8 ∧ (blockSymbol (baseList u)).SupportedBelow 2 := by
  simp only [sqUnits, Finset.mem_insert, Finset.mem_singleton] at hu
  have hmain : (∀ b ∈ baseList u, b.Valid) ∧ (∀ b ∈ baseList u, 0 ≤ blockExp b) ∧ dyDim (baseList u) = 3 ∧
      (∀ b ∈ baseList u, ¬ IsOddUnimodBlock b) ∧ valSum (baseList u) = 1 ∧
      unitProd (baseList u) % 8 = u % 8 := by
    rcases hu with rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [baseList, DyBlock.Valid, blockExp, dyDim, DyBlock.dim, IsOddUnimodBlock, valSum, unitProd, blockUnit]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hmain
  refine ⟨h1, h2, h3, h4, ?_, h5, h6, blockSymbol_supportedBelow h2 ?_⟩
  · unfold IsPrimBlocks
    rcases hu with rfl | rfl | rfl | rfl <;> exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩
  · intro b hb
    simp only [baseList, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp [blockExp]

#print axioms genusOf_eq_iff
#print axioms exists_genusOf
#print axioms nondeg_genusOf
#print axioms prim_genusOf_iff
#print axioms mem_lists3
#print axioms mem_admSet_iff
#print axioms blockSymbol_supportedBelow
#print axioms supportedBelow_of_mem_admSet
#print axioms baseList_props

end

end QuadFormsKB.Dyadic7
