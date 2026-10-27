import QuadFormsKB.Tamagawa.Measure.Weil.ConeAdelicSection

/-!
# The stabilizer of $e$ in $SO(V)(\mathbb A)$: $P = N\rtimes SO(Q_0')(\mathbb A)$

For the cone form $Q_0 = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ and $e = e_0 + e_1$:

* **`coneSecData`**: the section data of `ConeAdelicSection.lean` (base point $e$, an isotropic frame from
  `exists_isoFrame_cone`), so $C(\mathbb A)$, the section and the orbit coordinates are available.
* **`decompFun`** $(w, h)\mapsto n_{\mathbb A}(w)\,\mathrm{diag}(1,1,h)\in P$ is a bijection
  $\mathbb A^k\times SO(Q_0')(\mathbb A)\to P$ (`decompFun_bijective`): at every place an isometry fixing $e$ is
  $n(w)\mathrm{diag}(1,1,M)$ with $w = (ge_0)'$ (`ConeAlgebra.eq_nM_mul_mM_of_fix`), and the block $M$ is integral where
  $g$ and $n(w)$ are; **`decompEquiv`**: it is a measurable equivalence (Lusin–Souslin).
* Rationality: $n_{\mathbb A}(F^k)\subseteq SO(V)(F)$ (`coneN_mem_gamma`), $\mathrm{diag}(1,1,SO(Q_0')(F))\subseteq SO(V)(F)$
  (`hA_mem_gamma`), and the coordinates of a rational point of $P$ are rational (`decomp_symm_rat`).
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.Measure.ConeAlgebra

variable {F : Type} [Field F] [NumberField F]

/-! ### Blocks -/

section Block

variable {K : Type*} [Field K] [CharZero K] {k : ℕ}

/-- The lower right $k\times k$ block of a $(k+2)\times(k+2)$ matrix. -/
def blk (A : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) K) : Matrix (Fin k) (Fin k) K :=
  A.submatrix (fun i => i.succ.succ) (fun j => j.succ.succ)

@[simp] theorem blk_mM (M : Matrix (Fin k) (Fin k) K) : blk (mM M) = M := by
  ext i j; simp [blk, mM]

theorem mM_injective : Function.Injective (mM (K := K) (k := k)) := fun M M' h => by
  rw [← blk_mM M, h, blk_mM]

theorem mM_mulVec_e₀ (M : Matrix (Fin k) (Fin k) K) : mM M *ᵥ (e₀ : Fin (k + 1 + 1) → K) = e₀ := by
  rw [e₀_eq_v3, mM_mulVec_v3, mulVec_zero]

variable (c : K) (Q' : QuadForm K k)

/-- **The local stabilizer decomposition**: for an isometry $g$ of determinant $1$ with $ge = e$ and $w = (ge_0)'$,
$A = n(-w)g$ is $\mathrm{diag}(1,1,M)$ with $M = $ `blk A` an isometry of $Q'$ of determinant $1$. -/
theorem stab_decomp (hc : c ≠ 0) (hQ : (coneForm c Q').hessian.det ≠ 0)
    {g : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) K}
    (hg : gᵀ * (coneForm c Q').hessian * g = (coneForm c Q').hessian) (hdet : g.det = 1)
    (he : g *ᵥ (eV : Fin (k + 1 + 1) → K) = eV) :
    nM c Q' (-tl (g *ᵥ e₀)) * g = mM (blk (nM c Q' (-tl (g *ᵥ e₀)) * g)) ∧
      (blk (nM c Q' (-tl (g *ᵥ e₀)) * g))ᵀ * Q'.hessian * blk (nM c Q' (-tl (g *ᵥ e₀)) * g) = Q'.hessian ∧
      (blk (nM c Q' (-tl (g *ᵥ e₀)) * g)).det = 1 := by
  obtain ⟨M, hM, hgM⟩ := eq_nM_mul_mM_of_fix c Q' hc g hg he
  have hA : nM c Q' (-tl (g *ᵥ e₀)) * g = mM M := by
    generalize hw : tl (g *ᵥ e₀) = w at hgM ⊢
    rw [hgM, ← Matrix.mul_assoc, nM_mul c Q' hc, neg_add_cancel, nM_zero, Matrix.one_mul]
  have hd := congrArg Matrix.det hA
  rw [det_mul, hdet, mul_one, det_mM, det_nM c Q' hc hQ] at hd
  rw [hA, blk_mM]
  exact ⟨rfl, hM, hd.symm⟩

end Block


/-! ### Base change of the local elements -/

section MapLocal

variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L] {k : ℕ}

theorem map_v3 (σ : K →+* L) (a b : K) (y : Fin k → K) :
    (fun i => σ (v3 a b y i)) = v3 (σ a) (σ b) (fun i => σ (y i)) := by
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;> simp [v3]

theorem nM_mulVec_map (σ : K →+* L) (c : K) (Q' : QuadForm K k) (w : Fin k → K) (x : Fin (k + 1 + 1) → K) :
    nM (σ c) (Q'.map σ) (fun i => σ (w i)) *ᵥ (fun i => σ (x i)) = fun i => σ ((nM c Q' w *ᵥ x) i) := by
  rw [← v3_eta x, map_v3, nM_mulVec_v3, nM_mulVec_v3, map_v3]
  have hH : (Q'.map σ).hessian = Q'.hessian.map σ := Siegel.hessian_map_NF σ Q'
  have hq : (Q'.map σ).eval (fun i => σ (w i)) = σ (Q'.eval w) := (map_eval_apply' σ Q' w).symm
  have hd : ((Q'.map σ).hessian *ᵥ fun i => σ (w i)) ⬝ᵥ (fun i => σ (tl x i)) =
      σ ((Q'.hessian *ᵥ w) ⬝ᵥ tl x) := by
    simp only [hH, dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply, tl]
  refine v3_congr ?_ ?_ ?_
  · rw [hd, hq]; simp [map_sub, map_div₀, map_add, map_mul, map_ofNat]
  · rw [hd, hq]; simp [map_sub, map_div₀, map_add, map_mul, map_ofNat]
  · funext i; simp [tl]

/-- $n(w)$ commutes with base change. -/
theorem nM_map (σ : K →+* L) (c : K) (Q' : QuadForm K k) (w : Fin k → K) :
    (nM c Q' w).map σ = nM (σ c) (Q'.map σ) (fun i => σ (w i)) := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  have hs : (Pi.single j (1 : L) : Fin (k + 1 + 1) → L) =
      fun i => σ ((Pi.single j (1 : K) : Fin (k + 1 + 1) → K) i) := by
    funext i; rw [Pi.single_apply, Pi.single_apply]; split_ifs <;> simp
  rw [hs, nM_mulVec_map]
  funext i
  exact (RingHom.map_mulVec σ _ _ i).symm

end MapLocal

/-! ### The section data of the cone form -/

section ConeData

variable {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k}

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

theorem hess_coneF : ((ConeFinite.Qcone c₀ Q₀').map (algebraMap (𝓞 F) F)).hessian =
    (coneForm (algebraMap (𝓞 F) F c₀) (Q₀'.map (algebraMap (𝓞 F) F))).hessian := by
  congr 1; simp only [ConeFinite.Qcone, map_splitForm, map_neg, coneForm]

theorem qH_eV_cone : qH ((ConeFinite.Qcone c₀ Q₀').map (algebraMap (𝓞 F) F)).hessian eV = 0 := by
  rw [hess_coneF, qH_eq_bH, eV, bH_cone_v3]; simp [bH]

variable (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate)

include hc hQ' in
theorem exists_isoFrame_coneO (hk : 1 ≤ k) :
    Nonempty (IsoFrame ((ConeFinite.Qcone c₀ Q₀').map (algebraMap (𝓞 F) F)).hessian eV) := by
  rw [hess_coneF]
  refine exists_isoFrame_cone _ ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hc) ?_ hk
  exact nondegenerate_QF Q₀' hQ'

/-- **The section data of the cone form**: base point $e = e_0 + e_1$ and an isotropic frame. -/
def coneSecData (hk : 1 ≤ k) : ConeSecData QC where
  e := eV
  e_iso := qH_eV_cone
  Z := (exists_isoFrame_coneO hc hQ' hk).some

theorem coneSecData_eAd (hk : 1 ≤ k) : (coneSecData hc hQ' hk).eAd = eA F k := rfl

end ConeData

/-! ### The decomposition $P = N\rtimes SO(Q_0')(\mathbb A)$ -/

section Decomp

variable {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k} (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate)

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

/-- The stabilizer $P$ of $e$. -/
abbrev Pc (c₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) k) : Subgroup (SOAdele (ConeFinite.Qcone c₀ Q₀')) :=
  MulAction.stabilizer (SOAdele (ConeFinite.Qcone c₀ Q₀')) (eA F k)

/-- **The coordinates of $P$**: $(w, h)\mapsto n_{\mathbb A}(w)\,\mathrm{diag}(1,1,h)$. -/
def decompFun (p : AdeleSpace F (Fin k) × SOAdele Q₀') : Pc c₀ Q₀' :=
  ⟨coneN hc hQ' p.1 * hA p.2, by
    show (coneN hc hQ' p.1 * hA p.2) • eA F k = eA F k
    rw [mul_smul, hA_smul_eA, coneN_smul_eA]⟩

theorem decompFun_val (p : AdeleSpace F (Fin k) × SOAdele Q₀') :
    (decompFun hc hQ' p : SOAdele QC) = coneN hc hQ' p.1 * hA p.2 := rfl

/-- $e_0$ as an adelic vector. -/
abbrev e0A (F : Type) [Field F] [NumberField F] (k : ℕ) : AdeleSpace F (Fin (k + 1 + 1)) :=
  diagVec F (Fin (k + 1 + 1)) e₀

/-- The tail $(y_2,\dots,y_{k+1})$ of an adelic vector. -/
def tlA (y : AdeleSpace F (Fin (k + 1 + 1))) : AdeleSpace F (Fin k) := fun i => y i.succ.succ

theorem adR_tlA (y : AdeleSpace F (Fin (k + 1 + 1))) (w) : adR (tlA y) w = tl (adR y w) := rfl
theorem adC_tlA (y : AdeleSpace F (Fin (k + 1 + 1))) (w) : adC (tlA y) w = tl (adC y w) := rfl
theorem adV_tlA (y : AdeleSpace F (Fin (k + 1 + 1))) (v) : adV (tlA y) v = tl (adV y v) := rfl

theorem map_e₀ {K : Type*} [Field K] (σ : F →+* K) :
    (fun j => σ ((e₀ : Fin (k + 1 + 1) → F) j)) = (e₀ : Fin (k + 1 + 1) → K) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [e₀]

theorem adR_e0A (w : {w : InfinitePlace F // w.IsReal}) : adR (e0A F k) w = e₀ := by rw [← map_e₀ (σR w)]; rfl
theorem adC_e0A (w : {w : InfinitePlace F // w.IsComplex}) : adC (e0A F k) w = e₀ := by rw [← map_e₀ (σC w)]; rfl
theorem adV_e0A (v : HeightOneSpectrum (𝓞 F)) : adV (e0A F k) v = e₀ := by rw [← map_e₀ (σV v)]; rfl

/-- The $N$-coordinate $w(g) = (g\,e_0)'$. -/
def wOf (g : SOAdele QC) : AdeleSpace F (Fin k) := tlA (g • e0A F k)

theorem tl_nM_mulVec_e₀ {K : Type*} [Field K] [CharZero K] (c : K) (Q' : QuadForm K k) (hc' : c ≠ 0)
    (w : Fin k → K) : tl (nM c Q' w *ᵥ (e₀ : Fin (k + 1 + 1) → K)) = w := by
  rw [nM_mulVec_e₀ c Q' hc', tl_v3]

theorem wOf_decomp (p : AdeleSpace F (Fin k) × SOAdele Q₀') : wOf (decompFun hc hQ' p : SOAdele QC) = p.1 := by
  refine adeleSpace_ext (fun w => ?_) (fun w => ?_) (fun v => ?_)
  · rw [wOf, adR_tlA, decompFun_val, smul_apply_fst_fst, matR_mul, matR_coneN, matR_hA, adR_e0A, ← mulVec_mulVec,
      mM_mulVec_e₀, tl_nM_mulVec_e₀ _ _ (cAt_ne_zero hc _)]
  · rw [wOf, adC_tlA, decompFun_val, smul_apply_fst_snd, matC_mul, matC_coneN, matC_hA, adC_e0A, ← mulVec_mulVec,
      mM_mulVec_e₀, tl_nM_mulVec_e₀ _ _ (cAt_ne_zero hc _)]
  · rw [wOf, adV_tlA, decompFun_val, smul_apply_snd, matV_mul, matV_coneN, matV_hA, adV_e0A, ← mulVec_mulVec,
      mM_mulVec_e₀, tl_nM_mulVec_e₀ _ _ (cAt_ne_zero hc _)]

/-- `hA` is injective. -/
theorem hA_injective : Function.Injective (hA (c₀ := c₀) (Q₀' := Q₀')) := fun h h' e =>
  SOAdele.ext_mat (fun w => mM_injective (by rw [← matR_hA (c₀ := c₀), e, matR_hA]))
    (fun w => mM_injective (by rw [← matC_hA (c₀ := c₀), e, matC_hA]))
    (fun v => mM_injective (by rw [← matV_hA (c₀ := c₀), e, matV_hA]))

theorem decompFun_injective : Function.Injective (decompFun hc hQ') := by
  rintro ⟨y, h⟩ ⟨y', h'⟩ e
  have hy : y = y' := by
    have := congrArg (fun p : Pc c₀ Q₀' => wOf (p : SOAdele QC)) e
    simpa only [wOf_decomp] using this
  subst hy
  have : coneN hc hQ' y * hA h = coneN hc hQ' y * hA h' := congrArg Subtype.val e
  rw [mul_right_inj] at this
  rw [hA_injective this]

/-! #### Surjectivity: the Levi component of an element of $P$ -/

section Levi

variable {K : Type*} [Field K] [CharZero K]

/-- The block of an invertible matrix of the form $\mathrm{diag}(1,1,M)$ as an invertible matrix. -/
def blkGL (A : GL (Fin (k + 1 + 1)) K) (hd : (blk A.val).det = 1) : GL (Fin k) K :=
  Matrix.nonsingInvUnit (blk A.val) (by rw [hd]; exact isUnit_one)

theorem blkGL_val (A : GL (Fin (k + 1 + 1)) K) (hd : (blk A.val).det = 1) : (blkGL A hd).val = blk A.val := rfl

theorem blkGL_inv_val (A : GL (Fin (k + 1 + 1)) K) (hA : A.val = mM (blk A.val)) (hd : (blk A.val).det = 1) :
    (blkGL A hd)⁻¹.val = blk A⁻¹.val := by
  have hu : IsUnit (blk A.val).det := by rw [hd]; exact isUnit_one
  have h1 : mM (blk A.val)⁻¹ * A.val = 1 := by
    rw [hA, mM_mul, blk_mM, Matrix.nonsing_inv_mul _ hu, mM_one]
  have h2 : A⁻¹.val = mM (blk A.val)⁻¹ := by
    calc A⁻¹.val = (mM (blk A.val)⁻¹ * A.val) * A⁻¹.val := by rw [h1, Matrix.one_mul]
      _ = mM (blk A.val)⁻¹ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [h2, blk_mM]; rfl

end Levi

/-- The local data of the Levi component at an embedding: for $G\in SO(V)(K)$ with $Ge = e$,
$A = n(-(Ge_0)')\,G = \mathrm{diag}(1,1,M)$. -/
theorem stab_decomp_at {K : Type*} [Field K] [CharZero K] (σ : F →+* K) {G : GL (Fin (k + 1 + 1)) K}
    (hG : IsSOAt QC σ G) (he : G.val *ᵥ (eV : Fin (k + 1 + 1) → K) = eV) :
    let A := nGL (cAt c₀ σ) (QAt Q₀' σ) (cAt_ne_zero hc σ) (-tl (G.val *ᵥ e₀)) * G
    A.val = mM (blk A.val) ∧ IsSOAt Q₀' σ (blkGL A (by
      exact (stab_decomp _ _ (cAt_ne_zero hc σ) (det_hess_cone_ne_zero Q₀' hc hQ' σ)
        (by have := hG.1; rwa [hesAt_cone] at this) hG.2 he).2.2)) := by
  intro A
  have hG1 : G.valᵀ * (coneForm (cAt c₀ σ) (QAt Q₀' σ)).hessian * G.val =
      (coneForm (cAt c₀ σ) (QAt Q₀' σ)).hessian := by have := hG.1; rwa [hesAt_cone] at this
  have hs := stab_decomp _ _ (cAt_ne_zero hc σ) (det_hess_cone_ne_zero Q₀' hc hQ' σ) hG1 hG.2 he
  refine ⟨hs.1, ?_, ?_⟩
  · show (blk A.val)ᵀ * hesAt Q₀' σ * blk A.val = hesAt Q₀' σ
    rw [hesAt_base]; exact hs.2.1
  · exact hs.2.2

end Decomp


/-! ### Surjectivity of the coordinates of $P$ -/

section Surj

variable {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k} (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate)

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

/-- **The Levi block at an embedding** of an element $G$ of $SO(V)(K)$ fixing $e$. -/
def leviAt {K : Type*} [Field K] [CharZero K] (σ : F →+* K) (G : GL (Fin (k + 1 + 1)) K) (hG : IsSOAt QC σ G)
    (he : G.val *ᵥ (eV : Fin (k + 1 + 1) → K) = eV) : GL (Fin k) K :=
  blkGL (nGL (cAt c₀ σ) (QAt Q₀' σ) (cAt_ne_zero hc σ) (-tl (G.val *ᵥ e₀)) * G)
    (stab_decomp _ _ (cAt_ne_zero hc σ) (det_hess_cone_ne_zero Q₀' hc hQ' σ)
      (by have := hG.1; rwa [hesAt_cone] at this) hG.2 he).2.2

theorem isSOAt_leviAt {K : Type*} [Field K] [CharZero K] (σ : F →+* K) (G : GL (Fin (k + 1 + 1)) K)
    (hG : IsSOAt QC σ G) (he : G.val *ᵥ (eV : Fin (k + 1 + 1) → K) = eV) :
    IsSOAt Q₀' σ (leviAt hc hQ' σ G hG he) :=
  (stab_decomp_at hc hQ' σ hG he).2

theorem mM_leviAt {K : Type*} [Field K] [CharZero K] (σ : F →+* K) (G : GL (Fin (k + 1 + 1)) K)
    (hG : IsSOAt QC σ G) (he : G.val *ᵥ (eV : Fin (k + 1 + 1) → K) = eV) :
    mM (leviAt hc hQ' σ G hG he).val = nM (cAt c₀ σ) (QAt Q₀' σ) (-tl (G.val *ᵥ e₀)) * G.val :=
  (stab_decomp_at hc hQ' σ hG he).1.symm

theorem leviAt_inv_val {K : Type*} [Field K] [CharZero K] (σ : F →+* K) (G : GL (Fin (k + 1 + 1)) K)
    (hG : IsSOAt QC σ G) (he : G.val *ᵥ (eV : Fin (k + 1 + 1) → K) = eV) :
    (leviAt hc hQ' σ G hG he)⁻¹.val = blk (G⁻¹.val * nM (cAt c₀ σ) (QAt Q₀' σ) (tl (G.val *ᵥ e₀))) := by
  refine (blkGL_inv_val _ (stab_decomp_at hc hQ' σ hG he).1 _).trans ?_
  congr 1
  rw [_root_.mul_inv_rev, Units.val_mul, nGL_inv_val, neg_neg]

theorem blk_mem_intMat (v : HeightOneSpectrum (𝓞 F)) {A : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) (v.adicCompletion F)}
    (hA : A ∈ intMat v) : blk A ∈ intMat v := fun i j => hA _ _

variable (g : Pc c₀ Q₀')

theorem heR (w : {w : InfinitePlace F // w.IsReal}) :
    (ArchSO.incl _ ((g : SOAdele QC).1.1 w)).val *ᵥ (eV : Fin (k + 1 + 1) → ℝ) = eV := by
  have h := congrArg (fun y => adR y w) (show (g : SOAdele QC) • eA F k = eA F k from g.2)
  simp only [smul_apply_fst_fst, adR_eA] at h
  exact h

theorem heC (w : {w : InfinitePlace F // w.IsComplex}) :
    (ArchSOC.incl _ ((g : SOAdele QC).1.2 w)).val *ᵥ (eV : Fin (k + 1 + 1) → ℂ) = eV := by
  have h := congrArg (fun y => adC y w) (show (g : SOAdele QC) • eA F k = eA F k from g.2)
  simp only [smul_apply_fst_snd, adC_eA] at h
  exact h

theorem heV (v : HeightOneSpectrum (𝓞 F)) :
    ((((g : SOAdele QC).2 : OAf ((ConeFinite.Qcone c₀ Q₀').map (algebraMap (𝓞 F) F))) v : orthGroup ((ConeFinite.Qcone c₀ Q₀').map (algebraMap (𝓞 F) F))
      (v.adicCompletion F)) : GL (Fin (k + 1 + 1)) (v.adicCompletion F)).val *ᵥ
        (eV : Fin (k + 1 + 1) → v.adicCompletion F) = eV := by
  have h := congrArg (fun y => adV y v) (show (g : SOAdele QC) • eA F k = eA F k from g.2)
  simp only [smul_apply_snd, adV_eA] at h
  exact h

theorem adR_wOf (w : {w : InfinitePlace F // w.IsReal}) :
    adR (wOf (g : SOAdele QC)) w = tl (matR QC g w *ᵥ e₀) := by
  rw [wOf, adR_tlA, smul_apply_fst_fst, adR_e0A]

theorem adC_wOf (w : {w : InfinitePlace F // w.IsComplex}) :
    adC (wOf (g : SOAdele QC)) w = tl (matC QC g w *ᵥ e₀) := by
  rw [wOf, adC_tlA, smul_apply_fst_snd, adC_e0A]

theorem adV_wOf (v : HeightOneSpectrum (𝓞 F)) :
    adV (wOf (g : SOAdele QC)) v = tl (matV QC g v *ᵥ e₀) := by
  rw [wOf, adV_tlA, smul_apply_snd, adV_e0A]

/-- **The Levi component** $h(g)\in SO(Q_0')(\mathbb A)$ of $g\in P$: $g = n_{\mathbb A}(w(g))\,\mathrm{diag}(1,1,h(g))$. -/
def leviOf : SOAdele Q₀' :=
  mkSOAdele Q₀' (fun w => leviAt hc hQ' (σR w) _ (isSOAt_R (g : SOAdele QC) w) (heR g w))
    (fun w => isSOAt_leviAt hc hQ' _ _ _ _)
    (fun w => leviAt hc hQ' (σC w) _ (isSOAt_C (g : SOAdele QC) w) (heC g w)) (fun w => isSOAt_leviAt hc hQ' _ _ _ _)
    (fun v => leviAt hc hQ' (σV v) _ (isSOAt_V (g : SOAdele QC) v) (heV g v)) (fun v => isSOAt_leviAt hc hQ' _ _ _ _)
    (by
      filter_upwards [eventually_two_c hc, eventually_intVec (wOf (g : SOAdele QC)),
        ((g : SOAdele QC).2 : OAf ((ConeFinite.Qcone c₀ Q₀').map (algebraMap (𝓞 F) F))).2] with v h2 hy hgv
      have hg' := (mem_glInt_iff v).mp hgv
      rw [adV_wOf] at hy
      refine ⟨?_, ?_⟩
      · exact blk_mem_intMat v (mul_mem_intMat v (nM_mem_intMat v c₀ Q₀' h2 (hy.neg v)) hg'.1)
      · rw [leviAt_inv_val]
        exact blk_mem_intMat v (mul_mem_intMat v hg'.2 (nM_mem_intMat v c₀ Q₀' h2 hy)))

theorem matR_leviOf (w : {w : InfinitePlace F // w.IsReal}) :
    matR Q₀' (leviOf hc hQ' g) w = (leviAt hc hQ' (σR w) _ (isSOAt_R (g : SOAdele QC) w) (heR g w)).val := rfl

theorem matC_leviOf (w : {w : InfinitePlace F // w.IsComplex}) :
    matC Q₀' (leviOf hc hQ' g) w = (leviAt hc hQ' (σC w) _ (isSOAt_C (g : SOAdele QC) w) (heC g w)).val := rfl

theorem matV_leviOf (v : HeightOneSpectrum (𝓞 F)) :
    matV Q₀' (leviOf hc hQ' g) v = (leviAt hc hQ' (σV v) _ (isSOAt_V (g : SOAdele QC) v) (heV g v)).val := rfl

theorem decompFun_leviOf : decompFun hc hQ' (wOf (g : SOAdele QC), leviOf hc hQ' g) = g := by
  apply Subtype.ext
  rw [decompFun_val]
  refine SOAdele.ext_mat (fun w => ?_) (fun w => ?_) (fun v => ?_)
  · have e : matR QC (g : SOAdele QC) w = (ArchSO.incl _ ((g : SOAdele QC).1.1 w)).val := rfl
    rw [matR_mul, matR_coneN, matR_hA, matR_leviOf, mM_leviAt, adR_wOf, e, ← Matrix.mul_assoc,
      nM_mul _ _ (cAt_ne_zero hc _), add_neg_cancel, nM_zero, Matrix.one_mul]
  · have e : matC QC (g : SOAdele QC) w = (ArchSOC.incl _ ((g : SOAdele QC).1.2 w)).val := rfl
    rw [matC_mul, matC_coneN, matC_hA, matC_leviOf, mM_leviAt, adC_wOf, e, ← Matrix.mul_assoc,
      nM_mul _ _ (cAt_ne_zero hc _), add_neg_cancel, nM_zero, Matrix.one_mul]
  · have e : matV QC (g : SOAdele QC) v = ((((g : SOAdele QC).2 : OAf ((ConeFinite.Qcone c₀ Q₀').map
        (algebraMap (𝓞 F) F))) v : orthGroup ((ConeFinite.Qcone c₀ Q₀').map (algebraMap (𝓞 F) F))
          (v.adicCompletion F)) : GL (Fin (k + 1 + 1)) (v.adicCompletion F)).val := rfl
    rw [matV_mul, matV_coneN, matV_hA, matV_leviOf, mM_leviAt, adV_wOf, e, ← Matrix.mul_assoc,
      nM_mul _ _ (cAt_ne_zero hc _), add_neg_cancel, nM_zero, Matrix.one_mul]

theorem decompFun_surjective : Function.Surjective (decompFun hc hQ') := fun g =>
  ⟨_, decompFun_leviOf hc hQ' g⟩

end Surj

/-! ### Measurability and the measurable equivalence -/

section DecompEquiv

variable {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k} (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate)

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

theorem measurable_coneN : Measurable (coneN hc hQ') := by
  refine measurable_mkSOAdele _ (fun w => ?_) (fun w => ?_) (fun w => ?_) (fun w => ?_) (fun v => ?_) (fun v => ?_)
  · exact measurable_of_continuous_matrix ((ConeFinite.continuous_nM _ _).comp (continuous_adR w))
  · exact measurable_of_continuous_matrix ((ConeFinite.continuous_nM _ _).comp (continuous_adR w).neg)
  · exact measurable_of_continuous_matrix ((ConeFinite.continuous_nM _ _).comp (continuous_adC w))
  · exact measurable_of_continuous_matrix ((ConeFinite.continuous_nM _ _).comp (continuous_adC w).neg)
  · exact measurable_of_continuous_matrix ((ConeFinite.continuous_nM _ _).comp (continuous_adV v))
  · exact measurable_of_continuous_matrix ((ConeFinite.continuous_nM _ _).comp (continuous_adV v).neg)

theorem continuous_mM {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] :
    Continuous fun M : Matrix (Fin k) (Fin k) K => mM M :=
  continuous_cornerMat_one.comp continuous_cornerMat_one

theorem measurable_hA : Measurable (hA (c₀ := c₀) (Q₀' := Q₀')) := by
  refine measurable_SOAdele_of_mat _ (fun w => ?_) (fun w => ?_) (fun w => ?_) (fun w => ?_) (fun v => ?_) (fun v => ?_)
  · exact measurable_of_continuous_matrix (continuous_mM.comp (Units.continuous_val.comp
      ((ArchSO.continuous_incl _).comp ((continuous_apply w).comp (continuous_fst.comp continuous_fst)))))
  · exact measurable_of_continuous_matrix (continuous_mM.comp (Units.continuous_val.comp (continuous_inv.comp
      ((ArchSO.continuous_incl _).comp ((continuous_apply w).comp (continuous_fst.comp continuous_fst))))))
  · exact measurable_of_continuous_matrix (continuous_mM.comp (Units.continuous_val.comp
      (continuous_subtype_val.comp ((continuous_apply w).comp (continuous_snd.comp continuous_fst)))))
  · exact measurable_of_continuous_matrix (continuous_mM.comp (Units.continuous_val.comp (continuous_inv.comp
      (continuous_subtype_val.comp ((continuous_apply w).comp (continuous_snd.comp continuous_fst))))))
  · exact measurable_of_continuous_matrix (continuous_mM.comp (Units.continuous_val.comp
      (continuous_subtype_val.comp ((RestrictedProduct.continuous_eval v).comp
        (continuous_subtype_val.comp continuous_snd)))))
  · exact measurable_of_continuous_matrix (continuous_mM.comp (Units.continuous_val.comp (continuous_inv.comp
      (continuous_subtype_val.comp ((RestrictedProduct.continuous_eval v).comp
        (continuous_subtype_val.comp continuous_snd))))))

theorem measurable_decompFun : Measurable (decompFun hc hQ') :=
  Measurable.subtype_mk (((measurable_coneN hc hQ').comp measurable_fst).mul (measurable_hA.comp measurable_snd))

/-- **The coordinates $\mathbb A^k\times SO(Q_0')(\mathbb A)\simeq P$** as a measurable equivalence (Lusin–Souslin). -/
def decompEquiv : AdeleSpace F (Fin k) × SOAdele Q₀' ≃ᵐ Pc c₀ Q₀' where
  toEquiv := Equiv.ofBijective (decompFun hc hQ') ⟨decompFun_injective hc hQ', decompFun_surjective hc hQ'⟩
  measurable_toFun := measurable_decompFun hc hQ'
  measurable_invFun := by
    have := polishSpace_of_isTopologicalGroup (SOAdele Q₀')
    have : BorelSpace (AdeleSpace F (Fin k)) := inferInstance
    have : StandardBorelSpace (AdeleSpace F (Fin k)) := inferInstance
    have hemb := (measurable_decompFun hc hQ').measurableEmbedding (decompFun_injective hc hQ')
    intro A hA
    have : (Equiv.ofBijective (decompFun hc hQ') ⟨decompFun_injective hc hQ', decompFun_surjective hc hQ'⟩).symm ⁻¹' A =
        decompFun hc hQ' '' A := by
      ext g
      simp only [mem_preimage, mem_image]
      constructor
      · intro hg
        exact ⟨_, hg, Equiv.ofBijective_apply_symm_apply _ _ _⟩
      · rintro ⟨p, hp, rfl⟩
        convert hp; exact Equiv.ofBijective_symm_apply_apply _ _ p
    rw [this]
    exact hemb.measurableSet_image.mpr hA

theorem decompEquiv_apply (p : AdeleSpace F (Fin k) × SOAdele Q₀') :
    decompEquiv hc hQ' p = decompFun hc hQ' p := rfl

end DecompEquiv


/-! ### Rationality -/

section Rational

variable {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k} (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate)

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

theorem mM_map {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L] (σ : K →+* L)
    (M : Matrix (Fin k) (Fin k) K) : (mM M).map σ = mM (M.map σ) := by
  rw [mM, cornerMat_map, cornerMat_map, map_one, mM]

theorem hessF_cone_eq : ((ConeFinite.Qcone c₀ Q₀').map (algebraMap (𝓞 F) F)).hessian.map (algebraMap F F) =
    (coneForm (algebraMap (𝓞 F) F c₀) (Q₀'.map (algebraMap (𝓞 F) F))).hessian := by
  rw [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id, hess_coneF]

include hc in
theorem cF_ne : algebraMap (𝓞 F) F c₀ ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hc

include hc hQ' in
theorem det_hessF_cone_ne :
    (coneForm (algebraMap (𝓞 F) F c₀) (Q₀'.map (algebraMap (𝓞 F) F))).hessian.det ≠ 0 := by
  rw [← hess_coneF]; exact nondegenerate_QF _ (ConeFinite.nondeg_cone c₀ Q₀' hc hQ')

include hc hQ' in
/-- The rational element $n(\nu)\in SO(V)(F)$, $\nu\in F^k$. -/
def nRat (ν : Fin k → F) : soSub ((ConeFinite.Qcone c₀ Q₀').map (algebraMap (𝓞 F) F)) F :=
  ⟨⟨nGL _ _ (cF_ne hc) ν, (mem_orthGroup _).mpr (by rw [hessF_cone_eq]; exact isometry_nM _ _ (cF_ne hc) ν)⟩,
    det_nM _ _ (cF_ne hc) (det_hessF_cone_ne hc hQ') ν⟩

theorem coneN_diagVec (ν : Fin k → F) : coneN hc hQ' (diagVec F (Fin k) ν) = diagSOAdele QC (nRat hc hQ' ν) := by
  refine SOAdele.ext_mat (fun w => ?_) (fun w => ?_) (fun v => ?_)
  · rw [matR_coneN]
    exact (nM_map (σR w) _ _ ν).symm
  · rw [matC_coneN]
    exact (nM_map (σC w) _ _ ν).symm
  · rw [matV_coneN]
    exact (nM_map (σV v) _ _ ν).symm

/-- **$n_{\mathbb A}(F^k)\subseteq SO(V)(F)$.** -/
theorem coneN_mem_gamma {ν : AdeleSpace F (Fin k)} (hν : ν ∈ diagVecSub F (Fin k)) :
    coneN hc hQ' ν ∈ GammaSOAdele QC := by
  obtain ⟨ν₀, rfl⟩ := hν
  exact ⟨nRat hc hQ' ν₀, (coneN_diagVec hc hQ' ν₀).symm⟩

/-- The rational element $\mathrm{diag}(1,1,\eta)\in SO(V)(F)$. -/
def mRat (η : soSub (Q₀'.map (algebraMap (𝓞 F) F)) F) : soSub ((ConeFinite.Qcone c₀ Q₀').map (algebraMap (𝓞 F) F)) F :=
  ⟨⟨mGL ((η : orthGroup (Q₀'.map (algebraMap (𝓞 F) F)) F) : GL (Fin k) F), (mem_orthGroup _).mpr (by
      rw [hessF_cone_eq]
      refine isometry_mM _ _ ?_
      have := (mem_orthGroup _).mp (η : orthGroup (Q₀'.map (algebraMap (𝓞 F) F)) F).2
      rwa [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at this)⟩, by
    show (mM _).det = 1
    rw [det_mM]; exact η.2⟩

theorem hA_diag (η : soSub (Q₀'.map (algebraMap (𝓞 F) F)) F) :
    hA (c₀ := c₀) (diagSOAdele Q₀' η) = diagSOAdele QC (mRat η) := by
  refine SOAdele.ext_mat (fun w => ?_) (fun w => ?_) (fun v => ?_)
  · have hm : matR QC (diagSOAdele QC (mRat η)) w =
        (mM ((η : orthGroup (Q₀'.map (algebraMap (𝓞 F) F)) F) : GL (Fin k) F).val).map (σR w) := rfl
    have hm' : matR Q₀' (diagSOAdele Q₀' η) w =
        ((η : orthGroup (Q₀'.map (algebraMap (𝓞 F) F)) F) : GL (Fin k) F).val.map (σR w) := rfl
    rw [matR_hA, hm, hm', mM_map]
  · have hm : matC QC (diagSOAdele QC (mRat η)) w =
        (mM ((η : orthGroup (Q₀'.map (algebraMap (𝓞 F) F)) F) : GL (Fin k) F).val).map (σC w) := rfl
    have hm' : matC Q₀' (diagSOAdele Q₀' η) w =
        ((η : orthGroup (Q₀'.map (algebraMap (𝓞 F) F)) F) : GL (Fin k) F).val.map (σC w) := rfl
    rw [matC_hA, hm, hm', mM_map]
  · have hm : matV QC (diagSOAdele QC (mRat η)) v =
        (mM ((η : orthGroup (Q₀'.map (algebraMap (𝓞 F) F)) F) : GL (Fin k) F).val).map (σV v) := rfl
    have hm' : matV Q₀' (diagSOAdele Q₀' η) v =
        ((η : orthGroup (Q₀'.map (algebraMap (𝓞 F) F)) F) : GL (Fin k) F).val.map (σV v) := rfl
    rw [matV_hA, hm, hm', mM_map]

/-- **$\mathrm{diag}(1,1,SO(Q_0')(F))\subseteq SO(V)(F)$.** -/
theorem hA_mem_gamma {η : SOAdele Q₀'} (hη : η ∈ GammaSOAdele Q₀') : hA (c₀ := c₀) η ∈ GammaSOAdele QC := by
  obtain ⟨η₀, rfl⟩ := hη
  exact ⟨mRat η₀, (hA_diag η₀).symm⟩

theorem coneN_zero : coneN hc hQ' (0 : AdeleSpace F (Fin k)) = 1 := by
  have h := coneN_add hc hQ' (0 : AdeleSpace F (Fin k)) 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem coneN_neg (y : AdeleSpace F (Fin k)) : (coneN hc hQ' y)⁻¹ = coneN hc hQ' (-y) := by
  rw [inv_eq_iff_mul_eq_one, ← coneN_add, add_neg_cancel, coneN_zero]

theorem tlA_diagVec (ξ : Fin (k + 1 + 1) → F) : tlA (diagVec F (Fin (k + 1 + 1)) ξ) = diagVec F (Fin k) (tl ξ) := rfl

theorem decompEquiv_symm (p : Pc c₀ Q₀') :
    (decompEquiv hc hQ').symm p = (wOf (p : SOAdele QC), leviOf hc hQ' p) := by
  apply (decompEquiv hc hQ').injective
  rw [MeasurableEquiv.apply_symm_apply, decompEquiv_apply, decompFun_leviOf]

/-- **Rational points of $P$ have rational coordinates.** -/
theorem decomp_symm_rat (p : Pc c₀ Q₀') (hp : (p : SOAdele QC) ∈ GammaSOAdele QC) :
    ((decompEquiv hc hQ').symm p).1 ∈ diagVecSub F (Fin k) ∧ ((decompEquiv hc hQ').symm p).2 ∈ GammaSOAdele Q₀' := by
  rw [decompEquiv_symm]
  obtain ⟨γ, hγ⟩ := hp
  set G := ((γ : orthGroup ((ConeFinite.Qcone c₀ Q₀').map (algebraMap (𝓞 F) F)) F) : GL (Fin (k + 1 + 1)) F)
  -- the N-coordinate
  have hw : wOf (p : SOAdele QC) = diagVec F (Fin k) (tl (G.val *ᵥ e₀)) := by
    rw [wOf, ← hγ, diagSOAdele_smul_diagVec, tlA_diagVec]
  refine ⟨⟨_, hw.symm⟩, ?_⟩
  -- γ fixes e
  have hfix : G.val *ᵥ (eV : Fin (k + 1 + 1) → F) = eV := by
    have h := p.2
    change (p : SOAdele QC) • eA F k = eA F k at h
    rw [← hγ, diagSOAdele_smul_diagVec] at h
    exact diagVec_injective h
  have hiso : G.valᵀ * (coneForm (algebraMap (𝓞 F) F c₀) (Q₀'.map (algebraMap (𝓞 F) F))).hessian * G.val =
      (coneForm (algebraMap (𝓞 F) F c₀) (Q₀'.map (algebraMap (𝓞 F) F))).hessian := by
    have := (mem_orthGroup _).mp (γ : orthGroup ((ConeFinite.Qcone c₀ Q₀').map (algebraMap (𝓞 F) F)) F).2
    rwa [hessF_cone_eq] at this
  have hs := stab_decomp _ _ (cF_ne hc) (det_hessF_cone_ne hc hQ') hiso γ.2 hfix
  set B := nM (algebraMap (𝓞 F) F c₀) (Q₀'.map (algebraMap (𝓞 F) F)) (-tl (G.val *ᵥ e₀)) * G.val
  -- the Levi coordinate is rational
  let Bu : GL (Fin (k + 1 + 1)) F := (nRat hc hQ' (-tl (G.val *ᵥ e₀)) * γ : soSub _ F)
  have hBu : Bu.val = B := rfl
  let η₀ : soSub (Q₀'.map (algebraMap (𝓞 F) F)) F :=
    ⟨⟨blkGL Bu (by rw [hBu]; exact hs.2.2), (mem_orthGroup _).mpr (by
      rw [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id]; exact hs.2.1)⟩, hs.2.2⟩
  refine ⟨η₀, hA_injective (c₀ := c₀) ?_⟩
  rw [hA_diag]
  have hlev : hA (leviOf hc hQ' p) = (coneN hc hQ' (wOf (p : SOAdele QC)))⁻¹ * (p : SOAdele QC) := by
    have h := congrArg Subtype.val (decompFun_leviOf hc hQ' p)
    rw [decompFun_val] at h
    rw [eq_inv_mul_iff_mul_eq]; exact h
  rw [hlev, coneN_neg, hw, ← map_neg, coneN_diagVec, ← hγ, ← map_mul]
  congr 1
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  show mM (blk B) = B
  exact hs.1.symm

end Rational

end QuadFormsKB.Tamagawa.Measure.Weil

end
