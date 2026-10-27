/-
# The adelic isomorphism $(D\otimes\mathbb A)^\times/\mathbb A^\times \cong SO(D^0)(\mathbb A)$ and the global points

**Layer:** $F$ a number field, $a, b \in \mathcal O_F\setminus0$, $D = (a,b)_F$, $Q_0$ = `QuatZeta.pureFormO a b`
($= \operatorname{nrd}|_{D^0} = \langle -a,-b,ab\rangle$), any signature (definite or not, any number field).

**Defines/proves**
* `conjAdele a b : (D\otimes\mathbb A)^\times \to SO(V)(\mathbb A)$ = `SOAdele Q₀` (= `conjInf` $\times$ `conjFin` after
  `quatUnitsEquiv`); **`continuous_conjAdele`**, **`conjAdele_surjective`**, **`conjAdele_eq_one_iff`**
  (kernel = $\mathbb A^\times$ = `(quatScalar a b).range`), **`isOpenMap_conjAdele`** (open mapping theorem for
  $\sigma$-compact locally compact groups, Mathlib's `MonoidHom.isOpenMap_of_sigmaCompact`);
* `PDAdele a b` $:= (D\otimes\mathbb A)^\times/\mathbb A^\times$ (quotient group, quotient topology) and
  **`pdAdeleEquiv a b : PDAdele a b ≃ₜ* SOAdele Q₀`** — the adelic points of $PD^\times = D^\times/G_m \cong SO(D^0)$ as
  topological groups;
* `conjF a b : D^\times \to SO(V)(F)` (over $F$), `conjF_surjective`, and the compatibility with the diagonal
  embeddings **`conjAdele_diag`**: $c_{\mathbb A}(\xi) = $ `diagSOAdele Q₀` $(c_F(\xi))$; hence
  **`map_quatUnitsSub_conjAdele`**: $c_{\mathbb A}(D^\times) = SO(V)(F)$ = `GammaSOAdele Q₀`, and on the quotient
  **`map_pdGamma`**: $D^\times\mathbb A^\times/\mathbb A^\times \mapsto$ `GammaSOAdele Q₀`.

Source: Weil 1982, §3.7(a), p. 63 (the isomorphism $SO_3 \cong D^\times/G_m$ of algebraic groups), §2.4 (adelic points,
$G_k\subset G_{\mathbb A}$ discrete).
-/
import QuadFormsKB.Tamagawa.Measure.Weil.PDArch

open Matrix Quaternion NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain Topology

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.QuatZeta QuadFormsKB.Siegel
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

/-! ### Base change of the conjugation matrix -/

/-- **Conjugation commutes with base change**: if $\beta$ and $\beta^{-1}$ have the images under $f : K\to L$ of the
coordinates of $\alpha$ and $\alpha^{-1}$, then $c(\beta) = f(c(\alpha))$ entrywise. -/
theorem conjGL_map_of_coords {K L : Type*} [Field K] [Field L] (f : K →+* L) {A B : K} (α : (ℍ[K,A,B])ˣ)
    (β : (ℍ[L, f A, f B])ˣ) (h0 : β.val.re = f α.val.re) (h1 : β.val.imI = f α.val.imI)
    (h2 : β.val.imJ = f α.val.imJ) (h3 : β.val.imK = f α.val.imK) (h0' : β⁻¹.val.re = f α⁻¹.val.re)
    (h1' : β⁻¹.val.imI = f α⁻¹.val.imI) (h2' : β⁻¹.val.imJ = f α⁻¹.val.imJ) (h3' : β⁻¹.val.imK = f α⁻¹.val.imK) :
    ((conjGL β : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = ((conjGL α : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map f := by
  rw [conjGL_val, conjGL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [nMat, imv, Quat.pure, nrd, Pi.single_apply, h0, h1, h2, h3, h0', h1', h2', h3']

variable {F : Type} [Field F] [NumberField F] (a b : 𝓞 F)

local notation "Q₀" => pureFormO a b
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (pureFormO a b)

/-! ### The adelic map -/

/-- **$(D\otimes\mathbb A)^\times \to SO(V)(\mathbb A)$**, $\alpha\mapsto(y\mapsto\alpha_w y\alpha_w^{-1})_{w\le\infty}$. -/
@[kb "weil1982" "§3.7(a), p. 63"]
def conjAdele : (QuatAdele (a : F) (b : F))ˣ →* SOAdele Q₀ :=
  ((conjInf a b).prodMap (conjFin a b)).comp (quatUnitsEquiv (a : F) (b : F)).toMulEquiv.toMonoidHom

theorem conjAdele_apply (α : (QuatAdele (a : F) (b : F))ˣ) :
    conjAdele a b α = (conjInf a b (quatUnitsEquiv _ _ α).1, conjFin a b (quatUnitsEquiv _ _ α).2) := rfl

theorem continuous_conjAdele : Continuous (conjAdele a b) :=
  ((continuous_conjInf a b).prodMap (continuous_conjFin a b)).comp (quatUnitsEquiv _ _).continuous

/-- **$(D\otimes\mathbb A)^\times \to SO(V)(\mathbb A)$ is surjective** ($a, b \ne 0$). -/
@[kb "weil1982" "§3.7(a), p. 63"]
theorem conjAdele_surjective (ha : a ≠ 0) (hb : b ≠ 0) : Function.Surjective (conjAdele a b) := by
  intro g
  obtain ⟨x, hx⟩ := conjInf_surjective a b ha hb g.1
  obtain ⟨y, hy⟩ := conjFin_surjective a b ha hb g.2
  refine ⟨(quatUnitsEquiv _ _).symm (x, y), ?_⟩
  rw [conjAdele_apply, ContinuousMulEquiv.apply_symm_apply]
  exact Prod.ext hx hy

theorem quatUnitsEquiv_quatScalar (c : (Adeles F)ˣ) :
    quatUnitsEquiv (a : F) (b : F) (quatScalar (a : F) (b : F) c) =
      (infScalar (a : F) (b : F) (MulEquiv.prodUnits c).1, finScalar (a : F) (b : F) (MulEquiv.prodUnits c).2) :=
  Prod.ext (Units.ext (QuaternionAlgebra.ext rfl rfl rfl rfl)) (Units.ext (QuaternionAlgebra.ext rfl rfl rfl rfl))

/-- **The kernel of $(D\otimes\mathbb A)^\times \to SO(V)(\mathbb A)$ is $\mathbb A^\times$.** -/
@[kb "weil1982" "§3.7(a), p. 63"]
theorem conjAdele_eq_one_iff (ha : a ≠ 0) (α : (QuatAdele (a : F) (b : F))ˣ) :
    conjAdele a b α = 1 ↔ α ∈ (quatScalar (a : F) (b : F)).range := by
  constructor
  · intro h
    obtain ⟨c₁, hc₁⟩ := (conjInf_eq_one_iff a b ha _).1 (congrArg Prod.fst h)
    obtain ⟨c₂, hc₂⟩ := (conjFin_eq_one_iff a b ha _).1 (congrArg Prod.snd h)
    refine ⟨MulEquiv.prodUnits.symm (c₁, c₂), (quatUnitsEquiv (a : F) (b : F)).injective ?_⟩
    rw [quatUnitsEquiv_quatScalar, MulEquiv.apply_symm_apply, hc₁, hc₂]
    rfl
  · rintro ⟨c, rfl⟩
    rw [conjAdele_apply, quatUnitsEquiv_quatScalar]
    exact Prod.ext ((conjInf_eq_one_iff a b ha _).2 ⟨_, rfl⟩) ((conjFin_eq_one_iff a b ha _).2 ⟨_, rfl⟩)

theorem ker_conjAdele (ha : a ≠ 0) : (conjAdele a b).ker = (quatScalar (a : F) (b : F)).range := by
  ext α; exact (MonoidHom.mem_ker).trans (conjAdele_eq_one_iff a b ha α)

instance : LocallyCompactSpace (SOAf Q₀) :=
  (isClosed_soAf QF).isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- **`conjAdele` is open** (open mapping theorem for $\sigma$-compact groups onto a Baire group). -/
theorem isOpenMap_conjAdele (ha : a ≠ 0) (hb : b ≠ 0) : IsOpenMap (conjAdele a b) :=
  MonoidHom.isOpenMap_of_sigmaCompact _ (conjAdele_surjective a b ha hb) (continuous_conjAdele a b)

/-! ### The quotient $PD^\times(\mathbb A) = (D\otimes\mathbb A)^\times/\mathbb A^\times$ -/

instance quatScalar_range_normal : ((quatScalar (a : F) (b : F)).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨c, rfl⟩ := hn
  refine ⟨c, ?_⟩
  rw [← quatScalar_comm, mul_assoc, mul_inv_cancel, mul_one]

/-- **$PD^\times(\mathbb A) = (D\otimes\mathbb A)^\times/\mathbb A^\times$** (quotient group with the quotient topology). -/
abbrev PDAdele : Type := (QuatAdele (a : F) (b : F))ˣ ⧸ (quatScalar (a : F) (b : F)).range

/-- The group isomorphism $PD^\times(\mathbb A) \cong SO(V)(\mathbb A)$. -/
def pdAdeleMulEquiv (ha : a ≠ 0) (hb : b ≠ 0) : PDAdele a b ≃* SOAdele Q₀ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_conjAdele a b ha).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (conjAdele_surjective a b ha hb))

theorem pdAdeleMulEquiv_mk (ha : a ≠ 0) (hb : b ≠ 0) (α : (QuatAdele (a : F) (b : F))ˣ) :
    pdAdeleMulEquiv a b ha hb (QuotientGroup.mk α) = conjAdele a b α := rfl

theorem continuous_pdAdeleMulEquiv (ha : a ≠ 0) (hb : b ≠ 0) : Continuous (pdAdeleMulEquiv a b ha hb) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_conjAdele a b)

theorem isOpenMap_pdAdeleMulEquiv (ha : a ≠ 0) (hb : b ≠ 0) : IsOpenMap (pdAdeleMulEquiv a b ha hb) := by
  intro U hU
  have hpre : IsOpen ((QuotientGroup.mk : (QuatAdele (a : F) (b : F))ˣ → PDAdele a b) ⁻¹' U) :=
    hU.preimage (QuotientGroup.isQuotientMap_mk _).continuous
  have himg : (pdAdeleMulEquiv a b ha hb) '' U =
      (conjAdele a b) '' ((QuotientGroup.mk : (QuatAdele (a : F) (b : F))ˣ → PDAdele a b) ⁻¹' U) := by
    ext g
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective u
      exact ⟨α, hu, rfl⟩
    · rintro ⟨α, hα, rfl⟩
      exact ⟨_, hα, rfl⟩
  rw [himg]
  exact isOpenMap_conjAdele a b ha hb _ hpre

/-- **The adelic isomorphism $PD^\times(\mathbb A) = (D\otimes\mathbb A)^\times/\mathbb A^\times \cong SO(D^0)(\mathbb A)$**
as topological groups ($a, b \in \mathcal O_F\setminus0$, any number field, any signature). Placewise it is
$D_v^\times/F_v^\times \cong SO(D^0)(F_v)$.

Source: Weil 1982, §3.7(a), p. 63. -/
@[kb "weil1982" "§3.7(a), p. 63"]
def pdAdeleEquiv (ha : a ≠ 0) (hb : b ≠ 0) : PDAdele a b ≃ₜ* SOAdele Q₀ :=
  { pdAdeleMulEquiv a b ha hb with
    continuous_toFun := continuous_pdAdeleMulEquiv a b ha hb
    continuous_invFun := ((pdAdeleMulEquiv a b ha hb).toEquiv.toHomeomorphOfContinuousOpen
      (continuous_pdAdeleMulEquiv a b ha hb) (isOpenMap_pdAdeleMulEquiv a b ha hb)).symm.continuous }

theorem pdAdeleEquiv_mk (ha : a ≠ 0) (hb : b ≠ 0) (α : (QuatAdele (a : F) (b : F))ˣ) :
    pdAdeleEquiv a b ha hb (QuotientGroup.mk α) = conjAdele a b α := rfl

/-! ### Global points: $D^\times/F^\times \cong SO(V)(F)$, compatibly with the diagonal embeddings -/

theorem hessian_QF_self : (QF).hessian.map (algebraMap F F) = (pureForm (a : F) (b : F)).hessian := by
  rw [hQF]; simp

/-- **$D^\times \to SO(V)(F)$** (the conjugation over $F$, in the `soSub` form). -/
def conjF : (ℍ[F, (a : F), (b : F)])ˣ →* soSub QF F where
  toFun ξ := ⟨⟨conjGL ξ, by
    rw [mem_orthGroup, hessian_QF_self]
    exact ((mem_SO_iff_hessian (two_ne_zero : (2 : F) ≠ 0)).1 (conjGL_mem ξ)).2⟩, det_conjLin ξ⟩
  map_one' := by ext : 3; exact congrArg (fun g : SO (pureForm (a : F) (b : F)) => (g : GL (Fin 3) F).val) (map_one conjSO)
  map_mul' ξ η := by
    ext : 3; exact congrArg (fun g : SO (pureForm (a : F) (b : F)) => (g : GL (Fin 3) F).val) (map_mul conjSO ξ η)

@[simp] theorem conjF_coe (ξ : (ℍ[F, (a : F), (b : F)])ˣ) :
    (((conjF a b ξ : soSub QF F) : orthGroup QF F) : GL (Fin 3) F) = conjGL ξ := rfl

theorem conjF_surjective (ha : a ≠ 0) (hb : b ≠ 0) : Function.Surjective (conjF a b) := by
  intro γ
  have hA : (a : F) ≠ 0 := by exact_mod_cast ha
  have hB : (b : F) ≠ 0 := by exact_mod_cast hb
  have hmem : ((γ : orthGroup QF F) : GL (Fin 3) F) ∈ SO (pureForm (a : F) (b : F)) := by
    rw [mem_SO_iff_hessian (two_ne_zero : (2 : F) ≠ 0), ← hessian_QF_self]
    exact ⟨mem_soSub.1 γ.2, (mem_orthGroup QF).1 (γ : orthGroup QF F).2⟩
  obtain ⟨ξ, hξ⟩ := conjSO_surjective (two_ne_zero : (2 : F) ≠ 0) hA hB ⟨_, hmem⟩
  exact ⟨ξ, by ext : 3; exact congrArg (fun g : SO (pureForm (a : F) (b : F)) => (g : GL (Fin 3) F).val) hξ⟩

/-- The diagonal embedding $D^\times \to (D\otimes\mathbb A)^\times$. -/
abbrev quatDiagUnit : (ℍ[F, (a : F), (b : F)])ˣ →* (QuatAdele (a : F) (b : F))ˣ :=
  Units.map (quatDiagRing (a : F) (b : F)).toMonoidHom

/-- **Compatibility with the global points:** $c_{\mathbb A}(\xi) = (c_F(\xi))_{\mathrm{diag}}$ for $\xi \in D^\times$. -/
theorem conjAdele_diag (ξ : (ℍ[F, (a : F), (b : F)])ˣ) :
    conjAdele a b (quatDiagUnit a b ξ) = diagSOAdele Q₀ (conjF a b ξ) := by
  refine Prod.ext (Prod.ext (funext fun w => archSO_ext ?_) (funext fun w => archSOC_ext ?_)) ?_
  · change conjGL _ = Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) (conjGL ξ)
    ext : 1
    refine conjGL_map_of_coords (embedding_of_isReal w.2) ξ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact mixedEmbedding_apply_isReal F _ w
  · change conjGL _ = Matrix.GeneralLinearGroup.map w.1.embedding (conjGL ξ)
    ext : 1
    refine conjGL_map_of_coords w.1.embedding ξ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact mixedEmbedding_apply_isComplex F _ w
  · ext v : 3
    change conjGL _ = Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (conjGL ξ)
    ext : 1
    refine conjGL_map_of_coords (algebraMap F (v.adicCompletion F)) ξ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl

/-- **$c_{\mathbb A}(D^\times) = SO(V)(F)$** inside $SO(V)(\mathbb A)$: the image of the diagonal $D^\times$ is
`GammaSOAdele`. -/
@[kb "weil1982" "§3.7(a), p. 63"]
theorem map_quatUnitsSub_conjAdele (ha : a ≠ 0) (hb : b ≠ 0) :
    (quatUnitsSub (a : F) (b : F)).map (conjAdele a b) = GammaSOAdele Q₀ := by
  ext g
  constructor
  · rintro ⟨_, ⟨ξ, rfl⟩, rfl⟩
    exact ⟨conjF a b ξ, (conjAdele_diag a b ξ).symm⟩
  · rintro ⟨γ, rfl⟩
    obtain ⟨ξ, rfl⟩ := conjF_surjective a b ha hb γ
    exact ⟨_, ⟨ξ, rfl⟩, conjAdele_diag a b ξ⟩

/-- $PD^\times(F) = D^\times\mathbb A^\times/\mathbb A^\times$ inside $PD^\times(\mathbb A)$. -/
abbrev pdGamma : Subgroup (PDAdele a b) := (quatUnitsSub (a : F) (b : F)).map (QuotientGroup.mk' _)

/-- **The isomorphism carries $PD^\times(F)$ onto $SO(V)(F)$** (`GammaSOAdele`). -/
@[kb "weil1982" "§3.7(a), p. 63"]
theorem map_pdGamma (ha : a ≠ 0) (hb : b ≠ 0) :
    (pdGamma a b).map (pdAdeleEquiv a b ha hb).toMulEquiv.toMonoidHom = GammaSOAdele Q₀ := by
  rw [← map_quatUnitsSub_conjAdele a b ha hb, Subgroup.map_map]
  rfl

end QuadFormsKB.Tamagawa.Measure.Weil
