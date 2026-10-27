/-
# An Eisenstein series with prescribed constant terms at every cusp

Let $f : \mathbb{H}^d \to \mathbb{C}$ have a constant term $\mathrm{cv}_k(f, A)$ at every cusp $A\infty$ (`HasCuspLimits f k`) and satisfy
$f\,|_k\,\gamma = \chi(d)f$ on $\Gamma_0(\mathfrak N)$. We build **one** Eisenstein series $E_f = E_k(\cdot; W_f)$ with
$$\lim(E_f\,|_k\,A) = \mathrm{cv}_k(f, A)\quad\text{for every } A \in \mathrm{SL}_2(F)$$
(`tendsto_eisGen_slash`), $E_f \in M_k(\Gamma_0(\mathfrak N), \chi)$ for $k \ge 3$ (`eisGen_mem_modularFormChar`), and hence
**$f - E_f \in S_k(\Gamma_0(\mathfrak N), \chi)$** for $f \in M_k(\Gamma_0(\mathfrak N), \chi)$ (`sub_eisGen_mem_cuspFormChar`).

**The weight: supported at one point per cusp line.** For a row vector $x \ne 0$ let $\varphi_f(x) = \mathrm{cv}_k(f, A_x)$ for any $A_x$ with
$(0, 1)A_x^{-1} = x$ (`phiF`; well defined by `cuspVal_eq_of_col`). Then
* $\varphi_f(tx) = N(t)^k\varphi_f(x)$ (`phiF_smul`, from $\mathrm{diag}(t, t^{-1})$),
* $\varphi_f(x\gamma^{-1}) = \chi(\gamma_{11})\varphi_f(x)$ for $\gamma \in \Gamma_0(\mathfrak N)$ (`phiF_rowMul_inv`, from $f\,|_k\,\gamma = \chi(\gamma_{11})f$).
Put $W_f(x) = \varphi_f(x)$ if $x$ is **reduced** (`IsRedVec`: $\mathfrak b(x)$ is the fixed integral ideal of its class) and $W_f(x) = 0$
otherwise (`eisGenWeight`). Each line $Fx$ meets the reduced vectors in exactly one $\mathcal{O}_F^\times$-orbit
(`exists_isRedVec_smul`, `isRedVec_smul_unique`), so the constant term of $E_f$ at $A\infty$,
$\mathrm{c}(W_A) = \sum_{t\in U\backslash F^\times}W_f(t\,x_A)N(t)^{-k}$ (`eisConst_slashWeight`, $x_A = (-A_{10}, A_{00})$), has exactly one
nonzero term, $\varphi_f(t_0x_A)N(t_0)^{-k} = \varphi_f(x_A) = \mathrm{cv}_k(f, A)$ (`eisConst_eisGenWeight`). This is the "weight
supported at a single cusp" family, all cusps at once; no rank computation is needed.

$W_f$ is an admissible weight (`eisWeight_eisGenWeight`): unit equivariant, supported in $\mathcal{O}_F^2$, and **bounded** because a
$\Gamma(\mathfrak N)$-invariant function takes finitely many values on the vectors with a given ideal (`finite_image_of_invariant`) and
there are finitely many classes; it has level $\mathfrak N$ (`hasLevel_eisGenWeight`) and satisfies $(W_f)_\gamma = \chi(\gamma_{11})W_f$ on
$\Gamma_0(\mathfrak N)$ (`slashWeight_eisGenWeight`).

**Weight 2.** the weight-2 series $E_2(\cdot; W)$ is defined only for weights periodic modulo a lattice (`IntWeight`), and $W_f$ is not
periodic (it lives on primitive-type vectors). Writing $W_f$ through periodic weights needs a Möbius inversion over the ideals of
$\mathcal{O}_F$ (with ray classes); this is done in `EisensteinGenus2.lean` ($d \ge 2$); the construction here is for $k \ge 3$.

Sources: Hecke, *Analytische Funktionen und algebraische Zahlen II* (1924) and *Theorie der Eisensteinschen Reihen höherer Stufe*
(1927) [unverified]; Shimura (Duke 1978), §3 [unverified]; Freitag (1990), Ch. I §5 (Eisenstein series and constant terms)
[unverified]; over $\mathbb{Q}$ the analogue is `Siegel.GenusEis.eisQ` (weight 2, Möbius coefficients).
-/
import QuadFormsKB.HilbertModular.CuspFinite
import QuadFormsKB.HilbertModular.CuspValues

open Complex Matrix NumberField UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

/-! ### Row action of $\mathrm{SL}_2(\mathcal{O}_F)$ on cusp ideals and classes -/

/-- The transpose of $g \in \mathrm{SL}_2(\mathcal{O}_F)$. -/
def sl2OT (g : SL(2, 𝓞 F)) : SL(2, 𝓞 F) := ⟨g.valᵀ, by rw [det_transpose]; exact g.2⟩

lemma rowMul_toF_eq (g : SL(2, 𝓞 F)) (y : F × F) :
    rowMul y (toF F g) = (toF F (sl2OT g) 0 0 * y.1 + toF F (sl2OT g) 0 1 * y.2,
      toF F (sl2OT g) 1 0 * y.1 + toF F (sl2OT g) 1 1 * y.2) := by
  have hT : ∀ i j, toF F (sl2OT g) i j = algebraMap (𝓞 F) F (g j i) := fun i j => rfl
  refine Prod.ext ?_ ?_ <;> simp only [rowMul_fst, rowMul_snd, hT, toF_apply] <;> ring

/-- **$\mathrm{SL}_2(\mathcal{O}_F)$ acting on row vectors preserves the cusp ideal.** -/
lemma cuspIdeal_rowMul (g : SL(2, 𝓞 F)) (y : F × F) :
    cuspIdeal (rowMul y (toF F g)).1 (rowMul y (toF F g)).2 = cuspIdeal y.1 y.2 := by
  rw [rowMul_toF_eq]; exact cuspIdeal_SL2O _ _ _

lemma rowMul_ne_zero {y : F × F} (hy : y.1 ≠ 0 ∨ y.2 ≠ 0) (A : SL(2, F)) :
    (rowMul y A).1 ≠ 0 ∨ (rowMul y A).2 ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : rowMul y A = (0, 0) := Prod.ext h.1 h.2
  have := rowMul_rowMul_inv y A
  rw [h0] at this
  simp only [rowMul, zero_mul, add_zero] at this
  rcases hy with hy | hy
  · exact hy (congrArg Prod.fst this).symm
  · exact hy (congrArg Prod.snd this).symm

lemma cuspClass_rowMul (g : SL(2, 𝓞 F)) {y : F × F} (hy : y.1 ≠ 0 ∨ y.2 ≠ 0) :
    cuspClass (rowMul y (toF F g)).1 (rowMul y (toF F g)).2 = cuspClass y.1 y.2 := by
  have h' := rowMul_ne_zero hy (toF F g)
  rw [rowMul_toF_eq] at h' ⊢
  exact cuspClass_SL2O _ hy h'

lemma isRedVec_rowMul_iff (g : SL(2, 𝓞 F)) (y : F × F) :
    IsRedVec (rowMul y (toF F g)) ↔ IsRedVec y := by
  constructor
  · rintro ⟨h1, h2⟩
    have hy : y.1 ≠ 0 ∨ y.2 ≠ 0 := by
      have := rowMul_ne_zero h1 (toF F g)⁻¹
      rwa [rowMul_rowMul_inv] at this
    refine ⟨hy, ?_⟩
    rwa [cuspIdeal_rowMul, cuspClass_rowMul g hy] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨rowMul_ne_zero h1 _, ?_⟩
    rwa [cuspIdeal_rowMul, cuspClass_rowMul g h1]

/-! ### The function $\varphi_f$ on cusp vectors -/

section Phi

variable (f : (InfinitePlace F → ℍ) → ℂ) (k : ℤ)

/-- **The constant term of $f$ at the cusp of the row vector $x$**: $\varphi_f(x) = \mathrm{cv}_k(f, A_x)$ with $A_x$ = `cuspMat x₁ (-x₀)`,
so that $(0, 1)A_x^{-1} = x$. -/
noncomputable def phiF (x : F × F) : ℂ := cuspVal f k (cuspMat x.2 (-x.1))

variable {f k}

lemma neg_ne_zero_or {x : F × F} (hx : x.1 ≠ 0 ∨ x.2 ≠ 0) : x.2 ≠ 0 ∨ -x.1 ≠ 0 :=
  hx.symm.imp id (neg_ne_zero.mpr)

/-- $\mathrm{cv}_k(f, A) = \varphi_f(-A_{10}, A_{00})$: the constant term at $A\infty$ through the vector $x_A = (0,1)A^{-1}$. -/
lemma cuspVal_eq_phiF (hf : HasCuspLimits f k) (A : SL(2, F)) :
    cuspVal f k A = phiF f k (-(A 1 0), A 0 0) := by
  have hA : A 0 0 ≠ 0 ∨ A 1 0 ≠ 0 := by
    by_contra h; push Not at h
    have := sl2_det A; rw [h.1, h.2] at this; simp at this
  have hx : (A 0 0) ≠ 0 ∨ -(-(A 1 0)) ≠ 0 := by simpa using hA
  obtain ⟨c0, c1⟩ := cuspMat_col hx
  refine cuspVal_eq_of_col hf c0.symm ?_
  rw [c1, neg_neg]

/-- $\varphi_f(tx) = N(t)^k\varphi_f(x)$ for $t \ne 0$, $x \ne 0$ ($N(t) = \prod_v\sigma_v(t)$). -/
lemma phiF_smul (hf : HasCuspLimits f k) {x : F × F} (hx : x.1 ≠ 0 ∨ x.2 ≠ 0) {t : F} (ht : t ≠ 0) :
    phiF f k (t * x.1, t * x.2) = (∏ v, (realEmb F v t : ℂ)) ^ k * phiF f k x := by
  have h := cuspVal_mul_diagU hf (cuspMat x.2 (-x.1)) (Units.mk0 t ht)
  obtain ⟨c0, c1⟩ := cuspMat_col (neg_ne_zero_or hx)
  rw [cuspVal_eq_phiF hf (cuspMat x.2 (-x.1) * diagU (Units.mk0 t ht))] at h
  have e1 : -((cuspMat x.2 (-x.1) * diagU (Units.mk0 t ht)) 1 0) = t * x.1 := by
    rw [sl2_mul_apply, c1]; simp [mul_comm]
  have e2 : (cuspMat x.2 (-x.1) * diagU (Units.mk0 t ht)) 0 0 = t * x.2 := by
    rw [sl2_mul_apply, c0]; simp [mul_comm]
  rw [e1, e2] at h
  rw [h]; rfl

/-- **$\Gamma_0(\mathfrak N)$-equivariance of $\varphi_f$**: if $f\,|_k\,\gamma = \chi(\gamma_{11})f$ then $\varphi_f(x\gamma^{-1}) = \chi(\gamma_{11})\varphi_f(x)$. -/
lemma phiF_rowMul_inv (hf : HasCuspLimits f k) {γ : SL(2, F)} {c : ℂ}
    (hγ : f ∣[k] slHom (realEmb F) γ = c • f) {x : F × F} (hx : x.1 ≠ 0 ∨ x.2 ≠ 0) :
    phiF f k (rowMul x γ⁻¹) = c * phiF f k x := by
  have h := cuspVal_mul_left hf hγ (cuspMat x.2 (-x.1))
  obtain ⟨c0, c1⟩ := cuspMat_col (neg_ne_zero_or hx)
  rw [cuspVal_eq_phiF hf (γ * cuspMat x.2 (-x.1))] at h
  have e : (-((γ * cuspMat x.2 (-x.1)) 1 0), (γ * cuspMat x.2 (-x.1)) 0 0) = rowMul x γ⁻¹ := by
    obtain ⟨i0, i1, i2, i3⟩ := sl2_inv_apply γ
    refine Prod.ext ?_ ?_
    · rw [sl2_mul_apply, c0, c1, rowMul_fst, i0, i2]; ring
    · simp only [rowMul_snd, i1, i3]
      rw [sl2_mul_apply, c0, c1]; ring
  rw [e] at h
  rw [h]; rfl

end Phi

/-! ### The weight $W_f$ -/

section Weight

variable (f : (InfinitePlace F → ℍ) → ℂ) (k : ℤ)

open Classical in
/-- **The weight of $E_f$**: $W_f(x) = \varphi_f(x)$ on reduced vectors (`IsRedVec`), $0$ elsewhere.
Parameters: `f` (the form whose constant terms are prescribed), `k` (the weight). -/
@[kb "freitag1990" "Ch. I §5, Eisenstein series with prescribed constant terms [unverified]"]
noncomputable def eisGenWeight (x : F × F) : ℂ := if IsRedVec x then phiF f k x else 0

variable {f k}

lemma eisGenWeight_of_red {x : F × F} (h : IsRedVec x) : eisGenWeight f k x = phiF f k x := by
  classical
  simp only [eisGenWeight, h, ↓reduceIte]

lemma eisGenWeight_of_not_red {x : F × F} (h : ¬ IsRedVec x) : eisGenWeight f k x = 0 := by
  classical
  simp only [eisGenWeight, h, ↓reduceIte]

lemma prod_realEmb_unit (ε : (𝓞 F)ˣ) :
    (∏ v, (realEmb F v ((ε : 𝓞 F) : F) : ℂ)) = ((unitNorm ε : ℝ) : ℂ) := by
  rw [unitNorm, Complex.ofReal_prod]

/-- $W_f$ is unit equivariant of weight $k$. -/
lemma isUnitEquivariant_eisGenWeight (hf : HasCuspLimits f k) : IsUnitEquivariant (eisGenWeight f k) k := by
  intro ε x
  by_cases h : IsRedVec x
  · have h' := (isRedVec_unit_smul_iff x ε).mpr h
    rw [eisGenWeight_of_red h, eisGenWeight_of_red h']
    have hε : ((ε : 𝓞 F) : F) ≠ 0 := (map_ne_zero_iff _ algebraMap_O_injective).mpr ε.ne_zero
    have := phiF_smul hf h.1 hε
    rw [prod_realEmb_unit] at this
    exact this
  · rw [eisGenWeight_of_not_red h, eisGenWeight_of_not_red (fun h' => h ((isRedVec_unit_smul_iff x ε).mp h')),
      mul_zero]

variable {𝔑 : Ideal (𝓞 F)} {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ}

/-- **$(W_f)_\gamma = \chi(\gamma_{11})W_f$ on $\Gamma_0(\mathfrak N)$**, from the $\Gamma_0(\mathfrak N)$-law of $f$. -/
lemma slashWeight_eisGenWeight (hf : HasCuspLimits f k)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[k] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    {γ : SL(2, 𝓞 F)} (hγ : γ ∈ Gamma0R 𝔑) :
    slashWeight (eisGenWeight f k) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • eisGenWeight f k := by
  funext y
  rw [slashWeight, Pi.smul_apply, smul_eq_mul]
  have hinv : (toF F γ)⁻¹ = toF F γ⁻¹ := (map_inv _ _).symm
  by_cases h : IsRedVec y
  · have h' : IsRedVec (rowMul y (toF F γ)⁻¹) := by rw [hinv, isRedVec_rowMul_iff]; exact h
    rw [eisGenWeight_of_red h, eisGenWeight_of_red h', phiF_rowMul_inv hf (hfχ γ hγ) h.1]
  · have h' : ¬ IsRedVec (rowMul y (toF F γ)⁻¹) := by rw [hinv, isRedVec_rowMul_iff]; exact h
    rw [eisGenWeight_of_not_red h, eisGenWeight_of_not_red h', mul_zero]

lemma mk_one_of_gammaFullR {γ : SL(2, 𝓞 F)} (hγ : γ ∈ GammaFullR 𝔑) :
    γ ∈ Gamma0R 𝔑 ∧ Ideal.Quotient.mk 𝔑 (γ 1 1) = 1 :=
  (mem_Gamma1R 𝔑).mp (GammaFullR_le_Gamma1R 𝔑 hγ)

/-- $W_f$ has level $\mathfrak N$: it is invariant under $\Gamma(\mathfrak N)$. -/
lemma hasLevel_eisGenWeight (hf : HasCuspLimits f k)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[k] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f) :
    HasLevel (eisGenWeight f k) 𝔑 := by
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨h0, h1⟩ := mk_one_of_gammaFullR hγ
  rw [slashWeight_eisGenWeight hf hfχ h0, h1, MulChar.map_one, one_smul]

/-- $W_f$ takes finitely many values, hence is bounded. -/
lemma finite_range_eisGenWeight (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f k)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[k] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f) :
    (Set.range (eisGenWeight f k)).Finite := by
  have hinv : ∀ γ ∈ GammaFullR 𝔑, ∀ x, eisGenWeight f k (rowMul x (toF F γ)) = eisGenWeight f k x := by
    intro γ hγ x
    have hγ' : γ⁻¹ ∈ GammaFullR 𝔑 := Subgroup.inv_mem _ hγ
    have := congrFun (hasLevel_eisGenWeight hf hfχ (toF F γ⁻¹) ⟨γ⁻¹, hγ', rfl⟩) x
    rw [slashWeight, map_inv, inv_inv] at this
    exact this
  have hU : (⋃ C : ClassGroup (𝓞 F), eisGenWeight f k ''
      {x | cuspIdeal x.1 x.2 = ((repIdeal C : Ideal (𝓞 F)) : FI)}).Finite :=
    Set.finite_iUnion fun C => finite_image_of_invariant h𝔑 (repIdeal_ne_bot C) _ hinv
  refine ((hU.union (Set.finite_singleton 0))).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases h : IsRedVec x
  · exact Or.inl (Set.mem_iUnion.mpr ⟨cuspClass x.1 x.2, x, h.2, rfl⟩)
  · exact Or.inr (by rw [eisGenWeight_of_not_red h]; rfl)

/-- **$W_f$ is an admissible weight** (`EisWeight`): unit equivariant, supported in $\mathcal{O}_F^2$, bounded. -/
theorem eisWeight_eisGenWeight (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f k)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[k] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f) :
    EisWeight (eisGenWeight f k) k := by
  refine ⟨isUnitEquivariant_eisGenWeight hf, ⟨1, fun x hx => ?_⟩, ?_⟩
  · have h : IsRedVec x := by
      by_contra h; exact hx (eisGenWeight_of_not_red h)
    have hle : ((repIdeal (cuspClass x.1 x.2) : Ideal (𝓞 F)) : FI) ≤ 1 :=
      FractionalIdeal.coeIdeal_le_one
    have h1 : x.1 ∈ cuspIdeal x.1 x.2 := mem_cuspIdeal_fst _ _
    have h2 : x.2 ∈ cuspIdeal x.1 x.2 := mem_cuspIdeal_snd _ _
    rw [h.2] at h1 h2
    exact ⟨hle h1, hle h2⟩
  · obtain ⟨B, hB⟩ := ((finite_range_eisGenWeight h𝔑 hf hfχ).image (‖·‖)).bddAbove
    exact ⟨B, fun x => hB ⟨_, ⟨x, rfl⟩, rfl⟩⟩

end Weight

/-! ### The constant terms of $E_f$ -/

section ConstTerm

variable {f : (InfinitePlace F → ℍ) → ℂ} {k : ℤ}

lemma prod_realEmb_ne_zero {t : F} (ht : t ≠ 0) : (∏ v, (realEmb F v t : ℂ)) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun v _ => by
    rw [Ne, Complex.ofReal_eq_zero]; exact (map_ne_zero_iff _ (realEmb_injective F v)).mpr ht

lemma col_ne_zero (A : SL(2, F)) : (-(A 1 0)) ≠ 0 ∨ A 0 0 ≠ 0 := by
  by_contra h; push Not at h
  have := sl2_det A
  rw [neg_eq_zero.mp h.1, h.2] at this; simp at this

/-- **The constant term of $E_k(\cdot; W_f)$ at every cusp is that of $f$**: $\mathrm{c}((W_f)_A) = \mathrm{cv}_k(f, A)$ for every
$A \in \mathrm{SL}_2(F)$. *Proof:* in $\mathrm{c}((W_f)_A) = \sum_{t\in U\backslash F}W_f(t\,x_A)N(t)^{-k}$ only the orbit of the $t_0$ with $t_0x_A$ reduced
contributes (`isRedVec_smul_unique`), and $W_f(t_0x_A)N(t_0)^{-k} = \varphi_f(x_A) = \mathrm{cv}_k(f, A)$. -/
@[kb "freitag1990" "Ch. I §5, constant terms of Eisenstein series at the cusps [unverified]"]
theorem eisConst_eisGenWeight (hf : HasCuspLimits f k) (A : SL(2, F)) :
    eisConst (slashWeight (eisGenWeight f k) A) k = cuspVal f k A := by
  rw [eisConst_slashWeight (isUnitEquivariant_eisGenWeight hf) A]
  set x : F × F := (-(A 1 0), A 0 0) with hxdef
  have hx : x.1 ≠ 0 ∨ x.2 ≠ 0 := col_ne_zero A
  have hterm : ∀ t : F, (-(t * A 1 0), t * A 0 0) = (t * x.1, t * x.2) := fun t => by
    simp [hxdef, mul_neg]
  obtain ⟨t₀, ht₀, hred⟩ := exists_isRedVec_smul hx
  rw [tsum_eq_single (Quotient.mk _ t₀ : UOrbitF F)]
  · set s := (Quotient.mk _ t₀ : UOrbitF F).out
    obtain ⟨ε, hε⟩ : ∃ ε : (𝓞 F)ˣ, ε • t₀ = s :=
      MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact (Quotient.out_eq _)))
    have hεF : ((ε : 𝓞 F) : F) * t₀ = s := hε
    have hs : s ≠ 0 := by
      rw [← hεF]; exact mul_ne_zero ((map_ne_zero_iff _ algebraMap_O_injective).mpr ε.ne_zero) ht₀
    have hreds : IsRedVec (s * x.1, s * x.2) := by
      have := (isRedVec_unit_smul_iff (t₀ * x.1, t₀ * x.2) ε).mpr hred
      have e : ε • (t₀ * x.1, t₀ * x.2) = (s * x.1, s * x.2) := by
        rw [← hεF]; ext <;> simp [Units.smul_def, Algebra.smul_def, mul_assoc]
      rwa [e] at this
    rw [hterm, eisGenWeight_of_red hreds, phiF_smul hf hx hs, cuspVal_eq_phiF hf A, mul_comm,
      ← mul_assoc, ← zpow_add₀ (prod_realEmb_ne_zero hs), neg_add_cancel, zpow_zero, one_mul]
  · intro o ho
    rw [hterm]
    by_cases h : IsRedVec (o.out * x.1, o.out * x.2)
    · exfalso
      have hs : o.out ≠ 0 := by
        rintro h0; rw [h0] at h; simp at h; exact h.1.elim (fun h => h rfl) (fun h => h rfl)
      obtain ⟨ε, hε⟩ := isRedVec_smul_unique hx ht₀ hs hred h
      apply ho
      rw [← Quotient.out_eq o]
      refine Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨ε, ?_⟩))
      exact hε
    · rw [eisGenWeight_of_not_red h, zero_mul]

end ConstTerm

/-! ### $E_f$ and the cuspidal part of $f$ -/

section Main

variable {f : (InfinitePlace F → ℍ) → ℂ} {k : ℤ} {𝔑 : Ideal (𝓞 F)} {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ}

/-- **The Eisenstein series with the constant terms of $f$**: $E_f = E_k(\cdot; W_f)$ (`eisSeries`). -/
@[kb "freitag1990" "Ch. I §5, the Eisenstein part of a modular form [unverified]"]
noncomputable def eisGen (f : (InfinitePlace F → ℍ) → ℂ) (k : ℤ) : (InfinitePlace F → ℍ) → ℂ :=
  eisSeries (eisGenWeight f k) k

/-- **$E_f$ has the constant term of $f$ at every cusp** ($k \ge 3$): $(E_f\,|_k\,A)(z) \to \mathrm{cv}_k(f, A)$ for every
$A \in \mathrm{SL}_2(F)$. -/
@[kb "freitag1990" "Ch. I §5 [unverified]"]
theorem tendsto_eisGen_slash (hk : 3 ≤ k) (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f k)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[k] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (A : SL(2, F)) :
    Tendsto (eisGen f k ∣[k] slHom (realEmb F) A) atImInftyPi (𝓝 (cuspVal f k A)) := by
  have := tendsto_eisSeries_slash (eisWeight_eisGenWeight h𝔑 hf hfχ) hk h𝔑 (hasLevel_eisGenWeight hf hfχ) A
  rwa [eisConst_eisGenWeight hf A] at this

/-- **$E_f \in M_k(\Gamma_0(\mathfrak N), \chi)$** for $k \ge 3$, $\mathfrak N \ne 0$, whenever $f$ has constant terms at all cusps and the
$\Gamma_0(\mathfrak N)$-law with character $\chi$ (any degree $d \ge 1$). -/
@[kb "shimura1978" "§3, Eisenstein series in M_k(Γ₀(𝔑), χ) [unverified]"]
theorem eisGen_mem_modularFormChar (hk : 3 ≤ k) (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f k)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[k] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f) :
    eisGen f k ∈ modularFormChar 𝔑 χ k := by
  have hW := eisWeight_eisGenWeight h𝔑 hf hfχ
  have hlaw : ∀ γ ∈ Gamma0R 𝔑, eisGen f k ∣[k] slHom (realEmb F) (toF F γ) =
      χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • eisGen f k := fun γ hγ =>
    eisSeries_slash_of_weight hW.unit (toF F γ) (slashWeight_eisGenWeight hf hfχ hγ)
  refine ⟨⟨?_, isHolomorphic_eisSeries hW hk, fun A => ?_⟩, hlaw⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    have h1 := (mem_Gamma1R 𝔑).mp hγ
    rw [hlaw γ h1.1, h1.2, MulChar.map_one, one_smul]
  · exact (tendsto_eisGen_slash hk h𝔑 hf hfχ A).isBigO_one ℝ

/-- **Every $f \in M_k(\Gamma_0(\mathfrak N), \chi)$ with constant terms at all cusps is Eisenstein plus cuspidal** ($k \ge 3$):
$f - E_f \in S_k(\Gamma_0(\mathfrak N), \chi)$. For $d \ge 2$ the hypothesis `HasCuspLimits` is a consequence of Koecher's principle
(not used here). -/
@[kb "shimura1978" "§3, M_k = E_k ⊕ S_k (Eisenstein part with the same constant terms) [unverified]"]
theorem sub_eisGen_mem_cuspFormChar (hk : 3 ≤ k) (h𝔑 : 𝔑 ≠ ⊥) (hfM : f ∈ modularFormChar 𝔑 χ k)
    (hf : HasCuspLimits f k) :
    f - eisGen f k ∈ cuspFormChar 𝔑 χ k := by
  have hE := eisGen_mem_modularFormChar hk h𝔑 hf hfM.2
  have hsub := (modularFormChar 𝔑 χ k).sub_mem hfM hE
  exact ⟨⟨hsub.1.1, hsub.1.2.1, fun A =>
    isZeroAtImInftyPi_sub (tendsto_cuspVal hf A) (tendsto_eisGen_slash hk h𝔑 hf hfM.2 A)⟩, hsub⟩

end Main

end QuadFormsKB.HilbertModular
