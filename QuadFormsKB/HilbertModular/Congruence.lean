/-
# Hilbert modular forms II: $\mathrm{SL}_2(F)$, $\mathrm{GL}_2^+(F)$ and congruence subgroups

**Embedding into $\prod_v\mathrm{GL}_2^+(\mathbb{R})$.** For a field $K$ with a family of real embeddings
$\varphi = (\varphi_v)_{v\in\iota}$ (`φ : ι → K →+* ℝ`):

* `slHom φ : SL(2, K) →* (ι → GL(2, ℝ)⁺)`, $\gamma \mapsto (\varphi_v(\gamma))_v$;
* `glTotPos φ` $= \mathrm{GL}_2^+(K) = \{g \in \mathrm{GL}_2(K) : \varphi_v(\det g) > 0 \text{ for all } v\}$ (totally positive
  determinant), and `glTotPosHom φ : glTotPos φ →* (ι → GL(2, ℝ)⁺)`; `slHom_eq_glTotPosHom` shows `slHom` is its
  restriction to $\mathrm{SL}_2(K)$.

For a totally real number field $F$ (`NumberField.IsTotallyReal F`), $\iota$ is the set of infinite places
(`InfinitePlace F`, all real, $|\iota| = d = [F:\mathbb{Q}]$) and $\varphi_v$ = `realEmb F v`, the real embedding of $v$.

**Congruence subgroups (convention).** Let $\mathcal{O} = \mathcal{O}_F$, $\mathfrak{d}$ the different, $\mathfrak{N}$ an integral ideal
and $\mathfrak{a}$ a fractional ideal. We follow **Shimura** (Duke 1978, §1–2 [unverified]):

* `gammaXY x y` $= \Gamma[\mathfrak x, \mathfrak y] = \Big\{\begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(F) : a, d \in \mathcal{O},\ b \in \mathfrak x,\
  c \in \mathfrak y\Big\}$ for $\mathcal{O}$-submodules $\mathfrak x, \mathfrak y$ of $F$ with $\mathfrak x\mathfrak y \subseteq \mathcal{O}$ (needed for closure);
* `gammaShimura 𝔞 𝔑` $= \Gamma(\mathfrak a, \mathfrak N) = \Gamma[(\mathfrak a\mathfrak d)^{-1},\ \mathfrak N\mathfrak a\mathfrak d]$, i.e.
  $b \in \mathfrak a^{-1}\mathfrak d^{-1}$, $c \in \mathfrak N\mathfrak a\mathfrak d$;
* `Gamma0 𝔑` $= \Gamma_0(\mathfrak N) = \Gamma[\mathcal{O}, \mathfrak N]$: the image of
  $\{\gamma \in \mathrm{SL}_2(\mathcal{O}) : c \equiv 0 \bmod \mathfrak N\}$ (`Gamma0R`); `Gamma1 𝔑` adds $d \equiv 1 \bmod \mathfrak N$;
  `GammaFull 𝔑` $= \Gamma(\mathfrak N)$, the kernel of reduction mod $\mathfrak N$.

`gammaShimura_invDifferent`: $\Gamma(\mathfrak d^{-1}, \mathfrak N) = \Gamma_0(\mathfrak N)$, and `gammaXY_one_eq_Gamma0`:
$\Gamma[\mathcal{O}, \mathfrak N] = \Gamma_0(\mathfrak N)$.

*Why this convention.* The translations in $\Gamma(\mathfrak a, \mathfrak N)$ are $z \mapsto z + b$, $b \in (\mathfrak a\mathfrak d)^{-1}$, whose trace dual
is $\mathfrak a$ itself ($\mathfrak b^\vee = \mathfrak b^{-1}\mathfrak d^{-1}$); so $q$-expansions on $\Gamma(\mathfrak a, \mathfrak N)$ run over $\nu \in \mathfrak a$ and the
coefficients of the $h_F^+$-tuple of forms on $\Gamma(\mathfrak t_\lambda, \mathfrak N)$ (narrow class representatives $\mathfrak t_\lambda$)
assemble into a function on integral ideals $\nu\mathfrak t_\lambda^{-1}$ — the form in which theta series of
$\mathcal{O}_F$-lattices (sums over $\mathfrak d^{-1}$-dual lattices) and Hecke's ideal-theoretic Eisenstein series are
written (Shimura 1978; Garrett 1990, Ch. 2 [unverified]). The other common normalization
$\mathrm{SL}_2(\mathcal{O} \oplus \mathfrak a) = \Gamma[\mathfrak a^{-1}, \mathfrak a]$ (van der Geer; Freitag) is `gammaXY` with other
arguments; the two are conjugate by $\mathrm{diag}(1, \delta)$-type elements of $\mathrm{GL}_2^+(F)$ only when the ideals
involved are principal with totally positive generators, so we fix Shimura's.
-/
import QuadFormsKB.HilbertModular.Basic

open Matrix NumberField
open scoped MatrixGroups nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

/-! ### Real embeddings -/

section Embed

variable {ι : Type*} {K : Type*} [Field K] (φ : ι → K →+* ℝ)

/-- **$\mathrm{SL}_2(K) \to \prod_v\mathrm{GL}_2^+(\mathbb{R})$**, $\gamma \mapsto (\varphi_v(\gamma))_{v\in\iota}$ (entrywise; the
determinant is $1$). -/
noncomputable def slHom : SL(2, K) →* (ι → GL(2, ℝ)⁺) :=
  MonoidHom.pi fun v => SpecialLinearGroup.toGLPos.comp (SpecialLinearGroup.map (φ v))

@[simp] lemma slHom_apply_coe (γ : SL(2, K)) (v : ι) (i j : Fin 2) :
    ((slHom φ γ v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) i j = φ v (γ i j) := rfl

lemma slHom_det (γ : SL(2, K)) (v : ι) :
    ((slHom φ γ v : GL (Fin 2) ℝ).det.val : ℝ) = 1 := by
  rw [GeneralLinearGroup.val_det_apply]
  exact (SpecialLinearGroup.map (φ v) γ).2

/-- **$\mathrm{GL}_2^+(K)$**: invertible $2\times 2$ matrices over $K$ whose determinant is totally positive,
$\varphi_v(\det g) > 0$ for every $v \in \iota$. -/
@[kb "shimura1978" "§1 (GL₂⁺(F), totally positive determinant) [unverified]"]
def glTotPos : Subgroup (GL (Fin 2) K) where
  carrier := {g | ∀ v, 0 < φ v (g.det : K)}
  mul_mem' {a b} ha hb v := by
    simp only [Set.mem_setOf_eq, map_mul, Units.val_mul] at *
    exact mul_pos (ha v) (hb v)
  one_mem' v := by simp
  inv_mem' {a} ha v := by
    simp only [Set.mem_setOf_eq, map_inv, Units.val_inv_eq_inv_val, map_inv₀] at *
    exact inv_pos.mpr (ha v)

/-- **$\mathrm{GL}_2^+(K) \to \prod_v\mathrm{GL}_2^+(\mathbb{R})$**, $g \mapsto (\varphi_v(g))_v$. -/
noncomputable def glTotPosHom : glTotPos φ →* (ι → GL(2, ℝ)⁺) :=
  MonoidHom.pi fun v =>
    ((GeneralLinearGroup.map (φ v)).comp (glTotPos φ).subtype).codRestrict (GLPos (Fin 2) ℝ)
      fun g => by
        rw [mem_glpos, MonoidHom.comp_apply, GeneralLinearGroup.map_det]
        exact g.2 v

lemma toGL_mem_glTotPos (γ : SL(2, K)) : (γ : GL (Fin 2) K) ∈ glTotPos φ := by
  intro v
  have : ((γ : GL (Fin 2) K).det : K) = 1 := by
    rw [GeneralLinearGroup.val_det_apply]; exact γ.2
  rw [this, map_one]; exact one_pos

/-- `slHom` is the restriction of `glTotPosHom` to $\mathrm{SL}_2(K)$. -/
lemma slHom_eq_glTotPosHom (γ : SL(2, K)) :
    slHom φ γ = glTotPosHom φ ⟨γ, toGL_mem_glTotPos φ γ⟩ := by
  funext v
  ext i j
  rfl

end Embed

/-! ### Congruence subgroups over a Dedekind domain -/

section Ring

variable {R : Type*} [CommRing R] (𝔑 : Ideal R)

lemma sl2_mul_apply (a b : SL(2, R)) (i j : Fin 2) :
    (a * b) i j = a i 0 * b 0 j + a i 1 * b 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma sl2_inv_00 (a : SL(2, R)) : a⁻¹ 0 0 = a 1 1 := by
  simp [SpecialLinearGroup.coe_inv, adjugate_fin_two]
@[simp] lemma sl2_inv_01 (a : SL(2, R)) : a⁻¹ 0 1 = -a 0 1 := by
  simp [SpecialLinearGroup.coe_inv, adjugate_fin_two]
@[simp] lemma sl2_inv_10 (a : SL(2, R)) : a⁻¹ 1 0 = -a 1 0 := by
  simp [SpecialLinearGroup.coe_inv, adjugate_fin_two]
@[simp] lemma sl2_inv_11 (a : SL(2, R)) : a⁻¹ 1 1 = a 0 0 := by
  simp [SpecialLinearGroup.coe_inv, adjugate_fin_two]

/-- **$\Gamma_0(\mathfrak N)$ inside $\mathrm{SL}_2(R)$**: $\gamma_{10} \in \mathfrak N$ (0-based entries,
$\gamma = \begin{pmatrix}\gamma_{00}&\gamma_{01}\\\gamma_{10}&\gamma_{11}\end{pmatrix}$). -/
def Gamma0R : Subgroup SL(2, R) where
  carrier := {γ | γ 1 0 ∈ 𝔑}
  mul_mem' {a b} ha hb := by
    change (a * b) 1 0 ∈ 𝔑
    rw [sl2_mul_apply]
    exact 𝔑.add_mem (𝔑.mul_mem_right _ ha) (𝔑.mul_mem_left _ hb)
  one_mem' := by simp
  inv_mem' {a} ha := by
    change a⁻¹ 1 0 ∈ 𝔑
    rw [sl2_inv_10]
    exact 𝔑.neg_mem ha

lemma mem_Gamma0R {γ : SL(2, R)} : γ ∈ Gamma0R 𝔑 ↔ γ 1 0 ∈ 𝔑 := Iff.rfl

/-- **The $d$-entry modulo $\mathfrak N$** on $\Gamma_0(\mathfrak N)$: $\gamma \mapsto \gamma_{11} \bmod \mathfrak N$, a monoid
homomorphism to $R/\mathfrak N$ (because $\gamma_{10} \in \mathfrak N$). This is the argument of the nebentypus character. -/
def gamma0D : Gamma0R 𝔑 →* R ⧸ 𝔑 where
  toFun γ := Ideal.Quotient.mk 𝔑 ((γ : SL(2, R)) 1 1)
  map_one' := by simp
  map_mul' a b := by
    have ha : Ideal.Quotient.mk 𝔑 ((a : SL(2, R)) 1 0) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr a.2
    simp only [Subgroup.coe_mul, sl2_mul_apply, map_add, map_mul, ha, zero_mul, zero_add]

/-- **$\Gamma_1(\mathfrak N)$ inside $\mathrm{SL}_2(R)$**: $\gamma_{10} \in \mathfrak N$ and $\gamma_{11} \equiv 1 \bmod \mathfrak N$ (the kernel of
`gamma0D` on $\Gamma_0(\mathfrak N)$; `mem_Gamma1R`). -/
def Gamma1R : Subgroup SL(2, R) :=
  ((gamma0D 𝔑).toHomUnits.ker).map (Gamma0R 𝔑).subtype

lemma mem_Gamma1R {γ : SL(2, R)} :
    γ ∈ Gamma1R 𝔑 ↔ γ 1 0 ∈ 𝔑 ∧ Ideal.Quotient.mk 𝔑 (γ 1 1) = 1 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g.2, ?_⟩
    have := congrArg Units.val (MonoidHom.mem_ker.mp hg)
    simpa [gamma0D] using this
  · rintro ⟨h0, h1⟩
    refine Subgroup.mem_map.mpr ⟨⟨γ, h0⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    ext
    simpa [gamma0D] using h1

lemma Gamma1R_le_Gamma0R : Gamma1R 𝔑 ≤ Gamma0R 𝔑 := fun _ h => ((mem_Gamma1R 𝔑).mp h).1

/-- **The principal congruence subgroup $\Gamma(\mathfrak N)$ inside $\mathrm{SL}_2(R)$**: $\gamma \equiv 1 \bmod \mathfrak N$, the kernel
of reduction $\mathrm{SL}_2(R) \to \mathrm{SL}_2(R/\mathfrak N)$. -/
def GammaFullR : Subgroup SL(2, R) := (SpecialLinearGroup.map (Ideal.Quotient.mk 𝔑)).ker

lemma GammaFullR_le_Gamma1R : GammaFullR 𝔑 ≤ Gamma1R 𝔑 := by
  intro γ hγ
  have h : ∀ i j, (SpecialLinearGroup.map (Ideal.Quotient.mk 𝔑) γ) i j = (1 : SL(2, R ⧸ 𝔑)) i j :=
    fun i j => by rw [MonoidHom.mem_ker.mp hγ]
  refine (mem_Gamma1R 𝔑).mpr ⟨?_, ?_⟩
  · have := h 1 0
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, map_apply,
      SpecialLinearGroup.coe_one, one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  · have := h 1 1
    simpa using this

end Ring

/-! ### Over a totally real field -/

section Field

variable (F : Type*) [Field F] [NumberField F]

/-- **The real embedding of a real place** $v$ of $F$, $F \to \mathbb{R}$ (Mathlib's `embedding_of_isReal`); for totally real
$F$ every place is real. -/
noncomputable def realEmb [IsTotallyReal F] (v : InfinitePlace F) : F →+* ℝ :=
  InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)

lemma realEmb_injective [IsTotallyReal F] (v : InfinitePlace F) :
    Function.Injective (realEmb F v) := (realEmb F v).injective

/-- $\mathrm{SL}_2(\mathcal{O}_F) \to \mathrm{SL}_2(F)$ (entrywise inclusion; injective, `toF_injective`). -/
noncomputable def toF : SL(2, 𝓞 F) →* SL(2, F) := SpecialLinearGroup.map (algebraMap (𝓞 F) F)

lemma toF_injective : Function.Injective (toF F) := by
  intro a b h
  ext i j
  have := congrArg (fun g : SL(2, F) => g i j) h
  simpa [toF] using this

variable {F}

/-- **$\mathrm{SL}_2(\mathcal{O}_F)$** as a subgroup of $\mathrm{SL}_2(F)$. -/
noncomputable def SL2O : Subgroup SL(2, F) := (toF F).range

/-- **$\Gamma_0(\mathfrak N) \subseteq \mathrm{SL}_2(F)$**: matrices in $\mathrm{SL}_2(\mathcal{O}_F)$ with $c \in \mathfrak N$. -/
@[kb "shimura1978" "§2, Γ₀(𝔑) [unverified]"]
noncomputable def Gamma0 (𝔑 : Ideal (𝓞 F)) : Subgroup SL(2, F) := (Gamma0R 𝔑).map (toF F)

/-- **$\Gamma_1(\mathfrak N) \subseteq \mathrm{SL}_2(F)$**: matrices in $\mathrm{SL}_2(\mathcal{O}_F)$ with $c \in \mathfrak N$, $d \equiv 1 \bmod \mathfrak N$. -/
@[kb "shimura1978" "§2, Γ₁(𝔑) [unverified]"]
noncomputable def Gamma1 (𝔑 : Ideal (𝓞 F)) : Subgroup SL(2, F) := (Gamma1R 𝔑).map (toF F)

/-- **$\Gamma(\mathfrak N) \subseteq \mathrm{SL}_2(F)$**: matrices in $\mathrm{SL}_2(\mathcal{O}_F)$ congruent to $1$ modulo $\mathfrak N$. -/
noncomputable def GammaFull (𝔑 : Ideal (𝓞 F)) : Subgroup SL(2, F) := (GammaFullR 𝔑).map (toF F)

lemma Gamma1_le_Gamma0 (𝔑 : Ideal (𝓞 F)) : Gamma1 𝔑 ≤ Gamma0 𝔑 :=
  Subgroup.map_mono (Gamma1R_le_Gamma0R 𝔑)

lemma GammaFull_le_Gamma1 (𝔑 : Ideal (𝓞 F)) : GammaFull 𝔑 ≤ Gamma1 𝔑 :=
  Subgroup.map_mono (GammaFullR_le_Gamma1R 𝔑)

lemma Gamma0_le_SL2O (𝔑 : Ideal (𝓞 F)) : Gamma0 𝔑 ≤ SL2O := by
  rintro _ ⟨g, -, rfl⟩; exact ⟨g, rfl⟩

lemma Gamma0_top : Gamma0 (⊤ : Ideal (𝓞 F)) = SL2O := by
  apply le_antisymm (Gamma0_le_SL2O _)
  rintro _ ⟨g, rfl⟩
  exact ⟨g, (mem_Gamma0R _).mpr Submodule.mem_top, rfl⟩

/-! ### Shimura's groups $\Gamma[\mathfrak x, \mathfrak y]$ and $\Gamma(\mathfrak a, \mathfrak N)$ -/

/-- **Shimura's $\Gamma[\mathfrak x, \mathfrak y]$** for $\mathcal{O}_F$-submodules $\mathfrak x, \mathfrak y \subseteq F$ with $\mathfrak x\mathfrak y \subseteq \mathcal{O}_F$:
$\Big\{\begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(F) : a, d \in \mathcal{O}_F,\ b \in \mathfrak x,\ c \in \mathfrak y\Big\}$ (0-based:
$a = \gamma_{00}$, $b = \gamma_{01}$, $c = \gamma_{10}$, $d = \gamma_{11}$; $\mathcal{O}_F$ is the submodule `1`).

Parameters: `x`, `y` (the submodules), `hxy` ($\mathfrak x\mathfrak y \le \mathcal{O}_F$, which makes the set closed under
products). -/
@[kb "shimura1978" "§1, Γ[x, y] [unverified]"]
def gammaXY (x y : Submodule (𝓞 F) F) (hxy : x * y ≤ 1) : Subgroup SL(2, F) where
  carrier := {γ | γ 0 0 ∈ (1 : Submodule (𝓞 F) F) ∧ γ 0 1 ∈ x ∧ γ 1 0 ∈ y ∧
    γ 1 1 ∈ (1 : Submodule (𝓞 F) F)}
  mul_mem' {a b} ha hb := by
    obtain ⟨ha0, ha1, ha2, ha3⟩ := ha
    obtain ⟨hb0, hb1, hb2, hb3⟩ := hb
    have hyx : y * x ≤ 1 := by rwa [mul_comm]
    change (a * b) 0 0 ∈ (1 : Submodule (𝓞 F) F) ∧ (a * b) 0 1 ∈ x ∧ (a * b) 1 0 ∈ y ∧
      (a * b) 1 1 ∈ (1 : Submodule (𝓞 F) F)
    simp only [sl2_mul_apply]
    refine ⟨Submodule.add_mem _ ?_ ?_, Submodule.add_mem _ ?_ ?_, Submodule.add_mem _ ?_ ?_,
      Submodule.add_mem _ ?_ ?_⟩
    · simpa using Submodule.mul_mem_mul ha0 hb0
    · exact hxy (Submodule.mul_mem_mul ha1 hb2)
    · simpa using Submodule.mul_mem_mul ha0 hb1
    · simpa using Submodule.mul_mem_mul ha1 hb3
    · simpa using Submodule.mul_mem_mul ha2 hb0
    · simpa using Submodule.mul_mem_mul ha3 hb2
    · exact hyx (Submodule.mul_mem_mul ha2 hb1)
    · simpa using Submodule.mul_mem_mul ha3 hb3
  one_mem' := by
    change (1 : SL(2, F)) 0 0 ∈ (1 : Submodule (𝓞 F) F) ∧ (1 : SL(2, F)) 0 1 ∈ x ∧
      (1 : SL(2, F)) 1 0 ∈ y ∧ (1 : SL(2, F)) 1 1 ∈ (1 : Submodule (𝓞 F) F)
    have h1 : (1 : F) ∈ (1 : Submodule (𝓞 F) F) := Submodule.one_le.mp le_rfl
    simpa using ⟨h1, x.zero_mem, y.zero_mem, h1⟩
  inv_mem' {a} ha := by
    obtain ⟨ha0, ha1, ha2, ha3⟩ := ha
    change a⁻¹ 0 0 ∈ (1 : Submodule (𝓞 F) F) ∧ a⁻¹ 0 1 ∈ x ∧ a⁻¹ 1 0 ∈ y ∧
      a⁻¹ 1 1 ∈ (1 : Submodule (𝓞 F) F)
    simp only [sl2_inv_00, sl2_inv_01, sl2_inv_10, sl2_inv_11]
    exact ⟨by simpa using ha3, by simpa using x.neg_mem ha1, by simpa using y.neg_mem ha2,
      by simpa using ha0⟩

/-- The fractional ideals of $\mathcal{O}_F$. -/
local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

variable (F) in
/-- **The inverse different** $\mathfrak d^{-1} = \mathcal{O}_F^\vee = \{x \in F : \operatorname{Tr}(x\mathcal{O}_F) \subseteq \mathbb{Z}\}$ (Mathlib's trace dual
`FractionalIdeal.dual ℤ ℚ 1`). -/
noncomputable def invDifferent : FI := FractionalIdeal.dual ℤ ℚ 1

lemma invDifferent_ne_zero : invDifferent F ≠ 0 :=
  FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero

lemma mul_le_one_aux (u : FI) (𝔑 : Ideal (𝓞 F)) :
    ((u⁻¹ : FI) : Submodule (𝓞 F) F) * ((𝔑 * u : FI) : Submodule (𝓞 F) F) ≤ 1 := by
  rw [← FractionalIdeal.coe_mul, ← FractionalIdeal.coe_one, FractionalIdeal.coe_le_coe]
  by_cases hu : u = 0
  · simp [hu]
  · rw [mul_comm (𝔑 : FI) u, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
    exact FractionalIdeal.coeIdeal_le_one

/-- **Shimura's $\Gamma(\mathfrak a, \mathfrak N)$** $= \Gamma[(\mathfrak a\mathfrak d)^{-1}, \mathfrak N\mathfrak a\mathfrak d]$: matrices
$\begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(F)$ with $a, d \in \mathcal{O}_F$, $b \in \mathfrak a^{-1}\mathfrak d^{-1}$, $c \in \mathfrak N\mathfrak a\mathfrak d$
($\mathfrak d = (\mathfrak d^{-1})^{-1}$ the different).

Parameters: `𝔞` (a fractional ideal of $F$), `𝔑` (an integral ideal, the level). -/
@[kb "shimura1978" "§2, Γ(𝔞, 𝔑) = Γ[𝔞⁻¹𝔡⁻¹, 𝔑𝔞𝔡] [unverified]"]
noncomputable def gammaShimura (𝔞 : FI) (𝔑 : Ideal (𝓞 F)) : Subgroup SL(2, F) :=
  gammaXY ((𝔞 * (invDifferent F)⁻¹)⁻¹ : FI) ((𝔑 : FI) * (𝔞 * (invDifferent F)⁻¹) : FI)
    (mul_le_one_aux _ 𝔑)

/-- $\Gamma[\mathcal{O}_F, \mathfrak N] = \Gamma_0(\mathfrak N)$. -/
lemma gammaXY_one_eq_Gamma0 (𝔑 : Ideal (𝓞 F)) (h : (1 : Submodule (𝓞 F) F) * ((𝔑 : FI) : Submodule (𝓞 F) F) ≤ 1) :
    gammaXY 1 ((𝔑 : FI) : Submodule (𝓞 F) F) h = Gamma0 𝔑 := by
  ext γ
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp h0
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp h1
    obtain ⟨c, hc𝔑, hc⟩ := (FractionalIdeal.mem_coeIdeal _).mp h2
    obtain ⟨d, hd⟩ := Submodule.mem_one.mp h3
    have hdet : a * d - b * c = 1 := by
      apply IsFractionRing.injective (𝓞 F) F
      have := γ.2
      rw [det_fin_two] at this
      simp only [map_sub, map_mul, map_one, ha, hb, hc, hd]
      exact this
    refine ⟨⟨!![a, b; c, d], by rw [det_fin_two_of]; exact hdet⟩, hc𝔑, ?_⟩
    ext i j
    change algebraMap (𝓞 F) F (!![a, b; c, d] i j) = γ i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
  · rintro ⟨g, hg, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Submodule.mem_one.mpr ⟨g 0 0, by simp [toF]⟩
    · exact Submodule.mem_one.mpr ⟨g 0 1, by simp [toF]⟩
    · exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨g 1 0, hg, by simp [toF]⟩
    · exact Submodule.mem_one.mpr ⟨g 1 1, by simp [toF]⟩

/-- **$\Gamma(\mathfrak d^{-1}, \mathfrak N) = \Gamma_0(\mathfrak N)$**: with $\mathfrak a = \mathfrak d^{-1}$, Shimura's group is $\Gamma_0(\mathfrak N)$
($b \in \mathcal{O}_F$, $c \in \mathfrak N$). -/
lemma gammaShimura_invDifferent (𝔑 : Ideal (𝓞 F)) :
    gammaShimura (invDifferent F) 𝔑 = Gamma0 𝔑 := by
  have h1 : invDifferent F * (invDifferent F)⁻¹ = 1 := mul_inv_cancel₀ invDifferent_ne_zero
  rw [← gammaXY_one_eq_Gamma0 𝔑 (by rw [one_mul]; exact
    (FractionalIdeal.coe_le_coe.mpr FractionalIdeal.coeIdeal_le_one).trans_eq FractionalIdeal.coe_one)]
  unfold gammaShimura
  congr 1
  · rw [h1, inv_one, FractionalIdeal.coe_one]
  · rw [h1, mul_one]

end Field

end QuadFormsKB.HilbertModular
