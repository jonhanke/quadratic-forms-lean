import QuadFormsKB.Tamagawa.Measure.Weil.SOAdeleAction
import QuadFormsKB.Tamagawa.Measure.Weil.ReflectionSection
import QuadFormsKB.Siegel.NeighborGenus
import QuadFormsKB.Tamagawa.SphericalZeta

/-!
# Orbits of $SO(V)(F)\times F^\times$ on $V(F)\setminus 0$

$F$ any number field, $Q_0$ a nondegenerate form over $\mathcal O_F$ in $n\ge2$ variables, $Q = Q_0\otimes F$ on $V = F^n$.
This is the global (rational) algebra of Weil's unfolding (Weil 1982, §4.5, p. 109, Step 1):

* **Shells** (`tsum_ne_zero_eq_tsum_sqClasses`): for $G\ge0$ on $F^n$,
  $$\sum_{\xi:\ Q(\xi)\ne0}G(\xi) = \frac12\sum_{c\in F^\times/F^{\times2}}\ \sum_{\lambda\in F^\times}\ \sum_{\eta:\ Q(\eta)=\rho_c}G(\lambda\eta),$$
  $\rho_c$ = `Quotient.out c` (the representatives used in `sphericalZetaNF`). For anisotropic $Q$ the left side is
  the sum over $V(F)\setminus0$. (Generic port of `tsum_shell_eq`, which is stated over a totally real field.)
* **Witt's theorem for $SO$** (`exists_smul_eq_ratSphere`): $SO(V)(F)$ is transitive on each rational sphere
  $T(\rho)(F) = \{Q = \rho\}$, $\rho\ne0$ (from the two-reflection section `exists_SO_mulVec_eq`).
* The rational spheres as `GammaSOAdele Q₀`-sets (`RatSphere`, `instMulActionRatSphere`), with the diagonal embedding
  equivariant (`diagVec_smul_ratSphere`).
-/

open MeasureTheory Set Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure QuadFormsKB.SphericalZeta

/-! ### Square classes and shells (any number field) -/

section Shells

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

open Classical in
/-- **The square class of $t\in F$** in $F^\times/F^{\times2}$ (junk value $1$ at $t = 0$); any number field. -/
def sqClsNF (t : F) : SqClasses F :=
  if h : t = 0 then 1 else QuotientGroup.mk (Units.mk0 t h)

theorem sqClsNF_of_ne {t : F} (ht : t ≠ 0) : sqClsNF t = QuotientGroup.mk (Units.mk0 t ht) := by
  classical
  unfold sqClsNF
  rw [dif_neg ht]

theorem sqClasses_mk_eq_mk_iff (a b : Fˣ) :
    (QuotientGroup.mk a : SqClasses F) = QuotientGroup.mk b ↔ ∃ y : Fˣ, (a : F) = b * (y : F) ^ 2 := by
  rw [QuotientGroup.eq]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y⁻¹, ?_⟩
    have hy' : ((y : F)) ^ 2 = (a : F)⁻¹ * b := by
      have := congrArg (fun u : Fˣ => (u : F)) hy
      simpa [Units.val_mul, Units.val_inv_eq_inv_val] using this
    rw [Units.val_inv_eq_inv_val, inv_pow, hy']
    have ha : (a : F) ≠ 0 := a.ne_zero
    have hb : (b : F) ≠ 0 := b.ne_zero
    field_simp
  · rintro ⟨y, hy⟩
    refine ⟨y⁻¹, ?_⟩
    ext
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [hy]
    have hb : (b : F) ≠ 0 := b.ne_zero
    have hy0 : (y : F) ≠ 0 := y.ne_zero
    field_simp

/-- $t\in\rho_cF^{\times2}$ iff the square class of $t$ is $c$ ($t\ne0$). -/
theorem mem_sqClass_out_iff {t : F} (ht : t ≠ 0) (c : SqClasses F) :
    t ∈ sqClass ((Quotient.out c : Fˣ) : F) ↔ sqClsNF t = c := by
  rw [sqClsNF_of_ne ht]
  conv_rhs => rw [← QuotientGroup.out_eq' c]
  rw [sqClasses_mk_eq_mk_iff]
  constructor
  · rintro ⟨y, hy, hty⟩
    exact ⟨Units.mk0 y hy, by simpa using hty⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, y.ne_zero, by simpa using hy⟩

open Classical in
/-- Exactly two $\lambda\in F^\times$ satisfy $\rho y^2 = \rho\lambda^2$ ($\rho, y\ne0$). -/
theorem tsum_sq_eq_two' {ρ y : F} (hρ : ρ ≠ 0) (hy : y ≠ 0) :
    ∑' l : Fˣ, (if ρ * y ^ 2 = ρ * (l : F) ^ 2 then (1 : ℝ≥0∞) else 0) = 2 := by
  set u : Fˣ := Units.mk0 y hy
  have hu : u ≠ -u := by
    intro h
    have : (y : F) = -y := by simpa [u] using congrArg (fun z : Fˣ => (z : F)) h
    have h2 : (2 : F) * y = 0 := by linear_combination this
    exact hy ((mul_eq_zero.mp h2).resolve_left two_ne_zero)
  have hiff : ∀ l : Fˣ, ρ * y ^ 2 = ρ * (l : F) ^ 2 ↔ l = u ∨ l = -u := by
    intro l
    constructor
    · intro h
      have h' : ((l : F) - y) * ((l : F) + y) = 0 := by
        have := mul_left_cancel₀ hρ h
        linear_combination -this
      rcases mul_eq_zero.mp h' with h1 | h1
      · left; ext; simp [u]; linear_combination h1
      · right; ext; simp [u]; linear_combination h1
    · rintro (rfl | rfl) <;> simp [u]
  rw [tsum_eq_sum (s := {u, -u})]
  · rw [Finset.sum_pair hu]
    simp only [hiff, true_or, or_true, ↓reduceIte]
    norm_num
  · intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    rw [if_neg]
    rw [hiff]; tauto

open Classical in
/-- **The shell is covered twice by $F^\times\times$ the sphere** (Weil 1982, §4.5, p. 109: "$\xi = M\xi_0\tau$ runs
twice through the set $F(\xi)\in\rho k^{*2}$"), any number field: for $q$ homogeneous of degree $2$, $\rho\ne0$, $G\ge0$,
$$\sum_{\xi:\ q(\xi)\in\rho F^{\times2}}G(\xi) = \frac12\sum_{\lambda\in F^\times}\sum_{\eta:\ q(\eta) = \rho}G(\lambda\eta).$$
Port of `SphericalUnfold.tsum_shell_eq` (stated there over a totally real field; the proof is field-generic). -/
@[kb "weil1982" "§4.5, p. 109 (ξ = Mξ₀τ runs twice through F(ξ) ∈ ρk^{*2})"]
theorem tsum_shell_eq' (q : (Fin n → F) → F) (hq : ∀ (l : F) ξ, q (l • ξ) = l ^ 2 * q ξ) {ρ : F} (hρ : ρ ≠ 0)
    (G : (Fin n → F) → ℝ≥0∞) :
    ∑' ξ : Fin n → F, (if q ξ ∈ sqClass ρ then G ξ else 0) =
      2⁻¹ * ∑' l : Fˣ, ∑' η : Fin n → F, (if q η = ρ then G ((l : F) • η) else 0) := by
  have hinner : ∀ l : Fˣ, ∑' η : Fin n → F, (if q η = ρ then G ((l : F) • η) else 0) =
      ∑' ξ : Fin n → F, (if q ξ = ρ * (l : F) ^ 2 then G ξ else 0) := by
    intro l
    let e : (Fin n → F) ≃ (Fin n → F) :=
      { toFun := fun η => (l : F) • η, invFun := fun ξ => ((l⁻¹ : Fˣ) : F) • ξ,
        left_inv := fun η => by simp [smul_smul], right_inv := fun ξ => by simp [smul_smul] }
    rw [← e.tsum_eq (fun ξ => if q ξ = ρ * (l : F) ^ 2 then G ξ else 0)]
    refine tsum_congr fun η => ?_
    simp only [e, Equiv.coe_fn_mk]
    have hl : (l : F) ≠ 0 := l.ne_zero
    have : q ((l : F) • η) = ρ * (l : F) ^ 2 ↔ q η = ρ := by
      rw [hq]; constructor
      · intro h; exact mul_right_cancel₀ (pow_ne_zero 2 hl) (by linear_combination h)
      · intro h; rw [h]; ring
    exact (if_congr this.symm rfl rfl)
  simp_rw [hinner]
  rw [ENNReal.tsum_comm]
  have hcount : ∀ ξ : Fin n → F, ∑' l : Fˣ, (if q ξ = ρ * (l : F) ^ 2 then G ξ else 0) =
      (if q ξ ∈ sqClass ρ then 2 * G ξ else 0) := by
    intro ξ
    by_cases hs : q ξ ∈ sqClass ρ
    · obtain ⟨y, hy, hξ⟩ := hs
      rw [if_pos ⟨y, hy, hξ⟩]
      have : ∀ l : Fˣ, (if q ξ = ρ * (l : F) ^ 2 then G ξ else 0) =
          G ξ * (if ρ * y ^ 2 = ρ * (l : F) ^ 2 then 1 else 0) := by
        intro l; rw [hξ]; split_ifs <;> simp
      simp_rw [this]
      rw [ENNReal.tsum_mul_left, tsum_sq_eq_two' hρ hy, mul_comm]
    · rw [if_neg hs]
      refine ENNReal.tsum_eq_zero.mpr fun l => ?_
      rw [if_neg]
      intro h
      exact hs ⟨l, l.ne_zero, h⟩
  simp_rw [hcount]
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun ξ => ?_
  split_ifs
  · rw [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  · simp

open Classical in
/-- **The nonzero values split into square classes and shells** (Weil 1982, §4.5, p. 102, (2), and p. 109): for $q$
homogeneous of degree $2$ and $G\ge0$,
$$\sum_{\xi:\ q(\xi)\ne0}G(\xi) = \frac12\sum_{c\in F^\times/F^{\times2}}\sum_{\lambda\in F^\times}
  \sum_{\eta:\ q(\eta) = \rho_c}G(\lambda\eta),\qquad\rho_c = \texttt{Quotient.out}\ c.$$ -/
@[kb "weil1982" "§4.5, (2), p. 102 (sum over ρ ∈ k^×/k^{×2}); p. 109 (shells)"]
theorem tsum_ne_zero_eq_tsum_sqClasses (q : (Fin n → F) → F) (hq : ∀ (l : F) ξ, q (l • ξ) = l ^ 2 * q ξ)
    (G : (Fin n → F) → ℝ≥0∞) :
    ∑' ξ : Fin n → F, (if q ξ ≠ 0 then G ξ else 0) =
      2⁻¹ * ∑' c : SqClasses F, ∑' l : Fˣ, ∑' η : Fin n → F,
        (if q η = ((Quotient.out c : Fˣ) : F) then G ((l : F) • η) else 0) := by
  have hsplit : ∀ ξ : Fin n → F, (if q ξ ≠ 0 then G ξ else 0) =
      ∑' c : SqClasses F, (if q ξ ∈ sqClass ((Quotient.out c : Fˣ) : F) then G ξ else 0) := by
    intro ξ
    by_cases h0 : q ξ = 0
    · rw [if_neg (not_not.mpr h0)]
      refine (ENNReal.tsum_eq_zero.mpr fun c => if_neg ?_).symm
      rintro ⟨y, hy, hξ⟩
      rw [h0] at hξ
      exact (mul_ne_zero (Quotient.out c).ne_zero (pow_ne_zero 2 hy)) hξ.symm
    · rw [if_pos h0, tsum_eq_single (sqClsNF (q ξ))]
      · rw [if_pos ((mem_sqClass_out_iff h0 _).mpr rfl)]
      · intro c hc
        rw [if_neg]
        rw [mem_sqClass_out_iff h0]
        exact fun h => hc h.symm
  simp_rw [hsplit]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun c => tsum_shell_eq' q hq (Quotient.out c).ne_zero G

end Shells

/-! ### The rational spheres as $SO(V)(F)$-sets -/

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- $q(\xi) = Q(\xi)$ for $\xi\in F^n$, $Q = Q_0\otimes F$. -/
abbrev qF (ξ : Fin n → F) : F := (QF).eval ξ

theorem qF_smul (l : F) (ξ : Fin n → F) : qF Q₀ (l • ξ) = l ^ 2 * qF Q₀ ξ :=
  QuadFormsKB.Siegel.Kneser.eval_smul_gen _ ξ l

/-- $2Q(\xi) = \xi^{\mathsf T}H\xi$ ($H$ the Hessian of $Q$), i.e. $q_H = 2Q$. -/
theorem qH_hessian (ξ : Fin n → F) : qH (QF).hessian ξ = 2 * qF Q₀ ξ := by
  have h := QuadFormsKB.Siegel.Kneser.two_mul_evalIn (K := F) (QF) ξ
  rw [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h
  exact h.symm

theorem hessian_transpose : ((QF).hessian)ᵀ = (QF).hessian := by
  simp [QuadForm.hessian, Matrix.transpose_add, add_comm]

/-- The matrix of $\gamma\in SO(V)(F)$. -/
abbrev ratMat (γ : soSub QF F) : Matrix (Fin n) (Fin n) F := ((γ : orthGroup QF F) : GL (Fin n) F).val

theorem ratMat_orth (γ : soSub QF F) : (ratMat Q₀ γ)ᵀ * (QF).hessian * ratMat Q₀ γ = (QF).hessian := by
  have hγ := (mem_orthGroup QF).mp (γ : orthGroup QF F).2
  rwa [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at hγ

/-- $Q(\gamma\xi) = Q(\xi)$ for $\gamma\in SO(V)(F)$. -/
theorem qF_ratMat_mulVec (γ : soSub QF F) (ξ : Fin n → F) : qF Q₀ (ratMat Q₀ γ *ᵥ ξ) = qF Q₀ ξ := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have : qH (QF).hessian (ratMat Q₀ γ *ᵥ ξ) = qH (QF).hessian ξ := by
    unfold qH
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
      ← Matrix.mul_assoc, ratMat_orth, ← Matrix.dotProduct_mulVec]
  rw [qH_hessian, qH_hessian] at this
  exact mul_left_cancel₀ h2 this

/-- $SO(V)(F)\to SO(V)(\mathbb A)$ is injective. -/
theorem diagSOAdele_injective : Function.Injective (diagSOAdele Q₀) := by
  refine (injective_iff_map_eq_one _).mpr fun γ h => ?_
  have h1 : diagF QF (γ : orthGroup QF F) = 1 := congrArg Subtype.val (congrArg Prod.snd h)
  exact Subtype.ext (diagF_injective QF (h1.trans (map_one _).symm))

/-- $SO(V)(F)\cong\Gamma$ = `GammaSOAdele Q₀`. -/
def gammaEquiv : soSub QF F ≃* GammaSOAdele Q₀ := MonoidHom.ofInjective (diagSOAdele_injective Q₀)

theorem gammaEquiv_coe (γ : soSub QF F) : ((gammaEquiv Q₀ γ : GammaSOAdele Q₀) : SOAdele Q₀) = diagSOAdele Q₀ γ :=
  rfl

theorem coe_eq_diagSOAdele_symm (γ : GammaSOAdele Q₀) :
    (γ : SOAdele Q₀) = diagSOAdele Q₀ ((gammaEquiv Q₀).symm γ) := by
  rw [← gammaEquiv_coe, MulEquiv.apply_symm_apply]

/-- **The rational sphere** $T(\rho)(F) = \{\eta\in F^n : Q(\eta) = \rho\}$. -/
def RatSphere (ρ : F) : Type := {η : Fin n → F // qF Q₀ η = ρ}

instance (ρ : F) : Countable (RatSphere Q₀ ρ) :=
  inferInstanceAs (Countable {η : Fin n → F // qF Q₀ η = ρ})

/-- **$\Gamma = SO(V)(F)$ acts on $T(\rho)(F)$** by matrices. -/
instance instMulActionRatSphere (ρ : F) : MulAction (GammaSOAdele Q₀) (RatSphere Q₀ ρ) where
  smul γ η := ⟨ratMat Q₀ ((gammaEquiv Q₀).symm γ) *ᵥ η.1, by rw [qF_ratMat_mulVec]; exact η.2⟩
  one_smul η := Subtype.ext (by
    show ratMat Q₀ ((gammaEquiv Q₀).symm 1) *ᵥ η.1 = η.1
    rw [map_one]
    show ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ η.1 = η.1
    rw [Units.val_one, Matrix.one_mulVec])
  mul_smul γ δ η := Subtype.ext (by
    show ratMat Q₀ ((gammaEquiv Q₀).symm (γ * δ)) *ᵥ η.1 =
      ratMat Q₀ ((gammaEquiv Q₀).symm γ) *ᵥ (ratMat Q₀ ((gammaEquiv Q₀).symm δ) *ᵥ η.1)
    rw [map_mul, Matrix.mulVec_mulVec]; rfl)

theorem ratSphere_smul_val {ρ : F} (γ : GammaSOAdele Q₀) (η : RatSphere Q₀ ρ) :
    (γ • η).1 = ratMat Q₀ ((gammaEquiv Q₀).symm γ) *ᵥ η.1 := rfl

/-- **The diagonal embedding is equivariant**: $j(\gamma\eta) = \gamma\cdot j(\eta)$. -/
theorem diagVec_smul_ratSphere {ρ : F} (γ : GammaSOAdele Q₀) (η : RatSphere Q₀ ρ) :
    diagVec F (Fin n) (γ • η).1 = (γ : SOAdele Q₀) • diagVec F (Fin n) η.1 := by
  rw [ratSphere_smul_val, coe_eq_diagSOAdele_symm, diagSOAdele_smul_diagVec]

/-- **Witt's theorem for $SO(V)(F)$** (O'Meara 42:17 for $SO$; here from the explicit two-reflection section
`exists_SO_mulVec_eq`, no Cartan–Dieudonné): for $Q$ nondegenerate, $n\ge2$ and $\rho\ne0$, $SO(V)(F)$ is transitive on
$T(\rho)(F)$. -/
@[kb "omeara1963" "§42F, 42:17, p. 98 (Witt's theorem for SO(V))"]
theorem exists_smul_eq_ratSphere (hQ : Q₀.Nondegenerate) (hn : 2 ≤ n) {ρ : F} (hρ : ρ ≠ 0)
    (η η' : RatSphere Q₀ ρ) : ∃ γ : GammaSOAdele Q₀, γ • η = η' := by
  set H := (QF).hessian
  have hH : Hᵀ = H := hessian_transpose Q₀
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hdet : H.det ≠ 0 := by
    rw [show H = Q₀.hessian.map (algebraMap (𝓞 F) F) from QuadFormsKB.Siegel.Kneser.hessian_map _ _,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h => hQ ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective (𝓞 F) F) _ h)
  have hq : ∀ ξ : RatSphere Q₀ ρ, qH H ξ.1 = 2 * ρ := fun ξ => by rw [qH_hessian, ξ.2]
  have hx₀ : qH H η.1 ≠ 0 := by rw [hq]; exact mul_ne_zero h2 hρ
  obtain ⟨w, hw, horth⟩ := exists_orth_anisotropic hH h2 hdet hn hx₀
  let D : SphereData H := ⟨η.1, w, hx₀, hw, horth⟩
  obtain ⟨g, hgo, hgd, hg⟩ := exists_SO_mulVec_eq hH h2 D (y := η'.1) (by rw [hq, hq])
  have hu : IsUnit g.det := by rw [hgd]; exact isUnit_one
  let gGL : GL (Fin n) F := Matrix.nonsingInvUnit g hu
  have hgGL : gGL.val = g := rfl
  have hmemO : gGL ∈ orthGroup QF F := by
    rw [mem_orthGroup, Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id, hgGL]; exact hgo
  let γ₀ : soSub QF F := ⟨⟨gGL, hmemO⟩, by rw [mem_soSub]; exact hgd⟩
  refine ⟨gammaEquiv Q₀ γ₀, Subtype.ext ?_⟩
  rw [ratSphere_smul_val, MulEquiv.symm_apply_apply]
  exact hg

end QuadFormsKB.Tamagawa.Measure.Weil
