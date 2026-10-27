import QuadFormsKB.Tamagawa.AdditiveGenus
import QuadFormsKB.Tamagawa.SphericalZeta

/-!
# The $\rho$-wise unfolding of Weil's additive zeta function

**Setting** (as in `AdditiveZeta.lean`). $F$ totally real, $L = \bigoplus_iI_ie_i \subset V = F^n$ with a totally
positive Gram matrix $A$ ($Q(\xi) = \xi^{\mathsf T}A\xi$ = `qv A ξ`), $\Phi = \Phi_\infty\otimes\mathbf 1_{\hat L}$ with
the Gaussian $\Phi_\infty(y) = \exp(-\pi\sum_w\varphi_w(Q)(y_w))$, and the measure $d^\times z$ on $I_F/F^\times$
and on $I_F$.

**The unfolding** (Weil 1982, §4.5, p. 109: the $\mathbb G_m$-half of Lemma 2.4.2 applied to $T(\rho)$). Since $Q$ is anisotropic,
$V(F)\setminus0$ is the disjoint union over the square classes $\rho \in F^\times/F^{\times2}$ of the shells
$\{\xi : Q(\xi)\in\rho F^{\times2}\}$, and $(\lambda,\eta) \mapsto \lambda\eta$ maps $F^\times\times\{Q(\eta) = \rho\}$ two-to-one onto the shell
(`tsum_shell_eq`). The sum over $\lambda \in F^\times$ unfolds the integral over $I_F/F^\times$ to one over $I_F$
(`ideleLIntegral_eq_ideleClassLIntegral`), and on $I_F$ the integrand factors into the ideal $\mathfrak b$ of the
finite part and the infinite part $x$:
$$Z^+_L(s) = \sum_{\rho\in F^\times/F^{\times2}}\frac{|d_F|^{-1/2}}{2}\,I_\rho(s)\sum_{\mathfrak b}N\mathfrak b^{-n-2s}\,
  \#\{\eta\in\mathfrak b^{-1}L : Q(\eta) = \rho\}\qquad(\texttt{additiveZeta\_eq\_tsum\_sqClasses}),$$
$I_\rho(s) = \int_{F_\infty}N(x)^{n+2s}\exp(-\pi\sum_w\sigma_w(\rho)x_w^2)\,dx/N(x)$ (`archMellin`), an equality in $[0,\infty]$ for every real
$s$; $\rho$ runs over the representatives `Quotient.out` of the square classes. For $\rho$ totally positive,
$I_\rho(s) = \prod_w\Gamma(\frac n2+s)(\pi\sigma_w(\rho))^{-n/2-s}$ (`archMellin_eq`).

This is the first of the three layers of `SphericalFibration` : it is unconditional.
-/

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Set Matrix Filter Topology
open scoped Real nonZeroDivisors ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SphericalUnfold

open QuadFormsKB.HilbertModular QuadFormsKB.IdeleClass QuadFormsKB.AdditiveZeta QuadFormsKB.SphericalZeta

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "dq" => Module.finrank ℚ F

/-! ### Lattice coordinates versus vectors -/

/-- **Membership in $L = \bigoplus_iJ_ie_i$**: $\xi_i \in J_i$ for every $i$. -/
def LatMem (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (ξ : Fin n → F) : Prop :=
  ∀ i, ξ i ∈ ((J i : FractionalIdeal (𝓞 F)⁰ F) : Set F)

/-- The lattice coordinates $k \mapsto \xi = $ `latVec J k` are a bijection onto $L = \bigoplus_iJ_ie_i$. -/
def latVecEquiv (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    (Fin n → Fin dq → ℤ) ≃ {ξ : Fin n → F // LatMem J ξ} :=
  (Equiv.piCongrRight fun i => QuadFormsKB.Analysis.latEquiv (J i)).trans
    (Equiv.subtypePiEquivPi (p := fun i (x : F) => x ∈ ((J i : FractionalIdeal (𝓞 F)⁰ F) : Set F))).symm

lemma latVecEquiv_coe (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (k : Fin n → Fin dq → ℤ) :
    ((latVecEquiv J k : {ξ : Fin n → F // LatMem J ξ}) : Fin n → F) = latVec J k := by
  funext i
  exact QuadFormsKB.Analysis.latEquiv_coe (J i) (k i)

open Classical in
/-- **A lattice sum as a sum over vectors**: for $g : F^n \to [0,\infty]$,
$\sum_{k}g(\texttt{latVec}\ J\ k) = \sum_{\xi\in F^n}\mathbf 1[\xi\in L]\,g(\xi)$. -/
lemma tsum_latVec_eq (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (g : (Fin n → F) → ℝ≥0∞) :
    ∑' k : Fin n → Fin dq → ℤ, g (latVec J k) = ∑' ξ : Fin n → F, if LatMem J ξ then g ξ else 0 := by
  rw [← (latVecEquiv J).symm.tsum_eq]
  simp_rw [show ∀ x : {ξ // LatMem J ξ}, latVec J ((latVecEquiv J).symm x) = x from fun x => by
    rw [← latVecEquiv_coe, Equiv.apply_symm_apply]]
  rw [show (∑' c : {ξ // LatMem J ξ}, g c) = ∑' c : ({ξ | LatMem J ξ} : Set (Fin n → F)), g c from rfl,
    tsum_subtype {ξ | LatMem J ξ} g]
  refine tsum_congr fun ξ => ?_
  by_cases h : LatMem J ξ
  · simp [Set.indicator_of_mem (show ξ ∈ {ξ | LatMem J ξ} from h), h]
  · simp [Set.indicator_of_notMem (show ξ ∉ {ξ | LatMem J ξ} from h), h]

open Classical in
/-- **$\Theta^0$ as a sum over vectors**: $\Theta^0_{A,J}(t) = \sum_{\xi\in L\setminus0}\exp(-\pi\sum_v\varphi_v(Q(\xi))t_v)$. -/
lemma thetaZero_eq_tsum_vec (A : Matrix (Fin n) (Fin n) F) (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (t : InfinitePlace F → ℝ) :
    thetaZero A J t = ∑' ξ : Fin n → F,
      if ξ ≠ 0 ∧ LatMem J ξ then ENNReal.ofReal (gaussTerm A ξ t) else 0 := by
  unfold thetaZero
  have h : ∀ k : Fin n → Fin dq → ℤ, (if k = 0 then (0 : ℝ≥0∞) else ENNReal.ofReal (gaussTerm A (latVec J k) t)) =
      (fun ξ => if ξ ≠ 0 then ENNReal.ofReal (gaussTerm A ξ t) else 0) (latVec J k) := by
    intro k
    simp only
    by_cases hk : k = 0
    · simp [hk, latVec_zero]
    · have : latVec J k ≠ 0 := fun h0 => hk (latVec_injective J (h0.trans (latVec_zero J).symm))
      simp [hk, this]
  simp_rw [h]
  rw [tsum_latVec_eq J (fun ξ => if ξ ≠ 0 then ENNReal.ofReal (gaussTerm A ξ t) else 0)]
  refine tsum_congr fun ξ => ?_
  by_cases h1 : LatMem J ξ <;> by_cases h2 : ξ = 0 <;> simp [h1, h2]

/-! ### Square classes -/

open Classical in
/-- **The square class of $t \in F$** in $F^\times/F^{\times2}$ (junk value $1$ at $t = 0$). -/
def sqCls (t : F) : SqClasses F :=
  if h : t = 0 then 1 else QuotientGroup.mk (Units.mk0 t h)

lemma sqCls_of_ne {t : F} (ht : t ≠ 0) : sqCls t = QuotientGroup.mk (Units.mk0 t ht) := by
  classical
  unfold sqCls
  rw [dif_neg ht]

lemma mk_eq_mk_iff (a b : Fˣ) :
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

/-- $t \in \rho_cF^{\times2}$ iff the square class of $t$ is $c$ ($t \ne 0$, $\rho_c$ = `Quotient.out c`). -/
lemma sqClass_out_iff {t : F} (ht : t ≠ 0) (c : SqClasses F) :
    t ∈ sqClass ((Quotient.out c : Fˣ) : F) ↔ sqCls t = c := by
  rw [sqCls_of_ne ht]
  conv_rhs => rw [← QuotientGroup.out_eq' c]
  rw [mk_eq_mk_iff]
  constructor
  · rintro ⟨y, hy, hty⟩
    exact ⟨Units.mk0 y hy, by simpa using hty⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, y.ne_zero, by simpa using hy⟩

/-! ### Shells and spheres -/

open Classical in
/-- **The number of square roots**: for $a = \rho y^2$ with $\rho, y \ne 0$, exactly two $\lambda \in F^\times$ satisfy $a = \rho\lambda^2$. -/
lemma tsum_sq_eq_two {ρ y : F} (hρ : ρ ≠ 0) (hy : y ≠ 0) :
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
/-- **The shell is covered twice by $F^\times\times$ the sphere** (Weil 1982, §4.5, p. 109: "$\xi = M\xi_0\tau$ runs twice through the
set $F(\xi)\in\rho k^{*2}$"): for $q$ homogeneous of degree $2$, $\rho \ne 0$ and $G \ge 0$,
$$\sum_{\xi:\ q(\xi)\in\rho F^{\times2}}G(\xi) = \frac12\sum_{\lambda\in F^\times}\sum_{\eta:\ q(\eta) = \rho}G(\lambda\eta).$$ -/
lemma tsum_shell_eq (q : (Fin n → F) → F) (hq : ∀ (l : F) ξ, q (l • ξ) = l ^ 2 * q ξ) {ρ : F} (hρ : ρ ≠ 0)
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
      rw [ENNReal.tsum_mul_left, tsum_sq_eq_two hρ hy, mul_comm]
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

/-! ### The action of $F^\times$ -/

lemma qv_smul (A : Matrix (Fin n) (Fin n) F) (l : F) (ξ : Fin n → F) : qv A (l • ξ) = l ^ 2 * qv A ξ := by
  simp only [qv, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

lemma realEmb_sq_eq (v : InfinitePlace F) (l : F) : (v l) ^ 2 = realEmb F v (l ^ 2) := by
  rw [map_pow, ← norm_embedding_of_isReal (IsTotallyReal.isReal v) l, Real.norm_eq_abs, sq_abs]
  rfl

/-- $\Phi_\infty(\eta\cdot\lambda x) = \Phi_\infty(\lambda\eta\cdot x)$: the Gaussian term is invariant under moving $\lambda \in F^\times$ from the
idele to the vector. -/
lemma gaussTerm_principalSMulInf (A : Matrix (Fin n) (Fin n) F) (l : Fˣ) (η : Fin n → F) (x : mixedSpace F) :
    gaussTerm A η (sqPlaces (principalSMulInf F l x)) = gaussTerm A ((l : F) • η) (sqPlaces x) := by
  unfold gaussTerm sqPlaces principalSMulInf
  congr 2
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul, normAtPlace_apply, qv_smul, map_mul, ← realEmb_sq_eq]
  ring

/-- **Twisting by a principal ideal**: $\eta \in (\lambda\mathfrak a)^{-1}J$ iff $\lambda\eta \in \mathfrak a^{-1}J$. -/
lemma latMem_twist_principal (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (l : Fˣ) (𝔞 : FracIdeal F)
    (η : Fin n → F) :
    LatMem (twist (principalSMulFin F l 𝔞) J) η ↔ LatMem (twist 𝔞 J) ((l : F) • η) := by
  unfold LatMem twist principalSMulFin
  refine forall_congr' fun i => ?_
  have he : ((toPrincipalIdeal (𝓞 F) F l * 𝔞)⁻¹ * J i : (FractionalIdeal (𝓞 F)⁰ F)ˣ) =
      toPrincipalIdeal (𝓞 F) F l⁻¹ * (𝔞⁻¹ * J i) := by
    rw [mul_inv, map_inv, mul_assoc]
  rw [he, Units.val_mul, coe_toPrincipalIdeal, SetLike.mem_coe, SetLike.mem_coe,
    FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨y, hy, hyη⟩
    rw [Pi.smul_apply, smul_eq_mul, hyη, Units.val_inv_eq_inv_val, ← mul_assoc,
      mul_inv_cancel₀ l.ne_zero, one_mul]
    exact hy
  · intro h
    refine ⟨(l : F) * η i, h, ?_⟩
    rw [Units.val_inv_eq_inv_val, ← mul_assoc, inv_mul_cancel₀ l.ne_zero, one_mul]

/-! ### The integrand, square class by square class -/

/-- The representative $\rho_c$ = `Quotient.out c` $\in F^\times$ of a square class $c$, as an element of $F$. -/
abbrev rep (c : SqClasses F) : F := ((Quotient.out c : Fˣ) : F)

lemma rep_ne_zero (c : SqClasses F) : rep c ≠ 0 := Units.ne_zero _

open Classical in
/-- **The sphere integrand** for $\rho \in F^\times$ at the unramified idele $z = (x,\mathfrak b)$:
$$h_\rho(x,\mathfrak b) = |z|^{n+2s}\sum_{\eta\in\mathfrak b^{-1}L,\ Q(\eta) = \rho}\Phi_\infty(\eta x),$$
the integrand of $\int_{I_F}|z|^{n+2s}\sum_{Q(\eta)=\rho}\Phi(\eta z)\,d^\times z$ (Weil 1982, p. 109). -/
def sphereIntegrand (A : Matrix (Fin n) (Fin n) F) (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (s : ℝ) (ρ : F)
    (x : mixedSpace F) (𝔟 : FracIdeal F) : ℝ≥0∞ :=
  ENNReal.ofReal (ideleNorm F x 𝔟 ^ ((n : ℝ) + 2 * s)) *
    ∑' η : Fin n → F, if qv A η = ρ ∧ LatMem (twist 𝔟 J) η then ENNReal.ofReal (gaussTerm A η (sqPlaces x)) else 0

lemma qv_ne_zero {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A) {ξ : Fin n → F} (hξ : ξ ≠ 0) :
    qv A ξ ≠ 0 := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
  intro h
  have := realEmb_qv_pos hA v hξ
  rw [h, map_zero] at this
  exact lt_irrefl _ this

open Classical in
/-- **The additive integrand, unfolded over the square classes and $F^\times$** (pointwise in $z$): for $A$ totally positive,
$$|z|^{n+2s}\sum_{\xi\in\mathfrak a^{-1}L\setminus0}\Phi_\infty(\xi x) = \sum_{c\in F^\times/F^{\times2}}\frac12\sum_{\lambda\in F^\times}h_{\rho_c}(\lambda z).$$ -/
theorem zetaIntegrand_eq_tsum {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (s : ℝ) (x : mixedSpace F) (𝔞 : FracIdeal F) :
    zetaIntegrand A J s x 𝔞 = ∑' c : SqClasses F, 2⁻¹ * ∑' l : Fˣ,
      sphereIntegrand A J s (rep c) (principalSMulInf F l x) (principalSMulFin F l 𝔞) := by
  set N := ENNReal.ofReal (ideleNorm F x 𝔞 ^ ((n : ℝ) + 2 * s))
  set H : (Fin n → F) → ℝ≥0∞ := fun ξ =>
    if LatMem (twist 𝔞 J) ξ then ENNReal.ofReal (gaussTerm A ξ (sqPlaces x)) else 0
  have hsph : ∀ (c : SqClasses F) (l : Fˣ), sphereIntegrand A J s (rep c) (principalSMulInf F l x)
      (principalSMulFin F l 𝔞) = N * ∑' η : Fin n → F, if qv A η = rep c then H ((l : F) • η) else 0 := by
    intro c l
    unfold sphereIntegrand
    rw [ideleNorm_principal]
    congr 1
    refine tsum_congr fun η => ?_
    simp only [H, latMem_twist_principal, gaussTerm_principalSMulInf]
    by_cases h1 : qv A η = rep c <;> by_cases h2 : LatMem (twist 𝔞 J) ((l : F) • η) <;> simp [h1, h2]
  have hcls : ∀ c : SqClasses F, 2⁻¹ * ∑' l : Fˣ, sphereIntegrand A J s (rep c) (principalSMulInf F l x)
      (principalSMulFin F l 𝔞) = N * ∑' ξ : Fin n → F, if qv A ξ ∈ sqClass (rep c) then H ξ else 0 := by
    intro c
    simp_rw [hsph c]
    rw [ENNReal.tsum_mul_left, mul_left_comm,
      ← tsum_shell_eq (qv A) (qv_smul A) (rep_ne_zero c) H]
  rw [tsum_congr hcls, ENNReal.tsum_mul_left, ENNReal.tsum_comm]
  unfold zetaIntegrand
  rw [thetaZero_eq_tsum_vec]
  congr 1
  refine tsum_congr fun ξ => ?_
  by_cases hξ : ξ = 0
  · subst hξ
    have : ∀ c : SqClasses F, ¬ (0 : F) ∈ sqClass (rep c) := by
      rintro c ⟨y, hy, h⟩
      exact mul_ne_zero (rep_ne_zero c) (pow_ne_zero 2 hy) h.symm
    simp [this]
  · have hq := qv_ne_zero hA hξ
    have : ∀ c : SqClasses F, (if qv A ξ ∈ sqClass (rep c) then H ξ else 0) =
        if c = sqCls (qv A ξ) then H ξ else 0 := fun c => by
      by_cases h : c = sqCls (qv A ξ)
      · rw [if_pos h, if_pos ((sqClass_out_iff hq c).mpr h.symm)]
      · rw [if_neg h, if_neg (fun h' => h ((sqClass_out_iff hq c).mp h').symm)]
    simp_rw [this]
    rw [tsum_ite_eq]
    simp [H, hξ]

/-! ### Unfolding the integral over $I_F/F^\times$ -/

instance : Countable (SqClasses F) := QuotientGroup.mk_surjective.countable

lemma ideleClassLIntegral_tsum {ι : Type*} [Countable ι] (f : ι → mixedSpace F → FracIdeal F → ℝ≥0∞)
    (hf : ∀ i 𝔞, Measurable (f i · 𝔞)) :
    ideleClassLIntegral F (fun x 𝔞 => ∑' i, f i x 𝔞) = ∑' i, ideleClassLIntegral F (f i) := by
  simp only [ideleClassLIntegral]
  rw [ENNReal.tsum_mul_left]
  congr 1
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp_rw [← ENNReal.tsum_mul_right]
  exact lintegral_tsum fun i => ((hf i (classRep F c)).mul (measurable_ofReal_inv_norm F)).aemeasurable

lemma measurable_sphereIntegrand (A : Matrix (Fin n) (Fin n) F) (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (s : ℝ) (ρ : F) (𝔟 : FracIdeal F) : Measurable fun x => sphereIntegrand A J s ρ x 𝔟 := by
  classical
  refine ((measurable_ideleNorm F 𝔟).pow_const _).ennreal_ofReal.mul (Measurable.tsum fun η => ?_)
  split_ifs
  · exact (measurable_gaussTerm_sq A η).ennreal_ofReal
  · exact measurable_const

/-- **Weil's unfolding of the additive zeta function over the spheres** (Weil 1982, §4.5, p. 109; the $\mathbb G_m$-part of
Lemma 2.4.2, p. 26, with the unfolding `ideleLIntegral_eq_ideleClassLIntegral`): for $A$ totally positive,
$$Z^+_L(s) = \sum_{c\in F^\times/F^{\times2}}\frac12\int_{I_F}|z|^{n+2s}\sum_{\eta\in\mathfrak b^{-1}L,\ Q(\eta)=\rho_c}\Phi_\infty(\eta x)\,d^\times z,$$
in $[0,\infty]$ for every real $s$; $\int_{I_F}$ is `ideleLIntegral` (Weil's Tamagawa measure on $I_F$). -/
@[kb "weil1982" "§4.5, p. 109 (ξ = Mξ₀τ runs twice through F(ξ) ∈ ρk*²); Lemma 2.4.2, p. 26"]
theorem additiveZeta_eq_tsum_ideleLIntegral {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (s : ℝ) :
    additiveZeta A J s = ∑' c : SqClasses F, 2⁻¹ * ideleLIntegral F (sphereIntegrand A J s (rep c)) := by
  unfold additiveZeta
  have he : zetaIntegrand A J s = fun x 𝔞 => ∑' c : SqClasses F, 2⁻¹ * ∑' l : Fˣ,
      sphereIntegrand A J s (rep c) (principalSMulInf F l x) (principalSMulFin F l 𝔞) :=
    funext₂ fun x 𝔞 => zetaIntegrand_eq_tsum hA J s x 𝔞
  rw [he, ideleClassLIntegral_tsum]
  · refine tsum_congr fun c => ?_
    rw [ideleClassLIntegral_const_mul F _ (ENNReal.inv_ne_top.mpr two_ne_zero),
      ideleLIntegral_eq_ideleClassLIntegral F _ (measurable_sphereIntegrand A J s (rep c))]
  · intro c 𝔞
    exact measurable_const.mul (Measurable.tsum fun l =>
      (measurable_sphereIntegrand A J s (rep c) _).comp (measurable_principalSMulInf F l))

/-! ### The integral over $I_F$ factors -/

open Classical in
/-- **The number of vectors of the sphere** $\#\{\eta\in\mathfrak b^{-1}L : Q(\eta) = \rho\}$, in $[0,\infty]$. -/
def sphereCount (A : Matrix (Fin n) (Fin n) F) (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (ρ : F)
    (𝔟 : FracIdeal F) : ℝ≥0∞ :=
  ∑' η : Fin n → F, if qv A η = ρ ∧ LatMem (twist 𝔟 J) η then 1 else 0

open Classical in
/-- **The archimedean Mellin integral** $I_\rho(s) = \int_{F_\infty}N(x)^{n+2s}\exp(-\pi\sum_w\sigma_w(\rho)x_w^2)\,\frac{dx}{N(x)}$, in
$[0,\infty]$ (Lebesgue measure $dx$ on $F_\infty$ = `mixedSpace F`, $N(x) = \prod_w|x_w|$). -/
def archMellin (n : ℕ) (s : ℝ) (ρ : F) : ℝ≥0∞ :=
  ∫⁻ x : mixedSpace F, ENNReal.ofReal (mixedEmbedding.norm x ^ ((n : ℝ) + 2 * s)) *
    ENNReal.ofReal (Real.exp (-π * ∑ v, realEmb F v ρ * sqPlaces x v)) *
      ENNReal.ofReal (mixedEmbedding.norm x)⁻¹

lemma gaussTerm_of_qv_eq {A : Matrix (Fin n) (Fin n) F} {η : Fin n → F} {ρ : F} (h : qv A η = ρ)
    (t : InfinitePlace F → ℝ) : gaussTerm A η t = Real.exp (-π * ∑ v, realEmb F v ρ * t v) := by
  rw [gaussTerm, h]

lemma sphereIntegrand_eq (A : Matrix (Fin n) (Fin n) F) (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (s : ℝ)
    (ρ : F) (x : mixedSpace F) (𝔟 : FracIdeal F) :
    sphereIntegrand A J s ρ x 𝔟 = ENNReal.ofReal (idealNorm F 𝔟 ^ (-((n : ℝ) + 2 * s))) * sphereCount A J ρ 𝔟 *
      (ENNReal.ofReal (mixedEmbedding.norm x ^ ((n : ℝ) + 2 * s)) *
        ENNReal.ofReal (Real.exp (-π * ∑ v, realEmb F v ρ * sqPlaces x v))) := by
  classical
  unfold sphereIntegrand sphereCount
  have h1 : ∀ η : Fin n → F, (if qv A η = ρ ∧ LatMem (twist 𝔟 J) η then
      ENNReal.ofReal (gaussTerm A η (sqPlaces x)) else 0) =
      (if qv A η = ρ ∧ LatMem (twist 𝔟 J) η then 1 else 0) *
        ENNReal.ofReal (Real.exp (-π * ∑ v, realEmb F v ρ * sqPlaces x v)) := by
    intro η
    split_ifs with h
    · rw [gaussTerm_of_qv_eq h.1, one_mul]
    · rw [zero_mul]
  simp_rw [h1, ENNReal.tsum_mul_right]
  have hN := idealNorm_pos F 𝔟
  have hx : 0 ≤ mixedEmbedding.norm x := mixedEmbedding.norm_nonneg x
  rw [ideleNorm, Real.div_rpow hx hN.le, div_eq_mul_inv, ← Real.rpow_neg hN.le,
    ENNReal.ofReal_mul (Real.rpow_nonneg hx _)]
  ring

open Classical in
/-- **The integral over $I_F$ of the sphere integrand** (`ideleLIntegral`: $|d_F|^{-1/2}\sum_\mathfrak b\int_{F_\infty}\cdots dx/N(x)$):
$$\int_{I_F}h_\rho\,d^\times z = |d_F|^{-1/2}\,I_\rho(s)\sum_\mathfrak bN\mathfrak b^{-n-2s}\,\#\{\eta\in\mathfrak b^{-1}L : Q(\eta) = \rho\}.$$ -/
theorem ideleLIntegral_sphereIntegrand (A : Matrix (Fin n) (Fin n) F) (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (s : ℝ) (ρ : F) :
    ideleLIntegral F (sphereIntegrand A J s ρ) = ENNReal.ofReal (ideleConst F) * archMellin n s ρ *
      ∑' 𝔟 : FracIdeal F, ENNReal.ofReal (idealNorm F 𝔟 ^ (-((n : ℝ) + 2 * s))) * sphereCount A J ρ 𝔟 := by
  unfold ideleLIntegral
  conv_rhs => rw [mul_assoc, ← ENNReal.tsum_mul_left]
  congr 1
  refine tsum_congr fun 𝔟 => ?_
  simp_rw [sphereIntegrand_eq, mul_assoc]
  have hm : Measurable fun x : mixedSpace F => ENNReal.ofReal (mixedEmbedding.norm x ^ ((n : ℝ) + 2 * s)) *
      (ENNReal.ofReal (Real.exp (-π * ∑ v, realEmb F v ρ * sqPlaces x v)) *
        ENNReal.ofReal (mixedEmbedding.norm x)⁻¹) := by
    refine ((mixedEmbedding.continuous_norm F).measurable.pow_const _).ennreal_ofReal.mul
      (Measurable.mul ?_ (measurable_ofReal_inv_norm F))
    refine (Real.measurable_exp.comp (measurable_const.mul (Finset.measurable_sum _ fun v _ =>
      measurable_const.mul ?_))).ennreal_ofReal
    exact (continuous_normAtPlace v).measurable.pow_const 2
  rw [lintegral_const_mul _ (hm.const_mul _), lintegral_const_mul _ hm, archMellin]
  simp_rw [mul_assoc]
  ring

/-- **The $\rho$-wise unfolding of $Z^+_L$** (Weil 1982, §4.5, p. 109):
$$Z^+_L(s) = \sum_{c\in F^\times/F^{\times2}}\frac{|d_F|^{-1/2}}2\,I_{\rho_c}(s)\sum_{\mathfrak b}N\mathfrak b^{-n-2s}\,
  \#\{\eta\in\mathfrak b^{-1}L : Q(\eta) = \rho_c\},$$
for $A$ totally positive and every real $s$ (in $[0,\infty]$). -/
@[kb "weil1982" "§4.5, p. 109 (unfolding over T(ρ)); Lemma 2.4.2, p. 26; Thm 3.1.1, p. 41 (measure on I_k)"]
theorem additiveZeta_eq_tsum_sqClasses {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (s : ℝ) :
    additiveZeta A J s = ∑' c : SqClasses F, 2⁻¹ * ENNReal.ofReal (ideleConst F) * archMellin n s (rep c) *
      ∑' 𝔟 : FracIdeal F, ENNReal.ofReal (idealNorm F 𝔟 ^ (-((n : ℝ) + 2 * s))) * sphereCount A J (rep c) 𝔟 := by
  rw [additiveZeta_eq_tsum_ideleLIntegral hA]
  refine tsum_congr fun c => ?_
  rw [ideleLIntegral_sphereIntegrand]
  ring

/-! ### The archimedean Mellin integral -/

lemma integrable_abs_rpow_mul_exp {b q : ℝ} (hb : 0 < b) (hq : -1 < q) :
    Integrable fun t : ℝ => |t| ^ q * Real.exp (-b * t ^ 2) := by
  have hI : IntegrableOn (fun t : ℝ => t ^ q * Real.exp (-b * t ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hb hq
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  constructor
  · rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simp only [Function.comp_def, neg_sq, neg_preimage, neg_Iio, neg_zero, abs_neg]
    refine hI.congr_fun (fun t ht => ?_) measurableSet_Ioi
    rw [abs_of_pos ht]
  · refine hI.congr_fun (fun t ht => ?_) measurableSet_Ioi
    rw [abs_of_pos ht]

/-- $\int_{\mathbb R}|t|^q e^{-bt^2}\,dt = b^{-(q+1)/2}\,\Gamma(\frac{q+1}2)$ ($b > 0$, $q > -1$). -/
lemma integral_abs_rpow_mul_exp {b q : ℝ} (hb : 0 < b) (hq : -1 < q) :
    ∫ t : ℝ, |t| ^ q * Real.exp (-b * t ^ 2) = b ^ (-(q + 1) / 2) * Real.Gamma ((q + 1) / 2) := by
  have h := integral_comp_abs (f := fun t : ℝ => t ^ q * Real.exp (-b * t ^ 2))
  simp only [sq_abs] at h
  rw [h]
  have h2 := integral_rpow_mul_exp_neg_mul_rpow two_pos hq hb
  have he : ∫ x in Ioi (0 : ℝ), x ^ q * Real.exp (-b * x ^ 2) =
      ∫ x in Ioi (0 : ℝ), x ^ q * Real.exp (-b * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [Real.rpow_two]
  rw [he, h2]
  ring

open Classical in
/-- **The archimedean Mellin integral, evaluated** ($\rho$ totally positive, $n + 2s > 1$):
$$I_\rho(s) = \int_{F_\infty}N(x)^{n+2s}e^{-\pi\sum_w\sigma_w(\rho)x_w^2}\frac{dx}{N(x)} = \prod_w(\pi\sigma_w(\rho))^{-\frac n2-s}\,\Gamma\big(\tfrac n2+s\big).$$
Each real factor is $\int_{\mathbb R}|t|^{n+2s-1}e^{-\pi\sigma_w(\rho)t^2}dt$. -/
theorem archMellin_eq {s : ℝ} {ρ : F} (hρ : ∀ v : InfinitePlace F, 0 < realEmb F v ρ)
    (ha : 1 < (n : ℝ) + 2 * s) :
    archMellin n s ρ = ∏ v : InfinitePlace F,
      ENNReal.ofReal ((π * realEmb F v ρ) ^ (-((n : ℝ) + 2 * s) / 2) * Real.Gamma (((n : ℝ) + 2 * s) / 2)) := by
  set a : ℝ := (n : ℝ) + 2 * s
  set R := {w : InfinitePlace F // IsReal w}
  set g : R → ℝ → ℝ := fun w t => |t| ^ (a - 1) * Real.exp (-(π * realEmb F w.1 ρ) * t ^ 2)
  set G : (R → ℝ) → ℝ := fun y => ∏ w, g w (y w)
  let eR : InfinitePlace F ≃ R := (Equiv.subtypeUnivEquiv fun w => IsTotallyReal.isReal w).symm
  have hnorm : ∀ x : mixedSpace F, mixedEmbedding.norm x = ∏ w : R, |x.1 w| := by
    intro x
    rw [norm_eq_prod]
    refine Fintype.prod_equiv eR _ _ fun v => ?_
    rw [normAtPlace_apply_of_isReal (IsTotallyReal.isReal v), Real.norm_eq_abs]
    rfl
  have hsum : ∀ x : mixedSpace F, ∑ v, realEmb F v ρ * sqPlaces x v = ∑ w : R, realEmb F w.1 ρ * (x.1 w) ^ 2 := by
    intro x
    refine Fintype.sum_equiv eR _ _ fun v => ?_
    simp only [sqPlaces]
    rw [normAtPlace_apply_of_isReal (IsTotallyReal.isReal v), Real.norm_eq_abs, sq_abs]
    rfl
  have hpt : ∀ x : mixedSpace F, ENNReal.ofReal (mixedEmbedding.norm x ^ a) *
      ENNReal.ofReal (Real.exp (-π * ∑ v, realEmb F v ρ * sqPlaces x v)) *
        ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ = ENNReal.ofReal (G x.1) := by
    intro x
    rw [hnorm, hsum]
    have hN0 : 0 ≤ ∏ w : R, |x.1 w| := Finset.prod_nonneg fun w _ => abs_nonneg _
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hN0 _), ← ENNReal.ofReal_mul
      (mul_nonneg (Real.rpow_nonneg hN0 _) (Real.exp_pos _).le)]
    congr 1
    simp only [G, g]
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    by_cases h0 : ∃ w, x.1 w = 0
    · obtain ⟨w, hw⟩ := h0
      have hP : ∏ w : R, |x.1 w| = 0 := Finset.prod_eq_zero (Finset.mem_univ w) (by simp [hw])
      have hP' : ∏ w : R, |x.1 w| ^ (a - 1) = 0 := Finset.prod_eq_zero (Finset.mem_univ w)
        (by rw [hw, abs_zero, Real.zero_rpow (by linarith)])
      rw [hP, hP', Real.zero_rpow (by linarith)]
      simp
    · push_neg at h0
      have hpos : 0 < ∏ w : R, |x.1 w| := Finset.prod_pos fun w _ => abs_pos.mpr (h0 w)
      have hE : -π * ∑ w : R, realEmb F w.1 ρ * x.1 w ^ 2 = ∑ w : R, -(π * realEmb F w.1 ρ) * x.1 w ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun w _ => by ring
      have hP : (∏ w : R, |x.1 w|) ^ a * (∏ w : R, |x.1 w|)⁻¹ = ∏ w : R, |x.1 w| ^ (a - 1) := by
        rw [Real.finset_prod_rpow _ _ (fun w _ => abs_nonneg _), Real.rpow_sub hpos, Real.rpow_one,
          div_eq_mul_inv]
      rw [hE, mul_right_comm, hP]
  have hA : archMellin n s ρ = ∫⁻ x : mixedSpace F, ENNReal.ofReal (G x.1) := lintegral_congr fun x => hpt x
  rw [hA]
  have hb : ∀ w : R, 0 < π * realEmb F w.1 ρ := fun w => mul_pos Real.pi_pos (hρ w.1)
  have hq : -1 < a - 1 := by linarith
  have hint : Integrable G := Integrable.fintype_prod fun w => integrable_abs_rpow_mul_exp (hb w) hq
  have hG0 : ∀ y, 0 ≤ G y := fun y => Finset.prod_nonneg fun w _ =>
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le
  rw [MeasureTheory.Measure.volume_eq_prod, ← ofReal_integral_eq_lintegral_ofReal (hint.comp_fst _)
    (Eventually.of_forall fun x => hG0 x.1), integral_fun_fst]
  have hν : (volume : Measure ({w : InfinitePlace F // IsComplex w} → ℂ)).real univ = 1 := by
    haveI : IsEmpty {w : InfinitePlace F // IsComplex w} :=
      ⟨fun w => (not_isReal_iff_isComplex.mpr w.2) (IsTotallyReal.isReal w.1)⟩
    simp [Measure.real, volume_pi, Measure.pi_univ]
  rw [hν, one_smul]
  simp only [G]
  rw [volume_pi, integral_fintype_prod_eq_prod]
  simp only [g]
  simp_rw [integral_abs_rpow_mul_exp (hb _) hq]
  rw [ENNReal.ofReal_prod_of_nonneg (fun w _ => mul_nonneg (Real.rpow_nonneg (hb w).le _)
    (Real.Gamma_nonneg_of_nonneg (by positivity)))]
  refine (Fintype.prod_equiv eR _ _ fun v => ?_).symm
  simp only [show a - 1 + 1 = a by ring]
  rfl

/-! ### The archimedean spherical factor of the Gaussian -/

/-- **The radial integral**: $\int_{\mathbb R^n}|y|^{2s}e^{-\pi|y|^2}\,dy = \pi^{-s}\,\Gamma(\frac n2+s)/\Gamma(\frac n2)$ ($n \ge 1$, $s \ge 0$;
polar coordinates, `integral_fun_norm_addHaar`, and the volume $\pi^{n/2}/\Gamma(\frac n2+1)$ of the unit ball). -/
lemma integral_normSq_rpow_mul_exp (hn : 1 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    ∫ y : Fin n → ℝ, (∑ i, y i ^ 2) ^ s * Real.exp (-π * ∑ i, y i ^ 2) =
      π ^ (-s) * Real.Gamma ((n : ℝ) / 2 + s) / Real.Gamma ((n : ℝ) / 2) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set h : ℝ → ℝ := fun r => (r ^ 2) ^ s * Real.exp (-π * r ^ 2)
  have h1 : ∫ y : Fin n → ℝ, (∑ i, y i ^ 2) ^ s * Real.exp (-π * ∑ i, y i ^ 2) =
      ∫ v : EuclideanSpace ℝ (Fin n), h ‖v‖ := by
    rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [h, EuclideanSpace.real_norm_sq_eq]
  rw [h1, integral_fun_norm_addHaar volume h, finrank_euclideanSpace_fin]
  have hball : (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) =
      π ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1) := by
    rw [Measure.real, EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul,
      ENNReal.toReal_ofReal (div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
        (Real.Gamma_nonneg_of_nonneg (by positivity))), Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul Real.pi_pos.le]
    ring_nf
  have hrad : ∫ y in Ioi (0 : ℝ), y ^ (n - 1) • h y =
      π ^ (-((n : ℝ) + 2 * s) / 2) * (1 / 2) * Real.Gamma (((n : ℝ) + 2 * s) / 2) := by
    have := integral_rpow_mul_exp_neg_mul_rpow two_pos (q := (n : ℝ) - 1 + 2 * s) (by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith) Real.pi_pos
    rw [show (n : ℝ) - 1 + 2 * s + 1 = (n : ℝ) + 2 * s by ring] at this
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => ?_
    simp only [h, smul_eq_mul]
    rw [← Real.rpow_natCast, Nat.cast_sub hn, Nat.cast_one, ← Real.rpow_natCast y 2, Nat.cast_ofNat,
      ← Real.rpow_mul hy.le, ← mul_assoc, ← Real.rpow_add hy]
  rw [hball, hrad, nsmul_eq_mul, smul_eq_mul]
  have hG : Real.Gamma ((n : ℝ) / 2 + 1) = (n : ℝ) / 2 * Real.Gamma ((n : ℝ) / 2) :=
    Real.Gamma_add_one (by positivity)
  have hG0 : Real.Gamma ((n : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [hG, show ((n : ℝ) + 2 * s) / 2 = (n : ℝ) / 2 + s by ring,
    show -((n : ℝ) + 2 * s) / 2 = -((n : ℝ) / 2) + -s by ring, Real.rpow_add Real.pi_pos,
    Real.rpow_neg Real.pi_pos.le ((n : ℝ) / 2)]
  have hp : π ^ ((n : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  field_simp

open scoped MatrixOrder in
/-- **Change of variables in a positive definite quadratic form**: $\int_{\mathbb R^n}g(x^{\mathsf T}Bx)\,dx = (\det B)^{-1/2}\int g(|y|^2)\,dy$
for $B$ positive definite and $g$ continuous (the substitution $y = B^{1/2}x$, as in `integral_exp_neg_pi_dotProduct`). -/
lemma integral_comp_dotProduct {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ x : Fin n → ℝ, g (x ⬝ᵥ B *ᵥ x) = (Real.sqrt B.det)⁻¹ * ∫ y : Fin n → ℝ, g (∑ i, y i ^ 2) := by
  set C := CFC.sqrt B
  have h0 : 0 ≤ B := (Matrix.nonneg_iff_posSemidef).2 hB.posSemidef
  have hCC : C * C = B := CFC.sqrt_mul_sqrt_self B h0
  have hCt : Cᵀ = C := by
    have hsa : IsSelfAdjoint C := (CFC.sqrt_nonneg _).isSelfAdjoint
    simpa [Matrix.star_eq_conjTranspose] using hsa.star_eq
  have hdetC : C.det = Real.sqrt B.det := by
    rw [← hCC, det_mul, Real.sqrt_mul_self ((Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg B)).det_nonneg)]
  have hdet0 : C.det ≠ 0 := by rw [hdetC]; exact (Real.sqrt_pos.2 hB.det_pos).ne'
  set L := Matrix.toLin' C
  have hL : LinearMap.det L ≠ 0 := by rw [LinearMap.det_toLin']; exact hdet0
  set G : (Fin n → ℝ) → ℝ := fun y => g (∑ i, y i ^ 2)
  have hcomp : ∀ x : Fin n → ℝ, g (x ⬝ᵥ B *ᵥ x) = G (L x) := fun x => by
    simp only [G, L, Matrix.toLin'_apply]
    rw [sum_sq_mulVec, hCt, hCC]
  simp_rw [hcomp]
  have hGc : Continuous G := hg.comp (by fun_prop)
  rw [← integral_map L.continuous_of_finiteDimensional.measurable.aemeasurable
    hGc.aestronglyMeasurable, Measure.map_linearMap_addHaar_eq_smul_addHaar volume hL, integral_smul_measure,
    LinearMap.det_toLin', hdetC, smul_eq_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv,
    abs_of_pos (Real.sqrt_pos.2 hB.det_pos)]

open Classical in
/-- **The archimedean spherical factor of the Gaussian** ($\rho$ positive at $w$, $s > 0$, $n \ge 1$, $Q_0\otimes F$ totally positive
definite): with $\Phi_w = e^{-\pi Q_w}$ (`GlobalZeta.gaussian Q₀ π`),
$$Z_w(s,\sigma_w\rho) = 2\int_{Q_w(x)\in\sigma_w(\rho)\mathbb R^{\times2}}|Q_w(x)|^se^{-\pi Q_w(x)}\,dx = \frac{2\,\pi^{-s}\,\Gamma(\frac n2+s)}{\Gamma(\frac n2)\sqrt{\det A_w}},$$
$A_w = \varphi_w(A)$, $A = H/2$ (`gramF`). -/
theorem sphArchAt_gaussian (Q₀ : QuadForm (𝓞 F) n) (hpd : Lattices.IsTotallyPosDef (formF Q₀)) (hn : 1 ≤ n)
    (w : Siegel.RealPlace F) {r : ℝ} (hr : 0 < r) {s : ℝ} (hs : 0 < s) :
    sphArchAt Q₀ w (GlobalZeta.gaussian Q₀ π w) r s =
      2 * (π ^ (-s) * Real.Gamma ((n : ℝ) / 2 + s) / Real.Gamma ((n : ℝ) / 2)) *
        (Real.sqrt ((gramF Q₀).map (realEmb F w.1)).det)⁻¹ := by
  have hB : ((gramF Q₀).map (realEmb F w.1)).PosDef := isTotPosGram_of_isTotallyPosDef hpd w.1
  have hsq : ∀ t : ℝ, t ∈ sqClass r ↔ 0 < t := by
    intro t
    constructor
    · rintro ⟨y, hy, rfl⟩; positivity
    · intro ht
      refine ⟨Real.sqrt (t / r), (Real.sqrt_pos.2 (div_pos ht hr)).ne', ?_⟩
      rw [Real.sq_sqrt (div_pos ht hr).le]; field_simp
  unfold sphArchAt
  rw [mul_assoc]
  congr 1
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simp_rw [realVal_eq_dotProduct]
    have hcont : Continuous fun t : ℝ => |t| ^ s * Real.exp (-π * t) :=
      ((Real.continuous_rpow_const hs.le).comp continuous_abs).mul (by fun_prop)
    simp only [GlobalZeta.gaussian]
    simp_rw [realVal_eq_dotProduct]
    rw [integral_comp_dotProduct hB hcont, mul_comm]
    congr 1
    rw [← integral_normSq_rpow_mul_exp hn hs.le]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (y i))]
  · intro x hx
    simp only [Set.mem_preimage, hsq, not_lt] at hx
    have hx0 : GlobalZeta.realVal Q₀ w x = 0 := by
      by_contra h
      have hpos : 0 < GlobalZeta.realVal Q₀ w x := by
        rw [realVal_eq_dotProduct]
        by_cases hx' : x = 0
        · subst hx'; simp [realVal_eq_dotProduct] at h
        · exact hB.dotProduct_mulVec_pos hx'
      linarith
    rw [hx0, abs_zero, Real.zero_rpow hs.ne', zero_mul]

end QuadFormsKB.SphericalUnfold
