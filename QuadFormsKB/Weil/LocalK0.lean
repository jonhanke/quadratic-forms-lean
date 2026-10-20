/-
# Local $K_0(\mathfrak N_v)$-equivariance of the lattice function

**Layer:** local, non-archimedean. Every finite place $v$ of a number field $F$, dyadic places included. Only the
local Weil representation `weilRepV` of `Weil/NonArch.lean` (a homomorphism on $\mathrm{SL}_2(F_v)$) and local facts
about $\psi_v$, $\mathbf 1_{\mathcal O_v}$ and its Fourier transform are used: no global input, no Gauss sum is evaluated.

**Setting.** $V_v = \langle a_0, \dots, a_{2m-1}\rangle$ over $F_v$ with $a_i \in \mathcal O_v\setminus\{0\}$, the lattice
$L_v = \mathcal O_v^{2m}$ and $\varphi_v = \mathbf 1_{L_v} = \bigotimes_i\mathbf 1_{\mathcal O_v}$ (`oneS`). The **local level**
of $L_v$ is $\bigcap_i 4a_i\mathfrak d_v$, where $\mathfrak d_v = \mathfrak p_v^{d_v}$ is the local different (`diffExp`):
$t$ lies in the level iff $v(t) \le v(4a_i)\,\exp(-d_v)$ for every $i$ (`LevelV`). It is exactly the condition that
$\psi_v(tQ(y)) = 1$ on the dual lattice $L_v^\# = \{y : 2a_iy_i \in \mathfrak d_v^{-1}\}$.

**Results.**
* `weilRepV_nMat_oneS`, `weilRepV_mMat_oneS`: $\omega_v(n(b))\varphi_v = \varphi_v$ for $b \in \mathcal O_v$;
  $\omega_v(m(t))\varphi_v = \chi_V(t)\varphi_v$ for $t \in \mathcal O_v^\times$.
* `weilRepV_lowerMat_oneS`: $\omega_v\begin{pmatrix}1&0\\t&1\end{pmatrix}\varphi_v = \varphi_v$ for $t$ in the level. *Proof:*
  $\begin{pmatrix}1&0\\t&1\end{pmatrix} = w\,n(-t)\,m(-1)\,w$; $\omega_v(w)\varphi_v = \gamma_V\bigotimes_iF_{a_i}\mathbf 1_{\mathcal O_v}$ is
  supported on $L_v^\#$, where $\psi_v(-tQ) = 1$, it is even, and $F_{a_i}^2 = D_{-1}$; the constant is $\gamma_V^2\chi_V(-1) = 1$.
* **`weilRepV_oneS_of_unit`**: for $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(F_v)$ with $b \in \mathcal O_v$,
  $d \in \mathcal O_v^\times$ and $c$ in the level,
  $$\omega_v(\gamma)\varphi_v = \chi_{V,v}(d)\,\varphi_v,\qquad \chi_{V,v}(d) = (d, (-1)^m\det V)_v,$$
  from $\gamma = n(b/d)\,m(d^{-1})\begin{pmatrix}1&0\\c/d&1\end{pmatrix}$. **There is no Weil-index correction**, at dyadic
  places either: the factorization through the lower unipotent avoids the Bruhat cell, and the two Weil indices
  $\gamma_V$ met on the way cancel ($\gamma_V^2 = \chi_V(-1)$).
* **`weilRepV_oneS_of_good`**: at a good place ($d_v = 0$, $v \nmid 2$, all $a_i$ units), $\varphi_v$ is fixed by all of
  $\mathrm{SL}_2(\mathcal O_v)$; here also $(s, t)_v = 1$ for units (`hilbertSymbol_units_of_good`, from the Weil index:
  $\gamma_v = 1$ on units at a good place and $\gamma_v(st)\gamma_v(1) = (s,t)_v\gamma_v(s)\gamma_v(t)$).
* **`weilRepV_K0`** (the local $K_0(\mathfrak N_v)$-equivariance): for $\gamma \in \mathrm{SL}_2(\mathcal O_v)$ with $c$ in the
  level, $\omega_v(\gamma)\varphi_v = \chi_v(d)\varphi_v$ with the local symbol (`chiLoc`)
  $$\chi_v(d) = (d, (-1)^m\det V)_v\ \text{ if } d \in \mathcal O_v^\times,\qquad \chi_v(d) = 1\ \text{ otherwise}.$$
  ($d \notin \mathcal O_v^\times$ forces $c \in \mathcal O_v^\times$, and then the level condition forces $v$ to be good.)

Sources: Kudla, *Notes on the local theta correspondence* (1996), §I.1 and §II [unverified]; Weil, Acta Math. 111
(1964), §14 [unverified]; Bump, *Automorphic Forms and Representations* (1997), §4.8 (the theta series via
$K_0(N)$-invariance of the lattice function) [unverified]; Rallis, *On the Howe duality conjecture*, Compositio
Math. 51 (1984), §I [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Global

open IsDedekindDomain NumberField Metric MeasureTheory WithZero
open QuadFormsKB.Analysis
open scoped MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep

open LocalData

/-! ### The lower unipotent element and two factorizations -/

section Matrices

variable {k : Type*} [Field k]

/-- **The lower unipotent element** $\begin{pmatrix}1&0\\t&1\end{pmatrix} \in \mathrm{SL}_2(k)$. -/
def lowerMat (t : k) : SL(2, k) := ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

@[simp] lemma lowerMat_coe (t : k) : (lowerMat t : Matrix (Fin 2) (Fin 2) k) = !![1, 0; t, 1] := rfl

/-- $\begin{pmatrix}1&0\\t&1\end{pmatrix} = w\,n(-t)\,m(-1)\,w$. -/
lemma lowerMat_eq (t : k) : lowerMat t = wMat * nMat (-t) * (mMat (-1) * wMat) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- $\gamma = n(b/d)\,m(d^{-1})\begin{pmatrix}1&0\\c/d&1\end{pmatrix}$ when $d \ne 0$. -/
lemma eq_n_m_lower (g : SL(2, k)) (hd : (g : Matrix (Fin 2) (Fin 2) k) 1 1 ≠ 0) :
    g = nMat ((g : Matrix (Fin 2) (Fin 2) k) 0 1 / g 1 1) * mMat (Units.mk0 _ hd)⁻¹ *
      lowerMat ((g : Matrix (Fin 2) (Fin 2) k) 1 0 / g 1 1) := by
  have hdet := det_eq g
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> first | ring1 | linear_combination hdet | linear_combination -hdet

end Matrices

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-! ### The lattice function $\mathbf 1_{L_v}$ -/

lemma ballIndV_zero_mem_SBK : ballIndV v 0 0 ∈ SBK Fv := by
  have e : ballIndV v 0 0 = (closedBall (0 : Fv) 1).indicator fun _ => (1 : ℂ) := by
    unfold ballIndV; rw [ballIndV_eq]; simp
  rw [e]; exact indicator_closedBall_mem_SBK 0 one_pos

variable {m : ℕ}

lemma oneV_mem_Sn : oneV v (2 * m) ∈ (localDataV v).Sn (2 * m) :=
  ptensor_mem_Sn fun _ => ballIndV_zero_mem_SBK v

variable (m) in
/-- **The lattice function** $\varphi_v = \mathbf 1_{L_v} = \bigotimes_{i<2m}\mathbf 1_{\mathcal O_v}$, $L_v = \mathcal O_v^{2m}$, as an
element of $S(V_v)$. -/
@[kb "kudla1996" "§I.4 (the standard lattice function $\\varphi_v = \\mathbf 1_{L_v}$) [unverified]"]
def oneS : (localDataV v).Sn (2 * m) := ⟨oneV v (2 * m), oneV_mem_Sn v⟩

@[simp] lemma oneS_coe : ((oneS v m : (localDataV v).Sn (2 * m)) : (Fin (2 * m) → Fv) → ℂ) = oneV v (2 * m) :=
  rfl

/-! ### The generators on functions -/

variable (a : Fin (2 * m) → (v.adicCompletion F)ˣ)

lemma weilRepV_nMat_apply (b : Fv) (Φ : (localDataV v).Sn (2 * m)) :
    (weilRepV v a (nMat b) Φ : (Fin (2 * m) → Fv) → ℂ) = (localDataV v).opNf a b Φ := by
  simp [weilRepV]

lemma weilRepV_mMat_apply (t : (Fv)ˣ) (Φ : (localDataV v).Sn (2 * m)) :
    (weilRepV v a (mMat t) Φ : (Fin (2 * m) → Fv) → ℂ) = (localDataV v).opMf a t Φ := by
  simp [weilRepV]

lemma weilRepV_wMat_apply (Φ : (localDataV v).Sn (2 * m)) :
    (weilRepV v a wMat Φ : (Fin (2 * m) → Fv) → ℂ) = (localDataV v).opWf a Φ := by
  simp [weilRepV]

/-! ### Valuations -/

lemma md_eq_one {t : Fv} (ht : Valued.v t = 1) : (localDataV v).md t = 1 := by
  show Analysis.Weil.modK _ _ = 1
  rw [modK_eq_norm v (by rintro rfl; simp at ht), norm_eq_one_of_valued ht]

/-- $\psi_v$ is trivial on $\mathfrak d_v^{-1} = \{x : v(x) \le \exp(d_v)\}$. -/
lemma psiV_eq_one_of_le_exp {x : Fv} (hx : Valued.v x ≤ exp (diffExp v : ℤ)) : psiV v x = 1 := by
  have := (mem_invDiffV_iff v x).mpr hx 1 (by simp)
  rwa [one_mul] at this

lemma valued_natCast_le_one (n : ℕ) : Valued.v (n : Fv) ≤ 1 :=
  (norm_le_one_iff_valued v).mp (IsUltrametricDist.norm_natCast_le_one _ _)

lemma valued_four : Valued.v (4 : Fv) = Valued.v (2 : Fv) ^ 2 := by
  rw [← map_pow]; norm_num

/-! ### $\omega_v(n(b))$ and $\omega_v(m(t))$ on $\varphi_v$ -/

/-- $\omega_v(n(b))\varphi_v = \varphi_v$ for $b \in \mathcal O_v$ ($Q$ integral on $L_v$, $\psi_v$ trivial on $\mathcal O_v$). -/
lemma weilRepV_nMat_oneS (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) {b : Fv} (hb : Valued.v b ≤ 1) :
    weilRepV v a (nMat b) (oneS v m) = oneS v m := by
  apply Subtype.ext
  rw [weilRepV_nMat_apply, oneS_coe, oneV, opNf_ptensor]
  congr 1; funext i
  refine chirp_ballIndV ?_
  rw [map_mul]
  calc Valued.v b * Valued.v (a i : Fv) ≤ 1 * 1 := by gcongr; exact ha i
    _ = 1 := one_mul 1

/-- $\omega_v(m(t))\varphi_v = \chi_V(t)\varphi_v$ for $t \in \mathcal O_v^\times$. -/
lemma weilRepV_mMat_oneS (t : (Fv)ˣ) (ht : Valued.v (t : Fv) = 1) :
    weilRepV v a (mMat t) (oneS v m) = (localDataV v).chiV a t • oneS v m := by
  apply Subtype.ext
  rw [weilRepV_mMat_apply, oneS_coe, oneV, opMf_ptensor, md_eq_one v ht, Submodule.coe_smul, oneS_coe, oneV]
  simp only [Complex.ofReal_one, one_pow, mul_one]
  exact congrArg _ (congrArg ptensor (funext fun i => dil_ballIndV ht))

/-! ### The Fourier transform $F_\alpha\mathbf 1_{\mathcal O_v}$ -/

/-- $F_\alpha\mathbf 1_{\mathcal O_v}$ vanishes off $\{y : 2\alpha y \in \mathfrak d_v^{-1}\}$. -/
lemma Fa_ballIndV_eq_zero {α y : Fv} (hy : exp (diffExp v : ℤ) < Valued.v (2 * α * y)) :
    (localDataV v).Fa α (ballIndV v 0 0) y = 0 := by
  simp only [LocalData.Fa, Pi.smul_apply, dil, localDataV_four, fourierV_ballIndV_eq, smul_eq_mul]
  rw [ballIndV, Set.indicator_of_notMem]
  · simp
  · simp only [Set.mem_ofPred_eq, sub_zero, neg_sub, zero_sub, neg_neg, not_le, mul_assoc] at hy ⊢
    simpa [mul_assoc] using hy

/-- **On $L_v^\#$ the chirp $\psi_v(-ta_iy^2)$ is trivial** for $t$ in $4a_i\mathfrak d_v$:
$e_{-t\alpha}F_\alpha\mathbf 1_{\mathcal O_v} = F_\alpha\mathbf 1_{\mathcal O_v}$. -/
lemma chirp_Fa_ballIndV {α t : Fv} (ht : Valued.v t ≤ Valued.v (4 * α) * exp (-(diffExp v : ℤ))) :
    (localDataV v).chirp (-t * α) ((localDataV v).Fa α (ballIndV v 0 0)) =
      (localDataV v).Fa α (ballIndV v 0 0) := by
  funext y
  simp only [LocalData.chirp]
  by_cases hy : Valued.v (2 * α * y) ≤ exp (diffExp v : ℤ)
  · rw [ψV_eq, psiV_eq_one_of_le_exp v, Circle.coe_one, one_mul]
    have h4 : Valued.v (4 * α) * Valued.v α * Valued.v y ^ 2 = Valued.v (2 * α * y) ^ 2 := by
      simp only [map_mul, valued_four, mul_pow]; rw [sq (Valued.v α)]; ac_rfl
    calc Valued.v (-t * α * y ^ 2) = Valued.v t * Valued.v α * Valued.v y ^ 2 := by
          simp [map_mul, Valuation.map_neg]
      _ ≤ (Valued.v (4 * α) * exp (-(diffExp v : ℤ))) * Valued.v α * Valued.v y ^ 2 := by gcongr
      _ = Valued.v (2 * α * y) ^ 2 * exp (-(diffExp v : ℤ)) := by
          rw [← h4]; simp only [mul_comm, mul_left_comm, mul_assoc]
      _ ≤ exp (diffExp v : ℤ) ^ 2 * exp (-(diffExp v : ℤ)) := by gcongr
      _ = exp (diffExp v : ℤ) := by
          rw [← exp_nsmul, ← exp_add]; congr 1; simp; ring
  · rw [Fa_ballIndV_eq_zero v (lt_of_not_ge hy), mul_zero]

/-- $F_\alpha\mathbf 1_{\mathcal O_v}$ is even. -/
lemma dil_neg_one_Fa_ballIndV (α : (Fv)ˣ) :
    dil (-1) ((localDataV v).Fa α (ballIndV v 0 0)) = (localDataV v).Fa α (ballIndV v 0 0) := by
  have h := Fa_dil (isModel_V v) (ballIndV_zero_mem_SBK v) α (-1)
  have h1 : Valued.v ((-1 : (Fv)ˣ) : Fv) = 1 := by simp
  rw [dil_ballIndV h1] at h
  have h2 : (localDataV v).md (((-1 : (Fv)ˣ)) : Fv) = 1 := md_eq_one v h1
  rw [h2] at h
  simp only [Complex.ofReal_one, inv_one, one_smul, inv_neg, inv_one, Units.val_neg, Units.val_one] at h
  exact h.symm

/-- $F_\alpha F_\alpha\mathbf 1_{\mathcal O_v} = \mathbf 1_{\mathcal O_v}$ (Fourier inversion and evenness of $\mathbf 1_{\mathcal O_v}$). -/
lemma Fa_Fa_ballIndV (α : (Fv)ˣ) :
    (localDataV v).Fa α ((localDataV v).Fa α (ballIndV v 0 0)) = ballIndV v 0 0 := by
  rw [Fa_Fa (isModel_V v) (ballIndV_zero_mem_SBK v) α]
  exact dil_ballIndV (by simp)

/-! ### The lower unipotent element -/

/-- **The local level** of $L_v = \mathcal O_v^{2m}$: $t \in \bigcap_i 4a_i\mathfrak d_v$, i.e. $v(t) \le v(4a_i)\exp(-d_v)$ for all
$i$ (0-based). Equivalently $\psi_v(tQ(y)) = 1$ for $y \in L_v^\#$. -/
@[kb "kudla1996" "§I.4 (the level of the lattice $L_v$) [unverified]"]
def LevelV (t : Fv) : Prop := ∀ i, Valued.v t ≤ Valued.v (4 * (a i : Fv)) * exp (-(diffExp v : ℤ))

/-- **$\omega_v\begin{pmatrix}1&0\\t&1\end{pmatrix}\varphi_v = \varphi_v$ for $t$ in the level.** *Proof:* the factorization
$w\,n(-t)\,m(-1)\,w$ and $\omega_v(w)\varphi_v = \gamma_V\bigotimes_iF_{a_i}\mathbf 1_{\mathcal O_v}$; the constant is
$\gamma_V\cdot\chi_V(-1)\cdot\gamma_V = \chi_V(-1)^2 = 1$ (`gammaV_sq`). -/
@[kb "kudla1996" "§I.4 [unverified]"]
theorem weilRepV_lowerMat_oneS {t : Fv} (hlev : LevelV v a t) :
    weilRepV v a (lowerMat t) (oneS v m) = oneS v m := by
  have hD := isModel_V v
  set g : Fin (2 * m) → Fv → ℂ := fun i => (localDataV v).Fa (a i) (ballIndV v 0 0) with hg
  have h1 : (localDataV v).opWf a (oneV v (2 * m)) = (localDataV v).gammaV a • ptensor g := by
    rw [oneV, opWf_ptensor (isOps_V v)]
  have h2 : (localDataV v).opMf a (((-1 : (Fv)ˣ)) : Fv) (ptensor g) =
      (localDataV v).chiV a (-1) • ptensor g := by
    rw [opMf_ptensor, md_eq_one v (by simp)]
    simp only [Complex.ofReal_one, one_pow, mul_one, Units.val_neg, Units.val_one]
    exact congrArg _ (congrArg ptensor (funext fun i => dil_neg_one_Fa_ballIndV v (a i)))
  have h3 : (localDataV v).opNf a (-t) (ptensor g) = ptensor g := by
    rw [opNf_ptensor]; exact congrArg ptensor (funext fun i => chirp_Fa_ballIndV v (hlev i))
  have h4 : (localDataV v).opWf a (ptensor g) = (localDataV v).gammaV a • oneV v (2 * m) := by
    rw [opWf_ptensor (isOps_V v), oneV]
    exact congrArg _ (congrArg ptensor (funext fun i => Fa_Fa_ballIndV v (a i)))
  rw [lowerMat_eq, map_mul, map_mul, map_mul]
  apply Subtype.ext
  simp only [Module.End.mul_apply]
  rw [weilRepV_wMat_apply, weilRepV_nMat_apply, weilRepV_mMat_apply, weilRepV_wMat_apply, oneS_coe, h1,
    opMf_smul, h2, smul_smul, opNf_smul, h3, opWf_smul, h4, smul_smul]
  have hγ := gammaV_sq hD (a := a)
  have hχ := chiV_sq hD (a := a) (-1)
  simp only [Units.val_neg, Units.val_one] at hχ
  have : (localDataV v).gammaV a * (localDataV v).chiV a (-1) * (localDataV v).gammaV a = 1 := by
    linear_combination (localDataV v).chiV a (-1) * hγ + hχ
  rw [this, one_smul]

/-! ### The main local computation -/

/-- **Local equivariance, $d$ a unit** (every finite place, dyadic included): for
$\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(F_v)$ with $b \in \mathcal O_v$, $d \in \mathcal O_v^\times$ and $c$ in the
local level (`LevelV`), and $a_i \in \mathcal O_v$,
$$\omega_v(\gamma)\mathbf 1_{L_v} = (d, (-1)^m\det V)_v\,\mathbf 1_{L_v}.$$
*Proof:* $\gamma = n(b/d)\,m(d^{-1})\begin{pmatrix}1&0\\c/d&1\end{pmatrix}$ (`eq_n_m_lower`) and multiplicativity of $\omega_v$. No
Weil-index correction appears. -/
@[kb "kudla1996" "§I.4; Bump (1997), §4.8 (the lattice function is an eigenvector of $K_0(N)$) [unverified]"]
theorem weilRepV_oneS_of_unit (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (γ : SL(2, Fv))
    (hb : Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) 0 1) ≤ 1)
    (hd : Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) 1 1) = 1)
    (hlev : LevelV v a ((γ : Matrix (Fin 2) (Fin 2) Fv) 1 0)) :
    weilRepV v a γ (oneS v m) = (localDataV v).chiV a ((γ : Matrix (Fin 2) (Fin 2) Fv) 1 1) • oneS v m := by
  have hd0 : (γ : Matrix (Fin 2) (Fin 2) Fv) 1 1 ≠ 0 := by intro h; rw [h] at hd; simp at hd
  have hD := isModel_V v
  rw [eq_n_m_lower γ hd0, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have hlev' : LevelV v a ((γ : Matrix (Fin 2) (Fin 2) Fv) 1 0 / γ 1 1) := by
    intro i; rw [map_div₀, hd, div_one]; exact hlev i
  rw [weilRepV_lowerMat_oneS v a hlev', weilRepV_mMat_oneS v a _ (by simp [hd]), map_smul,
    weilRepV_nMat_oneS v a ha (by rw [map_div₀, hd, div_one]; exact hb)]
  congr 1
  have := chiV_inv hD (a := a) (Units.mk0 _ hd0)
  simpa using this

/-! ### Good places -/

/-- **A good place for $V$ and $L_v$**: $d_v = 0$, $v \nmid 2$ and all $a_i$ are units. -/
def IsGoodV : Prop := diffExp v = 0 ∧ Valued.v (2 : Fv) = 1 ∧ ∀ i, Valued.v (a i : Fv) = 1

/-- **The Hilbert symbol of two units is $1$ at a good place** ($d_v = 0$, $v \nmid 2$). *Proof* (local, via the Weil
index): $\gamma_v = 1$ on units (`weilV_eq_one`) and $\gamma_v(st)\gamma_v(1) = (s,t)_v\gamma_v(s)\gamma_v(t)$
(`HN.weilV_mul_identity`). -/
@[kb "serre1973" "Ch. III, Thm. 1 (the Hilbert symbol on units, $p \\ne 2$, over $\\mathbb{Q}_p$; here over $F_v$) [unverified]"]
theorem hilbertSymbol_units_of_good (hd : diffExp v = 0) (h2 : Valued.v (2 : Fv) = 1) {s t : Fv}
    (hs : Valued.v s = 1) (ht : Valued.v t = 1) : hilbertSymbol Fv s t = 1 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have h := HN.weilV_mul_identity v hs0 ht0
  rw [weilV_eq_one v hd h2 (by rw [map_mul, hs, ht, one_mul]), weilV_eq_one v hd h2 (by simp),
    weilV_eq_one v hd h2 hs, weilV_eq_one v hd h2 ht] at h
  have : (hilbertSymbol Fv s t : ℂ) = 1 := by linear_combination -h
  exact_mod_cast this

variable {v a}

lemma valued_discV_of_good (hg : IsGoodV v a) : Valued.v ((discV a : (Fv)ˣ) : Fv) = 1 := by
  simp [discV, map_prod, hg.2.2]

lemma chiV_eq_one_of_good (hg : IsGoodV v a) {t : Fv} (ht : Valued.v t = 1) : (localDataV v).chiV a t = 1 := by
  simp only [LocalData.chiV, LocalData.hC]
  rw [show (localDataV v).hilb = hilbertSymbol Fv from rfl,
    hilbertSymbol_units_of_good v hg.1 hg.2.1 ht (valued_discV_of_good hg)]
  simp

lemma gammaV_eq_one_of_good (hg : IsGoodV v a) : (localDataV v).gammaV a = 1 := by
  obtain ⟨hd, h2, hai⟩ := hg
  have hg' : IsGoodV v a := ⟨hd, h2, hai⟩
  have hgi : ∀ i, (localDataV v).gN ((a i : (Fv)ˣ) : Fv) = 1 := by
    intro i
    unfold LocalData.gN
    have hγ : (localDataV v).γ (a i : Fv) = 1 := weilV_eq_one v hd h2 (hai i)
    rw [hγ, md_eq_one v (by rw [map_mul, h2, hai i, one_mul]), Real.sqrt_one, Complex.ofReal_one, one_mul]
  rw [LocalData.gammaV, chiV_eq_one_of_good hg' (by simp), Finset.prod_eq_one fun i _ => hgi i, inv_one, one_mul]

variable (v a)

/-- $\omega_v(w)\varphi_v = \varphi_v$ at a good place ($L_v$ is self-dual and $\gamma_V = 1$). -/
lemma weilRepV_wMat_oneS_of_good (hg : IsGoodV v a) : weilRepV v a wMat (oneS v m) = oneS v m := by
  apply Subtype.ext
  rw [weilRepV_wMat_apply, oneS_coe, oneV, opWf_ptensor (isOps_V v), gammaV_eq_one_of_good hg, one_smul]
  congr 1; funext i
  exact Fa_ballIndV hg.1 (by rw [map_mul, hg.2.1, hg.2.2 i, one_mul])

/-- **At a good place $\varphi_v = \mathbf 1_{L_v}$ is $\mathrm{SL}_2(\mathcal O_v)$-invariant**: $d_v = 0$, $v \nmid 2$, all $a_i$ units,
and $\gamma \in \mathrm{SL}_2(F_v)$ with integral entries give $\omega_v(\gamma)\varphi_v = \varphi_v$. *Proof:* if $d$ is a unit,
`weilRepV_oneS_of_unit` (the level is $\mathcal O_v$) and $(d, (-1)^m\det V)_v = 1$; otherwise $c$ is a unit and the
Bruhat cell $n(a/c)\,m(-c^{-1})\,w\,n(d/c)$ fixes $\varphi_v$ factor by factor. -/
@[kb "kudla1996" "§I.4 (the unramified vector is $K$-fixed) [unverified]"]
theorem weilRepV_oneS_of_good (hg : IsGoodV v a) (γ : SL(2, Fv))
    (hint : ∀ i j, Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) i j) ≤ 1) :
    weilRepV v a γ (oneS v m) = oneS v m := by
  have ha : ∀ i, Valued.v (a i : Fv) ≤ 1 := fun i => (hg.2.2 i).le
  by_cases hd : Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) 1 1) = 1
  · have hlev : LevelV v a ((γ : Matrix (Fin 2) (Fin 2) Fv) 1 0) := by
      intro i
      rw [map_mul, valued_four, hg.2.1, hg.2.2 i, hg.1]; simpa using hint 1 0
    rw [weilRepV_oneS_of_unit v a ha γ (hint 0 1) hd hlev, chiV_eq_one_of_good hg hd, one_smul]
  · -- `d` is not a unit, so `c` is a unit
    have hdlt : Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) 1 1) < 1 := lt_of_le_of_ne (hint 1 1) hd
    have hdet := det_eq γ
    have hc : Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) 1 0) = 1 := by
      have had : Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) 0 0 * γ 1 1) < 1 := by
        rw [map_mul]
        calc Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) 0 0) * Valued.v (γ 1 1) ≤ 1 * Valued.v (γ 1 1) := by
              gcongr; exact hint 0 0
          _ < 1 := by rw [one_mul]; exact hdlt
      have hbc : (γ : Matrix (Fin 2) (Fin 2) Fv) 0 1 * γ 1 0 = (γ 0 0 * γ 1 1) - 1 := by
        linear_combination -hdet
      have h1 : Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) 0 1 * γ 1 0) = 1 := by
        rw [hbc, Valuation.map_sub_swap, Valuation.map_sub_eq_of_lt_left _ (by rw [map_one]; exact had), map_one]
      rw [map_mul] at h1
      refine le_antisymm (hint 1 0) ?_
      calc (1 : ℤᵐ⁰) = Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) 0 1) * Valued.v (γ 1 0) := h1.symm
        _ ≤ 1 * Valued.v (γ 1 0) := by gcongr; exact hint 0 1
        _ = _ := one_mul _
    have hc0 : (γ : Matrix (Fin 2) (Fin 2) Fv) 1 0 ≠ 0 := by intro h; rw [h] at hc; simp at hc
    rw [eq_cell_of_c_ne_zero γ hc0, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      Module.End.mul_apply, weilRepV_nMat_oneS v a ha (by rw [map_div₀, hc, div_one]; exact hint 1 1),
      weilRepV_wMat_oneS_of_good v a hg,
      weilRepV_mMat_oneS v a _ (by simp [Valuation.map_neg, hc]),
      chiV_eq_one_of_good hg (by simp [Valuation.map_neg, hc]), one_smul,
      weilRepV_nMat_oneS v a ha (by rw [map_div₀, hc, div_one]; exact hint 0 0)]

/-! ### The local character and the $K_0(\mathfrak N_v)$-equivariance -/

/-- **The local theta character** at $v$: $\chi_v(d) = (d, (-1)^m\det V)_v$ if $d \in \mathcal O_v^\times$, and $\chi_v(d) = 1$
otherwise (the second case occurs only at good places, where both values are trivial on units). -/
@[kb "kudla1996" "§I.1, (1.4) and §I.4 ($\\chi_V$ on $K_0(N)$) [unverified]"]
def chiLoc (d : Fv) : ℂ := if Valued.v d = 1 then (localDataV v).chiV a d else 1

lemma isGoodV_of_level_of_unit (hm : 0 < m) (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) {c : Fv} (hc : Valued.v c = 1)
    (hlev : LevelV v a c) : IsGoodV v a := by
  have h2le : Valued.v (2 : Fv) ≤ 1 := by exact_mod_cast valued_natCast_le_one v 2
  have hk : ∀ i, (1 : ℤᵐ⁰) ≤ Valued.v (2 : Fv) ^ 2 * Valued.v (a i : Fv) * exp (-(diffExp v : ℤ)) := by
    intro i; have := hlev i; rw [hc, map_mul, valued_four] at this; exact this
  have hexp : exp (-(diffExp v : ℤ)) ≤ 1 := by
    rw [← exp_zero, exp_le_exp]; omega
  have hle : ∀ i, Valued.v (2 : Fv) ^ 2 * Valued.v (a i : Fv) * exp (-(diffExp v : ℤ)) ≤ 1 := fun i => by
    calc Valued.v (2 : Fv) ^ 2 * Valued.v (a i : Fv) * exp (-(diffExp v : ℤ)) ≤ 1 ^ 2 * 1 * 1 := by
          gcongr; exact ha i
      _ = 1 := by simp
  have heq : ∀ i, Valued.v (2 : Fv) ^ 2 * Valued.v (a i : Fv) * exp (-(diffExp v : ℤ)) = 1 :=
    fun i => le_antisymm (hle i) (hk i)
  -- squeeze each factor
  have key : ∀ {x y z : ℤᵐ⁰}, x ≤ 1 → y ≤ 1 → z ≤ 1 → x * y * z = 1 → x = 1 ∧ y = 1 ∧ z = 1 := by
    intro x y z hx hy hz h
    have hx' : 1 ≤ x := by
      calc (1 : ℤᵐ⁰) = x * y * z := h.symm
        _ ≤ x * 1 * 1 := by gcongr
        _ = x := by simp
    have hy' : 1 ≤ y := by
      calc (1 : ℤᵐ⁰) = x * y * z := h.symm
        _ ≤ 1 * y * 1 := by gcongr
        _ = y := by simp
    have hz' : 1 ≤ z := by
      calc (1 : ℤᵐ⁰) = x * y * z := h.symm
        _ ≤ 1 * 1 * z := by gcongr
        _ = z := by simp
    exact ⟨le_antisymm hx hx', le_antisymm hy hy', le_antisymm hz hz'⟩
  obtain ⟨i⟩ : Nonempty (Fin (2 * m)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨h2, -, hd⟩ := key (pow_le_one₀ zero_le h2le) (ha i) hexp (heq i)
  refine ⟨?_, ?_, fun j => (key (pow_le_one₀ zero_le h2le) (ha j) hexp (heq j)).2.1⟩
  · rw [← exp_zero, exp_injective.eq_iff] at hd; omega
  · refine le_antisymm h2le ?_
    calc (1 : ℤᵐ⁰) = Valued.v (2 : Fv) ^ 2 := h2.symm
      _ = Valued.v (2 : Fv) * Valued.v (2 : Fv) := sq _
      _ ≤ Valued.v (2 : Fv) * 1 := by gcongr
      _ = _ := mul_one _

/-- **The local $K_0(\mathfrak N_v)$-equivariance of $\mathbf 1_{L_v}$** (every finite place, dyadic included; the heart of
Route 2). Let $a_i \in \mathcal O_v\setminus\{0\}$, $m \ge 1$, and $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(F_v)$
with integral entries and $c$ in the local level $\bigcap_i4a_i\mathfrak d_v$ (`LevelV`). Then
$$\omega_v(\gamma)\mathbf 1_{L_v} = \chi_v(d)\,\mathbf 1_{L_v},\qquad
  \chi_v(d) = \begin{cases}(d, (-1)^m\det V)_v & d \in \mathcal O_v^\times,\\ 1 & \text{otherwise}\end{cases}\quad(\texttt{chiLoc}).$$
*Proof:* `weilRepV_oneS_of_unit` if $d$ is a unit; otherwise $c$ is a unit, the level condition forces $v$ to be good
(`isGoodV_of_level_of_unit`), and `weilRepV_oneS_of_good` applies. -/
@[kb "kudla1996" "§I.4; Bump (1997), §4.8 (the lattice function under $K_0(N)$) [unverified]"]
theorem weilRepV_K0 (hm : 0 < m) (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (γ : SL(2, Fv))
    (hint : ∀ i j, Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) i j) ≤ 1)
    (hlev : LevelV v a ((γ : Matrix (Fin 2) (Fin 2) Fv) 1 0)) :
    weilRepV v a γ (oneS v m) = chiLoc v a ((γ : Matrix (Fin 2) (Fin 2) Fv) 1 1) • oneS v m := by
  by_cases hd : Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) 1 1) = 1
  · rw [chiLoc, if_pos hd]; exact weilRepV_oneS_of_unit v a ha γ (hint 0 1) hd hlev
  · rw [chiLoc, if_neg hd, one_smul]
    have hdlt : Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) 1 1) < 1 := lt_of_le_of_ne (hint 1 1) hd
    have hdet := det_eq γ
    have hc : Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) 1 0) = 1 := by
      have had : Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) 0 0 * γ 1 1) < 1 := by
        rw [map_mul]
        calc Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) 0 0) * Valued.v (γ 1 1) ≤ 1 * Valued.v (γ 1 1) := by
              gcongr; exact hint 0 0
          _ < 1 := by rw [one_mul]; exact hdlt
      have hbc : (γ : Matrix (Fin 2) (Fin 2) Fv) 0 1 * γ 1 0 = (γ 0 0 * γ 1 1) - 1 := by
        linear_combination -hdet
      have h1 : Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) 0 1 * γ 1 0) = 1 := by
        rw [hbc, Valuation.map_sub_swap, Valuation.map_sub_eq_of_lt_left _ (by rw [map_one]; exact had), map_one]
      rw [map_mul] at h1
      refine le_antisymm (hint 1 0) ?_
      calc (1 : ℤᵐ⁰) = Valued.v ((γ : Matrix (Fin 2) (Fin 2) Fv) 0 1) * Valued.v (γ 1 0) := h1.symm
        _ ≤ 1 * Valued.v (γ 1 0) := by gcongr; exact hint 0 1
        _ = _ := one_mul _
    exact weilRepV_oneS_of_good v a (isGoodV_of_level_of_unit v a hm ha hc hlev) γ hint

/-- At a good place the local character is trivial on units: $\chi_v(d) = 1$ for $d \in \mathcal O_v^\times$ (and by
definition for $d \notin \mathcal O_v^\times$), so $\chi_v = 1$ on $K_0(\mathfrak N_v) = \mathrm{SL}_2(\mathcal O_v)$. -/
lemma chiLoc_of_good (hg : IsGoodV v a) (d : Fv) : chiLoc v a d = 1 := by
  unfold chiLoc; split_ifs with h
  · exact chiV_eq_one_of_good hg h
  · rfl

lemma chiLoc_sq (d : Fv) : chiLoc v a d * chiLoc v a d = 1 := by
  unfold chiLoc; split_ifs with h
  · have hd0 : d ≠ 0 := by rintro rfl; simp at h
    simpa using chiV_sq (isModel_V v) (a := a) (Units.mk0 d hd0)
  · simp

end QuadFormsKB.WeilRep
