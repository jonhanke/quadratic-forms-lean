/-
# Shimura 2004, Proposition 4.6: the homomorphism $\pi$ of (4.16), $a_1, d_4 \in G^+(X)$ and (4.17)

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter I, §4.5,
Proposition 4.6, (4.16), (4.17), (4.20), (4.21) (printed pp. 31–32). Page numbers in the tags are printed pages.

**Setting and dictionary.** As in `Wave6/Prop46.lean`: $V$ with a hyperbolic pair $e_1, f_1$, $U = (Fe_1 +
Ff_1)^\perp$ (`uSpace Q e₁ f₁`), a hyperbolic pair $e_2, f_2$ in $U$, $X = (Fe_2 + Ff_2)^\perp \cap U$, and
$\Theta : A(V) \cong M_4(A(X))$ (`thetaBig`), rows and columns indexed by $(i, k) \in \{0,1\}^2$ in the order
$(0,0), (0,1), (1,0), (1,1)$, i.e. Shimura's indices $1, 2, 3, 4$. Thus
$a_1 = \Theta(\alpha)_{(0,0),(0,0)}$, $d_4 = \Theta(\alpha)_{(1,1),(1,1)}$, and the middle block
$\omega(\alpha) = \begin{pmatrix} a_4 & b_3 \\ c_2 & d_1\end{pmatrix}$ consists of the entries with row and column
in $\{(0,1), (1,0)\}$ (`midIdx`). $I_2 = Fe_1 + Fe_2$ (`Prop46.I₂`) and $P_2^+ = G^+(V) \cap P'_2$ is
`parabolicGPlus Q I₂` ((4.8b)).

**The map $\pi$.** Shimura defines $\pi(\alpha) = \omega(\alpha)\,\mathrm{diag}[d_4^{-1}, d_4^{-1}]$ (4.16) and shows
from (4.20) that $\pi(\alpha) = \begin{pmatrix} s & -q \\ -r & p\end{pmatrix}$, where $\alpha e_1\alpha^{-1} = se_1 +
re_2$ and $\alpha e_2\alpha^{-1} = qe_1 + pe_2$ ((4.18), (4.19)). We define `piMat α` by this formula, the
coefficients read off with $f_1, f_2$ ($s = \varphi(\alpha e_1\alpha^{-1}, f_1)$, etc.), and prove Shimura's
defining identity $\omega(\alpha) = \pi(\alpha)d_4$ entrywise (`omega_eq_piMat_smul`, (4.16), (4.20)).

**Proves** (all unconditional; standard axioms only):
* (4.16), (4.20): $\omega(\alpha) = \pi(\alpha)\,d_4$ for $\alpha \in P'_2$ (`omega_eq_piMat_smul`);
* **Proposition 4.6**: $\pi$ is a homomorphism of $P_2^+$ into $GL_2(F)$ (`piHom`, `piHom_apply`);
* (4.21): $\det(\pi(\alpha))d_4 = a_1$ (`det_piMat_smul`);
* **Proposition 4.6**: $a_1, d_4 \in G^+(X)$ (`a₁_mem_M0`, `d₄_mem_M0`);
* **(4.17)**: $a_1d_4^* = \nu(\alpha) = \det(\pi(\alpha))\nu(d_4) = \det(\pi(\alpha))^{-1}\nu(a_1)$, with
  $\nu(d_4) = d_4d_4^*$, $\nu(a_1) = a_1a_1^*$ (`formula_4_17`).
-/
import QuadFormsKB.Literature.Shimura2004.Wave6.Prop46
import QuadFormsKB.Literature.Shimura2004.Wave4.MatrixGroup
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

namespace Prop46Pi

open MatrixModel Theta Prop46

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {e₁ f₁ : V} {e₂ f₂ : uSpace Q e₁ f₁}

local notation "A" => CliffordAlgebra Q

/-! ### The conjugation $x \mapsto \alpha x\alpha^{-1}$ on $V$ -/

theorem homogeneous_of_mem {J : Submodule F V} {α : Aˣ} (h : α ∈ parabolicG' Q J) :
    α ∈ homogeneousCliffordGroup Q := h.1

/-- $x \mapsto \alpha x\alpha^{-1}$ on $V$ for $\alpha \in P'_J$, i.e. $\tau(\alpha^{-1})$. -/
def cv {J : Submodule F V} (α : parabolicG' Q J) : V ≃ₗ[F] V :=
  tau ⟨((α : Aˣ))⁻¹, homogeneous_le_cliffordGroup ((homogeneousCliffordGroup Q).inv_mem α.2.1)⟩

theorem cv_spec {J : Submodule F V} (α : parabolicG' Q J) (x : V) :
    ι Q (cv α x) = ((α : Aˣ) : A) * ι Q x * (((α : Aˣ)⁻¹ : Aˣ) : A) := by
  rw [cv, tau_spec]
  simp

theorem cv_mul {J : Submodule F V} (α β : parabolicG' Q J) (x : V) : cv (α * β) x = cv α (cv β x) := by
  apply cliffordι_injective Q
  rw [cv_spec, cv_spec, cv_spec]
  simp only [Subgroup.coe_mul, Units.val_mul, mul_inv_rev]
  simp only [mul_assoc]

theorem cv_one {J : Submodule F V} (x : V) : cv (1 : parabolicG' Q J) x = x := by
  apply cliffordι_injective Q
  rw [cv_spec]
  simp

variable (e₁ f₁ e₂ f₂) in
/-- **Shimura's $\pi(\alpha)$** (4.16), p. 31, in the form given by (4.20):
$\pi(\alpha) = \begin{pmatrix} s & -q \\ -r & p\end{pmatrix}$ where $\alpha e_1\alpha^{-1} = se_1 + re_2$ and
$\alpha e_2\alpha^{-1} = qe_1 + pe_2$; the coordinates are $s = \varphi(\alpha e_1\alpha^{-1}, f_1)$,
$r = \varphi(\alpha e_1\alpha^{-1}, f_2)$, $q = \varphi(\alpha e_2\alpha^{-1}, f_1)$,
$p = \varphi(\alpha e_2\alpha^{-1}, f_2)$ ($\varphi$ the bilinear form `QuadraticMap.polar Q`). Shimura's defining
identity $\pi(\alpha)\,\mathrm{diag}[d_4, d_4] = \omega(\alpha)$ is `omega_eq_piMat_smul`. -/
def piMat (α : parabolicG' Q (I₂ e₁ e₂)) : Matrix (Fin 2) (Fin 2) F :=
  !![QuadraticMap.polar Q (cv α e₁) f₁, -QuadraticMap.polar Q (cv α (e₂ : V)) f₁;
    -QuadraticMap.polar Q (cv α e₁) (f₂ : V), QuadraticMap.polar Q (cv α (e₂ : V)) (f₂ : V)]

/-- The middle indices $2, 3$ of Shimura's $4 \times 4$ matrices, i.e. $(0,1), (1,0)$ here. -/
def midIdx : Fin 2 → Fin 2 × Fin 2 := ![(0, 1), (1, 0)]

section Hyp

variable (he₁ : Q e₁ = 0) (hf₁ : Q f₁ = 0) (hef₁ : QuadraticMap.polar Q e₁ f₁ = 1)
  (he₂ : QU Q e₁ f₁ e₂ = 0) (hf₂ : QU Q e₁ f₁ f₂ = 0) (hef₂ : QuadraticMap.polar (QU Q e₁ f₁) e₂ f₂ = 1)

local notation "Θ" => thetaBig he₁ hf₁ hef₁ he₂ hf₂ hef₂

include hef₁ hef₂ in
/-- The coordinates of $se_1 + re_2$ are read off with $f_1$ and $f_2$. -/
theorem polar_comb (s r : F) :
    QuadraticMap.polar Q (s • e₁ + r • (e₂ : V)) f₁ = s ∧
      QuadraticMap.polar Q (s • e₁ + r • (e₂ : V)) (f₂ : V) = r := by
  have h21 : QuadraticMap.polar Q (e₂ : V) f₁ = 0 := (mem_uSpace.1 e₂.2).2
  have h12 : QuadraticMap.polar Q e₁ (f₂ : V) = 0 := by
    rw [QuadraticMap.polar_comm]; exact (mem_uSpace.1 f₂.2).1
  have h22 : QuadraticMap.polar Q (e₂ : V) (f₂ : V) = 1 := hef₂
  simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hef₁, h21, h12, h22, smul_eq_mul]
  constructor <;> ring

include he₁ hf₁ hef₁ he₂ hf₂ hef₂

/-- The conjugation $x \mapsto \alpha x\alpha^{-1}$ maps $e_1$ and $e_2$ into $I_2 = Fe_1 + Fe_2$, with the
coordinates read off by $f_1, f_2$. -/
theorem cv_eq (α : parabolicG' Q (I₂ e₁ e₂)) (x : V) (hx : x ∈ I₂ e₁ e₂) :
    cv α x = QuadraticMap.polar Q (cv α x) f₁ • e₁ + QuadraticMap.polar Q (cv α x) (f₂ : V) • (e₂ : V) := by
  obtain ⟨-, ⟨y, hy, K⟩⟩ := conj_mem he₁ hf₁ hef₁ he₂ hf₂ hef₂ ⟨(α : Aˣ), α.2.1⟩ α.2 x hx
  obtain ⟨s, r, rfl⟩ := (mem_I₂_iff y).1 hy
  have hcv : cv α x = s • e₁ + r • (e₂ : V) := by
    apply cliffordι_injective Q
    rw [cv_spec]
    change ((α : Aˣ) : A) * ι Q x = _ at K
    rw [K, mul_assoc, Units.mul_inv, mul_one]
  rw [hcv, (polar_comb hef₁ hef₂ s r).1, (polar_comb hef₁ hef₂ s r).2]

theorem piMat_one : piMat e₁ f₁ e₂ f₂ (1 : parabolicG' Q (I₂ e₁ e₂)) = 1 := by
  have h1 := polar_comb hef₁ hef₂ (1 : F) 0
  have h2 := polar_comb hef₁ hef₂ (0 : F) 1
  simp only [one_smul, zero_smul, add_zero, zero_add] at h1 h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [piMat, cv_one, h1.1, h1.2, h2.1, h2.2]

theorem piMat_mul (α β : parabolicG' Q (I₂ e₁ e₂)) :
    piMat e₁ f₁ e₂ f₂ (α * β) = piMat e₁ f₁ e₂ f₂ α * piMat e₁ f₁ e₂ f₂ β := by
  have he₁J : e₁ ∈ I₂ e₁ e₂ := Submodule.subset_span (Set.mem_insert _ _)
  have he₂J : (e₂ : V) ∈ I₂ e₁ e₂ := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  have hb1 := cv_eq he₁ hf₁ hef₁ he₂ hf₂ hef₂ β e₁ he₁J
  have hb2 := cv_eq he₁ hf₁ hef₁ he₂ hf₂ hef₂ β (e₂ : V) he₂J
  have ha1 := cv_eq he₁ hf₁ hef₁ he₂ hf₂ hef₂ α e₁ he₁J
  have ha2 := cv_eq he₁ hf₁ hef₁ he₂ hf₂ hef₂ α (e₂ : V) he₂J
  have k1 := cv_mul α β e₁
  have k2 := cv_mul α β (e₂ : V)
  rw [hb1, map_add, map_smul, map_smul, ha1, ha2] at k1
  rw [hb2, map_add, map_smul, map_smul, ha1, ha2] at k2
  have h21 : QuadraticMap.polar Q (e₂ : V) f₁ = 0 := (mem_uSpace.1 e₂.2).2
  have h12 : QuadraticMap.polar Q e₁ (f₂ : V) = 0 := by
    rw [QuadraticMap.polar_comm]; exact (mem_uSpace.1 f₂.2).1
  have h22 : QuadraticMap.polar Q (e₂ : V) (f₂ : V) = 1 := hef₂
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [piMat, k1, k2, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      hef₁, h21, h12, h22, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Proposition 4.6** (Shimura 2004, p. 31): $\pi$ gives a homomorphism of $P_2^+$ into $GL_2(F)$. (It is
defined, and multiplicative, on all of $P'_2 \supseteq P_2^+$: `piMat_mul`.) -/
@[kb "shimura2004" "Prop. 4.6, (4.16), p. 31 (π gives a homomorphism of P_2^+ into GL_2(F))"]
def piHom : parabolicGPlus Q (I₂ e₁ e₂) →* GL (Fin 2) F :=
  MonoidHom.toHomUnits
    { toFun := fun α => piMat e₁ f₁ e₂ f₂ ⟨(α : Aˣ), α.2.2⟩
      map_one' := piMat_one he₁ hf₁ hef₁ he₂ hf₂ hef₂
      map_mul' := fun α β => piMat_mul he₁ hf₁ hef₁ he₂ hf₂ hef₂ ⟨(α : Aˣ), α.2.2⟩ ⟨(β : Aˣ), β.2.2⟩ }

theorem piHom_apply (α : parabolicGPlus Q (I₂ e₁ e₂)) :
    ((piHom he₁ hf₁ hef₁ he₂ hf₂ hef₂ α : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      piMat e₁ f₁ e₂ f₂ ⟨(α : Aˣ), α.2.2⟩ := rfl

theorem conj_eqs (α : parabolicG' Q (I₂ e₁ e₂)) :
    ((α : Aˣ) : A) * ι Q e₁ = ι Q (QuadraticMap.polar Q (cv α e₁) f₁ • e₁ +
        QuadraticMap.polar Q (cv α e₁) (f₂ : V) • (e₂ : V)) * ((α : Aˣ) : A) ∧
      ((α : Aˣ) : A) * ι Q (e₂ : V) = ι Q (QuadraticMap.polar Q (cv α (e₂ : V)) f₁ • e₁ +
        QuadraticMap.polar Q (cv α (e₂ : V)) (f₂ : V) • (e₂ : V)) * ((α : Aˣ) : A) := by
  have he₁J : e₁ ∈ I₂ e₁ e₂ := Submodule.subset_span (Set.mem_insert _ _)
  have he₂J : (e₂ : V) ∈ I₂ e₁ e₂ := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  constructor
  · rw [← cv_eq he₁ hf₁ hef₁ he₂ hf₂ hef₂ α e₁ he₁J, cv_spec, mul_assoc, Units.inv_mul, mul_one]
  · rw [← cv_eq he₁ hf₁ hef₁ he₂ hf₂ hef₂ α (e₂ : V) he₂J, cv_spec, mul_assoc, Units.inv_mul, mul_one]

/-- **(4.16), (4.20)** (Shimura 2004, pp. 31–32): for $\alpha \in P'_2$,
$\omega(\alpha) = \begin{pmatrix} a_4 & b_3 \\ c_2 & d_1\end{pmatrix} = \pi(\alpha)\,\mathrm{diag}[d_4, d_4]$, i.e.
the $(i, j)$ entry of $\omega(\alpha)$ is $\pi(\alpha)_{ij}d_4$. -/
@[kb "shimura2004" "(4.16), (4.20), pp. 31–32 (ω(α) = [[a₄, b₃], [c₂, d₁]] = π(α)diag[d₄, d₄])"]
theorem omega_eq_piMat_smul (α : parabolicG' Q (I₂ e₁ e₂)) (i j : Fin 2) :
    Θ ((α : Aˣ) : A) (midIdx i) (midIdx j) = piMat e₁ f₁ e₂ f₂ α i j • Θ ((α : Aˣ) : A) (1, 1) (1, 1) := by
  obtain ⟨h₁, h₂⟩ := conj_eqs he₁ hf₁ hef₁ he₂ hf₂ hef₂ α
  have E₁ := congrArg Θ h₁
  have E₂ := congrArg Θ h₂
  rw [map_mul, map_mul, thetaBig_comb, thetaBig_e₁, thetaBig_e₂] at E₁ E₂
  have entry : ∀ {X Y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (AU (QU Q e₁ f₁) e₂ f₂)}, X = Y →
      ∀ p q, X p q = Y p q := fun h p q => by rw [h]
  have k1 := entry E₁ (0, 1) (1, 1)
  have k2 := entry E₁ (1, 0) (1, 1)
  have k3 := entry E₂ (0, 1) (1, 1)
  have k4 := entry E₂ (1, 0) (1, 1)
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply] at k1 k2 k3 k4
  simp at k1 k2 k3 k4
  fin_cases i <;> fin_cases j
  · simpa [midIdx, piMat] using k1
  · simp [midIdx, piMat]
    rw [← k3, neg_neg]
  · simpa [midIdx, piMat, neg_smul] using k2
  · simpa [midIdx, piMat] using k4

/-- **(4.21)** (Shimura 2004, p. 32): $\det(\pi(\alpha))\,d_4 = a_1$ for $\alpha \in P'_2$. -/
@[kb "shimura2004" "(4.21), p. 32 (det(π(α))d₄ = (ps − qr)d₄ = a₁)"]
theorem det_piMat_smul (α : parabolicG' Q (I₂ e₁ e₂)) :
    (piMat e₁ f₁ e₂ f₂ α).det • Θ ((α : Aˣ) : A) (1, 1) (1, 1) = Θ ((α : Aˣ) : A) (0, 0) (0, 0) := by
  obtain ⟨h₁, h₂⟩ := conj_eqs he₁ hf₁ hef₁ he₂ hf₂ hef₂ α
  rw [formula_4_21 he₁ hf₁ hef₁ he₂ hf₂ hef₂ ⟨(α : Aˣ), α.2.1⟩ α.2 h₁ h₂, Matrix.det_fin_two, piMat]
  congr 1
  simp
  ring

/-! ### $a_1, d_4 \in G^+(X)$ -/

/-- The corner entries of $\Theta(v)$, $v \in V$: both are the $X$-component of $v$. -/
theorem thetaBig_ι_corners (v : V) :
    Θ (ι Q v) (0, 0) (0, 0) =
        ι (QU (QU Q e₁ f₁) e₂ f₂) (proj he₂ hf₂ hef₂ (proj he₁ hf₁ hef₁ v)) ∧
      Θ (ι Q v) (1, 1) (1, 1) =
        ι (QU (QU Q e₁ f₁) e₂ f₂) (proj he₂ hf₂ hef₂ (proj he₁ hf₁ hef₁ v)) := by
  have h : theta he₂ hf₂ hef₂ (ι (QU Q e₁ f₁) (proj he₁ hf₁ hef₁ v)) =
      psiVec he₂ hf₂ hef₂ (proj he₁ hf₁ hef₁ v) := psi_ι he₂ hf₂ hef₂ _
  rw [thetaBig_apply, thetaBig_apply, psi_ι, psiVec_apply]
  simp [map_neg, h, psiVec_apply]

/-- If $\alpha\beta = 1$ in $P'_2$, then $a_1(\alpha)a_1(\beta) = 1$ and $d_4(\alpha)d_4(\beta) = 1$. -/
theorem corners_mul_eq_one (α β : parabolicG' Q (I₂ e₁ e₂)) (h : α * β = 1) :
    Θ ((α : Aˣ) : A) (0, 0) (0, 0) * Θ ((β : Aˣ) : A) (0, 0) (0, 0) = 1 ∧
      Θ ((α : Aˣ) : A) (1, 1) (1, 1) * Θ ((β : Aˣ) : A) (1, 1) (1, 1) = 1 := by
  obtain ⟨-, hrow⟩ := prop_4_6_shape he₁ hf₁ hef₁ he₂ hf₂ hef₂ ⟨(α : Aˣ), α.2.1⟩ α.2
  obtain ⟨hcol, -⟩ := prop_4_6_shape he₁ hf₁ hef₁ he₂ hf₂ hef₂ ⟨(β : Aˣ), β.2.1⟩ β.2
  have hM : Θ ((α : Aˣ) : A) * Θ ((β : Aˣ) : A) = 1 := by
    rw [← map_mul, ← Units.val_mul]
    have : (α : Aˣ) * (β : Aˣ) = 1 := congrArg Subtype.val h
    rw [this, Units.val_one, map_one]
  have k1 := congrArg (fun M => M (0, 0) (0, 0)) hM
  have k2 := congrArg (fun M => M (1, 1) (1, 1)) hM
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] at k1 k2
  rw [hcol (0, 1) (by decide), hcol (1, 0) (by decide), hcol (1, 1) (by decide)] at k1
  rw [hrow (0, 0) (by decide), hrow (0, 1) (by decide), hrow (1, 0) (by decide)] at k2
  simp only [mul_zero, zero_mul, add_zero, zero_add, Matrix.one_apply_eq] at k1 k2
  exact ⟨k1, k2⟩

/-- $a_1$ as a unit of $A(X)$ (Shimura, p. 32: "$a_1$, $d_4$ … are invertible"). -/
def a₁Unit (α : parabolicG' Q (I₂ e₁ e₂)) : (AU (QU Q e₁ f₁) e₂ f₂)ˣ where
  val := Θ ((α : Aˣ) : A) (0, 0) (0, 0)
  inv := Θ (((α⁻¹ : parabolicG' Q (I₂ e₁ e₂)) : Aˣ) : A) (0, 0) (0, 0)
  val_inv := (corners_mul_eq_one he₁ hf₁ hef₁ he₂ hf₂ hef₂ α α⁻¹ (mul_inv_cancel α)).1
  inv_val := (corners_mul_eq_one he₁ hf₁ hef₁ he₂ hf₂ hef₂ α⁻¹ α (inv_mul_cancel α)).1

/-- $d_4$ as a unit of $A(X)$. -/
def d₄Unit (α : parabolicG' Q (I₂ e₁ e₂)) : (AU (QU Q e₁ f₁) e₂ f₂)ˣ where
  val := Θ ((α : Aˣ) : A) (1, 1) (1, 1)
  inv := Θ (((α⁻¹ : parabolicG' Q (I₂ e₁ e₂)) : Aˣ) : A) (1, 1) (1, 1)
  val_inv := (corners_mul_eq_one he₁ hf₁ hef₁ he₂ hf₂ hef₂ α α⁻¹ (mul_inv_cancel α)).2
  inv_val := (corners_mul_eq_one he₁ hf₁ hef₁ he₂ hf₂ hef₂ α⁻¹ α (inv_mul_cancel α)).2

/-- $a_1xa_1^{-1}$ and $d_4xd_4^{-1}$ are the corner entries of $\Theta(\alpha x\alpha^{-1})$ for $x \in X$. -/
theorem corners_conj (α : parabolicG' Q (I₂ e₁ e₂)) (x : uSpace (QU Q e₁ f₁) e₂ f₂) :
    (a₁Unit he₁ hf₁ hef₁ he₂ hf₂ hef₂ α : AU (QU Q e₁ f₁) e₂ f₂) * ι _ x *
        (((a₁Unit he₁ hf₁ hef₁ he₂ hf₂ hef₂ α)⁻¹ : (AU (QU Q e₁ f₁) e₂ f₂)ˣ) : AU (QU Q e₁ f₁) e₂ f₂) =
        Θ (ι Q (cv α ((x : uSpace Q e₁ f₁) : V))) (0, 0) (0, 0) ∧
      (d₄Unit he₁ hf₁ hef₁ he₂ hf₂ hef₂ α : AU (QU Q e₁ f₁) e₂ f₂) * ι _ x *
        (((d₄Unit he₁ hf₁ hef₁ he₂ hf₂ hef₂ α)⁻¹ : (AU (QU Q e₁ f₁) e₂ f₂)ˣ) : AU (QU Q e₁ f₁) e₂ f₂) =
        Θ (ι Q (cv α ((x : uSpace Q e₁ f₁) : V))) (1, 1) (1, 1) := by
  obtain ⟨-, hrow⟩ := prop_4_6_shape he₁ hf₁ hef₁ he₂ hf₂ hef₂ ⟨(α : Aˣ), α.2.1⟩ α.2
  obtain ⟨hcol, -⟩ := prop_4_6_shape he₁ hf₁ hef₁ he₂ hf₂ hef₂ ⟨((α⁻¹ : parabolicG' Q (I₂ e₁ e₂)) : Aˣ),
    (α⁻¹).2.1⟩ (α⁻¹).2
  have H := congrArg Θ (cv_spec α ((x : uSpace Q e₁ f₁) : V))
  rw [← Subgroup.coe_inv, map_mul, map_mul, thetaBig_ι_X] at H
  have k1 := congrArg (fun M => M (0, 0) (0, 0)) H
  have k2 := congrArg (fun M => M (1, 1) (1, 1)) H
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] at k1 k2
  simp only at hcol
  rw [hcol (0, 1) (by decide), hcol (1, 0) (by decide), hcol (1, 1) (by decide)] at k1
  rw [hrow (0, 0) (by decide), hrow (0, 1) (by decide), hrow (1, 0) (by decide)] at k2
  simp at k1 k2
  constructor
  · rw [k1]; rfl
  · rw [k2]; rfl

/-- **Proposition 4.6** (Shimura 2004, p. 31): for $\alpha \in P_2^+$, $a_1 \in G^+(X)$. -/
@[kb "shimura2004" "Prop. 4.6, p. 31 (a₁ ∈ G⁺(X) for α ∈ P_2^+)"]
theorem a₁_mem_M0 (α : parabolicGPlus Q (I₂ e₁ e₂)) :
    a₁Unit he₁ hf₁ hef₁ he₂ hf₂ hef₂ ⟨(α : Aˣ), α.2.2⟩ ∈ M0 (QU (QU Q e₁ f₁) e₂ f₂) := by
  refine ⟨?_, fun x => ⟨_, ((thetaBig_ι_corners he₁ hf₁ hef₁ he₂ hf₂ hef₂ _).1.symm.trans
    (corners_conj he₁ hf₁ hef₁ he₂ hf₂ hef₂ ⟨(α : Aˣ), α.2.2⟩ x).1.symm)⟩⟩
  have h1 := ((psi_mem_evenOdd_zero_iff he₁ hf₁ hef₁ ((α : Aˣ) : A)).1 α.2.1.1).1
  exact ((psi_mem_evenOdd_zero_iff he₂ hf₂ hef₂ _).1 h1).1

/-- **Proposition 4.6** (Shimura 2004, p. 31): for $\alpha \in P_2^+$, $d_4 \in G^+(X)$. -/
@[kb "shimura2004" "Prop. 4.6, p. 31 (d₄ ∈ G⁺(X) for α ∈ P_2^+)"]
theorem d₄_mem_M0 (α : parabolicGPlus Q (I₂ e₁ e₂)) :
    d₄Unit he₁ hf₁ hef₁ he₂ hf₂ hef₂ ⟨(α : Aˣ), α.2.2⟩ ∈ M0 (QU (QU Q e₁ f₁) e₂ f₂) := by
  refine ⟨?_, fun x => ⟨_, ((thetaBig_ι_corners he₁ hf₁ hef₁ he₂ hf₂ hef₂ _).2.symm.trans
    (corners_conj he₁ hf₁ hef₁ he₂ hf₂ hef₂ ⟨(α : Aˣ), α.2.2⟩ x).2.symm)⟩⟩
  have h1 := ((psi_mem_evenOdd_zero_iff he₁ hf₁ hef₁ ((α : Aˣ) : A)).1 α.2.1.1).2.2.2
  exact ((psi_mem_evenOdd_zero_iff he₂ hf₂ hef₂ _).1 h1).2.2.2

/-! ### (4.17) -/

variable (hQ : (QuadraticMap.associated Q).Nondegenerate)

include hQ in
/-- $a_1d_4^* = \nu(\alpha)$ for $\alpha \in P_2^+$ (Shimura, p. 32: from (3.9) $ad^* - bc^* = \nu(\alpha)$ and
(4.13)). -/
theorem a₁_mul_reverse_d₄ (α : parabolicGPlus Q (I₂ e₁ e₂)) :
    Θ ((α : Aˣ) : A) (0, 0) (0, 0) * reverse (Θ ((α : Aˣ) : A) (1, 1) (1, 1)) =
      algebraMap F (AU (QU Q e₁ f₁) e₂ f₂) (multiplier hQ ⟨(α : Aˣ), α.2.2.1⟩ : F) := by
  set αh : homogeneousCliffordGroup Q := ⟨(α : Aˣ), α.2.2.1⟩
  obtain ⟨hcol, hrow⟩ := prop_4_6_shape he₁ hf₁ hef₁ he₂ hf₂ hef₂ αh α.2.2
  have h39 := (formula_3_9 ⟨psiUnits he₁ hf₁ hef₁ (αh : Aˣ), psi_mem_matGroup he₁ hf₁ hef₁ hQ αh⟩).1
  rw [matMu_psi_of_mem_M0 he₁ hf₁ hef₁ hQ αh α.2.1] at h39
  set P := psi he₁ hf₁ hef₁ ((α : Aˣ) : A)
  replace h39 : P 0 0 * reverse (P 1 1) - P 0 1 * reverse (P 1 0) =
      algebraMap F _ (multiplier hQ αh : F) := h39
  have hpar := (psi_mem_evenOdd_zero_iff he₁ hf₁ hef₁ ((α : Aˣ) : A)).1 α.2.1.1
  have hd : involute (P 1 1) = P 1 1 := involute_eq_of_mem_even hpar.2.2.2
  have hc : involute (P 1 0) = -P 1 0 := (mem_evenOdd_one_iff_involute_eq_neg _).1 hpar.2.2.1
  have E := congrArg (theta he₂ hf₂ hef₂) h39
  rw [map_sub, map_mul, map_mul, theta_reverse, theta_reverse, hd, hc, map_neg, AlgHom.commutes] at E
  have k := congrArg (fun M => M 0 0) E
  have z1 : theta he₂ hf₂ hef₂ (P 1 1) 1 0 = 0 := hrow (1, 0) (by decide)
  have z2 : theta he₂ hf₂ hef₂ (P 1 0) 1 0 = 0 := hrow (0, 0) (by decide)
  have z3 : theta he₂ hf₂ hef₂ (P 1 0) 1 1 = 0 := hrow (0, 1) (by decide)
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, matJ, matStar, Matrix.neg_apply,
    Matrix.map_apply, Matrix.transpose_apply, z1, z2, z3] at k
  simp [Matrix.algebraMap_matrix_apply] at k
  exact k

/-- $\det\pi(\alpha) \ne 0$ for $\alpha \in P_2^+$. -/
theorem det_piMat_ne_zero (α : parabolicGPlus Q (I₂ e₁ e₂)) :
    (piMat e₁ f₁ e₂ f₂ ⟨(α : Aˣ), α.2.2⟩).det ≠ 0 := by
  rw [← piHom_apply he₁ hf₁ hef₁ he₂ hf₂ hef₂]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (piHom he₁ hf₁ hef₁ he₂ hf₂ hef₂ α).isUnit).ne_zero

include hQ in
/-- **(4.17)** (Shimura 2004, p. 31): for $\alpha \in P_2^+$,
$a_1d_4^* = \nu(\alpha) = \det(\pi(\alpha))\,\nu(d_4) = \det(\pi(\alpha))^{-1}\nu(a_1)$, where
$\nu(d_4) = d_4d_4^*$ and $\nu(a_1) = a_1a_1^*$ ((3.4) in $A(X)$; $a_1, d_4 \in G^+(X)$ by `a₁_mem_M0`,
`d₄_mem_M0`). Here $a_1 = \Theta(\alpha)_{11}$, $d_4 = \Theta(\alpha)_{44}$ in Shimura's indexing. -/
@[kb "shimura2004" "(4.17), p. 31 (a₁d₄* = ν(α) = det(π(α))ν(d₄) = det(π(α))⁻¹ν(a₁))"]
theorem formula_4_17 (α : parabolicGPlus Q (I₂ e₁ e₂)) :
    let a₁ := Θ ((α : Aˣ) : A) (0, 0) (0, 0)
    let d₄ := Θ ((α : Aˣ) : A) (1, 1) (1, 1)
    let δ := (piMat e₁ f₁ e₂ f₂ ⟨(α : Aˣ), α.2.2⟩).det
    let ν := algebraMap F (AU (QU Q e₁ f₁) e₂ f₂) (multiplier hQ ⟨(α : Aˣ), α.2.2.1⟩ : F)
    a₁ * reverse d₄ = ν ∧ ν = δ • (d₄ * reverse d₄) ∧ ν = δ⁻¹ • (a₁ * reverse a₁) := by
  intro a₁ d₄ δ ν
  have h1 : a₁ * reverse d₄ = ν := a₁_mul_reverse_d₄ he₁ hf₁ hef₁ he₂ hf₂ hef₂ hQ α
  have ha : a₁ = δ • d₄ := (det_piMat_smul he₁ hf₁ hef₁ he₂ hf₂ hef₂ ⟨(α : Aˣ), α.2.2⟩).symm
  have hδ : δ ≠ 0 := det_piMat_ne_zero he₁ hf₁ hef₁ he₂ hf₂ hef₂ α
  have h2 : ν = δ • (d₄ * reverse d₄) := by rw [← h1, ha, smul_mul_assoc]
  refine ⟨h1, h2, ?_⟩
  rw [h2, ha, map_smul, smul_mul_smul_comm, smul_smul, ← mul_assoc, inv_mul_cancel₀ hδ, one_mul]

end Hyp

end Prop46Pi

end QuadFormsKB.Shimura2004
