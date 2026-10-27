/-
# The real-place fibration at an arbitrary vector, any signature (Siegel's formula for indefinite forms)

**Layer:** real analysis on $SO(Q)(\mathbb R)$ (the Leray measures, the orbital identity).

Let $Q$ be a nondegenerate real quadratic form in $n = m+1\ge2$ variables of **any signature**, $c\ne0$, and
$S_c = \{Q = c\}$ (`SphereLeray.Sph`) with its Leray measure $\sigma_c = dx/dQ$ (`SphereLeray.sig`). The group
$G = SO(Q)(\mathbb R)$ acts on $\mathbb R^n$ by $g\cdot v = gv$ (`archSOAction`). `OrbitalReal.lean` proved the
orbital identity only for the split form $\langle c\rangle\perp Q'$ at the base point $e_0$. Here it is moved to
**every** point $y\in S_c$ by a change of basis $P$ with $Pe_0 = y$ and $Q\circ P = \langle c\rangle\perp Q'_y$
(`OrthFq.exists_split`, `eq_splitForm_of`).

**Proves** (all unconditional, standard axioms only)
* `orbitCoordOfSection` (abstract): a measurable section $S$ of $g\mapsto gy$ gives orbit coordinates
  $T\times H_y\cong G$, $(x, h)\mapsto hS(x)^{-1}$, for the stabilizer $H_y$ of $y$;
* `nu_eq_smul_map_sphGL`: under $x\mapsto Px$ the cone measures satisfy $\nu_{Q} = |\det P|\cdot P_*\nu_{Q\circ P}$, and
  likewise for $\sigma_c$ (`sig_eq_smul_map_sphGL`);
* `lerayMeasure_fibration_at` (**the real-place fibration at $y$**): for every $y$ with $Q(y) = c$,
  $$\mu_Q = |2c|^{-m}\cdot\mathrm{coord}_*(\sigma_c\otimes\mu_{H_y}),\qquad \mathrm{coord}(x, h) = hS(x)^{-1},$$
  where $\mu_{H_y}$ (`stabMeasure`) is the Haar measure on $H_y = \operatorname{Stab}_G(y)\cong SO(Q'_y)(\mathbb R)$
  determined by this identity (the quotient measure: an explicit positive multiple of the image of the Leray measure of
  $Q'_y$);
* `realArchFibration` (**packaging**): these data form an `ArchFibration` over $S_c$ with the single constant
  $|2c|^{-m}$, the input of the classical theta unfolding (`ThetaUnfold.lean`).

**Outside results used:** Mathlib's `isMulLeftInvariant_eq_smul` (uniqueness of Haar measure),
`addHaar_image_linearMap`, `Measure.ext_of_lintegral`; the library's `lerayMeasure_orbital`, `sphSection`,
`exists_iota_eq_of_mulVec_e₀`, `conjEquiv`, `exists_split` (`OrthFq.lean`), `eq_splitForm_of`,
`lintegral_inv_lerayMeasure` (unimodularity).
-/
import QuadFormsKB.Tamagawa.Indefinite.ThetaUnfold
import QuadFormsKB.Tamagawa.Measure.OrbitalReal
import QuadFormsKB.Tamagawa.Measure.ConeReal
import QuadFormsKB.Tamagawa.OrthFq
import QuadFormsKB.Tamagawa.AlphaLawMoves

open MeasureTheory Measure Matrix MulAction Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.Tamagawa.ArchSOMeasure
open QuadFormsKB.Tamagawa.Measure.Weil

/-! ### Orbit coordinates from a measurable section (abstract) -/

section Section

variable {A : Type*} [Group A] [MeasurableSpace A] [MeasurableMul₂ A] [MeasurableInv A]
  {Y : Type*} [MulAction A Y] {T : Type*} [MeasurableSpace T]

theorem mul_section_mem_stabilizer {τ : T → Y} {y : Y} {S : T → A} (hSy : ∀ x, S x • y = τ x) {π : A → T}
    (hπy : ∀ g, τ (π g) = g⁻¹ • y) (g : A) : g * S (π g) ∈ stabilizer A y := by
  rw [mem_stabilizer_iff, mul_smul, hSy, hπy, smul_inv_smul]

/-- The inverse of the orbit coordinates: $g\mapsto(\pi g, gS(\pi g))$. -/
def sectionInv {τ : T → Y} {y : Y} {S : T → A} (hSy : ∀ x, S x • y = τ x) {π : A → T}
    (hπy : ∀ g, τ (π g) = g⁻¹ • y) (g : A) : T × stabilizer A y :=
  (π g, ⟨g * S (π g), mul_section_mem_stabilizer hSy hπy g⟩)

theorem measurable_sectionInv {τ : T → Y} {y : Y} {S : T → A} (hS : Measurable S) (hSy : ∀ x, S x • y = τ x)
    {π : A → T} (hπ : Measurable π) (hπy : ∀ g, τ (π g) = g⁻¹ • y) : Measurable (sectionInv hSy hπy) :=
  hπ.prodMk ((measurable_id.mul (hS.comp hπ)).subtype_mk)

/-- **Orbit coordinates from a section.** Let $\tau : T\to Y$ be injective (the orbit of `y`, parametrized), $S : T\to A$
a measurable section of the orbit map ($S(x)\,y = \tau(x)$) and $\pi : A\to T$ measurable with $\tau(\pi g) = g^{-1}y$.
Then $(x, h)\mapsto hS(x)^{-1}$ is a measurable equivalence $T\times\operatorname{Stab}_A(y)\cong A$ with inverse
$g\mapsto(\pi g, gS(\pi g))$, and it is an `OrbitCoord` for the inclusion of the stabilizer. Parameters: `τ`, `hτ`,
`y`, `S`, `hS`, `hSy`, `π`, `hπ`, `hπy`. -/
def orbitCoordOfSection (τ : T → Y) (hτ : Function.Injective τ) (y : Y) (S : T → A) (hS : Measurable S)
    (hSy : ∀ x, S x • y = τ x) (π : A → T) (hπ : Measurable π) (hπy : ∀ g, τ (π g) = g⁻¹ • y) :
    OrbitCoord (stabilizer A y).subtype τ y where
  coord :=
    { toFun := fun p => (p.2 : A) * (S p.1)⁻¹
      invFun := sectionInv hSy hπy
      left_inv := by
        rintro ⟨x, h⟩
        have hx : π ((h : A) * (S x)⁻¹) = x := hτ (by
          rw [hπy, _root_.mul_inv_rev, inv_inv, mul_smul, mem_stabilizer_iff.mp (inv_mem h.2), hSy])
        ext
        · exact hx
        · simp [sectionInv, hx]
      right_inv := fun g => by simp [sectionInv]
      measurable_toFun := (measurable_subtype_coe.comp measurable_snd).mul (hS.comp measurable_fst).inv
      measurable_invFun := measurable_sectionInv hS hSy hπ hπy }
  mul := fun x h h' => by simp [mul_assoc]
  orbit := fun x h => by
    show ((h : A) * (S x)⁻¹)⁻¹ • y = τ x
    rw [_root_.mul_inv_rev, inv_inv, mul_smul, mem_stabilizer_iff.mp (inv_mem h.2), hSy]

theorem orbitCoordOfSection_coord {τ : T → Y} {hτ : Function.Injective τ} {y : Y} {S : T → A} {hS : Measurable S}
    {hSy : ∀ x, S x • y = τ x} {π : A → T} {hπ : Measurable π} {hπy : ∀ g, τ (π g) = g⁻¹ • y} (x : T)
    (h : stabilizer A y) :
    (orbitCoordOfSection τ hτ y S hS hSy π hπ hπy).coord (x, h) = (h : A) * (S x)⁻¹ := rfl

end Section

/-! ### $SO(Q)(\mathbb R)$ acting on $\mathbb R^n$ -/

section Action

open QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.SphereLeray

variable {n : ℕ}

/-- **The action of $SO(Q)(\mathbb R)$ on $\mathbb R^n$**: $g\cdot v = gv$ (matrix times column vector). -/
instance archSOAction (Q : QuadForm ℝ n) : MulAction (ArchSO Q) (Fin n → ℝ) where
  smul g v := ArchSOInst.mat Q g *ᵥ v
  one_smul v := by
    show ArchSOInst.mat Q 1 *ᵥ v = v
    rw [ArchSOInst.mat_one, one_mulVec]
  mul_smul g h v := by
    show ArchSOInst.mat Q (g * h) *ᵥ v = ArchSOInst.mat Q g *ᵥ (ArchSOInst.mat Q h *ᵥ v)
    rw [ArchSOInst.mat_mul, mulVec_mulVec]

theorem archSO_smul_def (Q : QuadForm ℝ n) (g : ArchSO Q) (v : Fin n → ℝ) : g • v = ArchSOInst.mat Q g *ᵥ v := rfl

theorem continuous_archSO_smul (Q : QuadForm ℝ n) :
    Continuous fun p : ArchSO Q × (Fin n → ℝ) => p.1 • p.2 :=
  ((ArchSOInst.continuous_mat Q).comp continuous_fst).matrix_mulVec continuous_snd

theorem measurable_archSO_inv_smul (Q : QuadForm ℝ n) (y : Fin n → ℝ) :
    Measurable fun g : ArchSO Q => g⁻¹ • y :=
  ((continuous_archSO_smul Q).comp ((continuous_inv).prodMk continuous_const)).measurable

theorem eval_archSO_smul (Q : QuadForm ℝ n) (g : ArchSO Q) (v : Fin n → ℝ) : Q.eval (g • v) = Q.eval v :=
  eval_mulVec_of_isometry Q (ArchSOInst.isometry Q g) v

end Action

/-! ### The sphere measures under a linear change of variables -/

section SphereGL

open QuadFormsKB.Tamagawa.Measure.SphereLeray

variable {n : ℕ} {Q Q₁ : QuadForm ℝ n}

/-- The map $S_c(Q_1)\to S_c(Q)$, $x\mapsto Px$, for $Q_1 = Q\circ P$. -/
def sphGL (P : GL (Fin n) ℝ) (hP : ∀ x, Q₁.eval x = Q.eval ((P : Matrix (Fin n) (Fin n) ℝ) *ᵥ x)) (c : ℝ)
    (x : Sph Q₁ c) : Sph Q c :=
  ⟨(P : Matrix (Fin n) (Fin n) ℝ) *ᵥ (x : Fin n → ℝ), by show Q.eval _ = c; rw [← hP]; exact x.2⟩

theorem continuous_sphGL (P : GL (Fin n) ℝ) (hP : ∀ x, Q₁.eval x = Q.eval ((P : Matrix (Fin n) (Fin n) ℝ) *ᵥ x))
    (c : ℝ) : Continuous (sphGL P hP c) :=
  ((Matrix.toLin' (P : Matrix (Fin n) (Fin n) ℝ)).continuous_of_finiteDimensional.comp
    continuous_subtype_val).subtype_mk _

theorem det_GL_ne_zero (P : GL (Fin n) ℝ) : (P : Matrix (Fin n) (Fin n) ℝ).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit P)).ne_zero

/-- **The cone measure under a linear change of variables**: $\nu_Q = |\det P|\cdot(x\mapsto Px)_*\nu_{Q\circ P}$. -/
theorem nu_eq_smul_map_sphGL {c : ℝ} (hc : c ≠ 0) (P : GL (Fin n) ℝ)
    (hP : ∀ x, Q₁.eval x = Q.eval ((P : Matrix (Fin n) (Fin n) ℝ) *ᵥ x)) :
    nu Q c = ENNReal.ofReal |(P : Matrix (Fin n) (Fin n) ℝ).det| • (nu Q₁ c).map (sphGL P hP c) := by
  ext A hA
  have hm := (continuous_sphGL P hP c).measurable
  rw [Measure.smul_apply, Measure.map_apply hm hA, nu_apply hc hA, nu_apply hc (hm hA), smul_eq_mul]
  have himg : Matrix.toLin' (P : Matrix (Fin n) (Fin n) ℝ) '' (pol Q₁ c '' (Iic 0 ×ˢ (sphGL P hP c ⁻¹' A))) =
      pol Q c '' (Iic 0 ×ˢ A) := by
    ext v
    constructor
    · rintro ⟨_, ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩, rfl⟩
      exact ⟨(t, sphGL P hP c x), ⟨ht, hx⟩, by simp [pol, sphGL]⟩
    · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
      set Pi : Matrix (Fin n) (Fin n) ℝ := ((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
      have hPPi : (P : Matrix (Fin n) (Fin n) ℝ) * Pi = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hx₁ : Q₁.eval (Pi *ᵥ (x : Fin n → ℝ)) = c := by
        rw [hP, mulVec_mulVec, hPPi, one_mulVec]; exact x.2
      let x₁ : Sph Q₁ c := ⟨Pi *ᵥ (x : Fin n → ℝ), hx₁⟩
      have hx₁x : sphGL P hP c x₁ = x := Subtype.ext (by simp [sphGL, x₁, mulVec_mulVec, hPPi])
      refine ⟨pol Q₁ c (t, x₁), ⟨(t, x₁), ⟨ht, ?_⟩, rfl⟩, ?_⟩
      · show sphGL P hP c x₁ ∈ A
        rw [hx₁x]; exact hx
      · rw [← hx₁x]; simp [pol, sphGL]
  rw [← himg, MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin']
  ring

/-- **The Leray measure of the sphere under a linear change of variables**:
$\sigma_c(Q) = |\det P|\cdot(x\mapsto Px)_*\sigma_c(Q\circ P)$. -/
theorem sig_eq_smul_map_sphGL {c : ℝ} (hc : c ≠ 0) (P : GL (Fin n) ℝ)
    (hP : ∀ x, Q₁.eval x = Q.eval ((P : Matrix (Fin n) (Fin n) ℝ) *ᵥ x)) :
    sig Q c = ENNReal.ofReal |(P : Matrix (Fin n) (Fin n) ℝ).det| • (sig Q₁ c).map (sphGL P hP c) := by
  rw [sig, sig, Measure.map_smul, nu_eq_smul_map_sphGL hc P hP, smul_comm]
  exact (continuous_sphGL P hP c).measurable.aemeasurable

end SphereGL

/-! ### Split frames at a vector -/

section Frame

open QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.SphereLeray
open QuadFormsKB.Tamagawa.Measure.OrbitalReal

variable {m : ℕ}

/-- **A split frame at `y`** for the real form `Q` in $m+1$ variables and the value `c`: a change of basis
$P\in GL_{m+1}(\mathbb R)$ (`P`) with $Pe_0 = y$ (`base`) and $Q\circ P = \langle c\rangle\perp Q'$ (`hess`, stated on
Hessians: $H_{\langle c\rangle\perp Q'} = P^{\mathsf T}H_QP$), where $Q'$ (`Q'`) is the form of $y^\perp$ in the basis
given by the last $m$ columns of $P$. Data with its defining properties. Fields: `P`, `Q'`, `hess`, `base`. -/
structure SplitFrame (Q : QuadForm ℝ (m + 1)) (c : ℝ) (y : Fin (m + 1) → ℝ) where
  /-- The change of basis. -/
  P : GL (Fin (m + 1)) ℝ
  /-- The form on the orthogonal complement of `y`. -/
  Q' : QuadForm ℝ m
  /-- $Q\circ P = \langle c\rangle\perp Q'$. -/
  hess : (splitForm c Q').hessian = (P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)ᵀ * Q.hessian * P
  /-- $Pe_0 = y$. -/
  base : (P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) *ᵥ e₀ = y

theorem e₀_eq_single : (e₀ : Fin (m + 1) → ℝ) = Pi.single 0 1 := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp [Fin.succ_ne_zero]

/-- **Split frames exist** at every vector `y` with $Q(y) = c\ne0$ (orthogonal splitting, `OrthFq.exists_split`). -/
theorem exists_splitFrame (Q : QuadForm ℝ (m + 1)) {c : ℝ} (hc : c ≠ 0) {y : Fin (m + 1) → ℝ}
    (hy : Q.eval y = c) : Nonempty (SplitFrame Q c y) := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra h
    push Not at h
    have hy0 : y = (0 : ℝ) • y := by rw [zero_smul]; exact funext h
    apply hc
    rw [← hy, hy0, eval_smul_real]
    ring
  obtain ⟨g, hg0, hsplit⟩ := QuadForm.exists_split Q y
    (by rw [hy]; exact (mul_ne_zero two_ne_zero hc).isUnit) i hi.isUnit
  have hcol0 : (fun l => g.val l 0) = y := by rw [← hg0, mulVec_single_one]; rfl
  have h00 : (Q.compMat g.val).coeff 0 0 = c := by
    rw [QuadForm.compMat_coeff]
    simp [hcol0, hy]
  have hQ := eq_splitForm_of (Q.compMat g.val) hsplit
  rw [h00] at hQ
  refine ⟨⟨g, tailForm (Q.compMat g.val), ?_, ?_⟩⟩
  · rw [← hQ, QuadForm.hessian_compMat]
  · rw [e₀_eq_single]; exact hg0

namespace SplitFrame

variable {Q : QuadForm ℝ (m + 1)} {c : ℝ} {y : Fin (m + 1) → ℝ} (F : SplitFrame Q c y)

theorem P_mul_P_inv : (F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) * ((F.P⁻¹ : GL (Fin (m + 1)) ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem P_inv_mul_P : ((F.P⁻¹ : GL (Fin (m + 1)) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) *
    (F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem P_inv_base : ((F.P⁻¹ : GL (Fin (m + 1)) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) *ᵥ y = e₀ := by
  have h : ((F.P⁻¹ : GL (Fin (m + 1)) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) *ᵥ
      ((F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) *ᵥ e₀) = e₀ := by
    rw [mulVec_mulVec, F.P_inv_mul_P, one_mulVec]
  rwa [F.base] at h

/-- $Q_1(x) = Q(Px)$ for the split form $Q_1 = \langle c\rangle\perp Q'$. -/
theorem eval_split (x : Fin (m + 1) → ℝ) :
    (splitForm c F.Q').eval x = Q.eval ((F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) *ᵥ x) :=
  eval_of_hessian_eq F.P F.hess x

theorem eval_split_inv (x : Fin (m + 1) → ℝ) :
    Q.eval x =
      (splitForm c F.Q').eval (((F.P⁻¹ : GL (Fin (m + 1)) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) *ᵥ x) := by
  rw [F.eval_split, mulVec_mulVec, F.P_mul_P_inv, one_mulVec]

include F in
theorem eval_y : Q.eval y = c := by
  have h := F.eval_split e₀
  rw [QuadFormsKB.Tamagawa.Measure.OrbitalReal.eval_splitForm_e₀, F.base] at h
  exact h.symm

theorem gramDetR_Q' (hQ : gramDetR Q ≠ 0) : gramDetR F.Q' ≠ 0 := by
  have h := gramDetR_of_hessian_eq F.P F.hess
  rw [gramDetR_splitForm] at h
  intro h0
  rw [h0, mul_zero] at h
  exact mul_ne_zero (pow_ne_zero 2 (det_GL_ne_zero F.P)) hQ h.symm

/-- Conjugation by $P$: $SO(\langle c\rangle\perp Q')(\mathbb R)\cong SO(Q)(\mathbb R)$, $g\mapsto PgP^{-1}$. -/
def conj : ArchSO (splitForm c F.Q') ≃* ArchSO Q := conjEquiv F.P F.hess

theorem mat_conj (g : ArchSO (splitForm c F.Q')) :
    ArchSOInst.mat Q (F.conj g) = (F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) * ArchSOInst.mat _ g *
      ((F.P⁻¹ : GL (Fin (m + 1)) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) := by
  show (((F.P * _ * F.P⁻¹ : GL (Fin (m + 1)) ℝ)) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = _
  rw [Units.val_mul, Units.val_mul]
  rfl

theorem continuous_conj : Continuous F.conj := continuous_conjEquiv F.P F.hess

theorem continuous_conj_symm : Continuous F.conj.symm :=
  ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

/-- The sphere map $x\mapsto Px$, $S_c(Q_1)\to S_c(Q)$. -/
def fwd : Sph (splitForm c F.Q') c → Sph Q c := sphGL F.P F.eval_split c

/-- The sphere map $x\mapsto P^{-1}x$, $S_c(Q)\to S_c(Q_1)$. -/
def bwd : Sph Q c → Sph (splitForm c F.Q') c := sphGL F.P⁻¹ F.eval_split_inv c

theorem bwd_fwd (x : Sph (splitForm c F.Q') c) : F.bwd (F.fwd x) = x :=
  Subtype.ext (by simp [bwd, fwd, sphGL, mulVec_mulVec])

theorem measurable_bwd : Measurable F.bwd := (continuous_sphGL _ _ c).measurable

theorem measurable_fwd : Measurable F.fwd := (continuous_sphGL _ _ c).measurable

variable (hc : c ≠ 0) (hm : 1 ≤ m) (hQ : gramDetR Q ≠ 0)

/-- The explicit section for the split form. -/
def sphSec : SphSection c F.Q' := sphSection hc hm (F.gramDetR_Q' hQ)

/-- **The section at `y`**: $S(x) = P\,s(P^{-1}x)\,P^{-1}$, so that $S(x)\,y = x$. -/
def sec (x : Sph Q c) : ArchSO Q := F.conj ((F.sphSec hc hm hQ).toFun (F.bwd x))

theorem sec_smul (x : Sph Q c) : F.sec hc hm hQ x • y = (x : Fin (m + 1) → ℝ) := by
  rw [sec, archSO_smul_def, mat_conj, ← mulVec_mulVec, ← mulVec_mulVec, F.P_inv_base,
    (F.sphSec hc hm hQ).spec]
  show (F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) *ᵥ (((F.P⁻¹ : GL (Fin (m + 1)) ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) *ᵥ (x : Fin (m + 1) → ℝ)) = x
  rw [mulVec_mulVec, F.P_mul_P_inv, one_mulVec]

theorem measurable_sec : Measurable (F.sec hc hm hQ) :=
  F.continuous_conj.measurable.comp ((F.sphSec hc hm hQ).measurable.comp F.measurable_bwd)

theorem sec_fwd (x : Sph (splitForm c F.Q') c) :
    F.sec hc hm hQ (F.fwd x) = F.conj ((F.sphSec hc hm hQ).toFun x) := by
  rw [sec, bwd_fwd]

include F in
/-- The orbit point $g^{-1}y\in S_c$. -/
def proj (g : ArchSO Q) : Sph Q c := ⟨g⁻¹ • y, by show Q.eval _ = c; rw [eval_archSO_smul, F.eval_y]⟩

include F in
theorem measurable_proj : Measurable F.proj := (measurable_archSO_inv_smul Q y).subtype_mk

/-- **The orbit coordinates at `y`**: $(x, h)\mapsto hS(x)^{-1}$, $S_c\times H_y\cong SO(Q)(\mathbb R)$. -/
def coord : OrbitCoord (stabilizer (ArchSO Q) y).subtype (Subtype.val : Sph Q c → Fin (m + 1) → ℝ) y :=
  orbitCoordOfSection Subtype.val Subtype.val_injective y (F.sec hc hm hQ) (F.measurable_sec hc hm hQ)
    (F.sec_smul hc hm hQ) F.proj F.measurable_proj fun _ => rfl

theorem conj_iota_mem (h : ArchSO F.Q') : F.conj (iota c F.Q' h) ∈ stabilizer (ArchSO Q) y := by
  rw [mem_stabilizer_iff, archSO_smul_def, mat_conj, ← mulVec_mulVec, ← mulVec_mulVec, F.P_inv_base,
    iota_mulVec_e₀, F.base]

/-- **The stabilizer of `y`** is $P\,\iota(SO(Q'))\,P^{-1}$: the homomorphism $SO(Q')(\mathbb R)\to H_y$. -/
def stabHom : ArchSO F.Q' →* stabilizer (ArchSO Q) y :=
  (F.conj.toMonoidHom.comp (iota c F.Q')).codRestrict _ F.conj_iota_mem

theorem coe_stabHom (h : ArchSO F.Q') : (F.stabHom h : ArchSO Q) = F.conj (iota c F.Q' h) := rfl

theorem measurable_stabHom : Measurable F.stabHom :=
  (F.continuous_conj.comp (continuous_iota c F.Q')).measurable.subtype_mk

include hc in
theorem stabHom_surjective : Function.Surjective F.stabHom := by
  rintro ⟨g, hg⟩
  have hfix : ArchSOInst.mat _ (F.conj.symm g) *ᵥ (e₀ : Fin (m + 1) → ℝ) = e₀ := by
    have h1 : ArchSOInst.mat Q (F.conj (F.conj.symm g)) *ᵥ y = y := by
      rw [MulEquiv.apply_symm_apply]; exact mem_stabilizer_iff.mp hg
    rw [mat_conj] at h1
    have hM : ArchSOInst.mat _ (F.conj.symm g) * ((F.P⁻¹ : GL (Fin (m + 1)) ℝ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = ((F.P⁻¹ : GL (Fin (m + 1)) ℝ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) * ((F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) *
        ArchSOInst.mat _ (F.conj.symm g) * ((F.P⁻¹ : GL (Fin (m + 1)) ℝ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, F.P_inv_mul_P, Matrix.one_mul]
    rw [← F.P_inv_base, mulVec_mulVec, hM, ← mulVec_mulVec, h1]
  obtain ⟨h, hh⟩ := exists_iota_eq_of_mulVec_e₀ hc (F.conj.symm g) hfix
  refine ⟨h, Subtype.ext ?_⟩
  rw [coe_stabHom, hh, MulEquiv.apply_symm_apply]

theorem isHaarMeasure_map_conj :
    ((lerayMeasure (splitForm c F.Q') (gramDetR_splitForm_ne_zero hc (F.gramDetR_Q' hQ))).map
      F.conj).IsHaarMeasure := by
  haveI := isHaarMeasure_lerayMeasure (gramDetR_splitForm_ne_zero hc (F.gramDetR_Q' hQ))
  exact MulEquiv.isHaarMeasure_map _ F.conj F.continuous_conj F.continuous_conj_symm

/-- **The Haar constant of the conjugation** $\kappa_P$: $(g\mapsto PgP^{-1})_*\mu_{Q_1} = \kappa_P\,\mu_Q$
(`map_conj_lerayMeasure`; uniqueness of Haar measure). -/
def haarConst : ℝ≥0 := by
  haveI := isHaarMeasure_lerayMeasure hQ
  haveI := F.isHaarMeasure_map_conj hc hQ
  exact haarScalarFactor ((lerayMeasure (splitForm c F.Q') (gramDetR_splitForm_ne_zero hc (F.gramDetR_Q' hQ))).map
    F.conj) (lerayMeasure Q hQ)

theorem map_conj_lerayMeasure :
    (lerayMeasure (splitForm c F.Q') (gramDetR_splitForm_ne_zero hc (F.gramDetR_Q' hQ))).map F.conj =
      F.haarConst hc hQ • lerayMeasure Q hQ := by
  haveI := F.isHaarMeasure_map_conj hc hQ
  haveI := isHaarMeasure_lerayMeasure hQ
  exact isMulLeftInvariant_eq_smul _ _

theorem haarConst_pos : 0 < F.haarConst hc hQ := by
  haveI := F.isHaarMeasure_map_conj hc hQ
  haveI := isHaarMeasure_lerayMeasure hQ
  exact haarScalarFactor_pos_of_isHaarMeasure _ _

/-- **The measure on the stabilizer $H_y$**: $\mu_{H_y} = (\kappa_P\,|\det P|)^{-1}\cdot
(h\mapsto P\iota(h)P^{-1})_*\mu_{Q'}$, the Haar measure for which $\mu_Q = |2c|^{-m}\,\sigma_c\otimes\mu_{H_y}$
(`lerayMeasure_eq_map_coord`). -/
def stabMeasure : Measure (stabilizer (ArchSO Q) y) :=
  (((F.haarConst hc hQ : ℝ≥0∞))⁻¹ * (ENNReal.ofReal |(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det|)⁻¹) •
    (lerayMeasure F.Q' (F.gramDetR_Q' hQ)).map F.stabHom

theorem coord_apply (x : Sph Q c) (h : stabilizer (ArchSO Q) y) :
    (F.coord hc hm hQ).coord (x, h) = (h : ArchSO Q) * (F.sec hc hm hQ x)⁻¹ := rfl

/-- **The real-place fibration at `y`** (any signature; Weil 1982, Lemma 2.4.1 / Thm 2.4.3 at an arbitrary point of
the quadric): for every split frame at `y` (so $Q(y) = c$),
$$\mu_Q = |2c|^{-m}\cdot\mathrm{coord}_*(\sigma_c\otimes\mu_{H_y}),\qquad\mathrm{coord}(x, h) = hS(x)^{-1}.$$ -/
theorem lerayMeasure_eq_map_coord :
    lerayMeasure Q hQ = ENNReal.ofReal ((|2 * c| ^ m)⁻¹) •
      ((sig Q c).prod (F.stabMeasure hc hQ)).map (F.coord hc hm hQ).coord := by
  have hQ' := F.gramDetR_Q' hQ
  have hQ1 := gramDetR_splitForm_ne_zero hc hQ'
  set k := ENNReal.ofReal ((|2 * c| ^ m)⁻¹) with hk
  set d := ENNReal.ofReal |(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det| with hd
  set κ : ℝ≥0∞ := (F.haarConst hc hQ : ℝ≥0∞) with hκ
  set μ' := lerayMeasure F.Q' hQ'
  set σ₁ := sig (splitForm c F.Q') c
  set μ₁ := lerayMeasure (splitForm c F.Q') hQ1
  set s := F.sphSec hc hm hQ
  haveI := sigmaFinite_sig (Q := splitForm c F.Q') hc
  haveI := sigmaFinite_sig (Q := Q) hc
  haveI := isHaarMeasure_lerayMeasure hQ'
  haveI := isHaarMeasure_lerayMeasure hQ1
  haveI := isHaarMeasure_lerayMeasure hQ
  haveI := isMulRightInvariant_lerayMeasure hQ'
  haveI := isMulRightInvariant_lerayMeasure hQ1
  have hd0 : d ≠ 0 := ENNReal.ofReal_pos.mpr (abs_pos.mpr (det_GL_ne_zero F.P)) |>.ne'
  have hκ0 : κ ≠ 0 := ENNReal.coe_ne_zero.mpr (F.haarConst_pos hc hQ).ne'
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos (abs_pos.mpr
    (mul_ne_zero two_ne_zero hc)) m))).ne'
  -- the two images: σ_Q and μ_{H_y}
  have hprod : (sig Q c).prod (F.stabMeasure hc hQ) =
      (d * (κ⁻¹ * d⁻¹)) • (σ₁.prod μ').map (Prod.map F.fwd F.stabHom) := by
    have hσ : sig Q c = d • σ₁.map F.fwd := sig_eq_smul_map_sphGL hc F.P F.eval_split
    rw [hσ, stabMeasure, Measure.prod_smul_left,
      Measure.prod_smul_right, smul_smul, map_prod_map _ _ F.measurable_fwd F.measurable_stabHom]
  -- the composite map
  have hcomp : (F.coord hc hm hQ).coord ∘ Prod.map F.fwd F.stabHom =
      F.conj ∘ (fun g => g⁻¹) ∘ orb s ∘ Prod.map id (fun h => h⁻¹) := by
    funext p
    obtain ⟨x, h⟩ := p
    simp only [Function.comp_apply, Prod.map_apply, id]
    rw [coord_apply, coe_stabHom, sec_fwd, orb, _root_.mul_inv_rev, map_inv, inv_inv, map_mul, map_inv]
  have hA : (σ₁.prod μ').map (Prod.map id fun h => h⁻¹) = σ₁.prod μ' := by
    rw [← map_prod_map _ _ measurable_id measurable_inv, Measure.map_id]
    congr 1
    exact QuadFormsKB.Tamagawa.Measure.ConeReal.inv_eq_self_of_unimodular μ'
  have hinv₁ : μ₁.map (fun g => g⁻¹) = μ₁ := QuadFormsKB.Tamagawa.Measure.ConeReal.inv_eq_self_of_unimodular μ₁
  have horb : μ₁ = k • (σ₁.prod μ').map (orb s) := lerayMeasure_orbital hc hQ' s
  have hmc := (F.coord hc hm hQ).coord.measurable
  have hmP : Measurable (Prod.map F.fwd F.stabHom) := F.measurable_fwd.prodMap F.measurable_stabHom
  have hmorb := measurable_orb s
  have hmconj := F.continuous_conj.measurable
  have hmP' : Measurable (Prod.map (id : Sph (splitForm c F.Q') c → _) fun h : ArchSO F.Q' => h⁻¹) :=
    measurable_id.prodMap measurable_inv
  symm
  calc k • ((sig Q c).prod (F.stabMeasure hc hQ)).map (F.coord hc hm hQ).coord
      = (k * (d * (κ⁻¹ * d⁻¹))) • (σ₁.prod μ').map
          ((F.coord hc hm hQ).coord ∘ Prod.map F.fwd F.stabHom) := by
        rw [hprod, Measure.map_smul _ hmc.aemeasurable, Measure.map_map hmc hmP, smul_smul]
    _ = (k * (d * (κ⁻¹ * d⁻¹))) • (((((σ₁.prod μ').map (Prod.map id fun h => h⁻¹)).map (orb s)).map
          (fun g => g⁻¹)).map F.conj) := by
        rw [hcomp, Measure.map_map hmorb hmP', Measure.map_map measurable_inv (hmorb.comp hmP'),
          Measure.map_map hmconj (measurable_inv.comp (hmorb.comp hmP'))]
    _ = (d * (κ⁻¹ * d⁻¹)) • (((k • (σ₁.prod μ').map (orb s)).map (fun g => g⁻¹)).map F.conj) := by
        rw [hA, Measure.map_smul _ measurable_inv.aemeasurable, Measure.map_smul _ hmconj.aemeasurable, smul_smul,
          mul_comm k]
    _ = (d * (κ⁻¹ * d⁻¹)) • (κ • lerayMeasure Q hQ) := by
        rw [← horb, hinv₁, map_conj_lerayMeasure]
        rfl
    _ = lerayMeasure Q hQ := by
        have h1 : d * (κ⁻¹ * d⁻¹) * κ = 1 := by
          calc d * (κ⁻¹ * d⁻¹) * κ = (d * d⁻¹) * (κ⁻¹ * κ) := by ring
            _ = 1 := by
              rw [ENNReal.mul_inv_cancel hd0 ENNReal.ofReal_ne_top, ENNReal.inv_mul_cancel hκ0 ENNReal.coe_ne_top,
                one_mul]
        rw [smul_smul, h1, one_smul]

theorem iota_injective' : Function.Injective (iota c F.Q') := by
  intro a b h
  have h1 := congrArg (ArchSOInst.mat _) h
  rw [mat_iota, mat_iota] at h1
  exact Subtype.ext (Units.ext (cornerMat_injective_right h1))

theorem stabHom_injective : Function.Injective F.stabHom := by
  intro a b h
  have h1 : F.conj (iota c F.Q' a) = F.conj (iota c F.Q' b) := by
    rw [← coe_stabHom, ← coe_stabHom, h]
  exact F.iota_injective' (F.conj.injective h1)

theorem continuous_stabHom : Continuous F.stabHom :=
  (F.continuous_conj.comp (continuous_iota c F.Q')).subtype_mk _

/-- $\mu_{H_y}$ is σ-finite: it is finite on the images of a compact exhaustion of $SO(Q')(\mathbb R)$. -/
theorem sigmaFinite_stabMeasure : SigmaFinite (F.stabMeasure hc hQ) := by
  haveI := isHaarMeasure_lerayMeasure (F.gramDetR_Q' hQ)
  set K := compactCovering (ArchSO F.Q')
  have hK : ∀ k, IsCompact (K k) := isCompact_compactCovering _
  have hS : ∀ k, MeasurableSet (F.stabHom '' K k) := fun k =>
    ((hK k).image F.continuous_stabHom).isClosed.measurableSet
  have hd0 : ENNReal.ofReal |(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det| ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (abs_pos.mpr (det_GL_ne_zero F.P))).ne'
  have hκ0 : ((F.haarConst hc hQ : ℝ≥0) : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (F.haarConst_pos hc hQ).ne'
  have hfin : ∀ k, F.stabMeasure hc hQ (F.stabHom '' K k) < ⊤ := by
    intro k
    rw [stabMeasure, Measure.smul_apply, Measure.map_apply F.measurable_stabHom (hS k),
      F.stabHom_injective.preimage_image, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hκ0))
      (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hd0))) (hK k).measure_lt_top
  have hspan : ⋃ k, F.stabHom '' K k = Set.univ := by
    rw [← Set.image_iUnion, iUnion_compactCovering, Set.image_univ, (F.stabHom_surjective hc).range_eq]
  exact ⟨⟨⟨fun k => F.stabHom '' K k, fun _ => trivial, hfin, hspan⟩⟩⟩

theorem isMulLeftInvariant_stabMeasure : (F.stabMeasure hc hQ).IsMulLeftInvariant := by
  haveI := isHaarMeasure_lerayMeasure (F.gramDetR_Q' hQ)
  haveI := measurableMul_subgroup (stabilizer (ArchSO Q) y)
  haveI := isMulLeftInvariant_map (μ := lerayMeasure F.Q' (F.gramDetR_Q' hQ)) F.stabHom.toMulHom
    F.measurable_stabHom (F.stabHom_surjective hc)
  unfold stabMeasure
  infer_instance

end SplitFrame

/-! ### Packaging: the archimedean fibration at a real place -/

variable (Q : QuadForm ℝ (m + 1)) (hQ : gramDetR Q ≠ 0) {c : ℝ} (hc : c ≠ 0) (hm : 1 ≤ m)

/-- A chosen split frame at each point of the quadric $S_c$. -/
def frameAt {y : Fin (m + 1) → ℝ} (hy : y ∈ sph Q c) : SplitFrame Q c y := (exists_splitFrame Q hc hy).some

/-- **The measure $\mu_{H_y}$ on the stabilizer of `y`** (for $y\notin S_c$ it is $0$; it is never used there). -/
def realStabMeasure (y : Fin (m + 1) → ℝ) : Measure (stabilizer (ArchSO Q) y) :=
  haveI := Classical.propDecidable (y ∈ sph Q c)
  if hy : y ∈ sph Q c then (frameAt Q hc hy).stabMeasure hc hQ else 0

/-- **The archimedean fibration at a real place, any signature** (Weil 1982, Lemma 2.4.1 / Thm 2.4.3): for a
nondegenerate real form $Q$ in $m+1\ge2$ variables and $c\ne0$, the orbit maps $g\mapsto g^{-1}y$ ($y\in S_c$) of
$SO(Q)(\mathbb R)$ are fibred with
$$\mu_Q = |2c|^{-m}\cdot\mathrm{coord}_*(\sigma_c\otimes\mu_{H_y})$$
for every $y\in S_c$, one constant for all $y$. Built from `lerayMeasure_eq_map_coord` at a chosen split frame. -/
@[kb "weil1982" "§2.4 Lemma 2.4.1, Theorem 2.4.3, p. 25 (matching measures on G, H, G/H) [unverified page]"]
def realArchFibration :
    ArchFibration (lerayMeasure Q hQ) (sph Q c) (sig Q c) Subtype.val (ENNReal.ofReal ((|2 * c| ^ m)⁻¹)) where
  μH := realStabMeasure Q hQ hc
  coord y hy := (frameAt Q hc hy).coord hc hm hQ
  sigmaFinite y := by
    unfold realStabMeasure
    split_ifs with hy
    · exact (frameAt Q hc hy).sigmaFinite_stabMeasure hc hQ
    · infer_instance
  leftInv y := by
    unfold realStabMeasure
    split_ifs with hy
    · exact (frameAt Q hc hy).isMulLeftInvariant_stabMeasure hc hQ
    · exact ⟨fun g => by simp⟩
  fib y hy := by
    rw [realStabMeasure, dite_eq_left_of_eq_true (eq_true hy)]
    exact (frameAt Q hc hy).lerayMeasure_eq_map_coord hc hm hQ

end Frame

end QuadFormsKB.Tamagawa.Indefinite
