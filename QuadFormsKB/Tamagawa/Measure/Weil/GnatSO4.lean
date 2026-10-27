/-
# $SO(V) \cong G^\natural/\mathbb G_m$ for quaternary $V$, both discriminants at once

The algebra for Weil's $m = 4$ step, over **every field $K$
with $2 \ne 0$** and **every** $d \in K^\times$ (square or not).

**Setting.** $E = K[\delta]/(\delta^2 - d)$ = `QuadraticAlgebra K d 0` (`QE d`), with conjugation $\sigma$ (Mathlib's `star`);
$D = (a,b)_K$ = `ℍ[K,a,b]`, $D_E = (a,b)_E$ = `ℍ[E,a,b]` (`DE a b d`); `sig` is $\sigma$ on $D_E$ (coordinatewise), `star`
the quaternion conjugation, `nrdE` the $E$-valued reduced norm. $V_0 = \{x \in D_E : \sigma(x) = \bar x\} = K \oplus \delta D^0$
(`InV0`, `inV0_iff_exists_emb`), with coordinates `emb : K⁴ → V_0`, $v \mapsto v_0 + \delta(v_1 i + v_2 j + v_3 k)$, and
$\operatorname{nrd}|_{V_0} = \langle 1, -ad, -bd, abd\rangle$ = `V0Form a b d` (`nrdE_emb`).

**Main results.**
* `Gnat a b d` $= G^\natural = \{\alpha \in D_E^\times : \operatorname{nrd}\alpha \in K^\times\}$; `phiLin α` $= \varphi_\alpha$,
  $x \mapsto \operatorname{nrd}(\alpha)^{-1}\alpha x\sigma(\bar\alpha)$; isometry (`Q4_phiLin`), multiplicative (`phiLin_mul`).
* Reflections $s_u(x) = -u\bar x u/\operatorname{nrd}u$ (`emb_refl4`), $s_us_w = \varphi_{u\bar w}$ (`phiLin_reflUnit`),
  $\det s_u = -1$ (`det_refl4`), $\det\varphi_\alpha = 1$ (`det_phiLin`).
* `phiSO : G^♮ →* SO(V0Form)`, **surjective** (`phiSO_surjective`: two reflections move $g(1)$ to $1$, then `exists_eq_smul_conjLin` on $1^\perp = \delta D^0$), **kernel $K^\times$** (`ker_phiSO`, via `ker_conjSO`),
  so **`gnatQuotEquivSO`**: $G^\natural(K)/K^\times \cong SO(\langle 1,-ad,-bd,abd\rangle)(K)$.
* Item 1: `exists_isometric_smul_V0Form` (every nondegenerate quaternary $V$ is $c\cdot$`V0Form a b d`, $d \equiv \operatorname{disc}V$)
  and **`nonempty_SO_mulEquiv_gnat`**: the same $a, b, d \in k^\times$ give $SO(V)(K) \cong G^\natural(K)/K^\times$ for every
  field $K \supseteq k$ (characteristic $0$).
* Item 4 (square case $d = t^2$): `pairEquiv` ($D_E \cong D \times D$), `evQ_emb_bijective` + `nrd_evQ_emb`
  ($V_0 \cong (D, \operatorname{nrd})$), `mem_Gnat_iff_nrd_eq` ($G^\natural = \{(\alpha,\beta) : \operatorname{nrd}\alpha = \operatorname{nrd}\beta\}$),
  `evQ_phiLin` ($\varphi = (x \mapsto \alpha x\beta^{-1})$).

Sources: Weil 1982, §3.7, pp. 64–65 [unverified] (Weil treats the square case through $(R^{(1)}\times R^{(1)})/\pm1$ and the
non-square case through a torus; the uniform $G^\natural$ is the route taken here); Knus–Merkurjev–Rost–Tignol, *The Book of
Involutions* (1998), §15 [unverified]; Voight 2021, §4.5 [unverified].
-/
import QuadFormsKB.Tamagawa.QuaternionSO3
import QuadFormsKB.Literature.LocalGlobal.PadicClassification

open Quaternion Matrix
open scoped QuadraticAlgebra

noncomputable section

namespace QuadFormsKB.Quat.Gnat

variable {K : Type*} [Field K]

/-- `E = K[δ]/(δ² − d)`. -/
abbrev QE (d : K) := QuadraticAlgebra K d 0

/-- `D_E = (a,b)_E`. -/
abbrev DE (a b d : K) := ℍ[QE d, algebraMap K (QE d) a, algebraMap K (QE d) b]

variable {a b d : K}

@[simp] theorem star_algebraMap_QE (r : K) : star (algebraMap K (QE d) r) = algebraMap K (QE d) r := by
  ext <;> simp

/-- σ on `D_E`, coordinatewise conjugation of `E`. -/
def sig (x : DE a b d) : DE a b d := ⟨star x.re, star x.imI, star x.imJ, star x.imK⟩

@[simp] theorem re_sig (x : DE a b d) : (sig x).re = star x.re := rfl
@[simp] theorem imI_sig (x : DE a b d) : (sig x).imI = star x.imI := rfl
@[simp] theorem imJ_sig (x : DE a b d) : (sig x).imJ = star x.imJ := rfl
@[simp] theorem imK_sig (x : DE a b d) : (sig x).imK = star x.imK := rfl

theorem sig_mul (x y : DE a b d) : sig (x * y) = sig x * sig y := by
  ext : 1 <;> simp [star_mul', star_add, star_sub]

theorem sig_star (x : DE a b d) : sig (star x) = star (sig x) := by
  ext <;> simp

theorem sig_sig (x : DE a b d) : sig (sig x) = x := by ext <;> simp

theorem sig_add (x y : DE a b d) : sig (x + y) = sig x + sig y := by ext <;> simp [star_add]

/-- The reduced norm on `D_E`, with values in `E`. -/
def nrdE (x : DE a b d) : QE d :=
  x.re ^ 2 - algebraMap K (QE d) a * x.imI ^ 2 - algebraMap K (QE d) b * x.imJ ^ 2 +
    algebraMap K (QE d) a * algebraMap K (QE d) b * x.imK ^ 2

theorem mul_star_eq_nrdE (x : DE a b d) : x * star x = ((nrdE x : QE d) : DE a b d) := by
  ext : 1 <;> simp only [QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe, QuaternionAlgebra.imJ_coe,
    QuaternionAlgebra.imK_coe] <;> simp [nrdE] <;> ring

theorem star_mul_eq_nrdE (x : DE a b d) : star x * x = ((nrdE x : QE d) : DE a b d) := by
  ext : 1 <;> simp only [QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe, QuaternionAlgebra.imJ_coe,
    QuaternionAlgebra.imK_coe] <;> simp [nrdE] <;> ring

theorem nrdE_mul (x y : DE a b d) : nrdE (x * y) = nrdE x * nrdE y := by
  simp only [nrdE, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]
  ring

theorem nrdE_sig (x : DE a b d) : nrdE (sig x) = star (nrdE x) := by
  simp [nrdE, star_mul', star_add, star_sub, star_pow]

theorem nrdE_star (x : DE a b d) : nrdE (star x) = nrdE x := by
  simp [nrdE]

end QuadFormsKB.Quat.Gnat

namespace QuadFormsKB.Quat.Gnat

variable {K : Type*} [Field K] {a b d : K}

theorem nrdE_smul (c : K) (x : DE a b d) : nrdE (c • x) = algebraMap K (QE d) (c ^ 2) * nrdE x := by
  simp only [nrdE, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul]
  simp only [Algebra.smul_def, map_pow]
  ring

theorem coe_algebraMap_mul (c : K) (x : DE a b d) :
    ((algebraMap K (QE d) c : QE d) : DE a b d) * x = c • x := by
  ext <;> simp

theorem mul_coe_algebraMap (c : K) (x : DE a b d) :
    x * ((algebraMap K (QE d) c : QE d) : DE a b d) = c • x := by
  ext <;> simp [mul_comm]

/-- The coordinates `K⁴ → V_0`: `v ↦ v₀ + δ(v₁ i + v₂ j + v₃ k)`. -/
def emb (v : Fin 4 → K) : DE a b d := ⟨⟨v 0, 0⟩, ⟨0, v 1⟩, ⟨0, v 2⟩, ⟨0, v 3⟩⟩

/-- Coordinates of an element of `V_0`. -/
def coords (x : DE a b d) : Fin 4 → K := ![x.re.re, x.imI.im, x.imJ.im, x.imK.im]

/-- `V_0 = {x ∈ D_E : σ(x) = x̄}`. -/
def InV0 (x : DE a b d) : Prop := sig x = star x

theorem coords_emb (v : Fin 4 → K) : coords (emb v : DE a b d) = v := by
  funext i; fin_cases i <;> rfl

theorem inV0_emb (v : Fin 4 → K) : InV0 (emb v : DE a b d) := by
  ext <;> simp [emb]

theorem inV0_iff (h2 : (2 : K) ≠ 0) (x : DE a b d) :
    InV0 x ↔ x.re.im = 0 ∧ x.imI.re = 0 ∧ x.imJ.re = 0 ∧ x.imK.re = 0 := by
  constructor
  · intro h
    have e1 := congrArg (fun y : DE a b d => y.re.im) h
    have e2 := congrArg (fun y : DE a b d => y.imI.re) h
    have e3 := congrArg (fun y : DE a b d => y.imJ.re) h
    have e4 := congrArg (fun y : DE a b d => y.imK.re) h
    simp at e1 e2 e3 e4
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : 2 * x.re.im = 0 := by linear_combination -e1
      exact (mul_eq_zero.1 this).resolve_left h2
    · have : 2 * x.imI.re = 0 := by linear_combination e2
      exact (mul_eq_zero.1 this).resolve_left h2
    · have : 2 * x.imJ.re = 0 := by linear_combination e3
      exact (mul_eq_zero.1 this).resolve_left h2
    · have : 2 * x.imK.re = 0 := by linear_combination e4
      exact (mul_eq_zero.1 this).resolve_left h2
  · rintro ⟨h0, h1, h2', h3⟩
    ext <;> simp [h0, h1, h2', h3]

theorem emb_coords (h2 : (2 : K) ≠ 0) {x : DE a b d} (hx : InV0 x) : emb (coords x) = x := by
  obtain ⟨h0, h1, h2', h3⟩ := (inV0_iff h2 x).1 hx
  ext <;> simp [emb, coords, h0, h1, h2', h3]

/-- **`V_0 = K ⊕ δ D⁰`:** `x ∈ V_0` iff `x = v₀ + δ(v₁ i + v₂ j + v₃ k)` for some `v ∈ K⁴`. -/
theorem inV0_iff_exists_emb (h2 : (2 : K) ≠ 0) (x : DE a b d) : InV0 x ↔ ∃ v, x = emb v :=
  ⟨fun hx => ⟨coords x, (emb_coords h2 hx).symm⟩, by rintro ⟨v, rfl⟩; exact inV0_emb v⟩

theorem emb_add (v w : Fin 4 → K) : (emb (v + w) : DE a b d) = emb v + emb w := by
  ext <;> simp [emb]

theorem emb_smul (c : K) (v : Fin 4 → K) : (emb (c • v) : DE a b d) = c • emb v := by
  ext <;> simp [emb]

theorem coords_add (x y : DE a b d) : coords (x + y) = coords x + coords y := by
  funext i; fin_cases i <;> simp [coords]

theorem coords_smul (c : K) (x : DE a b d) : coords (c • x) = c • coords x := by
  funext i; fin_cases i <;> simp [coords]

theorem emb_injective : Function.Injective (emb : (Fin 4 → K) → DE a b d) := by
  intro v w h
  rw [← coords_emb (a := a) (b := b) (d := d) v, h, coords_emb]

/-! ### The quaternary form on `V_0` -/

variable (a b d) in
/-- The form `⟨1, −ad, −bd, abd⟩` = `nrd|_{V_0}`, explicitly. -/
def Q4 (v : Fin 4 → K) : K :=
  v 0 ^ 2 - a * d * v 1 ^ 2 - b * d * v 2 ^ 2 + a * b * d * v 3 ^ 2

variable (a b d) in
/-- The polar form of `Q4`. -/
def B4 (v w : Fin 4 → K) : K :=
  2 * (v 0 * w 0 - a * d * v 1 * w 1 - b * d * v 2 * w 2 + a * b * d * v 3 * w 3)

theorem nrdE_emb (v : Fin 4 → K) : nrdE (emb v : DE a b d) = algebraMap K (QE d) (Q4 a b d v) := by
  ext <;> simp [nrdE, emb, Q4, sq] <;> ring

theorem emb_mul_star_add (v w : Fin 4 → K) :
    (emb v : DE a b d) * star (emb w) + emb w * star (emb v) =
      ((algebraMap K (QE d) (B4 a b d v w) : QE d) : DE a b d) := by
  ext : 1 <;> simp only [QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe, QuaternionAlgebra.imJ_coe,
    QuaternionAlgebra.imK_coe, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
    QuaternionAlgebra.imK_add, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul] <;> ext <;> simp [emb, B4] <;> ring

theorem Q4_add (v w : Fin 4 → K) : Q4 a b d (v + w) = Q4 a b d v + Q4 a b d w + B4 a b d v w := by
  simp only [Q4, B4, Pi.add_apply]; ring

theorem Q4_smul (c : K) (v : Fin 4 → K) : Q4 a b d (c • v) = c ^ 2 * Q4 a b d v := by
  simp [Q4]; ring

theorem B4_self (v : Fin 4 → K) : B4 a b d v v = 2 * Q4 a b d v := by
  simp only [B4, Q4]; ring

theorem B4_comm (v w : Fin 4 → K) : B4 a b d v w = B4 a b d w v := by
  simp only [B4]; ring

end QuadFormsKB.Quat.Gnat

namespace QuadFormsKB.Quat.Gnat

variable {K : Type*} [Field K] {a b d : K}

/-! ### The group `G^♮` -/

theorem im_mul_of_im_eq_zero {z w : QE d} (hz : z.im = 0) (hw : w.im = 0) : (z * w).im = 0 := by
  simp [hz, hw]

theorem re_mul_of_im_eq_zero {z w : QE d} (hz : z.im = 0) : (z * w).re = z.re * w.re := by
  simp [hz]

theorem eq_algebraMap_of_im_eq_zero {z : QE d} (hz : z.im = 0) : z = algebraMap K (QE d) z.re := by
  ext <;> simp [hz]

@[simp] theorem nrdE_one : nrdE (1 : DE a b d) = 1 := by simp [nrdE]

variable (a b d) in
/-- **The group `G^♮ = {α ∈ D_E^× : nrd α ∈ K^×}`.** The condition `nrd α ∈ K` is `(nrd α).im = 0`. -/
@[kb "weil1982" "§3.7, p. 64 [unverified]"]
def Gnat : Subgroup (DE a b d)ˣ where
  carrier := {α | (nrdE (α : DE a b d)).im = 0}
  mul_mem' {α β} hα hβ := by
    simp only [Set.mem_setOf_eq, Units.val_mul, nrdE_mul] at *
    exact im_mul_of_im_eq_zero hα hβ
  one_mem' := by simp
  inv_mem' {α} hα := by
    simp only [Set.mem_setOf_eq] at *
    have h1 : nrdE (α : DE a b d) * nrdE ((α⁻¹ : (DE a b d)ˣ) : DE a b d) = 1 := by
      rw [← nrdE_mul, Units.mul_inv, nrdE_one]
    have hre := congrArg QuadraticAlgebra.re h1
    have him := congrArg QuadraticAlgebra.im h1
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, hα, QuadraticAlgebra.re_one,
      QuadraticAlgebra.im_one] at hre him
    have hre' : (nrdE (α : DE a b d)).re * (nrdE ((α⁻¹ : (DE a b d)ˣ) : DE a b d)).re = 1 := by
      linear_combination hre
    have him' : (nrdE (α : DE a b d)).re * (nrdE ((α⁻¹ : (DE a b d)ˣ) : DE a b d)).im = 0 := by
      linear_combination him
    exact (mul_eq_zero.1 him').resolve_left (left_ne_zero_of_mul_eq_one hre')

theorem mem_Gnat {α : (DE a b d)ˣ} : α ∈ Gnat a b d ↔ (nrdE (α : DE a b d)).im = 0 := Iff.rfl

/-- The reduced norm of `α ∈ G^♮`, as an element of `K`. -/
def nrdK (α : DE a b d) : K := (nrdE α).re

theorem nrdE_eq_nrdK {α : (DE a b d)ˣ} (hα : α ∈ Gnat a b d) :
    nrdE (α : DE a b d) = algebraMap K (QE d) (nrdK (α : DE a b d)) :=
  eq_algebraMap_of_im_eq_zero hα

theorem nrdK_ne_zero {α : (DE a b d)ˣ} (hα : α ∈ Gnat a b d) : nrdK (α : DE a b d) ≠ 0 := by
  intro h
  have h1 : nrdE (α : DE a b d) * nrdE ((α⁻¹ : (DE a b d)ˣ) : DE a b d) = 1 := by
    rw [← nrdE_mul, Units.mul_inv, nrdE_one]
  rw [nrdE_eq_nrdK hα, h, map_zero, zero_mul] at h1
  exact zero_ne_one h1

theorem nrdK_mul {α β : (DE a b d)ˣ} (hα : α ∈ Gnat a b d) :
    nrdK ((α * β : (DE a b d)ˣ) : DE a b d) = nrdK (α : DE a b d) * nrdK (β : DE a b d) := by
  simp only [nrdK, Units.val_mul, nrdE_mul]
  exact re_mul_of_im_eq_zero hα

/-! ### The action `φ_α(x) = nrd(α)⁻¹ α x σ(ᾱ)` -/

theorem inV0_conj (α x : DE a b d) (hx : InV0 x) : InV0 (α * x * sig (star α)) := by
  unfold InV0 at *
  rw [sig_mul, sig_mul, sig_sig, hx, star_mul, star_mul, sig_star, star_star, mul_assoc]

/-- `φ_α` in coordinates (a `K`-linear map of `K⁴`). -/
def phiLin (α : DE a b d) : (Fin 4 → K) →ₗ[K] (Fin 4 → K) where
  toFun v := (nrdK α)⁻¹ • coords (α * emb v * sig (star α))
  map_add' v w := by
    rw [emb_add, mul_add, add_mul, coords_add, smul_add]
  map_smul' c v := by
    rw [emb_smul, mul_smul_comm, smul_mul_assoc, coords_smul, smul_comm]
    rfl

theorem phiLin_apply (α : DE a b d) (v : Fin 4 → K) :
    phiLin α v = (nrdK α)⁻¹ • coords (α * emb v * sig (star α)) := rfl

theorem emb_phiLin (h2 : (2 : K) ≠ 0) (α : DE a b d) (v : Fin 4 → K) :
    (emb (phiLin α v) : DE a b d) = (nrdK α)⁻¹ • (α * emb v * sig (star α)) := by
  rw [phiLin_apply, emb_smul, emb_coords h2 (inV0_conj α _ (inV0_emb v))]

/-- **`φ_α` is an isometry of `(V_0, nrd)`** for `α ∈ G^♮`. -/
theorem Q4_phiLin (h2 : (2 : K) ≠ 0) {α : (DE a b d)ˣ} (hα : α ∈ Gnat a b d) (v : Fin 4 → K) :
    Q4 a b d (phiLin (α : DE a b d) v) = Q4 a b d v := by
  apply (algebraMap K (QE d)).injective
  rw [← nrdE_emb, ← nrdE_emb, emb_phiLin h2, nrdE_smul, nrdE_mul, nrdE_mul, nrdE_sig, nrdE_star,
    nrdE_eq_nrdK hα, star_algebraMap_QE, nrdE_emb]
  simp only [← map_mul]
  congr 1
  have := nrdK_ne_zero hα
  field_simp

theorem phiLin_mul (h2 : (2 : K) ≠ 0) {α β : (DE a b d)ˣ} (hα : α ∈ Gnat a b d) :
    phiLin ((α * β : (DE a b d)ˣ) : DE a b d) = phiLin (α : DE a b d) * phiLin (β : DE a b d) := by
  refine LinearMap.ext fun v => ?_
  apply emb_injective (a := a) (b := b) (d := d)
  rw [Module.End.mul_apply, emb_phiLin h2, emb_phiLin h2, emb_phiLin h2, nrdK_mul hα, Units.val_mul,
    star_mul, sig_mul, mul_smul_comm, smul_mul_assoc, smul_smul, mul_inv]
  congr 1
  noncomm_ring

theorem phiLin_one : phiLin (1 : DE a b d) = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  rw [phiLin_apply, star_one, show sig (1 : DE a b d) = 1 by ext <;> simp [sig], mul_one, one_mul,
    coords_emb]
  simp [nrdK, QuadraticAlgebra.re_one]

end QuadFormsKB.Quat.Gnat

namespace QuadFormsKB.Quat.Gnat

variable {K : Type*} [Field K] {a b d : K}

/-! ### Units from the reduced norm -/

theorem star_smulK (c : K) (y : DE a b d) : star (c • y) = c • star y := by
  ext <;> simp

theorem emb_sub (v w : Fin 4 → K) : (emb (v - w) : DE a b d) = emb v - emb w := by
  ext <;> simp [emb]

theorem emb_neg (v : Fin 4 → K) : (emb (-v) : DE a b d) = -emb v := by
  ext <;> simp [emb]

theorem coe_algebraMap_eq_smul_one (c : K) :
    ((algebraMap K (QE d) c : QE d) : DE a b d) = c • (1 : DE a b d) := by
  rw [← coe_algebraMap_mul, mul_one]

/-- An element of `D_E` whose reduced norm is a nonzero `r ∈ K` is a unit (inverse `r⁻¹ x̄`). -/
def unitOfNrd (x : DE a b d) (r : K) (hr : r ≠ 0) (h : nrdE x = algebraMap K (QE d) r) : (DE a b d)ˣ where
  val := x
  inv := r⁻¹ • star x
  val_inv := by
    rw [mul_smul_comm, mul_star_eq_nrdE, h, coe_algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hr,
      one_smul]
  inv_val := by
    rw [smul_mul_assoc, star_mul_eq_nrdE, h, coe_algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hr,
      one_smul]

@[simp] theorem coe_unitOfNrd (x : DE a b d) (r : K) (hr : r ≠ 0) (h : nrdE x = algebraMap K (QE d) r) :
    ((unitOfNrd x r hr h : (DE a b d)ˣ) : DE a b d) = x := rfl

theorem unitOfNrd_mem (x : DE a b d) (r : K) (hr : r ≠ 0) (h : nrdE x = algebraMap K (QE d) r) :
    unitOfNrd x r hr h ∈ Gnat a b d := by
  rw [mem_Gnat, coe_unitOfNrd, h]; rfl

theorem nrdK_of_nrdE {x : DE a b d} {r : K} (h : nrdE x = algebraMap K (QE d) r) : nrdK x = r := by
  rw [nrdK, h]; rfl

/-! ### Reflections of `V_0` -/

theorem B4_add_left (v w u : Fin 4 → K) : B4 a b d (v + w) u = B4 a b d v u + B4 a b d w u := by
  simp only [B4, Pi.add_apply]; ring

variable (a b d) in
/-- The reflection `s_u(v) = v − (B(v,u)/Q(u)) u` of `(K⁴, Q4)`. -/
def refl4 (u : Fin 4 → K) : (Fin 4 → K) →ₗ[K] (Fin 4 → K) where
  toFun v := v - (B4 a b d v u / Q4 a b d u) • u
  map_add' v w := by
    simp only [B4_add_left, add_div, add_smul]
    abel
  map_smul' c v := by
    simp only [B4, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_sub, smul_smul]
    congr 2
    ring

theorem refl4_apply (u v : Fin 4 → K) : refl4 a b d u v = v - (B4 a b d v u / Q4 a b d u) • u := rfl

/-- **The reflection in quaternion form:** `s_u(x) = −u x̄ u / nrd u` on `V_0`. -/
theorem emb_refl4 {u : Fin 4 → K} (hu : Q4 a b d u ≠ 0) (v : Fin 4 → K) :
    (emb (refl4 a b d u v) : DE a b d) = -(Q4 a b d u)⁻¹ • (emb u * star (emb v) * emb u) := by
  have h1 : (emb u : DE a b d) * star (emb v) =
      ((algebraMap K (QE d) (B4 a b d u v) : QE d) : DE a b d) - emb v * star (emb u) := by
    rw [← emb_mul_star_add]; abel
  have h2 : (emb u : DE a b d) * star (emb v) * emb u = B4 a b d u v • emb u - Q4 a b d u • emb v := by
    rw [h1, sub_mul, coe_algebraMap_mul, mul_assoc, star_mul_eq_nrdE, nrdE_emb, mul_coe_algebraMap]
  rw [h2, refl4_apply, emb_sub, emb_smul, B4_comm, smul_sub, smul_smul, smul_smul, neg_mul, neg_mul,
    inv_mul_cancel₀ hu, neg_smul, neg_smul, one_smul, div_eq_inv_mul]
  abel

theorem sig_of_inV0 {x : DE a b d} (hx : InV0 x) : sig x = star x := hx

theorem sig_star_of_inV0 {x : DE a b d} (hx : InV0 x) : sig (star x) = x := by
  rw [sig_star, hx, star_star]

theorem nrdE_emb_mul_star (u w : Fin 4 → K) :
    nrdE ((emb u : DE a b d) * star (emb w)) = algebraMap K (QE d) (Q4 a b d u * Q4 a b d w) := by
  rw [nrdE_mul, nrdE_star, nrdE_emb, nrdE_emb, map_mul]

/-- The element `u w̄ ∈ G^♮` for anisotropic `u, w ∈ V_0`. -/
def reflUnit {u w : Fin 4 → K} (hu : Q4 a b d u ≠ 0) (hw : Q4 a b d w ≠ 0) : (DE a b d)ˣ :=
  unitOfNrd ((emb u : DE a b d) * star (emb w)) _ (mul_ne_zero hu hw) (nrdE_emb_mul_star u w)

theorem reflUnit_mem {u w : Fin 4 → K} (hu : Q4 a b d u ≠ 0) (hw : Q4 a b d w ≠ 0) :
    reflUnit hu hw ∈ Gnat a b d := unitOfNrd_mem _ _ _ _

/-- **`s_u s_w = φ_{u w̄}`.** -/
theorem phiLin_reflUnit (h2 : (2 : K) ≠ 0) {u w : Fin 4 → K} (hu : Q4 a b d u ≠ 0) (hw : Q4 a b d w ≠ 0) :
    phiLin ((reflUnit hu hw : (DE a b d)ˣ) : DE a b d) = refl4 a b d u * refl4 a b d w := by
  refine LinearMap.ext fun v => ?_
  apply emb_injective (a := a) (b := b) (d := d)
  rw [emb_phiLin h2, Module.End.mul_apply, emb_refl4 hu, emb_refl4 hw, reflUnit, coe_unitOfNrd,
    nrdK_of_nrdE (nrdE_emb_mul_star u w), star_mul, star_star, sig_mul, sig_of_inV0 (inV0_emb w),
    sig_star_of_inV0 (inV0_emb u), star_smulK, star_mul, star_mul, star_star, mul_smul_comm,
    smul_mul_assoc, smul_smul, mul_inv]
  congr 1
  · ring
  · noncomm_ring

/-! ### Determinant of a reflection -/

theorem B4_eq_dot (v u : Fin 4 → K) :
    B4 a b d v u = (![2 * u 0, -2 * a * d * u 1, -2 * b * d * u 2, 2 * a * b * d * u 3]) ⬝ᵥ v := by
  simp only [B4, dotProduct, Fin.sum_univ_four]
  simp; ring

theorem det_refl4 (h2 : (2 : K) ≠ 0) {u : Fin 4 → K} (hu : Q4 a b d u ≠ 0) :
    (LinearMap.toMatrix' (refl4 a b d u)).det = -1 := by
  have hM : LinearMap.toMatrix' (refl4 a b d u) =
      1 + replicateCol Unit u * replicateRow Unit (-(Q4 a b d u)⁻¹ •
        ![2 * u 0, -2 * a * d * u 1, -2 * b * d * u 2, 2 * a * b * d * u 3]) := by
    ext i j
    rw [LinearMap.toMatrix'_apply, refl4_apply, B4_eq_dot]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.mul_apply,
      replicateCol_apply, replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, Matrix.one_apply,
      Pi.single_apply, dotProduct_single, mul_one]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  rw [hM, det_one_add_replicateCol_mul_replicateRow, smul_dotProduct, ← B4_eq_dot, B4_self, smul_eq_mul]
  field_simp
  ring

end QuadFormsKB.Quat.Gnat

namespace QuadFormsKB.Quat.Gnat

variable {K : Type*} [Field K] {a b d : K}

/-! ### `D ⊂ D_E` and the elements fixing `1` -/

/-- The inclusion `D = (a,b)_K ⊂ D_E = (a,b)_E`. -/
def iota (q : ℍ[K,a,b]) : DE a b d :=
  ⟨algebraMap K (QE d) q.re, algebraMap K (QE d) q.imI, algebraMap K (QE d) q.imJ,
    algebraMap K (QE d) q.imK⟩

theorem iota_mul (p q : ℍ[K,a,b]) : (iota (p * q) : DE a b d) = iota p * iota q := by
  ext <;> simp [iota] <;> ring

theorem iota_star (q : ℍ[K,a,b]) : (iota (star q) : DE a b d) = star (iota q) := by
  ext <;> simp [iota]

theorem sig_iota (q : ℍ[K,a,b]) : sig (iota q : DE a b d) = iota q := by
  ext <;> simp [iota]

theorem iota_smul (c : K) (q : ℍ[K,a,b]) : (iota (c • q) : DE a b d) = c • iota q := by
  ext <;> simp [iota]

theorem iota_coe (r : K) : (iota (r : ℍ[K,a,b]) : DE a b d) = ((algebraMap K (QE d) r : QE d) : DE a b d) := by
  ext <;> simp [iota]

theorem nrdE_iota (q : ℍ[K,a,b]) : nrdE (iota q : DE a b d) = algebraMap K (QE d) (nrd q) := by
  simp only [nrdE, iota, nrd, map_add, map_sub, map_mul, map_pow]

/-- The element of `G^♮` given by a unit of `D`. -/
def iotaUnit (β : (ℍ[K,a,b])ˣ) : (DE a b d)ˣ :=
  unitOfNrd (iota (β : ℍ[K,a,b])) _ (nrd_units_ne_zero β) (nrdE_iota _)

@[simp] theorem coe_iotaUnit (β : (ℍ[K,a,b])ˣ) :
    ((iotaUnit β : (DE a b d)ˣ) : DE a b d) = iota (β : ℍ[K,a,b]) := rfl

theorem iotaUnit_mem (β : (ℍ[K,a,b])ˣ) : (iotaUnit β : (DE a b d)ˣ) ∈ Gnat a b d := unitOfNrd_mem _ _ _ _

/-- `φ_β` for `β ∈ D^×` is `1 ⊕ (y ↦ β y β⁻¹)` on `V_0 = K ⊕ δ D⁰`. -/
theorem phiLin_iota (h2 : (2 : K) ≠ 0) (β : (ℍ[K,a,b])ˣ) (c : K) (y : Fin 3 → K) :
    phiLin (iota (β : ℍ[K,a,b]) : DE a b d) (Fin.cons c y) = Fin.cons c (conjLin β y) := by
  apply emb_injective (a := a) (b := b) (d := d)
  rw [emb_phiLin h2, nrdK_of_nrdE (nrdE_iota _)]
  have hn := nrd_units_ne_zero β
  have c1 : (Fin.cons c y : Fin 4 → K) 1 = y 0 := rfl
  have c2 : (Fin.cons c y : Fin 4 → K) 2 = y 1 := rfl
  have c3 : (Fin.cons c y : Fin 4 → K) 3 = y 2 := rfl
  have c0 : (Fin.cons c y : Fin 4 → K) 0 = c := rfl
  have hc := conjLin_apply' β y
  have d1 : (Fin.cons c (conjLin β y) : Fin 4 → K) 1 =
      ((nrd (β : ℍ[K,a,b]))⁻¹ • imv ((β : ℍ[K,a,b]) * pure y * star (β : ℍ[K,a,b]))) 0 := congrFun hc 0
  have d2 : (Fin.cons c (conjLin β y) : Fin 4 → K) 2 =
      ((nrd (β : ℍ[K,a,b]))⁻¹ • imv ((β : ℍ[K,a,b]) * pure y * star (β : ℍ[K,a,b]))) 1 := congrFun hc 1
  have d3 : (Fin.cons c (conjLin β y) : Fin 4 → K) 3 =
      ((nrd (β : ℍ[K,a,b]))⁻¹ • imv ((β : ℍ[K,a,b]) * pure y * star (β : ℍ[K,a,b]))) 2 := congrFun hc 2
  have d0 : (Fin.cons c (conjLin β y) : Fin 4 → K) 0 = c := rfl
  ext <;> simp only [emb, c0, c1, c2, c3, d0, d1, d2, d3] <;> simp [iota, imv, pure] <;> field_simp <;>
    simp only [nrd] <;> ring

theorem emb_e0 : (emb (Pi.single 0 1) : DE a b d) = 1 := by
  ext <;> simp [emb]

/-- **The stabilizer of `1`:** if `φ_α(1) = 1` for `α ∈ G^♮`, then `α ∈ D^×`. -/
theorem exists_iota_of_phiLin_e0 (h2 : (2 : K) ≠ 0) {α : (DE a b d)ˣ} (hα : α ∈ Gnat a b d)
    (hfix : phiLin (α : DE a b d) (Pi.single 0 1) = Pi.single 0 1) :
    ∃ β : (ℍ[K,a,b])ˣ, (α : DE a b d) = iota (β : ℍ[K,a,b]) := by
  set r := nrdK (α : DE a b d)
  have hr : r ≠ 0 := nrdK_ne_zero hα
  have h1 := congrArg (emb (a := a) (b := b) (d := d)) hfix
  rw [emb_phiLin h2, emb_e0, mul_one] at h1
  have h3 : (α : DE a b d) * sig (star (α : DE a b d)) = (α : DE a b d) * star (α : DE a b d) := by
    rw [mul_star_eq_nrdE, nrdE_eq_nrdK hα, coe_algebraMap_eq_smul_one, ← h1, smul_smul,
      mul_inv_cancel₀ hr, one_smul]
  have h4 : sig (star (α : DE a b d)) = star (α : DE a b d) := (Units.mul_right_inj α).1 h3
  rw [sig_star, star_inj] at h4
  have e0 := congrArg (fun x : DE a b d => x.re.im) h4
  have e1 := congrArg (fun x : DE a b d => x.imI.im) h4
  have e2 := congrArg (fun x : DE a b d => x.imJ.im) h4
  have e3 := congrArg (fun x : DE a b d => x.imK.im) h4
  simp only [re_sig, imI_sig, imJ_sig, imK_sig, QuadraticAlgebra.im_star] at e0 e1 e2 e3
  have z : ∀ t : K, -t = t → t = 0 := fun t ht => by
    have : 2 * t = 0 := by linear_combination -ht
    exact (mul_eq_zero.1 this).resolve_left h2
  set β₀ : ℍ[K,a,b] := ⟨(α : DE a b d).re.re, (α : DE a b d).imI.re, (α : DE a b d).imJ.re,
    (α : DE a b d).imK.re⟩
  have hαβ : (α : DE a b d) = iota β₀ := by
    ext <;> simp [iota, β₀, z _ e0, z _ e1, z _ e2, z _ e3]
  have hn : nrd β₀ ≠ 0 := by
    intro h
    have hE : nrdE (α : DE a b d) = algebraMap K (QE d) r := nrdE_eq_nrdK hα
    rw [hαβ, nrdE_iota, h, map_zero] at hE
    exact hr ((algebraMap K (QE d)).injective hE).symm
  exact ⟨((isUnit_iff_nrd_ne_zero β₀).2 hn).unit, hαβ⟩

/-! ### Determinants of maps fixing `1` -/

theorem single_succ_eq_cons (j : Fin 3) :
    (Pi.single (Fin.succ j) 1 : Fin 4 → K) = Fin.cons 0 (Pi.single j 1) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp [Pi.single_apply, Fin.succ_inj]

theorem det_toMatrix'_of_cons (f : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) (g : (Fin 3 → K) →ₗ[K] (Fin 3 → K))
    (h0 : f (Pi.single 0 1) = Pi.single 0 1) (hg : ∀ y, f (Fin.cons 0 y) = Fin.cons 0 (g y)) :
    (LinearMap.toMatrix' f).det = (LinearMap.toMatrix' g).det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  have hcol : ∀ i : Fin 3, LinearMap.toMatrix' f i.succ 0 = 0 := fun i => by
    rw [LinearMap.toMatrix'_apply, h0]; simp
  simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rw [LinearMap.toMatrix'_apply, h0, Fin.succAbove_zero]
  simp only [Fin.val_zero, pow_zero, Pi.single_eq_same, one_mul]
  congr 1
  ext i j
  rw [Matrix.submatrix_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, single_succ_eq_cons, hg]
  rfl

end QuadFormsKB.Quat.Gnat

namespace QuadFormsKB.Quat.Gnat

variable {K : Type*} [Field K] {a b d : K}

/-! ### The form as a `QuadForm`, isometries, and the reduction step -/

variable (a b d) in
/-- **The quaternary form `⟨1, −ad, −bd, abd⟩ = (V_0, nrd)`** as a `QuadForm K 4`. -/
def V0Form : QuadForm K 4 := QuadForm.diag ![1, -(a * d), -(b * d), a * b * d]

theorem eval_V0Form (v : Fin 4 → K) : (V0Form a b d).eval v = Q4 a b d v := by
  rw [QuadForm.eval, V0Form, QuadForm.evalIn_diag, Fin.sum_univ_four]
  simp [Q4]; ring

variable (a b d) in
/-- `g` preserves `Q4`. -/
def IsIsom4 (g : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) : Prop := ∀ v, Q4 a b d (g v) = Q4 a b d v

theorem IsIsom4.B4 {g : (Fin 4 → K) →ₗ[K] (Fin 4 → K)} (hg : IsIsom4 a b d g) (v w : Fin 4 → K) :
    B4 a b d (g v) (g w) = B4 a b d v w := by
  have h1 := hg (v + w)
  rw [map_add, Q4_add, Q4_add, hg, hg] at h1
  linear_combination h1

theorem IsIsom4.mul {g h : (Fin 4 → K) →ₗ[K] (Fin 4 → K)} (hg : IsIsom4 a b d g) (hh : IsIsom4 a b d h) :
    IsIsom4 a b d (g * h) := fun v => by rw [Module.End.mul_apply, hg, hh]

theorem isIsom4_phiLin (h2 : (2 : K) ≠ 0) {α : (DE a b d)ˣ} (hα : α ∈ Gnat a b d) :
    IsIsom4 a b d (phiLin (α : DE a b d)) := Q4_phiLin h2 hα

theorem Q4_sub (v w : Fin 4 → K) : Q4 a b d (v - w) = Q4 a b d v + Q4 a b d w - B4 a b d v w := by
  simp only [Q4, B4, Pi.sub_apply]; ring

theorem B4_sub_right (v w u : Fin 4 → K) : B4 a b d v (w - u) = B4 a b d v w - B4 a b d v u := by
  simp only [B4, Pi.sub_apply]; ring

theorem B4_add_right (v w u : Fin 4 → K) : B4 a b d v (w + u) = B4 a b d v w + B4 a b d v u := by
  simp only [B4, Pi.add_apply]; ring

theorem refl4_of_B4_eq_Q4 {u v : Fin 4 → K} (hu : Q4 a b d u ≠ 0) (h : B4 a b d v u = Q4 a b d u) :
    refl4 a b d u v = v - u := by
  rw [refl4_apply, h, div_self hu, one_smul]

theorem refl4_of_B4_eq_zero {u v : Fin 4 → K} (h : B4 a b d v u = 0) : refl4 a b d u v = v := by
  rw [refl4_apply, h, zero_div, zero_smul, sub_zero]

theorem refl4_self {u : Fin 4 → K} (hu : Q4 a b d u ≠ 0) : refl4 a b d u u = -u := by
  rw [refl4_apply, B4_self, mul_div_assoc, div_self hu, mul_one, two_smul]; abel

theorem Q4_e0 : Q4 a b d (Pi.single 0 1) = 1 := by simp [Q4]

theorem B4_e0 (v : Fin 4 → K) : B4 a b d v (Pi.single 0 1) = 2 * v 0 := by simp [B4]

/-- **Reduction step:** two reflections move `g(1)` back to `1` (`exists_step` pattern). -/
theorem exists_refl_pair (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hd : d ≠ 0) {g : (Fin 4 → K) →ₗ[K] (Fin 4 → K)}
    (hg : IsIsom4 a b d g) :
    ∃ (u w : Fin 4 → K) (hu : Q4 a b d u ≠ 0) (hw : Q4 a b d w ≠ 0),
      refl4 a b d u (refl4 a b d w (g (Pi.single 0 1))) = Pi.single 0 1 := by
  set e : Fin 4 → K := Pi.single 0 1
  have hQ : Q4 a b d (g e) = 1 := by rw [hg, Q4_e0]
  have he : Q4 a b d e = 1 := Q4_e0
  by_cases hm : Q4 a b d (g e - e) ≠ 0
  · set e1 : Fin 4 → K := Pi.single 1 1
    have hQ1 : Q4 a b d e1 ≠ 0 := by simp [Q4, e1, ha, hd]
    refine ⟨e1, g e - e, hQ1, hm, ?_⟩
    rw [refl4_of_B4_eq_Q4 hm, sub_sub_cancel, refl4_of_B4_eq_zero]
    · simp [B4, e, e1]
    · rw [B4_sub_right, B4_self, Q4_sub, hQ, he]; ring
  · push Not at hm
    have hp : Q4 a b d (g e + e) ≠ 0 := by
      intro hp
      have : Q4 a b d (g e - e) + Q4 a b d (g e + e) = 4 := by
        rw [Q4_sub, Q4_add, hQ, he]; ring
      rw [hm, hp] at this
      have h4 : (2 : K) * 2 = 0 := by linear_combination -this
      exact h2 (mul_self_eq_zero.1 h4)
    refine ⟨e, g e + e, by rw [he]; exact one_ne_zero, hp, ?_⟩
    rw [refl4_of_B4_eq_Q4 hp, show g e - (g e + e) = -e by abel, map_neg,
      refl4_self (by rw [he]; exact one_ne_zero), neg_neg]
    rw [B4_add_right, B4_self, Q4_add, hQ, he]; ring

end QuadFormsKB.Quat.Gnat

namespace QuadFormsKB.Quat.Gnat

variable {K : Type*} [Field K] {a b d : K}

theorem cons_one_zero : (Fin.cons 1 0 : Fin 4 → K) = Pi.single 0 1 := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp [Pi.single_apply]

theorem phiLin_iota_e0 (h2 : (2 : K) ≠ 0) (β : (ℍ[K,a,b])ˣ) :
    phiLin (iota (β : ℍ[K,a,b]) : DE a b d) (Pi.single 0 1) = Pi.single 0 1 := by
  rw [← cons_one_zero, phiLin_iota h2, map_zero]

theorem det_phiLin_iota (h2 : (2 : K) ≠ 0) (β : (ℍ[K,a,b])ˣ) :
    (LinearMap.toMatrix' (phiLin (iota (β : ℍ[K,a,b]) : DE a b d))).det = 1 := by
  rw [det_toMatrix'_of_cons _ (conjLin β) (phiLin_iota_e0 h2 β) (fun y => phiLin_iota h2 β 0 y),
    det_conjLin]

/-- **`det φ_α = 1`** for every `α ∈ G^♮`: after two reflections `φ_α` fixes `1`, hence is
`1 ⊕ conj(β)` with `β ∈ D^×`. -/
theorem det_phiLin (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hd : d ≠ 0) {α : (DE a b d)ˣ} (hα : α ∈ Gnat a b d) :
    (LinearMap.toMatrix' (phiLin (α : DE a b d))).det = 1 := by
  obtain ⟨u, w, hu, hw, huw⟩ := exists_refl_pair h2 ha hd (isIsom4_phiLin h2 hα)
  have hγ : reflUnit hu hw ∈ Gnat a b d := reflUnit_mem hu hw
  have hfix : phiLin ((reflUnit hu hw * α : (DE a b d)ˣ) : DE a b d) (Pi.single 0 1) = Pi.single 0 1 := by
    rw [phiLin_mul h2 hγ, phiLin_reflUnit h2, Module.End.mul_apply, Module.End.mul_apply]
    exact huw
  obtain ⟨β, hβ⟩ := exists_iota_of_phiLin_e0 h2 (mul_mem hγ hα) hfix
  have h1 : (LinearMap.toMatrix' (phiLin (iota (β : ℍ[K,a,b]) : DE a b d))).det = 1 :=
    det_phiLin_iota h2 β
  have h3 : phiLin (iota (β : ℍ[K,a,b]) : DE a b d) = refl4 a b d u * refl4 a b d w * phiLin (α : DE a b d) := by
    rw [← hβ, phiLin_mul h2 hγ, phiLin_reflUnit h2]
  rw [h3, LinearMap.toMatrix'_mul, LinearMap.toMatrix'_mul, det_mul, det_mul, det_refl4 h2 hu,
    det_refl4 h2 hw] at h1
  linear_combination h1

theorem phiLin_mul_inv (h2 : (2 : K) ≠ 0) {α : (DE a b d)ˣ} (hα : α ∈ Gnat a b d) :
    phiLin (α : DE a b d) * phiLin ((α⁻¹ : (DE a b d)ˣ) : DE a b d) = 1 := by
  rw [← phiLin_mul h2 hα, mul_inv_cancel, Units.val_one, phiLin_one]; rfl

theorem phiLin_inv_mul (h2 : (2 : K) ≠ 0) {α : (DE a b d)ˣ} (hα : α ∈ Gnat a b d) :
    phiLin ((α⁻¹ : (DE a b d)ˣ) : DE a b d) * phiLin (α : DE a b d) = 1 := by
  rw [← phiLin_mul h2 (inv_mem hα), inv_mul_cancel, Units.val_one, phiLin_one]; rfl

/-- `φ_α` as an element of `GL₄(K)`. -/
def phiGL (h2 : (2 : K) ≠ 0) (α : Gnat a b d) : GL (Fin 4) K :=
  ⟨LinearMap.toMatrix' (phiLin ((α : (DE a b d)ˣ) : DE a b d)),
    LinearMap.toMatrix' (phiLin (((α : (DE a b d)ˣ)⁻¹ : (DE a b d)ˣ) : DE a b d)),
    by rw [← LinearMap.toMatrix'_mul, phiLin_mul_inv h2 α.2]; exact LinearMap.toMatrix'_id,
    by rw [← LinearMap.toMatrix'_mul, phiLin_inv_mul h2 α.2]; exact LinearMap.toMatrix'_id⟩

theorem coe_phiGL (h2 : (2 : K) ≠ 0) (α : Gnat a b d) :
    ((phiGL h2 α : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      LinearMap.toMatrix' (phiLin ((α : (DE a b d)ˣ) : DE a b d)) := rfl

theorem phiGL_mem (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hd : d ≠ 0) (α : Gnat a b d) :
    phiGL h2 α ∈ SO (V0Form a b d) := by
  refine ⟨det_phiLin h2 ha hd α.2, fun v => ?_⟩
  change (V0Form a b d).eval (LinearMap.toMatrix' (phiLin ((α : (DE a b d)ˣ) : DE a b d)) *ᵥ v) = _
  rw [LinearMap.toMatrix'_mulVec, eval_V0Form, eval_V0Form, Q4_phiLin h2 α.2]

/-- **The homomorphism `φ : G^♮ → SO(V_0)`**, `α ↦ (x ↦ nrd(α)⁻¹ α x σ(ᾱ))`, in coordinates
`G^♮(K) → SO(⟨1, −ad, −bd, abd⟩)(K)`. -/
@[kb "weil1982" "§3.7, p. 64 [unverified]"]
def phiSO (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hd : d ≠ 0) : Gnat a b d →* SO (V0Form a b d) where
  toFun α := ⟨phiGL h2 α, phiGL_mem h2 ha hd α⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_phiGL, OneMemClass.coe_one, Units.val_one, OneMemClass.coe_one, Units.val_one, phiLin_one,
      LinearMap.toMatrix'_id]
  map_mul' α β := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_phiGL, Subgroup.coe_mul, phiLin_mul h2 α.2, LinearMap.toMatrix'_mul]
    rfl

theorem coe_phiSO (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hd : d ≠ 0) (α : Gnat a b d) :
    ((phiSO h2 ha hd α : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      LinearMap.toMatrix' (phiLin ((α : (DE a b d)ˣ) : DE a b d)) := rfl

/-! ### Surjectivity -/

/-- `y ↦ (0, y)`, the inclusion `δD⁰ ⊂ V_0` in coordinates. -/
def consLin : (Fin 3 → K) →ₗ[K] (Fin 4 → K) where
  toFun y := Fin.cons 0 y
  map_add' y z := by
    funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
  map_smul' c y := by
    funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp

theorem Q4_cons (y : Fin 3 → K) : Q4 a b d (Fin.cons 0 y) = d * Q3 a b y := by
  simp only [Q4, Q3]
  have c1 : (Fin.cons 0 y : Fin 4 → K) 1 = y 0 := rfl
  have c2 : (Fin.cons 0 y : Fin 4 → K) 2 = y 1 := rfl
  have c3 : (Fin.cons 0 y : Fin 4 → K) 3 = y 2 := rfl
  have c0 : (Fin.cons 0 y : Fin 4 → K) 0 = 0 := rfl
  rw [c0, c1, c2, c3]; ring

theorem linearMap_ext4 {f g : (Fin 4 → K) →ₗ[K] (Fin 4 → K)} (h0 : f (Pi.single 0 1) = g (Pi.single 0 1))
    (h : ∀ y, f (Fin.cons 0 y) = g (Fin.cons 0 y)) : f = g := by
  refine LinearMap.ext fun v => ?_
  have hv : v = v 0 • (Pi.single 0 1 : Fin 4 → K) + Fin.cons 0 (Fin.tail v) := by
    funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [Fin.tail, Pi.single_apply]
  rw [hv, map_add, map_add, map_smul, map_smul, h0, h]

/-- **`φ : G^♮(K) → SO(V_0)(K)` is surjective** (`2 ≠ 0`, `a, b, d ≠ 0`): two reflections move `g(1)` to `1`,
and `exists_eq_smul_conjLin` identifies the rest with conjugation by some `β ∈ D^×`. -/
@[kb "weil1982" "§3.7, p. 64 [unverified]"]
theorem phiSO_surjective (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) :
    Function.Surjective (phiSO (a := a) (b := b) h2 ha hd) := by
  rintro ⟨g, hg1, hg2⟩
  set G := Matrix.toLin' (g : Matrix (Fin 4) (Fin 4) K)
  have hG : IsIsom4 a b d G := fun v => by
    rw [Matrix.toLin'_apply, ← eval_V0Form, ← eval_V0Form, hg2]
  obtain ⟨u, w, hu, hw, huw⟩ := exists_refl_pair h2 ha hd hG
  set γ := reflUnit (a := a) (b := b) (d := d) hu hw
  have hγ : γ ∈ Gnat a b d := reflUnit_mem hu hw
  set h := phiLin (γ : DE a b d) * G with hhdef
  have hh : IsIsom4 a b d h := (isIsom4_phiLin h2 hγ).mul hG
  have he : h (Pi.single 0 1) = Pi.single 0 1 := by
    rw [Module.End.mul_apply, phiLin_reflUnit h2, Module.End.mul_apply, huw]
  -- `h` preserves `1^⊥ = δD⁰`
  have hperp : ∀ y, (h (Fin.cons 0 y)) 0 = 0 := fun y => by
    have := hh.B4 (Fin.cons 0 y) (Pi.single 0 1)
    rw [he, B4_e0, B4_e0] at this
    have h0 : (Fin.cons 0 y : Fin 4 → K) 0 = 0 := rfl
    rw [h0, mul_zero] at this
    exact (mul_eq_zero.1 this).resolve_left h2
  set h' : (Fin 3 → K) →ₗ[K] (Fin 3 → K) := LinearMap.funLeft K K Fin.succ ∘ₗ h ∘ₗ consLin
  have hcons : ∀ y, h (Fin.cons 0 y) = Fin.cons 0 (h' y) := fun y => by
    have := (Fin.cons_self_tail (h (Fin.cons 0 y))).symm
    rw [hperp y] at this
    exact this
  have hiso : IsIsom a b h' := fun y => by
    have := hh (Fin.cons 0 y)
    rw [hcons, Q4_cons, Q4_cons] at this
    exact mul_left_cancel₀ hd this
  obtain ⟨β, ε, hε, hβ⟩ := exists_eq_smul_conjLin h2 ha hb hiso
  have hdetG : (LinearMap.toMatrix' G).det = 1 := by rw [LinearMap.toMatrix'_toLin']; exact hg1
  have hdeth : (LinearMap.toMatrix' h).det = 1 := by
    rw [LinearMap.toMatrix'_mul, det_mul, hdetG, mul_one]
    exact det_phiLin h2 ha hd hγ
  rcases hε with rfl | rfl
  · -- `h = φ_β`
    have hhβ : h = phiLin (iota (β : ℍ[K,a,b]) : DE a b d) := by
      refine linearMap_ext4 ?_ fun y => ?_
      · rw [he, phiLin_iota_e0 h2]
      · rw [hcons, hβ, one_smul, phiLin_iota h2]
    refine ⟨⟨γ⁻¹ * iotaUnit β, mul_mem (inv_mem hγ) (iotaUnit_mem β)⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_phiSO, phiLin_mul h2 (inv_mem hγ), coe_iotaUnit, ← hhβ]
    rw [hhdef, ← mul_assoc, ← phiLin_mul h2 (inv_mem hγ), inv_mul_cancel, Units.val_one, phiLin_one,
      ← Module.End.one_eq_id, one_mul, LinearMap.toMatrix'_toLin']
  · -- `ε = −1` is impossible: `det h = −1`
    exfalso
    have hdet' := det_toMatrix'_of_cons h ((-1 : K) • conjLin β) he (fun y => by rw [hcons, hβ])
    rw [hdeth, map_smul, det_smul, det_conjLin, Fintype.card_fin] at hdet'
    have h4 : (2 : K) = 0 := by linear_combination hdet'
    exact h2 h4

end QuadFormsKB.Quat.Gnat

namespace QuadFormsKB.Quat.Gnat

variable {K : Type*} [Field K] {a b d : K}

/-! ### The kernel: the central scalars `K^×` -/

variable (a b d) in
/-- **The central scalars `G_m = K^× ⊂ G^♮`.** -/
def scalarsG : Subgroup (Gnat a b d) where
  carrier := {α | ∃ r : K, ((α : (DE a b d)ˣ) : DE a b d) = ((algebraMap K (QE d) r : QE d) : DE a b d)}
  mul_mem' {α β} := by
    rintro ⟨r, hr⟩ ⟨s, hs⟩
    refine ⟨r * s, ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, hr, hs, map_mul, QuaternionAlgebra.coe_mul]
  one_mem' := ⟨1, by rw [map_one]; rfl⟩
  inv_mem' {α} := by
    rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact (α : (DE a b d)ˣ).ne_zero (by rw [hr, map_zero]; rfl)
    refine ⟨r⁻¹, ?_⟩
    have h1 : ((α : (DE a b d)ˣ) : DE a b d) * (((α⁻¹ : Gnat a b d) : (DE a b d)ˣ) : DE a b d) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
    rw [hr, coe_algebraMap_mul] at h1
    rw [coe_algebraMap_eq_smul_one, ← h1, smul_smul, inv_mul_cancel₀ hr0, one_smul]

instance scalarsG_normal : (scalarsG a b d).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨r, hr⟩ := hn
  refine ⟨r, ?_⟩
  simp only [Subgroup.coe_mul, Units.val_mul, hr]
  rw [← QuaternionAlgebra.coe_commutes, mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
  rw [Subgroup.coe_one, Units.val_one, mul_one]

theorem conjLin_eq_id_of_phiLin (h2 : (2 : K) ≠ 0) (β : (ℍ[K,a,b])ˣ)
    (h : phiLin (iota (β : ℍ[K,a,b]) : DE a b d) = LinearMap.id) : conjLin β = LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  have := phiLin_iota (d := d) h2 β 0 y
  rw [h, LinearMap.id_apply] at this
  have h' := congrArg Fin.tail this
  rw [Fin.tail_cons, Fin.tail_cons] at h'
  exact h'.symm

/-- **The kernel of `φ` is `K^×`** (`2 ≠ 0`, `a, d ≠ 0`). -/
@[kb "weil1982" "§3.7, p. 64 [unverified]"]
theorem ker_phiSO (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hd : d ≠ 0) :
    (phiSO (a := a) (b := b) h2 ha hd).ker = scalarsG a b d := by
  ext α
  rw [MonoidHom.mem_ker]
  have hker : phiSO h2 ha hd α = 1 ↔ phiLin ((α : (DE a b d)ˣ) : DE a b d) = LinearMap.id := by
    constructor
    · intro h
      have := congrArg (fun g : SO (V0Form a b d) => ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) h
      simp only [coe_phiSO, OneMemClass.coe_one, Units.val_one] at this
      rw [← LinearMap.toMatrix'_id] at this
      exact LinearMap.toMatrix'.injective this
    · intro h
      apply Subtype.ext
      apply Units.ext
      rw [coe_phiSO, h, LinearMap.toMatrix'_id]
      rfl
  rw [hker]
  constructor
  · intro h
    obtain ⟨β, hβ⟩ := exists_iota_of_phiLin_e0 h2 α.2 (by rw [h, LinearMap.id_apply])
    rw [hβ] at h
    have hc := conjLin_eq_id_of_phiLin h2 β h
    have hk : (conjSO β : SO (pureForm a b)) = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [coe_conjSO, hc, LinearMap.toMatrix'_id]
      rfl
    have hmem : β ∈ centerUnits a b := by rw [← ker_conjSO h2 ha]; exact hk
    obtain ⟨r, hr⟩ := mem_centerUnits.1 hmem
    exact ⟨r, by rw [hβ, hr, iota_coe]⟩
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact (α : (DE a b d)ˣ).ne_zero (by rw [hr, map_zero]; rfl)
    refine LinearMap.ext fun v => ?_
    apply emb_injective (a := a) (b := b) (d := d)
    have hn : nrdE ((α : (DE a b d)ˣ) : DE a b d) = algebraMap K (QE d) (r ^ 2) := by
      rw [hr]; simp [nrdE]
    have hs : sig (star ((α : (DE a b d)ˣ) : DE a b d)) = ((algebraMap K (QE d) r : QE d) : DE a b d) := by
      rw [hr, QuaternionAlgebra.star_coe]; ext <;> simp [sig]
    rw [emb_phiLin h2, nrdK_of_nrdE hn, hs, hr, coe_algebraMap_mul, smul_mul_assoc, mul_coe_algebraMap,
      smul_smul, smul_smul, LinearMap.id_apply]
    rw [show (r ^ 2)⁻¹ * r * r = 1 by field_simp, one_smul]

/-- **`SO(V_0) ≅ G^♮/G_m` on `K`-points** for every field `K` with `2 ≠ 0` and `a, b, d ∈ K^×`:
$$G^\natural(K)/K^\times \;\cong\; SO(\langle 1, -ad, -bd, abd\rangle)(K),$$
where `G^♮(K) = {α ∈ ((a,b)_{K[δ]/(δ²−d)})^× : nrd α ∈ K^×}` acts by `φ_α(x) = nrd(α)⁻¹ α x σ(ᾱ)` on
`V_0 = {x : σ(x) = x̄} = K ⊕ δ D⁰`. No hypothesis on `d` being a non-square: `d` a square (`E ≅ K × K`)
and `d` a non-square (`E` a field) are treated together. -/
@[kb "weil1982" "§3.7, pp. 64–65 [unverified]"]
def gnatQuotEquivSO (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) :
    Gnat a b d ⧸ scalarsG a b d ≃* SO (V0Form a b d) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_phiSO h2 ha hd).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (phiSO_surjective h2 ha hb hd))

end QuadFormsKB.Quat.Gnat

namespace QuadFormsKB.Quat.Gnat

/-! ### Item 1: every quaternary form is `c · (V_0, nrd)`, and base change -/

section Classification

variable {F : Type*} [Field F] [CharZero F]

theorem eval_smul_V0Form (c a b d : F) (v : Fin 4 → F) :
    (c • V0Form a b d).eval v = c * Q4 a b d v := by
  rw [eval_smul_form, eval_V0Form]

/-- **Every nondegenerate quaternary form is `c · ⟨1, −ad, −bd, abd⟩ = c · (V_0, nrd)`** (characteristic `0`),
with `d ≡ disc V` modulo squares: `d · det H_V` is a square (`H_V` the Hessian). Explicitly, if
`V ≅ ⟨c₀, c₁, c₂, c₃⟩` then `c = c₀`, `a = −c₃/c₂`, `b = −c₃/c₁`, `d = c₁c₂/(c₀c₃)`; in the notation
(`V ≅ c⟨1, −a′, −b′, a′b′/d⟩`) `a′ = ad`, `b′ = bd`. -/
@[kb "weil1982" "§3.7, p. 64 [unverified]"]
theorem exists_isometric_smul_V0Form (V : QuadForm F 4) (hV : V.Nondegenerate) :
    ∃ a b d c : F, a ≠ 0 ∧ b ≠ 0 ∧ d ≠ 0 ∧ c ≠ 0 ∧ V.IsometricIn F (c • V0Form a b d) ∧
      IsSquare (d * V.hessian.det) := by
  obtain ⟨e, he, P, hPdet, hP⟩ := FieldGen.exists_isometric_diag V hV
  have h0 := he 0; have h1 := he 1; have h2 := he 2; have h3 := he 3
  have hdiag : ∀ x : Fin 4 → F, (QuadForm.diag e).evalIn F x =
      (e 0 • V0Form (-(e 3 / e 2)) (-(e 3 / e 1)) (e 1 * e 2 / (e 0 * e 3))).eval x := by
    intro x
    rw [eval_smul_V0Form, QuadForm.evalIn_diag, Fin.sum_univ_four, Q4]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    field_simp
    ring
  refine ⟨-(e 3 / e 2), -(e 3 / e 1), e 1 * e 2 / (e 0 * e 3), e 0, by simp [h2, h3], by simp [h1, h3],
    by simp [h0, h1, h2, h3], h0, ⟨P, hPdet, fun x => by rw [hP, hdiag]⟩, ?_⟩
  -- discriminant
  have hH := congrArg Matrix.det (PadicClass.transpose_mul_hessian_mul hP)
  simp only [Matrix.det_mul, Matrix.det_transpose, QuadForm.hessian, QuadForm.diag,
    Matrix.diagonal_transpose, Matrix.diagonal_add, Matrix.det_diagonal, Fin.prod_univ_four] at hH
  have hP0 : P.det ≠ 0 := hPdet.ne_zero
  refine ⟨4 * e 1 * e 2 / P.det, ?_⟩
  have hV' : (V.coeff + V.coeffᵀ).det = 16 * (e 0 * e 1 * e 2 * e 3) / P.det ^ 2 := by
    field_simp
    linear_combination hH
  change e 1 * e 2 / (e 0 * e 3) * (V.coeff + V.coeffᵀ).det = _
  rw [hV']
  field_simp
  ring

end Classification

section BaseChange

universe u v

variable {k : Type u} [Field k] {K : Type v} [Field K] [Algebra k K]

theorem hessian_map {n : ℕ} (Q : QuadForm k n) :
    (Q.map (algebraMap k K)).hessian = Q.hessian.map (algebraMap k K) := by
  simp [QuadForm.hessian, QuadForm.map, Matrix.transpose_map, Matrix.map_add]

omit [Algebra k K] in
theorem two_mul_eval_eq_dotProduct {n : ℕ} (Q : QuadForm K n) (x : Fin n → K) :
    2 * Q.eval x = x ⬝ᵥ (Q.hessian *ᵥ x) := by
  have hpol := QuadForm.polar_eq_hessian K Q x x
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at hpol
  rw [← hpol, show x + x = (2 : K) • x by rw [two_smul]]
  rw [QuadForm.eval, QuadForm.evalIn_smul]
  ring

/-- **Isometries extend to every extension field** (`2 ≠ 0` in `K`): an isometry over `k` gives one over `K`. -/
theorem exists_GL_isometric_map [CharZero k] (h2 : (2 : K) ≠ 0) {n : ℕ} {Q Q' : QuadForm k n}
    (h : Q.IsometricIn k Q') :
    ∃ P : GL (Fin n) K, ∀ x, (Q.map (algebraMap k K)).eval ((P : Matrix (Fin n) (Fin n) K) *ᵥ x) =
      (Q'.map (algebraMap k K)).eval x := by
  obtain ⟨P, hPdet, hP⟩ := h
  have hH := PadicClass.transpose_mul_hessian_mul hP
  set P' := P.map (algebraMap k K)
  have hH' : P'ᵀ * (Q.map (algebraMap k K)).hessian * P' = (Q'.map (algebraMap k K)).hessian := by
    rw [hessian_map, hessian_map, ← hH, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hdet : IsUnit P'.det := by
    rw [show P'.det = algebraMap k K P.det from (RingHom.map_det _ _).symm]
    exact hPdet.map _
  refine ⟨((Matrix.isUnit_iff_isUnit_det P').2 hdet).unit, fun x => ?_⟩
  apply mul_left_cancel₀ h2
  rw [two_mul_eval_eq_dotProduct, two_mul_eval_eq_dotProduct, IsUnit.unit_spec, ← hH',
    Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec]

theorem map_smul_V0Form (c a b d : k) :
    (c • V0Form a b d).map (algebraMap k K) =
      algebraMap k K c • V0Form (algebraMap k K a) (algebraMap k K b) (algebraMap k K d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [QuadForm.map, V0Form, QuadForm.diag]

/-- **`SO(V) ≅ G^♮/G_m` on `K`-points for every extension `K`**: for a
nondegenerate quaternary form `V` over a field `k` of characteristic `0` there are `a, b, d ∈ k^×` with
`d ≡ disc V` (`d · det H_V` a square) such that for **every** field `K ⊇ k`,
$$SO(V)(K) \;\cong\; G^\natural(K)/K^\times, \qquad G^\natural = \{\alpha \in ((a,b)_{K[\delta]/(\delta^2-d)})^\times : \operatorname{nrd}\alpha \in K^\times\}.$$
The same `a, b, d` serve every `K` (they are the `k`-structure of the group `G^♮`). -/
@[kb "weil1982" "§3.7, pp. 64–65 [unverified]"]
theorem nonempty_SO_mulEquiv_gnat [CharZero k] (V : QuadForm k 4) (hV : V.Nondegenerate) :
    ∃ a b d : k, a ≠ 0 ∧ b ≠ 0 ∧ d ≠ 0 ∧ IsSquare (d * V.hessian.det) ∧
      ∀ (K : Type v) [Field K] [Algebra k K],
        Nonempty (SO (V.map (algebraMap k K)) ≃*
          Gnat (algebraMap k K a) (algebraMap k K b) (algebraMap k K d) ⧸
            scalarsG (algebraMap k K a) (algebraMap k K b) (algebraMap k K d)) := by
  obtain ⟨a, b, d, c, ha, hb, hd, hc, hiso, hsq⟩ := exists_isometric_smul_V0Form V hV
  refine ⟨a, b, d, ha, hb, hd, hsq, fun K _ _ => ?_⟩
  have h2 : (2 : K) ≠ 0 := by
    rw [← map_ofNat (algebraMap k K) 2]
    exact (map_ne_zero _).2 two_ne_zero
  obtain ⟨P, hP⟩ := exists_GL_isometric_map (K := K) h2 hiso
  rw [map_smul_V0Form] at hP
  have e1 := SOMulEquivOfIsometric P hP
  rw [SO_smul ((map_ne_zero _).2 hc)] at e1
  exact ⟨e1.trans (gnatQuotEquivSO h2 ((map_ne_zero _).2 ha) ((map_ne_zero _).2 hb)
    ((map_ne_zero _).2 hd)).symm⟩

end BaseChange

end QuadFormsKB.Quat.Gnat

namespace QuadFormsKB.Quat.Gnat

/-! ### Item 4: the square case `E = K × K` -/

section Square

variable {K : Type*} [Field K] {a b d : K}

/-- `E → K`, `δ ↦ s`, for `s² = d`. -/
def evE (s : K) (hs : s ^ 2 = d) : QE d →+* K where
  toFun z := z.re + s * z.im
  map_one' := by simp
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    linear_combination (-(z.im * w.im)) * hs
  map_zero' := by simp
  map_add' z w := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]; ring

theorem evE_apply (s : K) (hs : s ^ 2 = d) (z : QE d) : evE s hs z = z.re + s * z.im := rfl

@[simp] theorem evE_algebraMap (s : K) (hs : s ^ 2 = d) (r : K) : evE s hs (algebraMap K (QE d) r) = r := by
  simp [evE_apply]

theorem evE_star (s : K) (hs : s ^ 2 = d) (hs' : (-s) ^ 2 = d) (z : QE d) :
    evE s hs (star z) = evE (-s) hs' z := by
  simp [evE_apply]

/-- `D_E → D`, coordinatewise `δ ↦ s`. -/
def evQ (s : K) (hs : s ^ 2 = d) : DE a b d →+* ℍ[K,a,b] where
  toFun x := ⟨evE s hs x.re, evE s hs x.imI, evE s hs x.imJ, evE s hs x.imK⟩
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext <;> simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
      QuaternionAlgebra.imK_mul, map_add, map_mul, map_sub, evE_algebraMap, map_zero, zero_mul, add_zero,
      mul_zero, sub_zero]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp] theorem re_evQ (s : K) (hs : s ^ 2 = d) (x : DE a b d) : (evQ s hs x).re = evE s hs x.re := rfl
@[simp] theorem imI_evQ (s : K) (hs : s ^ 2 = d) (x : DE a b d) : (evQ s hs x).imI = evE s hs x.imI := rfl
@[simp] theorem imJ_evQ (s : K) (hs : s ^ 2 = d) (x : DE a b d) : (evQ s hs x).imJ = evE s hs x.imJ := rfl
@[simp] theorem imK_evQ (s : K) (hs : s ^ 2 = d) (x : DE a b d) : (evQ s hs x).imK = evE s hs x.imK := rfl

theorem evQ_star (s : K) (hs : s ^ 2 = d) (x : DE a b d) : evQ s hs (star x) = star (evQ s hs x) := by
  ext <;> simp

theorem evQ_smul (s : K) (hs : s ^ 2 = d) (c : K) (x : DE a b d) : evQ s hs (c • x) = c • evQ s hs x := by
  ext <;> simp [evE_apply] <;> ring

/-- **σ swaps the two factors:** `ev_t ∘ σ = ev_{−t}`. -/
theorem evQ_sig (t : K) (ht : t ^ 2 = d) (ht' : (-t) ^ 2 = d) (x : DE a b d) :
    evQ t ht (sig x) = evQ (-t) ht' x := by
  ext <;> simp only [re_evQ, imI_evQ, imJ_evQ, imK_evQ, re_sig, imI_sig, imJ_sig, imK_sig, evE_star t ht ht']

theorem evQ_neg_sig (t : K) (ht : t ^ 2 = d) (ht' : (-t) ^ 2 = d) (x : DE a b d) :
    evQ (-t) ht' (sig x) = evQ t ht x := by
  ext <;> simp [evE_apply]

theorem nrd_evQ (s : K) (hs : s ^ 2 = d) (x : DE a b d) : nrd (evQ s hs x) = evE s hs (nrdE x) := by
  simp only [nrd, nrdE, re_evQ, imI_evQ, imJ_evQ, imK_evQ, map_add, map_sub, map_mul, map_pow,
    evE_algebraMap]

theorem neg_sq_eq {t : K} (ht : t ^ 2 = d) : (-t) ^ 2 = d := by rw [neg_sq, ht]

/-- The ring homomorphism `D_E → D × D`, `x ↦ (ev_t x, ev_{−t} x)`. -/
def pairHom (t : K) (ht : t ^ 2 = d) : DE a b d →+* ℍ[K,a,b] × ℍ[K,a,b] :=
  (evQ t ht).prod (evQ (-t) (neg_sq_eq ht))

theorem evE_inj (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = d) (ht0 : t ≠ 0) {z w : QE d}
    (h1 : evE t ht z = evE t ht w) (h2' : evE (-t) (neg_sq_eq ht) z = evE (-t) (neg_sq_eq ht) w) : z = w := by
  simp only [evE_apply] at h1 h2'
  have hre : 2 * (z.re - w.re) = 0 := by linear_combination h1 + h2'
  have him : (2 * t) * (z.im - w.im) = 0 := by linear_combination h1 - h2'
  ext
  · exact sub_eq_zero.1 ((mul_eq_zero.1 hre).resolve_left h2)
  · exact sub_eq_zero.1 ((mul_eq_zero.1 him).resolve_left (mul_ne_zero h2 ht0))

/-- The preimage of `(p, q)` coordinatewise. -/
def evPre (t : K) (p q : K) : QE d := ⟨(p + q) / 2, (p - q) / (2 * t)⟩

theorem evE_evPre (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = d) (ht0 : t ≠ 0) (p q : K) :
    evE t ht (evPre t p q) = p ∧ evE (-t) (neg_sq_eq ht) (evPre t p q) = q := by
  simp only [evE_apply, evPre]
  constructor <;> field_simp <;> ring

theorem pairHom_bijective (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = d) (ht0 : t ≠ 0) :
    Function.Bijective (pairHom (a := a) (b := b) t ht) := by
  constructor
  · intro x y hxy
    have h1 := congrArg Prod.fst hxy
    have h2' := congrArg Prod.snd hxy
    simp only [pairHom, RingHom.prod_apply] at h1 h2'
    ext : 1
    · exact evE_inj h2 ht ht0 (congrArg QuaternionAlgebra.re h1) (congrArg QuaternionAlgebra.re h2')
    · exact evE_inj h2 ht ht0 (congrArg QuaternionAlgebra.imI h1) (congrArg QuaternionAlgebra.imI h2')
    · exact evE_inj h2 ht ht0 (congrArg QuaternionAlgebra.imJ h1) (congrArg QuaternionAlgebra.imJ h2')
    · exact evE_inj h2 ht ht0 (congrArg QuaternionAlgebra.imK h1) (congrArg QuaternionAlgebra.imK h2')
  · rintro ⟨p, q⟩
    refine ⟨⟨evPre t p.re q.re, evPre t p.imI q.imI, evPre t p.imJ q.imJ, evPre t p.imK q.imK⟩, ?_⟩
    simp only [pairHom, RingHom.prod_apply, Prod.mk.injEq]
    constructor <;> ext <;> simp [(evE_evPre h2 ht ht0 _ _).1, (evE_evPre h2 ht ht0 _ _).2]

/-- **`D_E ≅ D × D` when `d = t²`** (`2t ≠ 0`). -/
@[kb "weil1982" "§3.7, p. 65 [unverified]"]
def pairEquiv (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = d) (ht0 : t ≠ 0) :
    DE a b d ≃+* ℍ[K,a,b] × ℍ[K,a,b] :=
  RingEquiv.ofBijective (pairHom t ht) (pairHom_bijective h2 ht ht0)

/-- **`V_0 ≅ (D, nrd)` when `d = t²`:** on `V_0` the second factor is the conjugate of the first,
`ev_{−t}(x) = \overline{ev_t(x)}`, and `nrd(ev_t x) = nrd|_{V_0}(x)`. -/
theorem evQ_neg_of_inV0 {t : K} (ht : t ^ 2 = d) {x : DE a b d} (hx : InV0 x) :
    evQ (-t) (neg_sq_eq ht) x = star (evQ t ht x) := by
  rw [← evQ_sig t ht, hx, evQ_star]

theorem nrd_evQ_emb {t : K} (ht : t ^ 2 = d) (v : Fin 4 → K) :
    nrd (evQ t ht (emb v : DE a b d)) = Q4 a b d v := by
  rw [nrd_evQ, nrdE_emb, evE_algebraMap]

/-- The isometry `(K⁴, Q4) → (D, nrd)`, `v ↦ ev_t(emb v)`, is bijective. -/
theorem evQ_emb_bijective (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = d) (ht0 : t ≠ 0) :
    Function.Bijective (fun v : Fin 4 → K => evQ t ht (emb v : DE a b d)) := by
  constructor
  · intro v w hvw
    apply emb_injective (a := a) (b := b) (d := d)
    apply (pairHom_bijective h2 ht ht0).1
    simp only [pairHom, RingHom.prod_apply, Prod.mk.injEq]
    refine ⟨hvw, ?_⟩
    rw [evQ_neg_of_inV0 ht (inV0_emb v), evQ_neg_of_inV0 ht (inV0_emb w)]
    exact congrArg star hvw
  · intro p
    obtain ⟨x, hx⟩ := (pairHom_bijective (a := a) (b := b) h2 ht ht0).2 (p, star p)
    simp only [pairHom, RingHom.prod_apply, Prod.mk.injEq] at hx
    have hV : InV0 x := by
      apply (pairHom_bijective (a := a) (b := b) h2 ht ht0).1
      simp only [pairHom, RingHom.prod_apply, Prod.mk.injEq]
      rw [evQ_sig t ht (neg_sq_eq ht), evQ_star, evQ_star, hx.1, hx.2, star_star,
        evQ_neg_sig t ht (neg_sq_eq ht), hx.1]
      exact ⟨rfl, rfl⟩
    exact ⟨coords x, by show evQ t ht (emb (coords x)) = p; rw [emb_coords h2 hV, hx.1]⟩

/-- **`G^♮ = {(α, β) : nrd α = nrd β}` when `d = t²`.** -/
@[kb "weil1982" "§3.7, p. 65 [unverified]"]
theorem mem_Gnat_iff_nrd_eq (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = d) (ht0 : t ≠ 0) (α : (DE a b d)ˣ) :
    α ∈ Gnat a b d ↔ nrd (evQ t ht (α : DE a b d)) = nrd (evQ (-t) (neg_sq_eq ht) (α : DE a b d)) := by
  rw [mem_Gnat, nrd_evQ, nrd_evQ, evE_apply, evE_apply]
  constructor
  · intro h; rw [h]; ring
  · intro h
    have : (2 * t) * (nrdE (α : DE a b d)).im = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 ht0)

/-- **`φ = (x ↦ α x β⁻¹)` when `d = t²`:** for `α ∈ G^♮` with components `(α₁, α₂) = (ev_t α, ev_{−t} α)`,
`ev_t(φ_α x) = α₁ · ev_t(x) · α₂⁻¹`. -/
@[kb "weil1982" "§3.7, p. 65 [unverified]"]
theorem evQ_phiLin (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = d) {α : (DE a b d)ˣ} (hα : α ∈ Gnat a b d)
    (v : Fin 4 → K) :
    evQ t ht (emb (phiLin (α : DE a b d) v) : DE a b d) =
      evQ t ht (α : DE a b d) * evQ t ht (emb v) *
        (((Units.map (evQ (-t) (neg_sq_eq ht)).toMonoidHom α)⁻¹ : (ℍ[K,a,b])ˣ) : ℍ[K,a,b]) := by
  have hr : nrdK (α : DE a b d) = nrd (evQ (-t) (neg_sq_eq ht) (α : DE a b d)) := by
    rw [nrd_evQ, nrdE_eq_nrdK hα, evE_algebraMap]
  rw [emb_phiLin h2, evQ_smul, map_mul, map_mul, evQ_sig t ht (neg_sq_eq ht), evQ_star, inv_eq, hr,
    mul_smul_comm]
  rfl

end Square

end QuadFormsKB.Quat.Gnat
