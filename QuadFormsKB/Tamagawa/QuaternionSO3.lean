/-
# $SO_3 \cong D^\times / F^\times$: conjugation on the pure quaternions

Weil, *Adeles and Algebraic Groups* (1982), §3.7(a), p. 63: "Let $F$ be a quadratic form in 3 variables, and $G$
the 'special' orthogonal group of $F$; then $G$ is isomorphic to the projective group of a simple central algebra
of dimension 4, viz. a quaternion algebra if $F$ is of index 0, and the matrix algebra $M_2$ otherwise." This file
proves that statement over every field $K$ with $2 \ne 0$ (so it applies to a number field $F$ and to every
completion $F_v$), in coordinates.

**Setting.** $D = (a,b)_K$ = `ℍ[K,a,b]` with $a, b \in K^\times$; the pure (trace-zero) quaternions
$D^0 = K i + K j + K k$ are identified with $K^3$ by $y \mapsto$ `pure y` $= y_0 i + y_1 j + y_2 k$ (0-based), and
$\operatorname{nrd}|_{D^0}$ is the ternary form $\langle -a, -b, ab \rangle$ = `pureForm a b` (`Quat.nrd_pure`).

**Main results.**
* `Quat.conjSO`: the homomorphism $D^\times \to SO(\langle -a,-b,ab\rangle)(K)$, $\alpha \mapsto (y \mapsto \alpha y \alpha^{-1})$.
* `Quat.conjSO_surjective`: it is **surjective** (every rotation is a product of pairs of reflections, and a
  product of two reflections $s_u s_w$ is conjugation by $uw$; `Quat.conjLin_pureUnit`).
* `Quat.ker_conjSO`: its **kernel is $K^\times$** (the central units).
* `Quat.projUnitsEquivSO`: hence $D^\times / K^\times \cong SO(\langle -a,-b,ab \rangle)(K)$.
* `Quat.exists_isometric_smul_pureForm`: **every nondegenerate ternary form is similar to some
  $(D^0, \operatorname{nrd})$**: $d\,Q \cong \langle -a, -b, ab \rangle$ with $d = \operatorname{disc}$-type scalar
  ($Q \cong \langle c_0, c_1, c_2\rangle$, $d = c_0c_1c_2$, $a = -c_1c_2$, $b = -c_0c_2$), characteristic $0$.
* `Quat.nonempty_SO_mulEquiv_proj`: so $SO(Q)(F) \cong D^\times/F^\times$ for every nondegenerate ternary $Q$ over
  a field $F$ of characteristic $0$.

`Quat.SO Q` is $\{g \in GL_n(K) : \det g = 1,\ Q(g x) = Q(x)\ \forall x \in K^n\}$; `Quat.mem_SO_iff_hessian`
matches it with the Hessian description used by `Lattices.orthGroup`.

Sources: Weil 1982, §3.7(a); Voight, *Quaternion Algebras* (2021), §4.5 and Prop. 4.5.? [unverified];
Vignéras 1980, Ch. I, §3 [unverified]; Cartan–Dieudonné in the form of Lam 2005, Ch. I (reflections).
-/
import QuadFormsKB.Tamagawa.Quaternion
import QuadFormsKB.Literature.LocalGlobal.FieldGeneral

open Quaternion Matrix

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section

namespace QuadFormsKB.Quat

/-! ### The special orthogonal group of a `QuadForm` over a field -/

section SO

variable {K : Type*} [Field K] {n : ℕ}

/-- **The special orthogonal group** $SO(Q)(K)$ of a form $Q$ in $n$ variables over a field $K$:
$$SO(Q)(K) = \{ g \in GL_n(K) : \det g = 1 \text{ and } Q(g\vec x) = Q(\vec x) \text{ for all } \vec x \in K^n \}.$$
(With $2 \ne 0$ in $K$ the value condition is equivalent to $g^{\mathsf T} H g = H$ for the Hessian $H$,
`mem_SO_iff_hessian`, the condition of `Lattices.orthGroup`.)

Source: O'Meara 1963, §43A, p. 100 (rotations); Weil 1982, §3.7(a) ("special" = determinant 1). -/
@[kb "weil1982" "§3.7(a), p. 63"]
def SO (Q : QuadForm K n) : Subgroup (GL (Fin n) K) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) K).det = 1 ∧
    ∀ v, Q.eval ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) = Q.eval v}
  mul_mem' {g h} hg hh := by
    refine ⟨?_, fun v => ?_⟩
    · rw [Units.val_mul, Matrix.det_mul, hg.1, hh.1, one_mul]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg.2, hh.2]
  one_mem' := ⟨by simp, fun v => by simp⟩
  inv_mem' {g} hg := by
    have hinv : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * g = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine ⟨?_, fun v => ?_⟩
    · have := congrArg Matrix.det hinv
      rw [Matrix.det_mul, hg.1, mul_one, Matrix.det_one] at this
      exact this
    · have h1 := hg.2 (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec] at h1
      exact h1.symm

theorem mem_SO {Q : QuadForm K n} {g : GL (Fin n) K} :
    g ∈ SO Q ↔ (g : Matrix (Fin n) (Fin n) K).det = 1 ∧
      ∀ v, Q.eval ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) = Q.eval v := Iff.rfl

/-- **The Hessian description of $SO(Q)$** (for $2 \ne 0$): $g \in SO(Q)(K)$ iff $\det g = 1$ and
$g^{\mathsf T} H g = H$, $H$ = `Q.hessian` (the matrix of the bilinear form $B(x,y) = Q(x+y) - Q(x) - Q(y)$). This is
the membership condition of `Lattices.orthGroup` (over a number field and its completions) plus $\det = 1$. -/
@[kb "omeara1963" "§41A, p. 84; §43A, p. 100 (rotations)"]
theorem mem_SO_iff_hessian (h2 : (2 : K) ≠ 0) {Q : QuadForm K n} {g : GL (Fin n) K} :
    g ∈ SO Q ↔ (g : Matrix (Fin n) (Fin n) K).det = 1 ∧
      (g : Matrix (Fin n) (Fin n) K)ᵀ * Q.hessian * g = Q.hessian := by
  have hpol := fun x y => QuadForm.polar_eq_hessian K Q x y
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at hpol
  have hself : ∀ x, 2 * Q.eval x = x ⬝ᵥ (Q.hessian *ᵥ x) := by
    intro x
    rw [← hpol x x, show x + x = (2 : K) • x by rw [two_smul]]
    rw [QuadForm.eval, QuadForm.evalIn_smul]
    ring
  have key : ∀ G : Matrix (Fin n) (Fin n) K,
      (∀ v, Q.eval (G *ᵥ v) = Q.eval v) ↔ Gᵀ * Q.hessian * G = Q.hessian := by
    intro G
    have hT : ∀ x y, (G *ᵥ x) ⬝ᵥ (Q.hessian *ᵥ (G *ᵥ y)) = x ⬝ᵥ ((Gᵀ * Q.hessian * G) *ᵥ y) := by
      intro x y
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Gᵀ,
        Matrix.vecMul_transpose]
    refine ⟨fun h => ?_, fun h v => ?_⟩
    · simp only [QuadForm.eval] at h
      have hB : ∀ x y, x ⬝ᵥ ((Gᵀ * Q.hessian * G) *ᵥ y) = x ⬝ᵥ (Q.hessian *ᵥ y) := by
        intro x y
        rw [← hT, ← hpol, ← Matrix.mulVec_add, h, h, h, hpol]
      ext i j
      have := hB (Pi.single i 1) (Pi.single j 1)
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
    · apply mul_left_cancel₀ h2
      rw [hself, hself, hT, h]
  rw [mem_SO]
  exact and_congr_right fun _ => key _

/-- Scaling the form does not change $SO$: $SO(d\,Q) = SO(Q)$ for $d \ne 0$. -/
theorem SO_smul {Q : QuadForm K n} {d : K} (hd : d ≠ 0) : SO (d • Q) = SO Q := by
  have hev : ∀ v, (d • Q).eval v = d * Q.eval v := by
    intro v
    simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul,
      Algebra.algebraMap_self, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  ext g
  simp only [mem_SO, hev]
  exact and_congr_right fun _ => forall_congr' fun v => mul_right_inj' hd

/-- **$SO$ is transported by isometries:** if $Q(P\vec x) = Q'(\vec x)$ for all $\vec x$ ($P \in GL_n(K)$), then
$g \mapsto P^{-1} g P$ is an isomorphism $SO(Q)(K) \cong SO(Q')(K)$. -/
@[kb "omeara1963" "§41A, p. 84"]
def SOMulEquivOfIsometric {Q Q' : QuadForm K n} (P : GL (Fin n) K)
    (hP : ∀ x, Q.eval ((P : Matrix (Fin n) (Fin n) K) *ᵥ x) = Q'.eval x) : SO Q ≃* SO Q' where
  toFun g := ⟨P⁻¹ * g * P, by
    obtain ⟨g, hg1, hg2⟩ := g
    refine ⟨?_, fun v => ?_⟩
    · simp only [Units.val_mul, Matrix.det_mul, hg1, mul_one]
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    · rw [← hP, ← hP]
      simp only [Units.val_mul, Matrix.mulVec_mulVec, ← mul_assoc, Units.mul_inv, one_mul]
      rw [← Matrix.mulVec_mulVec, hg2]⟩
  invFun h := ⟨P * h * P⁻¹, by
    obtain ⟨h, hh1, hh2⟩ := h
    refine ⟨?_, fun v => ?_⟩
    · simp only [Units.val_mul, Matrix.det_mul, hh1, mul_one]
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    · have e : Q.eval v = Q.eval ((P : Matrix (Fin n) (Fin n) K) *ᵥ
          (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)) := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      rw [e, hP, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP, hh2]⟩
  left_inv g := by
    ext : 2
    simp only [mul_assoc, mul_inv_cancel, mul_one]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
  right_inv h := by
    ext : 2
    simp only [mul_assoc, inv_mul_cancel, mul_one]
    simp only [← mul_assoc, inv_mul_cancel, one_mul]
  map_mul' g h := by
    ext : 2
    simp only [Subgroup.coe_mul, mul_assoc, mul_inv_cancel_left]

end SO

/-! ### Pure quaternions and conjugation -/

section Conj

variable {K : Type*} [Field K] {a b : K}

/-- The pure quaternion $y_0 i + y_1 j + y_2 k$ with coordinate vector $y \in K^3$ (0-based). -/
def pure (y : Fin 3 → K) : ℍ[K,a,b] := ⟨0, y 0, y 1, y 2⟩

/-- The coordinates $(x_1, x_2, x_3)$ of the $i, j, k$ part of $x \in (a,b)_K$, as a vector in $K^3$
(0-based: entry $0$ is the $i$-coefficient). -/
def imv (x : ℍ[K,a,b]) : Fin 3 → K := ![x.imI, x.imJ, x.imK]

@[simp] theorem imv_pure (y : Fin 3 → K) : imv (pure y : ℍ[K,a,b]) = y := by
  funext i; fin_cases i <;> rfl

theorem pure_add (y z : Fin 3 → K) : (pure (y + z) : ℍ[K,a,b]) = pure y + pure z := by
  ext <;> simp [pure]

theorem pure_smul (c : K) (y : Fin 3 → K) : (pure (c • y) : ℍ[K,a,b]) = c • pure y := by
  ext <;> simp [pure]

theorem imv_add (x y : ℍ[K,a,b]) : imv (x + y) = imv x + imv y := by
  funext i; fin_cases i <;> simp [imv]

theorem imv_smul (c : K) (x : ℍ[K,a,b]) : imv (c • x) = c • imv x := by
  funext i; fin_cases i <;> simp [imv]

theorem pure_imv {x : ℍ[K,a,b]} (hx : x.re = 0) : pure (imv x) = x := by
  ext <;> simp [pure, imv, hx]

/-- The ternary form $\langle -a, -b, ab\rangle$ written out: $Q_3(y) = -a y_0^2 - b y_1^2 + ab\, y_2^2$. -/
def Q3 (a b : K) (y : Fin 3 → K) : K := -a * y 0 ^ 2 - b * y 1 ^ 2 + a * b * y 2 ^ 2

/-- Its bilinear form $B_3(y, z) = Q_3(y + z) - Q_3(y) - Q_3(z) = -2a y_0 z_0 - 2b y_1 z_1 + 2ab\, y_2 z_2$. -/
def B3 (a b : K) (y z : Fin 3 → K) : K := -2 * a * y 0 * z 0 - 2 * b * y 1 * z 1 + 2 * a * b * y 2 * z 2

theorem eval_pureForm (y : Fin 3 → K) : (pureForm a b).eval y = Q3 a b y := by
  rw [QuadForm.eval, pureForm, QuadForm.evalIn_diag, Fin.sum_univ_three]
  simp [Q3]; ring

/-- **$\operatorname{nrd}$ on pure quaternions is $\langle -a,-b,ab\rangle$:** $\operatorname{nrd}(y_0 i + y_1 j + y_2 k) =
-a y_0^2 - b y_1^2 + ab\,y_2^2$. -/
@[kb "voight2021" "§5.2 [unverified]"]
theorem nrd_pure (y : Fin 3 → K) : nrd (pure y : ℍ[K,a,b]) = (pureForm a b).eval y := by
  rw [eval_pureForm]; simp [nrd, pure, Q3]

theorem Q3_add (y z : Fin 3 → K) : Q3 a b (y + z) = Q3 a b y + Q3 a b z + B3 a b y z := by
  simp [Q3, B3]; ring

theorem Q3_sub (y z : Fin 3 → K) : Q3 a b (y - z) = Q3 a b y + Q3 a b z - B3 a b y z := by
  simp [Q3, B3]; ring

theorem Q3_neg (y : Fin 3 → K) : Q3 a b (-y) = Q3 a b y := by simp [Q3]

theorem Q3_smul (c : K) (y : Fin 3 → K) : Q3 a b (c • y) = c ^ 2 * Q3 a b y := by
  simp [Q3]; ring

theorem B3_self (y : Fin 3 → K) : B3 a b y y = 2 * Q3 a b y := by simp [B3, Q3]; ring

theorem B3_comm (y z : Fin 3 → K) : B3 a b y z = B3 a b z y := by simp [B3]; ring

theorem B3_add_right (y z w : Fin 3 → K) : B3 a b y (z + w) = B3 a b y z + B3 a b y w := by
  simp [B3]; ring

theorem B3_sub_right (y z w : Fin 3 → K) : B3 a b y (z - w) = B3 a b y z - B3 a b y w := by
  simp [B3]; ring

theorem B3_add_left (y z w : Fin 3 → K) : B3 a b (y + z) w = B3 a b y w + B3 a b z w := by
  simp [B3]; ring

theorem B3_smul_left (c : K) (y z : Fin 3 → K) : B3 a b (c • y) z = c * B3 a b y z := by
  simp [B3]; ring

theorem B3_neg_left (y z : Fin 3 → K) : B3 a b (-y) z = -B3 a b y z := by simp [B3]; ring

/-- $\alpha\, p\, \bar\alpha$ is pure when $p$ is pure. -/
theorem re_mul_pure_mul_star (x : ℍ[K,a,b]) (y : Fin 3 → K) : (x * pure y * star x).re = 0 := by
  simp [pure]; ring

/-- **Conjugation on the pure quaternions:** for $\alpha \in D^\times$, the $K$-linear map
$D^0 \to D^0$, $y \mapsto \alpha y \alpha^{-1}$, in coordinates $K^3 \to K^3$ (via `pure` and `imv`). -/
@[kb "voight2021" "§4.5 [unverified]"]
def conjLin (α : (ℍ[K,a,b])ˣ) : (Fin 3 → K) →ₗ[K] (Fin 3 → K) where
  toFun y := imv ((α : ℍ[K,a,b]) * pure y * ((α⁻¹ : (ℍ[K,a,b])ˣ) : ℍ[K,a,b]))
  map_add' y z := by rw [pure_add, mul_add, add_mul, imv_add]
  map_smul' c y := by
    rw [pure_smul, mul_smul_comm, smul_mul_assoc, imv_smul]; rfl

theorem conjLin_apply (α : (ℍ[K,a,b])ˣ) (y : Fin 3 → K) :
    conjLin α y = imv ((α : ℍ[K,a,b]) * pure y * ((α⁻¹ : (ℍ[K,a,b])ˣ) : ℍ[K,a,b])) := rfl

theorem conjLin_apply' (α : (ℍ[K,a,b])ˣ) (y : Fin 3 → K) :
    conjLin α y = ((nrd (α : ℍ[K,a,b]))⁻¹ : K) • imv ((α : ℍ[K,a,b]) * pure y * star (α : ℍ[K,a,b])) := by
  rw [conjLin_apply, inv_eq, mul_smul_comm, imv_smul]

theorem re_conj (α : (ℍ[K,a,b])ˣ) (y : Fin 3 → K) :
    ((α : ℍ[K,a,b]) * pure y * ((α⁻¹ : (ℍ[K,a,b])ˣ) : ℍ[K,a,b])).re = 0 := by
  rw [inv_eq, mul_smul_comm]
  simp only [QuaternionAlgebra.re_smul, re_mul_pure_mul_star, smul_eq_mul, mul_zero]

theorem pure_conjLin (α : (ℍ[K,a,b])ˣ) (y : Fin 3 → K) :
    (pure (conjLin α y) : ℍ[K,a,b]) = (α : ℍ[K,a,b]) * pure y * ((α⁻¹ : (ℍ[K,a,b])ˣ) : ℍ[K,a,b]) :=
  pure_imv (re_conj α y)

theorem conjLin_one : conjLin (1 : (ℍ[K,a,b])ˣ) = LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  simp [conjLin_apply]

theorem conjLin_mul (α β : (ℍ[K,a,b])ˣ) : conjLin (α * β) = conjLin α * conjLin β := by
  refine LinearMap.ext fun y => ?_
  rw [Module.End.mul_apply, conjLin_apply, conjLin_apply α, pure_conjLin, _root_.mul_inv_rev, Units.val_mul,
    Units.val_mul]
  simp only [mul_assoc]

/-- **Conjugation as a group homomorphism** $D^\times \to \operatorname{End}_K(K^3)$. -/
def conjHom : (ℍ[K,a,b])ˣ →* Module.End K (Fin 3 → K) where
  toFun := conjLin
  map_one' := conjLin_one
  map_mul' := conjLin_mul

/-- **Conjugation preserves the reduced norm** on $D^0$: $\operatorname{nrd}(\alpha y \alpha^{-1}) = \operatorname{nrd}(y)$. -/
theorem Q3_conjLin (α : (ℍ[K,a,b])ˣ) (y : Fin 3 → K) : Q3 a b (conjLin α y) = Q3 a b y := by
  rw [← eval_pureForm, ← eval_pureForm, ← nrd_pure, ← nrd_pure, pure_conjLin, nrd_mul, nrd_mul,
    mul_comm, ← mul_assoc, ← nrd_mul, Units.inv_mul, nrd_one, one_mul]

/-- The unit $y_0 i + y_1 j + y_2 k$ of $D$ for a pure vector with $\operatorname{nrd} \ne 0$. -/
def pureUnit (u : Fin 3 → K) (hu : Q3 a b u ≠ 0) : (ℍ[K,a,b])ˣ :=
  ((isUnit_iff_nrd_ne_zero (pure u : ℍ[K,a,b])).2 (by rwa [nrd_pure, eval_pureForm])).unit

@[simp] theorem coe_pureUnit (u : Fin 3 → K) (hu : Q3 a b u ≠ 0) :
    ((pureUnit u hu : (ℍ[K,a,b])ˣ) : ℍ[K,a,b]) = pure u := rfl

/-- **The reflection** $s_u(y) = y - \dfrac{B_3(y,u)}{Q_3(u)}\, u$ of $(K^3, \langle -a,-b,ab\rangle)$ in an anisotropic
vector $u$. -/
def refl (a b : K) (u : Fin 3 → K) : (Fin 3 → K) →ₗ[K] (Fin 3 → K) where
  toFun y := y - (B3 a b y u / Q3 a b u) • u
  map_add' y z := by rw [B3_add_left, add_div, add_smul]; abel
  map_smul' c y := by
    rw [B3_smul_left, RingHom.id_apply, smul_sub, smul_smul, mul_div_assoc]

theorem refl_apply (u y : Fin 3 → K) : refl a b u y = y - (B3 a b y u / Q3 a b u) • u := rfl

theorem refl_self {u : Fin 3 → K} (hu : Q3 a b u ≠ 0) : refl a b u u = -u := by
  rw [refl_apply, B3_self, mul_div_assoc, div_self hu, mul_one, two_smul]; abel

theorem refl_of_B3_eq_zero {u y : Fin 3 → K} (h : B3 a b y u = 0) : refl a b u y = y := by
  rw [refl_apply, h, zero_div, zero_smul, sub_zero]

theorem refl_of_B3_eq_Q3 {u y : Fin 3 → K} (hu : Q3 a b u ≠ 0) (h : B3 a b y u = Q3 a b u) :
    refl a b u y = y - u := by
  rw [refl_apply, h, div_self hu, one_smul]

/-- **Conjugation by a pure quaternion is minus a reflection:** for pure $u$ with $\operatorname{nrd}(u) \ne 0$,
$u y u^{-1} = -s_u(y)$ on $D^0$. (From $uy + yu = -B(u,y)$ and $u^2 = -\operatorname{nrd}(u)$.) Hence the product of
two reflections $s_u s_w$ is conjugation by $uw$. -/
@[kb "voight2021" "§4.5 [unverified]"]
theorem conjLin_pureUnit (u : Fin 3 → K) (hu : Q3 a b u ≠ 0) :
    conjLin (pureUnit u hu) = -refl a b u := by
  refine LinearMap.ext fun y => ?_
  rw [conjLin_apply', coe_pureUnit, nrd_pure, eval_pureForm, LinearMap.neg_apply, refl_apply]
  funext i
  fin_cases i <;> simp [imv, pure, B3] <;> field_simp <;> simp only [Q3] <;> ring

theorem neg_one_smul_conjLin_pureUnit (u : Fin 3 → K) (hu : Q3 a b u ≠ 0) (y : Fin 3 → K) :
    ((-1 : K) • conjLin (pureUnit u hu)) y = refl a b u y := by
  rw [LinearMap.smul_apply, conjLin_pureUnit, LinearMap.neg_apply, neg_one_smul, neg_neg]

theorem conjLin_pureUnit_apply (u : Fin 3 → K) (hu : Q3 a b u ≠ 0) (y : Fin 3 → K) :
    conjLin (pureUnit u hu) y = -refl a b u y := by
  rw [conjLin_pureUnit, LinearMap.neg_apply]

/-! ### Every isometry of $D^0$ is $\pm$ a conjugation -/

/-- A linear map $g$ of $K^3$ preserving $\langle -a,-b,ab\rangle$. -/
def IsIsom (a b : K) (g : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) : Prop := ∀ y, Q3 a b (g y) = Q3 a b y

theorem IsIsom.B3 {g : (Fin 3 → K) →ₗ[K] (Fin 3 → K)} (hg : IsIsom a b g) (y z : Fin 3 → K) :
    B3 a b (g y) (g z) = B3 a b y z := by
  have h1 := hg (y + z)
  rw [map_add, Q3_add, Q3_add, hg, hg] at h1
  linear_combination h1

theorem isIsom_smul_conjLin (α : (ℍ[K,a,b])ˣ) {ε : K} (hε : ε = 1 ∨ ε = -1) :
    IsIsom a b (ε • conjLin α) := by
  intro y
  rw [LinearMap.smul_apply, Q3_smul, Q3_conjLin]
  rcases hε with rfl | rfl <;> ring

theorem IsIsom.mul {g h : (Fin 3 → K) →ₗ[K] (Fin 3 → K)} (hg : IsIsom a b g) (hh : IsIsom a b h) :
    IsIsom a b (g * h) := fun y => by rw [Module.End.mul_apply, hg, hh]

/-- **One reflection step** (Cartan–Dieudonné): given an isometry $g$ and an anisotropic $e$, some
$\varepsilon\,\mathrm{conj}(\alpha)$ ($\varepsilon = \pm 1$) maps $g e$ back to $e$ and fixes every $f \perp e, g e$.
(It is $s_{ge - e}$ if $Q(ge - e) \ne 0$, else $s_e s_{ge + e}$.) -/
theorem exists_step (h2 : (2 : K) ≠ 0) {g : (Fin 3 → K) →ₗ[K] (Fin 3 → K)} (hg : IsIsom a b g)
    {e : Fin 3 → K} (he : Q3 a b e ≠ 0) :
    ∃ (α : (ℍ[K,a,b])ˣ) (ε : K), (ε = 1 ∨ ε = -1) ∧ (ε • conjLin α) (g e) = e ∧
      ∀ f, B3 a b f e = 0 → B3 a b f (g e) = 0 → (ε • conjLin α) f = f := by
  have hQ := hg e
  by_cases hm : Q3 a b (g e - e) ≠ 0
  · refine ⟨pureUnit _ hm, -1, Or.inr rfl, ?_, fun f hfe hfg => ?_⟩
    · rw [neg_one_smul_conjLin_pureUnit, refl_of_B3_eq_Q3 hm]
      · abel
      · rw [B3_sub_right, B3_self, Q3_sub, B3_comm]; linear_combination hQ
    · rw [neg_one_smul_conjLin_pureUnit, refl_of_B3_eq_zero]
      rw [B3_sub_right, hfe, hfg, sub_zero]
  · push Not at hm
    have hp : Q3 a b (g e + e) ≠ 0 := by
      intro hp
      have : Q3 a b (g e - e) + Q3 a b (g e + e) = 4 * Q3 a b e := by
        rw [Q3_sub, Q3_add, hQ]; ring
      rw [hm, hp] at this
      have h4 : (4 : K) ≠ 0 := by
        rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
      exact he (by
        have := this.symm
        rw [add_zero] at this
        exact (mul_eq_zero.1 this).resolve_left h4)
    refine ⟨pureUnit e he * pureUnit _ hp, 1, Or.inl rfl, ?_, fun f hfe hfg => ?_⟩
    · rw [one_smul, conjLin_mul, Module.End.mul_apply, conjLin_pureUnit_apply _ hp,
        refl_of_B3_eq_Q3 hp, show g e - (g e + e) = -e by abel, neg_neg, conjLin_pureUnit_apply,
        refl_self he, neg_neg]
      rw [B3_add_right, B3_self, Q3_add]; linear_combination hQ
    · rw [one_smul, conjLin_mul, Module.End.mul_apply, conjLin_pureUnit_apply _ hp,
        refl_of_B3_eq_zero, conjLin_pureUnit_apply, refl_of_B3_eq_zero, neg_neg]
      · rw [B3_neg_left, hfe, neg_zero]
      · rw [B3_add_right, hfe, hfg, add_zero]

theorem e_Q3 (i : Fin 3) : Q3 a b (Pi.single i 1) = ![-a, -b, a * b] i := by
  fin_cases i <;> simp [Q3]

/-- **Every isometry of $(D^0, \operatorname{nrd})$ is $\pm$ a conjugation:** if $g$ preserves $\langle -a,-b,ab\rangle$
($a, b \ne 0$, $2 \ne 0$), then $g = \varepsilon \cdot (y \mapsto \alpha y \alpha^{-1})$ for some $\alpha \in D^\times$ and
$\varepsilon = \pm 1$. (Three applications of `exists_step`, along the orthogonal basis $i, j, k$.) -/
@[kb "voight2021" "§4.5 [unverified]"]
theorem exists_eq_smul_conjLin (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    {g : (Fin 3 → K) →ₗ[K] (Fin 3 → K)} (hg : IsIsom a b g) :
    ∃ (α : (ℍ[K,a,b])ˣ) (ε : K), (ε = 1 ∨ ε = -1) ∧ g = ε • conjLin α := by
  set e0 : Fin 3 → K := Pi.single 0 1
  set e1 : Fin 3 → K := Pi.single 1 1
  set e2 : Fin 3 → K := Pi.single 2 1
  have hB01 : B3 a b e0 e1 = 0 := by simp [B3, e0, e1]
  have hB20 : B3 a b e2 e0 = 0 := by simp [B3, e0, e2]
  have hB21 : B3 a b e2 e1 = 0 := by simp [B3, e1, e2]
  have hQ0 : Q3 a b e0 ≠ 0 := by simp [Q3, e0, ha]
  have hQ1 : Q3 a b e1 ≠ 0 := by simp [Q3, e1, hb]
  -- step 1
  obtain ⟨α₁, ε₁, hε₁, h1e, -⟩ := exists_step h2 hg hQ0
  set h₁ := (ε₁ • conjLin α₁) * g
  have hh₁ : IsIsom a b h₁ := (isIsom_smul_conjLin α₁ hε₁).mul hg
  have h₁e0 : h₁ e0 = e0 := h1e
  -- step 2
  obtain ⟨α₂, ε₂, hε₂, h2e, h2f⟩ := exists_step h2 hh₁ hQ1
  set h₂ := (ε₂ • conjLin α₂) * h₁
  have hh₂ : IsIsom a b h₂ := (isIsom_smul_conjLin α₂ hε₂).mul hh₁
  have h₂e1 : h₂ e1 = e1 := h2e
  have h₂e0 : h₂ e0 = e0 := by
    change (ε₂ • conjLin α₂) (h₁ e0) = e0
    rw [h₁e0]
    refine h2f e0 hB01 ?_
    have := hh₁.B3 e0 e1
    rw [h₁e0] at this
    rw [this, hB01]
  -- step 3: h₂ e2 = ± e2
  have hBe0 : ∀ y : Fin 3 → K, B3 a b y e0 = -2 * a * y 0 := fun y => by simp [B3, e0]
  have hBe1 : ∀ y : Fin 3 → K, B3 a b y e1 = -2 * b * y 1 := fun y => by simp [B3, e1]
  obtain ⟨w, hwdef⟩ : ∃ w, w = h₂ e2 := ⟨_, rfl⟩
  have hw0 : w 0 = 0 := by
    have := hh₂.B3 e2 e0
    rw [h₂e0, hB20, ← hwdef, hBe0] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero (by simpa using h2) ha)
    · exact h
  have hw1 : w 1 = 0 := by
    have := hh₂.B3 e2 e1
    rw [h₂e1, hB21, ← hwdef, hBe1] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero (by simpa using h2) hb)
    · exact h
  have hw2 : w 2 = 1 ∨ w 2 = -1 := by
    have h3 : Q3 a b w = a * b := by rw [hwdef, hh₂]; simp [Q3, e2]
    unfold Q3 at h3
    rw [hw0, hw1] at h3
    have hab : a * b ≠ 0 := mul_ne_zero ha hb
    have : (w 2 - 1) * (w 2 + 1) = 0 := by
      apply (mul_right_inj' hab).1
      linear_combination h3
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hw : w = w 2 • e2 := by
    funext i; fin_cases i <;> simp [e2, hw0, hw1]
  -- h₂ = ε₃ conj α₃
  have hext : ∀ {f f' : (Fin 3 → K) →ₗ[K] (Fin 3 → K)}, f e0 = f' e0 → f e1 = f' e1 → f e2 = f' e2 →
      f = f' := by
    intro f f' h0 h1 h2'
    refine LinearMap.pi_ext fun i x => ?_
    rw [show (Pi.single i x : Fin 3 → K) = x • Pi.single i 1 by
      rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, map_smul]
    fin_cases i
    · exact congrArg _ h0
    · exact congrArg _ h1
    · exact congrArg _ h2'
  have hQ2 : Q3 a b e2 ≠ 0 := by simp [Q3, e2, ha, hb]
  obtain ⟨α₃, ε₃, hε₃, h₂eq⟩ : ∃ (α₃ : (ℍ[K,a,b])ˣ) (ε₃ : K), (ε₃ = 1 ∨ ε₃ = -1) ∧
      h₂ = ε₃ • conjLin α₃ := by
    rcases hw2 with h | h
    · refine ⟨1, 1, Or.inl rfl, hext ?_ ?_ ?_⟩
      · rw [one_smul, conjLin_one, LinearMap.id_apply, h₂e0]
      · rw [one_smul, conjLin_one, LinearMap.id_apply, h₂e1]
      · rw [one_smul, conjLin_one, LinearMap.id_apply, ← hwdef, hw, h, one_smul]
    · refine ⟨pureUnit e2 hQ2, -1, Or.inr rfl, hext ?_ ?_ ?_⟩
      · rw [neg_one_smul_conjLin_pureUnit, refl_of_B3_eq_zero, h₂e0]
        rw [B3_comm, hB20]
      · rw [neg_one_smul_conjLin_pureUnit, refl_of_B3_eq_zero, h₂e1]
        rw [B3_comm, hB21]
      · rw [neg_one_smul_conjLin_pureUnit, refl_self hQ2, ← hwdef, hw, h, neg_one_smul]
  -- assemble
  refine ⟨(α₂ * α₁)⁻¹ * α₃, ε₁ * ε₂ * ε₃, ?_, ?_⟩
  · rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl <;> rcases hε₃ with rfl | rfl <;> norm_num
  · have hsq : ∀ ε : K, (ε = 1 ∨ ε = -1) → ε * ε = 1 := by
      rintro ε (rfl | rfl) <;> norm_num
    have key : h₂ = (ε₁ * ε₂) • (conjLin (α₂ * α₁) * g) := by
      change (ε₂ • conjLin α₂) * ((ε₁ • conjLin α₁) * g) = _
      rw [conjLin_mul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc, mul_comm ε₂]
    have hinv : conjLin (α₂ * α₁)⁻¹ * conjLin (α₂ * α₁) = 1 := by
      rw [← conjLin_mul, inv_mul_cancel, conjLin_one]; rfl
    have hg' : conjLin (α₂ * α₁)⁻¹ * h₂ = (ε₁ * ε₂) • g := by
      rw [key, mul_smul_comm, ← mul_assoc, hinv, one_mul]
    calc g = ((ε₁ * ε₂) * (ε₁ * ε₂)) • g := by
          rw [show (ε₁ * ε₂) * (ε₁ * ε₂) = (ε₁ * ε₁) * (ε₂ * ε₂) by ring, hsq ε₁ hε₁, hsq ε₂ hε₂, one_mul,
            one_smul]
      _ = (ε₁ * ε₂) • (conjLin (α₂ * α₁)⁻¹ * h₂) := by rw [hg', smul_smul]
      _ = _ := by rw [h₂eq, mul_smul_comm, smul_smul, ← conjLin_mul]

/-! ### The matrix of a conjugation, its determinant, and the map to $SO$ -/

/-- The matrix of $y \mapsto \alpha y \bar\alpha$ on $K^3$ (columns: images of $i, j, k$). -/
def nMat (x : ℍ[K,a,b]) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => imv (x * pure (Pi.single j 1) * star x) i

theorem det_nMat (x : ℍ[K,a,b]) : (nMat x).det = nrd x ^ 3 := by
  rw [Matrix.det_fin_three]
  simp [nMat, imv, pure, nrd]
  ring

theorem toMatrix'_conjLin (α : (ℍ[K,a,b])ˣ) :
    LinearMap.toMatrix' (conjLin α) = ((nrd (α : ℍ[K,a,b]))⁻¹ : K) • nMat (α : ℍ[K,a,b]) := by
  ext i j
  rw [LinearMap.toMatrix'_apply, conjLin_apply']
  rfl

/-- **Conjugation has determinant $1$** on $D^0$: $\det(y \mapsto \alpha y\alpha^{-1}) = 1$. -/
@[kb "voight2021" "§4.5 [unverified]"]
theorem det_conjLin (α : (ℍ[K,a,b])ˣ) : (LinearMap.toMatrix' (conjLin α)).det = 1 := by
  rw [toMatrix'_conjLin, Matrix.det_smul, det_nMat, Fintype.card_fin, ← mul_pow,
    inv_mul_cancel₀ (nrd_units_ne_zero α), one_pow]

/-- The conjugation matrix as an element of $GL_3(K)$. -/
def conjGL (α : (ℍ[K,a,b])ˣ) : GL (Fin 3) K :=
  ⟨LinearMap.toMatrix' (conjLin α), LinearMap.toMatrix' (conjLin α⁻¹),
    by rw [← LinearMap.toMatrix'_mul, ← conjLin_mul, mul_inv_cancel, conjLin_one, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_mul, ← conjLin_mul, inv_mul_cancel, conjLin_one, LinearMap.toMatrix'_id]⟩

theorem conjGL_mem (α : (ℍ[K,a,b])ˣ) : conjGL α ∈ SO (pureForm a b) := by
  refine ⟨det_conjLin α, fun v => ?_⟩
  change (pureForm a b).eval (LinearMap.toMatrix' (conjLin α) *ᵥ v) = _
  rw [LinearMap.toMatrix'_mulVec, eval_pureForm, eval_pureForm, Q3_conjLin]

/-- **The homomorphism $D^\times \to SO(D^0, \operatorname{nrd})$**, $\alpha \mapsto (y \mapsto \alpha y \alpha^{-1})$, in
coordinates: $(a,b)_K^\times \to SO(\langle -a,-b,ab\rangle)(K)$.

Source: Weil 1982, §3.7(a), p. 63; Voight 2021, §4.5 [unverified]. -/
@[kb "weil1982" "§3.7(a), p. 63"]
def conjSO : (ℍ[K,a,b])ˣ →* SO (pureForm a b) where
  toFun α := ⟨conjGL α, conjGL_mem α⟩
  map_one' := by
    ext : 2
    change LinearMap.toMatrix' (conjLin 1) = 1
    rw [conjLin_one, LinearMap.toMatrix'_id]
  map_mul' α β := by
    ext : 2
    change LinearMap.toMatrix' (conjLin (α * β)) = LinearMap.toMatrix' (conjLin α) * LinearMap.toMatrix' (conjLin β)
    rw [conjLin_mul, LinearMap.toMatrix'_mul]

theorem coe_conjSO (α : (ℍ[K,a,b])ˣ) :
    ((conjSO α : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = LinearMap.toMatrix' (conjLin α) := rfl

/-- **$D^\times \to SO(D^0)$ is surjective** ($a, b \in K^\times$, $2 \ne 0$ in $K$): every rotation of
$(D^0, \operatorname{nrd})$ is $y \mapsto \alpha y \alpha^{-1}$ for some $\alpha \in D^\times$.

*Proof.* `exists_eq_smul_conjLin` writes $g = \varepsilon\,\mathrm{conj}(\alpha)$ with $\varepsilon = \pm 1$; taking
determinants, $1 = \det g = \varepsilon^3 \det \mathrm{conj}(\alpha) = \varepsilon$.

Source: Weil 1982, §3.7(a), p. 63; Voight 2021, Prop. 4.5.? [unverified]. -/
@[kb "weil1982" "§3.7(a), p. 63"]
theorem conjSO_surjective (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Surjective (conjSO : (ℍ[K,a,b])ˣ →* SO (pureForm a b)) := by
  rintro ⟨g, hg1, hg2⟩
  have hiso : IsIsom a b (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K)) := by
    intro y
    rw [Matrix.toLin'_apply, ← eval_pureForm, ← eval_pureForm, hg2]
  obtain ⟨α, ε, hε, hge⟩ := exists_eq_smul_conjLin h2 ha hb hiso
  have hgm : (g : Matrix (Fin 3) (Fin 3) K) = ε • LinearMap.toMatrix' (conjLin α) := by
    rw [← LinearMap.toMatrix'_toLin' (g : Matrix (Fin 3) (Fin 3) K), hge, map_smul]
  have hε1 : ε = 1 := by
    have := hg1
    rw [hgm, Matrix.det_smul, det_conjLin, Fintype.card_fin, mul_one] at this
    rcases hε with rfl | rfl
    · rfl
    · exfalso
      norm_num at this
      exact h2 (by linear_combination -this)
  refine ⟨α, ?_⟩
  ext : 2
  rw [coe_conjSO]
  change _ = (g : Matrix (Fin 3) (Fin 3) K)
  rw [hgm, hε1, one_smul]

/-- The central units $K^\times \subseteq D^\times$ (the image of $K^\times$ under $r \mapsto r \cdot 1$). -/
def centerUnits (a b : K) : Subgroup (ℍ[K,a,b])ˣ :=
  (Units.map (algebraMap K ℍ[K,a,b]).toMonoidHom).range

theorem mem_centerUnits {α : (ℍ[K,a,b])ˣ} :
    α ∈ centerUnits a b ↔ ∃ r : K, (α : ℍ[K,a,b]) = (r : ℍ[K,a,b]) := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact α.ne_zero (by rw [hr]; rfl)
    refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
    rw [hr]
    rfl

instance centerUnits_normal : (centerUnits a b).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨r, hr⟩ := mem_centerUnits.1 hn
  refine mem_centerUnits.2 ⟨r, ?_⟩
  rw [Units.val_mul, Units.val_mul, hr, ← QuaternionAlgebra.coe_commutes, mul_assoc, Units.mul_inv, mul_one]

/-- **The kernel of $D^\times \to SO(D^0)$ is $K^\times$** ($a, b \ne 0$, $2 \ne 0$): $\alpha y \alpha^{-1} = y$ for all pure
$y$ iff $\alpha$ is central, i.e. $\alpha \in K^\times$.

Source: Weil 1982, §3.7(a); Voight 2021, §4.5 [unverified]. -/
@[kb "weil1982" "§3.7(a), p. 63"]
theorem ker_conjSO (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) :
    (conjSO : (ℍ[K,a,b])ˣ →* SO (pureForm a b)).ker = centerUnits a b := by
  ext α
  rw [MonoidHom.mem_ker, mem_centerUnits]
  have hker : conjSO α = 1 ↔ conjLin α = LinearMap.id := by
    constructor
    · intro h
      have := congrArg (fun g : SO (pureForm a b) => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
      simp only [coe_conjSO, OneMemClass.coe_one, Units.val_one] at this
      rw [← LinearMap.toMatrix'_id] at this
      exact LinearMap.toMatrix'.injective this
    · intro h
      ext : 2
      rw [coe_conjSO, h, LinearMap.toMatrix'_id]
      rfl
  rw [hker]
  constructor
  · intro h
    -- α commutes with every pure quaternion
    have hcomm : ∀ y : Fin 3 → K, (α : ℍ[K,a,b]) * pure y = pure y * (α : ℍ[K,a,b]) := by
      intro y
      have := pure_conjLin α y
      rw [h, LinearMap.id_apply] at this
      calc (α : ℍ[K,a,b]) * pure y = (α : ℍ[K,a,b]) * pure y * ((α⁻¹ : (ℍ[K,a,b])ˣ) : ℍ[K,a,b]) * (α : ℍ[K,a,b]) := by
            rw [mul_assoc _ _ (α : ℍ[K,a,b]), Units.inv_mul, mul_one]
        _ = pure y * (α : ℍ[K,a,b]) := by rw [← this]
    have hi := hcomm (Pi.single 0 1)
    have hj := hcomm (Pi.single 1 1)
    have e1 := congrArg QuaternionAlgebra.imJ hi
    have e2 := congrArg QuaternionAlgebra.imK hi
    have e3 := congrArg QuaternionAlgebra.imK hj
    simp [pure] at e1 e2 e3
    have hu : (α : ℍ[K,a,b]).imK = 0 := by
      have : 2 * a * (α : ℍ[K,a,b]).imK = 0 := by linear_combination -e1
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (mul_ne_zero h2 ha)
      · exact h
    have ht : (α : ℍ[K,a,b]).imJ = 0 := by
      have : 2 * (α : ℍ[K,a,b]).imJ = 0 := by linear_combination -e2
      exact (mul_eq_zero.1 this).resolve_left h2
    have hs : (α : ℍ[K,a,b]).imI = 0 := by
      have : 2 * (α : ℍ[K,a,b]).imI = 0 := by linear_combination e3
      exact (mul_eq_zero.1 this).resolve_left h2
    exact ⟨(α : ℍ[K,a,b]).re, by ext <;> simp [hs, ht, hu]⟩
  · rintro ⟨r, hr⟩
    refine LinearMap.ext fun y => ?_
    rw [conjLin_apply, hr, LinearMap.id_apply, QuaternionAlgebra.coe_commutes, mul_assoc]
    have : (r : ℍ[K,a,b]) * ((α⁻¹ : (ℍ[K,a,b])ˣ) : ℍ[K,a,b]) = 1 := by
      rw [← hr, Units.mul_inv]
    rw [this, mul_one, imv_pure]

/-- **$D^\times / K^\times \cong SO(D^0, \operatorname{nrd})$** for $D = (a,b)_K$, $a, b \in K^\times$, $2 \ne 0$ in $K$:
$$((a,b)_K)^\times / K^\times \;\cong\; SO(\langle -a, -b, ab \rangle)(K).$$
This is Weil's "$G$ is isomorphic to the projective group of a simple central algebra of dimension 4" for the
ternary form $\operatorname{nrd}|_{D^0}$ (Weil 1982, §3.7(a), p. 63), at the level of $K$-points. -/
@[kb "weil1982" "§3.7(a), p. 63"]
def projUnitsEquivSO (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    (ℍ[K,a,b])ˣ ⧸ centerUnits a b ≃* SO (pureForm a b) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_conjSO h2 ha).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (conjSO_surjective h2 ha hb))

end Conj

/-! ### Every ternary form is similar to $(D^0, \operatorname{nrd})$ -/

section Similar

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem eval_smul_form (d : F) {n : ℕ} (Q : QuadForm F n) (x : Fin n → F) :
    (d • Q).eval x = d * Q.eval x := by
  simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul,
    Algebra.algebraMap_self, RingHom.id_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- **Every nondegenerate ternary form is similar to the norm form on pure quaternions** (characteristic $0$):
for nondegenerate $Q$ in 3 variables over $F$ there are $a, b, d \in F^\times$ with
$$d\,Q \;\cong\; \langle -a, -b, ab \rangle = (D^0, \operatorname{nrd}), \qquad D = (a,b)_F.$$
Explicitly, if $Q \cong \langle c_0, c_1, c_2 \rangle$ then $d = c_0 c_1 c_2$, $a = -c_1 c_2$, $b = -c_0 c_2$
(0-based). This is the direction of the classical correspondence (ternary forms up to similarity
$\leftrightarrow$ quaternion algebras) that is needed for the base case.

Source: Voight 2021, Thm. 5.1.? / §5.2 [unverified]; Weil 1982, §3.7(a). -/
@[kb "voight2021" "§5.2 [unverified]"]
theorem exists_isometric_smul_pureForm (Q : QuadForm F 3) (hQ : Q.Nondegenerate) :
    ∃ a b d : F, a ≠ 0 ∧ b ≠ 0 ∧ d ≠ 0 ∧ (d • Q).IsometricIn F (pureForm a b) := by
  obtain ⟨c, hc, P, hPdet, hP⟩ := FieldGen.exists_isometric_diag Q hQ
  refine ⟨-(c 1 * c 2), -(c 0 * c 2), c 0 * c 1 * c 2, by simp [hc], by simp [hc], by simp [hc],
    P * Matrix.diagonal ![(c 0)⁻¹, (c 1)⁻¹, 1], ?_, fun x => ?_⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three]
    refine hPdet.mul (Ne.isUnit ?_)
    simp [hc]
  · change (_ • Q).eval _ = (pureForm _ _).eval x
    rw [eval_smul_form, ← Matrix.mulVec_mulVec]
    have := hP (Matrix.diagonal ![(c 0)⁻¹, (c 1)⁻¹, 1] *ᵥ x)
    rw [QuadForm.eval, this, QuadForm.evalIn_diag, eval_pureForm, Fin.sum_univ_three]
    have h0 := hc 0
    have h1 := hc 1
    simp [Q3, Matrix.mulVec_diagonal]
    field_simp

/-- **$SO_3 \cong D^\times/F^\times$** (Weil 1982, §3.7(a), p. 63): for every nondegenerate ternary form $Q$ over a field
$F$ of characteristic $0$ there are $a, b \in F^\times$ with
$$SO(Q)(F) \;\cong\; ((a,b)_F)^\times / F^\times.$$
(Combine `exists_isometric_smul_pureForm`, `SO_smul`, `SOMulEquivOfIsometric` and `projUnitsEquivSO`.) Applied over
each completion $F_v$ (with $Q$ base-changed), this identifies $SO(Q)(F_v)$ with $D_v^\times / F_v^\times$. -/
@[kb "weil1982" "§3.7(a), p. 63"]
theorem nonempty_SO_mulEquiv_proj (Q : QuadForm F 3) (hQ : Q.Nondegenerate) :
    ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧ Nonempty (SO Q ≃* (ℍ[F,a,b])ˣ ⧸ centerUnits a b) := by
  obtain ⟨a, b, d, ha, hb, hd, P, hPdet, hP⟩ := exists_isometric_smul_pureForm Q hQ
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 hPdet
  refine ⟨a, b, ha, hb, ⟨?_⟩⟩
  have e1 : SO (d • Q) ≃* SO (pureForm a b) :=
    SOMulEquivOfIsometric hPu.unit (fun x => by simpa [QuadForm.eval] using hP x)
  rw [SO_smul hd] at e1
  exact e1.trans (projUnitsEquivSO two_ne_zero ha hb).symm

end Similar

end QuadFormsKB.Quat
