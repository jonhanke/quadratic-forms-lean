/-
# Quaternion algebras are classified by their pure norm forms (Voight, Ch. 5)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021, Theorem 5.1.1 and
Corollary 5.2.6 (key `voight2021`).

**Setting.** $K$ is a field with $2 \ne 0$ in $K$ and $B = (a, b \mid K)$ = `ℍ[K,a,b]` is the
quaternion algebra with $i^2 = a$, $j^2 = b$, $ij = -ji = k$. Its **pure quaternions** are
$B^0 = \{\alpha : \operatorname{trd}(\alpha) = 0\} = K i + K j + K k$, and the reduced norm restricted
to $B^0$ is the ternary form
$$\operatorname{nrd}(x_0 i + x_1 j + x_2 k) = -a x_0^2 - b x_1^2 + ab\, x_2^2
= \langle -a, -b, ab \rangle (x_0, x_1, x_2)$$
(`QuadFormsKB.Quat.pureForm a b`; Voight p. 65, with variables $x, y, z$ renamed $x_0, x_1, x_2$).

**Main result** (`nonempty_algEquiv_iff_isometricIn`): for $a, b, a', b' \in K^\times$,
$$(a, b \mid K) \cong (a', b' \mid K) \iff \langle -a, -b, ab\rangle \simeq \langle -a', -b', a'b'\rangle,$$
i.e. the map $B \mapsto \operatorname{nrd}|_{B^0}$ is injective on isomorphism classes, the
injectivity half of the bijection of Theorem 5.1.1 = Corollary 5.2.6. Proved unconditionally.

**Similarity version** (`nonempty_algEquiv_iff_similar`, `exists_similar_pureForm`): $(a,b \mid K) \cong
(a',b' \mid K)$ iff the pure norm forms are *similar* (`Similar`: $c\,Q(P\vec x) = Q'(\vec x)$, $c \in K^\times$),
and every nondegenerate ternary form ($\det H_Q \ne 0$) is similar to a pure norm form. So
$B \mapsto \operatorname{nrd}|_{B^0}$ is a bijection from isomorphism classes of quaternion algebras
$(a, b \mid K)$ onto similarity classes of nondegenerate ternary forms: the second bijection of
Theorem 5.1.1, proved (for $2 \ne 0$ in $K$).

*Proof.* ($\Rightarrow$) An algebra isomorphism $f$ maps pure quaternions to pure quaternions and
preserves $\operatorname{nrd}$ on them (`map_pure`): if $\alpha \in B^0$ then $f(\alpha)^2 = f(\alpha^2)
= -\operatorname{nrd}(\alpha) \in K$, and writing $f(\alpha) = r + \beta$ with $\beta$ pure,
$f(\alpha)^2 = r^2 - \operatorname{nrd}(\beta) + 2r\beta$, so $r\beta = 0$; $\beta = 0$ would force
$\alpha \in K$, so $r = 0$. ($\Leftarrow$) If $g$ is an isometry, then $I = g(i)$ and $J = g(j)$ are pure
with $I^2 = a$, $J^2 = b$ and $IJ = -JI$ (orthogonality), so $i \mapsto I$, $j \mapsto J$ defines an
algebra homomorphism (Mathlib's `QuaternionAlgebra.Basis.liftHom`); it is injective because the
trace pairing with $1, i, j, k$ detects the coordinates ($a, b \ne 0$), hence bijective by dimension.

Indices are 0-based (Voight's $x, y, z$ are $x_0, x_1, x_2$).
-/
import QuadFormsKB.Tamagawa.Quaternion
import QuadFormsKB.Witt.Represents
import QuadFormsKB.Literature.Voight.Correspondence

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

open Quaternion

namespace QuadFormsKB.Voight

open QuadFormsKB.Quat

variable {K : Type*} [Field K]

namespace PureForm

/-- The pure quaternion $x_0 i + x_1 j + x_2 k$ with coordinate vector $x \in K^3$. -/
def pure {a b : K} (x : Fin 3 → K) : ℍ[K,a,b] := ⟨0, x 0, x 1, x 2⟩

/-- The coordinate vector $(x_1, x_2, x_3)$ of the pure part of $x_0 + x_1 i + x_2 j + x_3 k$. -/
def imv {a b : K} (x : ℍ[K,a,b]) : Fin 3 → K := ![x.imI, x.imJ, x.imK]

theorem imv_pure {a b : K} (x : Fin 3 → K) : imv (pure x : ℍ[K,a,b]) = x := by
  ext n; fin_cases n <;> rfl

theorem pure_imv {a b : K} {x : ℍ[K,a,b]} (hx : x.re = 0) : pure (imv x) = x := by
  ext <;> simp [pure, imv, hx]

/-- The values of $\langle -a, -b, ab\rangle$: $-a x_0^2 - b x_1^2 + ab\,x_2^2$. -/
theorem evalIn_pureForm_self (a b : K) (x : Fin 3 → K) :
    (pureForm a b).evalIn K x = -a * x 0 ^ 2 - b * x 1 ^ 2 + a * b * x 2 ^ 2 := by
  simp [pureForm, QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_three, Matrix.diagonal]
  ring

/-- $\operatorname{nrd}(x_0 i + x_1 j + x_2 k) = \langle -a, -b, ab\rangle(x)$. -/
theorem nrd_pure (a b : K) (x : Fin 3 → K) :
    nrd (pure x : ℍ[K,a,b]) = (pureForm a b).evalIn K x := by
  rw [evalIn_pureForm_self]; simp only [nrd, pure]; ring

/-- A pure quaternion squares to minus its norm: $\alpha^2 = -\operatorname{nrd}(\alpha)$. -/
theorem mul_self_of_re_eq_zero {a b : K} {x : ℍ[K,a,b]} (hx : x.re = 0) :
    x * x = ((-nrd x : K) : ℍ[K,a,b]) := by
  ext <;> simp only [QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe, QuaternionAlgebra.imJ_coe,
    QuaternionAlgebra.imK_coe] <;> simp [nrd, hx] <;> ring

/-- **Algebra homomorphisms preserve pure quaternions and their norms** (Voight, proof of
Main Theorem 5.2.5): if $f : (a,b \mid K) \to (a', b' \mid K)$ is an injective algebra homomorphism,
$2 \ne 0$ in $K$ and $\alpha$ is pure, then $f(\alpha)$ is pure and $\operatorname{nrd}(f(\alpha)) =
\operatorname{nrd}(\alpha)$. -/
theorem map_pure (h2 : (2 : K) ≠ 0) {a b a' b' : K} (f : ℍ[K,a,b] →ₐ[K] ℍ[K,a',b'])
    (hf : Function.Injective f) {x : ℍ[K,a,b]} (hx : x.re = 0) :
    (f x).re = 0 ∧ nrd (f x) = nrd x := by
  have hsq : f x * f x = ((-nrd x : K) : ℍ[K,a',b']) := by
    rw [← map_mul, mul_self_of_re_eq_zero hx, ← QuaternionAlgebra.coe_algebraMap, AlgHom.commutes,
      QuaternionAlgebra.coe_algebraMap]
  set y := f x with hy
  have hI : 2 * y.re * y.imI = 0 := by
    have := congrArg QuaternionAlgebra.imI hsq; simp at this; linear_combination this
  have hJ : 2 * y.re * y.imJ = 0 := by
    have := congrArg QuaternionAlgebra.imJ hsq; simp at this; linear_combination this
  have hK : 2 * y.re * y.imK = 0 := by
    have := congrArg QuaternionAlgebra.imK hsq; simp at this; linear_combination this
  have hre : y.re = 0 := by
    by_contra hr
    have h2r : 2 * y.re ≠ 0 := mul_ne_zero h2 hr
    have e1 : y.imI = 0 := (mul_eq_zero.1 hI).resolve_left h2r
    have e2 : y.imJ = 0 := (mul_eq_zero.1 hJ).resolve_left h2r
    have e3 : y.imK = 0 := (mul_eq_zero.1 hK).resolve_left h2r
    have hyc : y = ((y.re : K) : ℍ[K,a',b']) := by ext <;> simp [e1, e2, e3]
    have hxc : x = ((y.re : K) : ℍ[K,a,b]) := by
      apply hf
      rw [← hy, ← QuaternionAlgebra.coe_algebraMap, AlgHom.commutes, QuaternionAlgebra.coe_algebraMap]
      exact hyc
    have := congrArg QuaternionAlgebra.re hxc
    simp [hx] at this
    exact hr this.symm
  refine ⟨hre, ?_⟩
  have := congrArg QuaternionAlgebra.re hsq
  rw [mul_self_of_re_eq_zero hre] at this
  simpa using this

/-- The linear map $x \mapsto$ (coordinates of $f(x_0 i + x_1 j + x_2 k)$) induced on $K^3$ by an
algebra homomorphism $f$. -/
def pureMap {a b a' b' : K} (f : ℍ[K,a,b] →ₐ[K] ℍ[K,a',b']) : (Fin 3 → K) →ₗ[K] (Fin 3 → K) where
  toFun x := imv (f (pure x))
  map_add' x y := by
    have : (pure (x + y) : ℍ[K,a,b]) = pure x + pure y := by ext <;> simp [pure]
    rw [this, map_add]; ext n; fin_cases n <;> simp [imv]
  map_smul' c x := by
    have : (pure (c • x) : ℍ[K,a,b]) = c • pure x := by ext <;> simp [pure]
    rw [this, map_smul]; ext n; fin_cases n <;> simp [imv]

/-- **Isomorphic quaternion algebras have isometric pure norm forms** (Voight, Corollary 5.2.6,
the map $B \mapsto \operatorname{nrd}|_{B^0}$ is well defined on isomorphism classes): if
$2 \ne 0$ in $K$ and $(a, b \mid K) \cong (a', b' \mid K)$, then
$\langle -a, -b, ab\rangle \simeq \langle -a', -b', a'b'\rangle$ over $K$. No hypothesis on $a, b, a', b'$. -/
theorem isometricIn_of_algEquiv (h2 : (2 : K) ≠ 0) {a b a' b' : K}
    (f : ℍ[K,a,b] ≃ₐ[K] ℍ[K,a',b']) : (pureForm a b).IsometricIn K (pureForm a' b') := by
  rw [QuadForm.isometricIn_iff_equivalent]
  have key : ∀ {a b a' b' : K} (g : ℍ[K,a,b] ≃ₐ[K] ℍ[K,a',b']) (x : Fin 3 → K),
      pure (pureMap g.toAlgHom x) = g (pure x) ∧
      (pureForm a' b').evalIn K (pureMap g.toAlgHom x) = (pureForm a b).evalIn K x := by
    intro a b a' b' g x
    have hp := map_pure h2 g.toAlgHom g.injective (x := pure x) rfl
    have e : pure (pureMap g.toAlgHom x) = g (pure x) := pure_imv hp.1
    refine ⟨e, ?_⟩
    rw [← nrd_pure, ← nrd_pure, e]
    exact hp.2
  refine ⟨{ toLinearEquiv := LinearEquiv.ofLinearMap (pureMap f.symm.toAlgHom) (pureMap f.toAlgHom) ?_ ?_
            map_app' := fun x => ?_ }⟩
  · refine LinearMap.ext fun x => ?_
    show imv (f.symm (pure (imv (f (pure x))))) = x
    rw [show (pure (imv (f (pure x))) : ℍ[K,a',b']) = f (pure x) from (key f x).1,
      AlgEquiv.symm_apply_apply, imv_pure]
  · refine LinearMap.ext fun x => ?_
    show imv (f (pure (imv (f.symm (pure x))))) = x
    rw [show (pure (imv (f.symm (pure x))) : ℍ[K,a,b]) = f.symm (pure x) from (key f.symm x).1,
      AlgEquiv.apply_symm_apply, imv_pure]
  · simp only [QuadForm.toQuadraticFormIn_apply, LinearEquiv.coe_ofLinearMap]
    exact (key f.symm x).2

/-- The quaternion basis $I = x_0 i + \dots$, $J$ (with $I^2 = a'$, $J^2 = b'$, $JI = -IJ$) in
$(a, b \mid K)$ given by the images of $e_0, e_1$ under an isometry
$g : \langle -a', -b', a'b'\rangle \to \langle -a, -b, ab\rangle$. -/
def basisOfIsometry {a b a' b' : K}
    (g : (Fin 3 → K) →ₗ[K] (Fin 3 → K))
    (hg : ∀ x, (pureForm a b).evalIn K (g x) = (pureForm a' b').evalIn K x) :
    QuaternionAlgebra.Basis ℍ[K,a,b] a' 0 b' where
  i := pure (g (Pi.single 0 1))
  j := pure (g (Pi.single 1 1))
  k := pure (g (Pi.single 0 1)) * pure (g (Pi.single 1 1))
  i_mul_i := by
    rw [mul_self_of_re_eq_zero rfl, nrd_pure, hg, evalIn_pureForm_self]
    ext <;> simp
  j_mul_j := by
    rw [mul_self_of_re_eq_zero rfl, nrd_pure, hg, evalIn_pureForm_self]
    ext <;> simp
  i_mul_j := rfl
  j_mul_i := by
    set I : ℍ[K,a,b] := pure (g (Pi.single 0 1))
    set J : ℍ[K,a,b] := pure (g (Pi.single 1 1))
    have hII : I * I = ((a' : K) : ℍ[K,a,b]) := by
      rw [mul_self_of_re_eq_zero rfl, nrd_pure, hg, evalIn_pureForm_self]; simp
    have hJJ : J * J = ((b' : K) : ℍ[K,a,b]) := by
      rw [mul_self_of_re_eq_zero rfl, nrd_pure, hg, evalIn_pureForm_self]; simp
    have hIJ : (I + J) * (I + J) = ((a' + b' : K) : ℍ[K,a,b]) := by
      have : I + J = pure (g (Pi.single 0 1 + Pi.single 1 1)) := by
        rw [map_add]; ext <;> simp [I, J, pure]
      rw [this, mul_self_of_re_eq_zero rfl, nrd_pure, hg, evalIn_pureForm_self]
      simp [Pi.single_apply, add_comm]
    have : J * I = -(I * J) := by
      have h := hIJ
      rw [add_mul, mul_add, mul_add, hII, hJJ, QuaternionAlgebra.coe_add] at h
      have h' : I * J + J * I = 0 := by
        rw [show ((a' : K) : ℍ[K,a,b]) + I * J + (J * I + ((b' : K) : ℍ[K,a,b])) =
          (I * J + J * I) + (((a' : K) : ℍ[K,a,b]) + ((b' : K) : ℍ[K,a,b])) by abel] at h
        exact add_eq_right.mp h
      exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h')
    rw [this]; simp

/-- **Isometric pure norm forms give isomorphic quaternion algebras** (Voight, Corollary 5.2.6,
injectivity): if $2 \ne 0$ in $K$, $a', b' \ne 0$, and $g$ is an isometry
$\langle -a', -b', a'b'\rangle \to \langle -a, -b, ab\rangle$, then
$(a', b' \mid K) \cong (a, b \mid K)$. -/
theorem nonempty_algEquiv_of_isometry (h2 : (2 : K) ≠ 0) {a b a' b' : K} (ha' : a' ≠ 0)
    (hb' : b' ≠ 0) (g : (Fin 3 → K) →ₗ[K] (Fin 3 → K))
    (hg : ∀ x, (pureForm a b).evalIn K (g x) = (pureForm a' b').evalIn K x) :
    Nonempty (ℍ[K,a',b'] ≃ₐ[K] ℍ[K,a,b]) := by
  set q := basisOfIsometry g hg
  set φ := q.liftHom
  -- φ preserves the real part, since `q.i`, `q.j`, `q.k` are pure.
  have hk : q.k.re = 0 := by
    have h1 := q.j_mul_i
    have hre : (q.j * q.i).re = (q.i * q.j).re := by
      simp only [QuaternionAlgebra.re_mul]; ring
    rw [h1, q.i_mul_j] at hre
    simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.re_sub, QuaternionAlgebra.re_smul,
      zero_smul, zero_sub, QuaternionAlgebra.re_neg] at hre
    have : 2 * q.k.re = 0 := by linear_combination -hre
    exact (mul_eq_zero.1 this).resolve_left h2
  have hre : ∀ x : ℍ[K,a',b'], (φ x).re = x.re := by
    intro x
    show (q.lift x).re = x.re
    simp [QuaternionAlgebra.Basis.lift, q, basisOfIsometry, pure] at hk ⊢
    simp [hk]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h : ∀ y : ℍ[K,a',b'], (x * y).re = 0 := fun y => by
      rw [← hre, map_mul, hx, zero_mul]; rfl
    have h0 := h 1
    have h1 := h ⟨0, 1, 0, 0⟩
    have h2' := h ⟨0, 0, 1, 0⟩
    have h3 := h ⟨0, 0, 0, 1⟩
    simp at h0 h1 h2' h3
    ext <;> simp_all
  have hbij : Function.Bijective φ := by
    refine ⟨hinj, ?_⟩
    have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := φ.toLinearMap) (by rw [QuaternionAlgebra.finrank_eq_four,
        QuaternionAlgebra.finrank_eq_four])).1 hinj
    exact this
  exact ⟨AlgEquiv.ofBijective φ hbij⟩

/-- **Corollary 5.2.6 (injectivity on classes), Voight 2021**: over a field $K$ with $2 \ne 0$, for
$a, b, a', b' \in K^\times$,
$$(a, b \mid K) \cong (a', b' \mid K) \iff \langle -a, -b, ab\rangle \simeq \langle -a', -b', a'b'\rangle
\text{ over } K,$$
where $\langle -a, -b, ab\rangle = \operatorname{nrd}|_{B^0}$ is the reduced norm on the pure quaternions
(`QuadFormsKB.Quat.pureForm`). So $B \mapsto \operatorname{nrd}|_{B^0}$ is injective from isomorphism
classes of quaternion algebras to isometry classes of ternary forms (Theorem 5.1.1). Proved. -/
@[kb "voight2021" "Corollary 5.2.6, p. 68; Theorem 5.1.1, p. 65"]
theorem nonempty_algEquiv_iff_isometricIn (h2 : (2 : K) ≠ 0) {a b a' b' : K} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    Nonempty (ℍ[K,a,b] ≃ₐ[K] ℍ[K,a',b']) ↔ (pureForm a b).IsometricIn K (pureForm a' b') := by
  refine ⟨fun ⟨f⟩ => isometricIn_of_algEquiv h2 f, fun h => ?_⟩
  rw [QuadForm.isometricIn_iff_equivalent] at h
  obtain ⟨e⟩ := h.symm
  -- `e` : isometry from ⟨-a,-b,ab⟩ to ⟨-a',-b',a'b'⟩
  obtain ⟨f⟩ := nonempty_algEquiv_of_isometry h2 ha hb (a := a') (b := b') (a' := a) (b' := b) e.toLinearEquiv.toLinearMap
    (fun x => by
      have := e.map_app x
      simp only [QuadForm.toQuadraticFormIn_apply] at this
      exact this)
  exact ⟨f⟩

/-! ## Similarity classes (the second bijection of Theorem 5.1.1) -/

/-- The value of a rescaled form: $(cQ)(x) = c\,Q(x)$. -/
theorem evalIn_smul (c : K) (Q : QuadForm K 3) (x : Fin 3 → K) :
    (c • Q).evalIn K x = c * Q.evalIn K x := by
  simp only [QuadForm.evalIn, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul,
    Algebra.algebraMap_self, RingHom.id_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

open Matrix in
/-- **Isometric forms have Hessians related by $P^{\mathsf T} H P = H'$** (over any field; the same
computation as `PadicClass.transpose_mul_hessian_mul`, which assumes an infinite field). -/
theorem transpose_mul_hessian_mul' {n : ℕ} {Q Q' : QuadForm K n} {P : Matrix (Fin n) (Fin n) K}
    (hP : ∀ x, Q.evalIn K (P *ᵥ x) = Q'.evalIn K x) :
    P.transpose * Q.hessian * P = Q'.hessian := by
  have hpol : ∀ x y : Fin n → K,
      (P *ᵥ x) ⬝ᵥ (Q.hessian *ᵥ (P *ᵥ y)) = x ⬝ᵥ (Q'.hessian *ᵥ y) := by
    intro x y
    have h1 := QuadForm.polar_eq_hessian K Q (P *ᵥ x) (P *ᵥ y)
    have h2 := QuadForm.polar_eq_hessian K Q' x y
    rw [← Matrix.mulVec_add, hP, hP, hP] at h1
    have e : ∀ M : Matrix (Fin n) (Fin n) K, M.map (algebraMap K K) = M := fun M => by
      ext; simp
    rw [e] at h1 h2
    rw [← h1, ← h2]
  ext i j
  have := hpol (Pi.single i 1) (Pi.single j 1)
  have e2 : Pi.single i 1 ⬝ᵥ Q'.hessian *ᵥ Pi.single j 1 = Q'.hessian i j := by
    simp
  rw [e2] at this
  rw [← this]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp [Pi.single_apply]; ring

/-- $\det$ of the Hessian of $\langle -a, -b, ab\rangle$ is $8a^2b^2$. -/
theorem det_hessian_pureForm (a b : K) : (pureForm a b).hessian.det = 8 * (a * b) ^ 2 := by
  simp [pureForm, QuadForm.hessian, QuadForm.diag, Matrix.det_fin_three, Fin.prod_univ_three]
  ring

/-- **Similar pure norm forms are isometric** (Voight, proof of Corollary 5.2.6): if
$c\,\langle -a,-b,ab\rangle(P\vec x) = \langle -a',-b',a'b'\rangle(\vec x)$ with $c \in K^\times$ and $P$ invertible,
then comparing $\det$ of the Hessians, $c^3 \det(P)^2 (ab)^2 = (a'b')^2$, so $c$ is a square $s^2$ and
$\vec x \mapsto sP\vec x$ is an isometry. -/
theorem isometricIn_of_similar (h2 : (2 : K) ≠ 0) {a b a' b' : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha' : a' ≠ 0) (hb' : b' ≠ 0) (h : Similar (pureForm a b) (pureForm a' b')) :
    (pureForm a b).IsometricIn K (pureForm a' b') := by
  obtain ⟨c, P, hP, hPx⟩ := h
  have hc : (c : K) ≠ 0 := c.ne_zero
  have hdet := congrArg Matrix.det (transpose_mul_hessian_mul' hPx)
  have hH : ((c : K) • pureForm a b).hessian = (c : K) • (pureForm a b).hessian := by
    simp [QuadForm.hessian, Matrix.transpose_smul, smul_add]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hH, Matrix.det_smul,
    det_hessian_pureForm, det_hessian_pureForm, Fintype.card_fin] at hdet
  have hPd : P.det ≠ 0 := hP.ne_zero
  have h8 : (8 : K) ≠ 0 := by
    rw [show (8 : K) = 2 * 2 * 2 by norm_num]; exact mul_ne_zero (mul_ne_zero h2 h2) h2
  set s : K := (c : K) ^ 2 * (a * b) * P.det / (a' * b') with hs
  have hcs : (c : K) = s ^ 2 := by
    have hab : a * b ≠ 0 := mul_ne_zero ha hb
    have hab' : a' * b' ≠ 0 := mul_ne_zero ha' hb'
    rw [hs, div_pow, mul_pow, mul_pow]
    have key : (c : K) ^ 3 * (P.det ^ 2 * (a * b) ^ 2) = (a' * b') ^ 2 := by
      have := hdet
      field_simp at this
      linear_combination this
    field_simp
    linear_combination -key
  refine ⟨s • P, ?_, fun x => ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin]
    refine isUnit_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ ?_) hPd)
    rintro hs0
    rw [hs0] at hcs
    simp at hcs
  · rw [← hPx, evalIn_smul, Matrix.smul_mulVec]
    rw [show (pureForm a b).evalIn K (s • (P.mulVec x)) = s ^ 2 * (pureForm a b).evalIn K (P.mulVec x) by
      rw [evalIn_pureForm_self, evalIn_pureForm_self]; simp only [Pi.smul_apply, smul_eq_mul]; ring]
    rw [hcs]

/-- **Every nondegenerate ternary form is similar to a pure norm form** (Voight, proof of
Corollary 5.2.6: $\langle w_0, w_1, w_2\rangle \sim w_0w_1w_2\langle w_0, w_1, w_2\rangle \simeq
\langle w_1w_2, w_0w_2, w_0w_1\rangle$): over a field with $2 \ne 0$, a ternary form $Q$ with
$\det H_Q \ne 0$ is similar to $\langle -a, -b, ab\rangle = \operatorname{nrd}|_{B^0}$ for
$B = (a, b \mid K)$, some $a, b \in K^\times$. -/
theorem exists_similar_pureForm (h2 : (2 : K) ≠ 0) (Q : QuadForm K 3) (hQ : Q.Nondegenerate) :
    ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧ Similar (pureForm a b) Q := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  set Q' := Q.toQuadraticFormIn K with hQ'
  have hpol := (QuadForm.nondegenerate_polarBilin_toQuadraticFormIn (K := K) hQ).1
  have hsep : (QuadraticMap.associated (R := K) Q').SeparatingLeft := by
    intro x hx
    refine hpol x fun y => ?_
    have := hx y
    rw [QuadraticMap.associated_apply] at this
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    have h' : ⅟(2 : K) * (Q' (x + y) - Q' x - Q' y) = 0 := this
    rcases mul_eq_zero.1 h' with h | h
    · exact absurd h (by rw [invOf_eq_inv]; exact inv_ne_zero h2)
    · exact h
  have key : ∀ k, Module.finrank K (Fin 3 → K) = k →
      ∃ w : Fin k → Kˣ, Q'.Equivalent (QuadraticMap.weightedSumSquares K w) := by
    intro k hk
    subst hk
    exact QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q' hsep
  obtain ⟨w, hw⟩ := key 3 (by simp)
  set w0 : K := ((w 0 : Kˣ) : K)
  set w1 : K := ((w 1 : Kˣ) : K)
  set w2 : K := ((w 2 : Kˣ) : K)
  have h0 : w0 ≠ 0 := (w 0).ne_zero
  have h1 : w1 ≠ 0 := (w 1).ne_zero
  have h2' : w2 ≠ 0 := (w 2).ne_zero
  -- the diagonal form ⟨w0, w1, w2⟩ is isometric to Q
  have hdiag : (QuadForm.diag ![w0, w1, w2]).IsometricIn K Q := by
    rw [QuadForm.isometricIn_iff_equivalent]
    have hEq : QuadraticMap.weightedSumSquares K w =
        (QuadForm.diag ![w0, w1, w2]).toQuadraticFormIn K := by
      ext x
      simp only [QuadForm.toQuadraticFormIn_apply, QuadForm.evalIn_diag,
        QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_three, Units.smul_def, smul_eq_mul]
      simp [w0, w1, w2, pow_two]
    rw [← hEq]
    exact hw
  refine ⟨-(w1 * w2), -(w0 * w2), by simp [h1, h2'], by simp [h0, h2'],
    Units.mk0 (w0 * w1 * w2)⁻¹ (by simp [h0, h1, h2']), ?_⟩
  refine QuadForm.isometricIn_trans K ⟨Matrix.diagonal ![w0, w1, 1], ?_, fun x => ?_⟩ hdiag
  · simp [Matrix.det_diagonal, Fin.prod_univ_three, h0, h1]
  · rw [evalIn_smul, evalIn_pureForm_self, QuadForm.evalIn_diag, Fin.sum_univ_three]
    simp only [Units.val_mk0, Matrix.mulVec_diagonal, Algebra.algebraMap_self, RingHom.id_apply]
    simp
    field_simp

/-- **Theorem 5.1.1, second bijection (Voight 2021)**: over a field $K$ with $2 \ne 0$, for
$a, b, a', b' \in K^\times$,
$$(a, b \mid K) \cong (a', b' \mid K) \iff \langle -a,-b,ab\rangle \text{ and } \langle -a',-b',a'b'\rangle
\text{ are similar},$$
and every nondegenerate ternary form is similar to some $\langle -a, -b, ab\rangle$
(`exists_similar_pureForm`). Together: $B \mapsto \operatorname{nrd}|_{B^0}$ is a bijection from
isomorphism classes of quaternion algebras $(a, b \mid K)$ to similarity classes of nondegenerate ternary
forms over $K$. Proved. -/
@[kb "voight2021" "Theorem 5.1.1, p. 65; Corollary 5.2.6, p. 68"]
theorem nonempty_algEquiv_iff_similar (h2 : (2 : K) ≠ 0) {a b a' b' : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha' : a' ≠ 0) (hb' : b' ≠ 0) :
    Nonempty (ℍ[K,a,b] ≃ₐ[K] ℍ[K,a',b']) ↔ Similar (pureForm a b) (pureForm a' b') := by
  rw [nonempty_algEquiv_iff_isometricIn h2 ha hb]
  refine ⟨fun h => ?_, isometricIn_of_similar h2 ha hb ha' hb'⟩
  obtain ⟨P, hP, hPx⟩ := h
  exact ⟨1, P, hP, fun x => by rw [evalIn_smul, Units.val_one, one_mul]; exact hPx x⟩

end PureForm

end QuadFormsKB.Voight
