/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.TernaryBadDVR
import QuadFormsKB.LocalDensity.HyperbolicNumbers
import QuadFormsKB.Witt.Bridge

/-!
# Splitting off a hyperbolic plane: Eichler transformations and the frame lemma for $L\perp\mathbb H$

**Layer:** an arbitrary commutative ring $A$ (the algebra), then a local ring (transitivity), then a discrete valuation
ring $R$ (densities; every residue characteristic, dyadic included).

Let $L$ be a quadratic form in $m$ variables over $A$ and $Q = L\perp\mathbb H$ the form in $m+2$ variables with
$Q(l, s, t) = L(l) + st$ (`orthSum L (hyperbolic A)`; the last two variables are the hyperbolic plane
$\mathbb H(s,t) = st$). Write $e = (0, 1, 0)$, $f = (0, 0, 1)$, $B$ for the bilinear form $B(x, y) = x^{\mathsf T}H_Qy$.

**Eichler transformations** (for $v\in A^m$): $E_v(l,s,t) = (l+tv,\ s-B_L(l,v)-L(v)t,\ t)$ and
$F_v(l,s,t) = (l+sv,\ s,\ t-B_L(l,v)-L(v)s)$, the swap $\sigma(l,s,t) = (l,t,s)$ and the scalings
$D_{c,c'}(l,s,t) = (l, cs, c't)$ with $cc'=1$ are isometries of $Q$ with explicit inverses (`Good`).

**Transitivity** (`exists_good_pair`): over a local ring, for every hyperbolic pair $(u, w)$ of $Q$
($Q(u) = Q(w) = 0$, $B(u,w) = 1$) there is such an isometry $g$ with $g(u) = e$, $g(w) = f$. No Witt cancellation and no
Jordan theory are used: if the $f$-coordinate (or the $e$-coordinate) of $u$ is a unit an Eichler map clears the
$L$-part, otherwise $B_L(l, l')$ is a unit for $w = (l', \cdot, \cdot)$ and $F_{l'}$ makes the $f$-coordinate a unit.

**The frame lemma** (`repCountForm_hypFrame`, `localDensityForm_hypFrame`): for $L$ over a discrete valuation ring with
$L\perp\mathbb H$ nondegenerate,
$$\beta_\pi(L\perp\mathbb H, L\perp\mathbb H) = \beta_\pi(L\perp\mathbb H, \mathbb H)\cdot\beta_\pi(L, L).$$
*Proof.* Orbit–stabilizer for the frame $(e, f)$ in $O(Q \bmod \pi^k)$ (`card_compMat_eq_frameOrbit_mul`): the orbit is every
representation of $\mathbb H$ mod $\pi^k$ (transitivity over the local ring $R/\pi^k$), and the stabilizer is
$\{\mathrm{diag}(X_L, 1, 1) : L\circ X_L = L\}$ (`stabHypEquiv`), because an isometry fixing $e$ and $f$ preserves
$\{e,f\}^\perp$, the $L$-coordinates.

This generalizes `Tamagawa.localDensityForm_frame` ($\langle m\rangle\perp T$) in the direction of an arbitrary first summand
(the second summand is the hyperbolic plane). Sources: Kitaoka 1993, §5.6 [unverified] (densities); the reduction
$\alpha(L\perp\mathbb H) = \alpha(L\perp\mathbb H, \mathbb H)\,\alpha(L)$ is standard; Eichler transformations: O'Meara 1963, §55
[unverified]. Indices are 0-based; the hyperbolic coordinates are $m$ and $m+1$.
-/

open Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.LocalDensity.HypFrame

open QuadForm QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR

section Coords

variable {A : Type*} [CommRing A] {m : ℕ}

/-- The vector $(l, s, t)\in A^{m+2}$. -/
def vec (l : Fin m → A) (s t : A) : Fin (m + 2) → A := Fin.append l ![s, t]

/-- The $L$-part of $x\in A^{m+2}$ (its first $m$ coordinates). -/
def lp (x : Fin (m + 2) → A) : Fin m → A := fun a => x (Fin.castAdd 2 a)

/-- The coordinate $s$ (index $m$). -/
def sp (x : Fin (m + 2) → A) : A := x (Fin.natAdd m 0)

/-- The coordinate $t$ (index $m+1$). -/
def tp (x : Fin (m + 2) → A) : A := x (Fin.natAdd m 1)

@[simp] theorem lp_vec (l : Fin m → A) (s t : A) : lp (vec l s t) = l := by
  ext a; simp [lp, vec]

@[simp] theorem sp_vec (l : Fin m → A) (s t : A) : sp (vec l s t) = s := by
  simp [sp, vec]

@[simp] theorem tp_vec (l : Fin m → A) (s t : A) : tp (vec l s t) = t := by
  simp [tp, vec]

theorem vec_eta (x : Fin (m + 2) → A) : vec (lp x) (sp x) (tp x) = x := by
  ext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp [vec, lp]
  · fin_cases b <;> simp [vec, sp, tp]

theorem ext_lst {x y : Fin (m + 2) → A} (h1 : lp x = lp y) (h2 : sp x = sp y) (h3 : tp x = tp y) : x = y := by
  rw [← vec_eta x, ← vec_eta y, h1, h2, h3]

@[simp] theorem lp_add (x y : Fin (m + 2) → A) : lp (x + y) = lp x + lp y := rfl
@[simp] theorem sp_add (x y : Fin (m + 2) → A) : sp (x + y) = sp x + sp y := rfl
@[simp] theorem tp_add (x y : Fin (m + 2) → A) : tp (x + y) = tp x + tp y := rfl
@[simp] theorem lp_smul (c : A) (x : Fin (m + 2) → A) : lp (c • x) = c • lp x := rfl
@[simp] theorem sp_smul (c : A) (x : Fin (m + 2) → A) : sp (c • x) = c * sp x := rfl
@[simp] theorem tp_smul (c : A) (x : Fin (m + 2) → A) : tp (c • x) = c * tp x := rfl
@[simp] theorem lp_zero : lp (0 : Fin (m + 2) → A) = 0 := rfl
@[simp] theorem sp_zero : sp (0 : Fin (m + 2) → A) = 0 := rfl
@[simp] theorem tp_zero : tp (0 : Fin (m + 2) → A) = 0 := rfl

/-- The bilinear form $B_P(x, y) = x^{\mathsf T}H_Py$. -/
def bil {n : ℕ} (P : QuadForm A n) (x y : Fin n → A) : A := x ⬝ᵥ (P.hessian *ᵥ y)

theorem eval_add_bil {n : ℕ} (P : QuadForm A n) (x y : Fin n → A) :
    P.eval (x + y) = P.eval x + P.eval y + bil P x y := by
  have := eval_polar P x y
  unfold bil; rw [← this]; ring

theorem bil_add_left {n : ℕ} (P : QuadForm A n) (x x' y : Fin n → A) :
    bil P (x + x') y = bil P x y + bil P x' y := by simp [bil, add_dotProduct]

theorem bil_smul_left {n : ℕ} (P : QuadForm A n) (c : A) (x y : Fin n → A) :
    bil P (c • x) y = c * bil P x y := by simp [bil, smul_dotProduct]

theorem bil_smul_right {n : ℕ} (P : QuadForm A n) (c : A) (x y : Fin n → A) :
    bil P x (c • y) = c * bil P x y := by simp [bil, mulVec_smul, dotProduct_smul]

theorem bil_neg_right {n : ℕ} (P : QuadForm A n) (x y : Fin n → A) : bil P x (-y) = - bil P x y := by
  simp [bil, mulVec_neg, dotProduct_neg]

theorem bil_zero_left {n : ℕ} (P : QuadForm A n) (y : Fin n → A) : bil P 0 y = 0 := by simp [bil]

theorem bil_zero_right {n : ℕ} (P : QuadForm A n) (y : Fin n → A) : bil P y 0 = 0 := by simp [bil]

theorem bil_self {n : ℕ} (P : QuadForm A n) (x : Fin n → A) : bil P x x = 2 * P.eval x :=
  dotProduct_hessian_self P x

theorem bil_comm {n : ℕ} (P : QuadForm A n) (x y : Fin n → A) : bil P x y = bil P y x := by
  have h1 := eval_add_bil P x y
  have h2 := eval_add_bil P y x
  rw [add_comm y x] at h2
  linear_combination h2 - h1

theorem eval_smul' {n : ℕ} (P : QuadForm A n) (c : A) (x : Fin n → A) : P.eval (c • x) = c ^ 2 * P.eval x := by
  rw [eval_eq_dotProduct', eval_eq_dotProduct']
  simp [mulVec_smul, smul_dotProduct, dotProduct_smul]; ring

theorem eval_neg' {n : ℕ} (P : QuadForm A n) (x : Fin n → A) : P.eval (-x) = P.eval x := by
  have := eval_smul' P (-1) x
  simpa using this

theorem eval_zero' {n : ℕ} (P : QuadForm A n) : P.eval 0 = 0 := by
  simpa using eval_smul' P 0 0

/-- The form $Q = L\perp\mathbb H$ in $m+2$ variables. -/
abbrev hypExt (L : QuadForm A m) : QuadForm A (m + 2) := orthSum L (hyperbolic A)

theorem evalIn_hyperbolic' (y : Fin 2 → A) : (hyperbolic A).evalIn A y = y 0 * y 1 := by
  simp [QuadForm.evalIn, hyperbolic, QuadForm.ofUpper, Fin.sum_univ_two]

theorem eval_vec (L : QuadForm A m) (l : Fin m → A) (s t : A) :
    (hypExt L).eval (vec l s t) = L.eval l + s * t := by
  unfold hypExt
  rw [QuadForm.eval, evalIn_orthSum, evalIn_hyperbolic']
  simp [vec, QuadForm.eval]

theorem eval_hypExt (L : QuadForm A m) (x : Fin (m + 2) → A) :
    (hypExt L).eval x = L.eval (lp x) + sp x * tp x := by
  conv_lhs => rw [← vec_eta x]
  exact eval_vec L _ _ _

theorem vec_add (l l' : Fin m → A) (s s' t t' : A) :
    vec l s t + vec l' s' t' = vec (l + l') (s + s') (t + t') := ext_lst (by simp) (by simp) (by simp)

theorem bil_hypExt (L : QuadForm A m) (x y : Fin (m + 2) → A) :
    bil (hypExt L) x y = bil L (lp x) (lp y) + sp x * tp y + sp y * tp x := by
  have h := eval_add_bil (hypExt L) x y
  rw [eval_hypExt, eval_hypExt, eval_hypExt, lp_add, sp_add, tp_add, eval_add_bil L] at h
  linear_combination -h

/-- $e = (0, 1, 0)$. -/
def eV (m : ℕ) : Fin (m + 2) → A := vec 0 1 0
/-- $f = (0, 0, 1)$. -/
def fV (m : ℕ) : Fin (m + 2) → A := vec 0 0 1

end Coords

/-! ### Good isometries: isometries of $Q$ with a two-sided inverse -/

section Good

variable {A : Type*} [CommRing A] {m : ℕ} (L : QuadForm A m)

/-- An isometry of $Q = L\perp\mathbb H$ given by a linear map with a two-sided inverse. -/
def Good (g : (Fin (m + 2) → A) →ₗ[A] (Fin (m + 2) → A)) : Prop :=
  (∀ x, (hypExt L).eval (g x) = (hypExt L).eval x) ∧
    ∃ g' : (Fin (m + 2) → A) →ₗ[A] (Fin (m + 2) → A), (∀ x, g' (g x) = x) ∧ ∀ x, g (g' x) = x

theorem Good.comp {g h : (Fin (m + 2) → A) →ₗ[A] (Fin (m + 2) → A)} (hg : Good L g) (hh : Good L h) :
    Good L (g ∘ₗ h) := by
  obtain ⟨hg1, g', hg2, hg3⟩ := hg
  obtain ⟨hh1, h', hh2, hh3⟩ := hh
  refine ⟨fun x => by simp [hg1, hh1], h' ∘ₗ g', fun x => by simp [hg2, hh2], fun x => by simp [hg3, hh3]⟩

theorem Good.bil {g : (Fin (m + 2) → A) →ₗ[A] (Fin (m + 2) → A)} (hg : Good L g) (x y : Fin (m + 2) → A) :
    bil (hypExt L) (g x) (g y) = bil (hypExt L) x y := by
  have h1 := eval_add_bil (hypExt L) (g x) (g y)
  have h2 := eval_add_bil (hypExt L) x y
  rw [← map_add, hg.1, hg.1, hg.1] at h1
  linear_combination h2 - h1

/-- The Eichler transformation $E_v(l,s,t) = (l+tv,\ s-B_L(l,v)-L(v)t,\ t)$. -/
def eE (v : Fin m → A) : (Fin (m + 2) → A) →ₗ[A] (Fin (m + 2) → A) where
  toFun x := vec (lp x + tp x • v) (sp x - bil L (lp x) v - L.eval v * tp x) (tp x)
  map_add' x y := by
    rw [vec_add]
    congr 1
    · simp [add_smul]; abel
    · simp [bil_add_left]; ring
  map_smul' c x := by
    refine ext_lst ?_ ?_ ?_
    · simp [smul_add, mul_smul]
    · simp [bil_smul_left]; ring
    · simp

/-- The Eichler transformation $F_v(l,s,t) = (l+sv,\ s,\ t-B_L(l,v)-L(v)s)$. -/
def eF (v : Fin m → A) : (Fin (m + 2) → A) →ₗ[A] (Fin (m + 2) → A) where
  toFun x := vec (lp x + sp x • v) (sp x) (tp x - bil L (lp x) v - L.eval v * sp x)
  map_add' x y := by
    rw [vec_add]
    congr 1
    · simp [add_smul]; abel
    · simp [bil_add_left]; ring
  map_smul' c x := by
    refine ext_lst ?_ ?_ ?_
    · simp [smul_add, mul_smul]
    · simp
    · simp [bil_smul_left]; ring

/-- The swap $\sigma(l,s,t) = (l,t,s)$. -/
def eS : (Fin (m + 2) → A) →ₗ[A] (Fin (m + 2) → A) where
  toFun x := vec (lp x) (tp x) (sp x)
  map_add' x y := by rw [vec_add]; rfl
  map_smul' c x := ext_lst (by simp) (by simp) (by simp)

/-- The scaling $D_{c,c'}(l,s,t) = (l, cs, c't)$. -/
def eD (c c' : A) : (Fin (m + 2) → A) →ₗ[A] (Fin (m + 2) → A) where
  toFun x := vec (lp x) (c * sp x) (c' * tp x)
  map_add' x y := by rw [vec_add]; simp [mul_add]
  map_smul' a x := ext_lst (by simp) (by simp; ring) (by simp; ring)

@[simp] theorem eE_apply (v : Fin m → A) (x : Fin (m + 2) → A) :
    eE L v x = vec (lp x + tp x • v) (sp x - bil L (lp x) v - L.eval v * tp x) (tp x) := rfl
@[simp] theorem eF_apply (v : Fin m → A) (x : Fin (m + 2) → A) :
    eF L v x = vec (lp x + sp x • v) (sp x) (tp x - bil L (lp x) v - L.eval v * sp x) := rfl
@[simp] theorem eS_apply (x : Fin (m + 2) → A) : (eS : (Fin (m + 2) → A) →ₗ[A] _) x = vec (lp x) (tp x) (sp x) := rfl
@[simp] theorem eD_apply (c c' : A) (x : Fin (m + 2) → A) :
    (eD c c' : (Fin (m + 2) → A) →ₗ[A] _) x = vec (lp x) (c * sp x) (c' * tp x) := rfl

theorem eval_add_smul_L (l v : Fin m → A) (t : A) :
    L.eval (l + t • v) = L.eval l + t * bil L l v + t ^ 2 * L.eval v := by
  rw [eval_add_bil, eval_smul', bil_smul_right]; ring

theorem eE_inv (v : Fin m → A) (x : Fin (m + 2) → A) : eE L (-v) (eE L v x) = x := by
  refine ext_lst ?_ ?_ ?_
  · simp
  · simp only [eE_apply, lp_vec, sp_vec, tp_vec, eval_neg', bil_neg_right, bil_add_left, bil_smul_left, bil_self]
    ring
  · simp

theorem eF_inv (v : Fin m → A) (x : Fin (m + 2) → A) : eF L (-v) (eF L v x) = x := by
  refine ext_lst ?_ ?_ ?_
  · simp
  · simp
  · simp only [eF_apply, lp_vec, sp_vec, tp_vec, eval_neg', bil_neg_right, bil_add_left, bil_smul_left, bil_self]
    ring

theorem good_eE (v : Fin m → A) : Good L (eE L v) := by
  refine ⟨fun x => ?_, eE L (-v), eE_inv L v, fun x => by simpa using eE_inv L (-v) x⟩
  rw [eE_apply, eval_vec, eval_hypExt, eval_add_smul_L]; ring

theorem good_eF (v : Fin m → A) : Good L (eF L v) := by
  refine ⟨fun x => ?_, eF L (-v), eF_inv L v, fun x => by simpa using eF_inv L (-v) x⟩
  rw [eF_apply, eval_vec, eval_hypExt, eval_add_smul_L]; ring

theorem good_eS : Good L (eS : (Fin (m + 2) → A) →ₗ[A] _) := by
  refine ⟨fun x => ?_, eS, fun x => ?_, fun x => ?_⟩
  · rw [eS_apply, eval_vec, eval_hypExt]; ring
  · exact ext_lst (by simp) (by simp) (by simp)
  · exact ext_lst (by simp) (by simp) (by simp)

theorem good_eD {c c' : A} (h : c * c' = 1) : Good L (eD c c' : (Fin (m + 2) → A) →ₗ[A] _) := by
  refine ⟨fun x => ?_, eD c' c, fun x => ?_, fun x => ?_⟩
  · rw [eD_apply, eval_vec, eval_hypExt]; linear_combination (sp x * tp x) * h
  · refine ext_lst (by simp) ?_ ?_
    · simp; linear_combination (sp x) * h
    · simp; linear_combination (tp x) * h
  · refine ext_lst (by simp) ?_ ?_
    · simp; linear_combination (sp x) * h
    · simp; linear_combination (tp x) * h

theorem bil_eV (x : Fin (m + 2) → A) : bil (hypExt L) (eV m) x = tp x := by
  rw [bil_hypExt]; simp [eV, bil_zero_left]

end Good

/-! ### Transitivity on hyperbolic pairs over a local ring -/

section Transitive

variable {A : Type*} [CommRing A] [IsLocalRing A] {m : ℕ} (L : QuadForm A m)

/-- If the $f$-coordinate of an isotropic $u$ is a unit, a good isometry maps $u$ to $e$. -/
theorem exists_good_of_tp_unit (u : Fin (m + 2) → A) (hu : (hypExt L).eval u = 0) (hb : IsUnit (tp u)) :
    ∃ g, Good L g ∧ g u = eV m := by
  obtain ⟨b, hb'⟩ := hb
  have hQ : L.eval (lp u) + sp u * tp u = 0 := by rw [← eval_hypExt]; exact hu
  refine ⟨eS ∘ₗ (eD (tp u) (↑b⁻¹ : A) ∘ₗ eE L (-((↑b⁻¹ : A) • lp u))),
    (good_eS L).comp L ((good_eD L (by rw [← hb']; simp)).comp L (good_eE L _)), ?_⟩
  have hbinv : (↑b⁻¹ : A) * tp u = 1 := by rw [← hb']; simp
  refine ext_lst ?_ ?_ ?_
  · simp only [LinearMap.comp_apply, eE_apply, eD_apply, eS_apply, lp_vec, eV]
    rw [smul_neg, smul_smul, mul_comm, hbinv, one_smul, add_neg_cancel]
  · simp only [LinearMap.comp_apply, eE_apply, eD_apply, eS_apply, sp_vec, tp_vec, eV]
    exact hbinv
  · simp only [LinearMap.comp_apply, eE_apply, eD_apply, eS_apply, sp_vec, tp_vec, lp_vec, eV]
    rw [eval_neg', eval_smul', bil_neg_right, bil_smul_right, bil_self]
    linear_combination hQ + (2 * L.eval (lp u)) * hbinv - L.eval (lp u) * ((↑b⁻¹ : A) * tp u + 1) * hbinv


/-- If the $e$-coordinate of an isotropic $u$ is a unit, a good isometry maps $u$ to $e$. -/
theorem exists_good_of_sp_unit (u : Fin (m + 2) → A) (hu : (hypExt L).eval u = 0) (ha : IsUnit (sp u)) :
    ∃ g, Good L g ∧ g u = eV m := by
  obtain ⟨a, ha'⟩ := ha
  have hQ : L.eval (lp u) + sp u * tp u = 0 := by rw [← eval_hypExt]; exact hu
  have hainv : (↑a⁻¹ : A) * sp u = 1 := by rw [← ha']; simp
  refine ⟨eD (↑a⁻¹ : A) (sp u) ∘ₗ eF L (-((↑a⁻¹ : A) • lp u)),
    (good_eD L hainv).comp L (good_eF L _), ?_⟩
  refine ext_lst ?_ ?_ ?_
  · simp only [LinearMap.comp_apply, eF_apply, eD_apply, lp_vec, eV]
    rw [smul_neg, smul_smul, mul_comm, hainv, one_smul, add_neg_cancel]
  · simp only [LinearMap.comp_apply, eF_apply, eD_apply, sp_vec, eV]
    exact hainv
  · simp only [LinearMap.comp_apply, eF_apply, eD_apply, sp_vec, tp_vec, lp_vec, eV]
    rw [eval_neg', eval_smul', bil_neg_right, bil_smul_right, bil_self]
    linear_combination hQ + (2 * L.eval (lp u)) * hainv - L.eval (lp u) * ((↑a⁻¹ : A) * sp u + 1) * hainv

theorem nonunit_add {a b : A} (ha : ¬ IsUnit a) (hb : ¬ IsUnit b) : ¬ IsUnit (a + b) := by
  intro h
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h' | h'
  · exact ha h'
  · exact hb h'

theorem nonunit_mul_left {a : A} (b : A) (ha : ¬ IsUnit a) : ¬ IsUnit (b * a) := fun h =>
  ha (isUnit_of_mul_isUnit_right h)

/-- **Transitivity on isotropic vectors with a partner** (local ring): if $Q(u) = 0$ and $B(u, y) = 1$ for some $y$,
a good isometry maps $u$ to $e$. -/
theorem exists_good_vec (u y : Fin (m + 2) → A) (hu : (hypExt L).eval u = 0) (hy : bil (hypExt L) u y = 1) :
    ∃ g, Good L g ∧ g u = eV m := by
  by_cases hb : IsUnit (tp u)
  · exact exists_good_of_tp_unit L u hu hb
  by_cases ha : IsUnit (sp u)
  · exact exists_good_of_sp_unit L u hu ha
  -- neither coordinate is a unit: then `B_L(l, lp y)` is a unit
  rw [bil_hypExt] at hy
  have hc : IsUnit (bil L (lp u) (lp y)) := by
    by_contra hc
    have : ¬ IsUnit (bil L (lp u) (lp y) + sp u * tp y + sp y * tp u) :=
      nonunit_add (nonunit_add hc (by rw [mul_comm]; exact nonunit_mul_left _ ha)) (nonunit_mul_left _ hb)
    rw [hy] at this
    exact this isUnit_one
  set u' := eF L (lp y) u with hu'
  have hu'0 : (hypExt L).eval u' = 0 := by rw [hu', (good_eF L _).1, hu]
  have hb' : IsUnit (tp u') := by
    rw [hu', eF_apply, tp_vec]
    by_contra h
    have e : bil L (lp u) (lp y) = tp u - (tp u - bil L (lp u) (lp y) - L.eval (lp y) * sp u) -
        L.eval (lp y) * sp u := by ring
    have : ¬ IsUnit (tp u - (tp u - bil L (lp u) (lp y) - L.eval (lp y) * sp u) - L.eval (lp y) * sp u) := by
      rw [sub_eq_add_neg, sub_eq_add_neg]
      refine nonunit_add (nonunit_add hb ?_) ?_
      · rw [← neg_one_mul]; exact nonunit_mul_left _ h
      · rw [← neg_one_mul]; exact nonunit_mul_left _ (nonunit_mul_left _ ha)
    rw [← e] at this
    exact this hc
  obtain ⟨g, hg, hgu⟩ := exists_good_of_tp_unit L u' hu'0 hb'
  exact ⟨g ∘ₗ eF L (lp y), hg.comp L (good_eF L _), by simpa [hu'] using hgu⟩

/-- **Transitivity on hyperbolic pairs** (local ring): for $Q(u) = Q(w) = 0$, $B(u, w) = 1$ a good isometry maps
$(u, w)$ to $(e, f)$. -/
theorem exists_good_pair (u w : Fin (m + 2) → A) (hu : (hypExt L).eval u = 0) (hw : (hypExt L).eval w = 0)
    (huw : bil (hypExt L) u w = 1) : ∃ g, Good L g ∧ g u = eV m ∧ g w = fV m := by
  obtain ⟨g, hg, hgu⟩ := exists_good_vec L u w hu huw
  set w₁ := g w with hw₁
  have ht : tp w₁ = 1 := by rw [← bil_eV L, ← hgu, hw₁, hg.bil L, huw]
  have hQ : L.eval (lp w₁) + sp w₁ * tp w₁ = 0 := by rw [← eval_hypExt, hw₁, hg.1, hw]
  refine ⟨eE L (-lp w₁) ∘ₗ g, (good_eE L _).comp L hg, ?_, ?_⟩
  · rw [LinearMap.comp_apply, hgu]
    refine ext_lst ?_ ?_ ?_ <;> simp [eV, bil_zero_left]
  · rw [LinearMap.comp_apply, ← hw₁]
    refine ext_lst ?_ ?_ ?_
    · simp [ht, fV]
    · simp only [eE_apply, sp_vec, fV]
      rw [eval_neg', bil_neg_right, bil_self, ht]
      linear_combination hQ - sp w₁ * ht
    · simp [ht, fV]

end Transitive


/-! ### The frame $(e, f)$, its orbit and its stabilizer -/

section Frame

variable {A : Type*} [CommRing A] {m : ℕ} (L : QuadForm A m)

/-- The frame $(e, f)$ of the hyperbolic plane in $A^{m+2}$. -/
def frameH (A : Type*) [CommRing A] (m : ℕ) : Matrix (Fin (m + 2)) (Fin 2) A :=
  Matrix.of fun i j => (![eV m, fV m] j) i

/-- Column $j$ of a matrix. -/
def col {n r : ℕ} (Y : Matrix (Fin n) (Fin r) A) (j : Fin r) : Fin n → A := fun i => Y i j

theorem col_mul {n r : ℕ} (X : Matrix (Fin n) (Fin n) A) (Y : Matrix (Fin n) (Fin r) A) (j : Fin r) :
    col (X * Y) j = X *ᵥ col Y j := by
  ext i; simp [col, Matrix.mul_apply, mulVec, dotProduct]

@[simp] theorem col_frameH_zero : col (frameH A m) 0 = eV m := rfl
@[simp] theorem col_frameH_one : col (frameH A m) 1 = fV m := rfl

theorem frameH_mulVec (y : Fin 2 → A) : frameH A m *ᵥ y = vec 0 (y 0) (y 1) := by
  have : frameH A m *ᵥ y = y 0 • eV m + y 1 • fV m := by
    ext i; simp [frameH, mulVec, dotProduct, Fin.sum_univ_two]; ring
  rw [this]
  refine ext_lst ?_ ?_ ?_ <;> simp [eV, fV]

theorem eval_hyperbolic' (y : Fin 2 → A) : (hyperbolic A).eval y = y 0 * y 1 :=
  evalIn_hyperbolic' y

theorem compMat_frameH : (hypExt L).compMat (frameH A m) = hyperbolic A :=
  eq_of_eval_eq fun y => by
    rw [eval_compMat, frameH_mulVec, eval_vec, eval_zero', eval_hyperbolic']; ring

/-- **Representations of $\mathbb H$ are hyperbolic pairs:** $P\circ Y = \mathbb H$ iff the columns $u, w$ of $Y$ satisfy
$P(u) = P(w) = 0$, $B_P(u, w) = 1$. -/
theorem compMat_eq_hyperbolic_iff {n : ℕ} (P : QuadForm A n) (Y : Matrix (Fin n) (Fin 2) A) :
    P.compMat Y = hyperbolic A ↔ P.eval (col Y 0) = 0 ∧ P.eval (col Y 1) = 0 ∧ bil P (col Y 0) (col Y 1) = 1 := by
  have c00 : (P.compMat Y).coeff 0 0 = P.eval (col Y 0) := by rw [compMat_coeff]; rfl
  have c11 : (P.compMat Y).coeff 1 1 = P.eval (col Y 1) := by rw [compMat_coeff]; rfl
  have c01 : (P.compMat Y).coeff 0 1 = bil P (col Y 0) (col Y 1) := by rw [compMat_coeff]; rfl
  have h00 : (hyperbolic A).coeff 0 0 = 0 := by simp [hyperbolic, QuadForm.ofUpper]
  have h11 : (hyperbolic A).coeff 1 1 = 0 := by simp [hyperbolic, QuadForm.ofUpper]
  have h01 : (hyperbolic A).coeff 0 1 = 1 := by simp [hyperbolic, QuadForm.ofUpper]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rw [← c00, h, h00]
    · rw [← c11, h, h11]
    · rw [← c01, h, h01]
  · rintro ⟨h0, h1, h2⟩
    refine ext_upper fun i j hij => ?_
    fin_cases i <;> fin_cases j
    · simpa [c00, h00] using h0
    · simpa [c01, h01] using h2
    · exact absurd hij (by decide)
    · simpa [c11, h11] using h1

theorem eval_mulVec_of_compMat {n : ℕ} {P : QuadForm A n} {X : Matrix (Fin n) (Fin n) A} (hX : P.compMat X = P)
    (x : Fin n → A) : P.eval (X *ᵥ x) = P.eval x := by
  rw [← eval_compMat, hX]

theorem bil_mulVec_of_compMat {n : ℕ} {P : QuadForm A n} {X : Matrix (Fin n) (Fin n) A} (hX : P.compMat X = P)
    (x y : Fin n → A) : bil P (X *ᵥ x) (X *ᵥ y) = bil P x y := by
  have h1 := eval_add_bil P (X *ᵥ x) (X *ᵥ y)
  have h2 := eval_add_bil P x y
  rw [← mulVec_add, eval_mulVec_of_compMat hX, eval_mulVec_of_compMat hX, eval_mulVec_of_compMat hX] at h1
  linear_combination h2 - h1

theorem matrix_eq_toMatrix' {n : ℕ} (X : Matrix (Fin n) (Fin n) A) (g : (Fin n → A) →ₗ[A] (Fin n → A))
    (h : ∀ x, X *ᵥ x = g x) : X = LinearMap.toMatrix' g := by
  rw [← LinearMap.toMatrix'_toLin' X]
  congr 1
  exact LinearMap.ext fun x => by rw [Matrix.toLin'_apply, h]

/-- **The orbit of the frame is every representation of $\mathbb H$** (local ring; every isometry invertible). -/
theorem frameOrbit_iff [IsLocalRing A]
    (hinv : ∀ X : Matrix (Fin (m + 2)) (Fin (m + 2)) A, (hypExt L).compMat X = hypExt L → IsUnit X.det)
    (Y : Matrix (Fin (m + 2)) (Fin 2) A) :
    (∃ X : Matrix (Fin (m + 2)) (Fin (m + 2)) A, (hypExt L).compMat X = hypExt L ∧ X * frameH A m = Y) ↔
      (hypExt L).compMat Y = hyperbolic A := by
  constructor
  · rintro ⟨X, hX, rfl⟩
    rw [← compMat_mul, hX, compMat_frameH]
  · intro hY
    obtain ⟨h0, h1, h01⟩ := (compMat_eq_hyperbolic_iff _ Y).1 hY
    obtain ⟨g, hg, hgu, hgw⟩ := exists_good_pair L (col Y 0) (col Y 1) h0 h1 h01
    set X := LinearMap.toMatrix' g with hXdef
    have hX : (hypExt L).compMat X = hypExt L :=
      eq_of_eval_eq fun x => by rw [eval_compMat, hXdef, LinearMap.toMatrix'_mulVec, hg.1]
    have hu := hinv X hX
    have hXY : X * Y = frameH A m := by
      ext i j
      have hc : ∀ j, col (X * Y) j = col (frameH A m) j := by
        intro j
        rw [col_mul, hXdef, LinearMap.toMatrix'_mulVec]
        fin_cases j
        · simpa using hgu
        · simpa using hgw
      exact congrFun (hc j) i
    refine ⟨X⁻¹, ?_, ?_⟩
    · conv_lhs => rw [← hX]
      rw [compMat_mul, mul_nonsing_inv _ hu, compMat_one]
    · rw [← hXY, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]

theorem bil_fV (x : Fin (m + 2) → A) : bil (hypExt L) (fV m) x = sp x := by
  rw [bil_hypExt]; simp [fV, bil_zero_left]

/-- The block $X_L$ of a matrix on $A^{m+2}$ (rows and columns $0, \dots, m-1$). -/
def blockL (X : Matrix (Fin (m + 2)) (Fin (m + 2)) A) : Matrix (Fin m) (Fin m) A :=
  Matrix.of fun a b => X (Fin.castAdd 2 a) (Fin.castAdd 2 b)

theorem lp_mulVec_vec (X : Matrix (Fin (m + 2)) (Fin (m + 2)) A) (l : Fin m → A) :
    lp (X *ᵥ vec l 0 0) = blockL X *ᵥ l := by
  ext a
  simp [lp, blockL, mulVec, dotProduct, Fin.sum_univ_add, vec]

/-- The block-diagonal map $\mathrm{diag}(X_L, 1, 1)$. -/
def blkMap (XL : Matrix (Fin m) (Fin m) A) : (Fin (m + 2) → A) →ₗ[A] (Fin (m + 2) → A) where
  toFun x := vec (XL *ᵥ lp x) (sp x) (tp x)
  map_add' x y := by rw [vec_add]; simp [mulVec_add]
  map_smul' c x := ext_lst (by simp [mulVec_smul]) (by simp) (by simp)

@[simp] theorem blkMap_apply (XL : Matrix (Fin m) (Fin m) A) (x : Fin (m + 2) → A) :
    blkMap XL x = vec (XL *ᵥ lp x) (sp x) (tp x) := rfl

theorem decomp (x : Fin (m + 2) → A) : x = vec (lp x) 0 0 + sp x • eV m + tp x • fV m :=
  ext_lst (by simp [eV, fV]) (by simp [eV, fV]) (by simp [eV, fV])

/-- **The stabilizer of the frame** is $\{\mathrm{diag}(X_L, 1, 1) : L\circ X_L = L\}$. -/
def stabHypEquiv :
    {X : Matrix (Fin (m + 2)) (Fin (m + 2)) A // (hypExt L).compMat X = hypExt L ∧ X * frameH A m = frameH A m} ≃
      {XL : Matrix (Fin m) (Fin m) A // L.compMat XL = L} where
  toFun X := ⟨blockL X.1, by
    obtain ⟨hQ, hF⟩ := X.2
    have he : X.1 *ᵥ eV m = eV m := by rw [← col_frameH_zero, ← col_mul, hF]
    have hf : X.1 *ᵥ fV m = fV m := by rw [← col_frameH_one, ← col_mul, hF]
    refine eq_of_eval_eq fun l => ?_
    have hs : sp (X.1 *ᵥ vec l 0 0) = 0 := by
      rw [← bil_fV L, ← hf, bil_mulVec_of_compMat hQ, bil_fV, sp_vec]
    have ht : tp (X.1 *ᵥ vec l 0 0) = 0 := by
      rw [← bil_eV L, ← he, bil_mulVec_of_compMat hQ, bil_eV, tp_vec]
    have h := eval_mulVec_of_compMat hQ (vec l 0 0)
    rw [eval_hypExt, hs, ht, lp_mulVec_vec, eval_vec] at h
    rw [eval_compMat]; simpa using h⟩
  invFun XL := ⟨LinearMap.toMatrix' (blkMap XL.1), by
    refine ⟨eq_of_eval_eq fun x => ?_, ?_⟩
    · rw [eval_compMat, LinearMap.toMatrix'_mulVec, blkMap_apply, eval_vec, eval_hypExt, ← eval_compMat, XL.2]
    · ext i j
      have hc : ∀ j, col (LinearMap.toMatrix' (blkMap XL.1) * frameH A m) j = col (frameH A m) j := by
        intro j
        rw [col_mul, LinearMap.toMatrix'_mulVec]
        fin_cases j
        · simp only [col_frameH_zero]
          exact ext_lst (by simp [eV]) (by simp [eV]) (by simp [eV])
        · simp only [col_frameH_one]
          exact ext_lst (by simp [fV]) (by simp [fV]) (by simp [fV])
      exact congrFun (hc j) i⟩
  left_inv X := by
    obtain ⟨hQ, hF⟩ := X.2
    have he : X.1 *ᵥ eV m = eV m := by rw [← col_frameH_zero, ← col_mul, hF]
    have hf : X.1 *ᵥ fV m = fV m := by rw [← col_frameH_one, ← col_mul, hF]
    apply Subtype.ext
    symm
    refine matrix_eq_toMatrix' _ _ fun x => ?_
    have hs : ∀ l, sp (X.1 *ᵥ vec l 0 0) = 0 := fun l => by
      rw [← bil_fV L, ← hf, bil_mulVec_of_compMat hQ, bil_fV, sp_vec]
    have ht : ∀ l, tp (X.1 *ᵥ vec l 0 0) = 0 := fun l => by
      rw [← bil_eV L, ← he, bil_mulVec_of_compMat hQ, bil_eV, tp_vec]
    have hv : ∀ l, X.1 *ᵥ vec l 0 0 = vec (blockL X.1 *ᵥ l) 0 0 := fun l =>
      ext_lst (by rw [lp_mulVec_vec, lp_vec]) (by rw [hs, sp_vec]) (by rw [ht, tp_vec])
    conv_lhs => rw [decomp x]
    rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, he, hf, hv, blkMap_apply]
    exact ext_lst (by simp [eV, fV]) (by simp [eV, fV]) (by simp [eV, fV])
  right_inv XL := by
    apply Subtype.ext
    ext a b
    simp only [blockL, Matrix.of_apply, LinearMap.toMatrix'_apply, blkMap_apply, vec, Fin.append_left]
    have : lp (Pi.single (Fin.castAdd 2 b) (1 : A) : Fin (m + 2) → A) = Pi.single b 1 := by
      ext c
      simp [lp, Pi.single_apply, Fin.castAdd_inj]
    rw [this, mulVec_single_one]
    rfl

end Frame


/-! ### The frame lemma over a discrete valuation ring -/

section Density

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {m : ℕ}

theorem map_hypExt {B : Type*} [CommRing B] (f : R →+* B) (L : QuadForm R m) :
    (hypExt L).map f = hypExt (L.map f) := by
  unfold hypExt
  rw [← hyperbolic_map_ring f]
  ext i j
  simp only [QuadForm.map, QuadForm.orthSum, QuadForm.ofUpper, Matrix.map_apply, Matrix.of_apply]
  split_ifs
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
      simp
  · exact map_zero f

theorem hyperbolic_nondegenerate : (hyperbolic R).Nondegenerate := by
  have : (hyperbolic R).hessian.det = -1 := by
    simp [QuadForm.hessian, hyperbolic, QuadForm.ofUpper, Matrix.det_fin_two]
  rw [QuadForm.Nondegenerate, this]; exact neg_ne_zero.mpr one_ne_zero

/-- **The frame count at level $\pi^k$** ($k > d = \mathrm{ord}_\pi\det H_Q$, $Q = L\perp\mathbb H$):
$A_{\pi^k}(Q, Q) = A_{\pi^k}(Q, \mathbb H)\cdot A_{\pi^k}(L, L)$. -/
theorem repCountForm_hypFrame [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π) (L : QuadForm R m)
    {d k : ℕ} (hd : π ^ d ∣ (hypExt L).hessian.det) (hd' : ¬ π ^ (d + 1) ∣ (hypExt L).hessian.det) (hdk : d < k) :
    repCountForm (hypExt L) (hypExt L) π k = repCountForm (hypExt L) (hyperbolic R) π k * repCountForm L L π k := by
  have := finite_quot_pow π hπ k
  have hk : 0 < k := by omega
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ k}) with hmk
  have hne : Ideal.span {π ^ k} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact fun h => hπ.not_isUnit (isUnit_of_dvd_unit (dvd_pow_self π hk.ne') h)
  haveI : Nontrivial (R ⧸ Ideal.span {π ^ k}) := Ideal.Quotient.nontrivial_iff.mpr hne
  haveI : IsLocalRing (R ⧸ Ideal.span {π ^ k}) := IsLocalRing.of_surjective' mk Ideal.Quotient.mk_surjective
  have hinv : ∀ X, (hypExt (L.map mk)).compMat X = hypExt (L.map mk) → IsUnit X.det := fun X hX =>
    isUnit_det_of_compMat_eq (hypExt L) π hπ d k hd hd' hdk X (by rw [map_hypExt]; exact hX)
  unfold repCountForm
  rw [map_hypExt, hyperbolic_map_ring, Tamagawa.card_compMat_eq_frameOrbit_mul _ hinv (frameH _ m)]
  congr 1
  · unfold Tamagawa.frameOrbit
    exact Nat.card_congr (Equiv.subtypeEquivRight (frameOrbit_iff _ hinv))
  · exact Nat.card_congr (stabHypEquiv _)

theorem exponent_hypFrame (m : ℕ) :
    (m + 2) * (m + 2) - (m + 2) * (m + 2 + 1) / 2 = ((m + 2) * 2 - 2 * (2 + 1) / 2) + (m * m - m * (m + 1) / 2) := by
  have h1 : (m + 2) * (m + 2 + 1) = m * (m + 1) + 2 * (2 * m + 3) := by ring
  have h2 : (m + 2) * (m + 2 + 1) / 2 = m * (m + 1) / 2 + (2 * m + 3) := by
    rw [h1, Nat.add_mul_div_left _ _ (by norm_num)]
  have h3 : m * (m + 1) / 2 ≤ m * m := by
    apply Nat.div_le_of_le_mul
    nlinarith
  have h4 : (m + 2) * (m + 2) = m * m + 4 * m + 4 := by ring
  rw [h2, h4]
  omega

/-- **The frame lemma for $L\perp\mathbb H$** (every prime, dyadic included):
$$\beta_\pi(L\perp\mathbb H, L\perp\mathbb H) = \beta_\pi(L\perp\mathbb H, \mathbb H)\cdot\beta_\pi(L, L).$$ -/
@[kb "kitaoka1993" "§5.6 [unverified] (reduction α(L ⊥ H) = α(L ⊥ H, H) α(L); Eichler transformations)"]
theorem localDensityForm_hypFrame [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π)
    (L : QuadForm R m) (hL : L.Nondegenerate) (hQ : (hypExt L).Nondegenerate) :
    localDensityForm (hypExt L) (hypExt L) π =
      localDensityForm (hypExt L) (hyperbolic R) π * localDensityForm L L π := by
  obtain ⟨d, hd, hd'⟩ := exists_pow_dvd_not_dvd π hπ hQ
  have e1 := localDensityForm_eventually_eq (hypExt L) (hypExt L) hQ π hπ le_rfl
  have e2 := localDensityForm_eventually_eq (hypExt L) (hyperbolic R) hyperbolic_nondegenerate π hπ
    (by omega : 2 ≤ m + 2)
  have e3 := localDensityForm_eventually_eq L L hL π hπ le_rfl
  obtain ⟨k, h1, h2, h3, hk⟩ := (e1.and (e2.and (e3.and (Filter.eventually_gt_atTop d)))).exists
  rw [← h1, ← h2, ← h3, repCountForm_hypFrame hπ L hd hd' hk, exponent_hypFrame, Nat.mul_add, pow_add]
  push_cast
  ring

end Density

end QuadFormsKB.LocalDensity.HypFrame
