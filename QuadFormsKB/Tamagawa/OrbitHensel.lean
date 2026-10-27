/-
# Exact Hensel lifting for $Q(x) = m$ and for $Q \circ X = Q$ over a complete DVR

**Layer:** a complete discrete valuation ring $R$ (`IsAdicComplete (maximalIdeal R) R`), uniformizer $\pi$, any residue
characteristic (dyadic included). Used for Weil's local orbital identity at the primes $\mathfrak p \mid 2m$
(`LocalOrbitalBad.lean`).

**Proves**
* `newton_lift` (**Newton's method for quadratic maps**): let $F : R^\iota \to R^\kappa$ satisfy
  $F(\vec x + c\vec w) = F(\vec x) + c\,D_{\vec x}\vec w + c^2F(\vec w)$ with $D_{\vec x}$ linear (as in `card_sol_succ`), and suppose the
  image of $D_{\vec x}$ contains $\pi^dR^\kappa$ at every $\vec x$ with $F(\vec x) \equiv \vec t \bmod \pi^K$, $K \ge 2d + 1$. Then every
  solution mod $\pi^K$ is congruent mod $\pi^{K-d}$ to an exact solution $F(\vec x^*) = \vec t$. *Proof:* the Newton step
  $\vec x' = \vec x + \pi^{K-d}\vec w$, $D_{\vec x}\vec w = -\pi^d\vec e$ where $F(\vec x) - \vec t = \pi^K\vec e$, gives
  $F(\vec x') - \vec t = \pi^{2(K-d)}F(\vec w)$ and $2(K - d) \ge K + 1$; the iterates converge (precompleteness) and the limit
  solves $F = \vec t$ (an element divisible by every $\pi^j$ is $0$).
* `exists_eval_eq_of_dvd` (**points**): if $\pi^e \,\Vert\, 2m$, $K \ge 2e + 1$ and $Q(\vec x) \equiv m \bmod \pi^K$, there is
  $\vec x^*$ with $Q(\vec x^*) = m$ and $\vec x^* \equiv \vec x \bmod \pi^{K-e}$ (the gradient $H\vec x$ has $\vec x\cdot H\vec x = 2Q(\vec x)$
  of order $e$).
* `exists_compMat_eq_of_dvd` (**isometries**): if $\pi^d \,\Vert\, \det H_Q$, $K \ge 2d + 1$ and $Q\circ X \equiv Q \bmod \pi^K$, there is
  $X^*$ with $Q \circ X^* = Q$ and $X^* \equiv X \bmod \pi^{K-d}$ (the differential of $X \mapsto Q\circ X$ has image
  $\supseteq \pi^d\,\mathrm{Sym}$, `formD_surj`).

(Hensel's lemma in several variables; O'Meara 1963, 13:8, p. 26, is the one-variable form; Kitaoka 1993, §5.6 [unverified] for the isometry
case.) Indices are 0-based.
-/
import QuadFormsKB.LocalDensity.FormDensityStab
import QuadFormsKB.LocalDensity.DVRExplicit

open Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ι κ : Type*}

/-- An element of a DVR divisible by every power of $\pi$ is $0$. -/
theorem eq_zero_of_forall_pow_dvd {π : R} (hπ : Irreducible π) {x : R} (h : ∀ j, π ^ j ∣ x) : x = 0 := by
  by_contra hx
  obtain ⟨e, -, he⟩ := exists_pow_dvd_not_dvd π hπ hx
  exact he (h (e + 1))

/-- **One Newton step** for a quadratic map. -/
theorem newton_step (π : R) (F : (ι → R) → (κ → R)) (D : (ι → R) → (ι → R) →ₗ[R] (κ → R))
    (hF : ∀ x w (c : R), F (x + c • w) = F x + c • D x w + c ^ 2 • F w) (t : κ → R) (d K : ℕ)
    (hK : 2 * d + 1 ≤ K) (x : ι → R) (hx : ∀ j, π ^ K ∣ F x j - t j)
    (hD : ∀ c, ∃ w, D x w = π ^ d • c) :
    ∃ x', (∀ j, π ^ (K + 1) ∣ F x' j - t j) ∧ ∀ i, π ^ (K - d) ∣ x' i - x i := by
  choose e he using hx
  obtain ⟨w, hw⟩ := hD (-e)
  refine ⟨x + π ^ (K - d) • w, fun j => ?_, fun i => ⟨w i, by simp⟩⟩
  rw [hF]
  have hwj := congrFun hw j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at hwj ⊢
  have h1 : F x j + π ^ (K - d) * (D x w) j + (π ^ (K - d)) ^ 2 * F w j - t j =
      π ^ (2 * (K - d)) * F w j := by
    rw [hwj, show F x j = t j + π ^ K * e j by rw [← he j]; ring, ← pow_mul, mul_comm (K - d) 2]
    have : π ^ (K - d) * (π ^ d * -e j) = -(π ^ K * e j) := by
      rw [← mul_assoc, ← pow_add, show K - d + d = K by omega]; ring
    rw [this]; ring
  rw [h1]
  exact dvd_mul_of_dvd_left (pow_dvd_pow π (by omega)) _

/-- **Newton's method for quadratic maps over a complete DVR** (exact lifting): a solution of $F \equiv \vec t$ mod
$\pi^K$, $K \ge 2d+1$, is congruent mod $\pi^{K-d}$ to an exact solution, provided the image of the differential contains
$\pi^dR^\kappa$ at every solution mod $\pi^K$. -/
@[kb "omeara1963" "§13D, 13:8, p. 26 (Hensel's lemma); cassels1978 Ch. 3, Lemma 4.1, p. 47"]
theorem newton_lift [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π)
    (F : (ι → R) → (κ → R)) (D : (ι → R) → (ι → R) →ₗ[R] (κ → R))
    (hF : ∀ x w (c : R), F (x + c • w) = F x + c • D x w + c ^ 2 • F w) (t : κ → R) (d K : ℕ)
    (hK : 2 * d + 1 ≤ K) (hD : ∀ x, (∀ j, π ^ K ∣ F x j - t j) → ∀ c, ∃ w, D x w = π ^ d • c)
    (x : ι → R) (hx : ∀ j, π ^ K ∣ F x j - t j) :
    ∃ y, F y = t ∧ ∀ i, π ^ (K - d) ∣ y i - x i := by
  -- the Newton iterates
  have step : ∀ n (y : {y : ι → R // ∀ j, π ^ (K + n) ∣ F y j - t j}),
      ∃ y' : {y : ι → R // ∀ j, π ^ (K + (n + 1)) ∣ F y j - t j}, ∀ i, π ^ (K + n - d) ∣ y'.1 i - y.1 i := by
    rintro n ⟨y, hy⟩
    obtain ⟨y', h1, h2⟩ := newton_step π F D hF t d (K + n) (by omega) y hy
      (hD y fun j => (pow_dvd_pow π (by omega)).trans (hy j))
    exact ⟨⟨y', by rw [← add_assoc]; exact h1⟩, h2⟩
  choose g hg using step
  let s : (n : ℕ) → {y : ι → R // ∀ j, π ^ (K + n) ∣ F y j - t j} := fun n =>
    Nat.rec (motive := fun n => {y : ι → R // ∀ j, π ^ (K + n) ∣ F y j - t j}) ⟨x, hx⟩ (fun n y => g n y) n
  have hs : ∀ n, s (n + 1) = g n (s n) := fun n => rfl
  have hcauchy : ∀ i a b, a ≤ b → π ^ (K + a - d) ∣ (s b).1 i - (s a).1 i := by
    intro i a b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      rw [hs]
      have h1 := (pow_dvd_pow π (by omega : K + a - d ≤ K + b - d)).trans (hg b (s b) i)
      have h2 := h1.add ih
      rwa [sub_add_sub_cancel] at h2
  have hL : ∀ i, ∃ L : R, ∀ a, π ^ (K + a - d) ∣ L - (s a).1 i := by
    intro i
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := IsLocalRing.maximalIdeal R) (fun a => (s a).1 i)
      (fun {a b} hab => by
        rw [smodEq_maximalIdeal_pow_iff π hπ, ← dvd_neg, neg_sub]
        exact (pow_dvd_pow π (by omega)).trans (hcauchy i a b hab))
    refine ⟨L, fun a => ?_⟩
    have h1 := (smodEq_maximalIdeal_pow_iff π hπ (K + a - d) _ _).1 (hL (K + a - d))
    have h2 := hcauchy i a (K + a - d) (by omega)
    have h3 := (dvd_neg.mpr h1).add h2
    rw [show -((s (K + a - d)).1 i - L) + ((s (K + a - d)).1 i - (s a).1 i) = L - (s a).1 i by ring] at h3
    exact h3
  choose L hLs using hL
  refine ⟨L, funext fun j => ?_, fun i => hLs i 0⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_pow_dvd hπ fun a => ?_
  -- `L = s a + π^(K + a - d) w`
  have hw : ∀ i, ∃ w, L i = (s a).1 i + π ^ (K + a - d) * w := fun i => by
    obtain ⟨w, hw⟩ := hLs i a; exact ⟨w, by rw [← hw]; ring⟩
  choose w hw using hw
  have hLw : L = (s a).1 + π ^ (K + a - d) • w := funext fun i => by simp [hw i]
  have e1 := congrFun (hF (s a).1 w (π ^ (K + a - d))) j
  rw [← hLw] at e1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1
  rw [e1]
  have h1 : π ^ a ∣ F (s a).1 j - t j := (pow_dvd_pow π (by omega)).trans ((s a).2 j)
  have h2 : π ^ a ∣ π ^ (K + a - d) := pow_dvd_pow π (by omega)
  have := (h1.add (dvd_mul_of_dvd_left h2 ((D (s a).1) w j))).add
    (dvd_mul_of_dvd_left (h2.trans (dvd_pow_self _ two_ne_zero)) (F w j))
  convert this using 1
  ring

/-! ### Points: $Q(\vec x) = m$ -/

/-- The scalar quadratic map $\vec x \mapsto Q(\vec x)$ with its differential $\vec w \mapsto (H\vec x)\cdot\vec w$. -/
def evalD {n : ℕ} (Q : QuadForm R n) (x : Fin n → R) : (Fin n → R) →ₗ[R] (Unit → R) where
  toFun w := fun _ => (Q.hessian *ᵥ x) ⬝ᵥ w
  map_add' w w' := by funext; simp [dotProduct_add]
  map_smul' c w := by funext; simp [dotProduct_smul]

/-- **Exact Hensel lifting for $Q(\vec x) = m$** at every prime (dyadic included): if $\pi^e \,\Vert\, 2m$, $K \ge 2e+1$ and
$\pi^K \mid Q(\vec x) - m$, then $Q(\vec x^*) = m$ for some $\vec x^* \equiv \vec x \bmod \pi^{K-e}$. -/
@[kb "omeara1963" "§13D, 13:8, p. 26 (Hensel's lemma); cassels1978 Ch. 3, Lemma 4.1, p. 47"]
theorem exists_eval_eq_of_dvd [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π)
    {n : ℕ} (Q : QuadForm R n) {m : R} {e K : ℕ} (he : π ^ e ∣ 2 * m) (he' : ¬ π ^ (e + 1) ∣ 2 * m)
    (hK : 2 * e + 1 ≤ K) (x : Fin n → R) (hx : π ^ K ∣ Q.eval x - m) :
    ∃ y, Q.eval y = m ∧ ∀ i, π ^ (K - e) ∣ y i - x i := by
  obtain ⟨u, hu, hu1⟩ := dvr_exact hπ he he'
  have hF : ∀ x w (c : R), (fun x : Fin n → R => fun _ : Unit => Q.eval x) (x + c • w) =
      (fun _ => Q.eval x) + c • evalD Q x w + c ^ 2 • (fun _ => Q.eval w) := by
    intro x w c; funext; simp [evalD, eval_add_smul']
  have hD : ∀ x : Fin n → R, (∀ j : Unit, π ^ K ∣ Q.eval x - m) → ∀ c : Unit → R,
      ∃ w, evalD Q x w = π ^ e • c := by
    intro x hx c
    -- `x ⬝ H x = 2 Q(x) = π^e (unit)`
    obtain ⟨s, hs⟩ := hx ()
    have h2 : (Q.hessian *ᵥ x) ⬝ᵥ x = π ^ e * (u + 2 * π ^ (K - e) * s) := by
      rw [dotProduct_comm, dotProduct_hessian_self]
      have : Q.eval x = m + π ^ K * s := by rw [← hs]; ring
      rw [this, mul_add, hu, show π ^ K = π ^ e * π ^ (K - e) by
        rw [← pow_add]; congr 1; omega]
      ring
    have hv : IsUnit (u + 2 * π ^ (K - e) * s) := by
      apply dvr_isUnit_of_not_dvd hπ
      intro h
      apply dvr_not_dvd_of_isUnit hπ hu1
      have : π ∣ 2 * π ^ (K - e) * s :=
        dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self π (by omega)) 2) s
      simpa using dvd_sub h this
    refine ⟨(c () * ↑hv.unit⁻¹) • x, funext fun _ => ?_⟩
    simp only [evalD, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_smul, smul_eq_mul, h2, Pi.smul_apply]
    rw [show c () * ↑hv.unit⁻¹ * (π ^ e * (u + 2 * π ^ (K - e) * s)) =
      π ^ e * c () * (↑hv.unit⁻¹ * (u + 2 * π ^ (K - e) * s)) by ring, IsUnit.val_inv_mul, mul_one]
  obtain ⟨y, hy, hyx⟩ := newton_lift hπ (fun x : Fin n → R => fun _ : Unit => Q.eval x) (evalD Q) hF
    (fun _ => m) e K hK hD x (fun _ => hx)
  exact ⟨y, congrFun hy (), hyx⟩

/-! ### Isometries: $Q \circ X = Q$ -/

/-- **Exact Hensel lifting for $Q \circ X = Q$** at every prime (dyadic included): if $\pi^d \,\Vert\, \det H_Q$,
$K \ge 2d+1$ and $Q\circ X \equiv Q \bmod \pi^K$ (coefficientwise), then $Q \circ X^* = Q$ for some $X^* \equiv X \bmod \pi^{K-d}$. -/
@[kb "kitaoka1993" "§5.6 (lifting isometries) [unverified]"]
theorem exists_compMat_eq_of_dvd [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π)
    {n : ℕ} (Q : QuadForm R n) {d K : ℕ} (hd : π ^ d ∣ Q.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ Q.hessian.det)
    (hK : 2 * d + 1 ≤ K) (X : Matrix (Fin n) (Fin n) R)
    (hX : ∀ i j, π ^ K ∣ (Q.compMat X).coeff i j - Q.coeff i j) :
    ∃ Y : Matrix (Fin n) (Fin n) R, Q.compMat Y = Q ∧ ∀ i j, π ^ (K - d) ∣ Y i j - X i j := by
  obtain ⟨y, hy, hyx⟩ := newton_lift hπ (formF Q) (formD Q) (formF_add_smul Q)
    (fun p : UpperIdx n => Q.coeff p.1.1 p.1.2) d K hK
    (fun x hx c => formD_surj Q Q π hπ d K hd hd' (by omega) x hx c) (fun li => X li.1 li.2)
    (fun p => hX p.1.1 p.1.2)
  refine ⟨toMat y, ext_upper fun i j hij => ?_, fun i j => hyx (i, j)⟩
  exact congrFun hy ⟨(i, j), hij⟩

end QuadFormsKB.LocalDensity.DVR
