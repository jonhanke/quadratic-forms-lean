/-
# The ramified binary kernel at a dyadic place: counting

W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), §6, (6.3), (6.5):
for $r = 2$ and $E_\delta/F$ ramified the anisotropic kernel is $\mathcal O_{E_\delta}$ with the scaled norm form
$\alpha N_{E_\delta/F}$. In a basis $1, \varpi$ of $\mathcal O_E$ with $\varpi$ a root of an Eisenstein polynomial
$X^2 - tX + n$ ($\pi \mid t$, $\pi \,\|\, n$) the norm form is
$$N(x_0 + x_1\varpi) = x_0^2 + t\,x_0x_1 + n\,x_1^2 \qquad (\texttt{eisForm}\ t\ n).$$
This file needs no field $E$: everything is done with this explicit form over a commutative ring (the identities) and over
a discrete valuation ring $R$ (the counts).

* **Multiplication matrices** (`mulM`): $M_\xi$ is multiplication by $\xi = \xi_0 + \xi_1\varpi$ in the basis $1, \varpi$;
  $N(M_\xi v) = N(\xi)N(v)$ (`eval_mulM`) and $M_\xi M_{\bar\xi} = N(\xi)\cdot 1$ for the conjugate $\bar\xi$ (`conjV`).
* **Orbit–stabilizer without a group** (`card_aut_eq_mul`): over every commutative ring $A$,
  $$\#\{X \in M_2(A) : N\circ X = N\} = \#\{\xi : N(\xi) = 1\}\cdot\#\{y : N\circ[e_0\,|\,y] = N\},$$
  via $X \mapsto (Xe_0,\ M_{\overline{Xe_0}}Xe_1)$ and $(\xi, y)\mapsto M_\xi[e_0\,|\,y]$.
* **The norm filtration** (`pow_dvd_nrm_iff`, $R$ a discrete valuation ring, $\pi\mid t$, $\pi\,\|\,n$):
  $\pi^m \mid N(z) \iff \pi^{\lceil m/2\rceil}\mid z_0 \text{ and } \pi^{\lfloor m/2\rfloor}\mid z_1$ (this is
  $v_E(z) = v_F(N z)$ for the ramified $E$).
* **The stabilizer** (`card_stab`): for $\pi^d \,\|\, 4n - t^2$ and $k > d$, the $y \bmod \pi^k$ with
  $2y_0 + ty_1 \equiv t$, $N(y) \equiv n$ are the two boxes $\varpi + \mathfrak P^{2k-d}$ and $\bar\varpi + \mathfrak P^{2k-d}$, so there
  are $2q^d$ of them. *Proof:* $(\eta - \varpi)(\eta - \bar\varpi) = \alpha\eta - \beta$ with $\alpha = \operatorname{Tr}\eta - t$,
  $\beta = N\eta - n$ (`nrm_mul_identity`), and $v_E(\varpi - \bar\varpi) = d$.
* **The norm-one count** (`card_normOne`): if the unit norms have index $2$ in the units (`IndexTwo`, from the Hilbert
  symbol in `DyadicR2RamNorm.lean`) and $1 + \pi^k R$ consists of squares, then $\#\{\xi \bmod \pi^k : N\xi\equiv1\} = 2q^k$.

Indices are 0-based. Sources: Gan–Hanke–Yu 2001, §6 (the shape of the kernel); the counting is elementary.
-/
import QuadFormsKB.Literature.Hanke2005.DyadicAnisoKernel
import QuadFormsKB.LocalDensity.FormDensitySelf
import QuadFormsKB.LocalDensity.Hensel
import QuadFormsKB.LocalDensity.DVRDyadicTable
import QuadFormsKB.LocalDensity.DVRTable2
import QuadFormsKB.Defs.Hilbert

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.R2Ram

open QuadForm LocalDensity LocalDensity.DVR

/-! ### The Eisenstein norm form over a commutative ring -/

section Ring

variable {A : Type*} [CommRing A]

/-- **The Eisenstein norm form** $N(x) = x_0^2 + t\,x_0x_1 + n\,x_1^2$: the norm form of $\mathcal O_E = R[\varpi]$ in the basis
$1, \varpi$, $\varpi^2 = t\varpi - n$. -/
def eisForm (t n : A) : QuadForm A 2 := QuadForm.ofUpper ![![1, t], ![0, n]]

/-- The value $x_0^2 + t\,x_0x_1 + n\,x_1^2$ as a function of two scalars. -/
def nrm (t n a b : A) : A := a * a + t * (a * b) + n * (b * b)

theorem eval_eisForm (t n : A) (x : Fin 2 → A) : (eisForm t n).eval x = nrm t n (x 0) (x 1) := by
  simp [eisForm, nrm, QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two]
  ring

theorem eisForm_coeff (t n : A) :
    (eisForm t n).coeff 0 0 = 1 ∧ (eisForm t n).coeff 0 1 = t ∧ (eisForm t n).coeff 1 1 = n := by
  simp [eisForm, QuadForm.ofUpper]

theorem hessian_eisForm (t n : A) : (eisForm t n).hessian = !![2, t; t, 2 * n] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [QuadForm.hessian, eisForm, QuadForm.ofUpper] <;> ring

theorem det_hessian_eisForm (t n : A) : (eisForm t n).hessian.det = 4 * n - t ^ 2 := by
  rw [hessian_eisForm, det_fin_two_of]; ring

theorem map_eisForm {B : Type*} [CommRing B] (f : A →+* B) (t n : A) :
    (eisForm t n).map f = eisForm (f t) (f n) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eisForm, QuadForm.ofUpper, QuadForm.map]

/-- Multiplication by $\xi = \xi_0 + \xi_1\varpi$ in the basis $1, \varpi$ ($\varpi^2 = t\varpi - n$). -/
def mulM (t n : A) (ξ : Fin 2 → A) : Matrix (Fin 2) (Fin 2) A := !![ξ 0, -(n * ξ 1); ξ 1, ξ 0 + t * ξ 1]

/-- The conjugate $\bar\xi = (\xi_0 + t\xi_1) - \xi_1\varpi$. -/
def conjV (t : A) (ξ : Fin 2 → A) : Fin 2 → A := ![ξ 0 + t * ξ 1, -ξ 1]

/-- The matrix $[e_0\,|\,y]$. -/
def stabM (y : Fin 2 → A) : Matrix (Fin 2) (Fin 2) A := !![1, y 0; 0, y 1]

theorem nrm_mul (t n a b c d : A) :
    nrm t n (a * c - n * (b * d)) (a * d + b * c + t * (b * d)) = nrm t n a b * nrm t n c d := by
  unfold nrm; ring

theorem nrm_smul (t n c a b : A) : nrm t n (c * a) (c * b) = c ^ 2 * nrm t n a b := by
  unfold nrm; ring

theorem nrm_conj (t n a b : A) : nrm t n (a + t * b) (-b) = nrm t n a b := by
  unfold nrm; ring

theorem nrm_neg (t n a b : A) : nrm t n (-a) (-b) = nrm t n a b := by
  unfold nrm; ring

theorem eval_mulM (t n : A) (ξ v : Fin 2 → A) :
    (eisForm t n).eval (mulM t n ξ *ᵥ v) = (eisForm t n).eval ξ * (eisForm t n).eval v := by
  simp only [eval_eisForm, mulM, mulVec, dotProduct, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one, head_cons]
  unfold nrm; ring

theorem eval_smulF {m : ℕ} (c : A) (Q : QuadForm A m) (x : Fin m → A) : (c • Q).eval x = c * Q.eval x := by
  simp only [QuadForm.eval, QuadForm.evalIn, smul_coeff, Algebra.algebraMap_self, RingHom.id_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem one_smul_form {m : ℕ} (Q : QuadForm A m) : (1 : A) • Q = Q := by
  ext i j; simp

theorem compMat_mulM (t n : A) (ξ : Fin 2 → A) (X : Matrix (Fin 2) (Fin 2) A) :
    (eisForm t n).compMat (mulM t n ξ * X) = (eisForm t n).eval ξ • (eisForm t n).compMat X := by
  refine eq_of_eval_eq fun y => ?_
  rw [eval_compMat, eval_smulF, eval_compMat, ← mulVec_mulVec, eval_mulM]

theorem eval_conjV (t n : A) (ξ : Fin 2 → A) : (eisForm t n).eval (conjV t ξ) = (eisForm t n).eval ξ := by
  simp only [eval_eisForm, conjV, cons_val_zero, cons_val_one, head_cons]
  exact nrm_conj t n _ _

theorem mulM_mul_conj (t n : A) (ξ : Fin 2 → A) :
    mulM t n ξ * mulM t n (conjV t ξ) = (eisForm t n).eval ξ • (1 : Matrix (Fin 2) (Fin 2) A) := by
  rw [eval_eisForm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mulM, conjV, mul_apply, Fin.sum_univ_two, nrm] <;> ring

theorem mulM_conj_mul (t n : A) (ξ : Fin 2 → A) :
    mulM t n (conjV t ξ) * mulM t n ξ = (eisForm t n).eval ξ • (1 : Matrix (Fin 2) (Fin 2) A) := by
  rw [eval_eisForm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mulM, conjV, mul_apply, Fin.sum_univ_two, nrm] <;> ring

/-- The first column of $N\circ X = N$ has norm $1$. -/
theorem eval_col0_of_compMat (t n : A) {X : Matrix (Fin 2) (Fin 2) A}
    (hX : (eisForm t n).compMat X = eisForm t n) : (eisForm t n).eval (fun l => X l 0) = 1 := by
  have h := congrArg (fun Q : QuadForm A 2 => Q.coeff 0 0) hX
  simp only [compMat_coeff, le_refl, if_true] at h
  rw [h, (eisForm_coeff t n).1]

theorem stabM_eq (Y : Matrix (Fin 2) (Fin 2) A) (h0 : Y 0 0 = 1) (h1 : Y 1 0 = 0) :
    stabM (fun i => Y i 1) = Y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stabM, h0, h1]

theorem compMat_stabM_iff (t n : A) (y : Fin 2 → A) :
    (eisForm t n).compMat (stabM y) = eisForm t n ↔ 2 * y 0 + t * y 1 = t ∧ nrm t n (y 0) (y 1) = n := by
  have hc : ∀ i j : Fin 2, ((eisForm t n).compMat (stabM y)).coeff i j = if i ≤ j then
      (if i = j then (eisForm t n).eval (fun l => stabM y l i)
        else (fun l => stabM y l i) ⬝ᵥ ((eisForm t n).hessian *ᵥ fun l => stabM y l j)) else 0 :=
    fun i j => compMat_coeff _ _ i j
  have h01 : ((eisForm t n).compMat (stabM y)).coeff 0 1 = 2 * y 0 + t * y 1 := by
    rw [hc]; simp [stabM, hessian_eisForm, dotProduct, mulVec, Fin.sum_univ_two]
  have h11 : ((eisForm t n).compMat (stabM y)).coeff 1 1 = nrm t n (y 0) (y 1) := by
    rw [hc]; simp only [le_refl, if_true]; rw [eval_eisForm]; simp [stabM]
  have h00 : ((eisForm t n).compMat (stabM y)).coeff 0 0 = 1 := by
    rw [hc]; simp only [le_refl, if_true]; rw [eval_eisForm]; simp [stabM, nrm]
  obtain ⟨e00, e01, e11⟩ := eisForm_coeff t n
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← h01, h, e01]
    · rw [← h11, h, e11]
  · rintro ⟨ha, hb⟩
    refine ext_upper fun i j hij => ?_
    fin_cases i <;> fin_cases j
    · exact h00.trans e00.symm
    · exact h01.trans (ha.trans e01.symm)
    · exact absurd hij (by decide)
    · exact h11.trans (hb.trans e11.symm)

/-- **Orbit–stabilizer for the self-representations of the Eisenstein norm form** (every commutative ring):
$\#\{X : N\circ X = N\} = \#\{\xi : N(\xi) = 1\}\cdot\#\{y : N\circ[e_0\,|\,y] = N\}$. -/
theorem card_aut_eq_mul (t n : A) :
    Nat.card {X : Matrix (Fin 2) (Fin 2) A // (eisForm t n).compMat X = eisForm t n} =
      Nat.card {ξ : Fin 2 → A // (eisForm t n).eval ξ = 1} *
        Nat.card {y : Fin 2 → A // (eisForm t n).compMat (stabM y) = eisForm t n} := by
  rw [← Nat.card_prod]
  set Q := eisForm t n with hQ
  -- the normalized matrix `M_{\bar ξ} X`
  have hY : ∀ X : Matrix (Fin 2) (Fin 2) A, Q.compMat X = Q →
      Q.compMat (mulM t n (conjV t fun l => X l 0) * X) = Q := by
    intro X hX
    rw [compMat_mulM, eval_conjV, eval_col0_of_compMat t n hX, hX, one_smul_form]
  have hY0 : ∀ X : Matrix (Fin 2) (Fin 2) A, Q.compMat X = Q →
      (mulM t n (conjV t fun l => X l 0) * X) 0 0 = 1 ∧ (mulM t n (conjV t fun l => X l 0) * X) 1 0 = 0 := by
    intro X hX
    have h1 := eval_col0_of_compMat t n hX
    rw [eval_eisForm] at h1
    constructor
    · rw [← h1]; simp [mulM, conjV, mul_apply, Fin.sum_univ_two, nrm]; ring
    · simp [mulM, conjV, mul_apply, Fin.sum_univ_two]; ring
  refine Nat.card_congr
    { toFun := fun X => (⟨fun l => X.1 l 0, eval_col0_of_compMat t n X.2⟩,
        ⟨fun i => (mulM t n (conjV t fun l => X.1 l 0) * X.1) i 1, by
          rw [stabM_eq _ (hY0 X.1 X.2).1 (hY0 X.1 X.2).2]; exact hY X.1 X.2⟩)
      invFun := fun p => ⟨mulM t n p.1.1 * stabM p.2.1, by
        rw [compMat_mulM, p.1.2, one_smul_form]; exact p.2.2⟩
      left_inv := fun X => ?_
      right_inv := fun p => ?_ }
  · apply Subtype.ext
    simp only
    rw [stabM_eq _ (hY0 X.1 X.2).1 (hY0 X.1 X.2).2, ← Matrix.mul_assoc, mulM_mul_conj,
      eval_col0_of_compMat t n X.2, one_smul, Matrix.one_mul]
  · obtain ⟨⟨ξ, hξ⟩, ⟨y, hy⟩⟩ := p
    have hcol : (fun l => (mulM t n ξ * stabM y) l 0) = ξ := by
      funext l; fin_cases l <;> simp [mulM, stabM, mul_apply, Fin.sum_univ_two]
    refine Prod.ext (Subtype.ext hcol) (Subtype.ext ?_)
    simp only
    rw [hcol, ← Matrix.mul_assoc, mulM_conj_mul, hξ, one_smul, Matrix.one_mul]
    funext i; fin_cases i <;> simp [stabM]

end Ring

/-! ### The norm filtration over a discrete valuation ring -/

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R}

theorem nrm_pi_mul (t n a b : R) (π : R) : nrm t n (π * a) (π * b) = π ^ 2 * nrm t n a b := by
  unfold nrm; ring

/-- **The norm filtration of the ramified norm form:** for $\pi \mid t$ and $n = \pi w$ with $w$ a unit,
$\pi^m \mid N(a, b) \iff \pi^{\lceil m/2\rceil} \mid a$ and $\pi^{\lfloor m/2\rfloor} \mid b$. -/
theorem pow_dvd_nrm_iff (hπ : Irreducible π) {t n w : R} (ht : π ∣ t) (hn : n = π * w) (hw : IsUnit w) (m : ℕ) :
    ∀ a b : R, π ^ m ∣ nrm t n a b ↔ π ^ ((m + 1) / 2) ∣ a ∧ π ^ (m / 2) ∣ b := by
  have hπ0 := hπ.ne_zero
  obtain ⟨t', rfl⟩ := ht
  subst hn
  have base1 : ∀ a b : R, π ∣ nrm (π * t') (π * w) a b ↔ π ∣ a := by
    intro a b
    have e : nrm (π * t') (π * w) a b = a * a + π * (t' * (a * b) + w * (b * b)) := by
      unfold nrm; ring
    rw [e, dvd_add_left (dvd_mul_right _ _)]
    exact ⟨fun h => (hπ.prime.dvd_or_dvd h).elim id id, fun h => dvd_mul_of_dvd_left h _⟩
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a b
  match m, ih with
  | 0, _ => simp
  | 1, _ => simpa using base1 a b
  | m + 2, ih =>
    constructor
    · intro h
      have ha : π ∣ a := (base1 a b).1 ((dvd_pow_self π (by omega)).trans h)
      obtain ⟨a', rfl⟩ := ha
      have hb : π ∣ b := by
        have h2 : π ^ 2 ∣ nrm (π * t') (π * w) (π * a') b := (pow_dvd_pow π (by omega)).trans h
        have e : nrm (π * t') (π * w) (π * a') b = π ^ 2 * (a' * a' + t' * (a' * b)) + π * (w * (b * b)) := by
          unfold nrm; ring
        rw [e, dvd_add_right (dvd_mul_right _ _), pow_two, mul_dvd_mul_iff_left hπ0] at h2
        rcases hπ.prime.dvd_or_dvd h2 with h3 | h3
        · exact absurd (isUnit_of_dvd_unit h3 hw) hπ.not_isUnit
        · exact (hπ.prime.dvd_or_dvd h3).elim id id
      obtain ⟨b', rfl⟩ := hb
      rw [nrm_pi_mul, pow_add, mul_comm (π ^ m), mul_dvd_mul_iff_left (pow_ne_zero _ hπ0)] at h
      obtain ⟨h1, h2⟩ := (ih m (by omega) a' b').1 h
      refine ⟨?_, ?_⟩
      · rw [show (m + 2 + 1) / 2 = (m + 1) / 2 + 1 by omega, pow_succ, mul_comm]
        exact mul_dvd_mul_left π h1
      · rw [show (m + 2) / 2 = m / 2 + 1 by omega, pow_succ, mul_comm]
        exact mul_dvd_mul_left π h2
    · rintro ⟨h1, h2⟩
      rw [show (m + 2 + 1) / 2 = (m + 1) / 2 + 1 by omega, pow_succ'] at h1
      rw [show (m + 2) / 2 = m / 2 + 1 by omega, pow_succ'] at h2
      obtain ⟨a', ha'⟩ := (dvd_pow_self π (by omega : (m + 1) / 2 + 1 ≠ 0)).trans
        (show π ^ ((m + 1) / 2 + 1) ∣ a by rw [pow_succ']; exact h1)
      obtain ⟨b', hb'⟩ := (dvd_pow_self π (by omega : m / 2 + 1 ≠ 0)).trans
        (show π ^ (m / 2 + 1) ∣ b by rw [pow_succ']; exact h2)
      subst ha' hb'
      rw [mul_dvd_mul_iff_left hπ0] at h1 h2
      rw [nrm_pi_mul, pow_add, mul_comm (π ^ m)]
      exact mul_dvd_mul_left _ ((ih m (by omega) a' b').2 ⟨h1, h2⟩)

/-- Ultrametric inequality for the norm filtration. -/
theorem pow_dvd_nrm_add (hπ : Irreducible π) {t n w : R} (ht : π ∣ t) (hn : n = π * w) (hw : IsUnit w) (m : ℕ)
    {a b c d : R} (h1 : π ^ m ∣ nrm t n a b) (h2 : π ^ m ∣ nrm t n c d) : π ^ m ∣ nrm t n (a + c) (b + d) := by
  rw [pow_dvd_nrm_iff hπ ht hn hw] at h1 h2 ⊢
  exact ⟨dvd_add h1.1 h2.1, dvd_add h1.2 h2.2⟩

/-- **The identity $(\eta - \varpi)(\eta - \bar\varpi) = \alpha\eta - \beta$** in norms:
$N(y_0, y_1 - 1)\,N(y_0 - t, y_1 + 1) = N(\alpha y_0 - \beta, \alpha y_1)$ with $\alpha = 2y_0 + ty_1 - t$, $\beta = N(y) - n$. -/
theorem nrm_mul_identity (t n y0 y1 : R) :
    nrm t n y0 (y1 - 1) * nrm t n (y0 - t) (y1 + 1) =
      nrm t n ((2 * y0 + t * y1 - t) * y0 - (nrm t n y0 y1 - n)) ((2 * y0 + t * y1 - t) * y1) := by
  unfold nrm; ring

/-- In a discrete valuation ring: $\pi^{d+1}\nmid a$ and $\pi^N \mid ab$ with $d \le N$ give $\pi^{N-d} \mid b$. -/
theorem pow_dvd_of_mul (hπ : Irreducible π) {a b : R} {d N : ℕ} (ha : ¬ π ^ (d + 1) ∣ a) (hdN : d ≤ N)
    (h : π ^ N ∣ a * b) : π ^ (N - d) ∣ b := by
  have ha0 : a ≠ 0 := by rintro rfl; exact ha (dvd_zero _)
  obtain ⟨j, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
  have hj : j ≤ d := by
    by_contra hc
    exact ha (Dvd.dvd.mul_left (pow_dvd_pow π (by omega)) _)
  rw [mul_comm (u : R), mul_assoc, show N = j + (N - j) by omega, pow_add,
    mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)] at h
  have h' : π ^ (N - j) ∣ b := Units.dvd_mul_left.1 h
  exact (pow_dvd_pow π (by omega)).trans h'

variable (hπ : Irreducible π) {t n w : R} (ht : π ∣ t) (hn : n = π * w) (hw : IsUnit w) {d : ℕ}
  (hd : π ^ d ∣ 4 * n - t ^ 2) (hd' : ¬ π ^ (d + 1) ∣ 4 * n - t ^ 2)

include hπ ht hn hw hd hd'

/-- The discriminant is the norm of $\varpi - \bar\varpi$: $N(t, -2) = N(-t, 2) = 4n - t^2$. -/
theorem nrm_disc : nrm t n t (-2) = 4 * n - t ^ 2 ∧ nrm t n (-t) 2 = 4 * n - t ^ 2 := by
  constructor <;> (unfold nrm; ring)

/-- **The stabilizer conditions, lifted** ($k > d$): $\pi^k \mid 2y_0 + ty_1 - t$ and $\pi^k \mid N(y) - n$ iff $y$ lies in
one of the two boxes $\varpi + \mathfrak P^{2k-d}$, $\bar\varpi + \mathfrak P^{2k-d}$. -/
theorem stab_iff_box {k : ℕ} (hdk : d < k) (y0 y1 : R) :
    (π ^ k ∣ 2 * y0 + t * y1 - t ∧ π ^ k ∣ nrm t n y0 y1 - n) ↔
      (π ^ (2 * k - d) ∣ nrm t n y0 (y1 - 1) ∨ π ^ (2 * k - d) ∣ nrm t n (y0 - t) (y1 + 1)) := by
  have hπ0 := hπ.ne_zero
  have key := nrm_mul_identity t n y0 y1
  obtain ⟨hD1, hD2⟩ := nrm_disc hπ ht hn hw hd hd'
  constructor
  · rintro ⟨hα, hβ⟩
    have hprod : π ^ (2 * k) ∣ nrm t n y0 (y1 - 1) * nrm t n (y0 - t) (y1 + 1) := by
      rw [key, pow_dvd_nrm_iff hπ ht hn hw, show (2 * k + 1) / 2 = k by omega, show 2 * k / 2 = k by omega]
      exact ⟨dvd_sub (hα.mul_right _) hβ, hα.mul_right _⟩
    by_cases h1 : π ^ (d + 1) ∣ nrm t n y0 (y1 - 1)
    · have h2 : ¬ π ^ (d + 1) ∣ nrm t n (y0 - t) (y1 + 1) := by
        intro h2
        apply hd'
        have := pow_dvd_nrm_add hπ ht hn hw (d + 1) h1 (show π ^ (d + 1) ∣ nrm t n (-(y0 - t)) (-(y1 + 1)) by
          rwa [nrm_neg])
        rw [show y0 + -(y0 - t) = t by ring, show y1 - 1 + -(y1 + 1) = -2 by ring, hD1] at this
        exact this
      left
      exact pow_dvd_of_mul hπ h2 (by omega) (by rw [mul_comm (nrm t n (y0 - t) (y1 + 1))]; exact hprod)
    · right
      have := pow_dvd_of_mul hπ h1 (by omega) hprod
      exact this
  · intro hbox
    -- in both boxes `y1` is a unit and `π^d` divides both factors
    have hunit : IsUnit y1 := by
      have hB : 1 ≤ (2 * k - d) / 2 := by omega
      rcases hbox with h | h
      · have h' := ((pow_dvd_nrm_iff hπ ht hn hw _ _ _).1 h).2
        have h1 : π ∣ y1 - 1 := (dvd_pow_self π (by omega)).trans h'
        refine dvr_isUnit_of_not_dvd hπ fun hy => hπ.not_isUnit (isUnit_of_dvd_one ?_)
        have := dvd_sub hy h1; simpa using this
      · have h' := ((pow_dvd_nrm_iff hπ ht hn hw _ _ _).1 h).2
        have h1 : π ∣ y1 + 1 := (dvd_pow_self π (by omega)).trans h'
        refine dvr_isUnit_of_not_dvd hπ fun hy => hπ.not_isUnit (isUnit_of_dvd_one ?_)
        have := dvd_sub h1 hy; simpa using this
    have hprod : π ^ (2 * k) ∣ nrm t n y0 (y1 - 1) * nrm t n (y0 - t) (y1 + 1) := by
      rcases hbox with h | h
      · have h2 : π ^ d ∣ nrm t n (y0 - t) (y1 + 1) := by
          have := pow_dvd_nrm_add hπ ht hn hw d ((pow_dvd_pow π (by omega)).trans h)
            (show π ^ d ∣ nrm t n (-t) 2 by rw [hD2]; exact hd)
          rwa [show y0 + -t = y0 - t by ring, show y1 - 1 + 2 = y1 + 1 by ring] at this
        rw [show 2 * k = (2 * k - d) + d by omega, pow_add]
        exact mul_dvd_mul h h2
      · have h2 : π ^ d ∣ nrm t n y0 (y1 - 1) := by
          have := pow_dvd_nrm_add hπ ht hn hw d ((pow_dvd_pow π (by omega)).trans h)
            (show π ^ d ∣ nrm t n t (-2) by rw [hD1]; exact hd)
          rwa [show y0 - t + t = y0 by ring, show y1 + 1 + -2 = y1 - 1 by ring] at this
        rw [show 2 * k = d + (2 * k - d) by omega, pow_add]
        exact mul_dvd_mul h2 h
    rw [key, pow_dvd_nrm_iff hπ ht hn hw, show (2 * k + 1) / 2 = k by omega, show 2 * k / 2 = k by omega] at hprod
    obtain ⟨h1, h2⟩ := hprod
    have hα : π ^ k ∣ 2 * y0 + t * y1 - t := hunit.dvd_mul_right.1 h2
    refine ⟨hα, ?_⟩
    have := dvd_sub (hα.mul_right y0) h1
    rwa [sub_sub_cancel] at this

/-- The two boxes are disjoint ($k > d$). -/
theorem box_disjoint {k : ℕ} (hdk : d < k) (y0 y1 : R) :
    ¬ (π ^ (2 * k - d) ∣ nrm t n y0 (y1 - 1) ∧ π ^ (2 * k - d) ∣ nrm t n (y0 - t) (y1 + 1)) := by
  rintro ⟨h1, h2⟩
  obtain ⟨hD1, -⟩ := nrm_disc hπ ht hn hw hd hd'
  apply hd'
  have := pow_dvd_nrm_add hπ ht hn hw _ h1 (show π ^ (2 * k - d) ∣ nrm t n (-(y0 - t)) (-(y1 + 1)) by
    rwa [nrm_neg])
  rw [show y0 + -(y0 - t) = t by ring, show y1 - 1 + -(y1 + 1) = -2 by ring, hD1] at this
  exact (pow_dvd_pow π (by omega)).trans this

end DVR

end QuadFormsKB.Hanke2005.R2Ram
