/-
# Weil's local orbital identity, one prime at a time

**Layer:** first a commutative local ring $A$ (counting at level $\pi^k$), then a DVR $R$ (`LocalDensity.DVR`), then
the completions $\mathcal O_{F,\mathfrak p}$ of a number field (`LocalDensity.NF`) with the local lattices of `Lattices/`.

For $Q = \langle m\rangle\perp Q'$ (`splitForm`) on $V = F^{n+1}$, $L = \mathcal O_F e_0\perp\mathcal O_F^n$, $L' = \mathcal O_F^n$, the input
`LocalOrbitalIdentity` is the product over the finite primes $\mathfrak p$ of the **local orbital identity**
$$W_\mathfrak p\cdot\alpha_\mathfrak p(L, L)\cdot|2m|_\mathfrak p^{\,n} = \alpha_\mathfrak p(L', L')\cdot\beta_\mathfrak p(L, m)$$
(`LocalOrbitalIdentityAt`), where $W_\mathfrak p = \sum_t w_\mathfrak p(t)$ runs over the **local types**: the $O(Q')(F_\mathfrak p)$-orbits on
$Y_\mathfrak p = \{M \in O(V_\mathfrak p)\,\mathfrak o_\mathfrak p^{n+1} : e_0 \in M\}$ (`LocCompSet`, `LocTypes`), with
$w_\mathfrak p(M) = [K_0' : K_M\cap K_0']/[K_M : K_M\cap K_0']$ (`locWeight`), $K_M = \mathrm{Stab}(M)$, $K_0' = O(\mathfrak o_\mathfrak p^n)$
(Weil 1982, §3.4 [unverified]; Kitaoka 1993, §6.8 [unverified]; Siegel 1935 [unverified]).

**Proves**
* `card_compMat_splitForm` (counting, any commutative local ring $A$ with $2a \in A^\times$): the first-column map
  $X \mapsto Xe_0$ makes $\{X : Q\circ X = Q\}$ a product $\{x : Q(x) = a\}\times\{X' : Q'\circ X' = Q'\}$. Each fibre is carried to
  the fibre over $e_0$ by a reflection: $Q(x - e_0) + Q(x + e_0) = 4a$ is a unit, so one of the two is, and the reflection in
  that vector (times $-1$ in the second case) maps $e_0$ to $x$ (`exists_refl_e₀`); the fibre over $e_0$ is
  $\{\mathrm{diag}(1, X')\}$ because $2a$ is a unit (`eq_cornerMat_of_fix`).
* `DVR.localIdentity_unit`: for $\pi \nmid 2m$ and **any** nondegenerate $Q'$ (any determinant),
  $\beta_\pi(Q', Q')\,\beta_\pi(Q, m) = \beta_\pi(Q, Q)$: the counts multiply at every level $\pi^k$ and the exponents add,
  $\binom{n+1}{2} = n + \binom n2$. Over $F$: `localIdentity_unit_nf`. This generalizes `localIdentity_good`
  (which needed $\mathfrak p \nmid \det H_{Q'}$ and used closed forms).
* `exists_smul_locStdPt`: at $\mathfrak p \nmid 2m$ the group $O(Q')(F_\mathfrak p)$ is transitive on $Y_\mathfrak p$ (one local type), by the
  same reflections over $\mathfrak o_\mathfrak p$ and Witt's stabilizer lemma (`exists_orthEmb_eq`). So $W_\mathfrak p = 1$ (`locTypeSum_eq_one`).
* `localOrbitalIdentityAt_of_not_mem`: **the local orbital identity at every prime $\mathfrak p \nmid 2m$**, bad primes of
  $Q'$ included.

* `DVR.repCountForm_splitForm_orbit` (**every prime, dyadic included**): for $\pi^e \,\|\, 2m$ and $k \ge 2e$, $k > \mathrm{ord}\det H_Q$,
  $A_{\pi^k}(Q, Q) = |O(Q\bmod\pi^k)\,e_0|\cdot q^{en}\cdot A_{\pi^k}(Q', Q')$: orbit–stabilizer for $O(Q \bmod \pi^k)$, the stabilizer
  of $e_0$ being $\{\begin{pmatrix}1 & s^{\mathsf T}\\ 0 & Y\end{pmatrix} : 2ms = 0,\ Q'\circ Y = Q'\}$ (`fixEquiv`) with $q^{en}$ choices of $s$
  (`card_ann`). The factor $q^{en} = |2m|_\mathfrak p^{-n}$ is exactly the Jacobian.
* `localOrbitalIdentityAt_of_orbitCount`: at every prime, the local orbital identity follows from
  `LocalTypeOrbitCount` ($W_\mathfrak p\cdot|O(Q\bmod\varpi^k)e_0| = \#\{Q(x)\equiv m \bmod \varpi^k\}$ for $k \gg 0$), a statement
  with no densities and no Jacobian; it holds at $\mathfrak p \nmid 2m$ (`localTypeOrbitCount_of_not_mem`).

**Not proved here:** the identity at the finitely many $\mathfrak p \mid 2m$ (the dyadic primes and the primes dividing $m$),
where there can be several local types and $|2m|_\mathfrak p \ne 1$. There it needs the comparison of the index-normalized
Haar measures with the gauge forms on the stabilizers $K_M$ of non-split lattices.

**Conventions.** Indices are 0-based: $e_0 = (1, 0, \dots, 0)$, $x_0$ is the coordinate of $\langle m\rangle$.
The local type sum uses the representative $\mathfrak o_\mathfrak p^{n+1}$ for its own type and `Quotient.out` otherwise
(`locRep`); the weights do not depend on the representative (unimodularity of $O(Q')(F_\mathfrak p)$), which is used only
through the global weights (`LocalOrbitalGlobal.lean`), where it is proved.
-/
import QuadFormsKB.Tamagawa.LocalIdentity
import QuadFormsKB.Tamagawa.Reflection
import QuadFormsKB.LocalDensity.FormDensitySelf

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open QuadForm

section Count

variable {A : Type*} [CommRing A] {n : ℕ}

theorem eval_splitForm_cons (a : A) (Q' : QuadForm A n) (t : A) (x : Fin n → A) :
    (splitForm a Q').eval (Fin.cons t x) = a * t * t + Q'.eval x := by
  rw [QuadForm.eval, evalIn_splitForm]; rfl

theorem eval_splitForm_e₀' (a : A) (Q' : QuadForm A n) :
    (splitForm a Q').eval (e₀ : Fin (n + 1) → A) = a := by
  rw [QuadForm.eval, evalIn_splitForm_e₀]; rfl

/-- $Q \circ \mathrm{diag}(1, X') = \langle a\rangle \perp (Q' \circ X')$ for $Q = \langle a\rangle\perp Q'$. -/
theorem compMat_cornerMat (a : A) (Q' : QuadForm A n) (X : Matrix (Fin n) (Fin n) A) :
    (splitForm a Q').compMat (cornerMat 1 X) = splitForm a (Q'.compMat X) := by
  refine eq_of_eval_eq fun y => ?_
  rw [eval_compMat, ← Fin.cons_self_tail y, cornerMat_mulVec, eval_splitForm_cons, eval_splitForm_cons,
    eval_compMat, one_mul]

theorem splitForm_injective_right {a : A} {Q₁ Q₂ : QuadForm A n} (h : splitForm a Q₁ = splitForm a Q₂) :
    Q₁ = Q₂ := by
  ext i j
  have := congrArg (fun Q : QuadForm A (n + 1) => Q.coeff i.succ j.succ) h
  simpa [splitForm_coeff] using this

theorem eval_neg' (Q : QuadForm A n) (y : Fin n → A) : Q.eval (-y) = Q.eval y := by
  rw [eval_eq_dotProduct', eval_eq_dotProduct', mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]

/-- $Q(-y) = Q(y)$, so $Q \circ (-X) = Q \circ X$. -/
theorem compMat_neg (Q : QuadForm A n) (X : Matrix (Fin n) (Fin n) A) : Q.compMat (-X) = Q.compMat X := by
  refine eq_of_eval_eq fun y => ?_
  rw [eval_compMat, eval_compMat, neg_mulVec, eval_neg']

/-- **The fibre over $e_0$:** if $Q\circ X = Q$ for $Q = \langle a\rangle \perp Q'$ with $2a$ a unit and $X e_0 = e_0$,
then $X = \mathrm{diag}(1, X')$ with $X'$ the lower-right block. *Proof:* $X^{\mathsf T}HX = H$ and $e_0^{\mathsf T}H = 2a\,e_0^{\mathsf T}$
give $2a\,e_0^{\mathsf T}X = e_0^{\mathsf T}X^{\mathsf T}HX = (Xe_0)^{\mathsf T}HX = 2a\,e_0^{\mathsf T}$. -/
theorem eq_cornerMat_of_fix {a : A} (ha : IsUnit (2 * a)) (Q' : QuadForm A n)
    {X : Matrix (Fin (n + 1)) (Fin (n + 1)) A} (hX : (splitForm a Q').compMat X = splitForm a Q')
    (h0 : X *ᵥ (e₀ : Fin (n + 1) → A) = e₀) : X = cornerMat 1 (X.submatrix Fin.succ Fin.succ) := by
  have hH := congrArg QuadForm.hessian hX
  rw [hessian_compMat, hessian_splitForm] at hH
  have hcol : ∀ i, X i 0 = (e₀ : Fin (n + 1) → A) i := by
    intro i
    have := congrFun h0 i
    rw [e₀_eq_single, mulVec_single_one] at this
    rw [e₀_eq_single]; exact this
  have hrow : ∀ j, X 0 j = (e₀ : Fin (n + 1) → A) j := by
    have h1 : Pi.single 0 1 ᵥ* (Xᵀ * cornerMat (2 * a) Q'.hessian * X) =
        Pi.single 0 1 ᵥ* cornerMat (2 * a) Q'.hessian := by rw [hH]
    rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_transpose, ← e₀_eq_single, h0, e₀_eq_single] at h1
    have h2 : Pi.single (0 : Fin (n + 1)) (1 : A) ᵥ* cornerMat (2 * a) Q'.hessian = (2 * a) • Pi.single 0 1 := by
      rw [single_one_vecMul]
      ext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [Matrix.row]
    rw [h2, smul_vecMul, single_one_vecMul] at h1
    intro j
    have := congrFun h1 j
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.row] at this
    rw [e₀_eq_single]
    exact ha.mul_left_cancel this
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simpa using hcol 0
  · simpa [Fin.succ_ne_zero] using hrow j.succ
  · simpa [Fin.succ_ne_zero] using hcol i.succ
  · rfl

/-- **The reflection data in $x - e_0$:** with $z = x - e_0$, $Q(x) = a$ and $u = Q(z)$ a unit, $w = u^{-1}Hz$, the
reflection $\tau_z$ preserves $Q$, satisfies $\tau_z^2 = 1$ and $\tau_z e_0 = x$. -/
theorem exists_refl_e₀ [IsLocalRing A] {a : A} (h4 : IsUnit (4 * a)) (Q' : QuadForm A n)
    {x : Fin (n + 1) → A} (hx : (splitForm a Q').eval x = a) :
    ∃ σ : Matrix (Fin (n + 1)) (Fin (n + 1)) A, (splitForm a Q').compMat σ = splitForm a Q' ∧
      σ * σ = 1 ∧ σ *ᵥ (e₀ : Fin (n + 1) → A) = x := by
  set Q := splitForm a Q'
  have he : Q.eval (e₀ : Fin (n + 1) → A) = a := eval_splitForm_e₀' a Q'
  have hee : (e₀ : Fin (n + 1) → A) ⬝ᵥ (Q.hessian *ᵥ e₀) = 2 * a := by
    rw [dotProduct_hessian_self, he]
  have hsymm : ∀ y z : Fin (n + 1) → A, y ⬝ᵥ (Q.hessian *ᵥ z) = z ⬝ᵥ (Q.hessian *ᵥ y) := by
    intro y z
    rw [dotProduct_mulVec, ← mulVec_transpose, hessian_transpose, dotProduct_comm]
  set b := x ⬝ᵥ (Q.hessian *ᵥ e₀)
  -- the values of Q at x ∓ e₀
  have hm : Q.eval (x - e₀) = 2 * a - b := by
    have := eval_polar Q x (-e₀)
    rw [← sub_eq_add_neg] at this
    have h1 : Q.eval (-(e₀ : Fin (n + 1) → A)) = a := by
      rw [eval_neg', he]
    rw [h1, hx, mulVec_neg, dotProduct_neg] at this
    linear_combination this
  have hp : Q.eval (x + e₀) = 2 * a + b := by
    have := eval_polar Q x e₀
    rw [hx, he] at this
    linear_combination this
  have hsum : IsUnit (Q.eval (x - e₀) + Q.eval (x + e₀)) := by
    rw [hm, hp]; convert h4 using 1; ring
  -- a reflection with Q(z) a unit
  have refl : ∀ z : Fin (n + 1) → A, IsUnit (Q.eval z) →
      ∃ w, Q.compMat (reflMat z w) = Q ∧ reflMat z w * reflMat z w = 1 ∧
        Q.eval z * (w ⬝ᵥ e₀) = z ⬝ᵥ (Q.hessian *ᵥ e₀) := by
    intro z hz
    obtain ⟨u, hu⟩ := hz
    refine ⟨(↑u⁻¹ : A) • (Q.hessian *ᵥ z), ?_, ?_, ?_⟩
    · refine compMat_reflMat Q ?_
      rw [smul_smul, ← hu, Units.mul_inv, one_smul]
    · have hwz : ((↑u⁻¹ : A) • (Q.hessian *ᵥ z)) ⬝ᵥ z = 2 := by
        rw [smul_dotProduct, dotProduct_comm, dotProduct_hessian_self, ← hu, smul_eq_mul]
        rw [mul_left_comm, Units.inv_mul, mul_one]
      rw [reflMat, sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, vecMulVec_mul_vecMulVec, hwz]
      ext i j
      simp [vecMulVec_apply, two_smul]
      ring
    · rw [smul_dotProduct, smul_eq_mul, ← hu, ← mul_assoc, Units.mul_inv, one_mul, dotProduct_comm, hsymm]
  have hτ : ∀ z w : Fin (n + 1) → A, reflMat z w *ᵥ (e₀ : Fin (n + 1) → A) = e₀ - (w ⬝ᵥ e₀) • z :=
    fun z w => reflMat_mulVec z w e₀
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with hu | hu
  · obtain ⟨w, h1, h2, h3⟩ := refl (x - e₀) hu
    have hb : (x - e₀) ⬝ᵥ (Q.hessian *ᵥ e₀) = -Q.eval (x - e₀) := by
      rw [sub_dotProduct, hee, hm]; ring
    rw [hb] at h3
    have hw : w ⬝ᵥ e₀ = -1 := hu.mul_left_cancel (by rw [h3]; ring)
    refine ⟨reflMat (x - e₀) w, h1, h2, ?_⟩
    rw [hτ, hw, neg_one_smul, sub_neg_eq_add, add_sub_cancel]
  · obtain ⟨w, h1, h2, h3⟩ := refl (x + e₀) hu
    have hb : (x + e₀) ⬝ᵥ (Q.hessian *ᵥ e₀) = Q.eval (x + e₀) := by
      rw [add_dotProduct, hee, hp]; ring
    rw [hb] at h3
    have hw : w ⬝ᵥ e₀ = 1 := hu.mul_left_cancel (by rw [h3]; ring)
    refine ⟨-reflMat (x + e₀) w, by rw [compMat_neg, h1], by rw [neg_mul_neg, h2], ?_⟩
    rw [neg_mulVec, hτ, hw, one_smul]
    abel

/-- **Counting by the first column** (Weil's fibration $O(Q) \to \{Q = a\}$ mod $\pi^k$, $2a$ a unit): over a local
ring $A$ with $2a \in A^\times$, the solutions $X$ of $Q \circ X = Q$ for $Q = \langle a\rangle\perp Q'$ are in bijection
with pairs $(x, X')$, $Q(x) = a$, $Q' \circ X' = Q'$, via $X \mapsto (Xe_0, \text{block of } \sigma_x X)$, where $\sigma_x$ is the
reflection of `exists_refl_e₀` carrying $e_0$ to $x$. -/
def splitEquiv [IsLocalRing A] {a : A} (ha : IsUnit (2 * a)) (Q' : QuadForm A n) :
    {X : Matrix (Fin (n + 1)) (Fin (n + 1)) A // (splitForm a Q').compMat X = splitForm a Q'} ≃
      {x : Fin (n + 1) → A // (splitForm a Q').eval x = a} ×
        {X : Matrix (Fin n) (Fin n) A // Q'.compMat X = Q'} := by
  classical
  have h4 : IsUnit (4 * a) := by
    have : (4 : A) * a = 2 * (2 * a) := by ring
    rw [this]
    exact (isUnit_of_mul_isUnit_left (x := (2 : A)) (y := a) ha).mul ha
  have he : (splitForm a Q').eval (e₀ : Fin (n + 1) → A) = a := eval_splitForm_e₀' a Q'
  let σ : {x : Fin (n + 1) → A // (splitForm a Q').eval x = a} → Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
    fun x => (exists_refl_e₀ h4 Q' x.2).choose
  have hσ : ∀ x, (splitForm a Q').compMat (σ x) = splitForm a Q' ∧ σ x * σ x = 1 ∧
      σ x *ᵥ (e₀ : Fin (n + 1) → A) = x.1 := fun x => (exists_refl_e₀ h4 Q' x.2).choose_spec
  have hcol : ∀ X : {X : Matrix (Fin (n + 1)) (Fin (n + 1)) A // (splitForm a Q').compMat X = splitForm a Q'},
      (splitForm a Q').eval (X.1 *ᵥ e₀) = a := by
    intro X
    rw [← eval_compMat, X.2, he]
  have hfix : ∀ X : {X : Matrix (Fin (n + 1)) (Fin (n + 1)) A // (splitForm a Q').compMat X = splitForm a Q'},
      (splitForm a Q').compMat (σ ⟨_, hcol X⟩ * X.1) = splitForm a Q' ∧
        (σ ⟨_, hcol X⟩ * X.1) *ᵥ (e₀ : Fin (n + 1) → A) = e₀ := by
    intro X
    obtain ⟨h1, h2, h3⟩ := hσ ⟨_, hcol X⟩
    refine ⟨by rw [← compMat_mul, h1, X.2], ?_⟩
    rw [← mulVec_mulVec]
    have h4' : σ ⟨_, hcol X⟩ *ᵥ (σ ⟨_, hcol X⟩ *ᵥ (e₀ : Fin (n + 1) → A)) =
        σ ⟨_, hcol X⟩ *ᵥ (X.1 *ᵥ e₀) := congrArg _ h3
    rw [← h4', mulVec_mulVec, h2, one_mulVec]
  have hblock : ∀ X : {X : Matrix (Fin (n + 1)) (Fin (n + 1)) A // (splitForm a Q').compMat X = splitForm a Q'},
      Q'.compMat ((σ ⟨_, hcol X⟩ * X.1).submatrix Fin.succ Fin.succ) = Q' := by
    intro X
    obtain ⟨h1, h2⟩ := hfix X
    have hc := eq_cornerMat_of_fix ha Q' h1 h2
    rw [hc, compMat_cornerMat] at h1
    exact splitForm_injective_right h1
  refine
    { toFun := fun X => (⟨_, hcol X⟩, ⟨_, hblock X⟩)
      invFun := fun p => ⟨σ p.1 * cornerMat 1 p.2.1, ?_⟩
      left_inv := fun X => ?_
      right_inv := fun p => ?_ }
  · rw [← compMat_mul, (hσ p.1).1, compMat_cornerMat, p.2.2]
  · apply Subtype.ext
    obtain ⟨h1, h2⟩ := hfix X
    have hc := eq_cornerMat_of_fix ha Q' h1 h2
    show σ ⟨_, hcol X⟩ * cornerMat 1 _ = X.1
    rw [← hc, ← mul_assoc, (hσ _).2.1, one_mul]
  · have h1 : (σ p.1 * cornerMat 1 p.2.1) *ᵥ (e₀ : Fin (n + 1) → A) = p.1.1 := by
      rw [← mulVec_mulVec, show cornerMat (1 : A) p.2.1 *ᵥ (e₀ : Fin (n + 1) → A) = e₀ by
        rw [cornerMat_mulVec, one_mul, mulVec_zero], (hσ p.1).2.2]
    have hp1 : (⟨_, hcol ⟨σ p.1 * cornerMat 1 p.2.1, by
        rw [← compMat_mul, (hσ p.1).1, compMat_cornerMat, p.2.2]⟩⟩ :
          {x : Fin (n + 1) → A // (splitForm a Q').eval x = a}) = p.1 := Subtype.ext h1
    refine Prod.ext hp1 (Subtype.ext ?_)
    simp only
    rw [hp1, ← mul_assoc, (hσ p.1).2.1, one_mul]
    ext i j; rfl

/-- **Weil's fibration count at a unit:** $|\{X : Q\circ X = Q\}| = |\{x : Q(x) = a\}|\cdot|\{X' : Q'\circ X' = Q'\}|$ over a
local ring with $2a$ a unit. -/
@[kb "weil1982" "§3.4 (fibration count mod π^k) [unverified]"]
theorem card_compMat_splitForm [IsLocalRing A] {a : A} (ha : IsUnit (2 * a)) (Q' : QuadForm A n) :
    Nat.card {X : Matrix (Fin (n + 1)) (Fin (n + 1)) A // (splitForm a Q').compMat X = splitForm a Q'} =
      Nat.card {x : Fin (n + 1) → A // (splitForm a Q').eval x = a} *
        Nat.card {X : Matrix (Fin n) (Fin n) A // Q'.compMat X = Q'} := by
  rw [Nat.card_congr (splitEquiv ha Q'), Nat.card_prod]

end Count

end QuadFormsKB.Tamagawa

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Tamagawa

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

theorem isLocalRing_quot {π : R} (hπ : Irreducible π) {k : ℕ} (hk : 0 < k) :
    IsLocalRing (R ⧸ Ideal.span {π ^ k}) := by
  have : Nontrivial (R ⧸ Ideal.span {π ^ k}) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact fun h => hπ.not_isUnit (isUnit_of_dvd_unit (dvd_pow_self π hk.ne') h))
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- **Weil's fibration count at level $\pi^k$** ($k \ge 1$, $2m$ a unit): $A_{\pi^k}(Q, Q) = r_{\pi^k}(m)\cdot A_{\pi^k}(Q', Q')$ for
$Q = \langle m\rangle\perp Q'$, any $Q'$ (degenerate or not, any determinant), any residue characteristic $\ne 2$. -/
theorem repCountForm_splitForm_unit {π : R} (hπ : Irreducible π) {k : ℕ} (hk : 0 < k) {m : R}
    (hm : IsUnit (2 * m)) (Q' : QuadForm R n) :
    repCountForm (splitForm m Q') (splitForm m Q') π k =
      repCount (splitForm m Q') π k m * repCountForm Q' Q' π k := by
  have := isLocalRing_quot hπ hk
  have hu : IsUnit (2 * Ideal.Quotient.mk (Ideal.span {π ^ k}) m) := by
    have := hm.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))
    rwa [map_mul, map_ofNat] at this
  unfold repCountForm repCount
  rw [map_splitForm, card_compMat_splitForm hu]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [evalIn_eq_eval_map' (Ideal.Quotient.mk _) _ _ (Ideal.Quotient.algebraMap_eq _), map_splitForm]

/-- **Weil's local identity at a prime $\pi \nmid 2m$** (any $Q'$ nondegenerate, $\det H_{Q'}$ arbitrary):
$$\beta_\pi(Q', Q')\cdot\beta_\pi(Q, m) = \beta_\pi(Q, Q),\qquad Q = \langle m\rangle\perp Q'.$$
*Proof:* the counts satisfy $A_{\pi^k}(Q,Q) = r_{\pi^k}(m)\,A_{\pi^k}(Q',Q')$ at every level (`repCountForm_splitForm_unit`)
and the normalizing exponents add up: $\tfrac{(n+1)n}{2} = n + \tfrac{n(n-1)}{2}$. -/
@[kb "weil1982" "§3.4 (local fibration, p ∤ 2m) [unverified]"]
theorem localIdentity_unit [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π) {m : R}
    (hm : IsUnit (2 * m)) (h20 : (2 : R) ≠ 0) (Q' : QuadForm R n) (hQ' : Q'.Nondegenerate) :
    localDensityForm Q' Q' π * localDensity (splitForm m Q') π m =
      localDensityForm (splitForm m Q') (splitForm m Q') π := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hQ : (splitForm m Q').Nondegenerate := by
    rw [QuadForm.Nondegenerate, det_hessian_splitForm]
    exact mul_ne_zero (mul_ne_zero h20 hm0) hQ'
  have e1 := localDensityForm_eventually_eq Q' Q' hQ' π hπ le_rfl
  have e2 := localDensityForm_eventually_eq (splitForm m Q') (splitForm m Q') hQ π hπ le_rfl
  have e3 := localDensity_eventually_eq (splitForm m Q') hQ π hπ m hm0 h20
  obtain ⟨k, hk⟩ := (e1.and (e2.and (e3.and (Filter.eventually_gt_atTop 0)))).exists
  obtain ⟨h1, h2, h3, hk0⟩ := hk
  rw [← h1, ← h2, ← h3, repCountForm_splitForm_unit hπ hk0 hm Q']
  have hq : (q R : ℝ) ≠ 0 := by exact_mod_cast (q_pos (R := R)).ne'
  have hexp : (n + 1) * (n + 1) - (n + 1) * (n + 1 + 1) / 2 = (n * n - n * (n + 1) / 2) + (n + 1 - 1) := by
    rw [self_exp, self_exp, Tamagawa.nat_tri_succ]; omega
  rw [hexp, Nat.mul_add k, pow_add]
  push_cast
  field_simp

end QuadFormsKB.LocalDensity.DVR

namespace QuadFormsKB.Tamagawa

open NumberField IsDedekindDomain Lattices MulAction LocalDensity

section LocalTypes

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (m : F) (Q' : QuadForm F n)

local notation "QS" => splitForm m Q'
local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem e₀_mem_std : (e₀ : Fin (n + 1) → Fv) ∈ std v := by
  rw [mem_std_cons]
  refine ⟨by simp, fun i => ?_⟩
  simp

/-- **The local type set** $Y_\mathfrak p = \{M \in O(V)(F_\mathfrak p)\cdot\mathfrak o_\mathfrak p^{n+1} : e_0 \in M\}$ for
$V = (F^{n+1}, \langle m\rangle\perp Q')$: the local lattices in the local genus of $\mathfrak o_\mathfrak p^{n+1}$ that contain $e_0$.
The group $O(Q')(F_\mathfrak p)$ acts through $\mathrm{diag}(1, \cdot)$; its orbits are the **local types** at $\mathfrak p$
(Weil 1982, §3.4 [unverified]; Kitaoka 1993, §6.8 [unverified]). -/
@[kb "weil1982" "§3.4 (local types) [unverified]"]
def LocCompSet : Type _ :=
  {M : Submodule 𝔬 (Fin (n + 1) → Fv) //
    (∃ g : orthGroup QS Fv, locAct v (g : GL (Fin (n + 1)) Fv) (std v) = M) ∧ (e₀ : Fin (n + 1) → Fv) ∈ M}

theorem e₀_mem_locAct_orthEmb (h : orthGroup Q' Fv) {M : Submodule 𝔬 (Fin (n + 1) → Fv)}
    (hM : (e₀ : Fin (n + 1) → Fv) ∈ M) :
    (e₀ : Fin (n + 1) → Fv) ∈ locAct v (orthEmb m Q' Fv h : GL (Fin (n + 1)) Fv) M :=
  ⟨e₀, hM, orthEmb_mulVec_e₀ m Q' Fv h⟩

instance LocCompSet.instMulAction : MulAction (orthGroup Q' Fv) (LocCompSet v m Q') where
  smul h M := ⟨locAct v (orthEmb m Q' Fv h : GL (Fin (n + 1)) Fv) M.1, by
      obtain ⟨g, hg⟩ := M.2.1
      exact ⟨orthEmb m Q' Fv h * g, by rw [Subgroup.coe_mul, locAct_mul, hg]⟩,
    e₀_mem_locAct_orthEmb v m Q' h M.2.2⟩
  one_smul M := Subtype.ext (by
    show locAct v (orthEmb m Q' Fv 1 : GL (Fin (n + 1)) Fv) M.1 = M.1
    rw [map_one, OneMemClass.coe_one, locAct_one])
  mul_smul a b M := Subtype.ext (by
    show locAct v (orthEmb m Q' Fv (a * b) : GL (Fin (n + 1)) Fv) M.1 =
      locAct v (orthEmb m Q' Fv a : GL (Fin (n + 1)) Fv) (locAct v (orthEmb m Q' Fv b : GL (Fin (n + 1)) Fv) M.1)
    rw [map_mul, Subgroup.coe_mul, locAct_mul])

theorem LocCompSet.smul_val (h : orthGroup Q' Fv) (M : LocCompSet v m Q') :
    (h • M).1 = locAct v (orthEmb m Q' Fv h : GL (Fin (n + 1)) Fv) M.1 := rfl

/-- The base point $\mathfrak o_\mathfrak p^{n+1} \in Y_\mathfrak p$. -/
def locStdPt : LocCompSet v m Q' := ⟨std v, ⟨1, locAct_one _⟩, e₀_mem_std v⟩

/-- **The local types** at $\mathfrak p$: the $O(Q')(F_\mathfrak p)$-orbits on $Y_\mathfrak p$. -/
abbrev LocTypes : Type _ := orbitRel.Quotient (orthGroup Q' Fv) (LocCompSet v m Q')

/-- **The representative of a local type:** $\mathfrak o_\mathfrak p^{n+1}$ for its own type, `Quotient.out` otherwise. -/
def locRep (t : LocTypes v m Q') : LocCompSet v m Q' := by
  classical
  exact if (Quotient.mk'' (locStdPt v m Q') : LocTypes v m Q') = t then locStdPt v m Q' else t.out

theorem locRep_mk (t : LocTypes v m Q') : (Quotient.mk'' (locRep v m Q' t) : LocTypes v m Q') = t := by
  classical
  unfold locRep
  split_ifs with h
  · exact h
  · exact Quotient.out_eq' t

theorem locRep_std : locRep v m Q' (Quotient.mk'' (locStdPt v m Q')) = locStdPt v m Q' := by
  classical
  unfold locRep
  rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]

/-- **The local weight** of $M \in Y_\mathfrak p$: with $K_M = \mathrm{Stab}_{O(Q')(F_\mathfrak p)}(M)$ and $K_0' = O(\mathfrak o_\mathfrak p^n)$,
$$w_\mathfrak p(M) = \frac{\mu(K_0')}{\mu(K_M)} = \frac{[K_0' : K_M\cap K_0']}{[K_M : K_M \cap K_0']},$$
the local factor of `typeWeight` (an index ratio; any Haar measure). -/
@[kb "weil1982" "§3.5 (local weights) [unverified locator]"]
def locWeight (M : LocCompSet v m Q') : ℝ :=
  ((stabilizer (orthGroup Q' Fv) M).relIndex (stdStab Q' v) : ℝ) /
    ((stdStab Q' v).relIndex (stabilizer (orthGroup Q' Fv) M) : ℝ)

/-- **The local type sum** $W_\mathfrak p = \sum_{t} w_\mathfrak p(M_t)$ over the local types $t$ at $\mathfrak p$, $M_t$ = `locRep t`. -/
@[kb "weil1982" "§3.5 (local type sum) [unverified locator]"]
def locTypeSum : ℝ := ∑ᶠ t : LocTypes v m Q', locWeight v m Q' (locRep v m Q' t)

theorem stabilizer_locStdPt : stabilizer (orthGroup Q' Fv) (locStdPt v m Q') = stdStab Q' v := by
  ext h
  rw [mem_stabilizer_iff, ← mem_stdStab_orthEmb_iff m Q' v h]
  constructor
  · intro hh; exact congrArg Subtype.val hh
  · intro hh; exact Subtype.ext hh

theorem locWeight_std : locWeight v m Q' (locStdPt v m Q') = 1 := by
  simp [locWeight, stabilizer_locStdPt]

/-- If $\mathfrak o_\mathfrak p^{n+1}$ is the only local type, $W_\mathfrak p = 1$. -/
theorem locTypeSum_eq_one_of_subsingleton (h : ∀ M : LocCompSet v m Q', ∃ g : orthGroup Q' Fv, g • locStdPt v m Q' = M) :
    locTypeSum v m Q' = 1 := by
  have hs : ∀ t : LocTypes v m Q', t = Quotient.mk'' (locStdPt v m Q') := by
    intro t
    induction t using Quotient.inductionOn' with
    | h M =>
      obtain ⟨g, hg⟩ := h M
      exact Quotient.sound' ⟨g, hg⟩
  have : Unique (LocTypes v m Q') := ⟨⟨Quotient.mk'' (locStdPt v m Q')⟩, hs⟩
  rw [locTypeSum, finsum_unique, show (default : LocTypes v m Q') = _ from hs default, locRep_std,
    locWeight_std]

end LocalTypes


section Transitive

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem isUnit_ι_of_not_mem {a : 𝓞 F} (ha : a ∉ v.asIdeal) : IsUnit (NF.ι v a) :=
  DVR.dvr_isUnit_of_not_dvd (NF.irreducible_π v) (by rw [NF.π_dvd_ι_iff]; exact ha)

theorem coe_e₀_o : (fun i => (((e₀ : Fin (n + 1) → 𝔬) i : 𝔬) : Fv)) = (e₀ : Fin (n + 1) → Fv) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

/-- **Transitivity at $\mathfrak p \nmid 2m$** (every $Q'$ over $\mathcal O_F$, $\det H_{Q'}$ arbitrary): $O(Q')(F_\mathfrak p)$ is transitive
on $Y_\mathfrak p$, so there is exactly one local type, that of $\mathfrak o_\mathfrak p^{n+1}$. *Proof:* for $M = g\,\mathfrak o_\mathfrak p^{n+1} \ni e_0$,
$x = g^{-1}e_0 \in \mathfrak o_\mathfrak p^{n+1}$ has $Q(x) = m$; one of $Q(x \mp e_0)$ is a unit (their sum is $4m$), and the reflection in
that vector, composed with $-1$ if needed, is $k \in O(\mathfrak o_\mathfrak p^{n+1})$ with $ke_0 = x$ (`exists_refl_e₀`). Then $gk$ fixes
$e_0$, so $gk = \mathrm{diag}(1, h)$ (`exists_orthEmb_eq`) and $M = gk\,\mathfrak o_\mathfrak p^{n+1} = h\cdot\mathfrak o_\mathfrak p^{n+1}$
(O'Meara 1963, §92 [unverified], for the transitivity of $O(L_\mathfrak p)$ on vectors of unit norm). -/
@[kb "omeara1963" "§92 (transitivity on unit vectors) [unverified]"]
theorem exists_smul_locStdPt (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) (h2m : 2 * m₀ ∉ v.asIdeal)
    (M : LocCompSet v (algebraMap (𝓞 F) F m₀) (Q₀'.map (algebraMap (𝓞 F) F))) :
    ∃ h : orthGroup (Q₀'.map (algebraMap (𝓞 F) F)) Fv,
      h • locStdPt v (algebraMap (𝓞 F) F m₀) (Q₀'.map (algebraMap (𝓞 F) F)) = M := by
  set Q₀ := splitForm m₀ Q₀'
  have hsplit : splitForm (algebraMap (𝓞 F) F m₀) (Q₀'.map (algebraMap (𝓞 F) F)) = Q₀.map (algebraMap (𝓞 F) F) := (map_splitForm _ _ _).symm
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := fun h => h2m (v.asIdeal.mul_mem_right _ h)
  have hm : m₀ ∉ v.asIdeal := fun h => h2m (v.asIdeal.mul_mem_left _ h)
  obtain ⟨⟨g, hgO⟩, hg⟩ := M.2.1
  have he := M.2.2
  rw [← hg] at he
  obtain ⟨y, hy, hgy⟩ := he
  replace hgy : g.val *ᵥ y = e₀ := hgy
  have hyv : ∀ i, Valued.v (y i) ≤ 1 := by
    intro i; have := hy i; rwa [neg_zero, WithZero.exp_zero] at this
  let y' : Fin (n + 1) → 𝔬 := fun i => ⟨y i, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hyv i)⟩
  have hyy : (fun i => (y' i : Fv)) = y := rfl
  -- Q(y) = m
  have hQy : (splitForm (algebraMap (𝓞 F) F m₀) (Q₀'.map (algebraMap (𝓞 F) F))).evalIn Fv y = algebraMap F Fv (algebraMap (𝓞 F) F m₀) := by
    have h1 := evalIn_mulVec_of_mem (splitForm (algebraMap (𝓞 F) F m₀) (Q₀'.map (algebraMap (𝓞 F) F))) hgO y
    rw [hgy, evalIn_splitForm_e₀] at h1
    exact h1.symm
  have hQy' : (splitForm (NF.ι v m₀) (NF.Qp v Q₀')).eval y' = NF.ι v m₀ := by
    apply Subtype.ext
    rw [← map_splitForm]
    have h1 := evalIn_coe_o v Q₀ y'
    rw [hyy, ← hsplit, hQy] at h1
    exact h1.symm
  have h4 : IsUnit (4 * NF.ι v m₀) := by
    have : (4 : 𝔬) * NF.ι v m₀ = NF.ι v 2 * NF.ι v 2 * NF.ι v m₀ := by
      rw [map_ofNat]; norm_num
    rw [this]
    exact ((isUnit_ι_of_not_mem v h2).mul (isUnit_ι_of_not_mem v h2)).mul (isUnit_ι_of_not_mem v hm)
  obtain ⟨σ, hσQ, hσσ, hσe⟩ := exists_refl_e₀ h4 (NF.Qp v Q₀') hQy'
  let P₀ : GL (Fin (n + 1)) 𝔬 := ⟨σ, σ, hσσ, hσσ⟩
  let k : GL (Fin (n + 1)) Fv := Matrix.GeneralLinearGroup.map (algebraMap 𝔬 Fv) P₀
  have hkval : k.val = σ.map (algebraMap 𝔬 Fv) := rfl
  have hk : k ∈ orthGroup (splitForm (algebraMap (𝓞 F) F m₀) (Q₀'.map (algebraMap (𝓞 F) F))) Fv := by
    refine mem_orthGroup_of_evalIn _ fun z => ?_
    refine evalIn_eq_of_evalIn_o v (A := fun z => (splitForm (algebraMap (𝓞 F) F m₀) (Q₀'.map (algebraMap (𝓞 F) F))).evalIn Fv (k.val *ᵥ z))
      (B := (splitForm (algebraMap (𝓞 F) F m₀) (Q₀'.map (algebraMap (𝓞 F) F))).evalIn Fv)
      (fun c y => by simp only [mulVec_smul]; exact evalIn_smul' _ c _) (fun c y => evalIn_smul' _ c y)
      (fun z => ?_) z
    have e1 : k.val *ᵥ (fun i => (z i : Fv)) = fun i => ((σ *ᵥ z) i : Fv) := by
      funext i
      rw [hkval]
      exact (RingHom.map_mulVec (algebraMap 𝔬 Fv) _ z i).symm
    rw [e1, hsplit, evalIn_coe_o v, evalIn_coe_o v]
    congr 1
    rw [show NF.Qp v Q₀ = splitForm (NF.ι v m₀) (NF.Qp v Q₀') from map_splitForm _ _ _, ← QuadForm.eval_compMat, hσQ]
  have hkstd : locAct v k (std v) = std v := locAct_map_std v P₀
  have hke : k.val *ᵥ (e₀ : Fin (n + 1) → Fv) = y := by
    rw [← coe_e₀_o v, hkval, ← hyy]
    funext i
    have := RingHom.map_mulVec (algebraMap 𝔬 Fv) σ (e₀ : Fin (n + 1) → 𝔬) i
    rw [hσe] at this
    exact this.symm
  let γ : orthGroup (splitForm (algebraMap (𝓞 F) F m₀) (Q₀'.map (algebraMap (𝓞 F) F))) Fv := ⟨g, hgO⟩ * ⟨k, hk⟩
  have hγ : (γ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀ := by
    show (g * k).val *ᵥ _ = _
    rw [Units.val_mul, ← mulVec_mulVec, hke, hgy]
  have hm2 : algebraMap F Fv (2 * algebraMap (𝓞 F) F m₀) ≠ 0 := by
    rw [map_ne_zero]
    refine mul_ne_zero two_ne_zero ?_
    rw [Ne, map_eq_zero_iff _ RingOfIntegers.coe_injective]
    rintro rfl; exact hm v.asIdeal.zero_mem
  obtain ⟨h, hh⟩ := exists_orthEmb_eq (algebraMap (𝓞 F) F m₀) (Q₀'.map (algebraMap (𝓞 F) F)) Fv hm2 γ hγ
  refine ⟨h, Subtype.ext ?_⟩
  show locAct v (orthEmb (algebraMap (𝓞 F) F m₀) (Q₀'.map (algebraMap (𝓞 F) F)) Fv h : GL (Fin (n + 1)) Fv) (std v) = M.1
  rw [hh]
  show locAct v (g * k) (std v) = M.1
  rw [locAct_mul, hkstd, hg]

/-- **One local type of weight $1$ at $\mathfrak p \nmid 2m$**: $W_\mathfrak p = 1$. -/
theorem locTypeSum_eq_one (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) (h2m : 2 * m₀ ∉ v.asIdeal) :
    locTypeSum v (algebraMap (𝓞 F) F m₀) (Q₀'.map (algebraMap (𝓞 F) F)) = 1 :=
  locTypeSum_eq_one_of_subsingleton v _ _ (exists_smul_locStdPt v m₀ Q₀' h2m)

end Transitive


section PerPrime

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

/-- **The Jacobian** $|2m|_\mathfrak p$ (normalized: $|x|_\mathfrak p = N\mathfrak p^{-\mathrm{ord}_\mathfrak p x}$; Mathlib's norm on
$F_\mathfrak p$). The local fibration $O(V_\mathfrak p) \to \{Q = m\}$ has the constant $|2m|_\mathfrak p^{-n}$ in coefficient coordinates. -/
def absTwoM (m : 𝓞 F) : ℝ := ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (2 * m))‖

theorem absTwoM_eq_one {m : 𝓞 F} (h2m : 2 * m ∉ v.asIdeal) : absTwoM v m = 1 :=
  (NumberField.FinitePlace.norm_eq_one_iff_notMem F v (2 * m)).mpr h2m

theorem absTwoM_pos {m : 𝓞 F} (hm : m ≠ 0) : 0 < absTwoM v m := by
  refine norm_pos_iff.mpr ?_
  rw [map_ne_zero, Ne, map_eq_zero_iff _ RingOfIntegers.coe_injective]
  exact mul_ne_zero two_ne_zero hm

/-- **Weil's local identity at every prime $\mathfrak p \nmid 2m$** (bad primes of $Q_0'$ included):
$\alpha_\mathfrak p(L', L')\cdot\beta_\mathfrak p(L, m) = \alpha_\mathfrak p(L, L)$ for $L = \mathfrak o_\mathfrak p e_0 \perp L'$, $Q(e_0) = m$,
$Q_0'$ nondegenerate with any determinant. Generalizes `localIdentity_good` ($\mathfrak p \nmid 2m\det H_{Q_0'}$), by
counting instead of closed forms (`DVR.localIdentity_unit`). -/
@[kb "weil1982" "§3.4 (local fibration, p ∤ 2m) [unverified]"]
theorem localIdentity_unit_nf (m : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate)
    (h2m : 2 * m ∉ v.asIdeal) :
    NF.siegelDensity v Q₀' Q₀' * NF.localDensity v (splitForm m Q₀') m =
      NF.siegelDensity v (splitForm m Q₀') (splitForm m Q₀') := by
  have hu : IsUnit (2 * NF.ι v m) := by
    have := isUnit_ι_of_not_mem v h2m
    rwa [map_mul, map_ofNat] at this
  have hsplit : NF.Qp v (splitForm m Q₀') = splitForm (NF.ι v m) (NF.Qp v Q₀') := map_splitForm _ _ _
  unfold NF.siegelDensity
  simp only [↓reduceIte]
  rw [NF.localDensityForm_eq_completion, NF.localDensityForm_eq_completion, NF.localDensity_eq_completion,
    hsplit, ← DVR.localIdentity_unit (NF.irreducible_π v) hu (NF.two_ne_zero' v) (NF.Qp v Q₀')
      (NF.nondegenerate_Qp v hQ')]
  ring

/-- **Weil's local orbital identity at the prime $\mathfrak p$** for $L = \mathcal O_F e_0 \perp \mathcal O_F^n$, $Q(e_0) = m$
(Weil 1982, §3.4 [unverified]; Kitaoka 1993, §6.8 [unverified]; Siegel 1935 [unverified]):
$$W_\mathfrak p\cdot\alpha_\mathfrak p(L, L)\cdot|2m|_\mathfrak p^{\,n} = \alpha_\mathfrak p(L', L')\cdot\beta_\mathfrak p(L, m),$$
with $W_\mathfrak p = \sum_{t}w_\mathfrak p(t)$ the sum over the local types $t \in O(Q')(F_\mathfrak p)\backslash Y_\mathfrak p$ (`locTypeSum`),
$\alpha_\mathfrak p$ = `NF.siegelDensity` $= \mathrm{vol}(SO(L_\mathfrak p))$, $\beta_\mathfrak p$ = `NF.localDensity`, $|2m|_\mathfrak p$ = `absTwoM`.

Field:
- `typeSum_eq`: the displayed identity.

*Meaning.* Weil's fibration $O(V_\mathfrak p) \to \{v : Q(v) = m\}$, $g \mapsto ge_0$, fibre $O(e_0^\perp)$: the $O(L_\mathfrak p)$-orbits
on $\{v \in L_\mathfrak p : Q(v) = m\}$ are the local types (Witt), the orbit of $ge_0$ has measure
$\mathrm{vol}(O(L_\mathfrak p))/\mathrm{vol}(\mathrm{Stab})$ for the gauge forms up to the Jacobian $|2m|_\mathfrak p^{-n}$, and the total measure
of the level set is $\beta_\mathfrak p(L, m)$ (`volume_ballQ_eq_localDensity`). The product over $\mathfrak p$ is `LocalOrbitalIdentity` (`localOrbitalIdentity_of_local`). **Proved** at every $\mathfrak p \nmid 2m$
(`localOrbitalIdentityAt_of_not_mem`); at the finitely many $\mathfrak p \mid 2m$ (dyadic primes and primes dividing $m$) it is
an input. *Independence:* a statement about one prime; no global object occurs. -/
@[kb "weil1982" "§3.4 (local fibration, one prime) [unverified]"]
structure LocalOrbitalIdentityAt (Q₀' : QuadForm (𝓞 F) n) (m : 𝓞 F) : Prop where
  typeSum_eq : locTypeSum v (algebraMap (𝓞 F) F m) (Q₀'.map (algebraMap (𝓞 F) F)) *
      NF.siegelDensity v (splitForm m Q₀') (splitForm m Q₀') * absTwoM v m ^ n =
    NF.siegelDensity v Q₀' Q₀' * NF.localDensity v (splitForm m Q₀') m

/-- **The local orbital identity holds at every $\mathfrak p \nmid 2m$**: one local type of weight $1$
(`locTypeSum_eq_one`), $|2m|_\mathfrak p = 1$, and $\alpha_\mathfrak p(L')\beta_\mathfrak p(L,m) = \alpha_\mathfrak p(L)$ (`localIdentity_unit_nf`). -/
@[kb "weil1982" "§3.4 (local fibration, p ∤ 2m) [unverified]"]
theorem localOrbitalIdentityAt_of_not_mem (m : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate)
    (h2m : 2 * m ∉ v.asIdeal) : LocalOrbitalIdentityAt v Q₀' m :=
  ⟨by rw [locTypeSum_eq_one v m Q₀' h2m, absTwoM_eq_one v h2m, one_pow, mul_one, one_mul,
    localIdentity_unit_nf v m Q₀' hQ' h2m]⟩

end PerPrime

end QuadFormsKB.Tamagawa

/-! ## The fibration count at every prime, and the orbit-count form of the local identity -/

namespace QuadFormsKB.Tamagawa

open QuadForm

/-! ### The fibration count at every prime (dyadic included) -/

section General

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The block matrix $\begin{pmatrix}1 & s^{\mathsf T}\\ 0 & Y\end{pmatrix}$: first column $e_0$, first row $(1, s)$. -/
def topMat (s : Fin n → A) (Y : Matrix (Fin n) (Fin n) A) : Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 s j) (fun i' => Fin.cases 0 (fun j' => Y i' j') j) i

@[simp] theorem topMat_zero_zero (s : Fin n → A) (Y : Matrix (Fin n) (Fin n) A) : topMat s Y 0 0 = 1 := rfl
@[simp] theorem topMat_zero_succ (s : Fin n → A) (Y : Matrix (Fin n) (Fin n) A) (j : Fin n) :
    topMat s Y 0 j.succ = s j := rfl
@[simp] theorem topMat_succ_zero (s : Fin n → A) (Y : Matrix (Fin n) (Fin n) A) (i : Fin n) :
    topMat s Y i.succ 0 = 0 := rfl
@[simp] theorem topMat_succ_succ (s : Fin n → A) (Y : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    topMat s Y i.succ j.succ = Y i j := rfl

theorem topMat_mulVec (s : Fin n → A) (Y : Matrix (Fin n) (Fin n) A) (t : A) (x : Fin n → A) :
    topMat s Y *ᵥ (Fin.cons t x : Fin (n + 1) → A) = Fin.cons (t + s ⬝ᵥ x) (Y *ᵥ x) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [mulVec, dotProduct, Fin.sum_univ_succ]

theorem topMat_mulVec_e₀ (s : Fin n → A) (Y : Matrix (Fin n) (Fin n) A) :
    topMat s Y *ᵥ (e₀ : Fin (n + 1) → A) = e₀ := by
  rw [topMat_mulVec, dotProduct_zero, add_zero, mulVec_zero]

/-- **$Q\circ\begin{pmatrix}1 & s^{\mathsf T}\\0 & Y\end{pmatrix} = \langle a\rangle\perp(Q'\circ Y)$** when $2as_j = 0$ and $as_is_j = 0$. -/
theorem compMat_topMat (a : A) (Q' : QuadForm A n) (s : Fin n → A) (Y : Matrix (Fin n) (Fin n) A)
    (h1 : ∀ j, 2 * a * s j = 0) (h2 : ∀ i j, a * s i * s j = 0) :
    (splitForm a Q').compMat (topMat s Y) = splitForm a (Q'.compMat Y) := by
  refine eq_of_eval_eq fun y => ?_
  rw [eval_compMat, ← Fin.cons_self_tail y, topMat_mulVec, eval_splitForm_cons, eval_splitForm_cons,
    eval_compMat]
  set t := y 0
  set x := Fin.tail y
  have e1 : 2 * a * t * (s ⬝ᵥ x) = 0 := by
    rw [dotProduct, Finset.mul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [show 2 * a * t * (s j * x j) = (2 * a * s j) * t * x j by ring, h1 j, zero_mul, zero_mul]
  have e2 : a * (s ⬝ᵥ x) * (s ⬝ᵥ x) = 0 := by
    rw [mul_assoc, dotProduct, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [show a * (s i * x i * (s j * x j)) = (a * s i * s j) * x i * x j by ring, h2 i j, zero_mul, zero_mul]
  linear_combination e1 + e2

/-- **The fibre over $e_0$, every characteristic:** if $Q\circ X = Q$ ($Q = \langle a\rangle\perp Q'$) and $Xe_0 = e_0$, then $X$ is
$\begin{pmatrix}1 & s^{\mathsf T}\\0 & Y\end{pmatrix}$ with $2as_j = 0$. -/
theorem eq_topMat_of_fix {a : A} (Q' : QuadForm A n) {X : Matrix (Fin (n + 1)) (Fin (n + 1)) A}
    (hX : (splitForm a Q').compMat X = splitForm a Q') (h0 : X *ᵥ (e₀ : Fin (n + 1) → A) = e₀) :
    X = topMat (fun j : Fin n => X 0 j.succ) (X.submatrix Fin.succ Fin.succ) ∧
      ∀ j : Fin n, 2 * a * X 0 j.succ = 0 := by
  have hH := congrArg QuadForm.hessian hX
  rw [hessian_compMat, hessian_splitForm] at hH
  have hcol : ∀ i, X i 0 = (e₀ : Fin (n + 1) → A) i := by
    intro i
    have := congrFun h0 i
    rw [e₀_eq_single, mulVec_single_one] at this
    rw [e₀_eq_single]; exact this
  have hrow : ∀ j, 2 * a * X 0 j = 2 * a * (e₀ : Fin (n + 1) → A) j := by
    have h1 : Pi.single 0 1 ᵥ* (Xᵀ * cornerMat (2 * a) Q'.hessian * X) =
        Pi.single 0 1 ᵥ* cornerMat (2 * a) Q'.hessian := by rw [hH]
    rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_transpose, ← e₀_eq_single, h0, e₀_eq_single] at h1
    have h2 : Pi.single (0 : Fin (n + 1)) (1 : A) ᵥ* cornerMat (2 * a) Q'.hessian = (2 * a) • Pi.single 0 1 := by
      rw [single_one_vecMul]
      ext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [Matrix.row]
    rw [h2, smul_vecMul, single_one_vecMul] at h1
    intro j
    have := congrFun h1 j
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.row] at this
    rw [e₀_eq_single]
    exact this
  refine ⟨?_, fun j => by simpa [Fin.succ_ne_zero] using hrow j.succ⟩
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simpa using hcol 0
  · rfl
  · simpa [Fin.succ_ne_zero] using hcol i.succ
  · rfl

/-- **The fibre over $e_0$ as a product**, every characteristic: if $2as = 0$ forces $as_is_j = 0$, then
$\{X : Q\circ X = Q,\ Xe_0 = e_0\} \simeq \{s : 2as_j = 0\ \forall j\}\times\{Y : Q'\circ Y = Q'\}$. -/
def fixEquiv (a : A) (Q' : QuadForm A n)
    (hs : ∀ s : Fin n → A, (∀ j, 2 * a * s j = 0) → ∀ i j, a * s i * s j = 0) :
    {X : Matrix (Fin (n + 1)) (Fin (n + 1)) A //
        (splitForm a Q').compMat X = splitForm a Q' ∧ X *ᵥ (e₀ : Fin (n + 1) → A) = e₀} ≃
      {s : Fin n → A // ∀ j, 2 * a * s j = 0} × {Y : Matrix (Fin n) (Fin n) A // Q'.compMat Y = Q'} where
  toFun X := (⟨fun j : Fin n => X.1 0 j.succ, (eq_topMat_of_fix Q' X.2.1 X.2.2).2⟩,
    ⟨X.1.submatrix Fin.succ Fin.succ, by
      obtain ⟨h1, h2⟩ := eq_topMat_of_fix Q' X.2.1 X.2.2
      have h := X.2.1
      rw [h1, compMat_topMat a Q' _ _ h2 (hs _ h2)] at h
      exact splitForm_injective_right h⟩)
  invFun p := ⟨topMat p.1.1 p.2.1, by rw [compMat_topMat a Q' _ _ p.1.2 (hs _ p.1.2), p.2.2],
    topMat_mulVec_e₀ _ _⟩
  left_inv X := Subtype.ext (eq_topMat_of_fix Q' X.2.1 X.2.2).1.symm
  right_inv p := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> rfl

/-- The orbit of $x_0$ under $\{X : Q\circ X = Q\}$ (the image of $X \mapsto Xx_0$). -/
def orbitSet {N : ℕ} (Q : QuadForm A N) (x₀ : Fin N → A) : Type _ :=
  {x : Fin N → A // ∃ X : Matrix (Fin N) (Fin N) A, Q.compMat X = Q ∧ X *ᵥ x₀ = x}

/-- **Orbit–stabilizer for the isometries of $Q$**: if every $X$ with $Q\circ X = Q$ is invertible, all fibres of
$X \mapsto Xx_0$ over its image have the size of the fibre over $x_0$. -/
theorem card_compMat_eq_orbit_mul {N : ℕ} [Finite A] (Q : QuadForm A N)
    (hinv : ∀ X : Matrix (Fin N) (Fin N) A, Q.compMat X = Q → IsUnit X.det) (x₀ : Fin N → A) :
    Nat.card {X : Matrix (Fin N) (Fin N) A // Q.compMat X = Q} =
      Nat.card (orbitSet Q x₀) * Nat.card {X : Matrix (Fin N) (Fin N) A // Q.compMat X = Q ∧ X *ᵥ x₀ = x₀} := by
  classical
  let fib : orbitSet Q x₀ → Type _ := fun x => {X : Matrix (Fin N) (Fin N) A // Q.compMat X = Q ∧ X *ᵥ x₀ = x.1}
  let e : {X : Matrix (Fin N) (Fin N) A // Q.compMat X = Q} ≃ Σ x : orbitSet Q x₀, fib x :=
    { toFun := fun X => ⟨⟨X.1 *ᵥ x₀, X.1, X.2, rfl⟩, ⟨X.1, X.2, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, p.2.2.1⟩
      left_inv := fun X => rfl
      right_inv := fun p => Sigma.subtype_ext (Subtype.ext p.2.2.2) rfl }
  have hfib : ∀ x : orbitSet Q x₀, Nat.card (fib x) =
      Nat.card {X : Matrix (Fin N) (Fin N) A // Q.compMat X = Q ∧ X *ᵥ x₀ = x₀} := by
    intro x
    obtain ⟨Y, hY, hYx⟩ := x.2
    have hu := hinv Y hY
    have hYi : Q.compMat Y⁻¹ = Q := by
      conv_lhs => rw [← hY]
      rw [compMat_mul, mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det Y).mp
        ((Matrix.isUnit_iff_isUnit_det Y).mpr hu)), compMat_one]
    have hinvx : Y⁻¹ *ᵥ x.1 = x₀ := by
      rw [← hYx, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
    refine Nat.card_congr
      { toFun := fun X => ⟨Y⁻¹ * X.1, by rw [← compMat_mul, hYi, X.2.1], by
          rw [← mulVec_mulVec, X.2.2, hinvx]⟩
        invFun := fun X => ⟨Y * X.1, by rw [← compMat_mul, hY, X.2.1], by
          rw [← mulVec_mulVec, X.2.2, hYx]⟩
        left_inv := fun X => Subtype.ext (by
          show Y * (Y⁻¹ * X.1) = X.1
          rw [← mul_assoc, mul_nonsing_inv _ hu, one_mul])
        right_inv := fun X => Subtype.ext (by
          show Y⁻¹ * (Y * X.1) = X.1
          rw [← mul_assoc, nonsing_inv_mul _ hu, one_mul]) }
  have : Finite (orbitSet Q x₀) := Subtype.finite
  have : ∀ x, Finite (fib x) := fun x => Subtype.finite
  let _ : Fintype (orbitSet Q x₀) := Fintype.ofFinite _
  let _ : ∀ x, Fintype (fib x) := fun x => Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card] at hfib ⊢
  rw [Finset.sum_congr rfl fun x _ => hfib x, Finset.sum_const, Finset.card_univ, smul_eq_mul]

end General

end QuadFormsKB.Tamagawa

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Tamagawa

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-- **The annihilator of $\pi^e$ in $R/\pi^k$** ($e \le k$) is $\pi^{k-e}R/\pi^kR \cong R/\pi^e$: it has $q^e$ elements; the same holds
for any $c$ with $\pi^e \,\|\, c$. -/
theorem card_ann [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π) {e k : ℕ} (hek : e ≤ k)
    {c : R} (hc : π ^ e ∣ c) (hc' : ¬ π ^ (e + 1) ∣ c) :
    Nat.card {t : R ⧸ Ideal.span {π ^ k} // Ideal.Quotient.mk _ c * t = 0} = q R ^ e := by
  obtain ⟨u, rfl, hu⟩ := dvr_exact hπ hc hc'
  have hπ0 := hπ.ne_zero
  have key : ∀ r : R, Ideal.Quotient.mk (Ideal.span {π ^ k}) (π ^ e * u) * Ideal.Quotient.mk _ r = 0 ↔
      π ^ (k - e) ∣ r := by
    intro r
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    constructor
    · intro h
      have h' : π ^ e * π ^ (k - e) ∣ π ^ e * r := by
        rw [← pow_add, show e + (k - e) = k by omega]
        have : π ^ e * r = π ^ e * u * r * w := by
          rw [mul_assoc, mul_assoc, mul_comm r w, ← mul_assoc u, hw, one_mul]
        rw [this]; exact dvd_mul_of_dvd_left h w
      exact (mul_dvd_mul_iff_left (pow_ne_zero _ hπ0)).mp h'
    · rintro ⟨r', rfl⟩
      have hpk : π ^ k = π ^ e * π ^ (k - e) := by rw [← pow_add, show e + (k - e) = k by omega]
      exact ⟨u * r', by rw [hpk]; ring⟩
  let φ : R ⧸ Ideal.span {π ^ e} → {t : R ⧸ Ideal.span {π ^ k} //
      Ideal.Quotient.mk _ (π ^ e * u) * t = 0} :=
    Quotient.lift (fun r : R => ⟨Ideal.Quotient.mk _ (π ^ (k - e) * r), (key _).mpr (dvd_mul_right _ _)⟩)
      (fun a b hab => by
        apply Subtype.ext
        show Ideal.Quotient.mk _ (π ^ (k - e) * a) = Ideal.Quotient.mk _ (π ^ (k - e) * b)
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
        have hab' : a - b ∈ Ideal.span {π ^ e} := by
          have := (Submodule.quotientRel_def _).mp hab
          exact this
        rw [Ideal.mem_span_singleton] at hab'
        obtain ⟨w, hw⟩ := hab'
        exact ⟨w, by rw [← mul_sub, hw, ← mul_assoc, ← pow_add, show k - e + e = k by omega]⟩)
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      induction a using Quotient.inductionOn' with | h a => ?_
      induction b using Quotient.inductionOn' with | h b => ?_
      have h1 : Ideal.Quotient.mk (Ideal.span {π ^ k}) (π ^ (k - e) * a) =
          Ideal.Quotient.mk _ (π ^ (k - e) * b) := congrArg Subtype.val hab
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, ← mul_sub] at h1
      apply Quotient.sound'
      rw [Submodule.quotientRel_def, Ideal.mem_span_singleton]
      have : π ^ (k - e) * π ^ e ∣ π ^ (k - e) * (a - b) := by
        rw [← pow_add, show k - e + e = k by omega]; exact h1
      exact (mul_dvd_mul_iff_left (pow_ne_zero _ hπ0)).mp this
    · rintro ⟨t, ht⟩
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective t
      obtain ⟨r', rfl⟩ := (key r).mp ht
      exact ⟨Ideal.Quotient.mk _ r', rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), card_quot_pow π hπ]

/-- **Products of annihilated elements vanish** at level $k \ge 2e$: if $\pi^e \,\|\, c$ and $cs = ct = 0$ in $R/\pi^k$, then
$a\,s\,t = 0$ for every $a$. -/
theorem mul_mul_eq_zero_of_ann {π : R} (hπ : Irreducible π) {e k : ℕ} (hek : 2 * e ≤ k) {c : R}
    (hc : π ^ e ∣ c) (hc' : ¬ π ^ (e + 1) ∣ c) (a : R ⧸ Ideal.span {π ^ k}) {s t : R ⧸ Ideal.span {π ^ k}}
    (hs : Ideal.Quotient.mk _ c * s = 0) (ht : Ideal.Quotient.mk _ c * t = 0) : a * s * t = 0 := by
  obtain ⟨u, rfl, hu⟩ := dvr_exact hπ hc hc'
  have hπ0 := hπ.ne_zero
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have key : ∀ r : R, Ideal.Quotient.mk (Ideal.span {π ^ k}) (π ^ e * u) * Ideal.Quotient.mk _ r = 0 →
      π ^ (k - e) ∣ r := by
    intro r h
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
    have h' : π ^ e * π ^ (k - e) ∣ π ^ e * r := by
      rw [← pow_add, show e + (k - e) = k by omega]
      have : π ^ e * r = π ^ e * u * r * w := by
        rw [mul_assoc, mul_assoc, mul_comm r w, ← mul_assoc u, hw, one_mul]
      rw [this]; exact dvd_mul_of_dvd_left h w
    exact (mul_dvd_mul_iff_left (pow_ne_zero _ hπ0)).mp h'
  obtain ⟨rs, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨rt, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨ra, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨xs, rfl⟩ := key rs hs
  obtain ⟨xt, rfl⟩ := key rt ht
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨ra * xs * xt * π ^ (2 * (k - e) - k), by
    rw [show ra * (π ^ (k - e) * xs) * (π ^ (k - e) * xt) = ra * xs * xt * (π ^ (k - e) * π ^ (k - e)) by ring,
      ← pow_add, show k - e + (k - e) = k + (2 * (k - e) - k) by omega, pow_add]; ring⟩

/-- **Weil's fibration count at every prime** (dyadic included): for $Q = \langle m\rangle\perp Q'$, $\pi^e \,\|\, 2m$,
$\pi^d \,\|\, \det H_Q$ and $k \ge 2e$, $k > d$,
$$A_{\pi^k}(Q, Q) = |O(Q \bmod \pi^k)\cdot e_0|\cdot q^{en}\cdot A_{\pi^k}(Q', Q').$$
*Proof:* orbit–stabilizer for $O(Q \bmod \pi^k)$ acting on $e_0$ (`card_compMat_eq_orbit_mul`); the stabilizer is
$\{\begin{pmatrix}1 & s^{\mathsf T}\\0 & Y\end{pmatrix} : 2ms = 0,\ Q'\circ Y = Q'\}$ (`fixEquiv`), and $2ms_j = 0$ has $q^e$ solutions
(`card_ann`). The factor $q^{en} = |2m|_\pi^{-n}$ is the Jacobian of Weil's fibration. -/
@[kb "weil1982" "§3.4 (fibration count mod π^k, every prime) [unverified]"]
theorem repCountForm_splitForm_orbit [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π)
    {m : R} {e d k : ℕ} (he : π ^ e ∣ 2 * m) (he' : ¬ π ^ (e + 1) ∣ 2 * m) (Q' : QuadForm R n)
    (hd : π ^ d ∣ (splitForm m Q').hessian.det) (hd' : ¬ π ^ (d + 1) ∣ (splitForm m Q').hessian.det)
    (hk : 2 * e ≤ k) (hdk : d < k) :
    repCountForm (splitForm m Q') (splitForm m Q') π k =
      Nat.card (orbitSet ((splitForm m Q').map (Ideal.Quotient.mk (Ideal.span {π ^ k}))) e₀) * q R ^ (e * n) *
        repCountForm Q' Q' π k := by
  have := finite_quot_pow π hπ k
  set A := R ⧸ Ideal.span {π ^ k}
  have hsplit : (splitForm m Q').map (Ideal.Quotient.mk (Ideal.span {π ^ k})) =
      splitForm (Ideal.Quotient.mk _ m) (Q'.map (Ideal.Quotient.mk _)) := map_splitForm _ _ _
  have h2m : ∀ t : A, 2 * Ideal.Quotient.mk (Ideal.span {π ^ k}) m * t =
      Ideal.Quotient.mk _ (2 * m) * t := fun t => by rw [map_mul, map_ofNat]
  have hs : ∀ s : Fin n → A, (∀ j, 2 * Ideal.Quotient.mk (Ideal.span {π ^ k}) m * s j = 0) →
      ∀ i j, Ideal.Quotient.mk (Ideal.span {π ^ k}) m * s i * s j = 0 := by
    intro s h i j
    exact mul_mul_eq_zero_of_ann hπ hk he he' _ (by rw [← h2m]; exact h i) (by rw [← h2m]; exact h j)
  unfold repCountForm
  rw [card_compMat_eq_orbit_mul _ (fun X hX => isUnit_det_of_compMat_eq _ π hπ d k hd hd' hdk X hX) e₀,
    mul_assoc]
  congr 1
  have hcount : Nat.card {s : Fin n → A // ∀ j, 2 * Ideal.Quotient.mk (Ideal.span {π ^ k}) m * s j = 0} =
      q R ^ (e * n) := by
    rw [Nat.card_congr (Equiv.subtypePiEquivPi (p := fun _ t => 2 * Ideal.Quotient.mk (Ideal.span {π ^ k}) m * t = 0)),
      Nat.card_pi]
    simp_rw [h2m]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, card_ann hπ (by omega) he he', ← pow_mul]
  rw [hsplit, Nat.card_congr (fixEquiv _ _ hs), Nat.card_prod, hcount]

end QuadFormsKB.LocalDensity.DVR

namespace QuadFormsKB.Tamagawa

open NumberField IsDedekindDomain LocalDensity

section OrbitCount

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

/-- **The Jacobian as a power of $N\mathfrak p$:** with $e = \mathrm{ord}_\mathfrak p(2m)$, $\varpi^e \,\|\, 2m$ in $\mathfrak o_\mathfrak p$ and
$|2m|_\mathfrak p\cdot N\mathfrak p^{\,e} = 1$. -/
theorem exists_ord_absTwoM {m : 𝓞 F} (hm : m ≠ 0) :
    ∃ e : ℕ, NF.π v ^ e ∣ NF.ι v (2 * m) ∧ ¬ NF.π v ^ (e + 1) ∣ NF.ι v (2 * m) ∧
      absTwoM v m * (Ideal.absNorm v.asIdeal : ℝ) ^ e = 1 := by
  have hx : (2 * m : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero hm
  set c := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(2 * m : 𝓞 F)})).factors
  have hv := v.intValuation_if_neg hx
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [NF.π_pow_dvd_ι_iff]
    exact (v.intValuation_le_pow_iff_mem _ _).1 (by rw [hv])
  · rw [NF.π_pow_dvd_ι_iff]
    intro h
    have := (v.intValuation_le_pow_iff_mem _ _).2 h
    rw [hv, WithZero.exp_le_exp] at this
    push_cast at this; omega
  · have h := HeightOneSpectrum.embedding_mul_absNorm (K := F) v hx
    rw [HeightOneSpectrum.maxPowDividing, map_pow, Nat.cast_pow] at h
    exact h

/-- **The size of the orbit of $e_0$** under $O(Q\bmod\varpi^k)$ in $(\mathfrak o_\mathfrak p/\varpi^k)^{n+1}$, $Q = \langle m\rangle\perp Q_0'$. -/
def orbitCountE₀ (m : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) (k : ℕ) : ℕ :=
  Nat.card (orbitSet ((NF.Qp v (splitForm m Q₀')).map (Ideal.Quotient.mk (Ideal.span {NF.π v ^ k}))) e₀)

/-- **Input (at one prime): the local type sum counts orbits mod $\varpi^k$** (Weil's orbit-measure identity, in finite
form; Weil 1982, §3.4 [unverified]):
$$W_\mathfrak p\cdot\big|O(Q\bmod\varpi^k)\,e_0\big| = \#\{x \in (\mathfrak o_\mathfrak p/\varpi^k)^{n+1} : Q(x) \equiv m\}\qquad(k \gg 0).$$

Field:
- `eventually_eq`: the displayed identity for all large $k$.

*Meaning.* Both sides are "$\sum$ over local types of the orbit sizes": the type $t$ with representative $M_t = g^{-1}L$ ($ge_0 = x_t$)
contributes the solutions mod $\varpi^k$ near the $O(L_\mathfrak p)$-orbit of $x_t$, and $w_\mathfrak p(t) = \mu(K_0')/\mu(K_t)$ is the ratio of
its size to that of the orbit of $e_0$. It contains **no densities and no Jacobian**: by `localOrbitalIdentityAt_of_orbitCount`
it implies the local orbital identity, the factor $|2m|_\mathfrak p^{-n}$ and the three densities being accounted for by counting
(`repCountForm_splitForm_orbit`). It holds at every $\mathfrak p \nmid 2m$ (`localTypeOrbitCount_of_not_mem`: one type, and
$O(Q\bmod\varpi^k)$ is transitive on the solutions). -/
@[kb "weil1982" "§3.4 (orbits of the local fibration) [unverified]"]
structure LocalTypeOrbitCount (Q₀' : QuadForm (𝓞 F) n) (m : 𝓞 F) : Prop where
  eventually_eq : ∀ᶠ k in Filter.atTop,
    locTypeSum v (algebraMap (𝓞 F) F m) (Q₀'.map (algebraMap (𝓞 F) F)) * (orbitCountE₀ v m Q₀' k : ℝ) =
      (DVR.repCount (NF.Qp v (splitForm m Q₀')) (NF.π v) k (NF.ι v m) : ℝ)

/-- **The orbit count gives the local orbital identity at every prime**, dyadic included: the densities and the
Jacobian $|2m|_\mathfrak p^{-n}$ in `LocalOrbitalIdentityAt` are exactly accounted for by the fibration count
$A_{\varpi^k}(L, L) = |O(Q\bmod\varpi^k)e_0|\cdot N\mathfrak p^{en}\cdot A_{\varpi^k}(L', L')$ (`DVR.repCountForm_splitForm_orbit`). -/
@[kb "weil1982" "§3.4 (local fibration, every prime) [unverified]"]
theorem localOrbitalIdentityAt_of_orbitCount (m : 𝓞 F) (hm : m ≠ 0) (Q₀' : QuadForm (𝓞 F) n)
    (hQ' : Q₀'.Nondegenerate) (h : LocalTypeOrbitCount v Q₀' m) : LocalOrbitalIdentityAt v Q₀' m := by
  obtain ⟨e, he, he', hJ⟩ := exists_ord_absTwoM v hm
  have h20 : (2 : 𝓞 F) ≠ 0 := two_ne_zero
  have hQ : (splitForm m Q₀').Nondegenerate := by
    rw [QuadForm.Nondegenerate, det_hessian_splitForm]
    exact mul_ne_zero (mul_ne_zero h20 hm) hQ'
  have hsplit : NF.Qp v (splitForm m Q₀') = splitForm (NF.ι v m) (NF.Qp v Q₀') := map_splitForm _ _ _
  have hQp := NF.nondegenerate_Qp v hQ
  have hQp' := NF.nondegenerate_Qp v hQ'
  have hπ := NF.irreducible_π v
  obtain ⟨d, hd, hd'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ hQp
  have he2 : NF.π v ^ e ∣ 2 * NF.ι v m := by rw [← map_ofNat (NF.ι v), ← map_mul]; exact he
  have he2' : ¬ NF.π v ^ (e + 1) ∣ 2 * NF.ι v m := by rw [← map_ofNat (NF.ι v), ← map_mul]; exact he'
  have e1 := DVR.localDensityForm_eventually_eq (NF.Qp v Q₀') (NF.Qp v Q₀') hQp' (NF.π v) hπ le_rfl
  have e2 := DVR.localDensityForm_eventually_eq (NF.Qp v (splitForm m Q₀')) (NF.Qp v (splitForm m Q₀')) hQp
    (NF.π v) hπ le_rfl
  have e3 := DVR.localDensity_eventually_eq (NF.Qp v (splitForm m Q₀')) hQp (NF.π v) hπ (NF.ι v m)
    (NF.ι_ne_zero v hm) (NF.two_ne_zero' v)
  obtain ⟨k, hk⟩ := (e1.and (e2.and (e3.and (h.eventually_eq.and
    (Filter.eventually_ge_atTop (2 * e + d + 1)))))).exists
  obtain ⟨h1, h2, h3, h4, hk0⟩ := hk
  refine ⟨?_⟩
  unfold NF.siegelDensity
  simp only [↓reduceIte]
  rw [NF.localDensityForm_eq_completion, NF.localDensityForm_eq_completion, NF.localDensity_eq_completion,
    ← h1, ← h2, ← h3]
  have hcount := DVR.repCountForm_splitForm_orbit (d := d) (k := k) hπ he2 he2' (NF.Qp v Q₀')
    (by rw [← hsplit]; exact hd)
    (by rw [← hsplit]; exact hd') (by omega) (by omega)
  rw [← hsplit] at hcount
  rw [hcount]
  have hq : (DVR.q (v.adicCompletionIntegers F) : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by
    rw [NF.q_completion]
  set W := locTypeSum v (algebraMap (𝓞 F) F m) (Q₀'.map (algebraMap (𝓞 F) F))
  set O := (orbitCountE₀ v m Q₀' k : ℝ)
  have h4' : W * O = (DVR.repCount (NF.Qp v (splitForm m Q₀')) (NF.π v) k (NF.ι v m) : ℝ) := h4
  have hO : (Nat.card (orbitSet ((NF.Qp v (splitForm m Q₀')).map (Ideal.Quotient.mk (Ideal.span {NF.π v ^ k})))
      e₀) : ℝ) = O := rfl
  have hexp : (n + 1) * (n + 1) - (n + 1) * (n + 1 + 1) / 2 = (n * n - n * (n + 1) / 2) + (n + 1 - 1) := by
    rw [DVR.self_exp, DVR.self_exp, Tamagawa.nat_tri_succ]; omega
  rw [hexp, Nat.mul_add k, pow_add]
  push_cast
  rw [hO, ← h4', hq]
  have hN : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
    rw [← hq]; exact_mod_cast (DVR.q_pos (R := v.adicCompletionIntegers F)).ne'
  have hJ' : absTwoM v m = ((Ideal.absNorm v.asIdeal : ℝ) ^ e)⁻¹ := eq_inv_of_mul_eq_one_left hJ
  rw [hJ', one_div, inv_pow, ← pow_mul, mul_comm e n]
  field_simp

/-- **The orbit count holds at every $\mathfrak p \nmid 2m$**: one local type ($W_\mathfrak p = 1$) and $O(Q\bmod\varpi^k)$ is transitive on
$\{Q(x) \equiv m\}$ (the reflections of `exists_refl_e₀`). -/
theorem localTypeOrbitCount_of_not_mem (m : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) (h2m : 2 * m ∉ v.asIdeal) :
    LocalTypeOrbitCount v Q₀' m := by
  refine ⟨?_⟩
  filter_upwards [Filter.eventually_gt_atTop 0] with k hk
  rw [locTypeSum_eq_one v m Q₀' h2m, one_mul]
  have := DVR.isLocalRing_quot (NF.irreducible_π v) hk
  have hu : IsUnit (2 * NF.ι v m) := by
    have := isUnit_ι_of_not_mem v h2m
    rwa [map_mul, map_ofNat] at this
  have hu' : IsUnit (4 * Ideal.Quotient.mk (Ideal.span {NF.π v ^ k}) (NF.ι v m)) := by
    have h2a := (hu.map (Ideal.Quotient.mk (Ideal.span {NF.π v ^ k})))
    rw [map_mul, map_ofNat] at h2a
    rw [show (4 : v.adicCompletionIntegers F ⧸ Ideal.span {NF.π v ^ k}) *
        Ideal.Quotient.mk (Ideal.span {NF.π v ^ k}) (NF.ι v m) =
        2 * (2 * Ideal.Quotient.mk (Ideal.span {NF.π v ^ k}) (NF.ι v m)) by ring]
    exact (isUnit_of_mul_isUnit_left h2a).mul h2a
  have hsplit : (NF.Qp v (splitForm m Q₀')).map (Ideal.Quotient.mk (Ideal.span {NF.π v ^ k})) =
      splitForm (Ideal.Quotient.mk _ (NF.ι v m)) ((NF.Qp v Q₀').map (Ideal.Quotient.mk _)) := by
    rw [show NF.Qp v (splitForm m Q₀') = splitForm (NF.ι v m) (NF.Qp v Q₀') from map_splitForm _ _ _,
      map_splitForm]
  unfold orbitCountE₀ DVR.repCount
  congr 1
  rw [hsplit]
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1, ?_⟩
      invFun := fun x => ⟨x.1, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  · obtain ⟨X, hX, hXx⟩ := x.2
    rw [DVR.evalIn_eq_eval_map' (Ideal.Quotient.mk _) _ _ (Ideal.Quotient.algebraMap_eq _), ← hXx,
      ← QuadForm.eval_compMat, hsplit, hX, eval_splitForm_e₀']
  · have hx := x.2
    rw [DVR.evalIn_eq_eval_map' (Ideal.Quotient.mk _) _ _ (Ideal.Quotient.algebraMap_eq _), hsplit] at hx
    obtain ⟨σ, hσ, -, hσe⟩ := exists_refl_e₀ hu' _ hx
    exact ⟨σ, hσ, hσe⟩

end OrbitCount

end QuadFormsKB.Tamagawa
