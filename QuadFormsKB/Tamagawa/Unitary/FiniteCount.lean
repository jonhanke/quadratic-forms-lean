import Mathlib
import QuadFormsKB.Citation

/-!
# Orders of finite unitary groups

Setting: `K` a finite field, `a : K`, and `L := QuadraticAlgebra K a 0`, the algebra
$K[\omega]/(\omega^2 - a)$ with elements $z = z_{\mathrm{re}} + z_{\mathrm{im}} \omega$.  Since $b = 0$
the conjugation is $\overline{z} = z_{\mathrm{re}} - z_{\mathrm{im}} \omega$.  For a hermitian
$H \in M_m(L)$ with $\det H \neq 0$ the unitary group of $H$ is
$\{X \in M_m(L) : X^* H X = H\}$ where $X^* = \overline{X}^{\mathsf T}$ (`Matrix.conjTranspose`).

* `card_unitary_split` (split case, $a$ a nonzero square, $\operatorname{char} K \ne 2$):
  $|U(H)| = |\mathrm{GL}_m(K)|$ (so $\prod_{i<m} (q^m - q^i)$ by `Matrix.card_GL_field`).
* `card_unitary_inert` (inert case, $a$ a non-square, $\operatorname{char} K \ne 2$):
  $|U(H)| = q^{m(m-1)/2} \prod_{i=0}^{m-1} (q^{i+1} - (-1)^{i+1})$, $q = |K|$.

Both theorems are unconditional (no extra hypotheses beyond those displayed).  They are
intended to be tagged `@[kb]` in the main project (the `@[kb]` attribute is not available with a
plain Mathlib import, so it is only recorded here as a note).

Proof of the inert case.  (1) The norm $N : L \to K$ is surjective (`FiniteField.norm_surjective`),
so it has $q+1$ preimages of each nonzero value and $1$ of $0$ (`sum_norm_eq`); this gives the
recursion $V_{m+1}(c) = (q+1)q^{2m} - q V_m(c)$ for the number $V_m(c)$ of $x \in L^m$ with
$\sum N(x_i) = c$ (`V_option_rec`), hence $V_{m+1}(1) = q^m(q^{m+1} - (-1)^{m+1})$
(`V_fin_succ`).  (2) Every nondegenerate hermitian matrix is $P^* P$ (`gram_fin`, by induction on
$m$ using a vector with $x^* H x = 1$ and a Schur complement, `core`).  (3) Hence $U(H) \simeq U_m =
\{Y : Y^* Y = 1\}$ (`card_congr_of_gram`), and $|U_{m+1}| = V_{m+1}(1) |U_m|$ by orbit-stabilizer
(`ucard_option`, transitivity in `transitive`).
-/

set_option linter.unusedSectionVars false

open Matrix QuadraticAlgebra

namespace QuadFormsKB.Tamagawa.Unitary.FiniteCount

section Split

variable {K : Type*} [Field K] {a : K}

/-- For $t \in K$ with $t^2 = a$, the ring homomorphism $L \to K$,
$z \mapsto z_{\mathrm{re}} + t\, z_{\mathrm{im}}$ (evaluation at $\omega \mapsto t$). -/
def phi (t : K) (ht : a = t * t) : QuadraticAlgebra K a 0 →+* K where
  toFun z := z.re + t * z.im
  map_one' := by simp
  map_mul' x y := by
    subst ht
    simp only [re_mul, im_mul]
    ring
  map_zero' := by simp
  map_add' x y := by
    simp only [re_add, im_add]
    ring

theorem phi_apply (t : K) (ht : a = t * t) (z : QuadraticAlgebra K a 0) :
    phi t ht z = z.re + t * z.im := rfl

theorem phi_star (t : K) (ht : a = t * t) (ht' : a = (-t) * (-t)) (z : QuadraticAlgebra K a 0) :
    phi t ht (star z) = phi (-t) ht' z := by
  simp only [phi_apply, re_star, im_star]
  ring

/-- The pair of homomorphisms `(phi s, phi (-s))` is injective when $\operatorname{char} K \ne 2$
and $s \neq 0$. -/
theorem phi_pair_injective (hK : ringChar K ≠ 2) {s : K} (hs0 : s ≠ 0) (hs : a = s * s)
    (hs' : a = (-s) * (-s)) {z w : QuadraticAlgebra K a 0}
    (h1 : phi s hs z = phi s hs w) (h2 : phi (-s) hs' z = phi (-s) hs' w) : z = w := by
  simp only [phi_apply] at h1 h2
  have h2' : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have e1 : z.re = w.re := by
    have : (2 : K) * (z.re - w.re) = 0 := by linear_combination h1 + h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2')
  have e2 : z.im = w.im := by
    have : ((2 : K) * s) * (z.im - w.im) = 0 := by linear_combination h1 - h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (mul_ne_zero h2' hs0))
  exact QuadraticAlgebra.ext e1 e2

/-- A section of `(phi s, phi (-s))`. -/
def psi (s : K) (u v : K) : QuadraticAlgebra K a 0 := ⟨(u + v) / 2, (u - v) / (2 * s)⟩

theorem phi_psi_p (hK : ringChar K ≠ 2) {s : K} (hs0 : s ≠ 0) (hs : a = s * s) (u v : K) :
    phi s hs (psi s u v) = u := by
  have h2' : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  simp only [phi_apply, psi]
  field_simp
  ring

theorem phi_psi_m (hK : ringChar K ≠ 2) {s : K} (hs0 : s ≠ 0) (hs' : a = (-s) * (-s))
    (u v : K) : phi (-s) hs' (psi s u v) = v := by
  have h2' : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  simp only [phi_apply, psi]
  field_simp
  ring

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If $Z A Y = A$ with $\det A \ne 0$, $\det Y \ne 0$ then $Z = A Y^{-1} A^{-1}$. -/
theorem solve_left {A Y Z : Matrix n n K} (hA : A.det ≠ 0) (hY : Y.det ≠ 0)
    (h : Z * A * Y = A) : Z = A * Y⁻¹ * A⁻¹ := by
  have hA' : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hY' : IsUnit Y.det := isUnit_iff_ne_zero.mpr hY
  have h1 : Z * A = A * Y⁻¹ := by
    calc Z * A = Z * A * (Y * Y⁻¹) := by rw [Matrix.mul_nonsing_inv _ hY', Matrix.mul_one]
      _ = (Z * A * Y) * Y⁻¹ := by rw [Matrix.mul_assoc _ Y]
      _ = A * Y⁻¹ := by rw [h]
  calc Z = Z * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv _ hA', Matrix.mul_one]
    _ = (Z * A) * A⁻¹ := by rw [Matrix.mul_assoc]
    _ = A * Y⁻¹ * A⁻¹ := by rw [h1]

theorem solve_left_conv {A Y : Matrix n n K} (hA : A.det ≠ 0) (hY : Y.det ≠ 0) :
    (A * Y⁻¹ * A⁻¹) * A * Y = A := by
  have hA' : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hY' : IsUnit Y.det := isUnit_iff_ne_zero.mpr hY
  calc (A * Y⁻¹ * A⁻¹) * A * Y = A * Y⁻¹ * (A⁻¹ * A) * Y := by simp only [Matrix.mul_assoc]
    _ = A * (Y⁻¹ * Y) := by rw [Matrix.nonsing_inv_mul _ hA', Matrix.mul_one, Matrix.mul_assoc]
    _ = A := by rw [Matrix.nonsing_inv_mul _ hY', Matrix.mul_one]

/-- **Split case.** Let $K$ be a finite field of characteristic $\ne 2$, $a \in K$ a nonzero square
(so $L = K[\omega]/(\omega^2 - a) \cong K \times K$ and conjugation swaps the two factors), and
let $H \in M_m(L)$ be hermitian (`hH`) with $\det H \ne 0$ (`hdet`).  Then the unitary group
$\{X \in M_m(L) : X^* H X = H\}$ has the same cardinality as $\mathrm{GL}_m(K)$, namely
$\prod_{i<m}(q^m - q^i)$ with $q = |K|$ (by `Matrix.card_GL_field`).

Hypotheses: `ha` ($a$ is a square), `ha0` ($a \ne 0$), `hK` ($\operatorname{char} K \ne 2$),
`hH` ($H^* = H$), `hdet` ($\det H \ne 0$).  Indices are 0-based (`Fin m`). -/
@[kb "ganhankeyu2001" "(2.11), p. 104 (#H̄_v(A_v/π_v) for H_v = GL_m, v split) [running text]"]
theorem card_unitary_split {m : ℕ} (ha : IsSquare a) (ha0 : a ≠ 0) (hK : ringChar K ≠ 2)
    (H : Matrix (Fin m) (Fin m) (QuadraticAlgebra K a 0)) (hH : H.IsHermitian)
    (hdet : H.det ≠ 0) :
    Nat.card {X : Matrix (Fin m) (Fin m) (QuadraticAlgebra K a 0) // Xᴴ * H * X = H} =
      Nat.card (Matrix.GeneralLinearGroup (Fin m) K) := by
  obtain ⟨s, hs⟩ := ha
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact ha0 (by simpa using hs)
  have hs' : a = (-s) * (-s) := by rw [hs]; ring
  obtain ⟨φp, hφp⟩ : ∃ f : QuadraticAlgebra K a 0 →+* K, f = phi s hs := ⟨_, rfl⟩
  obtain ⟨φm, hφm⟩ : ∃ f : QuadraticAlgebra K a 0 →+* K, f = phi (-s) hs' := ⟨_, rfl⟩
  have hpair : ∀ {z w : QuadraticAlgebra K a 0}, φp z = φp w → φm z = φm w → z = w := by
    intro z w h1 h2
    subst hφp hφm
    exact phi_pair_injective hK hs0 hs hs' h1 h2
  have hpairM : ∀ {A B : Matrix (Fin m) (Fin m) (QuadraticAlgebra K a 0)},
      A.map φp = B.map φp → A.map φm = B.map φm → A = B := by
    intro A B h1 h2
    exact Matrix.ext fun i j =>
      hpair (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)
  have hstarp : ∀ z : QuadraticAlgebra K a 0, φp (star z) = φm z := by
    intro z; subst hφp hφm; exact phi_star s hs hs' z
  have hstarm : ∀ z : QuadraticAlgebra K a 0, φm (star z) = φp z := by
    intro z
    subst hφp hφm
    simp only [phi_apply, re_star, im_star]
    ring
  have hconjp : ∀ X : Matrix (Fin m) (Fin m) (QuadraticAlgebra K a 0),
      (Xᴴ).map φp = (X.map φm)ᵀ := by
    intro X; ext i j
    simp [conjTranspose_apply, hstarp]
  have hconjm : ∀ X : Matrix (Fin m) (Fin m) (QuadraticAlgebra K a 0),
      (Xᴴ).map φm = (X.map φp)ᵀ := by
    intro X; ext i j
    simp [conjTranspose_apply, hstarm]
  have hHmp : H.map φm = (H.map φp)ᵀ := by
    have := hconjp H
    rw [hH.eq] at this
    rw [this, transpose_transpose]
  have hdetp : (H.map φp).det ≠ 0 := by
    intro h0
    apply hdet
    have e1 : φp H.det = (H.map φp).det := RingHom.map_det _ _
    have e2 : φm H.det = (H.map φm).det := RingHom.map_det _ _
    apply hpair
    · rw [e1, h0, map_zero]
    · rw [e2, hHmp, det_transpose, h0, map_zero]
  have hcond : ∀ X : {X : Matrix (Fin m) (Fin m) (QuadraticAlgebra K a 0) // Xᴴ * H * X = H},
      (X.1.map φm)ᵀ * H.map φp * X.1.map φp = H.map φp := by
    intro X
    have := congrArg (fun Z => Z.map φp) X.2
    simpa only [Matrix.map_mul, hconjp] using this
  have hdetX : ∀ X : {X : Matrix (Fin m) (Fin m) (QuadraticAlgebra K a 0) // Xᴴ * H * X = H},
      (X.1.map φp).det ≠ 0 := by
    intro X h0
    have := congrArg Matrix.det (hcond X)
    rw [det_mul, det_mul, h0, mul_zero] at this
    exact hdetp this.symm
  let f : {X : Matrix (Fin m) (Fin m) (QuadraticAlgebra K a 0) // Xᴴ * H * X = H} →
      Matrix.GeneralLinearGroup (Fin m) K :=
    fun X => Matrix.GeneralLinearGroup.mkOfDetNeZero (X.1.map φp) (hdetX X)
  apply Nat.card_eq_of_bijective f
  constructor
  · intro X Y hXY
    have hp : X.1.map φp = Y.1.map φp := by
      have := congrArg (fun g : Matrix.GeneralLinearGroup (Fin m) K =>
        (g : Matrix (Fin m) (Fin m) K)) hXY
      simpa [f] using this
    have hz := solve_left hdetp (hdetX X) (hcond X)
    have hz' := solve_left hdetp (hdetX Y) (hcond Y)
    have hm : X.1.map φm = Y.1.map φm := by
      have : (X.1.map φm)ᵀ = (Y.1.map φm)ᵀ := by rw [hz, hz', hp]
      simpa using this
    exact Subtype.ext (hpairM hp hm)
  · intro g
    have hYdet : (g : Matrix (Fin m) (Fin m) K).det ≠ 0 :=
      isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit)
    let Yp : Matrix (Fin m) (Fin m) K := (g : Matrix (Fin m) (Fin m) K)
    let Ym : Matrix (Fin m) (Fin m) K := (H.map φp * Yp⁻¹ * (H.map φp)⁻¹)ᵀ
    let X : Matrix (Fin m) (Fin m) (QuadraticAlgebra K a 0) :=
      Matrix.of fun i j => psi s (Yp i j) (Ym i j)
    have hXp : X.map φp = Yp := by
      ext i j
      subst hφp
      simp [X, phi_psi_p hK hs0 hs]
    have hXm : X.map φm = Ym := by
      ext i j
      subst hφm
      simp [X, phi_psi_m hK hs0 hs']
    have hc1 : (X.map φm)ᵀ * H.map φp * X.map φp = H.map φp := by
      rw [hXp, hXm, transpose_transpose]
      exact solve_left_conv hdetp hYdet
    have hc2 : (X.map φp)ᵀ * H.map φm * X.map φm = H.map φm := by
      rw [hHmp]
      have := congrArg transpose hc1
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc] at this ⊢
      exact this
    have hXu : Xᴴ * H * X = H := by
      apply hpairM
      · rw [Matrix.map_mul, Matrix.map_mul, hconjp]
        exact hc1
      · rw [Matrix.map_mul, Matrix.map_mul, hconjm]
        exact hc2
    refine ⟨⟨X, hXu⟩, ?_⟩
    apply Units.ext
    simpa [f] using hXp

end Split

section Inert

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {a : K}

/-- The finite type `QuadraticAlgebra K a 0` (it is in bijection with `K × K`). -/
instance instFintypeQA : Fintype (QuadraticAlgebra K a 0) :=
  Fintype.ofEquiv (K × K) (equivProd a 0).symm

theorem card_QA : Fintype.card (QuadraticAlgebra K a 0) = Fintype.card K * Fintype.card K := by
  rw [Fintype.card_congr (equivProd a 0), Fintype.card_prod]

variable [Fact (¬ IsSquare a)]

/-- In the inert case the norm $L \to K$ is surjective. -/
theorem exists_norm_eq (c : K) : ∃ z : QuadraticAlgebra K a 0, QuadraticAlgebra.norm z = c := by
  obtain ⟨z, hz⟩ := FiniteField.norm_surjective K (QuadraticAlgebra K a 0) c
  refine ⟨z, ?_⟩
  rw [← hz, Algebra.norm_apply, ← det_toLinearMap_eq_norm]
  rfl

theorem card_norm_fiber_zero :
    (Finset.univ.filter fun z : QuadraticAlgebra K a 0 => QuadraticAlgebra.norm z = 0).card
      = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext z
  simp [norm_eq_zero_iff_eq_zero]

theorem card_norm_fiber_eq (t : K) (ht : t ≠ 0) :
    (Finset.univ.filter fun z : QuadraticAlgebra K a 0 => QuadraticAlgebra.norm z = 1).card
      = (Finset.univ.filter fun z : QuadraticAlgebra K a 0 => QuadraticAlgebra.norm z = t).card := by
  obtain ⟨z₀, hz₀⟩ := exists_norm_eq (a := a) t
  have hz0 : z₀ ≠ 0 := by
    rintro rfl
    simp at hz₀
    exact ht hz₀.symm
  have hinv : QuadraticAlgebra.norm z₀⁻¹ * t = 1 := by
    rw [← hz₀, ← map_mul, inv_mul_cancel₀ hz0, map_one]
  apply Finset.card_nbij' (fun z => z * z₀) (fun w => w * z₀⁻¹)
  · intro z hz
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hz ⊢
    rw [map_mul, hz, hz₀, one_mul]
  · intro w hw
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢
    rw [map_mul, hw, mul_comm]
    exact hinv
  · intro z _
    exact mul_inv_cancel_right₀ hz0 z
  · intro w _
    exact inv_mul_cancel_right₀ hz0 w

theorem card_norm_fiber (t : K) (ht : t ≠ 0) :
    (Finset.univ.filter fun z : QuadraticAlgebra K a 0 => QuadraticAlgebra.norm z = t).card
      = Fintype.card K + 1 := by
  rw [← card_norm_fiber_eq t ht]
  set c₁ := (Finset.univ.filter fun z : QuadraticAlgebra K a 0 => QuadraticAlgebra.norm z = 1).card
    with hc₁
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (QuadraticAlgebra K a 0))) (t := (Finset.univ : Finset K))
    (f := fun z => QuadraticAlgebra.norm z) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, card_QA, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K)),
    card_norm_fiber_zero,
    Finset.sum_congr rfl
      (fun t' ht' => (card_norm_fiber_eq (a := a) t' (Finset.mem_erase.mp ht').1).symm),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    smul_eq_mul] at hsum
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have h1 : (Fintype.card K - 1) * c₁ = (Fintype.card K - 1) * (Fintype.card K + 1) := by
    zify [show 1 ≤ Fintype.card K by omega] at hsum ⊢
    nlinarith
  exact Nat.eq_of_mul_eq_mul_left (by omega) h1

/-- Summing a function of the norm over `L`. -/
theorem sum_norm_eq (g : K → ℤ) :
    ∑ z : QuadraticAlgebra K a 0, g (QuadraticAlgebra.norm z) =
      ((Fintype.card K : ℤ) + 1) * ∑ t, g t - Fintype.card K * g 0 := by
  have h1 : ∑ z : QuadraticAlgebra K a 0, g (QuadraticAlgebra.norm z) =
      ∑ t : K, ((Finset.univ.filter fun z : QuadraticAlgebra K a 0 =>
        QuadraticAlgebra.norm z = t).card : ℤ) * g t := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun z : QuadraticAlgebra K a 0 =>
      QuadraticAlgebra.norm z) (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_congr rfl (fun z hz => by rw [(Finset.mem_filter.mp hz).2] :
      ∀ z ∈ Finset.univ.filter (fun z : QuadraticAlgebra K a 0 => QuadraticAlgebra.norm z = t),
        g (QuadraticAlgebra.norm z) = g t)]
    simp
  have h2 : ∀ t : K, ((Finset.univ.filter fun z : QuadraticAlgebra K a 0 =>
        QuadraticAlgebra.norm z = t).card : ℤ) =
      ((Fintype.card K : ℤ) + 1) - (if t = 0 then (Fintype.card K : ℤ) else 0) := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp [card_norm_fiber_zero]
    · simp [ht, card_norm_fiber t ht]
  rw [h1]
  simp_rw [h2, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [ite_mul]

/-- Number of vectors $x \in L^\iota$ with $\sum_i N(x_i) = c$ ($N$ the norm $L \to K$). -/
def V (a : K) (ι : Type*) [Fintype ι] [DecidableEq ι] (c : K) : ℕ :=
  (Finset.univ.filter fun x : ι → QuadraticAlgebra K a 0 =>
    ∑ i, QuadraticAlgebra.norm (x i) = c).card

theorem V_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (c : K) : V a ι c = V a κ c := by
  unfold V
  apply Finset.card_nbij' (fun x => x ∘ e.symm) (fun y => y ∘ e)
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    rw [← hx]
    exact Equiv.sum_comp e.symm (fun i => QuadraticAlgebra.norm (x i))
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    rw [← hy]
    exact Equiv.sum_comp e (fun i => QuadraticAlgebra.norm (y i))
  · intro x _
    funext i
    simp
  · intro y _
    funext i
    simp

theorem V_empty {c : K} (hc : c ≠ 0) : V a (Fin 0) c = 0 := by
  unfold V
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _
  simpa using hc.symm

theorem V_option {ι : Type*} [Fintype ι] [DecidableEq ι] (c : K) :
    V a (Option ι) c = ∑ z : QuadraticAlgebra K a 0, V a ι (c - QuadraticAlgebra.norm z) := by
  unfold V
  rw [Finset.card_filter]
  have := Equiv.sum_comp
    (Equiv.piOptionEquivProd (β := fun _ : Option ι => QuadraticAlgebra K a 0)).symm
    (fun x : Option ι → QuadraticAlgebra K a 0 =>
      if ∑ i, QuadraticAlgebra.norm (x i) = c then 1 else 0)
  rw [← this, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Equiv.piOptionEquivProd_symm_apply, Fintype.sum_option]
  refine if_congr ?_ rfl rfl
  change (QuadraticAlgebra.norm z + ∑ i, QuadraticAlgebra.norm (y i) = c) ↔ _
  constructor <;> intro h <;> linear_combination h

theorem sum_V (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ∑ t : K, V a ι t = (Fintype.card K * Fintype.card K) ^ Fintype.card ι := by
  unfold V
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (ι → QuadraticAlgebra K a 0))) (t := (Finset.univ : Finset K))
    (f := fun x => ∑ i, QuadraticAlgebra.norm (x i)) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fun, card_QA] at h
  exact h.symm

theorem V_option_rec (ι : Type*) [Fintype ι] [DecidableEq ι] (c : K) :
    (V a (Option ι) c : ℤ) = ((Fintype.card K : ℤ) + 1) *
      ((Fintype.card K : ℤ) * Fintype.card K) ^ Fintype.card ι -
      Fintype.card K * (V a ι c : ℤ) := by
  rw [V_option]
  push_cast
  rw [sum_norm_eq (fun t => (V a ι (c - t) : ℤ))]
  have h : ∑ t : K, (V a ι (c - t) : ℤ) =
      ((Fintype.card K : ℤ) * Fintype.card K) ^ Fintype.card ι := by
    rw [Fintype.sum_equiv (Equiv.subLeft c) (fun t => (V a ι (c - t) : ℤ))
      (fun t => (V a ι t : ℤ)) (fun _ => rfl)]
    exact_mod_cast sum_V (a := a) ι
  simp [h]

/-- Closed form (multiplied by $q$): $q \cdot \#\{x \in L^m : \sum N(x_i) = c\}
= q^m (q^m - (-1)^m)$ for $c \ne 0$. -/
theorem V_fin_mul {c : K} (hc : c ≠ 0) (m : ℕ) :
    (Fintype.card K : ℤ) * (V a (Fin m) c : ℤ) =
      (Fintype.card K : ℤ) ^ m * ((Fintype.card K : ℤ) ^ m - (-1) ^ m) := by
  induction m with
  | zero => simp [V_empty hc]
  | succ m ih =>
    rw [V_equiv (finSuccEquiv m) c, V_option_rec, Fintype.card_fin]
    linear_combination (-(Fintype.card K : ℤ)) * ih

/-- $\#\{x \in L^{m+1} : \sum N(x_i) = c\} = q^m (q^{m+1} - (-1)^{m+1})$ for $c \ne 0$. -/
theorem V_fin_succ {c : K} (hc : c ≠ 0) (m : ℕ) :
    (V a (Fin (m + 1)) c : ℤ) =
      (Fintype.card K : ℤ) ^ m * ((Fintype.card K : ℤ) ^ (m + 1) - (-1) ^ (m + 1)) := by
  have hq : (Fintype.card K : ℤ) ≠ 0 := by
    have : 0 < Fintype.card K := Fintype.card_pos
    exact_mod_cast this.ne'
  apply mul_left_cancel₀ hq
  rw [V_fin_mul hc (m + 1)]
  ring

section Matrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "𝕃" => QuadraticAlgebra K a 0

theorem star_mul_self_eq (z : 𝕃) : star z * z = algebraMap K 𝕃 (QuadraticAlgebra.norm z) := by
  rw [algebraMap_norm_eq_mul_star, mul_comm]

/-- The sesquilinear form $B_H(x, y) = x^* H y$ on $L^\iota$. -/
def B (H : Matrix ι ι 𝕃) (x y : ι → 𝕃) : 𝕃 := star x ⬝ᵥ (H *ᵥ y)

theorem gram_apply (P H Q : Matrix ι ι 𝕃) (i j : ι) :
    (Pᴴ * H * Q) i j = B H (fun k => P k i) (fun k => Q k j) := by
  simp only [B, Matrix.mul_apply, dotProduct, Matrix.mulVec, conjTranspose_apply, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem B_symm {H : Matrix ι ι 𝕃} (hH : H.IsHermitian) (x y : ι → 𝕃) :
    B H y x = star (B H x y) := by
  simp only [B, dotProduct, Matrix.mulVec, star_sum, star_mul, Pi.star_apply, star_star,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  rw [← hH.apply r p]
  ring

theorem B_smul (H : Matrix ι ι 𝕃) (z w : 𝕃) (x y : ι → 𝕃) :
    B H (z • x) (w • y) = star z * w * B H x y := by
  simp only [B, dotProduct, Matrix.mulVec, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem B_add_self (H : Matrix ι ι 𝕃) (x y : ι → 𝕃) :
    B H (x + y) (x + y) = B H x x + B H x y + B H y x + B H y y := by
  simp only [B, dotProduct, Matrix.mulVec, Pi.add_apply, Pi.star_apply, star_add,
    Finset.sum_add_distrib, mul_add, add_mul]
  ring

theorem a_ne_zero : a ≠ 0 := by
  rintro rfl
  exact Fact.out (p := ¬ IsSquare (0 : K)) ⟨0, by simp⟩

theorem re_eq_zero_of_add_star (hK : ringChar K ≠ 2) {β : 𝕃} (h : β + star β = 0) :
    β.re = 0 := by
  have h1 := congrArg QuadraticAlgebra.re h
  simp only [re_add, re_star, zero_mul, add_zero, re_zero] at h1
  have h2 : (2 : K) * β.re = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_left (Ring.two_ne_zero hK)

/-- A hermitian matrix whose quadratic form vanishes identically is zero. -/
theorem eq_zero_of_B_self_eq_zero (hK : ringChar K ≠ 2) {H : Matrix ι ι 𝕃} (hH : H.IsHermitian)
    (h : ∀ x, B H x x = 0) : H = 0 := by
  have hre : ∀ x y, (B H x y).re = 0 := by
    intro x y
    apply re_eq_zero_of_add_star hK
    have := h (x + y)
    rw [B_add_self, h x, h y, B_symm hH x y] at this
    simpa using this
  have hall : ∀ x y, B H x y = 0 := by
    intro x y
    have h1 := hre x y
    have h2 := hre x ((⟨0, 1⟩ : 𝕃) • y)
    rw [show B H x ((⟨0, 1⟩ : 𝕃) • y) = (⟨0, 1⟩ : 𝕃) * B H x y by
      have := B_smul H 1 (⟨0, 1⟩ : 𝕃) x y
      simpa using this] at h2
    simp only [re_mul, zero_mul, zero_add, mul_one] at h2
    have h3 : (B H x y).im = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h a_ne_zero
      · exact h
    exact QuadraticAlgebra.ext h1 h3
  refine Matrix.ext fun i j => ?_
  have := gram_apply 1 H 1 i j
  simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at this
  rw [this, hall]
  rfl

/-- For a nonzero hermitian matrix there is a vector with $x^* H x = 1$. -/
theorem exists_unit_vec (hK : ringChar K ≠ 2) {H : Matrix ι ι 𝕃} (hH : H.IsHermitian)
    (hne : H ≠ 0) : ∃ x, B H x x = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, B H x x ≠ 0 := by
    by_contra hcon
    exact hne (eq_zero_of_B_self_eq_zero hK hH fun x => by_contra fun hx => hcon ⟨x, hx⟩)
  have hstar : star (B H x x) = B H x x := (B_symm hH x x).symm
  have him : (B H x x).im = 0 := by
    have h1 := congrArg QuadraticAlgebra.im hstar
    simp only [im_star] at h1
    have h2 : (2 : K) * (B H x x).im = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h2).resolve_left (Ring.two_ne_zero hK)
  obtain ⟨c, hval⟩ : ∃ c : K, B H x x = algebraMap K 𝕃 c :=
    ⟨(B H x x).re, QuadraticAlgebra.ext rfl (by simpa using him)⟩
  have hc : c ≠ 0 := by
    intro h0
    apply hx
    rw [hval, h0, map_zero]
  obtain ⟨z, hz⟩ := exists_norm_eq (a := a) c⁻¹
  refine ⟨z • x, ?_⟩
  rw [B_smul, star_mul_self_eq, hz, hval, ← map_mul, inv_mul_cancel₀ hc, map_one]

theorem exists_basis_col (x : Option ι → 𝕃) (hx : x ≠ 0) :
    ∃ P : Matrix (Option ι) (Option ι) 𝕃, P.det ≠ 0 ∧ ∀ i, P i none = x i := by
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
    by_contra h
    exact hx (funext fun k => by_contra fun hk => h ⟨k, hk⟩)
  have hQ : ((1 : Matrix (Option ι) (Option ι) 𝕃).updateCol k x).det = x k := by
    have := det_updateCol_sum (1 : Matrix (Option ι) (Option ι) 𝕃) k x
    simpa [Matrix.one_apply] using this
  refine ⟨((1 : Matrix (Option ι) (Option ι) 𝕃).updateCol k x).submatrix id
    (Equiv.swap none k), ?_, ?_⟩
  · rw [det_permute', hQ]
    refine mul_ne_zero ?_ hk
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (none : Option ι) k)) with h | h <;>
      simp [h]
  · intro i
    simp

theorem det_schur (G : Matrix (Option ι) (Option ι) 𝕃) (h1 : G none none = 1) :
    G.det = (Matrix.of fun i j => G (some i) (some j) - G (some i) none * G none (some j)).det := by
  have hM : G.submatrix (Equiv.optionEquivSumPUnit ι).symm (Equiv.optionEquivSumPUnit ι).symm =
      Matrix.fromBlocks (Matrix.of fun i j => G (some i) (some j))
        (Matrix.of fun i (_ : PUnit.{1}) => G (some i) none)
        (Matrix.of fun (_ : PUnit.{1}) j => G none (some j)) 1 := by
    refine Matrix.ext ?_
    rintro (i | i) (j | j)
    · simp
    · simp
    · simp
    · simp [h1]
  rw [← det_submatrix_equiv_self (Equiv.optionEquivSumPUnit ι).symm G, hM, det_fromBlocks_one₂₂]
  refine congrArg _ (Matrix.ext fun i j => ?_)
  simp [Matrix.mul_apply]

theorem star_congr {Rg : Type*} [Ring Rg] [StarRing Rg] (P Q R H : Rg) (hPQ : P * Q = 1)
    (hRG : star R * R = star P * H * P) : star (R * Q) * (R * Q) = H := by
  have e1 : star Q * star P = 1 := by rw [← star_mul, hPQ, star_one]
  calc star (R * Q) * (R * Q) = star Q * (star R * R) * Q := by simp only [star_mul, mul_assoc]
    _ = star Q * (star P * H * P) * Q := by rw [hRG]
    _ = (star Q * star P) * H * (P * Q) := by simp only [mul_assoc]
    _ = H := by rw [e1, hPQ, one_mul, mul_one]

theorem star_congr_inv {Rg : Type*} [Ring Rg] [StarRing Rg] (P Q Y : Rg) (hPQ : P * Q = 1)
    (hY : star Y * Y = 1) : star (Q * Y * P) * (star P * P) * (Q * Y * P) = star P * P := by
  have e1 : star Q * star P = 1 := by rw [← star_mul, hPQ, star_one]
  calc star (Q * Y * P) * (star P * P) * (Q * Y * P)
      = star P * star Y * (star Q * star P) * (P * Q) * Y * P := by simp only [star_mul, mul_assoc]
    _ = star P * (star Y * Y) * P := by rw [e1, hPQ]; simp only [mul_one, mul_assoc]
    _ = star P * P := by rw [hY, mul_one]

/-- Every nondegenerate hermitian $H \in M_\iota(L)$ has the form $H = P^* P$. -/
def Gram (a : K) (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ H : Matrix ι ι (QuadraticAlgebra K a 0), H.IsHermitian → H.det ≠ 0 →
    ∃ P : Matrix ι ι (QuadraticAlgebra K a 0), Pᴴ * P = H

/-- The block matrix $\begin{pmatrix} 1 & s \\ 0 & Y \end{pmatrix}$ indexed by `Option ι`
(`none` is the extra index $0$). -/
def ext2 (s : ι → 𝕃) (Y : Matrix ι ι 𝕃) : Matrix (Option ι) (Option ι) 𝕃 :=
  Matrix.of fun i j => match i, j with
    | none, none => 1
    | none, some j => s j
    | some _, none => 0
    | some i, some j => Y i j

@[simp] theorem ext2_nn (s : ι → 𝕃) (Y : Matrix ι ι 𝕃) : ext2 s Y none none = 1 := rfl
@[simp] theorem ext2_ns (s : ι → 𝕃) (Y : Matrix ι ι 𝕃) (j : ι) : ext2 s Y none (some j) = s j := rfl
@[simp] theorem ext2_sn (s : ι → 𝕃) (Y : Matrix ι ι 𝕃) (i : ι) : ext2 s Y (some i) none = 0 := rfl
@[simp] theorem ext2_ss (s : ι → 𝕃) (Y : Matrix ι ι 𝕃) (i j : ι) :
    ext2 s Y (some i) (some j) = Y i j := rfl

theorem ext2_gram_nn (s : ι → 𝕃) (Y : Matrix ι ι 𝕃) :
    ((ext2 s Y)ᴴ * ext2 s Y) none none = 1 := by
  simp [Matrix.mul_apply, Fintype.sum_option, conjTranspose_apply]

theorem ext2_gram_ns (s : ι → 𝕃) (Y : Matrix ι ι 𝕃) (j : ι) :
    ((ext2 s Y)ᴴ * ext2 s Y) none (some j) = s j := by
  simp [Matrix.mul_apply, Fintype.sum_option, conjTranspose_apply]

theorem ext2_gram_sn (s : ι → 𝕃) (Y : Matrix ι ι 𝕃) (i : ι) :
    ((ext2 s Y)ᴴ * ext2 s Y) (some i) none = star (s i) := by
  simp [Matrix.mul_apply, Fintype.sum_option, conjTranspose_apply]

theorem ext2_gram_ss (s : ι → 𝕃) (Y : Matrix ι ι 𝕃) (i j : ι) :
    ((ext2 s Y)ᴴ * ext2 s Y) (some i) (some j) = star (s i) * s j + (Yᴴ * Y) i j := by
  simp [Matrix.mul_apply, Fintype.sum_option, conjTranspose_apply]

/-- The key reduction step: a hermitian matrix with $G_{00} = 1$ is $R^* R$ with $R$ block
upper triangular with first column $e_0$, provided the same holds in smaller dimension. -/
theorem core (hι : Gram a ι) (G : Matrix (Option ι) (Option ι) 𝕃) (hG : G.IsHermitian)
    (hdet : G.det ≠ 0) (h1 : G none none = 1) :
    ∃ R : Matrix (Option ι) (Option ι) 𝕃, Rᴴ * R = G ∧
      ∀ i, R i none = if i = none then 1 else 0 := by
  have hG'h : (Matrix.of fun i j => G (some i) (some j) - G (some i) none * G none (some j)
      : Matrix ι ι 𝕃).IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [of_apply, star_sub, star_mul, hG.apply]
  obtain ⟨R₁, hR₁⟩ := hι _ hG'h (by rw [← det_schur G h1]; exact hdet)
  refine ⟨ext2 (fun j => G none (some j)) R₁, ?_, ?_⟩
  · refine Matrix.ext ?_
    rintro (i | i) (j | j)
    · rw [ext2_gram_nn, h1]
    · rw [ext2_gram_ns]
    · rw [ext2_gram_sn]
      exact hG.apply _ _
    · rw [ext2_gram_ss, hR₁, hG.apply (some i) none]
      simp only [of_apply]
      ring
  · intro i
    cases i <;> simp

theorem data (hι : Gram a ι) (H : Matrix (Option ι) (Option ι) 𝕃) (hH : H.IsHermitian)
    (hdet : H.det ≠ 0) (x : Option ι → 𝕃) (hx : B H x x = 1) :
    ∃ P R : Matrix (Option ι) (Option ι) 𝕃, P.det ≠ 0 ∧ (∀ i, P i none = x i) ∧
      Rᴴ * R = Pᴴ * H * P ∧ ∀ i, R i none = if i = none then 1 else 0 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : B H 0 0 = 0 := by simp [B]
    rw [this] at hx
    exact zero_ne_one hx
  obtain ⟨P, hPdet, hPcol⟩ := exists_basis_col x hx0
  have hGh : (Pᴴ * H * P).IsHermitian := by
    show (Pᴴ * H * P)ᴴ = Pᴴ * H * P
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]
  have hGdet : (Pᴴ * H * P).det ≠ 0 := by
    rw [det_mul, det_mul, det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero (by simpa using hPdet) hdet) hPdet
  have hG1 : (Pᴴ * H * P) none none = 1 := by
    rw [gram_apply, show (fun k => P k none) = x from funext hPcol]
    exact hx
  obtain ⟨R, hR, hRcol⟩ := core hι _ hGh hGdet hG1
  exact ⟨P, R, hPdet, hPcol, hR, hRcol⟩

theorem gram_option (hK : ringChar K ≠ 2) (hι : Gram a ι) : Gram a (Option ι) := by
  intro H hH hdet
  have hne : H ≠ 0 := by
    rintro rfl
    have : Nonempty (Option ι) := ⟨none⟩
    exact hdet det_zero
  obtain ⟨x, hx⟩ := exists_unit_vec hK hH hne
  obtain ⟨P, R, hPdet, -, hR, -⟩ := data hι H hH hdet x hx
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdet
  exact ⟨R * P⁻¹, star_congr P P⁻¹ R H (Matrix.mul_nonsing_inv P hPu) hR⟩

theorem transitive (hι : Gram a ι) (x : Option ι → 𝕃)
    (hx : B (1 : Matrix (Option ι) (Option ι) 𝕃) x x = 1) :
    ∃ X : Matrix (Option ι) (Option ι) 𝕃, Xᴴ * X = 1 ∧ ∀ i, X i none = x i := by
  obtain ⟨P, R, hPdet, hPcol, hR, hRcol⟩ := data hι 1 Matrix.isHermitian_one (by simp) x hx
  have hRdet : R.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hR
    rw [det_mul, h0, mul_zero, Matrix.mul_one, det_mul, det_conjTranspose] at this
    exact mul_ne_zero (by simpa using hPdet) hPdet this.symm
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.mpr hRdet
  refine ⟨P * R⁻¹, ?_, ?_⟩
  · exact star_congr R R⁻¹ P 1 (Matrix.mul_nonsing_inv R hRu) (by
    have h := hR.symm
    rw [Matrix.mul_one] at h ⊢
    exact h)
  · intro i
    have h1 : ∀ j, R⁻¹ j none = if j = none then 1 else 0 := by
      intro j
      have := congrFun (congrFun (Matrix.nonsing_inv_mul R hRu) j) none
      simp only [Matrix.mul_apply, hRcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Matrix.one_apply] at this
      exact this
    simp only [Matrix.mul_apply, h1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    exact hPcol i

theorem gram_equiv {κ : Type*} [Fintype κ] [DecidableEq κ] (hι : Gram a ι) (e : ι ≃ κ) :
    Gram a κ := by
  intro H hH hdet
  obtain ⟨P, hP⟩ := hι (H.submatrix e e) (hH.submatrix e)
    (by rw [det_submatrix_equiv_self]; exact hdet)
  refine ⟨P.submatrix e.symm e.symm, Matrix.ext fun i j => ?_⟩
  have := congrFun (congrFun hP (e.symm i)) (e.symm j)
  simp only [Matrix.mul_apply, conjTranspose_apply, submatrix_apply, Equiv.apply_symm_apply]
    at this ⊢
  exact (Fintype.sum_equiv e.symm _ _ (fun k => rfl)).trans this

theorem card_congr_of_gram (P : Matrix ι ι 𝕃) (hP : P.det ≠ 0) (H : Matrix ι ι 𝕃)
    (hPH : Pᴴ * P = H) :
    Nat.card {X : Matrix ι ι 𝕃 // Xᴴ * H * X = H} =
      Nat.card {Y : Matrix ι ι 𝕃 // Yᴴ * Y = 1} := by
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have hPQ : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have hQP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
  subst hPH
  have hto : ∀ X : {X : Matrix ι ι 𝕃 // Xᴴ * (Pᴴ * P) * X = Pᴴ * P},
      (P * X.1 * P⁻¹)ᴴ * (P * X.1 * P⁻¹) = 1 := by
    intro X
    have h2 : (P * X.1)ᴴ * (P * X.1) = Pᴴ * P := by
      calc (P * X.1)ᴴ * (P * X.1) = X.1ᴴ * (Pᴴ * P) * X.1 := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = Pᴴ * P := X.2
    exact star_congr P P⁻¹ (P * X.1) 1 hPQ (by rw [Matrix.mul_one]; exact h2)
  have hfrom : ∀ Y : {Y : Matrix ι ι 𝕃 // Yᴴ * Y = 1},
      (P⁻¹ * Y.1 * P)ᴴ * (Pᴴ * P) * (P⁻¹ * Y.1 * P) = Pᴴ * P := fun Y =>
    star_congr_inv P P⁻¹ Y.1 hPQ Y.2
  refine Nat.card_congr
    { toFun := fun X => ⟨P * X.1 * P⁻¹, hto X⟩
      invFun := fun Y => ⟨P⁻¹ * Y.1 * P, hfrom Y⟩
      left_inv := fun X => Subtype.ext ?_
      right_inv := fun Y => Subtype.ext ?_ }
  · show P⁻¹ * (P * X.1 * P⁻¹) * P = X.1
    calc P⁻¹ * (P * X.1 * P⁻¹) * P = (P⁻¹ * P) * X.1 * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = X.1 := by rw [hQP, Matrix.one_mul, Matrix.mul_one]
  · show P * (P⁻¹ * Y.1 * P) * P⁻¹ = Y.1
    calc P * (P⁻¹ * Y.1 * P) * P⁻¹ = (P * P⁻¹) * Y.1 * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = Y.1 := by rw [hPQ, Matrix.one_mul, Matrix.mul_one]

theorem dot_star_self_eq (x : ι → 𝕃) :
    star x ⬝ᵥ x = algebraMap K 𝕃 (∑ i, QuadraticAlgebra.norm (x i)) := by
  simp only [dotProduct, Pi.star_apply, star_mul_self_eq, map_sum]

theorem dot_star_self_eq_one_iff (x : ι → 𝕃) :
    star x ⬝ᵥ x = 1 ↔ ∑ i, QuadraticAlgebra.norm (x i) = 1 := by
  rw [dot_star_self_eq, ← map_one (algebraMap K 𝕃)]
  exact QuadraticAlgebra.algebraMap_injective.eq_iff

theorem sumnorm_of_unitary (X : Matrix ι ι 𝕃) (hX : Xᴴ * X = 1) (j : ι) :
    ∑ i, QuadraticAlgebra.norm (X i j) = 1 := by
  have h := gram_apply X 1 X j j
  rw [Matrix.mul_one, hX, Matrix.one_apply_eq] at h
  apply (dot_star_self_eq_one_iff _).mp
  simpa [B, Matrix.one_mulVec] using h.symm

theorem stab_ext (Z : Matrix (Option ι) (Option ι) 𝕃) (hZ : Zᴴ * Z = 1)
    (hcol : ∀ i, Z i none = if i = none then 1 else 0) :
    Z = ext2 0 (Z.submatrix some some) ∧
      (Z.submatrix some some)ᴴ * Z.submatrix some some = 1 := by
  have hrow : ∀ j, Z none (some j) = 0 := by
    intro j
    have h := congrFun (congrFun hZ none) (some j)
    simpa [Matrix.mul_apply, Fintype.sum_option, conjTranspose_apply, hcol] using h
  refine ⟨Matrix.ext ?_, Matrix.ext fun i j => ?_⟩
  · rintro (i | i) (j | j)
    · simp [hcol]
    · simp [hrow]
    · simp [hcol]
    · simp
  · have h := congrFun (congrFun hZ (some i)) (some j)
    simpa [Matrix.mul_apply, Fintype.sum_option, conjTranspose_apply, hcol, hrow,
      Matrix.one_apply] using h

theorem ext2_zero_unitary (Y : Matrix ι ι 𝕃) (hY : Yᴴ * Y = 1) :
    (ext2 0 Y)ᴴ * ext2 0 Y = 1 ∧ ∀ i, ext2 0 Y i none = if i = none then 1 else 0 := by
  constructor
  · refine Matrix.ext ?_
    rintro (i | i) (j | j)
    · simp [ext2_gram_nn]
    · simp [ext2_gram_ns]
    · simp [ext2_gram_sn]
    · rw [ext2_gram_ss]
      simp [hY, Matrix.one_apply]
  · intro i
    cases i <;> simp

theorem stab_data (X G : Matrix (Option ι) (Option ι) 𝕃) (hX : Xᴴ * X = 1) (hG : Gᴴ * G = 1)
    (hcol : ∀ i, G i none = X i none) :
    (Gᴴ * X)ᴴ * (Gᴴ * X) = 1 ∧ ∀ i, (Gᴴ * X) i none = if i = none then 1 else 0 := by
  have hGG : G * Gᴴ = 1 := mul_eq_one_comm.mp hG
  constructor
  · calc (Gᴴ * X)ᴴ * (Gᴴ * X) = Xᴴ * (G * Gᴴ) * X := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = 1 := by rw [hGG, Matrix.mul_one, hX]
  · intro i
    have h := congrFun (congrFun hG i) none
    rw [Matrix.one_apply] at h
    rw [← h]
    simp only [Matrix.mul_apply, conjTranspose_apply, hcol]

/-- Orbit-stabilizer step: $|U_{m+1}| = N_{m+1}(1) \cdot |U_m|$, where $N_{m+1}(1)$ is the number of
vectors of norm $1$ (`V a (Option ι) 1`), given that every nondegenerate hermitian form of size
$|\iota|$ is of the form $P^* P$ (`hι`). -/
theorem ucard_option (hι : Gram a ι) :
    Nat.card {X : Matrix (Option ι) (Option ι) 𝕃 // Xᴴ * X = 1} =
      V a (Option ι) 1 * Nat.card {Y : Matrix ι ι 𝕃 // Yᴴ * Y = 1} := by
  classical
  have htrans : ∀ x : Option ι → 𝕃, ∑ i, QuadraticAlgebra.norm (x i) = 1 →
      ∃ X : Matrix (Option ι) (Option ι) 𝕃, Xᴴ * X = 1 ∧ ∀ i, X i none = x i := by
    intro x hx
    refine transitive hι x ?_
    have := (dot_star_self_eq_one_iff x).mpr hx
    simpa [B, Matrix.one_mulVec] using this
  choose! g hg1 hg2 using htrans
  have hSv : Nat.card {x : Option ι → 𝕃 // ∑ i, QuadraticAlgebra.norm (x i) = 1} =
      V a (Option ι) 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  have hZ : ∀ X : {X : Matrix (Option ι) (Option ι) 𝕃 // Xᴴ * X = 1},
      ((g (fun i => X.1 i none))ᴴ * X.1)ᴴ * ((g (fun i => X.1 i none))ᴴ * X.1) = 1 ∧
      ∀ i, ((g (fun i => X.1 i none))ᴴ * X.1) i none = if i = none then 1 else 0 := fun X =>
    stab_data X.1 (g _) X.2 (hg1 _ (sumnorm_of_unitary X.1 X.2 none))
      (fun i => hg2 _ (sumnorm_of_unitary X.1 X.2 none) i)
  have hinv : ∀ p : {x : Option ι → 𝕃 // ∑ i, QuadraticAlgebra.norm (x i) = 1} ×
      {Y : Matrix ι ι 𝕃 // Yᴴ * Y = 1},
      (g p.1.1 * ext2 0 p.2.1)ᴴ * (g p.1.1 * ext2 0 p.2.1) = 1 := by
    intro p
    calc (g p.1.1 * ext2 0 p.2.1)ᴴ * (g p.1.1 * ext2 0 p.2.1)
        = (ext2 0 p.2.1)ᴴ * ((g p.1.1)ᴴ * g p.1.1) * ext2 0 p.2.1 := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [hg1 _ p.1.2, Matrix.mul_one]
          exact (ext2_zero_unitary _ p.2.2).1
  rw [← hSv, ← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun X => (⟨fun i => X.1 i none, sumnorm_of_unitary X.1 X.2 none⟩,
        ⟨((g (fun i => X.1 i none))ᴴ * X.1).submatrix some some,
          (stab_ext _ (hZ X).1 (hZ X).2).2⟩)
      invFun := fun p => ⟨g p.1.1 * ext2 0 p.2.1, hinv p⟩
      left_inv := fun X => Subtype.ext ?_
      right_inv := fun p => ?_ }
  · show g (fun i => X.1 i none) * ext2 0 (((g (fun i => X.1 i none))ᴴ * X.1).submatrix some some)
      = X.1
    rw [← (stab_ext _ (hZ X).1 (hZ X).2).1, ← Matrix.mul_assoc,
      mul_eq_one_comm.mp (hg1 _ (sumnorm_of_unitary X.1 X.2 none)), Matrix.one_mul]
  · obtain ⟨⟨x, hx⟩, ⟨Y, hY⟩⟩ := p
    have hcol : (fun i => (g x * ext2 0 Y) i none) = x := by
      funext i
      simp only [Matrix.mul_apply, (ext2_zero_unitary Y hY).2, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact hg2 _ hx i
    have hgc : g (fun i => (g x * ext2 0 Y) i none) = g x := congrArg g hcol
    refine Prod.ext (Subtype.ext hcol) (Subtype.ext ?_)
    show ((g (fun i => (g x * ext2 0 Y) i none))ᴴ * (g x * ext2 0 Y)).submatrix some some = Y
    rw [hgc, ← Matrix.mul_assoc, hg1 _ hx, Matrix.one_mul]
    exact Matrix.ext fun i j => rfl

theorem unitary_submatrix {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (Y : Matrix ι ι 𝕃) (hY : Yᴴ * Y = 1) :
    (Y.submatrix e.symm e.symm)ᴴ * Y.submatrix e.symm e.symm = 1 := by
  refine Matrix.ext fun i j => ?_
  have := congrFun (congrFun hY (e.symm i)) (e.symm j)
  simp only [Matrix.mul_apply, conjTranspose_apply, submatrix_apply, Matrix.one_apply,
    EmbeddingLike.apply_eq_iff_eq] at this ⊢
  exact (Fintype.sum_equiv e.symm _ _ (fun k => rfl)).trans this

theorem ucard_equiv {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) :
    Nat.card {X : Matrix ι ι 𝕃 // Xᴴ * X = 1} = Nat.card {X : Matrix κ κ 𝕃 // Xᴴ * X = 1} := by
  have key2 : ∀ Y : Matrix κ κ 𝕃, Yᴴ * Y = 1 → (Y.submatrix e e)ᴴ * Y.submatrix e e = 1 := by
    intro Y hY
    have := unitary_submatrix e.symm Y hY
    rwa [Equiv.symm_symm] at this
  refine Nat.card_congr
    { toFun := fun X => ⟨X.1.submatrix e.symm e.symm, unitary_submatrix e X.1 X.2⟩
      invFun := fun Y => ⟨Y.1.submatrix e e, key2 Y.1 Y.2⟩
      left_inv := fun X => Subtype.ext (Matrix.ext fun i j => by simp)
      right_inv := fun Y => Subtype.ext (Matrix.ext fun i j => by simp) }

theorem gram_fin (hK : ringChar K ≠ 2) (m : ℕ) : Gram a (Fin m) := by
  induction m with
  | zero => exact fun H _ _ => ⟨H, Matrix.ext fun i j => i.elim0⟩
  | succ m ih => exact gram_equiv (gram_option hK ih) (finSuccEquiv m).symm

theorem ucard_fin (hK : ringChar K ≠ 2) (m : ℕ) :
    (Nat.card {X : Matrix (Fin m) (Fin m) 𝕃 // Xᴴ * X = 1} : ℤ) =
      (Fintype.card K : ℤ) ^ (m * (m - 1) / 2) *
        ∏ i ∈ Finset.range m, ((Fintype.card K : ℤ) ^ (i + 1) - (-1) ^ (i + 1)) := by
  induction m with
  | zero =>
    have : Nat.card {X : Matrix (Fin 0) (Fin 0) 𝕃 // Xᴴ * X = 1} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun X Y => Subtype.ext (Matrix.ext fun i j => i.elim0)⟩,
        ⟨⟨1, Matrix.ext fun i j => i.elim0⟩⟩⟩
    rw [this]
    simp
  | succ m ih =>
    have hV : (V a (Option (Fin m)) 1 : ℤ) = (Fintype.card K : ℤ) ^ m *
        ((Fintype.card K : ℤ) ^ (m + 1) - (-1) ^ (m + 1)) := by
      rw [V_equiv (finSuccEquiv m).symm 1]
      exact V_fin_succ one_ne_zero m
    have hexp : (m + 1) * (m + 1 - 1) / 2 = m + m * (m - 1) / 2 := by
      rcases m with _ | k
      · simp
      · have h : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
          simp only [Nat.add_sub_cancel]; ring
        rw [h]
        omega
    rw [ucard_equiv (finSuccEquiv m), ucard_option (gram_fin hK m), Nat.cast_mul, hV, ih,
      Finset.prod_range_succ, hexp, pow_add]
    ring

end Matrices

end Inert

section Final

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {a : K}

/-- **Inert case.** Let $K$ be a finite field with $q$ elements, $\operatorname{char} K \ne 2$, and
$a \in K$ a non-square (so $L = K[\omega]/(\omega^2 - a)$ is the field with $q^2$ elements and
conjugation is the Frobenius).  For a hermitian $H \in M_m(L)$ (`hH`) with $\det H \ne 0$
(`hdet`), the unitary group $U(H) = \{X \in M_m(L) : X^* H X = H\}$ has order
$$|U(H)| = q^{m(m-1)/2} \prod_{i=0}^{m-1} \bigl(q^{i+1} - (-1)^{i+1}\bigr).$$
Hypotheses: `ha` ($a$ is not a square), `hK` ($\operatorname{char} K \ne 2$), `hH` ($H^* = H$),
`hdet` ($\det H \ne 0$).  Indices are 0-based (`Fin m`). -/
@[kb "ganhankeyu2001" "(2.11), p. 104 and Table 1 (#U_m(𝔽_q), v inert) [running text]"]
theorem card_unitary_inert {m : ℕ} (ha : ¬ IsSquare a) (hK : ringChar K ≠ 2)
    (H : Matrix (Fin m) (Fin m) (QuadraticAlgebra K a 0)) (hH : H.IsHermitian)
    (hdet : H.det ≠ 0) :
    (Nat.card {X : Matrix (Fin m) (Fin m) (QuadraticAlgebra K a 0) // Xᴴ * H * X = H} : ℤ) =
      (Fintype.card K : ℤ) ^ (m * (m - 1) / 2) *
        ∏ i ∈ Finset.range m, ((Fintype.card K : ℤ) ^ (i + 1) - (-1) ^ (i + 1)) := by
  have : Fact (¬ IsSquare a) := ⟨ha⟩
  obtain ⟨P, hP⟩ := gram_fin hK m H hH hdet
  have hPdet : P.det ≠ 0 := by
    intro h0
    apply hdet
    rw [← hP, det_mul, h0, mul_zero]
  rw [card_congr_of_gram P hPdet H hP]
  exact ucard_fin hK m

end Final

end QuadFormsKB.Tamagawa.Unitary.FiniteCount
