/-
# O'Meara 55:5, the inclusion $\Omega \subseteq (O^+)^2$ (p. 140)

**Setting.** As in `Sec55.lean`: a field $F$ of characteristic $\ne 2$, a finite-dimensional quadratic space
$(V, Q)$, regular meaning `(QuadraticMap.associated Q).Nondegenerate`.

**Proves** the missing half of 55:5: for a regular space with $n \le 3$, $\Omega_n = (O^+_n)^2$, where
$(O^+_n)^2$ is the *set* of squares of rotations.

*Deviation from the book's proof.* The book (via 43:5a, 43:8 and a case analysis on the axis of a rotation) is
replaced by a shorter argument: if $\sigma \in O' = \Omega$ with $n \le 3$ then $\sigma = \tau_x\tau_y$ with
$Q(x) = Q(y)$ (this is how $O' \subseteq \Omega$ is proved in `Sec55.lean`), and for any two anisotropic vectors
with $Q(x) = Q(y)$ one has $\tau_x\tau_y = (\tau_x\tau_w)^2$ where $w = x + y$ or $w = x - y$ is anisotropic
(because $Q(x+y) + Q(x-y) = 4Q(x) \ne 0$), since $\tau_w x = \mp y$ gives $\tau_y = \tau_w\tau_x\tau_w$.
This needs neither Corollary 43:5a nor the structure of binary spaces. Helper lemmas are in the namespace `Om55`.
-/
import QuadFormsKB.Literature.OMeara.Sec55

noncomputable section

namespace QuadFormsKB.OMeara

open Cl54 Sp55

namespace Om55

section Basic

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- Symmetries in proportional vectors agree. -/
theorem symmetry_eq_of_eq_smul {u y : V} (hu : Q u ≠ 0) (hy : Q y ≠ 0) (t : F) (ht : t ≠ 0)
    (h : u = t • y) : symmetry Q u hu = symmetry Q y hy := by
  subst h
  exact symmetry_smul_vec Q ht hy hu

/-- **Key identity:** if $Q(x) = Q(y) \ne 0$ and $w = x + \varepsilon y$ is anisotropic with $\varepsilon^2 = 1$,
then $\tau_x\tau_y = (\tau_x\tau_w)^2$. -/
theorem symmetry_mul_symmetry_eq_sq {x y : V} (hx : Q x ≠ 0) (hy : Q y ≠ 0) (hxy : Q x = Q y) {ε : F}
    (hε : ε ^ 2 = 1) (hw : Q (x + ε • y) ≠ 0) :
    symmetry Q x hx * symmetry Q y hy = (symmetry Q x hx * symmetry Q (x + ε • y) hw) ^ 2 := by
  have hε0 : ε ≠ 0 := fun h => by simp [h] at hε
  have hQw : Q (x + ε • y) = 2 * (Q x + ε * bil Q x y) := by
    rw [Q_add, Q_smul, bil_smul_right, ← hxy]
    linear_combination (Q x) * hε
  have hbw : bil Q x (x + ε • y) = Q x + ε * bil Q x y := by
    rw [bil_add_right, bil_smul_right, bil_self]
  have hne : Q x + ε * bil Q x y ≠ 0 := fun h => hw (by rw [hQw, h, mul_zero])
  have hgx : symmetry Q (x + ε • y) hw x = (-ε) • y := by
    rw [symmetry_apply, hbw, hQw]
    have : 2 * (Q x + ε * bil Q x y) / (2 * (Q x + ε * bil Q x y)) = 1 :=
      div_self (mul_ne_zero two_ne_zero hne)
    rw [this, one_smul, sub_add_cancel_left, neg_smul]
  have hg : symmetry Q (x + ε • y) hw ∈ orth Q := symmetry_mem_orth Q hw
  have hconj := conj_symmetry Q hg hx
  have e := symmetry_eq_of_eq_smul Q (u := symmetry Q (x + ε • y) hw x)
    (by rw [hg x]; exact hx) hy (-ε) (neg_ne_zero.mpr hε0) hgx
  have hconj' : symmetry Q (x + ε • y) hw * symmetry Q x hx * (symmetry Q (x + ε • y) hw)⁻¹ =
      symmetry Q y hy := hconj.trans e
  have ginv : (symmetry Q (x + ε • y) hw)⁻¹ = symmetry Q (x + ε • y) hw := by
    refine inv_eq_of_mul_eq_one_right ?_
    ext z
    exact symmetry_symmetry Q hw z
  rw [ginv] at hconj'
  rw [← hconj', pow_two]
  simp only [mul_assoc]

/-- **A product of two symmetries in vectors of equal norm is the square of a rotation** (valid in every
dimension): if $Q(x) = Q(y) \ne 0$ then $\tau_x\tau_y = \rho^2$ with $\rho = \tau_x\tau_w \in O^+$, where
$w \in \{x + y, x - y\}$. -/
theorem exists_sq_symmetry_mul {x y : V} (hx : Q x ≠ 0) (hy : Q y ≠ 0) (hxy : Q x = Q y) :
    ∃ ρ ∈ orthPlus Q, symmetry Q x hx * symmetry Q y hy = ρ ^ 2 := by
  by_cases h : Q (x + (1 : F) • y) = 0
  · have hw : Q (x + (-1 : F) • y) ≠ 0 := by
      intro hz
      rw [Q_add, Q_smul, bil_smul_right] at h hz
      have h4 : (4 : F) ≠ 0 := by
        rw [show (4 : F) = 2 * 2 by norm_num]
        exact mul_ne_zero two_ne_zero two_ne_zero
      apply hx
      have : (4 : F) * Q x = 0 := by linear_combination h + hz + (2 : F) * hxy
      exact (mul_eq_zero.mp this).resolve_left h4
    exact ⟨_, symmetry_mul_mem_orthPlus Q hx hw,
      symmetry_mul_symmetry_eq_sq Q hx hy hxy (ε := -1) (by norm_num) hw⟩
  · exact ⟨_, symmetry_mul_mem_orthPlus Q hx h,
      symmetry_mul_symmetry_eq_sq Q hx hy hxy (ε := 1) (by norm_num) h⟩

end Basic

end Om55

section Main

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **$\Omega \subseteq (O^+)^2$ for $n \le 3$** (O'Meara 1963, 55:5, p. 140): every element of $\Omega_n$ is the
square of a rotation. (Valid also for $n = 0$.) -/
theorem exists_sq_of_mem_omega (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : Module.finrank F V ≤ 3) {τ : V ≃ₗ[F] V} (hτ : τ ∈ omega Q) :
    ∃ ρ ∈ orthPlus Q, τ = ρ ^ 2 := by
  rw [omega_eq_orthPrime_of_finrank_le_three Q hQ h3] at hτ
  obtain ⟨hplus, hσ1⟩ := hτ
  obtain ⟨l, hl, h, hlen⟩ := exists_symmetry_prod_eq_length_le_two Q hQ h3 hplus
  rw [attach_prod_eq_symProd Q l hl] at h
  have hev := even_length_of_mem_orthPlus Q hplus l hl h
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
  · have : τ = 1 := h
    exact ⟨1, (orthPlus Q).one_mem, by rw [this, one_pow]⟩
  · simp at hev
  · have hx := hl x (by simp)
    have hy := hl y (by simp)
    have hσ2 : HasSpinorNorm Q τ (Q x * Q y) :=
      (hasSpinorNorm_iff Q).mpr ⟨[x, y], hl, h, 1, one_ne_zero, by simp⟩
    obtain ⟨s, hs, hxy⟩ := HasSpinorNorm.eq_mul_sq Q hQ hσ2 hσ1
    have ht : s / Q y ≠ 0 := div_ne_zero hs hy
    have hQx : Q x = Q ((s / Q y) • y) := by
      rw [Q_smul]
      field_simp
      linear_combination hxy
    have hty : Q ((s / Q y) • y) ≠ 0 := by rw [← hQx]; exact hx
    have e1 : τ = symmetry Q x hx * symmetry Q ((s / Q y) • y) hty := by
      rw [h]
      simp only [symProd_cons, symProd_nil, mul_one]
      rw [symmetry_smul_vec Q ht hy hty]
    obtain ⟨ρ, hρ, hρ2⟩ := Om55.exists_sq_symmetry_mul Q hx hty hQx
    exact ⟨ρ, hρ, e1.trans hρ2⟩
  · simp at hlen

/-- **55:5, second part** (O'Meara 1963, 55:5, p. 140): for a regular $n$-ary space with $1 \le n \le 3$,
$(O^+_n)^2 = \Omega_n = O'_n$, where $(O^+_n)^2$ is the *set* of squares of rotations. The equality
$\Omega_n = O'_n$ is `omega_eq_orthPrime_of_finrank_le_three`; this theorem is $\Omega_n = (O^+_n)^2$.

*Update (simplification):* the book's proof goes through Corollary 43:5a and Remark 43:8 (binary and ternary
case analysis); the argument here ($\tau_x\tau_y = (\tau_x\tau_{x\pm y})^2$ when $Q(x) = Q(y)$) is uniform in
$n \le 3$, and the hypothesis $1 \le n$ is not needed (it is kept to match the book). -/
@[kb "omeara1963" "§55, 55:5, p. 140"]
theorem omega_eq_sq_orthPlus (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (_hn : 1 ≤ Module.finrank F V) (h3 : Module.finrank F V ≤ 3) :
    (omega Q : Set (V ≃ₗ[F] V)) = {τ | ∃ σ ∈ orthPlus Q, τ = σ ^ 2} := by
  ext τ
  constructor
  · exact exists_sq_of_mem_omega Q hQ h3
  · rintro ⟨σ, hσ, rfl⟩
    exact sq_mem_omega_of_mem_orthPlus Q hQ hσ

end Main

end QuadFormsKB.OMeara
