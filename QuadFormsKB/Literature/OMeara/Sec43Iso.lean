import QuadFormsKB.Literature.OMeara.Sec43E

/-!
# O'Meara §43E: isometries fixing all isotropic lines (43:10)

**Setting** (as in `Sec43E.lean`): $F$ a field with $2 \ne 0$, $(V, Q)$ a finite-dimensional regular quadratic space,
$B$ = `bil Q`, $O(V)$ = `orth Q`.

**Proves** (O'Meara 1973 printing, Chapter IV, §43E, p. 108):
* `eq_one_or_neg_of_forall_iso_line` (**43:10**): if $V$ is isotropic of dimension $n \ge 3$ and $\sigma \in O(V)$ leaves
  every isotropic line fixed, then $\sigma = \pm 1_V$.

**Proof notes.** As in the book, with $H = Fx + Fy$ a hyperbolic plane ($Q(x) = Q(y) = 0$, $B(x, y) = 1$) and
$W = H^\perp$: $\sigma x = \alpha x$, $\sigma y = \beta y$; for an anisotropic $z \in W$ the vectors $z \pm h$,
$h = x - \tfrac12 Q(z) y$, are isotropic, and comparing coefficients in the base $x, y, z$ gives
$\alpha = \beta$ and $\sigma z = \alpha z$. An isotropic $p \in W$ is $(p + cz) - cz$ with $c \in \{1, 2\}$ and
$p + cz$ anisotropic. Hence $\sigma = \alpha \cdot 1_V$ on $H + W = V$, and $\alpha\beta = 1$ gives $\alpha = \pm 1$.
O'Meara's appeal to 43:9 on $W$ and to Example 42:15 is replaced by this direct computation.
-/

open QuadraticMap Submodule Module LinearMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Sec43Iso

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)

/-- Key step of 43:10: for a hyperbolic pair $x, y$ with $\sigma x = \alpha x$, $\sigma y = \beta y$ and an
anisotropic $z \perp x, y$, we get $\beta = \alpha$ and $\sigma z = \alpha z$. -/
theorem iso_line_key {σ : V ≃ₗ[F] V} (h : ∀ v, v ≠ 0 → Q v = 0 → ∃ a : F, σ v = a • v)
    {x y z : V} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1) (hz : Q z ≠ 0) (hxz : bil Q x z = 0)
    (hyz : bil Q y z = 0) {α β : F} (hα : σ x = α • x) (hβ : σ y = β • y) :
    β = α ∧ σ z = α • z := by
  set hh := x - (Q z / 2) • y with hhdef
  have hQh : Q hh = -Q z := by
    rw [hhdef, sub_eq_add_neg, ← neg_smul, Q_add, Q_smul, hx, hy, bil_smul_right, hxy]
    linear_combination (-(Q z)) * iv_two_inv_mul_two (F := F)
  have hhz : bil Q hh z = 0 := by
    rw [hhdef, bil_sub_left, bil_smul_left, hxz, hyz]; ring
  have hQp : Q (z + hh) = 0 := by rw [Q_add, hQh, bil_comm, hhz]; ring
  have hQm : Q (z - hh) = 0 := by
    rw [sub_eq_add_neg, Q_add, QuadraticMap.map_neg, hQh, show bil Q z (-hh) = -bil Q z hh by simp [bil],
      bil_comm, hhz]; ring
  have hne : ∀ s : F, z + s • hh ≠ 0 := fun s h0 => by
    have := congrArg (bil Q z) h0
    rw [bil_add_right, bil_smul_right, bil_self, bil_comm, hhz, iv_bil_zero_right] at this
    exact hz (by simpa using this)
  obtain ⟨a, ha⟩ := h (z + hh) (by simpa using hne 1) hQp
  obtain ⟨b, hb⟩ := h (z - hh) (by simpa [sub_eq_add_neg] using hne (-1)) hQm
  have hσh : σ hh = α • x - (Q z / 2 * β) • y := by
    rw [hhdef, map_sub, map_smul, hα, hβ, smul_smul]
  rw [map_add, hσh] at ha
  rw [map_sub, hσh] at hb
  have hli : LinearIndependent F ![x, y, z] := by
    apply linearIndependent_of_det_gram_ne_zero (R := F) Q
    rw [Matrix.det_fin_three]
    simp [gram, hx, hy, hxy, hxz, hyz, bil_comm Q y x, bil_comm Q z x, bil_comm Q z y, hz]
  have key := (Fintype.linearIndependent_iff.1 hli) ![2 * α - (a + b), -(2 * (Q z / 2 * β)) + (a + b) * (Q z / 2), -(a - b)]
    (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rw [hhdef] at ha hb
      linear_combination (norm := module) ha - hb)
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, neg_eq_zero] at k0 k1 k2
  have hab : a = b := sub_eq_zero.1 k2
  subst hab
  have hαa : α = a := by
    have : (2 : F) * (α - a) = 0 := by linear_combination k0
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left iv_two_ne)
  subst hαa
  have hβα : β = α := by
    have : (Q z / 2) * (2 * (β - α)) = 0 := by linear_combination -k1
    have h' := (mul_eq_zero.1 this).resolve_left (div_ne_zero hz iv_two_ne)
    exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_left iv_two_ne)
  refine ⟨hβα, ?_⟩
  subst hβα
  rw [hhdef] at ha
  linear_combination (norm := module) ha

/-- **O'Meara 43:10** (p. 108). Let $V$ be a regular isotropic quadratic space of dimension $n \ge 3$ and let
$\sigma \in O(V)$ leave every isotropic line fixed ($\sigma v \in Fv$ whenever $v \ne 0$ and $Q(v) = 0$). Then
$\sigma = \pm 1_V$. -/
@[kb "omeara1963" "§43E, 43:10, p. 108"]
theorem eq_one_or_neg_of_forall_iso_line (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : 3 ≤ finrank F V) (hiso : ∃ x : V, x ≠ 0 ∧ Q x = 0) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q)
    (h : ∀ v, v ≠ 0 → Q v = 0 → ∃ a : F, σ v = a • v) : (∀ v, σ v = v) ∨ ∀ v, σ v = -v := by
  obtain ⟨x, hx0, hx⟩ := hiso
  obtain ⟨y, hy, hxy⟩ := exists_hyp_partner Q hQ hx0 hx
  have hy0 : y ≠ 0 := fun h0 => by rw [h0, iv_bil_zero_right] at hxy; exact one_ne_zero hxy.symm
  obtain ⟨α, hα⟩ := h x hx0 hx
  obtain ⟨β, hβ⟩ := h y hy0 hy
  obtain ⟨z0, hz0, hxz0, hyz0⟩ := exists_aniso_orth_pair Q hQ h3 hx hy hxy
  have hβα := (iso_line_key Q h hx hy hxy hz0 hxz0 hyz0 hα hβ).1
  rw [hβα] at hβ
  have hW : ∀ p, bil Q x p = 0 → bil Q y p = 0 → σ p = α • p := by
    intro p hxp hyp
    by_cases hp : Q p ≠ 0
    · exact (iso_line_key Q h hx hy hxy hp hxp hyp hα hβ).2
    push Not at hp
    have hQc : ∀ c : F, Q (p + c • z0) = 2 * c * bil Q p z0 + c ^ 2 * Q z0 := fun c => by
      rw [Q_add, hp, Q_smul, bil_smul_right]; ring
    obtain ⟨c, hc0, hc⟩ : ∃ c : F, c ≠ 0 ∧ Q (p + c • z0) ≠ 0 := by
      by_cases h1 : Q (p + (1 : F) • z0) = 0
      · refine ⟨2, iv_two_ne, ?_⟩
        rw [hQc] at h1 ⊢
        intro h2
        apply hz0
        have : (2 : F) * Q z0 = 0 := by linear_combination h2 - 2 * h1
        exact (mul_eq_zero.1 this).resolve_left iv_two_ne
      · exact ⟨1, one_ne_zero, h1⟩
    have hxq : bil Q x (p + c • z0) = 0 := by rw [bil_add_right, bil_smul_right, hxp, hxz0]; ring
    have hyq : bil Q y (p + c • z0) = 0 := by rw [bil_add_right, bil_smul_right, hyp, hyz0]; ring
    have hxc : bil Q x (c • z0) = 0 := by rw [bil_smul_right, hxz0, mul_zero]
    have hyc : bil Q y (c • z0) = 0 := by rw [bil_smul_right, hyz0, mul_zero]
    have hQcz : Q (c • z0) ≠ 0 := by rw [Q_smul]; exact mul_ne_zero (pow_ne_zero 2 hc0) hz0
    have e1 := (iso_line_key Q h hx hy hxy hc hxq hyq hα hβ).2
    have e2 := (iso_line_key Q h hx hy hxy hQcz hxc hyc hα hβ).2
    rw [map_add] at e1
    linear_combination (norm := module) e1 - e2
  have hαα : α * α = 1 := by
    have := iv_bil_orth Q hσ x y
    rw [hα, hβ, bil_smul_left, bil_smul_right, hxy] at this
    linear_combination this
  have hall : ∀ v, σ v = α • v := by
    intro v
    set p := v - bil Q v y • x - bil Q v x • y
    have hpx : bil Q x p = 0 := by
      simp only [p, bil_sub_right, bil_smul_right, bil_self, hx, hxy, bil_comm Q x v]; ring
    have hpy : bil Q y p = 0 := by
      simp only [p, bil_sub_right, bil_smul_right, bil_self, hy, bil_comm Q y x, hxy, bil_comm Q y v]; ring
    have hv : v = p + bil Q v y • x + bil Q v x • y := by simp only [p]; abel
    rw [hv, map_add, map_add, map_smul, map_smul, hW p hpx hpy, hα, hβ]
    module
  rcases mul_self_eq_one_iff.1 hαα with rfl | rfl
  · left; intro v; rw [hall, one_smul]
  · right; intro v; rw [hall, neg_one_smul]

end Sec43Iso

end QuadFormsKB.OMeara
