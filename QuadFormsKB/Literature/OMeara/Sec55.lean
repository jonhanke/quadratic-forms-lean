/-
# O'Meara §55 and §56: the spinor norm (55:1 to 55:7, and the remarks of pp. 137-141)

**Setting.** A field $F$ of characteristic $\ne 2$, a finite-dimensional quadratic space $(V, Q)$ over $F$, and
O'Meara's bilinear form $B$ = `bil Q` (so $B(x,x) = Q(x)$). *Regular* means
`(QuadraticMap.associated Q).Nondegenerate`. O'Meara's spinor norm $\theta(\sigma) = Q(u_1)\cdots Q(u_r)F^{\times 2}$ of
a rotation $\sigma = \tau_{u_1}\cdots\tau_{u_r}$ is expressed through the relation `HasSpinorNorm Q σ c`
("$\theta(\sigma) = cF^{\times 2}$ through some factorization", `Sec92Spinor.lean`); that this is independent of the
factorization is `HasSpinorNorm.eq_mul_sq` (`Sec54.lean`). The Cartan-Dieudonne theorem 43:3 is
`exists_symmetry_prod_eq_length_le` (`Sec43CD.lean`). Helper lemmas are in the namespace `Sp55`.

**Defines** $\Omega(V)$ (`omega`, §43D), $O'(V)$ (`orthPrime`, §55) and the spinor norm homomorphism
$\theta : O^+(V) \to F^\times/F^{\times 2}$ (`spinorNormHom`; the lemmas of `Lattices.SqClass` need an incidental
`CharZero` hypothesis, so copies valid over every field are in `Sp55`).

**Proves**
* API of `HasSpinorNorm`: `HasSpinorNorm.mul`, `HasSpinorNorm.inv`, `hasSpinorNorm_symmetry`,
  `HasSpinorNorm.of_eq_mul_sq`, `HasSpinorNorm.conj`, `mem_orthPrime_iff`, `orthPrime_subgroupOf_normal`;
* **55:1** (the hyperbolic plane): `hyperbolic_Q_sub_smul`, `hyperbolic_symmetry`, `hyperbolic_symmetry_form`,
  `hyperbolic_rotation`;
* **55:2a**: `exists_hasSpinorNorm_of_isotropic` ($\theta(O^+(V)) = F^\times$ for a regular isotropic space);
* **55:3**: `symProd_mul_inv_mem_omega`;
* **55:4** (implication form): `hasSpinorNorm_of_splitting`, `HasSpinorNorm.eq_mul_mul_sq_of_splitting`;
* **55:7**: `hasSpinorNorm_neg_one`, `neg_mem_orthPrime_iff`;
* scaling (p. 138): `orth_smul`, `orthPlus_smul`, `orthPrime_smul`;
* with Cartan-Dieudonne: `exists_hasSpinorNorm_of_mem_orth`, `omega_le_orthPrime` ($\Omega \subseteq O'$), normality of
  $\Omega$ and $O^+$ in $O$, `sq_mem_omega` ($\sigma^2 \in \Omega$, 43:6), **55:2** `exists_hasSpinorNorm_iff`,
  **55:4** (full) `exists_hasSpinorNorm_of_splitting`, **55:5** `omega_eq_orthPrime_of_finrank_le_three` and
  `sq_mem_omega_of_mem_orthPlus` (the inclusion $\Omega \subseteq (O^+)^2$ is `omega_eq_sq_orthPlus` in `Sec55Omega.lean`),
  **55:6** `omega_eq_orthPrime_of_subspace`, **55:6a** `omega_eq_orthPrime_of_isotropic`, `spinorNormHom`,
  `ker_spinorNormHom`, `spinorNormHom_surjective_of_isotropic`, `orthPlus_quotient_equiv_of_isotropic`;
* **§56** (p. 141): `neg_mem_omega_iff`, `omega_eq_orthPrime`, `spinorNormHom_range_of_finrank_le_three`,
  `orthPlus_quotient_equiv_range`.
-/
import QuadFormsKB.Literature.OMeara.Sec54
import QuadFormsKB.Witt.Extension
import QuadFormsKB.Literature.OMeara.Sec43CD
import QuadFormsKB.Lattices.SpinorNorm

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

open Cl54

/-! Helper lemmas live in the sub-namespace `Sp55` to keep names globally unique. -/
namespace Sp55

section Basic

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- `HasSpinorNorm` through the product `symProd` (without `attach`). -/
theorem hasSpinorNorm_iff {σ : V ≃ₗ[F] V} {c : F} :
    HasSpinorNorm Q σ c ↔ ∃ l : List V, ∃ hl : ∀ u ∈ l, Q u ≠ 0, σ = symProd Q l hl ∧
      ∃ s : F, s ≠ 0 ∧ (l.map Q).prod = c * s ^ 2 := by
  constructor
  · rintro ⟨l, hl, h1, h2⟩
    exact ⟨l, hl, by rw [← attach_prod_eq_symProd Q l hl]; exact h1, h2⟩
  · rintro ⟨l, hl, h1, h2⟩
    exact ⟨l, hl, by rw [attach_prod_eq_symProd Q l hl]; exact h1, h2⟩

theorem neg_one_ne_one_units : (-1 : Fˣ) ≠ 1 := by
  intro h
  have h2 : ((-1 : Fˣ) : F) = ((1 : Fˣ) : F) := congrArg Units.val h
  simp only [Units.val_neg, Units.val_one] at h2
  have : (2 : F) = 0 := by linear_combination -h2
  exact two_ne_zero this

theorem bil_orth {g : V ≃ₗ[F] V} (hg : g ∈ orth Q) (x y : V) : bil Q (g x) (g y) = bil Q x y := by
  have h := hg (x + y)
  rw [map_add, Q_add, Q_add, hg x, hg y] at h
  have h4 : (2 : F) * bil Q (g x) (g y) = 2 * bil Q x y := by linear_combination h
  exact mul_left_cancel₀ two_ne_zero h4

/-- **Conjugation of a symmetry:** $\sigma\tau_u\sigma^{-1} = \tau_{\sigma u}$ for an isometry $\sigma$. -/
theorem conj_symmetry {g : V ≃ₗ[F] V} (hg : g ∈ orth Q) {u : V} (hu : Q u ≠ 0) :
    g * symmetry Q u hu * g⁻¹ = symmetry Q (g u) (by rw [hg u]; exact hu) := by
  ext x
  have h1 : g (g⁻¹ x) = x := g.apply_symm_apply x
  have h2 : bil Q (g⁻¹ x) u = bil Q x (g u) := by
    rw [← bil_orth Q hg (g⁻¹ x) u, h1]
  simp only [LinearEquiv.mul_apply, symmetry_apply, map_sub, map_smul]
  rw [h1, h2, hg u]

theorem conj_symProd {g : V ≃ₗ[F] V} (hg : g ∈ orth Q) (l : List V) (hl : ∀ u ∈ l, Q u ≠ 0)
    (hl' : ∀ u ∈ l.map g, Q u ≠ 0) :
    g * symProd Q l hl * g⁻¹ = symProd Q (l.map g) hl' := by
  induction l with
  | nil => simp [symProd]
  | cons x l ih =>
    have hx := hl x List.mem_cons_self
    have hl2 : ∀ u ∈ l, Q u ≠ 0 := fun u hu => hl u (List.mem_cons_of_mem x hu)
    have hl2' : ∀ u ∈ l.map g, Q u ≠ 0 := fun u hu => hl' u (List.mem_cons_of_mem (g x) hu)
    have e1 : g * symProd Q (x :: l) hl * g⁻¹ =
        (g * symmetry Q x hx * g⁻¹) * (g * symProd Q l hl2 * g⁻¹) := by
      rw [symProd_cons Q hl]; group
    rw [e1, conj_symmetry Q hg hx, ih hl2 hl2']
    exact (symProd_cons Q (x := g x) (l := l.map g) hl').symm

/-- Witt's theorem in the form of transitivity: for a regular space, isometries act transitively on vectors of
the same nonzero value. -/
theorem exists_orth_apply_eq (hQ : (QuadraticMap.associated Q).Nondegenerate) {a b : V}
    (hab : Q a = Q b) (hb : Q b ≠ 0) : ∃ g ∈ orth Q, g b = a := by
  have hpol : (QuadraticMap.polarBilin Q).Nondegenerate :=
    (QuadraticMap.nondegenerate_polar_iff).mpr ((QuadraticMap.nondegenerate_associated_iff).mp hQ)
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_apply_eq_of_nondegenerate Q hpol hb
    (v := b) (w := a) rfl hab
  exact ⟨ρ.toLinearEquiv, fun x => ρ.map_app x, hρ⟩

theorem det_symProd (l : List V) (hl : ∀ u ∈ l, Q u ≠ 0) :
    LinearEquiv.det (symProd Q l hl) = (-1) ^ l.length := by
  induction l with
  | nil => simp [symProd]
  | cons x l ih =>
    have hl2 : ∀ u ∈ l, Q u ≠ 0 := fun u hu => hl u (List.mem_cons_of_mem x hu)
    rw [symProd_cons Q hl, map_mul, det_symmetry, ih hl2, List.length_cons, pow_succ]
    group

end Basic

end Sp55

open Sp55

section Defs

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **$\Omega(V)$** (O'Meara 1963, §43D, p. 106): the commutator subgroup of the orthogonal group $O(V)$. -/
@[kb "omeara1963" "§43D, p. 106 (Ω_n, the commutator subgroup of O_n)"]
def omega : Subgroup (V ≃ₗ[F] V) := ⁅orth Q, orth Q⁆

/-- **A spinor norm is nonzero:** if $\sigma$ has spinor norm $cF^{\times 2}$ then $c \ne 0$. -/
theorem HasSpinorNorm.ne_zero {σ : V ≃ₗ[F] V} {c : F} (h : HasSpinorNorm Q σ c) : c ≠ 0 := by
  obtain ⟨l, hl, -, s, hs, hp⟩ := h
  intro h0
  have : (l.map Q).prod ≠ 0 := List.prod_ne_zero (by
    simp only [List.mem_map]
    rintro ⟨u, hu, h0⟩
    exact hl u hu h0)
  rw [hp, h0] at this
  simp at this

/-- The identity has spinor norm $1$ (the empty product). -/
theorem HasSpinorNorm.one : HasSpinorNorm Q (1 : V ≃ₗ[F] V) 1 :=
  ⟨[], by simp, by simp, 1, one_ne_zero, by simp⟩

/-- **The spinor norm is multiplicative** (O'Meara 1963, §55, p. 137): if $\sigma$ has spinor norm $c$ and $\tau$
has spinor norm $d$ then $\sigma\tau$ has spinor norm $cd$ (concatenate the factorizations). -/
@[kb "omeara1963" "§55, p. 137 (θ(στ) = θ(σ)θ(τ))"]
theorem HasSpinorNorm.mul {σ τ : V ≃ₗ[F] V} {c d : F} (hσ : HasSpinorNorm Q σ c)
    (hτ : HasSpinorNorm Q τ d) : HasSpinorNorm Q (σ * τ) (c * d) := by
  rw [hasSpinorNorm_iff] at hσ hτ ⊢
  obtain ⟨l, hl, rfl, s, hs, hp⟩ := hσ
  obtain ⟨l', hl', rfl, s', hs', hp'⟩ := hτ
  refine ⟨l ++ l', fun u hu => ?_, ?_, s * s', mul_ne_zero hs hs', ?_⟩
  · rcases List.mem_append.mp hu with h | h
    exacts [hl u h, hl' u h]
  · rw [symProd_append]
  · rw [List.map_append, List.prod_append, hp, hp']; ring

/-- **The spinor norm of an inverse** (O'Meara 1963, §55, p. 137): $\sigma^{-1}$ has the spinor norm of $\sigma$
(reverse the factorization). -/
@[kb "omeara1963" "§55, p. 137 (θ(σ⁻¹) = θ(σ))"]
theorem HasSpinorNorm.inv {σ : V ≃ₗ[F] V} {c : F} (h : HasSpinorNorm Q σ c) :
    HasSpinorNorm Q σ⁻¹ c := by
  rw [hasSpinorNorm_iff] at h ⊢
  obtain ⟨l, hl, rfl, s, hs, hp⟩ := h
  refine ⟨l.reverse, fun u hu => hl u (List.mem_reverse.mp hu),
    inv_eq_of_mul_eq_one_right (symProd_reverse_right Q l hl), s, hs, ?_⟩
  rw [List.map_reverse, List.prod_reverse, hp]

/-- **The spinor norm of a symmetry** (O'Meara 1963, §55, p. 137): $\tau_u$ has spinor norm $Q(u)F^{\times 2}$. -/
@[kb "omeara1963" "§55, p. 137 (θ(τ_u) = Q(u)F²)"]
theorem hasSpinorNorm_symmetry {u : V} (hu : Q u ≠ 0) : HasSpinorNorm Q (symmetry Q u hu) (Q u) := by
  rw [hasSpinorNorm_iff]
  refine ⟨[u], fun v hv => by rw [List.mem_singleton.mp hv]; exact hu, ?_, 1, one_ne_zero, by simp⟩
  simp [symProd]

/-- A spinor norm may be changed by a nonzero square. -/
theorem HasSpinorNorm.of_eq_mul_sq {σ : V ≃ₗ[F] V} {c d s : F} (h : HasSpinorNorm Q σ c) (hs : s ≠ 0)
    (hd : d = c * s ^ 2) : HasSpinorNorm Q σ d := by
  obtain ⟨l, hl, hσ, t, ht, hp⟩ := h
  refine ⟨l, hl, hσ, t / s, div_ne_zero ht hs, ?_⟩
  rw [hp, hd]; field_simp

/-- **Conjugation preserves the spinor norm:** if $\sigma$ has spinor norm $c$ and $g \in O(V)$ then
$g\sigma g^{-1}$ has spinor norm $c$ (since $g\tau_u g^{-1} = \tau_{gu}$ and $Q(gu) = Q(u)$). -/
theorem HasSpinorNorm.conj {g : V ≃ₗ[F] V} (hg : g ∈ orth Q) {σ : V ≃ₗ[F] V} {c : F}
    (h : HasSpinorNorm Q σ c) : HasSpinorNorm Q (g * σ * g⁻¹) c := by
  rw [hasSpinorNorm_iff] at h ⊢
  obtain ⟨l, hl, rfl, s, hs, hp⟩ := h
  have hl' : ∀ u ∈ l.map g, Q u ≠ 0 := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    rw [hg v]; exact hl v hv
  refine ⟨l.map g, hl', conj_symProd Q hg l hl hl', s, hs, ?_⟩
  rw [← hp, List.map_map]
  congr 1
  exact List.map_congr_left fun v _ => hg v

/-- **$O'(V)$** (O'Meara 1963, §55, p. 137): $O'(V) = \{\sigma \in O^+(V) \mid \theta(\sigma) = 1\}$, the kernel of
the spinor norm on the rotations. Here $\theta(\sigma) = 1$ is `HasSpinorNorm Q σ 1` (through a factorization
$\sigma = \tau_{u_1}\cdots\tau_{u_r}$ with $Q(u_1)\cdots Q(u_r)$ a nonzero square); by `HasSpinorNorm.eq_mul_sq` for
a regular space every factorization of $\sigma \in O'(V)$ then has square product. -/
@[kb "omeara1963" "§55, p. 137 (O'_n(V), the kernel of the spinor norm on O⁺_n)"]
def orthPrime : Subgroup (V ≃ₗ[F] V) where
  carrier := {σ | σ ∈ orthPlus Q ∧ HasSpinorNorm Q σ 1}
  mul_mem' := fun {a b} ha hb =>
    ⟨(orthPlus Q).mul_mem ha.1 hb.1, by
      have := HasSpinorNorm.mul Q ha.2 hb.2
      rwa [mul_one] at this⟩
  one_mem' := ⟨(orthPlus Q).one_mem, HasSpinorNorm.one Q⟩
  inv_mem' := fun {a} ha => ⟨(orthPlus Q).inv_mem ha.1, HasSpinorNorm.inv Q ha.2⟩

theorem orthPrime_le_orthPlus : orthPrime Q ≤ orthPlus Q := fun _ h => h.1

/-- **Membership in $O'(V)$** for a regular space (O'Meara 1963, §55, p. 137): a rotation $\sigma$ that has some
spinor norm lies in $O'(V)$ if and only if every spinor norm of $\sigma$ is a square. -/
theorem mem_orthPrime_iff (hQ : (QuadraticMap.associated Q).Nondegenerate) {σ : V ≃ₗ[F] V}
    (hσ : ∃ c, HasSpinorNorm Q σ c) :
    σ ∈ orthPrime Q ↔ σ ∈ orthPlus Q ∧ ∀ c, HasSpinorNorm Q σ c → IsSquare c := by
  constructor
  · rintro ⟨hp, h1⟩
    refine ⟨hp, fun c hc => ?_⟩
    obtain ⟨s, -, hs⟩ := HasSpinorNorm.eq_mul_sq Q hQ hc h1
    exact ⟨s, by rw [hs]; ring⟩
  · rintro ⟨hp, hall⟩
    obtain ⟨c, hc⟩ := hσ
    obtain ⟨r, hr⟩ := hall c hc
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact HasSpinorNorm.ne_zero Q hc (by simpa using hr)
    exact ⟨hp, HasSpinorNorm.of_eq_mul_sq Q hc (inv_ne_zero hr0) (by rw [hr]; field_simp)⟩

/-- **$O'(V)$ is normal in $O(V)$** (O'Meara 1963, §55, p. 138): the subgroup $O'(V)$ of $O(V)$ is normal in
$O(V)$. -/
@[kb "omeara1963" "§55, p. 138 (O'_n is a normal subgroup of O_n)"]
theorem orthPrime_subgroupOf_normal : ((orthPrime Q).subgroupOf (orth Q)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hn
  have hg : (g : V ≃ₗ[F] V) ∈ orth Q := g.2
  have hn1' : (n : V ≃ₗ[F] V) ∈ orth Q := hn1
  refine ⟨⟨(orth Q).mul_mem ((orth Q).mul_mem hg hn1') ((orth Q).inv_mem hg), ?_⟩, ?_⟩
  · have hn2' : LinearEquiv.det (n : V ≃ₗ[F] V) = 1 := hn2
    show LinearEquiv.det ((g : V ≃ₗ[F] V) * (n : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V)⁻¹) = 1
    simp [hn2']
  · exact HasSpinorNorm.conj Q hg hn3

end Defs

/-! ### 55:1 and 55:2a: the hyperbolic plane -/

section Hyperbolic

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) {x y : V}

/-- **55:1, the value** (O'Meara 1963, 55:1, p. 138): for $x, y$ with $Q(x) = Q(y) = 0$ and $B(x,y) = 1$ (a hyperbolic
pair, as in the hyperbolic plane $H = Fx + Fy$ of 42:15) and $a \in F$, $Q(x - ay) = -2a$.

*Reconstruction:* the machine-read text of the matrix of $H$ is garbled; the hypotheses are reconstructed from the
book's value $Q(x - ay) = -2a$. -/
@[kb "omeara1963" "§55, 55:1, p. 138 (Q(x − ay) = −2a in the hyperbolic plane)"]
theorem hyperbolic_Q_sub_smul (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1) (a : F) :
    Q (x - a • y) = -2 * a := by
  rw [sub_eq_add_neg, ← neg_smul, Q_add, Q_smul, bil_smul_right, hxy, hy, hx]
  ring

theorem hyperbolic_Q_ne_zero (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1) {a : F} (ha : a ≠ 0) :
    Q (x - a • y) ≠ 0 := by
  rw [hyperbolic_Q_sub_smul Q hx hy hxy]
  exact mul_ne_zero (neg_ne_zero.mpr two_ne_zero) ha

/-- **55:1, the symmetry** (O'Meara 1963, 55:1, p. 138): for a hyperbolic pair $x, y$ and $a \ne 0$, the symmetry
$\tau = \tau_u$ with $u = x - ay$ satisfies $\tau x = ay$ and $\tau y = a^{-1}x$, and has spinor norm $-2a$. -/
@[kb "omeara1963" "§55, 55:1, p. 138 (τ_{x−ay}: x ↦ ay, y ↦ a⁻¹x, θ = −2a)"]
theorem hyperbolic_symmetry (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1) {a : F} (ha : a ≠ 0)
    {u : V} (hu : u = x - a • y) (h : Q u ≠ 0) :
    symmetry Q u h x = a • y ∧ symmetry Q u h y = a⁻¹ • x ∧ HasSpinorNorm Q (symmetry Q u h) (-2 * a) := by
  have hQu : Q u = -2 * a := by rw [hu]; exact hyperbolic_Q_sub_smul Q hx hy hxy a
  have hbx : bil Q x u = -a := by
    rw [hu, bil_sub_right, bil_smul_right, hxy, bil_self, hx]; ring
  have hby : bil Q y u = 1 := by
    rw [hu, bil_sub_right, bil_smul_right, bil_comm Q y x, hxy, bil_self, hy]; ring
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · rw [symmetry_apply, hbx, hQu]
    have : 2 * -a / (-2 * a) = 1 := by field_simp
    rw [this, one_smul, hu, sub_sub_cancel]
  · rw [symmetry_apply, hby, hQu]
    have : 2 * 1 / (-2 * a) = -a⁻¹ := by field_simp
    rw [this, hu, neg_smul, sub_neg_eq_add, smul_sub, smul_smul, inv_mul_cancel₀ ha, one_smul]
    abel
  · have := hasSpinorNorm_symmetry Q h
    rwa [hQu] at this

/-- **55:1, the rotation** (O'Meara 1963, 55:1, p. 139): for a hyperbolic pair $x, y$ and $a \ne 0$, the rotation
$\sigma = \tau_{x-y}\tau_{x-ay}$ satisfies $\sigma x = ax$ and $\sigma y = a^{-1}y$ and has spinor norm $a$
(since $(-2)(-2a) = a \cdot 2^2$).

*Reconstruction:* the printed equations are "$\sigma x = ax$, $\sigma y = ay$"; the second is $\sigma y = a^{-1}y$,
as $\det\sigma = 1$ forces. -/
@[kb "omeara1963" "§55, 55:1, p. 139 (σ = τ_{x−y}τ_{x−ay}: x ↦ ax, y ↦ a⁻¹y, θ(σ) = a)"]
theorem hyperbolic_rotation (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1) {a : F} (ha : a ≠ 0)
    {u v : V} (hu : u = x - y) (hv : v = x - a • y) (hu0 : Q u ≠ 0) (hv0 : Q v ≠ 0) :
    symmetry Q u hu0 * symmetry Q v hv0 ∈ orthPlus Q ∧
      (symmetry Q u hu0 * symmetry Q v hv0) x = a • x ∧
      (symmetry Q u hu0 * symmetry Q v hv0) y = a⁻¹ • y ∧
      HasSpinorNorm Q (symmetry Q u hu0 * symmetry Q v hv0) a := by
  obtain ⟨hv1, hv2, hv3⟩ := hyperbolic_symmetry Q hx hy hxy ha hv hv0
  obtain ⟨hu1, hu2, hu3⟩ := hyperbolic_symmetry Q hx hy hxy one_ne_zero (by rw [hu, one_smul]) hu0
  refine ⟨symmetry_mul_mem_orthPlus Q hu0 hv0, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hv1, map_smul, hu2]; simp
  · rw [LinearEquiv.mul_apply, hv2, map_smul, hu1]; simp
  · refine HasSpinorNorm.of_eq_mul_sq Q (HasSpinorNorm.mul Q hu3 hv3) (inv_ne_zero two_ne_zero) ?_
    field_simp

/-- **55:1, the first claim** (O'Meara 1963, 55:1, p. 138): if $V = Fx + Fy$ with $x, y$ a hyperbolic pair, every
symmetry $\tau_u$ of $V$ has the form $\tau x = ay$, $\tau y = a^{-1}x$ for some $a \in F^\times$ (it interchanges the
two isotropic lines). (The hypothesis is that $x, y$ span $V$, which for a hyperbolic pair means $\dim V = 2$.) -/
@[kb "omeara1963" "§55, 55:1, p. 138 (every symmetry of H has τx = ay, τy = a⁻¹x)"]
theorem hyperbolic_symmetry_form (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1)
    (hspan : Submodule.span F {x, y} = ⊤) {u : V} (hu : Q u ≠ 0) :
    ∃ a : F, a ≠ 0 ∧ symmetry Q u hu x = a • y ∧ symmetry Q u hu y = a⁻¹ • x := by
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp (hspan ▸ Submodule.mem_top (x := u))
  have hbx : bil Q x u = q := by
    rw [← hpq, bil_add_right, bil_smul_right, bil_smul_right, bil_self, hx, hxy]; ring
  have hby : bil Q y u = p := by
    rw [← hpq, bil_add_right, bil_smul_right, bil_smul_right, bil_self, hy, bil_comm Q y x, hxy]; ring
  have hQu : Q u = 2 * p * q := by
    rw [← hpq, Q_add, Q_smul, Q_smul, bil_smul_left, bil_smul_right, hxy, hx, hy]; ring
  have hp : p ≠ 0 := by
    rintro rfl
    apply hu
    rw [hQu]; ring
  have hq : q ≠ 0 := by
    rintro rfl
    apply hu
    rw [hQu]; ring
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  refine ⟨-q / p, div_ne_zero (neg_ne_zero.mpr hq) hp, ?_, ?_⟩
  · have e : 2 * q / (2 * p * q) = p⁻¹ := by field_simp
    rw [symmetry_apply, hbx, hQu, e, ← hpq, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hp, one_smul,
      sub_add_cancel_left, ← neg_smul]
    congr 1
    field_simp
  · have e : 2 * p / (2 * p * q) = q⁻¹ := by field_simp
    rw [symmetry_apply, hby, hQu, e, ← hpq, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hq, one_smul,
      sub_add_cancel_right, ← neg_smul]
    congr 1
    field_simp

/-- A regular isotropic space contains a hyperbolic pair. -/
theorem exists_hyperbolic_pair (hQ : (QuadraticMap.associated Q).Nondegenerate) {x : V} (hx0 : x ≠ 0)
    (hx : Q x = 0) : ∃ y : V, Q y = 0 ∧ bil Q x y = 1 := by
  have hz : ∃ z, bil Q x z ≠ 0 := by
    by_contra hcon
    exact hx0 (hQ.1 x fun z => by_contra fun h => hcon ⟨z, h⟩)
  obtain ⟨z, hz⟩ := hz
  obtain ⟨w, hxw⟩ : ∃ w : V, bil Q x w = 1 :=
    ⟨(bil Q x z)⁻¹ • z, by rw [bil_smul_right, inv_mul_cancel₀ hz]⟩
  refine ⟨w - (Q w / 2) • x, ?_, ?_⟩
  · rw [sub_eq_add_neg, ← neg_smul, Q_add, Q_smul, bil_smul_right, bil_comm Q w x, hxw, hx]
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    field_simp
    ring
  · rw [bil_sub_right, bil_smul_right, bil_self, hx, hxw]; ring

/-- **55:2a** (O'Meara 1963, 55:2a, p. 139): if $V$ is a regular isotropic quadratic space then
$\theta(O^+(V)) = F^\times$: for every $c \in F^\times$ there is a rotation with spinor norm $c F^{\times 2}$. (Every
spinor norm is nonzero by `HasSpinorNorm.ne_zero`.) -/
@[kb "omeara1963" "§55, 55:2a, p. 139 (θ(O⁺) = F^× for isotropic V)"]
theorem exists_hasSpinorNorm_of_isotropic (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hiso : ∃ x : V, x ≠ 0 ∧ Q x = 0) {c : F} (hc : c ≠ 0) :
    ∃ σ ∈ orthPlus Q, HasSpinorNorm Q σ c := by
  obtain ⟨x, hx0, hx⟩ := hiso
  obtain ⟨y, hy, hxy⟩ := exists_hyperbolic_pair Q hQ hx0 hx
  have h1 : Q (x - y) ≠ 0 := by
    have := hyperbolic_Q_ne_zero Q hx hy hxy (one_ne_zero (α := F))
    rwa [one_smul] at this
  have h2 := hyperbolic_Q_ne_zero Q hx hy hxy hc
  obtain ⟨hmem, -, -, hsp⟩ := hyperbolic_rotation Q hx hy hxy hc (u := x - y) (v := x - c • y) rfl rfl h1 h2
  exact ⟨_, hmem, hsp⟩

end Hyperbolic

/-! ### 55:3: symmetries with permuted norms agree modulo $\Omega$ -/

section OmegaSection

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

namespace Sp55

open scoped Classical in
/-- The symmetry $\tau_u$ as an element of $O(V)$ (and the identity for isotropic $u$): a total version used to
form products in the abelianization. -/
def tauHat (u : V) : orth Q := if h : Q u ≠ 0 then ⟨symmetry Q u h, symmetry_mem_orth Q h⟩ else 1

theorem coe_tauHat {u : V} (h : Q u ≠ 0) : ((tauHat Q u : orth Q) : V ≃ₗ[F] V) = symmetry Q u h := by
  simp [tauHat, h]

theorem coe_prod_tauHat (l : List V) (hl : ∀ u ∈ l, Q u ≠ 0) :
    (((l.map (tauHat Q)).prod : orth Q) : V ≃ₗ[F] V) = symProd Q l hl := by
  induction l with
  | nil => simp [symProd]
  | cons x l ih =>
    have hx := hl x List.mem_cons_self
    have hl2 : ∀ u ∈ l, Q u ≠ 0 := fun u hu => hl u (List.mem_cons_of_mem x hu)
    rw [List.map_cons, List.prod_cons, Subgroup.coe_mul, coe_tauHat Q hx, ih hl2, symProd_cons Q hl]

theorem omega_eq_map : omega Q = (commutator (orth Q)).map (orth Q).subtype := by
  unfold omega
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem mem_omega_of_of_eq {a b : orth Q} (h : Abelianization.of a = Abelianization.of b) :
    (a : V ≃ₗ[F] V) * (b : V ≃ₗ[F] V)⁻¹ ∈ omega Q := by
  rw [omega_eq_map]
  refine ⟨a * b⁻¹, ?_, rfl⟩
  have : a * b⁻¹ ∈ (Abelianization.of : orth Q →* Abelianization (orth Q)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  rwa [Abelianization.ker_of] at this

theorem of_tauHat_eq (hQ : (QuadraticMap.associated Q).Nondegenerate) {a b : V} (hab : Q a = Q b) :
    Abelianization.of (tauHat Q a) = Abelianization.of (tauHat Q b) := by
  by_cases hb : Q b = 0
  · have ha : Q a = 0 := hab.trans hb
    simp [tauHat, ha, hb]
  · obtain ⟨g, hg, hga⟩ := exists_orth_apply_eq Q hQ hab hb
    have ha : Q a ≠ 0 := by rw [hab]; exact hb
    have key : tauHat Q a = (⟨g, hg⟩ : orth Q) * tauHat Q b * (⟨g, hg⟩ : orth Q)⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_tauHat Q ha, coe_tauHat Q hb, Subgroup.coe_inv]
      have := conj_symmetry Q hg hb
      simp only [hga] at this
      exact this.symm
    rw [key, map_mul, map_mul, map_inv, mul_comm (Abelianization.of _) (Abelianization.of (tauHat Q b)),
      mul_assoc, mul_inv_cancel, mul_one]

theorem of_prod_tauHat_eq (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    ∀ (u w : List V), u.map Q = w.map Q →
      Abelianization.of (u.map (tauHat Q)).prod = Abelianization.of (w.map (tauHat Q)).prod
  | [], w, h => by
    have : w = [] := (List.map_eq_nil_iff.mp h.symm)
    simp [this]
  | a :: u, [], h => by simp at h
  | a :: u, b :: w, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.map_cons, List.prod_cons, map_mul]
    rw [of_prod_tauHat_eq hQ u w h.2, of_tauHat_eq Q hQ h.1]

open scoped Classical in
theorem exists_perm_map_eq : ∀ (p : List F) (v : List V), p.Perm (v.map Q) →
    ∃ w : List V, w.Perm v ∧ w.map Q = p
  | [], v, h => ⟨[], by
      have : v = [] := List.map_eq_nil_iff.mp h.symm.eq_nil
      rw [this], rfl⟩
  | a :: p, v, h => by
    have ha : a ∈ v.map Q := h.subset List.mem_cons_self
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    have hp : (x :: v.erase x).Perm v := (List.perm_cons_erase hx).symm
    have h' : (Q x :: p).Perm (Q x :: (v.erase x).map Q) := by
      have := h.trans (hp.symm.map Q)
      simpa using this
    obtain ⟨w', hw', hw'Q⟩ := exists_perm_map_eq p (v.erase x) (List.Perm.cons_inv h')
    exact ⟨x :: w', (hw'.cons x).trans hp, by simp [hw'Q]⟩

end Sp55

/-- **55:3** (O'Meara 1963, 55:3, p. 139): let $u_1, \dots, u_r$ and $v_1, \dots, v_r$ be anisotropic vectors in a
regular quadratic space, and suppose that $(Q(u_1), \dots, Q(u_r))$ is a permutation of
$(Q(v_1), \dots, Q(v_r))$ (`List.Perm`). Then $\tau_{u_1}\cdots\tau_{u_r}\,(\tau_{v_1}\cdots\tau_{v_r})^{-1} \in
\Omega(V)$.

(The proof differs slightly from the book: in the abelianization of $O(V)$ one has $\bar\tau_u = \bar\tau_w$ whenever
$Q(u) = Q(w)$, since $\tau_u = \sigma\tau_w\sigma^{-1}$ for an isometry $\sigma w = u$ (Witt).) -/
@[kb "omeara1963" "§55, 55:3, p. 139 (permuted norms give the same product of symmetries mod Ω)"]
theorem symProd_mul_inv_mem_omega (hQ : (QuadraticMap.associated Q).Nondegenerate) {u v : List V}
    (hu : ∀ x ∈ u, Q x ≠ 0) (hv : ∀ x ∈ v, Q x ≠ 0) (h : (u.map Q).Perm (v.map Q)) :
    symProd Q u hu * (symProd Q v hv)⁻¹ ∈ omega Q := by
  obtain ⟨w, hwv, hwQ⟩ := exists_perm_map_eq Q _ v h
  have h1 := of_prod_tauHat_eq Q hQ u w hwQ.symm
  have h2 : Abelianization.of (w.map (tauHat Q)).prod = Abelianization.of (v.map (tauHat Q)).prod := by
    rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
    exact (hwv.map _).prod_eq
  have := mem_omega_of_of_eq Q (h1.trans h2)
  rwa [coe_prod_tauHat Q u hu, coe_prod_tauHat Q v hv] at this

end OmegaSection

/-! ### 55:4: orthogonal splittings -/

section Splitting

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

namespace Sp55

/-- The bilinear form of the restriction of $Q$ to a subspace is the restriction of the bilinear form. -/
theorem bil_comp_subtype (S : Submodule F V) (a b : S) :
    bil (Q.comp S.subtype) a b = bil Q (a : V) (b : V) := by
  apply mul_left_cancel₀ (two_ne_zero (α := F))
  rw [← polar_eq_two_mul_bil, ← polar_eq_two_mul_bil]
  rfl

/-- The symmetry of $V$ in a vector $u$ of a subspace $S$, restricted to $S$, is the symmetry of $S$ in $u$;
and it fixes every vector orthogonal to $u$. -/
theorem symmetry_coe_add (S : Submodule F V) (u : S) (hu : (Q.comp S.subtype) u ≠ 0) (a : S) (b : V)
    (hb : ∀ s : S, bil Q b s = 0) :
    symmetry Q (u : V) hu ((a : V) + b) = ((symmetry (Q.comp S.subtype) u hu a : S) : V) + b := by
  have hu' : Q (u : V) ≠ 0 := hu
  have hQu : (Q.comp S.subtype) u = Q (u : V) := rfl
  rw [symmetry_apply Q hu', bil_add_left, hb u, add_zero, symmetry_apply (Q.comp S.subtype) hu a]
  simp only [Submodule.coe_sub, Submodule.coe_smul, bil_comp_subtype, hQu]
  abel

theorem ne_zero_map_coe (S : Submodule F V) (l : List S) (hl : ∀ u ∈ l, (Q.comp S.subtype) u ≠ 0) :
    ∀ u ∈ l.map (fun s : S => (s : V)), Q u ≠ 0 := by
  intro u hu
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hu
  exact hl s hs

theorem symProd_map_coe_add (S : Submodule F V) (l : List S) (hl : ∀ u ∈ l, (Q.comp S.subtype) u ≠ 0)
    (a : S) (b : V) (hb : ∀ s : S, bil Q b s = 0) :
    symProd Q (l.map (fun s : S => (s : V))) (ne_zero_map_coe Q S l hl) ((a : V) + b) =
      ((symProd (Q.comp S.subtype) l hl a : S) : V) + b := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    have hl2 : ∀ u ∈ l, (Q.comp S.subtype) u ≠ 0 := fun u hu => hl u (List.mem_cons_of_mem x hu)
    have e1 : symProd Q (List.map (fun s : S => (s : V)) (x :: l)) (ne_zero_map_coe Q S (x :: l) hl) =
        symmetry Q (x : V) (hl x List.mem_cons_self) *
          symProd Q (l.map (fun s : S => (s : V))) (ne_zero_map_coe Q S l hl2) :=
      symProd_cons Q (ne_zero_map_coe Q S (x :: l) hl)
    have e2 := symProd_cons (Q.comp S.subtype) hl
    rw [e1, LinearEquiv.mul_apply, ih hl2, symmetry_coe_add Q S x (hl x List.mem_cons_self) _ b hb,
      e2, LinearEquiv.mul_apply]

end Sp55

/-- **55:4** (O'Meara 1963, 55:4, p. 139): let $V = U \perp W$ be an orthogonal splitting of a quadratic space and
$\sigma \in O(V)$ with $\sigma|_U = \tau \in O(U)$ and $\sigma|_W = \rho \in O(W)$ (the splitting
$\sigma = \tau \perp \rho$). If $\tau$ has spinor norm $c$ (on $U$) and $\rho$ has spinor norm $d$ (on $W$) then
$\sigma$ has spinor norm $cd$: $\theta(\sigma) = \theta(\tau)\theta(\rho)$.

This is the implication form (in terms of `HasSpinorNorm`); together with the well definedness
`HasSpinorNorm.eq_mul_sq` it is the book's equality of spinor norms (`HasSpinorNorm.eq_mul_mul_sq_of_splitting`).
*Update (generalization):* regularity of $V$ is not needed for this implication. -/
@[kb "omeara1963" "§55, 55:4, p. 139 (θ(τ ⊥ ρ) = θ(τ)θ(ρ))"]
theorem hasSpinorNorm_of_splitting {U W : Submodule F V} (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, bil Q u w = 0) {τ : U ≃ₗ[F] U} {ρ : W ≃ₗ[F] W} {σ : V ≃ₗ[F] V}
    (hστ : ∀ u : U, σ (u : V) = ((τ u : U) : V)) (hσρ : ∀ w : W, σ (w : V) = ((ρ w : W) : V))
    {c d : F} (hτ : HasSpinorNorm (Q.comp U.subtype) τ c) (hρ : HasSpinorNorm (Q.comp W.subtype) ρ d) :
    HasSpinorNorm Q σ (c * d) := by
  rw [hasSpinorNorm_iff] at hτ hρ ⊢
  obtain ⟨lU, hlU, rfl, s, hs, hp⟩ := hτ
  obtain ⟨lW, hlW, rfl, t, ht, hq⟩ := hρ
  have hU' := Sp55.ne_zero_map_coe Q U lU hlU
  have hW' := Sp55.ne_zero_map_coe Q W lW hlW
  have hL : ∀ u ∈ lU.map (fun s : U => (s : V)) ++ lW.map (fun s : W => (s : V)), Q u ≠ 0 := by
    intro u hu
    rcases List.mem_append.mp hu with h | h
    exacts [hU' u h, hW' u h]
  refine ⟨_, hL, ?_, s * t, mul_ne_zero hs ht, ?_⟩
  · ext v
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (by rw [hUW.sup_eq_top]; trivial : v ∈ U ⊔ W)
    have hW0 : ∀ w : W, bil Q a (w : V) = 0 := fun w => horth a ha w w.2
    have hU0 : ∀ u : U, ∀ w : W, bil Q (w : V) (u : V) = 0 := fun u w => by
      rw [bil_comm]; exact horth u u.2 w w.2
    rw [symProd_append, LinearEquiv.mul_apply, add_comm (a : V) b]
    have h1 := Sp55.symProd_map_coe_add Q W lW hlW ⟨b, hb⟩ a hW0
    simp only at h1
    rw [h1]
    have h3 : ∀ x : V, x + a = a + x := fun x => add_comm x a
    rw [h3 ((symProd (Q.comp W.subtype) lW hlW ⟨b, hb⟩ : W) : V)]
    have h2 := Sp55.symProd_map_coe_add Q U lU hlU ⟨a, ha⟩
      ((symProd (Q.comp W.subtype) lW hlW ⟨b, hb⟩ : W) : V) (fun u => hU0 u _)
    simp only at h2
    rw [h2, map_add, ← hστ ⟨a, ha⟩, ← hσρ ⟨b, hb⟩]
    simp [add_comm]
  · rw [List.map_append, List.prod_append]
    have h1 : (lU.map (fun s : U => (s : V))).map Q = lU.map (Q.comp U.subtype) := by
      rw [List.map_map]; rfl
    have h2 : (lW.map (fun s : W => (s : V))).map Q = lW.map (Q.comp W.subtype) := by
      rw [List.map_map]; rfl
    rw [h1, h2, hp, hq]; ring

/-- **55:4, the equality of spinor norms:** in the situation of `hasSpinorNorm_of_splitting`, for a regular space
every spinor norm $e$ of $\sigma$ is $e = cds^2$ with $s \in F^\times$. -/
theorem HasSpinorNorm.eq_mul_mul_sq_of_splitting (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {U W : Submodule F V} (hUW : IsCompl U W) (horth : ∀ u ∈ U, ∀ w ∈ W, bil Q u w = 0)
    {τ : U ≃ₗ[F] U} {ρ : W ≃ₗ[F] W} {σ : V ≃ₗ[F] V}
    (hστ : ∀ u : U, σ (u : V) = ((τ u : U) : V)) (hσρ : ∀ w : W, σ (w : V) = ((ρ w : W) : V))
    {c d e : F} (hτ : HasSpinorNorm (Q.comp U.subtype) τ c) (hρ : HasSpinorNorm (Q.comp W.subtype) ρ d)
    (he : HasSpinorNorm Q σ e) : ∃ s : F, s ≠ 0 ∧ e = c * d * s ^ 2 :=
  HasSpinorNorm.eq_mul_sq Q hQ he (hasSpinorNorm_of_splitting Q hUW horth hστ hσρ hτ hρ)

end Splitting

/-! ### 55:7: the spinor norm of $-1_V$ -/

section Discriminant

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

namespace Sp55

theorem symProd_apply_of_orth (ms : List V) (hms : ∀ u ∈ ms, Q u ≠ 0) (z : V)
    (hz : ∀ u ∈ ms, bil Q z u = 0) : symProd Q ms hms z = z := by
  induction ms with
  | nil => rfl
  | cons x ms ih =>
    rw [symProd_cons Q hms, LinearEquiv.mul_apply,
      ih (fun u hu => hms u (List.mem_cons_of_mem x hu)) (fun u hu => hz u (List.mem_cons_of_mem x hu)),
      symmetry_apply, hz x List.mem_cons_self]
    simp

theorem symProd_apply_of_mem (ms : List V) (hms : ∀ u ∈ ms, Q u ≠ 0)
    (hpw : ms.Pairwise fun u w => bil Q u w = 0) (z : V) (hz : z ∈ ms) : symProd Q ms hms z = -z := by
  induction ms with
  | nil => simp at hz
  | cons x ms ih =>
    have hpw' := List.pairwise_cons.mp hpw
    have hx := hms x List.mem_cons_self
    rw [symProd_cons Q hms, LinearEquiv.mul_apply]
    rcases List.mem_cons.mp hz with h | hz'
    · rw [h, symProd_apply_of_orth Q ms _ x (fun u hu => hpw'.1 u hu), symmetry_apply, bil_self]
      have : 2 * Q x / Q x = 2 := by field_simp
      rw [this, two_smul]
      abel
    · rw [ih (fun u hu => hms u (List.mem_cons_of_mem x hu)) hpw'.2 hz', map_neg, symmetry_apply,
        bil_comm Q z x, hpw'.1 z hz']
      simp

theorem det_gram_orthogonal {n : ℕ} (e : Module.Basis (Fin n) F V)
    (he : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0) : (gram Q e).det = ∏ i, Q (e i) := by
  have : gram Q e = Matrix.diagonal fun i => Q (e i) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [gram]
    · simp [gram, Matrix.diagonal, h, he i j h]
  rw [this, Matrix.det_diagonal]

theorem det_gram_eq {n : ℕ} (e b : Module.Basis (Fin n) F V) :
    (gram Q b).det = (e.det b) ^ 2 * (gram Q e).det := by
  have h := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix e b (QuadraticMap.associated Q)
  have hg : ∀ c : Module.Basis (Fin n) F V,
      LinearMap.BilinForm.toMatrix c (QuadraticMap.associated Q) = gram Q c := fun c => by
    ext i j; simp [gram, LinearMap.BilinForm.toMatrix_apply]
  rw [hg, hg] at h
  rw [← h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Module.Basis.det_apply]
  ring

theorem det_gram_reindex {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : Module.Basis (Fin n) F V)
    (b : Module.Basis ι F V) :
    (gram Q b).det = (e.det (b.reindex (b.indexEquiv e))) ^ 2 * (gram Q e).det := by
  rw [← det_gram_eq Q e]
  have : gram Q (b.reindex (b.indexEquiv e)) = (gram Q b).submatrix (b.indexEquiv e).symm
      (b.indexEquiv e).symm := by
    ext i j; simp [gram]
  rw [this, Matrix.det_submatrix_equiv_self]

theorem det_neg_eq : LinearEquiv.det (LinearEquiv.neg F : V ≃ₗ[F] V) = (-1) ^ Module.finrank F V := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have : ((LinearEquiv.neg F : V ≃ₗ[F] V) : V →ₗ[F] V) = (-1 : F) • LinearMap.id := by
    ext x; simp
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]
  simp

end Sp55

/-- **55:7, first part** (O'Meara 1963, 55:7, p. 141): for a regular quadratic space $V$, $-1_V$ has spinor norm
the discriminant $dV = \det(B(b_i, b_j))$ (for any basis $b$; the class modulo squares does not depend on $b$,
which is built into `HasSpinorNorm`). -/
@[kb "omeara1963" "§55, 55:7, p. 141 (θ(−1_V) = dV)"]
theorem hasSpinorNorm_neg_one (hQ : (QuadraticMap.associated Q).Nondegenerate) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι F V) :
    HasSpinorNorm Q (LinearEquiv.neg F) (gram Q b).det := by
  obtain ⟨e, he, hea⟩ := exists_orthogonal_anisotropic_basis Q hQ
  have hms : ∀ u ∈ List.ofFn e, Q u ≠ 0 := by
    intro u hu
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    exact hea i
  have hneg : symProd Q (List.ofFn e) hms = LinearEquiv.neg F := by
    refine LinearEquiv.toLinearMap_injective (e.ext fun j => ?_)
    show symProd Q (List.ofFn e) hms (e j) = -(e j)
    exact Sp55.symProd_apply_of_mem Q _ hms (List.pairwise_ofFn.mpr fun i j hij => he i j hij.ne) _
      (List.mem_ofFn.mpr ⟨j, rfl⟩)
  set u := e.det (b.reindex (b.indexEquiv e)) with hu
  have hu0 : u ≠ 0 := (e.isUnit_det _).ne_zero
  refine (hasSpinorNorm_iff Q).mpr ⟨List.ofFn e, hms, hneg.symm, u⁻¹, inv_ne_zero hu0, ?_⟩
  have hprod : ∏ i, (⇑Q ∘ ⇑e) i = (gram Q e).det := (Sp55.det_gram_orthogonal Q e he).symm
  rw [Sp55.det_gram_reindex Q e b, ← hu, List.map_ofFn, List.prod_ofFn, hprod]
  field_simp

/-- **55:7, second part** (O'Meara 1963, 55:7, p. 141): for a regular $n$-ary space, $-1_V \in O'(V)$ if and only if
$n$ is even and $dV$ is a square ($dV = 1$ modulo squares). -/
@[kb "omeara1963" "§55, 55:7, p. 141 (−1_V ∈ O'_n iff n even and dV = 1)"]
theorem neg_mem_orthPrime_iff (hQ : (QuadraticMap.associated Q).Nondegenerate) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι F V) :
    LinearEquiv.neg F ∈ orthPrime Q ↔ Even (Module.finrank F V) ∧ IsSquare (gram Q b).det := by
  have hd := hasSpinorNorm_neg_one Q hQ b
  have hdet : LinearEquiv.det (LinearEquiv.neg F : V ≃ₗ[F] V) = 1 ↔ Even (Module.finrank F V) := by
    rw [Sp55.det_neg_eq]; exact neg_one_pow_eq_one_iff_even Sp55.neg_one_ne_one_units
  constructor
  · rintro ⟨⟨-, hker⟩, h1⟩
    refine ⟨hdet.mp hker, ?_⟩
    obtain ⟨s, -, hs⟩ := HasSpinorNorm.eq_mul_sq Q hQ hd h1
    exact ⟨s, by rw [hs]; ring⟩
  · rintro ⟨hev, r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact HasSpinorNorm.ne_zero Q hd (by simpa using hr)
    exact ⟨⟨fun x => by simp, (MonoidHom.mem_ker).mpr (hdet.mpr hev)⟩,
      HasSpinorNorm.of_eq_mul_sq Q hd (inv_ne_zero hr0) (by rw [hr]; field_simp)⟩

end Discriminant

/-! ### Scaling (p. 138) -/

section Scaling

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

namespace Sp55

theorem bil_smul_form (a : F) (x y : V) : bil (a • Q) x y = a * bil Q x y := by
  apply mul_left_cancel₀ (two_ne_zero (α := F))
  rw [← polar_eq_two_mul_bil, mul_left_comm, ← polar_eq_two_mul_bil]
  simp only [QuadraticMap.polar, smul_apply, smul_eq_mul]
  ring

theorem symmetry_smul {a : F} (ha : a ≠ 0) {u : V} (hu : (a • Q) u ≠ 0) :
    symmetry (a • Q) u hu = symmetry Q u (fun h => hu (by simp [h])) := by
  have hu' : Q u ≠ 0 := fun h => hu (by simp [h])
  ext x
  rw [symmetry_apply, symmetry_apply, bil_smul_form, smul_apply, smul_eq_mul]
  congr 2
  field_simp

theorem symProd_smul {a : F} (ha : a ≠ 0) (l : List V) (hl : ∀ u ∈ l, (a • Q) u ≠ 0)
    (hl' : ∀ u ∈ l, Q u ≠ 0) : symProd (a • Q) l hl = symProd Q l hl' := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [symProd_cons _ hl, symProd_cons _ hl', symmetry_smul Q ha,
      ih (fun u hu => hl u (List.mem_cons_of_mem x hu)) (fun u hu => hl' u (List.mem_cons_of_mem x hu))]

theorem prod_map_smul {a : F} (l : List V) : (l.map (a • Q)).prod = a ^ l.length * (l.map Q).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, ih, smul_apply, smul_eq_mul]
    ring

end Sp55

/-- Scaling does not change the orthogonal group: $O(V^\alpha) = O(V)$ for $\alpha \ne 0$, where
$V^\alpha = (V, \alpha Q)$ (O'Meara 1963, §55, p. 138). -/
@[kb "omeara1963" "§55, p. 138 (O(V^a) = O(V))"]
theorem orth_smul {a : F} (ha : a ≠ 0) : orth (a • Q) = orth Q := by
  ext σ
  constructor
  · intro h x
    have := h x
    simp only [smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ ha this
  · intro h x
    simp only [smul_apply, smul_eq_mul]
    rw [h x]

/-- Scaling does not change the rotation group: $O^+(V^\alpha) = O^+(V)$ for $\alpha \ne 0$. -/
@[kb "omeara1963" "§55, p. 138 (O⁺(V^a) = O⁺(V))"]
theorem orthPlus_smul {a : F} (ha : a ≠ 0) : orthPlus (a • Q) = orthPlus Q := by
  unfold orthPlus
  rw [orth_smul Q ha]

theorem orthPrime_smul_le {a : F} (ha : a ≠ 0) : orthPrime (a • Q) ≤ orthPrime Q := by
  rintro σ ⟨hplus, l, hl, hσ, s, hs, hp⟩
  have hl' : ∀ u ∈ l, Q u ≠ 0 := fun u hu h => hl u hu (by simp [h])
  rw [orthPlus_smul Q ha] at hplus
  rw [attach_prod_eq_symProd (a • Q) l hl] at hσ
  rw [Sp55.symProd_smul Q ha l hl hl'] at hσ
  have hdet : LinearEquiv.det σ = 1 := hplus.2
  rw [hσ, Sp55.det_symProd Q l hl'] at hdet
  obtain ⟨k, hk⟩ := (neg_one_pow_eq_one_iff_even Sp55.neg_one_ne_one_units).mp hdet
  refine ⟨hplus, l, hl', ?_, s / a ^ k, div_ne_zero hs (pow_ne_zero _ ha), ?_⟩
  · rw [attach_prod_eq_symProd Q l hl']; exact hσ
  · rw [Sp55.prod_map_smul, hk] at hp
    have h2 : a ^ (k + k) ≠ 0 := pow_ne_zero _ ha
    rw [pow_add] at hp h2
    field_simp
    linear_combination hp

/-- **Scaling preserves $O'$:** $O'(V^\alpha) = O'(V)$ for $\alpha \ne 0$ (O'Meara 1963, §55, p. 138): a rotation is
a product of an even number of symmetries, so its spinor norm changes by an even power of $\alpha$. -/
@[kb "omeara1963" "§55, p. 138 (O'(V^a) = O'(V))"]
theorem orthPrime_smul {a : F} (ha : a ≠ 0) : orthPrime (a • Q) = orthPrime Q := by
  refine le_antisymm (orthPrime_smul_le Q ha) ?_
  have := orthPrime_smul_le (a • Q) (inv_ne_zero ha)
  rwa [inv_smul_smul₀ ha] at this

end Scaling

/-! ### Consequences of the Cartan-Dieudonne theorem (pp. 137-141) -/

section CD

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

namespace Sp55

theorem symProd_mem_orth (l : List V) (hl : ∀ u ∈ l, Q u ≠ 0) : symProd Q l hl ∈ orth Q := by
  induction l with
  | nil => exact (orth Q).one_mem
  | cons x l ih =>
    rw [symProd_cons Q hl]
    exact (orth Q).mul_mem (symmetry_mem_orth Q _)
      (ih fun u hu => hl u (List.mem_cons_of_mem x hu))

theorem symmetry_smul_vec {y : V} {t : F} (ht : t ≠ 0) (hy : Q y ≠ 0) (hty : Q (t • y) ≠ 0) :
    symmetry Q (t • y) hty = symmetry Q y hy := by
  ext x
  rw [symmetry_apply, symmetry_apply, bil_smul_right, Q_smul, smul_smul]
  congr 2
  field_simp

theorem even_length_of_mem_orthPlus {σ : V ≃ₗ[F] V} (hσ : σ ∈ orthPlus Q) (l : List V)
    (hl : ∀ u ∈ l, Q u ≠ 0) (h : σ = symProd Q l hl) : Even l.length := by
  have hdet : LinearEquiv.det σ = 1 := hσ.2
  rw [h, det_symProd Q l hl] at hdet
  exact (neg_one_pow_eq_one_iff_even neg_one_ne_one_units).mp hdet

end Sp55

/-- **Every isometry of a regular space has a spinor norm** (O'Meara 1963, §55, p. 137): by the Cartan-Dieudonne
theorem 43:3 it is a product of symmetries. -/
@[kb "omeara1963" "§55, p. 137 (every σ ∈ O_n has a spinor norm)"]
theorem exists_hasSpinorNorm_of_mem_orth (hQ : (QuadraticMap.associated Q).Nondegenerate) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ orth Q) : ∃ c : F, c ≠ 0 ∧ HasSpinorNorm Q σ c := by
  obtain ⟨l, hl, h, -⟩ := exists_symmetry_prod_eq_length_le Q hQ hσ
  have hs : HasSpinorNorm Q σ (l.map Q).prod := ⟨l, hl, h, 1, one_ne_zero, by simp⟩
  exact ⟨_, HasSpinorNorm.ne_zero Q hs, hs⟩

/-- **$\Omega \subseteq O'$** (O'Meara 1963, §55, p. 138): "a commutator clearly has spinor norm $1$". -/
@[kb "omeara1963" "§55, p. 138 (Ω_n ⊆ O'_n)"]
theorem omega_le_orthPrime (hQ : (QuadraticMap.associated Q).Nondegenerate) : omega Q ≤ orthPrime Q := by
  unfold omega
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [commutatorElement_def]
  obtain ⟨c, hc0, hc⟩ := exists_hasSpinorNorm_of_mem_orth Q hQ hg
  obtain ⟨d, hd0, hd⟩ := exists_hasSpinorNorm_of_mem_orth Q hQ hh
  refine ⟨⟨(orth Q).mul_mem ((orth Q).mul_mem ((orth Q).mul_mem hg hh) ((orth Q).inv_mem hg))
    ((orth Q).inv_mem hh), ?_⟩, ?_⟩
  · show LinearEquiv.det (g * h * g⁻¹ * h⁻¹) = 1
    rw [← commutatorElement_def, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  · have := HasSpinorNorm.mul Q (HasSpinorNorm.mul Q (HasSpinorNorm.mul Q hc hd) (HasSpinorNorm.inv Q hc))
      (HasSpinorNorm.inv Q hd)
    refine HasSpinorNorm.of_eq_mul_sq Q this (inv_ne_zero (mul_ne_zero hc0 hd0)) ?_
    field_simp

/-- **$\Omega$ is normal in $O$** (O'Meara 1963, §55, p. 138). -/
@[kb "omeara1963" "§55, p. 138 (Ω_n is a normal subgroup of O_n)"]
theorem omega_subgroupOf_normal : ((omega Q).subgroupOf (orth Q)).Normal := by
  have : (omega Q).subgroupOf (orth Q) = commutator (orth Q) := by
    rw [omega_eq_map]
    ext g
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.subtype_apply]
    constructor
    · rintro ⟨x, hx, h⟩
      rw [← Subtype.ext h]; exact hx
    · intro hg; exact ⟨g, hg, rfl⟩
  rw [this]
  infer_instance

/-- **$O^+$ is normal in $O$** (O'Meara 1963, §55, p. 138). -/
@[kb "omeara1963" "§55, p. 138 (O⁺_n is a normal subgroup of O_n)"]
theorem orthPlus_subgroupOf_normal : ((orthPlus Q).subgroupOf (orth Q)).Normal := by
  have : (orthPlus Q).subgroupOf (orth Q) = (LinearEquiv.det.comp (orth Q).subtype).ker := by
    ext g
    simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.subtype_apply]
    exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
  rw [this]
  exact MonoidHom.normal_ker _

/-- **Squares of isometries lie in $\Omega$** (O'Meara 1963, §43D, 43:6 (first sentence), p. 107, for a regular
space): $\sigma^2 \in \Omega$ for every $\sigma \in O(V)$. (In $O/\Omega$, which is abelian, a product of
symmetries has square $1$ by Cartan-Dieudonne.) -/
@[kb "omeara1963" "§43D, 43:6, p. 107 (σ² ∈ Ω for σ ∈ O)"]
theorem sq_mem_omega (hQ : (QuadraticMap.associated Q).Nondegenerate) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ orth Q) : σ ^ 2 ∈ omega Q := by
  obtain ⟨l, hl, h, -⟩ := exists_symmetry_prod_eq_length_le Q hQ hσ
  rw [attach_prod_eq_symProd Q l hl] at h
  have key : ∀ m : List V, Abelianization.of ((m.map (tauHat Q)).prod) ^ 2 = 1 := by
    intro m
    induction m with
    | nil => simp
    | cons x m ih =>
      rw [List.map_cons, List.prod_cons, map_mul, mul_pow, ih, mul_one, ← map_pow]
      have : tauHat Q x ^ 2 = 1 := by
        apply Subtype.ext
        by_cases hx : Q x ≠ 0
        · rw [Subgroup.coe_pow, coe_tauHat Q hx, pow_two]
          ext y
          exact symmetry_symmetry Q hx y
        · simp [tauHat, hx]
      rw [this, map_one]
  have hσ' : (⟨σ, hσ⟩ : orth Q) = (l.map (tauHat Q)).prod := by
    apply Subtype.ext
    rw [coe_prod_tauHat Q l hl]
    exact h
  have h1 : Abelianization.of ((⟨σ, hσ⟩ : orth Q) ^ 2) = 1 := by
    rw [map_pow, hσ']; exact key l
  have h2 : (⟨σ, hσ⟩ : orth Q) ^ 2 ∈ (Abelianization.of : orth Q →* Abelianization (orth Q)).ker := h1
  rw [Abelianization.ker_of] at h2
  rw [omega_eq_map]
  exact ⟨_, h2, rfl⟩

/-- **55:2** (O'Meara 1963, 55:2, p. 139): for a regular $n$-ary space with $n \ge 2$, $c \in F^\times$ is the
spinor norm of a rotation if and only if $c = \kappa_1\cdots\kappa_r$ with $r \le n$ even and
$\kappa_i = Q(u_i)$ nonzero values of $Q$ (here phrased through the vectors $u_1, \dots, u_r$).

*Reconstruction:* the machine-read text says "$r \le n$ and $\kappa_1, \dots, \kappa_r \in Q(V)$"; the evenness of $r$
(a rotation is a product of an even number of symmetries) is implicit in the book and is made explicit here; for
$r$ odd the statement would be false (e.g. $n = 2$, $r = 1$). -/
@[kb "omeara1963" "§55, 55:2, p. 139 (θ(O⁺) = products of ≤ n values of Q)"]
theorem exists_hasSpinorNorm_iff (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : 2 ≤ Module.finrank F V) {c : F} :
    (∃ σ ∈ orthPlus Q, HasSpinorNorm Q σ c) ↔
      ∃ l : List V, (∀ u ∈ l, Q u ≠ 0) ∧ Even l.length ∧ l.length ≤ Module.finrank F V ∧
        (l.map Q).prod = c := by
  constructor
  · rintro ⟨σ, hσ, hc'⟩
    obtain ⟨l', hl', h', hlen⟩ := exists_symmetry_prod_eq_length_le Q hQ hσ.1
    rw [attach_prod_eq_symProd Q l' hl'] at h'
    have hs : HasSpinorNorm Q σ (l'.map Q).prod :=
      (hasSpinorNorm_iff Q).mpr ⟨l', hl', h', 1, one_ne_zero, by simp⟩
    obtain ⟨s, hs0, hcs⟩ := HasSpinorNorm.eq_mul_sq Q hQ hc' hs
    have hev := even_length_of_mem_orthPlus Q hσ l' hl' h'
    rcases l' with _ | ⟨x, rest⟩
    · have hpos : 0 < Module.finrank F V := by omega
      have : Nontrivial V := Module.finrank_pos_iff.mp hpos
      obtain ⟨u, hu⟩ := cd_exists_aniso Q (cd_reg_of_nondeg Q hQ)
      have hsu : Q ((s / Q u) • u) ≠ 0 := by
        rw [Q_smul]; exact mul_ne_zero (pow_ne_zero 2 (div_ne_zero hs0 hu)) hu
      refine ⟨[(s / Q u) • u, u], ?_, even_two, by simpa using hn, ?_⟩
      · intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        exacts [hsu, hu]
      · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Q_smul]
        rw [hcs]
        simp only [List.map_nil, List.prod_nil, one_mul]
        field_simp
    · have hx := hl' x List.mem_cons_self
      have hsx : Q (s • x) ≠ 0 := by rw [Q_smul]; exact mul_ne_zero (pow_ne_zero 2 hs0) hx
      refine ⟨(s • x) :: rest, ?_, hev, hlen, ?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hsx
        · exact hl' v (List.mem_cons_of_mem x hv)
      · simp only [List.map_cons, List.prod_cons, Q_smul] at hcs ⊢
        rw [hcs]; ring
  · rintro ⟨l, hl, hev, -, hp⟩
    refine ⟨symProd Q l hl, ⟨symProd_mem_orth Q l hl, (MonoidHom.mem_ker).mpr ?_⟩, ?_⟩
    · rw [det_symProd Q l hl]; exact hev.neg_one_pow
    · exact (hasSpinorNorm_iff Q).mpr ⟨l, hl, rfl, 1, one_ne_zero, by rw [hp]; ring⟩

/-- A regular space split orthogonally has regular summands. -/
theorem Sp55.nondegenerate_of_splitting (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {U W : Submodule F V} (hUW : IsCompl U W) (horth : ∀ u ∈ U, ∀ w ∈ W, bil Q u w = 0) :
    (QuadraticMap.associated (Q.comp U.subtype)).Nondegenerate := by
  apply cd_nondeg_of_reg
  intro u hu
  have : (u : V) = 0 := by
    apply hQ.1
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (by rw [hUW.sup_eq_top]; trivial : v ∈ U ⊔ W)
    show bil Q (u : V) (a + b) = 0
    rw [bil_add_right, horth (u : V) u.2 b hb, add_zero]
    have := hu ⟨a, ha⟩
    rwa [Sp55.bil_comp_subtype] at this
  exact Subtype.ext this

/-- **55:4, full form** (O'Meara 1963, 55:4, p. 139): let $V = U \perp W$ be an orthogonal splitting of a regular
quadratic space (so $U$ and $W$ are regular) and $\sigma \in O(V)$ with $\sigma = \tau \perp \rho$. Then $\tau$ and
$\rho$ have spinor norms $c$ and $d$ (as isometries of $U$, $W$), and $\sigma$ has spinor norm $cd$:
$\theta(\sigma) = \theta(\tau)\theta(\rho)$. -/
@[kb "omeara1963" "§55, 55:4, p. 139 (θ(τ ⊥ ρ) = θ(τ)θ(ρ), full form)"]
theorem exists_hasSpinorNorm_of_splitting (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {U W : Submodule F V} (hUW : IsCompl U W) (horth : ∀ u ∈ U, ∀ w ∈ W, bil Q u w = 0)
    {τ : U ≃ₗ[F] U} {ρ : W ≃ₗ[F] W} {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q)
    (hστ : ∀ u : U, σ (u : V) = ((τ u : U) : V)) (hσρ : ∀ w : W, σ (w : V) = ((ρ w : W) : V)) :
    ∃ c d : F, HasSpinorNorm (Q.comp U.subtype) τ c ∧ HasSpinorNorm (Q.comp W.subtype) ρ d ∧
      HasSpinorNorm Q σ (c * d) := by
  have hU := Sp55.nondegenerate_of_splitting Q hQ hUW horth
  have hW := Sp55.nondegenerate_of_splitting Q hQ hUW.symm (fun w hw u hu => by
    rw [bil_comm]; exact horth u hu w hw)
  have hτ : τ ∈ orth (Q.comp U.subtype) := fun x => by
    show Q ((τ x : U) : V) = Q (x : V)
    rw [← hστ x]; exact hσ _
  have hρ : ρ ∈ orth (Q.comp W.subtype) := fun x => by
    show Q ((ρ x : W) : V) = Q (x : V)
    rw [← hσρ x]; exact hσ _
  obtain ⟨c, -, hc⟩ := exists_hasSpinorNorm_of_mem_orth _ hU hτ
  obtain ⟨d, -, hd⟩ := exists_hasSpinorNorm_of_mem_orth _ hW hρ
  exact ⟨c, d, hc, hd, hasSpinorNorm_of_splitting Q hUW horth hστ hσρ hc hd⟩

/-! ### 55:5 -/

/-- $O' \subseteq \Omega$ for $n \le 3$ (part of O'Meara's 55:5, p. 140): a rotation is a product $\tau_x\tau_y$ of at most
two symmetries; if its spinor norm is $1$ one may scale $y$ so that $Q(x) = Q(y)$, and then 55:3 applies. -/
theorem orthPrime_le_omega_of_finrank_le_three (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : Module.finrank F V ≤ 3) : orthPrime Q ≤ omega Q := by
  rintro σ ⟨hplus, hσ1⟩
  obtain ⟨l, hl, h, hlen⟩ := exists_symmetry_prod_eq_length_le_two Q hQ h3 hplus
  rw [attach_prod_eq_symProd Q l hl] at h
  have hev := even_length_of_mem_orthPlus Q hplus l hl h
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
  · have : σ = 1 := h
    rw [this]; exact (omega Q).one_mem
  · simp at hev
  · have hx := hl x (by simp)
    have hy := hl y (by simp)
    have hσ2 : HasSpinorNorm Q σ (Q x * Q y) :=
      (hasSpinorNorm_iff Q).mpr ⟨[x, y], hl, h, 1, one_ne_zero, by simp⟩
    obtain ⟨s, hs, hxy⟩ := HasSpinorNorm.eq_mul_sq Q hQ hσ2 hσ1
    have ht : s / Q y ≠ 0 := div_ne_zero hs hy
    have hQx : Q x = Q ((s / Q y) • y) := by
      rw [Q_smul]
      field_simp
      linear_combination hxy
    have hty : Q ((s / Q y) • y) ≠ 0 := by rw [← hQx]; exact hx
    have hu' : ∀ w ∈ [x, (s / Q y) • y], Q w ≠ 0 := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      exacts [hx, hty]
    have hv' : ∀ w ∈ [(s / Q y) • y, (s / Q y) • y], Q w ≠ 0 := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hw
      rw [hw]; exact hty
    have hperm : ([x, (s / Q y) • y].map Q).Perm ([(s / Q y) • y, (s / Q y) • y].map Q) := by
      simp only [List.map_cons, List.map_nil, ← hQx]
      exact List.Perm.refl _
    have key := symProd_mul_inv_mem_omega Q hQ hu' hv' hperm
    have e2 : symProd Q [(s / Q y) • y, (s / Q y) • y] hv' = 1 := by
      simp only [symProd_cons, symProd_nil, mul_one]
      ext z
      exact symmetry_symmetry Q hty z
    have e1 : symProd Q [x, (s / Q y) • y] hu' = σ := by
      rw [h]
      simp only [symProd_cons, symProd_nil, mul_one]
      rw [Sp55.symmetry_smul_vec Q ht hy hty]
    rw [e1, e2, inv_one, mul_one] at key
    exact key
  · simp at hlen

/-- **55:5, first part** (O'Meara 1963, 55:5, p. 140): for a regular $n$-ary space with $n \le 3$,
$\Omega = O'$. (The book also states $1 \le n$; the case $n = 0$ is trivial.) -/
@[kb "omeara1963" "§55, 55:5, p. 140 (Ω_n = O'_n for n ≤ 3)"]
theorem omega_eq_orthPrime_of_finrank_le_three (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : Module.finrank F V ≤ 3) : omega Q = orthPrime Q :=
  le_antisymm (omega_le_orthPrime Q hQ) (orthPrime_le_omega_of_finrank_le_three Q hQ h3)

/-- **55:5, the inclusion $(O^+)^2 \subseteq \Omega$** (O'Meara 1963, 55:5, p. 140; valid in every dimension): the
square of a rotation lies in $\Omega$. The reverse inclusion $\Omega \subseteq (O^+)^2$ for $n \le 3$ is `omega_eq_sq_orthPlus`
(`Sec55Omega.lean`). -/
@[kb "omeara1963" "§55, 55:5, p. 140 ((O⁺_n)² ⊆ Ω_n)"]
theorem sq_mem_omega_of_mem_orthPlus (hQ : (QuadraticMap.associated Q).Nondegenerate) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ orthPlus Q) : σ ^ 2 ∈ omega Q :=
  sq_mem_omega Q hQ hσ.1

end CD

/-! ### 55:6, 55:6a and §56 -/

section Sub

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

namespace Sp55

/-- A regular subspace is complementary to its orthogonal complement. -/
theorem isCompl_perp {U : Submodule F V}
    (hU : (QuadraticMap.associated (Q.comp U.subtype)).Nondegenerate) :
    IsCompl U (LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q : LinearMap.BilinForm F V) U) := by
  apply LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
  · exact fun a b h => (bil_comm Q b a).trans h
  · constructor
    · intro x hx
      apply hU.1 x
      intro y
      have := hx y
      simpa [LinearMap.BilinForm.restrict_apply, bil_comp_subtype] using this
    · intro y hy
      apply hU.2 y
      intro x
      have := hy x
      simpa [LinearMap.BilinForm.restrict_apply, bil_comp_subtype] using this

theorem horth_perp {U : Submodule F V} :
    ∀ u ∈ U, ∀ w ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q : LinearMap.BilinForm F V) U,
      bil Q u w = 0 :=
  fun u hu _ hw => (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) u hu

/-- Extension by the identity: $\tau \mapsto \tau \perp 1_W$ for $V = U \oplus W$. -/
def extId {U W : Submodule F V} (h : IsCompl U W) : (U ≃ₗ[F] U) →* (V ≃ₗ[F] V) where
  toFun τ := (Submodule.prodEquivOfIsCompl U W h).symm.trans
    ((LinearEquiv.prodCongr τ (LinearEquiv.refl F W)).trans (Submodule.prodEquivOfIsCompl U W h))
  map_one' := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl U W h).surjective v
    simp
  map_mul' := by
    intro τ ρ
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl U W h).surjective v
    simp

theorem extId_apply {U W : Submodule F V} (h : IsCompl U W) (τ : U ≃ₗ[F] U) (a : U) (b : W) :
    extId h τ ((a : V) + b) = ((τ a : U) : V) + b := by
  have : (a : V) + b = Submodule.prodEquivOfIsCompl U W h (a, b) := by simp
  rw [this]
  simp [extId]

theorem exists_decomp {U W : Submodule F V} (h : IsCompl U W) (v : V) :
    ∃ a : U, ∃ b : W, v = (a : V) + b := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (by rw [h.sup_eq_top]; trivial : v ∈ U ⊔ W)
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

theorem extId_mem_orth {U W : Submodule F V} (h : IsCompl U W) (horth : ∀ u ∈ U, ∀ w ∈ W, bil Q u w = 0)
    {τ : U ≃ₗ[F] U} (hτ : τ ∈ orth (Q.comp U.subtype)) : extId h τ ∈ orth Q := by
  intro v
  obtain ⟨a, b, rfl⟩ := exists_decomp h v
  rw [extId_apply, Q_add, Q_add, horth _ (τ a).2 b b.2, horth _ a.2 b b.2]
  have := hτ a
  have e : Q ((τ a : U) : V) = Q (a : V) := this
  rw [e]

theorem extId_symProd {U W : Submodule F V} (h : IsCompl U W) (horth : ∀ u ∈ U, ∀ w ∈ W, bil Q u w = 0)
    (l : List U) (hl : ∀ u ∈ l, (Q.comp U.subtype) u ≠ 0) :
    extId h (symProd (Q.comp U.subtype) l hl) = symProd Q (l.map fun s : U => (s : V))
      (ne_zero_map_coe Q U l hl) := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨a, b, rfl⟩ := exists_decomp h v
  rw [extId_apply, symProd_map_coe_add Q U l hl a b (fun s => by rw [bil_comm]; exact horth _ s.2 b b.2)]

theorem map_omega_le {U W : Submodule F V} (h : IsCompl U W) (horth : ∀ u ∈ U, ∀ w ∈ W, bil Q u w = 0) :
    (omega (Q.comp U.subtype)).map (extId h) ≤ omega Q := by
  unfold omega
  rw [Subgroup.map_commutator]
  apply Subgroup.commutator_mono <;>
  · rintro _ ⟨τ, hτ, rfl⟩
    exact extId_mem_orth Q h horth hτ

theorem exists_lift_list {U : Submodule F V} (hval : ∀ v : V, ∃ u : U, Q (u : V) = Q v) :
    ∀ l : List V, ∃ l' : List U, l'.map (fun u : U => Q (u : V)) = l.map Q
  | [] => ⟨[], rfl⟩
  | x :: l => by
    obtain ⟨u, hu⟩ := hval x
    obtain ⟨l', h'⟩ := exists_lift_list hval l
    exact ⟨u :: l', by simp [hu, h']⟩

end Sp55

/-- **55:6** (O'Meara 1963, 55:6, p. 140): let $U$ be a regular subspace of a regular quadratic space $V$ with
$Q(U) = Q(V)$ (every value $Q(v)$, $v \in V$, is a value $Q(u)$, $u \in U$) and $\Omega(U) = O'(U)$ (for the
restricted form `Q.comp U.subtype`). Then $\Omega(V) = O'(V)$. -/
@[kb "omeara1963" "§55, 55:6, p. 140 (Ω(U) = O'(U), Q(U) = Q(V) imply Ω(V) = O'(V))"]
theorem omega_eq_orthPrime_of_subspace (hQ : (QuadraticMap.associated Q).Nondegenerate) {U : Submodule F V}
    (hU : (QuadraticMap.associated (Q.comp U.subtype)).Nondegenerate)
    (hval : ∀ v : V, ∃ u : U, Q (u : V) = Q v)
    (hΩ : omega (Q.comp U.subtype) = orthPrime (Q.comp U.subtype)) : omega Q = orthPrime Q := by
  refine le_antisymm (omega_le_orthPrime Q hQ) ?_
  intro σ hσ
  have hcomp := Sp55.isCompl_perp Q hU
  have horth := Sp55.horth_perp Q (U := U)
  obtain ⟨l, hl, h, -⟩ := exists_symmetry_prod_eq_length_le Q hQ hσ.1.1
  rw [attach_prod_eq_symProd Q l hl] at h
  obtain ⟨l', hl'map⟩ := Sp55.exists_lift_list Q hval l
  have hl'ne : ∀ u ∈ l', (Q.comp U.subtype) u ≠ 0 := by
    intro u hu
    have : Q (u : V) ∈ l.map Q := by rw [← hl'map]; exact List.mem_map_of_mem hu
    obtain ⟨v, hv, hvu⟩ := List.mem_map.mp this
    show Q (u : V) ≠ 0
    rw [← hvu]; exact hl v hv
  have hperm : (l.map Q).Perm ((l'.map fun u : U => (u : V)).map Q) := by
    rw [List.map_map]
    exact (show l.map Q = l'.map (Q ∘ fun u : U => (u : V)) from hl'map.symm) ▸ List.Perm.refl _
  have h1 := symProd_mul_inv_mem_omega Q hQ hl (Sp55.ne_zero_map_coe Q U l' hl'ne) hperm
  have hτ' : symProd (Q.comp U.subtype) l' hl'ne ∈ omega (Q.comp U.subtype) := by
    rw [hΩ]
    have hev := even_length_of_mem_orthPlus Q hσ.1 l hl h
    have hlen : l'.length = l.length := by simpa using congrArg List.length hl'map
    have hs : HasSpinorNorm Q σ (l.map Q).prod :=
      (hasSpinorNorm_iff Q).mpr ⟨l, hl, h, 1, one_ne_zero, by simp⟩
    obtain ⟨s, hs0, hps⟩ := HasSpinorNorm.eq_mul_sq Q hQ hs hσ.2
    refine ⟨⟨symProd_mem_orth _ _ _, (MonoidHom.mem_ker).mpr ?_⟩, ?_⟩
    · rw [det_symProd _ _ hl'ne, hlen]; exact hev.neg_one_pow
    · refine (hasSpinorNorm_iff _).mpr ⟨l', hl'ne, rfl, s, hs0, ?_⟩
      have e : l'.map (Q.comp U.subtype) = l.map Q := hl'map
      rw [e, hps]
  have h2 : symProd Q (l'.map fun u : U => (u : V)) (Sp55.ne_zero_map_coe Q U l' hl'ne) ∈ omega Q := by
    have := Sp55.map_omega_le Q hcomp horth (Subgroup.mem_map_of_mem (Sp55.extId hcomp) hτ')
    rwa [Sp55.extId_symProd Q hcomp horth] at this
  rw [← h] at h1
  have := (omega Q).mul_mem h1 h2
  simpa using this

/-- A hyperbolic plane $\mathrm{span}\{x, y\}$ is regular. -/
theorem Sp55.nondegenerate_span_pair {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1) :
    (QuadraticMap.associated (Q.comp (Submodule.span F {x, y}).subtype)).Nondegenerate := by
  apply cd_nondeg_of_reg
  intro u hu
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp u.2
  have hx' := hu ⟨x, Submodule.subset_span (by simp)⟩
  have hy' := hu ⟨y, Submodule.subset_span (by simp)⟩
  rw [Sp55.bil_comp_subtype] at hx' hy'
  simp only at hx' hy'
  rw [← hab] at hx' hy'
  rw [bil_add_left, bil_smul_left, bil_smul_left, bil_self, hx, bil_comm Q y x, hxy] at hx'
  rw [bil_add_left, bil_smul_left, bil_smul_left, bil_self, hy, hxy] at hy'
  have ha : a = 0 := by linear_combination hy'
  have hb : b = 0 := by linear_combination hx'
  apply Subtype.ext
  rw [← hab, ha, hb]
  simp

/-- **55:6a, first part** (O'Meara 1963, 55:6a, p. 140): if $V$ is a regular isotropic quadratic space then
$\Omega(V) = O'(V)$. (Proof as in the book: a hyperbolic plane $H \subseteq V$ has $Q(H) = F = Q(V)$ and
$\Omega(H) = O'(H)$ by 55:5, then 55:6.) -/
@[kb "omeara1963" "§55, 55:6a, p. 140 (Ω(V) = O'(V) for isotropic V)"]
theorem omega_eq_orthPrime_of_isotropic (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hiso : ∃ x : V, x ≠ 0 ∧ Q x = 0) : omega Q = orthPrime Q := by
  obtain ⟨x, hx0, hx⟩ := hiso
  obtain ⟨y, hy, hxy⟩ := exists_hyperbolic_pair Q hQ hx0 hx
  have hreg := Sp55.nondegenerate_span_pair Q hx hy hxy
  refine omega_eq_orthPrime_of_subspace Q hQ hreg ?_ ?_
  · intro v
    refine ⟨⟨(Q v / 2) • x + y, Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.subset_span (by simp))⟩, ?_⟩
    show Q ((Q v / 2) • x + y) = Q v
    rw [Q_add, Q_smul, bil_smul_left, hxy, hx, hy]
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    field_simp
    ring
  · apply omega_eq_orthPrime_of_finrank_le_three _ hreg
    classical
    have := finrank_span_finset_le_card (R := F) ({x, y} : Finset V)
    rw [Finset.coe_pair] at this
    exact this.trans (Finset.card_le_two.trans (by norm_num))

end Sub

/-! ### The spinor norm homomorphism and §56 -/

section Theta

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

namespace Sp55

/-! The lemmas on `Lattices.SqClass` in `QuadFormsKB/Lattices/SpinorNorm.lean` carry an incidental `[CharZero K]`
hypothesis (a section variable); the following copies hold over every field. -/

theorem sq_mk_eq_one_iff {K : Type*} [Field K] (x : Kˣ) :
    Lattices.SqClass.mk x = 1 ↔ ∃ y : Kˣ, y ^ 2 = x :=
  (QuotientGroup.eq_one_iff (N := (powMonoidHom 2 : Kˣ →* Kˣ).range) x).trans (by simp)

theorem sqClassOf_of_ne_zero' {K : Type*} [Field K] {a : K} (ha : a ≠ 0) :
    Lattices.sqClassOf a = Lattices.SqClass.mk (Units.mk0 a ha) := by
  simp [Lattices.sqClassOf, ha]

theorem sqClassOf_mul' {K : Type*} [Field K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    Lattices.sqClassOf (a * b) = Lattices.sqClassOf a * Lattices.sqClassOf b := by
  rw [sqClassOf_of_ne_zero' ha, sqClassOf_of_ne_zero' hb, sqClassOf_of_ne_zero' (mul_ne_zero ha hb)]
  have e : Units.mk0 (a * b) (mul_ne_zero ha hb) = Units.mk0 a ha * Units.mk0 b hb := by
    ext; simp
  rw [e]
  rfl

theorem sqClassOf_one' {K : Type*} [Field K] : Lattices.sqClassOf (1 : K) = 1 := by
  rw [sqClassOf_of_ne_zero' one_ne_zero, sq_mk_eq_one_iff]
  exact ⟨1, by ext; simp⟩

theorem sqClassOf_eq_one_iff' {K : Type*} [Field K] {a : K} (ha : a ≠ 0) :
    Lattices.sqClassOf a = 1 ↔ IsSquare a := by
  rw [sqClassOf_of_ne_zero' ha, sq_mk_eq_one_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have := congrArg Units.val hy
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at this
    rw [← this, sq]
  · rintro ⟨r, rfl⟩
    have hr : r ≠ 0 := fun h => ha (by rw [h, mul_zero])
    exact ⟨Units.mk0 r hr, by ext; simp [sq]⟩

open scoped Classical in
/-- The square class of some spinor norm of $\sigma$ (and $1$ if $\sigma$ has none). -/
def spinorFun (σ : V ≃ₗ[F] V) : Lattices.SqClass F :=
  if h : ∃ c, HasSpinorNorm Q σ c then Lattices.sqClassOf h.choose else 1

theorem sqClassOf_eq_of_hasSpinorNorm (hQ : (QuadraticMap.associated Q).Nondegenerate) {σ : V ≃ₗ[F] V}
    {c d : F} (hc : HasSpinorNorm Q σ c) (hd : HasSpinorNorm Q σ d) :
    Lattices.sqClassOf c = Lattices.sqClassOf d := by
  obtain ⟨s, hs, hcd⟩ := HasSpinorNorm.eq_mul_sq Q hQ hc hd
  have hd0 := HasSpinorNorm.ne_zero Q hd
  rw [hcd, Sp55.sqClassOf_mul' hd0 (pow_ne_zero 2 hs)]
  have : Lattices.sqClassOf (s ^ 2) = 1 :=
    (Sp55.sqClassOf_eq_one_iff' (pow_ne_zero 2 hs)).mpr ⟨s, sq s⟩
  rw [this, mul_one]

theorem spinorFun_eq (hQ : (QuadraticMap.associated Q).Nondegenerate) {σ : V ≃ₗ[F] V} {c : F}
    (hc : HasSpinorNorm Q σ c) : spinorFun Q σ = Lattices.sqClassOf c := by
  have h : ∃ c, HasSpinorNorm Q σ c := ⟨c, hc⟩
  simp only [spinorFun, h, ↓reduceDIte]
  exact sqClassOf_eq_of_hasSpinorNorm Q hQ h.choose_spec hc

end Sp55

/-- **The spinor norm** $\theta : O^+(V) \to F^\times/F^{\times 2}$ as a group homomorphism (O'Meara 1963, §55,
p. 137), for a regular space: $\theta(\sigma)$ is the square class of any `c` with `HasSpinorNorm Q σ c`
(`spinorNormHom_apply`). -/
@[kb "omeara1963" "§55, p. 137 (the spinor norm θ : O⁺_n → F/F², a homomorphism)"]
def spinorNormHom (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    orthPlus Q →* Lattices.SqClass F where
  toFun σ := spinorFun Q (σ : V ≃ₗ[F] V)
  map_one' := by
    show spinorFun Q 1 = 1
    rw [spinorFun_eq Q hQ (HasSpinorNorm.one Q), Sp55.sqClassOf_one']
  map_mul' := by
    intro σ τ
    obtain ⟨c, hc0, hc⟩ := exists_hasSpinorNorm_of_mem_orth Q hQ σ.2.1
    obtain ⟨d, hd0, hd⟩ := exists_hasSpinorNorm_of_mem_orth Q hQ τ.2.1
    show spinorFun Q ((σ : V ≃ₗ[F] V) * τ) = spinorFun Q σ * spinorFun Q τ
    rw [spinorFun_eq Q hQ (HasSpinorNorm.mul Q hc hd), spinorFun_eq Q hQ hc, spinorFun_eq Q hQ hd,
      Sp55.sqClassOf_mul' hc0 hd0]

theorem spinorNormHom_apply (hQ : (QuadraticMap.associated Q).Nondegenerate) {σ : orthPlus Q} {c : F}
    (hc : HasSpinorNorm Q (σ : V ≃ₗ[F] V) c) : spinorNormHom Q hQ σ = Lattices.sqClassOf c :=
  Sp55.spinorFun_eq Q hQ hc

/-- **The kernel of the spinor norm is $O'(V)$** (O'Meara 1963, §55, p. 137, definition of $O'_n(V)$). -/
@[kb "omeara1963" "§55, p. 137 (ker θ = O'_n)"]
theorem ker_spinorNormHom (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    (spinorNormHom Q hQ).ker = (orthPrime Q).subgroupOf (orthPlus Q) := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨c, hc0, hc⟩ := exists_hasSpinorNorm_of_mem_orth Q hQ σ.2.1
  rw [spinorNormHom_apply Q hQ hc, Sp55.sqClassOf_eq_one_iff' hc0]
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hc0 (by simpa using hr)
    exact ⟨σ.2, HasSpinorNorm.of_eq_mul_sq Q hc (inv_ne_zero hr0) (by rw [hr]; field_simp)⟩
  · rintro ⟨-, h1⟩
    obtain ⟨s, -, hs⟩ := HasSpinorNorm.eq_mul_sq Q hQ hc h1
    exact ⟨s, by rw [hs]; ring⟩

/-- **55:6a, second part** (O'Meara 1963, 55:6a, p. 140-141): for a regular isotropic quadratic space the spinor
norm $\theta : O^+(V) \to F^\times/F^{\times 2}$ is surjective, with kernel $O'(V)$, and induces an isomorphism
$O^+(V)/O'(V) \cong F^\times/F^{\times 2}$. Here the first statement is `spinorNormHom_surjective_of_isotropic`. -/
@[kb "omeara1963" "§55, 55:6a, p. 141 (θ : O⁺ → F/F² is surjective for isotropic V)"]
theorem spinorNormHom_surjective_of_isotropic (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hiso : ∃ x : V, x ≠ 0 ∧ Q x = 0) : Function.Surjective (spinorNormHom Q hQ) := by
  intro c
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective (s := (powMonoidHom 2 : Fˣ →* Fˣ).range) c
  obtain ⟨σ, hσ, hs⟩ := exists_hasSpinorNorm_of_isotropic Q hQ hiso u.ne_zero
  refine ⟨⟨σ, hσ⟩, ?_⟩
  rw [spinorNormHom_apply Q hQ hs, Sp55.sqClassOf_of_ne_zero' u.ne_zero]
  have e : Units.mk0 (u : F) u.ne_zero = u := Units.ext rfl
  rw [e]
  rfl

/-- **55:6a, the isomorphism** (O'Meara 1963, 55:6a, p. 141): for a regular isotropic space,
$O^+(V)/O'(V) \cong F^\times/F^{\times 2}$ (as the quotient of $O^+(V)$ by the kernel $O'(V)$ of $\theta$). -/
@[kb "omeara1963" "§55, 55:6a, p. 141 (O⁺/O' ≅ F/F² for isotropic V)"]
theorem orthPlus_quotient_equiv_of_isotropic (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hiso : ∃ x : V, x ≠ 0 ∧ Q x = 0) :
    Nonempty ((orthPlus Q ⧸ (spinorNormHom Q hQ).ker) ≃* Lattices.SqClass F) :=
  ⟨QuotientGroup.quotientKerEquivOfSurjective _ (spinorNormHom_surjective_of_isotropic Q hQ hiso)⟩

/-- **§56, item 1 (for $\Omega = O'$)** (O'Meara 1963, §56, p. 141): $-1_V \in \Omega(V)$ if and only if $n$ is
even and $dV = 1$ (modulo squares), when $1 \le n \le 3$ or $V$ is isotropic. (The book's item 1 describes
$Z_n \cap \Omega_n$ for $Z_n = \{\pm 1_V\}$; this is the statement for $-1_V$, the rest being trivial.) -/
@[kb "omeara1963" "§56, p. 141 (Z_n ∩ Ω_n)"]
theorem neg_mem_omega_iff (hQ : (QuadraticMap.associated Q).Nondegenerate) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι F V)
    (hcase : Module.finrank F V ≤ 3 ∨ ∃ x : V, x ≠ 0 ∧ Q x = 0) :
    LinearEquiv.neg F ∈ omega Q ↔ Even (Module.finrank F V) ∧ IsSquare (gram Q b).det := by
  have hΩ : omega Q = orthPrime Q := by
    rcases hcase with h | h
    · exact omega_eq_orthPrime_of_finrank_le_three Q hQ h
    · exact omega_eq_orthPrime_of_isotropic Q hQ h
  rw [hΩ]
  exact neg_mem_orthPrime_iff Q hQ b

/-- **§56, item 2** (O'Meara 1963, §56, p. 141): $O'_n/\Omega_n = 1$, i.e. $\Omega = O'$, when $n \le 3$ or $V$ is
isotropic (55:5, 55:6a). -/
@[kb "omeara1963" "§56, p. 141 (O'_n/Ω_n = 1)"]
theorem omega_eq_orthPrime (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hcase : Module.finrank F V ≤ 3 ∨ ∃ x : V, x ≠ 0 ∧ Q x = 0) : omega Q = orthPrime Q := by
  rcases hcase with h | h
  · exact omega_eq_orthPrime_of_finrank_le_three Q hQ h
  · exact omega_eq_orthPrime_of_isotropic Q hQ h

/-- **§56, item 3** (O'Meara 1963, §56, p. 141): for $n \le 3$, the image of the spinor norm
$\theta(O^+) \subseteq F^\times/F^{\times 2}$ is the group generated by the classes of the products
$\alpha\beta$ with $\alpha, \beta$ nonzero values of $Q$; hence $O^+/O'$ is isomorphic to this group. -/
@[kb "omeara1963" "§56, 3, p. 141 (O⁺/O' ≅ ⟨αβ : α, β ∈ Q(V)⟩ mod F², n ≤ 3)"]
theorem spinorNormHom_range_of_finrank_le_three (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : Module.finrank F V ≤ 3) :
    (spinorNormHom Q hQ).range = Subgroup.closure
      {c | ∃ x y : V, Q x ≠ 0 ∧ Q y ≠ 0 ∧ c = Lattices.sqClassOf (Q x * Q y)} := by
  apply le_antisymm
  · rintro _ ⟨σ, rfl⟩
    obtain ⟨l, hl, h, hlen⟩ := exists_symmetry_prod_eq_length_le_two Q hQ h3 σ.2
    rw [attach_prod_eq_symProd Q l hl] at h
    have hev := even_length_of_mem_orthPlus Q σ.2 l hl h
    have hs : HasSpinorNorm Q (σ : V ≃ₗ[F] V) (l.map Q).prod :=
      (hasSpinorNorm_iff Q).mpr ⟨l, hl, h, 1, one_ne_zero, by simp⟩
    rw [spinorNormHom_apply Q hQ hs]
    rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
    · simp [Sp55.sqClassOf_one']
    · simp at hev
    · apply Subgroup.subset_closure
      exact ⟨x, y, hl x (by simp), hl y (by simp), by simp⟩
    · simp at hlen
  · rw [Subgroup.closure_le]
    rintro _ ⟨x, y, hx, hy, rfl⟩
    refine ⟨⟨_, symmetry_mul_mem_orthPlus Q hx hy⟩, ?_⟩
    rw [spinorNormHom_apply Q hQ (hasSpinorNorm_symmetry_mul Q hx hy)]

/-- **§56, item 3, the isomorphism** (O'Meara 1963, §56, p. 141): for $n \le 3$,
$O^+(V)/O'(V) \cong \theta(O^+(V))$, the group of `spinorNormHom_range_of_finrank_le_three`. -/
theorem orthPlus_quotient_equiv_range (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    Nonempty ((orthPlus Q ⧸ (spinorNormHom Q hQ).ker) ≃* (spinorNormHom Q hQ).range) :=
  ⟨QuotientGroup.quotientKerEquivRange _⟩

end Theta

end QuadFormsKB.OMeara
