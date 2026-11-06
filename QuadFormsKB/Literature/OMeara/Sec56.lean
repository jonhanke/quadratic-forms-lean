/-
# O'Meara §55 (remaining running text) and §56: the centre $Z_n$, scaling, and the normal series

**Setting.** As in `Sec55.lean`: a field $F$ of characteristic $\ne 2$, a finite-dimensional quadratic space $(V, Q)$
over $F$; *regular* means `(QuadraticMap.associated Q).Nondegenerate`. Notation of the library: `orth Q` is $O_n(V)$,
`orthPlus Q` is $O^+_n(V)$, `orthPrime Q` is $O'_n(V)$, `omega Q` is $\Omega_n(V)$, `spinorNormHom Q hQ` is
$\theta : O^+_n \to F^\times/F^{\times 2}$ (all subgroups of `V ≃ₗ[F] V`).

**Defines**
* `zCenter Q`: O'Meara's $Z_n(V)$ (§43E, p. 108), the centre of $O_n(V)$, as a subgroup of `V ≃ₗ[F] V`;
* `ZassenhausSpinorNormFormula F`: the named statement of Zassenhaus' formula of the footnote on p. 137
  (quoted without proof by O'Meara), $\theta(\sigma) = \det\bigl(\tfrac12(1_V+\sigma)\bigr)$ for a rotation $\sigma$
  with $\det(1_V+\sigma) \ne 0$;
* `ArtinSimplicity F`: the named statement of Artin's theorem quoted in §56 (p. 141, without proof):
  $\Omega_n/\Omega_n\cap Z_n$ is simple when $V$ is regular, isotropic, $n \ge 5$.

**Proves**
* **55:1** with the general hyperbolic plane $H \cong \begin{pmatrix}0&\gamma\\\gamma&0\end{pmatrix}$ (pp. 138-139, read
  from the page image): `hyperbolic_Q_sub_smul_gamma`, `hyperbolic_symmetry_gamma`, `hyperbolic_rotation_gamma`
  (`Sec55.lean` has the case $\gamma = 1$);
* scaling (p. 138): `omega_smul`, `zCenter_smul` ($\Omega_n$ and $Z_n$ are unchanged when $Q$ is scaled; the
  cases $O_n$, $O^+_n$, $O'_n$ are `orth_smul`, `orthPlus_smul`, `orthPrime_smul` in `Sec55.lean`);
* **55:6a (iii)** (p. 141): `orthPlus_quotient_omega_equiv_of_isotropic`, $O^+_n/\Omega_n \cong F^\times/F^{\times 2}$
  for a regular isotropic space;
* **§56, the normal series** (p. 141): `normal_series`,
  $1 \lhd \Omega_n\cap Z_n \lhd \Omega_n \lhd O'_n \lhd O^+_n \lhd O_n$ (inclusions and normality of each term in the
  next; the instances `omega_subgroupOf_orthPlus_normal`, `omega_inf_zCenter_subgroupOf_normal`).
-/
import QuadFormsKB.Literature.OMeara.Sec55
import QuadFormsKB.Literature.OMeara.Sec43E

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

open Sp55

section Z56

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **$Z_n(V)$, the centre of $O_n(V)$** (O'Meara 1963, §43E, p. 108): the isometries $\sigma \in O_n(V)$ that
commute with every element of $O_n(V)$, as a subgroup of `V ≃ₗ[F] V` (like `orth Q`). By 43:12
(`mem_center_iff`) it is $\{\pm 1_V\}$ except for a hyperbolic plane over a field of three elements. -/
@[kb "omeara1963" "§43E, p. 108 (Z_n, the center of O_n)"]
def zCenter : Subgroup (V ≃ₗ[F] V) where
  carrier := {σ | σ ∈ orth Q ∧ ∀ ρ ∈ orth Q, σ * ρ = ρ * σ}
  mul_mem' := fun {a b} ha hb =>
    ⟨(orth Q).mul_mem ha.1 hb.1, fun ρ hρ => by rw [mul_assoc, hb.2 ρ hρ, ← mul_assoc, ha.2 ρ hρ, mul_assoc]⟩
  one_mem' := ⟨(orth Q).one_mem, fun ρ _ => by rw [one_mul, mul_one]⟩
  inv_mem' := fun {a} ha => ⟨(orth Q).inv_mem ha.1, fun ρ hρ => by
    have h := ha.2 ρ hρ
    calc a⁻¹ * ρ = a⁻¹ * (ρ * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * ρ) * a⁻¹ := by rw [h]
      _ = ρ * a⁻¹ := by group⟩

theorem zCenter_le_orth : zCenter Q ≤ orth Q := fun _ h => h.1

/-- $\pm 1_V \in Z_n$. -/
theorem neg_mem_zCenter : LinearEquiv.neg F ∈ zCenter Q := by
  refine ⟨fun x => by simp, fun ρ _ => ?_⟩
  ext x
  simp

/-- **$\Omega_n$ is unchanged by scaling** (O'Meara 1963, §55, p. 138): for $\alpha \ne 0$,
$\Omega_n(V^\alpha) = \Omega_n(V)$, since $O_n(V^\alpha) = O_n(V)$ (`orth_smul`). -/
@[kb "omeara1963" "§55, p. 138 (Ω_n unchanged on scaling V by α)"]
theorem omega_smul {a : F} (ha : a ≠ 0) : omega (a • Q) = omega Q := by
  unfold omega
  rw [orth_smul Q ha]

/-- **$Z_n$ is unchanged by scaling** (O'Meara 1963, §55, p. 138): for $\alpha \ne 0$, $Z_n(V^\alpha) = Z_n(V)$. -/
@[kb "omeara1963" "§55, p. 138 (Z_n unchanged on scaling V by α)"]
theorem zCenter_smul {a : F} (ha : a ≠ 0) : zCenter (a • Q) = zCenter Q := by
  ext σ
  simp only [zCenter, Subgroup.mem_mk, orth_smul Q ha]

/-- A subgroup normal in $O_n$ is normal in every subgroup of $O_n$. -/
theorem subgroupOf_normal_of_le {H K : Subgroup (V ≃ₗ[F] V)} (hH : (H.subgroupOf (orth Q)).Normal)
    (hK : K ≤ orth Q) : (H.subgroupOf K).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have := hH.conj_mem ⟨n, hK n.2⟩ (by rwa [Subgroup.mem_subgroupOf]) ⟨g, hK g.2⟩
  rwa [Subgroup.mem_subgroupOf] at this

instance omega_subgroupOf_orthPlus_normal : ((omega Q).subgroupOf (orthPlus Q)).Normal :=
  subgroupOf_normal_of_le Q (omega_subgroupOf_normal Q) inf_le_left

/-- $\Omega_n \cap Z_n$ is normal in $\Omega_n$ (its elements commute with all of $O_n$). -/
instance omega_inf_zCenter_subgroupOf_normal : ((omega Q ⊓ zCenter Q).subgroupOf (omega Q)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg : (g : V ≃ₗ[F] V) ∈ orth Q := by
    have : omega Q ≤ orth Q := by
      unfold omega
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact (orth Q).mul_mem ((orth Q).mul_mem ((orth Q).mul_mem ha hb) ((orth Q).inv_mem ha))
        ((orth Q).inv_mem hb)
    exact this g.2
  have e : ((g * n * g⁻¹ : omega Q) : V ≃ₗ[F] V) = (n : V ≃ₗ[F] V) := by
    show (g : V ≃ₗ[F] V) * n * (g : V ≃ₗ[F] V)⁻¹ = n
    rw [← hn.2.2 _ hg]
    group
  rw [e]
  exact hn

/-- **55:6a (iii)** (O'Meara 1963, 55:6a, p. 141): for a regular isotropic space, $O^+_n/\Omega_n \cong
F^\times/F^{\times 2}$. (By 55:6a (i) $\Omega_n = O'_n$, `omega_eq_orthPrime_of_isotropic`, and by (ii) the spinor
norm induces $O^+_n/O'_n \cong F^\times/F^{\times 2}$, `orthPlus_quotient_equiv_of_isotropic`.) Here the quotient is
$O^+_n$ modulo $\Omega_n$ viewed as a subgroup of $O^+_n$. -/
@[kb "omeara1963" "§55, 55:6a, p. 141 (O⁺_n/Ω_n ≅ F/F² for isotropic V)"]
theorem orthPlus_quotient_omega_equiv_of_isotropic (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hiso : ∃ x : V, x ≠ 0 ∧ Q x = 0) :
    Nonempty ((orthPlus Q ⧸ (omega Q).subgroupOf (orthPlus Q)) ≃* Lattices.SqClass F) := by
  have h : (omega Q).subgroupOf (orthPlus Q) = (spinorNormHom Q hQ).ker := by
    rw [ker_spinorNormHom, omega_eq_orthPrime_of_isotropic Q hQ hiso]
  obtain ⟨e⟩ := orthPlus_quotient_equiv_of_isotropic Q hQ hiso
  exact ⟨(QuotientGroup.quotientMulEquivOfEq h).trans e⟩

/-- **§56, the normal series** (O'Meara 1963, §56, p. 141): for a regular space,
$$1 \lhd \Omega_n\cap Z_n \lhd \Omega_n \lhd O'_n \lhd O^+_n \lhd O_n,$$
i.e. the inclusions $\Omega_n\cap Z_n \le \Omega_n \le O'_n \le O^+_n \le O_n$ hold and each term is normal in the
next. (In fact $\Omega_n$, $O'_n$, $O^+_n$ are normal in $O_n$ itself: `omega_subgroupOf_normal`,
`orthPrime_subgroupOf_normal`, `orthPlus_subgroupOf_normal`.) -/
@[kb "omeara1963" "§56, p. 141 (the normal series 1 ◁ Ω_n ∩ Z_n ◁ Ω_n ◁ O'_n ◁ O⁺_n ◁ O_n)"]
theorem normal_series (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    (omega Q ⊓ zCenter Q ≤ omega Q ∧ omega Q ≤ orthPrime Q ∧ orthPrime Q ≤ orthPlus Q ∧
      orthPlus Q ≤ orth Q) ∧
    ((omega Q ⊓ zCenter Q).subgroupOf (omega Q)).Normal ∧ ((omega Q).subgroupOf (orthPrime Q)).Normal ∧
      ((orthPrime Q).subgroupOf (orthPlus Q)).Normal ∧ ((orthPlus Q).subgroupOf (orth Q)).Normal := by
  have hPlus : orthPlus Q ≤ orth Q := inf_le_left
  have hPrime : orthPrime Q ≤ orthPlus Q := orthPrime_le_orthPlus Q
  refine ⟨⟨inf_le_left, omega_le_orthPrime Q hQ, hPrime, hPlus⟩, ?_, ?_, ?_, orthPlus_subgroupOf_normal Q⟩
  · exact omega_inf_zCenter_subgroupOf_normal Q
  · exact subgroupOf_normal_of_le Q (omega_subgroupOf_normal Q) (hPlus.trans' hPrime)
  · exact subgroupOf_normal_of_le Q (orthPrime_subgroupOf_normal Q) hPlus

end Z56

/-! ### 55:1 with the general hyperbolic plane $H \cong \begin{pmatrix}0&\gamma\\\gamma&0\end{pmatrix}$ -/

section Hyperbolic55

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) {x y : V} {γ : F}

/-- **55:1, the value** (O'Meara 1963, 55:1, p. 138, read from the page image): in the hyperbolic plane
$H = Fx + Fy \cong \begin{pmatrix}0&\gamma\\\gamma&0\end{pmatrix}$ in the base $x, y$ ($Q(x) = Q(y) = 0$,
$B(x,y) = \gamma$), $Q(x - \alpha y) = -2\alpha\gamma$. (`hyperbolic_Q_sub_smul` in `Sec55.lean` is the case
$\gamma = 1$.) -/
@[kb "omeara1963" "§55, 55:1, p. 138 (H ≅ (0 γ; γ 0): Q(x − αy) = −2αγ)"]
theorem hyperbolic_Q_sub_smul_gamma (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = γ) (a : F) :
    Q (x - a • y) = -2 * a * γ := by
  rw [sub_eq_add_neg, ← neg_smul, Q_add, Q_smul, bil_smul_right, hxy, hy, hx]
  ring

/-- **55:1, the symmetry** (O'Meara 1963, 55:1, p. 138, read from the page image): in
$H \cong \begin{pmatrix}0&\gamma\\\gamma&0\end{pmatrix}$ ($\gamma \ne 0$) and for $\alpha \ne 0$, the symmetry
$\tau = \tau_{x-\alpha y}$ satisfies $\tau x = \alpha y$, $\tau y = \alpha^{-1}x$, and
$\theta(\tau) = Q(x - \alpha y) = -2\alpha\gamma$. -/
@[kb "omeara1963" "§55, 55:1, p. 138 (τ_{x−αy}: x ↦ αy, y ↦ α⁻¹x, θ(τ) = −2αγ)"]
theorem hyperbolic_symmetry_gamma (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = γ) (hγ : γ ≠ 0)
    {a : F} (ha : a ≠ 0) {u : V} (hu : u = x - a • y) (h : Q u ≠ 0) :
    symmetry Q u h x = a • y ∧ symmetry Q u h y = a⁻¹ • x ∧
      HasSpinorNorm Q (symmetry Q u h) (-2 * a * γ) := by
  have hQu : Q u = -2 * a * γ := by rw [hu]; exact hyperbolic_Q_sub_smul_gamma Q hx hy hxy a
  have hbx : bil Q x u = -a * γ := by
    rw [hu, bil_sub_right, bil_smul_right, hxy, bil_self, hx]; ring
  have hby : bil Q y u = γ := by
    rw [hu, bil_sub_right, bil_smul_right, bil_comm Q y x, hxy, bil_self, hy]; ring
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · rw [symmetry_apply, hbx, hQu]
    have : 2 * (-a * γ) / (-2 * a * γ) = 1 := by field_simp
    rw [this, one_smul, hu, sub_sub_cancel]
  · rw [symmetry_apply, hby, hQu]
    have : 2 * γ / (-2 * a * γ) = -a⁻¹ := by field_simp
    rw [this, hu, neg_smul, sub_neg_eq_add, smul_sub, smul_smul, inv_mul_cancel₀ ha, one_smul]
    abel
  · have := hasSpinorNorm_symmetry Q h
    rwa [hQu] at this

/-- **55:1, the rotation** (O'Meara 1963, 55:1, p. 139, read from the page image): in
$H \cong \begin{pmatrix}0&\gamma\\\gamma&0\end{pmatrix}$ ($\gamma \ne 0$) and for $\alpha \ne 0$, the rotation
$\sigma = \tau_{x-y}\tau_{x-\alpha y}$ is described by $\sigma x = \alpha x$, $\sigma y = \alpha^{-1}y$, and
$\theta(\sigma) = (-2\gamma)(-2\alpha\gamma) = \alpha$ modulo squares. -/
@[kb "omeara1963" "§55, 55:1, p. 139 (σx = αx, σy = α⁻¹y: θ(σ) = (−2γ)(−2αγ) = α)"]
theorem hyperbolic_rotation_gamma (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = γ) (hγ : γ ≠ 0)
    {a : F} (ha : a ≠ 0) {u v : V} (hu : u = x - y) (hv : v = x - a • y) (hu0 : Q u ≠ 0) (hv0 : Q v ≠ 0) :
    symmetry Q u hu0 * symmetry Q v hv0 ∈ orthPlus Q ∧
      (symmetry Q u hu0 * symmetry Q v hv0) x = a • x ∧
      (symmetry Q u hu0 * symmetry Q v hv0) y = a⁻¹ • y ∧
      HasSpinorNorm Q (symmetry Q u hu0 * symmetry Q v hv0) a := by
  obtain ⟨hv1, hv2, hv3⟩ := hyperbolic_symmetry_gamma Q hx hy hxy hγ ha hv hv0
  obtain ⟨hu1, hu2, hu3⟩ := hyperbolic_symmetry_gamma Q hx hy hxy hγ one_ne_zero (by rw [hu, one_smul]) hu0
  refine ⟨symmetry_mul_mem_orthPlus Q hu0 hv0, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hv1, map_smul, hu2]; simp
  · rw [LinearEquiv.mul_apply, hv2, map_smul, hu1]; simp
  · refine HasSpinorNorm.of_eq_mul_sq Q (HasSpinorNorm.mul Q hu3 hv3) (inv_ne_zero (mul_ne_zero two_ne_zero hγ)) ?_
    field_simp

end Hyperbolic55

/-! ### Named statements quoted without proof -/

section Named

universe u

/-- **Zassenhaus' formula for the spinor norm** (O'Meara 1963, §55, footnote on p. 137, quoted without proof from
unpublished results of Zassenhaus): for a regular quadratic space $V$ over $F$ ($\operatorname{char} F \ne 2$) and a
rotation $\sigma \in O^+_n(V)$ with $\det(1_V + \sigma) \ne 0$,
$$\theta(\sigma) = \det\Bigl(\frac{1_V + \sigma}{2}\Bigr) \quad\text{in } F^\times/F^{\times 2}.$$
This is a *named statement* (a cited result assumed, not proved here; it is not used by any proof of the library).
The book's formula was confirmed from the page image (2026-10-29). Spaces range over `Type u`. -/
@[kb "omeara1963" "§55, footnote, p. 137 (Zassenhaus: θ(σ) = det((1_V + σ)/2) when det(1_V + σ) ≠ 0)"]
structure ZassenhausSpinorNormFormula (F : Type u) [Field F] [Invertible (2 : F)] : Prop where
  formula : ∀ (V : Type u) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) (σ : orthPlus Q),
    LinearMap.det ((1 : V →ₗ[F] V) + (σ : V ≃ₗ[F] V).toLinearMap) ≠ 0 →
    spinorNormHom Q hQ σ =
      Lattices.sqClassOf (LinearMap.det ((2 : F)⁻¹ • ((1 : V →ₗ[F] V) + (σ : V ≃ₗ[F] V).toLinearMap)))

/-- **Artin's simplicity theorem** (O'Meara 1963, §56, p. 141, quoted without proof; the footnote refers to
E. Artin, *Geometric algebra*, 1957): for a regular isotropic quadratic space $V$ of dimension $n \ge 5$ over $F$
($\operatorname{char} F \ne 2$), the group $\Omega_n/\Omega_n\cap Z_n$ is simple. Here $\Omega_n \cap Z_n$ is taken as a
subgroup of $\Omega_n$. This is a *named statement* (a cited result assumed, not proved here; nothing in the library
depends on it). Spaces range over `Type u`. -/
@[kb "omeara1963" "§56, p. 141 (Artin: Ω_n/Ω_n ∩ Z_n is simple, V isotropic, n ≥ 5)"]
structure ArtinSimplicity (F : Type u) [Field F] [Invertible (2 : F)] : Prop where
  simple : ∀ (V : Type u) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V),
    (QuadraticMap.associated Q).Nondegenerate → (∃ x : V, x ≠ 0 ∧ Q x = 0) → 5 ≤ Module.finrank F V →
    IsSimpleGroup (omega Q ⧸ (omega Q ⊓ zCenter Q).subgroupOf (omega Q))

end Named

end QuadFormsKB.OMeara
