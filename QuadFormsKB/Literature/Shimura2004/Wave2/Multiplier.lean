/-
# Shimura 2004, Proposition 8.7: the values of the multiplier $\nu$ on $G^+(V)$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Proposition 8.7 (printed p. 67).
Page numbers are printed pages.

**Statement in the book.** Over a local field $F$ (nonarchimedean, characteristic $0$; here the completion of a
number field at a finite prime), for nondegenerate $(V,\varphi)$ of dimension $n$ with Witt index $r$ and core
dimension $t$: $\nu(G^+(V)) = F^\times$ if $n \ge 3$ or $r > 0$; $\nu(G^+(V)) = N_{K/F}(K^\times)$ if $n = t = 2$
($K$ the discriminant field); $\nu(G^+(V)) = F^{\times 2}$ if $n = 1$.

**Route.** By (3.7) (`spinorNormHom_tau`), $\nu(\xi)F^{\times 2}$ is the spinor norm of $\tau(\xi)$, and
$\tau(G^+(V)) = SO^\varphi(V)$ (Theorem 3.6 (iii)); scalars $c \in F^\times \subset G^+(V)$ have $\nu(c) = c^2$. So
$\nu(G^+(V))$ is the full preimage in $F^\times$ of the spinor norm image $\sigma(SO^\varphi(V))$
(`exists_multiplier_eq_iff`), and Proposition 8.7 is the computation of $\sigma(SO^\varphi(V))$: all of
$F^\times/F^{\times2}$ when $V$ is isotropic (O'Meara 55:6a, any field; `spinorNormHom_surjective_of_isotropic`) or
$F$ is local and $n \ge 3$ (O'Meara 91:6; `spinorNormHom_surjective_of_three_le`), and trivial when $n = 1$.

**Proves** (unconditional; standard axioms only)
* `multiplier_scalar`: $\nu(c) = c^2$ for $c \in F^\times$;
* `exists_multiplier_eq_iff`: $c \in \nu(G^+(V))$ iff $cF^{\times2}$ is a spinor norm of $SO^\varphi(V)$;
* Proposition 8.7, the case $r > 0$ (over every field of characteristic $\ne 2$): `prop_8_7_isotropic`;
  the case $n \ge 3$ over a local field: `prop_8_7_local`; the case $n = 1$: `prop_8_7_dim_one`.
* the case $n = t = 2$, in the form $\nu(G^+(V)) = \{a^2 + \alpha\beta b^2\} \cap F^\times = N_{K/F}(K^\times)$ for
  an orthogonal basis $e_1, e_2$ with $\varphi[e_i] = \alpha, \beta$ (`prop_8_7_binary`, over every field).
-/
import QuadFormsKB.Literature.Shimura2004.Wave2.CliffordLemmas
import QuadFormsKB.Literature.OMeara.Sec91Local
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

section General

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

local notation "A" => CliffordAlgebra Q

/-- A scalar $c \in F^\times$, as an element of $G^+(V)$. -/
def scalarM0 (c : Fˣ) : M0 Q := ⟨Units.map (algebraMap F A).toMonoidHom c, scalar_mem_M0 c⟩

/-- $\nu(c) = c^2$ for a scalar $c \in F^\times \subset G^+(V)$. -/
theorem multiplier_scalar (hQ : (QuadraticMap.associated Q).Nondegenerate) (c : Fˣ) :
    multiplier hQ ⟨(scalarM0 c : M0 Q), M0_le_homogeneous (scalarM0 c).2⟩ = c ^ 2 := by
  ext
  apply (algebraMap _ (CliffordAlgebra Q)).injective
  rw [algebraMap_multiplier]
  change algebraMap F A (c : F) * reverse (algebraMap F A (c : F)) = _
  rw [reverse.commutes, ← map_mul]
  simp [sq]

/-- **$\nu(G^+(V))$ is the preimage of the spinor norm image**: $c \in \nu(G^+(V))$ if and only if the square class
of $c$ is the spinor norm of some $\alpha \in SO^\varphi(V)$ (from (3.7) and Theorem 3.6 (iii)). -/
theorem exists_multiplier_eq_iff (hQ : (QuadraticMap.associated Q).Nondegenerate) (c : Fˣ) :
    (∃ ξ : M0 Q, multiplier hQ ⟨ξ, M0_le_homogeneous ξ.2⟩ = c) ↔
      Lattices.sqClassOf (c : F) ∈ Set.range (spinorNormHom Q hQ) := by
  constructor
  · rintro ⟨ξ, hξ⟩
    exact ⟨_, by rw [spinorNormHom_tau hQ ξ, hξ]⟩
  · rintro ⟨⟨α, hα⟩, hσ⟩
    obtain ⟨ξ0, hξ0⟩ := exists_tau_eq hQ hα
    have h1 := spinorNormHom_tau hQ ξ0
    have heq : (⟨tau (Subgroup.inclusion M0_le ξ0), tau_mem_orthPlus hQ ξ0⟩ : orthPlus Q) = ⟨α, hα⟩ :=
      Subtype.ext hξ0
    rw [heq, hσ] at h1
    set m := multiplier hQ ⟨ξ0, M0_le_homogeneous ξ0.2⟩
    -- the square class of `m / c` is trivial
    have hsq : IsSquare ((m : F) * (c : F)⁻¹) := by
      rw [← Sp55.sqClassOf_eq_one_iff' (mul_ne_zero m.ne_zero (inv_ne_zero c.ne_zero)),
        Sp55.sqClassOf_mul' m.ne_zero (inv_ne_zero c.ne_zero), sqClassOf_inv c.ne_zero, ← h1]
      rw [← Sp55.sqClassOf_mul' c.ne_zero c.ne_zero, Sp55.sqClassOf_eq_one_iff' (mul_ne_zero c.ne_zero c.ne_zero)]
      exact ⟨c, rfl⟩
    obtain ⟨d, hd⟩ := hsq
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp at hd
    refine ⟨ξ0 * scalarM0 (Units.mk0 d hd0)⁻¹, ?_⟩
    have hmul := map_mul (multiplier hQ) ⟨ξ0, M0_le_homogeneous ξ0.2⟩
      ⟨(scalarM0 (Units.mk0 d hd0)⁻¹ : M0 Q), M0_le_homogeneous (scalarM0 (Units.mk0 d hd0)⁻¹).2⟩
    have hx : (⟨((ξ0 * scalarM0 (Units.mk0 d hd0)⁻¹ : M0 Q) : (CliffordAlgebra Q)ˣ),
        M0_le_homogeneous (ξ0 * scalarM0 (Units.mk0 d hd0)⁻¹).2⟩ : homogeneousCliffordGroup Q) =
        ⟨ξ0, M0_le_homogeneous ξ0.2⟩ *
          ⟨(scalarM0 (Units.mk0 d hd0)⁻¹ : M0 Q), M0_le_homogeneous (scalarM0 (Units.mk0 d hd0)⁻¹).2⟩ := rfl
    rw [hx, hmul, multiplier_scalar]
    ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0]
    have hm : (m : F) = (c : F) * (d * d) := by
      rw [← hd]; field_simp
    change (m : F) * _ = _
    rw [hm]
    field_simp

/-- **Proposition 8.7**, case $r > 0$ (Shimura 2004, p. 67): if $\varphi$ is nondegenerate and isotropic, then
$\nu(G^+(V)) = F^\times$. (Over every field of characteristic $\ne 2$, via O'Meara 55:6a.) -/
@[kb "shimura2004" "Prop. 8.7, p. 67 (ν(G⁺(V)) = F^× if r > 0)"]
theorem prop_8_7_isotropic (hQ : (QuadraticMap.associated Q).Nondegenerate) (hiso : ∃ x : V, x ≠ 0 ∧ Q x = 0)
    (c : Fˣ) : ∃ ξ : M0 Q, multiplier hQ ⟨ξ, M0_le_homogeneous ξ.2⟩ = c :=
  (exists_multiplier_eq_iff hQ c).2 (spinorNormHom_surjective_of_isotropic Q hQ hiso _)

/-- In dimension $1$, $SO^\varphi(V) = \{1\}$. -/
theorem eq_one_of_mem_orthPlus_of_finrank_one (hn : finrank F V = 1) {α : V ≃ₗ[F] V} (hα : α ∈ orthPlus Q) :
    α = 1 := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hn
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hspan := (finrank_eq_one_iff_of_nonzero' v hv).1 hn
  obtain ⟨l, hl⟩ := hspan (α v)
  have hαs : (α : V →ₗ[F] V) = l • LinearMap.id := by
    ext x
    obtain ⟨c, rfl⟩ := hspan x
    simp [map_smul, ← hl, smul_smul, mul_comm]
  have hdet : LinearMap.det (α : V →ₗ[F] V) = 1 := by
    have h : LinearEquiv.det α = 1 := hα.2
    rw [← LinearEquiv.coe_det, h, Units.val_one]
  rw [hαs, LinearMap.det_smul, LinearMap.det_id, hn, pow_one, mul_one] at hdet
  ext x
  have := congrArg (fun f : V →ₗ[F] V => f x) hαs
  simpa [hdet] using this

/-- **Proposition 8.7**, case $n = 1$ (Shimura 2004, p. 67): if $\dim V = 1$, $\nu(G^+(V)) = F^{\times2}$. -/
@[kb "shimura2004" "Prop. 8.7, p. 67 (ν(G⁺(V)) = F^{×2} if n = 1)"]
theorem prop_8_7_dim_one (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : finrank F V = 1) (c : Fˣ) :
    (∃ ξ : M0 Q, multiplier hQ ⟨ξ, M0_le_homogeneous ξ.2⟩ = c) ↔ IsSquare (c : F) := by
  rw [exists_multiplier_eq_iff, ← Sp55.sqClassOf_eq_one_iff' c.ne_zero]
  constructor
  · rintro ⟨⟨α, hα⟩, h⟩
    rw [← h]
    have : (⟨α, hα⟩ : orthPlus Q) = 1 := Subtype.ext (eq_one_of_mem_orthPlus_of_finrank_one hn hα)
    rw [this, map_one]
  · intro h
    exact ⟨1, by rw [map_one, h]⟩

/-- $(x_1\cdots x_r)(x_1\cdots x_r)^* = \varphi[x_1]\cdots\varphi[x_r]$ (3.4a). -/
theorem prod_mul_reverse_prod' (l : List V) :
    (l.map (ι Q)).prod * reverse (l.map (ι Q)).prod = algebraMap F A (l.map Q).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.prod_cons, reverse.map_mul, reverse_ι, mul_assoc, ← mul_assoc _ (reverse _), ih,
      Algebra.commutes, ← mul_assoc, ι_sq_scalar, ← map_mul, List.map_cons, List.prod_cons]

/-- The norm values $a^2 + \delta b^2$ ($\delta = \alpha\beta$) are closed under multiplication. -/
theorem norm_mul_mem {δ x y : F} (hx : ∃ a b : F, x = a ^ 2 + δ * b ^ 2) (hy : ∃ a b : F, y = a ^ 2 + δ * b ^ 2) :
    ∃ a b : F, x * y = a ^ 2 + δ * b ^ 2 := by
  obtain ⟨a, b, rfl⟩ := hx
  obtain ⟨c, d, rfl⟩ := hy
  exact ⟨a * c - δ * b * d, a * d + b * c, by ring⟩

/-- **Proposition 8.7**, case $n = t = 2$ (Shimura 2004, p. 67), in the form valid over every field of
characteristic $\ne 2$: if $V = Fe_1 \oplus Fe_2$ with $e_1 \perp e_2$, $\varphi[e_1] = \alpha$,
$\varphi[e_2] = \beta$, then $\nu(G^+(V)) = \{a^2 + \alpha\beta b^2\} \cap F^\times$, which is the norm group
$N_{K/F}(K^\times)$ of the discriminant algebra $K = F(\sqrt{-\alpha\beta})$ (for anisotropic $V$, $K$ is the
discriminant field of Shimura's statement). Proof: "$\subseteq$" by Theorem 3.7 (i), (3.4a) and
$\varphi[x]\varphi[y] = (\alpha x_1y_1 + \beta x_2y_2)^2 + \alpha\beta(x_1y_2 - x_2y_1)^2$; "$\supseteq$" by
Lemma 3.11: $\nu(a + be_1e_2) = a^2 + \alpha\beta b^2$. -/
@[kb "shimura2004" "Prop. 8.7, p. 67 (ν(G⁺(V)) = N_{K/F}(K^×) if n = t = 2)"]
theorem prop_8_7_binary (hQ : (QuadraticMap.associated Q).Nondegenerate) {e₁ e₂ : V}
    (he₁ : Q e₁ ≠ 0) (horth : QuadraticMap.polar Q e₁ e₂ = 0) (hspan : Submodule.span F {e₁, e₂} = ⊤) (c : Fˣ) :
    (∃ ξ : M0 Q, multiplier hQ ⟨ξ, M0_le_homogeneous ξ.2⟩ = c) ↔
      ∃ a b : F, (c : F) = a ^ 2 + Q e₁ * Q e₂ * b ^ 2 := by
  set δ := Q e₁ * Q e₂
  have hQx : ∀ x : V, ∃ x₁ x₂ : F, Q x = x₁ ^ 2 * Q e₁ + x₂ ^ 2 * Q e₂ ∧ x = x₁ • e₁ + x₂ • e₂ := by
    intro x
    have hx : x ∈ Submodule.span F {e₁, e₂} := hspan ▸ Submodule.mem_top
    obtain ⟨x₁, x₂, rfl⟩ := Submodule.mem_span_pair.1 hx
    refine ⟨x₁, x₂, ?_, rfl⟩
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_right, horth]
    simp [smul_eq_mul]; ring
  have hpair : ∀ x y : V, ∃ a b : F, Q x * Q y = a ^ 2 + δ * b ^ 2 := by
    intro x y
    obtain ⟨x₁, x₂, hx, -⟩ := hQx x
    obtain ⟨y₁, y₂, hy, -⟩ := hQx y
    exact ⟨Q e₁ * x₁ * y₁ + Q e₂ * x₂ * y₂, x₁ * y₂ - x₂ * y₁, by rw [hx, hy]; ring⟩
  have hlist : ∀ k : ℕ, ∀ l : List V, l.length = 2 * k → ∃ a b : F, (l.map Q).prod = a ^ 2 + δ * b ^ 2 := by
    intro k
    induction k with
    | zero =>
      intro l hl
      obtain rfl : l = [] := List.length_eq_zero_iff.1 (by simpa using hl)
      exact ⟨1, 0, by simp⟩
    | succ k ih =>
      intro l hl
      match l, hl with
      | x :: y :: t, hl =>
        have ht : t.length = 2 * k := by simp at hl; omega
        obtain ⟨a, b, hab⟩ := norm_mul_mem (hpair x y) (ih t ht)
        exact ⟨a, b, by rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ← mul_assoc, hab]⟩
  constructor
  · rintro ⟨ξ, hξ⟩
    have : Nontrivial V := ⟨⟨e₁, 0, fun h => he₁ (by rw [h, QuadraticMap.map_zero])⟩⟩
    obtain ⟨l, hl, hev, hal⟩ := (mem_M0_iff_exists_vecProd hQ (ξ : (CliffordAlgebra Q)ˣ)).1 ξ.2
    have hν : (multiplier hQ ⟨ξ, M0_le_homogeneous ξ.2⟩ : F) = (l.map Q).prod := by
      apply (algebraMap F A).injective
      rw [algebraMap_multiplier]
      change ((ξ : (CliffordAlgebra Q)ˣ) : A) * reverse ((ξ : (CliffordAlgebra Q)ˣ) : A) = _
      rw [hal, prod_mul_reverse_prod']
    obtain ⟨k, hk⟩ := hev
    rw [← hξ, hν]
    exact hlist k l (by omega)
  · rintro ⟨a, b, hab⟩
    have hne : a ^ 2 + a * QuadraticMap.polar Q (b • e₁) e₂ + Q (b • e₁) * Q e₂ ≠ 0 := by
      rw [QuadraticMap.polar_smul_left, horth, QuadraticMap.map_smul]
      convert c.ne_zero using 1
      rw [hab]; simp [smul_eq_mul, δ]; ring
    obtain ⟨u, hu, huM⟩ := rxy_mem_M0 a (b • e₁) e₂ hne
    refine ⟨⟨u, huM⟩, ?_⟩
    ext
    apply (algebraMap F A).injective
    rw [algebraMap_multiplier]
    change (u : A) * reverse (u : A) = _
    rw [hu, mul_reverse_rxy, QuadraticMap.polar_smul_left, horth, QuadraticMap.map_smul, hab]
    congr 1
    simp [smul_eq_mul, δ]; ring

end General

section Local

variable {K : Type} [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
variable {V : Type*} [AddCommGroup V] [Module (v.adicCompletion K) V] [FiniteDimensional (v.adicCompletion K) V]
  {Q : QuadraticForm (v.adicCompletion K) V}

/-- **Proposition 8.7**, case $n \ge 3$ (Shimura 2004, p. 67): over the completion $F = K_v$ of a number field at a
finite prime, if $\varphi$ is nondegenerate and $\dim V \ge 3$, then $\nu(G^+(V)) = F^\times$ (via O'Meara 91:6). -/
@[kb "shimura2004" "Prop. 8.7, p. 67 (ν(G⁺(V)) = F^× if n ≥ 3, F local)"]
theorem prop_8_7_local (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : 3 ≤ finrank (v.adicCompletion K) V) (c : (v.adicCompletion K)ˣ) :
    ∃ ξ : M0 Q, multiplier hQ ⟨ξ, M0_le_homogeneous ξ.2⟩ = c :=
  (exists_multiplier_eq_iff hQ c).2 (spinorNormHom_surjective_of_three_le v Q hQ h3 _)

end Local

end QuadFormsKB.Shimura2004
