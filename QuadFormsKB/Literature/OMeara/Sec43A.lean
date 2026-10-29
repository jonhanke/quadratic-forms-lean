import QuadFormsKB.Literature.OMeara.Sec42Iso
import QuadFormsKB.Literature.OMeara.Sec91

/-!
# O'Meara §43A, §43B, §43E: rotations, prolongations, fixed spaces, isometries fixing all lines
(43:1, 43:2, 43:3a, 43:9)

**Setting** (as in `Sec42.lean` and `Sec43CD.lean`): $F$ a field with $2 \ne 0$, $(V, Q)$ a finite-dimensional
quadratic space over $F$, $B$ = `bil Q`, *regular* = `(QuadraticMap.associated Q).Nondegenerate`, $O(V)$ =
`orth Q`, $\tau_u$ = `symmetry Q u hu` for $Q(u) \ne 0$. A *hyperplane* $U$ is a subspace with
$\dim U + 1 = \dim V$; the *fixed space* of $\sigma$ is $\ker(\sigma - 1) = \{x : \sigma x = x\}$.

**Proves** (O'Meara 1973 printing, Chapter IV, §43, pp. 101–108):
* `det_eq_one_of_fix_totallyIsotropic` (**43:1**): an isometry of a regular space that is the identity on a totally
  isotropic subspace $M$ with $2\dim M = \dim V$ (a maximal totally isotropic subspace of a hyperbolic space) is a
  rotation;
* `prolongation_eq_of_not_regular`, `prolongation_eq_or_mul_symmetry` (**43:2**, the uniqueness part): two elements of
  $O(V)$ that agree on a hyperplane $U$ are equal if $U$ is not regular, and differ by the symmetry $\tau_z$
  ($Fz = U^\perp$) if $U$ is regular (the existence of one prolongation is Witt's theorem 42:17, in Mathlib as
  `QuadraticForm.exists_isometryEquiv_extend_of_nondegenerate`, not restated here);
* `finrank_le_finrank_fixed_add_length` (**43:3a**): if $\sigma$ is a product of $r$ symmetries then its fixed space has
  dimension at least $n - r$;
* `eq_one_or_neg_of_forall_mem_line` (**43:9**): an isometry of a regular space that leaves every line fixed is
  $\pm 1_V$.

**Proof notes.** 43:1 follows O'Meara's argument ($\sigma y - y \in M^\perp = M$), with the determinant computed from
the flag $M \subseteq V$ as in `Sec43CD.lean`. 43:2 for a non-regular hyperplane uses $\dim U^\perp = 1$ (42:6) and a
vector $w \ne 0$ of $\operatorname{rad} U$ in place of O'Meara's radical splitting. 43:9 uses Mathlib's
`LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent`.

**Conventions.** Products of symmetries are `List.prod` of `symmetry Q u hu` over a list of anisotropic vectors
(`{u : V // Q u ≠ 0}`), as in `Sec43CD.lean`; $-1_V$ is stated pointwise ($\sigma x = -x$ for all $x$).
-/

open QuadraticMap Submodule Module LinearMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Sec43A

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)

/-- A hyperplane and a vector outside it span the space. -/
theorem sup_span_eq_top_of_hyperplane {U : Submodule F V} (hU : finrank F U + 1 = finrank F V) {v : V}
    (hv : v ∉ U) : U ⊔ F ∙ v = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have hlt : U < U ⊔ F ∙ v := lt_of_le_of_ne le_sup_left fun h =>
    hv (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := Submodule.finrank_le (U ⊔ F ∙ v)
  omega

/-- Linear maps agreeing on a hyperplane and at one vector outside it are equal. -/
theorem ext_of_hyperplane {U : Submodule F V} (hU : finrank F U + 1 = finrank F V) {v : V} (hv : v ∉ U)
    {f g : V →ₗ[F] V} (hfU : ∀ u ∈ U, f u = g u) (hfv : f v = g v) : f = g := by
  ext x
  have hx : x ∈ U ⊔ F ∙ v := (sup_span_eq_top_of_hyperplane hU hv) ▸ Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  rw [map_add, map_add, map_smul, map_smul, hfU u hu, hfv]

theorem exists_not_mem_of_hyperplane {U : Submodule F V} (hU : finrank F U + 1 = finrank F V) :
    ∃ v, v ∉ U := by
  by_contra h
  push Not at h
  have : U = ⊤ := eq_top_iff.2 fun x _ => h x
  rw [this, finrank_top] at hU
  omega

/-- A vector orthogonal to a hyperplane $U$ and to one vector outside $U$ is in the radical. -/
theorem eq_zero_of_orth_hyperplane (hQ : (QuadraticMap.associated Q).Nondegenerate) {U : Submodule F V}
    (hU : finrank F U + 1 = finrank F V) {v : V} (hv : v ∉ U) {w : V} (hwU : ∀ u ∈ U, bil Q w u = 0)
    (hwv : bil Q w v = 0) : w = 0 := by
  refine hQ.1 w fun x => ?_
  have hx : x ∈ U ⊔ F ∙ v := (sup_span_eq_top_of_hyperplane hU hv) ▸ Submodule.mem_top
  obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  show bil Q w (u + c • v) = 0
  rw [bil_add_right, bil_smul_right, hwU u hu, hwv, mul_zero, add_zero]

/-- **O'Meara 43:1** (p. 101). Let $V$ be regular and $M$ a totally isotropic subspace ($B(M, M) = 0$) with
$2 \dim M = \dim V$ (so $V$ is a hyperbolic space and $M$ a maximal totally isotropic subspace). If $\sigma \in O(V)$ is
the identity on $M$, then $\sigma$ is a rotation: $\det \sigma = 1$. -/
@[kb "omeara1963" "§43A, 43:1, p. 101"]
theorem det_eq_one_of_fix_totallyIsotropic (hQ : (QuadraticMap.associated Q).Nondegenerate) {M : Submodule F V}
    (hM : ∀ x ∈ M, ∀ y ∈ M, bil Q x y = 0) (hdim : 2 * finrank F M = finrank F V) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ orth Q) (hfix : ∀ x ∈ M, σ x = x) : LinearEquiv.det σ = 1 := by
  have hMperp : LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) M = M := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · intro x hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      exact hM n hn x hx
    · rw [LinearMap.BilinForm.finrank_orthogonal hQ]
      omega
  have hP : ∀ y, σ y - y ∈ M := by
    intro y
    rw [← hMperp, LinearMap.BilinForm.mem_orthogonal_iff]
    intro m hm
    show bil Q m (σ y - y) = 0
    have := iv_bil_orth Q hσ m y
    rw [hfix m hm] at this
    rw [bil_sub_right, this, sub_self]
  have he : M ≤ M.comap (σ : V →ₗ[F] V) := fun y hy => by
    show σ y ∈ M
    rw [hfix y hy]; exact hy
  apply Units.ext
  rw [LinearEquiv.coe_det, LinearMap.det_eq_det_mul_det M (σ : V →ₗ[F] V) he]
  have h1 : (σ : V →ₗ[F] V).restrict he = LinearMap.id := by
    ext ⟨y, hy⟩
    simp [hfix y hy]
  have h2 : M.mapQ M (σ : V →ₗ[F] V) he = LinearMap.id := by
    ext y
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.id_apply]
    rw [Submodule.Quotient.eq]
    exact hP y
  rw [h1, h2]
  simp

/-- An isometry that is the identity on a non-regular hyperplane is the identity (proof of 43:2, part (2)). -/
theorem eq_one_of_fix_hyperplane_of_not_regular (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {U : Submodule F V} (hU : finrank F U + 1 = finrank F V)
    (hrad : ∃ w ∈ U, w ≠ 0 ∧ ∀ u ∈ U, bil Q w u = 0) {ρ : V ≃ₗ[F] V} (hρ : ρ ∈ orth Q)
    (hfix : ∀ u ∈ U, ρ u = u) : ρ = 1 := by
  obtain ⟨w, hwU, hw0, hwrad⟩ := hrad
  obtain ⟨v, hv⟩ := exists_not_mem_of_hyperplane hU
  set p := ρ v - v with hp
  have hpU : ∀ u ∈ U, bil Q u p = 0 := by
    intro u hu
    have := iv_bil_orth Q hρ u v
    rw [hfix u hu] at this
    rw [hp, bil_sub_right, this, sub_self]
  set W := LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) U
  have hW1 : finrank F W = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ]; omega
  have hwW : w ∈ W := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]; intro u hu
    show bil Q u w = 0
    rw [bil_comm]; exact hwrad u hu
  have hpW : p ∈ W := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]; intro u hu; exact hpU u hu
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w, hwW⟩ : W) (by simpa using hw0)).1 hW1 ⟨p, hpW⟩
  have hcp : c • w = p := by simpa using congrArg Subtype.val hc
  have hQw : Q w = 0 := by rw [← bil_self]; exact hwrad w hwU
  have hBvw : bil Q w v ≠ 0 := fun h => hw0 (eq_zero_of_orth_hyperplane Q hQ hU hv hwrad h)
  have hQρ : Q (ρ v) = Q v := hρ v
  have hρv : ρ v = v + p := by rw [hp]; abel
  rw [hρv, Q_add, ← hcp, Q_smul, hQw, bil_smul_right, bil_comm Q v w] at hQρ
  have hc0 : c = 0 := by
    have : (2 * bil Q w v) * c = 0 := by linear_combination hQρ
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero iv_two_ne hBvw)
  have hp0 : p = 0 := by rw [← hcp, hc0, zero_smul]
  apply LinearEquiv.toLinearMap_injective
  refine ext_of_hyperplane hU hv (fun u hu => ?_) ?_
  · simp [hfix u hu]
  · simp [hρv, hp0]

/-- An isometry that is the identity on a regular hyperplane $U = (Fz)^\perp$ is $1$ or $\tau_z$
(proof of 43:2, part (1)). -/
theorem eq_one_or_symmetry_of_fix_hyperplane (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {U : Submodule F V} (hU : finrank F U + 1 = finrank F V) {z : V} (hz : Q z ≠ 0)
    (hzU : ∀ u ∈ U, bil Q u z = 0) {ρ : V ≃ₗ[F] V} (hρ : ρ ∈ orth Q) (hfix : ∀ u ∈ U, ρ u = u) :
    ρ = 1 ∨ ρ = symmetry Q z hz := by
  have hzn : z ∉ U := fun h => hz (by rw [← bil_self]; exact hzU z h)
  have hρz : ρ z ∈ U ⊔ F ∙ z := (sup_span_eq_top_of_hyperplane hU hzn) ▸ Submodule.mem_top
  obtain ⟨u', hu', y, hy, hsum⟩ := Submodule.mem_sup.1 hρz
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hu'0 : u' = 0 := by
    refine eq_zero_of_orth_hyperplane Q hQ hU hzn (fun u hu => ?_) ?_
    · have h1 := iv_bil_orth Q hρ u z
      rw [hfix u hu, hzU u hu, ← hsum, bil_add_right, bil_smul_right, hzU u hu, mul_zero, add_zero] at h1
      rw [bil_comm]; exact h1
    · exact hzU u' hu'
  rw [hu'0, zero_add] at hsum
  have hQρ : Q (ρ z) = Q z := hρ z
  rw [← hsum, Q_smul] at hQρ
  have ht : t * t = 1 := by
    have : (t ^ 2 - 1) * Q z = 0 := by linear_combination hQρ
    have := (mul_eq_zero.1 this).resolve_right hz
    linear_combination this
  rcases mul_self_eq_one_iff.1 ht with rfl | rfl
  · left
    apply LinearEquiv.toLinearMap_injective
    refine ext_of_hyperplane hU hzn (fun u hu => ?_) ?_
    · simp [hfix u hu]
    · simp [← hsum]
  · right
    apply LinearEquiv.toLinearMap_injective
    refine ext_of_hyperplane hU hzn (fun u hu => ?_) ?_
    · simp only [LinearEquiv.coe_coe, hfix u hu, symmetry_apply, hzU u hu]
      simp
    · simp only [LinearEquiv.coe_coe, ← hsum, symmetry_apply, bil_self]
      rw [show 2 * Q z / Q z = 2 by field_simp]
      rw [two_smul]; simp

/-- **O'Meara 43:2** (p. 101), the case of a regular hyperplane. Let $V$ be regular, $U$ a hyperplane and $z$ an
anisotropic vector orthogonal to $U$ (so $U = (Fz)^\perp$ is regular). If $\sigma_1, \sigma_2 \in O(V)$ agree on $U$
(are prolongations of the same isometry of $U$ into $V$), then $\sigma_2 = \sigma_1$ or $\sigma_2 = \sigma_1\tau_z$:
there are at most two prolongations, and one is the other times a symmetry. -/
@[kb "omeara1963" "§43A, 43:2, p. 101 (regular hyperplane: at most two prolongations, σ₁ and σ₁τ_z)"]
theorem prolongation_eq_or_mul_symmetry (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {U : Submodule F V} (hU : finrank F U + 1 = finrank F V) {z : V} (hz : Q z ≠ 0)
    (hzU : ∀ u ∈ U, bil Q u z = 0) {σ₁ σ₂ : V ≃ₗ[F] V} (h₁ : σ₁ ∈ orth Q) (h₂ : σ₂ ∈ orth Q)
    (hagree : ∀ u ∈ U, σ₁ u = σ₂ u) : σ₂ = σ₁ ∨ σ₂ = σ₁ * symmetry Q z hz := by
  have hρ : σ₁⁻¹ * σ₂ ∈ orth Q := (orth Q).mul_mem ((orth Q).inv_mem h₁) h₂
  have hfix : ∀ u ∈ U, (σ₁⁻¹ * σ₂) u = u := fun u hu => by
    rw [LinearEquiv.mul_apply, ← hagree u hu]
    exact σ₁.symm_apply_apply u
  rcases eq_one_or_symmetry_of_fix_hyperplane Q hQ hU hz hzU hρ hfix with h | h
  · left; rw [← mul_inv_cancel_left σ₁ σ₂, h, mul_one]
  · right; rw [← mul_inv_cancel_left σ₁ σ₂, h]

/-- **O'Meara 43:2** (p. 101), the case of a non-regular hyperplane. Let $V$ be regular and $U$ a hyperplane that is
not regular ($\operatorname{rad} U \ne 0$). If $\sigma_1, \sigma_2 \in O(V)$ agree on $U$ then $\sigma_1 = \sigma_2$: an
isometry of $U$ into $V$ has at most one prolongation to $O(V)$. -/
@[kb "omeara1963" "§43A, 43:2, p. 101 (non-regular hyperplane: at most one prolongation)"]
theorem prolongation_eq_of_not_regular (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {U : Submodule F V} (hU : finrank F U + 1 = finrank F V)
    (hrad : splitComp (R := F) Q U U ≠ ⊥) {σ₁ σ₂ : V ≃ₗ[F] V} (h₁ : σ₁ ∈ orth Q) (h₂ : σ₂ ∈ orth Q)
    (hagree : ∀ u ∈ U, σ₁ u = σ₂ u) : σ₂ = σ₁ := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hrad
  have hρ : σ₁⁻¹ * σ₂ ∈ orth Q := (orth Q).mul_mem ((orth Q).inv_mem h₁) h₂
  have hfix : ∀ u ∈ U, (σ₁⁻¹ * σ₂) u = u := fun u hu => by
    rw [LinearEquiv.mul_apply, ← hagree u hu]
    exact σ₁.symm_apply_apply u
  have h := eq_one_of_fix_hyperplane_of_not_regular Q hQ hU ⟨w, hw.1, hw0, hw.2⟩ hρ hfix
  rw [← mul_inv_cancel_left σ₁ σ₂, h, mul_one]

/-- The dimension of the fixed space $\ker(\sigma - 1)$ of $\sigma$. -/
def fixRank (σ : V ≃ₗ[F] V) : ℕ := finrank F (LinearMap.ker ((σ : V →ₗ[F] V) - LinearMap.id))

theorem fixRank_one : fixRank (1 : V ≃ₗ[F] V) = finrank F V := by
  have : LinearMap.ker (((1 : V ≃ₗ[F] V) : V →ₗ[F] V) - LinearMap.id) = ⊤ := by
    ext x; simp
  unfold fixRank
  calc finrank F (LinearMap.ker (((1 : V ≃ₗ[F] V) : V →ₗ[F] V) - LinearMap.id))
      = finrank F (⊤ : Submodule F V) := by rw [this]
    _ = finrank F V := finrank_top F V

theorem fixRank_le_symmetry_mul (σ : V ≃ₗ[F] V) {a : V} (ha : Q a ≠ 0) :
    fixRank σ ≤ fixRank (symmetry Q a ha * σ) + 1 := by
  unfold fixRank
  set K := LinearMap.ker ((σ : V →ₗ[F] V) - LinearMap.id)
  set H := LinearMap.ker (QuadraticMap.associated Q a)
  have hle : K ⊓ H ≤ LinearMap.ker (((symmetry Q a ha * σ : V ≃ₗ[F] V) : V →ₗ[F] V) - LinearMap.id) := by
    rintro x ⟨hK, hH⟩
    simp only [K, H, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe,
      LinearMap.id_apply, sub_eq_zero] at hK hH ⊢
    rw [LinearEquiv.mul_apply, hK, symmetry_apply]
    have : bil Q x a = 0 := by rw [bil_comm]; exact hH
    rw [this]; simp
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq K H
  have h3 := Submodule.finrank_le (K ⊔ H)
  have h4 : finrank F (LinearMap.range (QuadraticMap.associated Q a)) + finrank F H = finrank F V :=
    LinearMap.finrank_range_add_finrank_ker _
  have h5 : finrank F (LinearMap.range (QuadraticMap.associated Q a)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (QuadraticMap.associated Q a))
    rwa [Module.finrank_self] at this
  omega

theorem le_fixRank_prod_add_length (l : List {u : V // Q u ≠ 0}) :
    finrank F V ≤ fixRank ((l.map fun u => symmetry Q u.1 u.2).prod) + l.length := by
  induction l with
  | nil => rw [List.map_nil, List.prod_nil, fixRank_one]; simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons]
    have := fixRank_le_symmetry_mul Q ((l.map fun u => symmetry Q u.1 u.2).prod) a.2
    omega

/-- **O'Meara 43:3a** (p. 103). If $\sigma = \tau_{u_1} \cdots \tau_{u_r}$ is a product of $r$ symmetries of the
$n$-dimensional space $V$, then the fixed space $\{x : \sigma x = x\}$ of $\sigma$ has dimension at least $n - r$. -/
@[kb "omeara1963" "§43B, 43:3a, p. 103"]
theorem finrank_le_finrank_fixed_add_length (l : List {u : V // Q u ≠ 0}) :
    finrank F V ≤
      finrank F (LinearMap.ker ((((l.map fun u => symmetry Q u.1 u.2).prod : V ≃ₗ[F] V) : V →ₗ[F] V) -
        LinearMap.id)) + l.length :=
  le_fixRank_prod_add_length Q l

/-- **O'Meara 43:9** (p. 108). Let $V$ be regular and $\sigma \in O(V)$ leave every line fixed ($\sigma x \in Fx$ for
all $\vec{x}$). Then $\sigma = \pm 1_V$. -/
@[kb "omeara1963" "§43E, 43:9, p. 108"]
theorem eq_one_or_neg_of_forall_mem_line (hQ : (QuadraticMap.associated Q).Nondegenerate) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ orth Q) (h : ∀ x, ∃ a : F, σ x = a • x) : (∀ x, σ x = x) ∨ ∀ x, σ x = -x := by
  by_cases hsub : Subsingleton V
  · left; intro x; exact Subsingleton.elim _ _
  have hnt : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
  obtain ⟨a, ha⟩ : ∃ a : F, (σ : V →ₗ[F] V) = a • 1 := by
    apply LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    intro v hli
    obtain ⟨c, hc⟩ := h v
    have := LinearIndependent.pair_iff.1 hli c (-1) (by simp [hc])
    exact neg_ne_zero.2 one_ne_zero this.2
  have hσa : ∀ x, σ x = a • x := fun x => by
    have := congrArg (fun f : V →ₗ[F] V => f x) ha
    simpa using this
  obtain ⟨x, hx⟩ : ∃ x : V, Q x ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨y, hy⟩ := exists_ne (0 : V)
    apply hy
    refine hQ.1 y fun z => ?_
    have h := Q_add Q y z
    rw [hall, hall, hall] at h
    have : (2 : F) * bil Q y z = 0 := by linear_combination -h
    exact (mul_eq_zero.1 this).resolve_left iv_two_ne
  have hQx := hσ x
  rw [hσa, Q_smul] at hQx
  have ha2 : a * a = 1 := by
    have : (a ^ 2 - 1) * Q x = 0 := by linear_combination hQx
    have := (mul_eq_zero.1 this).resolve_right hx
    linear_combination this
  rcases mul_self_eq_one_iff.1 ha2 with rfl | rfl
  · left; intro y; rw [hσa, one_smul]
  · right; intro y; rw [hσa, neg_one_smul]

end Sec43A

end QuadFormsKB.OMeara
