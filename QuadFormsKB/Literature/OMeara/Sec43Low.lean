import QuadFormsKB.Literature.OMeara.Sec43C
import QuadFormsKB.Literature.OMeara.Sec55

/-!
# O'Meara §43C: isometries of spaces of dimension at most 3 (43:4)

**Setting** (as in `Sec43A.lean` and `Sec43C.lean`): $F$ a field with $2 \ne 0$, $(V, Q)$ a finite-dimensional regular
quadratic space, $n = \dim V$, $O(V)$ = `orth Q`, `cd_prod Q l` the product of the symmetries of a list $l$ of
anisotropic vectors, and `fixRank σ` the dimension $d$ of the fixed space $\ker(\sigma - 1)$.

**Proves** (O'Meara 1973 printing, Chapter IV, §43C, p. 105):
* `exists_cd_prod_eq_of_fix_hyperplane`: an isometry that is the identity on a hyperplane is $1$ or a symmetry (from
  43:2);
* `exists_cd_prod_length_eq_sub_fixRank` and `le_length_of_cd_prod_eq` (**43:4**): if $1 \le n \le 3$ and $d$ is the
  dimension of the fixed space of $\sigma \in O(V)$, then $\sigma$ is a product of $n - d$ symmetries, and not of fewer.

**Proof notes.** "Not fewer" is 43:3a. For the existence: $d = 0$ is 43:3; $d = n$ is $\sigma = 1$; $d = n - 1$ uses
43:2 (an isometry fixing a hyperplane is $1$ or a symmetry); $n = 3$, $d = 1$ follows the book: if $\sigma$ were a
reflexion, $-\sigma$ would be a rotation, hence (43:3 and parity) a product of two symmetries with a fixed vector $y$;
then $\sigma^2$ fixes the plane $Fx + Fy$ and is a rotation, so $\sigma^2 = 1$ by 43:2; then $-\sigma$ fixes the reversed
plane of the involution $\sigma$ (42:14), so it is a symmetry, contradicting $\det(-\sigma) = 1$. Hence $\sigma$ is a
rotation, a product of two symmetries.
-/

open QuadraticMap Submodule Module LinearMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Sec43Low

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)

theorem iv_cd_prod_mem_orth (l : List {u : V // Q u ≠ 0}) : cd_prod Q l ∈ orth Q := by
  rw [cd_prod]
  refine List.prod_induction _ (fun a b ha hb => (orth Q).mul_mem ha hb) (orth Q).one_mem ?_
  intro x hx
  obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx
  exact symmetry_mem_orth Q u.2

/-- A hyperplane of a regular space either contains a non-zero vector of its radical, or is $(Fz)^\perp$ for an
anisotropic $z$. -/
theorem hyperplane_dichotomy (hQ : (QuadraticMap.associated Q).Nondegenerate) {U : Submodule F V}
    (hU : finrank F U + 1 = finrank F V) :
    (∃ w ∈ U, w ≠ 0 ∧ ∀ u ∈ U, bil Q w u = 0) ∨ ∃ z, Q z ≠ 0 ∧ ∀ u ∈ U, bil Q u z = 0 := by
  set W := LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) U
  have hW : finrank F W = 1 := by rw [LinearMap.BilinForm.finrank_orthogonal hQ]; omega
  obtain ⟨z, hzW, hz0⟩ : ∃ z ∈ W, z ≠ 0 := by
    have : W ≠ ⊥ := fun h => by rw [h, finrank_bot] at hW; omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot this
  have hzU : ∀ u ∈ U, bil Q u z = 0 := fun u hu => (LinearMap.BilinForm.mem_orthogonal_iff.1 hzW) u hu
  by_cases hQz : Q z = 0
  · left
    by_cases hz : z ∈ U
    · exact ⟨z, hz, hz0, fun u hu => by rw [bil_comm]; exact hzU u hu⟩
    · exfalso
      exact hz0 (eq_zero_of_orth_hyperplane Q hQ hU hz (fun u hu => by rw [bil_comm]; exact hzU u hu)
        (by rw [bil_self]; exact hQz))
  · exact Or.inr ⟨z, hQz, hzU⟩

/-- An isometry of a regular space that is the identity on a hyperplane is $1$ or a symmetry. -/
theorem eq_one_or_symmetry_of_fix_hyperplane' (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {U : Submodule F V} (hU : finrank F U + 1 = finrank F V) {ρ : V ≃ₗ[F] V} (hρ : ρ ∈ orth Q)
    (hfix : ∀ u ∈ U, ρ u = u) : ρ = 1 ∨ ∃ z, ∃ hz : Q z ≠ 0, ρ = symmetry Q z hz := by
  rcases hyperplane_dichotomy Q hQ hU with hrad | ⟨z, hz, hzU⟩
  · exact Or.inl (eq_one_of_fix_hyperplane_of_not_regular Q hQ hU hrad hρ hfix)
  · rcases eq_one_or_symmetry_of_fix_hyperplane Q hQ hU hz hzU hρ hfix with h | h
    · exact Or.inl h
    · exact Or.inr ⟨z, hz, h⟩

/-- The fixed space of $\sigma$ as a submodule. -/
abbrev fixSp (σ : V ≃ₗ[F] V) : Submodule F V := LinearMap.ker ((σ : V →ₗ[F] V) - LinearMap.id)

theorem mem_fixSp {σ : V ≃ₗ[F] V} {x : V} : x ∈ fixSp σ ↔ σ x = x := by
  simp [fixSp, sub_eq_zero]

/-- An isometry fixing a hyperplane pointwise is a product of at most one symmetry (43:2). -/
theorem exists_cd_prod_eq_of_fix_hyperplane (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (hd : fixRank σ + 1 = finrank F V) :
    ∃ l : List {u : V // Q u ≠ 0}, σ = cd_prod Q l ∧ l.length = 1 := by
  rcases eq_one_or_symmetry_of_fix_hyperplane' Q hQ (U := fixSp σ) hd hσ (fun u hu => mem_fixSp.1 hu) with
    h | ⟨z, hz, h⟩
  · exfalso
    subst h
    rw [fixRank_one] at hd; omega
  · exact ⟨[⟨z, hz⟩], by rw [h]; show _ = _ * 1; rw [mul_one], rfl⟩

theorem fixRank_le_finrank (σ : V ≃ₗ[F] V) : fixRank σ ≤ finrank F V := Submodule.finrank_le _

theorem eq_one_of_fixRank_eq (σ : V ≃ₗ[F] V) (h : fixRank σ = finrank F V) : σ = 1 := by
  have htop : fixSp σ = ⊤ := Submodule.eq_top_of_finrank_eq h
  ext x
  have : x ∈ fixSp σ := htop ▸ Submodule.mem_top
  exact mem_fixSp.1 this

/-- The ternary case $d = 1$ of 43:4: $\sigma$ is a rotation. -/
theorem det_eq_one_of_ternary_fixRank_one (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : finrank F V = 3) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (hd : fixRank σ = 1) :
    LinearEquiv.det σ = 1 := by
  by_contra hdet
  have hdetσ : LinearEquiv.det σ = -1 := by
    obtain ⟨l, -, hl⟩ := cd_list Q hQ hσ
    have := cd_det_prod Q l
    rw [← hl] at this
    rcases neg_one_pow_eq_or Fˣ l.length with h | h
    · exact absurd (this.trans h) hdet
    · exact this.trans h
  -- −σ is a rotation, so it has a non-zero fixed vector y: σ y = −y
  set τ : V ≃ₗ[F] V := LinearEquiv.neg F * σ
  have hτ : τ ∈ orth Q := fun x => by simp [τ, hσ x]
  have hdetτ : LinearEquiv.det τ = 1 := by
    rw [map_mul, Sp55.det_neg_eq (F := F) (V := V), h3, hdetσ]; norm_num
  obtain ⟨m, hm, hτm⟩ := cd_list Q hQ hτ
  have hev : Even m.length := by
    rw [hτm, cd_det_prod] at hdetτ; exact (neg_one_pow_eq_one_iff_even (cd_neg_one_ne (F := F))).1 hdetτ
  have hm2 : m.length ≤ 2 := by obtain ⟨k, hk⟩ := hev; omega
  have hfτ := le_fixRank_prod_add_length Q m
  rw [← cd_prod, ← hτm] at hfτ
  obtain ⟨y, hy, hy0⟩ : ∃ y ∈ fixSp τ, y ≠ 0 := by
    have : fixSp τ ≠ ⊥ := fun h => by
      unfold fixRank at hfτ; rw [show LinearMap.ker ((τ : V →ₗ[F] V) - LinearMap.id) = ⊥ from h,
        finrank_bot] at hfτ; omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot this
  have hσy : σ y = -y := by
    have := mem_fixSp.1 hy
    simp only [τ, LinearEquiv.mul_apply, LinearEquiv.neg_apply] at this
    exact neg_eq_iff_eq_neg.1 this
  -- the fixed vector x of σ
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ fixSp σ, x ≠ 0 := by
    have : fixSp σ ≠ ⊥ := fun h => by
      unfold fixRank at hd; rw [show LinearMap.ker ((σ : V →ₗ[F] V) - LinearMap.id) = ⊥ from h,
        finrank_bot] at hd; omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot this
  have hσx : σ x = x := mem_fixSp.1 hx
  -- x, y independent
  have hli : LinearIndependent F ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg σ hst
    rw [map_add, map_smul, map_smul, hσx, hσy, map_zero] at h1
    have hsx : (2 * s) • x = 0 := by
      rw [mul_smul, two_smul]
      calc s • x + s • x = (s • x + t • y) + (s • x + t • -y) := by rw [smul_neg]; abel
        _ = 0 := by rw [hst, h1, add_zero]
    have hs : s = 0 := by
      rcases smul_eq_zero.1 hsx with h | h
      · exact (mul_eq_zero.1 h).resolve_left iv_two_ne
      · exact absurd h hx0
    subst hs
    rw [zero_smul, zero_add] at hst
    exact ⟨rfl, (smul_eq_zero.1 hst).resolve_right hy0⟩
  -- σ² is the identity on the plane P = Fx + Fy
  set P := Submodule.span F (Set.range ![x, y])
  have hP : finrank F P + 1 = finrank F V := by
    rw [finrank_span_eq_card hli, h3]; simp
  have hσ2 : σ * σ ∈ orth Q := (orth Q).mul_mem hσ hσ
  have hfixP : ∀ u ∈ P, (σ * σ) u = u := by
    intro u hu
    refine Submodule.span_induction (p := fun u _ => (σ * σ) u = u) ?_ (by simp) ?_ ?_ hu
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · simp [hσx]
      · simp [hσy]
    · intro a b _ _ ha hb; rw [map_add, ha, hb]
    · intro c a _ ha; rw [map_smul, ha]
  have hsq : σ * σ = 1 := by
    rcases eq_one_or_symmetry_of_fix_hyperplane' Q hQ hP hσ2 hfixP with h | ⟨z, hz, h⟩
    · exact h
    · exfalso
      have := congrArg LinearEquiv.det h
      rw [map_mul, hdetσ, det_symmetry] at this
      exact (cd_neg_one_ne (F := F)) (by simpa using this.symm)
  -- σ is an involution; −σ fixes the reversed space U, a hyperplane
  obtain ⟨U, W, hc, -, hU, hW⟩ := (involution_iff_splitting Q hσ).1 (fun v => by
    have := congrArg (fun f : V ≃ₗ[F] V => f v) hsq; simpa using this)
  have hWfix := (splitting_eq_fixed hc hU hW).1
  have hWeq : W = fixSp σ := by ext v; rw [hWfix v, mem_fixSp]
  have hUdim : finrank F U + 1 = finrank F V := by
    have := Submodule.finrank_add_eq_of_isCompl hc
    rw [hWeq] at this
    have hd' : finrank F (fixSp σ) = 1 := hd
    omega
  have hτU : ∀ u ∈ U, τ u = u := fun u hu => by
    simp [τ, hU u hu]
  rcases eq_one_or_symmetry_of_fix_hyperplane' Q hQ hUdim hτ hτU with h | ⟨z, hz, h⟩
  · -- τ = 1 means σ = −1, but σ x = x
    have := congrArg (fun f : V ≃ₗ[F] V => f x) h
    have hx' : -x = x := by simpa [τ, hσx] using this
    have h2x : (2 : F) • x = 0 := by rw [two_smul]; nth_rewrite 1 [← hx']; simp
    exact hx0 ((smul_eq_zero.1 h2x).resolve_left iv_two_ne)
  · have := congrArg LinearEquiv.det h
    rw [hdetτ, det_symmetry] at this
    exact (cd_neg_one_ne (F := F)) this.symm

/-- **O'Meara 43:4** (p. 105), "not fewer": if $\sigma$ is a product of $r$ symmetries then $r \ge n - d$, where $d$ is
the dimension of the fixed space of $\sigma$ (this is 43:3a, and holds in every dimension). -/
@[kb "omeara1963" "§43C, 43:4, p. 105 (σ is not a product of fewer than n − d symmetries)"]
theorem le_length_of_cd_prod_eq {σ : V ≃ₗ[F] V} {l : List {u : V // Q u ≠ 0}} (h : σ = cd_prod Q l) :
    finrank F V - fixRank σ ≤ l.length := by
  have := le_fixRank_prod_add_length Q l
  rw [← cd_prod, ← h] at this
  omega

/-- **O'Meara 43:4** (p. 105). Let $V$ be regular with $1 \le n = \dim V \le 3$, $\sigma \in O(V)$, and $d$ the dimension of
the fixed space of $\sigma$. Then $\sigma$ is a product of $n - d$ symmetries (and of no fewer, by
`le_length_of_cd_prod_eq`). -/
@[kb "omeara1963" "§43C, 43:4, p. 105"]
theorem exists_cd_prod_length_eq_sub_fixRank (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : finrank F V ≤ 3) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) :
    ∃ l : List {u : V // Q u ≠ 0}, σ = cd_prod Q l ∧ l.length = finrank F V - fixRank σ := by
  have hle := fixRank_le_finrank σ
  obtain ⟨l, hl, hσl⟩ := cd_list Q hQ hσ
  have hlow := le_length_of_cd_prod_eq Q hσl
  by_cases hd0 : fixRank σ = 0
  · exact ⟨l, hσl, by omega⟩
  by_cases hdn : fixRank σ = finrank F V
  · exact ⟨[], by rw [eq_one_of_fixRank_eq σ hdn]; rfl, by simp [hdn]⟩
  by_cases hd1 : fixRank σ + 1 = finrank F V
  · obtain ⟨m, hm, hlen⟩ := exists_cd_prod_eq_of_fix_hyperplane Q hQ hσ hd1
    exact ⟨m, hm, by omega⟩
  -- remaining case: n = 3, d = 1
  have hn3 : finrank F V = 3 := by omega
  have hd : fixRank σ = 1 := by omega
  have hdet := det_eq_one_of_ternary_fixRank_one Q hQ hn3 hσ hd
  rw [hσl, cd_det_prod] at hdet
  obtain ⟨k, hk⟩ := (neg_one_pow_eq_one_iff_even (cd_neg_one_ne (F := F))).1 hdet
  exact ⟨l, hσl, by omega⟩

end Sec43Low

end QuadFormsKB.OMeara
