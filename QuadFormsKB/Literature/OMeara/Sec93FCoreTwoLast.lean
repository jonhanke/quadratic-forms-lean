/-
# O'Meara 93:28 over a 2-adic field: the last case, proved

**Setting** (as in `Sec93E.lean`), with $2$ a prime element of $R$ (a 2-adic field, §93G).

**Proves** (O'Meara 1963, §93G, proof of 93:29, sufficiency, p. 278: "We therefore assume that $\mathfrak n_1 = \mathfrak o$.
Here we have $dK_1 \cong 1 \bmod 4\mathfrak o$, so $K_1 \cong \langle A(1, 4\lambda)\rangle \perp \langle A(2, 2\mu)\rangle$
... A computation of Hasse symbols ... will show that $\mu = 0$")
* `twoAdicCoreRest4`: the former named statement `CoreTwoMain.TwoAdicCoreRest4`. Route: $dL_1 = 1$ from a block base
  (`exists_basis_det_one_of_blockBase`); condition (i) with $\mathfrak f_1 = 4\mathfrak o$ (`fIdeal_four`) gives
  $dK_1 = \varepsilon^{-2}(1 + \alpha)$ with $\mathfrak d(1+\alpha) = \alpha\mathfrak o$, $\alpha \in 4\mathfrak o$
  (`exists_alpha`); 93:18 (iii) gives $K_1 \cong A(1, -\alpha) \perp A(2, 0)$ or $A(1, -(\alpha - 4\rho)) \perp A(2, 2\rho)$;
  93:19 moves the first block to $A(1, 0)$; in the second case condition (iii) at the first index
  ($\mathfrak f_1 = 4\mathfrak o \subsetneq 2\mathfrak o$, `hlt_four`) represents $FL_1$ (hyperbolic) by $H \perp (F\!A(2, 2\rho)
  \perp \langle a\rangle)$, impossible because $2(x^2 + xy + \rho y^2) + az^2$ is anisotropic (`ternary_aniso`,
  `no_rep_aniso`: the "Hasse symbol computation" is a parity count of orders);
* `dyadicClassification_twoAdic_unconditional`, `dyadicClassification_twoAdic_unconditional_nf`: Theorem 93:28 over a
  2-adic field and over 2-adic completions of number fields, with no named input.
-/
import QuadFormsKB.Literature.OMeara.Sec93FCoreTwoMain

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.CoreTwoLast

universe u v

section Arith

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- Over a 2-adic ring, $2 \in \mathfrak p$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
theorem two_mem_maximal (h2 : IsTwoAdic R) : (2 : R) ∈ maximalIdeal R :=
  (IsLocalRing.mem_maximalIdeal _).mpr (twoAdic_irreducible h2).not_isUnit

/-- Over a 2-adic ring, $\mathfrak p = 2R$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
theorem maximal_eq_span_two (h2 : IsTwoAdic R) : maximalIdeal R = Ideal.span {(2 : R)} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer 2).mp h2

/-- **$X^2 + X + \rho$ has no root modulo $\mathfrak p$** when the defect of $1 + 4\rho$ is $4\mathfrak o$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
theorem no_root_of_defect (h2 : IsTwoAdic R) {ρ : R}
    (hρ : quadDefect R (algebraMap R F (1 + 4 * ρ)) = span R {(4 : F)}) :
    ∀ t : R, t ^ 2 + t + ρ ∉ maximalIdeal R := by
  intro t ht
  rw [maximal_eq_span_two h2, Ideal.mem_span_singleton'] at ht
  obtain ⟨s, hs⟩ := ht
  have hle : quadDefect R (algebraMap R F (1 + 4 * ρ)) ≤
      span R {algebraMap R F (1 + 4 * ρ) - algebraMap R F (2 * t + 1) ^ 2} :=
    iInf_le (fun η : F => span R {algebraMap R F (1 + 4 * ρ) - η ^ 2}) (algebraMap R F (2 * t + 1))
  rw [hρ] at hle
  have h4 : (4 : F) ∈ span R {algebraMap R F (1 + 4 * ρ) - algebraMap R F (2 * t + 1) ^ 2} :=
    hle (mem_span_singleton_self _)
  obtain ⟨c, hc⟩ := mem_span_singleton.mp h4
  have hρ' : ρ = s * 2 - t ^ 2 - t := by linear_combination -hs
  have hval : (1 + 4 * ρ) - (2 * t + 1) ^ 2 = 8 * (s - t ^ 2 - t) := by rw [hρ']; ring
  have hF : algebraMap R F (1 + 4 * ρ) - algebraMap R F (2 * t + 1) ^ 2 =
      algebraMap R F (8 * (s - t ^ 2 - t)) := by
    rw [← hval, map_sub, map_pow]
  rw [hF, Algebra.smul_def, ← map_mul] at hc
  have hc' : (algebraMap R F) (c * (8 * (s - t ^ 2 - t))) = algebraMap R F 4 := by
    rw [hc, map_ofNat]
  have hR : c * (8 * (s - t ^ 2 - t)) = 4 := IsFractionRing.injective R F hc'
  have h2ne : (2 : R) ≠ 0 := (twoAdic_irreducible h2).ne_zero
  have : (2 : R) * (2 * (c * (2 * (s - t ^ 2 - t)))) = 2 * 2 := by linear_combination hR
  have h3 : 2 * (c * (2 * (s - t ^ 2 - t))) = 2 := mul_left_cancel₀ h2ne this
  have h4' : 2 * (c * (s - t ^ 2 - t)) = 1 := by
    have : (2 : R) * (2 * (c * (s - t ^ 2 - t))) = 2 * 1 := by linear_combination h3
    exact mul_left_cancel₀ h2ne this
  exact (twoAdic_irreducible h2).not_isUnit (isUnit_iff_exists_inv.mpr ⟨_, h4'⟩)

/-- A value of $X^2 + XY + \rho Y^2$ at a primitive vector is a unit. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
theorem norm_not_mem {ρ : R} (hno : ∀ t : R, t ^ 2 + t + ρ ∉ maximalIdeal R) {X Y : R}
    (h : X ∉ maximalIdeal R ∨ Y ∉ maximalIdeal R) : X ^ 2 + X * Y + ρ * Y ^ 2 ∉ maximalIdeal R := by
  intro hN
  have hN' : residue R (X ^ 2 + X * Y + ρ * Y ^ 2) = 0 := (residue_eq_zero_iff _).2 hN
  simp only [map_add, map_mul, map_pow] at hN'
  by_cases hy : residue R Y = 0
  · rw [hy] at hN'
    have hx : residue R X = 0 := by
      have : residue R X ^ 2 = 0 := by simpa using hN'
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    rcases h with h | h
    · exact h ((residue_eq_zero_iff X).1 hx)
    · exact h ((residue_eq_zero_iff Y).1 hy)
  · obtain ⟨t, ht⟩ := residue_surjective (residue R X / residue R Y)
    apply hno t
    rw [← residue_eq_zero_iff]
    simp only [map_add, map_pow, ht]
    field_simp
    linear_combination hN'

/-- **Anisotropy of $2(X^2 + XY + \rho Y^2) + aZ^2$ over $R$ on primitive vectors.** -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
theorem aniso_R (h2 : IsTwoAdic R) {ρ : R} (hno : ∀ t : R, t ^ 2 + t + ρ ∉ maximalIdeal R) {a : R}
    (ha : IsUnit a) {X Y Z : R} (hprim : X ∉ maximalIdeal R ∨ Y ∉ maximalIdeal R ∨ Z ∉ maximalIdeal R)
    (h : 2 * (X ^ 2 + X * Y + ρ * Y ^ 2) + a * Z ^ 2 = 0) : False := by
  have hmax := maximal_eq_span_two h2
  have h2ne : (2 : R) ≠ 0 := (twoAdic_irreducible h2).ne_zero
  by_cases hZ : Z ∈ maximalIdeal R
  · have hXY : X ∉ maximalIdeal R ∨ Y ∉ maximalIdeal R := by
      rcases hprim with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact absurd hZ h1
    have hN := norm_not_mem hno hXY
    rw [hmax, Ideal.mem_span_singleton'] at hZ
    obtain ⟨Z', rfl⟩ := hZ
    apply hN
    rw [hmax, Ideal.mem_span_singleton']
    refine ⟨-(a * Z' ^ 2), ?_⟩
    have : (2 : R) * (X ^ 2 + X * Y + ρ * Y ^ 2) = 2 * (-(a * Z' ^ 2) * 2) := by
      linear_combination h
    exact (mul_left_cancel₀ h2ne this).symm
  · have hZu : IsUnit Z := by
      by_contra hn; exact hZ ((IsLocalRing.mem_maximalIdeal _).mpr hn)
    have hu : IsUnit (a * Z ^ 2) := ha.mul (hZu.pow 2)
    have hmem : a * Z ^ 2 ∈ maximalIdeal R := by
      have : a * Z ^ 2 = -(2 * (X ^ 2 + X * Y + ρ * Y ^ 2)) := by linear_combination h
      rw [this]
      exact neg_mem (Ideal.mul_mem_right _ _ (two_mem_maximal h2))
    exact (IsLocalRing.mem_maximalIdeal _).1 hmem hu

/-- **The ternary form $2(x^2 + xy + \rho y^2) + az^2$ is anisotropic over $F$** ($a$ a unit of $R$, $X^2 + X + \rho$
without root modulo $\mathfrak p$). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
theorem ternary_aniso (h2 : IsTwoAdic R) {ρ : R} (hno : ∀ t : R, t ^ 2 + t + ρ ∉ maximalIdeal R) {a : R}
    (ha : IsUnit a) {x y z : F}
    (h : 2 * (x ^ 2 + x * y + algebraMap R F ρ * y ^ 2) + algebraMap R F a * z ^ 2 = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  by_contra hcon
  have hfg : (span R ({x, y, z} : Set F)).FG := Submodule.fg_span (Set.toFinite _)
  obtain ⟨g, hg, hspan⟩ := exists_mem_span_eq_singleton (R := R) hfg
  have hg0 : g ≠ 0 := by
    rintro rfl
    apply hcon
    have hx : x ∈ span R ({x, y, z} : Set F) := subset_span (by simp)
    have hy : y ∈ span R ({x, y, z} : Set F) := subset_span (by simp)
    have hz : z ∈ span R ({x, y, z} : Set F) := subset_span (by simp)
    rw [hspan] at hx hy hz
    simp only [span_singleton_eq_bot.mpr rfl, mem_bot] at hx hy hz
    exact ⟨hx, hy, hz⟩
  have hmem : ∀ w ∈ ({x, y, z} : Set F), ∃ r : R, w = algebraMap R F r * g := by
    intro w hw
    have : w ∈ span R ({x, y, z} : Set F) := subset_span hw
    rw [hspan] at this
    obtain ⟨r, hr⟩ := mem_span_singleton.mp this
    exact ⟨r, by rw [← hr, Algebra.smul_def]⟩
  obtain ⟨X, hX⟩ := hmem x (by simp)
  obtain ⟨Y, hY⟩ := hmem y (by simp)
  obtain ⟨Z, hZ⟩ := hmem z (by simp)
  have hprim : X ∉ maximalIdeal R ∨ Y ∉ maximalIdeal R ∨ Z ∉ maximalIdeal R := by
    have hone : ∀ r : R, g = algebraMap R F r * g → r = 1 := fun r hr => by
      have : algebraMap R F r = 1 := by
        have := mul_right_cancel₀ hg0 (show algebraMap R F r * g = 1 * g by rw [← hr, one_mul])
        exact this
      have h1 : algebraMap R F r = algebraMap R F 1 := by rw [this, map_one]
      exact IsFractionRing.injective R F h1
    have hgS : g ∈ ({x, y, z} : Set F) := hg.resolve_right hg0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgS
    have notmax : ∀ r : R, r = 1 → r ∉ maximalIdeal R := fun r hr => by
      rw [hr]; exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h isUnit_one
    rcases hgS with h | h | h
    · exact Or.inl (notmax X (hone X (by rw [← hX, h])))
    · exact Or.inr (Or.inl (notmax Y (hone Y (by rw [← hY, h]))))
    · exact Or.inr (Or.inr (notmax Z (hone Z (by rw [← hZ, h]))))
  have hF : algebraMap R F (2 * (X ^ 2 + X * Y + ρ * Y ^ 2) + a * Z ^ 2) * g ^ 2 = 0 := by
    rw [hX, hY, hZ] at h
    simp only [map_add, map_mul, map_pow, map_ofNat]
    linear_combination h
  have hR : 2 * (X ^ 2 + X * Y + ρ * Y ^ 2) + a * Z ^ 2 = 0 := by
    have := (mul_eq_zero.1 hF).resolve_right (pow_ne_zero 2 hg0)
    exact (map_eq_zero_iff _ (IsFractionRing.injective R F)).1 this
  exact aniso_R h2 hno ha hprim hR

end Arith

section NoRep

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open QuadFormsKB.OMeara

/-- **No representation of a hyperbolic space in $H' \perp (T \perp \langle a\rangle)$ with $T \perp \langle a\rangle$
anisotropic** (O'Meara 1963, §93G, p. 278: "a computation of Hasse symbols ... will show that $\mu = 0$"): let
$K' = (\mathfrak ox + \mathfrak oy) \perp (\mathfrak ou + \mathfrak ov)$ with $Q(x) = 0$, $B(x,y) = 1$, $Q(u) = 2$, $B(u,v) = 1$,
$Q(v) = 2\rho$ and $X^2 + X + \rho$ without root mod $\mathfrak p$ (2-adic). If $FL$ contains a totally isotropic $T$ with
$\operatorname{rank} L \le 2\dim T$, then $FL \to FK' \perp \langle a\rangle$ is impossible for a unit $a$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
theorem no_rep_aniso (h2 : IsTwoAdic R) {Lm Kp : Submodule R V} (hLfg : Lm.FG) (hLreg : IsRegular Q Lm)
    (hKreg : IsRegular Q Kp) {x y u v : V} {ρ a : R} (hxK : x ∈ Kp) (hyK : y ∈ Kp) (hx : Q x = 0)
    (hxy : bil Q x y = 1) (hu : Q u = 2) (huv : bil Q u v = 1) (hv : Q v = 2 * algebraMap R F ρ)
    (hxu : bil Q x u = 0) (hxv : bil Q x v = 0) (hyu : bil Q y u = 0) (hyv : bil Q y v = 0)
    (hspan : ∀ k ∈ span F (Kp : Set V), ∃ p q s r : F, k = p • x + q • y + s • u + r • v)
    (hno : ∀ t : R, t ^ 2 + t + ρ ∉ maximalIdeal R) (ha : IsUnit a)
    (T : Submodule F V) (hT0 : ∀ z ∈ T, Q z = 0) (hTL : ∀ z ∈ T, z ∈ span F (Lm : Set V))
    (hr4 : finrank R Lm = 4) (hrk : finrank R Lm ≤ 2 * finrank F T)
    (hrep : SpanRepresents Q Lm Kp (algebraMap R F a)) : False := by
  classical
  have ha0 : algebraMap R F a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 ha.ne_zero
  rw [RepTransfer.spanRepresents_iff_rep] at hrep
  obtain ⟨f, hf, hQ⟩ := hrep
  set c : F := algebraMap R F a with hc
  let QW : QuadraticForm F (D18.spanF F Kp × F) :=
    (D18.subQ Q Kp).prod (c • (QuadraticMap.sq : QuadraticForm F F))
  have hnd : (polarBilin QW).Nondegenerate := QuadraticForm.nondegenerate_polarBilin_prod
    (RepTransfer.nondegenerate_subQ Q hKreg) (RepTransfer.nondegenerate_smul_sq ha0)
  let TL : Submodule F (D18.spanF F Lm) := T.comap (D18.spanF F Lm).subtype
  have hTLfin : finrank F TL = finrank F T := by
    have h := Submodule.finrank_map_subtype_eq (D18.spanF F Lm) TL
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr (fun z hz => hTL z hz)] at h
    exact h.symm
  let S : Submodule F (D18.spanF F Kp × F) := TL.map f
  have hSfin : finrank F S = finrank F TL := (Submodule.equivMapOfInjective f hf TL).finrank_eq.symm
  have hS0 : ∀ z ∈ S, QW z = 0 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hQ t]; exact hT0 _ ht
  have hT2 : 2 ≤ finrank F S := by rw [hSfin, hTLfin]; omega
  -- the hyperbolic pair in `N × F`
  have hxx : bil Q x x = 0 := by rw [bil_self, hx]
  have hyx : bil Q y x = 1 := by rw [bil_comm]; exact hxy
  have hux : bil Q u x = 0 := by rw [bil_comm]; exact hxu
  have hvx : bil Q v x = 0 := by rw [bil_comm]; exact hxv
  have huy : bil Q u y = 0 := by rw [bil_comm]; exact hyu
  have hvy : bil Q v y = 0 := by rw [bil_comm]; exact hyv
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  set c' : F := Q y / 2 with hc'
  set f' : V := y - c' • x with hf'
  have hyy : bil Q y y = Q y := bil_self Q y
  have hf'0 : Q f' = 0 := by
    have e : bil Q f' f' = Q y - 2 * c' := by
      simp only [hf', bil_sub_left, bil_sub_right, bil_smul_left, bil_smul_right, hxx, hyx, hxy, hyy]; ring
    rw [← bil_self, e, hc']; field_simp; ring
  have hxf' : bil Q x f' = 1 := by
    simp only [hf', bil_sub_right, bil_smul_right, hxx, hxy]; ring
  have hxN : x ∈ span F (Kp : Set V) := subset_span hxK
  have hf'N : f' ∈ span F (Kp : Set V) :=
    sub_mem (subset_span hyK) (Submodule.smul_mem _ _ hxN)
  let xW : D18.spanF F Kp × F := (⟨x, hxN⟩, 0)
  let fW : D18.spanF F Kp × F := (⟨f', hf'N⟩, 0)
  have hQW0 : ∀ n : D18.spanF F Kp, QW (n, 0) = Q (n : V) := fun n => by
    simp [QW, QuadraticMap.prod_apply, D18.subQ]
  have hpolW : ∀ (k : D18.spanF F Kp) (z : F) (n : D18.spanF F Kp),
      polar QW (k, z) (n, 0) = polar Q (k : V) (n : V) := by
    intro k z n
    simp only [QuadraticMap.polar, QW, QuadraticMap.prod_apply, D18.subQ, QuadraticMap.comp_apply,
      Prod.mk_add_mk, add_zero, Submodule.coe_add, Submodule.subtype_apply]
    simp [QuadraticMap.sq_apply]
  have hxW : QW xW = 0 := by rw [hQW0]; exact hx
  have hpol : polar QW xW fW ≠ 0 := by
    have := hpolW ⟨x, hxN⟩ 0 ⟨f', hf'N⟩
    show polar QW (⟨x, hxN⟩, 0) (⟨f', hf'N⟩, 0) ≠ 0
    rw [this, RepTransfer.polar_eq_two_bil Q]
    have h1 : bil Q x f' ≠ 0 := by rw [hxf']; exact one_ne_zero
    exact mul_ne_zero h2F h1
  obtain ⟨S', hS'0, hS'perp, hrk'⟩ := Dim4.exists_isotropic_perp_pair QW hnd hxW hpol S hS0
  have hS'ne : S' ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hrk'
    omega
  obtain ⟨⟨k, z⟩, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS'ne
  obtain ⟨hwx, hwf⟩ := hS'perp _ hw
  have hQw := hS'0 _ hw
  have hbx : bil Q (k : V) x = 0 := by
    have := hpolW k z ⟨x, hxN⟩
    rw [RepTransfer.polar_eq_two_bil Q] at this
    have h' : polar QW (k, z) xW = 0 := hwx
    rw [show xW = (⟨x, hxN⟩, 0) from rfl, this] at h'
    exact (mul_eq_zero.1 h').resolve_left h2F
  have hbf : bil Q (k : V) f' = 0 := by
    have := hpolW k z ⟨f', hf'N⟩
    rw [RepTransfer.polar_eq_two_bil Q] at this
    have h' : polar QW (k, z) fW = 0 := hwf
    rw [show fW = (⟨f', hf'N⟩, 0) from rfl, this] at h'
    exact (mul_eq_zero.1 h').resolve_left h2F
  obtain ⟨p, q, s', r, hk⟩ := hspan (k : V) k.2
  have e1 : bil Q (k : V) x = q := by
    rw [hk]; simp only [bil_add_left, bil_smul_left, hxx, hyx, hux, hvx]; ring
  have e2 : bil Q (k : V) y = p + q * Q y := by
    rw [hk]; simp only [bil_add_left, bil_smul_left, hxy, bil_self, huy, hvy]; ring
  have hq : q = 0 := by rw [← e1]; exact hbx
  have hbf' : bil Q (k : V) f' = bil Q (k : V) y - c' * bil Q (k : V) x := by
    simp only [hf', bil_sub_right, bil_smul_right]
  have hp : p = 0 := by
    rw [hbf, e2, e1, hq] at hbf'
    simpa using hbf'.symm
  have hQk : Q (k : V) = 2 * (s' ^ 2 + s' * r + algebraMap R F ρ * r ^ 2) := by
    have huu : bil Q u u = 2 := by rw [bil_self, hu]
    have hvv : bil Q v v = 2 * algebraMap R F ρ := by rw [bil_self, hv]
    refine (bil_self Q (k : V)).symm.trans ?_
    rw [hk, hq, hp]
    simp only [zero_smul, zero_add, bil_add_left, bil_add_right, bil_smul_left, bil_smul_right, huu, hvv,
      huv, bil_comm Q v u]
    ring
  have hQw' : Q (k : V) + c * z ^ 2 = 0 := by
    have : QW (k, z) = Q (k : V) + c * z ^ 2 := by
      simp [QW, QuadraticMap.prod_apply, D18.subQ, QuadraticMap.smul_apply, QuadraticMap.sq_apply, pow_two]
    rw [← this]; exact hQw
  rw [hQk] at hQw'
  obtain ⟨hs0, hr0, hz0⟩ := ternary_aniso h2 hno ha hQw'
  apply hw0
  have hk0 : (k : V) = 0 := by rw [hk, hp, hq, hs0, hr0]; simp
  rw [show k = 0 from Subtype.ext hk0, hz0]
  rfl

end NoRep

section Aux

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open QuadFormsKB.OMeara Suff28 CoreHyp NecBlock Merge28

/-- Over a 2-adic field every Jordan splitting is saturated. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
theorem isSaturated_of_twoAdic (h2 : IsTwoAdic R) {K : Submodule R V} (hKfg : K.FG) (hKreg : IsRegular Q K) {t : ℕ}
    {Ks : Fin t → Submodule R V} (hK : IsJordanSplitting Q K Ks) : IsSaturated Q K Ks := by
  refine ⟨hK, fun i => ?_⟩
  have hle : Ks i ≤ K := hK.split.iSup_eq ▸ le_iSup Ks i
  have hifg : (Ks i).FG := FG.of_le hKfg hle
  apply SetLike.coe_injective
  rw [normGroup_eq_normIdeal_twoAdic Q h2 hifg ((hK.modular i).isRegular Q hifg)
      (CoreTwo.ne_bot_of_isModular (R := R) Q (hK.modular i)),
    fundNormGroup_eq_normIdeal_twoAdic Q h2 hKfg hKreg hK i]

/-- Orthogonality of two planes. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
theorem bil_zero_span_pair {a₁ a₂ b₁ b₂ : V} (h : bil Q a₁ b₁ = 0 ∧ bil Q a₁ b₂ = 0 ∧ bil Q a₂ b₁ = 0 ∧ bil Q a₂ b₂ = 0)
    {u v : V} (hu : u ∈ span R {a₁, a₂}) (hv : v ∈ span R {b₁, b₂}) : bil Q u v = 0 := by
  obtain ⟨r₁, r₂, rfl⟩ := Submodule.mem_span_pair.mp hu
  obtain ⟨s₁, s₂, rfl⟩ := Submodule.mem_span_pair.mp hv
  simp only [bil_add_left, bil_add_right, bil_rsmul_left, bil_rsmul_right, h.1, h.2.1, h.2.2.1, h.2.2.2]
  ring

/-- A block base with two blocks gives a base with Gram determinant $1$ (the blocks $A(c, 0) \perp A(c', 0)$). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
theorem exists_basis_det_one_of_blockBase {B : Submodule R V} {x : Fin 2 → V × V} (hx : IsBlockBase Q B x) :
    ∃ b : Basis (Fin 4) R B, (gram Q fun i => (b i : V)).det = 1 := by
  obtain ⟨hsp, hQ0, h1, hee, hef, hff⟩ := hx
  set v : Fin 4 → V := ![(x 0).1, (x 0).2, (x 1).1, (x 1).2] with hv
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have e11 : bil Q (x 0).2 (x 0).2 = 0 := by rw [bil_self, hQ0]
  have e22 : bil Q (x 1).2 (x 1).2 = 0 := by rw [bil_self, hQ0]
  have f10 : bil Q (x 0).2 (x 0).1 = 1 := by rw [bil_comm]; exact h1 0
  have f32 : bil Q (x 1).2 (x 1).1 = 1 := by rw [bil_comm]; exact h1 1
  have f20 : bil Q (x 1).1 (x 0).1 = 0 := hee 1 0 h10
  have f30 : bil Q (x 1).2 (x 0).1 = 0 := by rw [bil_comm]; exact hef 0 1 h01
  have f21 : bil Q (x 1).1 (x 0).2 = 0 := hef 1 0 h10
  have f12 : bil Q (x 0).2 (x 1).1 = 0 := by rw [bil_comm]; exact hef 1 0 h10
  have f31 : bil Q (x 1).2 (x 0).2 = 0 := hff 1 0 h10
  have hg : gram Q v = D18.blk2 (Q (x 0).1) 0 (Q (x 1).1) 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gram, hv, D18.blk2, bil_self, h1 0, h1 1, hee 0 1 h01, hef 0 1 h01, hff 0 1 h01, e11, e22, f10, f32,
        f20, f30, f21, f12, f31, hQ0]
  have hdet : (gram Q v).det = 1 := by rw [hg, D18.det_blk2]; ring
  have hli : LinearIndependent R v :=
    linearIndependent_of_det_gram_ne_zero (R := R) Q (by rw [hdet]; exact one_ne_zero)
  have hrange : (Set.range v : Set V) = Set.range (fun k => (x k).1) ∪ Set.range (fun k => (x k).2) := by
    ext z
    simp only [Set.mem_range, Set.mem_union, hv, Fin.exists_fin_succ, Fin.exists_fin_two]
    simp [Fin.forall_fin_succ]
    tauto
  have hspan : span R (Set.range v) = B := by rw [hrange]; exact hsp
  let b : Basis (Fin 4) R B := (Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  refine ⟨b, ?_⟩
  have : (fun i => (b i : V)) = v := funext fun i => by simp [b, Basis.span_apply]
  rw [this, hdet]

/-- Scaling the first base vector by a unit $\varepsilon$ multiplies the discriminant by $\varepsilon^2$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
theorem exists_basis_det_scale {M : Submodule R V} (b : Basis (Fin 4) R M) {ε : R} (hε : IsUnit ε) :
    ∃ b' : Basis (Fin 4) R M, (gram Q fun i => (b' i : V)).det = algebraMap R F ε ^ 2 *
      (gram Q fun i => (b i : V)).det := by
  classical
  let w : Fin 4 → Rˣ := fun i => if i = 0 then hε.unit else 1
  refine ⟨b.unitsSMul w, ?_⟩
  set c : Fin 4 → F := fun i => algebraMap R F (w i : R) with hc
  have hgr : (gram Q fun i => ((b.unitsSMul w) i : V)) =
      Matrix.diagonal c * gram Q (fun i => (b i : V)) * Matrix.diagonal c := by
    ext i j
    simp only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.diagonal_apply, Basis.unitsSMul_apply,
      Submodule.coe_smul, bil_rsmul_left, bil_rsmul_right]
    simp [Finset.sum_ite_eq, hc, Units.smul_def, Algebra.smul_def]
    ring
  rw [hgr, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hprod : ∏ i, c i = algebraMap R F ε := by
    simp [hc, w, Fin.prod_univ_four]
  rw [hprod]; ring

open Nec93 in
/-- **$\mathfrak f_1 = 4\mathfrak o$ in the case $\mathfrak n_1 = \mathfrak o$, $\mathfrak n_2 = 4\mathfrak o$** (O'Meara 1963, §93G,
p. 277–278, from 93:26): over a 2-adic field, for a Jordan splitting with $\mathfrak sL_1 = \mathfrak o$,
$\mathfrak nL_1 = \mathfrak o$ and $\mathfrak nL_2 = 4\mathfrak o$ ($0$-based `0`, `1`). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
theorem fIdeal_four (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L) {t : ℕ}
    {Ls : Fin (t + 2) → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hs : scale Q (Ls 0) = 1)
    (hn0 : normIdeal Q (Ls 0) = 1) (hn1 : normIdeal Q (Ls 1) = R ∙ (4 : F)) :
    fIdeal Q L Ls 0 1 = R ∙ (4 : F) := by
  have hπ := twoAdic_irreducible h2
  obtain ⟨u, σ, τ, k, hu, hσ0, hτ0, hσ, hτ, hk, p1, p2, q1, q2, hst, hcase⟩ :=
    exists_data Q h2 hfg hreg hL (i := 0) (j := 1) (by simp)
  have z2 : ∀ w : ℤ, (2 : F) ^ w ≠ 0 := fun w => two_zpow_ne_zero w
  have hσ1 : R ∙ σ = R ∙ ((2 : F) ^ (0 : ℤ)) := by rw [← hσ, hs, zpow_zero, ← Submodule.one_eq_span]
  have hdσ : dord hπ σ = 0 := by
    have h1 : σ ∈ R ∙ ((2 : F) ^ (0 : ℤ)) := hσ1 ▸ mem_span_singleton_self σ
    have h2' : (2 : F) ^ (0 : ℤ) ∈ R ∙ σ := hσ1 ▸ mem_span_singleton_self _
    rw [mem_span_two_zpow_iff h2 hσ0] at h1
    rw [mem_span_iff hπ (z2 0) hσ0, dord_two_zpow h2] at h2'
    omega
  have hu0 : u 0 = 0 := by
    have e1 : (2 : F) ^ u 0 ∈ R ∙ ((2 : F) ^ (0 : ℤ)) := by
      rw [zpow_zero, ← Submodule.one_eq_span, ← hn0, ← hu 0]; exact mem_span_singleton_self _
    have e2 : (2 : F) ^ (0 : ℤ) ∈ R ∙ ((2 : F) ^ u 0) := by
      rw [hu 0, hn0, zpow_zero]; exact ⟨1, by simp⟩
    rw [mem_span_two_zpow_iff h2 (z2 _), dord_two_zpow h2] at e1 e2
    omega
  have hu1 : u 1 = 2 := by
    have h4 : (4 : F) = (2 : F) ^ (2 : ℤ) := by norm_num
    have e1 : (2 : F) ^ u 1 ∈ R ∙ ((2 : F) ^ (2 : ℤ)) := by
      rw [← h4, ← hn1, ← hu 1]; exact mem_span_singleton_self _
    have e2 : (2 : F) ^ (2 : ℤ) ∈ R ∙ ((2 : F) ^ u 1) := by
      rw [hu 1, hn1, h4]; exact mem_span_singleton_self _
    rw [mem_span_two_zpow_iff h2 (z2 _), dord_two_zpow h2] at e1 e2
    omega
  have hk2 : k = 2 := by
    rcases hcase with ⟨ho, -⟩ | ⟨-, hk'⟩
    · exfalso; obtain ⟨m, hm⟩ := ho; omega
    · omega
  rw [hs, one_mul, one_mul, hk2] at hk
  rw [hk]; norm_num

/-- $4\mathfrak o \subsetneq 4a\cdot 2^{-1}\mathfrak o = 2\mathfrak o$ when $a\mathfrak o = \mathfrak o$ (2-adic). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
theorem strict_four (h2 : IsTwoAdic R) {a0 : F} (ha0 : R ∙ a0 = 1) :
    R ∙ (4 : F) < R ∙ (4 * a0 * (2 : F)⁻¹) := by
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  have hone : (1 : F) ∈ R ∙ a0 := by rw [ha0]; exact ⟨1, by simp⟩
  obtain ⟨s, hs⟩ := mem_span_singleton.mp hone
  have ha : a0 ∈ (1 : Submodule R F) := by rw [← ha0]; exact mem_span_singleton_self _
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp ha
  have hs' : algebraMap R F s * a0 = 1 := by rw [← hs, Algebra.smul_def]
  have h4 : (4 : F) = 2 * 2 := by norm_num
  refine lt_of_le_of_ne ?_ ?_
  · rw [Submodule.span_singleton_le_iff_mem, mem_span_singleton]
    refine ⟨2 * s, ?_⟩
    rw [Algebra.smul_def, map_mul, map_ofNat, h4]
    field_simp
    linear_combination hs'
  · intro heq
    have hmem : 4 * a0 * (2 : F)⁻¹ ∈ R ∙ (4 : F) := by rw [heq]; exact mem_span_singleton_self _
    obtain ⟨c, hc⟩ := mem_span_singleton.mp hmem
    rw [Algebra.smul_def] at hc
    have hrc : algebraMap R F r = algebraMap R F (2 * c) := by
      rw [hr, map_mul, map_ofNat]
      field_simp at hc
      linear_combination -hc
    have hrc' := IsFractionRing.injective R F hrc
    have hmax : r ∈ maximalIdeal R := by
      rw [hrc']; exact Ideal.mul_mem_right _ _ (two_mem_maximal h2)
    have hunit : IsUnit r := by
      refine isUnit_iff_exists_inv.mpr ⟨s, ?_⟩
      apply IsFractionRing.injective R F
      rw [map_mul, map_one, hr, mul_comm]; exact hs'
    exact (IsLocalRing.mem_maximalIdeal _).1 hmax hunit

/-- The vectors of a base with matrix $A(\alpha, \beta) \perp A(\gamma, \delta)$: $M = (\mathfrak o x + \mathfrak o y) \perp
(\mathfrak o u + \mathfrak o v)$ with $Q(x) = \beta$, $Q(y) = \alpha$, $B(x, y) = 1$, $Q(u) = \gamma$, $Q(v) = \delta$,
$B(u, v) = 1$ (the first block listed as $(x, y) = (e_1, e_0)$). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
theorem blk2_facts {M : Submodule R V} (e : Basis (Fin 4) R M) {α β γ δ : F}
    (hg : gram Q (fun i => (e i : V)) = D18.blk2 α β γ δ) :
    ∃ x y u v : V, x ∈ M ∧ y ∈ M ∧ u ∈ M ∧ v ∈ M ∧ Q x = β ∧ Q y = α ∧ bil Q x y = 1 ∧ Q u = γ ∧ Q v = δ ∧
      bil Q u v = 1 ∧ (bil Q x u = 0 ∧ bil Q x v = 0 ∧ bil Q y u = 0 ∧ bil Q y v = 0) ∧
      M = span R {x, y} ⊔ span R {u, v} := by
  have g : ∀ i j, bil Q (e i : V) (e j : V) = D18.blk2 α β γ δ i j := fun i j => by
    have := congrFun (congrFun hg i) j
    simpa [gram] using this
  have g00 : Q (e 0 : V) = α := by rw [← bil_self, g]; simp [D18.blk2]
  have g11 : Q (e 1 : V) = β := by rw [← bil_self, g]; simp [D18.blk2]
  have g22 : Q (e 2 : V) = γ := by rw [← bil_self, g]; simp [D18.blk2]
  have g33 : Q (e 3 : V) = δ := by rw [← bil_self, g]; simp [D18.blk2]
  have g10 : bil Q (e 1 : V) (e 0 : V) = 1 := by rw [g]; simp [D18.blk2]
  have g23 : bil Q (e 2 : V) (e 3 : V) = 1 := by rw [g]; simp [D18.blk2]
  have g12 : bil Q (e 1 : V) (e 2 : V) = 0 := by rw [g]; simp [D18.blk2]
  have g13 : bil Q (e 1 : V) (e 3 : V) = 0 := by rw [g]; simp [D18.blk2]
  have g02 : bil Q (e 0 : V) (e 2 : V) = 0 := by rw [g]; simp [D18.blk2]
  have g03 : bil Q (e 0 : V) (e 3 : V) = 0 := by rw [g]; simp [D18.blk2]
  refine ⟨(e 1 : V), (e 0 : V), (e 2 : V), (e 3 : V), (e 1).2, (e 0).2, (e 2).2, (e 3).2, g11, g00, g10, g22, g33,
    g23, ⟨g12, g13, g02, g03⟩, ?_⟩
  apply le_antisymm
  · intro z hz
    have hz' : z = ∑ i, (e.repr ⟨z, hz⟩ i) • (e i : V) := by
      have := congrArg Subtype.val (e.sum_repr ⟨z, hz⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hz']
    refine Submodule.sum_mem _ fun i _ => ?_
    fin_cases i
    · exact mem_sup_left (Submodule.smul_mem _ _ (subset_span (by simp)))
    · exact mem_sup_left (Submodule.smul_mem _ _ (subset_span (by simp)))
    · exact mem_sup_right (Submodule.smul_mem _ _ (subset_span (by simp)))
    · exact mem_sup_right (Submodule.smul_mem _ _ (subset_span (by simp)))
  · refine sup_le (span_le.mpr ?_) (span_le.mpr ?_)
    · rintro _ (rfl | rfl)
      · exact (e 1).2
      · exact (e 0).2
    · rintro _ (rfl | rfl)
      · exact (e 2).2
      · exact (e 3).2

open Nec93 in
/-- **Condition (iii) at the first index is required** (O'Meara 1963, §93G, p. 278): $\mathfrak f_1 = 4\mathfrak o \subsetneq
4a_1\mathfrak w_1^{-1} = 2\mathfrak o$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
theorem hlt_four (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L) {t : ℕ}
    {Ls : Fin (t + 2) → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hs : scale Q (Ls 0) = 1)
    (hn0 : normIdeal Q (Ls 0) = 1) (hn1 : normIdeal Q (Ls 1) = R ∙ (4 : F)) {a0 : F} (ha0 : R ∙ a0 = 1) :
    fIdeal Q L Ls 0 1 < (4 * a0) • (1 / fundWeight Q L Ls 0) := by
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  have hw : fundWeight Q L Ls 0 = R ∙ (2 : F) := by
    rw [fundWeight_eq_two_smul_scale_twoAdic Q h2 hfg hreg hL 0, hs, Submodule.one_eq_span,
      FIdealAux.smul_span_singleton, mul_one]
  rw [fIdeal_four Q h2 hfg hreg hL hs hn0 hn1, hw, one_div_span h2F, FIdealAux.smul_span_singleton]
  exact strict_four h2 ha0

/-- **The discriminant of $K_1$ in the form $1 + \alpha$ with $\mathfrak d(1+\alpha) = \alpha\mathfrak o$ and
$\alpha \in 4\mathfrak o$** (O'Meara 1963, §93G, p. 278: "$dK_1 \cong 1 \bmod 4\mathfrak o$"): if the discriminant of a
base is $(\varepsilon^2 + 4c)^{-1}$ ($\varepsilon$ and $\varepsilon^2 + 4c$ units, 2-adic field), then after scaling a base
vector by a unit it is $1 + \alpha$ with $\alpha = 0$ or $\alpha = 4\gamma$, $\mathfrak d(1+\alpha) = \alpha\mathfrak o$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
theorem exists_alpha (h2 : IsTwoAdic R) {M : Submodule R V} (bK : Basis (Fin 4) R M) {w ε c : R} (hw : IsUnit w)
    (hε : IsUnit ε) (hwe : w = ε ^ 2 + 4 * c)
    (hd : (gram Q fun i => (bK i : V)).det = (algebraMap R F w)⁻¹) :
    ∃ α : R, (∃ c' : R, α = 4 * c') ∧
      (∃ b' : Basis (Fin 4) R M, (gram Q fun i => (b' i : V)).det = 1 + algebraMap R F α) ∧
      quadDefect R (1 + algebraMap R F α) = span R {algebraMap R F α} := by
  have hπ := twoAdic_irreducible h2
  have h2R : (2 : R) ≠ 0 := hπ.ne_zero
  obtain ⟨wi, hwi⟩ := hw.exists_right_inv
  have hwiF : algebraMap R F wi = (algebraMap R F w)⁻¹ := by
    have hne : algebraMap R F w ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hw.ne_zero
    have h1 : algebraMap R F wi * algebraMap R F w = 1 := by rw [← map_mul, mul_comm, hwi, map_one]
    exact eq_inv_of_mul_eq_one_left h1
  have hwiu : IsUnit wi := isUnit_iff_exists_inv.mpr ⟨w, by rw [mul_comm]; exact hwi⟩
  set γ₀ : R := -c * wi with hγ₀
  set α₀ : R := 4 * γ₀ with hα₀
  have hδ : ε ^ 2 * wi = 1 + α₀ := by
    have : ε ^ 2 = w - 4 * c := by rw [hwe]; ring
    rw [this, hα₀, hγ₀]; linear_combination hwi
  have hδu : IsUnit (ε ^ 2 * wi) := (hε.pow 2).mul hwiu
  have hdF : (gram Q fun i => (bK i : V)).det = algebraMap R F wi := by rw [hd, hwiF]
  have hdefle : quadDefect R (1 + algebraMap R F α₀) ≤ span R {algebraMap R F α₀} :=
    D18.quadDefect_one_add_le _
  have hδF : algebraMap R F (ε ^ 2 * wi) = 1 + algebraMap R F α₀ := by rw [hδ, map_add, map_one]
  have hα4 : span R {algebraMap R F α₀} ≤ span R {(4 : F)} := by
    rw [Submodule.span_singleton_le_iff_mem, mem_span_singleton]
    refine ⟨γ₀, ?_⟩
    simp only [hα₀, Algebra.smul_def, map_mul, map_ofNat]; ring
  rcases quadDefect_unit_dyadic (F := F) h2R (twoAdic_irreducible h2).not_isUnit hπ hδu with
    hbot | h4 | ⟨d, hd', hlt, heq⟩
  · -- the discriminant is a square
    have hsq := (isSquare_iff_quadDefect_eq_bot h2R _).2 hbot
    obtain ⟨η, hη⟩ := hsq
    obtain ⟨η', rfl⟩ := exists_alg_of_sq (R := R) (η := η) (c := ε ^ 2 * wi) (by rw [pow_two, ← hη])
    have hη2 : η' ^ 2 = ε ^ 2 * wi :=
      IsFractionRing.injective R F (by rw [map_pow]; simpa [pow_two] using hη.symm)
    have hη'u : IsUnit η' := (isUnit_pow_iff two_ne_zero).1 (hη2 ▸ hδu)
    obtain ⟨ηi, hηi⟩ := hη'u.exists_right_inv
    have hε₂ : IsUnit (ε * ηi) := hε.mul (isUnit_iff_exists_inv.mpr ⟨η', by rw [mul_comm]; exact hηi⟩)
    obtain ⟨b', hb'⟩ := exists_basis_det_scale Q bK hε₂
    refine ⟨0, ⟨0, by ring⟩, ⟨b', ?_⟩, ?_⟩
    · rw [hb', hdF, map_zero, add_zero, ← map_pow, ← map_mul, ← map_one (algebraMap R F)]
      congr 1
      have : (ε * ηi) ^ 2 * wi = (ε ^ 2 * wi) * ηi ^ 2 := by ring
      rw [this, ← hη2]
      linear_combination (η' * ηi + 1) * ηi * η' * 0 + (η' * ηi + 1) * hηi
    · rw [map_zero, add_zero, span_singleton_eq_bot.mpr rfl]
      simpa using (FundAux.quadDefect_sq_eq_bot (R := R) (1 : F))
  · -- defect `4𝔬`
    obtain ⟨b', hb'⟩ := exists_basis_det_scale Q bK hε
    refine ⟨α₀, ⟨γ₀, rfl⟩, ⟨b', ?_⟩, ?_⟩
    · rw [hb', hdF, ← map_pow, ← map_mul, hδF]
    · rw [hδF] at h4
      rw [h4] at hdefle ⊢
      exact le_antisymm hdefle hα4
  · exfalso
    rw [← hδF] at hdefle
    rw [heq] at hdefle
    exact hlt.ne (le_antisymm hlt.le (hdefle.trans hα4))

end Aux

section Finish

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]

open QuadFormsKB.OMeara Suff28 CoreHyp NecBlock Merge28 SuffGood Sat93

/-- **The final step of the case $\mathfrak n_1 = \mathfrak o$, $\mathfrak n_2 = 4\mathfrak o$** (O'Meara 1963, §93G, p. 278): if
$K_1$ has a base with matrix $A(1, \varepsilon) \perp A(2, \delta)$, $\varepsilon \in 4\mathfrak o$,
$\delta = 0$ or $\delta = 2\rho$ ($X^2 + X + \rho$ without root mod $\mathfrak p$), then $K$ has a saturated splitting
with $FK_1'$ hyperbolic. The first block is moved to $A(1, 0)$ by 93:19 (`exists_shift_first`, $\varepsilon \in
\mathfrak gK_2 = 4\mathfrak o$); if $\delta = 2\rho$, condition (iii) at the first index
gives $FL_1 \to FK_1' \perp \langle a_1\rangle$ with $FK_1' = H \perp F\!A(2, 2\rho)$ and $FL_1$ hyperbolic, which is
impossible (`no_rep_aniso`). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o)"]
theorem finish (hHil : PadicClass.LocalHilbertField F) (h2 : IsTwoAdic R) (Q : QuadraticForm F V)
    (h2p : ¬ IsUnit (2 : R)) (hQ : (QuadraticMap.associated Q).Nondegenerate) (L K : Submodule R V)
    [hLl : L.IsLattice F] [hKl : K.IsLattice F] (m : ℕ) (Ls Ks : Fin (m + 2) → Submodule R V)
    (a : Fin (m + 2) → F) (hLs : IsSaturated Q L Ls) (hKs : IsSaturated Q K Ks)
    (hd : ∀ k, finrank R (Ls k) = 4)
    (hT : ∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
      finrank R (Ls k) ≤ 2 * finrank F T)
    (hsc : scale Q (Ls 0) = 1) (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hC : Cond93 Q L Ls Ks a)
    (ha0 : R ∙ a 0 = 1) (ha1 : R ∙ a 1 = R ∙ (4 : F))
    (e : Basis (Fin 4) R (Ks 0)) {ε δ : R} (hε : ∃ c : R, ε = 4 * c)
    (hg : gram Q (fun i => (e i : V)) = D18.blk2 (1 : F) (algebraMap R F ε) (2 : F) (algebraMap R F δ))
    (hδ : δ = 0 ∨ ∃ ρ : R, δ = 2 * ρ ∧ ∀ t : R, t ^ 2 + t + ρ ∉ maximalIdeal R) :
    ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧
      ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ks' 0 : Set V)) ∧
        finrank R (Ks' 0) ≤ 2 * finrank F T := by
  classical
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hKreg : IsRegular Q K := isRegular_of_lattice_max Q hQ hKl
  have hLreg : IsRegular Q L := isRegular_of_lattice_max Q hQ hLl
  have hKle : ∀ k, Ks k ≤ K := fun k => hKs.1.split.iSup_eq ▸ le_iSup Ks k
  have hLle : ∀ k, Ls k ≤ L := fun k => hLs.1.split.iSup_eq ▸ le_iSup Ls k
  obtain ⟨⟨h0, hTy⟩, -, -⟩ := id hS
  have hc0 : ∀ k : Fin (m + 2), Fin.cast h0 k = k := fun k => Fin.ext rfl
  have hs0K : scale Q (Ks 0) = 1 := by
    have := (hTy 0).2.1; rw [hc0] at this; rw [← this]; exact hsc
  have hrk4K : ∀ k, finrank R (Ks k) = 4 := fun k => by
    have := (hTy k).1; rw [hc0] at this; rw [← this]; exact hd k
  have hK1fg : (Ks 1).FG := FG.of_le hKfg (hKle 1)
  have haK : ∀ i, R ∙ a i = normIdeal Q (Ks i) := fun i => by
    rw [(hS.2.2 i).2, ← fundNormIdeal_eq_normIdeal_twoAdic Q h2 hKfg hKs.1 i]; rfl
  have haL : ∀ i, R ∙ a i = normIdeal Q (Ls i) := fun i => by
    rw [(hS.2.1 i).2, ← fundNormIdeal_eq_normIdeal_twoAdic Q h2 hLfg hLs.1 i]; rfl
  obtain ⟨x, y, u, v, hxM, hyM, huM, hvM, hQx, hQy, hxy, hQu, hQv, huv, ⟨hxu, hxv, hyu, hyv⟩, hdecomp⟩ :=
    blk2_facts Q e hg
  obtain ⟨c, hc⟩ := hε
  have hεm : ε ∈ maximalIdeal R := by
    rw [hc]
    exact Ideal.mul_mem_right _ _ (by
      have : (4 : R) = 2 * 2 := by norm_num
      rw [this]; exact Ideal.mul_mem_right _ _ (two_mem_maximal h2))
  have hK0fg : (Ks 0).FG := FG.of_le hKfg (hKle 0)
  have hαβ : IsUnit (ε * 1 - 1 * 1) := by
    have : ε * 1 - 1 * 1 = -(1 - ε) := by ring
    rw [this, IsUnit.neg_iff]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((IsLocalRing.mem_maximalIdeal _).mp hεm)
  have hJmod := D18.span_pair_isModular Q (R := R) (one_ne_zero : (1 : F) ≠ 0) hαβ
    (by rw [hQx, one_mul]) (by rw [hQy, one_mul, map_one]) (by rw [hxy, one_mul, map_one])
  have hJfg : (span R {x, y} : Submodule R V).FG := Submodule.fg_span (Set.toFinite _)
  have hJreg : IsRegular Q (span R {x, y}) := IsModular.isRegular Q hJmod.1 hJfg
  have horthJC : ∀ w ∈ span R {x, y}, ∀ z ∈ span R {u, v}, bil Q w z = 0 := fun w hw z hz =>
    bil_zero_span_pair Q ⟨hxu, hxv, hyu, hyv⟩ hw hz
  have hJC : IsOrthSum Q (Ks 0) (span R {x, y}) (span R {u, v}) :=
    ⟨horthJC, disjoint_of_orth Q hJreg horthJC, hdecomp.symm⟩
  have hrk1 : 3 ≤ finrank R (Ks 1) := by rw [hrk4K]; norm_num
  have hn1 : normIdeal Q (Ks 1) = R ∙ (4 : F) := (haK 1).symm.trans ha1
  have hset := normGroup_eq_normIdeal_twoAdic Q h2 hK1fg ((hKs.1.modular 1).isRegular Q hK1fg)
    (CoreTwo.ne_bot_of_isModular (R := R) Q (hKs.1.modular 1))
  have hγ : algebraMap R F (-ε) ∈ normGroup Q (Ks 1) := by
    rw [← SetLike.mem_coe, hset, hn1]
    refine mem_span_singleton.mpr ⟨-c, ?_⟩
    rw [hc, Algebra.smul_def]; simp only [map_neg, map_mul, map_ofNat]; ring
  have hdet : IsUnit ((ε + -ε) * 1 - 1 * 1) := by simp
  obtain ⟨Ks', hKs'J, hsame, x', y', hQx', hx'y', hQy', hJ'C⟩ :=
    CoreTwo.exists_shift_first Q hHil h2p hKfg hKs.1 hs0K hJC (α := ε) (β := 1) hQx hxy
      (by rw [hQy, map_one]) hεm hrk1 hγ hdet
  have hKs'sat : IsSaturated Q K Ks' := isSaturated_of_twoAdic Q h2 hKfg hKreg hKs'J
  have hQx'0 : Q x' = 0 := by rw [hQx']; simp
  refine ⟨Ks', hKs'sat, ?_⟩
  have hK'0fg : (Ks' 0).FG := FG.of_le hKfg (hKs'J.split.iSup_eq ▸ le_iSup Ks' 0)
  have hK'0reg : IsRegular Q (Ks' 0) := (hKs'J.modular 0).isRegular Q hK'0fg
  have hPK : span R {x', y'} ≤ Ks' 0 := hJ'C.sup_eq ▸ le_sup_left
  have hCK : span R {u, v} ≤ Ks' 0 := hJ'C.sup_eq ▸ le_sup_right
  have hx'K : x' ∈ Ks' 0 := hPK (subset_span (by simp))
  have hy'K : y' ∈ Ks' 0 := hPK (subset_span (by simp))
  have hyx : bil Q y' x' = 1 := by rw [bil_comm]; exact hx'y'
  have hpair : span R {y', x'} = span R {x', y'} := by rw [Set.pair_comm]
  rcases hδ with hδ0 | ⟨ρ, hδρ, hno⟩
  · subst hδ0
    have hQv0 : Q v = 0 := by rw [hQv, map_zero]
    have hb0 : IsBlockBase Q (⊥ : Submodule R V) (Fin.elim0 : Fin 0 → V × V) :=
      ⟨by simp [pairSpan], fun k => k.elim0, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0,
        fun k => k.elim0⟩
    have hC1 := CoreTwo.isBlockBase_cons Q hb0 hQv0 huv
      (by intro w _ z hz; rw [(mem_bot R).1 hz]; simp [bil])
    have horth : ∀ w ∈ span R {y', x'}, ∀ z ∈ span R {u, v} ⊔ ⊥, bil Q w z = 0 := by
      intro w hw z hz
      rw [sup_bot_eq] at hz
      rw [hpair] at hw
      exact hJ'C.orth w hw z hz
    have hJ1 := CoreTwo.isBlockBase_cons Q hC1 hQx'0 hyx horth
    have hset' : span R {y', x'} ⊔ (span R {u, v} ⊔ ⊥) = Ks' 0 := by
      rw [sup_bot_eq, hpair]; exact hJ'C.sup_eq
    rw [hset'] at hJ1
    exact CoreTwo.exists_lagrangian_of_blockBase Q hJ1
  · exfalso
    have hC' := Resplit.cond93_resplit Q hHil h2p hQ hLs.1 hKs.1 hKs'J hS hC
    have hn0 : normIdeal Q (Ls 0) = 1 := (haL 0).symm.trans ha0
    have hn1L : normIdeal Q (Ls 1) = R ∙ (4 : F) := (haL 1).symm.trans ha1
    have hlt := hlt_four Q h2 hLfg hLreg hLs.1 hsc hn0 hn1L ha0
    have hrep := (hC' 0 1 (by simp)).2.2 hlt
    rw [jordanChain_zero Ls 0 rfl, jordanChain_zero Ks' 0 rfl] at hrep
    obtain ⟨r, hr, hru⟩ : ∃ r : R, algebraMap R F r = a 0 ∧ IsUnit r := by
      have h1 : a 0 ∈ (1 : Submodule R F) := by rw [← ha0]; exact mem_span_singleton_self _
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp h1
      have h2' : (1 : F) ∈ R ∙ a 0 := by rw [ha0]; exact ⟨1, by simp⟩
      obtain ⟨s', hs'⟩ := mem_span_singleton.mp h2'
      refine ⟨r, hr, isUnit_iff_exists_inv.mpr ⟨s', ?_⟩⟩
      apply IsFractionRing.injective R F
      rw [map_mul, map_one, hr, mul_comm, ← Algebra.smul_def]; exact hs'
    have hL0fg : (Ls 0).FG := FG.of_le hLfg (hLle 0)
    have hL0reg : IsRegular Q (Ls 0) := (hLs.1.modular 0).isRegular Q hL0fg
    obtain ⟨T, hT0, hTL, hrk⟩ := hT 0
    have hspan : ∀ k ∈ span F ((Ks' 0 : Submodule R V) : Set V),
        ∃ p q s' r' : F, k = p • x' + q • y' + s' • u + r' • v := by
      have hsup : span F ((Ks' 0 : Submodule R V) : Set V) ≤
          span F {x', y'} ⊔ span F {u, v} := by
        refine span_le.mpr fun z hz => ?_
        rw [← hJ'C.sup_eq] at hz
        obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup.mp hz
        exact add_mem (mem_sup_left (Submodule.span_le_restrictScalars R F _ hp))
          (mem_sup_right (Submodule.span_le_restrictScalars R F _ hq))
      intro k hk
      obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup.mp (hsup hk)
      obtain ⟨a₁, b₁, rfl⟩ := Submodule.mem_span_pair.mp hp
      obtain ⟨c₁, d₁, rfl⟩ := Submodule.mem_span_pair.mp hq
      exact ⟨a₁, b₁, c₁, d₁, by abel⟩
    have hxu' := hJ'C.orth x' (subset_span (by simp)) u (subset_span (by simp))
    have hxv' := hJ'C.orth x' (subset_span (by simp)) v (subset_span (by simp))
    have hyu' := hJ'C.orth y' (subset_span (by simp)) u (subset_span (by simp))
    have hyv' := hJ'C.orth y' (subset_span (by simp)) v (subset_span (by simp))
    refine no_rep_aniso Q h2 hL0fg hL0reg hK'0reg hx'K hy'K hQx'0 hx'y' hQu huv ?_ hxu' hxv' hyu' hyv' hspan hno
      hru T hT0 hTL (hd 0) hrk ?_
    · rw [hQv, hδρ, map_mul, map_ofNat]
    · rw [hr]; exact hrep

end Finish

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

open QuadFormsKB.OMeara Suff28 CoreHyp NecBlock Merge28 SuffGood Sat93 Uni93

/-- **The core of 93:28 over a 2-adic field, case $\mathfrak n_1 = \mathfrak o$, $\mathfrak n_2 = 4\mathfrak o$** (O'Meara
1963, §93G, proof of 93:29, sufficiency, p. 278), proved: $dL_1 = 1$ ($L_1 \cong$ a lattice with a block base
$A(c,0) \perp A(c',0)$); by (i) ($\mathfrak f_1 = 4\mathfrak o$) $dK_1 = \varepsilon^{-2}(1 + \alpha)$, $\alpha \in 4\mathfrak o$,
$\mathfrak d(1+\alpha) = \alpha\mathfrak o$; by 93:18 (iii) (weight generator $2$) $K_1 \cong A(1, -\alpha) \perp A(2, 0)$ or
$A(1, -(\alpha - 4\rho)) \perp A(2, 2\rho)$; the first block is moved to $A(1, 0)$ by 93:19 and in the second case (iii) at
the first index contradicts the hyperbolicity of $FL_1$ (`finish`). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₁ = o, n₂ = 4o, proved)"]
theorem twoAdicCoreRest4 (hHil : PadicClass.LocalHilbertField F) : CoreTwoMain.TwoAdicCoreRest4.{u, v} R F := by
  refine ⟨fun h2 {V} _ _ _ _ _ Q h2p hQ L K _ _ m Ls Ks a hLs hKs hd hT hsc hS hC ha0 ha1 => ?_⟩
  classical
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hKreg : IsRegular Q K := isRegular_of_lattice_max Q hQ ‹K.IsLattice F›
  have hLreg : IsRegular Q L := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
  have hKle : ∀ k, Ks k ≤ K := fun k => hKs.1.split.iSup_eq ▸ le_iSup Ks k
  have hLle : ∀ k, Ls k ≤ L := fun k => hLs.1.split.iSup_eq ▸ le_iSup Ls k
  obtain ⟨⟨h0, hTy⟩, -, -⟩ := id hS
  have hc0 : ∀ k : Fin (m + 2), Fin.cast h0 k = k := fun k => Fin.ext rfl
  have hs0K : scale Q (Ks 0) = 1 := by
    have := (hTy 0).2.1; rw [hc0] at this; rw [← this]; exact hsc
  have hrk4K : ∀ k, finrank R (Ks k) = 4 := fun k => by
    have := (hTy k).1; rw [hc0] at this; rw [← this]; exact hd k
  have haK : ∀ i, R ∙ a i = normIdeal Q (Ks i) := fun i => by
    rw [(hS.2.2 i).2, ← fundNormIdeal_eq_normIdeal_twoAdic Q h2 hKfg hKs.1 i]; rfl
  have haL : ∀ i, R ∙ a i = normIdeal Q (Ls i) := fun i => by
    rw [(hS.2.1 i).2, ← fundNormIdeal_eq_normIdeal_twoAdic Q h2 hLfg hLs.1 i]; rfl
  have hK0fg : (Ks 0).FG := FG.of_le hKfg (hKle 0)
  have hK0reg : IsRegular Q (Ks 0) := (hKs.1.modular 0).isRegular Q hK0fg
  have hK0U : IsUnimodular Q (Ks 0) := by have := hKs.1.modular 0; rwa [hs0K] at this
  have hL0fg : (Ls 0).FG := FG.of_le hLfg (hLle 0)
  have hL0reg : IsRegular Q (Ls 0) := (hLs.1.modular 0).isRegular Q hL0fg
  have hLU : IsUnimodular Q (Ls 0) := by have := hLs.1.modular 0; rwa [hsc] at this
  have hn0 : normIdeal Q (Ls 0) = 1 := (haL 0).symm.trans ha0
  have hn1L : normIdeal Q (Ls 1) = R ∙ (4 : F) := (haL 1).symm.trans ha1
  have hf4 := fIdeal_four Q h2 hLfg hLreg hLs.1 hsc hn0 hn1L
  -- `L₁` has a block base: `dL₁ = 1`
  obtain ⟨T, hTiso, hTL, hTdim⟩ := hT 0
  obtain ⟨B, hMB, hBM, hBfg, hBU, hgB, hrB, mB, xB, hxB⟩ :=
    exists_unimodular_blocks Q hL0fg hL0reg hsc hTiso hTL hTdim
  have hmB : mB = 2 := by
    have := finrank_of_blockBase Q hxB
    have := hd 0
    omega
  subst hmB
  have hspanB : span F (B : Set V) = span F (Ls 0 : Set V) :=
    le_antisymm (span_le.mpr fun b hb => hBM b hb) (span_mono hMB)
  have hiso : IsometricLat Q Q (Ls 0) B :=
    isometricLat_of_normGroup_eq_of_span Q hL0fg hBfg hspanB hLU hBU hgB.symm
  obtain ⟨bB, hbB⟩ := exists_basis_det_one_of_blockBase Q hxB
  -- condition (i)
  have h1 := (hC 0 1 (by simp)).1
  rw [jordanChain_zero Ls 0 rfl, jordanChain_zero Ks 0 rfl, hf4] at h1
  have h1B := Transfer28.discQuot_of_isometricLat Q Q hiso ⟨LinearEquiv.refl R _, fun x => rfl⟩ h1
  obtain ⟨bK0⟩ := exists_basis (R := R) (F := F) hK0fg
  let bK : Basis (Fin 4) R (Ks 0) := bK0.reindex (finCongr (hrk4K 0))
  have hdK := Transfer28.det_gram_ne_zero_of_isRegular Q hK0reg bK
  have hsq := Transfer28.discQuot_bases Q h1B bB bK hdK
  rw [hbB] at hsq
  obtain ⟨⟨w, hw, hwe⟩, ε, hε, hmem⟩ := hsq
  rw [mul_one] at hwe
  have hdKw : (gram Q fun i => (bK i : V)).det = (algebraMap R F w)⁻¹ := by
    rw [← hwe, one_div, inv_inv]
  obtain ⟨c, hc⟩ := mem_span_singleton.mp hmem
  have hwe' : w = ε ^ 2 + 4 * c := by
    apply IsFractionRing.injective R F
    rw [map_add, map_pow, map_mul, map_ofNat, ← hwe]
    have : (1 : F) / (gram Q fun i => (bK i : V)).det = 1 / (gram Q fun i => (bK i : V)).det - 1 * algebraMap R F ε ^ 2 +
        algebraMap R F ε ^ 2 := by ring
    rw [this, ← hc, Algebra.smul_def]; ring
  obtain ⟨α, ⟨c', hc'⟩, ⟨b', hb'⟩, hdef⟩ := exists_alpha Q h2 bK hw hε hwe' hdKw
  -- 93:18 (iii)
  have hπ := twoAdic_irreducible h2
  have h2R : (2 : R) ≠ 0 := hπ.ne_zero
  have hn0K : normIdeal Q (Ks 0) = 1 := (haK 0).symm.trans ha0
  have hne0 : Ks 0 ≠ ⊥ := CoreTwo.ne_bot_of_isModular (R := R) Q (hKs.1.modular 0)
  have hset := normGroup_eq_normIdeal_twoAdic Q h2 hK0fg hK0reg hne0
  have hnorm : IsNormGenerator Q (Ks 0) (1 : F) := by
    refine ⟨?_, ?_⟩
    · rw [← SetLike.mem_coe, hset, hn0K]; exact ⟨1, by simp⟩
    · rw [hn0K, Submodule.one_eq_span]
  have hweight : IsWeightGenerator Q (Ks 0) (2 : F) := by
    unfold IsWeightGenerator
    rw [weight_eq_two_smul_scale_twoAdic Q h2 hK0fg hK0reg hne0, hs0K, Submodule.one_eq_span,
      FIdealAux.smul_span_singleton, mul_one]
  have hodd : Odd (dord hπ (1 : F) + dord hπ (2 : F)) := by
    have h1' : dord hπ (1 : F) = 0 := by simpa using dord_unit (F := F) hπ (u := (1 : R)) isUnit_one
    rw [h1', twoAdic_dord_two h2]; exact ⟨0, by norm_num⟩
  obtain ⟨ρ, -, hρ⟩ := G93.exists_delta (F := F) h2R h2p hπ
  obtain ⟨-, hX⟩ := D18.omeara93_18_iii_sub Q hHil h2p hπ hK0fg hK0U (hrk4K 0) hnorm hweight hodd ⟨b', hb'⟩ hdef hρ
  rcases hX with ⟨⟨e, he⟩, -⟩ | ⟨⟨e, he⟩, -⟩
  · refine finish hHil h2 Q h2p hQ L K m Ls Ks a hLs hKs hd hT hsc hS hC ha0 ha1 e (ε := -α) (δ := 0)
      ⟨-c', by rw [hc']; ring⟩ ?_ (Or.inl rfl)
    rw [he, map_neg, map_zero, div_one]
  · refine finish hHil h2 Q h2p hQ L K m Ls Ks a hLs hKs hd hT hsc hS hC ha0 ha1 e (ε := -(α - 4 * ρ)) (δ := 2 * ρ)
      ⟨ρ - c', by rw [hc']; ring⟩ ?_ (Or.inr ⟨ρ, rfl, no_root_of_defect h2 hρ⟩)
    rw [he]
    have h2F : (2 : F) ≠ 0 := two_ne_zero' F
    simp only [map_neg, map_sub, map_mul, map_ofNat, div_one]
    congr 2
    field_simp
    ring

end Main

section Final

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]

/-- **Theorem 93:28 over a 2-adic field, with no named input beyond the Hilbert symbol axioms** (O'Meara 1963, §93F,
pp. 267–276; 2 prime): `CoreTwoMain.dyadicClassification_twoAdic` with `TwoAdicCoreRest4` proved
(`twoAdicCoreRest4`). -/
@[kb "omeara1963" "§93F, 93:28, pp. 267–276 (2-adic field, unconditional)"]
theorem dyadicClassification_twoAdic_unconditional (Q : QuadraticForm F V) (h2 : IsTwoAdic R)
    (hHil : ∀ [CharZero F], PadicClass.LocalHilbertField F) : DyadicClassification R Q :=
  CoreTwoMain.dyadicClassification_twoAdic Q h2 hHil (fun [CharZero F] => twoAdicCoreRest4 hHil)

end Final

section NumberField

open NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type v} [AddCommGroup V] [Module (v.adicCompletion F) V] [FiniteDimensional (v.adicCompletion F) V]
  [Module (v.adicCompletionIntegers F) V] [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) V]

/-- **Theorem 93:28 over a 2-adic completion of a number field, unconditionally** (O'Meara 1963, §93F, pp. 267–276):
at a place $\mathfrak p$ over $2$ with $2$ prime in $F_\mathfrak p$ (e.g. $\mathbb Q_2$), a quadratic space $(V, Q)$
over $F_\mathfrak p$ and lattices $L$, $K$ with Jordan splittings of the same fundamental invariants satisfy
$\operatorname{cls} L = \operatorname{cls} K$ if and only if conditions (i)–(iii) hold. No named statement is assumed (the
Hilbert symbol axioms are proved for completions of number fields). -/
@[kb "omeara1963" "§93F, 93:28, pp. 267–276 (2-adic completion of a number field, unconditional)"]
theorem dyadicClassification_twoAdic_unconditional_nf (h2 : IsTwoAdic (v.adicCompletionIntegers F))
    (Q : QuadraticForm (v.adicCompletion F) V) :
    DyadicClassification (v.adicCompletionIntegers F) Q :=
  CoreTwoMain.dyadicClassification_twoAdic_nf v h2 (twoAdicCoreRest4 (HasseIsoNF.localHilbertField_adicCompletion v)) Q

end NumberField

end QuadFormsKB.OMeara.CoreTwoLast
