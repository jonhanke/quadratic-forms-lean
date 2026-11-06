/-
# O'Meara §93D, Example 93:18 (vi): quaternary unimodular lattices with $dL = 1$

**Setting** (as in `Sec93D18Q.lean`): $R$ a Henselian discrete valuation ring with finite residue field, fraction
field $F$ of characteristic $0$ satisfying the Hilbert-symbol axioms `PadicClass.LocalHilbertField`, $F$ dyadic.
$L \cong A(\alpha, \beta) \perp A(\gamma, \delta)$ is `HasBlk Q L α β γ δ`.

**Page image read** (O'Meara 1973 printing, pp. 261–262): "(vi) As a special example let us consider the case
$\dim L = 4$ with $dL = 1$. Then $FL$ is isotropic if $\operatorname{ord}_{\mathfrak p} a +
\operatorname{ord}_{\mathfrak p} b$ is even, and we actually have $L \cong \langle A(a,0)\rangle \perp
\langle A(0,0)\rangle$ by (ii) and Example 93:9. If $\operatorname{ord}_{\mathfrak p} a +
\operatorname{ord}_{\mathfrak p} b$ is odd, then $L \cong \langle A(a,0)\rangle \perp \langle A(b,0)\rangle$ or
$L \cong \langle A(a, 4a^{-1}\rho)\rangle \perp \langle A(b, 4b^{-1}\rho)\rangle$. The first of these is clearly
isotropic, and the second is not by Example 63:15 (i). So we have the following result: if $\dim L = 4$ and $dL = 1$,
then $L \cong \langle A(a, 4a^{-1}\lambda)\rangle \perp \langle A(b, 4b^{-1}\lambda)\rangle$ with $\lambda = 0$ when
$FL$ is isotropic (in particular when $\operatorname{ord}_{\mathfrak p} a + \operatorname{ord}_{\mathfrak p} b$ is
even) and with $\lambda = \rho$ when $FL$ is not isotropic."

**Proves**
* `isotropic_of_hasBlk_zero`: $A(\alpha, 0) \perp \cdots$ is isotropic;
* `not_isotropic_of_hasBlk_rho` (63:15 (i) as used here): $A(a, 4a^{-1}\rho) \perp A(b, 4b^{-1}\rho)$ is anisotropic
  when $\operatorname{ord} a + \operatorname{ord} b$ is odd;
* `omeara93_18_vi_even`: the even case ($FL$ isotropic, $L \cong A(a,0) \perp A(b,0)$ and
  $L \cong A(a,0) \perp A(0,0)$);
* `omeara93_18_vi_odd`: the odd case (exactly one of the two forms, the first isotropic, the second not);
* `omeara93_18_vi` (**93:18 (vi)**): the unified statement with $\lambda \in \{0, \rho\}$.
-/
import QuadFormsKB.Literature.OMeara.Sec93D18Q

open QuadraticMap Submodule Module IsLocalRing QuadFormsKB.PadicClass
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.D18

section Hasse

variable {F : Type*} [Field F] [CharZero F]

/-- The Hasse symbol of $\langle p, -p, q, -qs^2\rangle$ (an orthogonal sum of two hyperbolic planes) is
$(-1,-1)$, independently of $p, q, s$. -/
theorem hasse_hyp_hyp (hK : LocalHilbertField F) {p q s : F} (hp : p ≠ 0) (hq : q ≠ 0) (hs : s ≠ 0) :
    hasseS F ![p, -p, q, -(q * s ^ 2)] = hilbertSymbol F (-1) (-1) := by
  have hw : ∀ i, (![p, -p, q, -(q * s ^ 2)] : Fin 4 → F) i ≠ 0 := by
    intro i; fin_cases i <;> simp [*]
  rw [hasseS_eq_vec_mul hK _ hw, hasseVec_four]
  have hprod : ∏ i, (![p, -p, q, -(q * s ^ 2)] : Fin 4 → F) i = (p * q * s) ^ 2 := by
    simp [Fin.prod_univ_four]; ring
  rw [hprod, hs_sq _ _ (by simp [hp, hq, hs]), mul_one]
  have e4 : -(q * s ^ 2) = s ^ 2 * ((-1) * q) := by ring
  have e2 : -p = (-1) * p := by ring
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, e4, hs_sq_right _ _ _ hs]
  have L1 : ∀ x y z : F, x ≠ 0 → y ≠ 0 → z ≠ 0 →
      hilbertSymbol F (x * y) z = hilbertSymbol F x z * hilbertSymbol F y z := fun x y z hx hy hz =>
    hK.mul_left x y z hx hy hz
  have R1 : ∀ x y z : F, x ≠ 0 → y ≠ 0 → z ≠ 0 →
      hilbertSymbol F x (y * z) = hilbertSymbol F x y * hilbertSymbol F x z := fun x y z hx hy hz =>
    hK.mul_right hx hy hz
  have S1 : ∀ x : F, x ≠ 0 → hilbertSymbol F x x = hilbertSymbol F x (-1) := fun x hx => hK.self hx
  simp (disch := simp [hp, hq]) only [e2, L1, R1, S1]
  simp only [hilbertSymbol_comm F]
  have sq : ∀ x y : F, hilbertSymbol F x y ^ 2 = 1 := fun x y => by
    rcases hs_pm x y with h | h <;> simp [h]
  have s1 := sq p (-1)
  have s2 := sq q (-1)
  have s3 := sq (-1) (-1)
  have s4 := sq p q
  grind

end Hasse

section NormGroupEven

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **The norm group of $A(a, q) \perp A(b, s)$, even case**: as `normGroup_eq_of_blk2`, with the parity hypothesis
replaced by $b \in 2\mathfrak o$ (in the even case $b\mathfrak o = 2\mathfrak o$, `weight_gen_eq_of_even`). -/
theorem normGroup_eq_of_blk2_two (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V}
    (hfg : L.FG) (hU : IsUnimodular Q L) {a b : F} (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b)
    (hb2 : b ∈ R ∙ (2 : F)) {e : Fin 4 → V} {q s : F} (hq : q ∈ R ∙ b) (hs : s ∈ R ∙ b)
    (hgram : gram Q e = blk2 a q b s) (hMU : IsUnimodular Q (span R (Set.range e))) :
    normGroup Q L = normGroup Q (span R (Set.range e)) := by
  set M := span R (Set.range e) with hM
  have hne := Uni93.ne_bot_of_isUnimodular Q hU
  have hreg : IsRegular Q L := IsModular.isRegular Q hU hfg
  have hset := normGroup_eq_sq_add Q h2p hreg hne ha hb
  have h1L : (1 : F) ∈ scale Q L := by rw [hU.2.1]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have h2b : (2 : F) ∈ R ∙ b := two_smul_scale_le_weight_gen Q hb (by simpa using smul_mem_pointwise_smul (1 : F) (2 : F) _ h1L)
  obtain ⟨t, ht⟩ := mem_span_singleton.mp h2b
  obtain ⟨u, hu⟩ := mem_span_singleton.mp (weight_gen_le_norm_gen Q ha hb (mem_span_singleton_self b))
  obtain ⟨q', hq'⟩ := mem_span_singleton.mp hq
  obtain ⟨s', hs'⟩ := mem_span_singleton.mp hs
  obtain ⟨m, hm⟩ := mem_span_singleton.mp hb2
  rw [Algebra.smul_def] at ht hu hq' hs' hm
  have he : ∀ i, e i ∈ M := fun i => subset_span ⟨i, rfl⟩
  have hQe : ∀ i j, bil Q (e i) (e j) = blk2 a q b s i j := fun i j => by
    simpa [gram] using congrFun (congrFun hgram i) j
  have hQa : Q (e 0) = a := by rw [← bil_self, hQe]; simp [blk2]
  have hval : ∀ c : Fin 4 → R, Q (∑ i, algebraMap R F (c i) • e i) = a * algebraMap R F (c 0) ^ 2 +
      b * algebraMap R F (t * c 0 * c 1 + q' * c 1 ^ 2 + c 2 ^ 2 + t * c 2 * c 3 + s' * c 3 ^ 2) := by
    intro c
    rw [Q_blk2_comb Q hgram, ← ht, ← hq', ← hs']
    simp only [map_add, map_mul, map_pow]
    ring
  apply le_antisymm
  · intro z hz
    have hz' : z ∈ (normGroup Q L : Set F) := hz
    rw [hset] at hz'
    obtain ⟨ε, η, rfl⟩ := hz'
    refine add_mem ?_ ?_
    · have := Q_mem_normGroup Q (M.smul_mem ε (he 0))
      rwa [← algebraMap_smul F ε (e 0), Q_smul, hQa, mul_comm] at this
    · -- `b η = 2 (m η)` with `m η ∈ 𝔬 = 𝔰M`
      refine ⟨0, M.zero_mem, algebraMap R F (m * η), ?_, ?_⟩
      · rw [hMU.2.1]; exact Submodule.mem_one.mpr ⟨_, rfl⟩
      · rw [map_zero, ← hm, map_mul]; ring
  · rintro z ⟨y, hy, c, hc, rfl⟩
    rw [hMU.2.1] at hc
    obtain ⟨c₀, rfl⟩ := Submodule.mem_one.mp hc
    obtain ⟨x, rfl⟩ := exists_coeffs (R := R) (F := F) e hy
    have hz : Q (∑ i, algebraMap R F (x i) • e i) + 2 * algebraMap R F c₀ ∈ (normGroup Q L : Set F) := by
      rw [hset, hval]
      refine ⟨x 0, t * x 0 * x 1 + q' * x 1 ^ 2 + x 2 ^ 2 + t * x 2 * x 3 + s' * x 3 ^ 2 + t * c₀, ?_⟩
      rw [← ht]
      simp only [map_add, map_mul, map_pow]
      ring
    exact hz

end NormGroupEven

section IsoHasse

variable {F : Type*} [Field F] [CharZero F]

/-- **Isotropic quaternary forms of square discriminant**: if $\langle g_0, g_1, g_2, g_3\rangle$ is isotropic with
$g_0 g_1 g_2 g_3$ a square, then its Hasse symbol is $S = (-1,-1)$ (the value for two hyperbolic planes, see
`hasse_hyp_hyp`). Proof: by `isotropic_four_iff_common`, $\langle g_0, g_1\rangle$ and $\langle -g_2, -g_3\rangle$
represent a common $x$, hence $(g_0, g_1) = (-g_2, -g_3)$ since $-g_2 g_3 \equiv -g_0 g_1$ modulo squares. -/
theorem hasse_of_isotropic_sqdisc (hK : LocalHilbertField F) {w : Fin 4 → F} (hw : ∀ i, w i ≠ 0)
    (hd : ∃ t : F, t ≠ 0 ∧ ∏ i, w i = t ^ 2)
    (hiso : ∃ y : Fin 4 → F, y ≠ 0 ∧ ∑ i, w i * y i ^ 2 = 0) :
    hasseS F w = hilbertSymbol F (-1) (-1) := by
  obtain ⟨g₀, g₁, g₂, g₃, rfl⟩ : ∃ g₀ g₁ g₂ g₃ : F, w = ![g₀, g₁, g₂, g₃] :=
    ⟨w 0, w 1, w 2, w 3, by funext i; fin_cases i <;> rfl⟩
  have h₀ : g₀ ≠ 0 := by simpa using hw 0
  have h₁ : g₁ ≠ 0 := by simpa using hw 1
  have h₂ : g₂ ≠ 0 := by simpa using hw 2
  have h₃ : g₃ ≠ 0 := by simpa using hw 3
  obtain ⟨t, ht, hprod'⟩ := hd
  have hprod : g₀ * g₁ * g₂ * g₃ = t ^ 2 := by simpa [Fin.prod_univ_four] using hprod'
  have hI : (QuadFormsKB.QuadForm.diag ![g₀, g₁, g₂, g₃]).IsotropicIn F :=
    (isotropicIn_diag_iff _).mpr hiso
  obtain ⟨x, hx, hr1, hr2⟩ := (isotropic_four_iff_common h₀ h₁ h₂ h₃).mp hI
  have e1 := (represents_two_iff hK h₀ h₁ hx).mp hr1
  have e2 := (represents_two_iff hK (neg_ne_zero.mpr h₂) (neg_ne_zero.mpr h₃) hx).mp hr2
  have h01 : g₀ * g₁ ≠ 0 := mul_ne_zero h₀ h₁
  have hc : t / (g₀ * g₁) ≠ 0 := div_ne_zero ht h01
  have hrel : -(-g₂ * -g₃) = (t / (g₀ * g₁)) ^ 2 * (-(g₀ * g₁)) := by
    rw [div_pow, ← hprod]; field_simp
  rw [hrel, hs_sq_right _ _ _ hc, e1] at e2
  -- e2 : (g₀, g₁) = (-g₂, -g₃)
  have hn1 : (-1 : F) ≠ 0 := by norm_num
  have key : ∀ x y : F, x ≠ 0 → y ≠ 0 →
      hilbertSymbol F (-x) (-y) = hilbertSymbol F (-1) (-1) * hilbertSymbol F (-1) y *
        hilbertSymbol F x (-1) * hilbertSymbol F x y := by
    intro x y hx hy
    have a1 := hK.mul_left (-1) x (-y) hn1 hx (neg_ne_zero.mpr hy)
    have a2 := hK.mul_right hn1 hn1 hy
    have a3 := hK.mul_right hx hn1 hy
    rw [show -x = -1 * x by ring, a1, show -y = -1 * y by ring, a2, a3]
    ring
  have exp : ∀ y : F, y ≠ 0 → hilbertSymbol F (g₀ * g₁ * g₂ * g₃) y =
      hilbertSymbol F g₀ y * hilbertSymbol F g₁ y * hilbertSymbol F g₂ y * hilbertSymbol F g₃ y := by
    intro y hy
    rw [hK.mul_left _ _ _ (mul_ne_zero h01 h₂) h₃ hy, hK.mul_left _ _ _ h01 h₂ hy,
      hK.mul_left _ _ _ h₀ h₁ hy]
  have hone : ∀ y : F, y ≠ 0 → hilbertSymbol F g₀ y * hilbertSymbol F g₁ y * hilbertSymbol F g₂ y *
      hilbertSymbol F g₃ y = 1 := by
    intro y hy
    rw [← exp y hy, hprod]
    have := hs_sq_left 1 y t ht
    rw [mul_one] at this
    rw [this, hs_one_left]
  have R0 := hone g₀ h₀
  have R1 := hone g₁ h₁
  have R2 := hone g₂ h₂
  have Rm := hone (-1) hn1
  have S0 := hK.self h₀
  have S1 := hK.self h₁
  have S2 := hK.self h₂
  have S3 := hK.self h₃
  have K23 := key g₂ g₃ h₂ h₃
  rw [hilbertSymbol_comm F (-1) g₃] at K23
  have c10 := hilbertSymbol_comm F g₁ g₀
  have c20 := hilbertSymbol_comm F g₂ g₀
  have c30 := hilbertSymbol_comm F g₃ g₀
  have c21 := hilbertSymbol_comm F g₂ g₁
  have c31 := hilbertSymbol_comm F g₃ g₁
  have c32 := hilbertSymbol_comm F g₃ g₂
  have hwne : ∀ i, (![g₀, g₁, g₂, g₃] : Fin 4 → F) i ≠ 0 := hw
  rw [hasseS_eq_vec_mul hK _ hwne, hasseVec_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  have hp : ∏ i, (![g₀, g₁, g₂, g₃] : Fin 4 → F) i = t ^ 2 := hprod'
  rw [hp, hs_sq _ _ ht, mul_one]
  have sq : ∀ x y : F, hilbertSymbol F x y ^ 2 = 1 := fun x y => by
    rcases hs_pm x y with h | h <;> simp [h]
  have q1 := sq g₀ (-1)
  have q2 := sq g₁ (-1)
  have q3 := sq g₂ (-1)
  have q4 := sq g₃ (-1)
  have q5 := sq g₀ g₁
  have q6 := sq g₀ g₂
  have q7 := sq g₀ g₃
  have q8 := sq g₁ g₂
  have q9 := sq g₁ g₃
  have q10 := sq g₂ g₃
  have q11 := sq (-1) (-1)
  grind

end IsoHasse

section IsoSpace

variable {F : Type*} [Field F] [CharZero F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- **Isotropy in an orthogonal base**: if $(V, Q)$ has an orthogonal base with weights $w_i$, then $V$ has a nonzero
vector with $Q(v) = 0$ iff $\sum w_i y_i^2 = 0$ has a nonzero solution $y \in F^n$. -/
theorem isotropic_iff_of_rep {n : ℕ} {w : Fin n → F} (h : Rep Q (Matrix.diagonal w)) :
    (∃ v : V, v ≠ 0 ∧ Q v = 0) ↔ ∃ y : Fin n → F, y ≠ 0 ∧ ∑ i, w i * y i ^ 2 = 0 := by
  obtain ⟨e, he⟩ := h
  constructor
  · rintro ⟨v, hv0, hQ⟩
    refine ⟨fun i => e.repr v i, fun h0 => hv0 ?_, ?_⟩
    · have : e.repr v = 0 := Finsupp.ext fun i => congrFun h0 i
      exact (e.repr.map_eq_zero_iff).mp this
    · have := Q_sum_gram Q (fun i => (e i)) (fun i => e.repr v i)
      rw [he, dot_diag, e.sum_repr] at this
      rw [← this, hQ]
  · rintro ⟨y, hy0, hy⟩
    refine ⟨e.equivFun.symm y, fun h0 => hy0 ?_, ?_⟩
    · exact e.equivFun.symm.map_eq_zero_iff.mp h0 |>.symm ▸ rfl
    · have := Q_sum_gram Q (fun i => (e i)) y
      rw [he, dot_diag] at this
      rw [Basis.equivFun_symm_apply, this, hy]

end IsoSpace

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **$\Delta = 1 + 4\rho$ and $1 - 4\rho$**: for $\rho \in \mathfrak o$ in a dyadic local field, $1 + 4\rho$ is a unit,
$1 - 4\rho \neq 0$, and $1 - 4\rho = c^2 (1 + 4\rho)$ for some $c \neq 0$ (Local Square Theorem applied to
$(1 + 4\rho)(1 - 4\rho) = 1 - 16\rho^2 = 1 + 4(-4\rho^2)$). -/
theorem one_sub_four_rho (h2p : ¬ IsUnit (2 : R)) (ρ : R) :
    IsUnit (1 + 4 * ρ) ∧ (1 : F) - 4 * algebraMap R F ρ ≠ 0 ∧
      ∃ c : F, c ≠ 0 ∧ (1 : F) - 4 * algebraMap R F ρ = c ^ 2 * algebraMap R F (1 + 4 * ρ) := by
  have h2m : (2 : R) ∈ maximalIdeal R := Uni93.two_mem_maximalIdeal h2p
  have h4m : 4 * ρ ∈ maximalIdeal R := by
    rw [show (4 : R) * ρ = 2 * (2 * ρ) by ring]; exact Ideal.mul_mem_right _ _ h2m
  have hinj := IsFractionRing.injective R F
  have algne : ∀ {u : R}, IsUnit u → algebraMap R F u ≠ 0 := fun hu h =>
    hu.ne_zero (hinj (by rw [h, map_zero]))
  have heu : IsUnit (1 + -(4 * ρ)) := isUnit_one_add_aux (neg_mem h4m)
  have hΔu : IsUnit (1 + 4 * ρ) := isUnit_one_add_aux h4m
  have he0 : (1 : F) - 4 * algebraMap R F ρ ≠ 0 := by
    have := algne heu
    simp only [map_add, map_one, map_neg, map_mul, map_ofNat] at this
    convert this using 1; ring
  have hρρ : -(4 * ρ * ρ) ∈ maximalIdeal R := neg_mem (Ideal.mul_mem_right ρ _ h4m)
  obtain ⟨τ, hτ⟩ := isSquare_one_add_four_mul hρρ
  have hτu : IsUnit (τ * τ) := hτ ▸ isUnit_one_add_aux (Ideal.mul_mem_left _ _ hρρ)
  have hτ0 : algebraMap R F τ ≠ 0 := fun h => algne hτu (by rw [map_mul, h, zero_mul])
  have hΔ0 : algebraMap R F (1 + 4 * ρ) ≠ 0 := algne hΔu
  refine ⟨hΔu, he0, algebraMap R F τ / algebraMap R F (1 + 4 * ρ), div_ne_zero hτ0 hΔ0, ?_⟩
  have := congrArg (algebraMap R F) hτ
  simp only [map_mul, map_add, map_neg, map_one, map_ofNat] at this
  field_simp
  simp only [map_add, map_mul, map_one, map_ofNat] at hΔ0 ⊢
  linear_combination this

/-- **A lattice $A(\alpha, 0) \perp A(\gamma, \delta)$ is isotropic**: its second basis vector $y_1$ has
$Q(y_1) = 0$ and $y_1 \neq 0$ (clear from the matrix, O'Meara 93:18 (vi), "the first of these is clearly isotropic"). -/
theorem isotropic_of_hasBlk_zero {L : Submodule R V} {α γ δ : F} (h : HasBlk Q L α 0 γ δ) :
    ∃ v : V, v ≠ 0 ∧ Q v = 0 := by
  obtain ⟨e, he⟩ := h
  refine ⟨(e 1 : V), fun h0 => e.ne_zero 1 (Subtype.ext h0), ?_⟩
  have := congrFun (congrFun he 1) 1
  simpa [gram, blk2, bil_self] using this

/-- **63:15 (i) as used in 93:18 (vi)**: if $\operatorname{ord} a + \operatorname{ord} b$ is odd and
$\Delta = 1 + 4\rho$ has quadratic defect $4\mathfrak o$, then no quadratic space containing a lattice
$L \cong A(a, 4a^{-1}\rho) \perp A(b, 4b^{-1}\rho)$ as a base of a $4$-dimensional space $V$ is isotropic.

Proof: $V \cong \langle a, -ae, b, -be\rangle$ with $e = 1 - 4\rho \equiv \Delta$ modulo squares (`dw2`,
`one_sub_four_rho`). An isotropic vector gives, by `isotropic_four_iff_common` and `represents_two_iff`, an $x$ with
$(x, e) = (a, e) = (-b, e)$, hence $(-ab, e) = 1$; but $(-ab, \Delta) = (-1)^{\operatorname{ord}(ab)} = -1$
(`hilbert_delta_parity`). -/
theorem not_isotropic_of_hasBlk_rho (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {π : R}
    (hπ : Irreducible π) (hV : finrank F V = 4) {L : Submodule R V} {a b : F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hodd : Odd (dord hπ a + dord hπ b)) {ρ : R}
    (hρ : quadDefect R (algebraMap R F (1 + 4 * ρ)) = span R {(4 : F)})
    (h : HasBlk Q L a (4 * algebraMap R F ρ / a) b (4 * algebraMap R F ρ / b)) :
    ¬ ∃ v : V, v ≠ 0 ∧ Q v = 0 := by
  rintro hiso
  obtain ⟨hΔu, he0, c, hc0, hec⟩ := one_sub_four_rho (F := F) h2p ρ
  have h2R : (2 : R) ≠ 0 := fun h => two_ne_zero (α := F) (by
    rw [← map_ofNat (algebraMap R F) 2, h, map_zero])
  set e : F := 1 - 4 * algebraMap R F ρ with he
  have h1 : a * (4 * algebraMap R F ρ / a) - 1 = -e := by
    rw [he]; field_simp; ring
  have h2 : b * (4 * algebraMap R F ρ / b) - 1 = -e := by
    rw [he]; field_simp; ring
  have hdet : (a * (4 * algebraMap R F ρ / a) - 1) * (b * (4 * algebraMap R F ρ / b) - 1) ≠ 0 := by
    rw [h1, h2]; exact mul_ne_zero (neg_ne_zero.mpr he0) (neg_ne_zero.mpr he0)
  have hR := (rep_blk2_iff Q ha0 hb0 _ _).mp (rep_of_hasBlk Q hV h hdet)
  have hwe : dw2 a (4 * algebraMap R F ρ / a) b (4 * algebraMap R F ρ / b) = ![a, -(a * e), b, -(b * e)] := by
    funext i; fin_cases i
    · rfl
    · show a * (a * (4 * algebraMap R F ρ / a) - 1) = -(a * e)
      rw [h1]; ring
    · rfl
    · show b * (b * (4 * algebraMap R F ρ / b) - 1) = -(b * e)
      rw [h2]; ring
  rw [hwe] at hR
  obtain ⟨y, hy0, hy⟩ := (isotropic_iff_of_rep Q hR).mp hiso
  have hI : (QuadFormsKB.QuadForm.diag ![a, -(a * e), b, -(b * e)]).IsotropicIn F :=
    (isotropicIn_diag_iff _).mpr ⟨y, hy0, hy⟩
  have h₁ : -(a * e) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero ha0 he0)
  have h₃ : -(b * e) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hb0 he0)
  obtain ⟨x, hx, hr1, hr2⟩ := (isotropic_four_iff_common ha0 h₁ hb0 h₃).mp hI
  have e1 := (represents_two_iff hK ha0 h₁ hx).mp hr1
  have e2 := (represents_two_iff hK (neg_ne_zero.mpr hb0) (neg_ne_zero.mpr h₃) hx).mp hr2
  rw [show -(a * -(a * e)) = a ^ 2 * e by ring, hs_sq_right _ _ _ ha0,
    show -(a * e) = (-a) * e by ring, hK.mul_right ha0 (neg_ne_zero.mpr ha0) he0,
    hilbertSymbol_self_neg, one_mul] at e1
  rw [show -(-b * -(-(b * e))) = b ^ 2 * e by ring, hs_sq_right _ _ _ hb0, neg_neg,
    hK.mul_right (neg_ne_zero.mpr hb0) hb0 he0, hilbertSymbol_comm F (-b) b,
    hilbertSymbol_self_neg, one_mul] at e2
  have hab : hilbertSymbol F (-(a * b)) e = 1 := by
    rw [show -(a * b) = a * (-b) by ring, hK.mul_left _ _ _ ha0 (neg_ne_zero.mpr hb0) he0, ← e1, ← e2]
    rcases hs_pm x e with h | h <;> rw [h] <;> norm_num
  rw [hec, hs_sq_right _ _ _ hc0,
    hilbert_delta_parity hK h2R hΔu hρ hπ (neg_ne_zero.mpr (mul_ne_zero ha0 hb0)),
    dord_neg hπ (mul_ne_zero ha0 hb0), dord_mul hπ ha0 hb0,
    if_neg (Int.not_even_iff_odd.mpr hodd)] at hab
  norm_num at hab

/-- **93:18 (vi), odd case** (O'Meara 1963, §93D, p. 261): let $L$ be a quaternary unimodular lattice with
$dL = 1$ on a $4$-dimensional space $V$ over a dyadic local field, $a$ a norm generator and $b$ a weight generator
with $\operatorname{ord}_{\mathfrak p} a + \operatorname{ord}_{\mathfrak p} b$ odd, and $\Delta = 1 + 4\rho$ the unit of
quadratic defect $4\mathfrak o$. Then $L \cong A(a, 0) \perp A(b, 0)$ or
$L \cong A(a, 4a^{-1}\rho) \perp A(b, 4b^{-1}\rho)$, but not both; and the first alternative holds exactly when $V$
is isotropic.

*Form of the statement.* "$dL = 1$" is the existence of a base of $L$ with Gram determinant $1$ (i.e. $dL \cong 1$
modulo $\mathfrak u^2$). "$L \cong A(\alpha,\beta) \perp A(\gamma,\delta)$" is `HasBlk Q L α β γ δ`. "$FL$ is
isotropic" is `∃ v : V, v ≠ 0 ∧ Q v = 0` (here $FL = V$ because $L$ has rank $4 = \dim V$).

*Proof.* By 93:18 (iii) with $\alpha = 0$ (then $-(0 - 4\rho)a^{-1} = 4\rho a^{-1}$ and $\mathfrak d(1) = 0$); the
first form is isotropic (`isotropic_of_hasBlk_zero`), the second is not (`not_isotropic_of_hasBlk_rho`). -/
@[kb "omeara1963" "§93D, 93:18 (vi), pp. 261–262 (odd case)"]
theorem omeara93_18_vi_odd (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π)
    (hV : finrank F V = 4) {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L)
    (hrk : finrank R L = 4) {a b : F} (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b)
    (hodd : Odd (dord hπ a + dord hπ b))
    (hd : ∃ e : Basis (Fin 4) R L, (gram Q fun i => (e i : V)).det = 1) {ρ : R}
    (hρ : quadDefect R (algebraMap R F (1 + 4 * ρ)) = span R {(4 : F)}) :
    Xor' (HasBlk Q L a 0 b 0)
        (HasBlk Q L a (4 * algebraMap R F ρ / a) b (4 * algebraMap R F ρ / b)) ∧
      (HasBlk Q L a 0 b 0 ↔ ∃ v : V, v ≠ 0 ∧ Q v = 0) := by
  have hne := Uni93.ne_bot_of_isUnimodular Q hU
  have hreg : IsRegular Q L := IsModular.isRegular Q hU hfg
  have ha0 := ha.ne_zero Q hreg hne
  have hb0 := weight_gen_ne_zero Q ha ha0 hb
  have hdef : quadDefect R (1 + algebraMap R F 0) = span R {algebraMap R F 0} := by
    rw [map_zero]; exact le_antisymm (quadDefect_one_add_le (R := R) 0) (by simp)
  have h3 := (omeara93_18_iii Q hK h2p hπ hV hfg hU hrk ha hb hodd (α := 0) (by simpa using hd) hdef hρ).2
  have e1 : -(algebraMap R F 0) / a = 0 := by simp
  have e2 : -(algebraMap R F 0 - 4 * algebraMap R F ρ) / a = 4 * algebraMap R F ρ / a := by simp
  rw [e1, e2] at h3
  refine ⟨h3, isotropic_of_hasBlk_zero Q, fun hiso => ?_⟩
  rcases h3 with ⟨hJ, -⟩ | ⟨hK', -⟩
  · exact hJ
  · exact absurd hiso (not_isotropic_of_hasBlk_rho Q hK h2p hπ hV ha0 hb0 hodd hρ hK')

/-- **93:18 (vi), even case** (O'Meara 1963, §93D, p. 261): let $L$ be a quaternary unimodular lattice with $dL = 1$
on a $4$-dimensional space $V$ over a dyadic local field, $a$ a norm generator and $b$ a weight generator with
$\operatorname{ord}_{\mathfrak p} a + \operatorname{ord}_{\mathfrak p} b$ even. Then $V$ is isotropic and
$L \cong A(a, 0) \perp A(0, 0)$ and $L \cong A(a, 0) \perp A(b, 0)$.

*Form of the statement.* As in `omeara93_18_vi_odd`; the second isometry is added because it is the case $\lambda = 0$
of the unified statement `omeara93_18_vi`. (In the even case $b\mathfrak o = 2\mathfrak o$, so $A(b, 0) \cong A(0,0)$
by replacing $x$ with $x - \tfrac b2 y$.)

*Proof* (differs from the book's use of 93:9 only in the last step). 93:18 (ii)
(`exists_hyperbolic_splitting_of_even`) gives a hyperbolic pair $x, y \in L$, so $V$ is isotropic. By 93:15, $L$ has a
base with matrix $A(a_1, \beta_1) \perp A(a_2, \beta_2)$, so $V \cong \langle w_1, \dots, w_4\rangle$ (`dw2`) with
square discriminant (because $dL = 1$) and, being isotropic, Hasse symbol $(-1,-1)$ (`hasse_of_isotropic_sqdisc`).
The form $\langle a, -a, b, -b\rangle$ has the same discriminant class and Hasse symbol (`hasse_hyp_hyp`), hence is
isometric to $V$ (63:20, `rep_diag_iff_S`); then 93:16 applies, with the norm group computed by
`normGroup_eq_of_blk2_two`, to give a base of $L$ with matrix $A(a, 0) \perp A(b, 0)$. -/
@[kb "omeara1963" "§93D, 93:18 (vi), pp. 261–262 (even case)"]
theorem omeara93_18_vi_even (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π)
    (hV : finrank F V = 4) {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L)
    (hrk : finrank R L = 4) {a b : F} (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b)
    (hev : Even (dord hπ a + dord hπ b))
    (hd : ∃ e : Basis (Fin 4) R L, (gram Q fun i => (e i : V)).det = 1) :
    (∃ v : V, v ≠ 0 ∧ Q v = 0) ∧ HasBlk Q L a 0 0 0 ∧ HasBlk Q L a 0 b 0 := by
  have hinj := IsFractionRing.injective R F
  have hne := Uni93.ne_bot_of_isUnimodular Q hU
  have hreg : IsRegular Q L := IsModular.isRegular Q hU hfg
  have ha0 := ha.ne_zero Q hreg hne
  have hb0 := weight_gen_ne_zero Q ha ha0 hb
  -- isotropy from 93:18 (ii)
  obtain ⟨x, y, K, hQx, hQy, hxy, -⟩ :=
    Uni93.exists_hyperbolic_splitting_of_even Q h2p hπ hfg hU (by omega) ha hb hev
  have hiso : ∃ v : V, v ≠ 0 ∧ Q v = 0 := ⟨x, fun h0 => by rw [h0] at hxy; simp [bil] at hxy, hQx⟩
  refine ⟨hiso, ?_⟩
  -- `a`, `b` in `𝔬`, `b = 2 m`
  have hscale : ∀ z ∈ normIdeal Q L, ∃ z₀ : R, algebraMap R F z₀ = z := fun z hz => by
    have := normIdeal_le_scale Q L hz
    rw [hU.2.1] at this
    exact Submodule.mem_one.mp this
  obtain ⟨a₀, ha₀⟩ := hscale a (ha.2 ▸ mem_span_singleton_self a)
  obtain ⟨b₀, hb₀⟩ := hscale b ((weight_bounds Q L).2.2.2 (hb ▸ mem_span_singleton_self b))
  have hbeq := weight_gen_eq_of_even Q h2p hπ hreg hne ha hb hev
  rw [hU.2.1] at hbeq
  have hspan2 : R ∙ b = R ∙ (2 : F) := by
    rw [hbeq, Submodule.one_eq_span, Submodule.smul_span, Set.smul_set_singleton, smul_eq_mul, mul_one]
  have hb2 : b ∈ R ∙ (2 : F) := by rw [← hspan2]; exact mem_span_singleton_self b
  obtain ⟨m, hm⟩ := mem_span_singleton.mp hb2
  rw [Algebra.smul_def] at hm
  -- the space side
  obtain ⟨a₁, β₁, a₂, β₂, ha₁, ha₂, -, -, -, -, hu₁, hu₂, e, he⟩ := exists_blk2_basis Q h2p hfg hU hrk
  obtain ⟨e', he'⟩ := hd
  obtain ⟨ε, hε, hdet⟩ := exists_unit_det_gram Q e e'
  rw [he', he, det_blk2] at hdet
  have hu₁F : algebraMap R F a₁ * algebraMap R F β₁ - 1 ≠ 0 := by
    rw [← map_mul, ← map_one (algebraMap R F), ← map_sub]
    exact fun h => (by simpa [add_comm, sub_eq_add_neg] using hu₁ : IsUnit (a₁ * β₁ - 1)).ne_zero
      (hinj (by rw [h, map_zero]))
  have hu₂F : algebraMap R F a₂ * algebraMap R F β₂ - 1 ≠ 0 := by
    rw [← map_mul, ← map_one (algebraMap R F), ← map_sub]
    exact fun h => (by simpa [add_comm, sub_eq_add_neg] using hu₂ : IsUnit (a₂ * β₂ - 1)).ne_zero
      (hinj (by rw [h, map_zero]))
  have hε0 : algebraMap R F ε ≠ 0 := fun h => hε.ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨eF, heF⟩ := Eng93.basisF_of_lattice Q e (by rw [he, det_blk2]; exact mul_ne_zero hu₁F hu₂F) hV
  have hspan : span F (L : Set V) = ⊤ := Eng93.span_eq_top_of_basis e eF heF
  have hRepL : Rep Q (blk2 (algebraMap R F a₁) (algebraMap R F β₁) (algebraMap R F a₂) (algebraMap R F β₂)) :=
    rep_of_hasBlk Q hV ⟨e, he⟩ (mul_ne_zero hu₁F hu₂F)
  set w := dw2 (algebraMap R F a₁) (algebraMap R F β₁) (algebraMap R F a₂) (algebraMap R F β₂) with hw
  have hRepw : Rep Q (Matrix.diagonal w) := (rep_blk2_iff Q ha₁ ha₂ _ _).mp hRepL
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i; fin_cases i <;> simp [hw, dw2, ha₁, ha₂, hu₁F, hu₂F]
  have hprodw : ∏ i, w i = (algebraMap R F a₁ * algebraMap R F a₂ / algebraMap R F ε) ^ 2 := by
    have h1 : ∏ i, w i = (algebraMap R F a₁ * algebraMap R F a₂) ^ 2 *
        ((algebraMap R F a₁ * algebraMap R F β₁ - 1) * (algebraMap R F a₂ * algebraMap R F β₂ - 1)) := by
      simp [hw, dw2, Fin.prod_univ_four]; ring
    rw [h1, div_pow, eq_div_iff (pow_ne_zero 2 hε0)]
    linear_combination (-(algebraMap R F a₁ * algebraMap R F a₂) ^ 2) * hdet
  have hhasse : hasseS F w = hilbertSymbol F (-1) (-1) :=
    hasse_of_isotropic_sqdisc hK hw0
      ⟨_, div_ne_zero (mul_ne_zero ha₁ ha₂) hε0, hprodw⟩ ((isotropic_iff_of_rep Q hRepw).mp hiso)
  -- the target diagonal form `⟨a, -a, b, -b⟩`
  set w' := dw2 a 0 b 0 with hw'
  have hw'e : w' = ![a, -a, b, -(b * 1 ^ 2)] := by
    funext i; fin_cases i <;> simp [hw', dw2]
  have hw'0 : ∀ i, w' i ≠ 0 := by
    intro i; fin_cases i <;> simp [hw', dw2, ha0, hb0]
  have hhasse' : hasseS F w' = hilbertSymbol F (-1) (-1) := by
    rw [hw'e]; exact hasse_hyp_hyp hK ha0 hb0 one_ne_zero
  have hdisc : ∃ t : F, t ≠ 0 ∧ ∏ i, w' i = t ^ 2 * ∏ i, w i := by
    refine ⟨a * b * algebraMap R F ε / (algebraMap R F a₁ * algebraMap R F a₂), by
      simp [ha0, hb0, hε0, ha₁, ha₂], ?_⟩
    rw [hprodw]
    have : ∏ i, w' i = a ^ 2 * b ^ 2 := by
      simp [hw', dw2, Fin.prod_univ_four]; ring
    rw [this]; field_simp
  have hR' : Rep Q (Matrix.diagonal w') :=
    ((rep_diag_iff_S Q hK hw0 hw'0 hRepw).mpr ⟨hdisc, hhasse.trans hhasse'.symm⟩)
  -- lattice side (93:16)
  obtain ⟨eX, heX⟩ := (rep_blk2_iff Q ha0 hb0 0 0).mpr hR'
  have hG : gram Q (fun i => eX i) = (blk2 a₀ 0 b₀ 0).map (algebraMap R F) := by
    rw [map_blk2, ha₀, map_zero, hb₀]; exact heX
  have hGu : IsUnit (blk2 a₀ 0 b₀ 0).det := by rw [det_blk2]; simp
  obtain ⟨hMU, -, -, -⟩ := Eng93.span_basis_props Q eX hGu hG
  have hg := normGroup_eq_of_blk2_two Q h2p hfg hU ha hb hb2 (zero_mem _) (zero_mem _) heX hMU
  obtain ⟨bL, hbL⟩ := Eng93.exists_basis_gram_of_normGroup_eq Q hfg hU hspan eX hGu hG hg
  have hbL' : gram Q (fun i => (bL i : V)) = blk2 a 0 b 0 := by
    rw [hbL, map_blk2, ha₀, map_zero, hb₀]
  refine ⟨?_, ⟨bL, hbL'⟩⟩
  -- `A(b, 0) ≅ A(0, 0)`: replace `x` by `x - (b/2) y`
  set u : Fin 4 → V := fun i => (bL i : V) with hu
  set τ : F := algebraMap R F m with hτ
  have hbτ : b = τ * 2 := hm.symm
  let v : Fin 4 → V := ![u 0, u 1, u 2 - (m • u 3), u 3]
  have hv : ∀ i, v i ∈ L := by
    intro i; fin_cases i
    · exact (bL 0).2
    · exact (bL 1).2
    · exact L.sub_mem (bL 2).2 (L.smul_mem m (bL 3).2)
    · exact (bL 3).2
  let P : Matrix (Fin 4) (Fin 4) F :=
    Matrix.of ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, -τ], ![0, 0, 0, 1]]
  have hvP : v = fun i => ∑ j, P i j • u j := by
    funext i; fin_cases i <;>
      simp [v, P, Fin.sum_univ_four, sub_eq_add_neg, hτ, algebraMap_smul F m (u 3)]
  have hGv : gram Q v = blk2 a 0 0 0 := by
    rw [hvP, gram_comb, hbL', hbτ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, blk2, Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  have hG2 : gram Q v = (blk2 a₀ 0 0 0).map (algebraMap R F) := by
    rw [map_blk2, ha₀, map_zero]; exact hGv
  have hGu2 : IsUnit (blk2 a₀ 0 0 0).det := by rw [det_blk2]; simp
  obtain ⟨e2, he2⟩ := exists_basis_of_gram_unit Q hfg hU hrk hv hGu2 hG2
  refine ⟨e2, ?_⟩
  have : (fun i => (e2 i : V)) = v := funext he2
  rw [this]; exact hGv

/-- **Example 93:18 (vi)** (O'Meara 1963, §93D, pp. 261–262). Let $L$ be a quaternary unimodular lattice with
$dL = 1$ on a $4$-dimensional space $V$ over a dyadic local field, $a$ a norm generator and $b$ a weight generator of
$L$, and $\Delta = 1 + 4\rho$ the unit of quadratic defect $4\mathfrak o$. Then
$L \cong A(a, 4a^{-1}\lambda) \perp A(b, 4b^{-1}\lambda)$ with $\lambda = 0$ when $FL = V$ is isotropic (in particular
when $\operatorname{ord}_{\mathfrak p} a + \operatorname{ord}_{\mathfrak p} b$ is even) and with $\lambda = \rho$ when
$FL$ is not isotropic.

*Form of the statement.* The case $\lambda = 0$ is written `HasBlk Q L a 0 b 0` (the matrix
$A(a, 4a^{-1}\cdot 0) \perp A(b, 4b^{-1}\cdot 0)$); the other hypotheses and conventions are those of
`omeara93_18_vi_odd`. Only the parity of $\operatorname{ord} a + \operatorname{ord} b$ is split in the proof
(`omeara93_18_vi_even`, `omeara93_18_vi_odd`); it is not a hypothesis. -/
@[kb "omeara1963" "§93D, 93:18 (vi), pp. 261–262"]
theorem omeara93_18_vi (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π)
    (hV : finrank F V = 4) {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L)
    (hrk : finrank R L = 4) {a b : F} (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b)
    (hd : ∃ e : Basis (Fin 4) R L, (gram Q fun i => (e i : V)).det = 1) {ρ : R}
    (hρ : quadDefect R (algebraMap R F (1 + 4 * ρ)) = span R {(4 : F)}) :
    ((∃ v : V, v ≠ 0 ∧ Q v = 0) → HasBlk Q L a 0 b 0) ∧
      ((¬ ∃ v : V, v ≠ 0 ∧ Q v = 0) →
        HasBlk Q L a (4 * algebraMap R F ρ / a) b (4 * algebraMap R F ρ / b)) := by
  rcases Int.even_or_odd (dord hπ a + dord hπ b) with hev | hodd
  · obtain ⟨hiso, -, hJ⟩ := omeara93_18_vi_even Q hK h2p hπ hV hfg hU hrk ha hb hev hd
    exact ⟨fun _ => hJ, fun h => absurd hiso h⟩
  · obtain ⟨hx, hiff⟩ := omeara93_18_vi_odd Q hK h2p hπ hV hfg hU hrk ha hb hodd hd hρ
    refine ⟨fun hiso => hiff.mpr hiso, fun hniso => ?_⟩
    rcases hx with ⟨hJ, -⟩ | ⟨hKb, -⟩
    · exact absurd (hiff.mp hJ) hniso
    · exact hKb

end Main

end QuadFormsKB.OMeara.D18
