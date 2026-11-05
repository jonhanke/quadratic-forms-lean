import QuadFormsKB.Literature.OMeara.Sec43Omega

/-!
# O'Meara §43E–§43F: the centralizer of $\Omega_n$ and irreducibility (43:13, 43:13a, 43:14, 43:14a, 43:15)

**Setting** (as in `Sec43Omega.lean`): $F$ a field with $2 \ne 0$, $(V, Q)$ a finite-dimensional regular quadratic
space of dimension $n$, $O_n$ = `orth Q`, $\Omega_n$ = `omega Q`, $\tau_u$ = `symmetry Q u hu`. The center $Z_n$ of
$O_n$ is $\{\pm 1_V\}$ except for a hyperbolic plane over a field of three elements (43:12, `mem_center_iff`); an
isometry $\sigma = \pm 1_V$ is written `(∀ x, σ x = x) ∨ ∀ x, σ x = -x`.

**Proves** (O'Meara 1973 printing, Chapter IV, pp. 110–112):
* `mem_centralizer_omega_iff` (**43:13**): for $n \ge 3$ the centralizer of $\Omega_n$ in $O_n$ is $Z_n = \{\pm 1_V\}$;
* `mem_center_omega_iff` (**43:13a**, second sentence): for $n \ge 3$ the center of $\Omega_n$ is $\Omega_n \cap Z_n$;
* `exists_mem_omega_not_pm` (**43:14a**): for $n \ge 3$, $\Omega_n \cap Z_n \subsetneq \Omega_n$ (some element of
  $\Omega_n$ is not $\pm 1_V$). The machine-read text of this corollary is garbled; it was read from the page image
  (p. 112): "$\Omega_n \cap Z_n \subset \Omega_n$ if $n \ge 3$", with $\subset$ the book's proper inclusion;
* `eq_bot_or_eq_top_of_omega_stable`, `exists_mem_omega_map_ne` (**43:14**): for $n \ge 3$ and a subspace
  $0 \subsetneq U \subsetneq V$ there is $\sigma \in \Omega_n$ with $\sigma U \ne U$;
* `exists_basis_Q_eq_of_three_le`, `exists_basis_Q_eq` (**43:15**): a regular space other than a hyperbolic plane
  over a field of three elements has, for every value $\alpha = Q(x)$ with $x \ne 0$ (so $\alpha \ne 0$ in $Q(V)$, or
  $\alpha = 0$ for isotropic $V$), a base $x_0, \dots, x_{n-1}$ with $Q(x_i) = \alpha$ for all $i$.

**Proof notes.** O'Meara proves 43:13 with rotations of planes (anisotropic case) and the rotations of 43:5a
(isotropic case). Here a uniform argument is used: if $\sigma$ commutes with $\omega = \tau_x\tau_y \in \Omega_n$
($x, y$ anisotropic and independent), then $\sigma$ maps the fixed space $\{x, y\}^\perp$ of $\omega$ onto itself, so
$\sigma x \in Fx + Fy$; taking $y = \tau_{x + w}x$ (then $\tau_x\tau_y = \tau_x\tau_{x+w}\tau_x\tau_{x+w} \in \Omega_n$
and $Fx + Fy = Fx + Fw$) for two suitable $w \perp x$ gives $\sigma x \in Fx$, and 43:11 applies. In 43:14 the
regular case is O'Meara's ($-1_U \perp 1_{U^\perp}$ commutes with $\Omega_n$, contradicting 43:13); in the
non-regular case, instead of 43:5a, the element $\omega = \tau_a\tau_z\tau_a\tau_z$ with $a = y + z$ ($x \in \operatorname{rad} U$
isotropic, $y$ a hyperbolic partner, $z \perp x, y$ anisotropic) gives $B(x, \omega x) = -8/Q(z) \ne 0$, so
$\omega x \notin U$. 43:15 is O'Meara's proof (the span of the $\Omega_n$-orbit of $x$ is $\Omega_n$-stable).
-/

open QuadraticMap Submodule Module LinearMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Sec43Irred

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)

theorem omega_le_orth : omega Q ≤ orth Q := by
  unfold omega
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
    (Subgroup.inv_mem _ hb)

/-- $\pm 1_V$ commutes with every linear automorphism. -/
theorem pm_one_comm {σ : V ≃ₗ[F] V} (h : (∀ x, σ x = x) ∨ ∀ x, σ x = -x) (ρ : V ≃ₗ[F] V) :
    σ * ρ = ρ * σ := by
  rcases h with h | h <;> ext v <;> simp [h]

/-- The fixed vectors of $\tau_a\tau_b$ for independent anisotropic $a, b$ are the vectors of $\{a, b\}^\perp$. -/
theorem symmetry_mul_apply_eq_self_iff {a b : V} (ha : Q a ≠ 0) (hb : Q b ≠ 0)
    (hli : LinearIndependent F ![a, b]) (v : V) :
    (symmetry Q a ha * symmetry Q b hb) v = v ↔ bil Q v a = 0 ∧ bil Q v b = 0 := by
  rw [LinearEquiv.mul_apply]
  constructor
  · intro h
    have h' : symmetry Q a ha v = symmetry Q b hb v := by
      conv_lhs => rw [← h]
      exact symmetry_symmetry Q ha _
    rw [symmetry_apply, symmetry_apply] at h'
    have h0 : (2 * bil Q v a / Q a) • a + (-(2 * bil Q v b / Q b)) • b = 0 := by
      rw [neg_smul]; linear_combination (norm := module) -h'
    obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.1 hli _ _ h0
    have h2' : 2 * bil Q v b / Q b = 0 := neg_eq_zero.1 h2
    rw [div_eq_zero_iff, mul_eq_zero] at h1 h2'
    refine ⟨?_, ?_⟩
    · rcases h1 with (h | h) | h
      · exact absurd h iv_two_ne
      · exact h
      · exact absurd h ha
    · rcases h2' with (h | h) | h
      · exact absurd h iv_two_ne
      · exact h
      · exact absurd h hb
  · rintro ⟨h1, h2⟩
    rw [symmetry_apply Q hb, h2]
    simp only [mul_zero, zero_div, zero_smul, sub_zero]
    rw [symmetry_apply Q ha, h1]
    simp

/-- If an isometry $\sigma$ commutes with $\tau_a\tau_b$ ($a, b$ anisotropic and independent), then
$\sigma a \in Fa + Fb$: $\sigma$ preserves the fixed space $\{a, b\}^\perp$ of $\tau_a\tau_b$. -/
theorem apply_mem_span_of_comm_symmetry_mul (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) {a b : V} (ha : Q a ≠ 0) (hb : Q b ≠ 0)
    (hli : LinearIndependent F ![a, b])
    (hc : σ * (symmetry Q a ha * symmetry Q b hb) = (symmetry Q a ha * symmetry Q b hb) * σ) :
    σ a ∈ Submodule.span F {a, b} := by
  set ω := symmetry Q a ha * symmetry Q b hb
  set B : LinearMap.BilinForm F V := QuadraticMap.associated Q
  set P := Submodule.span F {a, b}
  have hrefl : B.IsRefl := fun u v h => (bil_comm Q v u).trans h
  have haP : a ∈ P := Submodule.subset_span (by simp)
  have hbP : b ∈ P := Submodule.subset_span (by simp)
  have hc' : σ⁻¹ * ω = ω * σ⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
  suffices h : σ a ∈ B.orthogonal (B.orthogonal P) by
    rwa [LinearMap.BilinForm.orthogonal_orthogonal hQ hrefl] at h
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hw
  have hwa : bil Q w a = 0 := by rw [bil_comm]; exact hw a haP
  have hwb : bil Q w b = 0 := by rw [bil_comm]; exact hw b hbP
  have hfix : ω w = w := (symmetry_mul_apply_eq_self_iff Q ha hb hli w).2 ⟨hwa, hwb⟩
  have hfix' : ω (σ⁻¹ w) = σ⁻¹ w := by
    have : σ⁻¹ (ω w) = ω (σ⁻¹ w) := LinearEquiv.congr_fun hc' w
    rw [hfix] at this
    exact this.symm
  have h1 := ((symmetry_mul_apply_eq_self_iff Q ha hb hli _).1 hfix').1
  have h2 : σ (σ⁻¹ w) = w := σ.apply_symm_apply w
  show bil Q w (σ a) = 0
  rw [← h2, iv_bil_orth Q hσ]
  exact h1

/-- A step of 43:13: an isometry $\sigma$ commuting with $\Omega_n$ maps an anisotropic $x$ into $Fx + Fw$ for every
$w \ne 0$ orthogonal to $x$ with $Q(x + w) = Q(x) + Q(w) \ne 0$. -/
theorem exists_apply_eq_of_comm_omega (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (hc : ∀ ω ∈ omega Q, σ * ω = ω * σ) {x w : V} (hx : Q x ≠ 0)
    (hxw : bil Q x w = 0) (hw0 : w ≠ 0) (hu : Q x + Q w ≠ 0) :
    ∃ p q : F, σ x = p • x + q • w := by
  have hQu : Q (x + w) = Q x + Q w := by rw [Q_add, hxw]; ring
  have hu' : Q (x + w) ≠ 0 := by rw [hQu]; exact hu
  set τu := symmetry Q (x + w) hu'
  set y := τu x
  have hy : Q y ≠ 0 := by rw [symmetry_mem_orth Q hu' x]; exact hx
  set c := 2 * Q x / Q (x + w)
  have hc0 : c ≠ 0 := div_ne_zero (mul_ne_zero iv_two_ne hx) hu'
  have hyx : y = (1 - c) • x - c • w := by
    simp only [y, τu, c, symmetry_apply, bil_add_right, hxw, bil_self, add_zero]
    module
  have hwx : bil Q w x = 0 := by rw [bil_comm]; exact hxw
  -- x and y are independent
  have hli : LinearIndependent F ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [hyx] at hst
    have h1 := congrArg (fun v => bil Q v x) hst
    simp only [bil_add_left, bil_smul_left, bil_sub_left, bil_self, hwx, iv_bil_zero_left] at h1
    have hcoef : s + t * (1 - c) = 0 := by
      have : (s + t * (1 - c)) * Q x = 0 := by linear_combination h1
      exact (mul_eq_zero.1 this).resolve_right hx
    have h2 : (t * c) • w = 0 := by
      have : (s + t * (1 - c)) • x - (t * c) • w = 0 := by
        linear_combination (norm := module) hst
      rw [hcoef, zero_smul, zero_sub, neg_eq_zero] at this
      exact this
    have ht : t = 0 := by
      have := (smul_eq_zero.1 h2).resolve_right hw0
      exact (mul_eq_zero.1 this).resolve_right hc0
    refine ⟨?_, ht⟩
    rw [ht] at hcoef; simpa using hcoef
  -- τ_x τ_y ∈ Ω
  have hmem : symmetry Q x hx * symmetry Q y hy ∈ omega Q := by
    have hτ : symmetry Q y hy = τu * symmetry Q x hx * τu := by
      have := Sp55.conj_symmetry Q (symmetry_mem_orth Q hu') hx
      rw [symmetry_inv'] at this
      exact this.symm
    rw [hτ]
    apply symmetryCommutators_subset_omega
    exact ⟨x, x + w, hx, hu', by simp only [τu]; group⟩
  have hspan := apply_mem_span_of_comm_symmetry_mul Q hQ hσ hx hy hli (hc _ hmem)
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.1 hspan
  refine ⟨p + q * (1 - c), -(q * c), ?_⟩
  rw [← hpq, hyx]
  module

/-- A field computation for 43:13: for nonzero $a, b, c$ there are two independent coefficient pairs
$(s_i, t_i)$ with $c + s_i^2a + t_i^2b \ne 0$. -/
theorem exists_two_pairs {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ s₁ t₁ s₂ t₂ : F, s₁ * t₂ - s₂ * t₁ ≠ 0 ∧ c + (s₁ ^ 2 * a + t₁ ^ 2 * b) ≠ 0 ∧
      c + (s₂ ^ 2 * a + t₂ ^ 2 * b) ≠ 0 := by
  by_cases hac : c + a = 0 <;> by_cases hbc : c + b = 0
  · refine ⟨1, 1, 1, -1, ?_, ?_, ?_⟩
    · have : (1 : F) * -1 - 1 * 1 = -2 := by ring
      rw [this]; exact neg_ne_zero.2 iv_two_ne
    · have : c + ((1 : F) ^ 2 * a + 1 ^ 2 * b) = -c := by linear_combination hac + hbc
      rw [this]; exact neg_ne_zero.2 hc
    · have : c + ((1 : F) ^ 2 * a + (-1) ^ 2 * b) = -c := by linear_combination hac + hbc
      rw [this]; exact neg_ne_zero.2 hc
  · refine ⟨0, 1, 1, 1, by norm_num, by simpa using hbc, ?_⟩
    have : c + ((1 : F) ^ 2 * a + 1 ^ 2 * b) = b := by linear_combination hac
    rw [this]; exact hb
  · refine ⟨1, 0, 1, 1, by norm_num, by simpa using hac, ?_⟩
    have : c + ((1 : F) ^ 2 * a + 1 ^ 2 * b) = a := by linear_combination hbc
    rw [this]; exact ha
  · exact ⟨1, 0, 0, 1, by norm_num, by simpa using hac, by simpa using hbc⟩

/-- **O'Meara 43:13** (p. 110). For a regular quadratic space of dimension $n \ge 3$, the centralizer of $\Omega_n$
in $O_n$ is $Z_n = \{\pm 1_V\}$: an isometry $\sigma$ commutes with every element of $\Omega_n$ if and only if
$\sigma = \pm 1_V$. (The proof differs from O'Meara's, see the module docstring.) -/
@[kb "omeara1963" "§43E, 43:13, p. 110"]
theorem mem_centralizer_omega_iff (hQ : (QuadraticMap.associated Q).Nondegenerate) (h3 : 3 ≤ finrank F V)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) :
    (∀ ω ∈ omega Q, σ * ω = ω * σ) ↔ (∀ x, σ x = x) ∨ ∀ x, σ x = -x := by
  constructor
  · intro hc
    have hexc : ¬ IsExceptional43 Q := fun h => by have := h.1; omega
    apply eq_one_or_neg_of_forall_aniso_line Q hQ hexc hσ
    intro x hx
    have hx0 : x ≠ 0 := fun h => hx (by rw [h, map_zero])
    obtain ⟨e₁, he₁, hxe₁⟩ := cd_exists_perp_aniso Q (cd_reg_of_nondeg Q hQ) h3 hx0
    obtain ⟨e₂, he₂, hxe₂, he₁₂⟩ := exists_aniso_orth_two Q hQ h3 hx he₁ hxe₁
    have he₂₁ : bil Q e₂ e₁ = 0 := by rw [bil_comm]; exact he₁₂
    obtain ⟨s₁, t₁, s₂, t₂, hdet, h₁, h₂⟩ := exists_two_pairs he₁ he₂ hx
    have hQw : ∀ s t : F, Q (s • e₁ + t • e₂) = s ^ 2 * Q e₁ + t ^ 2 * Q e₂ := by
      intro s t
      rw [Q_add, Q_smul, Q_smul, bil_smul_left, bil_smul_right, he₁₂]; ring
    have hbx : ∀ s t : F, bil Q x (s • e₁ + t • e₂) = 0 := by
      intro s t
      rw [bil_add_right, bil_smul_right, bil_smul_right, hxe₁, hxe₂]; ring
    have hb1 : ∀ s t : F, bil Q (s • e₁ + t • e₂) e₁ = s * Q e₁ := by
      intro s t
      rw [bil_add_left, bil_smul_left, bil_smul_left, he₂₁, bil_self]; ring
    have hb2 : ∀ s t : F, bil Q (s • e₁ + t • e₂) e₂ = t * Q e₂ := by
      intro s t
      rw [bil_add_left, bil_smul_left, bil_smul_left, he₁₂, bil_self]; ring
    have hne : ∀ s t : F, (s ≠ 0 ∨ t ≠ 0) → s • e₁ + t • e₂ ≠ 0 := by
      intro s t hst h0
      have k1 := hb1 s t
      have k2 := hb2 s t
      rw [h0, iv_bil_zero_left] at k1 k2
      rcases hst with hs | ht
      · exact mul_ne_zero hs he₁ k1.symm
      · exact mul_ne_zero ht he₂ k2.symm
    have hnz : ∀ s t s' t' : F, s * t' - s' * t ≠ 0 → s ≠ 0 ∨ t ≠ 0 := by
      intro s t s' t' h
      by_contra hc'
      push Not at hc'
      apply h; rw [hc'.1, hc'.2]; ring
    have hnz' : s₂ ≠ 0 ∨ t₂ ≠ 0 := hnz s₂ t₂ s₁ t₁ (by intro h; apply hdet; linear_combination -h)
    obtain ⟨p₁, q₁, hσ₁⟩ := exists_apply_eq_of_comm_omega Q hQ hσ hc hx (hbx s₁ t₁)
      (hne s₁ t₁ (hnz s₁ t₁ s₂ t₂ hdet)) (by rw [hQw]; exact h₁)
    obtain ⟨p₂, q₂, hσ₂⟩ := exists_apply_eq_of_comm_omega Q hQ hσ hc hx (hbx s₂ t₂)
      (hne s₂ t₂ hnz') (by rw [hQw]; exact h₂)
    have hxe₁' : bil Q x e₁ = 0 := hxe₁
    have k1 := congrArg (fun v => bil Q v e₁) (hσ₁.symm.trans hσ₂)
    have k2 := congrArg (fun v => bil Q v e₂) (hσ₁.symm.trans hσ₂)
    simp only [bil_add_left, bil_smul_left, hxe₁, hxe₂, hb1, hb2] at k1 k2
    have k1' : q₁ * s₁ = q₂ * s₂ := mul_right_cancel₀ he₁ (by linear_combination k1)
    have k2' : q₁ * t₁ = q₂ * t₂ := mul_right_cancel₀ he₂ (by linear_combination k2)
    have hq : q₁ = 0 := by
      have : q₁ * (s₁ * t₂ - s₂ * t₁) = 0 := by linear_combination t₂ * k1' - s₂ * k2'
      exact (mul_eq_zero.1 this).resolve_right hdet
    exact ⟨p₁, by rw [hσ₁, hq, zero_smul, add_zero]⟩
  · intro h ω _
    exact pm_one_comm h ω

/-- **O'Meara 43:13a**, second sentence (p. 111). For a regular quadratic space of dimension $n \ge 3$, the center
of $\Omega_n$ is $\Omega_n \cap Z_n$: an element of $\Omega_n$ commutes with all of $\Omega_n$ iff it is $\pm 1_V$.
The first sentence (the center of $O^+_n$) is `mem_center_orthPlus_iff`. -/
@[kb "omeara1963" "§43E, 43:13a, p. 111 (center of Ω_n is Ω_n ∩ Z_n for n ≥ 3)"]
theorem mem_center_omega_iff (hQ : (QuadraticMap.associated Q).Nondegenerate) (h3 : 3 ≤ finrank F V)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ omega Q) :
    (∀ ω ∈ omega Q, σ * ω = ω * σ) ↔ (∀ x, σ x = x) ∨ ∀ x, σ x = -x :=
  mem_centralizer_omega_iff Q hQ h3 (omega_le_orth Q hσ)

/-- **O'Meara 43:14a** (p. 112; the formula is lost in the machine-read text and was read from the page image:
"$\Omega_n \cap Z_n \subset \Omega_n$ if $n \ge 3$", a proper inclusion). For a regular quadratic space of dimension
$n \ge 3$, some element of $\Omega_n$ is not $\pm 1_V$. -/
@[kb "omeara1963" "§43F, 43:14a, p. 112 (Ω_n ∩ Z_n ⊊ Ω_n for n ≥ 3)"]
theorem exists_mem_omega_not_pm (hQ : (QuadraticMap.associated Q).Nondegenerate) (h3 : 3 ≤ finrank F V) :
    ∃ ω ∈ omega Q, ¬ ((∀ x, ω x = x) ∨ ∀ x, ω x = -x) := by
  by_contra h
  push Not at h
  have hall : ∀ σ ∈ orth Q, (∀ x, σ x = x) ∨ ∀ x, σ x = -x := by
    intro σ hσ
    refine (mem_centralizer_omega_iff Q hQ h3 hσ).1 fun ω hω => ?_
    exact (pm_one_comm (h ω hω) σ).symm
  exact not_commutative_of_two_le Q hQ (fun h => by have := h.1; omega) (by omega)
    fun σ hσ ρ _ => pm_one_comm (hall σ hσ) ρ

/-- The core of 43:14: for $n \ge 3$, a subspace mapped into itself by every element of $\Omega_n$ is $0$ or $V$. -/
theorem eq_bot_or_eq_top_of_omega_stable (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : 3 ≤ finrank F V) {U : Submodule F V} (hstab : ∀ σ ∈ omega Q, ∀ u ∈ U, σ u ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hrad : ∃ x ∈ U, x ≠ 0 ∧ ∀ u ∈ U, bil Q x u = 0
  · exfalso
    obtain ⟨x, hxU, hx0, hxrad⟩ := hrad
    have hx : Q x = 0 := by rw [← bil_self]; exact hxrad x hxU
    obtain ⟨y, hy, hxy⟩ := exists_hyp_partner Q hQ hx0 hx
    obtain ⟨z, hz, hxz, hyz⟩ := exists_aniso_orth_pair Q hQ h3 hx hy hxy
    have hQa : Q (y + z) = Q z := by rw [Q_add, hy, hyz]; ring
    have ha : Q (y + z) ≠ 0 := by rw [hQa]; exact hz
    set τa := symmetry Q (y + z) ha
    set τz := symmetry Q z hz
    have hω : τa * τz * τa * τz ∈ omega Q :=
      symmetryCommutators_subset_omega Q ⟨y + z, z, ha, hz, rfl⟩
    have hωx := hstab _ hω x hxU
    have key := hxrad _ hωx
    -- compute ωx = x - (8/q) y - (4/q) z
    have hzy : bil Q z y = 0 := by rw [bil_comm]; exact hyz
    have hzx : bil Q z x = 0 := by rw [bil_comm]; exact hxz
    have hyx : bil Q y x = 1 := by rw [bil_comm]; exact hxy
    have c1 : 2 * bil Q x z / Q z = 0 := by rw [hxz]; simp
    have c2 : 2 * bil Q x (y + z) / Q (y + z) = 2 / Q z := by rw [bil_add_right, hxy, hxz, hQa]; ring
    have c3 : 2 * bil Q (y + z) z / Q z = 2 := by
      rw [bil_add_left, hyz, bil_self, zero_add]; field_simp
    have c4 : 2 * bil Q (y - z) (y + z) / Q (y + z) = -2 := by
      rw [hQa, bil_sub_left, bil_add_right, bil_add_right, bil_self, bil_self, hy, hyz, hzy]
      field_simp; ring
    have e1 : τz x = x := by simp only [τz, symmetry_apply, c1, zero_smul, sub_zero]
    have e2 : τa x = x - (2 / Q z) • (y + z) := by simp only [τa, symmetry_apply, c2]
    have e3 : τz (y + z) = y - z := by
      simp only [τz, symmetry_apply, c3]; module
    have e4 : τa (y - z) = (3 : F) • y + z := by
      simp only [τa, symmetry_apply, c4]; module
    have hωx' : (τa * τz * τa * τz) x = x - (8 / Q z) • y - (4 / Q z) • z := by
      simp only [LinearEquiv.mul_apply]
      rw [e1, e2, map_sub, e1, map_smul, e3, map_sub, map_smul, e4, e2]
      field_simp
      module
    rw [hωx'] at key
    simp only [bil_sub_right, bil_smul_right, bil_self, hx, hxy, hxz] at key
    have : (8 : F) / Q z = 0 := by linear_combination -key
    rw [div_eq_zero_iff] at this
    rcases this with h8 | h8
    · have : (8 : F) = 2 * 2 * 2 := by norm_num
      rw [this] at h8
      exact iv_two_ne (by simpa [mul_self_eq_zero] using h8)
    · exact hz h8
  · push Not at hrad
    -- U is regular
    have hU : (QuadraticMap.associated (Q.comp U.subtype)).Nondegenerate := by
      constructor
      · intro a ha
        have := hrad a a.2
        have hb : ∀ u ∈ U, bil Q a u = 0 := fun u hu => by
          have := ha ⟨u, hu⟩
          simpa [bil, LinearMap.BilinForm.restrict_apply, Sp55.bil_comp_subtype] using this
        by_contra h0
        exact (this (fun h => h0 (Subtype.ext h))) |>.elim fun u hu => hu.2 (hb u hu.1)
      · intro a ha
        have hb : ∀ u ∈ U, bil Q a u = 0 := fun u hu => by
          have := ha ⟨u, hu⟩
          rw [bil_comm]
          simpa [bil, LinearMap.BilinForm.restrict_apply, Sp55.bil_comp_subtype] using this
        by_contra h0
        obtain ⟨u, hu, hne⟩ := hrad a a.2 (fun h => h0 (Subtype.ext h))
        exact hne (hb u hu)
    set W := LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q : LinearMap.BilinForm F V) U
    have hcpl : IsCompl U W := Sp55.isCompl_perp Q hU
    have horth := Sp55.horth_perp Q (U := U)
    set ρ := Sp55.extId hcpl (LinearEquiv.neg F)
    have hρ : ρ ∈ orth Q := Sp55.extId_mem_orth Q hcpl horth (fun v => by simp)
    have hρa : ∀ (a : U) (b : W), ρ ((a : V) + b) = -(a : V) + b := by
      intro a b
      rw [Sp55.extId_apply]; simp
    -- elements of Ω preserve W
    have hstabW : ∀ ω ∈ omega Q, ∀ b ∈ W, ω b ∈ W := by
      intro ω hω b hb
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      have hω' : ω⁻¹ ∈ omega Q := Subgroup.inv_mem _ hω
      have h1 : ω (ω⁻¹ u) = u := ω.apply_symm_apply u
      show bil Q u (ω b) = 0
      rw [← h1, iv_bil_orth Q (omega_le_orth Q hω)]
      exact horth _ (hstab _ hω' u hu) b hb
    have hcomm : ∀ ω ∈ omega Q, ρ * ω = ω * ρ := by
      intro ω hω
      ext v
      obtain ⟨a, b, rfl⟩ := Sp55.exists_decomp hcpl v
      simp only [LinearEquiv.mul_apply]
      have h1 : ω ((a : V) + b) = ((⟨ω a, hstab ω hω a a.2⟩ : U) : V) + ((⟨ω b, hstabW ω hω b b.2⟩ : W) : V) := by
        simp
      rw [h1, hρa, hρa, map_add, map_neg]
    rcases (mem_centralizer_omega_iff Q hQ h3 hρ).1 hcomm with h | h
    · left
      rw [eq_bot_iff]
      intro u hu
      have := h u
      have e := hρa ⟨u, hu⟩ 0
      simp only [Submodule.coe_zero, add_zero] at e
      rw [e] at this
      have h2 : (2 : F) • u = 0 := by rw [two_smul]; nth_rewrite 1 [← this]; simp
      exact (Submodule.mem_bot F).2 ((smul_eq_zero.1 h2).resolve_left iv_two_ne)
    · right
      have hWbot : W = ⊥ := by
        rw [eq_bot_iff]
        intro w hw
        have := h w
        have e := hρa 0 ⟨w, hw⟩
        simp only [Submodule.coe_zero, zero_add, neg_zero] at e
        rw [e] at this
        have h2 : (2 : F) • w = 0 := by rw [two_smul]; nth_rewrite 2 [this]; simp
        exact (Submodule.mem_bot F).2 ((smul_eq_zero.1 h2).resolve_left iv_two_ne)
      have := hcpl.sup_eq_top
      rwa [hWbot, sup_bot_eq] at this

/-- **O'Meara 43:14** (p. 111). Let $V$ be a regular quadratic space of dimension $n \ge 3$ and $U$ a subspace with
$0 \subsetneq U \subsetneq V$. Then there is $\sigma \in \Omega_n$ with $\sigma U \ne U$. -/
@[kb "omeara1963" "§43F, 43:14, p. 111"]
theorem exists_mem_omega_map_ne (hQ : (QuadraticMap.associated Q).Nondegenerate) (h3 : 3 ≤ finrank F V)
    {U : Submodule F V} (h0 : U ≠ ⊥) (htop : U ≠ ⊤) :
    ∃ σ ∈ omega Q, U.map (σ : V →ₗ[F] V) ≠ U := by
  by_contra h
  push Not at h
  rcases eq_bot_or_eq_top_of_omega_stable Q hQ h3 (U := U) (fun σ hσ u hu => by
    rw [← h σ hσ]; exact Submodule.mem_map_of_mem hu) with h' | h'
  · exact h0 h'
  · exact htop h'

/-- **O'Meara 43:15** (p. 112), the case $n \ge 3$. Let $V$ be a regular quadratic space of dimension $n \ge 3$ and
$x \ne 0$ a vector, $\alpha = Q(x)$ (so $\alpha$ is any non-zero element of $Q(V)$, or $\alpha = 0$ when $V$ is
isotropic). Then $V$ has a base $x_0, \dots, x_{n-1}$ with $Q(x_i) = \alpha$ for all $i$; the base vectors can be
taken of the form $\sigma x$ with $\sigma \in \Omega_n$. -/
@[kb "omeara1963" "§43F, 43:15, p. 112 (case n ≥ 3)"]
theorem exists_basis_Q_eq_of_three_le (hQ : (QuadraticMap.associated Q).Nondegenerate) (h3 : 3 ≤ finrank F V)
    {x : V} (hx0 : x ≠ 0) :
    ∃ b : Basis (Fin (finrank F V)) F V, ∀ i, Q (b i) = Q x := by
  set S := Set.range fun σ : omega Q => (σ : V ≃ₗ[F] V) x
  set U := Submodule.span F S
  have hstab : ∀ σ ∈ omega Q, ∀ u ∈ U, σ u ∈ U := by
    intro σ hσ u hu
    have hle : U ≤ U.comap (σ : V →ₗ[F] V) := by
      rw [Submodule.span_le]
      rintro _ ⟨τ, rfl⟩
      exact Submodule.subset_span ⟨⟨σ * τ, Subgroup.mul_mem _ hσ τ.2⟩, rfl⟩
    exact hle hu
  have hxU : x ∈ U := Submodule.subset_span ⟨1, rfl⟩
  have hU : U = ⊤ := by
    rcases eq_bot_or_eq_top_of_omega_stable Q hQ h3 hstab with h | h
    · exact absurd (h ▸ hxU) (by simpa using hx0)
    · exact h
  obtain ⟨T, hTS, hTspan, hTli⟩ := exists_linearIndependent F S
  let b₀ : Basis T F V := Basis.mk hTli (by rw [Subtype.range_coe, hTspan]; exact hU.ge)
  refine ⟨b₀.reindex (b₀.indexEquiv (Module.finBasis F V)), fun i => ?_⟩
  rw [Basis.reindex_apply, Basis.mk_apply]
  obtain ⟨σ, hσ⟩ := hTS (Subtype.mem _)
  rw [← hσ]
  exact omega_le_orth Q σ.2 x

/-- **O'Meara 43:15** (p. 112). Let $V$ be a regular quadratic space other than a hyperbolic plane over a field of
three elements, and let $x \ne 0$, $\alpha = Q(x)$ (any non-zero element of $Q(V)$, or $\alpha = 0$ when $V$ is
isotropic). Then $V$ has a base $x_0, \dots, x_{n-1}$ in which $Q(x_i) = \alpha$ for all $i$ (O'Meara's
$x_1, \dots, x_n$, indexed from $0$ here). -/
@[kb "omeara1963" "§43F, 43:15, p. 112"]
theorem exists_basis_Q_eq (hQ : (QuadraticMap.associated Q).Nondegenerate) (hexc : ¬ IsExceptional43 Q)
    {x : V} (hx0 : x ≠ 0) :
    ∃ b : Basis (Fin (finrank F V)) F V, ∀ i, Q (b i) = Q x := by
  have hpos : 0 < finrank F V := Module.finrank_pos_iff_exists_ne_zero.2 ⟨x, hx0⟩
  rcases Nat.lt_or_ge (finrank F V) 3 with hlt | h3
  · rcases Nat.lt_or_ge (finrank F V) 2 with hlt2 | h2
    · -- n = 1
      have h1 : finrank F V = 1 := by omega
      have hli : LinearIndependent F ![x] := linearIndependent_unique_iff.2 (by simpa using hx0)
      let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h1])
      refine ⟨b.reindex (finCongr (by simp [h1])), fun i => ?_⟩
      simp [b]
    · -- n = 2
      have h2' : finrank F V = 2 := by omega
      by_cases hα : Q x = 0
      · obtain ⟨y, hy, hxy⟩ := exists_hyp_partner Q hQ hx0 hα
        have hli := linearIndependent_pair_of_hyp Q hα hy hxy
        let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2'])
        refine ⟨b.reindex (finCongr (by simp [h2'])), fun i => ?_⟩
        rw [Basis.reindex_apply]
        simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]
        generalize (finCongr _).symm i = j
        fin_cases j <;> simp [hα, hy]
      · obtain ⟨b, hb⟩ := exists_basis_Q_eq_of_finrank_two Q hQ h2' hexc hα rfl
        exact ⟨b.reindex (finCongr h2'.symm), fun i => by rw [Basis.reindex_apply]; exact hb _⟩
  · exact exists_basis_Q_eq_of_three_le Q hQ h3 hx0

end Sec43Irred

end QuadFormsKB.OMeara
