/-
# O'Meara §92: gaps (the footnote of 92:4, Examples 92:7 and 92:8)

**Setting** (as in `Sec92Sym.lean`): $R$ a discrete valuation ring with fraction field $F$, $2$ a unit of $R$
(non-dyadic), a finite-dimensional regular quadratic space $(V, Q)$ over $F$, lattices = `Submodule R V`.
For the examples $R$ is moreover complete with finite residue field (the local field), which is used only through
Hensel's lemma: a unit congruent to a square modulo $\mathfrak p$ is a square.

**Proves**
* `exists_symmetry_list_of_two_le` (**92:4, footnote**, p. 248): for $n \ge 2$ every element of $O(L)$ is a product of
  at most $2n - 2$ symmetries in $O(L)$ (induction starting at $n = 2$; the binary step uses that an improper isometry
  of a regular binary space is a symmetry, `Gap92.binary_improper_symmetry`);
* `exists_lattice_spinorNorm_square` (**92:7**, p. 249): if $V \cong \langle 1\rangle \perp \cdots \perp \langle 1\rangle$
  there is a lattice $L$ on $V$ with $\theta(O(L)) = \dot F^2$;
* `exists_lattice_improper_spinorNorm` (**92:8**, p. 250): if moreover $\dim V$ is even (and positive) and $\varepsilon$
  is a unit, there is a lattice $L$ on $V$ with $\theta(O^-(L)) = \varepsilon\dot F^2$.
-/
import QuadFormsKB.Literature.OMeara.Sec93E
import QuadFormsKB.Literature.OMeara.Sec55

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

namespace Gap92

section Binary

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- An isometry fixing a vector $y$, moving a vector $k \perp y$ inside $Fy + Fk$ and fixing everything orthogonal to
$y$ and $k$ is the identity or the symmetry $\tau_k$. -/
theorem fix_y_cases {y k : V} (hy : Q y ≠ 0) (hk : Q k ≠ 0) (hyk : bil Q y k = 0)
    {θ : V ≃ₗ[F] V} (hθ : θ ∈ orth Q) (hθy : θ y = y) (hθk : ∃ a b : F, θ k = a • y + b • k)
    (hθx : ∀ x, bil Q x y = 0 → bil Q x k = 0 → θ x = x) :
    θ = 1 ∨ θ = symmetry Q k hk := by
  obtain ⟨a, b, hab⟩ := hθk
  have hbyk : bil Q k y = 0 := by rw [bil_comm]; exact hyk
  have ha : a = 0 := by
    have h1 : bil Q (θ k) (θ y) = bil Q k y := sym4_bil_orth Q hθ k y
    rw [hθy, hab, bil_add_left, bil_smul_left, bil_smul_left, bil_self, hbyk] at h1
    have : a * Q y = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_right hy
  subst ha
  have hb : b = 1 ∨ b = -1 := by
    have h1 : Q (θ k) = Q k := hθ k
    rw [hab, zero_smul, zero_add, Q_smul] at h1
    have : (b - 1) * (b + 1) * Q k = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · left; linear_combination h
      · right; linear_combination h
    · exact absurd h hk
  have hdec : ∀ v : V, ∃ α β : F, ∃ x : V, v = α • y + β • k + x ∧ bil Q x y = 0 ∧ bil Q x k = 0 ∧
      bil Q v k = β * Q k := by
    intro v
    have e1 : (bil Q v y / Q y) * Q y = bil Q v y := div_mul_cancel₀ _ hy
    have e2 : (bil Q v k / Q k) * Q k = bil Q v k := div_mul_cancel₀ _ hk
    refine ⟨bil Q v y / Q y, bil Q v k / Q k, v - (bil Q v y / Q y) • y - (bil Q v k / Q k) • k,
      by abel, ?_, ?_, e2.symm⟩
    · rw [bil_sub_left, bil_sub_left, bil_smul_left, bil_smul_left, bil_self, hbyk, e1]; ring
    · rw [bil_sub_left, bil_sub_left, bil_smul_left, bil_smul_left, bil_self, hyk, e2]; ring
  rcases hb with rfl | rfl
  · left
    ext v
    obtain ⟨α, β, x, hv, hxy, hxk, -⟩ := hdec v
    have hθv : θ v = α • y + β • ((0 : F) • y + (1 : F) • k) + x := by
      conv_lhs => rw [hv]
      rw [map_add, map_add, map_smul, map_smul, hθy, hab, hθx x hxy hxk]
    change θ v = v
    rw [hθv]
    conv_rhs => rw [hv]
    module
  · right
    ext v
    obtain ⟨α, β, x, hv, hxy, hxk, hbv⟩ := hdec v
    have hθv : θ v = α • y + β • ((0 : F) • y + (-1 : F) • k) + x := by
      conv_lhs => rw [hv]
      rw [map_add, map_add, map_smul, map_smul, hθy, hab, hθx x hxy hxk]
    have e2 : 2 * bil Q v k / Q k = 2 * β := by rw [hbv]; field_simp
    rw [hθv, symmetry_apply, e2]
    conv_rhs => rw [hv]
    module

/-- The quadratic form on the span of two orthogonal vectors. -/
theorem Q_pair {y k : V} (hyk : bil Q y k = 0) (r s : F) :
    Q (r • y + s • k) = r ^ 2 * Q y + s ^ 2 * Q k := by
  rw [Q_add, Q_smul, Q_smul, bil_smul_left, bil_smul_right, hyk]; ring

theorem neg_one_ne_one_of_two : (-1 : Fˣ) ≠ 1 := by
  intro h
  have h' : (-1 : F) = 1 := congrArg Units.val h
  have h2F : (2 : F) = 0 := by linear_combination -h'
  exact (isUnit_of_invertible (2 : F)).ne_zero h2F

/-- **An improper isometry of a binary lattice is a symmetry** (the binary step of the footnote of 92:4): if
$L = \mathfrak o y + \mathfrak o k$ with $y \perp k$ anisotropic, $\sigma \in O(L)$ fixes every vector orthogonal to
$L$ and has $\det\sigma = -1$, then $\sigma = \tau_u$ for some $u \in L$. -/
theorem binary_improper_symmetry [FiniteDimensional F V] {L : Submodule R V} {y k : V} (hy : Q y ≠ 0)
    (hk : Q k ≠ 0) (hyk : bil Q y k = 0) (hLyk : L = R ∙ y ⊔ R ∙ k) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ orthLat Q L) (hfix : ∀ x, (∀ z ∈ L, bil Q x z = 0) → σ x = x)
    (hdet : LinearEquiv.det σ = -1) : ∃ u : V, ∃ hu : Q u ≠ 0, u ∈ L ∧ σ = symmetry Q u hu := by
  have hyL : y ∈ L := hLyk ▸ mem_sup_left (mem_span_singleton_self y)
  have hkL : k ∈ L := hLyk ▸ mem_sup_right (mem_span_singleton_self k)
  have hP : ∀ z ∈ L, ∃ r s : F, z = r • y + s • k := by
    intro z hz
    rw [hLyk] at hz
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup.mp hz
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hp
    obtain ⟨s, rfl⟩ := mem_span_singleton.mp hq
    exact ⟨algebraMap R F r, algebraMap R F s, by rw [algebraMap_smul, algebraMap_smul]⟩
  have hσL : ∀ z ∈ L, σ z ∈ L := by
    intro z hz
    have : σ z ∈ latMap σ L := Submodule.mem_map_of_mem hz
    rwa [hσ.2] at this
  have hfix' : ∀ x, bil Q x y = 0 → bil Q x k = 0 → σ x = x := by
    intro x hxy hxk
    apply hfix
    intro z hz
    obtain ⟨r, s, rfl⟩ := hP z hz
    rw [bil_add_right, bil_smul_right, bil_smul_right, hxy, hxk]; ring
  by_cases hw : σ y = y
  · obtain ⟨a, b, hab⟩ := hP (σ k) (hσL k hkL)
    rcases fix_y_cases Q hy hk hyk hσ.1 hw ⟨a, b, hab⟩ hfix' with h | h
    · exfalso
      rw [h, map_one] at hdet
      exact neg_one_ne_one_of_two (F := F) hdet.symm
    · exact ⟨k, hk, hkL, h⟩
  · obtain ⟨w, hwdef⟩ : ∃ w, w = σ y := ⟨_, rfl⟩
    rw [← hwdef] at hw
    have hwL : w ∈ L := hwdef ▸ hσL y hyL
    obtain ⟨r, s, hrs⟩ := hP w hwL
    have hQw : Q w = Q y := by rw [hwdef]; exact hσ.1 y
    have hQw' : r ^ 2 * Q y + s ^ 2 * Q k = Q y := by rw [← Q_pair Q hyk, ← hrs]; exact hQw
    have hyw : y - w = (1 - r) • y + (-s) • k := by rw [hrs]; module
    have hQyw : Q (y - w) ≠ 0 := by
      intro h0
      rw [hyw, Q_pair Q hyk] at h0
      have h1 : 2 * (1 - r) * Q y = 0 := by linear_combination h0 - hQw'
      have hr : r = 1 := by
        have := (mul_eq_zero.mp h1).resolve_right hy
        have := (mul_eq_zero.mp this).resolve_left two_ne_zero
        linear_combination -this
      subst hr
      have h3 : s ^ 2 * Q k = 0 := by linear_combination hQw'
      have hs : s = 0 := by
        have := (mul_eq_zero.mp h3).resolve_right hk
        exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      subst hs
      apply hw
      rw [hrs]; simp
    set τ := symmetry Q (y - w) hQyw with hτ
    have hτy : τ y = w := by
      rw [hτ, sym4_symmetry_apply_of_two_bil Q hQyw]
      · abel
      · have hqa : Q (y - w) = 2 * Q y - 2 * bil Q y w := by
          have := Q_add Q y (-w)
          rw [← sub_eq_add_neg, sym4_bil_neg_right, QuadraticMap.map_neg] at this
          rw [this, hQw]; ring
        rw [bil_sub_right, bil_self, hqa]; ring
    have hτw : τ w = y := by
      have := symmetry_symmetry Q hQyw y
      rw [← hτ, hτy] at this
      exact this
    have hθ : τ * σ ∈ orth Q := (orth Q).mul_mem (symmetry_mem_orth Q hQyw) hσ.1
    have hθy : (τ * σ) y = y := by
      rw [LinearEquiv.mul_apply, ← hwdef, hτw]
    have hθk : ∃ a b : F, (τ * σ) k = a • y + b • k := by
      obtain ⟨r', s', hz⟩ := hP (σ k) (hσL k hkL)
      obtain ⟨c, hc⟩ : ∃ c, c = 2 * bil Q (σ k) (y - w) / Q (y - w) := ⟨_, rfl⟩
      refine ⟨r' - c * (1 - r), s' - c * (-s), ?_⟩
      rw [LinearEquiv.mul_apply, hτ, symmetry_apply, ← hc, hz, hyw]
      module
    have hθx : ∀ x, bil Q x y = 0 → bil Q x k = 0 → (τ * σ) x = x := by
      intro x hxy hxk
      rw [LinearEquiv.mul_apply, hfix' x hxy hxk, hτ, symmetry_apply]
      have : bil Q x (y - w) = 0 := by
        rw [hyw, bil_add_right, bil_smul_right, bil_smul_right, hxy, hxk]; ring
      rw [this]; simp
    have hdetθ : LinearEquiv.det (τ * σ) = 1 := by
      rw [map_mul, hdet, hτ, det_symmetry Q hQyw]; simp
    rcases fix_y_cases Q hy hk hyk hθ hθy hθk hθx with h | h
    · refine ⟨y - w, hQyw, L.sub_mem hyL hwL, ?_⟩
      ext x
      have h1 : τ (τ (σ x)) = σ x := symmetry_symmetry Q hQyw (σ x)
      have h2 : τ (σ x) = x := by
        have := DFunLike.congr_fun h x
        exact this
      show σ x = τ x
      calc σ x = τ (τ (σ x)) := h1.symm
        _ = τ x := by rw [h2]
    · exfalso
      rw [h, det_symmetry Q hk] at hdetθ
      exact neg_one_ne_one_of_two (F := F) hdetθ

end Binary

section Sym2

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- The base case of the footnote of 92:4: a binary lattice $L$ (with isometries fixing the orthogonal complement)
has every unit a product of at most $2$ symmetries of $L$. -/
theorem aux_rank_two (h2 : IsUnit (2 : R)) [FiniteDimensional F V] {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) (hrk : finrank R L = 2) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orthLat Q L)
    (hfix : ∀ x, (∀ z ∈ L, bil Q x z = 0) → σ x = x) :
    ∃ l : List V, l.length ≤ 2 ∧ (∀ u ∈ l, IsSymVec Q L u) ∧
      σ = (l.map (symmetryOrOne Q)).prod := by
  have hne : L ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hrk; omega
  obtain ⟨y, K, hyL, hQ, hs, hK, hrkK⟩ := sym4_exists_split Q h2 hfg hreg hne
  have hKL : K ≤ L := hK.sup_eq ▸ le_sup_right
  have hKfg : K.FG := FG.of_le hfg hKL
  have hKreg := IsOrthSum.isRegular_right Q hK hreg
  obtain ⟨l, hl2, hl, hρ⟩ := sym4_exists_list_two Q h2 hyL hQ hs hσ
  obtain ⟨σ', hσ'K, hfixK, hσeq⟩ := sym4_peel Q hQ hK hσ hfix l hl hρ
  obtain ⟨l', hl'1, hl', hσ'eq⟩ := sym4_aux Q h2 0 hKfg hKreg (by omega) hσ'K hfixK
  have hlist : σ = ((l ++ l').map (symmetryOrOne Q)).prod := by
    rw [List.map_append, List.prod_append, ← hσ'eq]; exact hσeq
  have hall : ∀ u ∈ l ++ l', IsSymVec Q L u := by
    intro u hu
    rcases List.mem_append.mp hu with h | h
    · exact hl u h
    · exact sym4_isSymVec_of_comp Q hK (hl' u h)
  by_cases hlen : (l ++ l').length ≤ 2
  · exact ⟨l ++ l', hlen, hall, hlist⟩
  · have hlen3 : (l ++ l').length = 3 := by rw [List.length_append] at hlen ⊢; omega
    have hQl : ∀ u ∈ l ++ l', Q u ≠ 0 := by
      intro u hu
      obtain ⟨-, hQ', -⟩ := hall u hu
      exact hQ'
    have hdet : LinearEquiv.det σ = -1 := by
      rw [hlist, det_symmetryOrOne_prod Q _ hQl, hlen3]; norm_num
    have hK0 : K ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hrkK; omega
    obtain ⟨k, K₂, hkK, hQk, hsk, hK₂, hrkK₂⟩ := sym4_exists_split Q h2 hKfg hKreg hK0
    have hK₂L : K₂ ≤ K := hK₂.sup_eq ▸ le_sup_right
    have hK₂fg : K₂.FG := FG.of_le hKfg hK₂L
    have := isTorsionFree_of_fractionRing (R := R) (F := F) (V := V)
    have : Module.Finite R K₂ := Module.Finite.iff_fg.mpr hK₂fg
    have hK₂0 : K₂ = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hLyk : L = R ∙ y ⊔ R ∙ k := by
      rw [← hK.sup_eq, ← hK₂.sup_eq, hK₂0, sup_bot_eq]
    have hyk : bil Q y k = 0 := hK.orth y (mem_span_singleton_self y) k hkK
    obtain ⟨u, hu, huL, hσu⟩ := binary_improper_symmetry Q hQ hQk hyk hLyk hσ hfix hdet
    refine ⟨[u], by simp, ?_, ?_⟩
    · intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      refine ⟨huL, hu, fun x hx => ?_⟩
      rw [← hσu]
      have : σ x ∈ latMap σ L := Submodule.mem_map_of_mem hx
      rwa [hσ.2] at this
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [sym4_symmetryOrOne_of_ne Q hu, hσu]

/-- The generalized statement of the footnote of 92:4, by induction on the rank starting at $2$. -/
theorem aux_two (h2 : IsUnit (2 : R)) [FiniteDimensional F V] (m : ℕ) :
    ∀ {L : Submodule R V}, L.FG → IsRegular Q L → finrank R L = m + 2 →
    ∀ {σ : V ≃ₗ[F] V}, σ ∈ orthLat Q L → (∀ x, (∀ z ∈ L, bil Q x z = 0) → σ x = x) →
    ∃ l : List V, l.length ≤ 2 * (m + 2) - 2 ∧ (∀ u ∈ l, IsSymVec Q L u) ∧
      σ = (l.map (symmetryOrOne Q)).prod := by
  induction m with
  | zero =>
    intro L hfg hreg hrk σ hσ hfix
    obtain ⟨l, hl, h1, h2'⟩ := aux_rank_two Q h2 hfg hreg (by omega) hσ hfix
    exact ⟨l, by omega, h1, h2'⟩
  | succ m ih =>
    intro L hfg hreg hrk σ hσ hfix
    have hne : L ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hrk; omega
    obtain ⟨y, K, hyL, hQ, hs, hK, hrkK⟩ := sym4_exists_split Q h2 hfg hreg hne
    have hKL : K ≤ L := hK.sup_eq ▸ le_sup_right
    have hKfg : K.FG := FG.of_le hfg hKL
    obtain ⟨l, hl2, hl, hρ⟩ := sym4_exists_list_two Q h2 hyL hQ hs hσ
    obtain ⟨σ', hσ'K, hfixK, hσeq⟩ := sym4_peel Q hQ hK hσ hfix l hl hρ
    have hKreg := IsOrthSum.isRegular_right Q hK hreg
    obtain ⟨l', hl'1, hl', hσ'eq⟩ := ih hKfg hKreg (by omega) hσ'K hfixK
    refine ⟨l ++ l', ?_, ?_, ?_⟩
    · rw [List.length_append]; omega
    · intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact hl u h
      · exact sym4_isSymVec_of_comp Q hK (hl' u h)
    · rw [List.map_append, List.prod_append, ← hσ'eq]; exact hσeq

end Sym2

section Hensel

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (ResidueField R)] [DecidableEq (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]

/-- **The valuation argument of 92:7/92:8.** Let $\pi$ be a prime of a complete discrete valuation ring with finite
residue field, $\pi \nmid 2$, and $S = \sum_i a_i^2\pi^{2d_i}$ with $d$ injective and $S \ne 0$. If $S$ divides every
$a_i\pi^{2d_i}$ then $S$ is a square in $R$. (The terms of smallest valuation $m$ force a unit coefficient and
$m = 2d_i$ by the divisibility; injectivity of $d$ makes this term unique, so $S \in \pi^{m}(a^2 + \pi R)$ and Hensel's
lemma finishes.) -/
theorem sq_of_dvd {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) {ι : Type*} [Fintype ι] (d : ι → ℕ)
    (hd : Function.Injective d) (a : ι → R) (hS : ∑ i, a i ^ 2 * π ^ (2 * d i) ≠ 0)
    (hdiv : ∀ i, (∑ j, a j ^ 2 * π ^ (2 * d j)) ∣ a i * π ^ (2 * d i)) :
    ∃ z : R, ∑ i, a i ^ 2 * π ^ (2 * d i) = z ^ 2 := by
  classical
  set v := IsDiscreteValuationRing.addVal R with hv
  set t : ι → R := fun i => a i ^ 2 * π ^ (2 * d i) with ht
  set S := ∑ i, t i with hSdef
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hS (by rw [hSdef]; simp)
  obtain ⟨i0, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun i => v (t i))
    (Finset.univ_nonempty)
  have hS_ne : v S ≠ ⊤ := fun h => hS (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
  have hmin_le : ∀ i, (∀ j, v (t i) ≤ v (t j)) → v (t i) ≤ v S := fun i hi =>
    v.map_le_sum (fun j _ => hi j)
  have hclaim : ∀ i, (∀ j, v (t i) ≤ v (t j)) → IsUnit (a i) ∧ v (t i) = ((2 * d i : ℕ) : ℕ∞) := by
    intro i hi
    have h1 : v (t i) ≤ v S := hmin_le i hi
    have h2' : v S ≤ v (a i * π ^ (2 * d i)) := IsDiscreteValuationRing.addVal_le_iff_dvd.mpr (hdiv i)
    have hai : a i ≠ 0 := by
      intro h0
      have : v (t i) = ⊤ := by simp [ht, h0]
      rw [this] at h1
      exact hS_ne (top_le_iff.mp h1)
    have hfin : v (a i) ≠ ⊤ := fun h => hai (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
    obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hfin
    have he2 : IsDiscreteValuationRing.addVal R (a i) = e := he.symm
    have hvt : v (t i) = ((2 * e + 2 * d i : ℕ) : ℕ∞) := by
      show IsDiscreteValuationRing.addVal R (a i ^ 2 * π ^ (2 * d i)) = _
      rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, hπ.addVal_pow, he2,
        nsmul_eq_mul]
      push_cast; ring
    have hva : v (a i * π ^ (2 * d i)) = ((e + 2 * d i : ℕ) : ℕ∞) := by
      show IsDiscreteValuationRing.addVal R (a i * π ^ (2 * d i)) = _
      rw [IsDiscreteValuationRing.addVal_mul, hπ.addVal_pow, he2]
      push_cast; ring
    have hle : ((2 * e + 2 * d i : ℕ) : ℕ∞) ≤ ((e + 2 * d i : ℕ) : ℕ∞) := by
      rw [← hvt, ← hva]; exact h1.trans h2'
    have he0 : e = 0 := by
      have := Nat.cast_le.mp hle
      omega
    subst he0
    refine ⟨IsDiscreteValuationRing.addVal_eq_zero_iff.mp (by rw [← hv]; simpa using he.symm), ?_⟩
    rw [hvt]; simp
  obtain ⟨hu0, hm0⟩ := hclaim i0 (fun j => hmin j (Finset.mem_univ j))
  have huniq : ∀ j, j ≠ i0 → ((2 * d i0 + 1 : ℕ) : ℕ∞) ≤ v (t j) := by
    intro j hj
    by_contra hlt
    push Not at hlt
    have h1 : v (t i0) ≤ v (t j) := hmin j (Finset.mem_univ j)
    have hfin : v (t j) ≠ ⊤ := ne_top_of_lt hlt
    obtain ⟨e', he'⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← he', hm0] at h1
    rw [← he'] at hlt
    have h1' := Nat.cast_le.mp h1
    have hlt' := Nat.cast_lt.mp hlt
    have hee : e' = 2 * d i0 := by omega
    have hjmin : ∀ j', v (t j) ≤ v (t j') := by
      intro j'
      rw [← he', hee, ← hm0]
      exact hmin j' (Finset.mem_univ j')
    obtain ⟨-, hmj⟩ := hclaim j hjmin
    rw [← he', hee] at hmj
    have := Nat.cast_injective hmj
    exact hj (hd (by omega))
  have hrest : π ^ (2 * d i0 + 1) ∣ ∑ j ∈ Finset.univ.erase i0, t j := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, hπ.addVal_pow]
    exact v.map_le_sum (fun j hj => huniq j (Finset.ne_of_mem_erase hj))
  obtain ⟨x, hx⟩ := hrest
  have hSdecomp : S = π ^ (2 * d i0) * (a i0 ^ 2 + π * x) := by
    rw [hSdef, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0), hx]
    simp only [ht]; ring
  have hπres : residue R π = 0 :=
    (residue_eq_zero_iff π).mpr ((IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit)
  have hres : residue R (a i0 ^ 2 + π * x) = (residue R (a i0)) ^ 2 := by
    simp [hπres]
  have hs0 : residue R (a i0) ≠ 0 := (hu0.map (residue R)).ne_zero
  obtain ⟨z, hz⟩ := Lattices.Nbr.exists_sq_eq_of_residue hπ h2 (a i0 ^ 2 + π * x) hs0 hres
  refine ⟨π ^ (d i0) * z, ?_⟩
  rw [hSdecomp, ← hz]; ring

end Hensel

section Lattice

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)
variable {ι : Type*} [Fintype ι]

variable (F) in
/-- The scaled vectors $g_i = \pi^{d_i} f_i$ ($d_i$ the exponents, $f_i$ an orthogonal family). -/
def gen (π : R) (d : ι → ℕ) (f : ι → V) (i : ι) : V := (algebraMap R F π) ^ d i • f i

variable (F) in
/-- **The lattice $L = \sum_i \mathfrak o\,\pi^{d_i} f_i$** of 92:7 and 92:8; for $f$ an orthogonal base with
$Q(f_i) = \varepsilon$ and $d_i = i$ it is $L \cong \langle\varepsilon\rangle \perp \langle\varepsilon\pi^2\rangle \perp \cdots
\perp \langle\varepsilon\pi^{2(n-1)}\rangle$. -/
def piLat (π : R) (d : ι → ℕ) (f : ι → V) : Submodule R V := span R (Set.range (gen F π d f))

theorem gen_mem (π : R) (d : ι → ℕ) (f : ι → V) (i : ι) : gen F π d f i ∈ piLat F π d f :=
  subset_span (Set.mem_range_self i)

theorem piLat_isLattice {π : R} (hπ : π ≠ 0) (d : ι → ℕ) {f : ι → V}
    (hspan : span F (Set.range f) = ⊤) : (piLat F π d f).IsLattice F := by
  refine ⟨fg_span (Set.finite_range _), ?_⟩
  have hϖ : algebraMap R F π ≠ 0 := fun h =>
    hπ (IsFractionRing.injective R F (h.trans (map_zero _).symm))
  rw [eq_top_iff, ← hspan, span_le]
  rintro _ ⟨i, rfl⟩
  have hg : gen F π d f i ∈ span F ((piLat F π d f : Submodule R V) : Set V) :=
    subset_span (gen_mem π d f i)
  have := Submodule.smul_mem (span F ((piLat F π d f : Submodule R V) : Set V))
    ((algebraMap R F π ^ d i)⁻¹) hg
  simpa [gen, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hϖ)] using this

theorem exists_coeff {π : R} {d : ι → ℕ} {f : ι → V} {y : V} (hy : y ∈ piLat F π d f) :
    ∃ a : ι → R, y = ∑ i, a i • gen F π d f i := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
  exact ⟨a, ha.symm⟩

theorem bil_gen_ne {π : R} {d : ι → ℕ} {f : ι → V} (hf : ∀ i j, i ≠ j → bil Q (f i) (f j) = 0)
    {i j : ι} (hij : i ≠ j) : bil Q (gen F π d f i) (gen F π d f j) = 0 := by
  simp only [gen, bil_smul_left, bil_smul_right, hf i j hij, mul_zero]

theorem Q_gen {π : R} (d : ι → ℕ) {f : ι → V} {ε : R} (hQf : ∀ i, Q (f i) = algebraMap R F ε)
    (i : ι) : Q (gen F π d f i) = algebraMap R F (ε * π ^ (2 * d i)) := by
  simp only [gen, Q_smul, hQf, map_mul, map_pow]; ring

theorem bil_sum_gen {π : R} {d : ι → ℕ} {f : ι → V} {ε : R}
    (hf : ∀ i j, i ≠ j → bil Q (f i) (f j) = 0) (hQf : ∀ i, Q (f i) = algebraMap R F ε)
    {y : V} {a : ι → R} (hy : y = ∑ i, a i • gen F π d f i) (j : ι) :
    bil Q y (gen F π d f j) = algebraMap R F (ε * (a j * π ^ (2 * d j))) := by
  rw [hy, bil_sum_left, Finset.sum_eq_single j]
  · rw [bil_rsmul_left, bil_self, Q_gen Q d hQf]; simp only [map_mul]; ring
  · intro i _ hij; rw [bil_rsmul_left, bil_gen_ne Q hf hij, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem Q_sum_gen {π : R} {d : ι → ℕ} {f : ι → V} {ε : R}
    (hf : ∀ i j, i ≠ j → bil Q (f i) (f j) = 0) (hQf : ∀ i, Q (f i) = algebraMap R F ε)
    {y : V} {a : ι → R} (hy : y = ∑ i, a i • gen F π d f i) :
    Q y = algebraMap R F (ε * ∑ i, a i ^ 2 * π ^ (2 * d i)) := by
  calc Q y = bil Q y y := (bil_self Q y).symm
    _ = bil Q y (∑ j, a j • gen F π d f j) := by rw [← hy]
    _ = ∑ j, algebraMap R F (a j) * bil Q y (gen F π d f j) := by
        rw [bil_sum_right]; exact Finset.sum_congr rfl fun j _ => bil_rsmul_right Q (a j) y _
    _ = _ := by
        rw [Finset.mul_sum, map_sum]
        exact Finset.sum_congr rfl fun j _ => by
          rw [bil_sum_gen Q hf hQf hy j, ← map_mul]; congr 1; ring

end Lattice

section LatticeLocal

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (ResidueField R)] [DecidableEq (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)
variable {ι : Type*} [Fintype ι]

/-- **Symmetries of $L = \sum \mathfrak o\pi^{d_i}f_i$ have spinor norm $\varepsilon F^{\times 2}$** (the core of 92:7
and 92:8): if $f_i$ are orthogonal with $Q(f_i) = \varepsilon$ a unit, the exponents $d_i$ are distinct, and
$\tau_u \in O(L)$, then $Q(u) \in \varepsilon F^{\times 2}$. (Write $u = ty$ with $y$ maximal in $L$ and
$y = \sum a_i\pi^{d_i}f_i$; by 92:6 / §91B, $2B(y, L) \subseteq Q(y)\mathfrak o$ gives
$S := \sum a_i^2\pi^{2d_i}$ divides each $a_i\pi^{2d_i}$ and `sq_of_dvd` shows $S$ is a square, $Q(y) = \varepsilon S$.) -/
theorem sq_class_of_symmetry (h2 : IsUnit (2 : R)) {π : R} (hπ : Irreducible π) {d : ι → ℕ}
    (hd : Function.Injective d) {f : ι → V} (hf : ∀ i j, i ≠ j → bil Q (f i) (f j) = 0) {ε : R}
    (hε : IsUnit ε) (hQf : ∀ i, Q (f i) = algebraMap R F ε) (hspan : span F (Set.range f) = ⊤)
    {u : V} (hu : Q u ≠ 0) (hτ : symmetry Q u hu ∈ orthLat Q (piLat F π d f)) :
    ∃ s : F, s ≠ 0 ∧ Q u = algebraMap R F ε * s ^ 2 := by
  have hlat := piLat_isLattice (F := F) hπ.ne_zero d hspan
  have h2' : ¬ π ∣ 2 := fun h => hπ.not_isUnit (isUnit_of_dvd_unit h h2)
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (map_zero Q)
  have huL : u ∈ span F ((piLat F π d f : Submodule R V) : Set V) := by
    rw [hlat.span_eq_top]; exact mem_top
  obtain ⟨y, hy, t, ht, rfl⟩ := exists_isMaxVec_smul hlat.fg hu0 huL
  have hQy : Q y ≠ 0 := by intro h; apply hu; rw [Q_smul, h, mul_zero]
  rw [symmetry_smul_eq' Q ht hQy hu] at hτ
  have hcrit := (symmetry_mem_orthLat_iff Q hQy hy).mp hτ
  obtain ⟨a, hya⟩ := exists_coeff hy.1
  have hQ := Q_sum_gen Q hf hQf hya
  have hS0 : ∑ i, a i ^ 2 * π ^ (2 * d i) ≠ 0 := by
    intro h; apply hQy; rw [hQ, h, mul_zero, map_zero]
  have hdiv : ∀ j, (∑ i, a i ^ 2 * π ^ (2 * d i)) ∣ a j * π ^ (2 * d j) := by
    intro j
    obtain ⟨r, hr⟩ := mem_span_singleton.mp (hcrit (gen F π d f j) (gen_mem π d f j))
    rw [bil_sum_gen Q hf hQf hya j, Algebra.smul_def, hQ] at hr
    have hr' : r * (ε * ∑ i, a i ^ 2 * π ^ (2 * d i)) = 2 * (ε * (a j * π ^ (2 * d j))) := by
      apply IsFractionRing.injective R F
      simp only [map_mul, map_ofNat] at hr ⊢
      linear_combination hr
    have hεS : ε * ((∑ i, a i ^ 2 * π ^ (2 * d i)) * r) = ε * (2 * (a j * π ^ (2 * d j))) := by
      linear_combination hr'
    have h3 := mul_left_cancel₀ hε.ne_zero hεS
    exact (h2.dvd_mul_left).mp ⟨r, h3.symm⟩
  obtain ⟨z, hz⟩ := sq_of_dvd hπ h2' d hd a hS0 hdiv
  have hQu : Q (t • y) = algebraMap R F ε * (t * algebraMap R F z) ^ 2 := by
    rw [Q_smul, hQ, hz]; simp only [map_mul, map_pow]; ring
  refine ⟨t * algebraMap R F z, ?_, hQu⟩
  intro h0
  apply hu
  rw [hQu, h0]; ring

/-- **Every element of $O(L)$ has spinor norm $\varepsilon^k$ with $\det = (-1)^k$** (92:4 + `sq_class_of_symmetry`):
for $L = \sum \mathfrak o\pi^{d_i}f_i$ as in `sq_class_of_symmetry` on a regular space of positive dimension, each
$\sigma \in O(L)$ is a product of $k$ symmetries in $O(L)$, each of spinor norm in $\varepsilon F^{\times 2}$. -/
theorem exists_hasSpinorNorm_pow (h2 : IsUnit (2 : R)) [FiniteDimensional F V]
    (hV : (QuadraticMap.associated Q).Nondegenerate) (hn : 1 ≤ finrank F V) {π : R}
    (hπ : Irreducible π) {d : ι → ℕ} (hd : Function.Injective d) {f : ι → V}
    (hf : ∀ i j, i ≠ j → bil Q (f i) (f j) = 0) {ε : R} (hε : IsUnit ε)
    (hQf : ∀ i, Q (f i) = algebraMap R F ε) (hspan : span F (Set.range f) = ⊤) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ orthLat Q (piLat F π d f)) :
    ∃ k : ℕ, HasSpinorNorm Q σ (algebraMap R F ε ^ k) ∧ LinearEquiv.det σ = (-1 : Fˣ) ^ k := by
  have hlat := piLat_isLattice (F := F) hπ.ne_zero d hspan
  obtain ⟨l, -, hl, hσl⟩ := exists_symmetry_list Q h2 hV hn hlat hσ
  have hQl : ∀ u ∈ l, Q u ≠ 0 := fun u hu => by
    obtain ⟨hu', -⟩ := hl u hu
    exact hu'
  have hnorm : ∀ u ∈ l, ∃ s : F, s ≠ 0 ∧ Q u = algebraMap R F ε * s ^ 2 := fun u hu => by
    obtain ⟨hu', hτ⟩ := hl u hu
    exact sq_class_of_symmetry Q h2 hπ hd hf hε hQf hspan hu' hτ
  have hprod : ∀ l' : List V, (∀ u ∈ l', ∃ s : F, s ≠ 0 ∧ Q u = algebraMap R F ε * s ^ 2) →
      ∃ s : F, s ≠ 0 ∧ (l'.map Q).prod = algebraMap R F ε ^ l'.length * s ^ 2 := by
    intro l' h
    induction l' with
    | nil => exact ⟨1, one_ne_zero, by simp⟩
    | cons u l' ih =>
      obtain ⟨s1, hs1, h1⟩ := h u (by simp)
      obtain ⟨s2, hs2, h2'⟩ := ih fun v hv => h v (by simp [hv])
      refine ⟨s1 * s2, mul_ne_zero hs1 hs2, ?_⟩
      rw [List.map_cons, List.prod_cons, h1, h2', List.length_cons]; ring
  obtain ⟨s, hs, hp⟩ := hprod l hnorm
  refine ⟨l.length, ⟨l, hQl, ?_, s, hs, hp⟩, ?_⟩
  · rw [hσl]
    have : (l.attach.map fun u => symmetry Q u.1 (hQl u.1 u.2)) =
        l.attach.map fun u => symmetryOrOne Q u.1 :=
      List.map_congr_left fun u _ => (sym4_symmetryOrOne_of_ne Q _).symm
    rw [this]
    simp
  · rw [hσl, det_symmetryOrOne_prod Q l hQl]

end LatticeLocal

end Gap92

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Theorem 92:4, footnote** (O'Meara 1963, p. 248, footnote): "Starting the induction at $n = 2$ will show that at
most $2n - 2$ symmetries are needed when $n \ge 2$." Let $L$ be a lattice on a regular $n$-ary quadratic space $V$
over a non-dyadic local field, $n \ge 2$. Then every element of $O(L)$ is a product of at most $2n - 2$ symmetries in
$O(L)$: $\sigma = \tau_{u_1}\cdots\tau_{u_k}$ with $k \le 2n - 2$, each $Q(u_j) \ne 0$ and each $\tau_{u_j} \in O(L)$.

*Proof* (as in the footnote). The induction of `exists_symmetry_list` (two symmetries per dimension) is started at
$n = 2$. For a binary lattice $L = \mathfrak o y \perp \mathfrak o k$ with $\mathfrak sL = Q(y)\mathfrak o$, one or two
symmetries $\rho$ of $O(L)$ carry $y$ to $\sigma y$, and $\rho^{-1}\sigma$ fixes $y$ and is $\pm 1$ on $\mathfrak ok$:
if $+1$, $\sigma = \rho$; if $-1$ and $\rho$ is a single symmetry, $\sigma = \rho\tau_k$; if $-1$ and $\rho$ is a
product of two symmetries then $\sigma$ is improper, hence a single symmetry (an improper isometry of a regular binary
space is a symmetry, `Gap92.binary_improper_symmetry`), namely $\sigma$ itself, which lies in $O(L)$.
(Only the discrete valuation ring and $2 \in \mathfrak u$ are used.) -/
@[kb "omeara1963" "§92, 92:4, p. 248, footnote (2n − 2 symmetries for n ≥ 2)"]
theorem exists_symmetry_list_of_two_le (h2 : IsUnit (2 : R)) [FiniteDimensional F V]
    (hV : (QuadraticMap.associated Q).Nondegenerate) (hn : 2 ≤ finrank F V) {L : Submodule R V}
    (hL : L.IsLattice F) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orthLat Q L) :
    ∃ l : List V, l.length ≤ 2 * finrank F V - 2 ∧
      (∀ u ∈ l, ∃ hu : Q u ≠ 0, symmetry Q u hu ∈ orthLat Q L) ∧ σ = (l.map (symmetryOrOne Q)).prod := by
  have hfg := hL.fg
  have hbil : ∀ x, (∀ z ∈ L, bil Q x z = 0) → x = 0 := by
    intro x hx
    have hBV : ∀ y : V, bil Q x y = 0 := by
      intro y
      have hy : y ∈ span F (L : Set V) := hL.span_eq_top ▸ mem_top
      refine span_induction (p := fun y _ => bil Q x y = 0) ?_ (by simp [bil]) ?_ ?_ hy
      · intro y hy; exact hx y hy
      · intro a b _ _ ha hb; rw [bil_add_right, ha, hb, add_zero]
      · intro c a _ ha; rw [bil_smul_right, ha, mul_zero]
    exact hV.1 x hBV
  have hreg : IsRegular Q L := fun x _ hx => hbil x hx
  have hrank : finrank R L = finrank F V :=
    Module.finrank_eq_of_rank_eq
      ((Submodule.IsLattice.rank' F L).trans (Module.finrank_eq_rank F V).symm)
  obtain ⟨m, hm⟩ : ∃ m, finrank R L = m + 2 := ⟨finrank R L - 2, by omega⟩
  obtain ⟨l, hl, hu, hσl⟩ := Gap92.aux_two Q h2 m hfg hreg hm hσ
    (fun x hx => by rw [hbil x hx, map_zero])
  refine ⟨l, by omega, fun u hu' => ?_, hσl⟩
  obtain ⟨-, hQ, hτ⟩ := hu u hu'
  exact ⟨hQ, symmetry_mem_orthLat_of_le Q hQ hτ⟩

end Main

section MainLocal

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (ResidueField R)] [DecidableEq (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Example 92:7** (O'Meara 1963, p. 249): let $V$ be a regular quadratic space over a non-dyadic local field with
$dV = 1$ and $S_{\mathfrak p}V = 1$. Then there is a lattice $L$ on $V$ with $\theta(O(L)) = \dot F^2$: every
$\sigma \in O(L)$ has spinor norm $\dot F^2$, i.e. every `c` with `HasSpinorNorm Q σ c` (a spinor norm of $\sigma$ through
some factorization into symmetries) is a square in $F$ (and `c ≠ 0` by `HasSpinorNorm.ne_zero`); that $\sigma$ has
the spinor norm $1$ is `Gap92.exists_hasSpinorNorm_pow` with $\varepsilon = 1$.

*Hypothesis.* There is no Hasse symbol $S_{\mathfrak p}$ for abstract spaces in this library, so "$dV = 1$ and
$S_{\mathfrak p}V = 1$, which by 63:20 means $V \cong \langle 1\rangle \perp \cdots \perp \langle 1\rangle$, the form
used here" is stated as its consequence used in the first line of the book's proof: $V$ has an orthogonal base
$e_0, \dots, e_{n-1}$ with $Q(e_i) = 1$ (`he`, `hQ`); $V$ is then automatically regular (`hV` is a convenience
hypothesis for the library's lemmas, implied by the base).

*Proof* (as in the book). $L = \sum_i \mathfrak o\pi^i e_i \cong \langle 1\rangle \perp \langle\pi^2\rangle \perp \cdots
\perp \langle\pi^{2(n-1)}\rangle$. A symmetry $\tau_u \in O(L)$ has $u = ty$ with $y$ maximal and $\mathfrak oy$ splitting
$L$ (92:6), and then $Q(y) \in \pi^{2i}\mathfrak u^2$ (here proved directly from $2B(y, L) \subseteq Q(y)\mathfrak o$ and
Hensel's lemma, `Gap92.sq_of_dvd`, in place of 92:2 on the Jordan splittings), so all symmetries in $O(L)$ have
spinor norm $\dot F^2$; by 92:4 (`exists_symmetry_list`) and the independence of the spinor norm of the factorization
(`HasSpinorNorm.eq_mul_sq`, 55:1) all of $O(L)$ does. -/
@[kb "omeara1963" "§92, 92:7, p. 249"]
theorem exists_lattice_spinorNorm_square (h2 : IsUnit (2 : R)) [FiniteDimensional F V]
    (hV : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ} (e : Module.Basis (Fin n) F V)
    (he : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0) (hQ : ∀ i, Q (e i) = 1) :
    ∃ L : Submodule R V, L.IsLattice F ∧
      ∀ σ ∈ orthLat Q L, ∀ c : F, HasSpinorNorm Q σ c → IsSquare c := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hQf : ∀ i, Q (e i) = algebraMap R F 1 := fun i => by rw [hQ, map_one]
  have hspan : span F (Set.range e) = ⊤ := e.span_eq
  refine ⟨Gap92.piLat F π (fun i : Fin n => i.val) e,
    Gap92.piLat_isLattice hπ.ne_zero _ hspan, ?_⟩
  intro σ hσ c hc
  have hfr : finrank F V = n := by rw [Module.finrank_eq_card_basis e, Fintype.card_fin]
  by_cases hn : 1 ≤ finrank F V
  · obtain ⟨k, hk, -⟩ := Gap92.exists_hasSpinorNorm_pow Q h2 hV hn hπ Fin.val_injective he isUnit_one
      hQf hspan hσ
    obtain ⟨s, -, hs⟩ := HasSpinorNorm.eq_mul_sq Q hV hc hk
    exact ⟨s, by rw [hs]; simp [_root_.sq]⟩
  · have hn0 : n = 0 := by omega
    subst hn0
    have hsub : ∀ x : V, x = 0 := fun x => by rw [← e.sum_repr x]; simp
    have hσ1 : σ = 1 := LinearEquiv.ext fun x => by rw [hsub x, map_zero]; rfl
    obtain ⟨s, -, hs⟩ := HasSpinorNorm.eq_mul_sq Q hV hc (by rw [hσ1]; exact HasSpinorNorm.one Q)
    exact ⟨s, by rw [hs]; simp [_root_.sq]⟩

/-- **Example 92:8** (O'Meara 1963, p. 250): suppose $V$ satisfies the conditions of Example 92:7 (an orthogonal base
$e_0, \dots, e_{n-1}$ with $Q(e_i) = 1$, i.e. $V \cong \langle 1\rangle \perp \cdots \perp \langle 1\rangle$) and
$\dim V$ is even. Let $\varepsilon$ be any unit in $\mathfrak o$. Then there is a lattice $L$ on $V$ with
$\theta(O^-(L)) = \varepsilon\dot F^2$: $O(L)$ contains an improper unit ($\det\sigma = -1$), and for every improper
$\sigma \in O(L)$ every spinor norm `c` of $\sigma$ (`HasSpinorNorm Q σ c`) lies in $\varepsilon F^{\times 2}$.
(No proof in the book.)

*Extra hypothesis.* `0 < finrank F V` ($V \ne 0$, hence $\dim V \ge 2$): for $V = 0$ the group $O(L)$ is trivial and
the statement (existence of an improper unit) is false.

*Proof.* Since $n = 2m$, group the base in pairs: with $a^2 + b^2 = \varepsilon$ ($a, b \in \mathfrak o$, from the binary
step `exists_binary_one` for the units $\varepsilon^{-1}, \varepsilon^{-1}$), the vectors $f_{2p} = ae_{2p} + be_{2p+1}$,
$f_{2p+1} = -be_{2p} + ae_{2p+1}$ are orthogonal with $Q(f_i) = \varepsilon$ and span $V$ (i.e.
$\langle 1, 1\rangle \cong \langle\varepsilon,\varepsilon\rangle$, so $V \cong \langle\varepsilon\rangle^n$ because
$\varepsilon^n \in \dot F^2$). Take $L = \sum_i \mathfrak o\pi^i f_i$ (indices in the order of the pairs). Then
$\tau_{f_0} \in O(L)$ is improper, and by `Gap92.exists_hasSpinorNorm_pow` every $\sigma \in O(L)$ is a product of $k$
symmetries of spinor norm in $\varepsilon F^{\times 2}$ with $\det\sigma = (-1)^k$; improper means $k$ odd, so the spinor
norm is $\varepsilon^k \in \varepsilon F^{\times 2}$. -/
@[kb "omeara1963" "§92, 92:8, p. 250"]
theorem exists_lattice_improper_spinorNorm (h2 : IsUnit (2 : R)) [FiniteDimensional F V]
    (hV : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ} (e : Module.Basis (Fin n) F V)
    (he : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0) (hQ : ∀ i, Q (e i) = 1)
    (hev : Even (finrank F V)) (hpos : 0 < finrank F V) {ε : R} (hε : IsUnit ε) :
    ∃ L : Submodule R V, L.IsLattice F ∧ (∃ σ ∈ orthLat Q L, LinearEquiv.det σ = -1) ∧
      ∀ σ ∈ orthLat Q L, LinearEquiv.det σ = -1 → ∀ c : F, HasSpinorNorm Q σ c →
        ∃ s : F, s ≠ 0 ∧ c = algebraMap R F ε * s ^ 2 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hfr : finrank F V = n := by rw [Module.finrank_eq_card_basis e, Fintype.card_fin]
  obtain ⟨m, hm⟩ := hev
  have hnm : n = m + m := by omega
  subst hnm
  have hm1 : 1 ≤ m := by omega
  have hE : algebraMap R F ε ≠ 0 := (hε.map (algebraMap R F)).ne_zero
  -- the pairs
  obtain ⟨s, t, hst⟩ := exists_binary_one (F := F) h2 (hε.unit⁻¹).isUnit (hε.unit⁻¹).isUnit
  have hab : s ^ 2 + t ^ 2 = ε := by
    have h1 := hε.unit.mul_inv
    rw [hε.unit_spec] at h1
    linear_combination ε * hst - (s ^ 2 + t ^ 2) * h1
  set A : F := algebraMap R F s with hA
  set B : F := algebraMap R F t with hB
  have hAB : A ^ 2 + B ^ 2 = algebraMap R F ε := by
    rw [← hab, hA, hB]; simp
  obtain ⟨e2, he2def⟩ : ∃ e2 : Fin m ⊕ Fin m → V, e2 = fun x => e (finSumFinEquiv x) := ⟨_, rfl⟩
  have he2 : ∀ x y, x ≠ y → bil Q (e2 x) (e2 y) = 0 := by
    intro x y hxy
    rw [he2def]
    exact he _ _ (fun h => hxy (finSumFinEquiv.injective h))
  have hQ2 : ∀ x, Q (e2 x) = 1 := fun x => by rw [he2def]; exact hQ _
  have hB2 : ∀ x y, bil Q (e2 x) (e2 y) = if x = y then 1 else 0 := by
    intro x y
    by_cases hxy : x = y
    · subst hxy; rw [bil_self, hQ2]; simp
    · rw [he2 x y hxy]; simp [hxy]
  obtain ⟨f, hfl, hfr'⟩ : ∃ f : Fin m ⊕ Fin m → V,
      (∀ p, f (Sum.inl p) = A • e2 (Sum.inl p) + B • e2 (Sum.inr p)) ∧
      (∀ p, f (Sum.inr p) = (-B) • e2 (Sum.inl p) + A • e2 (Sum.inr p)) :=
    ⟨Sum.elim (fun p => A • e2 (Sum.inl p) + B • e2 (Sum.inr p))
      (fun p => (-B) • e2 (Sum.inl p) + A • e2 (Sum.inr p)), fun p => rfl, fun p => rfl⟩
  have hpair : ∀ (α β γ δ : F) (x x' y y' : Fin m ⊕ Fin m),
      bil Q (α • e2 x + β • e2 x') (γ • e2 y + δ • e2 y') =
        α * γ * bil Q (e2 x) (e2 y) + α * δ * bil Q (e2 x) (e2 y') +
        β * γ * bil Q (e2 x') (e2 y) + β * δ * bil Q (e2 x') (e2 y') := by
    intro α β γ δ x x' y y'
    simp only [bil_add_left, bil_add_right, bil_smul_left, bil_smul_right]; ring
  have hLR : ∀ p q, bil Q (f (Sum.inl p)) (f (Sum.inr q)) = 0 := by
    intro p q
    rw [hfl, hfr', hpair]
    by_cases hpq : p = q
    · subst hpq; simp [hB2]; ring
    · simp [hB2, hpq]
  have hf : ∀ x y, x ≠ y → bil Q (f x) (f y) = 0 := by
    rintro (p | p) (q | q) hxy
    · have hpq : p ≠ q := fun h => hxy (by rw [h])
      rw [hfl, hfl, hpair]; simp [hB2, hpq]
    · exact hLR p q
    · rw [bil_comm]; exact hLR q p
    · have hpq : p ≠ q := fun h => hxy (by rw [h])
      rw [hfr', hfr', hpair]; simp [hB2, hpq]
  have hQf : ∀ x, Q (f x) = algebraMap R F ε := by
    rintro (p | p)
    · rw [hfl, Gap92.Q_pair Q (he2 _ _ Sum.inl_ne_inr), hQ2, hQ2]; linear_combination hAB
    · rw [hfr', Gap92.Q_pair Q (he2 _ _ Sum.inl_ne_inr), hQ2, hQ2]; linear_combination hAB
  have hspan : span F (Set.range f) = ⊤ := by
    rw [eq_top_iff, ← e.span_eq, span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
    have hxe : e (finSumFinEquiv x) = e2 x := by rw [he2def]
    rw [hxe]
    have hmemL : ∀ p, f (Sum.inl p) ∈ span F (Set.range f) := fun p => subset_span ⟨_, rfl⟩
    have hmemR : ∀ p, f (Sum.inr p) ∈ span F (Set.range f) := fun p => subset_span ⟨_, rfl⟩
    rcases x with p | p
    · have hl : A • f (Sum.inl p) - B • f (Sum.inr p) = (algebraMap R F ε) • e2 (Sum.inl p) := by
        rw [hfl, hfr', ← hAB]; module
      have : e2 (Sum.inl p) = (algebraMap R F ε)⁻¹ • (A • f (Sum.inl p) - B • f (Sum.inr p)) := by
        rw [hl, inv_smul_smul₀ hE]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ (hmemL p))
        (Submodule.smul_mem _ _ (hmemR p)))
    · have hl : B • f (Sum.inl p) + A • f (Sum.inr p) = (algebraMap R F ε) • e2 (Sum.inr p) := by
        rw [hfl, hfr', ← hAB]; module
      have : e2 (Sum.inr p) = (algebraMap R F ε)⁻¹ • (B • f (Sum.inl p) + A • f (Sum.inr p)) := by
        rw [hl, inv_smul_smul₀ hE]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (hmemL p))
        (Submodule.smul_mem _ _ (hmemR p)))
  obtain ⟨d, hdd⟩ : ∃ d : Fin m ⊕ Fin m → ℕ, d = fun x => (finSumFinEquiv x).val := ⟨_, rfl⟩
  have hd : Function.Injective d := by
    intro x y h
    rw [hdd] at h
    exact finSumFinEquiv.injective (Fin.ext h)
  have hlat := Gap92.piLat_isLattice (F := F) hπ.ne_zero d hspan
  refine ⟨Gap92.piLat F π d f, hlat, ?_, ?_⟩
  · -- the improper unit τ_{f i0}
    set i0 : Fin m ⊕ Fin m := Sum.inl ⟨0, hm1⟩ with hi0
    have hd0 : d i0 = 0 := by rw [hdd]; simp [hi0]
    have hgen : Gap92.gen F π d f i0 = f i0 := by simp [Gap92.gen, hd0]
    have hu0 : Q (f i0) ≠ 0 := by rw [hQf]; exact hE
    have hτ : symmetry Q (f i0) hu0 ∈ orthLat Q (Gap92.piLat F π d f) := by
      refine symmetry_mem_orthLat_of_le Q hu0 (fun x hx => ?_)
      obtain ⟨a, hxa⟩ := Gap92.exists_coeff hx
      have hb := Gap92.bil_sum_gen Q hf hQf hxa i0
      rw [hgen, hd0] at hb
      rw [symmetry_apply, hb, hQf i0]
      have : 2 * algebraMap R F (ε * (a i0 * π ^ (2 * 0))) / algebraMap R F ε =
          algebraMap R F (2 * a i0) := by
        simp only [mul_zero, pow_zero, mul_one, map_mul, map_ofNat]
        field_simp
      rw [this, algebraMap_smul]
      refine Submodule.sub_mem _ hx (Submodule.smul_mem _ _ ?_)
      rw [← hgen]; exact Gap92.gen_mem π d f i0
    exact ⟨_, hτ, det_symmetry Q hu0⟩
  · intro σ hσ hdet c hc
    obtain ⟨k, hk, hdk⟩ := Gap92.exists_hasSpinorNorm_pow Q h2 hV hpos hπ hd hf hε hQf hspan hσ
    have hodd : Odd k :=
      (neg_one_pow_eq_neg_one_iff_odd (Gap92.neg_one_ne_one_of_two (F := F))).mp (hdk.symm.trans hdet)
    obtain ⟨r, hr⟩ := hodd
    obtain ⟨s', hs0, hs⟩ := HasSpinorNorm.eq_mul_sq Q hV hc hk
    refine ⟨algebraMap R F ε ^ r * s', mul_ne_zero (pow_ne_zero _ hE) hs0, ?_⟩
    rw [hs, hr]; ring

end MainLocal

end QuadFormsKB.OMeara
