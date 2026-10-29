import QuadFormsKB.Literature.OMeara.Sec43A

/-!
# O'Meara §43E: isometries fixing all anisotropic lines, and the center of $O(V)$ (43:11, 43:12, 43:12a)

**Setting** (as in `Sec43A.lean`): $F$ a field with $2 \ne 0$, $(V, Q)$ a finite-dimensional regular quadratic space
(`(QuadraticMap.associated Q).Nondegenerate`), $B$ = `bil Q`, $O(V)$ = `orth Q`, $\tau_u$ = `symmetry Q u hu`.
O'Meara's exceptional space is a hyperbolic plane over a field of three elements; it is excluded by the hypothesis
`¬ (finrank F V = 2 ∧ (∃ x, x ≠ 0 ∧ Q x = 0) ∧ Nat.card F = 3)` (a regular isotropic binary space is a hyperbolic
plane by 42:9).

**Proves** (O'Meara 1973 printing, Chapter IV, §43E, pp. 109–110):
* `eq_one_or_neg_of_forall_aniso_line` (**43:11**): an isometry that leaves every anisotropic line fixed is $\pm 1_V$,
  unless $V$ is the exceptional space;
* `mem_center_iff` (**43:12**): outside the exceptional case, $\sigma \in O(V)$ commutes with all of $O(V)$ iff
  $\sigma = \pm 1_V$, i.e. $Z_n = \{\pm 1_V\}$;
* `not_commutative_of_two_le` and `commutative_of_finrank_eq_one` (**43:12a**, outside the exceptional case): $O(V)$ is
  not commutative when $n \ge 2$, and is commutative when $n = 1$.

**Proof notes.** For an isotropic $x \ne 0$ with a hyperbolic partner $y$ ($Q(y) = 0$, $B(x, y) = 1$), the vectors
$x + ty$ ($t \ne 0$) are anisotropic. If $F$ has an element $a \notin \{0, \pm 1\}$, the three lines through $x \pm y$
and $x + ay$ force $\sigma x \in Fx$ (this replaces O'Meara's count of anisotropic lines in the binary case and covers
every $n \ge 2$). If $n \ge 3$ we follow O'Meara: with an anisotropic $z \perp x, y$, the planes $Fx + Fy$ and
$Fx + F(y+z)$ are spanned by anisotropic lines, so $\sigma x$ lies in both, hence in $Fx$. Then 43:9 applies. The
exceptional case of 43:12 ($Z_n = O_n$ of order 4) and of 43:12a are not formalized.

**Conventions.** $\pm 1_V$ is stated pointwise. Commutation is stated as $\sigma\rho = \rho\sigma$ in
`V ≃ₗ[F] V`.
-/

open QuadraticMap Submodule Module LinearMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Sec43E

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)

/-- A field with $2 \ne 0$ and not of three elements has an element $a \notin \{0, 1, -1\}$. -/
theorem exists_ne_zero_mul_self_ne_one (h3 : Nat.card F ≠ 3) : ∃ a : F, a ≠ 0 ∧ a * a ≠ 1 := by
  classical
  by_contra h
  push Not at h
  apply h3
  have hmem : ∀ a : F, a ∈ ({0, 1, -1} : Finset F) := by
    intro a
    by_cases ha : a = 0
    · simp [ha]
    · rcases mul_self_eq_one_iff.1 (h a ha) with rfl | rfl <;> simp
  have h1 : (1 : F) ≠ -1 := fun h => iv_two_ne (by linear_combination h)
  rw [← Nat.card_congr (Equiv.subtypeUnivEquiv hmem), Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_insert_of_notMem (by simp [(neg_ne_zero.2 one_ne_zero).symm]),
    Finset.card_pair h1]

theorem Q_add_smul_of_pair {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1) (t : F) :
    Q (x + t • y) = 2 * t := by
  rw [Q_add, Q_smul, hx, hy, bil_smul_right, hxy]; ring

theorem linearIndependent_pair_of_hyp {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1) :
    LinearIndependent F ![x, y] := by
  apply linearIndependent_of_det_gram_ne_zero (R := F) Q
  rw [Matrix.det_fin_two]
  simp [gram, hx, hy, hxy, bil_comm Q y x]

/-- Case $F \ne \mathbb F_3$: an isometry fixing the anisotropic lines $F(x \pm y)$, $F(x + ay)$ fixes $Fx$. -/
theorem mem_line_of_three_lines {σ : V ≃ₗ[F] V} {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1)
    {a : F} (ha0 : a ≠ 0) (ha1 : a * a ≠ 1) (h : ∀ v, Q v ≠ 0 → ∃ c : F, σ v = c • v) :
    ∃ c : F, σ x = c • x := by
  have hQ : ∀ t : F, t ≠ 0 → Q (x + t • y) ≠ 0 := fun t ht => by
    rw [Q_add_smul_of_pair Q hx hy hxy]; exact mul_ne_zero iv_two_ne ht
  obtain ⟨α, e1⟩ := h _ (hQ 1 one_ne_zero)
  obtain ⟨β, e2⟩ := h _ (hQ (-1) (neg_ne_zero.2 one_ne_zero))
  obtain ⟨γ, e3⟩ := h _ (hQ a ha0)
  simp only [map_add, map_smul] at e1 e2 e3
  have hli := LinearIndependent.pair_iff.1 (linearIndependent_pair_of_hyp Q hx hy hxy)
  have hc := hli ((1 + a) * α + (1 - a) * β - 2 * γ) ((1 + a) * α - (1 - a) * β - 2 * γ * a) (by
    linear_combination (norm := module) (2 : F) • e3 - (1 + a) • e1 - (1 - a) • e2)
  have hαβ : α = β := by
    have : (1 - a * a) * (α - β) = 0 := by linear_combination hc.2 - a * hc.1
    have := (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm ha1))
    exact sub_eq_zero.1 this
  subst hαβ
  refine ⟨α, ?_⟩
  have h2 : (2 : F) • σ x = (2 : F) • (α • x) := by linear_combination (norm := module) e1 + e2
  exact smul_right_injective V iv_two_ne h2

/-- In a regular space of dimension $\ge 3$, a hyperbolic pair $x, y$ has an anisotropic vector orthogonal to both. -/
theorem exists_aniso_orth_pair (hQ : (QuadraticMap.associated Q).Nondegenerate) (h3 : 3 ≤ finrank F V)
    {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1) :
    ∃ z, Q z ≠ 0 ∧ bil Q x z = 0 ∧ bil Q y z = 0 := by
  set S := Submodule.span F (Set.range ![x, y])
  set W := LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) S
  have hmemW : ∀ w, w ∈ W ↔ bil Q x w = 0 ∧ bil Q y w = 0 := by
    intro w
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      exact ⟨h x (Submodule.subset_span ⟨0, rfl⟩), h y (Submodule.subset_span ⟨1, rfl⟩)⟩
    · rintro ⟨h1, h2⟩ n hn
      refine Submodule.span_induction (p := fun n _ => QuadraticMap.associated Q n w = 0) ?_ ?_ ?_ ?_ hn
      · rintro _ ⟨i, rfl⟩; fin_cases i
        · exact h1
        · exact h2
      · simp
      · intro a b _ _ ha hb; rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      · intro c a _ ha; rw [map_smul, LinearMap.smul_apply, ha, smul_zero]
  have hW : 1 ≤ finrank F W := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal hQ S
    have h2 : finrank F S ≤ 2 := by
      have := finrank_range_le_card (R := F) (b := ![x, y])
      exact le_trans this (by simp)
    rw [h1]
    exact Nat.le_sub_of_add_le (by omega)
  obtain ⟨w, hwW, hw0⟩ : ∃ w ∈ W, w ≠ 0 := by
    have : W ≠ ⊥ := fun h => by rw [h, finrank_bot] at hW; omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot this
  by_contra hno
  push Not at hno
  have hiso : ∀ z, bil Q x z = 0 → bil Q y z = 0 → Q z = 0 := fun z h1 h2 => by
    by_contra hz; exact hz (hno z hz h1 |> fun h => absurd h2 h) |>.elim
  apply hw0
  refine hQ.1 w fun v => ?_
  set p := v - bil Q v y • x - bil Q v x • y
  have hpx : bil Q x p = 0 := by
    simp only [p, bil_sub_right, bil_smul_right, bil_self, hx, hxy, bil_comm Q x v]; ring
  have hpy : bil Q y p = 0 := by
    simp only [p, bil_sub_right, bil_smul_right, bil_self, hy, bil_comm Q y x, hxy, bil_comm Q y v]; ring
  obtain ⟨hwx, hwy⟩ := (hmemW w).1 hwW
  have hwp : bil Q w p = 0 := by
    have h := Q_add Q w p
    rw [hiso w hwx hwy, hiso p hpx hpy,
      hiso (w + p) (by rw [bil_add_right, hwx, hpx, add_zero]) (by rw [bil_add_right, hwy, hpy, add_zero])] at h
    have : (2 : F) * bil Q w p = 0 := by linear_combination -h
    exact (mul_eq_zero.1 this).resolve_left iv_two_ne
  have hv : v = p + bil Q v y • x + bil Q v x • y := by simp only [p]; abel
  show bil Q w v = 0
  rw [hv, bil_add_right, bil_add_right, hwp, bil_smul_right, bil_smul_right, bil_comm Q w x, hwx,
    bil_comm Q w y, hwy]; ring

/-- Case $n \ge 3$ (O'Meara's argument): an isometry fixing all anisotropic lines fixes every isotropic line. -/
theorem mem_line_of_three_le (hQ : (QuadraticMap.associated Q).Nondegenerate) (h3 : 3 ≤ finrank F V)
    {σ : V ≃ₗ[F] V} {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1)
    (h : ∀ v, Q v ≠ 0 → ∃ c : F, σ v = c • v) : ∃ c : F, σ x = c • x := by
  obtain ⟨z, hz, hxz, hyz⟩ := exists_aniso_orth_pair Q hQ h3 hx hy hxy
  have hQ1 : ∀ t : F, t ≠ 0 → Q (x + t • y) ≠ 0 := fun t ht => by
    rw [Q_add_smul_of_pair Q hx hy hxy]; exact mul_ne_zero iv_two_ne ht
  obtain ⟨α, e1⟩ := h _ (hQ1 1 one_ne_zero)
  obtain ⟨β, e2⟩ := h _ (hQ1 (-1) (neg_ne_zero.2 one_ne_zero))
  have hQyz : Q (y + z) = Q z := by rw [Q_add, hy, hyz]; ring
  obtain ⟨μ, e4⟩ := h (y + z) (by rw [hQyz]; exact hz)
  have hQu : ∀ s : F, Q (x + s • (y + z)) = 2 * s + s ^ 2 * Q z := fun s => by
    rw [Q_add, Q_smul, hQyz, hx, bil_smul_right, bil_add_right, hxy, hxz]; ring
  obtain ⟨s, hs0, hs⟩ : ∃ s : F, s ≠ 0 ∧ Q (x + s • (y + z)) ≠ 0 := by
    by_cases h1 : 2 + Q z = 0
    · refine ⟨-1, neg_ne_zero.2 one_ne_zero, ?_⟩
      rw [hQu]
      have : 2 * (-1 : F) + (-1) ^ 2 * Q z = -4 := by linear_combination h1
      rw [this]
      have : (4 : F) = 2 * 2 := by norm_num
      rw [this, neg_ne_zero]; exact mul_ne_zero iv_two_ne iv_two_ne
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [hQu]; simpa [add_comm] using h1
  obtain ⟨ν, e5⟩ := h _ hs
  simp only [map_add, map_smul] at e1 e2 e4 e5
  -- independence of x, y, z
  have hli : LinearIndependent F ![x, y, z] := by
    apply linearIndependent_of_det_gram_ne_zero (R := F) Q
    rw [Matrix.det_fin_three]
    simp [gram, hx, hy, hxy, hxz, hyz, bil_comm Q y x, bil_comm Q z x, bil_comm Q z y, hz]
  have key := (Fintype.linearIndependent_iff.1 hli) ![(α + β) - 2 * ν, (α - β) - 2 * s * (ν - μ),
    -(2 * s * (ν - μ))] (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (norm := module) -(e1 + e2) + (2 : F) • e5 - (2 * s) • e4)
  have hk := key 2
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, neg_eq_zero] at hk
  refine ⟨ν, ?_⟩
  have hsνμ : s * (ν - μ) = 0 :=
    (mul_eq_zero.1 (by linear_combination hk : (2 : F) * (s * (ν - μ)) = 0)).resolve_left iv_two_ne
  have this : s • ν • (y + z) = s • μ • (y + z) := by
    rw [smul_smul, smul_smul, show s * ν = s * μ by linear_combination hsνμ]
  linear_combination (norm := module) e5 - s • e4 + this

/-- O'Meara's exceptional space: a regular isotropic binary space (a hyperbolic plane, 42:9) over a field of three
elements. -/
def IsExceptional43 : Prop :=
  finrank F V = 2 ∧ (∃ x : V, x ≠ 0 ∧ Q x = 0) ∧ Nat.card F = 3

/-- **O'Meara 43:11** (p. 109). Let $V$ be a regular quadratic space other than a hyperbolic plane over a field of
three elements, and let $\sigma \in O(V)$ leave every anisotropic line fixed ($\sigma x \in Fx$ whenever
$Q(x) \ne 0$). Then $\sigma = \pm 1_V$. -/
@[kb "omeara1963" "§43E, 43:11, p. 109"]
theorem eq_one_or_neg_of_forall_aniso_line (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hexc : ¬ IsExceptional43 Q) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q)
    (h : ∀ x, Q x ≠ 0 → ∃ a : F, σ x = a • x) : (∀ x, σ x = x) ∨ ∀ x, σ x = -x := by
  apply eq_one_or_neg_of_forall_mem_line Q hQ hσ
  intro x
  by_cases hx : Q x ≠ 0
  · exact h x hx
  push Not at hx
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  obtain ⟨y, hy, hxy⟩ := exists_hyp_partner Q hQ hx0 hx
  by_cases h3 : 3 ≤ finrank F V
  · exact mem_line_of_three_le Q hQ h3 hx hy hxy h
  · have h2 : finrank F V = 2 := by
      have := (linearIndependent_pair_of_hyp Q hx hy hxy).fintype_card_le_finrank
      simp at this; omega
    have hcard : Nat.card F ≠ 3 := fun hc => hexc ⟨h2, ⟨x, hx0, hx⟩, hc⟩
    obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_mul_self_ne_one hcard
    exact mem_line_of_three_lines Q hx hy hxy ha0 ha1 h

/-- $\tau_x x = -x$. -/
theorem iv_symmetry_self_apply {x : V} (hx : Q x ≠ 0) : symmetry Q x hx x = -x := by
  rw [symmetry_apply, bil_self, show 2 * Q x / Q x = 2 by field_simp, two_smul]; abel

/-- **O'Meara 43:12** (p. 110). Let $V$ be regular and not a hyperbolic plane over a field of three elements. Then
$\sigma \in O(V)$ lies in the center $Z_n$ of $O(V)$ (commutes with every element of $O(V)$) if and only if
$\sigma = \pm 1_V$; that is, $Z_n = \{\pm 1_V\}$. -/
@[kb "omeara1963" "§43E, 43:12, p. 110 (non-exceptional case)"]
theorem mem_center_iff (hQ : (QuadraticMap.associated Q).Nondegenerate) (hexc : ¬ IsExceptional43 Q)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) :
    (∀ ρ ∈ orth Q, σ * ρ = ρ * σ) ↔ (∀ x, σ x = x) ∨ ∀ x, σ x = -x := by
  constructor
  · intro hc
    apply eq_one_or_neg_of_forall_aniso_line Q hQ hexc hσ
    intro x hx
    have h1 := congrArg (fun f : V ≃ₗ[F] V => f x) (hc _ (symmetry_mem_orth Q hx))
    simp only [LinearEquiv.mul_apply, iv_symmetry_self_apply, map_neg] at h1
    rw [symmetry_apply] at h1
    refine ⟨bil Q (σ x) x / Q x, ?_⟩
    have h2 : (2 : F) • σ x = (2 : F) • ((bil Q (σ x) x / Q x) • x) := by
      rw [smul_smul, show 2 * (bil Q (σ x) x / Q x) = 2 * bil Q (σ x) x / Q x by ring]
      linear_combination (norm := module) -h1
    exact smul_right_injective V iv_two_ne h2
  · rintro (h | h) ρ _ <;> ext v <;> simp [h]

/-- **O'Meara 43:12a** (p. 110), non-commutativity: if $V$ is regular of dimension $n \ge 2$ and not a hyperbolic plane
over a field of three elements, then $O(V)$ is not commutative. -/
@[kb "omeara1963" "§43E, 43:12a, p. 110 (O_n not commutative for n ≥ 2, non-exceptional)"]
theorem not_commutative_of_two_le (hQ : (QuadraticMap.associated Q).Nondegenerate) (hexc : ¬ IsExceptional43 Q)
    (h2 : 2 ≤ finrank F V) : ¬ ∀ σ ∈ orth Q, ∀ ρ ∈ orth Q, σ * ρ = ρ * σ := by
  intro hcomm
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
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
  have hx0 : x ≠ 0 := fun h => hx (by simp [h])
  rcases (mem_center_iff Q hQ hexc (symmetry_mem_orth Q hx)).1 (hcomm _ (symmetry_mem_orth Q hx)) with h | h
  · have := h x
    rw [iv_symmetry_self_apply] at this
    have : (2 : F) • x = 0 := by rw [two_smul]; nth_rewrite 1 [← this]; simp
    exact hx0 ((smul_eq_zero.1 this).resolve_left iv_two_ne)
  · -- a non-zero vector orthogonal to x
    set W := LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) (F ∙ x)
    have hW : 1 ≤ finrank F W := by
      have h1 := LinearMap.BilinForm.finrank_orthogonal hQ (F ∙ x)
      rw [finrank_span_singleton hx0] at h1
      rw [h1]; exact Nat.le_sub_of_add_le (by omega)
    obtain ⟨w, hwW, hw0⟩ : ∃ w ∈ W, w ≠ 0 := by
      have : W ≠ ⊥ := fun h => by rw [h, finrank_bot] at hW; omega
      exact Submodule.exists_mem_ne_zero_of_ne_bot this
    have hwx : bil Q w x = 0 := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hwW
      rw [bil_comm]; exact hwW x (Submodule.mem_span_singleton_self x)
    have := h w
    rw [symmetry_apply, hwx] at this
    simp only [mul_zero, zero_div, zero_smul, sub_zero] at this
    have : (2 : F) • w = 0 := by rw [two_smul]; nth_rewrite 1 [this]; simp
    exact hw0 ((smul_eq_zero.1 this).resolve_left iv_two_ne)

/-- **O'Meara 43:12a** (p. 110), the case $n = 1$: the orthogonal group of a line is commutative. -/
@[kb "omeara1963" "§43E, 43:12a, p. 110 (O_1 is commutative)"]
theorem commutative_of_finrank_eq_one (h1 : finrank F V = 1) :
    ∀ σ ∈ orth Q, ∀ ρ ∈ orth Q, σ * ρ = ρ * σ := by
  have hsc : ∀ f : V →ₗ[F] V, ∃ a : F, f = a • 1 := fun f => by
    apply LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    intro v hli
    have := hli.fintype_card_le_finrank
    simp at this; omega
  intro σ _ ρ _
  obtain ⟨a, ha⟩ := hsc σ
  obtain ⟨b, hb⟩ := hsc ρ
  apply LinearEquiv.toLinearMap_injective
  ext v
  have hσ : σ v = a • v := by simpa using congrArg (fun f : V →ₗ[F] V => f v) ha
  have hρ : ∀ w, ρ w = b • w := fun w => by simpa using congrArg (fun f : V →ₗ[F] V => f w) hb
  have hσ' : ∀ w, σ w = a • w := fun w => by simpa using congrArg (fun f : V →ₗ[F] V => f w) ha
  simp only [LinearEquiv.coe_coe, LinearEquiv.mul_apply, hσ', hρ, smul_smul, mul_comm]

end Sec43E

end QuadFormsKB.OMeara
