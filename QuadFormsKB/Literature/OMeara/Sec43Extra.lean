import QuadFormsKB.Literature.OMeara.Sec43Irred
import QuadFormsKB.Literature.OMeara.Sec43Ternary
import QuadFormsKB.Literature.OMeara.Sec43Low
import QuadFormsKB.Literature.OMeara.Sec62Gap
import QuadFormsKB.Witt.Extension
import QuadFormsKB.Literature.OMeara.Sec42Extra

/-!
# O'Meara §43A–§43C: remaining items (prolongations, reflexions, axes, 43:5a)

**Setting** (as in `Sec43Omega.lean`): $F$ a field with $2 \ne 0$ (`[Invertible (2 : F)]`), $(V, Q)$ a
finite-dimensional quadratic space of dimension $n$, regular (`(QuadraticMap.associated Q).Nondegenerate`),
$B$ = `bil Q` ($B(x,x) = Q(x)$), $O_n = O(V)$ = `orth Q`, $O^+_n$ = `orthPlus Q` (rotations, determinant $1$),
$\tau_u$ = `symmetry Q u hu` ($Q(u) \ne 0$), the fixed space $\{x : \sigma x = x\}$ = `fixSp σ` and its dimension
`fixRank σ` (`Sec43A.lean`, `Sec43Low.lean`).

**Proves** (O'Meara 1973 printing, Chapter IV, §43, pp. 100–106):
* `reflexions` (definition, p. 100): the set $O^-_n$ of isometries of determinant $-1$;
  `orthPlus_union_reflexions`, `disjoint_orthPlus_reflexions`, `one_not_mem_reflexions` (p. 100): $O_n$ is the
  disjoint union of $O^+_n$ and $O^-_n$, and $O^-_n$ is not a subgroup;
* `cardinal_reflexions_eq`, `cardinal_anisoLine_le_reflexions` (p. 101): there are as many reflexions as rotations,
  and at least as many as anisotropic lines;
* `exists_eq_symmetry_of_mem_reflexions`, `cardinal_orthPlus_eq_of_finrank_two` (p. 104): in a binary space every
  reflexion is a symmetry, and #rotations = #symmetries = #anisotropic lines;
* `exists_two_prolongations` (**43:2**, regular hyperplane, p. 101): an isometry of a regular hyperplane $U$ into $V$
  has exactly two prolongations to $O_n$, $\sigma_1$ and $\sigma_1\tau_z$;
* `exists_symmetry_prod_eq_length_le_two_mul_sub_one` (footnote to 43:3, p. 102): the bound $2n - 1$;
* `exists_cd_prod_concat_eq` (**43:3b**, "or last", p. 104): the last symmetry can be chosen arbitrarily;
* `rotationsWithAxis` (definition, p. 105): the rotations fixing a line $L$ pointwise;
  `fixRank_eq_one_of_ternary` (p. 105): for ternary $V$ the fixed space of a rotation $\ne 1_V$ is a line, its axis;
  `mem_rotationsWithAxis_iff` (p. 105): for ternary $V$ the rotations with axis $L$ are $1_V$ and the rotations whose
  fixed space is $L$; `rotationsWithAxis_span_singleton` (comparison with `rotationsFixing` of 43:5);
* `exists_mulEquiv_rotationsWithAxis` (p. 105): for an anisotropic axis $L$, restriction to $L^\perp$ is an
  isomorphism of the rotations with axis $L$ onto $O^+(L^\perp)$;
* `exists_sq_eq_of_mem_rotationsFixing`, `exists_ne_one_mem_rotationsFixing` (**43:5a**, p. 106): every rotation on
  an isotropic axis is the square of a rotation on the same axis, and there is a rotation on this axis other than
  $1_V$.

Citations added at the end of the file: `det_orth_eq` ($\det\sigma = \pm1$, p. 100), `relIndex_orthPlus` and
`orthPlus_subgroupOf_normal` (pp. 100–101), `cd_star_even_det` (proof of 43:3), `fixSp` (p. 103),
`orthPlus_comm_of_finrank_le_two` (p. 104), `orthPlus_not_comm_of_three_le` (p. 105), `omega_eq_sq_orthPlus`
(43:8, $\Omega_2 = (O^+_2)^2$).

**Conventions.** Numbers of elements ("as many reflexions as rotations") are compared as cardinals (`Cardinal.mk`),
which covers infinite fields. "Rotations with axis $L$" (p. 105: the axis of a rotation $\ne 1_V$ of a ternary space is its
fixed space, a line, and every line is an axis of $1_V$) is formalized for all $n$ as the group
$\{\sigma \in O^+_n : \sigma v = v \text{ for } v \in L\}$; `mem_rotationsWithAxis_iff` shows it is the book's group for
$n = 3$. The restriction isomorphism (p. 105) is stated for any regular $V$ and anisotropic line $L$ (the book's case
is $n = 3$, $L^\perp$ a regular plane).
-/

open QuadraticMap Submodule Module LinearMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Sec43Extra

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)

theorem mem_orthPlus_iff' {σ : V ≃ₗ[F] V} : σ ∈ orthPlus Q ↔ σ ∈ orth Q ∧ LinearEquiv.det σ = 1 := by
  rw [orthPlus, Subgroup.mem_inf, MonoidHom.mem_ker]

/-! ### Rotations and reflexions (§43A) -/

/-- **The reflexions** $O^-_n(V)$ (O'Meara §43A, p. 100): the isometries of $V$ of determinant $-1$. -/
@[kb "omeara1963" "§43A, p. 100 (reflexions O⁻_n)"]
def reflexions : Set (V ≃ₗ[F] V) := {σ | σ ∈ orth Q ∧ LinearEquiv.det σ = -1}

/-- O'Meara §43A, p. 100: for regular $V$, $O_n = O^+_n \cup O^-_n$. -/
@[kb "omeara1963" "§43A, p. 100 (O_n = O⁺_n ∪ O⁻_n)"]
theorem orthPlus_union_reflexions (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    (orthPlus Q : Set (V ≃ₗ[F] V)) ∪ reflexions Q = orth Q := by
  ext σ
  simp only [Set.mem_union, SetLike.mem_coe, mem_orthPlus_iff', reflexions, Set.mem_ofPred_eq]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro h
    rcases det_orth_eq Q hQ h with h1 | h1
    · exact Or.inl ⟨h, h1⟩
    · exact Or.inr ⟨h, h1⟩

/-- O'Meara §43A, p. 100: the union $O_n = O^+_n \cup O^-_n$ is disjoint. -/
@[kb "omeara1963" "§43A, p. 100 (O⁺_n ∩ O⁻_n = ∅)"]
theorem disjoint_orthPlus_reflexions : Disjoint (orthPlus Q : Set (V ≃ₗ[F] V)) (reflexions Q) := by
  rw [Set.disjoint_left]
  rintro σ h1 ⟨-, h2⟩
  have h1' := ((mem_orthPlus_iff' Q).1 h1).2
  rw [h1'] at h2
  exact cd_neg_one_ne (F := F) h2.symm

/-- O'Meara §43A, p. 100: $O^-_n$ is not a subgroup (it does not contain $1_V$). -/
@[kb "omeara1963" "§43A, p. 100 (O⁻_n is not a subgroup)"]
theorem one_not_mem_reflexions : (1 : V ≃ₗ[F] V) ∉ reflexions Q := by
  rintro ⟨-, h⟩
  rw [map_one] at h
  exact cd_neg_one_ne (F := F) h.symm

/-- O'Meara §43A, p. 101: for a non-zero regular space there are as many reflexions as rotations
($\sigma \mapsto \tau_u\sigma$ is a bijection $O^-_n \to O^+_n$ for any anisotropic $u$). Counted as cardinals, so
infinite groups are included. -/
@[kb "omeara1963" "§43A, p. 101 (as many reflexions as rotations)"]
theorem cardinal_reflexions_eq (hQ : (QuadraticMap.associated Q).Nondegenerate) [Nontrivial V] :
    Cardinal.mk (reflexions Q) = Cardinal.mk (orthPlus Q) := by
  obtain ⟨u, hu⟩ := exists_Q_ne_zero Q hQ
  have hττ : symmetry Q u hu * symmetry Q u hu = 1 := iv_symmetry_mul_self Q hu
  refine Cardinal.mk_congr
    { toFun := fun σ => ⟨symmetry Q u hu * σ.1, (mem_orthPlus_iff' Q).2
        ⟨(orth Q).mul_mem (symmetry_mem_orth Q hu) σ.2.1, by rw [map_mul, det_symmetry, σ.2.2]; simp⟩⟩
      invFun := fun σ => ⟨symmetry Q u hu * σ.1,
        (orth Q).mul_mem (symmetry_mem_orth Q hu) ((mem_orthPlus_iff' Q).1 σ.2).1,
        by rw [map_mul, det_symmetry, ((mem_orthPlus_iff' Q).1 σ.2).2]; simp⟩
      left_inv := fun σ => Subtype.ext (by simp only [← mul_assoc, hττ, one_mul])
      right_inv := fun σ => Subtype.ext (by simp only [← mul_assoc, hττ, one_mul]) }

/-- The reflexion $\tau_L$ attached to an anisotropic line $L$. -/
def reflexionOfLine (L : AnisoLine Q) : reflexions Q :=
  ⟨symmetryOfLine Q L, symmetry_mem_orth Q _, det_symmetry Q _⟩

/-- O'Meara §43A, p. 101: there are at least as many reflexions as anisotropic lines (the symmetries $\tau_L$ are
distinct reflexions, 42.r25). -/
@[kb "omeara1963" "§43A, p. 101 (at least as many reflexions as anisotropic lines)"]
theorem cardinal_anisoLine_le_reflexions : Cardinal.mk (AnisoLine Q) ≤ Cardinal.mk (reflexions Q) :=
  Cardinal.mk_le_of_injective (f := reflexionOfLine Q) fun _ _ h =>
    symmetryOfLine_injective Q (congrArg Subtype.val h)

/-- O'Meara §43C, p. 104: in a regular binary space every reflexion is a symmetry (by 43:4). -/
@[kb "omeara1963" "§43C, p. 104 (binary: every reflexion is a symmetry)"]
theorem exists_eq_symmetry_of_mem_reflexions (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h2 : finrank F V = 2) {σ : V ≃ₗ[F] V} (hσ : σ ∈ reflexions Q) :
    ∃ (u : V) (hu : Q u ≠ 0), σ = symmetry Q u hu := by
  obtain ⟨l, rfl, hl⟩ := exists_cd_prod_length_eq_sub_fixRank Q hQ (by omega) hσ.1
  have hdet := hσ.2
  rw [cd_det_prod] at hdet
  have hle : l.length ≤ 2 := by omega
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp at hdet
    exact absurd hdet.symm (cd_neg_one_ne (F := F))
  · exact ⟨a.1, a.2, by simp [cd_prod]⟩
  · simp at hdet
    exact absurd hdet.symm (cd_neg_one_ne (F := F))
  · simp at hle

/-- O'Meara §43C, p. 104: in a regular binary space the reflexions are exactly the symmetries. -/
theorem reflexions_eq_range_symmetryOfLine (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h2 : finrank F V = 2) : reflexions Q = Set.range (symmetryOfLine Q) := by
  rw [symmetryOfLine_range]
  ext σ
  constructor
  · intro hσ
    exact exists_eq_symmetry_of_mem_reflexions Q hQ h2 hσ
  · rintro ⟨u, hu, rfl⟩
    exact ⟨symmetry_mem_orth Q hu, det_symmetry Q hu⟩

/-- O'Meara §43C, p. 104: in a regular binary space there are as many rotations as symmetries, and as many
symmetries as anisotropic lines (counted as cardinals). -/
@[kb "omeara1963" "§43C, p. 104 (binary: # rotations = # symmetries = # anisotropic lines)"]
theorem cardinal_orthPlus_eq_of_finrank_two (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h2 : finrank F V = 2) :
    Cardinal.mk (orthPlus Q) = Cardinal.mk {τ : V ≃ₗ[F] V | ∃ (u : V) (hu : Q u ≠ 0), τ = symmetry Q u hu} ∧
      Cardinal.mk {τ : V ≃ₗ[F] V | ∃ (u : V) (hu : Q u ≠ 0), τ = symmetry Q u hu} = Cardinal.mk (AnisoLine Q) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h2
  have hrange := reflexions_eq_range_symmetryOfLine Q hQ h2
  rw [symmetryOfLine_range] at hrange
  refine ⟨?_, ?_⟩
  · rw [← hrange, cardinal_reflexions_eq Q hQ]
  · rw [← symmetryOfLine_range, Cardinal.mk_range_eq _ (symmetryOfLine_injective Q)]

/-! ### Prolongations (43:2) -/

/-- **O'Meara 43:2** (p. 101), regular hyperplane, "exactly two". Let $V$ be regular, $U$ a hyperplane and $z$ an
anisotropic vector orthogonal to $U$ (so $U = (Fz)^\perp$ is regular), and let $\sigma : U \to V$ be an isometry of
$U$ into $V$ (an injective linear map with $Q(\sigma u) = Q(u)$). Then $\sigma$ has exactly two prolongations to
$O_n(V)$: there is $\sigma_1 \in O_n$ extending $\sigma$, the isometry $\sigma_1\tau_z$ also extends $\sigma$ and is
different from $\sigma_1$, and every prolongation is $\sigma_1$ or $\sigma_1\tau_z$. (Existence is Witt's theorem
42:17; uniqueness up to $\tau_z$ is `prolongation_eq_or_mul_symmetry`.) -/
@[kb "omeara1963" "§43A, 43:2, p. 101 (regular hyperplane: exactly two prolongations)"]
theorem exists_two_prolongations (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {U : Submodule F V} (hU : finrank F U + 1 = finrank F V) {z : V} (hz : Q z ≠ 0)
    (hzU : ∀ u ∈ U, bil Q u z = 0) (σ : U →ₗ[F] V) (hσi : Function.Injective σ) (hσ : ∀ u, Q (σ u) = Q u) :
    ∃ σ₁ ∈ orth Q, (∀ u : U, σ₁ u = σ u) ∧ σ₁ * symmetry Q z hz ∈ orth Q ∧
      (∀ u : U, (σ₁ * symmetry Q z hz) u = σ u) ∧ σ₁ * symmetry Q z hz ≠ σ₁ ∧
      ∀ σ₂ ∈ orth Q, (∀ u : U, σ₂ u = σ u) → σ₂ = σ₁ ∨ σ₂ = σ₁ * symmetry Q z hz := by
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_extend_of_associated Q hQ σ hσi hσ
  set σ₁ : V ≃ₗ[F] V := ρ.toLinearEquiv
  have h₁ : σ₁ ∈ orth Q := fun x => ρ.map_app x
  have hτU : ∀ u : U, symmetry Q z hz u = u := fun u => by
    rw [symmetry_apply, hzU u u.2]; simp
  refine ⟨σ₁, h₁, hρ, (orth Q).mul_mem h₁ (symmetry_mem_orth Q hz), fun u => ?_, fun h => ?_,
    fun σ₂ h₂ hext => ?_⟩
  · rw [LinearEquiv.mul_apply, hτU]; exact hρ u
  · have h' := congrArg (fun g : V ≃ₗ[F] V => σ₁⁻¹ * g) h
    simp only [inv_mul_cancel_left, inv_mul_cancel] at h'
    have hzz := congrArg (fun g : V ≃ₗ[F] V => g z) h'
    rw [iv_symmetry_self_apply, show (1 : V ≃ₗ[F] V) z = z from rfl] at hzz
    have : (2 : F) • z = 0 := by rw [two_smul]; nth_rewrite 1 [← hzz]; exact neg_add_cancel z
    have hz0 : z = 0 := (smul_eq_zero.1 this).resolve_left (two_ne_zero)
    exact hz (by rw [hz0, map_zero])
  · exact prolongation_eq_or_mul_symmetry Q hQ hU hz hzU h₁ h₂ fun u hu => by
      rw [show σ₁ u = σ ⟨u, hu⟩ from hρ ⟨u, hu⟩, ← hext ⟨u, hu⟩]

/-! ### Cartan–Dieudonné: the footnote bound and "or last" (43:3, 43:3b) -/

/-- **O'Meara 43:3, footnote** (p. 102): every isometry of a regular $n$-ary space ($n \ge 1$) is a product of at most
$2n - 1$ symmetries. (The book mentions an easy direct proof of this weaker bound; here it is deduced from the sharp
bound $n$ of 43:3, `exists_symmetry_prod_eq_length_le`.) -/
@[kb "omeara1963" "§43B, 43:3, p. 102 (footnote: at most 2n − 1 symmetries)"]
theorem exists_symmetry_prod_eq_length_le_two_mul_sub_one (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : 1 ≤ finrank F V) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) :
    ∃ l : List V, ∃ hl : ∀ u ∈ l, Q u ≠ 0,
      σ = (l.attach.map fun u => symmetry Q u.1 (hl u.1 u.2)).prod ∧ l.length ≤ 2 * finrank F V - 1 := by
  obtain ⟨l, hl, h, hlen⟩ := exists_symmetry_prod_eq_length_le Q hQ hσ
  exact ⟨l, hl, h, by omega⟩

theorem cd_prod_append (l m : List {u : V // Q u ≠ 0}) : cd_prod Q (l ++ m) = cd_prod Q l * cd_prod Q m := by
  simp [cd_prod]

theorem cd_prod_inv (l : List {u : V // Q u ≠ 0}) : (cd_prod Q l)⁻¹ = cd_prod Q l.reverse := by
  induction l with
  | nil => simp [cd_prod]
  | cons a l ih =>
    rw [cd_prod_cons, mul_inv_rev, ih, List.reverse_cons, cd_prod_append, symmetry_inv']
    simp [cd_prod]

/-- **O'Meara 43:3b** (p. 104), the "last" form. Let $V$ be regular of dimension $n$ and suppose
$\sigma = \tau_{u_1}\cdots\tau_{u_n}$ is a product of $n$ symmetries. Then for any anisotropic $a$, $\sigma$ is a
product $\tau_{v_1}\cdots\tau_{v_{n-1}}\tau_a$ of $n$ symmetries whose last symmetry is $\tau_a$. -/
@[kb "omeara1963" "§43B, 43:3b, p. 104 (last symmetry arbitrary)"]
theorem exists_cd_prod_concat_eq (hQ : (QuadraticMap.associated Q).Nondegenerate) {l : List {u : V // Q u ≠ 0}}
    (hlen : l.length = finrank F V) (a : {u : V // Q u ≠ 0}) :
    ∃ l' : List {u : V // Q u ≠ 0}, cd_prod Q l = cd_prod Q (l' ++ [a]) ∧ (l' ++ [a]).length = finrank F V := by
  obtain ⟨m, hm, hmlen⟩ := exists_cd_prod_cons_eq Q hQ (l := l.reverse) (by rw [List.length_reverse, hlen]) a
  refine ⟨m.reverse, ?_, by simpa using hmlen⟩
  have h := congrArg (·⁻¹) hm
  simp only [cd_prod_inv, List.reverse_reverse, List.reverse_cons] at h
  exact h

/-! ### Axes of rotations of a ternary space (§43C, p. 105) -/

/-- **Rotations with a given axis** (O'Meara §43C, p. 105): for a subspace $L$ (a line in the book), the rotations
$\sigma \in O^+(V)$ with $\sigma v = v$ for all $v \in L$. For a ternary space and a line $L$ this is the book's
group of rotations having $L$ as axis (`mem_rotationsWithAxis_iff`); it is a subgroup of $O^+_3(V)$, as the book
notes. -/
@[kb "omeara1963" "§43C, p. 105 (rotations with a given axis; a subgroup of O⁺_3)"]
def rotationsWithAxis (L : Submodule F V) : Subgroup (V ≃ₗ[F] V) :=
  orthPlus Q ⊓ fixingSubgroup (V ≃ₗ[F] V) (L : Set V)

theorem mem_rotationsWithAxis {L : Submodule F V} {σ : V ≃ₗ[F] V} :
    σ ∈ rotationsWithAxis Q L ↔ σ ∈ orthPlus Q ∧ ∀ v ∈ L, σ v = v := by
  rw [rotationsWithAxis, Subgroup.mem_inf, mem_fixingSubgroup_iff]
  rfl

/-- The rotations with axis $Fx$ are the rotations fixing $x$ (`rotationsFixing`, used for 43:5). -/
theorem rotationsWithAxis_span_singleton (x : V) :
    rotationsWithAxis Q (F ∙ x) = rotationsFixing Q x := by
  ext σ
  rw [mem_rotationsWithAxis, rotationsFixing, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 x (Submodule.mem_span_singleton_self x)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun v hv => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [map_smul]
    exact congrArg (c • ·) h2

theorem even_of_neg_one_pow_eq_one {k : ℕ} (h : (-1 : Fˣ) ^ k = 1) : Even k :=
  (neg_one_pow_eq_one_iff_even (cd_neg_one_ne (F := F))).1 h

/-- O'Meara §43C, p. 105 (consequence of 43:4): in a regular ternary space the fixed space of a rotation other
than $1_V$ is a line (the *axis* of the rotation). -/
@[kb "omeara1963" "§43C, p. 105 (the fixed space of a rotation ≠ 1 of a ternary space is a line, its axis)"]
theorem fixRank_eq_one_of_ternary (hQ : (QuadraticMap.associated Q).Nondegenerate) (h3 : finrank F V = 3)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ orthPlus Q) (h1 : σ ≠ 1) : fixRank σ = 1 := by
  obtain ⟨ho, hdet⟩ := (mem_orthPlus_iff' Q).1 hσ
  obtain ⟨l, rfl, hl⟩ := exists_cd_prod_length_eq_sub_fixRank Q hQ h3.le ho
  rw [cd_det_prod] at hdet
  have hev := even_of_neg_one_pow_eq_one hdet
  have hle := fixRank_le_finrank (cd_prod Q l)
  rcases Nat.lt_or_ge (fixRank (cd_prod Q l)) 3 with hlt | hge
  · obtain ⟨k, hk⟩ := hev
    omega
  · exact absurd (eq_one_of_fixRank_eq _ (by omega)) h1

/-- O'Meara §43C, p. 105: in a regular ternary space, for a line $L$, a rotation $\sigma$ has axis $L$ (it fixes
$L$ pointwise) iff $\sigma = 1_V$ or the fixed space of $\sigma$ is $L$. -/
@[kb "omeara1963" "§43C, p. 105 (rotations with axis L: 1_V and the rotations with fixed space L)"]
theorem mem_rotationsWithAxis_iff (hQ : (QuadraticMap.associated Q).Nondegenerate) (h3 : finrank F V = 3)
    {L : Submodule F V} (hL : finrank F L = 1) {σ : V ≃ₗ[F] V} :
    σ ∈ rotationsWithAxis Q L ↔ σ ∈ orthPlus Q ∧ (σ = 1 ∨ fixSp σ = L) := by
  rw [mem_rotationsWithAxis]
  constructor
  · rintro ⟨hσ, hfix⟩
    refine ⟨hσ, or_iff_not_imp_left.2 fun h1 => ?_⟩
    have hle : L ≤ fixSp σ := fun v hv => mem_fixSp.2 (hfix v hv)
    have hr := fixRank_eq_one_of_ternary Q hQ h3 hσ h1
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hL]; exact hr.symm)).symm
  · rintro ⟨hσ, h | h⟩
    · exact ⟨hσ, fun v _ => by rw [h]; rfl⟩
    · exact ⟨hσ, fun v hv => mem_fixSp.1 (h ▸ hv)⟩

/-! ### Restriction to the orthogonal complement of an anisotropic axis (§43C, p. 105) -/

theorem det_extId {U W : Submodule F V} (h : IsCompl U W) (τ : U ≃ₗ[F] U) :
    LinearEquiv.det (Sp55.extId h τ) = LinearEquiv.det τ := by
  apply Units.ext
  rw [LinearEquiv.coe_det, LinearEquiv.coe_det]
  have : ((Sp55.extId h τ : V ≃ₗ[F] V) : V →ₗ[F] V) =
      ((Submodule.prodEquivOfIsCompl U W h : (U × W) ≃ₗ[F] V) : (U × W) →ₗ[F] V) ∘ₗ
        (LinearMap.prodMap (τ : U →ₗ[F] U) LinearMap.id) ∘ₗ
        ((Submodule.prodEquivOfIsCompl U W h).symm : V →ₗ[F] U × W) := by
    ext v
    simp [Sp55.extId]
  rw [this, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, mul_one]

section Restrict

variable {z : V} (hz : Q z ≠ 0)

/-- The orthogonal complement $L^\perp$ of the line $L = Fz$. -/
abbrev perpLine (z : V) : Submodule F V :=
  LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q : LinearMap.BilinForm F V) (F ∙ z)

theorem isCompl_perpLine (hz : Q z ≠ 0) : IsCompl (perpLine Q z) (F ∙ z) := by
  refine (LinearMap.BilinForm.isCompl_span_singleton_orthogonal (B := QuadraticMap.associated Q) ?_).symm
  intro h
  apply hz
  have : bil Q z z = 0 := h
  rwa [bil_self] at this

theorem bil_perpLine {w : V} (hw : w ∈ perpLine Q z) : bil Q w z = 0 := by
  have := (LinearMap.BilinForm.mem_orthogonal_iff.1 hw) z (Submodule.mem_span_singleton_self z)
  rw [bil_comm]; exact this

theorem mem_perpLine_iff {w : V} : w ∈ perpLine Q z ↔ bil Q w z = 0 := by
  refine ⟨bil_perpLine Q, fun h => LinearMap.BilinForm.mem_orthogonal_iff.2 fun v hv => ?_⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  change bil Q (c • z) w = 0
  rw [bil_smul_left, bil_comm, h, mul_zero]

theorem horth_perpLine : ∀ u ∈ perpLine Q z, ∀ w ∈ F ∙ z, bil Q u w = 0 := by
  intro u hu w hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  rw [bil_smul_right, bil_perpLine Q hu, mul_zero]

/-- Extension by $1$ on $Fz$, as a homomorphism $O^+(L^\perp) \to$ rotations with axis $L$. -/
def extAxis : orthPlus (Q.comp (perpLine Q z).subtype) →* rotationsWithAxis Q (F ∙ z) where
  toFun τ := ⟨Sp55.extId (isCompl_perpLine Q hz) τ, by
    obtain ⟨hτo, hτd⟩ := (mem_orthPlus_iff' _).1 τ.2
    refine (mem_rotationsWithAxis Q).2 ⟨(mem_orthPlus_iff' Q).2
      ⟨Sp55.extId_mem_orth Q _ (horth_perpLine Q) hτo, by rw [det_extId, hτd]⟩, fun v hv => ?_⟩
    have := Sp55.extId_apply (isCompl_perpLine Q hz) (τ : _ ≃ₗ[F] _) 0 ⟨v, hv⟩
    simpa using this⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem extAxis_apply (τ : orthPlus (Q.comp (perpLine Q z).subtype)) (w : perpLine Q z) :
    ((extAxis Q hz τ : rotationsWithAxis Q (F ∙ z)) : V ≃ₗ[F] V) w = (((τ : _ ≃ₗ[F] _) w : perpLine Q z) : V) := by
  have := Sp55.extId_apply (isCompl_perpLine Q hz) (τ : _ ≃ₗ[F] _) w 0
  simp only [ZeroMemClass.coe_zero, add_zero] at this
  exact this

theorem mapsTo_perpLine {σ : V ≃ₗ[F] V} (hσ : σ ∈ rotationsWithAxis Q (F ∙ z)) {w : V}
    (hw : w ∈ perpLine Q z) : σ w ∈ perpLine Q z := by
  obtain ⟨hσp, hfix⟩ := (mem_rotationsWithAxis Q).1 hσ
  have ho := ((mem_orthPlus_iff' Q).1 hσp).1
  rw [mem_perpLine_iff] at hw ⊢
  rw [← hfix z (Submodule.mem_span_singleton_self z), bil_orth Q ho, hw]

theorem extAxis_bijective : Function.Bijective (extAxis Q hz) := by
  have hc := isCompl_perpLine Q hz
  constructor
  · intro τ τ' h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [← extAxis_apply Q hz, ← extAxis_apply Q hz, h]
  · rintro ⟨σ, hσ⟩
    have hσi : σ⁻¹ ∈ rotationsWithAxis Q (F ∙ z) := (rotationsWithAxis Q _).inv_mem hσ
    let f : perpLine Q z →ₗ[F] perpLine Q z :=
      (σ : V →ₗ[F] V).restrict fun w hw => mapsTo_perpLine Q hσ hw
    let g : perpLine Q z →ₗ[F] perpLine Q z :=
      ((σ⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V).restrict fun w hw => mapsTo_perpLine Q hσi hw
    let τ : perpLine Q z ≃ₗ[F] perpLine Q z := LinearEquiv.ofLinearMap f g
      (by ext w; simp [f, g]) (by ext w; simp [f, g])
    have hτ : ∀ w : perpLine Q z, ((τ w : perpLine Q z) : V) = σ w := fun w => rfl
    obtain ⟨hσp, hfix⟩ := (mem_rotationsWithAxis Q).1 hσ
    have ho := ((mem_orthPlus_iff' Q).1 hσp).1
    have hext : Sp55.extId hc τ = σ := by
      apply LinearEquiv.ext
      intro v
      obtain ⟨a, b, rfl⟩ := Sp55.exists_decomp hc v
      rw [Sp55.extId_apply, hτ, map_add, hfix b b.2]
    have hτo : τ ∈ orth (Q.comp (perpLine Q z).subtype) := fun w => by
      change Q ((τ w : perpLine Q z) : V) = Q (w : V)
      rw [hτ]; exact ho w
    have hτd : LinearEquiv.det τ = 1 := by
      rw [← det_extId hc, hext]; exact ((mem_orthPlus_iff' Q).1 hσp).2
    exact ⟨⟨τ, (mem_orthPlus_iff' _).2 ⟨hτo, hτd⟩⟩, Subtype.ext hext⟩

/-- **O'Meara §43C, p. 105.** Let $V$ be regular and $L = Fz$ an anisotropic line ($Q(z) \ne 0$). Restriction to
$L^\perp$ is an isomorphism of the group of rotations with axis $L$ onto the rotation group $O^+(L^\perp)$ of the
(regular) space $L^\perp$: there is an isomorphism $e$ with $e(\sigma) w = \sigma w$ for $w \in L^\perp$. (The book
states this for ternary $V$, where $L^\perp$ is a plane and $O^+(L^\perp) = O^+_2(L^*)$; it holds for every $n$.) -/
@[kb "omeara1963" "§43C, p. 105 (rotations with an anisotropic axis L ≅ O⁺(L^⊥) by restriction)"]
theorem exists_mulEquiv_rotationsWithAxis (hz : Q z ≠ 0) :
    ∃ e : rotationsWithAxis Q (F ∙ z) ≃* orthPlus (Q.comp (perpLine Q z).subtype),
      ∀ σ (w : perpLine Q z), (((e σ : _ ≃ₗ[F] _) w : perpLine Q z) : V) = (σ : V ≃ₗ[F] V) w := by
  let e := (MulEquiv.ofBijective (extAxis Q hz) (extAxis_bijective Q hz)).symm
  refine ⟨e, fun σ w => ?_⟩
  have h := extAxis_apply Q hz (e σ) w
  have h2 : extAxis Q hz (e σ) = σ := (MulEquiv.ofBijective (extAxis Q hz) (extAxis_bijective Q hz)).apply_symm_apply σ
  rw [h2] at h
  exact h.symm

end Restrict

/-! ### Rotations on an isotropic axis (43:5a) -/

/-- **O'Meara 43:5a** (p. 106), first sentence. In a regular ternary space, every rotation on an isotropic axis $Fx$
(a rotation fixing $x$, `rotationsFixing`; see `rotationsWithAxis_span_singleton`) is the square of a rotation on the
same axis. (Proof as in the book: $\rho_\alpha = \rho_{\alpha/2}^2$ under the isomorphism of 43:5.) -/
@[kb "omeara1963" "§43C, 43:5a, p. 106 (every rotation on an isotropic axis is a square)"]
theorem exists_sq_eq_of_mem_rotationsFixing (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : finrank F V = 3) {x : V} (hx0 : x ≠ 0) (hx : Q x = 0) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ rotationsFixing Q x) : ∃ ρ ∈ rotationsFixing Q x, σ = ρ ^ 2 := by
  obtain ⟨e⟩ := exists_mulEquiv_rotationsFixing Q hQ h3 hx0 hx
  obtain ⟨t, ht⟩ := e.surjective ⟨σ, hσ⟩
  let s : Multiplicative F := Multiplicative.ofAdd (Multiplicative.toAdd t / 2)
  have hts : t = s ^ 2 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow]
    simp only [s, toAdd_ofAdd]
    rw [two_nsmul, add_halves]
  refine ⟨(e s : V ≃ₗ[F] V), (e s).2, ?_⟩
  have := congrArg (fun g : rotationsFixing Q x => (g : V ≃ₗ[F] V)) ht
  simp only at this
  rw [← this, hts, map_pow, Subgroup.coe_pow]

/-- **O'Meara 43:5a** (p. 106), second sentence. In a regular ternary space there is a rotation on a given isotropic
axis $Fx$ which is not the identity. -/
@[kb "omeara1963" "§43C, 43:5a, p. 106 (a rotation on an isotropic axis other than 1_V)"]
theorem exists_ne_one_mem_rotationsFixing (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : finrank F V = 3) {x : V} (hx0 : x ≠ 0) (hx : Q x = 0) :
    ∃ σ ∈ rotationsFixing Q x, σ ≠ 1 := by
  obtain ⟨e⟩ := exists_mulEquiv_rotationsFixing Q hQ h3 hx0 hx
  refine ⟨(e (Multiplicative.ofAdd 1) : V ≃ₗ[F] V), (e _).2, fun h => ?_⟩
  have h' : e (Multiplicative.ofAdd 1) = 1 := Subtype.ext h
  rw [← map_one e] at h'
  have := congrArg Multiplicative.toAdd (e.injective h')
  simp at this

end Sec43Extra

/-! ### Citations for §43 items stated elsewhere in the library -/

attribute [kb "omeara1963" "§43A, p. 100 (det σ = ±1 for σ ∈ O_n)"] det_orth_eq
attribute [kb "omeara1963" "§43A, pp. 100–101 ((O_n : O⁺_n) = 2)"] relIndex_orthPlus
attribute [kb "omeara1963" "§43A, p. 101 (O⁺_n is normal in O_n)"] orthPlus_subgroupOf_normal
attribute [kb "omeara1963" "§43B, pp. 102–103 (proof of 43:3, step 1: n even and σ a rotation)"] cd_star_even_det
attribute [kb "omeara1963" "§43B, p. 103 (fixed space of σ)"] fixSp
attribute [kb "omeara1963" "§43C, p. 104 (O⁺_2 is commutative)"] orthPlus_comm_of_finrank_le_two
attribute [kb "omeara1963" "§43C, p. 105 (O⁺_n not commutative for n ≥ 3, announced)"]
  orthPlus_not_comm_of_three_le
attribute [kb "omeara1963" "§43D, 43:8, p. 108 (Ω_2 = (O⁺_2)²)"] omega_eq_sq_orthPlus

end QuadFormsKB.OMeara
