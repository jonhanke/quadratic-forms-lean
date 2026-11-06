/-
# O'Meara §61C and §62: the groups $\Omega_n$, $O_n'$, $O_n^+$, $Z_n$ over $\mathbb C$, $\mathbb R$ and a finite field

**Setting.** O'Meara works over a complex field ($\cong\mathbb C$), a real field ($\cong\mathbb R$) and a finite field
$F$ of odd characteristic (§61, §62). $(V,Q)$ is a regular quadratic space (`(QuadraticMap.associated Q).Nondegenerate`)
of dimension $n$. The groups are those of `Sec55.lean`: $O_n^+$ = `orthPlus Q`, $\Omega_n$ = `omega Q`,
$O_n'$ = `orthPrime Q`; $Z_n=\{\pm1_V\}$ is the set `{1, LinearEquiv.neg F}` (the centre of $O_n$ for $n\ge1$),
and "$dV=1$" is `IsSquare (gram Q b).det` for a basis `b` of $V$ (the discriminant is $1$ modulo squares).

**Proves**
* 61.r26 (p. 156, complex case): `complex_omega_eq_orthPrime_eq_orthPlus` ($\Omega_n=O_n'=O_n^+$) and
  `complex_omega_inter_center` ($\Omega_n\cap Z_n=\{\pm1_V\}$ for $n$ even, $\{1_V\}$ for $n$ odd);
* 61.r28 (p. 157, real case): `real_omega_eq_orthPrime` ($O_n'=\Omega_n$ for every regular $V$);
* 61.r29 (p. 157, real case): `real_orthPrime_inter_center` ($O_n'\cap Z_n$) and `real_omega_inter_center`
  ($\Omega_n\cap Z_n$), for every regular $V$;
* 62:4 (p. 158, finite field, $n\ge2$): `relIndex_orthPrime_orthPlus_finite` ($(O_n^+:O_n')=2$) and
  `omega_inter_center_finite` ($\Omega_n\cap Z_n=\{\pm1_V\}$ if $dV=1$ and $n$ even, $\{1_V\}$ otherwise); part (ii)
  $O_n'=\Omega_n$ is `omega_eq_orthPrime_finite` (`Sec62Gap.lean`).

**Deviations and gaps.**
* Real case, *definite* $V$ with $n\ge4$: the library's `omega_eq_orthPrime` needs $n\le3$ or an isotropic vector;
  the definite case is 55:6 (`omega_eq_orthPrime_of_subspace`) applied to a line $U=Fv$, as the book's "by 55:5 and
  55:6" indicates.
* "$dV=1$" is expressed as `IsSquare (gram Q b).det`, which over $\mathbb R$ means $\det\ge0$ (equivalently $>0$ for a
  regular space).
* $Z_n\cap\Omega_n$ is stated as a set equality in `V ≃ₗ[F] V`, in two implications (condition / not condition).
* The 62:4 index is stated for $n\ge2$ (as in the book); part (iii) needs no restriction beyond regularity.
-/
import QuadFormsKB.Literature.OMeara.Sec62Gap
import QuadFormsKB.Literature.OMeara.Sec61Rest

open QuadraticMap QuadraticForm Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section General

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- Intersection of a subgroup with $Z=\{1,-1_V\}$, in terms of whether $-1_V$ belongs to it. -/
private theorem inter_center_of_neg_mem_iff (H : Subgroup (V ≃ₗ[F] V)) {P : Prop}
    (h : LinearEquiv.neg F ∈ H ↔ P) :
    (P → (H : Set (V ≃ₗ[F] V)) ∩ {1, LinearEquiv.neg F} = {1, LinearEquiv.neg F}) ∧
    (¬ P → (H : Set (V ≃ₗ[F] V)) ∩ {1, LinearEquiv.neg F} = {1}) := by
  constructor
  · intro hP
    ext σ
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact fun h => h.2
    · rintro (rfl | rfl)
      · exact ⟨H.one_mem, Or.inl rfl⟩
      · exact ⟨h.mpr hP, Or.inr rfl⟩
  · intro hP
    ext σ
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hσ, rfl | rfl⟩
      · rfl
      · exact absurd (h.mp hσ) hP
    · rintro rfl
      exact ⟨H.one_mem, Or.inl rfl⟩

end General

/-! ### 61.r26: the complex case -/

section Complex

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

private theorem complex_omega_eq (Q : QuadraticForm ℂ V) (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    omega Q = orthPrime Q := by
  by_cases h3 : finrank ℂ V ≤ 3
  · exact omega_eq_orthPrime Q hQ (Or.inl h3)
  · obtain ⟨x, hx, hx0⟩ := by
      have := not_anisotropic_complex Q (by omega)
      simpa only [QuadraticMap.Anisotropic, not_forall] using this
    exact omega_eq_orthPrime Q hQ (Or.inr ⟨x, hx0, hx⟩)

/-- **$\Omega_n=O_n'=O_n^+$ over $\mathbb C$** (O'Meara 1963, §61C, p. 156, from §56): for a regular $n$-ary space $V$
over $\mathbb C$ the commutator subgroup $\Omega_n$, the spinor kernel $O_n'$ and the group of rotations $O_n^+$
coincide. (Every $n\le3$ is covered by 55:5, $n\ge2$ by isotropy and 55:6a; every spinor norm is a square since
$\mathbb C$ is algebraically closed.) -/
@[kb "omeara1963" "§61C, p. 156 (complex case: Ω_n = O'_n = O⁺_n)"]
theorem complex_omega_eq_orthPrime_eq_orthPlus (Q : QuadraticForm ℂ V)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) : omega Q = orthPrime Q ∧ orthPrime Q = orthPlus Q := by
  refine ⟨complex_omega_eq Q hQ, le_antisymm (orthPrime_le_orthPlus Q) fun σ hσ => ?_⟩
  obtain ⟨c, -, hc⟩ := exists_hasSpinorNorm_of_mem_orth Q hQ hσ.1
  refine (mem_orthPrime_iff Q hQ ⟨c, hc⟩).2 ⟨hσ, fun d _ => ?_⟩
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq d (n := 2) (by norm_num)
  exact ⟨r, by rw [← hr]; ring⟩

/-- **$\Omega_n\cap Z_n$ over $\mathbb C$** (O'Meara 1963, §61C, p. 156, from §56): for a regular $n$-ary space over
$\mathbb C$, $\Omega_n\cap Z_n=\{\pm1_V\}$ if $n$ is even and $\{1_V\}$ if $n$ is odd, where $Z_n=\{\pm1_V\}$.
In other words $-1_V\in\Omega_n$ if and only if $n$ is even ($dV$ is always a square in $\mathbb C$). -/
@[kb "omeara1963" "§61C, p. 156 (complex case: Ω_n ∩ Z_n = {±1_V} for n even, {1_V} for n odd)"]
theorem complex_omega_inter_center (Q : QuadraticForm ℂ V) (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    (Even (finrank ℂ V) →
      (omega Q : Set (V ≃ₗ[ℂ] V)) ∩ {1, LinearEquiv.neg ℂ} = {1, LinearEquiv.neg ℂ}) ∧
    (¬ Even (finrank ℂ V) → (omega Q : Set (V ≃ₗ[ℂ] V)) ∩ {1, LinearEquiv.neg ℂ} = {1}) := by
  refine inter_center_of_neg_mem_iff (omega Q) ?_
  have hcase : finrank ℂ V ≤ 3 ∨ ∃ x : V, x ≠ 0 ∧ Q x = 0 := by
    by_cases h3 : finrank ℂ V ≤ 3
    · exact Or.inl h3
    · obtain ⟨x, hx, hx0⟩ := by
        have := not_anisotropic_complex Q (by omega)
        simpa only [QuadraticMap.Anisotropic, not_forall] using this
      exact Or.inr ⟨x, hx0, hx⟩
  rw [neg_mem_omega_iff Q hQ (Module.finBasis ℂ V) hcase]
  refine and_iff_left_of_imp fun _ => ?_
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq ((gram Q (Module.finBasis ℂ V)).det) (n := 2) (by norm_num)
  exact ⟨r, by rw [← hr]; ring⟩

end Complex

/-! ### 61.r28, 61.r29: the real case -/

section Real

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

private theorem real_hcase (Q : QuadraticForm ℝ V) (h : finrank ℝ V ≤ 3 ∨ IsIndefinite Q) :
    finrank ℝ V ≤ 3 ∨ ∃ x : V, x ≠ 0 ∧ Q x = 0 := by
  rcases h with h | h
  · exact Or.inl h
  · obtain ⟨x, hx, hx0⟩ := by
      have := (isIndefinite_iff_not_anisotropic Q).1 h
      simpa only [QuadraticMap.Anisotropic, not_forall] using this
    exact Or.inr ⟨x, hx0, hx⟩

/-- An anisotropic real quadratic form has a nondegenerate associated bilinear form. -/
private theorem nondegenerate_of_anisotropic' {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Q : QuadraticForm ℝ W) (hA : Q.Anisotropic) : (QuadraticMap.associated Q).Nondegenerate :=
  (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (fun x y h => by rw [QuadraticMap.associated_isSymm ℝ Q]; exact h)).2 (QuadraticMap.separatingLeft_of_anisotropic Q hA)

/-- The definite case of 61.r28, by 55:6 with $U$ a line: every nonzero value of a definite $Q$ is a positive
multiple of $Q(v)$ for a fixed $v\ne0$, hence a value on $Fv$, and $\Omega(Fv)=O'(Fv)$ by 55:5 ($n=1$). -/
private theorem real_omega_eq_orthPrime_of_isDefinite (Q : QuadraticForm ℝ V)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) (hD : IsDefinite Q) : omega Q = orthPrime Q := by
  have hA : Q.Anisotropic := by
    rcases hD with h | h
    · exact h.anisotropic
    · intro x hx
      exact h.anisotropic x (by simp [hx])
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact omega_eq_orthPrime Q hQ (Or.inl (by simp [Module.finrank_zero_of_subsingleton]))
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hQv : Q v ≠ 0 := fun h => hv (hA v h)
  have hAU : (Q.comp (ℝ ∙ v).subtype).Anisotropic := fun u hu =>
    Subtype.ext (hA (u : V) hu)
  have hU := nondegenerate_of_anisotropic' _ hAU
  refine omega_eq_orthPrime_of_subspace Q hQ hU ?_
    (omega_eq_orthPrime_of_finrank_le_three _ hU (by rw [finrank_span_singleton hv]; norm_num))
  intro w
  have hnn : 0 ≤ Q w / Q v := by
    rcases hD with h | h
    · exact div_nonneg (h.nonneg w) (h.nonneg v)
    · have h1 := h.nonneg w
      have h2 := h.nonneg v
      simp only [neg_apply, neg_nonneg] at h1 h2
      exact div_nonneg_of_nonpos h1 h2
  refine ⟨⟨Real.sqrt (Q w / Q v) • v, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)⟩, ?_⟩
  simp only [QuadraticMap.map_smul, smul_eq_mul]
  rw [Real.mul_self_sqrt hnn]
  field_simp

/-- **$O_n'=\Omega_n$ over $\mathbb R$** (O'Meara 1963, §61C, p. 157, by 55:5 and 55:6): for every regular real
space, $\Omega_n=O_n'$. For $n\le3$ this is 55:5, for indefinite (hence isotropic) $V$ it is 55:6a, and for definite
$V$ it is 55:6 applied to a line $U=Fv$ (every value of $Q$ is attained on $U$). -/
@[kb "omeara1963" "§61C, p. 157 (real case: O'_n = Ω_n)"]
theorem real_omega_eq_orthPrime (Q : QuadraticForm ℝ V) (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    orthPrime Q = omega Q := by
  by_cases hD : IsDefinite Q
  · exact (real_omega_eq_orthPrime_of_isDefinite Q hQ hD).symm
  · exact (omega_eq_orthPrime Q hQ (real_hcase Q (Or.inr hD))).symm

/-- **$O_n'\cap Z_n$ over $\mathbb R$** (O'Meara 1963, §61C, p. 157, by 55:7): for every regular real space $V$ and
basis $b$, $O_n'\cap Z_n=\{\pm1_V\}$ if $dV=1$ (a square) and $n$ is even, and $\{1_V\}$ otherwise. -/
@[kb "omeara1963" "§61C, p. 157 (real case: O'_n ∩ Z_n = {±1_V} if dV = 1 and n even, {1_V} otherwise)"]
theorem real_orthPrime_inter_center (Q : QuadraticForm ℝ V) (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ V) :
    (Even (finrank ℝ V) ∧ IsSquare (gram Q b).det →
      (orthPrime Q : Set (V ≃ₗ[ℝ] V)) ∩ {1, LinearEquiv.neg ℝ} = {1, LinearEquiv.neg ℝ}) ∧
    (¬ (Even (finrank ℝ V) ∧ IsSquare (gram Q b).det) →
      (orthPrime Q : Set (V ≃ₗ[ℝ] V)) ∩ {1, LinearEquiv.neg ℝ} = {1}) :=
  inter_center_of_neg_mem_iff (orthPrime Q) (neg_mem_orthPrime_iff Q hQ b)

/-- **$\Omega_n\cap Z_n$ over $\mathbb R$** (O'Meara 1963, §61C, p. 157, by 55:7): for every regular real space,
$\Omega_n\cap Z_n=\{\pm1_V\}$ if $dV=1$ (a square) and $n$ is even, and $\{1_V\}$ otherwise. -/
@[kb "omeara1963" "§61C, p. 157 (real case: Ω_n ∩ Z_n = {±1_V} if dV = 1 and n even, {1_V} otherwise)"]
theorem real_omega_inter_center (Q : QuadraticForm ℝ V) (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ V) :
    (Even (finrank ℝ V) ∧ IsSquare (gram Q b).det →
      (omega Q : Set (V ≃ₗ[ℝ] V)) ∩ {1, LinearEquiv.neg ℝ} = {1, LinearEquiv.neg ℝ}) ∧
    (¬ (Even (finrank ℝ V) ∧ IsSquare (gram Q b).det) →
      (omega Q : Set (V ≃ₗ[ℝ] V)) ∩ {1, LinearEquiv.neg ℝ} = {1}) :=
  real_omega_eq_orthPrime Q hQ ▸ real_orthPrime_inter_center Q hQ b

end Real

/-! ### 62:4: the finite field -/

section Finite

variable {F : Type*} [Field F] [Fintype F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

private theorem finite_ringChar_ne_two : ringChar F ≠ 2 := by
  intro h
  have h2 : ((ringChar F : ℕ) : F) = 0 := ringChar.Nat.cast_ringChar
  rw [h] at h2
  exact (isUnit_of_invertible (2 : F)).ne_zero (by exact_mod_cast h2)

private theorem mem_range_sq_iff_isSquare (x : Fˣ) :
    x ∈ (powMonoidHom 2 : Fˣ →* Fˣ).range ↔ IsSquare (x : F) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by simp [_root_.sq]⟩
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact x.ne_zero (by simp [hr])
    exact ⟨Units.mk0 r hr0, by ext; simp [_root_.sq, hr]⟩

private theorem index_sq_units_finite : (powMonoidHom 2 : Fˣ →* Fˣ).range.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  obtain ⟨ε, hε⟩ := FiniteField.exists_nonsquare (finite_ringChar_ne_two (F := F))
  have hε0 : ε ≠ 0 := by rintro rfl; exact hε ⟨0, by simp⟩
  refine ⟨Units.mk0 ε hε0, fun b => ?_⟩
  simp only [mem_range_sq_iff_isSquare, Units.val_mul, Units.val_mk0]
  by_cases hb : IsSquare (b : F)
  · refine Or.inr ⟨hb, fun h => hε ?_⟩
    obtain ⟨r, hr⟩ := hb
    obtain ⟨s, hs⟩ := h
    have hr0 : r ≠ 0 := by rintro rfl; exact b.ne_zero (by simp [hr])
    exact ⟨s / r, by field_simp; linear_combination hs - ε * hr⟩
  · exact Or.inl ⟨nonsq_mul_nonsq hb hε, hb⟩

/-- **$(O_n^+:O_n')=2$ over a finite field** (O'Meara 1963, 62:4 (i), p. 158): for a regular quadratic space $V$ of
dimension $n\ge2$ over a finite field of odd characteristic, the spinor kernel $O_n'$ has index $2$ in $O_n^+$. (The
spinor norm is onto $\dot F/\dot F^2$, `exists_hasSpinorNorm_finite`, a group of order $2$.) -/
@[kb "omeara1963" "§62, 62:4 (i), p. 158 ((O⁺_n : O'_n) = 2)"]
theorem relIndex_orthPrime_orthPlus_finite (Q : QuadraticForm F V)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : 2 ≤ finrank F V) :
    (orthPrime Q).relIndex (orthPlus Q) = 2 := by
  have hsurj : Function.Surjective (spinorNormHom Q hQ) := by
    intro c
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective (s := (powMonoidHom 2 : Fˣ →* Fˣ).range) c
    obtain ⟨σ, hσ, hs⟩ := exists_hasSpinorNorm_finite Q hQ hn u.ne_zero
    refine ⟨⟨σ, hσ⟩, ?_⟩
    rw [spinorNormHom_apply Q hQ hs, Sp55.sqClassOf_of_ne_zero' u.ne_zero]
    have e : Units.mk0 (u : F) u.ne_zero = u := Units.ext rfl
    rw [e]
    rfl
  rw [Subgroup.relIndex, ← ker_spinorNormHom Q hQ, Subgroup.index,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv]
  have := index_sq_units_finite (F := F)
  rw [Subgroup.index] at this
  exact this

/-- **$\Omega_n\cap Z_n$ over a finite field** (O'Meara 1963, 62:4 (iii), p. 158): for a regular quadratic space of
dimension $n$ over a finite field of odd characteristic, $\Omega_n\cap Z_n=\{\pm1_V\}$ if $dV=1$ (a square) and $n$ is
even, and $\{1_V\}$ otherwise. (With 62:4 (ii), $\Omega_n=O_n'$, `omega_eq_orthPrime_finite`.) -/
@[kb "omeara1963" "§62, 62:4 (iii), p. 158 (Ω_n ∩ Z_n = {±1_V} if dV = 1 and n even, {1_V} otherwise)"]
theorem omega_inter_center_finite (Q : QuadraticForm F V) (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F V) :
    (Even (finrank F V) ∧ IsSquare (gram Q b).det →
      (omega Q : Set (V ≃ₗ[F] V)) ∩ {1, LinearEquiv.neg F} = {1, LinearEquiv.neg F}) ∧
    (¬ (Even (finrank F V) ∧ IsSquare (gram Q b).det) →
      (omega Q : Set (V ≃ₗ[F] V)) ∩ {1, LinearEquiv.neg F} = {1}) := by
  refine inter_center_of_neg_mem_iff (omega Q) ?_
  rw [omega_eq_orthPrime_finite Q hQ]
  exact neg_mem_orthPrime_iff Q hQ b

end Finite

end QuadFormsKB.OMeara
