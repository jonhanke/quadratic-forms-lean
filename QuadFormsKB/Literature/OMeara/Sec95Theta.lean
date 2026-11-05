/-
# O'Meara §95: the group $O_n^+/O'_n$ over a local field

**Setting** (as in `Sec95.lean`): $F$ a number field, $\mathfrak p$ (`v`) a finite place, $K = F_\mathfrak p$
(`v.adicCompletion F`), $(V, Q)$ a regular quadratic space over $K$ of dimension $n$. The spinor norm is the
homomorphism $\theta : O^+(V) \to \dot K/\dot K^2$ (`spinorNormHom Q hQ`, `Sec55.lean`, with values in
`Lattices.SqClass K`); its kernel is $O'(V)$ (`ker_spinorNormHom`), so $O^+_n/O'_n \cong \theta(O^+_n)$
(`orthPlus_quotient_equiv_range`).

**Proves** the closing remarks of §95 (O'Meara 1973 printing, p. 284):
* `spinorNormHom_surjective_local`, `orthPlus_quotient_equiv_local`: $O^+_n/O'_n \cong \dot F/\dot F^2$ for
  $n \ge 3$, and for $n = 2$ with $V$ isotropic (O'Meara recalls this from Proposition 91:6);
* `spinorNormHom_range_index_binary`: for $n = 2$ with $V$ anisotropic, $O^+_n/O'_n$ is isomorphic to a subgroup of
  index $2$ in $\dot F/\dot F^2$ (O'Meara: "use Example 63:15").
-/
import QuadFormsKB.Literature.OMeara.Sec95

open QuadraticMap Module NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type*} [AddCommGroup V] [Module (v.adicCompletion F) V] [FiniteDimensional (v.adicCompletion F) V]
  [Invertible (2 : v.adicCompletion F)]
variable (Q : QuadraticForm (v.adicCompletion F) V)

namespace S95

local notation "Kv" => v.adicCompletion F

local notation "hs" => hilbertSymbol (v.adicCompletion F)

/-- A regular space of dimension `n` has an orthogonal basis indexed by `Fin n` of non-isotropic vectors. -/
lemma t_orth_basis (hQ : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ} (hn : finrank Kv V = n) :
    ∃ e : Basis (Fin n) Kv V, (∀ i j, i ≠ j → bil Q (e i) (e j) = 0) ∧ ∀ i, Q (e i) ≠ 0 := by
  obtain ⟨e, ho, hne⟩ := exists_orth_basis v Q hQ
  refine ⟨e.reindex (finCongr hn), fun i j hij => ?_, fun i => ?_⟩
  · simp only [Basis.reindex_apply]
    exact ho _ _ (fun h => hij (by simpa using h))
  · simp only [Basis.reindex_apply]
    exact hne _

/-- Value of `Q` in an orthogonal basis of a binary space. -/
lemma t_Q_two (e : Basis (Fin 2) Kv V) (ho : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0) (x : V) :
    Q x = Q (e 0) * e.repr x 0 ^ 2 + Q (e 1) * e.repr x 1 ^ 2 := by
  have := Q_comb v Q e ho (fun i => e.repr x i)
  rw [e.sum_repr x, Fin.sum_univ_two] at this
  exact this

/-- A vector with prescribed binary coordinates. -/
lemma t_Q_two' (e : Basis (Fin 2) Kv V) (ho : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0) (X Y : Kv) :
    Q (X • e 0 + Y • e 1) = Q (e 0) * X ^ 2 + Q (e 1) * Y ^ 2 := by
  have := Q_comb v Q e ho ![X, Y]
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at this
  simpa using this

/-- Binary space: every non-zero value `t` of `Q` has `(t, -ab) = (a, b)`. -/
lemma t_hs_value (e : Basis (Fin 2) Kv V) (ho : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0)
    (hne : ∀ i, Q (e i) ≠ 0) {x : V} (hx : Q x ≠ 0) :
    hs (Q x) (-(Q (e 0) * Q (e 1))) = hs (Q (e 0)) (Q (e 1)) :=
  (LocalRankFive.represents_two_iff v (hne 0) (hne 1) hx).1
    ⟨_, _, (t_Q_two v Q e ho x).symm⟩

/-- Binary space: a `t` with `(t, -ab) = (a, b)` is a value of `Q`. -/
lemma t_value_of_hs (e : Basis (Fin 2) Kv V) (ho : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0)
    (hne : ∀ i, Q (e i) ≠ 0) {t : Kv} (ht : t ≠ 0)
    (h : hs t (-(Q (e 0) * Q (e 1))) = hs (Q (e 0)) (Q (e 1))) : ∃ x : V, Q x = t := by
  obtain ⟨X, Y, hXY⟩ := (LocalRankFive.represents_two_iff v (hne 0) (hne 1) ht).2 h
  exact ⟨X • e 0 + Y • e 1, by rw [t_Q_two' v Q e ho, hXY]⟩

/-- An anisotropic binary space has `-ab` a non-square. -/
lemma t_not_square (hQa : Q.Anisotropic) (e : Basis (Fin 2) Kv V)
    (ho : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0) (hne : ∀ i, Q (e i) ≠ 0) :
    ¬ IsSquare (-(Q (e 0) * Q (e 1))) := by
  rintro ⟨r, hr⟩
  have h0 : Q (e 0) * Q (e 1) ≠ 0 := mul_ne_zero (hne 0) (hne 1)
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply h0
    simpa using hr
  have hz : Q (r • e 0 + Q (e 0) • e 1) = 0 := by
    rw [t_Q_two' v Q e ho]
    linear_combination (-(Q (e 0))) * hr
  have hnz : r • e 0 + Q (e 0) • e 1 ≠ 0 := by
    have := comb_ne_zero v Q e ho hne (c := ![r, Q (e 0)]) (by
      intro h; apply hr0; simpa using congrFun h 0)
    rwa [Fin.sum_univ_two] at this
    
  exact hnz (hQa _ hz)

/-- Value of the orthogonal-basis ternary form: if `-αP` is a non-square (P the product of the norms) in an
anisotropic space then `α` is a value. -/
lemma t_rep3 (hQa : Q.Anisotropic) (W3 : Fin 3 → V) (horth3 : ∀ i j, i ≠ j → bil Q (W3 i) (W3 j) = 0)
    (hne3 : ∀ i, Q (W3 i) ≠ 0) {α : Kv} (hα0 : α ≠ 0)
    (hnsq : ¬ IsSquare (Q (W3 0) * Q (W3 1) * Q (W3 2) * (-α))) : ∃ x : V, Q x = α := by
  have hb : ∀ i, (![Q (W3 0), Q (W3 1), Q (W3 2), -α] : Fin 4 → Kv) i ≠ 0 := by
    intro i; fin_cases i <;> simp [hne3, hα0]
  have hd : ¬ IsSquare ((![Q (W3 0), Q (W3 1), Q (W3 2), -α] : Fin 4 → Kv) 0 *
      (![Q (W3 0), Q (W3 1), Q (W3 2), -α] : Fin 4 → Kv) 1 *
      (![Q (W3 0), Q (W3 1), Q (W3 2), -α] : Fin 4 → Kv) 2 *
      (![Q (W3 0), Q (W3 1), Q (W3 2), -α] : Fin 4 → Kv) 3) := by
    simpa using hnsq
  obtain ⟨y, hy0, hy⟩ := LocalRankFive.isotropic_four_of_not_isSquare v _ hb hd
  rw [LocalRankFive.evalIn_diag_four] at hy
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hy
  have hy' : Q (W3 0) * y 0 ^ 2 + Q (W3 1) * y 1 ^ 2 + Q (W3 2) * y 2 ^ 2 = α * y 3 ^ 2 := by
    linear_combination hy
  set cc : Fin 3 → Kv := ![y 0, y 1, y 2] with hcc
  by_cases ht : y 3 = 0
  · exfalso
    have hcc0 : cc ≠ 0 := by
      intro h
      apply hy0
      funext i
      fin_cases i
      · simpa [hcc] using congrFun h 0
      · simpa [hcc] using congrFun h 1
      · simpa [hcc] using congrFun h 2
      · simpa using ht
    have hz : Q (∑ i, cc i • W3 i) = 0 := by
      rw [Q_comb v Q W3 horth3]
      simp only [hcc, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [ht] at hy'
      linear_combination hy'
    exact comb_ne_zero v Q W3 horth3 hne3 hcc0 (hQa _ hz)
  · refine ⟨∑ i, (cc i / y 3) • W3 i, ?_⟩
    rw [Q_comb v Q W3 horth3]
    simp only [hcc, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp
    linear_combination hy'

/-- Group identity. -/
lemma t_grp_aux {G : Type*} [CommGroup G] (g gc gu : G) (h2 : gc * g⁻¹ * gu = 1) : g = gc * gu := by
  calc g = g * (gc * g⁻¹ * gu) := by rw [h2, mul_one]
    _ = gc * gu := by
      rw [mul_comm gc g⁻¹, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]

/-- Avoiding two square classes (there are at least four). -/
lemma t_avoid (u c : Kv) (hu : u ≠ 0) (hc : c ≠ 0) :
    ∃ e : Kv, e ≠ 0 ∧ ¬ IsSquare (e * u) ∧ ¬ IsSquare (c / e * u) := by
  classical
  set U : Kvˣ := Units.mk0 u hu
  set C : Kvˣ := Units.mk0 c hc
  set gu : SqDual.SqCl Kv := QuotientGroup.mk U
  set gc : SqDual.SqCl Kv := QuotientGroup.mk C
  have key : ∃ g : SqDual.SqCl Kv, g * gu ≠ 1 ∧ gc * g⁻¹ * gu ≠ 1 := by
    by_contra h
    push Not at h
    have hsurj : Function.Surjective (fun b : Bool => if b then gu⁻¹ else gc * gu) := by
      intro g
      by_cases h1 : g * gu = 1
      · exact ⟨true, by simpa using (eq_inv_of_mul_eq_one_left h1).symm⟩
      · have h2 := h g h1
        refine ⟨false, ?_⟩
        have : g = gc * gu := t_grp_aux g gc gu h2
        simp [this]
    have hle := Nat.card_le_card_of_surjective _ hsurj
    have h4 : 4 ≤ Nat.card (SqDual.SqCl Kv) := LocalRankFive.four_le_card_sqCl v
    simp at hle
    omega
  obtain ⟨g, hg1, hg2⟩ := key
  obtain ⟨E, rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨E.val, E.ne_zero, ?_, ?_⟩
  · intro hsq
    apply hg1
    have := (SqDual.mk_eq_one_iff_isSquare Kv (E * U)).2 (by simpa [U] using hsq)
    simpa [gu] using this
  · intro hsq
    apply hg2
    have := (SqDual.mk_eq_one_iff_isSquare Kv (C * E⁻¹ * U)).2 (by
      simpa [U, C, div_eq_mul_inv] using hsq)
    simpa [gu, gc] using this

/-- Surjectivity of the spinor norm from a representation of every class as `Q x * Q y`. -/
lemma t_surj_of_prod (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h : ∀ c : Kv, c ≠ 0 → ∃ x y : V, Q x ≠ 0 ∧ Q y ≠ 0 ∧ Q x * Q y = c) :
    Function.Surjective (spinorNormHom Q hQ) := by
  intro g
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective (s := (powMonoidHom 2 : Kvˣ →* Kvˣ).range) g
  obtain ⟨x, y, hx, hy, hxy⟩ := h u u.ne_zero
  refine ⟨⟨_, symmetry_mul_mem_orthPlus Q hx hy⟩, ?_⟩
  rw [spinorNormHom_apply Q hQ (hasSpinorNorm_symmetry_mul Q hx hy), hxy,
    Sp55.sqClassOf_of_ne_zero' u.ne_zero]
  have e : Units.mk0 (u : Kv) u.ne_zero = u := Units.ext rfl
  rw [e]
  rfl

end S95

/-- **$\theta(O^+_n) = \dot F/\dot F^2$ for $n \ge 3$** (O'Meara 1973, §95, p. 284, from 91:6): over a local field
the spinor norm of a regular space of dimension $n \ge 3$ is surjective. -/
@[kb "omeara1963" "§95, p. 284 (O⁺_n/O'_n ≅ Ḟ/Ḟ² for n ≥ 3)"]
theorem spinorNormHom_surjective_local (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : 3 ≤ finrank (v.adicCompletion F) V) : Function.Surjective (spinorNormHom Q hQ) := by
  by_cases hiso : ∃ x : V, x ≠ 0 ∧ Q x = 0
  · exact spinorNormHom_surjective_of_isotropic Q hQ hiso
  have hQa : Q.Anisotropic := fun x hx => by
    by_contra h; exact hiso ⟨x, h, hx⟩
  have h4 : finrank (v.adicCompletion F) V ≤ 4 := by
    by_contra h5
    exact hiso (S95.exists_isotropic_of_five_le v Q hQ (by omega))
  by_cases hn4 : 4 ≤ finrank (v.adicCompletion F) V
  · refine S95.t_surj_of_prod v Q hQ fun c hc => ?_
    obtain ⟨x, hx⟩ := S95.exists_Q_eq_of_four_le v Q hQ hn4 c
    obtain ⟨y, hy⟩ := S95.exists_Q_eq_of_four_le v Q hQ hn4 1
    exact ⟨x, y, by rw [hx]; exact hc, by rw [hy]; exact one_ne_zero, by rw [hx, hy, mul_one]⟩
  have h3 : finrank (v.adicCompletion F) V = 3 := by omega
  obtain ⟨e, ho, hne⟩ := S95.t_orth_basis v Q hQ h3
  set P : v.adicCompletion F := Q (e 0) * Q (e 1) * Q (e 2) with hP
  have hP0 : P ≠ 0 := mul_ne_zero (mul_ne_zero (hne 0) (hne 1)) (hne 2)
  refine S95.t_surj_of_prod v Q hQ fun c hc => ?_
  obtain ⟨ε, hε0, hε1, hε2⟩ := S95.t_avoid v (-P) c (neg_ne_zero.2 hP0) hc
  have hrep : ∀ α : v.adicCompletion F, α ≠ 0 → ¬ IsSquare (-P * α) → ∃ x : V, Q x = α := by
    intro α hα hns
    refine S95.t_rep3 v Q hQa e ho hne hα ?_
    intro hsq; apply hns
    have : -P * α = Q (e 0) * Q (e 1) * Q (e 2) * (-α) := by rw [hP]; ring
    rwa [this]
  obtain ⟨x, hx⟩ := hrep ε hε0 (by rwa [mul_comm])
  obtain ⟨y, hy⟩ := hrep (c / ε) (div_ne_zero hc hε0) (by rwa [mul_comm])
  exact ⟨x, y, by rw [hx]; exact hε0, by rw [hy]; exact div_ne_zero hc hε0, by
    rw [hx, hy]; field_simp⟩

/-- **$O^+_n/O'_n \cong \dot F/\dot F^2$** (O'Meara 1973, §95, p. 284): over a local field, for $n \ge 3$, and for
$n = 2$ with $V$ isotropic. -/
@[kb "omeara1963" "§95, p. 284 (O⁺_n/O'_n ≅ Ḟ/Ḟ², n ≥ 3 or n = 2 isotropic)"]
theorem orthPlus_quotient_equiv_local (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : 3 ≤ finrank (v.adicCompletion F) V ∨
      (finrank (v.adicCompletion F) V = 2 ∧ ∃ x : V, x ≠ 0 ∧ Q x = 0)) :
    Nonempty ((orthPlus Q ⧸ (spinorNormHom Q hQ).ker) ≃* Lattices.SqClass (v.adicCompletion F)) := by
  rcases hn with h | ⟨-, hiso⟩
  · exact ⟨QuotientGroup.quotientKerEquivOfSurjective _ (spinorNormHom_surjective_local v Q hQ h)⟩
  · exact orthPlus_quotient_equiv_of_isotropic Q hQ hiso

/-- **$n = 2$, $V$ anisotropic** (O'Meara 1973, §95, p. 284: "one can use Example 63:15 to show that $O^+_n/O'_n$
is isomorphic to a subgroup of index $2$ in $\dot F/\dot F^2$"): the image $\theta(O^+_2)$, which is isomorphic to
$O^+_2/O'_2$ by `orthPlus_quotient_equiv_range`, has index $2$ in $\dot F/\dot F^2$. -/
@[kb "omeara1963" "§95, p. 284 (O⁺₂/O'₂ is a subgroup of index 2 in Ḟ/Ḟ², V anisotropic binary)"]
theorem spinorNormHom_range_index_binary (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : finrank (v.adicCompletion F) V = 2) (han : Q.Anisotropic) :
    (spinorNormHom Q hQ).range.index = 2 := by
  classical
  obtain ⟨e, ho, hne⟩ := S95.t_orth_basis v Q hQ hn
  set a : v.adicCompletion F := Q (e 0) with ha
  set b : v.adicCompletion F := Q (e 1) with hb
  have ha0 : a ≠ 0 := hne 0
  have hb0 : b ≠ 0 := hne 1
  set d : v.adicCompletion F := -(a * b) with hd
  have hd0 : d ≠ 0 := neg_ne_zero.2 (mul_ne_zero ha0 hb0)
  have hdns : ¬ IsSquare d := S95.t_not_square v Q han e ho hne
  set y : SqDual.SqCl (v.adicCompletion F) := QuotientGroup.mk (Units.mk0 d hd0) with hy
  -- the index-two subgroup
  let S0 : Subgroup (SqDual.SqCl (v.adicCompletion F)) :=
    { carrier := {g | SqDual.hilbCl (v.adicCompletion F) g y = 1}
      mul_mem' := by
        intro g g' hg hg'
        show SqDual.hilbCl (v.adicCompletion F) (g * g') y = 1
        rw [SqDual.hilbCl_mul_fin]
        have h1 : SqDual.hilbCl (v.adicCompletion F) g y = 1 := hg
        have h2 : SqDual.hilbCl (v.adicCompletion F) g' y = 1 := hg'
        rw [h1, h2]; norm_num
      one_mem' := SqDual.hilbCl_one_left _ _
      inv_mem' := by
        intro g hg
        show SqDual.hilbCl (v.adicCompletion F) g⁻¹ y = 1
        have h1 : SqDual.hilbCl (v.adicCompletion F) g y = 1 := hg
        have h2 := SqDual.hilbCl_mul_fin v g g⁻¹ y
        rw [mul_inv_cancel, SqDual.hilbCl_one_left, h1, one_mul] at h2
        exact h2.symm }
  let ψ : Lattices.SqClass (v.adicCompletion F) →* SqDual.SqCl (v.adicCompletion F) :=
    { toFun := fun g => g
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let S : Subgroup (Lattices.SqClass (v.adicCompletion F)) := S0.comap ψ
  have hmem : ∀ g, g ∈ S ↔ SqDual.hilbCl (v.adicCompletion F) (ψ g) y = 1 := fun g => Iff.rfl
  have hrange : (spinorNormHom Q hQ).range = S := by
    rw [spinorNormHom_range_of_finrank_le_three Q hQ (by omega)]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨x, x', hx, hx', rfl⟩
      rw [SetLike.mem_coe, hmem, Sp55.sqClassOf_of_ne_zero' (mul_ne_zero hx hx')]
      show SqDual.hilbCl (v.adicCompletion F) (QuotientGroup.mk (Units.mk0 _ _)) y = 1
      rw [hy]
      rw [SqDual.hilbCl_mk]
      simp only [Units.val_mk0]
      rw [LocalRankFive.hs_mul_left v hx hx' hd0]
      have h1 := S95.t_hs_value v Q e ho hne hx
      have h2 := S95.t_hs_value v Q e ho hne hx'
      rw [← ha, ← hb] at h1 h2
      rw [← hd] at h1 h2
      rw [h1, h2]
      rcases LocalRankFive.hs_pm v a b with h | h <;> rw [h] <;> norm_num
    · intro g hg
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective (s := (powMonoidHom 2 : (v.adicCompletion F)ˣ →* _).range) g
      have hu : hilbertSymbol (v.adicCompletion F) (u : v.adicCompletion F) d = 1 := by
        have : SqDual.hilbCl (v.adicCompletion F) (QuotientGroup.mk u) y = 1 := (hmem _).1 hg
        rw [hy, SqDual.hilbCl_mk] at this
        exact this
      have had : hilbertSymbol (v.adicCompletion F) a d = hilbertSymbol (v.adicCompletion F) a b := by
        have : d = (-a) * b := by rw [hd]; ring
        rw [this, LocalRankFive.hs_mul_right v ha0 (neg_ne_zero.2 ha0) hb0, hilbertSymbol_self_neg, one_mul]
      have hau : a * (u : v.adicCompletion F) ≠ 0 := mul_ne_zero ha0 u.ne_zero
      obtain ⟨x, hx⟩ := S95.t_value_of_hs v Q e ho hne hau (by
        rw [← hd, LocalRankFive.hs_mul_left v ha0 u.ne_zero hd0, had, hu, mul_one])
      have hx0 : Q x ≠ 0 := by rw [hx]; exact hau
      have heq : Lattices.sqClassOf (Q x * Q (e 0)) = QuotientGroup.mk u := by
        have : Q x * Q (e 0) = (u : v.adicCompletion F) * a ^ 2 := by rw [hx, ← ha]; ring
        rw [this, Sp55.sqClassOf_mul' u.ne_zero (pow_ne_zero 2 ha0),
          (Sp55.sqClassOf_eq_one_iff' (pow_ne_zero 2 ha0)).2 ⟨a, sq a⟩, mul_one,
          Sp55.sqClassOf_of_ne_zero' u.ne_zero,
          show Units.mk0 (u : v.adicCompletion F) u.ne_zero = u from Units.ext rfl]
        rfl
      show _ ∈ Subgroup.closure _
      have hmk : (QuotientGroup.mk u : Lattices.SqClass (v.adicCompletion F)) = Lattices.sqClassOf (Q x * Q (e 0)) :=
        heq.symm
      rw [hmk]
      exact Subgroup.subset_closure ⟨x, e 0, hx0, hne 0, rfl⟩
  rw [hrange, Subgroup.index_eq_two_iff]
  obtain ⟨xx, hxx0, hxx⟩ := LocalRankFive.exists_hs_neg_one v hd0 hdns
  have hgx : SqDual.hilbCl (v.adicCompletion F) (QuotientGroup.mk (Units.mk0 xx hxx0)) y = -1 := by
    rw [hy, SqDual.hilbCl_mk]; exact hxx
  refine ⟨Lattices.SqClass.mk (Units.mk0 xx hxx0), fun g => ?_⟩
  have hψm : ∀ g g' : Lattices.SqClass (v.adicCompletion F), ψ (g * g') = ψ g * ψ g' := fun _ _ => rfl
  rw [hmem, hmem, hψm, SqDual.hilbCl_mul_fin]
  have hgx' : SqDual.hilbCl (v.adicCompletion F)
      (ψ (Lattices.SqClass.mk (Units.mk0 xx hxx0))) y = -1 := hgx
  rw [hgx']
  rcases SqDual.hilbCl_pm (v.adicCompletion F) (ψ g) y with h | h <;> rw [h] <;> simp

end QuadFormsKB.OMeara
