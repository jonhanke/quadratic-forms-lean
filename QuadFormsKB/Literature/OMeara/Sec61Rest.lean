/-
# O'Meara §61: the remaining statements of the real case

**Setting** (as in `Sec61.lean`, `Sec55.lean`). O'Meara (1973 printing, §61, pp. 154-157) works over a real complete
field, topologically isomorphic to $\mathbb R$ (§12), so everything is stated over `ℝ`. $(V, Q)$ is a
finite-dimensional real quadratic space (`QuadraticForm ℝ V`); *regular* means `Q.radical = ⊥` (equivalent to
`(QuadraticMap.associated Q).Nondegenerate`, the form used in `Sec55.lean`). The subgroups $O_n^+$, $O_n'$ of
`Sec55.lean` are `orthPlus Q`, `orthPrime Q`, and the index $(O_n^+ : O_n')$ is
`(orthPrime Q).relIndex (orthPlus Q)`. $\dot F^{2}$ is the range of the squaring homomorphism
`(powMonoidHom 2 : ℝˣ →* ℝˣ)`.

**Proves**
* 61.r2 (p. 154): `real_units_sq_index` ($(\dot{\mathbb R} : \dot{\mathbb R}^2) = 2$ with representatives $\pm 1$),
  `real_sq_trichotomy` (every real number is exactly one of a nonzero square, $0$, minus a nonzero square) and
  `quadraticForm_value_trichotomy` (the same for every value $Q(x)$);
* 61.r8 (p. 155): `real_sq_add_sq_ne_zero` (a sum of two nonzero squares is a nonzero square);
* 61.r16 (p. 155): `posDef_restrict_equivalent_one` (every positive definite subspace is regular and
  isometric to $\langle 1\rangle \perp \cdots \perp \langle 1\rangle$) and `maximal_posDef_subspace` (the book's
  statement for a maximal positive definite subspace, which then has dimension $\operatorname{ind}^+V$);
* 61.r27 (p. 157): `relIndex_orthPrime_orthPlus_of_isIndefinite` ($(O_n^+ : O_n') = 2$ for indefinite $V$) and
  `relIndex_orthPrime_orthPlus_of_isDefinite` ($=1$ for definite $V$).

**Deviations from the book.** 61.r16 is stated for every positive definite subspace (the maximality of $P$ is not
needed for regularity and the normal form; it is used only for the dimension count `maximal_posDef_subspace`).
In 61.r27 the book's $n$-ary space has $n \ge 1$ implicitly; the definite case holds also for $V = 0$.
-/
import QuadFormsKB.Literature.OMeara.Sec61
import QuadFormsKB.Literature.OMeara.Sec55

open QuadraticMap QuadraticForm Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

/-! ### 61.r2: the square classes of $\mathbb R$ -/

private lemma isSquare_real_iff (r : ℝ) : IsSquare r ↔ 0 ≤ r :=
  ⟨fun ⟨a, h⟩ => by rw [h]; exact mul_self_nonneg a, fun h => ⟨Real.sqrt r, (Real.mul_self_sqrt h).symm⟩⟩

private lemma mem_range_sq_iff (x : ℝˣ) :
    x ∈ (powMonoidHom 2 : ℝˣ →* ℝˣ).range ↔ 0 < (x : ℝ) := by
  constructor
  · rintro ⟨y, rfl⟩
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val]
    have := y.ne_zero
    positivity
  · intro h
    refine ⟨Units.mk0 (Real.sqrt x) (Real.sqrt_pos.2 h).ne', ?_⟩
    ext
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [_root_.sq]; exact Real.mul_self_sqrt h.le

/-- **$(\dot{\mathbb R} : \dot{\mathbb R}^{2}) = 2$ with representatives $\pm 1$** (O'Meara 1963, §61A, p. 154): the
subgroup $\dot{\mathbb R}^{2}$ of squares of the unit group $\dot{\mathbb R} = \mathbb R^\times$ has index $2$, and $1$
and $-1$ lie in different cosets: $-1 \notin \dot{\mathbb R}^{2}$ and every $x$ lies in exactly one of
$\dot{\mathbb R}^{2}$, $-\dot{\mathbb R}^{2}$. -/
@[kb "omeara1963" "§61A, p. 154 (index of the squares of ℝˣ is 2, representatives ±1)"]
theorem real_units_sq_index :
    (powMonoidHom 2 : ℝˣ →* ℝˣ).range.index = 2 ∧
      (-1 : ℝˣ) ∉ (powMonoidHom 2 : ℝˣ →* ℝˣ).range ∧
      ∀ x : ℝˣ, Xor (x ∈ (powMonoidHom 2 : ℝˣ →* ℝˣ).range) (-x ∈ (powMonoidHom 2 : ℝˣ →* ℝˣ).range) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.index_eq_two_iff]
    refine ⟨-1, fun b => ?_⟩
    rw [mem_range_sq_iff, mem_range_sq_iff]
    have : (b * -1 : ℝˣ) = -b := by simp
    rw [this]
    simp only [Units.val_neg]
    rcases lt_or_gt_of_ne b.ne_zero with h | h
    · left; exact ⟨by linarith, by linarith⟩
    · right; exact ⟨by linarith, by linarith⟩
  · rw [mem_range_sq_iff]; simp
  · intro x
    rw [mem_range_sq_iff, mem_range_sq_iff]
    simp only [Units.val_neg]
    rcases lt_or_gt_of_ne x.ne_zero with h | h
    · right; exact ⟨by linarith, by linarith⟩
    · left; exact ⟨by linarith, by linarith⟩

/-- **Trichotomy of real numbers** (O'Meara 1963, §61A, p. 154): every real $r$ satisfies exactly one of
$r \in \dot{\mathbb R}^{2}$ (a nonzero square), $r = 0$, $r \in -\dot{\mathbb R}^{2}$ (minus a nonzero square). -/
@[kb "omeara1963" "§61A, p. 154 (exactly one of r ∈ Ḟ², r = 0, r ∈ −Ḟ²)"]
theorem real_sq_trichotomy (r : ℝ) :
    ((r ≠ 0 ∧ IsSquare r) ∨ r = 0 ∨ (r ≠ 0 ∧ IsSquare (-r))) ∧
      ¬ ((r ≠ 0 ∧ IsSquare r) ∧ r = 0) ∧
      ¬ ((r ≠ 0 ∧ IsSquare r) ∧ (r ≠ 0 ∧ IsSquare (-r))) ∧
      ¬ (r = 0 ∧ (r ≠ 0 ∧ IsSquare (-r))) := by
  simp only [isSquare_real_iff]
  rcases lt_trichotomy r 0 with h | h | h
  · refine ⟨Or.inr (Or.inr ⟨h.ne, by linarith⟩), ?_, ?_, ?_⟩ <;> intro hh <;> simp_all <;> linarith
  · subst h; simp
  · refine ⟨Or.inl ⟨h.ne', h.le⟩, ?_, ?_, ?_⟩ <;> intro hh <;> simp_all <;> linarith

/-- **Trichotomy of the values of a real quadratic form** (O'Meara 1963, §61A, p. 154): each $x \in V$ satisfies
exactly one of $Q(x) \in \dot{\mathbb R}^{2}$, $Q(x) = 0$, $Q(x) \in -\dot{\mathbb R}^{2}$. -/
@[kb "omeara1963" "§61A, p. 154 (each x satisfies exactly one of Q(x) ∈ Ḟ², Q(x) = 0, Q(x) ∈ −Ḟ²)"]
theorem quadraticForm_value_trichotomy {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (x : V) :
    ((Q x ≠ 0 ∧ IsSquare (Q x)) ∨ Q x = 0 ∨ (Q x ≠ 0 ∧ IsSquare (-Q x))) ∧
      ¬ ((Q x ≠ 0 ∧ IsSquare (Q x)) ∧ Q x = 0) ∧
      ¬ ((Q x ≠ 0 ∧ IsSquare (Q x)) ∧ (Q x ≠ 0 ∧ IsSquare (-Q x))) ∧
      ¬ (Q x = 0 ∧ (Q x ≠ 0 ∧ IsSquare (-Q x))) :=
  real_sq_trichotomy (Q x)

/-! ### 61.r8: sums of squares -/

/-- **A sum of nonzero squares is a nonzero square** (O'Meara 1963, §61A, p. 155): $\dot{\mathbb R}^{2}$ is closed
under addition. Here $x, y \in \mathbb R$ are nonzero squares (hypotheses `hx`, `hxs`, `hy`, `hys`). -/
@[kb "omeara1963" "§61A, p. 155 (a sum of nonzero squares is a nonzero square)"]
theorem real_sq_add_sq_ne_zero {x y : ℝ} (hx : x ≠ 0) (hxs : IsSquare x) (hy : y ≠ 0) (hys : IsSquare y) :
    x + y ≠ 0 ∧ IsSquare (x + y) := by
  rw [isSquare_real_iff] at hxs hys ⊢
  have hx' : 0 < x := lt_of_le_of_ne hxs (Ne.symm hx)
  have hy' : 0 < y := lt_of_le_of_ne hys (Ne.symm hy)
  exact ⟨by linarith, by linarith⟩

/-! ### 61.r16: maximal positive definite subspaces -/

section PosDef

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

private lemma wss_equiv_of_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    (w : ι → ℝ) (w' : ι' → ℝ) (h : ∀ i, w' (e i) = w i) :
    (weightedSumSquares ℝ w).Equivalent (weightedSumSquares ℝ w') := by
  refine ⟨{ toLinearEquiv := LinearEquiv.funCongrLeft ℝ ℝ e.symm, map_app' := ?_ }⟩
  intro x
  simp only [weightedSumSquares_apply]
  rw [← Equiv.sum_comp e]
  simp [h, LinearEquiv.funCongrLeft_apply]

/-- **A positive definite subspace is regular and $\cong \langle 1\rangle \perp \cdots \perp \langle 1\rangle$**
(O'Meara 1963, §61A, p. 155): if $P \subseteq V$ is a subspace on which $Q$ is positive definite
(`hP : (Q.restrict P).PosDef`), then $P$ is regular and $Q|_P$ is isometric to the sum of $\dim P$ squares
$x_1^2 + \cdots + x_m^2$, $m = \dim P$. *Update (generalization):* O'Meara states this for a maximal positive definite
subspace; it holds for every positive definite subspace. -/
@[kb "omeara1963" "§61A, p. 155 (a positive definite subspace is regular and ≅ ⟨1⟩ ⊥ ⋯ ⊥ ⟨1⟩)"]
theorem posDef_restrict_equivalent_one (Q : QuadraticForm ℝ V) (P : Submodule ℝ V)
    (hP : (Q.restrict P).PosDef) :
    (Q.restrict P).radical = ⊥ ∧
      (Q.restrict P).Equivalent
        (weightedSumSquares ℝ (fun _ : Fin (finrank ℝ P) => (1 : ℝ))) := by
  have hreg : (Q.restrict P).radical = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact hP.anisotropic x ((QuadraticMap.mem_radical_iff'.1 hx).1)
  refine ⟨hreg, ?_⟩
  have hpos : sigPos (Q.restrict P) = finrank ℝ P := (posDef_iff_sigPos_eq _).1 hP
  have hsum := sigPos_add_sigNeg (Q.restrict P) hreg
  have hneg : sigNeg (Q.restrict P) = 0 := by omega
  refine (exists_equivalent_one_neg_one (Q.restrict P) hreg).trans ?_
  let e : Fin (sigPos (Q.restrict P)) ⊕ Fin (sigNeg (Q.restrict P)) ≃ Fin (finrank ℝ P) :=
    finSumFinEquiv.trans (finCongr hsum)
  refine wss_equiv_of_equiv e _ _ ?_
  intro i
  rcases i with i | i
  · rfl
  · exact absurd i.2 (by omega)

/-- **A maximal positive definite subspace** (O'Meara 1963, §61A, p. 155): let $V$ be a regular real quadratic space
and $P$ a maximal positive definite subspace (positive definite, and contained in no larger positive definite
subspace). Then $P$ is regular, $P \cong \langle 1\rangle \perp \cdots \perp \langle 1\rangle$ with
$\operatorname{ind}^+V$ summands. -/
@[kb "omeara1963" "§61A, p. 155 (a maximal positive definite subspace is regular and ≅ ⟨1⟩ ⊥ ⋯ ⊥ ⟨1⟩)"]
theorem maximal_posDef_subspace (Q : QuadraticForm ℝ V) (hQ : Q.radical = ⊥) (P : Submodule ℝ V)
    (hP : (Q.restrict P).PosDef)
    (hmax : ∀ P' : Submodule ℝ V, P ≤ P' → (Q.restrict P').PosDef → P' = P) :
    (Q.restrict P).radical = ⊥ ∧ finrank ℝ P = sigPos Q ∧
      (Q.restrict P).Equivalent (weightedSumSquares ℝ (fun _ : Fin (sigPos Q) => (1 : ℝ))) := by
  obtain ⟨hreg, heq⟩ := posDef_restrict_equivalent_one Q P hP
  have hdim := finrank_eq_sigPos_of_maximal Q hQ P hP hmax
  refine ⟨hreg, hdim, ?_⟩
  have : (weightedSumSquares ℝ (fun _ : Fin (finrank ℝ P) => (1 : ℝ))).Equivalent
      (weightedSumSquares ℝ (fun _ : Fin (sigPos Q) => (1 : ℝ))) :=
    wss_equiv_of_equiv (finCongr hdim) _ _ (fun _ => rfl)
  exact heq.trans this

end PosDef

/-! ### 61.r27: $(O_n^+ : O_n')$ over $\mathbb R$ -/

section Index

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

private lemma nondeg_of_radical (Q : QuadraticForm ℝ V) (hQ : Q.radical = ⊥) :
    (QuadraticMap.associated Q).Nondegenerate :=
  QuadraticMap.nondegenerate_associated_iff.mpr (QuadraticMap.nondegenerate_iff_radical_eq_bot.mpr hQ)

private lemma orthPrime_eq_orthPlus_of_posDef (Q : QuadraticForm ℝ V) (hQ : Q.radical = ⊥)
    (hpos : Q.PosDef) : orthPrime Q = orthPlus Q := by
  have hnd := nondeg_of_radical Q hQ
  refine le_antisymm (orthPrime_le_orthPlus Q) fun σ hσ => ?_
  obtain ⟨c, -, hc⟩ := exists_hasSpinorNorm_of_mem_orth Q hnd hσ.1
  refine (mem_orthPrime_iff Q hnd ⟨c, hc⟩).2 ⟨hσ, fun d hd => ?_⟩
  obtain ⟨l, hl, -, s, hs, hprod⟩ := hd
  have hpos' : 0 < (l.map Q).prod := by
    apply List.prod_pos
    intro a ha
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ha
    exact hpos u (fun h => hl u hu (by rw [h]; simp))
  have hd0 : 0 ≤ d := by
    have hpd : 0 < d * s ^ 2 := by rw [← hprod]; exact hpos'
    by_contra hneg
    push Not at hneg
    have : d * s ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le (sq_nonneg s)
    linarith
  exact (isSquare_real_iff d).2 hd0

/-- **$(O_n^+ : O_n') = 1$ for definite $V$** (O'Meara 1963, §61C, p. 157): over $\mathbb R$, if $V$ is a regular
definite quadratic space, then $O_n' = O_n^+$. (For positive definite $V$ every spinor norm is a product of
positive values $Q(u_i)$, hence a square; a negative definite space is reduced to this case by `orthPrime_smul`,
`orthPlus_smul` with the scalar $-1$.) -/
@[kb "omeara1963" "§61C, p. 157 ((O⁺_n : O'_n) = 1 if V is definite)"]
theorem relIndex_orthPrime_orthPlus_of_isDefinite (Q : QuadraticForm ℝ V) (hQ : Q.radical = ⊥)
    (hdef : IsDefinite Q) : (orthPrime Q).relIndex (orthPlus Q) = 1 := by
  have h : orthPrime Q = orthPlus Q := by
    rcases hdef with hpos | hneg
    · exact orthPrime_eq_orthPlus_of_posDef Q hQ hpos
    · have e : ((-1 : ℝ) • Q) = -Q := by ext x; simp
      have hneg' : ((-1 : ℝ) • Q).PosDef := by rw [e]; exact hneg
      have hQ' : ((-1 : ℝ) • Q).radical = ⊥ := by
        rw [e]
        rw [show (-Q).radical = Q.radical by ext x; simp [QuadraticMap.mem_radical_iff'], hQ]
      have := orthPrime_eq_orthPlus_of_posDef ((-1 : ℝ) • Q) hQ' hneg'
      rwa [orthPrime_smul Q (by norm_num), orthPlus_smul Q (by norm_num)] at this
  rw [h, Subgroup.relIndex_self]

/-- **$(O_n^+ : O_n') = 2$ for indefinite $V$** (O'Meara 1963, §61C, p. 157, by 55:2): over $\mathbb R$, if $V$ is a
regular indefinite quadratic space, then $V$ is isotropic (`isIndefinite_iff_not_anisotropic`), so by 55:6a the
spinor norm induces $O_n^+/O_n' \cong \dot{\mathbb R}/\dot{\mathbb R}^{2}$, a group of order $2$
(`real_units_sq_index`). -/
@[kb "omeara1963" "§61C, p. 157 ((O⁺_n : O'_n) = 2 if V is indefinite)"]
theorem relIndex_orthPrime_orthPlus_of_isIndefinite (Q : QuadraticForm ℝ V) (hQ : Q.radical = ⊥)
    (hind : IsIndefinite Q) : (orthPrime Q).relIndex (orthPlus Q) = 2 := by
  have hnd := nondeg_of_radical Q hQ
  have hiso : ∃ x : V, x ≠ 0 ∧ Q x = 0 := by
    have := (isIndefinite_iff_not_anisotropic Q).1 hind
    simp only [QuadraticMap.Anisotropic, not_forall] at this
    obtain ⟨x, hx, hx0⟩ := this
    exact ⟨x, hx0, hx⟩
  obtain ⟨e⟩ := orthPlus_quotient_equiv_of_isotropic Q hnd hiso
  rw [Subgroup.relIndex, ← ker_spinorNormHom Q hnd, Subgroup.index]
  rw [Nat.card_congr e.toEquiv]
  show Nat.card (Lattices.SqClass ℝ) = 2
  have := real_units_sq_index.1
  rw [Subgroup.index] at this
  exact this

end Index

end QuadFormsKB.OMeara
