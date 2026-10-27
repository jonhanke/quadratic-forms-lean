/-
# O'Meara §92: lattices over non-dyadic local fields (orthogonal bases, unimodular lattices)

**Setting** (as in `Sec82.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$, a
quadratic space $(V, Q)$ over $F$, O'Meara's bilinear form $B$ = `bil Q`, lattices = `Submodule R V`.
*Non-dyadic* (O'Meara 1963, §92, p. 246): $2$ is a unit of $R$ (`IsUnit (2 : R)`). For the results that need the local
field (the binary step: every unit is a sum $\varepsilon_1x^2 + \varepsilon_2y^2$), $R$ is moreover complete
(`IsAdicComplete (maximalIdeal R) R`) with finite residue field, the setting of `Lattices.Nbr.exists_binary_one_dvr`.

**Proves**
* `normIdeal_eq_scale` (p. 246): $\mathfrak nL = \mathfrak sL$ over a non-dyadic field;
* `exists_orthogonal_basis` (p. 246): every regular lattice has an orthogonal base;
* `exists_basis_diag_of_isUnimodular` (**92:1**): a unimodular lattice is
  $L \cong \langle 1\rangle \perp \cdots \perp \langle 1\rangle \perp \langle\varepsilon\rangle$ with $\varepsilon$ a unit;
* `isometricLat_iff_sameDisc` and `exists_nonsquare_unit` (**92:1a**: there are essentially two unimodular lattices of
  given rank, distinguished by the discriminant in $\mathfrak u/\mathfrak u^2$, which has two classes);
* `units_subset_Q_image`, `Q_image_eq` (**92:1b**): $Q(L) \supseteq \mathfrak u$ if $\dim L \ge 2$, and
  $Q(L) = \mathfrak o$ if $\dim L \ge 3$.
-/
import QuadFormsKB.Literature.OMeara.Sec82Isom
import QuadFormsKB.Lattices.UnimodularDVR

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- A finite family that is independent and spans $L$ gives a base of $L$ indexed by
$\{0, \dots, \operatorname{rank} L - 1\}$. -/
theorem exists_basis_of_family {L : Submodule R V} {m : ℕ} {x : Fin m → V} (hli : LinearIndependent R x)
    (hspan : span R (Set.range x) = L) :
    ∃ h : finrank R L = m, ∃ b : Basis (Fin (finrank R L)) R L, ∀ i, (b i : V) = x (Fin.cast h i) := by
  let b₀ := (Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  have h : finrank R L = m := by rw [finrank_eq_card_basis b₀, Fintype.card_fin]
  refine ⟨h, b₀.reindex (finCongr h.symm), fun i => ?_⟩
  simp [b₀, Basis.reindex_apply]

/-- If $B(v, z_k) = 0$ for all $k$, then $B(v, w) = 0$ for all $w$ in the span of the $z_k$. -/
theorem bil_eq_zero_of_mem_span {ι : Type*} {z : ι → V} {v w : V} (h : ∀ k, bil Q v (z k) = 0)
    (hw : w ∈ span R (Set.range z)) : bil Q v w = 0 := by
  refine span_induction (p := fun w _ => bil Q v w = 0) ?_ (by simp [bil]) ?_ ?_ hw
  · rintro _ ⟨k, rfl⟩; exact h k
  · intro a b _ _ ha hb; rw [bil_add_right, ha, hb, add_zero]
  · intro c a _ ha; rw [bil_rsmul_right, ha, mul_zero]

/-- An orthogonal family of anisotropic vectors is linearly independent. -/
theorem linearIndependent_of_orth {m : ℕ} {x : Fin m → V} (horth : ∀ i j, i ≠ j → bil Q (x i) (x j) = 0)
    (hQ : ∀ i, Q (x i) ≠ 0) : LinearIndependent R x := by
  classical
  refine linearIndependent_of_det_gram_ne_zero Q ?_
  have : gram Q x = Matrix.diagonal fun i => Q (x i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [gram]
    · simp [gram, Matrix.diagonal_apply_ne _ hij, horth i j hij]
  rw [this, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => hQ i

end Domain

section NonDyadic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Norm equals scale over a non-dyadic field** (O'Meara 1963, §92, p. 246): $2\,\mathfrak sL \subseteq
\mathfrak nL \subseteq \mathfrak sL$ and $2$ is a unit, so $\mathfrak nL = \mathfrak sL$. -/
@[kb "omeara1963" "§92, p. 246 (nL = sL over non-dyadic fields)"]
theorem normIdeal_eq_scale (h2 : IsUnit (2 : R)) (L : Submodule R V) : normIdeal Q L = scale Q L := by
  refine le_antisymm (normIdeal_le_scale Q L) fun c hc => ?_
  obtain ⟨u, hu⟩ := h2
  have h := two_mul_mem_normIdeal Q hc
  have : c = (↑u⁻¹ : R) • (2 * c) := by
    rw [Algebra.smul_def, ← mul_assoc, ← map_ofNat (algebraMap R F) 2, ← hu, ← map_mul, Units.inv_mul,
      map_one, one_mul]
  rw [this]; exact smul_mem _ _ h

/-- **Orthogonal families** (O'Meara 1963, §92, p. 246): over a non-dyadic field a regular lattice $L$ is spanned by
an orthogonal family of anisotropic vectors (split off $\mathfrak ox$ with $Q(x)\mathfrak o = \mathfrak nL = \mathfrak sL$
and repeat). -/
theorem exists_orth_family (h2 : IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L) :
    ∃ m, ∃ x : Fin m → V, (∀ i, x i ∈ L) ∧ span R (Set.range x) = L ∧
      (∀ i j, i ≠ j → bil Q (x i) (x j) = 0) ∧ ∀ i, Q (x i) ≠ 0 := by
  induction h : finrank R L using Nat.strong_induction_on generalizing L with
  | _ n ih =>
  by_cases hne : L = ⊥
  · exact ⟨0, Fin.elim0, fun i => i.elim0, by simp [hne], fun i => i.elim0, fun i => i.elim0⟩
  obtain ⟨u, hu, hn⟩ := exists_normIdeal_eq Q hfg
  rw [normIdeal_eq_scale Q h2] at hn
  have hQu : Q u ≠ 0 := by
    intro h0; exact scale_ne_bot Q hreg hne (by rw [hn, h0]; simp)
  let v : Fin 1 → V := fun _ => u
  have hG : gram Q v = Q u • (1 : Matrix (Fin 1) (Fin 1) R).map (algebraMap R F) := by
    ext i j; fin_cases i; fin_cases j; simp [v, gram]
  obtain ⟨hmod, hrk1⟩ := isModular_span_of_gram Q hQu (by simp) hG
  have hJ : span R (Set.range v) = R ∙ u := by simp [v, Set.range_const]
  rw [hJ] at hmod hrk1
  have hJL : R ∙ u ≤ L := (span_singleton_le_iff_mem _ _).mpr hu
  obtain ⟨K, hK⟩ := splits_of_isModular_of_scale_eq Q hJL hmod (fg_span_singleton u) hn
  have hKL : K ≤ L := hK.sup_eq ▸ le_sup_right
  have hKfg : K.FG := FG.of_le hfg hKL
  have hKreg : IsRegular Q K := IsOrthSum.isRegular_right Q hK hreg
  have hrk := isOrthSum_finrank Q hK hfg
  rw [hrk1] at hrk
  obtain ⟨m, y, hyK, hyspan, hyorth, hyQ⟩ := ih (finrank R K) (by simp at hrk; omega) hKfg hKreg rfl
  refine ⟨m + 1, Fin.cons u y, ?_, ?_, ?_, ?_⟩
  · intro i; refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hu
    · simpa using hKL (hyK i)
  · rw [Fin.range_cons, span_insert, hyspan, hK.sup_eq]
  · intro i j hij
    refine Fin.cases (fun hij => ?_) (fun i hij => ?_) i hij
    · refine Fin.cases (fun h => absurd rfl h) (fun j _ => ?_) j hij
      simpa using hK.orth u (mem_span_singleton_self u) (y j) (hyK j)
    · refine Fin.cases (fun _ => ?_) (fun j hij => ?_) j hij
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [bil_comm]; exact hK.orth u (mem_span_singleton_self u) (y i) (hyK i)
      · simpa using hyorth i j (fun h => hij (h ▸ rfl))
  · intro i; refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hQu
    · simpa using hyQ i

/-- **Orthogonal bases** (O'Meara 1963, §92, p. 246): over a non-dyadic local field every regular lattice has an
orthogonal base. -/
@[kb "omeara1963" "§92, p. 246 (every non-zero regular lattice has an orthogonal base)"]
theorem exists_orthogonal_basis (h2 : IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L) :
    ∃ b : Basis (Fin (finrank R L)) R L, (∀ i j, i ≠ j → bil Q (b i : V) (b j : V) = 0) ∧
      ∀ i, Q (b i : V) ≠ 0 := by
  obtain ⟨m, x, -, hspan, horth, hQ⟩ := exists_orth_family Q h2 hfg hreg
  obtain ⟨h, b, hb⟩ := exists_basis_of_family (linearIndependent_of_orth Q horth hQ) hspan
  refine ⟨b, fun i j hij => ?_, fun i => ?_⟩
  · rw [hb, hb]; exact horth _ _ (fun h' => hij (Fin.cast_injective _ h'))
  · rw [hb]; exact hQ _

end NonDyadic

section LocalNonDyadic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (ResidueField R)] [DecidableEq (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

omit [Invertible (2 : F)] in
include F in
/-- **Binary step** (complete non-dyadic discrete valuation ring with finite residue field): for units
$a, b$ there are $s, t$ with $as^2 + bt^2 = 1$ (`Lattices.Nbr.exists_binary_one_dvr`). -/
theorem exists_binary_one (h2 : IsUnit (2 : R)) {a b : R} (ha : IsUnit a) (hb : IsUnit b) :
    ∃ s t : R, a * s ^ 2 + b * t ^ 2 = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have h2' : ¬ π ∣ 2 := fun h => hπ.not_isUnit (isUnit_of_dvd_unit h h2)
  exact Lattices.Nbr.exists_binary_one_dvr hπ h2' ha hb

/-- **Normalizing an orthogonal family of unit length** (the inductive step of 92:1, via the binary step
$\langle a_0, a_1\rangle \cong \langle 1, a_0a_1\rangle$): an orthogonal family $x_0, \dots, x_m$ with
$Q(x_i) = a_i$ units can be replaced by an orthogonal family spanning the same lattice with
$Q = 1, \dots, 1, a_0 \cdots a_m$. -/
theorem exists_normalized_family (h2 : IsUnit (2 : R)) :
    ∀ (m : ℕ) (x : Fin (m + 1) → V) (a : Fin (m + 1) → R), (∀ i, IsUnit (a i)) →
      (∀ i, Q (x i) = algebraMap R F (a i)) → (∀ i j, i ≠ j → bil Q (x i) (x j) = 0) →
      ∃ y : Fin (m + 1) → V, span R (Set.range y) = span R (Set.range x) ∧
        (∀ i j, i ≠ j → bil Q (y i) (y j) = 0) ∧
        ∀ i, Q (y i) = if i = Fin.last m then algebraMap R F (∏ i, a i) else 1 := by
  intro m
  induction m with
  | zero =>
    intro x a _ hQ horth
    refine ⟨x, rfl, horth, fun i => ?_⟩
    fin_cases i
    simp [hQ]
  | succ m ih =>
    intro x a ha hQ horth
    obtain ⟨s, t, hst⟩ := exists_binary_one (F := F) h2 (ha 0) (ha 1)
    have h01 : bil Q (x 0) (x 1) = 0 := horth 0 1 (by simp)
    have h10 : bil Q (x 1) (x 0) = 0 := horth 1 0 (by simp)
    set f₁ := s • x 0 + t • x 1 with hf₁
    set f₂ := (-(a 1 * t)) • x 0 + (a 0 * s) • x 1 with hf₂
    have hQf₁ : Q f₁ = 1 := by
      rw [hf₁, Q_add, Q_rsmul, Q_rsmul, bil_rsmul_left, bil_rsmul_right, h01, hQ, hQ]
      have := congrArg (algebraMap R F) hst
      simp only [map_add, map_mul, map_pow, map_one] at this
      linear_combination this
    have hQf₂ : Q f₂ = algebraMap R F (a 0 * a 1) := by
      rw [hf₂, Q_add, Q_rsmul, Q_rsmul, bil_rsmul_left, bil_rsmul_right, h01, hQ, hQ]
      have := congrArg (algebraMap R F) hst
      simp only [map_add, map_mul, map_pow, map_one, map_neg] at this ⊢
      linear_combination (algebraMap R F (a 0) * algebraMap R F (a 1)) * this
    have hf₁f₂ : bil Q f₁ f₂ = 0 := by
      rw [hf₁, hf₂]
      simp only [bil_add_left, bil_add_right, bil_rsmul_left, bil_rsmul_right, h01, h10, bil_self, hQ,
        map_neg, map_mul]
      ring
    -- orthogonality of `f₁, f₂` to `x_k`, `k ≥ 2`
    have hfx : ∀ (f : V) (c d : R), f = c • x 0 + d • x 1 → ∀ k : Fin m, bil Q f (x k.succ.succ) = 0 := by
      intro f c d hf k
      rw [hf, bil_add_left, bil_rsmul_left, bil_rsmul_left, horth 0 _ (Fin.succ_ne_zero _).symm,
        horth 1 _ (fun h => by
          have := congrArg Fin.val h; simp at this),
        mul_zero, mul_zero, add_zero]
    -- the shorter family `f₂, x₂, …`
    let z : Fin (m + 1) → V := Fin.cons f₂ fun k => x k.succ.succ
    let a' : Fin (m + 1) → R := Fin.cons (a 0 * a 1) fun k => a k.succ.succ
    have ha' : ∀ i, IsUnit (a' i) := by
      intro i; refine Fin.cases ?_ (fun k => ?_) i
      · simpa [a'] using (ha 0).mul (ha 1)
      · simpa [a'] using ha _
    have hQz : ∀ i, Q (z i) = algebraMap R F (a' i) := by
      intro i; refine Fin.cases ?_ (fun k => ?_) i
      · simpa [z, a'] using hQf₂
      · simpa [z, a'] using hQ _
    have horthz : ∀ i j, i ≠ j → bil Q (z i) (z j) = 0 := by
      intro i j hij
      refine Fin.cases (fun hij => ?_) (fun i hij => ?_) i hij
      · refine Fin.cases (fun h => absurd rfl h) (fun j _ => ?_) j hij
        simpa [z] using hfx f₂ _ _ hf₂ j
      · refine Fin.cases (fun _ => ?_) (fun j hij => ?_) j hij
        · simp only [z, Fin.cons_zero, Fin.cons_succ]
          rw [bil_comm]; exact hfx f₂ _ _ hf₂ i
        · simp only [z, Fin.cons_succ]
          exact horth _ _ (fun h => hij (Fin.succ_injective _ h))
    obtain ⟨y', hy'span, hy'orth, hy'Q⟩ := ih z a' ha' hQz horthz
    refine ⟨Fin.cons f₁ y', ?_, ?_, ?_⟩
    · -- spans
      have hpair : (R ∙ f₁) ⊔ (R ∙ f₂) = (R ∙ x 0) ⊔ (R ∙ x 1) := by
        apply le_antisymm
        · refine sup_le ?_ ?_ <;> rw [span_singleton_le_iff_mem]
          · rw [hf₁]; exact add_mem (mem_sup_left (smul_mem _ _ (mem_span_singleton_self _)))
              (mem_sup_right (smul_mem _ _ (mem_span_singleton_self _)))
          · rw [hf₂]; exact add_mem (mem_sup_left (smul_mem _ _ (mem_span_singleton_self _)))
              (mem_sup_right (smul_mem _ _ (mem_span_singleton_self _)))
        · have e0 : x 0 = (a 0 * s) • f₁ + (-t) • f₂ := by
            have : (a 0 * s) • f₁ + (-t) • f₂ = (a 0 * s ^ 2 + a 1 * t ^ 2) • x 0 := by
              rw [hf₁, hf₂]; module
            rw [this, hst, one_smul]
          have e1 : x 1 = (a 1 * t) • f₁ + s • f₂ := by
            have : (a 1 * t) • f₁ + s • f₂ = (a 0 * s ^ 2 + a 1 * t ^ 2) • x 1 := by
              rw [hf₁, hf₂]; module
            rw [this, hst, one_smul]
          refine sup_le ?_ ?_ <;> rw [span_singleton_le_iff_mem]
          · rw [e0]; exact add_mem (mem_sup_left (smul_mem _ _ (mem_span_singleton_self _)))
              (mem_sup_right (smul_mem _ _ (mem_span_singleton_self _)))
          · rw [e1]; exact add_mem (mem_sup_left (smul_mem _ _ (mem_span_singleton_self _)))
              (mem_sup_right (smul_mem _ _ (mem_span_singleton_self _)))
      have hx : span R (Set.range x) =
          (R ∙ x 0) ⊔ ((R ∙ x 1) ⊔ span R (Set.range fun k : Fin m => x k.succ.succ)) := by
        conv_lhs => rw [← Fin.cons_self_tail x, Fin.range_cons, span_insert]
        congr 1
        conv_lhs => rw [show Fin.tail x = Fin.cons (x 1) (fun k : Fin m => x k.succ.succ) by
          rw [← Fin.cons_self_tail (Fin.tail x)]; rfl]
        rw [Fin.range_cons, span_insert]
      rw [Fin.range_cons, span_insert, hy'span, hx, Fin.range_cons, span_insert, ← sup_assoc, hpair,
        sup_assoc]
    · intro i j hij
      have hf₁z : ∀ w ∈ span R (Set.range z), bil Q f₁ w = 0 := by
        intro w hw
        refine bil_eq_zero_of_mem_span Q (fun k => ?_) hw
        refine Fin.cases ?_ (fun k => ?_) k
        · simpa [z] using hf₁f₂
        · simpa [z] using hfx f₁ _ _ hf₁ k
      have hy'mem : ∀ k, y' k ∈ span R (Set.range z) := fun k => hy'span ▸ subset_span ⟨k, rfl⟩
      refine Fin.cases (fun hij => ?_) (fun i hij => ?_) i hij
      · refine Fin.cases (fun h => absurd rfl h) (fun j _ => ?_) j hij
        simpa using hf₁z _ (hy'mem j)
      · refine Fin.cases (fun _ => ?_) (fun j hij => ?_) j hij
        · simp only [Fin.cons_zero, Fin.cons_succ]
          rw [bil_comm]; exact hf₁z _ (hy'mem i)
        · simpa using hy'orth i j (fun h => hij (h ▸ rfl))
    · intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp only [Fin.cons_zero, hQf₁]
        rw [ite_eq_right_iff.mpr (by simp [Fin.ext_iff])]
      · have hprod : ∏ i, a' i = ∏ i, a i := by
          rw [Fin.prod_univ_succ, Fin.prod_univ_succ (fun i => a i), Fin.prod_univ_succ (fun i => a i.succ)]
          simp [a', mul_assoc]
        simp only [Fin.cons_succ, hy'Q k, hprod, ← Fin.succ_last, Fin.succ_inj]

/-- **Proposition 92:1** (O'Meara 1963, p. 246): a unimodular lattice $L$ over a non-dyadic local field has a base
with matrix $\langle 1\rangle \perp \cdots \perp \langle 1 \rangle \perp \langle\varepsilon\rangle$, $\varepsilon$ a unit:
$L \cong \langle 1\rangle \perp \cdots \perp \langle 1\rangle \perp \langle\varepsilon\rangle$. (O'Meara's proof uses
63:20 and 91:2; here the binary step $\langle a, b\rangle \cong \langle 1, ab\rangle$ is applied directly.) -/
@[kb "omeara1963" "§92, 92:1, p. 246"]
theorem exists_basis_diag_of_isUnimodular (h2 : IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG)
    (hL : IsUnimodular Q L) :
    ∃ ε : R, IsUnit ε ∧ ∃ b : Basis (Fin (finrank R L)) R L, ∀ i j,
      bil Q (b i : V) (b j : V) =
        if i = j then (if i.val + 1 = finrank R L then algebraMap R F ε else 1) else 0 := by
  obtain ⟨m, x, hxL, hspan, horth, hQ⟩ := exists_orth_family Q h2 hfg (hL.isRegular Q hfg)
  -- the values `Q (x i)` are units of `R`
  have hli := linearIndependent_of_orth (R := R) Q horth hQ
  obtain ⟨hm, b, hb⟩ := exists_basis_of_family hli hspan
  have hα : (algebraMap R F 1) ≠ 0 := by simp
  have hL' : IsModular Q (R ∙ algebraMap R F 1) L := by
    have : (R ∙ algebraMap R F 1) = 1 := by
      rw [map_one, ← Submodule.one_eq_span]
    rw [this]; exact hL
  obtain ⟨-, U, hU, hG⟩ := (isModular_iff_gram Q b hα).mp hL'
  have hdiag : ∀ i, Q (b i : V) = algebraMap R F (U i i) := by
    intro i
    have := congrFun (congrFun hG i) i
    simpa [gram] using this
  have hoff : ∀ i j, i ≠ j → U i j = 0 := by
    intro i j hij
    have := congrFun (congrFun hG i) j
    simp only [gram, Matrix.of_apply, hb, Matrix.smul_apply, Matrix.map_apply, map_one,
      smul_eq_mul, one_mul] at this
    rw [horth _ _ (fun h => hij (Fin.cast_injective _ h))] at this
    exact (IsFractionRing.injective R F) (this.symm.trans (map_zero _).symm)
  have hUdiag : U = Matrix.diagonal fun i => U i i := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  have hunit : ∀ i, IsUnit (U i i) := by
    rw [hUdiag, Matrix.det_diagonal] at hU
    intro i
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => U i i) (Finset.mem_univ i)) hU
  -- normalize
  have hpos : 0 < finrank R L := by
    rcases Nat.eq_zero_or_pos (finrank R L) with h0 | h0
    · exfalso
      have hsc : scale Q L = ⊥ := by
        rw [← span_basis_eq b, scale_span, span_eq_bot]
        rintro _ ⟨p, rfl⟩; exact Fin.elim0 (h0 ▸ p.1)
      exact hL.1 (hL.2.1.symm.trans hsc)
    · exact h0
  obtain ⟨k, hk⟩ : ∃ k, finrank R L = k + 1 := ⟨finrank R L - 1, by omega⟩
  let x' : Fin (k + 1) → V := fun i => (b (Fin.cast hk.symm i) : V)
  let a : Fin (k + 1) → R := fun i => U (Fin.cast hk.symm i) (Fin.cast hk.symm i)
  have hx'orth : ∀ i j, i ≠ j → bil Q (x' i) (x' j) = 0 := by
    intro i j hij
    simp only [x', hb]
    exact horth _ _ (fun h => hij (by simpa using h))
  obtain ⟨y, hyspan, hyorth, hyQ⟩ := exists_normalized_family Q h2 k x' a (fun i => hunit _)
    (fun i => hdiag _) hx'orth
  have hx'span : span R (Set.range x') = L := by
    rw [← span_basis_eq b]
    congr 1
    ext v; constructor
    · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨Fin.cast hk i, by simp [x']⟩
  have hyQ0 : ∀ i, Q (y i) ≠ 0 := by
    intro i; rw [hyQ i]; split_ifs
    · simp only [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R F)]
      exact (IsUnit.ne_zero (IsUnit.prod_univ_iff.mpr fun i => hunit _))
    · exact one_ne_zero
  obtain ⟨hm', b', hb'⟩ := exists_basis_of_family (linearIndependent_of_orth Q hyorth hyQ0)
    (hyspan.trans hx'span)
  refine ⟨∏ i, a i, IsUnit.prod_univ_iff.mpr fun i => hunit _, b', fun i j => ?_⟩
  rw [hb', hb']
  split_ifs with hij hlast
  · subst hij; rw [bil_self, hyQ, ite_eq_left_iff.mpr]; intro h; exfalso; apply h; ext; simp; omega
  · subst hij; rw [bil_self, hyQ, ite_eq_right_iff.mpr]; intro h; exfalso; apply hlast
    rw [Fin.ext_iff] at h; simp at h; omega
  · exact hyorth _ _ (fun h => hij (Fin.cast_injective _ h))

end LocalNonDyadic

end QuadFormsKB.OMeara
