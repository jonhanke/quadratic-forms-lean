/-
# O'Meara §93D: auxiliary lemmas for Example 93:18 (v) and 93:20

**Setting** as in `Sec93D18Q.lean`: $R$ a Henselian discrete valuation ring with finite residue field, fraction field
$F$ with $2 \in F^\times$, $F$ dyadic ($2$ not a unit of $R$).

**Proves**
* `exists_isWeightGenerator`: a unimodular lattice has a weight generator;
* `exists_small_sublattice` (O'Meara 1963, p. 261, "a quaternary unimodular sublattice of $L$ which has norm
  $a\mathfrak o$"; "a suitable ternary or quaternary sublattice"): a unimodular lattice of rank $\ge 3$ contains a
  unimodular sublattice of rank $3$ or $4$ containing a vector $z$ with $Q(z)\mathfrak o = \mathfrak nL$;
* `exists_basis_det_one_add` (the normalization of 93:18 (iii): "$d$ has been expressed in the form $d = 1 + \alpha$
  with $\mathfrak d(d) = \alpha\mathfrak o$"): a unimodular lattice has a base of discriminant $1 + \alpha$ with
  $\mathfrak d(1 + \alpha) = \alpha\mathfrak o$.
-/
import QuadFormsKB.Literature.OMeara.Sec93DSub

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.D18

section Aux

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- A unimodular lattice over a dyadic local field has a weight generator: $\mathfrak wL = b\mathfrak o$ for some
$b \in F$ (`weight_cases`). -/
theorem exists_isWeightGenerator (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG)
    (hU : IsUnimodular Q L) : ∃ b : F, IsWeightGenerator Q L b := by
  have hreg : IsRegular Q L := IsModular.isRegular Q hU hfg
  have hne := Uni93.ne_bot_of_isUnimodular Q hU
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨x, hx, ha⟩ := exists_isNormGenerator_Q Q hfg
  have ha0 := ha.ne_zero Q hreg hne
  obtain ⟨m, hm0, hm, -, hcase⟩ := weight_cases Q h2p hπ ha ha0
  rcases hcase with h | ⟨h, -⟩
  · exact ⟨_, h.symm⟩
  · exact ⟨m, hm.symm.trans h.symm⟩

/-- **A ternary or quaternary unimodular sublattice carrying the norm** (O'Meara 1963, p. 261, proof of 93:18 (v)):
a unimodular lattice $L$ of rank $\ge 3$ contains a unimodular sublattice $M$ of rank $3$ or $4$ and a vector
$z \in M$ with $Q(z)\mathfrak o = \mathfrak nL$. -/
theorem exists_small_sublattice (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG)
    (hU : IsUnimodular Q L) (hrk : 3 ≤ finrank R L) :
    ∃ M : Submodule R V, M ≤ L ∧ M.FG ∧ IsUnimodular Q M ∧ (finrank R M = 3 ∨ finrank R M = 4) ∧
      ∃ z ∈ M, R ∙ Q z = normIdeal Q L := by
  have hsc : scale Q L = 1 := hU.2.1
  have hreg : IsRegular Q L := IsModular.isRegular Q hU hfg
  have hne := Uni93.ne_bot_of_isUnimodular Q hU
  obtain ⟨J, hJL, hJfg, hJU, hJrk, -, -, -, z, hzL, hzJ, hz⟩ := Uni93.exists_split_data Q hfg hU hrk
  have hzorth : ∀ j ∈ J, ∀ y ∈ span R {z}, bil Q j y = 0 := by
    intro j hj y hy
    exact Uni93.bil_zero_on_span Q (z := j) (S := {z}) (by
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      rw [bil_comm]; exact hzJ j hj) y hy
  obtain ⟨q, hq⟩ := a10_mem_one Q hU hzL hzL
  rw [bil_self] at hq
  by_cases hqu : IsUnit q
  · obtain ⟨hS, hSrk⟩ := u93_isUnimodular_span_singleton Q hqu hq.symm
    obtain ⟨hM, hMrk⟩ := isModular_sup Q hJU hS hJfg (fg_span_singleton z) hzorth
    refine ⟨J ⊔ span R {z}, sup_le hJL (by rw [span_le]; simpa using hzL), hJfg.sup (fg_span_singleton z),
      hM, Or.inl (by rw [hMrk, hJrk, hSrk]), z, mem_sup_right (mem_span_singleton_self z), hz⟩
  · have ha : IsNormGenerator Q L (Q z) := ⟨Q_mem_normGroup Q hzL, hz⟩
    have ha0 := ha.ne_zero Q hreg hne
    have hmax := a10_isMaxVec Q hzL ha ha0
    have hL1 : IsModular Q (R ∙ (1 : F)) L := by rw [← Submodule.one_eq_span]; exact hU
    obtain ⟨z', hz'L, hz'⟩ := exists_bil_unit_of_isMaxVec Q hfg hL1 hmax
    obtain ⟨K, hK⟩ := splits_of_isModular_of_scale_eq Q hJL hJU hJfg hsc
    have hKle : K ≤ L := hK.sup_eq ▸ le_sup_right
    have hz'JK : z' ∈ J ⊔ K := hK.sup_eq ▸ hz'L
    obtain ⟨j, hj, k, hk, rfl⟩ := Submodule.mem_sup.mp hz'JK
    have hzk : bil Q z k = bil Q z (j + k) := by
      rw [bil_add_right, hzJ j hj, zero_add]
    rw [← hzk] at hz'
    obtain ⟨e, he, hbe⟩ := u93_unit_of_span_eq_one (hz'.trans (Submodule.one_eq_span).symm)
    obtain ⟨q', hq'⟩ := a10_mem_one Q hU (hKle hk) (hKle hk)
    rw [bil_self] at hq'
    obtain ⟨hN, hNrk⟩ := Uni93.span_pair_unimodular Q hqu he hq.symm hq'.symm hbe
    have hNorth : ∀ x ∈ J, ∀ y ∈ span R {z, k}, bil Q x y = 0 := by
      intro x hx y hy
      refine Uni93.bil_zero_on_span Q (z := x) (S := {z, k}) ?_ y hy
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · rw [bil_comm]; exact hzJ x hx
      · exact hK.orth x hx _ hk
    obtain ⟨hM, hMrk⟩ := isModular_sup Q hJU hN hJfg (fg_span (Set.toFinite _)) hNorth
    have hNL : span R {z, k} ≤ L := by
      rw [span_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact hzL
      · exact hKle hk
    refine ⟨J ⊔ span R {z, k}, sup_le hJL hNL, hJfg.sup (fg_span (Set.toFinite _)), hM,
      Or.inr (by rw [hMrk, hJrk, hNrk]), z, mem_sup_right (subset_span (by simp)), hz⟩

/-- **The normalization $dL = 1 + \alpha$, $\mathfrak d(1 + \alpha) = \alpha\mathfrak o$** (O'Meara 1963, p. 260,
93:18 (iii)): a unimodular lattice of rank $n \ge 1$ over a dyadic local field has a base whose discriminant is
$1 + \alpha$ with $\alpha \in \mathfrak o$ and $\mathfrak d(1 + \alpha) = \alpha\mathfrak o$. -/
theorem exists_basis_det_one_add (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG)
    (hU : IsUnimodular Q L) {n : ℕ} [NeZero n] (hrk : finrank R L = n) :
    ∃ α : R, (∃ e : Basis (Fin n) R L, (gram Q fun i => (e i : V)).det = 1 + algebraMap R F α) ∧
      quadDefect R (1 + algebraMap R F α) = span R {algebraMap R F α} := by
  classical
  have h2 : (2 : R) ≠ 0 := fun h => two_ne_zero' F (by
    have := congrArg (algebraMap R F) h
    rw [map_ofNat, map_zero] at this
    exact this)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : Module.Finite R L := Module.Finite.iff_fg.mpr hfg
  have : NoZeroSMulDivisors R V := ⟨fun {c x} h => by
    rw [← algebraMap_smul F c x, smul_eq_zero] at h
    rcases h with h | h
    · left; exact (map_eq_zero_iff _ (IsFractionRing.injective R F)).mp h
    · right; exact h⟩
  let e : Basis (Fin n) R L := Module.finBasisOfFinrankEq R L hrk
  obtain ⟨u, hu, hdet⟩ := Eng93.isUnit_det_of_isUnimodular Q hU e
  obtain ⟨η, hη⟩ := exists_quadDefect_eq (R := R) (F := F) h2 (algebraMap R F u)
  have hmem : algebraMap R F u - η ^ 2 ∈ quadDefect R (algebraMap R F u) := by
    rw [← hη]; exact mem_span_singleton_self _
  have ha : ∃ a : R, ¬ IsUnit a ∧ algebraMap R F u - η ^ 2 = algebraMap R F a := by
    have h4 : ¬ IsUnit (4 : R) := by
      intro h; apply h2p
      exact isUnit_of_mul_isUnit_left (y := 2) (by rw [show (2 : R) * 2 = 4 by norm_num]; exact h)
    rcases quadDefect_unit_dyadic (F := F) h2 h2p hπ hu with h | h | ⟨d, hd, -, h⟩
    · refine ⟨0, not_isUnit_zero, ?_⟩
      rw [h] at hmem
      rw [(Submodule.mem_bot R).mp hmem, map_zero]
    · rw [h] at hmem
      obtain ⟨c, hc⟩ := mem_span_singleton.mp hmem
      refine ⟨c * 4, fun hh => h4 (isUnit_of_mul_isUnit_right hh), ?_⟩
      rw [← hc, Algebra.smul_def, map_mul, map_ofNat]
    · rw [h] at hmem
      obtain ⟨c, hc⟩ := mem_span_singleton.mp hmem
      have hd0 : d ≠ 0 := by rintro rfl; simp at hd
      refine ⟨c * π ^ d, fun hh => hπ.not_isUnit
        ((isUnit_pow_iff hd0).mp (isUnit_of_mul_isUnit_right hh)), ?_⟩
      rw [← hc, Algebra.smul_def, map_mul, map_pow]
  obtain ⟨a, ha_nu, haeq⟩ := ha
  have hD : quadDefect R (algebraMap R F u) = span R {algebraMap R F a} := by
    rw [← hη, haeq]
  have hη2 : η ^ 2 = algebraMap R F (u - a) := by rw [map_sub, ← haeq]; ring
  obtain ⟨η₀, hη₀⟩ := exists_alg_of_sq hη2
  have hsqR : η₀ ^ 2 = u - a := IsFractionRing.injective R F (by rw [map_pow, hη₀, hη2])
  have hua : IsUnit (u - a) := by
    by_contra hn
    have h1 : u - a ∈ maximalIdeal R := hn
    have h2' : a ∈ maximalIdeal R := ha_nu
    have h3 : u ∈ maximalIdeal R := by simpa using add_mem h1 h2'
    exact (IsLocalRing.mem_maximalIdeal u).mp h3 hu
  have hη₀u : IsUnit η₀ := (isUnit_pow_iff two_ne_zero).mp (hsqR ▸ hua)
  obtain ⟨v, hv⟩ := hη₀u
  set w0 : R := ((v⁻¹ : Rˣ) : R) with hw0
  have hw : w0 * η₀ = 1 := by rw [hw0, ← hv]; exact v.inv_mul
  have hrel : w0 ^ 2 * u = 1 + w0 ^ 2 * a := by
    have hu_eq : u = η₀ ^ 2 + a := by rw [hsqR]; ring
    rw [hu_eq]; linear_combination (w0 * η₀ + 1) * hw
  have hdef : quadDefect R (1 + algebraMap R F (w0 ^ 2 * a)) = span R {algebraMap R F (w0 ^ 2 * a)} := by
    have key := quadDefect_sq_mul (R := R) (algebraMap R F w0) (algebraMap R F u)
    have e1 : algebraMap R F w0 ^ 2 * algebraMap R F u = 1 + algebraMap R F (w0 ^ 2 * a) := by
      rw [← map_pow, ← map_mul, hrel, map_add, map_one]
    rw [e1, hD, Submodule.span_mul_span, Set.singleton_mul_singleton, ← map_pow, ← map_mul] at key
    exact key
  refine ⟨w0 ^ 2 * a, ?_, hdef⟩
  let w : Fin n → Rˣ := Function.update 1 0 v⁻¹
  let P : Matrix (Fin n) (Fin n) F := Matrix.diagonal fun i => algebraMap R F (w i : R)
  refine ⟨e.unitsSMul w, ?_⟩
  have hfun : (fun i => (((e.unitsSMul w) i : L) : V)) = fun i => ∑ j, P i j • (e j : V) := by
    funext i
    simp [P, Matrix.diagonal_apply, Basis.unitsSMul_apply, algebraMap_smul, Units.smul_def]
  rw [hfun, gram_comb Q P (fun j => (e j : V)), Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet,
    Matrix.det_diagonal]
  have hprod : ∏ i, algebraMap R F (w i : R) = algebraMap R F w0 := by
    rw [Fintype.prod_eq_single 0]
    · simp [w, w0]
    · intro i hi; simp [w, Function.update_of_ne hi]
  rw [hprod, ← map_mul, ← map_mul, show w0 * u * w0 = 1 + w0 ^ 2 * a by linear_combination hrel, map_add,
    map_one]

/-- **Example 93:18 (i)** (O'Meara 1963, §93D, p. 260, page image: "Regard $d$ as an element of $\mathfrak u$. Note
that $b\mathfrak o = 2\mathfrak o$ when $\operatorname{ord}_{\mathfrak p} a + \operatorname{ord}_{\mathfrak p} b$ is
even, by §93A"): for a unimodular lattice $L$ over a dyadic local field with norm generator $a$ and weight generator
$b$, $\operatorname{ord} a + \operatorname{ord} b$ even, $b\mathfrak o = 2\mathfrak o$. (For any non-zero regular
lattice this is `weight_gen_eq_of_even`: $b\mathfrak o = 2(\mathfrak sL)$.) -/
@[kb "omeara1963" "§93D, 93:18 (i), p. 260 (bo = 2o when ord a + ord b is even)"]
theorem omeara93_18_i (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π) {L : Submodule R V} (hfg : L.FG)
    (hU : IsUnimodular Q L) {a b : F} (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b)
    (hev : Even (dord hπ a + dord hπ b)) : R ∙ b = R ∙ (2 : F) := by
  have hbeq := weight_gen_eq_of_even Q h2p hπ (IsModular.isRegular Q hU hfg) (Uni93.ne_bot_of_isUnimodular Q hU) ha hb hev
  rw [hbeq, hU.2.1, Submodule.one_eq_span, Submodule.smul_span, Set.smul_set_singleton, smul_eq_mul, mul_one]

end Aux

end QuadFormsKB.OMeara.D18
