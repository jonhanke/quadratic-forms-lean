import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelFormAut
import QuadFormsKB.Binary.RelativeIdealCount

/-!
# Representation numbers of the binary lattices $(\mathfrak A, cN)$ over $\mathcal O_F$

Let $E/F$ be a quadratic extension of number fields, $N = N_{E/F}$, and for an $\mathcal O_F$-lattice $L \subseteq E$ with the form
$Q = cN$ let $r_{(L, Q)}(\nu) = \#\{x \in L : Q(x) = \nu\}$ (`repNumLat`). Let
$w_1 = \#\{u \in \mathcal O_E^\times : N(u) = 1\}$ ($= w_E$ in the CM case, `card_normOneUnits`).

**One lattice** (`repNumLat_ideal_eq`): for $\mathfrak A \ne 0$, $c \ne 0$, $\nu \ne 0$ (and $w_1 < \infty$),
$$r_{(\mathfrak A, cN)}(\nu) = w_1\cdot\#\{\mathfrak B \subseteq \mathcal O_E : \mathfrak A\mathfrak B = (x)\ \text{for some } x \in \mathfrak A \text{ with } c\,N(x) = \nu\},$$
since $x \mapsto \mathfrak B = x\mathfrak A^{-1}$ is $w_1$-to-$1$ (two generators of $(x)$ with the same norm differ by a unit of norm $1$).
This is the analogue of `repNum_eq` ($r_f(m) = w\cdot\#\{\mathfrak b : N\mathfrak b = m,\ [\mathfrak b] = [\mathfrak a_f]^{-1}\}$).

**The class sum** (`sum_repNumLat_eq`, `sum_repNumLat_eq_sum_relChar`): fix a representative $\mathfrak A_C$ of every ideal class
$C \in \mathrm{Cl}_E$ (`classRep`). For the classes with principal relative norm, $N_{E/F}\mathfrak A_C = (a_C)$, the normalized lattices on
$\mathfrak A_C$ are $(\mathfrak A_C, \tfrac{\eta}{a_C}N)$, $\eta \in \mathcal O_F^\times$, and up to isometry $\eta$ only matters modulo the norms of units:
$\eta \in U_{E/F} := \mathcal O_F^\times/N_{E/F}(\mathcal O_E^\times)$ (`unitQuot`, finite: `finite_unitQuot`). For $\nu \in \mathcal O_F\setminus 0$:
$$\sum_{C:\ N\mathfrak A_C\ \text{principal}}\ \sum_{\eta \in U_{E/F}} r_{(\mathfrak A_C,\ \frac{\eta}{a_C}N)}(\nu)
  = w_1\cdot\#\{\mathfrak B \subseteq \mathcal O_E : N_{E/F}\mathfrak B = (\nu)\} = w_1\sum_{\mathfrak d \mid (\nu)}\chi_{E/F}(\mathfrak d),$$
the last equality by `relNormCount_eq_finprod`. Over $F = \mathbb Q$: $U_{E/\mathbb Q} = \{\pm 1\}$, and $\eta = -1$ gives the negative
definite forms, which represent no $\nu > 0$; so this is `dirichlet_sum_repNum`, $\sum_{[f]^+}r_f(m) = w\sum_{d \mid m}\chi_D(d)$.

The **unit factor** has two parts: $w_1 = w_E$ (roots of unity, the automorphisms) and the index $[\mathcal O_F^\times : N\mathcal O_E^\times]$
(the number of isometry classes of normalized lattices on one ideal). By Hasse, $N\mathcal O_E^\times \supseteq \mathcal O_F^{\times 2}$ with
index $Q_E \in \{1, 2\}$ (Washington Thm. 4.12 [unverified locator]); here we only use (and prove) that the quotient is finite.

Sources: Shimura, *Arithmetic of Quadratic Forms* (2010), §4 [unverified locator]; Cox §7 (the case $F = \mathbb Q$);
Zagier, *Zetafunktionen und quadratische Körper*, §8 [unverified locator].
-/

open NumberField Module NumberField.Units
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-- **The representation number of a lattice** $L \subseteq E$ with a quadratic form $Q$:
$r_{(L, Q)}(\nu) = \#\{x \in L : Q(x) = \nu\}$ (`Nat.card`; $0$ if infinite). -/
@[kb "omeara1963" "§82 [unverified]; Siegel (1935)"]
def repNumLat (Q : QuadraticForm F E) (L : Submodule (𝓞 F) E) (ν : F) : ℕ := Nat.card {x : L // Q x = ν}

/-- The units of $\mathcal O_E$ of relative norm $1$. -/
abbrev NormOneUnits (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :=
  {v : (𝓞 E)ˣ // Algebra.norm F ((v : 𝓞 E) : E) = 1}

/-- The norm of an element of $\mathcal O_E$ in $F$. -/
abbrev nrm (x : 𝓞 E) : F := Algebra.norm F (algebraMap (𝓞 E) E x)

theorem nrm_mul (x y : 𝓞 E) : nrm (F := F) (x * y) = nrm (F := F) x * nrm (F := F) y := by
  simp [nrm, map_mul]

theorem nrm_ne_zero {x : 𝓞 E} (hx : x ≠ 0) : nrm (F := F) x ≠ 0 :=
  Algebra.norm_ne_zero_iff.mpr (algebraMap_ne_zero hx)

/-! ### One lattice -/

/-- Points of $(\mathfrak A, cN)$ of value $\nu$, as elements of $\mathcal O_E$. -/
abbrev RepSet (𝔄 : Ideal (𝓞 E)) (c ν : F) : Type := {x : 𝓞 E // x ∈ 𝔄 ∧ c * nrm (F := F) x = ν}

theorem repNumLat_eq_card_repSet (𝔄 : Ideal (𝓞 E)) (c ν : F) :
    repNumLat (c • normForm F E) (idealLat F 𝔄) ν = Nat.card (RepSet 𝔄 c ν) := by
  refine Nat.card_congr ?_
  exact
  { toFun := fun x => ⟨((mem_idealLat (F := F)).mp x.1.2).choose, ((mem_idealLat (F := F)).mp x.1.2).choose_spec.1, by
      have h := x.2
      rw [_root_.smul_apply, normForm_apply, smul_eq_mul,
        ← ((mem_idealLat (F := F)).mp x.1.2).choose_spec.2] at h
      exact h⟩
    invFun := fun x => ⟨⟨algebraMap (𝓞 E) E x.1, algebraMap_mem_idealLat x.2.1⟩, by
      rw [_root_.smul_apply, normForm_apply, smul_eq_mul]; exact x.2.2⟩
    left_inv := fun x => Subtype.ext (Subtype.ext ((mem_idealLat (F := F)).mp x.1.2).choose_spec.2)
    right_inv := fun x => Subtype.ext (FaithfulSMul.algebraMap_injective (𝓞 E) E
      ((mem_idealLat (F := F)).mp (algebraMap_mem_idealLat x.2.1)).choose_spec.2) }

/-- The quotient ideal $\mathfrak B = x\,\mathfrak A^{-1}$ for $x \in \mathfrak A$: $(x) = \mathfrak A\,\mathfrak B$. -/
def quotIdeal (𝔄 : Ideal (𝓞 E)) {x : 𝓞 E} (hx : x ∈ 𝔄) : Ideal (𝓞 E) :=
  (Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem 𝔄).mpr hx)).choose

theorem span_eq_mul_quotIdeal (𝔄 : Ideal (𝓞 E)) {x : 𝓞 E} (hx : x ∈ 𝔄) :
    Ideal.span {x} = 𝔄 * quotIdeal 𝔄 hx :=
  (Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem 𝔄).mpr hx)).choose_spec

theorem quotIdeal_eq_iff {𝔄 : Ideal (𝓞 E)} (h𝔄 : 𝔄 ≠ ⊥) {x : 𝓞 E} (hx : x ∈ 𝔄) (𝔅 : Ideal (𝓞 E)) :
    quotIdeal 𝔄 hx = 𝔅 ↔ 𝔄 * 𝔅 = Ideal.span {x} := by
  rw [span_eq_mul_quotIdeal 𝔄 hx]
  constructor
  · rintro rfl; rfl
  · intro h; exact (mul_left_cancel₀ h𝔄 h).symm

/-- The ideals $\mathfrak B$ with $\mathfrak A\mathfrak B = (x)$ for some $x \in \mathfrak A$ with $c\,N(x) = \nu$. -/
def RepIdeals (𝔄 : Ideal (𝓞 E)) (c ν : F) : Set (Ideal (𝓞 E)) :=
  {𝔅 | ∃ x : 𝓞 E, x ∈ 𝔄 ∧ c * nrm (F := F) x = ν ∧ 𝔄 * 𝔅 = Ideal.span {x}}

theorem relNorm_eq_of_mem_repIdeals {𝔄 : Ideal (𝓞 E)} (h𝔄 : 𝔄 ≠ ⊥) {c ν : F} (hc : c ≠ 0)
    {𝔅 𝔅' : Ideal (𝓞 E)} (h : 𝔅 ∈ RepIdeals 𝔄 c ν) (h' : 𝔅' ∈ RepIdeals 𝔄 c ν) :
    Ideal.relNorm (𝓞 F) 𝔅 = Ideal.relNorm (𝓞 F) 𝔅' := by
  obtain ⟨x, -, hx, hxB⟩ := h
  obtain ⟨x', -, hx', hxB'⟩ := h'
  have hn : Algebra.intNorm (𝓞 F) (𝓞 E) x = Algebra.intNorm (𝓞 F) (𝓞 E) x' := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [Algebra.algebraMap_intNorm (L := E), Algebra.algebraMap_intNorm (L := E)]
    exact mul_left_cancel₀ hc (hx.trans hx'.symm)
  have e := congrArg (Ideal.relNorm (𝓞 F)) hxB
  have e' := congrArg (Ideal.relNorm (𝓞 F)) hxB'
  rw [map_mul, Ideal.relNorm_singleton] at e e'
  rw [hn, ← e'] at e
  exact mul_left_cancel₀ ((Ideal.relNorm_eq_bot_iff).not.mpr h𝔄) e

theorem finite_repIdeals {𝔄 : Ideal (𝓞 E)} (h𝔄 : 𝔄 ≠ ⊥) {c ν : F} (hc : c ≠ 0) :
    (RepIdeals (F := F) 𝔄 c ν).Finite := by
  by_cases h : (RepIdeals (F := F) 𝔄 c ν).Nonempty
  · obtain ⟨𝔅₀, h₀⟩ := h
    exact (finite_relNormSet (E := E) (𝔪 := Ideal.relNorm (𝓞 F) 𝔅₀)).subset
      fun 𝔅 h𝔅 => relNorm_eq_of_mem_repIdeals h𝔄 hc h𝔅 h₀
  · rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h]
    exact Set.finite_empty

theorem nrm_unit_eq_one {x₀ x : 𝓞 E} (hx₀ : x₀ ≠ 0) {c ν : F} (hc : c ≠ 0) (h₀ : c * nrm (F := F) x₀ = ν)
    (hx : c * nrm (F := F) x = ν) (u : (𝓞 E)ˣ) (hu : x₀ * u = x) :
    Algebra.norm F (((u : 𝓞 E) : E)) = 1 := by
  rw [← hu, nrm_mul] at hx
  have hn : c * nrm (F := F) x₀ ≠ 0 := mul_ne_zero hc (nrm_ne_zero hx₀)
  refine mul_left_cancel₀ hn ?_
  rw [mul_one]
  change c * nrm (F := F) x₀ * nrm (F := F) (u : 𝓞 E) = _
  rw [mul_assoc, hx, h₀]

/-- **Generators of a principal ideal with prescribed value form a torsor under the norm-one units:** if
$c\,N(x_0) = \nu$, $x_0 \ne 0$, $c \ne 0$, then $\{x : (x) = (x_0),\ c\,N(x) = \nu\} \simeq \{u \in \mathcal O_E^\times : N(u) = 1\}$,
$x = x_0u$. -/
def genEquiv {x₀ : 𝓞 E} (hx₀ : x₀ ≠ 0) {c ν : F} (hc : c ≠ 0) (h₀ : c * nrm (F := F) x₀ = ν) :
    {x : 𝓞 E // Ideal.span {x} = Ideal.span {x₀} ∧ c * nrm (F := F) x = ν} ≃ NormOneUnits F E where
  toFun x := ⟨Classical.choose (Ideal.span_singleton_eq_span_singleton.mp x.2.1.symm),
    nrm_unit_eq_one hx₀ hc h₀ x.2.2 _
      (Classical.choose_spec (Ideal.span_singleton_eq_span_singleton.mp x.2.1.symm))⟩
  invFun u := ⟨x₀ * (u.1 : 𝓞 E), by rw [Ideal.span_singleton_mul_right_unit u.1.isUnit], by
    rw [nrm_mul, show nrm (F := F) ((u.1 : 𝓞 E)) = 1 from u.2, mul_one, h₀]⟩
  left_inv x := Subtype.ext
    (Classical.choose_spec (Ideal.span_singleton_eq_span_singleton.mp x.2.1.symm))
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    have h := Classical.choose_spec (Ideal.span_singleton_eq_span_singleton.mp
      (show Ideal.span {x₀} = Ideal.span {x₀ * (u.1 : 𝓞 E)} by
        rw [Ideal.span_singleton_mul_right_unit u.1.isUnit]))
    exact mul_left_cancel₀ hx₀ h

/-- The fibre of $x \mapsto x\mathfrak A^{-1}$ over $\mathfrak B$: the $x$ with $(x) = \mathfrak A\mathfrak B$ and $c\,N(x) = \nu$. -/
def repFiberEquiv {𝔄 : Ideal (𝓞 E)} (h𝔄 : 𝔄 ≠ ⊥) (c ν : F) (𝔅 : Ideal (𝓞 E)) :
    {x : RepSet (F := F) 𝔄 c ν // quotIdeal 𝔄 x.2.1 = 𝔅} ≃
      {x : 𝓞 E // Ideal.span {x} = 𝔄 * 𝔅 ∧ c * nrm (F := F) x = ν} where
  toFun x := ⟨x.1.1, ((quotIdeal_eq_iff h𝔄 x.1.2.1 𝔅).mp x.2).symm, x.1.2.2⟩
  invFun y := by
    have h : y.1 ∈ 𝔄 * 𝔅 := (Ideal.span_singleton_le_iff_mem _).mp (le_of_eq y.2.1)
    have h' : y.1 ∈ 𝔄 := (Ideal.mul_le_left : 𝔄 * 𝔅 ≤ 𝔄) h
    refine ⟨⟨y.1, h', y.2.2⟩, ?_⟩
    exact (quotIdeal_eq_iff h𝔄 h' 𝔅).mpr y.2.1.symm
  left_inv x := rfl
  right_inv y := rfl

/-- **Representation numbers of one ideal lattice** ($\mathfrak A \ne 0$, $c, \nu \ne 0$, finitely many norm-one units):
$$r_{(\mathfrak A, cN)}(\nu) = w_1\cdot\#\{\mathfrak B : \mathfrak A\mathfrak B = (x),\ x \in \mathfrak A,\ c\,N(x) = \nu\},\qquad
w_1 = \#\{u \in \mathcal O_E^\times : N(u) = 1\}.$$ -/
@[kb "cox2013" "Thm. 7.7, proof; Shimura (2010) §4 [unverified]"]
theorem repNumLat_ideal_eq {𝔄 : Ideal (𝓞 E)} (h𝔄 : 𝔄 ≠ ⊥) {c ν : F} (hc : c ≠ 0) (hν : ν ≠ 0)
    [Finite (NormOneUnits F E)] :
    repNumLat (c • normForm F E) (idealLat F 𝔄) ν =
      Nat.card (NormOneUnits F E) * (RepIdeals (F := F) 𝔄 c ν).ncard := by
  rw [repNumLat_eq_card_repSet]
  have hfin := finite_repIdeals h𝔄 hc (ν := ν)
  have : Fintype (RepIdeals (F := F) 𝔄 c ν) := hfin.fintype
  let f : RepSet (F := F) 𝔄 c ν → RepIdeals (F := F) 𝔄 c ν := fun x =>
    ⟨quotIdeal 𝔄 x.2.1, x.1, x.2.1, x.2.2, (span_eq_mul_quotIdeal 𝔄 x.2.1).symm⟩
  have hfib : ∀ s : RepIdeals (F := F) 𝔄 c ν, Nonempty ({x // f x = s} ≃ NormOneUnits F E) := by
    intro s
    obtain ⟨x₀, -, hx₀, hx₀B⟩ := s.2
    have hx₀0 : x₀ ≠ 0 := by
      rintro rfl
      apply hν
      rw [← hx₀, nrm, map_zero, Algebra.norm_eq_zero_iff.mpr rfl, mul_zero]
    have e1 : {x // f x = s} ≃ {x : RepSet (F := F) 𝔄 c ν // quotIdeal 𝔄 x.2.1 = s.1} :=
      Equiv.subtypeEquivRight fun x => Subtype.ext_iff
    have e2 : {x : 𝓞 E // Ideal.span {x} = 𝔄 * s.1 ∧ c * nrm (F := F) x = ν} ≃
        {x : 𝓞 E // Ideal.span {x} = Ideal.span {x₀} ∧ c * nrm (F := F) x = ν} :=
      Equiv.subtypeEquivRight fun x => by rw [hx₀B]
    exact ⟨e1.trans ((repFiberEquiv h𝔄 c ν s.1).trans (e2.trans (genEquiv hx₀0 hc hx₀)))⟩
  have : ∀ s, Finite {x // f x = s} := fun s => Finite.of_equiv _ (hfib s).some.symm
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  simp_rw [fun s => Nat.card_congr (hfib s).some]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq]

/-- **CM case:** $r_{(\mathfrak A, cN)}(\nu) = w_E\cdot\#\{\mathfrak B : \mathfrak A\mathfrak B = (x),\ x \in \mathfrak A,\ c\,N(x) = \nu\}$. -/
@[kb "cox2013" "Thm. 7.7, proof; Shimura (2010) §4 [unverified]"]
theorem repNumLat_ideal_eq_cm [IsTotallyReal F] [IsTotallyComplex E] {𝔄 : Ideal (𝓞 E)} (h𝔄 : 𝔄 ≠ ⊥) {c ν : F}
    (hc : c ≠ 0) (hν : ν ≠ 0) :
    repNumLat (c • normForm F E) (idealLat F 𝔄) ν = torsionOrder E * (RepIdeals (F := F) 𝔄 c ν).ncard := by
  have := finite_normOneUnits (F := F) (E := E)
  rw [repNumLat_ideal_eq h𝔄 hc hν, card_normOneUnits]

/-! ### The unit quotient $\mathcal O_F^\times/N_{E/F}(\mathcal O_E^\times)$ -/

theorem algebraMap_intNorm' (x : 𝓞 E) :
    algebraMap (𝓞 F) F (Algebra.intNorm (𝓞 F) (𝓞 E) x) = nrm (F := F) x :=
  Algebra.algebraMap_intNorm (L := E) x

variable (F E) in
/-- **The norms of units** $N_{E/F}(\mathcal O_E^\times) \le \mathcal O_F^\times$. -/
def normUnits : Subgroup (𝓞 F)ˣ := (Units.map (Algebra.intNorm (𝓞 F) (𝓞 E))).range

theorem algebraMap_normUnit (v : (𝓞 E)ˣ) :
    algebraMap (𝓞 F) F ((Units.map (Algebra.intNorm (𝓞 F) (𝓞 E)) v : (𝓞 F)ˣ) : 𝓞 F) =
      nrm (F := F) (v : 𝓞 E) := by
  rw [Units.coe_map, algebraMap_intNorm']

/-- Squares of units of $F$ are norms: $N_{E/F}(u) = u^2$ for $u \in \mathcal O_F^\times$. -/
theorem sq_mem_normUnits (u : (𝓞 F)ˣ) : u ^ 2 ∈ normUnits F E := by
  refine ⟨Units.map (algebraMap (𝓞 F) (𝓞 E)).toMonoidHom u, Units.ext ?_⟩
  apply FaithfulSMul.algebraMap_injective (𝓞 F) F
  rw [algebraMap_normUnit, Units.coe_map, Units.val_pow_eq_pow_val, map_pow]
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, nrm]
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E,
    Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two]

variable (F E) in
/-- **The unit quotient** $U_{E/F} = \mathcal O_F^\times/N_{E/F}(\mathcal O_E^\times)$: the scales $\eta/a$ of the normalized lattices on
one ideal, up to isometry. -/
@[kb "washington1997" "Thm. 4.12 (Hasse's unit index) [unverified]"]
abbrev unitQuot := (𝓞 F)ˣ ⧸ normUnits F E

/-- $U_{E/F}$ is finite: it is a quotient of $\mathcal O_F^\times/\mathcal O_F^{\times 2}$, finite since $\mathcal O_F^\times$ is finitely
generated (Dirichlet). -/
instance finite_unitQuot : Finite (unitQuot F E) := by
  have : Group.FG (𝓞 F)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  have h2 := Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 F)ˣ (n := 2) two_ne_zero
  have hle : (powMonoidHom (α := (𝓞 F)ˣ) 2).range ≤ normUnits F E := by
    rintro _ ⟨u, rfl⟩
    exact sq_mem_normUnits u
  have := Subgroup.finiteIndex_of_le hle
  exact Subgroup.finite_quotient_of_finiteIndex

/-! ### Class representatives -/

variable (E) in
/-- A chosen nonzero integral ideal $\mathfrak A_C$ in each class $C \in \mathrm{Cl}_E$. -/
def classRep (C : ClassGroup (𝓞 E)) : (Ideal (𝓞 E))⁰ := (ClassGroup.mk0_surjective C).choose

theorem mk0_classRep (C : ClassGroup (𝓞 E)) : ClassGroup.mk0 (classRep E C) = C :=
  (ClassGroup.mk0_surjective C).choose_spec

theorem classRep_ne_bot (C : ClassGroup (𝓞 E)) : (classRep E C : Ideal (𝓞 E)) ≠ ⊥ :=
  nonZeroDivisors.coe_ne_zero _

variable (F E) in
/-- The classes $C \in \mathrm{Cl}_E$ whose representative has principal relative norm $N_{E/F}\mathfrak A_C$ (this does not depend on the
representative; these are the classes carrying normalized lattices). -/
abbrev PNClass := {C : ClassGroup (𝓞 E) // (Ideal.relNorm (𝓞 F) (classRep E C : Ideal (𝓞 E))).IsPrincipal}

/-- A generator $a_C$ of $N_{E/F}\mathfrak A_C = (a_C)$. -/
def normGen (C : PNClass F E) : 𝓞 F :=
  @Submodule.IsPrincipal.generator _ _ _ _ _ _ C.2

noncomputable instance : Fintype (PNClass F E) := Fintype.ofFinite _

theorem span_normGen (C : PNClass F E) :
    Ideal.span {normGen C} = Ideal.relNorm (𝓞 F) (classRep E C.1 : Ideal (𝓞 E)) :=
  @Ideal.span_singleton_generator _ _ _ C.2

theorem normGen_ne_zero (C : PNClass F E) : normGen C ≠ 0 := by
  intro h
  have := span_normGen C
  rw [h, Ideal.span_singleton_eq_bot.mpr rfl, eq_comm, Ideal.relNorm_eq_bot_iff] at this
  exact classRep_ne_bot C.1 this

/-- **The scale** $c_{C, \eta} = \eta/a_C$ of the normalized lattice $(\mathfrak A_C, c_{C,\eta}N)$, with $\eta$ represented by a unit
(`Quotient.out`). -/
def scaleOf (C : PNClass F E) (η : unitQuot F E) : F :=
  algebraMap (𝓞 F) F ((η.out : (𝓞 F)ˣ) : 𝓞 F) / algebraMap (𝓞 F) F (normGen C)

theorem algebraMap_normGen_ne_zero (C : PNClass F E) : algebraMap (𝓞 F) F (normGen C) ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr (normGen_ne_zero C)

theorem algebraMap_unit_ne_zero (u : (𝓞 F)ˣ) : algebraMap (𝓞 F) F (u : 𝓞 F) ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr u.ne_zero

theorem scaleOf_ne_zero (C : PNClass F E) (η : unitQuot F E) : scaleOf C η ≠ 0 :=
  div_ne_zero (algebraMap_unit_ne_zero _) (algebraMap_normGen_ne_zero C)

noncomputable instance : Fintype (unitQuot F E) := Fintype.ofFinite _

theorem algebraMap_inv_unit (u : (𝓞 F)ˣ) :
    algebraMap (𝓞 F) F ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) = (algebraMap (𝓞 F) F (u : 𝓞 F))⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_mul, Units.inv_mul, map_one]

theorem nrm_inv_unit (v : (𝓞 E)ˣ) : nrm (F := F) ((v⁻¹ : (𝓞 E)ˣ) : 𝓞 E) = (nrm (F := F) (v : 𝓞 E))⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← nrm_mul, Units.inv_mul]
  simp [nrm]

/-- The points of value $\nu$ on the normalized lattices land in ideals of relative norm $(\nu)$:
$\mathfrak B \in$ `RepIdeals` $\Rightarrow N_{E/F}\mathfrak B = (\nu)$. -/
theorem relNorm_of_mem_repIdeals {C : PNClass F E} {η : unitQuot F E} {ν : 𝓞 F} {𝔅 : Ideal (𝓞 E)}
    (h : 𝔅 ∈ RepIdeals (F := F) (classRep E C.1 : Ideal (𝓞 E)) (scaleOf C η) (algebraMap (𝓞 F) F ν)) :
    Ideal.relNorm (𝓞 F) 𝔅 = Ideal.span {ν} := by
  obtain ⟨x, -, hx, hxB⟩ := h
  have hint : Algebra.intNorm (𝓞 F) (𝓞 E) x =
      normGen C * (ν * (((η.out : (𝓞 F)ˣ)⁻¹ : (𝓞 F)ˣ) : 𝓞 F)) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [algebraMap_intNorm', map_mul, map_mul, algebraMap_inv_unit]
    rw [scaleOf] at hx
    have hu := algebraMap_unit_ne_zero (η.out : (𝓞 F)ˣ)
    have ha := algebraMap_normGen_ne_zero C
    field_simp at hx ⊢
    linear_combination hx
  have e := congrArg (Ideal.relNorm (𝓞 F)) hxB
  rw [map_mul, Ideal.relNorm_singleton, hint, ← span_normGen, ← Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_mul_right_unit (Units.isUnit _)] at e
  have ha : Ideal.span {normGen C} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact normGen_ne_zero C
  exact mul_left_cancel₀ ha e

theorem ne_bot_of_relNorm {ν : 𝓞 F} (hν : ν ≠ 0) {𝔅 : Ideal (𝓞 E)}
    (h : Ideal.relNorm (𝓞 F) 𝔅 = Ideal.span {ν}) : 𝔅 ≠ ⊥ := by
  rintro rfl
  rw [Ideal.relNorm_bot, eq_comm, Ideal.span_singleton_eq_bot] at h
  exact hν h

/-- **Uniqueness:** an ideal $\mathfrak B$ comes from at most one normalized lattice $(\mathfrak A_C, c_{C,\eta}N)$. -/
theorem eq_of_mem_repIdeals {C C' : PNClass F E} {η η' : unitQuot F E} {ν : 𝓞 F} (hν : ν ≠ 0)
    {𝔅 : Ideal (𝓞 E)}
    (h : 𝔅 ∈ RepIdeals (F := F) (classRep E C.1 : Ideal (𝓞 E)) (scaleOf C η) (algebraMap (𝓞 F) F ν))
    (h' : 𝔅 ∈ RepIdeals (F := F) (classRep E C'.1 : Ideal (𝓞 E)) (scaleOf C' η') (algebraMap (𝓞 F) F ν)) :
    C = C' ∧ η = η' := by
  have hB0 := ne_bot_of_relNorm hν (relNorm_of_mem_repIdeals h)
  have hB : 𝔅 ∈ (Ideal (𝓞 E))⁰ := mem_nonZeroDivisors_of_ne_zero hB0
  obtain ⟨x, -, hx, hxB⟩ := h
  obtain ⟨x', -, hx', hxB'⟩ := h'
  have hνF : algebraMap (𝓞 F) F ν ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hν
  have hx0 : x ≠ 0 := by
    rintro rfl; apply hνF; rw [← hx, nrm, map_zero, Algebra.norm_eq_zero_iff.mpr rfl, mul_zero]
  have hx'0 : x' ≠ 0 := by
    rintro rfl; apply hνF; rw [← hx', nrm, map_zero, Algebra.norm_eq_zero_iff.mpr rfl, mul_zero]
  have hCC : C = C' := by
    apply Subtype.ext
    rw [← mk0_classRep C.1, ← mk0_classRep C'.1]
    have e1 : ClassGroup.mk0 (classRep E C.1) = (ClassGroup.mk0 ⟨𝔅, hB⟩)⁻¹ :=
      ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨x, hx0, hxB⟩
    have e2 : ClassGroup.mk0 (classRep E C'.1) = (ClassGroup.mk0 ⟨𝔅, hB⟩)⁻¹ :=
      ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨x', hx'0, hxB'⟩
    rw [e1, e2]
  subst hCC
  refine ⟨rfl, ?_⟩
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp (hxB.symm.trans hxB')
  rw [← QuotientGroup.out_eq' η, ← QuotientGroup.out_eq' η', QuotientGroup.eq]
  refine ⟨v⁻¹, Units.ext (FaithfulSMul.algebraMap_injective (𝓞 F) F ?_)⟩
  rw [algebraMap_normUnit, nrm_inv_unit, Units.val_mul, map_mul, algebraMap_inv_unit]
  rw [scaleOf] at hx hx'
  rw [← hv, nrm_mul] at hx'
  have hu := algebraMap_unit_ne_zero (η.out : (𝓞 F)ˣ)
  have hu' := algebraMap_unit_ne_zero (η'.out : (𝓞 F)ˣ)
  have ha := algebraMap_normGen_ne_zero C
  have hn := nrm_ne_zero (F := F) hx0
  have hnv : nrm (F := F) (v : 𝓞 E) ≠ 0 := nrm_ne_zero v.ne_zero
  field_simp at hx hx'
  have key : algebraMap (𝓞 F) F (η.out : (𝓞 F)ˣ) =
      algebraMap (𝓞 F) F (η'.out : (𝓞 F)ˣ) * nrm (F := F) (v : 𝓞 E) := by
    refine mul_right_cancel₀ hn ?_
    linear_combination hx - hx'
  rw [key, mul_inv]
  field_simp

/-- **Existence:** every $\mathfrak B$ with $N_{E/F}\mathfrak B = (\nu)$ comes from some normalized lattice: $\mathfrak A_C\mathfrak B = (x)$ with
$c_{C,\eta}N(x) = \nu$, for $C = [\mathfrak B]^{-1}$ and a suitable $\eta$. -/
theorem exists_mem_repIdeals {ν : 𝓞 F} (hν : ν ≠ 0) {𝔅 : Ideal (𝓞 E)}
    (h𝔅 : Ideal.relNorm (𝓞 F) 𝔅 = Ideal.span {ν}) :
    ∃ (C : PNClass F E) (η : unitQuot F E),
      𝔅 ∈ RepIdeals (F := F) (classRep E C.1 : Ideal (𝓞 E)) (scaleOf C η) (algebraMap (𝓞 F) F ν) := by
  have hB : 𝔅 ∈ (Ideal (𝓞 E))⁰ := mem_nonZeroDivisors_of_ne_zero (ne_bot_of_relNorm hν h𝔅)
  set C₀ := (ClassGroup.mk0 (⟨𝔅, hB⟩ : (Ideal (𝓞 E))⁰))⁻¹ with hC₀
  obtain ⟨x₀, hx₀0, hx₀⟩ := ClassGroup.mk0_eq_mk0_inv_iff.mp (mk0_classRep C₀)
  have hrel : Ideal.relNorm (𝓞 F) (classRep E C₀ : Ideal (𝓞 E)) * Ideal.span {ν} =
      Ideal.span {Algebra.intNorm (𝓞 F) (𝓞 E) x₀} := by
    rw [← h𝔅, ← map_mul, ← Ideal.relNorm_singleton]
    exact congrArg _ hx₀
  have ht : Algebra.intNorm (𝓞 F) (𝓞 E) x₀ ∈ Ideal.span {ν} := by
    have hm : Algebra.intNorm (𝓞 F) (𝓞 E) x₀ ∈
        Ideal.relNorm (𝓞 F) (classRep E C₀ : Ideal (𝓞 E)) * Ideal.span {ν} := by
      rw [hrel]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_right : Ideal.relNorm (𝓞 F) (classRep E C₀ : Ideal (𝓞 E)) * Ideal.span {ν} ≤
      Ideal.span {ν}) hm
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp ht
  have hν0 : Ideal.span {ν} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hν
  have hprin : Ideal.relNorm (𝓞 F) (classRep E C₀ : Ideal (𝓞 E)) = Ideal.span {s} := by
    refine mul_right_cancel₀ hν0 ?_
    rw [hrel, Ideal.span_singleton_mul_span_singleton, hs]
  let C : PNClass F E := ⟨C₀, ⟨s, hprin⟩⟩
  obtain ⟨ε, hε⟩ := Ideal.span_singleton_eq_span_singleton.mp ((span_normGen C).trans hprin)
  set η : unitQuot F E := QuotientGroup.mk ε⁻¹ with hη
  have hmem : (ε⁻¹)⁻¹ * η.out ∈ normUnits F E := QuotientGroup.eq.mp (QuotientGroup.out_eq' η).symm
  obtain ⟨v, hv⟩ := hmem
  have hspan : Ideal.span {x₀ * ((v⁻¹ : (𝓞 E)ˣ) : 𝓞 E)} = Ideal.span {x₀} :=
    Ideal.span_singleton_mul_right_unit (Units.isUnit _) _
  refine ⟨C, η, x₀ * ((v⁻¹ : (𝓞 E)ˣ) : 𝓞 E), ?_, ?_, ?_⟩
  · have hm : x₀ * ((v⁻¹ : (𝓞 E)ˣ) : 𝓞 E) ∈ (classRep E C₀ : Ideal (𝓞 E)) * 𝔅 := by
      rw [hx₀, ← hspan]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_left : (classRep E C₀ : Ideal (𝓞 E)) * 𝔅 ≤ _) hm
  · -- the value
    have hvF := congrArg (fun w : (𝓞 F)ˣ => algebraMap (𝓞 F) F (w : 𝓞 F)) hv
    simp only [algebraMap_normUnit, inv_inv, Units.val_mul, map_mul] at hvF
    have htF := congrArg (algebraMap (𝓞 F) F) hs
    rw [algebraMap_intNorm', map_mul] at htF
    have hεF := congrArg (algebraMap (𝓞 F) F) hε
    rw [map_mul] at hεF
    rw [scaleOf, nrm_mul, nrm_inv_unit, hvF, ← htF, ← hεF]
    have hu := algebraMap_unit_ne_zero (η.out : (𝓞 F)ˣ)
    have he := algebraMap_unit_ne_zero ε
    have ha := algebraMap_normGen_ne_zero C
    field_simp
  · rw [hspan]; exact hx₀

/-- **The class sum of representation numbers** (Dirichlet's formula over $F$). For $\nu \in \mathcal O_F \setminus 0$, summing over the
classes $C$ with principal $N_{E/F}\mathfrak A_C = (a_C)$ and over $\eta \in U_{E/F} = \mathcal O_F^\times/N(\mathcal O_E^\times)$:
$$\sum_C\sum_{\eta} r_{(\mathfrak A_C,\ \frac{\eta}{a_C}N)}(\nu) = w_1\cdot\#\{\mathfrak B \subseteq \mathcal O_E : N_{E/F}\mathfrak B = (\nu)\},
\qquad w_1 = \#\{u \in \mathcal O_E^\times : N(u) = 1\}.$$ -/
@[kb "cox2013" "Thm. 7.7 and Dirichlet's formula; Shimura (2010) §4 [unverified]"]
theorem sum_repNumLat_eq [Finite (NormOneUnits F E)] {ν : 𝓞 F} (hν : ν ≠ 0) :
    ∑ C : PNClass F E, ∑ η : unitQuot F E,
      repNumLat (scaleOf C η • normForm F E) (idealLat F (classRep E C.1 : Ideal (𝓞 E)))
        (algebraMap (𝓞 F) F ν) =
    Nat.card (NormOneUnits F E) * relNormCount E (Ideal.span {ν}) := by
  have hνF : algebraMap (𝓞 F) F ν ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hν
  simp_rw [repNumLat_ideal_eq (classRep_ne_bot _) (scaleOf_ne_zero _ _) hνF, ← Finset.mul_sum]
  congr 1
  rw [← Fintype.sum_prod_type']
  -- the partition of {𝔅 : N𝔅 = (ν)} by (C, η)
  let T := {𝔅 : Ideal (𝓞 E) // Ideal.relNorm (𝓞 F) 𝔅 = Ideal.span {ν}}
  have hT : Finite T := (finite_relNormSet (E := E) (𝔪 := Ideal.span {ν})).to_subtype
  let g : T → PNClass F E × unitQuot F E := fun 𝔅 =>
    ((exists_mem_repIdeals hν 𝔅.2).choose, (exists_mem_repIdeals hν 𝔅.2).choose_spec.choose)
  have hg : ∀ 𝔅 : T, 𝔅.1 ∈ RepIdeals (F := F) (classRep E (g 𝔅).1.1 : Ideal (𝓞 E))
      (scaleOf (g 𝔅).1 (g 𝔅).2) (algebraMap (𝓞 F) F ν) :=
    fun 𝔅 => (exists_mem_repIdeals hν 𝔅.2).choose_spec.choose_spec
  have hfib : ∀ p : PNClass F E × unitQuot F E,
      Nat.card {𝔅 : T // g 𝔅 = p} =
        (RepIdeals (F := F) (classRep E p.1.1 : Ideal (𝓞 E)) (scaleOf p.1 p.2) (algebraMap (𝓞 F) F ν)).ncard := by
    intro p
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_congr
      { toFun := fun 𝔅 => ⟨𝔅.1.1, by have h := hg 𝔅.1; rw [𝔅.2] at h; exact h⟩
        invFun := fun 𝔅 => ⟨⟨𝔅.1, relNorm_of_mem_repIdeals 𝔅.2⟩, by
          obtain ⟨h1, h2⟩ := eq_of_mem_repIdeals hν (hg ⟨𝔅.1, relNorm_of_mem_repIdeals 𝔅.2⟩) 𝔅.2
          exact Prod.ext h1 h2⟩
        left_inv := fun 𝔅 => rfl
        right_inv := fun 𝔅 => rfl }
  have : ∀ p, Finite {𝔅 : T // g 𝔅 = p} := fun p => Subtype.finite
  rw [relNormCount, ← Nat.card_congr (Equiv.sigmaFiberEquiv g), Nat.card_sigma]
  exact Finset.sum_congr rfl fun p _ => (hfib p).symm

/-- **Dirichlet's formula over $F$ with the splitting character** (`relNormCount_eq_finprod`): the class sum equals
$w_1\prod_\mathfrak p\sum_{j=0}^{v_\mathfrak p(\nu)}\chi_{E/F}(\mathfrak p)^j = w_1\sum_{\mathfrak d \mid (\nu)}\chi_{E/F}(\mathfrak d)$. -/
@[kb "cox2013" "Dirichlet's formula; Shimura (2010) §4 [unverified]"]
theorem sum_repNumLat_eq_finprod [Finite (NormOneUnits F E)] {ν : 𝓞 F} (hν : ν ≠ 0) :
    ((∑ C : PNClass F E, ∑ η : unitQuot F E,
      repNumLat (scaleOf C η • normForm F E) (idealLat F (classRep E C.1 : Ideal (𝓞 E)))
        (algebraMap (𝓞 F) F ν) : ℕ) : ℤ) =
    Nat.card (NormOneUnits F E) * ∏ᶠ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      geomSum (relChar E 𝔭)
        (Multiset.count 𝔭.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {ν}))) := by
  rw [sum_repNumLat_eq hν, Nat.cast_mul, relNormCount_eq_finprod (Algebra.IsQuadraticExtension.finrank_eq_two F E)
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hν)]

/-- **CM case** (`card_normOneUnits`): the class sum is $w_E\cdot\#\{\mathfrak B : N_{E/F}\mathfrak B = (\nu)\}$. -/
@[kb "cox2013" "Dirichlet's formula; Shimura (2010) §4 [unverified]"]
theorem sum_repNumLat_eq_cm [IsTotallyReal F] [IsTotallyComplex E] {ν : 𝓞 F} (hν : ν ≠ 0) :
    ∑ C : PNClass F E, ∑ η : unitQuot F E,
      repNumLat (scaleOf C η • normForm F E) (idealLat F (classRep E C.1 : Ideal (𝓞 E)))
        (algebraMap (𝓞 F) F ν) =
    torsionOrder E * relNormCount E (Ideal.span {ν}) := by
  have := finite_normOneUnits (F := F) (E := E)
  rw [sum_repNumLat_eq hν, card_normOneUnits]

end QuadFormsKB.Binary.Rel
