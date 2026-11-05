/-
# O'Meara §31: rational function fields, function fields and global fields (31:4, 31:5, 31:7–31:9)

**Setting.** O'Meara's rational function field is a field $Q = k(x)$ with $k$ a finite subfield and $x$ transcendental
over $k$; Mathlib's model is `RatFunc k`, with integers $k[x]$ and finite spots the height-one primes of $k[x]$
(`Sec31.lean`). Mathlib's `FunctionField Fq F` is a finite extension of `RatFunc Fq`.

**Defines**
* `IsRationalFunctionField Q` (§31, p. 55);
* `IsFunctionFieldOM F` (**31:7**): a finite extension of a rational function field;
* `IsGlobalFieldOM F` (**31:8**): a finite extension of a rational global field, i.e. a number field or a function
  field.
Comparison with Mathlib: `isRationalFunctionField_ratFunc`, `isFunctionFieldOM_of_functionField`,
`isGlobalFieldOM_of_numberField`, `isGlobalFieldOM_iff`.

**Proves**
* `residue_card_polynomial`, `residue_infty_representatives` (**31:4**, function field case: the residue class field
  at a prime polynomial $p$ has $q^{\deg p}$ elements, with the polynomials of degree $< \deg p$ as representatives;
  $k$ is a representative set at $\infty$). The number case is `residue_card_int` (`Sec31.lean`);
* `padic_expansion` (**31:5**): every non-zero $p$-adic number is uniquely $\sum_{\nu \ge m} c_\nu p^\nu$ with
  $0 \le c_\nu < p$, $c_m \ne 0$, $m$ its order;
* `isFunctionFieldOM_finite_separable` (**31:9**, function field case: separable generation). The number case is
  `numberField_finite_separable`.
-/
import QuadFormsKB.Citation
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.FunctionField
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import QuadFormsKB.Literature.OMeara.Sec31

open Polynomial IsDedekindDomain

namespace QuadFormsKB.OMeara

/-- A *rational function field* (§31, p. 55): a field $Q$ with a finite subfield $k$ and an element $x$
transcendental over $k$ such that $Q = k(x)$. ($k$ is the *constant field*; it does not depend on $x$, 31:3.) -/
@[kb "omeara1963" "§31, p. 55 (rational function field k(x) over a finite constant field k)"]
def IsRationalFunctionField (Q : Type*) [Field Q] : Prop :=
  ∃ (k : Subfield Q) (x : Q), Finite k ∧ Transcendental k x ∧ IntermediateField.adjoin k {x} = ⊤


/-- Criterion: a surjective ring map from `RatFunc k0` onto a field `Q`, `k0` finite, shows `Q` is a
rational function field. -/
theorem isRationalFunctionField_of_surjective {k0 Q : Type*} [Field k0] [Finite k0] [Field Q]
    (φ : RatFunc k0 →+* Q) (hφ : Function.Surjective φ) : IsRationalFunctionField Q := by
  classical
  let ψ : k0 →+* Q := φ.comp (algebraMap k0 (RatFunc k0))
  let _ : Algebra k0 Q := ψ.toAlgebra
  refine ⟨ψ.fieldRange, φ RatFunc.X, ?_, ?_, ?_⟩
  · have : Finite (Set.range ψ) := Set.finite_range ψ
    exact this
  · let f : k0 ≃+* ψ.fieldRange := RingEquiv.ofBijective (ψ.codRestrict ψ.fieldRange (fun a => ⟨a, rfl⟩))
      ⟨fun a b h => ψ.injective (congrArg Subtype.val h), fun ⟨_, a, ha⟩ => ⟨a, Subtype.ext ha⟩⟩
    have h1 : Transcendental k0 (φ RatFunc.X) := by
      rw [transcendental_ringHom_iff_of_comp_eq (RingEquiv.refl k0) φ φ.injective rfl]
      exact RatFunc.transcendental_X
    rwa [← transcendental_ringHom_iff_of_comp_eq f (RingHom.id Q) Function.injective_id
      (by ext a; rfl)] at h1
  · rw [eq_top_iff]
    intro y _
    obtain ⟨r, rfl⟩ := hφ y
    set L := IntermediateField.adjoin ψ.fieldRange {φ RatFunc.X} with hL
    have hpoly : ∀ p : k0[X], φ (algebraMap k0[X] (RatFunc k0) p) ∈ L := by
      intro p
      induction p using Polynomial.induction_on' with
      | add p q hp hq => rw [map_add, map_add]; exact L.add_mem hp hq
      | monomial n a =>
        have : (monomial n a : k0[X]) = C a * X ^ n := by rw [C_mul_X_pow_eq_monomial]
        rw [this, map_mul, map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X, map_pow]
        have hx : φ RatFunc.X ∈ L := IntermediateField.mem_adjoin_simple_self _ _
        have ha : φ (RatFunc.C a) ∈ L := L.algebraMap_mem (⟨ψ a, a, rfl⟩ : ψ.fieldRange)
        exact L.mul_mem ha (_root_.pow_mem hx n)
    have : r = algebraMap k0[X] (RatFunc k0) r.num / algebraMap k0[X] (RatFunc k0) r.denom :=
      (RatFunc.num_div_denom r).symm
    rw [this, map_div₀]
    exact L.div_mem (hpoly _) (hpoly _)

/-- Mathlib's `RatFunc k` over a finite field $k$ is a rational function field. -/
theorem isRationalFunctionField_ratFunc (k : Type*) [Field k] [Finite k] :
    IsRationalFunctionField (RatFunc k) :=
  isRationalFunctionField_of_surjective (RingHom.id _) Function.surjective_id

/-- **31:7 (Definition).** An *algebraic function field*, or *function field*, is a finite extension of a rational
function field. -/
@[kb "omeara1963" "§31, 31:7, p. 58"]
def IsFunctionFieldOM (F : Type*) [Field F] : Prop :=
  ∃ Q : Subfield F, IsRationalFunctionField Q ∧ FiniteDimensional Q F

/-- A function field in Mathlib's sense (`FunctionField Fq F`, a finite extension of `RatFunc Fq`) over a finite
field $\mathbb F_q$ is a function field in O'Meara's sense. -/
theorem isFunctionFieldOM_of_functionField (Fq F : Type*) [Field Fq] [Finite Fq] [Field F]
    [Algebra (RatFunc Fq) F] [FunctionField Fq F] : IsFunctionFieldOM F := by
  let Q : Subfield F := (algebraMap (RatFunc Fq) F).fieldRange
  refine ⟨Q, isRationalFunctionField_of_surjective (algebraMap (RatFunc Fq) F).rangeRestrict
    (algebraMap (RatFunc Fq) F).rangeRestrict_surjective, ?_⟩
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := RatFunc Fq) (M := F)
  refine ⟨⟨s, ?_⟩⟩
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ Submodule.span (RatFunc Fq) (s : Set F) := by rw [hs]; trivial
  clear ‹y ∈ ⊤›
  induction hy using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span hz
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul a z _ hz =>
    have : a • z = (⟨algebraMap (RatFunc Fq) F a, a, rfl⟩ : Q) • z := by
      rw [Algebra.smul_def]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ hz

/-- **31:8 (Definition).** A *global field* is a finite extension of a rational global field: a finite extension of
a rational number field (a field of characteristic $0$ finite over $\mathbb Q$, i.e. a number field, 31:6) or of a
rational function field (a function field, 31:7). -/
@[kb "omeara1963" "§31, 31:8, p. 58"]
def IsGlobalFieldOM (F : Type*) [Field F] : Prop :=
  (∃ _ : CharZero F, FiniteDimensional ℚ F) ∨ IsFunctionFieldOM F

/-- A number field is a global field. -/
theorem isGlobalFieldOM_of_numberField (F : Type*) [Field F] [NumberField F] : IsGlobalFieldOM F :=
  Or.inl ⟨inferInstance, inferInstance⟩

/-- The global fields are the number fields and the function fields (31:8, "in other words"). -/
theorem isGlobalFieldOM_iff (F : Type*) [Field F] :
    IsGlobalFieldOM F ↔ (∃ _ : CharZero F, NumberField F) ∨ IsFunctionFieldOM F := by
  refine or_congr ⟨fun ⟨h, hd⟩ => ⟨h, @NumberField.mk F _ h hd⟩,
    fun ⟨h, hd⟩ => ⟨h, inferInstance⟩⟩ Iff.rfl

universe u

theorem ratFunc_equiv_of_isRationalFunctionField {Q : Type u} [Field Q]
    (h : IsRationalFunctionField Q) :
    ∃ (k0 : Type u) (_ : Field k0) (_ : Finite k0), Nonempty (RatFunc k0 ≃+* Q) := by
  obtain ⟨k, x, hk, hx, hadj⟩ := h
  refine ⟨k, inferInstance, hk, ⟨?_⟩⟩
  exact ((RatFunc.algEquivOfTranscendental x hx).trans
    ((IntermediateField.equivOfEq hadj).trans IntermediateField.topEquiv)).toRingEquiv

open Cardinal in
theorem sep_main {k0 F : Type*} [Field k0] [Finite k0] [Field F] [Algebra (RatFunc k0) F]
    [FiniteDimensional (RatFunc k0) F] :
    ∃ Q' : Subfield F, IsRationalFunctionField Q' ∧ FiniteDimensional Q' F ∧
      Algebra.IsSeparable Q' F := by
  classical
  let : Algebra k0 F :=
    ((algebraMap (RatFunc k0) F).comp (algebraMap k0 (RatFunc k0))).toAlgebra
  have : IsScalarTower k0 (RatFunc k0) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap (RatFunc k0) F) :=
    (algebraMap (RatFunc k0) F).injective
  have : Algebra.EssFiniteType k0 (RatFunc k0) :=
    @Algebra.EssFiniteType.comp k0 k0[X] (RatFunc k0) _ _ _ _ _ _ _ inferInstance
      (Algebra.EssFiniteType.of_isLocalization (R := k0[X]) (S := RatFunc k0) (nonZeroDivisors k0[X]))
  have : Algebra.EssFiniteType (RatFunc k0) F := inferInstance
  have : Algebra.EssFiniteType k0 F := Algebra.EssFiniteType.comp k0 (RatFunc k0) F
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k0 F
  set x : F := algebraMap (RatFunc k0) F RatFunc.X with hxdef
  have hx : Transcendental k0 x := by
    rw [hxdef, transcendental_ringHom_iff_of_comp_eq (RingEquiv.refl k0)
      (algebraMap (RatFunc k0) F) hinj rfl]
    exact RatFunc.transcendental_X
  -- F is algebraic over the subalgebra k0[x]
  have halg : Algebra.IsAlgebraic (Algebra.adjoin k0 {x}) F := by
    let : Algebra k0[X] F :=
      ((algebraMap (RatFunc k0) F).comp (algebraMap k0[X] (RatFunc k0))).toAlgebra
    have : IsScalarTower k0[X] (RatFunc k0) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have : IsScalarTower k0 k0[X] F := IsScalarTower.of_algebraMap_eq (fun a => by
      exact congrArg (algebraMap (RatFunc k0) F) (IsScalarTower.algebraMap_apply k0 k0[X] (RatFunc k0) a))
    refine ⟨fun a => ?_⟩
    have h1 : IsAlgebraic (RatFunc k0) a := Algebra.IsAlgebraic.isAlgebraic a
    have h2 : IsAlgebraic k0[X] a := (IsFractionRing.isAlgebraic_iff k0[X] (RatFunc k0) F).2 h1
    let f : k0[X] →+* Algebra.adjoin k0 {x} :=
      ((Polynomial.aeval x : k0[X] →ₐ[k0] F).codRestrict (Algebra.adjoin k0 {x})
        (fun p => Polynomial.aeval_mem_adjoin_singleton k0 x)).toRingHom
    have hfinj : Function.Injective f := by
      intro p q hpq
      have := congrArg Subtype.val hpq
      exact (transcendental_iff_injective.1 hx) this
    refine h2.ringHom_of_comp_eq f (RingHom.id F) hfinj ?_
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · show Polynomial.aeval x (Polynomial.C a) =
        algebraMap (RatFunc k0) F (algebraMap k0[X] (RatFunc k0) (Polynomial.C a))
      rw [Polynomial.aeval_C, RatFunc.algebraMap_C]
      rfl
    · show Polynomial.aeval x (Polynomial.X : k0[X]) =
        algebraMap (RatFunc k0) F (algebraMap k0[X] (RatFunc k0) Polynomial.X)
      simp [hxdef]
  have hle : Algebra.trdeg k0 F ≤ 1 := by
    have := Algebra.IsAlgebraic.trdeg_le_cardinalMk k0 ({x} : Set F)
    simpa using this
  have hcard := hs.cardinalMk_eq_trdeg
  rw [Cardinal.mk_coe_finset] at hcard
  have hne : Nonempty s := hs.nonempty_iff_transcendental.2 ⟨⟨x, hx⟩⟩
  have hcard1 : s.card = 1 := by
    rw [← hcard] at hle
    have h1 : s.card ≤ 1 := by exact_mod_cast hle
    have h2 : 0 < s.card := by
      obtain ⟨a, ha⟩ := hne
      exact Finset.card_pos.2 ⟨a, ha⟩
    omega
  obtain ⟨y, rfl⟩ := Finset.card_eq_one.1 hcard1
  have hy : Transcendental k0 y := by
    have := hs.1
    rw [algebraicIndependent_singleton_iff (R := k0) (x := ((↑) : ↥({y} : Finset F) → F))
      ⟨y, by simp⟩] at this
    simpa using this
  have hsep' : Algebra.IsSeparable (IntermediateField.adjoin k0 ({y} : Set F)) F := by
    rw [Finset.coe_singleton] at hsep
    exact hsep
  have halgK : Algebra.IsAlgebraic (IntermediateField.adjoin k0 ({y} : Set F)) F := by
    have := hs.isAlgebraic_field
    convert! this <;> simp
  refine ⟨(IntermediateField.adjoin k0 ({y} : Set F)).toSubfield, ?_, ?_, hsep'⟩
  · exact isRationalFunctionField_of_surjective
      (RatFunc.algEquivOfTranscendental y hy).toRingEquiv.toRingHom
      (RatFunc.algEquivOfTranscendental y hy).toRingEquiv.surjective
  · have : Algebra.EssFiniteType (IntermediateField.adjoin k0 ({y} : Set F)) F :=
      Algebra.EssFiniteType.of_comp k0 _ F
    obtain ⟨S, hS⟩ := IntermediateField.fg_top (IntermediateField.adjoin k0 ({y} : Set F)) F
    have hfin : FiniteDimensional (IntermediateField.adjoin k0 ({y} : Set F))
        (IntermediateField.adjoin (IntermediateField.adjoin k0 ({y} : Set F)) (S : Set F)) :=
      IntermediateField.finiteDimensional_adjoin
        (fun z _ => (Algebra.IsAlgebraic.isAlgebraic z).isIntegral)
    rw [hS] at hfin
    have hK : FiniteDimensional (IntermediateField.adjoin k0 ({y} : Set F)) F :=
      LinearEquiv.finiteDimensional (IntermediateField.topEquiv.toLinearEquiv)
    exact hK

/-- **31:9 (function field case).** Every function field $F$ is a finite separable extension of a rational function
field: there is a subfield $Q = k(x) \subseteq F$ (for a suitable choice of $x$) with $F/Q$ finite and separable.
O'Meara takes $p$-th roots of $x$; the proof here uses Mathlib's separable generation of finitely generated extensions
of a perfect field (`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`). The number field case is
`numberField_finite_separable`. -/
@[kb "omeara1963" "§31, 31:9, p. 58 (function field case)"]
theorem isFunctionFieldOM_finite_separable {F : Type*} [Field F] (hF : IsFunctionFieldOM F) :
    ∃ Q : Subfield F, IsRationalFunctionField Q ∧ FiniteDimensional Q F ∧ Algebra.IsSeparable Q F := by
  obtain ⟨Q, hQ, hfd⟩ := hF
  obtain ⟨k0, _, _, ⟨e⟩⟩ := ratFunc_equiv_of_isRationalFunctionField hQ
  let _ : Algebra (RatFunc k0) F := (Q.subtype.comp e.toRingHom).toAlgebra
  have : FiniteDimensional (RatFunc k0) F := by
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Q) (M := F)
    refine ⟨⟨s, ?_⟩⟩
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ Submodule.span Q (s : Set F) := by rw [hs]; trivial
    clear ‹y ∈ ⊤›
    induction hy using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span hz
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul q z _ hz =>
      have : q • z = (e.symm q) • z := by
        rw [Algebra.smul_def, Algebra.smul_def]
        show (q : F) * z = (Q.subtype (e (e.symm q))) * z
        simp
      rw [this]
      exact Submodule.smul_mem _ _ hz
  exact sep_main (k0 := k0) (F := F)

/-- **31:4 (function field case, finite spots).** Let $k$ be a finite field with $q$ elements and $\mathfrak p$ a
finite spot of $k(x)$, i.e. a height-one prime of $k[x]$. Then $\mathfrak p$ is generated by a prime polynomial $p$
(monic irreducible), the residue class field $k[x]/\mathfrak p$ has $q^{\deg p}$ elements, and the polynomials of degree
$< \deg p$ form a representative set (each class contains exactly one). -/
@[kb "omeara1963" "§31, 31:4, p. 57 (function field case)"]
theorem residue_card_polynomial (k : Type*) [Field k] [Fintype k] (v : HeightOneSpectrum k[X]) :
    ∃ p : k[X], p.Monic ∧ Irreducible p ∧ v.asIdeal = Ideal.span {p} ∧
      Nat.card (k[X] ⧸ v.asIdeal) = Fintype.card k ^ p.natDegree ∧
      ∀ f : k[X], ∃! r : k[X], r.degree < p.degree ∧ f - r ∈ v.asIdeal := by
  classical
  have hprime := Submodule.IsPrincipal.prime_generator_of_isPrime v.asIdeal v.ne_bot
  set g := Submodule.IsPrincipal.generator v.asIdeal with hg
  have hg0 : g ≠ 0 := hprime.ne_zero
  have hspan : v.asIdeal = Ideal.span {g} := Ideal.span_singleton_generator v.asIdeal |>.symm
  set p := normalize g with hp
  have hp0 : p ≠ 0 := by simpa [hp] using hg0
  have hpm : p.Monic := Polynomial.monic_normalize hg0
  have hassoc : Associated g p := (normalize_associated g).symm
  have hI : v.asIdeal = Ideal.span {p} := by
    rw [hspan]; exact Ideal.span_singleton_eq_span_singleton.2 hassoc
  have hirr : Irreducible p := hassoc.irreducible_iff.1 hprime.irreducible
  have hmem : ∀ f : k[X], f - f %ₘ p ∈ v.asIdeal := by
    intro f
    rw [hI, Ideal.mem_span_singleton]
    refine ⟨f /ₘ p, ?_⟩
    have := modByMonic_add_div f p
    linear_combination (-1 : k[X]) * this
  have hex : ∀ f : k[X], ∃! r : k[X], r.degree < p.degree ∧ f - r ∈ v.asIdeal := by
    intro f
    refine ⟨f %ₘ p, ⟨degree_modByMonic_lt f hpm, ?_⟩, ?_⟩
    · rw [hI, Ideal.mem_span_singleton]
      refine ⟨f /ₘ p, ?_⟩
      have := modByMonic_add_div f p
      linear_combination (-1 : k[X]) * this
    · rintro r ⟨hr, hfr⟩
      rw [hI, Ideal.mem_span_singleton] at hfr
      obtain ⟨q, hq⟩ := hfr
      have h1 : p ∣ r - f %ₘ p := by
        have := modByMonic_add_div f p
        refine ⟨f /ₘ p - q, ?_⟩
        linear_combination (-1 : k[X]) * hq - this
      have h2 := degree_modByMonic_lt f hpm
      have h3 : (r - f %ₘ p).degree < p.degree :=
        lt_of_le_of_lt (degree_sub_le _ _) (max_lt hr h2)
      exact sub_eq_zero.1 (eq_zero_of_dvd_of_degree_lt h1 h3)
  refine ⟨p, hpm, hirr, hI, ?_, hex⟩
  have hdeg : p.degree = (p.natDegree : WithBot ℕ) := degree_eq_natDegree hp0
  let F : Polynomial.degreeLT k p.natDegree → k[X] ⧸ v.asIdeal := fun r => Ideal.Quotient.mk _ r.1
  have hbij : Function.Bijective F := by
    constructor
    · intro r r' h
      have h1 : (r.1 - r'.1) ∈ v.asIdeal := by
        rw [← Ideal.Quotient.eq]; exact h
      obtain ⟨hr, hr'⟩ := (⟨Polynomial.mem_degreeLT.1 r.2, Polynomial.mem_degreeLT.1 r'.2⟩ :
        _ ∧ _)
      rw [← hdeg] at hr hr'
      obtain ⟨y, hy⟩ := hex r.1
      have e1 := hy.2 r.1 ⟨hr, by simp [sub_self, Ideal.zero_mem]⟩
      have e2 := hy.2 r'.1 ⟨hr', by
        have : r.1 - r'.1 ∈ v.asIdeal := h1
        simpa using this⟩
      exact Subtype.ext (e1.trans e2.symm)
    · intro y
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine ⟨⟨f %ₘ p, Polynomial.mem_degreeLT.2 (by rw [← hdeg]; exact degree_modByMonic_lt f hpm)⟩, ?_⟩
      show Ideal.Quotient.mk _ (f %ₘ p) = _
      rw [Ideal.Quotient.eq]
      have := v.asIdeal.neg_mem (hmem f)
      simpa using this
  rw [← Nat.card_congr (Equiv.ofBijective F hbij)]
  rw [Nat.card_congr (Polynomial.degreeLTEquiv k p.natDegree).toEquiv]
  simp


/-- Valuation at infinity of a quotient of polynomials, strict form. -/
theorem inftyValuation_div_lt_one {k : Type*} [Field k] [DecidableEq (RatFunc k)] (a b : k[X])
    (hb : b ≠ 0) :
    RatFunc.inftyValuation k (algebraMap k[X] (RatFunc k) a / algebraMap k[X] (RatFunc k) b) < 1 ↔
      a = 0 ∨ a.natDegree < b.natDegree := by
  have hb' : RatFunc.inftyValuation k (algebraMap k[X] (RatFunc k) b) = WithZero.exp (b.natDegree : ℤ) := by
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation.polynomial k hb]
  have hbne : RatFunc.inftyValuation k (algebraMap k[X] (RatFunc k) b) ≠ 0 := by
    rw [hb']; exact WithZero.exp_ne_zero
  rw [map_div₀, div_lt_one₀ (zero_lt_iff.2 hbne), hb']
  by_cases ha : a = 0
  · simp [ha]
  · rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation.polynomial k ha, WithZero.exp_lt_exp]
    simp [ha]

/-- Valuation at infinity of a quotient of polynomials, non-strict form. -/
theorem inftyValuation_div_le_one {k : Type*} [Field k] [DecidableEq (RatFunc k)] (a b : k[X])
    (hb : b ≠ 0) :
    RatFunc.inftyValuation k (algebraMap k[X] (RatFunc k) a / algebraMap k[X] (RatFunc k) b) ≤ 1 ↔
      a = 0 ∨ a.natDegree ≤ b.natDegree := by
  have hb' : RatFunc.inftyValuation k (algebraMap k[X] (RatFunc k) b) = WithZero.exp (b.natDegree : ℤ) := by
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation.polynomial k hb]
  have hbne : RatFunc.inftyValuation k (algebraMap k[X] (RatFunc k) b) ≠ 0 := by
    rw [hb']; exact WithZero.exp_ne_zero
  rw [map_div₀, div_le_one₀ (zero_lt_iff.2 hbne), hb']
  by_cases ha : a = 0
  · simp [ha]
  · rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation.polynomial k ha, WithZero.exp_le_exp]
    simp [ha]

/-- **31:4 (function field case, the spot $\infty$).** In a rational function field $k(x)$ the constant field $k$ is a
representative set of the residue class field at $\infty$: every element integral at $\infty$ is congruent modulo the
maximal ideal at $\infty$ to exactly one constant. -/
@[kb "omeara1963" "§31, 31:4, p. 57 (k is a representative set at ∞)"]
theorem residue_infty_representatives (k : Type*) [Field k] [DecidableEq (RatFunc k)] (x : RatFunc k)
    (hx : RatFunc.inftyValuation k x ≤ 1) :
    ∃! c : k, RatFunc.inftyValuation k (x - RatFunc.C c) < 1 := by
  have hb0 : x.denom ≠ 0 := RatFunc.denom_ne_zero x
  have hxe : x = algebraMap k[X] (RatFunc k) x.num / algebraMap k[X] (RatFunc k) x.denom :=
    (RatFunc.num_div_denom x).symm
  have hle := (inftyValuation_div_le_one x.num x.denom hb0).1 (hxe ▸ hx)
  have hbd : (algebraMap k[X] (RatFunc k) x.denom) ≠ 0 := by simpa using hb0
  have uniq : ∀ c c' : k, RatFunc.inftyValuation k (x - RatFunc.C c) < 1 →
      RatFunc.inftyValuation k (x - RatFunc.C c') < 1 → c' = c := by
    intro c c' h1 h2
    by_contra hne
    have h3 : RatFunc.inftyValuation k (RatFunc.C (c - c')) = 1 :=
      RatFunc.inftyValuation.C k (sub_ne_zero.2 (Ne.symm hne))
    have h4 : RatFunc.C (c - c') = (x - RatFunc.C c') - (x - RatFunc.C c) := by
      rw [map_sub]; ring
    have h5 := (RatFunc.inftyValuation k).map_sub (x - RatFunc.C c') (x - RatFunc.C c)
    rw [← h4, h3] at h5
    exact absurd (lt_of_le_of_lt h5 (max_lt h2 h1)) (lt_irrefl _)
  obtain ⟨c0, hc0⟩ : ∃ c : k, RatFunc.inftyValuation k (x - RatFunc.C c) < 1 := by
    refine ⟨x.num.coeff x.denom.natDegree / x.denom.leadingCoeff, ?_⟩
    set c := x.num.coeff x.denom.natDegree / x.denom.leadingCoeff with hc
    have e : x - RatFunc.C c =
        algebraMap k[X] (RatFunc k) (x.num - Polynomial.C c * x.denom) /
          algebraMap k[X] (RatFunc k) x.denom := by
      rw [map_sub, map_mul, RatFunc.algebraMap_C, sub_div, mul_div_cancel_right₀ _ hbd, ← hxe]
    show RatFunc.inftyValuation k (x - RatFunc.C c) < 1
    rw [e, inftyValuation_div_lt_one _ _ hb0]
    by_cases h0 : x.num - Polynomial.C c * x.denom = 0
    · exact Or.inl h0
    · right
      have hlt : (x.num - Polynomial.C c * x.denom).degree < x.denom.degree := by
        rw [degree_eq_natDegree hb0, Polynomial.degree_lt_iff_coeff_zero]
        intro m hm
        rw [coeff_sub, coeff_C_mul]
        rcases hm.eq_or_lt' with h | h
        · subst h
          rw [hc]
          have : x.denom.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hb0
          rw [Polynomial.leadingCoeff] at this ⊢
          field_simp
          ring
        · have h1 : x.denom.coeff m = 0 := coeff_eq_zero_of_natDegree_lt h
          have h2 : x.num.coeff m = 0 := by
            rcases hle with h3 | h3
            · simp [h3]
            · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h3 h)
          rw [h1, h2]; simp
      exact natDegree_lt_natDegree h0 hlt
  exact ⟨c0, hc0, fun c' hc' => uniq _ _ hc0 hc'⟩

section PadicAux
open Filter Topology
namespace PadicAux
variable {p : ℕ} [Fact p.Prime]

/-- partial sum of digits -/
def T (p : ℕ) (c : ℕ → ℕ) (N : ℕ) : ℕ := ∑ k ∈ Finset.range N, c k * p ^ k

theorem T_lt (hp : 0 < p) (c : ℕ → ℕ) (hc : ∀ k, c k < p) (N : ℕ) : T p c N < p ^ N := by
  induction N with
  | zero => simp [T]
  | succ n ih =>
    have : T p c (n+1) = T p c n + c n * p ^ n := by simp [T, Finset.sum_range_succ]
    rw [this, pow_succ]
    have h1 : c n * p ^ n ≤ (p - 1) * p ^ n := Nat.mul_le_mul_right _ (by have := hc n; omega)
    have h2 : (p - 1) * p ^ n + p ^ n = p * p ^ n := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp; ring
    nlinarith

theorem T_dvd (c : ℕ → ℕ) {N M : ℕ} (h : N ≤ M) : (p ^ N : ℤ) ∣ (T p c M : ℤ) - T p c N := by
  induction M, h using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    have : T p c (M+1) = T p c M + c M * p ^ M := by simp [T, Finset.sum_range_succ]
    rw [this]; push_cast
    have : (p ^ N : ℤ) ∣ (c M : ℤ) * p ^ M :=
      Dvd.dvd.mul_left (pow_dvd_pow _ hM) _
    have := dvd_add ih this
    convert this using 1; ring

theorem hasSum_of_tendsto {f : ℕ → ℚ_[p]} {s : ℚ_[p]}
    (h : Tendsto (fun N => ∑ k ∈ Finset.range N, f k) atTop (𝓝 s)) : HasSum f s := by
  have hs : Summable f := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [Nat.cofinite_eq_atTop]
    have := (h.comp (tendsto_add_atTop_nat 1)).sub h
    simp only [sub_self] at this
    refine this.congr (fun n => ?_)
    simp [Finset.sum_range_succ]
  exact (hs.hasSum_iff_tendsto_nat).2 h


theorem T_eq_appr (z : ℤ_[p]) (c : ℕ → ℕ) (hc : ∀ k, c k < p)
    (hlim : Tendsto (fun N => ((T p c N : ℕ) : ℚ_[p])) atTop (𝓝 (z : ℚ_[p]))) (N : ℕ) :
    T p c N = z.appr N := by
  have h1 : ‖(z : ℚ_[p]) - (T p c N : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(N : ℤ)) := by
    have := (hlim.sub_const (T p c N : ℚ_[p])).norm
    refine le_of_tendsto this ?_
    filter_upwards [eventually_ge_atTop N] with M hM
    have := (Padic.norm_int_le_pow_iff_dvd ((T p c M : ℤ) - T p c N) N).2 (T_dvd c hM)
    simpa using this
  have h2 : ‖(z : ℚ_[p]) - (z.appr N : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(N : ℤ)) := by
    have := (PadicInt.norm_le_pow_iff_mem_span_pow (z - (z.appr N : ℤ_[p])) N).2
      (PadicInt.appr_spec N z)
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at this
    exact this
  have h3 : ‖(((T p c N : ℤ) - (z.appr N : ℤ) : ℤ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(N : ℤ)) := by
    have e : (((T p c N : ℤ) - (z.appr N : ℤ) : ℤ) : ℚ_[p]) =
        ((z : ℚ_[p]) - (z.appr N : ℚ_[p])) + (-((z : ℚ_[p]) - (T p c N : ℚ_[p]))) := by
      push_cast; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 ?_)
    rwa [norm_neg]
  have h4 := (Padic.norm_int_le_pow_iff_dvd _ N).1 h3
  have hp := (Fact.out : p.Prime).pos
  have hT := T_lt hp c hc N
  have hA := PadicInt.appr_lt z N
  have : ((T p c N : ℤ) - (z.appr N : ℤ)) = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd h4 ?_
    rw [abs_lt]
    have hT' : (T p c N : ℤ) < (p : ℤ) ^ N := by exact_mod_cast hT
    have hA' : (z.appr N : ℤ) < (p : ℤ) ^ N := by exact_mod_cast hA
    constructor <;> omega
  omega


theorem T_succ (c : ℕ → ℕ) (N : ℕ) : T p c (N + 1) = T p c N + c N * p ^ N := by
  simp [T, Finset.sum_range_succ]

theorem exists_unit_part {x : ℚ_[p]} (hx : x ≠ 0) :
    ∃ z : ℤ_[p], (z : ℚ_[p]) = x * (p : ℚ_[p]) ^ (-x.valuation) ∧ ‖z‖ = 1 := by
  have hn : ‖x * (p : ℚ_[p]) ^ (-x.valuation)‖ = 1 := by
    rw [norm_mul, norm_zpow, Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_p]
    have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    rw [inv_zpow, ← zpow_neg, neg_neg, ← zpow_add₀ hp]; simp
  exact ⟨⟨_, hn.le⟩, rfl, PadicInt.norm_def.trans hn⟩

theorem padic_expansion_aux {x : ℚ_[p]} (hx : x ≠ 0) :
    ∃! c : ℕ → ℕ, (∀ k, c k < p) ∧ c 0 ≠ 0 ∧
      HasSum (fun k : ℕ => (c k : ℚ_[p]) * (p : ℚ_[p]) ^ (x.valuation + k)) x := by
  obtain ⟨z, hz, hz1⟩ := exists_unit_part hx
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpp := (Fact.out : p.Prime).pos
  have hxz : x = (p : ℚ_[p]) ^ x.valuation * z := by
    rw [hz, mul_comm x, ← mul_assoc, ← zpow_add₀ hp0]; simp
  -- partial sums of the series
  have hpart : ∀ (c : ℕ → ℕ) (N : ℕ),
      ∑ k ∈ Finset.range N, (c k : ℚ_[p]) * (p : ℚ_[p]) ^ (x.valuation + k) =
        (p : ℚ_[p]) ^ x.valuation * (T p c N : ℚ_[p]) := by
    intro c N
    simp only [T, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [zpow_add₀ hp0]; push_cast; rw [zpow_natCast]; ring
  -- existence
  let A : ℕ → ℕ := fun N => z.appr N
  let c0 : ℕ → ℕ := fun k => (A (k + 1) - A k) / p ^ k
  have hc0mul : ∀ k, c0 k * p ^ k = A (k + 1) - A k := fun k =>
    Nat.div_mul_cancel (PadicInt.dvd_appr_sub_appr z k (k + 1) (Nat.le_succ k))
  have hT0 : ∀ N, T p c0 N = A N := by
    intro N
    induction N with
    | zero => have := PadicInt.appr_lt z 0; simp [T, A] at this ⊢; omega
    | succ n ih =>
      rw [T_succ, ih, hc0mul]
      have h1 : A n ≤ A (n + 1) := PadicInt.appr_mono z (Nat.le_succ n)
      omega
  have hvalid : (∀ k, c0 k < p) ∧ c0 0 ≠ 0 ∧
      HasSum (fun k : ℕ => (c0 k : ℚ_[p]) * (p : ℚ_[p]) ^ (x.valuation + k)) x := by
    refine ⟨?_, ?_, ?_⟩
    · intro k
      rw [Nat.div_lt_iff_lt_mul (pow_pos hpp k), ← pow_succ']
      have := PadicInt.appr_lt z (k + 1)
      simp only [A] at this ⊢; omega
    · have h0 : c0 0 = A 1 := by
        have := PadicInt.appr_lt z 0
        simp [c0, A] at this ⊢; omega
      rw [h0]
      intro h
      have := PadicInt.appr_spec 1 z
      simp only [A] at h
      rw [h] at this
      simp only [Nat.cast_zero, sub_zero, pow_one, Ideal.mem_span_singleton] at this
      have := (PadicInt.norm_lt_one_iff_dvd z).2 this
      rw [hz1] at this; exact lt_irrefl _ this
    · apply hasSum_of_tendsto
      simp_rw [hpart, hT0]
      have : Tendsto (fun N => (A N : ℚ_[p])) atTop (𝓝 (z : ℚ_[p])) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        have hlim : Tendsto (fun N : ℕ => ((p : ℝ)⁻¹) ^ N) atTop (𝓝 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
            (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))
        refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hlim
        have := (PadicInt.norm_le_pow_iff_mem_span_pow (z - (A N : ℤ_[p])) N).2
          (PadicInt.appr_spec N z)
        rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at this
        rw [norm_sub_rev]
        simpa [zpow_neg, inv_pow] using this
      have h2 := this.const_mul ((p : ℚ_[p]) ^ x.valuation)
      rw [← hxz] at h2
      exact h2.congr' (by simp)
  refine ⟨c0, hvalid, fun d hd => ?_⟩
  obtain ⟨hd1, -, hd3⟩ := hd
  have hlim : Tendsto (fun N => ((T p d N : ℕ) : ℚ_[p])) atTop (𝓝 (z : ℚ_[p])) := by
    have h1 := hd3.tendsto_sum_nat
    simp_rw [hpart] at h1
    have h2 := h1.const_mul ((p : ℚ_[p]) ^ (-x.valuation))
    have e : (p : ℚ_[p]) ^ (-x.valuation) * x = z := by rw [hz, mul_comm]
    rw [e] at h2
    refine h2.congr (fun N => ?_)
    rw [← mul_assoc, ← zpow_add₀ hp0]; simp
  funext k
  have h1 := T_eq_appr z d hd1 hlim (k + 1)
  have h2 := T_eq_appr z d hd1 hlim k
  have h3 := hT0 (k + 1)
  have h4 := hT0 k
  rw [T_succ] at h1 h3
  have : d k * p ^ k = c0 k * p ^ k := by
    have := hc0mul k
    simp only [A] at this ⊢
    omega
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hpp k) this

end PadicAux
end PadicAux

/-- **31:5 (Example).** Every non-zero $p$-adic number $x \in \mathbb Q_p$ has a unique expansion
$x = \sum_{\nu \ge m} c_\nu p^{\nu}$ with digits $0 \le c_\nu < p$, $m = \operatorname{ord}_p x$ and $c_m \ne 0$,
the sum taken in the $p$-adic topology (indexed here by $k = \nu - m \ge 0$). O'Meara deduces it from 16:3. -/
@[kb "omeara1963" "§31, 31:5, p. 57"]
theorem padic_expansion (p : ℕ) [Fact p.Prime] {x : ℚ_[p]} (hx : x ≠ 0) :
    ∃! c : ℕ → ℕ, (∀ k, c k < p) ∧ c 0 ≠ 0 ∧
      HasSum (fun k : ℕ => (c k : ℚ_[p]) * (p : ℚ_[p]) ^ (x.valuation + k)) x :=
  PadicAux.padic_expansion_aux hx

end QuadFormsKB.OMeara
