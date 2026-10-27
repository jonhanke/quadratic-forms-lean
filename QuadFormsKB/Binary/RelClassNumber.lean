import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelAmbiguous
import QuadFormsKB.Binary.RelSiegelGenus

/-!
# The number of totally positive classes of normalized binary lattices over $K^+$

$E/F$ quadratic, $\sigma$ its automorphism. For a class $c = [\mathfrak A] \in \mathrm{Cl}_E$ choose $\mathfrak A'$ with $\mathfrak A\mathfrak A' = (\gamma)$; the pair
$(\mathfrak A\,\sigma\mathfrak A', N\gamma)$ is normalized ($N(\mathfrak A\sigma\mathfrak A') = (N\gamma)$) and its class does not depend on the choices.

* **`jHom`**: $c \mapsto [(\mathfrak A\,\sigma\mathfrak A', N\gamma)]$ is a homomorphism $\mathrm{Cl}_E \to$ `PairClass F E` (the lattice $(\mathfrak A/\sigma\mathfrak A, N)$:
  "$c^{1-\sigma}$ with scale $1$").
* **`range_jHom`** (CM): its image is the principal genus of totally positive classes (Hasse norm theorem — proved in the
  repository — and the ideal Hilbert 90 `principal_identity`).
* **`jHom_eq_one_iff`**: its kernel is the group of strongly ambiguous classes (Hilbert 90).
* **`card_principalGenus_mul_card_strAmb`** (CM): $\#P_0\cdot\#\mathrm{Cl}_E^{\mathrm{str}} = h_E$.
* **`posClassNumberRelation`** ($K$ CM): **`PosClassNumberRelation K` is a theorem**:
  $\#G^+\cdot Q_K\,h_{K^+}\,2^t = 2\cdot2^{t-1}\,h_K$, from $\#G^+ = 2^{t-1}\#P_0$ (Gauss), $\#P_0\,\#\mathrm{Cl}^{\mathrm{str}} = h_K$,
  $\#\mathrm{Cl}^{\mathrm{str}}\,[\mu_K : \{u/\bar u\}] = 2^t h_{K^+}$ (`card_strAmb_mul_index`) and $Q_K\,[\mu_K : \{u/\bar u\}] = 2$ (Mathlib's
  `IsCMField.indexRealUnits_mul_eq`). No class field theory.
* **`siegel_binaryF_genus'`**: Siegel's formula genus by genus over $K^+$, unconditional.

Sources: Hilbert, *Zahlbericht* (1897) §§ 71–75 [unverified]; Chevalley (1933) [unverified]; Hecke (1923) §48 [unverified];
Washington (1997) Thm. 4.12 (Hasse's unit index) [unverified].
-/

open NumberField Module IsDedekindDomain Filter Topology
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-! ### The homomorphism $j : \mathrm{Cl}_E \to$ classes of pairs -/

theorem mul_mem_nzd (A B : (Ideal (𝓞 E))⁰) : (A : Ideal (𝓞 E)) * B ∈ (Ideal (𝓞 E))⁰ :=
  mul_mem A.2 B.2

theorem isPrincipal_rep_mul (c : ClassGroup (𝓞 E)) :
    ((classRep E c : Ideal (𝓞 E)) * classRep E c⁻¹).IsPrincipal := by
  rw [← ClassGroup.mk0_eq_one_iff (mul_mem_nzd _ _)]
  have : ClassGroup.mk0 (classRep E c * classRep E c⁻¹) = 1 := by
    rw [map_mul, mk0_classRep, mk0_classRep, mul_inv_cancel]
  exact this

/-- A generator $\gamma_c$ of $\mathfrak A_c\mathfrak A_{c^{-1}}$. -/
def genOf (c : ClassGroup (𝓞 E)) : 𝓞 E := @Submodule.IsPrincipal.generator _ _ _ _ _ _ (isPrincipal_rep_mul c)

theorem span_genOf (c : ClassGroup (𝓞 E)) :
    Ideal.span {genOf c} = (classRep E c : Ideal (𝓞 E)) * classRep E c⁻¹ :=
  @Ideal.span_singleton_generator _ _ _ (isPrincipal_rep_mul c)

theorem relNorm_mul_conj_eq {B B' : Ideal (𝓞 E)} {δ : 𝓞 E} (h : B * B' = Ideal.span {δ}) :
    Ideal.relNorm (𝓞 F) (B * conjIdeal F B') = Ideal.span {Algebra.intNorm (𝓞 F) (𝓞 E) δ} := by
  rw [map_mul, relNorm_conjIdeal, ← map_mul, h, Ideal.relNorm_singleton]

theorem ne_bot_of_mul_eq_span {B B' : (Ideal (𝓞 E))⁰} :
    (B : Ideal (𝓞 E)) * conjIdeal F (B' : Ideal (𝓞 E)) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot]
  exact mul_ne_zero (by rw [Ne, Ideal.zero_eq_bot]; exact nonZeroDivisors.coe_ne_zero B)
    (by rw [Ne, Ideal.zero_eq_bot]; exact conjIdeal_ne_bot (nonZeroDivisors.coe_ne_zero B'))

/-- The normalized pair $(\mathfrak B\,\sigma\mathfrak B', N\delta)$ for $\mathfrak B\mathfrak B' = (\delta)$. -/
def jPairOf (B B' : (Ideal (𝓞 E))⁰) (δ : 𝓞 E) (h : (B : Ideal (𝓞 E)) * (B' : Ideal (𝓞 E)) = Ideal.span {δ}) : NormPairs F E :=
  ⟨((B : Ideal (𝓞 E)) * conjIdeal F (B' : Ideal (𝓞 E)), Algebra.intNorm (𝓞 F) (𝓞 E) δ),
    ne_bot_of_mul_eq_span, relNorm_mul_conj_eq h⟩

theorem conjIdeal_span_mul (x : 𝓞 E) (A : Ideal (𝓞 E)) :
    conjIdeal F (Ideal.span {x} * A) = Ideal.span {conjO F E x} * conjIdeal F A := by
  rw [conjIdeal_mul, conjIdeal_span]

theorem jPairOf_fst (B B' : (Ideal (𝓞 E))⁰) (δ : 𝓞 E) (h : (B : Ideal (𝓞 E)) * (B' : Ideal (𝓞 E)) = Ideal.span {δ}) :
    ((jPairOf (F := F) B B' δ h : NormPairs F E) : Ideal (𝓞 E) × 𝓞 F).1 =
      (B : Ideal (𝓞 E)) * conjIdeal F (B' : Ideal (𝓞 E)) := rfl

theorem jPairOf_snd (B B' : (Ideal (𝓞 E))⁰) (δ : 𝓞 E) (h : (B : Ideal (𝓞 E)) * (B' : Ideal (𝓞 E)) = Ideal.span {δ}) :
    ((jPairOf (F := F) B B' δ h : NormPairs F E) : Ideal (𝓞 E) × 𝓞 F).2 = Algebra.intNorm (𝓞 F) (𝓞 E) δ := rfl

/-- Building a proper equivalence of pairs from its two equations. -/
theorem pairClass_eq_of {p q : NormPairs F E} (α β : 𝓞 E) (hα : α ≠ 0) (hβ : β ≠ 0)
    (h1 : Ideal.span {α} * (p : Ideal (𝓞 E) × 𝓞 F).1 = Ideal.span {β} * (q : Ideal (𝓞 E) × 𝓞 F).1)
    (h2 : nrm (F := F) β * ((q : Ideal (𝓞 E) × 𝓞 F).2 : F) = nrm (F := F) α * ((p : Ideal (𝓞 E) × 𝓞 F).2 : F)) :
    (p : PairClass F E) = (q : PairClass F E) :=
  (Con.eq _).mpr ⟨α, β, hα, hβ, h1, h2⟩

theorem coe_intNorm (x : 𝓞 E) : ((Algebra.intNorm (𝓞 F) (𝓞 E) x : 𝓞 F) : F) = nrm (F := F) x :=
  algebraMap_intNorm' x

/-- **The class of $(\mathfrak B\sigma\mathfrak B', N\delta)$ depends only on $[\mathfrak B]$.** -/
theorem jPairOf_eq {B B' C C' : (Ideal (𝓞 E))⁰} {δ γ : 𝓞 E} (hB : (B : Ideal (𝓞 E)) * (B' : Ideal (𝓞 E)) = Ideal.span {δ})
    (hC : (C : Ideal (𝓞 E)) * (C' : Ideal (𝓞 E)) = Ideal.span {γ}) (hBC : ClassGroup.mk0 B = ClassGroup.mk0 C) :
    ((jPairOf B B' δ hB : NormPairs F E) : PairClass F E) = (jPairOf C C' γ hC : NormPairs F E) := by
  have hinv : ∀ {X X' : (Ideal (𝓞 E))⁰} {x : 𝓞 E}, (X : Ideal (𝓞 E)) * (X' : Ideal (𝓞 E)) = Ideal.span {x} →
      ClassGroup.mk0 X' = (ClassGroup.mk0 X)⁻¹ := fun {X X' x} h => by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← map_mul]
    show ClassGroup.mk0 ⟨(X : Ideal (𝓞 E)) * (X' : Ideal (𝓞 E)), mul_mem_nzd X X'⟩ = 1
    rw [ClassGroup.mk0_eq_one_iff]
    exact ⟨x, h⟩
  have hBC' : ClassGroup.mk0 B' = ClassGroup.mk0 C' := by rw [hinv hB, hinv hC, hBC]
  obtain ⟨α, β, hα, hβ, h1⟩ := ClassGroup.mk0_eq_mk0_iff.mp hBC
  obtain ⟨α', β', hα', hβ', h1'⟩ := ClassGroup.mk0_eq_mk0_iff.mp hBC'
  have hspan : Ideal.span {α * α' * δ} = Ideal.span {β * β' * γ} := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton, ← hB,
      ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton, ← hC]
    calc Ideal.span {α} * Ideal.span {α'} * ((B : Ideal (𝓞 E)) * (B' : Ideal (𝓞 E)))
        = (Ideal.span {α} * (B : Ideal (𝓞 E))) * (Ideal.span {α'} * (B' : Ideal (𝓞 E))) := by ring
      _ = (Ideal.span {β} * (C : Ideal (𝓞 E))) * (Ideal.span {β'} * (C' : Ideal (𝓞 E))) := by rw [h1, h1']
      _ = _ := by ring
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  refine pairClass_eq_of (α * conjO F E α' * u) (β * conjO F E β')
    (mul_ne_zero (mul_ne_zero hα (conjO_ne_zero hα')) u.ne_zero) (mul_ne_zero hβ (conjO_ne_zero hβ')) ?_ ?_
  · rw [jPairOf_fst, jPairOf_fst, Ideal.span_singleton_mul_right_unit u.isUnit, ← Ideal.span_singleton_mul_span_singleton,
      ← Ideal.span_singleton_mul_span_singleton, ← conjIdeal_span, ← conjIdeal_span]
    calc Ideal.span {α} * conjIdeal F (Ideal.span {α'}) * ((B : Ideal (𝓞 E)) * conjIdeal F B')
        = (Ideal.span {α} * (B : Ideal (𝓞 E))) * conjIdeal F (Ideal.span {α'} * (B' : Ideal (𝓞 E))) := by
          rw [conjIdeal_mul]; ring
      _ = (Ideal.span {β} * (C : Ideal (𝓞 E))) * conjIdeal F (Ideal.span {β'} * (C' : Ideal (𝓞 E))) := by
          rw [h1, h1']
      _ = _ := by rw [conjIdeal_mul]; ring
  · rw [jPairOf_snd, jPairOf_snd, coe_intNorm, coe_intNorm, nrm_mul, nrm_mul, nrm_mul, nrm_conjO, nrm_conjO]
    have := congrArg (nrm (F := F)) hu
    rw [nrm_mul, nrm_mul, nrm_mul, nrm_mul, nrm_mul] at this
    linear_combination -this

variable (F) in
/-- **$j : \mathrm{Cl}_E \to$ `PairClass F E`**, $[\mathfrak A] \mapsto [(\mathfrak A\,\sigma\mathfrak A', N\gamma)]$ ($\mathfrak A\mathfrak A' = (\gamma)$). -/
def jFun (c : ClassGroup (𝓞 E)) : PairClass F E :=
  (jPairOf (F := F) (classRep E c) (classRep E c⁻¹) (genOf c) (span_genOf c).symm : NormPairs F E)

theorem jFun_eq {B B' : (Ideal (𝓞 E))⁰} {δ : 𝓞 E} (hB : (B : Ideal (𝓞 E)) * (B' : Ideal (𝓞 E)) = Ideal.span {δ}) :
    jFun F (ClassGroup.mk0 B) = ((jPairOf B B' δ hB : NormPairs F E) : PairClass F E) := by
  rw [jFun]
  exact jPairOf_eq _ _ (mk0_classRep _)

theorem exists_mul_eq_span (B : (Ideal (𝓞 E))⁰) :
    ∃ (B' : (Ideal (𝓞 E))⁰) (δ : 𝓞 E), (B : Ideal (𝓞 E)) * (B' : Ideal (𝓞 E)) = Ideal.span {δ} := by
  refine ⟨classRep E (ClassGroup.mk0 B)⁻¹, ?_⟩
  have h1 : ClassGroup.mk0 ⟨(B : Ideal (𝓞 E)) * (classRep E (ClassGroup.mk0 B)⁻¹ : Ideal (𝓞 E)),
      mul_mem_nzd _ _⟩ = 1 := by
    rw [show (⟨(B : Ideal (𝓞 E)) * (classRep E (ClassGroup.mk0 B)⁻¹ : Ideal (𝓞 E)), mul_mem_nzd _ _⟩ :
      (Ideal (𝓞 E))⁰) = B * classRep E (ClassGroup.mk0 B)⁻¹ from rfl, map_mul, mk0_classRep, mul_inv_cancel]
  obtain ⟨δ, hδ⟩ := (ClassGroup.mk0_eq_one_iff _).mp h1
  exact ⟨δ, hδ⟩

theorem jFun_one : jFun F (1 : ClassGroup (𝓞 E)) = 1 := by
  have h1 : ((1 : (Ideal (𝓞 E))⁰) : Ideal (𝓞 E)) * ((1 : (Ideal (𝓞 E))⁰) : Ideal (𝓞 E)) = Ideal.span {1} := by
    rw [Ideal.span_singleton_one]; simp
  rw [← map_one ClassGroup.mk0, jFun_eq h1, ← Con.coe_one]
  refine pairClass_eq_of 1 1 one_ne_zero one_ne_zero ?_ ?_
  · rw [jPairOf_fst, show ((1 : NormPairs F E) : Ideal (𝓞 E) × 𝓞 F).1 = ⊤ from Ideal.one_eq_top]
    simp only [Ideal.span_singleton_one, OneMemClass.coe_one, Ideal.one_eq_top, Ideal.top_mul, conjIdeal,
      Ideal.map_top]
  · rw [jPairOf_snd, map_one, show ((1 : NormPairs F E) : Ideal (𝓞 E) × 𝓞 F).2 = 1 from rfl]

theorem jFun_mul (c d : ClassGroup (𝓞 E)) : jFun F (c * d) = jFun F c * jFun F d := by
  obtain ⟨B, rfl⟩ := ClassGroup.mk0_surjective c
  obtain ⟨C, rfl⟩ := ClassGroup.mk0_surjective d
  obtain ⟨B', δ, hB⟩ := exists_mul_eq_span B
  obtain ⟨C', γ, hC⟩ := exists_mul_eq_span C
  have hBC : ((B * C : (Ideal (𝓞 E))⁰) : Ideal (𝓞 E)) * ((B' * C' : (Ideal (𝓞 E))⁰) : Ideal (𝓞 E)) =
      Ideal.span {δ * γ} := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← hB, ← hC, Submonoid.coe_mul, Submonoid.coe_mul]; ring
  rw [← map_mul, jFun_eq hBC, jFun_eq hB, jFun_eq hC, ← Con.coe_mul]
  refine pairClass_eq_of 1 1 one_ne_zero one_ne_zero ?_ ?_
  · rw [Submonoid.coe_mul, Prod.fst_mul, jPairOf_fst, jPairOf_fst, jPairOf_fst, Submonoid.coe_mul,
      Submonoid.coe_mul, conjIdeal_mul]
    ring
  · rw [Submonoid.coe_mul, Prod.snd_mul, jPairOf_snd, jPairOf_snd, jPairOf_snd, map_mul]

variable (F E) in
/-- **$j$ is a homomorphism.** -/
def jHom : ClassGroup (𝓞 E) →* PairClass F E where
  toFun := jFun F
  map_one' := jFun_one
  map_mul' := jFun_mul

theorem jHom_mk0 {B B' : (Ideal (𝓞 E))⁰} {δ : 𝓞 E} (hB : (B : Ideal (𝓞 E)) * (B' : Ideal (𝓞 E)) = Ideal.span {δ}) :
    jHom F E (ClassGroup.mk0 B) = ((jPairOf B B' δ hB : NormPairs F E) : PairClass F E) :=
  jFun_eq hB

/-! ### The kernel of $j$: strongly ambiguous classes -/

theorem gen_ne_zero {B B' : (Ideal (𝓞 E))⁰} {δ : 𝓞 E}
    (h : (B : Ideal (𝓞 E)) * (B' : Ideal (𝓞 E)) = Ideal.span {δ}) : δ ≠ 0 := by
  rintro rfl
  rw [Set.singleton_zero, Ideal.span_zero, ← Ideal.zero_eq_bot] at h
  rcases mul_eq_zero.mp h with h0 | h0
  · exact nonZeroDivisors.coe_ne_zero B (by rw [h0, Ideal.zero_eq_bot])
  · exact nonZeroDivisors.coe_ne_zero B' (by rw [h0, Ideal.zero_eq_bot])

/-- **The kernel of $j$ is the group of strongly ambiguous classes** (Hilbert 90). -/
@[kb "hilbert1897" "Zahlbericht §§71–75 [unverified]; neukirch1999 Ch. IV §3 (Hilbert 90) [unverified]"]
theorem jHom_eq_one_iff (c : ClassGroup (𝓞 E)) : jHom F E c = 1 ↔ IsStrAmb F c := by
  constructor
  · intro h
    obtain ⟨A, rfl⟩ := ClassGroup.mk0_surjective c
    obtain ⟨A', γ, hA⟩ := exists_mul_eq_span A
    rw [jHom_mk0 hA, ← Con.coe_one] at h
    obtain ⟨α, β, hα, hβ, h1, h2⟩ := (Con.eq _).mp h
    rw [jPairOf_fst, show ((1 : NormPairs F E) : Ideal (𝓞 E) × 𝓞 F).1 = ⊤ from Ideal.one_eq_top,
      ← Ideal.one_eq_top, mul_one] at h1
    rw [jPairOf_snd, show ((1 : NormPairs F E) : Ideal (𝓞 E) × 𝓞 F).2 = 1 from rfl, coe_intNorm] at h2
    have hγ0 : γ ≠ 0 := gen_ne_zero hA
    have hσA : conjIdeal F (A : Ideal (𝓞 E)) * conjIdeal F (A' : Ideal (𝓞 E)) = Ideal.span {conjO F E γ} := by
      rw [← conjIdeal_mul, hA, conjIdeal_span]
    set x := α * conjO F E γ
    have hx0 : x ≠ 0 := mul_ne_zero hα (conjO_ne_zero hγ0)
    have hxA : Ideal.span {x} * (A : Ideal (𝓞 E)) = Ideal.span {β} * conjIdeal F (A : Ideal (𝓞 E)) := by
      rw [← Ideal.span_singleton_mul_span_singleton, ← hσA, ← h1]
      ring
    have hN : Algebra.intNorm (𝓞 F) (𝓞 E) x = Algebra.intNorm (𝓞 F) (𝓞 E) β := by
      apply FaithfulSMul.algebraMap_injective (𝓞 F) F
      have h2' : nrm (F := F) β = nrm (F := F) α * nrm (F := F) γ := by simpa using h2
      rw [algebraMap_intNorm', algebraMap_intNorm', nrm_mul, nrm_conjO]
      linear_combination -h2'
    obtain ⟨r, hr, hrx⟩ := exists_hilbert90 hx0 hN
    have hxr : x * conjO F E r ≠ 0 := mul_ne_zero hx0 (conjO_ne_zero hr)
    have hD0 : Ideal.span {x * conjO F E r} * (A : Ideal (𝓞 E)) ≠ ⊥ := by
      have h1 : Ideal.span {x * conjO F E r} ≠ 0 := by
        rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hxr
      have h2 : (A : Ideal (𝓞 E)) ≠ 0 := by rw [Ne, Ideal.zero_eq_bot]; exact nonZeroDivisors.coe_ne_zero A
      rw [← Ideal.zero_eq_bot]
      exact mul_ne_zero h1 h2
    refine ⟨⟨_, mem_nonZeroDivisors_of_ne_zero hD0⟩, ?_, ?_⟩
    · show conjIdeal F (Ideal.span {x * conjO F E r} * (A : Ideal (𝓞 E))) = Ideal.span {x * conjO F E r} * A
      rw [conjIdeal_span_mul, map_mul, conjO_conjO, mul_comm (conjO F E x)]
      calc Ideal.span {r * conjO F E x} * conjIdeal F (A : Ideal (𝓞 E))
          = Ideal.span {β * conjO F E r} * conjIdeal F (A : Ideal (𝓞 E)) := by rw [hrx]
        _ = Ideal.span {conjO F E r} * (Ideal.span {β} * conjIdeal F (A : Ideal (𝓞 E))) := by
          rw [← Ideal.span_singleton_mul_span_singleton]; ring
        _ = Ideal.span {conjO F E r} * (Ideal.span {x} * (A : Ideal (𝓞 E))) := by rw [hxA]
        _ = _ := by rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton, mul_comm (conjO F E r)]
    · exact mk0_span_mul hxr A _
  · rintro ⟨D, hσD, rfl⟩
    obtain ⟨D', δ, hD⟩ := exists_mul_eq_span D
    have hδ0 : δ ≠ 0 := gen_ne_zero hD
    rw [jHom_mk0 hD, ← Con.coe_one]
    refine pairClass_eq_of 1 (conjO F E δ) one_ne_zero (conjO_ne_zero hδ0) ?_ ?_
    · rw [jPairOf_fst, show ((1 : NormPairs F E) : Ideal (𝓞 E) × 𝓞 F).1 = ⊤ from Ideal.one_eq_top,
        Ideal.span_singleton_one, ← Ideal.one_eq_top, one_mul, mul_one, ← conjIdeal_span, ← hD, conjIdeal_mul, hσD]
    · rw [jPairOf_snd, show ((1 : NormPairs F E) : Ideal (𝓞 E) × 𝓞 F).2 = 1 from rfl, coe_intNorm, nrm_conjO]
      simp [nrm]

/-! ### Counting along a homomorphism -/

/-- $\#G = \#\mathrm{im}(f)\cdot\#\ker f$ for a homomorphism from a finite group to a monoid. -/
theorem card_range_mul_card_ker {G M : Type*} [Group G] [Finite G] [Monoid M] (f : G →* M) :
    Nat.card (Set.range f) * Nat.card {g : G // f g = 1} = Nat.card G := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hfib : ∀ y : Set.range f, Nat.card {g : G // f g = y} = Nat.card {g : G // f g = 1} := by
    rintro ⟨y, g₀, rfl⟩
    exact Nat.card_congr
      { toFun := fun g => ⟨g.1 * g₀⁻¹, by rw [map_mul, g.2, ← map_mul, mul_inv_cancel, map_one]⟩
        invFun := fun g => ⟨g.1 * g₀, by rw [map_mul, g.2, one_mul]⟩
        left_inv := fun g => Subtype.ext (by simp)
        right_inv := fun g => Subtype.ext (by simp) }
  let φ : G → Set.range f := fun g => ⟨f g, g, rfl⟩
  have e : G ≃ Σ y : Set.range f, {g : G // φ g = y} := (Equiv.sigmaFiberEquiv φ).symm
  have hfib' : ∀ y : Set.range f, Nat.card {g : G // φ g = y} = Nat.card {g : G // f g = 1} := fun y => by
    rw [← hfib y]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [φ, Subtype.ext_iff])
  have : Fintype (Set.range f) := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_sigma, Finset.sum_congr rfl (fun y _ => hfib' y), Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card (α := Set.range f)]

/-! ### The image of $j$: the positive principal genus (CM) -/

section CM

variable [IsTotallyReal F] [IsTotallyComplex E]

/-- **The image of $j$ is the principal genus of totally positive classes** (CM): a class of pairs is $j(c)$ for some
$c \in \mathrm{Cl}_E$ iff it is totally positive with trivial genus characters. (Hasse norm theorem: a scale with trivial
characters is a norm $N(\lambda)$; then `principal_identity`, an ideal Hilbert 90.) -/
@[kb "hecke1923" "§48 [unverified]; cf. principalGenus_iff"]
theorem mem_range_jHom_iff (g : PairClass F E) :
    g ∈ Set.range (jHom F E) ↔ IsPos E g ∧ genusHom E g = 1 := by
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨B, rfl⟩ := ClassGroup.mk0_surjective c
    obtain ⟨B', δ, hB⟩ := exists_mul_eq_span B
    have hδ0 := gen_ne_zero hB
    rw [jHom_mk0 hB]
    refine ⟨(isPos_mk _).mpr (fun w => ?_), ?_⟩
    · show 0 < Siegel.realEmb w (((jPairOf (F := F) B B' δ hB : NormPairs F E) : Ideal (𝓞 E) × 𝓞 F).2 : F)
      rw [jPairOf_snd, coe_intNorm]
      exact realEmb_norm_pos' (algebraMap_ne_zero hδ0) w
    · funext v
      rw [genusHom_mk, jPairOf_snd, coe_intNorm]
      exact genusSym_norm v _
  · rintro ⟨-, hgen⟩
    induction g using Con.induction_on with
    | H p =>
    set B := (p : Ideal (𝓞 E) × 𝓞 F).1
    set b := (p : Ideal (𝓞 E) × 𝓞 F).2
    have hb0 : (b : F) ≠ 0 := pair_snd_ne_zero' p
    have hb : ∀ v, genusSym E v (b : F) = genusSym E v 1 := fun v => by
      have := congrFun hgen v
      rw [genusHom_mk] at this
      rw [this, genusSym_one]; rfl
    obtain ⟨l, hl, hl'⟩ := (genusSym_eq_iff_exists_norm (E := E) hb0 one_ne_zero).mp hb
    rw [one_mul] at hl'
    obtain ⟨p', q', hq', rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) l
    have hq0 : q' ≠ 0 := nonZeroDivisors.ne_zero hq'
    have hp0 : p' ≠ 0 := by rintro rfl; simp at hl
    set μ : 𝓞 E := p' * conjO F E q'
    set m : 𝓞 F := Algebra.intNorm (𝓞 F) (𝓞 E) q'
    have hpq : (b : F) * nrm (F := F) q' = nrm (F := F) p' := by
      rw [← hl']
      change _ = Algebra.norm F (algebraMap (𝓞 E) E p')
      rw [nrm, ← map_mul, div_mul_cancel₀ _ (algebraMap_ne_zero hq0)]
    have hNμ : nrm (F := F) μ = ((m : F)) ^ 2 * (b : F) := by
      rw [nrm_mul, nrm_conjO, ← hpq, coe_intNorm]; ring
    have hμ : Algebra.intNorm (𝓞 F) (𝓞 E) μ = m ^ 2 * ((1 : (𝓞 F)ˣ) : 𝓞 F) * b := by
      apply FaithfulSMul.algebraMap_injective (𝓞 F) F
      rw [algebraMap_intNorm', hNμ, Units.val_one, mul_one, map_mul, map_pow]
    have hμ0 : μ ≠ 0 := mul_ne_zero hp0 (conjO_ne_zero hq0)
    have hm0 : algebraMap (𝓞 F) (𝓞 E) m ≠ 0 := by
      refine algebraMap_O_ne_zero ?_
      intro h0
      apply nrm_ne_zero (F := F) hq0
      rw [← coe_intNorm]
      change ((m : 𝓞 F) : F) = 0
      rw [h0]; rfl
    have hid := principal_identity (pair_relNorm p) 1 hμ
    set C : Ideal (𝓞 E) := Ideal.span {algebraMap (𝓞 F) (𝓞 E) m} * B + Ideal.span {μ}
    have hC0 : C ≠ ⊥ := by
      intro h0
      have : μ ∈ C := Ideal.mem_sup_right (Ideal.mem_span_singleton_self μ)
      rw [h0, Ideal.mem_bot] at this
      exact hμ0 this
    obtain ⟨C', γ, hC⟩ := exists_mul_eq_span (⟨C, mem_nonZeroDivisors_of_ne_zero hC0⟩ : (Ideal (𝓞 E))⁰)
    have hγ0 := gen_ne_zero hC
    refine ⟨ClassGroup.mk0 ⟨C, mem_nonZeroDivisors_of_ne_zero hC0⟩, ?_⟩
    rw [jHom_mk0 hC]
    symm
    refine pairClass_eq_of (algebraMap (𝓞 F) (𝓞 E) m * conjO F E γ) (conjO F E μ)
      (mul_ne_zero hm0 (conjO_ne_zero hγ0)) (conjO_ne_zero hμ0) ?_ ?_
    · rw [jPairOf_fst]
      change Ideal.span {algebraMap (𝓞 F) (𝓞 E) m * conjO F E γ} * B =
        Ideal.span {conjO F E μ} * (C * conjIdeal F (C' : Ideal (𝓞 E)))
      rw [← Ideal.span_singleton_mul_span_singleton, ← conjIdeal_span]
      rw [show Ideal.span {γ} = C * (C' : Ideal (𝓞 E)) from hC.symm, conjIdeal_mul]
      have hid' : Ideal.span {algebraMap (𝓞 F) (𝓞 E) m} * B * conjIdeal F C = Ideal.span {conjO F E μ} * C := hid
      calc Ideal.span {algebraMap (𝓞 F) (𝓞 E) m} * (conjIdeal F C * conjIdeal F (C' : Ideal (𝓞 E))) * B
          = (Ideal.span {algebraMap (𝓞 F) (𝓞 E) m} * B * conjIdeal F C) * conjIdeal F (C' : Ideal (𝓞 E)) := by ring
        _ = _ := by rw [hid']; ring
    · rw [jPairOf_snd, coe_intNorm, nrm_conjO, hNμ, nrm_mul, nrm_conjO, norm_algebraMap_O]
      ring

/-- **$\#P_0\cdot\#\mathrm{Cl}_E^{\mathrm{str}} = h_E$** (CM): the totally positive classes of the principal genus times the strongly
ambiguous classes is the class number of $E$ ($j$: image $P_0$, kernel $\mathrm{Cl}_E^{\mathrm{str}}$). -/
@[kb "hilbert1897" "Zahlbericht §§71–75 [unverified]; hecke1923 §48 [unverified]"]
theorem card_principalGenus_mul_card_strAmb :
    Nat.card {t : PairClass F E // IsPos E t ∧ genusHom E t = 1} * Nat.card (StrAmb F E) = classNumber E := by
  rw [classNumber, ← Nat.card_eq_fintype_card, ← card_range_mul_card_ker (jHom F E)]
  congr 1
  · exact Nat.card_congr (Equiv.subtypeEquivRight fun g => (mem_range_jHom_iff g).symm)
  · exact Nat.card_congr (Equiv.subtypeEquivRight fun c => (jHom_eq_one_iff c).symm)

end CM

/-! ### The relation for a CM field $K$, $F = K^+$ -/

section Siegel

variable (K : Type) [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

theorem conj_eq_complexConj : conj K⁺ K = IsCMField.complexConj K := by
  rcases eq_one_or_eq_conj (F := K⁺) (E := K) (IsCMField.complexConj K) with h | h
  · exact absurd h (IsCMField.complexConj_ne_one K)
  · exact h.symm

/-- Our $u \mapsto u/\sigma u$ is Mathlib's `IsCMField.unitsMulComplexConjInv`. -/
theorem unitsMulConjInv_eq : unitsMulConjInv K⁺ K = IsCMField.unitsMulComplexConjInv K := by
  ext u
  have h : conjUnits K⁺ K u = IsCMField.unitsComplexConj K u := by
    ext
    show ((conjO K⁺ K (u : 𝓞 K) : 𝓞 K) : K) = _
    rw [show ((conjO K⁺ K (u : 𝓞 K) : 𝓞 K) : K) = conj K⁺ K ((u : 𝓞 K) : K) from rfl, conj_eq_complexConj]
    rfl
  simp only [coe_unitsMulConjInv, IsCMField.unitsMulComplexConjInv_apply, h]

/-- **$Q_K\cdot[\mu_K : \{u/\bar u\}] = 2$** (Mathlib, `IsCMField.indexRealUnits_mul_eq`). -/
theorem indexRealUnits_mul_index_conjQuotGroup :
    IsCMField.indexRealUnits K * (conjQuotGroup K⁺ K).index = 2 := by
  rw [conjQuotGroup, unitsMulConjInv_eq]
  exact IsCMField.indexRealUnits_mul_eq K

/-- **`PosClassNumberRelation` is a theorem** ($K$ CM, $F = K^+$, $t$ ramified primes):
$\#G^+\cdot Q_K\,h_{K^+}\,2^t = 2\cdot 2^{t-1}\,h_K$. Proof without class field theory: $\#G^+ = 2^{t-1}\#P_0$ (genus theory),
$\#P_0\cdot\#\mathrm{Cl}^{\mathrm{str}}_K = h_K$ ($j$), $\#\mathrm{Cl}^{\mathrm{str}}_K\cdot[\mu_K : \{u/\bar u\}] = 2^t h_{K^+}$ (ambiguous ideals,
Hilbert 90), $Q_K\,[\mu_K : \{u/\bar u\}] = 2$ (Hasse's unit index, Mathlib). -/
@[kb "hilbert1897" "Zahlbericht §§71–75 [unverified]; chevalley1933 [unverified]; washington1997 Thm. 4.12 [unverified]"]
theorem posClassNumberRelation : PosClassNumberRelation K := by
  refine ⟨fun T hT => ?_⟩
  have h1 := card_posClasses_eq (F := K⁺) (E := K) hT
  have h2 := card_principalGenus_mul_card_strAmb (F := K⁺) (E := K)
  have h3 := card_strAmb_mul_index (F := K⁺) (E := K) hT
  have h4 := indexRealUnits_mul_index_conjQuotGroup K
  set G := Nat.card {g : PairClass K⁺ K // IsPos K g}
  set a := Nat.card {t : PairClass K⁺ K // IsPos K t ∧ genusHom K t = 1}
  set s := Nat.card (StrAmb K⁺ K)
  set i := (conjQuotGroup K⁺ K).index
  set Q := IsCMField.indexRealUnits K
  have key : G * Q * classNumber K⁺ * 2 ^ T.card = 2 * 2 ^ (T.card - 1) * classNumber K := by
    calc G * Q * classNumber K⁺ * 2 ^ T.card = 2 ^ (T.card - 1) * a * Q * (2 ^ T.card * classNumber K⁺) := by
          rw [h1]; ring
      _ = 2 ^ (T.card - 1) * (a * s) * (Q * i) := by rw [← h3]; ring
      _ = 2 * 2 ^ (T.card - 1) * classNumber K := by rw [h2, h4]; ring
  exact_mod_cast key

open Classical in
/-- **Siegel's formula for $n = 2$ over $F = K^+$, genus by genus — unconditional** ($K$ CM). `siegel_binaryF_genus` with its
input `PosClassNumberRelation K` discharged by `posClassNumberRelation`. For an $\mathcal O_{K^+}$-basis $b$ of $\mathcal O_K$, the genus
$\mathcal G$ of a totally positive class $g_0$ (vector $\varphi$), the ramified primes $T$, $\lambda = L(1,\chi_{K/K^+})$, and $\nu \gg 0$
divisible only by good primes of $Q_b$:
$$\frac{1}{\#\mathcal G}\sum_{(C,\eta) \in \mathcal G} r_{L_{C,\eta}}(\nu) = \tfrac12\,|d_{K^+}|^{-1/2}\beta_\infty(\nu)\lambda^{-1}
\prod_{\mathfrak p \in T}\bigl(1 + \psi_\mathfrak p(\nu)\varphi_\mathfrak p\bigr)\prod_{\mathfrak p \mid \nu}\frac{\beta_\mathfrak p(Q_b,\nu)}{1 - \chi(\mathfrak p)N\mathfrak p^{-1}}.$$ -/
@[kb "siegel1935" "Hauptsatz (n = 2) [unverified]; hanke2004 (5.3); shimura2010 §4 [unverified]"]
theorem siegel_binaryF_genus' (b : Basis (Fin 2) (𝓞 K⁺) (𝓞 K)) {lam : ℝ}
    (hlam : Tendsto (relLR K⁺ K) (𝓝[>] 1) (𝓝 lam))
    {T : Finset (HeightOneSpectrum (𝓞 K⁺))} (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar K 𝔭 = 0)
    {g₀ : PairClass K⁺ K} (hg₀ : IsPos K g₀)
    {ν : 𝓞 K⁺} (hν : ν ≠ 0) (hpos : ∀ w : Siegel.RealPlace K⁺, 0 < Siegel.realEmb w (ν : K⁺))
    (hgood : ∀ 𝔭 : HeightOneSpectrum (𝓞 K⁺), ν ∈ 𝔭.asIdeal → Siegel.IsGoodPrimeNF (normFormBasis b) 𝔭) :
    ((∑ x ∈ Finset.univ.filter
        (fun x : PNClass K⁺ K × unitQuot K⁺ K => ∀ v, genusSym K v (scaleOf x.1 x.2) = genusHom K g₀ v),
        repNumLat (scaleOf x.1 x.2 • normForm K⁺ K) (idealLat K⁺ (classRep K x.1.1 : Ideal (𝓞 K)))
          (algebraMap (𝓞 K⁺) K⁺ ν) : ℕ) : ℝ) /
      (Finset.univ.filter
        (fun x : PNClass K⁺ K × unitQuot K⁺ K => ∀ v, genusSym K v (scaleOf x.1 x.2) = genusHom K g₀ v)).card =
    (1 / 2 : ℝ) * |(discr K⁺ : ℝ)| ^ (-(1 / 2 : ℝ)) * Siegel.betaInfNF (normFormBasis b) (ν : K⁺) / lam *
      (∏ 𝔭 ∈ T, (1 + (genusSym K (NFPlace.finite 𝔭) (ν : K⁺) : ℝ) *
        (genusHom K g₀ (NFPlace.finite 𝔭) : ℝ))) *
      ∏ᶠ 𝔭 : HeightOneSpectrum (𝓞 K⁺),
        (if ν ∈ 𝔭.asIdeal then
          LocalDensity.NF.localDensity 𝔭 (normFormBasis b) ν / (1 - (relChar K 𝔭 : ℝ) / (Ideal.absNorm 𝔭.asIdeal : ℝ))
        else 1) :=
  siegel_binaryF_genus (posClassNumberRelation K) b hlam hT hg₀ hν hpos hgood

end Siegel

end QuadFormsKB.Binary.Rel
