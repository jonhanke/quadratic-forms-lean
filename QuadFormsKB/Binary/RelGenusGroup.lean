import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelGenusExact

/-!
# The composition group of normalized binary lattices over $F$; classes per genus

$E/F$ quadratic. A **normalized pair** is $(\mathfrak A, a)$ with $\mathfrak A \ne 0$ an ideal of $\mathcal O_E$ and $a \in \mathcal O_F$ with
$N_{E/F}\mathfrak A = (a)$; it stands for the binary $\mathcal O_F$-lattice $(\mathfrak A, a^{-1}N)$, whose norm ideal is $\mathcal O_F$ (the $(\mathfrak A_C, \frac{\eta}{a_C}N)$ is the pair $(\mathfrak A_C, \eta^{-1}a_C)$). Two pairs are **properly equivalent**,
$(\mathfrak A, a) \sim (\mathfrak B, b)$, iff $\mathfrak B = \lambda\mathfrak A$ and $b = N(\lambda)a$ for some $\lambda \in E^\times$, i.e. iff
$x \mapsto \lambda x$ is an isometry $(\mathfrak A, a^{-1}N) \to (\mathfrak B, b^{-1}N)$ (`isometricLattices_ideal_iff`, the proper half).
In integral form: $\alpha\mathfrak A = \beta\mathfrak B$ and $N(\beta)b = N(\alpha)a$ with $\alpha, \beta \in \mathcal O_E \setminus 0$.

* **`NormPairs`**, **`pairCon`**, **`PairClass`**: the pairs form a commutative monoid under $(\mathfrak A, a)(\mathfrak B, b) = (\mathfrak A\mathfrak B, ab)$ (composition),
  $\sim$ is a congruence, and the classes form a commutative monoid in which every element is invertible:
  $(\mathfrak A, a)^{-1} = (\sigma\mathfrak A, a)$ (`mul_inv_pair`, from $\mathfrak A\,\sigma\mathfrak A = a\mathcal O_E$). This is the group of proper classes of
  normalized lattices (over $\mathbb Q$: Gauss composition).
* **`genusHom`**: the genus vector $(\psi_v(a))_v$ is a well-defined homomorphism on classes.
* **`card_fiber_eq`** (*Gauss's theorem over $F$*): every genus of totally positive classes contains the same number of
  classes as the principal genus.
* **`card_posClasses_eq`** (CM): $\#\{\text{totally positive classes}\} = 2^{t-1}\cdot\#(\text{principal genus})$, $t$ = number of ramified primes
  (with `ncard_genera_eq`).
* **`principalGenus_image`** (CM): the ideal classes of the principal genus are exactly $\mathrm{Cl}_E^{1-\sigma} = \{c\,\sigma_*c^{-1}\}$
  (`principalGenus_iff`).

Counts are `Nat.card` (no finiteness needed for the identities: an infinite type has `Nat.card = 0`, and the identities hold
in that case too).

Sources: Gauss, *Disq.* Art. 252 (each genus has the same number of classes) [unverified]; Hecke §48 [unverified];
Shimura (2010) §4 [unverified].
-/

open NumberField Module IsDedekindDomain
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

variable (F E) in
/-- **Normalized pairs** $(\mathfrak A, a)$: $\mathfrak A \ne 0$ an ideal of $\mathcal O_E$, $a \in \mathcal O_F$, $N_{E/F}\mathfrak A = (a)$ — a submonoid of
$\mathrm{Ideals}(\mathcal O_E) \times \mathcal O_F$. -/
def NormPairs : Submonoid (Ideal (𝓞 E) × 𝓞 F) where
  carrier := {p | p.1 ≠ ⊥ ∧ Ideal.relNorm (𝓞 F) p.1 = Ideal.span {p.2}}
  mul_mem' := by
    rintro ⟨𝔄, a⟩ ⟨𝔅, b⟩ ⟨h𝔄, ha⟩ ⟨h𝔅, hb⟩
    refine ⟨?_, ?_⟩
    · exact fun h => (Ideal.mul_eq_bot.mp h).elim h𝔄 h𝔅
    · show Ideal.relNorm (𝓞 F) (𝔄 * 𝔅) = Ideal.span {a * b}
      rw [map_mul, ha, hb, Ideal.span_singleton_mul_span_singleton]
  one_mem' := by
    refine ⟨?_, ?_⟩
    · show (1 : Ideal (𝓞 E)) ≠ ⊥
      rw [Ideal.one_eq_top]; exact top_ne_bot
    · show Ideal.relNorm (𝓞 F) (1 : Ideal (𝓞 E)) = Ideal.span {1}
      rw [map_one, Ideal.span_singleton_one, Ideal.one_eq_top]

theorem pair_ne_bot (p : NormPairs F E) : (p : Ideal (𝓞 E) × 𝓞 F).1 ≠ ⊥ := p.2.1

theorem pair_relNorm (p : NormPairs F E) :
    Ideal.relNorm (𝓞 F) (p : Ideal (𝓞 E) × 𝓞 F).1 = Ideal.span {(p : Ideal (𝓞 E) × 𝓞 F).2} := p.2.2

theorem pair_snd_ne_zero (p : NormPairs F E) : (p : Ideal (𝓞 E) × 𝓞 F).2 ≠ 0 := by
  intro h
  have := (pair_relNorm p)
  rw [h, Set.singleton_zero, Ideal.span_zero, Ideal.relNorm_eq_bot_iff] at this
  exact (pair_ne_bot p) this

theorem pair_snd_ne_zero' (p : NormPairs F E) : ((p : Ideal (𝓞 E) × 𝓞 F).2 : F) ≠ 0 := by
  exact_mod_cast (pair_snd_ne_zero p)

variable (F E) in
/-- **Proper equivalence of pairs:** $(\mathfrak A, a) \sim (\mathfrak B, b)$ iff $\alpha\mathfrak A = \beta\mathfrak B$ and $N(\beta)\,b = N(\alpha)\,a$ for some
nonzero $\alpha, \beta \in \mathcal O_E$ (i.e. $\mathfrak B = \lambda\mathfrak A$, $b = N(\lambda)a$, $\lambda = \alpha/\beta$). -/
def PairRel (p q : NormPairs F E) : Prop :=
  ∃ α β : 𝓞 E, α ≠ 0 ∧ β ≠ 0 ∧
    Ideal.span {α} * (p : Ideal (𝓞 E) × 𝓞 F).1 = Ideal.span {β} * (q : Ideal (𝓞 E) × 𝓞 F).1 ∧
    nrm (F := F) β * ((q : Ideal (𝓞 E) × 𝓞 F).2 : F) = nrm (F := F) α * ((p : Ideal (𝓞 E) × 𝓞 F).2 : F)

variable (F E) in
/-- Proper equivalence is a congruence on the monoid of pairs. -/
def pairCon : Con (NormPairs F E) where
  r := PairRel F E
  iseqv := by
    refine ⟨fun p => ⟨1, 1, one_ne_zero, one_ne_zero, rfl, rfl⟩, ?_, ?_⟩
    · rintro p q ⟨α, β, hα, hβ, h1, h2⟩
      exact ⟨β, α, hβ, hα, h1.symm, h2.symm⟩
    · rintro p q r ⟨α, β, hα, hβ, h1, h2⟩ ⟨γ, δ, hγ, hδ, h3, h4⟩
      refine ⟨α * γ, β * δ, mul_ne_zero hα hγ, mul_ne_zero hβ hδ, ?_, ?_⟩
      · rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
          mul_comm (Ideal.span {α}), mul_assoc, h1, ← mul_assoc, mul_comm (Ideal.span {γ}), mul_assoc, h3,
          ← mul_assoc, mul_comm (Ideal.span {β})]
      · rw [nrm_mul, nrm_mul]
        linear_combination nrm (F := F) β * h4 + nrm (F := F) γ * h2
  mul' := by
    rintro p q r s ⟨α, β, hα, hβ, h1, h2⟩ ⟨γ, δ, hγ, hδ, h3, h4⟩
    refine ⟨α * γ, β * δ, mul_ne_zero hα hγ, mul_ne_zero hβ hδ, ?_, ?_⟩
    · show Ideal.span {α * γ} * ((p : Ideal (𝓞 E) × 𝓞 F).1 * (r : Ideal (𝓞 E) × 𝓞 F).1) =
        Ideal.span {β * δ} * ((q : Ideal (𝓞 E) × 𝓞 F).1 * (s : Ideal (𝓞 E) × 𝓞 F).1)
      rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton]
      calc Ideal.span {α} * Ideal.span {γ} * ((p : Ideal (𝓞 E) × 𝓞 F).1 * (r : Ideal (𝓞 E) × 𝓞 F).1)
          = (Ideal.span {α} * (p : Ideal (𝓞 E) × 𝓞 F).1) * (Ideal.span {γ} * (r : Ideal (𝓞 E) × 𝓞 F).1) := by ring
        _ = (Ideal.span {β} * (q : Ideal (𝓞 E) × 𝓞 F).1) * (Ideal.span {δ} * (s : Ideal (𝓞 E) × 𝓞 F).1) := by
          rw [h1, h3]
        _ = _ := by ring
    · show nrm (F := F) (β * δ) * (((q : Ideal (𝓞 E) × 𝓞 F).2 * (s : Ideal (𝓞 E) × 𝓞 F).2 : 𝓞 F) : F) =
        nrm (F := F) (α * γ) * (((p : Ideal (𝓞 E) × 𝓞 F).2 * (r : Ideal (𝓞 E) × 𝓞 F).2 : 𝓞 F) : F)
      rw [nrm_mul, nrm_mul]; push_cast
      linear_combination (nrm (F := F) δ * ((s : Ideal (𝓞 E) × 𝓞 F).2 : F)) * h2 +
        (nrm (F := F) α * ((p : Ideal (𝓞 E) × 𝓞 F).2 : F)) * h4

variable (F E) in
/-- **The proper classes of normalized lattices** (pairs modulo proper equivalence), a commutative monoid under composition. -/
abbrev PairClass := (pairCon F E).Quotient

/-! ### Inverses -/

/-- The conjugate pair $(\sigma\mathfrak A, a)$. -/
def conjPair (p : NormPairs F E) : NormPairs F E :=
  ⟨(conjIdeal F (p : Ideal (𝓞 E) × 𝓞 F).1, (p : Ideal (𝓞 E) × 𝓞 F).2),
    conjIdeal_ne_bot (pair_ne_bot p), (relNorm_conjIdeal _).trans (pair_relNorm p)⟩

theorem norm_algebraMap_O (a : 𝓞 F) : nrm (F := F) (algebraMap (𝓞 F) (𝓞 E) a) = (a : F) ^ 2 := by
  rw [nrm, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E,
    Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two]

/-- **$(\mathfrak A, a)\,(\sigma\mathfrak A, a) \sim (\mathcal O_E, 1)$:** $\mathfrak A\,\sigma\mathfrak A = a\mathcal O_E$ (`mul_conjIdeal`) and $N(a) = a^2$. -/
theorem mul_inv_pair (p : NormPairs F E) : pairCon F E (p * conjPair p) 1 := by
  refine ⟨1, algebraMap (𝓞 F) (𝓞 E) (p : Ideal (𝓞 E) × 𝓞 F).2, one_ne_zero, ?_, ?_, ?_⟩
  · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).mpr (pair_snd_ne_zero p)
  · show Ideal.span {1} * ((p : Ideal (𝓞 E) × 𝓞 F).1 * conjIdeal F (p : Ideal (𝓞 E) × 𝓞 F).1) =
      Ideal.span {algebraMap (𝓞 F) (𝓞 E) (p : Ideal (𝓞 E) × 𝓞 F).2} * 1
    rw [Ideal.span_singleton_one, ← Ideal.one_eq_top, one_mul, mul_one, mul_conjIdeal, (pair_relNorm p), Ideal.map_span,
      Set.image_singleton]
  · show nrm (F := F) (algebraMap (𝓞 F) (𝓞 E) (p : Ideal (𝓞 E) × 𝓞 F).2) * ((1 : 𝓞 F) : F) =
      nrm (F := F) 1 * (((p : Ideal (𝓞 E) × 𝓞 F).2 * (p : Ideal (𝓞 E) × 𝓞 F).2 : 𝓞 F) : F)
    rw [norm_algebraMap_O]; simp [nrm]; ring

/-- **Every class is invertible.** -/
theorem exists_mul_eq_one (g : PairClass F E) : ∃ g' : PairClass F E, g * g' = 1 := by
  induction g using Con.induction_on with
  | H p => exact ⟨(conjPair p : NormPairs F E), (Con.eq _).mpr (mul_inv_pair p)⟩

/-! ### The classes are the pairs $(C, \eta)$ -/

/-- **Twisting by a norm of a unit does not change the class:** $(\mathfrak A, b) \sim (\mathfrak A, b\,N(v))$, $v \in \mathcal O_E^\times$. -/
theorem pairCon_mul_normUnit {p q : NormPairs F E}
    (h1 : (p : Ideal (𝓞 E) × 𝓞 F).1 = (q : Ideal (𝓞 E) × 𝓞 F).1) (v : (𝓞 E)ˣ)
    (h2 : (q : Ideal (𝓞 E) × 𝓞 F).2 =
      (p : Ideal (𝓞 E) × 𝓞 F).2 * ((Units.map (Algebra.intNorm (𝓞 F) (𝓞 E)) v : (𝓞 F)ˣ) : 𝓞 F)) :
    pairCon F E p q := by
  refine ⟨v, 1, v.ne_zero, one_ne_zero, ?_, ?_⟩
  · rw [Ideal.span_singleton_eq_top.mpr v.isUnit, Ideal.span_singleton_one, h1]
  · rw [h2]
    have e : ((((p : Ideal (𝓞 E) × 𝓞 F).2 * ((Units.map (Algebra.intNorm (𝓞 F) (𝓞 E)) v : (𝓞 F)ˣ) : 𝓞 F)) :
        𝓞 F) : F) = ((p : Ideal (𝓞 E) × 𝓞 F).2 : F) * nrm (F := F) (v : 𝓞 E) := by
      rw [← algebraMap_normUnit]; push_cast; rfl
    rw [e]; simp [nrm]; ring

/-- The normalized lattice $(\mathfrak A_C, \frac{\eta}{a_C}N)$ as a pair $(\mathfrak A_C, \eta^{-1}a_C)$ ($\eta$ = `η.out`). -/
def pairOf (C : PNClass F E) (η : unitQuot F E) : NormPairs F E :=
  ⟨(classRep E C.1, ((η.out⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * normGen C), classRep_ne_bot _, by
    show Ideal.relNorm (𝓞 F) (classRep E C.1 : Ideal (𝓞 E)) = Ideal.span {((η.out⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * normGen C}
    rw [Ideal.span_singleton_mul_left_unit (Units.isUnit _), span_normGen]⟩

variable (F E) in
/-- **The parametrization of the classes:** $(C, \eta) \mapsto [(\mathfrak A_C, \eta^{-1}a_C)]$. -/
def classOf (x : PNClass F E × unitQuot F E) : PairClass F E := (pairOf x.1 x.2 : PairClass F E)

/-- **`classOf` is a bijection** $\{C \in \mathrm{Cl}_E : N\mathfrak A_C \text{ principal}\} \times \mathcal O_F^\times/N(\mathcal O_E^\times) \to$ classes of pairs
(so the proper classes of normalized lattices are exactly the $(C, \eta)$, and there are finitely many). -/
@[kb "shimura2010" "§4 [unverified]"]
theorem classOf_bijective : Function.Bijective (classOf F E) := by
  constructor
  · rintro ⟨⟨C, hC⟩, η⟩ ⟨⟨C', hC'⟩, η'⟩ h
    obtain ⟨α, β, hα, hβ, h1, h2⟩ := (Con.eq _).mp h
    have hCC : C = C' := by
      rw [← mk0_classRep C, ← mk0_classRep C']
      exact ClassGroup.mk0_eq_mk0_iff.mpr ⟨α, β, hα, hβ, h1⟩
    subst hCC
    have h1' : Ideal.span {α} = Ideal.span {β} :=
      mul_right_cancel₀ (classRep_ne_bot C) h1
    obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp h1'
    refine Prod.ext rfl ?_
    show η = η'
    rw [← QuotientGroup.out_eq' η, ← QuotientGroup.out_eq' η', QuotientGroup.eq]
    refine ⟨v, Units.ext (FaithfulSMul.algebraMap_injective (𝓞 F) F ?_)⟩
    rw [algebraMap_normUnit, Units.val_mul, map_mul, algebraMap_inv_unit]
    have h2' : nrm (F := F) β * (algebraMap (𝓞 F) F ((η'.out⁻¹ : (𝓞 F)ˣ) : 𝓞 F) *
        algebraMap (𝓞 F) F (normGen (⟨C, hC'⟩ : PNClass F E))) =
        nrm (F := F) α * (algebraMap (𝓞 F) F ((η.out⁻¹ : (𝓞 F)ˣ) : 𝓞 F) *
        algebraMap (𝓞 F) F (normGen (⟨C, hC⟩ : PNClass F E))) := by
      have := h2
      simp only [pairOf] at this
      rw [← map_mul, ← map_mul]; exact this
    rw [← hv, nrm_mul, algebraMap_inv_unit, algebraMap_inv_unit] at h2'
    have hn : normGen (⟨C, hC'⟩ : PNClass F E) = normGen (⟨C, hC⟩ : PNClass F E) := rfl
    rw [hn] at h2'
    have ha := algebraMap_normGen_ne_zero (⟨C, hC⟩ : PNClass F E)
    have hu := algebraMap_unit_ne_zero (η.out : (𝓞 F)ˣ)
    have hu' := algebraMap_unit_ne_zero (η'.out : (𝓞 F)ˣ)
    have hnα := nrm_ne_zero (F := F) hα
    field_simp at h2'
    rw [← h2']
    field_simp
  · intro g
    induction g using Con.induction_on with
    | H p =>
    obtain ⟨⟨𝔅, b⟩, h𝔅, hb⟩ := p
    have hB : 𝔅 ∈ (Ideal (𝓞 E))⁰ := mem_nonZeroDivisors_of_ne_zero h𝔅
    set C₀ := ClassGroup.mk0 (⟨𝔅, hB⟩ : (Ideal (𝓞 E))⁰)
    obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp (mk0_classRep C₀)
    have hrel := congrArg (Ideal.relNorm (𝓞 F)) hxy
    simp only [map_mul, Ideal.relNorm_singleton] at hrel
    rw [show Ideal.relNorm (𝓞 F) (((⟨𝔅, hB⟩ : (Ideal (𝓞 E))⁰) : Ideal (𝓞 E))) = Ideal.span {b} from hb,
      Ideal.span_singleton_mul_span_singleton] at hrel
    have hmem : Algebra.intNorm (𝓞 F) (𝓞 E) y * b ∈ Ideal.span {Algebra.intNorm (𝓞 F) (𝓞 E) x} := by
      have : Algebra.intNorm (𝓞 F) (𝓞 E) y * b ∈ Ideal.span {Algebra.intNorm (𝓞 F) (𝓞 E) x} *
          Ideal.relNorm (𝓞 F) (classRep E C₀ : Ideal (𝓞 E)) := by
        rw [hrel]; exact Ideal.mem_span_singleton_self _
      exact (Ideal.mul_le_left (I := Ideal.span {Algebra.intNorm (𝓞 F) (𝓞 E) x})
        (J := Ideal.relNorm (𝓞 F) (classRep E C₀ : Ideal (𝓞 E)))) this
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hmem
    have hNx : Algebra.intNorm (𝓞 F) (𝓞 E) x ≠ 0 := by rw [Ne, Algebra.intNorm_eq_zero]; exact hx
    have hprin : Ideal.relNorm (𝓞 F) (classRep E C₀ : Ideal (𝓞 E)) = Ideal.span {s} := by
      have hx0 : Ideal.span {Algebra.intNorm (𝓞 F) (𝓞 E) x} ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]; exact hNx
      refine mul_left_cancel₀ hx0 ?_
      rw [hrel, ← hs, mul_comm s, Ideal.span_singleton_mul_span_singleton]
    let C : PNClass F E := ⟨C₀, ⟨s, hprin⟩⟩
    obtain ⟨ε, hε⟩ := Ideal.span_singleton_eq_span_singleton.mp ((span_normGen C).trans hprin)
    set η : unitQuot F E := QuotientGroup.mk ε⁻¹
    have hmemN : (ε⁻¹)⁻¹ * η.out ∈ normUnits F E := QuotientGroup.eq.mp (QuotientGroup.out_eq' η).symm
    obtain ⟨v, hv⟩ := hmemN
    refine ⟨(C, η), ?_⟩
    have hq : ((classRep E C₀ : Ideal (𝓞 E)), s) ∈ NormPairs F E := ⟨classRep_ne_bot _, hprin⟩
    -- pairOf C η ~ (𝔄_C, s) ~ (𝔅, b)
    have e1 : pairCon F E (pairOf C η) ⟨_, hq⟩ := by
      refine pairCon_mul_normUnit rfl v ?_
      show s = ((η.out⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * normGen C * _
      rw [hv, ← hε, inv_inv]
      have : ((η.out⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((ε * η.out : (𝓞 F)ˣ) : 𝓞 F) = (ε : 𝓞 F) := by
        rw [← Units.val_mul, mul_comm ε, ← mul_assoc, inv_mul_cancel, one_mul]
      linear_combination (-(normGen C)) * this
    have e2 : pairCon F E ⟨_, hq⟩ ⟨(𝔅, b), h𝔅, hb⟩ := by
      refine ⟨x, y, hx, hy, hxy, ?_⟩
      show nrm (F := F) y * (b : F) = nrm (F := F) x * (s : F)
      rw [← algebraMap_intNorm', ← algebraMap_intNorm']
      have h' : Algebra.intNorm (𝓞 F) (𝓞 E) y * b = Algebra.intNorm (𝓞 F) (𝓞 E) x * s := by
        rw [← hs]; ring
      have := congrArg (algebraMap (𝓞 F) F) h'
      rwa [map_mul, map_mul] at this
    exact (Con.eq _).mpr ((pairCon F E).trans e1 e2)

/-- The classes are finite in number. -/
instance finite_pairClass : Finite (PairClass F E) :=
  Finite.of_surjective _ (classOf_bijective (F := F) (E := E)).2

/-! ### The genus homomorphism -/

theorem genusSym_pair_eq (v : NFPlace F) {p q : NormPairs F E} (h : pairCon F E p q) :
    genusSym E v ((p : Ideal (𝓞 E) × 𝓞 F).2 : F) = genusSym E v ((q : Ideal (𝓞 E) × 𝓞 F).2 : F) := by
  obtain ⟨α, β, hα, hβ, -, h2⟩ := h
  have e1 := genusSym_mul_norm (E := E) v (pair_snd_ne_zero' q) (algebraMap_ne_zero hβ)
  have e2 := genusSym_mul_norm (E := E) v (pair_snd_ne_zero' p) (algebraMap_ne_zero hα)
  calc genusSym E v ((p : Ideal (𝓞 E) × 𝓞 F).2 : F)
      = genusSym E v (((p : Ideal (𝓞 E) × 𝓞 F).2 : F) * nrm (F := F) α) := e2.symm
    _ = genusSym E v (((q : Ideal (𝓞 E) × 𝓞 F).2 : F) * nrm (F := F) β) := by
        congr 1; rw [mul_comm, ← h2, mul_comm]
    _ = _ := e1

variable (E) in
/-- **The genus homomorphism** $[(\mathfrak A, a)] \mapsto (\psi_v(a))_v$ (well defined: $\psi_v(N(\lambda)a) = \psi_v(a)$; multiplicative:
$\psi_v(ab) = \psi_v(a)\psi_v(b)$). By `isometryEquiv_iff_genusSym` it is the rational genus of the lattice $(\mathfrak A, a^{-1}N)$. -/
@[kb "hecke1923" "§48 [unverified]; cf. genusChar"]
def genusHom : PairClass F E →* (NFPlace F → ℤ) where
  toFun := (pairCon F E).lift
    { toFun := fun p v => genusSym E v ((p : Ideal (𝓞 E) × 𝓞 F).2 : F)
      map_one' := by funext v; exact genusSym_one v
      map_mul' := fun p q => by
        funext v
        show genusSym E v ((((p * q : NormPairs F E) : Ideal (𝓞 E) × 𝓞 F).2 : 𝓞 F) : F) = _
        rw [show (((p * q : NormPairs F E) : Ideal (𝓞 E) × 𝓞 F).2 : F) =
          ((p : Ideal (𝓞 E) × 𝓞 F).2 : F) * ((q : Ideal (𝓞 E) × 𝓞 F).2 : F) by push_cast; rfl]
        exact genusSym_mul v (pair_snd_ne_zero' p) (pair_snd_ne_zero' q) }
    (fun p q h => by funext v; exact genusSym_pair_eq v h)
  map_one' := by rw [← Con.coe_one]; exact map_one _
  map_mul' := fun x y => map_mul _ x y

theorem genusHom_mk (p : NormPairs F E) (v : NFPlace F) :
    genusHom E (p : PairClass F E) v = genusSym E v ((p : Ideal (𝓞 E) × 𝓞 F).2 : F) := rfl

/-! ### Gauss: all genera have the same number of classes -/

/-- **Translation by a class is a bijection between fibres** of a homomorphism on a monoid whose elements are invertible,
restricted to a subset $P$ closed under multiplication and under the chosen inverses. -/
theorem card_fiber_eq_of_mul {G X : Type*} [CommMonoid G] [CommMonoid X] (γ : G →* X) (P : G → Prop)
    (hP : ∀ g h, P g → P h → P (g * h)) {g₀ g₀' : G} (h₀ : P g₀) (h₀' : P g₀') (hinv : g₀ * g₀' = 1) :
    Nat.card {t : G // P t ∧ γ t = γ g₀} = Nat.card {t : G // P t ∧ γ t = 1} := by
  refine Nat.card_congr
    { toFun := fun t => ⟨t.1 * g₀', hP _ _ t.2.1 h₀', by rw [map_mul, t.2.2, ← map_mul, hinv, map_one]⟩
      invFun := fun t => ⟨t.1 * g₀, hP _ _ t.2.1 h₀, by rw [map_mul, t.2.2, one_mul]⟩
      left_inv := fun t => Subtype.ext (by simp only; rw [mul_assoc, mul_comm g₀', hinv, mul_one])
      right_inv := fun t => Subtype.ext (by simp only; rw [mul_assoc, hinv, mul_one]) }

/-- **Positivity of a class** (CM, well defined since $N(\lambda) \gg 0$): $a \gg 0$, i.e. the lattice $(\mathfrak A, a^{-1}N)$ is totally positive
definite. Defined on pairs. -/
def IsPosPair (p : NormPairs F E) : Prop :=
  ∀ w : Siegel.RealPlace F, 0 < Siegel.realEmb w ((p : Ideal (𝓞 E) × 𝓞 F).2 : F)

section CM

variable [IsTotallyReal F] [IsTotallyComplex E]

theorem isPosPair_iff_of_rel {p q : NormPairs F E} (h : pairCon F E p q) : IsPosPair p ↔ IsPosPair q := by
  obtain ⟨α, β, hα, hβ, -, h2⟩ := h
  have hpos : ∀ x : 𝓞 E, x ≠ 0 → ∀ w, 0 < Siegel.realEmb w (nrm (F := F) x) :=
    fun x hx w => realEmb_norm_pos' (algebraMap_ne_zero hx) w
  have key : ∀ w, Siegel.realEmb w (nrm (F := F) β) * Siegel.realEmb w ((q : Ideal (𝓞 E) × 𝓞 F).2 : F) =
      Siegel.realEmb w (nrm (F := F) α) * Siegel.realEmb w ((p : Ideal (𝓞 E) × 𝓞 F).2 : F) := fun w => by
    rw [← map_mul, ← map_mul, h2]
  constructor
  · intro hp w
    have := key w
    have h1 := hpos β hβ w
    have h3 := mul_pos (hpos α hα w) (hp w)
    rw [← this] at h3
    exact pos_of_mul_pos_right h3 h1.le
  · intro hq w
    have := key w
    have h1 := hpos α hα w
    have h3 := mul_pos (hpos β hβ w) (hq w)
    rw [this] at h3
    exact pos_of_mul_pos_right h3 h1.le

variable (E) in
/-- Positivity on classes. -/
def IsPos (g : PairClass F E) : Prop :=
  Quotient.liftOn' g IsPosPair (fun _ _ h => propext (isPosPair_iff_of_rel h))

theorem isPos_mk (p : NormPairs F E) : IsPos E (p : PairClass F E) ↔ IsPosPair p := Iff.rfl

theorem isPos_mul {g h : PairClass F E} (hg : IsPos E g) (hh : IsPos E h) : IsPos E (g * h) := by
  induction g using Con.induction_on with
  | H p =>
  induction h using Con.induction_on with
  | H q =>
  intro w
  show 0 < Siegel.realEmb w ((((p * q : NormPairs F E) : Ideal (𝓞 E) × 𝓞 F).2 : 𝓞 F) : F)
  rw [show (((p * q : NormPairs F E) : Ideal (𝓞 E) × 𝓞 F).2 : F) =
    ((p : Ideal (𝓞 E) × 𝓞 F).2 : F) * ((q : Ideal (𝓞 E) × 𝓞 F).2 : F) by push_cast; rfl, map_mul]
  exact mul_pos (hg w) (hh w)

theorem exists_pos_inv {g : PairClass F E} (hg : IsPos E g) : ∃ g', IsPos E g' ∧ g * g' = 1 := by
  induction g using Con.induction_on with
  | H p => exact ⟨(conjPair p : NormPairs F E), hg, (Con.eq _).mpr (mul_inv_pair p)⟩

/-- **Gauss's theorem over $F$: each genus contains the same number of classes.** For every totally positive class $g$, the
totally positive classes in the genus of $g$ are as many as those in the principal genus (`Nat.card`). -/
@[kb "gauss1801" "Art. 252 [unverified]; hecke1923 §48 [unverified]"]
theorem card_fiber_eq {g : PairClass F E} (hg : IsPos E g) :
    Nat.card {t : PairClass F E // IsPos E t ∧ genusHom E t = genusHom E g} =
      Nat.card {t : PairClass F E // IsPos E t ∧ genusHom E t = 1} := by
  obtain ⟨g', hg', hinv⟩ := exists_pos_inv hg
  exact card_fiber_eq_of_mul (genusHom E) (IsPos E) (fun _ _ => isPos_mul) hg hg' hinv

/-- **The genus vectors of positive classes are those of the positive normalized values** (`posNormValues`). -/
theorem image_genusHom_eq :
    {φ | ∃ g : PairClass F E, IsPos E g ∧ genusHom E g = φ} =
      (fun (x : F) v => genusSym E v x) '' posNormValues E := by
  ext φ
  constructor
  · rintro ⟨g, hg, rfl⟩
    induction g using Con.induction_on with
    | H p =>
    refine ⟨((p : Ideal (𝓞 E) × 𝓞 F).2 : F), ⟨(p : Ideal (𝓞 E) × 𝓞 F).1, (p : Ideal (𝓞 E) × 𝓞 F).2, 1,
      (pair_ne_bot p), (pair_relNorm p), by simp, hg⟩, ?_⟩
    funext v; rfl
  · rintro ⟨x, ⟨𝔄, a, η, h𝔄, ha, rfl, hpos⟩, rfl⟩
    have hp : ((𝔄, (η : 𝓞 F) * a) : Ideal (𝓞 E) × 𝓞 F) ∈ NormPairs F E := by
      refine ⟨h𝔄, ?_⟩
      show Ideal.relNorm (𝓞 F) 𝔄 = Ideal.span {(η : 𝓞 F) * a}
      rw [ha, Ideal.span_singleton_mul_left_unit η.isUnit]
    refine ⟨((⟨_, hp⟩ : NormPairs F E) : PairClass F E), fun w => ?_, ?_⟩
    · show 0 < Siegel.realEmb w ((((η : 𝓞 F) * a : 𝓞 F)) : F)
      push_cast; exact hpos w
    · funext v
      show genusSym E v ((((η : 𝓞 F) * a : 𝓞 F)) : F) = _
      push_cast; rfl

/-- **Number of positive classes = (number of genera) × (classes in the principal genus):**
$\#\{g \gg 0\} = 2^{t-1}\cdot\#\{g \gg 0 : g \text{ in the principal genus}\}$, $t$ = number of ramified primes (CM). -/
@[kb "gauss1801" "Art. 252 [unverified]; hecke1923 §48 [unverified]"]
theorem card_posClasses_eq {T : Finset (HeightOneSpectrum (𝓞 F))} (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) :
    Nat.card {g : PairClass F E // IsPos E g} =
      2 ^ (T.card - 1) * Nat.card {t : PairClass F E // IsPos E t ∧ genusHom E t = 1} := by
  classical
  set Y := {φ | ∃ g : PairClass F E, IsPos E g ∧ genusHom E g = φ}
  have hY : Y.ncard = 2 ^ (T.card - 1) := by
    rw [show Y = _ from image_genusHom_eq]; exact ncard_genera_eq hT
  have hYfin : Y.Finite := Set.finite_of_ncard_pos (by rw [hY]; positivity)
  set K := {t : PairClass F E // IsPos E t ∧ genusHom E t = 1}
  -- the positive classes are the disjoint union of the fibres over Y
  let f : {g : PairClass F E // IsPos E g} → Y := fun g => ⟨genusHom E g.1, g.1, g.2, rfl⟩
  have efib : ∀ φ : Y, {x : {g : PairClass F E // IsPos E g} // f x = φ} ≃
      {t : PairClass F E // IsPos E t ∧ genusHom E t = φ} := fun φ =>
    { toFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
      invFun := fun t => ⟨⟨t.1, t.2.1⟩, Subtype.ext t.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun t => rfl }
  let e : {g : PairClass F E // IsPos E g} ≃ Σ φ : Y, {t : PairClass F E // IsPos E t ∧ genusHom E t = φ} :=
    (Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight efib)
  have hfib : ∀ φ : Y, Nat.card {t : PairClass F E // IsPos E t ∧ genusHom E t = φ} = Nat.card K := by
    rintro ⟨φ, g, hg, rfl⟩
    exact card_fiber_eq hg
  have : Finite Y := hYfin.to_subtype
  have : Fintype Y := Fintype.ofFinite Y
  by_cases hK : Finite K
  · have hfin : ∀ φ : Y, Finite {t : PairClass F E // IsPos E t ∧ genusHom E t = φ} := by
      rintro ⟨φ, g, hg, rfl⟩
      obtain ⟨g', hg', hinv⟩ := exists_pos_inv hg
      exact Finite.of_injective (β := K)
        (fun t => ⟨t.1 * g', isPos_mul t.2.1 hg', by rw [map_mul, t.2.2, ← map_mul, hinv, map_one]⟩)
        (fun a b h => Subtype.ext (by
          have := congrArg (fun x : K => x.1 * g) h
          simp only at this
          rwa [mul_assoc, mul_assoc, mul_comm g', hinv, mul_one, mul_one] at this))
    rw [Nat.card_congr e, Nat.card_sigma, Finset.sum_congr rfl (fun φ _ => hfib φ), Finset.sum_const,
      Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hY]
  · have hK0 : Nat.card K = 0 := by
      have : Infinite K := not_finite_iff_infinite.mp hK
      exact Nat.card_eq_zero_of_infinite
    rw [hK0, mul_zero]
    have : Infinite {g : PairClass F E // IsPos E g} := by
      rw [← not_finite_iff_infinite]
      intro hfin
      apply hK
      exact Finite.of_injective (fun t : K => (⟨t.1, t.2.1⟩ : {g : PairClass F E // IsPos E g}))
        (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
    exact Nat.card_eq_zero_of_infinite

/-- **The ideal classes of the principal genus** (CM): for $\mathfrak A \ne 0$ with $N\mathfrak A = (a)$, $[\mathfrak A] \in \mathrm{Cl}_E^{1-\sigma}$ iff some
totally positive pair $(\mathfrak A, b)$ lies in the principal genus (`principalGenus_iff`; positivity is automatic, the
characters at the infinite places being trivial). -/
@[kb "hecke1923" "§48 [unverified]; cf. principalGenus_eq_sq"]
theorem principalGenus_classes_iff (𝔄 : (Ideal (𝓞 E))⁰) {a : 𝓞 F}
    (h𝔄 : Ideal.relNorm (𝓞 F) (𝔄 : Ideal (𝓞 E)) = Ideal.span {a}) :
    (∃ c : ClassGroup (𝓞 E), ClassGroup.mk0 𝔄 = c * (conjClass F E c)⁻¹) ↔
      ∃ p : NormPairs F E, (p : Ideal (𝓞 E) × 𝓞 F).1 = 𝔄 ∧ IsPos E (p : PairClass F E) ∧
        genusHom E (p : PairClass F E) = 1 := by
  rw [principalGenus_iff 𝔄 h𝔄]
  constructor
  · rintro ⟨η, hη⟩
    have hp : (((𝔄 : Ideal (𝓞 E)), (η : 𝓞 F) * a) : Ideal (𝓞 E) × 𝓞 F) ∈ NormPairs F E := by
      refine ⟨nonZeroDivisors.coe_ne_zero 𝔄, ?_⟩
      show Ideal.relNorm (𝓞 F) (𝔄 : Ideal (𝓞 E)) = Ideal.span {(η : 𝓞 F) * a}
      rw [h𝔄, Ideal.span_singleton_mul_left_unit η.isUnit]
    have hcast : ((((η : 𝓞 F) * a : 𝓞 F)) : F) = ((η : 𝓞 F) : F) * (a : F) := by push_cast; rfl
    refine ⟨⟨_, hp⟩, rfl, fun w => ?_, ?_⟩
    · have hx : ((η : 𝓞 F) : F) * (a : F) ≠ 0 := by
        rw [← hcast]; exact pair_snd_ne_zero' (⟨_, hp⟩ : NormPairs F E)
      show 0 < Siegel.realEmb w ((((η : 𝓞 F) * a : 𝓞 F)) : F)
      rw [hcast]
      exact (genusSym_infinite_iff w hx).mp (hη _)
    · funext v
      rw [genusHom_mk]
      show genusSym E v ((((η : 𝓞 F) * a : 𝓞 F)) : F) = 1
      rw [hcast]; exact hη v
  · rintro ⟨p, hp1, -, hg⟩
    have hb := pair_relNorm p
    rw [hp1, h𝔄, Ideal.span_singleton_eq_span_singleton] at hb
    obtain ⟨u, hu⟩ := hb
    refine ⟨u, fun v => ?_⟩
    have := congrFun hg v
    rw [genusHom_mk, ← hu] at this
    rw [mul_comm]
    have hc : ((a * (u : 𝓞 F) : 𝓞 F) : F) = (a : F) * ((u : 𝓞 F) : F) := by push_cast; rfl
    rw [← hc]; exact this

end CM

end QuadFormsKB.Binary.Rel
