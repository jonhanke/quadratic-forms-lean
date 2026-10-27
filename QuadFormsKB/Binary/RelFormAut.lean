import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelFormsIdeals

/-!
# Automorphisms of the binary lattices $(\mathfrak A, cN)$ over $\mathcal O_F$

Let $E/F$ be a quadratic extension of number fields, $\sigma$ its nontrivial automorphism, $N = N_{E/F}$, and
$L \subseteq E$ an $\mathcal O_F$-lattice with the form $cN$, $c \in F^\times$. By `linear_isometry` every isometry of $(E, cN)$ is
$x \mapsto ux$ ("proper") or $x \mapsto u\,\sigma(x)$ ("improper") with $N(u) = 1$, so (`autEquiv`)
$$O(L) \;\simeq\; \{u : N(u) = 1,\ uL = L\} \;\sqcup\; \{u : N(u) = 1,\ u\,\sigma(L) = L\}.$$
For an ideal lattice $L = \mathfrak A \ne 0$:
* **proper automorphisms** (`properAutEquiv`): $\{u \in E : N(u) = 1,\ u\mathfrak A = \mathfrak A\} \simeq \{u \in \mathcal O_E^\times : N(u) = 1\}$;
* **improper automorphisms** exist iff $u\,\sigma(\mathfrak A) = \mathfrak A$ for some $u$ with $N(u) = 1$, and then they form a torsor under
  the proper ones; such an $\mathfrak A$ is **ambiguous**: $\sigma_*[\mathfrak A] = [\mathfrak A]$ (`conjClass_eq_of_improper`), hence
  $[\mathfrak A]^2 = 1$ in $\mathrm{Cl}_E/\iota(\mathrm{Cl}_F)$;
* **`card_autLat_ideal`:** $|O(\mathfrak A, cN)| = w_1\cdot(2$ if $\mathfrak A$ has an improper automorphism, else $1)$, with
  $w_1 = \#\{u \in \mathcal O_E^\times : N(u) = 1\}$.

**CM case** ($F$ totally real, $E$ totally complex; `normOneUnits_eq_torsion`, `card_normOneUnits`): a unit has $N_{E/F}(u) = 1$ iff
it is a root of unity, so $w_1 = w_E = |\mu_E|$ (Mathlib's `torsionOrder E`). The key input is that $\sigma$ is complex
conjugation under every complex embedding of $E$ (`isConj_conj`, from Mathlib's `exists_isConj_of_isRamified`: every
infinite place of $E$ is ramified over $F$). So $|SO(\mathfrak A, cN)| = w_E$ and $|O(\mathfrak A, cN)| \in \{w_E, 2w_E\}$, exactly as
over $\mathbb Q$ (`card_autSL`, `card_aut`). This is the relation of the automorphisms to $\mu_E$; Hasse's
unit index $Q_E = [\mathcal O_E^\times : \mu_E\mathcal O_F^\times]$ enters only through the scales $c$ (`RelRepCount.lean`).

Sources: Shimura, *Arithmetic of Quadratic Forms* (2010), §4 [unverified locator]; Washington, *Introduction to
Cyclotomic Fields*, Thm. 4.12, Cor. 4.13 (units of CM fields) [unverified locator]; Cox §7 (the case $F = \mathbb Q$).
-/

open NumberField Module NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-! ### Norm-one units of a CM extension are the roots of unity -/

section CM

variable [IsTotallyReal F] [IsTotallyComplex E]

/-- **$\sigma$ is complex conjugation** under every complex embedding $\varphi$ of $E$: $\varphi(\sigma x) = \overline{\varphi(x)}$. -/
@[kb "washington1997" "§4.1 (CM fields) [unverified]"]
theorem isConj_conj (φ : E →+* ℂ) : ComplexEmbedding.IsConj φ (conj F E) := by
  have hram : IsRamified F (InfinitePlace.mk φ) :=
    isRamified_iff.mpr ⟨IsTotallyComplex.isComplex _, IsTotallyReal.isReal _⟩
  obtain ⟨g, hg⟩ := exists_isConj_of_isRamified hram
  have hg1 : g ≠ 1 := (ComplexEmbedding.isConj_ne_one_iff hg).mpr
    (IsTotallyComplex.complexEmbedding_not_isReal φ)
  rcases eq_one_or_eq_conj F E g with h | h
  · exact absurd h hg1
  · exact h ▸ hg

theorem place_conj (w : InfinitePlace E) (x : E) : w (conj F E x) = w x := by
  rw [← norm_embedding_eq, (isConj_conj (F := F) w.embedding).eq, ← norm_embedding_eq]
  exact Complex.norm_conj _

/-- **In a CM extension, $N_{E/F}(x) = 1$ iff $|x|_w = 1$ at every infinite place $w$ of $E$.** -/
@[kb "washington1997" "§4.1 [unverified]"]
theorem norm_eq_one_iff (x : E) : Algebra.norm F x = 1 ↔ ∀ w : InfinitePlace E, w x = 1 := by
  constructor
  · intro h w
    have h1 : w x * w x = 1 := by
      conv_lhs => rw [show w x * w x = w x * w (conj F E x) by rw [place_conj]]
      rw [← map_mul, ← algebraMap_norm, h, map_one, map_one]
    have h0 : 0 ≤ w x := by positivity
    nlinarith [h0]
  · intro h
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    set φ := w.embedding
    apply (algebraMap F E).injective
    apply φ.injective
    rw [map_one, map_one, algebraMap_norm, map_mul, (isConj_conj (F := F) φ).eq, RCLike.star_def,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_embedding_eq, h w]
    simp

/-- **Norm-one units are the roots of unity** (CM case): for $u \in \mathcal O_E^\times$, $N_{E/F}(u) = 1$ iff $u \in \mu_E$. -/
@[kb "washington1997" "Thm. 4.12 [unverified]"]
theorem normOneUnits_eq_torsion (u : (𝓞 E)ˣ) :
    Algebra.norm F ((u : 𝓞 E) : E) = 1 ↔ u ∈ torsion E := by
  rw [norm_eq_one_iff, mem_torsion]

/-- **$w_1 = w_E$:** the number of units of relative norm $1$ is the number of roots of unity of $E$. -/
@[kb "washington1997" "Thm. 4.12 [unverified]"]
theorem card_normOneUnits :
    Nat.card {u : (𝓞 E)ˣ // Algebra.norm F ((u : 𝓞 E) : E) = 1} = torsionOrder E := by
  rw [torsionOrder]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun u => normOneUnits_eq_torsion (F := F) u)

end CM

/-! ### Automorphisms of $(L, cN)$ -/

section Aut

theorem norm_div' (x y : E) : Algebra.norm F (x / y) = Algebra.norm F x / Algebra.norm F y := by
  by_cases hy : y = 0
  · subst hy; simp [Algebra.norm_eq_zero_iff.mpr rfl]
  have hinv : Algebra.norm F y⁻¹ = (Algebra.norm F y)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, inv_mul_cancel₀ hy, map_one]
  rw [div_eq_mul_inv, map_mul, hinv, div_eq_mul_inv]

/-- The isometry $x \mapsto u\,x$ or $x \mapsto u\,\sigma(x)$ ($N(u) = 1$) of $(E, cN)$, as an element of $O(E, cN)$. -/
def autOf (c : F) (u : E) (hu : Algebra.norm F u = 1) (b : Bool) :
    Lattices.orthGroupV (c • normForm F E) :=
  have hu0 : u ≠ 0 := by rintro rfl; rw [Algebra.norm_eq_zero_iff.mpr rfl] at hu; exact zero_ne_one hu
  ⟨(simIso (c := c) (c' := c) u hu0 (by rw [hu, mul_one]) b).toLinearEquiv, fun x =>
    (simIso (c := c) (c' := c) u hu0 (by rw [hu, mul_one]) b).map_app x⟩

theorem autOf_apply (c : F) (u : E) (hu : Algebra.norm F u = 1) (b : Bool) (x : E) :
    ((autOf c u hu b : Lattices.orthGroupV (c • normForm F E)) : E ≃ₗ[F] E) x =
      u * (if b then conj F E x else x) :=
  simIso_apply (c := c) (c' := c) _ _ (by rw [hu, mul_one]) b x

theorem map_autOf (c : F) (u : E) (hu : Algebra.norm F u = 1) (b : Bool) (L : Submodule (𝓞 F) E) :
    L.map (((autOf c u hu b : Lattices.orthGroupV (c • normForm F E)) : E ≃ₗ[F] E).toLinearMap.restrictScalars
      (𝓞 F)) = smulLat u (if b then conjLat L else L) :=
  map_simIso (c := c) (c' := c) _ _ (by rw [hu, mul_one]) b L

theorem exists_conj_ne : ∃ x : E, conj F E x ≠ x := by
  by_contra h
  push Not at h
  exact conj_ne_one F E (AlgEquiv.ext h)

/-- **The automorphism group of $(L, cN)$**, $c \ne 0$: $O(L) \simeq \{u : N(u) = 1,\ uL = L\} \sqcup
\{u : N(u) = 1,\ u\,\sigma(L) = L\}$ (proper $x \mapsto ux$, improper $x \mapsto u\,\sigma(x)$). -/
@[kb "omeara1963" "§82C, p. 223 (O(L)); §43C, p. 104"]
def autEquiv {c : F} (hc : c ≠ 0) (L : Submodule (𝓞 F) E) :
    Lattices.autLatV (c • normForm F E) L ≃
      ({u : E // Algebra.norm F u = 1 ∧ smulLat u L = L} ⊕
        {u : E // Algebra.norm F u = 1 ∧ smulLat u (conjLat L) = L}) := by
  classical
  have hiso : ∀ g : Lattices.orthGroupV (c • normForm F E),
      ∀ x, Algebra.norm F ((g : E ≃ₗ[F] E) x) = Algebra.norm F x := fun g x => by
    have := g.2 x
    simp only [_root_.smul_apply, normForm_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hc this
  exact
  { toFun := fun g =>
      if hp : ∀ x, ((g : Lattices.orthGroupV (c • normForm F E)) : E ≃ₗ[F] E) x = ((g : Lattices.orthGroupV (c • normForm F E)) : E ≃ₗ[F] E) 1 * x
      then Sum.inl ⟨((g : Lattices.orthGroupV (c • normForm F E)) : E ≃ₗ[F] E) 1,
        (linear_isometry _ (hiso g)).1, by
          have hg := g.2
          change L.map _ = L at hg
          conv_rhs => rw [← hg]
          rw [smulLat]
          congr 1
          ext x
          simp only [LinearMap.mulLeft_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
          exact (hp x).symm⟩
      else Sum.inr ⟨((g : Lattices.orthGroupV (c • normForm F E)) : E ≃ₗ[F] E) 1,
        (linear_isometry _ (hiso g)).1, by
          have hg := g.2
          change L.map _ = L at hg
          have hσ := ((linear_isometry _ (hiso g)).2).resolve_left hp
          conv_rhs => rw [← hg]
          rw [smulLat, conjLat, ← Submodule.map_comp]
          congr 1
          ext x
          simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.coe_restrictScalars,
            LinearEquiv.coe_coe, AlgEquiv.toLinearMap_apply]
          exact (hσ x).symm⟩
    invFun := fun s => match s with
      | Sum.inl u => ⟨autOf c u.1 u.2.1 false, by
          change L.map _ = L
          rw [map_autOf]; exact u.2.2⟩
      | Sum.inr u => ⟨autOf c u.1 u.2.1 true, by
          change L.map _ = L
          rw [map_autOf]; exact u.2.2⟩
    left_inv := by
      intro g
      by_cases hp : ∀ x, ((g : Lattices.orthGroupV (c • normForm F E)) : E ≃ₗ[F] E) x = ((g : Lattices.orthGroupV (c • normForm F E)) : E ≃ₗ[F] E) 1 * x
      · simp only [dite_eq_left hp]
        apply Subtype.ext; apply Subtype.ext; apply LinearEquiv.ext; intro x
        exact (autOf_apply c _ (linear_isometry _ (hiso g)).1 false x).trans (hp x).symm
      · simp only [dite_eq_right hp]
        have hσ := ((linear_isometry _ (hiso g)).2).resolve_left hp
        apply Subtype.ext; apply Subtype.ext; apply LinearEquiv.ext; intro x
        exact (autOf_apply c _ (linear_isometry _ (hiso g)).1 true x).trans (hσ x).symm
    right_inv := by
      intro s
      rcases s with ⟨u, hu, hL⟩ | ⟨u, hu, hL⟩
      · have hp : ∀ x, ((autOf c u hu false : Lattices.orthGroupV (c • normForm F E)) : E ≃ₗ[F] E) x =
            ((autOf c u hu false : Lattices.orthGroupV (c • normForm F E)) : E ≃ₗ[F] E) 1 * x := fun x => by
          simp [autOf_apply]
        simp only [dite_eq_left hp]
        congr 2
        simp [autOf_apply]
      · have hp : ¬ ∀ x, ((autOf c u hu true : Lattices.orthGroupV (c • normForm F E)) : E ≃ₗ[F] E) x =
            ((autOf c u hu true : Lattices.orthGroupV (c • normForm F E)) : E ≃ₗ[F] E) 1 * x := by
          intro h
          obtain ⟨x, hx⟩ := exists_conj_ne (F := F) (E := E)
          have := h x
          simp only [autOf_apply, ite_true, map_one, mul_one] at this
          have hu0 : u ≠ 0 := by rintro rfl; rw [Algebra.norm_eq_zero_iff.mpr rfl] at hu; exact zero_ne_one hu
          exact hx (mul_left_cancel₀ hu0 this)
        simp only [dite_eq_right hp]
        congr 2
        simp [autOf_apply] }

/-- For an ideal lattice $\mathfrak A \ne 0$: $u\mathfrak A = \mathfrak A$ iff $u$ is a unit of $\mathcal O_E$. -/
theorem smulLat_idealLat_eq_self_iff {𝔄 : Ideal (𝓞 E)} (h𝔄 : 𝔄 ≠ ⊥) (u : E) :
    smulLat u (idealLat F 𝔄) = idealLat F 𝔄 ↔ ∃ v : (𝓞 E)ˣ, algebraMap (𝓞 E) E v = u := by
  constructor
  · intro h
    by_cases hu : u = 0
    · exfalso
      subst hu
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔄
      have hm : algebraMap (𝓞 E) E a ∈ smulLat 0 (idealLat F 𝔄) := by
        rw [h]; exact algebraMap_mem_idealLat ha
      obtain ⟨y, -, hy⟩ := mem_smulLat.mp hm
      rw [zero_mul] at hy
      exact algebraMap_ne_zero ha0 hy.symm
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) u
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have h' := (smulLat_idealLat_iff (F := F) hy0 𝔄 𝔄).mp h.symm
    have hspan : Ideal.span {x} = Ideal.span {y} := mul_right_cancel₀ h𝔄 h'
    obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
    refine ⟨v⁻¹, ?_⟩
    have hx0 : algebraMap (𝓞 E) E x ≠ 0 := by
      intro h0; apply hu; rw [h0, zero_div]
    have hvv : algebraMap (𝓞 E) E (↑v⁻¹ : 𝓞 E) * algebraMap (𝓞 E) E (v : 𝓞 E) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [← hv, map_mul, eq_div_iff (mul_ne_zero hx0 (algebraMap_ne_zero v.ne_zero))]
    linear_combination (algebraMap (𝓞 E) E x) * hvv
  · rintro ⟨v, rfl⟩
    have h1 : (1 : 𝓞 E) ≠ 0 := one_ne_zero
    have := (smulLat_idealLat_iff (F := F) (x := (v : 𝓞 E)) h1 𝔄 𝔄).mpr (by
      rw [Ideal.span_singleton_eq_top.mpr v.isUnit, Ideal.span_singleton_one])
    rw [map_one, div_one] at this
    exact this.symm

/-- **Proper automorphisms of an ideal lattice are the norm-one units:**
$\{u : N(u) = 1,\ u\mathfrak A = \mathfrak A\} \simeq \{u \in \mathcal O_E^\times : N(u) = 1\}$ ($\mathfrak A \ne 0$). -/
@[kb "omeara1963" "§82C, p. 223 (O⁺(L)); cf. autSLEquivUnits"]
def properAutEquiv {𝔄 : Ideal (𝓞 E)} (h𝔄 : 𝔄 ≠ ⊥) :
    {u : E // Algebra.norm F u = 1 ∧ smulLat u (idealLat F 𝔄) = idealLat F 𝔄} ≃
      {v : (𝓞 E)ˣ // Algebra.norm F ((v : 𝓞 E) : E) = 1} where
  toFun u := ⟨((smulLat_idealLat_eq_self_iff (F := F) h𝔄 u.1).mp u.2.2).choose, by
    rw [show (((smulLat_idealLat_eq_self_iff (F := F) h𝔄 u.1).mp u.2.2).choose : 𝓞 E) =
      algebraMap (𝓞 E) E _ from rfl, ((smulLat_idealLat_eq_self_iff (F := F) h𝔄 u.1).mp u.2.2).choose_spec]
    exact u.2.1⟩
  invFun v := ⟨algebraMap (𝓞 E) E (v.1 : 𝓞 E), v.2, (smulLat_idealLat_eq_self_iff h𝔄 _).mpr ⟨v.1, rfl⟩⟩
  left_inv u := Subtype.ext ((smulLat_idealLat_eq_self_iff (F := F) h𝔄 u.1).mp u.2.2).choose_spec
  right_inv v := by
    apply Subtype.ext
    apply Units.ext
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    exact ((smulLat_idealLat_eq_self_iff (F := F) h𝔄 (algebraMap (𝓞 E) E (v.1 : 𝓞 E))).mp
      ((smulLat_idealLat_eq_self_iff h𝔄 _).mpr ⟨v.1, rfl⟩)).choose_spec

/-- **The improper automorphisms form a torsor under the proper ones:** if $u_0\,\sigma(L) = L$ with $N(u_0) = 1$, then
$u \mapsto u/u_0$ is a bijection from $\{u : N(u) = 1,\ u\,\sigma(L) = L\}$ onto $\{v : N(v) = 1,\ vL = L\}$. -/
def improperEquiv {L : Submodule (𝓞 F) E} {u₀ : E} (hu₀ : Algebra.norm F u₀ = 1)
    (hL₀ : smulLat u₀ (conjLat L) = L) :
    {u : E // Algebra.norm F u = 1 ∧ smulLat u (conjLat L) = L} ≃
      {v : E // Algebra.norm F v = 1 ∧ smulLat v L = L} :=
  have hu₀0 : u₀ ≠ 0 := by rintro rfl; rw [Algebra.norm_eq_zero_iff.mpr rfl] at hu₀; exact zero_ne_one hu₀
  have hsmul : ∀ (a b : E) (M : Submodule (𝓞 F) E), smulLat a (smulLat b M) = smulLat (a * b) M :=
      fun a b M => by
    rw [smulLat, smulLat, smulLat, ← Submodule.map_comp]
    congr 1
    ext x
    simp
  have hone : smulLat 1 L = L := by
    ext x; simp [mem_smulLat]
  { toFun := fun u => ⟨u.1 / u₀, by rw [norm_div', u.2.1, hu₀, div_one], by
      calc smulLat (u.1 / u₀) L = smulLat (u.1 / u₀) (smulLat u₀ (conjLat L)) := by rw [hL₀]
        _ = smulLat u.1 (conjLat L) := by rw [hsmul, div_mul_cancel₀ _ hu₀0]
        _ = L := u.2.2⟩
    invFun := fun v => ⟨v.1 * u₀, by rw [map_mul, v.2.1, hu₀, mul_one], by
      rw [← hsmul, hL₀]; exact v.2.2⟩
    left_inv := fun u => Subtype.ext (div_mul_cancel₀ _ hu₀0)
    right_inv := fun v => Subtype.ext (mul_div_cancel_right₀ _ hu₀0) }

/-- **The order of $O(\mathfrak A, cN)$:** $|O| = w_1 \cdot (2$ if $\mathfrak A$ has an improper automorphism, $1$ otherwise$)$,
$w_1 = \#\{u \in \mathcal O_E^\times : N_{E/F}(u) = 1\}$, assumed finite (true in the CM case, `card_autLat_ideal_cm`). -/
@[kb "omeara1963" "§82C, p. 223 (O(L)); cf. card_aut"]
theorem card_autLat_ideal {c : F} (hc : c ≠ 0) {𝔄 : Ideal (𝓞 E)} (h𝔄 : 𝔄 ≠ ⊥)
    (hfin : Finite {v : (𝓞 E)ˣ // Algebra.norm F ((v : 𝓞 E) : E) = 1}) :
    Nat.card (Lattices.autLatV (c • normForm F E) (idealLat F 𝔄)) =
      Nat.card {v : (𝓞 E)ˣ // Algebra.norm F ((v : 𝓞 E) : E) = 1} *
        (open Classical in
          if ∃ u : E, Algebra.norm F u = 1 ∧ smulLat u (idealLat F (conjIdeal F 𝔄)) = idealLat F 𝔄
          then 2 else 1) := by
  classical
  have hP : Finite {u : E // Algebra.norm F u = 1 ∧ smulLat u (idealLat F 𝔄) = idealLat F 𝔄} :=
    Finite.of_equiv _ (properAutEquiv h𝔄).symm
  rw [Nat.card_congr (autEquiv hc _)]
  by_cases h : ∃ u : E, Algebra.norm F u = 1 ∧ smulLat u (idealLat F (conjIdeal F 𝔄)) = idealLat F 𝔄
  · rw [ite_eq_left h]
    obtain ⟨u₀, hu₀, hL₀⟩ := h
    rw [← conjLat_idealLat] at hL₀
    have hI := Finite.of_equiv _ (improperEquiv hu₀ hL₀).symm
    rw [Nat.card_sum, Nat.card_congr (improperEquiv hu₀ hL₀), Nat.card_congr (properAutEquiv h𝔄)]
    ring
  · rw [ite_eq_right h]
    have he : IsEmpty {u : E // Algebra.norm F u = 1 ∧ smulLat u (conjLat (idealLat F 𝔄)) = idealLat F 𝔄} :=
      ⟨fun u => h ⟨u.1, u.2.1, by rw [← conjLat_idealLat]; exact u.2.2⟩⟩
    rw [Nat.card_sum, Nat.card_of_isEmpty (α := {u : E // Algebra.norm F u = 1 ∧
      smulLat u (conjLat (idealLat F 𝔄)) = idealLat F 𝔄}), add_zero, mul_one,
      Nat.card_congr (properAutEquiv h𝔄)]

theorem finite_normOneUnits [IsTotallyReal F] [IsTotallyComplex E] :
    Finite {v : (𝓞 E)ˣ // Algebra.norm F ((v : 𝓞 E) : E) = 1} :=
  Finite.of_equiv _ (Equiv.subtypeEquivRight fun u => normOneUnits_eq_torsion (F := F) u).symm

/-- **$|O(\mathfrak A, cN)| \in \{w_E, 2w_E\}$ in a CM extension** ($F$ totally real, $E$ totally complex), $w_E = |\mu_E|$. -/
@[kb "omeara1963" "§82C, p. 223 (O(L)); cf. card_aut"]
theorem card_autLat_ideal_cm [IsTotallyReal F] [IsTotallyComplex E] {c : F} (hc : c ≠ 0) {𝔄 : Ideal (𝓞 E)}
    (h𝔄 : 𝔄 ≠ ⊥) :
    Nat.card (Lattices.autLatV (c • normForm F E) (idealLat F 𝔄)) =
      torsionOrder E *
        (open Classical in
          if ∃ u : E, Algebra.norm F u = 1 ∧ smulLat u (idealLat F (conjIdeal F 𝔄)) = idealLat F 𝔄
          then 2 else 1) := by
  rw [card_autLat_ideal hc h𝔄 finite_normOneUnits, card_normOneUnits]

/-- **An ideal lattice with an improper automorphism is ambiguous:** $\sigma_*[\mathfrak A] = [\mathfrak A]$, so
$[\mathfrak A]^2 = 1$ in $\mathrm{Cl}_E/\iota(\mathrm{Cl}_F)$ (`conjClass_eq_inv_mod`). -/
@[kb "omeara1963" "§82C, p. 223; cf. exists_improper_iff"]
theorem conjClass_eq_of_improper (𝔄 : (Ideal (𝓞 E))⁰)
    (h : ∃ u : E, Algebra.norm F u = 1 ∧
      smulLat u (idealLat F (conjIdeal F (𝔄 : Ideal (𝓞 E)))) = idealLat F (𝔄 : Ideal (𝓞 E))) :
    conjClass F E (ClassGroup.mk0 𝔄) = ClassGroup.mk0 𝔄 := by
  obtain ⟨u, hu, hL⟩ := h
  have hu0 : u ≠ 0 := by rintro rfl; rw [Algebra.norm_eq_zero_iff.mpr rfl] at hu; exact zero_ne_one hu
  rw [conjClass_mk0]
  exact (exists_smulLat_iff (F := F) (conjIdeal0 F 𝔄) 𝔄).mp ⟨u, hu0, hL.symm⟩

end Aut

end QuadFormsKB.Binary.Rel
