/-
# Class number one with signs: Hanke's Corollary 5.2, second assertion, corrected

**Layer:** Shimura's Lemma 2.4(4) (`Hanke2005/SpinorIdeleMain.lean`: the proper classes of an indefinite genus are
$F^\times_{\mathbb A}/F^\times\sigma(D)$) and Shimura's Lemma 2.5 (`Hanke2005/ShimuraLemma25.lean`: $\mathfrak o_v^\times\subseteq\sigma(SO(L_v))$
for a maximal lattice, $n\ge3$).

Hanke (thesis, p. 19, proof of Cor. 5.2) argues: "from [Shi, Lemma 2.5] we know that $k^\times_{\mathbb A}/k^\times\sigma(D)$ is a
quotient of the ideal class group of $k$", hence one class when $k$ has class number one. By Shimura's Lemma 2.2(1),
$\sigma(G_w) = F_w^{\times2}$ (the positive reals) at the real places $w\in\mathbf c$ where $G_w$ is compact ($V_w$ definite), so
with $\sigma(D)\supseteq\prod_v\mathfrak o_v^\times$ the group $F^\times_{\mathbb A}/F^\times\sigma(D)$ is a quotient of the **class group with
signs at $\mathbf c$** (the ray class group of modulus $\prod_{w\in\mathbf c}w$), not of the ideal class group. The two agree when
the units of $F$ realize every sign pattern on $\mathbf c$, e.g. when $\lvert\mathbf c\rvert\le1$.

**Proves**
* `classIdeleSub_eq_top_of_signs`: if $\sigma(SO(L_v))\supseteq\mathfrak o_v^\times$ at every finite $v$ and every prime ideal of
  $\mathcal O_F$ has a generator that is a square (i.e. positive) at every infinite place where $V$ is anisotropic, then
  $F^\times\sigma(D) = F^\times_{\mathbb A}$;
* **`card_DC_eq_one_of_signs`**: under these hypotheses, for $Q_0$ indefinite in $n\ge3$ variables, there is one proper class;
  `card_DC_eq_one_of_maximal_signs`: the same for a maximal lattice (Shimura's Lemma 2.5 supplies the units);
* **`corollary52_classNumberOne_signs`** (Hanke's Cor. 5.2, second assertion, corrected): for $\Lambda = \mathcal O_F^n$ maximal,
  $Q_0$ indefinite, $n\ge3$, and $F$ with trivial class group with signs at $\mathbf c$: $\mathrm{vol}_Z(D) = s\cdot\mathrm{Mass}$;
* `exists_signed_generator`, **`corollary52_classNumberOne_le_one`**: Hanke's printed assertion holds when $\mathcal O_F$ is a
  principal ideal domain and $V$ is anisotropic at **at most one** real place (adjust the sign of a generator by $-1$).

All unconditional, standard axioms only.
-/
import QuadFormsKB.Literature.Hanke2005.SpinorIdeleMain
import QuadFormsKB.Literature.Hanke2005.ShimuraLemma25

open NumberField IsDedekindDomain Matrix WithZero MeasureTheory
open QuadFormsKB.OMeara (ideleAt ideleAtInf ideleAt_mul ideleAt_one ideleAt_inv ideleAtInf_mul ideleAtInf_one
  ideleAtInf_inv)
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Hanke2005.SpinorIdele

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Hanke2005.EqualMasses

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "J" => IdeleGroup (𝓞 F) F

attribute [local instance] charZero_completion

/-! ### Valuations of a generator of a prime ideal -/

section Generator

theorem ne_zero_of_span_eq {v : HeightOneSpectrum (𝓞 F)} {π : 𝓞 F} (hπ : Ideal.span {π} = v.asIdeal) : π ≠ 0 := by
  rintro rfl
  apply v.ne_bot
  rw [← hπ, Ideal.span_singleton_eq_bot]

theorem intValuation_gen_self {v : HeightOneSpectrum (𝓞 F)} {π : 𝓞 F} (hπ : Ideal.span {π} = v.asIdeal) :
    v.intValuation π = exp (-1 : ℤ) :=
  v.intValuation_singleton (ne_zero_of_span_eq hπ) hπ.symm

theorem intValuation_gen_of_ne {v w : HeightOneSpectrum (𝓞 F)} {π : 𝓞 F} (hπ : Ideal.span {π} = w.asIdeal)
    (hvw : v ≠ w) : v.intValuation π = 1 := by
  rw [HeightOneSpectrum.intValuation_eq_one_iff]
  intro hmem
  apply hvw
  have hle : w.asIdeal ≤ v.asIdeal := by
    rw [← hπ, Ideal.span_le, Set.singleton_subset_iff]; exact hmem
  exact HeightOneSpectrum.ext ((w.isMaximal.eq_of_le v.isPrime.ne_top hle).symm)

end Generator

/-! ### $F^\times\sigma(D) = F^\times_{\mathbb A}$ -/

section Main

variable (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **The class group with signs is trivial** for $V$ (hypothesis of Hanke's Cor. 5.2(ii), corrected): every prime
ideal $\mathfrak p_v$ of $\mathcal O_F$ has a generator $\pi$ that is a square in $F_w$ at every infinite place $w$ where $V_w$ is
anisotropic (for a real place: $\pi>0$ at the compact places $w\in\mathbf c$). Equivalently, the ray class group of $F$ of
modulus $\prod_{w\in\mathbf c}w$ is trivial. -/
def SignedClassNumberOne : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ∃ π : 𝓞 F, Ideal.span {π} = v.asIdeal ∧
    ∀ w : InfinitePlace F, ¬ (QF).IsotropicIn w.Completion → IsSquare (algebraMap (𝓞 F) w.Completion π)

/-- **$F^\times\sigma(D) = F^\times_{\mathbb A}$** when $\sigma(SO(L_v))\supseteq\mathfrak o_v^\times$ at every finite place (`hunits`) and
the class group with signs at the compact places is trivial (`hsign`). -/
theorem classIdeleSub_eq_top_of_signs
    (hunits : ∀ v : HeightOneSpectrum (𝓞 F), ∀ u : v.adicCompletion F, Valued.v u = 1 →
      sqClassOf u ∈ sigmaFin QF (nondegenerate_map Q₀ hQ) v)
    (hsign : SignedClassNumberOne Q₀) :
    classIdeleSub QF (nondegenerate_map Q₀ hQ) = ⊤ := by
  classical
  have hQF := nondegenerate_map Q₀ hQ
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨a, ha⟩ := exists_isSquare_div x
  set y : J := x * (IdeleGroup.unitEmbedding (𝓞 F) F a)⁻¹
  have hyw : ∀ w, IsSquare (ideleAtInf y w) := by
    intro w
    have e : ideleAtInf y w = ideleAtInf x w / algebraMap F w.Completion (a : F) := by
      simp only [y, ideleAtInf_mul, ideleAtInf_inv, ideleAtInf_unitEmbedding, div_eq_mul_inv]
    rw [e]; exact ha w
  -- the finitely many places where `y_v` is not a unit
  have hfin : {v : HeightOneSpectrum (𝓞 F) | Valued.v (ideleAt y v) ≠ 1}.Finite :=
    Filter.eventually_cofinite.mp (NumberField.AdeleRing.isUnit_iff.mp (Units.isUnit y)).2.2
  set S := hfin.toFinset
  choose π hπ hπsq using hsign
  let m : HeightOneSpectrum (𝓞 F) → ℤ := fun v => log (Valued.v (ideleAt y v))
  have hm : ∀ v, Valued.v (ideleAt y v) = exp (m v) := fun v =>
    (exp_log ((map_ne_zero _).mpr (ideleAt_ne_zero y v))).symm
  have hπ0 : ∀ v, (algebraMap (𝓞 F) F (π v)) ≠ 0 := fun v =>
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr (ne_zero_of_span_eq (hπ v))
  -- `β = ∏_{v ∈ S} π_v^{-m_v}`
  set β : Fˣ := ∏ v ∈ S, (Units.mk0 _ (hπ0 v)) ^ (-(m v))
  have hβv : ∀ v', Valued.v (algebraMap F (v'.adicCompletion F) (β : F)) = if v' ∈ S then exp (m v') else 1 := by
    intro v'
    have hval : ∀ v, Valued.v (algebraMap F (v'.adicCompletion F) (algebraMap (𝓞 F) F (π v))) =
        if v' = v then exp (-1 : ℤ) else 1 := by
      intro v
      rw [← IsScalarTower.algebraMap_apply, valued_algebraMap_int]
      split_ifs with h
      · subst h; exact intValuation_gen_self (hπ v')
      · exact intValuation_gen_of_ne (hπ v) h
    simp only [β, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_prod, map_zpow₀, hval]
    split_ifs with hv'
    · rw [Finset.prod_eq_single_of_mem v' hv']
      · simp only [if_true]
        rw [← WithZero.exp_zsmul, smul_eq_mul]; congr 1; ring
      · intro v _ hv; rw [if_neg (Ne.symm hv), _root_.one_zpow]
    · refine Finset.prod_eq_one fun v hv => ?_
      rw [if_neg (fun h => hv' (by rw [h]; exact hv)), _root_.one_zpow]
  have hβw : ∀ w : InfinitePlace F, ¬ (QF).IsotropicIn w.Completion → IsSquare (algebraMap F w.Completion (β : F)) := by
    intro w hw
    simp only [β, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_prod, map_zpow₀]
    refine Finset.prod_induction _ IsSquare (fun _ _ h1 h2 => h1.mul h2) ⟨1, by simp⟩ fun v _ => ?_
    have := hπsq v w hw
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F w.Completion] at this
    exact this.zpow _
  -- `z = y / β ∈ σ(D)`
  set z : J := y * (IdeleGroup.unitEmbedding (𝓞 F) F β)⁻¹
  have hz : z ∈ sigmaD QF hQF := by
    refine ⟨fun w => ?_, fun v => ?_⟩
    · by_cases hw : (QF).IsotropicIn w.Completion
      · exact mem_sigmaInf_of_isotropic QF hQF hw _
      · have hsq : IsSquare (ideleAtInf z w) := by
          simp only [z, ideleAtInf_mul, ideleAtInf_inv, ideleAtInf_unitEmbedding]
          exact (hyw w).mul (hβw w hw).inv
        rw [(sqClassOf_eq_one_iff (ideleAtInf_ne_zero z w)).mpr hsq]; exact Subgroup.one_mem _
    · refine hunits v _ ?_
      simp only [z, ideleAt_mul, ideleAt_inv, ideleAt_unitEmbedding, map_mul, map_inv₀, hβv]
      split_ifs with hv
      · rw [hm, mul_inv_cancel₀ (exp_ne_zero)]
      · have : Valued.v (ideleAt y v) = 1 := by
          by_contra h; exact hv (hfin.mem_toFinset.mpr h)
        rw [this, inv_one, mul_one]
  have hx : x = z * IdeleGroup.unitEmbedding (𝓞 F) F β * IdeleGroup.unitEmbedding (𝓞 F) F a := by
    simp only [z, y]; group
  rw [hx]
  refine (classIdeleSub QF hQF).mul_mem ((classIdeleSub QF hQF).mul_mem (Subgroup.mem_sup_right hz) ?_) ?_
  · exact Subgroup.mem_sup_left ⟨β, rfl⟩
  · exact Subgroup.mem_sup_left ⟨a, rfl⟩

/-- **One proper class when the class group with signs is trivial** (Hanke's Cor. 5.2(ii), corrected, via Shimura's
Lemma 2.4(4)): $Q_0$ nondegenerate and indefinite in $n\ge3$ variables, $\sigma(SO(L_v))\supseteq\mathfrak o_v^\times$ at every finite
place, and every prime of $F$ has a generator positive at the real places where $V$ is anisotropic. -/
@[kb "hanke2005crelle" "Corollary 5.2, p. 19 (second assertion; corrected: class group with signs)"]
theorem card_DC_eq_one_of_signs (hn : 3 ≤ n) (hind : IsIndefinite QF)
    (hunits : ∀ v : HeightOneSpectrum (𝓞 F), ∀ u : v.adicCompletion F, Valued.v u = 1 →
      sqClassOf u ∈ sigmaFin QF (nondegenerate_map Q₀ hQ) v)
    (hsign : SignedClassNumberOne Q₀) : Nat.card (DC Q₀) = 1 := by
  rw [card_DC_eq_index_idele Q₀ hQ hn hind, classIdeleSub_eq_top_of_signs Q₀ hQ hunits hsign,
    Subgroup.index_top]

include hQ in
/-- **One proper class for a maximal lattice when the class group with signs is trivial**: $\Lambda = \mathcal O_F^n$ maximal,
$Q_0$ indefinite, $n\ge3$ (Shimura's Lemma 2.5 gives $\mathfrak o_v^\times\subseteq\sigma(SO(L_v))$). -/
@[kb "hanke2005crelle" "Corollary 5.2, p. 19 (second assertion; corrected: class group with signs)"]
theorem card_DC_eq_one_of_maximal_signs (hn : 3 ≤ n) (hind : IsIndefinite QF) (hmax : StdIsMaximal Q₀)
    (hsign : SignedClassNumberOne Q₀) : Nat.card (DC Q₀) = 1 := by
  refine card_DC_eq_one_of_signs Q₀ hQ hn hind (fun v u hu => ?_) hsign
  obtain ⟨g, hg, hgσ⟩ := shimuraLemma25 v hn Q₀ hQ hmax hu
  exact (mem_sigmaFin _ _).mpr ⟨g, hg, hgσ⟩

open Eq57 in
/-- **Hanke's Corollary 5.2, second assertion, corrected** (thesis, p. 19: "If $k$ has class number one, then
$\mathrm{vol}(\Gamma_a\backslash Z) = \varepsilon\,\mathrm{Mass}(\Lambda,\varphi)$"): for $\Lambda = \mathcal O_F^n$ maximal, $Q_0$ indefinite in $n\ge3$
variables, and $F$ with **trivial class group with signs at the compact real places** (`SignedClassNumberOne`), every class
has $\mathrm{vol}_Z(D) = s\cdot\mathrm{Mass}$, $s$ the multiplicity of the fundamental domain $D$. -/
@[kb "hanke2005crelle" "Corollary 5.2, p. 19 (second assertion; corrected: class group with signs)"]
theorem corollary52_classNumberOne_signs (hn : 3 ≤ n) (hind : IsIndefinite QF) (hmax : StdIsMaximal Q₀)
    (hsign : SignedClassNumberOne Q₀)
    (D : DC Q₀ → Set (ZQ Q₀ hQ)) (hD : ∀ i, MeasurableSet (D i)) (s : DC Q₀ → ℝ≥0∞) (hs0 : ∀ i, s i ≠ 0)
    (hsT : ∀ i, s i ≠ ⊤)
    (hDs : ∀ i, ∀ᵐ z ∂(muZQ Q₀ hQ), ∑' γ : unitGroup Q₀ i, (D i).indicator 1 (γ • z) = s i) (i : DC Q₀) :
    muZQ Q₀ hQ (D i) = s i * hankeMass Q₀ hQ :=
  corollary52_indefinite_classNumberOne Q₀ hn hQ hind D hD s hs0 hsT hDs
    (card_DC_eq_one_of_maximal_signs Q₀ hQ hn hind hmax hsign) i

/-- **At most one compact real place**: if $\mathcal O_F$ is a principal ideal domain and $V$ is anisotropic at most at one
real place, the class group with signs at $\mathbf c$ is trivial (replace a generator $\pi$ by $-\pi$ if needed). -/
theorem signedClassNumberOne_of_le_one [IsPrincipalIdealRing (𝓞 F)]
    (hc : ∀ w w' : InfinitePlace F, ¬ (QF).IsotropicIn w.Completion → ¬ (QF).IsotropicIn w'.Completion → w = w') :
    SignedClassNumberOne Q₀ := by
  intro v
  obtain ⟨π0, hπ0⟩ := (IsPrincipalIdealRing.principal v.asIdeal)
  have hspan : Ideal.span {π0} = v.asIdeal := by rw [hπ0]
  by_cases hany : ∃ w0 : InfinitePlace F, ¬ (QF).IsotropicIn w0.Completion
  · obtain ⟨w0, hw0⟩ := hany
    have hsq0 : ∀ π : 𝓞 F, (∀ w : InfinitePlace F, ¬ (QF).IsotropicIn w.Completion →
        IsSquare (algebraMap (𝓞 F) w.Completion π)) ↔ IsSquare (algebraMap (𝓞 F) w0.Completion π) := by
      intro π
      refine ⟨fun h => h w0 hw0, fun h w hw => ?_⟩
      rw [hc w w0 hw hw0]; exact h
    by_cases hreal : w0.IsReal
    · rcases isSquare_or_isSquare_neg w0 hreal (algebraMap (𝓞 F) w0.Completion π0) with h | h
      · exact ⟨π0, hspan, (hsq0 π0).mpr h⟩
      · refine ⟨-π0, by rw [Ideal.span_singleton_neg]; exact hspan, (hsq0 _).mpr ?_⟩
        rw [map_neg]; exact h
    · exact ⟨π0, hspan, (hsq0 π0).mpr
        (isSquare_of_isComplex w0 (InfinitePlace.not_isReal_iff_isComplex.mp hreal) _)⟩
  · push Not at hany
    exact ⟨π0, hspan, fun w hw => absurd (hany w) hw⟩

open Eq57 in
/-- **Hanke's Corollary 5.2, second assertion, as printed, when at most one real place is compact**: for
$\Lambda = \mathcal O_F^n$ maximal, $Q_0$ indefinite in $n\ge3$ variables, $\mathcal O_F$ a principal ideal domain (class number one),
and $V$ anisotropic at most at one real place: $\mathrm{vol}_Z(D) = s\cdot\mathrm{Mass}$. -/
@[kb "hanke2005crelle" "Corollary 5.2, p. 19 (second assertion, at most one compact real place)"]
theorem corollary52_classNumberOne_le_one [IsPrincipalIdealRing (𝓞 F)] (hn : 3 ≤ n) (hind : IsIndefinite QF)
    (hmax : StdIsMaximal Q₀)
    (hc : ∀ w w' : InfinitePlace F, ¬ (QF).IsotropicIn w.Completion → ¬ (QF).IsotropicIn w'.Completion → w = w')
    (D : DC Q₀ → Set (ZQ Q₀ hQ)) (hD : ∀ i, MeasurableSet (D i)) (s : DC Q₀ → ℝ≥0∞) (hs0 : ∀ i, s i ≠ 0)
    (hsT : ∀ i, s i ≠ ⊤)
    (hDs : ∀ i, ∀ᵐ z ∂(muZQ Q₀ hQ), ∑' γ : unitGroup Q₀ i, (D i).indicator 1 (γ • z) = s i) (i : DC Q₀) :
    muZQ Q₀ hQ (D i) = s i * hankeMass Q₀ hQ :=
  corollary52_classNumberOne_signs Q₀ hQ hn hind hmax (signedClassNumberOne_of_le_one Q₀ hc) D hD s hs0 hsT hDs i

end Main

end QuadFormsKB.Hanke2005.SpinorIdele
