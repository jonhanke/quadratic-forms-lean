/-
# O'Meara §71B: the idèle group $P_F N_{E/F} J_E$ and the reciprocity special cases 71:12, 71:13

**Setting** (O'Meara §71, p. 190, assumptions (i)–(iii)): $F$ is a number field, $\theta \in F$ is a non-square, and
$E = F(\sqrt\theta)$, given as a quadratic number field extension `E` with an element $s$, $s^2 = \theta$, such that
$E = F + Fs$. The idèle group $J_F$ is Mathlib's `IdeleGroup (𝓞 F) F` (as in `Sec64.lean`).

**The norm idèles.** O'Meara's $N_{E/F} J_E$ is the image of the idèle norm $J_E \to J_F$. That map (which needs the
maps between the completions of $F$ and of $E$) is not available, so `normIdeles E` is defined by the
characterization of Example 65:2 (O'Meara §65A, p. 176): an idèle of $F$ is in $N_{E/F}J_E$ if and only if it is a
local norm at every spot, i.e. its component $i_\mathfrak p$ lies in the local norm group
$N(F_\mathfrak p \otimes_F E)^\times$ (`HN.normGroup`; $F_\mathfrak p \otimes_F E = \prod_{\mathfrak P \mid \mathfrak p}
E_\mathfrak P$). The group $P_F N_{E/F} J_E$ is `principalNormIdeles E`. *Local degree $1$ at $\mathfrak q$*
($n_\mathfrak q = [E_\mathfrak Q : F_\mathfrak q] = 1$) is "$\theta$ is a square in $F_\mathfrak q$", as in `Sec65A.lean`.

**Proves**
* `mem_normGroup_iff_hilbertSymbol` (§65A, p. 176, through 63:10): $x \in N(M \otimes_F E)^\times$ iff
  $(x, \theta)_M = 1$, for every field $M \supseteq F$ of characteristic $\ne 2$;
* `mem_principalNormIdeles_iff` (the kernel description in the proof of 71:19, p. 203): $i \in P_F N_{E/F}J_E$ iff
  the set of spots with $(i_\mathfrak p, \theta)_\mathfrak p = -1$ is finite of even cardinality. The proof uses the
  library's Hilbert reciprocity (Weil index, `HN.hilbert_product_formula_nf`) and the existence of elements with
  prescribed Hilbert symbols (`PresNF.exists_prescribed_hilbert`), not O'Meara's ten-field construction;
* Proposition 71:12 (p. 195), `ideleSupportedAt_le_principalNormIdeles_of_cyclotomic`, and its general form
  `ideleSupportedAt_le_principalNormIdeles_iff` (also Proposition 71:17);
* Proposition 71:13 (p. 196), `prod_infinite_hilbert_neg_one`: the product form of `even_card_infinite_hilbert_neg_one`
  (`Sec71B.lean`).
-/
import QuadFormsKB.Literature.OMeara.Sec65B
import QuadFormsKB.Literature.OMeara.Sec71A
import QuadFormsKB.Literature.OMeara.Sec71B
import QuadFormsKB.Literature.HasseNorm.KummerSquares
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain
import QuadFormsKB.Literature.LocalGlobal.HasseIsometryNF

open NumberField IsDedekindDomain
open scoped TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type} [Field F] [NumberField F]

local notation "J" => IdeleGroup (𝓞 F) F

/-! ### Local norms and the Hilbert symbol -/

/-- **Local norms from $E = F(\sqrt\theta)$ and the Hilbert symbol** (O'Meara 1963, §65A, p. 176, through 63:10): for
a field $M \supseteq F$ of characteristic $\ne 2$ and $x \in \dot M$, $x$ is a norm from $M \otimes_F E$ if and only if
$(x, \theta)_M = 1$. -/
@[kb "omeara1963" "§65A, p. 176 (local norm if and only if the Hilbert symbol is 1); §63B, 63:10, p. 164"]
theorem mem_normGroup_iff_hilbertSymbol {E : Type} [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] {θ : F} (hθ : ¬ IsSquare θ) {s : E} (hs : s ^ 2 = algebraMap F E θ)
    (hspan : ∀ y : E, ∃ b₀ b₁ : F, y = algebraMap F E b₀ + algebraMap F E b₁ * s)
    (M : Type) [Field M] [Algebra F M] (h2 : (2 : M) ≠ 0) (x : Mˣ) :
    x ∈ HN.normGroup (F := F) E M ↔ hilbertSymbol M (x : M) (algebraMap F M θ) = 1 := by
  obtain ⟨t, -, ht2, hspanT, -, hnormT, -⟩ := HN.tensor_structure θ hθ s hs hspan M
  have hθ0 : θ ≠ 0 := fun h => hθ ⟨0, by simp [h]⟩
  have hθM : algebraMap F M θ ≠ 0 := (map_ne_zero _).mpr hθ0
  rw [hilbertSymbol_comm, HN.hilbertSymbol_eq_one_iff_norm M h2 hθM]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨x₀, x₁, hy⟩ := hspanT (u : M ⊗[F] E)
    refine ⟨x₀, x₁, ?_⟩
    have := congrArg (fun z : Mˣ => (z : M)) hu
    simp only [Units.coe_map] at this
    rw [← this, hy, hnormT]
  · rintro ⟨x₀, x₁, hx⟩
    set y : M ⊗[F] E := algebraMap M _ x₀ + algebraMap M _ x₁ * t
    set z : M ⊗[F] E := algebraMap M _ x₀ - algebraMap M _ x₁ * t
    have hyz : y * z = algebraMap M _ (x : M) := by
      rw [hx]
      simp only [y, z, map_sub, map_mul, map_pow]
      linear_combination -(algebraMap M (M ⊗[F] E) x₁) ^ 2 * ht2
    have hyu : IsUnit y := by
      refine isUnit_of_mul_isUnit_left (y := z) ?_
      rw [hyz]
      exact (x.isUnit).map _
    refine ⟨hyu.unit, Units.ext ?_⟩
    simp only [Units.coe_map, IsUnit.unit_spec]
    rw [hnormT, hx]

omit [NumberField F] in
theorem two_ne_zero_of_algebra (F : Type*) [Field F] [CharZero F] (M : Type*) [Field M] [Algebra F M] : (2 : M) ≠ 0 := by
  have h := (map_ne_zero (algebraMap F M)).mpr (two_ne_zero : (2 : F) ≠ 0)
  rwa [map_ofNat] at h

/-! ### The groups $N_{E/F} J_E$ and $P_F N_{E/F} J_E$ -/

/-- **The norm idèles $N_{E/F} J_E$** (O'Meara 1963, §65A, p. 176, through Example 65:2): the idèles of $F$ whose
component at every spot (finite or infinite) is a local norm, i.e. lies in $N(F_\mathfrak p \otimes_F E)^\times$
(`HN.normGroup`). O'Meara defines $N_{E/F} J_E$ as the image of the idèle norm $J_E \to J_F$; Example 65:2 shows that
this image is the group of idèles that are local norms everywhere, and that characterization is used as the definition
here (the idèle norm map is not available). -/
@[kb "omeara1963" "§65A, p. 176 (N_{E/F}J_E, through Example 65:2)"]
def normIdeles (E : Type) [Field E] [Algebra F E] : Subgroup J :=
  (⨅ v : HeightOneSpectrum (𝓞 F), (HN.normGroup (F := F) E (v.adicCompletion F)).comap (idAtHom v)) ⊓
    ⨅ w : InfinitePlace F, (HN.normGroup (F := F) E w.Completion).comap (idAtInfHom w)

/-- **The group $P_F N_{E/F} J_E$** (O'Meara 1963, §65A, p. 176): the product of the principal idèles $P_F$ (Mathlib's
`IdeleGroup.principalSubgroup`) and the norm idèles `normIdeles E`. -/
@[kb "omeara1963" "§65A, p. 176 (the group P_F N_{E/F}J_E)"]
def principalNormIdeles (E : Type) [Field E] [Algebra F E] : Subgroup J :=
  IdeleGroup.principalSubgroup (𝓞 F) F ⊔ normIdeles E

/-- **The Hilbert symbol $(i_\mathfrak p, \theta)_\mathfrak p$ of the component of an idèle** at a spot
$\mathfrak p$ (finite or infinite), the factors of O'Meara's homomorphism
$\varphi(i) = \prod_\mathfrak p (i_\mathfrak p, \theta)_\mathfrak p$ (proof of 71:19, p. 203). -/
def ideleSymbol (θ : F) (i : J) : NFPlace F → ℤ
  | .finite v => hilbertSymbol (v.adicCompletion F) (ideleAt i v) (algebraMap F _ θ)
  | .infinite w => hilbertSymbol w.Completion (ideleAtInf i w) (algebraMap F _ θ)

theorem ideleAt_ne_zero (i : J) (v : HeightOneSpectrum (𝓞 F)) : ideleAt i v ≠ 0 :=
  (idAtHom v i).ne_zero

theorem ideleAtInf_ne_zero (i : J) (w : InfinitePlace F) : ideleAtInf i w ≠ 0 :=
  (idAtInfHom w i).ne_zero

theorem ideleSymbol_mul {θ : F} (hθ : θ ≠ 0) (i j : J) (v : NFPlace F) :
    ideleSymbol θ (i * j) v = ideleSymbol θ i v * ideleSymbol θ j v := by
  cases v with
  | finite v =>
    simp only [ideleSymbol, ideleAt_mul]
    exact HN.hilbertSymbol_mul_left_finite_nf v _ _ _ (ideleAt_ne_zero i v) (ideleAt_ne_zero j v)
      ((map_ne_zero _).mpr hθ)
  | infinite w =>
    simp only [ideleSymbol, ideleAtInf_mul]
    exact NFLocal.hilbertSymbol_mul_left_infinite_nf w _ _ _ (ideleAtInf_ne_zero i w) (ideleAtInf_ne_zero j w)
      ((map_ne_zero _).mpr hθ)

theorem ideleSymbol_pm (θ : F) (i : J) (v : NFPlace F) : ideleSymbol θ i v = 1 ∨ ideleSymbol θ i v = -1 := by
  cases v <;> exact HN.hilbertSymbol_eq_one_or _ _ _

theorem ideleSymbol_inv {θ : F} (hθ : θ ≠ 0) (i : J) (v : NFPlace F) :
    ideleSymbol θ i⁻¹ v = ideleSymbol θ i v := by
  have h := ideleSymbol_mul hθ i⁻¹ i v
  rw [inv_mul_cancel] at h
  have h1 : ideleSymbol θ 1 v = 1 := by
    cases v with
    | finite v =>
      show hilbertSymbol _ (ideleAt 1 v) _ = 1
      rw [ideleAt_one, hilbertSymbol_comm, hilbertSymbol_one_right]
    | infinite w =>
      show hilbertSymbol _ (ideleAtInf 1 w) _ = 1
      rw [ideleAtInf_one, hilbertSymbol_comm, hilbertSymbol_one_right]
  rw [h1] at h
  rcases ideleSymbol_pm θ i v with h' | h' <;> rw [h'] at h ⊢ <;> linarith

theorem ideleSymbol_unitEmbedding (θ : F) (α : Fˣ) (v : NFPlace F) :
    ideleSymbol θ (IdeleGroup.unitEmbedding (𝓞 F) F α) v = v.hilbert (α : F) θ := by
  cases v with
  | finite v =>
    show hilbertSymbol _ (ideleAt _ v) _ = _
    rw [ideleAt_unitEmbedding]; rfl
  | infinite w =>
    show hilbertSymbol _ (ideleAtInf _ w) _ = _
    rw [ideleAtInf_unitEmbedding]; rfl

/-- **The norm idèles by Hilbert symbols** (O'Meara 1963, §65A, p. 176): for $E = F(\sqrt\theta)$, an idèle $i$ lies in
$N_{E/F}J_E$ if and only if $(i_\mathfrak p, \theta)_\mathfrak p = 1$ at every spot $\mathfrak p$. -/
@[kb "omeara1963" "§65A, p. 176 (i ∈ N_{E/F}J_E iff (i_𝔭, θ)_𝔭 = 1 for all 𝔭)"]
theorem mem_normIdeles_iff {E : Type} [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] {θ : F} (hθ : ¬ IsSquare θ) {s : E} (hs : s ^ 2 = algebraMap F E θ)
    (hspan : ∀ y : E, ∃ b₀ b₁ : F, y = algebraMap F E b₀ + algebraMap F E b₁ * s) (i : J) :
    i ∈ normIdeles E ↔ ∀ v : NFPlace F, ideleSymbol θ i v = 1 := by
  have hf : ∀ v : HeightOneSpectrum (𝓞 F), idAtHom v i ∈ HN.normGroup (F := F) E (v.adicCompletion F) ↔
      ideleSymbol θ i (.finite v) = 1 := fun v =>
    mem_normGroup_iff_hilbertSymbol hθ hs hspan (v.adicCompletion F) (two_ne_zero_of_algebra F _) (idAtHom v i)
  have hi : ∀ w : InfinitePlace F, idAtInfHom w i ∈ HN.normGroup (F := F) E w.Completion ↔
      ideleSymbol θ i (.infinite w) = 1 := fun w =>
    mem_normGroup_iff_hilbertSymbol hθ hs hspan w.Completion (two_ne_zero_of_algebra F _) (idAtInfHom w i)
  simp only [normIdeles, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, hf, hi]
  constructor
  · rintro ⟨h1, h2⟩ v
    cases v with
    | finite v => exact h1 v
    | infinite w => exact h2 w
  · intro h
    exact ⟨fun v => h _, fun w => h _⟩

theorem NFPlace_hilbert_comm (v : NFPlace F) (a b : F) : v.hilbert a b = v.hilbert b a := by
  cases v <;> exact hilbertSymbol_comm _ _ _

/-- **Non-degeneracy at an infinite spot:** a non-square $c \in \dot F_w$ has $(c, x)_w = -1$ for some $x$ ($w$ is
real and $c < 0$; take $x = -1$). -/
theorem exists_hilbertSymbol_neg_one_infinite (w : InfinitePlace F) {c : w.Completion} (_hc : c ≠ 0)
    (hns : ¬ IsSquare c) : ∃ x : w.Completion, x ≠ 0 ∧ hilbertSymbol w.Completion c x = -1 := by
  rcases InfinitePlace.isReal_or_isComplex w with hw | hw
  · set φ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have hneg : φ c < 0 := by
      by_contra hpos
      push Not at hpos
      apply hns
      refine ⟨φ.symm (Real.sqrt (φ c)), ?_⟩
      apply φ.injective
      rw [map_mul, RingEquiv.apply_symm_apply, Real.mul_self_sqrt hpos]
    refine ⟨-1, by simp, ?_⟩
    rw [← HasseIsoNF.hilbertSymbol_ringEquiv φ, map_neg, map_one,
      HasseIsoNF.hilbertSymbol_real_eq _ _ hneg.ne (by norm_num)]
    simp [hneg]
  · exfalso
    apply hns
    set φ := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (φ c) (n := 2) (by norm_num)
    refine ⟨φ.symm r, ?_⟩
    apply φ.injective
    rw [map_mul, RingEquiv.apply_symm_apply, ← sq, hr]

/-- **Non-degeneracy at every spot:** if $c \in F$ is not a square in $F_v$, then $(c, x)_v = -1$ for some
$x \in \dot F_v$ (O'Meara 63:13 at a discrete spot). -/
theorem exists_hilbertSymbol_neg_one (v : NFPlace F) {c : F} (hc : c ≠ 0)
    (hns : v.atPlace fun K _ _ => ¬ IsSquare (algebraMap F K c)) :
    v.atPlace fun K _ _ => ∃ x : K, x ≠ 0 ∧ hilbertSymbol K (algebraMap F K c) x = -1 := by
  cases v with
  | finite v =>
    exact (HasseIsoNF.localHilbertField_adicCompletion v).exists_neg_one _ ((map_ne_zero _).mpr hc) hns
  | infinite w => exact exists_hilbertSymbol_neg_one_infinite w ((map_ne_zero _).mpr hc) hns

/-! ### The kernel description of $P_F N_{E/F} J_E$ -/

section Kernel

variable {E : Type} [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] {θ : F}
  (hθ : ¬ IsSquare θ) {s : E} (hs : s ^ 2 = algebraMap F E θ)
  (hspan : ∀ y : E, ∃ b₀ b₁ : F, y = algebraMap F E b₀ + algebraMap F E b₁ * s)
include hθ hs hspan

open scoped Classical

omit hs hspan in
theorem ne_zero_of_not_isSquare : θ ≠ 0 := fun h => hθ ⟨0, by simp [h]⟩

/-- **Necessity** (O'Meara 1963, proof of 71:19, p. 203: $N_{E/F}J_E$ and $P_F$ lie in the kernel of
$\varphi(i) = \prod_\mathfrak p (i_\mathfrak p, \theta)_\mathfrak p$, the second by Hilbert's reciprocity law): for
$i \in P_F N_{E/F} J_E$ the set of spots with $(i_\mathfrak p, \theta)_\mathfrak p = -1$ is finite of even
cardinality. -/
theorem ideleSymbol_finite_even_of_mem {i : J} (hi : i ∈ principalNormIdeles E) :
    {v : NFPlace F | ideleSymbol θ i v = -1}.Finite ∧ Even {v : NFPlace F | ideleSymbol θ i v = -1}.ncard := by
  have hθ0 := ne_zero_of_not_isSquare hθ
  obtain ⟨y, ⟨α, rfl⟩, z, hz, rfl⟩ := Subgroup.mem_sup.mp hi
  have hz' := (mem_normIdeles_iff hθ hs hspan z).mp hz
  have hset : {v : NFPlace F | ideleSymbol θ (IdeleGroup.unitEmbedding (𝓞 F) F α * z) v = -1} =
      {v : NFPlace F | v.hilbert (α : F) θ = -1} := by
    ext v
    simp only [Set.mem_ofPred_eq, ideleSymbol_mul hθ0, hz' v, mul_one, ideleSymbol_unitEmbedding]
  rw [hset]
  exact HN.hilbert_product_formula_nf _ _ α.ne_zero hθ0

/-- **Sufficiency** (O'Meara 1963, proof of 71:19, p. 203: $P_F N_{E/F}J_E$ is the whole kernel of $\varphi$): an
idèle $i$ for which the set of spots with $(i_\mathfrak p, \theta)_\mathfrak p = -1$ is finite of even cardinality lies
in $P_F N_{E/F} J_E$. O'Meara obtains this from the index $(J_F : P_F N_{E/F} J_E) = 2$ (65:21); here it comes from the
existence of an $\alpha \in F$ with the prescribed symbols $(\alpha, \theta)_\mathfrak p = (i_\mathfrak p,
\theta)_\mathfrak p$ (`PresNF.exists_prescribed_hilbert`), so that $\alpha^{-1} i$ is a local norm everywhere. -/
theorem mem_of_ideleSymbol_finite_even {i : J} (h1 : {v : NFPlace F | ideleSymbol θ i v = -1}.Finite)
    (h2 : Even {v : NFPlace F | ideleSymbol θ i v = -1}.ncard) : i ∈ principalNormIdeles E := by
  have hθ0 := ne_zero_of_not_isSquare hθ
  obtain ⟨α, hα, hαv⟩ := PresNF.exists_prescribed_hilbert (ι := Unit) (fun _ => θ) (fun _ => hθ0)
    (fun _ v => ideleSymbol θ i v) (fun _ v => ideleSymbol_pm θ i v) (by simpa using h1) (fun _ => h2)
    (by
      intro v
      cases v with
      | finite v =>
        exact ⟨ideleAt i v, ideleAt_ne_zero i v, fun _ => hilbertSymbol_comm _ _ _⟩
      | infinite w =>
        exact ⟨ideleAtInf i w, ideleAtInf_ne_zero i w, fun _ => hilbertSymbol_comm _ _ _⟩)
  set a : J := IdeleGroup.unitEmbedding (𝓞 F) F (Units.mk0 α hα)
  have hn : a⁻¹ * i ∈ normIdeles E := by
    rw [mem_normIdeles_iff hθ hs hspan]
    intro v
    rw [ideleSymbol_mul hθ0, ideleSymbol_inv hθ0, ideleSymbol_unitEmbedding, Units.val_mk0,
      NFPlace_hilbert_comm, hαv () v]
    rcases ideleSymbol_pm θ i v with h | h <;> rw [h] <;> norm_num
  have : i = a * (a⁻¹ * i) := by group
  rw [this]
  exact Subgroup.mul_mem_sup ⟨_, rfl⟩ hn

/-- **The group $P_F N_{E/F} J_E$ as the kernel of $\varphi$** (O'Meara 1963, proof of 71:19, p. 203, with
$\varphi(i) = \prod_\mathfrak p (i_\mathfrak p, \theta)_\mathfrak p$): an idèle $i$ lies in $P_F N_{E/F} J_E$ if and
only if the set of spots with $(i_\mathfrak p, \theta)_\mathfrak p = -1$ is finite and of even cardinality. -/
@[kb "omeara1963" "§71D, proof of 71:19, p. 203 (P_F N_{E/F}J_E is the kernel of φ)"]
theorem mem_principalNormIdeles_iff (i : J) :
    i ∈ principalNormIdeles E ↔
      {v : NFPlace F | ideleSymbol θ i v = -1}.Finite ∧ Even {v : NFPlace F | ideleSymbol θ i v = -1}.ncard :=
  ⟨ideleSymbol_finite_even_of_mem hθ hs hspan,
    fun h => mem_of_ideleSymbol_finite_even hθ hs hspan h.1 h.2⟩

omit hθ hs hspan in
theorem ideleSymbol_ofAdic (q : HeightOneSpectrum (𝓞 F)) (x : (q.adicCompletion F)ˣ) (v : NFPlace F) :
    ideleSymbol θ (IdeleGroup.ofAdicCompletion (𝓞 F) F q x) v =
      if v = .finite q then hilbertSymbol (q.adicCompletion F) (x : q.adicCompletion F) (algebraMap F _ θ)
      else 1 := by
  cases v with
  | finite v =>
    by_cases h : v = q
    · subst h
      simp only [↓reduceIte]
      show hilbertSymbol _ (ideleAt _ v) _ = _
      rw [ideleAt_ofAdic_self]
    · rw [if_neg (by simpa using h)]
      show hilbertSymbol _ (ideleAt _ v) _ = _
      rw [ideleAt_ofAdic_ne q v h, hilbertSymbol_comm, hilbertSymbol_one_right]
  | infinite w =>
    rw [if_neg (by simp)]
    show hilbertSymbol _ (ideleAtInf _ w) _ = _
    rw [ideleAtInf_ofAdic, hilbertSymbol_comm, hilbertSymbol_one_right]

/-- **Propositions 71:12 and 71:17** (O'Meara 1963, pp. 195, 201), general form: for a discrete spot $\mathfrak q$,
$I_\mathfrak q \subseteq P_F N_{E/F} J_E$ if and only if $E/F$ has local degree $1$ at $\mathfrak q$, i.e. $\theta$ is a
square in $F_\mathfrak q$. *Update*: O'Meara assumes in 71:12 that $E/F$ is $m$-cyclotomic with $m$ a unit at $\mathfrak q$, and in
71:17 that $E/F$ is unramified at $\mathfrak q$; neither hypothesis is needed here, because the proof uses Hilbert's
reciprocity law (proved in the library by the Weil index) where O'Meara proves 71:12 and 71:17 on the way to it. -/
@[kb "omeara1963" "§71B, 71:12, p. 195 (without the cyclotomic hypothesis); §71C, 71:17, p. 201 (without the unramified hypothesis)"]
theorem ideleSupportedAt_le_principalNormIdeles_iff (q : HeightOneSpectrum (𝓞 F)) :
    ideleSupportedAt q ≤ principalNormIdeles E ↔ IsSquare (algebraMap F (q.adicCompletion F) θ) := by
  have hθ0 := ne_zero_of_not_isSquare hθ
  constructor
  · intro hle
    by_contra hns
    obtain ⟨x, hx0, hx⟩ := (HasseIsoNF.localHilbertField_adicCompletion q).exists_neg_one _
      ((map_ne_zero _).mpr hθ0) hns
    have hmem := hle ⟨Units.mk0 x hx0, rfl⟩
    obtain ⟨-, heven⟩ := ideleSymbol_finite_even_of_mem hθ hs hspan hmem
    have hset : {v : NFPlace F |
        ideleSymbol θ (IdeleGroup.ofAdicCompletion (𝓞 F) F q (Units.mk0 x hx0)) v = -1} = {.finite q} := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, ideleSymbol_ofAdic, Units.val_mk0]
      split_ifs with h
      · rw [hilbertSymbol_comm, hx]; simp [h]
      · simp [h]
    rw [hset, Set.ncard_singleton] at heven
    exact absurd heven (by decide)
  · rintro hsq i ⟨x, rfl⟩
    apply Subgroup.mem_sup_right
    rw [mem_normIdeles_iff hθ hs hspan]
    intro v
    rw [ideleSymbol_ofAdic]
    split_ifs
    · exact PadicClass.hs_of_isSquare _ _ ((map_ne_zero _).mpr hθ0) hsq
    · rfl

/-- **Proposition 71:16** (O'Meara 1963, p. 198): let $\mathfrak p_1$, $\mathfrak p_2$ be discrete spots and let
$i_1 \in I_{\mathfrak p_1} - N_{E/F}J_E$, $i_2 \in I_{\mathfrak p_2} - N_{E/F}J_E$. Then
$i_1 i_2 \in P_F N_{E/F} J_E$. *Update*: O'Meara assumes that $E/F$ is unramified of local degree $2$ at $\mathfrak p_1$ and
$\mathfrak p_2$ and proves this by the ten-field construction; those hypotheses are not needed here (the proof uses the
kernel description `mem_principalNormIdeles_iff`, i.e. Hilbert's reciprocity law). -/
@[kb "omeara1963" "§71C, 71:16, p. 198 (without the hypotheses on the local degree and ramification)"]
theorem mul_mem_principalNormIdeles (p₁ p₂ : HeightOneSpectrum (𝓞 F)) {i₁ i₂ : J}
    (hi₁ : i₁ ∈ ideleSupportedAt p₁) (hn₁ : i₁ ∉ normIdeles E)
    (hi₂ : i₂ ∈ ideleSupportedAt p₂) (hn₂ : i₂ ∉ normIdeles E) :
    i₁ * i₂ ∈ principalNormIdeles E := by
  classical
  have hθ0 := ne_zero_of_not_isSquare hθ
  obtain ⟨x₁, rfl⟩ := hi₁
  obtain ⟨x₂, rfl⟩ := hi₂
  -- the symbol of `iₖ` is `-1` exactly at `pₖ`
  have key : ∀ (p : HeightOneSpectrum (𝓞 F)) (x : (p.adicCompletion F)ˣ),
      IdeleGroup.ofAdicCompletion (𝓞 F) F p x ∉ normIdeles E →
      ∀ v, ideleSymbol θ (IdeleGroup.ofAdicCompletion (𝓞 F) F p x) v = if v = .finite p then -1 else 1 := by
    intro p x hn v
    rw [ideleSymbol_ofAdic]
    split_ifs with h
    · rcases HN.hilbertSymbol_eq_one_or (p.adicCompletion F) (x : p.adicCompletion F) (algebraMap F _ θ)
        with h' | h'
      · exfalso
        apply hn
        rw [mem_normIdeles_iff hθ hs hspan]
        intro v'
        rw [ideleSymbol_ofAdic]
        split_ifs
        · exact h'
        · rfl
      · exact h'
    · rfl
  have hprod : ∀ v, ideleSymbol θ (IdeleGroup.ofAdicCompletion (𝓞 F) F p₁ x₁ *
      IdeleGroup.ofAdicCompletion (𝓞 F) F p₂ x₂) v =
      (if v = .finite p₁ then -1 else 1) * (if v = .finite p₂ then -1 else 1) := by
    intro v
    rw [ideleSymbol_mul hθ0, key p₁ x₁ hn₁, key p₂ x₂ hn₂]
  apply mem_of_ideleSymbol_finite_even hθ hs hspan
  · refine (Set.toFinite ({.finite p₁, .finite p₂} : Set (NFPlace F))).subset ?_
    intro v hv
    simp only [Set.mem_ofPred_eq, hprod] at hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hc
    push Not at hc
    rw [if_neg hc.1, if_neg hc.2] at hv
    norm_num at hv
  · by_cases h12 : p₁ = p₂
    · subst h12
      have : {v : NFPlace F | ideleSymbol θ (IdeleGroup.ofAdicCompletion (𝓞 F) F p₁ x₁ *
          IdeleGroup.ofAdicCompletion (𝓞 F) F p₁ x₂) v = -1} = ∅ := by
        ext v
        simp only [Set.mem_ofPred_eq, hprod, Set.mem_empty_iff_false, iff_false]
        split_ifs <;> norm_num
      rw [this, Set.ncard_empty]
      exact ⟨0, rfl⟩
    · have hne : (NFPlace.finite p₁ : NFPlace F) ≠ .finite p₂ := by simpa using h12
      have : {v : NFPlace F | ideleSymbol θ (IdeleGroup.ofAdicCompletion (𝓞 F) F p₁ x₁ *
          IdeleGroup.ofAdicCompletion (𝓞 F) F p₂ x₂) v = -1} = {.finite p₁, .finite p₂} := by
        ext v
        simp only [Set.mem_ofPred_eq, hprod, Set.mem_insert_iff, Set.mem_singleton_iff]
        by_cases h1 : v = .finite p₁
        · subst h1
          simp [hne]
        · by_cases h2 : v = .finite p₂
          · subst h2
            simp [h1]
          · simp [h1, h2]
      rw [this, Set.ncard_pair hne]
      exact even_two

end Kernel

/-- **Proposition 71:12** (O'Meara 1963, p. 195), with O'Meara's hypotheses: if the quadratic extension
$E = F(\sqrt\theta)$ is $m$-cyclotomic (`IsMCyclotomic`, Definition 71:2) and $m$ is a unit at the discrete spot
$\mathfrak q$, then $I_\mathfrak q \subseteq P_F N_{E/F} J_E$ if and only if $E/F$ has local degree $1$ at
$\mathfrak q$ ($\theta$ is a square in $F_\mathfrak q$). The two hypotheses are not used: this is the special case of
`ideleSupportedAt_le_principalNormIdeles_iff`. -/
@[kb "omeara1963" "§71B, 71:12, p. 195"]
theorem ideleSupportedAt_le_principalNormIdeles_of_cyclotomic {E : Type} [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] {θ : F} (hθ : ¬ IsSquare θ) {s : E} (hs : s ^ 2 = algebraMap F E θ)
    (hspan : ∀ y : E, ∃ b₀ b₁ : F, y = algebraMap F E b₀ + algebraMap F E b₁ * s) (m : ℕ)
    (_hcyc : IsMCyclotomic m F E) (q : HeightOneSpectrum (𝓞 F)) (_hm : (m : 𝓞 F) ∉ q.asIdeal) :
    ideleSupportedAt q ≤ principalNormIdeles E ↔ IsSquare (algebraMap F (q.adicCompletion F) θ) :=
  ideleSupportedAt_le_principalNormIdeles_iff hθ hs hspan q

/-- **Proposition 71:13** (O'Meara 1963, p. 196): if $\alpha \in \dot F$ has $(\alpha, -1)_\mathfrak p = 1$ at every
discrete spot $\mathfrak p$, then $\prod_{\mathfrak p \in \Omega_\infty} (\alpha, -1)_\mathfrak p = 1$, the product over
the infinite spots (the complex spots contribute $1$). O'Meara proves this by the Frobenius automorphisms of
$F(\sqrt{-1})/F$ (Formulas 71:10, 71:11) on the way to Hilbert's reciprocity law; here it is the product form of
`even_card_infinite_hilbert_neg_one` (`Sec71B.lean`), a special case of the reciprocity law proved by the Weil index. *Clarification:* the displayed product is lost in the
machine-read text and is reconstructed from the end of the proof ($\alpha$ is negative at a real spot if and only if
$(\alpha, -1)_\mathfrak p = -1$, and the number of such spots is even). -/
@[kb "omeara1963" "§71B, 71:13, p. 196"]
theorem prod_infinite_hilbert_neg_one {α : F} (hα : α ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), (NFPlace.finite v).hilbert α (-1) = 1) :
    ∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert α (-1) = 1 := by
  classical
  have heven := even_card_infinite_hilbert_neg_one α hα h
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred] at heven
  have hpm : ∀ w : InfinitePlace F, (NFPlace.infinite w).hilbert α (-1) =
      if (NFPlace.infinite w).hilbert α (-1) = -1 then -1 else 1 := by
    intro w
    have h' : (NFPlace.infinite w).hilbert α (-1) = 1 ∨ (NFPlace.infinite w).hilbert α (-1) = -1 :=
      HN.hilbertSymbol_eq_one_or _ _ _
    rcases h' with h' | h' <;> rw [h'] <;> norm_num
  rw [Finset.prod_congr rfl (fun w _ => hpm w), Finset.prod_ite, Finset.prod_const, Finset.prod_const_one,
    mul_one]
  exact heven.neg_one_pow

end QuadFormsKB.OMeara
