import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelForms

/-!
# Binary lattices of type $E$ over $\mathcal O_F$ and ideal classes of $E$

Let $E/F$ be a quadratic extension of number fields, $\sigma$ its nontrivial automorphism and $N = N_{E/F}$. A nonzero
ideal $\mathfrak A \subseteq \mathcal O_E$ is an $\mathcal O_F$-lattice of rank $2$ in the $F$-space $E$ (`idealLat F 𝔄`; it is
projective, $\cong \mathcal O_F \oplus \mathfrak a$, and in general not free), and $(\mathfrak A, cN)$ is a binary
$\mathcal O_F$-lattice for every $c \in F^\times$. This file classifies these lattices by ideal classes.

* **Isometry** (`isometricLattices_ideal_iff`): $(\mathfrak A, cN) \cong (\mathfrak B, c'N)$ iff
  $\mathfrak B = \lambda\mathfrak A$ or $\mathfrak B = \lambda\,\sigma(\mathfrak A)$ for some $\lambda \in E^\times$ with
  $c'\,N(\lambda) = c$ (from `isometricLattices_iff`).
* **Ideal classes** (`exists_smulLat_iff`): $\mathfrak B = \lambda\mathfrak A$ for some $\lambda \in E^\times$ iff
  $[\mathfrak A] = [\mathfrak B]$ in $\mathrm{Cl}_E$ (Mathlib's `ClassGroup (𝓞 E)`).
* **Similarity classes ↔ $\mathrm{Cl}_E$ up to conjugation** (`isSimilarLat_ideal_iff`, the convention of this repository: a class and
  its conjugate): $(\mathfrak A, N)$ and $(\mathfrak B, N)$ are similar (isometric after scaling the form by some
  $a \in F^\times$) iff $[\mathfrak B] = [\mathfrak A]$ or $[\mathfrak B] = \sigma_*[\mathfrak A]$, $\sigma_*$ = `conjClass`.
* **Conjugation is inversion modulo the classes of $F$** (`mul_conjIdeal`, `mul_conjClass`, `conjClass_eq_inv_mod`):
  $\mathfrak A\,\sigma(\mathfrak A) = N_{E/F}(\mathfrak A)\,\mathcal O_E$, so $[\mathfrak A]\,\sigma_*[\mathfrak A] = \iota[N_{E/F}\mathfrak A]$
  with $\iota : \mathrm{Cl}_F \to \mathrm{Cl}_E$ the extension map (Mathlib's `ClassGroup.extendedHom`), and in
  $\mathrm{Cl}_E/\iota(\mathrm{Cl}_F)$ the conjugate class is the inverse class. Over $F = \mathbb Q$ ($\mathrm{Cl}_\mathbb Q = 1$) this is
  `idealClass_conj`: $[\mathfrak a_{\bar f}] = [\mathfrak a_f]^{-1}$.

Hence: the similarity classes of the lattices $(\mathfrak A, N)$ are $\mathrm{Cl}_E$ modulo $c \sim \sigma_*c$, and modulo the image of
the ideals of $F$ they are $\mathrm{Cl}_E/\iota(\mathrm{Cl}_F)$ modulo $c \sim c^{-1}$ (classes and inverses, as for the GL-classes). The
finer isometry classes (fixing the scale $c$) are counted by the units: see `RelFormAut.lean` and `RelRepCount.lean`.

The proof of $\mathfrak A\sigma(\mathfrak A) = N_{E/F}(\mathfrak A)\mathcal O_E$ uses only principal ideals: for $\mathfrak A^h = (\alpha)$ ($h$ the class
number) both sides have $h$-th power $(\alpha\,\sigma\alpha) = (N\alpha)$, and $h$-th roots of ideals of a Dedekind domain are
unique (`ideal_pow_left_injective`, by unique factorization).

Sources: Shimura, *Arithmetic of Quadratic Forms* (2010), §4 (binary forms over number fields) [unverified locator];
O'Meara §82 (classes of lattices) [unverified]; Cox §7 (the case $F = \mathbb Q$).
-/

open NumberField Module
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

/-- **$n$-th roots of ideals are unique** in a Dedekind domain: $I^n = J^n$, $n \ne 0$ $\Rightarrow$ $I = J$ (compare the
normalized factorizations). -/
theorem ideal_pow_left_injective {R : Type*} [CommRing R] [IsDedekindDomain R] {I J : Ideal R} {n : ℕ}
    (hn : n ≠ 0) (h : I ^ n = J ^ n) : I = J := by
  by_cases hI : I = 0
  · subst hI
    rw [zero_pow hn, eq_comm, pow_eq_zero_iff hn] at h
    exact h.symm
  by_cases hJ : J = 0
  · subst hJ
    rw [zero_pow hn, pow_eq_zero_iff hn] at h
    exact h
  have hf := congrArg UniqueFactorizationMonoid.normalizedFactors h
  rw [UniqueFactorizationMonoid.normalizedFactors_pow, UniqueFactorizationMonoid.normalizedFactors_pow] at hf
  have hm : UniqueFactorizationMonoid.normalizedFactors I = UniqueFactorizationMonoid.normalizedFactors J := by
    ext p
    have := congrArg (Multiset.count p) hf
    rw [Multiset.count_nsmul, Multiset.count_nsmul] at this
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) this
  exact associated_iff_eq.mp
    ((UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors hI hJ).mpr hm)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-! ### Ideal lattices and conjugation -/

variable (F) in
/-- **The ideal lattice** of $\mathfrak A \subseteq \mathcal O_E$: $\mathfrak A$ as an $\mathcal O_F$-submodule of $E$ (an $\mathcal O_F$-lattice of rank $2$
in the $F$-space $E$ when $\mathfrak A \ne 0$; projective, not necessarily free). -/
@[kb "omeara1963" "§81 (lattices) [unverified]"]
def idealLat (𝔄 : Ideal (𝓞 E)) : Submodule (𝓞 F) E :=
  (IsLocalization.coeSubmodule E 𝔄).restrictScalars (𝓞 F)

theorem mem_idealLat {𝔄 : Ideal (𝓞 E)} {x : E} :
    x ∈ idealLat F 𝔄 ↔ ∃ a ∈ 𝔄, algebraMap (𝓞 E) E a = x := by
  rw [idealLat, Submodule.restrictScalars_mem, IsLocalization.mem_coeSubmodule]

theorem algebraMap_mem_idealLat {𝔄 : Ideal (𝓞 E)} {a : 𝓞 E} (ha : a ∈ 𝔄) :
    algebraMap (𝓞 E) E a ∈ idealLat F 𝔄 := mem_idealLat.mpr ⟨a, ha, rfl⟩

variable (F E) in
/-- The conjugation $\sigma$ restricted to $\mathcal O_E$. -/
def conjO : 𝓞 E ≃+* 𝓞 E := (RingOfIntegers.mapAlgEquiv (conj F E)).toRingEquiv

theorem algebraMap_conjO (a : 𝓞 E) :
    algebraMap (𝓞 E) E (conjO F E a) = conj F E (algebraMap (𝓞 E) E a) := rfl

variable (F) in
/-- **The conjugate ideal** $\sigma(\mathfrak A)$. -/
def conjIdeal (𝔄 : Ideal (𝓞 E)) : Ideal (𝓞 E) := 𝔄.map (conjO F E)

theorem conjIdeal_ne_bot {𝔄 : Ideal (𝓞 E)} (h : 𝔄 ≠ ⊥) : conjIdeal F 𝔄 ≠ ⊥ :=
  (Ideal.map_eq_bot_iff_of_injective (conjO F E).injective).not.mpr h

/-- $\sigma(\mathfrak A)$ as a lattice is the conjugate lattice of $\mathfrak A$. -/
theorem conjLat_idealLat (𝔄 : Ideal (𝓞 E)) : conjLat (idealLat F 𝔄) = idealLat F (conjIdeal F 𝔄) := by
  ext x
  rw [mem_conjLat, mem_idealLat]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, ha, rfl⟩ := mem_idealLat.mp hy
    exact ⟨conjO F E a, Ideal.mem_map_of_mem _ ha, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_of_equiv (conjO F E) b).mp hb
    exact ⟨algebraMap _ E a, algebraMap_mem_idealLat ha, rfl⟩

/-! ### Scaling and ideal classes -/

theorem algebraMap_ne_zero {y : 𝓞 E} (hy : y ≠ 0) : algebraMap (𝓞 E) E y ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).mpr hy

/-- $\mathfrak B = (x/y)\,\mathfrak A$ in $E$ iff $(x)\,\mathfrak A = (y)\,\mathfrak B$ as ideals. -/
theorem smulLat_idealLat_iff {x y : 𝓞 E} (hy : y ≠ 0) (𝔄 𝔅 : Ideal (𝓞 E)) :
    idealLat F 𝔅 = smulLat (algebraMap _ E x / algebraMap _ E y) (idealLat F 𝔄) ↔
      Ideal.span {x} * 𝔄 = Ideal.span {y} * 𝔅 := by
  have hy' := algebraMap_ne_zero hy
  have inj := FaithfulSMul.algebraMap_injective (𝓞 E) E
  constructor
  · intro h
    ext z
    rw [Ideal.mem_span_singleton_mul, Ideal.mem_span_singleton_mul]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have hm : algebraMap _ E x / algebraMap _ E y * algebraMap _ E a ∈ idealLat F 𝔅 := by
        rw [h]; exact mem_smulLat.mpr ⟨_, algebraMap_mem_idealLat ha, rfl⟩
      obtain ⟨b, hb, hbe⟩ := mem_idealLat.mp hm
      refine ⟨b, hb, inj ?_⟩
      rw [map_mul, map_mul, hbe]
      field_simp
    · rintro ⟨b, hb, rfl⟩
      have hm : algebraMap _ E b ∈ smulLat (algebraMap _ E x / algebraMap _ E y) (idealLat F 𝔄) :=
        h ▸ algebraMap_mem_idealLat hb
      obtain ⟨w, hw, hwe⟩ := mem_smulLat.mp hm
      obtain ⟨a, ha, rfl⟩ := mem_idealLat.mp hw
      refine ⟨a, ha, inj ?_⟩
      rw [map_mul, map_mul, ← hwe]
      field_simp
  · intro h
    ext z
    rw [mem_idealLat, mem_smulLat]
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hm : y * b ∈ Ideal.span {x} * 𝔄 := h ▸ Ideal.mem_span_singleton_mul.mpr ⟨b, hb, rfl⟩
      obtain ⟨a, ha, hae⟩ := Ideal.mem_span_singleton_mul.mp hm
      refine ⟨algebraMap _ E a, algebraMap_mem_idealLat ha, ?_⟩
      have e := congrArg (algebraMap (𝓞 E) E) hae
      rw [map_mul, map_mul] at e
      field_simp
      linear_combination e
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨a, ha, rfl⟩ := mem_idealLat.mp hw
      have hm : x * a ∈ Ideal.span {y} * 𝔅 := h ▸ Ideal.mem_span_singleton_mul.mpr ⟨a, ha, rfl⟩
      obtain ⟨b, hb, hbe⟩ := Ideal.mem_span_singleton_mul.mp hm
      refine ⟨b, hb, ?_⟩
      have e := congrArg (algebraMap (𝓞 E) E) hbe
      rw [map_mul, map_mul] at e
      field_simp
      linear_combination e

/-- **Scaling classes are ideal classes:** $\mathfrak B = \lambda\mathfrak A$ for some $\lambda \in E^\times$ iff
$[\mathfrak A] = [\mathfrak B]$ in $\mathrm{Cl}_E$. -/
@[kb "neukirch1999" "Ch. I §3 (class group) [unverified]"]
theorem exists_smulLat_iff (𝔄 𝔅 : (Ideal (𝓞 E))⁰) :
    (∃ l : E, l ≠ 0 ∧ idealLat F (𝔅 : Ideal (𝓞 E)) = smulLat l (idealLat F (𝔄 : Ideal (𝓞 E)))) ↔
      ClassGroup.mk0 𝔄 = ClassGroup.mk0 𝔅 := by
  rw [ClassGroup.mk0_eq_mk0_iff]
  constructor
  · rintro ⟨l, hl, h⟩
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) l
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hx0 : x ≠ 0 := by rintro rfl; simp at hl
    exact ⟨x, y, hx0, hy0, (smulLat_idealLat_iff hy0 _ _).mp h⟩
  · rintro ⟨x, y, hx, hy, h⟩
    exact ⟨_, div_ne_zero (algebraMap_ne_zero hx) (algebraMap_ne_zero hy),
      (smulLat_idealLat_iff hy _ _).mpr h⟩

/-! ### Isometry and similarity classes -/

/-- **Isometry of ideal lattices.** For $c, c' \in F^\times$ and nonzero $\mathfrak A, \mathfrak B \subseteq \mathcal O_E$:
$(\mathfrak A, cN) \cong (\mathfrak B, c'N)$ iff $\mathfrak B = \lambda\mathfrak A$ or $\mathfrak B = \lambda\,\sigma(\mathfrak A)$ for some
$\lambda \in E^\times$ with $c'\,N(\lambda) = c$. -/
@[kb "omeara1963" "§82; Shimura (2010) §4 [unverified]"]
theorem isometricLattices_ideal_iff {c c' : F} (hc : c ≠ 0) (hc' : c' ≠ 0) (𝔄 𝔅 : Ideal (𝓞 E)) :
    Lattices.IsometricLattices (c • normForm F E) (c' • normForm F E) (idealLat F 𝔄) (idealLat F 𝔅) ↔
      ∃ l : E, l ≠ 0 ∧ c' * Algebra.norm F l = c ∧
        (idealLat F 𝔅 = smulLat l (idealLat F 𝔄) ∨
          idealLat F 𝔅 = smulLat l (idealLat F (conjIdeal F 𝔄))) := by
  rw [isometricLattices_iff hc hc', conjLat_idealLat]

/-- **Similar lattices:** $(L, Q)$ and $(L', Q)$ are similar if $(L, aQ) \cong (L', Q)$ for some $a \in F^\times$. -/
@[kb "omeara1963" "§82 (similarity of lattices) [unverified]"]
def IsSimilarLat (Q : QuadraticForm F E) (L L' : Submodule (𝓞 F) E) : Prop :=
  ∃ a : F, a ≠ 0 ∧ Lattices.IsometricLattices (a • Q) Q L L'

variable (F E) in
/-- **Conjugation on the class group**, $\sigma_*[\mathfrak A] = [\sigma(\mathfrak A)]$ (Mathlib's `ClassGroup.mulEquiv`). -/
def conjClass : ClassGroup (𝓞 E) ≃* ClassGroup (𝓞 E) := ClassGroup.mulEquiv (conjO F E)

variable (F) in
/-- $\sigma(\mathfrak A)$ as a nonzero ideal. -/
def conjIdeal0 (𝔄 : (Ideal (𝓞 E))⁰) : (Ideal (𝓞 E))⁰ :=
  ⟨conjIdeal F 𝔄, mem_nonZeroDivisors_of_ne_zero (conjIdeal_ne_bot (nonZeroDivisors.coe_ne_zero 𝔄))⟩

theorem conjClass_mk0 (𝔄 : (Ideal (𝓞 E))⁰) :
    conjClass F E (ClassGroup.mk0 𝔄) = ClassGroup.mk0 (conjIdeal0 F 𝔄) := by
  rw [conjClass, ClassGroup.mulEquiv_mk0]
  rfl

/-- **Similarity classes ↔ $\mathrm{Cl}_E$ up to conjugation.** For nonzero $\mathfrak A, \mathfrak B \subseteq \mathcal O_E$, the lattices
$(\mathfrak A, N)$ and $(\mathfrak B, N)$ are similar iff $[\mathfrak B] = [\mathfrak A]$ or $[\mathfrak B] = \sigma_*[\mathfrak A]$. -/
@[kb "omeara1963" "§82; Shimura (2010) §4 [unverified]"]
theorem isSimilarLat_ideal_iff (𝔄 𝔅 : (Ideal (𝓞 E))⁰) :
    IsSimilarLat (normForm F E) (idealLat F (𝔄 : Ideal (𝓞 E))) (idealLat F (𝔅 : Ideal (𝓞 E))) ↔
      ClassGroup.mk0 𝔅 = ClassGroup.mk0 𝔄 ∨ ClassGroup.mk0 𝔅 = conjClass F E (ClassGroup.mk0 𝔄) := by
  rw [conjClass_mk0]
  constructor
  · rintro ⟨a, ha, h⟩
    have h' : Lattices.IsometricLattices (a • normForm F E) ((1 : F) • normForm F E)
        (idealLat F (𝔄 : Ideal (𝓞 E))) (idealLat F (𝔅 : Ideal (𝓞 E))) := by rwa [one_smul]
    obtain ⟨l, hl, -, h1 | h1⟩ := (isometricLattices_ideal_iff ha one_ne_zero _ _).mp h'
    · exact Or.inl ((exists_smulLat_iff 𝔄 𝔅).mp ⟨l, hl, h1⟩).symm
    · exact Or.inr ((exists_smulLat_iff (conjIdeal0 F 𝔄) 𝔅).mp ⟨l, hl, h1⟩).symm
  · intro h
    have key : ∃ l : E, l ≠ 0 ∧ (idealLat F (𝔅 : Ideal (𝓞 E)) = smulLat l (idealLat F (𝔄 : Ideal (𝓞 E))) ∨
        idealLat F (𝔅 : Ideal (𝓞 E)) = smulLat l (idealLat F (conjIdeal F (𝔄 : Ideal (𝓞 E))))) := by
      rcases h with h | h
      · obtain ⟨l, hl, h1⟩ := (exists_smulLat_iff (F := F) 𝔄 𝔅).mpr h.symm
        exact ⟨l, hl, Or.inl h1⟩
      · obtain ⟨l, hl, h1⟩ := (exists_smulLat_iff (F := F) (conjIdeal0 F 𝔄) 𝔅).mpr h.symm
        exact ⟨l, hl, Or.inr h1⟩
    obtain ⟨l, hl, h1⟩ := key
    have hNl : Algebra.norm F l ≠ 0 := Algebra.norm_ne_zero_iff.mpr hl
    refine ⟨Algebra.norm F l, hNl, ?_⟩
    have := (isometricLattices_ideal_iff hNl one_ne_zero (𝔄 : Ideal (𝓞 E)) 𝔅).mpr ⟨l, hl, one_mul _, h1⟩
    rwa [one_smul] at this

/-! ### $\mathfrak A\,\sigma(\mathfrak A) = N_{E/F}(\mathfrak A)\,\mathcal O_E$ -/

/-- $N_{E/F}(\alpha) = \alpha\,\sigma(\alpha)$ in $\mathcal O_E$, for Mathlib's integral norm `Algebra.intNorm`. -/
theorem algebraMap_intNorm_eq (α : 𝓞 E) :
    algebraMap (𝓞 F) (𝓞 E) (Algebra.intNorm (𝓞 F) (𝓞 E) α) = α * conjO F E α := by
  apply FaithfulSMul.algebraMap_injective (𝓞 E) E
  rw [map_mul, algebraMap_conjO, ← algebraMap_norm, ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E,
    IsScalarTower.algebraMap_apply (𝓞 F) F E, Algebra.algebraMap_intNorm (L := E)]

theorem mul_conjIdeal_span (α : 𝓞 E) :
    Ideal.span {α} * conjIdeal F (Ideal.span {α}) =
      (Ideal.relNorm (𝓞 F) (Ideal.span {α})).map (algebraMap (𝓞 F) (𝓞 E)) := by
  rw [conjIdeal, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_mul_span_singleton,
    Ideal.relNorm_singleton, Ideal.map_span, Set.image_singleton, algebraMap_intNorm_eq]

/-- **$\mathfrak A\,\sigma(\mathfrak A) = N_{E/F}(\mathfrak A)\,\mathcal O_E$** for every ideal $\mathfrak A$ of $\mathcal O_E$
($N_{E/F}$ = Mathlib's `Ideal.relNorm`). -/
@[kb "neukirch1999" "Ch. I §8 [unverified]"]
theorem mul_conjIdeal (𝔄 : Ideal (𝓞 E)) :
    𝔄 * conjIdeal F 𝔄 = (Ideal.relNorm (𝓞 F) 𝔄).map (algebraMap (𝓞 F) (𝓞 E)) := by
  by_cases h0 : 𝔄 = ⊥
  · subst h0
    simp [conjIdeal]
  set n := Fintype.card (ClassGroup (𝓞 E))
  have hn : n ≠ 0 := Fintype.card_ne_zero
  have hmem : 𝔄 ∈ (Ideal (𝓞 E))⁰ := mem_nonZeroDivisors_of_ne_zero h0
  have hp : (𝔄 ^ n).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hmem n)]
    have : ClassGroup.mk0 (⟨𝔄, hmem⟩ ^ n) = 1 := by rw [map_pow, pow_card_eq_one]
    simpa using this
  obtain ⟨α, hα⟩ := hp
  refine ideal_pow_left_injective hn ?_
  rw [mul_pow, conjIdeal, ← Ideal.map_pow, ← conjIdeal, ← Ideal.map_pow, ← map_pow,
    hα]
  exact mul_conjIdeal_span α

/-- **The conjugate class times the class is extended from $F$:**
$[\mathfrak A]\cdot\sigma_*[\mathfrak A] = \iota\,[N_{E/F}\mathfrak A]$, $\iota : \mathrm{Cl}_F \to \mathrm{Cl}_E$ (`ClassGroup.extendedHom`). -/
@[kb "neukirch1999" "Ch. I §8 [unverified]"]
theorem mul_conjClass (𝔄 : (Ideal (𝓞 E))⁰) :
    ∃ 𝔞 : (Ideal (𝓞 F))⁰, ClassGroup.mk0 𝔄 * conjClass F E (ClassGroup.mk0 𝔄) =
      ClassGroup.extendedHom (𝓞 F) (𝓞 E) (ClassGroup.mk0 𝔞) := by
  have h0 : Ideal.relNorm (𝓞 F) (𝔄 : Ideal (𝓞 E)) ≠ ⊥ :=
    (Ideal.relNorm_eq_bot_iff).not.mpr (nonZeroDivisors.coe_ne_zero 𝔄)
  refine ⟨⟨_, mem_nonZeroDivisors_of_ne_zero h0⟩, ?_⟩
  rw [ClassGroup.extendedHom_mk0, conjClass_mk0, ← map_mul]
  congr 1
  ext1
  exact mul_conjIdeal (𝔄 : Ideal (𝓞 E))

/-- **Modulo the classes of $F$, conjugation is inversion:** in $\mathrm{Cl}_E/\iota(\mathrm{Cl}_F)$,
$\sigma_*c = c^{-1}$ for every class $c$. -/
@[kb "neukirch1999" "Ch. I §8 [unverified]"]
theorem conjClass_eq_inv_mod (c : ClassGroup (𝓞 E)) :
    (QuotientGroup.mk (conjClass F E c) : ClassGroup (𝓞 E) ⧸ (ClassGroup.extendedHom (𝓞 F) (𝓞 E)).range) =
      (QuotientGroup.mk c)⁻¹ := by
  obtain ⟨𝔄, rfl⟩ := ClassGroup.mk0_surjective c
  obtain ⟨𝔞, h⟩ := mul_conjClass (F := F) 𝔄
  rw [eq_inv_iff_mul_eq_one, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mul_comm, h]
  exact ⟨_, rfl⟩

end QuadFormsKB.Binary.Rel
