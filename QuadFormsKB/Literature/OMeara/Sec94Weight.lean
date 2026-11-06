/-
# O'Meara §94: the weight from a base

**Setting** (as in `Sec93Gap2.lean`): $R$ a Henselian discrete valuation ring with finite residue field (O'Meara's
$\mathfrak o$), $F$ its fraction field, $2 \in F^\times$, $F$ *dyadic* ($2$ not a unit of $R$); a quadratic space
$(V, Q)$ over $F$, lattices = `Submodule R V`; $\mathfrak sL$ = `scale Q L`, $\mathfrak wL$ = `weight Q L`, a norm
generator $a$ (`IsNormGenerator Q L a`), the quadratic defect $\mathfrak d$ (`quadDefect R`, §63A).

**Proves** the weight formula of §94 (O'Meara 1973 printing, p. 280; "We leave the verification of this formula to
the reader"; the machine-read text garbled the formula, the page image reads
$\mathfrak w = \sum_j a\,\mathfrak d(Q(x_j)/a) + 2(\mathfrak sL)$): for a base $x_1, \dots, x_n$ of $L$ and a norm
generator $a$,
$$\mathfrak wL = \sum_j a\,\mathfrak d\big(Q(x_j)/a\big) + 2\,\mathfrak sL$$
(`weight_eq_sum_quadDefect`). The verification: $\supseteq$ from 93:4 ($\mathfrak gL = a\mathfrak o^2 + \mathfrak wL$);
$\subseteq$ from 93:5 (`G93.weight_eq_sup`): a value $Q(y) = Q(\sum c_jx_j)$ of order of parity opposite to
$\operatorname{ord} a$ is $\equiv \sum_j c_j^2Q(x_j) \equiv a\eta^2 \bmod \sum_j a\,\mathfrak d(Q(x_j)/a) + 2\mathfrak sL$
($Q(x_j) = a\eta_j^2 + a\delta_j$ with $\delta_j\mathfrak o = \mathfrak d(Q(x_j)/a)$, $\eta = \sum c_j\eta_j$), and
$\operatorname{ord} Q(y) \ne \operatorname{ord} a\eta^2$ gives $Q(y)$ in that ideal by the Principle of Domination.
-/
import QuadFormsKB.Literature.OMeara.Sec93Gap2

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

namespace W94

/-- Twice an element of the scale lies in `2 • 𝔰L`. -/
lemma two_mul_mem {L : Submodule R V} {c : F} (hc : c ∈ scale Q L) : 2 * c ∈ (2 : F) • scale Q L :=
  Submodule.smul_mem_pointwise_smul _ (2 : F) _ hc

/-- For `q ∈ a𝔬` there is `e ∈ 𝔬` with `q - a e² ∈ a 𝔡(q / a)`. -/
lemma exists_defect (h2 : (2 : R) ≠ 0) {a q : F} (ha : a ≠ 0) (hq : q ∈ R ∙ a) :
    ∃ e : R, q - a * algebraMap R F e ^ 2 ∈ a • quadDefect R (q / a) := by
  obtain ⟨r, rfl⟩ := mem_span_singleton.mp hq
  have hξ : (r • a) / a = algebraMap R F r := by rw [Algebra.smul_def]; field_simp
  rw [hξ]
  obtain ⟨η, hη⟩ := exists_quadDefect_eq h2 (algebraMap R F r)
  have hδ : algebraMap R F r - η ^ 2 ∈ quadDefect R (algebraMap R F r) :=
    hη ▸ mem_span_singleton_self _
  obtain ⟨s, hs⟩ := mem_span_singleton.mp (quadDefect_le_span _ hδ)
  have hη2 : η ^ 2 = algebraMap R F (r - s * r) := by
    rw [map_sub, map_mul]; rw [Algebra.smul_def] at hs; linear_combination hs
  obtain ⟨e, he⟩ := exists_alg_of_sq hη2
  refine ⟨e, ?_⟩
  rw [Submodule.mem_smul_pointwise_iff_exists]
  refine ⟨algebraMap R F r - η ^ 2, hδ, ?_⟩
  rw [smul_eq_mul, he, Algebra.smul_def]; ring

/-- If `y` has order of parity opposite to `a` and `w ≠ 0`, then `y ∈ (y - a w²)𝔬`. -/
lemma mem_span_of_odd {π : R} (hπ : Irreducible π) {a w y : F} (ha : a ≠ 0) (hw : w ≠ 0) (hy : y ≠ 0)
    (hodd : Odd (dord hπ y - dord hπ a)) : y ∈ span R {y - a * w ^ 2} := by
  have h1 : a * w ^ 2 ≠ 0 := mul_ne_zero ha (pow_ne_zero 2 hw)
  have hd : dord hπ (a * w ^ 2) = dord hπ a + 2 * dord hπ w := by
    rw [dord_mul hπ ha (pow_ne_zero 2 hw), dord_sq hπ hw]
  have hne : dord hπ y ≠ dord hπ (a * w ^ 2) := by
    rw [hd]; obtain ⟨k, hk⟩ := hodd; omega
  have hs : y - a * w ^ 2 ≠ 0 := fun h => hne (by rw [sub_eq_zero.mp h])
  rw [mem_span_iff hπ hy hs]
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := dord_add_of_lt hπ hy (neg_ne_zero.mpr h1) (by rwa [← sub_eq_add_neg])
      (by rwa [dord_neg hπ h1])
    rw [← sub_eq_add_neg] at this; omega
  · have := dord_add_of_lt hπ (neg_ne_zero.mpr h1) hy (by rw [neg_add_eq_sub]; exact hs)
      (by rw [dord_neg hπ h1]; exact hlt)
    rw [neg_add_eq_sub, dord_neg hπ h1] at this; omega

/-- `Q(∑ cᵢxᵢ) ≡ a (∑ cᵢeᵢ)² + ∑ cᵢ²(Q xᵢ - a eᵢ²)` modulo `2 • 𝔰L`, for `a ∈ 𝔰L`. -/
lemma approx {L : Submodule R V} {a : F} (ha : a ∈ scale Q L) {ι : Type*} (x : ι → V) (hx : ∀ i, x i ∈ L)
    (c e : ι → R) (s : Finset ι) :
    Q (∑ i ∈ s, c i • x i) - a * algebraMap R F (∑ i ∈ s, c i * e i) ^ 2
      - ∑ i ∈ s, algebraMap R F (c i) ^ 2 * (Q (x i) - a * algebraMap R F (e i) ^ 2)
      ∈ (2 : F) • scale Q L := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    have hu : ∑ i ∈ s, c i • x i ∈ L := sum_mem fun i _ => L.smul_mem _ (hx i)
    have hck : c k • x k ∈ L := L.smul_mem _ (hx k)
    have h1 : bil Q (c k • x k) (∑ i ∈ s, c i • x i) ∈ scale Q L := bil_mem_scale Q hck hu
    have h2 : a * algebraMap R F (c k * e k * ∑ i ∈ s, c i * e i) ∈ scale Q L := by
      rw [mul_comm, ← Algebra.smul_def]; exact (scale Q L).smul_mem _ ha
    have key := add_mem ih (two_mul_mem Q (sub_mem h1 h2))
    convert key using 1
    rw [Q_add, Q_rsmul]
    simp only [map_add, map_mul]
    ring

end W94

/-- **The weight from a base** (O'Meara 1973, §94, p. 280): over a dyadic local field, let $L$ be a non-zero regular
lattice with base $x_1, \dots, x_n$ (`b : Basis ι R L`) and norm generator $a$. Then
$\mathfrak wL = \sum_j a\,\mathfrak d(Q(x_j)/a) + 2(\mathfrak sL)$. -/
@[kb "omeara1963" "§94, p. 280 (w = Σ_j a d(Q(x_j)/a) + 2(sL))"]
theorem weight_eq_sum_quadDefect (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hreg : IsRegular Q L)
    (hne : L ≠ ⊥) {ι : Type*} [Fintype ι] (b : Basis ι R L) {a : F} (ha : IsNormGenerator Q L a) :
    weight Q L = (⨆ j, a • quadDefect R (Q (b j : V) / a)) ⊔ (2 : F) • scale Q L := by
  classical
  have ha0 : a ≠ 0 := ha.ne_zero Q hreg hne
  have h2 : (2 : R) ≠ 0 := two_ne_zero_R (F := F)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨S0, hS0⟩ : ∃ S0 : Submodule R F, S0 = ⨆ j, a • quadDefect R (Q (b j : V) / a) := ⟨_, rfl⟩
  rw [← hS0]
  have haL : a ∈ scale Q L := normIdeal_le_scale Q L (ha.2 ▸ mem_span_singleton_self a)
  have hxj : ∀ j, Q (b j : V) ∈ R ∙ a := fun j => ha.2 ▸ Q_mem_normIdeal Q (b j).2
  have hle : ∀ j, a • quadDefect R (Q (b j : V) / a) ≤ S0 := fun j => by
    rw [hS0]; exact le_iSup (fun j => a • quadDefect R (Q (b j : V) / a)) j
  have hS0w : S0 ≤ weight Q L := by
    rw [hS0]
    refine iSup_le fun j => ?_
    intro z hz
    rw [Submodule.mem_smul_pointwise_iff_exists] at hz
    obtain ⟨d, hd, rfl⟩ := hz
    obtain ⟨ε, hε⟩ := exists_sub_sq_mem_weight Q h2p ha ha0 (Q_mem_normGroup Q (b j).2)
    have hd' : d ∈ span R {Q (b j : V) / a - algebraMap R F ε ^ 2} :=
      (iInf_le (fun η : F => span R {Q (b j : V) / a - η ^ 2}) (algebraMap R F ε)) hd
    obtain ⟨r, hr⟩ := mem_span_singleton.mp hd'
    have : a • d = r • (Q (b j : V) - a * algebraMap R F ε ^ 2) := by
      rw [← hr, smul_eq_mul, Algebra.smul_def, Algebra.smul_def]; field_simp
    rw [this]; exact (weight Q L).smul_mem r hε
  have hSw : S0 ⊔ (2 : F) • scale Q L ≤ weight Q L := sup_le hS0w (weight_bounds Q L).2.2.1
  have hS : ∀ y ∈ L, Q y ≠ 0 → Odd (dord hπ (Q y) - dord hπ a) → Q y ∈ S0 ⊔ (2 : F) • scale Q L := by
    intro y hy hQ hodd
    obtain ⟨c, hy'⟩ : ∃ c : ι → R, y = ∑ j, c j • (b j : V) := by
      refine ⟨fun j => b.repr ⟨y, hy⟩ j, ?_⟩
      have := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have hE : ∀ j, ∃ e : R, Q (b j : V) - a * algebraMap R F e ^ 2 ∈ a • quadDefect R (Q (b j : V) / a) :=
      fun j => W94.exists_defect h2 ha0 (hxj j)
    choose e he using hE
    have hap := W94.approx Q haL (fun j => (b j : V)) (fun j => (b j).2) c e Finset.univ
    have hT : ∑ j, algebraMap R F (c j) ^ 2 * (Q (b j : V) - a * algebraMap R F (e j) ^ 2) ∈ S0 := by
      refine sum_mem fun j _ => ?_
      have h3 : algebraMap R F (c j) ^ 2 * (Q (b j : V) - a * algebraMap R F (e j) ^ 2)
          = (c j ^ 2) • (Q (b j : V) - a * algebraMap R F (e j) ^ 2) := by
        rw [Algebra.smul_def, map_pow]
      rw [h3]
      exact hle j (Submodule.smul_mem _ _ (he j))
    subst hy'
    have hs : Q (∑ j, c j • (b j : V)) - a * algebraMap R F (∑ j, c j * e j) ^ 2 ∈
        S0 ⊔ (2 : F) • scale Q L := by
      have h4 : Q (∑ j, c j • (b j : V)) - a * algebraMap R F (∑ j, c j * e j) ^ 2
          = (Q (∑ j, c j • (b j : V)) - a * algebraMap R F (∑ j, c j * e j) ^ 2
            - ∑ j, algebraMap R F (c j) ^ 2 * (Q (b j : V) - a * algebraMap R F (e j) ^ 2))
            + ∑ j, algebraMap R F (c j) ^ 2 * (Q (b j : V) - a * algebraMap R F (e j) ^ 2) := by ring
      rw [h4]
      exact add_mem (mem_sup_right hap) (mem_sup_left hT)
    by_cases h0 : ∑ j, c j * e j = 0
    · rw [h0] at hs; simpa using hs
    · have hw : algebraMap R F (∑ j, c j * e j) ≠ 0 := (map_ne_zero_iff _ alg_inj).2 h0
      exact (span_singleton_le_iff_mem _ _).mpr hs (W94.mem_span_of_odd hπ ha0 hw hQ hodd)
  have hfin := weight_eq_sup Q h2p hπ ha ha0 hSw hS
  rw [hfin, sup_assoc, sup_idem]

/-- **The fundamental invariants by the same procedure** (O'Meara 1973, §94, p. 280: "In order to find the
fundamental invariants $a_1, \dots, a_t$ and $\mathfrak w_1, \dots, \mathfrak w_t$ we apply this procedure to each of
the lattices $L^{\mathfrak s_1}, \dots, L^{\mathfrak s_t}$"): for lattices $L_1, \dots, L_t$ (the components of a
Jordan splitting of $L$, whose $L^{\mathfrak s_i}$ is given by `subA_scale_isOrthSplit`), a base $y_1, \dots, y_m$ of
$L^{\mathfrak s_i}$ and a norm generator $a_i$ of $L^{\mathfrak s_i}$ (a fundamental norm generator, found by
`isNormGenerator_of_eq_two_scale` or `isNormGenerator_Q_of_basis`), the fundamental weight
$\mathfrak w_i = \mathfrak wL^{\mathfrak s_i}$ is $\sum_j a_i\,\mathfrak d(Q(y_j)/a_i) + 2\,\mathfrak sL^{\mathfrak s_i}$. -/
@[kb "omeara1963" "§94, p. 280 (the fundamental invariants a_i, w_i from L^{s_1}, …, L^{s_t})"]
theorem weight_subA_scale_eq_sum_quadDefect (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} {t : ℕ}
    (Ls : Fin t → Submodule R V) (i : Fin t) (hreg : IsRegular Q (subA Q (scale Q (Ls i)) L))
    (hne : subA Q (scale Q (Ls i)) L ≠ ⊥) {ι : Type*} [Fintype ι] (b : Basis ι R (subA Q (scale Q (Ls i)) L))
    {a : F} (ha : IsNormGenerator Q (subA Q (scale Q (Ls i)) L) a) :
    weight Q (subA Q (scale Q (Ls i)) L) =
      (⨆ j, a • quadDefect R (Q (b j : V) / a)) ⊔ (2 : F) • scale Q (subA Q (scale Q (Ls i)) L) :=
  weight_eq_sum_quadDefect Q h2p hreg hne b ha

end QuadFormsKB.OMeara
