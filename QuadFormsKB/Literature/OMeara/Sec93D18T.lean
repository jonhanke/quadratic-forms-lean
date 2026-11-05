/-
# O'Meara §93D, Example 93:18 (iv): ternary unimodular lattices with $\operatorname{ord} a + \operatorname{ord} b$ odd

**Setting** as in `Sec93D18Q.lean`. $L \cong A(\beta, \gamma) \perp \langle c\rangle$ is `HasBlk1 Q L β γ c`: $L$ has a
base with matrix `blk1 β γ c`.

**Page image read** (O'Meara 1973 printing, p. 261): "(iv) Now let $\dim L = 3$ with $\operatorname{ord}_{\mathfrak p} a
+ \operatorname{ord}_{\mathfrak p} b$ odd. We claim that $L \cong \langle A(b, 0)\rangle \perp \langle -d\rangle$ or
$L \cong \langle A(b, 4\rho b^{-1})\rangle \perp \langle -d(1 - 4\rho)\rangle$, but not both." O'Meara derives this from
(iii) by adjoining $\langle\varepsilon\rangle$ and cancelling with 93:14a; "a computation with Hasse symbols shows that
$L$ cannot have both the given forms".

**Proof here** (the pattern of (iii), without the adjunction): $L = \langle\varepsilon\rangle \perp L'$ with
$\varepsilon$ a unit and $L' \cong A(a', \beta')$ (93:10); the two candidate lattices have the norm group of $L$
($-d \in \mathfrak gL$ because $-d \equiv \varepsilon u^2 \bmod b\mathfrak o$), the discriminant of $L$, and opposite
Hasse symbols ($(e, bde) = (-1)^{\operatorname{ord} b}$ with $e = 1 - 4\rho$); then 63:20 and 93:16.

**Proves**
* `normIdeal_eq_one_of_rank_three`: a ternary unimodular lattice has $\mathfrak nL = \mathfrak o$;
* `exists_blk1_basis`: a ternary unimodular lattice has a base with matrix $A(a', \beta') \perp \langle\varepsilon\rangle$;
* `omeara93_18_iv` (**93:18 (iv)**).
-/
import QuadFormsKB.Literature.OMeara.Sec93D18Q

open QuadraticMap Submodule Module IsLocalRing QuadFormsKB.PadicClass
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.D18

/-- The block matrix $A(\beta, \gamma) \perp \langle c\rangle$. -/
def blk1 {S : Type*} [Semiring S] (β γ c : S) : Matrix (Fin 3) (Fin 3) S :=
  Matrix.of ![![β, 1, 0], ![1, γ, 0], ![0, 0, c]]

theorem det_blk1 {S : Type*} [CommRing S] (β γ c : S) : (blk1 β γ c).det = (β * γ - 1) * c := by
  simp [blk1, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem map_blk1 {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) (β γ c : S) :
    (blk1 β γ c).map f = blk1 (f β) (f γ) (f c) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [blk1]

/-- **$L \cong A(\beta, \gamma) \perp \langle c\rangle$** (O'Meara 1963, §93B, p. 255, notation of 93:18 (iv)): $L$ has a
base $x, y, z$ with matrix `blk1 β γ c`: $Q(x) = \beta$, $B(x, y) = 1$, $Q(y) = \gamma$, $Q(z) = c$, $z \perp x, y$. -/
def HasBlk1 {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)] {V : Type*}
    [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] (Q : QuadraticForm F V) (L : Submodule R V)
    (β γ c : F) : Prop :=
  ∃ e : Basis (Fin 3) R L, gram Q (fun i => (e i : V)) = blk1 β γ c

section Blocks

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- Weights of the orthogonal splitting of $A(\beta, \gamma) \perp \langle c\rangle$ over a field. -/
def dw1 (β γ c : K) : Fin 3 → K := ![β, β * (β * γ - 1), c]

/-- The change of basis from `blk1` to a diagonal matrix. -/
def pblk1 (β : K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of ![![1, 0, 0], ![-1, β, 0], ![0, 0, 1]]

theorem pblk1_det (β : K) : (pblk1 β).det = β := by
  simp [pblk1, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem pblk1_mul (β γ c : K) :
    pblk1 β * blk1 β γ c * (pblk1 β)ᵀ = Matrix.diagonal (dw1 β γ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pblk1, blk1, dw1, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] <;> ring

theorem rep_blk1_iff {β : K} (hβ : β ≠ 0) (γ c : K) :
    Rep Q (blk1 β γ c) ↔ Rep Q (Matrix.diagonal (dw1 β γ c)) := by
  rw [← pblk1_mul, rep_congr_iff Q (by rw [pblk1_det]; exact hβ.isUnit)]

end Blocks

section Hasse

variable {F : Type*} [Field F] [CharZero F]

theorem hasseVec_three (w : Fin 3 → F) :
    hasseVec w = hilbertSymbol F (w 0) (w 1) * hilbertSymbol F (w 0) (w 2) * hilbertSymbol F (w 1) (w 2) := by
  simp only [hasseVec, Fin.prod_univ_three]
  simp

/-- **The Hasse symbols of the two ternary forms of 93:18 (iv)**: $S\langle b, -b, -d\rangle \cdot
S\langle b, -be, -de\rangle = (e, bde)$. -/
theorem hasseS_three_diff (hK : LocalHilbertField F) {b d e : F} (hb : b ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) :
    hasseS F ![b, -b, -d] * hasseS F ![b, -(b * e), -(d * e)] = hilbertSymbol F e (b * d * e) := by
  have hw1 : ∀ i, (![b, -b, -d] : Fin 3 → F) i ≠ 0 := by
    intro i; fin_cases i <;> simp [hb, hd, he]
  have hw2 : ∀ i, (![b, -(b * e), -(d * e)] : Fin 3 → F) i ≠ 0 := by
    intro i; fin_cases i <;> simp [hb, hd, he]
  rw [hasseS_eq_vec_mul hK _ hw1, hasseS_eq_vec_mul hK _ hw2, hasseVec_three, hasseVec_three]
  have p1 : ∏ i, (![b, -b, -d] : Fin 3 → F) i = b ^ 2 * d := by
    rw [Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    ring
  have p2 : ∏ i, (![b, -(b * e), -(d * e)] : Fin 3 → F) i = (b * e) ^ 2 * d := by
    rw [Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    ring
  rw [p1, p2, hs_sq_right _ _ _ hb, hs_sq_right _ _ _ (mul_ne_zero hb he)]
  have L1 : ∀ x y z : F, x ≠ 0 → y ≠ 0 → z ≠ 0 →
      hilbertSymbol F (x * y) z = hilbertSymbol F x z * hilbertSymbol F y z := fun x y z hx hy hz =>
    hK.mul_left x y z hx hy hz
  have R1 : ∀ x y z : F, x ≠ 0 → y ≠ 0 → z ≠ 0 →
      hilbertSymbol F x (y * z) = hilbertSymbol F x y * hilbertSymbol F x z := fun x y z hx hy hz =>
    hK.mul_right hx hy hz
  have S1 : ∀ x : F, x ≠ 0 → hilbertSymbol F x x = hilbertSymbol F x (-1) := fun x hx => hK.self hx
  have e2 : -b = (-1) * b := by ring
  have e3 : -d = (-1) * d := by ring
  have e4 : -(b * e) = (-1) * (b * e) := by ring
  have e5 : -(d * e) = (-1) * (d * e) := by ring
  simp (disch := simp [hb, hd, he]) only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, e2, e3, e4, e5, L1, R1, S1]
  simp only [hilbertSymbol_comm F]
  have sq : ∀ x y : F, hilbertSymbol F x y ^ 2 = 1 := fun x y => by
    rcases hs_pm x y with h | h <;> simp [h]
  have s1 := sq b (-1)
  have s2 := sq d (-1)
  have s3 := sq e (-1)
  have s5 := sq (-1) (-1)
  have s6 := sq b d
  have s7 := sq b e
  have s8 := sq d e
  grind

end Hasse

section Split

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **A ternary unimodular lattice is $A(a_1, \beta_1) \perp \langle\varepsilon\rangle$** (93:15 and 93:10): it has a
base with matrix `blk1 a₁ β₁ ε`, $a_1 \neq 0$, $\beta_1 \in \mathfrak wL$, $-1 + a_1\beta_1$ and $\varepsilon$ units. -/
theorem exists_blk1_basis (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L)
    (hrk : finrank R L = 3) :
    ∃ a₁ β₁ ε : R, algebraMap R F a₁ ≠ 0 ∧ algebraMap R F β₁ ∈ weight Q L ∧ IsUnit (-1 + a₁ * β₁) ∧ IsUnit ε ∧
      ∃ e : Basis (Fin 3) R L, gram Q (fun i => (e i : V)) =
        blk1 (algebraMap R F a₁) (algebraMap R F β₁) (algebraMap R F ε) := by
  obtain ⟨J, hJL, hJfg, hJU, hJrk, -⟩ := Uni93.exists_split_data Q hfg hU (by omega)
  obtain ⟨K, hK⟩ := splits_of_isModular_of_scale_eq Q hJL hJU hJfg hU.2.1
  have hrkL := isOrthSum_finrank Q hK hfg
  have hK0 : K ≠ ⊥ := by
    rintro rfl
    simp at hrkL; omega
  have hKle : K ≤ L := hK.sup_eq ▸ le_sup_right
  have hKfg : K.FG := FG.of_le hfg hKle
  have hKU := u93_isUnimodular_of_orth Q hfg hU hJU hK hK0
  have hKrk : finrank R K = 1 := by omega
  obtain ⟨a₁, β₁, h1, -, h3, h4, bJ, hbJ⟩ := exists_matA_basis Q h2p hJfg hJU hJrk
  obtain ⟨bK₀⟩ := exists_basis (R := R) (F := F) hKfg
  let bK : Basis (Fin 1) R K := bK₀.reindex (finCongr hKrk)
  obtain ⟨ε, hε, hdetK⟩ := Eng93.isUnit_det_of_isUnimodular Q hKU bK
  have hQk : Q (bK 0 : V) = algebraMap R F ε := by
    rw [← hdetK, Matrix.det_unique]; simp [gram]
  have eJ : ∀ i j, bil Q (bJ i : V) (bJ j : V) = matA (algebraMap R F a₁) (algebraMap R F β₁) i j :=
    fun i j => by simpa [gram] using congrFun (congrFun hbJ i) j
  have cJK : ∀ i, bil Q (bJ i : V) (bK 0 : V) = 0 := fun i => hK.orth _ (bJ i).2 _ (bK 0).2
  have cKJ : ∀ i, bil Q (bK 0 : V) (bJ i : V) = 0 := fun i => by rw [bil_comm]; exact cJK i
  let v : Fin 3 → V := ![bJ 0, bJ 1, bK 0]
  have hv : ∀ i, v i ∈ L := by
    intro i
    fin_cases i
    · exact hJL (bJ 0).2
    · exact hJL (bJ 1).2
    · exact hKle (bK 0).2
  have hgram : gram Q v = (blk1 a₁ β₁ ε).map (algebraMap R F) := by
    rw [map_blk1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [v, gram, blk1, eJ, cJK, cKJ, matA, hQk]
  have hdet : IsUnit (blk1 a₁ β₁ ε).det := by
    rw [det_blk1]
    exact (by simpa [add_comm, sub_eq_add_neg] using h4 : IsUnit (a₁ * β₁ - 1)).mul hε
  obtain ⟨e, he⟩ := exists_basis_of_gram_unit Q hfg hU hrk hv hdet hgram
  refine ⟨a₁, β₁, ε, h1, weight_mono Q hJL h3, h4, hε, e, ?_⟩
  rw [← map_blk1, ← hgram]
  congr 1
  funext i
  exact he i

end Split

section NormGroup

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **The norm group of $A(b, q) \perp \langle c\rangle$** (O'Meara 1963, p. 261, "$\mathfrak gL = \mathfrak gK$"): let
$L$ be a unimodular lattice with norm generator $a$ and weight generator $b$, $\operatorname{ord} a +
\operatorname{ord} b$ odd, and let $M = \mathfrak oe_1 + \mathfrak oe_2 + \mathfrak oe_3$ be a unimodular lattice whose
base $e$ has matrix `blk1 b q c` with $q \in b\mathfrak o$ and $c \in \mathfrak gL$ a unit. Then $\mathfrak gM =
\mathfrak gL$. -/
theorem normGroup_eq_of_blk1 (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π) {L : Submodule R V}
    (hfg : L.FG) (hU : IsUnimodular Q L) {a b : F} (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b)
    (hodd : Odd (dord hπ a + dord hπ b)) {e : Fin 3 → V} {q : F} {c₀ : R} (hq : q ∈ R ∙ b)
    (hc₀ : IsUnit c₀) (hc : algebraMap R F c₀ ∈ normGroup Q L)
    (hgram : gram Q e = blk1 b q (algebraMap R F c₀)) (hMU : IsUnimodular Q (span R (Set.range e))) :
    normGroup Q L = normGroup Q (span R (Set.range e)) := by
  set M := span R (Set.range e) with hM
  have hinj := IsFractionRing.injective R F
  have hne := Uni93.ne_bot_of_isUnimodular Q hU
  have hreg : IsRegular Q L := IsModular.isRegular Q hU hfg
  have ha0 := ha.ne_zero Q hreg hne
  have hb0 := weight_gen_ne_zero Q ha ha0 hb
  have hset := normGroup_eq_sq_add Q h2p hreg hne ha hb
  have h1L : (1 : F) ∈ scale Q L := by rw [hU.2.1]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have h2b : (2 : F) ∈ R ∙ b := two_smul_scale_le_weight_gen Q hb
    (by simpa using smul_mem_pointwise_smul (1 : F) (2 : F) _ h1L)
  obtain ⟨t, ht⟩ := mem_span_singleton.mp h2b
  obtain ⟨q', hq'⟩ := mem_span_singleton.mp hq
  rw [Algebra.smul_def] at ht hq'
  have he : ∀ i, e i ∈ M := fun i => subset_span ⟨i, rfl⟩
  have hQe : ∀ i j, bil Q (e i) (e j) = blk1 b q (algebraMap R F c₀) i j := fun i j => by
    simpa [gram] using congrFun (congrFun hgram i) j
  have hQb : Q (e 0) = b := by rw [← bil_self, hQe]; simp [blk1]
  have hQc : Q (e 2) = algebraMap R F c₀ := by rw [← bil_self, hQe]; simp [blk1]
  have hval : ∀ x : Fin 3 → R, Q (∑ i, algebraMap R F (x i) • e i) = algebraMap R F (x 2) ^ 2 * algebraMap R F c₀ +
      b * algebraMap R F (x 0 ^ 2 + t * x 0 * x 1 + q' * x 1 ^ 2) := by
    intro x
    rw [Q_sum_gram, hgram]
    simp [blk1, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    linear_combination (-(algebraMap R F (x 0) * algebraMap R F (x 1))) * ht +
      (-(algebraMap R F (x 1) ^ 2)) * hq'
  -- `a` is a unit and `b ∈ 𝔭`
  have hscale : ∀ z ∈ normIdeal Q L, ∃ z₀ : R, algebraMap R F z₀ = z := fun z hz => by
    have := normIdeal_le_scale Q L hz
    rw [hU.2.1] at this
    exact Submodule.mem_one.mp this
  obtain ⟨a₀, ha₀⟩ := hscale a (ha.2 ▸ mem_span_singleton_self a)
  obtain ⟨b₀, hb₀⟩ := hscale b ((weight_bounds Q L).2.2.2 (hb ▸ mem_span_singleton_self b))
  have hca : algebraMap R F c₀ ∈ R ∙ a := by rw [ha.2]; exact normGroup_subset_normIdeal Q L hc
  obtain ⟨r, hr⟩ := mem_span_singleton.mp hca
  rw [Algebra.smul_def] at hr
  have ha₀u : IsUnit a₀ := by
    have : r * a₀ = c₀ := hinj (by rw [map_mul, ha₀, hr])
    exact isUnit_of_mul_isUnit_right (this ▸ hc₀)
  have hda : dord hπ a = 0 := by rw [← ha₀]; exact dord_unit hπ ha₀u
  have hdc : dord hπ (algebraMap R F c₀) = 0 := dord_unit hπ hc₀
  have hb₀m : b₀ ∈ maximalIdeal R := by
    by_contra hn
    have hu : IsUnit b₀ := by
      by_contra hu; exact hn ((mem_maximalIdeal _).mpr hu)
    have hdb : dord hπ b = 0 := by rw [← hb₀]; exact dord_unit hπ hu
    rw [hda, hdb] at hodd
    exact (Int.not_odd_iff_even.mpr ⟨0, rfl⟩) hodd
  -- `c` is a norm generator of `M` and `b ∈ 𝔴M`
  have hcM : IsNormGenerator Q M (algebraMap R F c₀) := by
    refine ⟨hQc ▸ Q_mem_normGroup Q (he 2), le_antisymm ?_ ?_⟩
    · rw [span_singleton_le_iff_mem, ← hQc]; exact Q_mem_normIdeal Q (he 2)
    · intro z hz
      have := normIdeal_le_scale Q M hz
      rw [hMU.2.1] at this
      obtain ⟨z₀, rfl⟩ := Submodule.mem_one.mp this
      obtain ⟨u, hu⟩ := hc₀.exists_left_inv
      refine mem_span_singleton.mpr ⟨z₀ * u, ?_⟩
      rw [Algebra.smul_def, ← map_mul, mul_assoc, hu, mul_one]
  have hc0 : algebraMap R F c₀ ≠ 0 := fun h => hc₀.ne_zero (hinj (h.trans (map_zero _).symm))
  have hbM : b ∈ weight Q M := by
    refine mem_weight_of_odd Q h2p hπ hcM hc0 (hQb ▸ Q_mem_normGroup Q (he 0)) hb0 ?_
    rw [hdc, sub_zero]; rw [hda, zero_add] at hodd; exact hodd
  have hbwM : ∀ η : R, b * algebraMap R F η ∈ normGroup Q M := fun η => by
    have hw : algebraMap R F η * b ∈ weight Q M := by
      rw [← Algebra.smul_def]; exact (weight Q M).smul_mem η hbM
    have := normGroupIdeal_subset Q M ((weight_bounds Q M).2.1 hw)
    rwa [mul_comm] at this
  have hbL : b ∈ weight Q L := hb ▸ mem_span_singleton_self b
  have hbwL : ∀ η : R, b * algebraMap R F η ∈ normGroup Q L := fun η => by
    have hw : algebraMap R F η * b ∈ weight Q L := by
      rw [← Algebra.smul_def]; exact (weight Q L).smul_mem η hbL
    have := normGroupIdeal_subset Q L ((weight_bounds Q L).2.1 hw)
    rwa [mul_comm] at this
  apply le_antisymm
  · intro z hz
    have hz' : z ∈ (normGroup Q L : Set F) := hz
    rw [hset] at hz'
    obtain ⟨ε, η, rfl⟩ := hz'
    have hc' : algebraMap R F c₀ ∈ (normGroup Q L : Set F) := hc
    rw [hset] at hc'
    obtain ⟨e₀, η₀, he₀⟩ := hc'
    have he₀u : IsUnit e₀ := by
      by_contra hn
      have hm : e₀ ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hn
      have hc₀eq : c₀ = a₀ * e₀ ^ 2 + b₀ * η₀ := hinj (by simp only [map_add, map_mul, map_pow, ha₀, hb₀]; exact he₀)
      have : c₀ ∈ maximalIdeal R := by
        rw [hc₀eq]
        exact add_mem (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hm 2 two_pos))
          (Ideal.mul_mem_right _ _ hb₀m)
      exact (mem_maximalIdeal _).mp this hc₀
    obtain ⟨f, hf⟩ := he₀u.exists_left_inv
    have hf' : algebraMap R F f * algebraMap R F e₀ = 1 := by rw [← map_mul, hf, map_one]
    have hrw : a * algebraMap R F ε ^ 2 + b * algebraMap R F η =
        algebraMap R F (ε * f) ^ 2 * algebraMap R F c₀ + b * algebraMap R F (η - η₀ * (ε * f) ^ 2) := by
      rw [he₀]; simp only [map_mul, map_sub, map_pow]
      linear_combination (-(a * algebraMap R F ε ^ 2 * (1 + algebraMap R F f * algebraMap R F e₀))) * hf'
    rw [hrw]
    exact add_mem (mul_sq_mem_normGroup Q (hQc ▸ Q_mem_normGroup Q (he 2)) ⟨ε * f, rfl⟩) (hbwM _)
  · rintro z ⟨y, hy, c', hc', rfl⟩
    rw [hMU.2.1] at hc'
    obtain ⟨c₁, rfl⟩ := Submodule.mem_one.mp hc'
    obtain ⟨x, rfl⟩ := exists_coeffs (R := R) (F := F) e hy
    rw [hval]
    have : algebraMap R F (x 2) ^ 2 * algebraMap R F c₀ +
        b * algebraMap R F (x 0 ^ 2 + t * x 0 * x 1 + q' * x 1 ^ 2) + 2 * algebraMap R F c₁ =
        algebraMap R F (x 2) ^ 2 * algebraMap R F c₀ +
          b * algebraMap R F (x 0 ^ 2 + t * x 0 * x 1 + q' * x 1 ^ 2 + t * c₁) := by
      simp only [map_add, map_mul, map_pow]
      linear_combination (-(algebraMap R F c₁)) * ht
    rw [this]
    exact add_mem (mul_sq_mem_normGroup Q hc ⟨x 2, rfl⟩) (hbwL _)

end NormGroup

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- A lattice $L \cong A(\beta, \gamma) \perp \langle c\rangle$ of rank $\dim V = 3$ gives an $F$-base of $V$ with
matrix `blk1 β γ c`. -/
theorem rep_of_hasBlk1 (hV : finrank F V = 3) {L : Submodule R V} {β γ c : F} (h : HasBlk1 Q L β γ c)
    (hdet : (β * γ - 1) * c ≠ 0) : Rep Q (blk1 β γ c) := by
  obtain ⟨e, he⟩ := h
  obtain ⟨eF, heF⟩ := Eng93.basisF_of_lattice Q e (by rw [he, det_blk1]; exact hdet) hV
  exact ⟨eF, by rw [← he]; congr 1; funext i; exact heF i⟩

/-- **Example 93:18 (iv)** (O'Meara 1963, §93D, p. 261). Let $L$ be a unimodular lattice on a $3$-dimensional
quadratic space $V$ over a dyadic local field, $a$ a norm generator and $b$ a weight generator of $L$ with
$\operatorname{ord}_{\mathfrak p} a + \operatorname{ord}_{\mathfrak p} b$ odd, $d$ the discriminant of $L$ (a base of
$L$ has discriminant $d$), and $\Delta = 1 + 4\rho$ the unit of quadratic defect $4\mathfrak o$ (§93, p. 251). Then
$L \cong A(b, 0) \perp \langle -d\rangle$ or $L \cong A(b, 4\rho b^{-1}) \perp \langle -d(1 - 4\rho)\rangle$, but not
both.

*Form of the statement.* "$L \cong A(\beta,\gamma) \perp \langle c\rangle$" is `HasBlk1 Q L β γ c` ($L$ has a base with
that matrix); "on $V$" is `finrank F V = 3 = finrank R L`. The local field is abstract, as in `omeara93_18_iii`.

*Proof.* O'Meara adjoins a unit $\langle\varepsilon\rangle$, applies the quaternary case (iii) and cancels with 93:14a.
Here the argument of (iii) is run directly in dimension $3$: both candidate lattices have the norm group of $L$
(`normGroup_eq_of_blk1`; $-d \in \mathfrak gL$ since $L = A(a_1, \beta_1) \perp \langle\varepsilon\rangle$ gives
$-d \equiv \varepsilon\eta^2 \bmod b\mathfrak o$), the discriminant of $L$, and opposite Hasse symbols
(`hasseS_three_diff`: the product is $(1 - 4\rho, bd(1 - 4\rho)) = (\Delta, bd(1-4\rho)) = (-1)^{\operatorname{ord} b} =
-1$, "a computation with Hasse symbols"); then 63:20 and 93:16. -/
@[kb "omeara1963" "§93D, 93:18 (iv), p. 261"]
theorem omeara93_18_iv (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π)
    (hV : finrank F V = 3) {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L)
    (hrk : finrank R L = 3) {a b : F} (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b)
    (hodd : Odd (dord hπ a + dord hπ b)) {d : R}
    (hd : ∃ e : Basis (Fin 3) R L, (gram Q fun i => (e i : V)).det = algebraMap R F d)
    {ρ : R} (hρ : quadDefect R (algebraMap R F (1 + 4 * ρ)) = span R {(4 : F)}) :
    Xor' (HasBlk1 Q L b 0 (-algebraMap R F d))
      (HasBlk1 Q L b (4 * algebraMap R F ρ / b) (-(algebraMap R F d * (1 - 4 * algebraMap R F ρ)))) := by
  have hinj := IsFractionRing.injective R F
  have hne := Uni93.ne_bot_of_isUnimodular Q hU
  have hreg : IsRegular Q L := IsModular.isRegular Q hU hfg
  have ha0 := ha.ne_zero Q hreg hne
  have hb0 := weight_gen_ne_zero Q ha ha0 hb
  have h2m : (2 : R) ∈ maximalIdeal R := Uni93.two_mem_maximalIdeal h2p
  have h2R : (2 : R) ≠ 0 := fun h => two_ne_zero (α := F) (by rw [← map_ofNat (algebraMap R F) 2, h, map_zero])
  have h4m : 4 * ρ ∈ maximalIdeal R := by
    rw [show (4 : R) * ρ = 2 * (2 * ρ) by ring]; exact Ideal.mul_mem_right _ _ h2m
  have algne : ∀ {u : R}, IsUnit u → algebraMap R F u ≠ 0 := fun hu h =>
    hu.ne_zero (hinj (by rw [h, map_zero]))
  have hscale : ∀ z ∈ normIdeal Q L, ∃ z₀ : R, algebraMap R F z₀ = z := fun z hz => by
    have := normIdeal_le_scale Q L hz
    rw [hU.2.1] at this
    exact Submodule.mem_one.mp this
  obtain ⟨a₀, ha₀⟩ := hscale a (ha.2 ▸ mem_span_singleton_self a)
  obtain ⟨b₀, hb₀⟩ := hscale b ((weight_bounds Q L).2.2.2 (hb ▸ mem_span_singleton_self b))
  have h1L : (1 : F) ∈ scale Q L := by rw [hU.2.1]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have h2b : (2 : F) ∈ R ∙ b := two_smul_scale_le_weight_gen Q hb
    (by simpa using smul_mem_pointwise_smul (1 : F) (2 : F) _ h1L)
  obtain ⟨t, ht⟩ := mem_span_singleton.mp h2b
  rw [Algebra.smul_def] at ht
  have hbL : b ∈ weight Q L := hb ▸ mem_span_singleton_self b
  have hbwL : ∀ η : R, b * algebraMap R F η ∈ normGroup Q L := fun η => by
    have hw : algebraMap R F η * b ∈ weight Q L := by
      rw [← Algebra.smul_def]; exact (weight Q L).smul_mem η hbL
    have := normGroupIdeal_subset Q L ((weight_bounds Q L).2.1 hw)
    rwa [mul_comm] at this
  -- the base `A(a₁, β₁) ⊥ ⟨ε⟩` of `L`
  obtain ⟨a₁, β₁, ε, ha₁, hβ₁, hu₁, hε, e, he⟩ := exists_blk1_basis Q h2p hfg hU hrk
  obtain ⟨e', he'⟩ := hd
  obtain ⟨η, hη, hdet⟩ := Uni93.exists_unit_det_gram Q e e'
  rw [he', he, det_blk1] at hdet
  have hu₁' : IsUnit (a₁ * β₁ - 1) := by simpa [add_comm, sub_eq_add_neg] using hu₁
  have hdR : d = η ^ 2 * ((a₁ * β₁ - 1) * ε) := hinj (by rw [hdet]; simp)
  have hdu : IsUnit d := by rw [hdR]; exact (hη.pow 2).mul (hu₁'.mul hε)
  have hd0 : algebraMap R F d ≠ 0 := algne hdu
  -- `a` is a unit (`ε ∈ 𝔫L`), so `ord b` is odd
  have hQe2 : Q (e 2 : V) = algebraMap R F ε := by
    have := congrFun (congrFun he 2) 2; simpa [gram, blk1] using this
  have hεa : algebraMap R F ε ∈ R ∙ a := by
    rw [ha.2, ← hQe2]; exact Q_mem_normIdeal Q (e 2).2
  obtain ⟨r, hr⟩ := mem_span_singleton.mp hεa
  rw [Algebra.smul_def] at hr
  have ha₀u : IsUnit a₀ := by
    have : r * a₀ = ε := hinj (by rw [map_mul, ha₀, hr])
    exact isUnit_of_mul_isUnit_right (this ▸ hε)
  have hda : dord hπ a = 0 := by rw [← ha₀]; exact dord_unit hπ ha₀u
  have hbodd : Odd (dord hπ b) := by rw [hda, zero_add] at hodd; exact hodd
  -- `-d` and `-d(1 - 4ρ)` lie in `𝔤L`
  have hβb : algebraMap R F β₁ ∈ R ∙ b := by rw [hb]; exact hβ₁
  obtain ⟨s, hs⟩ := mem_span_singleton.mp hβb
  rw [Algebra.smul_def] at hs
  have hmd : algebraMap R F (-d) ∈ normGroup Q L := by
    have : algebraMap R F (-d) = algebraMap R F η ^ 2 * algebraMap R F ε +
        b * algebraMap R F (-(η ^ 2 * ε * a₁ * s)) := by
      rw [map_neg, hdet]; simp only [map_neg, map_mul, map_pow]
      linear_combination (algebraMap R F η ^ 2 * algebraMap R F ε * algebraMap R F a₁) * hs
    rw [this]
    exact add_mem (mul_sq_mem_normGroup Q (hQe2 ▸ Q_mem_normGroup Q (e 2).2) ⟨η, rfl⟩) (hbwL _)
  have hmdK : algebraMap R F (-(d * (1 - 4 * ρ))) ∈ normGroup Q L := by
    have : algebraMap R F (-(d * (1 - 4 * ρ))) = algebraMap R F (-d) + b * algebraMap R F (2 * t * ρ * d) := by
      simp only [map_neg, map_mul, map_sub, map_one, map_ofNat]
      linear_combination (-(2 * algebraMap R F ρ * algebraMap R F d)) * ht
    rw [this]
    exact add_mem hmd (hbwL _)
  -- the parameters in `𝔬`
  have hsK : 4 * algebraMap R F ρ / b = algebraMap R F (2 * t * ρ) := by
    field_simp
    simp only [map_mul, map_ofNat]
    linear_combination (-(2 * algebraMap R F ρ)) * ht
  have hsKb : 4 * algebraMap R F ρ / b ∈ R ∙ b := by
    rw [hsK]
    refine mem_span_singleton.mpr ⟨t * t * ρ, ?_⟩
    rw [Algebra.smul_def]
    simp only [map_mul, map_ofNat]
    linear_combination (algebraMap R F t * algebraMap R F ρ) * ht
  have hzb : (0 : F) ∈ R ∙ b := zero_mem _
  have ht₀ : t * b₀ = 2 := hinj (by rw [map_mul, hb₀, ht, map_ofNat])
  have heu : IsUnit (1 - 4 * ρ) := by
    simpa [sub_eq_add_neg] using isUnit_one_add_aux (neg_mem h4m)
  have hdKu : IsUnit (-(d * (1 - 4 * ρ))) := (hdu.mul heu).neg
  have huJ : IsUnit ((b₀ * 0 - 1) * -d) := by
    have : (b₀ * 0 - 1) * -d = d := by ring
    rw [this]; exact hdu
  have huK : IsUnit ((b₀ * (2 * t * ρ) - 1) * -(d * (1 - 4 * ρ))) := by
    have : (b₀ * (2 * t * ρ) - 1) * -(d * (1 - 4 * ρ)) = d * (1 - 4 * ρ) * (1 - 4 * ρ) := by
      linear_combination (-(2 * ρ * d * (1 - 4 * ρ))) * ht₀
    rw [this]; exact (hdu.mul heu).mul heu
  -- the space side
  have hu₁F : algebraMap R F a₁ * algebraMap R F β₁ - 1 ≠ 0 := by
    rw [← map_mul, ← map_one (algebraMap R F), ← map_sub]; exact algne hu₁'
  have hε0 : algebraMap R F ε ≠ 0 := algne hε
  have hη0 : algebraMap R F η ≠ 0 := algne hη
  obtain ⟨eF, heF⟩ := Eng93.basisF_of_lattice Q e (by rw [he, det_blk1]; exact mul_ne_zero hu₁F hε0) hV
  have hspan : span F (L : Set V) = ⊤ := Eng93.span_eq_top_of_basis e eF heF
  have hRepL : Rep Q (blk1 (algebraMap R F a₁) (algebraMap R F β₁) (algebraMap R F ε)) :=
    rep_of_hasBlk1 Q hV ⟨e, he⟩ (mul_ne_zero hu₁F hε0)
  set w := dw1 (algebraMap R F a₁) (algebraMap R F β₁) (algebraMap R F ε) with hw
  have hRepw : Rep Q (Matrix.diagonal w) := (rep_blk1_iff Q ha₁ _ _).mp hRepL
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i; fin_cases i <;> simp [hw, dw1, ha₁, hu₁F, hε0]
  set dF := algebraMap R F d with hdF
  set eF' : F := 1 - 4 * algebraMap R F ρ with heF'
  have he0 : eF' ≠ 0 := by
    have := algne heu; simp only [map_sub, map_one, map_mul, map_ofNat] at this; exact this
  set sK : F := 4 * algebraMap R F ρ / b with hsKdef
  set wJ := dw1 b 0 (-dF) with hwJ
  set wK := dw1 b sK (-(dF * eF')) with hwK
  have hJv : wJ = ![b, -b, -dF] := by
    funext i; fin_cases i <;> simp [hwJ, dw1]
  have hKv : wK = ![b, -(b * eF'), -(dF * eF')] := by
    funext i; fin_cases i <;> simp [hwK, dw1, hsKdef, heF'] <;> field_simp <;> ring
  have hwJ0 : ∀ i, wJ i ≠ 0 := by
    rw [hJv]; intro i; fin_cases i <;> simp [hb0, hd0]
  have hwK0 : ∀ i, wK i ≠ 0 := by
    rw [hKv]; intro i; fin_cases i <;> simp [hb0, hd0, he0]
  -- discriminants
  have hprodw : ∏ i, w i = (algebraMap R F a₁ / algebraMap R F η) ^ 2 * dF := by
    rw [hdet, hw]; simp [dw1, Fin.prod_univ_three]; field_simp
  have hdiscJ : ∃ t : F, t ≠ 0 ∧ ∏ i, wJ i = t ^ 2 * ∏ i, w i := by
    refine ⟨b * algebraMap R F η / algebraMap R F a₁, by simp [hb0, hη0, ha₁], ?_⟩
    rw [hprodw, hJv]; simp [Fin.prod_univ_three]; field_simp
  have hdiscK : ∃ t : F, t ≠ 0 ∧ ∏ i, wK i = t ^ 2 * ∏ i, w i := by
    refine ⟨b * eF' * algebraMap R F η / algebraMap R F a₁, by simp [hb0, hη0, ha₁, he0], ?_⟩
    rw [hprodw, hKv]; simp [Fin.prod_univ_three]; field_simp
  -- Hasse symbols: `S(FJ) S(FK) = (e, b d e) = -1`
  have hP : hasseS F wJ * hasseS F wK = -1 := by
    rw [hJv, hKv, hasseS_three_diff hK hb0 hd0 he0]
    have hρρ : -(4 * ρ * ρ) ∈ maximalIdeal R := neg_mem (Ideal.mul_mem_right ρ _ h4m)
    obtain ⟨τ, hτ⟩ := isSquare_one_add_four_mul hρρ
    have hτu : IsUnit (τ * τ) := hτ ▸ isUnit_one_add_aux (Ideal.mul_mem_left _ _ hρρ)
    have hτ0 : algebraMap R F τ ≠ 0 := fun h => algne hτu (by rw [map_mul, h, zero_mul])
    have hΔu : IsUnit (1 + 4 * ρ) := isUnit_one_add_aux h4m
    have hΔ0 : algebraMap R F (1 + 4 * ρ) ≠ 0 := algne hΔu
    have heΔ : eF' = (algebraMap R F τ / algebraMap R F (1 + 4 * ρ)) ^ 2 * algebraMap R F (1 + 4 * ρ) := by
      have := congrArg (algebraMap R F) hτ
      simp only [map_mul, map_add, map_neg, map_one, map_ofNat] at this
      rw [heF']; field_simp
      simp only [map_add, map_mul, map_one, map_ofNat] at hΔ0 ⊢
      linear_combination this
    have hx0 : b * dF * eF' ≠ 0 := mul_ne_zero (mul_ne_zero hb0 hd0) he0
    have hsym : ∀ x : F, hilbertSymbol F eF' x = hilbertSymbol F x (algebraMap R F (1 + 4 * ρ)) := fun x => by
      rw [hilbertSymbol_comm F, heΔ, hs_sq_right _ _ _ (div_ne_zero hτ0 hΔ0)]
    have hde : dord hπ eF' = 0 := by
      have : eF' = algebraMap R F (1 - 4 * ρ) := by rw [heF']; simp only [map_sub, map_one, map_mul, map_ofNat]
      rw [this]; exact dord_unit hπ heu
    rw [hsym, hilbert_delta_parity hK h2R hΔu hρ hπ hx0, dord_mul hπ (mul_ne_zero hb0 hd0) he0,
      dord_mul hπ hb0 hd0, dord_unit hπ hdu, hde, add_zero, add_zero,
      if_neg (Int.not_even_iff_odd.mpr hbodd)]
  have iffJ := rep_diag_iff_S Q hK hw0 hwJ0 hRepw
  have iffK := rep_diag_iff_S Q hK hw0 hwK0 hRepw
  -- from a representation of the space to an isometry of lattices (93:16)
  have toBlk : ∀ {q c : F} (q₀ c₀ : R), algebraMap R F q₀ = q → algebraMap R F c₀ = c → q ∈ R ∙ b →
      IsUnit c₀ → algebraMap R F c₀ ∈ normGroup Q L → IsUnit ((b₀ * q₀ - 1) * c₀) →
      Rep Q (Matrix.diagonal (dw1 b q c)) → HasBlk1 Q L b q c := by
    intro q c q₀ c₀ hq hc hqb hc₀ hcg hunit hR
    obtain ⟨eX, heX⟩ := (rep_blk1_iff Q hb0 q c).mpr hR
    have hG : gram Q (fun i => eX i) = (blk1 b₀ q₀ c₀).map (algebraMap R F) := by
      rw [map_blk1, hb₀, hq, hc]; exact heX
    have hGu : IsUnit (blk1 b₀ q₀ c₀).det := by rw [det_blk1]; exact hunit
    obtain ⟨hMU, -, -, -⟩ := Eng93.span_basis_props Q eX hGu hG
    have hg := normGroup_eq_of_blk1 Q h2p hπ hfg hU ha hb hodd hqb hc₀ hcg (by rw [hc]; exact heX) hMU
    obtain ⟨bL, hbL⟩ := Eng93.exists_basis_gram_of_normGroup_eq Q hfg hU hspan eX hGu hG hg
    exact ⟨bL, by rw [hbL, map_blk1, hb₀, hq, hc]⟩
  have hdJ : (b * 0 - 1) * -dF = dF := by ring
  have hdK : (b * sK - 1) * -(dF * eF') = dF * eF' * eF' := by
    rw [hsKdef, heF']; field_simp; ring
  -- not both
  have notBoth : ¬ (HasBlk1 Q L b 0 (-dF) ∧ HasBlk1 Q L b sK (-(dF * eF'))) := by
    rintro ⟨hJ, hKb⟩
    have hRJ := (rep_blk1_iff Q hb0 _ _).mp (rep_of_hasBlk1 Q hV hJ (by rw [hdJ]; exact hd0))
    have hRK := (rep_blk1_iff Q hb0 _ _).mp
      (rep_of_hasBlk1 Q hV hKb (by rw [hdK]; exact mul_ne_zero (mul_ne_zero hd0 he0) he0))
    have hJK := ((rep_diag_iff_S Q hK hwJ0 hwK0 hRJ).mp hRK).2
    rw [← hJK] at hP
    rcases hasseS_pm' wJ with h | h <;> rw [h] at hP <;> norm_num at hP
  have hcJ : algebraMap R F (-d) = -dF := by rw [map_neg]
  have hcK : algebraMap R F (-(d * (1 - 4 * ρ))) = -(dF * eF') := by
    rw [hdF, heF']; simp only [map_neg, map_sub, map_one, map_mul, map_ofNat]
  have caseJ : hasseS F w = hasseS F wJ → Xor' (HasBlk1 Q L b 0 (-dF)) (HasBlk1 Q L b sK (-(dF * eF'))) :=
    fun h => by
      have hJ := toBlk 0 (-d) (map_zero _) hcJ hzb hdu.neg hmd huJ (iffJ.mpr ⟨hdiscJ, h⟩)
      exact Or.inl ⟨hJ, fun hKb => notBoth ⟨hJ, hKb⟩⟩
  have caseK : hasseS F w = hasseS F wK → Xor' (HasBlk1 Q L b 0 (-dF)) (HasBlk1 Q L b sK (-(dF * eF'))) :=
    fun h => by
      have hKb := toBlk _ _ hsK.symm hcK hsKb hdKu hmdK huK (iffK.mpr ⟨hdiscK, h⟩)
      exact Or.inr ⟨hKb, fun hJ => notBoth ⟨hJ, hKb⟩⟩
  rcases hasseS_pm' w with h | h <;> rcases hasseS_pm' wJ with h' | h' <;>
    rcases hasseS_pm' wK with h'' | h'' <;> rw [h', h''] at hP <;> norm_num at hP
  · exact caseJ (by rw [h, h'])
  · exact caseK (by rw [h, h''])
  · exact caseK (by rw [h, h''])
  · exact caseJ (by rw [h, h'])

end Main

end QuadFormsKB.OMeara.D18
