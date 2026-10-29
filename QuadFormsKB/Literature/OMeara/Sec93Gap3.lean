/-
# O'Meara 93:10: a binary unimodular lattice is $A(a, \beta)$ with $\beta \in \mathfrak wL$

**Setting** (as in `Sec93Gap2.lean`): $R$ a Henselian discrete valuation ring with finite residue field, $F$ its
fraction field, $2 \in F^\times$, $F$ dyadic ($2$ not a unit of $R$); $(V, Q)$ a quadratic space over $F$, O'Meara's
$B$ = `bil Q`, lattices = `Submodule R V`. $L \cong A(\alpha, \beta)$ is `HasMatrixA Q L α β` (`Sec93.lean`): $L$ has a
base with matrix $\begin{pmatrix}\alpha & 1\\ 1 & \beta\end{pmatrix}$ and $-1 + 4\alpha\beta$ is a unit.

**Proves** (O'Meara 1963, §93B, p. 255)
* `exists_hasMatrixA` (**93:10 (i)**): if $L$ is a binary unimodular lattice and $a = Q(x)$, $x \in L$, is a norm
  generator of $L$, then $L \cong A(a, \beta)$ for some $\beta \in \mathfrak wL$; moreover the base can be taken with
  first vector $x$.

**Proof** (O'Meara's): $x$ is a maximal vector; pick $y \in L$ with $\det\begin{pmatrix}a & B(x,y)\\ B(x,y) &
Q(y)\end{pmatrix}$ a unit (here: by 82:17 if $a \in \mathfrak p$, and from the splitting $L = \mathfrak ox \perp K$ if
$a$ is a unit, instead of O'Meara's "there is $y$ with $L = \mathfrak ox + \mathfrak oy$"); by 93:4,
$Q(y) \equiv a\xi^2 \bmod \mathfrak wL$; then $Q(y + \xi x) \in \mathfrak wL \subseteq \mathfrak p$, so
$B(x, y + \xi x)$ is a unit, and $z = (y + \xi x)/B(x, y + \xi x)$ gives the base $x, z$. Part (ii) of 93:10 is not
formalized.
-/
import QuadFormsKB.Literature.OMeara.Sec93Gap2
import QuadFormsKB.Literature.OMeara.Sec93Unimodular
import QuadFormsKB.Literature.OMeara.Sec92SpinorUnits

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section A10

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

omit [HenselianLocalRing R] [Finite (ResidueField R)] in
/-- Two vectors of a binary unimodular lattice with a unimodular matrix span the lattice. -/
theorem a10_span_eq {L : Submodule R V} (hfg : L.FG) (hL : IsUnimodular Q L) (hrk : finrank R L = 2)
    {v : Fin 2 → V} (hv : ∀ i, v i ∈ L) {U : Matrix (Fin 2) (Fin 2) R} (hU : IsUnit U.det)
    (hG : gram Q v = (1 : F) • U.map (algebraMap R F)) : span R (Set.range v) = L := by
  obtain ⟨hmod, hrkJ⟩ := isModular_span_of_gram Q one_ne_zero hU hG
  have hJL : span R (Set.range v) ≤ L := by rw [span_le]; rintro _ ⟨i, rfl⟩; exact hv i
  have hsc : scale Q L = R ∙ (1 : F) := by rw [hL.2.1, ← Submodule.one_eq_span]
  obtain ⟨K, hK⟩ := splits_of_isModular_of_scale_eq Q hJL hmod (fg_span (Set.finite_range v)) hsc
  have hr := isOrthSum_finrank Q hK hfg
  rw [hrk, hrkJ, Fintype.card_fin] at hr
  have hK0 : K = ⊥ := by
    have hKfg : K.FG := FG.of_le hfg (hK.sup_eq ▸ le_sup_right)
    obtain ⟨b⟩ := exists_basis (R := R) (F := F) hKfg
    rw [← span_basis_eq b]
    have : IsEmpty (Fin (finrank R K)) := by rw [show finrank R K = 0 by omega]; infer_instance
    rw [Set.range_eq_empty, span_empty]
  rw [← hK.sup_eq, hK0, sup_bot_eq]

omit [Finite (ResidueField R)] in
/-- For a unimodular lattice over a dyadic field, $\mathfrak wL \subseteq \mathfrak p$. -/
theorem a10_weight_le (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hL : IsUnimodular Q L) {w : F}
    (hw : w ∈ weight Q L) : ∃ r ∈ maximalIdeal R, algebraMap R F r = w := by
  have hs : scale Q L = 1 := hL.2.1
  have hle : weight Q L ≤ Submodule.map (Algebra.linearMap R F) (maximalIdeal R) := by
    refine sup_le ?_ ?_
    · rw [Submodule.mul_le]
      rintro _ ⟨m, hm, rfl⟩ z hz
      have hz1 : z ∈ (1 : Submodule R F) :=
        hs ▸ normIdeal_le_scale Q L (normGroupIdeal_le_normIdeal Q L hz)
      obtain ⟨c, rfl⟩ := Submodule.mem_one.mp hz1
      exact ⟨m * c, Ideal.mul_mem_right _ _ hm, by simp⟩
    · rintro _ ⟨c, hc, rfl⟩
      rw [hs] at hc
      obtain ⟨c', rfl⟩ := Submodule.mem_one.mp hc
      exact ⟨2 * c', Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).mpr h2p), by simp [smul_eq_mul]; exact Or.inl (map_ofNat (algebraMap R F) 2)⟩
  obtain ⟨r, hr, h⟩ := hle hw
  exact ⟨r, hr, h⟩

omit [HenselianLocalRing R] [Finite (ResidueField R)] in
theorem a10_mem_one {L : Submodule R V} (hL : IsUnimodular Q L) {x y : V} (hx : x ∈ L) (hy : y ∈ L) :
    ∃ r : R, algebraMap R F r = bil Q x y := by
  have := bil_mem_scale Q hx hy
  rw [hL.2.1] at this
  exact Submodule.mem_one.mp this

omit [HenselianLocalRing R] [Finite (ResidueField R)] in
/-- A vector $x$ with $Q(x)$ a non-zero norm generator is maximal. -/
theorem a10_isMaxVec {L : Submodule R V} {x : V} (hx : x ∈ L) (ha : IsNormGenerator Q L (Q x)) (ha0 : Q x ≠ 0) :
    IsMaxVec F L x := by
  refine ⟨hx, fun c hc => ?_⟩
  have h1 : Q (c • x) ∈ R ∙ Q x := ha.2 ▸ Q_mem_normIdeal Q hc
  rw [Q_smul] at h1
  obtain ⟨d, hd⟩ := mem_span_singleton.mp h1
  have : c ^ 2 = algebraMap R F d := by
    rw [Algebra.smul_def] at hd
    exact (mul_right_cancel₀ ha0 hd).symm
  obtain ⟨δ, hδ⟩ := exists_alg_of_sq this
  exact ⟨δ, hδ⟩

omit [HenselianLocalRing R] [Finite (ResidueField R)] in
/-- A partner $y$ of $x$ with unimodular matrix $(B(x_i, x_j))$ for $x_0 = x$, $x_1 = y$. -/
theorem a10_exists_partner {L : Submodule R V} (hfg : L.FG) (hL : IsUnimodular Q L) (hrk : finrank R L = 2)
    {x : V} (hx : x ∈ L) {α : R} (hQx : Q x = algebraMap R F α) (ha : IsNormGenerator Q L (Q x))
    (ha0 : Q x ≠ 0) :
    ∃ y ∈ L, ∃ e q : R, bil Q x y = algebraMap R F e ∧ Q y = algebraMap R F q ∧ IsUnit (α * q - e ^ 2) := by
  by_cases hα : IsUnit α
  · -- `𝔬x` is unimodular and splits `L`
    obtain ⟨hJ, hJrk⟩ := u93_isUnimodular_span_singleton Q hα hQx
    have hJL : R ∙ x ≤ L := (span_singleton_le_iff_mem _ _).mpr hx
    obtain ⟨K, hK⟩ := splits_of_isModular_of_scale_eq Q hJL hJ (fg_span_singleton x)
      (by rw [hL.2.1])
    have hr := isOrthSum_finrank Q hK hfg
    rw [hrk, hJrk] at hr
    have hKfg : K.FG := FG.of_le hfg (hK.sup_eq ▸ le_sup_right)
    have hK0 : K ≠ ⊥ := by
      rintro rfl; simp at hr
    have hKu := u93_isUnimodular_of_orth Q hfg hL hJ hK hK0
    obtain ⟨b⟩ := exists_basis (R := R) (F := F) hKfg
    have hKrk : finrank R K = 1 := by omega
    have hne : Nonempty (Fin (finrank R K)) := ⟨⟨0, by omega⟩⟩
    obtain ⟨-, U, hU, hG⟩ := (isModular_iff_gram Q b (one_ne_zero : (1 : F) ≠ 0)).mp
      (by rw [← Submodule.one_eq_span]; exact hKu)
    let i0 : Fin (finrank R K) := ⟨0, by omega⟩
    have hdet : U.det = U i0 i0 := by
      have : ∀ i : Fin (finrank R K), i = i0 := fun i => Fin.ext (by have := i.2; omega)
      have : Unique (Fin (finrank R K)) := ⟨⟨i0⟩, this⟩
      exact (Matrix.det_unique U).trans (congrArg₂ U (Subsingleton.elim _ _) (Subsingleton.elim _ _))
    refine ⟨b i0, hK.sup_eq ▸ mem_sup_right (b i0).2, 0, U i0 i0, ?_, ?_, ?_⟩
    · rw [map_zero]; exact hK.orth x (mem_span_singleton_self x) _ (b i0).2
    · have := congrFun (congrFun hG i0) i0
      simpa [gram, bil_self] using this
    · rw [← hdet]; simpa using hα.mul hU
  · -- `α ∈ 𝔭`: 82:17 gives `y` with `B(x, y)` a unit
    have hmax := a10_isMaxVec Q hx ha ha0
    obtain ⟨y, hy, hxy⟩ := exists_bil_unit_of_isMaxVec Q hfg
      (by rw [← Submodule.one_eq_span]; exact hL) hmax
    obtain ⟨e, he, hbe⟩ := u93_unit_of_span_eq_one (hxy.trans (Submodule.one_eq_span).symm)
    obtain ⟨q, hq⟩ := a10_mem_one Q hL hy hy
    rw [bil_self] at hq
    refine ⟨y, hy, e, q, hbe, hq.symm, ?_⟩
    exact u93_isUnit_sub_of_nonunit (fun h => hα (isUnit_of_mul_isUnit_left h)) (he.pow 2)

/-- **Example 93:10 (i)** (O'Meara 1963, p. 255): let $L$ be a binary unimodular lattice over a dyadic local field and
let $a = Q(x)$, $x \in L$, be a norm generator of $L$ (here $a = \alpha \in \mathfrak o$). Then $L \cong A(a, \beta)$
for some $\beta \in \mathfrak wL$, in a base whose first vector is $x$. -/
@[kb "omeara1963" "§93B, 93:10 (i), p. 255"]
theorem exists_hasMatrixA (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG) (hL : IsUnimodular Q L)
    (hrk : finrank R L = 2) {x : V} (hx : x ∈ L) {α : R} (hQx : Q x = algebraMap R F α)
    (ha : IsNormGenerator Q L (Q x)) :
    ∃ β : R, algebraMap R F β ∈ weight Q L ∧ IsUnit (-1 + 4 * α * β) ∧ ∃ b : Basis (Fin 2) R L,
      (b 0 : V) = x ∧ gram Q (fun i => (b i : V)) = matA (algebraMap R F α) (algebraMap R F β) := by
  have hne : L ≠ ⊥ := by rintro rfl; simp at hrk
  have hreg : IsRegular Q L := IsModular.isRegular Q hL hfg
  have ha0 : Q x ≠ 0 := ha.ne_zero Q hreg hne
  obtain ⟨y, hy, e, q, he, hq, hdet⟩ := a10_exists_partner Q hfg hL hrk hx hQx ha ha0
  -- 93:4: `Q(y) ≡ a ξ² mod 𝔴L`
  obtain ⟨ξ, hξ⟩ := exists_sub_sq_mem_weight Q h2p ha ha0 (Q_mem_normGroup Q hy)
  set y' := y + ξ • x with hy'
  have hy'L : y' ∈ L := L.add_mem hy (L.smul_mem ξ hx)
  have hQy' : Q y' ∈ weight Q L := by
    have h2 : 2 * (algebraMap R F (α * ξ ^ 2 + ξ * e)) ∈ weight Q L := by
      refine le_sup_right (a := Submodule.map (Algebra.linearMap R F) (maximalIdeal R) * normGroupIdeal Q L) ?_
      have : algebraMap R F (α * ξ ^ 2 + ξ * e) ∈ scale Q L := by
        rw [hL.2.1]; exact Submodule.mem_one.mpr ⟨_, rfl⟩
      exact Submodule.smul_mem_pointwise_smul _ (2 : F) _ this
    have : Q y' = (Q y - Q x * algebraMap R F ξ ^ 2) + 2 * algebraMap R F (α * ξ ^ 2 + ξ * e) := by
      rw [hy', Q_add, Q_rsmul, bil_rsmul_right, bil_comm Q y x, he, hQx]; simp only [map_add, map_mul, map_pow]
      ring
    rw [this]; exact add_mem hξ h2
  obtain ⟨q', hq'p, hq'⟩ := a10_weight_le Q h2p hL hQy'
  set e' := e + ξ * α with he'
  have hbe' : bil Q x y' = algebraMap R F e' := by
    rw [hy', bil_add_right, bil_rsmul_right, bil_self, he, hQx, he']; simp [map_add, map_mul]
  have hdet' : α * q' - e' ^ 2 = α * q - e ^ 2 := by
    apply IsFractionRing.injective R F
    have hq1 : algebraMap R F q' = Q y + 2 * algebraMap R F ξ * algebraMap R F e + algebraMap R F ξ ^ 2 *
        algebraMap R F α := by
      rw [hq', hy', Q_add, Q_rsmul, bil_rsmul_right, bil_comm Q y x, he, hQx]; ring
    simp only [map_sub, map_mul, map_pow, he', map_add, hq1, hq]; ring
  have he'u : IsUnit e' := by
    have h1 : ¬ IsUnit (α * q') := fun h => (mem_maximalIdeal _).mp (Ideal.mul_mem_left _ α hq'p)
      h
    have h2 : IsUnit (α * q' - (α * q' - e' ^ 2)) := by
      rw [hdet']; exact u93_isUnit_sub_of_nonunit h1 (by exact hdet)
    rw [sub_sub_cancel] at h2
    exact isUnit_of_mul_isUnit_left (by rwa [pow_two] at h2)
  obtain ⟨f, hf⟩ := he'u.exists_left_inv
  have hfF : algebraMap R F f * algebraMap R F e' = 1 := by rw [← map_mul, hf, map_one]
  set z := f • y' with hz
  set β := q' * f ^ 2 with hβ
  have hzL : z ∈ L := L.smul_mem f hy'L
  have hxz : bil Q x z = 1 := by rw [hz, bil_rsmul_right, hbe', hfF]
  have hQz : Q z = algebraMap R F β := by
    rw [hz, Q_rsmul, ← hq', hβ, map_mul, map_pow]; ring
  have hβw : algebraMap R F β ∈ weight Q L := by
    rw [hβ, map_mul, mul_comm, ← Algebra.smul_def, hq']; exact smul_mem _ _ hQy'
  have hβp : β ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hq'p
  let v : Fin 2 → V := ![x, z]
  let U : Matrix (Fin 2) (Fin 2) R := !![α, 1; 1, β]
  have hUdet : IsUnit U.det := by
    have : U.det = -1 + α * β := by simp [U, Matrix.det_fin_two_of]; ring
    rw [this, add_comm]
    exact u93_isUnit_add_of_nonunit (fun h => (mem_maximalIdeal _).mp (Ideal.mul_mem_left _ α hβp) h)
      isUnit_one.neg
  have hG : gram Q v = (1 : F) • U.map (algebraMap R F) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [v, U, gram, hQx, hQz, hxz, bil_comm Q z x]
  have hspan := a10_span_eq Q hfg hL hrk (v := v) (fun i => by fin_cases i <;> simp [v, hx, hzL]) hUdet hG
  have hli : LinearIndependent R v := by
    refine linearIndependent_of_det_gram_ne_zero Q ?_
    rw [hG, Matrix.det_smul, one_pow, one_mul]
    have hd : (U.map (algebraMap R F)).det = algebraMap R F U.det :=
      (RingHom.map_det (algebraMap R F) U).symm
    rw [hd]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hUdet.ne_zero
  let b : Basis (Fin 2) R L := (Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  have hb : ∀ i, (b i : V) = v i := fun i => by simp [b]
  refine ⟨β, hβw, ?_, b, by rw [hb]; rfl, ?_⟩
  · have : -1 + 4 * α * β = -1 + α * (4 * β) := by ring
    rw [this, add_comm]
    exact u93_isUnit_add_of_nonunit
      (fun h => (mem_maximalIdeal _).mp (Ideal.mul_mem_left _ α (Ideal.mul_mem_left _ 4 hβp)) h) isUnit_one.neg
  · have : (fun i => (b i : V)) = v := funext hb
    rw [this, hG]
    ext i j; fin_cases i <;> fin_cases j <;> simp [U, matA]

/-- The values of a lattice with matrix $A(\alpha, \beta)$ in the base $b$:
$Q(\xi b_0 + \eta b_1) = \alpha\xi^2 + 2\xi\eta + \beta\eta^2$. -/
theorem a10_Q_eq {L : Submodule R V} {α β : R} (b : Basis (Fin 2) R L)
    (hb : gram Q (fun i => (b i : V)) = matA (algebraMap R F α) (algebraMap R F β)) {y : V} (hy : y ∈ L) :
    ∃ ξ η : R, Q y = algebraMap R F α * algebraMap R F ξ ^ 2 + 2 * (algebraMap R F ξ * algebraMap R F η) +
      algebraMap R F β * algebraMap R F η ^ 2 := by
  have hsum := congrArg (fun w : L => (w : V)) (b.sum_repr ⟨y, hy⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Fin.sum_univ_two] at hsum
  have hg : ∀ i j, bil Q (b i : V) (b j : V) = matA (algebraMap R F α) (algebraMap R F β) i j := fun i j => by
    rw [← hb]; rfl
  refine ⟨b.repr ⟨y, hy⟩ 0, b.repr ⟨y, hy⟩ 1, ?_⟩
  refine (congrArg Q hsum).symm.trans ?_
  push_cast
  rw [Q_add, Q_rsmul, Q_rsmul, bil_rsmul_left, bil_rsmul_right, ← bil_self Q (b 0 : V),
    ← bil_self Q (b 1 : V), hg, hg, hg]
  simp [matA]; ring

/-- **Example 93:10 (ii)** (O'Meara 1963, p. 255), in the form $\mathfrak wL = \beta\mathfrak o + 2(\mathfrak sL)$: over
a dyadic local field, if the lattice $L$ has a base with matrix $A(\alpha, \beta)$, $\alpha$ a norm generator of $L$ and
$\beta \in \mathfrak wL$ (as in 93:10 (i)), then $\mathfrak wL = \beta\mathfrak o + 2(\mathfrak sL)$. -/
theorem weight_eq_of_matA (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hreg : IsRegular Q L) (hne : L ≠ ⊥)
    {α β : R} (ha : IsNormGenerator Q L (algebraMap R F α)) (hβw : algebraMap R F β ∈ weight Q L)
    (b : Basis (Fin 2) R L) (hb : gram Q (fun i => (b i : V)) = matA (algebraMap R F α) (algebraMap R F β)) :
    weight Q L = (R ∙ algebraMap R F β) ⊔ (2 : F) • scale Q L := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have ha0 := ha.ne_zero Q hreg hne
  have h2le : (2 : F) • scale Q L ≤ weight Q L := (weight_bounds Q L).2.2.1
  have hSw : (R ∙ algebraMap R F β) ⊔ (2 : F) • scale Q L ≤ weight Q L :=
    sup_le ((span_singleton_le_iff_mem _ _).mpr hβw) h2le
  have := weight_eq_sup Q h2p hπ ha ha0 hSw ?_
  · rw [this, sup_assoc, sup_idem]
  intro y hy hQ hodd
  obtain ⟨ξ, η, hQy⟩ := a10_Q_eq Q b hb hy
  set A := algebraMap R F α * algebraMap R F ξ ^ 2
  set C := algebraMap R F β * algebraMap R F η ^ 2
  set D := 2 * (algebraMap R F ξ * algebraMap R F η)
  have hD : D ∈ (2 : F) • scale Q L := by
    have hb01 : algebraMap R F (ξ * η) = algebraMap R F ξ * algebraMap R F η := map_mul _ _ _
    have hsc : algebraMap R F (ξ * η) * bil Q (b 0 : V) (b 1 : V) ∈ scale Q L := by
      rw [← Algebra.smul_def]; exact smul_mem _ _ (bil_mem_scale Q (b 0).2 (b 1).2)
    have h01 : bil Q (b 0 : V) (b 1 : V) = 1 := by
      have := congrFun (congrFun hb 0) 1; simpa [gram, matA] using this
    rw [h01, mul_one, hb01] at hsc
    exact Submodule.smul_mem_pointwise_smul _ (2 : F) _ hsc
  have hsplit : Q y = (A + C) + D := by rw [hQy]; ring
  by_cases h1 : D ≠ 0 ∧ dord hπ D ≤ dord hπ (Q y)
  · refine mem_sup_right ?_
    have : Q y ∈ R ∙ D := (mem_span_iff hπ hQ h1.1).mpr h1.2
    exact (span_singleton_le_iff_mem _ _).mpr hD this
  have hs : A + C ≠ 0 ∧ dord hπ (A + C) = dord hπ (Q y) := by
    by_cases hD0 : D = 0
    · rw [hD0, add_zero] at hsplit; rw [← hsplit]; exact ⟨hQ, rfl⟩
    have hlt : dord hπ (Q y) < dord hπ (-D) := by
      rw [dord_neg hπ hD0]; push_neg at h1; exact h1 hD0
    have hsum : Q y + -D ≠ 0 := by
      intro h
      have : Q y = D := by linear_combination h
      rw [this, dord_neg hπ hD0] at hlt; omega
    have := dord_add_of_lt hπ hQ (neg_ne_zero.mpr hD0) hsum hlt
    have he : Q y + -D = A + C := by rw [hsplit]; ring
    rw [he] at this hsum
    exact ⟨hsum, this⟩
  by_cases h2 : C ≠ 0 ∧ dord hπ C ≤ dord hπ (A + C)
  · refine mem_sup_left ?_
    have hQs : Q y ∈ R ∙ (A + C) := (mem_span_iff hπ hQ hs.1).mpr hs.2.le
    have hsC : A + C ∈ R ∙ C := (mem_span_iff hπ hs.1 h2.1).mpr h2.2
    have hCβ : C ∈ R ∙ algebraMap R F β := by
      show algebraMap R F β * algebraMap R F η ^ 2 ∈ _
      rw [mul_comm, ← map_pow, ← Algebra.smul_def]; exact smul_mem _ _ (mem_span_singleton_self _)
    exact (span_singleton_le_iff_mem _ _).mpr ((span_singleton_le_iff_mem _ _).mpr hCβ hsC) hQs
  exfalso
  have hA : A ≠ 0 ∧ dord hπ A = dord hπ (A + C) := by
    by_cases hC0 : C = 0
    · rw [hC0, add_zero] at hs ⊢; exact ⟨hs.1, rfl⟩
    have hlt : dord hπ (A + C) < dord hπ (-C) := by
      rw [dord_neg hπ hC0]; push_neg at h2; exact h2 hC0
    have hsum : A + C + -C ≠ 0 := by
      intro h
      have hA0 : A = 0 := by linear_combination h
      rw [hA0, zero_add] at hlt; rw [dord_neg hπ hC0] at hlt; omega
    have := dord_add_of_lt hπ hs.1 (neg_ne_zero.mpr hC0) hsum hlt
    simp only [add_neg_cancel_right] at this hsum
    exact ⟨hsum, this⟩
  have hξ : algebraMap R F ξ ≠ 0 := fun h => hA.1 (by simp only [A, h]; ring)
  have hdA : dord hπ A = dord hπ (algebraMap R F α) + 2 * dord hπ (algebraMap R F ξ) := by
    simp only [A]; rw [dord_mul hπ ha0 (pow_ne_zero 2 hξ), dord_sq hπ hξ]
  rw [hA.2, hs.2] at hdA
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **Example 93:10 (ii)** (O'Meara 1963, p. 255): in the situation of 93:10 (i) ($L$ binary unimodular over a dyadic
local field, $L \cong A(a, \beta)$ with $a$ a norm generator and $\beta \in \mathfrak wL$), if
$\mathfrak wL \supsetneq 2\mathfrak o$ then $\beta$ is a weight generator of $L$. -/
@[kb "omeara1963" "§93B, 93:10 (ii), p. 255"]
theorem isWeightGenerator_of_matA (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG)
    (hL : IsUnimodular Q L) {α β : R} (ha : IsNormGenerator Q L (algebraMap R F α))
    (hβw : algebraMap R F β ∈ weight Q L) (b : Basis (Fin 2) R L)
    (hb : gram Q (fun i => (b i : V)) = matA (algebraMap R F α) (algebraMap R F β))
    (hw : (2 : F) • scale Q L < weight Q L) : IsWeightGenerator Q L (algebraMap R F β) := by
  have hne : L ≠ ⊥ := by
    rintro rfl
    have := hL.2.1; rw [scale_bot] at this; have h1 : (1 : F) ∈ (1 : Submodule R F) := Submodule.mem_one.mpr ⟨1, map_one _⟩
    rw [← this] at h1
    exact one_ne_zero ((Submodule.mem_bot R).mp h1)
  have hreg : IsRegular Q L := IsModular.isRegular Q hL hfg
  have heq := weight_eq_of_matA Q h2p hreg hne ha hβw b hb
  unfold IsWeightGenerator
  rw [heq] at hw ⊢
  -- in a discrete valuation ring the ideals form a chain: compare `β𝔬` with `2𝔬`
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hs1 : scale Q L = 1 := hL.2.1
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  by_cases hle : (algebraMap R F β = 0) ∨ dord hπ (2 : F) < dord hπ (algebraMap R F β)
  · exfalso
    have : R ∙ algebraMap R F β ≤ (2 : F) • scale Q L := by
      rw [span_singleton_le_iff_mem]
      rcases hle with h0 | hlt
      · rw [h0]; exact zero_mem _
      have hβ0 : algebraMap R F β ≠ 0 := by
        intro h0
        have h00 : dord hπ (0 : F) = 0 := by simp [dord]
        rw [h0, h00] at hlt
        have := dord_four_nonneg (F := F) hπ (two_ne_zero_R (F := F))
        rw [show (4 : F) = 2 * 2 by norm_num, dord_mul hπ h2F h2F] at this; omega
      have hq : algebraMap R F β / 2 ≠ 0 := div_ne_zero hβ0 h2F
      have hdq : 0 ≤ dord hπ (algebraMap R F β / 2) := by
        have := dord_mul hπ h2F hq
        rw [mul_div_cancel₀ _ h2F] at this; omega
      obtain ⟨r, hr⟩ := exists_alg_of_nonneg hπ hq hdq
      have : algebraMap R F β = (2 : F) • algebraMap R F r := by
        rw [hr, smul_eq_mul]; field_simp
      rw [this, hs1]
      exact Submodule.smul_mem_pointwise_smul _ (2 : F) _ (Submodule.mem_one.mpr ⟨r, rfl⟩)
    exact hw.ne (sup_eq_right.mpr this).symm
  · push_neg at hle
    refine (sup_eq_left.mpr ?_).symm
    rintro _ ⟨c, hc, rfl⟩
    rw [hs1] at hc
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hc
    simp only [DistribSMul.toLinearMap_apply]
    by_cases hr : algebraMap R F r = 0
    · rw [hr, smul_zero]; exact zero_mem _
    rw [smul_eq_mul, mem_span_iff hπ (mul_ne_zero h2F hr) hle.1, dord_mul hπ h2F hr]
    have := dord_alg_nonneg (F := F) hπ (fun h : r = 0 => hr (by rw [h, map_zero]))
    omega

end A10

end QuadFormsKB.OMeara
