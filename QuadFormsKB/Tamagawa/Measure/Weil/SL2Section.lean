import QuadFormsKB.Tamagawa.Measure.Weil.SL2Adele

/-!
# Coordinates on $\mathrm{SL}_2(\mathbb A_F)$ along the orbit map $g\mapsto g e_1$

$F$ any number field. The orbit map $g\mapsto g e_1$ (the first column) identifies
$\mathrm{SL}_2(\mathbb A_F)/N(\mathbb A_F)$, $N = \{n(x)\}$, $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$, with the set
$P\subseteq\mathbb A_F^2$ of **primitive vectors** (`primSet`): $(a, c)$ with $(a_v, c_v)\ne 0$ at every place and
$(a_v, c_v)$ a primitive vector of $\mathcal O_v^2$ for almost all finite $v$. We construct an explicit measurable section
$s : P\to\mathrm{SL}_2(\mathbb A_F)$, $s(y)e_1 = y$ (`sec`): place by place,
$$ s_v(a, c) = \begin{pmatrix} a & 0\\ c & a^{-1}\end{pmatrix}\ \ (a\ne0,\ |c/a|_v\le1),\qquad
   s_v(a, c) = \begin{pmatrix} a & -c^{-1}\\ c & 0\end{pmatrix}\ \ \text{otherwise}, $$
which lies in $\mathrm{SL}_2(\mathcal O_v)$ when $(a_v, c_v)$ is primitive. Then
$$ \Psi : P\times\mathbb A_F\to\mathrm{SL}_2(\mathbb A_F),\qquad \Psi(y, x) = s(y)\,n(x) $$
is a **measurable equivalence** (`coordEquiv`), and left translation by $g_0$ becomes the skew product
$(y, x)\mapsto(g_0y,\ x + \beta(g_0, y))$ (`coordEquiv_symm_mul`). This is the concrete form of Weil's fibration
$G\to G/H$ (AAG §2.4, Lemma 2.4.1 / Thm 2.4.3) for $G = \mathrm{SL}_2$, $H = N\cong\mathbb G_a$, $G/H\cong\mathbb A^2\setminus 0$.

The archimedean components use the same formula with $|\cdot|$ the real or complex absolute value; the generic local
formula is `locB`, `locD` (`locB_det`) for a field with a "unit ball" $B\ni 0$.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding
open scoped ENNReal NNReal Pointwise Classical MatrixGroups RestrictedProduct

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

/-! ### The local section -/

section Local

variable {K : Type*} [Field K]

/-- The upper-right entry of the local section $s(a, c)$ (relative to the "unit ball" `B`). -/
def locB (B : Set K) (a c : K) : K := if a ≠ 0 ∧ c * a⁻¹ ∈ B then 0 else -c⁻¹

/-- The lower-right entry of the local section $s(a, c)$. -/
def locD (B : Set K) (a c : K) : K := if a ≠ 0 ∧ c * a⁻¹ ∈ B then a⁻¹ else 0

/-- $\det\begin{pmatrix}a & b\\ c& d\end{pmatrix} = 1$ for the local section, when $(a, c)\ne 0$ and $0\in B$. -/
theorem locB_det {B : Set K} (hB : (0 : K) ∈ B) {a c : K} (h : a ≠ 0 ∨ c ≠ 0) :
    a * locD B a c - locB B a c * c = 1 := by
  unfold locB locD
  split_ifs with hc
  · rw [mul_inv_cancel₀ hc.1, zero_mul, sub_zero]
  · have hc0 : c ≠ 0 := by
      rintro rfl
      rcases h with ha | h
      · exact hc ⟨ha, by rw [zero_mul]; exact hB⟩
      · exact h rfl
    rw [mul_zero, zero_sub, neg_mul, neg_neg, inv_mul_cancel₀ hc0]

theorem measurable_locB [MeasurableSpace K] [MeasurableInv K] [MeasurableMul₂ K] [MeasurableSingletonClass K]
    [MeasurableNeg K]
    {B : Set K} (hB : MeasurableSet B) : Measurable fun p : K × K => locB B p.1 p.2 := by
  unfold locB
  refine Measurable.ite ?_ measurable_const (measurable_snd.inv.neg)
  exact (measurableSet_singleton 0).compl.preimage measurable_fst |>.inter
    (hB.preimage (measurable_snd.mul measurable_fst.inv))

theorem measurable_locD [MeasurableSpace K] [MeasurableInv K] [MeasurableMul₂ K] [MeasurableSingletonClass K]
    {B : Set K} (hB : MeasurableSet B) : Measurable fun p : K × K => locD B p.1 p.2 := by
  unfold locD
  refine Measurable.ite ?_ measurable_fst.inv measurable_const
  exact (measurableSet_singleton 0).compl.preimage measurable_fst |>.inter
    (hB.preimage (measurable_snd.mul measurable_fst.inv))

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- A vector $(a, c)$ of $K^2$ is **primitive** for the valuation `w` if $a, c\in\mathcal O$ and one of them is a unit
(here: nonzero with inverse in $\mathcal O$). -/
def IsPrim (w : Valuation K Γ₀) (a c : K) : Prop :=
  w a ≤ 1 ∧ w c ≤ 1 ∧ ((a ≠ 0 ∧ w a⁻¹ ≤ 1) ∨ (c ≠ 0 ∧ w c⁻¹ ≤ 1))

/-- The local section is integral at a primitive vector: the upper-right entry. -/
theorem locB_integral (w : Valuation K Γ₀) {a c : K} (h : IsPrim w a c) :
    w (locB {x | w x ≤ 1} a c) ≤ 1 := by
  obtain ⟨-, hc, hu⟩ := h
  unfold locB
  split_ifs with hcond
  · simp
  · rw [Valuation.map_neg]
    rcases hu with ⟨ha0, hai⟩ | ⟨-, hci⟩
    · exfalso
      refine hcond ⟨ha0, ?_⟩
      show w (c * a⁻¹) ≤ 1
      rw [Valuation.map_mul]; exact mul_le_one' hc hai
    · exact hci

/-- The local section is integral at a primitive vector: the lower-right entry. -/
theorem locD_integral (w : Valuation K Γ₀) {a c : K} (h : IsPrim w a c) :
    w (locD {x | w x ≤ 1} a c) ≤ 1 := by
  obtain ⟨-, -, hu⟩ := h
  unfold locD
  split_ifs with hcond
  · rcases hu with ⟨-, hai⟩ | ⟨hc0, hci⟩
    · exact hai
    · have : a⁻¹ = (c * a⁻¹) * c⁻¹ := by field_simp
      rw [this, Valuation.map_mul]
      exact mul_le_one' hcond.2 hci
  · simp

/-- Primitivity of the first column of an integral matrix of determinant $1$. -/
theorem isPrim_of_det (w : Valuation K Γ₀) {a b c d : K} (ha : w a ≤ 1) (hb : w b ≤ 1) (hc : w c ≤ 1)
    (hd : w d ≤ 1) (hdet : a * d - b * c = 1) : IsPrim w a c := by
  refine ⟨ha, hc, ?_⟩
  by_contra hno
  push Not at hno
  -- both `a` and `c` lie in the maximal ideal
  have hlt : ∀ x : K, w x ≤ 1 → (x ≠ 0 → 1 < w x⁻¹) → w x < 1 := by
    intro x hx hxi
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · have := hxi hx0
      rw [map_inv₀] at this
      exact lt_of_le_of_ne hx fun h => by rw [h, inv_one] at this; exact lt_irrefl _ this
  have ha' := hlt a ha hno.1
  have hc' := hlt c hc hno.2
  have h1 : w (a * d - b * c) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
    · rw [Valuation.map_mul]
      exact lt_of_lt_of_le (mul_lt_one_of_lt_of_le ha' hd) le_rfl
    · rw [Valuation.map_mul]
      calc w b * w c ≤ 1 * w c := mul_le_mul_left hb _
        _ = w c := one_mul _
        _ < 1 := hc'
  rw [hdet, map_one] at h1
  exact lt_irrefl _ h1

end Local

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Primitive vectors in $\mathbb A_F^2$ -/

/-- The finite-place valuation on $F_v$. -/
abbrev valV (v : HeightOneSpectrum (𝓞 F)) : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) :=
  Valued.v

/-- The archimedean "unit ball" at a real place. -/
def ballR : Set ℝ := Metric.closedBall 0 1

/-- The archimedean "unit ball" at a complex place. -/
def ballC : Set ℂ := Metric.closedBall 0 1

theorem zero_mem_ballR : (0 : ℝ) ∈ ballR := Metric.mem_closedBall_self zero_le_one
theorem zero_mem_ballC : (0 : ℂ) ∈ ballC := Metric.mem_closedBall_self zero_le_one

variable (F) in
/-- **Primitive vectors** $P\subseteq\mathbb A_F^2$: $(a, c)\ne 0$ at every place, primitive in $\mathcal O_v^2$ at almost
all finite places. This is the image of the orbit map $g\mapsto ge_1$ (`col_mem_primSet`, `col_sec`). -/
def primSet : Set (AdeleSpace F (Fin 2)) :=
  {y | (∀ w, (y 0).1.1 w ≠ 0 ∨ (y 1).1.1 w ≠ 0) ∧ (∀ w, (y 0).1.2 w ≠ 0 ∨ (y 1).1.2 w ≠ 0) ∧
    (∀ v, (y 0).2 v ≠ 0 ∨ (y 1).2 v ≠ 0) ∧ ∀ᶠ v in cofinite, IsPrim (valV v) ((y 0).2 v) ((y 1).2 v)}

/-! ### The adelic section -/

/-- The archimedean part of the entry `b` of the section. -/
def secBInf (y : AdeleSpace F (Fin 2)) : mixedSpace F :=
  (fun w => locB ballR ((y 0).1.1 w) ((y 1).1.1 w), fun w => locB ballC ((y 0).1.2 w) ((y 1).1.2 w))

/-- The archimedean part of the entry `d` of the section. -/
def secDInf (y : AdeleSpace F (Fin 2)) : mixedSpace F :=
  (fun w => locD ballR ((y 0).1.1 w) ((y 1).1.1 w), fun w => locD ballC ((y 0).1.2 w) ((y 1).1.2 w))

/-- The finite part of the entry `b` of the section (junk `0` off the primitive set). -/
def secBFinOf (y : AdeleSpace F (Fin 2))
    (h : ∀ᶠ v in cofinite, IsPrim (valV v) ((y 0).2 v) ((y 1).2 v)) : AF :=
  ⟨fun v => locB (v.adicCompletionIntegers F) ((y 0).2 v) ((y 1).2 v),
    h.mono fun v hv => locB_integral (valV v) hv⟩

def secBFin (y : AdeleSpace F (Fin 2)) : AF :=
  if h : ∀ᶠ v in cofinite, IsPrim (valV v) ((y 0).2 v) ((y 1).2 v) then secBFinOf y h else 0

/-- The finite part of the entry `d` of the section. -/
def secDFinOf (y : AdeleSpace F (Fin 2))
    (h : ∀ᶠ v in cofinite, IsPrim (valV v) ((y 0).2 v) ((y 1).2 v)) : AF :=
  ⟨fun v => locD (v.adicCompletionIntegers F) ((y 0).2 v) ((y 1).2 v),
    h.mono fun v hv => locD_integral (valV v) hv⟩

def secDFin (y : AdeleSpace F (Fin 2)) : AF :=
  if h : ∀ᶠ v in cofinite, IsPrim (valV v) ((y 0).2 v) ((y 1).2 v) then secDFinOf y h else 0

theorem secBFin_apply (y : AdeleSpace F (Fin 2)) (v : HeightOneSpectrum (𝓞 F)) :
    secBFin y v = if ∀ᶠ v in cofinite, IsPrim (valV v) ((y 0).2 v) ((y 1).2 v) then
      locB (v.adicCompletionIntegers F) ((y 0).2 v) ((y 1).2 v) else 0 := by
  unfold secBFin
  by_cases h : ∀ᶠ v in cofinite, IsPrim (valV v) ((y 0).2 v) ((y 1).2 v)
  · simp only [h, ↓reduceDIte, ↓reduceIte]; rfl
  · simp only [h, ↓reduceDIte, ↓reduceIte]; rfl

theorem secDFin_apply (y : AdeleSpace F (Fin 2)) (v : HeightOneSpectrum (𝓞 F)) :
    secDFin y v = if ∀ᶠ v in cofinite, IsPrim (valV v) ((y 0).2 v) ((y 1).2 v) then
      locD (v.adicCompletionIntegers F) ((y 0).2 v) ((y 1).2 v) else 0 := by
  unfold secDFin
  by_cases h : ∀ᶠ v in cofinite, IsPrim (valV v) ((y 0).2 v) ((y 1).2 v)
  · simp only [h, ↓reduceDIte, ↓reduceIte]; rfl
  · simp only [h, ↓reduceDIte, ↓reduceIte]; rfl

/-- The matrix $\begin{pmatrix} a & b\\ c & d\end{pmatrix}$ of the section at $y = (a, c)$. -/
def secMat (y : AdeleSpace F (Fin 2)) : Matrix (Fin 2) (Fin 2) (Adeles F) :=
  !![y 0, (secBInf y, secBFin y); y 1, (secDInf y, secDFin y)]

theorem secMat_det {y : AdeleSpace F (Fin 2)} (hy : y ∈ primSet F) : (secMat y).det = 1 := by
  obtain ⟨hR, hC, hV, hP⟩ := hy
  rw [Matrix.det_fin_two]
  simp only [secMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) ?_
  · exact locB_det zero_mem_ballR (hR w)
  · exact locB_det zero_mem_ballC (hC w)
  · refine Subtype.ext (funext fun v => ?_)
    show (y 0).2 v * secDFin y v - secBFin y v * (y 1).2 v = 1
    rw [secBFin_apply, secDFin_apply, if_pos hP, if_pos hP]
    exact locB_det (v.adicCompletionIntegers F).zero_mem (hV v)

/-- The section on the primitive set. -/
def secOf (y : AdeleSpace F (Fin 2)) (hy : y ∈ primSet F) : SL2A F := ⟨secMat y, secMat_det hy⟩

/-- **The section** $s : \mathbb A_F^2\to\mathrm{SL}_2(\mathbb A_F)$, $s(y)e_1 = y$ on the primitive set (and $1$
off it). -/
def sec (y : AdeleSpace F (Fin 2)) : SL2A F :=
  if hy : y ∈ primSet F then secOf y hy else 1

theorem sec_apply (y : AdeleSpace F (Fin 2)) (i j : Fin 2) :
    (sec y : Matrix (Fin 2) (Fin 2) (Adeles F)) i j =
      if y ∈ primSet F then secMat y i j else (1 : Matrix (Fin 2) (Fin 2) (Adeles F)) i j := by
  by_cases hy : y ∈ primSet F
  · simp only [sec, hy, ↓reduceDIte, ↓reduceIte]; rfl
  · simp only [sec, hy, ↓reduceDIte, ↓reduceIte, Matrix.SpecialLinearGroup.coe_one]

/-! ### The first column -/

/-- The first column $g e_1$ of a matrix. -/
def col (g : SL2A F) : AdeleSpace F (Fin 2) := fun i => (g : Matrix (Fin 2) (Fin 2) (Adeles F)) i 0

theorem col_sec {y : AdeleSpace F (Fin 2)} (hy : y ∈ primSet F) : col (sec y) = y := by
  funext i
  simp only [col, sec_apply, if_pos hy]
  fin_cases i <;> rfl

theorem col_mul (g h : SL2A F) :
    col (g * h) = Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) (Adeles F)) (col h) := by
  funext i
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- The first column of every $g\in\mathrm{SL}_2(\mathbb A_F)$ is primitive. -/
theorem col_mem_primSet (g : SL2A F) : col g ∈ primSet F := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) (Adeles F)).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  set a := (g : Matrix (Fin 2) (Fin 2) (Adeles F)) 0 0
  set b := (g : Matrix (Fin 2) (Fin 2) (Adeles F)) 0 1
  set c := (g : Matrix (Fin 2) (Fin 2) (Adeles F)) 1 0
  set d := (g : Matrix (Fin 2) (Fin 2) (Adeles F)) 1 1
  have hne : ∀ {K : Type} [Field K] {a b c d : K}, a * d - b * c = 1 → a ≠ 0 ∨ c ≠ 0 := by
    intro K _ a b c d h
    by_contra hh
    push Not at hh
    rw [hh.1, hh.2] at h; simp at h
  refine ⟨fun w => ?_, fun w => ?_, fun v => ?_, ?_⟩
  · show a.1.1 w ≠ 0 ∨ c.1.1 w ≠ 0
    have := congrArg (fun z : Adeles F => z.1.1 w) hdet
    exact hne (b := b.1.1 w) (d := d.1.1 w) (by simpa using this)
  · show a.1.2 w ≠ 0 ∨ c.1.2 w ≠ 0
    have := congrArg (fun z : Adeles F => z.1.2 w) hdet
    exact hne (b := b.1.2 w) (d := d.1.2 w) (by simpa using this)
  · show a.2 v ≠ 0 ∨ c.2 v ≠ 0
    have := congrArg (fun z : Adeles F => z.2 v) hdet
    exact hne (b := b.2 v) (d := d.2 v)
      this
  · show ∀ᶠ v in cofinite, IsPrim (valV v) (a.2 v) (c.2 v)
    have ha : ∀ᶠ v in cofinite, a.2 v ∈ v.adicCompletionIntegers F := a.2.2
    have hb : ∀ᶠ v in cofinite, b.2 v ∈ v.adicCompletionIntegers F := b.2.2
    have hc : ∀ᶠ v in cofinite, c.2 v ∈ v.adicCompletionIntegers F := c.2.2
    have hd : ∀ᶠ v in cofinite, d.2 v ∈ v.adicCompletionIntegers F := d.2.2
    filter_upwards [ha, hb, hc, hd] with v hav hbv hcv hdv
    have := congrArg (fun z : Adeles F => z.2 v) hdet
    exact isPrim_of_det (valV v) hav hbv hcv hdv
      this

/-! ### Measurability -/

/-- `{x | ∀ᶠ i in cofinite, p i x}` is measurable for a countable family of measurable predicates. -/
theorem measurableSet_eventually_cofinite {ι X : Type*} [Countable ι] [MeasurableSpace X] {p : ι → X → Prop}
    (hp : ∀ i, MeasurableSet {x | p i x}) : MeasurableSet {x | ∀ᶠ i in cofinite, p i x} := by
  have : {x | ∀ᶠ i in cofinite, p i x} = ⋃ s : Finset ι, ⋂ i, ⋂ (_ : i ∉ s), {x | p i x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, Filter.eventually_cofinite]
    constructor
    · intro h
      exact ⟨h.toFinset, fun i hi => by by_contra hc; exact hi (by simpa using hc)⟩
    · rintro ⟨s, hs⟩
      exact s.finite_toSet.subset fun i hi => by by_contra hc; exact hi (hs i hc)
  rw [this]
  exact MeasurableSet.iUnion fun s => MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => hp i

/-- Coordinatewise measurability into $\mathbb A_f$. -/
theorem measurable_finiteAdele_of_forall_eval {X : Type*} [MeasurableSpace X] {f : X → AF}
    (hf : ∀ v, Measurable fun x => f x v) : Measurable f :=
  RestrictedProduct.measurable_of_forall_eval isOpen_adicCompletionIntegers hf

theorem measurable_finiteAdele_eval (v : HeightOneSpectrum (𝓞 F)) : Measurable fun x : AF => x v :=
  (show Continuous fun x : AF => x v from RestrictedProduct.continuous_eval v).measurable

theorem measurable_finComp (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) :
    Measurable fun y : AdeleSpace F (Fin 2) => (y i).2 v :=
  (measurable_finiteAdele_eval v).comp (measurable_snd.comp (measurable_pi_apply i))

theorem measurable_realComp (i : Fin 2) (w : {w : InfinitePlace F // w.IsReal}) :
    Measurable fun y : AdeleSpace F (Fin 2) => (y i).1.1 w :=
  (measurable_pi_apply w).comp (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i)))

theorem measurable_complexComp (i : Fin 2) (w : {w : InfinitePlace F // w.IsComplex}) :
    Measurable fun y : AdeleSpace F (Fin 2) => (y i).1.2 w :=
  (measurable_pi_apply w).comp (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i)))

theorem measurableSet_isPrim (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSet {y : AdeleSpace F (Fin 2) | IsPrim (valV v) ((y 0).2 v) ((y 1).2 v)} := by
  have hO := measurableSet_O v
  have h0 := measurable_finComp (F := F) 0 v
  have h1 := measurable_finComp (F := F) 1 v
  have hne : ∀ i : Fin 2, MeasurableSet {y : AdeleSpace F (Fin 2) | (y i).2 v ≠ 0} := fun i =>
    (measurableSet_singleton 0).compl.preimage (measurable_finComp i v)
  unfold IsPrim
  simp only [Set.ofPred_and, Set.ofPred_or]
  exact (hO.preimage h0).inter ((hO.preimage h1).inter
    (((hne 0).inter (hO.preimage h0.inv)).union ((hne 1).inter (hO.preimage h1.inv))))

theorem measurableSet_primSet : MeasurableSet (primSet F) := by
  unfold primSet
  simp only [Set.ofPred_and, Set.ofPred_forall, Set.ofPred_or]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))
  · exact MeasurableSet.iInter fun w =>
      ((measurableSet_singleton 0).compl.preimage (measurable_realComp 0 w)).union
        ((measurableSet_singleton 0).compl.preimage (measurable_realComp 1 w))
  · exact MeasurableSet.iInter fun w =>
      ((measurableSet_singleton 0).compl.preimage (measurable_complexComp 0 w)).union
        ((measurableSet_singleton 0).compl.preimage (measurable_complexComp 1 w))
  · exact MeasurableSet.iInter fun v =>
      ((measurableSet_singleton 0).compl.preimage (measurable_finComp 0 v)).union
        ((measurableSet_singleton 0).compl.preimage (measurable_finComp 1 v))
  · exact measurableSet_eventually_cofinite measurableSet_isPrim

theorem measurable_secBInf : Measurable (secBInf (F := F)) := by
  refine Measurable.prodMk (measurable_pi_iff.mpr fun w => ?_) (measurable_pi_iff.mpr fun w => ?_)
  · exact (measurable_locB (Metric.isClosed_closedBall.measurableSet)).comp
      ((measurable_realComp 0 w).prodMk (measurable_realComp 1 w))
  · exact (measurable_locB (Metric.isClosed_closedBall.measurableSet)).comp
      ((measurable_complexComp 0 w).prodMk (measurable_complexComp 1 w))

theorem measurable_secDInf : Measurable (secDInf (F := F)) := by
  refine Measurable.prodMk (measurable_pi_iff.mpr fun w => ?_) (measurable_pi_iff.mpr fun w => ?_)
  · exact (measurable_locD (Metric.isClosed_closedBall.measurableSet)).comp
      ((measurable_realComp 0 w).prodMk (measurable_realComp 1 w))
  · exact (measurable_locD (Metric.isClosed_closedBall.measurableSet)).comp
      ((measurable_complexComp 0 w).prodMk (measurable_complexComp 1 w))

theorem measurable_secBFin : Measurable (secBFin (F := F)) := by
  refine measurable_finiteAdele_of_forall_eval fun v => ?_
  simp only [secBFin_apply]
  exact Measurable.ite (measurableSet_eventually_cofinite measurableSet_isPrim)
    ((measurable_locB (measurableSet_O v)).comp ((measurable_finComp 0 v).prodMk (measurable_finComp 1 v)))
    measurable_const

theorem measurable_secDFin : Measurable (secDFin (F := F)) := by
  refine measurable_finiteAdele_of_forall_eval fun v => ?_
  simp only [secDFin_apply]
  exact Measurable.ite (measurableSet_eventually_cofinite measurableSet_isPrim)
    ((measurable_locD (measurableSet_O v)).comp ((measurable_finComp 0 v).prodMk (measurable_finComp 1 v)))
    measurable_const

/-- **The section is measurable.** -/
theorem measurable_sec : Measurable (sec (F := F)) := by
  refine measurable_SL2A_iff.mpr fun i j => ?_
  simp only [sec_apply]
  refine Measurable.ite measurableSet_primSet ?_ measurable_const
  fin_cases i <;> fin_cases j
  · exact measurable_pi_apply 0
  · exact measurable_secBInf.prodMk measurable_secBFin
  · exact measurable_pi_apply 1
  · exact measurable_secDInf.prodMk measurable_secDFin

theorem measurable_col : Measurable (col (F := F)) :=
  measurable_pi_iff.mpr fun i => measurable_SL2A_entry i 0

/-! ### The unipotent group $N$ and the coordinates -/

/-- $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}\in\mathrm{SL}_2(\mathbb A_F)$. -/
def nA (x : Adeles F) : SL2A F := ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩

@[simp] theorem nA_apply_01 (x : Adeles F) : (nA x : Matrix (Fin 2) (Fin 2) (Adeles F)) 0 1 = x := rfl

theorem nA_add (x x' : Adeles F) : nA x * nA x' = nA (x + x') := by
  refine Subtype.ext (funext fun i => funext fun j => ?_)
  show ((nA x : Matrix (Fin 2) (Fin 2) (Adeles F)) * (nA x' : Matrix (Fin 2) (Fin 2) (Adeles F))) i j =
    (nA (x + x') : Matrix (Fin 2) (Fin 2) (Adeles F)) i j
  fin_cases i <;> fin_cases j <;> simp [nA, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem col_nA (x : Adeles F) : col (nA x) = col 1 := by
  funext i; fin_cases i <;> rfl

theorem measurable_nA : Measurable (nA (F := F)) := by
  refine measurable_SL2A_iff.mpr fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact measurable_const
  · exact measurable_id
  · exact measurable_const
  · exact measurable_const

/-- An element of $\mathrm{SL}_2$ fixing $e_1$ is unipotent: $h = n(h_{01})$. -/
theorem eq_nA_of_col_eq {h : SL2A F} (hc : col h = col 1) :
    h = nA ((h : Matrix (Fin 2) (Fin 2) (Adeles F)) 0 1) := by
  have h00 : (h : Matrix (Fin 2) (Fin 2) (Adeles F)) 0 0 = 1 := congrFun hc 0
  have h10 : (h : Matrix (Fin 2) (Fin 2) (Adeles F)) 1 0 = 0 := congrFun hc 1
  have hdet : (h : Matrix (Fin 2) (Fin 2) (Adeles F)).det = 1 := h.2
  rw [Matrix.det_fin_two, h00, h10, one_mul, mul_zero, sub_zero] at hdet
  refine Subtype.ext (funext fun i => funext fun j => ?_)
  fin_cases i <;> fin_cases j
  · exact h00
  · rfl
  · exact h10
  · exact hdet

theorem col_inv_sec_mul {g : SL2A F} : col ((sec (col g))⁻¹ * g) = col 1 := by
  have hy := col_sec (col_mem_primSet g)
  calc col ((sec (col g))⁻¹ * g)
      = Matrix.mulVec ((sec (col g))⁻¹ : SL2A F) (col g) := col_mul _ _
    _ = Matrix.mulVec ((sec (col g))⁻¹ : SL2A F) (col (sec (col g))) := by rw [hy]
    _ = col ((sec (col g))⁻¹ * sec (col g)) := (col_mul _ _).symm
    _ = col 1 := by rw [inv_mul_cancel]

variable (F) in
/-- **The coordinates** $g\mapsto(ge_1,\ x)$ with $g = s(ge_1)\,n(x)$. -/
def toCoord (g : SL2A F) : primSet F × Adeles F :=
  (⟨col g, col_mem_primSet g⟩, ((sec (col g))⁻¹ * g : SL2A F) 0 1)

variable (F) in
/-- The inverse coordinates $\Psi(y, x) = s(y)\,n(x)$. -/
def ofCoord (p : primSet F × Adeles F) : SL2A F := sec p.1 * nA p.2

theorem ofCoord_toCoord (g : SL2A F) : ofCoord F (toCoord F g) = g := by
  unfold ofCoord toCoord
  rw [← eq_nA_of_col_eq col_inv_sec_mul, mul_inv_cancel_left]

theorem col_mul_nA (g : SL2A F) (x : Adeles F) : col (g * nA x) = col g := by
  rw [col_mul, col_nA, ← col_mul, mul_one]

theorem toCoord_ofCoord (p : primSet F × Adeles F) : toCoord F (ofCoord F p) = p := by
  obtain ⟨⟨y, hy⟩, x⟩ := p
  have hc : col (sec y * nA x) = y := by rw [col_mul_nA, col_sec hy]
  unfold ofCoord toCoord
  refine Prod.ext (Subtype.ext hc) ?_
  simp only
  rw [hc, inv_mul_cancel_left]
  rfl

theorem toCoord_mul_nA (g : SL2A F) (x : Adeles F) :
    toCoord F (g * nA x) = ((toCoord F g).1, (toCoord F g).2 + x) := by
  unfold toCoord
  refine Prod.ext (Subtype.ext (col_mul_nA g x)) ?_
  simp only
  rw [col_mul_nA, ← mul_assoc]
  conv_lhs => rw [eq_nA_of_col_eq (col_inv_sec_mul (g := g)), nA_add]
  rfl

theorem measurable_toCoord : Measurable (toCoord F) := by
  refine Measurable.prodMk (measurable_col.subtype_mk) ?_
  exact (measurable_SL2A_entry 0 1).comp ((measurable_sec.comp measurable_col).inv.mul measurable_id)

theorem measurable_ofCoord : Measurable (ofCoord F) :=
  (measurable_sec.comp (measurable_subtype_coe.comp measurable_fst)).mul (measurable_nA.comp measurable_snd)

variable (F) in
/-- **$\mathrm{SL}_2(\mathbb A_F)\cong P\times\mathbb A_F$ as measurable spaces**, $g\mapsto(ge_1, x)$,
$g = s(ge_1)n(x)$: the concrete fibration $G\to G/N$ of AAG §2.4 for $G = \mathrm{SL}_2\supset N = \mathbb G_a$. -/
@[kb "weil1982" "§2.4, Lemma 2.4.1 / Thm 2.4.3, pp. 23–26 (fibration G → G/H; here H = N ≅ 𝔾_a, G/H ≅ 𝔸²∖0) [unverified page for 2.4.3]"]
def coordEquiv : SL2A F ≃ᵐ primSet F × Adeles F where
  toFun := toCoord F
  invFun := ofCoord F
  left_inv := ofCoord_toCoord
  right_inv := toCoord_ofCoord
  measurable_toFun := measurable_toCoord
  measurable_invFun := measurable_ofCoord

/-- **Left translation in coordinates is a skew product**: $\Psi^{-1}(g_0\Psi(y, x)) = (\Psi^{-1}(g_0 s(y))_1,\
\Psi^{-1}(g_0 s(y))_2 + x)$, whose first coordinate is $g_0 y$ (`col_mul`, `col_sec`). -/
theorem toCoord_mul_ofCoord (g₀ : SL2A F) (p : primSet F × Adeles F) :
    toCoord F (g₀ * ofCoord F p) =
      ((toCoord F (g₀ * sec p.1)).1, (toCoord F (g₀ * sec p.1)).2 + p.2) := by
  unfold ofCoord
  rw [← mul_assoc, toCoord_mul_nA]

end

end QuadFormsKB.Tamagawa.Measure.Weil
