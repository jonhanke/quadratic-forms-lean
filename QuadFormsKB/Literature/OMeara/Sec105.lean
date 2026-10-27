/-
# O'Meara §105: the indecomposable splitting of a definite lattice

**Layer:** $V = F^n$ over a number field $F$ with the form $Q$ = `Q : QuadForm F n` and the bilinear form
$B(x, y) = x^{\mathsf T}H_Qy$ = `bil Q x y` (so $B(x, x) = 2Q(x)$; O'Meara's $B$ is half of it, which does not change
orthogonality). Lattices and their sublattices are $\mathcal O_F$-submodules of $F^n$; the underlying set of spots is
the set of all finite spots, so O'Meara's "$S$ is definite for $V$" means that $V$ is anisotropic at every infinite
spot.

**Defines** (O'Meara 1973, §105, pp. 321–322)
* `LatOrth Q K₁ K₂`: $B(K_1, K_2) = 0$;
* `IsOrthSplitting Q L S`: the finite set $S$ of non-zero sublattices is an orthogonal splitting
  $L = K_1 \perp \dots \perp K_t$ (the $K_i$ are pairwise orthogonal, independent, and their sum is $L$);
* `IsDecomposable Q K` / `IsIndecomposable Q K` (105.r1): $K = K_1 \perp K_2$ with $K_1, K_2 \ne 0$, or not (and
  $K \ne 0$);
* `IsReducibleVec Q L x` (105.d1): $x = y + z$ with non-zero $y, z \in L$ and $B(y, z) = 0$.

**Proves**
* 105.r1: every $L$ has an indecomposable splitting with at most $n$ components
  (`exists_indecomposable_splitting`);
* Theorem 105:1 (Eichler): if $V$ is totally positive definite, the components of an indecomposable splitting of $L$
  are unique (`indecomposable_splitting_unique`: two indecomposable splittings have the same set of components).

*Deviations.* O'Meara's 105:1 allows a general Dedekind set of spots $S$ containing the dyadic spots and $V$ definite
at the spots outside $S$; here $S$ is the set of all finite spots, so the condition is on the infinite spots only, and
it is stated for a totally positive definite $V$ (`IsTotallyPosDef Q`): O'Meara's definite $V$ may be negative
definite at some real spots, and scaling $V$ by an element of $F$ with suitable signs (weak approximation) reduces to
the positive case, which does not change orthogonality or splittings; that scaling step is not formalized. With $S$
the finite spots, the step "$N(Q(y + z)) > N(Q(y))$" of O'Meara's proof (which uses the Local Square Theorem at the
spots outside $S$) is replaced by the trace: $\operatorname{Tr}Q(y + z) = \operatorname{Tr}Q(y) + \operatorname{Tr}Q(z)$
with $\operatorname{Tr}Q(z) > 0$.
-/
import QuadFormsKB.Lattices.Finite

open NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **Orthogonal sublattices:** $B(K_1, K_2) = 0$. -/
def LatOrth (K₁ K₂ : Submodule (𝓞 F) (Fin n → F)) : Prop := ∀ x ∈ K₁, ∀ y ∈ K₂, bil Q x y = 0

/-- **An orthogonal splitting** $L = K_1 \perp \dots \perp K_t$ of $L$ into the non-zero sublattices of the finite set
$S$ (O'Meara 1973, §82A, p. 220, and §105, p. 321): the $K \in S$ are non-zero, pairwise orthogonal and independent,
and their sum is $L$. -/
@[kb "omeara1963" "§105, p. 321 (orthogonal splitting L = K₁ ⊥ ⋯ ⊥ K_t)"]
structure IsOrthSplitting (L : Submodule (𝓞 F) (Fin n → F)) (S : Finset (Submodule (𝓞 F) (Fin n → F))) :
    Prop where
  ne_bot : ∀ K ∈ S, K ≠ ⊥
  orth : ∀ K ∈ S, ∀ K' ∈ S, K ≠ K' → LatOrth Q K K'
  indep : iSupIndep fun K : S => (K : Submodule (𝓞 F) (Fin n → F))
  sup_eq : S.sup id = L

/-- **A decomposable lattice** (O'Meara 1973, §105, p. 321): $K = K_1 \perp K_2$ with $K_1, K_2 \ne 0$. -/
@[kb "omeara1963" "§105, p. 321 (decomposable lattice)"]
def IsDecomposable (K : Submodule (𝓞 F) (Fin n → F)) : Prop :=
  ∃ K₁ K₂ : Submodule (𝓞 F) (Fin n → F), K₁ ≠ ⊥ ∧ K₂ ≠ ⊥ ∧ LatOrth Q K₁ K₂ ∧ Disjoint K₁ K₂ ∧ K₁ ⊔ K₂ = K

/-- **An indecomposable lattice** (O'Meara 1973, §105, p. 321): a non-zero lattice which is not decomposable. -/
@[kb "omeara1963" "§105, p. 321 (indecomposable lattice)"]
def IsIndecomposable (K : Submodule (𝓞 F) (Fin n → F)) : Prop := K ≠ ⊥ ∧ ¬ IsDecomposable Q K

/-- **A reducible vector** of $L$ (O'Meara 1973, §105, proof of 105:1, p. 322): $x = y + z$ with non-zero
$y, z \in L$ and $B(y, z) = 0$; otherwise $x$ is *irreducible*. -/
@[kb "omeara1963" "§105, p. 322 (reducible and irreducible vectors)"]
def IsReducibleVec (L : Submodule (𝓞 F) (Fin n → F)) (x : Fin n → F) : Prop :=
  ∃ y ∈ L, ∃ z ∈ L, y ≠ 0 ∧ z ≠ 0 ∧ bil Q y z = 0 ∧ x = y + z

/-- Helper (§105): an irreducible vector of $L$: a non-zero element of $L$ which is not reducible in $L$. -/
private def IsIrr (L : Submodule (𝓞 F) (Fin n → F)) (x : Fin n → F) : Prop :=
  x ∈ L ∧ x ≠ 0 ∧ ¬ IsReducibleVec Q L x

/-- Helper (§105): the relation "both irreducible in $L$ and not orthogonal". -/
private def IrrRel (L : Submodule (𝓞 F) (Fin n → F)) (y z : Fin n → F) : Prop :=
  IsIrr Q L y ∧ IsIrr Q L z ∧ bil Q y z ≠ 0

section Helpers

variable {Q}

private theorem bil_add_left' (x y z : Fin n → F) : bil Q (x + y) z = bil Q x z + bil Q y z := by
  simp [bil, add_dotProduct]

private theorem bil_add_right' (x y z : Fin n → F) : bil Q x (y + z) = bil Q x y + bil Q x z := by
  simp [bil, Matrix.mulVec_add, dotProduct_add]

private theorem bil_zero_right' (x : Fin n → F) : bil Q x 0 = 0 := by simp [bil]

private theorem bil_zero_left' (x : Fin n → F) : bil Q 0 x = 0 := by simp [bil]

private theorem bil_sum_right' {ι : Type*} (x : Fin n → F) (s : Finset ι) (f : ι → Fin n → F) :
    bil Q x (∑ i ∈ s, f i) = ∑ i ∈ s, bil Q x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bil_zero_right']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bil_add_right', ih]

private theorem IsOrthSplitting.supIndep {L : Submodule (𝓞 F) (Fin n → F)}
    {S : Finset (Submodule (𝓞 F) (Fin n → F))} (hS : IsOrthSplitting Q L S) : S.SupIndep id :=
  iSupIndep.supIndep (f := id) hS.indep

private theorem IsOrthSplitting.le {L : Submodule (𝓞 F) (Fin n → F)}
    {S : Finset (Submodule (𝓞 F) (Fin n → F))} (hS : IsOrthSplitting Q L S) {K} (hK : K ∈ S) : K ≤ L := by
  rw [← hS.sup_eq]; exact Finset.le_sup (f := id) hK

private theorem exists_sum_of_mem_sup {S : Finset (Submodule (𝓞 F) (Fin n → F))}
    (p : Submodule (𝓞 F) (Fin n → F) → Submodule (𝓞 F) (Fin n → F)) {a : Fin n → F} (h : a ∈ S.sup p) :
    ∃ f : Submodule (𝓞 F) (Fin n → F) → (Fin n → F), (∀ K ∈ S, f K ∈ p K) ∧ ∑ K ∈ S, f K = a := by
  rw [Finset.sup_eq_iSup, Submodule.mem_iSup_finset_iff_exists_sum] at h
  obtain ⟨μ, hμ⟩ := h
  exact ⟨fun K => (μ K : Fin n → F), fun K _ => (μ K).2, hμ⟩

private theorem sum_eq_comp {S : Finset (Submodule (𝓞 F) (Fin n → F))} (hind : S.SupIndep id)
    {K : Submodule (𝓞 F) (Fin n → F)} (hK : K ∈ S) (f : Submodule (𝓞 F) (Fin n → F) → Fin n → F)
    (hf : ∀ J ∈ S, f J ∈ J) (hk : ∑ J ∈ S, f J ∈ K) : ∑ J ∈ S, f J = f K := by
  classical
  have h1 : ∑ J ∈ S, f J - f K = ∑ J ∈ S.erase K, f J := by
    rw [← Finset.add_sum_erase S f hK]; ring
  have h2 : ∑ J ∈ S, f J - f K ∈ K := K.sub_mem hk (hf K hK)
  have h3 : ∑ J ∈ S, f J - f K ∈ (S.erase K).sup id := by
    rw [h1]
    exact Submodule.sum_mem _ fun J hJ =>
      (Finset.le_sup (f := id) hJ : J ≤ (S.erase K).sup id) (hf J (Finset.mem_of_mem_erase hJ))
  have hd := (Finset.supIndep_iff_disjoint_erase.mp hind) K hK
  exact sub_eq_zero.mp ((Submodule.disjoint_def.mp hd) _ h2 h3)

private theorem exists_mem_of_irr {L : Submodule (𝓞 F) (Fin n → F)} {S : Finset (Submodule (𝓞 F) (Fin n → F))}
    (hS : IsOrthSplitting Q L S) {x : Fin n → F} (hx : IsIrr Q L x) : ∃ K ∈ S, x ∈ K := by
  classical
  obtain ⟨hxL, hx0, hxr⟩ := hx
  obtain ⟨f, hf, hsum⟩ := exists_sum_of_mem_sup id (S := S) (a := x) (by rw [hS.sup_eq]; exact hxL)
  have : ∃ K0 ∈ S, f K0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx0 (by rw [← hsum]; exact Finset.sum_eq_zero hcon)
  obtain ⟨K0, hK0, hne⟩ := this
  refine ⟨K0, hK0, ?_⟩
  have hrest : ∑ J ∈ S.erase K0, f J = 0 := by
    by_contra hr
    apply hxr
    refine ⟨f K0, hS.le hK0 (hf K0 hK0), ∑ J ∈ S.erase K0, f J, ?_, hne, hr, ?_, ?_⟩
    · exact Submodule.sum_mem _ fun J hJ =>
        hS.le (Finset.mem_of_mem_erase hJ) (hf J (Finset.mem_of_mem_erase hJ))
    · rw [bil_sum_right']
      exact Finset.sum_eq_zero fun J hJ =>
        hS.orth K0 hK0 J (Finset.mem_of_mem_erase hJ) (Finset.ne_of_mem_erase hJ).symm _ (hf K0 hK0) _
          (hf J (Finset.mem_of_mem_erase hJ))
    · rw [Finset.add_sum_erase S f hK0]; exact hsum.symm
  have : x = f K0 := by
    rw [← hsum, ← Finset.add_sum_erase S f hK0, hrest, add_zero]
  rw [this]; exact hf K0 hK0

private theorem irr_of_rtg {L : Submodule (𝓞 F) (Fin n → F)} {x y : Fin n → F} (hx : IsIrr Q L x)
    (h : Relation.ReflTransGen (IrrRel Q L) x y) : IsIrr Q L y := by
  induction h with
  | refl => exact hx
  | tail _ hbc _ => exact hbc.2.1

private theorem mem_of_rtg {L : Submodule (𝓞 F) (Fin n → F)} {S : Finset (Submodule (𝓞 F) (Fin n → F))}
    (hS : IsOrthSplitting Q L S) {K : Submodule (𝓞 F) (Fin n → F)} (hK : K ∈ S) {x : Fin n → F}
    (hxK : x ∈ K) {y : Fin n → F} (h : Relation.ReflTransGen (IrrRel Q L) x y) : y ∈ K := by
  induction h with
  | refl => exact hxK
  | @tail b c hab hbc ih =>
    obtain ⟨K', hK', hcK'⟩ := exists_mem_of_irr hS hbc.2.1
    by_cases e : K = K'
    · exact e ▸ hcK'
    · exact absurd (hS.orth K hK K' hK' e b ih c hcK') hbc.2.2

private theorem exists_scale {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.FG) :
    ∃ k : ℤ, k ≠ 0 ∧ ∀ x ∈ L, ∀ y ∈ L, (k : F) * bil Q x y ∈ (algebraMap (𝓞 F) F).range := by
  classical
  obtain ⟨g, hg⟩ := hL
  obtain ⟨k, hk, h⟩ := exists_int_mul_mem ((g ×ˢ g).image fun p => bil Q p.1 p.2)
  refine ⟨k, hk, ?_⟩
  rw [← hg]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      exact h _ (Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, rfl⟩)
    | zero => simp [bil_zero_right']
    | add y z _ _ ih1 ih2 => rw [bil_add_right', mul_add]; exact add_mem ih1 ih2
    | smul c y _ ih =>
      rw [← algebraMap_smul F c y, bil_smul_right, mul_left_comm]
      exact mul_mem (RingHom.mem_range_self _ _) ih
  | zero => intro y _; simp [bil_zero_left']
  | add x z _ _ ih1 ih2 =>
    intro y hy; rw [bil_add_left', mul_add]; exact add_mem (ih1 y hy) (ih2 y hy)
  | smul c x _ ih =>
    intro y hy
    rw [← algebraMap_smul F c x, bil_smul_left, mul_left_comm]
    exact mul_mem (RingHom.mem_range_self _ _) (ih y hy)

private theorem exists_measure (hQ : IsTotallyPosDef Q) {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.FG) :
    ∃ τ : (Fin n → F) → ℚ, (∀ x ∈ L, ∃ m : ℕ, τ x = m) ∧ (∀ x, x ≠ 0 → 0 < τ x) ∧
      (∀ y z, bil Q y z = 0 → τ (y + z) = τ y + τ z) := by
  obtain ⟨k, hk, hkb⟩ := exists_scale (Q := Q) hL
  have hkF : ((k : ℤ) : F) ≠ 0 := Int.cast_ne_zero.mpr hk
  refine ⟨fun x => Algebra.trace ℚ F (((k : F) * (k : F)) * bil Q x x), ?_, ?_, ?_⟩
  · intro x hx
    by_cases hx0 : x = 0
    · exact ⟨0, by simp [hx0, bil_zero_right']⟩
    obtain ⟨a, ha⟩ := hkb x hx x hx
    have hmem : ((k : F) * (k : F)) * bil Q x x ∈ (algebraMap (𝓞 F) F).range :=
      ⟨(k : 𝓞 F) * a, by rw [map_mul, ha]; simp [mul_assoc]⟩
    have hpos : 0 < Algebra.trace ℚ F (((k : F) * (k : F)) * bil Q x x) := by
      have := trForm_self_pos hQ (smul_ne_zero hkF hx0)
      rw [trForm_apply, bil_smul_left, bil_smul_right] at this
      simpa [mul_assoc] using this
    have hpos' := hpos
    rw [← trZ_eq hmem] at hpos'
    have h0 : 0 ≤ trZ (((k : F) * (k : F)) * bil Q x x) := by exact_mod_cast hpos'.le
    refine ⟨(trZ (((k : F) * (k : F)) * bil Q x x)).toNat, ?_⟩
    show Algebra.trace ℚ F (((k : F) * (k : F)) * bil Q x x) = _
    rw [← trZ_eq hmem]
    exact_mod_cast (Int.toNat_of_nonneg h0).symm
  · intro x hx
    have := trForm_self_pos hQ (smul_ne_zero hkF hx)
    rw [trForm_apply, bil_smul_left, bil_smul_right] at this
    simpa [mul_assoc] using this
  · intro y z h
    have h' : bil Q z y = 0 := by rw [bil_comm]; exact h
    simp only [bil_add_left', bil_add_right', h, h', add_zero, zero_add, mul_add, map_add]

private theorem span_irr (hQ : IsTotallyPosDef Q) {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.FG) :
    ∀ x ∈ L, x ∈ Submodule.span (𝓞 F) {y | IsIrr Q L y} := by
  obtain ⟨τ, hint, hpos, hadd⟩ := exists_measure hQ hL
  have key : ∀ m : ℕ, ∀ x ∈ L, τ x = m → x ∈ Submodule.span (𝓞 F) {y | IsIrr Q L y} := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro x hx hτ
      by_cases h0 : x = 0
      · simp [h0]
      by_cases hr : IsReducibleVec Q L x
      · obtain ⟨y, hy, z, hz, hy0, hz0, hyz, rfl⟩ := hr
        obtain ⟨my, hmy⟩ := hint y hy
        obtain ⟨mz, hmz⟩ := hint z hz
        have e := hadd y z hyz
        rw [hτ, hmy, hmz] at e
        have e' : m = my + mz := by exact_mod_cast e
        have p1 := hpos y hy0
        have p2 := hpos z hz0
        rw [hmy] at p1
        rw [hmz] at p2
        have q1 : 0 < my := by exact_mod_cast p1
        have q2 : 0 < mz := by exact_mod_cast p2
        exact add_mem (ih my (by omega) y hy hmy) (ih mz (by omega) z hz hmz)
      · exact Submodule.subset_span ⟨hx, h0, hr⟩
  intro x hx
  obtain ⟨m, hm⟩ := hint x hx
  exact key m x hx hm

private theorem latOrth_span {s t : Set (Fin n → F)} (h : ∀ y ∈ s, ∀ z ∈ t, bil Q y z = 0) :
    LatOrth Q (Submodule.span (𝓞 F) s) (Submodule.span (𝓞 F) t) := by
  intro a ha b hb
  induction ha using Submodule.span_induction with
  | mem a ha =>
    induction hb using Submodule.span_induction with
    | mem b hb => exact h a ha b hb
    | zero => exact bil_zero_right' a
    | add b c _ _ ih1 ih2 => rw [bil_add_right', ih1, ih2, add_zero]
    | smul c b _ ih => rw [← algebraMap_smul F c b, bil_smul_right, ih, mul_zero]
  | zero => exact bil_zero_left' b
  | add a c _ _ ih1 ih2 => rw [bil_add_left', ih1, ih2, add_zero]
  | smul c a _ ih => rw [← algebraMap_smul F c a, bil_smul_left, ih, mul_zero]

private theorem disjoint_of_latOrth (hQ : IsTotallyPosDef Q) {M N : Submodule (𝓞 F) (Fin n → F)}
    (h : LatOrth Q M N) : Disjoint M N := by
  rw [Submodule.disjoint_def]
  intro z hzM hzN
  by_contra hz
  have h0 := h z hzM z hzN
  have := trForm_self_pos hQ hz
  rw [trForm_apply, h0] at this
  simp at this

private theorem le_span_irr (hQ : IsTotallyPosDef Q) {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.FG)
    {S : Finset (Submodule (𝓞 F) (Fin n → F))} (hS : IsOrthSplitting Q L S)
    {K : Submodule (𝓞 F) (Fin n → F)} (hK : K ∈ S) :
    K ≤ Submodule.span (𝓞 F) {y | IsIrr Q L y ∧ y ∈ K} := by
  classical
  intro k hk
  have hkL : k ∈ L := hS.le hK hk
  have h1 := span_irr hQ hL k hkL
  have h2 : Submodule.span (𝓞 F) {y | IsIrr Q L y} ≤
      S.sup (fun J => Submodule.span (𝓞 F) {y | IsIrr Q L y ∧ y ∈ J}) := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨J, hJ, hyJ⟩ := exists_mem_of_irr hS hy
    exact (Finset.le_sup (f := fun J => Submodule.span (𝓞 F) {y | IsIrr Q L y ∧ y ∈ J}) hJ)
      (Submodule.subset_span ⟨hy, hyJ⟩)
  obtain ⟨f, hf, hsum⟩ := exists_sum_of_mem_sup _ (h2 h1)
  have hfJ : ∀ J ∈ S, f J ∈ J := fun J hJ =>
    (Submodule.span_le.mpr (fun y hy => hy.2)) (hf J hJ)
  have := sum_eq_comp hS.supIndep hK f hfJ (hsum ▸ hk)
  rw [← hsum, this]; exact hf K hK

private theorem exists_irr_mem (hQ : IsTotallyPosDef Q) {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.FG)
    {S : Finset (Submodule (𝓞 F) (Fin n → F))} (hS : IsOrthSplitting Q L S)
    {K : Submodule (𝓞 F) (Fin n → F)} (hK : K ∈ S) : ∃ x, IsIrr Q L x ∧ x ∈ K := by
  obtain ⟨k, hkK, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hS.ne_bot K hK)
  by_contra hcon
  push Not at hcon
  have h := le_span_irr hQ hL hS hK hkK
  have e : {y | IsIrr Q L y ∧ y ∈ K} = ∅ :=
    Set.eq_empty_of_forall_notMem fun y hy => hcon y hy.1 hy.2
  rw [e, Submodule.span_empty] at h
  exact hk0 (by simpa using h)

private theorem eq_span_class (hQ : IsTotallyPosDef Q) {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.FG)
    {S : Finset (Submodule (𝓞 F) (Fin n → F))} (hS : IsOrthSplitting Q L S)
    (hSi : ∀ K ∈ S, IsIndecomposable Q K) {K : Submodule (𝓞 F) (Fin n → F)} (hK : K ∈ S)
    {x : Fin n → F} (hxK : x ∈ K) (hx : IsIrr Q L x) :
    K = Submodule.span (𝓞 F) {y | Relation.ReflTransGen (IrrRel Q L) x y} := by
  classical
  set C : Set (Fin n → F) := {y | Relation.ReflTransGen (IrrRel Q L) x y} with hCdef
  set P : Set (Fin n → F) := {y | IsIrr Q L y ∧ y ∈ K} with hPdef
  have hCP : C ⊆ P := fun y hy =>
    ⟨irr_of_rtg hx hy, mem_of_rtg hS hK hxK hy⟩
  have hxC : x ∈ C := Relation.ReflTransGen.refl
  have hKeq : K = Submodule.span (𝓞 F) C ⊔ Submodule.span (𝓞 F) (P \ C) := by
    apply le_antisymm
    · refine (le_span_irr hQ hL hS hK).trans ?_
      rw [← Submodule.span_union]
      apply Submodule.span_mono
      intro y hy
      by_cases hyC : y ∈ C
      · exact Or.inl hyC
      · exact Or.inr ⟨hy, hyC⟩
    · refine sup_le ?_ ?_
      · exact Submodule.span_le.mpr fun y hy => (hCP hy).2
      · exact Submodule.span_le.mpr fun y hy => hy.1.2
  have horth : LatOrth Q (Submodule.span (𝓞 F) C) (Submodule.span (𝓞 F) (P \ C)) := by
    apply latOrth_span
    intro y hy z hz
    by_contra hne
    exact hz.2 (Relation.ReflTransGen.tail hy ⟨irr_of_rtg hx hy, hz.1.1, hne⟩)
  have hMne : Submodule.span (𝓞 F) C ≠ ⊥ := by
    intro h
    have : x ∈ Submodule.span (𝓞 F) C := Submodule.subset_span hxC
    rw [h] at this
    exact hx.2.1 (by simpa using this)
  have hN : Submodule.span (𝓞 F) (P \ C) = ⊥ := by
    by_contra hNne
    exact (hSi K hK).2 ⟨_, _, hMne, hNne, horth, disjoint_of_latOrth hQ horth, hKeq.symm⟩
  rw [hN, sup_bot_eq] at hKeq
  exact hKeq

private theorem subset_of_splittings (hQ : IsTotallyPosDef Q) {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.FG)
    {S S' : Finset (Submodule (𝓞 F) (Fin n → F))} (hS : IsOrthSplitting Q L S)
    (hSi : ∀ K ∈ S, IsIndecomposable Q K) (hS' : IsOrthSplitting Q L S')
    (hSi' : ∀ K ∈ S', IsIndecomposable Q K) : S ⊆ S' := by
  intro K hK
  obtain ⟨x, hx, hxK⟩ := exists_irr_mem hQ hL hS hK
  obtain ⟨K', hK', hxK'⟩ := exists_mem_of_irr hS' hx
  rw [eq_span_class hQ hL hS hSi hK hxK hx, ← eq_span_class hQ hL hS' hSi' hK' hxK' hx]
  exact hK'

/-! ### Existence -/

/-- Helper: the $F$-rank of the $F$-span of a lattice. -/
private def rk (K : Submodule (𝓞 F) (Fin n → F)) : ℕ :=
  Module.finrank F (Submodule.span F (K : Set (Fin n → F)))

private theorem exists_denom (K : Submodule (𝓞 F) (Fin n → F)) {z : Fin n → F}
    (hz : z ∈ Submodule.span F (K : Set (Fin n → F))) : ∃ d : 𝓞 F, d ≠ 0 ∧ d • z ∈ K := by
  induction hz using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨d₁, h1, hx⟩ := ihx
    obtain ⟨d₂, h2, hy⟩ := ihy
    refine ⟨d₁ * d₂, mul_ne_zero h1 h2, ?_⟩
    have e1 : (d₁ * d₂) • x = d₂ • (d₁ • x) := by rw [mul_comm, mul_smul]
    have e2 : (d₁ * d₂) • y = d₁ • (d₂ • y) := mul_smul _ _ _
    rw [smul_add, e1, e2]
    exact K.add_mem (K.smul_mem d₂ hx) (K.smul_mem d₁ hy)
  | smul c x _ ih =>
    obtain ⟨d, hd, hx⟩ := ih
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbF : algebraMap (𝓞 F) F b ≠ 0 := fun h =>
      hb0 ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
    have hc : c * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a := by
      rw [← hab]; exact div_mul_cancel₀ _ hbF
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have : ((b : 𝓞 F) * d) • (c • x) = a • (d • x) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      linear_combination (algebraMap (𝓞 F) F d * x i) * hc
    rw [this]
    exact K.smul_mem a hx

private theorem disjoint_span {K₁ K₂ : Submodule (𝓞 F) (Fin n → F)} (h : Disjoint K₁ K₂) :
    Disjoint (Submodule.span F (K₁ : Set (Fin n → F))) (Submodule.span F (K₂ : Set (Fin n → F))) := by
  rw [Submodule.disjoint_def]
  intro z hz1 hz2
  obtain ⟨d₁, h1, hd1⟩ := exists_denom K₁ hz1
  obtain ⟨d₂, h2, hd2⟩ := exists_denom K₂ hz2
  have a1 : (d₂ * d₁) • z ∈ K₁ := by rw [mul_smul]; exact K₁.smul_mem d₂ hd1
  have a2 : (d₂ * d₁) • z ∈ K₂ := by rw [mul_comm, mul_smul]; exact K₂.smul_mem d₁ hd2
  have h0 : (d₂ * d₁) • z = 0 := (Submodule.disjoint_def.mp h) _ a1 a2
  rcases smul_eq_zero.mp h0 with h | h
  · exact absurd h (mul_ne_zero h2 h1)
  · exact h

private theorem span_sup' (K₁ K₂ : Submodule (𝓞 F) (Fin n → F)) :
    Submodule.span F ((K₁ ⊔ K₂ : Submodule (𝓞 F) (Fin n → F)) : Set (Fin n → F)) =
      Submodule.span F (K₁ : Set (Fin n → F)) ⊔ Submodule.span F (K₂ : Set (Fin n → F)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    exact Submodule.add_mem_sup (Submodule.subset_span hx) (Submodule.subset_span hy)
  · exact sup_le (Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left))
      (Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_right))

private theorem rk_sup {K₁ K₂ : Submodule (𝓞 F) (Fin n → F)} (h : Disjoint K₁ K₂) :
    rk (K₁ ⊔ K₂) = rk K₁ + rk K₂ := by
  unfold rk
  rw [span_sup']
  have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F (K₁ : Set (Fin n → F)))
    (Submodule.span F (K₂ : Set (Fin n → F)))
  rw [disjoint_iff.mp (disjoint_span h), finrank_bot] at this
  omega

private theorem rk_pos {K : Submodule (𝓞 F) (Fin n → F)} (hK : K ≠ ⊥) : 1 ≤ rk K := by
  obtain ⟨k, hkK, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  unfold rk
  rw [Submodule.one_le_finrank_iff]
  intro h
  have : k ∈ Submodule.span F (K : Set (Fin n → F)) := Submodule.subset_span hkK
  rw [h] at this
  exact hk0 (by simpa using this)

private theorem rk_le (K : Submodule (𝓞 F) (Fin n → F)) : rk K ≤ n := by
  unfold rk
  exact (Submodule.finrank_le _).trans (by simp)

private theorem splitting_empty : IsOrthSplitting Q ⊥ (∅ : Finset (Submodule (𝓞 F) (Fin n → F))) where
  ne_bot := by simp
  orth := by simp
  indep := (Finset.supIndep_empty (id : Submodule (𝓞 F) (Fin n → F) → _)).independent
  sup_eq := by simp

private theorem splitting_single {K : Submodule (𝓞 F) (Fin n → F)} (hK : K ≠ ⊥) :
    IsOrthSplitting Q K ({K} : Finset (Submodule (𝓞 F) (Fin n → F))) where
  ne_bot := by simpa using hK
  orth := by
    intro A hA B hB hne
    simp only [Finset.mem_singleton] at hA hB
    exact absurd (hA.trans hB.symm) hne
  indep := (Finset.supIndep_singleton K (id : Submodule (𝓞 F) (Fin n → F) → _)).independent
  sup_eq := by simp

private theorem supIndep_aux {K₁ K₂ : Submodule (𝓞 F) (Fin n → F)} (hd : Disjoint K₁ K₂)
    {S₁ S₂ : Finset (Submodule (𝓞 F) (Fin n → F))} (h1 : S₁.SupIndep id) (hle1 : ∀ A ∈ S₁, A ≤ K₁)
    (hle2 : ∀ A ∈ S₂, A ≤ K₂) {t : Finset (Submodule (𝓞 F) (Fin n → F))} (ht : t ⊆ S₁ ∪ S₂)
    {i : Submodule (𝓞 F) (Fin n → F)} (hi : i ∈ S₁) (hit : i ∉ t) : Disjoint i (t.sup id) := by
  classical
  have ht1 : t.filter (· ∈ S₁) ⊆ S₁ := fun j hj => (Finset.mem_filter.mp hj).2
  have hd1 : Disjoint i ((t.filter (· ∈ S₁)).sup id) :=
    h1 ht1 hi (fun h => hit (Finset.mem_filter.mp h).1)
  have hsup : Disjoint (i ⊔ (t.filter (· ∈ S₁)).sup id) K₂ := by
    refine Disjoint.mono_left ?_ hd
    exact sup_le (hle1 i hi) (Finset.sup_le fun j hj => hle1 j (Finset.mem_filter.mp hj).2)
  refine (Disjoint.disjoint_sup_right_of_disjoint_sup_left hd1 hsup).mono_right ?_
  refine Finset.sup_le fun j hj => ?_
  by_cases hjS : j ∈ S₁
  · exact le_sup_of_le_left (Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hj, hjS⟩))
  · have : j ∈ S₂ := by
      rcases Finset.mem_union.mp (ht hj) with h | h
      · exact absurd h hjS
      · exact h
    exact le_sup_of_le_right (hle2 j this)

private theorem splitting_union {K₁ K₂ : Submodule (𝓞 F) (Fin n → F)} (ho : LatOrth Q K₁ K₂) (hd : Disjoint K₁ K₂)
    {S₁ S₂ : Finset (Submodule (𝓞 F) (Fin n → F))} (h1 : IsOrthSplitting Q K₁ S₁)
    (h2 : IsOrthSplitting Q K₂ S₂) : IsOrthSplitting Q (K₁ ⊔ K₂) (S₁ ∪ S₂) where
  ne_bot := by
    intro K hK
    rcases Finset.mem_union.mp hK with h | h
    · exact h1.ne_bot K h
    · exact h2.ne_bot K h
  orth := by
    intro A hA B hB hne
    rcases Finset.mem_union.mp hA with hA | hA <;> rcases Finset.mem_union.mp hB with hB | hB
    · exact h1.orth A hA B hB hne
    · exact fun x hx y hy => ho x (h1.le hA hx) y (h2.le hB hy)
    · intro x hx y hy
      rw [bil_comm]
      exact ho y (h1.le hB hy) x (h2.le hA hx)
    · exact h2.orth A hA B hB hne
  indep := by
    classical
    refine Finset.SupIndep.independent (f := (id : Submodule (𝓞 F) (Fin n → F) → _)) ?_
    intro t ht i hi hit
    rcases Finset.mem_union.mp hi with hi | hi
    · exact supIndep_aux hd h1.supIndep (fun A hA => h1.le hA) (fun A hA => h2.le hA) ht hi hit
    · rw [Finset.union_comm] at ht
      exact supIndep_aux hd.symm h2.supIndep (fun A hA => h2.le hA) (fun A hA => h1.le hA) ht hi hit
  sup_eq := by
    rw [Finset.sup_union, h1.sup_eq, h2.sup_eq]

end Helpers

/-- **Every lattice has an indecomposable splitting** (O'Meara 1973, §105, p. 321): every $L$ is an
orthogonal sum of at most $n$ indecomposable lattices. -/
@[kb "omeara1963" "§105, p. 321 (existence of an indecomposable splitting)"]
theorem exists_indecomposable_splitting (L : Submodule (𝓞 F) (Fin n → F)) :
    ∃ S : Finset (Submodule (𝓞 F) (Fin n → F)), IsOrthSplitting Q L S ∧ (∀ K ∈ S, IsIndecomposable Q K) ∧
      S.card ≤ n := by
  classical
  have key : ∀ r : ℕ, ∀ K : Submodule (𝓞 F) (Fin n → F), rk K = r →
      ∃ S : Finset (Submodule (𝓞 F) (Fin n → F)), IsOrthSplitting Q K S ∧
        (∀ K' ∈ S, IsIndecomposable Q K') ∧ S.card ≤ rk K := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro K hr
      by_cases hbot : K = ⊥
      · subst hbot
        exact ⟨∅, splitting_empty, by simp, by simp⟩
      by_cases hdec : IsDecomposable Q K
      · obtain ⟨K₁, K₂, h1, h2, ho, hd, hK⟩ := hdec
        have e := rk_sup hd
        rw [hK] at e
        have p1 := rk_pos h1
        have p2 := rk_pos h2
        obtain ⟨S₁, hS₁, hi₁, hc₁⟩ := ih (rk K₁) (by omega) K₁ rfl
        obtain ⟨S₂, hS₂, hi₂, hc₂⟩ := ih (rk K₂) (by omega) K₂ rfl
        refine ⟨S₁ ∪ S₂, ?_, ?_, ?_⟩
        · rw [← hK]; exact splitting_union ho hd hS₁ hS₂
        · intro K' hK'
          rcases Finset.mem_union.mp hK' with h | h
          · exact hi₁ _ h
          · exact hi₂ _ h
        · exact (Finset.card_union_le _ _).trans (by omega)
      · exact ⟨{K}, splitting_single hbot, by simpa [IsIndecomposable] using ⟨hbot, hdec⟩,
          by simpa using rk_pos hbot⟩
  obtain ⟨S, h1, h2, h3⟩ := key _ L rfl
  exact ⟨S, h1, h2, h3.trans (rk_le L)⟩

/-- **Theorem 105:1 (Eichler)** (O'Meara 1973, §105, 105:1, p. 321): for a totally positive definite space $V$ over
the number field $F$, the components of an indecomposable splitting of a finitely generated lattice $L$ are unique
(up to their order): two indecomposable splittings of $L$ have the same set of components. See the module docstring
for the deviations (all finite spots; totally positive definite). -/
@[kb "omeara1963" "§105, 105:1, p. 321 (special case: S all finite spots, V totally positive definite)"]
theorem indecomposable_splitting_unique (hQ : IsTotallyPosDef Q) (L : Submodule (𝓞 F) (Fin n → F))
    (hL : L.FG) {S S' : Finset (Submodule (𝓞 F) (Fin n → F))} (hS : IsOrthSplitting Q L S)
    (hSi : ∀ K ∈ S, IsIndecomposable Q K) (hS' : IsOrthSplitting Q L S') (hSi' : ∀ K ∈ S', IsIndecomposable Q K) :
    S = S' :=
  Finset.Subset.antisymm (subset_of_splittings hQ hL hS hSi hS' hSi')
    (subset_of_splittings hQ hL hS' hSi' hS hSi)

end QuadFormsKB.Lattices
