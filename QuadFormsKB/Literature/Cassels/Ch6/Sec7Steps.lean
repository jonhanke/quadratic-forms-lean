/-
# Cassels, Chapter 6, §7: the induction step for Theorem 1.3

Steps of the proof of Theorem 1.3 (`exists_form_of_local`, `Ch6/Sec7.lean`; see the module docstring there for the
setting): splitting off a represented value with rational coefficients (`exists_split_rat`), Cassels' $c_v$ of
$\langle t\rangle \perp \langle\beta\rangle$ (`hasseCassels_cons`), the case $n = 1$ (`exists_form_one`) and the
induction step (`reduce_step`).
-/
import QuadFormsKB.Literature.LocalGlobal.HasseConventions
import QuadFormsKB.Literature.LocalGlobal.PrescribedSymbols

namespace QuadFormsKB.Cassels.Ch6

open QuadForm

variable {m n : ℕ}

/-- Helper: $(t, \prod_j \beta_j)_v = \prod_j (t, \beta_j)_v$ for nonzero $\beta_j$. -/
theorem hilbert_prod_right_aux (v : RatPlace) {t : ℚ} (ht : t ≠ 0) (β : Fin m → ℚ) (hβ : ∀ i, β i ≠ 0) :
    v.hilbert t (∏ i, β i) = ∏ i, v.hilbert t (β i) := by
  rw [RatPlace.hilbert_comm, RatPlace.hilbert_prod_left v t ht Finset.univ β (fun i _ => hβ i)]
  exact Finset.prod_congr rfl fun i _ => RatPlace.hilbert_comm v _ _

/-- Cassels' $c_v$ of $\langle t\rangle \perp \langle\beta\rangle$: $c_v = (t, d(\beta))_v\, c_v(\beta)$ (Cassels, Ch. 4,
Lemma 2.3 (iii), p. 58, one summand a line). -/
theorem hasseCassels_cons (v : RatPlace) {t : ℚ} (ht : t ≠ 0) (β : Fin m → ℚ) (hβ : ∀ i, β i ≠ 0) :
    v.hasseCassels (Fin.cons t β : Fin (m + 1) → ℚ) = v.hilbert t (∏ i, β i) * v.hasseCassels β := by
  rw [hilbert_prod_right_aux v ht β hβ]
  unfold RatPlace.hasseCassels
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]; simp [Fin.succ_pos]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_succ]
    simp [Fin.succ_lt_succ_iff, (Fin.succ_pos i).not_gt]

/-- Helper: diagonal forms whose entries differ by nonzero squares are isometric. -/
theorem diag_isometric_of_sq {K : Type*} [Field K] [CharZero K] {a b : Fin n → K} (s : Fin n → K)
    (hs : ∀ i, s i ≠ 0) (h : ∀ i, a i = s i ^ 2 * b i) : (diag b).IsometricIn K (diag a) := by
  refine ⟨Matrix.diagonal s, ?_, fun x => ?_⟩
  · rw [isUnit_iff_ne_zero, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hs i
  · rw [evalIn_diag, evalIn_diag]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Algebra.algebraMap_self, RingHom.id_apply, Matrix.mulVec_diagonal, h]
    ring

/-- Helper: the case $n = 1$ over one completion. -/
theorem form_one_aux (K : Type) [Field K] [CharZero K] (a b : Fin 1 → ℚ)
    (h : SameSquareClass K (∏ i, b i) (∏ i, a i)) : (diag a).IsometricIn K (diag b) := by
  rw [isometricIn_cast]
  obtain ⟨u, hu, e⟩ := h
  refine diag_isometric_of_sq (fun _ => u) (fun _ => hu) fun i => ?_
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simpa [Fin.prod_univ_one] using e

/-- **The base case $n = 1$** of Theorem 1.3: $f = \langle d_0\rangle$. -/
theorem exists_form_one (d₀ : ℚ) (hd₀ : d₀ ≠ 0) (α : RatPlace → Fin 1 → ℚ)
    (hdet : ∀ v : RatPlace, v.atPlace fun K _ _ => SameSquareClass K (∏ i, α v i) d₀) :
    ∃ a : Fin 1 → ℚ, (∀ i, a i ≠ 0) ∧ SameSquareClass ℚ (∏ i, a i) d₀ ∧
      ∀ v : RatPlace, v.atPlace fun K _ _ => (diag a).IsometricIn K (diag (α v)) := by
  refine ⟨fun _ => d₀, fun _ => hd₀, ⟨1, one_ne_zero, by simp⟩, fun v => ?_⟩
  have h := hdet v
  cases v with
  | infinite =>
    have h' : SameSquareClass ℝ (∏ i, α RatPlace.infinite i) d₀ := h
    exact form_one_aux ℝ _ _ (by simpa using h')
  | finite p =>
    have : Fact p.1.Prime := ⟨p.2⟩
    have h' : SameSquareClass ℚ_[p.1] (∏ i, α (RatPlace.finite p) i) d₀ := h
    exact form_one_aux ℚ_[p.1] _ _ (by simpa using h')

/-- Helper: splitting off a represented value with rational coefficients over a field in which every nonzero
element is a rational times a square. -/
theorem split_rat_gen (K : Type) [Field K] [CharZero K]
    (H : ∀ x : K, x ≠ 0 → ∃ q : ℚ, q ≠ 0 ∧ ∃ s : K, s ≠ 0 ∧ x = s ^ 2 * algebraMap ℚ K q)
    (α : Fin (m + 1) → ℚ) (hα : ∀ i, α i ≠ 0) {t : ℚ} (ht : t ≠ 0)
    (hrep : (diag α).RepresentsIn K t) :
    ∃ β : Fin m → ℚ, (∀ i, β i ≠ 0) ∧ (diag α).IsometricIn K (diag (Fin.cons t β)) := by
  have hαK : ∀ i, algebraMap ℚ K (α i) ≠ 0 := fun i => (map_ne_zero _).2 (hα i)
  have htK : algebraMap ℚ K t ≠ 0 := (map_ne_zero _).2 ht
  have hrepK : (diag fun i => algebraMap ℚ K (α i)).RepresentsIn K (algebraMap ℚ K t) := by
    simp only [RepresentsIn, evalIn_diag, Algebra.algebraMap_self, RingHom.id_apply] at hrep ⊢
    exact hrep
  obtain ⟨β', hβ', hiso⟩ := exists_isometric_diag_cons (nondegenerate_diag hαK) htK hrepK
  choose q hq s hs hβ using fun i => H (β' i) (hβ' i)
  refine ⟨q, hq, ?_⟩
  rw [isometricIn_cast]
  have e : (fun i => algebraMap ℚ K ((Fin.cons t q : Fin (m + 1) → ℚ) i)) =
      (Fin.cons (algebraMap ℚ K t) (fun i => algebraMap ℚ K (q i)) : Fin (m + 1) → K) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [e]
  refine isometricIn_trans K hiso (isometricIn_symm K ?_)
  refine diag_isometric_of_sq (Fin.cons 1 s : Fin (m + 1) → K) (fun i => ?_) fun i => ?_
  · refine Fin.cases ?_ (fun j => ?_) i <;> simp [hs]
  · refine Fin.cases ?_ (fun j => ?_) i <;> simp [hβ]

/-- **Splitting off a represented value, with rational coefficients** (Cassels, Ch. 2, Lemma 2.1, Cor. 2 type step
in §7, p. 86): if $\langle\alpha\rangle$ ($\alpha_i \in \mathbb Q^\times$) represents $t \in \mathbb Q^\times$ over
$\mathbb Q_v$, then $\langle\alpha\rangle \cong \langle t, \beta_0, \dots, \beta_{m-1}\rangle$ over $\mathbb Q_v$ for some
$\beta_i \in \mathbb Q^\times$. -/
theorem exists_split_rat (v : RatPlace) (α : Fin (m + 1) → ℚ) (hα : ∀ i, α i ≠ 0) {t : ℚ} (ht : t ≠ 0)
    (hrep : v.atPlace fun K _ _ => (diag α).RepresentsIn K t) :
    ∃ β : Fin m → ℚ, (∀ i, β i ≠ 0) ∧ v.atPlace fun K _ _ => (diag α).IsometricIn K (diag (Fin.cons t β)) := by
  cases v with
  | infinite =>
    refine split_rat_gen ℝ ?_ α hα ht hrep
    intro x hx
    rcases lt_or_gt_of_ne hx with h | h
    · refine ⟨-1, by norm_num, Real.sqrt (-x), ?_, ?_⟩
      · exact (Real.sqrt_pos.2 (by linarith)).ne'
      · rw [Real.sq_sqrt (by linarith)]; simp
    · refine ⟨1, by norm_num, Real.sqrt x, ?_, ?_⟩
      · exact (Real.sqrt_pos.2 h).ne'
      · rw [Real.sq_sqrt h.le]; simp
  | finite p =>
    have : Fact p.1.Prime := ⟨p.2⟩
    refine split_rat_gen ℚ_[p.1] ?_ α hα ht hrep
    intro x hx
    obtain ⟨q, hq, r, hr⟩ := Prescribed.exists_rat_sq_class p.1 x hx
    have hq' : (q : ℚ_[p.1]) ≠ 0 := by exact_mod_cast hq
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero, div_eq_zero_iff] at hr
      exact hr.elim hx hq'
    refine ⟨q, hq, r, hr0, ?_⟩
    rw [eq_ratCast]
    field_simp at hr
    rw [sq]
    linear_combination hr

/-- Helper: $c_v = \pm 1$. -/
theorem hasseCassels_pm (v : RatPlace) (a : Fin n → ℚ) :
    v.hasseCassels a = 1 ∨ v.hasseCassels a = -1 := by
  unfold RatPlace.hasseCassels
  refine Finset.prod_induction _ (fun x : ℤ => x = 1 ∨ x = -1) ?_ (Or.inl rfl) fun i _ => ?_
  · rintro x y (rfl | rfl) (rfl | rfl) <;> simp
  refine Finset.prod_induction _ (fun x : ℤ => x = 1 ∨ x = -1) ?_ (Or.inl rfl) fun j _ => ?_
  · rintro x y (rfl | rfl) (rfl | rfl) <;> simp
  split_ifs
  · exact RatPlace.hilbert_pm _ _ _
  · exact Or.inl rfl

/-- Helper: the symmetric difference of two finite sets of even cardinality is finite of even cardinality. -/
theorem symmDiff_even_aux {α : Type*} {A C : Set α} (hA : A.Finite) (hC : C.Finite)
    (eA : Even A.ncard) (eC : Even C.ncard) : (symmDiff A C).Finite ∧ Even (symmDiff A C).ncard := by
  refine ⟨hA.symmDiff hC, ?_⟩
  have h1 := Set.ncard_union_add_ncard_inter A C hA hC
  have hdisj : Disjoint (symmDiff A C) (A ∩ C) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rcases hx with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact h' hx'.2
    · exact h' hx'.1
  have hu : A ∪ C = symmDiff A C ∪ (A ∩ C) := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_symmDiff]
    tauto
  have h2 : (A ∪ C).ncard = (symmDiff A C).ncard + (A ∩ C).ncard := by
    rw [hu]
    exact Set.ncard_union_eq hdisj (hA.symmDiff hC) (hA.subset Set.inter_subset_left)
  obtain ⟨a, ha⟩ := eA
  obtain ⟨c, hc⟩ := eC
  exact ⟨a + c - (A ∩ C).ncard, by omega⟩

/-- Helper: the determinant square class of $\beta$ in the split form, over one completion. -/
theorem det_gen (K : Type) [Field K] [CharZero K] (d₀ : ℚ) (α : Fin (m + 1) → ℚ) {t : ℚ} (ht : t ≠ 0)
    (β : Fin m → ℚ) (hdet : SameSquareClass K (∏ i, α i) d₀)
    (hiso : (diag α).IsometricIn K (diag (Fin.cons t β))) : SameSquareClass K (∏ i, β i) (d₀ / t) := by
  obtain ⟨s, hs, e⟩ := sameSq_gen (K := K) α (Fin.cons t β) hiso
  obtain ⟨w, hw, e'⟩ := hdet
  have htK : (t : K) ≠ 0 := by exact_mod_cast ht
  refine ⟨s * w, mul_ne_zero hs hw, ?_⟩
  simp only [eq_ratCast] at e' ⊢
  rw [Fin.prod_cons] at e
  push_cast at e e' ⊢
  field_simp
  rw [e'] at e
  linear_combination e

/-- Helper: from `SameSquareClass` at a place to `SameSqAt`. -/
theorem sameSqAt_of_class (v : RatPlace) {y y' : ℚ}
    (h : v.atPlace fun K _ _ => SameSquareClass K y' y) : SameSqAt v y y' := by
  cases v with
  | infinite =>
    obtain ⟨u, hu, e⟩ := h
    exact ⟨u, hu, by simpa using e⟩
  | finite p =>
    obtain ⟨u, hu, e⟩ := h
    exact ⟨u, hu, by simpa using e⟩

/-- **Cassels, Ch. 6, §7, p. 86** (the induction step of the proof of Theorem 1.3): if $t \in \mathbb Q^\times$ is
represented by every $f_v = \langle\alpha_v\rangle$, write $f_v \cong \langle t\rangle \perp g_v$; then the $g_v$ have
$d(g_v) = d_0/t$, $c_v(g_v) = 1$ for almost all $v$ and $\prod_v c_v(g_v) = 1$. -/
@[kb "cassels1978" "Ch. 6, §7, p. 86 (proof of Thm. 1.3, the induction step)"]
theorem reduce_step (d₀ : ℚ) (hd₀ : d₀ ≠ 0) (α : RatPlace → Fin (m + 1) → ℚ) (hα : ∀ v i, α v i ≠ 0)
    (hdet : ∀ v : RatPlace, v.atPlace fun K _ _ => SameSquareClass K (∏ i, α v i) d₀)
    (hfin : {v : RatPlace | v.hasseCassels (α v) = -1}.Finite)
    (heven : Even {v : RatPlace | v.hasseCassels (α v) = -1}.ncard)
    {t : ℚ} (ht : t ≠ 0) (hrep : ∀ v : RatPlace, v.atPlace fun K _ _ => (diag (α v)).RepresentsIn K t) :
    ∃ β : RatPlace → Fin m → ℚ, (∀ v i, β v i ≠ 0) ∧
      (∀ v : RatPlace, v.atPlace fun K _ _ => SameSquareClass K (∏ i, β v i) (d₀ / t)) ∧
      {v : RatPlace | v.hasseCassels (β v) = -1}.Finite ∧
      Even {v : RatPlace | v.hasseCassels (β v) = -1}.ncard ∧
      ∀ v : RatPlace, v.atPlace fun K _ _ => (diag (α v)).IsometricIn K (diag (Fin.cons t (β v))) := by
  choose β hβ hiso using fun v => exists_split_rat v (α v) (hα v) ht (hrep v)
  have hcls : ∀ v : RatPlace, v.atPlace fun K _ _ => SameSquareClass K (∏ i, β v i) (d₀ / t) := by
    intro v
    have h1 := hdet v
    have h2 := hiso v
    cases v with
    | infinite => exact det_gen ℝ d₀ _ ht _ h1 h2
    | finite p =>
      have : Fact p.1.Prime := ⟨p.2⟩
      exact det_gen ℚ_[p.1] d₀ _ ht _ h1 h2
  have hc : ∀ v : RatPlace, v.hasseCassels (β v) = v.hilbert t (d₀ / t) * v.hasseCassels (α v) := by
    intro v
    have e1 := RatPlace.hasseCassels_isometric v (α v) (Fin.cons t (β v)) (hα v)
      (fun i => Fin.cases ht (fun j => hβ v j) i) (hiso v)
    rw [e1, hasseCassels_cons v ht (β v) (hβ v),
      (sameSqAt_of_class v (hcls v)).hilbert_right t]
    rcases RatPlace.hilbert_pm v t (d₀ / t) with h | h <;> rw [h] <;> ring
  have hset : {v : RatPlace | v.hasseCassels (β v) = -1} =
      symmDiff {v : RatPlace | v.hasseCassels (α v) = -1} {v : RatPlace | v.hilbert t (d₀ / t) = -1} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_symmDiff, hc v]
    rcases RatPlace.hilbert_pm v t (d₀ / t) with h | h <;>
      rcases hasseCassels_pm v (α v) with h' | h' <;> simp [h, h']
  obtain ⟨hF, hE⟩ := hilbert_product_formula t (d₀ / t) ht (div_ne_zero hd₀ ht)
  obtain ⟨hF', hE'⟩ := symmDiff_even_aux hfin hF heven hE
  rw [← hset] at hF' hE'
  exact ⟨β, hβ, hcls, hF', hE', hiso⟩

end QuadFormsKB.Cassels.Ch6
