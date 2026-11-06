/-
# A common transversal for the two rows of a symplectic matrix

**Layer:** linear algebra over a field $k$ (every field).

**Result** (`twoRowTransversal`). The named input `TwoRowTransversal g k` of `SiegelTwoCell.lean` holds for every
field $k$ and every genus $g$: for $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{Sp}_{2g}(k)$ with
$\det c = 0$ or $\det a = 0$ there is a symmetric $T$ with $\det(cT + d) \ne 0$ and $\det(aT + b) \ne 0$.

**Method.** All matrices are indexed by a finite type $\kappa$; for $i_0 \in \kappa$, `restr i₀ X` is the restriction of
$X$ to $\kappa \setminus \{i_0\}$, and `KerLE1 N` says that the kernel of $N$ is contained in a line.
1. *Completion* (`exists_completion`): a symmetric $Y$ on $\kappa \setminus \{i_0\}$ with `KerLE1 Y` is the restriction
   of an invertible symmetric $X$ on $\kappa$ (border $Y$ by a row $y$ with $y \cdot w \ne 0$ for the kernel vector $w$).
2. *Sublemma K* (`exists_kerLE1`): for every symmetric $M$ there is an invertible symmetric $U$ with `KerLE1 (M + U)`
   (induction on $\#\kappa$, bordering the inductive $U'$ so that the new column avoids the range of $M' + U'$).
3. *Kernel split* (`exists_split_of_det_eq_zero`): a singular symmetric $C$ is congruent, $C' = Q^{\mathsf T}CQ$, to a
   matrix with a zero row and column $i_0$ ($Q$ is the identity with column $i_0$ replaced by a kernel vector); then
   $\det(1 - C'\Delta) = \det(1 - \tilde C\tilde\Delta)$ for the restrictions (`det_one_sub_mul_of_row_col_zero`).
4. *Main lemma* (`exists_det_one_sub_kerLE1`, induction on $\#\kappa$): for symmetric $C, B$ there is a symmetric
   $\Delta$ with $\det(1 - C\Delta) \ne 0$ and `KerLE1 (B + Δ)`; if $C$ is invertible take $\Delta = C^{-1} + U$ with $U$
   from 2 for $M = B + C^{-1}$; if $C$ is singular split as in 3, use the induction hypothesis on
   $\kappa \setminus \{i_0\}$ and complete by 1, which even gives $\det(B + \Delta) \ne 0$
   (`exists_det_one_sub_det`).
5. *Möbius change of variable* (`exists_two_rows_normal`): for $C$ singular and $Y$ from 4 (with $\Delta = Y$), the
   symmetric $T = (1 - YC)^{-1}Y$ has $1 + CT = (1 - CY)^{-1}$ and $(1 + BC)T + B = (Y + B)(1 + CT)$.
6. *Normal form*: replacing $\gamma$ by $m({}^td)\,\gamma\,n(T_0)$ for a $T_0$ with $\det(cT_0 + d) \ne 0$
   (`exists_symm_det_ne`) makes $d = 1$, $c = C$ symmetric, $b = B$ symmetric and $a = 1 + BC$; the case
   $\det a = 0$ follows from the case $\det c = 0$ for $w\gamma$.

Sources: elementary linear algebra; the statement is the transversality fact behind Kudla, *Notes on the local theta
correspondence* (1996), §I.1 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Genus.SiegelTwoCell

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

universe u

variable {k : Type*} [Field k]

section Finite

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The kernel of $N$ lies in a line: some $w$ with $Nx = 0 \Rightarrow x \in k\,w$. -/
def KerLE1 (N : Matrix κ κ k) : Prop := ∃ w : κ → k, ∀ x, N *ᵥ x = 0 → ∃ c : k, x = c • w

lemma kerLE1_of_det_ne_zero {N : Matrix κ κ k} (h : N.det ≠ 0) : KerLE1 N := by
  refine ⟨0, fun x hx => ⟨0, ?_⟩⟩
  by_contra hne
  rw [smul_zero] at hne
  exact h (Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hne, hx⟩)

/-- The complement $\kappa \setminus \{i_0\}$. -/
abbrev Off (i₀ : κ) := {j : κ // j ≠ i₀}

/-- The restriction of $X$ to $\kappa \setminus \{i_0\}$. -/
def restr (i₀ : κ) (X : Matrix κ κ k) : Matrix (Off i₀) (Off i₀) k := X.submatrix Subtype.val Subtype.val

/-- The bordered matrix: $Y$ on $\kappa \setminus \{i_0\}$, the vector $y$ in row and column $i_0$, and $\eta$ at
$(i_0, i_0)$. -/
def border (i₀ : κ) (Y : Matrix (Off i₀) (Off i₀) k) (y : Off i₀ → k) (η : k) : Matrix κ κ k :=
  fun i j => if hi : i = i₀ then (if hj : j = i₀ then η else y ⟨j, hj⟩)
    else (if hj : j = i₀ then y ⟨i, hi⟩ else Y ⟨i, hi⟩ ⟨j, hj⟩)

/-- The border of a symmetric matrix is symmetric. -/
lemma border_transpose (i₀ : κ) {Y : Matrix (Off i₀) (Off i₀) k} (hY : Yᵀ = Y) (y : Off i₀ → k) (η : k) :
    (border i₀ Y y η)ᵀ = border i₀ Y y η := by
  ext i j
  simp only [Matrix.transpose_apply, border]
  by_cases hi : i = i₀ <;> by_cases hj : j = i₀ <;> simp [hi, hj]
  all_goals exact congrFun (congrFun hY _) _

lemma restr_border (i₀ : κ) (Y : Matrix (Off i₀) (Off i₀) k) (y : Off i₀ → k) (η : k) :
    restr i₀ (border i₀ Y y η) = Y := by
  ext i j
  simp [restr, border, i.2, j.2]

lemma border_mulVec_off (i₀ : κ) (Y : Matrix (Off i₀) (Off i₀) k) (y : Off i₀ → k) (η : k) (v : κ → k)
    (j : Off i₀) :
    (border i₀ Y y η *ᵥ v) j.val = (Y *ᵥ (fun l : Off i₀ => v l.val)) j + y j * v i₀ := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀, add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro l _
    simp [border, j.2, l.2]
  · simp [border, j.2]

lemma border_mulVec_base (i₀ : κ) (Y : Matrix (Off i₀) (Off i₀) k) (y : Off i₀ → k) (η : k) (v : κ → k) :
    (border i₀ Y y η *ᵥ v) i₀ = y ⬝ᵥ (fun l : Off i₀ => v l.val) + η * v i₀ := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀, add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro l _
    simp [border, l.2]
  · simp [border]

/-- $X v = 0$ for the border $X$ of $Y$ by $(y, \eta)$ splits into $Yx + t\,y = 0$ and $y \cdot x + \eta t = 0$
($x$ the restriction of $v$, $t = v_{i_0}$). -/
lemma border_mulVec_eq_zero_iff (i₀ : κ) (Y : Matrix (Off i₀) (Off i₀) k) (y : Off i₀ → k) (η : k)
    (v : κ → k) :
    border i₀ Y y η *ᵥ v = 0 ↔
      (Y *ᵥ (fun l : Off i₀ => v l.val) + v i₀ • y = 0 ∧
        y ⬝ᵥ (fun l : Off i₀ => v l.val) + η * v i₀ = 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · funext j
      have := congrFun h j.val
      rw [border_mulVec_off] at this
      simpa [mul_comm] using this
    · have := congrFun h i₀
      rwa [border_mulVec_base] at this
  · rintro ⟨h1, h2⟩
    funext j
    by_cases hj : j = i₀
    · subst hj
      rw [border_mulVec_base]; simpa using h2
    · have := congrFun h1 ⟨j, hj⟩
      have e := border_mulVec_off i₀ Y y η v ⟨j, hj⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this e
      simp only [Pi.zero_apply]
      rw [e, ← this]; ring

lemma eq_zero_of_off (i₀ : κ) (v : κ → k) (hx : (fun l : Off i₀ => v l.val) = 0) (ht : v i₀ = 0) :
    v = 0 := by
  funext j
  by_cases hj : j = i₀
  · subst hj; simpa using ht
  · simpa using congrFun hx ⟨j, hj⟩

/-- **Completion.** A symmetric $Y$ on $\kappa \setminus \{i_0\}$ whose kernel lies in a line is the restriction of an
invertible symmetric matrix on $\kappa$. -/
theorem exists_completion (i₀ : κ) {Y : Matrix (Off i₀) (Off i₀) k} (hY : Yᵀ = Y) (h : KerLE1 Y) :
    ∃ X : Matrix κ κ k, Xᵀ = X ∧ restr i₀ X = Y ∧ X.det ≠ 0 := by
  obtain ⟨w, hw⟩ := h
  by_cases hinj : ∀ x, Y *ᵥ x = 0 → x = 0
  · refine ⟨border i₀ Y 0 1, border_transpose i₀ hY _ _, restr_border i₀ _ _ _, ?_⟩
    intro hdet
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    rw [border_mulVec_eq_zero_iff] at hv0
    obtain ⟨h1, h2⟩ := hv0
    have ht : v i₀ = 0 := by simpa using h2
    rw [ht, zero_smul, add_zero] at h1
    exact hv (eq_zero_of_off i₀ v (hinj _ h1) ht)
  · push Not at hinj
    obtain ⟨x, hx, hx0⟩ := hinj
    obtain ⟨c, hc⟩ := hw x hx
    have hc0 : c ≠ 0 := by
      rintro rfl; apply hx0; simp [hc]
    have hw0 : w ≠ 0 := by
      intro h; apply hx0; simp [hc, h]
    have hYw : Y *ᵥ w = 0 := by
      have : Y *ᵥ (c • w) = 0 := hc ▸ hx
      rw [Matrix.mulVec_smul] at this
      exact (smul_eq_zero.mp this).resolve_left hc0
    obtain ⟨j₀, hj₀⟩ : ∃ j, w j ≠ 0 := by
      by_contra hh; push Not at hh; exact hw0 (funext hh)
    have hyw : (Pi.single j₀ (1 : k) : Off i₀ → k) ⬝ᵥ w ≠ 0 := by simpa using hj₀
    refine ⟨border i₀ Y (Pi.single j₀ 1) 0, border_transpose i₀ hY _ _, restr_border i₀ _ _ _, ?_⟩
    intro hdet
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    rw [border_mulVec_eq_zero_iff] at hv0
    obtain ⟨h1, h2⟩ := hv0
    have hsym : w ⬝ᵥ (Y *ᵥ (fun l : Off i₀ => v l.val)) = 0 := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hY, hYw, zero_dotProduct]
    have h3 : v i₀ * (w ⬝ᵥ (Pi.single j₀ (1 : k) : Off i₀ → k)) = 0 := by
      have := congrArg (fun z => w ⬝ᵥ z) h1
      simpa [dotProduct_add, hsym, dotProduct_smul] using this
    rw [dotProduct_comm] at h3
    have ht : v i₀ = 0 := (mul_eq_zero.mp h3).resolve_right hyw
    rw [ht, zero_smul, add_zero] at h1
    obtain ⟨c', hc'⟩ := hw _ h1
    rw [ht, hc'] at h2
    simp only [mul_zero, add_zero, dotProduct_smul, smul_eq_mul] at h2
    have hc'0 : c' = 0 := (mul_eq_zero.mp h2).resolve_right hyw
    apply hv
    apply eq_zero_of_off i₀ v _ ht
    rw [hc', hc'0, zero_smul]


/-- Auxiliary statement of Sublemma K, by strong induction on the cardinality. -/
theorem exists_kerLE1_aux (n : ℕ) : ∀ (ι : Type u) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ M : Matrix ι ι k, Mᵀ = M → ∃ U : Matrix ι ι k, Uᵀ = U ∧ U.det ≠ 0 ∧ KerLE1 (M + U) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ι _ _ hn M hM
  by_cases he : IsEmpty ι
  · refine ⟨1, by simp, by simp, 0, fun x _ => ⟨0, ?_⟩⟩
    funext i; exact (he.false i).elim
  · rw [not_isEmpty_iff] at he
    obtain ⟨i₀⟩ := he
    have hcard : Fintype.card (Off i₀) < n :=
      hn ▸ Fintype.card_subtype_lt (p := fun j => j ≠ i₀) (x := i₀) (by simp)
    have hs : ∀ a b, M a b = M b a := fun a b => congrFun (congrFun hM b) a
    have hM' : (restr i₀ M)ᵀ = restr i₀ M := by
      ext i j; exact hs _ _
    obtain ⟨U', hU'T, hU'd, w', hw'⟩ := ih _ hcard (Off i₀) rfl (restr i₀ M) hM'
    set M' := restr i₀ M with hM'def
    set N' := M' + U' with hN'def
    have hN'T : N'ᵀ = N' := by
      rw [hN'def, Matrix.transpose_add, hM', hU'T]
    obtain ⟨m, hm⟩ : ∃ m : Off i₀ → k, m = fun j => M j.val i₀ := ⟨_, rfl⟩
    have hMb : M = border i₀ M' m (M i₀ i₀) := by
      ext i j
      simp only [border]
      by_cases hi : i = i₀ <;> by_cases hj : j = i₀
      · subst hi; subst hj; simp
      · simp [hi, hj, hm]
        exact hs _ _
      · simp [hi, hj, hm]
      · simp [hi, hj, hM'def, restr]
    have key : ∃ y : Off i₀ → k, (∀ x, N' *ᵥ x = 0 → x = 0) ∨ (N' *ᵥ w' = 0 ∧ (m + y) ⬝ᵥ w' ≠ 0) := by
      by_cases hinj : ∀ x, N' *ᵥ x = 0 → x = 0
      · exact ⟨0, Or.inl hinj⟩
      · push Not at hinj
        obtain ⟨x, hx, hx0⟩ := hinj
        obtain ⟨c, hc⟩ := hw' x hx
        have hc0 : c ≠ 0 := by
          rintro rfl; apply hx0; simp [hc]
        have hw0 : w' ≠ 0 := by
          intro h; apply hx0; simp [hc, h]
        have hNw : N' *ᵥ w' = 0 := by
          have : N' *ᵥ (c • w') = 0 := hc ▸ hx
          rw [Matrix.mulVec_smul] at this
          exact (smul_eq_zero.mp this).resolve_left hc0
        obtain ⟨j₀, hj₀⟩ : ∃ j, w' j ≠ 0 := by
          by_contra hh; push Not at hh; exact hw0 (funext hh)
        refine ⟨-m + Pi.single j₀ 1, Or.inr ⟨hNw, ?_⟩⟩
        rw [add_neg_cancel_left]
        simpa using hj₀
    obtain ⟨y, hy⟩ := key
    have hUunit : IsUnit U'.det := isUnit_iff_ne_zero.mpr hU'd
    refine ⟨border i₀ U' y (y ⬝ᵥ (U'⁻¹ *ᵥ y) + 1), border_transpose i₀ hU'T _ _, ?_, ?_⟩
    · intro hdet
      obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
      rw [border_mulVec_eq_zero_iff] at hv0
      obtain ⟨h1, h2⟩ := hv0
      obtain ⟨x, hxd⟩ : ∃ x, x = fun l : Off i₀ => v l.val := ⟨_, rfl⟩
      rw [← hxd] at h1 h2
      have hx : x = -(v i₀ • (U'⁻¹ *ᵥ y)) := by
        have h1' : U' *ᵥ x = -(v i₀ • y) := eq_neg_of_add_eq_zero_left h1
        calc x = (U'⁻¹ * U') *ᵥ x := by rw [Matrix.nonsing_inv_mul _ hUunit, Matrix.one_mulVec]
          _ = U'⁻¹ *ᵥ (U' *ᵥ x) := by rw [Matrix.mulVec_mulVec]
          _ = _ := by rw [h1', Matrix.mulVec_neg, Matrix.mulVec_smul]
      have h2' : y ⬝ᵥ x = -(v i₀ * (y ⬝ᵥ (U'⁻¹ *ᵥ y))) := by
        rw [hx, dotProduct_neg, dotProduct_smul, smul_eq_mul]
      have ht : v i₀ = 0 := by linear_combination h2 - h2'
      apply hv
      apply eq_zero_of_off i₀ v _ ht
      rw [← hxd, hx, ht]; simp
    · have hsum : border i₀ M' m (M i₀ i₀) + border i₀ U' y (y ⬝ᵥ (U'⁻¹ *ᵥ y) + 1)
          = border i₀ N' (m + y) (M i₀ i₀ + (y ⬝ᵥ (U'⁻¹ *ᵥ y) + 1)) := by
        ext i j
        simp only [Matrix.add_apply, border]
        split_ifs <;> simp [hN'def]
      have hsum' : M + border i₀ U' y (y ⬝ᵥ (U'⁻¹ *ᵥ y) + 1)
          = border i₀ N' (m + y) (M i₀ i₀ + (y ⬝ᵥ (U'⁻¹ *ᵥ y) + 1)) := by
        rw [← hsum, ← hMb]
      rw [hsum']
      rcases hy with hinj | ⟨hNw, hdot⟩
      · have hNd : N'.det ≠ 0 := fun hd => by
          obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
          exact hv (hinj v hv0)
        have hNunit : IsUnit N'.det := isUnit_iff_ne_zero.mpr hNd
        refine ⟨fun i => if h : i = i₀ then 1 else (-(N'⁻¹ *ᵥ (m + y))) ⟨i, h⟩, fun v hv => ⟨v i₀, ?_⟩⟩
        rw [border_mulVec_eq_zero_iff] at hv
        obtain ⟨h1, h2⟩ := hv
        obtain ⟨x, hxd⟩ : ∃ x, x = fun l : Off i₀ => v l.val := ⟨_, rfl⟩
        rw [← hxd] at h1 h2
        have hx : x = v i₀ • (-(N'⁻¹ *ᵥ (m + y))) := by
          have h1' : N' *ᵥ x = -(v i₀ • (m + y)) := eq_neg_of_add_eq_zero_left h1
          calc x = (N'⁻¹ * N') *ᵥ x := by rw [Matrix.nonsing_inv_mul _ hNunit, Matrix.one_mulVec]
            _ = N'⁻¹ *ᵥ (N' *ᵥ x) := by rw [Matrix.mulVec_mulVec]
            _ = _ := by rw [h1', Matrix.mulVec_neg, Matrix.mulVec_smul, smul_neg]
        funext j
        by_cases hj : j = i₀
        · simp [hj]
        · have := congrFun hx ⟨j, hj⟩
          simp only [hxd] at this
          simp [hj, this]
      · refine ⟨fun i => if h : i = i₀ then 0 else w' ⟨i, h⟩, fun v hv => ?_⟩
        rw [border_mulVec_eq_zero_iff] at hv
        obtain ⟨h1, h2⟩ := hv
        obtain ⟨x, hxd⟩ : ∃ x, x = fun l : Off i₀ => v l.val := ⟨_, rfl⟩
        rw [← hxd] at h1 h2
        have hsym : w' ⬝ᵥ (N' *ᵥ x) = 0 := by
          rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hN'T, hNw, zero_dotProduct]
        have h3 : v i₀ * (w' ⬝ᵥ (m + y)) = 0 := by
          have := congrArg (fun z => w' ⬝ᵥ z) h1
          rw [dotProduct_add]
          simp only [dotProduct_add, hsym, dotProduct_smul, smul_eq_mul, zero_add,
            dotProduct_zero] at this
          linear_combination this
        rw [dotProduct_comm] at h3
        have ht : v i₀ = 0 := (mul_eq_zero.mp h3).resolve_right hdot
        rw [ht, zero_smul, add_zero] at h1
        obtain ⟨c, hc⟩ := hw' _ h1
        refine ⟨c, ?_⟩
        funext j
        by_cases hj : j = i₀
        · simp [hj, ht]
        · have := congrFun hc ⟨j, hj⟩
          simp only [hxd] at this
          simp [hj, this]

/-- **Sublemma K.** For every symmetric $M$ there is an invertible symmetric $U$ such that the kernel of $M + U$ lies
in a line. -/
theorem exists_kerLE1 (M : Matrix κ κ k) (hM : Mᵀ = M) :
    ∃ U : Matrix κ κ k, Uᵀ = U ∧ U.det ≠ 0 ∧ KerLE1 (M + U) :=
  exists_kerLE1_aux _ κ rfl M hM

/-- **Kernel split.** A singular symmetric $C$ is congruent to a matrix with a zero row $i_0$. -/
theorem exists_split_of_det_eq_zero {C : Matrix κ κ k} (h : C.det = 0) :
    ∃ (Q : Matrix κ κ k) (i₀ : κ), Q.det ≠ 0 ∧ ∀ j, (Qᵀ * C * Q) i₀ j = 0 := by
  obtain ⟨v, hv, hvC⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    exact hv (funext fun i => by_contra fun hne => hcon ⟨i, hne⟩)
  refine ⟨Matrix.updateCol (1 : Matrix κ κ k) i₀ v, i₀, ?_, ?_⟩
  · have h1 : (Matrix.updateCol (1 : Matrix κ κ k) i₀ v).det = v i₀ := by
      have := Matrix.cramer_apply (1 : Matrix κ κ k) v i₀
      rw [Matrix.cramer_one] at this
      simpa using this.symm
    rw [h1]; exact hi₀
  · intro j
    have h2 : ((Matrix.updateCol (1 : Matrix κ κ k) i₀ v)ᵀ * C) i₀ = v ᵥ* C := by
      ext b
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.transpose_apply]
    rw [Matrix.mul_apply]
    simp [h2, hvC]

/-- If row and column $i_0$ of $C$ vanish, $\det(1 - C\Delta) = \det(1 - \tilde C\tilde\Delta)$ for the restrictions
to $\kappa \setminus \{i_0\}$. -/
theorem det_one_sub_mul_of_row_col_zero (i₀ : κ) {C : Matrix κ κ k} (Δ : Matrix κ κ k) (hrow : ∀ j, C i₀ j = 0)
    (hcol : ∀ i, C i i₀ = 0) : (1 - C * Δ).det = (1 - restr i₀ C * restr i₀ Δ).det := by
  have hM := Matrix.twoBlockTriangular_det (1 - C * Δ) (fun j => j ≠ i₀) (by
    intro i hi j hj
    have hii : i = i₀ := by simpa using hi
    subst hii
    have hne : i ≠ j := fun e => hj e.symm
    simp [Matrix.sub_apply, Matrix.mul_apply, hrow, hne])
  rw [hM]
  have hA : Matrix.toSquareBlockProp (1 - C * Δ) (fun j => j ≠ i₀) = 1 - restr i₀ C * restr i₀ Δ := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.toSquareBlockProp, Matrix.toBlock_apply, Matrix.sub_apply, restr, Matrix.mul_apply,
      Matrix.submatrix_apply, Matrix.one_apply, Subtype.mk.injEq]
    congr 1
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀, hcol, zero_mul, zero_add]
  have hB : Matrix.toSquareBlockProp (1 - C * Δ) (fun j => ¬ j ≠ i₀) = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    have e1 : i = i₀ := by simpa using hi
    have e2 : j = i₀ := by simpa using hj
    subst e1; subst e2
    simp [Matrix.toSquareBlockProp, Matrix.toBlock_apply, Matrix.mul_apply, hrow]
  rw [hA, hB]; simp

end Finite

/-- The singular step of the main lemma: split off a kernel direction, solve on the complement, complete. -/
lemma singular_step {κ : Type*} [Fintype κ] [DecidableEq κ] (C B : Matrix κ κ k) (hC : Cᵀ = C) (hB : Bᵀ = B)
    (h : C.det = 0)
    (IH : ∀ i₀ : κ, ∀ C' B' : Matrix (Off i₀) (Off i₀) k, C'ᵀ = C' → B'ᵀ = B' →
      ∃ Δ : Matrix (Off i₀) (Off i₀) k, Δᵀ = Δ ∧ (1 - C' * Δ).det ≠ 0 ∧ KerLE1 (B' + Δ)) :
    ∃ Δ : Matrix κ κ k, Δᵀ = Δ ∧ (1 - C * Δ).det ≠ 0 ∧ (B + Δ).det ≠ 0 := by
  obtain ⟨Q, i₀, hQ, hrow⟩ := exists_split_of_det_eq_zero h
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.2 hQ
  obtain ⟨C', hC'def⟩ : ∃ C', C' = Qᵀ * C * Q := ⟨_, rfl⟩
  rw [← hC'def] at hrow
  have hC' : C'ᵀ = C' := by simp [hC'def, transpose_mul, hC, Matrix.mul_assoc]
  have hcol : ∀ i, C' i i₀ = 0 := fun i => by
    have := congrFun (congrFun hC' i) i₀
    rw [transpose_apply] at this
    rw [← this]; exact hrow i
  obtain ⟨B', hB'def⟩ : ∃ B', B' = Q⁻¹ * B * Q⁻¹ᵀ := ⟨_, rfl⟩
  have hB' : B'ᵀ = B' := by simp [hB'def, transpose_mul, hB, Matrix.mul_assoc]
  have hrC : (restr i₀ C')ᵀ = restr i₀ C' := by
    ext i j; simp only [restr, transpose_apply, submatrix_apply]; exact congrFun (congrFun hC' i.1) j.1
  have hrB : (restr i₀ B')ᵀ = restr i₀ B' := by
    ext i j; simp only [restr, transpose_apply, submatrix_apply]; exact congrFun (congrFun hB' i.1) j.1
  obtain ⟨Δt, hΔt, h1, h2⟩ := IH i₀ (restr i₀ C') (restr i₀ B') hrC hrB
  obtain ⟨X, hX, hXr, hXd⟩ := exists_completion i₀ (Y := restr i₀ B' + Δt)
    (by rw [transpose_add, hrB, hΔt]) h2
  obtain ⟨Δ', hΔ'def⟩ : ∃ Δ', Δ' = X - B' := ⟨_, rfl⟩
  have hΔ' : Δ'ᵀ = Δ' := by rw [hΔ'def, transpose_sub, hX, hB']
  have hrΔ' : restr i₀ Δ' = Δt := by
    have : restr i₀ Δ' = restr i₀ X - restr i₀ B' := by ext i j; simp [restr, hΔ'def]
    rw [this, hXr, add_sub_cancel_left]
  have hdet1 : (1 - C' * Δ').det ≠ 0 := by
    rw [det_one_sub_mul_of_row_col_zero i₀ Δ' hrow hcol, hrΔ']; exact h1
  have hBX : B' + Δ' = X := by rw [hΔ'def, add_sub_cancel]
  refine ⟨Q * Δ' * Qᵀ, by simp [transpose_mul, hΔ', Matrix.mul_assoc], ?_, ?_⟩
  · have hC : C = Q⁻¹ᵀ * C' * Q⁻¹ := by
      rw [hC'def, transpose_nonsing_inv]
      simp only [← Matrix.mul_assoc]
      rw [nonsing_inv_mul _ (by rw [det_transpose]; exact hQu), Matrix.one_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ hQu, Matrix.mul_one]
    have hone : (1 : Matrix κ κ k) = Q⁻¹ᵀ * Qᵀ := by
      rw [transpose_nonsing_inv, nonsing_inv_mul _ (by rw [det_transpose]; exact hQu)]
    have : 1 - C * (Q * Δ' * Qᵀ) = Q⁻¹ᵀ * (1 - C' * Δ') * Qᵀ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← hone, hC]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q⁻¹ Q, nonsing_inv_mul _ hQu, Matrix.one_mul]
    rw [this, det_mul, det_mul, det_transpose, det_transpose, det_nonsing_inv]
    refine mul_ne_zero (mul_ne_zero ?_ hdet1) hQ
    rw [Ring.inverse_eq_inv']; exact inv_ne_zero hQ
  · have hB2 : B = Q * B' * Qᵀ := by
      rw [hB'def]
      simp only [← Matrix.mul_assoc]
      rw [mul_nonsing_inv _ hQu, Matrix.one_mul, Matrix.mul_assoc, ← transpose_mul,
        mul_nonsing_inv _ hQu, transpose_one, Matrix.mul_one]
    have : B + Q * Δ' * Qᵀ = Q * X * Qᵀ := by
      rw [hB2, ← hBX, Matrix.mul_add, Matrix.add_mul]
    rw [this, det_mul, det_mul, det_transpose]
    exact mul_ne_zero (mul_ne_zero hQ hXd) hQ

/-- **Main lemma.** For symmetric $C, B$ on a finite type there is a symmetric $\Delta$ with $\det(1 - C\Delta) \ne 0$
whose sum with $B$ has kernel in a line. -/
theorem exists_det_one_sub_kerLE1 (n : ℕ) : ∀ (κ : Type*) [Fintype κ] [DecidableEq κ], Fintype.card κ = n →
    ∀ (C B : Matrix κ κ k), Cᵀ = C → Bᵀ = B →
    ∃ Δ : Matrix κ κ k, Δᵀ = Δ ∧ (1 - C * Δ).det ≠ 0 ∧ KerLE1 (B + Δ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro κ _ _ hn C B hC hB
  by_cases hdet : C.det = 0
  · obtain ⟨Δ, hΔ, h1, h2⟩ := singular_step C B hC hB hdet (fun i₀ C' B' hC' hB' => by
      have hlt : Fintype.card (Off i₀) < n := by
        rw [← hn]; exact Fintype.card_subtype_lt (p := fun j => j ≠ i₀) (x := i₀) (by simp)
      exact ih _ hlt (Off i₀) rfl C' B' hC' hB')
    exact ⟨Δ, hΔ, h1, kerLE1_of_det_ne_zero h2⟩
  · have hCu : IsUnit C.det := isUnit_iff_ne_zero.2 hdet
    have hCi : C⁻¹ᵀ = C⁻¹ := by rw [transpose_nonsing_inv, hC]
    obtain ⟨U, hU, hUd, hK⟩ := exists_kerLE1 (B + C⁻¹) (by rw [transpose_add, hB, hCi])
    refine ⟨C⁻¹ + U, by rw [transpose_add, hCi, hU], ?_, by rwa [← add_assoc]⟩
    rw [Matrix.mul_add, mul_nonsing_inv _ hCu, sub_add_cancel_left, det_neg, det_mul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero hdet hUd)

/-- **Main lemma, singular case.** For symmetric $C, B$ with $C$ singular there is a symmetric $\Delta$ with
$\det(1 - C\Delta) \ne 0$ and $\det(B + \Delta) \ne 0$. -/
theorem exists_det_one_sub_det {κ : Type*} [Fintype κ] [DecidableEq κ] (C B : Matrix κ κ k) (hC : Cᵀ = C)
    (hB : Bᵀ = B) (h : C.det = 0) :
    ∃ Δ : Matrix κ κ k, Δᵀ = Δ ∧ (1 - C * Δ).det ≠ 0 ∧ (B + Δ).det ≠ 0 :=
  singular_step C B hC hB h (fun _ C' B' hC' hB' => exists_det_one_sub_kerLE1 _ _ rfl C' B' hC' hB')

/-- **Normal form of the two-row statement.** For symmetric $C, B$ with $C$ singular there is a symmetric $T$ with
$\det(1 + CT) \ne 0$ and $\det((1 + BC)T + B) \ne 0$. -/
theorem exists_two_rows_normal {κ : Type*} [Fintype κ] [DecidableEq κ] (C B : Matrix κ κ k) (hC : Cᵀ = C)
    (hB : Bᵀ = B) (h : C.det = 0) :
    ∃ T : Matrix κ κ k, Tᵀ = T ∧ (1 + C * T).det ≠ 0 ∧ ((1 + B * C) * T + B).det ≠ 0 := by
  obtain ⟨Y, hY, hE, hYB⟩ := exists_det_one_sub_det C B hC hB h
  obtain ⟨E, hEdef⟩ : ∃ E, E = 1 - C * Y := ⟨_, rfl⟩
  obtain ⟨F, hFdef⟩ : ∃ F, F = 1 - Y * C := ⟨_, rfl⟩
  rw [← hEdef] at hE
  have hFE : F = Eᵀ := by rw [hFdef, hEdef, transpose_sub, transpose_one, transpose_mul, hC, hY]
  have hEu : IsUnit E.det := isUnit_iff_ne_zero.2 hE
  have hFu : IsUnit F.det := by rw [hFE, det_transpose]; exact hEu
  obtain ⟨T, hTdef⟩ : ∃ T, T = F⁻¹ * Y := ⟨_, rfl⟩
  have hFT : F * T = Y := by rw [hTdef, ← Matrix.mul_assoc, mul_nonsing_inv _ hFu, Matrix.one_mul]
  have hYE : Y * E = F * Y := by
    rw [hEdef, hFdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  have hT : Tᵀ = T := by
    have h1 : Tᵀ = Y * E⁻¹ := by
      rw [hTdef, transpose_mul, hY, transpose_nonsing_inv, hFE, transpose_transpose]
    rw [h1, hTdef]
    calc Y * E⁻¹ = F⁻¹ * F * Y * E⁻¹ := by rw [nonsing_inv_mul _ hFu, Matrix.one_mul]
      _ = F⁻¹ * (F * Y) * E⁻¹ := by simp only [Matrix.mul_assoc]
      _ = F⁻¹ * (Y * E) * E⁻¹ := by rw [hYE]
      _ = F⁻¹ * Y := by rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hEu, Matrix.mul_one]
  have hEC : E * C = C * F := by
    rw [hEdef, hFdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  have hT2 : T = Y + Y * C * T := by
    have h0 : T - Y * C * T = Y := by
      have e : F * T = T - Y * C * T := by rw [hFdef, Matrix.sub_mul, Matrix.one_mul]
      rw [← e, hFT]
    calc T = (T - Y * C * T) + Y * C * T := (sub_add_cancel _ _).symm
      _ = Y + Y * C * T := by rw [h0]
  have hinv : E * (1 + C * T) = 1 := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hEC, Matrix.mul_assoc, hFT, hEdef, sub_add_cancel]
  have h1 : (1 + C * T).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hinv
    rw [det_mul, h0, mul_zero, det_one] at this
    exact zero_ne_one this
  refine ⟨T, hT, h1, ?_⟩
  have : (1 + B * C) * T + B = (Y + B) * (1 + C * T) := by
    calc (1 + B * C) * T + B = T + B * C * T + B := by rw [Matrix.add_mul, Matrix.one_mul]
      _ = (Y + Y * C * T) + B * C * T + B := by rw [← hT2]
      _ = (Y + B) * (1 + C * T) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc]
        abel
  rw [this, det_mul]
  exact mul_ne_zero (by rwa [add_comm]) h1

variable {g : ℕ}

lemma blocks_mul_spN' (γ : Sp g k) (T : Matrix (Fin g) (Fin g) k) (hT : Tᵀ = T) :
    blkA (γ * spN T hT) = blkA γ ∧ blkB (γ * spN T hT) = blkA γ * T + blkB γ ∧
      blkC (γ * spN T hT) = blkC γ ∧ blkD (γ * spN T hT) = blkC γ * T + blkD γ := by
  have h : ((γ * spN T hT : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) =
      fromBlocks (blkA γ) (blkB γ) (blkC γ) (blkD γ) * fromBlocks 1 T 0 1 := by
    rw [← sp_eq_fromBlocks]; rfl
  simp only [blkA, blkB, blkC, blkD, h, fromBlocks_multiply]
  simp

lemma blocks_spM_mul' (a : GL (Fin g) k) (γ : Sp g k) :
    blkA (spM a * γ) = (a : Matrix (Fin g) (Fin g) k) * blkA γ ∧
      blkB (spM a * γ) = (a : Matrix (Fin g) (Fin g) k) * blkB γ ∧
      blkC (spM a * γ) = ((a⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ * blkC γ ∧
      blkD (spM a * γ) = ((a⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ * blkD γ := by
  have h : ((spM a * γ : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) =
      fromBlocks (a : Matrix (Fin g) (Fin g) k) 0 0 (((a⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ) *
        fromBlocks (blkA γ) (blkB γ) (blkC γ) (blkD γ) := by
    rw [← sp_eq_fromBlocks]; rfl
  simp only [blkA, blkB, blkC, blkD, h, fromBlocks_multiply]
  simp

lemma blocks_spW_mul' (γ : Sp g k) : blkA (spW * γ) = blkC γ ∧ blkB (spW * γ) = blkD γ := by
  have h : ((spW * γ : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) =
      fromBlocks 0 1 (-1) 0 * fromBlocks (blkA γ) (blkB γ) (blkC γ) (blkD γ) := by
    rw [← sp_eq_fromBlocks]; rfl
  simp only [blkA, blkB, h, fromBlocks_multiply]
  simp

/-- The case $\det c = 0$ of `TwoRowTransversal`. -/
lemma twoRow_of_det_blkC (γ : Sp g k) (hc : (blkC γ).det = 0) :
    ∃ T : Matrix (Fin g) (Fin g) k, Tᵀ = T ∧ (blkC γ * T + blkD γ).det ≠ 0 ∧ (blkA γ * T + blkB γ).det ≠ 0 := by
  obtain ⟨T₀, hT₀, hd⟩ := exists_symm_det_ne γ
  obtain ⟨hA1, hB1, hC1, hD1⟩ := blocks_mul_spN' γ T₀ hT₀
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ₁, γ₁ = γ * spN T₀ hT₀ := ⟨_, rfl⟩
  rw [← hγ₁] at hA1 hB1 hC1 hD1
  obtain ⟨D, hDdef⟩ : ∃ D, D = blkC γ * T₀ + blkD γ := ⟨_, rfl⟩
  rw [← hDdef] at hD1
  have hdD : D.det ≠ 0 := by rw [hDdef]; simpa [blkC, blkD] using hd
  have hDu : IsUnit D.det := isUnit_iff_ne_zero.2 hdD
  obtain ⟨α, hα⟩ : ∃ α : GL (Fin g) k, (α : Matrix (Fin g) (Fin g) k) = Dᵀ :=
    ⟨glOfDet Dᵀ (by rwa [det_transpose]), rfl⟩
  obtain ⟨hA2, hB2, hC2, hD2⟩ := blocks_spM_mul' α γ₁
  obtain ⟨γ₂, hγ₂⟩ : ∃ γ₂, γ₂ = spM α * γ₁ := ⟨_, rfl⟩
  rw [← hγ₂] at hA2 hB2 hC2 hD2
  have hαi : ((α⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ = D⁻¹ := by
    rw [Matrix.coe_units_inv, hα, transpose_nonsing_inv, transpose_transpose]
  rw [hαi, hC1] at hC2
  rw [hαi, hD1, nonsing_inv_mul _ hDu] at hD2
  rw [hα, hA1] at hA2
  rw [hα, hB1] at hB2
  obtain ⟨-, s2, s3, s4⟩ := sp_blocks γ₂
  rw [hD2] at s2 s3 s4
  have hCs : (blkC γ₂)ᵀ = blkC γ₂ := by simpa using s2.symm
  have hBs : (blkB γ₂)ᵀ = blkB γ₂ := by simpa using s3
  have hA : blkA γ₂ = 1 + blkB γ₂ * blkC γ₂ := by
    have : (blkA γ₂)ᵀ = 1 + (blkC γ₂)ᵀ * blkB γ₂ := by rw [← s4]; simp
    rw [← transpose_transpose (blkA γ₂), this, transpose_add, transpose_one, transpose_mul, hBs,
      transpose_transpose]
  have hCd : (blkC γ₂).det = 0 := by rw [hC2, det_mul, hc, mul_zero]
  obtain ⟨T₁, hT₁, h1, h2⟩ := exists_two_rows_normal (blkC γ₂) (blkB γ₂) hCs hBs hCd
  refine ⟨T₀ + T₁, by rw [transpose_add, hT₀, hT₁], ?_, ?_⟩
  · have hc' : blkC γ = D * blkC γ₂ := by
      rw [hC2, ← Matrix.mul_assoc, mul_nonsing_inv _ hDu, Matrix.one_mul]
    have : blkC γ * (T₀ + T₁) + blkD γ = D * (1 + blkC γ₂ * T₁) := by
      rw [Matrix.mul_add D, Matrix.mul_one, ← Matrix.mul_assoc, ← hc', hDdef, Matrix.mul_add]
      abel
    rw [this, det_mul]
    exact mul_ne_zero hdD h1
  · have : Dᵀ * (blkA γ * (T₀ + T₁) + blkB γ) = (1 + blkB γ₂ * blkC γ₂) * T₁ + blkB γ₂ := by
      rw [← hA, hA2, hB2]
      simp only [Matrix.mul_add, Matrix.mul_assoc]
      abel
    intro h0
    apply h2
    rw [← this, det_mul, h0, mul_zero]

/-- **A common transversal for the two rows, for every field** (every genus $g$): the named input
`TwoRowTransversal g k` holds. See the module docstring for the method. -/
@[kb "kudla1996" "§I.1 (the big cell $PwP$ and its translates) [unverified]"]
theorem twoRowTransversal : TwoRowTransversal g k := by
  refine ⟨fun γ hor => ?_⟩
  by_cases hc : (blkC γ).det = 0
  · exact twoRow_of_det_blkC γ hc
  · have ha : (blkA γ).det = 0 := hor.resolve_left hc
    have hc' : (blkC (spW * γ)).det = 0 := by rw [blkC_spW_mul, det_neg, ha, mul_zero]
    obtain ⟨T, hT, h1, h2⟩ := twoRow_of_det_blkC (spW * γ) hc'
    obtain ⟨hA, hB⟩ := blocks_spW_mul' γ
    refine ⟨T, hT, by rwa [hA, hB] at h2, ?_⟩
    rw [blkC_spW_mul, blkD_spW_mul, neg_mul, ← neg_add, det_neg] at h1
    exact right_ne_zero_of_mul h1

/-- **The presentation of $\mathrm{Sp}_{2g}(k)$ from the connectedness input alone** (every field $k$, every genus
$g$; hypothesis `hC : CellGraphConnected g k`): the named input `SiegelPresentation g k` holds, the other condition
`TwoRowTransversal g k` being proved (`twoRowTransversal`). -/
@[kb "kudla1996" "§I.1 (generators $m(a)$, $n(b)$, $w$ of $\\mathrm{Sp}(W)$ and their relations) [unverified]"]
theorem siegelPresentation_of_cellGraphConnected (hC : CellGraphConnected g k) : SiegelPresentation.{u} g k :=
  siegelPresentation_of_twoCell hC twoRowTransversal

/-- **The small-field input from the connectedness input** (every genus $g$; hypothesis `h`: `CellGraphConnected g k`
for $k$ finite with at most $3g$ elements): the named input `SiegelPresentationSmallField g k` holds. -/
@[kb "kudla1996" "§I.1 (generators $m(a)$, $n(b)$, $w$ of $\\mathrm{Sp}(W)$ and their relations; finite fields with at most $3g$ elements) [unverified]"]
theorem siegelPresentationSmallField_of_cellGraphConnected
    (h : Finite k → Nat.card k ≤ 3 * g → CellGraphConnected g k) : SiegelPresentationSmallField.{u} g k :=
  ⟨fun hf hc => siegelPresentation_of_cellGraphConnected (h hf hc)⟩

end QuadFormsKB.WeilRep.Genus
