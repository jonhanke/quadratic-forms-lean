/-
# One class in the genus of $\mathbb Z$-maximal lattices for the sum of $n$ squares (Shimura 2004, §12.12)

Shimura (2004, §12.12, p. 122) uses that for $\varphi[x] = x\,{}^tx$ on $V = \mathbb Q^n$, $n \le 9$, the genus of
$\mathbb Z$-maximal lattices consists of a single class ([S02a, Lemma 1.6]); with Lemma 9.23 this is one
$SO^\varphi$-class. In the library this is the named input `SumSquaresOneClass` (for $n = 5, 7, 9$), the only input of
Theorem 12.14 (iv) (`theorem_12_14_iv_of_local`).

**This file** reduces `SumSquaresOneClass` to two statements about lattices on $V = \mathbb Q^n$ with the sum of
squares $I_n$, both stated for a single dimension $n$:

* `SumSqMaxContainsIntVec n`: every $\mathbb Z$-maximal lattice $M$ contains $\gamma\mathbb Z^n$ for some rational
  isometry $\gamma \in O(I_n)(\mathbb Q)$ (equivalently: $M$ contains a lattice with an orthonormal basis);
* `SumSqMaxOverIntVec n`: any two $\mathbb Z$-maximal lattices containing $\mathbb Z^n$ are isometric.

The reduction (`sumSquaresOneClass_of`): all $\mathbb Z$-maximal lattices form one genus (O'Meara 102:3), so a lattice
$M$ in the $SO$-genus of a $\mathbb Z$-maximal $L$ is $\mathbb Z$-maximal; move $L$ and $M$ by isometries to
$\mathbb Z$-maximal lattices over $\mathbb Z^n$; these are isometric; and for odd $n$ an isometry can be made proper by
composing with $-1$ (which fixes every lattice), the step that replaces Shimura's Lemma 9.23.

Indices are 0-based (coordinates $x_0, \dots, x_{n-1}$).
-/
import QuadFormsKB.Literature.Shimura2004.Fundamental.Theorem116
import QuadFormsKB.Literature.OMeara.Sec106Rank9
import QuadFormsKB.Literature.OMeara.Sec102Three
import QuadFormsKB.Literature.OMeara.Sec82Max

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Lattices

/-! ### The two statements -/

/-- **Every $\mathbb Z$-maximal lattice for the sum of $n$ squares contains an isometric copy of $\mathbb Z^n$**: for
every lattice $M$ on $V = \mathbb Q^n$ that is $\mathbb Z$-maximal for $\varphi[x] = x_0^2 + \dots + x_{n-1}^2$
(`IsGMaximal (sosQ n) M`: $\varphi[M] \subseteq \mathbb Z$ and $M$ is maximal with this property) there is a rational
isometry $\gamma$ of $\varphi$ with $\gamma\mathbb Z^n \subseteq M$. Here `n` is the dimension. (Equivalently: $M$
contains a sublattice with an orthonormal basis.) -/
structure SumSqMaxContainsIntVec (n : ℕ) : Prop where
  holds : ∀ M : Lat ℚ n, IsGMaximal (sosQ n) M →
    ∃ γ ∈ orthGroup (sosQ n) ℚ, glImage γ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ M.1

/-- **The $\mathbb Z$-maximal lattices over $\mathbb Z^n$ for the sum of $n$ squares are isometric**: if $M$, $M'$ are
lattices on $V = \mathbb Q^n$, both $\mathbb Z$-maximal for $\varphi[x] = x_0^2 + \dots + x_{n-1}^2$ and both
containing $\mathbb Z^n$, then $M' = \gamma M$ for a rational isometry $\gamma$ of $\varphi$ (`IsIsometric`). Here `n`
is the dimension. (Such $M$ are $\mathbb Z^n + \tfrac12 C$ for a maximal doubly even binary code $C$ of length $n$.) -/
structure SumSqMaxOverIntVec (n : ℕ) : Prop where
  holds : ∀ M M' : Lat ℚ n, IsGMaximal (sosQ n) M → IsGMaximal (sosQ n) M' →
    (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ M.1 → (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ M'.1 →
    IsIsometric (sosQ n) M.1 M'.1

/-! ### Auxiliary facts -/

theorem sosQ_hessian (n : ℕ) : (sosQ n).hessian = (2 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) :=
  two_sumSq_hessian n

/-- An isometry of the sum of squares has determinant $\pm 1$. -/
theorem det_sq_eq_one_of_mem_orth {n : ℕ} {γ : GL (Fin n) ℚ} (hγ : γ ∈ orthGroup (sosQ n) ℚ) :
    γ.val.det ^ 2 = 1 := by
  have h : γ.valᵀ * (sosQ n).hessian.map (algebraMap ℚ ℚ) * γ.val = (sosQ n).hessian.map (algebraMap ℚ ℚ) := hγ
  have hm : (sosQ n).hessian.map (algebraMap ℚ ℚ) = (sosQ n).hessian := by
    ext i j; simp
  rw [hm, sosQ_hessian] at h
  have h2 := congrArg Matrix.det h
  rw [det_mul, det_mul, det_transpose, det_smul, det_one, mul_one] at h2
  have h0 : (2 : ℚ) ^ Fintype.card (Fin n) ≠ 0 := pow_ne_zero _ two_ne_zero
  have : γ.val.det * γ.val.det = 1 := by
    have := h2
    field_simp at this
    linarith [this]
  rw [sq]; exact this

/-- $-\gamma$ is an isometry when $\gamma$ is. -/
theorem neg_mem_orth {n : ℕ} {γ : GL (Fin n) ℚ} (hγ : γ ∈ orthGroup (sosQ n) ℚ) :
    -γ ∈ orthGroup (sosQ n) ℚ := by
  change (-γ).valᵀ * _ * (-γ).val = _
  have h : γ.valᵀ * _ * γ.val = _ := hγ
  simp only [Units.val_neg, transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  exact h

/-- $-\gamma$ and $\gamma$ have the same image on a submodule. -/
theorem glImage_neg {n : ℕ} (γ : GL (Fin n) ℚ) (L : Submodule (𝓞 ℚ) (Fin n → ℚ)) :
    glImage (-γ) L = glImage γ L := by
  ext x
  simp only [mem_glImage, Units.val_neg, Matrix.neg_mulVec]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨-y, L.neg_mem hy, by rw [Matrix.mulVec_neg]⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨-y, L.neg_mem hy, by rw [Matrix.mulVec_neg, neg_neg]⟩

theorem glImage_mono {n : ℕ} (γ : GL (Fin n) ℚ) {L M : Submodule (𝓞 ℚ) (Fin n → ℚ)} (h : L ≤ M) :
    glImage γ L ≤ glImage γ M :=
  Submodule.map_mono h

/-- **Lemma 9.23 for odd $n$** (the step "one $O^\varphi$-class is one $SO^\varphi$-class"): for odd $n$, isometric
lattices are $SO$-equivalent, since $-1 \in O(V)$ has determinant $-1$ and fixes every lattice. -/
theorem soClassRel_of_isIsometric {n : ℕ} (hn : Odd n) {L M : Lat ℚ n} (h : IsIsometric (sosQ n) L.1 M.1) :
    SOClassRel (sosQ n) L M := by
  obtain ⟨γ, hγ, he⟩ := h
  have hd := det_sq_eq_one_of_mem_orth hγ
  rcases sq_eq_one_iff.mp hd with h1 | h1
  · exact ⟨⟨γ, hγ⟩, h1, Subtype.ext he⟩
  · refine ⟨⟨-γ, neg_mem_orth hγ⟩, ?_, Subtype.ext (by
      change glImage (-γ) L.1 = M.1
      rw [glImage_neg]; exact he)⟩
    change (-γ).val.det = 1
    rw [Units.val_neg, det_neg, h1, Fintype.card_fin, hn.neg_one_pow]
    norm_num

theorem one_submodule_fg_rat : (1 : Submodule (𝓞 ℚ) ℚ).FG := by
  rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _

/-- A lattice in the genus of a $\mathbb Z$-maximal lattice is $\mathbb Z$-maximal. -/
theorem isGMaximal_of_sameGenus {n : ℕ} {L M : Lat ℚ n} (hL : IsGMaximal (sosQ n) L)
    (h : SameGenus (sosQ n) L.1 M.1) : IsGMaximal (sosQ n) M :=
  isMaximal_of_sameGenus (sosQ n) one_submodule_fg_rat one_submodule_ne_bot hL h

/-- The image of a $\mathbb Z$-maximal lattice under a rational isometry is $\mathbb Z$-maximal. -/
theorem isGMaximal_image {n : ℕ} {L : Lat ℚ n} (hL : IsGMaximal (sosQ n) L) {γ : GL (Fin n) ℚ}
    (hγ : γ ∈ orthGroup (sosQ n) ℚ) : IsGMaximal (sosQ n) (Lat.image γ L) :=
  isGMaximal_of_sameGenus hL (IsIsometric.sameGenus (sosQ n) ⟨γ, hγ, rfl⟩)

/-- A lattice in the $SO$-genus of $L$ is in the genus of $L$. -/
theorem sameGenus_of_mem_soGenus {n : ℕ} {L M : Lat ℚ n} (h : M ∈ soGenus (sosQ n) L) :
    SameGenus (sosQ n) L.1 M.1 := by
  obtain ⟨g, -, rfl⟩ := h
  have := (orbit_eq_genus (sosQ n) L).le ⟨g, rfl⟩
  exact this

/-- A $\mathbb Z$-maximal lattice is isometric to a $\mathbb Z$-maximal lattice containing $\mathbb Z^n$. -/
theorem exists_isometric_over_intVec {n : ℕ} (h1 : SumSqMaxContainsIntVec n) {L : Lat ℚ n}
    (hL : IsGMaximal (sosQ n) L) :
    ∃ L' : Lat ℚ n, IsGMaximal (sosQ n) L' ∧ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ L'.1 ∧
      IsIsometric (sosQ n) L'.1 L.1 := by
  obtain ⟨γ, hγ, hle⟩ := h1.holds L hL
  have hγi : γ⁻¹ ∈ orthGroup (sosQ n) ℚ := (orthGroup (sosQ n) ℚ).inv_mem hγ
  refine ⟨Lat.image γ⁻¹ L, isGMaximal_image hL hγi, ?_, ⟨γ, hγ, ?_⟩⟩
  · have := glImage_mono γ⁻¹ hle
    rwa [← glImage_mul, inv_mul_cancel, glImage_one] at this
  · change glImage γ (glImage γ⁻¹ L.1) = L.1
    rw [← glImage_mul, mul_inv_cancel, glImage_one]

/-! ### The reduction -/

/-- **`SumSquaresOneClass` from the two lattice statements** for $n = 5, 7, 9$: if every $\mathbb Z$-maximal lattice
for the sum of $n$ squares contains an isometric copy of $\mathbb Z^n$ (`SumSqMaxContainsIntVec n`) and the
$\mathbb Z$-maximal lattices over $\mathbb Z^n$ are isometric (`SumSqMaxOverIntVec n`), then the $SO$-genus of a
$\mathbb Z$-maximal lattice is one $SO$-class. -/
theorem sumSquaresOneClass_of (h1 : ∀ n ∈ ({5, 7, 9} : Finset ℕ), SumSqMaxContainsIntVec n)
    (h2 : ∀ n ∈ ({5, 7, 9} : Finset ℕ), SumSqMaxOverIntVec n) : SumSquaresOneClass := by
  refine ⟨fun n hn L hL M hM => ?_⟩
  have hodd : Odd n := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl <;> decide
  have hM' : IsGMaximal (sosQ n) M := isGMaximal_of_sameGenus hL (sameGenus_of_mem_soGenus hM)
  obtain ⟨L', hL'm, hL'Z, hL'L⟩ := exists_isometric_over_intVec (h1 n hn) hL
  obtain ⟨M', hM'm, hM'Z, hM'M⟩ := exists_isometric_over_intVec (h1 n hn) hM'
  have hLM' := (h2 n hn).holds L' M' hL'm hM'm hL'Z hM'Z
  exact soClassRel_of_isIsometric hodd
    (IsIsometric.trans _ (IsIsometric.trans _ hL'L.symm hLM') hM'M)

/-! ### Every $\mathbb Z$-maximal lattice contains a unimodular lattice -/

section Unimodular

variable {n : ℕ}

theorem sosQ_toQF_eq (x : Fin n → ℚ) : (sosQ n).toQuadraticForm x = ∑ i, x i ^ 2 := by
  rw [omeara_Q_eq]
  exact two_sumSq_evalIn x

theorem eq_zero_of_sosQ_eq_zero {x : Fin n → ℚ} (h : (sosQ n).toQuadraticForm x = 0) : x = 0 := by
  rw [sosQ_toQF_eq] at h
  funext i
  have hle : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have hi : x i ^ 2 = 0 := by linarith [sq_nonneg (x i)]
  simpa using hi

/-- The bilinear form of the sum of squares is nondegenerate. -/
theorem sosQ_associated_nondegenerate (n : ℕ) :
    (QuadraticMap.associated (sosQ n).toQuadraticForm).Nondegenerate := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft ?_).mpr ?_
  · intro x y h
    rwa [QuadraticMap.associated_isSymm] at h
  · intro x hx
    have h := hx x
    rw [QuadraticMap.associated_eq_self_apply] at h
    exact eq_zero_of_sosQ_eq_zero h

/-- $\mathfrak n\mathbb Z^n \subseteq \mathbb Z$. -/
theorem normIdeal_intVec_le_one :
    OMeara.normIdeal (sosQ n).toQuadraticForm (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ 1 := by
  rw [OMeara.normIdeal, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, ha⟩ := isIntegral_of_unimodular (n := n) adj_D_unimodular x hx
  refine Submodule.mem_one.mpr ⟨a, ?_⟩
  rw [ha, omeara_Q_eq]
  rfl

/-- **There is a $\mathbb Z$-maximal lattice containing $\mathbb Z^n$** (O'Meara 82:18). -/
theorem exists_isGMaximal_ge_intVec :
    ∃ L : Lat ℚ n, IsGMaximal (sosQ n) L ∧ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ L.1 := by
  let _ : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  have h1fg : (1 : Submodule (𝓞 ℚ) ℚ).FG := one_submodule_fg_rat
  obtain ⟨L, hle, hL⟩ := QuadFormsKB.OMeara.Dedekind.exists_isMaximal_ge (sosQ n).toQuadraticForm
    (sosQ_associated_nondegenerate n) h1fg intVec_isLattice normIdeal_intVec_le_one
  exact ⟨⟨L, hL.1⟩, hL, hle⟩

theorem locAct_mono {v : HeightOneSpectrum (𝓞 ℚ)} (g : GL (Fin n) (v.adicCompletion ℚ))
    {A B : Submodule (v.adicCompletionIntegers ℚ) (Fin n → v.adicCompletion ℚ)} (h : A ≤ B) :
    locAct v g A ≤ locAct v g B :=
  Submodule.map_mono h

/-- The adelic action is monotone. -/
theorem latSMul_mono (g : OAf (sosQ n)) {L M : Lat ℚ n} (h : L.1 ≤ M.1) :
    (latSMul (sosQ n) g L).1 ≤ (latSMul (sosQ n) g M).1 := by
  rw [le_iff_forall_loc (latSMul (sosQ n) g M).2]
  intro v
  rw [loc_latSMul, loc_latSMul]
  exact locAct_mono _ (loc_mono v h)

/-- A unimodular lattice in the sense of §82G is unimodular in the sense $L^\# = L$ (for the sum of squares). -/
theorem isUnimodularZ_of_isUnimodular {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ) (hn : 0 < n)
    (hu : OMeara.IsUnimodular (sosQ n).toQuadraticForm L) : IsUnimodularZ (sosQ n) L := by
  have hreg : OMeara.IsRegular (sosQ n).toQuadraticForm L := by
    intro x hx hx0
    have h := hx0 x hx
    rw [OMeara.bil, QuadraticMap.associated_eq_self_apply] at h
    exact eq_zero_of_sosQ_eq_zero h
  unfold IsUnimodularZ
  rw [← dual_eq_omearaDual (sosQ n) hL]
  exact (OMeara.isUnimodular_iff_dual_eq _ hL.fg (lattice_ne_bot hL hn) hreg).mp hu

/-- **Every $\mathbb Z$-maximal lattice contains a unimodular lattice** (for the sum of $n \ge 1$ squares): if
$M = g L_0$ with $L_0 \supseteq \mathbb Z^n$ maximal and $g$ adelic, then $g\mathbb Z^n \subseteq M$ is in the genus of
$\mathbb Z^n$, hence unimodular (O'Meara 102A). -/
theorem exists_unimodular_le (hn : 0 < n) {M : Lat ℚ n} (hM : IsGMaximal (sosQ n) M) :
    ∃ K : Lat ℚ n, IsUnimodularZ (sosQ n) K.1 ∧ K.1 ≤ M.1 := by
  obtain ⟨L, hL, hZL⟩ := exists_isGMaximal_ge_intVec (n := n)
  have hLM : SameGenus (sosQ n) L.1 M.1 :=
    sameGenus_of_isMaximal (sosQ n) (sosQ_nondegenerate n) one_submodule_fg_rat one_submodule_ne_bot hL hM
  have hmem : M ∈ latGenus (sosQ n) L := hLM
  rw [← orbit_eq_genus] at hmem
  obtain ⟨g, hg⟩ := hmem
  let D : Lat ℚ n := ⟨intVec, intVec_isLattice⟩
  refine ⟨latSMul (sosQ n) g D, ?_, ?_⟩
  · have hDK : SameGenus (sosQ n) D.1 (latSMul (sosQ n) g D).1 :=
      (orbit_eq_genus (sosQ n) D).le ⟨g, rfl⟩
    have hDu : OMeara.IsUnimodular (sosQ n).toQuadraticForm D.1 :=
      isUnimodular_of_isUnimodularZ (sosQ n) D.2 hn adj_D_unimodular
    exact isUnimodularZ_of_isUnimodular (latSMul (sosQ n) g D).2 hn
      (isModular_of_sameGenus (sosQ n) hDu hDK)
  · have := latSMul_mono g (L := D) (M := L) hZL
    rw [← hg]
    exact this

/-- **`SumSqMaxContainsIntVec n` for $1 \le n \le 7$**: a $\mathbb Z$-maximal lattice contains a unimodular lattice
(`exists_unimodular_le`), which is isometric to $\mathbb Z^n$ by O'Meara 106:10 (`omeara106_10_uncond`). -/
theorem sumSqMaxContainsIntVec_of_le_seven {n : ℕ} (h1 : 1 ≤ n) (h7 : n ≤ 7) : SumSqMaxContainsIntVec n :=
  ⟨fun M hM => by
    obtain ⟨K, hK, hKM⟩ := exists_unimodular_le (by omega) hM
    obtain ⟨γ, hγ, he⟩ := omeara106_10_uncond h1 h7 (L := K) hK
    exact ⟨γ, hγ, he ▸ hKM⟩⟩

end Unimodular

end QuadFormsKB.Shimura2004
