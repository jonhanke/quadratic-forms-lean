/-
# O'Meara §105: the definiteness hypothesis of 105:1 is essential

**Layer:** as in `Literature/OMeara/Sec105.lean`: lattices are $\mathcal O_F$-submodules of $F^n$, here $F = \mathbb Q$,
$\mathcal O_F = \mathbb Z$ (`𝓞 ℚ`), the form is $Q = x_0^2 + x_1^2 - x_2^2$ (`QuadForm.diag ![1, 1, -1]`, indices
$0, 1, 2$ for O'Meara's $1, 2, 3$) and the lattice is $L = \mathbb Z^3$ (`intVec`).

**Proves** (O'Meara 1973, §105, p. 323, remark after 105:1, row 105.r6): the lattice $\mathbb Z^3$ on the indefinite
space $x_0^2 + x_1^2 - x_2^2$ has two indecomposable orthogonal splittings with different sets of components,
$\{\mathbb Ze_0, \mathbb Ze_1, \mathbb Ze_2\}$ and $\{\mathbb Zf_1, \mathbb Zf_2, \mathbb Zf_3\}$ with
$f_1 = (2, 1, 2)$, $f_2 = (1, 2, 2)$, $f_3 = (2, 2, 3)$ (`omeara105_r6`); so the uniqueness of 105:1
(`indecomposable_splitting_unique`) fails without definiteness. Also $Q(f_1) = Q(f_2) = 1$, $Q(f_3) = -1$, the $f_i$ are
pairwise orthogonal and $\det(f_1, f_2, f_3) = 1$ (`omeara105_r6_values`), and rank-one lattices are indecomposable
(`isIndecomposable_span_singleton`).
-/
import QuadFormsKB.Literature.OMeara.Sec105
import QuadFormsKB.Witt.Represents

open NumberField Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-! ### Rank-one lattices are indecomposable -/

/-- **A lattice $\mathfrak o v$ of rank one with $v \ne 0$ is indecomposable** (number field $F$; O'Meara 1973, §105,
p. 323, used in Example 105.r6): two non-zero sublattices of $\mathfrak o v$ always meet non-trivially. -/
theorem isIndecomposable_span_singleton {F : Type*} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)
    {v : Fin n → F} (hv : v ≠ 0) : IsIndecomposable Q (Submodule.span (𝓞 F) {v}) := by
  refine ⟨by simpa [Submodule.span_singleton_eq_bot] using hv, ?_⟩
  rintro ⟨K₁, K₂, h1, h2, -, hd, hK⟩
  obtain ⟨k₁, hk₁, hk₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h1
  obtain ⟨k₂, hk₂, hk₂0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h2
  have m₁ : k₁ ∈ Submodule.span (𝓞 F) {v} := hK ▸ Submodule.mem_sup_left hk₁
  have m₂ : k₂ ∈ Submodule.span (𝓞 F) {v} := hK ▸ Submodule.mem_sup_right hk₂
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp m₁
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp m₂
  have ha : a ≠ 0 := by rintro rfl; exact hk₁0 (zero_smul _ _)
  have hb : b ≠ 0 := by rintro rfl; exact hk₂0 (zero_smul _ _)
  have e1 : b • (a • v) ∈ K₁ := K₁.smul_mem b hk₁
  have e2 : b • (a • v) ∈ K₂ := by
    rw [smul_smul, mul_comm, ← smul_smul]; exact K₂.smul_mem a hk₂
  exact smul_ne_zero hb (smul_ne_zero ha hv) ((Submodule.disjoint_def.mp hd) _ e1 e2)

/-! ### A splitting from an orthogonal basis of $\mathbb Z^3$ -/

section Splitting

variable (Q : QuadForm ℚ 3)

/-- A linearly independent, pairwise orthogonal family of integral vectors which generates $\mathbb Z^3$ over
$\mathbb Z$ (each $e_j$ is an integral combination) gives an orthogonal splitting of $\mathbb Z^3$ into the lines. -/
theorem splitting_of_family (v : Fin 3 → Fin 3 → ℚ) (hli : LinearIndependent ℚ v)
    (hint : ∀ i, v i ∈ (intVec : Submodule (𝓞 ℚ) (Fin 3 → ℚ)))
    (horth : ∀ i j, i ≠ j → bil Q (v i) (v j) = 0)
    (hgen : ∃ c : Fin 3 → Fin 3 → ℤ, ∀ j, (Pi.single j (1 : ℚ) : Fin 3 → ℚ) = ∑ i, (c j i : ℚ) • v i) :
    IsOrthSplitting Q (intVec : Submodule (𝓞 ℚ) (Fin 3 → ℚ))
      (by classical exact Finset.univ.image fun i => Submodule.span (𝓞 ℚ) {v i}) := by
  classical
  have li' : LinearIndependent (𝓞 ℚ) v := hli.restrict_scalars' (𝓞 ℚ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hK
    simpa [Submodule.span_singleton_eq_bot] using li'.ne_zero i
  · intro K hK K' hK' hne x hx y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hK'
    have hij : i ≠ j := by rintro rfl; exact hne rfl
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [← algebraMap_smul ℚ a (v i), ← algebraMap_smul ℚ b (v j), bil_smul_left, bil_smul_right,
      horth i j hij]
    simp
  · have h1 : (Finset.univ : Finset (Fin 3)).SupIndep (fun i => Submodule.span (𝓞 ℚ) {v i}) :=
      iSupIndep_iff_supIndep_univ.mp li'.iSupIndep_span_singleton
    exact Finset.SupIndep.independent (f := (id : Submodule (𝓞 ℚ) (Fin 3 → ℚ) → _))
      (Finset.SupIndep.image (g := fun i => Submodule.span (𝓞 ℚ) {v i}) h1)
  · apply le_antisymm
    · refine Finset.sup_le fun K hK => ?_
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hK
      exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (hint i))
    · obtain ⟨c, hc⟩ := hgen
      have hmem : ∀ j, (Pi.single j (1 : ℚ) : Fin 3 → ℚ) ∈
          (Finset.univ.image fun i => Submodule.span (𝓞 ℚ) {v i}).sup id := by
        intro j
        rw [hc j]
        refine Submodule.sum_mem _ fun i _ => ?_
        have : ((c j i : ℚ)) • v i = ((c j i : 𝓞 ℚ)) • v i := by
          rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
        rw [this]
        have hle : Submodule.span (𝓞 ℚ) {v i} ≤
            (Finset.univ.image fun i => Submodule.span (𝓞 ℚ) {v i}).sup id :=
          Finset.le_sup (f := id) (Finset.mem_image_of_mem (fun i => Submodule.span (𝓞 ℚ) {v i})
            (Finset.mem_univ i))
        exact hle (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      intro x hx
      choose a ha using hx
      have hx' : x = ∑ j, a j • (Pi.single j (1 : ℚ) : Fin 3 → ℚ) := by
        ext k
        simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ha k]
      rw [hx']
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem j)

end Splitting

/-! ### The example -/

/-- The indefinite form $Q = x_0^2 + x_1^2 - x_2^2$ over $\mathbb Q$. -/
def Q105 : QuadForm ℚ 3 := QuadForm.diag ![1, 1, -1]

/-- The standard basis vectors $e_0, e_1, e_2$ of $\mathbb Z^3$, as a family of vectors in $\mathbb Q^3$. -/
def eVec : Fin 3 → Fin 3 → ℚ := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]

/-- The vectors $f_1 = (2, 1, 2)$, $f_2 = (1, 2, 2)$, $f_3 = (2, 2, 3)$ (indices $0, 1, 2$ here). -/
def fVec : Fin 3 → Fin 3 → ℚ := ![![2, 1, 2], ![1, 2, 2], ![2, 2, 3]]

/-- The components $\mathbb Ze_0, \mathbb Ze_1, \mathbb Ze_2$ of the first splitting. -/
def compE : Finset (Submodule (𝓞 ℚ) (Fin 3 → ℚ)) := by
  classical exact Finset.univ.image fun i => Submodule.span (𝓞 ℚ) {eVec i}

/-- The components $\mathbb Zf_1, \mathbb Zf_2, \mathbb Zf_3$ of the second splitting. -/
def compF : Finset (Submodule (𝓞 ℚ) (Fin 3 → ℚ)) := by
  classical exact Finset.univ.image fun i => Submodule.span (𝓞 ℚ) {fVec i}

private theorem int_mem_range (z : ℤ) : (z : ℚ) ∈ (algebraMap (𝓞 ℚ) ℚ).range := ⟨(z : 𝓞 ℚ), by simp⟩

private theorem eVec_int (i : Fin 3) : eVec i ∈ (intVec : Submodule (𝓞 ℚ) (Fin 3 → ℚ)) := by
  intro k
  fin_cases i <;> fin_cases k <;>
    first
    | exact_mod_cast int_mem_range 0
    | exact_mod_cast int_mem_range 1

private theorem fVec_int (i : Fin 3) : fVec i ∈ (intVec : Submodule (𝓞 ℚ) (Fin 3 → ℚ)) := by
  intro k
  fin_cases i <;> fin_cases k <;>
    first
    | exact_mod_cast int_mem_range 1
    | exact_mod_cast int_mem_range 2
    | exact_mod_cast int_mem_range 3

private theorem bil_Q105 (x y : Fin 3 → ℚ) :
    bil Q105 x y = 2 * (x 0 * y 0 + x 1 * y 1 - x 2 * y 2) := by
  simp [bil, Q105, QuadForm.hessian, QuadForm.diag, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

private theorem eVec_li : LinearIndependent ℚ eVec := by
  have := Matrix.linearIndependent_rows_of_det_ne_zero (R := ℚ)
    (A := !![(1 : ℚ), 0, 0; 0, 1, 0; 0, 0, 1]) (by simp [Matrix.det_fin_three])
  exact this

private theorem fVec_li : LinearIndependent ℚ fVec := by
  have := Matrix.linearIndependent_rows_of_det_ne_zero (R := ℚ)
    (A := !![(2 : ℚ), 1, 2; 1, 2, 2; 2, 2, 3]) (by simp [Matrix.det_fin_three]; norm_num)
  exact this

/-- **Row 105.r6 values:** $Q(f_1) = Q(f_2) = 1$, $Q(f_3) = -1$, the $f_i$ are pairwise orthogonal, and the
determinant of the matrix with rows $f_1, f_2, f_3$ is $1$ (O'Meara 1973, §105, p. 323). -/
@[kb "omeara1963" "§105, p. 323 (Q(f₁) = Q(f₂) = 1, Q(f₃) = −1, orthogonal, det 1)"]
theorem omeara105_r6_values :
    Q105.eval (fVec 0) = 1 ∧ Q105.eval (fVec 1) = 1 ∧ Q105.eval (fVec 2) = -1 ∧
      (∀ i j, i ≠ j → bil Q105 (fVec i) (fVec j) = 0) ∧
      (Matrix.of fVec).det = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Q105, QuadForm.eval, QuadForm.evalIn_diag, fVec, Fin.sum_univ_three]
  · simp [Q105, QuadForm.eval, QuadForm.evalIn_diag, fVec, Fin.sum_univ_three]
  · simp [Q105, QuadForm.eval, QuadForm.evalIn_diag, fVec, Fin.sum_univ_three]
    norm_num
  · intro i j hij
    rw [bil_Q105]
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | (simp [fVec]; norm_num)
  · have : Matrix.of fVec = !![(2 : ℚ), 1, 2; 1, 2, 2; 2, 2, 3] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [this]; simp [Matrix.det_fin_three]; norm_num

/-- The first splitting. -/
theorem splitting_E : IsOrthSplitting Q105 (intVec : Submodule (𝓞 ℚ) (Fin 3 → ℚ)) compE := by
  refine splitting_of_family Q105 eVec eVec_li eVec_int ?_
    ⟨![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ?_⟩
  · intro i j hij
    rw [bil_Q105]
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | (simp [eVec])
  · intro j
    fin_cases j <;> (ext k; fin_cases k <;> simp [eVec, Fin.sum_univ_three])

/-- The second splitting. -/
theorem splitting_F : IsOrthSplitting Q105 (intVec : Submodule (𝓞 ℚ) (Fin 3 → ℚ)) compF := by
  refine splitting_of_family Q105 fVec fVec_li fVec_int
    (omeara105_r6_values.2.2.2.1) ⟨![![2, 1, -2], ![1, 2, -2], ![-2, -2, 3]], ?_⟩
  intro j
  fin_cases j <;> (ext k; fin_cases k <;> simp [fVec, Fin.sum_univ_three] <;> norm_num)

/-- **Example 105.r6: the definiteness hypothesis in 105:1 is essential** (O'Meara 1973, §105, p. 323, remark after
105:1). For the indefinite form $Q = x_0^2 + x_1^2 - x_2^2$ over $\mathbb Q$ (O'Meara's $x_1^2 + x_2^2 - x_3^2$;
indices shifted by one) the lattice $\mathbb Z^3$ has two indecomposable orthogonal splittings,
$\mathbb Z^3 = \mathbb Ze_0 \perp \mathbb Ze_1 \perp \mathbb Ze_2$ and
$\mathbb Z^3 = \mathbb Zf_1 \perp \mathbb Zf_2 \perp \mathbb Zf_3$ with $f_1 = (2, 1, 2)$, $f_2 = (1, 2, 2)$,
$f_3 = (2, 2, 3)$, whose sets of components are different. In particular `indecomposable_splitting_unique` fails
for indefinite spaces. -/
@[kb "omeara1963" "§105, p. 323 (definiteness in 105:1 is essential)"]
theorem omeara105_r6 :
    IsOrthSplitting Q105 (intVec : Submodule (𝓞 ℚ) (Fin 3 → ℚ)) compE ∧
      (∀ K ∈ compE, IsIndecomposable Q105 K) ∧
      IsOrthSplitting Q105 (intVec : Submodule (𝓞 ℚ) (Fin 3 → ℚ)) compF ∧
      (∀ K ∈ compF, IsIndecomposable Q105 K) ∧ compE ≠ compF := by
  classical
  refine ⟨splitting_E, ?_, splitting_F, ?_, ?_⟩
  · intro K hK
    unfold compE at hK
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hK
    exact isIndecomposable_span_singleton Q105 (eVec_li.ne_zero i)
  · intro K hK
    unfold compF at hK
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hK
    exact isIndecomposable_span_singleton Q105 (fVec_li.ne_zero i)
  · intro h
    have hmem : Submodule.span (𝓞 ℚ) {eVec 0} ∈ compE := by
      show _ ∈ Finset.univ.image fun i => Submodule.span (𝓞 ℚ) {eVec i}
      exact Finset.mem_image_of_mem _ (Finset.mem_univ 0)
    rw [h] at hmem
    unfold compF at hmem
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    have : fVec i ∈ Submodule.span (𝓞 ℚ) {eVec 0} := by
      rw [← hi]; exact Submodule.mem_span_singleton_self _
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp this
    have h2 := congrFun ha 2
    fin_cases i <;> simp [fVec, eVec, Algebra.smul_def] at h2

end QuadFormsKB.Lattices
