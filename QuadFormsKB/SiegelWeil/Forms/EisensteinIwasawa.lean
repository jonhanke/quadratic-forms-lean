/-
# The Iwasawa decomposition of $\mathrm{Sp}_{2r}(F_v)$

**Layer:** linear algebra over a field (the expansion of a rectangular determinant), then local, non-archimedean: every finite
place $v$ of a number field $F$, dyadic places included.

**Results.**
* `det_mul_rect` (multilinear expansion): for $M \in M_{r\times\iota}(K)$, $N \in M_{\iota\times r}(K)$,
  $\det(MN) = \sum_{h : \{0..r-1\}\to\iota}\prod_jN_{h(j)j}\,\det M_h$ with $M_h$ the columns $h(0), \dots, h(r-1)$ of $M$ (`submatrix id h`).
* `iwasawaR` (**Iwasawa decomposition**): every $g \in \mathrm{Sp}_{2r}(F_v)$ is $g = pk$ with $p \in P(F_v)$ and $k \in \mathrm{Sp}_{2r}(F_v)$ with
  entries in $\mathcal O_v$.
* `htR_eq_maxMinor`: $\|g\|_v = |\det M_{h^*}|_v = \max_h|\det M_h|_v$ for the bottom block $M = (C\ D)$ of $g$: the height `htR` is the
  local height of the Plücker coordinates of the Lagrangian row space of $(C\ D)$.

*Proof (the max-minor normalization).* $M$ has a right inverse (from $g^{-1}$), so by `det_mul_rect` some $\det M_h \ne 0$; choose $h^*$
with $|\det M_{h^*}|_v$ maximal. By Cramer's rule the entries of $M'' = M_{h^*}^{-1}M$ are ratios $\det M_{h'}/\det M_{h^*}$ of minors, so
$M''$ is integral, with columns $h^*$ the identity; $M''J\,{}^tM'' = 0$ since $(C\ D)$ is Lagrangian. With the selection matrix $N$
($M''N = 1$), $T_0 = {}^tN\,J$ and $W = T_0J\,{}^tT_0$ (alternating), the rows $T = T_0 + UM''$, $U_{ij} = -W_{ij}$ for $i < j$ and $0$
otherwise, make $k = \binom{T}{M''}$ integral and symplectic, and the bottom block of $gk^{-1}$ is $(0\ \ M_{h^*})$, so $gk^{-1} \in P(F_v)$.

For $r = 1$ this is the degree-one `iwasawa` (`SiegelWeil/Convergence.lean`).

Sources: Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1 ($G(\mathbb A) = P(\mathbb A)K$) [unverified]. The proof
here (max-minor normalization and explicit symplectic completion) is written for this library.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.SiegelWeil.Forms.EisensteinHeight

open Matrix IsDedekindDomain NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

open WeilRep.Genus

section Algebra

variable {K : Type*} [Field K] {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The multilinear expansion of a rectangular determinant**:
$\det(MN) = \sum_h\prod_jN_{h(j)j}\det M_h$, $M_h$ = `M.submatrix id h`. -/
theorem det_mul_rect (M : Matrix (Fin r) ι K) (N : Matrix ι (Fin r) K) :
    (M * N).det = ∑ h : Fin r → ι, (∏ j, N (h j) j) * (M.submatrix id h).det := by
  rw [← det_transpose, transpose_mul]
  have hrow : (Nᵀ * Mᵀ) = fun j => ∑ c, N c j • (Mᵀ c) := by
    ext j k
    simp [mul_apply, Finset.sum_apply]
  have e : (Nᵀ * Mᵀ).det = (detRowAlternating : (Fin r → K) [⋀^Fin r]→ₗ[K] K) (fun j => ∑ c, N c j • Mᵀ c) := by
    rw [hrow]; rfl
  rw [e]
  change (detRowAlternating : (Fin r → K) [⋀^Fin r]→ₗ[K] K).toMultilinearMap (fun j => ∑ c, N c j • Mᵀ c) = _
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  congr 1
  rw [← det_transpose (M.submatrix id h)]
  rfl

/-- The selection matrix of the columns $h$: $N_{cj} = 1$ if $c = h(j)$, else $0$ (so $MN = M_h$). -/
def selN (h : Fin r → ι) : Matrix ι (Fin r) K := fun c j => if c = h j then 1 else 0

lemma mul_selN (M : Matrix (Fin r) ι K) (h : Fin r → ι) : M * selN (K := K) h = M.submatrix id h := by
  ext i j
  rw [mul_apply]
  simp [selN]

/-- **Cramer's rule for $M_h^{-1}M$**: its $(i, c)$ entry is $\det M_{h[i\mapsto c]}/\det M_h$. -/
lemma inv_submatrix_mul_apply (M : Matrix (Fin r) ι K) (h : Fin r → ι) (i : Fin r) (c : ι) :
    ((M.submatrix id h)⁻¹ * M) i c = (M.submatrix id (Function.update h i c)).det / (M.submatrix id h).det := by
  have e1 : ((M.submatrix id h)⁻¹ * M) i c = ((M.submatrix id h)⁻¹ *ᵥ fun k => M k c) i := by
    simp [mul_apply, mulVec, dotProduct]
  have e2 : (M.submatrix id h).updateCol i (fun k => M k c) = M.submatrix id (Function.update h i c) := by
    ext k j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [e1, inv_def, smul_mulVec, ← cramer_eq_adjugate_mulVec, Pi.smul_apply, cramer_apply, e2, smul_eq_mul,
    Ring.inverse_eq_inv', div_eq_inv_mul]

/-! ### Completing a Lagrangian block to a symplectic matrix -/

variable (P : Matrix (Fin r) (Fin r ⊕ Fin r) K) (N : Matrix (Fin r ⊕ Fin r) (Fin r) K)

/-- $T_0 = {}^tN\,J$. -/
def topT0 : Matrix (Fin r) (Fin r ⊕ Fin r) K := Nᵀ * Matrix.J (Fin r) K

/-- $W = T_0\,J\,{}^tT_0$ (alternating). -/
def wM : Matrix (Fin r) (Fin r) K := topT0 N * Matrix.J (Fin r) K * (topT0 N)ᵀ

/-- $U_{ij} = -W_{ij}$ for $i < j$, $0$ otherwise. -/
def uM : Matrix (Fin r) (Fin r) K := fun i j => if i < j then -wM N i j else 0

/-- The top rows $T = T_0 + UP$. -/
def topT : Matrix (Fin r) (Fin r ⊕ Fin r) K := topT0 N + uM N * P

/-- The completed matrix $k = \binom{T}{P}$. -/
def kMat : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := fromRows (topT P N) P

variable {P N}

lemma topT0_J_P (hPN : P * N = 1) : topT0 N * Matrix.J (Fin r) K * Pᵀ = -1 := by
  rw [topT0, Matrix.mul_assoc Nᵀ, J_squared, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, ← transpose_mul, hPN,
    transpose_one]

lemma P_J_topT0 (hPN : P * N = 1) : P * Matrix.J (Fin r) K * (topT0 N)ᵀ = 1 := by
  rw [topT0, transpose_mul, transpose_transpose, J_transpose]
  calc P * Matrix.J (Fin r) K * (-Matrix.J (Fin r) K * N)
      = -(P * (Matrix.J (Fin r) K * Matrix.J (Fin r) K) * N) := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = 1 := by rw [J_squared]; simp [hPN]

lemma wM_transpose : (wM N)ᵀ = -wM N := by
  rw [wM, transpose_mul, transpose_mul, transpose_transpose, J_transpose]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

lemma topT_J_P (hPN : P * N = 1) (hL : P * Matrix.J (Fin r) K * Pᵀ = 0) :
    topT P N * Matrix.J (Fin r) K * Pᵀ = -1 := by
  rw [topT, Matrix.add_mul, Matrix.add_mul, topT0_J_P hPN, Matrix.mul_assoc (uM N), Matrix.mul_assoc (uM N),
    hL, Matrix.mul_zero, add_zero]

lemma P_J_topT (hPN : P * N = 1) (hL : P * Matrix.J (Fin r) K * Pᵀ = 0) :
    P * Matrix.J (Fin r) K * (topT P N)ᵀ = 1 := by
  rw [topT, transpose_add, Matrix.mul_add, P_J_topT0 hPN, transpose_mul, ← Matrix.mul_assoc, hL, Matrix.zero_mul,
    add_zero]

lemma topT_J_topT (h2 : (2 : K) ≠ 0) (hPN : P * N = 1) (hL : P * Matrix.J (Fin r) K * Pᵀ = 0) :
    topT P N * Matrix.J (Fin r) K * (topT P N)ᵀ = 0 := by
  have e : topT P N * Matrix.J (Fin r) K * (topT P N)ᵀ = wM N - (uM N)ᵀ + uM N := by
    have h1 := topT0_J_P (K := K) hPN
    have h3 := P_J_topT0 (K := K) hPN
    have hL' : P * (Matrix.J (Fin r) K * Pᵀ) = 0 := by rw [← Matrix.mul_assoc, hL]
    have a1 : topT0 N * (Matrix.J (Fin r) K * (Pᵀ * (uM N)ᵀ)) = -(uM N)ᵀ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.neg_mul, Matrix.one_mul]
    have a2 : uM N * (P * (Matrix.J (Fin r) K * (topT0 N)ᵀ)) = uM N := by
      rw [← Matrix.mul_assoc P, h3, Matrix.mul_one]
    have a3 : uM N * (P * (Matrix.J (Fin r) K * (Pᵀ * (uM N)ᵀ))) = 0 := by
      rw [← Matrix.mul_assoc (Matrix.J (Fin r) K), ← Matrix.mul_assoc P, hL', Matrix.zero_mul, Matrix.mul_zero]
    rw [topT]
    simp only [transpose_add, transpose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    rw [a1, a2, a3, wM]
    simp only [Matrix.mul_assoc]
    abel
  rw [e]
  have hW := wM_transpose (N := N)
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, transpose_apply, uM, Matrix.zero_apply]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, not_lt.mpr h.le]
  · subst h
    have := congrFun (congrFun hW i) i
    simp only [transpose_apply, Matrix.neg_apply] at this
    have h0 : wM N i i = 0 := by
      have : (2 : K) * wM N i i = 0 := by linear_combination this
      exact (mul_eq_zero.mp this).resolve_left h2
    simp [h0]
  · have := congrFun (congrFun hW i) j
    simp only [transpose_apply, Matrix.neg_apply] at this
    simp only [not_lt.mpr h.le, h, ite_true, ite_false]
    linear_combination this

/-- **The completion is symplectic**: $k\,J\,{}^tk = J$ when $PN = 1$ and $PJ\,{}^tP = 0$. -/
theorem kMat_mem (h2 : (2 : K) ≠ 0) (hPN : P * N = 1) (hL : P * Matrix.J (Fin r) K * Pᵀ = 0) :
    kMat P N ∈ symplecticGroup (Fin r) K := by
  rw [SymplecticGroup.mem_iff, kMat, fromRows_mul, transpose_fromRows, fromRows_mul_fromCols, topT_J_topT h2 hPN hL,
    topT_J_P hPN hL, P_J_topT hPN hL, hL]
  rfl

end Algebra

/-! ### The Iwasawa decomposition at a finite place -/

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {r : ℕ}

local notation "Fv" => v.adicCompletion F

/-- A matrix with all entries in $\mathcal O_v$. -/
def IsIntM {ι κ : Type*} (A : Matrix ι κ (v.adicCompletion F)) : Prop := ∀ i j, ‖A i j‖ ≤ 1

variable {v}

lemma IsIntM.mul {ι κ μ : Type*} [Fintype κ] {A : Matrix ι κ Fv} {B : Matrix κ μ Fv} (hA : IsIntM v A)
    (hB : IsIntM v B) : IsIntM v (A * B) := fun i j => by
  rw [mul_apply]
  exact norm_sum_le_one v _ _ fun z _ => by rw [norm_mul]; exact mul_le_one₀ (hA i z) (norm_nonneg _) (hB z j)

lemma IsIntM.add {ι κ : Type*} {A B : Matrix ι κ Fv} (hA : IsIntM v A) (hB : IsIntM v B) : IsIntM v (A + B) :=
  fun i j => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA i j) (hB i j))

lemma IsIntM.neg {ι κ : Type*} {A : Matrix ι κ Fv} (hA : IsIntM v A) : IsIntM v (-A) :=
  fun i j => by rw [neg_apply, norm_neg]; exact hA i j

lemma IsIntM.transpose {ι κ : Type*} {A : Matrix ι κ Fv} (hA : IsIntM v A) : IsIntM v Aᵀ := fun i j => hA j i

lemma isIntM_J : IsIntM v (Matrix.J (Fin r) Fv) := isIntSp_J v

lemma isIntM_selN (h : Fin r → Fin r ⊕ Fin r) : IsIntM v (selN (K := Fv) h) := fun c j => by
  unfold selN; split_ifs <;> simp

variable (v)

/-- The minors of the bottom block are not all $0$: $(C\ D)$ has a right inverse (the last $r$ columns of $g^{-1}$). -/
lemma exists_minor_ne_zero (g : Sp r Fv) : ∃ h : Fin r → Fin r ⊕ Fin r, ((bottomRows v g).submatrix id h).det ≠ 0 := by
  set N : Matrix (Fin r ⊕ Fin r) (Fin r) Fv := fun x j => ((g⁻¹ : Sp r Fv) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) x (Sum.inr j)
  have hBM : bottomRows v g * N = 1 := by
    have : (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) * ((g⁻¹ : Sp r Fv) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) = 1 := by
      rw [← Submonoid.coe_mul, mul_inv_cancel]; rfl
    funext i j
    have h := congrFun (congrFun this (Sum.inr i)) (Sum.inr j)
    rw [mul_apply] at h
    rw [mul_apply]
    simpa [bottomRows, N, Matrix.one_apply] using h
  have h1 := det_mul_rect (bottomRows v g) N
  rw [hBM, det_one] at h1
  have hs : (∑ h : Fin r → Fin r ⊕ Fin r, (∏ j, N (h j) j) * ((bottomRows v g).submatrix id h).det) ≠ 0 := by
    rw [← h1]; exact one_ne_zero
  obtain ⟨h, -, hh⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  exact ⟨h, right_ne_zero_of_mul hh⟩

/-- A column choice $h^*$ of maximal $|\det M_{h}|_v$ for the bottom block $M$ of $g$. -/
def hMax (g : Sp r Fv) : Fin r → Fin r ⊕ Fin r :=
  (Finite.exists_max fun h : Fin r → Fin r ⊕ Fin r => ‖((bottomRows v g).submatrix id h).det‖).choose

lemma norm_minor_le_hMax (g : Sp r Fv) (h : Fin r → Fin r ⊕ Fin r) :
    ‖((bottomRows v g).submatrix id h).det‖ ≤ ‖((bottomRows v g).submatrix id (hMax v g)).det‖ :=
  (Finite.exists_max fun h : Fin r → Fin r ⊕ Fin r => ‖((bottomRows v g).submatrix id h).det‖).choose_spec h

lemma minor_hMax_ne_zero (g : Sp r Fv) : ((bottomRows v g).submatrix id (hMax v g)).det ≠ 0 := by
  obtain ⟨h, hh⟩ := exists_minor_ne_zero v g
  have := norm_minor_le_hMax v g h
  intro h0
  rw [h0, norm_zero] at this
  exact hh (norm_le_zero_iff.mp this)

/-- The block $M_{h^*}$ of maximal minor. -/
abbrev maxBlock (g : Sp r Fv) : Matrix (Fin r) (Fin r) Fv := (bottomRows v g).submatrix id (hMax v g)

/-- The normalized bottom block $M'' = M_{h^*}^{-1}M$. -/
def normB (g : Sp r Fv) : Matrix (Fin r) (Fin r ⊕ Fin r) Fv := (maxBlock v g)⁻¹ * bottomRows v g

lemma isIntM_normB (g : Sp r Fv) : IsIntM v (normB v g) := fun i c => by
  rw [normB, inv_submatrix_mul_apply, norm_div]
  exact div_le_one_of_le₀ (norm_minor_le_hMax v g _) (norm_nonneg _)

lemma isUnit_maxBlock (g : Sp r Fv) : IsUnit (maxBlock v g).det := (minor_hMax_ne_zero v g).isUnit

lemma normB_mul_selN (g : Sp r Fv) : normB v g * selN (K := Fv) (hMax v g) = 1 := by
  rw [normB, Matrix.mul_assoc, mul_selN, nonsing_inv_mul _ (isUnit_maxBlock v g)]

lemma maxBlock_mul_normB (g : Sp r Fv) : maxBlock v g * normB v g = bottomRows v g := by
  rw [normB, ← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_maxBlock v g), Matrix.one_mul]

/-- The bottom block of a symplectic matrix is Lagrangian: $M\,J\,{}^tM = 0$. -/
lemma bottomRows_lagrangian (g : Sp r Fv) : bottomRows v g * Matrix.J (Fin r) Fv * (bottomRows v g)ᵀ = 0 := by
  have h := (SymplecticGroup.mem_iff.mp g.2)
  ext i j
  have := congrFun (congrFun h (Sum.inr i)) (Sum.inr j)
  have e : (bottomRows v g * Matrix.J (Fin r) Fv * (bottomRows v g)ᵀ) i j =
      ((g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) * Matrix.J (Fin r) Fv *
        (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv)ᵀ) (Sum.inr i) (Sum.inr j) := rfl
  rw [e, this]
  simp [Matrix.J]

lemma normB_lagrangian (g : Sp r Fv) : normB v g * Matrix.J (Fin r) Fv * (normB v g)ᵀ = 0 := by
  rw [normB, transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (bottomRows v g),
    ← Matrix.mul_assoc _ (bottomRows v g)ᵀ, bottomRows_lagrangian, Matrix.zero_mul, Matrix.mul_zero]

/-- **The integral factor** $k = \binom{T}{M''} \in \mathrm{Sp}_{2r}(\mathcal O_v)$ of the Iwasawa decomposition of $g$. -/
def iwK (g : Sp r Fv) : Sp r Fv :=
  ⟨kMat (normB v g) (selN (hMax v g)), kMat_mem two_ne_zero (normB_mul_selN v g) (normB_lagrangian v g)⟩

lemma isIntSp_iwK (g : Sp r Fv) : IsIntSp v (iwK v g) := by
  have hP := isIntM_normB v g
  have hT0 : IsIntM v (topT0 (K := Fv) (selN (hMax v g))) := (isIntM_selN _).transpose.mul isIntM_J
  have hW : IsIntM v (wM (K := Fv) (selN (hMax v g))) := (hT0.mul isIntM_J).mul hT0.transpose
  have hU : IsIntM v (uM (K := Fv) (selN (hMax v g))) := fun i j => by
    unfold uM; split_ifs
    · rw [norm_neg]; exact hW i j
    · simp
  have hT : IsIntM v (topT (normB v g) (selN (hMax v g))) := hT0.add (hU.mul hP)
  intro x y
  rcases x with i | i
  · exact hT i y
  · exact hP i y

lemma bottomRows_iwK (g : Sp r Fv) : bottomRows v (iwK v g) = normB v g := rfl

/-- The parabolic factor $p = gk^{-1}$. -/
def iwP (g : Sp r Fv) : Sp r Fv := g * (iwK v g)⁻¹

lemma bottomRows_iwP (g : Sp r Fv) :
    bottomRows v (iwP v g) = maxBlock v g * bottomRows v (1 : Sp r Fv) := by
  rw [iwP, bottomRows_mul, ← maxBlock_mul_normB, ← bottomRows_iwK, Matrix.mul_assoc, ← bottomRows_mul,
    mul_inv_cancel]

lemma iwP_mem (g : Sp r Fv) : iwP v g ∈ siegelP r Fv := by
  show blockC _ = 0
  funext i j
  have := congrFun (congrFun (bottomRows_iwP v g) i) (Sum.inl j)
  show bottomRows v (iwP v g) i (Sum.inl j) = 0
  rw [this, mul_apply]
  exact Finset.sum_eq_zero fun l _ => by simp [bottomRows]

lemma blockD_iwP (g : Sp r Fv) : blockD (iwP v g) = maxBlock v g := by
  funext i j
  have := congrFun (congrFun (bottomRows_iwP v g) i) (Sum.inr j)
  simp only [bottomRows, mul_apply] at this
  simp only [blockD, toBlocks₂₂, of_apply]
  rw [this]
  simp [Matrix.one_apply]

lemma iwP_mul_iwK (g : Sp r Fv) : iwP v g * iwK v g = g := by rw [iwP, inv_mul_cancel_right]

/-- **The Iwasawa decomposition** $\mathrm{Sp}_{2r}(F_v) = P(F_v)\,\mathrm{Sp}_{2r}(\mathcal O_v)$, every finite place (dyadic included). -/
@[kb "kudla2008" "§1 ($G(\\mathbb A) = P(\\mathbb A)K$) [unverified]"]
theorem iwasawaR (g : Sp r Fv) : ∃ p ∈ siegelP r Fv, ∃ k : Sp r Fv, IsIntSp v k ∧ g = p * k :=
  ⟨iwP v g, iwP_mem v g, iwK v g, isIntSp_iwK v g, (iwP_mul_iwK v g).symm⟩

/-- **The height is the largest minor of the bottom block**: $\|g\|_v = \max_h|\det M_h|_v$, $M = (C\ D)$ (`hMax` attains the
maximum, `norm_minor_le_hMax`). -/
@[kb "kudla2008" "§1 (the function $|a(g)|$) [unverified]"]
theorem htR_eq_maxMinor (g : Sp r Fv) : htR v g = ‖(maxBlock v g).det‖ := by
  conv_lhs => rw [← iwP_mul_iwK v g]
  rw [htR_mul_of_mem_siegelP v (iwP_mem v g), htR_eq_one_of_int v (isIntSp_iwK v g), mul_one, blockD_iwP]

end Local

end QuadFormsKB.SiegelWeil.Forms
