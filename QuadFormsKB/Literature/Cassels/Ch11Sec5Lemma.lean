/-
# Cassels, Chapter 11, §5: Lemma 5.1

**Layer:** as in `Ch11Sec5.lean` ($\mathbb Z$-lattices `Lat ℚ n`, bases, `casselsI`, `latIndex`), with the form
$Q$ = `Q : QuadForm ℚ n`, $B = 2\phi$ (`qbil`), Gram matrices of local bases `locGram`.

**Proves** Cassels' Lemma 5.1 (pp. 223–224) (`exists_basis_casselsForm`): if at every $p \mid I(\Lambda, \Gamma)$ the
forms on $\Lambda_p$, $\Gamma_p$ are classically integral with unit determinant, there are a basis $b_j$ of $\Lambda$
and $s_j \in \mathbb Q$ with $s_jb_j$ a basis of $\Gamma$ and (i) $s_j > 0$, (ii) $s_j/s_{j+1} \in \mathbb Z$,
(iii) $s_js_{n-1-j} = 1$, (iv) $s_j \in \mathbb Z$ for $j < [(n+1)/2]$ (0-based; Cassels' (iii) is $s_js_{n+1-j} = 1$,
(iv) $j \le [(n+1)/2]$). *Proof* (Cassels): elementary divisors (Theorem 5.1) give (i), (ii); (iii) from the unit
determinants at the $p \mid I(\Lambda, \Gamma)$.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec5

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open Tamagawa.SiegelSpace

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ}

section Block
variable (v : HeightOneSpectrum (𝓞 ℚ))
local notation "Fv" => v.adicCompletion ℚ

theorem prod_lt_aux (S : Finset (Fin n)) (f : Fin n → WithZero (Multiplicative ℤ)) (c : WithZero (Multiplicative ℤ))
    (hc : c ≠ 0) (hle : ∀ i, f i ≤ c) (i0 : Fin n) (hi0 : i0 ∈ S) (hlt : f i0 < c) :
    ∏ i ∈ S, f i < c ^ S.card := by
  classical
  rw [← Finset.mul_prod_erase S f hi0, ← Finset.card_erase_add_one hi0, pow_succ']
  have h1 : ∏ i ∈ S.erase i0, f i ≤ c ^ (S.erase i0).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun i _ => hle i)
  have h2 : c ^ (S.erase i0).card ≠ 0 := pow_ne_zero _ hc
  calc f i0 * ∏ i ∈ S.erase i0, f i ≤ f i0 * c ^ (S.erase i0).card := by gcongr
    _ < c * c ^ (S.erase i0).card := by
      apply mul_lt_mul_of_pos_right hlt
      exact zero_lt_iff.2 h2

theorem det_lt_aux (G : Matrix (Fin n) (Fin n) Fv) (c : WithZero (Multiplicative ℤ)) (hc : c ≠ 0)
    (hle : ∀ i j, Valued.v (G i j) ≤ c) (I J : Finset (Fin n)) (hcard : n < I.card + J.card)
    (hlt : ∀ i ∈ I, ∀ j ∈ J, Valued.v (G i j) < c) : Valued.v G.det < c ^ n := by
  classical
  rw [Matrix.det_apply]
  have hcn : c ^ n ≠ 0 := pow_ne_zero _ hc
  refine Valuation.map_sum_lt _ hcn fun σ _ => ?_
  rw [Units.smul_def]
  have hs : Valued.v (((Equiv.Perm.sign σ : ℤˣ) : ℤ) • ∏ i, G (σ i) i) = Valued.v (∏ i, G (σ i) i) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hs, map_prod]
  have hex : ∃ j ∈ J, σ j ∈ I := by
    by_contra hno
    push Not at hno
    have hsub : J.image σ ⊆ Iᶜ := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_compl.2 (hno j hj)
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ σ.injective, Finset.card_compl, Fintype.card_fin] at this
    have := Finset.card_le_univ I
    simp only [Fintype.card_fin] at this
    omega
  obtain ⟨j, hj, hjI⟩ := hex
  have := prod_lt_aux Finset.univ (fun i => Valued.v (G (σ i) i)) c hc (fun i => hle _ _) j
    (Finset.mem_univ _) (hlt _ hjI _ hj)
  simpa using this

end Block

section LocalBasis

/-- The invertible matrix whose columns are the vectors $b_j$. -/
def basisGL {b : Fin n → Fin n → ℚ} (hb : LinearIndependent ℚ b) : GL (Fin n) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of fun i j => b j i) (by
    have : IsUnit (Matrix.of fun i j => b j i) := by
      rw [← Matrix.linearIndependent_col_iff_isUnit]
      exact hb
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero)

theorem basisGL_val {b : Fin n → Fin n → ℚ} (hb : LinearIndependent ℚ b) (i j : Fin n) :
    (basisGL hb).val i j = b j i := rfl

theorem basisGL_col {b : Fin n → Fin n → ℚ} (hb : LinearIndependent ℚ b) (j : Fin n) :
    (basisGL hb).val *ᵥ Pi.single j 1 = b j := by
  ext i
  simp [basisGL_val]

theorem lat_eq_latOf {Λ : Lat ℚ n} {b : Fin n → Fin n → ℚ} (h : Λ.1 = Submodule.span (𝓞 ℚ) (Set.range b)) :
    Λ.1 = latOf (basisGL (linIndep_of_lat h)) := by
  rw [← range_PhiLin, h, ← Submodule.map_top, ← (Pi.basisFun (𝓞 ℚ) (Fin n)).span_eq, Submodule.map_span,
    ← Set.range_comp]
  have hfam : (PhiLin (basisGL (linIndep_of_lat h))) ∘ (Pi.basisFun (𝓞 ℚ) (Fin n)) = b := by
    funext j
    rw [Function.comp_apply, PhiLin_apply]
    have : intCoe ((Pi.basisFun (𝓞 ℚ) (Fin n)) j) = Pi.single j 1 := by
      ext k
      by_cases hk : k = j <;> simp [intCoe, hk]
    rw [this, basisGL_col]
  rw [hfam]

variable (v : HeightOneSpectrum (𝓞 ℚ))
local notation "Fv" => v.adicCompletion ℚ

/-- The local image of the global basis matrix. -/
def basisGLv {b : Fin n → Fin n → ℚ} (hb : LinearIndependent ℚ b) : GL (Fin n) Fv :=
  GeneralLinearGroup.map (algebraMap ℚ Fv) (basisGL hb)

theorem basisGLv_col {b : Fin n → Fin n → ℚ} (hb : LinearIndependent ℚ b) (j : Fin n) :
    (basisGLv v hb).val *ᵥ Pi.single j 1 = locVec v (b j) := by
  ext i
  simp [basisGLv, basisGL_val]

theorem loc_eq_locAct_basis {Λ : Lat ℚ n} {b : Fin n → Fin n → ℚ}
    (h : Λ.1 = Submodule.span (𝓞 ℚ) (Set.range b)) :
    loc v Λ.1 = locAct v (basisGLv v (linIndep_of_lat h)) (std v) := by
  have e := congrArg (loc v) (lat_eq_latOf h)
  have := loc_glImage v (basisGL (linIndep_of_lat h)) intVec
  rw [loc_intVec] at this
  exact e.trans this

theorem locGram_basisGLv (Q : QuadForm ℚ n) {b : Fin n → Fin n → ℚ} (hb : LinearIndependent ℚ b) (k l : Fin n) :
    locGram Q v (basisGLv v hb) k l = qbil Q Fv (locVec v (b k)) (locVec v (b l)) := by
  rw [← locGram_apply_eq, basisGLv_col, basisGLv_col]

theorem det_locGram_basis (Q : QuadForm ℚ n) {Λ : Lat ℚ n} {b : Fin n → Fin n → ℚ}
    (h : Λ.1 = Submodule.span (𝓞 ℚ) (Set.range b)) (γ : GL (Fin n) Fv)
    (hγ : loc v Λ.1 = locAct v γ (std v)) :
    Valued.v (locGram Q v (basisGLv v (linIndep_of_lat h))).det = Valued.v (locGram Q v γ).det := by
  set β := basisGLv v (linIndep_of_lat h) with hβ
  have h1 : locAct v (γ⁻¹ * β) (std v) = std v := by
    rw [locAct_mul, ← loc_eq_locAct_basis v h, hγ, locAct_inv_locAct]
  obtain ⟨P, hP⟩ := exists_gl_o_of_locAct_eq v h1
  have hβγ : β = γ * GeneralLinearGroup.map (algebraMap _ Fv) P := by rw [hP]; simp
  have hdet : Valued.v ((GeneralLinearGroup.map (algebraMap _ Fv) P).val.det) = 1 := by
    have : (GeneralLinearGroup.map (algebraMap _ Fv) P).val.det = algebraMap _ Fv (P.val.det) := by
      rw [RingHom.map_det]; rfl
    rw [this]
    exact (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).1
      (Matrix.isUnits_det_units P)
  rw [hβγ, locGram_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, map_mul, map_mul, hdet]
  simp

theorem locVec_rat_smul (r : ℚ) (x : Fin n → ℚ) : locVec v (r • x) = algebraMap ℚ Fv r • locVec v x := by
  ext i; simp

theorem coord_le_aux {L : Lat ℚ n} {b : Fin n → Fin n → ℚ} (h : L.1 = Submodule.span (𝓞 ℚ) (Set.range b))
    (j : Fin n) (r : ℚ) (hr : locVec v (r • b j) ∈ loc v L.1) : Valued.v (algebraMap ℚ Fv r) ≤ 1 := by
  rw [loc_eq_locAct_basis v h, mem_locAct] at hr
  obtain ⟨y, hy, hyeq⟩ := hr
  have hinj := Matrix.mulVec_injective_of_det_ne_zero
    (Matrix.isUnits_det_units (basisGLv v (linIndep_of_lat h))).ne_zero
  have : y = algebraMap ℚ Fv r • Pi.single j 1 := by
    apply hinj
    show _ *ᵥ y = _ *ᵥ _
    rw [hyeq, Matrix.mulVec_smul, basisGLv_col, locVec_rat_smul]
  have h1 := mem_std_iff.1 hy j
  rwa [this, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h1

theorem unit_of_loc_eq (Λ Γ : Lat ℚ n) {b : Fin n → Fin n → ℚ} {s : Fin n → ℚ} (hg : Good Λ Γ b s)
    (hloc : loc v Λ.1 = loc v Γ.1) (j : Fin n) : Valued.v (algebraMap ℚ Fv (s j)) = 1 := by
  apply le_antisymm
  · refine coord_le_aux v hg.1 j (s j) ?_
    rw [hloc]
    exact locVec_mem_loc v (hg.2.1 ▸ Submodule.subset_span ⟨j, rfl⟩)
  · have hg2 := good_swap_aux hg
    have := coord_le_aux v hg2.1 j (s j)⁻¹ (by
      rw [← hloc]
      have : (s j)⁻¹ • (s j • b j) = b j := by rw [smul_smul, inv_mul_cancel₀ (hg.2.2 j).ne', one_smul]
      rw [this]
      exact locVec_mem_loc v (hg.1 ▸ Submodule.subset_span ⟨j, rfl⟩))
    rw [map_inv₀, map_inv₀] at this
    have hne : algebraMap ℚ Fv (s j) ≠ 0 := by
      simpa using (hg.2.2 j).ne'
    exact (inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hne))).1 this

/-- **The zero-block argument** (Cassels p. 224): with a basis $b$ of $\Lambda$ such that $t_jb_j \in \Gamma$, if the
forms on $\Lambda_p$, $\Gamma_p$ are classically integral and $\Lambda_p$ has unit determinant, then there are no
index sets $I, J$ with $|I| + |J| > n$ and $\lvert t_it_j\rvert_p > 1$ for all $i \in I$, $j \in J$. -/
theorem block_aux (Q : QuadForm ℚ n) {Λ Γ : Lat ℚ n} {b : Fin n → Fin n → ℚ}
    (h : Λ.1 = Submodule.span (𝓞 ℚ) (Set.range b)) (t : Fin n → ℚ) (ht : ∀ j, t j • b j ∈ Γ.1)
    (intΛ : ∀ x ∈ loc v Λ.1, ∀ y ∈ loc v Λ.1,
      Valued.v (qbil Q (v.adicCompletion ℚ) x y) ≤ Valued.v (2 : v.adicCompletion ℚ))
    (intΓ : ∀ x ∈ loc v Γ.1, ∀ y ∈ loc v Γ.1,
      Valued.v (qbil Q (v.adicCompletion ℚ) x y) ≤ Valued.v (2 : v.adicCompletion ℚ))
    (γ : GL (Fin n) (v.adicCompletion ℚ)) (hγ : loc v Λ.1 = locAct v γ (std v))
    (hdet : Valued.v (locGram Q v γ).det = Valued.v (2 : v.adicCompletion ℚ) ^ n)
    (I J : Finset (Fin n)) (hcard : n < I.card + J.card) :
    ¬ ∀ i ∈ I, ∀ j ∈ J, 1 < Valued.v (algebraMap ℚ Fv (t i * t j)) := by
  intro hall
  have hb := linIndep_of_lat h
  set c := Valued.v (2 : Fv) with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef]; exact (Valuation.ne_zero_iff _).2 two_ne_zero
  have hG : ∀ i j, locGram Q v (basisGLv v hb) i j = qbil Q Fv (locVec v (b i)) (locVec v (b j)) :=
    locGram_basisGLv v Q hb
  have hmemΛ : ∀ i, locVec v (b i) ∈ loc v Λ.1 := fun i =>
    locVec_mem_loc v (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  have hmemΓ : ∀ i, locVec v (t i • b i) ∈ loc v Γ.1 := fun i => locVec_mem_loc v (ht i)
  have hle : ∀ i j, Valued.v (locGram Q v (basisGLv v hb) i j) ≤ c := fun i j => by
    rw [hG]; exact intΛ _ (hmemΛ i) _ (hmemΛ j)
  have hlt : ∀ i ∈ I, ∀ j ∈ J, Valued.v (locGram Q v (basisGLv v hb) i j) < c := by
    intro i hi j hj
    have h1 := intΓ _ (hmemΓ i) _ (hmemΓ j)
    rw [locVec_rat_smul, locVec_rat_smul, qbil_smul_left, qbil_smul_right, ← mul_assoc,
      mul_comm _ (qbil _ _ _ _), map_mul, ← map_mul (algebraMap ℚ Fv), ← hG i j] at h1
    have hw := hall i hi j hj
    by_contra hcon
    push Not at hcon
    have h2 : c * 1 < c * Valued.v (algebraMap ℚ Fv (t i * t j)) :=
      mul_lt_mul_of_pos_left hw (zero_lt_iff.2 hc)
    have h3 : c * Valued.v (algebraMap ℚ Fv (t i * t j)) ≤
        Valued.v (locGram Q v (basisGLv v hb) i j) * Valued.v (algebraMap ℚ Fv (t i * t j)) := by
      gcongr
    rw [mul_one] at h2
    exact absurd (h2.trans_le (h3.trans h1)) (lt_irrefl _)
  have := det_lt_aux v (locGram Q v (basisGLv v hb)) c hc hle I J hcard hlt
  rw [det_locGram_basis v Q h γ hγ, hdet] at this
  exact lt_irrefl _ this

theorem val_dvdQ_le {x y : ℚ} (h : DvdQ x y) : Valued.v (algebraMap ℚ Fv y) ≤ Valued.v (algebraMap ℚ Fv x) := by
  obtain ⟨z, rfl⟩ := h
  have hz : Valued.v (algebraMap ℚ Fv (z : ℚ)) ≤ 1 := by
    rw [map_intCast]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (intCast_mem (v.adicCompletionIntegers ℚ) z)
  rw [map_mul, map_mul]
  calc Valued.v (algebraMap ℚ Fv (z : ℚ)) * Valued.v (algebraMap ℚ Fv x)
      ≤ 1 * Valued.v (algebraMap ℚ Fv x) := by gcongr
    _ = _ := one_mul _

/-- **The local pairing:** at a prime $p \mid I(\Lambda,\Gamma)$, $\lvert s_us_w\rvert_p = 1$ whenever
$u + w = n - 1$ (0-based). -/
theorem unit_prod_aux (Q : QuadForm ℚ n) {Λ Γ : Lat ℚ n} {b : Fin n → Fin n → ℚ} {s : Fin n → ℚ}
    (hg : Good Λ Γ b s) (hch : ∀ i j : Fin n, i.1 < j.1 → DvdQ (s j) (s i))
    (intΛ : ∀ x ∈ loc v Λ.1, ∀ y ∈ loc v Λ.1,
      Valued.v (qbil Q (v.adicCompletion ℚ) x y) ≤ Valued.v (2 : v.adicCompletion ℚ))
    (intΓ : ∀ x ∈ loc v Γ.1, ∀ y ∈ loc v Γ.1,
      Valued.v (qbil Q (v.adicCompletion ℚ) x y) ≤ Valued.v (2 : v.adicCompletion ℚ))
    (hΛd : ∃ γ : GL (Fin n) (v.adicCompletion ℚ), loc v Λ.1 = locAct v γ (std v) ∧
        Valued.v (locGram Q v γ).det = Valued.v (2 : v.adicCompletion ℚ) ^ n)
    (hΓd : ∃ δ : GL (Fin n) (v.adicCompletion ℚ), loc v Γ.1 = locAct v δ (std v) ∧
        Valued.v (locGram Q v δ).det = Valued.v (2 : v.adicCompletion ℚ) ^ n)
    (u w : Fin n) (huw : u.1 + w.1 + 1 = n) :
    Valued.v (algebraMap ℚ Fv (s u * s w)) = 1 := by
  have hle : ∀ i j : Fin n, i.1 ≤ j.1 → Valued.v (algebraMap ℚ Fv (s i)) ≤ Valued.v (algebraMap ℚ Fv (s j)) := by
    intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact val_dvdQ_le v (hch i j h)
    · rw [Fin.ext h]
  have hne : ∀ i, algebraMap ℚ Fv (s i) ≠ 0 := fun i => by simpa using (hg.2.2 i).ne'
  apply le_antisymm
  · by_contra hgt
    push Not at hgt
    obtain ⟨γ, hγ, hdet⟩ := hΛd
    refine block_aux v Q hg.1 s (fun j => hg.2.1 ▸ Submodule.subset_span ⟨j, rfl⟩) intΛ intΓ γ hγ hdet
      (Finset.Ici u) (Finset.Ici w) (by simp [Fin.card_Ici]; omega) ?_
    intro i hi j hj
    rw [Finset.mem_Ici] at hi hj
    refine lt_of_lt_of_le hgt ?_
    simp only [map_mul] at hgt ⊢
    exact mul_le_mul' (hle u i hi) (hle w j hj)
  · by_contra hlt
    push Not at hlt
    obtain ⟨δ, hδ, hdet⟩ := hΓd
    have hg2 := good_swap_aux hg
    refine block_aux v Q hg2.1 (fun j => (s j)⁻¹)
      (fun j => by
        have : (s j)⁻¹ • (s j • b j) = b j := by rw [smul_smul, inv_mul_cancel₀ (hg.2.2 j).ne', one_smul]
        rw [this]; exact hg.1 ▸ Submodule.subset_span ⟨j, rfl⟩) intΓ intΛ δ hδ hdet
      (Finset.Iic u) (Finset.Iic w) (by simp [Fin.card_Iic]; omega) ?_
    intro i hi j hj
    rw [Finset.mem_Iic] at hi hj
    have h1 : Valued.v (algebraMap ℚ Fv (s i * s j)) < 1 := by
      simp only [map_mul] at hlt ⊢
      exact lt_of_le_of_lt (mul_le_mul' (hle i u hi) (hle j w hj)) hlt
    have h2 : algebraMap ℚ Fv ((s i)⁻¹ * (s j)⁻¹) = (algebraMap ℚ Fv (s i * s j))⁻¹ := by
      simp [mul_comm]
    rw [h2, map_inv₀]
    have hne2 : algebraMap ℚ Fv (s i * s j) ≠ 0 := by
      rw [map_mul]; exact mul_ne_zero (hne i) (hne j)
    exact (one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hne2))).2 h1

end LocalBasis

theorem int_of_val_aux (x : ℚ) (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v (algebraMap ℚ (v.adicCompletion ℚ) x) ≤ 1) :
    ∃ z : ℤ, x = z := by
  have := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ x (fun v => by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact h v)
  obtain ⟨a, ha⟩ := this
  obtain ⟨z, rfl⟩ := exists_int_eq_aux a
  exact ⟨z, by rw [← ha]; simp⟩

theorem eq_one_of_val_aux (x : ℚ) (hx : 0 < x)
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v (algebraMap ℚ (v.adicCompletion ℚ) x) = 1) : x = 1 := by
  obtain ⟨z, hz⟩ := int_of_val_aux x (fun v => (h v).le)
  obtain ⟨z', hz'⟩ := int_of_val_aux x⁻¹ (fun v => by rw [map_inv₀, map_inv₀, h v]; simp)
  have hzz : z * z' = 1 := by
    have : (z : ℚ) * z' = 1 := by rw [← hz, ← hz']; exact mul_inv_cancel₀ hx.ne'
    exact_mod_cast this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hzz with h1 | h1
  · rw [hz, h1]; simp
  · rw [hz, h1] at hx; simp at hx; linarith

/-- **Cassels, Lemma 5.1** (Ch. 11, pp. 223–224): *let $\Lambda, \Gamma$ be $\mathbb Z$-lattices of the same
determinant in the $\mathbb Q$-quadratic space $V, \phi$ of dimension $n$. For every $p \mid I(\Lambda, \Gamma)$
suppose that the quadratic forms induced by $\phi$ on $\Lambda_p$ and $\Gamma_p$ are classically integral and that
their determinants are $p$-adic units. Then there are a basis $b_1, \dots, b_n$ of $\Lambda$ and $s_1, \dots, s_n \in
\mathbb Q$ such that $s_1b_1, \dots, s_nb_n$ is a basis of $\Gamma$ and (i) $s_j > 0$; (ii) $s_j/s_{j+1} \in \mathbb Z$;
(iii) $s_js_{n+1-j} = 1$; (iv) $s_j \in \mathbb Z$ ($1 \le j \le [(n+1)/2]$).* 0-based. "Classically integral":
$\lvert B(x, y)\rvert_p \le \lvert 2\rvert_p$ on the local lattice ($B = 2\phi$); "determinant a unit": the Gram matrix
$G = (B(b_k, b_l))$ of a basis of $\Lambda_p$ has $\lvert\det G\rvert_p = \lvert 2\rvert_p^n$ (so
$\det(\phi(b_k, b_l)) = 2^{-n}\det G$ is a unit), and the same for $\Gamma_p$. -/
@[kb "cassels1978" "Ch. 11, Lemma 5.1, pp. 223–224 (0-based)"]
theorem exists_basis_casselsForm (Q : QuadForm ℚ n) {Λ Γ : Lat ℚ n} (h : latIndex Λ = latIndex Γ)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 ℚ), Rat.HeightOneSpectrum.natGenerator v ∣ casselsI Λ Γ →
      (∀ x ∈ loc v Λ.1, ∀ y ∈ loc v Λ.1,
        Valued.v (qbil Q (v.adicCompletion ℚ) x y) ≤ Valued.v (2 : v.adicCompletion ℚ)) ∧
      (∀ x ∈ loc v Γ.1, ∀ y ∈ loc v Γ.1,
        Valued.v (qbil Q (v.adicCompletion ℚ) x y) ≤ Valued.v (2 : v.adicCompletion ℚ)) ∧
      (∃ γ : GL (Fin n) (v.adicCompletion ℚ), loc v Λ.1 = locAct v γ (std v) ∧
        Valued.v (locGram Q v γ).det = Valued.v (2 : v.adicCompletion ℚ) ^ n) ∧
      (∃ δ : GL (Fin n) (v.adicCompletion ℚ), loc v Γ.1 = locAct v δ (std v) ∧
        Valued.v (locGram Q v δ).det = Valued.v (2 : v.adicCompletion ℚ) ^ n)) :
    ∃ (b : Fin n → Fin n → ℚ) (s : Fin n → ℚ), LinearIndependent ℚ b ∧
      Λ.1 = Submodule.span (𝓞 ℚ) (Set.range b) ∧
      Γ.1 = Submodule.span (𝓞 ℚ) (Set.range fun j => s j • b j) ∧
      (∀ j, 0 < s j) ∧
      (∀ j : Fin n, ∀ hj : j.1 + 1 < n, ∃ z : ℤ, s j / s ⟨j.1 + 1, hj⟩ = z) ∧
      (∀ j : Fin n, s j * s (Fin.rev j) = 1) ∧
      (∀ j : Fin n, j.1 < (n + 1) / 2 → ∃ z : ℤ, s j = z) := by
  have hne0 : casselsI Λ Γ ≠ 0 :=
    relIndex_ne_zero (L := (⟨Λ.1 ⊓ Γ.1, isLattice_inf_aux Λ.2 Γ.2⟩ : Lat ℚ n)) (M := Λ) inf_le_left
  obtain ⟨b0, s0, hg0⟩ := exists_good (Nat.pos_of_ne_zero hne0)
    (smul_mem_of_casselsI_aux (L := Λ) (M := Γ) (p := casselsI Λ Γ) rfl)
  obtain ⟨b, s, hg, hch⟩ := exists_good_chain hg0
  have hcomm : casselsI Γ Λ = casselsI Λ Γ := (casselsI_comm h).symm
  have hne : ∀ i, s i ≠ 0 := fun i => (hg.2.2 i).ne'
  -- the local pairing statement at every prime
  have hunit : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (u w : Fin n), u.1 + w.1 + 1 = n →
      Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (s u * s w)) = 1 := by
    intro v u w huw
    by_cases hd : Rat.HeightOneSpectrum.natGenerator v ∣ casselsI Λ Γ
    · obtain ⟨i1, i2, i3, i4⟩ := hloc v hd
      exact unit_prod_aux v Q hg hch i1 i2 i3 i4 u w huw
    · have hl := (loc_eq_iff_not_dvd_casselsI h v).2 hd
      rw [map_mul, map_mul, unit_of_loc_eq v Λ Γ hg hl u, unit_of_loc_eq v Λ Γ hg hl w, one_mul]
  have hrev : ∀ j : Fin n, j.1 + (Fin.rev j).1 + 1 = n := fun j => by
    rw [Fin.val_rev]; have := j.2; omega
  have h3 : ∀ j : Fin n, s j * s (Fin.rev j) = 1 :=
    fun j => eq_one_of_val_aux _ (mul_pos (hg.2.2 j) (hg.2.2 _)) (fun v => hunit v j _ (hrev j))
  refine ⟨b, s, linIndep_of_lat hg.1, hg.1, hg.2.1, hg.2.2, ?_, h3, ?_⟩
  · intro j hj
    obtain ⟨z, hz⟩ := hch j ⟨j.1 + 1, hj⟩ (by simp)
    exact ⟨z, by rw [hz]; field_simp [hne ⟨j.1 + 1, hj⟩]⟩
  · intro j hj
    have hjr : j.1 ≤ (Fin.rev j).1 := by rw [Fin.val_rev]; omega
    apply int_of_val_aux
    intro v
    by_contra hgt
    push Not at hgt
    have hle : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (s j)) ≤
        Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (s (Fin.rev j))) := by
      rcases hjr.lt_or_eq with hlt | heq
      · exact val_dvdQ_le v (hch j _ hlt)
      · exact (congrArg (fun k => Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (s k))) (Fin.ext heq)).le
    have hu := hunit v j _ (hrev j)
    rw [map_mul, map_mul] at hu
    have hy := hgt.trans_le hle
    have : 1 < Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (s j)) *
        Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (s (Fin.rev j))) := by
      calc (1 : WithZero (Multiplicative ℤ)) < 1 * Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (s (Fin.rev j))) := by
            rw [one_mul]; exact hy
        _ < _ := mul_lt_mul_of_pos_right hgt (lt_trans zero_lt_one hy)
    rw [hu] at this
    exact lt_irrefl _ this

end QuadFormsKB.Lattices
