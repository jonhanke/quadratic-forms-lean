/-
# O'Meara §106F, toward 106.r38: the classes in the genus of $I_n$, $9 \le n \le 13$

**Layer:** integral forms (`Siegel.SameGenus`, `Siegel.IntEquiv`, `Siegel.mass`) and lattices on $I_n$, as in
`Sec106Rank13Lat.lean`. $I_n$ = `sumSq n`, $E_8 \perp I_k$ = `ofMatrixZ (sumI (CartanMatrix.E 8) k)`,
$E_{12} \perp I_k$ = `ofMatrixZ (sumI d12Gram k)`. Indices are 0-based.

**Proves** (all unconditional)
* `intEquiv_of_sameGenus_sumSq_nine`: every form in the genus of $I_9$ is equivalent to $I_9$ or to $E_8 \perp I_1$
  (O'Meara 106:13 for $n = 9$, through the lattice bridge).
* `card_aut_e8`: $|\mathrm{Aut}(E_8)| = 696729600$, from the mass of the genus of $I_9$ and the two classes in it.
-/
import QuadFormsKB.Literature.OMeara.Sec106Rank13Lat
import QuadFormsKB.HilbertModular.GenusTheta

open Matrix NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open Siegel LocalDensity ConwaySloane.Mass QuadFormsKB.Tamagawa.Frames

variable {n : ℕ}

/-- The Gram matrix of a basis of $E_m$ is positive definite. -/
theorem EBasisData.posDefGram_G {m : ℕ} (D : EBasisData m) : PosDefGram D.G := by
  refine ⟨D.G_symm, fun x hx => ?_⟩
  rw [gramQ, ← D.gl_norm]
  have hne : D.B *ᵥ x ≠ 0 := by
    intro h
    apply hx
    have := congrArg (fun v => D.Binv *ᵥ v) h
    simpa [mulVec_mulVec, D.Binv_mul_B] using this
  exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
    (Ne.symm fun h => hne (dotProduct_self_eq_zero.mp h))

/-- **The genus of $I_9$** (O'Meara 106:13 for $n = 9$, transported to integral forms): every form in the genus of $I_9$
is integrally equivalent to $I_9$ or to $E_8 \perp I_1$. -/
theorem intEquiv_of_sameGenus_sumSq_nine {Q' : QuadForm ℤ 9} (h : Siegel.SameGenus (sumSq 9) Q') :
    IntEquiv (sumSq 9) Q' ∨ IntEquiv (ofMatrixZ (sumI e8Data.G 1)) Q' := by
  have hd0 : (sumSq 9).hessian.det ≠ 0 := by
    rw [hessian_sumSq, Matrix.det_smul, Matrix.det_one]
    simp
  obtain ⟨g, hg⟩ := isometricGL_rat_of_sameGenus (sumSq 9) Q' h.hessian_det_eq hd0 h
  have hg' : ∀ x : Fin 9 → ℚ, (sumSq 9).evalIn ℚ (g.val *ᵥ x) = Q'.evalIn ℚ x := by
    intro x
    have := hg x
    rwa [map_eval_eq_evalIn_int, map_eval_eq_evalIn_int] at this
  have hU := isUnimodularZ_glImage_of_sameGenus h g hg'
  let L : Lat ℚ 9 := ⟨glImage g intVec, glImage_isLattice g intVec_isLattice⟩
  rcases unimodular_rank9 L hU with ⟨σ, hσ, hσL⟩ | ⟨σ, hσ, hσL⟩
  · exact Or.inl (intEquiv_of_glImage_eq g σ hσ hσL hg')
  · right
    refine intEquiv_of_isIsometric_glImage (e8Data.blk 1) g σ (e8Data.gram_blk 1) hg' hσ ?_
    rw [e8Data.glImage_blk (by norm_num) (by norm_num) 1]
    exact hσL

/-- **The Gram matrix of a basis of a unimodular lattice is integral.** -/
theorem exists_int_gram (γ : GL (Fin n) ℚ) (hU : IsUnimodularZ (sumSqForm n) (glImage γ intVec)) :
    ∃ G : Matrix (Fin n) (Fin n) ℤ, G.map (Int.castRingHom ℚ) = γ.valᵀ * γ.val := by
  have hcol : ∀ i, (γ.val *ᵥ Pi.single i 1) ∈ glImage γ intVec := fun i =>
    mulVec_mem_glImage (mem_intVec_iff_int.mpr fun j => ⟨if j = i then 1 else 0, by
      by_cases h : j = i <;> simp [Pi.single_apply, h]⟩)
  have hent : ∀ i j, ∃ z : ℤ, (γ.valᵀ * γ.val) i j = z := by
    intro i j
    have hi := hcol i
    rw [← hU] at hi
    obtain ⟨z, hz⟩ := hi _ (hcol j)
    refine ⟨z, ?_⟩
    rw [DefiniteForms.bil_sumSq] at hz
    have e : (γ.valᵀ * γ.val) i j = (γ.val *ᵥ Pi.single i 1) ⬝ᵥ (γ.val *ᵥ Pi.single j 1) := by
      simp [Matrix.mul_apply, dotProduct, Matrix.mulVec, Pi.single_apply]
    rw [e]; linarith
  choose G hG using hent
  exact ⟨Matrix.of G, by ext i j; simp [hG]⟩

/-- **An even positive definite Gram matrix of determinant $1$ has $8 \mid n$** (O'Meara 106:1, via
`Siegel.eight_dvd_of_posDef_det_one` applied to the half form). Hence for $8 \nmid n$ the type is $1$. -/
theorem gramType_eq_one_of_not_dvd (hn : ¬ 8 ∣ n) {G : Matrix (Fin n) (Fin n) ℤ} (hG : PosDefGram G)
    (hdet : G.det = 1) : gramType G = 1 := by
  rcases gramType_eq_one_or_two G with h | h
  · exact h
  exfalso
  have he : EvenGram G := by
    by_contra hne
    simp [gramType, hne] at h
  let Qh : QuadForm ℤ n := ⟨Matrix.of fun i j => if i < j then G i j else if i = j then G i i / 2 else 0, by
    intro i j hij
    simp only [id] at hij
    simp [Matrix.of_apply, not_lt.mpr hij.le, (ne_of_lt hij).symm]⟩
  have hH : Qh.hessian = G := by
    ext i j
    simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply, Qh, Matrix.of_apply]
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [hij, not_lt.mpr hij.le, ne_of_lt hij, (ne_of_lt hij).symm]
    · obtain ⟨c, hc⟩ := he i
      simp; omega
    · have hs : G j i = G i j := by have := congrFun (congrFun hG.1 i) j; simpa using this
      simp [hij, not_lt.mpr hij.le, ne_of_gt hij, (ne_of_gt hij).symm, hs]
  have hpos : IntQF.PosDef Qh := by
    intro x hx
    have h2 := Siegel.Kneser.two_mul_evalIn (K := ℚ) Qh (fun i => (x i : ℚ))
    rw [hH] at h2
    have hp := hG.pos_int hx
    have e : ((x ⬝ᵥ (G *ᵥ x) : ℤ) : ℚ) = (fun i => (x i : ℚ)) ⬝ᵥ (G.map (algebraMap ℤ ℚ) *ᵥ fun i => (x i : ℚ)) := by
      simp [dotProduct, Matrix.mulVec, Matrix.map_apply]
    have : (0 : ℚ) < 2 * Qh.evalIn ℚ (fun i => (x i : ℚ)) := by
      rw [h2, ← e]; exact_mod_cast hp
    have h3 : Qh.evalIn ℚ (fun i => (x i : ℚ)) = (Qh.eval x : ℚ) := evalIn_intCast Qh x
    rw [h3] at this
    have : (0 : ℚ) < (Qh.eval x : ℚ) := by linarith
    exact_mod_cast this
  exact hn (eight_dvd_of_posDef_det_one hpos (by rw [hH, hdet]))

/-- **A unimodular lattice on $I_n$, $8 \nmid n$, has a basis whose Gram form is in the genus of $I_n$.** -/
theorem exists_basis_sameGenus (hn1 : 1 ≤ n) (hn : ¬ 8 ∣ n) (L : Lat ℚ n)
    (hL : IsUnimodularZ (sumSqForm n) L.1) :
    ∃ (γ : GL (Fin n) ℚ) (G : Matrix (Fin n) (Fin n) ℤ), L.1 = glImage γ intVec ∧
      (∀ x : Fin n → ℚ, (sumSq n).evalIn ℚ (γ.val *ᵥ x) = (ofMatrixZ G).evalIn ℚ x) ∧
      Siegel.SameGenus (sumSq n) (ofMatrixZ G) := by
  obtain ⟨γ, hγ⟩ := HilbertModular.exists_latOf_of_isPrincipalIdealRing L
  have hγ' : L.1 = glImage γ intVec := hγ
  have hU : IsUnimodularZ (sumSqForm n) (glImage γ intVec) := hγ' ▸ hL
  obtain ⟨G, hG⟩ := exists_int_gram γ hU
  have hsymm : Gᵀ = G := by
    apply Matrix.map_injective (f := (Int.castRingHom ℚ : ℤ → ℚ)) Int.cast_injective
    show Gᵀ.map (Int.castRingHom ℚ) = G.map (Int.castRingHom ℚ)
    rw [Matrix.transpose_map, hG, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hgram : ∀ x : Fin n → ℚ, (sumSq n).evalIn ℚ (γ.val *ᵥ x) = (ofMatrixZ G).evalIn ℚ x := by
    intro x
    rw [evalIn_sumSq, Cassels.Thm71Coords.evalIn_ofMatrixZ _ hsymm]
    have e : x ⬝ᵥ (G.map (Int.cast : ℤ → ℚ) *ᵥ x) = (γ.val *ᵥ x) ⬝ᵥ (γ.val *ᵥ x) := by
      have : G.map (Int.cast : ℤ → ℚ) = γ.valᵀ * γ.val := hG
      rw [this, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm,
        Matrix.transpose_transpose]
    rw [e]; simp [dotProduct, sq]
  have hpd : PosDefGram G := by
    refine ⟨hsymm, fun x hx => ?_⟩
    have e : x ⬝ᵥ (gramQ G *ᵥ x) = (γ.val *ᵥ x) ⬝ᵥ (γ.val *ᵥ x) := by
      rw [gramQ, hG, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm,
        Matrix.transpose_transpose]
    rw [e]
    have hne : γ.val *ᵥ x ≠ 0 := by
      intro h; apply hx
      have := congrArg (fun v => (γ⁻¹).val *ᵥ v) h
      simpa [mulVec_mulVec, ← Units.val_mul] using this
    exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
      (Ne.symm fun h => hne (dotProduct_self_eq_zero.mp h))
  have hdet := det_gram_eq_one_of_unimodular γ G hG hU
  exact ⟨γ, G, hγ', hgram, sameGenus_sumSq_of_det_one hn1 hpd hdet (gramType_eq_one_of_not_dvd hn hpd hdet)⟩

/-- **The mass of a genus covered by a list of pairwise inequivalent forms** is the sum of their weights. -/
theorem mass_eq_sum_of_cover {ι : Type*} [Fintype ι] {Q : IntQF n} (hQ : Q.PosDef) (R : ι → QuadForm ℤ n)
    (hgen : ∀ i, Siegel.SameGenus Q (R i)) (hdist : ∀ i j, IntEquiv (R i) (R j) → i = j)
    (hcov : ∀ Q', Siegel.SameGenus Q Q' → ∃ i, IntEquiv (R i) Q') :
    Siegel.mass Q = ∑ i, ((Nat.card (Aut (R i)) : ℝ))⁻¹ := by
  classical
  have hF := genusFinite hQ
  rw [Siegel.mass_eq_sum hF, ← Kneser.sum_classFinset hdist]
  congr 1
  ext c
  rw [Set.Finite.mem_toFinset, Kneser.mem_classFinset]
  constructor
  · intro hc
    induction c using Quotient.inductionOn with
    | h Q' =>
      obtain ⟨i, hi⟩ := hcov Q' (classOf_mem_genusClasses_iff.mp hc)
      exact ⟨i, classOf_eq_classOf_iff.mpr hi⟩
  · rintro ⟨i, rfl⟩
    exact classOf_mem_genusClasses_iff.mpr (hgen i)

end QuadFormsKB.Lattices
