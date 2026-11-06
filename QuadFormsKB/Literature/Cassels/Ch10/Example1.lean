/-
# Cassels, Chapter 10, Example 1: spinor norms of a ternary lattice with $p \Vert d$

**Layer** (as in `Ch11Sec3Local.lean`): $V_\mathfrak p = F_\mathfrak p^n$ at a finite prime $\mathfrak p \nmid 2$ of a number
field $F$ (Cassels: $\mathbb Q_p$, $p \ne 2$), $Q$ = `Q : QuadForm F 3`, a lattice $L$ and its localization
$\Lambda_p = L_\mathfrak p$ with basis the columns of $\gamma$, Gram matrix `locGram Q v γ` (the matrix of
$B = 2\phi$; $2$ is a unit, so its determinant has the valuation of Cassels' $d$), and
$\theta(O^+(\Lambda_p))$ = `localSpinorNormGroup` (a subgroup of $F_\mathfrak p^\times$ containing the squares).

**Proves** (Cassels, *Rational Quadratic Forms*, Ch. 10, Example 1, p. 192): if $\phi$ is integer-valued on the ternary
lattice $\Lambda_p$ and $p$ divides its determinant exactly once, then $\theta(\sigma)$ runs through all classes of
$F_\mathfrak p^\times/(F_\mathfrak p^\times)^2$ as $\sigma$ runs through $O^+(\Lambda_p)$
(`localSpinorNormGroup_eq_top_of_det`). Generalization: a number field $F$ in place of $\mathbb Q$.

**Proof.** A diagonal basis (Jordan decomposition, `exists_diag_basis`) has values of valuations $0, 0, 1$: the two
unit vectors give all units (Cassels, Ch. 11, Lemma 3.7, `units_mem_localSpinorNormGroup_of_orthogonal`), and the
product of the symmetries in a unit vector and in the third vector has spinor norm of valuation $1$.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec3Local

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] (Q : QuadForm F 3) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- If an orthogonal basis of $L_\mathfrak p$ has two vectors of unit value and one of valuation $1$, then
$\theta(O^+(L_\mathfrak p))$ is everything. -/
theorem localSpinorNormGroup_eq_top_of_orthogonal_triple (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (L : Lat F 3) (γ : GL (Fin 3) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1)
    (horth : ∀ k l, k ≠ l → locGram Q v γ k l = 0) {i i' j : Fin 3} (hii' : i ≠ i') (hij : i ≠ j)
    (hi : Valued.v (locGram Q v γ i i) = 1) (hi' : Valued.v (locGram Q v γ i' i') = 1)
    (hj : Valued.v (locGram Q v γ j j) = exp (-1 : ℤ)) :
    localSpinorNormGroup Q hQ v L = ⊤ := by
  have hunits := units_mem_localSpinorNormGroup_of_orthogonal Q v hQ h2 L γ hγ horth hii' (hi.trans hi'.symm)
  have h2v : Valued.v (2 : Fv) = 1 := valued_two h2
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  have hmem : ∀ l, γ.val *ᵥ Pi.single l 1 ∈ loc v L.1 := fun l => by
    rw [hγ, mem_locAct]; exact ⟨_, single_mem_std l (by simp), rfl⟩
  set x : Fin 3 → Fv := γ.val *ᵥ Pi.single i 1 with hx
  set y : Fin 3 → Fv := γ.val *ᵥ Pi.single j 1 with hy
  have hQx2 : 2 * Q.evalIn Fv x = locGram Q v γ i i := by
    rw [two_mul_evalIn_eq, hx, locGram_apply_eq]
  have hQy2 : 2 * Q.evalIn Fv y = locGram Q v γ j j := by
    rw [two_mul_evalIn_eq, hy, locGram_apply_eq]
  have hQx : Valued.v (Q.evalIn Fv x) = 1 := by
    have h := hi
    rw [← hQx2, map_mul, h2v, one_mul] at h
    exact h
  have hQy : Valued.v (Q.evalIn Fv y) = exp (-1 : ℤ) := by
    have h := hj
    rw [← hQy2, map_mul, h2v, one_mul] at h
    exact h
  have hx0 : Q.evalIn Fv x ≠ 0 := fun h => by rw [h, map_zero] at hQx; exact zero_ne_one hQx
  have hy0 : Q.evalIn Fv y ≠ 0 := fun h => by
    rw [h, map_zero] at hQy; exact WithZero.exp_ne_zero hQy.symm
  have hxs : symm Q Fv x ∈ locStabV Q v L := symm_mem_locStabV_of_unit L hint (hmem i) hQx
  have hys : symm Q Fv y ∈ locStabV Q v L := by
    show locAct v (symm Q Fv y : GL (Fin 3) Fv) (loc v L.1) = loc v L.1
    refine locAct_symm_eq (hmem j) hy0 fun z hz => ?_
    rw [hγ, mem_locAct] at hz
    obtain ⟨d, hd, rfl⟩ := hz
    rw [hy, qbil_mulVec_locGram, single_dotProduct, locGram_mulVec_diag horth, hQy, one_mul, map_mul, hj]
    have hd' := mem_std_iff.mp hd
    calc _ ≤ exp (-1 : ℤ) * 1 := mul_le_mul' le_rfl (hd' j)
      _ = _ := mul_one _
  have hprod : Q.evalIn Fv x * Q.evalIn Fv y ≠ 0 := mul_ne_zero hx0 hy0
  have ha : Units.mk0 _ hprod ∈ localSpinorNormGroup Q hQ v L :=
    mem_localSpinorNormGroup_of_symm_pair hQ L hx0 hy0 hxs hys _ (sqClassOf_of_ne_zero hprod)
  have hva : Valued.v ((Units.mk0 _ hprod : Fvˣ) : Fv) = exp (-1 : ℤ) := by
    show Valued.v (Q.evalIn Fv x * Q.evalIn Fv y) = _
    rw [map_mul, hQx, hQy, one_mul]
  rw [eq_top_iff]
  intro w _
  have hw0 : Valued.v (w : Fv) ≠ 0 := (Valuation.ne_zero_iff _).mpr w.ne_zero
  set m : ℤ := WithZero.log (Valued.v (w : Fv)) with hm
  have hwm : Valued.v (w : Fv) = exp m := by rw [hm, exp_log hw0]
  have hu : Valued.v ((w * (Units.mk0 _ hprod) ^ m : Fvˣ) : Fv) = 1 := by
    rw [Units.val_mul, map_mul, hwm, Units.val_zpow_eq_zpow_val, map_zpow₀, hva, ← WithZero.exp_zsmul]
    rw [← exp_add]
    simp
  have hwu := hunits _ hu
  have : w = (w * (Units.mk0 _ hprod) ^ m) * ((Units.mk0 _ hprod) ^ m)⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ hwu (Subgroup.inv_mem _ (Subgroup.zpow_mem _ ha m))

/-- **Cassels, Ch. 10, Example 1** (p. 192). Let $\mathfrak p \nmid 2$, let $\phi$ be integer-valued on the ternary
lattice $\Lambda_p$, and let $\mathfrak p$ divide the determinant of $\Lambda_p$ exactly once. Then the spinor norms of
$O^+(\Lambda_p)$ run through all of $F_\mathfrak p^\times/(F_\mathfrak p^\times)^2$. -/
@[kb "cassels1978" "Ch. 10, Example 1, p. 192 (generalization: number field)"]
theorem localSpinorNormGroup_eq_top_of_det (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (L : Lat F 3)
    (γ : GL (Fin 3) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1)
    (hdet : Valued.v (locGram Q v γ).det = exp (-1 : ℤ)) :
    localSpinorNormGroup Q hQ v L = ⊤ := by
  obtain ⟨γ', ν, hγ', horth, hval, hdet'⟩ := exists_diag_basis hQ h2 L γ hγ hint
  have hG : locGram Q v γ' = Matrix.diagonal (fun k => locGram Q v γ' k k) := by
    ext k l
    by_cases h : k = l
    · subst h; simp
    · rw [horth k l h, Matrix.diagonal_apply_ne _ h]
  have hd1 := hdet'.trans hdet
  rw [hG, Matrix.det_diagonal, map_prod] at hd1
  simp only [hval] at hd1
  rw [prod_exp, exp_inj] at hd1
  have h3 : (∑ k, ν k) = 1 := by
    have : (∑ k, -(ν k : ℤ)) = -((∑ k, ν k : ℕ) : ℤ) := by simp [Finset.sum_neg_distrib]
    omega
  rw [Fin.sum_univ_three] at h3
  have hv0 : ∀ k, ν k = 0 → Valued.v (locGram Q v γ' k k) = 1 := fun k hk => by
    rw [hval k, hk]; simp
  have hv1 : ∀ k, ν k = 1 → Valued.v (locGram Q v γ' k k) = exp (-1 : ℤ) := fun k hk => by
    rw [hval k, hk]; simp
  have a0 : ν 0 = 1 ∧ ν 1 = 0 ∧ ν 2 = 0 ∨ ν 0 = 0 ∧ ν 1 = 1 ∧ ν 2 = 0 ∨ ν 0 = 0 ∧ ν 1 = 0 ∧ ν 2 = 1 := by
    omega
  rcases a0 with ⟨h0, h1, h2'⟩ | ⟨h0, h1, h2'⟩ | ⟨h0, h1, h2'⟩
  · exact localSpinorNormGroup_eq_top_of_orthogonal_triple Q v hQ h2 L γ' hγ' hint horth (i := 1) (i' := 2) (j := 0) (by decide) (by decide)
      (hv0 _ h1) (hv0 _ h2') (hv1 _ h0)
  · exact localSpinorNormGroup_eq_top_of_orthogonal_triple Q v hQ h2 L γ' hγ' hint horth (i := 0) (i' := 2) (j := 1) (by decide) (by decide)
      (hv0 _ h0) (hv0 _ h2') (hv1 _ h1)
  · exact localSpinorNormGroup_eq_top_of_orthogonal_triple Q v hQ h2 L γ' hγ' hint horth (i := 0) (i' := 1) (j := 2) (by decide) (by decide)
      (hv0 _ h0) (hv0 _ h1) (hv1 _ h2')

end QuadFormsKB.Lattices
