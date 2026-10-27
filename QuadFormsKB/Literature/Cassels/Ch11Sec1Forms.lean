/-
# Cassels, Chapter 11, §1: lattices and forms, proper equivalence (Corollaries 1 and 2 to Lemma 1.1)

**Layer:** $V = F^n$ over a number field $F$ with the form $Q$ = `Q : QuadForm F n` (Cassels: $F = \mathbb Q$); the
free lattice $\gamma\mathcal O_F^n$ = `latOf γ` with basis the columns $b_j = \gamma e_j$ of $\gamma \in
\mathrm{GL}_n(F)$, and its form $f_\gamma(x) = Q(\gamma x) = \phi(x_1b_1 + \dots + x_nb_n)$ (`basisForm`, the Gram
form `gramFormF` of the basis, a form over $F$); `IsProperIsometric` (Cassels' proper equivalence of lattices).

**Proves**
* Lemma 1.1, Corollary 1 (p. 197): $\Lambda = \gamma\mathcal O_F^n$ is improperly equivalent to itself (has an
  automorph of determinant $-1$) if and only if its form $f_\gamma$ is improperly $\mathcal O_F$-equivalent to itself
  (`exists_improper_autLat_iff`).
* Lemma 1.1, Corollary 2 (pp. 197–198), over $\mathbb Q$: for positively oriented bases ($\det\gamma > 0$), the
  lattices $\gamma\mathbb Z^n$, $\delta\mathbb Z^n$ are properly equivalent if and only if the forms $f_\gamma$,
  $f_\delta$ are properly $\mathbb Z$-equivalent (`isProperIsometric_latOf_iff_rat`); every lattice has a positively
  oriented basis (`exists_latOf_pos_rat`); and the form of the basis $\gamma$ is $x \mapsto Q(\gamma x)$
  (`basisForm_evalIn_rat`), so the forms that occur are those $\mathbb Q$-equivalent to $Q$ by a matrix of positive
  determinant. Together: proper classes of lattices in $V$ $\leftrightarrow$ proper $\mathbb Z$-classes of forms in the
  proper $\mathbb Q$-class of $Q$ (Cassels' $\mathbb Q$-basis $e_1, \dots, e_n$ of $V$ is the standard basis here).
-/
import QuadFormsKB.Literature.OMeara.Sec102
import QuadFormsKB.Lattices.FreeBridge
import QuadFormsKB.HilbertModular.GenusTheta

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **The form of a basis** $f_\gamma(x) = Q(\gamma x) = \phi(x_1b_1 + \dots + x_nb_n)$, $b_j = \gamma e_j$ the columns
of $\gamma$ (Cassels 1978, Ch. 11, §1, p. 197: the form corresponding to the lattice with basis $b_1, \dots, b_n$). -/
abbrev basisForm (γ : GL (Fin n) F) : QuadForm F n :=
  gramFormF Q.toQuadraticForm (fun j => γ.val *ᵥ Pi.single j 1)

/-- **Cassels, Lemma 1.1, Corollary 1** (Ch. 11, p. 197): *suppose that the class of the lattice $\Lambda$ and the
class of the form $f$ correspond. Then $\Lambda$ is improperly equivalent to itself precisely when $f$ is improperly
equivalent to itself.* Here $\Lambda = \gamma\mathcal O_F^n$ and $f = f_\gamma$: there is $\alpha \in O(V)$ with
$\det\alpha = -1$ and $\alpha\Lambda = \Lambda$ if and only if there is $P \in \mathrm{GL}_n(\mathcal O_F)$ with
$\det P = -1$ and $f_\gamma(Px) = f_\gamma(x)$. -/
@[kb "cassels1978" "Ch. 11, Lemma 1.1, Cor. 1, p. 197 (over 𝓞_F, free lattices)"]
theorem exists_improper_autLat_iff (γ : GL (Fin n) F) :
    (∃ α : orthGroup Q F, ((α : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = -1 ∧
        glImage (α : GL (Fin n) F) (latOf γ) = latOf γ) ↔
      ∃ P : GL (Fin n) (𝓞 F), (P : Matrix (Fin n) (Fin n) (𝓞 F)).det = -1 ∧
        ∀ x : Fin n → F, (basisForm Q γ).evalIn F ((P : Matrix (Fin n) (Fin n) (𝓞 F)).map
          (algebraMap (𝓞 F) F) *ᵥ x) = (basisForm Q γ).evalIn F x := by
  constructor
  · rintro ⟨α, hdet, hα⟩
    have hP : glImage (γ⁻¹ * (α : GL (Fin n) F) * γ) intVec = intVec := by
      rw [glImage_mul, glImage_mul]
      change glImage γ⁻¹ (glImage (α : GL (Fin n) F) (latOf γ)) = intVec
      rw [hα, latOf, ← glImage_mul, inv_mul_cancel, glImage_one]
    obtain ⟨P₀, hP₀⟩ := exists_gl_int_of_glImage_eq hP
    have e : (P₀ : Matrix (Fin n) (Fin n) (𝓞 F)).map (algebraMap (𝓞 F) F) =
        (γ⁻¹ * (α : GL (Fin n) F) * γ).val := congrArg Units.val hP₀
    refine ⟨P₀, ?_, fun x => ?_⟩
    · apply IsFractionRing.injective (𝓞 F) F
      rw [RingHom.map_det, RingHom.mapMatrix_apply, e, Units.val_mul, Units.val_mul, det_mul, det_mul,
        hdet, map_neg, map_one]
      have h1 := congrArg Matrix.det (Units.inv_mul γ)
      rw [det_mul, det_one] at h1
      linear_combination -h1
    · rw [evalIn_gramFormF_col, evalIn_gramFormF_col, e, mulVec_mulVec, ← Units.val_mul, ← mul_assoc,
        ← mul_assoc, mul_inv_cancel, one_mul, Units.val_mul, ← mulVec_mulVec]
      exact evalIn_mulVec_of_mem Q α.2 _
  · rintro ⟨P₀, hdet, hP₀⟩
    set P := GeneralLinearGroup.map (algebraMap (𝓞 F) F) P₀
    have hPv : P.val = (P₀ : Matrix (Fin n) (Fin n) (𝓞 F)).map (algebraMap (𝓞 F) F) := rfl
    have hval : ∀ z, Q.evalIn F ((γ * P * γ⁻¹).val *ᵥ z) = Q.evalIn F z := by
      intro z
      have := hP₀ (γ⁻¹.val *ᵥ z)
      have h2 : γ.val *ᵥ (γ⁻¹.val *ᵥ z) = z := by
        rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      rw [evalIn_gramFormF_col, evalIn_gramFormF_col, h2] at this
      rw [Units.val_mul, Units.val_mul, hPv, ← mulVec_mulVec, ← mulVec_mulVec]
      exact this
    have hmem : γ * P * γ⁻¹ ∈ orthGroup Q F := mem_orthGroup_of_eval Q fun z => hval z
    refine ⟨⟨γ * P * γ⁻¹, hmem⟩, ?_, ?_⟩
    · change (γ * P * γ⁻¹).val.det = -1
      rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hPv, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
        hdet, map_neg, map_one]
      have h1 := congrArg Matrix.det (Units.mul_inv γ)
      rw [det_mul, det_one] at h1
      linear_combination -h1
    · change glImage (γ * P * γ⁻¹) (glImage γ intVec) = glImage γ intVec
      rw [← glImage_mul, mul_assoc, inv_mul_cancel, mul_one, glImage_mul, glImage_map_intVec]

/-- The determinant of a matrix in $\mathrm{GL}_n(\mathbb Z)$ ($\mathbb Z = \mathcal O_{\mathbb Q}$) is $\pm 1$. -/
theorem det_int_rat_eq {n : ℕ} (P : GL (Fin n) (𝓞 ℚ)) :
    (P : Matrix (Fin n) (Fin n) (𝓞 ℚ)).det = 1 ∨ (P : Matrix (Fin n) (Fin n) (𝓞 ℚ)).det = -1 := by
  have hu : IsUnit (Rat.ringOfIntegersEquiv (P : Matrix (Fin n) (Fin n) (𝓞 ℚ)).det) :=
    (P.isUnit.map Matrix.detMonoidHom).map _
  rcases Int.isUnit_iff.mp hu with h | h
  · left; exact Rat.ringOfIntegersEquiv.injective (by rw [h, map_one])
  · right; exact Rat.ringOfIntegersEquiv.injective (by rw [h, map_neg, map_one])

/-- **Cassels, Lemma 1.1, Corollary 2** (Ch. 11, pp. 197–198), the correspondence on classes: *if
$a_1, \dots, a_n$ and $b_1, \dots, b_n$ are positively oriented bases of lattices $\Lambda$, $\Gamma$, then $\Lambda$
and $\Gamma$ are properly equivalent if and only if the forms $\phi(\sum x_ia_i)$ and $\phi(\sum x_ib_i)$ are properly
$\mathbb Z$-equivalent.* Here the bases are the columns of $\gamma$, $\delta$ with $\det\gamma > 0$, $\det\delta > 0$
("positively oriented" with respect to the standard basis of $\mathbb Q^n$), and proper $\mathbb Z$-equivalence is
$f_\delta(Px) = f_\gamma(x)$ with $P \in \mathrm{GL}_n(\mathbb Z)$ (here $\mathcal O_{\mathbb Q}$), $\det P = 1$. The
space $V$ is regular (Cassels' standing assumption): this is used to see that an isometry of positive determinant has
determinant $1$. -/
@[kb "cassels1978" "Ch. 11, Lemma 1.1, Cor. 2, pp. 197–198 (classes correspond)"]
theorem isProperIsometric_latOf_iff_rat {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (γ δ : GL (Fin n) ℚ)
    (hγ : 0 < (γ : Matrix (Fin n) (Fin n) ℚ).det) (hδ : 0 < (δ : Matrix (Fin n) (Fin n) ℚ).det) :
    IsProperIsometric Q (latOf γ) (latOf δ) ↔
      ∃ P : GL (Fin n) (𝓞 ℚ), (P : Matrix (Fin n) (Fin n) (𝓞 ℚ)).det = 1 ∧
        ∀ x : Fin n → ℚ, (basisForm Q δ).evalIn ℚ ((P : Matrix (Fin n) (Fin n) (𝓞 ℚ)).map
          (algebraMap (𝓞 ℚ) ℚ) *ᵥ x) = (basisForm Q γ).evalIn ℚ x := by
  have hinv : ∀ g : GL (Fin n) ℚ, (g⁻¹ : GL (Fin n) ℚ).val.det * g.val.det = 1 := fun g => by
    rw [← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
  have hpos : ∀ g : GL (Fin n) ℚ, 0 < g.val.det → 0 < (g⁻¹ : GL (Fin n) ℚ).val.det := fun g hg => by
    have := hinv g
    by_contra h
    push Not at h
    nlinarith
  constructor
  · rintro ⟨σ, hσ, he⟩
    have hP : glImage (δ⁻¹ * (σ : GL (Fin n) ℚ) * γ) intVec = intVec := by
      rw [glImage_mul, glImage_mul]
      change glImage δ⁻¹ (glImage (σ : GL (Fin n) ℚ) (latOf γ)) = intVec
      rw [he, latOf, ← glImage_mul, inv_mul_cancel, glImage_one]
    obtain ⟨P₀, hP₀⟩ := exists_gl_int_of_glImage_eq hP
    have e : (P₀ : Matrix (Fin n) (Fin n) (𝓞 ℚ)).map (algebraMap (𝓞 ℚ) ℚ) =
        (δ⁻¹ * (σ : GL (Fin n) ℚ) * γ).val := congrArg Units.val hP₀
    refine ⟨P₀, ?_, fun x => ?_⟩
    · have hd : algebraMap (𝓞 ℚ) ℚ (P₀ : Matrix (Fin n) (Fin n) (𝓞 ℚ)).det =
          (δ⁻¹ : GL (Fin n) ℚ).val.det * γ.val.det := by
        rw [RingHom.map_det, RingHom.mapMatrix_apply, e, Units.val_mul, Units.val_mul, det_mul, det_mul,
          show ((σ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det = 1 from hσ, mul_one]
      rcases det_int_rat_eq P₀ with h | h
      · exact h
      · exfalso
        rw [h, map_neg, map_one] at hd
        have := mul_pos (hpos δ hδ) hγ
        linarith
    · rw [evalIn_gramFormF_col, evalIn_gramFormF_col, e, mulVec_mulVec, ← Units.val_mul, ← mul_assoc,
        ← mul_assoc, mul_inv_cancel, one_mul, Units.val_mul, ← mulVec_mulVec]
      exact evalIn_mulVec_of_mem Q σ.2 _
  · rintro ⟨P₀, hdet, hP₀⟩
    set P := GeneralLinearGroup.map (algebraMap (𝓞 ℚ) ℚ) P₀
    have hPv : P.val = (P₀ : Matrix (Fin n) (Fin n) (𝓞 ℚ)).map (algebraMap (𝓞 ℚ) ℚ) := rfl
    have hval : ∀ z, Q.evalIn ℚ ((δ * P * γ⁻¹).val *ᵥ z) = Q.evalIn ℚ z := by
      intro z
      have := hP₀ (γ⁻¹.val *ᵥ z)
      have h2 : γ.val *ᵥ (γ⁻¹.val *ᵥ z) = z := by
        rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      rw [evalIn_gramFormF_col, evalIn_gramFormF_col, h2] at this
      rw [Units.val_mul, Units.val_mul, hPv, ← mulVec_mulVec, ← mulVec_mulVec]
      exact this
    have hmem : δ * P * γ⁻¹ ∈ orthGroup Q ℚ := mem_orthGroup_of_eval Q fun z => hval z
    refine ⟨⟨δ * P * γ⁻¹, hmem⟩, ?_, ?_⟩
    · have hd : (δ * P * γ⁻¹).val.det = δ.val.det * (γ⁻¹ : GL (Fin n) ℚ).val.det := by
        rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hPv, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
          hdet, map_one, mul_one]
      rcases Tamagawa.det_eq_one_or_neg_one Q hQ ⟨δ * P * γ⁻¹, hmem⟩ with h | h
      · exact h
      · exfalso
        change (δ * P * γ⁻¹).val.det = -1 at h
        have := mul_pos hδ (hpos γ hγ)
        linarith
    · change glImage (δ * P * γ⁻¹) (glImage γ intVec) = glImage δ intVec
      rw [← glImage_mul, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, glImage_mul, glImage_map_intVec]

/-- **Cassels, Lemma 1.1, Corollary 2** (Ch. 11, pp. 197–198), the map is defined on all lattices: *every
$\mathbb Z$-lattice in $V$ has a positively oriented basis*: $\Lambda = \gamma\mathbb Z^n$ with $\det\gamma > 0$
(for $n \ge 1$; change the sign of one basis vector). -/
@[kb "cassels1978" "Ch. 11, Lemma 1.1, Cor. 2, pp. 197–198 (positively oriented bases)"]
theorem exists_latOf_pos_rat {n : ℕ} (hn : 0 < n) (L : Lat ℚ n) :
    ∃ γ : GL (Fin n) ℚ, 0 < (γ : Matrix (Fin n) (Fin n) ℚ).det ∧ L.1 = latOf γ := by
  have : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom Rat.ringOfIntegersEquiv.symm.surjective
  obtain ⟨γ, hγ⟩ := HilbertModular.exists_latOf_of_isPrincipalIdealRing L
  have h0 : γ.val.det ≠ 0 := (γ.isUnit.map Matrix.detMonoidHom).ne_zero
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · -- flip the sign of the first basis vector
    let D₀ : Matrix (Fin n) (Fin n) (𝓞 ℚ) := Matrix.diagonal (Function.update 1 ⟨0, hn⟩ (-1))
    have hD₀ : D₀ * D₀ = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i
      by_cases hi : i = ⟨0, hn⟩
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    let D : GL (Fin n) (𝓞 ℚ) := ⟨D₀, D₀, hD₀, hD₀⟩
    have hdetD : algebraMap (𝓞 ℚ) ℚ (D : Matrix (Fin n) (Fin n) (𝓞 ℚ)).det = -1 := by
      change algebraMap (𝓞 ℚ) ℚ D₀.det = -1
      rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp
    refine ⟨γ * GeneralLinearGroup.map (algebraMap (𝓞 ℚ) ℚ) D, ?_, ?_⟩
    · rw [Units.val_mul, det_mul]
      change 0 < γ.val.det * ((D : Matrix (Fin n) (Fin n) (𝓞 ℚ)).map (algebraMap (𝓞 ℚ) ℚ)).det
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdetD]
      linarith
    · rw [hγ, latOf, latOf, glImage_mul, glImage_map_intVec]
  · exact ⟨γ, hpos, hγ⟩

/-- **Cassels, Lemma 1.1, Corollary 2** (Ch. 11, pp. 197–198), the forms that occur: the form of the basis $\gamma$
of $\gamma\mathbb Z^n$ is $x \mapsto Q(\gamma x)$. So every form $f(x) = Q(\gamma x)$ with $\det\gamma > 0$ (in
particular every form in the proper $\mathbb Q$-class of $Q$, $\det\gamma = 1$) is the form of the positively oriented
basis $\gamma$ of the lattice $\gamma\mathbb Z^n$. -/
@[kb "cassels1978" "Ch. 11, Lemma 1.1, Cor. 2, pp. 197–198 (every form of the proper ℚ-class occurs)"]
theorem basisForm_evalIn_rat {n : ℕ} (Q : QuadForm ℚ n) (γ : GL (Fin n) ℚ) (x : Fin n → ℚ) :
    (basisForm Q γ).evalIn ℚ x = Q.evalIn ℚ ((γ : Matrix (Fin n) (Fin n) ℚ) *ᵥ x) :=
  evalIn_gramFormF_col Q γ x

end QuadFormsKB.Lattices
