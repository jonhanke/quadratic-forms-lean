/-
# Cassels, Chapter 11, §4: lattices agreeing at all but finitely many odd primes (Lemma 4.1)

**Layer:** $V = F^n$ over a number field $F$ with the form $Q$ = `Q : QuadForm F n` (Cassels: $F = \mathbb Q$);
lattices `Lat F n`, localizations `loc v L.1`, bases of local lattices as in `Ch11Sec3Local.lean` (`locGram`).

**Proves** Cassels' Lemma 4.1 (p. 215) (`sameGenus_of_unimodular_of_loc_ne`): two lattices $\Lambda, \Gamma$ such that
at every prime $p$ where $\Lambda_p \ne \Gamma_p$ (i.e. $p \mid I(\Lambda, \Gamma)$, (4.2)–(4.3)) $p$ is odd and the
forms induced on $\Lambda_p$, $\Gamma_p$ are $p$-adically integral with unit determinants, are in the same genus.
*Proof* (Cassels): at such $p$ the two unimodular lattices on $V_p$ are isometric (Cassels, Ch. 8, Lemma 3.4;
O'Meara 92:2); elsewhere $\Lambda_p = \Gamma_p$.

*Deviation.* Cassels assumes that $\Lambda$ and $\Gamma$ have the same determinant (so that $I(\Lambda, \Gamma)$ is
defined, (4.1)) and that $I(\Lambda, \Gamma)$ is odd; here the hypothesis is stated directly prime by prime. The
equality of determinants is not needed: two unimodular lattices on the same space $V_p$ have determinants that differ
by the square $(\det\delta/\det\gamma)^2$ of a unit.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec3Local

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

section Aux4

variable {v : HeightOneSpectrum (𝓞 F)}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $2B(x) = x^{\mathsf T}Hx$ for a form over any ring, evaluated over an algebra. -/
theorem two_mul_evalIn_alg {A K : Type*} [CommRing A] [CommRing K] [Algebra A K] (B : QuadForm A n)
    (x : Fin n → K) : 2 * B.evalIn K x = x ⬝ᵥ (B.hessian.map (algebraMap A K) *ᵥ x) := by
  rw [QuadForm.evalIn_eq_dotProduct, QuadForm.hessian, Matrix.map_add _ (map_add _), add_mulVec, dotProduct_add,
    Matrix.transpose_map, mulVec_transpose, dotProduct_comm x (vecMul x _), ← dotProduct_mulVec]
  ring

/-- The Gram matrix of an integral local lattice has integral entries. -/
theorem locGram_le_one' (L : Lat F n) (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1) (k l : Fin n) :
    Valued.v (locGram Q v γ k l) ≤ 1 := by
  have hmemb : ∀ k, γ.val *ᵥ Pi.single k 1 ∈ loc v L.1 := fun k => by
    rw [hγ, mem_locAct]; exact ⟨_, single_mem_std k (by simp), rfl⟩
  rw [← locGram_apply_eq]; exact qbil_le_one_of_int hint (hmemb k) (hmemb l)

/-- An integral basis gives an $\mathfrak o_\mathfrak p$-form $B$ with $B(y) = Q(\gamma y)$ and Hessian $\gamma^tH\gamma$. -/
theorem exists_intForm (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (γ : GL (Fin n) Fv)
    (hG : ∀ k l, Valued.v (locGram Q v γ k l) ≤ 1) :
    ∃ B : QuadForm 𝔬 n, B.hessian.map (algebraMap 𝔬 Fv) = locGram Q v γ ∧
      ∀ y : Fin n → Fv, B.evalIn Fv y = Q.evalIn Fv (γ.val *ᵥ y) := by
  have h2v := valued_two h2
  have hc : ∀ k l, Valued.v (if k = l then locGram Q v γ k l / 2 else locGram Q v γ k l) ≤ 1 := by
    intro k l
    split_ifs
    · rw [map_div₀, h2v, div_one]; exact hG k l
    · exact hG k l
  let B : QuadForm 𝔬 n := QuadForm.ofUpper fun k l => toO v _ (hc k l)
  have hsym : ∀ k l, locGram Q v γ l k = locGram Q v γ k l := fun k l => by
    have := congrFun (congrFun (locGram_transpose (Q := Q) (v := v) γ) k) l
    simpa using this
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  have hH : B.hessian.map (algebraMap 𝔬 Fv) = locGram Q v γ := by
    refine Matrix.ext fun k l => ?_
    simp only [Matrix.map_apply, QuadForm.hessian, B, QuadForm.ofUpper, Matrix.add_apply,
      Matrix.transpose_apply, Matrix.of_apply, map_add]
    rcases lt_trichotomy k l with h | h | h
    · have : ¬ l ≤ k := not_le.mpr h
      simp only [h.le, this, ite_true, ite_false, h.ne, map_zero, add_zero]
      rfl
    · subst h
      simp only [le_refl, ite_true]
      show locGram Q v γ k k / 2 + locGram Q v γ k k / 2 = _
      field_simp
      ring
    · have : ¬ k ≤ l := not_le.mpr h
      simp only [h.le, this, ite_true, ite_false, h.ne, map_zero, zero_add]
      show locGram Q v γ l k = _
      exact hsym k l
  refine ⟨B, hH, fun y => ?_⟩
  apply mul_left_cancel₀ h2ne
  rw [two_mul_evalIn_alg, hH, two_mul_evalIn_locGram]

end Aux4

/-- **Cassels, Lemma 4.1** (Ch. 11, p. 215): *suppose that $I(\Lambda, \Gamma)$ is odd. For all $p \mid I(\Lambda,
\Gamma)$ suppose that the quadratic forms induced by $\phi$ on $\Lambda$, $\Gamma$ are $p$-adically integral and that
their determinants are $p$-adic units. Then $\Lambda$, $\Gamma$ are in the same genus.* Here, over a number field: at
every finite prime $\mathfrak p$ with $L_\mathfrak p \ne M_\mathfrak p$, $\mathfrak p \nmid 2$, $Q$ is integral on
$L_\mathfrak p$ and on $M_\mathfrak p$, and both have a basis with unit Gram determinant. -/
@[kb "cassels1978" "Ch. 11, Lemma 4.1, p. 215 (over a number field; hypotheses prime by prime)"]
theorem sameGenus_of_unimodular_of_loc_ne (L M : Lat F n)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), loc v L.1 ≠ loc v M.1 →
      (2 : 𝓞 F) ∉ v.asIdeal ∧
      (∀ x ∈ loc v L.1, Valued.v (Q.evalIn (v.adicCompletion F) x) ≤ 1) ∧
      (∀ x ∈ loc v M.1, Valued.v (Q.evalIn (v.adicCompletion F) x) ≤ 1) ∧
      (∃ γ : GL (Fin n) (v.adicCompletion F), loc v L.1 = locAct v γ (std v) ∧
        Valued.v (locGram Q v γ).det = 1) ∧
      (∃ δ : GL (Fin n) (v.adicCompletion F), loc v M.1 = locAct v δ (std v) ∧
        Valued.v (locGram Q v δ).det = 1)) :
    SameGenus Q L.1 M.1 := by
  intro v
  by_cases hv : loc v L.1 = loc v M.1
  · exact ⟨1, (orthGroup Q _).one_mem, by rw [locAct_one, hv]⟩
  obtain ⟨h2, hL, hM, ⟨γ, hγ, hdγ⟩, ⟨δ, hδ, hdδ⟩⟩ := h v hv
  obtain ⟨Bγ, hHγ, hEγ⟩ := exists_intForm Q h2 γ (locGram_le_one' Q L γ hγ hL)
  obtain ⟨Bδ, hHδ, hEδ⟩ := exists_intForm Q h2 δ (locGram_le_one' Q M δ hδ hM)
  have hπ := LocalDensity.NF.irreducible_π v
  have hπ2 := LocalDensity.NF.π_not_dvd_two v h2
  have hunim : ∀ (B : QuadForm (v.adicCompletionIntegers F) n) (g : GL (Fin n) (v.adicCompletion F)),
      B.hessian.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) = locGram Q v g →
      Valued.v (locGram Q v g).det = 1 → ¬ LocalDensity.NF.π v ∣ B.hessian.det := by
    intro B g hB hd hdvd
    have hunit : IsUnit B.hessian.det := by
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one, ← hd, ← hB]
      exact congrArg Valued.v (RingHom.map_det (algebraMap (v.adicCompletionIntegers F)
        (v.adicCompletion F)) B.hessian)
    exact hπ.not_isUnit (isUnit_of_dvd_unit hdvd hunit)
  have hg : ∀ x : Fin n → v.adicCompletion F, Bδ.evalIn (v.adicCompletion F) x =
      Bγ.evalIn (v.adicCompletion F) ((γ⁻¹ * δ).val *ᵥ x) := by
    intro x
    rw [hEδ, hEγ, Units.val_mul, ← mulVec_mulVec, mulVec_inv_mulVec]
  have hiso := (Nbr.isometricGL_of_unimodular_of_isometricIn hπ hπ2 (v.adicCompletion F) Bγ Bδ
    (hunim Bγ γ hHγ hdγ) (hunim Bδ δ hHδ hdδ) (γ⁻¹ * δ) hg).symm
  obtain ⟨P, hP⟩ := hiso
  have hPH : Bγ.hessian = P.valᵀ * Bδ.hessian * P.val :=
    Nbr.hessian_eq_of_eval' fun x => (hP x).symm
  have hPval : (GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) P).val =
      P.val.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) := rfl
  have hGeq : locGram Q v γ = locGram Q v (δ * GeneralLinearGroup.map
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) P) := by
    rw [locGram_mul, ← hHγ, ← hHδ, hPval, hPH]
    simp [Matrix.map_mul, Matrix.transpose_map]
  generalize hP' : GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) P = P'
    at hGeq
  refine ⟨δ * P' * γ⁻¹, ?_, ?_⟩
  · have h1 : locGram Q v (δ * P' * γ⁻¹) = locGram Q v (γ * γ⁻¹) := by
      rw [locGram_mul (δ * P') γ⁻¹, ← hGeq, locGram_mul γ γ⁻¹]
    rw [mul_inv_cancel] at h1
    have h2' : locGram Q v (1 : GL (Fin n) (v.adicCompletion F)) =
        Q.hessian.map (algebraMap F (v.adicCompletion F)) := by simp [locGram]
    rw [h2'] at h1
    exact h1
  · rw [hγ, hδ, locAct_mul, locAct_mul, locAct_inv_locAct, ← hP', locAct_map_std]

end QuadFormsKB.Lattices
