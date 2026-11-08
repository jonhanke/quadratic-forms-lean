/-
# Hanke 2011, Remark 4.1: one genus of maximal lattices on a quadratic space

J. Hanke, *Enumerating maximal definite quadratic forms of bounded class number over $\mathbb Z$ in $n\ge3$ variables*,
arXiv:1110.1876v1 (bib key `hanke2011enumerating`), Remark 4.1, p. 7.

**Setting.** $F$ a number field (the paper: $F = \mathbb Q$), $Q_0$ a non-degenerate quadratic form over $\mathcal O_F$ in $n$
variables, $V = (F^n, Q)$ with $Q = Q_0$ over $F$, lattices $L$ on $V$ of any Steinitz class (`Lattices.Lat F n`).
"Maximal" is O'Meara's maximal $\mathcal O_F$-valued lattice (`OMeara.IsMaximal Q 1`, §82, p. 230: $Q(L)\subseteq\mathcal O_F$
and no larger lattice has this property); for $F = \mathbb Q$ these are the paper's maximal $\mathbb Z$-valued lattices.

**Proves** Remark 4.1: there is exactly one genus of maximal lattices on $V$ (`remark_4_1_sameGenus`; the paper cites
[Shi10, §30.1]), so the mass and the class number of a maximal lattice are determined by $V$ (`remark_4_1_mass`,
`remark_4_1_classNumber`; the library's mass counts $O(L)$, Hanke's $\mathrm{Mass}^+$ is twice it in the definite case,
`Hanke2005.hankeMass_definite_eq_two_mul_mass`).

**Proof.** Locally: a maximal lattice is maximal at every finite prime (`Hanke2005.isMaximal_loc`), and two maximal
lattices on a regular space over a local field are isometric (O'Meara 91:2, `OMeara.cls_eq_of_isMaximal`); the local
isometry is a matrix in $O(V)(F_{\mathfrak p})$ (`exists_orth_locAct_of_isMaximal`). The paper's "expressed in terms of the
standard local invariants" (the local mass factors) is §5–§7 and is not part of this file.
-/
import QuadFormsKB.Literature.Hanke2005.TheoremSixThree
import QuadFormsKB.Literature.OMeara.Sec102
import QuadFormsKB.Citation

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2011Enumerating

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity QuadFormsKB.Hanke2005

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **O'Meara 91:2 in matrix form**: two maximal lattices $\Lambda,\Lambda'$ on $(F_{\mathfrak p}^n, Q)$ are related by an
isometry $g\in O(V)(F_{\mathfrak p})$, $g\Lambda' = \Lambda$. -/
theorem exists_orth_locAct_of_isMaximal (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (Λ Λ' : Submodule 𝔬 (Fin n → Fv))
    (hΛ : letI : Invertible (2 : Fv) := invertibleOfNonzero two_ne_zero
      OMeara.IsMaximal (qv v Q₀) (pPow v 0) Λ)
    (hΛ' : letI : Invertible (2 : Fv) := invertibleOfNonzero two_ne_zero
      OMeara.IsMaximal (qv v Q₀) (pPow v 0) Λ') :
    ∃ g ∈ orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv, locAct v g Λ' = Λ := by
  classical
  let : Invertible (2 : Fv) := invertibleOfNonzero two_ne_zero
  have hV : (QuadraticMap.associated (qv v Q₀)).Nondegenerate :=
    QuadraticMap.nondegenerate_associated_iff.mpr
      (QuadraticMap.nondegenerate_polar_iff.mp (polar_nondeg_toQuadraticForm _ (nondegenerate_Qf v Q₀ hQ)))
  have hcls := OMeara.cls_eq_of_isMaximal (qv v Q₀) hV hΛ' hΛ
  have hmem : Λ ∈ OMeara.cls (qv v Q₀) Λ := ⟨1, (OMeara.orth (qv v Q₀)).one_mem, by ext x; simp [OMeara.latMap]⟩
  rw [hcls] at hmem
  obtain ⟨σ, hσ, hσΛ⟩ := hmem
  let B : Matrix (Fin n) (Fin n) Fv := LinearMap.toMatrix' (σ : (Fin n → Fv) →ₗ[Fv] (Fin n → Fv))
  have hB : ∀ z, B *ᵥ z = σ z := fun z => by
    rw [← Matrix.toLin'_apply]
    simp [B]
  have hBorth : Bᵀ * hessV v Q₀ * B = hessV v Q₀ := by
    have := sim_of_eval (Qf v Q₀) B 1 (fun z => by
      rw [one_mul, ← qv_apply, ← qv_apply, hB]
      exact hσ z)
    rwa [hessian_Qf, one_smul] at this
  have hdetH : (hessV v Q₀).det ≠ 0 := by
    have := nondegenerate_Qf v Q₀ hQ
    rwa [QuadForm.Nondegenerate, hessian_Qf] at this
  have hBdet : IsUnit B.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have := congrArg Matrix.det hBorth
    rw [det_mul, det_mul, det_transpose, h0] at this
    simp at this
    exact hdetH this.symm
  let gB : GL (Fin n) Fv := ⟨B, B⁻¹, Matrix.mul_nonsing_inv B hBdet, Matrix.nonsing_inv_mul B hBdet⟩
  have hlat : ∀ M, OMeara.latMap σ M = locAct v gB M := fun M => by
    ext x
    simp only [OMeara.latMap, locAct, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      Matrix.mulVecLin_apply]
    exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, by rw [← h, hB]⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, by rw [← h]; exact (hB y).symm⟩⟩
  exact ⟨gB, hBorth, by rw [← hlat, ← hσΛ]⟩

end Local

/-- **Remark 4.1, one genus** (Hanke 2011, p. 7; [Shi10, §30.1]): any two maximal ($\mathcal O_F$-valued) lattices $L$, $M$ on
the non-degenerate space $(F^n, Q_0)$ are in the same genus. -/
@[kb "hanke2011enumerating" "Remark 4.1, p. 7 (exactly one genus of maximal lattices in (V, Q))"]
theorem remark_4_1_sameGenus (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (L M : Lat F n)
    (hL : letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
      OMeara.IsMaximal (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F))) (1 : Submodule (𝓞 F) F) L.1)
    (hM : letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
      OMeara.IsMaximal (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F))) (1 : Submodule (𝓞 F) F) M.1) :
    SameGenus (Q₀.map (algebraMap (𝓞 F) F)) L.1 M.1 := by
  intro v
  have hL' := isMaximal_loc v Q₀ hQ ⊤ top_ne_bot L (by rw [span_image_top]; exact hL)
  have hM' := isMaximal_loc v Q₀ hQ ⊤ top_ne_bot M (by rw [span_image_top]; exact hM)
  rw [ordIdeal_top] at hL' hM'
  exact exists_orth_locAct_of_isMaximal v Q₀ hQ (loc v M.1) (loc v L.1) hM' hL'

/-- Lattices in the same genus have the same classes in their genus. -/
theorem genusClasses_eq_of_sameGenus {Q : QuadForm F n} {L M : Lat F n} (h : SameGenus Q L.1 M.1) :
    genusClasses Q L = genusClasses Q M := by
  ext c
  constructor
  · rintro ⟨N, hN, hLN⟩; exact ⟨N, hN, SameGenus.trans Q (SameGenus.symm Q h) hLN⟩
  · rintro ⟨N, hN, hMN⟩; exact ⟨N, hN, SameGenus.trans Q h hMN⟩

/-- **Remark 4.1, the mass is determined by the space** (Hanke 2011, p. 7): maximal lattices $L$, $M$ on
$(F^n, Q_0)$ have the same mass (the library's `Lattices.mass`, with $O(L)$; Hanke's $\mathrm{Mass}^+$ is twice it for
totally definite $Q_0$). -/
@[kb "hanke2011enumerating" "Remark 4.1, p. 7 (the mass of a maximal lattice is determined by (V, Q))"]
theorem remark_4_1_mass (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (L M : Lat F n)
    (hL : letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
      OMeara.IsMaximal (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F))) (1 : Submodule (𝓞 F) F) L.1)
    (hM : letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
      OMeara.IsMaximal (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F))) (1 : Submodule (𝓞 F) F) M.1) :
    mass (Q₀.map (algebraMap (𝓞 F) F)) L = mass (Q₀.map (algebraMap (𝓞 F) F)) M := by
  unfold mass
  rw [genusClasses_eq_of_sameGenus (remark_4_1_sameGenus Q₀ hQ L M hL hM)]

/-- **Remark 4.1, the class number is determined by the space**: maximal lattices on $(F^n, Q_0)$ have the same class
number $h$. -/
@[kb "hanke2011enumerating" "Remark 4.1, p. 7 (the class number of a maximal lattice is determined by (V, Q))"]
theorem remark_4_1_classNumber (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (L M : Lat F n)
    (hL : letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
      OMeara.IsMaximal (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F))) (1 : Submodule (𝓞 F) F) L.1)
    (hM : letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
      OMeara.IsMaximal (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F))) (1 : Submodule (𝓞 F) F) M.1) :
    Lattices.classNumber (Q₀.map (algebraMap (𝓞 F) F)) L = Lattices.classNumber (Q₀.map (algebraMap (𝓞 F) F)) M := by
  unfold Lattices.classNumber
  rw [genusClasses_eq_of_sameGenus (remark_4_1_sameGenus Q₀ hQ L M hL hM)]

end QuadFormsKB.Hanke2011Enumerating
