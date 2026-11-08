/-
# O'Meara Example 102:5 with local representations

**Layer:** $V = F^n$ over a number field $F$ with a regular form `Q : QuadForm F n`; lattices `Lat F n`, their
localizations `loc 𝔭 L` at the finite spots, the genus `SameGenus`; the form on $V_\mathfrak p$ as a Mathlib quadratic
form `qk Q F_𝔭`, and Witt's extension theorem (`QuadraticForm.exists_isometryEquiv_extend_of_associated`,
`Witt/Extension.lean`).

**Proves** Example 102:5 (O'Meara 1973, §102A, p. 300) with the book's hypothesis, `omeara102_5`: if $K$ is a
finitely generated $\mathcal O_F$-submodule of $V$ and at every spot $\mathfrak p$ there is a representation
$K_\mathfrak p \to L_\mathfrak p$, then $K \subseteq L'$ for some lattice $L'$ in the genus of $L$. The earlier
`exists_sameGenus_le` (`Sec102Rep.lean`) took the isometries $\varphi_\mathfrak p$ of $V_\mathfrak p$ as hypothesis; here
they are produced by Witt's theorem, as in the book.

*Representations.* A representation of $K_\mathfrak p$ into $L_\mathfrak p$ is given by its $F_\mathfrak p$-linear
extension $\varphi$ to the space $F_\mathfrak pK_\mathfrak p$ (`Submodule.span`): $\varphi$ is injective, preserves
$Q$, and carries $K_\mathfrak p$ into $L_\mathfrak p$. O'Meara's $K$ is a regular lattice, and an isometric linear map
of a regular space is injective, so injectivity is part of his hypothesis.
-/
import QuadFormsKB.Literature.OMeara.Sec102Rep
import QuadFormsKB.Literature.OMeara.Sec104Bridge
import QuadFormsKB.Literature.OMeara.Sec101TenAux
import QuadFormsKB.Witt.Extension

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open OMeara.QIn (glEquiv glEquiv_apply)

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **Witt's theorem for a representation of $K_\mathfrak p$**: an injective isometric linear map $\varphi$ of
$F_\mathfrak pK_\mathfrak p$ into $V_\mathfrak p$ carrying $K_\mathfrak p$ into $L_\mathfrak p$ gives an isometry
$g \in O(V_\mathfrak p)$ with $K_\mathfrak p \subseteq gL_\mathfrak p$ ($g$ is the inverse of an extension of
$\varphi$). -/
theorem exists_orthGroup_loc_le_of_rep (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) (L : Lat F n)
    {K : Submodule (𝓞 F) (Fin n → F)}
    (φ : Submodule.span (v.adicCompletion F) (loc v K : Set (Fin n → v.adicCompletion F)) →ₗ[v.adicCompletion F]
      (Fin n → v.adicCompletion F))
    (hinj : Function.Injective φ)
    (hQφ : ∀ x, Q.evalIn (v.adicCompletion F) (φ x) = Q.evalIn (v.adicCompletion F) x)
    (hφL : ∀ x (hx : x ∈ loc v K), φ ⟨x, Submodule.subset_span hx⟩ ∈ loc v L.1) :
    ∃ g ∈ orthGroup Q (v.adicCompletion F), loc v K ≤ locAct v g (loc v L.1) := by
  set Fv := v.adicCompletion F
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_extend_of_associated (qk Q Fv) (nondegenerate_qk Q v hQ)
    φ hinj (fun x => by rw [qk_apply, qk_apply]; exact hQφ x)
  have hmem : ρ.symm.toLinearEquiv ∈ OMeara.orth (qk Q Fv) := fun x => ρ.symm.map_app x
  obtain ⟨g, hg⟩ := exists_orthGroup_glEquiv_eq Q Fv hmem
  refine ⟨g, g.2, fun x hx => ?_⟩
  rw [locAct_eq_latMap, hg]
  refine ⟨φ ⟨x, Submodule.subset_span hx⟩, hφL x hx, ?_⟩
  have h1 := hρ ⟨x, Submodule.subset_span hx⟩
  change ρ.symm (φ ⟨x, Submodule.subset_span hx⟩) = x
  rw [← h1]
  exact ρ.symm_apply_apply x

/-- **Example 102:5** (O'Meara 1973, §102A, p. 300): let $L$ be a lattice on the regular quadratic space
$V = (F^n, Q)$ over a number field $F$ and $K$ a finitely generated $\mathcal O_F$-submodule of $V$ (`hK`). Suppose
that at every finite spot $\mathfrak p$ there is a representation $K_\mathfrak p \to L_\mathfrak p$: an injective
$F_\mathfrak p$-linear map $\varphi$ of the space $F_\mathfrak pK_\mathfrak p$ into $V_\mathfrak p$ with
$Q(\varphi x) = Q(x)$ and $\varphi(K_\mathfrak p) \subseteq L_\mathfrak p$ (for O'Meara's regular $K$ every
representation is injective). Then there is a representation $K \to L'$ for some lattice $L'$ in the genus of $L$; in
fact $K \subseteq L'$. Unconditional. The case of a scalar is `exists_sameGenus_represents` (`Sec102Rep.lean`). -/
@[kb "omeara1963" "§102A, 102:5, p. 300"]
theorem omeara102_5 (hQ : Q.Nondegenerate) (L : Lat F n) {K : Submodule (𝓞 F) (Fin n → F)} (hK : K.FG)
    (h : ∀ v : HeightOneSpectrum (𝓞 F),
      ∃ φ : Submodule.span (v.adicCompletion F) (loc v K : Set (Fin n → v.adicCompletion F)) →ₗ[v.adicCompletion F]
          (Fin n → v.adicCompletion F),
        Function.Injective φ ∧ (∀ x, Q.evalIn (v.adicCompletion F) (φ x) = Q.evalIn (v.adicCompletion F) x) ∧
        ∀ x (hx : x ∈ loc v K), φ ⟨x, Submodule.subset_span hx⟩ ∈ loc v L.1) :
    ∃ L' : Lat F n, SameGenus Q L.1 L'.1 ∧ K ≤ L'.1 := by
  refine exists_sameGenus_le Q L hK fun v => ?_
  obtain ⟨φ, hinj, hQφ, hφL⟩ := h v
  exact exists_orthGroup_loc_le_of_rep Q hQ v L φ hinj hQφ hφL

end QuadFormsKB.Lattices
