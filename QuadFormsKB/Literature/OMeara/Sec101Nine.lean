/-
# O'Meara 101:9 and the input `QuaternarySpinorInput`

**Layer:** $F$ a number field, $V = F^4$ with a nondegenerate `Q : QuadForm F 4`; the matrix groups $O'(V)$ =
`spinorKernel Q F`, $\Omega_4(V_\mathfrak p)$ = `commutator (orthGroup Q F_𝔭)` at the finite spots, localization
`orthMap`.

**Proves**
* `omeara101_9` (**Proposition 101:9**, p. 292, at the finite spots): for a finite set $T$ of finite spots with
  $\Omega_4(V_\mathfrak p) \subsetneq O'_4(V_\mathfrak p)$ ($\mathfrak p \in T$) there is $\sigma \in O'_4(V)$ with
  $\sigma_\mathfrak p \notin \Omega_4(V_\mathfrak p)$ for $\mathfrak p \in T$ and $\sigma_\mathfrak p \in \Omega_4(V_\mathfrak p)$ at
  every other finite spot. Unconditional.
* `quaternarySpinorInput_holds : QuaternarySpinorInput F`: the named input of `Lattices/StrongApproximationProof.lean`
  (its field `index` is 95:1, `OMeara.quaternarySpinor_index`; its field `global` is 101:9) holds.

*Proof of 101:9.* Not O'Meara's construction (symmetries $\tau_{(1)}\tau_{(\lambda)}\tau_{(\kappa)}\tau_{(\kappa\lambda)}$
with weak approximation and 66:3), but the correction step of 104:4 already in the library (`exists_correction`, built
from the same ingredients): pick $\varphi_\mathfrak p \in O'_4(V_\mathfrak p) \setminus \Omega_4(V_\mathfrak p)$ for
$\mathfrak p \in T$; `exists_correction` gives $g \in O'_4(V)$ with $g_\mathfrak p\varphi_\mathfrak p \in
\Omega_4(V_\mathfrak p)$ on $T$ and $g_\mathfrak p \in \Omega_4(V_\mathfrak p)$ off $T$; then $g_\mathfrak p \notin
\Omega_4(V_\mathfrak p)$ on $T$, since otherwise $\varphi_\mathfrak p = g_\mathfrak p^{-1}(g_\mathfrak p\varphi_\mathfrak p) \in
\Omega_4(V_\mathfrak p)$.

*Scope.* O'Meara's $T$ may contain any spots and his conclusion covers the infinite spots too; at an infinite spot
$\Omega_4 = O'_4$ (so $T$ consists of finite spots anyway), and the library's statement (the field `global` of
`QuaternarySpinorInput`) has no condition at the infinite spots.
-/
import QuadFormsKB.Lattices.SACorrection
import QuadFormsKB.Literature.OMeara.Sec95Input

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F]

/-- **Proposition 101:9** (O'Meara 1973, §101B, p. 292, at the finite spots): let $V = F^4$ be a regular quaternary
space over the number field $F$ and $T$ a finite set of finite spots such that $\Omega_4(V_\mathfrak p) \subsetneq
O'_4(V_\mathfrak p)$ for every $\mathfrak p \in T$ (some $\varphi \in O'_4(V_\mathfrak p)$ is not in
$\Omega_4(V_\mathfrak p)$). Then there is $\sigma \in O'_4(V)$ with $\sigma_\mathfrak p \notin \Omega_4(V_\mathfrak p)$ for
all $\mathfrak p \in T$ and $\sigma_\mathfrak p \in \Omega_4(V_\mathfrak p)$ at every other finite spot. Unconditional. -/
@[kb "omeara1963" "§101B, 101:9, p. 292"]
theorem omeara101_9 (Q : QuadForm F 4) (hQ : Q.Nondegenerate) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : ∀ v ∈ T, ∃ φ ∈ spinorKernel Q (v.adicCompletion F),
      φ ∉ commutator (↥(orthGroup Q (v.adicCompletion F)))) :
    ∃ σ ∈ spinorKernel Q F, (∀ v ∈ T, orthMap Q (v.adicCompletion F) σ ∉
        commutator (↥(orthGroup Q (v.adicCompletion F)))) ∧
      ∀ v ∉ T, orthMap Q (v.adicCompletion F) σ ∈ commutator (↥(orthGroup Q (v.adicCompletion F))) := by
  classical
  let φ : ∀ v : HeightOneSpectrum (𝓞 F), orthGroup Q (v.adicCompletion F) := fun v =>
    if h : v ∈ T then (hT v h).choose else 1
  have hφ : ∀ v (hv : v ∈ T), φ v = (hT v hv).choose := fun v hv => by simp only [φ, hv, dite_true]
  obtain ⟨g, hg, h1, h2⟩ := exists_correction Q hQ le_rfl T φ fun v hv => by
    rw [hφ v hv]; exact (hT v hv).choose_spec.1
  refine ⟨g, hg, fun v hv hgv => ?_, h2⟩
  have hmem := (commutator (↥(orthGroup Q (v.adicCompletion F)))).mul_mem
    ((commutator (↥(orthGroup Q (v.adicCompletion F)))).inv_mem hgv) (h1 v hv)
  rw [inv_mul_cancel_left, hφ v hv] at hmem
  exact (hT v hv).choose_spec.2 hmem

/-- **The named input `QuaternarySpinorInput F` holds** (O'Meara 1973, 95:1 and 101:9): the field `index` is 95:1
(`OMeara.quaternarySpinor_index`, `Sec95Input.lean`), the field `global` is 101:9 (`omeara101_9`). Unconditional. -/
@[kb "omeara1963" "§95, 95:1, p. 280; §101B, 101:9, p. 292 (the input QuaternarySpinorInput holds)"]
theorem quaternarySpinorInput_holds : QuaternarySpinorInput F :=
  ⟨fun Q hQ v φ ψ hφ hψ hφΩ hψΩ => OMeara.quaternarySpinor_index Q hQ v φ ψ hφ hψ hφΩ hψΩ,
    fun Q hQ T hT => omeara101_9 Q hQ T hT⟩

end QuadFormsKB.Lattices
