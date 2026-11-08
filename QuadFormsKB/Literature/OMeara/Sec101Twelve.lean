/-
# O'Meara §101C: Proposition 101:12 for $n \le 3$

**Layer:** $F$ a number field, $V = F^n$ with a nondegenerate `Q : QuadForm F n`; the matrix groups $O(V)$ =
`orthGroup Q F`, $O^+(V)$ = `Tamagawa.soSub Q F`, $O'(V)$ = `spinorKernel Q F`, $\Omega_n(V)$ = the commutator subgroup
`commutator (orthGroup Q F)`, the same over the completions $F_\mathfrak p$ (finite spots) and $F_w$ (infinite spots),
localization `orthMap`; O'Meara's abstract groups `OMeara.omega`, `OMeara.orthPrime` through `QIn.glEquiv`.

**Proves**
* `commutator_le_spinorKernel`: $\Omega_n \subseteq O'_n$ over any field of characteristic $0$ containing $F$
  (a commutator of products of symmetries is a product of an even number of symmetries with square spinor norm);
* `omeara101_12_of_le_three` (**Proposition 101:12 for $n \le 3$**, p. 294): for $\sigma \in O^+(V)$,
  $\sigma \in \Omega_n(V)$ iff $\sigma_\mathfrak p \in \Omega_n(V_\mathfrak p)$ at every spot. This is the first step of
  O'Meara's proof ("In particular this proves the proposition when $1 \le n \le 3$"): the local conditions give
  $\sigma \in O'_n(V)$ (Global Square Theorem, `mem_spinorKernel_iff_forall`), and $O'_n = \Omega_n$ for $n \le 3$
  (55:5, `OMeara.omega_eq_orthPrime_of_finrank_le_three`). Unconditional. The case $n \ge 4$ is the named statement
  `OMeara101_12` (it needs Lemma 101:11).
-/
import QuadFormsKB.Literature.OMeara.Sec101Named
import QuadFormsKB.Literature.OMeara.Sec95Input

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **$\Omega_n \subseteq O'_n$** (O'Meara 1973, §55, p. 137; the inclusion $\Omega_n \subseteq O'_n$ of the normal series
of §56) over any field $K \supseteq F$ of characteristic $0$: every commutator in $O(V_K)$ lies in the spinor kernel. -/
@[kb "omeara1963" "§56, p. 141 (Ω_n ⊆ O'_n)"]
theorem commutator_le_spinorKernel (K : Type) [Field K] [Algebra F K] [CharZero K] (hQ : Q.Nondegenerate) :
    commutator (orthGroup Q K) ≤ spinorKernel Q K := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  obtain ⟨xs, hxs, rfl⟩ := exists_symmProd_eq Q K hQ a
  obtain ⟨ys, hys, rfl⟩ := exists_symmProd_eq Q K hQ b
  refine ⟨xs ++ ys ++ xs.reverse ++ ys.reverse, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro z hz
    simp only [List.mem_append, List.mem_reverse] at hz
    rcases hz with ((h | h) | h) | h
    · exact hxs z h
    · exact hys z h
    · exact hxs z h
    · exact hys z h
  · simp only [List.length_append, List.length_reverse]
    exact ⟨xs.length + ys.length, by ring⟩
  · rw [valProd_append, valProd_append, valProd_append, valProd_reverse, valProd_reverse]
    exact ⟨valProd Q K xs * valProd Q K ys, by ring⟩
  · rw [symmProd_append, symmProd_append, symmProd_append, symmProd_reverse, symmProd_reverse,
      commutatorElement_def]

/-- Localization maps commutators to commutators. -/
theorem orthMap_mem_commutator (R : Type*) [CommRing R] [Algebra F R] {σ : orthGroup Q F}
    (h : σ ∈ commutator (orthGroup Q F)) : orthMap Q R σ ∈ commutator (orthGroup Q R) := by
  have hle : (commutator (orthGroup Q F)).map (orthMap Q R) ≤ commutator (orthGroup Q R) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact hle (Subgroup.mem_map_of_mem _ h)

/-- **Proposition 101:12 for $n \le 3$** (O'Meara 1973, §101C, p. 294): for a regular $V = F^n$ with $n \le 3$ over the
number field $F$ and $\sigma \in O^+(V)$, $\sigma \in \Omega_n(V)$ if and only if $\sigma_\mathfrak p \in
\Omega_n(V_\mathfrak p)$ at every spot $\mathfrak p$, finite and infinite. (Only the finite spots are needed for the
sufficiency.) Unconditional. -/
@[kb "omeara1963" "§101C, 101:12, p. 294 (the case 1 ≤ n ≤ 3)"]
theorem omeara101_12_of_le_three (hQ : Q.Nondegenerate) (hn : n ≤ 3) {σ : orthGroup Q F}
    (hσ : σ ∈ Tamagawa.soSub Q F) :
    σ ∈ commutator (orthGroup Q F) ↔
      (∀ v : HeightOneSpectrum (𝓞 F),
        orthMap Q (v.adicCompletion F) σ ∈ commutator (orthGroup Q (v.adicCompletion F))) ∧
      ∀ w : InfinitePlace F, orthMap Q w.Completion σ ∈ commutator (orthGroup Q w.Completion) := by
  constructor
  · intro h
    exact ⟨fun v => orthMap_mem_commutator Q _ h, fun w => orthMap_mem_commutator Q _ h⟩
  · rintro ⟨hv, -⟩
    have hk : σ ∈ spinorKernel Q F :=
      (mem_spinorKernel_iff_forall Q hQ hσ).mpr fun v => commutator_le_spinorKernel Q _ hQ (hv v)
    have hnd : (QuadraticMap.associated (qk Q F)).Nondegenerate :=
      QuadraticMap.nondegenerate_associated_iff.mpr
        (QuadraticMap.nondegenerate_polar_iff.mp (QuadForm.nondegenerate_polarBilin_toQuadraticFormIn F hQ))
    rw [OMeara.QIn.mem_commutator_iff, OMeara.omega_eq_orthPrime_of_finrank_le_three _ hnd
      (by rw [Module.finrank_fin_fun]; exact hn)]
    exact OMeara.QIn.mem_orthPrime_of_mem_spinorKernel Q F hk

/-- **$O'_n = \Omega_n$ for $n \le 3$** (O'Meara 1973, §101C, p. 295, the case $n \le 3$ of "$O'_n = \Omega_n$ when
$n \ne 4$", i.e. of the field `ne_four` of the named statement `OMeara101_r40`): over the number field $F$, for a
regular $V = F^n$ with $n \le 3$, $O'_n(V) \subseteq \Omega_n(V)$ (55:5). Unconditional. -/
@[kb "omeara1963" "§101C, p. 295 (O'_n = Ω_n for n ≠ 4: the case n ≤ 3)"]
theorem spinorKernel_le_commutator_of_le_three (hQ : Q.Nondegenerate) (hn : n ≤ 3) :
    spinorKernel Q F ≤ commutator (orthGroup Q F) := by
  intro σ hk
  have hnd : (QuadraticMap.associated (qk Q F)).Nondegenerate :=
    QuadraticMap.nondegenerate_associated_iff.mpr
      (QuadraticMap.nondegenerate_polar_iff.mp (QuadForm.nondegenerate_polarBilin_toQuadraticFormIn F hQ))
  rw [OMeara.QIn.mem_commutator_iff, OMeara.omega_eq_orthPrime_of_finrank_le_three _ hnd
    (by rw [Module.finrank_fin_fun]; exact hn)]
  exact OMeara.QIn.mem_orthPrime_of_mem_spinorKernel Q F hk

/-- **The kernel half of 101.r39 from 101:12** (O'Meara 1973, §101C, p. 295): the field `ker` of the named statement
`OMeara101_r39` (for $\sigma \in O'_n(V)$: $\sigma \in \Omega_n(V)$ iff $\sigma_\mathfrak p \in \Omega_n(V_\mathfrak p)$ at
every spot) follows from Proposition 101:12 (the named statement `OMeara101_12`), since $O'_n \subseteq O^+_n$. -/
@[kb "omeara1963" "§101C, p. 295 (O'_n/Ω_n ≅ ∏ O'_n(V_𝔭)/Ω_n(V_𝔭): the kernel, from 101:12)"]
theorem omeara101_r39_ker (h12 : OMeara101_12 F) (Q : QuadForm F n) (hQ : Q.Nondegenerate) {σ : orthGroup Q F}
    (hσ : σ ∈ spinorKernel Q F) :
    σ ∈ commutator (orthGroup Q F) ↔
      (∀ v : HeightOneSpectrum (𝓞 F),
        orthMap Q (v.adicCompletion F) σ ∈ commutator (orthGroup Q (v.adicCompletion F))) ∧
      ∀ w : InfinitePlace F, orthMap Q w.Completion σ ∈ commutator (orthGroup Q w.Completion) :=
  h12.holds n Q hQ σ (spinorKernel_le_soSub Q F hσ)

end QuadFormsKB.Lattices
