/-
# O'Meara §66: complete invariants over a number field, and isotropy at almost all spots

**Setting.** $F$ is a number field (O'Meara's global field; the function field case of §66 is outside the library),
and quadratic forms over $F$ are `QuadForm F n` with $n$ variables, nondegenerate (`Nondegenerate`: the Hessian
$H_Q = C + C^{\mathsf T}$ has $\det H_Q \ne 0$; $\det H_Q = 2^{n}\,dV$ for O'Meara's discriminant $dV$, so for forms of
the same dimension the two conventions give the same square-class condition). At a finite spot $\mathfrak p$ the
Hasse symbol $S_\mathfrak p$ is the library's `NFPlace.hasseOMearaForm`, and at a real spot $w$ the negative index
$\operatorname{ind}^{-}$ is `LocalClassNF.realNegIndex`.

**Proves**
* Remark 66:5 (p. 189): `isometricIn_iff_invariants`, the complete set of invariants of a regular space over a number
  field: dimension, discriminant, the Hasse symbols at the discrete spots and the indices at the real spots;
* Corollary of 66:6 (p. 189): `finite_not_isotropicIn` — a regular space of dimension $n \ge 3$ is isotropic at almost
  all spots.
-/
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationGeneralNF
import QuadFormsKB.Tamagawa.FormClassNF
import QuadFormsKB.Literature.LocalGlobal.NumberFieldLocal

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **Remark 66:5** (O'Meara 1963, p. 189): two regular quadratic forms $Q$, $R$ in $n$ variables over a number field
$F$ are isometric over $F$ if and only if they have the same discriminant ($\det H_Q / \det H_R$ is a square in $F$),
the same Hasse symbol $S_\mathfrak p$ at every discrete spot $\mathfrak p$, and the same index at every real spot $w$.
O'Meara uses the positive index $\operatorname{ind}^{+}$; the library's real invariant is the negative index
$\operatorname{ind}^{-} = n - \operatorname{ind}^{+}$ (§61A), which carries the same information. The proof combines
the Hasse–Minkowski theorem 66:4 (`Tamagawa.FormClassNF.isometricIn_of_everywhere_nf`), the local classification
63:20 and 61:1 (`NFPlace.isometric_iff_general_hasseOMeara`), and the real and complex classifications (`LocalClassNF.isometric_real_iff_general`, `LocalClassNF.isometric_complex_general`).
-/
@[kb "omeara1963" "§66, 66:5, p. 189 (complete invariants: dim, d, S_𝔭 at discrete spots, indices at real spots)"]
theorem isometricIn_iff_invariants (Q R : QuadForm F n) (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.IsometricIn F R ↔ IsSquare (Q.hessian.det / R.hessian.det) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), (NFPlace.finite v).hasseOMearaForm Q = (NFPlace.finite v).hasseOMearaForm R) ∧
      ∀ (w : InfinitePlace F) (hw : w.IsReal), LocalClassNF.realNegIndex w hw Q = LocalClassNF.realNegIndex w hw R := by
  have hnegR : ∀ (w : InfinitePlace F) (hw : w.IsReal) (S : QuadForm F n),
      (NFPlace.infinite w).negIndexForm S = LocalClassNF.realNegIndex w hw S := by
    intro w hw S
    simp only [LocalClassNF.realNegIndex, NFPlace.negIndexForm, NFPlace.negIndex, hw, ↓reduceDIte]
  constructor
  · intro h
    have hloc : ∀ v : NFPlace F, v.atPlace (fun K _ _ => Q.IsometricIn K R) := by
      intro v
      cases v with
      | infinite w => exact FieldGen.isometricIn_of_base _ h
      | finite v => exact FieldGen.isometricIn_of_base _ h
    obtain ⟨s, hs, es⟩ := LocalClassNF.hessian_det_of_isometricIn h
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨1 / s, ?_⟩
      rw [es]
      have : Q.hessian.det ≠ 0 := hQ
      field_simp
    · intro v
      exact ((NFPlace.isometric_iff_general_hasseOMeara _ Q R hQ hR).mp (hloc (NFPlace.finite v))).2.1
    · intro w hw
      have := ((NFPlace.isometric_iff_general_hasseOMeara _ Q R hQ hR).mp (hloc (NFPlace.infinite w))).2.2
      rwa [hnegR w hw, hnegR w hw] at this
  · rintro ⟨hsq, hS, hI⟩
    apply Tamagawa.FormClassNF.isometricIn_of_everywhere_nf Q R hQ hR
    intro v
    cases v with
    | finite v =>
      rw [NFPlace.isometric_iff_general_hasseOMeara _ Q R hQ hR]
      refine ⟨?_, hS v, ?_⟩
      · obtain ⟨c, hc⟩ := hsq
        exact ⟨algebraMap F _ c, by rw [hc, map_mul]⟩
      · simp [NFPlace.negIndexForm, NFPlace.negIndex]
    | infinite w =>
      rcases InfinitePlace.isReal_or_isComplex w with hw | hw
      · exact (LocalClassNF.isometric_real_iff_general w hw Q R hQ hR).mpr (hI w hw)
      · exact LocalClassNF.isometric_complex_general w hw Q R hQ hR

/-- **A regular space of dimension $n \ge 3$ is isotropic at almost all spots** (O'Meara 1963, §66, p. 189, the
corollary of Example 66:6, through 63:14): the set of finite spots $\mathfrak p$ at which $Q$ is anisotropic over
$F_\mathfrak p$ is finite. -/
@[kb "omeara1963" "§66, p. 189 (corollary of 66:6: V_𝔭 is isotropic at almost all 𝔭 when n ≥ 3)"]
theorem finite_not_isotropicIn (Q : QuadForm F n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) :
    {v : HeightOneSpectrum (𝓞 F) | ¬ Q.IsotropicIn (v.adicCompletion F)}.Finite := by
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
  refine (NFLocal.finite_bad_places_nf n a ha).subset ?_
  intro v hv
  by_contra hcon
  simp only [Set.mem_ofPred_eq, not_or, not_exists, not_not] at hcon hv
  apply hv
  rw [FieldGen.isotropicIn_iff_of_isometricIn _ (FieldGen.isometricIn_of_base (v.adicCompletion F) hiso)]
  exact NFLocal.isotropic_diag_units_nf v hcon.1 n hn a hcon.2

end QuadFormsKB.OMeara
