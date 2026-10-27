/-
# The norm-one measures of representations do not depend on the choices

**Layer:** number fields. $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $N = r + 2$ variables (any signature),
$T_0$ nondegenerate of rank $r$, $\Xi$ a rational frame of $T_0$ ($Q_0\circ\Xi = T_0$) whose complement $\Xi^\perp$ is isotropic.
The regularized measure of representations $\rho^1(M_i, T_0)$ (`repMeasureIso`) is defined with chosen algebraic frame
data
(`isoTower`) and a chosen isotropic vector of the complement form (`isoVec`); `repMeasureIsoOf D hv` is the same quantity for
arbitrary frame data `D : FrameTowerAlg Q₀ hQ 2 (cols Ξ.1)` and an arbitrary isotropic vector $v$ of $Q''_D$.

**Proves** (unconditional)
* **`repMeasureIsoOf_indep`**: `repMeasureIsoOf D hv i = repMeasureIsoOf D' hv' i` for all frame data $D, D'$ and isotropic
  vectors $v, v'$, class by class, every $r$;
* **`repMeasureIso_eq_repMeasureIsoOf`**: the `repMeasureIso` equals `repMeasureIsoOf D hv` for every choice;
* `isSquare_deltaForms_of_isIsoVec`: an isotropic vector of a complement form forces the hypothesis
  ($-\det H_{Q_0}\det H_{T_0}$ a square);
* **`repMeasureOf_unary_isoShellFrameOf`** ($r = 1$, ternary $Q_0$, $T_0 = \langle m\rangle$): the shell covolumes left open
  earlier — with the stabilizer measures of `archFibrationNF` restricted to the norm-one shell of **any** $(D, v)$,
  the sum
  over the representations is the same as with the original shell.

*Proof.* `repMeasureIsoOf_frameChange` (a change of frame data only changes the isotropic vector: $v'\mapsto Rv'$) and
`repMeasureIsoOf_isoTower_vec` (for the frame data the isotropic vector does not matter: the same line gives the same
character,
the other line the inverse character, and the two shells $\{0\le\log|\chi|_\infty<1\}$, $\{-1<\log|\chi|_\infty\le0\}$ have the same
covolume because the arithmetic stabilizers lie in $\ker|\chi|_\infty$).
-/
import QuadFormsKB.Tamagawa.Indefinite.IsoIndepFrame

open MeasureTheory Measure Set MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity

section General

variable {F : Type} [Field F] [NumberField F] {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 2)) (hQ : Q₀.Nondegenerate)
  (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀)

include hT in
/-- An isotropic vector of the complement form of any frame data makes the complement isotropic:
$\delta = -\det H_{Q_0}\det H_{T_0}$ (`deltaForms`) is a square in $F$. -/
theorem isSquare_deltaForms_of_isIsoVec (D : FrameTowerAlg Q₀ hQ 2 (cols Ξ.1)) {v : Fin 2 → F}
    (hv : IsIsoVec D.Q'' v) : IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀)) := by
  by_contra h
  have hA := (anisotropicF_adapted_iff Q₀ T₀ hT (IsoAlg.towerAdapted Q₀ hQ T₀ Ξ D hT)).2 h
  exact (isotropicF_iff_not_anisotropicF D.Q'').1 ⟨v, hv⟩ hA

/-- `repMeasureIsoOf D hv` is the `repMeasureIso` (for the hypothesis supplied by $v$). -/
theorem repMeasureIsoOf_eq_repMeasureIso (D : FrameTowerAlg Q₀ hQ 2 (cols Ξ.1)) {v : Fin 2 → F}
    (hv : IsIsoVec D.Q'' v) (i : DC Q₀) :
    repMeasureIsoOf Q₀ hQ T₀ hT Ξ D hv i =
      repMeasureIso Q₀ hQ T₀ hT (isSquare_deltaForms_of_isIsoVec Q₀ hQ T₀ hT Ξ D hv) Ξ i := by
  rw [repMeasureIsoOf_frameChange Q₀ hQ T₀ hT Ξ (isoTower Q₀ hQ T₀ hT Ξ) D hv i]
  exact repMeasureIsoOf_isoTower_vec Q₀ hQ T₀ hT (isSquare_deltaForms_of_isIsoVec Q₀ hQ T₀ hT Ξ D hv) Ξ _ i

/-- **The norm-one measures of representations do not depend on the choices.** Let $F$ be a number field, $Q_0$ a
nondegenerate quadratic form over $\mathcal O_F$ in $N = r + 2$ variables (any signature), $T_0$ a nondegenerate form of rank
$r$, $\Xi$ a rational frame of $T_0$ by $Q_0$, `D`, `D'` any two algebraic frame data of $\Xi$ (complement forms $Q''_D$,
$Q''_{D'}$ in $2$ variables) and $v$, $v'$ isotropic vectors of $Q''_D$, $Q''_{D'}$. Then for every class $i$,
$$\rho^1_{D,v}(M_i, T_0) = \rho^1_{D',v'}(M_i, T_0),$$
where $\rho^1_{D,v}(M_i,T_0) = \sum_{X\in\Gamma_i\backslash R(M_i,T_0)}\operatorname{vol}(\Gamma_{i,X}\backslash H^1_X)$ is computed with the
stabilizer measure $\lambda_D\,\mu^{\mathrm{Tam}}_{Q''_D}$ restricted to the shell $\{0\le\log|\chi_v|_\infty<1\}$
(`repMeasureIsoOf`). Parameters: `Q₀`, `hQ`, `T₀`, `hT`, `Ξ`, `D`, `D'`, `v`, `v'`, `hv`, `hv'`, `i`. -/
@[kb "siegel1944indef" "On the theory of indefinite quadratic forms (the excluded case, regularized: independence of the frame data and of the isotropic line) [unverified]"]
theorem repMeasureIsoOf_indep (D D' : FrameTowerAlg Q₀ hQ 2 (cols Ξ.1)) {v v' : Fin 2 → F}
    (hv : IsIsoVec D.Q'' v) (hv' : IsIsoVec D'.Q'' v') (i : DC Q₀) :
    repMeasureIsoOf Q₀ hQ T₀ hT Ξ D hv i = repMeasureIsoOf Q₀ hQ T₀ hT Ξ D' hv' i := by
  rw [repMeasureIsoOf_eq_repMeasureIso Q₀ hQ T₀ hT Ξ D hv i, repMeasureIsoOf_eq_repMeasureIso Q₀ hQ T₀ hT Ξ D' hv' i]

/-- **`repMeasureIso` is `repMeasureIsoOf` for any choice**: for every algebraic frame data `D` of $\Xi$ and every
isotropic vector $v$ of $Q''_D$, the regularized measure of representations $\rho^1(M_i,T_0)$ (defined with the chosen
`isoTower`, `isoVec`) equals `repMeasureIsoOf D hv i`. Parameters: `Q₀`, `hQ`, `T₀`, `hT`, `hiso`, `Ξ`, `D`, `v`, `hv`, `i`. -/
@[kb "siegel1944indef" "On the theory of indefinite quadratic forms (the excluded case, regularized: any frame data and isotropic line) [unverified]"]
theorem repMeasureIso_eq_repMeasureIsoOf (hiso : IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀)))
    (D : FrameTowerAlg Q₀ hQ 2 (cols Ξ.1)) {v : Fin 2 → F} (hv : IsIsoVec D.Q'' v) (i : DC Q₀) :
    repMeasureIso Q₀ hQ T₀ hT hiso Ξ i = repMeasureIsoOf Q₀ hQ T₀ hT Ξ D hv i :=
  (repMeasureIsoOf_eq_repMeasureIso Q₀ hQ T₀ hT Ξ D hv i).symm

end General

/-! ### Ternary forms: the shell covolumes -/

section Ternary

variable {F : Type} [Field F] [NumberField F] (Q₀ : QuadForm (𝓞 F) (1 + 2)) (hQ : Q₀.Nondegenerate) {m : 𝓞 F}
  (hm : (m : F) ≠ 0) (hiso : IsSquare (-(2 * (m : F) * algebraMap (𝓞 F) F Q₀.hessian.det)))
  (ξ : RatSphere Q₀ (m : F))

/-- **The shell covolumes at $r = 1$** (ternary $Q_0$, $T_0 = \langle m\rangle$, $m^\perp$ isotropic): for **every** algebraic
frame data `D` of the $1$-frame of $\xi$ and every isotropic vector $v$ of $Q''_D$, the stabilizer measures
(`archFibrationNF`, independent of all choices) restricted to the norm-one shell of $(D, v)$ give the same measure of
representations, class by class, as with the original shell. Together with `isoStabMeasureOf_unary_eq` this is the full
independence at $r = 1$ in the sphere normalization. Parameters: `Q₀`, `hQ`, `m`, `hm`, `hiso`, `ξ`, `D`, `v`, `hv`,
`i`. -/
@[kb "siegel1944indef" "On the theory of indefinite quadratic forms (ternary, excluded case; norm-one shells of any frame data and isotropic line) [unverified]"]
theorem repMeasureOf_unary_isoShellFrameOf (D : FrameTowerAlg Q₀ hQ 2 (cols (ternFrame Q₀ ξ).1)) {v : Fin 2 → F}
    (hv : IsIsoVec D.Q'' v) (i : DC Q₀) :
    repMeasureOf (unitGroup Q₀ i) (repsT Q₀ (DVR.unary m) i) (fun X =>
        (((archFibrationNF (k := 2) Q₀ hQ hm (by norm_num)).μH (X 0)).map (stabFrameVecME X).symm).restrict
          (isoShellFrameOf Q₀ hQ (DVR.unary m) (ternFrame Q₀ ξ) D hv X)) =
      repMeasureOf (unitGroup Q₀ i) (repsT Q₀ (DVR.unary m) i) (fun X =>
        (((archFibrationNF (k := 2) Q₀ hQ hm (by norm_num)).μH (X 0)).map (stabFrameVecME X).symm).restrict
          (isoShellFrame Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (isSquare_deltaForms_unary hiso)
            (ternFrame Q₀ ξ) X)) := by
  have h1 : repMeasureOf (unitGroup Q₀ i) (repsT Q₀ (DVR.unary m) i) (fun X =>
        (((archFibrationNF (k := 2) Q₀ hQ hm (by norm_num)).μH (X 0)).map (stabFrameVecME X).symm).restrict
          (isoShellFrameOf Q₀ hQ (DVR.unary m) (ternFrame Q₀ ξ) D hv X)) =
      repMeasureIsoOf Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (ternFrame Q₀ ξ) D hv i := by
    unfold repMeasureIsoOf repMeasureOf
    refine tsum_congr fun q => ?_
    congr 1
    refine (isoStabMeasureOf_unary_eq Q₀ hQ hm ξ D hv _ ?_).symm
    obtain ⟨Ξ', hΞ'⟩ := exists_ratFrame_of_mem_repsT Q₀ m i (q.out : repsT Q₀ (DVR.unary m) i)
    obtain ⟨γ, hγ⟩ := FrameTowerAlg.exists_smul_eq_ratFrame Q₀ hQ (DVR.unary m) (ternFrame Q₀ ξ) D
      (unary_nondegenerate hm) (by norm_num) Ξ'
    exact ⟨(γ : SOAdele Q₀).1, by rw [← hΞ', ← hγ, ratAT_smul]⟩
  rw [h1, repMeasureIsoOf_eq_repMeasureIso]
  exact repMeasureIso_unary_eq Q₀ hQ hm hiso ξ i

end Ternary

end QuadFormsKB.Tamagawa.Indefinite
