import QuadFormsKB.Tamagawa.Measure.Weil.SplitSL1Final

/-!
# $\tau(SO(V)) = 2$ for every ternary form $\langle -a,-b,ab\rangle$ over every number field

The named input `TauSL1EqOne` of `PDSplitReduction.lean` is now a theorem for every quaternion algebra
(`tauSL1EqOne`: the residue computation for division algebras, `tamagawa_SL1_split` for $M_2(F)$),
so the conditional results become unconditional:

* **`covolume_muTamWeil_pureForm_unconditional`**: $\tau(SO(V)) = 2$ in Weil's normalization (`muTamWeil`);
* **`covolume_muTam_pureForm_unconditional`**: the covolume for `muTam` is $2$ (with Weil's complex normalization of
  `muTam`, i.e. the complex-place normalization of `muArchTamSO`).
-/

open MeasureTheory NumberField NumberField.InfinitePlace
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.QuatZeta QuadFormsKB.Siegel

variable {F : Type} [Field F] [NumberField F]

/-- **$\tau(SO(V)) = 2$ in Weil's normalization for every ternary form $\langle -a,-b,ab\rangle$, $a, b\in\mathcal O_F
\setminus 0$, over every number field**, unconditionally (split or division quaternion algebra, every signature). -/
@[kb "weil1982" "Thm 3.2.1, p. 43; §2.3, Thm 2.3.1; §3.7(a), p. 63; Thm 3.7.1 (m = 3), p. 65"]
theorem covolume_muTamWeil_pureForm_unconditional (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0) :
    covolume (GammaSOAdele (pureFormO a b)) (SOAdele (pureFormO a b))
      (muTamWeil (pureFormO a b) (nondegenerate_pureFormO a b ha hb)) = 2 :=
  covolume_muTamWeil_pureForm_of_tauSL1 a b ha hb (tauSL1EqOne a b)

/-- **The covolume of $SO(V)(F)$ for `muTam` is $2$** (with Weil's complex normalization of `muTam`) for every $\langle -a,-b,ab\rangle$, unconditionally. -/
@[kb "weil1982" "Thm 3.2.1, p. 43; §2.3, Thm 2.3.1; §3.7(a), p. 63"]
theorem covolume_muTam_pureForm_unconditional (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0) :
    covolume (GammaSOAdele (pureFormO a b)) (SOAdele (pureFormO a b))
        (muTam (pureFormO a b) (nondegenerate_pureFormO a b ha hb) fun _ => 1) =
      2 :=
  covolume_muTam_pureForm_of_tauSL1 a b ha hb (tauSL1EqOne a b)

end QuadFormsKB.Tamagawa.Measure.Weil
