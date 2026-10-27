/-
# O'Meara Chapter V: citations for declarations elsewhere in the library

Declarations outside `Literature/OMeara/` that state (special cases of) items of O'Meara's Chapter V (1973 printing)
but carried no O'Meara tag. The tags are added
here with `attribute [kb …]`, so the files where the declarations live are unchanged.

* 57:1 (p. 143): a quaternion $x$ is invertible iff $Nx \ne 0$, and then $x^{-1} = (Nx)^{-1}\bar x$:
  `Quat.isUnit_iff_nrd_ne_zero`, `Quat.inv_eq` (the reduced norm `Quat.nrd` is O'Meara's $N$).
* 57:9 (pp. 146–147), in the form with the Hilbert symbol: $(\alpha,\beta)$ is isotropic, resp. a division algebra,
  resp. $\cong M_2(F)$ according to the value of the Hilbert symbol (`Quat.hilbertSymbol_eq_one_iff_exists_nrd_eq_zero`,
  `Quat.hilbertSymbol_eq_neg_one_iff_division`, `Quat.nonempty_algEquiv_matrix_iff`); the book's form is
  `QuatIso57.tfae_division` (`Sec57Iso.lean`).
* 57:12 (p. 148), in coordinates on $F^3$: conjugation by an anisotropic pure quaternion is minus a symmetry
  (`Quat.conjLin_pureUnit`); the book's form is `Quaternions57.symmetry_pure_apply` (`Sec57.lean`).
* 58:2 (p. 151), local version: the Hasse symbol (the Hilbert-symbol product, whose Brauer class is that of
  O'Meara's Hasse algebra $SV$) of a diagonal form over a completion of a number field, resp. of $\mathbb Q$, is an
  isometry invariant (`NFPlace.hasseSerre_isometric`, `NFPlace.hasseOMeara_isometric`,
  `RatPlace.hasseOMeara_isometric`).
-/
import QuadFormsKB.Tamagawa.Quaternion
import QuadFormsKB.Tamagawa.QuaternionSO3
import QuadFormsKB.Literature.LocalGlobal.HasseIsometryNF
import QuadFormsKB.Literature.LocalGlobal.HasseConventions

namespace QuadFormsKB

attribute [kb "omeara1963" "§57A, 57:1, p. 143"] Quat.isUnit_iff_nrd_ne_zero
attribute [kb "omeara1963" "§57A, 57:1, p. 143 (x⁻¹ = (Nx)⁻¹ x̄)"] Quat.inv_eq
attribute [kb "omeara1963" "§57B, 57:9, p. 146 ((2) ⇔ (3), Hilbert symbol form)"]
  Quat.hilbertSymbol_eq_one_iff_exists_nrd_eq_zero
attribute [kb "omeara1963" "§57B, 57:9, p. 146 (division algebra, Hilbert symbol form)"]
  Quat.hilbertSymbol_eq_neg_one_iff_division
attribute [kb "omeara1963" "§57B, 57:9, p. 146 ((1) ⇔ (3), Hilbert symbol form)"] Quat.nonempty_algEquiv_matrix_iff
attribute [kb "omeara1963" "§57C, 57:12, p. 148 (in coordinates)"] Quat.conjLin_pureUnit
attribute [kb "omeara1963" "§58, 58:2, p. 151 (local Hilbert-symbol version)"] NFPlace.hasseSerre_isometric
attribute [kb "omeara1963" "§58, 58:2, p. 151 (local Hilbert-symbol version)"] NFPlace.hasseOMeara_isometric
attribute [kb "omeara1963" "§58, 58:2, p. 151 (local Hilbert-symbol version over ℚ)"] RatPlace.hasseOMeara_isometric

end QuadFormsKB
