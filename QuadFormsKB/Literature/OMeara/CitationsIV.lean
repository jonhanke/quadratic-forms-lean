import QuadFormsKB.Literature.OMeara.Sec91Jordan
import QuadFormsKB.Literature.OMeara.Sec92Class
import QuadFormsKB.Literature.OMeara.Sec55
import QuadFormsKB.Literature.OMeara.Sec82Radical

/-!
# O'Meara Chapter IV: citations for declarations elsewhere in the library

Declarations in other files that state items of O'Meara's Chapter IV (1973 printing) but carried no tag with the
item number. The tags are added here with `attribute [kb …]`, so the files where the declarations live are unchanged.

* 41:3 (p. 87), the matrix part: `gram_smul` (`Sec92Class.lean`): the scaled space $V^a$ (the form $aQ$) has the
  matrix $aN$ in a family in which $V$ has the matrix $N$. The discriminant part is `det_gram_smul` (`Sec41.lean`).
* 41:4 (p. 87): `linearIndependent_of_det_gram_ne_zero` (`Sec91Jordan.lean`), vectors with non-zero discriminant are
  independent; stated over a ring $R$ with $R \to F$, the book's statement is the case $R = F$.
* 42:8 (2) (p. 93): `isometricLat_iff_of_radical` (`Sec82Radical.lean`), two lattices with radical splittings
  $L = K \perp \operatorname{rad} L$ are isometric iff the regular parts and the radicals are; the book's statement for
  spaces is the case $R = F$, $L = V$ (checked to instantiate with `R := F`, `L := ⊤`).
* 42:15 (p. 97): `hyperbolic_symmetry_form` (every symmetry $\tau$ of a hyperbolic plane $Fx + Fy$ has
  $\tau x = \alpha y$, $\tau y = \alpha^{-1}x$), `hyperbolic_symmetry` ($\tau_{x - \alpha y}x = \alpha y$,
  $\tau_{x-\alpha y}y = \alpha^{-1}x$) and `hyperbolic_rotation` ($\tau_{x-y}\tau_{x-\alpha y}$ is the rotation
  $x \mapsto \alpha x$, $y \mapsto \alpha^{-1}y$), all in `Sec55.lean` (tagged there as 55:1, which repeats 42:15).
-/

namespace QuadFormsKB.OMeara

attribute [kb "omeara1963" "§41B, 41:3, p. 87 (V^a ≅ aN)"] gram_smul
attribute [kb "omeara1963" "§41B, 41:4, p. 87"] linearIndependent_of_det_gram_ne_zero
attribute [kb "omeara1963" "§42C, 42:8 (2), p. 93 (lattice version; spaces are R = F, L = V)"]
  isometricLat_iff_of_radical
attribute [kb "omeara1963" "§42E, 42:15, p. 97 (every symmetry of H interchanges the isotropic lines)"]
  hyperbolic_symmetry_form
attribute [kb "omeara1963" "§42E, 42:15, p. 97 (τ_{x−αy}: x ↦ αy, y ↦ α⁻¹x)"] hyperbolic_symmetry
attribute [kb "omeara1963" "§42E, 42:15, p. 97 (σ = τ_{x−y}τ_{x−αy}: x ↦ αx, y ↦ α⁻¹y)"] hyperbolic_rotation

end QuadFormsKB.OMeara
