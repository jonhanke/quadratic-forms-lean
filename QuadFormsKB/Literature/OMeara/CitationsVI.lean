/-
# O'Meara Chapter VI: further citations

Declarations that formalize running-text claims of O'Meara's Chapter VI (1973 printing) which had no citation tag
yet. The tags are added here with `attribute [kb …]`, so the files where the declarations live are unchanged.
-/
import QuadFormsKB.Literature.OMeara.Sec65Main
import QuadFormsKB.Literature.HasseNorm.GoodPrimes
import QuadFormsKB.Defs.QuadForm

namespace QuadFormsKB

-- 65.r7: an idèle is a unit (square, ...) at 𝔭 if its 𝔭-component is; J_F^S consists of the idèles that are units at
-- all spots of S
attribute [kb "omeara1963" "§65A, p. 174 (J_F^S consists of the idèles that are units at all 𝔭 ∈ S)"]
  OMeara.sIdeles
attribute [kb "omeara1963" "§65A, p. 174 (J^{S,2}: idèles that are squares at all 𝔭 ∈ Ω − S and units on S)"]
  OMeara.sqSIdeles

-- 65.r11: θ a non-square, E = F(√θ) quadratic, conjugation with Galois group {1, conjugation}
attribute [kb "omeara1963" "§65A, pp. 174–175 (E = F(√θ) is quadratic, with conjugation σ, σ(√θ) = −√θ)"]
  HN.quadData
attribute [kb "omeara1963" "§65A, p. 174 (E = F(√θ): every element is β₀ + β₁√θ)"]
  OMeara.exists_eq_add_mul_sqrt

-- 66.r2: V is isotropic at 𝔭 if V_𝔭 is; U and V are isometric at 𝔭 if U_𝔭 ≅ V_𝔭 (with K a completion F_𝔭)
attribute [kb "omeara1963" "§66, p. 186 (V is isotropic at 𝔭 if V_𝔭 is; K = F_𝔭)"]
  QuadForm.IsotropicIn
attribute [kb "omeara1963" "§66, p. 186 (U and V are isometric at 𝔭 if U_𝔭 ≅ V_𝔭; K = F_𝔭)"]
  QuadForm.IsometricIn

end QuadFormsKB
