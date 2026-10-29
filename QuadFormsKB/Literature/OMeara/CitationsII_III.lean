/-
# O'Meara Chapters II and III: citations for declarations elsewhere

Tags for earlier declarations that state (special cases of) items of §21-§33:
* 31:2 for $\mathbb Z \subset \mathbb Q$: `OMeara.rat_dedekindAxioms` (proved with 21:1);
* 32:5: the residue field of a completion has $N\mathfrak p$ elements and $|\mathcal O_v/\varpi^n| = (N\mathfrak p)^n$:
  `HN.card_residueField`, `HN.card_quot_ϖ_pow`.
-/
import QuadFormsKB.Literature.OMeara.Sec21
import QuadFormsKB.Literature.HasseNorm.SquareClasses

attribute [kb "omeara1963" "§31, 31:2, p. 57 (rational number field case)"]
  QuadFormsKB.OMeara.rat_dedekindAxioms

attribute [kb "omeara1963" "§32A, 32:5, p. 60 (the residue field has Np elements; number field completion)"]
  QuadFormsKB.HN.card_residueField

attribute [kb "omeara1963" "§32A, 32:5, p. 60 ((o : p^ν) = (Np)^ν; number field completion)"]
  QuadFormsKB.HN.card_quot_ϖ_pow
