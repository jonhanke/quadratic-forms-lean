/-
# Conway–Sloane 1988: citations for declarations elsewhere in the library

Declarations outside `Literature/ConwaySloane/Mass/` that state items of J. H. Conway and N. J. A. Sloane,
"Low-dimensional lattices. IV. The mass formula" (1988, `conwaysloane1988`) but carried no tag for it. The tags are added with `attribute [kb …]`, so the files where the
declarations live are unchanged. Each locator says how the declaration relates to the paper's item.
-/
import QuadFormsKB.Siegel.GenusFinite
import QuadFormsKB.Siegel.RankOne
import QuadFormsKB.Tamagawa.MassFormula
import QuadFormsKB.Literature.ConwaySloane.OddClassification
import QuadFormsKB.Literature.ConwaySloane.TwoAdicForm

/- (1): the mass of a genus, $\sum 1/\lvert\mathrm{Aut}(f^{(i)})\rvert$ over GL-classes. -/
attribute [kb "conwaysloane1988" "(1), p. 259 (GL-classes, all automorphisms)"] QuadFormsKB.Siegel.mass

/- §1, p. 259: the classes $f^{(1)}, \ldots, f^{(h)}$ of the genus; $h$ is finite for positive definite forms. -/
attribute [kb "conwaysloane1988" "§1, p. 259 (the classes of a genus)"] QuadFormsKB.Siegel.genusClasses
attribute [kb "conwaysloane1988" "§1, p. 259 (h is finite)"] QuadFormsKB.Siegel.genusFinite

/- (4): the $p$-adic Jordan decomposition, recorded by the symbols of *Sphere Packings, Lattices and Groups* Ch. 15. -/
attribute [kb "conwaysloane1988" "(4), p. 263 (Jordan decomposition, odd p, nonnegative exponents)"]
  QuadFormsKB.ConwaySloane.IsOddSymbolOf
attribute [kb "conwaysloane1988" "(4), p. 263 (Jordan decomposition, p = 2, nonnegative exponents)"]
  QuadFormsKB.ConwaySloane.IsTwoSymbolOf

/- §6, p. 266: in dimension 1 the mass is $\frac12$ (the initial 2 of (2) is to be replaced by 1). -/
attribute [kb "conwaysloane1988" "§6, p. 266 (dimension 1: mass 1/2)"] QuadFormsKB.Siegel.RankOne.mass_unary

/- §6, p. 266: $2m_p(f)$ is the proper $p$-mass; the factor 2 is $[O_n : SO_n]$ (number field lattices,
$L = \mathcal O_F^n$). -/
attribute [kb "conwaysloane1988" "§6, p. 266 (proper mass; number field generalization)"]
  QuadFormsKB.Tamagawa.mass_SO_eq_two_mul_mass
