import QuadFormsKB.Literature.Hanke2005.EqualMasses
import QuadFormsKB.Tamagawa.SiegelGenusV
import QuadFormsKB.Tamagawa.Measure.Weil.SpaceHeadlines
import QuadFormsKB.Tamagawa.Measure.LeraySlice
import QuadFormsKB.Literature.OMeara.Sec82

/-!
# Hanke 2005 (Crelle 584; 1999 thesis): citations for declarations formalized elsewhere

Some statements of the paper are formalized in the repository under another source or in another normalization and
had no citation tag yet. Their source tags are added here with
`attribute [kb …]`, so the files where the declarations live are unchanged. Locators refer to the 1999 thesis (as all
`hanke2005crelle` tags do, until the Crelle version is available).
-/

-- §1: quadratic space, lattices, localizations
attribute [kb "hanke2005crelle" "§1, pp. 1–2 (lattices Λ ⊂ V)"] QuadFormsKB.Tamagawa.SiegelSpace.LatV
attribute [kb "hanke2005crelle" "§1, p. 2 (Λ_p = Λ ⊗ O_p)"] QuadFormsKB.Tamagawa.SiegelSpace.locLatV
-- §1: the groups G^φ, G_v, G_A, G_a, G_h
attribute [kb "hanke2005crelle" "§1, p. 2 (G_A^φ, special orthogonal group of (V, φ))"]
  QuadFormsKB.Tamagawa.Measure.Weil.SOAdele
attribute [kb "hanke2005crelle" "§1, p. 2 (G_a, the archimedean part)"] QuadFormsKB.Tamagawa.Measure.Weil.GInfSO
attribute [kb "hanke2005crelle" "§1, p. 2 (G_h, the finite part)"] QuadFormsKB.Tamagawa.Measure.SOAf
-- §1: genus, classes, the stabilizer D, the double cosets
attribute [kb "hanke2005crelle" "§1, p. 2 (the genus: locally equivalent lattices)"]
  QuadFormsKB.Tamagawa.SiegelSpace.SameGenusV
attribute [kb "hanke2005crelle" "§1, p. 2 (D, the stabilizer of Λ in G_h)"] QuadFormsKB.Tamagawa.Measure.KSO
attribute [kb "hanke2005crelle" "§1, p. 2 (Cl ↔ G\\G_A/D, the proper classes in the genus)"]
  QuadFormsKB.Tamagawa.Indefinite.DC
attribute [kb "hanke2005crelle" "§1, p. 2 (representatives a of the classes)"] QuadFormsKB.Tamagawa.Indefinite.dcRep
attribute [kb "hanke2005crelle" "§1, p. 2 (Γ_a = G ∩ aDa⁻¹)"] QuadFormsKB.Tamagawa.Indefinite.unitGroup
-- §1, §5: maximal lattices
attribute [kb "hanke2005crelle" "§1, p. 2; §5, p. 16 (maximal and a-maximal lattices)"]
  QuadFormsKB.OMeara.IsMaximal
-- (2.1)–(2.4): the Tamagawa number and measure
attribute [kb "hanke2005crelle" "(2.1), p. 4 (τ(G) = 2 for n ≥ 3, cited)"]
  QuadFormsKB.Tamagawa.Measure.Weil.tauTwoAll_release_uncond
attribute [kb "hanke2005crelle" "(2.1), p. 4 (τ(G) = 2 for n ≥ 3, cited; quadratic spaces)"]
  QuadFormsKB.Tamagawa.Measure.Weil.tauTwo_space_uncond
attribute [kb "hanke2005crelle" "(2.2)–(2.3), p. 4 (the Tamagawa measure on G_A)"]
  QuadFormsKB.Tamagawa.Measure.Weil.muTam
attribute [kb "hanke2005crelle" "(2.3), p. 4 (τ(G) = vol(G\\G_A))"]
  QuadFormsKB.Tamagawa.Measure.Weil.TamagawaNumberTwoAdelic
attribute [kb "hanke2005crelle" "(2.4), p. 4 (the factor |D_k|^{-n(n-1)/4})"] QuadFormsKB.Tamagawa.Measure.cF
attribute [kb "hanke2005crelle" "(2.4), p. 4 (i dz ∧ dz̄ = 2 × Lebesgue at complex places)"]
  QuadFormsKB.Tamagawa.Measure.Weil.cxWeil
attribute [kb "hanke2005crelle" "(2.4), p. 4 (the archimedean measures |ω_G|'_v)"]
  QuadFormsKB.Tamagawa.Measure.Weil.muArchTamSO
-- (2.5)–(2.7): the form ω̃_G as a Leray (gauge-form) measure
attribute [kb "hanke2005crelle" "(2.5)–(2.7), p. 5 (ω̃_G on the fibre of x ↦ ᵗxψx, real places)"]
  QuadFormsKB.Tamagawa.Measure.LerayReal.lerayMeasure
attribute [kb "hanke2005crelle" "(2.5)–(2.7), p. 5 (ω̃_G on the fibre of x ↦ ᵗxψx, complex places)"]
  QuadFormsKB.Tamagawa.Measure.LerayComplex.lerayMeasureC
-- Lemma A6: the fibre measure
attribute [kb "hanke2005crelle" "Lemma A6, pp. 23–24 (the fibre volume form ω_C with ω ∧ F*ω_Y = ω_X)"]
  QuadFormsKB.Tamagawa.Measure.Leray.slice_decomposition
