/-
# Cassels, Chapters 7 and 8: citations for declarations elsewhere in the library

Declarations outside `Literature/Cassels/Ch7`, `Ch8` that state items of Cassels' Chapters 7 (*Quadratic forms over
integral domains*, pp. 102–110) and 8 (*Integral p-adic forms*, pp. 111–126) but carried no Cassels tag yet. The tags are added with `attribute [kb …]`, so the
files where the declarations live are unchanged. Each locator says how the declaration differs from Cassels' item.
-/
import QuadFormsKB.Lattices.FreeBridge
import QuadFormsKB.Lattices.Steinitz
import QuadFormsKB.Lattices.ClassSet
import QuadFormsKB.Lattices.UnimodularDVR
import QuadFormsKB.Literature.OMeara.Sec82Max

namespace QuadFormsKB

/-! ### Chapter 7 -/

-- 7.r1: the lattice with basis b₁, …, bₙ is {Σ rⱼbⱼ : rⱼ ∈ I}; `latOf γ` is the lattice with basis the columns of γ,
-- for I the ring of integers of a number field.
attribute [kb "cassels1978" "Ch. 7, §2, (2.1), p. 102 (the lattice with basis b₁, …, bₙ; I = 𝓞_F, basis the columns of γ)"]
  Lattices.latOf

-- 7.r5: Cassels' Notes, definition (ii): a finitely generated I-module spanning V (here: an 𝓞_F-lattice on Fⁿ), and the
-- Dedekind-domain substitute for a basis: Λ = {s₁b₁ + ⋯ + sₙbₙ : s₁, …, s_{n-1} ∈ I, sₙ ∈ J}.
attribute [kb "cassels1978" "Ch. 7, Notes, p. 109 (lattices in sense (ii): finitely generated, spanning V; I = 𝓞_F)"]
  Lattices.Lat
attribute [kb "cassels1978" "Ch. 7, Notes, p. 110 (Dedekind domain: Λ = Ib₁ + ⋯ + Ibₙ₋₁ + Jbₙ; I = 𝓞_F)"]
  Lattices.Steinitz.exists_eq_glImage_steinitzLat

/-! ### Chapter 8 -/

-- 8.r2: Cassels' Notes: the results for p ≠ 2 generalize to finite extensions of ℚ_p; the unimodular classification
-- over a complete discrete valuation ring with finite residue field of characteristic ≠ 2.
attribute [kb "cassels1978" "Ch. 8, Notes, p. 124 (generalization to finite extensions of ℚ_p, p ≠ 2: unimodular case)"]
  Lattices.Nbr.isometricGL_of_unimodular_dvr

-- Ch. 8, Ex. 7 (i): with the non-classical integrality (φ(c) ∈ ℤ_p for c ∈ Λ, i.e. nΛ ⊆ ℤ_p) every integral lattice
-- lies in a maximal one: O'Meara's 82:18 with 𝔞 = 𝔬 (stated for a Dedekind domain R, e.g. R = ℤ_p).
attribute [kb "cassels1978" "Ch. 8, Ex. 7 (i), p. 126 (non-classical maximal lattices exist; O'Meara 82:18 with 𝔞 = 𝔬)"]
  OMeara.Dedekind.exists_isMaximal_ge

end QuadFormsKB
