/-
# Cassels, Chapters 11 and 12: further citations

Declarations that state items of Cassels' Chapter 11 (*Spinor genera*, pp. 196–254) and Chapter 12 (*The reduction of
positive definite quadratic forms*, pp. 255–283) but carried no Cassels tag for them. The tags are added here with `attribute [kb …]`, so the files where the
declarations live are unchanged. Each locator says how the declaration differs from the book's statement, where it does.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec1Forms
import QuadFormsKB.Literature.Cassels.Ch11Sec1
import QuadFormsKB.Literature.Cassels.Ch11Sec3Group
import QuadFormsKB.Literature.Cassels.Ch11Sec3Local
import QuadFormsKB.Literature.Cassels.Ch11Sec4Thm
import QuadFormsKB.Literature.Cassels.Ch11Sec4Local
import QuadFormsKB.Literature.Cassels.Ch11Sec7Lemma
import QuadFormsKB.Lattices.Steinitz
import QuadFormsKB.Lattices.Local
import QuadFormsKB.Lattices.KneserLocal
import QuadFormsKB.Lattices.FreeBridge
import QuadFormsKB.Lattices.SpinorGenusCount
import QuadFormsKB.Literature.Cassels.Ch12.Basic
import QuadFormsKB.Literature.Cassels.Ch12.SquareDecomp
import QuadFormsKB.Literature.Cassels.Ch12.Sec7

namespace QuadFormsKB

/-! ### Chapter 11 -/

-- 11.r3: the form of a basis; different bases give the forms equivalent (wide sense) to it
attribute [kb "cassels1978" "Ch. 11, §1, p. 196 (the form f(x) = φ(x₁a₁ + ⋯ + xₙaₙ) of a basis)"] Lattices.basisForm
attribute [kb "cassels1978" "Ch. 11, §1, p. 196 (the lattice of a form; free lattices over 𝓞_F)"] Lattices.latOf

-- 11.r6: forms in one genus are rationally equivalent, so they correspond to lattices in one space
attribute [kb "cassels1978" "Ch. 11, §1, p. 198 (forms of one genus give lattices in one space; over a number field)"]
  Lattices.Steinitz.exists_latOf_of_sameGenus
attribute [kb "cassels1978" "Ch. 11, §1, p. 198 (genus of a form versus genus of its lattice)"]
  Lattices.sameGenus_latOf_iff

-- 11.r8: the genus of lattices
attribute [kb "cassels1978" "Ch. 11, §1, (1.5)–(1.6), p. 199 (genus of lattices; full O(V_p), equivalent by Ch. 8, Lemma 3.2, Cor.)"]
  Lattices.SameGenus

-- 11:Thm 1.2 (b): the number of spinor genera is computable (it is the order of an explicit finite group)
attribute [kb "cassels1978" "Ch. 11, Thm. 1.2, p. 202 (spinor genera of a genus as an explicit group; effectivity via Thm. 3.1)"]
  Lattices.spinorGeneraEquivQuot

-- 11.r19: the set P; the conditions depend only on the genus
attribute [kb "cassels1978" "Ch. 11, §3, (3.6)–(3.7), p. 208 (θ(Λ_p) depends only on the genus, by Lemma 1.3)"]
  Lattices.localSpinorNormGroup_eq_of_sameGenus
attribute [kb "cassels1978" "Ch. 11, §3, (3.6)–(3.7), p. 208 (θ(Λ_p) = U_p(ℚ_p^×)² for unimodular Λ_p, p ∉ P)"]
  Lattices.mem_localSpinorNormGroup_iff_of_unimodular

-- 11.r20: the groups R, S, T and the diagonal map
attribute [kb "cassels1978" "Ch. 11, §3, (3.8)–(3.9), p. 208 (the group R)"] Lattices.CasselsR
attribute [kb "cassels1978" "Ch. 11, §3, (3.10), p. 208 (the subgroup S = ∏ θ(Λ_p))"] Lattices.casselsS
attribute [kb "cassels1978" "Ch. 11, §3, (3.12)–(3.13), p. 209 (the group T)"] Lattices.casselsT
attribute [kb "cassels1978" "Ch. 11, §3, (3.14), p. 209 (the diagonal map T → R)"] Lattices.casselsDiag
attribute [kb "cassels1978" "Ch. 11, §3, (3.11), p. 208 (R² ⊆ S)"] Lattices.sq_mem_casselsS

-- 11.r24: direct orthogonal summands: θ(Λ') ⊆ θ(Λ)
attribute [kb "cassels1978" "Ch. 11, §3, p. 213 (direct orthogonal summand Λ': θ(Λ') ⊆ θ(Λ))"]
  Lattices.units_mem_localSpinorNormGroup_of_orthogonal

-- 11.r26: the set P* of (4.4) (as hypotheses of the Theorem 4.1 declaration)
attribute [kb "cassels1978" "Ch. 11, §4, (4.4), p. 216 (the set P* of primes, as hypotheses)"]
  Lattices.sameProperSpinorGenus_latSMul_of_casselsI

-- 11.r28: the local index I(Λ^(p), Γ^(p))
attribute [kb "cassels1978" "Ch. 11, §4, pp. 218–219 (the local index I(Λ^(p), Γ^(p)), through the local lattices)"]
  Lattices.exists_hyperbolic_basis_of_casselsI

-- 11:Thm 5.1: simultaneous bases of Γ ⊆ Λ (Mathlib's Smith normal form; the divisibility s_j ∣ s_{j+1} is not part of it)
attribute [kb "cassels1978" "Ch. 11, Thm. 5.1, (5.3), p. 221 (over a principal ideal domain; without s_j ∣ s_{j+1})"]
  Submodule.exists_smith_normal_form_of_le

-- 11.p8: the substitutions (7.5)–(7.12) of the proof of Lemma 7.1
attribute [kb "cassels1978" "Ch. 11, proof of Lemma 7.1, (7.5)–(7.7), p. 229 (a hyperbolic pair in Λ_p)"]
  Lattices.exists_isotropic_qbil_eq_one
attribute [kb "cassels1978" "Ch. 11, proof of Lemma 7.1, (7.8)–(7.10), pp. 229–230 (scaling a primitive vector)"]
  Lattices.exists_locPrimitive_smul
attribute [kb "cassels1978" "Ch. 11, proof of Lemma 7.1, (7.11)–(7.12), p. 230 (the rotation scaling by p^{∓1})"]
  Lattices.spnRepresentsPrim_shift

-- 11.r48: Theorem 1.1 for Dedekind domains (Notes, p. 249)
attribute [kb "cassels1978" "Ch. 11, Notes, p. 249 (Thm. 1.1 over the ring of integers of a number field)"]
  Lattices.LocFamily.existsUnique_loc_eq

/-! ### Chapter 12 -/

-- 12.p1: only finitely many integral m have f(m) < M
attribute [kb "cassels1978" "Ch. 12, proof of Thm. 1.1, p. 256 (finitely many integral m with f(m) ≤ M)"]
  Reduction.finite_val_le

-- 12.r6: ⋃ T𝓡 is the set of positive definite forms
attribute [kb "cassels1978" "Ch. 12, §1, p. 257 (⋃_T T𝓡 is the set of positive definite forms)"] Reduction.thm_7_1

-- 12.r15: (1.9)
attribute [kb "cassels1978" "Ch. 12, §1, p. 260 (√f(x₁ + x₂) ≤ √f(x₁) + √f(x₂))"] Reduction.sqrt_val_add_le
attribute [kb "cassels1978" "Ch. 12, §1, (1.9), p. 260"] Reduction.sqrt_val_sum_le

-- 11.p9: the neighbour lattice of the proof of Thm. 8.4, Cor. 2 (Λ' = {c ∈ Λ : φ(2b, c) ≡ 0 mod 2} is `kerN` with
-- x = b, since φ(2b, c) ≡ 0 mod 2 iff φ(b, c) ∈ ℤ; Λ₁ = Λ' + ℤb is `nbr`)
attribute [kb "cassels1978" "Ch. 11, proof of Thm. 8.4, Cor. 2, p. 234 (the sublattice Λ'; over 𝓞_F)"]
  Lattices.KneserLocal.kerN
attribute [kb "cassels1978" "Ch. 11, proof of Thm. 8.4, Cor. 2, p. 234 (the neighbour Λ₁ generated by Λ' and b; over 𝓞_F)"]
  Lattices.KneserLocal.nbr

-- 12.p4, 12.p6, 12.p7: completing the square
attribute [kb "cassels1978" "Ch. 12, §2, (2.8), and §3, (3.1), pp. 262–263 (existence of the decomposition)"]
  Reduction.exists_isSqDecomp
attribute [kb "cassels1978" "Ch. 12, §3, (3.1), p. 263 (uniqueness of the decomposition)"] Reduction.IsSqDecomp.unique
attribute [kb "cassels1978" "Ch. 12, proof of Thm. 3.1 (iii), p. 265 (h₁ ⋯ hₙ = d(f))"] Reduction.IsSqDecomp.det_eq
attribute [kb "cassels1978" "Ch. 12, (3.4), p. 265 (f_ij = h_i c_ij + Σ_{k<i} h_k c_ki c_kj)"]
  Reduction.IsSqDecomp.offdiag_eq

-- 12.r35, 12.r36, 12.r37: the binary picture
attribute [kb "cassels1978" "Ch. 12, §6, p. 275 (T takes strictly definite forms to strictly definite forms; any n)"]
  Reduction.PosDef.act
attribute [kb "cassels1978" "Ch. 12, §6, p. 275 (fact (i): the T𝓕 cover the open disc; case n = 2)"] Reduction.thm_7_1
attribute [kb "cassels1978" "Ch. 12, §6, p. 275 (fact (ii): interior points; case n = 2)"] Reduction.thm_7_4

end QuadFormsKB
