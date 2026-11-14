/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch5Stabilization
import Mathlib.Topology.Sequences
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Kitaoka, Corollary 5.4.4: a symmetric matrix close to $A$ is equivalent to $A$

**Source.** Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.4, Corollary 5.4.4, printed p. 91.

**Book statement.** Let $R = \mathbb Z_p$ and $F = \mathbb Q_p$. Let $A = {}^tA \in \mathrm{GL}_n(F)$ and let $h$ be an
integer with $p^hA^{-1} \in M_n(R)$ and with all diagonal entries of $p^hA^{-1}$ in $2R$. If
$B = {}^tB \in M_n(F)$ satisfies $B \equiv A \bmod p^{h+1}M_n(R)$ and all diagonal entries of $B - A$ lie in
$2p^{h+1}R$, then there is $U \in \mathrm{GL}_n(R)$ with $B = A[U] = {}^tUAU$ and
$U \equiv 1_n \bmod p^{h+1}A^{-1}M_n(R)$.

**Integral formulation (what is proved here).** Write $A' = p^hA^{-1}$.  The hypothesis on $A'$ says
$AA' = p^h1$ and $A' \in E_m$ (symmetric with even diagonal, `ModE p 0 A'`).  The hypothesis on $B$ says
$B - A \in p^{h+1}E_m$ (`ModE p (h + 1) (B - A)`), by `modE_iff_dvd` for the symmetric matrix $B - A$.  The conclusion
$U \equiv 1 \bmod p^{h+1}A^{-1}M_n(R)$ says $U = 1 + p\,A'Z$ for some $Z \in M_n(R)$, since
$p^{h+1}A^{-1} = pA'$.  We state the result for $A, B$ with entries in $\mathbb Z_p$.  The general case reduces to
this one: for $A, B$ over $\mathbb Q_p$ with $p^hA^{-1}$ integral, replace $(A, B)$ by $(p^sA, p^sB)$ with $s$ large
enough that both are integral, and $h$ by $h + s$.  Then $(p^sA)^{-1} = p^{-s}A^{-1}$, so $p^{h+s}(p^sA)^{-1} = p^hA^{-1}$
is unchanged, the hypotheses on $B - A$ are preserved (they scale by $p^s$ along with the modulus $p^{h+s+1}$), the
module $p^{h+1}A^{-1}M_n(R)$ is unchanged, and the relation $B = {}^tUAU$ is invariant under scaling.

**Proof (Newton iteration; not Kitaoka's proof).**  Put $U(Z) = 1 + pA'Z$; this is invertible for every $Z$, since
$\det U(Z) \equiv 1 \bmod p$.  Say $Z$ is *good at level $k$* if $B - {}^tU(Z)AU(Z) \in p^{h+1+k}E_m$.
`Z = 0` is good at level $0$ by hypothesis.  *Step* (`exists_next`): if $Z$ is good at level $k$, write
$B - A_k = p^{h+1+k}(F + {}^tF)$ for $A_k = {}^tUAU$ and $U = U(Z)$.  Then $A_k A'_k = p^h1$ with
$A'_k = U^{-1}A'\,{}^t(U^{-1}) \in E_m$.  With $V = 1 + p^{k+1}A'_kF$ one computes
${}^tVA_kV = A_k + p^{h+1+k}(F + {}^tF) + p^{h+2+2k+1}\,{}^tFA'_kF$ (`hensel_explicit`), so
$B - {}^t(UV)A(UV) \in p^{h+2+k}E_m$; and $UV = U(Z')$ with $Z' = Z + p^k\,{}^t(U^{-1})F$.  Choosing such $Z_k$ for
every $k$ and, by compactness of $M_m(\mathbb Z_p)$, a convergent subsequence with limit $Z$, continuity gives
$B = {}^tU(Z)AU(Z)$, because the entries of $B - {}^tU(Z_k)AU(Z_k)$ tend to $0$.  Finally $U(Z)$ is invertible.

The statement is unconditional: it assumes no unproved input.
-/

open Matrix Filter Topology

noncomputable section

namespace QuadFormsKB.Kitaoka.Density

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

namespace Cor544

/-- The matrix $U(Z) = 1 + p\,A'Z$. -/
def uOf (A' Z : Matrix (Fin m) (Fin m) ℤ_[p]) : Matrix (Fin m) (Fin m) ℤ_[p] :=
  1 + (p : ℤ_[p]) • (A' * Z)

/-- $\det(1 + pM)$ is a unit of $\mathbb Z_p$, since it is congruent to $1$ modulo $p$. -/
theorem isUnit_det_one_add_smul (M : Matrix (Fin m) (Fin m) ℤ_[p]) :
    IsUnit (1 + (p : ℤ_[p]) • M).det := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, RingHom.map_det]
  have : (PadicInt.toZMod : ℤ_[p] →+* ZMod p).mapMatrix (1 + (p : ℤ_[p]) • M) = 1 := by
    ext i j
    simp [Matrix.one_apply, apply_ite]
  rw [this, det_one]
  exact one_ne_zero

/-- Entries of an element of $p^kE_m$ have norm at most $\|p\|^k$. -/
theorem norm_le_of_modE {k : ℕ} {D : Matrix (Fin m) (Fin m) ℤ_[p]} (hD : ModE p k D) (i j : Fin m) :
    ‖D i j‖ ≤ ‖(p : ℤ_[p])‖ ^ k := by
  obtain ⟨F, rfl⟩ := hD
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)

/-- **One Hensel step with explicit correction.**  Let $T$ be symmetric with $TA = p^h1$ and $A \in E_m$.  Then for
$V = 1 + p^{k+1}AF$ we have $T[V] \equiv T + p^{h+1+k}(F + F^{\mathsf T}) \bmod p^{h+2+k}E_m$. -/
theorem hensel_explicit {T A : Matrix (Fin m) (Fin m) ℤ_[p]} (hT : Tᵀ = T) {h : ℕ}
    (hA : T * A = (p : ℤ_[p]) ^ h • 1) (hAE : ModE p 0 A) (k : ℕ) (F : Matrix (Fin m) (Fin m) ℤ_[p]) :
    ModE p (h + 1 + k + 1)
      ((1 + (p : ℤ_[p]) ^ (k + 1) • (A * F))ᵀ * T * (1 + (p : ℤ_[p]) ^ (k + 1) • (A * F)) -
        (T + (p : ℤ_[p]) ^ (h + 1 + k) • (F + Fᵀ))) := by
  obtain ⟨G, hG⟩ := hAE
  rw [pow_zero, one_smul] at hG
  have hAs : Aᵀ = A := by rw [hG]; simp [add_comm]
  have hAT : A * T = (p : ℤ_[p]) ^ h • 1 := by
    have := congrArg transpose hA
    rwa [transpose_mul, hT, hAs, transpose_smul, transpose_one] at this
  have hTA' : ∀ X : Matrix (Fin m) (Fin m) ℤ_[p], T * (A * X) = (p : ℤ_[p]) ^ h • X := fun X => by
    rw [← Matrix.mul_assoc, hA, Matrix.smul_mul, Matrix.one_mul]
  set U : Matrix (Fin m) (Fin m) ℤ_[p] := 1 + (p : ℤ_[p]) ^ (k + 1) • (A * F) with hU
  refine ⟨(p : ℤ_[p]) ^ k • (Fᵀ * (G * F)), ?_⟩
  have hTU : Uᵀ * T * U = T + (p : ℤ_[p]) ^ (h + 1 + k) • (F + Fᵀ) +
      (p : ℤ_[p]) ^ (h + 1 + k + 1) • ((p : ℤ_[p]) ^ k • (Fᵀ * (A * F))) := by
    have e1 : Uᵀ = 1 + (p : ℤ_[p]) ^ (k + 1) • (Fᵀ * A) := by
      simp [U, transpose_mul, hAs]
    rw [e1]
    simp only [U, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc, hTA']
    rw [hAT]
    simp only [Matrix.mul_smul, Matrix.mul_one, smul_add, smul_smul]
    module
  rw [hTU, hG]
  simp only [transpose_mul, transpose_transpose, transpose_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, smul_add]
  module

/-- **The Newton step.**  If $Z$ is good at level $k$, some $Z'$ is good at level $k + 1$. -/
theorem exists_next {A A' B : Matrix (Fin m) (Fin m) ℤ_[p]} (hA : Aᵀ = A) {h : ℕ}
    (hAA' : A * A' = (p : ℤ_[p]) ^ h • 1) (hA'E : ModE p 0 A') {k : ℕ} {Z : Matrix (Fin m) (Fin m) ℤ_[p]}
    (hP : ModE p (h + 1 + k) (B - (uOf A' Z)ᵀ * A * uOf A' Z)) :
    ∃ Z' : Matrix (Fin m) (Fin m) ℤ_[p],
      ModE p (h + 1 + (k + 1)) (B - (uOf A' Z')ᵀ * A * uOf A' Z') := by
  have hdet : IsUnit (uOf A' Z).det := isUnit_det_one_add_smul _
  set U := uOf A' Z with hUdef
  set W := U⁻¹ with hW
  have hUW : U * W = 1 := mul_nonsing_inv _ hdet
  have hWU : W * U = 1 := nonsing_inv_mul _ hdet
  have hT : (Uᵀ * A * U)ᵀ = Uᵀ * A * U := by
    simp [transpose_mul, hA, Matrix.mul_assoc]
  have hUtWt : Uᵀ * Wᵀ = 1 := by rw [← transpose_mul, hWU, transpose_one]
  have hTA : (Uᵀ * A * U) * (W * A' * Wᵀ) = (p : ℤ_[p]) ^ h • 1 := by
    calc (Uᵀ * A * U) * (W * A' * Wᵀ) = Uᵀ * (A * ((U * W) * A')) * Wᵀ := by
          simp only [Matrix.mul_assoc]
      _ = (p : ℤ_[p]) ^ h • 1 := by
          rw [hUW, Matrix.one_mul, hAA']
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUtWt]
  have hAkE : ModE p 0 (W * A' * Wᵀ) := by
    have := hA'E.conj Wᵀ
    rwa [transpose_transpose] at this
  obtain ⟨F, hF⟩ := hP
  have H := hensel_explicit hT hTA hAkE k F
  set V := 1 + (p : ℤ_[p]) ^ (k + 1) • ((W * A' * Wᵀ) * F) with hV
  refine ⟨Z + (p : ℤ_[p]) ^ k • (Wᵀ * F), ?_⟩
  have hUA : U * (W * A' * Wᵀ) = A' * Wᵀ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hUW, Matrix.one_mul]
  have hUV : uOf A' (Z + (p : ℤ_[p]) ^ k • (Wᵀ * F)) = U * V := by
    have h1 : U * V = U + (p : ℤ_[p]) ^ (k + 1) • (A' * Wᵀ * F) := by
      rw [hV, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc U, hUA]
    rw [h1, hUdef]
    simp only [uOf, Matrix.mul_add, Matrix.mul_smul, smul_add, smul_smul, pow_succ, Matrix.mul_assoc]
    rw [add_assoc]
    congr 2
    rw [mul_comm (p : ℤ_[p]) ((p : ℤ_[p]) ^ k)]
  rw [hUV]
  have e1 : (U * V)ᵀ * A * (U * V) = Vᵀ * (Uᵀ * A * U) * V := by
    simp only [transpose_mul, Matrix.mul_assoc]
  have hF' : B = Uᵀ * A * U + (p : ℤ_[p]) ^ (h + 1 + k) • (F + Fᵀ) := (sub_eq_iff_eq_add'.1 hF)
  have e2 : B - (U * V)ᵀ * A * (U * V) = -(Vᵀ * (Uᵀ * A * U) * V -
      (Uᵀ * A * U + (p : ℤ_[p]) ^ (h + 1 + k) • (F + Fᵀ))) := by
    rw [e1, neg_sub, ← hF']
  rw [e2]
  exact H.neg

end Cor544

open Cor544 in
/-- **Kitaoka, Corollary 5.4.4** (integral formulation; see the module docstring).  Let $A, B$ be symmetric
over $\mathbb Z_p$ and $A' = p^hA^{-1}$, i.e. $AA' = p^h1$, with $A' \in E_m$.  If $B - A \in p^{h+1}E_m$ then there is
an invertible $U$ with ${}^tUAU = B$ and $U = 1 + pA'Z$ for some $Z$, i.e. $U \equiv 1 \bmod p^{h+1}A^{-1}M_m$. -/
@[kb "kitaoka1993" "§5.4, Cor. 5.4.4, p. 91"]
theorem corollary544 {A A' B : Matrix (Fin m) (Fin m) ℤ_[p]} (hA : Aᵀ = A) (hB : Bᵀ = B) {h : ℕ}
    (hAA' : A * A' = (p : ℤ_[p]) ^ h • 1) (hA'E : ModE p 0 A') (hBA : ModE p (h + 1) (B - A)) :
    ∃ U : Matrix (Fin m) (Fin m) ℤ_[p], IsUnit U ∧ Uᵀ * A * U = B ∧
      ∃ Z : Matrix (Fin m) (Fin m) ℤ_[p], U = 1 + (p : ℤ_[p]) • (A' * Z) := by
  have _ := hB
  choose! f hf using fun (k : ℕ) (Z : Matrix (Fin m) (Fin m) ℤ_[p]) (hP : ModE p (h + 1 + k)
    (B - (uOf A' Z)ᵀ * A * uOf A' Z)) => exists_next (B := B) hA hAA' hA'E hP
  let Zs : ℕ → Matrix (Fin m) (Fin m) ℤ_[p] := fun k => Nat.rec 0 (fun k Z => f k Z) k
  have hZ : ∀ k, ModE p (h + 1 + k) (B - (uOf A' (Zs k))ᵀ * A * uOf A' (Zs k)) := by
    intro k
    induction k with
    | zero =>
      have : uOf A' (0 : Matrix (Fin m) (Fin m) ℤ_[p]) = 1 := by simp [uOf]
      show ModE p (h + 1 + 0) (B - (uOf A' 0)ᵀ * A * uOf A' 0)
      rw [this]
      simpa using hBA
    | succ k ih => exact hf k (Zs k) ih
  have : FirstCountableTopology (Matrix (Fin m) (Fin m) ℤ_[p]) :=
    inferInstanceAs (FirstCountableTopology (Fin m → Fin m → ℤ_[p]))
  have : CompactSpace (Matrix (Fin m) (Fin m) ℤ_[p]) :=
    inferInstanceAs (CompactSpace (Fin m → Fin m → ℤ_[p]))
  obtain ⟨Zl, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq Zs
  have hcont : Continuous (fun Z : Matrix (Fin m) (Fin m) ℤ_[p] =>
      B - (uOf A' Z)ᵀ * A * uOf A' Z) := by
    have hu : Continuous (fun Z : Matrix (Fin m) (Fin m) ℤ_[p] => uOf A' Z) := by
      have e : (fun Z : Matrix (Fin m) (Fin m) ℤ_[p] => uOf A' Z) =
          fun Z => 1 + ((p : ℤ_[p]) • (1 : Matrix (Fin m) (Fin m) ℤ_[p])) * (A' * Z) := by
        ext Z : 1
        simp [uOf]
      rw [e]
      exact continuous_const.add (continuous_const.matrix_mul (continuous_const.matrix_mul continuous_id))
    exact continuous_const.sub ((hu.matrix_transpose.matrix_mul continuous_const).matrix_mul hu)
  have hr0 : 0 ≤ ‖(p : ℤ_[p])‖ := norm_nonneg _
  have hr1 : ‖(p : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have hzero : Tendsto (fun k => B - (uOf A' (Zs (φ k)))ᵀ * A * uOf A' (Zs (φ k))) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    refine squeeze_zero_norm (a := fun k => ‖(p : ℤ_[p])‖ ^ (φ k)) (fun k => ?_) ?_
    · refine (norm_le_of_modE (hZ (φ k)) i j).trans ?_
      exact pow_le_pow_of_le_one hr0 hr1.le (by omega)
    · exact (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp hφ.tendsto_atTop
  have hfa : B - (uOf A' Zl)ᵀ * A * uOf A' Zl = 0 :=
    tendsto_nhds_unique ((hcont.tendsto Zl).comp hlim) hzero
  refine ⟨uOf A' Zl, ?_, sub_eq_zero.1 hfa |>.symm, Zl, rfl⟩
  exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_one_add_smul _)

end QuadFormsKB.Kitaoka.Density
