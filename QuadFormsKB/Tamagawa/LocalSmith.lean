/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.OrbitalNonStd
import QuadFormsKB.Tamagawa.SiegelAllRanks

/-!
# Local Smith normal form and the $\alpha$ transformation law at every prime

**Proves** the $\alpha$ transformation law `AlphaLawAt v (Q₀)_v P` for **every** finite prime $\mathfrak p$ (dyadic
included), every nondegenerate global form $Q_0$ over $\mathcal O_F$ and every $P \in M_N(\mathfrak o_\mathfrak p)$ with $\det P \ne 0$,
for **any** number field $F$ (no class-number hypothesis). Consequently the input `DyadicAlphaLaw Q₀` and the input
`OrbitalLocalIdentities Q₀` are theorems.

*Proof.*
1. *Diagonal global $P$* (`alphaLaw_diag_global`): the local change-of-lattice identity `LatChange.localDensity_mul_relRatio`
   (valid at every prime, proved from the box formula `LatChange.selfDensity_formula` by Hensel lifting; no split vectors)
   for $c = 1$, $D = \mathrm{diag}(c_a)$, $c_a \in \mathcal O_F$, rewritten in the groups `KL`.
2. *Local Smith normal form* (`exists_smith_local`): $P = U\,\mathrm{diag}(a)\,V$ over the DVR $\mathfrak o_\mathfrak p$ (`exists_smith_decomp` over any PID), $a_i = u_i\varpi^{k_i}$.
3. *Globalization* (`exists_global_right_mul`): approximate $U$ by a global $U' \in M_N(\mathcal O_F)$ with
   $U' \equiv U \bmod \varpi^K$, $K > \max k_i$; then $U'\,\mathrm{diag}(\varpi^{k}) = P\,X$ with $X \in \mathrm{GL}_N(\mathfrak o_\mathfrak p)$.
4. The moves: invariance under $P \mapsto PX$ (`alphaLaw_mul_right`), the cocycle (`alphaLaw_mul`), and the trivial law for
   $U' \in \mathrm{GL}_N(\mathfrak o_\mathfrak p)$; $Q_0\circ U'$ is again global, so step 1 applies to it.

This replaces a dyadic split-vector induction: the only local input needed there is now proved.
-/

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open NumberField IsDedekindDomain Lattices QuadForm LocalDensity LocalDensity.DVR QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-! ### Stabilizers in `orthGroup` versus `KL` -/

section KL

variable {N : ℕ}

theorem stabLat_map_subtype_eq_KL (Q : QuadForm F N) (Λ : Submodule 𝔬 (Fin N → Fv)) :
    (stabLat v (orthGroup Q Fv).subtype Λ).map (orthGroup Q Fv).subtype = KL v (Q.map (algebraMap F Fv)) Λ := by
  ext g
  rw [mem_KL]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨(mem_orthGroup_iff_compMat v Q _).mp h.2, hh⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨g, (mem_orthGroup_iff_compMat v Q _).mpr h1⟩, h2, rfl⟩

theorem stdStab_map_subtype_eq_KL (Q : QuadForm F N) :
    (stdStab Q v).map (orthGroup Q Fv).subtype = KL v (Q.map (algebraMap F Fv)) (std v) := by
  rw [stdStab_eq_stabLat, stabLat_map_subtype_eq_KL]

theorem relRatio_mul_relRatio_symm {G : Type*} [Group G] {A B : Subgroup G} (h : Commens A B) :
    relRatio A B * relRatio B A = 1 := by
  have := relRatio_mul h ⟨h.2, h.1⟩ ⟨by simp, by simp⟩
  rwa [relRatio_self] at this

end KL

/-! ### Step 1: the law for a global diagonal matrix, at every prime -/

section Diag

variable {N : ℕ}

open LatChange in
theorem stabB_map_subtype_eq_KL (Q₀ : QuadForm (𝓞 F) N) (cv : Fin N → 𝓞 F) (hcv : ∀ a, cv a ≠ 0)
    (hP : (diagonal fun a => NF.ι v (cv a)).det ≠ 0) :
    (stabB v Q₀ (one_ne_zero) cv hcv).map (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv).subtype =
      KL v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv))
        (locAct v (glOf v (diagonal fun a => NF.ι v (cv a)) hP) (std v)) := by
  set g := gR (gDiag cv hcv) Fv
  have hg : glOf v (diagonal fun a => NF.ι v (cv a)) hP = g := Units.ext (by
    rw [glOf_val]; exact (gR_gDiag_val v cv hcv).symm)
  rw [hg, map_Qp_eq, ← stabLat_map_subtype_eq_KL]
  ext k
  simp only [Subgroup.mem_map, stabB]
  constructor
  · rintro ⟨σ, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨conjD v Q₀ one_ne_zero cv hcv h, ?_, rfl⟩
    show locAct v ((conjD v Q₀ one_ne_zero cv hcv h : orthGroup _ Fv) : GL (Fin N) Fv) (locAct v g (std v)) =
      locAct v g (std v)
    have hh' : locAct v (h : GL (Fin N) Fv) (std v) = std v := hh
    rw [conjD, conjOrth_apply, ← locAct_mul, mul_assoc, inv_mul_cancel, mul_one, locAct_mul, hh']
  · rintro ⟨σ, hσ, rfl⟩
    have hσ' : locAct v (σ : GL (Fin N) Fv) (locAct v g (std v)) = locAct v g (std v) := hσ
    refine ⟨σ, ⟨(conjD v Q₀ one_ne_zero cv hcv).symm σ, ?_, by simp⟩, rfl⟩
    show locAct v (((conjD v Q₀ one_ne_zero cv hcv).symm σ : orthGroup _ Fv) : GL (Fin N) Fv) (std v) = std v
    rw [conjD, conjOrth_symm_apply, locAct_mul, locAct_mul, hσ', ← locAct_mul, inv_mul_cancel, locAct_one]

open LatChange in
/-- **The $\alpha$ law for a global diagonal matrix** $D = \mathrm{diag}(c_a)$, $c_a \in \mathcal O_F\setminus 0$, at every prime
(dyadic included): `localDensity_mul_relRatio` with $c = 1$ in the notation. -/
theorem alphaLaw_diag_global (Q₀ : QuadForm (𝓞 F) N) (hQ₀ : Q₀.Nondegenerate) (cv : Fin N → 𝓞 F)
    (hcv : ∀ a, cv a ≠ 0) (hP : (diagonal fun a => NF.ι v (cv a)).det ≠ 0) :
    AlphaLawAt v (NF.Qp v Q₀) (diagonal fun a => NF.ι v (cv a)) hP := by
  have key := localDensity_mul_relRatio v Q₀ (c := 1) one_ne_zero cv hcv hQ₀
  rw [prod_q_pow_ord_eq v one_ne_zero hcv, NF.localDensityForm_eq_completion,
    NF.localDensityForm_eq_completion] at key
  have e1 : NF.Qp v ((1 : 𝓞 F) • Q₀.compMat (diagonal cv)) =
      (NF.Qp v Q₀).compMat (diagonal fun a => NF.ι v (cv a)) := by
    rw [NF.Qp, LatChange.map_smul_compMat_diagonal, map_one]; ext a b; simp [smul_coeff]
  have hA := stdStab_map_subtype_eq_KL v (Q₀.map (algebraMap (𝓞 F) F))
  rw [← map_Qp_eq] at hA
  have hr : relRatio (stdStab (Q₀.map (algebraMap (𝓞 F) F)) v) (stabB v Q₀ one_ne_zero cv hcv) =
      relRatio (KL v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)) (std v))
        (KL v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv))
          (locAct v (glOf v (diagonal fun a => NF.ι v (cv a)) hP) (std v))) := by
    rw [← hA, ← stabB_map_subtype_eq_KL v Q₀ cv hcv hP, relRatio_map (Subgroup.subtype_injective _)]
  have hJ : ‖FinitePlace.embedding v (algebraMap (𝓞 F) F (jac 1 cv))‖ =
      ‖(((diagonal fun a => NF.ι v (cv a)).det : 𝔬) : Fv)‖ ^ (N + 1) := by
    show ‖((NF.ι v (jac 1 cv) : 𝔬) : Fv)‖ = _
    rw [jac, det_diagonal, one_pow, one_mul, map_pow, ← map_prod]
    push_cast
    rw [norm_pow]
  rw [e1, hr, hJ] at key
  have hc : Commens (KL v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv))
        (locAct v (glOf v (diagonal fun a => NF.ι v (cv a)) hP) (std v)))
      (KL v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)) (std v)) :=
    commens_KL v _ (latOf_isLattice v _ hP) (std_isLattice v)
  have hinv := relRatio_mul_relRatio_symm hc
  have hJpos : 0 < ‖(((diagonal fun a => NF.ι v (cv a)).det : 𝔬) : Fv)‖ ^ (N + 1) := by
    refine pow_pos (norm_pos_iff.mpr ?_) _
    exact_mod_cast hP
  unfold AlphaLawAt
  set r₁ := relRatio (KL v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv))
        (locAct v (glOf v (diagonal fun a => NF.ι v (cv a)) hP) (std v)))
      (KL v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)) (std v))
  set r₂ := relRatio (KL v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)) (std v))
        (KL v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv))
          (locAct v (glOf v (diagonal fun a => NF.ι v (cv a)) hP) (std v)))
  set J := ‖(((diagonal fun a => NF.ι v (cv a)).det : 𝔬) : Fv)‖ ^ (N + 1)
  calc r₁ * localDensityForm (NF.Qp v Q₀) (NF.Qp v Q₀) (NF.π v)
      = r₁ * (J * (J⁻¹ * localDensityForm (NF.Qp v Q₀) (NF.Qp v Q₀) (NF.π v))) := by
        rw [← mul_assoc J, mul_inv_cancel₀ hJpos.ne', one_mul]
    _ = r₁ * (J * (localDensityForm ((NF.Qp v Q₀).compMat (diagonal fun a => NF.ι v (cv a)))
          ((NF.Qp v Q₀).compMat (diagonal fun a => NF.ι v (cv a))) (NF.π v) * r₂)) := by rw [key]
    _ = _ := by
        rw [show r₁ * (J * (localDensityForm ((NF.Qp v Q₀).compMat (diagonal fun a => NF.ι v (cv a)))
          ((NF.Qp v Q₀).compMat (diagonal fun a => NF.ι v (cv a))) (NF.π v) * r₂)) =
          (r₂ * r₁) * (localDensityForm ((NF.Qp v Q₀).compMat (diagonal fun a => NF.ι v (cv a)))
          ((NF.Qp v Q₀).compMat (diagonal fun a => NF.ι v (cv a))) (NF.π v) * J) by ring]
        rw [mul_comm r₂ r₁, hinv, one_mul]

end Diag

/-! ### Steps 2–3: local Smith normal form and globalization -/

section Smith

variable {N : ℕ}

/-- $\det(1 + \varpi Y)$ is a unit of $\mathfrak o_\mathfrak p$ (it is $\equiv 1$ modulo the maximal ideal). -/
theorem isUnit_det_one_add_π_smul (Y : Matrix (Fin N) (Fin N) 𝔬) : IsUnit (1 + NF.π v • Y).det := by
  by_contra h
  have hm : (1 + NF.π v • Y).det ∈ IsLocalRing.maximalIdeal 𝔬 := (IsLocalRing.mem_maximalIdeal _).mpr h
  have hπ : NF.π v ∈ IsLocalRing.maximalIdeal 𝔬 :=
    (IsLocalRing.mem_maximalIdeal _).mpr (NF.irreducible_π v).not_isUnit
  set f := Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝔬)
  have h1 : f (1 + NF.π v • Y).det = 1 := by
    rw [RingHom.map_det, map_add, map_one, smul_eq_diagonal_mul, map_mul, RingHom.mapMatrix_apply f (diagonal _),
      diagonal_map (map_zero f), Ideal.Quotient.eq_zero_iff_mem.mpr hπ, diagonal_zero, zero_mul, add_zero, det_one]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm] at h1
  exact zero_ne_one h1

/-- **Local Smith normal form** with global elementary divisors: every $P \in M_N(\mathfrak o_\mathfrak p)$, $\det P \ne 0$, is
$P = U\,\mathrm{diag}(\varpi^{k_i})\,V$ with $U, V \in \mathrm{GL}_N(\mathfrak o_\mathfrak p)$ ($\varpi$ = `NF.π v`, the image of a global
uniformizer). From `exists_smith_decomp` over the DVR $\mathfrak o_\mathfrak p$. -/
@[kb "cohen1993" "§2.4.4 (Smith normal form) [unverified]"]
theorem exists_smith_local (P : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0) :
    ∃ (U V : Matrix (Fin N) (Fin N) 𝔬) (k : Fin N → ℕ), IsUnit U.det ∧ IsUnit V.det ∧
      P = U * diagonal (fun i => NF.π v ^ k i) * V := by
  obtain ⟨U, V, a, ha, hPa⟩ := LatChange.exists_smith_decomp P hP
  choose k u hu using fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (ha i) (NF.irreducible_π v)
  refine ⟨U.val, diagonal (fun i => (u i : 𝔬)) * V.val, k, ?_, ?_, ?_⟩
  · exact (Matrix.isUnits_det_units U)
  · rw [det_mul, det_diagonal]
    rw [← Units.coe_prod]
    exact (IsUnit.mul (Units.isUnit _) (Matrix.isUnits_det_units V))
  · rw [hPa, ← Matrix.mul_assoc (U.val * _) (diagonal _) V.val, Matrix.mul_assoc U.val (diagonal _) (diagonal _),
      diagonal_mul_diagonal]
    congr 3
    funext i
    rw [hu i, mul_comm]

/-- **Globalization of the left factor**: for $P \in M_N(\mathfrak o_\mathfrak p)$ with $\det P \ne 0$ there are $B \in M_N(\mathcal O_F)$ with
$\det B$ a unit at $\mathfrak p$, exponents $k_i$ and $X \in \mathrm{GL}_N(\mathfrak o_\mathfrak p)$ with
$B\,\mathrm{diag}(\varpi^{k_i}) = P\,X$ (so $P\mathfrak o_\mathfrak p^N = B\,\mathrm{diag}(\varpi^{k_i})\,\mathfrak o_\mathfrak p^N$ comes from a global matrix). -/
theorem exists_global_right_mul (P : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0) :
    ∃ (B : Matrix (Fin N) (Fin N) (𝓞 F)) (k : Fin N → ℕ) (X : Matrix (Fin N) (Fin N) 𝔬),
      IsUnit (B.map (NF.ι v)).det ∧ IsUnit X.det ∧
      B.map (NF.ι v) * diagonal (fun i => NF.π v ^ k i) = P * X := by
  classical
  obtain ⟨U, V, k, hU, hV, rfl⟩ := exists_smith_local v P hP
  set π := NF.π v
  set K := (∑ i, k i) + 1
  have hK : ∀ i, k i + 1 ≤ K := fun i => by
    have := Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i); omega
  -- approximate `U` modulo `π ^ K`
  have happ : ∀ i j, ∃ b : 𝓞 F, ∃ e : 𝔬, NF.ι v b = U i j + π ^ K * e := by
    intro i j
    obtain ⟨b, hb⟩ := NF.redHom_surjective v K (Ideal.Quotient.mk _ (U i j))
    have hmem : NF.ι v b - U i j ∈ Ideal.span {π ^ K} := Ideal.Quotient.eq.mp hb
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨b, e, by rw [mul_comm]; linear_combination -he⟩
  choose B E₀ hBE using happ
  have hBmap : (Matrix.of B).map (NF.ι v) = U + π ^ K • Matrix.of E₀ := by
    ext i j; simp [hBE]
  obtain ⟨Uinv, hUU, hUU'⟩ : ∃ Uinv : Matrix (Fin N) (Fin N) 𝔬, U * Uinv = 1 ∧ Uinv * U = 1 :=
    ⟨U⁻¹, Matrix.mul_nonsing_inv U hU, Matrix.nonsing_inv_mul U hU⟩
  set E := Uinv * Matrix.of E₀
  have hBU : (Matrix.of B).map (NF.ι v) = U * (1 + π ^ K • E) := by
    rw [hBmap, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  set Y : Matrix (Fin N) (Fin N) 𝔬 :=
    diagonal (fun i => π ^ (K - 1 - k i)) * E * diagonal (fun i => π ^ k i)
  have hpow : ∀ i, π ^ k i * (π * π ^ (K - 1 - k i)) = π ^ K := fun i => by
    rw [← pow_succ', ← pow_add]; congr 1; have := hK i; omega
  have hM : (1 + π ^ K • E) * diagonal (fun i => π ^ k i) = diagonal (fun i => π ^ k i) * (1 + π • Y) := by
    ext i j
    simp only [Y, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.add_apply,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, diagonal_mul, mul_diagonal]
    by_cases h : i = j
    · subst h; simp only [Matrix.one_apply_eq]
      congr 2; rw [← hpow i]; ring
    · simp only [Matrix.one_apply_ne h, zero_mul, zero_add]
      congr 2; rw [← hpow i]; ring
  refine ⟨Matrix.of B, k, V⁻¹ * (1 + π • Y), ?_, ?_, ?_⟩
  · rw [hBU, det_mul]
    refine hU.mul ?_
    rw [show K = (∑ i, k i) + 1 from rfl, pow_succ', mul_smul]
    exact isUnit_det_one_add_π_smul v _
  · rw [det_mul]
    exact (Matrix.isUnit_nonsing_inv_det V hV).mul (isUnit_det_one_add_π_smul v Y)
  · rw [hBU, Matrix.mul_assoc, hM, ← Matrix.mul_assoc, Matrix.mul_assoc (U * _) V, ← Matrix.mul_assoc V,
      Matrix.mul_nonsing_inv V hV, Matrix.one_mul]

end Smith

/-! ### Step 4: the law for every $P$ at every prime -/

section Law

variable {N : ℕ}

/-- **The $\alpha$ transformation law at every prime** (dyadic included) for every nondegenerate global $Q_0$ over $\mathcal O_F$
and every $P \in M_N(\mathfrak o_\mathfrak p)$ with $\det P \ne 0$:
$$r\big(K(P\mathfrak o_\mathfrak p^N), K(\mathfrak o_\mathfrak p^N)\big)\,\beta_\mathfrak p(Q_0) = \beta_\mathfrak p(Q_0\circ P)\,\|\det P\|_\mathfrak p^{N+1}.$$
No class-number hypothesis. *Proof:* globalize $P$ up to $\mathrm{GL}_N(\mathfrak o_\mathfrak p)$ (`exists_global_right_mul`), then the cocycle
(`alphaLaw_mul`) with the unit law and the global diagonal law (`alphaLaw_diag_global`) for $Q_0\circ B$. -/
@[kb "weil1982" "§2.4 and §3.4 (Haar measures of lattice stabilizers) [unverified]"]
theorem alphaLaw_global (Q₀ : QuadForm (𝓞 F) N) (hQ₀ : Q₀.Nondegenerate) (P : Matrix (Fin N) (Fin N) 𝔬)
    (hP : P.det ≠ 0) : AlphaLawAt v (NF.Qp v Q₀) P hP := by
  obtain ⟨B, k, X, hB, hX, hBX⟩ := exists_global_right_mul v P hP
  set D : Matrix (Fin N) (Fin N) 𝔬 := diagonal fun i => NF.π v ^ k i
  have hD : D.det ≠ 0 := by
    rw [det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (NF.irreducible_π v).ne_zero
  have hBD : (B.map (NF.ι v) * D).det ≠ 0 := by rw [det_mul]; exact mul_ne_zero hB.ne_zero hD
  have hPX : (P * X).det ≠ 0 := by rw [← hBX]; exact hBD
  refine (alphaLaw_mul_right v _ P X hP hX hPX).mp ((alphaLaw_congr v _ hBX hBD hPX).mp ?_)
  refine alphaLaw_mul v _ _ _ hB.ne_zero hD hBD (alphaLaw_unit v _ _ hB.ne_zero hB) ?_
  have hBdet : B.det ≠ 0 := by
    intro h; apply hB.ne_zero; rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  have eQ : (NF.Qp v Q₀).compMat (B.map (NF.ι v)) = NF.Qp v (Q₀.compMat B) := map_compMat _ _ _
  have hcv : ∀ i, (NF.unif v) ^ k i ≠ 0 := fun i => pow_ne_zero _ (fun h => (NF.irreducible_π v).ne_zero (by rw [NF.π, h, map_zero]))
  have eD : D = diagonal fun i => NF.ι v ((NF.unif v) ^ k i) := by simp [D, map_pow]
  have hD' : (diagonal fun i => NF.ι v ((NF.unif v) ^ k i)).det ≠ 0 := eD ▸ hD
  rw [eQ]
  exact (alphaLaw_congr v _ eD hD hD').mpr
    (alphaLaw_diag_global v (Q₀.compMat B) (LatChange.nondegenerate_compMat_of_det hQ₀ hBdet) _ hcv hD')

end Law

/-! ### Consequences: the and the local inputs are theorems -/

section Consequences

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-- **The input `DyadicAlphaLaw` is a theorem** (for every nondegenerate $Q_0$, any number field). -/
@[kb "weil1982" "§2.4 and §3.4 (Haar measures of lattice stabilizers at the dyadic places) [unverified]"]
theorem dyadicAlphaLaw (Q₀ : QuadForm (𝓞 F) (n + 1)) (hQ₀ : Q₀.Nondegenerate) : DyadicAlphaLaw Q₀ :=
  ⟨fun v _ P hP => alphaLaw_global v Q₀ hQ₀ P hP⟩

/-- **The input `OrbitalLocalIdentities` is a theorem**: the local orbital identity holds at every non-standard prime of every
adapted frame of every nondegenerate $Q_0$ (any class number; the dyadic primes included). -/
@[kb "weil1982" "§3.4 and §4.5, p. 109 (local orbital identities at all non-standard primes) [unverified]"]
theorem orbitalLocalIdentities (Q₀ : QuadForm (𝓞 F) (n + 1)) (hQ₀ : Q₀.Nondegenerate) : OrbitalLocalIdentities Q₀ :=
  orbitalLocalIdentities_of_dyadic Q₀ hQ₀ (dyadicAlphaLaw Q₀ hQ₀)

variable (F) in
/-- **The input `OddRankOrbitalLocalIdentities F` is a theorem.** -/
@[kb "weil1982" "§3.4 and §4.5, p. 109 [unverified]"]
theorem oddRankOrbitalLocalIdentities : OddRankOrbitalLocalIdentities F :=
  OddRankOrbitalLocalIdentities.of_all fun _ Q₀ hpd =>
    orbitalLocalIdentities Q₀ (nondegenerate_of_totallyPosDef' hpd)

open QuadFormsKB.SphericalFibration in
/-- **The orbital Euler product with no local input** ($\mathcal O_F$ a PID, rank $n + 1 \ge 5$). -/
@[kb "weil1982" "§4.5, p. 109 (the orbital Euler product)"]
theorem orbitalEulerProduct_pid [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) (hn : 4 ≤ n) : OrbitalEulerProduct Q₀ (tauComp Q₀) :=
  orbitalEulerProduct Q₀ hpd hn (orbitalLocalIdentities Q₀ (nondegenerate_of_totallyPosDef' hpd))

variable [IsPrincipalIdealRing (𝓞 F)]

/-- **$\tau(SO(Q_0)) = 2$ in every rank $N \ge 3$, conditional only on `TernaryTamagawaTwo F`** ($F$ totally real of degree $\ge 2$,
$\mathcal O_F$ a PID, $Q_0$ totally positive definite). `tamagawaNumberTwo_all_ranks` with its odd-rank input discharged. -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109; §3.7, Thm 3.7.1, p. 65"]
theorem tamagawaNumberTwo_all_ranks_of_ternary (hd : 2 ≤ Fintype.card (InfinitePlace F))
    (hT : TernaryTamagawaTwo F) {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) :
    TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_all_ranks hd hT (oddRankOrbitalLocalIdentities F) hN Q₀ hpd

/-- **The mass formula in every rank $N \ge 3$, conditional only on `TernaryTamagawaTwo F`.** -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109; cf. Kitaoka 1993, Thm 6.8.1 [unverified]"]
theorem massFormula_all_ranks_of_ternary (hd : 2 ≤ Fintype.card (InfinitePlace F)) (hT : TernaryTamagawaTwo F)
    {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : MassFormulaHolds Q₀ :=
  massFormula_all_ranks hd hT (oddRankOrbitalLocalIdentities F) hN Q₀ hpd

/-- **Siegel's formula for numbers in every rank $N \ge 4$, conditional only on `TernaryTamagawaTwo F`** (even $N$:
unconditional; odd $N$: `siegelFormulaAt_of_massFormula` with the local identities now proved). -/
@[kb "weil1982" "§4.5, p. 100 (Siegel's theorem as a consequence of τ = 2), Thm 4.5.1, p. 109"]
theorem siegelFormulaAt_all_ranks_of_ternary (hd : 2 ≤ Fintype.card (InfinitePlace F)) (hT : TernaryTamagawaTwo F)
    {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_all_ranks hd hT (oddRankOrbitalLocalIdentities F) hN Q₀ hpd hm

/-- **Odd rank in the form, conditional only on `TernaryTamagawaTwo F`**:
$\mathrm{repMass} = \mathrm{Mass}\cdot|d_F|^{-(N-1)/2}\,\mathtt{aENF}(Q_0, m)$, $N = n + 1 \ge 5$ odd. -/
@[kb "weil1982" "§4.5, p. 100; Thm 4.5.1, p. 109"]
theorem siegelFormula_odd_aENF_of_ternary (hd : 2 ≤ Fintype.card (InfinitePlace F)) (hT : TernaryTamagawaTwo F)
    {n : ℕ} (hn : 4 ≤ n) (he : Even n) (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMass (formF Q₀) (stdLat F (n + 1)) (algebraMap (𝓞 F) F m) =
      mass (formF Q₀) (stdLat F (n + 1)) * ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n + 1 - 1) * Siegel.aENF Q₀ m) :=
  siegelFormula_odd_aENF hd hT (oddRankOrbitalLocalIdentities F) hn he Q₀ hpd hm

/-- **$\tau(SO) = 2$ in every rank $N \ge 4$ from rank 4 alone** (any totally real $F$ with $\mathcal O_F$ a PID, $\mathbb Q$ included). -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109"]
theorem tamagawaNumberTwo_of_quaternary (h4 : QuaternaryTamagawaTwo F) {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_of_four h4 (oddRankOrbitalLocalIdentities F) hN Q₀ hpd

end Consequences

/-- **Over $\mathbb Q$: Siegel's formula in every rank $N \ge 5$, conditional only on `QuaternaryTamagawaTwo ℚ`.** -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109"]
theorem siegelFormulaAt_rat_of_quaternary (h4 : QuaternaryTamagawaTwo ℚ) {N : ℕ} (hN : 5 ≤ N)
    (Q₀ : QuadForm (𝓞 ℚ) N) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 ℚ}
    (hm : ∀ v, 0 < realEmb ℚ v (algebraMap (𝓞 ℚ) ℚ m)) : SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_rat h4 (oddRankOrbitalLocalIdentities ℚ) hN Q₀ hpd hm

end QuadFormsKB.Tamagawa
