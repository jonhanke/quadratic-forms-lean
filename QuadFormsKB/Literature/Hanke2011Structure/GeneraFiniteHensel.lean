/-
# Finiteness of the local genera of a given determinant at every prime (Hensel's lemma)

**Layer:** local, at a finite prime $\mathfrak p$ of a number field $F$ (dyadic included), every rank $n$.

**Proves**
* `isometricGL_of_close` (**Hensel's lemma for forms**): over a complete discrete valuation ring $R$ with uniformizer
  $\pi$, if $\pi^d \,\Vert\, \det H_T$, $K \ge 2d + 1$ and the coefficients of $Q$ and $T$ are congruent mod $\pi^K$,
  then $Q \cong T$ over $R$ ($T = Q\circ Y$ with $Y \in \mathrm{GL}_n(R)$, $Y \equiv I \bmod \pi^{K-d}$). *Proof:* Newton's
  method for the quadratic map $X \mapsto Q \circ X$ started at $X = I$ (`LocalDensity.DVR.newton_lift`, with the
  surjectivity of the differential onto $\pi^d\,\mathrm{Sym}$, `LocalDensity.DVR.formD_surj`); $Y \equiv I \bmod \pi$ is
  invertible.
* `genera_finite` (**finitely many local genera of a given determinant**): for every finite prime $\mathfrak p$ of every
  number field $F$, every $n$ and every $S \in \mathrm{SqCl}(F_{\mathfrak p}^\times,\mathcal O_{\mathfrak p}^\times)$, the
  nondegenerate $\mathcal O_{\mathfrak p}$-genera of rank $n$ with $\det_H = S$ are finitely many. *Proof:* $S$ fixes
  $d = \operatorname{ord}_{\mathfrak p}\det H$; by Hensel's lemma the genus of a form depends only on its coefficients mod
  $\pi^{2d+1}$, and $\mathcal O_{\mathfrak p}/\pi^{2d+1}$ is finite.
* `binaryDyadicGeneraFinite`: the named input `BinaryDyadicGeneraFinite F` **holds for every number field**; so
  `BinaryLocalGeneraFinite F` holds (`binaryLocalGeneraFinite`), and Lemma 7.8 for $n = 2$ is unconditional over every
  totally real $F$ (`lemma_7_8_two_uncond`), Thm. 7.11 conditional only on the tables (`theorem_7_11_two_tables`).

This replaces the citation of O'Meara §93 (dyadic Jordan splittings) by a purely local argument that is uniform in
$\mathfrak p$ (it also re-proves the nondyadic case `RatND.genera_finite_nd`). Indices are 0-based.
-/
import Mathlib
import QuadFormsKB.Tamagawa.OrbitHensel
import QuadFormsKB.LocalDensity.NFBridge
import QuadFormsKB.Literature.Hanke2011Structure.GeneraFiniteNondyadic

open Matrix IsDedekindDomain NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Siegel QuadForm

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {n : ℕ}

theorem compMat_one' (Q : QuadForm R n) : Q.compMat (1 : Matrix (Fin n) (Fin n) R) = Q :=
  QuadForm.eq_of_eval_eq fun x => by rw [QuadForm.eval_compMat, Matrix.one_mulVec]

/-- **Hensel's lemma for quadratic forms over a complete discrete valuation ring** (every residue characteristic): if
$\pi^d \,\Vert\, \det H_T$, $K \ge 2d+1$ and $Q \equiv T \bmod \pi^K$ coefficientwise, then $Q \cong T$ over $R$. -/
@[kb "omeara1963" "§13D, 13:8, p. 26 (Hensel's lemma), applied to X ↦ Q∘X"]
theorem isometricGL_of_close {π : R} (hπ : Irreducible π) (Q T : QuadForm R n) {d K : ℕ}
    (hd : π ^ d ∣ T.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det) (hK : 2 * d + 1 ≤ K)
    (hQT : ∀ i j, π ^ K ∣ Q.coeff i j - T.coeff i j) : IsometricGL Q T := by
  obtain ⟨y, hy, hyx⟩ := newton_lift hπ (formF Q) (formD Q) (formF_add_smul Q)
    (fun p : UpperIdx n => T.coeff p.1.1 p.1.2) d K hK
    (fun x hx c => formD_surj Q T π hπ d K hd hd' (by omega) x hx c)
    (fun li => (1 : Matrix (Fin n) (Fin n) R) li.1 li.2)
    (fun p => by
      show π ^ K ∣ (Q.compMat 1).coeff p.1.1 p.1.2 - T.coeff p.1.1 p.1.2
      rw [compMat_one']; exact hQT _ _)
  set Y : Matrix (Fin n) (Fin n) R := toMat y
  have hYT : Q.compMat Y = T := ext_upper fun i j hij => congrFun hy ⟨(i, j), hij⟩
  -- `Y ≡ 1 mod π`, so `det Y` is a unit
  have hres : Y.map (IsLocalRing.residue R) = 1 := by
    ext i j
    rw [Matrix.map_apply, ← Matrix.map_one (IsLocalRing.residue R) (map_zero _) (map_one _)]
    rw [Matrix.map_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have h1 : π ^ (K - d) ∣ Y i j - (1 : Matrix (Fin n) (Fin n) R) i j := hyx (i, j)
    have h2 : π ∣ π ^ (K - d) := dvd_pow_self π (by omega)
    obtain ⟨c, hc⟩ := h2.trans h1
    rw [hc]
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self π)
  have hdet : IsUnit Y.det := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, RingHom.map_det, RingHom.mapMatrix_apply, hres, det_one]
    exact one_ne_zero
  have hYu : IsUnit Y := (Matrix.isUnit_iff_isUnit_det Y).mpr hdet
  exact isometricGL_iff_compMat.mpr ⟨hYu.unit, by rw [IsUnit.unit_spec, hYT]⟩

end DVR

section NF

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- Two nondegenerate forms over $\mathcal O_{\mathfrak p}$ with the same $\det_H$ squareclass have Hessian determinants
differing by the square of a unit. -/
theorem det_eq_mul_sq_of_detSqForm {n : ℕ} {T T' : QuadForm 𝔬 n} (hT : T.hessian.det ≠ 0)
    (hT' : T'.hessian.det ≠ 0) (h : detSqForm T = detSqForm T') :
    ∃ u : 𝔬ˣ, T'.hessian.det = T.hessian.det * (u : 𝔬) ^ 2 := by
  have hT0 : algebraMap 𝔬 Fv T.hessian.det ≠ 0 := algebraMap_ne_zero_iff.mpr hT
  have hT0' : algebraMap 𝔬 Fv T'.hessian.det ≠ 0 := algebraMap_ne_zero_iff.mpr hT'
  rw [detSqForm_of_ne hT0, detSqForm_of_ne hT0'] at h
  have h' := QuotientGroup.eq.mp h
  obtain ⟨w, ⟨u, rfl⟩, hw⟩ := Subgroup.mem_map.mp h'
  refine ⟨u, IsFractionRing.injective 𝔬 Fv ?_⟩
  have e := congrArg Units.val hw
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_mk0] at e
  rw [map_mul, map_pow]
  have : ((Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u : Fvˣ) : Fv) =
      algebraMap 𝔬 Fv (u : 𝔬) := rfl
  rw [this] at e
  field_simp at e
  first | linear_combination e | linear_combination -e

/-- **Finiteness of the nondegenerate local genera of a given determinant at every finite prime** (every rank $n$,
every number field, dyadic primes included). -/
@[kb "omeara1963" "§92–93 (finitely many local integral classes of given discriminant); proved by Hensel's lemma"]
theorem genera_finite (n : ℕ) (S : LocalSqCl v) :
    {G : LocGenus v n | G.Nondeg ∧ G.det = S}.Finite := by
  classical
  by_cases hne : {G : LocGenus v n | G.Nondeg ∧ G.det = S}.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne; rw [hne]; exact Set.finite_empty
  obtain ⟨G₁, hN₁, hd₁⟩ := hne
  set T₁ := G₁.out
  have hT₁ : T₁.hessian.det ≠ 0 := by
    have : G₁ = LocGenus.mk T₁ := (Quotient.out_eq G₁).symm
    rw [this] at hN₁; exact hN₁
  have hπ := NF.irreducible_π v
  obtain ⟨d, hd, hd'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ hT₁
  set K := 2 * d + 1
  have hN : Ideal.absNorm v.asIdeal ≠ 0 :=
    (Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr (mem_nonZeroDivisors_of_ne_zero v.ne_bot)
  have : Finite (𝔬 ⧸ Ideal.span {NF.π v ^ K}) :=
    Nat.finite_of_card_ne_zero (by rw [NF.card_quot_π_pow]; exact pow_ne_zero _ hN)
  let f : {G : LocGenus v n | G.Nondeg ∧ G.det = S} → (Fin n → Fin n → 𝔬 ⧸ Ideal.span {NF.π v ^ K}) :=
    fun G i j => Ideal.Quotient.mk _ (G.1.out.coeff i j)
  -- every member has `π^d ∥ det H`
  have hval : ∀ G ∈ {G : LocGenus v n | G.Nondeg ∧ G.det = S},
      G.out.hessian.det ≠ 0 ∧ NF.π v ^ d ∣ G.out.hessian.det ∧ ¬ NF.π v ^ (d + 1) ∣ G.out.hessian.det := by
    rintro G ⟨hN', hd₂⟩
    have eG : G = LocGenus.mk G.out := (Quotient.out_eq G).symm
    have h0 : G.out.hessian.det ≠ 0 := by rw [eG] at hN'; exact hN'
    have hsq : detSqForm T₁ = detSqForm G.out := by
      have e1 : G₁.det = detSqForm T₁ := by
        conv_lhs => rw [show G₁ = LocGenus.mk T₁ from (Quotient.out_eq G₁).symm]
        rfl
      have e2 : G.det = detSqForm G.out := by
        conv_lhs => rw [eG]
        rfl
      rw [← e1, ← e2, hd₁, hd₂]
    obtain ⟨u, hu⟩ := det_eq_mul_sq_of_detSqForm v hT₁ h0 hsq
    refine ⟨h0, ?_, ?_⟩
    · rw [hu]; exact dvd_mul_of_dvd_left hd _
    · rw [hu, ← Units.val_pow_eq_pow_val, Units.dvd_mul_right]; exact hd'
  have hinj : Function.Injective f := by
    rintro ⟨G, hG⟩ ⟨G', hG'⟩ hff
    obtain ⟨-, hdG', hdG''⟩ := hval G' hG'
    have hc : ∀ i j, NF.π v ^ K ∣ G.out.coeff i j - G'.out.coeff i j := fun i j => by
      have := congrFun (congrFun hff i) j
      exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp this)
    have hiso := isometricGL_of_close hπ G.out G'.out hdG' hdG'' le_rfl hc
    apply Subtype.ext
    show G = G'
    rw [← Quotient.out_eq G, ← Quotient.out_eq G']
    exact LocGenus.mk_eq_mk.mpr hiso
  exact Set.finite_coe_iff.mp (Finite.of_injective f hinj)

/-- **The named input `BinaryDyadicGeneraFinite` holds for every number field** (proved by Hensel's lemma, not through
O'Meara §93). -/
theorem binaryDyadicGeneraFinite (F : Type) [Field F] [NumberField F] : BinaryDyadicGeneraFinite F where
  finite v _ s := (genera_finite v 2 s).subset fun _ hG => ⟨hG.1, hG.2.2⟩

/-- `BinaryLocalGeneraFinite F` holds for every number field. -/
theorem binaryLocalGeneraFinite (F : Type) [Field F] [NumberField F] : BinaryLocalGeneraFinite F :=
  binaryLocalGeneraFinite_of_dyadic (binaryDyadicGeneraFinite F)

end NF

section Main

open Real QuadFormsKB.Lattices QuadFormsKB.HilbertModular QuadFormsKB.NFEuler QuadFormsKB.RegProd
  QuadFormsKB.Hanke2011Ternary.NF

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- **Lemma 7.8 for $n = 2$, unconditional, over every totally real number field $F$**: for the totally positive
definite signature, every $S$ with $\mathrm{Cls}^*(S,\vec\sigma^+_\infty;2) \ne \emptyset$ and every admissible generic
family, $\sum 1/|\mathrm{Aut}(L)| = \beta^{-1}_{2,f}(\widetilde S)|\Delta_F|^{1/2}N(I(S))^{3/2}[A^* + \varepsilon_\infty B^*]/
(2(4\pi)^{[F:\mathbb Q]})$, the product over the primes read as a regularized product (see `lemma_7_8_two`). -/
@[kb "hanke2011structure" "Lemma 7.8, p. 32 (n = 2, every totally real F, unconditional)"]
theorem lemma_7_8_two_uncond (S : AdelicSqCl F)
    (hne : (GenStar S (totPosSig F 2) ∅ (fun _ => 1)).Nonempty)
    {βgen χ : HeightOneSpectrum (𝓞 F) → ℝ} (hg : IsGenericFamily S βgen χ) :
    ∑ᶠ t ∈ GenStar S (totPosSig F 2) ∅ (fun _ => 1), massOfTuple S (totPosSig F 2) ∅ (fun _ => 1) t =
      betaInvReg χ βgen * |(discr F : ℝ)| ^ ((1 : ℝ) / 2) * normAssoc S ^ ((3 : ℝ) / 2) *
        (astarTwo S βgen + (epsInf (totPosSig F 2) : ℝ) * bstarTwo S βgen) /
          (2 * (4 * π) ^ Module.finrank ℚ F) :=
  lemma_7_8_two (binaryLocalGeneraFinite F) S hne hg

/-- **Theorem 7.11 (identity of the total mass, corrected $\kappa$)**, over every totally real $F$ in which $2$ splits
completely, conditional only on the tables `BinaryTableHolds` (see `theorem_7_11_two`). -/
@[kb "hanke2011structure" "Thm. 7.11, p. 33 (identity of the total mass; corrected κ)"]
theorem theorem_7_11_two_tables (hs : TwoSplitsCompletely F) (S : AdelicSqCl F)
    (hne : (GenStar S (totPosSig F 2) ∅ (fun _ => 1)).Nonempty)
    {d : HeightOneSpectrum (𝓞 F) → LocalDatum ℝ} (hd : BinaryTableHolds S d) :
    ∑ᶠ t ∈ GenStar S (totPosSig F 2) ∅ (fun _ => 1), massOfTuple S (totPosSig F 2) ∅ (fun _ => 1) t =
      kappaCorr d * |(discr F : ℝ)| ^ ((1 : ℝ) / 2) * normAssoc S ^ ((1 : ℝ) / 2) /
        (2 * (2 * π) ^ Module.finrank ℚ F) * prodGammaInvNotDvd d :=
  theorem_7_11_two (binaryLocalGeneraFinite F) hs S hne hd

end Main

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.genera_finite
#print axioms QuadFormsKB.Hanke2011Structure.binaryLocalGeneraFinite
#print axioms QuadFormsKB.Hanke2011Structure.lemma_7_8_two_uncond
#print axioms QuadFormsKB.Hanke2011Structure.theorem_7_11_two_tables
