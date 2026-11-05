/-
# Conway–Sloane, Ch. 15, §9.5–9.6: $2$-adically automorphous numbers of even order

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5–9.6, pp. 391–393
(`conwaysloane1999`).

**Layer.** As in `Section9DyadicUpper.lean`: $f(x) = xAx^{\mathsf T}$ (`csQ A`), the standard lattice
$L = \mathbb Z^n$, a prime $v$ over $2$ and $\mathbb Q_2$ = `v.adicCompletion ℚ` with the completion's
$\mathbb Q$-algebra structure.

**Proves**
* `even_log_of_wallCore`: if every integral $S$ with $S^{\mathsf T}AS = A$, $\det S = 1$ has Wall determinants
  $\det(P^{\mathsf T}AR)$ of square valuation (the hypothesis `hcore`), then every $2$-adically automorphous number of
  $f$ (every element of $\theta(O^+(L_2))$) has even order. The proof: Wall's formula
  (`Wall.wall_formula`) gives $\theta(\sigma) = \det(P^{\mathsf T}HR) = 2^m\det(P^{\mathsf T}AR)$ with $H = 2A$, and
  $\det\sigma = (-1)^m = 1$ makes $m$ even;
* `even_log_of_evenUnimodular` (**unconditional**): this holds whenever $A$ is even unimodular at $2$
  ($\det A$ odd, every $A_{ii}$ even), by the core lemma `EvenUnimodular.exists_sq_valued_wallDet`.

This is the $2$-adic upper bound that the book's examples need (§9.6, (44)); before, it was derived from the named
statement `Theorem18Dyadic` (`even_log_of_theorem18Dyadic`).
-/
import QuadFormsKB.Literature.ConwaySloane.Section9EvenUnimodular
import QuadFormsKB.Literature.ConwaySloane.Section9DyadicUpper
import QuadFormsKB.Literature.ConwaySloane.Section9Theorems
import QuadFormsKB.Literature.OMeara.Sec101A

open Matrix NumberField IsDedekindDomain WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices Wall

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- The Hessian of $f(x) = xAx^{\mathsf T}$ over $\mathbb Q_p$ is $2A$. -/
theorem hessian_csQ_map {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) :
    (csQ A).hessian.map (algebraMap ℚ Fv) = (2 : Fv) • A.map (Int.cast : ℤ → Fv) := by
  ext i j
  have h1 : (csQ A).hessian = (Cassels.Ch8Ex2.gramForm A).hessian.map (Int.castRingHom ℚ) :=
    QuadForm.hessian_map _ _
  rw [map_apply, h1, hessian_csForm hA, map_apply, Matrix.smul_apply, Matrix.smul_apply, map_apply]
  simp

/-- Entries of an element of $O(L_v)$, $L = \mathbb Z^n$, are integral. -/
theorem entries_le_one_of_mem_locStabV {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hd : A.det ≠ 0)
    {σ : orthGroup (csQ A) Fv} (hσ : σ ∈ locStabV (csQ A) v stdLat) :
    ∀ i j, Valued.v (((σ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) i j) ≤ 1 := by
  have hL : loc v (stdLat : Lat ℚ n).1 = std v := loc_intVec v
  have hs : σ ∈ stdStab (csQ A) v := (locStabV_eq_stdStab (csQ A) v stdLat hL).mp hσ
  have hn := (mem_stdStab_iff_matNorm_le_one (csQ A) v (csQ_nondegenerate hA hd) σ).mp hs
  exact fun i j => (le_matNorm _ i j).trans hn

/-- **From Wall determinants to the order of the automorphous numbers.** If every integral proper automorph $S$ of
$A$ has Wall determinants of square valuation, then every element of $\theta(O^+(L_2))$ has even order. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (2-adically automorphous numbers)"]
theorem even_log_of_wallCore {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hd : A.det ≠ 0)
    (hv2 : Valued.v (2 : Fv) = exp (-1 : ℤ))
    (hcore : ∀ S : Matrix (Fin n) (Fin n) Fv, (∀ i j, Valued.v (S i j) ≤ 1) →
      Sᵀ * A.map (Int.cast : ℤ → Fv) * S = A.map (Int.cast : ℤ → Fv) → S.det = 1 →
      ∀ (m : ℕ) (P R : Matrix (Fin n) (Fin m) Fv), IsWallFrame Fv S P R →
        ∃ γ : ℤᵐ⁰, Valued.v (Pᵀ * A.map (Int.cast : ℤ → Fv) * R).det = γ ^ 2)
    (B : Fvˣ) (hB : B ∈ localSpinorNormGroup (csQ A) (csQ_nondegenerate hA hd) v stdLat) :
    ∃ k : ℤ, Valued.v (B : Fv) = exp (2 * k) := by
  have hQ := csQ_nondegenerate hA hd
  obtain ⟨σ, ⟨hσL, hσS⟩, hσB⟩ := (mem_localSpinorNormGroup (csQ A) hQ v stdLat).mp hB
  set S := mat (csQ A) Fv σ
  have hS := entries_le_one_of_mem_locStabV hA hd hσL
  have hdet1 : S.det = 1 := hσS
  set Af := A.map (Int.cast : ℤ → Fv)
  have hH := hessian_csQ_map (v := v) hA
  have hSA : Sᵀ * Af * S = Af := by
    have h := mat_orth σ
    rw [hH] at h
    simp only [Matrix.mul_smul, Matrix.smul_mul] at h
    exact smul_right_injective _ (two_ne_zero : (2 : Fv) ≠ 0) h
  obtain ⟨m, P, R, hf⟩ := exists_wallFrame S
  obtain ⟨hθ, hne, hdetm⟩ := wall_formula hQ σ hf
  obtain ⟨γ, hγ⟩ := hcore S hS hSA hdet1 m P R hf
  have hm : Even m := by
    rw [hdet1] at hdetm
    exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : Fv) ≠ 1)).mp hdetm.symm
  obtain ⟨m', rfl⟩ := hm
  have hG : wallGram (csQ A) Fv P R = (2 : Fv) • (Pᵀ * Af * R) := by
    simp only [wallGram, hH, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  set d := (wallGram (csQ A) Fv P R).det
  have hd' : Valued.v d = exp (-(2 * m' : ℤ)) * γ ^ 2 := by
    simp only [d, hG, det_smul, Fintype.card_fin, map_mul, map_pow, hv2, hγ]
    rw [← WithZero.exp_nsmul]
    congr 2
    simp; ring
  have hγ0 : γ ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero, mul_zero, Valuation.zero_iff] at hd'
    exact hne hd'
  -- `B` and `d` have the same square class
  rw [hθ] at hσB
  rw [sqClassOf_of_ne_zero hne] at hσB
  set D : Fvˣ := Units.mk0 d hne
  have h1 : SqClass.mk (B⁻¹ * D) = 1 := by
    rw [SqClass.mk_mul, hσB, ← SqClass.mk_mul, inv_mul_cancel]
    rfl
  obtain ⟨y, hy⟩ := (SqClass.mk_eq_one_iff (B⁻¹ * D)).mp h1
  have hBe : (B : Fv) = d * ((y : Fv) ^ 2)⁻¹ := by
    have : B = D * (y ^ 2)⁻¹ := by rw [hy]; group
    rw [this]; simp [D]
  have hsv : Valued.v (y : Fv) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  refine ⟨log γ - m' - log (Valued.v (y : Fv)), ?_⟩
  rw [hBe, map_mul, map_inv₀, map_pow, hd', ← exp_log hγ0, ← exp_log hsv, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul,
    ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_add, WithZero.log_exp, WithZero.log_exp]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  push_cast
  ring

/-- **The $2$-adically automorphous numbers of an even unimodular form have even order** (unconditional): if
$\det A$ is a $2$-adic unit and every diagonal entry $A_{ii}$ is even, every element of $\theta(O^+(L_2))$ has even
order. (Conway–Sloane derive this from Theorem 18 at $p = 2$: the root vectors of such a form have norms
$2\cdot$unit.) -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18 and the algorithm, p. 391 (even unimodular case)"]
theorem even_log_of_evenUnimodular {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hd : A.det ≠ 0)
    (hv2 : Valued.v (2 : Fv) = exp (-1 : ℤ)) (hdetA : Valued.v ((A.det : ℤ) : Fv) = 1)
    (heven : ∀ i, Even (A i i)) (B : Fvˣ)
    (hB : B ∈ localSpinorNormGroup (csQ A) (csQ_nondegenerate hA hd) v stdLat) :
    ∃ k : ℤ, Valued.v (B : Fv) = exp (2 * k) :=
  even_log_of_wallCore hA hd hv2
    (fun S hS hSA _ m P R hf => EvenUnimodular.exists_sq_valued_wallDet A hA hdetA heven S hS hSA hf) B hB

end QuadFormsKB.ConwaySloane
