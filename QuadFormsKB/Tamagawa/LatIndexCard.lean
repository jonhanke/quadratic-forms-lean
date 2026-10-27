/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.SiegelClassical
import QuadFormsKB.Tamagawa.LatCovolNF
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# The index of a lattice is the module index
**Layer:** $F$ a number field (any class number); $L$ an $\mathcal O_F$-lattice in $F^N$ (`Lat F N`, any Steinitz class).

gd defined $\mathrm{latIndex}(L) = \prod_\mathfrak p\|\det A_\mathfrak p\|_\mathfrak p$ ($A_\mathfrak p$ a local basis of $L_\mathfrak p$), the volume of $L$
for the product of the Haar measures with $\mathrm{vol}(\mathfrak o_\mathfrak p^N) = 1$. This file identifies it with the module
index (O'Meara 1963, §81D, p. 216, the index $(L : K)$ through the invariant factors):

* **`latIndex_eq_inv_covol`**: for a presentation $L = P\,(\bigoplus_i\mathfrak a_ie_i)$ ($P \in \mathrm{GL}_N(F)$, $\mathfrak a_i$ fractional
  ideals; `glImage P (diagLat 𝔞)`), $\mathrm{latIndex}(L) = \big(|N_{F/\mathbb Q}\det P|\prod_iN(\mathfrak a_i)\big)^{-1}$ = `(covol P 𝔞)⁻¹`,
  i.e. $N(\mathfrak a_L)^{-1}$ for the index ideal $\mathfrak a_L = (\det P)\prod_i\mathfrak a_i$;
* **`exists_presentation`**: every lattice has one (Steinitz, `exists_eq_glImage_steinitzLat`);
* **`latIndex_mul_relIndex`**: for lattices $L \subseteq M$, $\mathrm{latIndex}(M) = [M : L]\cdot\mathrm{latIndex}(L)$
  (multiplicativity of the index; with LatCovol's `relIndex_presGrp`);
* **`latIndex_eq_inv_relIndex`**, **`latIndex_eq_inv_card`**: for $L \subseteq \mathcal O_F^N$,
  $\mathrm{latIndex}(L) = [\mathcal O_F^N : L]^{-1} = 1/\#(\mathcal O_F^N/L)$;
* **`latIndex_eq_relIndex_div`** (general $L$): $\mathrm{latIndex}(L) = [L : L\cap\mathcal O_F^N]\,/\,[\mathcal O_F^N : L\cap\mathcal O_F^N]$;
* **`latIndex_coordLat_mul_relIndex`** ($V$-version): for lattices $L \subseteq M$ in an $F$-space $V$ and any basis $e$,
  $\mathrm{latIndex}(e^*M) = [M : L]\cdot\mathrm{latIndex}(e^*L)$, i.e. $\prod_\mathfrak p\|\det(L_\mathfrak p/M_\mathfrak p)\|_\mathfrak p = [M:L]^{-1}$.

*Proof of `latIndex_eq_inv_covol`.* Write $\mathfrak a_i = c_i\cdot(x_{i1}, \dots, x_{ik})$ with $x_{ij} \in \mathcal O_F \setminus 0$
(`exists_gens`). At $\mathfrak p$ pick $j$ with $\|x_{ij}\|_\mathfrak p$ maximal; then $a_i = c_ix_{ij}$ generates $\mathfrak a_i\mathfrak o_\mathfrak p$
(ultrametric inequality), so $P\,\mathrm{diag}(a_i)$ is a local basis and $\mathrm{locIndex}_\mathfrak p(L) = \|\det P\|_\mathfrak p\prod_i\|c_i\|_\mathfrak p\max_j\|x_{ij}\|_\mathfrak p$
(`locIndex_glImage_diagLat`). The product over $\mathfrak p$ is computed by the product formula
(`FinitePlace.prod_eq_inv_abs_norm`) and Mathlib's height identity $N(x_{i1}, \dots, x_{ik})\cdot\prod_\mathfrak p\max_j\|x_{ij}\|_\mathfrak p = 1$
(`absNorm_mul_finprod_finitePlace_eq_one`). No structure theory of modules over Dedekind domains is used.

Sources: O'Meara 1963, §81D, 81:11–81:12, pp. 214–216 (invariant factors, the index $(L:K)$), and §82E, p. 228 (volume); Neukirch 1999, Ch. III §1 (product formula)
[unverified].
-/

open NumberField IsDedekindDomain Module Matrix
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.SiegelSpace

open QuadFormsKB.Lattices QuadFormsKB.LatCovol QuadFormsKB.SphericalUnfold QuadFormsKB.IdeleClass
open QuadFormsKB.Tamagawa.SiegelLat

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

/-! ### Diagonal and presented lattices -/

/-- **The diagonal lattice** $\bigoplus_i\mathfrak a_ie_i = \{\xi : \xi_i \in \mathfrak a_i\}$ for fractional ideals $\mathfrak a_i$. -/
def diagLat (𝔞 : Fin N → FracIdeal F) : Submodule (𝓞 F) (Fin N → F) where
  carrier := {ξ | LatMem 𝔞 ξ}
  add_mem' hξ hη i := Submodule.add_mem _ (hξ i) (hη i)
  zero_mem' _ := Submodule.zero_mem _
  smul_mem' c _ hξ i := Submodule.smul_mem ((𝔞 i : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) c (hξ i)

theorem mem_diagLat {𝔞 : Fin N → FracIdeal F} {ξ : Fin N → F} :
    ξ ∈ diagLat 𝔞 ↔ ∀ i, ξ i ∈ (𝔞 i : FractionalIdeal (𝓞 F)⁰ F) := Iff.rfl

/-- The presented lattice $P(\bigoplus_i\mathfrak a_ie_i)$ is LatCovol's `presGrp P 𝔞` as an additive group. -/
theorem glImage_diagLat_toAddSubgroup (P : GL (Fin N) F) (𝔞 : Fin N → FracIdeal F) :
    (glImage P (diagLat 𝔞)).toAddSubgroup = presGrp P.val 𝔞 := by
  ext y
  simp only [Submodule.mem_toAddSubgroup, mem_glImage, mem_presGrp]
  constructor
  · rintro ⟨ξ, hξ, rfl⟩; exact ⟨ξ, hξ, rfl⟩
  · rintro ⟨ξ, hξ, rfl⟩; exact ⟨ξ, hξ, rfl⟩

/-! ### Generators of a fractional ideal -/

/-- **A fractional ideal is $c\cdot(x_1, \dots, x_k)$** with $c \ne 0$ and $x_j \in \mathcal O_F \setminus 0$, $k \ge 1$; then
$N(\mathfrak a) = |N_{F/\mathbb Q}(c)|\,N(x_1, \dots, x_k)$. -/
theorem exists_gens (𝔞 : FracIdeal F) :
    ∃ (c : F) (k : ℕ) (x : Fin k → 𝓞 F), c ≠ 0 ∧ 0 < k ∧ (∀ j, x j ≠ 0) ∧
      (∀ y : F, y ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ↔
        ∃ r : Fin k → 𝓞 F, y = c * algebraMap (𝓞 F) F (∑ j, r j * x j)) ∧
      idealNorm F 𝔞 = |((Algebra.norm ℚ c : ℚ) : ℝ)| * ((Ideal.span (Set.range x)).absNorm : ℝ) := by
  classical
  obtain ⟨a, I, ha, h𝔞⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (𝔞 : FractionalIdeal (𝓞 F)⁰ F)
  have ha' : algebraMap (𝓞 F) F a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ha
  have hI : I ≠ ⊥ := by
    rintro rfl; apply 𝔞.ne_zero; rw [h𝔞, FractionalIdeal.coeIdeal_bot, mul_zero]
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  set t := s.filter (· ≠ 0)
  have hts : Ideal.span (↑t : Set (𝓞 F)) = I := by
    rw [← hs]
    refine le_antisymm (Ideal.span_mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
      (Ideal.span_le.mpr fun z hz => ?_)
    by_cases h : z = 0
    · rw [h]; exact zero_mem _
    · exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hz, h⟩))
  set x : Fin t.card → 𝓞 F := fun i => (t.equivFin.symm i : 𝓞 F)
  have hrange : Set.range x = ↑t := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩; exact (t.equivFin.symm i).2
    · intro hz; exact ⟨t.equivFin ⟨z, hz⟩, by simp [x]⟩
  have hspan : Ideal.span (Set.range x) = I := by rw [hrange, hts]
  have hk : 0 < t.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr fun h => hI (by
    rw [← hts, h, Finset.coe_empty, Ideal.span_empty]))
  refine ⟨(algebraMap (𝓞 F) F a)⁻¹, t.card, x, inv_ne_zero ha', hk,
    fun j => (Finset.mem_filter.mp (t.equivFin.symm j).2).2, fun y => ?_, ?_⟩
  · rw [h𝔞, FractionalIdeal.mem_singleton_mul]
    constructor
    · rintro ⟨y', hy', rfl⟩
      obtain ⟨z, hz, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
      rw [← hspan, Ideal.mem_span_range_iff_exists_fun] at hz
      obtain ⟨r, rfl⟩ := hz
      exact ⟨r, rfl⟩
    · rintro ⟨r, rfl⟩
      refine ⟨_, (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, ?_, rfl⟩, rfl⟩
      rw [← hspan, Ideal.mem_span_range_iff_exists_fun]
      exact ⟨r, rfl⟩
  · unfold idealNorm
    rw [h𝔞, map_mul, FractionalIdeal.absNorm_span_singleton, FractionalIdeal.coeIdeal_absNorm, hspan]
    push_cast
    rfl

/-! ### The local index of a presented lattice -/

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

theorem exists_max_norm {k : ℕ} (hk : 0 < k) (x : Fin k → 𝓞 F) :
    ∃ j, ∀ j', ‖algebraMap F Fv (algebraMap (𝓞 F) F (x j'))‖ ≤ ‖algebraMap F Fv (algebraMap (𝓞 F) F (x j))‖ := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ
    (fun j => ‖algebraMap F Fv (algebraMap (𝓞 F) F (x j))‖) (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
  exact ⟨j, fun j' => hj j' (Finset.mem_univ _)⟩

/-- **The ultrametric bound**: every element of $c\cdot(x_1, \dots, x_k)$ has $\|y\|_\mathfrak p \le \|c\,x_j\|_\mathfrak p$ for $j$ maximizing
$\|x_j\|_\mathfrak p$. -/
theorem norm_le_of_mem_gens {k : ℕ} {c : F} {x : Fin k → 𝓞 F} {S : Set F}
    (hmem : ∀ y : F, y ∈ S ↔ ∃ r : Fin k → 𝓞 F, y = c * algebraMap (𝓞 F) F (∑ j, r j * x j)) {j : Fin k}
    (hj : ∀ j', ‖algebraMap F Fv (algebraMap (𝓞 F) F (x j'))‖ ≤ ‖algebraMap F Fv (algebraMap (𝓞 F) F (x j))‖)
    {y : F} (hy : y ∈ S) :
    ‖algebraMap F Fv y‖ ≤ ‖algebraMap F Fv (c * algebraMap (𝓞 F) F (x j))‖ := by
  obtain ⟨r, rfl⟩ := (hmem y).mp hy
  rw [map_mul, map_mul, norm_mul, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [map_sum, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  rw [map_mul, map_mul, norm_mul]
  have hr : ‖algebraMap F Fv (algebraMap (𝓞 F) F (r i))‖ ≤ 1 := by
    rw [← IsScalarTower.algebraMap_apply]
    exact Valued.toNormedField.norm_le_one_iff.mpr (valued_int_le_one v (r i))
  calc _ ≤ 1 * ‖algebraMap F Fv (algebraMap (𝓞 F) F (x i))‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hj i

/-- **The local index of a presented lattice**: if $a_i \in \mathfrak a_i$ has maximal $\|\cdot\|_\mathfrak p$ on $\mathfrak a_i$, then
$P\,\mathrm{diag}(a_i)$ is a local basis of $L = P(\bigoplus_i\mathfrak a_ie_i)$ at $\mathfrak p$ and
$\mathrm{locIndex}_\mathfrak p(L) = \|\det P\|_\mathfrak p\prod_i\|a_i\|_\mathfrak p$. -/
theorem locIndex_glImage_diagLat (P : GL (Fin N) F) (𝔞 : Fin N → FracIdeal F) (L : Lat F N)
    (hL : L.1 = glImage P (diagLat 𝔞)) (a : Fin N → F) (ha0 : ∀ i, a i ≠ 0)
    (ha : ∀ i, a i ∈ (𝔞 i : FractionalIdeal (𝓞 F)⁰ F))
    (hmax : ∀ i, ∀ y ∈ (𝔞 i : FractionalIdeal (𝓞 F)⁰ F), ‖algebraMap F Fv y‖ ≤ ‖algebraMap F Fv (a i)‖) :
    locIndex v L = ‖algebraMap F Fv P.val.det‖ * ∏ i, ‖algebraMap F Fv (a i)‖ := by
  have hD : IsUnit (diagonal a).det := isUnit_iff_ne_zero.mpr (by
    rw [det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun i _ => ha0 i)
  set D : GL (Fin N) F := Matrix.nonsingInvUnit (diagonal a) hD
  have hDv : D.val = diagonal a := rfl
  have hloc : loc v (Lattices.latOf (P * D)) = loc v L.1 := by
    rw [hL, latOf_mul, loc_glImage, loc_glImage]
    congr 1
    apply le_antisymm
    · apply loc_mono
      intro y hy
      obtain ⟨z, hz, rfl⟩ := mem_glImage.mp hy
      intro i
      rw [hDv, mulVec_diagonal]
      obtain ⟨w, hw⟩ := (mem_intVec.mp hz) i
      rw [← hw, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ w (ha i)
    · rw [Lattices.latOf, loc_glImage, loc_intVec]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨ξ, hξ, rfl⟩
      refine mem_locAct.mpr ⟨fun i => algebraMap F Fv (ξ i) / algebraMap F Fv (a i), ?_, ?_⟩
      · rw [mem_ball]
        intro i
        have hai : 0 < ‖algebraMap F Fv (a i)‖ := norm_pos_iff.mpr ((map_ne_zero _).mpr (ha0 i))
        have h1 : ‖algebraMap F Fv (ξ i) / algebraMap F Fv (a i)‖ ≤ 1 := by
          rw [norm_div]; exact (div_le_one hai).mpr (hmax i _ (hξ i))
        have := Valued.toNormedField.norm_le_one_iff.mp h1
        simpa using this
      · funext i
        rw [show (Matrix.GeneralLinearGroup.map (algebraMap F Fv) D).val = (diagonal a).map (algebraMap F Fv) from rfl,
          diagonal_map (map_zero _), mulVec_diagonal, locVec_apply]
        field_simp [(map_ne_zero (algebraMap F Fv)).mpr (ha0 i)]
  rw [locIndex_eq v hloc, Units.val_mul, det_mul, map_mul, norm_mul, hDv, det_diagonal, map_prod, norm_prod]

end Local

/-! ### The global index -/

theorem norm_algebraMap_eq_mk (v : HeightOneSpectrum (𝓞 F)) (y : F) :
    ‖algebraMap F (v.adicCompletion F) y‖ = FinitePlace.equivHeightOneSpectrum.symm v y := by
  rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.embedding_apply]
  rfl

/-- **The index of a presented lattice** (cf. O'Meara 1963, §81D, p. 216): for $L = P(\bigoplus_i\mathfrak a_ie_i)$,
$$\mathrm{latIndex}(L) = \prod_\mathfrak p\|\det A_\mathfrak p\|_\mathfrak p = \Big(|N_{F/\mathbb Q}(\det P)|\prod_iN(\mathfrak a_i)\Big)^{-1} = N(\mathfrak a_L)^{-1},$$
$\mathfrak a_L = (\det P)\prod_i\mathfrak a_i$ the index ideal of $L$ relative to $\mathcal O_F^N$. -/
@[kb "omeara1963" "§81D, p. 216 ((L:K) via invariant factors); §103, 103:1, p. 305"]
theorem latIndex_eq_inv_covol (L : Lat F N) (P : GL (Fin N) F) (𝔞 : Fin N → FracIdeal F)
    (hL : L.1 = glImage P (diagLat 𝔞)) : latIndex L = (covol P.val 𝔞)⁻¹ := by
  classical
  choose c k x hc hk hx0 hmem hnorm using fun i => exists_gens (𝔞 i)
  choose J hJ using fun (v : HeightOneSpectrum (𝓞 F)) i => exists_max_norm v (hk i) (x i)
  set e := (FinitePlace.equivHeightOneSpectrum (K := F)).symm
  have hx0' : ∀ i j, algebraMap (𝓞 F) F (x i j) ≠ 0 := fun i j =>
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (hx0 i j)
  have hdet : P.val.det ≠ 0 := (P.isUnit.map Matrix.detMonoidHom).ne_zero
  -- the local factors, as functions of the finite place
  have hloc : ∀ v, locIndex v L = e v P.val.det * ∏ i, (e v (c i) * ⨆ j, e v (algebraMap (𝓞 F) F (x i j))) := by
    intro v
    rw [locIndex_glImage_diagLat v P 𝔞 L hL (fun i => c i * algebraMap (𝓞 F) F (x i (J v i)))
      (fun i => mul_ne_zero (hc i) (hx0' i _))
      (fun i => (hmem i _).mpr ⟨Pi.single (J v i) 1, by simp [Pi.single_apply]⟩)
      (fun i y hy => norm_le_of_mem_gens v (hmem i) (hJ v i) hy)]
    rw [norm_algebraMap_eq_mk]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_mul, norm_mul, norm_algebraMap_eq_mk, norm_algebraMap_eq_mk]
    congr 1
    refine le_antisymm (le_ciSup (f := fun j => e v (algebraMap (𝓞 F) F (x i j))) (Set.finite_range _).bddAbove (J v i)) ?_
    have : Nonempty (Fin (k i)) := ⟨⟨0, hk i⟩⟩
    exact ciSup_le fun j => by rw [← norm_algebraMap_eq_mk, ← norm_algebraMap_eq_mk]; exact hJ v i j
  have hf1 : Function.HasFiniteMulSupport fun w : FinitePlace F => w P.val.det :=
    FinitePlace.hasFiniteMulSupport hdet
  have hf2 : ∀ i, Function.HasFiniteMulSupport fun w : FinitePlace F => w (c i) :=
    fun i => FinitePlace.hasFiniteMulSupport (hc i)
  have hf3 : ∀ i, Function.HasFiniteMulSupport fun w : FinitePlace F => ⨆ j, w (algebraMap (𝓞 F) F (x i j)) := by
    intro i
    have : Nonempty (Fin (k i)) := ⟨⟨0, hk i⟩⟩
    exact Function.HasFiniteMulSupport.iSup fun j => FinitePlace.hasFiniteMulSupport (hx0' i j)
  have hsup : ∀ i, ∏ᶠ w : FinitePlace F, ⨆ j, w (algebraMap (𝓞 F) F (x i j)) =
      ((Ideal.span (Set.range (x i))).absNorm : ℝ)⁻¹ := by
    intro i
    have hne : x i ≠ 0 := fun h => hx0 i ⟨0, hk i⟩ (congrFun h _)
    exact eq_inv_of_mul_eq_one_right (absNorm_mul_finprod_finitePlace_eq_one hne)
  have hf23 : ∀ i, Function.HasFiniteMulSupport fun w : FinitePlace F =>
      w (c i) * ⨆ j, w (algebraMap (𝓞 F) F (x i j)) := fun i => (hf2 i).mul (hf3 i)
  have hf4 : Function.HasFiniteMulSupport fun w : FinitePlace F =>
      ∏ i, (w (c i) * ⨆ j, w (algebraMap (𝓞 F) F (x i j))) :=
    Function.HasFiniteMulSupport.prod (f := fun i (w : FinitePlace F) => w (c i) * ⨆ j, w (algebraMap (𝓞 F) F (x i j)))
      hf23 _
  unfold latIndex
  rw [finprod_congr hloc, finprod_comp_equiv e (f := fun w : FinitePlace F =>
      w P.val.det * ∏ i, (w (c i) * ⨆ j, w (algebraMap (𝓞 F) F (x i j)))),
    finprod_mul_distrib hf1 hf4,
    finprod_prod_comm _ (fun (w : FinitePlace F) i => w (c i) * ⨆ j, w (algebraMap (𝓞 F) F (x i j)))
      (fun i _ => hf23 i), FinitePlace.prod_eq_inv_abs_norm hdet]
  simp_rw [finprod_mul_distrib (hf2 _) (hf3 _), FinitePlace.prod_eq_inv_abs_norm (hc _), hsup]
  rw [covol, mul_inv, ← Finset.prod_inv_distrib]
  congr 1
  · push_cast; rfl
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [hnorm i, mul_inv]
    push_cast; rfl

/-! ### Every lattice is presented (Steinitz) -/

/-- **Every lattice has a presentation** $L = P(\bigoplus_i\mathfrak a_ie_i)$ (Steinitz 1911; O'Meara 81:5, p. 212), from
`exists_eq_glImage_steinitzLat` ($\mathfrak a = (\mathcal O_F, \dots, \mathcal O_F, \mathfrak c)$). -/
@[kb "omeara1963" "§81A, 81:5, p. 212 (Steinitz form of a lattice)"]
theorem exists_presentation (L : Lat F N) :
    ∃ (P : GL (Fin N) F) (𝔞 : Fin N → FracIdeal F), L.1 = glImage P (diagLat 𝔞) := by
  classical
  rcases N with _ | m
  · refine ⟨1, Fin.elim0, ?_⟩
    ext y
    rw [show y = 0 from Subsingleton.elim _ _]
    simp only [Submodule.zero_mem]
  · obtain ⟨γ, 𝔠, h⟩ := Steinitz.exists_eq_glImage_steinitzLat L.2
    have hS : (Steinitz.steinitzLat (m := m) 𝔠).IsLattice F := by
      have := glImage_isLattice γ⁻¹ L.2
      rwa [h, ← glImage_mul, inv_mul_cancel, glImage_one] at this
    set π : (Fin (m + 1) → F) →ₗ[𝓞 F] F :=
      (LinearMap.proj (R := F) (φ := fun _ : Fin (m + 1) => F) (Fin.last m)).restrictScalars (𝓞 F)
    have hsingle : ∀ c ∈ 𝔠, (Pi.single (Fin.last m) c : Fin (m + 1) → F) ∈ Steinitz.steinitzLat (m := m) 𝔠 :=
      fun c hc => ⟨fun i => ⟨0, by simp [Fin.castSucc_ne_last]⟩, by simpa using hc⟩
    have h𝔠 : 𝔠 = (Steinitz.steinitzLat (m := m) 𝔠).map π := by
      ext c
      constructor
      · intro hc; exact ⟨_, hsingle c hc, by simp [π]⟩
      · rintro ⟨y, hy, rfl⟩; exact hy.2
    have hfg : 𝔠.FG := by rw [h𝔠]; exact hS.fg.map π
    have hne : 𝔠 ≠ ⊥ := by
      intro h0
      have hle : Submodule.span F (Steinitz.steinitzLat (m := m) 𝔠 : Set (Fin (m + 1) → F)) ≤
          LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : Fin (m + 1) => F) (Fin.last m)) := by
        refine Submodule.span_le.mpr fun y hy => ?_
        have := hy.2
        rw [h0, Submodule.mem_bot] at this
        exact this
      rw [hS.span_eq_top] at hle
      have := hle (Submodule.mem_top (x := (Pi.single (Fin.last m) 1 : Fin (m + 1) → F)))
      simp at this
    set I : FractionalIdeal (𝓞 F)⁰ F := ⟨𝔠, FractionalIdeal.isFractional_of_fg hfg⟩
    have hI : I ≠ 0 := by
      intro h0
      apply hne
      have := congrArg (fun J : FractionalIdeal (𝓞 F)⁰ F => (J : Submodule (𝓞 F) F)) h0
      simpa [I] using this
    refine ⟨γ, fun i => if i = Fin.last m then Units.mk0 I hI else 1, ?_⟩
    rw [h]
    congr 1
    ext ξ
    rw [mem_diagLat, Fin.forall_fin_succ']
    simp only [Fin.castSucc_ne_last, ite_false, ite_true, Units.val_one, Units.val_mk0]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun i => (FractionalIdeal.mem_one_iff _).mpr (h1 i), h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun i => (FractionalIdeal.mem_one_iff _).mp (h1 i), h2⟩

/-! ### The index as a module index -/

theorem relIndex_mul_covol {L M : Lat F N} (hLM : L.1 ≤ M.1) :
    ∃ (P P' : GL (Fin N) F) (𝔞 𝔞' : Fin N → FracIdeal F), L.1 = glImage P (diagLat 𝔞) ∧ M.1 = glImage P' (diagLat 𝔞') ∧
      (L.1.toAddSubgroup.relIndex M.1.toAddSubgroup : ℝ) * covol P'.val 𝔞' = covol P.val 𝔞 := by
  obtain ⟨P, 𝔞, hP⟩ := exists_presentation L
  obtain ⟨P', 𝔞', hP'⟩ := exists_presentation M
  refine ⟨P, P', 𝔞, 𝔞', hP, hP', ?_⟩
  have hle : presGrp P.val 𝔞 ≤ presGrp P'.val 𝔞' := by
    rw [← glImage_diagLat_toAddSubgroup, ← glImage_diagLat_toAddSubgroup, ← hP, ← hP']
    exact fun y hy => hLM hy
  rw [hP, hP', glImage_diagLat_toAddSubgroup, glImage_diagLat_toAddSubgroup]
  exact relIndex_presGrp (P.isUnit.map Matrix.detMonoidHom).ne_zero (P'.isUnit.map Matrix.detMonoidHom).ne_zero hle

/-- **Multiplicativity of the index** (O'Meara 1963, §81D, p. 216): for lattices $L \subseteq M$,
$\mathrm{latIndex}(M) = [M : L]\cdot\mathrm{latIndex}(L)$, i.e. $\prod_\mathfrak p\|\det(L_\mathfrak p/M_\mathfrak p)\|_\mathfrak p = [M : L]^{-1}$. -/
@[kb "omeara1963" "§81D, p. 216"]
theorem latIndex_mul_relIndex {L M : Lat F N} (hLM : L.1 ≤ M.1) :
    latIndex M = (L.1.toAddSubgroup.relIndex M.1.toAddSubgroup : ℝ) * latIndex L := by
  obtain ⟨P, P', 𝔞, 𝔞', hP, hP', h⟩ := relIndex_mul_covol hLM
  rw [latIndex_eq_inv_covol L P 𝔞 hP, latIndex_eq_inv_covol M P' 𝔞' hP', ← h]
  have h1 := (covol_pos P'.val (P'.isUnit.map Matrix.detMonoidHom).ne_zero 𝔞').ne'
  have h2 : (L.1.toAddSubgroup.relIndex M.1.toAddSubgroup : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h; exact (covol_pos P.val (P.isUnit.map Matrix.detMonoidHom).ne_zero 𝔞).ne' h.symm
  field_simp

theorem relIndex_ne_zero {L M : Lat F N} (hLM : L.1 ≤ M.1) : L.1.toAddSubgroup.relIndex M.1.toAddSubgroup ≠ 0 := by
  obtain ⟨P, P', 𝔞, 𝔞', -, -, h⟩ := relIndex_mul_covol hLM
  intro h0
  rw [h0, Nat.cast_zero, zero_mul] at h
  exact (covol_pos P.val (P.isUnit.map Matrix.detMonoidHom).ne_zero 𝔞).ne' h.symm

/-- **`latIndex` is the inverse module index** for $L \subseteq \mathcal O_F^N$: $\mathrm{latIndex}(L) = [\mathcal O_F^N : L]^{-1}$. -/
@[kb "omeara1963" "§81D, p. 216"]
theorem latIndex_eq_inv_relIndex {L : Lat F N} (hL : L.1 ≤ (stdLat F N).1) :
    latIndex L = ((L.1.toAddSubgroup.relIndex (stdLat F N).1.toAddSubgroup : ℕ) : ℝ)⁻¹ := by
  have h := latIndex_mul_relIndex hL
  rw [latIndex_std] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- **`latIndex` as a cardinality**: for $L \subseteq \mathcal O_F^N$, $\mathrm{latIndex}(L) = 1/\#(\mathcal O_F^N/L)$. -/
theorem latIndex_eq_inv_card {L : Lat F N} (hL : L.1 ≤ (stdLat F N).1) :
    latIndex L = ((Nat.card ((stdLat F N).1.toAddSubgroup ⧸
      L.1.toAddSubgroup.addSubgroupOf (stdLat F N).1.toAddSubgroup) : ℕ) : ℝ)⁻¹ :=
  latIndex_eq_inv_relIndex hL

/-- **`latIndex` as a generalized module index** for every lattice $L$:
$\mathrm{latIndex}(L) = [L : L\cap\mathcal O_F^N]\,/\,[\mathcal O_F^N : L\cap\mathcal O_F^N]$ (Mathlib's `relIndex`: $H$`.relIndex`$K = [K : H\cap K]$). -/
@[kb "omeara1963" "§81D, p. 216; cassels1978 Ch. 7, §3, p. 104 (relative determinant); Ch. 11, Lemma 2.1, p. 206"]
theorem latIndex_eq_relIndex_div (L : Lat F N) :
    latIndex L = ((stdLat F N).1.toAddSubgroup.relIndex L.1.toAddSubgroup : ℝ) /
      (L.1.toAddSubgroup.relIndex (stdLat F N).1.toAddSubgroup : ℝ) := by
  obtain ⟨d, hd, h1, h2⟩ := exists_global_bounds L.2
  set K : Lat F N := ⟨L.1 ⊓ (stdLat F N).1, isLattice_of_global_bounds hd
    (fun x hx => ⟨h1 x hx, intVec.smul_mem d hx⟩) (fun x hx => intVec.smul_mem d hx.2)⟩
  have h1 := latIndex_mul_relIndex (L := K) (M := L) inf_le_left
  have h2 := latIndex_mul_relIndex (L := K) (M := stdLat F N) inf_le_right
  rw [latIndex_std] at h2
  have hK : K.1.toAddSubgroup = L.1.toAddSubgroup ⊓ (stdLat F N).1.toAddSubgroup := rfl
  rw [hK, AddSubgroup.inf_relIndex_left] at h1
  rw [hK, AddSubgroup.inf_relIndex_right] at h2
  have hne : (L.1.toAddSubgroup.relIndex (stdLat F N).1.toAddSubgroup : ℝ) ≠ 0 := by
    have := relIndex_ne_zero (L := K) (M := stdLat F N) inf_le_right
    rw [hK, AddSubgroup.inf_relIndex_right] at this
    exact_mod_cast this
  rw [h1, eq_div_iff hne, mul_assoc,
    mul_comm (latIndex K), ← h2, mul_one]

/-! ### The $V$-version -/

section AbstractSpace

variable {V : Type*} [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] {n : ℕ}

/-- **The index of two lattices in a quadratic space** (basis-free): for $\mathcal O_F$-lattices $L \subseteq M$ in $V$ and any
basis $e$, $\mathrm{latIndex}(e^*M) = [M : L]\cdot\mathrm{latIndex}(e^*L)$, i.e. $\prod_\mathfrak p\|\det(L_\mathfrak p/M_\mathfrak p)\|_\mathfrak p = [M : L]^{-1}$. -/
@[kb "omeara1963" "§81D, p. 216"]
theorem latIndex_coordLat_mul_relIndex (e : Basis (Fin n) F V) {L M : Submodule (𝓞 F) V} [L.IsLattice F]
    [M.IsLattice F] (hLM : L ≤ M) :
    latIndex (coordLat e M) = (L.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) * latIndex (coordLat e L) := by
  have hle : (coordLat e L).1 ≤ (coordLat e M).1 := Submodule.map_mono hLM
  rw [latIndex_mul_relIndex hle]
  congr 2
  have hf : Function.Injective (e.equivFun.toLinearMap.restrictScalars (𝓞 F)).toAddMonoidHom := e.equivFun.injective
  have hmap : ∀ K : Submodule (𝓞 F) V, (coordLatSub e K).toAddSubgroup =
      K.toAddSubgroup.map (e.equivFun.toLinearMap.restrictScalars (𝓞 F)).toAddMonoidHom := fun K => rfl
  show (coordLatSub e L).toAddSubgroup.relIndex (coordLatSub e M).toAddSubgroup = _
  rw [hmap, hmap, AddSubgroup.relIndex_map_map_of_injective _ _ hf]

end AbstractSpace

end QuadFormsKB.Tamagawa.SiegelSpace
