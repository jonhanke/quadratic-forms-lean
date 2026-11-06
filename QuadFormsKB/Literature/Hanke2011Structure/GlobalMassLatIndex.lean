/-
# Hanke 2011, Def. 6.1 for every lattice: the volume $\mu_f(SO(\hat L))$ of an arbitrary lattice stabilizer

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), Def. 6.1 and Theorem 6.2, pp. 25–26.

**Setting.** $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $n\ge1$ variables, $V = (F^n, Q)$, $Q = Q_0\otimes F$,
$L$ an $\mathcal O_F$-valued lattice on $V$ (any Steinitz class), $\mu_f$ = `muFin Q₀ 1` Weil's Haar measure on $SO(V)(\mathbb A_f)$,
normalized by $\mu_f(SO(\hat{\mathcal O}_F^n)) = \prod_{\mathfrak p}\alpha_{\mathfrak p}(Q_0, Q_0)$ (`muFin_KSO`, `finFactor`).

**Proves** (unconditional, standard axioms only)
* `relIndex_restrictedPi_of_le`: indices of "product" subgroups of a restricted product whose local factors agree outside a
  finite set $S$ are products over $S$ (a variant of `relIndex_restrictedPi`, whose local factors must be the reference
  subgroups outside $S$);
* `relRatio_inf_eq_of_relIndex_two`: $r(N\cap A, N\cap B) = r(A, B)$ when $[A : N\cap A] = [B : N\cap B] = 2$,
  $r(A, B) = [A : A\cap B]/[B : A\cap B]$ (`relRatio`);
* `exists_stabLat_det_neg_one`: $O(L_{\mathfrak p})$ contains an improper isometry at every finite $\mathfrak p$ (a reflection of
  the integral local form $Q\circ\gamma$, $L_{\mathfrak p} = \gamma\,\mathfrak o_{\mathfrak p}^n$; O'Meara 91:4, dyadic included);
* **`relRatio_KSOLat`**: $r(SO(\hat L), SO(\hat{\mathcal O}_F^n)) = r(O(\hat L), O(\hat{\mathcal O}_F^n))$;
* **`muFin_KSOLat`**: $\mu_f(SO(\hat L)) = r(O(\hat L), O(\hat{\mathcal O}_F^n))\cdot\prod_{\mathfrak p}\alpha_{\mathfrak p}(Q_0,Q_0)$.
-/
import QuadFormsKB.Literature.Hanke2011Structure.GlobalMassLatK

namespace QuadFormsKB.Hanke2011Structure

open MeasureTheory Measure MulAction Set NumberField IsDedekindDomain Matrix
open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite
open scoped ENNReal RestrictedProduct

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

/-! ### Indices in a restricted product -/

section RestrictedIndex

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] {K : ∀ i, Subgroup (G i)}

/-- **Indices of "product" subgroups of a restricted product.** If $A = \{h : h_i \in A_i\ \forall i\}$ and
$B = \{h : h_i \in B_i\ \forall i\}$ with $A_i \le B_i$ outside a finite set $S$, then
$[A : A \cap B] = \prod_{i\in S}[A_i : A_i\cap B_i]$. -/
theorem relIndex_restrictedPi_of_le (S : Finset ι) (A' B' : ∀ i, Subgroup (G i)) (hAB : ∀ i ∉ S, A' i ≤ B' i)
    (A B : Subgroup (Πʳ i, [G i, K i]))
    (hAm : ∀ h, h ∈ A ↔ ∀ i, h i ∈ A' i) (hBm : ∀ h, h ∈ B ↔ ∀ i, h i ∈ B' i) :
    B.relIndex A = ∏ i ∈ S, (B' i).relIndex (A' i) := by
  classical
  let f : A →* ((i : S) → A' i) :=
    { toFun := fun a i => ⟨(a : Πʳ i, [G i, K i]) i, (hAm a).mp a.2 i⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    intro x
    let y : Πʳ i, [G i, K i] := ⟨fun i => if hi : i ∈ S then (x ⟨i, hi⟩ : G i) else 1, by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with i hi
      simp only [show i ∉ S from hi, ↓reduceDIte]; exact (K i).one_mem⟩
    have hy : y ∈ A := by
      rw [hAm]
      intro i
      show (if hi : i ∈ S then (x ⟨i, hi⟩ : G i) else 1) ∈ A' i
      split_ifs with hi
      · exact (x ⟨i, hi⟩).2
      · exact (A' i).one_mem
    refine ⟨⟨y, hy⟩, funext fun i => Subtype.ext ?_⟩
    show (if hi : (i : ι) ∈ S then (x ⟨i, hi⟩ : G i) else 1) = (x i : G i)
    simp only [i.2, ↓reduceDIte]
  have hcomap : B.subgroupOf A = (Subgroup.pi Set.univ fun i : S => (B' i).subgroupOf (A' i)).comap f := by
    ext a
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, hBm]
    constructor
    · intro h i _
      rw [Subgroup.mem_subgroupOf]; exact h i
    · intro h i
      by_cases hi : i ∈ S
      · have := h ⟨i, hi⟩ (Set.mem_univ _)
        rwa [Subgroup.mem_subgroupOf] at this
      · exact hAB i hi ((hAm a).mp a.2 i)
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hf, Tamagawa.index_pi_dep]
  rw [← Finset.prod_coe_sort S]
  rfl

end RestrictedIndex

/-! ### Index ratios of the subgroups of determinant one -/

section Abstract

variable {G : Type*} [Group G]

/-- **$r(N\cap A, N\cap B) = r(A, B)$ when $N$ has index $2$ in both $A$ and $B$** (and $A$, $B$ are commensurable). -/
theorem relRatio_inf_eq_of_relIndex_two (N A B : Subgroup G) (hA : (N ⊓ A).relIndex A = 2)
    (hB : (N ⊓ B).relIndex B = 2) (hAB : B.relIndex A ≠ 0) (hBA : A.relIndex B ≠ 0) :
    relRatio (N ⊓ A) (N ⊓ B) = relRatio A B := by
  set D := N ⊓ A ⊓ B with hD
  have hD' : D = N ⊓ B ⊓ A := by rw [hD, inf_right_comm]
  have hDA : D.relIndex A ≠ 0 := Subgroup.relIndex_inf_ne_zero (by rw [hA]; norm_num) hAB
  have hDB : D.relIndex B ≠ 0 := by
    rw [hD']; exact Subgroup.relIndex_inf_ne_zero (by rw [hB]; norm_num) hBA
  have e1 := Subgroup.relIndex_mul_relIndex D (N ⊓ A) A inf_le_left inf_le_right
  have e2 := Subgroup.relIndex_mul_relIndex D (N ⊓ B) B (by rw [hD']; exact inf_le_left) inf_le_right
  rw [hA] at e1
  rw [hB] at e2
  have hDNA : D.relIndex (N ⊓ A) ≠ 0 := fun h => hDA (by rw [← e1, h, zero_mul])
  have hle1 : D ≤ A ⊓ B := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hle2 : D ≤ (N ⊓ A) ⊓ (N ⊓ B) := by
    rw [hD]
    exact le_inf inf_le_left (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  rw [relRatio_eq_of_le hle1 hDA, relRatio_eq_of_le hle2 hDNA, ← e1, ← e2]
  push_cast
  rw [mul_div_mul_right _ _ two_ne_zero]

end Abstract

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### An improper isometry of $L_{\mathfrak p}$ -/

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **$O(L_{\mathfrak p})$ contains an improper isometry** at every finite $\mathfrak p$ (dyadic included), for an
$\mathcal O_F$-valued lattice $L$ on a nondegenerate $(F^n, Q)$, $n\ge1$: with $L_{\mathfrak p} = \gamma\,\mathfrak o_{\mathfrak p}^n$ the
local form $T = Q\circ\gamma$ is integral, it has a reflection $\tau\in\mathrm{GL}_n(\mathfrak o_{\mathfrak p})$
(`QuadForm.exists_refl_data_dvr`), and $\gamma\tau\gamma^{-1}$ is an improper isometry of $Q$ fixing $L_{\mathfrak p}$. -/
@[kb "omeara1963" "§91B, 91:4, p. 241 (O(L) contains a symmetry)"]
theorem exists_stabLat_det_neg_one (Q : QuadForm F n) (hQ : Q.hessian.det ≠ 0) (hn : 0 < n) (L : Lat F n)
    (hL : IsIntegral Q L.1) :
    ∃ g : orthGroup Q Fv, g ∈ stabLat v (orthGroup Q Fv).subtype (loc v L.1) ∧
      (g : GL (Fin n) Fv).val.det = -1 := by
  obtain ⟨γ, hγ⟩ := exists_locAct_std_model v L
  set T : QuadForm 𝔬 n := QuadForm.toO v (localForm Q v γ) (localForm_coeff_integral v Q L hL hγ) with hTdef
  have hTm : T.map (algebraMap 𝔬 Fv) = localForm Q v γ := QuadForm.map_toO v _ _
  have hγd : γ.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero
  have hTnd : T.Nondegenerate := by
    intro h0
    have h1 := congrArg (fun S : QuadForm Fv n => S.hessian.det) hTm
    simp only [localForm, QuadForm.hessian_compMat, det_mul, det_transpose] at h1
    rw [QuadForm.hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero,
      QuadForm.hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
    have hQv : algebraMap F Fv Q.hessian.det ≠ 0 := (map_ne_zero _).mpr hQ
    exact (mul_ne_zero (mul_ne_zero hγd hQv) hγd) h1.symm
  obtain ⟨x, w, hx, hw⟩ := QuadForm.exists_refl_data_dvr T hTnd hn
  have hdet := QuadForm.det_reflMat T hw hx
  let R₀ : GL (Fin n) 𝔬 := Matrix.nonsingInvUnit (QuadForm.reflMat x w) (by rw [hdet]; exact isUnit_one.neg)
  let R : GL (Fin n) Fv := Matrix.GeneralLinearGroup.map (algebraMap 𝔬 Fv) R₀
  have hRval : R.val = (QuadForm.reflMat x w).map (algebraMap 𝔬 Fv) := rfl
  set ρ : GL (Fin n) Fv := γ * R * γ⁻¹ with hρ
  have hTR : (localForm Q v γ).compMat R.val = localForm Q v γ := by
    rw [← hTm, hRval, QuadForm.map_compMat, QuadForm.compMat_reflMat T hw]
  have hval : ∀ y, Q.evalIn Fv (γ.val *ᵥ y) = (localForm Q v γ).eval y := by
    intro y
    rw [localForm, QuadForm.eval_compMat]
    unfold QuadForm.eval QuadForm.evalIn QuadForm.map
    simp
  have hmem : ρ ∈ orthGroup Q Fv := by
    refine mem_orthGroup_of_evalIn Q fun z => ?_
    have e1 : ρ.val *ᵥ z = γ.val *ᵥ (R.val *ᵥ (γ⁻¹.val *ᵥ z)) := by
      simp only [hρ, Units.val_mul, mulVec_mulVec, Matrix.mul_assoc]
    have e2 : z = γ.val *ᵥ (γ⁻¹.val *ᵥ z) := by
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    rw [e1, hval, ← QuadForm.eval_compMat, hTR]
    conv_rhs => rw [e2]
    rw [hval]
  refine ⟨⟨ρ, hmem⟩, ?_, ?_⟩
  · show locAct v ρ (loc v L.1) = loc v L.1
    rw [hγ, hρ, locAct_mul, locAct_mul, locAct_inv_locAct,
      show locAct v R (std v) = std v from locAct_map_std v R₀]
  · show ρ.val.det = -1
    have hRd : R.val.det = -1 := by
      rw [hRval, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet]
      simp
    have hinv : γ.val.det * (γ⁻¹).val.det = 1 := by
      rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
    rw [hρ, Units.val_mul, Units.val_mul, det_mul, det_mul, hRd]
    linear_combination (-1 : Fv) * hinv

end Local

/-! ### $r(SO(\hat L), SO(\hat{\mathcal O}_F^n))$ and $\mu_f(SO(\hat L))$ -/

section Global

variable (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **The index ratio of the $SO$-stabilizers is that of the $O$-stabilizers** (every $O(L_{\mathfrak p})$ and every
$O(\mathfrak o_{\mathfrak p}^n)$ has an improper element, so $SO$ has index $2$ in each):
$r(SO(\hat L), SO(\hat{\mathcal O}_F^n)) = r(O(\hat L), O(\hat{\mathcal O}_F^n))$, for an $\mathcal O_F$-valued lattice $L$. -/
theorem relRatio_KSOLat (hQ : Q₀.Nondegenerate) (hn : 0 < n) (L : Lat F n) (hL : IsIntegral QF L.1) :
    relRatio (KSOLat Q₀ L) (KSO Q₀) = relRatio (locStab QF L) (locStab QF (Tamagawa.stdLat F n)) := by
  classical
  have hQF : (QF).hessian.det ≠ 0 := nondegenerate_map Q₀ hQ
  rw [← relRatio_map (Subgroup.subtype_injective (soAf QF)) (KSOLat Q₀ L) (KSO Q₀),
    Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
  have hSfin : {v : HeightOneSpectrum (𝓞 F) | ¬ loc v L.1 = std v}.Finite :=
    Filter.eventually_cofinite.mp (loc_eventually_std L.2)
  set S := hSfin.toFinset
  have hS : ∀ v ∉ S, loc v L.1 = std v := fun v hv => by
    by_contra h; exact hv (hSfin.mem_toFinset.mpr h)
  set A' : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (orthGroup QF (v.adicCompletion F)) := fun v =>
    soSub QF (v.adicCompletion F) ⊓ stabLat v (orthGroup QF (v.adicCompletion F)).subtype (loc v L.1) with hA'
  set B' : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (orthGroup QF (v.adicCompletion F)) := fun v =>
    soSub QF (v.adicCompletion F) ⊓ stdStab QF v with hB'
  have hAB : ∀ v ∉ S, A' v = B' v := by
    intro v hv
    simp only [hA', hB']
    rw [hS v hv, ← stdStab_eq_stabLat]
  have hAm : ∀ h : OAf QF, h ∈ locStab QF L ⊓ soAf QF ↔ ∀ v, h v ∈ A' v :=
    fun h => ⟨fun ⟨h1, h2⟩ v => ⟨h2 v, h1 v⟩, fun h' => ⟨fun v => (h' v).2, fun v => (h' v).1⟩⟩
  have hBm : ∀ h : OAf QF, h ∈ locStab QF (Tamagawa.stdLat F n) ⊓ soAf QF ↔ ∀ v, h v ∈ B' v := by
    intro h
    rw [Subgroup.mem_inf, mem_locStab_intVec]
    exact ⟨fun ⟨h1, h2⟩ v => ⟨h2 v, h1 v⟩, fun h' => ⟨fun v => (h' v).2, fun v => (h' v).1⟩⟩
  have e1 := relIndex_restrictedPi_of_le S A' B' (fun v hv => (hAB v hv).le) _ _ hAm hBm
  have e2 := relIndex_restrictedPi_of_le S B' A' (fun v hv => (hAB v hv).ge) _ _ hBm hAm
  -- the local ratios
  have hloc : ∀ v, relRatio (A' v) (B' v) =
      relRatio (stabLat v (orthGroup QF (v.adicCompletion F)).subtype (loc v L.1)) (stdStab QF v) := by
    intro v
    obtain ⟨ρ, hρK, hρ⟩ := exists_stabLat_det_neg_one v QF hQF hn L hL
    have h2L := relIndex_soSub_eq_two QF hQF _ ρ hρK hρ
    have h2s := relIndex_soStab v Q₀ hQ hn
    have hlatL : (loc v L.1).IsLattice (v.adicCompletion F) := loc_isLattice v L.2
    have hlatS : (std v : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F)).IsLattice
        (v.adicCompletion F) := by
      rw [← loc_intVec]; exact loc_isLattice v intVec_isLattice
    refine relRatio_inf_eq_of_relIndex_two _ _ _ h2L h2s ?_ ?_
    · rw [stdStab_eq_stabLat]; exact relIndex_stabLat_ne_zero v _ hlatL hlatS
    · rw [stdStab_eq_stabLat]; exact relIndex_stabLat_ne_zero v _ hlatS hlatL
  -- the global ratio of the `O`-stabilizers
  have hO : relRatio (locStab QF L) (locStab QF (Tamagawa.stdLat F n)) =
      ∏ v ∈ S, relRatio (stabLat v (orthGroup QF (v.adicCompletion F)).subtype (loc v L.1)) (stdStab QF v) := by
    rw [LatChange.relRatio_symm', LatChange.relRatio_locStab_eq_prod QF L S hS, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun v _ => (LatChange.relRatio_symm' _ _).symm
  rw [hO, ← Finset.prod_congr rfl fun v _ => hloc v]
  unfold relRatio
  rw [e1, e2, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]

/-- **$\mu_f(SO(\hat L)) = r(O(\hat L), O(\hat{\mathcal O}_F^n))\cdot\mu_f(SO(\hat{\mathcal O}_F^n))$** for an $\mathcal O_F$-valued
lattice $L$ ($\mu_f(SO(\hat{\mathcal O}_F^n)) = \prod_{\mathfrak p}\alpha_{\mathfrak p}(Q_0,Q_0)$ = `finFactor Q₀ 1`). -/
theorem muFin_KSOLat (hQ : Q₀.Nondegenerate) (hn : 0 < n) (L : Lat F n) (hL : IsIntegral QF L.1) :
    muFin Q₀ (fun _ => 1) (KSOLat Q₀ L) =
      ENNReal.ofReal (relRatio (locStab QF L) (locStab QF (Tamagawa.stdLat F n)) * finFactor Q₀ fun _ => 1) := by
  have h12 : (KSO Q₀).relIndex (KSOLat Q₀ L) ≠ 0 :=
    relIndex_ne_zero_of_isOpen (isCompact_KSOLat Q₀ L) (isOpen_KSO Q₀)
  have h21 : (KSOLat Q₀ L).relIndex (KSO Q₀) ≠ 0 :=
    relIndex_ne_zero_of_isOpen (isCompact_KSO Q₀) (isOpen_KSOLat Q₀ L)
  have e := measure_toReal_eq_relRatio_mul (muFin Q₀ fun _ => 1) (isOpen_KSOLat Q₀ L) (isOpen_KSO Q₀) h12 h21
  rw [muFin_KSO, ENNReal.toReal_ofReal (finFactor_nonneg _ _), relRatio_KSOLat Q₀ hQ hn L hL] at e
  have hfin : muFin Q₀ (fun _ => 1) (KSOLat Q₀ L) ≠ ⊤ := by
    unfold Tamagawa.Measure.muFin
    exact (isCompact_KSOLat Q₀ L).measure_lt_top.ne
  rw [← e, ENNReal.ofReal_toReal hfin]

end Global

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.exists_stabLat_det_neg_one
#print axioms QuadFormsKB.Hanke2011Structure.relRatio_KSOLat
#print axioms QuadFormsKB.Hanke2011Structure.muFin_KSOLat
