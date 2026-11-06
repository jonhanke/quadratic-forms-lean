/-
# Hanke 2005, (3.3) at odd places: the anisotropic kernel of $\langle u\rangle\perp\pi W$

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

Work in progress towards `OddWittType`: for $\mathfrak p\nmid2$ and the shape $\langle u_0,\dots,u_{a-1}\rangle\perp\pi W$ with $\overline W$ an anisotropic plane,
the unit part splits as $\mathbb H^k\perp\langle r\rangle$ (`peel_units`, $\le2$ leftover units $r$) and the remaining form
$\langle r\rangle\perp\pi W$ is anisotropic when $\bar r$ and $\overline W$ are (`aniso_unit_pi`), so the anisotropic dimension is $\rho+2$.
-/
import QuadFormsKB.Literature.Hanke2005.DensityOddJordan
import QuadFormsKB.Literature.Hanke2005.SelfDualNondyadic

open NumberField IsDedekindDomain Matrix QuadraticMap QuadraticForm

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Tamagawa QuadFormsKB.Lattices QuadForm

section Reindex

variable {K : Type*} [Field K]

/-- Reindexing the variables of a weighted sum of squares. -/
def wssReindex {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] (e : ι ≃ ι') (c : ι' → K) :
    (weightedSumSquares K (c ∘ e)).IsometryEquiv (weightedSumSquares K c) where
  toLinearEquiv := LinearEquiv.funCongrLeft K K e.symm
  map_app' x := by
    simp only [weightedSumSquares_apply, LinearEquiv.funCongrLeft_apply, Function.comp, LinearMap.funLeft,
      smul_eq_mul]
    exact (Equiv.sum_comp e (fun j => c j * (x (e.symm j) * x (e.symm j)))).symm.trans
      (Finset.sum_congr rfl fun i _ => by simp)

end Reindex

section Peel

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

open SelfDualN in
/-- **Peeling hyperbolic planes off a unit diagonal form** ($\mathfrak p\nmid2$): $\langle a_0,\dots,a_{m-1}\rangle\cong\mathbb H^k\perp\langle r_0,\dots,r_{\rho-1}\rangle$ over
$F_\mathfrak p$ with $m=2k+\rho$, $\rho\le2$ ($\rho\ge1$ if $m\ge1$), units $r_i$, and the same signed discriminant
$(-1)^{\lfloor m/2\rfloor}\prod a_i=(-1)^{\lfloor\rho/2\rfloor}\prod r_i$. -/
theorem peel_units (h2 : IsUnit (2 : 𝔬)) : ∀ (m : ℕ) (a : Fin m → 𝔬), (∀ i, IsUnit (a i)) →
    ∃ (k ρ : ℕ) (r : Fin ρ → 𝔬), m = 2 * k + ρ ∧ ρ ≤ 2 ∧ (0 < m → 0 < ρ) ∧ (∀ i, IsUnit (r i)) ∧
      (weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (a i))).Equivalent
        ((hyperbolicSpace Fv k).prod (weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (r i)))) ∧
      (-1 : 𝔬) ^ (m / 2) * ∏ i, a i = (-1 : 𝔬) ^ (ρ / 2) * ∏ i, r i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a ha
  by_cases hm : m < 3
  · refine ⟨0, m, a, by omega, by omega, fun h => h, ha, ?_, by simp⟩
    exact ⟨(Witt.hyperbolicSpaceZeroProd _).symm⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 3 ≤ m)
    have h2' := two_ne_zero_Fv v
    let a3 : Fin 3 → 𝔬 := fun i => a (Fin.castAdd k i)
    let r : Fin k → 𝔬 := fun j => a (Fin.natAdd 3 j)
    have ha3 : ∀ i, IsUnit (a3 i) := fun i => ha _
    have hr : ∀ j, IsUnit (r j) := fun j => ha _
    have hT := ternary h2' (fun i => algebraMap 𝔬 Fv (a3 i)) (fun i => ne_zero_Fv v (ha3 i))
      (isotropic_three v a3 ha3 h2)
    let u : 𝔬 := -(a3 0 * a3 1 * a3 2)
    have hu : IsUnit u := (((ha3 0).mul (ha3 1)).mul (ha3 2)).neg
    have hιu : algebraMap 𝔬 Fv u =
        -(algebraMap 𝔬 Fv (a3 0) * algebraMap 𝔬 Fv (a3 1) * algebraMap 𝔬 Fv (a3 2)) := by
      simp [u]
    let a' : Fin (1 + k) → 𝔬 := Fin.append (fun _ : Fin 1 => u) r
    have ha' : ∀ i, IsUnit (a' i) := by
      intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simpa [a'] using hu
      · simpa [a'] using hr j
    have e1 := splitIso (K := Fv) 3 k (fun i => algebraMap 𝔬 Fv (a i))
    have e4 : (weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (a' i))).Equivalent
        ((weightedSumSquares Fv (fun _ : Fin 1 => algebraMap 𝔬 Fv u)).prod
          (weightedSumSquares Fv (fun j => algebraMap 𝔬 Fv (r j)))) := by
      have h : (weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (a' i))).Equivalent
          ((weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (a' (Fin.castAdd k i)))).prod
            (weightedSumSquares Fv (fun j => algebraMap 𝔬 Fv (a' (Fin.natAdd 1 j))))) :=
        ⟨splitIso (K := Fv) 1 k (fun i => algebraMap 𝔬 Fv (a' i))⟩
      simp only [a', Fin.append_left, Fin.append_right] at h
      exact h
    rw [← hιu] at hT
    have hE : (weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (a i))).Equivalent
        ((hyperbolicSpace Fv 1).prod (weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (a' i)))) := by
      exact ⟨e1.trans ((hT.some.prod (QuadraticMap.IsometryEquiv.refl _)).trans
        ((Witt.prodAssoc _ _ _).trans ((QuadraticMap.IsometryEquiv.refl _).prod e4.some.symm)))⟩
    obtain ⟨k', ρ, r', hlen, hρ, hpos, hr', hE', hinv'⟩ := ih (1 + k) (by omega) a' ha'
    refine ⟨1 + k', ρ, r', by omega, hρ, fun _ => hpos (by omega), hr', ?_, ?_⟩
    · refine hE.trans ?_
      have e : ((hyperbolicSpace Fv 1).prod (weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (a' i)))).IsometryEquiv
          ((hyperbolicSpace Fv (1 + k')).prod (weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (r' i)))) :=
        ((QuadraticMap.IsometryEquiv.refl _).prod hE'.some).trans ((Witt.prodAssoc _ _ _).symm.trans
          ((hyperbolicSpace_prod_equiv 1 k').some.prod (QuadraticMap.IsometryEquiv.refl _)))
      exact ⟨e⟩
    · -- the discriminant
      have hprod : ∏ i, a i = (a3 0 * a3 1 * a3 2) * ∏ j, r j := by
        rw [Fin.prod_univ_add, Fin.prod_univ_three]
      have hprod' : ∏ i, a' i = u * ∏ j, r j := by
        rw [Fin.prod_univ_add]
        simp [a', Fin.append_left, Fin.append_right]
      have hpar : (3 + k) / 2 = (1 + k) / 2 + 1 := by omega
      rw [hpar, pow_succ, hprod]
      have := hinv'
      rw [hprod'] at this
      simp only [u] at this
      linear_combination this

end Peel

section Aniso

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **A unit form plus $\pi$ times a unit form is anisotropic when both residue forms are** (the valuation argument of Springer's
theorem): if $\sum r_iz_i^2\equiv0\bmod\pi$ forces $\pi\mid z_i$ and the same for $w$, then $\langle r\rangle\perp\langle\pi w\rangle$ has no
nonzero zero over $F_\mathfrak p$. -/
theorem aniso_unit_pi {ρ b : ℕ} (r : Fin ρ → 𝔬) (w : Fin b → 𝔬)
    (R1 : ∀ z : Fin ρ → 𝔬, NF.π v ∣ ∑ i, r i * z i ^ 2 → ∀ i, NF.π v ∣ z i)
    (R2 : ∀ z : Fin b → 𝔬, NF.π v ∣ ∑ j, w j * z j ^ 2 → ∀ j, NF.π v ∣ z j) :
    ((weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (r i))).prod
      (weightedSumSquares Fv (fun j => algebraMap 𝔬 Fv (NF.π v * w j)))).Anisotropic := by
  have hπ := NF.irreducible_π v
  intro ⟨x, y⟩ h
  by_contra hne
  rw [QuadraticMap.prod_apply] at h
  simp only [weightedSumSquares_apply, smul_eq_mul] at h
  set Z : Fin ρ ⊕ Fin b → Fv := Sum.elim x y with hZ
  have hZne : ∃ i, Z i ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hne
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · simpa [hZ] using hall (Sum.inl i)
    · simpa [hZ] using hall (Sum.inr j)
  obtain ⟨i1, hi1⟩ := hZne
  obtain ⟨i0, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin ρ ⊕ Fin b)) (fun i => Valued.v (Z i))
    ⟨i1, Finset.mem_univ _⟩
  have hv1 : 0 < Valued.v (Z i1) := (Valued.v).pos_iff.mpr hi1
  have hZ0 : Z i0 ≠ 0 := by
    intro h0
    have := hmax i1 (Finset.mem_univ _)
    rw [h0, map_zero] at this
    exact absurd hv1 (not_lt.mpr this)
  set c : Fv := (Z i0)⁻¹ with hc
  have hcle : ∀ i, Valued.v (c * Z i) ≤ 1 := by
    intro i
    have hv0 : 0 < Valued.v (Z i0) := (Valued.v).pos_iff.mpr hZ0
    rw [map_mul, hc, map_inv₀]
    rw [inv_mul_le_iff₀ hv0, mul_one]
    exact hmax i (Finset.mem_univ _)
  set Λ : Fin ρ ⊕ Fin b → 𝔬 := fun i => toO v (c * Z i) (hcle i) with hΛ
  have hΛι : ∀ i, algebraMap 𝔬 Fv (Λ i) = c * Z i := fun i => rfl
  have heq : ∑ i, r i * Λ (Sum.inl i) ^ 2 + NF.π v * ∑ j, w j * Λ (Sum.inr j) ^ 2 = 0 := by
    apply (IsFractionRing.injective 𝔬 Fv)
    simp only [map_add, map_sum, map_mul, map_pow, hΛι, map_zero, Finset.mul_sum]
    have h' := congrArg (fun t => c ^ 2 * t) h
    simp only [mul_zero, mul_add, Finset.mul_sum, map_mul] at h'
    simp only [hZ, Sum.elim_inl, Sum.elim_inr]
    rw [← h']
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => by ring
  have hS1 : NF.π v ∣ ∑ i, r i * Λ (Sum.inl i) ^ 2 :=
    ⟨-(∑ j, w j * Λ (Sum.inr j) ^ 2), by linear_combination heq⟩
  have hX := R1 (fun i => Λ (Sum.inl i)) hS1
  choose X' hX' using hX
  have heq2 : NF.π v * ∑ i, r i * X' i ^ 2 + ∑ j, w j * Λ (Sum.inr j) ^ 2 = 0 := by
    have h3 : NF.π v * (NF.π v * ∑ i, r i * X' i ^ 2 + ∑ j, w j * Λ (Sum.inr j) ^ 2) = 0 := by
      have : ∑ i, r i * Λ (Sum.inl i) ^ 2 = NF.π v ^ 2 * ∑ i, r i * X' i ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hX' i]; ring
      linear_combination heq - this
    exact (mul_eq_zero.1 h3).resolve_left hπ.ne_zero
  have hS2 : NF.π v ∣ ∑ j, w j * Λ (Sum.inr j) ^ 2 :=
    ⟨-(∑ i, r i * X' i ^ 2), by linear_combination heq2⟩
  have hY := R2 (fun j => Λ (Sum.inr j)) hS2
  have hΛ0 : Λ i0 = 1 := by
    apply (IsFractionRing.injective 𝔬 Fv)
    rw [hΛι, map_one, hc]
    exact inv_mul_cancel₀ hZ0
  have hdiv : NF.π v ∣ Λ i0 := by
    rcases i0 with i | j
    · exact ⟨X' i, hX' i⟩
    · exact hY j
  rw [hΛ0] at hdiv
  exact hπ.not_isUnit (isUnit_of_dvd_one hdiv)

end Aniso

section Binary

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $\chi_D\langle w_0,w_1\rangle=\chi(-\bar w_0\bar w_1)$. -/
theorem chiDisc_diag_two_eq (h2 : IsUnit (2 : 𝔬)) (w : Fin 2 → 𝔬) :
    chiDisc (QuadForm.diag w) =
      quadraticChar (IsLocalRing.ResidueField 𝔬) (-(IsLocalRing.residue 𝔬 (w 0) * IsLocalRing.residue 𝔬 (w 1))) := by
  have hπ2 : ¬ NF.π v ∣ 2 := DensitySD.not_dvd_two v h2
  have h2F : (2 : IsLocalRing.ResidueField 𝔬) ≠ 0 := by
    have := DVR.res_ne_zero (NF.irreducible_π v) hπ2
    rwa [map_ofNat] at this
  have hc : (-1 : IsLocalRing.ResidueField 𝔬) ^ (2 / 2) * resGramDet (QuadForm.diag w) =
      -(IsLocalRing.residue 𝔬 (w 0) * IsLocalRing.residue 𝔬 (w 1)) := by
    unfold resGramDet
    rw [det_hessian_diag, map_mul, map_pow, map_ofNat, Fin.prod_univ_two, map_mul]
    field_simp
    norm_num
  unfold chiDisc
  rw [hc]

/-- **A binary unit form with $\chi(-\bar r_0\bar r_1)=-1$ is anisotropic mod $\pi$.** -/
theorem aniso_two_of_chi (h2 : IsUnit (2 : 𝔬)) (r : Fin 2 → 𝔬) (hr : ∀ j, IsUnit (r j))
    (hχ : quadraticChar (IsLocalRing.ResidueField 𝔬)
      (-(IsLocalRing.residue 𝔬 (r 0) * IsLocalRing.residue 𝔬 (r 1))) = -1) :
    ∀ z : Fin 2 → 𝔬, NF.π v ∣ ∑ j, r j * z j ^ 2 → ∀ j, NF.π v ∣ z j := by
  have hπ := NF.irreducible_π v
  intro z hz
  have hr0 : IsLocalRing.residue 𝔬 (r 0) ≠ 0 := DVR.res_ne_zero hπ (DVR.dvr_not_dvd_of_isUnit hπ (hr 0))
  have hr1 : IsLocalRing.residue 𝔬 (r 1) ≠ 0 := DVR.res_ne_zero hπ (DVR.dvr_not_dvd_of_isUnit hπ (hr 1))
  have hres : IsLocalRing.residue 𝔬 (r 0) * IsLocalRing.residue 𝔬 (z 0) ^ 2 +
      IsLocalRing.residue 𝔬 (r 1) * IsLocalRing.residue 𝔬 (z 1) ^ 2 = 0 := by
    have := (DVR.residue_eq_zero_iff_dvd hπ _).2 hz
    simpa [Fin.sum_univ_two] using this
  have hz1 : NF.π v ∣ z 1 := by
    by_contra hnd
    have hz1 : IsLocalRing.residue 𝔬 (z 1) ≠ 0 := DVR.res_ne_zero hπ hnd
    have hsq : IsSquare (-(IsLocalRing.residue 𝔬 (r 0) * IsLocalRing.residue 𝔬 (r 1))) := by
      refine ⟨IsLocalRing.residue 𝔬 (r 0) * IsLocalRing.residue 𝔬 (z 0) / IsLocalRing.residue 𝔬 (z 1), ?_⟩
      field_simp
      first
        | linear_combination (-1 : IsLocalRing.ResidueField 𝔬) * hres
        | linear_combination (-(IsLocalRing.residue 𝔬 (r 0))) * hres
    have := (quadraticChar_one_iff_isSquare (neg_ne_zero.2 (mul_ne_zero hr0 hr1))).2 hsq
    rw [this] at hχ
    exact absurd hχ (by norm_num)
  have hz0 : NF.π v ∣ z 0 := by
    have hr1' : IsLocalRing.residue 𝔬 (z 1) = 0 := (DVR.residue_eq_zero_iff_dvd hπ _).2 hz1
    rw [hr1'] at hres
    have h0 : IsLocalRing.residue 𝔬 (z 0) = 0 := by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at hres
      rcases mul_eq_zero.1 hres with h | h
      · exact absurd h hr0
      · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
    exact (DVR.residue_eq_zero_iff_dvd hπ _).1 h0
  intro j
  fin_cases j
  · exact hz0
  · exact hz1

end Binary

section Decomp

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The anisotropic dimension from a peeled decomposition:** if $Q_\mathfrak p\simeq\langle u\rangle\perp\pi\langle w\rangle$ (two variables $w$), the unit part is
$\langle u\rangle\cong\mathbb H^k\perp\langle r\rangle$ over $F_\mathfrak p$ and both residue forms of $r$ and $w$ are anisotropic, then
$t_\mathfrak p=\rho+2$ (the Witt index is $k$ by Witt's uniqueness `eq_wittIndex`). -/
theorem anisoDim_of_decomp {a : ℕ} (Q₀ : QuadForm (𝓞 F) (2 + a)) (hQ : Q₀.Nondegenerate)
    (u : Fin a → 𝔬) (w : Fin 2 → 𝔬)
    (he : DVR.IsGLEquiv (NF.Qp v Q₀) (unitSum (QuadForm.diag fun j => NF.π v * w j) a u))
    {k ρ : ℕ} (r : Fin ρ → 𝔬) (hlen : a = 2 * k + ρ)
    (hE : (weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (u i))).Equivalent
      ((hyperbolicSpace Fv k).prod (weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (r i)))))
    (R1 : ∀ z : Fin ρ → 𝔬, NF.π v ∣ ∑ i, r i * z i ^ 2 → ∀ i, NF.π v ∣ z i)
    (R2 : ∀ z : Fin 2 → 𝔬, NF.π v ∣ ∑ j, w j * z j ^ 2 → ∀ j, NF.π v ∣ z j) :
    anisoDim v Q₀ = 2 + ρ := by
  classical
  set t : Fin 2 → 𝔬 := fun j => NF.π v * w j with ht
  have hnd : ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)).Nondegenerate := by
    rw [Tamagawa.map_Qp_eq]; exact nondegenerate_Qf v Q₀ hQ
  have hrad := radical_eq_bot_map v _ hnd
  have e1 := equivalent_map_of_isGLEquiv v he
  rw [unitSum_diag, SelfDualN.map_diag_toQF] at e1
  -- split the diagonal form
  set c' : Fin (2 + a) → Fv := fun i => algebraMap 𝔬 Fv (cseq t a u i) with hc'
  let e : Fin (a + 2) ≃ Fin (2 + a) := finCongr (Nat.add_comm a 2)
  have hl : ∀ i : Fin a, (c' ∘ e) (Fin.castAdd 2 i) = algebraMap 𝔬 Fv (u i) := by
    intro i
    simp only [Function.comp, hc', e, finCongr_apply]
    rw [cseq_lt t a u _ (by simpa using i.2)]
    rfl
  have hr : ∀ j : Fin 2, (c' ∘ e) (Fin.natAdd a j) = algebraMap 𝔬 Fv (t j) := by
    intro j
    simp only [Function.comp, hc', e, finCongr_apply]
    rw [cseq_ge t a u _ (by simp)]
    congr 2
    ext; simp
  have e2 : (weightedSumSquares Fv c').Equivalent
      ((weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (u i))).prod
        (weightedSumSquares Fv (fun j => algebraMap 𝔬 Fv (t j)))) := by
    have s1 := SelfDualN.splitIso (K := Fv) a 2 (c' ∘ e)
    have : (fun i : Fin a => (c' ∘ e) (Fin.castAdd 2 i)) = fun i => algebraMap 𝔬 Fv (u i) := funext hl
    have this2 : (fun j : Fin 2 => (c' ∘ e) (Fin.natAdd a j)) = fun j => algebraMap 𝔬 Fv (t j) := funext hr
    rw [this, this2] at s1
    exact ⟨(wssReindex e c').symm.trans s1⟩
  have e3 : (weightedSumSquares Fv c').Equivalent
      ((hyperbolicSpace Fv k).prod ((weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (r i))).prod
        (weightedSumSquares Fv (fun j => algebraMap 𝔬 Fv (t j))))) := by
    refine e2.trans ⟨?_⟩
    exact ((hE.some).prod (QuadraticMap.IsometryEquiv.refl _)).trans (Witt.prodAssoc _ _ _)
  have hA := aniso_unit_pi v r w R1 R2
  have hfin : QuadraticForm.wittIndex ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)).toQuadraticForm = k := by
    have e4 : ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)).toQuadraticForm.Equivalent
        ((hyperbolicSpace Fv k).prod ((weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (r i))).prod
          (weightedSumSquares Fv (fun j => algebraMap 𝔬 Fv (t j))))) := e1.trans e3
    exact (eq_wittIndex _ hrad hA e4).symm
  unfold anisoDim
  have hQV : Tamagawa.Measure.LerayPadic.QV v Q₀ = (NF.Qp v Q₀).map (algebraMap 𝔬 Fv) := rfl
  rw [hQV, hfin]
  omega

end Decomp

section Delta

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The determinant of the Jordan shape up to a square:** $\det H(Q)=\pi^b\cdot(2^a\prod u_i\det H(W))s^2$ with $s$ a unit. -/
theorem det_shape_sq {a b : ℕ} (h2 : IsUnit (2 : 𝔬)) (u : Fin a → 𝔬) (hu : ∀ i, IsUnit (u i))
    (W T : QuadForm 𝔬 b) (hW : IsUnit W.hessian.det) (hT : ∀ i j, T.coeff i j = NF.π v * W.coeff i j)
    (Q : QuadForm 𝔬 (b + a)) (hQ : DVR.IsGLEquiv Q (unitSum T a u)) :
    ∃ s : 𝔬, IsUnit s ∧ Q.hessian.det = NF.π v ^ b * ((2 ^ a * (∏ i, u i) * W.hessian.det) * s ^ 2) := by
  obtain ⟨U, hU, hUe⟩ := hQ
  have hH := DVR.hessian_eq_of_eval hUe
  have hD : (unitSum T a u).hessian.det = U.det * Q.hessian.det * U.det := by
    rw [hH, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hTH : T.hessian = NF.π v • W.hessian := by ext i j; simp [hessian, hT]; ring
  obtain ⟨s, hs⟩ := hU.exists_left_inv
  have hsu : IsUnit s := ⟨⟨s, U.det, hs, by rw [mul_comm]; exact hs⟩, rfl⟩
  refine ⟨s, hsu, ?_⟩
  have e : (unitSum T a u).hessian.det = NF.π v ^ b * (2 ^ a * (∏ i, u i) * W.hessian.det) := by
    rw [det_hessian_unitSum, hTH, Matrix.det_smul, Fintype.card_fin]; ring
  calc Q.hessian.det = Q.hessian.det * (U.det * s) * (U.det * s) := by rw [mul_comm U.det s, hs]; ring
    _ = (U.det * Q.hessian.det * U.det) * s ^ 2 := by ring
    _ = _ := by rw [← hD, e]; ring

/-- $\chi_D\langle u\rangle=\chi\big((-1)^{\lfloor a/2\rfloor}\prod\bar u_i\big)$. -/
theorem chiDisc_diag_eq (h2 : IsUnit (2 : 𝔬)) {a : ℕ} (u : Fin a → 𝔬) :
    chiDisc (QuadForm.diag u) =
      quadraticChar (IsLocalRing.ResidueField 𝔬) (IsLocalRing.residue 𝔬 ((-1 : 𝔬) ^ (a / 2) * ∏ i, u i)) := by
  have hπ2 : ¬ NF.π v ∣ 2 := DensitySD.not_dvd_two v h2
  have h2F : (2 : IsLocalRing.ResidueField 𝔬) ≠ 0 := by
    have := DVR.res_ne_zero (NF.irreducible_π v) hπ2
    rwa [map_ofNat] at this
  have hc : (-1 : IsLocalRing.ResidueField 𝔬) ^ (a / 2) * resGramDet (QuadForm.diag u) =
      IsLocalRing.residue 𝔬 ((-1 : 𝔬) ^ (a / 2) * ∏ i, u i) := by
    unfold resGramDet
    rw [det_hessian_diag]
    simp only [map_mul, map_pow, map_neg, map_one, map_ofNat]
    field_simp
  unfold chiDisc
  rw [hc]

end Delta

section TwoCase

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The case $a$ even, $\chi_U=+1$:** $t_\mathfrak p=2$ (the discriminant $\delta$ is a non-square, `anisoDim_eq_two_iff`). -/
theorem anisoDim_eq_two_of_chi {j : ℕ} (Q₀ : QuadForm (𝓞 F) (2 + (j + j))) (hQ : Q₀.Nondegenerate)
    (h2 : IsUnit (2 : 𝔬)) (u : Fin (j + j) → 𝔬) (hu : ∀ i, IsUnit (u i)) (w : Fin 2 → 𝔬) (hw : ∀ i, IsUnit (w i))
    (he : DVR.IsGLEquiv (NF.Qp v Q₀) (unitSum (QuadForm.diag fun j => NF.π v * w j) (j + j) u))
    (hU : chiDisc (QuadForm.diag u) = 1) (hW : chiDisc (QuadForm.diag w) = -1) : anisoDim v Q₀ = 2 := by
  have hπ := NF.irreducible_π v
  have hπ2 : ¬ NF.π v ∣ 2 := DensitySD.not_dvd_two v h2
  rw [anisoDim_eq_two_iff v Q₀ hQ ⟨1 + j, by omega⟩]
  rintro ⟨q, hq⟩
  have hWdet : IsUnit (QuadForm.diag w).hessian.det := by
    rw [det_hessian_diag]
    exact (h2.pow 2).mul (Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun i _ => hw i))
  have hT : ∀ i k, (QuadForm.diag fun j => NF.π v * w j).coeff i k = NF.π v * (QuadForm.diag w).coeff i k := by
    intro i k
    simp only [QuadForm.diag, Matrix.diagonal_apply]
    split_ifs <;> simp
  obtain ⟨s, hs, hD⟩ := det_shape_sq v h2 u hu (QuadForm.diag w) _ hWdet hT (NF.Qp v Q₀) he
  rw [det_hessian_diag, Fin.prod_univ_two] at hD
  rw [algebraMap_discK_eq, hD] at hq
  set E : 𝔬 := (2 ^ (j + j) * (∏ i, u i) * (2 ^ 2 * (w 0 * w 1))) * s ^ 2 with hE
  set ε : 𝔬 := (-1 : 𝔬) ^ (j + 1) * E with hε
  have hπ0 : ((NF.π v : 𝔬) : Fv) ≠ 0 := by
    intro h0; exact hπ.ne_zero (Subtype.ext h0)
  have h2F : (2 : Fv) ≠ 0 := two_ne_zero
  have hsq : IsSquare (algebraMap 𝔬 Fv ε) := by
    refine ⟨q * 2 ^ (j + 1) / ((NF.π v : 𝔬) : Fv), ?_⟩
    have hn2 : (2 + (j + j)) / 2 = j + 1 := by omega
    rw [hn2] at hq
    have hcoe : ((NF.π v ^ 2 * E : 𝔬) : Fv) = ((NF.π v : 𝔬) : Fv) ^ 2 * (E : Fv) := by push_cast; rfl
    have hε' : algebraMap 𝔬 Fv ε = (-1) ^ (j + 1) * (E : Fv) := by
      simp only [hε, map_mul, map_pow, map_neg, map_one]
      rfl
    rw [hcoe] at hq
    rw [hε']
    generalize (E : Fv) = Eι at hq ⊢
    generalize ((NF.π v : 𝔬) : Fv) = p at hq hπ0 ⊢
    field_simp at hq ⊢
    linear_combination hq
  have hεsq : IsSquare ε := (DVR.isSquare_algebraMap_iff Fv ε).1 hsq
  have hεu : IsUnit ε := by
    refine (isUnit_one.neg.pow _).mul ?_
    exact (((h2.pow _).mul (Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun i _ => hu i))).mul
      ((h2.pow 2).mul ((hw 0).mul (hw 1)))).mul (hs.pow 2)
  have hchi := (DVR.isSquare_iff_quadraticChar_residue hπ hπ2
    (DVR.dvr_not_dvd_of_isUnit hπ hεu)).1 hεsq
  have hid : ε = ((-1 : 𝔬) ^ j * ∏ i, u i) * (-(w 0 * w 1)) * (2 ^ (j + 1) * s) ^ 2 := by
    simp only [hε, hE]; ring
  have hz : IsLocalRing.residue 𝔬 (2 ^ (j + 1) * s) ≠ 0 :=
    DVR.res_ne_zero hπ (DVR.dvr_not_dvd_of_isUnit hπ ((h2.pow _).mul hs))
  have hres : IsLocalRing.residue 𝔬 ε =
      IsLocalRing.residue 𝔬 ((-1 : 𝔬) ^ j * ∏ i, u i) * IsLocalRing.residue 𝔬 (-(w 0 * w 1)) *
        (IsLocalRing.residue 𝔬 (2 ^ (j + 1) * s)) ^ 2 := by
    rw [hid]; simp only [map_mul, map_pow]
  rw [hres, map_mul, map_mul, quadraticChar_sq_one' hz] at hchi
  have hX : quadraticChar (IsLocalRing.ResidueField 𝔬)
      (IsLocalRing.residue 𝔬 ((-1 : 𝔬) ^ j * ∏ i, u i)) = 1 := by
    have := chiDisc_diag_eq v h2 u
    rw [show (j + j) / 2 = j by omega] at this
    rw [← this]; exact hU
  have hY : quadraticChar (IsLocalRing.ResidueField 𝔬) (IsLocalRing.residue 𝔬 (-(w 0 * w 1))) = -1 := by
    have := chiDisc_diag_two_eq v h2 w
    rw [hW] at this
    rw [map_neg, map_mul]
    exact this.symm
  rw [hX, hY] at hchi
  norm_num at hchi

end TwoCase

/-- **The Witt type of $\langle u\rangle\perp\pi W$ ($b=2$) at an odd place** (O'Meara 63, 92; Springer's theorem in the form needed here; proved):
`OddWittType F` holds. *Proof:* the unit part splits as $\mathbb H^k\perp\langle r\rangle$ (`peel_units`), the form $\langle r\rangle\perp\pi W$ is
anisotropic (`aniso_unit_pi`), so the Witt index is $k$ (`eq_wittIndex`) and $t_\mathfrak p=\rho+2$ (`anisoDim_of_decomp`); for $a$ even and
$\chi_U=+1$ the discriminant is a non-square (`anisoDim_eq_two_of_chi`). -/
@[kb "omeara1963" "§63, §92 (anisotropic kernel of an orthogonal sum of Jordan components; Springer); proved"]
theorem oddWittType (F : Type) [Field F] [NumberField F] : OddWittType F := by
  refine ⟨fun {n} Q₀ hQ v h2 a h u W T hu hW hT hχ hd he => ?_⟩
  subst h
  obtain ⟨w, rfl, rfl⟩ := hd
  have hπ := NF.irreducible_π v
  have hw : ∀ j, IsUnit (w j) := by
    rw [det_hessian_diag, Fin.prod_univ_two] at hW
    have h1 := (isUnit_of_mul_isUnit_right hW)
    intro j
    fin_cases j
    · exact isUnit_of_mul_isUnit_left h1
    · exact isUnit_of_mul_isUnit_right h1
  have hχW : quadraticChar (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) (-(IsLocalRing.residue (v.adicCompletionIntegers F) (w 0) * IsLocalRing.residue (v.adicCompletionIntegers F) (w 1))) = -1 := by
    rw [← chiDisc_diag_two_eq v h2 w]; exact hχ
  have R2 := aniso_two_of_chi v h2 w hw hχW
  obtain ⟨k, ρ, r, hlen, hρ, hpos, hr, hE, hinv⟩ := peel_units v h2 a u hu
  have he' : DVR.IsGLEquiv (NF.Qp v Q₀) (unitSum (QuadForm.diag fun j => NF.π v * w j) a u) := he
  refine ⟨fun hev => ⟨fun hU => ?_, fun hU => ?_⟩, fun hodd => ?_⟩
  · obtain ⟨j, hj⟩ := hev
    subst hj
    exact anisoDim_eq_two_of_chi v Q₀ hQ h2 u hu w hw he' hU hχ
  · obtain ⟨j, hj⟩ := hev
    have hχU := chiDisc_diag_eq v h2 u
    rw [hU, hinv] at hχU
    have hρ0 : ρ ≠ 0 := by
      rintro rfl
      simp at hχU
    obtain rfl : ρ = 2 := by omega
    have hχr : quadraticChar (IsLocalRing.ResidueField (v.adicCompletionIntegers F))
        (-(IsLocalRing.residue (v.adicCompletionIntegers F) (r 0) * IsLocalRing.residue (v.adicCompletionIntegers F) (r 1))) = -1 := by
      have e : IsLocalRing.residue (v.adicCompletionIntegers F) ((-1 : v.adicCompletionIntegers F) ^ (2 / 2) * ∏ i, r i) =
          -(IsLocalRing.residue (v.adicCompletionIntegers F) (r 0) *
            IsLocalRing.residue (v.adicCompletionIntegers F) (r 1)) := by
        simp [Fin.prod_univ_two]
      rw [e] at hχU
      exact hχU.symm
    have R1 := aniso_two_of_chi v h2 r hr hχr
    have := anisoDim_of_decomp v Q₀ hQ u w he' r hlen hE R1 R2
    omega
  · obtain ⟨j, hj⟩ := hodd
    obtain rfl : ρ = 1 := by omega
    have R1 : ∀ z : Fin 1 → v.adicCompletionIntegers F, NF.π v ∣ ∑ i, r i * z i ^ 2 → ∀ i, NF.π v ∣ z i := by
      intro z hz i
      rw [Fin.sum_univ_one] at hz
      rcases hπ.prime.dvd_or_dvd hz with h | h
      · exact absurd h (DVR.dvr_not_dvd_of_isUnit hπ (hr 0))
      · have := hπ.prime.dvd_of_dvd_pow h
        rwa [Fin.fin_one_eq_zero i]
    have := anisoDim_of_decomp v Q₀ hQ u w he' r hlen hE R1 R2
    omega

/-- **(3.3) at a non-dyadic place with $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$ (unconditional given the repository's proved results):**
`ShimuraDensityOddRamified F` holds. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (non-dyadic places with Λ̃_p ≠ Λ_p; proved)"]
theorem shimuraDensityOddRamified (F : Type) [Field F] [NumberField F] : ShimuraDensityOddRamified F :=
  shimuraDensityOddRamified_of_wittType (oddWittType F)

end QuadFormsKB.Hanke2005
