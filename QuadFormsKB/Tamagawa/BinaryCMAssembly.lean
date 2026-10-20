import QuadFormsKB.Tamagawa.BinaryCMLocalType

/-!
# The mass formula of $\langle1,D\rangle$: reduction to the maximal order

**Layer:** $F$ a number field, $E = F(\theta)$, $\theta^2 = -D$ (`SqrtData`), $Q = \langle1,D\rangle$ totally positive definite, $L_E$ the lattice of
$\mathcal O_E$ in the coordinates $x_0 + x_1\theta$ (`latE`), $c_\mathfrak p$ the exponent with $[L_{E,\mathfrak p} : \mathfrak o_\mathfrak p^2] = N\mathfrak p^{c_\mathfrak p}$ (`cv`),
$\chi = \chi_{E/F}$ (`relChar`), $T$ the set of ramified primes, $\rho_K$ the residue of $\zeta_K$ at $s = 1$.

**Proves**
* `localFactor_eq` (every prime, dyadic included): $r_\mathfrak p\,\beta_\mathfrak p(Q, 1) = N\mathfrak p^{c_\mathfrak p}\cdot(2$ if $\mathfrak p$ ramifies, else $1 - \chi(\mathfrak p)/N\mathfrak p)$;
* `cv_eq_zero`: $c_\mathfrak p = 0$ where $L_{E,\mathfrak p} = \mathfrak o_\mathfrak p^2$;
* **`mass_mul_siegelProduct2Reg_eq`** (the reduction):
  $$\mathrm{Mass}(\mathcal O_F^2)\,S^{\mathrm{reg}}_2(Q, 1) = \mathrm{Mass}(L_E)\cdot 2^{|T|}\prod_\mathfrak pN\mathfrak p^{c_\mathfrak p}\cdot|d_F|^{-1/2}\,\pi^n\,|N_{F/\mathbb Q}D|^{-1/2}\cdot
  \frac{\rho_F}{\rho_E}.$$

Source: Siegel 1935 (the local side) [unverified]; Shimura 2010, §4 (mass of a CM order) [unverified]; the comparison of two lattices in one genus
space is `mass_eq_mass_mul_relRatio`.

-/

open NumberField IsDedekindDomain Matrix WithZero Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.BinaryCM

open Lattices QuadForm QuadFormsKB.HilbertModular Binary.Rel BinaryNormOne Loc LocalDensity NFEuler RegProd LatChange

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

variable {D : 𝓞 F} (S : SqrtData D E)

local notation "QD" => formF (diagForm1 D)

/-! ### The local factor at every prime -/

/-- The chosen local data of $L_E$ at $\mathfrak p$ (`exists_struct_loc`). -/
def locD (v : HeightOneSpectrum (𝓞 F)) : LocData S v := Classical.choice (nonempty_locData S v)

/-- **The local index exponent** $c_\mathfrak p$: $L_{E,\mathfrak p} = \mathfrak o + \mathfrak o\,\omega$ with $\omega$ of second coordinate $\varpi^{-c_\mathfrak p}$,
so $[L_{E,\mathfrak p} : \mathfrak o_\mathfrak p^2] = N\mathfrak p^{c_\mathfrak p}$. -/
def cv (v : HeightOneSpectrum (𝓞 F)) : ℕ := (locD S v).c

/-- **The local factor of $\langle1,D\rangle$ at $\mathfrak p$ against the maximal order** (every prime, dyadic included):
$$r_\mathfrak p\,\beta_\mathfrak p(\langle1,D\rangle, 1) = N\mathfrak p^{c_\mathfrak p}\cdot\begin{cases}2 & \chi_{E/F}(\mathfrak p) = 0,\\ 1 - \chi_{E/F}(\mathfrak p)/N\mathfrak p & \text{else,}\end{cases}$$
$r_\mathfrak p = r(O(L_{E,\mathfrak p}), O(\mathfrak o_\mathfrak p^2))$ (`relRatio_mul_localDensity`, `localFactor_maximal`). -/
@[kb "siegel1935" "Hilfssatz (local densities of binary forms) [unverified]"]
theorem localFactor_eq (v : HeightOneSpectrum (𝓞 F)) :
    relRatio (stabLat v (orthGroup QD (v.adicCompletion F)).subtype (loc v (latE S))) (stdStab QD v) *
        NF.localDensity v (diagForm1 D) 1 =
      (qv v : ℝ) ^ cv S v * (if relChar E v = 0 then 2 else 1 - (relChar E v : ℝ) / qv v) := by
  rw [relRatio_mul_localDensity (locD S v), localFactor_maximal]; rfl

/-- $c_\mathfrak p = 0$ where $L_{E,\mathfrak p} = \mathfrak o_\mathfrak p^2$ ($\omega \in \mathfrak o_\mathfrak p^2$ forces $\varpi^{-c} \in \mathfrak o_\mathfrak p$). -/
theorem cv_eq_zero {v : HeightOneSpectrum (𝓞 F)} (h : loc v (latE S) = std v) : cv S v = 0 := by
  set L := locD S v
  have hmem := (L.mem_iff (omegaVec v L.c L.s 0 1)).mpr ⟨0, 1, rfl⟩
  rw [h] at hmem
  have h1 := hmem 1
  simp only [omegaVec, Matrix.cons_val_one, Matrix.cons_val_zero, OneMemClass.coe_one, one_mul] at h1
  rw [map_pow, map_inv₀, valued_πF, ← WithZero.exp_neg, ← WithZero.exp_nsmul, neg_zero,
    exp_le_exp] at h1
  show L.c = 0
  simp at h1
  omega

/-- $r_\mathfrak p = 1$ where $L_{E,\mathfrak p} = \mathfrak o_\mathfrak p^2$. -/
theorem relRatio_eq_one {v : HeightOneSpectrum (𝓞 F)} (h : loc v (latE S) = std v) :
    relRatio (stabLat v (orthGroup QD (v.adicCompletion F)).subtype (loc v (latE S))) (stdStab QD v) = 1 := by
  rw [h, ← stdStab_eq_stabLat]; simp [relRatio]

/-! ### The archimedean factor -/

/-- **$\prod_\sigma\beta_\sigma(1) = \pi^n\,|N_{F/\mathbb Q}D|^{-1/2}$** for $\langle1,D\rangle$ ($\beta_\sigma(1) = \pi\,|\sigma D|^{-1/2}$ in rank $2$). -/
theorem prod_archRepDensity_diagForm1 :
    ∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F 1)‖ (detGram (diagForm1 D) σ) =
      Real.pi ^ Module.finrank ℚ F * |(Algebra.norm ℚ (algebraMap (𝓞 F) F D) : ℝ)| ^ (-(1 / 2 : ℝ)) := by
  have hd : ∀ σ : F →ₐ[ℚ] ℂ, detGram (diagForm1 D) σ = ‖σ (algebraMap (𝓞 F) F D)‖ := fun σ => by
    unfold detGram
    rw [hessian_det_diagForm1, map_mul, map_ofNat]
    congr 2
    norm_num
  have ha : ∀ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F 1)‖ (detGram (diagForm1 D) σ) =
      Real.pi * ‖σ (algebraMap (𝓞 F) F D)‖ ^ (-(1 / 2 : ℝ)) := fun σ => by
    rw [hd, archRepDensity]
    simp only [map_one, norm_one, Nat.cast_ofNat, div_self (two_ne_zero' ℝ), Real.rpow_one, Real.Gamma_one,
      div_one, sub_self, zero_div, Real.rpow_zero, mul_one]
  rw [Finset.prod_congr rfl fun σ _ => ha σ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    AlgHom.card, Real.finsetProd_rpow _ _ (fun σ _ => norm_nonneg _)]
  congr 2
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ (algebraMap (𝓞 F) F D)
  rw [← norm_prod, ← h]
  simp

/-! ### The reduction to the maximal order -/

/-- $r(A,B) = r(B,A)^{-1}$. -/
theorem relRatio_symm {G : Type*} [Group G] (A B : Subgroup G) : relRatio A B = (relRatio B A)⁻¹ := by
  simp [relRatio]

/-- **The mass formula of $\langle1,D\rangle$, reduced to the maximal order** ($Q = \langle1,D\rangle$ totally positive definite, $T$ the ramified
primes, $U \supseteq T$ a finite set containing every $\mathfrak p \mid 2D$):
$$\mathrm{Mass}(\mathcal O_F^2)\,S^{\mathrm{reg}}_2(Q,1) = \mathrm{Mass}(L_E)\cdot2^{|T|}\prod_{\mathfrak p\in U}N\mathfrak p^{c_\mathfrak p}\cdot
|d_F|^{-1/2}\,\pi^n\,|N_{F/\mathbb Q}D|^{-1/2}\cdot\frac{\rho_F}{\rho_E}.$$
*Proof:* $\mathrm{Mass}(\mathcal O_F^2) = \mathrm{Mass}(L_E)\prod_Ur_\mathfrak p$ (`mass_eq_mass_mul_relRatio`, `relRatio_locStab_eq_prod`); the regularized
product may use $\chi_{E/F}$ instead of $\chi_Q$ (they agree off a finite set, `regProd_congr_finite`), and then
$L(1,\chi_{E/F}) = \rho_E/\rho_F$ (`hasLOne_relChar`) and $\beta_\mathfrak p(1-\chi_{E/F}(\mathfrak p)/N\mathfrak p)^{-1} = 1$ off $U$ (`localFactor_eq`). -/
@[kb "siegel1935" "Hauptsatz, n = 2 (mass formula of a binary norm form) [unverified]"]
theorem mass_mul_siegelProduct2Reg_eq (hpd : IsTotallyPosDef QD) {T : Finset (HeightOneSpectrum (𝓞 F))}
    (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) {U : Finset (HeightOneSpectrum (𝓞 F))} (hTU : T ⊆ U)
    (hU : ∀ v ∉ U, (2 * D : 𝓞 F) ∉ v.asIdeal) :
    mass QD (stdLat F 2) * siegelProduct2Reg (diagForm1 D) 1 =
      mass QD (latEL S) * (2 ^ T.card * ∏ v ∈ U, (qv v : ℝ) ^ cv S v) *
        (|(discr F : ℝ)| ^ (-(1 / 2 : ℝ)) * (Real.pi ^ Module.finrank ℚ F *
          |(Algebra.norm ℚ (algebraMap (𝓞 F) F D) : ℝ)| ^ (-(1 / 2 : ℝ)))) *
        (dedekindZeta_residue F / dedekindZeta_residue E) := by
  classical
  set β : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.localDensity v (diagForm1 D) 1 with hβdef
  set χE : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (relChar E v : ℝ) with hχEdef
  set r : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    relRatio (stabLat v (orthGroup QD (v.adicCompletion F)).subtype (loc v (latE S))) (stdStab QD v) with hrdef
  have hdeg := Algebra.IsQuadraticExtension.finrank_eq_two F E
  have hχE : ∀ v, |χE v| ≤ 1 := fun v => by
    have := abs_relChar_le_one hdeg v; simp only [χE]; exact_mod_cast this
  have hloc : ∀ v ∉ U, loc v (latE S) = std v := fun v hv => loc_latE_of_not_mem S v (hU v hv)
  have hunr : ∀ v ∉ U, relChar E v ≠ 0 := fun v hv h0 => hv (hTU ((hT v).mpr h0))
  have hβ : ∀ v ∉ U, β v = 1 - χE v / (normP v : ℝ) := fun v hv => by
    have h := localFactor_eq S v
    rw [relRatio_eq_one S (hloc v hv), cv_eq_zero S (hloc v hv), if_neg (hunr v hv), one_mul, pow_zero,
      one_mul] at h
    exact h
  set f : HeightOneSpectrum (𝓞 F) → ℝ := fun v => β v * (1 - χE v / (normP v : ℝ)) ^ (-1 : ℤ) with hfdef
  have hne : ∀ v, 1 - χE v / (normP v : ℝ) ≠ 0 := fun v => (one_sub_div_pos (hχE v) v).ne'
  have hf1 : ∀ v ∉ U, f v = 1 := fun v hv => by
    simp only [f]; rw [hβ v hv, _root_.zpow_neg_one, mul_inv_cancel₀ (hne v)]
  have hfm : Multipliable f := multipliable_of_ne_finset_one hf1
  -- χ_Q = χ_E off a finite set
  obtain ⟨S₂, hS₂⟩ : IsAlmostRelChar (fun v => chiP v (diagForm1 D)) E := by
    refine isAlmostRelChar_of_sqrt (δ := -(diagForm1 D).hessian.det) (θ := 2 * S.θ) ?_ ?_ ?_ ∅ ?_
    · rw [hessian_det_diagForm1]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) S.D_ne)
    · rw [mul_pow, S.sq, hessian_det_diagForm1]; simp only [map_neg, map_mul, map_ofNat]; ring
    · rw [map_mul, S.conj_eq, map_ofNat]; ring
    · intro v _ h2 hδ
      exact chiP_binary_eq_charNF v _ h2 fun h => hδ (v.asIdeal.neg_mem_iff.2 h)
  have hL : HasLOne χE (dedekindZeta_residue E / dedekindZeta_residue F) := hasLOne_relChar hdeg
  have hreg : regProd (fun v => chiP v (diagForm1 D)) (-1) β = regProd χE (-1) β :=
    regProd_congr_finite (fun v => abs_chiP_le _ v) hχE S₂ (fun v hv => hS₂ v hv)
      (by rw [hL.lOne_eq]; exact hL) (-1) β hfm
  have hregE : regProd χE (-1) β = (dedekindZeta_residue F / dedekindZeta_residue E) * ∏ v ∈ U, f v := by
    unfold regProd
    rw [hL.lOne_eq, _root_.zpow_neg_one, inv_div, tprod_eq_prod hf1]
  -- the mass comparison
  have hm := mass_eq_mass_mul_relRatio hpd (latEL S) (stdLat F 2) (isIntegral_latE S)
    (isIntegral_std (diagForm1 D))
  have hprod := relRatio_locStab_eq_prod QD (latEL S) U (fun v hv => hloc v hv)
  have hmU : mass QD (stdLat F 2) = mass QD (latEL S) * ∏ v ∈ U, r v := by
    rw [hm, relRatio_symm, hprod, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [relRatio_symm, inv_inv]
  -- the local factors on U
  have hrf : ∀ v, r v * f v = (qv v : ℝ) ^ cv S v * (if v ∈ T then 2 else 1) := fun v => by
    have h := localFactor_eq S v
    simp only [r, f, β, χE] at h ⊢
    rw [← mul_assoc, h, mul_assoc]
    congr 1
    by_cases h0 : relChar E v = 0
    · rw [if_pos h0, if_pos ((hT v).mpr h0), h0]; simp
    · rw [if_neg h0, if_neg (fun h => h0 ((hT v).mp h)), _root_.zpow_neg_one, mul_inv_cancel₀]
      exact hne v
  have hUT : ∏ v ∈ U, (if v ∈ T then (2 : ℝ) else 1) = 2 ^ T.card := by
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hTU, Finset.prod_const]
  unfold siegelProduct2Reg siegelProductWith
  rw [hreg, hregE, prod_archRepDensity_diagForm1, hmU]
  have hU2 : (∏ v ∈ U, r v) * ∏ v ∈ U, f v = 2 ^ T.card * ∏ v ∈ U, (qv v : ℝ) ^ cv S v := by
    rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun v _ => hrf v, Finset.prod_mul_distrib, hUT, mul_comm]
  have e : -(((2 : ℕ) : ℝ) - 1) / 2 = -(1 / 2 : ℝ) := by norm_num
  rw [e, ← hU2]
  ring

end QuadFormsKB.Tamagawa.BinaryCM
