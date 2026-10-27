/-
# Siegel's formula for representations of quadratic lattices by quadratic lattices, every rank

**Layer:** $F$ a totally real number field of **any class number**; $V = (F^N, Q_0)$ with an arbitrary integral lattice $L$ (`Lat F N`, any
Steinitz class); a totally positive quadratic lattice $T = (T_\ell, T_0)$ of rank $r$, $1 \le r \le N$, $T_\ell$ any lattice on $(F^r, T_0)$
(any Steinitz class: $T \cong \mathfrak a_0x_0\oplus\dots\oplus\mathfrak a_{r-1}x_{r-1}$).

**Defines**
* `siegelProductAllLat Q₀ L T₀ Tl`
  $= \mathrm{pre}(Q_0, T_0)\cdot\mathrm{prodAll}(\varepsilon\,\beta_\mathfrak p(L, T))$: the Siegel product in every
  rank with
  the local densities $\beta_\mathfrak p(L, T)$ of the lattices (`latBetaT`) in place of $\beta_\mathfrak p(Q_0, T_0)$ (plain for $N \ge 3$,
  $N - r \ne 2$ and $N = 1$, regularized by $L_F(1,\chi)$ for $N - r = 2$ and for $N = 2$, doubled for $N = 1$);
* `SiegelFormsAllLat Q₀ L T₀ Tl`: $\sum_{\mathrm{cls}M\subseteq\mathrm{gen}L} r(M, T)/|O(M)| = \mathrm{Mass}(L)\cdot$ `siegelProductAllLat`.

**Proves**
* `massComplement_eq` (**the identity K**): for a frame adapted to $T_0$ with complement $Q'$,
  $\mathrm{Mass}(\mathcal O_F^{n'}, Q') = \mathrm{Mass}(\mathcal O_F^N)\,\mathrm{pre}(T_0)\,\mathrm{prodAll}(u)\prod_\mathfrak p\|\det H_{T_0}\|^{n'}/\prod_\mathfrak p\|\det g\|^{n'+1}$,
  $u = \varepsilon\beta(Q_0,Q_0)/\beta(Q',Q')$. It does not involve $L$ or $T_\ell$. *Proof:* the
  `siegelForms_all_ranks` for
  $T_1 = c^2T_0$, $c \in \mathcal O_F$ clearing the denominators of the frame (so $\mathcal O_F^N$ represents $T_1$ and the product of its local
  type sums is not $0$), the global reduction and the local identity for $(\mathcal O_F^N, T_1)$, and the scaling back to $T_0$ (product
  formula).
* `siegelFormsAllLat_of_frame`: the formula given an adapted frame (assembly: global reduction, local identity for lattices,
  $\mathrm{Mass}(L)\prod_\mathfrak p r_\mathfrak p(L) = \mathrm{Mass}(\mathcal O_F^N)$, multiplicativity of `prodAll`, the identity K).
* **`siegelFormsLat_all_ranks`** (headline, **unconditional**).
* Consistency: `siegelFormsAllLat_std_iff` (free $L$ and $T$: the `SiegelFormsAll`); `mass_mul_siegelProductAllLat_self`
  ($T = L$: the mass formula for the genus of an arbitrary lattice, $\mathrm{Mass}(L)\cdot S(L, L) = 1$).

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameLatLocal
import QuadFormsKB.Tamagawa.FrameLatProd

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.FramesLat

open QuadFormsKB.Tamagawa Lattices LocalDensity Frames SiegelLat QuadFormsKB.HilbertModular LatChange

variable {F : Type} [Field F] [NumberField F] {N r : ℕ}

/-! ### The statement -/

/-- **Siegel's product for lattices, every rank** (Siegel 1935, Hauptsatz; Siegel 1937 over $F$ [unverified]):
`siegelProductAll` with the local densities $\varepsilon\,\beta_\mathfrak p(L, T)$ of the lattices (`siegelDensityLat`). The archimedean
factor is computed in the coordinates of $Q_0$ and $T_0$, matching the normalization of $\beta_\mathfrak p(L, T)$. -/
@[kb "siegel1935" "Hauptsatz (local side, lattices by lattices, every rank) [unverified]"]
def siegelProductAllLat (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) (T₀ : QuadForm (𝓞 F) r) (Tl : Lat F r) : ℝ :=
  preAll Q₀ T₀ * prodAll Q₀ T₀ (fun v => siegelDensityLat v Q₀ L T₀ Tl)

/-- **Siegel's formula for embeddings of the quadratic lattice $T = (T_\ell, T_0)$ into the genus of $L$** (Siegel 1935, Hauptsatz
[unverified]):
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r(M, T)}{|O(M)|} = \mathrm{Mass}(L)\cdot\texttt{siegelProductAllLat}(L, T).$$

Field:
- `repMass_eq`: the displayed identity.

A statement, not an input: proved for every $1 \le r \le N$ over every totally real field (`siegelFormsLat_all_ranks`). -/
@[kb "siegel1935" "Hauptsatz (lattices by lattices, every rank) [unverified]"]
structure SiegelFormsAllLat (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) (T₀ : QuadForm (𝓞 F) r) (Tl : Lat F r) : Prop where
  repMass_eq : repMassLat (formF Q₀) L Tl (formF T₀) = mass (formF Q₀) L * siegelProductAllLat Q₀ L T₀ Tl

/-! ### The core: global reduction and local factors of an arbitrary pair -/

section Core

variable [IsTotallyReal F] {n' : ℕ}

/-- $\mathrm{Mass}(L)\prod_\mathfrak p r_\mathfrak p(L) = \mathrm{Mass}(\mathcal O_F^N)$ (the lattice change). -/
theorem mass_mul_finprod_locRatio {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) (L : Lat F N)
    (hLi : Lattices.IsIntegral (formF Q₀) L.1) :
    mass (formF Q₀) L * ∏ᶠ v, locRatio v Q₀ L = mass (formF Q₀) (stdLat F N) := by
  rw [← relRatio_locStab_eq_finprod, mass_eq_mass_mul_relRatio hpd (stdLat F N) L (isIntegral_stdLat_map Q₀) hLi,
    mul_assoc, relRatio_mul_relRatio_symm, mul_one]
  have hc := commensurable_locStab (formF Q₀) (stdLat F N) L
  exact ⟨hc.1.relIndex_ne_zero, hc.2.relIndex_ne_zero⟩

/-- **The core of the argument for an arbitrary pair $(L, T)$** and an adapted frame: the global reduction
$r(\mathrm{gen}L, T) = \mathrm{Mass}(Q')\prod_\mathfrak pW_\mathfrak p$ and the local factors $\varepsilon\beta_\mathfrak p(L, T) = (W_\mathfrak p r_\mathfrak p E_\mathfrak p/G_\mathfrak p)\,u_\mathfrak p$, so
$\mathrm{prodAll}(\varepsilon\beta(L,T)) = \mathrm{prodAll}(u)\prod W\prod r\prod E/\prod G$. -/
theorem core (Q₀ : QuadForm (𝓞 F) (r + n')) (L : Lat F (r + n')) (T₀ : QuadForm (𝓞 F) r) (Tl : Lat F r) (hr : 1 ≤ r)
    (hpd : IsTotallyPosDef (formF Q₀)) (hpdT : IsTotallyPosDef (formF T₀)) (hLi : Lattices.IsIntegral (formF Q₀) L.1)
    (hTi : Lattices.IsIntegral (formF T₀) Tl.1) (fr : AdaptedFrameT (formF Q₀) (formF T₀))
    (hmult : ProdMult Q₀ T₀ (baseU Q₀ fr.Q' r)) :
    repMassLat (formF Q₀) L Tl (formF T₀) = mass (formF fr.Q') (stdLat F n') *
        ∏ᶠ v, locFrameTypeSumL v (formF T₀) (formF fr.Q') (loc v (Lat.image fr.g⁻¹ L).1) (loc v Tl.1) ∧
      prodAll Q₀ T₀ (fun v => siegelDensityLat v Q₀ L T₀ Tl) = prodAll Q₀ T₀ (baseU Q₀ fr.Q' r) *
        ((∏ᶠ v, locFrameTypeSumL v (formF T₀) (formF fr.Q') (loc v (Lat.image fr.g⁻¹ L).1) (loc v Tl.1)) *
          (∏ᶠ v, locRatio v Q₀ L) *
          (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ n') /
          ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n' + 1)) := by
  classical
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
  have hpdB : IsTotallyPosDef (blockForm (formF T₀) (formF fr.Q')) := by
    rw [← fr.compMat_eq]; exact isTotallyPosDef_compMat _ fr.g hpd
  have hpdQ' := isTotallyPosDef_of_blockForm_right hpdB
  have hQ' : fr.Q'.Nondegenerate := nondegenerate_of_map hpdQ'.nondegenerate
  have hLi' : Lattices.IsIntegral (blockForm (formF T₀) (formF fr.Q')) (Lat.image fr.g⁻¹ L).1 := by
    rw [← fr.compMat_eq]; exact isIntegral_compMat _ fr.g hLi
  refine ⟨?_, ?_⟩
  · rw [← repMassLat_compMat hpd fr.g hLi Tl (formF T₀), fr.compMat_eq]
    exact repMassLat_eq_mass_mul_finprod T₀ fr.Q' _ Tl hpdB hLi'
  -- the local factors
  set W : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    locFrameTypeSumL v (formF T₀) (formF fr.Q') (loc v (Lat.image fr.g⁻¹ L).1) (loc v Tl.1) with hWdef
  set ρ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => locRatio v Q₀ L with hρdef
  set E : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ n' with hEdef
  set G : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n' + 1) with hGdef
  have hx : algebraMap (𝓞 F) F T₀.hessian.det ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hT
  have hd : fr.g.val.det ≠ 0 := (Matrix.isUnits_det_units fr.g).ne_zero
  have hGpos : ∀ v, 0 < G v := fun v => pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr hd)) _
  have hlam' : ∀ v : HeightOneSpectrum (𝓞 F), 0 < NF.localDensityForm v fr.Q' fr.Q' := by
    intro v
    have h := siegelDensity_pos v fr.Q' hQ'
    unfold NF.siegelDensity at h
    rw [if_pos rfl] at h
    linarith
  have hloc : ∀ v, siegelDensityLat v Q₀ L T₀ Tl = (W v * ρ v * E v / G v) * baseU Q₀ fr.Q' r v := by
    intro v
    have hid := latFrameLocalIdentity v hr Q₀ hQ T₀ hT fr L hLi Tl hTi
    have h1 := hlam' v
    have h2 := hGpos v
    have hβ : latBetaT v Q₀ L T₀ Tl = (W v * ρ v * E v / G v) *
        (NF.localDensityForm v Q₀ Q₀ / NF.localDensityForm v fr.Q' fr.Q') := by
      simp only [hWdef, hρdef, hEdef, hGdef] at h2 ⊢
      rw [div_mul_div_comm, eq_div_iff (mul_pos h2 h1).ne']
      linear_combination (-1 : ℝ) * hid
    unfold siegelDensityLat baseU
    rw [hβ]
    ring
  -- finite supports
  have hWf : Function.HasFiniteMulSupport W :=
    hasFiniteMulSupport_locFrameTypeSumL T₀ fr.Q' (Lat.image fr.g⁻¹ L) Tl hpdB
  have hρf : Function.HasFiniteMulSupport ρ :=
    (Filter.eventually_cofinite.mp (loc_eventually_std L.2)).subset fun v hv => by
      by_contra h
      exact hv (locRatio_eq_one v Q₀ L (not_not.mp h))
  have hEf : Function.HasFiniteMulSupport E :=
    (finite_valuation_ne_one hx).subset fun v hv => by
      by_contra h
      simp only [Set.mem_setOf_eq, not_not] at h
      apply hv
      simp only [hEdef]
      rw [norm_algebraMap_eq_one h, one_pow]
  have hGf : Function.HasFiniteMulSupport G :=
    (finite_valuation_ne_one hd).subset fun v hv => by
      by_contra h
      simp only [Set.mem_setOf_eq, not_not] at h
      apply hv
      simp only [hGdef]
      rw [norm_algebraMap_eq_one h, one_pow]
  have haf : Function.HasFiniteMulSupport fun v => W v * ρ v * E v / G v :=
    (((hWf.mul hρf).mul hEf).div hGf)
  rw [show (fun v => siegelDensityLat v Q₀ L T₀ Tl) = fun v => (W v * ρ v * E v / G v) * baseU Q₀ fr.Q' r v from
    funext hloc, hmult _ haf]
  congr 1
  rw [finprod_div_distrib (f := fun v => W v * ρ v * E v) (((hWf.mul hρf).mul hEf)) hGf,
    finprod_mul_distrib (f := fun v => W v * ρ v) (hWf.mul hρf) hEf, finprod_mul_distrib hWf hρf]

/-- $\mathrm{diag}(a1_r, 1)\,E = aE$. -/
theorem blockMat_smul_one_mul_stdFrameMat {A : Type*} [CommRing A] {r n' : ℕ} (a : A) :
    blockMat (a • (1 : Matrix (Fin r) (Fin r) A)) 0 0 (1 : Matrix (Fin n') (Fin n') A) * stdFrameMat =
      a • stdFrameMat := by
  ext i j
  refine (Matrix.mul_apply (M := blockMat (a • 1) 0 0 1) (N := stdFrameMat)).trans ?_
  simp only [Fin.sum_univ_add]
  induction i using Fin.addCases with
  | left i =>
    show _ = a * (if Fin.castAdd n' i = Fin.castAdd n' j then 1 else 0)
    simp [Matrix.one_apply, stdFrameMat, Fin.castAdd_inj, eq_comm]
  | right i =>
    show _ = a * (if Fin.natAdd r i = Fin.castAdd n' j then 1 else 0)
    simp [stdFrameMat, Ne.symm (castAdd_ne_natAdd _ _)]

/-- **The identity K** (module docstring): for a frame adapted to $T_0$ with complement $Q'$,
$$\mathrm{Mass}(\mathcal O_F^{n'}, Q') = \mathrm{Mass}(\mathcal O_F^N)\,\mathrm{pre}(T_0)\,\mathrm{prodAll}(u)\,
  \frac{\prod_\mathfrak p\|\det H_{T_0}\|_\mathfrak p^{n'}}{\prod_\mathfrak p\|\det g\|_\mathfrak p^{n'+1}}.$$ -/
theorem massComplement_eq (Q₀ : QuadForm (𝓞 F) (r + n')) (T₀ : QuadForm (𝓞 F) r) (hr : 1 ≤ r)
    (hpd : IsTotallyPosDef (formF Q₀)) (hpdT : IsTotallyPosDef (formF T₀)) (fr : AdaptedFrameT (formF Q₀) (formF T₀)) :
    mass (formF fr.Q') (stdLat F n') = mass (formF Q₀) (stdLat F (r + n')) * preAll Q₀ T₀ *
      prodAll Q₀ T₀ (baseU Q₀ fr.Q' r) *
      ((∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ n') /
        ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n' + 1)) := by
  classical
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
  obtain ⟨c, hc0, hcint⟩ := exists_mul_integral fr.g.val
  set cF : F := algebraMap (𝓞 F) F c with hcFdef
  have hcF : cF ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hc0
  set T₁ : QuadForm (𝓞 F) r := T₀.compMat (c • (1 : Matrix (Fin r) (Fin r) (𝓞 F))) with hT₁def
  -- the scaling matrices
  have hPdet : (cF • (1 : Matrix (Fin r) (Fin r) F)).det ≠ 0 := by
    rw [det_smul, det_one, mul_one]; exact pow_ne_zero _ hcF
  set P : GL (Fin r) F := Matrix.nonsingInvUnit _ (isUnit_iff_ne_zero.mpr hPdet) with hPdef
  have hDdet : (blockMat (cF • (1 : Matrix (Fin r) (Fin r) F)) 0 0 (1 : Matrix (Fin n') (Fin n') F)).det ≠ 0 := by
    rw [det_blockMat_diag, det_one, mul_one]; exact hPdet
  set D : GL (Fin (r + n')) F := Matrix.nonsingInvUnit _ (isUnit_iff_ne_zero.mpr hDdet) with hDdef
  have hmapP : (c • (1 : Matrix (Fin r) (Fin r) (𝓞 F))).map (algebraMap (𝓞 F) F) = cF • 1 := by
    ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, hcFdef]; split_ifs <;> simp
  have hformT₁ : formF T₁ = (formF T₀).compMat (cF • 1) := by
    rw [hT₁def, formF, ← QuadForm.map_compMat, hmapP]
  have hpdT₁ : IsTotallyPosDef (formF T₁) := by
    rw [hformT₁]; exact isTotallyPosDef_compMat _ P hpdT
  have hcomp₁ : (formF Q₀).compMat (fr.g * D).val = blockForm (formF T₁) (formF fr.Q') := by
    rw [Units.val_mul, ← QuadForm.compMat_mul, fr.compMat_eq]
    show (blockForm (formF T₀) (formF fr.Q')).compMat (blockMat (cF • 1) 0 0 1) = _
    rw [compMat_blockMat_diag, QuadForm.compMat_one, ← hformT₁]
  let fr₁ : AdaptedFrameT (formF Q₀) (formF T₁) := ⟨fr.g * D, fr.Q', hcomp₁⟩
  -- the all-ranks formula for `T₁`
  have hB := (siegelForms_all_ranks Q₀ T₁ hr (by omega) hpd hpdT₁).repMass_eq
  rw [siegelProductAll_eq] at hB
  -- the core for `(𝒪^N, 𝒪^r, T₁)`
  obtain ⟨c1, c2⟩ := core Q₀ (stdLat F (r + n')) T₁ (stdLat F r) hr hpd hpdT₁ (isIntegral_stdLat_map Q₀)
    (isIntegral_stdLat_map T₁) fr₁ (prodMult_baseU Q₀ T₁ hr hpd hpdT₁ fr₁)
  have hsd : (fun v => siegelDensityLat v Q₀ (stdLat F (r + n')) T₁ (stdLat F r)) =
      fun v => NF.siegelDensity v Q₀ T₁ := by
    funext v
    unfold siegelDensityLat NF.siegelDensity epsNR
    rw [latBetaT_of_std v (by omega) hr Q₀ _ (isIntegral_stdLat_map Q₀) T₁ _ (isIntegral_stdLat_map T₁)
      (loc_intVec v) (loc_intVec v)]
    by_cases h : r = r + n'
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  have hρ1 : ∏ᶠ v, locRatio v Q₀ (stdLat F (r + n')) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => locRatio_eq_one v Q₀ _ (loc_intVec v)
  rw [hsd, hρ1, mul_one, prodAll_scale Q₀ T₀ hr hpd hpdT fr hc0] at c2
  rw [repMassLat_stdLat] at c1
  -- positivity of the product of the local type sums
  have hX₁T : (formF Q₀).compMat ((fr.g * D).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) : Matrix (Fin (r + n')) (Fin r) F) = formF T₁ := by
    rw [← QuadForm.compMat_mul, hcomp₁, compMat_stdFrameMat]
  have hX₁ : ∀ t ∈ (stdLat F r).1, ((fr.g * D).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) : Matrix (Fin (r + n')) (Fin r) F) *ᵥ t ∈ (stdLat F (r + n')).1 := by
    intro t ht
    have hDE : (D.val : Matrix (Fin (r + n')) (Fin (r + n')) F) * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) = cF • (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) :=
      blockMat_smul_one_mul_stdFrameMat cF
    rw [show ((fr.g * D).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) : Matrix (Fin (r + n')) (Fin r) F) =
        (fr.g.val : Matrix (Fin (r + n')) (Fin (r + n')) F) * ((D.val : Matrix (Fin (r + n')) (Fin (r + n')) F) *
          (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F)) by
      rw [Units.val_mul, Matrix.mul_assoc], hDE, Matrix.mul_smul]
    intro i
    obtain ⟨z, hz⟩ := mem_intVec_iff_exists.mp ht
    choose w hw using hcint
    refine ⟨∑ j : Fin r, w i (Fin.castAdd n' j) * z j, ?_⟩
    rw [← hz]
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, map_sum, map_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hsum : ∑ j, fr.g.val i j * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) j x = fr.g.val i (Fin.castAdd n' x) := by
      simp [stdFrameMat, Matrix.of_apply]
    rw [hsum, ← hw]
  have hpos := repMassLat_pos_of_mem hpd (isIntegral_stdLat_map Q₀) (stdLat F r) (formF T₁) _ hX₁ hX₁T
  rw [repMassLat_stdLat, c1] at hpos
  set W₁ := ∏ᶠ v, locFrameTypeSumL v (formF T₁) (formF fr₁.Q') (loc v (Lat.image fr₁.g⁻¹ (stdLat F (r + n'))).1)
    (loc v (stdLat F r).1) with hW₁def
  have hW₁ : W₁ ≠ 0 := fun h0 => by rw [h0, mul_zero] at hpos; exact lt_irrefl _ hpos
  -- the determinants
  set x : F := algebraMap (𝓞 F) F T₀.hessian.det with hxdef
  have hx : x ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hT
  set d : F := fr.g.val.det with hddef
  have hd : d ≠ 0 := (Matrix.isUnits_det_units fr.g).ne_zero
  have hx₁ : algebraMap (𝓞 F) F T₁.hessian.det = cF ^ (2 * r) * x := by
    rw [hT₁def, QuadForm.hessian_compMat, det_mul, det_mul, det_transpose, det_smul, det_one, mul_one, map_mul, map_mul,
      map_pow, hxdef, ← hcFdef, Fintype.card_fin]
    ring
  have hd₁ : (fr₁.g).val.det = cF ^ r * d := by
    show (fr.g * D).val.det = _
    rw [Units.val_mul, det_mul]
    show d * (blockMat (cF • (1 : Matrix (Fin r) (Fin r) F)) 0 0 1).det = _
    rw [det_blockMat_diag, det_one, mul_one, det_smul, det_one, mul_one, Fintype.card_fin]
    ring
  have hx₁0 : cF ^ (2 * r) * x ≠ 0 := mul_ne_zero (pow_ne_zero _ hcF) hx
  have hd₁0 : cF ^ r * d ≠ 0 := mul_ne_zero (pow_ne_zero _ hcF) hd
  rw [hx₁, hd₁, finprod_norm_pow_eq _ hx₁0, finprod_norm_pow_eq _ hd₁0] at c2
  rw [finprod_norm_pow_eq _ hx, finprod_norm_pow_eq _ hd]
  have hprod : ∀ a b : F, ∏ σ : F →ₐ[ℚ] ℂ, ‖σ (a * b)‖ = (∏ σ : F →ₐ[ℚ] ℂ, ‖σ a‖) * ∏ σ : F →ₐ[ℚ] ℂ, ‖σ b‖ := by
    intro a b
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun σ _ => by rw [map_mul, norm_mul]
  have hpow : ∀ (a : F) (k : ℕ), ∏ σ : F →ₐ[ℚ] ℂ, ‖σ (a ^ k)‖ = (∏ σ : F →ₐ[ℚ] ℂ, ‖σ a‖) ^ k := by
    intro a k
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun σ _ => by rw [map_pow, norm_pow]
  rw [hprod, hprod, hpow, hpow] at c2
  rw [preAll_scale Q₀ T₀ hpd hpdT hc0] at hB
  set C := ∏ σ : F →ₐ[ℚ] ℂ, ‖σ cF‖ with hCdef
  have hCpos : 0 < C := Finset.prod_pos fun σ _ => norm_pos_iff.mpr ((map_ne_zero σ).mpr hcF)
  set Cx := ∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖
  have hCx : 0 < Cx := Finset.prod_pos fun σ _ => norm_pos_iff.mpr ((map_ne_zero σ).mpr hx)
  set Cd := ∏ σ : F →ₐ[ℚ] ℂ, ‖σ d‖
  have hCd : 0 < Cd := Finset.prod_pos fun σ _ => norm_pos_iff.mpr ((map_ne_zero σ).mpr hd)
  have hCr : C ^ ((r : ℝ) * (((r + n' : ℕ) : ℝ) - r - 1)) * C ^ (r * (n' + 1)) = C ^ (2 * r * n') := by
    rw [← Real.rpow_natCast C (r * (n' + 1)), ← Real.rpow_add hCpos, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  rw [hB, c2] at c1
  have hmass := c1
  rw [mul_inv, mul_inv, mul_pow, mul_pow, inv_pow (C ^ (2 * r)), inv_pow (C ^ r), ← pow_mul, ← pow_mul] at hmass
  have hZ : C ^ ((r : ℝ) * (((r + n' : ℕ) : ℝ) - r - 1)) = C ^ (2 * r * n') / C ^ (r * (n' + 1)) := by
    rw [eq_div_iff (by positivity), hCr]
  rw [hZ] at hmass
  generalize prodAll Q₀ T₀ (baseU Q₀ fr.Q' r) = Pu at hmass ⊢
  generalize preAll Q₀ T₀ = Pr at hmass ⊢
  apply mul_right_cancel₀ hW₁
  have hC2 : C ^ (2 * r * n') ≠ 0 := by positivity
  have hCrr : C ^ (r * (n' + 1)) ≠ 0 := by positivity
  refine hmass.symm.trans ?_
  field_simp

/-- **Siegel's formula for lattices, given a frame adapted to $T_0$** (assembly; module docstring). -/
theorem siegelFormsAllLat_of_frame (Q₀ : QuadForm (𝓞 F) (r + n')) (L : Lat F (r + n')) (T₀ : QuadForm (𝓞 F) r)
    (Tl : Lat F r) (hr : 1 ≤ r) (hpd : IsTotallyPosDef (formF Q₀)) (hpdT : IsTotallyPosDef (formF T₀))
    (hLi : Lattices.IsIntegral (formF Q₀) L.1) (hTi : Lattices.IsIntegral (formF T₀) Tl.1)
    (fr : AdaptedFrameT (formF Q₀) (formF T₀)) : SiegelFormsAllLat Q₀ L T₀ Tl := by
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  obtain ⟨h1, h2⟩ := core Q₀ L T₀ Tl hr hpd hpdT hLi hTi fr (prodMult_baseU Q₀ T₀ hr hpd hpdT fr)
  have hK := massComplement_eq Q₀ T₀ hr hpd hpdT fr
  have hm := mass_mul_finprod_locRatio Q₀ hpd L hLi
  refine ⟨?_⟩
  unfold siegelProductAllLat
  rw [h1, h2, hK, ← hm]
  ring

end Core

/-! ### The headline -/

/-- **Not represented over $F$:** both sides vanish. -/
theorem siegelFormsAllLat_of_not_rep [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) (T₀ : QuadForm (𝓞 F) r)
    (Tl : Lat F r) (hrN : r ≤ N) (hpd : IsTotallyPosDef (formF Q₀)) (hpdT : IsTotallyPosDef (formF T₀))
    (h : ¬ ∃ X : Matrix (Fin N) (Fin r) F, (formF Q₀).compMat X = formF T₀) : SiegelFormsAllLat Q₀ L T₀ Tl := by
  refine ⟨?_⟩
  rw [repMassLat_eq_zero_of_not_rep _ _ _ _ h]
  obtain ⟨v, hv⟩ := exists_local_not_rep Q₀ T₀ hpd hpdT h
  have h0 := latBetaT_eq_zero_of_not_rep v hrN Q₀ L T₀ (nondegenerate_of_map hpdT.nondegenerate) Tl hv
  unfold siegelProductAllLat
  rw [prodAll_eq_zero_of_exists Q₀ T₀ ⟨v, by unfold siegelDensityLat; rw [h0, mul_zero]⟩]
  ring

/-- **Siegel's formula for representations of quadratic lattices by quadratic lattices, in every rank, over every totally real
field, any class number (unconditional).** For $Q_0$ over $\mathcal O_F$ of rank $N$ totally positive definite, $L$ any lattice on
$(F^N, Q_0)$ with $Q_0$ integral on $L$ (any Steinitz class), $T_0$ over $\mathcal O_F$ of rank $r$ totally positive definite, $T_\ell$ any lattice on
$(F^r, T_0)$ with $T_0$ integral on $T_\ell$ (any Steinitz class), $1 \le r \le N$:
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r(M, T)}{|O(M)|} = \mathrm{Mass}(L)\cdot\texttt{siegelProductAllLat}(L, T),$$
$r(M, T)$ the number of isometric embeddings $T \to M$, the product read as in `siegelProductAll` (plain for
$N \ge 3$, $N - r \ne 2$; regularized by
$L_F(1,\chi)$ for $N - r = 2$ and for $N = 2$; doubled for $N = 1$) with the local densities $\beta_\mathfrak p(L, T)$ of the lattices. -/
@[kb "siegel1935" "Hauptsatz (lattices by lattices, every rank r ≤ N), over a totally real field [unverified]"]
theorem siegelFormsLat_all_ranks [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) (T₀ : QuadForm (𝓞 F) r)
    (Tl : Lat F r) (hr : 1 ≤ r) (hrN : r ≤ N) (hpd : IsTotallyPosDef (formF Q₀)) (hpdT : IsTotallyPosDef (formF T₀))
    (hLi : Lattices.IsIntegral (formF Q₀) L.1) (hTi : Lattices.IsIntegral (formF T₀) Tl.1) :
    SiegelFormsAllLat Q₀ L T₀ Tl := by
  obtain ⟨n', rfl⟩ : ∃ n', N = r + n' := ⟨N - r, by omega⟩
  by_cases h : ∃ X : Matrix (Fin (r + n')) (Fin r) F, (formF Q₀).compMat X = formF T₀
  · obtain ⟨X, hX⟩ := h
    obtain ⟨fr⟩ := exists_adaptedFrameT _ _ hpdT.nondegenerate X hX
    exact siegelFormsAllLat_of_frame Q₀ L T₀ Tl hr hpd hpdT hLi hTi fr
  · exact siegelFormsAllLat_of_not_rep Q₀ L T₀ Tl hrN hpd hpdT h

end QuadFormsKB.Tamagawa.FramesLat
