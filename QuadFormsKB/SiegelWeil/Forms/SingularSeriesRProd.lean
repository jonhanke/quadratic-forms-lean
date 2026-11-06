/-
# The terms of the singular series of degree $r$ as products of local terms
**Layer:** global over a number field $F$, through the product formula for the standard character.

**Setting.** $Q = \sum_{i<n}b_ix_i^2$, $b_i \in \mathcal O_F\setminus\{0\}$, $n = 2m$, $\Phi_v = \mathbf 1_{L_v^r}$ at every finite place $v$; a form $T$ in
$r$ variables over $F$ with (upper-triangular) coefficient matrix $C_T$; $B = \operatorname{symOf}(u)$ for upper coordinates $u \in F^{\{i\le i'\}}$;
$\langle T, u\rangle = \sum_{i\le i'}c_{ii'}u_{ii'} = \operatorname{tr}(T_GB)$ (`pairTF`, the global `pairT`).

**Results.**
* `trace_coeff_mul_symOf`: $\operatorname{tr}(C_T\operatorname{symOf}(u)) = \sum_{i\le i'}c_{ii'}u_{ii'}$ (because $C_T$ is upper triangular).
* `cexp_trace_eq_finprod_psiV`: $e(\operatorname{Tr}_{F/\mathbb Q}x) = \prod_v\psi_v(-x)$ for $x \in F$ (the product formula,
  `finprod_psiV_eq_fourierChar`).
* **`fFinR_mul_eT_eq_finprod`**: the term of the singular series is a product of local terms,
  $$f_f(w\,n(B), s_0)\,e_T(\sigma(B)) = \prod_{v<\infty}f_v(w\,n(B))\,\psi_v(-\langle T, u\rangle),$$
  each factor being the integrand of the local Whittaker integral `whittakerTrR` at $u$.

Sources: Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. Math. 36 (1935), § 3 [unverified]; Weil, Acta Math.
113 (1965), Ch. II [unverified]; Tate's thesis (Cassels–Fröhlich, Ch. XV, Lemma 4.1.5) for the product formula.
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinUnfold

open Matrix NumberField IsDedekindDomain
open QuadFormsKB.HilbertModular QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData
  QuadFormsKB.WeilRep.Genus

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

/-! ### Algebra -/

section Alg

variable {K : Type*} [CommRing K] {r : ℕ}

/-- $\langle T, u\rangle = \sum_{i\le i'}c_{ii'}u_{ii'}$ over any commutative ring (the global version of `pairT`). -/
def pairTF (T : QuadForm K r) (u : SymIdx r → K) : K := ∑ p : SymIdx r, u p * T.coeff p.1.1 p.1.2

lemma symOf_map {K' : Type*} [CommRing K'] (f : K →+* K') (u : SymIdx r → K) :
    (symOf u).map f = symOf (fun p => f (u p)) := by
  ext i j; simp only [symOf, map_apply, of_apply]; split_ifs <;> rfl

/-- $\operatorname{tr}(C_T\operatorname{symOf}(u)) = \sum_{i\le i'}c_{ii'}u_{ii'}$. -/
lemma trace_coeff_mul_symOf (T : QuadForm K r) (u : SymIdx r → K) :
    trace (T.coeff * symOf u) = pairTF T u := by
  have e : trace (T.coeff * symOf u) = ∑ i, ∑ j, T.coeff i j * symOf u j i := by
    simp only [trace, diag, mul_apply]
  rw [e, sum_eq_sum_symIdx, pairTF]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨⟨i, j⟩, hij⟩ := p
  dsimp only
  by_cases h : i = j
  · subst h; simp [symOf, mul_comm]
  · have hlt : i < j := lt_of_le_of_ne hij h
    rw [ite_eq_right_iff.mpr (fun h' => absurd h' h), T.upper hlt]
    simp [symOf, not_le.mpr hlt, mul_comm]

end Alg

variable {F : Type} [Field F] [NumberField F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

lemma locSp_spW {k k' : Type*} [Field k] [Field k'] (ι : k →+* k') : locSp ι (spW : Sp r k) = spW := by
  apply Subtype.ext
  rw [locSp_coe, spW_coe, spW_coe, fromBlocks_map]
  simp [Matrix.map_one ι (map_zero ι) (map_one ι), Matrix.map_neg]

/-- The local image $u_v$ of global upper coordinates. -/
abbrev locU (v : HeightOneSpectrum (𝓞 F)) (u : SymIdx r → F) : SymIdx r → v.adicCompletion F :=
  fun p => algebraMap F (v.adicCompletion F) (u p)

/-- **The product formula**: $e(\operatorname{Tr}_{F/\mathbb Q}x) = \prod_v\psi_v(-x)$ for $x \in F$. -/
theorem cexp_trace_eq_finprod_psiV (x : F) :
    Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), (psiV v (-algebraMap F (v.adicCompletion F) x) : ℂ) := by
  have h := finprod_psiV_eq_fourierChar (-x)
  simp only [map_neg] at h
  have hfin := hasFiniteMulSupport_psiV (F := F) (-x)
  simp only [map_neg] at hfin
  have e : ∀ v : HeightOneSpectrum (𝓞 F), (psiV v (-algebraMap F (v.adicCompletion F) x) : ℂ) =
      Circle.coeHom (psiV v (-algebraMap F (v.adicCompletion F) x)) := fun v => rfl
  simp_rw [e]
  rw [← MonoidHom.map_finprod Circle.coeHom hfin, h]
  change _ = Complex.exp ((((2 * Real.pi * (-(((-(Algebra.trace ℚ F x) : ℚ)) : ℝ))) : ℝ) : ℂ) * Complex.I)
  congr 1
  push_cast
  ring

lemma pairT_locU (v : HeightOneSpectrum (𝓞 F)) (T : QuadForm F r) (u : SymIdx r → F) :
    pairT v (T.map (algebraMap F (v.adicCompletion F))) (locU v u) = algebraMap F (v.adicCompletion F) (pairTF T u) := by
  simp only [pairT, pairTF, map_sum, map_mul, locU]
  rfl

/-- $e_T(\sigma(B)) = \prod_v\psi_v(-\langle T, u\rangle)$. -/
theorem eT_realMat_eq_finprod [IsTotallyReal F] (T : QuadForm F r) (u : SymIdx r → F) :
    eT T (realMat (symOf u)) = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      (psiV v (-pairT v (T.map (algebraMap F (v.adicCompletion F))) (locU v u)) : ℂ) := by
  rw [eT, trPair_realMat, trace_gramT_mul T (symOf_transpose u), trace_coeff_mul_symOf, cexp_trace_eq_finprod_psiV]
  simp only [pairT_locU]

lemma locSpV_spW_spN (v : HeightOneSpectrum (𝓞 F)) (u : SymIdx r → F) :
    locSpV v (spW * spN (symOf u) (symOf_transpose u)) =
      spW * spN (symOf (locU v u)) (symOf_transpose _) := by
  rw [map_mul, locSp_spW, locSp_spN]
  congr 2
  exact symOf_map _ u

/-- $f_f(w\,n(B), s_0) = \prod_vf_v(w\,n(B))$ (`wfunR` at the local image). -/
lemma fFinR_eq_finprod (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (u : SymIdx r → F) :
    fFinR b hb u = ∏ᶠ v : HeightOneSpectrum (𝓞 F), wfunR v (aV (unitsOfInt b hb) v) (locU v u) := by
  unfold fFinR
  rw [finSecR_sZero]
  congr 1; funext v
  rw [locSpV_spW_spN]
  rfl

lemma hasFiniteMulSupport_wfunR (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (u : SymIdx r → F) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => wfunR v (aV (unitsOfInt b hb) v) (locU v u) := by
  have h := hasFiniteMulSupport_secSR (unitsOfInt b hb) (fun v => oneSG v m r) (Filter.Eventually.of_forall fun _ => rfl)
    (spW * spN (symOf u) (symOf_transpose u)) (sZero m r)
  have e : (fun v : HeightOneSpectrum (𝓞 F) => secSR v (aV (unitsOfInt b hb) v) (oneSG v m r)
      (locSpV v (spW * spN (symOf u) (symOf_transpose u))) (sZero m r)) =
      fun v => wfunR v (aV (unitsOfInt b hb) v) (locU v u) := by
    funext v
    simp only [secSR, sub_self, neg_zero, Complex.cpow_zero, mul_one]
    rw [locSpV_spW_spN]
    rfl
  rw [e] at h
  exact h

/-- **The term of the singular series is a product of local Whittaker integrands**:
$f_f(w\,n(B), s_0)\,e_T(\sigma(B)) = \prod_{v<\infty}f_v(w\,n(B))\,\psi_v(-\langle T, u\rangle)$, $B = \operatorname{symOf}(u)$. -/
@[kb "weil1965" "Ch. II (factorization of the global section and of the character) [unverified]"]
theorem fFinR_mul_eT_eq_finprod [IsTotallyReal F] (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (T : QuadForm F r)
    (u : SymIdx r → F) :
    fFinR b hb u * eT T (realMat (symOf u)) = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      wfunR v (aV (unitsOfInt b hb) v) (locU v u) *
        (psiV v (-pairT v (T.map (algebraMap F (v.adicCompletion F))) (locU v u)) : ℂ) := by
  rw [fFinR_eq_finprod, eT_realMat_eq_finprod, ← finprod_mul_distrib (hasFiniteMulSupport_wfunR b hb u)]
  have hfin := hasFiniteMulSupport_psiV (F := F) (-pairTF T u)
  have hfin' : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => psiV v
      (algebraMap F (v.adicCompletion F) (-pairTF T u))).Finite := hfin
  refine Set.Finite.subset hfin' fun v hv => ?_
  simp only [Function.mem_mulSupport] at hv ⊢
  rw [pairT_locU, ← map_neg] at hv
  intro h; exact hv (by rw [h]; rfl)

end QuadFormsKB.SiegelWeil.Forms
