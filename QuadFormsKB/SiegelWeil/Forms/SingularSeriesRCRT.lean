/-
# The truncated singular series of degree $r$ is a product of truncated local Whittaker integrals

**Layer:** global over a totally real number field $F$; the Chinese remainder theorem over $\mathcal O_F$, then local at each finite
place (dyadic places included).

**Setting.** $Q = \sum_{i<n}b_ix_i^2$, $b_i \in \mathcal O_F\setminus\{0\}$, $n = 2m$, $\Phi_v = \mathbf 1_{L_v^r}$ at every finite place; $T_0$ a form in
$r$ variables over $\mathcal O_F$, $T = T_0$ over $F$; $c \in \mathcal O_F\setminus\{0\}$ with $(c) = \prod_\mathfrak p\mathfrak p^{e_\mathfrak p}$. The
symmetric matrices $B \in c^{-1}\mathrm{Sym}_r(\mathcal O_F)$ modulo $\mathrm{Sym}_r(\mathcal O_F)$ are $B = \operatorname{symOf}(u)$,
$u_p = \tilde a_p/c$ for $a \in (\mathcal O_F/c)^{\{i\le i'\}}$ (`uOf`).

**Result.** **`truncSS_eq_finprod`**:
$$\sum_{a\in(\mathcal O_F/c)^{\{i\le i'\}}}f_f(w\,n(B_a), s_0)\,e_T(\sigma(B_a)) =
  \prod_{v<\infty}\operatorname{vol}(\mathcal O_v)^{-r(r+1)/2}\int_{\mathrm{Sym}_r(\mathfrak p_v^{-e_v})}f_v(w\,n(B))\,\psi_v(-\operatorname{tr}(T_GB))\,dB,$$
the right side a finite product (`whittakerTrR` at level $e_v$; at $v \nmid c$ the factor is $f_v(w)$, which is $1$ at good places).
*Proof.* Each term is $\prod_vf_v(w\,n(B))\psi_v(-\langle T, u\rangle)$ (`fFinR_mul_eT_eq_finprod`, the product formula); the factor at $v$
depends only on $a \bmod \mathfrak p_v^{e_v}$ (`wgR_add_int`), and for that residue $x$ it is the value at the representative
$\tilde x/c$ of `resRho`; the Chinese remainder theorem $\mathcal O_F/c \cong \prod_\mathfrak p\mathcal O_F/\mathfrak p^{e_\mathfrak p}$ turns the sum of
products into the product of the local sums, and each local sum is the truncated local Whittaker integral divided by
$\operatorname{vol}(\mathcal O_v)^{r(r+1)/2}$ (`whittakerTrR_eq_sum`).

Sources: Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. Math. 36 (1935), § 3 (multiplicativity of the singular
series) [unverified]; Weil, Acta Math. 113 (1965), Ch. II [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.SingularSeriesRResidue
import QuadFormsKB.SiegelWeil.Forms.SingularSeriesRSum

open Matrix NumberField IsDedekindDomain WithZero
open QuadFormsKB.HilbertModular QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData
  QuadFormsKB.WeilRep.Genus

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-- The exponent $e_v = v_\mathfrak p((c))$. -/
abbrev eC (c : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) : ℕ := SingularNF.ordI v (Ideal.span {c})

lemma span_le_pow_eC (c : 𝓞 F) (hc : c ≠ 0) (v : HeightOneSpectrum (𝓞 F)) : Ideal.span {c} ≤ v.asIdeal ^ eC c v := by
  have hI : Ideal.span {c} ≠ ⊥ := by simpa using hc
  exact Ideal.le_of_dvd ((SingularNF.pow_dvd_iff_le_ordI v hI _).mpr le_rfl)

/-- The reduction $\mathcal O_F/c \to \mathcal O_F/\mathfrak p_v^{e_v}$. -/
def redV (c : 𝓞 F) (hc : c ≠ 0) (v : HeightOneSpectrum (𝓞 F)) : 𝓞 F ⧸ Ideal.span {c} →+* 𝓞 F ⧸ v.asIdeal ^ eC c v :=
  Ideal.Quotient.factor (span_le_pow_eC c hc v)

lemma redV_mk (c : 𝓞 F) (hc : c ≠ 0) (v : HeightOneSpectrum (𝓞 F)) (o : 𝓞 F) :
    redV c hc v (Ideal.Quotient.mk _ o) = Ideal.Quotient.mk _ o := rfl

/-- $(\tilde a - \widetilde{a \bmod \mathfrak p^{e}})/c$ is $v$-integral. -/
lemma valued_out_sub_out_div_le (c : 𝓞 F) (hc : c ≠ 0) (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F ⧸ Ideal.span {c}) :
    Valued.v (algebraMap F (v.adicCompletion F)
      ((ιO (Quotient.out x) - ιO (Quotient.out (redV c hc v x))) / ιO c)) ≤ 1 := by
  have hmem : Quotient.out x - Quotient.out (redV c hc v x) ∈ v.asIdeal ^ eC c v := by
    rw [← Ideal.Quotient.eq]
    have h1 : (Ideal.Quotient.mk (v.asIdeal ^ eC c v) (Quotient.out (redV c hc v x))) = redV c hc v x :=
      Ideal.Quotient.mk_out _
    have h2 : redV c hc v x = Ideal.Quotient.mk _ (Quotient.out x) := by
      conv_lhs => rw [← Ideal.Quotient.mk_out x]
      rfl
    rw [h1, h2]
  have h1 := (valued_algebraMap_int_le_iff v _ (eC c v)).mpr hmem
  have h2 := valued_algebraMap_int_eq v c hc
  have hc0 : Valued.v (algebraMap F (v.adicCompletion F) (ιO c)) ≠ 0 := by rw [h2]; exact exp_ne_zero
  rw [map_div₀, map_div₀, div_le_one₀ (zero_lt_iff.mpr hc0), h2]
  simpa only [map_sub] using h1

/-- The local factor $x \mapsto f_v(w\,n(\tilde x/c))\,\psi_v(-\langle T, \tilde x/c\rangle)$ on $(\mathcal O_F/\mathfrak p_v^{e_v})^{\{i\le i'\}}$. -/
def gLocR (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (T : QuadForm F r) (c : 𝓞 F) (v : HeightOneSpectrum (𝓞 F))
    (x : SymIdx r → 𝓞 F ⧸ v.asIdeal ^ eC c v) : ℂ :=
  wgR v (aV (unitsOfInt b hb) v) (T.map (algebraMap F (v.adicCompletion F))) (fun p => resRho c v (x p))

lemma valued_coeff_map_int (v : HeightOneSpectrum (𝓞 F)) (T₀ : QuadForm (𝓞 F) r) (i j : Fin r) :
    Valued.v (((T₀.map (algebraMap (𝓞 F) F)).map (algebraMap F (v.adicCompletion F))).coeff i j) ≤ 1 := by
  simp only [QuadForm.map, Matrix.map_apply]
  exact valued_algebraMap_int v _

/-- The factor at $v$ of the global term depends only on the residue modulo $\mathfrak p_v^{e_v}$. -/
lemma wgR_locU_uOf (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (T₀ : QuadForm (𝓞 F) r) (c : 𝓞 F) (hc : c ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) (a : SymIdx r → 𝓞 F ⧸ Ideal.span {c}) :
    wgR v (aV (unitsOfInt b hb) v) ((T₀.map (algebraMap (𝓞 F) F)).map (algebraMap F (v.adicCompletion F)))
        (locU v (uOf c a)) =
      gLocR b hb (T₀.map (algebraMap (𝓞 F) F)) c v (fun p => redV c hc v (a p)) := by
  unfold gLocR
  have e : locU v (uOf c a) = (fun p => resRho c v (redV c hc v (a p))) +
      fun p => algebraMap F (v.adicCompletion F)
        ((ιO (Quotient.out (a p)) - ιO (Quotient.out (redV c hc v (a p)))) / ιO c) := by
    funext p
    simp only [locU, uOf, resRho, Pi.add_apply, ← map_add]
    congr 1
    ring
  rw [e, wgR_add_int v _ (aV_unitsOfInt_le_one b hb v) _ (valued_coeff_map_int v T₀) _ _
    (fun p => valued_out_sub_out_div_le c hc v (a p))]

/-- The factor at $v$ when $v \nmid c$: every residue gives $f_v(w)$ (the value at $B = 0$). -/
lemma gLocR_of_eC_eq_zero (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (T₀ : QuadForm (𝓞 F) r) (c : 𝓞 F) (hc : c ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) (he : eC c v = 0) (x : SymIdx r → 𝓞 F ⧸ v.asIdeal ^ eC c v) :
    gLocR b hb (T₀.map (algebraMap (𝓞 F) F)) c v x =
      wfunR v (aV (unitsOfInt b hb) v) (locU v (0 : SymIdx r → F)) := by
  unfold gLocR
  have h0 : (fun p => resRho c v (x p)) = 0 + fun p => resRho c v (x p) := by rw [zero_add]
  rw [h0, wgR_add_int v _ (aV_unitsOfInt_le_one b hb v) _ (valued_coeff_map_int v T₀) 0
    (fun p => resRho c v (x p)) (fun p => resRho_int_of_not_dvd v hc he _)]
  have hl : locU v (0 : SymIdx r → F) = 0 := by funext p; simp [locU]
  rw [hl, wgR]
  have hp : pairT v ((T₀.map (algebraMap (𝓞 F) F)).map (algebraMap F (v.adicCompletion F))) 0 = 0 := by
    simp [pairT]
  rw [hp, neg_zero, AddChar.map_zero_eq_one]
  simp

/-- **The Chinese remainder theorem for the truncated singular series**: for $c \ne 0$,
$$\sum_{a\in(\mathcal O_F/c)^{\{i\le i'\}}}f_f(w\,n(u_a), s_0)\,e_T(\sigma(u_a)) = \prod_v\sum_{x\in(\mathcal O_F/\mathfrak p_v^{e_v})^{\{i\le i'\}}}
  f_v(w\,n(\tilde x/c))\,\psi_v(-\langle T, \tilde x/c\rangle).$$ -/
@[kb "siegel1935" "§ 3 (the singular series is multiplicative: Chinese remainder theorem) [unverified]"]
theorem truncSS_eq_finprod (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (T₀ : QuadForm (𝓞 F) r) (c : 𝓞 F)
    (hc : c ≠ 0) [Fintype (𝓞 F ⧸ Ideal.span {c})] :
    ∑ a : SymIdx r → 𝓞 F ⧸ Ideal.span {c}, fFinR b hb (uOf c a) *
        eT (T₀.map (algebraMap (𝓞 F) F)) (realMat (symOf (uOf c a))) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ∑ x : SymIdx r → 𝓞 F ⧸ v.asIdeal ^ eC c v,
        gLocR b hb (T₀.map (algebraMap (𝓞 F) F)) c v x := by
  classical
  set T := T₀.map (algebraMap (𝓞 F) F)
  set G : ∀ v : HeightOneSpectrum (𝓞 F), (SymIdx r → 𝓞 F ⧸ v.asIdeal ^ eC c v) → ℂ := gLocR b hb T c
  have hI : Ideal.span {c} ≠ ⊥ := by simpa using hc
  have hκ := hasFiniteMulSupport_wfunR b hb (0 : SymIdx r → F)
  have hκ' : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      wfunR v (aV (unitsOfInt b hb) v) (locU v 0)).Finite := hκ
  set S : Finset (HeightOneSpectrum (𝓞 F)) := SingularNF.suppI hI ∪ hκ'.toFinset
  have hsupp : SingularNF.suppI hI ⊆ S := Finset.subset_union_left
  have he0 : ∀ v ∉ S, eC c v = 0 := fun v hv => by
    by_contra h
    exact hv (hsupp ((SingularNF.mem_suppI hI v).mpr ((SingularNF.ordI_ne_zero_iff hI v).mp h)))
  have hG1 : ∀ v ∉ S, ∀ x, G v x = 1 := fun v hv x => by
    show gLocR b hb (T₀.map (algebraMap (𝓞 F) F)) c v x = 1
    rw [gLocR_of_eC_eq_zero b hb T₀ c hc v (he0 v hv) x]
    by_contra h
    exact hv (Finset.mem_union_right _ (hκ'.mem_toFinset.mpr h))
  -- the terms
  have hterm : ∀ a, fFinR b hb (uOf c a) * eT T (realMat (symOf (uOf c a))) =
      ∏ v : S, G v (fun p => redV c hc v (a p)) := by
    intro a
    rw [Finset.prod_coe_sort S fun v => G v (fun p => redV c hc v (a p))]
    rw [fFinR_mul_eT_eq_finprod]
    have e : ∀ v, wfunR v (aV (unitsOfInt b hb) v) (locU v (uOf c a)) *
        (psiV v (-pairT v (T.map (algebraMap F (v.adicCompletion F))) (locU v (uOf c a))) : ℂ) =
        G v (fun p => redV c hc v (a p)) := fun v => wgR_locU_uOf b hb T₀ c hc v a
    simp_rw [e]
    exact finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      by_contra h; exact hv (hG1 v h _)
  have hrhs : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ∑ x, G v x) = ∏ v ∈ S, ∑ x, G v x := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra h
    apply hv
    have : Subsingleton (𝓞 F ⧸ v.asIdeal ^ eC c v) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [he0 v h, pow_zero, Ideal.one_eq_top])
    show ∑ x, G v x = 1
    rw [Finset.sum_eq_single (0 : SymIdx r → 𝓞 F ⧸ v.asIdeal ^ eC c v)
      (fun y _ hy => absurd (Subsingleton.elim y 0) hy) (fun h0 => absurd (Finset.mem_univ _) h0), hG1 v h]
  simp_rw [hterm]
  rw [hrhs, ← Finset.prod_coe_sort S]
  -- the Chinese remainder theorem
  have hprod : ∏ v : S, (v : HeightOneSpectrum (𝓞 F)).asIdeal ^ eC c v = Ideal.span {c} := by
    rw [Finset.prod_coe_sort S fun v => v.asIdeal ^ eC c v]
    exact SingularNF.prod_suppI hI hsupp
  let E := HeightOneSpectrum.quotientEquivPiOfProdEq (Ideal.span {c}) (fun v : S => (v : HeightOneSpectrum (𝓞 F)))
    (fun v => eC c v) (fun a b h => Subtype.coe_injective.ne h) hprod
  have hE : ∀ (x : 𝓞 F ⧸ Ideal.span {c}) (v : S), E x v = redV c hc v x := by
    intro x v
    induction x using Quotient.inductionOn with
    | h o => rfl
  let Ψ : (SymIdx r → 𝓞 F ⧸ Ideal.span {c}) ≃
      (∀ v : S, SymIdx r → 𝓞 F ⧸ (v : HeightOneSpectrum (𝓞 F)).asIdeal ^ eC c v) :=
    (Equiv.piCongrRight fun _ => E.toEquiv).trans (Equiv.piComm _)
  have hΨ : ∀ a (v : S), Ψ a v = fun p => redV c hc v (a p) := by
    intro a v; funext p; exact hE (a p) v
  have e2 : ∀ a, ∏ v : S, G v (fun p => redV c hc v (a p)) = ∏ v : S, G v (Ψ a v) := fun a => by
    simp_rw [hΨ]
  simp_rw [e2]
  rw [Ψ.sum_comp (fun f => ∏ v : S, G v (f v)), Finset.prod_univ_sum]
  rfl

end QuadFormsKB.SiegelWeil.Forms
