/-
# The Fourier coefficients of a weight-2 Eisenstein series of a periodic weight, row by row

**Setting.** $F$ totally real of degree $d$, $\mathcal O = \mathcal O_F$, $\mathfrak d^{-1}$ the inverse different, $e(x) = e^{2\pi ix}$,
$\operatorname{Tr} = \operatorname{Tr}_{F/\mathbb Q}$, $N$ the absolute norm. $W$ is an integral weight of parallel weight $2$ and level
$\mathfrak M$ (`IntWeight`: unit equivariant, bounded, supported on $\mathcal O^2$, periodic
modulo $\mathfrak M^2$), and in addition
**translation invariant**: $W(c, d + cb) = W(c, d)$ for $b \in \mathcal O$ (the weight is invariant under $\begin{pmatrix}1&b\\0&1\end{pmatrix}$;
true for every weight with a $\Gamma_0(\mathfrak N)$-law). $E_{W,2}$ = `eis2 W 𝔐` is the weight-2 Eisenstein series (Hecke's limit; for
$d \ge 2$ holomorphic with no correction term).

**Results.**
* `latConst_koecherBasis`, `latConst_levelBasis`: the Lipschitz constant (inverse covolume) of $\sigma(I)$ is $\operatorname{embDet}(I)^{-1}$,
  and for an integral ideal $c_{\mathfrak M} = c_{\mathcal O}/N(\mathfrak M)$.
* `exists_oDual_of_oscA_ne_zero`: every frequency $\mu = c\nu$ of the row expansion with a nonzero coefficient lies in $\mathfrak d^{-1}$
  (translation invariance makes the row sum $R_W(c, \nu)$ vanish unless $e(\operatorname{Tr}c\nu b) = 1$ for all $b \in \mathcal O$).
* **`qCoeff_eis2`**: for $\mu = \mu_m \in \mathfrak d^{-1}\setminus 0$,
  $$a_\mu(E_{W,2}) = \sum_{t\in U\backslash F}\rho_W(t, \mu),$$
  $\rho_W(t, \mu)$ = `rowCo` the coefficient of $e(\operatorname{Tr}\mu z)$ in the row $t$ (absolutely convergent).
* **`rowCo_eq`** (the row coefficient as an average): for $c = \tilde t \ne 0$ and any nonzero $M \subseteq \mathfrak M$ with
  $e(\operatorname{Tr}\mu m/c) = 1$ for $m \in M$,
  $$\rho_W(t, \mu) = c_{\mathcal O}\,\Lambda_2(\mu)\,|N(c)|^{-1}\cdot\frac1{N(M)}\sum_{r\in\mathcal O/M}W(c, \tilde r)\,e\Big(\operatorname{Tr}\frac{\mu\tilde r}c\Big),$$
  $\Lambda_2(\mu) = ((-2\pi i)^2)^d\,N(\mu)\,[\mu \gg 0]$ (`lipCoeff 2`), $c_{\mathcal O} = |d_F|^{-1/2}$. The average does not depend on $M$.

Sources: Hecke (1927) [unverified]; Shimura, Duke Math. J. 45 (1978), §3, (3.4)–(3.11) [unverified]; over $\mathbb Q$ the row
coefficients are `Siegel.EisensteinWt2` (`hasSum_eis2`).
-/
import QuadFormsKB.HilbertModular.SiegelFormulaNF

open Complex Matrix NumberField UpperHalfPlane Filter Topology MeasureTheory
open scoped MatrixGroups ModularForm nonZeroDivisors Real

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "ιO" => algebraMap (𝓞 F) F
local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

open SiegelWeil.SingularNF (eTr eTr_add eTr_of_mem eTr_eq_one_iff)

/-! ### The Lipschitz constant of $\sigma(I)$ -/

lemma embDet_pos (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : 0 < embDet I := by
  have h := embDet_sq_eq (F := F) I
  have hI : (FractionalIdeal.absNorm (I : FI) : ℚ) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact I.ne_zero
  have h0 : embDet I ≠ 0 := by
    intro h0; rw [h0] at h
    have hd : (discr F : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero F
    have : ((FractionalIdeal.absNorm (I : FI) : ℚ) : ℝ) ^ 2 * (discr F : ℝ) = 0 := by
      rw [← h]; ring
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hI (by exact_mod_cast pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1)
    · exact hd h1
  exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)

/-- **The Lipschitz constant of $\sigma(I)$ is the inverse covolume**: $c_I = \operatorname{embDet}(I)^{-1}$ (`latConst_oBasis` for any
$I$). -/
theorem latConst_koecherBasis (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    (latConst (koecherBasis I) : ℝ) = (embDet I)⁻¹ := by
  classical
  set kb := koecherBasis I
  set L : (Fin (Module.finrank ℚ F) → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ) := kb.equivFun.symm.toLinearMap
  set e := LinearEquiv.funCongrLeft ℝ ℝ (placeEquiv (F := F))
  set M : (Fin (Module.finrank ℚ F) → ℝ) →ₗ[ℝ] (Fin (Module.finrank ℚ F) → ℝ) := e.toLinearMap ∘ₗ L
  have hmat : LinearMap.toMatrix' M = embMat (QuadFormsKB.Analysis.bq I) := by
    ext j l
    rw [LinearMap.toMatrix'_apply, embMat, Matrix.of_apply]
    simp only [M, L, e, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.funCongrLeft_apply]
    rw [Module.Basis.equivFun_symm_apply]
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rw [koecherBasis_apply]
    rfl
  have hdet : LinearMap.det M = (embMat (QuadFormsKB.Analysis.bq I)).det := by
    rw [← LinearMap.det_toMatrix', hmat]
  have hpos := embDet_pos I
  have hdet0 : LinearMap.det M ≠ 0 := by
    rw [hdet]; intro h; rw [embDet, h, abs_zero] at hpos; exact lt_irrefl _ hpos
  have he : MeasurePreserving (fun x : InfinitePlace F → ℝ => fun j => x (placeEquiv j)) volume volume := by
    have := (volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace F => ℝ) (placeEquiv (F := F))).symm
    exact this
  have h1 : Measure.map M (volume : Measure (Fin (Module.finrank ℚ F) → ℝ)) =
      (latConst kb : ENNReal) • (volume : Measure (Fin (Module.finrank ℚ F) → ℝ)) := by
    have hL : Measure.map L (volume : Measure (Fin (Module.finrank ℚ F) → ℝ)) = latConst kb • volume :=
      map_basis_volume kb
    have hM : (M : (Fin (Module.finrank ℚ F) → ℝ) → (Fin (Module.finrank ℚ F) → ℝ)) =
        (fun x : InfinitePlace F → ℝ => fun j => x (placeEquiv j)) ∘ L := by
      funext x; rfl
    rw [hM, ← Measure.map_map he.measurable L.continuous_of_finiteDimensional.measurable, hL,
      Measure.map_smul, he.map_eq]
    · rfl
    · exact he.measurable.aemeasurable
  have h2 := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (Fin (Module.finrank ℚ F) → ℝ)) hdet0
  rw [h1] at h2
  have hcube : (volume : Measure (Fin (Module.finrank ℚ F) → ℝ)) (Set.Icc 0 1) = 1 := by
    rw [Real.volume_Icc_pi]; simp
  have h3 := congrArg (fun μ : Measure (Fin (Module.finrank ℚ F) → ℝ) => μ (Set.Icc 0 1)) h2
  simp only [Measure.smul_apply, hcube, smul_eq_mul, mul_one] at h3
  have h4 : ((latConst kb : NNReal) : ℝ) = |(LinearMap.det M)⁻¹| := by
    have := congrArg ENNReal.toReal h3
    rwa [ENNReal.coe_toReal, ENNReal.toReal_ofReal (abs_nonneg _)] at this
  rw [h4, hdet, abs_inv, embDet]

/-- $\operatorname{embDet}(\mathfrak M) = N(\mathfrak M)\sqrt{d_F}$ for an integral ideal $\mathfrak M \ne 0$. -/
lemma embDet_levelUnit (𝔐 : Ideal (𝓞 F)) (h𝔐 : 𝔐 ≠ ⊥) :
    embDet (levelUnit 𝔐 h𝔐) = (Ideal.absNorm 𝔐 : ℝ) * Real.sqrt (discr F : ℝ) := by
  have h := embDet_sq_eq (F := F) (levelUnit 𝔐 h𝔐)
  have hval : ((levelUnit 𝔐 h𝔐 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FI) = (𝔐 : FI) := rfl
  rw [hval, FractionalIdeal.coeIdeal_absNorm] at h
  have hd : (0 : ℝ) ≤ (discr F : ℝ) := (discr_pos (F := F)).le
  have h' : embDet (levelUnit 𝔐 h𝔐) ^ 2 = ((Ideal.absNorm 𝔐 : ℝ) * Real.sqrt (discr F : ℝ)) ^ 2 := by
    rw [h, mul_pow, Real.sq_sqrt hd]; push_cast; ring
  exact (pow_left_inj₀ (embDet_pos _).le (by positivity) two_ne_zero).mp h'

/-- **$c_{\mathfrak M} = c_{\mathcal O}/N(\mathfrak M)$** for the level lattice $\sigma(\mathfrak M)$. -/
@[kb "shimura1978" "§3: covolume of σ(𝔐) is N(𝔐)·|d_F|^{1/2} [unverified]"]
theorem latConst_levelBasis (𝔐 : Ideal (𝓞 F)) (h𝔐 : 𝔐 ≠ ⊥) :
    (latConst (levelBasis 𝔐 h𝔐) : ℝ) = (latConst (oBasis F) : ℝ) / (Ideal.absNorm 𝔐 : ℝ) := by
  rw [levelBasis, latConst_koecherBasis, embDet_levelUnit, latConst_oBasis_eq, mul_inv, div_eq_mul_inv,
    mul_comm]


/-! ### Character sums over $\mathcal O/J$ -/

/-- **A shifted finite sum vanishes**: if $g(r + s + m) = e\,g(r)$ for all $r$ and $m \in J$, with $e \ne 1$, then
$\sum_{r\in\mathcal O/J}g(\tilde r) = 0$. -/
lemma finsum_quot_eq_zero_of_shift {J : Ideal (𝓞 F)} (hJ : J ≠ ⊥) (g : 𝓞 F → ℂ) {s : 𝓞 F} {e : ℂ} (he : e ≠ 1)
    (hg : ∀ r m, m ∈ J → g (r + s + m) = e * g r) :
    ∑ᶠ r : 𝓞 F ⧸ J, g (Quotient.out r) = 0 := by
  classical
  haveI := SiegelWeil.SingularNF.finite_quot hJ
  letI : Fintype (𝓞 F ⧸ J) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  set S := ∑ r : 𝓞 F ⧸ J, g (Quotient.out r)
  have hS : S = e * S := by
    calc S = ∑ r : 𝓞 F ⧸ J, g (Quotient.out (r + Ideal.Quotient.mk J s)) :=
          (Fintype.sum_equiv (Equiv.addRight (Ideal.Quotient.mk J s)) _ _ (fun _ => rfl)).symm
      _ = ∑ r : 𝓞 F ⧸ J, e * g (Quotient.out r) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          have hm : Quotient.out (r + Ideal.Quotient.mk J s) - (Quotient.out r + s) ∈ J := by
            rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out, map_add, Ideal.Quotient.mk_out]
          have := hg (Quotient.out r) _ hm
          rwa [add_sub_cancel] at this
      _ = e * S := by rw [Finset.mul_sum]
  have h1 : (1 - e) * S = 0 := by linear_combination hS
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr (Ne.symm he))

/-- **Averages over $\mathcal O/J$ do not depend on $J$**: for $J \le I$ nonzero and $g$ periodic modulo $I$,
$N(J)^{-1}\sum_{r\in\mathcal O/J}g(\tilde r) = N(I)^{-1}\sum_{r\in\mathcal O/I}g(\tilde r)$. -/
lemma avg_quot_eq {J I : Ideal (𝓞 F)} (hJ : J ≠ ⊥) (hJI : J ≤ I) (g : 𝓞 F → ℂ)
    (hg : ∀ r m, m ∈ I → g (r + m) = g r) :
    ((Ideal.absNorm J : ℂ))⁻¹ * ∑ᶠ r : 𝓞 F ⧸ J, g (Quotient.out r) =
      ((Ideal.absNorm I : ℂ))⁻¹ * ∑ᶠ r : 𝓞 F ⧸ I, g (Quotient.out r) := by
  classical
  have hI : I ≠ ⊥ := fun h => hJ (le_bot_iff.mp (h ▸ hJI))
  haveI := SiegelWeil.SingularNF.finite_quot hJ
  haveI := SiegelWeil.SingularNF.finite_quot hI
  letI : Fintype (𝓞 F ⧸ J) := Fintype.ofFinite _
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  set f : (𝓞 F ⧸ J) →+ (𝓞 F ⧸ I) := (Ideal.Quotient.factor hJI).toAddMonoidHom
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hJI
  have h := SiegelWeil.SingularNF.sum_comp_mul f hf (fun h => g (Quotient.out h))
  have hcomp : ∀ r : 𝓞 F ⧸ J, g (Quotient.out (f r)) = g (Quotient.out r) := by
    intro r
    have hm : Quotient.out (f r) - Quotient.out r ∈ I := by
      rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
      conv_lhs => rw [← Ideal.Quotient.mk_out r]
      rfl
    have := hg (Quotient.out r) _ hm
    rwa [add_sub_cancel] at this
  simp only [hcomp] at h
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have hNJ : (Fintype.card (𝓞 F ⧸ J) : ℂ) = Ideal.absNorm J := by
    rw [← SiegelWeil.SingularNF.card_quot_eq_absNorm, Nat.card_eq_fintype_card]
  have hNI : (Fintype.card (𝓞 F ⧸ I) : ℂ) = Ideal.absNorm I := by
    rw [← SiegelWeil.SingularNF.card_quot_eq_absNorm, Nat.card_eq_fintype_card]
  rw [hNJ, hNI] at h
  have hJ0 : (Ideal.absNorm J : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact hJ
  have hI0 : (Ideal.absNorm I : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact hI
  field_simp
  linear_combination h

/-! ### The frequencies of the row expansion lie in $\mathfrak d^{-1}$ -/

lemma cexp_pair_realVec (a x : F) :
    cexp (2 * π * Complex.I * (pair (realVec a) (realVec x) : ℂ)) = eTr (a * x) := by
  rw [pair_realVec, eTr]; push_cast; rfl

/-- $e(\operatorname{Tr}\nu y) = 1$ for $\nu$ in the trace dual of $I$ and $y \in I$. -/
lemma eTr_dualElt_mul_of_mem {I : (FractionalIdeal (𝓞 F)⁰ F)ˣ} (n : Fin (Module.finrank ℚ F) → ℤ) {y : F}
    (hy : y ∈ (I : FI)) : eTr (QuadFormsKB.Analysis.dualElt I n * y) = 1 := by
  have hmem := (QuadFormsKB.Analysis.dualEquiv I n).2
  rw [QuadFormsKB.Analysis.dualEquiv_coe] at hmem
  obtain ⟨k, hk⟩ := (FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) I.ne_zero).mp hmem y hy
  rw [eTr_eq_one_iff]
  refine ⟨k, ?_⟩
  rw [← Algebra.traceForm_apply, ← hk]
  simp

/-- A vector in the trace dual of $I$ is some $\nu_n$ = `dualElt I n`. -/
lemma exists_dualElt_of_eTr {I : (FractionalIdeal (𝓞 F)⁰ F)ˣ} {x : F}
    (h : ∀ y ∈ (I : FI), eTr (x * y) = 1) : ∃ n, QuadFormsKB.Analysis.dualElt I n = x := by
  have hmem : x ∈ ((FractionalIdeal.dual ℤ ℚ (I : FI) : FI) : Set F) := by
    rw [SetLike.mem_coe, FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) I.ne_zero]
    intro a ha
    obtain ⟨k, hk⟩ := (eTr_eq_one_iff _).mp (h a ha)
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, hk]
    simp
  refine ⟨(QuadFormsKB.Analysis.dualEquiv I).symm ⟨x, hmem⟩, ?_⟩
  rw [← QuadFormsKB.Analysis.dualEquiv_coe, Equiv.apply_symm_apply]

lemma mem_levelUnit {𝔐 : Ideal (𝓞 F)} (h𝔐 : 𝔐 ≠ ⊥) {m : 𝓞 F} (hm : m ∈ 𝔐) :
    ιO m ∈ ((levelUnit 𝔐 h𝔐 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FI) :=
  (FractionalIdeal.mem_coeIdeal _).mpr ⟨m, hm, rfl⟩

/-- **Translation invariance kills the off-dual frequencies**: if $W(c, d + cb) = W(c, d)$ ($b \in \mathcal O$) and
$e(\operatorname{Tr}\nu\,c\,b) \ne 1$ for some $b$, then the row sum $R_W(c, \nu) = 0$ ($\nu$ in the trace dual of $\mathfrak M$). -/
lemma rowR_eq_zero_of_eTr_ne {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W 2 𝔐)
    (hT : ∀ (c d : F) (b : 𝓞 F), W (c, d + c * ιO b) = W (c, d)) {c : 𝓞 F} {ν : F}
    (hν : ∀ m ∈ 𝔐, eTr (ν * ιO m) = 1) {b : 𝓞 F} (hb : eTr (ν * (ιO c * ιO b)) ≠ 1) :
    rowR W 𝔐 (ιO c) (realVec ν) = 0 := by
  rw [rowR]
  simp_rw [cexp_pair_realVec]
  refine finsum_quot_eq_zero_of_shift hW.ne (fun r => W (ιO c, ιO r) * eTr (ν * ιO r)) (s := c * b) hb
    fun r m hm => ?_
  simp only [map_add, map_mul]
  have h1 : W (ιO c, ιO r + ιO c * ιO b + ιO m) = W (ιO c, ιO r) := by
    have := hW.per (ιO c, ιO r + ιO c * ιO b) 0 m (Submodule.zero_mem _) hm
    simp only [map_zero, add_zero] at this
    rw [this, hT]
  rw [h1, mul_add, mul_add, eTr_add, eTr_add, hν m hm]
  ring

/-- **The frequencies of $E_{W,2}$ lie in $\mathfrak d^{-1}$**: if the coefficient $a_{t,n}$ (`oscA`) is nonzero then the exponent
$\mu_{t,n} = \tilde t\nu_n$ (`oscMu`) is $\sigma(\mu)$ for some $\mu = \mu_m \in \mathfrak d^{-1}$. -/
theorem exists_oDual_of_oscA_ne_zero {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W 2 𝔐)
    (hT : ∀ (c d : F) (b : 𝓞 F), W (c, d + c * ιO b) = W (c, d))
    {p : UOrbitF F × (Fin (Module.finrank ℚ F) → ℤ)} (hp : oscA W 𝔐 hW.ne p ≠ 0) :
    ∃ m, oscMu 𝔐 hW.ne p = dualVec (oBasis F) m := by
  classical
  have hR : rowR W 𝔐 (crep p.1) (dualVec (levelBasis 𝔐 hW.ne) p.2) ≠ 0 := by
    intro h; apply hp; unfold oscA; split_ifs <;> simp [h]
  -- the row is integral
  obtain ⟨c, hc⟩ : ∃ c : 𝓞 F, ιO c = crep p.1 := by
    by_contra hne
    apply hR
    rw [rowR]
    refine finsum_eq_zero_of_forall_eq_zero fun r => ?_
    have : W (crep p.1, ιO (Quotient.out r)) = 0 := by
      by_contra hW0
      obtain ⟨q, hq⟩ := hW.supp _ hW0
      exact hne ⟨q.1, congrArg Prod.fst hq⟩
    rw [this, zero_mul]
  set ν := QuadFormsKB.Analysis.dualElt (levelUnit 𝔐 hW.ne) p.2
  have hνv : dualVec (levelBasis 𝔐 hW.ne) p.2 = realVec ν := dualVec_koecherBasis _ _
  have hν : ∀ m ∈ 𝔐, eTr (ν * ιO m) = 1 := fun m hm => eTr_dualElt_mul_of_mem _ (mem_levelUnit hW.ne hm)
  have hall : ∀ b : 𝓞 F, eTr (ιO b * (ν * ιO c)) = 1 := by
    intro b
    by_contra hb
    apply hR
    rw [hνv, ← hc]
    exact rowR_eq_zero_of_eTr_ne hW hT hν (b := b) (by rw [show ν * (ιO c * ιO b) = ιO b * (ν * ιO c) by ring]; exact hb)
  obtain ⟨m, hm⟩ := exists_oDual_eq ((SiegelWeil.SingularNF.mem_invDifferent_iff_eTr _).mpr hall)
  refine ⟨m, ?_⟩
  rw [dualVec_oBasis, hm]
  funext v
  simp only [oscMu, hνv, realVec, map_mul, hc]


/-! ### The Fourier coefficients of $E_{W,2}$ as a sum over rows -/

/-- **The row coefficient** $\rho_W(t, \mu)$: the coefficient of $e(\operatorname{Tr}\mu z)$ in the row $t \in U\backslash F$ of
$E_{W,2}$, i.e. $\sum_n[\mu_{t,n} = \sigma(\mu)]\,a_{t,n}$ (at most one nonzero term). Parameters: `W` (weight), `𝔐` (level), `t` (row),
`μ` (frequency). -/
@[kb "shimura1978" "§3: the coefficient of e(Tr μz) in one row of E₂ [unverified]"]
noncomputable def rowCo (W : F × F → ℂ) (𝔐 : Ideal (𝓞 F)) (h𝔐 : 𝔐 ≠ ⊥) (t : UOrbitF F) (μ : F) : ℂ :=
  ∑' n, if oscMu 𝔐 h𝔐 (t, n) = realVec μ then oscA W 𝔐 h𝔐 (t, n) else 0

lemma qTerm_dualVec_zero (z : InfinitePlace F → ℍ) : qTerm (dualVec (oBasis F) 0) z = 1 := by
  have : dualVec (oBasis F) 0 = 0 := by
    rw [dualVec]; convert map_zero (pairEquiv (oBasis F)).symm; simp
  rw [this, qTerm]; simp

/-- **The Fourier coefficients of $E_{W,2}$, row by row**: for a translation-invariant integral weight $W$ of weight $2$ with
$E_{W,2}$ periodic for $\sigma(\mathcal O)$, and $\mu = \mu_m \in \mathfrak d^{-1}$, $m \ne 0$,
$$a_\mu(E_{W,2}) = \sum_{t\in U\backslash F}\rho_W(t, \mu)\qquad(\text{absolutely convergent}).$$
Proof: regroup the absolutely convergent expansion
$E_{W,2} = \mathrm c_\infty(W) + \sum_{t,n}a_{t,n}e(\langle\mu_{t,n}, z\rangle)$
(`eis2_eq_qSeries`) by frequency (all frequencies lie in $\mathfrak d^{-1}$, `exists_oDual_of_oscA_ne_zero`), and use uniqueness of
$q$-expansions (`qCoeff_unique`). -/
@[kb "shimura1978" "§3: Fourier coefficients of E₂ as a sum of row coefficients [unverified]"]
theorem qCoeff_eis2 {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W 2 𝔐)
    (hT : ∀ (c d : F) (b : 𝓞 F), W (c, d + c * ιO b) = W (c, d))
    (hper : IsLatticePeriodic (eis2 W 𝔐 hW.ne) (oBasis F)) {m : Fin (Module.finrank ℚ F) → ℤ} (hm : m ≠ 0) :
    (Summable fun t => rowCo W 𝔐 hW.ne t (oDual m)) ∧
      qCoeff (eis2 W 𝔐 hW.ne) (oBasis F) (realVec (oDual m)) = ∑' t, rowCo W 𝔐 hW.ne t (oDual m) := by
  classical
  set A := oscA W 𝔐 hW.ne
  set Mu := oscMu 𝔐 hW.ne
  set b := oBasis F
  have hκex : ∀ p, A p ≠ 0 → ∃ m, Mu p = dualVec b m := fun p hp => exists_oDual_of_oscA_ne_zero hW hT hp
  set κ : UOrbitF F × (Fin (Module.finrank ℚ F) → ℤ) → (Fin (Module.finrank ℚ F) → ℤ) :=
    fun p => if h : ∃ m, Mu p = dualVec b m then h.choose else 0
  have hκ : ∀ p, A p ≠ 0 → Mu p = dualVec b (κ p) := by
    intro p hp; have h := hκex p hp; simp only [κ, dif_pos h]; exact h.choose_spec
  -- the fibre of `κ` over `m`, for a family vanishing with `A`
  have hfib : ∀ (w : UOrbitF F × (Fin (Module.finrank ℚ F) → ℤ) → ℂ), (∀ p, A p = 0 → w p = 0) →
      ∀ m', ∑' p : κ ⁻¹' {m'}, w p = ∑' p, if Mu p = dualVec b m' then w p else 0 := by
    intro w hw m'
    rw [tsum_subtype]
    refine tsum_congr fun p => ?_
    by_cases hA : A p = 0
    · simp [hw p hA]
    · have hiff : κ p = m' ↔ Mu p = dualVec b m' := by
        rw [hκ p hA]; exact ⟨fun h => by rw [h], fun h => dualVec_injective b h⟩
      by_cases h : Mu p = dualVec b m'
      · rw [if_pos h, Set.indicator_of_mem (by exact hiff.mpr h)]
      · rw [if_neg h, Set.indicator_of_notMem (by exact fun h' => h (hiff.mp h'))]
  set G : (Fin (Module.finrank ℚ F) → ℤ) → ℂ := fun m' => ∑' p, if Mu p = dualVec b m' then A p else 0
  set α : (Fin (Module.finrank ℚ F) → ℤ) → ℂ := fun m' => (if m' = 0 then eisConst W 2 else 0) + G m'
  have hy1 : ∀ v : InfinitePlace F, (0 : ℝ) < (1 : InfinitePlace F → ℝ) v := fun _ => one_pos
  obtain ⟨g, hgs, hgb⟩ := dom_oscA hW (y₀ := 1) one_pos
  have him : ∀ x : InfinitePlace F → ℝ, ∀ v, (1 : ℝ) ≤ (ptXY x 1 v).im := by
    intro x v
    have := congrFun (imVec_ptXY (x := x) hy1) v
    simp only [imVec] at this; rw [this]; rfl
  -- the fibre sums at a point
  have hfibz : ∀ (z : InfinitePlace F → ℍ) m', ∑' p : κ ⁻¹' {m'}, A p * qTerm (Mu p) z =
      G m' * qTerm (dualVec b m') z := by
    intro z m'
    rw [hfib (fun p => A p * qTerm (Mu p) z) (fun p hp => by simp [hp]),
      show G m' * qTerm (dualVec b m') z =
        ∑' p, (if Mu p = dualVec b m' then A p else 0) * qTerm (dualVec b m') z from tsum_mul_right.symm]
    refine tsum_congr fun p => ?_
    split_ifs with h
    · rw [h]
    · rw [zero_mul]
  -- the expansion
  have hexp : ∀ x, HasSum (fun m' => α m' * qTerm (dualVec b m') (ptXY x 1)) (eis2 W 𝔐 hW.ne (ptXY x 1)) := by
    intro x
    set z := ptXY x 1
    have hsg : Summable fun p => A p * qTerm (Mu p) z :=
      Summable.of_norm_bounded hgs fun p => hgb z (him x) p
    have h1 := hsg.hasSum.tsum_fiberwise κ
    simp_rw [hfibz z] at h1
    have h0 : HasSum (fun m' : Fin (Module.finrank ℚ F) → ℤ =>
        (if m' = 0 then eisConst W 2 else 0) * qTerm (dualVec b m') z) (eisConst W 2) := by
      convert hasSum_ite_eq (0 : Fin (Module.finrank ℚ F) → ℤ) (eisConst W 2) using 1
      funext m'
      split_ifs with hm'
      · rw [hm', qTerm_dualVec_zero, mul_one]
      · rw [zero_mul]
    rw [eis2_eq_qSeries hW z]
    convert h0.add h1 using 1
    funext m'
    simp only [α, add_mul]
  -- summability
  have hsum : Summable fun m' => ‖α m'‖ * Real.exp (-2 * π * pair (dualVec b m') 1) := by
    set z := ptXY (0 : InfinitePlace F → ℝ) 1
    have hn : Summable fun p => ‖A p * qTerm (Mu p) z‖ :=
      hgs.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => hgb z (him 0) p
    have h1 := hn.hasSum.tsum_fiberwise κ
    have hE : ∀ m', Real.exp (-2 * π * pair (dualVec b m') 1) = ‖qTerm (dualVec b m') z‖ := by
      intro m'; rw [norm_qTerm, imVec_ptXY hy1]
    have hG : ∀ m', ‖G m'‖ * Real.exp (-2 * π * pair (dualVec b m') 1) ≤
        ∑' p : κ ⁻¹' {m'}, ‖A p * qTerm (Mu p) z‖ := by
      intro m'
      rw [hE, ← norm_mul, ← hfibz z m']
      exact norm_tsum_le_tsum_norm (hn.subtype _)
    have hc : Summable fun m' : Fin (Module.finrank ℚ F) → ℤ =>
        ‖(if m' = 0 then eisConst W 2 else 0)‖ * Real.exp (-2 * π * pair (dualVec b m') 1) := by
      refine summable_of_ne_finset_zero (s := {0}) fun m' hm' => ?_
      rw [Finset.mem_singleton] at hm'
      simp [hm']
    refine (hc.add h1.summable).of_nonneg_of_le (fun _ => by positivity) fun m' => ?_
    calc ‖α m'‖ * Real.exp (-2 * π * pair (dualVec b m') 1)
        ≤ (‖(if m' = 0 then eisConst W 2 else 0)‖ + ‖G m'‖) * Real.exp (-2 * π * pair (dualVec b m') 1) :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) (Real.exp_pos _).le
      _ ≤ _ := by rw [add_mul]; exact add_le_add le_rfl (hG m')
  have hq := qCoeff_unique (isHolomorphic_eis2 hW) hper hy1 hsum hexp m
  have hαm : α m = G m := by simp [α, hm]
  -- the double sum over rows
  have hsp : Summable fun p => if Mu p = dualVec b m then A p else 0 := by
    set z := ptXY (0 : InfinitePlace F → ℝ) 1
    have hn : Summable fun p => ‖A p * qTerm (Mu p) z‖ :=
      hgs.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => hgb z (him 0) p
    refine Summable.of_norm_bounded (hn.mul_left (Real.exp (2 * π * pair (dualVec b m) 1))) fun p => ?_
    split_ifs with h
    · rw [norm_mul, norm_qTerm, imVec_ptXY hy1, h, ← mul_assoc, mul_comm (Real.exp _), mul_assoc,
        ← Real.exp_add]
      simp
    · simp only [norm_zero]; positivity
  have hrow : ∀ t, rowCo W 𝔐 hW.ne t (oDual m) = ∑' n, (fun p => if Mu p = dualVec b m then A p else 0) (t, n) := by
    intro t
    rw [rowCo, show dualVec b m = realVec (oDual m) from dualVec_oBasis m]
  refine ⟨?_, ?_⟩
  · simp_rw [hrow]; exact hsp.prod
  · rw [← dualVec_oBasis, ← hq, hαm]
    simp_rw [hrow]
    exact hsp.tsum_prod


/-! ### The row coefficient as an average over $\mathcal O/M$ -/

/-- **The row average** $N(M)^{-1}\sum_{r\in\mathcal O/M}V(c, \tilde r)\,e(\operatorname{Tr}\mu\tilde r/c)$ (representatives `Quotient.out`).
Parameters: `V` (weight), `M` (modulus), `c` (row), `μ` (frequency). -/
@[kb "shimura1978" "§3: Ramanujan-type row averages of an Eisenstein weight [unverified]"]
noncomputable def rowAvg (V : F × F → ℂ) (M : Ideal (𝓞 F)) (c μ : F) : ℂ :=
  ((Ideal.absNorm M : ℂ))⁻¹ * ∑ᶠ r : 𝓞 F ⧸ M, V (c, ιO (Quotient.out r)) * eTr (μ * ιO (Quotient.out r) / c)

/-- The sign-and-norm identity $\operatorname{sgn}N(c)\prod_v\sigma_v(\mu/c) = \prod_v\sigma_v(\mu)\cdot|N(c)|^{-1}$. -/
lemma normSign_mul_prod_div {c : F} (hc : c ≠ 0) (μ : F) :
    normSign c * ∏ v, ((realEmb F v (μ / c) : ℝ) : ℂ) =
      (∏ v, ((realEmb F v μ : ℝ) : ℂ)) * ((absNorm c : ℝ) : ℂ)⁻¹ := by
  rw [normSign, absNorm, ← Finset.prod_mul_distrib, Complex.ofReal_prod, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hcv : realEmb F v c ≠ 0 := (map_ne_zero_iff _ (realEmb_injective F v)).mpr hc
  rw [map_div₀]
  split_ifs with h
  · rw [abs_of_pos h]; push_cast; field_simp
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hcv)]; push_cast
    have : (realEmb F v c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcv
    field_simp

/-- **The row coefficient as a row average** (any admissible modulus): for a translation-invariant integral weight $W$ of
level $\mathfrak M$, a row $t$ with $c = \tilde t \ne 0$, and $0 \ne M \subseteq \mathfrak M$ with $e(\operatorname{Tr}\mu m/c) = 1$ for $m \in M$,
$$\rho_W(t, \mu) = c_{\mathcal O}\,\Lambda_2(\mu)\,|N(c)|^{-1}\,\frac1{N(M)}\sum_{r\in\mathcal O/M}W(c, \tilde r)\,e\Big(\operatorname{Tr}\frac{\mu\tilde r}c\Big),$$
$\Lambda_2$ = `lipCoeff 2`, $c_{\mathcal O}$ = `latConst (oBasis F)` $= |d_F|^{-1/2}$. (If $\mu/c$ is not in the trace dual of $\mathfrak M$ both
sides vanish.) -/
@[kb "shimura1978" "§3: the row coefficients of E₂ as Ramanujan-type averages [unverified]"]
theorem rowCo_eq {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W 2 𝔐) {t : UOrbitF F} (ht : t.out ≠ 0)
    {μ : F} {M : Ideal (𝓞 F)} (hM : M ≠ ⊥) (hM𝔐 : M ≤ 𝔐) (hμM : ∀ m ∈ M, eTr (μ * ιO m / crep t) = 1) :
    rowCo W 𝔐 hW.ne t μ = (latConst (oBasis F) : ℂ) * lipCoeff 2 (realVec μ) *
      ((absNorm (crep t) : ℝ) : ℂ)⁻¹ * rowAvg W M (crep t) μ := by
  classical
  set c := crep t
  have hc : c ≠ 0 := (crep_eq_zero_iff t).not.mpr ht
  have hcF : ∀ x : F, x / c * c = x := fun x => div_mul_cancel₀ x hc
  -- the case `μ` not totally positive
  by_cases hpos : ∀ v, 0 < realVec μ v
  swap
  · have hL : lipCoeff 2 (realVec μ) = 0 := by rw [lipCoeff, if_neg hpos]
    rw [hL, mul_zero, zero_mul, zero_mul, rowCo]
    refine (tsum_congr fun n => ?_).trans tsum_zero
    split_ifs with h
    · by_contra hA
      exact hpos (fun v => by rw [← h]; exact oscMu_pos hW.ne hA v)
    · rfl
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
    simpa [realVec] using hpos v
  by_cases hdual : ∀ m ∈ 𝔐, eTr (μ / c * ιO m) = 1
  · -- `μ/c` is the dual vector `ν_n`
    obtain ⟨n, hn⟩ := exists_dualElt_of_eTr (I := levelUnit 𝔐 hW.ne) (x := μ / c) (by
      intro y hy
      obtain ⟨m, hm, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
      exact hdual m hm)
    have hdv : dualVec (levelBasis 𝔐 hW.ne) n = realVec (μ / c) := by
      rw [dualVec_koecherBasis, hn]
    have hmu : ∀ n', oscMu 𝔐 hW.ne (t, n') = realVec (dualVec (levelBasis 𝔐 hW.ne) n' |> fun _ =>
        QuadFormsKB.Analysis.dualElt (levelUnit 𝔐 hW.ne) n' * c) := by
      intro n'
      funext v
      simp only [oscMu, dualVec_koecherBasis, realVec, map_mul]
      rfl
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hμ0
      have : μ / c = 0 := by rw [← hn]; simp [QuadFormsKB.Analysis.dualElt]
      rwa [div_eq_zero_iff, or_iff_left hc] at this
    have hrow : rowCo W 𝔐 hW.ne t μ = oscA W 𝔐 hW.ne (t, n) := by
      rw [rowCo, tsum_eq_single n]
      · rw [if_pos (by rw [hmu, hn, hcF])]
      · intro n' hn'
        rw [if_neg]
        intro h
        rw [hmu] at h
        apply hn'
        apply dualVec_injective (levelBasis 𝔐 hW.ne)
        rw [hdv, dualVec_koecherBasis]
        congr 1
        have h' := realVec_injective h
        field_simp
        exact h'
    rw [hrow, oscA, if_neg (by push Not; exact ⟨ht, hn0⟩)]
    -- the archimedean factor
    have harch : (if ∀ v, 0 < dualVec (levelBasis 𝔐 hW.ne) n v * realEmb F v c then
        normSign c * ((-2 * π * Complex.I) ^ 2 / (2 - 1).factorial) ^ Fintype.card (InfinitePlace F) *
          ∏ v, ((dualVec (levelBasis 𝔐 hW.ne) n v : ℂ) ^ (2 - 1)) else 0) =
        lipCoeff 2 (realVec μ) * ((absNorm c : ℝ) : ℂ)⁻¹ := by
      have hiff : ∀ v, dualVec (levelBasis 𝔐 hW.ne) n v * realEmb F v c = realVec μ v := by
        intro v; rw [hdv]; simp only [realVec]; rw [← map_mul, hcF]
      simp_rw [hiff]
      rw [lipCoeff, if_pos hpos, if_pos hpos, hdv]
      simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one, Nat.add_one_sub_one]
      have := normSign_mul_prod_div hc μ
      simp only [realVec] at this ⊢
      linear_combination ((-2 * π * Complex.I) ^ 2) ^ Fintype.card (InfinitePlace F) * this
    rw [harch]
    -- the row sum
    have hR : rowR W 𝔐 c (dualVec (levelBasis 𝔐 hW.ne) n) =
        ∑ᶠ r : 𝓞 F ⧸ 𝔐, W (c, ιO (Quotient.out r)) * eTr (μ * ιO (Quotient.out r) / c) := by
      rw [rowR, hdv]
      refine finsum_congr fun r => ?_
      rw [cexp_pair_realVec]
      congr 2
      field_simp
    have havg := avg_quot_eq hM hM𝔐 (fun r => W (c, ιO r) * eTr (μ * ιO r / c)) (by
      intro r m hm
      simp only [map_add]
      have h1 := hW.per (c, ιO r) 0 m (Submodule.zero_mem _) hm
      simp only [map_zero, add_zero] at h1
      rw [h1, mul_add, add_div, eTr_add, show μ * ιO m / c = μ / c * ιO m by ring, hdual m hm, mul_one])
    rw [hR, latConst_levelBasis, rowAvg, havg]
    push_cast
    ring
  · -- off the dual: both sides vanish
    push Not at hdual
    obtain ⟨m₀, hm₀, he⟩ := hdual
    have hL : rowCo W 𝔐 hW.ne t μ = 0 := by
      rw [rowCo]
      refine (tsum_congr fun n => ?_).trans tsum_zero
      rw [if_neg]
      intro h
      apply he
      have hx : QuadFormsKB.Analysis.dualElt (levelUnit 𝔐 hW.ne) n = μ / c := by
        have h' : realVec (QuadFormsKB.Analysis.dualElt (levelUnit 𝔐 hW.ne) n * c) = realVec μ := by
          rw [← h]; funext v; simp only [oscMu, dualVec_koecherBasis, realVec, map_mul]; rfl
        have := realVec_injective h'
        field_simp
        exact this
      rw [← hx]
      exact eTr_dualElt_mul_of_mem n (mem_levelUnit hW.ne hm₀)
    have hR : rowAvg W M c μ = 0 := by
      rw [rowAvg]
      refine mul_eq_zero_of_right _ (finsum_quot_eq_zero_of_shift hM
        (fun r => W (c, ιO r) * eTr (μ * ιO r / c)) (s := m₀) (e := eTr (μ / c * ιO m₀)) he
        fun r m hm => ?_)
      simp only [map_add]
      have h1 := hW.per (c, ιO r) 0 (m₀ + m) (Submodule.zero_mem _) (𝔐.add_mem hm₀ (hM𝔐 hm))
      simp only [map_zero, add_zero, map_add] at h1
      rw [add_assoc, h1, show μ * (ιO r + (ιO m₀ + ιO m)) / c = μ * ιO r / c + (μ / c * ιO m₀ + μ * ιO m / c) by
        ring, eTr_add, eTr_add, hμM m hm]
      ring
    rw [hL, hR, mul_zero]


/-! ### Vanishing of row coefficients -/

/-- $\rho_W(t, \mu) = 0$ for the zero row $t = 0$. -/
lemma rowCo_of_out_eq_zero (W : F × F → ℂ) (𝔐 : Ideal (𝓞 F)) (h𝔐 : 𝔐 ≠ ⊥) {t : UOrbitF F} (ht : t.out = 0) (μ : F) :
    rowCo W 𝔐 h𝔐 t μ = 0 := by
  classical
  rw [rowCo]
  refine (tsum_congr fun n => ?_).trans tsum_zero
  have : oscA W 𝔐 h𝔐 (t, n) = 0 := by unfold oscA; rw [if_pos (Or.inl ht)]
  simp [this]

/-- $\rho_W(t, \mu) = 0$ if $W$ vanishes on the row $c = \tilde t$. -/
lemma rowCo_of_row_eq_zero (W : F × F → ℂ) (𝔐 : Ideal (𝓞 F)) (h𝔐 : 𝔐 ≠ ⊥) {t : UOrbitF F}
    (h0 : ∀ d : 𝓞 F, W (crep t, ιO d) = 0) (μ : F) : rowCo W 𝔐 h𝔐 t μ = 0 := by
  classical
  rw [rowCo]
  refine (tsum_congr fun n => ?_).trans tsum_zero
  have hR : rowR W 𝔐 (crep t) (dualVec (levelBasis 𝔐 h𝔐) n) = 0 := by
    rw [rowR]; refine finsum_eq_zero_of_forall_eq_zero fun r => ?_; rw [h0, zero_mul]
  have : oscA W 𝔐 h𝔐 (t, n) = 0 := by unfold oscA; split_ifs <;> simp [hR]
  simp [this]

/-- $\rho_W(t, \mu) = 0$ unless $\mu/c$ is in the trace dual of the level. -/
lemma rowCo_of_eTr_ne {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W 2 𝔐) {t : UOrbitF F} {μ : F}
    {m₀ : 𝓞 F} (hm₀ : m₀ ∈ 𝔐) (he : eTr (μ / crep t * ιO m₀) ≠ 1) : rowCo W 𝔐 hW.ne t μ = 0 := by
  classical
  by_cases ht : t.out = 0
  · exact rowCo_of_out_eq_zero W 𝔐 hW.ne ht μ
  have hc : crep t ≠ 0 := (crep_eq_zero_iff t).not.mpr ht
  rw [rowCo]
  refine (tsum_congr fun n => ?_).trans tsum_zero
  rw [if_neg]
  intro h
  apply he
  have hx : QuadFormsKB.Analysis.dualElt (levelUnit 𝔐 hW.ne) n = μ / crep t := by
    have h' : realVec (QuadFormsKB.Analysis.dualElt (levelUnit 𝔐 hW.ne) n * crep t) = realVec μ := by
      rw [← h]; funext v; simp only [oscMu, dualVec_koecherBasis, realVec, map_mul]
    have := realVec_injective h'
    field_simp
    exact this
  rw [← hx]
  exact eTr_dualElt_mul_of_mem n (mem_levelUnit hW.ne hm₀)

open Classical in
/-- **The number of residues in an ideal**: for $J \le I$ nonzero, $\#\{r \in \mathcal O/J : \tilde r \in I\}\cdot N(I) = N(J)$. -/
lemma sum_indicator_mem_quot {J I : Ideal (𝓞 F)} (hJ : J ≠ ⊥) (hJI : J ≤ I) :
    (∑ᶠ r : 𝓞 F ⧸ J, (if Quotient.out r ∈ I then (1 : ℂ) else 0)) * (Ideal.absNorm I : ℂ) =
      (Ideal.absNorm J : ℂ) := by
  classical
  have hI : I ≠ ⊥ := fun h => hJ (le_bot_iff.mp (h ▸ hJI))
  haveI := SiegelWeil.SingularNF.finite_quot hJ
  haveI := SiegelWeil.SingularNF.finite_quot hI
  letI : Fintype (𝓞 F ⧸ J) := Fintype.ofFinite _
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  set f : (𝓞 F ⧸ J) →+ (𝓞 F ⧸ I) := (Ideal.Quotient.factor hJI).toAddMonoidHom
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hJI
  have h := SiegelWeil.SingularNF.sum_comp_mul f hf (fun h => if h = 0 then (1 : ℂ) else 0)
  have hcomp : ∀ r : 𝓞 F ⧸ J, (f r = 0) ↔ Quotient.out r ∈ I := by
    intro r
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    conv_lhs => rw [← Ideal.Quotient.mk_out r]
    rfl
  simp only [hcomp, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, one_mul] at h
  rw [finsum_eq_sum_of_fintype]
  have hNJ : (Fintype.card (𝓞 F ⧸ J) : ℂ) = Ideal.absNorm J := by
    rw [← SiegelWeil.SingularNF.card_quot_eq_absNorm, Nat.card_eq_fintype_card]
  have hNI : (Fintype.card (𝓞 F ⧸ I) : ℂ) = Ideal.absNorm I := by
    rw [← SiegelWeil.SingularNF.card_quot_eq_absNorm, Nat.card_eq_fintype_card]
  rw [hNJ, hNI] at h
  exact h

end QuadFormsKB.HilbertModular
