import QuadFormsKB.Tamagawa.Measure.Weil.MuTamSO
import QuadFormsKB.Tamagawa.BinaryRegChange

/-!
# Weil's Tamagawa measure on $SO(V)(\mathbb A)$ for binary $V$, with convergence factors
**Layer:** number fields. $F$ is any number field, $Q_0$ a nondegenerate binary quadratic form over $\mathcal O_F$
($V = F^2$, $Q = Q_0\otimes F$, any signature at the real places, complex places allowed), $H = H_{Q_0}$ its Hessian,
so $-\det H = b^2-4ac$ for $Q_0 = ax_0^2+bx_0x_1+cx_1^2$. For anisotropic $V$, $SO(V)\cong R^1_{E/F}\mathbb G_m$ with
$E = F(\sqrt{-\det H})$, the **discriminant field**.

For $n = 2$ the local volumes $\alpha_v = \mu_v(SO(L_v))$ are $1-\chi_E(v)/Nv$ at almost all $v$, so $\prod_v\alpha_v$ is not
absolutely convergent and `muTam Q₀ hQ 1` is not Weil's measure (Mathlib's `tprod` returns $1$; the warning on
`tamagawaK`). Weil's measure uses convergence factors: the local measures $L_v(1,\chi_E)\,\omega_v$ and the global
factor $\rho^{-1}$, $\rho = L(1,\chi_E)$ (Weil 1982, §2.3, p. 21: $\prod_v\lambda_v^{-1}\omega_v$; Ono 1963 for tori
[unverified locators]).

**Defines**
* `IsDiscField Q₀ E` (a condition): $[E:F] = 2$ and $E = F(s)$ with $s^2 = -\det H$;
* `chiE F E v` $= \chi_{E/F}(v)\in\{1,-1,0\}$ (`relChar`: split, inert, ramified);
* `lamL χ v` $= 1-\chi(v)/Nv = L_v(1,\chi)^{-1}$, the repository's $\lambda_v$ (the local measure is $\lambda_v^{-1}\mu_v$);
* `muTamChi Q₀ hQ χ` $= L(1,\chi)^{-1}\cdot$ `muTam Q₀ hQ (lamL χ)`, and **`muTamBin Q₀ hQ E`** = `muTamChi Q₀ hQ (chiE F E)`:
  Weil's Tamagawa measure on $SO(V)(\mathbb A)$ with the convergence factors of $\chi_E$.

**Proves**
* `lamL_eq_inv_lFactor` ($\lambda_v = L_v(1,\chi)^{-1}$), `lOne_chiE` ($L(1,\chi_E) = \rho_E/\rho_F > 0$);
* `eventually_muLocSO_lamL_chiE`: $\lambda_v^{-1}\mu_v(SO(L_v)) = 1$ for all but finitely many $v$, so the product of the local
  volumes has finite support (absolutely convergent), and `finFactor_lamL_eq`;
* `muTamChi_eq_regProd`: $\mu = \mathrm{regProd}(\chi,-1,\alpha)\cdot(\mu_{\infty,\mathrm{Tam}}\times\mu^1_f)$, $\mu^1_f(SO(\hat L)) = 1$;
* `chiP_eq_chiE` (the combinatorial `chiP · Q₀` is $\chi_E$ off a finite set),
  **`muTamBin_eq_chiP`**, **`muTamBin_congr`**: the measure is the one built from `chiP`, so it does not depend on the
  choice of $E$ (Weil 1982, §2.3: independence of the convergence factors);
* `isDiscField_iff_not_isSquare`-type facts: `not_isSquare_of_isDiscField`, `exists_isDiscField` (an $E$ exists whenever
  $-\det H$ is not a square, over every number field).
-/

open MeasureTheory Measure Set Topology
open scoped ENNReal NNReal Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure QuadFormsKB.RegProd
  QuadFormsKB.NFEuler QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F]

/-! ### The discriminant field and its character -/

/-- **$E$ is the discriminant field of the binary form $Q_0$** (a condition): $[E:F] = 2$, and $E$ contains a square root
$s\notin F$ of $-\det H_{Q_0}$ ($= b^2-4ac$ for $Q_0 = ax_0^2+bx_0x_1+cx_1^2$), so $E = F(s)$; this determines $E$ up to
$F$-isomorphism. For anisotropic $Q_0$, $SO(V)\cong R^1_{E/F}\mathbb G_m$.

Fields:
- `finrank_eq_two`: $[E:F] = 2$;
- `exists_sqrt`: some $s\in E$ with $s^2 = -\det H_{Q_0}$ and $s\notin F$. -/
@[kb "weil1982" "§2.4 (convergence factors of a torus); ono1963 [unverified]"]
structure IsDiscField (Q₀ : QuadForm (𝓞 F) 2) (E : Type) [Field E] [NumberField E] [Algebra F E] : Prop where
  finrank_eq_two : Module.finrank F E = 2
  exists_sqrt : ∃ s : E, s ^ 2 = algebraMap F E (algebraMap (𝓞 F) F (-Q₀.hessian.det)) ∧
    s ∉ Set.range (algebraMap F E)

/-- **The character $\chi_E = \chi_{E/F}$ of a quadratic extension** at a finite place $v$: $1$, $-1$, $0$ when $v$ splits,
is inert, ramifies in $E$ (`relChar`, `Binary.Rel.splitting`). -/
def chiE (F : Type) [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (Binary.Rel.relChar E v : ℝ)

/-- **The repository's convergence factor** $\lambda_v = 1-\chi(v)\,Nv^{-1} = L_v(1,\chi)^{-1}$: the local measure is
$\lambda_v^{-1}\mu_v$ (`muLocSO v Q₀ λ_v`), so this is Weil's and Ono's factor $L_v(1,\chi)$ multiplying $\omega_v$
(as `lamV` for $\mathbb G_m$). -/
def lamL (χ : HeightOneSpectrum (𝓞 F) → ℝ) (v : HeightOneSpectrum (𝓞 F)) : ℝ := 1 - χ v / (normP v : ℝ)

theorem lamL_pos {χ : HeightOneSpectrum (𝓞 F) → ℝ} (hχ : ∀ v, |χ v| ≤ 1) (v : HeightOneSpectrum (𝓞 F)) :
    0 < lamL χ v :=
  one_sub_div_pos (hχ v) v

/-- $\lambda_v = L_v(1,\chi)^{-1}$, with $L_v(s,\chi) = (1-\chi(v)Nv^{-s})^{-1}$ = `lFactor χ s v`. -/
theorem lamL_eq_inv_lFactor (χ : HeightOneSpectrum (𝓞 F) → ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    lamL χ v = (lFactor χ 1 v)⁻¹ := by
  rw [lFactor, inv_inv, lamL, Real.rpow_neg_one, div_eq_mul_inv]

section Char

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem abs_chiE_le (hdeg : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) : |chiE F E v| ≤ 1 := by
  have := Binary.Rel.abs_relChar_le_one hdeg v
  unfold chiE; exact_mod_cast this

/-- **$L(1,\chi_E)$ exists and is positive** (for every quadratic extension of every number field): it is
$\rho_E/\rho_F$ (`hasLOne_relChar`, from the residues of the Dedekind zeta functions). -/
@[kb "neukirch1999" "Ch. VII §5, Cor. 5.11 (L(1, χ_{E/F}) = ρ_E/ρ_F) [unverified]"]
theorem lOne_chiE (hdeg : Module.finrank F E = 2) :
    0 < LOne (chiE F E) ∧ HasLOne (chiE F E) (LOne (chiE F E)) :=
  exists_hasLOne_of_almost_relChar hdeg (abs_chiE_le hdeg) ⟨∅, fun _ _ => rfl⟩

theorem lOne_chiE_eq (hdeg : Module.finrank F E = 2) :
    LOne (chiE F E) = dedekindZeta_residue E / dedekindZeta_residue F :=
  (hasLOne_relChar hdeg).lOne_eq

end Char

/-! ### The archimedean normalization constants in rank 2 -/

/-- **Weil's global factor in rank 2:** $c_F = |d_F|^{-\dim SO_2/2} = |d_F|^{-1/2}$. -/
theorem cF_two : cF F 2 = |(discr F : ℝ)| ^ (-(1 / 2 : ℝ)) := by
  rw [cF]; norm_num

/-- **Weil's complex normalization in rank 2:** $2^{\dim SO_2\cdot r_2} = 2^{r_2}$ ($|dz\wedge d\bar z| = 2\,dx\,dy$ once per
complex place, $\dim SO_2 = 1$). -/
theorem cxWeil_two : cxWeil F 2 = (2 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces F := by
  rw [cxWeil]; norm_num

/-! ### The measure -/

variable (Q₀ : QuadForm (𝓞 F) 2)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- The Haar measure $\mu^1_f$ on $SO(V)(\mathbb A_f)$ with $\mu^1_f(SO(\hat L)) = 1$. -/
def muFinOne : Measure (SOAf Q₀) := haarNorm (KSO Q₀) (isCompact_KSO Q₀) (isOpen_KSO Q₀) 1

instance : (muFinOne Q₀).IsMulLeftInvariant := by unfold muFinOne; infer_instance

theorem muFinOne_KSO : muFinOne Q₀ (KSO Q₀ : Set (SOAf Q₀)) = 1 := by
  rw [muFinOne, haarNorm_self]; rfl

instance sigmaFinite_muFinOne : SigmaFinite (muFinOne Q₀) := by
  have := countable_SOAf_quot Q₀
  refine Measure.sigmaFinite_of_countable (S := Set.range fun q : SOAf Q₀ ⧸ KSO Q₀ =>
      (Quotient.out q : SOAf Q₀) • (KSO Q₀ : Set (SOAf Q₀))) (Set.countable_range _) ?_ ?_
  · rintro _ ⟨q, rfl⟩
    rw [measure_smul, muFinOne_KSO]; exact ENNReal.one_lt_top
  · refine Set.eq_univ_of_forall fun g => ?_
    refine Set.mem_sUnion.mpr ⟨_, ⟨(QuotientGroup.mk g : SOAf Q₀ ⧸ KSO Q₀), rfl⟩, ?_⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KSO Q₀) g
    refine Set.mem_smul_set.mpr ⟨(k : SOAf Q₀)⁻¹, (KSO Q₀).inv_mem k.2, ?_⟩
    rw [smul_eq_mul, hk, mul_inv_cancel_right]

/-- $\mu_f = \prod'_v\mu_v(SO(L_v))\cdot\mu^1_f$. -/
theorem muFin_eq_smul_muFinOne (lam : HeightOneSpectrum (𝓞 F) → ℝ) :
    muFin Q₀ lam = ENNReal.ofReal (finFactor Q₀ lam) • muFinOne Q₀ := by
  rw [muFin, muFinOne, haarNorm, haarNorm, one_smul, ENNReal.ofReal]
  rfl

/-- **The finite product with the factors $\lambda_v = L_v(1,\chi)^{-1}$:**
$\prod'_v\lambda_v^{-1}\mu_v(SO(L_v)) = \prod'_v\alpha_v(L,L)\,(1-\chi(v)/Nv)^{-1}$, the product of `regProd χ (-1)`. -/
theorem finFactor_lamL_eq (hQ : Q₀.Nondegenerate) {χ : HeightOneSpectrum (𝓞 F) → ℝ} (hχ : ∀ v, |χ v| ≤ 1) :
    finFactor Q₀ (lamL χ) =
      ∏' v, NF.siegelDensity v Q₀ Q₀ * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) := by
  rw [finFactor_eq Q₀ hQ (lamL_pos hχ)]
  refine tprod_congr fun v => ?_
  rw [_root_.zpow_neg_one, div_eq_mul_inv, lamL]

/-- **Weil's Tamagawa measure with the convergence factors of a character $\chi$** (rank 2):
$$\mu^\chi_{\mathrm{Tam}} = L(1,\chi)^{-1}\cdot c_F\,2^{r_2}\,\mu^{\mathrm{Leray}}_\infty\times\mu^{\lambda}_f,\qquad
  \lambda_v = L_v(1,\chi)^{-1},$$
i.e. `muTam Q₀ hQ (lamL χ)` with the global factor $\rho^{-1} = L(1,\chi)^{-1}$ (`LOne`). -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure ρ^{-1}∏_v λ_v^{-1}ω_v with convergence factors) [unverified]"]
def muTamChi (hQ : Q₀.Nondegenerate) (χ : HeightOneSpectrum (𝓞 F) → ℝ) : Measure (SOAdele Q₀) :=
  ENNReal.ofReal (LOne χ)⁻¹ • muTam Q₀ hQ (lamL χ)

/-- **Weil's Tamagawa measure on $SO(V)(\mathbb A)$ for binary $V$** (any signature, any number field), with the
convergence factors of the character $\chi_E$ of the discriminant field $E$:
$$\mu^{\chi_E}_{\mathrm{Tam}} = L(1,\chi_E)^{-1}\cdot|d_F|^{-1/2}\,2^{r_2}\,\mu^{\mathrm{Leray}}_\infty\times\mu_f,\qquad
  \mu_f(SO(\hat L)) = \prod_v\frac{\alpha_v(L,L)}{1-\chi_E(v)/Nv},$$
$L = \mathcal O_F^2$, $\alpha_v$ Siegel's local density (= Weil's $|\omega|_v(SO(L_v))$), $\mu^{\mathrm{Leray}}_\infty$ the
gauge-form measures at the real and complex places and $2^{r_2}$ Weil's normalization at the complex places
(`cxWeil`). The product has finite support (`eventually_muLocSO_lamL_chiE`), $L(1,\chi_E) = \rho_E/\rho_F$ (`lOne_chiE_eq`),
and the measure does not depend on the choice of $E$ (`muTamBin_congr`). -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure with convergence factors λ_v); §2.4, p. 23; ono1963 (τ of tori) [unverified]"]
def muTamBin (hQ : Q₀.Nondegenerate) (E : Type) [Field E] [NumberField E] [Algebra F E] : Measure (SOAdele Q₀) :=
  muTamChi Q₀ hQ (chiE F E)

instance (hQ : Q₀.Nondegenerate) (χ : HeightOneSpectrum (𝓞 F) → ℝ) : (muTamChi Q₀ hQ χ).IsMulLeftInvariant := by
  unfold muTamChi; infer_instance

instance (hQ : Q₀.Nondegenerate) (E : Type) [Field E] [NumberField E] [Algebra F E] :
    (muTamBin Q₀ hQ E).IsMulLeftInvariant := by
  unfold muTamBin; infer_instance

/-- **The measure as one constant times a fixed Haar measure:**
$\mu^\chi_{\mathrm{Tam}} = \mathrm{regProd}(\chi,-1,\alpha)\cdot(\mu_{\infty,\mathrm{Tam}}\times\mu^1_f)$, with
$\mathrm{regProd}(\chi,-1,\alpha) = L(1,\chi)^{-1}\prod_v\alpha_v(1-\chi(v)/Nv)^{-1}$. -/
theorem muTamChi_eq_regProd (hQ : Q₀.Nondegenerate) {χ : HeightOneSpectrum (𝓞 F) → ℝ} (hχ : ∀ v, |χ v| ≤ 1)
    (hL : 0 ≤ LOne χ) :
    muTamChi Q₀ hQ χ = ENNReal.ofReal (regProd χ (-1) fun v => NF.siegelDensity v Q₀ Q₀) •
      (muArchTamSO Q₀ hQ).prod (muFinOne Q₀) := by
  rw [muTamChi, muTam, muFin_eq_smul_muFinOne, Measure.prod_smul_right, smul_smul, ← ENNReal.ofReal_mul
    (inv_nonneg.mpr hL), finFactor_lamL_eq Q₀ hQ hχ, regProd, _root_.zpow_neg_one]

/-! ### Independence of the choice of $E$ -/

section Indep

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

/-- Under `IsDiscField`, $-\det H$ is not a square in $F$. -/
theorem not_isSquare_of_isDiscField (h : IsDiscField Q₀ E) :
    ¬ IsSquare (algebraMap (𝓞 F) F (-Q₀.hessian.det)) := by
  rintro ⟨r, hr⟩
  obtain ⟨s, hs, hsF⟩ := h.exists_sqrt
  have h1 : (s - algebraMap F E r) * (s + algebraMap F E r) = 0 := by
    have : s ^ 2 = (algebraMap F E r) ^ 2 := by rw [hs, hr, ← map_pow, sq]
    linear_combination this
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact hsF ⟨r, (sub_eq_zero.mp h2).symm⟩
  · exact hsF ⟨-r, by rw [map_neg]; linear_combination -h2⟩

theorem det_ne_zero_of_isDiscField (h : IsDiscField Q₀ E) : Q₀.hessian.det ≠ 0 := by
  intro h0
  apply not_isSquare_of_isDiscField Q₀ h
  rw [h0, neg_zero, map_zero]
  exact ⟨0, by rw [mul_zero]⟩

/-- **The combinatorial character is $\chi_E$ off a finite set:**
`chiP v Q₀` $= \chi_E(v)$ for all but finitely many $v$. -/
theorem chiP_eq_chiE (h : IsDiscField Q₀ E) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, chiP v Q₀ = chiE F E v := by
  have : Algebra.IsQuadraticExtension F E := ⟨h.finrank_eq_two⟩
  obtain ⟨s, hs, hsF⟩ := h.exists_sqrt
  have hδ : (-Q₀.hessian.det : 𝓞 F) ≠ 0 := neg_ne_zero.mpr (det_ne_zero_of_isDiscField Q₀ h)
  have hc : Binary.Rel.conj F E s = -s := by
    have hsq : (Binary.Rel.conj F E s - s) * (Binary.Rel.conj F E s + s) = 0 := by
      have : (Binary.Rel.conj F E s) ^ 2 = s ^ 2 := by
        rw [← map_pow, hs, AlgEquiv.commutes]
      linear_combination this
    rcases mul_eq_zero.mp hsq with h1 | h1
    · exfalso
      apply hsF
      rw [IsGalois.mem_range_algebraMap_iff_fixed]
      intro f
      rcases (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).mp (Binary.Rel.card_aut F E) with ⟨σ, hσ1, hσ⟩
      have hconj := hσ _ (Binary.Rel.conj_ne_one F E)
      by_cases hf : f = 1
      · rw [hf]; rfl
      · rw [hσ f hf, ← hconj]; exact sub_eq_zero.mp h1
    · linear_combination h1
  obtain ⟨S, hS⟩ := isAlmostRelChar_of_sqrt hδ hs hc (χ := fun v => chiP v Q₀) ∅ fun v _ h2 hd =>
    chiP_binary_eq_charNF v Q₀ h2 fun h' => hd (v.asIdeal.neg_mem_iff.2 h')
  exact ⟨S, hS⟩

/-- **The convergence factors make the product of local volumes finitely supported:** for all but finitely many $v$,
$\lambda_v^{-1}\mu_v(SO(L_v)) = \alpha_v(L,L)/(1-\chi_E(v)/Nv) = 1$. Hence $\prod_v\lambda_v^{-1}\mu_v(SO(L_v))$ converges
absolutely (Weil's condition on convergence factors, 1982, §2.3), whereas $\prod_v\mu_v(SO(L_v))$ does not. -/
@[kb "weil1982" "§2.3, p. 21 (convergence factors: ∏ λ_v^{-1} ω_v(G(𝔬_v)) absolutely convergent) [unverified]"]
theorem eventually_muLocSO_lamL_chiE (hQ : Q₀.Nondegenerate) (h : IsDiscField Q₀ E) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
      muLocSO v Q₀ (lamL (chiE F E) v) (soStabSO v Q₀ : Set (SOv v Q₀)) = 1 := by
  classical
  obtain ⟨S, hS⟩ := chiP_eq_chiE Q₀ h
  have hfin := hasFiniteMulSupport_siegelDensity_binary_reg hQ S hS
  refine ⟨S ∪ hfin.toFinset, fun v hv => ?_⟩
  rw [Finset.mem_union, not_or] at hv
  have h1 : NF.siegelDensity v Q₀ Q₀ * (1 - chiE F E v / (normP v : ℝ)) ^ (-1 : ℤ) = 1 := by
    by_contra hne
    exact hv.2 (hfin.mem_toFinset.mpr hne)
  rw [muLocSO_soStabSO, ← ENNReal.ofReal_one]
  congr 1
  rw [← h1, _root_.zpow_neg_one, div_eq_mul_inv, lamL]

/-- **The measure is the one built from the combinatorial character `chiP · Q₀`** (which differs from $\chi_E$ at
finitely many places): changing $\chi$ at finitely many places changes $L(1,\chi)$ and the local factors by
the same finite factor. -/
@[kb "weil1982" "§2.3, p. 21 (independence of the convergence factors) [unverified]"]
theorem muTamBin_eq_chiP (hQ : Q₀.Nondegenerate) (h : IsDiscField Q₀ E) :
    muTamBin Q₀ hQ E = ENNReal.ofReal (regProd (fun v => chiP v Q₀) (-1) fun v => NF.siegelDensity v Q₀ Q₀) •
      (muArchTamSO Q₀ hQ).prod (muFinOne Q₀) := by
  obtain ⟨S, hS⟩ := chiP_eq_chiE Q₀ h
  obtain ⟨hL0, hL⟩ := lOne_chiE h.finrank_eq_two
  rw [muTamBin, muTamChi_eq_regProd Q₀ hQ (abs_chiE_le h.finrank_eq_two) hL0.le,
    regProd_congr_finite (abs_chiP_le Q₀) (abs_chiE_le h.finrank_eq_two) S hS hL (-1) _
      (multipliable_siegelDensity_binary_reg hQ S hS)]

/-- **`muTamBin` does not depend on the choice of the discriminant field.** -/
theorem muTamBin_congr (hQ : Q₀.Nondegenerate) (h : IsDiscField Q₀ E) {E' : Type} [Field E'] [NumberField E']
    [Algebra F E'] (h' : IsDiscField Q₀ E') : muTamBin Q₀ hQ E = muTamBin Q₀ hQ E' := by
  rw [muTamBin_eq_chiP Q₀ hQ h, muTamBin_eq_chiP Q₀ hQ h']

end Indep

/-! ### Existence of the discriminant field -/

/-- **A discriminant field exists** whenever $-\det H$ is not a square in $F$ (every number field). -/
theorem exists_isDiscField (hd : ¬ IsSquare (algebraMap (𝓞 F) F (-Q₀.hessian.det))) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E), IsDiscField Q₀ E := by
  obtain ⟨E, _, _, _, s, hs, hspan⟩ := Lam.exists_quadExt _ hd
  obtain ⟨hQ, -⟩ := HN.quadData _ hd s hs hspan
  refine ⟨E, inferInstance, inferInstance, inferInstance, ⟨Algebra.IsQuadraticExtension.finrank_eq_two F E, s, hs, ?_⟩⟩
  rintro ⟨r, hr⟩
  apply hd
  refine ⟨r, (algebraMap F E).injective ?_⟩
  rw [← hs, ← hr, map_mul, sq]

end QuadFormsKB.Tamagawa.Measure.Weil
