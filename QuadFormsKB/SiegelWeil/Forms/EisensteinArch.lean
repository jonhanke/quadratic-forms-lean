/-
# The archimedean section of degree $r$ and weight $m$ (Siegel–Weil for forms by forms)

**Layer:** archimedean, over a totally real number field $F$ with real embeddings $\sigma_v$ (`realEmb F v`).

**Setting.** $Z = (Z_v)_v$ with $Z_v$ an $r\times r$ complex matrix, one per real place $v$ ($Z \in \mathbb H_r^d$ in applications,
`siegelHF`); for $\gamma = \begin{pmatrix}A&B\\C&D\end{pmatrix} \in \mathrm{Sp}_{2r}(F)$,
$$j(\gamma, Z) = \prod_v\det\big(\sigma_v(C)Z_v + \sigma_v(D)\big)\quad(\texttt{denR}),$$
and the **archimedean section of weight $m$** at $s$ (`archSecR`):
$$f_\infty(\gamma g_Z, s) = \prod_v\det(\operatorname{Im}Z_v)^{(s+\rho_r)/2}\cdot j(\gamma, Z)^{-m}\cdot|j(\gamma, Z)|^{m-(s+\rho_r)},\qquad
  \rho_r = \tfrac{r+1}2.$$
At $s = s_0 = m - \rho_r$ the last factor is $1$ and $f_\infty(\gamma g_Z, s_0) = \det(\operatorname{Im}Z)^{m/2}j(\gamma, Z)^{-m}$, the classical
holomorphic section of weight $m$ ($n = 2m$).

**Result.** `isArchSectionR_archSecR`: for $Q = \sum_ib_ix_i^2$ totally positive ($b_i \in \mathcal O_F$), `archSecR` satisfies the
parabolic law $f_\infty(n(B)m(A)\gamma) = \chi_{V,\infty}(\det A)|N(\det A)|^{s+\rho_r}f_\infty(\gamma)$ (`IsArchSectionR`), for every $s$ and
every $Z$. (*Proof:* the bottom blocks of $n(B)m(A)\gamma$ are ${}^tA^{-1}(C\ D)$, so $j$ is multiplied by $\prod_v\sigma_v(\det A)^{-1}$, and
$\chi_{V,\infty}(t)|N(t)|^m = \prod_v\sigma_v(t)^m$ for $Q$ totally positive, `chiV_mul_md_pow`.) For $r = 1$ this is `archSecS`
(`SiegelWeil/Convergence.lean`).

Sources: Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1 (the standard section of weight $l$) [unverified];
Shimura, *On Eisenstein series*, Duke Math. J. 50 (1983) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinGlobal
import QuadFormsKB.SiegelWeil.Convergence

open Matrix NumberField NumberField.mixedEmbedding IsDedekindDomain
open QuadFormsKB.HilbertModular QuadFormsKB.Lattices QuadFormsKB.WeilRep QuadFormsKB.WeilRep.Genus

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {r : ℕ}

local notation "RP" => {w : InfinitePlace F // InfinitePlace.IsReal w}
local notation "ιO" => algebraMap (𝓞 F) F

/-- $\sigma_v(C)Z_v + \sigma_v(D)$ for the bottom blocks $C, D$ of $\gamma$. -/
def denW (γ : Sp r F) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (v : InfinitePlace F) :
    Matrix (Fin r) (Fin r) ℂ :=
  (blockC γ).map (fun x => (realEmb F v x : ℂ)) * Z v + (blockD γ).map (fun x => (realEmb F v x : ℂ))

/-- $j(\gamma, Z) = \prod_v\det(\sigma_v(C)Z_v + \sigma_v(D))$. -/
def denR (γ : Sp r F) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) : ℂ := ∏ v, (denW γ Z v).det

variable (m : ℕ) in
/-- **The archimedean section of degree $r$ and weight $m$** at $s$ through $g_Z$:
$f_\infty(\gamma g_Z, s) = \prod_v\det(\operatorname{Im}Z_v)^{(s+\rho_r)/2}\,j(\gamma, Z)^{-m}\,|j(\gamma, Z)|^{m-(s+\rho_r)}$. -/
@[kb "kudla2008" "§1 (the standard section of weight l in I(s, χ)) [unverified]"]
def archSecR (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (s : ℂ) (γ : Sp r F) : ℂ :=
  (∏ v, ((((Z v).map Complex.im).det : ℝ) : ℂ) ^ ((s + rhoR r) / 2)) * denR γ Z ^ (-(m : ℤ)) *
    ((‖denR γ Z‖ : ℝ) : ℂ) ^ ((m : ℂ) - (s + rhoR r))

lemma blockD_spN_spM (B : Matrix (Fin r) (Fin r) F) (hB : Bᵀ = B) (A : GL (Fin r) F) :
    blockD (spN B hB * spM A) = (((A⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F))ᵀ := by
  simp [blockD, spN_coe, spM_coe, fromBlocks_multiply]

lemma det_blockD_spN_spM (B : Matrix (Fin r) (Fin r) F) (hB : Bᵀ = B) (A : GL (Fin r) F) :
    (blockD (spN B hB * spM A)).det = (((A : Matrix (Fin r) (Fin r) F).det)⁻¹) := by
  rw [blockD_spN_spM, det_transpose, Matrix.coe_units_inv, det_nonsing_inv, Ring.inverse_eq_inv']

lemma map_mul_emb (v : InfinitePlace F) (M N : Matrix (Fin r) (Fin r) F) :
    (M * N).map (fun x => (realEmb F v x : ℂ)) = M.map (fun x => (realEmb F v x : ℂ)) * N.map (fun x => (realEmb F v x : ℂ)) :=
  Matrix.map_mul (f := (Complex.ofRealHom).comp (realEmb F v))

/-- $j(n(B)m(A)\gamma, Z) = \prod_v\sigma_v(\det A)^{-1}\cdot j(\gamma, Z)$. -/
lemma denR_spN_spM_mul (B : Matrix (Fin r) (Fin r) F) (hB : Bᵀ = B) (A : GL (Fin r) F) (γ : Sp r F)
    (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    denR (spN B hB * spM A * γ) Z =
      (∏ v, (realEmb F v (((A : Matrix (Fin r) (Fin r) F).det)⁻¹) : ℂ)) * denR γ Z := by
  obtain ⟨hC, hD⟩ := blockCD_mul_of_mem_siegelP (spN_spM_mem_siegelP B hB A) γ
  unfold denR
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have e : denW (spN B hB * spM A * γ) Z v =
      (blockD (spN B hB * spM A)).map (fun x => (realEmb F v x : ℂ)) * denW γ Z v := by
    rw [denW, denW, hC, hD, map_mul_emb, map_mul_emb, Matrix.mul_add, Matrix.mul_assoc]
  rw [e, det_mul, ← det_blockD_spN_spM B hB A]
  congr 1
  have := RingHom.map_det ((Complex.ofRealHom).comp (realEmb F v)) (blockD (spN B hB * spM A))
  simpa [RingHom.mapMatrix_apply, Function.comp_def] using this.symm

open scoped Classical in
/-- **The archimedean section has the parabolic law of $I(s, \chi_V)$** for every $s$ and $Z$ ($Q = \sum_ib_ix_i^2$ totally
positive): `archSecR` is an `IsArchSectionR` at $s$. -/
@[kb "kudla2008" "§1 (the standard section of weight l lies in I(s, χ)) [unverified]"]
theorem isArchSectionR_archSecR {m : ℕ} (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (s : ℂ) :
    IsArchSectionR (unitsOfInt b hb) (archSecR m Z s) s := by
  intro B hB A γ
  set t : Fˣ := detU A
  have htA : ((t : Fˣ) : F) = (A : Matrix (Fin r) (Fin r) F).det := rfl
  rw [← htA]
  have hpos : ∀ i (w : RP), 0 < ((aInf (unitsOfInt b hb) i : (mixedSpace F)ˣ) : mixedSpace F).1 w := fun i w => by
    show 0 < ew w _
    rw [ew_eq_realEmbF]; exact hbpos i w.1
  have hχ := chiV_mul_md_pow hpos (mixedEmbedding F (t : F)) (fun w => by
    rw [mixedEmbedding_fst]; exact (map_ne_zero _).mpr t.ne_zero)
  have hRP : ∏ w : RP, ((((mixedEmbedding F (t : F)).1 w : ℝ)) : ℂ) ^ m =
      ∏ v, ((realEmb F v (t : F) : ℝ) : ℂ) ^ m := by
    rw [← prod_RP_eq]; exact Finset.prod_congr rfl fun w _ => by rw [mixedEmbedding_fst, ew_eq_realEmbF]
  rw [hRP] at hχ
  set N : ℝ := mixedEmbedding.norm (mixedEmbedding F (t : F))
  have hNeq : N = ∏ v, |realEmb F v (t : F)| := mixedNorm_eq_prod _
  have hN0 : 0 < N := by
    rw [hNeq]; exact Finset.prod_pos fun v _ => abs_pos.mpr ((map_ne_zero _).mpr t.ne_zero)
  have hmd : (localDataInf (F := F)).md (mixedEmbedding F (t : F)) = N := rfl
  rw [hmd] at hχ
  set E := denR γ Z
  set P : ℂ := ∏ v, (realEmb F v (((t : Fˣ) : F)⁻¹) : ℂ) with hPdef
  have hPn : ‖P‖ = N⁻¹ := by
    rw [hPdef, norm_prod, hNeq, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_inv₀, Complex.ofReal_inv, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  have hPz : P ^ (-(m : ℤ)) = ∏ v, ((realEmb F v (t : F) : ℝ) : ℂ) ^ m := by
    rw [hPdef, _root_.zpow_neg, zpow_natCast, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_inv₀, Complex.ofReal_inv, inv_pow, inv_inv]
  unfold archSecR
  rw [denR_spN_spM_mul, ← htA]
  rw [mul_zpow, norm_mul, hPn, hPz, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr hN0.le) (norm_nonneg _), Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hN0.le]; exact Real.pi_ne_zero.symm),
    Complex.cpow_sub _ _ (by exact_mod_cast hN0.ne'), Complex.cpow_natCast, ← hχ]
  have hNm : ((N : ℝ) : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hN0.ne')
  have hNs : ((N : ℝ) : ℂ) ^ (s + rhoR r) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => (by exact_mod_cast hN0.ne' : ((N : ℝ) : ℂ) ≠ 0) h.1
  field_simp

end QuadFormsKB.SiegelWeil.Forms
