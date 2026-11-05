/-
# A majorant of the Siegel Eisenstein series of degree $r$ depending on $Z$ only through the archimedean constants

**Layer:** global over a totally real number field $F$ of degree $d$.

**Setting.** As in `EisensteinSummable.lean`: $Q = \sum_{i<n}b_ix_i^2$ totally positive over $\mathcal O_F$, $n = 2m$, a finite datum $\Phi$,
$r \ge 1$, $\tau = \operatorname{Re}s + \frac{r+1}2 > 4r^2$.

**Result.** **`exists_norm_globalSecR_le`**: there are $K \ge 0$ and a summable $G \ge 0$ on $P(F)\backslash\mathrm{Sp}_{2r}(F)$ such that for every
$Z \in \mathbb H_r^d$ and every family of constants $c_w > 0$ with $|\det(CZ_w + D)| \ge c_w\max(1, |E_{ix}|)$ for all normalized real
Lagrangian blocks $E = (C\ D)$ (the conclusion of `exists_norm_det_CZD_ge`),
$$|f(\gamma g_Z, s)| \le \prod_w\det(\operatorname{Im}Z_w)^{\tau/2}\cdot K\cdot\Big(\prod_wc_w/2^d\Big)^{-\tau}\cdot G(P\gamma).$$
So a lower bound for $c_w$ that is uniform in $Z$ gives a majorant uniform in $Z$ (used for the Fourier coefficients and holomorphy of
$E$). The proof is that of `summable_norm_globalSecR` with the constants kept explicit.

Sources: Weil, Acta Math. 113 (1965), Ch. II [unverified]; Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I (normal convergence of
Eisenstein series) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinSummable

open Matrix NumberField IsDedekindDomain Filter
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData QuadFormsKB.WeilRep.Genus QuadFormsKB.Analysis

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-- The property of an archimedean constant $c$ at a point $Z \in \mathbb H_r$ (the conclusion of `exists_norm_det_CZD_ge`):
$c\max(1, |E_{ix}|) \le |\det(CZ + D)|$ for every real Lagrangian block $E = (C\ D)$ containing an identity block. -/
def IsDetConst (c : ℝ) (Z : Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ (C D : Matrix (Fin r) (Fin r) ℝ), C * Dᵀ = D * Cᵀ →
    ∀ h : Fin r → Fin r ⊕ Fin r, (Matrix.fromCols C D).submatrix id h = 1 →
      ∀ (i : Fin r) (x : Fin r ⊕ Fin r),
        c * max 1 |Matrix.fromCols C D i x| ≤ ‖(C.map (↑) * Z + D.map (↑) : Matrix (Fin r) (Fin r) ℂ).det‖

/-- **A majorant of the Eisenstein terms with explicit dependence on $Z$** (see the module docstring). -/
@[kb "weil1965" "Ch. II (convergence of the Eisenstein series) [unverified]; freitag1983 Ch. I [unverified]"]
theorem exists_norm_globalSecR_le (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (Φ : ∀ v : HeightOneSpectrum (𝓞 F), Sg (localDataV v) m r) (hΦ : ∀ᶠ v in cofinite, Φ v = oneSG v m r)
    (hr : 1 ≤ r) {s : ℂ} (hs : 4 * (r : ℝ) ^ 2 < s.re + ((r : ℝ) + 1) / 2) :
    ∃ (K : ℝ) (G : PQuot r F → ℝ), 0 ≤ K ∧ Summable G ∧ (∀ q, 0 ≤ G q) ∧
      ∀ Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ, Z ∈ siegelHF F r →
        ∀ c : InfinitePlace F → ℝ, (∀ w, 0 < c w) → (∀ w, IsDetConst (c w) (Z w)) →
          ∀ q : PQuot r F, ‖globalSecR (unitsOfInt b hb) Φ (archSecR m Z s) s q.out‖ ≤
            (∏ v, ((Z v).map Complex.im).det ^ ((s.re + ((r : ℝ) + 1) / 2) / 2)) * K *
              ((∏ w, c w) / 2 ^ Fintype.card (InfinitePlace F)) ^ (-(s.re + ((r : ℝ) + 1) / 2)) * G q := by
  classical
  set a := unitsOfInt b hb
  set τ : ℝ := s.re + ((r : ℝ) + 1) / 2 with hτ
  have hcard : (Fintype.card (Fin r × (Fin r ⊕ Fin r)) : ℝ) = 2 * (r : ℝ) ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]; push_cast; ring
  set Nc : ℝ := (Fintype.card (Fin r × (Fin r ⊕ Fin r)) : ℝ)
  have hr0 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hNc : 0 < Nc := by rw [hcard]; positivity
  have hNn : 0 < Fintype.card (Fin r × (Fin r ⊕ Fin r)) := Fintype.card_pos_iff.mpr ⟨(⟨0, hr⟩, Sum.inl ⟨0, hr⟩)⟩
  set α : ℝ := τ / Nc with hαdef
  have hα : 2 < α := by
    rw [hαdef, hcard, lt_div_iff₀ (by positivity)]; nlinarith
  have hτ0 : 0 ≤ τ := by nlinarith
  have hαN : α * Nc = τ := by rw [hαdef]; field_simp
  obtain ⟨K, hK0, hK⟩ := exists_norm_finSecR_le a Φ hΦ
  set zI : InfinitePlace F → UpperHalfPlane := fun _ => UpperHalfPlane.I
  set φ : F → ℝ := fun u => (‖eisDen ((1 : F), u) (fun v => (zI v : ℂ))‖ *
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 ‖algebraMap F (v.adicCompletion F) u‖) ^ (-α) with hφdef
  have hφ : Summable φ := summable_heightZeta zI hα
  have hφ0 : ∀ u, 0 ≤ φ u := fun u => Real.rpow_nonneg (mul_nonneg (norm_nonneg _)
    (finprod_nonneg fun v => zero_le_one.trans (le_max_left _ _))) _
  set G : Matrix (Fin r) (Fin r ⊕ Fin r) F → ℝ := fun E => ∏ p : Fin r × (Fin r ⊕ Fin r), φ (E p.1 p.2) with hGdef
  have hG : Summable G := by
    have h1 := summable_prod_pi (ι := Fin r × (Fin r ⊕ Fin r)) hφ0 hφ
    have h2 : Summable ((fun x : Fin r × (Fin r ⊕ Fin r) → F => ∏ p, φ (x p)) ∘
        (Equiv.curry (Fin r) (Fin r ⊕ Fin r) F).symm) := (Equiv.summable_iff _).mpr h1
    exact h2
  have hG0 : ∀ E, 0 ≤ G E := fun E => Finset.prod_nonneg fun p _ => hφ0 _
  refine ⟨K, G ∘ normEQ, hK0, hG.comp_injective normEQ_injective, fun q => hG0 _, ?_⟩
  intro Z hZ c hc0 hc q
  set c0 : ℝ := ∏ w, c w
  have hc00 : 0 < c0 := Finset.prod_pos fun w _ => hc0 w
  set d := Fintype.card (InfinitePlace F)
  set Yd : ℝ := ∏ v, ((Z v).map Complex.im).det ^ (τ / 2)
  have hYd : 0 ≤ Yd := Finset.prod_nonneg fun v _ => Real.rpow_nonneg (det_im_pos hZ v).le _
  set κ : ℝ := c0 / 2 ^ d
  have hκ : 0 < κ := div_pos hc00 (by positivity)
  set γ := q.out
  set γ' := normRep γ
  have hInf := isArchSectionR_archSecR b hb hbpos Z s
  have heq : globalSecR a Φ (archSecR m Z s) s γ = globalSecR a Φ (archSecR m Z s) s γ' :=
    globalSecR_lift a Φ hΦ hInf _ _ (normRep_rel γ)
  have hE : (botR γ').submatrix id (hNz γ) = 1 := by rw [botR_normRep]; exact normE_submatrix γ
  have hEq : normEQ q = botR γ' := (botR_normRep γ).symm
  -- the archimedean factor
  set A := ‖denR γ' Z‖
  have hA : ∀ p : Fin r × (Fin r ⊕ Fin r), c0 * ∏ w, max 1 |realEmb F w (botR γ' p.1 p.2)| ≤ A := by
    intro p
    rw [show A = ∏ w, ‖(denW γ' Z w).det‖ from norm_prod _ _, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun w _ => mul_nonneg (hc0 w).le (zero_le_one.trans (le_max_left _ _)))
      fun w _ => le_norm_det_denW w (hc w) hE p.1 p.2
  obtain ⟨p0⟩ : Nonempty (Fin r × (Fin r ⊕ Fin r)) := Fintype.card_pos_iff.mp hNn
  have hApos : 0 < A := lt_of_lt_of_le (mul_pos hc00 (Finset.prod_pos fun w _ =>
    zero_lt_one.trans_le (le_max_left _ _))) (hA p0)
  have hD : denR γ' Z ≠ 0 := norm_pos_iff.mp hApos
  -- the finite factor
  set H := ∏ᶠ v, htR v (locSpV v γ')
  have hHf : ∀ p : Fin r × (Fin r ⊕ Fin r),
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 ‖algebraMap F (v.adicCompletion F) (botR γ' p.1 p.2)‖ ≤ H :=
    fun p => cvFinprod_le (hasFiniteMulSupport_max_norm _) (hasFiniteMulSupport_htR' γ')
      (fun v => zero_le_one.trans (le_max_left _ _)) fun v => le_htR_of_normalized v hE p.1 p.2
  have hHm : ∀ e : F, 0 < ∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 ‖algebraMap F (v.adicCompletion F) e‖ :=
    fun e => finprod_pos_of (hasFiniteMulSupport_max_norm e) fun v => zero_lt_one.trans_le (le_max_left _ _)
  have hHpos : 0 < H := (hHm _).trans_le (hHf p0)
  -- the term
  have hterm : ‖globalSecR a Φ (archSecR m Z s) s γ'‖ ≤ Yd * K * (A * H) ^ (-τ) := by
    rw [globalSecR, norm_mul, norm_archSecR m hZ s γ' hD, Real.mul_rpow hApos.le hHpos.le]
    calc Yd * A ^ (-τ) * ‖finSecR a Φ γ' s‖ ≤ Yd * A ^ (-τ) * (K * H ^ (-τ)) :=
          mul_le_mul_of_nonneg_left (hK γ' s) (mul_nonneg hYd (Real.rpow_nonneg hApos.le _))
      _ = Yd * K * (A ^ (-τ) * H ^ (-τ)) := by ring
  set gp : Fin r × (Fin r ⊕ Fin r) → ℝ := fun p => κ * (‖eisDen ((1 : F), botR γ' p.1 p.2) (fun v => (zI v : ℂ))‖ *
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 ‖algebraMap F (v.adicCompletion F) (botR γ' p.1 p.2)‖)
  have hgp0 : ∀ p, 0 < gp p := fun p => mul_pos hκ (mul_pos (norm_pos_iff.mpr (eisDen_one_ne_zero _ zI)) (hHm _))
  have hgp : ∀ p, gp p ≤ A * H := by
    intro p
    have h1 : κ * ‖eisDen ((1 : F), botR γ' p.1 p.2) (fun v => (zI v : ℂ))‖ ≤ A := by
      refine le_trans ?_ (hA p)
      calc κ * ‖eisDen ((1 : F), botR γ' p.1 p.2) (fun v => (zI v : ℂ))‖
          ≤ κ * (2 ^ d * ∏ w, max 1 |realEmb F w (botR γ' p.1 p.2)|) :=
            mul_le_mul_of_nonneg_left (norm_eisDen_I_le _) hκ.le
        _ = c0 * ∏ w, max 1 |realEmb F w (botR γ' p.1 p.2)| := by
            simp only [κ]; field_simp
    calc gp p = (κ * ‖eisDen ((1 : F), botR γ' p.1 p.2) (fun v => (zI v : ℂ))‖) *
          ∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 ‖algebraMap F (v.adicCompletion F) (botR γ' p.1 p.2)‖ := by
            simp only [gp]; ring
      _ ≤ A * H := mul_le_mul h1 (hHf p) (hHm _).le hApos.le
  have hprod := rpow_neg_le_prod hNn hτ0 hgp0 hgp
  have hfac : ∏ p, gp p ^ (-τ / Nc) = κ ^ (-α * Nc) * G (normEQ q) := by
    have e1 : ∀ p, gp p ^ (-τ / Nc) = κ ^ (-α) * φ (botR γ' p.1 p.2) := fun p => by
      show (κ * _) ^ (-τ / Nc) = _
      rw [Real.mul_rpow hκ.le (mul_nonneg (norm_nonneg _) (finprod_nonneg fun v =>
        zero_le_one.trans (le_max_left _ _))), neg_div, ← hαdef]
    rw [Finset.prod_congr rfl fun p _ => e1 p, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← Real.rpow_natCast, ← Real.rpow_mul hκ.le, hEq]
  have hκτ : κ ^ (-α * Nc) = κ ^ (-τ) := by rw [neg_mul, hαN]
  show ‖globalSecR a Φ (archSecR m Z s) s γ‖ ≤ Yd * K * κ ^ (-τ) * (G ∘ normEQ) q
  rw [heq]
  calc ‖globalSecR a Φ (archSecR m Z s) s γ'‖ ≤ Yd * K * (A * H) ^ (-τ) := hterm
    _ ≤ Yd * K * ∏ p, gp p ^ (-τ / Nc) := mul_le_mul_of_nonneg_left hprod (mul_nonneg hYd hK0)
    _ = Yd * K * κ ^ (-τ) * (G ∘ normEQ) q := by rw [hfac, hκτ]; simp only [Function.comp]; ring

end QuadFormsKB.SiegelWeil.Forms
