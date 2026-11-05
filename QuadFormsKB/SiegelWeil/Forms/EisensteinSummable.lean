/-
# Absolute convergence of the Siegel Eisenstein series of degree $r$
**Layer:** global over a totally real number field $F$ of degree $d$.

**Setting.** $Q = \sum_{i<n}b_ix_i^2$ totally positive with $b_i \in \mathcal O_F$, $n = 2m$; the degree $r \ge 1$; a finite datum
$\Phi = (\Phi_v)_v$, $\Phi_v \in S(V_v^r)$ arbitrary, $\Phi_v = \mathbf 1_{L_v^r}$ for almost all $v$; $Z \in \mathbb H_r^d$; the archimedean
section of weight $m$ (`archSecR`); $\sigma = \operatorname{Re}s$, $\rho_r = \frac{r+1}2$.

**Result.** **`summable_norm_globalSecR`**: for $\sigma + \rho_r > 4r^2$ the series
$$E(g_Z, s, \Phi) = \sum_{\gamma\in P(F)\backslash\mathrm{Sp}_{2r}(F)}f_\infty(\gamma g_Z, s)\prod_{v<\infty}f_v(\gamma_v, s)$$
converges absolutely; `eisensteinR_hasSum`: `eisensteinR` is its (absolutely convergent) sum.

*Proof.* Put $\tau = \sigma + \rho_r$ and $N = 2r^2$. Each coset has a representative $\gamma$ whose bottom block $E$ is the identity in some
columns $h$ (`normRep`), and $q \mapsto E$ is injective (`normEQ_injective`). For every entry $e = E_{ix}$:
$\|\gamma_v\|_v \ge \max(1, |e|_v)$ at every finite $v$ (`le_htR_of_normalized`) and $|\det(\sigma_w(C)Z_w + \sigma_w(D))| \ge c_w\max(1, |\sigma_w e|)$
at every real place $w$ (`exists_norm_det_CZD_ge`). With $|f_f(\gamma, s)| \le KH_f(\gamma)^{-\tau}$ (`exists_norm_finSecR_le`) and
$|f_\infty(\gamma g_Z, s)| = c_Y|j(\gamma, Z)|^{-\tau}$ (`norm_archSecR`), the term is at most a constant times
$\prod_{i,x}\big(|N(i + E_{ix})|\prod_v\max(1, |E_{ix}|_v)\big)^{-\tau/N}$, and $\sum_{u\in F}\big(|N(i+u)|\prod_v\max(1,|u|_v)\big)^{-\alpha} < \infty$ for
$\alpha = \tau/N > 2$ (`summable_heightZeta`). The range $\sigma + \rho_r > 4r^2$ is crude; the sharp range $\sigma > \rho_r$ (Godement) is not
proved here.

Sources: Weil, Acta Math. 113 (1965), Ch. II [unverified]; Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1
[unverified]; Shimura, *On Eisenstein series*, Duke Math. J. 50 (1983) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinConv
import QuadFormsKB.SiegelWeil.Forms.EisensteinArchBound
import QuadFormsKB.SiegelWeil.Forms.EisensteinHeightZeta
import QuadFormsKB.SiegelWeil.Forms.BruhatBigCell

open Matrix NumberField IsDedekindDomain Filter
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData QuadFormsKB.WeilRep.Genus QuadFormsKB.Analysis

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

lemma fromCols_blockC_blockD (γ : Sp r F) : Matrix.fromCols (blockC γ) (blockD γ) = botR γ := by
  funext i x
  rcases x with j | j <;> rfl

/-- The real bottom blocks at a real place $w$. -/
abbrev blockCw (γ : Sp r F) (w : InfinitePlace F) : Matrix (Fin r) (Fin r) ℝ := (blockC γ).map (realEmb F w)
abbrev blockDw (γ : Sp r F) (w : InfinitePlace F) : Matrix (Fin r) (Fin r) ℝ := (blockD γ).map (realEmb F w)

lemma denW_eq (γ : Sp r F) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (w : InfinitePlace F) :
    denW γ Z w = (blockCw γ w).map (↑) * Z w + (blockDw γ w).map (↑) := by
  simp only [denW, Matrix.map_map]; rfl

/-- **The archimedean lower bound at a normalized representative**: if $E_h = 1$ for the bottom block $E$ of $\gamma$, then
$|\det(\sigma_w(C)Z_w + \sigma_w(D))| \ge c_w\max(1, |\sigma_w(E_{ix})|)$. -/
lemma le_norm_det_denW {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (w : InfinitePlace F)
    {c : ℝ} (hc : ∀ (C D : Matrix (Fin r) (Fin r) ℝ), C * Dᵀ = D * Cᵀ →
      ∀ h : Fin r → Fin r ⊕ Fin r, (Matrix.fromCols C D).submatrix id h = 1 →
        ∀ (i : Fin r) (x : Fin r ⊕ Fin r),
          c * max 1 |Matrix.fromCols C D i x| ≤ ‖(C.map (↑) * Z w + D.map (↑) : Matrix (Fin r) (Fin r) ℂ).det‖)
    {γ : Sp r F} {h : Fin r → Fin r ⊕ Fin r} (hE : (botR γ).submatrix id h = 1) (i : Fin r) (x : Fin r ⊕ Fin r) :
    c * max 1 |realEmb F w (botR γ i x)| ≤ ‖(denW γ Z w).det‖ := by
  have hfc : Matrix.fromCols (blockCw γ w) (blockDw γ w) = (botR γ).map (realEmb F w) := by
    rw [← fromCols_blockC_blockD]; funext i x; rcases x with j | j <;> rfl
  have hL : blockCw γ w * (blockDw γ w)ᵀ = blockDw γ w * (blockCw γ w)ᵀ := by
    simp only [blockCw, blockDw, ← transpose_map, ← Matrix.map_mul]
    rw [blockC_mul_blockD_transpose]
  have hEw : (Matrix.fromCols (blockCw γ w) (blockDw γ w)).submatrix id h = 1 := by
    rw [hfc, show ((botR γ).map (realEmb F w)).submatrix id h = ((botR γ).submatrix id h).map (realEmb F w) from rfl,
      hE, Matrix.map_one _ (map_zero _) (map_one _)]
  have := hc _ _ hL h hEw i x
  rw [hfc, Matrix.map_apply, ← denW_eq] at this
  exact this

/-! ### Finite products of reals -/

lemma finprod_pos_of {ι : Type*} {f : ι → ℝ} (hf : Function.HasFiniteMulSupport f) (h : ∀ i, 0 < f i) :
    0 < ∏ᶠ i, f i := by
  have hf' : (Function.mulSupport f).Finite := hf
  rw [finprod_eq_prod_of_mulSupport_subset f (s := hf'.toFinset) (fun i hi => hf'.mem_toFinset.mpr hi)]
  exact Finset.prod_pos fun i _ => h i

lemma hasFiniteMulSupport_max_norm (e : F) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => max 1 ‖algebraMap F (v.adicCompletion F) e‖ :=
  (HeightOneSpectrum.Support.finite (𝓞 F) e).subset fun v hv => by
    by_contra h
    apply hv
    have := (norm_le_one_iff_valued v).mpr (valued_le_one_of_not_mem_support h)
    simp only [max_eq_left this]

lemma hasFiniteMulSupport_htR' (γ : Sp r F) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => htR v (locSpV v γ) :=
  (Set.finite_iUnion fun x => Set.finite_iUnion fun y =>
    HeightOneSpectrum.Support.finite (𝓞 F) ((γ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) x y)).subset fun v hv => by
    by_contra h
    apply hv
    simp only [Set.mem_iUnion, not_exists] at h
    refine htR_eq_one_of_int v fun x y => ?_
    rw [locSp_coe, Matrix.map_apply]
    exact (norm_le_one_iff_valued v).mpr (valued_le_one_of_not_mem_support (h x y))

lemma norm_eisDen_I_le (e : F) :
    ‖eisDen ((1 : F), e) (fun _ : InfinitePlace F => ((UpperHalfPlane.I : UpperHalfPlane) : ℂ))‖ ≤
      2 ^ Fintype.card (InfinitePlace F) * ∏ w, max 1 |realEmb F w e| := by
  rw [eisDen, norm_prod, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun w _ => norm_nonneg _) fun w _ => ?_
  rw [map_one, Complex.ofReal_one, one_mul, UpperHalfPlane.coe_I, add_comm]
  exact norm_add_I_le _

/-! ### The convergence theorem -/

/-- **Absolute convergence of the Siegel Eisenstein series of degree $r$ for $\operatorname{Re}s$ large**: for $F$ totally real,
$Q = \sum_ib_ix_i^2$ totally positive over $\mathcal O_F$, every finite datum $\Phi$, $Z \in \mathbb H_r^d$, $r \ge 1$ and
$\operatorname{Re}s + \frac{r+1}2 > 4r^2$, the terms $f(\gamma, s) = f_\infty(\gamma g_Z, s)f_f(\gamma, s)$ of $E(g_Z, s, \Phi)$ are absolutely
summable over $P(F)\backslash\mathrm{Sp}_{2r}(F)$ (through any representative `q.out`). -/
@[kb "weil1965" "Ch. II (convergence of the Eisenstein series for Re s large) [unverified]; kudla2008 §1 [unverified]"]
theorem summable_norm_globalSecR (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (Φ : ∀ v : HeightOneSpectrum (𝓞 F), Sg (localDataV v) m r) (hΦ : ∀ᶠ v in cofinite, Φ v = oneSG v m r)
    (hr : 1 ≤ r) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) {s : ℂ}
    (hs : 4 * (r : ℝ) ^ 2 < s.re + ((r : ℝ) + 1) / 2) :
    Summable fun q : PQuot r F => ‖globalSecR (unitsOfInt b hb) Φ (archSecR m Z s) s q.out‖ := by
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
  obtain ⟨K, hK0, hK⟩ := exists_norm_finSecR_le a Φ hΦ
  have hcw := fun w => exists_norm_det_CZD_ge (hZ w)
  choose c hc0 hc using hcw
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
  set c0 : ℝ := ∏ w, c w
  have hc00 : 0 < c0 := Finset.prod_pos fun w _ => hc0 w
  set d := Fintype.card (InfinitePlace F)
  set Yd : ℝ := ∏ v, ((Z v).map Complex.im).det ^ (τ / 2)
  have hYd : 0 ≤ Yd := Finset.prod_nonneg fun v _ => Real.rpow_nonneg (det_im_pos hZ v).le _
  set κ : ℝ := c0 / 2 ^ d
  have hκ : 0 < κ := div_pos hc00 (by positivity)
  refine ((hG.comp_injective normEQ_injective).mul_left (Yd * K * κ ^ (-α * Nc))).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun q => ?_
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
  rw [heq]
  calc ‖globalSecR a Φ (archSecR m Z s) s γ'‖ ≤ Yd * K * (A * H) ^ (-τ) := hterm
    _ ≤ Yd * K * ∏ p, gp p ^ (-τ / Nc) := mul_le_mul_of_nonneg_left hprod (mul_nonneg hYd hK0)
    _ = Yd * K * κ ^ (-α * Nc) * (G ∘ normEQ) q := by rw [hfac]; simp only [Function.comp]; ring

/-- **The Siegel Eisenstein series of degree $r$ converges absolutely for $\operatorname{Re}s + \frac{r+1}2 > 4r^2$** (same setting as
`summable_norm_globalSecR`): `eisensteinR` $= \sum_{q\in P(F)\backslash\mathrm{Sp}_{2r}(F)}f(q.\mathrm{out}, s)$, an absolutely convergent sum. -/
@[kb "weil1965" "Ch. II (convergence of the Eisenstein series for Re s large) [unverified]; kudla2008 §1 [unverified]"]
theorem eisensteinR_hasSum (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (Φ : ∀ v : HeightOneSpectrum (𝓞 F), Sg (localDataV v) m r) (hΦ : ∀ᶠ v in cofinite, Φ v = oneSG v m r)
    (hr : 1 ≤ r) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) {s : ℂ}
    (hs : 4 * (r : ℝ) ^ 2 < s.re + ((r : ℝ) + 1) / 2) :
    HasSum (fun q : PQuot r F => globalSecR (unitsOfInt b hb) Φ (archSecR m Z s) s q.out)
      (eisensteinR (unitsOfInt b hb) Φ hΦ (isArchSectionR_archSecR b hb hbpos Z s)) := by
  have hsum := (summable_norm_globalSecR b hb hbpos Φ hΦ hr hZ hs).of_norm
  have e : ∀ q : PQuot r F, Quotient.lift (globalSecR (unitsOfInt b hb) Φ (archSecR m Z s) s)
      (globalSecR_lift (unitsOfInt b hb) Φ hΦ (isArchSectionR_archSecR b hb hbpos Z s)) q =
        globalSecR (unitsOfInt b hb) Φ (archSecR m Z s) s q.out := by
    intro q
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  unfold eisensteinR
  simp only [e]
  exact hsum.hasSum

end QuadFormsKB.SiegelWeil.Forms
