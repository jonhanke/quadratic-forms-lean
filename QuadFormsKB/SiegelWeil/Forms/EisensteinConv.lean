/-
# Absolute convergence of the Siegel Eisenstein series of degree $r$ for $\operatorname{Re}s$ large
**Layer:** global over a totally real number field $F$.

**Setting.** $Q = \sum_{i<n}b_ix_i^2$ totally positive with $b_i \in \mathcal O_F$, $n = 2m$, the degree $r \ge 1$; a finite datum
$\Phi = (\Phi_v)_v$ ($\Phi_v = \mathbf 1_{L_v^r}$ for almost all $v$); $Z \in \mathbb H_r^d$; $f_\infty = $ `archSecR` (weight $m$).

**Results.**
* `exists_norm_finSecR_le` (**the finite section is bounded by the height**): $|f_f(\gamma, s)| \le K\,H_f(\gamma)^{-(\operatorname{Re}s+\rho_r)}$,
  $H_f(\gamma) = \prod_{v<\infty}\|\gamma_v\|_v$, every $\gamma \in \mathrm{Sp}_{2r}(F)$ and $s$ (`exists_norm_secSR_le` at the finitely many bad places,
  $C_v = 1$ at the good ones).
* `normRep` (**normalized representatives**): every coset $P(F)\gamma$ contains $\gamma' = m({}^tM_h)\gamma$ whose bottom block $E = M_h^{-1}M$ has
  the identity in the columns $h$; $q \mapsto E$ is injective on $P(F)\backslash\mathrm{Sp}_{2r}(F)$ (`normE_injective`).

Sources: Weil, Acta Math. 113 (1965), Ch. II [unverified]; Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1
[unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinBound
import QuadFormsKB.SiegelWeil.Forms.EisensteinArch
import QuadFormsKB.SiegelWeil.Forms.ThetaR

open Matrix NumberField IsDedekindDomain Filter
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData QuadFormsKB.WeilRep.Genus

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

/-! ### The finite section is bounded by the height -/

section Finite

variable {F : Type} [Field F] [NumberField F] {m r : ℕ} (a : Fin (2 * m) → Fˣ)
  (Φ : ∀ v : HeightOneSpectrum (𝓞 F), Sg (localDataV v) m r) (hΦ : ∀ᶠ v in cofinite, Φ v = oneSG v m r)

include a Φ hΦ in
lemma hasFiniteMulSupport_htR (γ : Sp r F) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => htR v (locSpV v γ) :=
  (badR_finite a Φ hΦ γ).subset fun v hv => by
    by_contra h
    exact hv (htR_eq_one_of_int v (isIntSp_of_not_badR a Φ h))

lemma norm_secRV_oneSG_int_le {v : HeightOneSpectrum (𝓞 F)} (hg : IsGoodV v (aV a v)) (k : Sp r (v.adicCompletion F))
    (hk : IsIntSp v k) : ‖secRV v (aV a v) (oneSG v m r) k‖ ≤ 1 := by
  rw [secRV_eq, weilRepSpV_oneSG_of_good v _ hg k hk]
  simp [coe_oneSG, oneG, ptG, Analysis.ballIndV]

include hΦ in
/-- **The finite section is bounded by the height** (every finite place, dyadic included): there is $K \ge 0$ with
$|f_f(\gamma, s)| \le K\,\big(\prod_{v<\infty}\|\gamma_v\|_v\big)^{-(\operatorname{Re}s+\rho_r)}$ for all $\gamma \in \mathrm{Sp}_{2r}(F)$ and $s$. -/
@[kb "kudla2008" "§1 (the standard section; the bound by the height) [unverified]; weil1965 Ch. II [unverified]"]
theorem exists_norm_finSecR_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (γ : Sp r F) (s : ℂ), ‖finSecR a Φ γ s‖ ≤
      K * (∏ᶠ v, htR v (locSpV v γ)) ^ (-(s.re + ((r : ℝ) + 1) / 2)) := by
  classical
  have hC : ∀ v : HeightOneSpectrum (𝓞 F), ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Sp r (v.adicCompletion F)) (s : ℂ),
      ‖secSR v (aV a v) (Φ v) g s‖ ≤ C * htR v g ^ (-(s.re + ((r : ℝ) + 1) / 2)) :=
    fun v => exists_norm_secSR_le v (aV a v) (Φ v)
  choose C hC0 hC using hC
  set S := badPlaces a 1 ∪ {v | Φ v ≠ oneSG v m r}
  have hS : S.Finite := (badPlaces_finite a 1).union hΦ
  set C' : HeightOneSpectrum (𝓞 F) → ℝ := fun v => if v ∈ S then C v else 1 with hC'
  have hC'0 : ∀ v, 0 ≤ C' v := fun v => by simp only [hC']; split_ifs; exacts [hC0 v, zero_le_one]
  have hC'fin : Function.HasFiniteMulSupport C' :=
    hS.subset fun v hv => by
      by_contra h; exact hv (show (if v ∈ S then C v else 1) = 1 from ite_eq_right_iff.mpr fun h' => absurd h' h)
  refine ⟨∏ᶠ v, C' v, finprod_nonneg hC'0, fun γ s => ?_⟩
  set τ : ℝ := s.re + ((r : ℝ) + 1) / 2
  have hle : ∀ v, ‖secSR v (aV a v) (Φ v) (locSpV v γ) s‖ ≤ C' v * htR v (locSpV v γ) ^ (-τ) := by
    intro v
    by_cases hv : v ∈ S
    · simp only [hC', hv, ite_true]; exact hC v _ s
    · simp only [hC', hv, ite_false, one_mul]
      have hv' : v ∉ badPlaces a 1 ∧ Φ v = oneSG v m r := by
        simp only [S, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hv; exact hv
      have hgood := isGoodV_of_not_bad (γ := 1) a hv'.1
      rw [hv'.2]
      have := norm_secSR_le_of_int_bound v (aV a v) (oneSG v m r) (C := 1)
        (fun k hk => norm_secRV_oneSG_int_le a hgood k hk) (locSpV v γ) s
      rw [one_mul] at this
      exact this
  have hH := hasFiniteMulSupport_htR a Φ hΦ γ
  have hHr : Function.HasFiniteMulSupport fun v => htR v (locSpV v γ) ^ (-τ) :=
    hH.subset fun v hv h => hv (by simp only at h ⊢; rw [h, Real.one_rpow])
  have hsec := hasFiniteMulSupport_secSR a Φ hΦ γ s
  have hnsec : Function.HasFiniteMulSupport fun v => ‖secSR v (aV a v) (Φ v) (locSpV v γ) s‖ :=
    hsec.subset fun v hv h => hv (by simp only at h ⊢; rw [h, norm_one])
  unfold finSecR
  rw [cvNorm_finprod hsec, ← cvFinprod_rpow hH (fun v => (htR_pos v _).le), ← finprod_mul_distrib hC'fin hHr]
  exact cvFinprod_le hnsec (hC'fin.mul hHr) (fun v => norm_nonneg _) hle

end Finite

/-! ### Normalized representatives of $P(k)\backslash\mathrm{Sp}_{2r}(k)$ -/

section Normalize

variable {k : Type*} [Field k] {r : ℕ}

/-- The bottom $r\times 2r$ block $(C\ D)$ of $g \in \mathrm{Sp}_{2r}(k)$. -/
def botR (g : Sp r k) : Matrix (Fin r) (Fin r ⊕ Fin r) k :=
  fun i x => (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) (Sum.inr i) x

lemma botR_mul (g g' : Sp r k) : botR (g * g') = botR g * (g' : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) := by
  funext i x; rfl

lemma exists_minor_ne_zero_botR (g : Sp r k) : ∃ h : Fin r → Fin r ⊕ Fin r, ((botR g).submatrix id h).det ≠ 0 := by
  set N : Matrix (Fin r ⊕ Fin r) (Fin r) k :=
    fun x j => ((g⁻¹ : Sp r k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) x (Sum.inr j)
  have hBM : botR g * N = 1 := by
    have : (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) * ((g⁻¹ : Sp r k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) = 1 := by
      rw [← Submonoid.coe_mul, mul_inv_cancel]; rfl
    funext i j
    have h := congrFun (congrFun this (Sum.inr i)) (Sum.inr j)
    rw [mul_apply] at h
    rw [mul_apply]
    simpa [botR, N, Matrix.one_apply] using h
  have h1 := det_mul_rect (botR g) N
  rw [hBM, det_one] at h1
  have hs : (∑ h : Fin r → Fin r ⊕ Fin r, (∏ j, N (h j) j) * ((botR g).submatrix id h).det) ≠ 0 := by
    rw [← h1]; exact one_ne_zero
  obtain ⟨h, -, hh⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  exact ⟨h, right_ne_zero_of_mul hh⟩

/-- A column choice $h$ with $\det M_h \ne 0$ for the bottom block $M$ of $g$. -/
def hNz (g : Sp r k) : Fin r → Fin r ⊕ Fin r := (exists_minor_ne_zero_botR g).choose

lemma det_hNz_ne_zero (g : Sp r k) : ((botR g).submatrix id (hNz g)).det ≠ 0 :=
  (exists_minor_ne_zero_botR g).choose_spec

/-- **The normalized bottom block** $E = M_h^{-1}M$ (identity in the columns $h$). -/
def normE (g : Sp r k) : Matrix (Fin r) (Fin r ⊕ Fin r) k := ((botR g).submatrix id (hNz g))⁻¹ * botR g

lemma normE_submatrix (g : Sp r k) : (normE g).submatrix id (hNz g) = 1 := by
  rw [normE, ← mul_selN, Matrix.mul_assoc, mul_selN, nonsing_inv_mul _ (det_hNz_ne_zero g).isUnit]

/-- The block $M_h$ as an element of $\mathrm{GL}_r(k)$, transposed: $A = {}^tM_h$, so $m(A)$ has lower right block $M_h^{-1}$. -/
def normA (g : Sp r k) : GL (Fin r) k :=
  ((Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [det_transpose]; exact (det_hNz_ne_zero g).isUnit) :
      IsUnit ((botR g).submatrix id (hNz g))ᵀ).unit

/-- **The normalized representative** $m({}^tM_h)\,g$ of the coset $P(k)g$. -/
def normRep (g : Sp r k) : Sp r k := spM (normA g) * g

lemma botR_spM_mul (A : GL (Fin r) k) (g : Sp r k) :
    botR (spM A * g) = (((A⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k))ᵀ * botR g := by
  funext i x
  simp only [botR, Submonoid.coe_mul, spM_coe, mul_apply, Fintype.sum_sum_type, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]

lemma botR_normRep (g : Sp r k) : botR (normRep g) = normE g := by
  rw [normRep, botR_spM_mul, normE]
  congr 1
  have e : ((normA g)⁻¹ : GL (Fin r) k) = (((botR g).submatrix id (hNz g))ᵀ)⁻¹ := by
    rw [Matrix.coe_units_inv]; rfl
  rw [e, transpose_nonsing_inv, transpose_transpose]

lemma normRep_rel (g : Sp r k) : QuotientGroup.rightRel (siegelP r k) g (normRep g) := by
  rw [QuotientGroup.rightRel_apply, normRep, mul_inv_cancel_right]
  exact spM_mem_siegelP _

/-- Two symplectic matrices whose bottom blocks differ by an invertible left factor lie in the same coset of $P(k)$. -/
lemma rightRel_of_botR_eq {g g' : Sp r k} (D : Matrix (Fin r) (Fin r) k) (h : botR g' = D * botR g) :
    QuotientGroup.rightRel (siegelP r k) g g' := by
  rw [QuotientGroup.rightRel_apply]
  show blockC _ = 0
  have hb : botR (g' * g⁻¹) = D * botR (1 : Sp r k) := by
    rw [botR_mul, h, Matrix.mul_assoc, ← botR_mul, mul_inv_cancel]
  funext i j
  have := congrFun (congrFun hb i) (Sum.inl j)
  show botR (g' * g⁻¹) i (Sum.inl j) = 0
  rw [this, mul_apply]
  exact Finset.sum_eq_zero fun l _ => by simp [botR]

lemma rightRel_of_normE_eq {g g' : Sp r k} (h : normE g = normE g') : QuotientGroup.rightRel (siegelP r k) g g' := by
  refine rightRel_of_botR_eq (((botR g').submatrix id (hNz g')) * ((botR g).submatrix id (hNz g))⁻¹) ?_
  have h' : botR g' = ((botR g').submatrix id (hNz g')) * normE g' := by
    rw [normE, ← Matrix.mul_assoc, mul_nonsing_inv _ (det_hNz_ne_zero g').isUnit, Matrix.one_mul]
  calc botR g' = ((botR g').submatrix id (hNz g')) * normE g' := h'
    _ = ((botR g').submatrix id (hNz g')) * normE g := by rw [h]
    _ = _ := by rw [normE, Matrix.mul_assoc]

/-- **The normalized block of a coset** (through the representative `q.out`); injective (`normEQ_injective`). -/
def normEQ (q : PQuot r k) : Matrix (Fin r) (Fin r ⊕ Fin r) k := normE q.out

lemma normEQ_injective : Function.Injective (normEQ (r := r) (k := k)) := by
  intro q q' h
  rw [← Quotient.out_eq q, ← Quotient.out_eq q']
  exact Quotient.sound (rightRel_of_normE_eq h)

/-- The entries of $E$ are minors: $E_{ix} = \det E_{h[i\mapsto x]}$ when $E_h = 1$. -/
lemma entry_eq_minor {E : Matrix (Fin r) (Fin r ⊕ Fin r) k} {h : Fin r → Fin r ⊕ Fin r} (hE : E.submatrix id h = 1)
    (i : Fin r) (x : Fin r ⊕ Fin r) : E i x = (E.submatrix id (Function.update h i x)).det := by
  have := inv_submatrix_mul_apply E h i x
  rw [hE, inv_one, Matrix.one_mul, det_one, div_one] at this
  exact this

end Normalize

/-! ### The local height of a normalized block -/

section LocalHeight

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {r : ℕ}

lemma bottomRows_locSpV (γ : Sp r F) :
    bottomRows v (locSpV v γ) = (botR γ).map (algebraMap F (v.adicCompletion F)) := by
  funext i x; rfl

/-- **The local height bounds the entries of a normalized block**: if the bottom block $E$ of $\gamma$ has $E_h = 1$, then
$\|\gamma_v\|_v \ge \max(1, |E_{ix}|_v)$ for all $i, x$. -/
theorem le_htR_of_normalized {γ : Sp r F} {h : Fin r → Fin r ⊕ Fin r} (hE : (botR γ).submatrix id h = 1)
    (i : Fin r) (x : Fin r ⊕ Fin r) :
    max 1 ‖algebraMap F (v.adicCompletion F) (botR γ i x)‖ ≤ htR v (locSpV v γ) := by
  rw [htR_eq_maxMinor]
  have hmin : ∀ h' : Fin r → Fin r ⊕ Fin r, ‖algebraMap F (v.adicCompletion F) ((botR γ).submatrix id h').det‖ ≤
      ‖(maxBlock v (locSpV v γ)).det‖ := by
    intro h'
    have := norm_minor_le_hMax v (locSpV v γ) h'
    rw [bottomRows_locSpV] at this
    calc ‖algebraMap F (v.adicCompletion F) ((botR γ).submatrix id h').det‖
        = ‖(((botR γ).map (algebraMap F (v.adicCompletion F))).submatrix id h').det‖ := by
          rw [RingHom.map_det]; rfl
      _ ≤ _ := this
      _ = _ := by rw [maxBlock, bottomRows_locSpV]
  refine max_le ?_ ?_
  · have := hmin h
    rwa [hE, det_one, map_one, norm_one] at this
  · rw [entry_eq_minor hE i x]; exact hmin _

end LocalHeight

/-! ### The archimedean section in absolute value -/

section ArchNorm

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {r : ℕ}

lemma det_im_pos {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) (v : InfinitePlace F) :
    0 < ((Z v).map Complex.im).det := (hZ v).2.det_pos

/-- $|f_\infty(\gamma g_Z, s)| = \prod_v\det(\operatorname{Im}Z_v)^{(\sigma+\rho_r)/2}\,|j(\gamma, Z)|^{-(\sigma+\rho_r)}$ when $j(\gamma, Z) \ne 0$. -/
lemma norm_archSecR (m : ℕ) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) (s : ℂ)
    (γ : Sp r F) (hD : denR γ Z ≠ 0) :
    ‖archSecR m Z s γ‖ = (∏ v, ((Z v).map Complex.im).det ^ ((s.re + ((r : ℝ) + 1) / 2) / 2)) *
      ‖denR γ Z‖ ^ (-(s.re + ((r : ℝ) + 1) / 2)) := by
  have hDn : 0 < ‖denR γ Z‖ := norm_pos_iff.mpr hD
  unfold archSecR
  rw [norm_mul, norm_mul, norm_prod, norm_zpow, Complex.norm_cpow_eq_rpow_re_of_pos hDn]
  have hy : ∀ v, ‖((((Z v).map Complex.im).det : ℝ) : ℂ) ^ ((s + rhoR r) / 2)‖ =
      ((Z v).map Complex.im).det ^ ((s.re + ((r : ℝ) + 1) / 2) / 2) := fun v => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (det_im_pos hZ v)]; congr 1; simp [rhoR]
  simp_rw [hy]
  rw [mul_assoc]
  congr 1
  have e : ((m : ℂ) - (s + rhoR r)).re = (m : ℝ) - (s.re + ((r : ℝ) + 1) / 2) := by simp [rhoR]
  rw [e, ← Real.rpow_intCast, ← Real.rpow_add hDn]
  congr 1; push_cast; ring

end ArchNorm

/-! ### Elementary inequalities -/

/-- If $y \ge g_j > 0$ for all $j$ in a finite set of size $N > 0$, then $y^{-\tau} \le \prod_jg_j^{-\tau/N}$ ($\tau \ge 0$). -/
lemma rpow_neg_le_prod {ι : Type*} [Fintype ι] (hN : 0 < Fintype.card ι) {y τ : ℝ} {g : ι → ℝ} (hτ : 0 ≤ τ)
    (hg : ∀ j, 0 < g j) (hy : ∀ j, g j ≤ y) :
    y ^ (-τ) ≤ ∏ j, g j ^ (-τ / Fintype.card ι) := by
  obtain ⟨j0⟩ : Nonempty ι := Fintype.card_pos_iff.mp hN
  have hy0 : 0 < y := (hg j0).trans_le (hy j0)
  have hNr : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  have e : y ^ (-τ) = ∏ _j : ι, y ^ (-τ / Fintype.card ι) := by
    rw [Finset.prod_const, Finset.card_univ, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    congr 1; field_simp
  rw [e]
  refine Finset.prod_le_prod₀ (fun j _ => (Real.rpow_pos_of_pos hy0 _).le) fun j _ => ?_
  exact Real.rpow_le_rpow_of_nonpos (hg j) (hy j) (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hτ) hNr.le)

lemma norm_add_I_le (t : ℝ) : ‖(t : ℂ) + Complex.I‖ ≤ 2 * max 1 |t| := by
  calc ‖(t : ℂ) + Complex.I‖ ≤ ‖(t : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
    _ = |t| + 1 := by rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]
    _ ≤ 2 * max 1 |t| := by linarith [le_max_left 1 |t|, le_max_right 1 |t|]

end QuadFormsKB.SiegelWeil.Forms
