/-
# (5.5) at each real place of $F$: $\beta_w(m)$ as Siegel's volume limit

**Layer:** real forms, then number field ($F$ a number field, $w$ = `RealPlace F`, $\sigma_w$ = `realEmb w`,
$Q_w = \sigma_w(Q)$ = `realForm Q w`, $D_w = \det H_w/2^n$ = `gramDetNF Q w`).
**Proves** Hanke 2004, (5.1) and (5.5), pp. 368–369, at every real place: for $Q$ positive definite at $w$, $n \ge 1$
and $\sigma_w(m) > 0$,
$$\lim_{\varepsilon \to 0^+}\frac{\mathrm{Vol}\{\vec x \in \mathbb R^n : \sigma_w(m) < Q_w(\vec x) \le \sigma_w(m) + \varepsilon\}}{\varepsilon}
= \frac{n\,\omega_n}{2}D_w^{-1/2}\sigma_w(m)^{(n-2)/2} = \beta_w(m)$$
(`tendsto_volume_shell_div_realPlace`), and for $F$ with $Q$ totally positive definite and $m$ totally positive,
`betaInfNF` $= \prod_w \beta_w(m)$ is the product of these limits (`tendsto_prod_volume_shell_div`,
`betaInfNF_eq_prod_limUnder`).

The ℚ/ℝ version `Siegel.tendsto_volume_shell_div` is stated for integral forms; here it is generalized to any positive
definite **real** form (`tendsto_volume_shell_div_real`, same proof via `exists_sqrt_factor`), which is what $Q_w$ is,
and the integral version is recovered from it (`tendsto_volume_shell_div_of_real`).
-/
import QuadFormsKB.Siegel.Archimedean
import QuadFormsKB.Siegel.NFMainTerm

open Matrix MeasureTheory Filter Topology NumberField

noncomputable section

namespace QuadFormsKB.Siegel

variable {n : ℕ}

/-! ### Real forms -/

section Real

/-- **The Gram matrix** $A = H/2$ of a real form: $Q(\vec x) = \vec x^{\mathsf T}A\vec x$ (`eval_real_eq_gramR`). -/
def gramMatrixR (Q : QuadForm ℝ n) : Matrix (Fin n) (Fin n) ℝ := (1 / 2 : ℝ) • Q.hessian

/-- **$D = \det(H/2) = \det H/2^n$** for a real form (Hanke's determinant; `gramDet`, `gramDetNF` conventions). -/
def gramDetR (Q : QuadForm ℝ n) : ℝ := Q.hessian.det / 2 ^ n

/-- **Positive definite real form:** $Q(\vec x) > 0$ for $\vec x \in \mathbb R^n \setminus 0$. -/
def IsPosDefR (Q : QuadForm ℝ n) : Prop := ∀ x : Fin n → ℝ, x ≠ 0 → 0 < Q.eval x

/-- **The (5.5) value for a real form:** $\frac{n\,\omega_n}{2}D^{-1/2}m^{(n-2)/2}$ (as `betaInf`). -/
def betaInfR (Q : QuadForm ℝ n) (m : ℝ) : ℝ :=
  n * unitBallVol n * gramDetR Q ^ (-(1 / 2 : ℝ)) / 2 * m ^ (((n : ℝ) - 2) / 2)

theorem eval_smul_real (Q : QuadForm ℝ n) (c : ℝ) (x : Fin n → ℝ) : Q.eval (c • x) = c ^ 2 * Q.eval x := by
  simp only [QuadForm.evalIn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem eval_real_eq_gramR (Q : QuadForm ℝ n) (x : Fin n → ℝ) : Q.eval x = x ⬝ᵥ (gramMatrixR Q *ᵥ x) := by
  have h := QuadForm.polar_eq_hessian ℝ Q x x
  rw [← two_smul ℝ x, show Q.evalIn ℝ ((2 : ℝ) • x) = Q.eval ((2 : ℝ) • x) from rfl, eval_smul_real] at h
  have h2 : Q.hessian.map ⇑(algebraMap ℝ ℝ) = Q.hessian := by ext; rfl
  rw [h2] at h
  rw [gramMatrixR, smul_mulVec, dotProduct_smul, smul_eq_mul]
  change 2 ^ 2 * Q.eval x - Q.eval x - Q.eval x = _ at h
  linear_combination (1 / 2 : ℝ) * h

theorem gramMatrixR_isHermitian (Q : QuadForm ℝ n) : (gramMatrixR Q).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, gramMatrixR, transpose_smul]
  congr 1
  simp [QuadForm.hessian, Matrix.transpose_add, add_comm]

theorem gramDetR_eq_det (Q : QuadForm ℝ n) : gramDetR Q = (gramMatrixR Q).det := by
  rw [gramDetR, gramMatrixR, det_smul, Fintype.card_fin, div_eq_mul_inv, mul_comm, one_div, inv_pow]

theorem continuous_eval_real (Q : QuadForm ℝ n) : Continuous fun x : Fin n → ℝ => Q.eval x := by
  show Continuous fun x : Fin n → ℝ => Q.evalIn ℝ x
  unfold QuadForm.evalIn
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  split_ifs <;> fun_prop

theorem gramDetR_pos {Q : QuadForm ℝ n} (hQ : IsPosDefR Q) : 0 < gramDetR Q := by
  obtain ⟨S, -, h, -⟩ := exists_sqrt_factor (gramMatrixR Q) (gramMatrixR_isHermitian Q)
    (fun x hx => by rw [← eval_real_eq_gramR]; exact hQ x hx)
  rwa [gramDetR_eq_det]

/-- **Volume of the solid ellipsoid of a positive definite real form** ($n \ge 1$, $t \ge 0$):
$\mathrm{Vol}\{\vec x : Q(\vec x) \le t\} = \omega_n D^{-1/2}t^{n/2}$. Same proof as `volume_setOf_evalIn_le`. -/
theorem volume_setOf_eval_le_real {Q : QuadForm ℝ n} (hQ : IsPosDefR Q) (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    volume {x : Fin n → ℝ | Q.eval x ≤ t} =
      ENNReal.ofReal (unitBallVol n * gramDetR Q ^ (-(1 / 2 : ℝ)) * t ^ ((n : ℝ) / 2)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨S, hS, hdetpos, hdetS⟩ := exists_sqrt_factor (gramMatrixR Q) (gramMatrixR_isHermitian Q)
    (fun x hx => by rw [← eval_real_eq_gramR]; exact hQ x hx)
  have hS0 : S.det ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hdetS
    exact (Real.sqrt_pos.mpr hdetpos).ne' hdetS.symm
  set s : Set (Fin n → ℝ) := {y | (∑ i, |y i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ Real.sqrt t}
  have hset : {x : Fin n → ℝ | Q.eval x ≤ t} = (Matrix.toLin' S) ⁻¹' s := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Matrix.toLin'_apply, s]
    rw [eval_real_eq_gramR, hS]
    have e : (∑ i, |(S *ᵥ x) i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = Real.sqrt (∑ i, (S *ᵥ x) i ^ 2) := by
      rw [Real.sqrt_eq_rpow]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.rpow_two, sq_abs]
    rw [e, Real.sqrt_le_sqrt_iff ht]
  rw [hset, MeasureTheory.Measure.addHaar_preimage_linearMap _ (by rwa [LinearMap.det_toLin']),
    LinearMap.det_toLin', MeasureTheory.volume_sum_rpow_le (Fin n) (by norm_num : (1 : ℝ) ≤ 2),
    Fintype.card_fin, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hG : 2 * Real.Gamma (2⁻¹ + 1) = Real.sqrt Real.pi := by
    rw [← one_div]; exact two_mul_Gamma_three_halves
  have hD : 0 ≤ gramDetR Q := by rw [gramDetR_eq_det]; exact hdetpos.le
  have ht' : Real.sqrt t ^ n = t ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht]
    ring_nf
  have hD' : gramDetR Q ^ (-(2⁻¹ : ℝ)) = (Real.sqrt (gramDetR Q))⁻¹ := by
    rw [Real.rpow_neg hD, Real.sqrt_eq_rpow, one_div]
  rw [abs_inv, hdetS, ← gramDetR_eq_det, unitBallVol_eq hn, one_div, hG, hD', ht']
  ring

/-- **Siegel's archimedean density for a positive definite real form** (Hanke 2004, (5.1), (5.5), pp. 368–369;
Siegel, Hilfssatz 26): for $n \ge 1$ and $m > 0$,
$\mathrm{Vol}\{m < Q \le m + \varepsilon\}/\varepsilon \to \frac{n\,\omega_n}{2}D^{-1/2}m^{(n-2)/2}$ as $\varepsilon \to 0^+$.
Generalizes `tendsto_volume_shell_div` from integral to real forms (same proof). -/
@[kb "hanke2004" "(5.1), (5.5), pp. 368–369 (real form)"]
theorem tendsto_volume_shell_div_real {Q : QuadForm ℝ n} (hQ : IsPosDefR Q) (hn : 1 ≤ n) {m : ℝ}
    (hm : 0 < m) :
    Tendsto (fun ε => (volume {x : Fin n → ℝ | Q.eval x ∈ Set.Ioc m (m + ε)}).toReal / ε)
      (𝓝[>] 0) (𝓝 (betaInfR Q m)) := by
  set K := unitBallVol n * gramDetR Q ^ (-(1 / 2 : ℝ))
  have hK : 0 ≤ K := by
    have : 0 ≤ unitBallVol n := ENNReal.toReal_nonneg
    have : 0 ≤ gramDetR Q ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (gramDetR_pos hQ).le _
    positivity
  set f : ℝ → ℝ := fun t => K * t ^ ((n : ℝ) / 2)
  have hf : HasDerivAt f (K * ((n : ℝ) / 2 * m ^ ((n : ℝ) / 2 - 1))) m :=
    (Real.hasDerivAt_rpow_const (Or.inl hm.ne')).const_mul K
  have heq : betaInfR Q m = K * ((n : ℝ) / 2 * m ^ ((n : ℝ) / 2 - 1)) := by
    rw [betaInfR, show ((n : ℝ) / 2 - 1) = ((n : ℝ) - 2) / 2 by ring]
    ring
  rw [heq]
  refine hf.tendsto_slope_zero_right.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 0 < ε := hε
  have hsub : {x : Fin n → ℝ | Q.eval x ≤ m} ⊆ {x | Q.eval x ≤ m + ε} :=
    fun x (hx : Q.eval x ≤ m) => show Q.eval x ≤ m + ε by linarith
  have hdiff : {x : Fin n → ℝ | Q.eval x ∈ Set.Ioc m (m + ε)} =
      {x | Q.eval x ≤ m + ε} \ {x | Q.eval x ≤ m} := by
    ext x; simp [Set.mem_Ioc, and_comm]
  have hmeas : MeasurableSet {x : Fin n → ℝ | Q.eval x ≤ m} :=
    (isClosed_le (continuous_eval_real Q) continuous_const).measurableSet
  have hmono : m ^ ((n : ℝ) / 2) ≤ (m + ε) ^ ((n : ℝ) / 2) :=
    Real.rpow_le_rpow hm.le (by linarith) (by positivity)
  rw [hdiff, measure_sdiff hsub hmeas.nullMeasurableSet (by
      rw [volume_setOf_eval_le_real hQ hn hm.le]; exact ENNReal.ofReal_ne_top),
    volume_setOf_eval_le_real hQ hn (by linarith), volume_setOf_eval_le_real hQ hn hm.le,
    ← ENNReal.ofReal_sub _ (by positivity), ENNReal.toReal_ofReal (by nlinarith)]
  simp only [f, smul_eq_mul]
  field_simp
  ring

/-- **The integral case recovered:** for an integral positive definite $Q$, the real form $Q \otimes \mathbb R$ has the
same values, $D$ and (5.5) value, so `tendsto_volume_shell_div` is the special case of `tendsto_volume_shell_div_real`. -/
theorem tendsto_volume_shell_div_of_real {Q : IntQF n} (hQ : Q.PosDef) (hn : 1 ≤ n) {m : ℝ} (hm : 0 < m) :
    Tendsto (fun ε => (volume {x : Fin n → ℝ | Q.evalIn ℝ x ∈ Set.Ioc m (m + ε)}).toReal / ε)
      (𝓝[>] 0) (𝓝 (betaInf Q m)) := by
  set QR : QuadForm ℝ n := Q.map (Int.castRingHom ℝ)
  have hev : ∀ x : Fin n → ℝ, QR.eval x = Q.evalIn ℝ x := fun x =>
    LocalDensity.evalIn_map_intCast ℝ Q x
  have hpos : IsPosDefR QR := fun x hx => by rw [hev]; exact hQ.evalIn_real_pos x hx
  have hD : gramDetR QR = gramDet Q := by
    rw [gramDetR, gramDet, hessian_map_NF]
    have h := RingHom.map_det (Int.castRingHom ℝ) Q.hessian
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]; simp
  have := tendsto_volume_shell_div_real hpos hn hm
  simp only [hev] at this
  rwa [betaInfR, hD, ← betaInf] at this

end Real

/-! ### Each real place of $F$, and the product -/

section NF

open Classical

variable {F : Type} [Field F] [NumberField F]

/-- **$Q$ is positive definite at the real place $w$:** $Q_w = \sigma_w(Q)$ is positive definite on $\mathbb R^n$. -/
def IsPosDefAt (Q : QuadForm (𝓞 F) n) (w : RealPlace F) : Prop := IsPosDefR (realForm Q w)

/-- $\beta_w(m)$ is the (5.5) value of the real form $Q_w$ at $\sigma_w(m)$. -/
theorem betaInfAt_eq_betaInfR (Q : QuadForm (𝓞 F) n) (w : RealPlace F) (m : F) :
    betaInfAt Q w m = betaInfR (realForm Q w) (realEmb w m) := rfl

/-- **(5.5) at a real place, as Siegel's volume limit** (Hanke 2004, (5.1), (5.5), pp. 368–369, at the real place $w$):
if $Q$ is positive definite at $w$, $n \ge 1$ and $\sigma_w(m) > 0$, then
$\mathrm{Vol}\{\vec x \in \mathbb R^n : \sigma_w(m) < Q_w(\vec x) \le \sigma_w(m) + \varepsilon\}/\varepsilon \to \beta_w(m)
= \frac{n\,\omega_n}{2}D_w^{-1/2}\sigma_w(m)^{(n-2)/2}$ (`betaInfAt`, $D_w$ = `gramDetNF`). -/
@[kb "hanke2004" "(5.1), (5.5), pp. 368–369 (at a real place)"]
theorem tendsto_volume_shell_div_realPlace {Q : QuadForm (𝓞 F) n} {w : RealPlace F} (hQ : IsPosDefAt Q w)
    (hn : 1 ≤ n) {m : F} (hm : 0 < realEmb w m) :
    Tendsto (fun ε => (volume {x : Fin n → ℝ |
        (realForm Q w).eval x ∈ Set.Ioc (realEmb w m) (realEmb w m + ε)}).toReal / ε)
      (𝓝[>] 0) (𝓝 (betaInfAt Q w m)) :=
  tendsto_volume_shell_div_real hQ hn hm

/-- **$\beta_\infty$ over $F$ is the product of the real-place volume limits** (Hanke 2004, (5.3), (5.5), pp. 368–369): for
$Q$ positive definite at every real place, $n \ge 1$ and $m$ positive at every real place,
$\prod_w \mathrm{Vol}_w(\varepsilon)/\varepsilon \to$ `betaInfNF Q m` $= \prod_w \beta_w(m)$. -/
@[kb "hanke2004" "(5.3), (5.5), pp. 368–369 (over F)"]
theorem tendsto_prod_volume_shell_div {Q : QuadForm (𝓞 F) n} (hQ : ∀ w, IsPosDefAt Q w) (hn : 1 ≤ n) {m : F}
    (hm : ∀ w : RealPlace F, 0 < realEmb w m) :
    Tendsto (fun ε => ∏ w : RealPlace F, (volume {x : Fin n → ℝ |
        (realForm Q w).eval x ∈ Set.Ioc (realEmb w m) (realEmb w m + ε)}).toReal / ε)
      (𝓝[>] 0) (𝓝 (betaInfNF Q m)) :=
  tendsto_finsetProd _ fun w _ => tendsto_volume_shell_div_realPlace (hQ w) hn (hm w)

/-- **`betaInfNF` as a product of limits:** $\beta_\infty(m) = \prod_w \lim_{\varepsilon \to 0^+}
\mathrm{Vol}\{\sigma_w(m) < Q_w \le \sigma_w(m) + \varepsilon\}/\varepsilon$. -/
@[kb "hanke2004" "(5.3), (5.5), pp. 368–369 (over F)"]
theorem betaInfNF_eq_prod_limUnder {Q : QuadForm (𝓞 F) n} (hQ : ∀ w, IsPosDefAt Q w) (hn : 1 ≤ n) {m : F}
    (hm : ∀ w : RealPlace F, 0 < realEmb w m) :
    betaInfNF Q m = ∏ w : RealPlace F, limUnder (𝓝[>] (0 : ℝ)) (fun ε => (volume {x : Fin n → ℝ |
        (realForm Q w).eval x ∈ Set.Ioc (realEmb w m) (realEmb w m + ε)}).toReal / ε) :=
  Finset.prod_congr rfl fun w _ => (tendsto_volume_shell_div_realPlace (hQ w) hn (hm w)).limUnder_eq.symm

end NF

end QuadFormsKB.Siegel

end
