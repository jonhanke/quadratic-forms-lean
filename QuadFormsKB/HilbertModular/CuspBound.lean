/-
# Hilbert cusp forms: the growth bound $|f(z)| \le C\,N(\operatorname{Im}z)^{-k/2}$

Let $F$ be totally real of degree $d$, $\mathfrak N \ne 0$, $\Gamma \supseteq \Gamma(\mathfrak N)$ (e.g. $\Gamma_1(\mathfrak N)$), $k \in \mathbb{Z}$ and
$f \in S_k(\Gamma)$ (`cuspFormSpace`: $f\,|_k\,\gamma = f$ on $\Gamma$, holomorphic, $f\,|_k\,A \to 0$ at $i\infty$ for every
$A \in \mathrm{SL}_2(F)$). Write $N(y) = \prod_vy_v$ and $\varphi(z) = N(\operatorname{Im}z)^{k/2}|f(z)|$.

**Main theorem** (`exists_bound_of_mem_cuspFormSpace`): $\varphi$ is bounded on $\mathbb{H}^d$; equivalently
(`exists_norm_le_of_mem_cuspFormSpace`) there is $C$ with
$$|f(z)| \le C\,N(\operatorname{Im}z)^{-k/2}\qquad(z \in \mathbb{H}^d).$$
For $S_k(\Gamma_0(\mathfrak N), \chi)$ (`cuspFormChar`, contained in $S_k(\Gamma_1(\mathfrak N))$): `exists_norm_le_of_mem_cuspFormChar`.
This discharges the hypothesis `hbound` of `MeanSquare.lean` for cusp forms: `sum_sq_qCoeff_le_trace_of_cuspFormChar` and
`norm_qCoeff_le_hecke_norm_of_cuspFormChar` (Hecke's bound $|a_\nu| \ll N(\nu)^{k/2}$) have no growth hypothesis.

**Proof** (Siegel sets at finitely many cusps).
1. *Invariance* (`phi_slash`): $N(\operatorname{Im}Mw)^{k/2}|f(Mw)| = N(\operatorname{Im}w)^{k/2}|(f\,|_k\,M)(w)|$ for $M \in \mathrm{SL}_2(F)$,
   because $\operatorname{Im}(Mw)_v = \operatorname{Im}w_v/|c_vw_v + d_v|^2$; so $\varphi$ is $\Gamma$-invariant.
2. *Reduction* (`Reduction.lean`, `exists_cusp_reduction`): finitely many $A \in T$ and $c_0 > 0$ such that every $z$ has
   $\gamma \in \Gamma(\mathfrak N)$, $A \in T$ with $w = A\gamma z$ satisfying $N(\operatorname{Im}w) \ge c_0$; then
   $\varphi(z) = \varphi(A^{-1}w) = N(\operatorname{Im}w)^{k/2}|(f\,|_k\,A^{-1})(w)|$.
3. *The bound at one cusp* (`exists_bound_slash_of_mem_cuspFormSpace`): for $g = f\,|_k\,B$ ($B \in \mathrm{SL}_2(F)$),
   $N(\operatorname{Im}w)^{k/2}|g(w)|$ is bounded on $\{N(\operatorname{Im}w) \ge c_0\}$. Indeed $B^{-1}\Gamma B$ contains $T(I)$ for a fractional
   ideal $I$ and $\mathrm{diag}(u^m, u^{-m})$ for all units $u$ (`koecher_cusp_hyp_of_GammaFull_le`). The units act by
   $w \mapsto u^{2m}w$, preserving $|g|$ and $N(\operatorname{Im}w)$; by Dirichlet's unit theorem (`exists_unit_log_balance`) a unit
   moves $y = \operatorname{Im}w$ to $y'$ with $\log y'_v \ge \frac1d\log N(y) - R$ for all $v$, so $\min_vy'_v \ge e^{-R}N(y)^{1/d}$. The
   cusp form $g$ decays like $e^{-2\pi\min_vy_v/N}$ (`CuspDecay.lean`; $N \in I$ a positive integer), and
   $N(y)^{k/2}\exp(-\beta N(y)^{1/d})$ is bounded for $N(y) \ge c_0$ (`exists_exp_mul_sub_exp_le`).

Sources: Shimura, *The special values of the zeta functions associated with Hilbert modular forms*, Duke Math. J. 45
(1978), §1–2 (cusp forms are bounded in this sense) [unverified]; van der Geer, *Hilbert Modular Surfaces* (1988), Ch. I
§2–3 (Siegel sets, reduction) [unverified]; Garrett, *Holomorphic Hilbert Modular Forms* (1990), Ch. 1 (Hecke's estimate)
[unverified]; Freitag, *Hilbert Modular Forms* (1990), Ch. I §2–4 [unverified].
-/
import QuadFormsKB.HilbertModular.CuspDecay
import QuadFormsKB.HilbertModular.Reduction

open Matrix NumberField UpperHalfPlane Complex Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped MatrixGroups ModularForm Real nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

/-! ### Two real-variable lemmas -/

/-- $\exp(aL - \beta e^L)$ is bounded above on $[L_0, \infty)$ for $\beta > 0$ (any real $a$). For $a > 0$ use
$e^u \ge 1 + u$ at $u = L - \log(a/\beta)$: $aL - \beta e^L \le a\log(a/\beta) - a$. -/
lemma exists_exp_mul_sub_exp_le (a β L₀ : ℝ) (hβ : 0 < β) :
    ∃ B, ∀ L, L₀ ≤ L → Real.exp (a * L - β * Real.exp L) ≤ B := by
  refine ⟨Real.exp (a * L₀) + Real.exp (a * Real.log (a / β) - a), fun L hL => ?_⟩
  rcases le_or_gt a 0 with ha | ha
  · have : a * L - β * Real.exp L ≤ a * L₀ := by
      have := Real.exp_pos L
      nlinarith
    exact (Real.exp_le_exp.mpr this).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have hab : 0 < a / β := div_pos ha hβ
    have h := Real.add_one_le_exp (L - Real.log (a / β))
    rw [Real.exp_sub, Real.exp_log hab, le_div_iff₀ hab] at h
    have : a * L - β * Real.exp L ≤ a * Real.log (a / β) - a := by
      have e : (L - Real.log (a / β) + 1) * (a / β) * β = a * (L - Real.log (a / β) + 1) := by
        field_simp
      nlinarith
    exact (Real.exp_le_exp.mpr this).trans (le_add_of_nonneg_left (Real.exp_pos _).le)

/-- If $\sum_v\ell_v = 0$ and $\ell_v \le R$ for all $v$ ($R \ge 0$), then $\ell_v \ge -|\iota|R$. -/
lemma neg_card_mul_le_of_sum_eq_zero {ι : Type*} [Fintype ι] (ℓ : ι → ℝ) (hsum : ∑ w, ℓ w = 0)
    {R : ℝ} (hR : 0 ≤ R) (h : ∀ w, ℓ w ≤ R) (v : ι) : -(Fintype.card ι * R) ≤ ℓ v := by
  classical
  have h1 := Finset.add_sum_erase Finset.univ ℓ (Finset.mem_univ v)
  have h2 : ∑ w ∈ Finset.univ.erase v, ℓ w ≤ ∑ w ∈ Finset.univ.erase v, R := Finset.sum_le_sum fun w _ => h w
  have h3 : ∑ w ∈ Finset.univ.erase v, R ≤ Fintype.card ι * R := by
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hR
    exact_mod_cast (Finset.card_erase_le).trans (le_of_eq Finset.card_univ)
  linarith

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

/-! ### Units: balancing in logarithmic form -/

variable (F) in
/-- **Balancing by $2m$-th powers of units (Dirichlet).** For $m \ge 1$ there is $R \ge 0$ such that every $y \in \mathbb{R}^d_{>0}$ has a
unit $\varepsilon$ with
$$\log\big(|\sigma_v\varepsilon|^{2m}y_v\big) \ge \tfrac1d\sum_w\log y_w - R\qquad\text{for every place } v.$$
(From `exists_unit_balance`, applied to $a_v = y_v^{1/2m}$, which bounds the logarithms from above; their sum is
$\sum_w\log y_w$ since $\prod_w|\sigma_w\varepsilon| = 1$, which bounds them from below.) -/
lemma exists_unit_log_balance (m : ℕ) (hm : 0 < m) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y : InfinitePlace F → ℝ, (∀ v, 0 < y v) → ∃ ε : (𝓞 F)ˣ, ∀ v,
      (∑ w, Real.log (y w)) / Fintype.card (InfinitePlace F) - R ≤
        Real.log (v (ε : F) ^ (2 * m) * y v) := by
  obtain ⟨C, hC, hbal⟩ := exists_unit_balance F
  set d := Fintype.card (InfinitePlace F)
  have hd : (0 : ℝ) < d := by exact_mod_cast Fintype.card_pos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set R₀ : ℝ := 2 * m * |Real.log C|
  refine ⟨R₀, by positivity, fun y hy => ?_⟩
  set a : InfinitePlace F → ℝ := fun v => Real.exp (Real.log (y v) / (2 * m))
  obtain ⟨ε, hε⟩ := hbal a fun v => Real.exp_pos _
  refine ⟨ε, fun v => ?_⟩
  have hpos : ∀ w : InfinitePlace F, 0 < w (ε : F) := fun w => Units.pos_at_place ε w
  set Λ := ∑ w, Real.log (y w)
  set L : InfinitePlace F → ℝ := fun w => Real.log (w (ε : F) ^ (2 * m) * y w)
  have hL : ∀ w, L w = 2 * m * Real.log (w (ε : F)) + Real.log (y w) := by
    intro w
    simp only [L]
    rw [Real.log_mul (pow_pos (hpos w) _).ne' (hy w).ne', Real.log_pow]; push_cast; ring
  have hlogA : ∀ w, Real.log (w (ε : F) * Real.exp (Real.log (y w) / (2 * m))) =
      Real.log (w (ε : F)) + Real.log (y w) / (2 * m) := by
    intro w
    rw [Real.log_mul (hpos w).ne' (Real.exp_pos _).ne', Real.log_exp]
  have hsumU := sum_log_place_unit ε
  -- the upper bound `d L_v ≤ Λ + 2m log C`
  have hup : ∀ w, d * L w - Λ ≤ R₀ := by
    intro w
    have h := hε w
    have hl := Real.log_le_log (pow_pos (mul_pos (hpos w) (Real.exp_pos _)) _) h
    rw [Real.log_pow, Real.log_mul hC.ne' (Finset.prod_pos fun u _ =>
      mul_pos (hpos u) (Real.exp_pos _)).ne', Real.log_prod (fun u _ =>
        (mul_pos (hpos u) (Real.exp_pos _)).ne')] at hl
    simp only [hlogA, Finset.sum_add_distrib, hsumU, zero_add, ← Finset.sum_div] at hl
    rw [hL w]
    have hlC : Real.log C ≤ |Real.log C| := le_abs_self _
    have e : d * (2 * m * Real.log (w (ε : F)) + Real.log (y w)) - Λ =
        2 * m * ((d : ℝ) * (Real.log (w (ε : F)) + Real.log (y w) / (2 * m)) - Λ / (2 * m)) := by
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left (show (d : ℝ) * (Real.log (w (ε : F)) + Real.log (y w) / (2 * m)) -
      Λ / (2 * m) ≤ |Real.log C| by linarith) (by positivity : (0:ℝ) ≤ 2 * m)
    simpa [R₀, mul_assoc] using this
  -- the logarithms sum to `Λ`
  have hsum : ∑ w, (d * L w - Λ) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [hL, Finset.sum_add_distrib, ← Finset.mul_sum, hsumU, mul_zero, zero_add]
    ring
  have hlow := neg_card_mul_le_of_sum_eq_zero (fun w => d * L w - Λ) hsum (by positivity) hup v
  change Λ / d - R₀ ≤ L v
  rw [div_sub' hd.ne', div_le_iff₀ hd]
  linarith

/-! ### $\varphi(z) = N(\operatorname{Im}z)^{k/2}|f(z)|$ under $\mathrm{SL}_2(F)$ -/

/-- **The slash law for $\varphi$**: for $M \in \mathrm{SL}_2(F)$,
$$N(\operatorname{Im}Mw)^{k/2}\,|f(Mw)| = N(\operatorname{Im}w)^{k/2}\,|(f\,|_k\,M)(w)|,$$
since $\operatorname{Im}(Mw)_v = \operatorname{Im}w_v/|j_v|^2$ and $|(f\,|_k\,M)(w)| = |f(Mw)|\prod_v|j_v|^{-k}$, $j_v = \sigma_v(c)w_v + \sigma_v(d)$. -/
theorem phi_slash (k : ℤ) (f : (InfinitePlace F → ℍ) → ℂ) (M : SL(2, F))
    (w : InfinitePlace F → ℍ) :
    (∏ v, ((slHom (realEmb F) M • w) v).im) ^ ((k : ℝ) / 2) * ‖f (slHom (realEmb F) M • w)‖ =
      (∏ v, (w v).im) ^ ((k : ℝ) / 2) * ‖(f ∣[k] slHom (realEmb F) M) w‖ := by
  set j : InfinitePlace F → ℂ := fun v =>
    denom ((slHom (realEmb F) M v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (w v)
  have hj : ∀ v, 0 < ‖j v‖ := fun v => norm_pos_iff.mpr (denom_ne_zero _ _)
  have him : ∀ v, ((slHom (realEmb F) M • w) v).im = (w v).im / ‖j v‖ ^ 2 := by
    intro v; rw [im_slHom_smul, Complex.normSq_eq_norm_sq]
  have hslash : ‖(f ∣[k] slHom (realEmb F) M) w‖ = ‖f (slHom (realEmb F) M • w)‖ *
      ∏ v, (‖j v‖ ^ k)⁻¹ := by
    rw [slash_apply, norm_mul, norm_prod]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [slHom_det, _root_.one_zpow, ofReal_one, one_mul, norm_zpow, _root_.zpow_neg]
  have hy : 0 < ∏ v, (w v).im := Finset.prod_pos fun v _ => (w v).im_pos
  have hJ : 0 < ∏ v, ‖j v‖ ^ 2 := Finset.prod_pos fun v _ => pow_pos (hj v) 2
  have hpow : (∏ v, ‖j v‖ ^ 2) ^ ((k : ℝ) / 2) = ∏ v, ‖j v‖ ^ k := by
    rw [← Real.finsetProd_rpow _ _ (fun v _ => (pow_pos (hj v) 2).le)]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hj v).le, ← Real.rpow_intCast]
    congr 1; push_cast; ring
  rw [Finset.prod_congr rfl fun v _ => him v, Finset.prod_div_distrib,
    Real.div_rpow hy.le hJ.le, hpow, hslash, Finset.prod_inv_distrib]
  have : 0 < ∏ v, ‖j v‖ ^ k := Finset.prod_pos fun v _ => zpow_pos (hj v) k
  field_simp

/-- **$\varphi$ is invariant** under $M$ with $f\,|_k\,M = f$. -/
lemma phi_smul_of_slash_eq {k : ℤ} {f : (InfinitePlace F → ℍ) → ℂ} {M : SL(2, F)}
    (hM : f ∣[k] slHom (realEmb F) M = f) (w : InfinitePlace F → ℍ) :
    (∏ v, ((slHom (realEmb F) M • w) v).im) ^ ((k : ℝ) / 2) * ‖f (slHom (realEmb F) M • w)‖ =
      (∏ v, (w v).im) ^ ((k : ℝ) / 2) * ‖f w‖ := by
  rw [phi_slash, hM]

/-! ### Integers in fractional ideals; translations in $\Gamma_1(\mathfrak N)$ -/

/-- **A nonzero fractional ideal contains a positive integer** $N$ (the norm of a nonzero integral element of $I$). -/
lemma exists_nat_mem_fractionalIdeal (I : FIˣ) : ∃ N : ℕ, 0 < N ∧ (N : F) ∈ (I : FI) := by
  obtain ⟨x, hx0, hxI⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger (I.ne_zero)
  set J : Ideal (𝓞 F) := Ideal.span {x}
  have hJ : J ≠ ⊥ := by simpa [J] using hx0
  refine ⟨Ideal.absNorm J, Nat.pos_of_ne_zero fun h => hJ (Ideal.absNorm_eq_zero_iff.mp h), ?_⟩
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem J)
  have : ((Ideal.absNorm J : ℕ) : F) = algebraMap (𝓞 F) F r * algebraMap (𝓞 F) F x := by
    rw [← map_mul, hr, map_natCast]
  rw [this, ← Algebra.smul_def]
  exact Submodule.smul_mem _ r hxI

/-- $T(\beta) \in \Gamma_1(\mathfrak N)$ for $\beta \in \mathcal{O}_F$. -/
lemma transl_mem_Gamma1 (𝔑 : Ideal (𝓞 F)) {β : F}
    (hβ : β ∈ (1 : FractionalIdeal (𝓞 F)⁰ F)) : transl β ∈ Gamma1 𝔑 := by
  obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hβ
  refine ⟨⟨!![1, r; 0, 1], by simp [det_fin_two_of]⟩, (mem_Gamma1R 𝔑).mpr ⟨?_, ?_⟩, ?_⟩
  · change (0 : 𝓞 F) ∈ 𝔑; exact 𝔑.zero_mem
  · change Ideal.Quotient.mk 𝔑 (1 : 𝓞 F) = 1; exact map_one _
  · ext i j
    change algebraMap (𝓞 F) F (!![1, r; 0, 1] i j) = transl (algebraMap (𝓞 F) F r) i j
    fin_cases i <;> fin_cases j <;> simp

/-! ### The bound at one cusp (a Siegel set) -/

/-- **The bound at one cusp.** For $f \in S_k(\Gamma)$, $\Gamma \supseteq \Gamma(\mathfrak N)$, $\mathfrak N \ne 0$, any $B \in \mathrm{SL}_2(F)$ and $c_0 > 0$, the
function $N(\operatorname{Im}w)^{k/2}|(f\,|_k\,B)(w)|$ is bounded on $\{w : N(\operatorname{Im}w) \ge c_0\}$.

*Proof.* $g = f\,|_k\,B$ is periodic for a fractional ideal $I$ and invariant (up to the factor $N(u)^{km}$ of modulus $1$)
under $w \mapsto u^{2m}w$, $u \in \mathcal{O}_F^\times$ (`koecher_cusp_hyp_of_GammaFull_le`). Choose $u$ by `exists_unit_log_balance`:
$y' = u^{2m}\operatorname{Im}w$ has $\min_vy'_v \ge e^{-R}N(y)^{1/d}$, $N(y') = N(y)$, $|g(w)| = |g(u^{2m}w)|$. By `CuspDecay.lean`
($N \in I$ a positive integer) $|g(u^{2m}w)| \le M\exp(-2\pi(e^{-R}N(y)^{1/d} - c_1)/N)$, and
$N(y)^{k/2}\exp(-\beta N(y)^{1/d})$ is bounded on $N(y) \ge c_0$ (`exists_exp_mul_sub_exp_le`, with $L = \frac1d\log N(y)$). -/
@[kb "vandergeer1988" "Ch. I §3 (Siegel sets at the cusps; cusp forms are bounded there) [unverified]"]
theorem exists_bound_slash_of_mem_cuspFormSpace {𝔑 : Ideal (𝓞 F)} (h𝔑 : 𝔑 ≠ ⊥)
    {Γ : Subgroup SL(2, F)} (hΓ : GammaFull 𝔑 ≤ Γ) {k : ℤ} {f : (InfinitePlace F → ℍ) → ℂ}
    (hf : f ∈ cuspFormSpace (realEmb F) Γ k) (B : SL(2, F)) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ M, ∀ w : InfinitePlace F → ℍ, c₀ ≤ ∏ v, (w v).im →
      (∏ v, (w v).im) ^ ((k : ℝ) / 2) * ‖(f ∣[k] slHom (realEmb F) B) w‖ ≤ M := by
  classical
  set g := f ∣[k] slHom (realEmb F) B
  obtain ⟨I, m, hm, hT, hU⟩ := koecher_cusp_hyp_of_GammaFull_le 𝔑 h𝔑 hΓ B
  set Γ' : Subgroup SL(2, F) := Γ.comap (MulAut.conj B).toMonoidHom
  have hmem : ∀ δ, δ ∈ Γ' ↔ B * δ * B⁻¹ ∈ Γ := fun δ => Iff.rfl
  have hinv' : ∀ δ ∈ Γ', g ∣[k] slHom (realEmb F) δ = g := fun δ hδ =>
    slash_conj_invariant hf.1 B δ ((hmem δ).mp hδ)
  have hper : IsLatticePeriodic g (koecherBasis I) :=
    isLatticePeriodic_of_transl hinv' I fun β hβ => (hmem _).mpr (hT β hβ)
  have hg : IsHolomorphic g := hf.2.1.slash k _
  have hz : IsZeroAtImInftyPi g := hf.2.2 B
  obtain ⟨N, hN, hNI⟩ := exists_nat_mem_fractionalIdeal I
  obtain ⟨mN, hmN⟩ := latElt_surj I hNI
  have hmN' : (koecherBasis I).equivFun.symm (fun j => (mN j : ℝ)) = fun _ => (N : ℝ) := by
    rw [koecherBasis_symm, hmN]; funext v; simp [realVec]
  obtain ⟨R, hR, hbal⟩ := exists_unit_log_balance F m hm
  set d := Fintype.card (InfinitePlace F)
  have hd : (0 : ℝ) < d := by exact_mod_cast Fintype.card_pos
  set S₀ := Real.exp (Real.log c₀ / d)
  set c₁ := Real.exp (-R) * S₀ / 2
  have hc₁ : 0 < c₁ := by positivity
  obtain ⟨M, hM⟩ := exists_norm_le_exp_of_isZeroAtImInftyPi hg hper hz hN mN hmN' hc₁
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set β := 2 * π * Real.exp (-R) / N
  have hβ : 0 < β := by positivity
  obtain ⟨Bd, hBd⟩ := exists_exp_mul_sub_exp_le (d * k / 2) β (Real.log c₀ / d) hβ
  refine ⟨|M| * Real.exp (2 * π * c₁ / N) * Bd, fun w hw => ?_⟩
  set y := imVec w
  have hy : ∀ v, 0 < y v := imVec_pos w
  set P := ∏ v, (w v).im
  have hP : 0 < P := Finset.prod_pos fun v _ => (w v).im_pos
  obtain ⟨ε, hε⟩ := hbal y hy
  set u : (𝓞 F)ˣ := ε ^ m
  set e : InfinitePlace F → ℝ := fun v => realEmb F v (u : F) ^ 2
  have he : ∀ v, e v = v (ε : F) ^ (2 * m) := fun v => by
    have hu : ((u : 𝓞 F) : F) = ((ε : 𝓞 F) : F) ^ m := by simp [u]
    simp only [e, hu, map_pow]
    rw [← pow_mul, mul_comm m 2, pow_mul, pow_mul, ← sq_abs (realEmb F v _), abs_realEmb]
  -- the unit moves `w` to `w'` without changing `|g|`
  have hDU : g ∣[k] slHom (realEmb F) (diagU (unitF u)) = g := by
    refine hinv' _ ((hmem _).mpr ?_)
    have : unitF u = unitF ε ^ m := map_pow _ _ _
    rw [this]; exact hU ε
  have h1 := norm_slash_diagU k g u (x := reVec w) hy
  rw [hDU, ptXY_re_im] at h1
  have hy' : ∀ v, 0 < (e * y) v := fun v => by
    simp only [Pi.mul_apply, he]; exact mul_pos (pow_pos (Units.pos_at_place ε v) _) (hy v)
  set w' := ptXY (e * reVec w) (e * y)
  have him' : ∀ v, (w' v).im = e v * y v := fun v => congrFun (imVec_ptXY hy') v
  -- lower bound for `Im w'`
  have hΛ : ∑ v, Real.log (y v) = Real.log P := by
    rw [show P = ∏ v, y v from rfl, Real.log_prod (fun v _ => (hy v).ne')]
  set S := Real.exp (Real.log P / d)
  have hlow : ∀ v, Real.exp (-R) * S ≤ (w' v).im := by
    intro v
    have h := hε v
    rw [hΛ] at h
    rw [him', he, ← Real.exp_add, ← Real.exp_log (mul_pos (pow_pos (Units.pos_at_place ε v) _) (hy v))]
    exact Real.exp_le_exp.mpr (by linarith)
  have hS : S₀ ≤ S := Real.exp_le_exp.mpr
    (div_le_div_of_nonneg_right (Real.log_le_log hc₀ hw) hd.le)
  set t := Real.exp (-R) * S - c₁
  have ht : 0 ≤ t := by
    have : Real.exp (-R) * S₀ ≤ Real.exp (-R) * S := mul_le_mul_of_nonneg_left hS (Real.exp_pos _).le
    have h0 : 0 < Real.exp (-R) * S₀ := by positivity
    simp only [t, c₁]; linarith
  have hM' := hM w' t ht fun v => by have := hlow v; simp only [t]; linarith
  rw [← h1] at hM'
  -- assemble
  have hM0 : 0 ≤ M := by
    have := (norm_nonneg _).trans hM'
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  have hPk : P ^ ((k : ℝ) / 2) = Real.exp (d * k / 2 * (Real.log P / d)) := by
    rw [Real.rpow_def_of_pos hP]; congr 1; field_simp
  have hexp : Real.exp (-2 * π * t / N) = Real.exp (2 * π * c₁ / N) * Real.exp (-(β * S)) := by
    rw [← Real.exp_add]; congr 1; simp only [t, β]; field_simp; ring
  have hfin := hBd (Real.log P / d) (div_le_div_of_nonneg_right (Real.log_le_log hc₀ hw) hd.le)
  calc P ^ ((k : ℝ) / 2) * ‖g w‖ ≤ P ^ ((k : ℝ) / 2) * (M * Real.exp (-2 * π * t / N)) :=
        mul_le_mul_of_nonneg_left hM' (Real.rpow_nonneg hP.le _)
    _ = |M| * Real.exp (2 * π * c₁ / N) *
          Real.exp (d * k / 2 * (Real.log P / d) - β * Real.exp (Real.log P / d)) := by
        rw [hPk, hexp, abs_of_nonneg hM0, sub_eq_add_neg, Real.exp_add]; ring
    _ ≤ |M| * Real.exp (2 * π * c₁ / N) * Bd :=
        mul_le_mul_of_nonneg_left hfin (by positivity)

/-! ### The main bound -/

/-- **Cusp forms are bounded in the Petersson sense**: for $\mathfrak N \ne 0$, $\Gamma \supseteq \Gamma(\mathfrak N)$ and $f \in S_k(\Gamma)$
(`cuspFormSpace`), the function $\varphi(z) = N(\operatorname{Im}z)^{k/2}|f(z)|$ is bounded on $\mathbb{H}^d$:
$$\exists C,\ \forall z \in \mathbb{H}^d:\quad \Big(\prod_v\operatorname{Im}z_v\Big)^{k/2}|f(z)| \le C.$$
*Proof:* `exists_cusp_reduction` moves $z$ by $\gamma \in \Gamma(\mathfrak N) \subseteq \Gamma$ and one of finitely many $A$ to $w = A\gamma z$ with
$N(\operatorname{Im}w) \ge c_0$; $\varphi(z) = \varphi(\gamma z) = N(\operatorname{Im}w)^{k/2}|(f\,|_k\,A^{-1})(w)|$ (`phi_slash`), which is bounded by
`exists_bound_slash_of_mem_cuspFormSpace` at $A^{-1}$.

Parameters: `h𝔑` ($\mathfrak N \ne 0$), `hΓ` ($\Gamma(\mathfrak N) \le \Gamma$), `hf` ($f \in S_k(\Gamma)$). -/
@[kb "shimura1978" "§1–2 (cusp forms: N(Im z)^{k/2}|f(z)| is bounded) [unverified]"]
theorem exists_bound_of_mem_cuspFormSpace {𝔑 : Ideal (𝓞 F)} (h𝔑 : 𝔑 ≠ ⊥)
    {Γ : Subgroup SL(2, F)} (hΓ : GammaFull 𝔑 ≤ Γ) {k : ℤ} {f : (InfinitePlace F → ℍ) → ℂ}
    (hf : f ∈ cuspFormSpace (realEmb F) Γ k) :
    ∃ C, ∀ z : InfinitePlace F → ℍ, (∏ v, (z v).im) ^ ((k : ℝ) / 2) * ‖f z‖ ≤ C := by
  obtain ⟨T, c₀, hc₀, hred⟩ := exists_cusp_reduction (F := F) h𝔑
  choose M hM using fun A : SL(2, F) => exists_bound_slash_of_mem_cuspFormSpace h𝔑 hΓ hf A⁻¹ hc₀
  refine ⟨∑ A ∈ T, |M A|, fun z => ?_⟩
  obtain ⟨A, hA, γ, hγ, hc⟩ := hred z
  set w := slHom (realEmb F) (A * γ) • z
  have hγz : slHom (realEmb F) A⁻¹ • w = slHom (realEmb F) γ • z := by
    simp only [w, smul_smul, ← map_mul, inv_mul_cancel_left]
  have h1 := phi_smul_of_slash_eq (hf.1 γ (hΓ hγ)) z
  rw [← hγz, phi_slash] at h1
  rw [← h1]
  exact (hM A w hc).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun A => |M A|) (fun _ _ => abs_nonneg _) hA))

/-- **The growth bound** $|f(z)| \le C\,N(\operatorname{Im}z)^{-k/2}$ for $f \in S_k(\Gamma)$, $\Gamma \supseteq \Gamma(\mathfrak N)$, $\mathfrak N \ne 0$: the
hypothesis `hbound` of `MeanSquare.lean`, with weight $(k : \mathbb{R})$. -/
@[kb "shimura1978" "§1–2 (growth of cusp forms) [unverified]"]
theorem exists_norm_le_of_mem_cuspFormSpace {𝔑 : Ideal (𝓞 F)} (h𝔑 : 𝔑 ≠ ⊥)
    {Γ : Subgroup SL(2, F)} (hΓ : GammaFull 𝔑 ≤ Γ) {k : ℤ} {f : (InfinitePlace F → ℍ) → ℂ}
    (hf : f ∈ cuspFormSpace (realEmb F) Γ k) :
    ∃ C, ∀ z : InfinitePlace F → ℍ, ‖f z‖ ≤ C * (∏ v, (z v).im) ^ (-(k : ℝ) / 2) := by
  obtain ⟨C, hC⟩ := exists_bound_of_mem_cuspFormSpace h𝔑 hΓ hf
  refine ⟨C, fun z => ?_⟩
  have hP : 0 < ∏ v, (z v).im := Finset.prod_pos fun v _ => (z v).im_pos
  have h1 : (∏ v, (z v).im) ^ (-(k : ℝ) / 2) * (∏ v, (z v).im) ^ ((k : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hP, show -(k : ℝ) / 2 + (k : ℝ) / 2 = 0 by ring, Real.rpow_zero]
  calc ‖f z‖ = (∏ v, (z v).im) ^ (-(k : ℝ) / 2) * ((∏ v, (z v).im) ^ ((k : ℝ) / 2) * ‖f z‖) := by
        rw [← mul_assoc, h1, one_mul]
    _ ≤ (∏ v, (z v).im) ^ (-(k : ℝ) / 2) * C :=
        mul_le_mul_of_nonneg_left (hC z) (Real.rpow_nonneg hP.le _)
    _ = C * (∏ v, (z v).im) ^ (-(k : ℝ) / 2) := mul_comm _ _

/-- **The growth bound for $S_k(\Gamma_0(\mathfrak N), \chi)$** ($\mathfrak N \ne 0$): $|f(z)| \le C\,N(\operatorname{Im}z)^{-k/2}$. (A form in `cuspFormChar`
is a cusp form on $\Gamma_1(\mathfrak N) \supseteq \Gamma(\mathfrak N)$.) -/
@[kb "shimura1978" "§2 (cusp forms with character: growth bound) [unverified]"]
theorem exists_norm_le_of_mem_cuspFormChar {𝔑 : Ideal (𝓞 F)} (h𝔑 : 𝔑 ≠ ⊥)
    {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ} {k : ℤ} {f : (InfinitePlace F → ℍ) → ℂ}
    (hf : f ∈ cuspFormChar 𝔑 χ k) :
    ∃ C, ∀ z : InfinitePlace F → ℍ, ‖f z‖ ≤ C * (∏ v, (z v).im) ^ (-(k : ℝ) / 2) :=
  exists_norm_le_of_mem_cuspFormSpace h𝔑 (GammaFull_le_Gamma1 𝔑) hf.1

/-! ### The mean-square and Hecke bounds for cusp forms, unconditionally -/

/-- A form in `cuspFormChar` is periodic for the lattice $\mathcal{O}_F$ (translations $T(\beta)$, $\beta \in \mathcal{O}_F$, lie in
$\Gamma_1(\mathfrak N)$). -/
lemma isLatticePeriodic_of_mem_cuspFormChar {𝔑 : Ideal (𝓞 F)} {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ}
    {k : ℤ} {f : (InfinitePlace F → ℍ) → ℂ} (hf : f ∈ cuspFormChar 𝔑 χ k) :
    IsLatticePeriodic f (koecherBasis (1 : FIˣ)) :=
  isLatticePeriodic_of_transl hf.1.1 1 fun β hβ => transl_mem_Gamma1 𝔑 (by simpa using hβ)

/-- **Mean square of the coefficients of a cusp form, unconditionally.** For $f \in S_k(\Gamma_0(\mathfrak N), \chi)$, $\mathfrak N \ne 0$, there is
$C$ such that for all $X > 0$ and every finite set $S$ of $\nu \in \mathfrak d^{-1}$ (`dualElt 1 n`) with $\operatorname{Tr}\nu \le X$,
$$\sum_{\nu\in S}|a_\nu|^2 \le e^{4\pi}C^2X^{dk}$$
($a_\nu$ = `qCoeff` for the lattice $\mathcal{O}_F$). This is `sum_sq_qCoeff_le_trace` with `hbound` supplied by
`exists_norm_le_of_mem_cuspFormChar`. -/
@[kb "garrett1990" "Ch. 1, Hecke's estimate (mean square) [unverified]"]
theorem sum_sq_qCoeff_le_trace_of_cuspFormChar {𝔑 : Ideal (𝓞 F)} (h𝔑 : 𝔑 ≠ ⊥)
    {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ} {k : ℤ} {f : (InfinitePlace F → ℍ) → ℂ}
    (hf : f ∈ cuspFormChar 𝔑 χ k) :
    ∃ C : ℝ, ∀ X : ℝ, 0 < X → ∀ S : Finset (Fin (Module.finrank ℚ F) → ℤ),
      (∀ n ∈ S, ((Algebra.trace ℚ F (QuadFormsKB.Analysis.dualElt (1 : FIˣ) n) : ℚ) : ℝ) ≤ X) →
      ∑ n ∈ S, ‖qCoeff f (koecherBasis (1 : FIˣ)) (realVec (QuadFormsKB.Analysis.dualElt 1 n))‖ ^ 2 ≤
        Real.exp (4 * π) * C ^ 2 * X ^ ((Fintype.card (InfinitePlace F) : ℝ) * k) := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_mem_cuspFormChar h𝔑 hf
  exact ⟨C, fun X hX S hS => sum_sq_qCoeff_le_trace 1 hf.1.2.1
    (isLatticePeriodic_of_mem_cuspFormChar hf) hC hX S hS⟩

/-- **Hecke's bound for cusp forms, unconditionally**: for $f \in S_k(\Gamma_0(\mathfrak N), \chi)$, $\mathfrak N \ne 0$, there is $C$ with
$$|a_\nu| \le C\,e^{2\pi d}\,N_{F/\mathbb{Q}}(\nu)^{k/2}$$
for every totally positive $\nu \in \mathfrak d^{-1}$ (`dualElt 1 n`; coefficients for the lattice $\mathcal{O}_F$). This is
`norm_qCoeff_le_hecke_norm` with `hbound` supplied by `exists_norm_le_of_mem_cuspFormChar`. -/
@[kb "garrett1990" "Ch. 1, Hecke's estimate [unverified]"]
theorem norm_qCoeff_le_hecke_norm_of_cuspFormChar {𝔑 : Ideal (𝓞 F)} (h𝔑 : 𝔑 ≠ ⊥)
    {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ} {k : ℤ} {f : (InfinitePlace F → ℍ) → ℂ}
    (hf : f ∈ cuspFormChar 𝔑 χ k) :
    ∃ C : ℝ, ∀ n : Fin (Module.finrank ℚ F) → ℤ,
      (∀ v, 0 < realEmb F v (QuadFormsKB.Analysis.dualElt (1 : FIˣ) n)) →
      ‖qCoeff f (koecherBasis (1 : FIˣ)) (realVec (QuadFormsKB.Analysis.dualElt 1 n))‖ ≤
        C * Real.exp (2 * π * Fintype.card (InfinitePlace F)) *
          |((Algebra.norm ℚ (QuadFormsKB.Analysis.dualElt (1 : FIˣ) n) : ℚ) : ℝ)| ^ ((k : ℝ) / 2) := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_mem_cuspFormChar h𝔑 hf
  exact ⟨C, fun n hpos => norm_qCoeff_le_hecke_norm 1 hf.1.2.1
    (isLatticePeriodic_of_mem_cuspFormChar hf) hC n hpos⟩

end QuadFormsKB.HilbertModular
