/-
# Hilbert Eisenstein series VII: the Fourier expansion, $q$-expansion for $k \ge 3$

**Rows.** Every $U$-orbit of pairs $(c, d)$ with $c \ne 0$ contains exactly one pair $(\tilde c, d)$ with $\tilde c$ a fixed,
*balanced* representative of the orbit $Uc$ (`crep`; $|\sigma_v\tilde c|^d \le C|N\tilde c|$ for all $v$, `crep_balanced`). Hence
(`heckeSeries_eq_rows`)
$$H_{W,k}(z, s) = \sum_{t\in U\backslash F}H^0_t + \sum_{t \in U\backslash F^\times}\ \sum_{d\in F}W(\tilde t, d)N(\tilde tz+d)^{-k}|N(\tilde tz+d)|^{-2s},$$
$H^0_t = W(0, t)N(t)^{-k}|N(t)|^{-2s}$ the terms with $c = 0$. With the row expansion (`hasSum_row`) this is the **Fourier
expansion** (`heckeSeries_eq_fourier`):
$$H_{W,k}(z, s) = \sum_tH^0_t + \sum_{t\ne0}\sum_{n}c_{\mathfrak M}\,R_W(\tilde t, \nu_n)\prod_vT_{k,s}(\nu_{n,v}, \sigma_v(\tilde t)y_v)\,
  e\Big(\sum_v\nu_{n,v}\sigma_v(\tilde t)x_v\Big).$$

**The $q$-expansion for $k \ge 3$** (`eisSeries_qExpansion`): at $s = 0$, $T_{k,0}(\nu, h)e(\nu a) = \operatorname{sgn}(h)\frac{(-2\pi i)^k}{(k-1)!}
\nu^{k-1}e(\nu(a + ih))$ if $\nu h > 0$ and $0$ otherwise (`lineFT_zero_eq`), so
$$E_{W,k}(z) = \mathrm{c}_\infty(W) + \sum_{t\ne0}\sum_{\nu\in\mathfrak M^\vee,\ \tilde t\nu\gg0}
  c_{\mathfrak M}\Big(\frac{(-2\pi i)^k}{(k-1)!}\Big)^d\operatorname{sgn}N(\tilde t)\,R_W(\tilde t, \nu)\,N(\nu)^{k-1}\,e(\operatorname{Tr}(\tilde t\nu z)).$$
Every exponent $\mu = \tilde t\nu$ is totally positive. For $W = W_\chi$ (level $\mathfrak N$, $\chi$ trivial, $\mathfrak N = (1)$) $R_W = 1$ and
the coefficient of $e(\operatorname{Tr}\mu z)$ is $c\,\sum_{(t) \mid \mu\mathfrak d}\operatorname{sgn}N(t)^k\,N(\mu/t)^{k-1}$, a divisor sum over
the principal ideals $(t)$ with $\mu \in t\mathfrak d^{-1}$: the classical form (Shimura 1978, (3.11) [unverified]); the sum over all
ideals $\mathfrak a \mid \mu\mathfrak d$ arises after summing over the ideal-class components $\mathfrak b\mathfrak N\times\mathfrak b$.
-/
import QuadFormsKB.HilbertModular.EisensteinRows
import QuadFormsKB.HilbertModular.CuspClasses

open Complex Matrix NumberField UpperHalfPlane Filter Topology MeasureTheory
open scoped MatrixGroups ModularForm nonZeroDivisors Real

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-! ### Balanced representatives of $U\backslash F$ -/

variable (F) in
/-- The balancing constant of `exists_unit_balance`. -/
noncomputable def balConst : ℝ := (exists_unit_balance F).choose

lemma balConst_pos : 0 < balConst F := (exists_unit_balance F).choose_spec.1

lemma exists_crep_unit (t : UOrbitF F) : ∃ ε : (𝓞 F)ˣ, t.out ≠ 0 → ∀ v : InfinitePlace F,
    (v (ε : F) * v t.out) ^ Fintype.card (InfinitePlace F) ≤
      balConst F * ∏ w : InfinitePlace F, (w (ε : F) * w t.out) := by
  by_cases h : t.out = 0
  · exact ⟨1, fun h' => absurd h h'⟩
  · have hpos : ∀ v : InfinitePlace F, 0 < v t.out := fun v => by
      rw [InfinitePlace.pos_iff]; exact h
    obtain ⟨ε, hε⟩ := (exists_unit_balance F).choose_spec.2 (fun v => v t.out) hpos
    exact ⟨ε, fun _ => hε⟩

/-- **The balanced representative** $\tilde t = \varepsilon t$ of an orbit $t \in U\backslash F$. -/
noncomputable def crep (t : UOrbitF F) : F := ((exists_crep_unit t).choose : F) * t.out

lemma crep_mk (t : UOrbitF F) : (Quotient.mk _ (crep t) : UOrbitF F) = t := by
  refine (Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr
    ⟨(exists_crep_unit t).choose, ?_⟩))).trans (Quotient.out_eq t)
  rw [crep, unit_smul_eq]

lemma crep_eq_zero_iff (t : UOrbitF F) : crep t = 0 ↔ t.out = 0 := by
  rw [crep, mul_eq_zero]
  have : ((exists_crep_unit t).choose : F) ≠ 0 := by
    rw [show ((exists_crep_unit t).choose : F) = algebraMap (𝓞 F) F ((exists_crep_unit t).choose : 𝓞 F) from rfl]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (Units.ne_zero _)
  simp [this]

/-- **Balance**: $|\sigma_v\tilde t|^d \le C\,|N\tilde t|$ for every place $v$ ($t \ne 0$). -/
lemma crep_balanced {t : UOrbitF F} (ht : t.out ≠ 0) (v : InfinitePlace F) :
    |realEmb F v (crep t)| ^ Fintype.card (InfinitePlace F) ≤ balConst F * ∏ w, |realEmb F w (crep t)| := by
  have h := (exists_crep_unit t).choose_spec ht v
  simp only [crep, map_mul, abs_mul, abs_realEmb] at h ⊢
  exact h

lemma exists_smul_outF (x : F) : ∃ ε : (𝓞 F)ˣ, ε • x = (Quotient.mk _ x : UOrbitF F).out := by
  have : MulAction.orbitRel (𝓞 F)ˣ F (Quotient.mk _ x : UOrbitF F).out x :=
    Quotient.mk_out (s := MulAction.orbitRel (𝓞 F)ˣ F) x
  exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp this)

/-! ### Splitting the orbit sum into rows -/

/-- The orbit of $(\tilde t, d)$. -/
noncomputable def rowOrbit (p : UOrbitF F × F) : UOrbit F := Quotient.mk _ (crep p.1, p.2)

lemma rowOrbit_injective_on {p q : UOrbitF F × F} (hp : p.1.out ≠ 0)
    (h : rowOrbit p = rowOrbit q) : p = q := by
  obtain ⟨ε, hε⟩ := orbitRel_iff.mp (Quotient.exact h)
  have h1 : (ε : F) * crep q.1 = crep p.1 := by have := congrArg Prod.fst hε; rwa [smul_fst] at this
  have h2 : (ε : F) * q.2 = p.2 := by have := congrArg Prod.snd hε; rwa [smul_snd] at this
  have ht : p.1 = q.1 := by
    rw [← crep_mk p.1, ← crep_mk q.1]
    exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨ε, by
      rw [unit_smul_eq]; exact h1⟩))
  have hε1 : (ε : F) = 1 := by
    rw [ht] at h1
    have hc : crep q.1 ≠ 0 := (crep_eq_zero_iff _).not.mpr (ht ▸ hp)
    exact mul_right_cancel₀ hc (h1.trans (one_mul _).symm)
  rw [hε1, one_mul] at h2
  exact Prod.ext ht h2.symm

open Classical in
/-- **The orbit sum split into the $c = 0$ part and rows**, for a summable $f$ on $U\backslash F^2$. -/
theorem tsum_orbit_eq_rows {f : UOrbit F → ℂ} (hf : Summable fun o => ‖f o‖) :
    ∑' o, f o = ∑' t : UOrbitF F, f (zeroRowOrbit t) +
      ∑' t : UOrbitF F, ∑' d : F, (if t.out = 0 then 0 else f (rowOrbit (t, d))) := by
  classical
  have hs : Summable f := hf.of_norm
  set f0 : UOrbit F → ℂ := fun o => if o.out.1 = 0 then f o else 0
  set f1 : UOrbit F → ℂ := fun o => if o.out.1 = 0 then 0 else f o
  have hsplit : ∑' o, f o = ∑' o, f0 o + ∑' o, f1 o := by
    rw [← Summable.tsum_add (hs.indicator {o | o.out.1 = 0} |>.congr fun o => by
        simp only [f0, Set.indicator]; split_ifs <;> simp_all)
      (hs.indicator {o | o.out.1 ≠ 0} |>.congr fun o => by
        simp only [f1, Set.indicator]; split_ifs <;> simp_all)]
    congr 1; funext o; simp only [f0, f1]; split_ifs <;> simp
  have hs0 : Summable f0 := hs.indicator {o | o.out.1 = 0} |>.congr fun o => by
    simp only [f0, Set.indicator]; split_ifs <;> simp_all
  have hs1 : Summable f1 := hs.indicator {o | o.out.1 ≠ 0} |>.congr fun o => by
    simp only [f1, Set.indicator]; split_ifs <;> simp_all
  rw [hsplit]
  congr 1
  · -- the `c = 0` part
    have hsupp : Function.support f0 ⊆ Set.range zeroRowOrbit := by
      intro o ho
      have h1 : o.out.1 = 0 := by by_contra h; exact ho (by simp only [f0, h, ↓reduceIte])
      refine ⟨Quotient.mk _ o.out.2, ?_⟩
      rw [zeroRowOrbit_mk]
      conv_rhs => rw [← Quotient.out_eq o]
      congr 1
      exact Prod.ext h1.symm rfl
    rw [← zeroRowOrbit_injective.tsum_eq hsupp]
    refine tsum_congr fun t => ?_
    have hout : ((zeroRowOrbit t).out).1 = 0 := by
      obtain ⟨ε, hε⟩ := exists_smul_out ((0 : F), t.out)
      rw [← Quotient.out_eq t, zeroRowOrbit_mk, ← hε]
      simp [smul_fst]
    simp only [f0, hout, ↓reduceIte]
  · -- the rows
    set g : UOrbitF F × F → ℂ := fun p => if p.1.out = 0 then 0 else f (rowOrbit p)
    have hg : Summable g := by
      have hinj : Function.Injective fun q : {p : UOrbitF F × F // p.1.out ≠ 0} => rowOrbit q.1 :=
        fun q q' h => Subtype.ext (rowOrbit_injective_on q.2 h)
      have hsub : Summable fun q : {p : UOrbitF F × F // p.1.out ≠ 0} => f (rowOrbit q.1) :=
        hs.comp_injective hinj
      have hind : Summable ({p : UOrbitF F × F | p.1.out ≠ 0}.indicator fun p => f (rowOrbit p)) :=
        summable_subtype_iff_indicator.mp hsub
      have hgeq : g = {p : UOrbitF F × F | p.1.out ≠ 0}.indicator fun p => f (rowOrbit p) := by
        funext p
        by_cases h : p.1.out = 0
        · simp [g, Set.indicator, h]
        · simp [g, Set.indicator, h]
      rw [hgeq]; exact hind
    have hrow : ∀ t, Summable fun d => g (t, d) := fun t => hg.comp_injective (Prod.mk_right_injective t)
    rw [← hg.tsum_prod' hrow]
    refine tsum_eq_tsum_of_ne_zero_bij (fun p => rowOrbit p.1) ?_ ?_ ?_
    · intro p q h
      have hp : p.1.1.out ≠ 0 := by
        intro h0; apply p.2; simp only [g, h0, ↓reduceIte]
      exact Subtype.ext (rowOrbit_injective_on hp h)
    · intro o ho
      have h1 : o.out.1 ≠ 0 := by intro h; exact ho (by simp only [f1, h, ↓reduceIte])
      set c := o.out.1
      set t : UOrbitF F := Quotient.mk _ c
      obtain ⟨ε₁, hε₁⟩ := exists_smul_outF c
      have ht : t.out = (ε₁ : F) * c := by rw [← hε₁, unit_smul_eq]
      obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : (𝓞 F)ˣ, crep t = (ε₀ : F) * t.out := ⟨_, rfl⟩
      set eu : (𝓞 F)ˣ := ε₀ * ε₁
      have hcoe : ∀ a b : (𝓞 F)ˣ, ((a * b : (𝓞 F)ˣ) : F) = (a : F) * (b : F) := by
        intro a b
        rw [show ((a * b : (𝓞 F)ˣ) : F) = algebraMap (𝓞 F) F ((a * b : (𝓞 F)ˣ) : 𝓞 F) from rfl,
          Units.val_mul, map_mul]
      have hcrep : crep t = (eu : F) * c := by rw [hε₀, ht, hcoe]; ring
      have hne : ∀ a : (𝓞 F)ˣ, (a : F) ≠ 0 := fun a => by
        rw [show (a : F) = algebraMap (𝓞 F) F (a : 𝓞 F) from rfl]
        exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (Units.ne_zero _)
      have htout : t.out ≠ 0 := by
        rw [ht]; exact mul_ne_zero (hne ε₁) h1
      have hrow : rowOrbit (t, (eu : F) * o.out.2) = o := by
        rw [rowOrbit, hcrep]
        conv_rhs => rw [← Quotient.out_eq o]
        refine Quotient.sound (orbitRel_iff.mpr ⟨eu, ?_⟩)
        rfl
      refine ⟨⟨(t, (eu : F) * o.out.2), fun h0 => ?_⟩, hrow⟩
      have hfo : f o ≠ 0 := by intro h; apply ho; simp [f1, h]
      apply hfo
      rw [← hrow]
      have := h0
      simp only [g, htout, ↓reduceIte] at this
      exact this
    · intro p
      have hp : p.1.1.out ≠ 0 := by
        intro h0; apply p.2; simp only [g, h0, ↓reduceIte]
      have hc : (rowOrbit p.1).out.1 ≠ 0 := by
        obtain ⟨ε, hε⟩ := exists_smul_out (crep p.1.1, p.1.2)
        rw [rowOrbit, ← hε, smul_fst]
        refine mul_ne_zero ?_ ((crep_eq_zero_iff _).not.mpr hp)
        rw [show ((ε : (𝓞 F)ˣ) : F) = algebraMap (𝓞 F) F (ε : 𝓞 F) from rfl]
        exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (Units.ne_zero _)
      simp only [f1, hc, ↓reduceIte, g, hp]

/-! ### The Fourier expansion of the Hecke series -/

/-- **The row coefficient**: $c_{\mathfrak M}R_W(c, \nu_n)\prod_vT_{k,s}(\nu_{n,v}, \sigma_v(c)y_v)\,e(\sum_v\nu_{n,v}\sigma_v(c)x_v)$. -/
noncomputable def rowCoeff (W : F × F → ℂ) (𝔐 : Ideal (𝓞 F)) (h𝔐 : 𝔐 ≠ ⊥) (k : ℕ) (s : ℝ) (c : F)
    (z : InfinitePlace F → ℍ) (n : Fin (Module.finrank ℚ F) → ℤ) : ℂ :=
  (latConst (levelBasis 𝔐 h𝔐) : ℂ) * rowR W 𝔐 c (dualVec (levelBasis 𝔐 h𝔐) n) *
    (∏ v, lineFT k s (dualVec (levelBasis 𝔐 h𝔐) n v) (realEmb F v c * (z v).im)) *
      cexp (2 * π * Complex.I * (pair (dualVec (levelBasis 𝔐 h𝔐) n) (fun v => realEmb F v c * (z v).re) : ℂ))

lemma zeroRowOrbit_eq (t : UOrbitF F) : zeroRowOrbit t = Quotient.mk _ ((0 : F), t.out) := by
  conv_lhs => rw [← Quotient.out_eq t]
  rfl

open Classical in
/-- **The Fourier expansion of the Hecke series** (integral weight, $k \ge 2$, $0 \le s \le 1$, $k + 2s > 2$):
$H_{W,k}(z, s) = \sum_{t}W(0,t)N(t)^{-k}|N(t)|^{-2s} + \sum_{t\ne0}\sum_n$ `rowCoeff`. -/
theorem heckeSeries_eq_fourier {W : F × F → ℂ} {k : ℕ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W (k : ℤ) 𝔐)
    (hk : 2 ≤ k) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hks : 2 < (k : ℝ) + 2 * s)
    (z : InfinitePlace F → ℍ) :
    heckeSeries W k s z = ∑' t : UOrbitF F, heckeTerm W k s ((0 : F), t.out) (fun v => (z v : ℂ)) +
      ∑' t : UOrbitF F, (if t.out = 0 then 0 else
        ∑' n, rowCoeff W 𝔐 hW.ne k s (crep t) z n) := by
  obtain ⟨hmaj, hs, hb⟩ := exists_summable_bound_hecke hW.eisWeight hks (∑ v, |(z v).re| + 1)
    (B := (exists_pos_lt_min (y := imVec z) (imVec_pos z)).choose)
    (exists_pos_lt_min (y := imVec z) (imVec_pos z)).choose_spec.1
  have hsum : Summable fun o : UOrbit F => ‖heckeTerm W k s o.out fun v => (z v : ℂ)‖ := by
    refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) fun o => hb z (fun v => ⟨?_, ?_⟩) o
    · have := Finset.single_le_sum (f := fun v => |(z v).re|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ v)
      linarith
    · exact ((exists_pos_lt_min (y := imVec z) (imVec_pos z)).choose_spec.2 v).le
  rw [heckeSeries, tsum_orbit_eq_rows hsum]
  congr 1
  · refine tsum_congr fun t => ?_
    rw [zeroRowOrbit_eq, heckeTerm_out hW.unit]
  · refine tsum_congr fun t => ?_
    split_ifs with ht
    · exact tsum_zero
    · have hc : crep t ≠ 0 := (crep_eq_zero_iff t).not.mpr ht
      have hrow : ∀ d : F, (heckeTerm W k s (rowOrbit (t, d)).out fun v => (z v : ℂ)) =
          heckeTerm W k s (crep t, d) fun v => (z v : ℂ) := fun d => by
        rw [rowOrbit, heckeTerm_out hW.unit]
      simp_rw [hrow]
      exact (hasSum_row hW hk hs0 hs1 hks hc z).tsum_eq.symm

open Classical in
/-- **The Fourier expansion of $E_{W,k}$, $k \ge 3$** ($s = 0$): $E_{W,k}(z) = \mathrm{c}_\infty(W) + \sum_{t\ne0}\sum_n$ `rowCoeff`. -/
theorem eisSeries_eq_fourier {W : F × F → ℂ} {k : ℕ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W (k : ℤ) 𝔐)
    (hk : 3 ≤ k) (z : InfinitePlace F → ℍ) :
    eisSeries W k z = eisConst W k + ∑' t : UOrbitF F, (if t.out = 0 then 0 else
        ∑' n, rowCoeff W 𝔐 hW.ne k 0 (crep t) z n) := by
  have h := heckeSeries_eq_fourier hW (by omega) le_rfl zero_le_one (by push_cast; norm_num; omega) z
  rw [heckeSeries_zero] at h
  rw [h, eisConst_eq_tsum_orbitF hW.unit]
  congr 1
  refine tsum_congr fun t => ?_
  rw [heckeTerm_zero, eisTerm, eisDen_of_fst_eq_zero rfl]

/-! ### The exponential form ($s = 0$) -/

/-- The sign $\prod_v\operatorname{sgn}\sigma_v(c)$ of $N(c)$, as $\pm1$. -/
noncomputable def normSign (c : F) : ℂ := ∏ v : InfinitePlace F, ((if 0 < realEmb F v c then 1 else -1 : ℝ) : ℂ)

open Classical in
/-- **The row coefficient at $s = 0$ is a single exponential**: with $\mu_v = \nu_{n,v}\sigma_v(c)$,
$$\texttt{rowCoeff}(\dots, 0, c, z, n) = c_{\mathfrak M}R_W(c, \nu_n)\cdot[\mu \gg 0]\,\operatorname{sgn}N(c)
  \Big(\frac{(-2\pi i)^k}{(k-1)!}\Big)^d\prod_v\nu_{n,v}^{k-1}\cdot e\Big(\sum_v\mu_vz_v\Big).$$ -/
theorem rowCoeff_zero_eq {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (h𝔐 : 𝔐 ≠ ⊥) {k : ℕ} (hk : 2 ≤ k) {c : F}
    (hc : c ≠ 0) (z : InfinitePlace F → ℍ) (n : Fin (Module.finrank ℚ F) → ℤ) :
    rowCoeff W 𝔐 h𝔐 k 0 c z n =
      (latConst (levelBasis 𝔐 h𝔐) : ℂ) * rowR W 𝔐 c (dualVec (levelBasis 𝔐 h𝔐) n) *
        ((if ∀ v, 0 < dualVec (levelBasis 𝔐 h𝔐) n v * realEmb F v c then
          normSign c * ((-2 * π * Complex.I) ^ k / (k - 1).factorial) ^ Fintype.card (InfinitePlace F) *
            ∏ v, ((dualVec (levelBasis 𝔐 h𝔐) n v : ℂ) ^ (k - 1)) else 0) *
          qTerm (fun v => dualVec (levelBasis 𝔐 h𝔐) n v * realEmb F v c) z) := by
  have hcv : ∀ v, realEmb F v c ≠ 0 := fun v => (map_ne_zero_iff _ (realEmb_injective F v)).mpr hc
  have hh : ∀ v, realEmb F v c * (z v).im ≠ 0 := fun v => mul_ne_zero (hcv v) (z v).im_pos.ne'
  rw [rowCoeff, mul_assoc]
  congr 1
  simp_rw [lineFT_zero_eq hk _ (hh _)]
  set ν := dualVec (levelBasis 𝔐 h𝔐) n
  have hpos : ∀ v, (0 < ν v * (realEmb F v c * (z v).im) ↔ 0 < ν v * realEmb F v c) := by
    intro v
    rw [← mul_assoc]
    exact mul_pos_iff_of_pos_right (z v).im_pos
  have hsgn : ∀ v, (0 < realEmb F v c * (z v).im ↔ 0 < realEmb F v c) :=
    fun v => mul_pos_iff_of_pos_right (z v).im_pos
  by_cases hall : ∀ v, 0 < ν v * realEmb F v c
  · rw [if_pos hall]
    have hall' : ∀ v, 0 < ν v * (realEmb F v c * (z v).im) := fun v => (hpos v).mpr (hall v)
    simp only [hall', ↓reduceIte, hsgn]
    rw [Finset.prod_mul_distrib, qTerm_eq]
    -- collect the factors
    have hprod : ∏ v, ((-2 * π * Complex.I) ^ k / (k - 1).factorial * (ν v : ℂ) ^ (k - 1) *
        ((Real.exp (-2 * π * ν v * (realEmb F v c * (z v).im)) : ℝ) : ℂ)) =
        ((-2 * π * Complex.I) ^ k / (k - 1).factorial) ^ Fintype.card (InfinitePlace F) *
          (∏ v, (ν v : ℂ) ^ (k - 1)) *
            ((Real.exp (-2 * π * pair (fun v => ν v * realEmb F v c) (imVec z)) : ℝ) : ℂ) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        ← ofReal_prod, ← Real.exp_sum]
      congr 3
      simp only [pair, imVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => by ring
    rw [hprod, normSign]
    have hre : pair ν (fun v => realEmb F v c * (z v).re) = pair (fun v => ν v * realEmb F v c) (reVec z) := by
      simp only [pair, reVec]; refine Finset.sum_congr rfl fun v _ => by ring
    rw [hre]
    ring
  · rw [if_neg hall, zero_mul]
    push Not at hall
    obtain ⟨v₀, hv₀⟩ := hall
    have : ¬ 0 < ν v₀ * (realEmb F v₀ c * (z v₀).im) := fun h => (not_lt.mpr hv₀) ((hpos v₀).mp h)
    rw [Finset.prod_eq_zero (Finset.mem_univ v₀) (by rw [if_neg this]), zero_mul]

end QuadFormsKB.HilbertModular
