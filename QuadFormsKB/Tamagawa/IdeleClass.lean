/-
# Integration over the idele class group: $\int_{I_K/K^\times} f(|z|)\,d^\times z = \rho_K\int_0^\infty f(t)\,dt/t$

**Source.** A. Weil, *Adeles and Algebraic Groups* (`weil1982`), Theorem 3.1.1 (iii), p. 41, for $D = k$ ($n = 1$), i.e.
for $Z = \mathbb G_m$, $Z_{\mathbb A} = I_k$, with the Tamagawa measure $\omega_Z$ "determined by" the convergence factors
$\lambda_\mathfrak p = 1 - N\mathfrak p^{-1}$ "on $Z_A = I_k$, and also on $Z_A/Z_k = I_k/k^*$" (§3.2, p. 42):
$$\int_{I_k/k^\times}F(|z|)\,\omega_Z = \rho_k\int_0^{+\infty}F(t)\,\frac{dt}{t},\qquad \rho_k = [(s-1)\zeta_k(s)]_{s=1}.$$
Weil proves it by comparing his additive and multiplicative calculations (Lemma 3.1.2, p. 33, gives the shape
$c\int F(t)\,dt/t$, and $c = \rho_k$ comes out on p. 40). Here it is proved **directly**, from Dirichlet's unit theorem
and the finiteness of the class group, using Mathlib's fundamental cone and its volume
(`NumberField.mixedEmbedding.fundamentalCone.volume_normLeOne`), so it is an independent proof of (iii) and needs no
zeta function. Weil uses (iii) in the additive calculations: §4.4, p. 98 ("applying Theorem 3.1.1 (iii) to $D^*$") and
§4.5, p. 109 ("exactly the same as in 4.4"); it is used there.

**Route (a): a concrete model of the unramified ideles.** Mathlib has the idele group (`NumberField.IdeleGroup`, the units
of the adele ring) but no Haar measure on it or on its quotient. We work instead with functions that are invariant
under $\hat{\mathcal O}^\times = \prod_v\mathcal O_v^\times$, which is all that is needed (for $\Phi = \Phi_\infty\otimes\bigotimes_v\mathbf 1_{L_v}$
the function $z \mapsto \sum_\xi\Phi(\xi z)$ is $\hat{\mathcal O}^\times$-invariant, since each $L_v$ is an $\mathcal O_v$-module).
* An idele $z = (z_\infty, z_f)$ modulo $\hat{\mathcal O}^\times$ is the pair $(x, \mathfrak a)$ with $x = z_\infty \in K_\infty = K\otimes_{\mathbb Q}\mathbb R$
  (Mathlib's `mixedSpace K` $= \mathbb R^{r_1}\times\mathbb C^{r_2}$; the non-units $\{N(x) = 0\}$ are a null set) and
  $\mathfrak a = \prod_v\mathfrak p_v^{v(z_v)}$ the fractional ideal of $z_f$ (`FracIdeal K`). So an $\hat{\mathcal O}^\times$-invariant
  function on $I_K$ is a function `H : mixedSpace K → FracIdeal K → _`.
* The idele norm is $|z| = \prod_w|z_w|_w\prod_v|z_v|_v = N(x)\,N(\mathfrak a)^{-1}$ (`ideleNorm`), $N(x) = \prod_{w\text{ real}}|x_w|\prod_{w\text{ complex}}|x_w|^2$
  (`mixedEmbedding.norm`); $\gamma \in K^\times$ acts by $(x,\mathfrak a) \mapsto (\gamma x, \gamma\mathfrak a)$ and $|\gamma z| = |z|$ (`ideleNorm_principal`).

**Measure normalization (Weil's).** The Tamagawa measure on $I_K$ for the gauge form $dz/z$ and the convergence factors
$\lambda_\mathfrak p = 1 - N\mathfrak p^{-1}$ (§2.3, p. 21; §3.1, p. 32; §3.2, p. 42) is
$$d^\times z = |d_K|^{-1/2}\prod_w\frac{dx_w}{|x_w|_w}\prod_v\lambda_v^{-1}\frac{dx_v}{|x_v|_v},$$
with Weil's local measures (§2.1.1, p. 10): $dx_w$ Lebesgue on $\mathbb R$, $dx_w = i\,dz\,d\bar z = 2\,dx\,dy$ on $\mathbb C$ (so
$|z|_w = |z|^2$), and $\operatorname{vol}(\mathcal O_v) = 1$; the factor $|d_K|^{-1/2} = \mu_K^{-\dim}$ is Weil's $\mu_k = |\Delta_k|^{1/2}$ (§2.1.3,
p. 13). Each $\lambda_v^{-1}dx_v/|x_v|_v$ gives every coset $\mathfrak p^j\mathcal O_v^\times$ volume $1$, and $\prod_w dx_w/|x_w|_w = 2^{r_2}\,dx/N(x)$
with $dx$ = Lebesgue measure on $\mathbb R^{r_1}\times\mathbb C^{r_2}$ (`volume`). Hence, for $\hat{\mathcal O}^\times$-invariant $g \ge 0$,
$$\int_{I_K}g\,d^\times z = |d_K|^{-1/2}\,2^{r_2}\sum_{\mathfrak b}\int_{K_\infty}g(x,\mathfrak b)\,\frac{dx}{N(x)} \qquad(\texttt{ideleLIntegral}).$$

**The quotient $I_K/K^\times$.** With ideal-class representatives $\mathfrak a_c$ (`classRep`) and Mathlib's fundamental cone $C$
(a fundamental domain for $\mathcal O_K^\times/\mu_K$ acting on $\{N \ne 0\}$, from the log embedding and Dirichlet's unit
theorem), every $K^\times$-orbit in $K_\infty^\times\times\{\text{ideals}\}$ meets $\bigsqcup_c C\times\{\mathfrak a_c\}$ in exactly $w_K$ points.
So for $K^\times$-invariant $H \ge 0$ on the unramified ideles,
$$\int_{I_K/K^\times}H\,d^\times z = \frac{|d_K|^{-1/2}\,2^{r_2}}{w_K}\sum_{c\in\mathrm{Cl}_K}\int_C H(x,\mathfrak a_c)\,\frac{dx}{N(x)}\qquad(\texttt{ideleClassLIntegral}).$$
This is not an unchecked definition: **`ideleLIntegral_eq_ideleClassLIntegral`** proves the unfolding
$\int_{I_K}g = \int_{I_K/K^\times}\sum_{\gamma\in K^\times}g(\gamma z)$ for every measurable $g \ge 0$, which is the defining property of the
quotient measure (Weil §2.4, Lemma 2.4.1, pp. 25–26), so the choice of $C$ and of the $\mathfrak a_c$ does not matter.

**Results.**
* **`ideleClassLIntegral_comp_ideleNorm`** (Theorem 3.1.1 (iii)): for $f : \mathbb R \to [0,\infty]$ measurable,
  $\int_{I_K/K^\times}f(|z|)\,d^\times z = \rho_K\int_0^\infty f(t)\,dt/t$, with $\rho_K$ = `dedekindZeta_residue K`
  $= 2^{r_1}(2\pi)^{r_2}h_KR_K/(w_K\sqrt{|d_K|})$, the residue of $\zeta_K$ at $1$ (`tendsto_sub_one_mul_dedekindZeta_nhdsGT`;
  The $\rho_F$).
* `ideleClassIntegral_comp_ideleNorm`: the same for real $f$ with $f(t)/t$ integrable on $(0,\infty)$ ("provided the
  right-hand side is absolutely convergent", p. 41).
* `ideleClassLIntegral_indicator_Ioc`: $\operatorname{vol}\{z \in I_K/K^\times : a < |z| \le b\} = \rho_K\log(b/a)$; with $b = ea$ this is
  $\operatorname{vol}(I_K^1/K^\times) = \rho_K$ for the measure $d^\times z = d^\times z^1\cdot dt/t$.
* `ideleLIntegral_eq_ideleClassLIntegral`: the unfolding above.

*Proof of (iii).* $C$ is a cone, so $\operatorname{vol}\{x \in C : N(x) \le s\} = s\operatorname{vol}(C_{\le1})$
(`volume_cone_inter_norm_le`), i.e. the pushforward of $dx|_C$ under $N/a$ is $a\operatorname{vol}(C_{\le1})\,dt|_{(0,\infty)}$
(`map_norm_div_restrict_cone`); with Mathlib's $\operatorname{vol}(C_{\le1}) = 2^{r_1}\pi^{r_2}R_K$ each class contributes
$2^{r_1}\pi^{r_2}R_K\int_0^\infty f\,dt/t$, and $h_K\cdot|d_K|^{-1/2}2^{r_2}w_K^{-1}\cdot2^{r_1}\pi^{r_2}R_K = \rho_K$.
-/
import Mathlib
import QuadFormsKB.Citation

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
open MeasureTheory Set ENNReal NumberField.mixedEmbedding.fundamentalCone
open scoped Classical Pointwise nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.IdeleClass

variable (K : Type) [Field K] [NumberField K]

/-! ### The fundamental cone: a function of the norm -/

/-- **Scaling of the fundamental cone** $C$ (Mathlib's `fundamentalCone K`, a fundamental domain for
$\mathcal O_K^\times/\mu_K$ on $\{x \in K_\infty : N(x) \ne 0\}$): for real $s$,
$\operatorname{vol}\{x \in C : N(x) \le s\} = \max(s,0)\cdot\operatorname{vol}(C_{\le 1})$, $C_{\le1}$ = `normLeOne K`, since
$\{x \in C : N(x) \le s\} = s^{1/n}C_{\le1}$ for $s > 0$ ($n = [K:\mathbb Q]$, $N(cx) = |c|^nN(x)$). -/
theorem volume_cone_inter_norm_le (s : ℝ) :
    volume (fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ s}) =
      ENNReal.ofReal s * volume (normLeOne K) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [ENNReal.ofReal_of_nonpos hs, zero_mul, measure_eq_zero_iff_ae_notMem.mpr]
    · exact Filter.Eventually.of_forall fun x hx =>
        (fundamentalCone.norm_pos_of_mem hx.1).not_ge (hx.2.trans hs)
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  set c : ℝ := s ^ ((Module.finrank ℚ K : ℝ)⁻¹) with hc_def
  have hc : 0 < c := Real.rpow_pos_of_pos hs _
  have hcn : c ^ Module.finrank ℚ K = s := by
    rw [hc_def, ← Real.rpow_natCast, ← Real.rpow_mul hs.le,
      inv_mul_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]
  have hset : fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ s} = c • normLeOne K := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', mem_normLeOne,
      fundamentalCone.smul_mem_iff_mem (inv_ne_zero hc.ne'), mixedEmbedding.norm_smul,
      abs_inv, abs_of_pos hc, inv_pow, hcn]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [inv_mul_le_iff₀ hs, mul_one]
  rw [hset, Measure.addHaar_smul, mixedEmbedding.finrank, hcn, abs_of_pos hs]


/-- $\operatorname{vol}(C_{\le1}) = 2^{r_1}\pi^{r_2}R_K < \infty$. -/
theorem volume_normLeOne_ne_top : volume (normLeOne K) ≠ ∞ := by
  rw [volume_normLeOne]
  exact mul_ne_top (mul_ne_top (pow_ne_top ofNat_ne_top) (pow_ne_top coe_ne_top)) ofReal_ne_top

/-- Two measures on `ℝ` agreeing (finitely) on every `Iic s` are equal. -/
lemma measure_ext_of_Iic {μ ν : Measure ℝ} (hfin : ∀ s, μ (Iic s) ≠ ∞)
    (h : ∀ s, μ (Iic s) = ν (Iic s)) : μ = ν := by
  refine Measure.ext_of_Ioc' μ ν (fun a b _ => ne_top_of_le_ne_top (hfin b)
    (measure_mono Ioc_subset_Iic_self)) fun a b hab => ?_
  rw [← Iic_sdiff_Iic, measure_sdiff (Iic_subset_Iic.2 hab.le) measurableSet_Iic.nullMeasurableSet (hfin a),
    measure_sdiff (Iic_subset_Iic.2 hab.le) measurableSet_Iic.nullMeasurableSet (h a ▸ hfin a), h, h]

/-- **The pushforward of Lebesgue measure on the fundamental cone under $x \mapsto N(x)/a$** ($a > 0$) is
$a\,\operatorname{vol}(\{x \in C : N(x) \le 1\})$ times Lebesgue measure on $(0,\infty)$. -/
theorem map_norm_div_restrict_cone {a : ℝ} (ha : 0 < a) :
    Measure.map (fun x => mixedEmbedding.norm x / a) (volume.restrict (fundamentalCone K)) =
      (ENNReal.ofReal a * volume (normLeOne K)) • volume.restrict (Ioi (0 : ℝ)) := by
  have hm : Measurable fun x : mixedSpace K => mixedEmbedding.norm x / a :=
    (mixedEmbedding.continuous_norm K).measurable.div_const a
  have hL : ∀ s, Measure.map (fun x => mixedEmbedding.norm x / a) (volume.restrict (fundamentalCone K)) (Iic s)
      = ENNReal.ofReal (a * s) * volume (normLeOne K) := fun s => by
    rw [Measure.map_apply hm measurableSet_Iic, Measure.restrict_apply (hm measurableSet_Iic), inter_comm,
      ← volume_cone_inter_norm_le]
    congr 1; ext x
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_ofPred_eq, div_le_iff₀ ha, mul_comm s a]
  have hfin : ∀ s, Measure.map (fun x => mixedEmbedding.norm x / a)
      (volume.restrict (fundamentalCone K)) (Iic s) ≠ ∞ := fun s => by
    rw [hL]; exact mul_ne_top ofReal_ne_top (volume_normLeOne_ne_top K)
  refine measure_ext_of_Iic hfin fun s => ?_
  rw [hL, Measure.smul_apply, Measure.restrict_apply measurableSet_Iic, smul_eq_mul]
  rcases le_or_gt s 0 with hs | hs
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ha.le hs), zero_mul,
      Iic_inter_Ioi, Ioc_eq_empty (not_lt.2 hs), measure_empty, mul_zero]
  · rw [Iic_inter_Ioi, Real.volume_Ioc, sub_zero, ENNReal.ofReal_mul ha.le]; ring

/-- **The cone integral of a function of the norm** ($a > 0$, $f \ge 0$ measurable; the archimedean core of
Weil's Lemma 3.1.2, p. 33, with the constant computed):
$$\int_{C} f(N(x)/a)\,\frac{dx}{N(x)} = \operatorname{vol}(\{x \in C : N(x) \le 1\})\int_0^\infty f(t)\,\frac{dt}{t}.$$ -/
theorem lintegral_cone_comp_norm {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in fundamentalCone K, f (mixedEmbedding.norm x / a) * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ =
      volume (normLeOne K) * ∫⁻ t in Ioi (0 : ℝ), f t * ENNReal.ofReal t⁻¹ := by
  have hm : Measurable fun x : mixedSpace K => mixedEmbedding.norm x / a :=
    (mixedEmbedding.continuous_norm K).measurable.div_const a
  set g : ℝ → ℝ≥0∞ := fun t => f t * ENNReal.ofReal (a * t)⁻¹
  have hg : Measurable g := hf.mul (measurable_const.mul measurable_id).inv.ennreal_ofReal
  have h1 : ∀ x : mixedSpace K, f (mixedEmbedding.norm x / a) * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ =
      g (mixedEmbedding.norm x / a) := fun x => by
    simp only [g, mul_div_cancel₀ _ ha.ne']
  simp_rw [h1]
  rw [← lintegral_map hg hm, map_norm_div_restrict_cone K ha, lintegral_smul_measure, smul_eq_mul,
    mul_comm (ENNReal.ofReal a), mul_assoc, ← lintegral_const_mul _ hg]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [g]
  rw [mul_inv, ENNReal.ofReal_mul (inv_nonneg.2 ha.le), ← mul_assoc, mul_comm (ENNReal.ofReal a), mul_assoc,
    ← mul_assoc (ENNReal.ofReal a), ← ENNReal.ofReal_mul ha.le, mul_inv_cancel₀ ha.ne', ENNReal.ofReal_one, one_mul]


/-! ### The unramified idele class group -/

/-- **The fractional ideals of $K$** (the units of the monoid of fractional ideals, i.e. all nonzero ones, $\mathcal O_K$
being Dedekind). An idele modulo $\hat{\mathcal O}^\times$ has a finite part $\mathfrak a \in$ `FracIdeal K`. -/
abbrev FracIdeal := (FractionalIdeal (𝓞 K)⁰ K)ˣ

/-- **Chosen representatives $\mathfrak a_c$ of the ideal classes** $c \in \mathrm{Cl}_K$ (`Classical.choose`; any choice gives the same
integrals, by `ideleLIntegral_eq_ideleClassLIntegral`). -/
def classRep (c : ClassGroup (𝓞 K)) : FracIdeal K :=
  Classical.choose (ClassGroup.induction (P := fun c => ∃ I : FracIdeal K, ClassGroup.mk K I = c) K
    (fun I => ⟨I, rfl⟩) c)

/-- $[\mathfrak a_c] = c$. -/
theorem mk_classRep (c : ClassGroup (𝓞 K)) : ClassGroup.mk K (classRep K c) = c :=
  Classical.choose_spec (ClassGroup.induction (P := fun c => ∃ I : FracIdeal K, ClassGroup.mk K I = c) K
    (fun I => ⟨I, rfl⟩) c)

/-- **The absolute norm** $N(\mathfrak a) \in \mathbb Q_{>0}$ of a fractional ideal (`FractionalIdeal.absNorm`), as a real
number; $N(\mathfrak a) = \prod_v N\mathfrak p_v^{v(\mathfrak a)}$. -/
def idealNorm (𝔞 : FracIdeal K) : ℝ := ((FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ)

theorem idealNorm_pos (𝔞 : FracIdeal K) : 0 < idealNorm K 𝔞 := by
  unfold idealNorm
  have h0 := FractionalIdeal.absNorm_nonneg (𝔞 : FractionalIdeal (𝓞 K)⁰ K)
  have h1 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    fun h => 𝔞.ne_zero (FractionalIdeal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast lt_of_le_of_ne h0 (Ne.symm h1)

/-- **The idele norm** of the unramified idele $z = (x, \mathfrak a)$: $|z| = \prod_w|x_w|_w\prod_v|z_v|_v = N(x)\,N(\mathfrak a)^{-1}$,
where $x \in K_\infty$ = `mixedSpace K`, $N(x) = \prod_{w\text{ real}}|x_w|\prod_{w\text{ complex}}|x_w|^2$ (`mixedEmbedding.norm`), and
$\mathfrak a$ is the ideal of the finite part ($|z_v|_v = N\mathfrak p_v^{-v(\mathfrak a)}$). Weil's idele-module, §2.1.2, p. 11. -/
def ideleNorm (x : mixedSpace K) (𝔞 : FracIdeal K) : ℝ := mixedEmbedding.norm x / idealNorm K 𝔞

/-- **The normalizing constant of $d^\times z$ on the quotient:** $|d_K|^{-1/2}\,2^{r_2}/w_K$, $w_K$ = `torsionOrder K` the number
of roots of unity (each $K^\times$-orbit meets the fundamental set $w_K$ times). -/
def ideleClassConst : ℝ :=
  |(discr K : ℝ)| ^ (-(1 / 2 : ℝ)) * 2 ^ nrComplexPlaces K / torsionOrder K

/-- **The normalizing constant of Weil's Tamagawa measure $d^\times z$ on $I_K$** on unramified functions:
$|d_K|^{-1/2}\,2^{r_2}$ ($\mu_K^{-1}$, §2.1.3, p. 13, times the $2$ in $dx_w = 2\,dx\,dy$ at each complex place, §2.1.1, p. 10). -/
def ideleConst : ℝ := |(discr K : ℝ)| ^ (-(1 / 2 : ℝ)) * 2 ^ nrComplexPlaces K

/-- **The integral over the idele class group $I_K/K^\times$** of an unramified function $H \ge 0$ (a function of
$(x,\mathfrak a) \in K_\infty\times$ `FracIdeal K`, intended $K^\times$-invariant: $H(\gamma x,\gamma\mathfrak a) = H(x,\mathfrak a)$), for
Weil's Tamagawa measure $d^\times z$ (convergence factors $\lambda_\mathfrak p = 1 - N\mathfrak p^{-1}$, §3.2, p. 42):
$$\int_{I_K/K^\times}H\,d^\times z = \frac{|d_K|^{-1/2}\,2^{r_2}}{w_K}\sum_{c\in\mathrm{Cl}_K}\int_C H(x,\mathfrak a_c)\,\frac{dx}{N(x)},$$
$C$ = `fundamentalCone K`, $dx$ = Lebesgue measure on $\mathbb R^{r_1}\times\mathbb C^{r_2}$, $\mathfrak a_c$ = `classRep K c`. Justified as the
quotient of `ideleLIntegral` by `ideleLIntegral_eq_ideleClassLIntegral`. -/
@[kb "weil1982" "§3.2, p. 42 (ω_Z on Z_A/Z_k = I_k/k*); §2.4, Lemma 2.4.1, pp. 25–26 (quotient measure)"]
def ideleClassLIntegral (H : mixedSpace K → FracIdeal K → ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (ideleClassConst K) * ∑ c : ClassGroup (𝓞 K),
    ∫⁻ x in fundamentalCone K, H x (classRep K c) * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹

/-- $|d_K|^{-1/2}2^{r_2}w_K^{-1}\cdot h_K\cdot2^{r_1}\pi^{r_2}R_K = \rho_K$ (Mathlib's `dedekindZeta_residue_def`). -/
theorem ideleClassConst_mul :
    ideleClassConst K * (classNumber K * (2 ^ nrRealPlaces K * Real.pi ^ nrComplexPlaces K * regulator K)) =
      dedekindZeta_residue K := by
  have hw : (torsionOrder K : ℝ) ≠ 0 := by exact_mod_cast (torsionOrder_pos K).ne'
  have hd : 0 < |(discr K : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero K)
  rw [ideleClassConst, dedekindZeta_residue_def, Real.rpow_neg hd.le, ← Real.sqrt_eq_rpow, mul_pow]
  field_simp

/-- **Weil's Theorem 3.1.1 (iii) for $\mathbb G_m$** (p. 41; $D = k$, $n = 1$): for every measurable $f : \mathbb R \to [0,\infty]$,
$$\int_{I_K/K^\times}f(|z|)\,d^\times z = \rho_K\int_0^\infty f(t)\,\frac{dt}{t},$$
$d^\times z$ Weil's Tamagawa measure on $I_K/K^\times$ (`ideleClassLIntegral`), $|z|$ the idele norm (`ideleNorm`), and
$\rho_K$ = `dedekindZeta_residue K` $= 2^{r_1}(2\pi)^{r_2}h_KR_K/(w_K\sqrt{|d_K|}) = \lim_{s\to1}(s-1)\zeta_K(s)$. Both sides may be
$\infty$ (no convergence hypothesis). Proved directly (fundamental cone, unit theorem, class number), not via $\zeta_K$. -/
@[kb "weil1982" "Thm 3.1.1 (iii), p. 41 (D = k, so D* = G_m and D_A*/D_k* = I_k/k*); Lemma 3.1.2, p. 33"]
theorem ideleClassLIntegral_comp_ideleNorm {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ideleClassLIntegral K (fun x 𝔞 => f (ideleNorm K x 𝔞)) =
      ENNReal.ofReal (dedekindZeta_residue K) * ∫⁻ t in Ioi (0 : ℝ), f t * ENNReal.ofReal t⁻¹ := by
  simp only [ideleClassLIntegral, ideleNorm]
  simp_rw [lintegral_cone_comp_norm K (idealNorm_pos K _) hf, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [← classNumber, ← ideleClassConst_mul, volume_normLeOne, ← mul_assoc, ← mul_assoc]
  congr 1
  have h1 : (0 : ℝ) ≤ 2 ^ nrRealPlaces K * Real.pi ^ nrComplexPlaces K := by positivity
  rw [ENNReal.ofReal_mul (by unfold ideleClassConst; positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul h1, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_pow Real.pi_pos.le, ENNReal.ofReal_ofNat]
  simp only [coe_nnreal_eq, NNReal.coe_real_pi, mul_assoc]


/-! ### The real-valued (Bochner) version -/

/-- **Real-valued version of `lintegral_cone_comp_norm`:** for $a > 0$ and $f$ with $f(t)/t$ integrable on $(0,\infty)$,
$\int_C f(N(x)/a)\,dx/N(x) = \operatorname{vol}(C_{\le1})\int_0^\infty f(t)\,dt/t$. -/
theorem integral_cone_comp_norm {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : IntegrableOn (fun t => f t * t⁻¹) (Ioi 0)) :
    ∫ x in fundamentalCone K, f (mixedEmbedding.norm x / a) * (mixedEmbedding.norm x)⁻¹ =
      (volume (normLeOne K)).toReal * ∫ t in Ioi (0 : ℝ), f t * t⁻¹ := by
  have hm : Measurable fun x : mixedSpace K => mixedEmbedding.norm x / a :=
    (mixedEmbedding.continuous_norm K).measurable.div_const a
  set g : ℝ → ℝ := fun t => a⁻¹ * (f t * t⁻¹)
  have h1 : ∀ x : mixedSpace K, f (mixedEmbedding.norm x / a) * (mixedEmbedding.norm x)⁻¹ =
      g (mixedEmbedding.norm x / a) := fun x => by
    simp only [g]
    rcases eq_or_ne (mixedEmbedding.norm x) 0 with h0 | h0
    · simp [h0]
    · field_simp
  simp_rw [h1]
  have hg : AEStronglyMeasurable g (Measure.map (fun x => mixedEmbedding.norm x / a)
      (volume.restrict (fundamentalCone K))) := by
    rw [map_norm_div_restrict_cone K ha]
    exact (hf.aestronglyMeasurable.const_mul a⁻¹).smul_measure _
  rw [← integral_map hm.aemeasurable hg, map_norm_div_restrict_cone K ha, integral_smul_measure,
    smul_eq_mul, integral_const_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le]
  field_simp

/-- **The integral over $I_K/K^\times$ of a real-valued unramified function** (the Bochner analogue of `ideleClassLIntegral`,
same normalization): $\frac{|d_K|^{-1/2}2^{r_2}}{w_K}\sum_c\int_C H(x,\mathfrak a_c)\,dx/N(x)$, each $\int_C$ a Bochner integral
(zero when not integrable). -/
@[kb "weil1982" "§3.2, p. 42 (ω_Z on I_k/k*)"]
def ideleClassIntegral (H : mixedSpace K → FracIdeal K → ℝ) : ℝ :=
  ideleClassConst K * ∑ c : ClassGroup (𝓞 K),
    ∫ x in fundamentalCone K, H x (classRep K c) * (mixedEmbedding.norm x)⁻¹

/-- **Weil's Theorem 3.1.1 (iii) for $\mathbb G_m$, real-valued form** (p. 41: "provided $F$ is such that the right-hand side
is absolutely convergent"): if $t \mapsto f(t)/t$ is integrable on $(0,\infty)$, then
$$\int_{I_K/K^\times}f(|z|)\,d^\times z = \rho_K\int_0^\infty f(t)\,\frac{dt}{t}.$$ -/
@[kb "weil1982" "Thm 3.1.1 (iii), p. 41 (D = k; F with ∫F(t)dt/t absolutely convergent)"]
theorem ideleClassIntegral_comp_ideleNorm {f : ℝ → ℝ} (hf : IntegrableOn (fun t => f t * t⁻¹) (Ioi 0)) :
    ideleClassIntegral K (fun x 𝔞 => f (ideleNorm K x 𝔞)) =
      dedekindZeta_residue K * ∫ t in Ioi (0 : ℝ), f t * t⁻¹ := by
  simp only [ideleClassIntegral, ideleNorm]
  simp_rw [integral_cone_comp_norm K (idealNorm_pos K _) hf, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [← classNumber, ← ideleClassConst_mul, volume_normLeOne]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat, coe_toReal, NNReal.coe_real_pi,
    ENNReal.toReal_ofReal (regulator_pos K).le]
  ring

/-! ### The action of $K^\times$ and the product formula -/

/-- **$K^\times$ acting on the infinite part:** $\gamma\cdot x = \gamma x$ ($K \hookrightarrow K_\infty$ = `mixedEmbedding K`). Together
with `principalSMulFin` this is the action $\gamma\cdot(x,\mathfrak a) = (\gamma x,\gamma\mathfrak a)$ of the principal ideles. -/
def principalSMulInf (γ : Kˣ) (x : mixedSpace K) : mixedSpace K := mixedEmbedding K (γ : K) * x

/-- **$K^\times$ acting on the finite part:** $\gamma\cdot\mathfrak a = (\gamma)\,\mathfrak a$. -/
def principalSMulFin (γ : Kˣ) (𝔞 : FracIdeal K) : FracIdeal K := toPrincipalIdeal (𝓞 K) K γ * 𝔞

/-- $N((\gamma)\mathfrak a) = |N_{K/\mathbb Q}(\gamma)|\,N(\mathfrak a)$. -/
theorem idealNorm_principalSMulFin (γ : Kˣ) (𝔞 : FracIdeal K) :
    idealNorm K (principalSMulFin K γ 𝔞) = |((Algebra.norm ℚ (γ : K) : ℚ) : ℝ)| * idealNorm K 𝔞 := by
  simp only [idealNorm, principalSMulFin, Units.val_mul, coe_toPrincipalIdeal, map_mul,
    FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, Rat.cast_abs]

/-- **The product formula** $|\gamma z| = |z|$ for $\gamma \in K^\times$ (Weil §2.1.2, p. 11: $\prod_v|a_v|_v = 1$ for principal
ideles): $N(\gamma x)N((\gamma)\mathfrak a)^{-1} = |N(\gamma)|N(x)\,(|N(\gamma)|N(\mathfrak a))^{-1}$. So functions of $|z|$ live on $I_K/K^\times$. -/
@[kb "weil1982" "§2.1.2, p. 11 (|a| = ∏_v|a_v|_v = 1 for principal ideles)"]
theorem ideleNorm_principal (γ : Kˣ) (x : mixedSpace K) (𝔞 : FracIdeal K) :
    ideleNorm K (principalSMulInf K γ x) (principalSMulFin K γ 𝔞) = ideleNorm K x 𝔞 := by
  have hγ : |((Algebra.norm ℚ (γ : K) : ℚ) : ℝ)| ≠ 0 := by
    simp [γ.ne_zero]
  simp only [ideleNorm, principalSMulInf, idealNorm_principalSMulFin, map_mul, mixedEmbedding.norm_eq_norm,
    Rat.cast_abs]
  rw [mul_div_mul_left _ _ hγ]


/-! ### Multiplication on the mixed space scales Lebesgue measure by the norm -/

/-- $\det_{\mathbb R}(x \mapsto yx) = \prod_{w\text{ real}}y_w\prod_{w\text{ complex}}|y_w|^2$ on $K_\infty$. -/
theorem det_mulLeft_mixedSpace (y : mixedSpace K) :
    LinearMap.det (LinearMap.mulLeft ℝ y) = (∏ w, y.1 w) * ∏ w, Complex.normSq (y.2 w) := by
  have h : LinearMap.mulLeft ℝ y = LinearMap.prodMap
      (LinearMap.pi fun w => (LinearMap.mulLeft ℝ (y.1 w)).comp (LinearMap.proj w))
      (LinearMap.pi fun w => (LinearMap.mulLeft ℝ (y.2 w)).comp (LinearMap.proj w)) := by
    ext x <;> simp
  rw [h, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [show LinearMap.mulLeft ℝ (y.2 w) = Algebra.lmul ℝ ℂ (y.2 w) from rfl, ← Algebra.norm_apply,
      Algebra.norm_complex_apply]

/-- $|\det_{\mathbb R}(x \mapsto yx)| = N(y)$. -/
theorem abs_det_mulLeft_mixedSpace (y : mixedSpace K) :
    |LinearMap.det (LinearMap.mulLeft ℝ y)| = mixedEmbedding.norm y := by
  rw [det_mulLeft_mixedSpace, mixedEmbedding.norm_apply, prod_eq_prod_mul_prod, abs_mul,
    Finset.abs_prod, Finset.abs_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [normAtPlace_apply_of_isReal w.2, mult]
    simp only [w.2, ↓reduceIte, pow_one, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ => ?_
    have hw : ¬ IsReal w.1 := not_isReal_iff_isComplex.2 w.2
    rw [normAtPlace_apply_of_isComplex w.2, mult]
    simp only [hw, ↓reduceIte, Complex.normSq_eq_norm_sq]
    exact abs_of_nonneg (sq_nonneg _)

/-- **Change of variables $x \mapsto yx$** on $K_\infty$: $\int g(yx)\,dx = N(y)^{-1}\int g(x)\,dx$ for $N(y) \ne 0$. -/
theorem lintegral_comp_mul_left {y : mixedSpace K} (hy : mixedEmbedding.norm y ≠ 0) (g : mixedSpace K → ℝ≥0∞) :
    ∫⁻ x, g (y * x) = ENNReal.ofReal (mixedEmbedding.norm y)⁻¹ * ∫⁻ x, g x := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ y) ≠ 0 := by
    rw [← abs_ne_zero, abs_det_mulLeft_mixedSpace]; exact hy
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (mixedSpace K))) hdet
  rw [abs_inv, abs_det_mulLeft_mixedSpace] at hmap
  set e := (LinearMap.equivOfDetNeZero (LinearMap.mulLeft ℝ y) hdet).toContinuousLinearEquiv
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have he : (e : mixedSpace K → mixedSpace K) = LinearMap.mulLeft ℝ y := rfl
  have := hme.lintegral_map (μ := volume) g
  rw [he, hmap, lintegral_smul_measure] at this
  simpa [smul_eq_mul] using this.symm


/-! ### Unfolding: the integral over $I_K$ is the integral over $I_K/K^\times$ of the sum over $K^\times$ -/

/-- A number field is countable (it is finite-dimensional over $\mathbb Q$). -/
instance countable_field : Countable K :=
  Countable.of_equiv _ (Module.finBasis ℚ K).equivFun.toEquiv.symm

instance countable_units_field : Countable Kˣ :=
  Function.Injective.countable (f := ((↑) : Kˣ → K)) Units.val_injective

instance countable_units_ringOfIntegers : Countable (𝓞 K)ˣ := by
  have : Countable (𝓞 K) := Function.Injective.countable (f := ((↑) : 𝓞 K → K)) Subtype.val_injective
  exact Function.Injective.countable (f := ((↑) : (𝓞 K)ˣ → 𝓞 K)) Units.val_injective

/-- $N(\gamma) = |N_{K/\mathbb Q}(\gamma)| > 0$ for $\gamma \in K^\times$. -/
theorem norm_mixedEmbedding_pos (γ : Kˣ) : 0 < mixedEmbedding.norm (mixedEmbedding K (γ : K)) := by
  rw [mixedEmbedding.norm_eq_norm]; simp [γ.ne_zero]

theorem principalSMulInf_inv (γ : Kˣ) (x : mixedSpace K) :
    principalSMulInf K γ⁻¹ (principalSMulInf K γ x) = x := by
  simp only [principalSMulInf, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

theorem principalSMulInf_inv' (γ : Kˣ) (x : mixedSpace K) :
    principalSMulInf K γ (principalSMulInf K γ⁻¹ x) = x := by
  simpa using principalSMulInf_inv K γ⁻¹ x

theorem measurable_principalSMulInf (γ : Kˣ) : Measurable (principalSMulInf K γ) :=
  (continuous_const.mul continuous_id).measurable

/-- **$d^\times x = dx/N(x)$ is invariant under $x \mapsto \gamma x$** ($\gamma \in K^\times$). -/
theorem lintegral_principalSMulInf (γ : Kˣ) (G : mixedSpace K → ℝ≥0∞) :
    ∫⁻ x, G (principalSMulInf K γ x) * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ =
      ∫⁻ x, G x * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ := by
  set y := mixedEmbedding K (γ : K)
  have hy : 0 < mixedEmbedding.norm y := norm_mixedEmbedding_pos K γ
  have h := lintegral_comp_mul_left K hy.ne'
    (fun z => G z * ENNReal.ofReal (mixedEmbedding.norm z)⁻¹ * ENNReal.ofReal (mixedEmbedding.norm y))
  have h2 : ∀ x, G (y * x) * ENNReal.ofReal (mixedEmbedding.norm (y * x))⁻¹ *
      ENNReal.ofReal (mixedEmbedding.norm y) = G (principalSMulInf K γ x) *
      ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ := by
    intro x
    rw [mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 (mixedEmbedding.norm_nonneg _)), map_mul]
    congr 2
    rcases eq_or_ne (mixedEmbedding.norm x) 0 with h0 | h0
    · simp [h0]
    · field_simp
  simp_rw [h2] at h
  rw [h, lintegral_mul_const' _ _ ofReal_ne_top, mul_comm, mul_assoc, ← ENNReal.ofReal_mul hy.le,
    mul_inv_cancel₀ hy.ne', ENNReal.ofReal_one, mul_one]

/-- **Each orbit of $\mathcal O_K^\times$ on $\{N \ne 0\}$ meets the fundamental cone in exactly $w_K$ points.** -/
theorem tsum_indicator_cone_unit_smul {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    ∑' u : (𝓞 K)ˣ, (fundamentalCone K).indicator (1 : mixedSpace K → ℝ≥0∞) (u • x) =
      (torsionOrder K : ℝ≥0∞) := by
  obtain ⟨u0, hu0⟩ := fundamentalCone.exists_unit_smul_mem hx
  have key : ∀ u : (𝓞 K)ˣ, (fundamentalCone K).indicator (1 : mixedSpace K → ℝ≥0∞) (u • x) =
      (torsion K : Set (𝓞 K)ˣ).indicator 1 (u * u0⁻¹) := by
    intro u
    have hux : u • x = (u * u0⁻¹) • (u0 • x) := by rw [smul_smul, inv_mul_cancel_right]
    by_cases h : u * u0⁻¹ ∈ torsion K
    · rw [Set.indicator_of_mem (by rw [hux]; exact (fundamentalCone.unit_smul_mem_iff_mem_torsion hu0 _).2 h),
        Set.indicator_of_mem (show u * u0⁻¹ ∈ (torsion K : Set (𝓞 K)ˣ) from h)]
      rfl
    · rw [Set.indicator_of_notMem (by
          rw [hux]; exact fun h' => h ((fundamentalCone.unit_smul_mem_iff_mem_torsion hu0 _).1 h')),
        Set.indicator_of_notMem (show u * u0⁻¹ ∉ (torsion K : Set (𝓞 K)ˣ) from h)]
  simp_rw [key]
  have := (Equiv.mulRight u0⁻¹).tsum_eq (fun v => (torsion K : Set (𝓞 K)ˣ).indicator
      (1 : (𝓞 K)ˣ → ℝ≥0∞) v)
  simp only [Equiv.coe_mulRight] at this
  rw [this, ← tsum_subtype]
  simp only [Pi.one_apply]
  rw [ENNReal.tsum_const, mul_one, torsionOrder]
  simp [ENat.card_eq_coe_natCard]


/-- The embedding $\mathcal O_K^\times \hookrightarrow K^\times$. -/
abbrev unitsToField : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K)

theorem principalSMulInf_unitsToField (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    principalSMulInf K (unitsToField K u) x = u • x := rfl

theorem principalSMulFin_mul (γ γ' : Kˣ) (𝔞 : FracIdeal K) :
    principalSMulFin K (γ * γ') 𝔞 = principalSMulFin K γ (principalSMulFin K γ' 𝔞) := by
  simp only [principalSMulFin, map_mul, mul_assoc]

theorem toPrincipalIdeal_unitsToField (u : (𝓞 K)ˣ) : toPrincipalIdeal (𝓞 K) K (unitsToField K u) = 1 := by
  rw [toPrincipalIdeal_eq_iff, Units.val_one, ← map_one (FractionalIdeal.spanSingleton (𝓞 K)⁰),
    FractionalIdeal.spanSingleton_eq_spanSingleton]
  refine ⟨u⁻¹, ?_⟩
  rw [Units.smul_def, Algebra.smul_def]
  simp only [Units.coe_map, MonoidHom.coe_ofClass, ← map_mul, Units.inv_mul, map_one]

theorem mk_principalSMulFin (γ : Kˣ) (𝔞 : FracIdeal K) :
    ClassGroup.mk K (principalSMulFin K γ 𝔞) = ClassGroup.mk K 𝔞 := by
  rw [principalSMulFin, map_mul, (ClassGroup.mk_eq_one_iff).2, one_mul]
  rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨_, rfl⟩⟩

theorem exists_principalSMulFin_classRep (𝔟 : FracIdeal K) :
    ∃ γ0 : Kˣ, principalSMulFin K γ0 (classRep K (ClassGroup.mk K 𝔟)) = 𝔟 := by
  set 𝔞 := classRep K (ClassGroup.mk K 𝔟)
  have h : ClassGroup.mk K (𝔟 * 𝔞⁻¹) = 1 := by
    rw [map_mul, map_inv, mk_classRep, mul_inv_cancel]
  rw [ClassGroup.mk_eq_one_iff] at h
  obtain ⟨⟨x, hx⟩⟩ := h
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : ((𝔟 * 𝔞⁻¹ : FracIdeal K) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
      rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_zero, hx]; simp
    exact (𝔟 * 𝔞⁻¹).ne_zero this
  refine ⟨Units.mk0 x hx0, ?_⟩
  have h2 : toPrincipalIdeal (𝓞 K) K (Units.mk0 x hx0) = 𝔟 * 𝔞⁻¹ := by
    rw [toPrincipalIdeal_eq_iff, ← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_spanSingleton,
      hx, Units.val_mk0]
  rw [principalSMulFin, h2, inv_mul_cancel_right]

theorem principalSMulFin_eq_iff {γ γ' : Kˣ} {𝔞 : FracIdeal K} :
    principalSMulFin K γ' 𝔞 = principalSMulFin K γ 𝔞 ↔ ∃ u : (𝓞 K)ˣ, unitsToField K u * γ = γ' := by
  rw [principalSMulFin, principalSMulFin, mul_left_inj, toPrincipalIdeal_eq_iff, coe_toPrincipalIdeal,
    eq_comm, FractionalIdeal.spanSingleton_eq_spanSingleton]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, Units.ext ?_⟩
    rw [← hu, Units.smul_def, Algebra.smul_def]; rfl
  · rintro ⟨u, rfl⟩
    refine ⟨u, ?_⟩
    rw [Units.smul_def, Algebra.smul_def]; rfl

/-- **The fiber count:** for $N(y) \ne 0$ and a fractional ideal $\mathfrak b$,
$\sum_{c}\sum_{\gamma\in K^\times,\ \gamma\mathfrak a_c = \mathfrak b}\mathbf 1_C(\gamma^{-1}y) = w_K$. -/
theorem sum_tsum_fiber_indicator (𝔟 : FracIdeal K) {y : mixedSpace K} (hy : mixedEmbedding.norm y ≠ 0) :
    ∑ c : ClassGroup (𝓞 K), ∑' γ : Kˣ, (if principalSMulFin K γ (classRep K c) = 𝔟 then
      (fundamentalCone K).indicator (1 : mixedSpace K → ℝ≥0∞) (principalSMulInf K γ⁻¹ y) else 0) =
      (torsionOrder K : ℝ≥0∞) := by
  rw [Finset.sum_eq_single (ClassGroup.mk K 𝔟)]
  · obtain ⟨γ0, hγ0⟩ := exists_principalSMulFin_classRep K 𝔟
    set 𝔞 := classRep K (ClassGroup.mk K 𝔟)
    set F : Kˣ → ℝ≥0∞ := fun γ => if principalSMulFin K γ 𝔞 = 𝔟 then
      (fundamentalCone K).indicator (1 : mixedSpace K → ℝ≥0∞) (principalSMulInf K γ⁻¹ y) else 0
    have hinj : Function.Injective fun u : (𝓞 K)ˣ => unitsToField K u * γ0 := by
      intro u v h
      have h' : unitsToField K u = unitsToField K v := mul_right_cancel h
      exact Units.ext (RingOfIntegers.ext (by simpa [Units.ext_iff] using h'))
    have hsupp : Function.support F ⊆ Set.range fun u : (𝓞 K)ˣ => unitsToField K u * γ0 := by
      intro γ hγ
      by_contra hr
      apply hγ
      simp only [F]
      split_ifs with h
      · exfalso
        have h' : principalSMulFin K γ 𝔞 = principalSMulFin K γ0 𝔞 := h.trans hγ0.symm
        rw [principalSMulFin_eq_iff] at h'
        obtain ⟨u, hu⟩ := h'
        exact hr ⟨u, hu⟩
      · rfl
    rw [← hinj.tsum_eq hsupp]
    have hF : ∀ u : (𝓞 K)ˣ, F (unitsToField K u * γ0) =
        (fundamentalCone K).indicator 1 (u⁻¹ • principalSMulInf K γ0⁻¹ y) := by
      intro u
      have hc : principalSMulFin K (unitsToField K u * γ0) 𝔞 = 𝔟 := by
        rw [principalSMulFin_mul, hγ0, principalSMulFin, toPrincipalIdeal_unitsToField, one_mul]
      simp only [F, hc, ↓reduceIte]
      rw [mul_inv_rev, ← map_inv, ← principalSMulInf_unitsToField]
      simp only [principalSMulInf, Units.val_mul, map_mul]
      congr 1; ring
    simp_rw [hF]
    have := (Equiv.inv (𝓞 K)ˣ).tsum_eq (fun u => (fundamentalCone K).indicator (1 : mixedSpace K → ℝ≥0∞)
      (u • principalSMulInf K γ0⁻¹ y))
    simp only [Equiv.inv_apply] at this
    rw [this, tsum_indicator_cone_unit_smul]
    simp only [principalSMulInf, map_mul]
    exact mul_ne_zero (norm_mixedEmbedding_pos K γ0⁻¹).ne' hy
  · intro c _ hc
    refine ENNReal.tsum_eq_zero.2 fun γ => ?_
    split_ifs with h
    · exact absurd (by rw [← mk_classRep K c, ← mk_principalSMulFin K γ, h]) hc
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h


theorem measurable_invNorm :
    Measurable fun x : mixedSpace K => ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ :=
  (mixedEmbedding.continuous_norm K).measurable.inv.ennreal_ofReal

/-- **The integral over the idele group $I_K$** of an unramified ($\hat{\mathcal O}^\times$-invariant) function $g \ge 0$, for Weil's
Tamagawa measure $d^\times z = |d_K|^{-1/2}\prod_w dx_w/|x_w|_w\prod_v(1-N\mathfrak p_v^{-1})^{-1}dx_v/|x_v|_v$ (§2.3, p. 21; §3.2,
p. 42): every coset $\mathfrak p^j\mathcal O_v^\times$ has local volume $1$ and $\prod_w dx_w/|x_w|_w = 2^{r_2}dx/N(x)$, so
$$\int_{I_K}g\,d^\times z = |d_K|^{-1/2}\,2^{r_2}\sum_{\mathfrak b}\int_{K_\infty}g(x,\mathfrak b)\,\frac{dx}{N(x)},$$
the sum over all fractional ideals $\mathfrak b$ (an unordered sum in $[0,\infty]$), $dx$ Lebesgue measure on
$K_\infty = \mathbb R^{r_1}\times\mathbb C^{r_2}$. The restricted-product measure itself is not formalized; this formula is its
value on unramified functions. -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure); §3.1, p. 32 (λ_p = 1 - N(p)^{-1}); §3.2, p. 42 (ω_Z on I_k)"]
def ideleLIntegral (g : mixedSpace K → FracIdeal K → ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (ideleConst K) * ∑' 𝔟 : FracIdeal K, ∫⁻ x, g x 𝔟 * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹

/-- **The unfolding identity on the fundamental set** (the core of `ideleLIntegral_eq_ideleClassLIntegral`):
$$\sum_c\int_C\sum_{\gamma\in K^\times}g(\gamma x,\gamma\mathfrak a_c)\,\frac{dx}{N(x)} = w_K\sum_{\mathfrak b}\int_{K_\infty}g(x,\mathfrak b)\,\frac{dx}{N(x)}.$$
*Proof.* Substitute $y = \gamma x$ ($dx/N(x)$ is invariant), group the $\gamma$ by the ideal $\mathfrak b = \gamma\mathfrak a_c$, and use
that the $\gamma$ with $\gamma\mathfrak a_c = \mathfrak b$ form one coset $\gamma_0\mathcal O_K^\times$ and the $w_K$-fold covering
`tsum_indicator_cone_unit_smul`. -/
theorem sum_lintegral_cone_tsum (g : mixedSpace K → FracIdeal K → ℝ≥0∞) (hg : ∀ 𝔟, Measurable (g · 𝔟)) :
    ∑ c : ClassGroup (𝓞 K), ∫⁻ x in fundamentalCone K,
      (∑' γ : Kˣ, g (principalSMulInf K γ x) (principalSMulFin K γ (classRep K c))) *
        ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ =
      (torsionOrder K : ℝ≥0∞) * ∑' 𝔟 : FracIdeal K, ∫⁻ x, g x 𝔟 * ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ := by
  have hC := measurableSet_fundamentalCone K
  set ω : mixedSpace K → ℝ≥0∞ := fun x => ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ with hω
  have hωm : Measurable ω := measurable_invNorm K
  show ∑ c : ClassGroup (𝓞 K), ∫⁻ x in fundamentalCone K,
      (∑' γ : Kˣ, g (principalSMulInf K γ x) (principalSMulFin K γ (classRep K c))) * ω x =
      (torsionOrder K : ℝ≥0∞) * ∑' 𝔟 : FracIdeal K, ∫⁻ x, g x 𝔟 * ω x
  set ind : Kˣ → mixedSpace K → ℝ≥0∞ := fun γ y =>
    (fundamentalCone K).indicator (1 : mixedSpace K → ℝ≥0∞) (principalSMulInf K γ⁻¹ y)
  have hind : ∀ γ, Measurable (ind γ) := fun γ =>
    (measurable_one.indicator hC).comp (measurable_principalSMulInf K γ⁻¹)
  have hF : ∀ γ 𝔟, Measurable fun y => ind γ y * g y 𝔟 * ω y := fun γ 𝔟 =>
    ((hind γ).mul (hg 𝔟)).mul hωm
  -- Step 1: unfold the cone integral of the sum over `γ`, and change variables `y = γx`.
  have h1 : ∀ c, ∫⁻ x in fundamentalCone K,
      (∑' γ : Kˣ, g (principalSMulInf K γ x) (principalSMulFin K γ (classRep K c))) * ω x =
      ∑' γ : Kˣ, ∫⁻ y, ind γ y * g y (principalSMulFin K γ (classRep K c)) * ω y := by
    intro c
    rw [← lintegral_indicator hC]
    have : (fundamentalCone K).indicator (fun x =>
        (∑' γ : Kˣ, g (principalSMulInf K γ x) (principalSMulFin K γ (classRep K c))) * ω x) =
        fun x => ∑' γ : Kˣ, (ind γ (principalSMulInf K γ x) *
          g (principalSMulInf K γ x) (principalSMulFin K γ (classRep K c))) * ω x := by
      ext x
      simp only [ind, principalSMulInf_inv]
      by_cases hx : x ∈ fundamentalCone K
      · simp [Set.indicator_of_mem hx, ENNReal.tsum_mul_right]
      · simp [Set.indicator_of_notMem hx]
    rw [this, lintegral_tsum]
    · refine tsum_congr fun γ => ?_
      exact lintegral_principalSMulInf K γ (fun y => ind γ y * g y (principalSMulFin K γ (classRep K c)))
    · intro γ
      exact (((hind γ).comp (measurable_principalSMulInf K γ)).mul
        ((hg _).comp (measurable_principalSMulInf K γ))).mul hωm |>.aemeasurable
  -- Step 2: insert the sum over `𝔟`.
  have h2 : ∀ c (γ : Kˣ), ∫⁻ y, ind γ y * g y (principalSMulFin K γ (classRep K c)) * ω y =
      ∑' 𝔟 : FracIdeal K, (if principalSMulFin K γ (classRep K c) = 𝔟 then
        ∫⁻ y, ind γ y * g y 𝔟 * ω y else 0) := by
    intro c γ
    rw [tsum_eq_single (principalSMulFin K γ (classRep K c))]
    · simp only [↓reduceIte]
    · intro 𝔟 h𝔟; exact ite_eq_right_iff.2 fun h => absurd h.symm h𝔟
  simp_rw [h1, h2]
  -- Step 3: for fixed `𝔟`, fold the sums over `c` and `γ` back into the integral and count the fiber.
  have key : ∀ 𝔟 : FracIdeal K, ∑' c : ClassGroup (𝓞 K), ∑' γ : Kˣ,
      (if principalSMulFin K γ (classRep K c) = 𝔟 then ∫⁻ y, ind γ y * g y 𝔟 * ω y else 0) =
      (torsionOrder K : ℝ≥0∞) * ∫⁻ y, g y 𝔟 * ω y := by
    intro 𝔟
    have hite : ∀ c γ, (if principalSMulFin K γ (classRep K c) = 𝔟 then ∫⁻ y, ind γ y * g y 𝔟 * ω y else 0) =
        ∫⁻ y, (if principalSMulFin K γ (classRep K c) = 𝔟 then ind γ y else 0) * g y 𝔟 * ω y := by
      intro c γ; split_ifs
      · rfl
      · simp
    have hm : ∀ c γ, Measurable fun y => (if principalSMulFin K γ (classRep K c) = 𝔟 then ind γ y else 0) * g y 𝔟 * ω y := by
      intro c γ; split_ifs
      · exact hF γ 𝔟
      · simp only [zero_mul]; exact measurable_const
    simp_rw [hite]
    rw [← lintegral_const_mul (f := fun y => g y 𝔟 * ω y) _ ((hg 𝔟).mul hωm)]
    have hin : ∀ c, ∑' γ : Kˣ, ∫⁻ y, (if principalSMulFin K γ (classRep K c) = 𝔟 then ind γ y else 0) * g y 𝔟 * ω y =
        ∫⁻ y, ∑' γ : Kˣ, (if principalSMulFin K γ (classRep K c) = 𝔟 then ind γ y else 0) * g y 𝔟 * ω y :=
      fun c => (lintegral_tsum fun γ => (hm c γ).aemeasurable).symm
    simp_rw [hin]
    rw [← lintegral_tsum fun c => (Measurable.tsum fun γ => hm c γ).aemeasurable]
    congr 1; ext y
    rcases eq_or_ne (mixedEmbedding.norm y) 0 with hy | hy
    · simp [ω, hy]
    · simp_rw [ENNReal.tsum_mul_right, tsum_fintype]
      rw [sum_tsum_fiber_indicator K 𝔟 hy, mul_assoc]
  calc ∑ c : ClassGroup (𝓞 K), ∑' γ : Kˣ, ∑' 𝔟 : FracIdeal K,
        (if principalSMulFin K γ (classRep K c) = 𝔟 then ∫⁻ y, ind γ y * g y 𝔟 * ω y else 0)
      = ∑' c : ClassGroup (𝓞 K), ∑' γ : Kˣ, ∑' 𝔟 : FracIdeal K,
        (if principalSMulFin K γ (classRep K c) = 𝔟 then ∫⁻ y, ind γ y * g y 𝔟 * ω y else 0) :=
          (tsum_fintype _).symm
    _ = ∑' c : ClassGroup (𝓞 K), ∑' 𝔟 : FracIdeal K, ∑' γ : Kˣ,
        (if principalSMulFin K γ (classRep K c) = 𝔟 then ∫⁻ y, ind γ y * g y 𝔟 * ω y else 0) :=
          tsum_congr fun c => ENNReal.tsum_comm
    _ = ∑' 𝔟 : FracIdeal K, ∑' c : ClassGroup (𝓞 K), ∑' γ : Kˣ,
        (if principalSMulFin K γ (classRep K c) = 𝔟 then ∫⁻ y, ind γ y * g y 𝔟 * ω y else 0) :=
          ENNReal.tsum_comm
    _ = ∑' 𝔟 : FracIdeal K, (torsionOrder K : ℝ≥0∞) * ∫⁻ y, g y 𝔟 * ω y := tsum_congr key
    _ = _ := ENNReal.tsum_mul_left


/-- $|d_K|^{-1/2}2^{r_2}/w_K = (|d_K|^{-1/2}2^{r_2})/w_K$. -/
theorem ideleClassConst_eq : ideleClassConst K = ideleConst K / torsionOrder K := rfl

/-- **Unfolding: `ideleClassLIntegral` is the quotient of `ideleLIntegral` by $K^\times$.** For every $g \ge 0$ on the unramified
ideles, measurable in $x$,
$$\int_{I_K}g(z)\,d^\times z = \int_{I_K/K^\times}\Big(\sum_{\gamma\in K^\times}g(\gamma z)\Big)\,d^\times z.$$
This is the defining property of the measure on $I_K/K^\times$ "locally isomorphic" to $d^\times z$ (Weil, Lemma 2.4.1,
pp. 25–26, (1) with $\gamma = K^\times$; and the same formula is Lemma 2.4.2's unfolding). It identifies the concrete
`ideleClassLIntegral` (fundamental cone, class representatives) with the quotient measure, independently of those choices,
and is the tool needed to unfold $\int_{V(\mathbb A)}$ over $K^\times$-orbits. -/
@[kb "weil1982" "§2.4, Lemma 2.4.1 (1), pp. 25–26 (∫_{G/γ} f = ∫_{G/g}∫_{g/γ} f); applied to I_k ⊃ k* as in §3.2, p. 42"]
theorem ideleLIntegral_eq_ideleClassLIntegral (g : mixedSpace K → FracIdeal K → ℝ≥0∞)
    (hg : ∀ 𝔟, Measurable (g · 𝔟)) :
    ideleLIntegral K g = ideleClassLIntegral K
      (fun x 𝔞 => ∑' γ : Kˣ, g (principalSMulInf K γ x) (principalSMulFin K γ 𝔞)) := by
  have hw : (0 : ℝ) < torsionOrder K := by exact_mod_cast torsionOrder_pos K
  rw [ideleClassLIntegral, sum_lintegral_cone_tsum K g hg, ideleLIntegral, ← mul_assoc, ideleClassConst_eq,
    ENNReal.ofReal_div_of_pos hw, ENNReal.ofReal_natCast,
    ENNReal.div_mul_cancel (by exact_mod_cast hw.ne') (natCast_ne_top _)]


/-- **The volume of a norm shell:** for $0 < a \le b$,
$$\operatorname{vol}\{z \in I_K/K^\times : a < |z| \le b\} = \rho_K\log(b/a).$$
In particular ($b = ea$) the norm-one idele classes have volume $\operatorname{vol}(I_K^1/K^\times) = \rho_K$ for the decomposition
$d^\times z = d^\times z^1\cdot dt/t$ along $I_K/K^\times \cong I_K^1/K^\times\times\mathbb R_{>0}$ (Weil's normalization; cf. the use of (iii)
with $F(|N(x)|t^n)$ in §3.2, p. 43). -/
@[kb "weil1982" "Thm 3.1.1 (iii), p. 41, with F = 1_{(a,b]}"]
theorem ideleClassLIntegral_indicator_Ioc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ideleClassLIntegral K (fun x 𝔞 => (Ioc a b).indicator 1 (ideleNorm K x 𝔞)) =
      ENNReal.ofReal (dedekindZeta_residue K * Real.log (b / a)) := by
  rw [ideleClassLIntegral_comp_ideleNorm K (measurable_one.indicator measurableSet_Ioc),
    ENNReal.ofReal_mul (dedekindZeta_residue_pos K).le]
  congr 1
  have hsub : Ioc a b ⊆ Ioi 0 := fun t ht => ha.trans ht.1
  have h1 : ∫⁻ t in Ioi (0 : ℝ), (Ioc a b).indicator 1 t * ENNReal.ofReal t⁻¹ =
      ∫⁻ t in Ioc a b, ENNReal.ofReal t⁻¹ := by
    rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioi]
    congr 1; ext t
    by_cases ht : t ∈ Ioc a b
    · simp [ht, hsub ht]
    · simp [ht]
  have hint : IntegrableOn (fun t : ℝ => t⁻¹) (Ioc a b) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact intervalIntegral.intervalIntegrable_inv (fun t ht => by
      have := ht.1; rw [min_eq_left hab] at this; exact (ha.trans_le this).ne') (continuousOn_id)
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => inv_nonneg.2 (ha.le.trans ht.1.le)),
    ← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha (ha.trans_le hab)]


/-! ### The two halves of Tate's split -/

/-- **The inner half of Tate's split:** for real $s > 0$,
$$\int_{I_K/K^\times,\ |z| \le 1}|z|^s\,d^\times z = \frac{\rho_K}{s}.$$
(This is the boundary term of the additive calculation: Weil, §3.1, p. 40, the integral of
$f_-(|x|)\,(\Psi(0)|x|^{s-n} - \Phi(0)|x|^s)$; §4.4, p. 97.) -/
@[kb "weil1982" "Thm 3.1.1 (iii), p. 41, with F(t) = t^s on (0,1]; cf. p. 40 (the boundary term)"]
theorem ideleClassIntegral_rpow_le_one {s : ℝ} (hs : 0 < s) :
    ideleClassIntegral K (fun x 𝔞 => (Ioc 0 1).indicator (fun t => t ^ s) (ideleNorm K x 𝔞)) =
      dedekindZeta_residue K / s := by
  have hfun : (fun t : ℝ => (Ioc 0 1).indicator (fun t => t ^ s) t * t⁻¹) =
      (Ioc 0 1).indicator (fun t => t ^ (s - 1)) := by
    ext t
    by_cases ht : t ∈ Ioc 0 1
    · simp only [Set.indicator_of_mem ht]
      rw [Real.rpow_sub_one ht.1.ne', div_eq_mul_inv]
    · simp [Set.indicator_of_notMem ht]
  have hint : IntegrableOn (fun t : ℝ => t ^ (s - 1)) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hI : IntegrableOn (fun t : ℝ => (Ioc 0 1).indicator (fun t => t ^ s) t * t⁻¹) (Ioi 0) := by
    rw [hfun]
    exact ((integrable_indicator_iff measurableSet_Ioc).2 hint).integrableOn
  rw [ideleClassIntegral_comp_ideleNorm K hI, hfun, setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_right.2 Ioc_subset_Ioi_self, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl (by linarith))]
  rw [sub_add_cancel, Real.one_rpow, Real.zero_rpow hs.ne', sub_zero, one_div, div_eq_mul_inv]

/-- **The outer half of Tate's split:** for real $s > 0$,
$$\int_{I_K/K^\times,\ |z| > 1}|z|^{-s}\,d^\times z = \frac{\rho_K}{s}.$$ -/
@[kb "weil1982" "Thm 3.1.1 (iii), p. 41, with F(t) = t^{-s} on (1,∞)"]
theorem ideleClassIntegral_rpow_neg_gt_one {s : ℝ} (hs : 0 < s) :
    ideleClassIntegral K (fun x 𝔞 => (Ioi 1).indicator (fun t => t ^ (-s)) (ideleNorm K x 𝔞)) =
      dedekindZeta_residue K / s := by
  have hfun : (fun t : ℝ => (Ioi 1).indicator (fun t => t ^ (-s)) t * t⁻¹) =
      (Ioi 1).indicator (fun t => t ^ (-s - 1)) := by
    ext t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp only [Set.indicator_of_mem ht]
      rw [Real.rpow_sub_one (zero_lt_one.trans ht).ne', div_eq_mul_inv]
    · simp [Set.indicator_of_notMem ht]
  have hint : IntegrableOn (fun t : ℝ => t ^ (-s - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hI : IntegrableOn (fun t : ℝ => (Ioi 1).indicator (fun t => t ^ (-s)) t * t⁻¹) (Ioi 0) := by
    rw [hfun]
    exact ((integrable_indicator_iff measurableSet_Ioi).2 hint).integrableOn
  rw [ideleClassIntegral_comp_ideleNorm K hI, hfun, setIntegral_indicator measurableSet_Ioi,
    Ioi_inter_Ioi, max_eq_right zero_le_one, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
  rw [show -s - 1 + 1 = -s by ring, Real.one_rpow, div_neg, neg_div, neg_neg, one_div, div_eq_mul_inv]

end QuadFormsKB.IdeleClass