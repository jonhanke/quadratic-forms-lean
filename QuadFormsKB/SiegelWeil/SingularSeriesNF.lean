/-
# The singular series over a totally real field: Gauss sums, the Chinese remainder theorem, local factors

**Layer:** finite (algebraic, purely local after the Chinese remainder theorem). $F$ is a totally real number field,
$\mathcal O = \mathcal O_F$, $Q$ a quadratic form over $\mathcal O$ in $n$ variables (0-based $x_0, \dots, x_{n-1}$),
$e(x) = e^{2\pi ix}$, $\operatorname{Tr} = \operatorname{Tr}_{F/\mathbb Q}$, $\mathfrak d = \mathfrak d_{F}$ the different
(`differentIdeal ℤ (𝓞 F)`; $\mathfrak d^{-1}$ = `invDifferent F` is the trace dual of $\mathcal O$), and
$N$ the absolute norm of ideals.

**The Gauss average** (`gAvg`). For $c \in \mathcal O\setminus 0$ and $u \in F$,
$$G_Q(u; c) = N(c)^{-n}\sum_{r\in(\mathcal O/c)^n}e\big(\operatorname{Tr}(u\,Q(\tilde r))\big)$$
($\tilde r$ = `Quotient.out`). It is the normalized theta Gauss sum: `gaussSumF Q a c 0` is $N(c)^nG_Q(a/c; c)$.

**The truncated singular series** (`ssTrunc`). For $\nu \in F$,
$$S_c(\nu) = \sum_{d\in\mathcal O/c}G_Q(\tilde d/c; c)\,e\big(-\operatorname{Tr}(\nu\tilde d/c)\big).$$
These are the partial sums over $u = d/c \in c^{-1}\mathcal O/\mathcal O \subset F/\mathcal O$ of the singular series of the
Eisenstein series $E_Q$ (`HilbertModular/EisensteinCoeff.lean`).

**Results.**
* `sum_eTr_div` (orthogonality over $\mathcal O/c$): for $y \in \mathfrak d^{-1}$,
  $\sum_{d\in\mathcal O/c}e(\operatorname{Tr}(\tilde dy/c)) = N(c)\,[\,y/c \in \mathfrak d^{-1}\,]$. The dual of $\mathcal O$ under the trace is
  $\mathfrak d^{-1}$, **not** $\mathcal O$: this is where the different enters.
* `ssTrunc_eq_count` (**the count**): for $\nu \in \mathcal O$,
  $S_c(\nu) = N(c)^{1-n}\,\#\{r \in (\mathcal O/c)^n : (Q(\tilde r) - \nu)\,\mathfrak d \subseteq c\mathcal O\}$.
* `cnt_eq_prod` (**the Chinese remainder theorem**): the count `cnt Q I ν` of $r \in (\mathcal O/I)^n$ with
  $(Q(\tilde r) - \nu)\mathfrak d \subseteq I$ is multiplicative: $\mathrm{cnt}(I) = \prod_{\mathfrak p^e\|I}\mathrm{cnt}(\mathfrak p^e)$.
* `cnt_prime_pow` (**the local count**, every prime, dyadic included): with $\delta_\mathfrak p$ the exponent of $\mathfrak p$ in
  $\mathfrak d$ (`diffExpNF`) and $j = e - \delta_\mathfrak p$ (truncated),
  $\mathrm{cnt}(\mathfrak p^e) = N\mathfrak p^{n(e-j)}\,r_{\mathfrak p^j}(\nu)$, $r_{\mathfrak p^j}$ = `LocalDensity.NF.repCount`.
* `locFactor_eventually_eq` (**the local factor**): $\lambda_\mathfrak p(e) = N\mathfrak p^{e(1-n)}\mathrm{cnt}(\mathfrak p^e)$ equals
  $N(\mathfrak d_\mathfrak p)\,\beta_\mathfrak p(\nu)$ for all large $e$, with $N(\mathfrak d_\mathfrak p) = N\mathfrak p^{\delta_\mathfrak p}$ and
  $\beta_\mathfrak p$ = `LocalDensity.NF.localDensity` (Hanke (5.1)–(5.2): $\operatorname{Vol}(\mathfrak o_\mathfrak p) = 1$).

So the local factor of the singular series at $\mathfrak p$ is **$N(\mathfrak d_\mathfrak p)\beta_\mathfrak p(\nu)$, not $\beta_\mathfrak p(\nu)$**: summing
$e(\operatorname{Tr}(u\,\cdot))$ over $u \in \mathfrak p^{-e}/\mathcal O$ detects congruences modulo $\mathfrak p^{e}\mathfrak d_\mathfrak p^{-1}$, so there are
$N\mathfrak p^{n\delta_\mathfrak p}$ times more solutions than modulo $\mathfrak p^e$, against the normalization $N\mathfrak p^{-e(n-1)}$.
Over $\mathbb Q$, $\mathfrak d = (1)$ and this is `Siegel.sum_ssTerm_prime_pow`.

Sources: Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. Math. 36 (1935), §§ 3–5 (the singular
series as Gauss sums) [unverified]; Siegel, *Über die Klassenzahl quadratischer Zahlkörper / analytische Theorie III*,
Ann. Math. 38 (1937) (the series over a number field) [unverified]; Hanke 2004, (5.1)–(5.2), p. 368.
-/
import QuadFormsKB.HilbertModular.ThetaGenusInv
import QuadFormsKB.LocalDensity.NFLocal
import QuadFormsKB.Siegel.NFMainTerm

open NumberField IsDedekindDomain Complex Filter Topology
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.SiegelWeil.SingularNF

open QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-! ### The additive character $e(\operatorname{Tr}\,\cdot)$ -/

/-- **The standard additive character of $F$**: $e(\operatorname{Tr}_{F/\mathbb Q}x) = \exp(2\pi i\operatorname{Tr}x)$. -/
def eTr (x : F) : ℂ := cexp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ))

lemma eTr_add (x y : F) : eTr (x + y) = eTr x * eTr y := by
  simp only [eTr, map_add, Rat.cast_add, mul_add, Complex.exp_add]

lemma eTr_zero : eTr (0 : F) = 1 := by simp [eTr]

lemma eTr_neg (x : F) : eTr (-x) = (eTr x)⁻¹ := by
  simp only [eTr, map_neg, Rat.cast_neg, mul_neg, Complex.exp_neg]

lemma eTr_of_mem {y : F} (hy : y ∈ invDifferent F) : eTr y = 1 := cexp_trace_eq_one hy

lemma eTr_add_of_mem {x y : F} (hy : y ∈ invDifferent F) : eTr (x + y) = eTr x := by
  rw [eTr_add, eTr_of_mem hy, mul_one]

lemma eTr_eq_one_iff (x : F) : eTr x = 1 ↔ ∃ m : ℤ, Algebra.trace ℚ F x = m := by
  rw [eTr, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((m : ℚ) : ℂ) := by
      apply mul_left_cancel₀ h2
      rw [hm]; push_cast; ring
    exact_mod_cast this
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hm]; push_cast; ring⟩

/-- $\mathfrak d^{-1}$ is the trace dual of $\mathcal O$: $y \in \mathfrak d^{-1}$ iff $e(\operatorname{Tr}(ry)) = 1$ for all $r \in \mathcal O$. -/
lemma mem_invDifferent_iff_eTr (y : F) : y ∈ invDifferent F ↔ ∀ r : 𝓞 F, eTr (ιO r * y) = 1 := by
  rw [invDifferent, FractionalIdeal.mem_dual (one_ne_zero)]
  constructor
  · intro h r
    obtain ⟨m, hm⟩ := h (ιO r) ((FractionalIdeal.mem_one_iff _).mpr ⟨r, rfl⟩)
    rw [eTr_eq_one_iff]
    refine ⟨m, ?_⟩
    rw [mul_comm]
    simpa [Algebra.traceForm_apply] using hm.symm
  · intro h a ha
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨m, hm⟩ := (eTr_eq_one_iff _).mp (h r)
    refine ⟨m, ?_⟩
    rw [Algebra.traceForm_apply, mul_comm]
    simp [hm]

/-! ### Orthogonality over $\mathcal O/c$ -/

lemma finite_quot_span {c : 𝓞 F} (hc : c ≠ 0) : Finite (𝓞 F ⧸ Ideal.span {c}) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa [Ideal.span_singleton_eq_bot] using hc)

lemma algebraMap_ne_zero {c : 𝓞 F} (hc : c ≠ 0) : ιO c ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hc

/-- The character $d \mapsto e(\operatorname{Tr}(\tilde dy/c))$ of $\mathcal O/c$ is well defined for $y \in \mathfrak d^{-1}$. -/
lemma eTr_div_congr {c : 𝓞 F} (hc : c ≠ 0) {y : F} (hy : y ∈ invDifferent F) {a b : 𝓞 F}
    (h : Ideal.Quotient.mk (Ideal.span {c}) a = Ideal.Quotient.mk (Ideal.span {c}) b) :
    eTr (ιO a * y / ιO c) = eTr (ιO b * y / ιO c) := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp h)
  have : ιO a * y / ιO c = ιO b * y / ιO c + ιO t * y := by
    have ha : a = b + t * c := by rw [ht]; ring
    rw [ha, map_add, map_mul]; field_simp [algebraMap_ne_zero hc]
  rw [this, eTr_add_of_mem (algebraMap_mul_mem_invDifferent t hy)]

open Classical in
/-- **Orthogonality of the characters of $\mathcal O/c$**: for $c \ne 0$ and $y \in \mathfrak d^{-1}$,
$$\sum_{d\in\mathcal O/c}e\Big(\operatorname{Tr}\frac{\tilde d\,y}{c}\Big) = \begin{cases}N(c) & y/c \in \mathfrak d^{-1},\\ 0 & \text{otherwise.}\end{cases}$$ -/
theorem sum_eTr_div {c : 𝓞 F} (hc : c ≠ 0) {y : F} (hy : y ∈ invDifferent F) :
    ∑ᶠ d : 𝓞 F ⧸ Ideal.span {c}, eTr (ιO (Quotient.out d) * y / ιO c) =
      if y / ιO c ∈ invDifferent F then (Ideal.absNorm (Ideal.span {c}) : ℂ) else 0 := by
  classical
  haveI := finite_quot_span hc
  letI : Fintype (𝓞 F ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  set ψ : 𝓞 F ⧸ Ideal.span {c} → ℂ := fun d => eTr (ιO (Quotient.out d) * y / ιO c)
  have hψadd : ∀ d d', ψ (d + d') = ψ d * ψ d' := by
    intro d d'
    have hmk : Ideal.Quotient.mk (Ideal.span {c}) (Quotient.out (d + d')) =
        Ideal.Quotient.mk (Ideal.span {c}) (Quotient.out d + Quotient.out d') := by
      rw [map_add]
      simp only [Ideal.Quotient.mk_out]
    simp only [ψ]
    rw [eTr_div_congr hc hy hmk, map_add, add_mul, add_div, eTr_add]
  split_ifs with hyc
  · have h1 : ∀ d, ψ d = 1 := fun d => by
      simp only [ψ]
      rw [mul_div_assoc]
      exact eTr_of_mem (algebraMap_mul_mem_invDifferent _ hyc)
    rw [Finset.sum_congr rfl fun d _ => h1 d]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  · -- a nontrivial character sums to zero
    have : ∃ r : 𝓞 F, eTr (ιO r * (y / ιO c)) ≠ 1 := by
      by_contra h; push Not at h
      exact hyc ((mem_invDifferent_iff_eTr _).mpr h)
    obtain ⟨r, hr⟩ := this
    set d₀ : 𝓞 F ⧸ Ideal.span {c} := Ideal.Quotient.mk _ r
    have hd₀ : ψ d₀ ≠ 1 := by
      simp only [ψ, d₀]
      rw [eTr_div_congr hc hy (Ideal.Quotient.mk_out _)]
      rwa [mul_div_assoc]
    have hshift : ∑ d, ψ d = ψ d₀ * ∑ d, ψ d := by
      have h := Fintype.sum_equiv (Equiv.addLeft d₀) (fun d => ψ (d₀ + d)) ψ (fun _ => rfl)
      calc ∑ d, ψ d = ∑ d, ψ (d₀ + d) := h.symm
        _ = ∑ d, ψ d₀ * ψ d := Finset.sum_congr rfl fun d _ => hψadd d₀ d
        _ = ψ d₀ * ∑ d, ψ d := (Finset.mul_sum _ _ _).symm
    have : (ψ d₀ - 1) * ∑ d, ψ d = 0 := by rw [sub_mul, ← hshift]; ring
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hd₀)

/-! ### The different and the trace dual -/

/-- **The different** $\mathfrak d = \mathfrak d_{F/\mathbb Q}$ as an integral ideal (Mathlib's `differentIdeal ℤ (𝓞 F)`). -/
abbrev dif (F : Type) [Field F] [NumberField F] : Ideal (𝓞 F) := differentIdeal ℤ (𝓞 F)

lemma coe_dif : ((dif F : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (invDifferent F)⁻¹ :=
  coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)

lemma invDifferent_eq_inv_dif : invDifferent F = ((dif F : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
  rw [coe_dif, inv_inv]

lemma dif_ne_bot : dif F ≠ ⊥ := differentIdeal_ne_bot

/-- **$y/c \in \mathfrak d^{-1}$ iff $y\,\mathfrak d \subseteq c\mathcal O$** ($y, c \in \mathcal O$, $c \ne 0$). -/
theorem div_mem_invDifferent_iff (y : 𝓞 F) {c : 𝓞 F} (hc : c ≠ 0) :
    ιO y / ιO c ∈ invDifferent F ↔ Ideal.span {y} * dif F ≤ Ideal.span {c} := by
  have hd0 : ((dif F : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact dif_ne_bot
  rw [invDifferent_eq_inv_dif, FractionalIdeal.mem_inv_iff hd0, Ideal.span_singleton_mul_le_iff]
  have hc' := algebraMap_ne_zero hc
  constructor
  · intro h δ hδ
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp
      (h (ιO δ) ((FractionalIdeal.mem_coeIdeal _).mpr ⟨δ, hδ, rfl⟩))
    refine Ideal.mem_span_singleton'.mpr ⟨r, ?_⟩
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [map_mul, map_mul, hr]; field_simp
  · intro h x hx
    obtain ⟨δ, hδ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hx
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (h δ hδ)
    refine (FractionalIdeal.mem_one_iff _).mpr ⟨r, ?_⟩
    have := congrArg ιO hr
    rw [map_mul, map_mul] at this
    field_simp
    rw [this]

/-! ### Gauss averages and the truncated singular series -/

/-- The lift $\tilde r \in \mathcal O^n$ of $r \in (\mathcal O/I)^n$ (`Quotient.out` in each coordinate). -/
def liftV {I : Ideal (𝓞 F)} (r : Fin n → 𝓞 F ⧸ I) : Fin n → 𝓞 F := fun i => Quotient.out (r i)

/-- **The normalized Gauss sum of $Q$ with modulus $c$**:
$G_Q(u; c) = N(c)^{-n}\sum_{r\in(\mathcal O/c)^n}e(\operatorname{Tr}(u\,Q(\tilde r)))$, $u \in F$, $c \in \mathcal O$
(meaningful for $c \ne 0$ and $cu \in \mathcal O$, where it does not depend on the lift or on $c$: `gAvg_eq_of_dvd`). -/
@[kb "siegel1935" "§3, the Gauss sums of the singular series [unverified]"]
def gAvg (Q : QuadForm (𝓞 F) n) (c : 𝓞 F) (u : F) : ℂ :=
  ((Ideal.absNorm (Ideal.span {c}) : ℂ) ^ n)⁻¹ *
    ∑ᶠ r : Fin n → 𝓞 F ⧸ Ideal.span {c}, eTr (u * ιO (Q.eval (liftV r)))

/-- **The truncated singular series** at $\nu \in F$ with modulus $c$:
$$S_c(\nu) = \sum_{d\in\mathcal O/c}G_Q(\tilde d/c; c)\,e\big(-\operatorname{Tr}(\nu\,\tilde d/c)\big),$$
the part of the singular series $\sum_{u\in F/\mathcal O}G_Q(u)e(-\operatorname{Tr}\nu u)$ with $cu \in \mathcal O$. -/
@[kb "siegel1935" "§3–5, the singular series, truncated [unverified]"]
def ssTrunc (Q : QuadForm (𝓞 F) n) (c : 𝓞 F) (ν : F) : ℂ :=
  ∑ᶠ d : 𝓞 F ⧸ Ideal.span {c},
    gAvg Q c (ιO (Quotient.out d) / ιO c) * eTr (-(ν * (ιO (Quotient.out d) / ιO c)))

/-- **The congruence condition modulo $I$ twisted by the different**: $(Q(x) - \nu)\,\mathfrak d \subseteq I$. -/
def CondI (Q : QuadForm (𝓞 F) n) (I : Ideal (𝓞 F)) (ν : 𝓞 F) (x : Fin n → 𝓞 F) : Prop :=
  Ideal.span {Q.eval x - ν} * dif F ≤ I

/-- **The count** $\mathrm{cnt}_Q(I, \nu) = \#\{r \in (\mathcal O/I)^n : (Q(\tilde r) - \nu)\,\mathfrak d \subseteq I\}$. -/
def cnt (Q : QuadForm (𝓞 F) n) (I : Ideal (𝓞 F)) (ν : 𝓞 F) : ℕ :=
  Nat.card {r : Fin n → 𝓞 F ⧸ I // CondI Q I ν (liftV r)}

lemma finite_quot {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : Finite (𝓞 F ⧸ I) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ hI

lemma span_ne_bot {c : 𝓞 F} (hc : c ≠ 0) : Ideal.span {c} ≠ ⊥ := by
  simpa [Ideal.span_singleton_eq_bot] using hc

/-- **The truncated singular series is a count** (orthogonality, `sum_eTr_div`): for $c \ne 0$ and $\nu \in \mathcal O$,
$$S_c(\nu) = N(c)^{1-n}\,\#\{r \in (\mathcal O/c)^n : (Q(\tilde r) - \nu)\,\mathfrak d \subseteq c\mathcal O\}.$$ -/
@[kb "siegel1935" "§3, the singular series as a congruence count [unverified]"]
theorem ssTrunc_eq_count (Q : QuadForm (𝓞 F) n) {c : 𝓞 F} (hc : c ≠ 0) (ν : 𝓞 F) :
    ssTrunc Q c (ιO ν) = ((Ideal.absNorm (Ideal.span {c}) : ℂ) ^ n)⁻¹ *
      (Ideal.absNorm (Ideal.span {c}) : ℂ) * (cnt Q (Ideal.span {c}) ν : ℂ) := by
  classical
  haveI := finite_quot_span hc
  letI : Fintype (𝓞 F ⧸ Ideal.span {c}) := Fintype.ofFinite _
  set N : ℂ := (Ideal.absNorm (Ideal.span {c}) : ℂ)
  have hc' := algebraMap_ne_zero hc
  unfold ssTrunc gAvg
  simp only [finsum_eq_sum_of_fintype, mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  have hterm : ∀ (r : Fin n → 𝓞 F ⧸ Ideal.span {c}) (d : 𝓞 F ⧸ Ideal.span {c}),
      eTr (ιO (Quotient.out d) / ιO c * ιO (Q.eval (liftV r))) *
        eTr (-(ιO ν * (ιO (Quotient.out d) / ιO c))) =
      eTr (ιO (Quotient.out d) * ιO (Q.eval (liftV r) - ν) / ιO c) := by
    intro r d
    rw [← eTr_add]
    congr 1
    rw [map_sub]; field_simp; ring
  simp_rw [hterm]
  have hsum : ∀ r : Fin n → 𝓞 F ⧸ Ideal.span {c},
      ∑ d : 𝓞 F ⧸ Ideal.span {c}, eTr (ιO (Quotient.out d) * ιO (Q.eval (liftV r) - ν) / ιO c) =
        if CondI Q (Ideal.span {c}) ν (liftV r) then N else 0 := by
    intro r
    have h := sum_eTr_div hc (algebraMap_mem_invDifferent (Q.eval (liftV r) - ν))
    rw [finsum_eq_sum_of_fintype] at h
    rw [h, div_mem_invDifferent_iff _ hc]
    rfl
  simp_rw [hsum]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  rw [cnt, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-! ### The count depends only on residues -/

lemma mk_eval (Q : QuadForm (𝓞 F) n) (J : Ideal (𝓞 F)) (x : Fin n → 𝓞 F) :
    Ideal.Quotient.mk J (Q.eval x) = Q.evalIn (𝓞 F ⧸ J) (fun i => Ideal.Quotient.mk J (x i)) := by
  simp [QuadForm.evalIn, map_sum, apply_ite, Ideal.Quotient.algebraMap_eq]

lemma span_mul_dif_le_of_sub_mem {J : Ideal (𝓞 F)} {a b : 𝓞 F} (hab : a - b ∈ J)
    (hb : Ideal.span {b} * dif F ≤ J) : Ideal.span {a} * dif F ≤ J := by
  rw [Ideal.span_singleton_mul_le_iff] at hb ⊢
  intro z hz
  rw [show a * z = b * z + (a - b) * z by ring]
  exact J.add_mem (hb z hz) (J.mul_mem_right z hab)

lemma condI_congr (Q : QuadForm (𝓞 F) n) (J : Ideal (𝓞 F)) (ν : 𝓞 F) {x x' : Fin n → 𝓞 F}
    (h : ∀ i, Ideal.Quotient.mk J (x i) = Ideal.Quotient.mk J (x' i)) :
    CondI Q J ν x ↔ CondI Q J ν x' := by
  have hQ : Q.eval x - Q.eval x' ∈ J := by
    rw [← Ideal.Quotient.eq, mk_eval, mk_eval]
    simp only [h]
  constructor
  · intro hc
    refine span_mul_dif_le_of_sub_mem ?_ hc
    rw [show Q.eval x' - ν - (Q.eval x - ν) = -(Q.eval x - Q.eval x') by ring]
    exact J.neg_mem hQ
  · intro hc
    refine span_mul_dif_le_of_sub_mem ?_ hc
    rwa [show Q.eval x - ν - (Q.eval x' - ν) = Q.eval x - Q.eval x' by ring]

/-! ### The Chinese remainder theorem -/

/-- The exponent $v_\mathfrak p(I)$ of $\mathfrak p$ in a nonzero ideal $I$. -/
def ordI (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk I).factors

lemma pow_dvd_iff_le_ordI (v : HeightOneSpectrum (𝓞 F)) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (m : ℕ) :
    v.asIdeal ^ m ∣ I ↔ m ≤ ordI v I := by
  rw [← Associates.mk_dvd_mk, Associates.mk_pow]
  exact Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hI) v.associates_irreducible

lemma ordI_mul (v : HeightOneSpectrum (𝓞 F)) {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    ordI v (I * J) = ordI v I + ordI v J := by
  rw [ordI, ← Associates.mk_mul_mk]
  exact Associates.count_mul (Associates.mk_ne_zero.mpr hI) (Associates.mk_ne_zero.mpr hJ)
    v.associates_irreducible

/-- **The exponent $\delta_\mathfrak p$ of $\mathfrak p$ in the different** $\mathfrak d$: $N(\mathfrak d_\mathfrak p) = N\mathfrak p^{\delta_\mathfrak p}$;
$\delta_\mathfrak p > 0$ iff $\mathfrak p$ is ramified over $\mathbb Q$ (Dedekind). -/
def diffExpNF (v : HeightOneSpectrum (𝓞 F)) : ℕ := ordI v (dif F)

/-- **The condition at a prime power** (every prime, dyadic included): $(y)\,\mathfrak d \subseteq \mathfrak p^e$ iff
$y \in \mathfrak p^{e - \delta_\mathfrak p}$ (truncated subtraction). -/
theorem span_mul_dif_le_pow_iff (v : HeightOneSpectrum (𝓞 F)) (y : 𝓞 F) (e : ℕ) :
    Ideal.span {y} * dif F ≤ v.asIdeal ^ e ↔ y ∈ v.asIdeal ^ (e - diffExpNF v) := by
  by_cases hy : y = 0
  · subst hy; simp
  have hs : Ideal.span {y} ≠ ⊥ := span_ne_bot hy
  rw [← Ideal.dvd_iff_le, pow_dvd_iff_le_ordI v (mul_ne_zero hs dif_ne_bot), ordI_mul v hs dif_ne_bot,
    ← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le, pow_dvd_iff_le_ordI v hs, diffExpNF]
  omega

lemma mem_iff_forall_of_prod_eq {T : Finset (HeightOneSpectrum (𝓞 F))} (e : HeightOneSpectrum (𝓞 F) → ℕ)
    {I : Ideal (𝓞 F)} (hI : ∏ v ∈ T, v.asIdeal ^ e v = I) (x : 𝓞 F) :
    x ∈ I ↔ ∀ v ∈ T, x ∈ v.asIdeal ^ e v := by
  have h := inf_pow_eq_prod_of_prime T (fun v => v.asIdeal) e
    (fun v _ => Ideal.prime_of_isPrime v.ne_bot v.isPrime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h))
  rw [← hI, ← h, Submodule.mem_finsetInf]

lemma le_iff_forall_of_prod_eq {T : Finset (HeightOneSpectrum (𝓞 F))} (e : HeightOneSpectrum (𝓞 F) → ℕ)
    {I : Ideal (𝓞 F)} (hI : ∏ v ∈ T, v.asIdeal ^ e v = I) (X : Ideal (𝓞 F)) :
    X ≤ I ↔ ∀ v ∈ T, X ≤ v.asIdeal ^ e v := by
  constructor
  · intro h v hv x hx
    exact (mem_iff_forall_of_prod_eq e hI x).mp (h hx) v hv
  · intro h x hx
    exact (mem_iff_forall_of_prod_eq e hI x).mpr fun v hv => h v hv hx

/-- **The count is multiplicative** (Chinese remainder theorem over $\mathcal O_F$): if $I = \prod_{\mathfrak p\in T}\mathfrak p^{e_\mathfrak p}$
(distinct primes) then $\mathrm{cnt}_Q(I, \nu) = \prod_{\mathfrak p\in T}\mathrm{cnt}_Q(\mathfrak p^{e_\mathfrak p}, \nu)$. -/
@[kb "siegel1935" "§3, multiplicativity of the singular series (CRT) [unverified]"]
theorem cnt_eq_prod (Q : QuadForm (𝓞 F) n) (ν : 𝓞 F) {T : Finset (HeightOneSpectrum (𝓞 F))}
    (e : HeightOneSpectrum (𝓞 F) → ℕ) {I : Ideal (𝓞 F)} (hI : ∏ v ∈ T, v.asIdeal ^ e v = I) :
    cnt Q I ν = ∏ v ∈ T, cnt Q (v.asIdeal ^ e v) ν := by
  classical
  have hprod : ∏ v : T, (v : HeightOneSpectrum (𝓞 F)).asIdeal ^ e v = I := by
    rw [← hI]; exact Finset.prod_coe_sort T fun v => v.asIdeal ^ e v
  let E := HeightOneSpectrum.quotientEquivPiOfProdEq I (fun v : T => (v : HeightOneSpectrum (𝓞 F)))
    (fun v => e v) (fun a b h => Subtype.coe_injective.ne h) hprod
  have hE : ∀ (a : 𝓞 F) (v : T), E (Ideal.Quotient.mk I a) v = Ideal.Quotient.mk _ a := fun a v => rfl
  let V : (Fin n → 𝓞 F ⧸ I) ≃ (∀ v : T, Fin n → 𝓞 F ⧸ (v : HeightOneSpectrum (𝓞 F)).asIdeal ^ e v) :=
    (Equiv.piCongrRight fun _ => E.toEquiv).trans (Equiv.piComm _)
  have hV : ∀ r (v : T) i, V r v i = Ideal.Quotient.mk _ (Quotient.out (r i)) := by
    intro r v i
    change E (r i) v = _
    conv_lhs => rw [← Ideal.Quotient.mk_out (r i)]
    exact hE _ v
  have hiff : ∀ r : Fin n → 𝓞 F ⧸ I, CondI Q I ν (liftV r) ↔
      ∀ v : T, CondI Q ((v : HeightOneSpectrum (𝓞 F)).asIdeal ^ e v) ν (liftV (V r v)) := by
    intro r
    rw [CondI, le_iff_forall_of_prod_eq e hI]
    constructor
    · intro h v
      refine (condI_congr Q _ ν fun i => ?_).mpr (h v v.2)
      simp only [liftV, Ideal.Quotient.mk_out, hV]
    · intro h v hv
      refine (condI_congr Q _ ν fun i => ?_).mp (h ⟨v, hv⟩)
      simp only [liftV, Ideal.Quotient.mk_out, hV]
  let P : ∀ v : T, (Fin n → 𝓞 F ⧸ (v : HeightOneSpectrum (𝓞 F)).asIdeal ^ e v) → Prop :=
    fun v x => CondI Q ((v : HeightOneSpectrum (𝓞 F)).asIdeal ^ e v) ν (liftV x)
  have e1 : {r : Fin n → 𝓞 F ⧸ I // CondI Q I ν (liftV r)} ≃
      {s : ∀ v : T, Fin n → 𝓞 F ⧸ (v : HeightOneSpectrum (𝓞 F)).asIdeal ^ e v // ∀ v : T, P v (s v)} :=
    Equiv.subtypeEquiv V hiff
  have e2 : {s : ∀ v : T, Fin n → 𝓞 F ⧸ (v : HeightOneSpectrum (𝓞 F)).asIdeal ^ e v // ∀ v : T, P v (s v)} ≃
      ∀ v : T, {x // P v x} := Equiv.subtypePiEquivPi
  have h1 : cnt Q I ν = ∏ v : T, Nat.card {x // P v x} := by
    rw [cnt, Nat.card_congr (e1.trans e2), Nat.card_pi]
  rw [h1]
  exact Finset.prod_coe_sort T fun v => cnt Q (v.asIdeal ^ e v) ν

/-! ### Counting along a reduction map -/

/-- **Fibres of a surjective homomorphism**: for a surjective additive homomorphism $f : G \to H$ of finite groups and a
predicate $p$ on $H$, $\#\{g : p(f g)\}\cdot\#H = \#\{h : p\,h\}\cdot\#G$. -/
lemma card_pred_comp_mul {G H : Type*} [AddGroup G] [AddGroup H] [Fintype G] [Fintype H] [DecidableEq H]
    (f : G →+ H) (hf : Function.Surjective f) (p : H → Prop) [DecidablePred p] :
    Fintype.card {g // p (f g)} * Fintype.card H = Fintype.card {h // p h} * Fintype.card G := by
  classical
  set K := (Finset.univ.filter fun g : G => f g = 0).card
  have hfib : ∀ h : H, (Finset.univ.filter fun g : G => f g = h).card = K := fun h =>
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf h) (hf 0)
  have hG : Fintype.card G = Fintype.card H * K := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hP : Fintype.card {g // p (f g)} = Fintype.card {h // p h} * K := by
    rw [Fintype.card_subtype, Fintype.card_subtype,
      Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ.filter p) (fun g hg => by
        simpa using hg)]
    rw [Finset.card_eq_sum_ones (Finset.univ.filter p), Finset.sum_mul, one_mul]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [← hfib h]
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h' => h'.2
    · intro h'; exact ⟨by rw [h']; simpa using hh, h'⟩
  rw [hG, hP]; ring

lemma card_quot_eq_absNorm (I : Ideal (𝓞 F)) : Nat.card (𝓞 F ⧸ I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- **The reduction count**: for $J \le I$ nonzero ideals of $\mathcal O_F$ and any predicate $p$ on $(\mathcal O/I)^n$,
$\#\{r \in (\mathcal O/J)^n : p(\bar r)\}\cdot N(I)^n = \#\{s \in (\mathcal O/I)^n : p(s)\}\cdot N(J)^n$. -/
lemma natCard_reduce {J I : Ideal (𝓞 F)} (hJ : J ≠ ⊥) (hJI : J ≤ I) (p : (Fin n → 𝓞 F ⧸ I) → Prop) :
    Nat.card {r : Fin n → 𝓞 F ⧸ J // p (fun i => Ideal.Quotient.factor hJI (r i))} * Ideal.absNorm I ^ n =
      Nat.card {s : Fin n → 𝓞 F ⧸ I // p s} * Ideal.absNorm J ^ n := by
  classical
  have hI : I ≠ ⊥ := fun h => hJ (le_bot_iff.mp (h ▸ hJI))
  haveI := finite_quot hJ
  haveI := finite_quot hI
  letI : Fintype (𝓞 F ⧸ J) := Fintype.ofFinite _
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  set f : (Fin n → 𝓞 F ⧸ J) →+ (Fin n → 𝓞 F ⧸ I) :=
    AddMonoidHom.compLeft (Ideal.Quotient.factor hJI).toAddMonoidHom (Fin n)
  have hf : Function.Surjective f := by
    intro s
    choose r hr using fun i => Ideal.Quotient.factor_surjective hJI (s i)
    exact ⟨r, funext hr⟩
  have h := card_pred_comp_mul f hf p
  rw [← card_quot_eq_absNorm, ← card_quot_eq_absNorm, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin] at h
  convert h using 3
  rfl

/-- **The local count at a prime power** (every prime $\mathfrak p$, dyadic included): with $\delta = \delta_\mathfrak p$ and
$j = e - \delta$ (truncated),
$$\mathrm{cnt}_Q(\mathfrak p^e, \nu)\cdot N\mathfrak p^{nj} = r_{\mathfrak p^j}(\nu)\cdot N\mathfrak p^{ne},$$
i.e. $\mathrm{cnt}_Q(\mathfrak p^e, \nu) = N\mathfrak p^{n\min(e,\delta)}\,r_{\mathfrak p^{e-\delta}}(\nu)$. -/
@[kb "siegel1935" "§3, local factors of the singular series over F [unverified]"]
theorem cnt_prime_pow (Q : QuadForm (𝓞 F) n) (ν : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (e : ℕ) :
    cnt Q (v.asIdeal ^ e) ν * Ideal.absNorm v.asIdeal ^ (n * (e - diffExpNF v)) =
      LocalDensity.NF.repCount v Q (e - diffExpNF v) ν * Ideal.absNorm v.asIdeal ^ (n * e) := by
  set j := e - diffExpNF v
  have hJ : v.asIdeal ^ e ≠ ⊥ := pow_ne_zero _ v.ne_bot
  have hJI : v.asIdeal ^ e ≤ v.asIdeal ^ j := Ideal.pow_le_pow_right (Nat.sub_le _ _)
  have h := natCard_reduce (n := n) hJ hJI
    (fun s => Q.evalIn (𝓞 F ⧸ v.asIdeal ^ j) s = Ideal.Quotient.mk _ ν)
  rw [map_pow, map_pow, ← pow_mul, ← pow_mul, mul_comm j n, mul_comm e n] at h
  have hc : cnt Q (v.asIdeal ^ e) ν = Nat.card {r : Fin n → 𝓞 F ⧸ v.asIdeal ^ e //
      Q.evalIn (𝓞 F ⧸ v.asIdeal ^ j) (fun i => Ideal.Quotient.factor hJI (r i)) = Ideal.Quotient.mk _ ν} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun r => ?_)
    rw [CondI, span_mul_dif_le_pow_iff, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, mk_eval]
    have : ∀ i, Ideal.Quotient.mk (v.asIdeal ^ j) (liftV r i) = Ideal.Quotient.factor hJI (r i) := by
      intro i
      rw [← Ideal.Quotient.factor_mk hJI, liftV, Ideal.Quotient.mk_out]
    rw [show (fun i => Ideal.Quotient.mk (v.asIdeal ^ j) (liftV r i)) =
      fun i => Ideal.Quotient.factor hJI (r i) from funext this]
  rw [LocalDensity.NF.repCount, hc, h]

/-! ### The local factor -/

/-- **The local factor of the singular series at $\mathfrak p$, truncated at $\mathfrak p^e$**:
$\lambda_\mathfrak p(e) = N\mathfrak p^{e(1-n)}\,\mathrm{cnt}_Q(\mathfrak p^e, \nu)$ (written $(N\mathfrak p^{e})^{-n}N\mathfrak p^{e}\,\mathrm{cnt}$, the
normalization of `ssTrunc_eq_count`). -/
def locFactor (Q : QuadForm (𝓞 F) n) (ν : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (e : ℕ) : ℝ :=
  (((Ideal.absNorm v.asIdeal : ℝ) ^ e) ^ n)⁻¹ * (Ideal.absNorm v.asIdeal : ℝ) ^ e * (cnt Q (v.asIdeal ^ e) ν : ℝ)

lemma absNorm_pos (v : HeightOneSpectrum (𝓞 F)) : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)

/-- **The local factor in terms of $r_{\mathfrak p^j}$**: for $e \ge \delta_\mathfrak p$, $j = e - \delta_\mathfrak p$ and $n \ge 1$,
$$\lambda_\mathfrak p(e) = N\mathfrak p^{\delta_\mathfrak p}\cdot\frac{r_{\mathfrak p^j}(\nu)}{N\mathfrak p^{j(n-1)}}.$$ -/
theorem locFactor_eq (Q : QuadForm (𝓞 F) n) (hn : 1 ≤ n) (ν : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) {e : ℕ}
    (he : diffExpNF v ≤ e) :
    locFactor Q ν v e = (Ideal.absNorm v.asIdeal : ℝ) ^ diffExpNF v *
      ((LocalDensity.NF.repCount v Q (e - diffExpNF v) ν : ℝ) /
        (Ideal.absNorm v.asIdeal : ℝ) ^ ((e - diffExpNF v) * (n - 1))) := by
  set δ := diffExpNF v
  set j := e - δ with hj
  have hej : e = j + δ := by omega
  have hq := absNorm_pos v
  have h := congrArg (Nat.cast : ℕ → ℝ) (cnt_prime_pow Q ν v e)
  push_cast at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hc : (cnt Q (v.asIdeal ^ e) ν : ℝ) =
      (LocalDensity.NF.repCount v Q j ν : ℝ) * (Ideal.absNorm v.asIdeal : ℝ) ^ ((m + 1) * δ) := by
    have hpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ ((m + 1) * j) := pow_pos hq _
    apply mul_right_cancel₀ hpos.ne'
    rw [h, mul_assoc, ← pow_add]
    congr 2
    rw [hej]; ring
  rw [locFactor, hc, Nat.add_sub_cancel, hej]
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := hq.ne'
  field_simp
  ring

/-- **The local factor is eventually $N(\mathfrak d_\mathfrak p)\,\beta_\mathfrak p(\nu)$** (every prime, dyadic included; $Q$
nondegenerate, $\nu \ne 0$, $n \ge 1$): $\lambda_\mathfrak p(e) = N\mathfrak p^{\delta_\mathfrak p}\beta_\mathfrak p(\nu)$ for all large $e$, with
$\beta_\mathfrak p$ = `LocalDensity.NF.localDensity` (Hanke (5.1)–(5.2), $\operatorname{Vol}(\mathfrak o_\mathfrak p) = 1$). -/
@[kb "siegel1935" "§3–5, the local factor of the singular series over F is N(𝔡_𝔭)β_𝔭 [unverified]"]
theorem locFactor_eventually_eq (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {ν : 𝓞 F}
    (hν : ν ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    ∀ᶠ e in atTop, locFactor Q ν v e =
      (Ideal.absNorm v.asIdeal : ℝ) ^ diffExpNF v * LocalDensity.NF.localDensity v Q ν := by
  have h := LocalDensity.NF.localDensity_eventually_eq v Q hQ ν hν
  have ht : Tendsto (fun e : ℕ => e - diffExpNF v) atTop atTop := tendsto_sub_atTop_nat _
  filter_upwards [ht.eventually h, eventually_ge_atTop (diffExpNF v)] with e he hge
  rw [locFactor_eq Q hn ν v hge, he]

/-! ### The Gauss average does not depend on the modulus -/

/-- **Sums along a surjective homomorphism**: $\big(\sum_g\varphi(f g)\big)\cdot\#H = \big(\sum_h\varphi(h)\big)\cdot\#G$. -/
lemma sum_comp_mul {G H : Type*} [AddGroup G] [AddGroup H] [Fintype G] [Fintype H] [DecidableEq H]
    (f : G →+ H) (hf : Function.Surjective f) (φ : H → ℂ) :
    (∑ g, φ (f g)) * Fintype.card H = (∑ h, φ h) * Fintype.card G := by
  classical
  set K := (Finset.univ.filter fun g : G => f g = 0).card
  have hfib : ∀ h : H, (Finset.univ.filter fun g : G => f g = h).card = K := fun h =>
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf h) (hf 0)
  have hG : Fintype.card G = Fintype.card H * K := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hS : ∑ g, φ (f g) = (∑ h, φ h) * K := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := f) (f := fun g => φ (f g)), Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_congr rfl fun g hg => by rw [(Finset.mem_filter.mp hg).2], Finset.sum_const, hfib h,
      nsmul_eq_mul, mul_comm]
  rw [hS, hG]; push_cast; ring

/-- $u$ is $c$-integral: $cu \in \mathcal O$. -/
def IsDen (c : 𝓞 F) (u : F) : Prop := ∃ a : 𝓞 F, ιO a = ιO c * u

lemma eTr_mul_int_of_isDen {c : 𝓞 F} {u : F} (h : IsDen c u) (t : 𝓞 F) : eTr (u * ιO (c * t)) = 1 := by
  obtain ⟨a, ha⟩ := h
  apply eTr_of_mem
  rw [map_mul, ← mul_assoc, mul_comm u, ← ha, ← map_mul]
  exact algebraMap_mem_invDifferent _

/-- The summand of the Gauss sum depends only on $r \bmod c$ when $cu \in \mathcal O$. -/
lemma eTr_eval_congr (Q : QuadForm (𝓞 F) n) {c : 𝓞 F} {u : F} (h : IsDen c u) {x x' : Fin n → 𝓞 F}
    (hx : ∀ i, Ideal.Quotient.mk (Ideal.span {c}) (x i) = Ideal.Quotient.mk (Ideal.span {c}) (x' i)) :
    eTr (u * ιO (Q.eval x)) = eTr (u * ιO (Q.eval x')) := by
  have hQ : Ideal.Quotient.mk (Ideal.span {c}) (Q.eval x) = Ideal.Quotient.mk (Ideal.span {c}) (Q.eval x') := by
    rw [mk_eval, mk_eval]; simp only [hx]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hQ)
  have : Q.eval x = Q.eval x' + c * t := by rw [mul_comm c t, ht]; ring
  rw [this, map_add, mul_add, eTr_add, eTr_mul_int_of_isDen h, mul_one]

/-- **Changing the modulus**: $G_Q(u; cm) = G_Q(u; c)$ when $cu \in \mathcal O$ ($c, m \ne 0$). -/
theorem gAvg_mul (Q : QuadForm (𝓞 F) n) {c m : 𝓞 F} (hc : c ≠ 0) (hm : m ≠ 0) {u : F} (h : IsDen c u) :
    gAvg Q (c * m) u = gAvg Q c u := by
  classical
  have hcm : c * m ≠ 0 := mul_ne_zero hc hm
  have hle : Ideal.span {c * m} ≤ Ideal.span {c} :=
    Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right c m)
  haveI := finite_quot_span hc
  haveI := finite_quot_span hcm
  letI : Fintype (𝓞 F ⧸ Ideal.span {c}) := Fintype.ofFinite _
  letI : Fintype (𝓞 F ⧸ Ideal.span {c * m}) := Fintype.ofFinite _
  set f : (Fin n → 𝓞 F ⧸ Ideal.span {c * m}) →+ (Fin n → 𝓞 F ⧸ Ideal.span {c}) :=
    AddMonoidHom.compLeft (Ideal.Quotient.factor hle).toAddMonoidHom (Fin n)
  have hf : Function.Surjective f := by
    intro s
    choose r hr using fun i => Ideal.Quotient.factor_surjective hle (s i)
    exact ⟨r, funext hr⟩
  set φ : (Fin n → 𝓞 F ⧸ Ideal.span {c}) → ℂ := fun s => eTr (u * ιO (Q.eval (liftV s)))
  have hterm : ∀ r : Fin n → 𝓞 F ⧸ Ideal.span {c * m}, eTr (u * ιO (Q.eval (liftV r))) = φ (f r) := by
    intro r
    refine eTr_eval_congr Q h fun i => ?_
    simp only [f, liftV, AddMonoidHom.compLeft, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, Ideal.Quotient.mk_out]
    rw [← Ideal.Quotient.factor_mk hle, Ideal.Quotient.mk_out]
    rfl
  have hsum := sum_comp_mul f hf φ
  have hNc : (Fintype.card (Fin n → 𝓞 F ⧸ Ideal.span {c}) : ℂ) =
      (Ideal.absNorm (Ideal.span {c}) : ℂ) ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, card_quot_eq_absNorm]
    push_cast; rfl
  have hNcm : (Fintype.card (Fin n → 𝓞 F ⧸ Ideal.span {c * m}) : ℂ) =
      (Ideal.absNorm (Ideal.span {c * m}) : ℂ) ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, card_quot_eq_absNorm]
    push_cast; rfl
  rw [hNc, hNcm] at hsum
  unfold gAvg
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp_rw [hterm]
  have h0 : (Ideal.absNorm (Ideal.span {c}) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact span_ne_bot hc
  have h1 : (Ideal.absNorm (Ideal.span {c * m}) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact span_ne_bot hcm
  have hφ : ∑ g, φ (f g) = (∑ h, φ h) * (Ideal.absNorm (Ideal.span {c * m}) : ℂ) ^ n /
      (Ideal.absNorm (Ideal.span {c}) : ℂ) ^ n := by
    rw [eq_div_iff (pow_ne_zero _ h0), hsum]
  rw [hφ]
  field_simp
  rfl

lemma isDen_mul {c : 𝓞 F} {u : F} (h : IsDen c u) (m : 𝓞 F) : IsDen (c * m) u := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a * m, by rw [map_mul, ha, map_mul]; ring⟩

/-- **The Gauss average is independent of the modulus**: $G_Q(u; c) = G_Q(u; c')$ whenever $cu, c'u \in \mathcal O$. -/
theorem gAvg_eq_of_isDen (Q : QuadForm (𝓞 F) n) {c c' : 𝓞 F} (hc : c ≠ 0) (hc' : c' ≠ 0) {u : F}
    (h : IsDen c u) (h' : IsDen c' u) : gAvg Q c u = gAvg Q c' u := by
  rw [← gAvg_mul Q hc hc' h, mul_comm, gAvg_mul Q hc' hc h']

lemma exists_isDen (u : F) : ∃ c : 𝓞 F, c ≠ 0 ∧ IsDen c u := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) u
  refine ⟨b, nonZeroDivisors.ne_zero hb, a, ?_⟩
  have : ιO b ≠ 0 := algebraMap_ne_zero (nonZeroDivisors.ne_zero hb)
  field_simp

/-- A fixed denominator of $u \in F$: $\mathrm{den}(u) \ne 0$, $\mathrm{den}(u)\,u \in \mathcal O$. -/
def den (u : F) : 𝓞 F := (exists_isDen u).choose

lemma den_ne_zero (u : F) : den u ≠ 0 := (exists_isDen u).choose_spec.1

lemma isDen_den (u : F) : IsDen (den u) u := (exists_isDen u).choose_spec.2

/-- **The Gauss average of $Q$ at $u \in F$**: $G_Q(u) = G_Q(u; c)$ for any $c \ne 0$ with $cu \in \mathcal O$ (`gaussAvg_eq`). -/
@[kb "siegel1935" "§3, the normalized Gauss sum of the singular series [unverified]"]
def gaussAvg (Q : QuadForm (𝓞 F) n) (u : F) : ℂ := gAvg Q (den u) u

theorem gaussAvg_eq (Q : QuadForm (𝓞 F) n) {c : 𝓞 F} (hc : c ≠ 0) {u : F} (h : IsDen c u) :
    gaussAvg Q u = gAvg Q c u :=
  gAvg_eq_of_isDen Q (den_ne_zero u) hc (isDen_den u) h

/-- **$G_Q$ is $\mathcal O$-periodic**: $G_Q(u + b) = G_Q(u)$ for $b \in \mathcal O$. -/
theorem gaussAvg_add_int (Q : QuadForm (𝓞 F) n) (u : F) (b : 𝓞 F) :
    gaussAvg Q (u + ιO b) = gaussAvg Q u := by
  have h := isDen_den u
  have h' : IsDen (den u) (u + ιO b) := by
    obtain ⟨a, ha⟩ := h
    exact ⟨a + den u * b, by rw [map_add, ha, map_mul]; ring⟩
  rw [gaussAvg_eq Q (den_ne_zero u) h', gaussAvg]
  unfold gAvg
  congr 1
  refine finsum_congr fun r => ?_
  rw [add_mul, eTr_add, ← map_mul, eTr_of_mem (algebraMap_mem_invDifferent _), mul_one]

/-! ### The singular series as a sum over $F/\mathcal O$ -/

variable (F) in
/-- $\mathcal O_F$ as an additive subgroup of $F$. -/
def OSub : AddSubgroup F := (algebraMap (𝓞 F) F).range.toAddSubgroup

variable (F) in
/-- **$F/\mathcal O_F$**, the index set of the singular series. -/
abbrev FO := F ⧸ OSub F

lemma mem_OSub {x : F} : x ∈ OSub F ↔ ∃ b : 𝓞 F, ιO b = x := Iff.rfl

/-- **The summand of the singular series** at $u + \mathcal O \in F/\mathcal O$: $G_Q(u)\,e(-\operatorname{Tr}(\nu u))$ (representative
`Quotient.out`; independent of it for $\nu \in \mathfrak d^{-1}$, `ssFun_mk`). -/
def ssFun (Q : QuadForm (𝓞 F) n) (ν : F) (x : FO F) : ℂ :=
  gaussAvg Q (Quotient.out x) * eTr (-(ν * Quotient.out x))

theorem ssFun_mk (Q : QuadForm (𝓞 F) n) {ν : F} (hν : ν ∈ invDifferent F) (u : F) :
    ssFun Q ν (QuotientAddGroup.mk u) = gaussAvg Q u * eTr (-(ν * u)) := by
  have h : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk u : FO F)) : FO F) = QuotientAddGroup.mk u :=
    Quotient.out_eq _
  obtain ⟨b, hb⟩ := mem_OSub.mp (QuotientAddGroup.eq.mp h)
  rw [ssFun]
  generalize Quotient.out (QuotientAddGroup.mk u : FO F) = w at hb
  have hu : u = w + ιO b := by rw [hb]; ring
  subst hu
  have hνb : -(ν * ιO b) ∈ invDifferent F := by
    rw [mul_comm]; exact Submodule.neg_mem _ (algebraMap_mul_mem_invDifferent b hν)
  rw [gaussAvg_add_int, mul_add, neg_add, eTr_add, eTr_of_mem hνb, mul_one]

/-- **The singular series of $Q$ over $F$** at $\nu$:
$$\mathfrak S_Q(\nu) = \sum_{u\in F/\mathcal O}G_Q(u)\,e(-\operatorname{Tr}(\nu u)),\qquad G_Q(u) = N(c)^{-n}\sum_{r\in(\mathcal O/c)^n}e(\operatorname{Tr}(uQ(r)))\ (cu \in \mathcal O).$$
(`tsum`; absolutely convergent in use, the summability being a hypothesis where needed.) -/
@[kb "siegel1935" "§3–5, the singular series over a number field [unverified]"]
def singSeries (Q : QuadForm (𝓞 F) n) (ν : F) : ℂ := ∑' x : FO F, ssFun Q ν x

/-- The embedding $\mathcal O/c \to F/\mathcal O$, $d \mapsto \tilde d/c$. -/
def jmap (c : 𝓞 F) (d : 𝓞 F ⧸ Ideal.span {c}) : FO F := QuotientAddGroup.mk (ιO (Quotient.out d) / ιO c)

lemma jmap_injective {c : 𝓞 F} (hc : c ≠ 0) : Function.Injective (jmap c) := by
  intro d d' h
  obtain ⟨b, hb⟩ := mem_OSub.mp (QuotientAddGroup.eq.mp h)
  have hc' := algebraMap_ne_zero hc
  rw [← Ideal.Quotient.mk_out d, ← Ideal.Quotient.mk_out d', Ideal.Quotient.eq]
  refine Ideal.mem_span_singleton'.mpr ⟨-b, ?_⟩
  apply FaithfulSMul.algebraMap_injective (𝓞 F) F
  have : ιO b * ιO c = ιO (Quotient.out d') - ιO (Quotient.out d) := by
    rw [hb]; field_simp; ring
  rw [map_mul, map_neg, map_sub, neg_mul, this]; ring

lemma mk_mem_range_jmap {c : 𝓞 F} (hc : c ≠ 0) {u : F} (h : IsDen c u) :
    (QuotientAddGroup.mk u : FO F) ∈ Set.range (jmap c) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  have hc' := algebraMap_ne_zero hc
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp
    (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {c}) a)))
  rw [jmap, QuotientAddGroup.eq]
  refine mem_OSub.mpr ⟨-t, ?_⟩
  have hu : u = ιO a / ιO c := by rw [ha]; field_simp
  have := congrArg ιO ht
  rw [map_mul, map_sub] at this
  rw [hu, map_neg]
  field_simp
  linear_combination (-1 : F) * this

lemma isDen_of_mem_range_jmap {c : 𝓞 F} {x : FO F} (h : x ∈ Set.range (jmap c)) :
    IsDen c (Quotient.out x) := by
  obtain ⟨d, rfl⟩ := h
  have h' : (QuotientAddGroup.mk (Quotient.out (jmap c d)) : FO F) = jmap c d := Quotient.out_eq _
  rw [jmap, QuotientAddGroup.eq] at h'
  obtain ⟨b, hb⟩ := mem_OSub.mp h'
  by_cases hc : c = 0
  · exact ⟨0, by simp [hc]⟩
  refine ⟨Quotient.out d - c * b, ?_⟩
  have hc' := algebraMap_ne_zero hc
  have hx : Quotient.out (jmap c d) = ιO (Quotient.out d) / ιO c - ιO b := by
    simp only [jmap]
    linear_combination hb
  rw [hx, map_sub, map_mul]; field_simp

/-- **The truncated singular series is a partial sum of the singular series**: for $c \ne 0$ and $\nu \in \mathfrak d^{-1}$,
$S_c(\nu) = \sum_{d\in\mathcal O/c}\mathrm{ss}_Q(\nu)(\tilde d/c)$. -/
theorem ssTrunc_eq_sum_jmap (Q : QuadForm (𝓞 F) n) {c : 𝓞 F} (hc : c ≠ 0) {ν : F} (hν : ν ∈ invDifferent F) :
    ssTrunc Q c ν = ∑ᶠ d : 𝓞 F ⧸ Ideal.span {c}, ssFun Q ν (jmap c d) := by
  unfold ssTrunc
  refine finsum_congr fun d => ?_
  rw [jmap, ssFun_mk Q hν, gaussAvg_eq Q hc ⟨Quotient.out d, by field_simp [algebraMap_ne_zero hc]⟩]

/-- The truncated singular series as a `tsum` of an indicator. -/
theorem ssTrunc_eq_tsum_indicator (Q : QuadForm (𝓞 F) n) {c : 𝓞 F} (hc : c ≠ 0) {ν : F}
    (hν : ν ∈ invDifferent F) :
    ssTrunc Q c ν = ∑' x, (Set.range (jmap c)).indicator (ssFun Q ν) x := by
  classical
  haveI := finite_quot_span hc
  letI : Fintype (𝓞 F ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [ssTrunc_eq_sum_jmap Q hc hν, finsum_eq_sum_of_fintype, ← tsum_subtype,
    ← (Equiv.ofInjective _ (jmap_injective hc)).tsum_eq, tsum_fintype]
  rfl

lemma mem_range_jmap_mul {c : 𝓞 F} (hc : c ≠ 0) {m : 𝓞 F} (hm : m ≠ 0) {x : FO F}
    (h : x ∈ Set.range (jmap c)) : x ∈ Set.range (jmap (c * m)) := by
  have := mk_mem_range_jmap (mul_ne_zero hc hm) (isDen_mul (isDen_of_mem_range_jmap h) m)
  rwa [QuotientAddGroup.out_eq'] at this

/-! ### Factorization of ideals over a finset of primes -/

/-- The finite set of primes dividing a nonzero ideal. -/
def suppI {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (Ideal.finite_factors (I := I) (by simpa using hI)).toFinset

lemma mem_suppI {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ suppI hI ↔ v.asIdeal ∣ I := by
  simp [suppI]

lemma ordI_ne_zero_iff {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (v : HeightOneSpectrum (𝓞 F)) :
    ordI v I ≠ 0 ↔ v.asIdeal ∣ I :=
  Associates.count_ne_zero_iff_dvd (by simpa using hI) v.irreducible

/-- **Factorization over the support**: $I = \prod_{\mathfrak p \mid I}\mathfrak p^{v_\mathfrak p(I)}$. -/
theorem prod_suppI {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS : suppI hI ⊆ S) : ∏ v ∈ S, v.asIdeal ^ ordI v I = I := by
  have h := Ideal.finprod_heightOneSpectrum_factorization (I := I) (by simpa using hI)
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)] at h
  · exact h
  · intro v hv
    apply hS
    rw [mem_suppI, ← ordI_ne_zero_iff hI]
    intro h0
    apply hv
    simp only [HeightOneSpectrum.maxPowDividing]
    rw [show (Associates.mk v.asIdeal).count (Associates.mk I).factors = ordI v I from rfl, h0, pow_zero]

/-! ### Step A: the part of the singular series with denominators dividing a power of $c$ -/

/-- The elements of $F/\mathcal O$ with denominator dividing a power of $c$. -/
def Acl (c : 𝓞 F) : Set (FO F) := ⋃ E : ℕ, Set.range (jmap (c ^ E))

/-- **The truncated singular series at $c^E$ is a product of local factors** ($\nu \in \mathcal O$):
$S_{c^E}(\nu) = \prod_{\mathfrak p \mid c}\lambda_\mathfrak p(E\,v_\mathfrak p(c))$. -/
theorem ssTrunc_pow_eq_prod (Q : QuadForm (𝓞 F) n) {c : 𝓞 F} (hc : c ≠ 0) (ν : 𝓞 F) (E : ℕ) :
    ssTrunc Q (c ^ E) (ιO ν) = ∏ v ∈ suppI (span_ne_bot hc),
      ((locFactor Q ν v (E * ordI v (Ideal.span {c})) : ℝ) : ℂ) := by
  have hcE : c ^ E ≠ 0 := pow_ne_zero _ hc
  set T := suppI (span_ne_bot hc)
  have hprod : ∏ v ∈ T, v.asIdeal ^ (E * ordI v (Ideal.span {c})) = Ideal.span {c ^ E} := by
    rw [← Ideal.span_singleton_pow]
    conv_rhs => rw [← prod_suppI (span_ne_bot hc) (le_refl T)]
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← pow_mul, mul_comm]
  rw [ssTrunc_eq_count Q hcE, cnt_eq_prod Q ν (fun v => E * ordI v (Ideal.span {c})) hprod, ← hprod,
    map_prod]
  simp only [map_pow, locFactor]
  push_cast
  rw [← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

/-- **Step A**: for $c \ne 0$ and $\nu \in \mathcal O\setminus 0$ ($Q$ nondegenerate, $n \ge 1$), if the singular series converges
absolutely then its part over $\{u : c^Eu \in \mathcal O\text{ for some }E\}$ is $\prod_{\mathfrak p\mid c}N\mathfrak p^{\delta_\mathfrak p}\beta_\mathfrak p(\nu)$. -/
theorem tsum_indicator_Acl (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {ν : 𝓞 F}
    (hν : ν ≠ 0) (hsum : Summable fun x => ‖ssFun Q (ιO ν) x‖) {c : 𝓞 F} (hc : c ≠ 0) :
    ∑' x, (Acl c).indicator (ssFun Q (ιO ν)) x = ∏ v ∈ suppI (span_ne_bot hc),
      (((Ideal.absNorm v.asIdeal : ℝ) ^ diffExpNF v * LocalDensity.NF.localDensity v Q ν : ℝ) : ℂ) := by
  set T := suppI (span_ne_bot hc)
  have hν' : ιO ν ∈ invDifferent F := algebraMap_mem_invDifferent ν
  -- the truncations converge to the part over `Acl c`
  have hlim : Tendsto (fun E : ℕ => ssTrunc Q (c ^ E) (ιO ν)) atTop
      (𝓝 (∑' x, (Acl c).indicator (ssFun Q (ιO ν)) x)) := by
    simp_rw [fun E => ssTrunc_eq_tsum_indicator Q (pow_ne_zero E hc) hν']
    refine tendsto_tsum_of_dominated_convergence hsum (fun x => ?_) (Eventually.of_forall fun E x => ?_)
    · by_cases hx : x ∈ Acl c
      · obtain ⟨E₀, hE₀⟩ := Set.mem_iUnion.mp hx
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop E₀] with E hE
        have : x ∈ Set.range (jmap (c ^ E)) := by
          have h := mem_range_jmap_mul (pow_ne_zero E₀ hc) (pow_ne_zero (E - E₀) hc) hE₀
          rwa [← pow_add, Nat.add_sub_cancel' hE] at h
        simp only [Set.indicator_of_mem hx, Set.indicator_of_mem this]
      · refine tendsto_const_nhds.congr' (Eventually.of_forall fun E => ?_)
        have : x ∉ Set.range (jmap (c ^ E)) := fun h => hx (Set.mem_iUnion.mpr ⟨E, h⟩)
        simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem this]
    · by_cases h : x ∈ Set.range (jmap (c ^ E))
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, norm_zero]; exact norm_nonneg _
  -- the truncations are eventually the product of the local factors
  have hev : ∀ᶠ E : ℕ in atTop, ssTrunc Q (c ^ E) (ιO ν) = ∏ v ∈ T,
      (((Ideal.absNorm v.asIdeal : ℝ) ^ diffExpNF v * LocalDensity.NF.localDensity v Q ν : ℝ) : ℂ) := by
    have hall : ∀ v ∈ T, ∀ᶠ E : ℕ in atTop, locFactor Q ν v (E * ordI v (Ideal.span {c})) =
        (Ideal.absNorm v.asIdeal : ℝ) ^ diffExpNF v * LocalDensity.NF.localDensity v Q ν := by
      intro v hv
      have ho : 1 ≤ ordI v (Ideal.span {c}) :=
        Nat.one_le_iff_ne_zero.mpr ((ordI_ne_zero_iff (span_ne_bot hc) v).mpr
          ((mem_suppI (span_ne_bot hc) v).mp hv))
      have ht : Tendsto (fun E : ℕ => E * ordI v (Ideal.span {c})) atTop atTop :=
        tendsto_id.atTop_mul_const' (by exact_mod_cast ho)
      exact ht.eventually (locFactor_eventually_eq Q hQ hn hν v)
    filter_upwards [(Filter.eventually_all_finset T).mpr hall] with E hE
    rw [ssTrunc_pow_eq_prod Q hc ν E]
    exact Finset.prod_congr rfl fun v hv => by rw [hE v hv]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (by
    filter_upwards [hev] with E hE using hE.symm))

/-! ### Step B: all denominators -/

variable (F) in
/-- The cofinal moduli $c_X = X!$. -/
def cX (X : ℕ) : 𝓞 F := ((X.factorial : ℕ) : 𝓞 F)

lemma cX_ne_zero (X : ℕ) : cX F X ≠ 0 := by
  rw [cX, Nat.cast_ne_zero]; exact Nat.factorial_ne_zero X

variable (F) in
/-- The primes dividing $X!$. -/
def TX (X : ℕ) : Finset (HeightOneSpectrum (𝓞 F)) :=
  suppI (span_ne_bot (cX_ne_zero (F := F) X))

lemma natCast_mem_of_dvd {v : HeightOneSpectrum (𝓞 F)} {a b : ℕ} (hab : a ∣ b)
    (ha : (a : 𝓞 F) ∈ v.asIdeal) : (b : 𝓞 F) ∈ v.asIdeal := by
  obtain ⟨k, rfl⟩ := hab
  rw [Nat.cast_mul]; exact v.asIdeal.mul_mem_right _ ha

lemma mem_TX_of_le (v : HeightOneSpectrum (𝓞 F)) {X : ℕ} (hX : Ideal.absNorm v.asIdeal ≤ X) : v ∈ TX F X := by
  rw [TX, mem_suppI, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, cX]
  have hpos : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  exact natCast_mem_of_dvd (Nat.dvd_factorial hpos hX) (Ideal.absNorm_mem v.asIdeal)

lemma TX_mono : Monotone (TX F) := by
  intro X Y hXY v hv
  rw [TX, mem_suppI] at hv ⊢
  refine hv.trans ?_
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton, cX, cX]
  exact Nat.cast_dvd_cast (Nat.factorial_dvd_factorial hXY)

lemma tendsto_TX : Tendsto (TX F) atTop atTop :=
  Filter.tendsto_atTop_finset_of_monotone TX_mono fun v => ⟨_, mem_TX_of_le v le_rfl⟩

/-- **$\prod_\mathfrak pN(\mathfrak d_\mathfrak p) = |d_F|$** over any finite set of primes containing the ramified ones (Dedekind;
Mathlib's `NumberField.absNorm_differentIdeal`). -/
theorem prod_absNorm_pow_diffExp {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : suppI (dif_ne_bot (F := F)) ⊆ S) :
    ∏ v ∈ S, (Ideal.absNorm v.asIdeal : ℝ) ^ diffExpNF v = ((discr F).natAbs : ℝ) := by
  have h := congrArg (fun I => (Ideal.absNorm I : ℝ)) (prod_suppI (dif_ne_bot (F := F)) hS)
  simp only [map_prod, map_pow, Nat.cast_prod, Nat.cast_pow] at h
  rw [← NumberField.absNorm_differentIdeal F (𝓞 F)]
  exact h

/-- **The singular series over $F$ is $|d_F|$ times the Euler product of the local densities** (every prime, dyadic
included): for $Q$ nondegenerate over $\mathcal O_F$, $n \ge 1$, $\nu \in \mathcal O_F\setminus 0$, if
$\sum_{u\in F/\mathcal O}|G_Q(u)| < \infty$ and $\prod_\mathfrak p\beta_\mathfrak p(\nu)$ is multipliable,
$$\mathfrak S_Q(\nu) = \sum_{u\in F/\mathcal O}G_Q(u)\,e(-\operatorname{Tr}\nu u) = |d_F|\prod_\mathfrak p\beta_\mathfrak p(\nu),$$
$\beta_\mathfrak p$ = `LocalDensity.NF.localDensity` (Hanke (5.1)–(5.2), $\operatorname{Vol}(\mathfrak o_\mathfrak p) = 1$). The factor $|d_F| = \prod_\mathfrak pN(\mathfrak d_\mathfrak p)$
is the product of the local factors $N(\mathfrak d_\mathfrak p)$ of `locFactor_eventually_eq`: the dual of $\mathcal O$ under
$e(\operatorname{Tr}\,\cdot)$ is $\mathfrak d^{-1}$. Over $\mathbb Q$ it is $1$ (`Siegel.hasSum_ssTerm`). -/
@[kb "siegel1935" "§§3–5 and Siegel (1937): the singular series over F is |d_F| ∏_𝔭 β_𝔭 [unverified]"]
theorem singSeries_eq (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {ν : 𝓞 F} (hν : ν ≠ 0)
    (hsum : Summable fun x => ‖ssFun Q (ιO ν) x‖)
    (hmult : Multipliable fun v => LocalDensity.NF.localDensity v Q ν) :
    singSeries Q (ιO ν) = (((discr F).natAbs : ℝ) * ∏' v, LocalDensity.NF.localDensity v Q ν : ℝ) := by
  set f := ssFun Q (ιO ν)
  -- the parts over `Acl (X!)` converge to the whole series
  have hlim : Tendsto (fun X : ℕ => ∑' x, (Acl (cX F X)).indicator f x) atTop (𝓝 (singSeries Q (ιO ν))) := by
    refine tendsto_tsum_of_dominated_convergence hsum (fun x => ?_) (Eventually.of_forall fun X x => ?_)
    · refine tendsto_const_nhds.congr' ?_
      set u := Quotient.out x
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {den u}))
      set M := Ideal.absNorm (Ideal.span {den u})
      have hM : 0 < M := Nat.pos_of_ne_zero (by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact span_ne_bot (den_ne_zero u))
      filter_upwards [eventually_ge_atTop M] with X hX
      obtain ⟨k, hk⟩ := Nat.dvd_factorial hM hX
      have hden : IsDen (cX F X) u := by
        have := isDen_mul (isDen_mul (isDen_den u) t) (k : 𝓞 F)
        rwa [show den u * t * (k : 𝓞 F) = cX F X by rw [cX, hk, Nat.cast_mul, ← ht]; ring] at this
      have hmem : x ∈ Acl (cX F X) := by
        have := mk_mem_range_jmap (cX_ne_zero X) hden
        rw [QuotientAddGroup.out_eq'] at this
        exact Set.mem_iUnion.mpr ⟨1, by rwa [pow_one]⟩
      simp only [Set.indicator_of_mem hmem]
      rfl
    · by_cases h : x ∈ Acl (cX F X)
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, norm_zero]; exact norm_nonneg _
  -- the parts are products of local factors
  have hval : ∀ X, ∑' x, (Acl (cX F X)).indicator f x = ((∏ v ∈ TX F X,
      ((Ideal.absNorm v.asIdeal : ℝ) ^ diffExpNF v * LocalDensity.NF.localDensity v Q ν) : ℝ) : ℂ) := by
    intro X
    rw [tsum_indicator_Acl Q hQ hn hν hsum (cX_ne_zero X), Complex.ofReal_prod]
    rfl
  -- the products converge to |d_F| ∏ β
  have hdisc : ∀ᶠ X in atTop, ∏ v ∈ TX F X, (Ideal.absNorm v.asIdeal : ℝ) ^ diffExpNF v =
      ((discr F).natAbs : ℝ) := by
    have : ∀ v ∈ suppI (dif_ne_bot (F := F)), ∀ᶠ X in atTop, v ∈ TX F X := fun v _ =>
      (eventually_ge_atTop _).mono fun X hX => mem_TX_of_le v hX
    filter_upwards [(Filter.eventually_all_finset _).mpr this] with X hX
    exact prod_absNorm_pow_diffExp hX
  have hprod : Tendsto (fun X => ∏ v ∈ TX F X,
      ((Ideal.absNorm v.asIdeal : ℝ) ^ diffExpNF v * LocalDensity.NF.localDensity v Q ν)) atTop
      (𝓝 (((discr F).natAbs : ℝ) * ∏' v, LocalDensity.NF.localDensity v Q ν)) := by
    simp_rw [Finset.prod_mul_distrib]
    refine Tendsto.mul (tendsto_const_nhds.congr' (by filter_upwards [hdisc] with X hX using hX.symm)) ?_
    exact hmult.hasProd.comp tendsto_TX
  have hC := (Complex.continuous_ofReal.tendsto _).comp hprod
  refine tendsto_nhds_unique hlim ?_
  simp_rw [hval]
  exact hC

end QuadFormsKB.SiegelWeil.SingularNF
