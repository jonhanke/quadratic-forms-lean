/-
# The singular series over $F$ grouped by denominators (weight 2, $n = 4$)

**Layer:** finite (algebraic) plus one limit. $F$ totally real, $\mathcal O = \mathcal O_F$, $\mathfrak d^{-1}$ the inverse different,
$e(x) = e^{2\pi ix}$, $\operatorname{Tr} = \operatorname{Tr}_{F/\mathbb Q}$, $Q$ a quadratic form over $\mathcal O$ in $n$ variables,
$G_Q(u)$ = `gaussAvg` and $\mathrm{ss}_Q(\mu)(x) = G_Q(\tilde x)e(-\operatorname{Tr}\mu\tilde x)$ = `ssFun` on $F/\mathcal O$.

**Why grouping.** For $n = 4$ the singular series $\sum_{u\in F/\mathcal O}G_Q(u)e(-\operatorname{Tr}\mu u)$ does **not** converge absolutely
($|G_Q(u)| \asymp N(\mathfrak q)^{-2}$ on the $\asymp N(\mathfrak q)^2$ classes of denominator $\mathfrak q$), so `singSeries_eq` (which assumes
$\sum_u|G_Q(u)| < \infty$) does not apply. The Eisenstein series of weight 2 produces it **grouped by rows**: for a class $C$ with fixed
integral ideal $\mathfrak b_C$ (`repIdeal`) and a row $t \in U\backslash F$ with representative $c = \tilde t$ (`crep`), the classes
$$\{u : c\,(\mathcal O + u\mathcal O) = \mathfrak b_C\}\quad(\texttt{RowKey}\ C\ t\ u)$$
are finite and partition $F/\mathcal O$ (`existsUnique_rowKey`); they are the classes of exact denominator $\mathfrak q = (c)\mathfrak b_C^{-1}$.
The **row parts** (`ssPart`)
$$A_{C,t}(\mu) = \sum_{u\in F/\mathcal O:\ \texttt{RowKey}\ C\ t\ u}G_Q(-u)\,e(\operatorname{Tr}\mu u)$$
are finite sums, and the grouped series $\sum_{(C,t)}A_{C,t}(\mu)$ converges absolutely (this is proved in
`HilbertModular/EisensteinQ2Coeff.lean` from the Eisenstein series, not here).

**Results.**
* `ssTrunc_eq_tsum_ssPart`: the truncated singular series $S_K(\mu)$ ($K \in \mathcal O\setminus0$, `ssTrunc`) is the sum of the row parts
  with denominator dividing $K$.
* **`tsum_ssPart_eq`**: if $\sum_{(C,t)}|A_{C,t}(\nu)| < \infty$ ($\nu \in \mathcal O\setminus0$, $Q$ nondegenerate, $\prod_\mathfrak p\beta_\mathfrak p(\nu)$
  multipliable), then
  $$\sum_{(C,t)}A_{C,t}(\nu) = |d_F|\prod_\mathfrak p\beta_\mathfrak p(\nu).$$
  *Convention for the product:* $\prod_\mathfrak p\beta_\mathfrak p$ is the unconditional product (`tprod`; for $n \ge 4$ it converges absolutely,
  `Siegel.multipliable_eulerFactorNF`). The **series** is summed unconditionally over the rows $(C,t)$ (absolute convergence after
  grouping); it is never summed over $u \in F/\mathcal O$ termwise.
  *Proof:* $S_{(X!)^E}(\nu) = \prod_{\mathfrak p\mid X!}\lambda_\mathfrak p(E\,v_\mathfrak p(X!))$ (CRT), which equals
  $\prod_{\mathfrak p\mid X!}N(\mathfrak d_\mathfrak p)\beta_\mathfrak p(\nu)$ for $E \gg 0$ (`locFactor_eventually_eq`); by dominated convergence over the rows,
  $\lim_E S_{(X!)^E}$ is the sum of the row parts with denominator supported on $\{\mathfrak p \mid X!\}$, and these tend to
  $\sum_{(C,t)}A_{C,t}$ as $X \to \infty$; the products tend to $|d_F|\prod_\mathfrak p\beta_\mathfrak p$.
* `tsum_ssPart_eq_zero_of_not_int`: for $\mu \in \mathfrak d^{-1}\setminus\mathcal O$ the grouped series is $0$ (the truncations vanish once
  $\mathfrak d \mid K$, `ssTrunc_eq_zero_of_not_int`).

Sources: Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. Math. 36 (1935), §§3–5 [unverified]; Siegel,
Ann. Math. 38 (1937) [unverified]; Hanke 2004, (5.1)–(5.3), p. 368.
-/
import QuadFormsKB.HilbertModular.EisensteinCoeff2

open NumberField IsDedekindDomain Complex Filter Topology
open scoped nonZeroDivisors MatrixGroups

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.SiegelWeil.SingularNF

open QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F
local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

/-! ### Row keys -/

/-- **The row key** of $u \in F$: the class $C$ and the row $t \in U\backslash F$ with $\tilde t\,(\mathcal O + u\mathcal O) = \mathfrak b_C$
($\tilde t$ = `crep t`, $\mathfrak b_C$ = `repIdeal C`). Then $(\tilde t, \tilde tu)$ is the reduced vector of the cusp $-u$. Parameters: `C`
(ideal class), `t` (row), `u` (the point of $F$). -/
@[kb "siegel1935" "§3: classes of F/𝒪 by exact denominator (rows of reduced cusp vectors) [unverified]"]
def RowKey (C : ClassGroup (𝓞 F)) (t : UOrbitF F) (u : F) : Prop :=
  FractionalIdeal.spanSingleton (𝓞 F)⁰ (crep t) * cuspIdeal 1 u = ((repIdeal C : Ideal (𝓞 F)) : FI)

lemma spanSingleton_ne_zero' {c : F} (hc : c ≠ 0) : FractionalIdeal.spanSingleton (𝓞 F)⁰ c ≠ 0 := by
  rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]

lemma repIdeal_coe_ne_zero (C : ClassGroup (𝓞 F)) : ((repIdeal C : Ideal (𝓞 F)) : FI) ≠ 0 := by
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact repIdeal_ne_bot C

lemma crep_ne_zero_of_rowKey {C : ClassGroup (𝓞 F)} {t : UOrbitF F} {u : F} (h : RowKey C t u) :
    crep t ≠ 0 := by
  intro h0
  rw [RowKey, h0, map_zero, zero_mul] at h
  exact repIdeal_coe_ne_zero C h.symm

/-- $\mathcal O\alpha + \mathcal O(\gamma + b\alpha) = \mathcal O\alpha + \mathcal O\gamma$ for $b \in \mathcal O$. -/
lemma cuspIdeal_add_mul (α γ : F) (b : 𝓞 F) : cuspIdeal α (γ + ιO b * α) = cuspIdeal α γ := by
  refine le_antisymm ?_ ?_
  · have := cuspIdeal_le_of 1 0 b 1 α γ
    convert this using 2 <;> simp [Algebra.smul_def]; ring
  · have := cuspIdeal_le_of 1 0 (-b) 1 α (γ + ιO b * α)
    convert this using 2 <;> simp [Algebra.smul_def]

lemma cuspIdeal_one_add_int (u : F) (b : 𝓞 F) : cuspIdeal 1 (u + ιO b) = cuspIdeal 1 u := by
  have := cuspIdeal_add_mul (1 : F) u b
  rwa [mul_one] at this

lemma rowKey_add_int_iff (C : ClassGroup (𝓞 F)) (t : UOrbitF F) (u : F) (b : 𝓞 F) :
    RowKey C t (u + ιO b) ↔ RowKey C t u := by
  rw [RowKey, RowKey, cuspIdeal_one_add_int]

lemma rowKey_out_mk_iff (C : ClassGroup (𝓞 F)) (t : UOrbitF F) (u : F) :
    RowKey C t (Quotient.out (QuotientAddGroup.mk u : FO F)) ↔ RowKey C t u := by
  have h : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk u : FO F)) : FO F) = QuotientAddGroup.mk u :=
    Quotient.out_eq _
  obtain ⟨b, hb⟩ := mem_OSub.mp (QuotientAddGroup.eq.mp h)
  have hu : u = Quotient.out (QuotientAddGroup.mk u : FO F) + ιO b := by rw [hb]; ring
  conv_rhs => rw [hu]
  exact (rowKey_add_int_iff C t _ b).symm

/-- **Every $u$ has exactly one row key.** -/
@[kb "freitag1990" "Ch. I §2: every cusp has a unique reduced representative [unverified]"]
theorem existsUnique_rowKey (u : F) : ∃! p : ClassGroup (𝓞 F) × UOrbitF F, RowKey p.1 p.2 u := by
  have hx : ((1 : F), u).1 ≠ 0 ∨ ((1 : F), u).2 ≠ 0 := Or.inl one_ne_zero
  obtain ⟨T, hT0, hT⟩ := exists_isRedVec_smul hx
  set t : UOrbitF F := Quotient.mk _ T
  -- `crep t` is a unit multiple of `T`
  have hct : ∃ ε : (𝓞 F)ˣ, crep t = (ε : F) * T := by
    have h1 : (Quotient.mk _ (crep t) : UOrbitF F) = Quotient.mk _ T := crep_mk t
    obtain ⟨ε, hε⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact h1))
    exact ⟨ε, by rw [← hε]; rfl⟩
  have hspan : FractionalIdeal.spanSingleton (𝓞 F)⁰ (crep t) = FractionalIdeal.spanSingleton (𝓞 F)⁰ T := by
    obtain ⟨ε, hε⟩ := hct
    rw [hε, FractionalIdeal.spanSingleton_eq_spanSingleton]
    exact ⟨ε⁻¹, by rw [Units.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]⟩
  have hkey : RowKey (cuspClass (T * 1) (T * u)) t u := by
    rw [RowKey, hspan, ← cuspIdeal_smul]
    exact hT.2
  refine ⟨(cuspClass (T * 1) (T * u), t), hkey, ?_⟩
  intro p h'
  obtain ⟨C', t'⟩ := p
  change RowKey C' t' u at h'
  have hc' := crep_ne_zero_of_rowKey h'
  have hI : cuspIdeal 1 u ≠ 0 := cuspIdeal_ne_zero (Or.inl one_ne_zero)
  -- the classes agree
  have hC : C' = cuspClass (T * 1) (T * u) := by
    have e1 : cuspIdeal (crep t' * 1) (crep t' * u) = ((repIdeal C' : Ideal (𝓞 F)) : FI) := by
      rw [cuspIdeal_smul]; exact h'
    have := cuspClass_eq_of_cuspIdeal_eq (y := (crep t' * 1, crep t' * u))
      (Or.inl (by simp only [mul_one]; exact hc')) e1
    rw [cuspClass_smul hc' (Or.inl one_ne_zero)] at this
    rw [← this, cuspClass_smul hT0 (Or.inl one_ne_zero)]
  subst hC
  -- the rows agree
  have e2 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (crep t') = FractionalIdeal.spanSingleton (𝓞 F)⁰ (crep t) := by
    have := h'.trans hkey.symm
    exact mul_right_cancel₀ hI this
  obtain ⟨ε, hε⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp e2
  have : t' = t := by
    rw [← crep_mk t', ← crep_mk t]
    exact (Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨ε, hε⟩))).symm
  rw [this]

/-- The row key of $u$ (`existsUnique_rowKey`). -/
def rowKeyOf (u : F) : ClassGroup (𝓞 F) × UOrbitF F := (existsUnique_rowKey u).exists.choose

lemma rowKey_rowKeyOf (u : F) : RowKey (rowKeyOf u).1 (rowKeyOf u).2 u :=
  (existsUnique_rowKey u).exists.choose_spec

lemma rowKey_iff_eq (u : F) (p : ClassGroup (𝓞 F) × UOrbitF F) : RowKey p.1 p.2 u ↔ p = rowKeyOf u :=
  ⟨fun h => (existsUnique_rowKey u).unique h (rowKey_rowKeyOf u), fun h => h ▸ rowKey_rowKeyOf u⟩

/-- $cu \in \mathcal O$ iff $(c)(\mathcal O + u\mathcal O) \subseteq \mathcal O$. -/
lemma isDen_iff_le (K : 𝓞 F) (u : F) :
    IsDen K u ↔ FractionalIdeal.spanSingleton (𝓞 F)⁰ (ιO K) * cuspIdeal 1 u ≤ 1 := by
  rw [← cuspIdeal_smul, cuspIdeal_le_iff, mul_one]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(FractionalIdeal.mem_one_iff _).mpr ⟨K, rfl⟩, (FractionalIdeal.mem_one_iff _).mpr ⟨a, ha⟩⟩
  · rintro ⟨-, h⟩
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp h
    exact ⟨a, ha⟩

/-- **Denominators depend only on the row key.** -/
lemma isDen_iff_of_rowKey {C : ClassGroup (𝓞 F)} {t : UOrbitF F} {u u' : F} (h : RowKey C t u)
    (h' : RowKey C t u') (K : 𝓞 F) : IsDen K u ↔ IsDen K u' := by
  have hc := crep_ne_zero_of_rowKey h
  have e : cuspIdeal 1 u = cuspIdeal 1 u' := mul_left_cancel₀ (spanSingleton_ne_zero' hc) (h.trans h'.symm)
  rw [isDen_iff_le, isDen_iff_le, e]

/-- A point with row key $(C, t)$ has denominator dividing $\tilde t$: $\tilde t = \iota(c')$ with $c' \in \mathcal O$ and $c'u \in \mathcal O$. -/
lemma exists_isDen_of_rowKey {C : ClassGroup (𝓞 F)} {t : UOrbitF F} {u : F} (h : RowKey C t u) :
    ∃ c' : 𝓞 F, ιO c' = crep t ∧ IsDen c' u := by
  have hle : cuspIdeal (crep t * 1) (crep t * u) ≤ 1 := by
    rw [cuspIdeal_smul, h]; exact FractionalIdeal.coeIdeal_le_one
  obtain ⟨h1, h2⟩ := cuspIdeal_le_iff.mp hle
  obtain ⟨c', hc'⟩ := (FractionalIdeal.mem_one_iff _).mp h1
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp h2
  refine ⟨c', by rw [hc', mul_one], a, by rw [ha, hc', mul_one]⟩

/-! ### The row parts of the singular series -/

open Classical in
/-- **The row part of the singular series** $A_{C,t}(\mu) = \sum_{u\in F/\mathcal O,\ \texttt{RowKey}\ C\ t\ u}\mathrm{ss}_Q(\mu)(-u)
= \sum G_Q(-u)e(\operatorname{Tr}\mu u)$ (a finite sum: such $u$ have denominator dividing $\tilde t$). Parameters: `Q`, `μ`, `p = (C, t)`. -/
@[kb "siegel1935" "§§3–5: the part of the singular series with a fixed denominator [unverified]"]
def ssPart (Q : QuadForm (𝓞 F) n) (μ : F) (p : ClassGroup (𝓞 F) × UOrbitF F) : ℂ :=
  ∑' x : FO F, if RowKey p.1 p.2 (Quotient.out x) then ssFun Q μ (-x) else 0

open Classical in
/-- The summand of `ssPart` is supported in $\tilde t^{-1}\mathcal O/\mathcal O$, a finite set. -/
lemma ssPart_support_finite (Q : QuadForm (𝓞 F) n) (μ : F) (p : ClassGroup (𝓞 F) × UOrbitF F) :
    (Function.support fun x : FO F => if RowKey p.1 p.2 (Quotient.out x) then ssFun Q μ (-x) else 0).Finite := by
  by_cases hp : ∃ x : FO F, RowKey p.1 p.2 (Quotient.out x)
  · obtain ⟨x₀, hx₀⟩ := hp
    obtain ⟨c', hc', -⟩ := exists_isDen_of_rowKey hx₀
    have hc0 : c' ≠ 0 := by
      intro h; rw [h, map_zero] at hc'; exact crep_ne_zero_of_rowKey hx₀ hc'.symm
    haveI := finite_quot_span hc0
    refine (Set.finite_range (jmap c')).subset fun x hx => ?_
    have hk : RowKey p.1 p.2 (Quotient.out x) := by
      by_contra h; exact hx (by simp only [h, ↓reduceIte])
    obtain ⟨c'', hc'', hden⟩ := exists_isDen_of_rowKey hk
    have : c'' = c' := FaithfulSMul.algebraMap_injective (𝓞 F) F (hc''.trans hc'.symm)
    subst this
    have := mk_mem_range_jmap hc0 hden
    rwa [QuotientAddGroup.out_eq'] at this
  · push Not at hp
    convert Set.finite_empty
    ext x
    simp [hp x]

open Classical in
/-- **The row part through a row representative**: if $\tilde t = \iota(c')$, $c' \ne 0$, then for any $h$ on $F/\mathcal O$,
$\sum_{u:\ \texttt{RowKey}\ C\ t\ u}h(u) = \sum_{r\in\mathcal O/c'}[\mathcal O\tilde t + \mathcal O\tilde r = \mathfrak b_C]\,h(\tilde r/\tilde t)$. -/
theorem tsum_rowKey_eq_sum (C : ClassGroup (𝓞 F)) (t : UOrbitF F) {c' : 𝓞 F} (hc0 : c' ≠ 0)
    (hc' : ιO c' = crep t) (h : FO F → ℂ) [Fintype (𝓞 F ⧸ Ideal.span {c'})] :
    (∑' x : FO F, if RowKey C t (Quotient.out x) then h x else 0) =
      ∑ r : 𝓞 F ⧸ Ideal.span {c'}, if cuspIdeal (ιO c') (ιO (Quotient.out r)) = ((repIdeal C : Ideal (𝓞 F)) : FI)
        then h (jmap c' r) else 0 := by
  classical
  have hc := algebraMap_ne_zero hc0
  -- the key of `jmap c' r`
  have hkey : ∀ r : 𝓞 F ⧸ Ideal.span {c'}, RowKey C t (Quotient.out (jmap c' r)) ↔
      cuspIdeal (ιO c') (ιO (Quotient.out r)) = ((repIdeal C : Ideal (𝓞 F)) : FI) := by
    intro r
    rw [jmap, rowKey_out_mk_iff, RowKey, ← hc', ← cuspIdeal_smul, mul_one,
      show ιO c' * (ιO (Quotient.out r) / ιO c') = ιO (Quotient.out r) by field_simp]
  -- the support lies in the range of `jmap c'`
  have hsupp : Function.support (fun x : FO F => if RowKey C t (Quotient.out x) then h x else 0) ⊆
      Set.range (jmap c') := by
    intro x hx
    have hk : RowKey C t (Quotient.out x) := by
      by_contra h'; exact hx (by simp only [h', ↓reduceIte])
    obtain ⟨c'', hc'', hden⟩ := exists_isDen_of_rowKey hk
    have : c'' = c' := FaithfulSMul.algebraMap_injective (𝓞 F) F (hc''.trans hc'.symm)
    subst this
    have := mk_mem_range_jmap hc0 hden
    rwa [QuotientAddGroup.out_eq'] at this
  rw [← (jmap_injective hc0).tsum_eq hsupp, tsum_fintype]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : cuspIdeal (ιO c') (ιO (Quotient.out r)) = ((repIdeal C : Ideal (𝓞 F)) : FI)
  · rw [if_pos ((hkey r).mpr hr), if_pos hr]
  · rw [if_neg (fun h' => hr ((hkey r).mp h')), if_neg hr]

/-! ### The truncated singular series as a sum of row parts -/

lemma isDen_neg_iff (K : 𝓞 F) (u : F) : IsDen K (-u) ↔ IsDen K u := by
  constructor
  · rintro ⟨a, ha⟩; exact ⟨-a, by rw [map_neg, ha]; ring⟩
  · rintro ⟨a, ha⟩; exact ⟨-a, by rw [map_neg, ha]; ring⟩

lemma mem_range_jmap_iff {K : 𝓞 F} (hK : K ≠ 0) (x : FO F) :
    x ∈ Set.range (jmap K) ↔ IsDen K (Quotient.out x) := by
  constructor
  · exact isDen_of_mem_range_jmap
  · intro h
    have := mk_mem_range_jmap hK h
    rwa [QuotientAddGroup.out_eq'] at this

lemma isDen_out_neg_iff (K : 𝓞 F) (x : FO F) : IsDen K (Quotient.out (-x)) ↔ IsDen K (Quotient.out x) := by
  have h : (QuotientAddGroup.mk (Quotient.out (-x)) : FO F) = QuotientAddGroup.mk (-Quotient.out x) := by
    rw [QuotientAddGroup.out_eq', QuotientAddGroup.mk_neg, QuotientAddGroup.out_eq']
  obtain ⟨b, hb⟩ := mem_OSub.mp (QuotientAddGroup.eq.mp h)
  have e : Quotient.out (-x) = -Quotient.out x - ιO b := by rw [hb]; ring
  rw [e, ← isDen_neg_iff, neg_sub, sub_neg_eq_add]
  constructor
  · rintro ⟨a, ha⟩; exact ⟨a - K * b, by rw [map_sub, ha, map_mul]; ring⟩
  · rintro ⟨a, ha⟩; exact ⟨a + K * b, by rw [map_add, ha, map_mul]; ring⟩

/-- The predicate "the rows $(C, t)$ have denominator dividing $K$": some (equivalently every, `isDen_iff_of_rowKey`) $u$ with row key
$(C, t)$ has $Ku \in \mathcal O$. -/
def DenDvd (K : 𝓞 F) (p : ClassGroup (𝓞 F) × UOrbitF F) : Prop :=
  ∃ u : F, RowKey p.1 p.2 u ∧ IsDen K u

lemma denDvd_iff_of_rowKey {K : 𝓞 F} {p : ClassGroup (𝓞 F) × UOrbitF F} {u : F} (h : RowKey p.1 p.2 u) :
    DenDvd K p ↔ IsDen K u :=
  ⟨fun ⟨_, h', hd⟩ => (isDen_iff_of_rowKey h' h K).mp hd, fun hd => ⟨u, h, hd⟩⟩

lemma denDvd_mul {K : 𝓞 F} {p : ClassGroup (𝓞 F) × UOrbitF F} (h : DenDvd K p) (m : 𝓞 F) : DenDvd (K * m) p := by
  obtain ⟨u, hu, hd⟩ := h
  exact ⟨u, hu, isDen_mul hd m⟩

open Classical in
/-- **The truncated singular series is the sum of the row parts with denominator dividing $K$**: for $K \ne 0$ and $\mu \in \mathfrak d^{-1}$,
$$S_K(\mu) = \sum_{(C,t):\ \mathfrak q_{C,t}\mid K}A_{C,t}(\mu)\qquad(\text{finitely many nonzero terms}).$$ -/
@[kb "siegel1935" "§3: truncated singular series = sum of the row parts with denominator dividing K [unverified]"]
theorem ssTrunc_eq_tsum_ssPart (Q : QuadForm (𝓞 F) n) {K : 𝓞 F} (hK : K ≠ 0) {μ : F} (hμ : μ ∈ invDifferent F) :
    ssTrunc Q K μ = ∑' p, if DenDvd K p then ssPart Q μ p else 0 := by
  classical
  haveI := finite_quot_span hK
  set g : FO F → ℂ := fun x => ssFun Q μ (-x)
  -- step 1: the indicator sum, after `x ↦ -x`
  have h1 : ssTrunc Q K μ = ∑' x, (Set.range (jmap K)).indicator g x := by
    rw [ssTrunc_eq_tsum_indicator Q hK hμ, ← (Equiv.neg (FO F)).tsum_eq]
    refine tsum_congr fun x => ?_
    simp only [Equiv.neg_apply, g]
    by_cases hx : x ∈ Set.range (jmap K)
    · have hx' : -x ∈ Set.range (jmap K) := by
        rw [mem_range_jmap_iff hK] at hx ⊢; rwa [isDen_out_neg_iff]
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · have hx' : -x ∉ Set.range (jmap K) := by
        rw [mem_range_jmap_iff hK] at hx ⊢; rwa [isDen_out_neg_iff]
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
  -- step 2: split each `x` by its row key
  set G : FO F → ClassGroup (𝓞 F) × UOrbitF F → ℂ := fun x p =>
    if RowKey p.1 p.2 (Quotient.out x) then (if DenDvd K p then g x else 0) else 0
  have h2 : ∀ x, (Set.range (jmap K)).indicator g x = ∑' p, G x p := by
    intro x
    rw [tsum_eq_single (rowKeyOf (Quotient.out x))]
    · simp only [G, if_pos (rowKey_rowKeyOf _)]
      rw [denDvd_iff_of_rowKey (rowKey_rowKeyOf _), ← mem_range_jmap_iff hK]
      by_cases hx : x ∈ Set.range (jmap K)
      · rw [Set.indicator_of_mem hx, if_pos hx]
      · rw [Set.indicator_of_notMem hx, if_neg hx]
    · intro p hp
      simp only [G]
      rw [if_neg (fun h => hp ((rowKey_iff_eq _ p).mp h))]
  -- step 3: swap the sums (finite support)
  have hfin : (Function.support (Function.uncurry G)).Finite := by
    refine ((Set.finite_range (jmap K)).image fun x => (x, rowKeyOf (Quotient.out x))).subset ?_
    rintro ⟨x, p⟩ hxp
    simp only [Function.mem_support, Function.uncurry, G] at hxp
    split_ifs at hxp with hk hd
    · refine ⟨x, ?_, ?_⟩
      · exact (mem_range_jmap_iff hK x).mpr ((denDvd_iff_of_rowKey hk).mp hd)
      · simp only [Prod.mk.injEq, true_and]; exact ((rowKey_iff_eq _ p).mp hk).symm
    · exact absurd rfl hxp
    · exact absurd rfl hxp
  have hs : Summable (Function.uncurry G) := summable_of_hasFiniteSupport hfin
  rw [h1, tsum_congr h2, ← hs.tsum_comm']
  · refine tsum_congr fun p => ?_
    simp only [G, ssPart]
    by_cases hd : DenDvd K p
    · simp only [hd, ↓reduceIte]; rfl
    · simp only [hd, ↓reduceIte, ite_self, tsum_zero]
  · exact fun x => hs.prod_factor x
  · exact fun p => (hs.comp_injective (Prod.mk_left_injective p)).congr fun x => rfl


/-! ### The limit: the grouped series is $|d_F|\prod_\mathfrak p\beta_\mathfrak p$ -/

/-- The rows whose denominator is supported on the primes dividing $X!$. -/
def DenPow (X : ℕ) (p : ClassGroup (𝓞 F) × UOrbitF F) : Prop := ∃ E : ℕ, DenDvd (cX F X ^ E) p

open Classical in
/-- **Step 1** ($E \to \infty$): $S_{(X!)^E}(\mu) \to \sum_{(C,t)}[\mathfrak q_{C,t}\mid (X!)^\infty]A_{C,t}(\mu)$ (dominated convergence over
the rows, `ssTrunc_eq_tsum_ssPart`). -/
theorem tendsto_ssTrunc_pow (Q : QuadForm (𝓞 F) n) {μ : F} (hμ : μ ∈ invDifferent F)
    (hsum : Summable fun p => ‖ssPart Q μ p‖) (X : ℕ) :
    Tendsto (fun E : ℕ => ssTrunc Q (cX F X ^ E) μ) atTop
      (𝓝 (∑' p, if DenPow X p then ssPart Q μ p else 0)) := by
  classical
  simp_rw [fun E => ssTrunc_eq_tsum_ssPart Q (pow_ne_zero E (cX_ne_zero X)) hμ]
  refine tendsto_tsum_of_dominated_convergence hsum (fun p => ?_) (Eventually.of_forall fun E p => ?_)
  · by_cases hp : DenPow X p
    · obtain ⟨E₀, hE₀⟩ := hp
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop E₀] with E hE
      have hD : DenDvd (cX F X ^ E) p := by
        have := denDvd_mul hE₀ (cX F X ^ (E - E₀))
        rwa [← pow_add, Nat.add_sub_cancel' hE] at this
      rw [if_pos ⟨E₀, hE₀⟩, if_pos hD]
    · refine tendsto_const_nhds.congr' (Eventually.of_forall fun E => ?_)
      have hD : ¬ DenDvd (cX F X ^ E) p := fun h => hp ⟨E, h⟩
      simp only [if_neg hp, if_neg hD]
  · split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _

open Classical in
/-- **Step 2** ($X \to \infty$): $\sum_{(C,t)}[\mathfrak q_{C,t}\mid(X!)^\infty]A_{C,t}(\mu) \to \sum_{(C,t)}A_{C,t}(\mu)$ (every denominator
divides some $X!$). -/
theorem tendsto_tsum_denPow (Q : QuadForm (𝓞 F) n) {μ : F} (hsum : Summable fun p => ‖ssPart Q μ p‖) :
    Tendsto (fun X : ℕ => ∑' p, if DenPow X p then ssPart Q μ p else 0) atTop (𝓝 (∑' p, ssPart Q μ p)) := by
  classical
  refine tendsto_tsum_of_dominated_convergence hsum (fun p => ?_) (Eventually.of_forall fun X p => ?_)
  · by_cases hA : ssPart Q μ p = 0
    · refine tendsto_const_nhds.congr' (Eventually.of_forall fun X => ?_)
      simp only [hA, ite_self]
    · -- some `u` has row key `p`
      obtain ⟨x, hx⟩ : ∃ x : FO F, RowKey p.1 p.2 (Quotient.out x) := by
        by_contra h
        push Not at h
        apply hA
        rw [ssPart]
        simp [h]
      set u := Quotient.out x
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {den u}))
      set M := Ideal.absNorm (Ideal.span {den u})
      have hM : 0 < M := Nat.pos_of_ne_zero (by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact span_ne_bot (den_ne_zero u))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop M] with X hX
      obtain ⟨k, hk⟩ := Nat.dvd_factorial hM hX
      have hden : IsDen (cX F X) u := by
        have := isDen_mul (isDen_mul (isDen_den u) t) (k : 𝓞 F)
        rwa [show den u * t * (k : 𝓞 F) = cX F X by rw [cX, hk, Nat.cast_mul, ← ht]; ring] at this
      have hD : DenPow X p := ⟨1, u, hx, by rw [pow_one]; exact hden⟩
      rw [if_pos hD]
  · split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _

/-- **The grouped singular series over $F$ is $|d_F|$ times the Euler product of the local densities** (weight 2: the series is
summed over the rows $(C, t)$, i.e. grouped by denominators): for $Q$ nondegenerate over $\mathcal O_F$, $n \ge 1$, $\nu \in \mathcal O_F\setminus0$, if
$\sum_{(C,t)}|A_{C,t}(\nu)| < \infty$ and $\prod_\mathfrak p\beta_\mathfrak p(\nu)$ is multipliable,
$$\sum_{(C,t)}A_{C,t}(\nu) = |d_F|\prod_\mathfrak p\beta_\mathfrak p(\nu)\qquad(\beta_\mathfrak p = \texttt{LocalDensity.NF.localDensity}).$$
The analogue of `singSeries_eq` without absolute convergence over $F/\mathcal O$. -/
@[kb "siegel1935" "§§3–5: the singular series grouped by denominators is |d_F| ∏_𝔭 β_𝔭 (weight 2) [unverified]"]
theorem tsum_ssPart_eq (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {ν : 𝓞 F} (hν : ν ≠ 0)
    (hsum : Summable fun p => ‖ssPart Q (ιO ν) p‖)
    (hmult : Multipliable fun v => LocalDensity.NF.localDensity v Q ν) :
    ∑' p, ssPart Q (ιO ν) p = (((discr F).natAbs : ℝ) * ∏' v, LocalDensity.NF.localDensity v Q ν : ℝ) := by
  classical
  have hν' : ιO ν ∈ invDifferent F := algebraMap_mem_invDifferent ν
  -- for each `X`, the limit in `E` is the product of the local factors over `TX`
  have hval : ∀ X, (∑' p, if DenPow X p then ssPart Q (ιO ν) p else 0) = ((∏ v ∈ TX F X,
      ((Ideal.absNorm v.asIdeal : ℝ) ^ diffExpNF v * LocalDensity.NF.localDensity v Q ν) : ℝ) : ℂ) := by
    intro X
    set c := cX F X
    have hc := cX_ne_zero (F := F) X
    set T := TX F X
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
    rw [Complex.ofReal_prod]
    exact tendsto_nhds_unique (tendsto_ssTrunc_pow Q hν' hsum X)
      (tendsto_const_nhds.congr' (by filter_upwards [hev] with E hE using hE.symm))
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
  refine tendsto_nhds_unique (tendsto_tsum_denPow Q hsum) ?_
  simp_rw [hval]
  exact hC

/-- **The grouped singular series vanishes off $\mathcal O_F$** ($\mu \in \mathfrak d^{-1}\setminus\mathcal O_F$, the row parts absolutely summable):
$\sum_{(C,t)}A_{C,t}(\mu) = 0$. The truncations $S_{(X!)^E}(\mu)$ vanish once $\mathfrak d \mid X!$ (`ssTrunc_eq_zero_of_not_int`). -/
@[kb "siegel1935" "the grouped singular series vanishes at non-integral μ ∈ 𝔡⁻¹ (weight 2) [unverified]"]
theorem tsum_ssPart_eq_zero_of_not_int (Q : QuadForm (𝓞 F) n) {μ : F} (hμ : μ ∈ invDifferent F)
    (hμO : ¬ ∃ b : 𝓞 F, ιO b = μ) (hsum : Summable fun p => ‖ssPart Q μ p‖) :
    ∑' p, ssPart Q μ p = 0 := by
  classical
  set D := Ideal.absNorm (dif F)
  have hD : 0 < D := Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact dif_ne_bot)
  have hzero : ∀ X, D ≤ X → (∑' p, if DenPow X p then ssPart Q μ p else 0) = 0 := by
    intro X hX
    have hcX : cX F X ∈ dif F := by
      obtain ⟨k, hk⟩ := Nat.dvd_factorial hD hX
      rw [cX, hk, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    refine tendsto_nhds_unique (tendsto_ssTrunc_pow Q hμ hsum X) (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with E hE
    symm
    refine ssTrunc_eq_zero_of_not_int Q (pow_ne_zero E (cX_ne_zero X)) ?_ hμ hμO
    obtain ⟨j, rfl⟩ : ∃ j, E = j + 1 := ⟨E - 1, by omega⟩
    rw [pow_succ]
    exact Ideal.mul_mem_left _ _ hcX
  exact tendsto_nhds_unique (tendsto_tsum_denPow Q hsum) (tendsto_const_nhds.congr' (by
    filter_upwards [eventually_ge_atTop D] with X hX using (hzero X hX).symm))

end QuadFormsKB.SiegelWeil.SingularNF
