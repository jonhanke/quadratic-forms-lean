/-
# Hasse norm theorem, step 4a: square classes of a completion

For a number field $K$ and a finite place $v$ with completion $K_v$, valuation ring $\mathcal O_v$,
residue field of size $N\mathfrak p$ (`card_residueField`), and $e = \operatorname{ord}_v 2$ (`ordTwo`):

* `isSquare_of_valued_sub_one_lt`: local square theorem, $v(x - 1) < v(4) \Rightarrow x \in K_v^{\times 2}$
  (contraction mapping, as in `NFLocal.isSquare_of_valuation_sub_one_lt_nf`, now also at $v \mid 2$);
* `Ufil`: higher unit groups $U^{(n+1)}$; `relIndex_Ufil`: $[U^{(m+1)} : U^{(m+n+1)}] = (N\mathfrak p)^n$ for
  $n \le m + 1$ (via $x \mapsto (x - 1)/\varpi^{m+1} \bmod \varpi^n$);
* `sq_mem_Ufil_iff`: $y^2 \in U^{(2e+1)} \iff \pm y \in U^{(e+1)}$;
* `index_sq_U0`: $[\mathcal O_v^\times : \mathcal O_v^{\times2}] = 2 (N\mathfrak p)^e$;
* `index_sq_completion`: $[K_v^\times : K_v^{\times 2}] = 4 (N\mathfrak p)^e$.

Proof of `index_sq_U0`: $U^{(2e+1)} \subseteq \mathcal O_v^{\times 2}$ (local square theorem), the squaring map
pulls $U^{(2e+1)}$ back to $\pm U^{(e+1)}$ and $-1 \notin U^{(e+1)}$, so
$[\mathcal O_v^\times : \mathcal O_v^{\times 2}] = 2\,[U^{(e+1)} : U^{(2e+1)}]$. Mathlib v4.35.0 has none of this for
completions of number fields (no residue field of `adicCompletionIntegers`, no unit filtration).

See `Herbrand.lean` for the overall plan. Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.HasseNorm.Places

open Module NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HN

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K

/-- $K_v$ has characteristic $0$. -/
instance : CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective

/-- **Local square theorem:** in $K_v$, if $v(x - 1) < v(4)$ then $x$ is a square. -/
@[kb "omeara1963" "§63A, 63:1 and 63:1a, p. 159 (Local Square Theorem); cassels1978 Ch. 3, Lemma 1.6, p. 40"]
theorem isSquare_of_valued_sub_one_lt (x : Kv) (hx : Valued.v (x - 1) < Valued.v (4 : Kv)) :
    IsSquare x := by
  have h2K : (2 : Kv) ≠ 0 := two_ne_zero
  have hn2 : 0 < ‖(2 : Kv)‖ := norm_pos_iff.mpr h2K
  set e : Kv := x - 1 with he
  have h4 : ‖(4 : Kv)‖ = ‖(2 : Kv)‖ * ‖(2 : Kv)‖ := by
    rw [← norm_mul]; norm_num
  have hr : ‖e‖ < ‖(2 : Kv)‖ * ‖(2 : Kv)‖ := by
    rw [← h4]; exact (Valued.toNormedField.norm_lt_iff).mpr hx
  set r := ‖e‖ / ‖(2 : Kv)‖ with hrdef
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg _) hn2.le
  have hr2 : r < ‖(2 : Kv)‖ := by rw [hrdef, div_lt_iff₀ hn2]; exact hr
  have hk : r / ‖(2 : Kv)‖ < 1 := by rw [div_lt_one hn2]; exact hr2
  let f : Kv → Kv := fun y => (e - y ^ 2) / 2
  let s := Metric.closedBall (0 : Kv) r
  have hmaps : Set.MapsTo f s s := by
    intro y hy
    simp only [s, Metric.mem_closedBall, dist_zero_right] at hy ⊢
    simp only [f, norm_div]
    rw [div_le_iff₀ hn2, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [hrdef, div_mul_cancel₀ _ hn2.ne']
    · rw [norm_neg, norm_pow, pow_two]
      exact mul_le_mul hy (hy.trans hr2.le) (norm_nonneg y) hr0
  set k : NNReal := ⟨r / ‖(2 : Kv)‖, div_nonneg hr0 hn2.le⟩ with hkdef
  have hcon : ContractingWith k (hmaps.restrict f s s) := by
    refine ⟨hk, LipschitzWith.of_dist_le_mul fun y y' => ?_⟩
    have hy := y.2; have hy' := y'.2
    simp only [s, Metric.mem_closedBall, dist_zero_right] at hy hy'
    change dist (f (y:Kv)) (f y') ≤ (k : ℝ) * dist (y:Kv) y'
    simp only [f, hkdef, NNReal.coe_mk]
    rw [dist_eq_norm, dist_eq_norm]
    have : (e - (y:Kv)^2)/2 - (e - (y':Kv)^2)/2 = -((y:Kv) - y') * ((y:Kv) + y') / 2 := by ring
    rw [this, norm_div, norm_mul, norm_neg]
    have hsum : ‖(y:Kv) + y'‖ ≤ r := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy hy')
    rw [div_le_iff₀ hn2]
    calc ‖(y:Kv) - y'‖ * ‖(y:Kv) + y'‖ ≤ ‖(y:Kv) - y'‖ * r :=
          mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
      _ = r / ‖(2 : Kv)‖ * ‖(y:Kv) - y'‖ * ‖(2 : Kv)‖ := by field_simp
  obtain ⟨y, -, hfix, -⟩ := ContractingWith.exists_fixedPoint' (Metric.isClosed_closedBall.isComplete)
    hmaps hcon (x := 0) (by simp [s, hr0]) (edist_ne_top _ _)
  refine ⟨1 + y, ?_⟩
  have : f y = y := hfix
  simp only [f] at this
  have h2' : (2:Kv) * y = e - y^2 := by
    have h3 : (2:Kv) * ((e - y^2)/2) = 2 * y := by rw [this]
    rw [mul_div_cancel₀ _ h2K] at h3
    exact h3.symm
  rw [he] at h2'
  linear_combination -h2'


/-- $\exp(-(n+1)) \le 1$. -/
lemma exp_neg_succ_le_one (n : ℕ) : exp (-((n : ℤ) + 1)) ≤ (1 : ℤᵐ⁰) := by
  rw [← exp_zero, exp_le_exp]; omega

/-- Elements of $U^{(n+1)}$ are units. -/
lemma valued_eq_one_of_sub_le {x : Kv} {n : ℕ} (hx : Valued.v (x - 1) ≤ exp (-((n : ℤ) + 1))) :
    Valued.v x = 1 := by
  have hlt : Valued.v (x - 1) < Valued.v (1 : Kv) := by
    rw [map_one]
    exact lt_of_le_of_lt hx (by rw [← exp_zero, exp_lt_exp]; omega)
  have : x = 1 + (x - 1) := by ring
  rw [this, Valuation.map_add_eq_of_lt_left _ hlt, map_one]

/-- The higher unit group $U^{(n+1)} = \{x : v(x - 1) \le \exp(-(n+1))\}$ of $K_v^\times$. -/
@[kb "omeara1963" "§63A, p. 162 (the groups 1 + 𝔭ʳ)"]
def Ufil (n : ℕ) : Subgroup Kvˣ where
  carrier := {x | Valued.v ((x : Kv) - 1) ≤ exp (-((n : ℤ) + 1))}
  one_mem' := by simp
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at hx hy ⊢
    have e : (x : Kv) * y - 1 = ((x : Kv) - 1) * ((y : Kv) - 1) + (((x : Kv) - 1) + ((y : Kv) - 1)) := by
      ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ((Valuation.map_add _ _ _).trans (max_le hx hy)))
    rw [map_mul]
    calc Valued.v ((x : Kv) - 1) * Valued.v ((y : Kv) - 1) ≤ exp (-((n : ℤ) + 1)) * 1 :=
          mul_le_mul' hx ((hy.trans (exp_neg_succ_le_one n)))
      _ = _ := mul_one _
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val] at hx ⊢
    have hx1 := valued_eq_one_of_sub_le v hx
    have hx0 : (x : Kv) ≠ 0 := x.ne_zero
    have e : (x : Kv)⁻¹ - 1 = -((x : Kv) - 1) * (x : Kv)⁻¹ := by field_simp; ring
    rw [e, map_mul, Valuation.map_neg, map_inv₀, hx1, inv_one, mul_one]
    exact hx

/-- Membership in $U^{(n+1)}$. -/
lemma mem_Ufil {n : ℕ} {x : Kvˣ} :
    x ∈ Ufil v n ↔ Valued.v ((x : Kv) - 1) ≤ exp (-((n : ℤ) + 1)) := Iff.rfl

/-- The unit group $U = \mathcal O_v^\times$ of $K_v^\times$. -/
abbrev U0 : Subgroup Kvˣ := (v.adicCompletionIntegers K).units

/-- Membership in $\mathcal O_v^\times$. -/
lemma mem_U0 {x : Kvˣ} : x ∈ U0 v ↔ Valued.v (x : Kv) = 1 :=
  HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one

/-- $U^{(n+1)} \subseteq \mathcal O_v^\times$. -/
lemma Ufil_le_U0 (n : ℕ) : Ufil v n ≤ U0 v := fun x hx =>
  (mem_U0 v).mpr (valued_eq_one_of_sub_le v hx)

/-- Nonzero values of the valuation are powers of `exp 1`. -/
lemma exists_exp_eq {x : Kv} (hx : x ≠ 0) : ∃ k : ℤ, Valued.v x = exp k := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp h0
  exact ⟨Multiplicative.toAdd a, by rw [← ha]; rfl⟩


local notation "Ov" => v.adicCompletionIntegers K

/-- A uniformizer of $K_v$ (coming from $K$). -/
def ϖ : Kv := algebraMap K Kv (v.valuation_exists_uniformizer K).choose

/-- $v(\varpi) = \exp(-1)$. -/
lemma valued_ϖ : Valued.v (ϖ v) = exp (-1 : ℤ) := by
  rw [ϖ, valued_algebraMap]; exact (v.valuation_exists_uniformizer K).choose_spec

/-- $\varpi \ne 0$. -/
lemma ϖ_ne_zero : ϖ v ≠ 0 := by
  intro h; have := valued_ϖ v; rw [h, map_zero] at this; exact exp_ne_zero this.symm

/-- $v(\varpi^n) = \exp(-n)$. -/
lemma valued_ϖ_pow (n : ℕ) : Valued.v (ϖ v ^ n) = exp (-(n : ℤ)) := by
  rw [map_pow, valued_ϖ, ← exp_nsmul]; congr 1; simp

/-- The uniformizer as an element of $\mathcal O_v$. -/
def ϖO : Ov := ⟨ϖ v, by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_ϖ, ← exp_zero, exp_le_exp]; omega⟩

/-- $z \in \varpi^n \mathcal O_v$ iff $v(z) \le \exp(-n)$. -/
lemma mem_span_ϖ_pow (n : ℕ) (z : Ov) :
    z ∈ Ideal.span {ϖO v ^ n} ↔ Valued.v (z : Kv) ≤ exp (-(n : ℤ)) := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    have e : (((ϖO v ^ n * c : Ov)) : Kv) = (ϖ v) ^ n * (c : Kv) := rfl
    rw [e, map_mul, valued_ϖ_pow]
    have hc : Valued.v (c : Kv) ≤ 1 := c.2
    calc exp (-(n : ℤ)) * Valued.v (c : Kv) ≤ exp (-(n : ℤ)) * 1 := mul_le_mul_right hc _
      _ = _ := mul_one _
  · intro hz
    have hϖn : (ϖ v) ^ n ≠ 0 := pow_ne_zero _ (ϖ_ne_zero v)
    refine ⟨⟨(z : Kv) / (ϖ v) ^ n, ?_⟩, ?_⟩
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, valued_ϖ_pow, div_le_one₀]
      · exact hz
      · exact exp_pos
    · apply Subtype.ext
      change (z : Kv) = (ϖ v) ^ n * ((z : Kv) / (ϖ v) ^ n)
      field_simp


/-- $t(x) = (x - 1)/\varpi^{m+1} \in \mathcal O_v$ for $x \in U^{(m+1)}$. -/
def tval (m : ℕ) (x : Ufil v m) : Ov := ⟨(((x : Kvˣ) : Kv) - 1) / (ϖ v) ^ (m + 1), by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, valued_ϖ_pow,
    div_le_one₀ exp_pos]
  have := x.2
  rw [mem_Ufil] at this
  simpa using this⟩

/-- Unfolding `tval`. -/
lemma tval_coe (m : ℕ) (x : Ufil v m) :
    ((tval v m x : Ov) : Kv) = (((x : Kvˣ) : Kv) - 1) / (ϖ v) ^ (m + 1) := rfl

/-- $x - 1 = \varpi^{m+1} t(x)$. -/
lemma sub_one_eq_tval (m : ℕ) (x : Ufil v m) :
    ((x : Kvˣ) : Kv) - 1 = (ϖ v) ^ (m + 1) * (tval v m x : Kv) := by
  rw [tval_coe]; field_simp [pow_ne_zero (m + 1) (ϖ_ne_zero v)]

/-- **The map $U^{(m+1)} \to \mathcal O_v/\varpi^n$, $x \mapsto (x-1)/\varpi^{m+1}$**, a homomorphism for
$n \le m + 1$. -/
def ψ (m n : ℕ) (hnm : n ≤ m + 1) : Ufil v m →* Multiplicative (Ov ⧸ Ideal.span {ϖO v ^ n}) where
  toFun x := Multiplicative.ofAdd (Ideal.Quotient.mk _ (tval v m x))
  map_one' := by
    rw [← ofAdd_zero]; congr 1
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have : tval v m 1 = 0 := by
      apply Subtype.ext; rw [tval_coe]; simp
    rw [this]; exact zero_mem _
  map_mul' x y := by
    rw [← ofAdd_add]; congr 1
    rw [← map_add, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    -- t(xy) = t x + t y + ϖ^{m+1} t x t y
    set a := tval v m x; set b := tval v m y
    refine ⟨ϖO v ^ (m + 1 - n) * a * b, ?_⟩
    apply Subtype.ext
    have hx := sub_one_eq_tval v m x
    have hy := sub_one_eq_tval v m y
    have hxy := sub_one_eq_tval v m (x * y)
    have hϖ : (ϖ v) ^ (m + 1) ≠ 0 := pow_ne_zero _ (ϖ_ne_zero v)
    change ((tval v m (x * y) : Kv)) - ((a : Kv) + (b : Kv)) =
      (ϖ v) ^ n * ((ϖ v) ^ (m + 1 - n) * (a : Kv) * (b : Kv))
    have hpow : (ϖ v) ^ n * (ϖ v) ^ (m + 1 - n) = (ϖ v) ^ (m + 1) := by
      rw [← pow_add]; congr 1; omega
    have key : (ϖ v) ^ (m + 1) * (tval v m (x * y) : Kv) =
        (ϖ v) ^ (m + 1) * ((a : Kv) + (b : Kv) + (ϖ v) ^ (m + 1) * (a : Kv) * (b : Kv)) := by
      rw [← hxy]
      have : (((x * y : Ufil v m) : Kvˣ) : Kv) = ((x : Kvˣ) : Kv) * ((y : Kvˣ) : Kv) := rfl
      rw [this]
      have ex : ((x : Kvˣ) : Kv) = 1 + (ϖ v) ^ (m + 1) * (a : Kv) := by rw [← hx]; ring
      have ey : ((y : Kvˣ) : Kv) = 1 + (ϖ v) ^ (m + 1) * (b : Kv) := by rw [← hy]; ring
      rw [ex, ey]; ring
    have key' := mul_left_cancel₀ hϖ key
    rw [key', ← hpow]; ring


/-- The filtration is decreasing. -/
lemma Ufil_anti {m n : ℕ} (h : m ≤ n) : Ufil v n ≤ Ufil v m := by
  intro x hx
  rw [mem_Ufil] at hx ⊢
  exact hx.trans (by rw [exp_le_exp]; omega)

/-- $\ker \psi = U^{(m+n+1)}$. -/
lemma ψ_ker (m n : ℕ) (hnm : n ≤ m + 1) :
    (ψ v m n hnm).ker = (Ufil v (m + n)).subgroupOf (Ufil v m) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_Ufil]
  change Multiplicative.ofAdd (Ideal.Quotient.mk _ (tval v m x)) = 1 ↔ _
  rw [← ofAdd_zero, Multiplicative.ofAdd.apply_eq_iff_eq, Ideal.Quotient.eq_zero_iff_mem, mem_span_ϖ_pow,
    sub_one_eq_tval, map_mul, valued_ϖ_pow]
  constructor
  · intro h
    calc exp (-((m + 1 : ℕ) : ℤ)) * Valued.v (tval v m x : Kv) ≤ exp (-((m + 1 : ℕ) : ℤ)) * exp (-(n : ℤ)) :=
          mul_le_mul_right h _
      _ = exp (-(((m + n : ℕ) : ℤ) + 1)) := by rw [← exp_add]; congr 1; push_cast; ring
  · intro h
    have h' : exp (-((m + 1 : ℕ) : ℤ)) * Valued.v (tval v m x : Kv) ≤
        exp (-((m + 1 : ℕ) : ℤ)) * exp (-(n : ℤ)) := by
      refine h.trans (le_of_eq ?_); rw [← exp_add]; congr 1; push_cast; ring
    exact le_of_mul_le_mul_left h' exp_pos

/-- $\psi$ is surjective. -/
lemma ψ_surjective (m n : ℕ) (hnm : n ≤ m + 1) : Function.Surjective (ψ v m n hnm) := by
  intro q
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (Multiplicative.toAdd q)
  set x : Kv := 1 + (ϖ v) ^ (m + 1) * (z : Kv) with hxdef
  have hx1 : Valued.v (x - 1) ≤ exp (-((m : ℤ) + 1)) := by
    rw [hxdef, add_sub_cancel_left, map_mul, valued_ϖ_pow]
    calc exp (-((m + 1 : ℕ) : ℤ)) * Valued.v (z : Kv) ≤ exp (-((m + 1 : ℕ) : ℤ)) * 1 :=
          mul_le_mul_right z.2 _
      _ = _ := by rw [mul_one]; push_cast; ring_nf
  have hx0 : x ≠ 0 := by
    intro h; have := valued_eq_one_of_sub_le v hx1; rw [h, map_zero] at this
    exact zero_ne_one this
  refine ⟨⟨Units.mk0 x hx0, hx1⟩, ?_⟩
  change Multiplicative.ofAdd (Ideal.Quotient.mk _ (tval v m _)) = q
  have ht : tval v m ⟨Units.mk0 x hx0, hx1⟩ = z := by
    apply Subtype.ext
    rw [tval_coe, Units.val_mk0, hxdef, add_sub_cancel_left]
    field_simp [pow_ne_zero (m + 1) (ϖ_ne_zero v)]
  rw [ht, hz]; rfl

/-- **$[U^{(m+1)} : U^{(m+n+1)}] = |\mathcal O_v/\varpi^n|$** for $n \le m + 1$. -/
@[kb "neukirch1999" "Ch. II, Prop. 3.10 [unverified]; omeara1963 §63A, 63:8 (1), p. 163"]
theorem relIndex_Ufil (m n : ℕ) (hnm : n ≤ m + 1) :
    (Ufil v (m + n)).relIndex (Ufil v m) = Nat.card (Ov ⧸ Ideal.span {ϖO v ^ n}) := by
  rw [Subgroup.relIndex, ← ψ_ker v m n hnm, Subgroup.index_ker,
    MonoidHom.range_eq_top_of_surjective _ (ψ_surjective v m n hnm), Subgroup.card_top]
  rfl


/-- The valuation of an integer of $K$ in $K_v$. -/
lemma valued_algebraMap_int (x : 𝓞 K) :
    Valued.v ((algebraMap (𝓞 K) Ov x : Ov) : Kv) = v.intValuation x := by
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

/-- Elements of $\mathcal O_v$ are approximated mod $\mathfrak m_v$ by elements of $\mathcal O_K$. -/
lemma exists_int_approx (z : Ov) : ∃ x : 𝓞 K, Valued.v ((z : Kv) - (algebraMap (𝓞 K) Ov x : Kv)) < 1 := by
  obtain ⟨y, hy⟩ : ∃ y : K, Valued.v ((z : Kv) - algebraMap K Kv y) < 1 := by
    have hn : {w : Kv | Valued.v ((z : Kv) - w) < 1} ∈ nhds (z : Kv) := by
      have h0 : {u : Kv | Valued.v u < 1} ∈ nhds (0 : Kv) := Valued.mem_nhds.mpr ⟨1, by simp⟩
      have hcont : Continuous fun w : Kv => (z : Kv) - w := continuous_const.sub continuous_id
      have := hcont.continuousAt (x := (z : Kv)) (by simpa using h0)
      exact this
    obtain ⟨_, h1, ⟨y, rfl⟩⟩ := mem_closure_iff_nhds.mp
      (HeightOneSpectrum.denseRange_algebraMap K v (z : Kv)) _ hn
    exact ⟨y, h1⟩
  have hz : Valued.v (z : Kv) ≤ 1 := z.2
  have hyv : v.valuation K y ≤ 1 := by
    rw [← valued_algebraMap]
    have : algebraMap K Kv y = (z : Kv) - ((z : Kv) - algebraMap K Kv y) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le hz hy.le)
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v y hyv
  have := v.isMaximal
  let := Ideal.Quotient.field v.asIdeal
  have hd : Ideal.Quotient.mk v.asIdeal (d : 𝓞 K) ≠ 0 := by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]; exact d.2
  obtain ⟨d', hd'⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk v.asIdeal (d : 𝓞 K))⁻¹
  have hdd : (d : 𝓞 K) * d' - 1 ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hd', mul_inv_cancel₀ hd, map_one, sub_self]
  refine ⟨n * d', ?_⟩
  have hdK : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
    intro h0; apply d.2; rw [h0]; exact zero_mem _
  have hyx : v.valuation K (y - algebraMap (𝓞 K) K (n * d')) < 1 := by
    have e : y - algebraMap (𝓞 K) K (n * d') =
        -(algebraMap (𝓞 K) K n * algebraMap (𝓞 K) K ((d : 𝓞 K) * d' - 1)) / algebraMap (𝓞 K) K (d : 𝓞 K) := by
      rw [eq_div_iff hdK]; simp only [map_mul, map_sub, map_one]; linear_combination hnd
    rw [e, map_div₀, Valuation.map_neg, map_mul, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v d).mpr d.2, div_one]
    calc v.intValuation n * v.intValuation ((d : 𝓞 K) * d' - 1) ≤ 1 * v.intValuation ((d : 𝓞 K) * d' - 1) :=
          mul_le_mul_left (v.intValuation_le_one n) _
      _ < 1 := by rw [one_mul]; exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).mpr hdd
  have e2 : ((algebraMap (𝓞 K) Ov (n * d') : Ov) : Kv) = algebraMap K Kv (algebraMap (𝓞 K) K (n * d')) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    rw [HeightOneSpectrum.algebraMap_adicCompletion (𝓞 K)]
    rfl
  rw [e2]
  have : (z : Kv) - algebraMap K Kv (algebraMap (𝓞 K) K (n * d')) =
      ((z : Kv) - algebraMap K Kv y) + algebraMap K Kv (y - algebraMap (𝓞 K) K (n * d')) := by
    rw [map_sub]; ring
  rw [this]
  refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hy ?_)
  rw [valued_algebraMap]; exact hyx


/-- The maximal ideal of $\mathcal O_v$ is $\{v < 1\}$. -/
lemma mem_maximalIdeal_iff (z : Ov) :
    z ∈ IsLocalRing.maximalIdeal Ov ↔ Valued.v (z : Kv) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have hz : Valued.v (z : Kv) ≤ 1 := z.2
  constructor
  · intro h; exact lt_of_le_of_ne hz h
  · intro h h1; rw [h1] at h; exact lt_irrefl _ h

/-- **The residue field of $K_v$ has $N\mathfrak p$ elements.** -/
@[kb "neukirch1999" "Ch. II §4 [unverified]"]
theorem card_residueField : Nat.card (IsLocalRing.ResidueField Ov) = Ideal.absNorm v.asIdeal := by
  let φ : 𝓞 K →+* IsLocalRing.ResidueField Ov :=
    (IsLocalRing.residue Ov).comp (algebraMap (𝓞 K) Ov)
  have hsurj : Function.Surjective φ := by
    intro r
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨x, hx⟩ := exists_int_approx v z
    refine ⟨x, ?_⟩
    simp only [φ, RingHom.coe_comp, Function.comp_apply]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff,
      ← Valuation.map_neg]
    simpa using hx
  have hker : RingHom.ker φ = v.asIdeal := by
    ext x
    rw [RingHom.mem_ker]
    simp only [φ, RingHom.coe_comp, Function.comp_apply]
    rw [IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff, valued_algebraMap_int,
      HeightOneSpectrum.intValuation_lt_one_iff_mem]
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hker]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv).symm


/-- Discreteness: $v(x) < 1 \Rightarrow v(x) \le \exp(-1)$. -/
lemma valued_le_exp_neg_one {x : Kv} (hx : Valued.v x < 1) : Valued.v x ≤ exp (-1 : ℤ) := by
  by_cases h0 : x = 0
  · rw [h0, map_zero]; exact zero_le
  obtain ⟨k, hk⟩ := exists_exp_eq v h0
  rw [hk] at hx ⊢
  rw [← exp_zero, exp_lt_exp] at hx
  rw [exp_le_exp]; omega

/-- $\varpi$ is a uniformizer of $\mathcal O_v$. -/
lemma irreducible_ϖO : Irreducible (ϖO v) := by
  have hv : Valued.v ((ϖO v : Ov) : Kv) = exp (-1 : ℤ) := valued_ϖ v
  refine ⟨?_, ?_⟩
  · rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one, hv]
    rw [← exp_zero, exp_inj]; omega
  · intro a b hab
    by_contra hc
    push Not at hc
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hc
    have ha : Valued.v (a : Kv) ≤ exp (-1 : ℤ) := valued_le_exp_neg_one v (lt_of_le_of_ne a.2 hc.1)
    have hb : Valued.v (b : Kv) ≤ exp (-1 : ℤ) := valued_le_exp_neg_one v (lt_of_le_of_ne b.2 hc.2)
    have : Valued.v ((ϖO v : Ov) : Kv) = Valued.v (a : Kv) * Valued.v (b : Kv) := by
      rw [hab]; exact map_mul _ _ _
    rw [hv] at this
    have h2 : Valued.v (a : Kv) * Valued.v (b : Kv) ≤ exp (-1 : ℤ) * exp (-1 : ℤ) := mul_le_mul' ha hb
    rw [← this, ← exp_add, exp_le_exp] at h2
    omega

/-- The residue field is finite. -/
instance : Finite (IsLocalRing.ResidueField Ov) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_residueField]
  exact (Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr  -- placeholder
    (mem_nonZeroDivisors_of_ne_zero v.ne_bot)

/-- **$|\mathcal O_v/\varpi^n| = (N\mathfrak p)^n$.** -/
@[kb "serre1973" "Ch. II §1 [unverified]"]
theorem card_quot_ϖ_pow (n : ℕ) :
    Nat.card (Ov ⧸ Ideal.span {ϖO v ^ n}) = Ideal.absNorm v.asIdeal ^ n := by
  have hspan : Ideal.span {ϖO v ^ n} = (IsLocalRing.maximalIdeal Ov) ^ n := by
    rw [← Ideal.span_singleton_pow, (irreducible_ϖO v).maximalIdeal_eq]
  rw [hspan, ← Submodule.cardQuot_apply,
    _root_.cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field Ov),
    Submodule.cardQuot_apply, ← card_residueField]
  rfl


/-- The element of `𝓞_v` underlying a unit of valuation `1`. -/
def toOv (x : U0 v) : Ov := ⟨((x : Kvˣ) : Kv), ((mem_U0 v).mp x.2).le⟩

/-- A valuation-one element is a unit of $\mathcal O_v$. -/
lemma isUnit_toOv (x : U0 v) : IsUnit (toOv v x) :=
  HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr ((mem_U0 v).mp x.2)

/-- Reduction of units: $\mathcal O_v^\times \to k_v^\times$. -/
def χ0 : U0 v →* (IsLocalRing.ResidueField Ov)ˣ where
  toFun x := Units.map (IsLocalRing.residue Ov : Ov →* IsLocalRing.ResidueField Ov) (isUnit_toOv v x).unit
  map_one' := by ext; simp [toOv]
  map_mul' x y := by
    ext
    simp only [toOv, Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe, Units.val_mul]
    rw [← map_mul]; rfl

/-- $\ker \chi_0 = U^{(1)}$. -/
lemma χ0_ker : (χ0 v).ker = (Ufil v 0).subgroupOf (U0 v) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_Ufil, Units.ext_iff]
  simp only [χ0, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_map, IsUnit.unit_spec,
    MonoidHom.coe_ofClass, Units.val_one]
  rw [← sub_eq_zero, ← map_one (IsLocalRing.residue Ov), ← map_sub,
    IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff]
  simp only [CharP.cast_eq_zero, zero_add, Int.reduceNeg]
  constructor
  · intro h; exact valued_le_exp_neg_one v h
  · intro h; exact lt_of_le_of_lt h (by rw [← exp_zero, exp_lt_exp]; omega)

/-- $[\mathcal O_v^\times : U^{(1)}]$ is finite. -/
lemma relIndex_Ufil_zero_ne_zero : (Ufil v 0).relIndex (U0 v) ≠ 0 := by
  rw [Subgroup.relIndex, ← χ0_ker, Subgroup.index_ker]
  exact Nat.card_pos.ne'

/-- $[\mathcal O_v^\times : U^{(n+1)}]$ is finite. -/
lemma relIndex_Ufil_ne_zero (n : ℕ) : (Ufil v n).relIndex (U0 v) ≠ 0 := by
  induction n with
  | zero => exact relIndex_Ufil_zero_ne_zero v
  | succ n ih =>
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ (Ufil_anti v (Nat.le_succ n)) (Ufil_le_U0 v n)]
    refine mul_ne_zero ?_ ih
    have := relIndex_Ufil v n 1 (by omega)
    rw [this, card_quot_ϖ_pow, pow_one]
    exact (Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr (mem_nonZeroDivisors_of_ne_zero v.ne_bot)


/-- $e_v = \operatorname{ord}_v(2)$, the absolute ramification index of $v$ over $2$ (0 if $v \nmid 2$). -/
def ordTwo : ℕ := multiplicity v.asIdeal (Ideal.span {(2 : 𝓞 K)})

/-- $v(2) = \exp(-e)$. -/
@[kb "omeara1963" "§63, p. 159 (dyadic if and only if 0 < |2| < 1)"]
lemma valued_two : Valued.v (2 : Kv) = exp (-(ordTwo v : ℤ)) := by
  have h2 : (2 : 𝓞 K) ≠ 0 := two_ne_zero
  have : (2 : Kv) = algebraMap K Kv (algebraMap (𝓞 K) K 2) := by rw [map_ofNat, map_ofNat]
  rw [this, valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ h2]
  rfl

/-- Discreteness of $\mathbb Z^{\times 0}$-values. -/
lemma ge_exp_of_gt {a : ℤᵐ⁰} {k : ℤ} (h : exp (k - 1) < a) : exp k ≤ a := by
  have ha : a ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le h)
  obtain ⟨b, rfl⟩ := WithZero.ne_zero_iff_exists.mp ha
  rw [show ((b : ℤᵐ⁰)) = exp (Multiplicative.toAdd b) from rfl] at h ⊢
  rw [exp_lt_exp] at h; rw [exp_le_exp]; omega

/-- **Square roots of higher units:** for a unit $y$, $y^2 \in U^{(2e+1)}$ iff $\pm y \in U^{(e+1)}$
($e = \operatorname{ord}_v 2$). -/
lemma sq_mem_Ufil_iff (y : Kvˣ) :
    y ^ 2 ∈ Ufil v (2 * ordTwo v) ↔ y ∈ Ufil v (ordTwo v) ∨ -y ∈ Ufil v (ordTwo v) := by
  set e := ordTwo v
  have h2 := valued_two v
  simp only [mem_Ufil, Units.val_pow_eq_pow_val, Units.val_neg]
  have hfac : ((y : Kv)) ^ 2 - 1 = ((y : Kv) - 1) * ((y : Kv) + 1) := by ring
  have hneg : -(y : Kv) - 1 = -((y : Kv) + 1) := by ring
  rw [hfac, map_mul, hneg, Valuation.map_neg]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have h1 : exp (-(e : ℤ)) ≤ Valued.v ((y : Kv) - 1) := ge_exp_of_gt (by
      have := hc.1; refine lt_of_eq_of_lt ?_ this; congr 1; ring)
    have h1' : exp (-(e : ℤ)) ≤ Valued.v ((y : Kv) + 1) := ge_exp_of_gt (by
      have := hc.2; refine lt_of_eq_of_lt ?_ this; congr 1; ring)
    have := mul_le_mul' h1 h1'
    rw [← exp_add] at this
    have := this.trans h
    rw [exp_le_exp] at this
    push_cast at this
    omega
  · have key : ∀ z : Kv, Valued.v (z - 1) ≤ exp (-((e : ℤ) + 1)) →
        Valued.v (z + 1) ≤ exp (-(e : ℤ)) := by
      intro z hz
      have : z + 1 = (z - 1) + 2 := by ring
      rw [this]
      refine (Valuation.map_add _ _ _).trans (max_le ?_ h2.le)
      exact hz.trans (by rw [exp_le_exp]; omega)
    rintro (h | h)
    · have := mul_le_mul' h (key _ h)
      refine this.trans (le_of_eq ?_)
      rw [← exp_add]; congr 1; push_cast; ring
    · have h' : Valued.v (-(y : Kv) - 1) ≤ exp (-((e : ℤ) + 1)) := by
        rw [hneg, Valuation.map_neg]; exact h
      have h3 := key _ h'
      have e3 : -(y : Kv) + 1 = -((y : Kv) - 1) := by ring
      rw [e3, Valuation.map_neg] at h3
      have := mul_le_mul' h3 h
      refine this.trans (le_of_eq ?_)
      rw [← exp_add]; congr 1; push_cast; ring


/-- Relative index in a range is the index of the preimage. -/
@[kb "omeara1963" "§63A, 63:7, p. 162"]
lemma relIndex_range_eq_index_comap_mul {G H : Type*} [Group G] [Group H] (f : G →* H)
    (A : Subgroup H) : A.relIndex f.range = (A.comap f).index := by
  rw [Subgroup.relIndex, ← Subgroup.index_comap_of_surjective _ f.rangeRestrict_surjective]
  congr 1

/-- **Squares in the units:** $[\mathcal O_v^\times : \mathcal O_v^{\times 2}] = 2\,(N\mathfrak p)^{e}$, $e = \operatorname{ord}_v 2$. -/
@[kb "milne2020cft" "Ch. VII, Prop. 6.8 (n = 2) [unverified]; omeara1963 §63A, 63:9, p. 163 (the middle term 2(𝔲 : 𝔲²))"]
theorem index_sq_U0 :
    (powMonoidHom 2 : U0 v →* U0 v).range.index = 2 * Ideal.absNorm v.asIdeal ^ ordTwo v := by
  classical
  set e := ordTwo v
  set G := U0 v
  set sq : G →* G := powMonoidHom 2
  set WG := (Ufil v (2 * e)).subgroupOf G
  set W'G := (Ufil v e).subgroupOf G
  have hneg1 : (-1 : Kvˣ) ∈ G := by rw [mem_U0]; simp
  set n1 : G := ⟨-1, hneg1⟩
  -- WG ≤ squares
  have hW : WG ≤ sq.range := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, mem_Ufil] at hx
    have hlt : Valued.v (((x : Kvˣ) : Kv) - 1) < Valued.v (4 : Kv) := by
      have h4 : (4 : Kv) = 2 * 2 := by norm_num
      rw [h4, map_mul, valued_two, ← exp_add]
      exact lt_of_le_of_lt hx (by rw [exp_lt_exp]; push_cast; omega)
    obtain ⟨r, hr⟩ := isSquare_of_valued_sub_one_lt v _ hlt
    have hr0 : r ≠ 0 := by
      rintro rfl; simp at hr
    have hrv : Valued.v r = 1 := by
      have hx1 : Valued.v ((x : Kvˣ) : Kv) = 1 := (mem_U0 v).mp x.2
      rw [hr, map_mul] at hx1
      have := eq_one_of_pow_eq_one (n := 2) two_ne_zero (by rw [pow_two]; exact hx1)
      exact this
    refine ⟨⟨Units.mk0 r hr0, (mem_U0 v).mpr hrv⟩, ?_⟩
    apply Subtype.ext; apply Units.ext
    simp [sq, hr, pow_two]
  -- preimage of WG under squaring
  have hcomap : WG.comap sq = W'G ⊔ Subgroup.zpowers n1 := by
    have hn1sq : n1 ^ 2 = 1 := by apply Subtype.ext; apply Units.ext; simp [n1]
    have hz : ∀ b : G, b ∈ Subgroup.zpowers n1 ↔ b = 1 ∨ b = n1 := by
      intro b
      constructor
      · rintro ⟨k, rfl⟩
        rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
        · left; simp only [hj, ← two_mul, zpow_mul]
          rw [show n1 ^ (2 : ℤ) = 1 by exact_mod_cast hn1sq, one_zpow]
        · right; simp only [hj, zpow_add, zpow_mul, zpow_one]
          rw [show n1 ^ (2 : ℤ) = 1 by exact_mod_cast hn1sq, one_zpow, one_mul]
      · rintro (rfl | rfl)
        · exact one_mem _
        · exact Subgroup.mem_zpowers n1
    ext y
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    change ((y : Kvˣ)) ^ 2 ∈ Ufil v (2 * e) ↔ _
    rw [sq_mem_Ufil_iff, Subgroup.mem_sup]
    constructor
    · rintro (h | h)
      · exact ⟨y, h, 1, one_mem _, mul_one y⟩
      · refine ⟨y * n1, ?_, n1, Subgroup.mem_zpowers n1, ?_⟩
        · rw [Subgroup.mem_subgroupOf]; simpa [n1] using h
        · rw [mul_assoc, ← pow_two, hn1sq, mul_one]
    · rintro ⟨a, ha, b, hb, rfl⟩
      rw [Subgroup.mem_subgroupOf] at ha
      rcases (hz b).mp hb with rfl | rfl
      · left; simpa using ha
      · right; simpa [n1] using ha
  have hn1 : n1 ∉ W'G := by
    rw [Subgroup.mem_subgroupOf, mem_Ufil]
    simp only [n1, Units.val_neg, Units.val_one]
    rw [show (-1 : Kv) - 1 = -2 by ring, Valuation.map_neg, valued_two, exp_le_exp]
    omega
  have hn1ne : n1 ≠ 1 := fun h => hn1 (h ▸ one_mem _)
  have hn1sq : n1 ^ 2 = 1 := by apply Subtype.ext; apply Units.ext; simp [n1]
  have hord : orderOf n1 = 2 := orderOf_eq_prime hn1sq hn1ne
  have hidx2 : W'G.relIndex (W'G ⊔ Subgroup.zpowers n1) = 2 := by
    rw [Subgroup.relIndex_sup_left]
    have hbot : W'G.subgroupOf (Subgroup.zpowers n1) = ⊥ := by
      rw [eq_bot_iff]
      rintro ⟨b, hb⟩ hbW
      rw [Subgroup.mem_subgroupOf] at hbW
      rw [Subgroup.mem_bot]
      obtain ⟨k, rfl⟩ := hb
      apply Subtype.ext
      simp only [OneMemClass.coe_one]
      rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · simp only [hj, ← two_mul, zpow_mul]
        rw [show n1 ^ (2 : ℤ) = 1 by exact_mod_cast hn1sq, one_zpow]
      · exfalso; apply hn1
        have : n1 ^ k = n1 := by
          simp only [hj, zpow_add, zpow_mul, zpow_one]
          rw [show n1 ^ (2 : ℤ) = 1 by exact_mod_cast hn1sq, one_zpow, one_mul]
        simpa [this] using hbW
    have hcm := Subgroup.card_mul_index (W'G.subgroupOf (Subgroup.zpowers n1))
    rw [hbot, Subgroup.card_bot, one_mul, Nat.card_zpowers, hord] at hcm
    rw [Subgroup.relIndex, hbot] at *
    exact hcm
  have hA := Subgroup.relIndex_mul_index hW
  have hB : WG.relIndex sq.range = (W'G ⊔ Subgroup.zpowers n1).index := by
    rw [relIndex_range_eq_index_comap_mul, hcomap]
  have hC := Subgroup.relIndex_mul_index (le_sup_left : W'G ≤ W'G ⊔ Subgroup.zpowers n1)
  have hWW : WG ≤ W'G := fun x hx => Ufil_anti v (show e ≤ 2 * e by omega) hx
  have hD := Subgroup.relIndex_mul_index hWW
  have hD' : WG.relIndex W'G = Ideal.absNorm v.asIdeal ^ e := by
    rw [Subgroup.relIndex_subgroupOf (Ufil_le_U0 v e)]
    have := relIndex_Ufil v e e (by omega)
    rw [show e + e = 2 * e by ring] at this
    rw [this, card_quot_ϖ_pow]
  have hW'0 : W'G.index ≠ 0 := by
    have := relIndex_Ufil_ne_zero v e
    rwa [Subgroup.relIndex] at this
  rw [hB] at hA
  rw [hidx2] at hC
  rw [hD'] at hD
  have hX : (W'G ⊔ Subgroup.zpowers n1).index ≠ 0 := by
    intro h; rw [h, mul_zero] at hC; exact hW'0 hC.symm
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hX)
  calc sq.range.index * (W'G ⊔ Subgroup.zpowers n1).index = WG.index := by rw [← hA, mul_comm]
    _ = Ideal.absNorm v.asIdeal ^ e * W'G.index := hD.symm
    _ = Ideal.absNorm v.asIdeal ^ e * (2 * (W'G ⊔ Subgroup.zpowers n1).index) := by rw [hC]
    _ = 2 * Ideal.absNorm v.asIdeal ^ e * (W'G ⊔ Subgroup.zpowers n1).index := by ring


/-- The uniformizer as a unit of $K_v$. -/
def ϖu : Kvˣ := Units.mk0 (ϖ v) (ϖ_ne_zero v)

/-- $v(\varpi^j) = \exp(-j)$. -/
lemma valued_ϖu_zpow (j : ℤ) : Valued.v (((ϖu v) ^ j : Kvˣ) : Kv) = exp (-j) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ϖu, Units.val_mk0, valued_ϖ, ← exp_zsmul]
  congr 1; simp

/-- $x \in K_v^{\times2}\mathcal O_v^\times$ iff $v(x)$ has even exponent. -/
lemma mem_sq_sup_U0_iff (x : Kvˣ) :
    x ∈ (powMonoidHom 2 : Kvˣ →* Kvˣ).range ⊔ U0 v ↔ ∃ j : ℤ, Valued.v (x : Kv) = exp (2 * j) := by
  rw [Subgroup.mem_sup]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, u, hu, rfl⟩
    obtain ⟨k, hk⟩ := exists_exp_eq v (y : Kvˣ).ne_zero
    refine ⟨k, ?_⟩
    simp only [powMonoidHom_apply, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hk,
      (mem_U0 v).mp hu, mul_one, ← exp_nsmul]
    congr 1
  · rintro ⟨j, hj⟩
    refine ⟨(ϖu v ^ (-j)) ^ 2, ⟨ϖu v ^ (-j), rfl⟩, ((ϖu v ^ (-j)) ^ 2)⁻¹ * x, ?_, by group⟩
    rw [mem_U0, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
      Units.val_pow_eq_pow_val, map_pow, valued_ϖu_zpow, hj, neg_neg, ← exp_nsmul, ← exp_neg,
      ← exp_add]
    rw [← exp_zero]; congr 1; simp

/-- **Square classes of a completion:** $[K_v^\times : K_v^{\times 2}] = 4\,(N\mathfrak p)^{e}$ with
$e = \operatorname{ord}_v 2$ (so $= 4$ when $v \nmid 2$). -/
@[kb "milne2020cft" "Ch. VII, Prop. 6.8 (n = 2) [unverified]; omeara1963 §63A, 63:9, p. 163"]
theorem index_sq_completion :
    (powMonoidHom 2 : Kvˣ →* Kvˣ).range.index = 4 * Ideal.absNorm v.asIdeal ^ ordTwo v := by
  classical
  set Sq := (powMonoidHom 2 : Kvˣ →* Kvˣ).range
  set H := Sq ⊔ U0 v
  have hH : H.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨ϖu v, fun b => ?_⟩
    obtain ⟨k, hk⟩ := exists_exp_eq v (b : Kvˣ).ne_zero
    have hbϖ : Valued.v ((b * ϖu v : Kvˣ) : Kv) = exp (k - 1) := by
      rw [Units.val_mul, map_mul, hk, ϖu, Units.val_mk0, valued_ϖ, ← exp_add]; ring_nf
    rw [mem_sq_sup_U0_iff, mem_sq_sup_U0_iff, hbϖ, hk]
    simp only [exp_inj]
    rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hA : ∃ i : ℤ, k = 2 * i := ⟨j, by omega⟩
      have hB : ¬ ∃ i : ℤ, k - 1 = 2 * i := by rintro ⟨i, hi⟩; omega
      simp [hA, hB]
    · have hA : ¬ ∃ i : ℤ, k = 2 * i := by rintro ⟨i, hi⟩; omega
      have hB : ∃ i : ℤ, k - 1 = 2 * i := ⟨j, by omega⟩
      simp [hA, hB]
  have hsub : Sq.subgroupOf (U0 v) = (powMonoidHom 2 : U0 v →* U0 v).range := by
    ext y
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨z, hz⟩
      have hzv : Valued.v ((z : Kvˣ) : Kv) = 1 := by
        have hy := (mem_U0 v).mp y.2
        rw [← hz] at hy
        simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, map_pow] at hy
        exact eq_one_of_pow_eq_one two_ne_zero hy
      exact ⟨⟨z, (mem_U0 v).mpr hzv⟩, Subtype.ext (by simpa using hz)⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
  have h1 := Subgroup.relIndex_mul_index (le_sup_left : Sq ≤ H)
  rw [Subgroup.relIndex_sup_left, Subgroup.relIndex, hsub, index_sq_U0, hH] at h1
  rw [← h1]; ring

end QuadFormsKB.HN

end
