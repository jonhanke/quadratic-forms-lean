/-
# Local densities over $\mathbb F_q(t)$: the bridge $k[X] \leftrightarrow \mathfrak o_v$ (function field case)

**Layer:** bridge (function field $F = k(t)$, `RatFunc k`, $k$ finite; finite place $v$ of $k[X]$ $\leftrightarrow$
discrete valuation ring $R = \mathfrak o_v$ = `v.adicCompletionIntegers (RatFunc k)`). This is the function field port of
`NFBridge.lean` (the number field bridge $\mathcal O_F \leftrightarrow \mathfrak o_\mathfrak p$), with $\mathcal O_F$ replaced by
the polynomial ring $k[X]$.

**Instances.** $\mathfrak o_v$ satisfies every typeclass hypothesis of the abstract discrete valuation ring theory
(`QuadFormsKB/LocalDensity/DVR*.lean`): `IsDomain`, `IsDiscreteValuationRing` (Mathlib), finite residue field,
`Fintype`/`DecidableEq` on the residue field, `IsFractionRing`, and **`IsAdicComplete`** (`isAdicComplete`,
proved here exactly as for number fields).

**Proves** $k[X]/P^j \cong \mathfrak o_v/\varpi^j$ (`quotEquiv`), $q(\mathfrak o_v) = Nv$ with $Nv = |k[X]/P| = q^{\deg P}$
(`q_completion`), and that counts and Zero/Good-type counts mod $P^j$ over $k[X]$ equal those mod $\varpi^j$ over
$\mathfrak o_v$ (`repCount_eq_completion`, `repCountZero_eq_completion`, `repCountGood_eq_completion`;
Hanke 2004, §2, p. 356, function field case). The uniformizer is a *global* polynomial
$\varpi = $ `unif v` $\in P \setminus P^2$, so that $\varpi^{2\nu} m$ stays in $k[X]$.

Differences from `NFBridge.lean`: the norm $N\mathfrak p$ (`Ideal.absNorm`, defined only for rings of integers of
number fields) is replaced by `Nm v` $=$ `Nat.card (k[X] ⧸ v.asIdeal)`; and the helpers `HN.ϖ`, `HN.ϖO`, `HN.mem_span_ϖ_pow`,
`HN.card_residueField`, `HN.valued_algebraMap_int`, `HN.valued_le_exp_neg_one` (stated for `𝓞 K`) are re-proved here
for `k[X]`, using the global uniformizer `π v` directly instead of a uniformizer of $K_v$.
Hypothesis: $k$ is finite (`[Finite k]`); when $2 \ne 0$ is needed (`two_ne_zero'`) we assume `ringChar k ≠ 2`.

The local density $\beta_v(Q, m)$ over $k[X]$ and the corollaries are in `FFDensityLocal.lean`. Indices are 0-based.
-/
import QuadFormsKB.LocalDensity.DVRLowerBounds
import QuadFormsKB.LocalDensity.Bridge
import QuadFormsKB.FunctionField.RatFuncLocal
import QuadFormsKB.FunctionField.DedekindLocal

open IsDedekindDomain WithZero Polynomial

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.LocalDensity.FF

open QuadForm

variable {k : Type} [Field k] [Finite k] (v : HeightOneSpectrum k[X]) {n : ℕ}

local notation "Fv" => v.adicCompletion (RatFunc k)
local notation "𝔬" => v.adicCompletionIntegers (RatFunc k)

/-! ### The residue count and basic valuation facts -/

/-- **The residue count $Nv = |k[X]/P| = q^{\deg P}$** of the finite place $v = (P)$ of $k[X]$ (replaces
$N\mathfrak p$ = `Ideal.absNorm` of the number field case). -/
def Nm : ℕ := Nat.card (k[X] ⧸ v.asIdeal)

/-- $k[X]/P$ is finite (`QuadFormsKB.RatFuncPlace.finite_quotient`). -/
instance finite_quot : Finite (k[X] ⧸ v.asIdeal) := QuadFormsKB.RatFuncPlace.finite_quotient v

theorem Nm_pos : 0 < Nm v := Nat.card_pos

theorem Nm_ne_zero : Nm v ≠ 0 := (Nm_pos v).ne'

/-- $|k[X]/P^j| = (Nv)^j$. -/
theorem card_quot_pow_poly (j : ℕ) : Nat.card (k[X] ⧸ v.asIdeal ^ j) = Nm v ^ j := by
  rw [← Submodule.cardQuot_apply, _root_.cardQuot_pow_of_prime v.ne_bot, Submodule.cardQuot_apply]
  rfl

/-- The valuation of a polynomial in $\mathfrak o_v$ (as an element of $F_v$): $v(f)$ = `intValuation`. -/
theorem valued_algebraMap_poly (x : k[X]) :
    Valued.v ((algebraMap k[X] 𝔬 x : 𝔬) : Fv) = v.intValuation x := by
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

/-- Nonzero values of the valuation of $F_v$ are powers of $\exp(1)$. -/
theorem exists_exp_eq {x : Fv} (hx : x ≠ 0) : ∃ j : ℤ, Valued.v x = exp j := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp h0
  exact ⟨Multiplicative.toAdd a, by rw [← ha]; rfl⟩

/-- Discreteness: $v(x) < 1 \Rightarrow v(x) \le \exp(-1)$. -/
theorem valued_le_exp_neg_one {x : Fv} (hx : Valued.v x < 1) : Valued.v x ≤ exp (-1 : ℤ) := by
  by_cases h0 : x = 0
  · rw [h0, map_zero]; exact zero_le
  obtain ⟨j, hj⟩ := exists_exp_eq v h0
  rw [hj] at hx ⊢
  rw [← exp_zero, exp_lt_exp] at hx
  rw [exp_le_exp]; omega

/-- The maximal ideal of $\mathfrak o_v$ is $\{v < 1\}$. -/
theorem mem_maximalIdeal_iff (z : 𝔬) :
    z ∈ IsLocalRing.maximalIdeal 𝔬 ↔ Valued.v (z : Fv) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have hz : Valued.v (z : Fv) ≤ 1 := z.2
  constructor
  · intro h; exact lt_of_le_of_ne hz h
  · intro h h1; rw [h1] at h; exact lt_irrefl _ h

/-! ### The embedding $k[X] \to \mathfrak o_v$ and a global uniformizer -/

/-- The embedding $\iota : k[X] \to \mathfrak o_v$ (`algebraMap`). -/
abbrev ι : k[X] →+* 𝔬 := algebraMap k[X] 𝔬

/-- $v(\iota(x)) = v_P(x)$ for $x \in k[X]$. -/
theorem valued_ι (x : k[X]) : Valued.v ((ι v x : 𝔬) : Fv) = v.intValuation x :=
  valued_algebraMap_poly v x

/-- $\iota : k[X] \to \mathfrak o_v$ is injective. -/
theorem ι_injective : Function.Injective (ι v) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h0
  have h := valued_ι v a
  rw [ha, ZeroMemClass.coe_zero, map_zero, v.intValuation_if_neg h0] at h
  exact exp_ne_zero h.symm

/-- **A global uniformizer** $\varpi \in k[X]$ at $v$: $v(\varpi) = \exp(-1)$, i.e. $\varpi \in P \setminus P^2$
(`intValuation_exists_uniformizer`). -/
def unif : k[X] := v.intValuation_exists_uniformizer.choose

theorem intValuation_unif : v.intValuation (unif v) = exp (-1 : ℤ) :=
  v.intValuation_exists_uniformizer.choose_spec

/-- The global uniformizer as an element of $\mathfrak o_v$. -/
abbrev π : 𝔬 := ι v (unif v)

theorem valued_π : Valued.v ((π v : 𝔬) : Fv) = exp (-1 : ℤ) := by
  rw [valued_ι, intValuation_unif]

theorem π_ne_zero : (π v : 𝔬) ≠ 0 := by
  intro h
  have := valued_π v
  rw [h, ZeroMemClass.coe_zero, map_zero] at this
  exact exp_ne_zero this.symm

theorem valued_π_pow (j : ℕ) : Valued.v (((π v : 𝔬) : Fv) ^ j) = exp (-(j : ℤ)) := by
  rw [map_pow, valued_π, ← exp_nsmul]; congr 1; simp

/-- An element of $\mathfrak o_v$ of valuation $\exp(-1)$ is irreducible (a uniformizer). -/
theorem irreducible_of_valued {z : 𝔬} (hv : Valued.v (z : Fv) = exp (-1 : ℤ)) : Irreducible z := by
  refine ⟨?_, ?_⟩
  · rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one, hv]
    rw [← exp_zero, exp_inj]; omega
  · intro a b hab
    by_contra hc
    push Not at hc
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hc
    have ha : Valued.v (a : Fv) ≤ exp (-1 : ℤ) := valued_le_exp_neg_one v (lt_of_le_of_ne a.2 hc.1)
    have hb : Valued.v (b : Fv) ≤ exp (-1 : ℤ) := valued_le_exp_neg_one v (lt_of_le_of_ne b.2 hc.2)
    have : Valued.v (z : Fv) = Valued.v (a : Fv) * Valued.v (b : Fv) := by
      rw [hab]; exact map_mul _ _ _
    rw [hv] at this
    have h2 : Valued.v (a : Fv) * Valued.v (b : Fv) ≤ exp (-1 : ℤ) * exp (-1 : ℤ) := mul_le_mul' ha hb
    rw [← this, ← exp_add, exp_le_exp] at h2
    omega

/-- $\varpi$ is irreducible in $\mathfrak o_v$. -/
theorem irreducible_π : Irreducible (π v) := irreducible_of_valued v (valued_π v)

/-- $z \in \varpi^j \mathfrak o_v \iff v(z) \le \exp(-j)$. -/
theorem mem_span_π_pow (j : ℕ) (z : 𝔬) :
    z ∈ Ideal.span {π v ^ j} ↔ Valued.v (z : Fv) ≤ exp (-(j : ℤ)) := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    have e : (((π v ^ j * c : 𝔬)) : Fv) = ((π v : 𝔬) : Fv) ^ j * (c : Fv) := rfl
    rw [e, map_mul, valued_π_pow]
    have hc : Valued.v (c : Fv) ≤ 1 := c.2
    calc exp (-(j : ℤ)) * Valued.v (c : Fv) ≤ exp (-(j : ℤ)) * 1 := mul_le_mul_right hc _
      _ = _ := mul_one _
  · intro hz
    have hϖn : ((π v : 𝔬) : Fv) ^ j ≠ 0 := pow_ne_zero _ (fun h => π_ne_zero v (Subtype.ext h))
    refine ⟨⟨(z : Fv) / ((π v : 𝔬) : Fv) ^ j, ?_⟩, ?_⟩
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, valued_π_pow, div_le_one₀]
      · exact hz
      · exact exp_pos
    · apply Subtype.ext
      change (z : Fv) = ((π v : 𝔬) : Fv) ^ j * ((z : Fv) / ((π v : 𝔬) : Fv) ^ j)
      field_simp

/-- Congruence mod $\mathfrak m^j$ in $\mathfrak o_v$: $a \equiv b$ iff $v(a - b) \le \exp(-j)$. -/
theorem sModEq_iff_valued (j : ℕ) (a b : 𝔬) :
    a ≡ b [SMOD ((IsLocalRing.maximalIdeal 𝔬) ^ j • ⊤ : Submodule 𝔬 𝔬)] ↔
      Valued.v ((a : Fv) - (b : Fv)) ≤ exp (-(j : ℤ)) := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, (irreducible_π v).maximalIdeal_eq,
    Ideal.span_singleton_pow, mem_span_π_pow]
  rfl

/-- **$\mathfrak o_v$ is $\mathfrak m$-adically complete** (not in Mathlib v4.35). *Proof* (as for number fields):
a sequence that is Cauchy for the $\mathfrak m$-adic filtration is Cauchy in the complete field $F_v$; its limit
$L$ satisfies $v(f_j - L) \le \exp(-j)$ (ultrametric inequality), so $v(L) \le 1$ and $L \in \mathfrak o_v$.
Hausdorffness is Krull's intersection theorem (Mathlib, for Noetherian local rings). -/
@[kb "serre1973" "Ch. II §1 [unverified] (function field case)"]
instance isAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal 𝔬) 𝔬 where
  prec' {f} hf := by
    set u : ℕ → Fv := fun j => (f j : Fv)
    have hd : ∀ a b, a ≤ b → Valued.v (u a - u b) ≤ exp (-(a : ℤ)) := fun a b hab =>
      (sModEq_iff_valued v a (f a) (f b)).mp (hf hab)
    have hd' : ∀ N a b, N ≤ a → N ≤ b → Valued.v (u b - u a) ≤ exp (-(N : ℤ)) := by
      intro N a b ha hb
      have hmono : ∀ c : ℕ, N ≤ c → exp (-(c : ℤ)) ≤ exp (-(N : ℤ)) := fun c hc => by
        rw [exp_le_exp]; omega
      rcases le_total a b with h | h
      · rw [Valuation.map_sub_swap]; exact (hd a b h).trans (hmono a ha)
      · exact (hd b a h).trans (hmono b hb)
    have hc : CauchySeq u := by
      rw [CauchySeq, Valued.cauchy_iff]
      refine ⟨inferInstance, fun γ => ?_⟩
      have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by
        intro h0
        exact γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_inj.mp (by rw [h0, map_zero]))
      set j₀ := log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
      refine ⟨u '' Set.Ici (1 - j₀).toNat, Filter.image_mem_map (Filter.Ici_mem_atTop _), ?_⟩
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [Valuation.restrict_lt_iff_lt_embedding, ← exp_log hγ]
      refine lt_of_le_of_lt (hd' _ a b ha hb) ?_
      rw [exp_lt_exp]
      have := Int.self_le_toNat (1 - j₀)
      omega
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hlim : ∀ N : ℕ, Valued.v (u N - L) ≤ exp (-(N : ℤ)) := by
      intro N
      have hne : Valued.v.restrict (((π v : 𝔬) : Fv) ^ (N + 1)) ≠ 0 := by
        rw [ne_eq, map_eq_zero]
        exact pow_ne_zero _ (fun h => π_ne_zero v (Subtype.ext h))
      have hball : {y : Fv | Valued.v.restrict (y - L) < (Units.mk0 _ hne).1} ∈ nhds L :=
        Valued.mem_nhds.mpr ⟨Units.mk0 _ hne, subset_rfl⟩
      obtain ⟨j, hj1, hj2⟩ := ((hL.eventually hball).and (Filter.eventually_ge_atTop N)).exists
      simp only [Units.val_mk0, Valuation.restrict_lt_iff, valued_π_pow] at hj1
      have h1 : Valued.v (u j - L) ≤ exp (-(N : ℤ)) := by
        refine (le_of_lt hj1).trans ?_
        rw [exp_le_exp]; push_cast; omega
      have h2 : Valued.v (u N - u j) ≤ exp (-(N : ℤ)) := hd N j hj2
      calc Valued.v (u N - L) = Valued.v ((u N - u j) + (u j - L)) := by ring_nf
        _ ≤ max (Valued.v (u N - u j)) (Valued.v (u j - L)) := Valuation.map_add _ _ _
        _ ≤ _ := max_le h2 h1
    have hL1 : Valued.v L ≤ 1 := by
      have h0 := hlim 0
      have hu0 : Valued.v (u 0) ≤ 1 := (f 0).2
      calc Valued.v L = Valued.v (u 0 - (u 0 - L)) := by ring_nf
        _ ≤ max (Valued.v (u 0)) (Valued.v (u 0 - L)) := Valuation.map_sub _ _ _
        _ ≤ 1 := max_le hu0 (by simpa using h0)
    refine ⟨⟨L, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hL1⟩, fun N => ?_⟩
    exact (sModEq_iff_valued v N _ _).mpr (hlim N)

/-- For $a \in k[X]$: $\iota(a) \in \varpi^j \mathfrak o_v \iff a \in P^j$. -/
theorem ι_mem_span_π_pow (j : ℕ) (a : k[X]) : ι v a ∈ Ideal.span {π v ^ j} ↔ a ∈ v.asIdeal ^ j := by
  rw [mem_span_π_pow, valued_ι, v.intValuation_le_pow_iff_mem]

/-- For $a \in k[X]$: $\varpi^j \mid \iota(a) \in \mathfrak o_v \iff a \in P^j$. -/
theorem π_pow_dvd_ι_iff (j : ℕ) (a : k[X]) : π v ^ j ∣ ι v a ↔ a ∈ v.asIdeal ^ j := by
  rw [← Ideal.mem_span_singleton, ι_mem_span_π_pow]

/-! ### The residue field of $\mathfrak o_v$ -/

/-- Elements of $\mathfrak o_v$ are approximated mod $\mathfrak m_v$ by polynomials. -/
theorem exists_poly_approx (z : 𝔬) :
    ∃ x : k[X], Valued.v ((z : Fv) - (algebraMap k[X] 𝔬 x : Fv)) < 1 := by
  obtain ⟨y, hy⟩ : ∃ y : RatFunc k, Valued.v ((z : Fv) - algebraMap (RatFunc k) Fv y) < 1 := by
    have hn : {w : Fv | Valued.v ((z : Fv) - w) < 1} ∈ nhds (z : Fv) := by
      have h0 : {u : Fv | Valued.v u < 1} ∈ nhds (0 : Fv) := Valued.mem_nhds.mpr ⟨1, by simp⟩
      have hcont : Continuous fun w : Fv => (z : Fv) - w := continuous_const.sub continuous_id
      have := hcont.continuousAt (x := (z : Fv)) (by simpa using h0)
      exact this
    obtain ⟨_, h1, ⟨y, rfl⟩⟩ := mem_closure_iff_nhds.mp
      (HeightOneSpectrum.denseRange_algebraMap (RatFunc k) v (z : Fv)) _ hn
    exact ⟨y, h1⟩
  have hz : Valued.v (z : Fv) ≤ 1 := z.2
  have hyv : v.valuation (RatFunc k) y ≤ 1 := by
    rw [← QuadFormsKB.FF.valued_algebraMap]
    have : algebraMap (RatFunc k) Fv y = (z : Fv) - ((z : Fv) - algebraMap (RatFunc k) Fv y) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le hz hy.le)
  obtain ⟨m, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v y hyv
  have := v.isMaximal
  let := Ideal.Quotient.field v.asIdeal
  have hd : Ideal.Quotient.mk v.asIdeal (d : k[X]) ≠ 0 := by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]; exact d.2
  obtain ⟨d', hd'⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk v.asIdeal (d : k[X]))⁻¹
  have hdd : (d : k[X]) * d' - 1 ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hd', mul_inv_cancel₀ hd, map_one, sub_self]
  refine ⟨m * d', ?_⟩
  have hdK : algebraMap k[X] (RatFunc k) (d : k[X]) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))]
    intro h0; apply d.2; rw [h0]; exact zero_mem _
  have hyx : v.valuation (RatFunc k) (y - algebraMap k[X] (RatFunc k) (m * d')) < 1 := by
    have e : y - algebraMap k[X] (RatFunc k) (m * d') =
        -(algebraMap k[X] (RatFunc k) m * algebraMap k[X] (RatFunc k) ((d : k[X]) * d' - 1)) /
          algebraMap k[X] (RatFunc k) (d : k[X]) := by
      rw [eq_div_iff hdK]; simp only [map_mul, map_sub, map_one]; linear_combination hnd
    rw [e, map_div₀, Valuation.map_neg, map_mul, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v d).mpr d.2, div_one]
    calc v.intValuation m * v.intValuation ((d : k[X]) * d' - 1)
        ≤ 1 * v.intValuation ((d : k[X]) * d' - 1) :=
          mul_le_mul_left (v.intValuation_le_one m) _
      _ < 1 := by rw [one_mul]; exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).mpr hdd
  have e2 : ((algebraMap k[X] 𝔬 (m * d') : 𝔬) : Fv) =
      algebraMap (RatFunc k) Fv (algebraMap k[X] (RatFunc k) (m * d')) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    rw [HeightOneSpectrum.algebraMap_adicCompletion k[X]]
    rfl
  rw [e2]
  have : (z : Fv) - algebraMap (RatFunc k) Fv (algebraMap k[X] (RatFunc k) (m * d')) =
      ((z : Fv) - algebraMap (RatFunc k) Fv y) +
        algebraMap (RatFunc k) Fv (y - algebraMap k[X] (RatFunc k) (m * d')) := by
    rw [map_sub]; ring
  rw [this]
  refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hy ?_)
  rw [QuadFormsKB.FF.valued_algebraMap]; exact hyx

/-- **The residue field of $\mathfrak o_v$ has $Nv = |k[X]/P|$ elements.** -/
@[kb "neukirch1999" "Ch. II §4 [unverified] (function field case)"]
theorem card_residueField : Nat.card (IsLocalRing.ResidueField 𝔬) = Nm v := by
  let φ : k[X] →+* IsLocalRing.ResidueField 𝔬 :=
    (IsLocalRing.residue 𝔬).comp (algebraMap k[X] 𝔬)
  have hsurj : Function.Surjective φ := by
    intro r
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨x, hx⟩ := exists_poly_approx v z
    refine ⟨x, ?_⟩
    simp only [φ, RingHom.coe_comp, Function.comp_apply]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff,
      ← Valuation.map_neg]
    simpa using hx
  have hker : RingHom.ker φ = v.asIdeal := by
    ext x
    rw [RingHom.mem_ker]
    simp only [φ, RingHom.coe_comp, Function.comp_apply]
    rw [IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff, valued_algebraMap_poly,
      HeightOneSpectrum.intValuation_lt_one_iff_mem]
  rw [Nm, ← hker]
  exact Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv.symm

/-- The residue field of $\mathfrak o_v$ is finite. -/
instance finiteResidueField : Finite (IsLocalRing.ResidueField 𝔬) :=
  Nat.finite_of_card_ne_zero (by rw [card_residueField]; exact Nm_ne_zero v)

/-- The residue field of $\mathfrak o_v$ is a `Fintype` (it has $Nv$ elements). -/
instance fintypeResidueField : Fintype (IsLocalRing.ResidueField 𝔬) := Fintype.ofFinite _

/-- Decidable equality on the residue field of $\mathfrak o_v$ (classical). -/
instance decidableEqResidueField : DecidableEq (IsLocalRing.ResidueField 𝔬) := Classical.decEq _

/-- $|\mathfrak o_v/\varpi^j| = (Nv)^j$. -/
theorem card_quot_π_pow (j : ℕ) : Nat.card (𝔬 ⧸ Ideal.span {π v ^ j}) = Nm v ^ j := by
  have hspan : Ideal.span {π v ^ j} = (IsLocalRing.maximalIdeal 𝔬) ^ j := by
    rw [← Ideal.span_singleton_pow, (irreducible_π v).maximalIdeal_eq]
  rw [hspan, ← Submodule.cardQuot_apply,
    _root_.cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field 𝔬),
    Submodule.cardQuot_apply, ← card_residueField]
  rfl

/-! ### $k[X]/P^j \cong \mathfrak o_v/\varpi^j$ -/

/-- The reduction $k[X] \to \mathfrak o_v/\varpi^j$. -/
abbrev redHom (j : ℕ) : k[X] →+* 𝔬 ⧸ Ideal.span {π v ^ j} := (Ideal.Quotient.mk _).comp (ι v)

theorem ker_redHom (j : ℕ) : RingHom.ker (redHom v j) = v.asIdeal ^ j := by
  ext a
  rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ι_mem_span_π_pow]

theorem redHom_surjective (j : ℕ) : Function.Surjective (redHom v j) := by
  have : Finite (𝔬 ⧸ Ideal.span {π v ^ j}) :=
    Nat.finite_of_card_ne_zero (by rw [card_quot_π_pow]; exact pow_ne_zero _ (Nm_ne_zero v))
  have hc : Nat.card (𝔬 ⧸ Ideal.span {π v ^ j}) ≤ Nat.card (k[X] ⧸ RingHom.ker (redHom v j)) := by
    rw [card_quot_π_pow, ker_redHom, card_quot_pow_poly]
  have hb := (RingHom.kerLift_injective (redHom v j)).bijective_of_nat_card_le hc
  intro y
  obtain ⟨q, hq⟩ := hb.2 y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨x, hq⟩

/-- **$k[X]/P^j \cong \mathfrak o_v/\varpi^j$** as rings, $a \bmod P^j \mapsto \iota(a) \bmod \varpi^j$ (kernel $P^j$ by
valuations; surjective since both sides have $(Nv)^j$ elements). Valid for all $j \ge 0$. -/
@[kb "neukirch1999" "Ch. II §4 [unverified] (function field case)"]
def quotEquiv (j : ℕ) : k[X] ⧸ v.asIdeal ^ j ≃+* 𝔬 ⧸ Ideal.span {π v ^ j} :=
  (Ideal.quotEquivOfEq (ker_redHom v j).symm).trans
    (RingHom.quotientKerEquivOfSurjective (redHom_surjective v j))

@[simp] theorem quotEquiv_mk (j : ℕ) (a : k[X]) :
    quotEquiv v j (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (ι v a) := rfl

/-! ### Transfer of counts -/

/-- **$r_{P^j}(m)$ over $k[X]$:** the number of $\vec x \in (k[X]/P^j)^n$ with $Q(\vec x) \equiv m \pmod{P^j}$
(Hanke 2004, pp. 356–357, $r_{\mathfrak p^k,Q}(m)$, function field case). -/
@[kb "hanke2004" "§2, pp. 356–357 (function field case)"]
def repCount (Q : QuadForm k[X] n) (j : ℕ) (m : k[X]) : ℕ :=
  Nat.card {x : Fin n → k[X] ⧸ v.asIdeal ^ j //
    Q.evalIn (k[X] ⧸ v.asIdeal ^ j) x = Ideal.Quotient.mk _ m}

/-- **Zero type over $k[X]$** (Hanke 2004, Def. 3.1): every $x_i \in P/P^j$. -/
def IsZeroType (j : ℕ) (x : Fin n → k[X] ⧸ v.asIdeal ^ j) : Prop :=
  ∀ i, x i ∈ v.asIdeal.map (Ideal.Quotient.mk (v.asIdeal ^ j))

/-- **Good type over $k[X]$** (Hanke 2004, Def. 3.1), relative to the unimodular coordinates $S_0$ of a local
Jordan splitting: not Zero type, and $x_i \notin P/P^j$ for some $i \in S_0$. -/
def IsGoodType (S₀ : Finset (Fin n)) (j : ℕ) (x : Fin n → k[X] ⧸ v.asIdeal ^ j) : Prop :=
  ¬ IsZeroType v j x ∧ ∃ i ∈ S₀, x i ∉ v.asIdeal.map (Ideal.Quotient.mk (v.asIdeal ^ j))

/-- **Solutions of a given type** mod $P^j$ over $k[X]$. -/
def repCountOf (Q : QuadForm k[X] n) (j : ℕ) (m : k[X])
    (T : (Fin n → k[X] ⧸ v.asIdeal ^ j) → Prop) : ℕ :=
  Nat.card {x : Fin n → k[X] ⧸ v.asIdeal ^ j //
    Q.evalIn (k[X] ⧸ v.asIdeal ^ j) x = Ideal.Quotient.mk _ m ∧ T x}

/-- The base change $Q \otimes \mathfrak o_v$ of a form over $k[X]$. -/
abbrev Qp (Q : QuadForm k[X] n) : QuadForm 𝔬 n := Q.map (ι v)

/-- Evaluation commutes with the isomorphism `quotEquiv`. -/
theorem quotEquiv_evalIn (Q : QuadForm k[X] n) (j : ℕ) (x : Fin n → k[X] ⧸ v.asIdeal ^ j) :
    quotEquiv v j (Q.evalIn _ x) = (Qp v Q).evalIn _ (fun i => quotEquiv v j (x i)) := by
  simp only [QuadForm.evalIn, map_sum, apply_ite (quotEquiv v j), map_mul, map_zero, QuadForm.map,
    Matrix.map_apply, Ideal.Quotient.algebraMap_eq, quotEquiv_mk]

/-- $P/P^j$ corresponds to $(\varpi)/(\varpi^j)$: $y \in P/P^j \iff \varpi \mid e(y)$. -/
theorem mem_map_iff_dvd (j : ℕ) (y : k[X] ⧸ v.asIdeal ^ j) :
    y ∈ v.asIdeal.map (Ideal.Quotient.mk (v.asIdeal ^ j)) ↔
      Ideal.Quotient.mk (Ideal.span {π v ^ j}) (π v) ∣ quotEquiv v j y := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h1 : Subsingleton (k[X] ⧸ v.asIdeal ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
    have h2 : Subsingleton (𝔬 ⧸ Ideal.span {π v ^ 0}) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.span_singleton_one])
    exact iff_of_true (by rw [Subsingleton.elim (Ideal.Quotient.mk _ a) 0]; exact zero_mem _)
      (by rw [Subsingleton.elim (quotEquiv v 0 _) 0]; exact dvd_zero _)
  rw [Ideal.mem_quotient_iff_mem (Ideal.pow_le_self hj.ne'), quotEquiv_mk]
  rw [← pow_one v.asIdeal, ← π_pow_dvd_ι_iff, pow_one]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨Ideal.Quotient.mk _ c, by rw [hc, map_mul]⟩
  · rintro ⟨c, hc⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
    have : π v ∣ ι v a - π v * c := (dvd_pow_self _ hj.ne').trans hc
    have h2 : π v ∣ ι v a - π v * c + π v * c := dvd_add this (dvd_mul_right _ _)
    rwa [sub_add_cancel] at h2

/-- The coordinatewise isomorphism $(k[X]/P^j)^n \cong (\mathfrak o_v/\varpi^j)^n$. -/
abbrev vecEquiv (j : ℕ) : (Fin n → k[X] ⧸ v.asIdeal ^ j) ≃ (Fin n → 𝔬 ⧸ Ideal.span {π v ^ j}) :=
  Equiv.piCongrRight fun _ => (quotEquiv v j).toEquiv

theorem evalIn_iff (Q : QuadForm k[X] n) (j : ℕ) (m : k[X]) (x : Fin n → k[X] ⧸ v.asIdeal ^ j) :
    Q.evalIn _ x = Ideal.Quotient.mk _ m ↔
      (Qp v Q).evalIn _ (vecEquiv v j x) = Ideal.Quotient.mk _ (ι v m) := by
  rw [← (quotEquiv v j).injective.eq_iff, quotEquiv_evalIn, quotEquiv_mk]
  rfl

theorem isZeroType_iff (j : ℕ) (x : Fin n → k[X] ⧸ v.asIdeal ^ j) :
    IsZeroType v j x ↔ DVR.IsZeroType (π v) j (vecEquiv v j x) := by
  simp only [IsZeroType, DVR.IsZeroType, mem_map_iff_dvd]
  rfl

theorem isGoodType_iff (S₀ : Finset (Fin n)) (j : ℕ) (x : Fin n → k[X] ⧸ v.asIdeal ^ j) :
    IsGoodType v S₀ j x ↔ DVR.IsGoodType S₀ (π v) j (vecEquiv v j x) := by
  simp only [IsGoodType, DVR.IsGoodType, isZeroType_iff, mem_map_iff_dvd]
  rfl

/-- **Counts over $k[X]/P^j$ equal counts over $\mathfrak o_v/\varpi^j$** (Hanke 2004, §2, p. 356, function field
case): $r_{P^j}(Q, m) = r_{\varpi^j}(Q \otimes \mathfrak o_v, m)$. -/
@[kb "hanke2004" "§2, p. 356 (function field case)"]
theorem repCount_eq_completion (Q : QuadForm k[X] n) (j : ℕ) (m : k[X]) :
    repCount v Q j m = DVR.repCount (Qp v Q) (π v) j (ι v m) :=
  Nat.card_congr ((vecEquiv v j).subtypeEquiv (evalIn_iff v Q j m))

/-- **Typed counts transfer** for any type predicates $T$ over $k[X]/P^j$ and $T'$ over $\mathfrak o_v/\varpi^j$
that correspond under `vecEquiv`. -/
theorem repCountOf_eq_completion (Q : QuadForm k[X] n) (j : ℕ) (m : k[X])
    (T : (Fin n → k[X] ⧸ v.asIdeal ^ j) → Prop) (T' : (Fin n → 𝔬 ⧸ Ideal.span {π v ^ j}) → Prop)
    (hT : ∀ x, T x ↔ T' (vecEquiv v j x)) :
    repCountOf v Q j m T = DVR.repCountOf (Qp v Q) (π v) j (ι v m) T' :=
  Nat.card_congr ((vecEquiv v j).subtypeEquiv fun x => and_congr (evalIn_iff v Q j m x) (hT x))

/-- Zero-type counts transfer to $\mathfrak o_v$. -/
theorem repCountZero_eq_completion (Q : QuadForm k[X] n) (j : ℕ) (m : k[X]) :
    repCountOf v Q j m (IsZeroType v j) =
      DVR.repCountOf (Qp v Q) (π v) j (ι v m) (DVR.IsZeroType (π v) j) :=
  repCountOf_eq_completion v Q j m _ _ (isZeroType_iff v j)

/-- Non-Zero-type (Good $\cup$ Bad) counts transfer to $\mathfrak o_v$. -/
theorem repCountNonZero_eq_completion (Q : QuadForm k[X] n) (j : ℕ) (m : k[X]) :
    repCountOf v Q j m (fun x => ¬ IsZeroType v j x) =
      DVR.repCountOf (Qp v Q) (π v) j (ι v m) (fun x => ¬ DVR.IsZeroType (π v) j x) :=
  repCountOf_eq_completion v Q j m _ _ fun x => not_congr (isZeroType_iff v j x)

/-- Good-type counts transfer to $\mathfrak o_v$. -/
@[kb "hanke2004" "§2, p. 356; Def. 3.1, p. 358 (function field case)"]
theorem repCountGood_eq_completion (Q : QuadForm k[X] n) (S₀ : Finset (Fin n)) (j : ℕ) (m : k[X]) :
    repCountOf v Q j m (IsGoodType v S₀ j) =
      DVR.repCountOf (Qp v Q) (π v) j (ι v m) (DVR.IsGoodType S₀ (π v) j) :=
  repCountOf_eq_completion v Q j m _ _ (isGoodType_iff v S₀ j)

/-- **$q(\mathfrak o_v) = Nv$**: the residue field of the completion has $Nv = q^{\deg P}$ elements. -/
@[kb "neukirch1999" "Ch. II §4 [unverified] (function field case)"]
theorem q_completion : DVR.q 𝔬 = Nm v := card_residueField v

/-- Nondegeneracy is preserved by base change to $\mathfrak o_v$ (as $\iota$ is injective). -/
theorem nondegenerate_Qp {Q : QuadForm k[X] n} (hQ : Q.Nondegenerate) : (Qp v Q).Nondegenerate := by
  have h : (Qp v Q).hessian = Q.hessian.map (ι v) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [QuadForm.Nondegenerate, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact fun h0 => hQ ((injective_iff_map_eq_zero _).mp (ι_injective v) _ h0)

/-- $2 \ne 0$ in $\mathfrak o_v$, when $\operatorname{char} k \ne 2$. -/
theorem two_ne_zero' (hk : ringChar k ≠ 2) : (2 : 𝔬) ≠ 0 := by
  intro h
  have h2 : ((2 : 𝔬) : Fv) = 0 := by rw [h]; rfl
  have h3 : algebraMap (RatFunc k) Fv (algebraMap k (RatFunc k) 2) = 0 := by
    rw [map_ofNat, map_ofNat]; exact h2
  have h4 : algebraMap k (RatFunc k) 2 = 0 := (map_eq_zero _).mp h3
  exact QuadFormsKB.RatFuncPlace.two_ne_zero_k hk ((map_eq_zero _).mp h4)

/-- $\iota(m) \ne 0$ for $m \ne 0$. -/
theorem ι_ne_zero {m : k[X]} (hm : m ≠ 0) : ι v m ≠ 0 :=
  fun h => hm ((injective_iff_map_eq_zero _).mp (ι_injective v) _ h)

/-- $\varpi^e \mid 2$ in $\mathfrak o_v$ iff $2 \in P^e$. -/
theorem π_pow_dvd_two_iff (e : ℕ) : π v ^ e ∣ 2 ↔ (2 : k[X]) ∈ v.asIdeal ^ e := by
  rw [← π_pow_dvd_ι_iff, map_ofNat]

example : IsDomain 𝔬 := inferInstance
example : IsDiscreteValuationRing 𝔬 := inferInstance
example : Finite (IsLocalRing.ResidueField 𝔬) := inferInstance
example : IsFractionRing 𝔬 Fv := inferInstance

end QuadFormsKB.LocalDensity.FF
