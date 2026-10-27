/-
# Local densities over a number field: the bridge $\mathcal O_F \leftrightarrow \mathfrak o_\mathfrak p$

**Layer:** bridge (number field $F$ ↔ DVR at $R = \mathfrak o_\mathfrak p$ = `v.adicCompletionIntegers F`).
This is the number-field analogue of `Padic.lean` (the $\mathbb Z \leftrightarrow \mathbb Z_p$ bridge).

**Instances.** $\mathfrak o_\mathfrak p$ satisfies every typeclass hypothesis of the DVR theory: `IsDomain`,
`IsDiscreteValuationRing` (Mathlib), finite residue field (`HN`), `Fintype`/`DecidableEq` on the residue
field, `IsFractionRing 𝔬_𝔭 F_𝔭` (Mathlib), and **`IsAdicComplete (maximalIdeal 𝔬_𝔭) 𝔬_𝔭`**
(`isAdicComplete`, proved here: Mathlib v4.35 lacks it).

**Proves** $\mathcal O_F/\mathfrak p^k \cong \mathfrak o_\mathfrak p/\varpi^k$ (`quotEquiv`), $q(\mathfrak o_\mathfrak p) = N\mathfrak p$
(`q_completion`), and that counts and Zero/Good-type counts mod $\mathfrak p^k$ over $\mathcal O_F$ equal those
mod $\varpi^k$ over $\mathfrak o_\mathfrak p$ (`repCount_eq_completion`, `repCountZero_eq_completion`,
`repCountGood_eq_completion`; Hanke 2004, §2, p. 356). The uniformizer is a *global* integer
$\varpi = $ `unif v` $\in \mathfrak p \setminus \mathfrak p^2$, so that $\varpi^{2\nu} m$ stays in $\mathcal O_F$.

The local density $\beta_\mathfrak p(Q, m)$ over $\mathcal O_F$ and the corollaries over $F$ are in
`NFLocal.lean`.
-/
import QuadFormsKB.LocalDensity.DVRLowerBounds
import QuadFormsKB.LocalDensity.Bridge
import QuadFormsKB.Literature.HasseNorm.SquareClasses

open NumberField IsDedekindDomain WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.LocalDensity.NF

open QuadForm

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-! ### Instances on $\mathfrak o_\mathfrak p$ -/

/-- The residue field of $\mathfrak o_\mathfrak p$ is a `Fintype` (it has $N\mathfrak p$ elements). -/
instance fintypeResidueField : Fintype (IsLocalRing.ResidueField 𝔬) := Fintype.ofFinite _

/-- Decidable equality on the residue field of $\mathfrak o_\mathfrak p$ (classical). -/
instance decidableEqResidueField : DecidableEq (IsLocalRing.ResidueField 𝔬) := Classical.decEq _

/-- The values $v(x - y)$ for $x, y \in \mathfrak o_\mathfrak p$ congruent mod $\mathfrak m^n$: congruence mod
$\mathfrak m^n$ means $v(x - y) \le \exp(-n)$. -/
theorem sModEq_iff_valued (k : ℕ) (a b : 𝔬) :
    a ≡ b [SMOD ((IsLocalRing.maximalIdeal 𝔬) ^ k • ⊤ : Submodule 𝔬 𝔬)] ↔
      Valued.v ((a : Fv) - (b : Fv)) ≤ exp (-(k : ℤ)) := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, (HN.irreducible_ϖO v).maximalIdeal_eq,
    Ideal.span_singleton_pow, HN.mem_span_ϖ_pow]
  rfl

/-- **$\mathfrak o_\mathfrak p$ is $\mathfrak m$-adically complete** (not in Mathlib v4.35). *Proof:* a sequence
that is Cauchy for the $\mathfrak m$-adic filtration is Cauchy in the complete field $F_\mathfrak p$; its limit
$L$ satisfies $v(f_n - L) \le \exp(-n)$ (ultrametric inequality), so $v(L) \le 1$ and $L \in \mathfrak o_\mathfrak p$.
Hausdorffness is Krull's intersection theorem (Mathlib, for Noetherian local rings). -/
@[kb "serre1973" "Ch. II §1 [unverified]"]
instance isAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal 𝔬) 𝔬 where
  prec' {f} hf := by
    set u : ℕ → Fv := fun k => (f k : Fv)
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
      set k := log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
      refine ⟨u '' Set.Ici (1 - k).toNat, Filter.image_mem_map (Filter.Ici_mem_atTop _), ?_⟩
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [Valuation.restrict_lt_iff_lt_embedding, ← exp_log hγ]
      refine lt_of_le_of_lt (hd' _ a b ha hb) ?_
      rw [exp_lt_exp]
      have := Int.self_le_toNat (1 - k)
      omega
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hlim : ∀ N : ℕ, Valued.v (u N - L) ≤ exp (-(N : ℤ)) := by
      intro N
      have hne : Valued.v.restrict (HN.ϖ v ^ (N + 1)) ≠ 0 := by
        rw [ne_eq, map_eq_zero]; exact pow_ne_zero _ (HN.ϖ_ne_zero v)
      have hball : {y : Fv | Valued.v.restrict (y - L) < (Units.mk0 _ hne).1} ∈ nhds L :=
        Valued.mem_nhds.mpr ⟨Units.mk0 _ hne, subset_rfl⟩
      obtain ⟨j, hj1, hj2⟩ := ((hL.eventually hball).and (Filter.eventually_ge_atTop N)).exists
      simp only [Units.val_mk0, Valuation.restrict_lt_iff, HN.valued_ϖ_pow] at hj1
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

/-! ### The embedding $\mathcal O_F \to \mathfrak o_\mathfrak p$ and a global uniformizer -/

/-- The embedding $\iota : \mathcal O_F \to \mathfrak o_\mathfrak p$ (`algebraMap`). -/
abbrev ι : 𝓞 F →+* 𝔬 := algebraMap (𝓞 F) 𝔬

/-- $v(\iota(x)) = v_\mathfrak p(x)$ for $x \in \mathcal O_F$. -/
theorem valued_ι (x : 𝓞 F) : Valued.v ((ι v x : 𝔬) : Fv) = v.intValuation x :=
  HN.valued_algebraMap_int v x

/-- $\iota : \mathcal O_F \to \mathfrak o_\mathfrak p$ is injective. -/
theorem ι_injective : Function.Injective (ι v) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h0
  have h := valued_ι v a
  rw [ha, ZeroMemClass.coe_zero, map_zero, v.intValuation_if_neg h0] at h
  exact exp_ne_zero h.symm

/-- **A global uniformizer** $\varpi \in \mathcal O_F$ at $\mathfrak p$: $v_\mathfrak p(\varpi) = 1$, i.e.
$\varpi \in \mathfrak p \setminus \mathfrak p^2$ (`intValuation_exists_uniformizer`). -/
def unif : 𝓞 F := v.intValuation_exists_uniformizer.choose

theorem intValuation_unif : v.intValuation (unif v) = exp (-1 : ℤ) :=
  v.intValuation_exists_uniformizer.choose_spec

/-- The global uniformizer as an element of $\mathfrak o_\mathfrak p$. -/
abbrev π : 𝔬 := ι v (unif v)

theorem valued_π : Valued.v ((π v : 𝔬) : Fv) = exp (-1 : ℤ) := by
  rw [valued_ι, intValuation_unif]

/-- An element of $\mathfrak o_\mathfrak p$ of valuation $\exp(-1)$ is irreducible (a uniformizer). -/
theorem irreducible_of_valued {z : 𝔬} (hv : Valued.v (z : Fv) = exp (-1 : ℤ)) : Irreducible z := by
  refine ⟨?_, ?_⟩
  · rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one, hv]
    rw [← exp_zero, exp_inj]; omega
  · intro a b hab
    by_contra hc
    push Not at hc
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hc
    have ha : Valued.v (a : Fv) ≤ exp (-1 : ℤ) := HN.valued_le_exp_neg_one v (lt_of_le_of_ne a.2 hc.1)
    have hb : Valued.v (b : Fv) ≤ exp (-1 : ℤ) := HN.valued_le_exp_neg_one v (lt_of_le_of_ne b.2 hc.2)
    have : Valued.v (z : Fv) = Valued.v (a : Fv) * Valued.v (b : Fv) := by
      rw [hab]; exact map_mul _ _ _
    rw [hv] at this
    have h2 : Valued.v (a : Fv) * Valued.v (b : Fv) ≤ exp (-1 : ℤ) * exp (-1 : ℤ) := mul_le_mul' ha hb
    rw [← this, ← exp_add, exp_le_exp] at h2
    omega

/-- $\varpi$ is irreducible in $\mathfrak o_\mathfrak p$. -/
theorem irreducible_π : Irreducible (π v) := irreducible_of_valued v (valued_π v)

/-- $(\varpi^k) = (\varpi_{\mathrm{HN}}^k) = \mathfrak m^k$ in $\mathfrak o_\mathfrak p$. -/
theorem span_π_pow (k : ℕ) : Ideal.span {π v ^ k} = Ideal.span {HN.ϖO v ^ k} := by
  rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, ← (irreducible_π v).maximalIdeal_eq,
    ← (HN.irreducible_ϖO v).maximalIdeal_eq]

/-- $z \in \varpi^k \mathfrak o_\mathfrak p \iff v(z) \le \exp(-k)$. -/
theorem mem_span_π_pow (k : ℕ) (z : 𝔬) :
    z ∈ Ideal.span {π v ^ k} ↔ Valued.v (z : Fv) ≤ exp (-(k : ℤ)) := by
  rw [span_π_pow, HN.mem_span_ϖ_pow]

/-- For $a \in \mathcal O_F$: $\iota(a) \in \varpi^k \mathfrak o_\mathfrak p \iff a \in \mathfrak p^k$. -/
theorem ι_mem_span_π_pow (k : ℕ) (a : 𝓞 F) : ι v a ∈ Ideal.span {π v ^ k} ↔ a ∈ v.asIdeal ^ k := by
  rw [mem_span_π_pow, valued_ι, v.intValuation_le_pow_iff_mem]

/-- For $a \in \mathcal O_F$: $\varpi^k \mid \iota(a)$ in $\mathfrak o_\mathfrak p \iff a \in \mathfrak p^k$. -/
theorem π_pow_dvd_ι_iff (k : ℕ) (a : 𝓞 F) : π v ^ k ∣ ι v a ↔ a ∈ v.asIdeal ^ k := by
  rw [← Ideal.mem_span_singleton, ι_mem_span_π_pow]

/-- $|\mathfrak o_\mathfrak p/\varpi^k| = (N\mathfrak p)^k$. -/
theorem card_quot_π_pow (k : ℕ) :
    Nat.card (𝔬 ⧸ Ideal.span {π v ^ k}) = Ideal.absNorm v.asIdeal ^ k := by
  rw [span_π_pow, HN.card_quot_ϖ_pow]

/-! ### $\mathcal O_F/\mathfrak p^k \cong \mathfrak o_\mathfrak p/\varpi^k$ -/

/-- The reduction $\mathcal O_F \to \mathfrak o_\mathfrak p/\varpi^k$. -/
abbrev redHom (k : ℕ) : 𝓞 F →+* 𝔬 ⧸ Ideal.span {π v ^ k} := (Ideal.Quotient.mk _).comp (ι v)

theorem ker_redHom (k : ℕ) : RingHom.ker (redHom v k) = v.asIdeal ^ k := by
  ext a
  rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ι_mem_span_π_pow]

theorem redHom_surjective (k : ℕ) : Function.Surjective (redHom v k) := by
  have hN : Ideal.absNorm v.asIdeal ≠ 0 :=
    (Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr (mem_nonZeroDivisors_of_ne_zero v.ne_bot)
  have : Finite (𝔬 ⧸ Ideal.span {π v ^ k}) :=
    Nat.finite_of_card_ne_zero (by rw [card_quot_π_pow]; exact pow_ne_zero _ hN)
  have hc : Nat.card (𝔬 ⧸ Ideal.span {π v ^ k}) ≤ Nat.card (𝓞 F ⧸ RingHom.ker (redHom v k)) := by
    rw [card_quot_π_pow, ker_redHom, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_pow]
  have hb := (RingHom.kerLift_injective (redHom v k)).bijective_of_nat_card_le hc
  intro y
  obtain ⟨q, hq⟩ := hb.2 y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨x, hq⟩

/-- **$\mathcal O_F/\mathfrak p^k \cong \mathfrak o_\mathfrak p/\varpi^k$** as rings, $a \bmod \mathfrak p^k \mapsto \iota(a) \bmod
\varpi^k$ (kernel $\mathfrak p^k$ by valuations; surjective since both sides have $(N\mathfrak p)^k$ elements).
Valid for all $k \ge 0$. -/
@[kb "neukirch1999" "Ch. II §4 [unverified]"]
def quotEquiv (k : ℕ) : 𝓞 F ⧸ v.asIdeal ^ k ≃+* 𝔬 ⧸ Ideal.span {π v ^ k} :=
  (Ideal.quotEquivOfEq (ker_redHom v k).symm).trans
    (RingHom.quotientKerEquivOfSurjective (redHom_surjective v k))

@[simp] theorem quotEquiv_mk (k : ℕ) (a : 𝓞 F) :
    quotEquiv v k (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (ι v a) := rfl

/-! ### Transfer of counts -/

/-- **$r_{\mathfrak p^k}(m)$ over $\mathcal O_F$:** the number of $\vec x \in (\mathcal O_F/\mathfrak p^k)^n$ with
$Q(\vec x) \equiv m \pmod{\mathfrak p^k}$ (Hanke 2004, pp. 356–357, $r_{\mathfrak p^k,Q}(m)$). -/
@[kb "hanke2004" "§2, pp. 356–357"]
def repCount (Q : QuadForm (𝓞 F) n) (k : ℕ) (m : 𝓞 F) : ℕ :=
  Nat.card {x : Fin n → 𝓞 F ⧸ v.asIdeal ^ k //
    Q.evalIn (𝓞 F ⧸ v.asIdeal ^ k) x = Ideal.Quotient.mk _ m}

/-- **Zero type over $\mathcal O_F$** (Hanke 2004, Def. 3.1): every $x_i \in \mathfrak p/\mathfrak p^k$. -/
def IsZeroType (k : ℕ) (x : Fin n → 𝓞 F ⧸ v.asIdeal ^ k) : Prop :=
  ∀ i, x i ∈ v.asIdeal.map (Ideal.Quotient.mk (v.asIdeal ^ k))

/-- **Good type over $\mathcal O_F$** (Hanke 2004, Def. 3.1), relative to the unimodular coordinates $S_0$ of
a local Jordan splitting: not Zero type, and $x_i \notin \mathfrak p/\mathfrak p^k$ for some $i \in S_0$. -/
def IsGoodType (S₀ : Finset (Fin n)) (k : ℕ) (x : Fin n → 𝓞 F ⧸ v.asIdeal ^ k) : Prop :=
  ¬ IsZeroType v k x ∧ ∃ i ∈ S₀, x i ∉ v.asIdeal.map (Ideal.Quotient.mk (v.asIdeal ^ k))

/-- **Solutions of a given type** mod $\mathfrak p^k$ over $\mathcal O_F$. -/
def repCountOf (Q : QuadForm (𝓞 F) n) (k : ℕ) (m : 𝓞 F)
    (T : (Fin n → 𝓞 F ⧸ v.asIdeal ^ k) → Prop) : ℕ :=
  Nat.card {x : Fin n → 𝓞 F ⧸ v.asIdeal ^ k //
    Q.evalIn (𝓞 F ⧸ v.asIdeal ^ k) x = Ideal.Quotient.mk _ m ∧ T x}

/-- The base change $Q \otimes \mathfrak o_\mathfrak p$ of a form over $\mathcal O_F$. -/
abbrev Qp (Q : QuadForm (𝓞 F) n) : QuadForm 𝔬 n := Q.map (ι v)

/-- Evaluation commutes with the isomorphism `quotEquiv`. -/
theorem quotEquiv_evalIn (Q : QuadForm (𝓞 F) n) (k : ℕ) (x : Fin n → 𝓞 F ⧸ v.asIdeal ^ k) :
    quotEquiv v k (Q.evalIn _ x) = (Qp v Q).evalIn _ (fun i => quotEquiv v k (x i)) := by
  simp only [QuadForm.evalIn, map_sum, apply_ite (quotEquiv v k), map_mul, map_zero, QuadForm.map,
    Matrix.map_apply, Ideal.Quotient.algebraMap_eq, quotEquiv_mk]

/-- $\mathfrak p/\mathfrak p^k$ corresponds to $(\varpi)/(\varpi^k)$: $y \in \mathfrak p/\mathfrak p^k \iff \varpi \mid e(y)$. -/
theorem mem_map_iff_dvd (k : ℕ) (y : 𝓞 F ⧸ v.asIdeal ^ k) :
    y ∈ v.asIdeal.map (Ideal.Quotient.mk (v.asIdeal ^ k)) ↔
      Ideal.Quotient.mk (Ideal.span {π v ^ k}) (π v) ∣ quotEquiv v k y := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h1 : Subsingleton (𝓞 F ⧸ v.asIdeal ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
    have h2 : Subsingleton (𝔬 ⧸ Ideal.span {π v ^ 0}) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.span_singleton_one])
    exact iff_of_true (by rw [Subsingleton.elim (Ideal.Quotient.mk _ a) 0]; exact zero_mem _)
      (by rw [Subsingleton.elim (quotEquiv v 0 _) 0]; exact dvd_zero _)
  rw [Ideal.mem_quotient_iff_mem (Ideal.pow_le_self hk.ne'), quotEquiv_mk]
  rw [← pow_one v.asIdeal, ← π_pow_dvd_ι_iff, pow_one]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨Ideal.Quotient.mk _ c, by rw [hc, map_mul]⟩
  · rintro ⟨c, hc⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
    have : π v ∣ ι v a - π v * c := (dvd_pow_self _ hk.ne').trans hc
    have h2 : π v ∣ ι v a - π v * c + π v * c := dvd_add this (dvd_mul_right _ _)
    rwa [sub_add_cancel] at h2

/-- The coordinatewise isomorphism $(\mathcal O_F/\mathfrak p^k)^n \cong (\mathfrak o_\mathfrak p/\varpi^k)^n$. -/
abbrev vecEquiv (k : ℕ) : (Fin n → 𝓞 F ⧸ v.asIdeal ^ k) ≃ (Fin n → 𝔬 ⧸ Ideal.span {π v ^ k}) :=
  Equiv.piCongrRight fun _ => (quotEquiv v k).toEquiv

theorem evalIn_iff (Q : QuadForm (𝓞 F) n) (k : ℕ) (m : 𝓞 F) (x : Fin n → 𝓞 F ⧸ v.asIdeal ^ k) :
    Q.evalIn _ x = Ideal.Quotient.mk _ m ↔
      (Qp v Q).evalIn _ (vecEquiv v k x) = Ideal.Quotient.mk _ (ι v m) := by
  rw [← (quotEquiv v k).injective.eq_iff, quotEquiv_evalIn, quotEquiv_mk]
  rfl

theorem isZeroType_iff (k : ℕ) (x : Fin n → 𝓞 F ⧸ v.asIdeal ^ k) :
    IsZeroType v k x ↔ DVR.IsZeroType (π v) k (vecEquiv v k x) := by
  simp only [IsZeroType, DVR.IsZeroType, mem_map_iff_dvd]
  rfl

theorem isGoodType_iff (S₀ : Finset (Fin n)) (k : ℕ) (x : Fin n → 𝓞 F ⧸ v.asIdeal ^ k) :
    IsGoodType v S₀ k x ↔ DVR.IsGoodType S₀ (π v) k (vecEquiv v k x) := by
  simp only [IsGoodType, DVR.IsGoodType, isZeroType_iff, mem_map_iff_dvd]
  rfl

/-- **Counts over $\mathcal O_F/\mathfrak p^k$ equal counts over $\mathfrak o_\mathfrak p/\varpi^k$** (Hanke 2004,
§2, p. 356): $r_{\mathfrak p^k}(Q, m) = r_{\varpi^k}(Q \otimes \mathfrak o_\mathfrak p, m)$. -/
@[kb "hanke2004" "§2, p. 356"]
theorem repCount_eq_completion (Q : QuadForm (𝓞 F) n) (k : ℕ) (m : 𝓞 F) :
    repCount v Q k m = DVR.repCount (Qp v Q) (π v) k (ι v m) :=
  Nat.card_congr ((vecEquiv v k).subtypeEquiv (evalIn_iff v Q k m))

/-- **Typed counts transfer** for any type predicates $T$ over $\mathcal O_F/\mathfrak p^k$ and $T'$ over
$\mathfrak o_\mathfrak p/\varpi^k$ that correspond under `vecEquiv`. -/
theorem repCountOf_eq_completion (Q : QuadForm (𝓞 F) n) (k : ℕ) (m : 𝓞 F)
    (T : (Fin n → 𝓞 F ⧸ v.asIdeal ^ k) → Prop) (T' : (Fin n → 𝔬 ⧸ Ideal.span {π v ^ k}) → Prop)
    (hT : ∀ x, T x ↔ T' (vecEquiv v k x)) :
    repCountOf v Q k m T = DVR.repCountOf (Qp v Q) (π v) k (ι v m) T' :=
  Nat.card_congr ((vecEquiv v k).subtypeEquiv fun x => and_congr (evalIn_iff v Q k m x) (hT x))

/-- Zero-type counts transfer to $\mathfrak o_\mathfrak p$. -/
theorem repCountZero_eq_completion (Q : QuadForm (𝓞 F) n) (k : ℕ) (m : 𝓞 F) :
    repCountOf v Q k m (IsZeroType v k) =
      DVR.repCountOf (Qp v Q) (π v) k (ι v m) (DVR.IsZeroType (π v) k) :=
  repCountOf_eq_completion v Q k m _ _ (isZeroType_iff v k)

/-- Non-Zero-type (Good $\cup$ Bad) counts transfer to $\mathfrak o_\mathfrak p$. -/
theorem repCountNonZero_eq_completion (Q : QuadForm (𝓞 F) n) (k : ℕ) (m : 𝓞 F) :
    repCountOf v Q k m (fun x => ¬ IsZeroType v k x) =
      DVR.repCountOf (Qp v Q) (π v) k (ι v m) (fun x => ¬ DVR.IsZeroType (π v) k x) :=
  repCountOf_eq_completion v Q k m _ _ fun x => not_congr (isZeroType_iff v k x)

/-- Good-type counts transfer to $\mathfrak o_\mathfrak p$. -/
@[kb "hanke2004" "§2, p. 356; Def. 3.1, p. 358"]
theorem repCountGood_eq_completion (Q : QuadForm (𝓞 F) n) (S₀ : Finset (Fin n)) (k : ℕ) (m : 𝓞 F) :
    repCountOf v Q k m (IsGoodType v S₀ k) =
      DVR.repCountOf (Qp v Q) (π v) k (ι v m) (DVR.IsGoodType S₀ (π v) k) :=
  repCountOf_eq_completion v Q k m _ _ (isGoodType_iff v S₀ k)

/-- **$q(\mathfrak o_\mathfrak p) = N\mathfrak p$**: the residue field of the completion has $N\mathfrak p$ elements. -/
@[kb "neukirch1999" "Ch. II §4 [unverified]"]
theorem q_completion : DVR.q 𝔬 = Ideal.absNorm v.asIdeal := HN.card_residueField v

/-- Nondegeneracy is preserved by base change to $\mathfrak o_\mathfrak p$ (as $\iota$ is injective). -/
theorem nondegenerate_Qp {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) : (Qp v Q).Nondegenerate := by
  have h : (Qp v Q).hessian = Q.hessian.map (ι v) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [QuadForm.Nondegenerate, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact fun h0 => hQ ((injective_iff_map_eq_zero _).mp (ι_injective v) _ h0)

/-- $2 \ne 0$ in $\mathfrak o_\mathfrak p$. -/
theorem two_ne_zero' : (2 : 𝔬) ≠ 0 := by
  intro h
  have : ((2 : 𝔬) : Fv) = 0 := by rw [h]; rfl
  exact two_ne_zero (by simp at this)

/-- $\iota(m) \ne 0$ for $m \ne 0$. -/
theorem ι_ne_zero {m : 𝓞 F} (hm : m ≠ 0) : ι v m ≠ 0 :=
  fun h => hm ((injective_iff_map_eq_zero _).mp (ι_injective v) _ h)

/-- $\varpi^e \mid 2$ in $\mathfrak o_\mathfrak p$ iff $2 \in \mathfrak p^e$. -/
theorem π_pow_dvd_two_iff (e : ℕ) : π v ^ e ∣ 2 ↔ (2 : 𝓞 F) ∈ v.asIdeal ^ e := by
  rw [← π_pow_dvd_ι_iff, map_ofNat]

example : IsDomain 𝔬 := inferInstance
example : IsDiscreteValuationRing 𝔬 := inferInstance
example : Finite (IsLocalRing.ResidueField 𝔬) := inferInstance
example : IsFractionRing 𝔬 Fv := inferInstance

end QuadFormsKB.LocalDensity.NF
