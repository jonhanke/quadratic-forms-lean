/-
# Conway–Sloane, Ch. 15, §9.7: units and odd-order elements of $\theta(O^+(L_2))$

**Layer.** As in `Section9DyadicPatterns.lean`: $L_2 = \gamma\mathbb Z_2^n$ over $\mathbb Q_2$, Gram matrix
`locGram Q v γ` of $B = 2Q$ (so $G_{kk} = 2Q(b_k)$), $\theta(O^+(L_2))$ = `localSpinorNormGroup`.

**Proves**
* `units_mem_or_neg_of_five_mem`: if $5 \in \theta(O^+(L_2))$ then for every $2$-adic unit $u$, $u$ or $-u$ lies in
  $\theta(O^+(L_2))$ (units mod squares are $\{1,3,5,7\}$ and $3 \equiv -5$, $7 \equiv -1 \pmod 8$).
* `exists_odd_order_of_unimodular`: if $n \ge 3$ is odd and $L_2$ is classically integral and unimodular (the Gram matrix
  $A = \tfrac12G$ of the classical form has unit determinant), then $\theta(O^+(L_2))$ contains an element of
  valuation $\lvert 2\rvert$. (An argument not in the book, used for Conway–Sloane's Cor. 22, $n$ odd.)
  *Proof:* by the $2$-adic Jordan basis (`exists_dyadic_basis`), every $1\times1$ block has $Q(b_k)$ a unit and every
  $2\times2$ block has $B(b_1,b_2)\in 2\mathbb Z_2^\times$ (a column of $A$ with no unit entry would make $\det A$
  a non-unit). Since $n$ is odd there is a $1\times 1$ block $b_i$: $x = b_i$ has $\lvert Q(x)\rvert = 1$. If there
  is a $2\times2$ block, one of $b_1, b_2, b_1+b_2$ has $\lvert Q\rvert = \lvert 2\rvert$; otherwise $n\ge3$ gives three
  orthogonal vectors of unit norm, two of which are congruent mod $4$, and $y = b_i + b_j$ has $Q(y) = 2\cdot$unit.
  Both $x$ and $y$ give integral reflections, and $Q(x)Q(y)\in\theta$ has valuation $\lvert 2\rvert$.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9DyadicPatterns

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

section Units

variable {n : ℕ} {Q : QuadForm ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}
  (hQ : Q.Nondegenerate) (L : Lat ℚ n)

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- **If $5 \in \theta(O^+(L_2))$ then $u$ or $-u$ lies in $\theta(O^+(L_2))$ for every $2$-adic unit $u$**
(`h5` is the hypothesis $5 \in \theta$; `hu` says $\lvert u\rvert = 1$). -/
theorem units_mem_or_neg_of_five_mem (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (h5 : Units.mk0 (5 : Fv) (by norm_num) ∈ localSpinorNormGroup Q hQ v L)
    (u : Fvˣ) (hu : Valued.v (u : Fv) = 1) :
    u ∈ localSpinorNormGroup Q hQ v L ∨ -u ∈ localSpinorNormGroup Q hQ v L := by
  have i5 : InT hQ L (5 : Fv) := ⟨by norm_num, h5⟩
  have hc5 : ((5 : 𝔬) : Fv) = 5 := map_ofNat (algebraMap 𝔬 Fv) 5
  have i5' : InT hQ L (((5 : 𝔬)) : Fv) := by rw [hc5]; exact i5
  have u0 : IsUnit (toO v (u : Fv) hu.le) :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hu
  have hu0 : ((toO v (u : Fv) hu.le : 𝔬) : Fv) = u := rfl
  set w : 𝔬 := toO v (u : Fv) hu.le with hw
  obtain ⟨c, hc, s, hs⟩ := Tamagawa.Indefinite.exists_unit_eq_mul_sq h2 u0
  have hsu : IsUnit s := by
    have : IsUnit ((c : 𝔬) * s ^ 2) := hs ▸ u0
    exact (isUnit_pow_iff two_ne_zero).mp (isUnit_of_mul_isUnit_right this)
  have key : ∀ (a r : 𝔬), IsUnit r → w = a * r ^ 2 → InT hQ L (a : Fv) → InT hQ L (u : Fv) := by
    intro a r hr ha hia
    have hr0 : (r : Fv) ≠ 0 := fun h => hr.ne_zero (by exact_mod_cast h)
    have e := congrArg (fun x : 𝔬 => (x : Fv)) ha
    push_cast at e
    rw [← hu0, e]
    exact (InT.sq_mul_iff hQ L hr0).mpr hia
  have key' : ∀ (a r : 𝔬), IsUnit r → -w = a * r ^ 2 → InT hQ L (a : Fv) → InT hQ L (((-u : Fvˣ)) : Fv) := by
    intro a r hr ha hia
    have hr0 : (r : Fv) ≠ 0 := fun h => hr.ne_zero (by exact_mod_cast h)
    have e := congrArg (fun x : 𝔬 => (x : Fv)) ha
    push_cast at e
    rw [Units.val_neg, ← hu0, e]
    exact (InT.sq_mul_iff hQ L hr0).mpr hia
  have u5 : IsUnit (5 : 𝔬) := by
    have := isUnit_one_add_two_mul h2 (2 : 𝔬)
    convert this using 1; norm_num
  rcases hc with rfl | rfl | rfl | rfl
  · left
    exact InT.mem hQ L (key 1 s hsu (by simpa using hs) (by simpa using InT.one hQ L))
  · right
    obtain ⟨t, ht, ht'⟩ := cong_sq h2 u5 (-1 : 𝔬) (x := -3) (by norm_num)
    refine InT.mem hQ L (key' 5 (t * s) (ht.mul hsu) ?_ i5')
    have : w = 3 * s ^ 2 := by simpa using hs
    rw [this]
    linear_combination (s ^ 2) * ht'
  · left
    exact InT.mem hQ L (key 5 s hsu (by simpa using hs) i5')
  · right
    exact InT.mem hQ L (key' 1 s hsu (by
      have : w = -1 * s ^ 2 := by simpa using hs
      rw [this]; ring) (by simpa using InT.one hQ L))

end Units

section Odd

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ} {Q : QuadForm ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}
  (hQ : Q.Nondegenerate) (L : Lat ℚ n)

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

theorem two_Q_single (γ : GL (Fin n) Fv) (k : Fin n) :
    2 * Q.evalIn Fv (γ.val *ᵥ Pi.single k 1) = locGram Q v γ k k := by
  rw [two_mul_evalIn_locGram]
  simp

theorem two_Q_pair (γ : GL (Fin n) Fv) {k l : Fin n} :
    2 * Q.evalIn Fv (γ.val *ᵥ (Pi.single k 1 + Pi.single l 1)) =
      locGram Q v γ k k + locGram Q v γ l l + 2 * locGram Q v γ k l := by
  rw [two_mul_evalIn_locGram]
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  simp [locGram_symm' (Q := Q) (v := v) γ l k]
  ring

theorem hG_of_ci (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    (hci : ∀ x ∈ loc v L.1, ∀ y ∈ loc v L.1, Valued.v (qbil Q Fv x y) ≤ Valued.v (2 : Fv)) (m l : Fin n) :
    Valued.v (locGram Q v γ m l) ≤ Valued.v (2 : Fv) := by
  have hmemb : ∀ k : Fin n, γ.val *ᵥ (Pi.single k 1 : Fin n → Fv) ∈ loc v L.1 := fun k => by
    rw [hγ, mem_locAct]; exact ⟨_, single_mem_std k (by simp), rfl⟩
  rw [← locGram_apply_eq]
  exact hci _ (hmemb m) _ (hmemb l)

theorem symm_of_ci (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    (hG : ∀ m l, Valued.v (locGram Q v γ m l) ≤ Valued.v (2 : Fv)) {c : Fin n → Fv} (hc : c ∈ std v)
    (hQ2 : Valued.v (2 : Fv) ≤ Valued.v (Q.evalIn Fv (γ.val *ᵥ c))) :
    symm Q Fv (γ.val *ᵥ c) ∈ locStabV Q v L := by
  have h2pos : 0 < Valued.v (2 : Fv) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr two_ne_zero)
  have hx0 : Q.evalIn Fv (γ.val *ᵥ c) ≠ 0 := fun h => by
    rw [h, map_zero] at hQ2
    exact absurd (lt_of_lt_of_le h2pos hQ2) (lt_irrefl _)
  refine symm_mem_of_gram L γ hγ hc hx0 fun m => ?_
  refine le_trans ?_ hQ2
  have hc' := mem_std_iff.mp hc
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  calc Valued.v (locGram Q v γ m l) * Valued.v (c l) ≤ Valued.v (2 : Fv) * 1 :=
        mul_le_mul' (hG m l) (hc' l)
    _ = _ := mul_one _

/-- The conclusion for a pair of root vectors: $x = \gamma c_x$ with $\lvert Q(x)\rvert = 1$ and $y = \gamma c_y$ with
$\lvert Q(y)\rvert = \lvert 2\rvert$ give an element of $\theta$ of valuation $\lvert 2\rvert$. -/
theorem exists_of_xy (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v))
    (hG : ∀ m l, Valued.v (locGram Q v γ m l) ≤ Valued.v (2 : Fv)) {cx cy : Fin n → Fv}
    (hcx : cx ∈ std v) (hcy : cy ∈ std v) (hx : Valued.v (Q.evalIn Fv (γ.val *ᵥ cx)) = 1)
    (hy : Valued.v (Q.evalIn Fv (γ.val *ᵥ cy)) = Valued.v (2 : Fv)) :
    ∃ c : Fvˣ, c ∈ localSpinorNormGroup Q hQ v L ∧ Valued.v (c : Fv) = exp (-1 : ℤ) := by
  have h2v := valued_two_dyadic v h2
  have h2le : Valued.v (2 : Fv) ≤ 1 := by rw [h2v]; exact exp_le_one_iff.mpr (by norm_num)
  have hx0 : Q.evalIn Fv (γ.val *ᵥ cx) ≠ 0 := fun h => by rw [h, map_zero] at hx; exact zero_ne_one hx
  have hy0 : Q.evalIn Fv (γ.val *ᵥ cy) ≠ 0 := fun h => by
    rw [h, map_zero, h2v] at hy; exact exp_ne_zero hy.symm
  have hxs := symm_of_ci L γ hγ hG hcx (by rw [hx]; exact h2le)
  have hys := symm_of_ci L γ hγ hG hcy hy.ge
  obtain ⟨h0, hm⟩ := InT.of_symm_pair hQ L hx0 hy0 hxs hys
  refine ⟨Units.mk0 _ h0, hm, ?_⟩
  rw [Units.val_mk0, map_mul, hx, hy, one_mul, h2v]

theorem vQ_eq {q : Fv} {t : WithZero (Multiplicative ℤ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (h : Valued.v (2 * q) = Valued.v (2 : Fv) * t) : Valued.v q = t := by
  rw [map_mul] at h
  have hne : Valued.v (2 : Fv) ≠ 0 := by
    rw [valued_two_dyadic v h2]; exact exp_ne_zero
  exact mul_left_cancel₀ hne h

/-- **A column of the classical Gram matrix has a unit entry** (the $\mathfrak p$-adic unimodularity): if
$\lvert G_{ml}\rvert \le \lvert 2\rvert$ for all $m, l$ and $\lvert\det G\rvert = \lvert 2\rvert^n$, then for each
$k$ some $m$ has $\lvert G_{mk}\rvert = \lvert 2\rvert$. (Otherwise column $k$ of $A = \frac12G \in M_n(\mathfrak o)$
vanishes in the residue field, so $\det A$ is a non-unit.) -/
theorem col_unit (_h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hG : ∀ m l, Valued.v (locGram Q v γ m l) ≤ Valued.v (2 : Fv))
    (hdet : Valued.v (locGram Q v γ).det = Valued.v (2 : Fv) ^ n) (k : Fin n) :
    ∃ m, Valued.v (locGram Q v γ m k) = Valued.v (2 : Fv) := by
  by_contra hcon
  push Not at hcon
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  have h2pos : 0 < Valued.v (2 : Fv) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr h2ne)
  have hA : ∀ m l, Valued.v (locGram Q v γ m l / 2) ≤ 1 := fun m l => by
    rw [map_div₀]; exact (div_le_one₀ h2pos).mpr (hG m l)
  let A : Matrix (Fin n) (Fin n) 𝔬 := Matrix.of fun m l => toO v _ (hA m l)
  have hAc : ∀ m l, ((A m l : 𝔬) : Fv) = locGram Q v γ m l / 2 := fun _ _ => rfl
  have hAdet : ((A.det : 𝔬) : Fv) = ((2 : Fv)⁻¹) ^ n * (locGram Q v γ).det := by
    have h1 : A.map (algebraMap 𝔬 Fv) = (2 : Fv)⁻¹ • locGram Q v γ := by
      refine Matrix.ext fun m l => ?_
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      exact (hAc m l).trans (div_eq_inv_mul _ _)
    have h3 : algebraMap 𝔬 Fv A.det = (A.map (algebraMap 𝔬 Fv)).det := RingHom.map_det _ _
    show algebraMap 𝔬 Fv A.det = _
    rw [h3, h1, Matrix.det_smul, Fintype.card_fin]
  have hunit : IsUnit A.det := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one, hAdet, map_mul, map_pow, map_inv₀,
      hdet, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ h2pos.ne')]
  have hcol : ∀ m, IsLocalRing.residue 𝔬 (A m k) = 0 := fun m => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hu
    rw [hAc, map_div₀] at this
    exact hcon m ((div_eq_one_iff_eq h2pos.ne').mp this)
  have hz : ((IsLocalRing.residue 𝔬).mapMatrix A).det = 0 :=
    Matrix.det_eq_zero_of_column_eq_zero k fun m => hcol m
  rw [← RingHom.map_det] at hz
  exact (hunit.map (IsLocalRing.residue 𝔬)).ne_zero hz

/-- **The $2$-adic Jordan blocks of a unimodular classically integral lattice**: every $1\times1$ block has
$\lvert G_{kk}\rvert = \lvert 2\rvert$ and every $2\times2$ block has $\lvert G_{e_1e_2}\rvert = \lvert 2\rvert$. -/
theorem dyadic_unimod (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (P : Finset (Fin n × Fin n))
    (hzero : ∀ k l, k ≠ l → (k, l) ∉ P → (l, k) ∉ P → locGram Q v γ k l = 0)
    (hdisj : ∀ e ∈ P, ∀ e' ∈ P, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2)
    (hpair : ∀ e ∈ P, e.1 ≠ e.2 ∧ locGram Q v γ e.1 e.2 ≠ 0 ∧
        Valued.v (locGram Q v γ e.1 e.1) ≤ Valued.v (2 * locGram Q v γ e.1 e.2) ∧
        Valued.v (locGram Q v γ e.2 e.2) ≤ Valued.v (2 * locGram Q v γ e.1 e.2))
    (hG : ∀ m l, Valued.v (locGram Q v γ m l) ≤ Valued.v (2 : Fv))
    (hdet : Valued.v (locGram Q v γ).det = Valued.v (2 : Fv) ^ n) :
    (∀ k, ¬ LocalDensity.IsPaired P k → Valued.v (locGram Q v γ k k) = Valued.v (2 : Fv)) ∧
    (∀ e ∈ P, Valued.v (locGram Q v γ e.1 e.2) = Valued.v (2 : Fv)) := by
  have h2v := valued_two_dyadic v h2
  have h2ne : Valued.v (2 : Fv) ≠ 0 := by rw [h2v]; exact exp_ne_zero
  refine ⟨fun k hk => ?_, fun e he => ?_⟩
  · obtain ⟨m, hm⟩ := col_unit h2 γ hG hdet k
    by_cases hmk : m = k
    · subst hmk; exact hm
    · exfalso
      have h0 : locGram Q v γ m k = 0 :=
        hzero m k hmk (fun h => hk ⟨(m, k), h, Or.inr rfl⟩) (fun h => hk ⟨(k, m), h, Or.inl rfl⟩)
      rw [h0, map_zero] at hm
      exact h2ne hm.symm
  · obtain ⟨hne, h0, hi, hj⟩ := hpair e he
    obtain ⟨m, hm⟩ := col_unit h2 γ hG hdet e.1
    by_cases hm1 : m = e.1
    · exfalso
      rw [hm1] at hm
      have h12 := hG e.1 e.2
      have hlt : Valued.v (2 : Fv) * Valued.v (2 : Fv) < Valued.v (2 : Fv) := by
        rw [h2v, ← exp_add]
        exact exp_lt_exp.mpr (by norm_num)
      have : Valued.v (2 : Fv) ≤ Valued.v (2 : Fv) * Valued.v (2 : Fv) := by
        calc Valued.v (2 : Fv) = Valued.v (locGram Q v γ e.1 e.1) := hm.symm
          _ ≤ Valued.v (2 * locGram Q v γ e.1 e.2) := hi
          _ = Valued.v (2 : Fv) * Valued.v (locGram Q v γ e.1 e.2) := map_mul _ _ _
          _ ≤ _ := mul_le_mul' le_rfl h12
      exact absurd (lt_of_le_of_lt this hlt) (lt_irrefl _)
    by_cases hm2 : m = e.2
    · rw [hm2] at hm
      rw [locGram_symm' (Q := Q) (v := v) γ e.1 e.2]
      exact hm
    · exfalso
      have k1 : (m, e.1) ∉ P := by
        intro hP
        by_cases hee : (m, e.1) = e
        · exact hm1 (Prod.ext_iff.mp hee).1
        · obtain ⟨-, -, h3, -⟩ := hdisj _ hP e he hee
          exact h3 rfl
      have k2 : (e.1, m) ∉ P := by
        intro hP
        by_cases hee : (e.1, m) = e
        · exact hm2 (Prod.ext_iff.mp hee).2
        · obtain ⟨h1, -, -, -⟩ := hdisj _ hP e he hee
          exact h1 rfl
      have h0' : locGram Q v γ m e.1 = 0 := hzero m e.1 hm1 k1 k2
      rw [h0', map_zero] at hm
      exact h2ne hm.symm

theorem card_unpaired {P : Finset (Fin n × Fin n)}
    (hdisj : ∀ e ∈ P, ∀ e' ∈ P, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2)
    (hne : ∀ e ∈ P, e.1 ≠ e.2) (s : Finset (Fin n)) (hs : ∀ k, k ∈ s ↔ ¬ LocalDensity.IsPaired P k) :
    s.card + 2 * P.card = n := by
  classical
  have hp : Finset.univ.filter (fun k => LocalDensity.IsPaired P k) =
      P.biUnion (fun e => ({e.1, e.2} : Finset (Fin n))) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨e, he, h⟩
      exact ⟨e, he, h.imp Eq.symm Eq.symm⟩
    · rintro ⟨e, he, h⟩
      exact ⟨e, he, h.imp Eq.symm Eq.symm⟩
  have hc : (P.biUnion (fun e => ({e.1, e.2} : Finset (Fin n)))).card = 2 * P.card := by
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun e he => Finset.card_pair (hne e he))]
      simp [mul_comm]
    · intro e he e' he' hee
      refine Finset.disjoint_left.mpr fun k hk hk' => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk hk'
      obtain ⟨h1, h2, h3, h4⟩ := hdisj e he e' he' hee
      rcases hk with rfl | rfl <;> rcases hk' with h | h
      · exact h1 h
      · exact h2 h
      · exact h3 h
      · exact h4 h
  have hs' : s = Finset.univ.filter (fun k => ¬ LocalDensity.IsPaired P k) := by
    ext k; simp [hs]
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun k => LocalDensity.IsPaired P k)
  rw [hp, hc, ← hs'] at this
  simp at this
  omega

/-- $x \equiv 0 \pmod 4$ in $\mathbb Z/8$. -/
def Z4 (x : ZMod 8) : Prop := x = 0 ∨ x = 4

instance (x : ZMod 8) : Decidable (Z4 x) := by unfold Z4; infer_instance

theorem exists_four_mul {x y : 𝔬} {a b : ZMod 8} (hx : Rl x a) (hy : Rl y b)
    (h : Z4 (a - b)) : ∃ m : 𝔬, x = y + 4 * m := by
  have := hx.sub hy
  unfold Z4 at h
  rcases h with h | h
  · rw [h] at this
    obtain ⟨m, hm⟩ := Rl.of_cast (n := 0) (by simpa using this)
    exact ⟨2 * m, by push_cast at hm; linear_combination hm⟩
  · rw [h] at this
    obtain ⟨m, hm⟩ := Rl.of_cast (n := 4) (by simpa using this)
    exact ⟨1 + 2 * m, by push_cast at hm; linear_combination hm⟩

theorem pigeon4 : ∀ a b c : ZMod 8, Od a → Od b → Od c →
    Z4 (a - b) ∨ Z4 (a - c) ∨ Z4 (b - c) := by decide

theorem three_units (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u1 u2 u3 : 𝔬} (h1 : IsUnit u1) (h2' : IsUnit u2)
    (h3 : IsUnit u3) :
    (∃ m : 𝔬, u1 = u2 + 4 * m) ∨ (∃ m : 𝔬, u1 = u3 + 4 * m) ∨ (∃ m : 𝔬, u2 = u3 + 4 * m) := by
  obtain ⟨a, ha, ha'⟩ := Rl.unit_exists h2 h1
  obtain ⟨b, hb, hb'⟩ := Rl.unit_exists h2 h2'
  obtain ⟨c, hc, hc'⟩ := Rl.unit_exists h2 h3
  rcases pigeon4 a b c ha' hb' hc' with h | h | h
  · exact Or.inl (exists_four_mul ha hb h)
  · exact Or.inr (Or.inl (exists_four_mul ha hc h))
  · exact Or.inr (Or.inr (exists_four_mul hb hc h))

theorem vadd_one {x y : Fv} (hx : Valued.v x = 1) (hy : Valued.v y < 1) : Valued.v (x + y) = 1 := by
  rw [Valuation.map_add_eq_of_lt_left _ (by rwa [hx])]
  exact hx

theorem v_two_lt_one (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : Valued.v (2 : Fv) < 1 := by
  rw [valued_two_dyadic v h2, ← exp_zero]
  exact exp_lt_exp.mpr (by norm_num)

/-- Two orthogonal unit-norm vectors $b_a, b_b$ with $Q(b_a) \equiv Q(b_b) \pmod 4$ give $y = b_a + b_b$ with
$\lvert Q(y)\rvert = \lvert 2\rvert$. -/
theorem caseA_y (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv) {a b : Fin n}
    (hab0 : locGram Q v γ a b = 0) {ua ub m : 𝔬} (hub : IsUnit ub)
    (hua : locGram Q v γ a a = 2 * (ua : Fv)) (hub' : locGram Q v γ b b = 2 * (ub : Fv))
    (hm : ua = ub + 4 * m) :
    Valued.v (Q.evalIn Fv (γ.val *ᵥ (Pi.single a 1 + Pi.single b 1))) = Valued.v (2 : Fv) := by
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  have e1 := two_Q_pair (Q := Q) (v := v) γ (k := a) (l := b)
  rw [hua, hub', hab0] at e1
  have hm' : (ua : Fv) = (ub : Fv) + 4 * (m : Fv) := by
    have := congrArg (fun x : 𝔬 => (x : Fv)) hm
    push_cast at this
    rw [coe_four_eq] at this
    exact this
  have hq : Q.evalIn Fv (γ.val *ᵥ (Pi.single a 1 + Pi.single b 1)) = 2 * ((ub : Fv) + 2 * (m : Fv)) := by
    apply mul_left_cancel₀ h2ne
    rw [e1, hm']; ring
  have hub1 := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hub
  have hv : Valued.v ((ub : Fv) + 2 * (m : Fv)) = 1 := by
    refine vadd_one hub1 ?_
    rw [map_mul]
    calc Valued.v (2 : Fv) * Valued.v (m : Fv) ≤ Valued.v (2 : Fv) * 1 := mul_le_mul' le_rfl (vle_one m)
      _ = Valued.v (2 : Fv) := mul_one _
      _ < 1 := v_two_lt_one h2
  rw [hq, map_mul, hv, mul_one]

/-- A $2\times2$ block $(a, b)$ with $\lvert G_{ab}\rvert = \lvert 2\rvert$ and $\lvert G_{aa}\rvert, \lvert G_{bb}\rvert
\le \lvert 2G_{ab}\rvert$ contains one of $b_a, b_b, b_a + b_b$ with $\lvert Q\rvert = \lvert 2\rvert$. -/
theorem caseB_y (_h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv) {a b : Fin n}
    (hab : Valued.v (locGram Q v γ a b) = Valued.v (2 : Fv))
    (ha : Valued.v (locGram Q v γ a a) ≤ Valued.v (2 * locGram Q v γ a b))
    (hb : Valued.v (locGram Q v γ b b) ≤ Valued.v (2 * locGram Q v γ a b)) :
    ∃ cy : Fin n → Fv, cy ∈ std v ∧
      Valued.v (Q.evalIn Fv (γ.val *ᵥ cy)) = Valued.v (2 : Fv) := by
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  have h4ne : (4 : Fv) ≠ 0 := by norm_num
  have h2pos : 0 < Valued.v (2 : Fv) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr h2ne)
  have hv4 : Valued.v (4 : Fv) = Valued.v (2 : Fv) * Valued.v (2 : Fv) := by
    rw [← map_mul]; norm_num
  obtain ⟨β, hβ, hβ'⟩ := exists_unit_ratio h2ne hab
  have hβ1 := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hβ
  have hbound : Valued.v (2 * locGram Q v γ a b) = Valued.v (4 : Fv) := by
    rw [hβ', map_mul, map_mul, hβ1, mul_one, hv4]
  have hα1 : Valued.v (locGram Q v γ a a / 4) ≤ 1 := by
    rw [map_div₀, div_le_one₀ (by rw [hv4]; exact mul_pos h2pos h2pos)]
    exact hbound ▸ ha
  have hδ1 : Valued.v (locGram Q v γ b b / 4) ≤ 1 := by
    rw [map_div₀, div_le_one₀ (by rw [hv4]; exact mul_pos h2pos h2pos)]
    exact hbound ▸ hb
  set α : 𝔬 := toO v _ hα1
  set δ : 𝔬 := toO v _ hδ1
  have hGa : locGram Q v γ a a = 4 * (α : Fv) := by
    show locGram Q v γ a a = 4 * (locGram Q v γ a a / 4)
    field_simp
  have hGb : locGram Q v γ b b = 4 * (δ : Fv) := by
    show locGram Q v γ b b = 4 * (locGram Q v γ b b / 4)
    field_simp
  have hq : ∀ (c : Fin n → Fv) (t : Fv), 2 * Q.evalIn Fv (γ.val *ᵥ c) = 2 * (2 * t) →
      Q.evalIn Fv (γ.val *ᵥ c) = 2 * t := fun c t h => mul_left_cancel₀ h2ne h
  have hv_of : ∀ (t : 𝔬), IsUnit t → Valued.v (2 * (t : Fv)) = Valued.v (2 : Fv) := fun t ht => by
    rw [map_mul, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp ht, mul_one]
  by_cases hαu : IsUnit α
  · refine ⟨Pi.single a 1, single_mem_std a (by simp), ?_⟩
    have : Q.evalIn Fv (γ.val *ᵥ Pi.single a 1) = 2 * (α : Fv) := hq _ _ (by
      rw [two_Q_single, hGa]; ring)
    rw [this]; exact hv_of α hαu
  by_cases hδu : IsUnit δ
  · refine ⟨Pi.single b 1, single_mem_std b (by simp), ?_⟩
    have : Q.evalIn Fv (γ.val *ᵥ Pi.single b 1) = 2 * (δ : Fv) := hq _ _ (by
      rw [two_Q_single, hGb]; ring)
    rw [this]; exact hv_of δ hδu
  · refine ⟨Pi.single a 1 + Pi.single b 1, (std v).add_mem (single_mem_std a (by simp))
      (single_mem_std b (by simp)), ?_⟩
    have hαlt : Valued.v (α : Fv) < 1 := by
      refine lt_of_le_of_ne (vle_one α) fun h => hαu ?_
      exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr h
    have hδlt : Valued.v (δ : Fv) < 1 := by
      refine lt_of_le_of_ne (vle_one δ) fun h => hδu ?_
      exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr h
    have hsum : Valued.v ((β : Fv) + ((α : Fv) + (δ : Fv))) = 1 := by
      refine vadd_one hβ1 ?_
      calc Valued.v ((α : Fv) + (δ : Fv)) ≤ max (Valued.v (α : Fv)) (Valued.v (δ : Fv)) :=
            Valuation.map_add _ _ _
        _ < 1 := max_lt hαlt hδlt
    have : Q.evalIn Fv (γ.val *ᵥ (Pi.single a 1 + Pi.single b 1)) =
        2 * ((β : Fv) + ((α : Fv) + (δ : Fv))) := hq _ _ (by
      rw [two_Q_pair, hGa, hGb, hβ']; ring)
    rw [this, map_mul, hsum, mul_one]

/-- **Conway–Sloane, Ch. 15, §9.7, proof of Cor. 22 ($n$ odd, local form at $2$): an element of $\theta(O^+(L_2))$ of
odd order.** Let $n \ge 3$ be odd, $L_2 = \gamma\mathbb Z_2^n$ (`hγ`) with $Q$ $2$-adically integral on $L_2$ (`hint`),
the polar form classically integral (`hci`: $\lvert B(x,y)\rvert \le \lvert 2\rvert$ for $x, y \in L_2$) and
unimodular in the classical sense (`hdet`: $\lvert\det G\rvert = \lvert 2\rvert^n$, i.e. $\det(\tfrac12G)$ is a unit).
Then $\theta(O^+(L_2))$ contains an element $c$ with $\lvert c\rvert = \lvert 2\rvert$. Hypotheses `hQ`: $Q$ is
nondegenerate; `h2`: the prime $v$ lies over $2$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, proof of Cor. 22, p. 395 (d odd, n odd: θ(Λ_2) has an element of odd order; an argument not in the book)"]
theorem exists_odd_order_of_unimodular (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (L : Lat ℚ n) (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1) (hn : Odd n) (hn3 : 3 ≤ n)
    (hci : ∀ x ∈ loc v L.1, ∀ y ∈ loc v L.1, Valued.v (qbil Q Fv x y) ≤ Valued.v (2 : Fv))
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    (hdet : Valued.v (locGram Q v γ).det = Valued.v ((2 : Fv) ^ n)) :
    ∃ c : Fvˣ, c ∈ localSpinorNormGroup Q hQ v L ∧ Valued.v (c : Fv) = exp (-1 : ℤ) := by
  classical
  have h2' : ¬ LocalDensity.NF.π v ^ 2 ∣ 2 := fun h =>
    Tamagawa.Indefinite.two_not_mem_sq h2 ((LocalDensity.NF.π_pow_dvd_two_iff v 2).mp h)
  obtain ⟨γ', P, ν, hγ', hdet', hzero, hdisj, hpair, hsing⟩ :=
    exists_dyadic_basis hQ (valued_two_dyadic v h2) h2' L γ hγ hint
  have hG := hG_of_ci L γ' hγ' hci
  have hdetG : Valued.v (locGram Q v γ').det = Valued.v (2 : Fv) ^ n := by
    rw [hdet', hdet, map_pow]
  obtain ⟨hS, hB⟩ := dyadic_unimod h2 γ' P hzero hdisj hpair hG hdetG
  have hs : ∀ k, k ∈ Finset.univ.filter (fun k => ¬ LocalDensity.IsPaired P k) ↔
      ¬ LocalDensity.IsPaired P k := fun k => by simp
  have hcard := card_unpaired hdisj (fun e he => (hpair e he).1) _ hs
  set s := Finset.univ.filter (fun k => ¬ LocalDensity.IsPaired P k) with hsdef
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  -- the unit-norm vector `x`
  have hxcase : ∀ k ∈ s, Valued.v (Q.evalIn Fv (γ'.val *ᵥ (Pi.single k 1 : Fin n → Fv))) = 1 := by
    intro k hk
    have hk' := (hs k).mp hk
    refine vQ_eq h2 ?_
    rw [two_Q_single, hS k hk', mul_one]
  have hxstd : ∀ k, (Pi.single k 1 : Fin n → Fv) ∈ std v := fun k => single_mem_std k (by simp)
  by_cases hPe : P = ∅
  · -- no `2 × 2` blocks: all `n ≥ 3` vectors are singles
    subst hPe
    have hsn : s.card = n := by simpa using hcard
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp (by omega : 2 < s.card)
    have hunit : ∀ k ∈ s, ∃ u : 𝔬, IsUnit u ∧ locGram Q v γ' k k = 2 * (u : Fv) := by
      intro k hk
      obtain ⟨u, hu, hu'⟩ := exists_unit_ratio h2ne (hS k ((hs k).mp hk))
      exact ⟨u, hu, hu'⟩
    have horth : ∀ k l, k ≠ l → locGram Q v γ' k l = 0 := fun k l hkl =>
      hzero k l hkl (by simp) (by simp)
    obtain ⟨ua, hua, hua'⟩ := hunit a ha
    obtain ⟨ub, hub, hub'⟩ := hunit b hb
    obtain ⟨uc, huc, huc'⟩ := hunit c hc
    have key : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ ∃ ux uy m : 𝔬, IsUnit uy ∧
        locGram Q v γ' x x = 2 * (ux : Fv) ∧ locGram Q v γ' y y = 2 * (uy : Fv) ∧ ux = uy + 4 * m := by
      rcases three_units h2 hua hub huc with ⟨m, hm⟩ | ⟨m, hm⟩ | ⟨m, hm⟩
      · exact ⟨a, ha, b, hb, hab, ua, ub, m, hub, hua', hub', hm⟩
      · exact ⟨a, ha, c, hc, hac, ua, uc, m, huc, hua', huc', hm⟩
      · exact ⟨b, hb, c, hc, hbc, ub, uc, m, huc, hub', huc', hm⟩
    obtain ⟨x, hx, y, hy, hxy, ux, uy, m, huy, hux', huy', hm⟩ := key
    exact exists_of_xy hQ L h2 γ' hγ' hG (hxstd x)
      ((std v).add_mem (hxstd x) (hxstd y)) (hxcase x hx)
      (caseA_y h2 γ' (horth x y hxy) huy hux' huy' hm)
  · -- some `2 × 2` block
    obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hPe
    have hspos : 0 < s.card := by
      have : 2 * P.card % 2 = 0 := by omega
      obtain ⟨t, ht⟩ := hn
      omega
    obtain ⟨k, hk⟩ := Finset.card_pos.mp hspos
    obtain ⟨-, -, hi, hj⟩ := hpair e he
    obtain ⟨cy, hcy, hcyv⟩ := caseB_y h2 γ' (hB e he) hi hj
    exact exists_of_xy hQ L h2 γ' hγ' hG (hxstd k) hcy (hxcase k hk) hcyv

end Odd

end QuadFormsKB.ConwaySloane
