/-
# Hilbert reciprocity over $\mathbb{F}_q(t)$

For a finite field $k = \mathbb{F}_q$ of odd characteristic, the **Hilbert reciprocity law** holds over $k(t)$
(`hilbertReciprocity`, which proves the named input `RatFuncPlace.HilbertReciprocity k` of `RatFuncHMFour.lean`):
for $a, b \in k(t)^\times$, $(a, b)_v = -1$ at only finitely many places $v$, and at an even number of them,
i.e. $\prod_v (a, b)_v = 1$. This is O'Meara 71:18 with the number field replaced by $k(t)$.

*Proof* (the classical one for $\mathbb{Q}$, Serre Ch. III §2.1, Thm. 3, transposed to $k[t]$; purely local formulas
plus quadratic reciprocity). Both sides are multiplicative in each argument (`localHilbertMul`), so it suffices to
check the product formula for the generators of $k(t)^\times$: the constants $c \in k^\times$ and the monic irreducible
$P \in k[t]$. The local symbols of generators are (with $\chi$ the quadratic character of $k$ and $d = \deg P$):

* at a finite place $Q$: units have symbol $1$ (`hilbert_units`), and $(P, a)_P = \left(\frac{a}{P}\right)$ for
  $P \nmid a$ (`hilbert_unif`, the Legendre symbol of `RatFuncQR.lean`);
* at $\infty$, with uniformizer $t^{-1}$: $(c, c')_\infty = 1$, $(c, t)_\infty = \chi(c)$, and a monic $P$ of degree
  $d$ is $t^d$ times a square (`hilbert_infty_monic`), so $(a, P)_\infty = (a, t)_\infty^d$ and
  $(t, t)_\infty = (t, -1)_\infty = \chi(-1)$.

So for $(c, P)$ the symbol is $\chi(c)^d$ at $P$ (supplementary law `RatFuncQR.legendreSym_C`) and at $\infty$, and
$1$ elsewhere; for distinct $(P, Q)$ it is $\left(\frac{Q}{P}\right)$ at $P$, $\left(\frac{P}{Q}\right)$ at $Q$ and
$\chi(-1)^{\deg P \deg Q}$ at $\infty$, whose product is $1$ by quadratic reciprocity
(`RatFuncQR.legendreSym_mul_legendreSym`); and $(P, P)_v = (P, -1)_v$.

Indices are 0-based.
-/
import QuadFormsKB.FunctionField.RatFuncLocal
import QuadFormsKB.FunctionField.RatFuncQR

open IsDedekindDomain Polynomial WithZero

namespace QuadFormsKB.RatFuncPlace

open scoped Classical

variable {k : Type} [Field k]

/-! ### Generic facts about the local symbols -/

lemma hilbert_pm (v : RatFuncPlace k) (a b : RatFunc k) : v.hilbert a b = 1 ∨ v.hilbert a b = -1 := by
  cases v <;> exact FF.OddLocalAxioms.hs_pm _ _

lemma hilbert_comm (v : RatFuncPlace k) (a b : RatFunc k) : v.hilbert a b = v.hilbert b a := by
  cases v <;> exact hilbertSymbol_comm _ _ _

variable [Fintype k]

lemma hilbert_mul_left (hk : ringChar k ≠ 2) (v : RatFuncPlace k) {a b c : RatFunc k} (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) : v.hilbert (a * b) c = v.hilbert a c * v.hilbert b c := by
  have h := (localHilbertMul hk).mul_left v
  cases v with
  | finite w =>
    simp only [hilbert, map_mul]
    exact h _ _ _ ((_root_.map_ne_zero _).mpr ha) ((_root_.map_ne_zero _).mpr hb)
      ((_root_.map_ne_zero _).mpr hc)
  | infinite =>
    simp only [hilbert, map_mul]
    exact h _ _ _ ((_root_.map_ne_zero _).mpr ha) ((_root_.map_ne_zero _).mpr hb)
      ((_root_.map_ne_zero _).mpr hc)

lemma hilbert_mul_right (hk : ringChar k ≠ 2) (v : RatFuncPlace k) {a b c : RatFunc k} (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) : v.hilbert a (b * c) = v.hilbert a b * v.hilbert a c := by
  rw [hilbert_comm, hilbert_mul_left hk v hb hc ha, hilbert_comm v b, hilbert_comm v c]

omit [Fintype k] in
lemma hilbert_inv_right (v : RatFuncPlace k) (a : RatFunc k) {b : RatFunc k} (hb : b ≠ 0) :
    v.hilbert a b⁻¹ = v.hilbert a b := by
  have e : b⁻¹ = b * (b⁻¹) ^ 2 := by field_simp
  cases v with
  | finite w =>
    simp only [hilbert]
    rw [e, map_mul, map_pow, FF.OddLocalAxioms.hs_mul_sq_right _ _ _
      ((_root_.map_ne_zero _).mpr (inv_ne_zero hb))]
  | infinite =>
    simp only [hilbert]
    rw [e, map_mul, map_pow, FF.OddLocalAxioms.hs_mul_sq_right _ _ _
      ((_root_.map_ne_zero _).mpr (inv_ne_zero hb))]

/-- $(a, a)_v = (a, -1)_v$. -/
lemma hilbert_self (hk : ringChar k ≠ 2) (v : RatFuncPlace k) {a : RatFunc k} (ha : a ≠ 0) :
    v.hilbert a a = v.hilbert a (-1) := by
  have h1 : v.hilbert a (-a) = 1 := by
    cases v <;> simp only [hilbert, map_neg] <;> exact hilbertSymbol_self_neg _ _
  rw [show -a = a * (-1) by ring, hilbert_mul_right hk v ha ha (by norm_num)] at h1
  rcases hilbert_pm v a a with h | h <;> rcases hilbert_pm v a (-1) with h' | h' <;>
    rw [h, h'] at h1 ⊢ <;> norm_num at h1

/-! ### The product formula, abstractly -/

/-- **The product formula for $(a, b)$:** some finite set $S$ of places carries all the places where
$(a, b)_v \ne 1$, and $\prod_{v \in S} (a, b)_v = 1$. -/
def ProdOne (a b : RatFunc k) : Prop :=
  ∃ S : Finset (RatFuncPlace k), (∀ v ∉ S, v.hilbert a b = 1) ∧ ∏ v ∈ S, v.hilbert a b = 1

omit [Fintype k] in
lemma ProdOne.symm {a b : RatFunc k} (h : ProdOne a b) : ProdOne b a := by
  obtain ⟨S, h1, h2⟩ := h
  exact ⟨S, fun v hv => by rw [hilbert_comm]; exact h1 v hv,
    by rw [← h2]; exact Finset.prod_congr rfl fun v _ => hilbert_comm v b a⟩

omit [Fintype k] in
lemma ProdOne.congr {a b a' b' : RatFunc k} (h : ProdOne a b)
    (he : ∀ v : RatFuncPlace k, v.hilbert a' b' = v.hilbert a b) : ProdOne a' b' := by
  obtain ⟨S, h1, h2⟩ := h
  exact ⟨S, fun v hv => by rw [he]; exact h1 v hv,
    by rw [← h2]; exact Finset.prod_congr rfl fun v _ => he v⟩

omit [Fintype k] in
lemma ProdOne.inv_right {a b : RatFunc k} (hb : b ≠ 0) (h : ProdOne a b) : ProdOne a b⁻¹ :=
  h.congr fun v => hilbert_inv_right v a hb

omit [Fintype k] in
/-- Enlarging $S$ does not change the product. -/
lemma prod_eq_of_subset {a b : RatFunc k} {S T : Finset (RatFuncPlace k)} (hST : S ⊆ T)
    (h1 : ∀ v ∉ S, v.hilbert a b = 1) : ∏ v ∈ T, v.hilbert a b = ∏ v ∈ S, v.hilbert a b :=
  (Finset.prod_subset hST fun v _ hv => h1 v hv).symm

lemma ProdOne.mul_right (hk : ringChar k ≠ 2) {a b b' : RatFunc k} (ha : a ≠ 0) (hb : b ≠ 0)
    (hb' : b' ≠ 0) (h : ProdOne a b) (h' : ProdOne a b') : ProdOne a (b * b') := by
  obtain ⟨S, h1, h2⟩ := h
  obtain ⟨S', h1', h2'⟩ := h'
  refine ⟨S ∪ S', fun v hv => ?_, ?_⟩
  · rw [Finset.mem_union, not_or] at hv
    rw [hilbert_mul_right hk v ha hb hb', h1 v hv.1, h1' v hv.2, mul_one]
  · rw [Finset.prod_congr rfl fun v _ => hilbert_mul_right hk v ha hb hb', Finset.prod_mul_distrib,
      prod_eq_of_subset Finset.subset_union_left h1, prod_eq_of_subset Finset.subset_union_right h1',
      h2, h2', mul_one]

lemma ProdOne.mul_left (hk : ringChar k ≠ 2) {a a' b : RatFunc k} (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hb : b ≠ 0) (h : ProdOne a b) (h' : ProdOne a' b) : ProdOne (a * a') b :=
  (ProdOne.mul_right hk hb ha ha' h.symm h'.symm).symm

omit [Fintype k] in
/-- The product formula gives the parity statement of `HilbertReciprocity`. -/
lemma ProdOne.finite_even {a b : RatFunc k} (h : ProdOne a b) :
    {v : RatFuncPlace k | v.hilbert a b = -1}.Finite ∧
      Even {v : RatFuncPlace k | v.hilbert a b = -1}.ncard := by
  obtain ⟨S, h1, h2⟩ := h
  have hset : {v : RatFuncPlace k | v.hilbert a b = -1} = ↑(S.filter fun v => v.hilbert a b = -1) := by
    ext v
    simp only [Set.mem_ofPred_eq, Finset.coe_filter]
    constructor
    · intro hv
      refine ⟨?_, hv⟩
      by_contra hS
      rw [h1 v hS] at hv
      norm_num at hv
    · exact fun hv => hv.2
  rw [hset, Set.ncard_coe_finset]
  refine ⟨Finset.finite_toSet _, ?_⟩
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun v => v.hilbert a b = -1)] at h2
  rw [Finset.prod_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2), Finset.prod_const,
    Finset.prod_congr rfl (fun v hv => ((hilbert_pm v a b).resolve_right (Finset.mem_filter.mp hv).2)),
    Finset.prod_const_one, mul_one] at h2
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp h2

/-! ### Local symbols at the finite places -/

section Finite

variable (w : HeightOneSpectrum k[X])

local notation "Kw" => w.adicCompletion (RatFunc k)

omit [Fintype k] in
lemma v_poly_eq_one {p : k[X]} (hp : p ∉ w.asIdeal) :
    Valued.v (algebraMap (RatFunc k) Kw (algebraMap k[X] (RatFunc k) p)) = 1 := by
  rw [v_finite_poly, HeightOneSpectrum.intValuation_eq_one_iff]; exact hp

/-- **Units have trivial symbol** at a finite place: if $a, b \in k[t]$ are prime to $w$, then $(a, b)_w = 1$. -/
lemma hilbert_units (hk : ringChar k ≠ 2) {a b : k[X]} (ha : a ∉ w.asIdeal) (hb : b ∉ w.asIdeal) :
    (finite w).hilbert (algebraMap k[X] (RatFunc k) a) (algebraMap k[X] (RatFunc k) b) = 1 := by
  have h := oddLocalAxioms_finite w hk
  simp only [hilbert]
  by_cases hsq : IsSquare (algebraMap (RatFunc k) Kw (algebraMap k[X] (RatFunc k) a))
  · exact FF.OddLocalAxioms.hs_of_isSquare hsq _
  · obtain ⟨π, hπ⟩ := h.exists_uniformizer
    have hb1 := v_poly_eq_one w hb
    have hb0 : algebraMap (RatFunc k) Kw (algebraMap k[X] (RatFunc k) b) ≠ 0 := by
      intro h0; rw [h0, Valuation.map_zero] at hb1; exact zero_ne_one hb1
    rw [h.unit_hs_iff hπ (v_poly_eq_one w ha) hsq hb0,
      FF.OddLocalAxioms.L_of_v (n := 0) (by rw [hb1, exp_zero])]
    exact ⟨0, by norm_num⟩

omit [Fintype k] in
/-- An irreducible $P$ lies in no height-one prime other than $(P)$. -/
lemma not_mem_of_ne {P : k[X]} (hP : Irreducible P) (hw : w ≠ ofIrreducible P hP) : P ∉ w.asIdeal := by
  intro hmem
  apply hw
  have hmax : (Ideal.span {P}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hP
  have hle : Ideal.span {P} ≤ w.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hmem
  have := hmax.eq_of_le w.isPrime.ne_top hle
  exact HeightOneSpectrum.ext this.symm

end Finite

omit [Fintype k] in
lemma mem_ofIrreducible_iff {P : k[X]} (hP : Irreducible P) (a : k[X]) :
    a ∈ (ofIrreducible P hP).asIdeal ↔ P ∣ a := by
  rw [ofIrreducible_asIdeal, Ideal.mem_span_singleton]

/-- **The symbol of the uniformizer at its own place is the Legendre symbol:** for $P$ monic irreducible and
$P \nmid a$, $(P, a)_P = \left(\frac{a}{P}\right)$. -/
lemma hilbert_unif (hk : ringChar k ≠ 2) {P : k[X]} (hP : Irreducible P) {a : k[X]} (ha : ¬ P ∣ a) :
    (finite (ofIrreducible P hP)).hilbert (algebraMap k[X] (RatFunc k) P)
      (algebraMap k[X] (RatFunc k) a) = RatFuncQR.legendreSym P a := by
  set w := ofIrreducible P hP
  have h := oddLocalAxioms_finite w hk
  set ρ : k[X] →+* w.adicCompletion (RatFunc k) :=
    (algebraMap (RatFunc k) (w.adicCompletion (RatFunc k))).comp (algebraMap k[X] (RatFunc k)) with hρ
  have hρv : ∀ p, Valued.v (ρ p) = w.intValuation p := fun p => v_finite_poly w p
  have haw : a ∉ w.asIdeal := by rw [mem_ofIrreducible_iff]; exact ha
  have hPv : Valued.v (ρ P) = exp (-1 : ℤ) := by
    rw [hρv]
    refine FF.intValuation_eq_exp_neg_one w P ((mem_ofIrreducible_iff hP P).mpr dvd_rfl) ?_
    intro hmem
    rw [ofIrreducible_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    apply hP.not_isUnit
    obtain ⟨c, hc⟩ := hmem
    refine isUnit_iff_exists_inv.mpr ⟨c, ?_⟩
    have h0 : P * (P * c - 1) = 0 := by rw [mul_sub, ← mul_assoc, ← sq, ← hc]; ring
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact absurd h0 hP.ne_zero
    · exact sub_eq_zero.mp h0
  have key : hilbertSymbol _ (ρ P) (ρ a) = 1 ↔ ∃ r : k[X], P ∣ r ^ 2 - a := by
    rw [h.unif_hs_unit_iff hPv (w := ρ a) (by rw [hρv, HeightOneSpectrum.intValuation_eq_one_iff]; exact haw)]
    constructor
    · intro hsq
      obtain ⟨r, hr⟩ := FF.exists_sq_mod_of_isSquare w a hsq
      exact ⟨r, by rw [← mem_ofIrreducible_iff hP, ← neg_sub]; exact w.asIdeal.neg_mem hr⟩
    · rintro ⟨r, hr⟩
      have hrw : r ∉ w.asIdeal := by
        intro hrm
        apply haw
        have : a = r ^ 2 - (r ^ 2 - a) := by ring
        rw [this]
        exact w.asIdeal.sub_mem (w.asIdeal.pow_mem_of_mem hrm 2 two_pos)
          ((mem_ofIrreducible_iff hP _).mpr hr)
      have hr1 : Valued.v (ρ (r ^ 2)) = 1 := by
        rw [hρv, HeightOneSpectrum.intValuation_eq_one_iff]
        exact fun hm => hrw (w.isPrime.mem_of_pow_mem 2 hm)
      have hr0 : ρ (r ^ 2) ≠ 0 := by
        intro h0; rw [h0, Valuation.map_zero] at hr1; exact zero_ne_one hr1
      obtain ⟨s, hs⟩ := h.isSquare_of_near_one (ρ a / ρ (r ^ 2)) (by
        have e : ρ a / ρ (r ^ 2) - 1 = -ρ (r ^ 2 - a) / ρ (r ^ 2) := by
          rw [map_sub]; field_simp; ring
        rw [e, map_div₀, Valuation.map_neg, hr1, div_one, hρv,
          HeightOneSpectrum.intValuation_lt_one_iff_mem]
        exact (mem_ofIrreducible_iff hP _).mpr hr)
      refine ⟨ρ r * s, ?_⟩
      have : ρ a = ρ (r ^ 2) * (ρ a / ρ (r ^ 2)) := by field_simp
      rw [this, hs, map_pow]; ring
  simp only [hilbert]
  change hilbertSymbol _ (ρ P) (ρ a) = _
  rw [RatFuncQR.legendreSym, if_neg ha]
  by_cases hr : ∃ r : k[X], P ∣ r ^ 2 - a
  · rw [if_pos hr]; exact key.mpr hr
  · rw [if_neg hr]
    exact (FF.OddLocalAxioms.hs_pm _ _).resolve_left (fun h1 => hr (key.mp h1))

/-! ### Local symbols at infinity -/

section Infinite

local notation "Ki" => RatFunc.CompletionAtInfty k

omit [Fintype k] in
lemma v_infty_C {c : k} (hc : c ≠ 0) :
    Valued.v (algebraMap (RatFunc k) Ki (algebraMap k[X] (RatFunc k) (C c))) = 1 := by
  rw [v_infty, v_infty_poly (C_ne_zero.mpr hc), natDegree_C]; rfl

/-- At infinity, constants have trivial symbol: $(c, c')_\infty = 1$. -/
lemma hilbert_infty_C_C (hk : ringChar k ≠ 2) {c c' : k} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    infinite.hilbert (algebraMap k[X] (RatFunc k) (C c)) (algebraMap k[X] (RatFunc k) (C c')) = 1 := by
  have h := oddLocalAxioms_infty (k := k) hk
  simp only [hilbert]
  by_cases hsq : IsSquare (algebraMap (RatFunc k) Ki (algebraMap k[X] (RatFunc k) (C c)))
  · exact FF.OddLocalAxioms.hs_of_isSquare hsq _
  · obtain ⟨π, hπ⟩ := h.exists_uniformizer
    have hb1 := v_infty_C (k := k) hc'
    have hb0 : algebraMap (RatFunc k) Ki (algebraMap k[X] (RatFunc k) (C c')) ≠ 0 := by
      intro h0; rw [h0, Valuation.map_zero] at hb1; exact zero_ne_one hb1
    rw [h.unit_hs_iff hπ (v_infty_C hc) hsq hb0, FF.OddLocalAxioms.L_of_v (n := 0) (by rw [hb1, exp_zero])]
    exact ⟨0, by norm_num⟩

omit [Fintype k] in
/-- A constant is a square at infinity iff it is a square in $k$ (the residue field at $\infty$ is $k$). -/
lemma isSquare_infty_C_iff {c : k} (hc : c ≠ 0) :
    IsSquare (algebraMap (RatFunc k) Ki (algebraMap k[X] (RatFunc k) (C c))) ↔ IsSquare c := by
  constructor
  · rintro ⟨s, hs⟩
    have hsv : Valued.v s = 1 := by
      have h1 := v_infty_C (k := k) hc
      rw [hs, map_mul] at h1
      rcases lt_trichotomy (Valued.v s) 1 with hlt | heq | hgt
      · exfalso
        have : Valued.v s * Valued.v s < 1 := by
          calc Valued.v s * Valued.v s ≤ 1 * Valued.v s := mul_le_mul_left hlt.le _
            _ < 1 := by rw [one_mul]; exact hlt
        rw [h1] at this; exact lt_irrefl _ this
      · exact heq
      · exfalso
        have : 1 < Valued.v s * Valued.v s := by
          calc 1 < 1 * Valued.v s := by rw [one_mul]; exact hgt
            _ ≤ Valued.v s * Valued.v s := mul_le_mul_left hgt.le _
        rw [h1] at this; exact lt_irrefl _ this
    obtain ⟨c₀, hc₀⟩ := exists_const_near_infty s hsv.le
    set e := algebraMap (RatFunc k) Ki (RatFunc.C c₀)
    refine ⟨c₀, ?_⟩
    by_contra hne
    have hd : c - c₀ * c₀ ≠ 0 := sub_ne_zero.mpr hne
    have h1 := v_infty_C (k := k) hd
    have e1 : algebraMap (RatFunc k) Ki (algebraMap k[X] (RatFunc k) (C (c - c₀ * c₀))) =
        (s - e) * (s + e) := by
      have hce : algebraMap (RatFunc k) Ki (algebraMap k[X] (RatFunc k) (C c₀)) = e := by
        simp only [e, RatFunc.algebraMap_C]
      rw [C_sub, C_mul, map_sub, map_sub, map_mul, map_mul, hs, hce]; ring
    rw [e1, map_mul] at h1
    have hle : Valued.v (s + e) ≤ 1 := by
      have : s + e = (s + s) - (s - e) := by ring
      rw [this]
      refine (Valuation.map_sub _ _ _).trans (max_le ((Valuation.map_add _ _ _).trans
        (max_le hsv.le hsv.le)) hc₀.le)
    have : Valued.v (s - e) * Valued.v (s + e) < 1 := by
      calc Valued.v (s - e) * Valued.v (s + e) ≤ Valued.v (s - e) * 1 := mul_le_mul_right hle _
        _ < 1 := by rw [mul_one]; exact hc₀
    rw [h1] at this; exact lt_irrefl _ this
  · rintro ⟨r, rfl⟩
    exact ⟨algebraMap (RatFunc k) Ki (algebraMap k[X] (RatFunc k) (C r)), by simp [C_mul]⟩

/-- **The symbol $(c, t)_\infty$ is the quadratic character** $\chi(c)$ of $k$ (as $t = (t^{-1})^{-1}$, with
$t^{-1}$ a uniformizer at $\infty$). -/
lemma hilbert_infty_C_X (hk : ringChar k ≠ 2) [DecidableEq k] {c : k} (hc : c ≠ 0) :
    infinite.hilbert (algebraMap k[X] (RatFunc k) (C c)) (algebraMap k[X] (RatFunc k) X) =
      quadraticChar k c := by
  have h := oddLocalAxioms_infty (k := k) hk
  have hX0 : (algebraMap k[X] (RatFunc k) X) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr X_ne_zero
  rw [← hilbert_inv_right _ _ hX0, hilbert_comm]
  set π := algebraMap (RatFunc k) Ki (algebraMap k[X] (RatFunc k) X)⁻¹
  have hπ : Valued.v π = exp (-1 : ℤ) := by
    simp only [π]
    rw [v_infty, ← one_div, RatFunc.algebraMap_X]
    exact RatFunc.inftyValuation.X_inv k
  have key := h.unif_hs_unit_iff hπ (v_infty_C hc)
  simp only [hilbert]
  rw [isSquare_infty_C_iff hc] at key
  rcases quadraticChar_dichotomy hc with hq | hq
  · rw [hq]; exact key.mpr ((quadraticChar_one_iff_isSquare hc).mp hq)
  · rw [hq]
    refine (FF.OddLocalAxioms.hs_pm _ _).resolve_left fun h1 => ?_
    have := (quadraticChar_one_iff_isSquare hc).mpr (key.mp h1)
    rw [hq] at this; norm_num at this

/-- **A monic polynomial of degree $d$ is $t^d$ times a square at infinity**, so
$(a, P)_\infty = (a, t)_\infty^{d}$. -/
lemma hilbert_infty_monic (hk : ringChar k ≠ 2) {a : RatFunc k} (ha : a ≠ 0) {P : k[X]} (hP : P.Monic) :
    infinite.hilbert a (algebraMap k[X] (RatFunc k) P) =
      infinite.hilbert a (algebraMap k[X] (RatFunc k) X) ^ P.natDegree := by
  have h := oddLocalAxioms_infty (k := k) hk
  set d := P.natDegree
  have hXd : infinite.hilbert a (algebraMap k[X] (RatFunc k) (X ^ d)) =
      infinite.hilbert a (algebraMap k[X] (RatFunc k) X) ^ d := by
    have hX0 : (algebraMap k[X] (RatFunc k) X) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr X_ne_zero
    induction d with
    | zero =>
      rw [pow_zero, pow_zero, map_one]
      simp only [hilbert]
      rw [map_one, hilbertSymbol_comm]
      exact FF.OddLocalAxioms.hs_of_isSquare ⟨1, by ring⟩ _
    | succ n ih =>
      rw [pow_succ, map_mul, hilbert_mul_right hk _ ha
        ((map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr (pow_ne_zero _ X_ne_zero))
        hX0, ih, pow_succ]
  rw [← hXd]
  -- `P = t^d · (P / t^d)` with `P / t^d` close to `1`
  have hP0 : P ≠ 0 := hP.ne_zero
  have hXd0 : (X ^ d : k[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  set ι := algebraMap (RatFunc k) Ki
  set j := algebraMap k[X] (RatFunc k)
  have hj0 : ∀ {p : k[X]}, p ≠ 0 → j p ≠ 0 := fun hp =>
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hp
  obtain ⟨s, hs⟩ := h.isSquare_of_near_one (ι (j P / j (X ^ d))) (by
    have e : ι (j P / j (X ^ d)) - 1 = ι (j (P - X ^ d) / j (X ^ d)) := by
      have e' : j P / j (X ^ d) - 1 = j (P - X ^ d) / j (X ^ d) := by
        rw [map_sub, sub_div, div_self (hj0 hXd0)]
      rw [← e', map_sub, map_one]
    rw [e, v_infty]
    by_cases h0 : P - X ^ d = 0
    · rw [h0, map_zero, zero_div, map_zero]; exact zero_lt_one
    · rw [map_div₀, v_infty_poly h0, v_infty_poly hXd0, div_lt_one₀ (zero_lt_iff.mpr exp_ne_zero),
        exp_lt_exp, natDegree_X_pow]
      have hdeg : (P - X ^ d).degree < P.degree :=
        degree_sub_lt (by rw [degree_X_pow, degree_eq_natDegree hP0]) hP0
          (by rw [hP.leadingCoeff, leadingCoeff_X_pow])
      have := natDegree_lt_natDegree h0 hdeg
      exact_mod_cast this)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero, map_eq_zero_iff _ ι.injective, div_eq_zero_iff] at hs
    rcases hs with h1 | h1
    · exact hj0 hP0 h1
    · exact hj0 hXd0 h1
  have hPe : ι (j P) = ι (j (X ^ d)) * s ^ 2 := by
    rw [sq, ← hs, ← map_mul, mul_div_cancel₀ _ (hj0 hXd0)]
  simp only [hilbert]
  rw [hPe, FF.OddLocalAxioms.hs_mul_sq_right _ _ _ hs0]

end Infinite

/-! ### The product formula for the generators $c \in k^\times$ and monic irreducible $P$ -/

section Generators

omit [Fintype k] in
lemma j_ne_zero {p : k[X]} (hp : p ≠ 0) : algebraMap k[X] (RatFunc k) p ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hp

omit [Fintype k] in
lemma C_not_mem (w : HeightOneSpectrum k[X]) {c : k} (hc : c ≠ 0) : C c ∉ w.asIdeal :=
  fun h => w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (isUnit_C.mpr hc.isUnit))

omit [Fintype k] in
lemma not_dvd_C {P : k[X]} (hP : Irreducible P) {c : k} (hc : c ≠ 0) : ¬ P ∣ C c :=
  fun h => hP.not_isUnit (isUnit_of_dvd_unit h (isUnit_C.mpr hc.isUnit))

omit [Fintype k] in
lemma not_dvd_of_ne {P Q : k[X]} (hP : Irreducible P) (hPm : P.Monic) (hQ : Irreducible Q)
    (hQm : Q.Monic) (hPQ : P ≠ Q) : ¬ P ∣ Q :=
  fun h => hPQ (eq_of_monic_of_associated hPm hQm (hP.associated_of_dvd hQ h))

/-- $(c, c')$: every symbol is $1$. -/
lemma prodOne_C_C (hk : ringChar k ≠ 2) {c c' : k} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    ProdOne (algebraMap k[X] (RatFunc k) (C c)) (algebraMap k[X] (RatFunc k) (C c')) := by
  refine ⟨∅, fun v _ => ?_, by simp⟩
  cases v with
  | finite w => exact hilbert_units w hk (C_not_mem w hc) (C_not_mem w hc')
  | infinite => exact hilbert_infty_C_C hk hc hc'

/-- $(c, P)$: the symbol is $\chi(c)^{\deg P}$ at $P$ and at $\infty$, and $1$ elsewhere. -/
lemma prodOne_C_irr (hk : ringChar k ≠ 2) {c : k} (hc : c ≠ 0) {P : k[X]} (hP : Irreducible P)
    (hPm : P.Monic) : ProdOne (algebraMap k[X] (RatFunc k) (C c)) (algebraMap k[X] (RatFunc k) P) := by
  classical
  refine ⟨{infinite, finite (ofIrreducible P hP)}, fun v hv => ?_, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    cases v with
    | infinite => exact absurd rfl hv.1
    | finite w =>
      have hw : w ≠ ofIrreducible P hP := fun h => hv.2 (by rw [h])
      exact hilbert_units w hk (C_not_mem w hc) (not_mem_of_ne w hP hw)
  · rw [Finset.prod_pair (by simp), hilbert_infty_monic hk (j_ne_zero (C_ne_zero.mpr hc)) hPm,
      hilbert_infty_C_X hk hc, hilbert_comm, hilbert_unif hk hP (not_dvd_C hP hc),
      RatFuncQR.legendreSym_C hk P hP hPm, ← mul_pow, ← sq, quadraticChar_sq_one hc, one_pow]

/-- $(t, t)_\infty = \chi(-1)$. -/
lemma hilbert_infty_X_X (hk : ringChar k ≠ 2) :
    infinite.hilbert (algebraMap k[X] (RatFunc k) X) (algebraMap k[X] (RatFunc k) X) =
      quadraticChar k (-1) := by
  rw [hilbert_self hk _ (j_ne_zero X_ne_zero), hilbert_comm,
    show (-1 : RatFunc k) = algebraMap k[X] (RatFunc k) (C (-1)) by simp,
    hilbert_infty_C_X hk (by norm_num)]

/-- $(P, Q)$ for distinct monic irreducibles: the symbols at $P$, $Q$, $\infty$ are $\left(\frac{Q}{P}\right)$,
$\left(\frac{P}{Q}\right)$, $\chi(-1)^{\deg P \deg Q}$, with product $1$ by quadratic reciprocity. -/
lemma prodOne_irr_irr (hk : ringChar k ≠ 2) {P Q : k[X]} (hP : Irreducible P) (hPm : P.Monic)
    (hQ : Irreducible Q) (hQm : Q.Monic) (hPQ : P ≠ Q) :
    ProdOne (algebraMap k[X] (RatFunc k) P) (algebraMap k[X] (RatFunc k) Q) := by
  classical
  set wP := ofIrreducible P hP
  set wQ := ofIrreducible Q hQ
  have hPQ' : ¬ P ∣ Q := not_dvd_of_ne hP hPm hQ hQm hPQ
  have hQP' : ¬ Q ∣ P := not_dvd_of_ne hQ hQm hP hPm hPQ.symm
  have hw : wP ≠ wQ := by
    intro h
    apply hPQ'
    rw [← mem_ofIrreducible_iff hP, show ofIrreducible P hP = wQ from h, mem_ofIrreducible_iff]
  refine ⟨{infinite, finite wP, finite wQ}, fun v hv => ?_, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    cases v with
    | infinite => exact absurd rfl hv.1
    | finite w =>
      have h1 : w ≠ wP := fun h => hv.2.1 (by rw [h])
      have h2 : w ≠ wQ := fun h => hv.2.2 (by rw [h])
      exact hilbert_units w hk (not_mem_of_ne w hP h1) (not_mem_of_ne w hQ h2)
  · rw [Finset.prod_insert (by simp), Finset.prod_pair (by simpa using hw),
      hilbert_infty_monic hk (j_ne_zero hP.ne_zero) hQm, hilbert_comm infinite _ (algebraMap _ _ X),
      hilbert_infty_monic hk (j_ne_zero X_ne_zero) hPm, hilbert_infty_X_X hk,
      hilbert_unif hk hP hPQ', hilbert_comm (finite wQ), hilbert_unif hk hQ hQP',
      RatFuncQR.legendreSym_mul_legendreSym hk P Q hP hPm hQ hQm hPQ]
    rw [← pow_mul, ← mul_pow, ← sq, quadraticChar_sq_one (by norm_num), one_pow]

/-- $(P, P)_v = (P, -1)_v$, so $(P, P)$ reduces to $(-1, P)$. -/
lemma prodOne_irr_self (hk : ringChar k ≠ 2) {P : k[X]} (hP : Irreducible P) (hPm : P.Monic) :
    ProdOne (algebraMap k[X] (RatFunc k) P) (algebraMap k[X] (RatFunc k) P) := by
  refine (prodOne_C_irr hk (c := -1) (by norm_num) hP hPm).symm.congr fun v => ?_
  rw [hilbert_self hk v (j_ne_zero hP.ne_zero)]
  simp

/-- The generators of $k(t)^\times$: nonzero constants and monic irreducible polynomials. -/
def IsGen (a : RatFunc k) : Prop :=
  (∃ c : k, c ≠ 0 ∧ a = algebraMap k[X] (RatFunc k) (C c)) ∨
    ∃ P : k[X], Irreducible P ∧ P.Monic ∧ a = algebraMap k[X] (RatFunc k) P

omit [Fintype k] in
lemma IsGen.ne_zero {a : RatFunc k} (h : IsGen a) : a ≠ 0 := by
  rcases h with ⟨c, hc, rfl⟩ | ⟨P, hP, -, rfl⟩
  · exact j_ne_zero (C_ne_zero.mpr hc)
  · exact j_ne_zero hP.ne_zero

lemma prodOne_gen (hk : ringChar k ≠ 2) {a b : RatFunc k} (ha : IsGen a) (hb : IsGen b) :
    ProdOne a b := by
  rcases ha with ⟨c, hc, rfl⟩ | ⟨P, hP, hPm, rfl⟩ <;> rcases hb with ⟨c', hc', rfl⟩ | ⟨Q, hQ, hQm, rfl⟩
  · exact prodOne_C_C hk hc hc'
  · exact prodOne_C_irr hk hc hQ hQm
  · exact (prodOne_C_irr hk hc' hP hPm).symm
  · by_cases hPQ : P = Q
    · subst hPQ; exact prodOne_irr_self hk hP hPm
    · exact prodOne_irr_irr hk hP hPm hQ hQm hPQ

omit [Fintype k] in
/-- A prime of $k[t]$ is a nonzero constant times a monic irreducible. -/
lemma prime_eq_C_mul {p : k[X]} (hp : Prime p) :
    IsGen (algebraMap k[X] (RatFunc k) (C p.leadingCoeff)) ∧
      IsGen (algebraMap k[X] (RatFunc k) (p * C p.leadingCoeff⁻¹)) ∧
      p = C p.leadingCoeff * (p * C p.leadingCoeff⁻¹) := by
  have hp0 := hp.ne_zero
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  refine ⟨Or.inl ⟨_, hlc, rfl⟩, Or.inr ⟨_, ?_, monic_mul_leadingCoeff_inv hp0, rfl⟩, ?_⟩
  · exact (associated_mul_unit_right p _ (isUnit_C.mpr (inv_ne_zero hlc).isUnit)).irreducible
      hp.irreducible
  · rw [mul_comm p, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul]

omit [Fintype k] in
/-- Every nonzero polynomial is a product of generators: an induction principle. -/
lemma poly_induction {M : RatFunc k → Prop} (hgen : ∀ a, IsGen a → M a)
    (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → M a → M b → M (a * b)) (b : k[X]) (hb : b ≠ 0) :
    M (algebraMap k[X] (RatFunc k) b) := by
  revert hb
  refine UniqueFactorizationMonoid.induction_on_prime b (fun h => absurd rfl h) ?_ ?_
  · intro x hx _
    obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.mp hx
    exact hgen _ (Or.inl ⟨c, hc.ne_zero, rfl⟩)
  · intro x p hx hp ih _
    obtain ⟨h1, h2, h3⟩ := prime_eq_C_mul hp
    rw [h3, map_mul, map_mul]
    have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp.ne_zero
    exact hmul _ _ (mul_ne_zero h1.ne_zero h2.ne_zero) (j_ne_zero hx)
      (hmul _ _ h1.ne_zero h2.ne_zero (hgen _ h1) (hgen _ h2)) (ih hx)

lemma prodOne_poly_poly (hk : ringChar k ≠ 2) (a b : k[X]) (ha : a ≠ 0) (hb : b ≠ 0) :
    ProdOne (algebraMap k[X] (RatFunc k) a) (algebraMap k[X] (RatFunc k) b) := by
  refine poly_induction (M := fun a => ProdOne a (algebraMap k[X] (RatFunc k) b)) ?_
    (fun a a' ha ha' h h' => ProdOne.mul_left hk ha ha' (j_ne_zero hb) h h') a ha
  intro a hga
  exact poly_induction (M := fun b => ProdOne a b) (fun b hgb => prodOne_gen hk hga hgb)
    (fun b b' hb hb' h h' => ProdOne.mul_right hk hga.ne_zero hb hb' h h') b hb

lemma prodOne_all (hk : ringChar k ≠ 2) {a b : RatFunc k} (ha : a ≠ 0) (hb : b ≠ 0) : ProdOne a b := by
  have split : ∀ x : RatFunc k, x ≠ 0 → x = algebraMap k[X] (RatFunc k) x.num *
      (algebraMap k[X] (RatFunc k) x.denom)⁻¹ := fun x _ => by
    rw [← div_eq_mul_inv, RatFunc.num_div_denom]
  have hn : ∀ x : RatFunc k, x ≠ 0 → x.num ≠ 0 := fun x hx => RatFunc.num_ne_zero hx
  have hd : ∀ x : RatFunc k, x.denom ≠ 0 := fun x => x.denom_ne_zero
  -- first for polynomial `a`
  have hpoly : ∀ p : k[X], p ≠ 0 → ProdOne (algebraMap k[X] (RatFunc k) p) b := by
    intro p hp
    rw [split b hb]
    exact ProdOne.mul_right hk (j_ne_zero hp) (j_ne_zero (hn b hb)) (inv_ne_zero (j_ne_zero (hd b)))
      (prodOne_poly_poly hk p _ hp (hn b hb))
      ((prodOne_poly_poly hk p _ hp (hd b)).inv_right (j_ne_zero (hd b)))
  rw [split a ha]
  exact ProdOne.mul_left hk (j_ne_zero (hn a ha)) (inv_ne_zero (j_ne_zero (hd a))) hb
    (hpoly _ (hn a ha)) ((hpoly _ (hd a)).symm.inv_right (j_ne_zero (hd a))).symm

/-- **Hilbert reciprocity over $\mathbb{F}_q(t)$**, $q$ odd (O'Meara 71:18 for $F = \mathbb{F}_q(t)$): for
$a, b \in k(t)^\times$, $(a, b)_v = -1$ at only finitely many places $v$ of $k(t)$, and at an even number of them.
This proves the named input `HilbertReciprocity k`. *Proof:* see the module docstring (generators, local formulas,
quadratic reciprocity in $k[t]$). -/
@[kb "omeara1963" "§71, 71:18, p. 199 (Hilbert Reciprocity Law; F = F_q(t)) [unverified]; serre1973 Ch. III §2.1, Thm. 3 (proof for Q, transposed to F_q[t]) [unverified]"]
theorem hilbertReciprocity (hk : ringChar k ≠ 2) : HilbertReciprocity k :=
  ⟨fun _ _ ha hb => (prodOne_all hk ha hb).finite_even⟩

end Generators

end QuadFormsKB.RatFuncPlace
