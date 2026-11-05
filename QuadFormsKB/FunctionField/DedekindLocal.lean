/-
# Local facts at a finite place of a Dedekind domain (function field case)

The number field proofs of Hasse–Minkowski use a few facts at a finite place $\mathfrak{p}$ of
$\mathcal{O}_F$ that never use that $F$ is a number field: only that $\mathcal{O}_F$ is a Dedekind domain
with fraction field $F$ and that $F_{\mathfrak{p}}$ is the $\mathfrak{p}$-adic completion. They are restated
here for an arbitrary Dedekind domain $R$ with fraction field $K$ and a height-one prime $v$ of $R$,
so that they apply to $R = \mathbb{F}_q[t]$ (and to the ring of integers of any function field) as well
as to $R = \mathcal{O}_F$.

* `exists_sq_mod_of_near_sq`: an element of $R$ that is close to a square in $K_v$ is a square mod $v$
  (the proof of `SqLG.exists_sq_mod_of_isSquare` with $\mathcal{O}_F$ replaced by $R$);
* `exists_sq_mod_of_isSquare`: an element of $R$ that is a square in $K_v$ is a square mod $v$;
* `valuation_isSquare_of_isSquare`: a square of $K_v$ has square valuation;
* `intValuation_eq_exp_neg_one`: an element of $v \setminus v^2$ has valuation $\exp(-1)$;
* `exists_sq_mod_of_hilbert`: if $a \notin v$, $b \in v \setminus v^2$ and $(a, b)_{K_v} = 1$, then
  $a$ is a square mod $v$ (Serre, Ch. IV §3.2, the residue step of Legendre's theorem, which over
  $\mathbb{Q}$ is `HM3.isSquare_mod_of_hilbert`). Unlike the $\mathbb{Q}_p$ proof, this one does not use the
  explicit formula for the Hilbert symbol, and it holds in every characteristic.

Indices are 0-based.
-/
import Mathlib
import QuadFormsKB.Defs.Hilbert

open IsDedekindDomain WithZero

namespace QuadFormsKB.FF

/-- **Values below $1$ in $\mathbb{Z}_{(0)}$:** a nonzero $\gamma \in \mathbb{Z}^{\times}_{0}$ (multiplicative
notation, $\gamma = \exp(m)$) with $\gamma < 1$ satisfies $\gamma \le \exp(-1)$, since $m < 0$ forces
$m \le -1$. -/
theorem le_exp_neg_one_of_lt_one {γ : ℤᵐ⁰} (h0 : γ ≠ 0) (h : γ < 1) : γ ≤ exp (-1 : ℤ) := by
  rw [← exp_log h0] at h ⊢
  rw [← exp_zero, exp_lt_exp] at h
  rw [exp_le_exp]; omega

/-- **$\exp(-1)$ is not a square in $\mathbb{Z}^{\times}_{0}$:** no $w$ satisfies $w \cdot w = \exp(-1)$,
because $2m = -1$ has no integer solution. -/
theorem mul_self_ne_exp_neg_one (w : ℤᵐ⁰) : w * w ≠ exp (-1 : ℤ) := by
  intro h
  by_cases hw : w = 0
  · subst hw; rw [zero_mul] at h; exact exp_ne_zero h.symm
  rw [← exp_log hw, ← exp_add, exp_inj] at h
  omega

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- **The valuation of $K_v$ restricts to that of $K$:** for $x \in K$, the extended valuation of
$x \in K_v$ equals $v(x)$. -/
theorem valued_algebraMap (x : K) :
    Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion R]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

/-- **Elements near a square are squares mod $v$:** let $a \in R$ and $w \in K_v$ with $|w|_v \le 1$
and $|a - w^2|_v < 1$. Then $a \equiv r^2 \pmod v$ for some $r \in R$.

*Proof* (as in `SqLG.exists_sq_mod_of_isSquare`, with $\mathcal{O}_F$ replaced by $R$). Approximate $w$ by
$y \in K$ with $|w - y|_v < 1$ (density of $K$ in $K_v$); then $|y|_v \le 1$ and $|a - y^2|_v < 1$.
Write $y = b/s$ with $b, s \in R$, $s \notin v$, and replace $y$ by $r = t b$ where $t s \equiv 1
\pmod v$ ($R/v$ is a field). -/
theorem exists_sq_mod_of_near_sq (a : R) (w : v.adicCompletion K) (hw : Valued.v w ≤ 1)
    (h : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K a) - w ^ 2) < 1) :
    ∃ r : R, a - r ^ 2 ∈ v.asIdeal := by
  have key : ∀ y : K, v.valuation K y ≤ 1 → ∃ a s : R, s ∉ v.asIdeal ∧ y * algebraMap R K s =
      algebraMap R K a := by
    intro y hy
    have hy' : y ∈ HeightOneSpectrum.valuationSubringAtPrime K v := by
      rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]; exact hy
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl
      (⟨y, hy'⟩ : HeightOneSpectrum.valuationSubringAtPrime K v)
    have h2 := IsLocalization.mk'_spec (HeightOneSpectrum.valuationSubringAtPrime K v) a s
    simp only at h
    rw [h] at h2
    refine ⟨a, s, s.2, ?_⟩
    have h3 := congrArg Subtype.val h2
    exact h3
  have hval := valued_algebraMap (K := K) v
  obtain ⟨y, hy⟩ : ∃ y : K, Valued.v (w - algebraMap K _ y) < 1 := by
    have hn : {z : v.adicCompletion K | Valued.v (z - w) < 1} ∈ nhds w :=
      Valued.mem_nhds.mpr ⟨1, by simp⟩
    obtain ⟨_, h1, ⟨y, rfl⟩⟩ :=
      mem_closure_iff_nhds.mp (HeightOneSpectrum.denseRange_algebraMap K v w) _ hn
    refine ⟨y, ?_⟩
    rw [← Valuation.map_neg, neg_sub]; exact h1
  set y' := algebraMap K (v.adicCompletion K) y with hy'def
  have hvw : Valued.v y' ≤ 1 := by
    have : y' = w - (w - y') := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le hw hy.le)
  have hvy : v.valuation K y ≤ 1 := by rw [← hval]; exact hvw
  have hay : v.valuation K (algebraMap R K a - y ^ 2) < 1 := by
    rw [← hval, map_sub, map_pow, ← hy'def]
    have : algebraMap K (v.adicCompletion K) (algebraMap R K a) - y' ^ 2 =
        (algebraMap K (v.adicCompletion K) (algebraMap R K a) - w ^ 2) + (w - y') * (w + y') := by
      ring
    rw [this]
    apply Valuation.map_add_lt _ h
    rw [map_mul]
    have h3 : Valued.v (w + y') ≤ 1 := (Valuation.map_add _ _ _).trans (max_le hw hvw)
    calc Valued.v (w - y') * Valued.v (w + y') ≤ Valued.v (w - y') * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hy
  obtain ⟨b, s, hs, hys⟩ := key y hvy
  obtain ⟨t, i, hi, hti⟩ := Ideal.IsMaximal.exists_inv (v.isMaximal) hs
  refine ⟨t * b, ?_⟩
  rw [← v.valuation_lt_one_iff_mem (K := K)]
  have hi' : v.valuation K (algebraMap R K i) < 1 := (v.valuation_lt_one_iff_mem i).mpr hi
  have hyr : v.valuation K (y - algebraMap R K (t * b)) < 1 := by
    have : y - algebraMap R K (t * b) = y * algebraMap R K i := by
      have e : algebraMap R K t * algebraMap R K s + algebraMap R K i = 1 := by
        rw [← map_mul, ← map_add, hti, map_one]
      rw [map_mul]
      linear_combination (-y) * e + algebraMap R K t * hys
    rw [this, map_mul]
    calc v.valuation K y * v.valuation K (algebraMap R K i) ≤ 1 * v.valuation K (algebraMap R K i) := by
          gcongr
      _ < 1 := by rw [one_mul]; exact hi'
  have hyr2 : v.valuation K (y + algebraMap R K (t * b)) ≤ 1 :=
    (Valuation.map_add _ _ _).trans (max_le hvy (v.valuation_le_one _))
  have e2 : algebraMap R K (a - (t * b) ^ 2) = (algebraMap R K a - y ^ 2) +
      (y - algebraMap R K (t * b)) * (y + algebraMap R K (t * b)) := by
    rw [map_sub, map_pow]; ring
  change v.valuation K (algebraMap R K (a - (t * b) ^ 2)) < 1
  rw [e2]
  apply Valuation.map_add_lt _ hay
  rw [map_mul]
  calc v.valuation K (y - algebraMap R K (t * b)) * v.valuation K (y + algebraMap R K (t * b))
      ≤ v.valuation K (y - algebraMap R K (t * b)) * 1 := by gcongr
    _ < 1 := by rw [mul_one]; exact hyr

/-- **Squares in $K_v$ are squares mod $v$:** if $a \in R$ is a square in the completion $K_v$, then
$a \equiv r^2 \pmod v$ for some $r \in R$. (The generalization of `SqLG.exists_sq_mod_of_isSquare` from
$\mathcal{O}_F$ to any Dedekind domain; the hypothesis $\mathfrak{p} \nmid 2a$ there is not needed.) -/
@[kb "neukirch1999" "Ch. II §4 [unverified]"]
theorem exists_sq_mod_of_isSquare (a : R)
    (hsq : IsSquare (algebraMap K (v.adicCompletion K) (algebraMap R K a))) :
    ∃ r : R, a - r ^ 2 ∈ v.asIdeal := by
  obtain ⟨x, hx⟩ := hsq
  have hva : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K a)) ≤ 1 := by
    rw [valued_algebraMap]; exact v.valuation_le_one a
  have hvx : Valued.v x ≤ 1 := by
    by_contra hc
    have hc' : 1 < Valued.v x := lt_of_not_ge hc
    have : 1 < Valued.v x * Valued.v x := one_lt_mul hc'.le hc'
    rw [← map_mul, ← hx] at this
    exact absurd hva (not_le.mpr this)
  refine exists_sq_mod_of_near_sq v a x hvx ?_
  rw [hx, sq, sub_self, map_zero]; exact zero_lt_one

/-- **Squares of $K_v$ have square valuation:** if $x \in K$ is a square in $K_v$, then
$v(x) = w \cdot w$ for some $w \in \mathbb{Z}^{\times}_{0}$. -/
theorem valuation_isSquare_of_isSquare (x : K)
    (hsq : IsSquare (algebraMap K (v.adicCompletion K) x)) :
    ∃ w : ℤᵐ⁰, v.valuation K x = w * w := by
  obtain ⟨y, hy⟩ := hsq
  exact ⟨Valued.v y, by rw [← valued_algebraMap v, hy, map_mul]⟩

/-- **Simple zeros have valuation $\exp(-1)$:** if $d \in v$ and $d \notin v^2$, then
$v(d) = \exp(-1)$. -/
theorem intValuation_eq_exp_neg_one (d : R) (h1 : d ∈ v.asIdeal) (h2 : d ∉ v.asIdeal ^ 2) :
    v.intValuation d = exp (-1 : ℤ) := by
  have hd0 : d ≠ 0 := by rintro rfl; exact h2 (Submodule.zero_mem _)
  have hle : v.intValuation d ≤ exp (-(1 : ℕ) : ℤ) := (v.intValuation_le_pow_iff_mem d 1).mpr (by simpa using h1)
  have hnle : ¬ v.intValuation d ≤ exp (-(2 : ℕ) : ℤ) := fun h => h2 ((v.intValuation_le_pow_iff_mem d 2).mp h)
  have h0 : v.intValuation d ≠ 0 := v.intValuation_ne_zero d hd0
  rw [← exp_log h0] at hle hnle ⊢
  rw [exp_le_exp] at hle hnle
  rw [exp_inj]
  push_cast at hle hnle
  omega

/-- **Local solvability gives a residue square** (Serre, Ch. IV §3.2; over $\mathbb{Q}$ this is
`HM3.isSquare_mod_of_hilbert`): let $a, b \in R$ with $a \notin v$, $b \in v$, $b \notin v^2$. If the
Hilbert symbol $(a, b)_{K_v} = 1$, then $a \equiv r^2 \pmod v$ for some $r \in R$.

*Proof.* Take $(x, y, z) \ne 0$ in $K_v$ with $z^2 = a x^2 + b y^2$ and scale it so that
$\max(|x|, |y|, |z|) = 1$. If $|x| < 1$ then $|z^2| = |a x^2 + b y^2| < 1$, so $|z| < 1$ and $|y| = 1$;
then $|b y^2| = \exp(-1)$ while $|z^2 - a x^2| \le \exp(-2)$, a contradiction. So $|x| = 1$ and
$|a - (z/x)^2| = |b y^2 / x^2| < 1$ with $|z/x| \le 1$; apply `exists_sq_mod_of_near_sq`. -/
@[kb "serre1973" "Ch. IV §3.2 [unverified]; cassels1978 Ch. 6, Lemma 4.2, p. 79"]
theorem exists_sq_mod_of_hilbert (a b : R) (ha : a ∉ v.asIdeal) (hb1 : b ∈ v.asIdeal)
    (hb2 : b ∉ v.asIdeal ^ 2)
    (h : hilbertSymbol (v.adicCompletion K) (algebraMap K _ (algebraMap R K a))
      (algebraMap K _ (algebraMap R K b)) = 1) :
    ∃ r : R, a - r ^ 2 ∈ v.asIdeal := by
  set A := algebraMap K (v.adicCompletion K) (algebraMap R K a) with hA
  set B := algebraMap K (v.adicCompletion K) (algebraMap R K b) with hB
  have hvA : Valued.v A = 1 := by
    rw [hA, valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v a).mpr ha
  have hvB : Valued.v B = exp (-1 : ℤ) := by
    rw [hB, valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact intValuation_eq_exp_neg_one v b hb1 hb2
  unfold hilbertSymbol at h
  split_ifs at h with hex
  · obtain ⟨x, y, z, hne, he⟩ := hex
    -- the largest of |x|, |y|, |z|
    obtain ⟨m, hm0, hmx, hmy, hmz, hmem⟩ : ∃ m : v.adicCompletion K, m ≠ 0 ∧ Valued.v x ≤ Valued.v m ∧
        Valued.v y ≤ Valued.v m ∧ Valued.v z ≤ Valued.v m ∧ (m = x ∨ m = y ∨ m = z) := by
      by_cases hxy : Valued.v y ≤ Valued.v x
      · by_cases hxz : Valued.v z ≤ Valued.v x
        · refine ⟨x, ?_, le_rfl, hxy, hxz, Or.inl rfl⟩
          intro hx0
          apply hne
          have hy0 : y = 0 := by
            have := hxy; rw [hx0, map_zero] at this; exact (Valuation.zero_iff _).mp (le_antisymm this zero_le)
          have hz0 : z = 0 := by
            have := hxz; rw [hx0, map_zero] at this; exact (Valuation.zero_iff _).mp (le_antisymm this zero_le)
          simp [hx0, hy0, hz0]
        · have hxz' := (not_le.mp hxz).le
          refine ⟨z, ?_, hxz', hxy.trans hxz', le_rfl, Or.inr (Or.inr rfl)⟩
          intro hz0; rw [hz0, map_zero] at hxz; exact hxz zero_le
      · have hxy' := (not_le.mp hxy).le
        by_cases hyz : Valued.v z ≤ Valued.v y
        · refine ⟨y, ?_, hxy', le_rfl, hyz, Or.inr (Or.inl rfl)⟩
          intro hy0; rw [hy0, map_zero] at hxy; exact hxy zero_le
        · have hyz' := (not_le.mp hyz).le
          refine ⟨z, ?_, hxy'.trans hyz', hyz', le_rfl, Or.inr (Or.inr rfl)⟩
          intro hz0; rw [hz0, map_zero] at hyz; exact hyz zero_le
    have hvm : Valued.v m ≠ 0 := by simpa using hm0
    set x' := x / m with hx'
    set y' := y / m with hy'
    set z' := z / m with hz'
    have hx1 : Valued.v x' ≤ 1 := by
      simp only [x', map_div₀]; exact div_le_one_of_le₀ hmx zero_le
    have hy1 : Valued.v y' ≤ 1 := by
      simp only [y', map_div₀]; exact div_le_one_of_le₀ hmy zero_le
    have hz1 : Valued.v z' ≤ 1 := by
      simp only [z', map_div₀]; exact div_le_one_of_le₀ hmz zero_le
    have hmax : Valued.v x' = 1 ∨ Valued.v y' = 1 ∨ Valued.v z' = 1 := by
      rcases hmem with e | e | e
      · left; simp only [x', map_div₀, e]; exact div_self (e ▸ hvm)
      · right; left; simp only [y', map_div₀, e]; exact div_self (e ▸ hvm)
      · right; right; simp only [z', map_div₀, e]; exact div_self (e ▸ hvm)
    have he' : z' ^ 2 = A * x' ^ 2 + B * y' ^ 2 := by
      simp only [x', y', z']
      field_simp
      linear_combination he
    have hBy : Valued.v (B * y' ^ 2) ≤ exp (-1 : ℤ) := by
      rw [map_mul, hvB, map_pow]
      calc exp (-1 : ℤ) * Valued.v y' ^ 2 ≤ exp (-1 : ℤ) * 1 := by
            gcongr; exact pow_le_one₀ zero_le hy1
        _ = exp (-1 : ℤ) := mul_one _
    have hexp : exp (-1 : ℤ) < (1 : ℤᵐ⁰) := by rw [← exp_zero, exp_lt_exp]; norm_num
    by_cases hx1' : Valued.v x' = 1
    · have hx0 : x' ≠ 0 := by intro h0; rw [h0, map_zero] at hx1'; exact zero_ne_one hx1'
      refine exists_sq_mod_of_near_sq v a (z' / x') ?_ ?_
      · rw [map_div₀, hx1', div_one]; exact hz1
      · have : A - (z' / x') ^ 2 = -(B * y' ^ 2) / x' ^ 2 := by
          rw [div_pow, he']; field_simp; ring
        rw [this, map_div₀, Valuation.map_neg, map_pow, hx1', one_pow, div_one]
        exact lt_of_le_of_lt hBy hexp
    · exfalso
      have hxlt : Valued.v x' < 1 := lt_of_le_of_ne hx1 hx1'
      have hAx : Valued.v (A * x' ^ 2) < 1 := by
        rw [map_mul, hvA, one_mul, map_pow]; exact pow_lt_one₀ zero_le hxlt (by norm_num)
      have hzlt : Valued.v z' < 1 := by
        have h2 : Valued.v (z' ^ 2) < 1 := by
          rw [he']; exact Valuation.map_add_lt _ hAx (lt_of_le_of_lt hBy hexp)
        rw [map_pow] at h2
        by_contra hc
        have : Valued.v z' = 1 := le_antisymm hz1 (not_lt.mp hc)
        rw [this, one_pow] at h2; exact lt_irrefl _ h2
      have hy1' : Valued.v y' = 1 := by
        rcases hmax with h | h | h
        · exact absurd h hx1'
        · exact h
        · exact absurd h hzlt.ne
      have hBy' : Valued.v (B * y' ^ 2) = exp (-1 : ℤ) := by
        rw [map_mul, hvB, map_pow, hy1', one_pow, mul_one]
      have hsmall : ∀ u : v.adicCompletion K, Valued.v u < 1 → Valued.v (u ^ 2) ≤ exp (-2 : ℤ) := by
        intro u hu
        rw [map_pow]
        by_cases hu0 : Valued.v u = 0
        · rw [hu0]; simp
        have := le_exp_neg_one_of_lt_one hu0 hu
        calc Valued.v u ^ 2 ≤ exp (-1 : ℤ) ^ 2 := by gcongr
          _ = exp (-2 : ℤ) := by rw [sq, ← exp_add]; norm_num
      have hAx2 : Valued.v (A * x' ^ 2) ≤ exp (-2 : ℤ) := by
        rw [map_mul, hvA, one_mul]; exact hsmall x' hxlt
      have hdiff : Valued.v (z' ^ 2 - A * x' ^ 2) ≤ exp (-2 : ℤ) :=
        (Valuation.map_sub _ _ _).trans (max_le (hsmall z' hzlt) hAx2)
      have : z' ^ 2 - A * x' ^ 2 = B * y' ^ 2 := by rw [he']; ring
      rw [this, hBy', exp_le_exp] at hdiff
      norm_num at hdiff

end QuadFormsKB.FF
