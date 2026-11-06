/-
# Legendre's theorem over $\mathbb{F}_q(t)$: the Hasse norm theorem for quadratic extensions

**Theorem** (`RatFuncPlace.hilbert_eq_one_of_finite`). Let $k$ be a finite field of odd characteristic
and $a, b \in k(t)^\times$. If the local Hilbert symbol $(a, b)_P = 1$ at every finite place $P$ of
$k(t)$, then $(a, b)_{k(t)} = 1$, i.e. $z^2 = a x^2 + b y^2$ has a nonzero solution in $k(t)$. With the
place at infinity included this is O'Meara's Hasse Norm Theorem 65:23 for $F = k(t)$ and the
quadratic extension $F(\sqrt a)$ (`RatFuncPlace.hilbert_eq_one_of_everywhere`); the place at infinity is
not needed, which is the function field shadow of Hilbert reciprocity.

*Proof* (Legendre's descent, as over $\mathbb{Q}$ in Serre, Ch. IV §3.2 and Cassels, Ch. 6, Thm. 4.1;
O'Meara's footnote to 66:1 says the binary and ternary cases over $\mathbb{Q}$ "can be obtained by
elementary methods"; the same methods work over $k[t]$ with the degree in place of the absolute value).
The steps are those of `HM3.hilbert_rat_eq_one_of_everywhere`:

1. reduce to squarefree polynomials $a, b \in k[t]$ with $\deg a \le \deg b$;
2. if $\deg b = 0$, then $a, b \in k^\times$ and the conic $a x^2 + b y^2 = 1$ has a point over the finite
   field $k$ (Chevalley; Mathlib's `FiniteField.exists_root_sum_quadratic`);
3. otherwise $a$ is a square modulo every irreducible $P \mid b$ (`FF.exists_sq_mod_of_hilbert` at
   $P \nmid a$), hence modulo $b$ (Chinese remainder theorem); take $t$ with $t^2 \equiv a \pmod b$ and
   $\deg t < \deg b$, write $t^2 - a = b b'$; then $\deg b' < \deg b$, $(a, b) = (a, b')$ globally and at
   every place (since $b b'$ is a norm from $F(\sqrt a)$), and induct on $\deg a + \deg b$.

Indices are 0-based.
-/
import QuadFormsKB.FunctionField.RatFuncPlace
import QuadFormsKB.Equiv.Hilbert

open IsDedekindDomain Polynomial

namespace QuadFormsKB.FF

/-! ### Hilbert symbol identities over an arbitrary field -/

/-- The Hilbert symbol is $1$ iff the conic $z^2 = a x^2 + b y^2$ has a nonzero point. -/
theorem hilbertSymbol_eq_one_iff (K : Type*) [Field K] (a b : K) :
    hilbertSymbol K a b = 1 ↔ ∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2 := by
  unfold hilbertSymbol
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by norm_num) h

/-- **Square factors do not matter:** $(a, b c^2)_K = 1 \iff (a, b)_K = 1$ for $c \ne 0$. -/
theorem hilbertSymbol_mul_sq_right_eq_one_iff (K : Type*) [Field K] (a b c : K) (hc : c ≠ 0) :
    hilbertSymbol K a (b * c ^ 2) = 1 ↔ hilbertSymbol K a b = 1 := by
  rw [hilbertSymbol_eq_one_iff, hilbertSymbol_eq_one_iff]
  constructor
  · rintro ⟨x, y, z, hne, he⟩
    refine ⟨x, y * c, z, ?_, by rw [he]; ring⟩
    intro h0
    apply hne
    simp only [Prod.mk_eq_zero, mul_eq_zero] at h0 ⊢
    tauto
  · rintro ⟨x, y, z, hne, he⟩
    refine ⟨x, y / c, z, ?_, by rw [he]; field_simp⟩
    intro h0
    apply hne
    simp only [Prod.mk_eq_zero, div_eq_zero_iff] at h0 ⊢
    tauto

/-- **Norms are multiplicative (Legendre's step):** if $b b' = t^2 - a$ with $b' \ne 0$ and
$(a, b')_K = 1$, then $(a, b)_K = 1$. (From a point $(x, y, z)$ of $z^2 = a x^2 + b' y^2$, the point
$(z + x t,\ b' y,\ z t + a x)$ lies on $Z^2 = a X^2 + b Y^2$.) -/
theorem hilbertSymbol_eq_one_of_mul (K : Type*) [Field K] (a b b' t : K) (hb' : b' ≠ 0)
    (he : b * b' = t ^ 2 - a) (h : hilbertSymbol K a b' = 1) : hilbertSymbol K a b = 1 := by
  rw [hilbertSymbol_eq_one_iff] at h ⊢
  obtain ⟨x, y, z, hne, hz⟩ := h
  by_cases hy : y = 0
  · subst hy
    exact ⟨x, 0, z, hne, by rw [hz]; ring⟩
  · refine ⟨z + x * t, b' * y, z * t + a * x, ?_, ?_⟩
    · intro h0
      simp only [Prod.mk_eq_zero] at h0
      exact mul_ne_zero hb' hy h0.2.1
    · linear_combination (t ^ 2 - a) * hz - b' * y ^ 2 * he

/-! ### Polynomial lemmas -/

variable {k : Type} [Field k]

/-- **Chinese remainder theorem for squares:** if $b \in k[t]$ is squarefree and $a$ is a square
modulo every irreducible factor $P$ of $b$, then $a \equiv t^2 \pmod b$ for some $t$. -/
theorem exists_sq_mod_squarefree (a b : k[X]) (hb : Squarefree b)
    (h : ∀ P : k[X], Irreducible P → P ∣ b → ∃ r : k[X], P ∣ r ^ 2 - a) :
    ∃ t : k[X], b ∣ t ^ 2 - a := by
  induction b using WfDvdMonoid.induction_on_irreducible with
  | zero => exact absurd hb not_squarefree_zero
  | unit u hu => exact ⟨0, hu.dvd⟩
  | mul z p hz hp ih =>
    have hsz : Squarefree z := hb.of_mul_right
    have hpz : ¬ p ∣ z := by
      rintro ⟨w, rfl⟩
      exact hp.not_isUnit (hb p ⟨w, by ring⟩)
    obtain ⟨t1, h1⟩ := ih hsz (fun P hP hPz => h P hP (dvd_mul_of_dvd_right hPz p))
    obtain ⟨t2, h2⟩ := h p hp (dvd_mul_right p z)
    have hc : IsCoprime p z := (Irreducible.coprime_iff_not_dvd hp).mpr hpz
    obtain ⟨u, v, huv⟩ := hc
    refine ⟨t2 * v * z + t1 * u * p, ?_⟩
    apply IsCoprime.mul_dvd ⟨u, v, huv⟩
    · have : (t2 * v * z + t1 * u * p) ^ 2 - a =
          (t2 ^ 2 - a) + p * (u * (t1 - t2) * ((t2 * v * z + t1 * u * p) + t2)) := by
        linear_combination ((t2 * v * z + t1 * u * p) + t2) * t2 * huv
      rw [this]; exact dvd_add h2 (dvd_mul_right _ _)
    · have : (t2 * v * z + t1 * u * p) ^ 2 - a =
          (t1 ^ 2 - a) + z * (v * (t2 - t1) * ((t2 * v * z + t1 * u * p) + t1)) := by
        linear_combination ((t2 * v * z + t1 * u * p) + t1) * t1 * huv
      rw [this]; exact dvd_add h1 (dvd_mul_right _ _)

/-- **A small square root mod $b$:** if $b \mid t^2 - a$ and $\deg b \ge 1$, then $b \mid t'^2 - a$ for some
$t'$ with $\deg t' < \deg b$ (take $t' = t \bmod b$). -/
theorem exists_sq_mod_small (a b t : k[X]) (hb : 0 < b.natDegree) (ht : b ∣ t ^ 2 - a) :
    ∃ t' : k[X], b ∣ t' ^ 2 - a ∧ t'.natDegree < b.natDegree := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  refine ⟨t % b, ?_, ?_⟩
  · have e : t % b = t - b * (t / b) := EuclideanDomain.mod_eq_sub_mul_div t b
    have : (t % b) ^ 2 - a = (t ^ 2 - a) + b * ((t / b) * (b * (t / b) - 2 * t)) := by
      rw [e]; ring
    rw [this]; exact dvd_add ht (dvd_mul_right _ _)
  · by_cases h0 : t % b = 0
    · rw [h0, natDegree_zero]; exact hb
    · exact natDegree_lt_natDegree h0 (degree_mod_lt t hb0)

/-- **Squarefree part:** every nonzero $f \in k[t]$ is $e^2 d$ with $d$ squarefree, $e \ne 0$ and
$\deg d \le \deg f$. -/
theorem exists_sq_mul_squarefree_natDegree (f : k[X]) (hf : f ≠ 0) :
    ∃ e d : k[X], e ≠ 0 ∧ Squarefree d ∧ f = e ^ 2 * d ∧ d.natDegree ≤ f.natDegree := by
  obtain ⟨e, d, hed, hd⟩ := exists_sq_mul_squarefree f
  have he : e ≠ 0 := by rintro rfl; rw [zero_pow two_ne_zero, zero_mul] at hed; exact hf hed.symm
  have hd0 : d ≠ 0 := by rintro rfl; rw [mul_zero] at hed; exact hf hed.symm
  refine ⟨e, d, he, hd, hed.symm, ?_⟩
  rw [← hed, natDegree_mul (pow_ne_zero 2 he) hd0]
  omega

/-- **Squarefree representatives in $k(t)$:** every $a \in k(t)^\times$ is $d c^2$ with $d \in k[t]$
squarefree and $c \in k(t)^\times$. -/
theorem exists_squarefree_mul_sq (a : RatFunc k) (ha : a ≠ 0) :
    ∃ (d : k[X]) (c : RatFunc k), Squarefree d ∧ c ≠ 0 ∧ a = algebraMap k[X] (RatFunc k) d * c ^ 2 := by
  have hq : a.denom ≠ 0 := RatFunc.denom_ne_zero a
  have hp : a.num ≠ 0 := by simpa using ha
  have hpq : algebraMap k[X] (RatFunc k) a.num / algebraMap k[X] (RatFunc k) a.denom = a :=
    RatFunc.num_div_denom a
  have inj := IsFractionRing.injective k[X] (RatFunc k)
  obtain ⟨e, d, he, hd, hed, -⟩ := exists_sq_mul_squarefree_natDegree (a.num * a.denom)
    (mul_ne_zero hp hq)
  have hqK : algebraMap k[X] (RatFunc k) a.denom ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ inj]; exact hq
  have heK : algebraMap k[X] (RatFunc k) e ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ inj]; exact he
  refine ⟨d, algebraMap k[X] (RatFunc k) e / algebraMap k[X] (RatFunc k) a.denom, hd,
    div_ne_zero heK hqK, ?_⟩
  conv_lhs => rw [← hpq]
  have : algebraMap k[X] (RatFunc k) a.num * algebraMap k[X] (RatFunc k) a.denom =
      algebraMap k[X] (RatFunc k) e ^ 2 * algebraMap k[X] (RatFunc k) d := by
    rw [← map_mul, hed, map_mul, map_pow]
  field_simp
  linear_combination this

end QuadFormsKB.FF

namespace QuadFormsKB.RatFuncPlace

open FF

variable {k : Type} [Field k] [Fintype k]

/-- **The Hasse norm theorem over $\mathbb{F}_q(t)$, finite places only** (Legendre's theorem over
$k[t]$): for a finite field $k$ of odd characteristic and $a, b \in k(t)^\times$, if
$(a, b)_P = 1$ at every finite place $P$, then $(a, b)_{k(t)} = 1$. See the module docstring for the
proof. -/
@[kb "omeara1963" "§65D, 65:23, p. 186 (Hasse Norm Theorem, F = k(t)); serre1973 Ch. IV §3.2 (descent) [unverified]; cassels1978 Ch. 6, Thm. 4.1, p. 80 (Legendre)"]
theorem hilbert_eq_one_of_finite (hk : ringChar k ≠ 2) (a b : RatFunc k) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ v : HeightOneSpectrum k[X], (RatFuncPlace.finite v).hilbert a b = 1) :
    hilbertSymbol (RatFunc k) a b = 1 := by
  classical
  set φ := algebraMap k[X] (RatFunc k) with hφ
  have inj : Function.Injective φ := IsFractionRing.injective k[X] (RatFunc k)
  have hφ0 : ∀ f : k[X], f ≠ 0 → φ f ≠ 0 := fun f hf => by rw [Ne, map_eq_zero_iff _ inj]; exact hf
  -- local versions of the identities
  have hpL : ∀ (v : HeightOneSpectrum k[X]) (x y y' s : RatFunc k), y ≠ 0 → y' * y = s ^ 2 - x →
      (RatFuncPlace.finite v).hilbert x y = 1 → (RatFuncPlace.finite v).hilbert x y' = 1 := by
    intro v x y y' s hy he hh
    simp only [RatFuncPlace.hilbert] at hh ⊢
    refine hilbertSymbol_eq_one_of_mul _ _ _ _ (algebraMap _ _ s) ?_ ?_ hh
    · rw [Ne, map_eq_zero_iff _ (algebraMap (RatFunc k) _).injective]; exact hy
    · rw [← map_mul, he, map_sub, map_pow]
  have hpSq : ∀ (v : HeightOneSpectrum k[X]) (x y c : RatFunc k), c ≠ 0 →
      ((RatFuncPlace.finite v).hilbert x (y * c ^ 2) = 1 ↔ (RatFuncPlace.finite v).hilbert x y = 1) := by
    intro v x y c hc
    simp only [RatFuncPlace.hilbert, map_mul, map_pow]
    exact hilbertSymbol_mul_sq_right_eq_one_iff _ _ _ _
      (by rw [Ne, map_eq_zero_iff _ (algebraMap (RatFunc k) _).injective]; exact hc)
  have hpC : ∀ (v : HeightOneSpectrum k[X]) (x y : RatFunc k),
      (RatFuncPlace.finite v).hilbert x y = (RatFuncPlace.finite v).hilbert y x := by
    intro v x y
    exact hilbertSymbol_comm _ _ _
  -- the residue step
  have hres : ∀ (a b : k[X]) (P : k[X]), Irreducible P → Squarefree b → P ∣ b →
      (∀ v : HeightOneSpectrum k[X], (RatFuncPlace.finite v).hilbert (φ a) (φ b) = 1) →
      ∃ r : k[X], P ∣ r ^ 2 - a := by
    intro a b P hP hsb hPb hloc
    by_cases hPa : P ∣ a
    · exact ⟨0, by simpa using hPa⟩
    set v := RatFuncPlace.ofIrreducible P hP
    have h1 : a ∉ v.asIdeal := by
      rw [ofIrreducible_asIdeal, Ideal.mem_span_singleton]; exact hPa
    have h2 : b ∈ v.asIdeal := by
      rw [ofIrreducible_asIdeal, Ideal.mem_span_singleton]; exact hPb
    have h3 : b ∉ v.asIdeal ^ 2 := by
      rw [ofIrreducible_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      intro hd
      exact hP.not_isUnit (hsb P (by rw [← sq]; exact hd))
    obtain ⟨r, hr⟩ := FF.exists_sq_mod_of_hilbert v a b h1 h2 h3 (hloc v)
    refine ⟨r, ?_⟩
    rw [ofIrreducible_asIdeal, Ideal.mem_span_singleton] at hr
    have : r ^ 2 - a = -(a - r ^ 2) := by ring
    rw [this]; exact (dvd_neg).mpr hr
  -- the base case: a conic over a finite field has a point
  have hbase : ∀ α β : k, α ≠ 0 → β ≠ 0 → hilbertSymbol (RatFunc k) (φ (C α)) (φ (C β)) = 1 := by
    intro α β hα hβ
    have hodd : Fintype.card k % 2 = 1 := FiniteField.odd_card_of_char_ne_two hk
    obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic (f := C α * X ^ 2)
      (g := C β * X ^ 2 - 1) (by rw [degree_C_mul_X_pow 2 hα]; rfl)
      (by
        rw [degree_sub_eq_left_of_degree_lt] <;> rw [degree_C_mul_X_pow 2 hβ]
        · rfl
        · rw [degree_one]; norm_num) hodd
    simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one] at hxy
    rw [hilbertSymbol_eq_one_iff]
    refine ⟨φ (C x), φ (C y), 1, by simp, ?_⟩
    simp only [← map_pow, ← map_mul, ← map_add, ← C_pow, ← C_mul, ← C_add, one_pow]
    rw [show α * x ^ 2 + β * y ^ 2 = 1 by linear_combination hxy, C_1, map_one]
  -- the descent
  have main : ∀ N : ℕ, ∀ a b : k[X], Squarefree a → Squarefree b →
      a.natDegree + b.natDegree = N →
      (∀ v : HeightOneSpectrum k[X], (RatFuncPlace.finite v).hilbert (φ a) (φ b) = 1) →
      hilbertSymbol (RatFunc k) (φ a) (φ b) = 1 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    have key : ∀ a b : k[X], Squarefree a → Squarefree b → a.natDegree + b.natDegree = N →
        a.natDegree ≤ b.natDegree →
        (∀ v : HeightOneSpectrum k[X], (RatFuncPlace.finite v).hilbert (φ a) (φ b) = 1) →
        hilbertSymbol (RatFunc k) (φ a) (φ b) = 1 := by
      intro a b hsa hsb hN hab hloc
      have ha0 : a ≠ 0 := by rintro rfl; exact not_squarefree_zero hsa
      have hb0 : b ≠ 0 := by rintro rfl; exact not_squarefree_zero hsb
      by_cases hb1 : b.natDegree = 0
      · rw [natDegree_eq_zero] at hb1
        obtain ⟨β, rfl⟩ := hb1
        have ha1 : a.natDegree = 0 := by
          have := hab; rw [natDegree_C] at this; omega
        rw [natDegree_eq_zero] at ha1
        obtain ⟨α, rfl⟩ := ha1
        exact hbase α β (by rintro rfl; simp at ha0) (by rintro rfl; simp at hb0)
      · have hbpos : 0 < b.natDegree := Nat.pos_of_ne_zero hb1
        obtain ⟨t0, ht0⟩ := exists_sq_mod_squarefree a b hsb
          (fun P hP hPb => hres a b P hP hsb hPb hloc)
        obtain ⟨t, ht, htb⟩ := exists_sq_mod_small a b t0 hbpos ht0
        obtain ⟨b', hb'⟩ := ht
        by_cases hb'0 : b' = 0
        · rw [hilbertSymbol_eq_one_iff]
          have : t ^ 2 = a := by rw [hb'0, mul_zero, sub_eq_zero] at hb'; exact hb'
          refine ⟨1, 0, φ t, by simp, ?_⟩
          rw [← map_pow, this]; ring
        · obtain ⟨e, m, he, hm, hbm, hmle⟩ := exists_sq_mul_squarefree_natDegree b' hb'0
          have hlt : b'.natDegree < b.natDegree := by
            have h1 : (b * b').natDegree = b.natDegree + b'.natDegree := natDegree_mul hb0 hb'0
            have h2 : (t ^ 2 - a).natDegree ≤ max (t ^ 2).natDegree a.natDegree := natDegree_sub_le _ _
            have h3 : (t ^ 2).natDegree ≤ 2 * t.natDegree := by
              have := natDegree_pow_le (p := t) (n := 2); omega
            have h4 : (b * b').natDegree = (t ^ 2 - a).natDegree := by rw [← hb']
            omega
          have hcast : φ m * φ e ^ 2 = φ b' := by rw [hbm, map_mul, map_pow]; ring
          have IH := ih (a.natDegree + m.natDegree) (by omega) a m hsa hm rfl (by
            intro v
            rw [← hpSq v _ _ (φ e) (hφ0 e he), hcast]
            exact hpL v (φ a) (φ b) (φ b') (φ t) (hφ0 b hb0)
              (by rw [mul_comm, ← map_mul, ← hb', map_sub, map_pow]) (hloc v))
          have h2 : hilbertSymbol (RatFunc k) (φ a) (φ b') = 1 := by
            rw [← hcast, hilbertSymbol_mul_sq_right_eq_one_iff _ _ _ _ (hφ0 e he)]
            exact IH
          exact hilbertSymbol_eq_one_of_mul _ _ _ (φ b') (φ t) (hφ0 b' hb'0)
            (by rw [← map_mul, ← hb', map_sub, map_pow]) h2
    intro a b hsa hsb hN hloc
    rcases le_total a.natDegree b.natDegree with hle | hle
    · exact key a b hsa hsb hN hle hloc
    · rw [hilbertSymbol_comm]
      exact key b a hsb hsa (by omega) hle (fun v => by rw [hpC]; exact hloc v)
  obtain ⟨m1, c1, hm1, hc1, rfl⟩ := FF.exists_squarefree_mul_sq a ha
  obtain ⟨m2, c2, hm2, hc2, rfl⟩ := FF.exists_squarefree_mul_sq b hb
  have hloc : ∀ v : HeightOneSpectrum k[X], (RatFuncPlace.finite v).hilbert (φ m1) (φ m2) = 1 := by
    intro v
    have := h v
    rw [hpSq v _ _ _ hc2, hpC, hpSq v _ _ _ hc1, hpC] at this
    exact this
  have := main _ m1 m2 hm1 hm2 rfl hloc
  rw [hilbertSymbol_comm, ← hilbertSymbol_mul_sq_right_eq_one_iff.{0} (RatFunc k) _ _ c1 hc1] at this
  rw [hilbertSymbol_comm] at this
  rw [← hilbertSymbol_mul_sq_right_eq_one_iff.{0} (RatFunc k) _ _ c2 hc2] at this
  exact this

/-- **The Hasse norm theorem for $\mathbb{F}_q(t)$** (O'Meara 65:23 for $F = \mathbb{F}_q(t)$, $q$ odd): if
$(a, b)_v = 1$ at every place $v$ of $k(t)$, then $(a, b)_{k(t)} = 1$. (The place at infinity is not
needed: `hilbert_eq_one_of_finite`.) -/
@[kb "omeara1963" "§65D, 65:23, p. 186 (Hasse Norm Theorem, F = k(t))"]
theorem hilbert_eq_one_of_everywhere (hk : ringChar k ≠ 2) (a b : RatFunc k) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ v : RatFuncPlace k, v.hilbert a b = 1) : hilbertSymbol (RatFunc k) a b = 1 :=
  hilbert_eq_one_of_finite hk a b ha hb (fun v => h (.finite v))

end QuadFormsKB.RatFuncPlace
