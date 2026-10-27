/-
# Hasse–Minkowski for ternary forms: the blueprint (Serre, *A Course in Arithmetic*, IV §3.2)

Serre's proof of the case $n = 3$, broken into lemmas:

1. square classes: $(a c^2, b)_K = (a, b)_K$; every $a \in \mathbb{Q}^\times$ is $m c^2$, $m$ a
   squarefree integer;
2. local $\Rightarrow$ residue: $(a,b)_p = 1$, $p \mid b$, $p \nmid a$ $\Rightarrow$ $a$ is a square mod $p$;
3. CRT: $a$ a square mod every prime of squarefree $b$ $\Rightarrow$ $a \equiv t^2 \pmod b$,
   $2|t| \le |b|$;
4. **Legendre's theorem / the descent:** $(a,b)_v = 1$ at every place $\Rightarrow$
   $(a,b)_{\mathbb{Q}} = 1$, by induction on $|a| + |b|$;
5. reduction of a nondegenerate ternary form to $\langle 1, -a, -b \rangle$: diagonalization over
   $\mathbb{Q}$, isotropy invariant under isometry, scaling and base change.

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Equiv.Hilbert
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal

namespace QuadFormsKB.HM3

open RatPlace

variable {n : ℕ}

/-! ### 1. Square classes -/

/-- **The Hilbert symbol only sees square classes:** for $c \ne 0$ in a field $K$,
$(a c^2, b)_K = (a, b)_K$. -/
@[kb "serre1973" "Ch. III §1.1, Prop. 2 [unverified]"]
theorem hilbertSymbol_mul_sq_left (K : Type*) [Field K] (a b c : K) (hc : c ≠ 0) :
    hilbertSymbol K (a * c ^ 2) b = hilbertSymbol K a b := by
  unfold QuadFormsKB.hilbertSymbol
  have key : (∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = a * c ^ 2 * x ^ 2 + b * y ^ 2) ↔
      (∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2) := by
    constructor
    · rintro ⟨x, y, z, hne, h⟩
      refine ⟨c * x, y, z, ?_, ?_⟩
      · intro h0
        apply hne
        simp only [Prod.mk_eq_zero, mul_eq_zero] at h0 ⊢
        tauto
      · rw [h]; ring
    · rintro ⟨x, y, z, hne, h⟩
      refine ⟨x / c, y, z, ?_, ?_⟩
      · intro h0
        apply hne
        simp only [Prod.mk_eq_zero, div_eq_zero_iff] at h0 ⊢
        tauto
      · rw [h]; field_simp
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (key.mp h1) h2
  · exact absurd (key.mpr h2) h1
  · rfl

/-- **Squarefree representatives:** every $a \in \mathbb{Q}^\times$ is $m c^2$ with $m$ a
squarefree integer and $c \in \mathbb{Q}^\times$. -/
@[kb "serre1973" "Ch. IV §3.2 [unverified]; cassels1978 Ch. 6, Lemma 4.1, p. 78"]
theorem exists_squarefree_mul_sq (a : ℚ) (ha : a ≠ 0) :
    ∃ (m : ℤ) (c : ℚ), Squarefree m ∧ c ≠ 0 ∧ a = m * c ^ 2 := by
  have hN : a.num * a.den ≠ 0 := mul_ne_zero (Rat.num_ne_zero.mpr ha) (by exact_mod_cast a.den_nz)
  obtain ⟨s, b, hs, hb, hsb, hsq⟩ := Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.mpr hN)
  refine ⟨(a.num * a.den).sign * s, (b : ℚ) / a.den, ?_, ?_, ?_⟩
  · have hs' : Squarefree (s : ℤ) := Int.squarefree_natCast.mpr hsq
    rcases lt_or_gt_of_ne hN with h | h
    · rw [Int.sign_eq_neg_one_of_neg h]
      rw [Int.squarefree_natAbs.symm]; simpa using hsq
    · rw [Int.sign_eq_one_of_pos h]; simpa using hs'
  · have : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
    have : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    positivity
  · have hd : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
    have h1 : ((a.num * a.den : ℤ) : ℚ) = (a.num * a.den).sign * ((b : ℚ) ^ 2 * s) := by
      have := Int.sign_mul_natAbs (a.num * a.den)
      rw [← hsb] at this
      exact_mod_cast this.symm
    conv_lhs => rw [← Rat.num_div_den a]
    rw [div_pow]
    field_simp
    push_cast at h1 ⊢
    linear_combination h1

/-! ### 2. Local ⇒ residue -/

/-- **Local solvability gives a residue square:** for integers $a, b$ with $b$ squarefree and a
prime $p \mid b$, $p \nmid a$: if $(a,b)_p = 1$ then $a$ is a square mod $p$. (For odd $p$ the
explicit formula gives $(a,b)_p = \left(\frac{a}{p}\right)$; for $p = 2$ every odd residue is a
square.) -/
@[kb "serre1973" "Ch. IV §3.2 [unverified]; cassels1978 Ch. 6, Lemma 4.2, p. 79"]
theorem isSquare_mod_of_hilbert (a b : ℤ) (p : ℕ) [hp : Fact p.Prime] (hb : Squarefree b)
    (hpb : (p : ℤ) ∣ b) (hpa : ¬ (p : ℤ) ∣ a)
    (h : (RatPlace.finite ⟨p, hp.out⟩).hilbert a b = 1) :
    IsSquare ((a : ZMod p)) := by
  by_cases hp2 : p = 2
  · subst hp2
    generalize (a : ZMod 2) = x
    fin_cases x
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  obtain ⟨c, rfl⟩ := hpb
  have hpc : ¬ (p : ℤ) ∣ c := by
    rintro ⟨d, rfl⟩
    have := hb p ⟨d, by ring⟩
    have h1 := Int.isUnit_iff.mp this
    have h2 : (2:ℤ) ≤ p := by exact_mod_cast hp.out.two_le
    omega
  have unitOf : ∀ m : ℤ, ¬ (p : ℤ) ∣ m → IsUnit (m : ℤ_[p]) := by
    intro m hm
    rw [PadicInt.isUnit_iff]
    have := PadicInt.norm_int_lt_one_iff_dvd (p := p) m
    have h3 := PadicInt.norm_le_one (m : ℤ_[p])
    by_contra hne
    exact hm (this.mp (lt_of_le_of_ne h3 hne))
  obtain ⟨u, hu⟩ := unitOf a hpa
  obtain ⟨v, hv⟩ := unitOf c hpc
  have key := HilbertLocal.hilbertSymbol_odd_formula hp2 0 1 u v
  have ea : ((p:ℚ_[p]) ^ 0 * ((u : ℤ_[p]) : ℚ_[p])) = ((a : ℚ) : ℚ_[p]) := by
    rw [hu]; simp
  have eb : ((p:ℚ_[p]) ^ 1 * ((v : ℤ_[p]) : ℚ_[p])) = (((p * c : ℤ) : ℚ) : ℚ_[p]) := by
    rw [hv]; simp
  rw [ea, eb] at key
  have h' : hilbertSymbol ℚ_[p] (((a : ℚ) : ℚ_[p])) (((p * c : ℤ) : ℚ) : ℚ_[p]) = 1 := h
  rw [h'] at key
  simp [HilbertLocal.unitChar] at key
  rw [hu] at key
  simp at key
  have ha0 : (a : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact (quadraticChar_one_iff_isSquare ha0).mp key.symm

/-! ### 3. Chinese remainder theorem -/

/-- **Square mod a squarefree modulus, with a small root:** if $b \ne 0$ is squarefree and $a$ is
a square mod every prime $p \mid b$, then $a \equiv t^2 \pmod b$ for some $t$ with
$2|t| \le |b|$. -/
@[kb "serre1973" "Ch. IV §3.2 [unverified]; cassels1978 Ch. 6, Lemma 4.2, p. 79"]
theorem exists_sq_mod_small (a b : ℤ) (hb0 : b ≠ 0) (hb : Squarefree b)
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ b → IsSquare ((a : ZMod p))) :
    ∃ t : ℤ, b ∣ t ^ 2 - a ∧ 2 * |t| ≤ |b| := by
  have key : ∀ n : ℕ, Squarefree n → (∀ p : ℕ, p.Prime → p ∣ n → IsSquare ((a : ZMod p))) →
      IsSquare ((a : ZMod n)) := by
    intro n
    induction n using Nat.recOnPrimeCoprime with
    | zero => intro h0; exact absurd h0 not_squarefree_zero
    | prime_pow p k hp =>
      intro hsq hd
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; rw [pow_zero]; exact ⟨a, Subsingleton.elim _ _⟩
      · have := (Nat.squarefree_pow_iff hp.ne_one hk.ne').1 hsq
        rw [this.2, pow_one] at hd ⊢
        exact hd p hp dvd_rfl
    | coprime m n hm hn hmn ihm ihn =>
      intro hsq hd
      obtain ⟨r1, hr1⟩ := ihm (hsq.of_mul_left) (fun p hp hpd => hd p hp (dvd_mul_of_dvd_left hpd _))
      obtain ⟨r2, hr2⟩ := ihn (hsq.of_mul_right) (fun p hp hpd => hd p hp (dvd_mul_of_dvd_right hpd _))
      refine ⟨(ZMod.chineseRemainder hmn).symm (r1, r2), ?_⟩
      apply (ZMod.chineseRemainder hmn).injective
      rw [map_mul, RingEquiv.apply_symm_apply, map_intCast]
      ext <;> simp [hr1, hr2]
  set n := b.natAbs with hn
  have hn0 : n ≠ 0 := Int.natAbs_ne_zero.mpr hb0
  have : NeZero n := ⟨hn0⟩
  obtain ⟨r, hr⟩ := key n (Int.squarefree_natAbs.mpr hb) (fun p hp hpd => h p hp (Int.natCast_dvd.mpr hpd))
  refine ⟨r.valMinAbs, ?_, ?_⟩
  · rw [← Int.natAbs_dvd, ← hn, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hr]; ring
  · have h1 := ZMod.natAbs_valMinAbs_le r
    have h2 : (|r.valMinAbs| : ℤ) = (r.valMinAbs.natAbs : ℤ) := Int.abs_eq_natAbs _
    have h3 : (|b| : ℤ) = (n : ℤ) := Int.abs_eq_natAbs _
    rw [h2, h3]
    omega

/-! ### 4. Legendre's theorem (the descent) -/

/-- **Legendre's theorem, Hilbert-symbol form:** for $a, b \in \mathbb{Q}^\times$, if
$(a,b)_v = 1$ at every place $v$ of $\mathbb{Q}$, then $(a,b)_{\mathbb{Q}} = 1$, i.e.
$z^2 = a x^2 + b y^2$ has a nonzero rational solution. Proof: reduce to squarefree integers
$|a| \le |b|$ and descend on $|a| + |b|$ using steps 1–3. -/
@[kb "serre1973" "Ch. IV §3.2, Thm. 8 (n = 3) [unverified]; cassels1978 Ch. 6, Thm. 4.1, p. 80 (Legendre)"]
theorem hilbert_rat_eq_one_of_everywhere (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ v : RatPlace, v.hilbert a b = 1) : hilbertSymbol ℚ a b = 1 := by
  have hS : ∀ (K : Type) [Field K] (a b : K), hilbertSymbol K a b = 1 ↔ ∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2 := by
    intro K _ a b
    unfold hilbertSymbol
    split_ifs with h
    · exact iff_of_true rfl h
    · exact iff_of_false (by norm_num) h
  have hSq : ∀ (K : Type) [Field K] (a b c : K), c ≠ 0 → (hilbertSymbol K a (b * c ^ 2) = 1 ↔ hilbertSymbol K a b = 1) := by
    intro K _ a b c hc
    rw [hS, hS]
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
  have hL : ∀ (K : Type) [Field K] (a b b' t : K), b' ≠ 0 → b * b' = t ^ 2 - a → hilbertSymbol K a b' = 1 → hilbertSymbol K a b = 1 := by
    intro K _ a b b' t hb' he h
    rw [hS] at h ⊢
    obtain ⟨x, y, z, hne, hz⟩ := h
    by_cases hy : y = 0
    · subst hy
      exact ⟨x, 0, z, hne, by rw [hz]; ring⟩
    · refine ⟨z + x * t, b' * y, z * t + a * x, ?_, ?_⟩
      · intro h0
        simp only [Prod.mk_eq_zero] at h0
        exact mul_ne_zero hb' hy h0.2.1
      · linear_combination (t^2 - a) * hz - b' * y ^ 2 * he
  have hpL : ∀ (v : RatPlace) (x y y' s : ℚ), y ≠ 0 → y' * y = s ^ 2 - x → v.hilbert x y = 1 → v.hilbert x y' = 1 := by
    intro v x y y' s hy he h
    cases v with
    | infinite =>
      exact hL ℝ _ _ _ (s : ℝ) (by exact_mod_cast hy) (by exact_mod_cast he) h
    | finite p =>
      have : Fact (p : ℕ).Prime := ⟨p.2⟩
      exact hL ℚ_[p] _ _ _ (s : ℚ_[p]) (by exact_mod_cast hy) (by exact_mod_cast he) h
  have hpSq : ∀ (v : RatPlace) (x y c : ℚ), c ≠ 0 → (v.hilbert x (y * c ^ 2) = 1 ↔ v.hilbert x y = 1) := by
    intro v x y c hc
    cases v with
    | infinite =>
      have := hSq ℝ (x : ℝ) (y : ℝ) (c : ℝ) (by exact_mod_cast hc)
      simp only [RatPlace.hilbert]; push_cast; exact this
    | finite p =>
      have : Fact (p : ℕ).Prime := ⟨p.2⟩
      have := hSq ℚ_[p] (x : ℚ_[p]) (y : ℚ_[p]) (c : ℚ_[p]) (by exact_mod_cast hc)
      simp only [RatPlace.hilbert]; push_cast; exact this
  have hpC : ∀ (v : RatPlace) (x y : ℚ), v.hilbert x y = v.hilbert y x := by
    intro v x y
    cases v <;> exact hilbertSymbol_comm _ _ _
  have hsqZ : ∀ n : ℤ, n ≠ 0 → ∃ m k : ℤ, Squarefree m ∧ k ≠ 0 ∧ n = m * k ^ 2 ∧ m.natAbs ≤ n.natAbs := by
    intro n hn
    obtain ⟨a', b', hab, hsq⟩ := Nat.sq_mul_squarefree n.natAbs
    have hb0 : b' ≠ 0 := by rintro rfl; simp at hab; omega
    have ha0 : a' ≠ 0 := by rintro rfl; simp at hab; omega
    refine ⟨n.sign * a', b', ?_, by exact_mod_cast hb0, ?_, ?_⟩
    · rw [← Int.squarefree_natAbs, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hn]; simpa
    · conv_lhs => rw [← Int.sign_mul_natAbs n, ← hab]
      push_cast; ring
    · rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hn, ← hab]
      simp only [Int.natAbs_natCast, one_mul]
      exact Nat.le_mul_of_pos_left _ (by positivity)
  have hsqQ : ∀ q : ℚ, q ≠ 0 → ∃ (m : ℤ) (c : ℚ), Squarefree m ∧ c ≠ 0 ∧ q = m * c ^ 2 := by
    intro q hq
    have hn : q.num * q.den ≠ 0 := mul_ne_zero (Rat.num_ne_zero.mpr hq) (by exact_mod_cast q.den_ne_zero)
    obtain ⟨m, k, hm, hk, he, -⟩ := hsqZ _ hn
    refine ⟨m, k / q.den, hm, div_ne_zero (by exact_mod_cast hk) (by exact_mod_cast q.den_ne_zero), ?_⟩
    have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    have : ((q.num * q.den : ℤ) : ℚ) = (m * k ^ 2 : ℤ) := by rw [he]
    push_cast at this
    rw [div_pow, ← mul_div_assoc, ← this, eq_div_iff (pow_ne_zero 2 hd), ← Rat.mul_den_eq_num]
    ring
  have hres : ∀ (a b : ℤ) (p : ℕ) [Fact p.Prime], Squarefree b → (p : ℤ) ∣ b →
      hilbertSymbol ℚ_[p] ((a:ℚ):ℚ_[p]) ((b:ℚ):ℚ_[p]) = 1 → IsSquare ((a : ZMod p)) := by
    intro a b p hp hb hpb h
    by_cases hpa : (p : ℤ) ∣ a
    · rw [(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr hpa]; exact ⟨0, by simp⟩
    by_cases h2 : p = 2
    · subst h2
      generalize (a : ZMod 2) = x
      fin_cases x
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    obtain ⟨c, rfl⟩ := hpb
    have hpc : ¬ (p : ℤ) ∣ c := by
      rintro ⟨d, rfl⟩
      have := hb (p : ℤ) ⟨d, by ring⟩
      exact hp.out.not_isUnit (Int.ofNat_isUnit.mp this)
    have hua : IsUnit (a : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff]
      exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp (fun h => hpa ((PadicInt.norm_int_lt_one_iff_dvd a).mp h)))
    have huc : IsUnit (c : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff]
      exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp (fun h => hpc ((PadicInt.norm_int_lt_one_iff_dvd c).mp h)))
    have e1 : ((a:ℚ):ℚ_[p]) = (p:ℚ_[p]) ^ 0 * ((hua.unit : ℤ_[p]) : ℚ_[p]) := by simp
    have e2 : (((p * c : ℤ) :ℚ):ℚ_[p]) = (p:ℚ_[p]) ^ 1 * ((huc.unit : ℤ_[p]) : ℚ_[p]) := by simp
    rw [e1, e2, HilbertLocal.hilbertSymbol_odd_formula h2] at h
    simp only [HilbertLocal.unitChar, pow_one, pow_zero, mul_one, one_mul, zero_mul, IsUnit.unit_spec, map_intCast] at h
    rwa [quadraticChar_one_iff_isSquare] at h
    intro h0
    exact hpa ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h0)
  have hcrt : ∀ (a : ℤ) (n : ℕ), Squarefree n → (∀ p : ℕ, p.Prime → p ∣ n → IsSquare (a : ZMod p)) → ∃ t : ℤ, (n:ℤ) ∣ t^2 - a := by
    intro a n
    induction n using Nat.recOnPrimeCoprime with
    | zero => intro h; exact absurd h not_squarefree_zero
    | prime_pow p k hp =>
      intro hsq hall
      rcases Nat.lt_or_ge k 2 with hk | hk
      · interval_cases k
        · exact ⟨0, by simp⟩
        · obtain ⟨r, hr⟩ := hall p hp (by simp)
          have : NeZero p := ⟨hp.ne_zero⟩
          refine ⟨(r.val : ℤ), ?_⟩
          rw [pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
          push_cast
          rw [ZMod.natCast_zmod_val, hr]; ring
      · exfalso
        have := hsq p ⟨p ^ (k - 2), by rw [← pow_two, ← pow_add]; congr 1; omega⟩
        exact hp.not_isUnit (Nat.isUnit_iff.mpr (by simpa using this))
    | coprime m n hm hn hmn ihm ihn =>
      intro hsq hall
      obtain ⟨t1, h1⟩ := ihm (Squarefree.of_mul_left hsq) (fun p hp hd => hall p hp (dvd_mul_of_dvd_left hd n))
      obtain ⟨t2, h2⟩ := ihn (Squarefree.of_mul_right hsq) (fun p hp hd => hall p hp (dvd_mul_of_dvd_right hd m))
      have hc : IsCoprime (m : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.mpr hmn
      obtain ⟨u, v, huv⟩ := hc
      refine ⟨t1 * v * n + t2 * u * m, ?_⟩
      push_cast
      apply IsCoprime.mul_dvd ⟨u, v, huv⟩
      · have : (t1 * v * n + t2 * u * m) ^ 2 - a = (t1 ^ 2 - a) + m * (u * (t2 - t1) * ((t1 * v * n + t2 * u * m) + t1)) := by
          linear_combination ((t1 * v * n + t2 * u * m) + t1) * t1 * huv
        rw [this]; exact dvd_add h1 (dvd_mul_right _ _)
      · have : (t1 * v * n + t2 * u * m) ^ 2 - a = (t2 ^ 2 - a) + n * (v * (t1 - t2) * ((t1 * v * n + t2 * u * m) + t2)) := by
          linear_combination ((t1 * v * n + t2 * u * m) + t2) * t2 * huv
        rw [this]; exact dvd_add h2 (dvd_mul_right _ _)
  have hsmall : ∀ (a B t : ℤ), B ≠ 0 → B ∣ t^2 - a → ∃ t' : ℤ, B ∣ t'^2 - a ∧ 2 * |t'| ≤ |B| := by
    intro a B t hB ht
    have hN : 0 < |B| := abs_pos.mpr hB
    have h0 := Int.emod_nonneg t hN.ne'
    have h1 := Int.emod_lt_of_pos t hN
    have hd : B ∣ t % |B| - t := by
      rw [Int.emod_def]; simp only [sub_sub_cancel_left, dvd_neg]
      exact Dvd.dvd.mul_right (self_dvd_abs B) _
    have key : ∀ s : ℤ, B ∣ s - t → B ∣ s ^ 2 - a := by
      intro s hs
      have : s ^ 2 - a = (t^2 - a) + (s - t) * (s + t) := by ring
      rw [this]; exact dvd_add ht (Dvd.dvd.mul_right hs _)
    by_cases hc : 2 * (t % |B|) ≤ |B|
    · refine ⟨t % |B|, key _ hd, ?_⟩
      rwa [abs_of_nonneg h0]
    · refine ⟨t % |B| - |B|, key _ ?_, ?_⟩
      · have : t % |B| - |B| - t = (t % |B| - t) - |B| := by ring
        rw [this]; exact dvd_sub hd (self_dvd_abs B)
      · rw [abs_of_neg (by linarith)]; linarith
  have main : ∀ N : ℕ, ∀ a b : ℤ, Squarefree a → Squarefree b → a.natAbs + b.natAbs = N →
      (∀ v : RatPlace, v.hilbert a b = 1) → hilbertSymbol ℚ a b = 1 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    have key : ∀ a b : ℤ, Squarefree a → Squarefree b → a.natAbs + b.natAbs = N → a.natAbs ≤ b.natAbs →
        (∀ v : RatPlace, v.hilbert a b = 1) → hilbertSymbol ℚ a b = 1 := by
      intro a b hsa hsb hN hab hloc
      have ha0 : a ≠ 0 := by rintro rfl; exact not_squarefree_zero hsa
      have hb0 : b ≠ 0 := by rintro rfl; exact not_squarefree_zero hsb
      by_cases hb1 : b.natAbs = 1
      · have ha1 : a.natAbs = 1 := by have := Int.natAbs_pos.mpr ha0; omega
        rcases Int.natAbs_eq_iff.mp ha1 with rfl | rfl <;> rcases Int.natAbs_eq_iff.mp hb1 with rfl | rfl
        · rw [hS]; exact ⟨1, 0, 1, by simp, by norm_num⟩
        · rw [hS]; exact ⟨1, 0, 1, by simp, by norm_num⟩
        · rw [hS]; exact ⟨0, 1, 1, by simp, by norm_num⟩
        · exfalso
          have := hloc RatPlace.infinite
          simp only [RatPlace.hilbert] at this
          push_cast at this
          rw [(hilbertSymbol_real (-1) (-1) (by norm_num) (by norm_num)).mpr ⟨by norm_num, by norm_num⟩] at this
          norm_num at this
      · have hb2 : 2 ≤ b.natAbs := by have := Int.natAbs_pos.mpr hb0; omega
        have hsqmod : ∀ p : ℕ, p.Prime → p ∣ b.natAbs → IsSquare (a : ZMod p) := by
          intro p hp hpb
          have : Fact p.Prime := ⟨hp⟩
          exact hres a b p hsb (Int.natAbs_dvd_natAbs.mp (by simpa using hpb)) (hloc (RatPlace.finite ⟨p, hp⟩))
        obtain ⟨t0, ht0⟩ := hcrt a b.natAbs (Int.squarefree_natAbs.mpr hsb) hsqmod
        obtain ⟨t, ht, htb⟩ := hsmall a b t0 hb0 (Int.natAbs_dvd.mp ht0)
        obtain ⟨b', hb'⟩ := ht
        by_cases hb'0 : b' = 0
        · rw [hS]
          have : t ^ 2 = a := by subst hb'0; linarith
          refine ⟨1, 0, t, by simp, ?_⟩
          have : ((t:ℚ)) ^ 2 = a := by exact_mod_cast this
          rw [this]; ring
        · obtain ⟨m, k, hm, hk, hbm, hmle⟩ := hsqZ b' hb'0
          have hlt : b'.natAbs < b.natAbs := by
            have e1 := Int.natCast_natAbs a
            have e2 := Int.natCast_natAbs b
            have e3 := Int.natCast_natAbs b'
            have hA : |a| ≤ |b| := by rw [← e1, ← e2]; exact_mod_cast hab
            have hB : (2:ℤ) ≤ |b| := by rw [← e2]; exact_mod_cast hb2
            have hm : |b| * |b'| ≤ t ^ 2 + |a| := by
              rw [← abs_mul, ← hb']
              calc |t^2 - a| ≤ |t^2| + |a| := abs_sub _ _
                _ = t^2 + |a| := by rw [abs_of_nonneg (sq_nonneg t)]
            have ht2 : 4 * t ^ 2 ≤ |b| ^ 2 := by
              have : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
              nlinarith [abs_nonneg t]
            have : |b'| < |b| := by
              by_contra hc
              have hc' := not_lt.mp hc
              nlinarith
            rw [← e2, ← e3] at this
            exact_mod_cast this
          have hcast : ((m:ℚ) * (k:ℚ)^2) = (b' : ℚ) := by rw [hbm]; push_cast; ring
          have IH := ih (a.natAbs + m.natAbs) (by omega) a m hsa hm rfl (by
            intro v
            rw [← hpSq v _ _ (k:ℚ) (by exact_mod_cast hk), hcast]
            exact hpL v a b b' t (by exact_mod_cast hb0) (by rw [mul_comm]; exact_mod_cast hb'.symm) (hloc v))
          have h2 : hilbertSymbol ℚ (a:ℚ) (b':ℚ) = 1 := by
            rw [← hcast, hSq ℚ _ _ _ (by exact_mod_cast hk)]
            exact IH
          exact hL ℚ _ _ (b' : ℚ) (t : ℚ) (by exact_mod_cast hb'0) (by exact_mod_cast hb'.symm) h2
    intro a b hsa hsb hN hloc
    rcases le_total a.natAbs b.natAbs with h | h
    · exact key a b hsa hsb hN h hloc
    · rw [hilbertSymbol_comm]; exact key b a hsb hsa (by omega) h (fun v => by rw [hpC]; exact hloc v)
  obtain ⟨m1, c1, hm1, hc1, rfl⟩ := hsqQ a ha
  obtain ⟨m2, c2, hm2, hc2, rfl⟩ := hsqQ b hb
  have hloc : ∀ v : RatPlace, v.hilbert m1 m2 = 1 := by
    intro v
    have := h v
    rw [hpSq v _ _ _ hc2, hpC, hpSq v _ _ _ hc1, hpC] at this
    exact this
  have := main _ m1 m2 hm1 hm2 rfl hloc
  rw [hSq ℚ _ _ _ hc2, hilbertSymbol_comm, hSq ℚ _ _ _ hc1, hilbertSymbol_comm]
  exact this

/-! ### 5. Reducing a ternary form to ⟨1, −a, −b⟩ -/

/-- **Diagonalization over $\mathbb{Q}$:** every nondegenerate rational form is isometric over
$\mathbb{Q}$ to a diagonal form $\langle a_0, \dots, a_{n-1} \rangle$ with all $a_i \ne 0$.
(Via Mathlib's `QuadraticForm.equivalent_weightedSumSquares` and `Equiv/Mathlib.lean`.) -/
@[kb "serre1973" "Ch. IV §1.2, Thm. 1 [unverified]"]
theorem exists_isometric_diag (Q : RatQF n) (hQ : Q.Nondegenerate) :
    ∃ a : Fin n → ℚ, (∀ i, a i ≠ 0) ∧ Q.IsometricIn ℚ (QuadForm.diag a) := by
  set Q' : QuadraticForm ℚ (Fin n → ℚ) := LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' ℚ Q.coeff) with hQ'
  have hev : ∀ x, QuadForm.evalIn ℚ Q x = Q' x := fun x => by
    rw [hQ', LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
    simp only [QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · ring
    · rw [Q.upper (not_le.mp h)]; ring
  clear_value Q'
  obtain ⟨v0, hv0⟩ := LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm ℚ Q')
  let e : Fin (Module.finrank ℚ (Fin n → ℚ)) ≃ Fin n := finCongr (Module.finrank_fin_fun ℚ)
  let v := v0.reindex e
  have hv : LinearMap.IsOrthoᵢ (QuadraticMap.associated Q') v := by
    intro i j hij
    show QuadraticMap.associated Q' (v i) (v j) = 0
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply]
    exact hv0 (fun h => hij (e.symm.injective h))
  clear_value v
  refine ⟨fun i => Q' (v i), ?_, ?_⟩
  · intro i hi
    simp only at hi
    apply hQ
    rw [← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨v i, v.ne_zero i, ?_⟩
    have hA : ∀ y, QuadraticMap.associated Q' (v i) y = 0 := by
      intro y
      rw [← v.sum_repr y]
      simp only [map_sum, map_smul]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hij : i = j
      · subst hij
        rw [QuadraticMap.associated_eq_self_apply, hi, smul_zero]
      · rw [hv hij, smul_zero]
    have hP : ∀ y, v i ⬝ᵥ Q.hessian.mulVec y = 0 := by
      intro y
      have := QuadForm.polar_eq_hessian ℚ Q (v i) y
      rw [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at this
      rw [← this, hev, hev, hev]
      have h2 := hA y
      rw [QuadraticMap.associated_apply] at h2
      simpa using h2
    ext j
    have := hP (Pi.single j 1)
    rw [Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at this
    simpa using this
  · refine ⟨(Pi.basisFun ℚ (Fin n)).toMatrix v, ?_, ?_⟩
    · have := Module.Basis.invertibleToMatrix (Pi.basisFun ℚ (Fin n)) v
      exact (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_invertible _)
    · intro y
      have hmul : ((Pi.basisFun ℚ (Fin n)).toMatrix v).mulVec y = ∑ i, y i • v i := by
        ext k
        simp [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Finset.sum_apply, mul_comm]
      rw [hmul, hev, ← QuadraticMap.basisRepr_apply, QuadraticMap.basisRepr_eq_of_iIsOrtho Q' v hv,
        QuadraticMap.weightedSumSquares_apply]
      simp only [QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply, Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · simp [mul_assoc]
      · intro b _ hb
        simp [Ne.symm hb]
      · simp

/-- **Isometry over $\mathbb{Q}$ gives isometry over every field $K \supseteq \mathbb{Q}$**
(map the change-of-variables matrix into $K$). -/
@[kb "serre1973" "Ch. IV §1.1 [unverified]"]
theorem isometricIn_of_rat (K : Type*) [Field K] [CharZero K] {Q Q' : RatQF n}
    (h : Q.IsometricIn ℚ Q') : Q.IsometricIn K Q' := by
  obtain ⟨P, hP, hPx⟩ := h
  have hF : QuadForm.evalIn (MvPolynomial (Fin n) ℚ) Q ((P.map (algebraMap ℚ (MvPolynomial (Fin n) ℚ))).mulVec (fun i => MvPolynomial.X i)) = QuadForm.evalIn (MvPolynomial (Fin n) ℚ) Q' (fun i => MvPolynomial.X i) := by
    apply MvPolynomial.funext
    intro r
    have := hPx r
    have e1 : ∀ (R : RatQF n) (x : Fin n → MvPolynomial (Fin n) ℚ),
        MvPolynomial.eval r (QuadForm.evalIn _ R x) = QuadForm.evalIn ℚ R (fun i => MvPolynomial.eval r (x i)) := by
      intro R x
      simp [QuadForm.evalIn, map_sum, apply_ite]
    rw [e1, e1]
    convert this using 2
    · ext i
      simp [Matrix.mulVec, dotProduct, map_sum]
    · ext i; simp
  refine ⟨P.map (algebraMap ℚ K), ?_, ?_⟩
  · have := RingHom.map_det (algebraMap ℚ K) P
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact hP.map _
  · intro x
    have e2 : ∀ (R : RatQF n) (y : Fin n → MvPolynomial (Fin n) ℚ),
        MvPolynomial.aeval x (QuadForm.evalIn _ R y) = QuadForm.evalIn K R (fun i => MvPolynomial.aeval x (y i)) := by
      intro R y
      simp [QuadForm.evalIn, map_sum, apply_ite]
    have := congrArg (MvPolynomial.aeval x) hF
    rw [e2, e2] at this
    convert this using 2
    · ext i
      simp [Matrix.mulVec, dotProduct, map_sum]
    · simp

/-- **Isotropy is invariant under isometry** over a field $K \supseteq \mathbb{Q}$. -/
@[kb "serre1973" "Ch. IV §1.6 [unverified]"]
theorem isotropicIn_iff_of_isometricIn (K : Type*) [Field K] [CharZero K] {Q Q' : RatQF n}
    (h : Q.IsometricIn K Q') : Q.IsotropicIn K ↔ Q'.IsotropicIn K := by
  obtain ⟨P, hP, hPx⟩ := h
  constructor
  · rintro ⟨x, hx, hQx⟩
    refine ⟨P⁻¹.mulVec x, ?_, ?_⟩
    · intro h0
      apply hx
      have := congrArg P.mulVec h0
      rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec,
        Matrix.mulVec_zero] at this
    · rw [← hPx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
      exact hQx
  · rintro ⟨y, hy, hQy⟩
    refine ⟨P.mulVec y, ?_, ?_⟩
    · intro h0
      apply hy
      have := congrArg P⁻¹.mulVec h0
      rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hP, Matrix.one_mulVec,
        Matrix.mulVec_zero] at this
    · rw [hPx]; exact hQy

/-- **Diagonal ternary forms and the Hilbert symbol:** for nonzero $a_0, a_1, a_2 \in \mathbb{Q}$ and
a field $K \supseteq \mathbb{Q}$, $\langle a_0, a_1, a_2 \rangle$ is isotropic over $K$ iff
$\left(-\tfrac{a_1}{a_0}, -\tfrac{a_2}{a_0}\right)_K = 1$. -/
@[kb "serre1973" "Ch. IV §2.2 [unverified]; cassels1978 Ch. 4, Lemma 2.5, p. 59"]
theorem isotropic_diag_three_iff (K : Type*) [Field K] [CharZero K] (a₀ a₁ a₂ : ℚ)
    (h₀ : a₀ ≠ 0) (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0) :
    (QuadForm.diag ![a₀, a₁, a₂]).IsotropicIn K ↔
      hilbertSymbol K (algebraMap ℚ K (-a₁ / a₀)) (algebraMap ℚ K (-a₂ / a₀)) = 1 := by
  have hev : ∀ (a b c : ℚ) (x : Fin 3 → K),
      QuadForm.evalIn K (QuadForm.diag ![a, b, c]) x = algebraMap ℚ K a * x 0 ^ 2 + algebraMap ℚ K b * x 1 ^ 2 + algebraMap ℚ K c * x 2 ^ 2 := by
    intro a b c x
    simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_three, Matrix.diagonal]
    ring
  rw [hilbertSymbol_eq_one_iff_isotropic]
  have h0K : algebraMap ℚ K a₀ ≠ 0 := by simpa using h₀
  constructor
  · rintro ⟨x, hx, hq⟩
    refine ⟨![x 1, x 2, x 0], ?_, ?_⟩
    · intro h
      apply hx
      funext i
      fin_cases i
      · exact congrFun h 2
      · exact congrFun h 0
      · exact congrFun h 1
    · rw [hev] at hq ⊢
      simp only [map_div₀, map_neg, map_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      linear_combination (-1 : K) * hq
  · rintro ⟨x, hx, hq⟩
    refine ⟨![x 2, x 0, x 1], ?_, ?_⟩
    · intro h
      apply hx
      funext i
      fin_cases i
      · exact congrFun h 1
      · exact congrFun h 2
      · exact congrFun h 0
    · rw [hev] at hq ⊢
      simp only [map_div₀, map_neg, map_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hq ⊢
      field_simp at hq
      linear_combination (-1 : K) * hq

end QuadFormsKB.HM3
