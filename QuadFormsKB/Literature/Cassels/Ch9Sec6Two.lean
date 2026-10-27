/-
# Cassels, Chapter 9, §6: primitive representations as a sum of two squares (Lemma 6.3)

**Layer:** the form $x_0^2 + x_1^2$ = `Siegel.sumSq 2`, primitive representations `primRepSet`, their number
`primRepNum` (`Ch9Sec6.lean`), the proper automorphs `AutPlus` (`Ch9Sec1.lean`).

**Proves** Lemma 6.3 (Cassels, p. 149): the criterion (`primRep_sumSq_two_iff`, proved in `Ch9Sec5Squares.lean`, is
tagged here as well) and the count (`primRepNum_sumSq_two`): if $a > 0$, $4 \nmid a$ and no prime $p \equiv 3 \pmod 4$
divides $a$, the number of primitive representations of $a$ as $x^2 + y^2$ is $2^{\alpha + 2}$, $\alpha$ the number of
distinct odd prime divisors of $a$.

*Proof (Cassels', made explicit):* a primitive representation $b$ is the first column of some
$T \in \mathrm{SL}_2(\mathbb Z)$, $T = (b \; t)$; the class $c = b_0t_0 + b_1t_1 \bmod a$ does not depend on the choice of
$t$ and satisfies $c^2 \equiv -1 \pmod a$ ((6.8): $f(T\mathbf x) = ax^2 + 2cxy + \frac{c^2+1}{a}y^2$). Every root $c$ of
$c^2 \equiv -1 \pmod a$ occurs, since $ax^2 + 2cxy + \frac{c^2+1}{a}y^2$ is positive definite of determinant $1$, hence
properly equivalent to $x^2 + y^2$ (Lemma 3.2, Corollary 2); and $b, b'$ give the same $c$ iff $b' = Rb$ for one of the
$o^{+}(f) = 4$ proper automorphs $R$. Finally $c^2 \equiv -1$ has $2^\alpha$ roots modulo $a$ (Chinese remainder theorem;
two roots modulo each $p^k \parallel a$, $p \equiv 1 \pmod 4$, as $(\mathbb Z/p^k)^\times$ is cyclic of order divisible by
$4$; one root modulo $2$).
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec5Squares
import QuadFormsKB.Literature.Cassels.Ch9Sec6

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

attribute [kb "cassels1978" "Ch. 9, Lemma 6.3, p. 149 (first part: the criterion)"] primRep_sumSq_two_iff

/-- In a finite cyclic group, if `e ≠ 1` has `e ^ 2 = 1`, every square root of `1` is `1` or `e`. -/
theorem cyc_sq_eq_one {G : Type*} [CommGroup G] [Fintype G] [IsCyclic G] [DecidableEq G] {e : G} (hne : e ≠ 1)
    (he : e ^ 2 = 1) (z : G) (hz : z ^ 2 = 1) : z = 1 ∨ z = e := by
  by_contra h
  rw [not_or] at h
  have hsub : ({1, e, z} : Finset G) ⊆ Finset.univ.filter (fun a : G => a ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl <;> simp [*]
  have h1 := Finset.card_le_card hsub
  have h2 := IsCyclic.card_pow_eq_one_le (α := G) (n := 2) (by norm_num)
  have h3 : ({1, e, z} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact fun h' => h.2 h'.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hne.symm, fun h' => h.1 h'.symm⟩
  omega

/-- For a prime `p ≡ 1 (4)` and `k > 0`, the congruence `c² = -1` has exactly two solutions modulo `p ^ k`. -/
theorem card_sqrt_neg_one_primePow {p k : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) (hk : 0 < k) :
    Nat.card {c : ZMod (p ^ k) // c * c = -1} = 2 := by
  have hp2 : p ≠ 2 := by omega
  have hn : 2 < p ^ k := by
    calc 2 < p := by have := hp.two_le; omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
  have : NeZero (p ^ k) := ⟨by positivity⟩
  have : Fact (2 < p ^ k) := ⟨hn⟩
  have : IsCyclic (ZMod (p ^ k))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 k
  classical
  have hcard : 4 ∣ Fintype.card (ZMod (p ^ k))ˣ := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp hk]
    exact Dvd.dvd.mul_left (by omega) _
  have hne : (-1 : (ZMod (p ^ k))ˣ) ≠ 1 := by
    intro h
    exact ZMod.neg_one_ne_one (n := p ^ k) (by simpa using congrArg Units.val h)
  have hsq : ((-1 : (ZMod (p ^ k))ˣ)) ^ 2 = 1 := by simp
  have key : ∀ u : (ZMod (p ^ k))ˣ, u * u = -1 ↔ orderOf u = 4 := by
    intro u
    constructor
    · intro h
      have h2 : u ^ 2 = -1 := by rw [pow_two]; exact h
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := u) (by rw [pow_one, h2]; exact hne)
        (by
          have : u ^ 4 = (u ^ 2) ^ 2 := by rw [← pow_mul]
          rw [show 2 ^ (1 + 1) = 4 by norm_num, this, h2]; simp)
      simpa using this
    · intro h
      have hu4 : (u ^ 2) ^ 2 = 1 := by rw [← pow_mul]; have := pow_orderOf_eq_one u; rwa [h] at this
      rcases cyc_sq_eq_one hne hsq (u ^ 2) hu4 with h1 | h1
      · exfalso
        have := orderOf_dvd_of_pow_eq_one h1
        rw [h] at this; omega
      · rw [← pow_two]; exact h1
  let e1 : {c : ZMod (p ^ k) // c * c = -1} ≃ {u : (ZMod (p ^ k))ˣ // u * u = -1} :=
    Equiv.ofBijective (fun c => ⟨⟨c.1, -c.1, by rw [mul_neg, c.2]; simp, by rw [neg_mul, c.2]; simp⟩,
      Units.ext (by simpa using c.2)⟩) ⟨by
        intro x y h; apply Subtype.ext; simpa using congrArg (fun w => (w.1 : ZMod (p ^ k))) h, by
        intro u
        exact ⟨⟨u.1, by simpa using congrArg Units.val u.2⟩, Subtype.ext (Units.ext rfl)⟩⟩
  rw [Nat.card_congr (e1.trans (Equiv.subtypeEquivRight key))]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, IsCyclic.card_orderOf_eq_totient hcard]
  decide

/-- The number of square roots of `-1` modulo coprime `m, n` is multiplicative (Chinese remainder theorem). -/
theorem card_sqrt_neg_one_mul {m n : ℕ} (h : m.Coprime n) :
    Nat.card {c : ZMod (m * n) // c * c = -1} =
      Nat.card {c : ZMod m // c * c = -1} * Nat.card {c : ZMod n // c * c = -1} := by
  let e := (ZMod.chineseRemainder h)
  let e1 : {c : ZMod (m * n) // c * c = -1} ≃
      {x : ZMod m × ZMod n // x.1 * x.1 = -1 ∧ x.2 * x.2 = -1} :=
    Equiv.subtypeEquiv e.toEquiv (fun c => by
      constructor
      · intro hc
        have := congrArg e hc
        simp only [map_mul, map_neg, map_one] at this
        exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
      · rintro ⟨h1, h2⟩
        apply e.injective
        simp only [map_mul, map_neg, map_one]
        exact Prod.ext h1 h2)
  rw [Nat.card_congr (e1.trans (Equiv.subtypeProdEquivProd (p := fun x : ZMod m => x * x = -1)
    (q := fun y : ZMod n => y * y = -1))), Nat.card_prod]

/-- The number of square roots of `-1` modulo `a` is `2 ^ α` for `a` as in Lemma 6.3. -/
theorem card_sqrt_neg_one : ∀ a : ℕ, 0 < a → ¬ 4 ∣ a → (∀ p ∈ a.primeFactors, p % 4 ≠ 3) →
    Nat.card {c : ZMod a // c * c = -1} = 2 ^ (a.primeFactors.filter (· ≠ 2)).card := by
  intro a
  induction a using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro _ h4 h3
    rw [Nat.primeFactors_prime_pow hn.ne' hp] at h3 ⊢
    by_cases h2 : p = 2
    · subst h2
      have : n = 1 := by
        by_contra hn1
        exact h4 (by
          have : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
          simpa using this)
      subst this
      rw [Nat.card_eq_fintype_card]
      simp
      decide
    · have hodd := (hp.eq_two_or_odd).resolve_left h2
      have h3p := h3 p (by simp)
      have hp4 : p % 4 = 1 := by omega
      rw [card_sqrt_neg_one_primePow hp hp4 hn]
      rw [Finset.filter_true_of_mem (by simpa using h2)]
      simp
  | zero => intro h; omega
  | one =>
    intro _ _ _
    simp only [Nat.primeFactors_one, Finset.filter_empty, Finset.card_empty, pow_zero]
    rw [Nat.card_eq_fintype_card]
    decide
  | coprime a b ha hb hab iha ihb =>
    intro _ h4 h3
    have hmul : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := hab.primeFactors_mul
    have hdisj : Disjoint a.primeFactors b.primeFactors := hab.disjoint_primeFactors
    rw [card_sqrt_neg_one_mul hab, iha (by omega) (fun h => h4 (Dvd.dvd.mul_right h _))
      (fun p hp => h3 p (by rw [hmul]; exact Finset.mem_union_left _ hp)),
      ihb (by omega) (fun h => h4 (Dvd.dvd.mul_left h _))
      (fun p hp => h3 p (by rw [hmul]; exact Finset.mem_union_right _ hp)),
      hmul, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj),
      pow_add]

/-- The primitive representations of `a` as `x² + y²`, as pairs of integers. -/
def PrimPair (a : ℕ) : Set (ℤ × ℤ) := {p | Int.gcd p.1 p.2 = 1 ∧ p.1 ^ 2 + p.2 ^ 2 = a}

/-- The relation "`c` is attached to `p`": `c p₀ = p₁` and `c p₁ = -p₀` modulo `a`. -/
def Attached (a : ℕ) (c : ZMod a) (p : ℤ × ℤ) : Prop :=
  c * (p.1 : ZMod a) = p.2 ∧ c * (p.2 : ZMod a) = -p.1

/-- The primitive representations of `a` by `x² + y²` correspond to `PrimPair a`. -/
theorem primRepNum_sumSq_two_eq (a : ℕ) : primRepNum (sumSq 2) a = Nat.card (PrimPair a) := by
  unfold primRepNum
  refine Nat.card_congr ((Equiv.subtypeEquiv (finTwoArrowEquiv ℤ) (fun b => ?_)))
  simp only [primRepSet, PrimPair, Set.mem_ofPred_eq, eval_sumSq_int, Fin.sum_univ_two, finTwoArrowEquiv_apply]
  have hg : Finset.univ.gcd b = ((b 0).gcd (b 1) : ℤ) := by
    rw [Int.coe_gcd]
    simp [Fin.univ_succ, Finset.gcd_insert]
    exact dvd_antisymm_of_normalize_eq (by simp) (by simp)
      (dvd_gcd (gcd_dvd_left _ _) (dvd_normalize_iff.1 (gcd_dvd_right _ _)))
      (dvd_gcd (gcd_dvd_left _ _) (dvd_normalize_iff.2 (gcd_dvd_right _ _)))
  have : (Finset.univ.gcd b = 1) ↔ (b 0).gcd (b 1) = 1 := by
    rw [hg]; exact_mod_cast Iff.rfl
  rw [this]; rfl

/-- Each primitive pair has a unique attached residue class modulo `a`. -/
theorem attached_existsUnique {a : ℕ} {p : ℤ × ℤ} (hp : p ∈ PrimPair a) : ∃! c : ZMod a, Attached a c p := by
  obtain ⟨hg, hs⟩ := hp
  obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hg
  have huv' : (u : ZMod a) * p.1 + v * p.2 = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ZMod a) huv
  have hz : (p.1 : ZMod a) ^ 2 + (p.2 : ZMod a) ^ 2 = 0 := by
    have := congrArg (Int.cast : ℤ → ZMod a) hs
    push_cast at this
    rw [this]; exact ZMod.natCast_self a
  refine ⟨u * p.2 - v * p.1, ⟨?_, ?_⟩, ?_⟩
  · linear_combination (-(v : ZMod a)) * hz + (p.2 : ZMod a) * huv'
  · linear_combination (u : ZMod a) * hz - (p.1 : ZMod a) * huv'
  · rintro c ⟨h1, h2⟩
    linear_combination (u : ZMod a) * h1 + (v : ZMod a) * h2 - c * huv'

/-- For a primitive pair, `1` is a combination of its coordinates in `ZMod a`. -/
theorem bezout_zmod {a : ℕ} {p : ℤ × ℤ} (hp : p ∈ PrimPair a) :
    ∃ u v : ZMod a, u * (p.1 : ZMod a) + v * (p.2 : ZMod a) = 1 := by
  obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hp.1
  exact ⟨u, v, by exact_mod_cast congrArg (Int.cast : ℤ → ZMod a) huv⟩

/-- An attached residue class is a square root of `-1`. -/
theorem Attached.sq {a : ℕ} {c : ZMod a} {p : ℤ × ℤ} (hp : p ∈ PrimPair a) (h : Attached a c p) :
    c * c = -1 := by
  obtain ⟨u, v, huv⟩ := bezout_zmod hp
  obtain ⟨h1, h2⟩ := h
  linear_combination (u * c - v) * h1 + (u + v * c) * h2 - (c * c + 1) * huv

/-- Two primitive pairs with the same attached class differ by one of the four rotations. -/
theorem Attached.rot {a : ℕ} (ha : 0 < a) {c : ZMod a} {p q : ℤ × ℤ} (hp : p ∈ PrimPair a) (hq : q ∈ PrimPair a)
    (hcp : Attached a c p) (hcq : Attached a c q) :
    q = p ∨ q = (-p.2, p.1) ∨ q = (-p.1, -p.2) ∨ q = (p.2, -p.1) := by
  have hc := hcp.sq hp
  obtain ⟨hp1, hp2⟩ := hcp
  obtain ⟨hq1, hq2⟩ := hcq
  have hP : ((p.1 * q.1 + p.2 * q.2 : ℤ) : ZMod a) = 0 := by
    push_cast
    linear_combination ((p.1 : ZMod a) * q.1) * hc - (q.2 : ZMod a) * hp1 - (c * p.1) * hq1
  have hQ : ((p.1 * q.2 - p.2 * q.1 : ℤ) : ZMod a) = 0 := by
    push_cast
    linear_combination (-(p.1 : ZMod a)) * hq1 + (q.1 : ZMod a) * hp1
  obtain ⟨e, he⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ a).1 hP
  obtain ⟨f, hf⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ a).1 hQ
  have hpa := hp.2
  have hqa := hq.2
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hsum : (a : ℤ) * (e ^ 2 + f ^ 2) = a := by
    have h1 : (a : ℤ) * ((a : ℤ) * (e ^ 2 + f ^ 2)) = (a : ℤ) * a := by
      calc (a : ℤ) * ((a : ℤ) * (e ^ 2 + f ^ 2)) = (a * e) ^ 2 + (a * f) ^ 2 := by ring
        _ = (p.1 * q.1 + p.2 * q.2) ^ 2 + (p.1 * q.2 - p.2 * q.1) ^ 2 := by rw [← he, ← hf]
        _ = (p.1 ^ 2 + p.2 ^ 2) * (q.1 ^ 2 + q.2 ^ 2) := by ring
        _ = a * a := by rw [hpa, hqa]
    exact mul_left_cancel₀ ha'.ne' h1
  have hef : e ^ 2 + f ^ 2 = 1 := by
    have := mul_left_cancel₀ ha'.ne' (hsum.trans (mul_one (a : ℤ)).symm)
    exact this
  have hq0 : (a : ℤ) * q.1 = a * (e * p.1 - f * p.2) := by
    calc (a : ℤ) * q.1 = (p.1 ^ 2 + p.2 ^ 2) * q.1 := by rw [hpa]
      _ = (p.1 * q.1 + p.2 * q.2) * p.1 - (p.1 * q.2 - p.2 * q.1) * p.2 := by ring
      _ = _ := by rw [he, hf]; ring
  have hq1' : (a : ℤ) * q.2 = a * (e * p.2 + f * p.1) := by
    calc (a : ℤ) * q.2 = (p.1 ^ 2 + p.2 ^ 2) * q.2 := by rw [hpa]
      _ = (p.1 * q.1 + p.2 * q.2) * p.2 + (p.1 * q.2 - p.2 * q.1) * p.1 := by ring
      _ = _ := by rw [he, hf]; ring
  have hq0' := mul_left_cancel₀ ha'.ne' hq0
  have hq1'' := mul_left_cancel₀ ha'.ne' hq1'
  have he1 : e ≤ 1 := by nlinarith
  have he2 : -1 ≤ e := by nlinarith
  have hf1 : f ≤ 1 := by nlinarith
  have hf2 : -1 ≤ f := by nlinarith
  have he3 : e = -1 ∨ e = 0 ∨ e = 1 := by omega
  have hf3 : f = -1 ∨ f = 0 ∨ f = 1 := by omega
  clear he hf hsum hq0 hq1' he1 he2 hf1 hf2
  obtain ⟨q0, q1⟩ := q
  simp only at hq0' hq1''
  simp only [Prod.ext_iff]
  rcases he3 with rfl | rfl | rfl <;> rcases hf3 with rfl | rfl | rfl <;>
    first | (norm_num at hef; done) | (norm_num at hq0' hq1''; omega)

/-- A positive definite integral binary form of determinant `1` is a sum of two squares of linear forms. -/
theorem exists_entries {a : ℕ} (ha : 0 < a) (cz m : ℤ) (hm : cz * cz + 1 = a * m) :
    ∃ t00 t01 t10 t11 : ℤ, (a : ℤ) = t00 * t00 + t10 * t10 ∧ cz = t00 * t01 + t10 * t11 ∧
      m = t01 * t01 + t11 * t11 := by
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![(a : ℤ), cz; cz, m]
  have hpd : Siegel.Hermite.IsPosDefInt A := by
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [A]
    · intro x hx
      have hv : x ⬝ᵥ (A *ᵥ x) = a * x 0 ^ 2 + 2 * cz * x 0 * x 1 + m * x 1 ^ 2 := by
        simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
      rw [hv]
      by_contra hle
      push Not at hle
      have key : (a : ℤ) * (a * x 0 ^ 2 + 2 * cz * x 0 * x 1 + m * x 1 ^ 2) =
          (a * x 0 + cz * x 1) ^ 2 + x 1 ^ 2 := by linear_combination (-(x 1 ^ 2)) * hm
      have h1 : (a : ℤ) * (a * x 0 ^ 2 + 2 * cz * x 0 * x 1 + m * x 1 ^ 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ha'.le hle
      have hx1 : x 1 = 0 := by nlinarith [sq_nonneg (a * x 0 + cz * x 1), sq_nonneg (x 1)]
      have hx0 : x 0 = 0 := by
        have h : (a : ℤ) * x 0 ^ 2 ≤ 0 := by simpa [hx1] using hle
        by_contra hne
        have : 0 < x 0 ^ 2 := by positivity
        nlinarith
      apply hx
      ext i; fin_cases i <;> simp [hx0, hx1]
  have hdet : A.det = 1 := by
    simp only [A, Matrix.det_fin_two_of]; linarith
  obtain ⟨g, hg⟩ := Siegel.Hermite.unimodular_posDef_equiv_one 2 (by norm_num) A hpd hdet
  set T := g.inv with hT
  have h1 : Tᵀ * g.valᵀ = 1 := by rw [← Matrix.transpose_mul, hT, g.val_inv, Matrix.transpose_one]
  have h2 : g.val * T = 1 := g.val_inv
  have hA : A = Tᵀ * T := by
    calc A = (Tᵀ * g.valᵀ) * A * (g.val * T) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
      _ = Tᵀ * (g.valᵀ * A * g.val) * T := by simp only [Matrix.mul_assoc]
      _ = Tᵀ * T := by rw [hg, Matrix.mul_one]
  have e00 := congrFun (congrFun hA 0) 0
  have e01 := congrFun (congrFun hA 0) 1
  have e11 := congrFun (congrFun hA 1) 1
  simp only [A, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at e00 e01 e11
  exact ⟨T 0 0, T 0 1, T 1 0, T 1 1, by simpa using e00, by simpa using e01, by simpa using e11⟩

/-- Integer identities for the entries of `T` with `TᵀT = [[a, c], [c, m]]` and `d = det T`, `d² = 1`. -/
theorem entries_identities (t00 t01 t10 t11 a cz d : ℤ) (h00 : a = t00 * t00 + t10 * t10)
    (h01 : cz = t00 * t01 + t10 * t11) (hd : d = t00 * t11 - t01 * t10) (hd2 : d * d = 1) :
    cz * t00 - d * t10 = a * t01 ∧ cz * (d * t10) + t00 = a * (d * t11) := by
  subst h00 h01 hd
  constructor
  · ring
  · linear_combination (-t00) * hd2

/-- Every square root of `-1` modulo `a` is attached to some primitive pair. -/
theorem exists_attached {a : ℕ} (ha : 0 < a) {c : ZMod a} (hc : c * c = -1) :
    ∃ p ∈ PrimPair a, Attached a c p := by
  have : NeZero a := ⟨ha.ne'⟩
  set cz : ℤ := (c.val : ℤ) with hcz
  have hcz' : (cz : ZMod a) = c := by simp [hcz]
  have hdvd : (a : ℤ) ∣ cz * cz + 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast; rw [hcz', hc]; ring
  obtain ⟨m, hm⟩ := hdvd
  obtain ⟨t00, t01, t10, t11, h00, h01, h11⟩ := exists_entries ha cz m hm
  set d : ℤ := t00 * t11 - t01 * t10 with hd
  have hd2 : d * d = 1 := by
    have : d * d = (a : ℤ) * m - cz * cz := by
      rw [h00, h11, h01, hd]; ring
    linarith
  obtain ⟨e1, e2⟩ := entries_identities t00 t01 t10 t11 a cz d h00 h01 hd hd2
  have hsq : (d * t10) ^ 2 = t10 * t10 := by
    calc (d * t10) ^ 2 = d * d * (t10 * t10) := by ring
      _ = t10 * t10 := by rw [hd2, one_mul]
  refine ⟨(t00, d * t10), ⟨?_, ?_⟩, ?_, ?_⟩
  · apply Int.isCoprime_iff_gcd_eq_one.mp
    refine ⟨d * t11, -t01, ?_⟩
    calc d * t11 * t00 + -t01 * (d * t10) = d * (t00 * t11 - t01 * t10) := by ring
      _ = d * d := by rw [← hd]
      _ = 1 := hd2
  · show t00 ^ 2 + (d * t10) ^ 2 = a
    rw [hsq, h00]; ring
  · show c * (t00 : ZMod a) = ((d * t10 : ℤ) : ZMod a)
    have := congrArg (Int.cast : ℤ → ZMod a) e1
    push_cast at this ⊢
    rw [hcz', ZMod.natCast_self, zero_mul] at this
    linear_combination this
  · show c * ((d * t10 : ℤ) : ZMod a) = -(t00 : ZMod a)
    have := congrArg (Int.cast : ℤ → ZMod a) e2
    push_cast at this ⊢
    rw [hcz', ZMod.natCast_self, zero_mul] at this
    linear_combination this

/-- The three nontrivial rotations of a primitive pair are primitive pairs. -/
theorem rot_mem {a : ℕ} {p : ℤ × ℤ} (hp : p ∈ PrimPair a) :
    (-p.2, p.1) ∈ PrimPair a ∧ (-p.1, -p.2) ∈ PrimPair a ∧ (p.2, -p.1) ∈ PrimPair a := by
  obtain ⟨hg, hs⟩ := hp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simpa [Int.gcd_comm] using hg
  · simp only; rw [← hs]; ring
  · simpa using hg
  · simp only; rw [← hs]; ring
  · simpa [Int.gcd_comm] using hg
  · simp only; rw [← hs]; ring

/-- The three nontrivial rotations of a pair with attached class `c` have attached class `c`. -/
theorem rot_attached {a : ℕ} {c : ZMod a} {p : ℤ × ℤ} (h : Attached a c p) :
    Attached a c (-p.2, p.1) ∧ Attached a c (-p.1, -p.2) ∧ Attached a c (p.2, -p.1) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> push_cast
  · linear_combination (-1 : ZMod a) * h2
  · linear_combination h1
  · linear_combination (-1 : ZMod a) * h1
  · linear_combination (-1 : ZMod a) * h2
  · linear_combination h2
  · linear_combination (-1 : ZMod a) * h1

/-- Each square root of `-1` modulo `a` is attached to exactly four primitive pairs. -/
theorem card_fiber {a : ℕ} (ha : 0 < a) {c : ZMod a} (hc : c * c = -1) :
    Nat.card {q : ℤ × ℤ // q ∈ PrimPair a ∧ Attached a c q} = 4 := by
  classical
  obtain ⟨p, hp, hcp⟩ := exists_attached ha hc
  obtain ⟨r1, r2, r3⟩ := rot_mem hp
  obtain ⟨s1, s2, s3⟩ := rot_attached hcp
  have hmem : ∀ q, (q ∈ PrimPair a ∧ Attached a c q) ↔
      q ∈ ({p, (-p.2, p.1), (-p.1, -p.2), (p.2, -p.1)} : Finset (ℤ × ℤ)) := by
    intro q
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hq, hcq⟩
      have := Attached.rot ha hp hq hcp hcq
      tauto
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨hp, hcp⟩
      · exact ⟨r1, s1⟩
      · exact ⟨r2, s2⟩
      · exact ⟨r3, s3⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hmem), Nat.card_eq_fintype_card, Fintype.card_coe]
  have hp0 : ¬ (p.1 = 0 ∧ p.2 = 0) := by
    rintro ⟨h1, h2⟩
    have := hp.2
    rw [h1, h2] at this
    have : (0 : ℤ) < a := by exact_mod_cast ha
    simp_all
  obtain ⟨x, y⟩ := p
  simp only at hp0
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
  · simp only [ne_eq, Prod.mk.injEq]; omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega

/-- The number of primitive pairs is `4` times the number of square roots of `-1` modulo `a`. -/
theorem card_primPair {a : ℕ} (ha : 0 < a) :
    Nat.card (PrimPair a) = 4 * Nat.card {c : ZMod a // c * c = -1} := by
  classical
  have : NeZero a := ⟨ha.ne'⟩
  let Φ : PrimPair a → {c : ZMod a // c * c = -1} := fun x =>
    ⟨(attached_existsUnique x.2).exists.choose,
      Attached.sq x.2 (attached_existsUnique x.2).exists.choose_spec⟩
  have hΦ : ∀ (x : PrimPair a) (c : {c : ZMod a // c * c = -1}), Φ x = c ↔ Attached a c.1 x.1 := by
    intro x c
    constructor
    · rintro rfl
      exact (attached_existsUnique x.2).exists.choose_spec
    · intro h
      exact Subtype.ext ((attached_existsUnique x.2).unique
        (attached_existsUnique x.2).exists.choose_spec h)
  have hfib : ∀ c : {c : ZMod a // c * c = -1}, Nat.card {x : PrimPair a // Φ x = c} = 4 := by
    intro c
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x => hΦ x c))]
    rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun q => q ∈ PrimPair a)
      (fun q => Attached a c.1 q))]
    exact card_fiber ha c.2
  have hfin : ∀ c : {c : ZMod a // c * c = -1}, Finite {x : PrimPair a // Φ x = c} := fun c =>
    Nat.finite_of_card_ne_zero (by rw [hfib c]; norm_num)
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv Φ), Nat.card_sigma]
  simp [hfib]
  ring

/-- **Cassels, Lemma 6.3** (Ch. 9, p. 149), the count: *if $a$ satisfies this condition (not divisible by $4$ nor by a
prime $p \equiv -1 \pmod 4$) then the number of primitive representations is $2^{\alpha + 2}$ where $\alpha$ is the number
of distinct odd prime divisors of $a$.* -/
@[kb "cassels1978" "Ch. 9, Lemma 6.3, p. 149 (the number 2^{α+2} of primitive representations)"]
theorem primRepNum_sumSq_two {a : ℕ} (ha : 0 < a) (h4 : ¬ 4 ∣ a) (h3 : ∀ p ∈ a.primeFactors, p % 4 ≠ 3) :
    primRepNum (sumSq 2) a = 2 ^ ((a.primeFactors.filter (· ≠ 2)).card + 2) := by
  rw [primRepNum_sumSq_two_eq, card_primPair ha, card_sqrt_neg_one a ha h4 h3, pow_add]
  norm_num
  ring

end QuadFormsKB.Siegel
