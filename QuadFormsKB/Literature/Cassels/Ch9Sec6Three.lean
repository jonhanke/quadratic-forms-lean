import QuadFormsKB.Literature.Cassels.Ch9Sec6Weight
import QuadFormsKB.Siegel.FourSquaresClassNumber

open Matrix

set_option linter.unusedSectionVars false

/-!
# Cassels, Chapter 9, §6: Lemma 6.4, sums of three squares

**Layer:** classically integral positive definite forms; $f = I_3 = x_0^2 + x_1^2 + x_2^2$ (`sumSq 3`) and binary forms
$g$ ($m = 2$ variables $x_0, x_1$; Cassels' $x_1, x_2$ are shifted to 0-based indices); $g_{ij}$ is Cassels' matrix
(`casselsMat g` $= H/2$); $o^{+}$ is the number of proper automorphs (`AutPlus`).

**Cassels' statement** (Lemma 6.4, p. 150): *Let $a$ be a positive square-free integer and suppose that
$a \not\equiv 3, a \not\equiv 7 \pmod 8$. Then the number $v(a)$ of representations of $a$ as the sum of three squares
satisfies $v(a) = 12\cdot 2^m N$, where $m$ is the number of odd prime divisors of $a$ and $N$ is the number of proper
equivalence classes in a certain genus of positive definite binary forms of determinant $a$.*

**Proves**
* `card_repSet_sumSq_three`: $v(a) = 12\cdot 2^m N$ for squarefree $a \ne 1, 3$, where $N$ (`threeSqClassCount`) is the
  number of proper classes of the forms $g$ with (i)–(iii) (`threeSqGenusSet`);
* `card_repSet_sumSq_three_cassels`: the same under Cassels' hypotheses ($a \not\equiv 3, 7 \pmod 8$, plus $a \ne 1$).

*Proof (Cassels'):* Lemma 6.2 for $f = I_3$ (a genus of one class, $o^{+}(I_3) = 24$, `card_autPlus_sumSq_three`) gives,
for each proper class $[g]$, that the number of primitive representations of $a$ associated with $[g]$ is
$24\rho/o^{+}(g)$ (`sigmaWeight_eq`). The $g$ that occur are those with (i)–(iii) (`assocClass_mem`); for them
$\rho = 2^m$ (6.41: the Chinese remainder theorem, `rhoCount_sumSq_three`) and $o^{+}(g) = 2$
(`card_autPlus_binary`, using $a \ne 1, 3$). For squarefree $a$ all representations are primitive.

*Erratum (Cassels, Lemma 6.4):* the lemma is false for $a = 1$: $v(1) = 6$ while $12\cdot 2^0 N = 12$ for
$N = 1$ (the class of $g = x^2 + y^2$, which has $o^{+}(g) = 4$, not $2$). Cassels' proof asserts $o^{+}(g) = 2$
"since $a \ne 3$" but also needs $a \ne 1$. The hypothesis $a \ne 1$ is added here. The only other exceptional value is
$a = 3$ ($g = 2x^2 + 2xy + 2y^2$ has $o^{+}(g) = 6$), excluded by Cassels' congruence $a \not\equiv 3 \pmod 8$; the
identity proved here holds for every squarefree $a \notin \{1, 3\}$, so the congruence conditions of the book (other
than through $a \ne 3$) are not needed.

*Not proved:* that the set (i)–(iii) is a single genus (Cassels (6.36)–(6.39), via the Hasse–Minkowski symbols and
Theorem 1.2); $N$ is the number of proper classes of the forms satisfying (i)–(iii), which Cassels shows to be one
genus.
-/

noncomputable section

namespace QuadFormsKB.Siegel

/-! ### Part A: $o^{+}(I_3) = 24$ -/

/-- $-I$ is an improper automorph of $I_3$ ($\det(-I_3) = -1$). -/
theorem hasImproperAut_sumSq_three : HasImproperAut (sumSq 3) := by
  refine ⟨-1, ?_, ?_⟩
  · rw [mem_aut_sumSq_iff]
    simp
  · simp [Matrix.det_neg]

/-- $o^{+}(I_3) = 24$: $\lvert O(I_3)\rvert = 2^3\cdot 3! = 48$ (`card_aut_sumSq`) and $-I$ is improper. -/
theorem card_autPlus_sumSq_three : Nat.card (AutPlus (sumSq 3)) = 24 := by
  have h := card_aut_eq_mul (sumSq 3)
  simp only [card_aut_sumSq, hasImproperAut_sumSq_three, ite_true] at h
  norm_num [Nat.factorial] at h
  omega

/-! ### Part B: $o^{+}(g) = 2$ -/

set_option maxHeartbeats 1000000 in
/-- Integer core. -/
theorem aut_core {α β γ p q r s a : ℤ} (ha : 0 < a) (hsf : Squarefree a) (h1 : a ≠ 1) (h3 : a ≠ 3)
    (hΔ : α * γ - β ^ 2 = a) (D : p * s - q * r = 1)
    (E00 : α * p ^ 2 + 2 * β * p * r + γ * r ^ 2 = α)
    (E01 : α * p * q + β * p * s + β * q * r + γ * r * s = β)
    (E11 : α * q ^ 2 + 2 * β * q * s + γ * s ^ 2 = γ) :
    q = 0 ∧ r = 0 ∧ p = s ∧ p * p = 1 := by
  have hα : α ≠ 0 := by
    rintro rfl; nlinarith [sq_nonneg β]
  have hγ : γ ≠ 0 := by
    rintro rfl; nlinarith [sq_nonneg β]
  have L1 : α * (p - s) + 2 * β * r = 0 := by
    linear_combination (s) * E00 + (-r) * E01 + (-(α * p + β * r)) * D
  have L2 : γ * (p - s) - 2 * β * q = 0 := by
    linear_combination (q) * E01 + (-p) * E11 + ((β * q + γ * s)) * D
  have L3 : α * q + γ * r = 0 := by
    linear_combination (-q) * E00 + (p) * E01 + (-(p * β + γ * r)) * D
  have hd : (2 * α * q - β * (p - s)) ^ 2 = (4 - (p + s) ^ 2) * a := by
    rw [← hΔ]
    have e4 : (4 : ℤ) = (p + s) ^ 2 - (p - s) ^ 2 - 4 * q * r := by
      linear_combination (-4) * D
    rw [e4]
    linear_combination (γ * (p - s) - 4 * β * q) * L1 + 4 * α * q * L3 - 2 * β * r * L2
  set d : ℤ := 2 * α * q - β * (p - s) with hddef
  have hsq : (p + s) ^ 2 ≤ 4 := by
    by_contra hcon
    have hcon := not_le.mp hcon
    nlinarith [sq_nonneg d]
  have hb1 : p + s ≤ 2 := by nlinarith
  have hb2 : -2 ≤ p + s := by nlinarith
  have unit_sq : ∀ e : ℤ, e * e ∣ a → e ^ 2 = 1 := by
    intro e he
    rcases Int.isUnit_iff.mp (hsf e he) with h | h <;> simp [h]
  have hmain : p + s = 2 ∨ p + s = -2 := by
    by_contra hcon
    have hcon := not_or.mp hcon
    have h3' : (p + s = -1 ∨ p + s = 0 ∨ p + s = 1) := by omega
    rcases h3' with h | h | h
    · -- t = -1 : d^2 = 3a
      have e : d ^ 2 = 3 * a := by rw [hd, h]; ring
      have h3d : (3 : ℤ) ∣ d := Int.prime_three.dvd_of_dvd_pow (n := 2) ⟨a, e⟩
      obtain ⟨e', he'⟩ := h3d
      have : a = 3 * e' ^ 2 := by rw [he'] at e; nlinarith
      have := unit_sq e' ⟨3, by rw [this]; ring⟩
      apply h3; rw [‹a = 3 * e' ^ 2›, this]; norm_num
    · have e : d ^ 2 = 4 * a := by rw [hd, h]; ring
      have h2d : (2 : ℤ) ∣ d := Int.prime_two.dvd_of_dvd_pow (n := 2) ⟨2 * a, by rw [e]; ring⟩
      obtain ⟨e', he'⟩ := h2d
      have : a = e' ^ 2 := by rw [he'] at e; nlinarith
      have := unit_sq e' ⟨1, by rw [this]; ring⟩
      apply h1; rw [‹a = e' ^ 2›, this]
    · have e : d ^ 2 = 3 * a := by rw [hd, h]; ring
      have h3d : (3 : ℤ) ∣ d := Int.prime_three.dvd_of_dvd_pow (n := 2) ⟨a, e⟩
      obtain ⟨e', he'⟩ := h3d
      have : a = 3 * e' ^ 2 := by rw [he'] at e; nlinarith
      have := unit_sq e' ⟨3, by rw [this]; ring⟩
      apply h3; rw [‹a = 3 * e' ^ 2›, this]; norm_num
  have hd0 : d = 0 := by
    have : d ^ 2 = 0 := by rw [hd]; rcases hmain with h | h <;> rw [h] <;> norm_num
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have hr2 : 2 * a * r = 0 := by
    linear_combination (-α) * hd0 + 2 * α * L3 - β * L1 - 2 * r * hΔ
  have hq2 : 2 * a * q = 0 := by
    linear_combination γ * hd0 + β * L2 - 2 * q * hΔ
  have h2a : 2 * a ≠ 0 := by positivity
  have hr : r = 0 := (mul_eq_zero.mp hr2).resolve_left h2a
  have hq : q = 0 := (mul_eq_zero.mp hq2).resolve_left h2a
  have hu : p = s := by
    have : α * (p - s) = 0 := by rw [hr] at L1; linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hα
    · linarith
  refine ⟨hq, hr, hu, ?_⟩
  subst hu
  rcases hmain with h | h <;> nlinarith

/-- **The proper automorphs of a binary form** $g$ classically integral with $\det(g_{ij}) = a$, $a > 0$ squarefree,
$a \ne 1, 3$: $O^{+}(g) = \{\pm I\}$, so $o^{+}(g) = 2$ (Cassels, p. 151: *$o^{+}(g) = 2$ since $a \ne 3$*; the
case $a = 1$, $g = x^2 + y^2$ has $o^{+} = 4$ and $a = 3$, $g = 2x^2 + 2xy + 2y^2$ has $o^{+} = 6$). -/
theorem stabSet_binary {g : QuadForm ℤ 2} {a : ℕ} (ha0 : 0 < a) (hsf : Squarefree a) (h1 : a ≠ 1) (h3 : a ≠ 3)
    (hdet : (casselsMat g).det = a) :
    stabSet (casselsMat g) = {1, -1} := by
  have hG := casselsMat_isSymm g
  have hsfZ : Squarefree (a : ℤ) := Int.squarefree_natCast.mpr hsf
  ext σ
  simp only [stabSet, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hd, hσ⟩
    have e00 := congrFun (congrFun hσ 0) 0
    have e01 := congrFun (congrFun hσ 0) 1
    have e11 := congrFun (congrFun hσ 1) 1
    have g10 : casselsMat g 1 0 = casselsMat g 0 1 := (hG.apply 1 0).symm
    rw [Matrix.det_fin_two] at hdet hd
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at e00 e01 e11
    rw [g10] at e00 e01 e11 hdet
    obtain ⟨hq, hr, hps, hpp⟩ := aut_core (α := casselsMat g 0 0) (β := casselsMat g 0 1)
      (γ := casselsMat g 1 1) (p := σ.val 0 0) (q := σ.val 0 1) (r := σ.val 1 0) (s := σ.val 1 1)
      (a := a) (by exact_mod_cast ha0) hsfZ (by exact_mod_cast h1) (by exact_mod_cast h3)
      (by linear_combination hdet) (by linear_combination hd)
      (by linear_combination e00) (by linear_combination e01) (by linear_combination e11)
    have hp : σ.val 0 0 = 1 ∨ σ.val 0 0 = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hpp
    rcases hp with hp | hp
    · left; ext i j; fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, ← hps]
    · right; ext i j; fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, ← hps]
  · rintro (rfl | rfl)
    · simp
    · simp [Matrix.det_neg]

/-- $o^{+}(g) = 2$ (Cassels, p. 151). -/
theorem card_autPlus_binary {g : QuadForm ℤ 2} (hg : IsClassicallyIntegral g) {a : ℕ} (ha0 : 0 < a)
    (hsf : Squarefree a) (h1 : a ≠ 1) (h3 : a ≠ 3) (hdet : (casselsMat g).det = a) :
    Nat.card (AutPlus g) = 2 := by
  rw [← card_stabSet hg, stabSet_binary ha0 hsf h1 h3 hdet, Nat.card_coe_set_eq]
  rw [Set.ncard_pair]
  intro h
  have := congrArg (fun u : GL (Fin 2) ℤ => u.val 0 0) h
  simp at this

/-! ### Part C: counting the solutions of $\mathbf v\mathbf v^{\mathsf T} \equiv -G \pmod a$ -/

/-- The solutions $\mathbf v \in (\mathbb Z/n)^2$ of $v_iv_j + G_{ij} = 0$ for all $i, j$. -/
def solSet (n : ℕ) (G : Matrix (Fin 2) (Fin 2) ℤ) : Set (Fin 2 → ZMod n) :=
  {v | ∀ i j, v i * v j + (G i j : ZMod n) = 0}

/-- **CRT:** the solutions modulo $mn$ ($m, n$ coprime) are the pairs of solutions. -/
def solSetCRT {m n : ℕ} (h : Nat.Coprime m n) (G : Matrix (Fin 2) (Fin 2) ℤ) :
    solSet (m * n) G ≃ solSet m G × solSet n G where
  toFun v := (⟨fun i => (ZMod.chineseRemainder h (v.1 i)).1, fun i j => by
      have h' := congrArg (ZMod.chineseRemainder h) (v.2 i j)
      rw [map_add, map_mul, map_intCast, map_zero] at h'
      simpa using congrArg Prod.fst h'⟩,
    ⟨fun i => (ZMod.chineseRemainder h (v.1 i)).2, fun i j => by
      have h' := congrArg (ZMod.chineseRemainder h) (v.2 i j)
      rw [map_add, map_mul, map_intCast, map_zero] at h'
      simpa using congrArg Prod.snd h'⟩)
  invFun w := ⟨fun i => (ZMod.chineseRemainder h).symm (w.1.1 i, w.2.1 i), fun i j => by
    apply (ZMod.chineseRemainder h).injective
    rw [map_add, map_mul, map_intCast, map_zero]
    simp only [RingEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · simpa using w.1.2 i j
    · simpa using w.2.2 i j⟩
  left_inv v := by
    ext i
    simp
  right_inv w := by
    ext i <;> simp

theorem card_solSet_mul {m n : ℕ} (h : Nat.Coprime m n) (G : Matrix (Fin 2) (Fin 2) ℤ) :
    Nat.card (solSet (m * n) G) = Nat.card (solSet m G) * Nat.card (solSet n G) := by
  rw [Nat.card_congr (solSetCRT h G), Nat.card_prod]

/-- Over $\mathbb Z/p$: a nonzero solution forces exactly $\{\pm v\}$. -/
theorem card_solSet_prime {p : ℕ} [Fact p.Prime] {G : Matrix (Fin 2) (Fin 2) ℤ} {v : Fin 2 → ZMod p}
    (hv : v ∈ solSet p G) (hnz : ∃ i j, (G i j : ZMod p) ≠ 0) :
    Nat.card (solSet p G) = if p = 2 then 1 else 2 := by
  obtain ⟨i0, j0, hij⟩ := hnz
  have hk : ∃ k, v k ≠ 0 := by
    by_contra hcon
    have hcon : ∀ k, v k = 0 := fun k => by_contra fun h => hcon ⟨k, h⟩
    apply hij
    have := hv i0 j0
    rw [hcon i0, hcon j0] at this
    simpa using this
  obtain ⟨k, hk⟩ := hk
  have hset : solSet p G = {v, -v} := by
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hw
      have hww : ∀ i j, w i * w j = v i * v j := fun i j => by
        have h1 := hw i j
        have h2 := hv i j
        linear_combination h1 - h2
      have hk2 : w k ^ 2 = v k ^ 2 := by rw [sq, sq]; exact hww k k
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hk2 with h | h
      · left
        funext i
        have := hww i k
        rw [h] at this
        exact mul_right_cancel₀ hk this
      · right
        funext i
        have := hww i k
        rw [h] at this
        have : (w i + v i) * v k = 0 := by linear_combination -this
        have := (mul_eq_zero.mp this).resolve_right hk
        simp only [Pi.neg_apply]
        linear_combination this
    · rintro (rfl | rfl)
      · exact hv
      · intro i j
        have := hv i j
        simp only [Pi.neg_apply, neg_mul_neg]
        exact this
  rw [hset, Nat.card_coe_set_eq]
  by_cases hp2 : p = 2
  · subst hp2
    have : -v = v := by
      funext i
      simp only [Pi.neg_apply]
      have : (2 : ZMod 2) = 0 := rfl
      linear_combination (-(v i)) * this
    rw [this]; simp
  · have hne : v ≠ -v := by
      intro h
      have := congrFun h k
      simp only [Pi.neg_apply] at this
      have h2 : (2 : ZMod p) * v k = 0 := by linear_combination this
      rcases mul_eq_zero.mp h2 with h | h
      · have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
        rw [ZMod.natCast_eq_zero_iff] at this
        exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)
      · exact hk h
    rw [Set.ncard_pair hne]
    simp [hp2]

theorem card_solSet_one (G : Matrix (Fin 2) (Fin 2) ℤ) : Nat.card (solSet 1 G) = 1 := by
  have : Unique (solSet 1 G) :=
    ⟨⟨⟨fun _ => 0, fun i j => Subsingleton.elim _ _⟩⟩, fun w => Subtype.ext (Subsingleton.elim _ _)⟩
  exact Nat.card_unique

/-- The count over a squarefree modulus is the product over its prime factors. -/
theorem card_solSet_finset (G : Matrix (Fin 2) (Fin 2) ℤ) :
    ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ (∃ v : Fin 2 → ZMod p, v ∈ solSet p G) ∧
        ∃ i j, (G i j : ZMod p) ≠ 0) →
      Nat.card (solSet (∏ p ∈ s, p) G) = ∏ p ∈ s, (if p = 2 then 1 else 2) := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simpa using card_solSet_one G
  | insert q s hq ih =>
    intro hs
    have hqp : q.Prime := (hs q (Finset.mem_insert_self _ _)).1
    have hsp : ∀ p ∈ s, p.Prime ∧ (∃ v : Fin 2 → ZMod p, v ∈ solSet p G) ∧
        ∃ i j, (G i j : ZMod p) ≠ 0 := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert hq, Finset.prod_insert hq]
    have hcop : Nat.Coprime q (∏ p ∈ s, p) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      exact (Nat.coprime_primes hqp (hsp p hp).1).mpr (fun h => hq (h ▸ hp))
    rw [card_solSet_mul hcop, ih hsp]
    have : Fact q.Prime := ⟨hqp⟩
    obtain ⟨-, ⟨v, hv⟩, hnz⟩ := hs q (Finset.mem_insert_self _ _)
    rw [card_solSet_prime hv hnz]

/-- **The number of solutions of $\mathbf v\mathbf v^{\mathsf T} \equiv -G \pmod a$** for $a$ squarefree: $2^{m}$,
$m$ the number of odd prime divisors of $a$. -/
theorem card_solSet {a : ℕ} (_ha0 : 0 < a) (hsf : Squarefree a) {G : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : G.det = a) (hv : ∃ v : Fin 2 → ℤ, ∀ i j, (a : ℤ) ∣ v i * v j + G i j) :
    Nat.card (solSet a G) = 2 ^ (a.primeFactors.filter (· ≠ 2)).card := by
  obtain ⟨v, hv⟩ := hv
  have hcond : ∀ p : ℕ, p.Prime → p ∣ a →
      (∃ w : Fin 2 → ZMod p, w ∈ solSet p G) ∧ ∃ i j, (G i j : ZMod p) ≠ 0 := by
    intro p hp hpa
    refine ⟨⟨fun i => (v i : ZMod p), fun i j => ?_⟩, ?_⟩
    · have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
        ((Int.natCast_dvd_natCast.mpr hpa).trans (hv i j))
      push_cast at this
      exact this
    · by_contra hcon
      have hcon : ∀ i j, (G i j : ZMod p) = 0 := fun i j => by_contra fun h => hcon ⟨i, j, h⟩
      have hd : ∀ i j, (p : ℤ) ∣ G i j := fun i j =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (hcon i j)
      obtain ⟨x00, h00⟩ := hd 0 0
      obtain ⟨x01, h01⟩ := hd 0 1
      obtain ⟨x10, h10⟩ := hd 1 0
      obtain ⟨x11, h11⟩ := hd 1 1
      rw [Matrix.det_fin_two, h00, h01, h10, h11] at hdet
      have : (p : ℤ) * p ∣ a := ⟨x00 * x11 - x01 * x10, by rw [← hdet]; ring⟩
      have hsfZ : Squarefree (a : ℤ) := Int.squarefree_natCast.mpr hsf
      have := Int.isUnit_iff.mp (hsfZ _ this)
      have hp1 := hp.one_lt
      rcases this with h | h <;> nlinarith
  have h := card_solSet_finset G a.primeFactors (fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp, hcond p (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)⟩)
  rw [Nat.prod_primeFactors_of_squarefree hsf] at h
  rw [h, Finset.prod_ite]
  simp [Finset.prod_const]

/-! ### Part D: $\rho(I_3, g) = 2^{m}$ -/

/-- For a symmetric ternary $A$: $\det(\mathrm{assocMat}\,A_{00}\,A) = A_{00}\det A$. -/
theorem det_assocMat_three {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : A.IsSymm) :
    (assocMat (A 0 0) A).det = A 0 0 * A.det := by
  have h10 := hA.apply 1 0
  have h20 := hA.apply 2 0
  have h21 := hA.apply 2 1
  rw [Matrix.det_fin_two, Matrix.det_fin_three]
  simp only [assocMat, Matrix.of_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  simp only [h10, h20, h21]
  ring

/-- `hMat` has determinant $1$ when $\det G = a$ (ternary case). -/
theorem det_hMat_two {a : ℕ} (ha0 : 0 < a) {c : Fin 2 → ℤ} {G : Matrix (Fin 2) (Fin 2) ℤ} (hG : G.IsSymm)
    (hdiv : ∀ i j, (a : ℤ) ∣ c i * c j + G i j) (hdet : G.det = a) : (hMat (a : ℤ) c G).det = 1 := by
  have h := det_assocMat_three (hMat_isSymm (a := (a : ℤ)) (c := c) hG)
  rw [hMat_zero_zero, assocMat_hMat hdiv, hdet] at h
  have ha : (a : ℤ) ≠ 0 := by exact_mod_cast ha0.ne'
  have h' : (a : ℤ) * (hMat (a : ℤ) c G).det = a * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel₀ ha h'

/-- `hMat` is positive definite. -/
theorem isPosDefInt_hMat {a : ℕ} (ha0 : 0 < a) {c : Fin 2 → ℤ} {g : QuadForm ℤ 2} (hg : IsClassicallyIntegral g)
    (hpd : IntQF.PosDef g) (hdiv : ∀ i j, (a : ℤ) ∣ c i * c j + casselsMat g i j) :
    Hermite.IsPosDefInt (hMat (a : ℤ) c (casselsMat g)) := by
  refine ⟨hMat_isSymm (casselsMat_isSymm g), fun x hx => ?_⟩
  have key := complete_square (hMat_isSymm (a := (a : ℤ)) (c := c) (casselsMat_isSymm g)) x
  rw [hMat_zero_zero, assocMat_hMat hdiv, ← eval_eq_casselsMat hg] at key
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha0
  by_cases ht : Fin.tail x = 0
  · have hx0 : x 0 ≠ 0 := by
      intro h0
      apply hx
      funext i
      refine Fin.cases h0 (fun j => ?_) i
      exact congrFun ht j
    have h1 : (hMat (a : ℤ) c (casselsMat g) *ᵥ x) 0 = a * x 0 := by
      have hx1 : ∀ j : Fin 2, x j.succ = 0 := fun j => congrFun ht j
      simp [mulVec, dotProduct, Fin.sum_univ_succ, hx1]
    rw [h1, ht] at key
    have : (a : ℤ) * x 0 ≠ 0 := mul_ne_zero haZ.ne' hx0
    have hpos : 0 < ((a : ℤ) * x 0) ^ 2 := by positivity
    have h0 : g.eval 0 = 0 := by simp [eval_eq_casselsMat hg]
    rw [h0] at key
    by_contra hneg
    nlinarith
  · have := hpd _ ht
    by_contra hneg
    nlinarith [sq_nonneg ((hMat (a : ℤ) c (casselsMat g) *ᵥ x) 0)]

/-- The genus of $I_3$ contains `ofGram (hMat a c G)` whenever $a \mid c_ic_j + g_{ij}$ (Cassels, p. 151: *$h$
is positive definite of determinant $1$, hence equivalent to $x_1^2 + x_2^2 + x_3^2$*). -/
theorem sameGenus_hMat {a : ℕ} (ha0 : 0 < a) {c : Fin 2 → ℤ} {g : QuadForm ℤ 2} (hg : IsClassicallyIntegral g)
    (hpd : IntQF.PosDef g) (hdet : (casselsMat g).det = a)
    (hdiv : ∀ i j, (a : ℤ) ∣ c i * c j + casselsMat g i j) :
    SameGenus (sumSq 3) (ofGram (hMat (a : ℤ) c (casselsMat g))) := by
  obtain ⟨T, hT⟩ := Hermite.unimodular_posDef_equiv_one 3 (by norm_num) _ (isPosDefInt_hMat ha0 hg hpd hdiv)
    (det_hMat_two ha0 (casselsMat_isSymm g) hdiv hdet)
  refine IntEquiv.sameGenus (IsometricGL.symm (⟨T, fun x => ?_⟩ : IntEquiv (ofGram (hMat (a : ℤ) c (casselsMat g))) (sumSq 3)))
  rw [eval_ofGram (hMat_isSymm (casselsMat_isSymm g)), dotProduct_conj, hT, eval_sumSq]
  simp [dotProduct, sq]

/-- **Cassels' $\rho(I_3, g) = 2^{m}$** (6.41), $m$ the number of odd prime divisors of $a$: for $g$ satisfying
(i)–(iii) the congruence classes $\mathbf c \bmod a$ counted by $\rho$ are exactly the solutions of
$c_ic_j + g_{ij} \equiv 0 \pmod a$ (the form $h$ is automatically in the genus of $I_3$, being positive definite of
determinant $1$), and there are $2^m$ of them (Chinese remainder theorem). -/
theorem rhoCount_sumSq_three {a : ℕ} (ha0 : 0 < a) (hsf : Squarefree a) {g : QuadForm ℤ 2}
    (hg : IsClassicallyIntegral g) (hpd : IntQF.PosDef g) (hdet : (casselsMat g).det = a)
    (hv : ∃ v : Fin 2 → ℤ, ∀ i j, (a : ℤ) ∣ v i * v j + casselsMat g i j) :
    rhoCount (sumSq 3) a (casselsMat g) = 2 ^ (a.primeFactors.filter (· ≠ 2)).card := by
  have : NeZero a := ⟨ha0.ne'⟩
  rw [← card_solSet ha0 hsf hdet hv, rhoCount]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  show _ ↔ w ∈ solSet a (casselsMat g)
  simp only [solSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c, hc, hdiv, -⟩ i j
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ a).mpr (hdiv i j)
    push_cast at this
    rw [← hc i, ← hc j]
    exact this
  · intro hw
    have hdiv : ∀ i j, (a : ℤ) ∣ canLift w i * canLift w j + casselsMat g i j := fun i j => by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ a).mp ?_
      push_cast
      rw [cast_canLift, cast_canLift]
      exact hw i j
    exact ⟨canLift w, cast_canLift w, hdiv, sameGenus_hMat ha0 hg hpd hdet hdiv⟩

/-! ### Part E: the forms $g$ and the assembly -/

/-- $I_n$ is classically integral. -/
theorem ci_sumSq (n : ℕ) : IsClassicallyIntegral (sumSq n) :=
  ⟨1, Matrix.isSymm_one, fun x => by simp [gramForm, eval_sumSq, dotProduct, sq]⟩

/-- Cassels' matrix of $I_n$ is $1$. -/
theorem casselsMat_sumSq (n : ℕ) : casselsMat (sumSq n) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [casselsMat, hessian_sumSq]
  · simp [casselsMat, hessian_sumSq, h]

/-- **Cassels' set (i)–(iii)** (Ch. 9, §6, pp. 150–151) of binary forms $g$ occurring in the application of Lemma 6.2
to $f = x_0^2 + x_1^2 + x_2^2$ and $a$: $g$ is classically integral ($g = \sum g_{ij}x_ix_j$ with $g_{ij} \in \mathbb Z$),
(i) $\det(g_{ij}) = a$, (ii) $g$ is positive definite, (iii) there are integers $v_0, v_1$ with
$a \mid v_iv_j + g_{ij}$ for all $i, j$ (equivalently, $(v_0x_0 + v_1x_1)^2 + g(\mathbf x)$ is divisible by $a$ as a
classically integral form, (6.35)). -/
def threeSqGenusSet (a : ℕ) : Set (QuadForm ℤ 2) :=
  {g | IsClassicallyIntegral g ∧ IntQF.PosDef g ∧ (casselsMat g).det = a ∧
    ∃ v : Fin 2 → ℤ, ∀ i j, (a : ℤ) ∣ v i * v j + casselsMat g i j}

/-- **The number $N$ of Lemma 6.4:** the number of proper equivalence classes of the forms of `threeSqGenusSet a`. -/
def threeSqClassCount (a : ℕ) : ℕ := Nat.card (pclassOf '' threeSqGenusSet a)

/-- Every primitive representation of $a$ by a form $f_0$ of the genus of $I_3$ is associated with the proper class
of a form satisfying (i)–(iii) (Cassels, p. 150: *the forms $g$ which occur are those with ...*). -/
theorem assocClass_mem {f0 : QuadForm ℤ 3} (hf0 : IsClassicallyIntegral f0) (hpd0 : IntQF.PosDef f0)
    (hdet0 : (casselsMat f0).det = 1) {a : ℕ} {b : Fin 3 → ℤ} (hb : b ∈ primRepSet f0 a) :
    ∃ g ∈ threeSqGenusSet a, assocClass f0 b = pclassOf g := by
  have hex : ∃ T : GL (Fin 3) ℤ, T.val.det = 1 ∧ T.val *ᵥ Pi.single 0 1 = b := by
    obtain ⟨T, hT, hTb⟩ := exists_sl_first_of_gcd (n := 3) (by omega) b hb.1
    exact ⟨T, hT, by simpa only [Fin.zero_eta] using hTb⟩
  obtain ⟨hT1, hT2⟩ := Tsel_spec hex
  have hev : f0.eval b = a := hb.2
  set T := (Tsel b).val with hTdef
  set A := Tᵀ * casselsMat f0 * T with hAdef
  have hA : A.IsSymm := isSymm_conj (casselsMat_isSymm f0) T
  have h00 : A 0 0 = a := by rw [hAdef, ← eval_first_col hf0, hT2, hev]
  have hGs : (assocMat (a : ℤ) A).IsSymm := assocMat_isSymm hA _
  have hcl : assocClass f0 b = pclassOf (ofGram (assocMat (a : ℤ) A)) := by
    rw [assocClass_eq f0 hex, assocGram_eq, hev]
  refine ⟨ofGram (assocMat (a : ℤ) A), ⟨ci_ofGram hGs, ?_, ?_, ?_⟩, hcl⟩
  · -- positive definite
    have hP0 : Hermite.IsPosDefInt (casselsMat f0) :=
      ⟨casselsMat_isSymm f0, fun x hx => by rw [← eval_eq_casselsMat hf0]; exact hpd0 x hx⟩
    have hP : Hermite.IsPosDefInt A := hP0.conj (Tsel b)
    have hS := hP.schur
    have hSA : Hermite.schur A = assocMat (a : ℤ) A := by
      ext i j
      simp only [Hermite.schur, Matrix.sub_apply, Matrix.smul_apply, submatrix_apply, vecMulVec_apply,
        smul_eq_mul, assocMat, Matrix.of_apply, Hermite.colT, Hermite.rowT, h00]
      rw [hA.apply i.succ 0]
    rw [hSA] at hS
    intro y hy
    rw [eval_ofGram hGs]
    exact hS.2 y hy
  · rw [casselsMat_ofGram hGs]
    have h := det_assocMat_three hA
    rw [h00] at h
    rw [h, hAdef, det_mul, det_mul, det_transpose, hT1, hdet0]
    simp
  · refine ⟨fun j => A 0 j.succ, fun i j => ?_⟩
    rw [casselsMat_ofGram hGs]
    exact ⟨A i.succ j.succ, by simp only [assocMat, Matrix.of_apply]; ring⟩

/-- The genus of $I_3$ is a single proper class. -/
theorem pgenusClasses_sumSq_three : pgenusClasses (sumSq 3) = {pclassOf (sumSq 3)} := by
  ext D
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨f', hf', hg⟩
    rw [← hf']
    have h1 := sameGenus_sumSq_intEquiv (n := 3) (by norm_num) hg
    have h2 := (intEquiv_iff_properIntEquiv_of_hasImproperAut hasImproperAut_sumSq_three f').mp h1
    exact (pclassOf_eq_pclassOf_iff.mpr h2).symm
  · rintro rfl
    exact ⟨sumSq 3, rfl, SameGenus.refl _⟩

/-- **The representation count attached to a class of $g$:** for $g$ satisfying (i)–(iii), the number of primitive
representations of $a$ by (the representative of the class of) $I_3$ associated with the class of $g$ is
$24\cdot 2^m / 2 = 12\cdot 2^m$ (Lemma 6.2 for one class, $\rho = 2^m$, $o^{+}(I_3) = 24$, $o^{+}(g) = 2$). -/
theorem fiber_card {a : ℕ} (hsf : Squarefree a) (h1 : a ≠ 1) (h3 : a ≠ 3) {g : QuadForm ℤ 2}
    (hgs : g ∈ threeSqGenusSet a) :
    Nat.card {b // b ∈ primRepSet (pclassOf (sumSq 3)).out a ∧
        assocClass (pclassOf (sumSq 3)).out b = pclassOf g} =
      12 * 2 ^ (a.primeFactors.filter (· ≠ 2)).card := by
  obtain ⟨hg, hpd, hdet, hv⟩ := hgs
  have ha0 : 0 < a := hsf.ne_zero.bot_lt
  have key := sigmaWeight_eq (m := 2) (by norm_num) (ci_sumSq 3) posDef_sumSq ha0 hg hpd
    (by rw [hdet, casselsMat_sumSq, det_one]; simp)
  rw [rhoCount_sumSq_three ha0 hsf hg hpd hdet hv, card_autPlus_binary hg ha0 hsf h1 h3 hdet] at key
  unfold sigmaWeight at key
  rw [pgenusClasses_sumSq_three, finsum_mem_singleton] at key
  have hs : SameGenus (sumSq 3) (pclassOf (sumSq 3)).out :=
    mem_pgenusClasses_iff_out.mp (by rw [pgenusClasses_sumSq_three]; rfl)
  have hA : Nat.card (AutPlus (pclassOf (sumSq 3)).out) = 24 := by
    rw [← card_autPlus_eq_of_intEquiv (sameGenus_sumSq_intEquiv (n := 3) (by norm_num) hs),
      card_autPlus_sumSq_three]
  rw [hA] at key
  set n := Nat.card {b // b ∈ primRepSet (pclassOf (sumSq 3)).out a ∧
        assocClass (pclassOf (sumSq 3)).out b = pclassOf g} with hn
  have : (n : ℝ) = 12 * 2 ^ (a.primeFactors.filter (· ≠ 2)).card := by
    push_cast at key
    field_simp at key
    linarith
  exact_mod_cast this

/-- **Cassels, Lemma 6.4** (Ch. 9, p. 150): *the number $v(a)$ of representations of $a$ as the sum of three squares
satisfies $v(a) = 12\cdot 2^m N$, where $m$ is the number of odd prime divisors of $a$ and $N$ is the number of proper
equivalence classes in a certain genus of positive definite binary forms of determinant $a$.*

Hypotheses: `hsf` ($a$ is squarefree), `h1` ($a \ne 1$) and `h3` ($a \ne 3$). Conclusion: with
$v(a) = $ `Nat.card (repSet (sumSq 3) a)` (the number of $(x_0, x_1, x_2) \in \mathbb Z^3$ with $x_0^2 + x_1^2 + x_2^2 = a$),
$m = $ `(a.primeFactors.filter (· ≠ 2)).card` and $N = $ `threeSqClassCount a`, the number of proper classes of the binary
forms $g$ with (i) $\det(g_{ij}) = a$, (ii) $g$ positive definite, (iii) $a \mid v_iv_j + g_{ij}$ for some integers
$v_0, v_1$ (`threeSqGenusSet`). Unconditional (no assumed inputs).

*Erratum:* Cassels' statement is false for $a = 1$ ($v(1) = 6 \ne 12$); the hypothesis $a \ne 1$ is added. Cassels'
$a \not\equiv 3 \pmod 8$ is only used here through $a \ne 3$ (for $a = 3$, $o^{+}(g) = 6$ for
$g = 2x^2 + 2xy + 2y^2$), and $a \not\equiv 7 \pmod 8$ is not needed; see `card_repSet_sumSq_three_cassels`.
*Note:* the library does not prove that the forms (i)–(iii) form a single genus (Cassels (6.36)–(6.39)); $N$ counts
the proper classes of all forms satisfying (i)–(iii). -/
@[kb "cassels1978" "Ch. 9, Lemma 6.4, p. 150 (sums of three squares)"]
theorem card_repSet_sumSq_three {a : ℕ} (hsf : Squarefree a) (h1 : a ≠ 1) (h3 : a ≠ 3) :
    Nat.card (repSet (sumSq 3) a) =
      12 * 2 ^ (a.primeFactors.filter (· ≠ 2)).card * threeSqClassCount a := by
  classical
  have ha0 : 0 < a := hsf.ne_zero.bot_lt
  have hsfZ : Squarefree (a : ℤ) := Int.squarefree_natCast.mpr hsf
  set f0 := (pclassOf (sumSq 3)).out with hf0def
  have hs : SameGenus (sumSq 3) f0 :=
    mem_pgenusClasses_iff_out.mp (by rw [pgenusClasses_sumSq_three]; rfl)
  have hci : IsClassicallyIntegral f0 := hs.isClassicallyIntegral (ci_sumSq 3)
  have hpd : IntQF.PosDef f0 := hs.posDef posDef_sumSq
  have hdet : (casselsMat f0).det = 1 := by
    rw [← casselsMat_det_eq (ci_sumSq 3) hci hs, casselsMat_sumSq, det_one]
  have hequiv : IntEquiv (sumSq 3) f0 := sameGenus_sumSq_intEquiv (n := 3) (by norm_num) hs
  -- all representations are primitive
  have hset : primRepSet f0 a = repSet f0 a := by
    ext b
    exact ⟨fun h => h.2, fun h => ⟨gcd_eq_one_of_squarefree hsfZ h, h⟩⟩
  have hrep : Nat.card (repSet (sumSq 3) a) = Nat.card (primRepSet f0 a) := by
    rw [hset]
    exact repNum_eq_of_intEquiv hequiv a
  have hPfin : (primRepSet f0 a).Finite := (IntQF.PosDef.repSet_finite hpd a).subset fun b hb => hb.2
  set φ : (Fin 3 → ℤ) → PClass 2 := assocClass f0 with hφ
  -- every nonempty fibre has `12 * 2^m` elements
  have hfib : ∀ C ∈ hPfin.toFinset.image φ,
      (hPfin.toFinset.filter (fun b => φ b = C)).card = 12 * 2 ^ (a.primeFactors.filter (· ≠ 2)).card := by
    intro C hC
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨g, hg, hbg⟩ := assocClass_mem hci hpd hdet ((Set.Finite.mem_toFinset _).mp hb)
    rw [← fiber_card hsf h1 h3 hg, ← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hφ, hbg]
    exact Iff.rfl
  have himage : (↑(hPfin.toFinset.image φ) : Set (PClass 2)) = pclassOf '' threeSqGenusSet a := by
    ext C
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨g, hg, hbg⟩ := assocClass_mem hci hpd hdet hb
      exact ⟨g, hg, hbg.symm⟩
    · rintro ⟨g, hg, rfl⟩
      have hpos : 0 < Nat.card {b // b ∈ primRepSet f0 a ∧ assocClass f0 b = pclassOf g} := by
        rw [fiber_card hsf h1 h3 hg]; positivity
      obtain ⟨⟨b, hb⟩⟩ := Nat.card_pos_iff.mp hpos |>.1
      exact ⟨b, hb.1, hb.2⟩
  rw [hrep, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hPfin,
    Finset.card_eq_sum_card_image φ, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    threeSqClassCount, Nat.card_coe_set_eq, ← himage, Set.ncard_coe_finset, mul_comm]

/-- **Cassels, Lemma 6.4** (Ch. 9, p. 150) with Cassels' hypotheses: `hsf` ($a$ squarefree), `h1` ($a \ne 1$, *added*:
Cassels' statement fails for $a = 1$), `h38` ($a \not\equiv 3 \pmod 8$) and `_h78` ($a \not\equiv 7 \pmod 8$, unused). The
conclusion is that of `card_repSet_sumSq_three`: $v(a) = 12\cdot 2^m N$. -/
@[kb "cassels1978" "Ch. 9, Lemma 6.4, p. 150 (with Cassels' congruence hypotheses)"]
theorem card_repSet_sumSq_three_cassels {a : ℕ} (hsf : Squarefree a) (h1 : a ≠ 1) (h38 : a % 8 ≠ 3)
    (_h78 : a % 8 ≠ 7) :
    Nat.card (repSet (sumSq 3) a) =
      12 * 2 ^ (a.primeFactors.filter (· ≠ 2)).card * threeSqClassCount a :=
  card_repSet_sumSq_three hsf h1 (fun h => h38 (by omega))

end QuadFormsKB.Siegel
