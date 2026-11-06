import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Defs.Binary
import QuadFormsKB.Siegel.Theta

/-!
# Saha–Hanke, the non-trivial three-term theta relation (Lemma 6.2)

Source: R. Saha and J. Hanke, *On three-term linear relations for theta series of positive-definite
binary quadratic forms*, arXiv:2307.00747v1, §6.3, Lemma 6.2, pp. 17–18 (bib key
`hanke2023threeterm`).

For every integer $c > 0$, with
$$Q_1 \sim_{\mathbb{Z}} c(x^2 + xy + y^2),\quad Q_2 \sim_{\mathbb{Z}} 4c(x^2 + xy + y^2),\quad
Q_3 \sim_{\mathbb{Z}} c(x^2 + 3y^2),$$
$$\tfrac13 \theta_{Q_1} + \tfrac23 \theta_{Q_2} = \theta_{Q_3},$$
i.e. $r_{Q_1}(m) + 2 r_{Q_2}(m) = 3 r_{Q_3}(m)$ for every $m \ge 0$.

## Proof

We follow the source's bijections. Write $E(u,v) = u^2 + uv + v^2$.
* $(a, b) \mapsto (a - b, 2b)$ is a bijection from $R_{x^2+3y^2}(m)$ onto the representations
  $(u, v) \in R_E(m)$ with $v$ even (since $E(a-b, 2b) = a^2 + 3b^2$).
* $(u, v) \mapsto (2u, 2v)$ is a bijection from $R_{4E}(m)$ onto the representations in $R_E(m)$
  with $u$ and $v$ both even.
* The automorphisms $(u,v) \mapsto (v,u)$ and $(u,v) \mapsto (-u-v, v)$ of $E$ permute the three
  conditions "$v$ even", "$u$ even", "$u + v$ even" (this is the source's cyclic group $G$).
* Every $(u, v)$ satisfies exactly one of the three conditions, or all three (when $u, v$ are both
  even).

Counting, $r_E(m) + 2 r_{4E}(m) = 3 r_{x^2+3y^2}(m)$. The source splits instead by the parity of
$a \equiv b \pmod 2$ for a representation $m = a^2 + 3b^2$; the bijections are the same.
*Update (proof gap):* the printed proof fixes $m = a^2 + 3b^2$ ("it suffices to show …"), which
leaves out $m$ not represented by $x^2 + 3y^2$. The counting argument here covers every $m$.
-/

namespace QuadFormsKB.Hanke2023ThreeTerm

open QuadFormsKB QuadFormsKB.Siegel

/-- The representation number of a binary form, counted on $\mathbb{Z} \times \mathbb{Z}$:
$r_Q(m) = \#\{(x, y) \in \mathbb{Z}^2 : Q(x, y) = m\}$. -/
theorem repNum_eq_card_prod (Q : BinQF) (m : ℤ) :
    repNum Q m = Nat.card {p : ℤ × ℤ // Q.eval p.1 p.2 = m} := by
  unfold repNum repSet
  refine Nat.card_congr
    { toFun := fun x => ⟨(x.1 0, x.1 1), by
        have h := x.2
        simp only [Set.mem_ofPred_eq] at h
        have hx : (![x.1 0, x.1 1] : Fin 2 → ℤ) = x.1 := by
          funext i; fin_cases i <;> rfl
        simp only [BinQF.eval, hx]; exact h⟩
      invFun := fun p => ⟨![p.1.1, p.1.2], by
        have h := p.2
        simp only [Set.mem_ofPred_eq]; exact h⟩
      left_inv := fun x => by
        ext1; funext i; fin_cases i <;> rfl
      right_inv := fun p => by ext <;> rfl }

/-- $c(x^2 + xy + y^2)$. -/
def formE (c : ℤ) : BinQF := BinQF.mk c c c

/-- $c(x^2 + 3y^2)$. -/
def formF (c : ℤ) : BinQF := BinQF.mk c 0 (3 * c)

@[simp] lemma formE_eval (c x y : ℤ) : (formE c).eval x y = c * (x ^ 2 + x * y + y ^ 2) := by
  rw [formE, BinQF.eval_eq]; simp; ring

@[simp] lemma formF_eval (c x y : ℤ) : (formF c).eval x y = c * (x ^ 2 + 3 * y ^ 2) := by
  rw [formF, BinQF.eval_eq]; simp; ring

/-- Values $u^2 + uv + v^2 = m$ force $|u|, |v| \le 2|m|$ (as $4E(u,v) = (2u+v)^2 + 3v^2$). -/
lemma bound_E {u v m : ℤ} (h : u ^ 2 + u * v + v ^ 2 = m) : |u| ≤ 2 * |m| ∧ |v| ≤ 2 * |m| := by
  have hu : u ^ 2 ≤ 2 * m := by nlinarith [sq_nonneg (2 * v + u)]
  have hv : v ^ 2 ≤ 2 * m := by nlinarith [sq_nonneg (2 * u + v)]
  have hm : m ≤ |m| := le_abs_self m
  have h1 : |u| ≤ u ^ 2 := by
    rcases eq_or_ne u 0 with rfl | h0
    · simp
    · have : 1 ≤ |u| := Int.one_le_abs h0
      nlinarith [sq_abs u]
  have h2 : |v| ≤ v ^ 2 := by
    rcases eq_or_ne v 0 with rfl | h0
    · simp
    · have : 1 ≤ |v| := Int.one_le_abs h0
      nlinarith [sq_abs v]
  constructor <;> linarith

/-- The finite set of representations $R_E(m) \subset \mathbb{Z}^2$ of $m$ by
$E = x^2 + xy + y^2$. -/
def repFinset (m : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(2 * |m|)) (2 * |m|)) ×ˢ (Finset.Icc (-(2 * |m|)) (2 * |m|))).filter
    (fun p => p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = m)

lemma mem_repFinset {m : ℤ} {p : ℤ × ℤ} :
    p ∈ repFinset m ↔ p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = m := by
  constructor
  · intro h; exact (Finset.mem_filter.1 h).2
  · intro h
    obtain ⟨h1, h2⟩ := bound_E h
    rw [abs_le] at h1 h2
    simp only [repFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨h1, h2⟩, h⟩

/-- `Nat.card` of a sub-predicate of $R_E(m)$ is the card of the corresponding filter. -/
lemma card_sub (m : ℤ) (q : ℤ × ℤ → Prop) [DecidablePred q] :
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = m ∧ q p} =
      ((repFinset m).filter q).card := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun p => ?_)
  simp [Finset.mem_filter, mem_repFinset]

/-- The pointwise counting identity behind the proof: for $(u, v) \in \mathbb{Z}^2$,
$[2 \mid v] + [2 \mid u] + [2 \mid u+v] = 1 + 2\,[2 \mid u \wedge 2 \mid v]$. -/
lemma parity_count (u v : ℤ) :
    (if 2 ∣ v then 1 else 0) + (if 2 ∣ u then 1 else 0) + (if 2 ∣ u + v then 1 else 0) =
      1 + 2 * (if 2 ∣ u ∧ 2 ∣ v then 1 else 0 : ℕ) := by
  rcases Int.emod_two_eq_zero_or_one u with hu | hu <;>
    rcases Int.emod_two_eq_zero_or_one v with hv | hv <;>
    simp [Int.dvd_iff_emod_eq_zero, Int.add_emod, hu, hv]

/-- The core identity for $c = 1$:
$r_E(m) + 2\, r_{4E}(m) = 3\, r_{x^2+3y^2}(m)$, with $E = x^2 + xy + y^2$. -/
theorem core_identity (m : ℤ) :
    repNum (formE 1) m + 2 * repNum (formE 4) m = 3 * repNum (formF 1) m := by
  classical
  rw [repNum_eq_card_prod, repNum_eq_card_prod, repNum_eq_card_prod]
  simp only [formE_eval, formF_eval, one_mul]
  set F := repFinset m
  -- r_E(m) = #F
  have hE : Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = m} = F.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun p => by simp [F, mem_repFinset])
  -- r_{4E}(m) = #{both even}
  have h4 : Nat.card {p : ℤ × ℤ // 4 * (p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2) = m} =
      (F.filter fun p => 2 ∣ p.1 ∧ 2 ∣ p.2).card := by
    rw [← card_sub]
    refine Nat.card_congr
      { toFun := fun p => ⟨(2 * p.1.1, 2 * p.1.2), by have h := p.2; dsimp only; linear_combination h, dvd_mul_right _ _,
          dvd_mul_right _ _⟩
        invFun := fun p => ⟨(p.1.1 / 2, p.1.2 / 2), by
          obtain ⟨h, ⟨a, ha⟩, ⟨b, hb⟩⟩ := p.2
          simp only [ha, hb] at h ⊢
          rw [← h]; simp; ring⟩
        left_inv := fun p => by ext <;> simp
        right_inv := fun p => by
          obtain ⟨h, ⟨a, ha⟩, ⟨b, hb⟩⟩ := p.2
          ext <;> simp [ha, hb] }
  -- r_{x²+3y²}(m) = #{v even}
  have h3 : Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 3 * p.2 ^ 2 = m} =
      (F.filter fun p => 2 ∣ p.2).card := by
    rw [← card_sub]
    refine Nat.card_congr
      { toFun := fun p => ⟨(p.1.1 - p.1.2, 2 * p.1.2), by have h := p.2; dsimp only; linear_combination h, dvd_mul_right _ _⟩
        invFun := fun p => ⟨(p.1.1 + p.1.2 / 2, p.1.2 / 2), by
          obtain ⟨h, ⟨b, hb⟩⟩ := p.2
          simp only [hb] at h ⊢
          rw [Int.mul_ediv_cancel_left _ two_ne_zero]; linear_combination h⟩
        left_inv := fun p => by ext <;> simp
        right_inv := fun p => by
          obtain ⟨h, ⟨b, hb⟩⟩ := p.2
          ext <;> simp [hb] }
  -- symmetry: #{v even} = #{u even} = #{u + v even}
  have hs1 : (F.filter fun p => 2 ∣ p.2).card = (F.filter fun p => 2 ∣ p.1).card := by
    rw [← card_sub, ← card_sub]
    exact Nat.card_congr
      { toFun := fun p => ⟨(p.1.2, p.1.1), by have h := p.2.1; dsimp only; linear_combination h, p.2.2⟩
        invFun := fun p => ⟨(p.1.2, p.1.1), by have h := p.2.1; dsimp only; linear_combination h, p.2.2⟩
        left_inv := fun p => rfl
        right_inv := fun p => rfl }
  have hs2 : (F.filter fun p => 2 ∣ p.1).card = (F.filter fun p => 2 ∣ p.1 + p.2).card := by
    rw [← card_sub, ← card_sub]
    exact Nat.card_congr
      { toFun := fun p => ⟨(-p.1.1 - p.1.2, p.1.2), by have h := p.2.1; dsimp only; linear_combination h, by
          obtain ⟨k, hk⟩ := p.2.2; exact ⟨-k, by simp only; rw [hk]; ring⟩⟩
        invFun := fun p => ⟨(-p.1.1 - p.1.2, p.1.2), by have h := p.2.1; dsimp only; linear_combination h, by
          obtain ⟨k, hk⟩ := p.2.2; exact ⟨-k, by simp only; linarith⟩⟩
        left_inv := fun p => by ext <;> simp
        right_inv := fun p => by ext <;> simp }
  -- counting
  have hcount : (F.filter fun p => 2 ∣ p.2).card + (F.filter fun p => 2 ∣ p.1).card +
      (F.filter fun p => 2 ∣ p.1 + p.2).card =
      F.card + 2 * (F.filter fun p => 2 ∣ p.1 ∧ 2 ∣ p.2).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter,
      Finset.card_eq_sum_ones F, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simpa using parity_count p.1 p.2
  rw [hE, h4, h3]
  omega

/-- Scaling: for $c > 0$, $r_{cQ}(cm) = r_Q(m)$ and $r_{cQ}(m) = 0$ when $c \nmid m$; we only
need the forms $E$ and $x^2 + 3y^2$ here. -/
lemma repNum_scale (Q : ℤ → BinQF) (f : ℤ → ℤ → ℤ)
    (hQ : ∀ c x y, (Q c).eval x y = c * f x y) {c : ℤ} (hc : 0 < c) (m : ℤ) :
    repNum (Q c) m = if c ∣ m then repNum (Q 1) (m / c) else 0 := by
  rw [repNum_eq_card_prod, repNum_eq_card_prod]
  simp only [hQ, one_mul]
  split_ifs with hdvd
  · obtain ⟨k, rfl⟩ := hdvd
    rw [Int.mul_ediv_cancel_left _ hc.ne']
    exact Nat.card_congr (Equiv.subtypeEquivRight fun p => by
      constructor
      · intro h; exact mul_left_cancel₀ hc.ne' h
      · intro h; rw [h])
  · rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨p, hp⟩
    exact hdvd ⟨_, hp.symm⟩

/-- **Lemma 6.2, coefficient form.** For every integer $c > 0$ and every $m$,
$$r_{c(x^2+xy+y^2)}(m) + 2\, r_{4c(x^2+xy+y^2)}(m) = 3\, r_{c(x^2+3y^2)}(m).$$ -/
theorem relation_scaled {c : ℤ} (hc : 0 < c) (m : ℤ) :
    repNum (formE c) m + 2 * repNum (formE (4 * c)) m = 3 * repNum (formF c) m := by
  have hE := repNum_scale formE (fun x y => x ^ 2 + x * y + y ^ 2) (by simp) hc
  have hF := repNum_scale formF (fun x y => x ^ 2 + 3 * y ^ 2) (by simp) hc
  have hE4 : repNum (formE (4 * c)) m = if c ∣ m then repNum (formE 4) (m / c) else 0 := by
    rw [repNum_eq_card_prod, repNum_eq_card_prod]
    simp only [formE_eval]
    split_ifs with hdvd
    · obtain ⟨k, rfl⟩ := hdvd
      rw [Int.mul_ediv_cancel_left _ hc.ne']
      exact Nat.card_congr (Equiv.subtypeEquivRight fun p => by
        constructor
        · intro h; apply mul_left_cancel₀ hc.ne'; linarith
        · intro h; rw [← h]; ring)
    · rw [Nat.card_eq_zero]
      left
      constructor
      rintro ⟨p, hp⟩
      exact hdvd ⟨4 * (p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2), by rw [← hp]; ring⟩
  rw [hE m, hF m, hE4]
  split_ifs
  · exact core_identity _
  · simp

/-- **Lemma 6.2 (non-trivial 3-term linear relation), coefficient form.** Let $Q_1, Q_2, Q_3$ be
integral binary forms with $Q_1 \sim_{\mathbb{Z}} c(x^2+xy+y^2)$, $Q_2 \sim_{\mathbb{Z}}
4c(x^2+xy+y^2)$ and $Q_3 \sim_{\mathbb{Z}} c(x^2+3y^2)$ (equivalence under
$\mathrm{GL}_2(\mathbb{Z})$, `IntEquiv`) for some integer $c > 0$. Then for every $m$,
$$\tfrac13 r_{Q_1}(m) + \tfrac23 r_{Q_2}(m) = r_{Q_3}(m).$$ -/
@[kb "hanke2023threeterm" "§6.3, Lemma 6.2, p. 17"]
theorem nontrivial_relation_coeff {Q₁ Q₂ Q₃ : BinQF} {c : ℤ} (hc : 0 < c)
    (h₁ : IntEquiv Q₁ (formE c)) (h₂ : IntEquiv Q₂ (formE (4 * c)))
    (h₃ : IntEquiv Q₃ (formF c)) (m : ℤ) :
    (1 / 3 : ℚ) * repNum Q₁ m + (2 / 3 : ℚ) * repNum Q₂ m = repNum Q₃ m := by
  rw [repNum_eq_of_intEquiv h₁, repNum_eq_of_intEquiv h₂, repNum_eq_of_intEquiv h₃]
  have := relation_scaled hc m
  have h' : ((repNum (formE c) m : ℚ) + 2 * repNum (formE (4 * c)) m) =
      3 * repNum (formF c) m := by exact_mod_cast this
  linarith

/-- A coefficientwise linear relation $\sum_i \alpha_i r_{Q_i}(m) = 0$ ($m \ge 0$) among positive
definite forms gives the same relation $\sum_i \alpha_i \theta_{Q_i}(z) = 0$ among their theta
functions on the upper half plane (by the $q$-expansion `hasSum_theta`). Three-term version. -/
theorem theta_relation_of_coeff {n : ℕ} {Q₁ Q₂ Q₃ : IntQF n} (h₁ : Q₁.PosDef) (h₂ : Q₂.PosDef)
    (h₃ : Q₃.PosDef) (α₁ α₂ α₃ : ℂ)
    (h : ∀ m : ℕ, α₁ * repNum Q₁ m + α₂ * repNum Q₂ m + α₃ * repNum Q₃ m = 0)
    {z : ℂ} (hz : 0 < z.im) :
    α₁ * theta Q₁ z + α₂ * theta Q₂ z + α₃ * theta Q₃ z = 0 := by
  have s := (((hasSum_theta h₁ hz).mul_left α₁).add ((hasSum_theta h₂ hz).mul_left α₂)).add
    ((hasSum_theta h₃ hz).mul_left α₃)
  have s0 : HasSum (fun m : ℕ => ((α₁ * repNum Q₁ m + α₂ * repNum Q₂ m + α₃ * repNum Q₃ m) *
      Complex.exp (2 * Real.pi * Complex.I * z * m))) 0 := by
    simp only [h, zero_mul]; exact hasSum_zero
  refine s.unique ?_
  convert s0 using 2 with m
  ring

/-- **Lemma 6.2 (non-trivial 3-term linear relation), theta-function form.** Let $Q_1, Q_2, Q_3$
be positive definite integral binary forms with $Q_1 \sim_{\mathbb{Z}} c(x^2+xy+y^2)$,
$Q_2 \sim_{\mathbb{Z}} 4c(x^2+xy+y^2)$ and $Q_3 \sim_{\mathbb{Z}} c(x^2+3y^2)$ for some integer
$c > 0$. Then $\tfrac13 \theta_{Q_1}(z) + \tfrac23 \theta_{Q_2}(z) = \theta_{Q_3}(z)$ for every $z$
in the upper half plane. -/
@[kb "hanke2023threeterm" "§6.3, Lemma 6.2, p. 17"]
theorem nontrivial_relation {Q₁ Q₂ Q₃ : BinQF} (hp₁ : IntQF.PosDef Q₁) (hp₂ : IntQF.PosDef Q₂)
    (hp₃ : IntQF.PosDef Q₃) {c : ℤ} (hc : 0 < c)
    (h₁ : IntEquiv Q₁ (formE c)) (h₂ : IntEquiv Q₂ (formE (4 * c)))
    (h₃ : IntEquiv Q₃ (formF c)) {z : ℂ} (hz : 0 < z.im) :
    (1 / 3 : ℂ) * theta Q₁ z + (2 / 3 : ℂ) * theta Q₂ z = theta Q₃ z := by
  have := theta_relation_of_coeff hp₁ hp₂ hp₃ (1 / 3) (2 / 3) (-1) (fun m => by
    have e := nontrivial_relation_coeff hc h₁ h₂ h₃ m
    have e' : ((1 / 3 : ℚ) * repNum Q₁ m + (2 / 3 : ℚ) * repNum Q₂ m : ℚ) = (repNum Q₃ m : ℚ) := e
    have e'' : ((1 / 3 : ℂ) * repNum Q₁ m + (2 / 3 : ℂ) * repNum Q₂ m : ℂ) = (repNum Q₃ m : ℂ) := by
      have := congrArg (fun q : ℚ => (q : ℂ)) e'
      push_cast at this
      exact this
    linear_combination e'') hz
  linear_combination this

end QuadFormsKB.Hanke2023ThreeTerm
