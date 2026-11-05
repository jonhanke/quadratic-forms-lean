/-
# Cassels, Chapter 3, Example 16 (p. 51): Minkowski's bound for finite groups of rational matrices

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 3, *Examples*, Ex. 16, p. 51.

**Statement.** Let $G$ be a finite group of $n \times n$ matrices with entries in $\mathbb Q$ (a finite subgroup of
$GL_n(\mathbb Q)$, `Subgroup (GL (Fin n) ℚ)`) and let $g = |G|$. Put
$$g^{*}(n) = \prod_{q\ \text{prime}} q^{\beta(q)},\qquad
\beta(2) = n + 2\lfloor n/2\rfloor + \lfloor n/2^{2}\rfloor + \lfloor n/2^{3}\rfloor + \cdots,\qquad
\beta(q) = \Big\lfloor \tfrac{n}{q-1}\Big\rfloor + \Big\lfloor \tfrac{n}{q(q-1)}\Big\rfloor +
\Big\lfloor \tfrac{n}{q^{2}(q-1)}\Big\rfloor + \cdots\quad(q\ \text{odd}).$$
(i) $g \mid g^{*}(n)$ (`ex16_i`). (ii) If every element of $G$ has determinant $+1$ then $g \mid \tfrac12 g^{*}(n)$,
stated as $2g \mid g^{*}(n)$ (`ex16_ii`). This is Minkowski's bound.

**Formalization.** `beta n q` is $\beta(q)$ (all sums are finite since the terms vanish once $q^k$ exceeds $n$), `gStar n`
is $g^{*}(n)$, with the product over the primes $q \le n + 1$ (for $q \ge n + 2$, $\beta(q) = 0$: `beta_of_lt`).
The proof follows the book's hint: the entries of the finitely many elements of $G$ have bounded denominators, so for all
large primes $p$ the group embeds into $GL_n(\mathbb Z_p)$ (`exists_embedding`); the reduction modulo $p$ is injective
on a finite subgroup (the argument of `ex14_ii`, redone in `card_dvd_reduction` to also get the determinant refinement),
so $|G|$ divides $|GL_n(\mathbb F_p)| = \prod_{i<n}(p^{n} - p^{i})$ (Ch. 2, Ex. 12), and $|G|$ divides
$|SL_n(\mathbb F_p)| = |GL_n(\mathbb F_p)|/(p-1)$ in case (ii). For a prime $q$, Dirichlet's theorem
(`Nat.forall_exists_prime_gt_and_eq_mod`) gives a large prime $p$ with $v_q(|GL_n(\mathbb F_p)|) = \beta(q)$
(`exists_prime_val`): for odd $q$, $p$ a primitive root modulo $q^{2}$ (`val_sum_odd`, using lifting the exponent), for
$q = 2$, $p \equiv 3 \pmod 8$ (`val_sum_two`; then also $v_2(p-1) = 1$, giving the factor $\tfrac12$ in (ii)).

**Erratum/Update (Ex. 16 (ii)).** For $n = 0$ the statement (ii) is false: $G$ is trivial, $g^{*}(0) = 1$, and
$\tfrac12 g^{*}(0)$ is not an integer. We therefore assume $n \ge 1$ in `ex16_ii`.

**Unconditional**: no named inputs; uses only Mathlib's Dirichlet theorem on primes in arithmetic progressions.
-/
import QuadFormsKB.Literature.Cassels.Ch3.Exercises
import QuadFormsKB.Literature.Cassels.Ch2.Exercises

open Finset Matrix

noncomputable section

namespace QuadFormsKB.Cassels.Ch3Ex

theorem padicNorm_le_one_of_not_dvd_den (p : ℕ) [Fact p.Prime] (x : ℚ) (h : ¬ p ∣ x.den) :
    padicNorm p x ≤ 1 := by
  rw [← Rat.num_div_den x, padicNorm.div, (padicNorm.nat_eq_one_iff _).2 h]
  simpa using padicNorm.of_int (p := p) x.num

theorem exists_bound {n : ℕ} (G : Subgroup (GL (Fin n) ℚ)) [Finite G] :
    ∃ M : ℕ, ∀ (p : ℕ) [Fact p.Prime], M < p → ∀ g ∈ G, ∀ i j,
      ‖((((g : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) i j : ℚ) : ℚ_[p])‖ ≤ 1 := by
  have := Fintype.ofFinite G
  refine ⟨(Finset.univ : Finset (G × Fin n × Fin n)).sup
    (fun t => ((((t.1 : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) t.2.1 t.2.2).den)), ?_⟩
  intro p _ hMp g hg i j
  rw [Padic.eq_padicNorm]
  have key : ¬ p ∣ (((g : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) i j).den := by
    intro hdvd
    have h1 := Nat.le_of_dvd (Rat.den_pos _) hdvd
    have h2 : (((g : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) i j).den ≤
        (Finset.univ : Finset (G × Fin n × Fin n)).sup
          (fun t => ((((t.1 : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) t.2.1 t.2.2).den)) :=
      Finset.le_sup (f := fun t : G × Fin n × Fin n =>
      ((((t.1 : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) t.2.1 t.2.2).den)) (Finset.mem_univ (⟨g, hg⟩, i, j))
    omega
  exact_mod_cast padicNorm_le_one_of_not_dvd_den p _ key

theorem exists_embedding {n p : ℕ} [Fact p.Prime] (G : Subgroup (GL (Fin n) ℚ))
    (h : ∀ g ∈ G, ∀ i j, ‖((((g : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) i j : ℚ) : ℚ_[p])‖ ≤ 1) :
    ∃ ψ : G →* GL (Fin n) ℤ_[p], Function.Injective ψ ∧ ∀ g : G,
      ((ψ g : Matrix (Fin n) (Fin n) ℤ_[p])).map (PadicInt.Coe.ringHom (p := p)) =
        (((g : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ)).map (Rat.castHom ℚ_[p]) := by
  let θ : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom (p := p)
  let κ : ℚ →+* ℚ_[p] := Rat.castHom ℚ_[p]
  have hθ : Function.Injective θ := Subtype.val_injective
  have hκ : Function.Injective κ := (Rat.castHom ℚ_[p]).injective
  let A : G → Matrix (Fin n) (Fin n) ℤ_[p] := fun g =>
    Matrix.of fun i j => ⟨κ (((g : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) i j), h g g.2 i j⟩
  have hA : ∀ g, (A g).map θ = (((g : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ)).map κ := by
    intro g; ext i j; rfl
  have hinjM : Function.Injective (fun M : Matrix (Fin n) (Fin n) ℤ_[p] => M.map θ) :=
    Matrix.map_injective hθ
  let Φ : G →* Matrix (Fin n) (Fin n) ℤ_[p] :=
    { toFun := A
      map_one' := by
        apply hinjM
        simp only [hA]
        simp
      map_mul' := by
        intro g g'
        apply hinjM
        show (A (g * g')).map θ = (A g * A g').map θ
        rw [Matrix.map_mul, hA, hA, hA]
        simp [Matrix.map_mul] }
  refine ⟨Φ.toHomUnits, ?_, ?_⟩
  · intro g g' hgg
    have h1 : Φ g = Φ g' := congrArg Units.val hgg
    have h2 : (Φ g).map θ = (Φ g').map θ := by rw [h1]
    change (A g).map θ = (A g').map θ at h2
    rw [hA, hA] at h2
    have h3 : (((g : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ)) =
        (((g' : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ)) :=
      Matrix.map_injective hκ h2
    exact Subtype.ext (Units.ext h3)
  · intro g
    exact hA g


theorem card_dvd_reduction {n p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {Γ : Type*} [Group Γ] [Finite Γ]
    (ψ : Γ →* GL (Fin n) ℤ_[p]) (hψ : Function.Injective ψ) :
    Nat.card Γ ∣ ∏ i ∈ Finset.range n, (p ^ n - p ^ i) ∧
      ((∀ γ, ((ψ γ : Matrix (Fin n) (Fin n) ℤ_[p])).det = 1) → 1 ≤ n →
        Nat.card Γ * (p - 1) ∣ ∏ i ∈ Finset.range n, (p ^ n - p ^ i)) := by
  let f : Γ →* GL (Fin n) (ZMod p) :=
    (Matrix.GeneralLinearGroup.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)).comp ψ
  have hf : ∀ γ, ((f γ : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) =
      ((ψ γ : Matrix (Fin n) (Fin n) ℤ_[p])).map PadicInt.toZMod := by
    intro γ; simp [f, Matrix.GeneralLinearGroup.map]
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg1 : ((ψ g : Matrix (Fin n) (Fin n) ℤ_[p])).map PadicInt.toZMod = 1 := by
      rw [← hf, hg]; rfl
    have hcong : CongOne ((ψ g : Matrix (Fin n) (Fin n) ℤ_[p])) := by
      intro i j
      apply dvd_of_toZMod_eq_zero
      have := congrFun (congrFun hg1 i) j
      simp only [Matrix.map_apply] at this
      simp only [Matrix.sub_apply, map_sub, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    obtain ⟨k, hk, hk1⟩ := (isOfFinOrder_of_finite g).exists_pow_eq_one
    have hmat : ((ψ g : Matrix (Fin n) (Fin n) ℤ_[p])) = 1 := by
      by_contra hne
      refine ex14_i hp2 hcong hne k hk ?_
      have := congrArg (fun u : Γ => ((ψ u : GL (Fin n) ℤ_[p]) : Matrix (Fin n) (Fin n) ℤ_[p])) hk1
      simpa using this
    exact hψ (by rw [map_one]; exact Units.ext hmat)
  have hcard : Nat.card (GL (Fin n) (ZMod p)) = ∏ i ∈ Finset.range n, (p ^ n - p ^ i) :=
    Ch2Ex.ex12 p n
  refine ⟨hcard ▸ Subgroup.card_dvd_of_injective f hinj, fun hdet hn => ?_⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let D : GL (Fin n) (ZMod p) →* (ZMod p)ˣ := Matrix.GeneralLinearGroup.det
  have hmem : ∀ γ, f γ ∈ D.ker := by
    intro γ
    rw [MonoidHom.mem_ker]
    apply Units.ext
    show ((f γ : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)).det = 1
    rw [hf, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet γ, map_one]
  let f' : Γ →* D.ker := f.codRestrict D.ker hmem
  have hinj' : Function.Injective f' := fun a b h => hinj (congrArg Subtype.val h)
  have h1 : Nat.card Γ ∣ Nat.card D.ker := Subgroup.card_dvd_of_injective f' hinj'
  have h2 : Nat.card D.ker * Nat.card (ZMod p)ˣ = Nat.card (GL (Fin n) (ZMod p)) := by
    have := Subgroup.card_mul_index D.ker
    rwa [Subgroup.index_ker, MonoidHom.range_eq_top.mpr Matrix.GeneralLinearGroup.det_surjective,
      Subgroup.card_top] at this
  have h3 : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units p]
  rw [← hcard, ← h2, h3]
  exact Nat.mul_dvd_mul_right h1 _



/-- Sum over multiples. -/
theorem sum_Icc_multiples (d : ℕ) (hd : 0 < d) (h : ℕ → ℕ) (hz : ∀ j, ¬ d ∣ j → h j = 0) (n : ℕ) :
    ∑ j ∈ Icc 1 n, h j = ∑ m ∈ Icc 1 (n / d), h (d * m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    by_cases hdn : d ∣ n + 1
    · obtain ⟨c, hc⟩ := hdn
      cases c with
      | zero => simp at hc
      | succ c =>
        have h1 : (n + 1) / d = c + 1 := by rw [hc]; exact Nat.mul_div_cancel_left _ hd
        have h2 : n / d = c := by
          have hn : n = d * c + (d - 1) := by
            have : d * (c + 1) = d * c + d := Nat.mul_succ d c
            omega
          rw [hn, Nat.mul_add_div hd, Nat.div_eq_of_lt (by omega)]; simp
        rw [h1, h2, Finset.sum_Icc_succ_top (show 1 ≤ c + 1 by omega), ← hc]
    · rw [Nat.succ_div_of_not_dvd hdn, hz _ hdn]; simp

theorem padicValNat_factorial_eq_sum (q : ℕ) [Fact q.Prime] (N : ℕ) :
    padicValNat q N.factorial = ∑ m ∈ Icc 1 N, padicValNat q m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero N),
      Finset.sum_Icc_succ_top (by omega), ih, add_comm]

/-- **Cassels, Ch. 3, Ex. 16, p. 51: the exponent $\beta(q)$.** For $q = 2$,
$\beta(2) = n + 2\lfloor n/2\rfloor + \lfloor n/2^{2}\rfloor + \lfloor n/2^{3}\rfloor + \cdots$;
for a prime $q \ne 2$, $\beta(q) = \lfloor n/(q-1)\rfloor + \lfloor n/q(q-1)\rfloor + \lfloor n/q^{2}(q-1)\rfloor + \cdots$.
Here `n` is the matrix size and the sums are finite (terms vanish once $2^{k} > n$, resp. $q^{k}(q-1) > n$). -/
@[kb "cassels1978" "Ch. 3, Ex. 16, p. 51"]
def beta (n q : ℕ) : ℕ :=
  if q = 2 then n + 2 * (n / 2) + ∑ k ∈ Finset.Ico 2 (n + 2), n / 2 ^ k
  else ∑ k ∈ Finset.range (n + 1), n / (q ^ k * (q - 1))

theorem beta_two (n : ℕ) : beta n 2 = n + 2 * (n / 2) + padicValNat 2 (n / 2).factorial := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold beta
  rw [if_pos rfl, padicValNat_factorial (b := n + 1)]
  · congr 1
    rw [← Finset.sum_Ico_add' (fun k => n / 2 ^ k) 1 (n + 1) 1]
    -- LHS: Ico (1+1) (n+1+1)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
  · exact lt_of_le_of_lt (Nat.log_le_self 2 _) (by omega)

theorem beta_odd (n q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    beta n q = n / (q - 1) + padicValNat q (n / (q - 1)).factorial := by
  have : Fact q.Prime := ⟨hq⟩
  unfold beta
  rw [if_neg hq2, padicValNat_factorial (b := n + 1), Finset.sum_range_eq_add_Ico _ (by omega)]
  · simp only [pow_zero, one_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.div_div_eq_div_mul, mul_comm]
  · exact lt_of_le_of_lt (Nat.log_le_self q _) (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))

theorem beta_of_lt (n q : ℕ) (hq : q.Prime) (h : n + 2 ≤ q) : beta n q = 0 := by
  unfold beta
  by_cases h2 : q = 2
  · subst h2
    have : n = 0 := by omega
    subst this; simp
  · rw [if_neg h2]
    refine Finset.sum_eq_zero fun k _ => ?_
    apply Nat.div_eq_of_lt
    have : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq.pos
    nlinarith [Nat.sub_add_cancel hq.one_le]


theorem padicValNat_prod_range (q : ℕ) [Fact q.Prime] (f : ℕ → ℕ) (n : ℕ) (hf : ∀ i < n, f i ≠ 0) :
    padicValNat q (∏ i ∈ range n, f i) = ∑ i ∈ range n, padicValNat q (f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ,
      padicValNat.mul (Finset.prod_ne_zero_iff.2 fun i hi => hf i (by simp at hi; omega))
        (hf n (by omega)), ih fun i hi => hf i (by omega)]

theorem val_GL_reduce (q p n : ℕ) [Fact q.Prime] (hp : p.Prime) (hpq : p ≠ q) :
    padicValNat q (∏ i ∈ range n, (p ^ n - p ^ i)) = ∑ j ∈ Icc 1 n, padicValNat q (p ^ j - 1) := by
  have hqp : ¬ q ∣ p := fun h =>
    hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp).1 h).symm
  have hfac : ∀ i ∈ range n, p ^ n - p ^ i = p ^ i * (p ^ (n - i) - 1) := by
    intro i hi
    have hi : i < n := by simpa using hi
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hi.le]
  have hne : ∀ i ∈ range n, p ^ n - p ^ i ≠ 0 := by
    intro i hi
    have hi : i < n := by simpa using hi
    have := Nat.pow_lt_pow_right hp.one_lt hi
    omega
  rw [padicValNat_prod_range q _ n (fun i hi => hne i (by simpa using hi))]
  have h1 : ∀ i ∈ range n, padicValNat q (p ^ n - p ^ i) = padicValNat q (p ^ (n - i) - 1) := by
    intro i hi
    have hi' : i < n := by simpa using hi
    have h2 : p ^ (n - i) - 1 ≠ 0 := by
      have := Nat.pow_lt_pow_right hp.one_lt (show 0 < n - i by omega)
      simp at this; omega
    rw [hfac i hi, padicValNat.mul (pow_ne_zero _ hp.ne_zero) h2,
      padicValNat.eq_zero_of_not_dvd (fun h => hqp (Fact.out (p := q.Prime) |>.dvd_of_dvd_pow h)), zero_add]
  rw [Finset.sum_congr rfl h1]
  refine Finset.sum_nbij' (fun i => n - i) (fun j => n - j) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp at hi ⊢; omega
  · intro i hi; simp at hi ⊢; omega
  · intro i hi; simp at hi ⊢; omega
  · intro i hi; simp at hi ⊢; omega
  · intro i hi; rfl

theorem dvd_pow_sub_one_iff (c a j : ℕ) (hpos : 1 ≤ a ^ j) :
    c ∣ a ^ j - 1 ↔ (a : ZMod c) ^ j = 1 := by
  rw [← Nat.modEq_iff_dvd' hpos, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact eq_comm


section Odd

variable {q p : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hp : p.Prime) (hpq : p ≠ q)
  (u : (ZMod (q ^ 2))ˣ) (hu : orderOf u = q * (q - 1)) (hpu : (p : ZMod (q ^ 2)) = u)

include hq hq2 hp hpq

theorem not_dvd_of_dvd_sub_one {x : ℕ} (hx : 1 ≤ x) (h : q ∣ x - 1) : ¬ q ∣ x := by
  intro h2
  have : q ∣ 1 := by
    have := (Nat.dvd_sub h2 h)
    rwa [show x - (x - 1) = 1 by omega] at this
  exact hq.one_lt.ne' (Nat.dvd_one.1 this)

include hu hpu

theorem order_dvd_of_pow (j : ℕ) (hj : (p : ZMod (q ^ 2)) ^ j = 1) : q * (q - 1) ∣ j := by
  rw [← hu, orderOf_dvd_iff_pow_eq_one]
  apply Units.ext
  simpa [hpu] using hj

theorem dvd_sub_one_imp (j : ℕ) (hj : 1 ≤ j) (hqj : q ∣ p ^ j - 1) : (q - 1) ∣ j := by
  have : Fact q.Prime := ⟨hq⟩
  have hpj : 1 < p ^ j := Nat.one_lt_pow (by omega) hp.one_lt
  have hnd := not_dvd_of_dvd_sub_one hq hq2 hp hpq (by omega) hqj
  have hlte := padicValNat.pow_sub_pow (p := q) (hq.odd_of_ne_two hq2) (x := p ^ j) (y := 1) hpj hqj hnd
    (n := q) hq.ne_zero
  rw [one_pow] at hlte
  have h1 : 1 ≤ padicValNat q (p ^ j - 1) := one_le_padicValNat_of_dvd (by omega) hqj
  have h2 : padicValNat q q = 1 := padicValNat_self
  have hne : (p ^ j) ^ q - 1 ≠ 0 := by
    have : 1 < (p ^ j) ^ q := Nat.one_lt_pow hq.ne_zero hpj
    omega
  have hdiv : q ^ 2 ∣ (p ^ j) ^ q - 1 := (padicValNat_dvd_iff_le hne).2 (by omega)
  have hpow : (p : ZMod (q ^ 2)) ^ (j * q) = 1 := by
    rw [← dvd_pow_sub_one_iff _ _ _ (Nat.one_le_pow _ _ hp.pos), pow_mul]
    exact hdiv
  have := order_dvd_of_pow hq hq2 hp hpq u hu hpu _ hpow
  rw [mul_comm j q] at this
  exact Nat.dvd_of_mul_dvd_mul_left hq.pos this

theorem val_pow_sub_one_odd (m : ℕ) (hm : 1 ≤ m) :
    padicValNat q (p ^ ((q - 1) * m) - 1) = 1 + padicValNat q m := by
  have : Fact q.Prime := ⟨hq⟩
  have hqp : ¬ q ∣ p := fun h =>
    hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 h).symm
  have hq1 : 0 < q - 1 := by have := hq.two_le; omega
  set x := p ^ (q - 1) with hx
  have hx1 : 1 < x := Nat.one_lt_pow hq1.ne' hp.one_lt
  have hqx : q ∣ x - 1 := by
    have : Fact q.Prime := ⟨hq⟩
    rw [hx, dvd_pow_sub_one_iff _ _ _ (Nat.one_le_pow _ _ hp.pos)]
    exact ZMod.pow_card_sub_one_eq_one (by simpa [ZMod.natCast_eq_zero_iff] using hqp)
  have hnx := not_dvd_of_dvd_sub_one hq hq2 hp hpq (by omega) hqx
  have hq2x : ¬ q ^ 2 ∣ x - 1 := by
    intro h
    rw [hx, dvd_pow_sub_one_iff _ _ _ (Nat.one_le_pow _ _ hp.pos)] at h
    have := order_dvd_of_pow hq hq2 hp hpq u hu hpu _ h
    have := Nat.le_of_dvd hq1 this
    have h2 := hq.two_le
    nlinarith
  have hv : padicValNat q (x - 1) = 1 := by
    have h1 : 1 ≤ padicValNat q (x - 1) := one_le_padicValNat_of_dvd (by omega) hqx
    have h2 : ¬ 2 ≤ padicValNat q (x - 1) := fun h =>
      hq2x ((padicValNat_dvd_iff_le (by omega)).2 h)
    omega
  have := padicValNat.pow_sub_pow (p := q) (hq.odd_of_ne_two hq2) (x := x) (y := 1) hx1 hqx hnx
    (n := m) (by omega)
  rw [one_pow, hv] at this
  rw [pow_mul]
  exact this

theorem val_pow_sub_one_odd' (j : ℕ) (hj : 1 ≤ j) (hnd : ¬ (q - 1) ∣ j) :
    padicValNat q (p ^ j - 1) = 0 := by
  have : Fact q.Prime := ⟨hq⟩
  exact padicValNat.eq_zero_of_not_dvd fun h => hnd (dvd_sub_one_imp hq hq2 hp hpq u hu hpu j hj h)

theorem val_sum_odd (n : ℕ) :
    ∑ j ∈ Icc 1 n, padicValNat q (p ^ j - 1) = beta n q := by
  have : Fact q.Prime := ⟨hq⟩
  have hq1 : 0 < q - 1 := by have := hq.two_le; omega
  rw [beta_odd n q hq hq2, sum_Icc_multiples (q - 1) hq1 _ (fun j hj => by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · exact absurd (dvd_zero _) hj
    · exact val_pow_sub_one_odd' hq hq2 hp hpq u hu hpu j h hj)]
  rw [Finset.sum_congr rfl (fun m hm => val_pow_sub_one_odd hq hq2 hp hpq u hu hpu m (Finset.mem_Icc.1 hm).1),
    Finset.sum_add_distrib, ← padicValNat_factorial_eq_sum]
  simp

end Odd


section Two

theorem padicValNat_two_eq (a k : ℕ) (ha : a ≠ 0) (h1 : 2 ^ k ∣ a) (h2 : ¬ 2 ^ (k + 1) ∣ a) :
    padicValNat 2 a = k := by
  have a1 := (padicValNat_dvd_iff_le ha).1 h1
  have a2 : ¬ k + 1 ≤ padicValNat 2 a := fun h => h2 ((padicValNat_dvd_iff_le ha).2 h)
  omega

theorem three_pow_odd_mod_four (k : ℕ) : 3 ^ (2 * k + 1) % 4 = 3 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have : 3 ^ (2 * (k + 1) + 1) = 9 * 3 ^ (2 * k + 1) := by ring
    omega

variable {p : ℕ} (hp8 : p % 8 = 3)
include hp8

theorem val_p_sub_one_two : padicValNat 2 (p - 1) = 1 :=
  padicValNat_two_eq _ 1 (by omega) (by omega) (by omega)

theorem val_pow_sub_one_two_odd (j : ℕ) (hj : j % 2 = 1) : padicValNat 2 (p ^ j - 1) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k + 1 := ⟨j / 2, by omega⟩
  have hmod : p ^ (2 * k + 1) % 4 = 3 := by
    rw [Nat.pow_mod, show p % 4 = 3 by omega]
    exact three_pow_odd_mod_four k
  have hpos : 1 ≤ p ^ (2 * k + 1) := Nat.one_le_pow _ _ (by omega)
  exact padicValNat_two_eq _ 1 (by omega) (by omega) (by omega)

theorem val_pow_sub_one_two_even (m : ℕ) (hm : 1 ≤ m) :
    padicValNat 2 (p ^ (2 * m) - 1) = 3 + padicValNat 2 m := by
  have h := padicValNat.pow_two_sub_one (x := p) (n := 2 * m) (by omega) (by omega) (by omega)
    (even_two_mul m)
  have h1 : padicValNat 2 (p + 1) = 2 := padicValNat_two_eq _ 2 (by omega) (by omega) (by omega)
  have h2 := val_p_sub_one_two hp8
  have h3 : padicValNat 2 (2 * m) = 1 + padicValNat 2 m := by
    rw [padicValNat.mul (by norm_num) (by omega)]; simp
  omega

theorem val_sum_two (n : ℕ) :
    ∑ j ∈ Icc 1 n, padicValNat 2 (p ^ j - 1) = beta n 2 := by
  have hge : ∀ j ∈ Icc 1 n, padicValNat 2 (p ^ j - 1) = 1 + (padicValNat 2 (p ^ j - 1) - 1) := by
    intro j hj
    rcases Nat.even_or_odd' j with ⟨m, hm | hm⟩
    · have hm1 : 1 ≤ m := by have := (Finset.mem_Icc.1 hj).1; omega
      rw [hm, val_pow_sub_one_two_even hp8 m hm1]; omega
    · rw [val_pow_sub_one_two_odd hp8 j (by omega)]
  rw [Finset.sum_congr rfl hge, Finset.sum_add_distrib,
    sum_Icc_multiples 2 (by norm_num) (fun j => padicValNat 2 (p ^ j - 1) - 1) (fun j hj => by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · exact absurd (dvd_zero _) hj
      · rw [val_pow_sub_one_two_odd hp8 j (by omega)]) n, beta_two]
  have : ∀ m ∈ Icc 1 (n / 2), padicValNat 2 (p ^ (2 * m) - 1) - 1 = 2 + padicValNat 2 m := by
    intro m hm
    rw [val_pow_sub_one_two_even hp8 m (Finset.mem_Icc.1 hm).1]; omega
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← padicValNat_factorial_eq_sum]
  simp
  ring

end Two


theorem exists_prime_val (n q : ℕ) (hq : q.Prime) (M : ℕ) :
    ∃ p, p.Prime ∧ M < p ∧ q < p ∧
      padicValNat q (∏ i ∈ range n, (p ^ n - p ^ i)) = beta n q ∧
      (q = 2 → padicValNat 2 (p - 1) = 1) := by
  have : Fact q.Prime := ⟨hq⟩
  by_cases hq2 : q = 2
  · subst hq2
    have hu : IsUnit (3 : ZMod 8) := by decide
    obtain ⟨p, hpM, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu (max M 2)
    have h8 : p % 8 = 3 := by
      have := (ZMod.natCast_eq_natCast_iff' p 3 8).1 (by simpa using hpmod)
      simpa using this
    refine ⟨p, hp, by omega, by omega, ?_, fun _ => val_p_sub_one_two h8⟩
    rw [val_GL_reduce 2 p n hp (by omega), val_sum_two h8]
  · have : NeZero (q ^ 2) := ⟨pow_ne_zero 2 hq.ne_zero⟩
    have : IsCyclic (ZMod (q ^ 2))ˣ := ZMod.isCyclic_units_of_prime_pow q hq hq2 2
    obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod (q ^ 2))ˣ)
    have hord : orderOf u = q * (q - 1) := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_eq_fintype_card,
        ZMod.card_units_eq_totient, Nat.totient_prime_pow hq (by norm_num)]
      simp
    obtain ⟨p, hpM, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod u.isUnit (max M q)
    have hpq : p ≠ q := by omega
    refine ⟨p, hp, by omega, by omega, ?_, fun h => absurd h hq2⟩
    rw [val_GL_reduce q p n hp hpq, val_sum_odd hq hq2 hp hpq u hord hpmod]


/-- **Cassels, Ch. 3, Ex. 16, p. 51: Minkowski's number $g^{*}(n) = \prod_{q\ \text{prime}} q^{\beta(q)}$.**
Only the primes $q \le n + 1$ contribute (`beta_of_lt`), so the product is over those. -/
@[kb "cassels1978" "Ch. 3, Ex. 16, p. 51"]
def gStar (n : ℕ) : ℕ :=
  ∏ q ∈ (Finset.range (n + 2)).filter Nat.Prime, q ^ beta n q

theorem padicValNat_gStar (n q : ℕ) (hq : q.Prime) : padicValNat q (gStar n) = beta n q := by
  rw [← Nat.factorization_def _ hq]
  unfold gStar
  rw [Nat.factorization_prod (fun x hx => pow_ne_zero _ (Nat.Prime.ne_zero (Finset.mem_filter.1 hx).2)),
    Finsupp.finset_sum_apply]
  have hterm : ∀ x ∈ (Finset.range (n + 2)).filter Nat.Prime,
      (x ^ beta n x).factorization q = if x = q then beta n q else 0 := by
    intro x hx
    have hxp := (Finset.mem_filter.1 hx).2
    rw [Nat.factorization_pow, hxp.factorization]
    by_cases h : x = q
    · subst h; simp
    · simp [Finsupp.single_apply, h]
  rw [Finset.sum_congr rfl hterm]
  by_cases hqS : q ∈ (Finset.range (n + 2)).filter Nat.Prime
  · simp [hqS]
  · rw [Finset.sum_ite_eq' ]
    simp only [hqS, if_false]
    symm
    apply beta_of_lt n q hq
    by_contra hlt
    exact hqS (by simp [hq]; omega)

theorem main_bound {n : ℕ} (G : Subgroup (GL (Fin n) ℚ)) [Finite G] (q : ℕ) (hq : q.Prime) :
    padicValNat q (Nat.card G) ≤ beta n q ∧
      (q = 2 → (∀ g ∈ G, (((g : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ)).det = 1) → 1 ≤ n →
        padicValNat 2 (Nat.card G) + 1 ≤ beta n 2) := by
  obtain ⟨M, hM⟩ := exists_bound G
  obtain ⟨p, hp, hMp, hqp, hval, hval2⟩ := exists_prime_val n q hq M
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have hp2 : p ≠ 2 := by have := hq.two_le; omega
  obtain ⟨ψ, hψ, hψmap⟩ := exists_embedding (p := p) G (fun g hg i j => hM p hMp g hg i j)
  obtain ⟨hd1, hd2⟩ := card_dvd_reduction hp2 ψ hψ
  have hP : ∏ i ∈ Finset.range n, (p ^ n - p ^ i) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
    have hi : i < n := by simpa using hi
    have := Nat.pow_lt_pow_right hp.one_lt hi
    omega
  have hc : Nat.card G ≠ 0 := Nat.card_pos.ne'
  refine ⟨?_, ?_⟩
  · rw [← hval]
    exact (padicValNat_dvd_iff_le hP).1 (dvd_trans pow_padicValNat_dvd hd1) |> fun h => by
      simpa using h
  · rintro rfl hdet hn
    have hdet' : ∀ γ : G, ((ψ γ : Matrix (Fin n) (Fin n) ℤ_[p])).det = 1 := by
      intro γ
      apply Subtype.val_injective
      have h1 := RingHom.map_det (PadicInt.Coe.ringHom (p := p)) (ψ γ : Matrix (Fin n) (Fin n) ℤ_[p])
      rw [RingHom.mapMatrix_apply, hψmap γ, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
        hdet γ γ.2] at h1
      simpa using h1
    have hd := hd2 hdet' hn
    have hle := (padicValNat_dvd_iff_le (p := 2) hP).1
      (dvd_trans (pow_padicValNat_dvd (p := 2) (n := Nat.card G * (p - 1))) hd)
    have hp1 : 0 < p - 1 := by have := hp.two_le; omega
    rw [padicValNat.mul hc hp1.ne', hval2 rfl, hval] at hle
    exact hle


/-- **Cassels, Ch. 3, Ex. 16 (i), p. 51 (Minkowski).** Let $G$ be a finite group of invertible $n \times n$ matrices
with entries in $\mathbb Q$ (a finite subgroup of $GL_n(\mathbb Q)$). Then the order $g = |G|$ divides
$g^{*}(n) = \prod_q q^{\beta(q)}$ (`gStar n`), with $\beta$ as in `beta`. -/
@[kb "cassels1978" "Ch. 3, Ex. 16 (i), p. 51"]
theorem ex16_i {n : ℕ} (G : Subgroup (GL (Fin n) ℚ)) [Finite G] : Nat.card G ∣ gStar n := by
  have hc : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hg : gStar n ≠ 0 := Finset.prod_ne_zero_iff.2 fun q hq =>
    pow_ne_zero _ (Nat.Prime.ne_zero (Finset.mem_filter.1 hq).2)
  rw [← Nat.factorization_prime_le_iff_dvd hc hg]
  intro q hq
  rw [Nat.factorization_def _ hq, Nat.factorization_def _ hq, padicValNat_gStar n q hq]
  exact (main_bound G q hq).1

/-- **Cassels, Ch. 3, Ex. 16 (ii), p. 51 (Minkowski).** Let $G$ be a finite subgroup of $GL_n(\mathbb Q)$, $n \ge 1$,
all of whose elements have determinant $+1$ (`hdet`). Then $g = |G|$ divides $\tfrac12 g^{*}(n)$, stated as
$2g \mid g^{*}(n)$. *Erratum/update:* the hypothesis $n \ge 1$ (`hn`) is needed, since for $n = 0$ the
number $\tfrac12 g^{*}(0) = \tfrac12$ is not an integer. -/
@[kb "cassels1978" "Ch. 3, Ex. 16 (ii), p. 51"]
theorem ex16_ii {n : ℕ} (hn : 1 ≤ n) (G : Subgroup (GL (Fin n) ℚ)) [Finite G]
    (hdet : ∀ g ∈ G, (((g : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ)).det = 1) :
    2 * Nat.card G ∣ gStar n := by
  have hc : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hg : gStar n ≠ 0 := Finset.prod_ne_zero_iff.2 fun q hq =>
    pow_ne_zero _ (Nat.Prime.ne_zero (Finset.mem_filter.1 hq).2)
  rw [← Nat.factorization_prime_le_iff_dvd (by omega) hg]
  intro q hq
  rw [Nat.factorization_mul (by norm_num) hc, Finsupp.add_apply,
    Nat.factorization_def _ hq, Nat.factorization_def _ hq, Nat.factorization_def _ hq,
    padicValNat_gStar n q hq]
  by_cases h2 : q = 2
  · subst h2
    have := (main_bound G 2 Nat.prime_two).2 rfl hdet hn
    have h22 : padicValNat 2 2 = 1 := padicValNat_self
    omega
  · have : Fact q.Prime := ⟨hq⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h22 : padicValNat q 2 = 0 := padicValNat_primes h2
    have := (main_bound G q hq).1
    omega

end QuadFormsKB.Cassels.Ch3Ex

