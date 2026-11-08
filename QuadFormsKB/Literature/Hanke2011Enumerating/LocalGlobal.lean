/-
# Hanke 2011, Lemma 5.2: which local spaces come from a positive definite rational space

J. Hanke, *Enumerating maximal definite quadratic forms of bounded class number over $\mathbb Z$ in $n\ge3$ variables*,
arXiv:1110.1876v1 (bib key `hanke2011enumerating`), Lemma 5.2 (second part), p. 9.

**Setting** as in `ProductFormula.lean`. A local quadratic space at the prime $p$ is a diagonal form
$\langle\alpha_{p,0},\dots,\alpha_{p,n-1}\rangle$ with $\alpha_{p,i}\in\mathbb Q^\times$, viewed over $\mathbb Q_p$ (no loss of
generality: every non-degenerate space over $\mathbb Q_p$ is one, see `Cassels.Ch6.exists_form_of_local`). A positive
definite rational space is a diagonal form $\langle a_0,\dots,a_{n-1}\rangle$ with $a_i\in\mathbb Q_{>0}$ (every positive definite
rational space is one). $\delta_p$ = `deltaQ (α p)` $= (-1)^{\lfloor n/2\rfloor}\prod_i\alpha_{p,i}$ and $w_p$ = `wP p (α p)` are
Gan–Hanke–Yu's local invariants (Lemma 5.1).

**Proves** the local–global part of Lemma 5.2 (`lemma_5_2_exists`): the collection $\{\langle\alpha_p\rangle\}_p$ comes
from a positive definite rational space iff there is $\Delta\in\mathbb Q_{>0}$ with
$\Delta\equiv(-1)^{\lfloor n/2\rfloor}\delta_p$ modulo $(\mathbb Q_p^\times)^2$ for all $p$, and the product formula (4) holds (in its
corrected form, exponent $\lfloor(n-1)/2\rfloor$, see `lemma_5_2`; "(4) holds" includes that only finitely many $w_p$ are
$-1$).

**Proof.** As in the paper, "a rephrasing of [Cas78, Thm 1.3, p. 77] using the Gan–Hanke–Yu local invariants": the library's
`Cassels.Ch6.exists_form_of_local`, applied with $f_\infty = \langle1,\dots,1\rangle$ (positive definite) and $d_0 = \Delta$.
The rephrasing: $w_p = c_p\,\mu_p(n,\delta)$ where $\mu_p$ depends only on the square class of $\delta$ in $\mathbb Q_p$; comparing
with the model space $\langle\Delta,1,\dots,1\rangle$ (for which (4) holds by `lemma_5_2`) turns (4) into
$\prod_pc_p = 1$, Cassels' condition.
-/
import QuadFormsKB.Literature.Hanke2011Enumerating.ProductFormula
import QuadFormsKB.Literature.Cassels.Ch6.Sec7
import QuadFormsKB.Citation

open QuadFormsKB RatPlace QuadForm Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2011Enumerating

/-! ### Square-class invariance of the Gan–Hanke–Yu invariants -/

/-- $(x,y)_p$ depends only on the square class of $y$ in $\mathbb Q_p^\times$. -/
theorem hp_congr_right (p : Nat.Primes) (x : ℚ) {y y' : ℚ}
    (h : haveI : Fact p.1.Prime := ⟨p.2⟩; SameSquareClass ℚ_[p.1] y y') : hp p x y = hp p x y' := by
  haveI : Fact p.1.Prime := ⟨p.2⟩
  obtain ⟨t, ht, e⟩ := h
  simp only [hp, RatPlace.hilbert]
  simp only [eq_ratCast] at e
  rw [e, PadicClass.hs_sq_right _ _ _ ht]

theorem sameSquareClass_symm {K : Type*} [Field K] [CharZero K] {d₁ d₂ : ℚ} (h : SameSquareClass K d₁ d₂) :
    SameSquareClass K d₂ d₁ := by
  obtain ⟨t, ht, e⟩ := h
  refine ⟨t⁻¹, inv_ne_zero ht, ?_⟩
  rw [e]; field_simp

theorem sameSquareClass_mul_left {K : Type*} [Field K] [CharZero K] (s : ℚ) {d₁ d₂ : ℚ}
    (h : SameSquareClass K d₁ d₂) : SameSquareClass K (s * d₁) (s * d₂) := by
  obtain ⟨t, ht, e⟩ := h
  refine ⟨t, ht, ?_⟩
  rw [map_mul, map_mul, e]; ring

theorem sameSquareClass_trans {K : Type*} [Field K] [CharZero K] {d₁ d₂ d₃ : ℚ} (h₁ : SameSquareClass K d₁ d₂)
    (h₂ : SameSquareClass K d₂ d₃) : SameSquareClass K d₁ d₃ := by
  obtain ⟨t, ht, e⟩ := h₁
  obtain ⟨s, hs, f⟩ := h₂
  exact ⟨t * s, mul_ne_zero ht hs, by rw [e, f]; ring⟩

/-- $\mu_p(n,\delta)$ depends only on the square class of $\delta$ in $\mathbb Q_p^\times$. -/
theorem muP_congr (p : Nat.Primes) (n : ℕ) {δ δ' : ℚ}
    (h : haveI : Fact p.1.Prime := ⟨p.2⟩; SameSquareClass ℚ_[p.1] δ δ') : muP p n δ = muP p n δ' := by
  have hneg : haveI : Fact p.1.Prime := ⟨p.2⟩; SameSquareClass ℚ_[p.1] (-δ) (-δ') := by
    simpa using sameSquareClass_mul_left (-1) h
  unfold muP
  rw [hp_congr_right p _ h, hp_congr_right p _ hneg]

/-- $c_p$ is the Hasse invariant over $\mathbb Q_p$. -/
theorem cP_eq_hasseInvariant (p : Nat.Primes) {n : ℕ} (a : Fin n → ℚ) :
    haveI : Fact p.1.Prime := ⟨p.2⟩; cP p a = hasseInvariant ℚ_[p.1] a :=
  hasseSerre_finite p a

theorem cP_pm (p : Nat.Primes) {n : ℕ} (a : Fin n → ℚ) : cP p a = 1 ∨ cP p a = -1 := by
  haveI : Fact p.1.Prime := ⟨p.2⟩
  rw [cP_eq_hasseInvariant, PadicClass.hasseInvariant_eq_hasseVec]
  exact PadicClass.hasseVec_pm _

theorem muP_pm (p : Nat.Primes) (n : ℕ) (δ : ℚ) : muP p n δ = 1 ∨ muP p n δ = -1 := by
  have h : ∀ x y : ℚ, ∀ k : ℕ, hp p x y ^ k = 1 ∨ hp p x y ^ k = -1 := fun x y k => by
    rcases hp_pm p x y with h | h <;> rw [h]
    · simp
    · exact neg_one_pow_eq_or ℤ k
  have m : ∀ u v : ℤ, (u = 1 ∨ u = -1) → (v = 1 ∨ v = -1) → (u * v = 1 ∨ u * v = -1) := by
    rintro u v (rfl | rfl) (rfl | rfl) <;> simp
  unfold muP
  split_ifs
  · exact m _ _ (h _ _ _) (hp_pm _ _ _)
  · exact m _ _ (h _ _ _) (hp_pm _ _ _)

theorem deltaQ_congr {K : Type*} [Field K] [CharZero K] {n : ℕ} {a b : Fin n → ℚ}
    (h : SameSquareClass K (∏ i, a i) (∏ i, b i)) : SameSquareClass K (deltaQ a) (deltaQ b) :=
  sameSquareClass_mul_left _ h

/-- $(-1)^{\lfloor n/2\rfloor}\delta = \prod_ia_i$. -/
theorem neg_one_pow_mul_deltaQ {n : ℕ} (a : Fin n → ℚ) : (-1) ^ (n / 2) * deltaQ a = ∏ i, a i := by
  unfold deltaQ
  rw [← mul_assoc, ← mul_pow, show (-1 : ℚ) * -1 = 1 by norm_num, one_pow, one_mul]

/-- **The Gan–Hanke–Yu invariants are invariants of the $\mathbb Q_p$-space**: isometric diagonal forms over $\mathbb Q_p$ have the same
$w_p$, and their $\delta$'s lie in the same square class of $\mathbb Q_p^\times$. -/
theorem wP_congr (p : Nat.Primes) {n : ℕ} {a b : Fin n → ℚ} (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (h : haveI : Fact p.1.Prime := ⟨p.2⟩; (diag a).IsometricIn ℚ_[p.1] (diag b)) :
    wP p a = wP p b ∧ ∀ x, hp p x (deltaQ a) = hp p x (deltaQ b) := by
  haveI : Fact p.1.Prime := ⟨p.2⟩
  obtain ⟨hd, hc⟩ := (isometric_padic_iff_invariants p.1 a b ha hb).1 h
  have hδ := deltaQ_congr hd
  refine ⟨?_, fun x => hp_congr_right p x hδ⟩
  unfold wP
  rw [cP_eq_hasseInvariant, cP_eq_hasseInvariant, hc, muP_congr p n hδ]

/-! ### Products of signs over the primes -/

/-- For a function of the primes with values $\pm1$ and finitely many $-1$'s, $\prod_pf(p) = (-1)^{\#\{p : f(p) = -1\}}$. -/
theorem finprod_eq_neg_one_pow {f : Nat.Primes → ℤ} (hf : ∀ p, f p = 1 ∨ f p = -1)
    (hfin : Function.HasFiniteMulSupport f) :
    {p | f p = -1}.Finite ∧ ∏ᶠ p, f p = (-1) ^ {p | f p = -1}.ncard := by
  have hsupp : Function.mulSupport f = {p | f p = -1} := by
    ext p
    simp only [Function.mem_mulSupport, Set.mem_ofPred_eq]
    rcases hf p with h | h <;> simp [h]
  have hS : {p | f p = -1}.Finite := hsupp ▸ hfin
  refine ⟨hS, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hS.toFinset) (by rw [hsupp, Set.Finite.coe_toFinset]),
    Finset.prod_congr rfl (fun p hp' => (Set.Finite.mem_toFinset hS).1 hp'), Finset.prod_const,
    Set.ncard_eq_toFinset_card _ hS]

/-! ### The real place -/

/-- A diagonal form isometric over $\mathbb R$ to $\langle1,\dots,1\rangle$ has positive coefficients. -/
theorem pos_of_isometricIn_real {n : ℕ} {a : Fin n → ℚ}
    (h : (diag a).IsometricIn ℝ (diag (fun _ => (1 : ℚ)))) (i : Fin n) : 0 < a i := by
  obtain ⟨P, hP, hx⟩ := h
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 hP
  set y : Fin n → ℝ := P⁻¹ *ᵥ Pi.single i 1
  have hPy : P *ᵥ y = Pi.single i 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]
  have hy : y ≠ 0 := by
    intro h0
    have := hPy
    rw [h0, Matrix.mulVec_zero] at this
    have h1 := congrFun this i
    simp at h1
  have e := hx y
  rw [hPy, QuadForm.evalIn_diag, QuadForm.evalIn_diag] at e
  simp only [Pi.single_apply, map_one, one_mul] at e
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at e
  simp only [ite_true, one_pow, mul_one, eq_ratCast] at e
  have hpos : 0 < ∑ j, y j ^ 2 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
    exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj))) (Finset.single_le_sum (f := fun j => y j ^ 2)
      (fun j _ => sq_nonneg (y j)) (Finset.mem_univ j))
  have : (0 : ℝ) < a i := e ▸ hpos
  exact_mod_cast this

/-- $\Delta>0$ and $1$ are in the same real square class. -/
theorem sameSquareClass_real_one {Δ : ℚ} (hΔ : 0 < Δ) : SameSquareClass ℝ 1 Δ := by
  have hΔ' : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  refine ⟨(Real.sqrt Δ)⁻¹, inv_ne_zero (Real.sqrt_pos.2 hΔ').ne', ?_⟩
  rw [inv_pow, Real.sq_sqrt hΔ'.le, map_one, eq_ratCast, inv_mul_cancel₀ hΔ'.ne']

theorem hasseCassels_infinite_one {n : ℕ} : RatPlace.infinite.hasseCassels (fun _ : Fin n => (1 : ℚ)) = 1 := by
  unfold hasseCassels
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
  split_ifs
  · show hinf 1 1 = 1
    rw [hinf_eq one_ne_zero one_ne_zero, if_neg (by norm_num)]
  · rfl

/-! ### Lemma 5.2, local–global part -/

/-- The model space $\langle\Delta,1,\dots,1\rangle$. -/
def modelDelta {n : ℕ} (hn : 1 ≤ n) (Δ : ℚ) : Fin n → ℚ := Pi.mulSingle ⟨0, hn⟩ Δ

theorem modelDelta_pos {n : ℕ} (hn : 1 ≤ n) {Δ : ℚ} (hΔ : 0 < Δ) (i : Fin n) : 0 < modelDelta hn Δ i := by
  unfold modelDelta
  rcases eq_or_ne i ⟨0, hn⟩ with rfl | h
  · simpa using hΔ
  · rw [Pi.mulSingle_eq_of_ne h]; norm_num

theorem prod_modelDelta {n : ℕ} (hn : 1 ≤ n) (Δ : ℚ) : ∏ i, modelDelta hn Δ i = Δ := by
  unfold modelDelta
  rw [Finset.prod_pi_mulSingle', if_pos (Finset.mem_univ _)]

/-- **Lemma 5.2, local–global part** (Hanke 2011, p. 9): a collection of local spaces $\langle\alpha_p\rangle$ over $\mathbb Q_p$
($p$ prime, common dimension $n\ge1$; the paper has $n\ge2$) comes from a positive definite rational space
$\langle a_0,\dots,a_{n-1}\rangle$ ($a_i>0$; isometric to $\langle\alpha_p\rangle$ over every $\mathbb Q_p$) if and only if there is
$\Delta\in\mathbb Q_{>0}$ with $\Delta\equiv(-1)^{\lfloor n/2\rfloor}\delta_p$ modulo $(\mathbb Q_p^\times)^2$ for all $p$, and the product formula
(4) holds: finitely many $w_p\ne1$ and $\prod_pw_p = (-1)^{\lfloor n/4\rfloor}\prod_p(-1,\delta_p)_p^{\lfloor(n-1)/2\rfloor}$. *Erratum:*
the exponent in (4) is the corrected one (the paper prints $\lfloor(n+1)/2\rfloor$; see `lemma_5_2_printed_false`). The proof
is the paper's: Cassels Ch. 6, Thm. 1.3 (`Cassels.Ch6.exists_form_of_local`) rephrased in the Gan–Hanke–Yu invariants. -/
@[kb "hanke2011enumerating" "Lemma 5.2, p. 9 (local–global existence, with the corrected (4))"]
theorem lemma_5_2_exists {n : ℕ} (hn : 1 ≤ n) (α : Nat.Primes → Fin n → ℚ) (hα : ∀ p i, α p i ≠ 0) :
    (∃ a : Fin n → ℚ, (∀ i, 0 < a i) ∧
        ∀ p : Nat.Primes, haveI : Fact p.1.Prime := ⟨p.2⟩; (diag a).IsometricIn ℚ_[p.1] (diag (α p))) ↔
      (∃ Δ : ℚ, 0 < Δ ∧ ∀ p : Nat.Primes, haveI : Fact p.1.Prime := ⟨p.2⟩;
          SameSquareClass ℚ_[p.1] Δ ((-1) ^ (n / 2) * deltaQ (α p))) ∧
        Function.HasFiniteMulSupport (fun p => wP p (α p)) ∧
        ∏ᶠ p, wP p (α p) = (-1) ^ (n / 4) * (∏ᶠ p, hp p (-1) (deltaQ (α p))) ^ ((n - 1) / 2) := by
  constructor
  · rintro ⟨a, ha, hiso⟩
    have ha0 : ∀ i, a i ≠ 0 := fun i => (ha i).ne'
    have hw : ∀ p, wP p a = wP p (α p) ∧ ∀ x, hp p x (deltaQ a) = hp p x (deltaQ (α p)) := fun p =>
      wP_congr p ha0 (hα p) (hiso p)
    obtain ⟨hfin, hprod⟩ := lemma_5_2 hn a ha
    refine ⟨⟨∏ i, a i, Finset.prod_pos fun i _ => ha i, fun p => ?_⟩, ?_, ?_⟩
    · haveI : Fact p.1.Prime := ⟨p.2⟩
      rw [neg_one_pow_mul_deltaQ]
      exact ((isometric_padic_iff_invariants p.1 a (α p) ha0 (hα p)).1 (hiso p)).1
    · have : (fun p => wP p (α p)) = fun p => wP p a := funext fun p => (hw p).1.symm
      rw [this]; exact hfin
    · have e1 : (fun p => wP p (α p)) = fun p => wP p a := funext fun p => (hw p).1.symm
      have e2 : (fun p => hp p (-1) (deltaQ (α p))) = fun p => hp p (-1) (deltaQ a) :=
        funext fun p => ((hw p).2 (-1)).symm
      rw [e1, e2]; exact hprod
  · rintro ⟨⟨Δ, hΔ, hsq⟩, hfin, hprod⟩
    -- the model space `⟨Δ, 1, …, 1⟩`
    set a₀ := modelDelta hn Δ
    have ha₀ : ∀ i, 0 < a₀ i := modelDelta_pos hn hΔ
    obtain ⟨hfin₀, hprod₀⟩ := lemma_5_2 hn a₀ ha₀
    obtain ⟨hcfin₀, hcprod₀⟩ := finprod_cP ha₀
    -- `δ_p` and the model's `δ` agree in `ℚ_p^×/(ℚ_p^×)²`
    have hδ : ∀ p : Nat.Primes, haveI : Fact p.1.Prime := ⟨p.2⟩;
        SameSquareClass ℚ_[p.1] (deltaQ (α p)) (deltaQ a₀) := fun p => by
      haveI : Fact p.1.Prime := ⟨p.2⟩
      apply deltaQ_congr
      rw [prod_modelDelta, ← neg_one_pow_mul_deltaQ]
      exact sameSquareClass_symm (hsq p)
    -- `c_p(α_p) = w_p(α_p) w_p(a₀) c_p(a₀)`
    have hc : ∀ p, cP p (α p) = wP p (α p) * wP p a₀ * cP p a₀ := fun p => by
      unfold wP
      rw [muP_congr p n (hδ p)]
      rcases muP_pm p n (deltaQ a₀) with h | h <;> rcases cP_pm p a₀ with h' | h' <;>
        rw [h, h'] <;> ring
    have hcfin : Function.HasFiniteMulSupport (fun p => cP p (α p)) := by
      rw [funext hc]; exact (hfin.mul hfin₀).mul hcfin₀
    have hRHS : ∏ᶠ p, hp p (-1) (deltaQ (α p)) = ∏ᶠ p, hp p (-1) (deltaQ a₀) :=
      finprod_congr fun p => hp_congr_right p (-1) (hδ p)
    have hcprod : ∏ᶠ p, cP p (α p) = 1 := by
      have d1 : ∏ᶠ p, wP p (α p) * wP p a₀ * cP p a₀ = (∏ᶠ p, wP p (α p) * wP p a₀) * ∏ᶠ p, cP p a₀ :=
        finprod_mul_distrib (hfin.mul hfin₀) hcfin₀
      have d2 : ∏ᶠ p, wP p (α p) * wP p a₀ = (∏ᶠ p, wP p (α p)) * ∏ᶠ p, wP p a₀ :=
        finprod_mul_distrib hfin hfin₀
      rw [funext hc, d1, d2, hprod, hprod₀, hcprod₀, hRHS]
      have m1 : (-1 : ℚ) ≠ 0 := by norm_num
      have hδ0 : deltaQ a₀ ≠ 0 := by
        unfold deltaQ
        exact mul_ne_zero (pow_ne_zero _ m1) (Finset.prod_ne_zero_iff.2 fun i _ => (ha₀ i).ne')
      rw [(finprod_hp m1 hδ0).2]
      rcases hinf_pm (-1) (deltaQ a₀) with h | h <;> rw [h] <;>
        rcases neg_one_pow_eq_or ℤ (n / 4) with h' | h' <;> rw [h'] <;> ring_nf <;> simp
    -- Cassels' data: `⟨1, …, 1⟩` at `∞`, `⟨α_p⟩` at `p`
    let β : RatPlace → Fin n → ℚ := fun v => match v with
      | .infinite => fun _ => 1
      | .finite p => α p
    have hβ : ∀ v i, β v i ≠ 0 := fun v i => by
      cases v with
      | infinite => exact one_ne_zero
      | finite p => exact hα p i
    have hdet : ∀ v : RatPlace, v.atPlace fun K _ _ => SameSquareClass K (∏ i, β v i) Δ := fun v => by
      cases v with
      | infinite =>
        show SameSquareClass ℝ (∏ _i : Fin n, (1 : ℚ)) Δ
        rw [Finset.prod_const_one]; exact sameSquareClass_real_one hΔ
      | finite p =>
        haveI : Fact p.1.Prime := ⟨p.2⟩
        show SameSquareClass ℚ_[p.1] (∏ i, α p i) Δ
        rw [← neg_one_pow_mul_deltaQ]; exact sameSquareClass_symm (hsq p)
    have hcv : ∀ v : RatPlace, v.hasseCassels (β v) = match v with
        | .infinite => 1
        | .finite p => cP p (α p) := fun v => by
      cases v with
      | infinite => exact hasseCassels_infinite_one
      | finite p => rfl
    obtain ⟨hSfin, hSprod⟩ := finprod_eq_neg_one_pow (fun p => cP_pm p (α p)) hcfin
    have hset : {v : RatPlace | v.hasseCassels (β v) = -1} = RatPlace.finite '' {p | cP p (α p) = -1} := by
      ext v
      cases v with
      | infinite => simp [hcv]
      | finite p =>
        simp only [Set.mem_ofPred_eq, Set.mem_image]
        rw [hcv]
        constructor
        · intro h; exact ⟨p, h, rfl⟩
        · rintro ⟨q, hq, e⟩; cases e; exact hq
    have hinj : Function.Injective RatPlace.finite := fun a b h => by injection h
    have hfin' : {v : RatPlace | v.hasseCassels (β v) = -1}.Finite := by rw [hset]; exact hSfin.image _
    have heven : Even {v : RatPlace | v.hasseCassels (β v) = -1}.ncard := by
      rw [hset, Set.ncard_image_of_injective _ hinj]
      rw [hcprod] at hSprod
      exact (neg_one_pow_eq_one_iff_even (by norm_num)).1 hSprod.symm
    obtain ⟨a, ha, -, hiso⟩ := Cassels.Ch6.exists_form_of_local hn Δ hΔ.ne' β hβ hdet hfin' heven
    exact ⟨a, pos_of_isometricIn_real (hiso .infinite), fun p => hiso (.finite p)⟩

end QuadFormsKB.Hanke2011Enumerating
