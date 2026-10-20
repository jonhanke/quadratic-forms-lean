/-
# Local densities over a DVR: the depth bounds of Lemma 3.4 and Remarks 3.4.1(c), 3.5.1, 3.6.1

**Layer:** DVR ($R$ a discrete valuation ring with uniformizer $\pi$, finite residue field of size $q$, $2 \ne 0$,
$e = \mathrm{ord}_\pi 2$; every prime of a number field, including ramified dyadic ones).

**Proves** the quantitative content of Hanke 2004, Def. 3.3 and Lemma 3.4 (p. 361):

* `DVR.w_le_of_isLocalLevel`: in the corrected normal form every norm exponent satisfies $\nu_j \le \mathrm{ord}_\pi N$ (the
  step "$\max_j \nu_j \le \mathrm{ord}_\mathfrak p(N)$" from (2.5) in the proof of Lemma 3.4, at every prime).
* **Bad-type depth** (`DVR.repCountOf_unitOn_succ`, `DVR.repCountOf_nonZero_succ`): the non-Zero-type (Good $\cup$ Bad)
  counts satisfy $r^{*}_{\pi^{k+1}}(m) = q^{n-1}r^{*}_{\pi^k}(m)$ for **every** $m$ as soon as
  $k \ge \max_j\nu_j + 2e + 1$, hence for $k \ge \mathrm{ord}_\pi N + 2e + 1 = \mathrm{ord}_\pi(4N) + 1$. This is Lemma 3.4's
  "Bad-type depth $\le \mathrm{ord}_\mathfrak p(N) + 1$" combined with the level $2e+1$ ("mod $4\mathfrak p$") at which Good-type
  solutions lift (Lemma 3.2). The proof is the paper's recursion through $\pi_G$, $\pi_{B'}$, $\pi_{B''}$, run on counts of
  solutions with a unit coordinate in a prescribed set $V$ (`unitPat`, `repCountOf_badI_pat`, `repCountOf_badII_pat`:
  the maps $\pi_{B'}$, $\pi_{B''}$ with "extra congruence conditions mod $\mathfrak p$ of the kind we allow", p. 361).
* **Zero-type depth** (`DVR.zero_depth_le`): a solution mod $\pi^k$, $k > \mathrm{ord}_\pi m$, that is $\equiv 0 \bmod \pi^j$ has
  $2j \le \mathrm{ord}_\pi m$.
* **Good-type depth**: Lemma 3.2 (`DVR.repCountGood_add`, level $2e + 1 \le k$; depth $k - (2e+1) \le k - 1$).

and, as consequences, Remarks 3.4.1(c), 3.5.1 and 3.6.1 (p. 362) and the local constancy of $\beta_\pi$ used for the
finiteness of $B_{\mathbb T}$ (p. 372). See the docstrings and `docs/local-densities.md`.

**Depends on** `DVRLevel.lean` (and through it `DVRDyadic.lean`, `DVRGeneral.lean`).
-/
import QuadFormsKB.LocalDensity.DVRLevel

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Matrix

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-! ### Norm exponents are bounded by the level -/

/-- **$\nu_j \le \mathrm{ord}_\pi N$** (Hanke 2004, (2.5) as used in the proof of Lemma 3.4, p. 361, at every prime): if $Q$ is
in the corrected normal form `IsJordanFormW Q π P w` and $\pi^k$ is a local level of $Q$, then $w_i \le k$ for every $i$.
*Proof:* row $i$ of the Hessian is divisible by $\pi^{w_i}$, and $(HW)_{ii} = \pi^k$. -/
@[kb "hanke2004" "Proof of Lemma 3.4, p. 361 (max ν_j ≤ ord N)"]
theorem w_le_of_isLocalLevel {Q : QuadForm R n} {π : R} (hπ : Irreducible π) {P : Finset (Fin n × Fin n)}
    {w : Fin n → ℕ} (hJ : IsJordanFormW Q π P w) {k : ℕ} (hL : IsLocalLevel Q π k) (i : Fin n) :
    w i ≤ k := by
  obtain ⟨W, hW, -, -⟩ := hL
  have hc : ∀ a b, (a = i ∨ b = i) → π ^ w i ∣ Q.coeff a b := by
    intro a b hab
    by_cases h0 : Q.coeff a b = 0
    · rw [h0]; exact dvd_zero _
    by_cases hle : a ≤ b
    · obtain ⟨hw, hd⟩ := hJ.coeff_block a b hle h0
      rcases hab with rfl | rfl
      · exact hd
      · rw [← hw]; exact hd
    · exact absurd (Q.upper (show id b < id a from not_le.mp hle)) h0
  have hrow : ∀ l, π ^ w i ∣ Q.hessian i l := by
    intro l
    have : Q.hessian i l = Q.coeff i l + Q.coeff l i := by
      simp [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply]
    rw [this]
    exact dvd_add (hc i l (Or.inl rfl)) (hc l i (Or.inr rfl))
  have hii : (Q.hessian * W) i i = π ^ k := by
    rw [hW]; simp
  rw [Matrix.mul_apply] at hii
  have hd : π ^ w i ∣ π ^ k := hii ▸ Finset.dvd_sum fun l _ => (hrow l).mul_right _
  exact (pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).1 hd

/-- The maximum norm exponent is at most $\mathrm{ord}_\pi N$ for any normal form $\mathrm{GL}_n(R)$-equivalent to $Q$. -/
theorem w_le_levelExp {Q Q' : QuadForm R n} (hQ : Q.Nondegenerate) {π : R} (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) (hG : IsGLEquiv Q Q') {P : Finset (Fin n × Fin n)} {w : Fin n → ℕ}
    (hJ : IsJordanFormW Q' π P w) (i : Fin n) : w i ≤ levelExp Q π := by
  have hex := exists_isLocalLevel hQ hπ h20
  have hL : IsLocalLevel Q π (levelExp Q π) := (isLocalLevel_iff_levelExp_le hex _).2 le_rfl
  exact w_le_of_isLocalLevel hπ hJ ((hG.isLocalLevel_iff π _).1 hL) i

/-- **$\mathrm{ord}_\pi N \le \mathrm{ord}_\pi(2\det H)$**: $\pi^{\mathrm{ord}_\pi N} \mid 2\det H$ ($W = 2u^{-1}\operatorname{adj}H$ is a level matrix
for $\pi^v$, $2\det H = \pi^v u$). -/
theorem pow_levelExp_dvd {Q : QuadForm R n} (hQ : Q.Nondegenerate) {π : R} (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) : π ^ levelExp Q π ∣ 2 * Q.hessian.det := by
  obtain ⟨v, u, hv, hu⟩ := dvr_eq_pow_mul_unit hπ (mul_ne_zero h20 hQ)
  have hL : IsLocalLevel Q π v := by
    refine ⟨(hu.unit⁻¹ : Rˣ).val • (2 : R) • Q.hessian.adjugate, ?_, ?_, fun i => ?_⟩
    · rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, smul_smul]
      congr 1
      rw [mul_assoc, hv, mul_left_comm, IsUnit.val_inv_mul, mul_one]
    · rw [transpose_smul, transpose_smul, adjugate_transpose, hessian_transpose]
    · rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      exact (dvd_mul_right 2 _).mul_left _
  have hle := (isLocalLevel_iff_levelExp_le ⟨v, hL⟩ v).1 hL
  rw [hv]
  exact (pow_dvd_pow π hle).mul_right _

/-- **$\mathrm{ord}_\pi(4N) \le \mathrm{ord}_\pi(8\det H)$**: $\pi^{\mathrm{ord}_\pi N + 2e} \mid 8\det H$, $e = \mathrm{ord}_\pi 2$. -/
theorem pow_levelExp_add_dvd {Q : QuadForm R n} (hQ : Q.Nondegenerate) {π : R} (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) {e : ℕ} (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) :
    π ^ (levelExp Q π + 2 * e) ∣ 8 * Q.hessian.det := by
  rw [show (8 : R) * Q.hessian.det = (2 * 2) * (2 * Q.hessian.det) by ring, pow_add, mul_comm,
    two_mul, pow_add]
  exact mul_dvd_mul (mul_dvd_mul he.1 he.1) (pow_levelExp_dvd hQ hπ h20)

/-! ### The maps $\pi_{B'}$, $\pi_{B''}$ with a unit-pattern condition -/

/-- **The unit pattern of $\vec x$ on the coordinates $A$**: $j \mapsto (A_j \wedge x_j \not\equiv 0 \bmod \pi)$. -/
def unitPat (π : R) {k : ℕ} (A : Fin n → Prop) (x : Fin n → R ⧸ Ideal.span {π ^ k}) : Fin n → Prop :=
  fun j => A j ∧ ¬ Ideal.Quotient.mk _ π ∣ x j

/-- **Bad type I with a pattern condition** (Hanke 2004, map $\pi_{B'}$, p. 360, with "extra congruence conditions
mod $\mathfrak p$", p. 361): for $Q$ in normal form, $m = \pi m'$, $k \ge 2$, $Q'$ as in `repCountBadI_eq`, and any condition
$\Phi$ on the unit pattern of $\vec x$ on the coordinates with $\nu_j \ne 0$ (where $\vec x$ and its image agree mod $\pi$):
$$\#\{\vec x \bmod \pi^k : Q(\vec x) \equiv m,\ \vec x_{S_0} \equiv 0,\ \Phi\} = q^{s_1 + s_2}\,
  \#\{\vec y \bmod \pi^{k-1} : Q'(\vec y) \equiv m',\ \Phi\}.$$ -/
theorem repCountOf_badI_pat (Q Q' : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν)
    (hQ' : ∀ i j, (ν i = 0 → Q'.coeff i j = π * Q.coeff i j) ∧ (ν i ≠ 0 → Q.coeff i j = π * Q'.coeff i j))
    (m m' : R) (hm : m = π * m') (k : ℕ) (hk : 2 ≤ k) (Φ : (Fin n → Prop) → Prop) :
    repCountOf Q π k m (fun x => (∀ j, ν j = 0 → Ideal.Quotient.mk _ π ∣ x j) ∧
        Φ (unitPat π (fun j => ν j ≠ 0) x)) =
      q R ^ ((Finset.univ.filter fun i => 1 ≤ ν i).card) *
        repCountOf Q' π (k - 1) m' (fun y => Φ (unitPat π (fun j => ν j ≠ 0) y)) := by
  classical
  obtain ⟨N, rfl⟩ : ∃ N, k = N + 1 := ⟨k - 1, by omega⟩
  have hN : 1 ≤ N := by omega
  rw [show N + 1 - 1 = N by omega]
  have hπ0 := hπ.ne_zero
  subst hm
  let eI : Fin n → ℕ := fun j => if ν j = 0 then 1 else 0
  let tI : Fin n → ℕ := fun j => if ν j = 0 then 0 else 1
  let y : (Fin n → R ⧸ Ideal.span {π ^ (N + 1)}) → Fin n → R ⧸ Ideal.span {π ^ N} :=
    fun x j => coordMap π (N + 1) (eI j) N (x j)
  have key : ∀ x : Fin n → R ⧸ Ideal.span {π ^ (N + 1)},
      (Q.evalIn _ x = Ideal.Quotient.mk _ (π * m') ∧ ((∀ j, ν j = 0 → Ideal.Quotient.mk _ π ∣ x j) ∧
        Φ (unitPat π (fun j => ν j ≠ 0) x))) ↔
      ((∀ j, π ^ eI j ∣ qlift (x j)) ∧ (Q'.evalIn _ (y x) = Ideal.Quotient.mk _ m' ∧
        Φ (unitPat π (fun j => ν j ≠ 0) (y x)))) := by
    intro x
    have hdx : ∀ j, Ideal.Quotient.mk _ π ∣ x j ↔ π ∣ qlift (x j) :=
      fun j => mk_dvd_iff π (by omega) (x j)
    have hdy : ∀ j, ν j ≠ 0 → (Ideal.Quotient.mk _ π ∣ y x j ↔ π ∣ qlift (x j)) := by
      intro j hj
      simp only [y, coordMap, eI, hj, ite_false, divPow_zero]
      exact mk_dvd_mk_iff π hN _
    have hD : (∀ j, π ^ eI j ∣ qlift (x j)) ↔ ∀ j, ν j = 0 → Ideal.Quotient.mk _ π ∣ x j := by
      refine forall_congr' fun j => ?_
      by_cases h : ν j = 0 <;> simp [eI, h, hdx]
    have hpat : unitPat π (fun j => ν j ≠ 0) x = unitPat π (fun j => ν j ≠ 0) (y x) := by
      funext j
      simp only [unitPat, eq_iff_iff]
      constructor
      · rintro ⟨hj, h⟩; exact ⟨hj, by rwa [hdy j hj, ← hdx]⟩
      · rintro ⟨hj, h⟩; exact ⟨hj, by rwa [hdx, ← hdy j hj]⟩
    have hE : (∀ j, π ^ eI j ∣ qlift (x j)) →
        (Q.evalIn _ x = Ideal.Quotient.mk _ (π * m') ↔
          Q'.evalIn _ (y x) = Ideal.Quotient.mk _ m') := by
      intro hA
      rw [show π * m' = π ^ 1 * m' by ring]
      have hXY := evalIn_badI Q Q' π hπ0 P ν hJ hQ' _ _ (fun j => eq_mul_divPow (hA j))
      exact evalIn_eq_mk_iff Q Q' π hπ0 N 1 rfl x _ m' (by rw [pow_one]; exact hXY)
    rw [hpat]
    constructor
    · rintro ⟨hE', hA, hΦ⟩
      have hA' := hD.2 hA
      exact ⟨hA', (hE hA').1 hE', hΦ⟩
    · rintro ⟨hA, hE', hΦ⟩
      exact ⟨(hE hA).2 hE', hD.1 hA, hΦ⟩
  unfold repCountOf
  rw [Nat.card_congr (Equiv.subtypeEquivRight key),
    natCard_pi_fibres (fun j a => π ^ eI j ∣ qlift a) (fun j => coordMap π (N + 1) (eI j) N)
      (fun j => R ⧸ Ideal.span {π ^ tI j})
      (fun j b => coordFibre_nonempty π hπ0 N (eI j) (tI j)
        (by simp only [eI, tI]; split_ifs <;> omega) b)
      (fun y => Q'.evalIn _ y = Ideal.Quotient.mk _ m' ∧ Φ (unitPat π (fun j => ν j ≠ 0) y))]
  rw [mul_comm]
  congr 1
  simp only [natCard_quot_pow π hπ, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [tI]
  split_ifs <;> omega

/-- **Bad type II with a pattern condition** (Hanke 2004, map $\pi_{B''}$, p. 360, with extra congruence conditions,
p. 361): for $Q$ in normal form, $m = \pi^2 m'$, $k \ge 3$, $Q''$ as in `repCountBadII_eq`, and any condition $\Phi$ on the
unit pattern on the coordinates with $\nu_j \ge 2$:
$$\#\{\vec x \bmod \pi^k : Q(\vec x) \equiv m,\ \vec x_{S_0 \cup S_1} \equiv 0,\ \Phi\} = q^{2n - s_0 - s_1}\,
  \#\{\vec y \bmod \pi^{k-2} : Q''(\vec y) \equiv m',\ \Phi\}.$$ -/
theorem repCountOf_badII_pat (Q Q'' : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν)
    (hQ'' : ∀ i j, (2 ≤ ν i → Q.coeff i j = π ^ 2 * Q''.coeff i j) ∧ (ν i < 2 → Q''.coeff i j = Q.coeff i j))
    (m m' : R) (hm : m = π ^ 2 * m') (k : ℕ) (hk : 3 ≤ k) (Φ : (Fin n → Prop) → Prop) :
    repCountOf Q π k m (fun x => (∀ j, ν j ≤ 1 → Ideal.Quotient.mk _ π ∣ x j) ∧
        Φ (unitPat π (fun j => 2 ≤ ν j) x)) =
      q R ^ (2 * n - (Finset.univ.filter fun i => ν i ≤ 1).card) *
        repCountOf Q'' π (k - 2) m' (fun y => Φ (unitPat π (fun j => 2 ≤ ν j) y)) := by
  classical
  obtain ⟨N, rfl⟩ : ∃ N, k = N + 2 := ⟨k - 2, by omega⟩
  have hN : 1 ≤ N := by omega
  rw [show N + 2 - 2 = N by omega]
  have hπ0 := hπ.ne_zero
  subst hm
  let eI : Fin n → ℕ := fun j => if ν j ≤ 1 then 1 else 0
  let tI : Fin n → ℕ := fun j => if ν j ≤ 1 then 1 else 2
  let y : (Fin n → R ⧸ Ideal.span {π ^ (N + 2)}) → Fin n → R ⧸ Ideal.span {π ^ N} :=
    fun x j => coordMap π (N + 2) (eI j) N (x j)
  have key : ∀ x : Fin n → R ⧸ Ideal.span {π ^ (N + 2)},
      (Q.evalIn _ x = Ideal.Quotient.mk _ (π ^ 2 * m') ∧ ((∀ j, ν j ≤ 1 → Ideal.Quotient.mk _ π ∣ x j) ∧
        Φ (unitPat π (fun j => 2 ≤ ν j) x))) ↔
      ((∀ j, π ^ eI j ∣ qlift (x j)) ∧ (Q''.evalIn _ (y x) = Ideal.Quotient.mk _ m' ∧
        Φ (unitPat π (fun j => 2 ≤ ν j) (y x)))) := by
    intro x
    have hdx : ∀ j, Ideal.Quotient.mk _ π ∣ x j ↔ π ∣ qlift (x j) :=
      fun j => mk_dvd_iff π (by omega) (x j)
    have hdy : ∀ j, 2 ≤ ν j → (Ideal.Quotient.mk _ π ∣ y x j ↔ π ∣ qlift (x j)) := by
      intro j hj
      have : ¬ ν j ≤ 1 := by omega
      simp only [y, coordMap, eI, this, ite_false, divPow_zero]
      exact mk_dvd_mk_iff π hN _
    have hD : (∀ j, π ^ eI j ∣ qlift (x j)) ↔ ∀ j, ν j ≤ 1 → Ideal.Quotient.mk _ π ∣ x j := by
      refine forall_congr' fun j => ?_
      by_cases h : ν j ≤ 1 <;> simp [eI, h, hdx]
    have hpat : unitPat π (fun j => 2 ≤ ν j) x = unitPat π (fun j => 2 ≤ ν j) (y x) := by
      funext j
      simp only [unitPat, eq_iff_iff]
      constructor
      · rintro ⟨hj, h⟩; exact ⟨hj, by rwa [hdy j hj, ← hdx]⟩
      · rintro ⟨hj, h⟩; exact ⟨hj, by rwa [hdx, ← hdy j hj]⟩
    have hE : (∀ j, π ^ eI j ∣ qlift (x j)) →
        (Q.evalIn _ x = Ideal.Quotient.mk _ (π ^ 2 * m') ↔
          Q''.evalIn _ (y x) = Ideal.Quotient.mk _ m') := by
      intro hA
      exact evalIn_eq_mk_iff Q Q'' π hπ0 N 2 rfl x _ m'
        (evalIn_badII Q Q'' π hπ0 P ν hJ hQ'' _ _ fun j => eq_mul_divPow (hA j))
    rw [hpat]
    constructor
    · rintro ⟨hE', hA, hΦ⟩
      have hA' := hD.2 hA
      exact ⟨hA', (hE hA').1 hE', hΦ⟩
    · rintro ⟨hA, hE', hΦ⟩
      exact ⟨(hE hA).2 hE', hD.1 hA, hΦ⟩
  unfold repCountOf
  rw [Nat.card_congr (Equiv.subtypeEquivRight key),
    natCard_pi_fibres (fun j a => π ^ eI j ∣ qlift a) (fun j => coordMap π (N + 2) (eI j) N)
      (fun j => R ⧸ Ideal.span {π ^ tI j})
      (fun j b => coordFibre_nonempty π hπ0 N (eI j) (tI j)
        (by simp only [eI, tI]; split_ifs <;> omega) b)
      (fun y => Q''.evalIn _ y = Ideal.Quotient.mk _ m' ∧ Φ (unitPat π (fun j => 2 ≤ ν j) y))]
  rw [mul_comm]
  congr 1
  simp only [natCard_quot_pow π hπ, Finset.prod_pow_eq_pow_sum]
  congr 1
  have hsum : ∑ j, tI j + (Finset.univ.filter fun i => ν i ≤ 1).card = 2 * n := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (g := fun _ => 2) fun j _ => by simp only [tI]; split_ifs <;> rfl]
    simp [mul_comm]
  omega

/-! ### Counts with a unit-pattern condition as Hensel counts -/

/-- A count whose condition is tested on residues is a `countG` count. -/
theorem repCountOf_eq_countG (Q : QuadForm R n) (π : R) (K : ℕ) (m : R)
    (T : (Fin n → R ⧸ Ideal.span {π ^ K}) → Prop) (G : (Fin n → R) → Prop)
    (hTG : ∀ x, T x ↔ G (liftV π K x)) :
    repCountOf Q π K m T = countG Q π G m K := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  have hev : Q.evalIn (R ⧸ Ideal.span {π ^ K}) x = Ideal.Quotient.mk _ (Q.eval (liftV π K x)) := by
    conv_lhs => rw [← redV_liftV π K x]
    exact evalIn_redV Q π K _
  rw [hev, Ideal.Quotient.eq, Ideal.mem_span_singleton, hTG]

/-- Residue tests on a lift: $\pi \mid x_j$ in $R/\pi^K$ iff $\pi \mid$ (lift of $x$)$_j$ ($K \ge 1$). -/
theorem mk_dvd_iff_liftV (π : R) {K : ℕ} (hK : 1 ≤ K) (x : Fin n → R ⧸ Ideal.span {π ^ K}) (j : Fin n) :
    Ideal.Quotient.mk _ π ∣ x j ↔ π ∣ liftV π K x j := by
  have hx : x j = Ideal.Quotient.mk _ (liftV π K x j) := (congrFun (redV_liftV π K x) j).symm
  rw [hx, mk_pi_dvd_iff π K hK]

/-- Unit conditions are stable under $\vec x \mapsto \vec x + \pi\vec y$. -/
theorem not_dvd_add_pi_smul (π : R) (x y : Fin n → R) (j : Fin n) :
    ¬ π ∣ (x + π • y) j ↔ ¬ π ∣ x j := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [dvd_add_left (dvd_mul_right π _)]

/-! ### Uniform stabilization of the non-Zero-type counts (the Bad-type depth) -/

section Uniform

variable [Finite (IsLocalRing.ResidueField R)]

/-- **Counts with a unit coordinate in $V$ stabilize uniformly in $m$** (Hanke 2004, Lemma 3.4 and its proof, p. 361,
at every prime): let $Q$ be in normal form `IsJordanFormW Q π P ν`, $e = \mathrm{ord}_\pi 2$, $V$ a set of coordinates with
$\nu_i \le L$ for $i \in V$. Then for **every** $m$ and every $k \ge L + 2e + 1$,
$$\#\{\vec x \bmod \pi^{k+1} : Q(\vec x) \equiv m,\ \exists i \in V,\ \pi \nmid x_i\} = q^{n-1}\,
  \#\{\vec x \bmod \pi^{k} : Q(\vec x) \equiv m,\ \exists i \in V,\ \pi \nmid x_i\}.$$
*Proof:* the paper's recursion. Split by the first block level carrying a unit: some unit with $\nu_i = 0$ (Good type,
Hensel from $2e+1$: `countG_succ`); $\vec x_{S_0} \equiv 0$ and a unit with $\nu_i = 1$ ($\pi_{B'}$ to Good type of $Q'$ at
level $k - 1$: `repCountOf_badI_pat`); $\vec x_{S_0 \cup S_1} \equiv 0$ ($\pi_{B''}$ to $Q''$ at level $k - 2$ with $V$ replaced
by $V \cap S_2$, whose exponents drop by $2$: `repCountOf_badII_pat`, induction on $L$). Each $\pi_{B''}$ costs depth $2$
and each $\pi_{B'}$ depth $1$, so the Bad-type depth is $\le L$, plus the level $2e + 1$ of Lemma 3.2. -/
@[kb "hanke2004" "Lemma 3.4, p. 361 (Bad-type depth, uniform in m)"]
theorem repCountOf_unitOn_succ (π : R) (hπ : Irreducible π) (e : ℕ)
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (L : ℕ) :
    ∀ (Q : QuadForm R n) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ), IsJordanFormW Q π P ν →
    ∀ V : Finset (Fin n), (∀ i ∈ V, ν i ≤ L) → ∀ (m : R) (k : ℕ), L + 2 * e + 1 ≤ k →
      repCountOf Q π (k + 1) m (fun x => ∃ i ∈ V, ¬ Ideal.Quotient.mk _ π ∣ x i) =
        q R ^ (n - 1) * repCountOf Q π k m (fun x => ∃ i ∈ V, ¬ Ideal.Quotient.mk _ π ∣ x i) := by
  induction L using Nat.strong_induction_on with
  | _ L IH =>
  intro Q P ν hJ V hV m k hk
  classical
  have hπ0 := hπ.ne_zero
  have hfin : ∀ k, Finite (Fin n → R ⧸ Ideal.span {π ^ k}) := fun k => by
    have := finite_quot_pow π hπ k; infer_instance
  obtain ⟨hJI, hJII⟩ := isJordanFormW_badI_badII Q π hπ0 P ν hJ
  let ΦB : (Fin n → Prop) → Prop := fun p => (∃ i ∈ V, p i) ∧ ∃ i, ν i = 1 ∧ p i
  let ΦC : (Fin n → Prop) → Prop := fun p => ∃ i ∈ V, p i
  -- the three pieces at level `j`
  have hsplit : ∀ j, repCountOf Q π j m (fun x => ∃ i ∈ V, ¬ Ideal.Quotient.mk _ π ∣ x i) =
      repCountOf Q π j m (fun x => (∃ i ∈ V, ¬ Ideal.Quotient.mk _ π ∣ x i) ∧
        ∃ i, ν i = 0 ∧ ¬ Ideal.Quotient.mk _ π ∣ x i) +
      repCountOf Q π j m (fun x => (∀ l, ν l = 0 → Ideal.Quotient.mk _ π ∣ x l) ∧
        ΦB (unitPat π (fun l => ν l ≠ 0) x)) +
      repCountOf Q π j m (fun x => (∀ l, ν l ≤ 1 → Ideal.Quotient.mk _ π ∣ x l) ∧
        ΦC (unitPat π (fun l => 2 ≤ ν l) x)) := by
    intro j
    have := hfin j
    unfold repCountOf
    rw [natCard_split _ (fun x => Q.evalIn _ x = Ideal.Quotient.mk _ m ∧
        (∃ i ∈ V, ¬ Ideal.Quotient.mk _ π ∣ x i) ∧ ∃ i, ν i = 0 ∧ ¬ Ideal.Quotient.mk _ π ∣ x i)
      (fun x => Q.evalIn _ x = Ideal.Quotient.mk _ m ∧
        (∃ i ∈ V, ¬ Ideal.Quotient.mk _ π ∣ x i) ∧ ¬ ∃ i, ν i = 0 ∧ ¬ Ideal.Quotient.mk _ π ∣ x i)
      (fun x => ∃ i, ν i = 0 ∧ ¬ Ideal.Quotient.mk _ π ∣ x i) (fun x => by simp only [and_assoc])
      (fun x => by simp only [and_assoc]), add_assoc]
    congr 1
    refine natCard_split _ _ _ (fun x => ∃ i, ν i = 1 ∧ ¬ Ideal.Quotient.mk _ π ∣ x i)
      (fun x => ?_) (fun x => ?_)
    · simp only [ΦB, unitPat]
      constructor
      · rintro ⟨hE, hS0, ⟨i, hiV, hi0, hi⟩, ⟨i', hi'1, -, hi'⟩⟩
        exact ⟨⟨hE, ⟨i, hiV, hi⟩, fun ⟨l, hl0, hl⟩ => hl (hS0 l hl0)⟩, i', hi'1, hi'⟩
      · rintro ⟨⟨hE, ⟨i, hiV, hi⟩, hS0⟩, ⟨i', hi'1, hi'⟩⟩
        have hS0' : ∀ l, ν l = 0 → Ideal.Quotient.mk _ π ∣ x l := fun l hl0 => by
          by_contra h; exact hS0 ⟨l, hl0, h⟩
        exact ⟨hE, hS0', ⟨i, hiV, fun h0 => hi (hS0' i h0), hi⟩, ⟨i', hi'1, by omega, hi'⟩⟩
    · simp only [ΦC, unitPat]
      constructor
      · rintro ⟨hE, hS01, ⟨i, hiV, hi2, hi⟩⟩
        exact ⟨⟨hE, ⟨i, hiV, hi⟩, fun ⟨l, hl0, hl⟩ => hl (hS01 l (by omega))⟩,
          fun ⟨l, hl1, hl⟩ => hl (hS01 l (by omega))⟩
      · rintro ⟨⟨hE, ⟨i, hiV, hi⟩, hS0⟩, hS1⟩
        have hS01 : ∀ l, ν l ≤ 1 → Ideal.Quotient.mk _ π ∣ x l := fun l hl => by
          by_contra h
          rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hl with h0 | h1
          · exact hS0 ⟨l, h0, h⟩
          · exact hS1 ⟨l, h1, h⟩
        refine ⟨hE, hS01, ⟨i, hiV, ?_, hi⟩⟩
        by_contra h2; exact hi (hS01 i (by omega))
  -- Good part: Hensel from level `2e + 1`
  have hA : ∀ j, 2 * e + 1 ≤ j →
      repCountOf Q π (j + 1) m (fun x => (∃ i ∈ V, ¬ Ideal.Quotient.mk _ π ∣ x i) ∧
        ∃ i, ν i = 0 ∧ ¬ Ideal.Quotient.mk _ π ∣ x i) =
      q R ^ (n - 1) * repCountOf Q π j m (fun x => (∃ i ∈ V, ¬ Ideal.Quotient.mk _ π ∣ x i) ∧
        ∃ i, ν i = 0 ∧ ¬ Ideal.Quotient.mk _ π ∣ x i) := by
    intro j hj
    let G : (Fin n → R) → Prop := fun z => (∃ i ∈ V, ¬ π ∣ z i) ∧ ∃ i, ν i = 0 ∧ ¬ π ∣ z i
    have hTG : ∀ K, 1 ≤ K → ∀ x : Fin n → R ⧸ Ideal.span {π ^ K},
        ((∃ i ∈ V, ¬ Ideal.Quotient.mk _ π ∣ x i) ∧ ∃ i, ν i = 0 ∧ ¬ Ideal.Quotient.mk _ π ∣ x i) ↔
          G (liftV π K x) := by
      intro K hK x
      simp only [G, mk_dvd_iff_liftV π hK]
    have hGs : ∀ x y, G x → G (x + π • y) := by
      intro x y hx
      simp only [G, not_dvd_add_pi_smul]; exact hx
    have hGt : ∀ x, G x → ∃ l, ¬ π ^ (e + 1) ∣ (Q.hessian *ᵥ x) l := by
      rintro x ⟨-, i, hi0, hi⟩
      exact exists_hessian_not_dvd_of_gradBound Q π hπ P ν hJ e (gradBound_ord_two hJ e he) x
        ⟨i, hi0, hi⟩
    rw [repCountOf_eq_countG Q π _ m _ G (hTG _ (by omega)),
      repCountOf_eq_countG Q π _ m _ G (hTG _ (by omega))]
    exact countG_succ Q π hπ G hGs e hGt m hj
  -- Bad type I part
  have hB : repCountOf Q π (k + 1) m (fun x => (∀ l, ν l = 0 → Ideal.Quotient.mk _ π ∣ x l) ∧
        ΦB (unitPat π (fun l => ν l ≠ 0) x)) =
      q R ^ (n - 1) * repCountOf Q π k m (fun x => (∀ l, ν l = 0 → Ideal.Quotient.mk _ π ∣ x l) ∧
        ΦB (unitPat π (fun l => ν l ≠ 0) x)) := by
    by_cases hL0 : L = 0
    · have h0 : ∀ j, repCountOf Q π j m (fun x => (∀ l, ν l = 0 → Ideal.Quotient.mk _ π ∣ x l) ∧
          ΦB (unitPat π (fun l => ν l ≠ 0) x)) = 0 := by
        intro j
        unfold repCountOf
        rw [Nat.card_eq_zero]; left
        refine ⟨fun ⟨x, _, _, ⟨i, hiV, hi0, _⟩, _⟩ => hi0 ?_⟩
        have := hV i hiV; omega
      rw [h0, h0, mul_zero]
    by_cases h1 : π ∣ m
    · have hm1 : m = π * divPow π 1 m := by
        have := eq_mul_divPow (π := π) (e := 1) (r := m) (by rwa [pow_one]); rwa [pow_one] at this
      rw [repCountOf_badI_pat Q (badIForm Q π ν) π hπ P ν hJ (badIForm_rel hJ) m _ hm1 _ (by omega),
        repCountOf_badI_pat Q (badIForm Q π ν) π hπ P ν hJ (badIForm_rel hJ) m _ hm1 _ (by omega),
        show k + 1 - 1 = (k - 1) + 1 by omega, mul_left_comm]
      congr 1
      let G : (Fin n → R) → Prop := fun z =>
        (∃ i ∈ V, ν i ≠ 0 ∧ ¬ π ∣ z i) ∧ ∃ i, ν i = 1 ∧ ν i ≠ 0 ∧ ¬ π ∣ z i
      have hTG : ∀ K, 1 ≤ K → ∀ y : Fin n → R ⧸ Ideal.span {π ^ K},
          ΦB (unitPat π (fun l => ν l ≠ 0) y) ↔ G (liftV π K y) := by
        intro K hK y
        simp only [ΦB, G, unitPat, mk_dvd_iff_liftV π hK]
      have hGs : ∀ x y, G x → G (x + π • y) := by
        intro x y hx
        simp only [G, not_dvd_add_pi_smul]; exact hx
      have hGt : ∀ x, G x → ∃ l, ¬ π ^ (e + 1) ∣ ((badIForm Q π ν).hessian *ᵥ x) l := by
        rintro x ⟨-, i, hi1, -, hi⟩
        exact exists_hessian_not_dvd_of_gradBound _ π hπ P _ hJI e (gradBound_ord_two hJI e he) x
          ⟨i, by simp [nuI, hi1], hi⟩
      rw [repCountOf_eq_countG _ π _ _ _ G (hTG _ (by omega)),
        repCountOf_eq_countG _ π _ _ _ G (hTG _ (by omega))]
      exact countG_succ _ π hπ G hGs e hGt _ (by omega)
    · have h0 : ∀ j, 1 ≤ j → repCountOf Q π j m (fun x => (∀ l, ν l = 0 → Ideal.Quotient.mk _ π ∣ x l) ∧
          ΦB (unitPat π (fun l => ν l ≠ 0) x)) = 0 := fun j hj =>
        repCountOf_eq_zero_of_not_dvd Q π P ν hJ m j 1 (by norm_num) hj (by rwa [pow_one]) _
          (fun x hx i hi => hx.1 i (by omega))
      rw [h0 _ (by omega), h0 _ (by omega), mul_zero]
  -- Bad type II part
  have hC : repCountOf Q π (k + 1) m (fun x => (∀ l, ν l ≤ 1 → Ideal.Quotient.mk _ π ∣ x l) ∧
        ΦC (unitPat π (fun l => 2 ≤ ν l) x)) =
      q R ^ (n - 1) * repCountOf Q π k m (fun x => (∀ l, ν l ≤ 1 → Ideal.Quotient.mk _ π ∣ x l) ∧
        ΦC (unitPat π (fun l => 2 ≤ ν l) x)) := by
    by_cases hL2 : L < 2
    · have h0 : ∀ j, repCountOf Q π j m (fun x => (∀ l, ν l ≤ 1 → Ideal.Quotient.mk _ π ∣ x l) ∧
          ΦC (unitPat π (fun l => 2 ≤ ν l) x)) = 0 := by
        intro j
        unfold repCountOf
        rw [Nat.card_eq_zero]; left
        refine ⟨fun ⟨x, _, _, ⟨i, hiV, hi2, _⟩⟩ => ?_⟩
        have := hV i hiV; omega
      rw [h0, h0, mul_zero]
    by_cases h2 : π ^ 2 ∣ m
    · rw [repCountOf_badII_pat Q (badIIForm Q π ν) π hπ P ν hJ (badIIForm_rel hJ) m _
          (eq_mul_divPow h2) _ (by omega),
        repCountOf_badII_pat Q (badIIForm Q π ν) π hπ P ν hJ (badIIForm_rel hJ) m _
          (eq_mul_divPow h2) _ (by omega),
        show k + 1 - 2 = (k - 2) + 1 by omega, mul_left_comm]
      congr 1
      have hpred : ∀ j (y : Fin n → R ⧸ Ideal.span {π ^ j}), ΦC (unitPat π (fun l => 2 ≤ ν l) y) ↔
          ∃ i ∈ V.filter (fun i => 2 ≤ ν i), ¬ Ideal.Quotient.mk _ π ∣ y i := by
        intro j y
        simp only [ΦC, unitPat, Finset.mem_filter, and_assoc]
      simp only [hpred]
      refine IH (L - 2) (by omega) _ P (nuII ν) hJII _ (fun i hi => ?_) _ _ (by omega)
      rw [Finset.mem_filter] at hi
      have := hV i hi.1
      simp only [nuII, hi.2, ite_true]; omega
    · have h0 : ∀ j, 2 ≤ j → repCountOf Q π j m (fun x => (∀ l, ν l ≤ 1 → Ideal.Quotient.mk _ π ∣ x l) ∧
          ΦC (unitPat π (fun l => 2 ≤ ν l) x)) = 0 := fun j hj =>
        repCountOf_eq_zero_of_not_dvd Q π P ν hJ m j 2 le_rfl hj h2 _
          (fun x hx i hi => hx.1 i (by omega))
      rw [h0 _ (by omega), h0 _ (by omega), mul_zero]
  rw [hsplit, hsplit, hA k (by omega), hB, hC]
  ring

/-- The non-Zero-type predicate is "a unit coordinate somewhere". -/
theorem not_isZeroType_iff_unitOn (π : R) (k : ℕ) (x : Fin n → R ⧸ Ideal.span {π ^ k}) :
    ¬ IsZeroType π k x ↔ ∃ i ∈ (Finset.univ : Finset (Fin n)), ¬ Ideal.Quotient.mk _ π ∣ x i := by
  simp [IsZeroType]

/-- **Non-Zero-type counts of a normal form stabilize uniformly in $m$** (Hanke 2004, Lemma 3.4, p. 361): for $Q$ in
normal form with all $\nu_i \le L$, $r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^{k+1}}(m) = q^{n-1}r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^k}(m)$
for every $m$ and every $k \ge L + 2e + 1$ (`repCountOf_unitOn_succ` with $V$ = all coordinates). -/
theorem repCountOf_nonZero_succ_J (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν) (e : ℕ)
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (L : ℕ) (hL : ∀ i, ν i ≤ L) (m : R) (k : ℕ)
    (hk : L + 2 * e + 1 ≤ k) :
    repCountOf Q π (k + 1) m (fun x => ¬ IsZeroType π (k + 1) x) =
      q R ^ (n - 1) * repCountOf Q π k m (fun x => ¬ IsZeroType π k x) := by
  simp only [not_isZeroType_iff_unitOn]
  exact repCountOf_unitOn_succ π hπ e he L Q P ν hJ _ (fun i _ => hL i) m k hk

/-- **The level from which the primitive counts are uniform**: $K_0 = \mathrm{ord}_\pi N + 2e + 1 = \mathrm{ord}_\pi(4N) + 1$,
$e = \mathrm{ord}_\pi 2$ (`levelExp` is $\mathrm{ord}_\pi N$). -/
noncomputable def depthLevel (Q : QuadForm R n) (π : R) (e : ℕ) : ℕ := levelExp Q π + 2 * e + 1

/-- **Lemma 3.4, quantitative form, for every nondegenerate $Q$** (Hanke 2004, p. 361; every prime with $2 \ne 0$): with
$e = \mathrm{ord}_\pi 2$, for **every** $m \in R$ and every $k \ge \mathrm{ord}_\pi N + 2e + 1$,
$$r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^{k+1}}(m) = q^{n-1}\, r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^k}(m).$$
So the non-Zero-type solutions are all obtained by lifting from level $\mathrm{ord}_\pi(4N) + 1$: Lemma 3.4's Bad-type depth
$\le \mathrm{ord}_\mathfrak p(N) + 1$ together with Good-type lifting from "mod $4\mathfrak p$". *Proof:* pass to a normal form
(`exists_jordanFormW_isGLEquiv`; the counts and the level are $\mathrm{GL}_n(R)$-invariant), bound $\nu_j \le \mathrm{ord}_\pi N$
(`w_le_levelExp`) and apply `repCountOf_nonZero_succ_J`. -/
@[kb "hanke2004" "Lemma 3.4, p. 361 (depth bounds, uniform stabilization)"]
theorem repCountOf_nonZero_succ (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (m : R) (k : ℕ)
    (hk : depthLevel Q π e ≤ k) :
    repCountOf Q π (k + 1) m (fun x => ¬ IsZeroType π (k + 1) x) =
      q R ^ (n - 1) * repCountOf Q π k m (fun x => ¬ IsZeroType π k x) := by
  obtain ⟨Q', P, w, hJ, -, hG⟩ := exists_jordanFormW_isGLEquiv Q hQ π hπ h20
  rw [← hG.repCountOf_eq π (k + 1) m Not, ← hG.repCountOf_eq π k m Not]
  exact repCountOf_nonZero_succ_J Q' π hπ P w hJ e he (levelExp Q π)
    (w_le_levelExp hQ hπ h20 hG hJ) m k hk

/-- Iterated form of `repCountOf_nonZero_succ`: $r^{*}_{\pi^{k+l}}(m) = q^{(n-1)l}r^{*}_{\pi^k}(m)$ for $k \ge K_0$. -/
theorem repCountOf_nonZero_add (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (m : R) (k l : ℕ)
    (hk : depthLevel Q π e ≤ k) :
    repCountOf Q π (k + l) m (fun x => ¬ IsZeroType π (k + l) x) =
      q R ^ ((n - 1) * l) * repCountOf Q π k m (fun x => ¬ IsZeroType π k x) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [← Nat.add_assoc, repCountOf_nonZero_succ Q hQ π hπ h20 e he m _ (by omega), ih, ← mul_assoc,
      ← pow_add, Nat.mul_succ, Nat.add_comm (n - 1)]

/-- Counts mod $\pi^k$ depend only on $m \bmod \pi^k$. -/
theorem repCountOf_congr_mod (Q : QuadForm R n) (π : R) (k : ℕ) {m m' : R} (h : π ^ k ∣ m - m')
    (T : (Fin n → R ⧸ Ideal.span {π ^ k}) → Prop) :
    repCountOf Q π k m T = repCountOf Q π k m' T := by
  have : Ideal.Quotient.mk (Ideal.span {π ^ k}) m = Ideal.Quotient.mk _ m' := (mk_eq_mk_iff π k m m').2 h
  unfold repCountOf; rw [this]

theorem repCount_congr_mod (Q : QuadForm R n) (π : R) (k : ℕ) {m m' : R} (h : π ^ k ∣ m - m') :
    repCount Q π k m = repCount Q π k m' := by
  have : Ideal.Quotient.mk (Ideal.span {π ^ k}) m = Ideal.Quotient.mk _ m' := (mk_eq_mk_iff π k m m').2 h
  unfold repCount; rw [this]

/-- **The primitive counts depend only on $m \bmod \pi^{K_0}$** (Hanke 2004, Lemma 3.4 and Remark 3.4.1(c), p. 361): if
$m \equiv m' \pmod{\pi^{K_0}}$, $K_0 = \mathrm{ord}_\pi(4N) + 1$, then
$r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^k}(m) = r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^k}(m')$ for **every** $k$. -/
@[kb "hanke2004" "Remark 3.4.1(c), p. 361 (primitive counts locally constant in m)"]
theorem repCountOf_nonZero_congr (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {m m' : R}
    (h : π ^ depthLevel Q π e ∣ m - m') (k : ℕ) :
    repCountOf Q π k m (fun x => ¬ IsZeroType π k x) =
      repCountOf Q π k m' (fun x => ¬ IsZeroType π k x) := by
  set K := depthLevel Q π e
  by_cases hk : k ≤ K
  · exact repCountOf_congr_mod Q π k ((pow_dvd_pow π hk).trans h) _
  · obtain ⟨l, rfl⟩ : ∃ l, k = K + l := ⟨k - K, by omega⟩
    rw [repCountOf_nonZero_add Q hQ π hπ h20 e he m K l le_rfl,
      repCountOf_nonZero_add Q hQ π hπ h20 e he m' K l le_rfl, repCountOf_congr_mod Q π K h]

end Uniform

/-! ### Remark 3.4.1(c): the Good- and Bad-type terms -/

section BadTerm

variable [Finite (IsLocalRing.ResidueField R)]

/-- **The Good-type count depends only on $m \bmod \pi^{2e+1}$** (Lemma 3.2, p. 358): for $Q$ in normal form. -/
theorem repCountGood_congr (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν) (e : ℕ)
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {m m' : R} (h : π ^ (2 * e + 1) ∣ m - m') (k : ℕ) :
    repCountOf Q π k m (IsGoodType (unimodularCoords ν) π k) =
      repCountOf Q π k m' (IsGoodType (unimodularCoords ν) π k) := by
  by_cases hk : k ≤ 2 * e + 1
  · exact repCountOf_congr_mod Q π k ((pow_dvd_pow π hk).trans h) _
  · obtain ⟨l, rfl⟩ : ∃ l, k = 2 * e + 1 + l := ⟨k - (2 * e + 1), by omega⟩
    rw [repCountGood_add Q π hπ P ν hJ e he m _ l le_rfl, repCountGood_add Q π hπ P ν hJ e he m' _ l le_rfl,
      repCountOf_congr_mod Q π _ h]

/-- Non-Zero = Good + Bad. -/
theorem repCountOf_nonZero_eq_good_add_bad (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (S₀ : Finset (Fin n)) (k : ℕ) (m : R) :
    repCountOf Q π k m (fun x => ¬ IsZeroType π k x) =
      repCountOf Q π k m (IsGoodType S₀ π k) + repCountOf Q π k m (IsBadType S₀ π k) := by
  have := finite_quot_pow π hπ k
  unfold repCountOf
  refine natCard_split _ _ _ (IsGoodType S₀ π k) (fun x => ?_) (fun x => ?_)
  · simp only [IsGoodType]; tauto
  · simp only [IsBadType]; tauto

/-- **Remark 3.4.1(c)** (Hanke 2004, p. 361–362), at every prime: let $Q$ be in normal form with a local level $\pi^{N_0}$
($N_0 \ge \mathrm{ord}_\pi N$), $e = \mathrm{ord}_\pi 2$ and $K = N_0 + 2e + 1$. Then the Bad-type count $r^{\mathrm{Bad}}_{\pi^k}(m)$
depends only on $m \bmod \pi^K$, for every $k$; in particular it is the same for all $m$ with $\pi^K \mid m$ ("constancy of
the Bad-type term as $m$ becomes more $\mathfrak p$-divisible"). At $\mathfrak p \nmid 2$ ($e = 0$) the condition is $\mathrm{ord}_\pi m \ge \mathrm{ord}_\pi N + 1$, weaker
than the paper's $\mathrm{ord}_\mathfrak p(m) \ge \mathrm{ord}_\mathfrak p(N) + 2$. *Update (candidate; pending author):* at dyadic
$\mathfrak p$ this proof needs $\mathrm{ord}_\mathfrak p(m) \ge \mathrm{ord}_\mathfrak p(4N) + 1$, because the Good-type solutions of
the reduced forms lift only from "mod $4\mathfrak p$". -/
@[kb "hanke2004" "Remark 3.4.1(c), p. 361"]
theorem repCountBad_congr (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν) (e : ℕ)
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (N₀ : ℕ) (hN : IsLocalLevel Q π N₀) {m m' : R}
    (h : π ^ (N₀ + 2 * e + 1) ∣ m - m') (k : ℕ) :
    repCountOf Q π k m (IsBadType (unimodularCoords ν) π k) =
      repCountOf Q π k m' (IsBadType (unimodularCoords ν) π k) := by
  have hP : ∀ m₁ m₂ : R, π ^ (N₀ + 2 * e + 1) ∣ m₁ - m₂ → repCountOf Q π k m₁ (fun x => ¬ IsZeroType π k x) =
      repCountOf Q π k m₂ (fun x => ¬ IsZeroType π k x) := by
    intro m₁ m₂ h12
    by_cases hk : k ≤ N₀ + 2 * e + 1
    · exact repCountOf_congr_mod Q π k ((pow_dvd_pow π hk).trans h12) _
    · obtain ⟨l, rfl⟩ : ∃ l, k = N₀ + 2 * e + 1 + l := ⟨k - (N₀ + 2 * e + 1), by omega⟩
      have hst : ∀ m₀ : R, ∀ l, repCountOf Q π (N₀ + 2 * e + 1 + l) m₀
          (fun x => ¬ IsZeroType π (N₀ + 2 * e + 1 + l) x) = q R ^ ((n - 1) * l) *
            repCountOf Q π (N₀ + 2 * e + 1) m₀ (fun x => ¬ IsZeroType π (N₀ + 2 * e + 1) x) := by
        intro m₀ l
        induction l with
        | zero => simp
        | succ l ih =>
          rw [← Nat.add_assoc, repCountOf_nonZero_succ_J Q π hπ P ν hJ e he N₀
            (w_le_of_isLocalLevel hπ hJ hN) m₀ _ (by omega), ih, ← mul_assoc, ← pow_add, Nat.mul_succ,
            Nat.add_comm (n - 1)]
      rw [hst, hst, repCountOf_congr_mod Q π _ h12]
  have h1 := repCountOf_nonZero_eq_good_add_bad Q π hπ (unimodularCoords ν) k m
  have h2 := repCountOf_nonZero_eq_good_add_bad Q π hπ (unimodularCoords ν) k m'
  have hG := repCountGood_congr Q π hπ P ν hJ e he
    ((pow_dvd_pow π (by omega : 2 * e + 1 ≤ N₀ + 2 * e + 1)).trans h) k
  rw [hP m m' h] at h1
  omega

end BadTerm

/-! ### Zero-type depth -/

/-- **Zero-type depth $\le \mathrm{ord}_\pi m$** (Hanke 2004, Lemma 3.4, p. 361): if $\vec x \equiv \vec 0 \pmod{\pi^j}$ solves
$Q(\vec x) \equiv m \pmod{\pi^k}$ with $\pi^{a+1} \nmid m$ and $a < k$, then $2j \le a$; so a chain of $\pi_Z$ maps (each of depth
$2$) from level $k > \mathrm{ord}_\pi m$ has total depth $\le \mathrm{ord}_\pi m$. Any $Q$, any $R$. -/
@[kb "hanke2004" "Lemma 3.4, p. 361 (Zero-type depth)"]
theorem zero_depth_le (Q : QuadForm R n) (π : R) (x : Fin n → R) {j k a : ℕ} {m : R}
    (hx : ∀ i, π ^ j ∣ x i) (hsol : π ^ k ∣ Q.eval x - m) (ha : ¬ π ^ (a + 1) ∣ m) (hak : a < k) :
    2 * j ≤ a := by
  by_contra hlt
  choose y hy using hx
  have hQ : Q.eval x = (π ^ j) ^ 2 * Q.eval y := by
    have := evalIn_const_mul Q (π ^ j) y
    rw [show x = fun i => π ^ j * y i from funext hy]
    exact this
  apply ha
  have h1 : π ^ (a + 1) ∣ Q.eval x := by
    rw [hQ, ← pow_mul]; exact dvd_mul_of_dvd_left (pow_dvd_pow π (by omega)) _
  have h2 : π ^ (a + 1) ∣ Q.eval x - m := (pow_dvd_pow π (by omega)).trans hsol
  have := dvd_sub h1 h2
  rwa [sub_sub_cancel] at this

/-! ### Remark 3.5.1: local representability is decided at level $\mathrm{ord}_\pi(4N) + 1$ -/

section Represented

variable [Finite (IsLocalRing.ResidueField R)]

/-- No Zero-type solutions of $Q(\vec x) \equiv m \pmod{\pi^k}$ when $\pi^2 \nmid m$ and $k \ge 2$ (any $Q$). -/
theorem repCountOf_zeroType_eq_zero (Q : QuadForm R n) (π : R) {k : ℕ} (hk : 2 ≤ k) {m : R}
    (h2 : ¬ π ^ 2 ∣ m) : repCountOf Q π k m (IsZeroType π k) = 0 := by
  unfold repCountOf
  rw [Nat.card_eq_zero]; left
  refine ⟨fun ⟨x, hx, hz⟩ => h2 (pow_dvd_of_mk_dvd π k 2 hk m ?_)⟩
  choose y hy using hz
  rw [← hx, show x = fun i => Ideal.Quotient.mk _ π * y i from funext hy, evalIn_const_mul]
  exact dvd_mul_right _ _

/-- $0$ is represented at every level. -/
theorem repCount_zero_pos (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (k : ℕ) :
    0 < repCount Q π k 0 := by
  have := finite_quot_pow π hπ k
  unfold repCount
  have : Nonempty {x : Fin n → R ⧸ Ideal.span {π ^ k} //
      Q.evalIn (R ⧸ Ideal.span {π ^ k}) x = Ideal.Quotient.mk _ 0} :=
    ⟨⟨0, by simp [QuadForm.evalIn]⟩⟩
  exact Nat.card_pos

/-- **Positive primitive count at $K \ge K_0$ gives positive counts above $K$**, for every square multiple: if
$r^{*}_{\pi^K}(m') > 0$ then $r_{\pi^k}(\pi^{2j}m') > 0$ for all $k \ge K + 2j$. -/
theorem repCount_pos_of_nonZero_pos (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {K : ℕ} (hK : depthLevel Q π e ≤ K)
    {m' : R} (hp : 0 < repCountOf Q π K m' (fun x => ¬ IsZeroType π K x)) (j : ℕ) :
    ∀ k, K + 2 * j ≤ k → 0 < repCount Q π k (π ^ (2 * j) * m') := by
  induction j with
  | zero =>
    intro k hk
    obtain ⟨l, rfl⟩ : ∃ l, k = K + l := ⟨k - K, by omega⟩
    refine lt_of_lt_of_le ?_ (repCountOf_le_repCount Q π hπ _ _ (fun x => ¬ IsZeroType π (K + l) x))
    rw [mul_zero, pow_zero, one_mul, repCountOf_nonZero_add Q hQ π hπ h20 e he m' K l (by omega)]
    exact Nat.mul_pos (pow_pos q_pos _) hp
  | succ j ih =>
    intro k hk
    refine lt_of_lt_of_le ?_ (repCountOf_le_repCount Q π hπ _ _ (IsZeroType π k))
    rw [repCountZero_eq Q π hπ _ (π ^ (2 * j) * m') (by ring) k (by omega)]
    exact Nat.mul_pos (pow_pos q_pos _) (ih _ (by omega))

/-- The descent of `isLocallyRepresentedAt_iff_nonZero` (chains of $\pi_Z$, then a primitive solution). -/
theorem exists_nonZero_pos_of_repCount_pos (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R)
    (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {K : ℕ}
    (hK : depthLevel Q π e ≤ K) (a : ℕ) :
    ∀ m : R, ¬ π ^ (a + 1) ∣ m → ∀ k, a + K + 1 ≤ k → 0 < repCount Q π k m →
      ∃ j m', m = π ^ (2 * j) * m' ∧ 0 < repCountOf Q π K m' (fun x => ¬ IsZeroType π K x) := by
  induction a using Nat.strong_induction_on with
  | _ a IH =>
  intro m ha k hk hpos
  have hK1 : 1 ≤ K := le_trans (by unfold depthLevel; omega) hK
  rw [repCount_eq_zero_add_nonZero Q π hπ k m] at hpos
  by_cases hp : 0 < repCountOf Q π k m (fun x => ¬ IsZeroType π k x)
  · refine ⟨0, m, by simp, ?_⟩
    obtain ⟨l, rfl⟩ : ∃ l, k = K + l := ⟨k - K, by omega⟩
    rw [repCountOf_nonZero_add Q hQ π hπ h20 e he m K l (by omega)] at hp
    exact Nat.pos_of_mul_pos_left hp
  · have hZ : 0 < repCountOf Q π k m (IsZeroType π k) := by omega
    by_cases h2 : π ^ 2 ∣ m
    · have hm2 := eq_mul_divPow h2
      rw [repCountZero_eq Q π hπ m _ hm2 k (by omega)] at hZ
      have ha2 : 2 ≤ a := by
        by_contra hlt
        exact ha ((pow_dvd_pow π (by omega)).trans h2)
      have ha' : ¬ π ^ (a - 2 + 1) ∣ divPow π 2 m := by
        intro h
        apply ha
        rw [hm2, show a + 1 = 2 + (a - 2 + 1) by omega, pow_add]
        exact mul_dvd_mul_left _ h
      obtain ⟨j, m', hj, hp'⟩ := IH (a - 2) (by omega) _ ha' (k - 2) (by omega)
        (Nat.pos_of_mul_pos_left hZ)
      refine ⟨j + 1, m', ?_, hp'⟩
      rw [hm2, hj, show 2 * (j + 1) = 2 + 2 * j by ring, pow_add, mul_assoc]
    · rw [repCountOf_zeroType_eq_zero Q π (by omega) h2] at hZ
      exact absurd hZ (lt_irrefl 0)

/-- **Remark 3.5.1, every prime** (Hanke 2004, p. 362, corrected and sharpened): for $Q$ nondegenerate over $R$ with
$2 \ne 0$, $e = \mathrm{ord}_\pi 2$ and any $K \ge \mathrm{ord}_\pi N + 2e + 1 = \mathrm{ord}_\pi(4N) + 1$, $m$ is locally represented at $\pi$
iff $m = 0$ or some quotient $m' = m/\pi^{2j}$ of $m$ by a square factor has a **primitive** (non-Zero-type) solution of
$Q(\vec x) \equiv m' \pmod{\pi^K}$.
*Clarification (candidate; pending author):* the paper says "represented mod $\mathfrak p^{\mathrm{ord}_\mathfrak p(4N)+2}$"; a plain
(possibly Zero-type) solution does not suffice ($Q = x^2$, $p$ odd, $m = p^2u$ with $u$ a non-residue: $x = 0$ solves
$x^2 \equiv m \bmod p^2$ but $m$ is not a local square), so "represented" must mean primitively represented; and the
exponent $\mathrm{ord}_\mathfrak p(4N) + 2$ can be lowered to $\mathrm{ord}_\mathfrak p(4N) + 1$ (`isLocallyRepresentedAt_iff_nonZero_printed`
is the printed exponent). At $\mathfrak p \nmid 2N$, $K = 1$: "mod $\mathfrak p$" as printed. -/
@[kb "hanke2004" "Remark 3.5.1, p. 362"]
theorem isLocallyRepresentedAt_iff_nonZero (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R)
    (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {K : ℕ}
    (hK : depthLevel Q π e ≤ K) (m : R) :
    IsLocallyRepresentedAt Q π m ↔
      m = 0 ∨ ∃ j m', m = π ^ (2 * j) * m' ∧ 0 < repCountOf Q π K m' (fun x => ¬ IsZeroType π K x) := by
  constructor
  · intro hloc
    by_cases hm : m = 0
    · exact Or.inl hm
    right
    obtain ⟨a, -, ha⟩ := exists_pow_dvd_not_dvd π hπ hm
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hloc
    exact exists_nonZero_pos_of_repCount_pos Q hQ π hπ h20 e he hK a m ha (max N (a + K + 1))
      (le_max_right _ _) (hN _ (le_max_left _ _))
  · rintro (rfl | ⟨j, m', rfl, hp⟩)
    · exact Filter.Eventually.of_forall fun k => repCount_zero_pos Q π hπ k
    · exact Filter.eventually_atTop.2 ⟨K + 2 * j,
        repCount_pos_of_nonZero_pos Q hQ π hπ h20 e he hK hp j⟩

/-- **Remark 3.5.1 with the printed exponent** $\mathrm{ord}_\mathfrak p(4N) + 2$ (Hanke 2004, p. 362; $\mathrm{ord}_\pi 4 = 2e$),
"represented" read as "primitively represented" (see `isLocallyRepresentedAt_iff_nonZero`). -/
theorem isLocallyRepresentedAt_iff_nonZero_printed (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R)
    (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (m : R) :
    IsLocallyRepresentedAt Q π m ↔
      m = 0 ∨ ∃ j m', m = π ^ (2 * j) * m' ∧ 0 < repCountOf Q π (levelExp Q π + 2 * e + 2) m'
        (fun x => ¬ IsZeroType π (levelExp Q π + 2 * e + 2) x) :=
  isLocallyRepresentedAt_iff_nonZero Q hQ π hπ h20 e he (by unfold depthLevel; omega) m

/-- Local representability passes from $m$ to $\pi^2 m$ (any $Q$): $r_{\pi^k}(\pi^2m) \ge q^n r_{\pi^{k-2}}(m)$. -/
theorem isLocallyRepresentedAt_mul_sq (Q : QuadForm R n) (π : R) (hπ : Irreducible π) {m : R}
    (h : IsLocallyRepresentedAt Q π m) : IsLocallyRepresentedAt Q π (π ^ 2 * m) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  refine Filter.eventually_atTop.2 ⟨N + 2, fun k hk => ?_⟩
  refine lt_of_lt_of_le ?_ (repCountOf_le_repCount Q π hπ _ _ (IsZeroType π k))
  rw [repCountZero_eq Q π hπ _ m rfl k (by omega)]
  exact Nat.mul_pos (pow_pos q_pos _) (hN _ (by omega))

/-- **Local representability is constant on deep square classes** (Hanke 2004, Remark 3.6.1 and p. 372, "$m$ is locally
represented $\iff T'$ is"): if $\pi^{K_0} \mid m$, $K_0 = \mathrm{ord}_\pi(4N) + 1$, then $\pi^{2\nu}m$ is locally represented at $\pi$
iff $m$ is, for every $\nu$. -/
@[kb "hanke2004" "Remark 3.6.1, p. 362 (representability of deep square classes)"]
theorem isLocallyRepresentedAt_pow_mul_iff (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R)
    (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {m : R}
    (hm : π ^ depthLevel Q π e ∣ m) (ν : ℕ) :
    IsLocallyRepresentedAt Q π (π ^ (2 * ν) * m) ↔ IsLocallyRepresentedAt Q π m := by
  set K := depthLevel Q π e
  have step : ∀ m₀ : R, π ^ K ∣ m₀ →
      (IsLocallyRepresentedAt Q π (π ^ 2 * m₀) ↔ IsLocallyRepresentedAt Q π m₀) := by
    intro m₀ hm₀
    refine ⟨fun h => ?_, isLocallyRepresentedAt_mul_sq Q π hπ⟩
    have hcong : ∀ k, repCountOf Q π k (π ^ 2 * m₀) (fun x => ¬ IsZeroType π k x) =
        repCountOf Q π k m₀ (fun x => ¬ IsZeroType π k x) := fun k =>
      repCountOf_nonZero_congr Q hQ π hπ h20 e he
        (by rw [show π ^ 2 * m₀ - m₀ = (π ^ 2 - 1) * m₀ by ring]; exact dvd_mul_of_dvd_right hm₀ _) k
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
    by_cases hp : ∃ k, K ≤ k ∧ 0 < repCountOf Q π k m₀ (fun x => ¬ IsZeroType π k x)
    · obtain ⟨k₀, hk₀, hp₀⟩ := hp
      have hpK : 0 < repCountOf Q π K m₀ (fun x => ¬ IsZeroType π K x) := by
        obtain ⟨l, rfl⟩ : ∃ l, k₀ = K + l := ⟨k₀ - K, by omega⟩
        rw [repCountOf_nonZero_add Q hQ π hπ h20 e he m₀ K l le_rfl] at hp₀
        exact Nat.pos_of_mul_pos_left hp₀
      refine Filter.eventually_atTop.2 ⟨K, fun k hk => ?_⟩
      have := repCount_pos_of_nonZero_pos Q hQ π hπ h20 e he le_rfl hpK 0 k (by omega)
      simpa using this
    · push Not at hp
      refine Filter.eventually_atTop.2 ⟨N + K + 2, fun k hk => ?_⟩
      have h1 := hN (k + 2) (by omega)
      rw [repCount_eq_zero_add_nonZero Q π hπ, repCountZero_eq Q π hπ _ m₀ rfl _ (by omega),
        hcong, Nat.le_zero.1 (hp (k + 2) (by omega)), add_zero, show k + 2 - 2 = k by omega] at h1
      exact Nat.pos_of_mul_pos_left h1
  induction ν with
  | zero => simp
  | succ ν ih =>
    rw [show π ^ (2 * (ν + 1)) * m = π ^ 2 * (π ^ (2 * ν) * m) by ring]
    exact (step _ (dvd_mul_of_dvd_right hm _)).trans ih

/-! ### Remark 3.6.1: $\pi$-stability -/

/-- **Remark 3.6.1, every prime** (Hanke 2004, p. 362): if $m$ is locally represented at $\pi$ and
$\pi^{\mathrm{ord}_\pi N + 2e - 1} \mid m$ ($e = \mathrm{ord}_\pi 2$), then $m$ is $\pi$-stable: for **every** $k$ and $\nu \ge 1$,
$r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^k}(\pi^{2\nu}m) = r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^k}(\pi^2 m)$ (both arguments are
$\equiv 0 \bmod \pi^{K_0}$; `repCountOf_nonZero_congr`). At $\pi \nmid 2$ this is $\pi^{\mathrm{ord}_\pi N - 1} \mid m$, weaker than the
paper's $m \in \mathfrak s_\mathfrak p = \mathfrak p^{\mathrm{ord}_\mathfrak p N}$ (`isPStable_of_nondyadic`).
*Update (candidate; pending author):* at dyadic $\mathfrak p$ this proof gives $\mathfrak p$-stability on
$\mathfrak p^{\mathrm{ord}_\mathfrak p(4N) - 1}$; the printed $\mathfrak s_\mathfrak p = \mathfrak p^{\mathrm{ord}_\mathfrak p N}$ is not proved here at dyadic
$\mathfrak p$ (it would follow from uniform primitive stabilization from level $\mathrm{ord}_\mathfrak p N + 1$, which holds in all
examples checked by brute force over $\mathbb{Z}_2$ but is not proved). For the stable ideal of p. 372 any ideal works; the
global corollaries use $8\det H$ (`docs/local-densities.md`). -/
@[kb "hanke2004" "Remark 3.6.1, p. 362"]
theorem isPStable_of_dvd (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (S₀ : Finset (Fin n)) {m : R}
    (hm : π ^ (levelExp Q π + 2 * e - 1) ∣ m) (hloc : IsLocallyRepresentedAt Q π m) :
    IsPStable Q S₀ π m := by
  refine ⟨hloc, Filter.Eventually.of_forall fun k ν hν => ?_⟩
  refine repCountOf_nonZero_congr Q hQ π hπ h20 e he ?_ k
  have hd : π ^ depthLevel Q π e ∣ π ^ 2 * m := by
    unfold depthLevel
    exact (pow_dvd_pow π (show levelExp Q π + 2 * e + 1 ≤ levelExp Q π + 2 * e - 1 + 2 by omega)).trans
      (by rw [show levelExp Q π + 2 * e - 1 + 2 = 2 + (levelExp Q π + 2 * e - 1) by omega, pow_add];
          exact mul_dvd_mul_left _ hm)
  have hd' : π ^ depthLevel Q π e ∣ π ^ (2 * ν) * m := by
    rw [show 2 * ν = (2 * ν - 2) + 2 by omega, pow_add, mul_assoc]
    exact dvd_mul_of_dvd_right hd _
  exact dvd_sub hd' hd

/-- **Remark 3.6.1 as printed, at $\pi \nmid 2$** (Hanke 2004, p. 362): every locally represented $m \in \mathfrak s_\mathfrak p =
\mathfrak p^{\mathrm{ord}_\mathfrak p N}$ is $\mathfrak p$-stable. -/
theorem isPStable_of_nondyadic (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (S₀ : Finset (Fin n)) {m : R} (hm : π ^ levelExp Q π ∣ m)
    (hloc : IsLocallyRepresentedAt Q π m) : IsPStable Q S₀ π m :=
  isPStable_of_dvd Q hQ π hπ (fun h => h2 (h ▸ dvd_zero _)) 0 ⟨by simp, by simpa using h2⟩ S₀
    ((pow_dvd_pow π (by omega)).trans hm) hloc

/-- **Remark 3.6.1 at every prime with the ideal $4N$**: every locally represented $m \in \mathfrak p^{\mathrm{ord}_\mathfrak p(4N)}$ is
$\mathfrak p$-stable. -/
theorem isPStable_of_dvd_four_level (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (S₀ : Finset (Fin n)) {m : R}
    (hm : π ^ (levelExp Q π + 2 * e) ∣ m) (hloc : IsLocallyRepresentedAt Q π m) : IsPStable Q S₀ π m :=
  isPStable_of_dvd Q hQ π hπ h20 e he S₀ ((pow_dvd_pow π (by omega)).trans hm) hloc

end Represented

/-! ### Local constancy of $\beta_\pi$ and $C_\pi$ (finiteness of $B_{\mathbb T}$) -/

section Constancy

variable [Finite (IsLocalRing.ResidueField R)]

/-- **All counts depend only on $m \bmod \pi^{\mathrm{ord}_\pi m + K_0}$**: if $\pi^{a+1} \nmid m$ and
$m \equiv m' \pmod{\pi^{a + K_0}}$ then $r_{\pi^k}(m) = r_{\pi^k}(m')$ for every $k$ (Zero-type chains of length
$\le a/2$, then `repCountOf_nonZero_congr`). -/
theorem repCount_congr (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (a : ℕ) :
    ∀ m m' : R, ¬ π ^ (a + 1) ∣ m → π ^ (a + depthLevel Q π e) ∣ m - m' →
      ∀ k, repCount Q π k m = repCount Q π k m' := by
  induction a using Nat.strong_induction_on with
  | _ a IH =>
  intro m m' ha h k
  set K := depthLevel Q π e
  have hK1 : 1 ≤ K := by unfold K depthLevel; omega
  rw [repCount_eq_zero_add_nonZero Q π hπ k m, repCount_eq_zero_add_nonZero Q π hπ k m',
    repCountOf_nonZero_congr Q hQ π hπ h20 e he ((pow_dvd_pow π (by omega)).trans h) k]
  congr 1
  by_cases hk : k < 2
  · exact repCountOf_congr_mod Q π k ((pow_dvd_pow π (by omega)).trans h) _
  by_cases h2 : π ^ 2 ∣ m
  · have ha2 : 2 ≤ a := by
      by_contra hlt
      exact ha ((pow_dvd_pow π (by omega)).trans h2)
    have h2' : π ^ 2 ∣ m' := by
      have := dvd_sub h2 ((pow_dvd_pow π (by omega)).trans h)
      rwa [sub_sub_cancel] at this
    have hm2 := eq_mul_divPow h2
    have hm2' := eq_mul_divPow h2'
    rw [repCountZero_eq Q π hπ m _ hm2 k (by omega), repCountZero_eq Q π hπ m' _ hm2' k (by omega)]
    congr 1
    refine IH (a - 2) (by omega) _ _ (fun hd => ha ?_) ?_ (k - 2)
    · rw [hm2, show a + 1 = 2 + (a - 2 + 1) by omega, pow_add]; exact mul_dvd_mul_left _ hd
    · rw [hm2, hm2', ← mul_sub, show a + K = 2 + (a - 2 + K) by omega, pow_add] at h
      exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hπ.ne_zero)).1 h
  · have h2' : ¬ π ^ 2 ∣ m' := by
      intro h2'
      by_cases haK : 2 ≤ a + K
      · have := dvd_add ((pow_dvd_pow π haK).trans h) h2'
        rw [sub_add_cancel] at this; exact h2 this
      · have ha0 : a = 0 := by omega
        subst ha0
        have h1 : π ∣ m - m' := by simpa [show K = 1 by omega] using h
        have := dvd_add h1 ((dvd_pow_self π (by norm_num)).trans h2')
        rw [sub_add_cancel] at this
        exact ha (by simpa using this)
    rw [repCountOf_zeroType_eq_zero Q π (by omega) h2, repCountOf_zeroType_eq_zero Q π (by omega) h2']

/-- **$\beta_\pi$ is locally constant** (used for the finiteness of $B_{\mathbb T}$, Hanke 2004, p. 372): if $\pi^{a+1} \nmid m$ and
$m \equiv m' \pmod{\pi^{a + K_0}}$, $K_0 = \mathrm{ord}_\pi(4N) + 1$, then $\beta_\pi(m) = \beta_\pi(m')$. -/
@[kb "hanke2004" "p. 372 (local constancy of β_p behind the finiteness of B_T)"]
theorem localDensity_congr (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {a : ℕ} {m m' : R}
    (ha : ¬ π ^ (a + 1) ∣ m) (h : π ^ (a + depthLevel Q π e) ∣ m - m') :
    localDensity Q π m = localDensity Q π m' := by
  unfold localDensity
  simp only [repCount_congr Q hQ π hπ h20 e he a m m' ha h]

/-- The primitive density depends only on $m \bmod \pi^{K_0}$. -/
theorem localDensityOf_nonZero_congr (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {m m' : R}
    (h : π ^ depthLevel Q π e ∣ m - m') :
    localDensityOf Q π m (fun k x => ¬ IsZeroType π k x) =
      localDensityOf Q π m' (fun k x => ¬ IsZeroType π k x) := by
  unfold localDensityOf
  simp only [repCountOf_nonZero_congr Q hQ π hπ h20 e he h]

/-- **$C_\pi(T')$ and $C'_\pi(T')$ are locally constant**: if $\pi^{a+1} \nmid T$ and $T \equiv T' \pmod{\pi^{a+K_0}}$, then
$C_\pi(T) = C_\pi(T')$ and $C'_\pi(T) = C'_\pi(T')$. -/
theorem localConstC_congr (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {a : ℕ} {T T' : R}
    (ha : ¬ π ^ (a + 1) ∣ T) (h : π ^ (a + depthLevel Q π e) ∣ T - T') :
    localConstC Q π T = localConstC Q π T' ∧ localConstC' Q π T = localConstC' Q π T' := by
  have hC : localConstC Q π T = localConstC Q π T' := by
    unfold localConstC
    rw [localDensity_congr Q hQ π hπ h20 e he ha h, localDensityOf_nonZero_congr Q hQ π hπ h20 e he
      (m' := π ^ 2 * T') (by
        rw [← mul_sub]; exact dvd_mul_of_dvd_right ((pow_dvd_pow π (by omega)).trans h) _)]
  exact ⟨hC, by unfold localConstC'; rw [hC]⟩

end Constancy

end QuadFormsKB.LocalDensity.DVR
