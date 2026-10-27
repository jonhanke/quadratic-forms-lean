/-
# Local densities over a DVR: Lemma 3.2 from a lower level at dyadic primes

**Layer:** DVR ($R$ a discrete valuation ring with uniformizer $\pi$, residue field of size $q$; the interest
is in **dyadic** $\pi \mid 2$, with $e = \mathrm{ord}_\pi(2) \ge 1$ the ramification index of $2$, $q = 2^f$).

**Proves** the sharp form of Hanke 2004, Lemma 3.2 (p. 358) and of the sentence "Since $b$ is a unit, we may even
lift these solutions when $k = 1$" in its proof (p. 359):

* `DVR.countG_add` (general Hensel count): if a set $G \subseteq R^n$ of vectors is stable under
  $\vec{x} \mapsto \vec{x} + \pi\vec{y}$ and every $\vec{x} \in G$ has a gradient entry $(H\vec{x})_j$ of valuation
  $\le t$, then the number of $\vec{x} \bmod \pi^k$ in $G$ with $Q(\vec{x}) \equiv m \pmod{\pi^k}$ gets multiplied by
  exactly $q^{(n-1)l}$ from level $k$ to level $k + l$, for every $k \ge 2t + 1$.
* `DVR.exists_hessian_not_dvd_pair`: for $Q$ in normal form `IsJordanFormW`, a coordinate $i$ of a pair block
  with norm exponent $w = 0$ and scale exponent $\mu \le t$ (i.e. $\pi^{t+1} \nmid b$): if $\pi \nmid x_i$ then some
  gradient entry of $\vec{x}$ has valuation $\le \mu \le t$.
* `DVR.repCountGood_add_of_pairs`: if **every** unimodular coordinate ($w_i = 0$) lies in a pair block with
  $\mu \le t$, then Lemma 3.2 holds from $k \ge 2t + 1$; with $t = 0$ (all unimodular blocks binary with unit
  Hessian, the "even unimodular" part) from $k \ge 1$.

Since $\mu \le e$ always, $t = e$ recovers Lemma 3.2 as printed (`DVR.repCountGood_add`, $k \ge 2e + 1$); for
1-dimensional unimodular blocks $u x^2$ the gradient $2ux$ has valuation exactly $e$, and $2e + 1$ cannot be
lowered (`LocalDensity.localDensity_sumTwoSq_two` in `BridgeDyadic.lean`: $x_0^2 + x_1^2$ over $\mathbb{Z}_2$).

**Depends on** `Lemma32.lean`.
-/
import QuadFormsKB.LocalDensity.DVRTable2

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Matrix

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-! ### Hensel lifting for a general set of vectors with bounded gradient valuation -/

section General

variable (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (G : (Fin n → R) → Prop)
    (hGs : ∀ x y, G x → G (x + π • y)) (t : ℕ)
    (hGt : ∀ x, G x → ∃ j, ¬ π ^ (t + 1) ∣ (Q.hessian *ᵥ x) j) (m : R)

include hGs in
theorem G_add_pow (x y : Fin n → R) (hx : G x) (s : ℕ) (hs : 1 ≤ s) : G (x + π ^ s • y) := by
  have : π ^ s • y = π • (π ^ (s - 1) • y) := by
    rw [smul_smul, ← pow_succ']; congr 2; omega
  rw [this]; exact hGs x _ hx

include hGs hGt in
theorem dval_hessian_addG (x y : Fin n → R) (hx : G x) (s : ℕ) (hs : t + 1 ≤ s) :
    dval π (Q.hessian *ᵥ (x + π ^ s • y)) = dval π (Q.hessian *ᵥ x) := by
  have hb := hGt x hx
  obtain ⟨⟨j, hj⟩, hall⟩ := dval_spec π _ ⟨t, hb⟩
  have hle := dval_le π _ t hb
  set v := dval π (Q.hessian *ᵥ x)
  rw [mulVec_add, mulVec_smul]
  apply dval_eq
  · refine ⟨j, fun h => hj ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    exact (dvd_add_left (dvd_mul_of_dvd_left (pow_dvd_pow π (by omega)) _)).mp h
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact dvd_add (hall i) (dvd_mul_of_dvd_left (pow_dvd_pow π (by omega)) _)

/-- The predicate on $R^n$ cut out by the solutions mod $\pi^K$ in $G$ with gradient valuation $v$. -/
def PKG (K v : ℕ) (x : Fin n → R) : Prop :=
  π ^ K ∣ Q.eval x - m ∧ G x ∧ dval π (Q.hessian *ᵥ x) = v

include hGt in
theorem PKG_le {K v : ℕ} {x : Fin n → R} (hx : PKG Q π G m K v x) : v ≤ t := by
  rw [← hx.2.2]; exact dval_le π _ t (hGt x hx.2.1)

include hGs hGt in
theorem PKG_add {K v : ℕ} (hk : 2 * t + 1 ≤ K) (x y : Fin n → R) (hx : PKG Q π G m K v x) :
    PKG Q π G m K v (x + π ^ (K - v) • y) := by
  have hle := PKG_le Q π G t hGt m hx
  obtain ⟨hsol, hgood, hd⟩ := hx
  have hall : ∀ i, π ^ v ∣ (Q.hessian *ᵥ x) i := by
    have := (dval_spec π _ ⟨t, hGt x hgood⟩).2
    rwa [hd] at this
  refine ⟨?_, G_add_pow π G hGs x y hgood _ (by omega), ?_⟩
  · rw [eval_add_smul']
    have hD : π ^ v ∣ (Q.hessian *ᵥ x) ⬝ᵥ y :=
      Finset.dvd_sum fun i _ => dvd_mul_of_dvd_left (hall i) _
    obtain ⟨D, hD⟩ := hD
    have hK : π ^ K = π ^ (K - v) * π ^ v := by rw [← pow_add]; congr 1; omega
    have h2 : (π ^ (K - v)) ^ 2 = π ^ K * π ^ (K - 2 * v) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    rw [hD, h2, show Q.eval x + π ^ (K - v) * (π ^ v * D) + π ^ K * π ^ (K - 2 * v) * Q.eval y - m
      = (Q.eval x - m) + (π ^ (K - v) * π ^ v) * D + π ^ K * π ^ (K - 2 * v) * Q.eval y by ring, ← hK]
    exact dvd_add (dvd_add hsol (dvd_mul_right _ _)) (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
  · rw [dval_hessian_addG Q π G hGs t hGt x y hgood _ (by omega), hd]

include hπ hGs hGt in
theorem PKG_succ_iff {K v : ℕ} (hk : 2 * t + 1 ≤ K) (c : Fin n → R)
    (hc : PKG Q π G m K v c) (s : R) (hs : Q.eval c - m = π ^ K * s)
    (g' : Fin n → R) (hg : Q.hessian *ᵥ c = π ^ v • g') (z : Fin n → R) :
    PKG Q π G m (K + 1) v (c + π ^ (K - v) • z) ↔ π ∣ s + g' ⬝ᵥ z := by
  have hle := PKG_le Q π G t hGt m hc
  have hz := PKG_add Q π G hGs t hGt m hk c z hc
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hiff : π ^ (K + 1) ∣ Q.eval (c + π ^ (K - v) • z) - m ↔ π ∣ s + g' ⬝ᵥ z := by
    rw [eval_add_smul', hg, smul_dotProduct, smul_eq_mul]
    have hK : π ^ (K - v) * π ^ v = π ^ K := by rw [← pow_add]; congr 1; omega
    have h2 : (π ^ (K - v)) ^ 2 = π ^ (K + 1) * π ^ (K - 2 * v - 1) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    rw [h2, show Q.eval c + π ^ (K - v) * (π ^ v * (g' ⬝ᵥ z)) +
        π ^ (K + 1) * π ^ (K - 2 * v - 1) * Q.eval z - m =
        (Q.eval c - m) + (π ^ (K - v) * π ^ v) * (g' ⬝ᵥ z) +
        π ^ (K + 1) * (π ^ (K - 2 * v - 1) * Q.eval z) by ring, hK, hs,
      ← mul_add, dvd_add_left (dvd_mul_right _ _), pow_succ,
      mul_dvd_mul_iff_left (pow_ne_zero _ hπ0)]
  exact ⟨fun h => hiff.mp h.1, fun h => ⟨hiff.mpr h, hz.2⟩⟩

include hπ hGs hGt in
/-- **The lifting step for one gradient valuation $v$** (general $G$; as `step_equiv_v`). -/
theorem stepG_equiv_v {K : ℕ} (hk : 2 * t + 1 ≤ K) (v : ℕ) :
    Nonempty ({x : Fin n → R ⧸ Ideal.span {π ^ (K + 1)} //
        PKG Q π G m (K + 1) v (liftV π (K + 1) x)} ≃
      {x : Fin n → R ⧸ Ideal.span {π ^ K} // PKG Q π G m K v (liftV π K x)} ×
        (Fin (n - 1) → R ⧸ Ideal.span {π ^ 1})) := by
  classical
  have hπ0 : π ≠ 0 := hπ.ne_zero
  by_cases hv : v ≤ t
  swap
  · have : IsEmpty {x : Fin n → R ⧸ Ideal.span {π ^ (K + 1)} //
        PKG Q π G m (K + 1) v (liftV π (K + 1) x)} :=
      ⟨fun x => hv (PKG_le Q π G t hGt m x.2)⟩
    have : IsEmpty {x : Fin n → R ⧸ Ideal.span {π ^ K} //
        PKG Q π G m K v (liftV π K x)} :=
      ⟨fun x => hv (PKG_le Q π G t hGt m x.2)⟩
    exact ⟨Equiv.equivOfIsEmpty _ _⟩
  have hP : ∀ x y, PKG Q π G m K v x → PKG Q π G m K v (x + π ^ (K - v) • y) :=
    fun x y hx => PKG_add Q π G hGs t hGt m hk x y hx
  have hPK : ∀ x y, PKG Q π G m K v x → PKG Q π G m K v (x + π ^ K • y) := by
    intro x y hx
    have : π ^ K • y = π ^ (K - v) • (π ^ v • y) := by
      rw [smul_smul, ← pow_add]; congr 2; omega
    rw [this]; exact hP x _ hx
  have hPK1 : ∀ x y, PKG Q π G m (K + 1) v x → PKG Q π G m (K + 1) v (x + π ^ (K + 1) • y) := by
    rintro x y ⟨h1, h2, h3⟩
    exact ⟨sol_add Q π m _ x y h1, G_add_pow π G hGs x y h2 _ (by omega),
      by rw [dval_hessian_addG Q π G hGs t hGt x y h2 _ (by omega), h3]⟩
  have hP1P : ∀ x, PKG Q π G m (K + 1) v x → PKG Q π G m K v x := by
    rintro x ⟨h1, h2, h3⟩
    exact ⟨dvd_trans (pow_dvd_pow π (by omega)) h1, h2, h3⟩
  obtain ⟨e1⟩ := fiber_equiv π hπ0 (K - v) v K (by omega) (PKG Q π G m K v) (PKG Q π G m K v)
    (Fin n → R ⧸ Ideal.span {π ^ v}) hP (fun _ h => h) hPK
    (fun c hc => ⟨Equiv.subtypeUnivEquiv fun y => hP c _ hc⟩)
  have hF2 : ∀ c, PKG Q π G m K v c → Nonempty ({y : Fin n → R ⧸ Ideal.span {π ^ (v + 1)} //
      PKG Q π G m (K + 1) v (c + π ^ (K - v) • liftV π (v + 1) y)} ≃
      (Fin (n - 1) → R ⧸ Ideal.span {π ^ 1}) × (Fin n → R ⧸ Ideal.span {π ^ v})) := by
    intro c hc
    obtain ⟨s, hs⟩ := hc.1
    have hgood := hc.2.1
    obtain ⟨⟨j, hj⟩, hall⟩ := dval_spec π _ ⟨t, hGt c hgood⟩
    rw [hc.2.2] at hj hall
    let g' : Fin n → R := fun i => Classical.choose (hall i)
    have hg : Q.hessian *ᵥ c = π ^ v • g' := funext fun i => by
      simp only [Pi.smul_apply, smul_eq_mul, g']; exact Classical.choose_spec (hall i)
    have hgj : ¬ π ∣ g' j := by
      intro h; apply hj
      rw [show (Q.hessian *ᵥ c) j = π ^ v * g' j from congrFun hg j, pow_succ]
      exact mul_dvd_mul_left _ h
    have ea : {y : Fin n → R ⧸ Ideal.span {π ^ (v + 1)} //
        PKG Q π G m (K + 1) v (c + π ^ (K - v) • liftV π (v + 1) y)} ≃
        {y : Fin n → R ⧸ Ideal.span {π ^ (v + 1)} // π ∣ s + g' ⬝ᵥ liftV π (v + 1) y} :=
      Equiv.subtypeEquivRight fun y => PKG_succ_iff Q π hπ G hGs t hGt m hk c hc s hs g' hg _
    have hPl : ∀ z y, π ∣ s + g' ⬝ᵥ z → ∀ s', 1 ≤ s' → π ∣ s + g' ⬝ᵥ (z + π ^ s' • y) := by
      intro z y hz s' hs'
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, ← add_assoc]
      exact dvd_add hz (dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _)
    obtain ⟨eb⟩ := fiber_equiv π hπ0 1 v (v + 1) (by omega) (fun z => π ∣ s + g' ⬝ᵥ z)
      (fun z => π ∣ s + g' ⬝ᵥ z) (Fin n → R ⧸ Ideal.span {π ^ v})
      (fun z y hz => hPl z y hz 1 le_rfl) (fun _ h => h) (fun z y hz => hPl z y hz _ (by omega))
      (fun c' hc' => ⟨Equiv.subtypeUnivEquiv fun y => hPl c' _ hc' 1 le_rfl⟩)
    have ec : {z : Fin n → R ⧸ Ideal.span {π ^ 1} // π ∣ s + g' ⬝ᵥ liftV π 1 z} ≃
        {z : Fin n → R ⧸ Ideal.span {π ^ 1} //
          Ideal.Quotient.mk _ s + ∑ i, Ideal.Quotient.mk _ (g' i) * z i = 0} := by
      refine Equiv.subtypeEquivRight fun z => ?_
      have hz : ∀ i, z i = Ideal.Quotient.mk _ (liftV π 1 z i) := fun i =>
        (congrFun (redV_liftV π 1 z) i).symm
      have key : Ideal.Quotient.mk (Ideal.span {π ^ 1}) s +
          ∑ i, Ideal.Quotient.mk (Ideal.span {π ^ 1}) (g' i) * z i =
          Ideal.Quotient.mk (Ideal.span {π ^ 1}) (s + g' ⬝ᵥ liftV π 1 z) := by
        simp only [map_add, map_sum, map_mul, dotProduct, ← hz]
      rw [key, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, pow_one]
    obtain ⟨ed⟩ := linear_equiv_aux (fun i => Ideal.Quotient.mk (Ideal.span {π ^ 1}) (g' i))
      (Ideal.Quotient.mk _ s) j ((isUnit_of_not_dvd π hπ _ hgj).map _)
    have hcard : Fintype.card {i : Fin n // i ≠ j} = n - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
    let ee := Fintype.equivFinOfCardEq hcard
    exact ⟨ea.trans (eb.trans (Equiv.prodCongr (ec.trans (ed.trans
      (Equiv.arrowCongr ee (Equiv.refl _)))) (Equiv.refl _)))⟩
  obtain ⟨e2⟩ := fiber_equiv π hπ0 (K - v) (v + 1) (K + 1) (by omega) (PKG Q π G m K v)
    (PKG Q π G m (K + 1) v)
    ((Fin (n - 1) → R ⧸ Ideal.span {π ^ 1}) × (Fin n → R ⧸ Ideal.span {π ^ v})) hP hP1P hPK1 hF2
  exact ⟨e2.trans ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)).trans
    ((Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodCongr e1.symm (Equiv.refl _))))⟩

/-- **The count of solutions in $G$** mod $\pi^K$: $\#\{\vec{x} \in (R/\pi^K)^n : Q(\vec{x}) \equiv m,\ \vec{x} \in G\}$,
$G \subseteq R^n$ tested on (any) lift; well defined when $G$ is stable under $\pi R^n$-shifts. -/
noncomputable def countG (K : ℕ) : ℕ :=
  Nat.card {x : Fin n → R ⧸ Ideal.span {π ^ K} // π ^ K ∣ Q.eval (liftV π K x) - m ∧ G (liftV π K x)}

include hπ hGs hGt in
/-- **The lifting step for $G$**: $\#G_{K+1} = q^{n-1}\#G_K$ for $K \ge 2t + 1$. -/
theorem countG_succ {K : ℕ} (hk : 2 * t + 1 ≤ K) :
    countG Q π G m (K + 1) = q R ^ (n - 1) * countG Q π G m K := by
  classical
  unfold countG
  rw [← card_W π hπ, mul_comm, ← Nat.card_prod]
  apply Nat.card_congr
  have split : ∀ N : ℕ, {x : Fin n → R ⧸ Ideal.span {π ^ N} //
      π ^ N ∣ Q.eval (liftV π N x) - m ∧ G (liftV π N x)} ≃
      Σ v : ℕ, {x : Fin n → R ⧸ Ideal.span {π ^ N} // PKG Q π G m N v (liftV π N x)} := fun N =>
    (Equiv.sigmaFiberEquiv fun x : {x : Fin n → R ⧸ Ideal.span {π ^ N} //
        π ^ N ∣ Q.eval (liftV π N x) - m ∧ G (liftV π N x)} =>
      dval π (Q.hessian *ᵥ liftV π N x.1)).symm.trans
    (Equiv.sigmaCongrRight fun v => (Equiv.subtypeSubtypeEquivSubtypeInter _
      (fun x => dval π (Q.hessian *ᵥ liftV π N x) = v)).trans
      (Equiv.subtypeEquivRight fun x => by simp only [PKG, and_assoc]))
  exact (split (K + 1)).trans ((Equiv.sigmaCongrRight fun v =>
    (stepG_equiv_v Q π hπ G hGs t hGt m hk v).some).trans
    ((Equiv.sigmaProdDistrib _ _).symm.trans (Equiv.prodCongr (split K).symm (Equiv.refl _))))

include hπ hGs hGt in
/-- **Hensel count with bounded gradient valuation** (sharp form of Hanke 2004, Lemma 3.2 and its proof,
pp. 358–359): let $G \subseteq R^n$ be stable under $\vec{x} \mapsto \vec{x} + \pi\vec{y}$, and suppose every
$\vec{x} \in G$ has some gradient entry $(H\vec{x})_j$ ($H$ the Hessian) not divisible by $\pi^{t+1}$. Then for
$k \ge 2t + 1$ and $l \ge 0$,
$$\#\{\vec{x} \in (R/\pi^{k+l})^n : Q(\vec{x}) \equiv m,\ \vec{x} \in G\} = q^{(n-1)l}\, \#\{\vec{x} \in (R/\pi^k)^n : Q(\vec{x}) \equiv m,\ \vec{x} \in G\}.$$
The level $2t + 1$ comes from the Taylor expansion $Q(\vec{x} + \pi^{k-v}\vec{z}) = Q(\vec{x}) + \pi^{k-v}H\vec{x}\cdot\vec{z} +
\pi^{2(k-v)}Q(\vec{z})$, $v \le t$ the gradient valuation: one needs $2(k - v) \ge k + 1$ and $k - v \ge t + 1$. -/
@[kb "hanke2004" "Lemma 3.2 proof, pp. 358–359"]
theorem countG_add (k l : ℕ) (hk : 2 * t + 1 ≤ k) :
    countG Q π G m (k + l) = q R ^ ((n - 1) * l) * countG Q π G m k := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [← Nat.add_assoc, countG_succ Q π hπ G hGs t hGt m (by omega), ih, ← mul_assoc,
      ← pow_add, Nat.mul_succ, Nat.add_comm (n - 1)]

end General


/-! ### Gradient bounds from the block structure -/

/-- **The gradient-valuation bound $t$ of a normal form** `IsJordanFormW Q π P w`: every unimodular
coordinate ($w_i = 0$) has gradient valuation $\le t$, block by block:
1. an unpaired unimodular coordinate ($u x_i^2$, gradient $2u x_i$, valuation $e = \mathrm{ord}_\pi 2$) needs
   $\pi^{t+1} \nmid 2$, i.e. $t \ge e$;
2. a pair block $a x_i^2 + b x_i x_j + c x_j^2$ with $w = 0$ needs $\pi^{t+1} \nmid b$, i.e. its scale exponent
   $\mu = v(b)$ is $\le t$.
Always true for $t = e$ (`gradBound_ord_two`); true for $t = 0$ iff every unimodular block is binary with
unit Hessian ($b$ a unit; the even unimodular case). -/
@[kb "hanke2004" "Lemma 3.2 proof, p. 359 (gradient bound per block)"]
def GradBound (Q : QuadForm R n) (π : R) (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ) (t : ℕ) : Prop :=
  (∀ i, w i = 0 → ¬ IsPaired P i → ¬ π ^ (t + 1) ∣ 2) ∧
    (∀ p ∈ P, w p.1 = 0 → ¬ π ^ (t + 1) ∣ Q.coeff p.1 p.2)

/-- **$t = e$ is always a gradient bound** ($\mu \le w + e$ in every pair block). -/
theorem gradBound_ord_two {Q : QuadForm R n} {π : R} {P : Finset (Fin n × Fin n)}
    {w : Fin n → ℕ} (hJ : IsJordanFormW Q π P w) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) :
    GradBound Q π P w e := by
  refine ⟨fun _ _ _ => he.2, fun p hp hw hd => ?_⟩
  obtain ⟨-, -, -, μ, β, hβ, hβu, -, -, -, d3⟩ := (hJ.2.2.2.2.1 p hp).2
  rw [hw, pow_zero, mul_one] at d3
  rw [hβ] at hd
  exact he.2 (((hβu.dvd_mul_right).1 hd).trans d3)

/-- **Gradient bound for Good vectors under `GradBound t`** (generalizes `exists_hessian_not_dvd`, which is
the case $t = e$): if $Q$ is in normal form with gradient bound $t$ and $\pi \nmid x_i$ for some $w_i = 0$, then
some entry of $H\vec{x}$ is not divisible by $\pi^{t+1}$. -/
theorem exists_hessian_not_dvd_of_gradBound (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ) (hJ : IsJordanFormW Q π P w) (t : ℕ)
    (hB : GradBound Q π P w t) (x : Fin n → R) (hx : ∃ i, w i = 0 ∧ ¬ π ∣ x i) :
    ∃ j, ¬ π ^ (t + 1) ∣ (Q.hessian *ᵥ x) j := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hJ
  obtain ⟨i, hwi, hxi⟩ := hx
  have hH : ∀ a c, Q.hessian a c = Q.coeff a c + Q.coeff c a := fun a c => by
    simp [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply]
  have hz : ∀ a c, a ≠ c → (a, c) ∉ P → (c, a) ∉ P → Q.hessian a c = 0 := by
    intro a c hac h1' h2'
    rw [hH]
    rcases lt_or_gt_of_ne hac with h | h
    · rw [h3 a c h h1', Q.upper h, add_zero]
    · rw [h3 c a h h2', Q.upper h, zero_add]
  have hxu : IsUnit (x i) := dvr_isUnit_of_not_dvd hπ hxi
  by_cases hp : IsPaired P i
  · obtain ⟨p0, hp0, hpi⟩ := hp
    obtain ⟨hwe, -, -, -, μ, β, hβ, hβu, -, d1, d2, -⟩ := h4 p0 hp0
    have hlt := h1 p0 hp0
    have hw0 : w p0.1 = 0 := by rcases hpi with h | h <;> [rw [h]; rw [hwe, h]] <;> exact hwi
    have hμt : ¬ π ^ (t + 1) ∣ π ^ μ := fun hd =>
      hB.2 p0 hp0 hw0 (hβ ▸ dvd_mul_of_dvd_left hd β)
    obtain ⟨j, hij, hmem, hb, hjj⟩ : ∃ j, i ≠ j ∧ ((i, j) ∈ P ∨ (j, i) ∈ P) ∧
        Q.hessian j i = π ^ μ * β ∧ π ^ (μ + 1) ∣ Q.hessian j j := by
      rcases hpi with h | h
      · refine ⟨p0.2, by rw [← h]; exact ne_of_lt hlt, Or.inl (by rw [← h]; exact hp0), ?_, ?_⟩
        · subst h; rw [hH, Q.upper hlt, zero_add, hβ]
        · rw [hH, ← two_mul]; exact d2
      · refine ⟨p0.1, by rw [← h]; exact (ne_of_lt hlt).symm, Or.inr (by rw [← h]; exact hp0), ?_, ?_⟩
        · subst h; rw [hH, Q.upper hlt, add_zero, hβ]
        · rw [hH, ← two_mul]; exact d1
    refine ⟨j, fun hd => ?_⟩
    have hsum : (Q.hessian *ᵥ x) j = Q.hessian j i * x i + Q.hessian j j * x j := by
      rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_add i j hij]
      intro k ⟨hki, hkj⟩
      rw [hz j k (Ne.symm hkj), zero_mul]
      · intro hjk
        rcases hmem with hm | hm
        · have := h2 (i, j) hm (j, k) hjk (by intro h; simp only [Prod.mk.injEq] at h; exact hij h.1)
          exact this.2.2.1 rfl
        · have := h2 (j, i) hm (j, k) hjk (by intro h; simp only [Prod.mk.injEq] at h; exact hki h.2.symm)
          exact this.1 rfl
      · intro hkj'
        rcases hmem with hm | hm
        · have := h2 (i, j) hm (k, j) hkj' (by intro h; simp only [Prod.mk.injEq] at h; exact hki h.1.symm)
          exact this.2.2.2 rfl
        · have := h2 (j, i) hm (k, j) hkj' (by intro h; simp only [Prod.mk.injEq] at h; exact hkj h.1.symm)
          exact this.2.1 rfl
    obtain ⟨s, hs⟩ := hjj
    have hU : IsUnit (β * x i + π * s * x j) := by
      refine dvr_isUnit_of_not_dvd hπ fun hdv => ?_
      have : π ∣ β * x i := by
        have := dvd_sub hdv (dvd_mul_of_dvd_left (dvd_mul_right π s) (x j))
        rwa [add_sub_cancel_right] at this
      exact dvr_not_dvd_of_isUnit hπ (hβu.mul hxu) this
    rw [hsum, hb, hs, show π ^ μ * β * x i + π ^ (μ + 1) * s * x j =
      π ^ μ * (β * x i + π * s * x j) by ring] at hd
    exact hμt (hU.dvd_mul_right.1 hd)
  · obtain ⟨u, hu, huu⟩ := h5 i hp
    refine ⟨i, fun hd => ?_⟩
    have hsum : (Q.hessian *ᵥ x) i = Q.hessian i i * x i := by
      rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_single i]
      intro k hki
      rw [hz i k (Ne.symm hki) (fun h => hp ⟨_, h, Or.inl rfl⟩) (fun h => hp ⟨_, h, Or.inr rfl⟩),
        zero_mul]
    rw [hsum, hH, hu, hwi, pow_zero, one_mul] at hd
    have hunit2 : IsUnit (u * x i) := huu.mul hxu
    have h' : (u + u) * x i = 2 * (u * x i) := by ring
    rw [h'] at hd
    exact hB.1 i hwi hp ((IsUnit.dvd_mul_right hunit2).mp hd)

/-! ### Lemma 3.2 from level $2t + 1$ -/

theorem goodR_add_pi (S₀ : Finset (Fin n)) (π : R) (x y : Fin n → R) (hx : GoodR S₀ π x) :
    GoodR S₀ π (x + π • y) := by
  have := (goodR_add_iff S₀ π x y 1 le_rfl).2 hx
  rwa [pow_one] at this

/-- **Lemma 3.2 from level $2t + 1$** (Hanke 2004, Lemma 3.2, eq. (3.1), p. 358, sharpened as in its proof,
p. 359: "since $b$ is a unit, we may even lift these solutions when $k = 1$"): for $Q$ in normal form
`IsJordanFormW Q π P w` with gradient bound $t$ (`GradBound`: $t \ge e = \mathrm{ord}_\pi 2$ if some unimodular block
is 1-dimensional, and $t \ge \mu$ for every unimodular pair block), for $k \ge 2t + 1$ and $l \ge 0$,
$$r^{\mathrm{Good}}_{\pi^{k+l}}(m) = q^{(n-1)l}\, r^{\mathrm{Good}}_{\pi^k}(m).$$
With $t = e$ this is `repCountGood_add` ($k \ge 2e + 1$, the paper's bound, independent of $f$). With $t = 0$
(every unimodular block binary with unit middle coefficient) it holds from $k = 1$, for every $e$.
*Update (candidate; pending author):* in the corrected normal form a binary block
may have $b = \pi^\mu\beta$ with $\mu \ge 1$ (ramified dyadic primes), and then the level is $2\mu + 1$, not $1$; for
1-dimensional blocks $2e + 1$ is sharp (`LocalDensity.localDensity_sumTwoSq_two`). -/
@[kb "hanke2004" "Lemma 3.2, eq. (3.1), p. 358; proof, p. 359"]
theorem repCountGood_add_of_gradBound (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ) (hJ : IsJordanFormW Q π P w) (t : ℕ)
    (hB : GradBound Q π P w t) (m : R) (k l : ℕ) (hk : 2 * t + 1 ≤ k) :
    repCountOf Q π (k + l) m (IsGoodType (unimodularCoords w) π (k + l)) =
      q R ^ ((n - 1) * l) * repCountOf Q π k m (IsGoodType (unimodularCoords w) π k) := by
  rw [repCountOf_good_eq Q _ π (k + l) (by omega), repCountOf_good_eq Q _ π k (by omega)]
  exact countG_add Q π hπ (GoodR (unimodularCoords w) π) (goodR_add_pi _ π) t
    (fun x ⟨i, hi, hxi⟩ => exists_hessian_not_dvd_of_gradBound Q π hπ P w hJ t hB x
      ⟨i, (Finset.mem_filter.mp hi).2, hxi⟩) m k l hk

/-! ### Densities of unimodular forms at an explicit level -/

section Density

variable [Finite (IsLocalRing.ResidueField R)]

/-- Normalized Good-type counts are constant from level $K \ge 2t + 1$. -/
theorem normalized_good_const (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ) (hJ : IsJordanFormW Q π P w) (t : ℕ)
    (hB : GradBound Q π P w t) (m : R) (K k : ℕ) (hK : 2 * t + 1 ≤ K) (hk : K ≤ k) :
    (repCountOf Q π k m (IsGoodType (unimodularCoords w) π k) : ℝ) / (q R : ℝ) ^ (k * (n - 1)) =
      (repCountOf Q π K m (IsGoodType (unimodularCoords w) π K) : ℝ) / (q R : ℝ) ^ (K * (n - 1)) := by
  obtain ⟨l, rfl⟩ : ∃ l, k = K + l := ⟨k - K, by omega⟩
  have hq0 : (q R : ℝ) ≠ 0 := by exact_mod_cast (q_pos (R := R)).ne'
  rw [repCountGood_add_of_gradBound Q π hπ P w hJ t hB m K l hK,
    show (K + l) * (n - 1) = K * (n - 1) + (n - 1) * l by ring, pow_add]
  push_cast
  field_simp

/-- **Primitive density of a unimodular form at an explicit level** (dyadic Hanke 2004, Lemma 3.2 with
Remark 3.4.1(a), p. 361): if $Q$ is in normal form with all $w_i = 0$ and gradient bound $t$, then for every
$m$ and every $K \ge 2t + 1$,
$\beta^{\mathrm{Good}\cup\mathrm{Bad}}_\pi(m) = r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^K}(m)/q^{K(n-1)}$ (Good ∪ Bad = non-Zero type,
and there is no Bad type). -/
theorem localDensityOf_nonZero_unimodular (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (hJ : IsJordanFormW Q π P 0) (t : ℕ) (hB : GradBound Q π P 0 t)
    (m : R) (K : ℕ) (hK : 2 * t + 1 ≤ K) :
    localDensityOf Q π m (fun k x => ¬ IsZeroType π k x) =
      (repCountOf Q π K m (fun x => ¬ IsZeroType π K x) : ℝ) / (q R : ℝ) ^ (K * (n - 1)) := by
  apply limUnder_eq_of_eventually
  filter_upwards [Filter.eventually_ge_atTop K] with k hk
  have := normalized_good_const Q π hπ P 0 hJ t hB m K k hK hk
  rwa [isGoodType_unimodularCoords_zero, isGoodType_unimodularCoords_zero] at this

/-- **Dyadic Remark 3.4.1(a): unit densities of unimodular forms at an explicit level.** Let $\pi \mid 2$ be
allowed ($e = \mathrm{ord}_\pi 2$ arbitrary), $Q$ in normal form `IsJordanFormW Q π P 0` (all blocks unimodular) with
gradient bound $t$, and $\pi \nmid m$. Then all solutions are of Good type and for every $K \ge 2t + 1$
$$\beta_\pi(m) = \frac{r_{\pi^K}(m)}{q^{K(n-1)}}.$$
With $t = e$ (always allowed, `gradBound_ord_two`): level $K = 2e + 1$, i.e. "mod $4\pi$" as on p. 359. With
$t = 0$ (all blocks binary with unit middle coefficient): $K = 1$, as for $\pi \nmid 2$ (`DVR.localDensity_unit`).
Level $1$ is wrong in general when 1-dimensional blocks occur: see `LocalDensity.localDensity_sumTwoSq_two`
($x_0^2 + x_1^2$ over $\mathbb{Z}_2$). -/
@[kb "hanke2004" "Remark 3.4.1(a), p. 361; Lemma 3.2 (dyadic)"]
theorem localDensity_unit_unimodular (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (hJ : IsJordanFormW Q π P 0) (t : ℕ) (hB : GradBound Q π P 0 t)
    (m : R) (hm : ¬ π ∣ m) (K : ℕ) (hK : 2 * t + 1 ≤ K) :
    localDensity Q π m = (repCount Q π K m : ℝ) / (q R : ℝ) ^ (K * (n - 1)) := by
  have hz : ∀ k, 1 ≤ k → repCount Q π k m = repCountOf Q π k m (fun x => ¬ IsZeroType π k x) := by
    intro k hk
    rw [repCount_eq_zero_add_nonZero Q π hπ,
      repCountOf_eq_zero_of_not_dvd Q π P 0 hJ m k 1 (by omega) hk (by rwa [pow_one])
        (IsZeroType π k) (fun x hx i _ => hx i), zero_add]
  rw [hz K (by omega), ← localDensityOf_nonZero_unimodular Q π hπ P hJ t hB m K hK]
  unfold localDensity localDensityOf Filter.limUnder
  refine congrArg Filter.lim (Filter.map_congr ?_)
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  rw [hz k hk]

/-- **Densities at $\mathrm{ord}_\pi(m) = 1$ for unimodular forms at an explicit level** (dyadic version of
`DVR.localDensity_diag_ord_one`): $Q$ in normal form with all $w_i = 0$ and gradient bound $t$, $\pi \mid m$,
$\pi^2 \nmid m$, $K \ge 2t + 1$: there are no Zero-type solutions from level 2 on, so
$\beta_\pi(m) = r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^K}(m)/q^{K(n-1)}$. -/
theorem localDensity_ord_one_unimodular (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (hJ : IsJordanFormW Q π P 0) (t : ℕ) (hB : GradBound Q π P 0 t)
    (m : R) (hm : ¬ π ^ 2 ∣ m) (K : ℕ) (hK : 2 * t + 1 ≤ K) :
    localDensity Q π m =
      (repCountOf Q π K m (fun x => ¬ IsZeroType π K x) : ℝ) / (q R : ℝ) ^ (K * (n - 1)) := by
  rw [← localDensityOf_nonZero_unimodular Q π hπ P hJ t hB m K hK]
  unfold localDensity localDensityOf Filter.limUnder
  refine congrArg Filter.lim (Filter.map_congr ?_)
  filter_upwards [Filter.eventually_ge_atTop 2] with k hk
  rw [repCount_eq_zero_add_nonZero Q π hπ,
    repCountOf_eq_zero_of_not_dvd Q π P 0 hJ m k 2 le_rfl hk hm
      (IsZeroType π k) (fun x hx i _ => hx i), zero_add]

end Density

end QuadFormsKB.LocalDensity.DVR
