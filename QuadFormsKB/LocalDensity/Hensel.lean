/-
# Local densities over a DVR: the Hensel toolkit behind Lemma 3.2

**Layer:** DVR. **Proves** the ingredients of Hanke 2004, Lemma 3.2 (p. 358) and its proof (pp. 358–359):
$\#(R/\pi^j) = q^j$ (`card_quot_pow`); $Q(\vec{x} + t\vec{y}) = Q(\vec{x}) + t\,(H\vec{x})\cdot\vec{y} + t^2 Q(\vec{y})$
(`evalIn_add_smul`); counting a linear congruence with a unit coefficient (`card_linear_congr`); and the
**gradient bound** `exists_hessian_not_dvd`: for $Q$ in normal form `IsJordanFormW` and $\vec{x}$ with
$\pi \nmid x_i$ for some $w_i = 0$, some entry of $H\vec{x}$ has valuation $\le e = \mathrm{ord}_\pi(2)$. (At dyadic
primes reduction mod $\pi^k$ does not have uniform fibres on solutions; see `Lemma32.lean`.)
**Depends on** `DyadicJordan.lean`.
-/
import QuadFormsKB.LocalDensity.DyadicJordan

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Matrix

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-- **$\#(R/\pi^j) = q^j$** for a uniformizer $\pi$ and finite residue field. *Proof:* the filtration
$R \supset \pi R \supset \dots \supset \pi^j R$ has successive quotients $\cong R/\pi$ (multiplication by $\pi^i$). -/
@[kb "serre1973" "Ch. II §1 [unverified]"]
theorem card_quot_pow [Finite (IsLocalRing.ResidueField R)] (π : R) (hπ : Irreducible π) (j : ℕ) :
    Nat.card (R ⧸ Ideal.span {π ^ j}) = q R ^ j := by
  have hspan : Ideal.span {π ^ j} = (IsLocalRing.maximalIdeal R) ^ j := by
    rw [← Ideal.span_singleton_pow, hπ.maximalIdeal_eq]
  rw [hspan, ← Submodule.cardQuot_apply,
    _root_.cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field R),
    Submodule.cardQuot_apply]
  rfl

/-- **Taylor expansion of a quadratic form** (exact; over any commutative $R$-algebra $S$):
$Q(\vec{x} + t\vec{y}) = Q(\vec{x}) + t\, \vec{x} \cdot H\vec{y} + t^2 Q(\vec{y})$, with $H$ the Hessian (the polar form is
`QuadForm.polar_eq_hessian`). -/
@[kb "hanke2004" "Lemma 3.2 proof, p. 359"]
theorem evalIn_add_smul (S : Type*) [CommRing S] [Algebra R S] (Q : QuadForm R n)
    (x y : Fin n → S) (t : S) :
    Q.evalIn S (x + t • y) =
      Q.evalIn S x + t * (x ⬝ᵥ (Q.hessian.map (algebraMap R S) *ᵥ y)) + t ^ 2 * Q.evalIn S y := by
  have h1 := polar_eq_hessian S Q x (t • y)
  have h2 : Q.evalIn S (t • y) = t ^ 2 * Q.evalIn S y := by
    rw [evalIn_eq_dotProduct, evalIn_eq_dotProduct, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, smul_eq_mul]
    ring
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] at h1
  linear_combination h1 + h2

/-- **Linear equation with a unit coefficient** (over any commutative ring $S$): if $g_{i_0}$ is a unit,
the solutions of $\sum_i g_i y_i = c$ in $S^n$ are in bijection with $S^{n-1}$ (the coordinates other
than $i_0$), so $\#\{\vec{y}\} = \#S^{\,n-1}$. -/
theorem nat_card_linear_eq_of_isUnit {S : Type*} [CommRing S] (g : Fin n → S) (i0 : Fin n)
    (hu : IsUnit (g i0)) (c : S) :
    Nat.card {y : Fin n → S // ∑ i, g i * y i = c} = Nat.card S ^ (n - 1) := by
  classical
  obtain ⟨u, hu⟩ := hu
  let F : {y : Fin n → S // ∑ i, g i * y i = c} → ({j : Fin n // j ≠ i0} → S) :=
    fun y j => y.1 j
  have hsplit : ∀ y : Fin n → S, ∑ i, g i * y i =
      g i0 * y i0 + ∑ i ∈ ({i0}ᶜ : Finset (Fin n)), g i * y i :=
    fun y => Fintype.sum_eq_add_sum_compl i0 _
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨y, hy⟩ ⟨y', hy'⟩ h
      have hoff : ∀ j, j ≠ i0 → y j = y' j := fun j hj => congrFun h ⟨j, hj⟩
      have hs : ∑ i ∈ ({i0}ᶜ : Finset (Fin n)), g i * y i =
          ∑ i ∈ ({i0}ᶜ : Finset (Fin n)), g i * y' i :=
        Finset.sum_congr rfl fun j hj => by
          rw [hoff j (by simpa using hj)]
      have h0 : g i0 * y i0 = g i0 * y' i0 := by
        rw [hsplit] at hy hy'; rw [hs] at hy; linear_combination hy - hy'
      have h0' : y i0 = y' i0 := by
        rw [← hu] at h0
        simpa using congrArg (fun t => (↑u⁻¹ : S) * t) h0
      apply Subtype.ext
      funext j
      by_cases hj : j = i0
      · subst hj; exact h0'
      · exact hoff j hj
    · intro z
      let y0 : Fin n → S := fun j => if h : j = i0 then 0 else z ⟨j, h⟩
      let s := ∑ i ∈ ({i0}ᶜ : Finset (Fin n)), g i * y0 i
      let y : Fin n → S := Function.update y0 i0 ((↑u⁻¹ : S) * (c - s))
      have hs : ∑ i ∈ ({i0}ᶜ : Finset (Fin n)), g i * y i = s :=
        Finset.sum_congr rfl fun j hj => by
          have : j ≠ i0 := by simpa using hj
          simp [y, Function.update_of_ne this]
      refine ⟨⟨y, ?_⟩, ?_⟩
      · rw [hsplit, hs]
        simp only [y, Function.update_self, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
        ring
      · funext j
        have hj := j.2
        simp [F, y, y0, hj]
  rw [Nat.card_eq_of_bijective F hF, Nat.card_pi, Finset.prod_const, Finset.card_univ]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]

/-- **Counting a linear congruence:** if some $g_i$ is a unit, the number of $\vec{y} \in (R/\pi^a)^n$ with
$\sum_i g_i y_i \equiv c \pmod{\pi^a}$ is $q^{a(n-1)}$ ($n \ge 1$). *Proof:* solve for $y_i$; the others are free. -/
@[kb "hanke2004" "Lemma 3.2 proof, p. 359"]
theorem card_linear_congr [Finite (IsLocalRing.ResidueField R)] (π : R) (hπ : Irreducible π)
    (hn : 1 ≤ n) (g : Fin n → R) (hg : ∃ i, IsUnit (g i)) (c : R) (a : ℕ) :
    Nat.card {y : Fin n → R ⧸ Ideal.span {π ^ a} //
      ∑ i, Ideal.Quotient.mk _ (g i) * y i = Ideal.Quotient.mk _ c} = q R ^ (a * (n - 1)) := by
  obtain ⟨i0, hi0⟩ := hg
  rw [nat_card_linear_eq_of_isUnit _ i0 (hi0.map _), card_quot_pow π hπ, ← pow_mul]

/-- **Gradient bound for Good-type vectors** (Hanke 2004, proof of Lemma 3.2, pp. 358–359; the only place
Lemma 3.2 uses the normal form). Let $Q$ be in local normal form `IsJordanFormW Q π P w`, let
$e = \mathrm{ord}_\pi(2)$ (given by `he`: $\pi^e \mid 2$, $\pi^{e+1} \nmid 2$), and let $\vec{x} \in R^n$ have
$\pi \nmid x_i$ for some unimodular coordinate $i$ ($w_i = 0$). Then some entry of $H\vec{x}$ ($H$ the Hessian) is
not divisible by $\pi^{e+1}$. *Proof:* if $i$ is unpaired, $(H\vec{x})_i = 2u x_i$ has valuation exactly $e$; if
$i$ lies in a pair $\{i, j\}$ with $w = 0$, then $(H\vec{x})_j = \pi^\mu(\beta x_i + \pi t x_j)$ with $\beta$ a
unit and $\mu \le w + e = e$. (At $\pi^2 \nmid 2$, $\mu = 0$ and this is a unit, as in the paper.) -/
@[kb "hanke2004" "Lemma 3.2 proof, pp. 358–359"]
theorem exists_hessian_not_dvd (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ) (hJ : IsJordanFormW Q π P w) (e : ℕ)
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (x : Fin n → R)
    (hx : ∃ i, w i = 0 ∧ ¬ π ∣ x i) :
    ∃ j, ¬ π ^ (e + 1) ∣ (Q.hessian *ᵥ x) j := by
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
    obtain ⟨hwe, -, -, -, μ, β, hβ, hβu, -, d1, d2, d3⟩ := h4 p0 hp0
    have hlt := h1 p0 hp0
    have hμ2 : π ^ μ ∣ 2 := by
      have hw0 : w p0.1 = 0 := by rcases hpi with h | h <;> [rw [h]; rw [hwe, h]] <;> exact hwi
      rwa [hw0, pow_zero, mul_one] at d3
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
    obtain ⟨t, ht⟩ := hjj
    have hU : IsUnit (β * x i + π * t * x j) := by
      refine dvr_isUnit_of_not_dvd hπ fun hdv => ?_
      have : π ∣ β * x i := by
        have := dvd_sub hdv (dvd_mul_of_dvd_left (dvd_mul_right π t) (x j))
        rwa [add_sub_cancel_right] at this
      exact dvr_not_dvd_of_isUnit hπ (hβu.mul hxu) this
    rw [hsum, hb, ht, show π ^ μ * β * x i + π ^ (μ + 1) * t * x j =
      π ^ μ * (β * x i + π * t * x j) by ring] at hd
    exact he.2 ((hU.dvd_mul_right.1 hd).trans hμ2)
  · obtain ⟨u, hu, huu⟩ := h5 i hp
    refine ⟨i, fun hd => ?_⟩
    have hsum : (Q.hessian *ᵥ x) i = Q.hessian i i * x i := by
      rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_single i]
      intro k hki
      rw [hz i k (Ne.symm hki) (fun h => hp ⟨_, h, Or.inl rfl⟩) (fun h => hp ⟨_, h, Or.inr rfl⟩),
        zero_mul]
    rw [hsum, hH, hu, hwi, pow_zero, one_mul] at hd
    have hunit2 : IsUnit (u * x i) := huu.mul hxu
    have : π ^ (e + 1) ∣ 2 := by
      have h' : (u + u) * x i = 2 * (u * x i) := by ring
      rw [h'] at hd
      exact (IsUnit.dvd_mul_right hunit2).mp hd
    exact he.2 this

end QuadFormsKB.LocalDensity.DVR
