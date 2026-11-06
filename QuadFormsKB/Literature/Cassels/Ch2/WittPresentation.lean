/-
# Cassels, Chapter 2, §5: generators and relations for $G(k)$ and $W(k)$; the Witt group of a finite field

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 2, §5, pp. 26–27.

**Setting.** As in `Ch2/WittGroup.lean`: $k$ = `K` is a field with $2 \ne 0$ (`[Invertible (2 : K)]`); $G(k)$ = `G K`
is the Grothendieck group of the semigroup $S(k)$ of classes of regular spaces, $W(k) = G(k)/\langle h\rangle$ =
`W K`, and $\langle a\rangle$ = `toG K (unary K a)` for $a \in k^{\times}$.

**Proves.**
* Lemma 5.6 (p. 26), `G_lift`: $G(k)$ is the abelian group with generators $\langle a\rangle$ ($a \in k^{\times}$) and
  relations (i) $\langle ab^{2}\rangle = \langle a\rangle$, (ii) $\langle a\rangle + \langle b\rangle =
  \langle a+b\rangle + \langle ab(a+b)\rangle$ ($a + b \ne 0$). "Given by the generators and relations" is stated by
  the universal property: every map $g\colon k^{\times} \to H$ to an abelian group satisfying (i) and (ii) extends
  uniquely to a homomorphism $G(k) \to H$. (That the $\langle a\rangle$ generate and satisfy (i), (ii) is
  `closure_unary`, `unary_mul_sq`, `unary_add_unary` in `Ch2/WittGroup.lean`.)
* Lemma 5.6, Corollary (pp. 26–27), `W_lift`: $W(k)$ is given by the same generators, relations (i), (ii) and
  (iii) $\langle 1\rangle + \langle -1\rangle = 0$.

**Proof notes.** Lemma 5.6 follows Cassels: a map on generators is extended to a regular space through a normal
basis; it does not depend on the normal basis, because by Witt's chain lemma (Lemma 3.1, here O'Meara's 58:1,
`OMeara.exists_adjacent_chain_of_orthogonal_bases`) two normal bases are joined by steps changing two vectors, and a
step changing two vectors is a case of (i) and (ii) (Cassels' cases $n = 1, 2$).
-/
import QuadFormsKB.Literature.Cassels.Ch2.WittGroup
import QuadFormsKB.Literature.Cassels.Ch2.WittChain

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels

variable {K : Type*} [Field K] [Invertible (2 : K)]

section Helpers

variable {H : Type*} [AddCommGroup H]

/-- Relation (i) for a function `G'` defined on all of `K`. -/
def Rel1 (G' : K → H) : Prop := ∀ x y : K, x ≠ 0 → y ≠ 0 → G' (x * y ^ 2) = G' x

/-- Relation (ii) for a function `G'` defined on all of `K`. -/
def Rel2 (G' : K → H) : Prop :=
  ∀ x y : K, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → G' x + G' y = G' (x + y) + G' (x * y * (x + y))

open Classical in
/-- Extension by zero of a function on units to all of `K`. -/
def extG (g : Kˣ → H) (x : K) : H := if h : x ≠ 0 then g (Units.mk0 x h) else 0

/-- `extG` agrees with `g` on units. -/
theorem extG_unit (g : Kˣ → H) (a : Kˣ) : extG g a = g a := by
  simp [extG]

/-- Relation (i) for `extG`. -/
theorem rel1_extG (g : Kˣ → H) (h₁ : ∀ a b : Kˣ, g (a * b ^ 2) = g a) : Rel1 (extG g) := by
  intro x y hx hy
  have e : ((Units.mk0 x hx * Units.mk0 y hy ^ 2 : Kˣ) : K) = x * y ^ 2 := by simp
  rw [← e, extG_unit, h₁]
  exact (extG_unit g (Units.mk0 x hx)).symm

/-- Relation (ii) for `extG`. -/
theorem rel2_extG (g : Kˣ → H)
    (h₂ : ∀ (a b : Kˣ) (hab : (a : K) + b ≠ 0),
      g a + g b = g (Units.mk0 _ hab) + g (a * b * Units.mk0 _ hab)) : Rel2 (extG g) := by
  intro x y hx hy hxy
  have hab : ((Units.mk0 x hx : Kˣ) : K) + (Units.mk0 y hy : Kˣ) ≠ 0 := hxy
  have := h₂ (Units.mk0 x hx) (Units.mk0 y hy) hab
  have e : ((Units.mk0 x hx * Units.mk0 y hy * Units.mk0 _ hab : Kˣ) : K) = x * y * (x + y) := by simp
  have ex : extG g x = g (Units.mk0 x hx) := extG_unit g (Units.mk0 x hx)
  have ey : extG g y = g (Units.mk0 y hy) := extG_unit g (Units.mk0 y hy)
  have es : extG g (x + y) = g (Units.mk0 _ hab) := extG_unit g (Units.mk0 _ hab)
  have ep : extG g (x * y * (x + y)) = g (Units.mk0 x hx * Units.mk0 y hy * Units.mk0 _ hab) := by
    rw [← e]; exact extG_unit _ _
  rw [ex, ey, es, ep]; exact this

/-- The binary algebra lemma behind the case of two changed vectors. -/
theorem binary_alg {G' : K → H} (h1 : Rel1 G') (h2 : Rel2 G') {a b α β γ δ : K} (ha : a ≠ 0)
    (hb : b ≠ 0) (hrel : α * γ * a + β * δ * b = 0) (hA : α ^ 2 * a + β ^ 2 * b ≠ 0)
    (hC : γ ^ 2 * a + δ ^ 2 * b ≠ 0) :
    G' a + G' b = G' (α ^ 2 * a + β ^ 2 * b) + G' (γ ^ 2 * a + δ ^ 2 * b) := by
  by_cases hβ : β = 0
  · subst hβ
    have hα : α ≠ 0 := by rintro rfl; simp at hA
    have hγ : γ = 0 := by
      have : α * γ * a = 0 := by simpa using hrel
      simpa [hα, ha] using this
    subst hγ
    have hδ : δ ≠ 0 := by rintro rfl; simp at hC
    have e1 : α ^ 2 * a + 0 ^ 2 * b = a * α ^ 2 := by ring
    have e2 : 0 ^ 2 * a + δ ^ 2 * b = b * δ ^ 2 := by ring
    rw [e1, e2, h1 a α ha hα, h1 b δ hb hδ]
  by_cases hα : α = 0
  · subst hα
    have hδ : δ = 0 := by
      have : β * δ * b = 0 := by simpa using hrel
      simpa [hβ, hb] using this
    subst hδ
    have hγ : γ ≠ 0 := by rintro rfl; simp at hC
    have e1 : 0 ^ 2 * a + β ^ 2 * b = b * β ^ 2 := by ring
    have e2 : γ ^ 2 * a + 0 ^ 2 * b = a * γ ^ 2 := by ring
    rw [e1, e2, h1 a γ ha hγ, h1 b β hb hβ, add_comm]
  have hδ : δ ≠ 0 := by
    rintro rfl
    have : α * γ * a = 0 := by simpa using hrel
    have hγ : γ = 0 := by simpa [hα, ha] using this
    subst hγ
    simp at hC
  have ha' : α ^ 2 * a ≠ 0 := mul_ne_zero (pow_ne_zero 2 hα) ha
  have hb' : β ^ 2 * b ≠ 0 := mul_ne_zero (pow_ne_zero 2 hβ) hb
  have key := h2 (α ^ 2 * a) (β ^ 2 * b) ha' hb' hA
  have hγ : γ = -(β * δ * b) / (α * a) := by
    field_simp
    linear_combination hrel
  have hCe : γ ^ 2 * a + δ ^ 2 * b =
      (α ^ 2 * a * (β ^ 2 * b) * (α ^ 2 * a + β ^ 2 * b)) * (δ / (α ^ 2 * β * a)) ^ 2 := by
    rw [hγ]; field_simp; ring
  have hne : α ^ 2 * a * (β ^ 2 * b) * (α ^ 2 * a + β ^ 2 * b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero ha' hb') hA
  have hte : δ / (α ^ 2 * β * a) ≠ 0 :=
    div_ne_zero hδ (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hα) hβ) ha)
  have e3 : G' (α ^ 2 * a) = G' a := by rw [mul_comm]; exact h1 a α ha hα
  have e4 : G' (β ^ 2 * b) = G' b := by rw [mul_comm]; exact h1 b β hb hβ
  rw [hCe, h1 _ _ hne hte, ← key, e3, e4]

section Basis

variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {n : ℕ}

/-- `polar Q v v = 2 * Q v`. -/
theorem polar_self_eq (Q : QuadraticForm K V) (v : V) : polar Q v v = 2 * Q v := by
  rw [polar_self]; simp [two_mul]

/-- Expanding the second argument of `polar` in a basis. -/
theorem polar_repr_right (x : Basis (Fin n) K V) (v w : V) :
    polar Q v w = ∑ j, x.repr w j * polar Q v (x j) := by
  conv_lhs => rw [← x.sum_repr w]
  have := map_sum (polarBilin Q v) (fun j => x.repr w j • x j) Finset.univ
  simpa [polarBilin_apply_apply] using this

/-- Expanding the first argument of `polar` in a basis. -/
theorem polar_repr_left (x : Basis (Fin n) K V) (v w : V) :
    polar Q v w = ∑ j, x.repr v j * polar Q (x j) w := by
  rw [polar_comm, polar_repr_right x]
  exact Finset.sum_congr rfl fun j _ => by rw [polar_comm]

/-- The vectors of a normal basis of a regular space have nonzero value. -/
theorem normal_Q_ne_zero (hreg : ∀ v, (∀ w, polar Q v w = 0) → v = 0) (x : Basis (Fin n) K V)
    (hx : ∀ i j, i ≠ j → polar Q (x i) (x j) = 0) (i : Fin n) : Q (x i) ≠ 0 := by
  intro h0
  apply x.ne_zero i
  apply hreg
  intro w
  rw [polar_repr_right x]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hij : i = j
  · subst hij; rw [polar_self_eq, h0]; simp
  · rw [hx i j hij, mul_zero]

/-- A vector orthogonal to `x j` has zero `j`-th coordinate in a normal basis `x`. -/
theorem repr_eq_zero_of_polar (x : Basis (Fin n) K V) (hx : ∀ i j, i ≠ j → polar Q (x i) (x j) = 0)
    (hne : ∀ j, Q (x j) ≠ 0) (v : V) (j : Fin n) (hv : polar Q v (x j) = 0) : x.repr v j = 0 := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero (2 : K)
  have := polar_repr_left (Q := Q) x v (x j)
  rw [hv, Finset.sum_eq_single j] at this
  · rw [polar_self_eq] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact h
    · exact absurd h (mul_ne_zero h2 (hne j))
  · intro i _ hij; rw [hx i j hij, mul_zero]
  · simp

/-- A vector orthogonal to all but one basis vector is a multiple of it. -/
theorem eq_single (x : Basis (Fin n) K V) (hx : ∀ i j, i ≠ j → polar Q (x i) (x j) = 0)
    (hne : ∀ j, Q (x j) ≠ 0) {i : Fin n} {v : V} (h : ∀ j, j ≠ i → polar Q v (x j) = 0) :
    v = x.repr v i • x i := by
  conv_lhs => rw [← x.sum_repr v]
  rw [Finset.sum_eq_single i]
  · intro j _ hj
    rw [repr_eq_zero_of_polar x hx hne v j (h j hj), zero_smul]
  · simp

/-- A vector orthogonal to all but two basis vectors lies in their span. -/
theorem eq_pair (x : Basis (Fin n) K V) (hx : ∀ i j, i ≠ j → polar Q (x i) (x j) = 0)
    (hne : ∀ j, Q (x j) ≠ 0) {i k : Fin n} (hik : i ≠ k) {v : V}
    (h : ∀ j, j ≠ i → j ≠ k → polar Q v (x j) = 0) :
    v = x.repr v i • x i + x.repr v k • x k := by
  conv_lhs => rw [← x.sum_repr v]
  rw [Finset.sum_eq_add_of_mem i k (Finset.mem_univ _) (Finset.mem_univ _) hik]
  intro j _ hj
  rw [repr_eq_zero_of_polar x hx hne v j (h j hj.1 hj.2), zero_smul]

/-- `polar` of two vectors in the span of an orthogonal pair. -/
theorem pair_polar (p q : V) (hpq : polar Q p q = 0) (α β γ δ : K) :
    polar Q (α • p + β • q) (γ • p + δ • q) = α * γ * (2 * Q p) + β * δ * (2 * Q q) := by
  have hqp : polar Q q p = 0 := by rw [polar_comm]; exact hpq
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, hpq, hqp,
    polar_self_eq, smul_eq_mul]
  ring

/-- Sums that agree away from two indices and on their total. -/
theorem sum_eq_of_pair (f g : Fin n → H) (i k : Fin n) (hik : i ≠ k)
    (h : ∀ j, j ≠ i → j ≠ k → f j = g j) (hs : f i + f k = g i + g k) : ∑ j, f j = ∑ j, g j := by
  have hk : k ∈ Finset.univ.erase i := by simp [Ne.symm hik]
  have hsum : ∑ j ∈ (Finset.univ.erase i).erase k, f j = ∑ j ∈ (Finset.univ.erase i).erase k, g j :=
    Finset.sum_congr rfl fun j hj => h j (by simp at hj; exact hj.2) (by simp at hj; exact hj.1)
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ i), ← Finset.add_sum_erase _ g (Finset.mem_univ i),
    ← Finset.add_sum_erase _ f hk, ← Finset.add_sum_erase _ g hk, hsum, ← add_assoc, ← add_assoc, hs]

/-- The step lemma: changing at most two vectors of a normal basis preserves `∑ G'(Q(b i))`. -/
theorem step_sum {G' : K → H} (h1 : Rel1 G') (h2 : Rel2 G')
    (hreg : ∀ v, (∀ w, polar Q v w = 0) → v = 0) {x y : Basis (Fin n) K V}
    (hx : ∀ i j, i ≠ j → polar Q (x i) (x j) = 0) (hy : ∀ i j, i ≠ j → polar Q (y i) (y j) = 0)
    (hxy : DifferInAtMostTwo x y) : ∑ i, G' (Q (x i)) = ∑ i, G' (Q (y i)) := by
  classical
  have h2' : (2 : K) ≠ 0 := Invertible.ne_zero (2 : K)
  have hxne := normal_Q_ne_zero hreg x hx
  have hyne := normal_Q_ne_zero hreg y hy
  obtain ⟨S, hS, hSk⟩ := hxy
  have hc : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases hc with hc | hc | hc
  · rw [Finset.card_eq_zero] at hc; subst hc
    exact Finset.sum_congr rfl fun j _ => by rw [hSk j (by simp)]
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
    have hyj : ∀ j, j ≠ i → y j = x j := fun j hj => hSk j (by simpa using hj)
    obtain ⟨c, hspan⟩ : ∃ c : K, y i = c • x i :=
      ⟨_, eq_single x hx hxne fun j hj => by rw [← hyj j hj]; exact hy i j (Ne.symm hj)⟩
    have hc0 : c ≠ 0 := by
      intro h0; apply y.ne_zero i; rw [hspan, h0, zero_smul]
    have hQ : Q (y i) = Q (x i) * c ^ 2 := by
      rw [hspan, QuadraticMap.map_smul, smul_eq_mul]; ring
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj; rw [hQ, h1 _ _ (hxne j) hc0]
    · rw [hyj j hj]
  · obtain ⟨i, k, hik, rfl⟩ := Finset.card_eq_two.mp hc
    have hyj : ∀ j, j ≠ i → j ≠ k → y j = x j := fun j h1 h2 => hSk j (by simp [h1, h2])
    obtain ⟨α, β, hyi⟩ : ∃ α β : K, y i = α • x i + β • x k :=
      ⟨_, _, eq_pair x hx hxne hik fun j hji hjk => by
        rw [← hyj j hji hjk]; exact hy i j (Ne.symm hji)⟩
    obtain ⟨γ, δ, hyk⟩ : ∃ γ δ : K, y k = γ • x i + δ • x k :=
      ⟨_, _, eq_pair x hx hxne hik fun j hji hjk => by
        rw [← hyj j hji hjk]; exact hy k j (Ne.symm hjk)⟩
    have hxik := hx i k hik
    have hQi : Q (y i) = α ^ 2 * Q (x i) + β ^ 2 * Q (x k) := by
      have e := pair_polar (Q := Q) (x i) (x k) hxik α β α β
      rw [← hyi, polar_self_eq] at e
      apply mul_left_cancel₀ h2'
      linear_combination e
    have hQk : Q (y k) = γ ^ 2 * Q (x i) + δ ^ 2 * Q (x k) := by
      have e := pair_polar (Q := Q) (x i) (x k) hxik γ δ γ δ
      rw [← hyk, polar_self_eq] at e
      apply mul_left_cancel₀ h2'
      linear_combination e
    have hrel : α * γ * Q (x i) + β * δ * Q (x k) = 0 := by
      have e := pair_polar (Q := Q) (x i) (x k) hxik α β γ δ
      rw [← hyi, ← hyk, hy i k hik] at e
      apply mul_left_cancel₀ h2'
      linear_combination -e
    have key := binary_alg h1 h2 (hxne i) (hxne k) hrel (by rw [← hQi]; exact hyne i)
      (by rw [← hQk]; exact hyne k)
    refine sum_eq_of_pair (fun j => G' (Q (x j))) (fun j => G' (Q (y j))) i k hik
      (fun j hji hjk => by simp only [hyj j hji hjk]) ?_
    simp only [hQi, hQk]
    exact key

/-- `∑ G'(Q(b i))` does not depend on the normal basis `b`. -/
theorem chain_sum {G' : K → H} (h1 : Rel1 G') (h2 : Rel2 G') [FiniteDimensional K V]
    (hreg : ∀ v, (∀ w, polar Q v w = 0) → v = 0) (x y : Basis (Fin n) K V)
    (hx : ∀ i j, i ≠ j → polar Q (x i) (x j) = 0) (hy : ∀ i j, i ≠ j → polar Q (y i) (y j) = 0) :
    ∑ i, G' (Q (x i)) = ∑ i, G' (Q (y i)) := by
  have hB : LinearMap.BilinForm.IsSymm (polarBilin Q) := ⟨fun u v => polar_comm Q u v⟩
  have hreg' : (polarBilin Q).Nondegenerate := (QSpace.reg_iff Q).mpr hreg
  have hch := exists_reflTransGen_normalBasis hB hreg' (Invertible.ne_zero (2 : K)) x y hx hy
  clear hy
  induction hch with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (step_sum h1 h2 hreg hs.1 hs.2.1 hs.2.2)

end Basis

/-- Diagonalizations of isometric regular diagonal spaces have the same `∑ G'(w i)`. -/
theorem diag_invariant {G' : K → H} (h1 : Rel1 G') (h2 : Rel2 G') {n m : ℕ} (w : Fin n → K)
    (w' : Fin m → K) (hw : ∀ i, w i ≠ 0) (hw' : ∀ i, w' i ≠ 0)
    (h : (diagSp K w hw).form.Equivalent (diagSp K w' hw').form) :
    ∑ i, G' (w i) = ∑ j, G' (w' j) := by
  have hnm : n = m := S.dim_eq_of_equivalent h
  subst hnm
  obtain ⟨e⟩ := h
  have hreg := (QSpace.reg_iff _).mp (diagSp K w hw).reg
  let Q : QuadraticForm K (Fin n → K) := weightedSumSquares K w
  let Q' : QuadraticForm K (Fin n → K) := weightedSumSquares K w'
  let L : (Fin n → K) ≃ₗ[K] (Fin n → K) := e.toLinearEquiv.symm
  have hQe : ∀ u, Q (L u) = Q' u := fun u => by
    have h3 : e (L u) = u := e.toLinearEquiv.apply_symm_apply u
    have := e.map_app (L u)
    rw [h3] at this
    exact this.symm
  have hp : ∀ u v, polar Q (L u) (L v) = polar Q' u v := by
    intro u v
    simp only [polar, ← map_add, hQe]
  have hQb : ∀ (v : Fin n → K) (i : Fin n), Q (Pi.single i 1) = w i := by
    intro v i
    simp [Q, weightedSumSquares_apply, Pi.single_apply]
  have hQb' : ∀ i : Fin n, Q' (Pi.single i 1) = w' i := by
    intro i
    simp [Q', weightedSumSquares_apply, Pi.single_apply]
  have hnorm : ∀ (u : Fin n → K) (i j : Fin n), i ≠ j → polar (weightedSumSquares K u)
      (Pi.single i 1) (Pi.single j 1) = 0 := by
    intro u i j hij
    rw [polar_wss_single]; simp [hij]
  have key := chain_sum (Q := Q) h1 h2 hreg (Pi.basisFun K (Fin n))
    ((Pi.basisFun K (Fin n)).map L) (fun i j hij => by simpa using hnorm w i j hij)
    (fun i j hij => by
      simp only [Basis.map_apply, hp, Pi.basisFun_apply]
      exact hnorm w' i j hij)
  simp only [Basis.map_apply, hQe, Pi.basisFun_apply] at key
  simpa [Q, Q', weightedSumSquares_apply, Pi.single_apply] using key

/-- The value `∑ G'(w i)` is determined by any diagonalization of `X`. -/
theorem exists_diagVal {G' : K → H} (h1 : Rel1 G') (h2 : Rel2 G') (X : QSpace K) :
    ∃ v : H, ∀ (n : ℕ) (w : Fin n → K) (hw : ∀ i, w i ≠ 0),
      X.form.Equivalent (diagSp K w hw).form → v = ∑ i, G' (w i) := by
  obtain ⟨n, w, hw, hX⟩ := exists_diag X
  refine ⟨∑ i, G' (w i), fun n' w' hw' h => ?_⟩
  exact diag_invariant h1 h2 w w' hw hw' ((S.mk_eq_mk.mp hX).symm.trans h)

/-- Orthogonal sums of diagonal spaces are diagonal. -/
theorem add_equiv_diag {X Y : QSpace K} {n m : ℕ} {w : Fin n → K} {w' : Fin m → K}
    {hw : ∀ i, w i ≠ 0} {hw' : ∀ i, w' i ≠ 0} (hX : X.form.Equivalent (diagSp K w hw).form)
    (hY : Y.form.Equivalent (diagSp K w' hw').form) :
    ∃ hww : ∀ i, Fin.append w w' i ≠ 0,
      (QSpace.add X Y).form.Equivalent (diagSp K (Fin.append w w') hww).form := by
  have hww : ∀ i, Fin.append w w' i ≠ 0 := by
    intro i
    induction i using Fin.addCases <;> simp [hw, hw']
  refine ⟨hww, ?_⟩
  refine (QSpace.add_equiv X Y).trans ((Equivalent.prod hX hY).trans
    ((QSpace.add_equiv (diagSp K w hw) (diagSp K w' hw')).symm.trans ?_))
  refine equiv_of_apply (V := Fin (n + m) → K) fun x => ?_
  show (QSpace.add (diagSp K w hw) (diagSp K w' hw')).form x = weightedSumSquares K (Fin.append w w') x
  rw [QSpace.add_form_apply]
  simp only [diagSp, weightedSumSquares_apply]
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- A relation-respecting function on `K` induces a homomorphism `S(k) → H` sending `⟨a⟩` to `G'(a)`. -/
theorem exists_S_hom {G' : K → H} (h1 : Rel1 G') (h2 : Rel2 G') :
    ∃ f : S K →+ H, ∀ a : Kˣ, f (unary K a) = G' a := by
  have hF := exists_diagVal h1 h2
  let F : QSpace K → H := fun X => (hF X).choose
  have hspec : ∀ (X : QSpace K) (n : ℕ) (w : Fin n → K) (hw : ∀ i, w i ≠ 0),
      X.form.Equivalent (diagSp K w hw).form → F X = ∑ i, G' (w i) :=
    fun X => (hF X).choose_spec
  have hFwd : ∀ X Y : QSpace K, X.form.Equivalent Y.form → F X = F Y := by
    intro X Y hXY
    obtain ⟨n, w, hw, hY⟩ := exists_diag Y
    have hY' := S.mk_eq_mk.mp hY
    rw [hspec X n w hw (hXY.trans hY'), hspec Y n w hw hY']
  have hF0 : F QSpace.zero = 0 := by
    have : QSpace.zero.form.Equivalent (diagSp K (fun i : Fin 0 => (0 : K)) (fun i => i.elim0)).form :=
      S.mk_eq_mk.mp (mk_diagSp_zero _ _).symm
    rw [hspec _ 0 _ (fun i => i.elim0) this]; simp
  have hFadd : ∀ X Y : QSpace K, F (QSpace.add X Y) = F X + F Y := by
    intro X Y
    obtain ⟨n, w, hw, hX⟩ := exists_diag X
    obtain ⟨m, w', hw', hY⟩ := exists_diag Y
    obtain ⟨hww, hadd⟩ := add_equiv_diag (S.mk_eq_mk.mp hX) (S.mk_eq_mk.mp hY)
    rw [hspec _ _ _ hww hadd, hspec X n w hw (S.mk_eq_mk.mp hX), hspec Y m w' hw' (S.mk_eq_mk.mp hY),
      Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  let f₀ : S K → H := Quotient.lift F fun _ _ h => hFwd _ _ h
  refine ⟨{ toFun := f₀, map_zero' := hF0, map_add' := fun a b => ?_ }, fun a => ?_⟩
  · induction a using S.ind; induction b using S.ind
    exact hFadd _ _
  · show F _ = _
    rw [hspec _ 1 (fun _ : Fin 1 => (a : K)) (fun _ => a.ne_zero) (Equivalent.refl _)]
    simp

end Helpers

/-- **Cassels, Ch. 2, Lemma 5.6.** ($\operatorname{char} k \ne 2$.) $G(k)$ is the abelian group given by the
generators $\langle a\rangle$, $a \in k^{\times}$, and the relations
(i) $\langle ab^{2}\rangle = \langle a\rangle$ for $a, b \in k^{\times}$ and
(ii) $\langle a\rangle + \langle b\rangle = \langle a+b\rangle + \langle ab(a+b)\rangle$ for $a, b \in k^{\times}$
with $a + b \ne 0$:
for every abelian group $H$ and every map $g \colon k^{\times} \to H$ with
$g(ab^{2}) = g(a)$ and $g(a) + g(b) = g(a+b) + g(ab(a+b))$ (when $a + b \ne 0$) there is a unique homomorphism
$\varphi \colon G(k) \to H$ with $\varphi\langle a\rangle = g(a)$ for all $a$. -/
@[kb "cassels1978" "Ch. 2, Lemma 5.6, p. 26"]
theorem G_lift {H : Type*} [AddCommGroup H] (g : Kˣ → H)
    (h₁ : ∀ a b : Kˣ, g (a * b ^ 2) = g a)
    (h₂ : ∀ (a b : Kˣ) (hab : (a : K) + b ≠ 0),
      g a + g b = g (Units.mk0 _ hab) + g (a * b * Units.mk0 _ hab)) :
    ∃! φ : G K →+ H, ∀ a : Kˣ, φ (toG K (unary K a)) = g a := by
  obtain ⟨f, hf⟩ := exists_S_hom (rel1_extG g h₁) (rel2_extG g h₂)
  have hf' : ∀ a : Kˣ, f (unary K a) = g a := fun a => by rw [hf, extG_unit]
  refine ⟨Algebra.GrothendieckAddGroup.lift f, fun a => by rw [lift_of, hf'], ?_⟩
  intro ψ hψ
  have hcomp : ψ.comp (toG K) = f := by
    have hmem : ∀ s : S K, s ∈ AddSubmonoid.closure (Set.range (unary K)) := by
      intro s; rw [closure_unary]; trivial
    ext s
    refine AddSubmonoid.closure_induction (fun x hx => ?_) ?_ (fun x y _ _ hx hy => ?_) (hmem s)
    · obtain ⟨a, rfl⟩ := hx
      simp only [AddMonoidHom.comp_apply]
      rw [hψ, hf']
    · simp
    · simp only [AddMonoidHom.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]
  obtain ⟨g0, -, huniq⟩ := (grothendieck_universal (M := S K)).2 H f
  have hl : (Algebra.GrothendieckAddGroup.lift f).comp (toG K) = f := by
    ext x; exact lift_of f x
  exact (huniq ψ hcomp).trans (huniq _ hl).symm

/-- **Cassels, Ch. 2, Lemma 5.6, Corollary.** ($\operatorname{char} k \ne 2$.) $W(k)$ is the abelian group given by
the generators $\langle a\rangle$, $a \in k^{\times}$, and the relations (i), (ii) of Lemma 5.6 and
(iii) $\langle 1\rangle + \langle -1\rangle = 0$: every map $g \colon k^{\times} \to H$ to an abelian group satisfying
(i), (ii) and $g(1) + g(-1) = 0$ induces a unique homomorphism $\varphi \colon W(k) \to H$ with
$\varphi\langle a\rangle = g(a)$. -/
@[kb "cassels1978" "Ch. 2, Lemma 5.6, Cor., pp. 26–27"]
theorem W_lift {H : Type*} [AddCommGroup H] (g : Kˣ → H)
    (h₁ : ∀ a b : Kˣ, g (a * b ^ 2) = g a)
    (h₂ : ∀ (a b : Kˣ) (hab : (a : K) + b ≠ 0),
      g a + g b = g (Units.mk0 _ hab) + g (a * b * Units.mk0 _ hab))
    (h₃ : g 1 + g (-1) = 0) :
    ∃! φ : W K →+ H, ∀ a : Kˣ, φ (toW K (toG K (unary K a))) = g a := by
  obtain ⟨φ, hφ, huniq⟩ := G_lift g h₁ h₂
  have hker : φ (toG K (hyp K)) = 0 := by
    rw [← unary_add_star 1, star_unary, map_add, map_add, hφ, hφ]
    exact h₃
  let ψ : W K →+ H := QuotientAddGroup.lift _ φ (by
    intro x hx
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    rw [AddMonoidHom.mem_ker, map_zsmul, hker, smul_zero])
  refine ⟨ψ, fun a => ?_, ?_⟩
  · exact (QuotientAddGroup.lift_mk _ _ _).trans (hφ a)
  · intro ψ' hψ'
    have : ψ'.comp (toW K) = φ := huniq _ fun a => hψ' a
    ext x
    exact DFunLike.congr_fun this x

end QuadFormsKB.Cassels
