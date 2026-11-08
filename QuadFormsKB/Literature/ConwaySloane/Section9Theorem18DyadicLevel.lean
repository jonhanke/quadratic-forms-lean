/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$ for the level shapes

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18, the "only if" direction at $p = 2$.

**Layer.** As in `Section9Theorem18DyadicTwoSided.lean`: over $\mathbb Q$ at the prime $v$ over $2$, a basis
$b_k = \gamma e_k$ of $L_2$ with Gram matrix $G$ = `locGram Q v γ` of $B$ ($G_{kk} = 2Q(b_k)$) and $N = G^{-1}$
($GN = 1$, the Gram matrix of the dual basis). "$x \in 2^a$" means $\lvert x\rvert \le e^{-a}$ ($\lvert 2\rvert = e^{-1}$).
Indices are $0$-based.

**The shape.** `LevelShape v G N p λ S` (a **condition**): integers $p$, $\lambda_i$ and a set $S$ of indices (the
*single* indices, $1$-dimensional Jordan constituents; the others are the *paired* indices, constituents of even
type); the *scale exponent* of $i$ is $e_i = 2\lambda_i + p$ ($i \notin S$) or $2\lambda_i + p + 1$ ($i \in S$)
(`levE`). The conditions: $G_{ij} \in 2^{\max(e_i, e_j)}$, $N_{ij} \in 2^{-\min(e_i, e_j)}$, $G_{ii} \in 2^{e_i + 1}$
for paired $i$, the single basis vectors are orthogonal to all others, and at each level $\lambda$ there are at most
two single indices $k, l$, and then $G_{kk} + G_{ll} \in 2^{e_k + 2}$ ($u_k + u_l \equiv 0 \pmod 4$ for
$G_{kk} = 2^{e_k}u_k$). In a Jordan basis this says: the even constituents lie at scales $2^{e}$ with $e \equiv p$, the odd
ones at the other parity, and the odd constituent at each scale has rank at most $2$, with
$u_k + u_l \equiv 0 \pmod 4$ in rank $2$. These are exactly the Jordan forms with at least one even constituent whose
root group is not everything (checked by computer), the family left open by the earlier steps
(`Theorem18DyadicResidual11`).

**The idea** (a canonical overlattice and the Wall core lemma without unimodularity). Let $M$ be the lattice with basis
$b'_i = 2^{-\lambda_i}b_i$ and the form scaled by $c = 2^{-p}$: its Gram matrix $A = cG'$ is integral and even, the
paired indices span an even unimodular sublattice and the single ones $\langle 2u_k\rangle$. ($M = \sum_a 2^{-a}L_2(2a)$ with
$L_2(k) = \{x \in L_2 : B(x, L_2) \subseteq 2^k\}$, so it is canonical, but only the matrix facts below are used.)
For $\sigma \in O(L_2)$ with matrix $S'$ in the basis $b$:
* the columns of $S'$ satisfy $S'_{ij} \in 2^{\max(0, e_j - e_i)}$ (`ord_conj_entry`: $S' = N\,T'^{\mathsf T}G$ with
  $T' = S'^{-1}$ integral), so the matrix $S'' = \Lambda^{-1}S'\Lambda$ of $\sigma$ in the basis $b'$ is integral;
* for a single index $k$, $S''_{ik} \equiv \delta_{ik} \pmod 2$ (`level_key`): for $i$ at another level or paired, from
  the column bound; for the single indices at the level of $k$, from $Q(\sigma b_k) = Q(b_k)$ modulo $2^{e_k + 2}$:
  $\sum_i x_i^2u_i \equiv u_k \pmod 4$ over the singles $i$ of that level ($x = S'e_k$), and with
  $u_k + u_l \equiv 0 \pmod 4$ only $x_k$ odd, $x_l$ even is possible.
Hence $(1 - S'')A^{-1}$ is integral ($A^{-1}$ is integral except for the entries $1/(2u_k)$): $\sigma$ acts trivially on
the discriminant group $M^\#/M$, and the Wall core lemma `exists_sq_valued_wallDet_of_dual` shows that every proper
$\sigma \in O(L_2)$ has a spinor norm of even order.

**Defines** `levE`, `LevelShape` (a **condition**).

**Proves**
* the valuation helpers `ord_mul`, `ord_mono`, `ord_add`, `ord_sub`, `ord_sum`, `ord_two_zpow`, `ord_cancel`,
  `ord_one_of_ne`, `ord_unit_sq_sub_one`, `ord_one_sub_unit`;
* `ord_conj_entry` (the column bound), `valued_single_diag`, `level_rem`, `level_key` (the congruence for single
  columns), `locGram_mul_diagGL`, `inv_symm_of_mul_eq_one`;
* `evenSpinor_of_conj_dual` (even spinor norm through a preserved lattice whose discriminant group is acted on
  trivially);
* **`evenSpinor_of_levelShape`**: every proper $\sigma \in O(L_2)$ has a spinor norm of even order;
* **`theorem18OnlyIf_of_levelShape`** (Theorem 18, "only if", at $p = 2$ for the level shapes with at least one paired
  index; unconditional).
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicWallDual
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicRelChain
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicTwoSided

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices Wall Levels EvenUnimodular

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

section Ord

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

theorem ord_mul {x y : Fv} {a b : ℤ} (hx : Valued.v x ≤ exp (-a)) (hy : Valued.v y ≤ exp (-b)) :
    Valued.v (x * y) ≤ exp (-(a + b)) := by
  rw [map_mul, neg_add, exp_add]; exact mul_le_mul' hx hy

theorem ord_mono {x : Fv} {a b : ℤ} (hx : Valued.v x ≤ exp (-a)) (hab : b ≤ a) : Valued.v x ≤ exp (-b) :=
  hx.trans (exp_le_exp.mpr (by omega))

theorem ord_add {x y : Fv} {a : ℤ} (hx : Valued.v x ≤ exp (-a)) (hy : Valued.v y ≤ exp (-a)) :
    Valued.v (x + y) ≤ exp (-a) := (Valuation.map_add _ _ _).trans (max_le hx hy)

theorem ord_sub {x y : Fv} {a : ℤ} (hx : Valued.v x ≤ exp (-a)) (hy : Valued.v y ≤ exp (-a)) :
    Valued.v (x - y) ≤ exp (-a) := (Valuation.map_sub _ _ _).trans (max_le hx hy)

theorem ord_sum {ι : Type*} (s : Finset ι) (f : ι → Fv) {a : ℤ} (h : ∀ i ∈ s, Valued.v (f i) ≤ exp (-a)) :
    Valued.v (∑ i ∈ s, f i) ≤ exp (-a) := Valuation.map_sum_le _ h

theorem ord_two_zpow (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (k : ℤ) : Valued.v ((2 : Fv) ^ k) ≤ exp (-k) :=
  (valued_two_zpow h2 k).le

theorem ord_zero_iff {x : Fv} : Valued.v x ≤ exp (-0) ↔ Valued.v x ≤ 1 := by
  rw [neg_zero, exp_zero]

/-- Cancelling a factor of exact order: $\lvert a\rvert = e^{-e}$ and $ab \in 2^{e + c}$ give $b \in 2^c$. -/
theorem ord_cancel {a b : Fv} {e c : ℤ} (ha : Valued.v a = exp (-e)) (h : Valued.v (a * b) ≤ exp (-(e + c))) :
    Valued.v b ≤ exp (-c) := by
  rw [map_mul, ha, neg_add, exp_add] at h
  have h' := mul_le_mul' (le_refl (exp e)) h
  rwa [← mul_assoc, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul, one_mul] at h'

/-- An integral non-unit lies in $2$. -/
theorem ord_one_of_ne (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {x : Fv} (hx : Valued.v x ≤ 1) (hne : Valued.v x ≠ 1) :
    Valued.v x ≤ exp (-1) := by
  have := valued_le_two_of_lt_one h2 (lt_of_le_of_ne hx hne)
  rwa [valued_two_dyadic v h2] at this

/-- $x^2 \equiv 1 \pmod 4$ for a unit $x$. -/
theorem ord_unit_sq_sub_one (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {x : Fv} (hx : Valued.v x = 1) :
    Valued.v (x * x - 1) ≤ exp (-2) := by
  have h1 : Valued.v (1 + x) ≤ exp (-1) := by
    have := valued_one_add_unit_le h2 hx; rwa [valued_two_dyadic v h2] at this
  have h2' : Valued.v (1 + -x) ≤ exp (-1) := by
    have := valued_one_add_unit_le h2 (u := -x) (by rw [Valuation.map_neg]; exact hx)
    rwa [valued_two_dyadic v h2] at this
  have e : x * x - 1 = -((1 + -x) * (1 + x)) := by ring
  rw [e, Valuation.map_neg]
  have := ord_mul h2' h1
  norm_num at this ⊢
  exact this

/-- $1 - x \in 2$ for a unit $x$. -/
theorem ord_one_sub_unit (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {x : Fv} (hx : Valued.v x = 1) :
    Valued.v (1 - x) ≤ exp (-1) := by
  have := valued_one_add_unit_le h2 (u := -x) (by rw [Valuation.map_neg]; exact hx)
  rwa [valued_two_dyadic v h2, ← sub_eq_add_neg] at this

theorem valued_two_eq (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : Valued.v (2 : Fv) = exp (-1) := valued_two_dyadic v h2

end Ord

section Level

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- **The scale exponent** $e_i = 2\lambda_i + p$ for $i \notin S$ and $2\lambda_i + p + 1$ for $i \in S$. -/
def levE (p : ℤ) (lam : Fin n → ℤ) (Sg : Finset (Fin n)) (i : Fin n) : ℤ :=
  2 * lam i + p + if i ∈ Sg then 1 else 0

theorem levE_of_mem {p : ℤ} {lam : Fin n → ℤ} {Sg : Finset (Fin n)} {i : Fin n} (h : i ∈ Sg) :
    levE p lam Sg i = 2 * lam i + p + 1 := by simp [levE, h]

theorem levE_of_not_mem {p : ℤ} {lam : Fin n → ℤ} {Sg : Finset (Fin n)} {i : Fin n} (h : i ∉ Sg) :
    levE p lam Sg i = 2 * lam i + p := by simp [levE, h]

theorem levE_bounds (p : ℤ) (lam : Fin n → ℤ) (Sg : Finset (Fin n)) (i : Fin n) :
    2 * lam i + p ≤ levE p lam Sg i ∧ levE p lam Sg i ≤ 2 * lam i + p + 1 := by
  unfold levE; split_ifs <;> omega

variable (v) in
/-- **The level shape** (a **condition** on a Gram matrix $G$, its inverse $N$, integers $p$, $\lambda_i$ and the set
$S$ of single indices; see the module docstring): with $e_i$ = `levE p lam Sg i`,
* `gram`: $G_{ij} \in 2^{\max(e_i, e_j)}$;
* `dual`: $N_{ij} \in 2^{-\min(e_i, e_j)}$;
* `even`: $G_{ii} \in 2^{e_i + 1}$ for $i \notin S$;
* `orth`: $G_{mk} = 0$ for $k \in S$, $m \ne k$;
* `pair`: two distinct single indices $k, l$ at the same level $\lambda_l = \lambda_k$ are the only ones at that level,
  and $G_{kk} + G_{ll} \in 2^{e_k + 2}$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: the level shapes, even constituents at one scale parity, odd ones of rank ≤ 2 at the other)"]
structure LevelShape (G N : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ)) (p : ℤ) (lam : Fin n → ℤ)
    (Sg : Finset (Fin n)) : Prop where
  gram : ∀ i j, Valued.v (G i j) ≤ exp (-(max (levE p lam Sg i) (levE p lam Sg j)))
  dual : ∀ i j, Valued.v (N i j) ≤ exp (-(-min (levE p lam Sg i) (levE p lam Sg j)))
  even : ∀ i, i ∉ Sg → Valued.v (G i i) ≤ exp (-(levE p lam Sg i + 1))
  orth : ∀ k ∈ Sg, ∀ m, m ≠ k → G m k = 0
  pair : ∀ k ∈ Sg, ∀ l ∈ Sg, l ≠ k → lam l = lam k →
    (∀ l' ∈ Sg, l' ≠ k → lam l' = lam k → l' = l) ∧
      Valued.v (G k k + G l l) ≤ exp (-(levE p lam Sg k + 2))

/-- **The column bound**: if $T'^{\mathsf T}G = GS'$ with $T'$ integral and $NG = 1$, then
$S'_{ij} \in 2^{e_j - e_i}$. -/
theorem ord_conj_entry {G N S' T' : Matrix (Fin n) (Fin n) Fv} {p : ℤ} {lam : Fin n → ℤ} {Sg : Finset (Fin n)}
    (hs : LevelShape v G N p lam Sg) (hNG : N * G = 1) (hT : ∀ i j, Valued.v (T' i j) ≤ 1)
    (hTG : T'ᵀ * G = G * S') (i j : Fin n) :
    Valued.v (S' i j) ≤ exp (-(levE p lam Sg j - levE p lam Sg i)) := by
  have e : S' = N * (T'ᵀ * G) := by rw [hTG, ← Matrix.mul_assoc, hNG, Matrix.one_mul]
  rw [e, Matrix.mul_apply]
  refine ord_sum _ _ fun l _ => ?_
  have hin : Valued.v ((T'ᵀ * G) l j) ≤ exp (-(levE p lam Sg j)) := by
    rw [Matrix.mul_apply]
    refine ord_sum _ _ fun m _ => ?_
    have h1 : Valued.v (T'ᵀ l m) ≤ exp (-0) := by rw [ord_zero_iff, transpose_apply]; exact hT m l
    have := ord_mul h1 (ord_mono (hs.gram m j) (le_max_right _ _))
    simpa using this
  exact ord_mono (ord_mul (hs.dual i l) hin) (by have := min_le_left (levE p lam Sg i) (levE p lam Sg l); omega)

/-- The diagonal entry of a single index has exact order $e_k$. -/
theorem valued_single_diag {G N : Matrix (Fin n) (Fin n) Fv} {p : ℤ} {lam : Fin n → ℤ} {Sg : Finset (Fin n)}
    (hs : LevelShape v G N p lam Sg) (hG : Gᵀ = G) (hGN : G * N = 1) {l : Fin n} (hl : l ∈ Sg) :
    Valued.v (G l l) = exp (-(levE p lam Sg l)) := by
  have hsym : ∀ i j, G j i = G i j := fun i j => by
    have := congrFun (congrFun hG i) j; simpa [transpose_apply] using this
  have hrow : G l l * N l l = 1 := by
    have := congrFun (congrFun hGN l) l
    rw [Matrix.mul_apply, Finset.sum_eq_single l
      (fun m _ hm => by rw [hsym, hs.orth l hl m hm, zero_mul]) (by simp)] at this
    simpa using this
  have hG1 := hs.gram l l
  have hN1 := hs.dual l l
  simp only [max_self, min_self, neg_neg] at hG1 hN1
  have hprod : Valued.v (G l l) * Valued.v (N l l) = 1 := by rw [← map_mul, hrow, map_one]
  refine le_antisymm hG1 ?_
  have h1 : (1 : ℤᵐ⁰) ≤ Valued.v (G l l) * exp (levE p lam Sg l) := hprod ▸ mul_le_mul' le_rfl hN1
  calc exp (-(levE p lam Sg l)) = exp (-(levE p lam Sg l)) * 1 := (mul_one _).symm
    _ ≤ exp (-(levE p lam Sg l)) * (Valued.v (G l l) * exp (levE p lam Sg l)) := mul_le_mul' le_rfl h1
    _ = Valued.v (G l l) := by
        rw [mul_comm (Valued.v (G l l)), ← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]

/-- **The remainder bound** in `level_key`: with $I$ the single indices at the level of $k$ and $y$ the vector $x$
with the entries in $I$ set to $0$, $y^{\mathsf T}Gy \in 2^{e_k + 2}$. -/
theorem level_rem (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {G N : Matrix (Fin n) (Fin n) Fv} {p : ℤ} {lam : Fin n → ℤ}
    {Sg : Finset (Fin n)} (hs : LevelShape v G N p lam Sg) (hG : Gᵀ = G) {k : Fin n} (hk : k ∈ Sg)
    (x : Fin n → Fv) (hx : ∀ i, Valued.v (x i) ≤ exp (-(max 0 (levE p lam Sg k - levE p lam Sg i)))) :
    Valued.v ((fun i => if i ∈ Sg ∧ lam i = lam k then 0 else x i) ⬝ᵥ
      (G *ᵥ fun i => if i ∈ Sg ∧ lam i = lam k then 0 else x i)) ≤ exp (-(levE p lam Sg k + 2)) := by
  classical
  have hsym : ∀ i j, G j i = G i j := fun i j => by
    have := congrFun (congrFun hG i) j; simpa [transpose_apply] using this
  have hrow : ∀ i ∈ Sg, ∀ j, j ≠ i → G i j = 0 := fun i hi j hj => by rw [← hsym]; exact hs.orth i hi j hj
  set e := levE p lam Sg with he
  have hgram : ∀ i j, Valued.v (G i j) ≤ exp (-(max (e i) (e j))) := hs.gram
  have hdual : ∀ i j, Valued.v (N i j) ≤ exp (-(-min (e i) (e j))) := hs.dual
  have heven2 : ∀ i, i ∉ Sg → Valued.v (G i i) ≤ exp (-(e i + 1)) := hs.even
  set I : Fin n → Prop := fun i => i ∈ Sg ∧ lam i = lam k with hI
  set f : Fin n → ℤ := fun i => max 0 (e k - e i) with hf
  set y : Fin n → Fv := fun i => if I i then 0 else x i with hy
  have hentry : ∀ i j, ¬ I i → ¬ I j →
      Valued.v (G i j) ≤ exp (-(e k + 1 - f i - f j + if i = j then 1 else 0)) := by
    intro i j hi hj
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      by_cases hiS : i ∈ Sg
      · have hli : lam i ≠ lam k := fun h => hi ⟨hiS, h⟩
        refine ord_mono (ord_mono (hgram i i) (le_of_eq (max_self _).symm)) ?_
        simp only [hf, he, levE_of_mem hiS, levE_of_mem hk]
        omega
      · refine ord_mono (heven2 i hiS) ?_
        simp only [hf, he, levE_of_not_mem hiS, levE_of_mem hk]
        omega
    · simp only [hij, if_false, add_zero]
      by_cases hiS : i ∈ Sg
      · rw [hrow i hiS j (Ne.symm hij)]; simp
      by_cases hjS : j ∈ Sg
      · rw [hs.orth j hjS i hij]; simp
      refine ord_mono (hgram i j) ?_
      simp only [hf, he, levE_of_not_mem hiS, levE_of_not_mem hjS, levE_of_mem hk]
      omega
  set c : Fv := (2 : Fv) ^ (-(e k + 1)) with hc
  set A : Matrix (Fin n) (Fin n) Fv := Matrix.of fun i j =>
    if I i ∨ I j then 0 else c * ((2 : Fv) ^ (f i) * G i j * (2 : Fv) ^ (f j)) with hA
  set z : Fin n → Fv := fun i => (2 : Fv) ^ (-(f i)) * y i with hz
  have hinv : ∀ t : ℤ, (2 : Fv) ^ (-t) * (2 : Fv) ^ t = 1 := fun t => by
    rw [_root_.zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ two_ne_zero)]
  have hAsym : Aᵀ = A := by
    ext i j
    simp only [hA, transpose_apply, of_apply, or_comm, hsym i j]
    split_ifs <;> ring
  have hAord : ∀ i j, Valued.v (A i j) ≤ exp (-(if i = j then 1 else 0)) := by
    intro i j
    by_cases h : I i ∨ I j
    · simp only [hA, of_apply, if_pos h, map_zero]; exact zero_le'
    · simp only [hA, of_apply, if_neg h]
      push_neg at h
      have := ord_mul (ord_two_zpow h2 (-(e k + 1)))
        (ord_mul (ord_mul (ord_two_zpow h2 (f i)) (hentry i j h.1 h.2)) (ord_two_zpow h2 (f j)))
      refine ord_mono this ?_
      split_ifs <;> omega
  have hAint : ∀ i j, Valued.v (A i j) ≤ 1 := fun i j => by
    have := hAord i j; rw [← ord_zero_iff]; refine ord_mono this ?_; split_ifs <;> omega
  have hAeven : ∀ i, Valued.v (A i i / 2) ≤ 1 := fun i => by
    have h1 := hAord i i
    simp only [if_true] at h1
    rw [div_eq_mul_inv, ← ord_zero_iff, ← _root_.zpow_neg_one]
    exact ord_mono (ord_mul h1 (ord_two_zpow h2 (-1))) (by omega)
  have hzint : ∀ i, Valued.v (z i) ≤ 1 := by
    intro i
    simp only [hz, hy]
    split_ifs with h
    · simp
    · rw [← ord_zero_iff]
      exact ord_mono (ord_mul (ord_two_zpow h2 (-(f i))) (hx i)) (by simp only [hf, he]; omega)
  have hzAz : z ⬝ᵥ (A *ᵥ z) = c * (y ⬝ᵥ (G *ᵥ y)) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hz, hA, of_apply]
    by_cases hi : I i
    · simp [hy, hi]
    by_cases hj : I j
    · simp [hy, hj]
    simp only [hi, hj, or_self, if_false]
    calc (2 : Fv) ^ (-f i) * y i * (c * ((2 : Fv) ^ f i * G i j * (2 : Fv) ^ f j) * ((2 : Fv) ^ (-f j) * y j))
        = ((2 : Fv) ^ (-f i) * (2 : Fv) ^ f i) * ((2 : Fv) ^ (-f j) * (2 : Fv) ^ f j) *
            (c * (y i * (G i j * y j))) := by ring
      _ = c * (y i * (G i j * y j)) := by rw [hinv, hinv, one_mul, one_mul]
  have h := valued_half_quad_le_one' A hAsym hAint hAeven z hzint
  rw [hzAz] at h
  have e2 : c * (y ⬝ᵥ (G *ᵥ y)) / 2 = (2 : Fv) ^ (-(e k + 2)) * (y ⬝ᵥ (G *ᵥ y)) := by
    rw [hc, div_eq_mul_inv, ← _root_.zpow_neg_one, mul_comm _ ((2 : Fv) ^ (-1 : ℤ)), ← mul_assoc,
      ← zpow_add₀ two_ne_zero]
    ring_nf
  rw [e2] at h
  refine ord_cancel (e := -(e k + 2)) (valued_two_zpow h2 _) ?_
  rw [← ord_zero_iff] at h
  exact ord_mono h (by omega)

/-- **The congruence for a single column** (see the module docstring): let $k \in S$ and $x$ a vector with
$x_i \in 2^{\max(0, e_k - e_i)}$ and $x^{\mathsf T}Gx = G_{kk}$ (the column $S'e_k$ of an integral isometry). Then
$1 - x_k \in 2$ and $x_l \in 2$ for every other single index $l$ at the level of $k$. -/
theorem level_key (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {G N : Matrix (Fin n) (Fin n) Fv} {p : ℤ} {lam : Fin n → ℤ}
    {Sg : Finset (Fin n)} (hs : LevelShape v G N p lam Sg) (hG : Gᵀ = G) (hGN : G * N = 1) {k : Fin n}
    (hk : k ∈ Sg) (x : Fin n → Fv)
    (hx : ∀ i, Valued.v (x i) ≤ exp (-(max 0 (levE p lam Sg k - levE p lam Sg i))))
    (hxx : x ⬝ᵥ (G *ᵥ x) = G k k) :
    Valued.v (1 - x k) ≤ exp (-1) ∧ ∀ l ∈ Sg, l ≠ k → lam l = lam k → Valued.v (x l) ≤ exp (-1) := by
  classical
  have hsym : ∀ i j, G j i = G i j := fun i j => by
    have := congrFun (congrFun hG i) j; simpa [transpose_apply] using this
  have hrow : ∀ i ∈ Sg, ∀ j, j ≠ i → G i j = 0 := fun i hi j hj => by rw [← hsym]; exact hs.orth i hi j hj
  set e := levE p lam Sg with he
  have hgram : ∀ i j, Valued.v (G i j) ≤ exp (-(max (e i) (e j))) := hs.gram
  have hdual : ∀ i j, Valued.v (N i j) ≤ exp (-(-min (e i) (e j))) := hs.dual
  have heven2 : ∀ i, i ∉ Sg → Valued.v (G i i) ≤ exp (-(e i + 1)) := hs.even
  set I : Fin n → Prop := fun i => i ∈ Sg ∧ lam i = lam k with hI
  set y : Fin n → Fv := fun i => if I i then 0 else x i with hy
  have hsplit : x ⬝ᵥ (G *ᵥ x) = (∑ i, if I i then x i * G i i * x i else 0) + y ⬝ᵥ (G *ᵥ y) := by
    simp only [dotProduct, mulVec]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : I i
    · have : ∑ j, G i j * x j = G i i * x i :=
        Finset.sum_eq_single i (fun j _ hj => by rw [hrow i hi.1 j hj, zero_mul]) (by simp)
      simp only [hy, hi, if_true, zero_mul, add_zero, this]
      ring
    · have : ∑ j, G i j * x j = ∑ j, G i j * y j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : I j
        · have hji : i ≠ j := fun h => hi (h ▸ hj)
          rw [hs.orth j hj.1 i hji]; simp
        · simp [hy, hj]
      simp only [hy, hi, if_false, zero_add, this]
  have hrem : Valued.v (y ⬝ᵥ (G *ᵥ y)) ≤ exp (-(e k + 2)) := level_rem h2 hs hG hk x hx
  have hgk := valued_single_diag hs hG hGN hk
  have hxk : Valued.v (x k) ≤ 1 := by
    have := hx k; rw [sub_self, max_self, ord_zero_iff] at this; exact this
  have hmain : Valued.v ((∑ i, if I i then x i * G i i * x i else 0) - G k k) ≤ exp (-(e k + 2)) := by
    have e1 : (∑ i, if I i then x i * G i i * x i else 0) - G k k = -(y ⬝ᵥ (G *ᵥ y)) := by
      rw [← hxx, hsplit]; ring
    rw [e1, Valuation.map_neg]; exact hrem
  have hne1 : ¬ (1 : ℤᵐ⁰) ≤ exp (-2) := by
    rw [← exp_zero, exp_le_exp]; omega
  have hone : Valued.v (x k * G k k * x k - G k k) ≤ exp (-(e k + 2)) → Valued.v (1 - x k) ≤ exp (-1) := by
    intro h
    have e1 : x k * G k k * x k - G k k = G k k * (x k * x k - 1) := by ring
    rw [e1] at h
    have h' := ord_cancel hgk h
    by_cases hu : Valued.v (x k) = 1
    · exact ord_one_sub_unit h2 hu
    · exfalso
      have hx1 := ord_one_of_ne h2 hxk hu
      have hsq := ord_mul hx1 hx1
      have e3 : (1 : Fv) = x k * x k - (x k * x k - 1) := by ring
      have := ord_sub (ord_mono hsq (by norm_num)) h'
      rw [← e3, map_one] at this
      exact hne1 this
  by_cases hpair : ∃ l ∈ Sg, l ≠ k ∧ lam l = lam k
  · obtain ⟨l, hl, hlk, hll⟩ := hpair
    obtain ⟨huniq, hsum⟩ := hs.pair k hk l hl hlk hll
    have hIiff : ∀ i, I i ↔ i = k ∨ i = l := by
      intro i
      constructor
      · rintro ⟨hiS, hil⟩
        by_cases hik : i = k
        · exact Or.inl hik
        · exact Or.inr (huniq i hiS hik hil)
      · rintro (rfl | rfl)
        exacts [⟨hk, rfl⟩, ⟨hl, hll⟩]
    have hsumI : (∑ i, if I i then x i * G i i * x i else 0) = x k * G k k * x k + x l * G l l * x l := by
      rw [← Finset.sum_filter]
      have : Finset.univ.filter I = {k, l} := by
        ext i; simp [hIiff]
      rw [this, Finset.sum_pair (Ne.symm hlk)]
    rw [hsumI] at hmain
    have hel : e l = e k := by rw [he, levE_of_mem hl, levE_of_mem hk, hll]
    have hgl : Valued.v (G l l) = exp (-(e k)) := by rw [← hel]; exact valued_single_diag hs hG hGN hl
    have hxl : Valued.v (x l) ≤ 1 := by
      have := hx l; rw [hel, sub_self, max_self, ord_zero_iff] at this; exact this
    have hxl2 : Valued.v (x l) ≤ exp (-1) := by
      by_contra hcon
      have hu : Valued.v (x l) = 1 := by
        by_contra hne; exact hcon (ord_one_of_ne h2 hxl hne)
      have h1 : Valued.v ((x l * x l - 1) * G l l) ≤ exp (-(2 + e k)) :=
        ord_mul (ord_unit_sq_sub_one h2 hu) hgl.le
      have e1 : G k k * (x k * x k - 2) =
          (x k * G k k * x k + x l * G l l * x l - G k k) - (x l * x l - 1) * G l l - (G k k + G l l) := by
        ring
      have h3 : Valued.v (G k k * (x k * x k - 2)) ≤ exp (-(e k + 2)) := by
        rw [e1]
        exact ord_sub (ord_sub hmain (ord_mono h1 (by omega))) hsum
      have h4 := ord_cancel hgk h3
      by_cases hku : Valued.v (x k) = 1
      · have e3 : (1 : Fv) = (x k * x k - 1) - (x k * x k - 2) := by ring
        have := ord_sub (ord_unit_sq_sub_one h2 hku) h4
        rw [← e3, map_one] at this
        exact hne1 this
      · have hk1 := ord_one_of_ne h2 hxk hku
        have e3 : (2 : Fv) = x k * x k - (x k * x k - 2) := by ring
        have := ord_sub (ord_mono (ord_mul hk1 hk1) (by norm_num)) h4
        rw [← e3, valued_two_eq h2, exp_le_exp] at this
        omega
    refine ⟨hone ?_, fun l' hl' hl'k hl'l => ?_⟩
    · have h1 : Valued.v (x l * G l l * x l) ≤ exp (-(1 + e k + 1)) :=
        ord_mul (ord_mul hxl2 hgl.le) hxl2
      have e1 : x k * G k k * x k - G k k =
          (x k * G k k * x k + x l * G l l * x l - G k k) - x l * G l l * x l := by ring
      rw [e1]
      exact ord_sub hmain (ord_mono h1 (by omega))
    · rw [huniq l' hl' hl'k hl'l]; exact hxl2
  · push_neg at hpair
    have hIiff : ∀ i, I i ↔ i = k := by
      intro i
      constructor
      · rintro ⟨hiS, hil⟩
        by_contra hik; exact hpair i hiS hik hil
      · rintro rfl; exact ⟨hk, rfl⟩
    have hsumI : (∑ i, if I i then x i * G i i * x i else 0) = x k * G k k * x k := by
      rw [← Finset.sum_filter]
      have : Finset.univ.filter I = {k} := by
        ext i; simp [hIiff]
      rw [this, Finset.sum_singleton]
    rw [hsumI] at hmain
    exact ⟨hone hmain, fun l hl hlk hll => absurd hll (hpair l hl hlk)⟩

/-- The Gram matrix of the rescaled basis $\gamma\Lambda$, $\Lambda = \mathrm{diag}(\lambda)$: $\Lambda G\Lambda$. -/
theorem locGram_mul_diagGL (γ : GL (Fin n) Fv) (lam : Fin n → Fv) (hlam : ∀ i, lam i ≠ 0) :
    locGram Q v (γ * diagGL lam hlam) = diagonal lam * locGram Q v γ * diagonal lam := by
  unfold locGram
  rw [Units.val_mul, diagGL_val, transpose_mul, diagonal_transpose]
  simp only [Matrix.mul_assoc]

/-- **Even spinor norm through a preserved lattice whose discriminant group is acted on trivially**: if
$A = cG'$ ($G'$ = `locGram Q v γ'`) is integral with $A_{ii}/2$ integral and $\det A \ne 0$, $\det\sigma = 1$, and
$(1 - S'')A^{-1}$ is integral for $S'' = \gamma'^{-1}S\gamma'$, then $\theta(\sigma)$ has even order
(`exists_sq_valued_wallDet_of_dual`). -/
theorem evenSpinor_of_conj_dual (hQ : Q.Nondegenerate) (γ : GL (Fin n) Fv) {c : Fv} (hc : c ≠ 0)
    (hint : ∀ i j, Valued.v (c * locGram Q v γ i j) ≤ 1)
    (heven : ∀ i, Valued.v (c * locGram Q v γ i i / 2) ≤ 1) (hdet : (c • locGram Q v γ).det ≠ 0)
    (σ : orthGroup Q Fv) (hσ1 : σ ∈ Tamagawa.soSub Q Fv)
    (hK : ∀ i j, Valued.v (((1 - (γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val) *
      (c • locGram Q v γ)⁻¹) i j) ≤ 1) :
    EvenSpinor Q σ := by
  set G := locGram Q v γ
  set S' := (γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val
  have hS'G : S'ᵀ * G * S' = G := conj_orth_any γ σ
  obtain ⟨m, P, R, hf⟩ := exists_wallFrame S'
  obtain ⟨hθ, hne, hdetm⟩ := spinorNorm_eq_wallDet_conj hQ γ σ hf
  set A := c • G
  have hA : Aᵀ = A := by simp only [A, transpose_smul, G, locGram_transpose]
  have hSA : S'ᵀ * A * S' = A := by
    simp only [A, Matrix.mul_smul, Matrix.smul_mul]
    rw [hS'G]
  obtain ⟨δ, hδ⟩ := exists_sq_valued_wallDet_of_dual A hA (fun i j => by simpa [A] using hint i j) hdet
    (fun i => by simpa [A, mul_div_assoc] using heven i) S' hSA hK hf
  have hm : Even m := by
    have h1 : (mat Q Fv σ).det = 1 := hσ1
    rw [h1] at hdetm
    exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : Fv) ≠ 1)).mp hdetm.symm
  obtain ⟨m', rfl⟩ := hm
  have hAd : (Pᵀ * A * R).det = c ^ (m' + m') * (Pᵀ * G * R).det := by
    simp only [A, Matrix.mul_smul, Matrix.smul_mul, det_smul, Fintype.card_fin]
  rw [hAd] at hδ
  exact ⟨_, hne, exists_even_of_scaled_sq hc hne m' hδ, hθ⟩

/-- $N = G^{-1}$ is symmetric when $G$ is. -/
theorem inv_symm_of_mul_eq_one {G N : Matrix (Fin n) (Fin n) Fv} (hG : Gᵀ = G) (hGN : G * N = 1) : Nᵀ = N := by
  have hNG : N * G = 1 := mul_eq_one_comm.mp hGN
  have h1 : Nᵀ * G = 1 := by
    have := congrArg transpose hGN
    rwa [transpose_mul, hG, transpose_one] at this
  calc Nᵀ = Nᵀ * (G * N) := by rw [hGN, Matrix.mul_one]
    _ = (Nᵀ * G) * N := by rw [Matrix.mul_assoc]
    _ = N := by rw [h1, Matrix.one_mul]

/-- **Even spinor norms for the level shapes** (see the module docstring): if $L_2 = \gamma\mathbb Z_2^n$ and
$G$ = `locGram Q v γ`, $N$ with $GN = 1$ satisfy `LevelShape v G N p lam Sg`, every proper $\sigma \in O(L_2)$ has a
spinor norm of even order. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: spinor norms of rotations of a level shape have even order)"]
theorem evenSpinor_of_levelShape (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) (N : Matrix (Fin n) (Fin n) Fv) (hN : locGram Q v γ * N = 1)
    {p : ℤ} {lam : Fin n → ℤ} {Sg : Finset (Fin n)} (hs : LevelShape v (locGram Q v γ) N p lam Sg)
    {σ : orthGroup Q Fv} (hσ : σ ∈ locStabV Q v L) (hσ1 : σ ∈ Tamagawa.soSub Q Fv) : EvenSpinor Q σ := by
  classical
  set G := locGram Q v γ with hGdef
  set e := levE p lam Sg with he
  have hgram : ∀ i j, Valued.v (G i j) ≤ exp (-(max (e i) (e j))) := hs.gram
  have hdual : ∀ i j, Valued.v (N i j) ≤ exp (-(-min (e i) (e j))) := hs.dual
  have heven2 : ∀ i, i ∉ Sg → Valued.v (G i i) ≤ exp (-(e i + 1)) := hs.even
  have hG : Gᵀ = G := locGram_transpose γ
  have hNG : N * G = 1 := mul_eq_one_comm.mp hN
  have hNsym : Nᵀ = N := inv_symm_of_mul_eq_one hG hN
  have hNcol : ∀ k ∈ Sg, ∀ m, m ≠ k → N m k = 0 := fun k hk => (col_orth_of_mul_eq_one hNG (hs.orth k hk)).1
  have hNrow : ∀ k ∈ Sg, ∀ m, m ≠ k → N k m = 0 := fun k hk m hm => by
    have := congrFun (congrFun hNsym m) k
    rw [transpose_apply] at this
    rw [this]; exact hNcol k hk m hm
  obtain ⟨hSint, hSorth⟩ := conj_integral_orth γ hγ hσ
  set S' := (γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val with hS'
  obtain ⟨hTint, -⟩ := conj_integral_orth γ hγ (inv_mem hσ)
  set T' := (γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ⁻¹ * γ.val with hT'
  have hmat : mat Q Fv σ⁻¹ * mat Q Fv σ = 1 := by
    change ((σ⁻¹ : orthGroup Q Fv) : GL (Fin n) Fv).val * (σ : GL (Fin n) Fv).val = 1
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  have hγγ : γ.val * (γ⁻¹ : GL (Fin n) Fv).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hγγ' : (γ⁻¹ : GL (Fin n) Fv).val * γ.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hTS : T' * S' = 1 := by
    calc T' * S' = (γ⁻¹ : GL (Fin n) Fv).val * (mat Q Fv σ⁻¹ * (γ.val * (γ⁻¹ : GL (Fin n) Fv).val) *
          mat Q Fv σ) * γ.val := by simp only [hT', hS', Matrix.mul_assoc]
      _ = 1 := by rw [hγγ, Matrix.mul_one, hmat, Matrix.mul_one, hγγ']
  have hST : S' * T' = 1 := mul_eq_one_comm.mp hTS
  have hTG : T'ᵀ * G = G * S' := by
    calc T'ᵀ * G = T'ᵀ * (S'ᵀ * G * S') := by rw [hSorth]
      _ = (S' * T')ᵀ * G * S' := by rw [Matrix.transpose_mul S' T']; simp only [Matrix.mul_assoc]
      _ = G * S' := by rw [hST, transpose_one, Matrix.one_mul]
  have hcolB := ord_conj_entry hs hNG hTint hTG
  have hcol : ∀ i j, Valued.v (S' i j) ≤ exp (-(max 0 (e j - e i))) := by
    intro i j
    rcases le_total 0 (e j - e i) with h | h
    · rw [max_eq_right h]; exact hcolB i j
    · rw [max_eq_left h, ord_zero_iff]; exact hSint i j
  have hbd : ∀ i, 2 * lam i + p ≤ e i ∧ e i ≤ 2 * lam i + p + 1 := fun i => levE_bounds p lam Sg i
  have hem : ∀ i ∈ Sg, e i = 2 * lam i + p + 1 := fun i hi => levE_of_mem hi
  have hen : ∀ i, i ∉ Sg → e i = 2 * lam i + p := fun i hi => levE_of_not_mem hi
  -- the rescaled basis
  set lamF : Fin n → Fv := fun i => (2 : Fv) ^ (-(lam i)) with hlamF
  have hlamF0 : ∀ i, lamF i ≠ 0 := fun i => zpow_ne_zero _ two_ne_zero
  set γ' := γ * diagGL lamF hlamF0 with hγ'
  have hpow : ∀ a b : ℤ, (2 : Fv) ^ a * (2 : Fv) ^ b = (2 : Fv) ^ (a + b) := fun a b =>
    (zpow_add₀ two_ne_zero a b).symm
  set S'' := (γ'⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ'.val with hS''def
  have hS'' : ∀ i j, S'' i j = (2 : Fv) ^ (lam i) * S' i j * (2 : Fv) ^ (-(lam j)) := by
    intro i j
    rw [hS''def, hγ', conj_diagGL_apply]
    simp only [hlamF, _root_.zpow_neg, inv_inv]
    rfl
  have hG' : ∀ i j, locGram Q v γ' i j = (2 : Fv) ^ (-(lam i)) * G i j * (2 : Fv) ^ (-(lam j)) := by
    intro i j
    rw [hγ', locGram_mul_diagGL, mul_diagonal, diagonal_mul]
  set c : Fv := (2 : Fv) ^ (-p) with hc
  have hc0 : c ≠ 0 := zpow_ne_zero _ two_ne_zero
  set B : Matrix (Fin n) (Fin n) Fv :=
    c⁻¹ • (diagonal (fun i => (lamF i)⁻¹) * N * diagonal (fun i => (lamF i)⁻¹)) with hB
  have hAB : (c • locGram Q v γ') * B = 1 := by
    rw [hB, hγ', locGram_mul_diagGL, smul_mul_smul_comm, mul_inv_cancel₀ hc0, one_smul]
    have hDD : diagonal lamF * diagonal (fun i => (lamF i)⁻¹) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hlamF0 i)
    calc diagonal lamF * G * diagonal lamF * (diagonal (fun i => (lamF i)⁻¹) * N * diagonal (fun i => (lamF i)⁻¹))
        = diagonal lamF * (G * (diagonal lamF * diagonal (fun i => (lamF i)⁻¹)) * N) *
            diagonal (fun i => (lamF i)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDD, Matrix.mul_one, hN, Matrix.mul_one, hDD]
  have hAinv : (c • locGram Q v γ')⁻¹ = B := Matrix.inv_eq_right_inv hAB
  have hdet : (c • locGram Q v γ').det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hAB
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  have hBe : ∀ i j, B i j = (2 : Fv) ^ p * ((2 : Fv) ^ (lam i) * N i j * (2 : Fv) ^ (lam j)) := by
    intro i j
    simp only [hB, Matrix.smul_apply, mul_diagonal, diagonal_mul, smul_eq_mul, hc, hlamF, _root_.zpow_neg, inv_inv]
  -- integrality of `S''`
  have hS''int : ∀ i j, Valued.v (S'' i j) ≤ exp (-0) := by
    intro i j
    rw [hS'']
    refine ord_mono (ord_mul (ord_mul (ord_two_zpow h2 (lam i)) (hcol i j)) (ord_two_zpow h2 (-(lam j)))) ?_
    have := hbd i; have := hbd j
    omega
  have h1S : ∀ i j, Valued.v ((1 - S'') i j) ≤ exp (-0) := by
    intro i j
    rw [Matrix.sub_apply]
    refine ord_sub ?_ (hS''int i j)
    rw [Matrix.one_apply]; split_ifs <;> simp
  -- the key congruence
  have hkey : ∀ k ∈ Sg, ∀ i, Valued.v ((1 - S'') i k) ≤ exp (-1) := by
    intro k hk i
    have hxx : (fun l => S' l k) ⬝ᵥ (G *ᵥ fun l => S' l k) = G k k := by
      rw [← gram_apply', hSorth]
    obtain ⟨hk1, hkl⟩ := level_key h2 hs hG hN hk (fun l => S' l k) (fun l => hcol l k) hxx
    rw [Matrix.sub_apply]
    by_cases hik : i = k
    · subst hik
      rw [Matrix.one_apply_eq, hS'', mul_assoc, mul_comm (S' i i), ← mul_assoc, hpow, add_neg_cancel,
        zpow_zero, one_mul]
      exact hk1
    · rw [Matrix.one_apply_ne hik, zero_sub, Valuation.map_neg, hS'']
      by_cases hsame : i ∈ Sg ∧ lam i = lam k
      · refine ord_mono (ord_mul (ord_mul (ord_two_zpow h2 (lam i)) (hkl i hsame.1 hik hsame.2))
          (ord_two_zpow h2 (-(lam k)))) ?_
        omega
      · refine ord_mono (ord_mul (ord_mul (ord_two_zpow h2 (lam i)) (hcol i k))
          (ord_two_zpow h2 (-(lam k)))) ?_
        have hek := hem k hk
        by_cases hiS : i ∈ Sg
        · have := hem i hiS
          have hne : lam i ≠ lam k := fun h => hsame ⟨hiS, h⟩
          omega
        · have := hen i hiS
          omega
  refine evenSpinor_of_conj_dual hQ γ' hc0 (fun i j => ?_) (fun i => ?_) hdet σ hσ1 (fun i k => ?_)
  · rw [hG', ← ord_zero_iff]
    refine ord_mono (ord_mul (ord_two_zpow h2 (-p)) (ord_mul (ord_mul (ord_two_zpow h2 (-(lam i)))
      (hgram i j)) (ord_two_zpow h2 (-(lam j))))) ?_
    have := hbd i; have := hbd j
    omega
  · have hGi : Valued.v (G i i) ≤ exp (-(2 * lam i + p + 1)) := by
      by_cases hiS : i ∈ Sg
      · have := hgram i i; rw [max_self, hem i hiS] at this; exact this
      · have := heven2 i hiS; rw [hen i hiS] at this; exact this
    rw [hG', div_eq_mul_inv, ← _root_.zpow_neg_one, ← ord_zero_iff]
    refine ord_mono (ord_mul (ord_mul (ord_two_zpow h2 (-p)) (ord_mul (ord_mul (ord_two_zpow h2 (-(lam i)))
      hGi) (ord_two_zpow h2 (-(lam i))))) (ord_two_zpow h2 (-1))) ?_
    omega
  · rw [hS''def.symm, hAinv, Matrix.mul_apply, ← ord_zero_iff]
    refine ord_sum _ _ fun j _ => ?_
    rw [hBe]
    by_cases hkS : k ∈ Sg
    · by_cases hjk : j = k
      · subst hjk
        have hNkk := hdual j j
        rw [min_self, hem j hkS] at hNkk
        refine ord_mono (ord_mul (hkey j hkS i) (ord_mul (ord_two_zpow h2 p) (ord_mul (ord_mul
          (ord_two_zpow h2 (lam j)) hNkk) (ord_two_zpow h2 (lam j))))) ?_
        omega
      · rw [hNcol k hkS j hjk]; simp
    · by_cases hjS : j ∈ Sg
      · have hjk : k ≠ j := fun h => hkS (h ▸ hjS)
        rw [hNrow j hjS k hjk]; simp
      · refine ord_mono (ord_mul (h1S i j) (ord_mul (ord_two_zpow h2 p) (ord_mul (ord_mul
          (ord_two_zpow h2 (lam j)) (hdual j k)) (ord_two_zpow h2 (lam k))))) ?_
        have := hen j hjS; have := hen k hkS
        have := min_le_left (e j) (e k); have := min_le_right (e j) (e k)
        omega

/-- **Theorem 18, "only if", at $p = 2$ for the level shapes** (Conway–Sloane §9.5, p. 391; unconditional): if
$L_2 = \gamma\mathbb Z_2^n$ satisfies `LevelShape` (with $GN = 1$) and has a binary orthogonal summand $b_i, b_j$ of
type (i) ($\lvert G_{ii}\rvert, \lvert G_{jj}\rvert \le \lvert 2G_{ij}\rvert$, an even Jordan constituent), then every
element of $\theta(O^+(L_2))$ is, up to squares, the product of the norms of an even number of $2$-adic root
vectors. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': the level shapes, any number of even constituents)"]
theorem theorem18OnlyIf_of_levelShape (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (N : Matrix (Fin n) (Fin n) Fv)
    (hN : locGram Q v γ * N = 1) {p : ℤ} {lam : Fin n → ℤ} {Sg : Finset (Fin n)}
    (hs : LevelShape v (locGram Q v γ) N p lam Sg) {i j : Fin n} (hij : i ≠ j)
    (horth : ∀ m, m ≠ i → m ≠ j → locGram Q v γ m i = 0 ∧ locGram Q v γ m j = 0)
    (hij0 : locGram Q v γ i j ≠ 0)
    (hi : Valued.v (locGram Q v γ i i) ≤ Valued.v (2 * locGram Q v γ i j))
    (hj : Valued.v (locGram Q v γ j j) ≤ Valued.v (2 * locGram Q v γ i j)) : Theorem18OnlyIf Q L v hQ :=
  theorem18OnlyIf_of_evenSpinor hQ h2 (fun _ hσ hσ1 => evenSpinor_of_levelShape hQ h2 γ hγ N hN hs hσ hσ1)
    (units_le_rootGroup_of_binary h2 γ hγ hij horth hij0 hi hj)

end Level

end QuadFormsKB.ConwaySloane
