/-
# Chenevier–Lannes, §3.1: $d$-neighbours are the lattices $\mathrm{vois}_d(L; u)$

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §3.1, the definition of $d$-neighbours, Proposition 3.1.4 and
Proposition 3.1.5, pp. 46–48. Printed page numbers.

Setting: $L = \mathbb{Z}^n$ with an integral quadratic form $Q = q_L$ whose Gram matrix $H$ (the inner product
$x \cdot y$ = `bQ Q x y` on $V = \mathbb{Q}^n$, `bZ` on $L$) has determinant $\pm 1$ (`IsUnit Q.hessian.det`): $L$ is
a q-module over $\mathbb{Z}$ in the book's sense (no definiteness is needed). For an integer $d \ge 1$, $u \in L$
with $q(u) \equiv 0 \bmod d$ and $v \in L$ with $u \cdot v \equiv 1 \bmod d$ (this $v$ exists exactly when $u$ is
$d$-primitive, $L$ being unimodular), the book's lattices are
$$M_d(L; u) = \{x \in L : u \cdot x \equiv 0 \bmod d\}, \qquad
  \mathrm{vois}_d(L; u) = M_d(L; u) + \mathbb{Z}\,e, \quad e = \tfrac1d\,(u - q(u)\,v)$$
(`voisLat Q d u v`, wave 3; `voisGen Q d u v` is $e$).

**Proves** (unconditional):
- `isDNeighbor_voisLat`, `prop_3_1_4` (Proposition 3.1.4): $\mathrm{vois}_d(L; u)$ is a $d$-neighbour of $L$
  (`IsDNeighbor`: an even integral lattice of $V$ equal to its dual, with $L/(L \cap L') \cong \mathbb{Z}/d$), with
  $L \cap \mathrm{vois}_d(L; u) = M_d(L; u)$; moreover $M^\sharp = L + \mathbb{Z}\,\tfrac ud$ for
  $M = M_d(L; u)$, and $\operatorname{res} M = M^\sharp / M$ is the hyperbolic module $H(\mathbb{Z}/d)$ on the classes
  of $e$ and $v$ ($q(e), q(v) \in \mathbb{Z}$, $e \cdot v \equiv \tfrac1d \bmod \mathbb{Z}$, and $ae + bv \in M$ iff
  $d \mid a$ and $d \mid b$), with the two Lagrangians $L/M = \langle v \rangle$ and
  $\mathrm{vois}_d(L; u)/M = \langle e \rangle$;
- `prop_3_1_5_surjective`, `prop_3_1_5_injective` (Proposition 3.1.5): every $d$-neighbour of $L$ is some
  $\mathrm{vois}_d(L; u)$, and $\mathrm{vois}_d(L; u) = \mathrm{vois}_d(L; u')$ iff $u' \equiv cu \bmod dL$ for an
  integer $c$, i.e. iff $[u] = [u']$ in $C_L(\mathbb{Z}/d)$: the map $C_L(\mathbb{Z}/d) \to \mathrm{Vois}_d(L)$,
  $c \mapsto \mathrm{vois}_d(L; c)$, is a bijection;
- `eq_voisLat_of_inf` (the end of the discussion before Proposition 3.1.4, p. 47): a $d$-neighbour $L'$ is determined
  by $L \cap L'$.

The book takes $d \ge 2$; everything here holds for $d \ge 1$ ($\mathrm{vois}_1(L; u) = L$).
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave4.HolyRoots

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

variable {n : ℕ}

/-! ### $d$-neighbours -/

/-- **A $d$-neighbour of $L$** (Chenevier–Lannes, §3.1, p. 46): a lattice $L' \subset V = \mathbb{Q} \otimes L$ which
is an even integral lattice equal to its own dual (a self-dual q-module for the form of $L$) and satisfies
$L/(L \cap L') \cong \mathbb{Z}/d$. Here $L = \mathbb{Z}^n$ with the form $Q$, and $L'$ is a $\mathbb{Z}$-submodule of
$\mathbb{Q}^n$; it is automatically a lattice, since $dL \subset L' \subset \tfrac1d L$ (`IsDNeighbor.smul_mem`,
`IsDNeighbor.smul_mem_std`). -/
@[kb "chenevierlannes2019" "§3.1, p. 46 (d-neighbours)"]
structure IsDNeighbor (Q : QuadForm ℤ n) (d : ℕ) (N : Submodule ℤ (Fin n → ℚ)) : Prop where
  /-- $q(x) \in \mathbb{Z}$ for every $x \in L'$ (even integral lattice). -/
  even : ∀ x ∈ N, ∃ k : ℤ, Q.evalIn ℚ x = k
  /-- $L'^\sharp = L'$: a vector $x \in V$ lies in $L'$ iff $x \cdot y \in \mathbb{Z}$ for every $y \in L'$. -/
  selfDual : ∀ x : Fin n → ℚ, x ∈ N ↔ ∀ y ∈ N, ∃ k : ℤ, bQ Q x y = k
  /-- $L/(L \cap L') \cong \mathbb{Z}/d$: a surjective homomorphism $f : L \to \mathbb{Z}/d$ with kernel
  $L \cap L'$. -/
  quotient : ∃ f : (Fin n → ℤ) →+ ZMod d, Function.Surjective f ∧ ∀ y, f y = 0 ↔ cv y ∈ N

/-! ### Unimodular lattices are self-dual (for $\det H = \pm 1$) -/

theorem det_mul_self_of_isUnit {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) :
    Q.hessian.det * Q.hessian.det = 1 := by
  rcases Int.isUnit_iff.mp hdet with h | h <;> rw [h] <;> norm_num

/-- $\rho = (\rho\,H)\,(\det H \operatorname{adj} H)$ for $\det H = \pm 1$. -/
theorem vecMul_hessian_adjugate' {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) (ρ : Fin n → ℚ) :
    ρ = (ρ ᵥ* Q.hessian.map (algebraMap ℤ ℚ)) ᵥ*
      ((Q.hessian.det • Q.hessian.adjugate).map (algebraMap ℤ ℚ)) := by
  rw [vecMul_vecMul, ← Matrix.map_mul, Matrix.mul_smul, mul_adjugate, smul_smul,
    det_mul_self_of_isUnit hdet, one_smul, Matrix.map_one _ (map_zero _) (map_one _), vecMul_one]

/-- **A unimodular lattice is its own dual** (for $\det H = \pm 1$): if $\rho \in V$ has $\rho \cdot y \in \mathbb{Z}$
for every $y \in L$, then $\rho \in L$. -/
theorem eq_cv_of_bQ_int' {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) {ρ : Fin n → ℚ}
    (h : ∀ y : Fin n → ℤ, ∃ k : ℤ, bQ Q ρ (cv y) = k) : ∃ r : Fin n → ℤ, ρ = cv r := by
  classical
  choose k hk using fun i => h (Pi.single i 1)
  have hcv : ∀ i : Fin n, cv (Pi.single i (1 : ℤ)) = Pi.single i (1 : ℚ) := fun i => by
    ext j
    by_cases hj : j = i
    · subst hj; simp [cv]
    · simp [cv, Pi.single_apply, hj]
  have hc : ρ ᵥ* Q.hessian.map (algebraMap ℤ ℚ) = cv k := by
    ext i
    have := hk i
    rw [hcv] at this
    simp only [bQ, dotProduct_mulVec, dotProduct_single, mul_one] at this
    simpa [cv] using this
  refine ⟨k ᵥ* (Q.hessian.det • Q.hessian.adjugate), ?_⟩
  rw [vecMul_hessian_adjugate' (Q := Q) hdet ρ, hc]
  ext j
  simp only [cv, vecMul, dotProduct, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]
  exact Finset.sum_congr rfl fun x _ => by simp only [eq_intCast, Int.cast_mul]

/-- $d \mid u \cdot y$ for all $y \in L$ forces $u \in dL$ (for $\det H = \pm 1$). -/
theorem dvd_of_forall_dvd_bZ {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) {d : ℕ} (hd : 1 ≤ d)
    {w : Fin n → ℤ} (h : ∀ y, (d : ℤ) ∣ bZ Q w y) : ∀ i, (d : ℤ) ∣ w i := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  obtain ⟨r, hr⟩ := eq_cv_of_bQ_int' hdet (ρ := (1 / (d : ℚ)) • cv w) fun y => by
    obtain ⟨k, hk⟩ := h y
    refine ⟨k, ?_⟩
    rw [bQ_smul_left, bQ_cv, hk]; push_cast; field_simp
  intro i
  refine ⟨r i, ?_⟩
  have := congrFun hr i
  simp only [Pi.smul_apply, cv_apply, smul_eq_mul] at this
  have h2 : (w i : ℚ) = d * r i := by rw [← this]; field_simp
  exact_mod_cast h2

theorem bZ_sub_left (Q : QuadForm ℤ n) (x y v : Fin n → ℤ) : bZ Q (x - y) v = bZ Q x v - bZ Q y v := by
  simp [bZ, sub_dotProduct]

/-! ### The generator $e$ of $\mathrm{vois}_d(L; u)$ over $M_d(L; u)$ -/

/-- **The generator** $e = \tfrac1d\,(u - q(u)\,v)$ of $\mathrm{vois}_d(L; u)$ over $M_d(L; u)$ (§3.1, p. 48; $w$ in
the proof of Proposition 3.1.4). -/
noncomputable def voisGen (Q : QuadForm ℤ n) (d : ℕ) (u v : Fin n → ℤ) : Fin n → ℚ :=
  (1 / (d : ℚ)) • cv (u - Q.eval u • v)

theorem voisGen_mem (Q : QuadForm ℤ n) (d : ℕ) (u v : Fin n → ℤ) : voisGen Q d u v ∈ voisLat Q d u v :=
  Submodule.subset_span (Or.inr rfl)

theorem cv_mem_voisLat {Q : QuadForm ℤ n} {d : ℕ} {u v y : Fin n → ℤ} (hy : (d : ℤ) ∣ bZ Q u y) :
    cv y ∈ voisLat Q d u v :=
  Submodule.subset_span (Or.inl ⟨y, rfl, hy⟩)

section Gen

variable {Q : QuadForm ℤ n} {d : ℕ} {u v : Fin n → ℤ}

/-- $e = \tfrac1d u - a v$ for $q(u) = da$. -/
theorem voisGen_eq (hd : 1 ≤ d) {a : ℤ} (ha : Q.eval u = d * a) :
    voisGen Q d u v = (1 / (d : ℚ)) • cv u - (a : ℚ) • cv v := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  ext i
  simp only [voisGen, ha, Pi.smul_apply, Pi.sub_apply, cv_apply, smul_eq_mul]
  push_cast
  field_simp

/-- $y \cdot e = \tfrac1d\,(u \cdot y) - a\,(v \cdot y)$ for $q(u) = da$. -/
theorem bQ_cv_voisGen (hd : 1 ≤ d) {a : ℤ} (ha : Q.eval u = d * a) (y : Fin n → ℤ) :
    bQ Q (cv y) (voisGen Q d u v) = (bZ Q u y : ℚ) / d - a * bZ Q v y := by
  rw [voisGen_eq hd ha, sub_eq_add_neg, bQ_add_right, ← neg_smul, bQ_smul_right, bQ_smul_right, bQ_cv, bQ_cv,
    bZ_comm Q y u, bZ_comm Q y v]
  ring

/-- $q(e) = a^2 q(v) - ac \in \mathbb{Z}$ for $q(u) = da$ and $u \cdot v = 1 + dc$. -/
theorem evalIn_voisGen (hd : 1 ≤ d) {a c : ℤ} (ha : Q.eval u = d * a) (hc : bZ Q u v - 1 = d * c) :
    Q.evalIn ℚ (voisGen Q d u v) = a ^ 2 * Q.eval v - a * c := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have h1 : Q.eval (u - Q.eval u • v) = Q.eval u - Q.eval u * bZ Q u v + Q.eval u ^ 2 * Q.eval v := by
    have := eval_add_smulZ Q u v (-Q.eval u)
    rw [neg_smul, ← sub_eq_add_neg] at this
    rw [this]; ring
  have hb : bZ Q u v = 1 + d * c := by linarith
  rw [voisGen, evalIn_smulQ, evalIn_cv, h1, ha, hb]
  push_cast
  field_simp
  ring

/-- **Elements of $\mathrm{vois}_d(L; u)$**: they are the $m + ke$ with $m \in M_d(L; u)$ and $k \in \mathbb{Z}$. -/
theorem mem_voisLat_iff {x : Fin n → ℚ} :
    x ∈ voisLat Q d u v ↔ ∃ m : Fin n → ℤ, ∃ k : ℤ, (d : ℤ) ∣ bZ Q u m ∧ x = cv m + (k : ℚ) • voisGen Q d u v := by
  constructor
  · intro hx
    refine Submodule.span_induction (p := fun x _ => ∃ m : Fin n → ℤ, ∃ k : ℤ, (d : ℤ) ∣ bZ Q u m ∧
      x = cv m + (k : ℚ) • voisGen Q d u v) ?_ ?_ ?_ ?_ hx
    · rintro x (⟨y, rfl, hy⟩ | rfl)
      · exact ⟨y, 0, hy, by simp⟩
      · exact ⟨0, 1, by simp [bZ], by simp [cv_zero, voisGen]⟩
    · exact ⟨0, 0, by simp [bZ], by simp [cv_zero]⟩
    · rintro x x' - - ⟨m, k, hm, rfl⟩ ⟨m', k', hm', rfl⟩
      refine ⟨m + m', k + k', ?_, ?_⟩
      · rw [bZ_add_right']; exact dvd_add hm hm'
      · rw [cv_add]; push_cast; rw [add_smul]; abel
    · rintro c x - ⟨m, k, hm, rfl⟩
      refine ⟨c • m, c * k, ?_, ?_⟩
      · rw [bZ_smul_right']; exact Dvd.dvd.mul_left hm c
      · ext i
        simp only [Pi.add_apply, Pi.smul_apply, cv_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_mul,
          Pi.mul_apply, Pi.intCast_apply, Int.cast_add, Int.cast_id]
        ring
  · rintro ⟨m, k, hm, rfl⟩
    exact Submodule.add_mem _ (cv_mem_voisLat hm)
      (by rw [Int.cast_smul_eq_zsmul]; exact Submodule.smul_mem _ _ (voisGen_mem Q d u v))

variable (hd : 1 ≤ d) (hq : (d : ℤ) ∣ Q.eval u) (hv : (d : ℤ) ∣ bZ Q u v - 1)
include hd hq hv

omit hv in
/-- $m \cdot e \in \mathbb{Z}$ for $m \in M_d(L; u)$. -/
theorem bQ_cv_voisGen_int {m : Fin n → ℤ} (hm : (d : ℤ) ∣ bZ Q u m) :
    ∃ k : ℤ, bQ Q (cv m) (voisGen Q d u v) = k := by
  obtain ⟨a, ha⟩ := hq
  obtain ⟨b, hb⟩ := hm
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  refine ⟨b - a * bZ Q v m, ?_⟩
  rw [bQ_cv_voisGen hd ha, hb]
  push_cast
  field_simp

/-- **$\mathrm{vois}_d(L; u)$ is even**: $q(x) \in \mathbb{Z}$ for every $x$ in it. -/
theorem voisLat_even {x : Fin n → ℚ} (hx : x ∈ voisLat Q d u v) : ∃ k : ℤ, Q.evalIn ℚ x = k := by
  obtain ⟨m, k, hm, rfl⟩ := mem_voisLat_iff.mp hx
  obtain ⟨a, ha⟩ := hq
  obtain ⟨c, hc⟩ := hv
  obtain ⟨z, hz⟩ := bQ_cv_voisGen_int hd ⟨a, ha⟩ hm
  refine ⟨Q.eval m + k * z + k ^ 2 * (a ^ 2 * Q.eval v - a * c), ?_⟩
  rw [evalIn_add_smulQ, evalIn_cv, hz, evalIn_voisGen hd ha hc]
  push_cast; ring

end Gen

/-- Polarization: an even lattice is integral, $x \cdot y = q(x + y) - q(x) - q(y)$. -/
theorem bQ_int_of_even {Q : QuadForm ℤ n} {N : Submodule ℤ (Fin n → ℚ)}
    (h : ∀ x ∈ N, ∃ k : ℤ, Q.evalIn ℚ x = k) {x y : Fin n → ℚ} (hx : x ∈ N) (hy : y ∈ N) :
    ∃ k : ℤ, bQ Q x y = k := by
  obtain ⟨a, ha⟩ := h _ (N.add_mem hx hy)
  obtain ⟨b, hb⟩ := h x hx
  obtain ⟨c, hc⟩ := h y hy
  have := evalIn_add_smulQ Q x y 1
  rw [one_smul, one_mul, one_pow, one_mul, ha, hb, hc] at this
  exact ⟨a - b - c, by push_cast; linarith⟩

/-! ### The dual of $M_d(L; u)$ -/

section Dual

variable {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) {d : ℕ} (hd : 1 ≤ d) {u v : Fin n → ℤ}
  (hv : (d : ℤ) ∣ bZ Q u v - 1)
include hdet hd hv

omit hdet hd in
/-- $y - (u \cdot y)\,v \in M_d(L; u)$. -/
theorem dvd_bZ_sub (y : Fin n → ℤ) : (d : ℤ) ∣ bZ Q u (y - bZ Q u y • v) := by
  obtain ⟨c, hc⟩ := hv
  refine ⟨-(bZ Q u y * c), ?_⟩
  rw [bZ_sub_right', bZ_smul_right']
  linear_combination (-(bZ Q u y)) * hc

/-- **The dual of $M = M_d(L; u)$** (proof of Proposition 3.1.4, p. 47): a vector $x \in V$ with $x \cdot M \subset
\mathbb{Z}$ is of the form $r + K\,\tfrac ud$ with $r \in L$ and $K \in \mathbb{Z}$ (one can take $K = d\,(x \cdot v)$).
-/
theorem eq_of_dual_mLat {x : Fin n → ℚ} (hx : ∀ y : Fin n → ℤ, (d : ℤ) ∣ bZ Q u y → ∃ k : ℤ, bQ Q x (cv y) = k) :
    ∃ r : Fin n → ℤ, ∃ K : ℤ, x = cv r + (K : ℚ) • ((1 / (d : ℚ)) • cv u) := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  obtain ⟨K, hK⟩ := hx ((d : ℤ) • v) (by rw [bZ_smul_right']; exact dvd_mul_right _ _)
  rw [cv_smul, bQ_smul_right] at hK
  obtain ⟨r, hr⟩ := eq_cv_of_bQ_int' hdet (ρ := x - (K : ℚ) • ((1 / (d : ℚ)) • cv u)) fun y => by
    obtain ⟨z, hz⟩ := hx _ (dvd_bZ_sub hv y)
    refine ⟨z, ?_⟩
    have e1 : cv y = cv (y - bZ Q u y • v) + (bZ Q u y : ℚ) • cv v := by
      rw [cv_sub, cv_smul]; abel
    have e2 : bQ Q x (cv v) = K / d := by
      field_simp; push_cast at hK; linarith
    rw [sub_eq_add_neg, bQ_add_left, ← neg_smul, bQ_smul_left, bQ_smul_left, bQ_cv, e1, bQ_add_right,
      bQ_smul_right, hz, e2, bZ_comm Q u y]
    ring
  exact ⟨r, K, by rw [← hr]; abel⟩

end Dual

/-! ### Proposition 3.1.4 -/

section Prop314

variable {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) {d : ℕ} (hd : 1 ≤ d) {u v : Fin n → ℤ}
  (hq : (d : ℤ) ∣ Q.eval u) (hv : (d : ℤ) ∣ bZ Q u v - 1)
include hd hq hv

/-- **$L \cap \mathrm{vois}_d(L; u) = M_d(L; u)$** (Proposition 3.1.4, p. 47). -/
theorem cv_mem_voisLat_iff (y : Fin n → ℤ) : cv y ∈ voisLat Q d u v ↔ (d : ℤ) ∣ bZ Q u y := by
  refine ⟨fun h => ?_, cv_mem_voisLat⟩
  obtain ⟨a, ha⟩ := hq
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  obtain ⟨k, hk⟩ := bQ_int_of_even (fun x hx => voisLat_even hd ⟨a, ha⟩ hv hx) h (voisGen_mem Q d u v)
  rw [bQ_cv_voisGen hd ha] at hk
  refine ⟨k + a * bZ Q v y, ?_⟩
  have : (bZ Q u y : ℚ) = d * (k + a * bZ Q v y) := by
    field_simp at hk; push_cast; linarith
  exact_mod_cast this

include hdet in
/-- **$\mathrm{vois}_d(L; u)$ is its own dual.** -/
theorem mem_voisLat_of_dual {x : Fin n → ℚ} (hx : ∀ y ∈ voisLat Q d u v, ∃ k : ℤ, bQ Q x y = k) :
    x ∈ voisLat Q d u v := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  obtain ⟨a, ha⟩ := hq
  obtain ⟨c, hc⟩ := hv
  obtain ⟨r, K, rfl⟩ := eq_of_dual_mLat hdet hd ⟨c, hc⟩ fun y hy => hx _ (cv_mem_voisLat hy)
  -- $u/d = e + a v$, so $x = (r + K a v) + K e$
  have hx' : cv r + (K : ℚ) • ((1 / (d : ℚ)) • cv u) =
      cv (r + (K * a) • v) + (K : ℚ) • voisGen Q d u v := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, cv_apply, smul_eq_mul, zsmul_eq_mul, voisGen,
      Pi.mul_apply, Pi.intCast_apply, Int.cast_mul, Int.cast_add, Int.cast_sub]
    rw [ha]; push_cast; field_simp; ring
  rw [hx'] at hx ⊢
  refine mem_voisLat_iff.mpr ⟨_, K, ?_, rfl⟩
  obtain ⟨z, hz⟩ := hx _ (voisGen_mem Q d u v)
  rw [bQ_add_left, bQ_smul_left, bQ_cv_voisGen hd ha, bQ_self_eq, evalIn_voisGen hd ha hc] at hz
  refine ⟨z + (K * a) * 0 + a * bZ Q v (r + (K * a) • v) - 2 * K * (a ^ 2 * Q.eval v - a * c), ?_⟩
  have : (bZ Q u (r + (K * a) • v) : ℚ) =
      d * (z + a * bZ Q v (r + (K * a) • v) - 2 * K * (a ^ 2 * Q.eval v - a * c)) := by
    field_simp at hz ⊢; push_cast at hz ⊢; linarith
  rw [mul_zero, add_zero]
  exact_mod_cast this

/-- The map $f : L \to \mathbb{Z}/d$, $y \mapsto u \cdot y \bmod d$. -/
def dotModHom (Q : QuadForm ℤ n) (d : ℕ) (u : Fin n → ℤ) : (Fin n → ℤ) →+ ZMod d where
  toFun y := ((bZ Q u y : ℤ) : ZMod d)
  map_zero' := by simp [bZ]
  map_add' y z := by rw [bZ_add_right']; push_cast; rfl

include hdet in
/-- **Proposition 3.1.4, the $d$-neighbour** (Chenevier–Lannes, p. 47): $\mathrm{vois}_d(L; u)$ is a $d$-neighbour of
$L$. Unconditional. -/
@[kb "chenevierlannes2019" "Prop. 3.1.4, p. 47"]
theorem isDNeighbor_voisLat : IsDNeighbor Q d (voisLat Q d u v) where
  even _ hx := voisLat_even hd hq hv hx
  selfDual x := ⟨fun hx _ hy => bQ_int_of_even (fun _ h => voisLat_even hd hq hv h) hx hy,
    mem_voisLat_of_dual hdet hd hq hv⟩
  quotient := by
    refine ⟨dotModHom Q d u, fun z => ?_, fun y => ?_⟩
    · obtain ⟨c, hc⟩ := hv
      refine ⟨(z.val : ℤ) • v, ?_⟩
      simp only [dotModHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, bZ_smul_right']
      have : bZ Q u v = 1 + d * c := by linarith
      rw [this]; push_cast
      rw [ZMod.natCast_self, zero_mul, add_zero, mul_one]
      haveI : NeZero d := ⟨by omega⟩
      exact ZMod.natCast_zmod_val z
    · rw [cv_mem_voisLat_iff hd hq hv]
      exact ZMod.intCast_zmod_eq_zero_iff_dvd _ d

end Prop314

/-- **Proposition 3.1.4** (Chenevier–Lannes, p. 47), in full: for $d \ge 1$, $u \in L$ with $q(u) \equiv 0 \bmod d$
and $v \in L$ with $u \cdot v \equiv 1 \bmod d$ (an isotropic line $c = [u]$ of $L/dL$), with
$M = M_d(L; u)$ and $e = \tfrac1d(u - q(u)v)$:
1. (the dual of $M$) $x \in V$ satisfies $x \cdot M \subset \mathbb{Z}$ iff $x = r + K\,\tfrac ud$ with $r \in L$,
   $K \in \mathbb{Z}$;
2. ($\operatorname{res} M \cong H(\mathbb{Z}/d)$, on the classes of $e$ and $v$, which generate $M^\sharp$ over $M$
   since $\tfrac ud = e + \tfrac{q(u)}d v$) $q(e), q(v) \in \mathbb{Z}$, $e \cdot v - \tfrac1d \in \mathbb{Z}$, and for
   integers $a, b$, $ae + bv \in M$ iff $d \mid a$ and $d \mid b$; the Lagrangian $L/M$ is generated by $v$;
3. ($\mathrm{vois}_d(L; u)$, the inverse image of the Lagrangian generated by $e$) is a $d$-neighbour of $L$ with
   $L \cap \mathrm{vois}_d(L; u) = M$.
Unconditional. -/
@[kb "chenevierlannes2019" "Prop. 3.1.4, p. 47"]
theorem prop_3_1_4 {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) {d : ℕ} (hd : 1 ≤ d) {u v : Fin n → ℤ}
    (hq : (d : ℤ) ∣ Q.eval u) (hv : (d : ℤ) ∣ bZ Q u v - 1) :
    (∀ x : Fin n → ℚ, (∀ y : Fin n → ℤ, (d : ℤ) ∣ bZ Q u y → ∃ k : ℤ, bQ Q x (cv y) = k) ↔
      ∃ r : Fin n → ℤ, ∃ K : ℤ, x = cv r + (K : ℚ) • ((1 / (d : ℚ)) • cv u)) ∧
    ((∃ k : ℤ, Q.evalIn ℚ (voisGen Q d u v) = k) ∧ (∃ k : ℤ, bQ Q (voisGen Q d u v) (cv v) - 1 / d = k) ∧
      ∀ a b : ℤ, ((∃ m : Fin n → ℤ, (d : ℤ) ∣ bZ Q u m ∧
        (a : ℚ) • voisGen Q d u v + (b : ℚ) • cv v = cv m) ↔ ((d : ℤ) ∣ a ∧ (d : ℤ) ∣ b))) ∧
    IsDNeighbor Q d (voisLat Q d u v) ∧ (∀ y : Fin n → ℤ, cv y ∈ voisLat Q d u v ↔ (d : ℤ) ∣ bZ Q u y) := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  obtain ⟨a₀, ha₀⟩ := hq
  obtain ⟨c₀, hc₀⟩ := hv
  refine ⟨fun x => ⟨eq_of_dual_mLat hdet hd ⟨c₀, hc₀⟩, ?_⟩, ⟨?_, ?_, ?_⟩, isDNeighbor_voisLat hdet hd ⟨a₀, ha₀⟩
    ⟨c₀, hc₀⟩, cv_mem_voisLat_iff hd ⟨a₀, ha₀⟩ ⟨c₀, hc₀⟩⟩
  · rintro ⟨r, K, rfl⟩ y ⟨b, hb⟩
    refine ⟨bZ Q r y + K * b, ?_⟩
    rw [bQ_add_left, bQ_smul_left, bQ_smul_left, bQ_cv, bQ_cv, hb]
    push_cast; field_simp
  · exact ⟨a₀ ^ 2 * Q.eval v - a₀ * c₀, by rw [evalIn_voisGen hd ha₀ hc₀]; push_cast; ring⟩
  · refine ⟨-(a₀ * bZ Q v v) + c₀, ?_⟩
    rw [bQ_symm, bQ_cv_voisGen hd ha₀]
    have : (bZ Q u v : ℚ) = 1 + d * c₀ := by exact_mod_cast (by linarith : bZ Q u v = 1 + d * c₀)
    rw [this]; push_cast; field_simp; ring
  · intro a b
    constructor
    · rintro ⟨m, hm, he⟩
      -- pair with $v$-free test vectors: $x \cdot (d\,y) $ ... use $u \cdot m$ and $e \cdot$ nothing: compute directly
      have hb' : (a : ℚ) • voisGen Q d u v = cv m - (b : ℚ) • cv v := by rw [← he]; abel
      rw [voisGen_eq hd ha₀, smul_sub, smul_smul, smul_smul] at hb'
      -- $\tfrac ad u = m - bv + a a_0 v \in L$
      have hu : (a * (1 / (d : ℚ))) • cv u = cv (m - b • v + (a * a₀) • v) := by
        rw [cv_add, cv_sub, cv_smul, cv_smul]; push_cast
        rw [← hb', mul_comm (a : ℚ) (a₀ : ℚ)]; abel
      -- pairing with $v$: $\tfrac ad (u \cdot v) \in \mathbb{Z}$, so $d \mid a$
      have hpair := congrArg (fun x => bQ Q x (cv v)) hu
      simp only [bQ_smul_left, bQ_cv] at hpair
      have hbv : (bZ Q u v : ℚ) = 1 + d * c₀ := by exact_mod_cast (by linarith : bZ Q u v = 1 + d * c₀)
      rw [hbv] at hpair
      set w := m - b • v + (a * a₀) • v
      have hda : (d : ℤ) ∣ a := by
        refine ⟨bZ Q w v - a * c₀, ?_⟩
        have : (a : ℚ) = d * (bZ Q w v - a * c₀) := by
          push_cast; field_simp at hpair; linarith
        exact_mod_cast this
      refine ⟨hda, ?_⟩
      -- then $bv = m - a e \in M$, so $d \mid b\,(u \cdot v)$, so $d \mid b$
      obtain ⟨a', rfl⟩ := hda
      have he2 : cv (b • v) = cv (m - a' • (u - Q.eval u • v)) := by
        rw [cv_sub, cv_smul, cv_smul, ← he, voisGen]; push_cast
        rw [smul_smul]; field_simp; abel
      have hbm := cv_injective he2
      have h1 : (d : ℤ) ∣ bZ Q u (b • v) := by
        rw [hbm, bZ_sub_right', bZ_smul_right', bZ_sub_right', bZ_smul_right', ha₀, bZ_self]
        exact dvd_sub hm ⟨a' * (2 * a₀ - a₀ * bZ Q u v), by rw [ha₀]; ring⟩
      rw [bZ_smul_right', show bZ Q u v = 1 + d * c₀ by linarith] at h1
      have : (d : ℤ) ∣ b := by
        have h2 : (d : ℤ) ∣ b * (d * c₀) := ⟨b * c₀, by ring⟩
        have := dvd_sub h1 h2
        rwa [show b * (1 + d * c₀) - b * (d * c₀) = b by ring] at this
      exact this
    · rintro ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩
      refine ⟨a' • (u - Q.eval u • v) + (d * b') • v, ?_, ?_⟩
      · rw [bZ_add_right', bZ_smul_right', bZ_smul_right', bZ_sub_right', bZ_smul_right', bZ_self, ha₀]
        exact ⟨a' * (2 * a₀ - a₀ * bZ Q u v) + b' * bZ Q u v, by ring⟩
      · ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, cv_apply, smul_eq_mul, zsmul_eq_mul, voisGen,
      Pi.mul_apply, Pi.intCast_apply, Int.cast_mul, Int.cast_add, Int.cast_sub]
        push_cast; field_simp

/-! ### Proposition 3.1.5 -/

/-- $dL \subset L'$ for a $d$-neighbour $L'$. -/
theorem IsDNeighbor.smul_mem {Q : QuadForm ℤ n} {d : ℕ} {N : Submodule ℤ (Fin n → ℚ)} (hN : IsDNeighbor Q d N)
    (y : Fin n → ℤ) : cv ((d : ℤ) • y) ∈ N := by
  obtain ⟨f, -, hf⟩ := hN.quotient
  rw [← hf, map_zsmul, zsmul_eq_mul]
  simp

/-- $dL' \subset L$ for a $d$-neighbour $L'$ of a unimodular $L$, so $dL \subset L' \subset \tfrac1d L$. -/
theorem IsDNeighbor.smul_mem_std {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) {d : ℕ}
    {N : Submodule ℤ (Fin n → ℚ)} (hN : IsDNeighbor Q d N) {x : Fin n → ℚ} (hx : x ∈ N) :
    ∃ y : Fin n → ℤ, (d : ℚ) • x = cv y := by
  refine eq_cv_of_bQ_int' hdet fun y => ?_
  obtain ⟨k, hk⟩ := (hN.selfDual x).mp hx _ (hN.smul_mem y)
  refine ⟨k, ?_⟩
  rw [bQ_smul_left, ← hk, cv_smul, bQ_smul_right]
  push_cast; ring

/-- **A $d$-neighbour is determined by $L \cap L'$** (Chenevier–Lannes, p. 47, before Proposition 3.1.4): if $L'$ is
an even lattice equal to its dual with $L \cap L' = M_d(L; u)$, where $u \cdot v \equiv 1 \bmod d$, then
$L' = \mathrm{vois}_d(L; u + dr)$ for some $r \in L$ with $q(u + dr) \equiv 0 \bmod d^2$. Unconditional. -/
@[kb "chenevierlannes2019" "§3.1, p. 47 (L' is determined by L ∩ L')"]
theorem eq_voisLat_of_inf {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) {d : ℕ} (hd : 1 ≤ d)
    {N : Submodule ℤ (Fin n → ℚ)} (heven : ∀ x ∈ N, ∃ k : ℤ, Q.evalIn ℚ x = k)
    (hdual : ∀ x : Fin n → ℚ, x ∈ N ↔ ∀ y ∈ N, ∃ k : ℤ, bQ Q x y = k) {u v : Fin n → ℤ}
    (hM : ∀ y : Fin n → ℤ, cv y ∈ N ↔ (d : ℤ) ∣ bZ Q u y) (hv : (d : ℤ) ∣ bZ Q u v - 1) :
    ∃ r : Fin n → ℤ, ((d : ℤ) ^ 2 ∣ Q.eval (u + (d : ℤ) • r)) ∧ N = voisLat Q d (u + (d : ℤ) • r) v := by
  classical
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  set w : Fin n → ℚ := (1 / (d : ℚ)) • cv u
  -- every element of $N$ is $r + K\,u/d$
  have hrep : ∀ x ∈ N, ∃ r : Fin n → ℤ, ∃ K : ℤ, x = cv r + (K : ℚ) • w := fun x hx =>
    eq_of_dual_mLat hdet hd hv fun y hy => (hdual x).mp hx _ ((hM y).mpr hy)
  -- the ideal of coefficients $K$
  let G : Ideal ℤ :=
    { carrier := {K | ∃ r : Fin n → ℤ, cv r + (K : ℚ) • w ∈ N}
      add_mem' := by
        rintro K K' ⟨r, hr⟩ ⟨r', hr'⟩
        refine ⟨r + r', ?_⟩
        have := N.add_mem hr hr'
        convert this using 1
        ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, cv_apply, smul_eq_mul, zsmul_eq_mul, voisGen,
      Pi.mul_apply, Pi.intCast_apply, Int.cast_mul, Int.cast_add, Int.cast_sub]
        push_cast; ring
      zero_mem' := ⟨0, by simp [cv_zero]⟩
      smul_mem' := by
        rintro c K ⟨r, hr⟩
        refine ⟨c • r, ?_⟩
        have := N.smul_mem c hr
        convert this using 1
        ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, cv_apply, smul_eq_mul, zsmul_eq_mul, voisGen,
      Pi.mul_apply, Pi.intCast_apply, Int.cast_mul, Int.cast_add, Int.cast_sub]
        push_cast; ring }
  obtain ⟨g, hg⟩ := (Submodule.IsPrincipal.principal G)
  have hgG : g ∈ G := by rw [hg]; exact Submodule.mem_span_singleton_self g
  have hdvd : ∀ K ∈ G, g ∣ K := fun K hK => by
    rw [hg, Submodule.mem_span_singleton] at hK
    obtain ⟨t, rfl⟩ := hK
    exact Dvd.intro_left t rfl
  -- $d \in G$, so $g \mid d$
  have hdG : (d : ℤ) ∈ G := ⟨(d : ℤ) • v - u, by
    have : cv ((d : ℤ) • v - u) + ((d : ℤ) : ℚ) • w = cv ((d : ℤ) • v) := by
      simp only [w, cv_sub, smul_smul]; push_cast
      rw [mul_one_div_cancel hd0, one_smul]; abel
    rw [this]
    exact (hM _).mpr (by rw [bZ_smul_right']; exact dvd_mul_right _ _)⟩
  obtain ⟨s, hs⟩ := hdvd _ hdG
  -- $s v \in N^\sharp = N$, hence $d \mid s$
  have hsv : cv (s • v) ∈ N := by
    refine (hdual _).mpr fun y hy => ?_
    obtain ⟨r, K, rfl⟩ := hrep y hy
    obtain ⟨t, rfl⟩ := hdvd K ⟨r, hy⟩
    refine ⟨bZ Q (s • v) r + t * bZ Q v u, ?_⟩
    simp only [w, bQ_add_right, bQ_smul_right, bQ_cv]
    rw [bZ_smul_left Q s v u]
    have hs' : (d : ℚ) = g * s := by exact_mod_cast hs
    push_cast
    field_simp
    rw [hs']; ring
  obtain ⟨c, hc⟩ := hv
  have hds : (d : ℤ) ∣ s := by
    have h1 := (hM _).mp hsv
    rw [bZ_smul_right', show bZ Q u v = 1 + d * c by linarith] at h1
    have h2 : (d : ℤ) ∣ s * (d * c) := ⟨s * c, by ring⟩
    have := dvd_sub h1 h2
    rwa [show s * (1 + d * c) - s * (d * c) = s by ring] at this
  obtain ⟨k', hk'⟩ := hds
  have hgu : IsUnit g := by
    refine isUnit_iff_exists_inv.mpr ⟨k', ?_⟩
    have : (d : ℤ) * 1 = d * (g * k') := by rw [mul_one]; nth_rewrite 1 [hs, hk']; ring
    exact (mul_left_cancel₀ (by exact_mod_cast (by omega : d ≠ 0)) this).symm
  have h1G : (1 : ℤ) ∈ G := by
    rw [hg, Ideal.submodule_span_eq, Ideal.span_singleton_eq_top.mpr hgu]; trivial
  obtain ⟨r₀, hr₀⟩ := h1G
  set x₀ := cv r₀ + ((1 : ℤ) : ℚ) • w
  set u' := u + (d : ℤ) • r₀
  have hx₀ : (d : ℚ) • x₀ = cv u' := by
    ext i
    simp only [x₀, u', w]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, cv_apply, smul_eq_mul, zsmul_eq_mul, voisGen,
      Pi.mul_apply, Pi.intCast_apply, Int.cast_mul, Int.cast_add, Int.cast_sub]
    push_cast; field_simp; ring
  obtain ⟨z, hz⟩ := heven _ hr₀
  have hqu' : Q.eval u' = (d : ℤ) ^ 2 * z := by
    have := congrArg (Q.evalIn ℚ) hx₀
    rw [evalIn_smulQ, evalIn_cv, hz] at this
    exact_mod_cast this.symm
  have hv' : (d : ℤ) ∣ bZ Q u' v - 1 := ⟨c + bZ Q r₀ v, by
    simp only [u', bZ_add_left, bZ_smul_left]; linarith⟩
  have hq' : (d : ℤ) ∣ Q.eval u' := ⟨d * z, by rw [hqu']; ring⟩
  have he : voisGen Q d u' v = x₀ - cv (((d : ℤ) * z) • v) := by
    rw [voisGen_eq hd (a := (d : ℤ) * z) (by rw [hqu']; ring), ← hx₀, smul_smul, one_div_mul_cancel hd0,
      one_smul, cv_smul]
  have he_mem : voisGen Q d u' v ∈ N := by
    rw [he]
    refine N.sub_mem hr₀ ((hM _).mpr ?_)
    rw [bZ_smul_right']; exact ⟨z * bZ Q u v, by ring⟩
  refine ⟨r₀, ⟨z, hqu'⟩, le_antisymm (fun x hx => ?_) ?_⟩
  · exact mem_voisLat_of_dual hdet hd hq' hv' fun y hy => (hdual x).mp hx y (by
      -- $\mathrm{vois}_d(L; u') \subset N$, shown below; we inline it
      obtain ⟨m, k, hm, rfl⟩ := mem_voisLat_iff.mp hy
      refine N.add_mem ((hM m).mpr ?_) ?_
      · have : bZ Q u' m = bZ Q u m + d * bZ Q r₀ m := by simp only [u', bZ_add_left, bZ_smul_left]
        rw [this] at hm
        simpa using (Int.dvd_add_left (dvd_mul_right (d : ℤ) _)).mp hm
      · rw [Int.cast_smul_eq_zsmul]
        exact N.smul_mem k he_mem)
  · rw [voisLat, Submodule.span_le]
    rintro x (⟨y, rfl, hy⟩ | rfl)
    · refine (hM y).mpr ?_
      have : bZ Q u' y = bZ Q u y + d * bZ Q r₀ y := by simp only [u', bZ_add_left, bZ_smul_left]
      rw [this] at hy
      simpa using (Int.dvd_add_left (dvd_mul_right (d : ℤ) _)).mp hy
    · exact he_mem

/-- `bZ Q u` modulo $d$ represents every additive map $L \to \mathbb{Z}/d$ (for $\det H = \pm 1$). -/
theorem exists_dotModHom_eq {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) {d : ℕ} [NeZero d]
    (f : (Fin n → ℤ) →+ ZMod d) : ∃ u : Fin n → ℤ, ∀ y, f y = ((bZ Q u y : ℤ) : ZMod d) := by
  classical
  let gv : Fin n → ℤ := fun i => ((f (Pi.single i 1)).val : ℤ)
  refine ⟨(Q.hessian.det • Q.hessian.adjugate) *ᵥ gv, fun y => ?_⟩
  have hH : Q.hessian *ᵥ ((Q.hessian.det • Q.hessian.adjugate) *ᵥ gv) = gv := by
    rw [mulVec_mulVec, Matrix.mul_smul, mul_adjugate, smul_smul, det_mul_self_of_isUnit hdet, one_smul,
      one_mulVec]
  rw [bZ_comm, bZ, hH]
  have hy : y = ∑ i, y i • Pi.single i (1 : ℤ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hy]
  rw [map_sum]
  simp only [map_zsmul, dotProduct, gv]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ZMod.natCast_zmod_val, zsmul_eq_mul]

/-- **Proposition 3.1.5, surjectivity** (Chenevier–Lannes, p. 48): every $d$-neighbour $L'$ of $L$ ($d \ge 1$, $L$
unimodular) is $\mathrm{vois}_d(L; u)$ for some $u \in L$ with $q(u) \equiv 0 \bmod d$ and some $v \in L$ with
$u \cdot v \equiv 1 \bmod d$ (an isotropic line $[u] \in C_L(\mathbb{Z}/d)$). Unconditional. -/
@[kb "chenevierlannes2019" "Prop. 3.1.5, p. 48"]
theorem prop_3_1_5_surjective {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) {d : ℕ} (hd : 1 ≤ d)
    {N : Submodule ℤ (Fin n → ℚ)} (hN : IsDNeighbor Q d N) :
    ∃ u v : Fin n → ℤ, (d : ℤ) ∣ Q.eval u ∧ (d : ℤ) ∣ bZ Q u v - 1 ∧ N = voisLat Q d u v := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨f, hfs, hf⟩ := hN.quotient
  obtain ⟨u, hu⟩ := exists_dotModHom_eq hdet f
  obtain ⟨v, hv1⟩ := hfs 1
  have hv : (d : ℤ) ∣ bZ Q u v - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [← hu, hv1, sub_self]
  have hM : ∀ y, cv y ∈ N ↔ (d : ℤ) ∣ bZ Q u y := fun y => by
    rw [← hf, hu, ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨r, ⟨z, hz⟩, hN'⟩ := eq_voisLat_of_inf hdet hd hN.even hN.selfDual hM hv
  refine ⟨_, v, ⟨d * z, by rw [hz]; ring⟩, ?_, hN'⟩
  obtain ⟨c, hc⟩ := hv
  exact ⟨c + bZ Q r v, by rw [bZ_add_left, bZ_smul_left]; linarith⟩

/-- **Proposition 3.1.5, injectivity** (Chenevier–Lannes, p. 48): for $d \ge 1$ and admissible pairs $(u, v)$,
$(u', v')$, $\mathrm{vois}_d(L; u) = \mathrm{vois}_d(L; u')$ iff $u' \equiv cu \bmod dL$ for some integer $c$, i.e. iff
$u$ and $u'$ define the same line of $L/dL$. Together with `prop_3_1_5_surjective` and `isDNeighbor_voisLat`: the
map $C_L(\mathbb{Z}/d) \to \mathrm{Vois}_d(L)$, $c \mapsto \mathrm{vois}_d(L; c)$, is a bijection. Unconditional. -/
@[kb "chenevierlannes2019" "Prop. 3.1.5, p. 48"]
theorem prop_3_1_5_injective {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) {d : ℕ} (hd : 1 ≤ d)
    {u v u' v' : Fin n → ℤ} (hq : (d : ℤ) ∣ Q.eval u) (hv : (d : ℤ) ∣ bZ Q u v - 1)
    (hq' : (d : ℤ) ∣ Q.eval u') (hv' : (d : ℤ) ∣ bZ Q u' v' - 1) :
    voisLat Q d u v = voisLat Q d u' v' ↔ ∃ c : ℤ, ∀ i, (d : ℤ) ∣ u' i - c * u i := by
  constructor
  · intro h
    have hM : ∀ y, (d : ℤ) ∣ bZ Q u y ↔ (d : ℤ) ∣ bZ Q u' y := fun y => by
      rw [← cv_mem_voisLat_iff hd hq hv, ← cv_mem_voisLat_iff hd hq' hv', h]
    refine ⟨bZ Q u' v, dvd_of_forall_dvd_bZ hdet hd fun y => ?_⟩
    have h1 := (hM _).mp (dvd_bZ_sub hv y)
    rw [bZ_sub_right', bZ_smul_right'] at h1
    have : bZ Q (u' - bZ Q u' v • u) y = bZ Q u' y - bZ Q u y * bZ Q u' v := by
      rw [bZ_sub_left, bZ_smul_left]; ring
    rw [show u' - bZ Q u' v • u = fun i => u' i - bZ Q u' v * u i from rfl] at this
    rw [this]; exact h1
  · rintro ⟨c, hc⟩
    -- $c$ is a unit modulo $d$
    have hcop : IsCoprime c (d : ℤ) := by
      obtain ⟨c', hc'⟩ := hv'
      have hw : ∀ y, (d : ℤ) ∣ bZ Q u' y - c * bZ Q u y := fun y => by
        have : bZ Q u' y - c * bZ Q u y = bZ Q (fun i => u' i - c * u i) y := by
          rw [show (fun i => u' i - c * u i) = u' - c • u from rfl, bZ_sub_left, bZ_smul_left]
        rw [this]
        obtain ⟨t, ht⟩ : ∃ t : Fin n → ℤ, (fun i => u' i - c * u i) = (d : ℤ) • t :=
          ⟨fun i => (hc i).choose, funext fun i => by simpa using (hc i).choose_spec⟩
        rw [ht, bZ_smul_left]; exact dvd_mul_right _ _
      obtain ⟨t, ht⟩ := hw v'
      exact ⟨bZ Q u v', t - c', by linear_combination hc' - ht⟩
    have hM : ∀ y, cv y ∈ voisLat Q d u' v' ↔ (d : ℤ) ∣ bZ Q u y := fun y => by
      rw [cv_mem_voisLat_iff hd hq' hv']
      obtain ⟨t, ht⟩ : ∃ t : Fin n → ℤ, u' = c • u + (d : ℤ) • t :=
        ⟨fun i => (hc i).choose, funext fun i => by
          have := (hc i).choose_spec; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linarith⟩
      rw [ht, bZ_add_left, bZ_smul_left, bZ_smul_left, Int.dvd_add_left (dvd_mul_right _ _)]
      exact ⟨fun h => hcop.symm.dvd_of_dvd_mul_left h, fun h => Dvd.dvd.mul_left h c⟩
    have hN := isDNeighbor_voisLat hdet hd hq' hv'
    obtain ⟨r, ⟨z, hz⟩, he⟩ := eq_voisLat_of_inf hdet hd hN.even hN.selfDual hM hv
    rw [he]
    refine (voisLat_congr hd r rfl hq ⟨d * z, by rw [hz]; ring⟩ hv (by
      obtain ⟨c₁, hc₁⟩ := hv
      exact ⟨c₁ + bZ Q r v, by rw [bZ_add_left, bZ_smul_left]; linarith⟩)).symm

end QuadFormsKB.ChenevierLannes
