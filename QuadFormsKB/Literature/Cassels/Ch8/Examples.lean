/-
# Cassels, Chapter 8, Examples 1 and 4 (i)–(ii)

**Setting** (as in `Ch8/Canonical.lean`): forms over $\mathbb Q_p$ by their symmetric matrices, $\mathbb Z_p$-equivalence
`ZpEquiv`; in Example 4, a classically integral form over $\mathbb Z_2$ is a symmetric matrix $F$ over $\mathbb Z_2$ with
$f(\vec a) = \vec a^{t}F\vec a$ and $f(\vec a, \vec b) = \vec a^{t}F\vec b$.

**Proves**
* `ex1_two`, `ex1_three`, `ex1_five` (**Example 1**, p. 124): diagonal forms $\mathbb Z_p$-equivalent to
  $f = 5x^{2} + 2xy + 5y^{2}$ for $p = 2, 3, 5$: $5x^{2} + \frac{24}{5}y^{2}$ for $p = 2, 3$ and $12x^{2} + 8y^{2}$ for
  $p = 3, 5$;
* `ex4_exists_char`, `ex4_char_unique`, `ex4_char_value` (**Example 4 (i)–(ii)**, p. 125): for a classically integral
  form over $\mathbb Z_2$ with unit determinant there is a vector $\vec b$ with $f(\vec a) \equiv f(\vec a, \vec b)
  \pmod 2$ for all $\vec a$, unique modulo $2$, and $f(\vec b)$ is determined modulo $8$.
-/
import QuadFormsKB.Literature.Cassels.Ch8.Canonical

namespace QuadFormsKB.Cassels

open Matrix

/-- $5$ is prime (the instance needed for $\mathbb Z_5$). -/
local instance factPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- A matrix over $\mathbb Z_p$ with unit determinant, as an element of $\mathrm{GL}_2(\mathbb Z_p)$. -/
private noncomputable def glOfDet {p : ℕ} [Fact p.Prime] (T : Matrix (Fin 2) (Fin 2) ℤ_[p]) (h : IsUnit T.det) :
    GL (Fin 2) ℤ_[p] :=
  ((Matrix.isUnit_iff_isUnit_det T).2 h).unit

/-- The substitution $x \mapsto x - y/5$ over $\mathbb Z_p$, $p \ne 5$. -/
private theorem ex1_shear {p : ℕ} [hp : Fact p.Prime] (hp5 : p ≠ 5) :
    ZpEquiv (p := p) !![5, 1; 1, 5] !![5, 0; 0, 24 / 5] := by
  have h5 : IsUnit (5 : ℤ_[p]) := by
    have : IsUnit ((5 : ℕ) : ℤ_[p]) := PadicInt.isUnit_iff.2
      (PadicInt.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes hp.out (by norm_num)).2 hp5))
    simpa using this
  obtain ⟨u, hu⟩ := h5
  set c : ℤ_[p] := ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
  have hc : (c : ℚ_[p]) = 5⁻¹ := by
    have h1 : (5 : ℤ_[p]) * c = 1 := by rw [← hu]; exact u.mul_inv
    have h2 : (5 : ℚ_[p]) * (c : ℚ_[p]) = 1 := by exact_mod_cast congrArg ((↑) : ℤ_[p] → ℚ_[p]) h1
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h2)
  refine ⟨glOfDet !![1, -c; 0, 1] (by simp [Matrix.det_fin_two]), ?_⟩
  simp only [glOfDet, IsUnit.unit_spec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, hc]

/-- The substitution $x \mapsto x + y$, $y \mapsto x - y$ over $\mathbb Z_p$, $p \ne 2$. -/
private theorem ex1_sum {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ZpEquiv (p := p) !![5, 1; 1, 5] !![12, 0; 0, 8] := by
  have h2 : IsUnit (2 : ℤ_[p]) := by
    have : IsUnit ((2 : ℕ) : ℤ_[p]) := PadicInt.isUnit_iff.2
      (PadicInt.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2))
    simpa using this
  have hdet : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℤ_[p]).det = -2 := by
    simp [Matrix.det_fin_two]; ring
  refine ⟨glOfDet !![1, 1; 1, -1] (by rw [hdet]; exact h2.neg), ?_⟩
  simp only [glOfDet, IsUnit.unit_spec]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> norm_num

/-- **Cassels, Ch. 8, Example 1** ($p = 2$): *let $f(x) = 5x^{2} + 2xy + 5y^{2}$; find diagonal forms which are
$\mathbb Z_p$-equivalent to $f$ for $p = 2, 3, 5$.* For $p = 2$: $5x^{2} + \frac{24}{5}y^{2}$ (substitute
$x \mapsto x - y/5$). -/
@[kb "cassels1978" "Ch. 8, Ex. 1, p. 124 (p = 2)"]
theorem ex1_two : ZpEquiv (p := 2) !![5, 1; 1, 5] !![5, 0; 0, 24 / 5] :=
  ex1_shear (by norm_num)

/-- **Cassels, Ch. 8, Example 1** ($p = 3$): $f = 5x^{2} + 2xy + 5y^{2}$ is $\mathbb Z_3$-equivalent to
$5x^{2} + \frac{24}{5}y^{2}$ and to $12x^{2} + 8y^{2}$ (substitute $x \mapsto x + y$, $y \mapsto x - y$). -/
@[kb "cassels1978" "Ch. 8, Ex. 1, p. 124 (p = 3)"]
theorem ex1_three : ZpEquiv (p := 3) !![5, 1; 1, 5] !![5, 0; 0, 24 / 5] ∧
    ZpEquiv (p := 3) !![5, 1; 1, 5] !![12, 0; 0, 8] :=
  ⟨ex1_shear (by norm_num), ex1_sum (by norm_num)⟩

/-- **Cassels, Ch. 8, Example 1** ($p = 5$): $f = 5x^{2} + 2xy + 5y^{2}$ is $\mathbb Z_5$-equivalent to
$12x^{2} + 8y^{2}$. -/
@[kb "cassels1978" "Ch. 8, Ex. 1, p. 124 (p = 5)"]
theorem ex1_five : ZpEquiv (p := 5) !![5, 1; 1, 5] !![12, 0; 0, 8] :=
  ex1_sum (by norm_num)

variable {n : ℕ}

/-- Divisibility by $2$ in $\mathbb Z_2$ is vanishing of the reduction mod $2$. -/
private theorem two_dvd_iff_toZMod (x : ℤ_[2]) : (2 : ℤ_[2]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
  simp

/-- Over $\mathbb F_2$, $\vec a^{t}G\vec a = \sum_i G_{ii}a_i$ for symmetric $G$. -/
private theorem zmod_two_quad (G : Matrix (Fin n) (Fin n) (ZMod 2)) (hG : Gᵀ = G) (a : Fin n → ZMod 2) :
    a ⬝ᵥ (G *ᵥ a) = ∑ i, G i i * a i := by
  have hsymm : ∀ i j, G j i = G i j := fun i j => by
    have := congrFun (congrFun hG i) j
    simpa [Matrix.transpose_apply] using this
  set f : Fin n × Fin n → ZMod 2 := fun x => if x.1 = x.2 then 0 else a x.1 * G x.1 x.2 * a x.2 with hf
  have h0 : ∑ x, f x = 0 := by
    refine Finset.sum_involution (fun x _ => (x.2, x.1)) ?_ ?_ ?_ ?_
    · intro x _
      by_cases h : x.1 = x.2
      · simp [hf, h]
      · have h' : x.2 ≠ x.1 := fun e => h e.symm
        simp only [hf, h, h', ite_false, hsymm x.1 x.2]
        have : ∀ y : ZMod 2, y + y = 0 := by decide
        rw [show a x.2 * G x.1 x.2 * a x.1 = a x.1 * G x.1 x.2 * a x.2 by ring]
        exact this _
    · intro x _ hx h
      apply hx
      have : x.2 = x.1 := congrArg Prod.fst h
      simp [hf, this]
    · intros; exact Finset.mem_univ _
    · intro x _; rfl
  have h1 : a ⬝ᵥ (G *ᵥ a) = ∑ x : Fin n × Fin n, a x.1 * G x.1 x.2 * a x.2 := by
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : ∀ x : Fin n × Fin n, a x.1 * G x.1 x.2 * a x.2 = f x + if x.1 = x.2 then G x.1 x.1 * a x.1 else 0 := by
    intro x
    by_cases h : x.1 = x.2
    · have sq : ∀ y : ZMod 2, y * y = y := by decide
      simp only [hf, h, ite_true, zero_add]
      rw [← h]
      linear_combination (G x.1 x.1) * sq (a x.1)
    · simp [hf, h]
  rw [h1, Finset.sum_congr rfl fun x _ => h2 x, Finset.sum_add_distrib, h0, zero_add, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- For symmetric $F$ over $\mathbb Z_2$, $\vec a^{t}F\vec a - \sum_i F_{ii}a_i$ is even. -/
private theorem two_dvd_quad_diag (F : Matrix (Fin n) (Fin n) ℤ_[2]) (hF : Fᵀ = F) (a : Fin n → ℤ_[2]) :
    (2 : ℤ_[2]) ∣ a ⬝ᵥ (F *ᵥ a) - a ⬝ᵥ (fun i => F i i) := by
  rw [two_dvd_iff_toZMod, map_sub, sub_eq_zero]
  have hG : (F.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2))ᵀ = F.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) := by
    rw [← Matrix.transpose_map, hF]
  have := zmod_two_quad _ hG (fun i => PadicInt.toZMod (a i))
  have h1 : PadicInt.toZMod (a ⬝ᵥ (F *ᵥ a)) = (fun i => PadicInt.toZMod (a i)) ⬝ᵥ
      ((F.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)) *ᵥ (fun i => PadicInt.toZMod (a i))) := by
    simp [dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply]
  rw [h1, this]
  simp [dotProduct, map_sum, map_mul, Matrix.map_apply, mul_comm]

/-- **Cassels, Ch. 8, Example 4 (i)**, existence: *let $f$ be a classically integral $\mathbb Z_2$-form in $n$ variables
with $d(f)$ a unit. Show that there is a $\vec b \in \mathbb Z_2^n$ such that $f(\vec a) \equiv f(\vec a, \vec b)
\pmod 2$ for every $\vec a \in \mathbb Z_2^n$.* -/
@[kb "cassels1978" "Ch. 8, Ex. 4 (i), p. 125 (existence)"]
theorem ex4_exists_char (F : Matrix (Fin n) (Fin n) ℤ_[2]) (hF : Fᵀ = F) (hd : IsUnit F.det) :
    ∃ b : Fin n → ℤ_[2], ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (F *ᵥ a) - a ⬝ᵥ (F *ᵥ b) := by
  refine ⟨F⁻¹ *ᵥ (fun i => F i i), fun a => ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]
  exact two_dvd_quad_diag F hF a

/-- **Cassels, Ch. 8, Example 4 (i)**, uniqueness: *… and that $\vec b$ is unique mod $2$.* -/
@[kb "cassels1978" "Ch. 8, Ex. 4 (i), p. 125 (uniqueness mod 2)"]
theorem ex4_char_unique (F : Matrix (Fin n) (Fin n) ℤ_[2]) (_hF : Fᵀ = F) (hd : IsUnit F.det)
    {b b' : Fin n → ℤ_[2]} (hb : ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (F *ᵥ a) - a ⬝ᵥ (F *ᵥ b))
    (hb' : ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (F *ᵥ a) - a ⬝ᵥ (F *ᵥ b')) : ∀ i, (2 : ℤ_[2]) ∣ b i - b' i := by
  intro i
  have hk : ∀ k, (2 : ℤ_[2]) ∣ (F *ᵥ (b - b')) k := by
    intro k
    have h := dvd_sub (hb' (Pi.single k 1)) (hb (Pi.single k 1))
    have e : Pi.single k (1 : ℤ_[2]) ⬝ᵥ (F *ᵥ b) - Pi.single k 1 ⬝ᵥ (F *ᵥ b') = (F *ᵥ (b - b')) k := by
      simp [Matrix.mulVec_sub]
    rw [← e]
    convert h using 1
    ring
  have hc : b i - b' i = (F⁻¹ *ᵥ (F *ᵥ (b - b'))) i := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]
    rfl
  rw [hc, two_dvd_iff_toZMod]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_eq_zero fun j _ => ?_
  have := (two_dvd_iff_toZMod _).1 (hk j)
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at this
  rw [this, mul_zero]

/-- **Cassels, Ch. 8, Example 4 (ii)**: *show that $f(\vec b)$ is uniquely determined mod $8$*: any two vectors
$\vec b, \vec b'$ as in (i) have $f(\vec b) \equiv f(\vec b') \pmod 8$. -/
@[kb "cassels1978" "Ch. 8, Ex. 4 (ii), p. 125"]
theorem ex4_char_value (F : Matrix (Fin n) (Fin n) ℤ_[2]) (hF : Fᵀ = F) (hd : IsUnit F.det)
    {b b' : Fin n → ℤ_[2]} (hb : ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (F *ᵥ a) - a ⬝ᵥ (F *ᵥ b))
    (hb' : ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (F *ᵥ a) - a ⬝ᵥ (F *ᵥ b')) :
    (8 : ℤ_[2]) ∣ b ⬝ᵥ (F *ᵥ b) - b' ⬝ᵥ (F *ᵥ b') := by
  have hu := fun i => ex4_char_unique F hF hd hb hb' i
  choose c hc using hu
  have hb'eq : b = b' + (2 : ℤ_[2]) • c := by
    funext i
    have := hc i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination this
  have hsymm : c ⬝ᵥ (F *ᵥ b') = b' ⬝ᵥ (F *ᵥ c) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hF, dotProduct_comm]
  obtain ⟨m, hm⟩ := hb' c
  have hexp : b ⬝ᵥ (F *ᵥ b) - b' ⬝ᵥ (F *ᵥ b') =
      4 * (b' ⬝ᵥ (F *ᵥ c) + c ⬝ᵥ (F *ᵥ c)) := by
    rw [hb'eq]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    have h3 : (F *ᵥ b') ⬝ᵥ c = c ⬝ᵥ (F *ᵥ b') := dotProduct_comm _ _
    linear_combination 2 * hsymm
  refine ⟨b' ⬝ᵥ (F *ᵥ c) + m, ?_⟩
  rw [hexp]
  linear_combination 4 * hm + 4 * hsymm

end QuadFormsKB.Cassels
