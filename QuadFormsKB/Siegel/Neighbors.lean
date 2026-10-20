/-
# Kneser neighbours, part 2: $p$-neighbours of $\mathbb{Z}^n$ and their construction

**Layer:** lattices in $V = \mathbb{Q}^n$ with the rational quadratic form of an integral form $Q$ (`QuadForm ℤ n`);
lattices are $\mathbb{Z}$-submodules of $\mathbb{Q}^n$ (`Submodule ℤ (Fin n → ℚ)`), the base lattice is $L = \mathbb{Z}^n$
(`stdLat`), so $Q$ itself is the Gram form of $L$ in the standard basis.

**Defines** (AWS notes `hanke2011aws`, Def. 1.10.1, p. 22) the **$p$-neighbours** of $L$ (`IsNeighbor`): lattices $L'$
with $[L : L \cap L'] = [L' : L \cap L'] = p$ on which $Q$ is $\mathbb{Z}$-valued; and the explicit neighbour
(`nbLat`, AWS §1.10.1, Thm. 1.10.2)
$$L(\vec{v}) = L_{\vec{v}} + \mathbb{Z}\tfrac{1}{p}\vec{v}, \qquad L_{\vec{v}} = \{\vec{x} \in L : p \mid B(\vec{x}, \vec{v})\},$$
for $\vec{v} \in \mathbb{Z}^n$ with $\vec{v} \not\equiv 0$, $p^2 \mid Q(\vec{v})$ ($B(\vec{x}, \vec{y}) = \vec{x}^{\mathsf T} H \vec{y}$, $H$ the Hessian).

**Proves**, for an odd prime $p \nmid \det H$:
- `isNeighbor_nbLat`: $L(\vec{v})$ is a $p$-neighbour;
- `exists_eq_nbLat` (AWS Thm. 1.10.2): every $p$-neighbour is some $L(\vec{v})$;
- `mem_nbLat_iff`: $\tfrac1p\vec{y} \in L(\vec{v}) \iff \vec{y} \equiv k\vec{v} \pmod p$ for some $k$ and $p^2 \mid B(\vec{y}, \vec{v})$; so
  $L(\vec{v})$ depends only on the line $\mathbb{F}_p\bar{\vec{v}}$ (`nbLat_eq_of_line`), and different isotropic lines give different
  neighbours (`line_eq_of_nbLat_eq`);
- `exists_lift`: every nonzero isotropic $\bar{\vec{v}} \in \mathbb{F}_p^n$ lifts to $\vec{v}$ with $p^2 \mid Q(\vec{v})$.

So the $p$-neighbours of $L$ are in bijection with the isotropic lines of $L/pL$ (AWS Thm. 1.10.4; `Siegel/EichlerCommutation.lean`).

*Remark (AWS Def. 1.10.1).* The notes also require $H(L, L') \not\subseteq \mathbb{Z}$. It is omitted here: for $p \nmid \det H$ it
is automatic ($H(L, L') \subseteq \mathbb{Z}$ would put $L'$ in the dual lattice $L^\#$, which equals $L$ locally at $p$, while $L'$
agrees with $L$ away from $p$, so $L' \subseteq L$, contradicting $[L' : L \cap L'] = p$). This argument is not formalized; with
it omitted, the definition and the characterization `exists_eq_nbLat` are what is used.
-/
import QuadFormsKB.Siegel.NeighborCount

open Matrix

namespace QuadFormsKB.Siegel.Kneser

variable {n : ℕ}

/-! ### The standard lattice and integer vectors in $\mathbb{Q}^n$ -/

/-- The integer vector $\vec{y} \in \mathbb{Z}^n$ as a vector of $\mathbb{Q}^n$. -/
def cv (y : Fin n → ℤ) : Fin n → ℚ := fun i => (y i : ℚ)

@[simp] theorem cv_apply (y : Fin n → ℤ) (i : Fin n) : cv y i = y i := rfl

theorem cv_add (y z : Fin n → ℤ) : cv (y + z) = cv y + cv z := by ext i; simp
theorem cv_smul (c : ℤ) (y : Fin n → ℤ) : cv (c • y) = (c : ℚ) • cv y := by ext i; simp
theorem cv_zero : cv (0 : Fin n → ℤ) = 0 := by ext i; simp
theorem cv_sub (y z : Fin n → ℤ) : cv (y - z) = cv y - cv z := by ext i; simp
theorem cv_injective : Function.Injective (cv (n := n)) := fun y z h => by
  ext i; have := congrFun h i; simpa using this

/-- **The standard lattice** $L = \mathbb{Z}^n \subset \mathbb{Q}^n$. -/
def stdLat (n : ℕ) : Submodule ℤ (Fin n → ℚ) where
  carrier := {x | ∃ y : Fin n → ℤ, x = cv y}
  add_mem' := by
    rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩; exact ⟨y + z, (cv_add y z).symm⟩
  zero_mem' := ⟨0, cv_zero.symm⟩
  smul_mem' := by
    rintro c _ ⟨y, rfl⟩; exact ⟨c • y, by rw [cv_smul]; rfl⟩

theorem mem_stdLat {x : Fin n → ℚ} : x ∈ stdLat n ↔ ∃ y : Fin n → ℤ, x = cv y := Iff.rfl

/-- The integral bilinear form $B(\vec{y}, \vec{v}) = \vec{y}^{\mathsf T} H \vec{v} \in \mathbb{Z}$. -/
def bZ (Q : QuadForm ℤ n) (y v : Fin n → ℤ) : ℤ := y ⬝ᵥ (Q.hessian *ᵥ v)

/-- The rational polar form $B(\vec{x}, \vec{y}) = \vec{x}^{\mathsf T} H \vec{y}$ on $\mathbb{Q}^n$. -/
def bQ (Q : QuadForm ℤ n) (x y : Fin n → ℚ) : ℚ := x ⬝ᵥ (Q.hessian.map (algebraMap ℤ ℚ) *ᵥ y)

section Basic

variable (Q : QuadForm ℤ n)

theorem evalIn_cv (y : Fin n → ℤ) : Q.evalIn ℚ (cv y) = (Q.eval y : ℚ) := evalIn_intCast Q y

theorem bQ_cv (y v : Fin n → ℤ) : bQ Q (cv y) (cv v) = (bZ Q y v : ℚ) := by
  simp only [bQ, bZ, dotProduct, mulVec, cv_apply]
  push_cast
  simp [Matrix.map_apply]

theorem evalIn_add_smulQ (x y : Fin n → ℚ) (t : ℚ) :
    Q.evalIn ℚ (x + t • y) = Q.evalIn ℚ x + t * bQ Q x y + t ^ 2 * Q.evalIn ℚ y := by
  have h1 := QuadForm.polar_eq_hessian ℚ Q x (t • y)
  have h2 : Q.evalIn ℚ (t • y) = t ^ 2 * Q.evalIn ℚ y := by
    rw [QuadForm.evalIn_eq_dotProduct, QuadForm.evalIn_eq_dotProduct, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, smul_eq_mul]
    ring
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] at h1
  unfold bQ
  linear_combination h1 + h2

theorem evalIn_smulQ (x : Fin n → ℚ) (t : ℚ) : Q.evalIn ℚ (t • x) = t ^ 2 * Q.evalIn ℚ x := by
  have h := evalIn_add_smulQ Q 0 x t
  simpa [QuadForm.evalIn, bQ] using h

theorem bQ_add_right (x y z : Fin n → ℚ) : bQ Q x (y + z) = bQ Q x y + bQ Q x z := by
  simp [bQ, mulVec_add, dotProduct_add]

theorem bQ_add_left (x y z : Fin n → ℚ) : bQ Q (x + y) z = bQ Q x z + bQ Q y z := by
  simp [bQ, add_dotProduct]

theorem bQ_smul_right (x y : Fin n → ℚ) (t : ℚ) : bQ Q x (t • y) = t * bQ Q x y := by
  simp [bQ, mulVec_smul, dotProduct_smul]

theorem bQ_smul_left (x y : Fin n → ℚ) (t : ℚ) : bQ Q (t • x) y = t * bQ Q x y := by
  simp [bQ, smul_dotProduct]

theorem bZ_add_left (x y v : Fin n → ℤ) : bZ Q (x + y) v = bZ Q x v + bZ Q y v := by
  simp [bZ, add_dotProduct]

theorem bZ_smul_left (c : ℤ) (x v : Fin n → ℤ) : bZ Q (c • x) v = c * bZ Q x v := by
  unfold bZ; rw [smul_dotProduct, smul_eq_mul]

theorem bZ_comm (x y : Fin n → ℤ) : bZ Q x y = bZ Q y x := by
  unfold bZ
  conv_lhs => rw [← LocalDensity.hessian_isSymm Q]
  rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]

theorem bZ_self (v : Fin n → ℤ) : bZ Q v v = 2 * Q.eval v := by
  rw [bZ, ← LocalDensity.two_mul_eval_eq_hessian]

/-- Taylor expansion over $\mathbb{Z}$: $Q(\vec{x} + t\vec{y}) = Q(\vec{x}) + tB(\vec{x}, \vec{y}) + t^2Q(\vec{y})$. -/
theorem eval_add_smulZ (x y : Fin n → ℤ) (t : ℤ) :
    Q.eval (x + t • y) = Q.eval x + t * bZ Q x y + t ^ 2 * Q.eval y := by
  have h := evalIn_add_smulQ Q (cv x) (cv y) t
  rw [← cv_smul, ← cv_add, evalIn_cv, evalIn_cv, evalIn_cv, bQ_cv] at h
  exact_mod_cast h

end Basic

/-! ### Neighbours -/

/-- **$p$-neighbours of $L = \mathbb{Z}^n$** (AWS notes, Def. 1.10.1, p. 22): a lattice $L' \subset \mathbb{Q}^n$ with
$$[L : L \cap L'] = p, \qquad [L' : L \cap L'] = p, \qquad Q(L') \subseteq \mathbb{Z}.$$
Fields: `relIndex_std` ($[L : L \cap L'] = p$; Mathlib's `relIndex H K` is $[K : H \cap K]$), `relIndex_self`
($[L' : L \cap L'] = p$), `integral` ($Q(\vec{x}) \in \mathbb{Z}$ for $\vec{x} \in L'$). The notes' extra condition
$H(L, L') \not\subseteq \mathbb{Z}$ is omitted (automatic for $p \nmid \det H$; module docstring, not formalized). -/
@[kb "hanke2011aws" "Def. 1.10.1, p. 22"]
structure IsNeighbor (Q : QuadForm ℤ n) (p : ℕ) (L' : Submodule ℤ (Fin n → ℚ)) : Prop where
  relIndex_std : L'.toAddSubgroup.relIndex (stdLat n).toAddSubgroup = p
  relIndex_self : (stdLat n).toAddSubgroup.relIndex L'.toAddSubgroup = p
  integral : ∀ x ∈ L', ∃ z : ℤ, Q.evalIn ℚ x = z

/-- **The explicit $p$-neighbour** $L(\vec{v}) = L_{\vec{v}} + \mathbb{Z}\frac1p\vec{v}$, $L_{\vec{v}} = \{\vec{y} \in \mathbb{Z}^n : p \mid B(\vec{y}, \vec{v})\}$
(AWS notes, §1.10.1, Thm. 1.10.2, p. 22): the vectors $\vec{y} + \frac{k}{p}\vec{v}$ with $\vec{y} \in \mathbb{Z}^n$, $p \mid B(\vec{y}, \vec{v})$,
$k \in \mathbb{Z}$. A $p$-neighbour when $\vec{v} \not\equiv 0 \pmod p$ and $p^2 \mid Q(\vec{v})$ (`isNeighbor_nbLat`). -/
@[kb "hanke2011aws" "§1.10.1, Thm. 1.10.2, p. 22"]
def nbLat (Q : QuadForm ℤ n) (p : ℕ) (v : Fin n → ℤ) : Submodule ℤ (Fin n → ℚ) where
  carrier := {x | ∃ y : Fin n → ℤ, ∃ k : ℤ, (p : ℤ) ∣ bZ Q y v ∧ x = cv y + ((k : ℚ) / p) • cv v}
  add_mem' := by
    rintro _ _ ⟨y, k, hy, rfl⟩ ⟨y', k', hy', rfl⟩
    refine ⟨y + y', k + k', by rw [bZ_add_left]; exact dvd_add hy hy', ?_⟩
    rw [cv_add]; push_cast; rw [add_div, add_smul]; abel
  zero_mem' := ⟨0, 0, by simp [bZ], by simp [cv_zero]⟩
  smul_mem' := by
    rintro c _ ⟨y, k, hy, rfl⟩
    refine ⟨c • y, c * k, by rw [bZ_smul_left]; exact dvd_mul_of_dvd_right hy c, ?_⟩
    rw [cv_smul]; simp only [zsmul_eq_mul, Int.cast_mul, smul_add]
    rw [Pi.intCast_def]
    ext i; simp [mul_div_assoc]; ring

section Lattice

variable {Q : QuadForm ℤ n} {p : ℕ} [hp : Fact p.Prime]

theorem p_ne_zero : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero

/-- Every element of $L(\vec{v})$ is $\frac1p\vec{y}$ with $\vec{y} \in \mathbb{Z}^n$. -/
theorem exists_eq_of_mem_nbLat {v : Fin n → ℤ} {x : Fin n → ℚ} (hx : x ∈ nbLat Q p v) :
    ∃ y : Fin n → ℤ, x = (1 / (p : ℚ)) • cv y := by
  obtain ⟨y, k, -, rfl⟩ := hx
  refine ⟨(p : ℤ) • y + k • v, ?_⟩
  rw [cv_add, cv_smul, cv_smul, smul_add, smul_smul, smul_smul]
  have := p_ne_zero (p := p)
  congr 1
  · rw [show (1 / (p : ℚ)) * ((p : ℤ) : ℚ) = 1 by push_cast; field_simp, one_smul]
  · congr 1; ring

/-- **Membership in $L(\vec{v})$** ($p^2 \mid Q(\vec{v})$): $\frac1p\vec{y} \in L(\vec{v})$ iff $\vec{y} \equiv k\vec{v} \pmod p$ for some
$k \in \mathbb{Z}$ and $p^2 \mid B(\vec{y}, \vec{v})$. -/
theorem mem_nbLat_iff {v : Fin n → ℤ} (hv : (p : ℤ) ^ 2 ∣ Q.eval v) (y : Fin n → ℤ) :
    (1 / (p : ℚ)) • cv y ∈ nbLat Q p v ↔
      (∃ k : ℤ, ∃ z : Fin n → ℤ, y = k • v + (p : ℤ) • z) ∧ (p : ℤ) ^ 2 ∣ bZ Q y v := by
  have hp0 := p_ne_zero (p := p)
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  constructor
  · rintro ⟨z, k, hz, he⟩
    have hy : y = k • v + (p : ℤ) • z := by
      apply cv_injective
      have := congrArg (fun w => (p : ℚ) • w) he
      simp only [smul_smul, smul_add] at this
      rw [show (p : ℚ) * (1 / p) = 1 by field_simp, one_smul,
        show (p : ℚ) * (k / p) = k by field_simp] at this
      rw [this, cv_add, cv_smul, cv_smul]; push_cast; abel
    refine ⟨⟨k, z, hy⟩, ?_⟩
    obtain ⟨c, hc⟩ := hz
    obtain ⟨d, hd⟩ := hv
    rw [hy, bZ_add_left, bZ_smul_left, bZ_smul_left, bZ_self, hd, hc]
    exact ⟨2 * k * d + c, by ring⟩
  · rintro ⟨⟨k, z, hy⟩, hb⟩
    refine ⟨z, k, ?_, ?_⟩
    · obtain ⟨d, hd⟩ := hv
      rw [hy, bZ_add_left, bZ_smul_left, bZ_smul_left, bZ_self, hd] at hb
      obtain ⟨c, hc⟩ := hb
      refine ⟨c - 2 * k * d, ?_⟩
      apply mul_left_cancel₀ hpZ
      linear_combination hc
    · rw [hy, cv_add, cv_smul, cv_smul, smul_add, smul_smul, smul_smul]
      push_cast
      rw [show 1 / (p : ℚ) * p = 1 by field_simp, one_smul, add_comm]
      congr 1; congr 1; ring

/-- **Integrality of $L(\vec{v})$** ($p^2 \mid Q(\vec{v})$): $Q(\vec{y} + \frac kp\vec{v}) = Q(\vec{y}) + \frac kp B(\vec{y}, \vec{v}) + \frac{k^2}{p^2}Q(\vec{v}) \in \mathbb{Z}$. -/
theorem nbLat_integral {v : Fin n → ℤ} (hv : (p : ℤ) ^ 2 ∣ Q.eval v) :
    ∀ x ∈ nbLat Q p v, ∃ z : ℤ, Q.evalIn ℚ x = z := by
  rintro _ ⟨y, k, ⟨c, hc⟩, rfl⟩
  obtain ⟨d, hd⟩ := hv
  refine ⟨Q.eval y + k * c + k ^ 2 * d, ?_⟩
  rw [evalIn_add_smulQ, evalIn_cv, evalIn_cv, bQ_cv, hc, hd]
  have := p_ne_zero (p := p)
  push_cast
  field_simp

/-- **The reduction of an integer vector mod $p$.** -/
def red (p : ℕ) (y : Fin n → ℤ) : Fin n → ZMod p := fun i => (y i : ZMod p)

theorem red_add (y z : Fin n → ℤ) : red p (y + z) = red p y + red p z := by ext i; simp [red]
theorem red_smul (c : ℤ) (y : Fin n → ℤ) : red p (c • y) = (c : ZMod p) • red p y := by ext i; simp [red]

theorem red_eq_zero_iff (y : Fin n → ℤ) : red p y = 0 ↔ ∀ i, (p : ℤ) ∣ y i := by
  simp only [funext_iff, red, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem qv_red (y : Fin n → ℤ) : qv Q p (red p y) = (Q.eval y : ZMod p) := by
  unfold red; exact evalIn_intCast Q y

theorem bv_red (y v : Fin n → ℤ) : bv Q p (red p y) (red p v) = (bZ Q y v : ZMod p) := by
  simp only [bv, bZ, red, dotProduct, mulVec]
  push_cast
  simp [Matrix.map_apply]

theorem dvd_of_red (z : ℤ) : (z : ZMod p) = 0 ↔ (p : ℤ) ∣ z := ZMod.intCast_zmod_eq_zero_iff_dvd z p

/-- $\vec{y} \equiv k\vec{v} \pmod p$ for some $k \in \mathbb{Z}$ iff $\bar{\vec{y}} \in \mathbb{F}_p \bar{\vec{v}}$. -/
theorem exists_congr_iff (y v : Fin n → ℤ) :
    (∃ k : ℤ, ∃ z : Fin n → ℤ, y = k • v + (p : ℤ) • z) ↔ ∃ c : ZMod p, red p y = c • red p v := by
  constructor
  · rintro ⟨k, z, rfl⟩
    refine ⟨k, ?_⟩
    rw [red_add, red_smul, red_smul]
    simp
  · rintro ⟨c, hc⟩
    refine ⟨(c.val : ℤ), fun i => (y i - c.val * v i) / p, ?_⟩
    ext i
    have h : (p : ℤ) ∣ y i - c.val * v i := by
      rw [← dvd_of_red]
      have := congrFun hc i
      simp only [red, Pi.smul_apply, smul_eq_mul] at this
      push_cast; rw [this]; simp
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Int.mul_ediv_cancel' h]; ring

/-- **Membership of $\frac1p\vec{y}$ for $\bar{\vec{y}} \ne 0$** ($p^2 \mid Q(\vec{v})$, $p^2 \mid Q(\vec{y})$): $\frac1p\vec{y} \in L(\vec{v})$ iff
$\bar{\vec{y}} \in \mathbb{F}_p\bar{\vec{v}}$ (the condition $p^2 \mid B(\vec{y}, \vec{v})$ is then automatic). -/
theorem mem_nbLat_iff_of_red_ne_zero {v : Fin n → ℤ} (hv : (p : ℤ) ^ 2 ∣ Q.eval v) {y : Fin n → ℤ}
    (hy : (p : ℤ) ^ 2 ∣ Q.eval y) (hy0 : red p y ≠ 0) :
    (1 / (p : ℚ)) • cv y ∈ nbLat Q p v ↔ ∃ c : ZMod p, red p y = c • red p v := by
  rw [mem_nbLat_iff hv, ← exists_congr_iff]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  obtain ⟨k, z, rfl⟩ := h
  have hk : ¬ (p : ℤ) ∣ k := by
    intro hk
    apply hy0
    rw [red_add, red_smul, red_smul, (dvd_of_red k).mpr hk]
    simp
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  -- Q(kv + pz) = k²Q(v) + kp B(v,z) + p²Q(z), so p | B(v, z)
  have e := eval_add_smulZ Q (k • v) z p
  rw [show Q.eval (k • v) = k ^ 2 * Q.eval v by
    have := eval_add_smulZ Q 0 v k
    simpa [bZ, QuadForm.evalIn] using this] at e
  rw [bZ_smul_left] at e
  obtain ⟨d, hd⟩ := hv
  obtain ⟨c, hc⟩ := hy
  have h1 : (p : ℤ) ∣ k * bZ Q v z := by
    have : (p : ℤ) ^ 2 * (c - k ^ 2 * d - Q.eval z) = (p : ℤ) * (k * bZ Q v z) := by
      linear_combination -hc + e + k ^ 2 * hd
    have h2 : (p : ℤ) * (p : ℤ) ∣ (p : ℤ) * (k * bZ Q v z) :=
      ⟨c - k ^ 2 * d - Q.eval z, by rw [← this]; ring⟩
    exact (mul_dvd_mul_iff_left (by exact_mod_cast hp.out.ne_zero)).mp h2
  have h2 : (p : ℤ) ∣ bZ Q v z := (hpZ.dvd_or_dvd h1).resolve_left hk
  obtain ⟨b, hb⟩ := h2
  rw [bZ_add_left, bZ_smul_left, bZ_smul_left, bZ_self, hd, bZ_comm, hb]
  exact ⟨2 * k * d + b, by ring⟩

/-- **Membership of $\vec{z} \in \mathbb{Z}^n$** ($p^2 \mid Q(\vec{v})$): $\vec{z} \in L(\vec{v})$ iff $p \mid B(\vec{z}, \vec{v})$. -/
theorem cv_mem_nbLat_iff {v : Fin n → ℤ} (hv : (p : ℤ) ^ 2 ∣ Q.eval v) (z : Fin n → ℤ) :
    cv z ∈ nbLat Q p v ↔ (p : ℤ) ∣ bZ Q z v := by
  have hp0 := p_ne_zero (p := p)
  have e : cv z = (1 / (p : ℚ)) • cv ((p : ℤ) • z) := by
    rw [cv_smul, smul_smul]; push_cast; rw [show 1 / (p : ℚ) * p = 1 by field_simp, one_smul]
  rw [e, mem_nbLat_iff hv]
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  constructor
  · rintro ⟨-, h⟩
    rw [bZ_smul_left, sq] at h
    exact (mul_dvd_mul_iff_left hpZ).mp h
  · intro h
    refine ⟨⟨0, z, by simp⟩, ?_⟩
    rw [bZ_smul_left, sq]
    exact mul_dvd_mul_left _ h

/-- **$L(\vec{v})$ depends only on the line $\mathbb{F}_p\bar{\vec{v}}$:** if $p^2 \mid Q(\vec{v}), Q(\vec{w})$ and $\bar{\vec{w}} = c\bar{\vec{v}}$ with
$c \ne 0$, then $L(\vec{w}) = L(\vec{v})$. -/
theorem nbLat_eq_of_line {v w : Fin n → ℤ} (hv : (p : ℤ) ^ 2 ∣ Q.eval v) (hw : (p : ℤ) ^ 2 ∣ Q.eval w)
    {c : ZMod p} (hc : c ≠ 0) (hwv : red p w = c • red p v) : nbLat Q p w = nbLat Q p v := by
  have hp0 := p_ne_zero (p := p)
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := exists_eq_of_mem_nbLat hx
    have hint := nbLat_integral hw _ hx
    obtain ⟨m, hm⟩ := hint
    have hy : Q.eval y = (p : ℤ) ^ 2 * m := by
      rw [evalIn_smulQ, evalIn_cv] at hm
      have : (Q.eval y : ℚ) = (p : ℚ) ^ 2 * m := by field_simp at hm; linear_combination hm
      exact_mod_cast this
    have hy2 : (p : ℤ) ^ 2 ∣ Q.eval y := ⟨m, hy⟩
    by_cases hy0 : red p y = 0
    · obtain ⟨z, rfl⟩ : ∃ z, y = (p : ℤ) • z := by
        refine ⟨fun i => y i / p, ?_⟩
        ext i; simp only [Pi.smul_apply, smul_eq_mul]
        rw [Int.mul_ediv_cancel' ((red_eq_zero_iff y).mp hy0 i)]
      have e : (1 / (p : ℚ)) • cv ((p : ℤ) • z) = cv z := by
        rw [cv_smul, smul_smul]; push_cast; rw [show 1 / (p : ℚ) * p = 1 by field_simp, one_smul]
      rw [e] at hx ⊢
      rw [cv_mem_nbLat_iff hw] at hx
      rw [cv_mem_nbLat_iff hv, ← dvd_of_red, ← bv_red, ← mul_eq_zero_iff_left hc, ← bv_smul_right,
        ← hwv, bv_red, dvd_of_red]
      exact hx
    · rw [mem_nbLat_iff_of_red_ne_zero hw hy2 hy0] at hx
      rw [mem_nbLat_iff_of_red_ne_zero hv hy2 hy0]
      obtain ⟨d, hd⟩ := hx
      exact ⟨d * c, by rw [hd, hwv, smul_smul]⟩
  · intro hx
    obtain ⟨y, rfl⟩ := exists_eq_of_mem_nbLat hx
    have hint := nbLat_integral hv _ hx
    obtain ⟨m, hm⟩ := hint
    have hy : Q.eval y = (p : ℤ) ^ 2 * m := by
      rw [evalIn_smulQ, evalIn_cv] at hm
      have : (Q.eval y : ℚ) = (p : ℚ) ^ 2 * m := by field_simp at hm; linear_combination hm
      exact_mod_cast this
    have hy2 : (p : ℤ) ^ 2 ∣ Q.eval y := ⟨m, hy⟩
    have hvw : red p v = c⁻¹ • red p w := by rw [hwv, smul_smul, inv_mul_cancel₀ hc, one_smul]
    by_cases hy0 : red p y = 0
    · obtain ⟨z, rfl⟩ : ∃ z, y = (p : ℤ) • z := by
        refine ⟨fun i => y i / p, ?_⟩
        ext i; simp only [Pi.smul_apply, smul_eq_mul]
        rw [Int.mul_ediv_cancel' ((red_eq_zero_iff y).mp hy0 i)]
      have e : (1 / (p : ℚ)) • cv ((p : ℤ) • z) = cv z := by
        rw [cv_smul, smul_smul]; push_cast; rw [show 1 / (p : ℚ) * p = 1 by field_simp, one_smul]
      rw [e] at hx ⊢
      rw [cv_mem_nbLat_iff hv] at hx
      rw [cv_mem_nbLat_iff hw, ← dvd_of_red, ← bv_red, hwv, bv_smul_right, bv_red,
        (dvd_of_red _).mpr hx, mul_zero]
    · rw [mem_nbLat_iff_of_red_ne_zero hv hy2 hy0] at hx
      rw [mem_nbLat_iff_of_red_ne_zero hw hy2 hy0]
      obtain ⟨d, hd⟩ := hx
      exact ⟨d * c⁻¹, by rw [hd, hvw, smul_smul]⟩

/-- **Different lines give different neighbours:** if $L(\vec{w}) = L(\vec{v})$ (with $p^2 \mid Q(\vec{v}), Q(\vec{w})$ and
$\bar{\vec{w}} \ne 0$) then $\bar{\vec{w}} \in \mathbb{F}_p\bar{\vec{v}}$ (as $\frac1p\vec{w} \in L(\vec{w})$). -/
theorem line_eq_of_nbLat_eq {v w : Fin n → ℤ} (hv : (p : ℤ) ^ 2 ∣ Q.eval v) (hw : (p : ℤ) ^ 2 ∣ Q.eval w)
    (hw0 : red p w ≠ 0) (h : nbLat Q p w = nbLat Q p v) : ∃ c : ZMod p, red p w = c • red p v := by
  have hmem : (1 / (p : ℚ)) • cv w ∈ nbLat Q p w := by
    rw [mem_nbLat_iff hw]
    refine ⟨⟨1, 0, by simp⟩, ?_⟩
    rw [bZ_self]; obtain ⟨d, hd⟩ := hw; exact ⟨2 * d, by rw [hd]; ring⟩
  rw [h, mem_nbLat_iff_of_red_ne_zero hv hw hw0] at hmem
  exact hmem

/-! ### Indices -/

/-- **An index computed by a surjection onto $\mathbb{Z}/p$:** if $f : K \to \mathbb{Z}/p$ is a surjective homomorphism
whose kernel is $H \cap K$, then $[K : H \cap K] = p$. -/
theorem relIndex_eq_of_hom {G : Type*} [AddCommGroup G] (H K : AddSubgroup G) (f : K →+ ZMod p)
    (hf : Function.Surjective f) (hker : ∀ x : K, f x = 0 ↔ (x : G) ∈ H) : H.relIndex K = p := by
  have e : H.addSubgroupOf K = f.ker := by
    ext x; rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker, hker]
  rw [AddSubgroup.relIndex, e, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf,
    AddSubgroup.card_top, Nat.card_zmod]

/-- The integer vector of an integral rational vector (coordinatewise numerator). -/
def intPart (x : Fin n → ℚ) : Fin n → ℤ := fun i => (x i).num

@[simp] theorem intPart_cv (y : Fin n → ℤ) : intPart (cv y) = y := by
  ext i; simp [intPart, Rat.num_intCast]

theorem cv_intPart {x : Fin n → ℚ} (hx : x ∈ stdLat n) : cv (intPart x) = x := by
  obtain ⟨y, rfl⟩ := hx; simp

/-- **$\vec{v} \not\equiv 0$ has a vector with $B(\vec{z}, \vec{v}) \equiv 1 \pmod p$** ($p \nmid \det H$). -/
theorem exists_bZ_eq_one (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) {v : Fin n → ℤ} (hv0 : red p v ≠ 0) :
    ∃ z : Fin n → ℤ, (bZ Q z v : ZMod p) = 1 := by
  have hc := card_bv_eq hdet hv0 1
  obtain ⟨y, hy⟩ : ∃ y, bv Q p (red p v) y = 1 := by
    by_contra h
    push Not at h
    have : (Finset.univ.filter fun y => bv Q p (red p v) y = 1) = ∅ :=
      Finset.filter_false_of_mem fun y _ => h y
    rw [this, Finset.card_empty] at hc
    exact (pow_ne_zero _ hp.out.ne_zero) hc.symm
  refine ⟨fun i => ((y i).val : ℤ), ?_⟩
  have hred : red p (fun i => ((y i).val : ℤ)) = y := by ext i; simp [red]
  rw [← bv_red, hred, bv_comm, hy]

/-- $L(\vec{v}) \cap \mathbb{Z}^n = L_{\vec{v}}$. -/
theorem mem_nbLat_inf_std {v : Fin n → ℤ} (hv : (p : ℤ) ^ 2 ∣ Q.eval v) {x : Fin n → ℚ} :
    x ∈ nbLat Q p v ∧ x ∈ stdLat n ↔ ∃ z, x = cv z ∧ (p : ℤ) ∣ bZ Q z v := by
  constructor
  · rintro ⟨h1, z, rfl⟩
    exact ⟨z, rfl, (cv_mem_nbLat_iff hv z).mp h1⟩
  · rintro ⟨z, rfl, hz⟩
    exact ⟨(cv_mem_nbLat_iff hv z).mpr hz, z, rfl⟩

/-- $[\mathbb{Z}^n : \mathbb{Z}^n \cap L(\vec{v})] = p$: the kernel of $\vec{z} \mapsto B(\vec{z}, \vec{v}) \bmod p$, which is onto. -/
theorem relIndex_nbLat_std (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) {v : Fin n → ℤ}
    (hv : (p : ℤ) ^ 2 ∣ Q.eval v) (hv0 : red p v ≠ 0) :
    (nbLat Q p v).toAddSubgroup.relIndex (stdLat n).toAddSubgroup = p := by
  let f : (stdLat n).toAddSubgroup →+ ZMod p :=
    { toFun := fun x => (bZ Q (intPart (x : Fin n → ℚ)) v : ZMod p)
      map_zero' := by
        have : intPart (0 : Fin n → ℚ) = 0 := by ext i; simp [intPart]
        simp [this, bZ]
      map_add' := by
        rintro ⟨_, y, rfl⟩ ⟨_, z, rfl⟩
        simp only [AddSubgroup.coe_add]
        rw [← cv_add, intPart_cv, intPart_cv, intPart_cv, bZ_add_left]; push_cast; ring }
  refine relIndex_eq_of_hom _ _ f ?_ ?_
  · obtain ⟨z, hz⟩ := exists_bZ_eq_one hdet hv0
    intro t
    refine ⟨⟨cv ((t.val : ℤ) • z), _, rfl⟩, ?_⟩
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, intPart_cv, bZ_smul_left]
    push_cast; rw [hz, mul_one]; simp
  · rintro ⟨_, y, rfl⟩
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, intPart_cv, Submodule.mem_toAddSubgroup]
    rw [dvd_of_red, cv_mem_nbLat_iff hv]

/-- $[L(\vec{v}) : \mathbb{Z}^n \cap L(\vec{v})] = p$: the kernel of $\frac1p\vec{y} \mapsto y_{i_0}v_{i_0}^{-1} \bmod p$ ($p \nmid v_{i_0}$). -/
theorem relIndex_std_nbLat {v : Fin n → ℤ} (hv : (p : ℤ) ^ 2 ∣ Q.eval v) (hv0 : red p v ≠ 0) :
    (stdLat n).toAddSubgroup.relIndex (nbLat Q p v).toAddSubgroup = p := by
  have hp0 := p_ne_zero (p := p)
  obtain ⟨i0, hi0⟩ : ∃ i, red p v i ≠ 0 := by
    by_contra h; push Not at h; exact hv0 (funext h)
  have hpx : ∀ x ∈ nbLat Q p v, (p : ℚ) • x ∈ stdLat n := by
    intro x hx
    obtain ⟨y, rfl⟩ := exists_eq_of_mem_nbLat hx
    refine ⟨y, ?_⟩
    rw [smul_smul, show (p : ℚ) * (1 / p) = 1 by field_simp, one_smul]
  let f : (nbLat Q p v).toAddSubgroup →+ ZMod p :=
    { toFun := fun x => (intPart ((p : ℚ) • (x : Fin n → ℚ)) i0 : ZMod p) * (red p v i0)⁻¹
      map_zero' := by simp [intPart]
      map_add' := by
        rintro ⟨x, hx⟩ ⟨x', hx'⟩
        simp only [AddSubgroup.coe_add]
        obtain ⟨y, hy⟩ := hpx x hx
        obtain ⟨y', hy'⟩ := hpx x' hx'
        rw [smul_add, hy, hy', ← cv_add, intPart_cv, intPart_cv, intPart_cv]
        simp only [Pi.add_apply]; push_cast; ring }
  have key : ∀ y : Fin n → ℤ, (1 / (p : ℚ)) • cv y ∈ nbLat Q p v →
      intPart ((p : ℚ) • ((1 / (p : ℚ)) • cv y)) = y := by
    intro y _
    rw [smul_smul, show (p : ℚ) * (1 / p) = 1 by field_simp, one_smul, intPart_cv]
  refine relIndex_eq_of_hom _ _ f ?_ ?_
  · have hmem : (1 / (p : ℚ)) • cv v ∈ nbLat Q p v := by
      rw [mem_nbLat_iff hv]
      refine ⟨⟨1, 0, by simp⟩, ?_⟩
      rw [bZ_self]; obtain ⟨d, hd⟩ := hv; exact ⟨2 * d, by rw [hd]; ring⟩
    intro t
    refine ⟨(t.val : ℤ) • ⟨_, hmem⟩, ?_⟩
    rw [map_zsmul]
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [key v hmem]
    change (t.val : ℤ) • ((v i0 : ZMod p) * (red p v i0)⁻¹) = t
    rw [show (v i0 : ZMod p) = red p v i0 from rfl, mul_inv_cancel₀ hi0, zsmul_eq_mul, mul_one]
    simp
  · rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := exists_eq_of_mem_nbLat hx
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Submodule.mem_toAddSubgroup]
    rw [key y hx]
    have hx' : (1 / (p : ℚ)) • cv y ∈ nbLat Q p v := hx
    rw [mem_nbLat_iff hv, exists_congr_iff] at hx'
    obtain ⟨⟨c, hc⟩, -⟩ := hx'
    have hyi : (y i0 : ZMod p) = c * red p v i0 := by
      have := congrFun hc i0; simpa [red] using this
    rw [hyi, mul_assoc, mul_inv_cancel₀ hi0, mul_one]
    constructor
    · intro hc0
      have hy0 : red p y = 0 := by rw [hc, hc0, zero_smul]
      refine ⟨fun i => y i / p, ?_⟩
      ext i
      have hd := (red_eq_zero_iff y).mp hy0 i
      simp only [Pi.smul_apply, smul_eq_mul, cv_apply]
      rw [Int.cast_div hd (by exact_mod_cast hp.out.ne_zero)]
      push_cast; ring
    · rintro ⟨w, hw⟩
      have hy : y = (p : ℤ) • w := by
        apply cv_injective
        rw [cv_smul, ← hw, smul_smul]; push_cast
        rw [show (p : ℚ) * (1 / p) = 1 by field_simp, one_smul]
      have : red p y = 0 := by rw [hy, red_smul]; simp
      rw [hc] at this
      by_contra hc0
      exact hv0 (by
        have := congrArg (fun u => c⁻¹ • u) this
        simpa [smul_smul, inv_mul_cancel₀ hc0] using this)

/-- **$L(\vec{v})$ is a $p$-neighbour of $\mathbb{Z}^n$** (AWS notes, §1.10.1, proof of Thm. 1.10.2, "by reversing our
reasoning"): for $p \nmid \det H$, $\vec{v} \not\equiv 0 \pmod p$ and $p^2 \mid Q(\vec{v})$. -/
@[kb "hanke2011aws" "§1.10.1, Thm. 1.10.2, p. 22"]
theorem isNeighbor_nbLat (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) {v : Fin n → ℤ}
    (hv : (p : ℤ) ^ 2 ∣ Q.eval v) (hv0 : red p v ≠ 0) : IsNeighbor Q p (nbLat Q p v) :=
  ⟨relIndex_nbLat_std hdet hv hv0, relIndex_std_nbLat hv hv0, nbLat_integral hv⟩

/-- **Every $p$-neighbour is explicit** (AWS notes, §1.10.1, Thm. 1.10.2, p. 22): if $p \nmid \det H$ and $L'$ is a
$p$-neighbour of $\mathbb{Z}^n$, then $L' = L(\vec{v})$ for some $\vec{v} \in \mathbb{Z}^n$ with $\vec{v} \not\equiv 0 \pmod p$ and
$p^2 \mid Q(\vec{v})$ (namely $\vec{v} = p\vec{w}$ for any $\vec{w} \in L' \setminus \mathbb{Z}^n$).

*Proof.* $[L' : L \cap L'] = p$ gives $p\vec{w} \in L$; integrality of $Q$ on $L'$ gives $p^2 \mid Q(\vec{v})$ and
$L \cap L' \subseteq L_{\vec{v}}$, with equality since both have index $p$ in $L$; then $L(\vec{v}) \subseteq L'$, with equality since both
contain $L_{\vec{v}}$ with index $p$. (The notes' appeal to the elementary divisor theorem is not needed.) -/
@[kb "hanke2011aws" "§1.10.1, Thm. 1.10.2, p. 22"]
theorem exists_eq_nbLat (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) {L : Submodule ℤ (Fin n → ℚ)}
    (hL : IsNeighbor Q p L) : ∃ v : Fin n → ℤ, (p : ℤ) ^ 2 ∣ Q.eval v ∧ red p v ≠ 0 ∧ L = nbLat Q p v := by
  have hp0 := p_ne_zero (p := p)
  have hp1 : p ≠ 1 := hp.out.one_lt.ne'
  set S := (stdLat n).toAddSubgroup
  set LA := L.toAddSubgroup
  -- a vector of L outside ℤⁿ
  obtain ⟨w, hwL, hwS⟩ : ∃ w ∈ L, w ∉ stdLat n := by
    by_contra h
    push Not at h
    have : S.relIndex LA = 1 := AddSubgroup.relIndex_eq_one.mpr fun x hx => h x hx
    exact hp1 (hL.relIndex_self.symm.trans this)
  -- p • w ∈ ℤⁿ
  have hpw : (p : ℚ) • w ∈ stdLat n := by
    have := AddSubgroup.nsmul_index_mem (S.addSubgroupOf LA) (⟨w, hwL⟩ : LA)
    rw [← AddSubgroup.relIndex, hL.relIndex_self, AddSubgroup.mem_addSubgroupOf] at this
    have h2 : p • w ∈ stdLat n := this
    rwa [← Nat.cast_smul_eq_nsmul ℚ] at h2
  obtain ⟨v, hv⟩ := hpw
  have hw : w = (1 / (p : ℚ)) • cv v := by
    rw [← hv, smul_smul, show 1 / (p : ℚ) * p = 1 by field_simp, one_smul]
  obtain ⟨m, hm⟩ := hL.integral w hwL
  have hQv : Q.eval v = (p : ℤ) ^ 2 * m := by
    have h := hm
    rw [hw, evalIn_smulQ, evalIn_cv] at h
    have : (Q.eval v : ℚ) = (p : ℚ) ^ 2 * m := by field_simp at h; linear_combination h
    exact_mod_cast this
  have hv2 : (p : ℤ) ^ 2 ∣ Q.eval v := ⟨m, hQv⟩
  have hv0 : red p v ≠ 0 := by
    intro h0
    apply hwS
    refine ⟨fun i => v i / p, ?_⟩
    rw [hw]; ext i
    have hd := (red_eq_zero_iff v).mp h0 i
    simp only [Pi.smul_apply, smul_eq_mul, cv_apply]
    rw [Int.cast_div hd (by exact_mod_cast hp.out.ne_zero)]
    push_cast; ring
  refine ⟨v, hv2, hv0, ?_⟩
  set N := nbLat Q p v
  set NA := N.toAddSubgroup
  -- L ∩ ℤⁿ ⊆ L_v
  have hsub : LA ⊓ S ≤ NA ⊓ S := by
    rintro x ⟨hxL, z, rfl⟩
    refine ⟨?_, z, rfl⟩
    change cv z ∈ N
    rw [cv_mem_nbLat_iff hv2]
    obtain ⟨a, ha⟩ := hL.integral _ (L.add_mem hxL hwL)
    obtain ⟨b, hb⟩ := hL.integral _ hxL
    have hpol := evalIn_add_smulQ Q (cv z) w 1
    rw [one_smul, one_mul, one_pow, one_mul, ha, hb, hm] at hpol
    have hB : bQ Q (cv z) (cv v) = p * (a - b - m) := by
      rw [← hv, bQ_smul_right]; linear_combination (-(p : ℚ)) * hpol
    rw [bQ_cv] at hB
    exact ⟨a - b - m, by exact_mod_cast hB⟩
  -- equality of L ∩ ℤⁿ and L_v by indices
  have hNstd := relIndex_nbLat_std hdet hv2 hv0
  have hstdN := relIndex_std_nbLat (Q := Q) hv2 hv0
  have hsub' : NA ⊓ S ≤ LA ⊓ S := by
    have h1 := AddSubgroup.relIndex_mul_relIndex (LA ⊓ S) (NA ⊓ S) S hsub inf_le_right
    rw [AddSubgroup.inf_relIndex_right, AddSubgroup.inf_relIndex_right, hNstd, hL.relIndex_std] at h1
    have : (LA ⊓ S).relIndex (NA ⊓ S) = 1 := by
      have hp0' : 0 < p := hp.out.pos
      exact (Nat.mul_eq_right hp0'.ne').mp h1
    exact AddSubgroup.relIndex_eq_one.mp this |>.trans inf_le_left |> fun h => le_inf h inf_le_right
  -- N ≤ L
  have hNL : NA ≤ LA := by
    rintro _ ⟨z, k, hz, rfl⟩
    have hzL : cv z ∈ L := (hsub' ⟨(cv_mem_nbLat_iff hv2 z).mpr hz, z, rfl⟩).1
    have : ((k : ℚ) / p) • cv v = k • w := by
      rw [hw, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]; congr 1; field_simp
    change cv z + ((k : ℚ) / p) • cv v ∈ L
    rw [this]
    exact L.add_mem hzL (L.smul_of_tower_mem k hwL)
  -- L ≤ N by indices
  have hLN : LA ≤ NA := by
    have h1 := AddSubgroup.relIndex_mul_relIndex (S ⊓ NA) NA LA inf_le_right hNL
    have e : S ⊓ NA = S ⊓ LA := by
      rw [inf_comm, inf_comm S LA]; exact le_antisymm hsub' hsub
    rw [AddSubgroup.inf_relIndex_right, hstdN, e, AddSubgroup.inf_relIndex_right, hL.relIndex_self] at h1
    have : NA.relIndex LA = 1 := (Nat.mul_eq_left hp.out.pos.ne').mp h1
    exact AddSubgroup.relIndex_eq_one.mp this
  exact le_antisymm (fun x hx => hLN hx) (fun x hx => hNL hx)

/-- **Lifting isotropic vectors** ($p \nmid \det H$): every $\bar{\vec{v}} \in \mathbb{F}_p^n \setminus 0$ with $\bar Q(\bar{\vec{v}}) = 0$ has a lift
$\vec{v} \in \mathbb{Z}^n$ with $p^2 \mid Q(\vec{v})$ (correct an arbitrary lift by $p\vec{w}$, using that $B(\vec{v}, \cdot)$ is onto mod $p$). -/
theorem exists_lift (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) {vb : Fin n → ZMod p} (hv0 : vb ≠ 0)
    (hq : qv Q p vb = 0) : ∃ v : Fin n → ℤ, red p v = vb ∧ (p : ℤ) ^ 2 ∣ Q.eval v := by
  set v0 : Fin n → ℤ := fun i => ((vb i).val : ℤ)
  have hred : red p v0 = vb := by ext i; simp [red, v0]
  have hq0 : (p : ℤ) ∣ Q.eval v0 := by rw [← dvd_of_red, ← qv_red, hred, hq]
  obtain ⟨q, hq'⟩ := hq0
  obtain ⟨z, hz⟩ := exists_bZ_eq_one hdet (Q := Q) (by rw [hred]; exact hv0)
  refine ⟨v0 + (p : ℤ) • ((-q) • z), ?_, ?_⟩
  · rw [red_add, red_smul]; simp [hred]
  · rw [eval_add_smulZ, hq', bZ_comm, bZ_smul_left]
    have : (p : ℤ) ∣ q + (-q) * bZ Q z v0 := by
      rw [← dvd_of_red]; push_cast; rw [hz]; ring
    obtain ⟨c, hc⟩ := this
    refine ⟨c + q ^ 2 * Q.eval z, ?_⟩
    have e : Q.eval ((-q) • z) = q ^ 2 * Q.eval z := by
      have := eval_add_smulZ Q 0 z (-q)
      simpa [bZ, QuadForm.evalIn] using this
    rw [e]
    linear_combination (p : ℤ) * hc

end Lattice

/-! ### The neighbours as a finite set, indexed by isotropic lines (AWS Thm. 1.10.4) -/

section Count

variable {Q : QuadForm ℤ n} {p : ℕ} [hp : Fact p.Prime]

/-- **The nonzero isotropic vectors of $L/pL$:** $\{\bar{\vec{v}} \in \mathbb{F}_p^n : \bar{\vec{v}} \ne 0,\ \bar Q(\bar{\vec{v}}) = 0\}$. -/
def isoSet (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] : Finset (Fin n → ZMod p) :=
  Finset.univ.filter fun y => y ≠ 0 ∧ qv Q p y = 0

open Classical in
/-- A lift $\vec{v} \in \mathbb{Z}^n$ of $\bar{\vec{v}}$ with $p^2 \mid Q(\vec{v})$ (`exists_lift`; junk $0$ if there is none). -/
noncomputable def liftV (Q : QuadForm ℤ n) (p : ℕ) (vb : Fin n → ZMod p) : Fin n → ℤ :=
  if h : ∃ v : Fin n → ℤ, red p v = vb ∧ (p : ℤ) ^ 2 ∣ Q.eval v then h.choose else 0

/-- **The neighbour of an isotropic line:** $L(\bar{\vec{v}}) = L(\vec{v})$ for a lift $\vec{v}$ with $p^2 \mid Q(\vec{v})$
(independent of the lift and of the point on the line, `nbLat_eq_of_line`). -/
noncomputable def nbOf (Q : QuadForm ℤ n) (p : ℕ) (vb : Fin n → ZMod p) : Submodule ℤ (Fin n → ℚ) :=
  nbLat Q p (liftV Q p vb)

open Classical in
/-- **The $p$-neighbours of $\mathbb{Z}^n$** as a finite set (`mem_neighbors_iff`): the image of `isoSet` under `nbOf`. -/
noncomputable def neighbors (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] : Finset (Submodule ℤ (Fin n → ℚ)) :=
  (isoSet Q p).image (nbOf Q p)

theorem mem_isoSet {vb : Fin n → ZMod p} : vb ∈ isoSet Q p ↔ vb ≠ 0 ∧ qv Q p vb = 0 := by
  simp [isoSet]

theorem liftV_spec (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) {vb : Fin n → ZMod p} (hvb : vb ∈ isoSet Q p) :
    red p (liftV Q p vb) = vb ∧ (p : ℤ) ^ 2 ∣ Q.eval (liftV Q p vb) := by
  rw [mem_isoSet] at hvb
  have h := exists_lift hdet hvb.1 hvb.2 (Q := Q)
  unfold liftV
  rw [dif_pos h]
  exact h.choose_spec

theorem nbOf_eq_nbLat (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) {v : Fin n → ℤ} (hv : (p : ℤ) ^ 2 ∣ Q.eval v)
    (hv0 : red p v ≠ 0) : nbOf Q p (red p v) = nbLat Q p v := by
  have hmem : red p v ∈ isoSet Q p := by
    rw [mem_isoSet, qv_red, dvd_of_red]
    exact ⟨hv0, (dvd_pow_self _ two_ne_zero).trans hv⟩
  obtain ⟨h1, h2⟩ := liftV_spec hdet hmem
  exact nbLat_eq_of_line hv h2 one_ne_zero (by rw [h1, one_smul])

/-- **The $p$-neighbours of $\mathbb{Z}^n$** ($p \nmid \det H$): `neighbors Q p` is exactly the set of $p$-neighbours. -/
theorem mem_neighbors_iff (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) {L : Submodule ℤ (Fin n → ℚ)} :
    L ∈ neighbors Q p ↔ IsNeighbor Q p L := by
  classical
  unfold neighbors
  rw [Finset.mem_image]
  constructor
  · rintro ⟨vb, hvb, rfl⟩
    obtain ⟨h1, h2⟩ := liftV_spec hdet hvb
    exact isNeighbor_nbLat hdet h2 (by rw [h1]; exact (mem_isoSet.mp hvb).1)
  · intro hL
    obtain ⟨v, hv, hv0, rfl⟩ := exists_eq_nbLat hdet hL
    refine ⟨red p v, ?_, nbOf_eq_nbLat hdet hv hv0⟩
    rw [mem_isoSet, qv_red, dvd_of_red]
    exact ⟨hv0, (dvd_pow_self _ two_ne_zero).trans hv⟩

/-- **Same neighbour iff same line:** for $\bar{\vec{v}}, \bar{\vec{w}} \in$ `isoSet`, $L(\bar{\vec{w}}) = L(\bar{\vec{v}})$ iff
$\bar{\vec{w}} = c\bar{\vec{v}}$ for some $c \in \mathbb{F}_p$ (necessarily $c \ne 0$). -/
theorem nbOf_eq_iff (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) {vb wb : Fin n → ZMod p} (hv : vb ∈ isoSet Q p)
    (hw : wb ∈ isoSet Q p) : nbOf Q p wb = nbOf Q p vb ↔ ∃ c : ZMod p, wb = c • vb := by
  obtain ⟨hv1, hv2⟩ := liftV_spec hdet hv
  obtain ⟨hw1, hw2⟩ := liftV_spec hdet hw
  constructor
  · intro h
    have := line_eq_of_nbLat_eq hv2 hw2 (by rw [hw1]; exact (mem_isoSet.mp hw).1) h
    rwa [hw1, hv1] at this
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl; exact (mem_isoSet.mp hw).1 (by rw [hc, zero_smul])
    exact nbLat_eq_of_line hv2 hw2 hc0 (by rw [hw1, hv1, hc])

/-- **The points of a line:** for $\vec{u} \ne 0$, $\#\{\vec{w} \ne 0 : \vec{w} \in \mathbb{F}_p\vec{u}\} = p - 1$. -/
theorem card_line {u : Fin n → ZMod p} (hu : u ≠ 0) :
    (Finset.univ.filter fun w : Fin n → ZMod p => w ≠ 0 ∧ ∃ c : ZMod p, w = c • u).card = p - 1 := by
  classical
  have e : (Finset.univ.filter fun w : Fin n → ZMod p => w ≠ 0 ∧ ∃ c : ZMod p, w = c • u) =
      (Finset.univ.erase (0 : ZMod p)).image (fun c => c • u) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨hw, c, rfl⟩
      exact ⟨c, ⟨fun h => hw (by rw [h, zero_smul]), trivial⟩, rfl⟩
    · rintro ⟨c, ⟨hc, -⟩, rfl⟩
      exact ⟨smul_ne_zero hc hu, c, rfl⟩
  rw [e, Finset.card_image_of_injOn, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ZMod.card]
  intro c _ d _ h
  exact smul_left_injective _ hu h

/-- **Each neighbour comes from $p - 1$ isotropic vectors** (the nonzero points of its line). -/
theorem card_fibre_nbOf (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) {vb : Fin n → ZMod p} (hv : vb ∈ isoSet Q p) :
    ((isoSet Q p).filter fun wb => nbOf Q p wb = nbOf Q p vb).card = p - 1 := by
  rw [← card_line (mem_isoSet.mp hv).1]
  congr 1
  ext wb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hw, h⟩
    exact ⟨(mem_isoSet.mp hw).1, (nbOf_eq_iff hdet hv hw).mp h⟩
  · rintro ⟨hw0, c, rfl⟩
    have hw : c • vb ∈ isoSet Q p := by
      rw [mem_isoSet, qv_smul, (mem_isoSet.mp hv).2, mul_zero]; exact ⟨hw0, rfl⟩
    exact ⟨hw, (nbOf_eq_iff hdet hv hw).mpr ⟨c, rfl⟩⟩

/-- **Sums over neighbours as sums over isotropic vectors:** $(p-1)\sum_{L'} f(L') = \sum_{\bar{\vec{v}}} f(L(\bar{\vec{v}}))$, the
sum over the $p$-neighbours $L'$ of $\mathbb{Z}^n$ and over the nonzero isotropic $\bar{\vec{v}} \in \mathbb{F}_p^n$. -/
theorem sum_neighbors (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) {M : Type*} [AddCommMonoid M]
    (f : Submodule ℤ (Fin n → ℚ) → M) :
    (p - 1) • ∑ L ∈ neighbors Q p, f L = ∑ vb ∈ isoSet Q p, f (nbOf Q p vb) := by
  classical
  unfold neighbors
  rw [Finset.smul_sum]
  refine Finset.sum_image' _ fun vb hv => ?_
  rw [Finset.sum_congr rfl fun wb hw => by rw [(Finset.mem_filter.mp hw).2], Finset.sum_const,
    card_fibre_nbOf hdet hv]

/-- **The number of $p$-neighbours** (AWS Thm. 1.10.4, p. 23): $(p - 1)\cdot\#\{L'\} = \#\{\bar{\vec{v}} \ne 0 : \bar Q(\bar{\vec{v}}) = 0\}$,
i.e. the neighbours correspond to the isotropic lines of $\mathbb{F}_p^n$. -/
@[kb "hanke2011aws" "Thm. 1.10.4, p. 23"]
theorem card_neighbors (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) :
    (p - 1) * (neighbors Q p).card = (isoSet Q p).card := by
  have := sum_neighbors hdet (Q := Q) (fun _ => (1 : ℕ))
  simpa using this

theorem card_isoSet : (isoSet Q p).card + 1 = (Finset.univ.filter fun y => qv Q p y = 0).card := by
  classical
  have : (Finset.univ.filter fun y => qv Q p y = 0) = insert 0 (isoSet Q p) := by
    ext y; by_cases hy : y = 0 <;> simp [isoSet, hy, qv_zero]
  rw [this, Finset.card_insert_of_notMem (by simp [isoSet])]

/-- **The number of $p$-neighbours for $n = 4$** ($p$ odd, $p \nmid \det H$, $\varepsilon = \left(\frac{\det H}{p}\right)$):
$$\#\{p\text{-neighbours of } \mathbb{Z}^4\} = p^2 + p + 1 + \varepsilon p = \begin{cases} (p+1)^2 & \varepsilon = 1, \\ p^2 + 1 & \varepsilon = -1. \end{cases}$$
*Erratum (AWS notes, p. 23):* the notes say the $p$-neighbour graph is "$p^{n-2}$-regular" for $p \nmid 2\det L$; the
number of $p$-neighbours is the number of isotropic lines, $\frac{p^{n-1}-1}{p-1} + \varepsilon p^{n/2-1}$ for even $n$
($\sim p^{n-2}$, but not equal to it). -/
@[kb "hanke2011aws" "Thm. 1.10.4 and the remark after it, p. 23"]
theorem card_neighbors_four {Q : QuadForm ℤ 4} (hp2 : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) :
    ((neighbors Q p).card : ℤ) = p ^ 2 + p + 1 + legendreSym p Q.hessian.det * p := by
  have h1 := card_neighbors hdet (Q := Q)
  have h2 := card_isoSet (Q := Q) (p := p)
  have h3 := card_qv_zero_four hp2 hdet (Q := Q) (p := p)
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hp0 : ((p : ℤ) - 1) ≠ 0 := by
    have := hp.out.one_lt; omega
  have : ((p : ℤ) - 1) * (neighbors Q p).card = ((p : ℤ) - 1) * (p ^ 2 + p + 1 + legendreSym p Q.hessian.det * p) := by
    have e1 : (((p - 1) * (neighbors Q p).card : ℕ) : ℤ) = ((isoSet Q p).card : ℤ) := by rw [h1]
    push_cast [Nat.cast_sub hp1] at e1
    rw [e1]
    have e2 : (((isoSet Q p).card + 1 : ℕ) : ℤ) = _ := congrArg (fun k : ℕ => (k : ℤ)) h2
    push_cast at e2
    linear_combination e2 + h3
  exact mul_left_cancel₀ hp0 this

end Count

end QuadFormsKB.Siegel.Kneser
