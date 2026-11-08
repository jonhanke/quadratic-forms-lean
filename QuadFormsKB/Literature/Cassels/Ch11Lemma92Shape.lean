/-
# Cassels, Chapter 11, Lemma 9.3 at a nearby vector (case (a) of the proof of Lemma 9.2)

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, Lemma 9.3 and its Corollary (pp. 243–245)
and case (a) of the proof of Lemma 9.2 (p. 246: "In this case $\mathbf u$ is close to $\pi^l\mathbf t$ … there is thus an
element $\sigma$ of $O(\mathbb Z_p^4)$ such that $\mathbf u = \mu\sigma\mathbf t$ … Then $\mathbf u$, $\Gamma_p$ have all the
properties stated in Lemma 9.3 and its Corollary for $\mathbf t$, $\Delta_p$").

**Conventions.** $Q$ is a quaternary form over $\mathbb Z_p$, $B(x, y) = Q(x + y) - Q(x) - Q(y)$ its polar form (`bl`,
Cassels' $f(x, y)$ is $B/2$). A lattice $\Delta$ in the space normal to $t$ is given by a $4 \times 3$ matrix whose columns
$c_0, c_1, c_2$ are a basis; `gramOf Q B` is its form $y \mapsto Q(By)$.

**The shape** (`Shape93 Q t B μ u₁ u₂`): the normal form found in Cassels' proof of Lemma 9.3: $Q(t) = p^\mu u_2$, the
columns of $B$ are normal to $t$ and independent, $Q(c_0), Q(c_1) \equiv 0$ and $B(c_0, c_1) \equiv p^\mu u_1 \pmod{p^{\mu+1}}$,
all other values of $Q$ and $B$ on the columns are divisible by $p^\mu$, and property (ii) of Lemma 9.3 holds.

**Proves.**
* `exists_root_quadratic`: Hensel's lemma for $\alpha + \beta a + p\gamma a^2$ with $\beta$ a unit.
* `Shape93.cor`, `Shape93.prim'`, `Shape93.units`, `Shape93.toData`: the shape gives (i), (ii), (iii) of Lemma 9.3 and
  its Corollary (in the stronger form: every $z \in p^\mu\mathbb Z_p$ is $Q(t + c)$ with $c \in \Delta$).
* `Shape93.smul_unit`, `Shape93.perturb`: the shape is preserved when $t$ is multiplied by a unit, and when $t$ is
  replaced by any $y$ with $Q(y) = Q(t)$ and $y \equiv t \pmod{p^{\mu+2}}$ ($\Delta$ is replaced by its projection to
  $y^\perp$). This replaces Cassels' automorph $\sigma$ (p. 246).
* `exists_shape93`: Cassels' construction (`Ch11L93.core`) gives the shape for every regular isotropic quaternary form.
-/
import QuadFormsKB.Literature.Cassels.Ch11Lemma93

open Matrix QuadFormsKB.Cassels.Ch11L93

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11L92

/-! ### Generic helpers -/

section Generic

variable {R : Type*} [CommRing R]

/-- Helper: the $j$-th column $Be_j$ of a $4 \times 3$ matrix. -/
def col (B : Matrix (Fin 4) (Fin 3) R) (j : Fin 3) : Fin 4 → R := B *ᵥ Pi.single j 1

theorem mulVec_three (B : Matrix (Fin 4) (Fin 3) R) (y : Fin 3 → R) :
    B *ᵥ y = y 0 • col B 0 + y 1 • col B 1 + y 2 • col B 2 := by
  ext i; simp [col, mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply]; ring

theorem eval_add3 (Q : QuadForm R 4) (a b c : Fin 4 → R) :
    Q.eval (a + b + c) = Q.eval a + Q.eval b + Q.eval c + bl Q a b + bl Q a c + bl Q b c := by
  rw [eval_add, eval_add, bl_add_left]; ring

/-- **Expansion of $Q(By)$** in the values of $Q$ and $B$ on the columns. -/
theorem eval_mulVec_three (Q : QuadForm R 4) (B : Matrix (Fin 4) (Fin 3) R) (y : Fin 3 → R) :
    Q.eval (B *ᵥ y) = y 0 ^ 2 * Q.eval (col B 0) + y 1 ^ 2 * Q.eval (col B 1) + y 2 ^ 2 * Q.eval (col B 2) +
      y 0 * y 1 * bl Q (col B 0) (col B 1) + y 0 * y 2 * bl Q (col B 0) (col B 2) +
      y 1 * y 2 * bl Q (col B 1) (col B 2) := by
  rw [mulVec_three, eval_add3, eval_smul, eval_smul, eval_smul, bl_smul_left, bl_smul_left, bl_smul_left,
    bl_smul_right, bl_smul_right, bl_smul_right]
  ring

theorem bl_mulVec_three (Q : QuadForm R 4) (B : Matrix (Fin 4) (Fin 3) R) (x : Fin 4 → R) (y : Fin 3 → R) :
    bl Q x (B *ᵥ y) = y 0 * bl Q x (col B 0) + y 1 * bl Q x (col B 1) + y 2 * bl Q x (col B 2) := by
  rw [mulVec_three, bl_add_right, bl_add_right, bl_smul_right, bl_smul_right, bl_smul_right]

/-- **The form of the lattice spanned by the columns of $B$:** $y \mapsto Q(By)$. Arguments: `Q` the quaternary form,
`B` the $4 \times 3$ matrix. -/
def gramOf (Q : QuadForm R 4) (B : Matrix (Fin 4) (Fin 3) R) : QuadForm R 3 :=
  QuadForm.ofUpper fun i j => if i = j then Q.eval (col B i) else bl Q (col B i) (col B j)

theorem gramOf_eval (Q : QuadForm R 4) (B : Matrix (Fin 4) (Fin 3) R) (y : Fin 3 → R) :
    (gramOf Q B).eval y = Q.eval (B *ᵥ y) := by
  rw [eval_three, eval_mulVec_three]
  simp [gramOf, QuadForm.ofUpper]
  ring

theorem gramOf_coeff (Q : QuadForm R 4) (B : Matrix (Fin 4) (Fin 3) R) (i j : Fin 3) (hij : i ≤ j) :
    (gramOf Q B).coeff i j = if i = j then Q.eval (col B i) else bl Q (col B i) (col B j) := by
  simp [gramOf, QuadForm.ofUpper, hij]

end Generic

variable {p : ℕ} [Fact p.Prime]

/-! ### Hensel's lemma for a quadratic with a unit linear coefficient -/

theorem norm_p_lt_one' : ‖(p : ℤ_[p])‖ < 1 := by
  rw [PadicInt.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

theorem isUnit_add_p_mul {u : ℤ_[p]} (hu : IsUnit u) (x : ℤ_[p]) : IsUnit (u + (p : ℤ_[p]) * x) := by
  rw [PadicInt.isUnit_iff] at hu ⊢
  have h1 : ‖(p : ℤ_[p]) * x‖ < 1 := by
    rw [norm_mul]
    have := PadicInt.norm_le_one x
    have hp : ‖(p : ℤ_[p])‖ < 1 := norm_p_lt_one'
    nlinarith [norm_nonneg x, norm_nonneg (p : ℤ_[p])]
  rw [← hu] at h1
  rw [PadicInt.norm_add_eq_max_of_ne (by linarith), hu, max_eq_left (by linarith)]

/-- **Hensel's lemma for $\alpha + \beta a + p\gamma a^2$** with $\beta$ a unit: there is a root $a \in \mathbb Z_p$. -/
theorem exists_root_quadratic (α β γ : ℤ_[p]) (hβ : IsUnit β) :
    ∃ a : ℤ_[p], α + β * a + (p : ℤ_[p]) * γ * a ^ 2 = 0 := by
  classical
  obtain ⟨βi, hβi⟩ := hβ.exists_right_inv
  set F : Polynomial ℤ_[p] := Polynomial.C ((p : ℤ_[p]) * γ) * Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X +
    Polynomial.C α with hFdef
  set a0 : ℤ_[p] := -α * βi with ha0
  have hF : ∀ z, F.aeval z = α + β * z + (p : ℤ_[p]) * γ * z ^ 2 := by
    intro z; simp [hFdef]; ring
  have hF' : ∀ z, F.derivative.aeval z = β + (p : ℤ_[p]) * (2 * γ * z) := by
    intro z; simp [hFdef, Polynomial.derivative_X_pow]; ring
  have hunit : ‖F.derivative.aeval a0‖ = 1 := by
    rw [hF']; exact PadicInt.isUnit_iff.mp (isUnit_add_p_mul hβ _)
  have hval : F.aeval a0 = (p : ℤ_[p]) * (γ * a0 ^ 2) := by
    rw [hF, ha0]; linear_combination (-α) * hβi
  have hsmall : ‖F.aeval a0‖ < ‖F.derivative.aeval a0‖ ^ 2 := by
    rw [hunit, one_pow, hval, norm_mul]
    have := PadicInt.norm_le_one (γ * a0 ^ 2)
    have hp : ‖(p : ℤ_[p])‖ < 1 := norm_p_lt_one'
    nlinarith [norm_nonneg (γ * a0 ^ 2), norm_nonneg (p : ℤ_[p])]
  obtain ⟨z, hz, -⟩ := hensels_lemma hsmall
  exact ⟨z, by rw [← hF]; exact hz⟩

/-! ### The shape of Lemma 9.3 -/

/-- **The normal form of Cassels' proof of Lemma 9.3** (Ch. 11, pp. 243–245), for the quaternary form `Q` over
$\mathbb Z_p$, the vector `t`, the lattice $\Delta$ with basis the columns $c_0, c_1, c_2$ of `B`, the exponent `μ` and the
units `u₁`, `u₂`. Fields: `hu1`, `hu2` $u_1, u_2$ are units; `ht` $Q(t) = p^\mu u_2$; `orth` $B(t, c_j) = 0$; `indep` the
columns are linearly independent over $\mathbb Q_p$; `q0`, `q1` $p^{\mu+1} \mid Q(c_0), Q(c_1)$; `q2` $p^\mu \mid Q(c_2)$;
`b01` $B(c_0, c_1) \equiv p^\mu u_1 \pmod{p^{\mu+1}}$; `b02`, `b12` $p^\mu \mid B(c_0, c_2), B(c_1, c_2)$; `prim` property (ii) of
Lemma 9.3: if $c \in \Delta$ and $|Q(t + c)|_p < |Q(t)|_p$ then $t + c$ is primitive. -/
structure Shape93 (Q : QuadForm ℤ_[p] 4) (t : Fin 4 → ℤ_[p]) (B : Matrix (Fin 4) (Fin 3) ℤ_[p]) (μ : ℕ)
    (u1 u2 : ℤ_[p]) : Prop where
  hu1 : IsUnit u1
  hu2 : IsUnit u2
  ht : Q.eval t = (p : ℤ_[p]) ^ μ * u2
  orth : ∀ j : Fin 3, bl Q t (col B j) = 0
  indep : LinearIndependent ℚ_[p] (fun j : Fin 3 => fun i : Fin 4 => ((B i j : ℤ_[p]) : ℚ_[p]))
  q0 : (p : ℤ_[p]) ^ (μ + 1) ∣ Q.eval (col B 0)
  q1 : (p : ℤ_[p]) ^ (μ + 1) ∣ Q.eval (col B 1)
  q2 : (p : ℤ_[p]) ^ μ ∣ Q.eval (col B 2)
  b01 : (p : ℤ_[p]) ^ (μ + 1) ∣ bl Q (col B 0) (col B 1) - (p : ℤ_[p]) ^ μ * u1
  b02 : (p : ℤ_[p]) ^ μ ∣ bl Q (col B 0) (col B 2)
  b12 : (p : ℤ_[p]) ^ μ ∣ bl Q (col B 1) (col B 2)
  prim : ∀ y : Fin 3 → ℤ_[p], ‖Q.eval (t + B *ᵥ y)‖ < ‖Q.eval t‖ → ∃ i, IsUnit ((t + B *ᵥ y) i)

namespace Shape93

variable {Q : QuadForm ℤ_[p] 4} {t : Fin 4 → ℤ_[p]} {B : Matrix (Fin 4) (Fin 3) ℤ_[p]} {μ : ℕ} {u1 u2 : ℤ_[p]}

theorem bl_t (S : Shape93 Q t B μ u1 u2) (y : Fin 3 → ℤ_[p]) : bl Q t (B *ᵥ y) = 0 := by
  rw [bl_mulVec_three, S.orth 0, S.orth 1, S.orth 2]; ring

theorem eval_t_add (S : Shape93 Q t B μ u1 u2) (y : Fin 3 → ℤ_[p]) :
    Q.eval (t + B *ᵥ y) = Q.eval t + Q.eval (B *ᵥ y) := by
  rw [eval_add, S.bl_t, add_zero]

theorem p_pow_ne_zero (k : ℕ) : (p : ℤ_[p]) ^ k ≠ 0 :=
  pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

/-- **The values on the line $t + a c_0 + c_1$:** $Q(t + ac_0 + c_1) = p^\mu(u_2 + px_1 + (u_1 + px_{01})a + px_0a^2)$. -/
theorem exists_line (S : Shape93 Q t B μ u1 u2) : ∃ x0 x1 x01 : ℤ_[p], ∀ a : ℤ_[p],
    Q.eval (t + B *ᵥ ![a, 1, 0]) = (p : ℤ_[p]) ^ μ * (u2 + (p : ℤ_[p]) * x1 + (u1 + (p : ℤ_[p]) * x01) * a +
      (p : ℤ_[p]) * x0 * a ^ 2) := by
  obtain ⟨x0, hx0⟩ := S.q0
  obtain ⟨x1, hx1⟩ := S.q1
  obtain ⟨x01, hx01⟩ := S.b01
  refine ⟨x0, x1, x01, fun a => ?_⟩
  rw [S.eval_t_add, S.ht, eval_mulVec_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have e : bl Q (col B 0) (col B 1) = (p : ℤ_[p]) ^ μ * u1 + (p : ℤ_[p]) ^ (μ + 1) * x01 := by
    linear_combination hx01
  rw [hx0, hx1, e]
  ring

/-- **Corollary to Lemma 9.3, from the shape** (Cassels, p. 245): every $z \in p^\mu\mathbb Z_p$ (in particular every $z$ with
$|z|_p < |Q(t)|_p$) is $Q(t + c)$ for some $c \in \Delta$. -/
theorem cor (S : Shape93 Q t B μ u1 u2) (z : ℤ_[p]) (hz : (p : ℤ_[p]) ^ μ ∣ z) :
    ∃ y : Fin 3 → ℤ_[p], Q.eval (t + B *ᵥ y) = z := by
  obtain ⟨x0, x1, x01, hline⟩ := S.exists_line
  obtain ⟨z', rfl⟩ := hz
  obtain ⟨a, ha⟩ := exists_root_quadratic (u2 + (p : ℤ_[p]) * x1 - z') (u1 + (p : ℤ_[p]) * x01) x0
    (isUnit_add_p_mul S.hu1 x01)
  refine ⟨![a, 1, 0], ?_⟩
  rw [hline]
  linear_combination (p : ℤ_[p]) ^ μ * ha

theorem norm_eval_t (S : Shape93 Q t B μ u1 u2) : ‖Q.eval t‖ = ‖((p : ℤ_[p]) ^ μ)‖ := by
  rw [S.ht, norm_mul, PadicInt.isUnit_iff.mp S.hu2, mul_one]

/-- **Property (ii) of Lemma 9.3 in divisibility form:** if $p^{\mu+1} \mid Q(t + c)$, $c \in \Delta$, then $t + c$ is
primitive. -/
theorem prim' (S : Shape93 Q t B μ u1 u2) (y : Fin 3 → ℤ_[p]) (hy : (p : ℤ_[p]) ^ (μ + 1) ∣ Q.eval (t + B *ᵥ y)) :
    ∃ i, IsUnit ((t + B *ᵥ y) i) := by
  refine S.prim y ?_
  rw [S.norm_eval_t]
  obtain ⟨w, hw⟩ := hy
  rw [hw, norm_mul, pow_succ, norm_mul]
  have h1 := PadicInt.norm_le_one w
  have hp : ‖(p : ℤ_[p])‖ < 1 := norm_p_lt_one'
  have hpos : 0 < ‖(p : ℤ_[p]) ^ μ‖ := norm_pos_iff.mpr (p_pow_ne_zero μ)
  have := norm_nonneg w
  nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt (mul_pos hpos (norm_pos_iff.mpr
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℤ_[p]) ≠ 0))))]

end Shape93

/-! ### Norms and divisibility -/

theorem dvd_of_norm_lt_pow {x : ℤ_[p]} {μ : ℕ} (h : ‖x‖ < ‖(p : ℤ_[p]) ^ μ‖) : (p : ℤ_[p]) ^ (μ + 1) ∣ x := by
  rw [PadicInt.norm_p_pow, PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one] at h
  have e : (-(μ : ℤ) - 1) = -((μ + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, PadicInt.norm_le_pow_iff_mem_span_pow] at h
  exact Ideal.mem_span_singleton.mp h

theorem norm_lt_of_dvd_pow {x : ℤ_[p]} {μ : ℕ} (h : (p : ℤ_[p]) ^ (μ + 1) ∣ x) : ‖x‖ < ‖(p : ℤ_[p]) ^ μ‖ := by
  rw [PadicInt.norm_p_pow, PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one]
  have e : (-(μ : ℤ) - 1) = -((μ + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, PadicInt.norm_le_pow_iff_mem_span_pow]
  exact Ideal.mem_span_singleton.mpr h

/-! ### Part (iii) for the general shape -/

/-- **Units in the spinor norm for a ternary form of the shape $p^\mu(u_1y_0y_1 + p(\dots))$, general version** (the
argument of `Ch11L93.units_of_shape`, Cassels p. 244): if every coefficient of $g$ is divisible by $p^\mu$,
$p^{\mu+1} \mid g_{00}, g_{11}$ and $g_{01} \equiv p^\mu u_1 \pmod{p^{\mu+1}}$ with $u_1$ a unit, then every unit is the
spinor norm of a product of two reflections mapping $\mathbb Z_p^3$ onto itself (`UnitsInSpinorNorm`). The two vectors
are $(a, 1, 0)$ with $g(a, 1, 0) = p^\mu$, resp. $p^\mu u$ (Hensel, `exists_root_quadratic`). -/
theorem units_of_gen_shape (μ : ℕ) (g : QuadForm ℤ_[p] 3) {u1 : ℤ_[p]} (hu1 : IsUnit u1)
    (hdiv : ∀ i j, (p : ℤ_[p]) ^ μ ∣ g.coeff i j) (h00 : (p : ℤ_[p]) ^ (μ + 1) ∣ g.coeff 0 0)
    (h11 : (p : ℤ_[p]) ^ (μ + 1) ∣ g.coeff 1 1) (h01 : (p : ℤ_[p]) ^ (μ + 1) ∣ g.coeff 0 1 - (p : ℤ_[p]) ^ μ * u1) :
    UnitsInSpinorNorm p g := by
  choose m hm using hdiv
  obtain ⟨x0, hx0⟩ := h00
  obtain ⟨x1, hx1⟩ := h11
  obtain ⟨x01, hx01⟩ := h01
  have hp0 : (p : ℤ_[p]) ^ μ ≠ 0 := Shape93.p_pow_ne_zero μ
  have hm00 : m 0 0 = (p : ℤ_[p]) * x0 := by
    apply mul_left_cancel₀ hp0; rw [← hm, hx0]; ring
  have hm11 : m 1 1 = (p : ℤ_[p]) * x1 := by
    apply mul_left_cancel₀ hp0; rw [← hm, hx1]; ring
  have hm01 : m 0 1 = u1 + (p : ℤ_[p]) * x01 := by
    apply mul_left_cancel₀ hp0; rw [← hm]; linear_combination hx01
  set G := g.map PadicInt.Coe.ringHom with hGdef
  set π : ℚ_[p] := (p : ℚ_[p]) ^ μ with hπ
  have hπ0 : π ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hG : ∀ v : Fin 3 → ℚ_[p], G.eval v = π * ((m 0 0 : ℚ_[p]) * v 0 * v 0 + (m 0 1 : ℚ_[p]) * v 0 * v 1 +
      (m 0 2 : ℚ_[p]) * v 0 * v 2 + (m 1 1 : ℚ_[p]) * v 1 * v 1 + (m 1 2 : ℚ_[p]) * v 1 * v 2 +
      (m 2 2 : ℚ_[p]) * v 2 * v 2) := by
    intro v
    rw [eval_three]
    simp only [hGdef, QuadForm.map, Matrix.map_apply, hm, PadicInt.Coe.ringHom_apply]
    rw [hπ]; push_cast; ring
  -- reflections in integral vectors with value `π * ε` preserve integrality
  have hrefl : ∀ (ξ : Fin 3 → ℤ_[p]) (ε : ℤ_[p]), IsUnit ε →
      G.eval (fun i => (ξ i : ℚ_[p])) = π * (ε : ℚ_[p]) →
      ∀ z : Fin 3 → ℚ_[p], (∀ i, ‖z i‖ ≤ 1) →
        ∀ i, ‖reflectionBy G (fun i => (ξ i : ℚ_[p])) z i‖ ≤ 1 := by
    intro ξ ε hε hξ z hz
    obtain ⟨εi, hεi⟩ := hε.exists_right_inv
    set ζ : Fin 3 → ℤ_[p] := fun i => ⟨z i, hz i⟩ with hζ
    have hzζ : z = fun i => (ζ i : ℚ_[p]) := rfl
    set Pz : ℤ_[p] := m 0 0 * (2 * ζ 0 * ξ 0) + m 0 1 * (ζ 0 * ξ 1 + ζ 1 * ξ 0) +
      m 0 2 * (ζ 0 * ξ 2 + ζ 2 * ξ 0) + m 1 1 * (2 * ζ 1 * ξ 1) + m 1 2 * (ζ 1 * ξ 2 + ζ 2 * ξ 1) +
      m 2 2 * (2 * ζ 2 * ξ 2) with hPz
    have hεq : (ε : ℚ_[p]) * (εi : ℚ_[p]) = 1 := by rw [← PadicInt.coe_mul, hεi, PadicInt.coe_one]
    have hε0 : (ε : ℚ_[p]) ≠ 0 := left_ne_zero_of_mul_eq_one hεq
    intro i
    have hpol : G.eval (z + fun i => (ξ i : ℚ_[p])) - G.eval z - G.eval (fun i => (ξ i : ℚ_[p])) =
        π * (Pz : ℚ_[p]) := by
      have h2c : ((2 : ℤ_[p]) : ℚ_[p]) = 2 := by
        rw [show (2 : ℤ_[p]) = 1 + 1 by norm_num, PadicInt.coe_add, PadicInt.coe_one]; norm_num
      rw [hG, hG, hG, hzζ]; simp only [Pi.add_apply]; rw [hPz]; push_cast; rw [h2c]; ring
    have hdiv : π * (Pz : ℚ_[p]) / (π * (ε : ℚ_[p])) = (Pz : ℚ_[p]) * (εi : ℚ_[p]) := by
      rw [mul_div_mul_left _ _ hπ0, div_eq_iff hε0]; linear_combination (-(Pz : ℚ_[p])) * hεq
    have key : reflectionBy G (fun i => (ξ i : ℚ_[p])) z i = ((ζ i - Pz * εi * ξ i : ℤ_[p]) : ℚ_[p]) := by
      rw [reflectionBy]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hpol, hξ, hdiv, hzζ]; push_cast; ring
    rw [key]; exact (ζ i - Pz * εi * ξ i).2
  -- the vectors `(a, 1, 0)` with value `π * ε`
  have hline : ∀ ε : ℤ_[p], ∃ a : ℤ_[p], G.eval (fun i => ((![a, 1, 0] : Fin 3 → ℤ_[p]) i : ℚ_[p])) =
      π * (ε : ℚ_[p]) := by
    intro ε
    obtain ⟨a, ha⟩ := exists_root_quadratic (m 1 1 - ε) (m 0 1) x0 (by rw [hm01]; exact isUnit_add_p_mul hu1 x01)
    refine ⟨a, ?_⟩
    rw [hG]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, PadicInt.coe_one, PadicInt.coe_zero]
    have ha' : ((m 1 1 - ε + m 0 1 * a + (p : ℤ_[p]) * x0 * a ^ 2 : ℤ_[p]) : ℚ_[p]) = 0 := by rw [ha]; simp
    rw [hm00]
    push_cast at ha' ⊢
    linear_combination π * ha'
  intro u hu
  obtain ⟨a1, ha1⟩ := hline 1
  obtain ⟨a2, ha2⟩ := hline u
  set ξ1 : Fin 3 → ℤ_[p] := ![a1, 1, 0]
  set ξ2 : Fin 3 → ℤ_[p] := ![a2, 1, 0]
  have hu0 : (u : ℚ_[p]) ≠ 0 := by
    obtain ⟨ui, hui⟩ := hu.exists_right_inv
    have : (u : ℚ_[p]) * (ui : ℚ_[p]) = 1 := by rw [← PadicInt.coe_mul, hui, PadicInt.coe_one]
    exact left_ne_zero_of_mul_eq_one this
  have hn1 : G.eval (fun i => (ξ1 i : ℚ_[p])) ≠ 0 := by rw [ha1]; simpa using hπ0
  have hn2 : G.eval (fun i => (ξ2 i : ℚ_[p])) ≠ 0 := by rw [ha2]; exact mul_ne_zero hπ0 hu0
  have hr1 := hrefl ξ1 1 isUnit_one ha1
  have hr2 := hrefl ξ2 u hu ha2
  refine ⟨[fun i => (ξ1 i : ℚ_[p]), fun i => (ξ2 i : ℚ_[p])], ⟨1, rfl⟩, ?_, ?_, π, hπ0, ?_⟩
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hn1
    · exact hn2
  · intro x
    simp only [rotationBy, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Function.comp_apply,
      id_eq]
    constructor
    · intro hx; exact hr1 _ (hr2 x hx)
    · intro hx
      have h1 := hr1 _ hx
      rw [reflectionBy_invol G hn1] at h1
      have h2 := hr2 _ h1
      rwa [reflectionBy_invol G hn2] at h2
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [ha1, ha2]; push_cast; ring

namespace Shape93

variable {Q : QuadForm ℤ_[p] 4} {t : Fin 4 → ℤ_[p]} {B : Matrix (Fin 4) (Fin 3) ℤ_[p]} {μ : ℕ} {u1 u2 : ℤ_[p]}

/-- **Part (iii) of Lemma 9.3 from the shape.** -/
theorem units (S : Shape93 Q t B μ u1 u2) : UnitsInSpinorNorm p (gramOf Q B) := by
  refine units_of_gen_shape μ (gramOf Q B) S.hu1 ?_ ?_ ?_ ?_
  · intro i j
    by_cases hij : i ≤ j
    · rw [gramOf_coeff Q B i j hij]
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · exact (pow_dvd_pow _ (Nat.le_succ μ)).trans S.q0
      · have h := dvd_add ((pow_dvd_pow _ (Nat.le_succ μ)).trans S.b01) (dvd_mul_right ((p : ℤ_[p]) ^ μ) u1)
        simpa using h
      · exact S.b02
      · exact (pow_dvd_pow _ (Nat.le_succ μ)).trans S.q1
      · exact S.b12
      · exact S.q2
    · rw [(gramOf Q B).upper (lt_of_not_ge hij)]; exact dvd_zero _
  · rw [gramOf_coeff Q B 0 0 le_rfl]; simpa using S.q0
  · rw [gramOf_coeff Q B 1 1 le_rfl]; simpa using S.q1
  · rw [gramOf_coeff Q B 0 1 (by decide)]; simpa using S.b01

/-- **Lemma 9.3 (i)–(iii) from the shape** (`Lemma93Data` for $t$, $B$ and the form `gramOf Q B`). -/
theorem toData (S : Shape93 Q t B μ u1 u2) : Lemma93Data p Q t B (gramOf Q B) where
  ne := by rw [S.ht]; exact mul_ne_zero (p_pow_ne_zero μ) S.hu2.ne_zero
  orth j := by
    have hc : (fun i => B i j) = col B j := by rw [col, mulVec_single_one]; rfl
    rw [hc, eval_add, S.orth j, add_zero]
  indep := S.indep
  gram y := gramOf_eval Q B y
  rep := by
    obtain ⟨y, hy⟩ := S.cor 0 (dvd_zero _)
    refine ⟨y, ?_⟩
    rw [gramOf_eval]
    rw [S.eval_t_add] at hy
    linear_combination hy
  prim := S.prim
  units := S.units

/-- **Multiplying $t$ and $\Delta$ by a unit** $\varepsilon$ preserves the shape (with $u_1, u_2$ multiplied by
$\varepsilon^2$). -/
theorem smul_unit (S : Shape93 Q t B μ u1 u2) {ε : ℤ_[p]} (hε : IsUnit ε) :
    Shape93 Q (ε • t) (ε • B) μ (ε ^ 2 * u1) (ε ^ 2 * u2) := by
  have hcol : ∀ j, col (ε • B) j = ε • col B j := fun j => by rw [col, col, Matrix.smul_mulVec]
  have hbl : ∀ x y : Fin 4 → ℤ_[p], bl Q (ε • x) (ε • y) = ε ^ 2 * bl Q x y := fun x y => by
    rw [bl_smul_left, bl_smul_right]; ring
  refine ⟨(hε.pow 2).mul S.hu1, (hε.pow 2).mul S.hu2, ?_, fun j => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_⟩
  · rw [eval_smul, S.ht]; ring
  · rw [hcol, hbl, S.orth j, mul_zero]
  · have hε' : (ε : ℚ_[p]) ≠ 0 := by
      intro h0; exact hε.ne_zero (by simpa using h0)
    have := S.indep.units_smul (fun _ : Fin 3 => Units.mk0 (ε : ℚ_[p]) hε')
    convert this using 1
    ext j i
    simp [Matrix.smul_apply]
  · rw [hcol, eval_smul]; exact Dvd.dvd.mul_left S.q0 _
  · rw [hcol, eval_smul]; exact Dvd.dvd.mul_left S.q1 _
  · rw [hcol, eval_smul]; exact Dvd.dvd.mul_left S.q2 _
  · rw [hcol, hcol, hbl]
    have := Dvd.dvd.mul_left S.b01 (ε ^ 2)
    convert this using 1; ring
  · rw [hcol, hcol, hbl]; exact Dvd.dvd.mul_left S.b02 _
  · rw [hcol, hcol, hbl]; exact Dvd.dvd.mul_left S.b12 _
  · have e : ε • t + (ε • B) *ᵥ y = ε • (t + B *ᵥ y) := by rw [Matrix.smul_mulVec, smul_add]
    rw [e, eval_smul, eval_smul, norm_mul, norm_mul, PadicInt.isUnit_iff.mp (hε.pow 2), one_mul, one_mul] at hy
    obtain ⟨i, hi⟩ := S.prim y hy
    exact ⟨i, by rw [e, Pi.smul_apply, smul_eq_mul]; exact hε.mul hi⟩

end Shape93

/-- Helper: $2\kappa = p$ for some $\kappa \in \mathbb Z_p$ ($\kappa = 1$ if $p = 2$, $\kappa = p/2$ otherwise). -/
theorem exists_two_mul_eq_p : ∃ κ : ℤ_[p], 2 * κ = (p : ℤ_[p]) := by
  by_cases hp2 : p = 2
  · refine ⟨1, ?_⟩
    subst hp2; norm_num
  · have h2 : IsUnit (2 : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff]
      have h := PadicInt.norm_le_one (2 : ℤ_[p])
      refine le_antisymm h (not_lt.mp fun hlt => ?_)
      have h1 : ‖((2 : ℤ) : ℤ_[p])‖ < 1 := by exact_mod_cast hlt
      have h3 := (PadicInt.norm_int_lt_one_iff_dvd 2).mp h1
      have h4 : p ∣ 2 := by exact_mod_cast h3
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h4)
    obtain ⟨i2, hi2⟩ := h2.exists_right_inv
    exact ⟨(p : ℤ_[p]) * i2, by linear_combination (p : ℤ_[p]) * hi2⟩

/-- Helper: $p^2 \nmid 2$ in $\mathbb Z_p$. -/
theorem not_sq_dvd_two : ¬ (p : ℤ_[p]) ^ 2 ∣ 2 := by
  intro h
  have h' : ((p : ℤ) ^ 2 : ℤ) ∣ 2 := by
    have := (PadicInt.pow_p_dvd_int_iff 2 2).mp (by exact_mod_cast h)
    exact_mod_cast this
  have hp := (Fact.out : p.Prime).two_le
  have h4 : (4 : ℤ) ≤ (p : ℤ) ^ 2 := by nlinarith
  have := Int.le_of_dvd (by norm_num) h'
  omega

/-- Helper: $Q(a - sy) = Q(a) + s^2Q(y) - sB(a, y)$. -/
theorem eval_sub_smul {R : Type*} [CommRing R] (Q : QuadForm R 4) (a y : Fin 4 → R) (s : R) :
    Q.eval (a - s • y) = Q.eval a + s ^ 2 * Q.eval y - s * bl Q a y := by
  rw [sub_eq_add_neg, ← neg_smul, eval_add, eval_smul, bl_smul_right]; ring

/-- Helper: polar form of the base change of a form along a ring homomorphism. -/
theorem bl_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (Q : QuadForm R 4) (x z : Fin 4 → R) :
    bl (Q.map φ) (fun i => φ (x i)) (fun i => φ (z i)) = φ (bl Q x z) := by
  simp only [bl, QuadForm.hessian, QuadForm.map, dotProduct, mulVec, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.map_apply, map_sum, map_mul, map_add]

namespace Shape93

variable {Q : QuadForm ℤ_[p] 4} {t : Fin 4 → ℤ_[p]} {B : Matrix (Fin 4) (Fin 3) ℤ_[p]} {μ : ℕ} {u1 u2 : ℤ_[p]}

/-- **The shape at a nearby vector** (replacing Cassels' automorph $\sigma$, p. 246): if $Q(y) = Q(t)$ and
$y \equiv t \pmod{p^{\mu+2}}$, then $y$ and the projection $c_j - \lambda_jy$ of $\Delta$ to $y^\perp$
($\lambda_j = B(c_j, y)/2Q(y)$) have the same shape. -/
theorem perturb (S : Shape93 Q t B μ u1 u2) {y : Fin 4 → ℤ_[p]} (hQy : Q.eval y = Q.eval t)
    (hy : ∀ i, (p : ℤ_[p]) ^ (μ + 2) ∣ y i - t i) : ∃ B' : Matrix (Fin 4) (Fin 3) ℤ_[p], Shape93 Q y B' μ u1 u2 := by
  classical
  choose δ' hδ' using hy
  have hyt : y = t + (p : ℤ_[p]) ^ (μ + 2) • δ' := by
    funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linear_combination hδ' i
  obtain ⟨κ, hκ⟩ := exists_two_mul_eq_p (p := p)
  obtain ⟨u2i, hu2i⟩ := S.hu2.exists_right_inv
  set lam : Fin 3 → ℤ_[p] := fun j => (p : ℤ_[p]) * (κ * bl Q (col B j) δ' * u2i) with hlam
  have hblc : ∀ j, bl Q (col B j) y = 2 * lam j * Q.eval y := by
    intro j
    have e : bl Q (col B j) y = (p : ℤ_[p]) ^ (μ + 2) * bl Q (col B j) δ' := by
      rw [hyt, bl_add_right, bl_comm Q (col B j) t, S.orth j, bl_smul_right]; ring
    rw [e, hQy, S.ht, hlam]
    linear_combination (-(p : ℤ_[p]) ^ (μ + 1) * bl Q (col B j) δ' * u2 * u2i) * hκ +
      (-(p : ℤ_[p]) ^ (μ + 2) * bl Q (col B j) δ') * hu2i
  set M : Matrix (Fin 4) (Fin 3) ℤ_[p] := Matrix.of fun i j => y i * lam j with hM
  set B' := B - M with hB'
  have hcol : ∀ j, col B' j = col B j - lam j • y := by
    intro j; rw [col, col, hB', sub_mulVec]; congr 1
    ext i; simp [hM, mulVec, dotProduct, Pi.single_apply, mul_comm]
  have hQyv : Q.eval y = (p : ℤ_[p]) ^ μ * u2 := hQy.trans S.ht
  have hD : ∀ i, (p : ℤ_[p]) ^ (μ + 2) ∣ lam i ^ 2 * Q.eval y := by
    intro i; rw [hQyv, hlam]; exact ⟨(κ * bl Q (col B i) δ' * u2i) ^ 2 * u2, by ring⟩
  have hE : ∀ i j, (p : ℤ_[p]) ^ (μ + 2) ∣ 2 * lam i * lam j * Q.eval y := by
    intro i j; rw [hQyv, hlam]
    exact ⟨2 * (κ * bl Q (col B i) δ' * u2i) * (κ * bl Q (col B j) δ' * u2i) * u2, by ring⟩
  have hQc : ∀ i, Q.eval (col B' i) = Q.eval (col B i) - lam i ^ 2 * Q.eval y := by
    intro i; rw [hcol, eval_sub_smul, hblc]; ring
  have hbc : ∀ i j, bl Q (col B' i) (col B' j) = bl Q (col B i) (col B j) - 2 * lam i * lam j * Q.eval y := by
    intro i j
    rw [hcol, hcol, bl_sub_left, bl_sub_right, bl_sub_right, bl_smul_left, bl_smul_left, bl_smul_right,
      bl_smul_right, hblc, bl_comm Q y (col B j), hblc, bl_self]
    ring
  have hle : ∀ k : ℕ, k ≤ μ + 2 → ∀ x : ℤ_[p], (p : ℤ_[p]) ^ (μ + 2) ∣ x → (p : ℤ_[p]) ^ k ∣ x :=
    fun k hk x hx => (pow_dvd_pow _ hk).trans hx
  refine ⟨B', S.hu1, S.hu2, hQyv, fun j => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun Y hY => ?_⟩
  · rw [hcol, bl_sub_right, bl_smul_right, bl_comm, hblc, bl_self]; ring
  · -- independence, over `ℚ_[p]`
    rw [Fintype.linearIndependent_iff]
    intro w hw
    set φ := PadicInt.Coe.ringHom (p := p)
    set Qp := Q.map φ
    have hcast : ∀ j, (fun i => ((B' i j : ℤ_[p]) : ℚ_[p])) =
        (fun i => ((B i j : ℤ_[p]) : ℚ_[p])) - (lam j : ℚ_[p]) • fun i => ((y i : ℤ_[p]) : ℚ_[p]) := by
      intro j; ext i; simp [hB', hM]; ring
    simp only [hcast, smul_sub, Finset.sum_sub_distrib, smul_smul] at hw
    set s : ℚ_[p] := ∑ j, w j * (lam j : ℚ_[p]) with hs
    have hw' : ∑ j, w j • (fun i => ((B i j : ℤ_[p]) : ℚ_[p])) = s • fun i => ((y i : ℤ_[p]) : ℚ_[p]) := by
      rw [hs, Finset.sum_smul]; exact sub_eq_zero.mp hw
    -- pair with `t`
    have hbt : ∀ j, bl Qp (fun i => ((B i j : ℤ_[p]) : ℚ_[p])) (fun i => ((t i : ℤ_[p]) : ℚ_[p])) = 0 := by
      intro j
      have := bl_map φ Q (col B j) t
      rw [bl_comm Q (col B j) t, S.orth j, map_zero] at this
      have hc : (fun i => ((B i j : ℤ_[p]) : ℚ_[p])) = fun i => φ (col B j i) := by
        ext i; simp [φ, col, mulVec, dotProduct, Pi.single_apply]
      rw [hc]; exact this
    have hLsum : bl Qp (∑ j, w j • (fun i => ((B i j : ℤ_[p]) : ℚ_[p]))) (fun i => ((t i : ℤ_[p]) : ℚ_[p])) = 0 := by
      rw [Fin.sum_univ_three, bl_add_left, bl_add_left, bl_smul_left, bl_smul_left, bl_smul_left, hbt, hbt, hbt]
      ring
    have hyt0 : bl Q y t ≠ 0 := by
      rw [hyt, bl_add_left, bl_self, bl_smul_left, S.ht]
      intro h0
      have e : (p : ℤ_[p]) ^ μ * (2 * u2 + (p : ℤ_[p]) ^ 2 * bl Q δ' t) = 0 := by linear_combination h0
      rcases mul_eq_zero.mp e with h1 | h1
      · exact p_pow_ne_zero μ h1
      · apply not_sq_dvd_two (p := p)
        obtain ⟨u2i', hu2i'⟩ := S.hu2.exists_right_inv
        exact ⟨-(bl Q δ' t) * u2i', by linear_combination u2i' * h1 - 2 * hu2i'⟩
    have hs0 : s = 0 := by
      rw [hw', bl_smul_left] at hLsum
      have := bl_map φ Q y t
      rcases mul_eq_zero.mp hLsum with h | h
      · exact h
      · exfalso; apply hyt0
        have h' : φ (bl Q y t) = 0 := by rw [← this]; exact h
        simpa [φ] using h'
    rw [hs0, zero_smul] at hw'
    exact (Fintype.linearIndependent_iff.mp S.indep) w hw'
  · rw [hQc]; exact dvd_sub S.q0 (hle _ (by omega) _ (hD 0))
  · rw [hQc]; exact dvd_sub S.q1 (hle _ (by omega) _ (hD 1))
  · rw [hQc]; exact dvd_sub S.q2 (hle _ (by omega) _ (hD 2))
  · rw [hbc, show bl Q (col B 0) (col B 1) - 2 * lam 0 * lam 1 * Q.eval y - (p : ℤ_[p]) ^ μ * u1 =
        (bl Q (col B 0) (col B 1) - (p : ℤ_[p]) ^ μ * u1) - 2 * lam 0 * lam 1 * Q.eval y by ring]
    exact dvd_sub S.b01 (hle (μ + 1) (by omega) _ (hE 0 1))
  · rw [hbc]; exact dvd_sub S.b02 (hle _ (by omega) _ (hE 0 2))
  · rw [hbc]; exact dvd_sub S.b12 (hle _ (by omega) _ (hE 1 2))
  · -- primitivity
    set Λ : ℤ_[p] := ∑ j, lam j * Y j with hΛ
    have hΛp : (p : ℤ_[p]) ∣ Λ := by
      rw [hΛ]; exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (dvd_mul_right _ _) _
    obtain ⟨Λ', hΛ'⟩ := hΛp
    have hν : IsUnit (1 - Λ) := by
      have := isUnit_add_p_mul (p := p) isUnit_one (-Λ'); rw [hΛ']; convert this using 1; ring
    obtain ⟨νi, hνi⟩ := hν.exists_right_inv
    set Y' : Fin 3 → ℤ_[p] := νi • Y with hY'
    have hMY : M *ᵥ Y = Λ • y := by
      funext i
      simp only [hM, mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      rw [hΛ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have he : y + B' *ᵥ Y = (1 - Λ) • (y + B *ᵥ Y') := by
      rw [hB', sub_mulVec, hMY, hY', mulVec_smul, smul_add, smul_smul, hνi, one_smul, sub_smul, one_smul]
      abel
    have hval : Q.eval (y + B' *ᵥ Y) = (1 - Λ) ^ 2 * Q.eval (y + B *ᵥ Y') := by rw [he, eval_smul]
    rw [hval, norm_mul, PadicInt.isUnit_iff.mp (hν.pow 2), one_mul, hQy, S.norm_eval_t] at hY
    have hdiv := dvd_of_norm_lt_pow hY
    -- compare with `t + B Y'`
    have hcmp : Q.eval (y + B *ᵥ Y') = Q.eval (t + B *ᵥ Y') +
        (p : ℤ_[p]) ^ (μ + 2) * ((p : ℤ_[p]) ^ (μ + 2) * Q.eval δ' + bl Q (t + B *ᵥ Y') δ') := by
      have e2 : y + B *ᵥ Y' = (t + B *ᵥ Y') + (p : ℤ_[p]) ^ (μ + 2) • δ' := by rw [hyt]; abel
      rw [e2, eval_add, eval_smul, bl_smul_right]; ring
    have hdivt : (p : ℤ_[p]) ^ (μ + 1) ∣ Q.eval (t + B *ᵥ Y') := by
      have h2 : (p : ℤ_[p]) ^ (μ + 1) ∣ (p : ℤ_[p]) ^ (μ + 2) *
          ((p : ℤ_[p]) ^ (μ + 2) * Q.eval δ' + bl Q (t + B *ᵥ Y') δ') :=
        Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
      have := dvd_sub hdiv h2
      rw [hcmp] at this
      simpa using this
    obtain ⟨i, hi⟩ := S.prim' Y' hdivt
    refine ⟨i, ?_⟩
    rw [he, Pi.smul_apply, smul_eq_mul]
    refine hν.mul ?_
    have e3 : (y + B *ᵥ Y') i = (t + B *ᵥ Y') i + (p : ℤ_[p]) * ((p : ℤ_[p]) ^ (μ + 1) * δ' i) := by
      rw [hyt]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e3]
    exact isUnit_add_p_mul hi _

/-- **Transfer of the shape along a change of basis** $E \in \mathrm{GL}_4(\mathbb Z_p)$ (as `Ch11L93.transfer`). -/
theorem transfer {Q : QuadForm ℤ_[p] 4} (E : Matrix (Fin 4) (Fin 4) ℤ_[p]) (hE : IsUnit E.det)
    (S : Shape93 (pull Q E) t B μ u1 u2) : Shape93 Q (E *ᵥ t) (E * B) μ u1 u2 := by
  have hcol : ∀ j, col (E * B) j = E *ᵥ col B j := fun j => by rw [col, col, mulVec_mulVec]
  have hD := (S.toData).indep
  refine ⟨S.hu1, S.hu2, by rw [← pull_eval]; exact S.ht, fun j => by rw [hcol, ← pull_bl]; exact S.orth j, ?_,
    by rw [hcol, ← pull_eval]; exact S.q0, by rw [hcol, ← pull_eval]; exact S.q1,
    by rw [hcol, ← pull_eval]; exact S.q2, by rw [hcol, hcol, ← pull_bl]; exact S.b01,
    by rw [hcol, hcol, ← pull_bl]; exact S.b02, by rw [hcol, hcol, ← pull_bl]; exact S.b12, fun y hy => ?_⟩
  · set Eq : Matrix (Fin 4) (Fin 4) ℚ_[p] := E.map PadicInt.Coe.ringHom with hEq
    have hdet : IsUnit Eq.det := by
      rw [hEq, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact hE.map _
    have hinj : Function.Injective (Matrix.mulVecLin Eq) := by
      intro v w hvw
      have := congrArg (fun v => Eq⁻¹ *ᵥ v) hvw
      simpa [Matrix.mulVecLin_apply, mulVec_mulVec, nonsing_inv_mul _ hdet] using this
    have := S.indep.map' (Matrix.mulVecLin Eq) (LinearMap.ker_eq_bot.mpr hinj)
    convert this using 1
    ext j i
    simp [hEq, mulVec, dotProduct, Matrix.mul_apply]
  · rw [← mulVec_mulVec, ← mulVec_add, ← pull_eval, ← pull_eval] at hy
    have hu := S.prim y hy
    have hEu : IsUnit E := (Matrix.isUnit_iff_isUnit_det E).mpr hE
    obtain ⟨i, hi⟩ := Siegel.exists_isUnit_coord_mulVec hEu.unit hu
    refine ⟨i, ?_⟩
    simpa [mulVec_add, mulVec_mulVec] using hi

end Shape93

/-- **Cassels' construction gives the shape** (the computation of `Ch11L93.core`, pp. 243–245): in coordinates adapted to
an isotropic vector ($Q(e_0) = 0$, $B(e_0, e_2) = B(e_0, e_3) = 0$, $B(e_0, e_1) \ne 0$, $Q(e_2) \ne 0$), the vector
$t = p^se_2$ and the lattice with basis $e_0$, $p^re_1 - k_1p^se_2$, $p^Te_3 - k_3p^se_2$ have the shape. -/
theorem core_shape (Q : QuadForm ℤ_[p] 4) (h00 : Q.coeff 0 0 = 0) (h02 : Q.coeff 0 2 = 0) (h03 : Q.coeff 0 3 = 0)
    (h01 : Q.coeff 0 1 ≠ 0) (h22 : Q.coeff 2 2 ≠ 0) :
    ∃ (t : Fin 4 → ℤ_[p]) (B : Matrix (Fin 4) (Fin 3) ℤ_[p]) (μ : ℕ) (u1 u2 : ℤ_[p]), Shape93 Q t B μ u1 u2 := by
  obtain ⟨bb, u1, hu1, hc01⟩ := decomp h01
  obtain ⟨gg, u2, hu2, hc22⟩ := decomp h22
  obtain ⟨ll, w, hw, h2⟩ := decomp (two_ne_zero : (2 : ℤ_[p]) ≠ 0)
  obtain ⟨W, hW⟩ := (hw.mul hu2).exists_right_inv
  have hP0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨k2, hk2⟩ : ∃ k : ℤ_[p], k = Q.coeff 1 2 * (p : ℤ_[p]) ^ (gg + 2) * W := ⟨_, rfl⟩
  obtain ⟨k4, hk4⟩ : ∃ k : ℤ_[p], k = Q.coeff 2 3 * (p : ℤ_[p]) ^ (bb + gg + 3) * W := ⟨_, rfl⟩
  obtain ⟨A11, hA11⟩ : ∃ A : ℤ_[p], A = Q.coeff 1 1 * (p : ℤ_[p]) ^ (2 * ll + 3 * gg + 3) -
      Q.coeff 1 2 ^ 2 * W * (p : ℤ_[p]) ^ (ll + 2 * gg + 3) +
      Q.coeff 2 2 * Q.coeff 1 2 ^ 2 * W ^ 2 * (p : ℤ_[p]) ^ (gg + 3) := ⟨_, rfl⟩
  obtain ⟨A12, hA12⟩ : ∃ A : ℤ_[p], A = -(Q.coeff 1 2 * Q.coeff 2 3 * W * (p : ℤ_[p]) ^ (bb + ll + 2 * gg + 4)) +
      Q.coeff 1 3 * (p : ℤ_[p]) ^ (bb + 2 * ll + 3 * gg + 4) +
      2 * Q.coeff 2 2 * Q.coeff 1 2 * Q.coeff 2 3 * W ^ 2 * (p : ℤ_[p]) ^ (bb + gg + 4) -
      Q.coeff 2 3 * Q.coeff 1 2 * W * (p : ℤ_[p]) ^ (bb + ll + 2 * gg + 4) := ⟨_, rfl⟩
  obtain ⟨A22, hA22⟩ : ∃ A : ℤ_[p], A = Q.coeff 2 2 * Q.coeff 2 3 ^ 2 * W ^ 2 * (p : ℤ_[p]) ^ (2 * bb + gg + 5) -
      Q.coeff 2 3 ^ 2 * W * (p : ℤ_[p]) ^ (2 * bb + ll + 2 * gg + 5) +
      Q.coeff 3 3 * (p : ℤ_[p]) ^ (2 * bb + 2 * ll + 3 * gg + 5) := ⟨_, rfl⟩
  set t : Fin 4 → ℤ_[p] := ![0, 0, (p : ℤ_[p]) ^ (bb + ll + gg + 2), 0] with ht
  set B : Matrix (Fin 4) (Fin 3) ℤ_[p] := Matrix.of ![![1, 0, 0],
    ![0, (p : ℤ_[p]) ^ (bb + 2 * ll + 3 * gg + 4), 0],
    ![0, -(k2 * (p : ℤ_[p]) ^ (bb + ll + gg + 2)), -(k4 * (p : ℤ_[p]) ^ (bb + ll + gg + 2))],
    ![0, 0, (p : ℤ_[p]) ^ (2 * bb + 2 * ll + 3 * gg + 5)]] with hBdef
  have hB : ∀ y : Fin 3 → ℤ_[p], B *ᵥ y = ![y 0, (p : ℤ_[p]) ^ (bb + 2 * ll + 3 * gg + 4) * y 1,
      -(k2 * (p : ℤ_[p]) ^ (bb + ll + gg + 2)) * y 1 + -(k4 * (p : ℤ_[p]) ^ (bb + ll + gg + 2)) * y 2,
      (p : ℤ_[p]) ^ (2 * bb + 2 * ll + 3 * gg + 5) * y 2] := by
    intro y; ext i; fin_cases i <;> simp [hBdef, mulVec, dotProduct, Fin.sum_univ_three]
  set μ := 2 * bb + 2 * ll + 3 * gg + 4 with hμ
  have hQB : ∀ y : Fin 3 → ℤ_[p], Q.eval (B *ᵥ y) = (p : ℤ_[p]) ^ μ * u1 * y 0 * y 1 +
      (p : ℤ_[p]) ^ (μ + 1) * (A11 * y 1 * y 1 + A12 * y 1 * y 2 + A22 * y 2 * y 2) := by
    intro y
    rw [hB, eval_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    rw [h00, h02, h03, hc01, hA11, hA12, hA22, hk2, hk4, hμ]
    ring
  have hQt : ∀ y : Fin 3 → ℤ_[p], Q.eval (t + B *ᵥ y) = (p : ℤ_[p]) ^ μ * u2 + Q.eval (B *ᵥ y) := by
    intro y
    rw [hB, ht, eval_four, eval_four]
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [h00, h02, h03, hc22, hk2, hk4, hμ]
    linear_combination (-((p : ℤ_[p]) ^ gg * u2 * (p : ℤ_[p]) ^ (2 * bb + 2 * ll + 2 * gg + 4) *
      (Q.coeff 1 2 * (p : ℤ_[p]) ^ (gg + 2) * W * y 1 + Q.coeff 2 3 * (p : ℤ_[p]) ^ (bb + gg + 3) * W * y 2))) * h2 +
      (-(Q.coeff 1 2 * (p : ℤ_[p]) ^ (2 * bb + 3 * ll + 4 * gg + 6) * y 1 +
        Q.coeff 2 3 * (p : ℤ_[p]) ^ (3 * bb + 3 * ll + 4 * gg + 7) * y 2)) * hW
  have hQt0 : Q.eval t = (p : ℤ_[p]) ^ μ * u2 := by
    have := hQt 0
    rwa [mulVec_zero, add_zero, eval_zero', add_zero] at this
  have hPμ : (p : ℤ_[p]) ^ μ ≠ 0 := pow_ne_zero _ hP0
  have hnormt : ‖Q.eval t‖ = ‖(p : ℤ_[p]) ^ μ‖ := by
    rw [hQt0, norm_mul, PadicInt.isUnit_iff.mp hu2, mul_one]
  have hbl : ∀ y z : Fin 3 → ℤ_[p], bl Q (B *ᵥ y) (B *ᵥ z) = Q.eval (B *ᵥ (y + z)) - Q.eval (B *ᵥ y) -
      Q.eval (B *ᵥ z) := by
    intro y z; rw [bl_eq, mulVec_add]
  have hs : ∀ j : Fin 3, col B j = B *ᵥ Pi.single j 1 := fun j => rfl
  refine ⟨t, B, μ, u1, u2, ⟨hu1, hu2, hQt0, fun j => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [bl_eq, hs, hQt, hQt0]; ring
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have e0 := congrFun hc 0
    have e1 := congrFun hc 1
    have e3 := congrFun hc 3
    simp [Fin.sum_univ_three, hBdef] at e0 e1 e3
    intro i; fin_cases i
    · simpa using e0
    · exact e1.resolve_right (Fact.out : p.Prime).ne_zero
    · exact e3.resolve_right (Fact.out : p.Prime).ne_zero
  · rw [hs, hQB]; simp
  · rw [hs, hQB]; exact ⟨A11, by simp⟩
  · rw [hs, hQB]; exact ⟨(p : ℤ_[p]) * A22, by simp; ring⟩
  · rw [hs, hs, hbl, hQB, hQB, hQB]; exact ⟨0, by simp⟩
  · rw [hs, hs, hbl, hQB, hQB, hQB]; exact ⟨0, by simp⟩
  · rw [hs, hs, hbl, hQB, hQB, hQB]; exact ⟨(p : ℤ_[p]) * A12, by simp; ring⟩
  · intro y hy
    refine ⟨0, ?_⟩
    have hy0 : (t + B *ᵥ y) 0 = y 0 := by rw [hB, ht]; simp
    rw [hy0]
    rw [hnormt, hQt, hQB] at hy
    have hZ : ‖u2 + u1 * y 0 * y 1 + (p : ℤ_[p]) * (A11 * y 1 * y 1 + A12 * y 1 * y 2 + A22 * y 2 * y 2)‖ < 1 := by
      have e : (p : ℤ_[p]) ^ μ * u2 + ((p : ℤ_[p]) ^ μ * u1 * y 0 * y 1 + (p : ℤ_[p]) ^ (μ + 1) *
          (A11 * y 1 * y 1 + A12 * y 1 * y 2 + A22 * y 2 * y 2)) = (p : ℤ_[p]) ^ μ * (u2 + u1 * y 0 * y 1 +
          (p : ℤ_[p]) * (A11 * y 1 * y 1 + A12 * y 1 * y 2 + A22 * y 2 * y 2)) := by ring
      rw [e, norm_mul] at hy
      have hpos : 0 < ‖(p : ℤ_[p]) ^ μ‖ := norm_pos_iff.mpr hPμ
      nlinarith
    by_contra hnu
    have m1 : u2 + u1 * y 0 * y 1 + (p : ℤ_[p]) * (A11 * y 1 * y 1 + A12 * y 1 * y 2 + A22 * y 2 * y 2) ∈
        IsLocalRing.maximalIdeal ℤ_[p] := PadicInt.mem_nonunits.mpr hZ
    have m2 : u1 * y 0 * y 1 ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hnu)
    have m3 : (p : ℤ_[p]) * (A11 * y 1 * y 1 + A12 * y 1 * y 2 + A22 * y 2 * y 2) ∈
        IsLocalRing.maximalIdeal ℤ_[p] := Ideal.mul_mem_right _ _ PadicInt.p_nonunit
    have : u2 ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      have := Ideal.sub_mem _ (Ideal.sub_mem _ m1 m2) m3
      convert this using 1; ring
    exact this hu2

/-- **The shape exists for every regular isotropic quaternary form over $\mathbb Z_p$** (Cassels, Lemma 9.3 and its
proof): normal form of a primitive isotropic vector (`Ch11L93.normal_form`), `core_shape`, `Shape93.transfer`. -/
theorem exists_shape93 (Q : QuadForm ℤ_[p] 4) (hnd : Q.Nondegenerate)
    (hiso : (Q.map PadicInt.Coe.ringHom).IsotropicIn ℚ_[p]) :
    ∃ (t : Fin 4 → ℤ_[p]) (B : Matrix (Fin 4) (Fin 3) ℤ_[p]) (μ : ℕ) (u1 u2 : ℤ_[p]), Shape93 Q t B μ u1 u2 := by
  have hiso' : Q.IsotropicIn ℚ_[p] := by
    obtain ⟨v, hv0, hv⟩ := hiso
    refine ⟨v, hv0, ?_⟩
    rw [← hv]
    simp [QuadForm.evalIn, QuadForm.map]
  obtain ⟨x, ⟨i, hi⟩, hx⟩ := LocalDensity.DVR.exists_primitive_of_isotropicIn ℚ_[p] Q (p : ℤ_[p])
    PadicInt.irreducible_p hiso'
  have hxu : IsUnit (x i) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) ?_
    by_contra hlt
    exact hi ((PadicInt.norm_lt_one_iff_dvd _).mp (lt_of_not_ge hlt))
  obtain ⟨c, hc, hc0, hc01, hc02, hc03, hc2⟩ := normal_form Q hnd ⟨i, hxu⟩ hx
  set E := colMat c with hEdef
  have hE : IsUnit E.det := by rwa [hEdef, colMat, det_transpose]
  have k00 : (pull Q E).coeff 0 0 = 0 := by rw [coeff00, pull_eval, hEdef, colMat_single, hc0]
  have k01 : (pull Q E).coeff 0 1 ≠ 0 := by
    rw [coeff01, pull_bl, hEdef, colMat_single, colMat_single]; exact hc01
  have k02 : (pull Q E).coeff 0 2 = 0 := by
    rw [coeff02, pull_bl, hEdef, colMat_single, colMat_single]; exact hc02
  have k03 : (pull Q E).coeff 0 3 = 0 := by
    rw [coeff03, pull_bl, hEdef, colMat_single, colMat_single]; exact hc03
  have k22 : (pull Q E).coeff 2 2 ≠ 0 := by rw [coeff22, pull_eval, hEdef, colMat_single]; exact hc2
  obtain ⟨t, B, μ, u1, u2, S⟩ := core_shape (pull Q E) k00 k02 k03 k01 k22
  exact ⟨E *ᵥ t, E * B, μ, u1, u2, S.transfer E hE⟩

end QuadFormsKB.Cassels.Ch11L92
