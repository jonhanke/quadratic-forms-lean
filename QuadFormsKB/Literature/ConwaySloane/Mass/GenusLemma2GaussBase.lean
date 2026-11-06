/-
# Conway–Sloane, LDL IV, §11, Lemma 2 at $p = 2$: Gauss sums of the discriminant form (definitions)

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §11, Lemma 2, p. 280; Conway–Sloane, *Sphere Packings, Lattices and Groups*, Ch. 15,
§7.3–7.5 (`conwaysloane1999`) for the 2-adic symbols.

This file fixes the objects used to prove the local 2-adic step `Mass.Lemma2IfDyadicRationalStatement` (see
`GenusLemma2Local.lean` for the proof outline).

**Definitions.**
* `ch x` $= \psi_2(x/2)$, where $\psi_2$ is the standard additive character of $\mathbb Q_2$ (`Analysis.psiP`, kernel
  $\mathbb Z_2$). So `ch` is an additive character of $\mathbb Q_2$ with kernel $2\mathbb Z_2$; on $\mathbb Z[1/2]$ it
  is $x \mapsto e^{-\pi i x}$.
* `zeta8` $=$ `ch (1/4)` $= e^{-2\pi i/8}$, a primitive 8th root of unity.
* `qv F v` $= v^{\mathsf T}Fv$; `natVec f` the vector of the natural numbers $f_i$, viewed in $\mathbb Q_2$.
* `blockGauss b m` $= \sum_{x} \mathrm{ch}(2^m\, x^{\mathsf T} B^{-1} x)$, the sum over $x \in \{0, \dots, 2^e - 1\}^{d}$,
  for a Jordan block $b$ (`Cassels.DyBlock`) with matrix $B$, exponent $e$ and $d$ variables: the Gauss sum of the
  discriminant form $2^{-e}\mathbb Z_2^d / \mathbb Z_2^d$ of the block, scaled by $2^m$.
* `blockPhase b m` $\in \mathbb Z/8$: $t_b + 4(e - m)[\varepsilon_b = -1]$ if $e > m$ and $0$ otherwise
  ($t_b$ = `blockOddity`, $\varepsilon_b$ = `blockSign`). `blockGauss b m` is a positive real multiple of
  `zeta8 ^ blockPhase b m` unless $b = 2^m u x^2$ with $m \ge 1$, when it is $0$ (`GenusLemma2GaussBlocks.lean`).
* `Admissible F F' T`: the matrix data of an isomorphism of discriminant forms $\mathbb Z_2^\iota / F\mathbb Z_2^\iota
  \to \mathbb Z_2^{\iota'}/F'\mathbb Z_2^{\iota'}$ preserving the norms $y^{\mathsf T}F^{-1}y$ modulo $T\mathbb Z_2$.

Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.TwoAdicClassification
import QuadFormsKB.Analysis.LocalFourier

set_option linter.unusedSectionVars false

open Matrix QuadFormsKB QuadFormsKB.Analysis QuadFormsKB.Cassels Finset

namespace QuadFormsKB.ConwaySloane.Mass.Gauss2

/-! ### The character -/

/-- The additive character $x \mapsto \psi_2(x/2)$ of $\mathbb Q_2$, with kernel $2\mathbb Z_2$. -/
noncomputable def ch (x : ℚ_[2]) : ℂ := ((psiP (p := 2) (x / 2) : Circle) : ℂ)

theorem ch_add (x y : ℚ_[2]) : ch (x + y) = ch x * ch y := by
  unfold ch; rw [add_div, AddChar.map_add_eq_mul, Circle.coe_mul]

@[simp] theorem ch_zero : ch 0 = 1 := by
  unfold ch; rw [zero_div, AddChar.map_zero_eq_one, Circle.coe_one]

theorem ch_eq_one {x : ℚ_[2]} (h : ‖x / 2‖ ≤ 1) : ch x = 1 := by
  unfold ch; rw [(psiP_eq_one_iff (p := 2) _).2 h, Circle.coe_one]

theorem ch_add_of {x z : ℚ_[2]} (h : ‖z / 2‖ ≤ 1) : ch (x + z) = ch x := by
  rw [ch_add, ch_eq_one h, mul_one]

theorem ch_neg (x : ℚ_[2]) : ch (-x) * ch x = 1 := by
  rw [← ch_add, neg_add_cancel, ch_zero]

theorem ch_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ_[2]) : ch (∑ i ∈ s, f i) = ∏ i ∈ s, ch (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, ch_add, ih]

/-- $\zeta_8 = \mathrm{ch}(1/4) = e^{-2\pi i/8}$. -/
noncomputable def zeta8 : ℂ := ch (1 / 4)

/-! ### Integrality, quadratic values, representatives -/

/-- A matrix over $\mathbb Q_2$ with entries in $\mathbb Z_2$. -/
def IsIntM {ι κ : Type*} (M : Matrix ι κ ℚ_[2]) : Prop := ∀ i j, ‖M i j‖ ≤ 1

/-- A vector over $\mathbb Q_2$ with entries in $\mathbb Z_2$. -/
def IsIntV {ι : Type*} (v : ι → ℚ_[2]) : Prop := ∀ i, ‖v i‖ ≤ 1

/-- The quadratic value $v^{\mathsf T}Fv$. -/
noncomputable def qv {ι : Type*} [Fintype ι] (F : Matrix ι ι ℚ_[2]) (v : ι → ℚ_[2]) : ℚ_[2] := v ⬝ᵥ (F *ᵥ v)

/-- The vector of natural numbers $f_i$ in $\mathbb Q_2$. -/
noncomputable def natVec {ι : Type*} {N : ι → ℕ} (f : (i : ι) → Fin (N i)) : ι → ℚ_[2] :=
  fun i => (((f i : ℕ) : ℚ) : ℚ_[2])

/-- The exponent of a block, as a natural number. -/
def bex (b : DyBlock) : ℕ := (blockExp b).toNat

/-- **The Gauss sum of a block**: $\sum_{x \in \{0,\dots,2^e-1\}^d} \mathrm{ch}(2^m x^{\mathsf T}B^{-1}x)$. -/
noncomputable def blockGauss (b : DyBlock) (m : ℕ) : ℂ :=
  ∑ f : Fin b.dim → Fin (2 ^ bex b), ch ((2 : ℚ_[2]) ^ m * qv b.mat⁻¹ (natVec f))

/-- **The phase of a block Gauss sum** (in $\mathbb Z/8$): $t_b + 4(e - m)[\varepsilon_b = -1]$ for $e > m$, else $0$. -/
def blockPhase (b : DyBlock) (m : ℕ) : ZMod 8 :=
  if m < bex b then blockOddity b + 4 * ((bex b - m : ℕ) : ZMod 8) * signInd (blockSign b) else 0

/-! ### Admissible data: an isomorphism of discriminant forms in matrix form -/

/-- **Matrix data of an isomorphism of discriminant forms over $\mathbb Z_2$.** Integral $\Psi$, $\Psi'$ with
$\Psi F = F'W$, $\Psi'F' = FW'$ (so $y \mapsto \Psi y$, $z \mapsto \Psi' z$ induce maps between
$\mathbb Z_2^\iota/F\mathbb Z_2^\iota$ and $\mathbb Z_2^{\iota'}/F'\mathbb Z_2^{\iota'}$), mutually inverse
($\Psi'\Psi = 1 + FM$, $\Psi\Psi' = 1 + F'M'$), and preserving the norms modulo $T$:
$(\Psi y)^{\mathsf T}F'^{-1}(\Psi y) - y^{\mathsf T}F^{-1}y \in T\mathbb Z_2$ for $y \in \mathbb Z_2^\iota$. -/
def Admissible {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (F : Matrix ι ι ℚ_[2]) (F' : Matrix ι' ι' ℚ_[2]) (T : ℕ) : Prop :=
  ∃ (Ψ : Matrix ι' ι ℚ_[2]) (Ψ' : Matrix ι ι' ℚ_[2]) (W : Matrix ι' ι ℚ_[2]) (W' : Matrix ι ι' ℚ_[2])
    (M : Matrix ι ι ℚ_[2]) (M' : Matrix ι' ι' ℚ_[2]),
    IsIntM Ψ ∧ IsIntM Ψ' ∧ IsIntM W ∧ IsIntM W' ∧ IsIntM M ∧ IsIntM M' ∧
    Ψ * F = F' * W ∧ Ψ' * F' = F * W' ∧ Ψ' * Ψ = 1 + F * M ∧ Ψ * Ψ' = 1 + F' * M' ∧
    ∀ y : ι → ℚ_[2], IsIntV y → ∃ z : ℚ_[2], ‖z‖ ≤ 1 ∧ qv F'⁻¹ (Ψ *ᵥ y) - qv F⁻¹ y = (T : ℚ_[2]) * z

end QuadFormsKB.ConwaySloane.Mass.Gauss2
