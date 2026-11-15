/-
# Shimura 2004, §7.3–§7.4: the Clifford algebra and groups in dimensions 3 and 4

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), §7.3 (printed p. 53),
§7.4, formulas (7.3a), (7.3b) (printed p. 54). Page numbers in the tags are printed pages.

**Setting and dictionary.** As in `Wave5/LowDim.lean` (§7.1–7.2): $F$ a field of characteristic $\ne 2$
(`Invertible (2 : F)`), `Q : QuadraticForm F V` with $Q(x) = \varphi[x]$, $A(Z)$ = `CliffordAlgebra Q`,
$A^\pm(Z)$ = `evenOdd Q 0`, `evenOdd Q 1`, $a \mapsto a^*$ = `reverse`, $G^+(Z)$ = `M0 Q`, $G^1(Z)$ =
`spinGroupG1 Q`.

*Dimension 3* (§7.3): an orthogonal basis `h : Fin 3 → V` of $Z$ with $c_i = \varphi[h_i] \ne 0$
(`hh`, `horth`, `hspan`). **Indices are 0-based**: Shimura's $h_1, h_2, h_3$ are `h 0`, `h 1`, `h 2` here, and
$c_i$ is `Q (h i)`. Shimura's $g_1 = h_2h_3$, $g_2 = h_3h_1$, $g_3 = h_1h_2$ become
$g_0 = h_1h_2$ (`g₀ Q h`), $g_1 = h_2h_0$ (`g₁ Q h`), $g_2 = h_0h_1$ (`g₂ Q h`), written with the 0-based
$h_0,h_1,h_2$; $\zeta = h_0h_1h_2$ (`zeta Q h`), $d = c_0c_1c_2$, $T = Fg_0 + Fg_1 + Fg_2$, $B = F + T$.
Statements write $r + s_0g_0 + s_1g_1 + s_2g_2$ out in full; internal lemmas abbreviate it by a local notation.

*Dimension 4* (§7.4): an orthogonal basis `h : Fin 4 → V`, same hypotheses.

**Proves** (all unconditional; standard axioms only)
* §7.3: $A^+(Z) = B$ (`dim3_evenOdd_zero_iff`); $g_i^* = -g_i$, i.e. $a \mapsto a^*$ is the main involution of
  $B$ (`dim3_reverse_B`), and $bb^* = b^*b = N(b)$ (`dim3_nu`, `dim3_nu'`); $\zeta^2 = -d$ (`zeta_sq`) and $\zeta$
  central (`zeta_comm`); $A^-(Z) = Z + F\zeta$ (`dim3_evenOdd_one_iff`) and $\{x \in A^-(Z) \mid x^* = x\} = \iota(Z)$
  (`dim3_odd_fixed_iff`); (7.2) $G^+(Z) = B^\times$ (`dim3_mem_M0_iff`), $G^1(Z) = \{b \in B^\times \mid bb^* = 1\}$
  (`dim3_mem_spinGroupG1_iff`), $\nu(b) = bb^*$ (`dim3_nu_M0`); $Z = T\zeta$ (`dim3_zeta_vec`) and $\varphi[x\zeta] =
  d\,xx^*$ (`dim3_Q_zeta`); $\varphi$ anisotropic $\iff$ $B$ a division algebra (`dim3_anisotropic_iff`).
* §7.4: (7.3a) (`dim4_odd_fixed_iff`) and (7.3b) (`dim4_mem_M0_iff`); in (7.3b) the condition $xx^* \in F^\times$ is
  stated as $xx^* \in F$ (nonvanishing is automatic for a unit).
-/
import QuadFormsKB.Literature.Shimura2004.CliffordGroups
import QuadFormsKB.Literature.Shimura2004.CliffordParity
import QuadFormsKB.Literature.Shimura2004.Wave2.CliffordLemmas
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

namespace LowDim

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

local notation "A" => CliffordAlgebra Q

/-! ### General lemmas for an orthogonal family -/

section Basic

variable {n : ℕ} {h : Fin n → V}

theorem ι_anti (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) {i j : Fin n} (hij : i ≠ j) :
    ι Q (h j) * ι Q (h i) = -(ι Q (h i) * ι Q (h j)) := by
  have := ι_mul_ι_add_swap (Q := Q) (h i) (h j)
  rw [horth i j hij, map_zero] at this
  exact eq_neg_of_add_eq_zero_right this

theorem ι_sq' (i : Fin n) : ι Q (h i) * ι Q (h i) = Q (h i) • (1 : A) := by
  rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one]

theorem sq_r (i : Fin n) (x : A) : ι Q (h i) * (ι Q (h i) * x) = Q (h i) • x := by
  rw [← mul_assoc, ι_sq', smul_mul_assoc, one_mul]

/-- A general element of the span of an orthogonal family has polar form $2c_j a_j$ against $h_j$. -/
theorem polar_sum_right (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (a : Fin n → F) (j : Fin n) :
    QuadraticMap.polar Q (∑ i, a i • h i) (h j) = a j * (2 * Q (h j)) := by
  have hpol : ∀ i, QuadraticMap.polar Q (a i • h i) (h j) = if i = j then a j * (2 * Q (h j)) else 0 := by
    intro i
    rw [QuadraticMap.polar_smul_left]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, QuadraticMap.polar_self, nsmul_eq_mul]
      push_cast
      ring
    · rw [if_neg hij, horth i j hij, smul_zero]
  have hsum : QuadraticMap.polar Q (∑ i, a i • h i) (h j) = ∑ i, QuadraticMap.polar Q (a i • h i) (h j) := by
    rw [← QuadraticMap.polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
    simp_rw [QuadraticMap.polarBilin_apply_apply]
  rw [hsum]
  simp [hpol]

/-- For an orthogonal spanning family with $\varphi[h_i] \ne 0$: a vector orthogonal to all $h_j$ is zero. -/
theorem eq_zero_of_polar (hh : ∀ i, Q (h i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin n → F, z = ∑ i, c i • h i) {v : V}
    (hv : ∀ j, QuadraticMap.polar Q v (h j) = 0) : v = 0 := by
  obtain ⟨c, rfl⟩ := hspan v
  have : ∀ j, c j = 0 := by
    intro j
    have := hv j
    rw [polar_sum_right horth] at this
    exact (mul_eq_zero.1 this).resolve_right
      (mul_ne_zero (isUnit_of_invertible (2 : F)).ne_zero (hh j))
  simp [this]

/-- If $\iota(v) = 0$ for an orthogonal spanning family with $\varphi[h_i] \ne 0$, then $v = 0$. -/
theorem eq_zero_of_ι_eq_zero (hh : ∀ i, Q (h i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin n → F, z = ∑ i, c i • h i) {v : V} (hv : ι Q v = 0) : v = 0 := by
  refine eq_zero_of_polar hh horth hspan fun j => ?_
  have := ι_mul_ι_add_swap (Q := Q) v (h j)
  rw [hv, zero_mul, mul_zero, add_zero] at this
  exact (algebraMap F A).injective (by rw [← this, map_zero])

/-- An orthogonal spanning family with $\varphi[h_i] \ne 0$ makes $\varphi$ nondegenerate. -/
theorem nondegenerate_of_orthogonal (hh : ∀ i, Q (h i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin n → F, z = ∑ i, c i • h i) :
    (QuadraticMap.associated Q).Nondegenerate := by
  have hpol : ∀ u v, QuadraticMap.associated Q u v = 0 → QuadraticMap.polar Q u v = 0 := by
    intro u v huv
    have e := LinearMap.congr_fun₂ (QuadraticMap.two_nsmul_associated F Q) u v
    rw [LinearMap.smul_apply, LinearMap.smul_apply] at e
    change 2 • QuadraticMap.associated Q u v = QuadraticMap.polar Q u v at e
    rw [huv, smul_zero] at e
    exact e.symm
  have key : ∀ m, (∀ v, QuadraticMap.polar Q m v = 0) → m = 0 := by
    intro m hp
    exact eq_zero_of_polar hh horth hspan fun j => hp (h j)
  refine ⟨fun m hm => key m fun v => hpol m v (hm v), fun m hm => key m fun v => ?_⟩
  rw [QuadraticMap.polar_comm]
  exact hpol v m (hm v)

end Basic

/-! ### The generic step: units that conjugate odd fixed elements into $V$ -/

section Generic

/-- Shimura's argument for (7.2) and (7.3b): an even unit $a$ with $aa^* \in F$ lies in $G^+$ provided that every
odd $*$-fixed element of $A$ lies in $\iota(V)$ (so that $a\,\iota(x)\,a^*$, being odd and $*$-fixed, lies in $V$). -/
theorem mem_M0_of_odd_fixed (u : Aˣ) (hu : (u : A) ∈ evenOdd Q 0) {c : F}
    (hc : (u : A) * reverse (u : A) = algebraMap F A c)
    (hV : ∀ w : A, w ∈ evenOdd Q 1 → reverse w = w → ∃ v : V, ι Q v = w) : u ∈ M0 Q := by
  have hunit : IsUnit ((u : A) * reverse (u : A)) := by
    refine IsUnit.mul u.isUnit ⟨⟨reverse (u : A), reverse ((u⁻¹ : Aˣ) : A), ?_, ?_⟩, rfl⟩
    · rw [← reverse.map_mul]; simp
    · rw [← reverse.map_mul]; simp
  have hc0 : c ≠ 0 := by
    intro h0
    rw [hc, h0, map_zero] at hunit
    exact not_isUnit_zero hunit
  have hrev : reverse (u : A) ∈ evenOdd Q 0 := (reverse_mem_evenOdd_iff Q).2 hu
  obtain ⟨u', hu', hM⟩ := mem_M0_of_mul_reverse hu hc0 hc fun x => by
    have hodd : (u : A) * ι Q x * reverse (u : A) ∈ evenOdd Q 1 := by
      have := mul_mem_evenOdd (mul_mem_evenOdd hu (ι_mem_evenOdd_one Q x)) hrev
      simpa using this
    have hfix : reverse ((u : A) * ι Q x * reverse (u : A)) = (u : A) * ι Q x * reverse (u : A) := by
      simp only [reverse.map_mul, reverse_reverse, reverse_ι, mul_assoc]
    exact hV _ hodd hfix
  have : u = u' := Units.ext hu'.symm
  rwa [this]

end Generic

/-! ### §7.3: dimension 3 -/

section Dim3

variable {h : Fin 3 → V}

omit [FiniteDimensional F V] in
/-- $g_0 = h_1h_2$ (Shimura's $g_1 = h_2h_3$). -/
def g₀ (Q : QuadraticForm F V) (h : Fin 3 → V) : CliffordAlgebra Q := ι Q (h 1) * ι Q (h 2)

omit [FiniteDimensional F V] in
/-- $g_1 = h_2h_0$ (Shimura's $g_2 = h_3h_1$). -/
def g₁ (Q : QuadraticForm F V) (h : Fin 3 → V) : CliffordAlgebra Q := ι Q (h 2) * ι Q (h 0)

omit [FiniteDimensional F V] in
/-- $g_2 = h_0h_1$ (Shimura's $g_3 = h_1h_2$). -/
def g₂ (Q : QuadraticForm F V) (h : Fin 3 → V) : CliffordAlgebra Q := ι Q (h 0) * ι Q (h 1)

omit [FiniteDimensional F V] in
/-- $\zeta = h_0h_1h_2$ (Shimura's $\zeta = h_1h_2h_3$). -/
def zeta (Q : QuadraticForm F V) (h : Fin 3 → V) : CliffordAlgebra Q := ι Q (h 0) * ι Q (h 1) * ι Q (h 2)

section Table

variable (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
include horth

theorem a10 : ι Q (h 1) * ι Q (h 0) = -(ι Q (h 0) * ι Q (h 1)) := ι_anti horth (by decide)
theorem a20 : ι Q (h 2) * ι Q (h 0) = -(ι Q (h 0) * ι Q (h 2)) := ι_anti horth (by decide)
theorem a21 : ι Q (h 2) * ι Q (h 1) = -(ι Q (h 1) * ι Q (h 2)) := ι_anti horth (by decide)

theorem r10 (x : A) : ι Q (h 1) * (ι Q (h 0) * x) = -(ι Q (h 0) * (ι Q (h 1) * x)) := by
  rw [← mul_assoc, a10 horth, neg_mul, mul_assoc]
theorem r20 (x : A) : ι Q (h 2) * (ι Q (h 0) * x) = -(ι Q (h 0) * (ι Q (h 2) * x)) := by
  rw [← mul_assoc, a20 horth, neg_mul, mul_assoc]
theorem r21 (x : A) : ι Q (h 2) * (ι Q (h 1) * x) = -(ι Q (h 1) * (ι Q (h 2) * x)) := by
  rw [← mul_assoc, a21 horth, neg_mul, mul_assoc]

end Table

/-- Normal-form simp set for words in $\iota(h_0), \iota(h_1), \iota(h_2)$ (sorting by anticommutation). -/
local macro "norm3 " ho:term : tactic =>
  `(tactic| simp only [mul_assoc, a10 $ho, a20 $ho, a21 $ho, r10 $ho, r20 $ho, r21 $ho, ι_sq', sq_r,
    mul_neg, neg_mul, smul_mul_assoc, mul_smul_comm, neg_smul, smul_neg, smul_smul, one_mul, mul_one,
    Algebra.algebraMap_eq_smul_one, map_add, map_smul, add_mul, mul_add, map_neg, neg_neg])

local notation "𝔟[" r ", " a ", " b ", " c "]" =>
  algebraMap F (CliffordAlgebra Q) r + a • g₀ Q h + b • g₁ Q h + c • g₂ Q h

theorem hspan3 (hspan : ∀ z : V, ∃ c : Fin 3 → F, z = ∑ i, c i • h i) (z : V) :
    ∃ a0 a1 a2 : F, z = a0 • h 0 + a1 • h 1 + a2 • h 2 := by
  obtain ⟨c, rfl⟩ := hspan z
  exact ⟨c 0, c 1, c 2, by simp [Fin.sum_univ_three]⟩

theorem B_congr {r r' s0 s0' s1 s1' s2 s2' : F} (e : r = r') (e0 : s0 = s0') (e1 : s1 = s1')
    (e2 : s2 = s2') : (𝔟[r, s0, s1, s2] : A) = 𝔟[r', s0', s1', s2'] := by
  subst e e0 e1 e2; rfl

theorem ι_mul_ι_B (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) (a0 a1 a2 b0 b1 b2 : F) :
    ι Q (a0 • h 0 + a1 • h 1 + a2 • h 2) * ι Q (b0 • h 0 + b1 • h 1 + b2 • h 2) =
      𝔟[a0 * b0 * Q (h 0) + a1 * b1 * Q (h 1) + a2 * b2 * Q (h 2), a1 * b2 - a2 * b1,
        a2 * b0 - a0 * b2, a0 * b1 - a1 * b0] := by
  simp only [g₀, g₁, g₂]
  norm3 horth
  module

theorem B_mul (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) (r s0 s1 s2 r' s0' s1' s2' : F) :
    (𝔟[r, s0, s1, s2] : A) * 𝔟[r', s0', s1', s2'] =
      𝔟[r * r' - s0 * s0' * (Q (h 1) * Q (h 2)) - s1 * s1' * (Q (h 2) * Q (h 0))
          - s2 * s2' * (Q (h 0) * Q (h 1)),
        r * s0' + s0 * r' + Q (h 0) * (s2 * s1' - s1 * s2'),
        r * s1' + s1 * r' + Q (h 1) * (s0 * s2' - s2 * s0'),
        r * s2' + s2 * r' + Q (h 2) * (s1 * s0' - s0 * s1')] := by
  simp only [g₀, g₁, g₂]
  norm3 horth
  module

theorem reverse_g₀ (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) :
    reverse (g₀ Q h) = -g₀ Q h := by
  simp only [g₀, reverse.map_mul, reverse_ι]; exact a21 horth

theorem reverse_g₁ (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) :
    reverse (g₁ Q h) = -g₁ Q h := by
  simp only [g₁, reverse.map_mul, reverse_ι]; rw [a20 horth, neg_neg]

theorem reverse_g₂ (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) :
    reverse (g₂ Q h) = -g₂ Q h := by
  simp only [g₂, reverse.map_mul, reverse_ι]; exact a10 horth

/-- **§7.3, p. 53**: $A^+(Z) = B = F + Fg_0 + Fg_1 + Fg_2$ when $\dim Z = 3$ (here $g_0 = h_1h_2$,
$g_1 = h_2h_0$, $g_2 = h_0h_1$; Shimura's $g_1,g_2,g_3$). -/
@[kb "shimura2004" "§7.3, p. 53 (dim Z = 3: A⁺(Z) = B = F + T)"]
theorem dim3_evenOdd_zero_iff (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 3 → F, z = ∑ i, c i • h i) (a : A) :
    a ∈ evenOdd Q 0 ↔ ∃ r s₀ s₁ s₂ : F,
      a = algebraMap F A r + s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h := by
  constructor
  · intro ha
    refine CliffordAlgebra.even_induction (Q := Q)
      (motive := fun x _ => ∃ r s₀ s₁ s₂ : F,
        x = algebraMap F A r + s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h) ?_ ?_ ?_ a ha
    · exact fun r => ⟨r, 0, 0, 0, by simp⟩
    · rintro x y - - ⟨r, s0, s1, s2, rfl⟩ ⟨r', s0', s1', s2', rfl⟩
      exact ⟨r + r', s0 + s0', s1 + s1', s2 + s2', by
        rw [map_add]; simp only [add_smul]; abel⟩
    · rintro m₁ m₂ x - ⟨r, s0, s1, s2, rfl⟩
      obtain ⟨a0, a1, a2, rfl⟩ := hspan3 hspan m₁
      obtain ⟨b0, b1, b2, rfl⟩ := hspan3 hspan m₂
      exact ⟨_, _, _, _, by rw [ι_mul_ι_B horth, B_mul horth]⟩
  · rintro ⟨r, s0, s1, s2, rfl⟩
    have hg : ∀ (m₁ m₂ : V), ι Q m₁ * ι Q m₂ ∈ evenOdd Q 0 := ι_mul_ι_mem_evenOdd_zero Q
    exact add_mem (add_mem (add_mem (algebraMap_mem_evenOdd_zero r)
      (Submodule.smul_mem _ s0 (hg _ _))) (Submodule.smul_mem _ s1 (hg _ _)))
      (Submodule.smul_mem _ s2 (hg _ _))

/-- $g_i^* = -g_i$, hence $(r + s_0g_0 + s_1g_1 + s_2g_2)^* = r - s_0g_0 - s_1g_1 - s_2g_2$: on $B$ the map
$a \mapsto a^*$ is the main involution of the quaternion algebra $B$. -/
@[kb "shimura2004" "§7.3, p. 53 (dim Z = 3: g_i* = −g_i, a ↦ a* is the main involution of B)"]
theorem dim3_reverse_B (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) (r s₀ s₁ s₂ : F) :
    reverse (algebraMap F A r + s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h) =
      algebraMap F A r + (-s₀) • g₀ Q h + (-s₁) • g₁ Q h + (-s₂) • g₂ Q h := by
  simp only [map_add, map_smul, reverse.commutes, reverse_g₀ horth, reverse_g₁ horth, reverse_g₂ horth,
    smul_neg, neg_smul]

/-- **§7.3, p. 53**: for $b = r + s_0g_0 + s_1g_1 + s_2g_2$, $bb^* = N(b) = r^2 + s_0^2c_1c_2 + s_1^2c_2c_0 +
s_2^2c_0c_1$, where $c_i = \varphi[h_i]$. -/
@[kb "shimura2004" "§7.3, p. 53 (dim Z = 3: bb* = N(b) = r² + s₀²c₁c₂ + s₁²c₂c₀ + s₂²c₀c₁)"]
theorem dim3_nu (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) (r s₀ s₁ s₂ : F) :
    (algebraMap F A r + s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h) *
        reverse (algebraMap F A r + s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h) =
      algebraMap F A (r ^ 2 + s₀ ^ 2 * (Q (h 1) * Q (h 2)) + s₁ ^ 2 * (Q (h 2) * Q (h 0))
        + s₂ ^ 2 * (Q (h 0) * Q (h 1))) := by
  rw [dim3_reverse_B horth, B_mul horth]
  have e : algebraMap F A (r ^ 2 + s₀ ^ 2 * (Q (h 1) * Q (h 2)) + s₁ ^ 2 * (Q (h 2) * Q (h 0))
        + s₂ ^ 2 * (Q (h 0) * Q (h 1))) =
      𝔟[r ^ 2 + s₀ ^ 2 * (Q (h 1) * Q (h 2)) + s₁ ^ 2 * (Q (h 2) * Q (h 0))
        + s₂ ^ 2 * (Q (h 0) * Q (h 1)), 0, 0, 0] := by simp
  rw [e]
  exact B_congr (by ring) (by ring) (by ring) (by ring)

/-- Same as `dim3_nu` in the other order: $b^*b = N(b)$. -/
@[kb "shimura2004" "§7.3, p. 53 (dim Z = 3: b*b = N(b))"]
theorem dim3_nu' (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) (r s₀ s₁ s₂ : F) :
    reverse (algebraMap F A r + s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h) *
        (algebraMap F A r + s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h) =
      algebraMap F A (r ^ 2 + s₀ ^ 2 * (Q (h 1) * Q (h 2)) + s₁ ^ 2 * (Q (h 2) * Q (h 0))
        + s₂ ^ 2 * (Q (h 0) * Q (h 1))) := by
  rw [dim3_reverse_B horth, B_mul horth]
  have e : algebraMap F A (r ^ 2 + s₀ ^ 2 * (Q (h 1) * Q (h 2)) + s₁ ^ 2 * (Q (h 2) * Q (h 0))
        + s₂ ^ 2 * (Q (h 0) * Q (h 1))) =
      𝔟[r ^ 2 + s₀ ^ 2 * (Q (h 1) * Q (h 2)) + s₁ ^ 2 * (Q (h 2) * Q (h 0))
        + s₂ ^ 2 * (Q (h 0) * Q (h 1)), 0, 0, 0] := by simp
  rw [e]
  exact B_congr (by ring) (by ring) (by ring) (by ring)

/-- $T$ consists of $*$-anti-fixed elements: $(s_0g_0 + s_1g_1 + s_2g_2)^* = -(s_0g_0 + s_1g_1 + s_2g_2)$. -/
theorem dim3_reverse_T (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) (s₀ s₁ s₂ : F) :
    reverse (s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h) = -(s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h) := by
  simp only [map_add, map_smul, reverse_g₀ horth, reverse_g₁ horth, reverse_g₂ horth, smul_neg, neg_add]

/-- If $b = r + t \in B$ ($t \in T$) satisfies $b^* = -b$, then $r = 0$, i.e. $b \in T$. -/
theorem dim3_reverse_eq_neg (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) {r s₀ s₁ s₂ : F}
    (hb : reverse (algebraMap F A r + s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h) =
      -(algebraMap F A r + s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h)) (hnz : Function.Injective (algebraMap F A)) :
    r = 0 := by
  rw [dim3_reverse_B horth] at hb
  have h2 : algebraMap F A r + (-s₀) • g₀ Q h + (-s₁) • g₁ Q h + (-s₂) • g₂ Q h +
      (algebraMap F A r + s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h) = 0 := by
    rw [hb]; abel
  have e : algebraMap F A (2 * r) = 0 := by
    have e1 : algebraMap F A (2 * r) = algebraMap F A r + (-s₀) • g₀ Q h + (-s₁) • g₁ Q h +
        (-s₂) • g₂ Q h + (algebraMap F A r + s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h) := by
      rw [two_mul, map_add]
      simp only [neg_smul]
      abel
    rw [e1, h2]
  have h2r : 2 * r = 0 := hnz (by rw [e, map_zero])
  exact (mul_eq_zero.1 h2r).resolve_left (isUnit_of_invertible (2 : F)).ne_zero

/-! #### The element $\zeta = h_0h_1h_2$ -/

/-- **§7.3, p. 53**: $\zeta^2 = -d$ with $d = c_0c_1c_2$. -/
@[kb "shimura2004" "§7.3, p. 53 (dim Z = 3: ζ² = −d, d = c₁c₂c₃)"]
theorem zeta_sq (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) :
    zeta Q h * zeta Q h = algebraMap F A (-(Q (h 0) * Q (h 1) * Q (h 2))) := by
  simp only [zeta]
  norm3 horth
  module

theorem zc0 (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) :
    zeta Q h * ι Q (h 0) = ι Q (h 0) * zeta Q h := by
  simp only [zeta]; norm3 horth
theorem zc1 (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) :
    zeta Q h * ι Q (h 1) = ι Q (h 1) * zeta Q h := by
  simp only [zeta]; norm3 horth
theorem zc2 (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) :
    zeta Q h * ι Q (h 2) = ι Q (h 2) * zeta Q h := by
  simp only [zeta]; norm3 horth

/-- **§7.3, p. 53**: $\zeta$ is central in $A(Z)$ (it commutes with every $\iota(h_i)$, which generate $A(Z)$). -/
@[kb "shimura2004" "§7.3, p. 53 (dim Z = 3: ζ is central in A(Z))"]
theorem zeta_comm (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 3 → F, z = ∑ i, c i • h i) (a : A) :
    zeta Q h * a = a * zeta Q h := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => exact (Algebra.commutes r _).symm
  | ι v =>
    obtain ⟨a0, a1, a2, rfl⟩ := hspan3 hspan v
    simp only [map_add, map_smul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, zc0 horth, zc1 horth,
      zc2 horth]
  | mul a b ha hb => rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]
  | add a b ha hb => rw [mul_add, add_mul, ha, hb]

/-- $\zeta^* = -\zeta$. -/
theorem reverse_zeta (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) :
    reverse (zeta Q h) = -zeta Q h := by
  simp only [zeta, reverse.map_mul, reverse_ι]
  norm3 horth

theorem zeta_mem_odd : zeta Q h ∈ evenOdd Q 1 := by
  have := mul_mem_evenOdd (ι_mul_ι_mem_evenOdd_zero Q (h 0) (h 1)) (ι_mem_evenOdd_one Q (h 2))
  simpa [zeta] using this

/-- **§7.3, p. 53**: $A^-(Z) = Z + F\zeta$ when $\dim Z = 3$ (so $A(Z) = B + B\zeta$ as $A = A^+ + A^-$). -/
@[kb "shimura2004" "§7.3, p. 53 (dim Z = 3: A⁻(Z) = Z + Fζ)"]
theorem dim3_evenOdd_one_iff (hh : ∀ i, Q (h i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 3 → F, z = ∑ i, c i • h i) (a : A) :
    a ∈ evenOdd Q 1 ↔ ∃ (v : V) (r : F), a = ι Q v + r • zeta Q h := by
  constructor
  · intro ha
    have he : ι Q (h 0) * a ∈ evenOdd Q 0 := by
      have := mul_mem_evenOdd (ι_mem_evenOdd_one Q (h 0)) ha
      simpa [show (1 : ZMod 2) + 1 = 0 from rfl] using this
    obtain ⟨r, s0, s1, s2, hb⟩ := (dim3_evenOdd_zero_iff horth hspan _).1 he
    have key : Q (h 0) • a =
        ι Q (r • h 0 + (Q (h 0) * s2) • h 1 + (-(Q (h 0) * s1)) • h 2) + s0 • zeta Q h := by
      rw [← sq_r 0 a, hb]
      simp only [g₀, g₁, g₂, zeta]
      norm3 horth
      module
    refine ⟨(Q (h 0))⁻¹ • (r • h 0 + (Q (h 0) * s2) • h 1 + (-(Q (h 0) * s1)) • h 2),
      (Q (h 0))⁻¹ * s0, ?_⟩
    calc a = (Q (h 0))⁻¹ • (Q (h 0) • a) := by rw [smul_smul, inv_mul_cancel₀ (hh 0), one_smul]
      _ = _ := by rw [key, smul_add, map_smul, smul_smul]
  · rintro ⟨v, r, rfl⟩
    exact add_mem (ι_mem_evenOdd_one Q v) (Submodule.smul_mem _ r zeta_mem_odd)

/-- **§7.3, p. 53**: $\{x \in A^-(Z) \mid x^* = x\} = \iota(Z)$ when $\dim Z = 3$ (as $\zeta^* = -\zeta$). -/
@[kb "shimura2004" "§7.3, p. 53 (dim Z = 3: {x ∈ A⁻(Z) | x* = x} = Z)"]
theorem dim3_odd_fixed_iff (hh : ∀ i, Q (h i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 3 → F, z = ∑ i, c i • h i) (a : A) :
    (a ∈ evenOdd Q 1 ∧ reverse a = a) ↔ ∃ v : V, a = ι Q v := by
  constructor
  · rintro ⟨ha, hfix⟩
    obtain ⟨v, r, rfl⟩ := (dim3_evenOdd_one_iff hh horth hspan _).1 ha
    refine ⟨v, ?_⟩
    rw [map_add, map_smul, reverse_ι, reverse_zeta horth, smul_neg] at hfix
    have h1 : -(r • zeta Q h) = r • zeta Q h := add_left_cancel hfix
    have h2 : r • zeta Q h = 0 := by
      have h3 : r • zeta Q h + r • zeta Q h = 0 := neg_eq_iff_add_eq_zero.1 h1
      rw [← two_smul F, smul_eq_zero] at h3
      exact h3.resolve_left (isUnit_of_invertible (2 : F)).ne_zero
    have h4 : (r • zeta Q h) * zeta Q h = 0 := by rw [h2, zero_mul]
    rw [smul_mul_assoc, zeta_sq horth, Algebra.smul_def, ← map_mul] at h4
    have h5 : r * -(Q (h 0) * Q (h 1) * Q (h 2)) = 0 := (algebraMap F A).injective (by rw [h4, map_zero])
    have hd : -(Q (h 0) * Q (h 1) * Q (h 2)) ≠ 0 :=
      neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (hh 0) (hh 1)) (hh 2))
    rw [(mul_eq_zero.1 h5).resolve_right hd, zero_smul, add_zero]
  · rintro ⟨v, rfl⟩
    exact ⟨ι_mem_evenOdd_one Q v, reverse_ι v⟩

/-! #### (7.2): $G^+(Z) = B^\times$ -/

/-- **(7.2), p. 53**: $G^+(Z) = B^\times$ when $\dim Z = 3$: a unit $u$ of $A(Z)$ lies in $G^+(Z)$ if and only if
it lies in $A^+(Z) = B$. -/
@[kb "shimura2004" "(7.2), p. 53 (dim Z = 3: G⁺(Z) = B^×)"]
theorem dim3_mem_M0_iff (hh : ∀ i, Q (h i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 3 → F, z = ∑ i, c i • h i) (u : Aˣ) :
    u ∈ M0 Q ↔ (u : A) ∈ evenOdd Q 0 := by
  refine ⟨fun hu => hu.1, fun hu => ?_⟩
  obtain ⟨r, s0, s1, s2, hb⟩ := (dim3_evenOdd_zero_iff horth hspan _).1 hu
  refine mem_M0_of_odd_fixed u hu (c := r ^ 2 + s0 ^ 2 * (Q (h 1) * Q (h 2)) + s1 ^ 2 * (Q (h 2) * Q (h 0))
        + s2 ^ 2 * (Q (h 0) * Q (h 1))) ?_ fun w hw hfix => ?_
  · rw [hb]; exact dim3_nu horth r s0 s1 s2
  · obtain ⟨v, hv⟩ := (dim3_odd_fixed_iff hh horth hspan w).1 ⟨hw, hfix⟩
    exact ⟨v, hv.symm⟩

/-- **§7.3, p. 53 (7.2)**: $G^1(Z) = \{b \in B^\times \mid bb^* = 1\}$ when $\dim Z = 3$. -/
@[kb "shimura2004" "(7.2), p. 53 (dim Z = 3: G¹(Z) = {b ∈ B^× | bb* = 1})"]
theorem dim3_mem_spinGroupG1_iff (hh : ∀ i, Q (h i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 3 → F, z = ∑ i, c i • h i) (u : Aˣ) :
    u ∈ spinGroupG1 Q ↔ (u : A) ∈ evenOdd Q 0 ∧ (u : A) * reverse (u : A) = 1 :=
  ⟨fun hu => ⟨hu.1.1, hu.2⟩, fun hu => ⟨(dim3_mem_M0_iff hh horth hspan u).2 hu.1, hu.2⟩⟩

/-- **§7.3, p. 53 (7.2)**: for $u \in G^+(Z) = B^\times$, $\nu(u) = uu^*$ is the scalar $N(u) = r^2 + s_0^2c_1c_2 +
s_1^2c_2c_0 + s_2^2c_0c_1$ for $u = r + s_0g_0 + s_1g_1 + s_2g_2$. -/
@[kb "shimura2004" "(7.2), p. 53 (dim Z = 3: ν(b) = bb*)"]
theorem dim3_nu_M0 (hh : ∀ i, Q (h i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 3 → F, z = ∑ i, c i • h i) (u : Aˣ) (hu : u ∈ M0 Q) :
    ∃ r s₀ s₁ s₂ : F, (u : A) = algebraMap F A r + s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h ∧
      (u : A) * reverse (u : A) = algebraMap F A (r ^ 2 + s₀ ^ 2 * (Q (h 1) * Q (h 2))
        + s₁ ^ 2 * (Q (h 2) * Q (h 0)) + s₂ ^ 2 * (Q (h 0) * Q (h 1))) := by
  obtain ⟨r, s0, s1, s2, hb⟩ := (dim3_evenOdd_zero_iff horth hspan _).1 hu.1
  exact ⟨r, s0, s1, s2, hb, by rw [hb]; exact dim3_nu horth r s0 s1 s2⟩

/-! #### $Z = T\zeta$ -/

theorem T_mul_zeta (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) (s0 s1 s2 : F) :
    (s0 • g₀ Q h + s1 • g₁ Q h + s2 • g₂ Q h) * zeta Q h =
      ι Q ((-(s0 * (Q (h 1) * Q (h 2)))) • h 0 + (-(s1 * (Q (h 2) * Q (h 0)))) • h 1
        + (-(s2 * (Q (h 0) * Q (h 1)))) • h 2) := by
  simp only [g₀, g₁, g₂, zeta]
  norm3 horth
  module

theorem zeta_vec_explicit (hh : ∀ i, Q (h i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) (a0 a1 a2 : F) :
    ι Q (a0 • h 0 + a1 • h 1 + a2 • h 2) =
      ((-(a0 * (Q (h 1) * Q (h 2))⁻¹)) • g₀ Q h + (-(a1 * (Q (h 2) * Q (h 0))⁻¹)) • g₁ Q h
        + (-(a2 * (Q (h 0) * Q (h 1))⁻¹)) • g₂ Q h) * zeta Q h := by
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  rw [T_mul_zeta horth]
  congr 1
  have e0 : -(-(a0 * (Q (h 1) * Q (h 2))⁻¹) * (Q (h 1) * Q (h 2))) = a0 := by field_simp
  have e1 : -(-(a1 * (Q (h 2) * Q (h 0))⁻¹) * (Q (h 2) * Q (h 0))) = a1 := by field_simp
  have e2 : -(-(a2 * (Q (h 0) * Q (h 1))⁻¹) * (Q (h 0) * Q (h 1))) = a2 := by field_simp
  rw [e0, e1, e2]

/-- **§7.3, p. 53**: $Z = T\zeta$: every vector $z$ has $\iota(z) = t\zeta$ for some $t \in T = Fg_0 + Fg_1 + Fg_2$. -/
@[kb "shimura2004" "§7.3, p. 53 (dim Z = 3: Z = Tζ)"]
theorem dim3_zeta_vec (hh : ∀ i, Q (h i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 3 → F, z = ∑ i, c i • h i) (z : V) :
    ∃ s₀ s₁ s₂ : F, ι Q z = (s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h) * zeta Q h := by
  obtain ⟨a0, a1, a2, rfl⟩ := hspan3 hspan z
  exact ⟨_, _, _, zeta_vec_explicit hh horth a0 a1 a2⟩

/-- **§7.3, p. 53**: $\varphi[x\zeta] = d\,xx^*$ for $x \in T$: if $\iota(z) = t\zeta$ with $t \in T$, then
$\varphi[z] = d\,tt^*$, $d = c_0c_1c_2$. -/
@[kb "shimura2004" "§7.3, p. 53 (dim Z = 3: φ[xζ] = d x x* for x ∈ T)"]
theorem dim3_Q_zeta (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 3 → F, z = ∑ i, c i • h i) (s₀ s₁ s₂ : F) (z : V)
    (hz : ι Q z = (s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h) * zeta Q h) :
    algebraMap F A (Q z) = algebraMap F A (Q (h 0) * Q (h 1) * Q (h 2)) *
      ((s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h) *
        reverse (s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h)) := by
  set t := s₀ • g₀ Q h + s₁ • g₁ Q h + s₂ • g₂ Q h with ht
  have hc := zeta_comm horth hspan t
  calc algebraMap F A (Q z) = ι Q z * ι Q z := (ι_sq_scalar Q z).symm
    _ = t * (zeta Q h * t) * zeta Q h := by rw [hz]; simp only [mul_assoc]
    _ = t * t * (zeta Q h * zeta Q h) := by rw [hc]; simp only [mul_assoc]
    _ = _ := by
      have hr : reverse t = -t := dim3_reverse_T horth s₀ s₁ s₂
      rw [zeta_sq horth, hr]
      simp only [map_neg, mul_neg]
      rw [Algebra.commutes]

/-! #### $\varphi$ anisotropic $\iff$ $B$ a division algebra -/

theorem T_even (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 3 → F, z = ∑ i, c i • h i) (s0 s1 s2 : F) :
    s0 • g₀ Q h + s1 • g₁ Q h + s2 • g₂ Q h ∈ evenOdd Q 0 :=
  (dim3_evenOdd_zero_iff horth hspan _).2 ⟨0, s0, s1, s2, by rw [map_zero, zero_add]⟩

theorem T_sq (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) (s0 s1 s2 : F) :
    (s0 • g₀ Q h + s1 • g₁ Q h + s2 • g₂ Q h) * (s0 • g₀ Q h + s1 • g₁ Q h + s2 • g₂ Q h) =
      algebraMap F A (-(s0 ^ 2 * (Q (h 1) * Q (h 2)) + s1 ^ 2 * (Q (h 2) * Q (h 0))
        + s2 ^ 2 * (Q (h 0) * Q (h 1)))) := by
  simp only [g₀, g₁, g₂]
  norm3 horth
  module

theorem T_anti (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) (s0 s1 s2 u0 u1 u2 : F) :
    (s0 • g₀ Q h + s1 • g₁ Q h + s2 • g₂ Q h) * (u0 • g₀ Q h + u1 • g₁ Q h + u2 • g₂ Q h) +
      (u0 • g₀ Q h + u1 • g₁ Q h + u2 • g₂ Q h) * (s0 • g₀ Q h + s1 • g₁ Q h + s2 • g₂ Q h) =
      algebraMap F A (-2 * (s0 * u0 * (Q (h 1) * Q (h 2)) + s1 * u1 * (Q (h 2) * Q (h 0))
        + s2 * u2 * (Q (h 0) * Q (h 1)))) := by
  simp only [g₀, g₁, g₂]
  norm3 horth
  module

theorem coeff_zero (hh : ∀ i, Q (h i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) {a0 a1 a2 : F}
    (hz : a0 • h 0 + a1 • h 1 + a2 • h 2 = 0) : a0 = 0 ∧ a1 = 0 ∧ a2 = 0 := by
  have e : ∀ j : Fin 3, (![a0, a1, a2] : Fin 3 → F) j * (2 * Q (h j)) = 0 := by
    intro j
    have h1 : QuadraticMap.polar Q (a0 • h 0 + a1 • h 1 + a2 • h 2) (h j) =
        (![a0, a1, a2] : Fin 3 → F) j * (2 * Q (h j)) := by
      have := polar_sum_right horth ![a0, a1, a2] j
      simpa [Fin.sum_univ_three] using this
    rw [hz, QuadraticMap.polar_zero_left] at h1
    exact h1.symm
  have h2 : (2 : F) ≠ 0 := (isUnit_of_invertible (2 : F)).ne_zero
  exact ⟨(mul_eq_zero.1 (e 0)).resolve_right (mul_ne_zero h2 (hh 0)),
    (mul_eq_zero.1 (e 1)).resolve_right (mul_ne_zero h2 (hh 1)),
    (mul_eq_zero.1 (e 2)).resolve_right (mul_ne_zero h2 (hh 2))⟩

theorem exists_perp (w0 w1 w2 : F) :
    ∃ a0 a1 a2 : F, (a0 ≠ 0 ∨ a1 ≠ 0 ∨ a2 ≠ 0) ∧ a0 * w0 + a1 * w1 + a2 * w2 = 0 := by
  by_cases h0 : w0 = 0
  · exact ⟨1, 0, 0, Or.inl one_ne_zero, by simp [h0]⟩
  · exact ⟨-w1, w0, 0, Or.inr (Or.inl h0), by ring⟩

/-- A nonzero $x \in T$ with $x^2 = 0$ gives an isotropic vector ($\iota(z) = x\zeta$, $\varphi[z] = d\,xx^* = 0$). -/
theorem iso_of_T (hh : ∀ i, Q (h i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 3 → F, z = ∑ i, c i • h i) {x0 x1 x2 : F}
    (hx0 : x0 • g₀ Q h + x1 • g₁ Q h + x2 • g₂ Q h ≠ 0)
    (hxx : (x0 • g₀ Q h + x1 • g₁ Q h + x2 • g₂ Q h) * (x0 • g₀ Q h + x1 • g₁ Q h + x2 • g₂ Q h) = 0) :
    ∃ z : V, z ≠ 0 ∧ Q z = 0 := by
  have hd0 : Q (h 0) * Q (h 1) * Q (h 2) ≠ 0 := mul_ne_zero (mul_ne_zero (hh 0) (hh 1)) (hh 2)
  refine ⟨(-(x0 * (Q (h 1) * Q (h 2)))) • h 0 + (-(x1 * (Q (h 2) * Q (h 0)))) • h 1
    + (-(x2 * (Q (h 0) * Q (h 1)))) • h 2, ?_, ?_⟩
  · intro hz
    have h1 := T_mul_zeta horth x0 x1 x2
    rw [hz, map_zero] at h1
    apply hx0
    have h2 : (x0 • g₀ Q h + x1 • g₁ Q h + x2 • g₂ Q h) * zeta Q h * zeta Q h = 0 := by
      rw [h1, zero_mul]
    rw [mul_assoc, zeta_sq horth, ← Algebra.commutes, ← Algebra.smul_def] at h2
    exact (smul_eq_zero.1 h2).resolve_left (neg_ne_zero.2 hd0)
  · have hq := dim3_Q_zeta horth hspan x0 x1 x2 _ (T_mul_zeta horth x0 x1 x2).symm
    rw [dim3_reverse_T horth, mul_neg, hxx, neg_zero, mul_zero] at hq
    exact (algebraMap F A).injective (by rw [hq, map_zero])

/-- **§7.3, p. 53**, "if $B$ is a division algebra then $\varphi$ is anisotropic" direction: a nonzero isotropic
vector $z = $ (via $\iota(z) = t\zeta$) would give a nonzero element $t \in B$ with $tt^* = 0$, not a unit. -/
theorem dim3_anisotropic_of_isUnit (hh : ∀ i, Q (h i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 3 → F, z = ∑ i, c i • h i)
    (hdiv : ∀ b : A, b ∈ evenOdd Q 0 → b ≠ 0 → IsUnit b) (z : V) (hz : z ≠ 0) : Q z ≠ 0 := by
  intro hQ
  obtain ⟨s0, s1, s2, hz'⟩ := dim3_zeta_vec hh horth hspan z
  obtain ⟨t, ht⟩ : ∃ t : A, t = s0 • g₀ Q h + s1 • g₁ Q h + s2 • g₂ Q h := ⟨_, rfl⟩
  have hq := dim3_Q_zeta horth hspan s0 s1 s2 z hz'
  rw [← ht] at hz' hq
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hz'
    exact hz (eq_zero_of_ι_eq_zero hh horth hspan hz')
  have hu := hdiv t (ht ▸ T_even horth hspan s0 s1 s2) ht0
  rw [hQ, map_zero] at hq
  have hd : IsUnit (algebraMap F A (Q (h 0) * Q (h 1) * Q (h 2))) :=
    (isUnit_iff_ne_zero.2 (mul_ne_zero (mul_ne_zero (hh 0) (hh 1)) (hh 2))).map _
  have h1 : t * reverse t = 0 := hd.mul_right_eq_zero.1 hq.symm
  have h2 : reverse t = 0 := hu.mul_right_eq_zero.1 h1
  apply ht0
  rw [← reverse_reverse t, h2, map_zero]

/-- Algebraic core of the converse: if $s, t$ anticommute, $s^2 = \kappa$ and $t^2 = r^2$ are scalars, then
$x = st + rs$ satisfies $x^2 = 0$. -/
theorem sq_zero_aux {s t : A} {r κ : F} (hts : t * s = -(s * t)) (hss : s * s = algebraMap F A κ)
    (htt : t * t = algebraMap F A (r ^ 2)) : (s * t + r • s) * (s * t + r • s) = 0 := by
  have a1 : s * t * (s * t) = -(algebraMap F A (κ * r ^ 2)) := by
    calc s * t * (s * t) = s * (t * s) * t := by simp only [mul_assoc]
      _ = -(s * s * (t * t)) := by rw [hts]; simp only [mul_neg, neg_mul, mul_assoc]
      _ = -(algebraMap F A (κ * r ^ 2)) := by rw [hss, htt, ← map_mul]
  have a2 : s * t * s = -(s * s * t) := by
    rw [mul_assoc, hts]; simp only [mul_neg, mul_assoc]
  have a3 : s * (s * t) = s * s * t := (mul_assoc _ _ _).symm
  have e : (s * t + r • s) * (s * t + r • s) =
      s * t * (s * t) + r • (s * t * s) + r • (s * (s * t)) + (r * r) • (s * s) := by
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
    module
  have e2 : algebraMap F A (κ * r ^ 2) = (r * r) • algebraMap F A κ := by
    rw [Algebra.smul_def, ← map_mul]; congr 1; ring
  rw [e, a1, a2, a3, hss, smul_neg, e2]
  abel

/-- **§7.3, p. 53**, "if $\varphi$ is anisotropic then $B$ is a division algebra" direction: every nonzero element
of $B$ is a unit. If $N(b) \ne 0$ then $b^{-1} = N(b)^{-1}b^*$; if $N(b) = 0$, pick $s \in T$ nonzero anticommuting
with the pure part $t$ of $b$ (one linear condition on three unknowns); then $x = st + rs \in T$ has $x^2 = 0$
and $x \ne 0$ (or $s^2 = 0$ and $s$ itself works), giving an isotropic vector. -/
theorem dim3_isUnit_of_anisotropic (hh : ∀ i, Q (h i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 3 → F, z = ∑ i, c i • h i)
    (hanis : ∀ z : V, z ≠ 0 → Q z ≠ 0) {b : A} (hb : b ∈ evenOdd Q 0) (hb0 : b ≠ 0) : IsUnit b := by
  obtain ⟨r, τ0, τ1, τ2, hbe⟩ := (dim3_evenOdd_zero_iff horth hspan b).1 hb
  by_cases hN : r ^ 2 + τ0 ^ 2 * (Q (h 1) * Q (h 2)) + τ1 ^ 2 * (Q (h 2) * Q (h 0))
      + τ2 ^ 2 * (Q (h 0) * Q (h 1)) = 0
  swap
  · refine ⟨⟨b, (r ^ 2 + τ0 ^ 2 * (Q (h 1) * Q (h 2)) + τ1 ^ 2 * (Q (h 2) * Q (h 0))
      + τ2 ^ 2 * (Q (h 0) * Q (h 1)))⁻¹ • reverse b, ?_, ?_⟩, rfl⟩
    · rw [mul_smul_comm, hbe, dim3_nu horth, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hN, map_one]
    · rw [smul_mul_assoc, hbe, dim3_nu' horth, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hN, map_one]
  exfalso
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  obtain ⟨a0, a1, a2, hne, hperp⟩ := exists_perp τ0 τ1 τ2
  have hz0 : a0 • h 0 + a1 • h 1 + a2 • h 2 ≠ 0 := by
    intro hz
    obtain ⟨e0, e1, e2⟩ := coeff_zero hh horth hz
    rcases hne with h | h | h <;> contradiction
  have hs := zeta_vec_explicit hh horth a0 a1 a2
  obtain ⟨s0, hs0⟩ : ∃ s0 : F, s0 = -(a0 * (Q (h 1) * Q (h 2))⁻¹) := ⟨_, rfl⟩
  obtain ⟨s1, hs1⟩ : ∃ s1 : F, s1 = -(a1 * (Q (h 2) * Q (h 0))⁻¹) := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ s2 : F, s2 = -(a2 * (Q (h 0) * Q (h 1))⁻¹) := ⟨_, rfl⟩
  rw [← hs0, ← hs1, ← hs2] at hs
  obtain ⟨s, hsd⟩ : ∃ s : A, s = s0 • g₀ Q h + s1 • g₁ Q h + s2 • g₂ Q h := ⟨_, rfl⟩
  obtain ⟨t, htd⟩ : ∃ t : A, t = τ0 • g₀ Q h + τ1 • g₁ Q h + τ2 • g₂ Q h := ⟨_, rfl⟩
  have hbt : b = algebraMap F A r + t := by rw [hbe, htd]; abel
  rw [← hsd] at hs
  have hs_ne : s ≠ 0 := by
    intro h0'
    rw [h0', zero_mul] at hs
    exact hz0 (eq_zero_of_ι_eq_zero hh horth hspan hs)
  have hsc : -2 * (s0 * τ0 * (Q (h 1) * Q (h 2)) + s1 * τ1 * (Q (h 2) * Q (h 0))
      + s2 * τ2 * (Q (h 0) * Q (h 1))) = 0 := by
    have e : -2 * (s0 * τ0 * (Q (h 1) * Q (h 2)) + s1 * τ1 * (Q (h 2) * Q (h 0))
        + s2 * τ2 * (Q (h 0) * Q (h 1))) = 2 * (a0 * τ0 + a1 * τ1 + a2 * τ2) := by
      rw [hs0, hs1, hs2]; field_simp <;> ring
    rw [e, hperp, mul_zero]
  have hanti : s * t + t * s = 0 := by
    rw [hsd, htd, T_anti horth, hsc, map_zero]
  have hts : t * s = -(s * t) := eq_neg_of_add_eq_zero_right hanti
  have hss : s * s = algebraMap F A (-(s0 ^ 2 * (Q (h 1) * Q (h 2)) + s1 ^ 2 * (Q (h 2) * Q (h 0))
      + s2 ^ 2 * (Q (h 0) * Q (h 1)))) := by rw [hsd]; exact T_sq horth s0 s1 s2
  have htt : t * t = algebraMap F A (r ^ 2) := by
    rw [htd, T_sq horth]
    congr 1
    linear_combination (-1 : F) * hN
  by_cases hnS : s0 ^ 2 * (Q (h 1) * Q (h 2)) + s1 ^ 2 * (Q (h 2) * Q (h 0))
      + s2 ^ 2 * (Q (h 0) * Q (h 1)) = 0
  · -- s itself is an isotropic element of T
    rw [hnS, neg_zero, map_zero] at hss
    obtain ⟨z, hz, hQ⟩ := iso_of_T hh horth hspan (x0 := s0) (x1 := s1) (x2 := s2)
      (hsd ▸ hs_ne) (hsd ▸ hss)
    exact hanis z hz hQ
  · -- x = st + rs
    have hse : s ∈ evenOdd Q 0 := hsd ▸ T_even horth hspan s0 s1 s2
    have hte : t ∈ evenOdd Q 0 := htd ▸ T_even horth hspan τ0 τ1 τ2
    have hxe : s * t + r • s ∈ evenOdd Q 0 := by
      refine add_mem ?_ (Submodule.smul_mem _ r hse)
      simpa using mul_mem_evenOdd hse hte
    obtain ⟨r', x0, x1, x2, hxf⟩ := (dim3_evenOdd_zero_iff horth hspan _).1 hxe
    have hrs : reverse s = -s := by rw [hsd]; simpa using dim3_reverse_T horth s0 s1 s2
    have hrt : reverse t = -t := by rw [htd]; simpa using dim3_reverse_T horth τ0 τ1 τ2
    have hrev : reverse (s * t + r • s) = -(s * t + r • s) := by
      rw [map_add, reverse.map_mul, map_smul, hrs, hrt, neg_mul_neg, hts, smul_neg]
      abel
    have hr' : r' = 0 := by
      refine dim3_reverse_eq_neg horth (r := r') (s₀ := x0) (s₁ := x1) (s₂ := x2) ?_ (algebraMap F A).injective
      rw [← hxf]; exact hrev
    subst hr'
    have hxT : s * t + r • s = x0 • g₀ Q h + x1 • g₁ Q h + x2 • g₂ Q h := by
      rw [hxf, map_zero, zero_add]
    have hxx := sq_zero_aux hts hss htt
    have hx0 : s * t + r • s ≠ 0 := by
      intro hx
      have e : s * (s * t + r • s) = algebraMap F A (-(s0 ^ 2 * (Q (h 1) * Q (h 2))
          + s1 ^ 2 * (Q (h 2) * Q (h 0)) + s2 ^ 2 * (Q (h 0) * Q (h 1)))) * b := by
        calc s * (s * t + r • s) = s * (s * t) + s * (r • s) := mul_add _ _ _
          _ = algebraMap F A (-(s0 ^ 2 * (Q (h 1) * Q (h 2)) + s1 ^ 2 * (Q (h 2) * Q (h 0))
              + s2 ^ 2 * (Q (h 0) * Q (h 1)))) * t +
              r • algebraMap F A (-(s0 ^ 2 * (Q (h 1) * Q (h 2)) + s1 ^ 2 * (Q (h 2) * Q (h 0))
              + s2 ^ 2 * (Q (h 0) * Q (h 1)))) := by
            rw [← mul_assoc, hss, mul_smul_comm, hss]
          _ = _ := by
            rw [hbt, mul_add, Algebra.smul_def, add_comm]
            congr 1
            exact Algebra.commutes _ _
      rw [hx, mul_zero] at e
      have hk : algebraMap F A (-(s0 ^ 2 * (Q (h 1) * Q (h 2)) + s1 ^ 2 * (Q (h 2) * Q (h 0))
          + s2 ^ 2 * (Q (h 0) * Q (h 1)))) ≠ 0 := by
        intro h0'
        exact hnS (neg_eq_zero.1 ((algebraMap F A).injective (by rw [h0', map_zero])))
      have hku : IsUnit (algebraMap F A (-(s0 ^ 2 * (Q (h 1) * Q (h 2)) + s1 ^ 2 * (Q (h 2) * Q (h 0))
          + s2 ^ 2 * (Q (h 0) * Q (h 1))))) :=
        (isUnit_iff_ne_zero.2 (neg_ne_zero.2 hnS)).map _
      exact hb0 (hku.mul_right_eq_zero.1 e.symm)
    obtain ⟨z, hz, hQ⟩ := iso_of_T hh horth hspan (x0 := x0) (x1 := x1) (x2 := x2)
      (hxT ▸ hx0) (hxT ▸ hxx)
    exact hanis z hz hQ

/-- **§7.3, p. 53**: $\varphi$ is anisotropic if and only if $B = A^+(Z)$ is a division algebra (every nonzero
element of $B$ is invertible). -/
@[kb "shimura2004" "§7.3, p. 53 (dim Z = 3: φ anisotropic ⟺ B is a division algebra)"]
theorem dim3_anisotropic_iff (hh : ∀ i, Q (h i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 3 → F, z = ∑ i, c i • h i) :
    (∀ z : V, z ≠ 0 → Q z ≠ 0) ↔ ∀ b : A, b ∈ evenOdd Q 0 → b ≠ 0 → IsUnit b :=
  ⟨fun hanis _ hb hb0 => dim3_isUnit_of_anisotropic hh horth hspan hanis hb hb0,
    fun hdiv z hz => dim3_anisotropic_of_isUnit hh horth hspan hdiv z hz⟩

end Dim3

/-! ### §7.4: dimension 4, formulas (7.3a) and (7.3b) -/

section Dim4

variable {h : Fin 4 → V}

section Table4

variable (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
include horth

theorem b10 : ι Q (h 1) * ι Q (h 0) = -(ι Q (h 0) * ι Q (h 1)) := ι_anti horth (by decide)
theorem b20 : ι Q (h 2) * ι Q (h 0) = -(ι Q (h 0) * ι Q (h 2)) := ι_anti horth (by decide)
theorem b21 : ι Q (h 2) * ι Q (h 1) = -(ι Q (h 1) * ι Q (h 2)) := ι_anti horth (by decide)
theorem b30 : ι Q (h 3) * ι Q (h 0) = -(ι Q (h 0) * ι Q (h 3)) := ι_anti horth (by decide)
theorem b31 : ι Q (h 3) * ι Q (h 1) = -(ι Q (h 1) * ι Q (h 3)) := ι_anti horth (by decide)
theorem b32 : ι Q (h 3) * ι Q (h 2) = -(ι Q (h 2) * ι Q (h 3)) := ι_anti horth (by decide)

theorem q10 (x : A) : ι Q (h 1) * (ι Q (h 0) * x) = -(ι Q (h 0) * (ι Q (h 1) * x)) := by
  rw [← mul_assoc, b10 horth, neg_mul, mul_assoc]
theorem q20 (x : A) : ι Q (h 2) * (ι Q (h 0) * x) = -(ι Q (h 0) * (ι Q (h 2) * x)) := by
  rw [← mul_assoc, b20 horth, neg_mul, mul_assoc]
theorem q21 (x : A) : ι Q (h 2) * (ι Q (h 1) * x) = -(ι Q (h 1) * (ι Q (h 2) * x)) := by
  rw [← mul_assoc, b21 horth, neg_mul, mul_assoc]
theorem q30 (x : A) : ι Q (h 3) * (ι Q (h 0) * x) = -(ι Q (h 0) * (ι Q (h 3) * x)) := by
  rw [← mul_assoc, b30 horth, neg_mul, mul_assoc]
theorem q31 (x : A) : ι Q (h 3) * (ι Q (h 1) * x) = -(ι Q (h 1) * (ι Q (h 3) * x)) := by
  rw [← mul_assoc, b31 horth, neg_mul, mul_assoc]
theorem q32 (x : A) : ι Q (h 3) * (ι Q (h 2) * x) = -(ι Q (h 2) * (ι Q (h 3) * x)) := by
  rw [← mul_assoc, b32 horth, neg_mul, mul_assoc]

end Table4

/-- Normal-form simp set for words in $\iota(h_0), \dots, \iota(h_3)$ (sorting by anticommutation). -/
local macro "norm4 " ho:term : tactic =>
  `(tactic| simp only [mul_assoc, b10 $ho, b20 $ho, b21 $ho, b30 $ho, b31 $ho, b32 $ho, q10 $ho, q20 $ho,
    q21 $ho, q30 $ho, q31 $ho, q32 $ho, ι_sq', sq_r, mul_neg, neg_mul, smul_mul_assoc, mul_smul_comm,
    neg_smul, smul_neg, smul_smul, one_mul, mul_one, map_add, map_smul, add_mul, mul_add, map_neg, neg_neg])

theorem hspan4 (hspan : ∀ z : V, ∃ c : Fin 4 → F, z = ∑ i, c i • h i) (z : V) :
    ∃ a0 a1 a2 a3 : F, z = a0 • h 0 + a1 • h 1 + a2 • h 2 + a3 • h 3 := by
  obtain ⟨c, rfl⟩ := hspan z
  exact ⟨c 0, c 1, c 2, c 3, by simp [Fin.sum_univ_four]⟩

omit [FiniteDimensional F V] in
/-- The eight even monomials $1,\ h_ih_j\ (i<j),\ h_0h_1h_2h_3$ spanning $A^+(V)$ (dim 4). -/
def genE (Q : QuadraticForm F V) (h : Fin 4 → V) : Set (CliffordAlgebra Q) :=
  {1, ι Q (h 0) * ι Q (h 1), ι Q (h 0) * ι Q (h 2), ι Q (h 0) * ι Q (h 3), ι Q (h 1) * ι Q (h 2),
    ι Q (h 1) * ι Q (h 3), ι Q (h 2) * ι Q (h 3), ι Q (h 0) * (ι Q (h 1) * (ι Q (h 2) * ι Q (h 3)))}

omit [FiniteDimensional F V] in
/-- The eight odd monomials $h_i$ and $h_ih_jh_k\ (i<j<k)$ spanning $A^-(V)$ (dim 4). -/
def genW (Q : QuadraticForm F V) (h : Fin 4 → V) : Set (CliffordAlgebra Q) :=
  {ι Q (h 0), ι Q (h 1), ι Q (h 2), ι Q (h 3), ι Q (h 0) * (ι Q (h 1) * ι Q (h 2)),
    ι Q (h 0) * (ι Q (h 1) * ι Q (h 3)), ι Q (h 0) * (ι Q (h 2) * ι Q (h 3)),
    ι Q (h 1) * (ι Q (h 2) * ι Q (h 3))}

/-- Solve goals `x ∈ span (genE ∪ genW)` for `x = ± c • generator`. -/
local macro "memtac" : tactic =>
  `(tactic| repeat' first | apply neg_mem | apply Submodule.smul_mem | exact Submodule.subset_span (by simp [genE, genW]))

theorem mul_genW (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) {g : A}
    (hg : g ∈ genW Q h) :
    ι Q (h 0) * g ∈ Submodule.span F (genE Q h) ∧ ι Q (h 1) * g ∈ Submodule.span F (genE Q h) ∧
    ι Q (h 2) * g ∈ Submodule.span F (genE Q h) ∧ ι Q (h 3) * g ∈ Submodule.span F (genE Q h) := by
  simp only [genW, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (try norm4 horth) <;> memtac

theorem mul_genE (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) {g : A}
    (hg : g ∈ genE Q h) :
    ι Q (h 0) * g ∈ Submodule.span F (genW Q h) ∧ ι Q (h 1) * g ∈ Submodule.span F (genW Q h) ∧
    ι Q (h 2) * g ∈ Submodule.span F (genW Q h) ∧ ι Q (h 3) * g ∈ Submodule.span F (genW Q h) := by
  simp only [genE, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (try norm4 horth) <;> memtac

theorem ιmul_W (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) (a0 a1 a2 a3 : F) {x : A}
    (hx : x ∈ Submodule.span F (genW Q h)) :
    ι Q (a0 • h 0 + a1 • h 1 + a2 • h 2 + a3 • h 3) * x ∈ Submodule.span F (genE Q h) := by
  induction hx using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨c0, c1, c2, c3⟩ := mul_genW horth hg
    simp only [map_add, map_smul, add_mul, smul_mul_assoc]
    exact add_mem (add_mem (add_mem (Submodule.smul_mem _ _ c0) (Submodule.smul_mem _ _ c1))
      (Submodule.smul_mem _ _ c2)) (Submodule.smul_mem _ _ c3)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem ιmul_E (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) (a0 a1 a2 a3 : F) {x : A}
    (hx : x ∈ Submodule.span F (genE Q h)) :
    ι Q (a0 • h 0 + a1 • h 1 + a2 • h 2 + a3 • h 3) * x ∈ Submodule.span F (genW Q h) := by
  induction hx using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨c0, c1, c2, c3⟩ := mul_genE horth hg
    simp only [map_add, map_smul, add_mul, smul_mul_assoc]
    exact add_mem (add_mem (add_mem (Submodule.smul_mem _ _ c0) (Submodule.smul_mem _ _ c1))
      (Submodule.smul_mem _ _ c2)) (Submodule.smul_mem _ _ c3)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

/-- Every odd element lies in the span of the four vectors $\iota(h_i)$ and the four triple products. -/
theorem dim4_odd_mem_W (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 4 → F, z = ∑ i, c i • h i) {a : A} (ha : a ∈ evenOdd Q 1) :
    a ∈ Submodule.span F (genW Q h) := by
  refine CliffordAlgebra.odd_induction (Q := Q) (P := fun x _ => x ∈ Submodule.span F (genW Q h))
    ?_ ?_ ?_ a ha
  · intro v
    obtain ⟨a0, a1, a2, a3, rfl⟩ := hspan4 hspan v
    simp only [map_add, map_smul]
    exact add_mem (add_mem (add_mem
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [genW])))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [genW]))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [genW]))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [genW])))
  · intro x y _ _ hx hy
    exact add_mem hx hy
  · intro m₁ m₂ x _ hx
    obtain ⟨a0, a1, a2, a3, rfl⟩ := hspan4 hspan m₁
    obtain ⟨b0, b1, b2, b3, rfl⟩ := hspan4 hspan m₂
    rw [mul_assoc]
    exact ιmul_E horth _ _ _ _ (ιmul_W horth _ _ _ _ hx)

theorem W_form {a : A} (ha : a ∈ Submodule.span F (genW Q h)) :
    ∃ (v : V) (y0 y1 y2 y3 : F), a = ι Q v + y0 • (ι Q (h 0) * (ι Q (h 1) * ι Q (h 2)))
      + y1 • (ι Q (h 0) * (ι Q (h 1) * ι Q (h 3))) + y2 • (ι Q (h 0) * (ι Q (h 2) * ι Q (h 3)))
      + y3 • (ι Q (h 1) * (ι Q (h 2) * ι Q (h 3))) := by
  induction ha using Submodule.span_induction with
  | mem g hg =>
    simp only [genW, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨h 0, 0, 0, 0, 0, by simp⟩
    · exact ⟨h 1, 0, 0, 0, 0, by simp⟩
    · exact ⟨h 2, 0, 0, 0, 0, by simp⟩
    · exact ⟨h 3, 0, 0, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, 0, 0, by simp⟩
    · exact ⟨0, 0, 1, 0, 0, by simp⟩
    · exact ⟨0, 0, 0, 1, 0, by simp⟩
    · exact ⟨0, 0, 0, 0, 1, by simp⟩
  | zero => exact ⟨0, 0, 0, 0, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨v, y0, y1, y2, y3, rfl⟩ := hx
    obtain ⟨v', y0', y1', y2', y3', rfl⟩ := hy
    exact ⟨v + v', y0 + y0', y1 + y1', y2 + y2', y3 + y3', by simp only [map_add, add_smul]; module⟩
  | smul c x _ hx =>
    obtain ⟨v, y0, y1, y2, y3, rfl⟩ := hx
    exact ⟨c • v, c * y0, c * y1, c * y2, c * y3, by simp only [map_smul, mul_smul]; module⟩

theorem reverse_t012 (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) :
    reverse (ι Q (h 0) * (ι Q (h 1) * ι Q (h 2))) = -(ι Q (h 0) * (ι Q (h 1) * ι Q (h 2))) := by
  simp only [reverse.map_mul, reverse_ι]; norm4 horth
theorem reverse_t013 (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) :
    reverse (ι Q (h 0) * (ι Q (h 1) * ι Q (h 3))) = -(ι Q (h 0) * (ι Q (h 1) * ι Q (h 3))) := by
  simp only [reverse.map_mul, reverse_ι]; norm4 horth
theorem reverse_t023 (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) :
    reverse (ι Q (h 0) * (ι Q (h 2) * ι Q (h 3))) = -(ι Q (h 0) * (ι Q (h 2) * ι Q (h 3))) := by
  simp only [reverse.map_mul, reverse_ι]; norm4 horth
theorem reverse_t123 (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) :
    reverse (ι Q (h 1) * (ι Q (h 2) * ι Q (h 3))) = -(ι Q (h 1) * (ι Q (h 2) * ι Q (h 3))) := by
  simp only [reverse.map_mul, reverse_ι]; norm4 horth

/-- **(7.3a)**, p. 54: $V = \{x \in A^-(V) \mid x^* = x\}$ when $\dim V = 4$ (here $V$ is identified with
$\iota(V) \subseteq A(V)$). $A^-(V)$ is spanned by the $h_i$ and the triple products $h_ih_jh_k$, which satisfy
$(h_ih_jh_k)^* = -h_ih_jh_k$. -/
@[kb "shimura2004" "(7.3a), p. 54 (dim V = 4: V = {x ∈ A⁻(V) | x* = x})"]
theorem dim4_odd_fixed_iff (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 4 → F, z = ∑ i, c i • h i) (a : A) :
    (a ∈ evenOdd Q 1 ∧ reverse a = a) ↔ ∃ v : V, a = ι Q v := by
  constructor
  · rintro ⟨ha, hfix⟩
    obtain ⟨v, y0, y1, y2, y3, hform⟩ := W_form (dim4_odd_mem_W horth hspan ha)
    refine ⟨v, ?_⟩
    obtain ⟨T, hT⟩ : ∃ T : A, T = y0 • (ι Q (h 0) * (ι Q (h 1) * ι Q (h 2)))
      + y1 • (ι Q (h 0) * (ι Q (h 1) * ι Q (h 3))) + y2 • (ι Q (h 0) * (ι Q (h 2) * ι Q (h 3)))
      + y3 • (ι Q (h 1) * (ι Q (h 2) * ι Q (h 3))) := ⟨_, rfl⟩
    have ha' : a = ι Q v + T := by rw [hform, hT]; abel
    have hrT : reverse T = -T := by
      rw [hT]
      simp only [map_add, map_smul, reverse_t012 horth, reverse_t013 horth, reverse_t023 horth,
        reverse_t123 horth, smul_neg, neg_add]
    rw [ha', map_add, reverse_ι, hrT] at hfix
    have h1 : -T = T := add_left_cancel hfix
    have h3 : T + T = 0 := neg_eq_iff_add_eq_zero.1 h1
    rw [← two_smul F, smul_eq_zero] at h3
    have hT0 : T = 0 := h3.resolve_left (isUnit_of_invertible (2 : F)).ne_zero
    rw [ha', hT0, add_zero]
  · rintro ⟨v, rfl⟩
    exact ⟨ι_mem_evenOdd_one Q v, reverse_ι v⟩

/-- **(7.3b)**, p. 54: $G^+(V) = \{x \in A^+(V)^\times \mid xx^* \in F^\times\}$ when $\dim V = 4$: a unit $u$ of
$A(V)$ lies in $G^+(V)$ if and only if $u \in A^+(V)$ and $uu^* \in F$ (it is then automatically in $F^\times$, as
$u$ is a unit). -/
@[kb "shimura2004" "(7.3b), p. 54 (dim V = 4: G⁺(V) = {x ∈ A⁺(V)^× | xx* ∈ F^×})"]
theorem dim4_mem_M0_iff (hh : ∀ i, Q (h i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 4 → F, z = ∑ i, c i • h i) (u : Aˣ) :
    u ∈ M0 Q ↔ (u : A) ∈ evenOdd Q 0 ∧ ∃ c : F, (u : A) * reverse (u : A) = algebraMap F A c := by
  constructor
  · intro hu
    obtain ⟨c, -, hc⟩ := M0_mul_reverse (nondegenerate_of_orthogonal hh horth hspan) ⟨u, hu⟩
    exact ⟨hu.1, c, hc⟩
  · rintro ⟨hu, c, hc⟩
    refine mem_M0_of_odd_fixed u hu hc fun w hw hf => ?_
    obtain ⟨v, hv⟩ := (dim4_odd_fixed_iff horth hspan w).1 ⟨hw, hf⟩
    exact ⟨v, hv.symm⟩

end Dim4

end LowDim

end QuadFormsKB.Shimura2004
