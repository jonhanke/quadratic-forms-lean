/-
# Shimura 2004, §7.1–§7.2: the Clifford groups in dimensions 1 and 2

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), §7.1 (printed p. 52) and §7.2,
formula (7.1) (printed pp. 52–53; wave 6 corrected the tags, which read pp. 41–42). Page numbers in the tags are printed pages.

**Setting and dictionary.** As in `CliffordGroups.lean`: $F$ a field of characteristic $\ne 2$ (`Invertible (2 : F)`),
`Q : QuadraticForm F V` with $Q(x) = \varphi[x]$, $A(Z)$ = `CliffordAlgebra Q` for $Z = (V, \varphi)$, $A^\pm(Z)$ =
`evenOdd Q 0`, `evenOdd Q 1`, $a \mapsto a^*$ = `reverse`, $G(Z)$ = `Cassels.cliffordGroup Q`, $G^+(Z)$ = `M0 Q`,
$G^-(Z)$ = `cliffordGroupOdd Q`, $G^1(Z)$ = `spinGroupG1 Q`, $\tau$ = `tau` (with $x\tau(a) = a^{-1}xa$, written
`tau a x`). A group of units $u \in A(Z)^\times$ is stated through its value `(u : CliffordAlgebra Q)`.

*Dimension 1* (§7.1): $Z = Fh$ with $\varphi[h] \ne 0$, hypotheses `hh : Q h ≠ 0`, `hspan : ∀ z, ∃ c, z = c • h`.
*Dimension 2* (§7.2): $Z = Fg + Fh$ with $\varphi[g]\varphi[h] \ne 0$ and $\varphi(g, h) = 0$ (so $gh = -hg$),
hypotheses `hg`, `hh`, `hgh : QuadraticMap.polar Q g h = 0`, `hspan : ∀ z, ∃ x y, z = x • g + y • h`. We put
$z = gh$ (`ι Q g * ι Q h`) and $K = F + Fz$.

**Proves** (all unconditional; standard axioms only)
* §7.1: $A^+(Z) = F$ (`dim1_evenOdd_zero_iff`), $A^-(Z) = Fh$ (`dim1_evenOdd_one_iff`), $A(Z)$ commutative
  (`dim1_comm`), $G(Z) = A(Z)^\times$ (`dim1_cliffordGroup_eq_top`), $G^+(Z) = F^\times$ (`dim1_mem_M0_iff`),
  $G^1(Z) = \{\pm1\}$ (`dim1_mem_spinGroupG1_iff`), $G^-(Z) = F^\times h$ (`dim1_mem_cliffordGroupOdd_iff`);
* §7.2: $z^2 = -\varphi[g]\varphi[h]$ (`z_sq`), $A^+(Z) = K = F + Fz$ (`dim2_evenOdd_zero_iff`), $K$ commutative
  (`dim2_comm_of_even`), (7.1) $G^+(Z) = K^\times$ (`dim2_mem_M0_iff`), $\nu(r + sz) = (r + sz)(r + sz)^* =
  r^2 + s^2\varphi[g]\varphi[h]$, the norm of $K/F$ (`dim2_nu`, with $(r+sz)^* = r - sz$ in `dim2_reverse_K`),
  $G^1(Z) = \{a \in K^\times \mid aa^* = 1\}$ (`dim2_mem_spinGroupG1_iff`, `dim2_mem_spinGroupG1_iff_norm`), and
  "$\tau(a)$ is multiplication by $a^*/a$": $v a = a^* v$ for $a \in K$, $v \in V$ (`dim2_ι_mul_K`), hence
  $\iota(\tau(a)v) = a^{-1}a^*\,\iota(v)$ for $a \in G^+(Z)$ (`dim2_tau`).
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

/-! ### Scalars lie in $G^+$ -/

/-- A unit of $A(Z)$ that is a scalar lies in $G^+(Z)$ (it commutes with $V$). -/
theorem unit_mem_M0_of_scalar (u : Aˣ) (r : F) (hu : (u : A) = algebraMap F A r) : u ∈ M0 Q := by
  refine ⟨hu ▸ algebraMap_mem_evenOdd_zero r, fun x => ⟨x, ?_⟩⟩
  have hc : (u : A) * ι Q x = ι Q x * (u : A) := by rw [hu]; exact Algebra.commutes r _
  rw [hc, mul_assoc, Units.mul_inv, mul_one]

/-! ### §7.1: dimension 1 -/

section Dim1

variable {h : V}

theorem dim1_ι_mul (c d : F) :
    ι Q (c • h) * ι Q (d • h) = algebraMap F A (c * d * Q h) := by
  rw [map_smul, map_smul, smul_mul_smul_comm, ι_sq_scalar, Algebra.smul_def, ← map_mul]

/-- **§7.1, p. 52**: $A^+(Z) = F$ when $\dim Z = 1$. -/
@[kb "shimura2004" "§7.1, p. 52 (dim Z = 1: A⁺(Z) = F)"]
theorem dim1_evenOdd_zero_iff (hspan : ∀ z : V, ∃ c : F, z = c • h) (a : A) :
    a ∈ evenOdd Q 0 ↔ ∃ r : F, a = algebraMap F A r := by
  constructor
  · intro ha
    refine CliffordAlgebra.even_induction (Q := Q) (motive := fun x _ => ∃ r : F, x = algebraMap F A r)
      ?_ ?_ ?_ a ha
    · exact fun r => ⟨r, rfl⟩
    · rintro x y - - ⟨r, rfl⟩ ⟨s, rfl⟩
      exact ⟨r + s, by rw [map_add]⟩
    · rintro m₁ m₂ x - ⟨r, rfl⟩
      obtain ⟨c, rfl⟩ := hspan m₁
      obtain ⟨d, rfl⟩ := hspan m₂
      exact ⟨c * d * Q h * r, by rw [dim1_ι_mul, ← map_mul]⟩
  · rintro ⟨r, rfl⟩
    exact algebraMap_mem_evenOdd_zero r

/-- **§7.1, p. 52**: $A^-(Z) = Fh$ when $\dim Z = 1$. -/
@[kb "shimura2004" "§7.1, p. 52 (dim Z = 1: A⁻(Z) = Fh)"]
theorem dim1_evenOdd_one_iff (hspan : ∀ z : V, ∃ c : F, z = c • h) (a : A) :
    a ∈ evenOdd Q 1 ↔ ∃ c : F, a = c • ι Q h := by
  constructor
  · intro ha
    refine CliffordAlgebra.odd_induction (Q := Q) (P :=fun x _ => ∃ c : F, x = c • ι Q h) ?_ ?_ ?_ a ha
    · intro v
      obtain ⟨c, rfl⟩ := hspan v
      exact ⟨c, by rw [map_smul]⟩
    · rintro x y - - ⟨c, rfl⟩ ⟨d, rfl⟩
      exact ⟨c + d, by rw [add_smul]⟩
    · rintro m₁ m₂ x - ⟨c, rfl⟩
      obtain ⟨a, rfl⟩ := hspan m₁
      obtain ⟨b, rfl⟩ := hspan m₂
      exact ⟨a * b * Q h * c, by rw [dim1_ι_mul, ← Algebra.smul_def, smul_smul]⟩
  · rintro ⟨c, rfl⟩
    exact Submodule.smul_mem _ c (ι_mem_evenOdd_one Q h)

/-- Every element of $A(Z)$ is $r + s h$ when $\dim Z = 1$. -/
theorem dim1_eq (hspan : ∀ z : V, ∃ c : F, z = c • h) (a : A) :
    ∃ r s : F, a = algebraMap F A r + s • ι Q h := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | ι v =>
    obtain ⟨c, rfl⟩ := hspan v
    exact ⟨0, c, by simp [map_smul]⟩
  | mul a b ha hb =>
    obtain ⟨r, s, rfl⟩ := ha
    obtain ⟨r', s', rfl⟩ := hb
    refine ⟨r * r' + s * s' * Q h, r * s' + s * r', ?_⟩
    have hh : ι Q h * ι Q h = (Q h) • (1 : A) := by
      rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one]
    simp only [Algebra.algebraMap_eq_smul_one, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul,
      mul_one, smul_smul, hh]
    module
  | add a b ha hb =>
    obtain ⟨r, s, rfl⟩ := ha
    obtain ⟨r', s', rfl⟩ := hb
    exact ⟨r + r', s + s', by rw [map_add, add_smul]; abel⟩

/-- $A(Z)$ is commutative when $\dim Z = 1$ ($A(Z) = F + Fh$). -/
theorem dim1_comm (hspan : ∀ z : V, ∃ c : F, z = c • h) (a b : A) : a * b = b * a := by
  obtain ⟨r, s, rfl⟩ := dim1_eq hspan a
  obtain ⟨r', s', rfl⟩ := dim1_eq hspan b
  have hh : ι Q h * ι Q h = (Q h) • (1 : A) := by
    rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one]
  simp only [Algebra.algebraMap_eq_smul_one, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one, smul_smul, hh]
  module

/-- **§7.1, p. 52**: $G(Z) = A(Z)^\times$ when $\dim Z = 1$ (every unit conjugates $V$ into itself,
because $A(Z)$ is commutative). -/
@[kb "shimura2004" "§7.1, p. 52 (dim Z = 1: G(Z) = A(Z)^×)"]
theorem dim1_cliffordGroup_eq_top (hspan : ∀ z : V, ∃ c : F, z = c • h) : cliffordGroup Q = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun u x => ⟨x, ?_⟩
  rw [dim1_comm hspan (u : A) (ι Q x), mul_assoc, Units.mul_inv, mul_one]

/-- **§7.1, p. 52**: $G^+(Z) = F^\times$ when $\dim Z = 1$: a unit $u$ of $A(Z)$ lies in $G^+(Z)$ if and only if
it is a nonzero scalar. -/
@[kb "shimura2004" "§7.1, p. 52 (dim Z = 1: G⁺(Z) = F^×)"]
theorem dim1_mem_M0_iff (hspan : ∀ z : V, ∃ c : F, z = c • h) (u : Aˣ) :
    u ∈ M0 Q ↔ ∃ r : F, r ≠ 0 ∧ (u : A) = algebraMap F A r := by
  constructor
  · intro hu
    obtain ⟨r, hr⟩ := (dim1_evenOdd_zero_iff hspan _).1 hu.1
    refine ⟨r, fun h0 => ?_, hr⟩
    rw [h0, map_zero] at hr
    exact u.ne_zero hr
  · rintro ⟨r, -, hr⟩
    exact unit_mem_M0_of_scalar u r hr

/-- **§7.1, p. 52**: $G^1(Z) = \{\pm 1\}$ when $\dim Z = 1$. -/
@[kb "shimura2004" "§7.1, p. 52 (dim Z = 1: G¹(Z) = {±1})"]
theorem dim1_mem_spinGroupG1_iff (hspan : ∀ z : V, ∃ c : F, z = c • h) (u : Aˣ) :
    u ∈ spinGroupG1 Q ↔ (u : A) = 1 ∨ (u : A) = -1 := by
  constructor
  · rintro ⟨hM, hn⟩
    obtain ⟨r, -, hr⟩ := (dim1_mem_M0_iff hspan u).1 hM
    rw [hr, reverse.commutes, ← map_mul, ← map_one (algebraMap F A)] at hn
    have hr1 : r * r = 1 := (algebraMap F A).injective hn
    rcases mul_self_eq_one_iff.1 hr1 with h1 | h1
    · left; rw [hr, h1, map_one]
    · right; rw [hr, h1, map_neg, map_one]
  · intro hu
    have hM : u ∈ M0 Q := by
      rcases hu with hu | hu
      · exact unit_mem_M0_of_scalar u 1 (by rw [hu, map_one])
      · exact unit_mem_M0_of_scalar u (-1) (by rw [hu, map_neg, map_one])
    refine ⟨hM, ?_⟩
    rcases hu with hu | hu <;> rw [hu] <;> simp

/-- **§7.1, p. 52**: $G^-(Z) = F^\times h$ when $\dim Z = 1$: a unit $u$ of $A(Z)$ lies in $G^-(Z)$ if and only
if $u = ch$ with $c \in F^\times$. -/
@[kb "shimura2004" "§7.1, p. 52 (dim Z = 1: G⁻(Z) = F^× h)"]
theorem dim1_mem_cliffordGroupOdd_iff (hspan : ∀ z : V, ∃ c : F, z = c • h) (u : Aˣ) :
    u ∈ cliffordGroupOdd Q ↔ ∃ c : F, c ≠ 0 ∧ (u : A) = c • ι Q h := by
  constructor
  · rintro ⟨-, hu⟩
    obtain ⟨c, hc⟩ := (dim1_evenOdd_one_iff hspan _).1 hu
    refine ⟨c, fun h0 => ?_, hc⟩
    rw [h0, zero_smul] at hc
    exact u.ne_zero hc
  · rintro ⟨c, -, hc⟩
    exact ⟨(dim1_cliffordGroup_eq_top hspan).symm ▸ Subgroup.mem_top u,
      (dim1_evenOdd_one_iff hspan _).2 ⟨c, hc⟩⟩

end Dim1

/-! ### §7.2: dimension 2 -/

section Dim2

variable {g h : V}

theorem ι_h_mul_ι_g (hgh : QuadraticMap.polar Q g h = 0) : ι Q h * ι Q g = -(ι Q g * ι Q h) := by
  have := ι_mul_ι_add_swap (Q := Q) g h
  rw [hgh, map_zero] at this
  exact eq_neg_of_add_eq_zero_right this

theorem ι_g_sq : ι Q g * ι Q g = (Q g) • (1 : A) := by
  rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one]

theorem ι_h_sq : ι Q h * ι Q h = (Q h) • (1 : A) := by
  rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one]

/-- **§7.2, p. 53**: $z = gh$ satisfies $z^2 = -\varphi[g]\varphi[h]$. -/
@[kb "shimura2004" "§7.2, p. 53 (z = gh, z² = −φ[g]φ[h] ∈ F)"]
theorem z_sq (hgh : QuadraticMap.polar Q g h = 0) :
    (ι Q g * ι Q h) * (ι Q g * ι Q h) = (-(Q g * Q h)) • (1 : A) := by
  calc (ι Q g * ι Q h) * (ι Q g * ι Q h) = ι Q g * (ι Q h * ι Q g) * ι Q h := by simp only [mul_assoc]
    _ = ι Q g * (-(ι Q g * ι Q h)) * ι Q h := by rw [ι_h_mul_ι_g hgh]
    _ = -((ι Q g * ι Q g) * (ι Q h * ι Q h)) := by simp only [mul_neg, neg_mul, mul_assoc]
    _ = _ := by
      rw [ι_g_sq, ι_h_sq, smul_mul_assoc, one_mul, smul_smul, neg_smul]

/-- The product in $K = F + Fz$: $(r + sz)(r' + s'z) = (rr' - ss'\varphi[g]\varphi[h]) + (rs' + sr')z$. -/
theorem K_mul (hgh : QuadraticMap.polar Q g h = 0) (r s r' s' : F) :
    (algebraMap F A r + s • (ι Q g * ι Q h)) * (algebraMap F A r' + s' • (ι Q g * ι Q h)) =
      algebraMap F A (r * r' - s * s' * (Q g * Q h)) + (r * s' + s * r') • (ι Q g * ι Q h) := by
  have hz := z_sq hgh
  simp only [Algebra.algebraMap_eq_smul_one, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one, smul_smul, hz]
  module

/-- $\iota(x_1 g + y_1 h)\,\iota(x_2 g + y_2 h) \in K$. -/
theorem ι_mul_ι_K (hgh : QuadraticMap.polar Q g h = 0) (x₁ y₁ x₂ y₂ : F) :
    ι Q (x₁ • g + y₁ • h) * ι Q (x₂ • g + y₂ • h) =
      algebraMap F A (x₁ * x₂ * Q g + y₁ * y₂ * Q h) + (x₁ * y₂ - y₁ * x₂) • (ι Q g * ι Q h) := by
  have hhg := ι_h_mul_ι_g hgh
  simp only [Algebra.algebraMap_eq_smul_one, map_add, map_smul, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, smul_smul, ι_g_sq, hhg, smul_neg]
  module

/-- **§7.2, p. 53**: $A^+(Z) = K = F + Fz$ when $\dim Z = 2$, $\varphi(g, h) = 0$, $z = gh$. -/
@[kb "shimura2004" "§7.2, p. 53 (dim Z = 2: A⁺(Z) = K = F + Fz, z = gh)"]
theorem dim2_evenOdd_zero_iff (hgh : QuadraticMap.polar Q g h = 0)
    (hspan : ∀ z : V, ∃ x y : F, z = x • g + y • h) (a : A) :
    a ∈ evenOdd Q 0 ↔ ∃ r s : F, a = algebraMap F A r + s • (ι Q g * ι Q h) := by
  constructor
  · intro ha
    refine CliffordAlgebra.even_induction (Q := Q)
      (motive := fun x _ => ∃ r s : F, x = algebraMap F A r + s • (ι Q g * ι Q h)) ?_ ?_ ?_ a ha
    · exact fun r => ⟨r, 0, by simp⟩
    · rintro x y - - ⟨r, s, rfl⟩ ⟨r', s', rfl⟩
      exact ⟨r + r', s + s', by rw [map_add, add_smul]; abel⟩
    · rintro m₁ m₂ x - ⟨r, s, rfl⟩
      obtain ⟨x₁, y₁, rfl⟩ := hspan m₁
      obtain ⟨x₂, y₂, rfl⟩ := hspan m₂
      exact ⟨_, _, by rw [ι_mul_ι_K hgh, K_mul hgh]⟩
  · rintro ⟨r, s, rfl⟩
    exact add_mem (algebraMap_mem_evenOdd_zero r)
      (Submodule.smul_mem _ s (ι_mul_ι_mem_evenOdd_zero Q g h))

/-- **§7.2, p. 53**: $K = A^+(Z)$ is commutative. -/
@[kb "shimura2004" "§7.2, p. 53 (dim Z = 2: K = A⁺(Z) is a commutative field/algebra F + Fz)"]
theorem dim2_comm_of_even (hgh : QuadraticMap.polar Q g h = 0)
    (hspan : ∀ z : V, ∃ x y : F, z = x • g + y • h) {a b : A} (ha : a ∈ evenOdd Q 0) (hb : b ∈ evenOdd Q 0) :
    a * b = b * a := by
  obtain ⟨r, s, rfl⟩ := (dim2_evenOdd_zero_iff hgh hspan a).1 ha
  obtain ⟨r', s', rfl⟩ := (dim2_evenOdd_zero_iff hgh hspan b).1 hb
  rw [K_mul hgh, K_mul hgh, show r' * r - s' * s * (Q g * Q h) = r * r' - s * s' * (Q g * Q h) by ring,
    show r' * s + s' * r = r * s' + s * r' by ring]

/-- The canonical involution on $K$: $(r + sz)^* = r - sz$ (as $z^* = hg = -z$). -/
theorem dim2_reverse_K (hgh : QuadraticMap.polar Q g h = 0) (r s : F) :
    reverse (algebraMap F A r + s • (ι Q g * ι Q h)) = algebraMap F A r + (-s) • (ι Q g * ι Q h) := by
  rw [map_add, map_smul, reverse.commutes, reverse.map_mul, reverse_ι, reverse_ι, ι_h_mul_ι_g hgh,
    smul_neg, neg_smul]

/-- **§7.2, p. 53**: $\nu(r + sz) = (r + sz)(r + sz)^* = r^2 + s^2\varphi[g]\varphi[h]$, which is the norm
$N_{K/F}(r + sz)$ of the quadratic algebra $K = F[z]$, $z^2 = -\varphi[g]\varphi[h]$. -/
@[kb "shimura2004" "§7.2, p. 53 (dim Z = 2: ν(r + sz) = r² + s²φ[g]φ[h] = N_{K/F}(r + sz))"]
theorem dim2_nu (hgh : QuadraticMap.polar Q g h = 0) (r s : F) :
    (algebraMap F A r + s • (ι Q g * ι Q h)) * reverse (algebraMap F A r + s • (ι Q g * ι Q h)) =
      algebraMap F A (r ^ 2 + s ^ 2 * Q g * Q h) := by
  rw [dim2_reverse_K hgh, K_mul hgh, show r * (-s) + s * r = 0 by ring, zero_smul, add_zero]
  congr 1
  ring

/-- **(7.1)**, p. 53: $G^+(Z) = K^\times$ when $\dim Z = 2$: a unit $u$ of $A(Z)$ lies in $G^+(Z)$ if and only if
it lies in $A^+(Z) = K$. (The inclusion $K^\times \subseteq G^+(Z)$ uses Lemma 3.11 with $x = sg$, $y = h$.) -/
@[kb "shimura2004" "(7.1), p. 53 (dim Z = 2: G⁺(Z) = K^×)"]
theorem dim2_mem_M0_iff (hgh : QuadraticMap.polar Q g h = 0)
    (hspan : ∀ z : V, ∃ x y : F, z = x • g + y • h) (u : Aˣ) :
    u ∈ M0 Q ↔ (u : A) ∈ evenOdd Q 0 := by
  refine ⟨fun hu => hu.1, fun hu => ?_⟩
  obtain ⟨r, s, hrs⟩ := (dim2_evenOdd_zero_iff hgh hspan _).1 hu
  have hr : (u : A) = rxy Q r (s • g) h := by
    rw [hrs, rxy, map_smul, smul_mul_assoc]
  have hmul := mul_reverse_rxy (Q := Q) r (s • g) h
  rw [← hr] at hmul
  have hunit : IsUnit ((u : A) * reverse (u : A)) := by
    refine IsUnit.mul u.isUnit ⟨⟨reverse (u : A), reverse ((u⁻¹ : Aˣ) : A), ?_, ?_⟩, rfl⟩
    · rw [← reverse.map_mul]; simp
    · rw [← reverse.map_mul]; simp
  have hne : r ^ 2 + r * QuadraticMap.polar Q (s • g) h + Q (s • g) * Q h ≠ 0 := by
    intro h0
    rw [hmul, h0, map_zero] at hunit
    exact not_isUnit_zero hunit
  obtain ⟨u', hu', hM⟩ := rxy_mem_M0 r (s • g) h hne
  have : u = u' := Units.ext (hr.trans hu'.symm)
  rwa [this]

/-- **§7.2, p. 53**: $G^1(Z) = \{a \in K^\times \mid aa^* = 1\}$ when $\dim Z = 2$. -/
@[kb "shimura2004" "§7.2, p. 53 (dim Z = 2: G¹(Z) = {a ∈ K^× | aa* = 1})"]
theorem dim2_mem_spinGroupG1_iff (hgh : QuadraticMap.polar Q g h = 0)
    (hspan : ∀ z : V, ∃ x y : F, z = x • g + y • h) (u : Aˣ) :
    u ∈ spinGroupG1 Q ↔ (u : A) ∈ evenOdd Q 0 ∧ (u : A) * reverse (u : A) = 1 :=
  ⟨fun hu => ⟨hu.1.1, hu.2⟩, fun hu => ⟨(dim2_mem_M0_iff hgh hspan u).2 hu.1, hu.2⟩⟩

/-- **§7.2, p. 53**: $G^1(Z) = \{r + sz \mid r, s \in F,\ r^2 + s^2\varphi[g]\varphi[h] = 1\}$ (the norm-one
elements of $K^\times$). -/
@[kb "shimura2004" "§7.2, p. 53 (dim Z = 2: G¹(Z) = norm-one elements r + sz with r² + s²φ[g]φ[h] = 1)"]
theorem dim2_mem_spinGroupG1_iff_norm (hgh : QuadraticMap.polar Q g h = 0)
    (hspan : ∀ z : V, ∃ x y : F, z = x • g + y • h) (u : Aˣ) :
    u ∈ spinGroupG1 Q ↔ ∃ r s : F, (u : A) = algebraMap F A r + s • (ι Q g * ι Q h) ∧
      r ^ 2 + s ^ 2 * Q g * Q h = 1 := by
  rw [dim2_mem_spinGroupG1_iff hgh hspan]
  constructor
  · rintro ⟨hu, hn⟩
    obtain ⟨r, s, hrs⟩ := (dim2_evenOdd_zero_iff hgh hspan _).1 hu
    refine ⟨r, s, hrs, ?_⟩
    rw [hrs, dim2_nu hgh, ← map_one (algebraMap F A)] at hn
    exact (algebraMap F A).injective hn
  · rintro ⟨r, s, hrs, hn⟩
    refine ⟨(dim2_evenOdd_zero_iff hgh hspan _).2 ⟨r, s, hrs⟩, ?_⟩
    rw [hrs, dim2_nu hgh, hn, map_one]

/-- $v z = -z v$ for $v \in V$, $z = gh$ (when $\varphi(g, h) = 0$ and $V = Fg + Fh$). -/
theorem ι_mul_z (hgh : QuadraticMap.polar Q g h = 0) (hspan : ∀ z : V, ∃ x y : F, z = x • g + y • h) (v : V) :
    ι Q v * (ι Q g * ι Q h) = -((ι Q g * ι Q h) * ι Q v) := by
  have a1 : ι Q g * (ι Q g * ι Q h) = (Q g) • ι Q h := by
    rw [← mul_assoc, ι_g_sq, smul_mul_assoc, one_mul]
  have a4 : (ι Q g * ι Q h) * ι Q h = (Q h) • ι Q g := by
    rw [mul_assoc, ι_h_sq, mul_smul_comm, mul_one]
  have a3 : (ι Q g * ι Q h) * ι Q g = -((Q g) • ι Q h) := by
    rw [mul_assoc, ι_h_mul_ι_g hgh, mul_neg, a1]
  have a2 : ι Q h * (ι Q g * ι Q h) = -((Q h) • ι Q g) := by
    rw [← mul_assoc, ι_h_mul_ι_g hgh, neg_mul, a4]
  obtain ⟨x, y, rfl⟩ := hspan v
  simp only [map_add, map_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, a1, a2, a3, a4, smul_neg]
  module

/-- **§7.2, p. 53**: $va = a^*v$ for every $a \in K = F + Fz$ and $v \in V$. This is the content of "$\tau(a)$ is
multiplication by $a^*/a$". -/
@[kb "shimura2004" "§7.2, p. 53 (dim Z = 2: va = a*v for a ∈ K, v ∈ V)"]
theorem dim2_ι_mul_K (hgh : QuadraticMap.polar Q g h = 0) (hspan : ∀ z : V, ∃ x y : F, z = x • g + y • h)
    (v : V) (r s : F) :
    ι Q v * (algebraMap F A r + s • (ι Q g * ι Q h)) =
      reverse (algebraMap F A r + s • (ι Q g * ι Q h)) * ι Q v := by
  rw [dim2_reverse_K hgh, mul_add, mul_smul_comm, ι_mul_z hgh hspan, add_mul, smul_mul_assoc,
    ← Algebra.commutes, neg_smul, smul_neg]

/-- **§7.2, p. 53**: for $a \in G^+(Z)$ (an element of $G(Z)$ lying in $A^+(Z) = K$), $\tau(a)$ is
multiplication by $a^*/a$: $\iota(\tau(a)v) = a^{-1}a^*\,\iota(v)$ (here $x\tau(a) = a^{-1}xa$, `tau`). -/
@[kb "shimura2004" "§7.2, p. 53 (dim Z = 2: τ(a) is multiplication by a*/a for a ∈ G⁺(Z))"]
theorem dim2_tau (hgh : QuadraticMap.polar Q g h = 0) (hspan : ∀ z : V, ∃ x y : F, z = x • g + y • h)
    (a : cliffordGroup Q) (ha : ((a : Aˣ) : A) ∈ evenOdd Q 0) (v : V) :
    ι Q (tau a v) = (((a : Aˣ)⁻¹ : Aˣ) : A) * reverse ((a : Aˣ) : A) * ι Q v := by
  obtain ⟨r, s, hrs⟩ := (dim2_evenOdd_zero_iff hgh hspan _).1 ha
  have key := dim2_ι_mul_K hgh hspan v r s
  rw [← hrs] at key
  rw [tau_spec, mul_assoc, key, ← mul_assoc]

/-- **§7.2, p. 53**: $G^-(Z) = K^\times h$ when $\dim Z = 2$: a unit $u$ of $A(Z)$ lies in $G^-(Z)$ if and only if
$u = kh$ for a unit $k$ of $A(Z)$ lying in $A^+(Z) = K$. -/
@[kb "shimura2004" "§7.2, p. 53 (dim Z = 2: G⁻(Z) = K^× h)"]
theorem dim2_mem_cliffordGroupOdd_iff (hh : Q h ≠ 0) (hgh : QuadraticMap.polar Q g h = 0)
    (hspan : ∀ z : V, ∃ x y : F, z = x • g + y • h) (u : Aˣ) :
    u ∈ cliffordGroupOdd Q ↔ ∃ k : Aˣ, (k : A) ∈ evenOdd Q 0 ∧ (u : A) = k * ι Q h := by
  have hv : ((vecUnit h hh : Aˣ) : A) = ι Q h := rfl
  constructor
  · rintro ⟨-, hu⟩
    refine ⟨u * (vecUnit h hh)⁻¹, ?_, ?_⟩
    · have hxi : (((vecUnit h hh)⁻¹ : Aˣ) : A) ∈ evenOdd Q 1 :=
        mem_evenOdd_of_mul_eq_one Q (ι_mem_evenOdd_one Q h) (vecUnit h hh).mul_inv
      simpa [show (1 : ZMod 2) + 1 = 0 from rfl] using mul_mem_evenOdd hu hxi
    · rw [← hv, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  · rintro ⟨k, hk, hu⟩
    have hkM := (dim2_mem_M0_iff hgh hspan k).2 hk
    have hku : u = k * vecUnit h hh := Units.ext (by rw [hu, Units.val_mul, hv])
    refine ⟨hku ▸ (cliffordGroup Q).mul_mem hkM.2 (vecUnit_mem h hh), ?_⟩
    rw [hu]
    simpa [show (0 : ZMod 2) + 1 = 1 from rfl] using mul_mem_evenOdd hk (ι_mem_evenOdd_one Q h)

omit [FiniteDimensional F V] in
theorem polar_comb_g (hgh : QuadraticMap.polar Q g h = 0) (x y : F) :
    QuadraticMap.polar Q (x • g + y • h) g = x * (2 * Q g) := by
  rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_self, QuadraticMap.polar_comm Q h g, hgh, nsmul_eq_mul]
  push_cast
  ring

omit [FiniteDimensional F V] in
theorem polar_comb_h (hgh : QuadraticMap.polar Q g h = 0) (x y : F) :
    QuadraticMap.polar Q (x • g + y • h) h = y * (2 * Q h) := by
  rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_self, hgh, nsmul_eq_mul]
  push_cast
  ring

omit [FiniteDimensional F V] in
theorem two_mul_ne_zero' {c : F} (hc : c ≠ 0) : 2 * c ≠ 0 :=
  mul_ne_zero (isUnit_of_invertible (2 : F)).ne_zero hc

omit [FiniteDimensional F V] in
/-- In the setting of §7.2, $g$ and $h$ are linearly independent. -/
theorem dim2_linearIndependent (hg : Q g ≠ 0) (hh : Q h ≠ 0) (hgh : QuadraticMap.polar Q g h = 0) :
    LinearIndependent F ![g, h] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := polar_comb_g hgh s t
  have h2 := polar_comb_h hgh s t
  rw [hst, QuadraticMap.polar_zero_left] at h1 h2
  exact ⟨(mul_eq_zero.1 h1.symm).resolve_right (two_mul_ne_zero' hg),
    (mul_eq_zero.1 h2.symm).resolve_right (two_mul_ne_zero' hh)⟩

omit [FiniteDimensional F V] in
/-- In the setting of §7.2, $\dim Z = 2$. -/
theorem dim2_finrank (hg : Q g ≠ 0) (hh : Q h ≠ 0) (hgh : QuadraticMap.polar Q g h = 0)
    (hspan : ∀ z : V, ∃ x y : F, z = x • g + y • h) : finrank F V = 2 := by
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![g, h]) := by
    rintro v -
    obtain ⟨x, y, rfl⟩ := hspan v
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  rw [Module.finrank_eq_card_basis (Basis.mk (dim2_linearIndependent hg hh hgh) hsp), Fintype.card_fin]

omit [FiniteDimensional F V] in
/-- In the setting of §7.2, $\varphi$ is nondegenerate. -/
theorem dim2_nondegenerate (hg : Q g ≠ 0) (hh : Q h ≠ 0) (hgh : QuadraticMap.polar Q g h = 0)
    (hspan : ∀ z : V, ∃ x y : F, z = x • g + y • h) : (QuadraticMap.associated Q).Nondegenerate := by
  have hpol : ∀ u v, QuadraticMap.associated Q u v = 0 → QuadraticMap.polar Q u v = 0 := by
    intro u v huv
    have e := LinearMap.congr_fun₂ (QuadraticMap.two_nsmul_associated F Q) u v
    rw [LinearMap.smul_apply, LinearMap.smul_apply] at e
    change 2 • QuadraticMap.associated Q u v = QuadraticMap.polar Q u v at e
    rw [huv, smul_zero] at e
    exact e.symm
  have key : ∀ m, (∀ v, QuadraticMap.polar Q m v = 0) → m = 0 := by
    intro m hp
    obtain ⟨x, y, rfl⟩ := hspan m
    have h1 := hp g
    have h2 := hp h
    rw [polar_comb_g hgh] at h1
    rw [polar_comb_h hgh] at h2
    rw [(mul_eq_zero.1 h1).resolve_right (two_mul_ne_zero' hg),
      (mul_eq_zero.1 h2).resolve_right (two_mul_ne_zero' hh), zero_smul, zero_smul, add_zero]
  refine ⟨fun m hm => key m fun v => hpol m v (hm v), fun m hm => key m fun v => ?_⟩
  rw [QuadraticMap.polar_comm]
  exact hpol v m (hm v)

/-- **§7.2, p. 53**: $G(Z) = K^\times \cup K^\times h$ when $\dim Z = 2$: a unit $u$ of $A(Z)$ lies in $G(Z)$ if and
only if $u \in K = A^+(Z)$, or $u = kh$ for a unit $k$ of $A(Z)$ lying in $K$. (Via Theorem 3.6 (ii),
$G(Z) = G^+(Z) \cup G^-(Z)$ for $\dim Z$ even.) -/
@[kb "shimura2004" "§7.2, p. 53 (dim Z = 2: G(Z) = K^× ∪ K^× h)"]
theorem dim2_mem_cliffordGroup_iff (hg : Q g ≠ 0) (hh : Q h ≠ 0) (hgh : QuadraticMap.polar Q g h = 0)
    (hspan : ∀ z : V, ∃ x y : F, z = x • g + y • h) (u : Aˣ) :
    u ∈ cliffordGroup Q ↔
      (u : A) ∈ evenOdd Q 0 ∨ ∃ k : Aˣ, (k : A) ∈ evenOdd Q 0 ∧ (u : A) = k * ι Q h := by
  have : Nontrivial V :=⟨⟨g, 0, fun h0 => hg (by rw [h0, map_zero])⟩⟩
  constructor
  · intro hu
    have hhom := cliffordGroup_le_homogeneous_of_even (dim2_nondegenerate hg hh hgh hspan)
      (by rw [dim2_finrank hg hh hgh hspan]; exact even_two) hu
    rcases (mem_homogeneous_iff u).1 hhom with h0 | h1
    · exact Or.inl h0.1
    · exact Or.inr ((dim2_mem_cliffordGroupOdd_iff hh hgh hspan u).1 h1)
  · rintro (h0 | h1)
    · exact ((dim2_mem_M0_iff hgh hspan u).2 h0).2
    · exact ((dim2_mem_cliffordGroupOdd_iff hh hgh hspan u).2 h1).1

end Dim2

end LowDim

end QuadFormsKB.Shimura2004
