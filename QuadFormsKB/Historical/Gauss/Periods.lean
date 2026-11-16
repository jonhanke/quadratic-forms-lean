import QuadFormsKB.Citation
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.GroupTheory.Coset.Card

/-!
# Gaussian periods (Disquisitiones Arithmeticae, Section VII, Art. 342-351)

Let $p$ be an odd prime, $\zeta$ a $p$-th root of unity in a commutative ring $R$, and $H$ a subgroup of
$(\mathbb{Z}/p)^\times$. The **period** of $H$ at $x \in \mathbb{Z}/p$ is `periodSum ζ H x` $= \sum_{h \in H}
\zeta^{x h}$. Gauss's period $(f, \lambda)$ with $p - 1 = e f$, $h = g^e$ is `gaussPeriod ζ f h lam`.

The following lists the relevant results of the historical sources and what is proved (everything is unconditional; $\zeta^p = 1$ is the only assumption unless
stated):

* (Art. 343-344): `gaussPeriod_eq_periodSum` (it is the period of $\langle h \rangle$),
  `gaussPeriod_mul_pow` (depends only on the coset of $\lambda$), `zpowers_pow_eq`,
  `gaussPeriod_eq_of_primitiveRoots`, `eq_zpowers_of_card_eq` (independence of $g$; uniqueness of the subgroup of
  order $f$), `periodExponents_eq_or_disjoint`, `periodRoots_eq_or_disjoint` (equal or no common root of unity;
  $\zeta$ primitive), `sum_cosetPeriod`, `sum_cosetPeriod_eq_neg_one` (partition; sum $= -1$ in a domain),
  `periodSum_eq_sum_quotPeriod` (the period of $\beta\gamma$ terms is the sum of the $\beta$ periods of $\gamma$
  terms it contains).
* (Art. 345): `periodSum_mul_periodSum`, `gaussPeriod_mul_gaussPeriod` (product formula, with
  $(f, 0) = f$), `periodSum_mul_periodSum_nonneg` (nonnegative integer coefficients), `mul_mem_periodSpan`,
  `periodSubring` (the span of $1$ and the periods is a subring).
* (Art. 342, 350-351): `towerPoly` (monic of degree $\beta$, `towerPoly_monic`,
  `towerPoly_natDegree`), `towerPoly_coeff_mem_periodSpan` (coefficients lie in the integer span of $1$ and the
  periods of $H'$; no primitivity needed, and no hypothesis $H \le H'$), `towerPoly_coeff_int` (integers when
  $H' = (\mathbb{Z}/p)^\times$, $\zeta$ primitive in a domain).

Gauss's $\alpha, \beta, \gamma$ with $p - 1 = \alpha\beta\gamma$ correspond to the index of $H'$, the index of $H$
in $H'$, and $|H|$. All indices are 0-based (`range f` is $j = 0, \dots, f - 1$).
-/

namespace QuadFormsKB.Historical.Gauss

open scoped Classical

section Basics

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime]

/-- The power $\zeta^{x}$ of a root of unity $\zeta$ ($\zeta^p = 1$) with exponent a residue class $x$ modulo $p$,
computed from the representative $0 \le x.\mathrm{val} < p$. -/
def rootPow (ζ : R) (x : ZMod p) : R := ζ ^ x.val

theorem pow_mod_eq {ζ : R} (hζ : ζ ^ p = 1) (n : ℕ) : ζ ^ (n % p) = ζ ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n p, pow_add, pow_mul, hζ, one_pow, one_mul]

theorem rootPow_add {ζ : R} (hζ : ζ ^ p = 1) (x y : ZMod p) :
    rootPow ζ (x + y) = rootPow ζ x * rootPow ζ y := by
  unfold rootPow
  rw [ZMod.val_add, pow_mod_eq hζ, pow_add]

@[simp] theorem rootPow_zero (ζ : R) : rootPow ζ (0 : ZMod p) = 1 := by
  simp [rootPow]

/-- Sum over a finite group split along the cosets of a subgroup: representatives `c.out`. -/
theorem sum_eq_sum_coset {G : Type*} [Group G] [Fintype G] (K : Subgroup G) {M : Type*}
    [AddCommMonoid M] (F : G → M) :
    ∑ g, F g = ∑ c : G ⧸ K, ∑ k : K, F (c.out * (k : G)) := by
  have key : ∀ (c : G ⧸ K) (k : K), (QuotientGroup.mk (c.out * (k : G)) : G ⧸ K) = c := by
    intro c k
    have h1 : (QuotientGroup.mk (c.out * (k : G)) : G ⧸ K) = QuotientGroup.mk c.out :=
      QuotientGroup.eq.mpr (by simpa using K.inv_mem k.2)
    rw [h1, QuotientGroup.out_eq']
  have hbij : Function.Bijective (fun x : (G ⧸ K) × K => x.1.out * (x.2 : G)) := by
    constructor
    · rintro ⟨c, k⟩ ⟨c', k'⟩ h
      have hc : c = c' := by
        have := congrArg (fun g : G => (QuotientGroup.mk g : G ⧸ K)) h
        simpa [key] using this
      subst hc
      have : (k : G) = k' := mul_left_cancel h
      exact Prod.ext rfl (Subtype.ext this)
    · intro g
      refine ⟨⟨QuotientGroup.mk g, ⟨(QuotientGroup.mk g : G ⧸ K).out⁻¹ * g, ?_⟩⟩, ?_⟩
      · have h2 : (QuotientGroup.mk (QuotientGroup.mk g : G ⧸ K).out : G ⧸ K) = QuotientGroup.mk g :=
          QuotientGroup.out_eq' _
        exact QuotientGroup.eq.mp h2
      · simp
  have h2 : ∑ c : G ⧸ K, ∑ k : K, F (c.out * (k : G))
      = ∑ x : (G ⧸ K) × K, F (x.1.out * (x.2 : G)) :=
    (Fintype.sum_prod_type' (f := fun (c : G ⧸ K) (k : K) => F (c.out * (k : G)))).symm
  rw [h2]
  exact (Fintype.sum_bijective (fun x : (G ⧸ K) × K => x.1.out * (x.2 : G)) hbij _ _
    fun _ => rfl).symm

/-- A sum over residues modulo $p$ is the term at $0$ plus the sum over the units. -/
theorem sum_zmod_eq {M : Type*} [AddCommMonoid M] (F : ZMod p → M) :
    ∑ x, F x = F 0 + ∑ u : (ZMod p)ˣ, F u := by
  rw [← Finset.add_sum_erase (Finset.univ : Finset (ZMod p)) F (Finset.mem_univ 0)]
  congr 1
  symm
  refine Finset.sum_bij (fun u _ => (u : ZMod p)) ?_ ?_ ?_ ?_
  · intro u _; simp
  · intro a _ b _ h; exact Units.ext h
  · intro x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact ⟨Units.mk0 x hx0, Finset.mem_univ _, rfl⟩
  · intro _ _; rfl

/-! ### Periods of a subgroup -/

/-- **Period of a subgroup** $H \le (\mathbb{Z}/p)^\times$ at the exponent $x \in \mathbb{Z}/p$ (the historical sources
; Gauss's period $(f, \lambda)$ when $H$ has $f$ elements and $x = \lambda$;
*Disq. Arith.* Art. 343): $\sum_{h \in H} \zeta^{x h}$. For $x = 0$ every term is $1$, so the value is
$|H| = f$, which is Gauss's convention $(f, 0) := f$ of Art. 345. -/
@[kb "gauss1801" "Art. 343"]
noncomputable def periodSum (ζ : R) (H : Subgroup (ZMod p)ˣ) (x : ZMod p) : R :=
  ∑ h : H, rootPow ζ (x * ((h : (ZMod p)ˣ) : ZMod p))

theorem periodSum_zero (ζ : R) (H : Subgroup (ZMod p)ˣ) :
    periodSum ζ H 0 = (Nat.card H : R) := by
  simp [periodSum, Nat.card_eq_fintype_card]

/-- The period depends only on the coset of the exponent modulo $H$. -/
theorem periodSum_mul_of_mem (ζ : R) (H : Subgroup (ZMod p)ˣ) (x : ZMod p) {u : (ZMod p)ˣ}
    (hu : u ∈ H) : periodSum ζ H (x * u) = periodSum ζ H x := by
  unfold periodSum
  refine Fintype.sum_equiv (Equiv.mulRight (⟨u, hu⟩ : H)) _ _ fun h => ?_
  simp only [Equiv.coe_mulRight]
  congr 1
  push_cast
  ring

/-- **Product of two periods of a subgroup** (*Disq. Arith.* Art. 345):
$\eta_H(x)\,\eta_H(y) = \sum_{h \in H} \eta_H(x h + y)$ with $\eta_H(0) = |H|$ (Gauss's
$(f, \lambda)(f, \mu) = \sum_j (f, \lambda h^{j} + \mu)$). Needs only $\zeta^p = 1$. -/
@[kb "gauss1801" "Art. 345"]
theorem periodSum_mul_periodSum {ζ : R} (hζ : ζ ^ p = 1) (H : Subgroup (ZMod p)ˣ) (x y : ZMod p) :
    periodSum ζ H x * periodSum ζ H y
      = ∑ h : H, periodSum ζ H (x * ((h : (ZMod p)ˣ) : ZMod p) + y) := by
  unfold periodSum
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  symm
  refine Fintype.sum_equiv (Equiv.mulRight b) _ _ fun h => ?_
  simp only [Equiv.coe_mulRight]
  rw [← rootPow_add hζ]
  congr 1
  push_cast
  ring

/-! ### The ring spanned by the periods -/

/-- Generators of the integer span of $1$ and the periods of $H$. -/
noncomputable def periodGens (ζ : R) (H : Subgroup (ZMod p)ˣ) : Set R :=
  insert 1 (Set.range fun u : (ZMod p)ˣ => periodSum ζ H (u : ZMod p))

/-- The $\mathbb{Z}$-span of $1$ and the periods $(f, \lambda)$, $\lambda$ prime to $p$, of the subgroup $H$. -/
noncomputable def periodSpan (ζ : R) (H : Subgroup (ZMod p)ˣ) : Submodule ℤ R :=
  Submodule.span ℤ (periodGens ζ H)

theorem one_mem_periodSpan (ζ : R) (H : Subgroup (ZMod p)ˣ) : (1 : R) ∈ periodSpan ζ H :=
  Submodule.subset_span (Set.mem_insert _ _)

theorem natCast_mem_periodSpan (ζ : R) (H : Subgroup (ZMod p)ˣ) (n : ℕ) :
    (n : R) ∈ periodSpan ζ H := by
  have : (n : R) = (n : ℤ) • (1 : R) := by simp
  rw [this]
  exact Submodule.smul_mem _ _ (one_mem_periodSpan ζ H)

theorem periodSum_mem_periodSpan (ζ : R) (H : Subgroup (ZMod p)ˣ) (x : ZMod p) :
    periodSum ζ H x ∈ periodSpan ζ H := by
  by_cases hx : x = 0
  · subst hx
    rw [periodSum_zero]
    exact natCast_mem_periodSpan ζ H _
  · exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨Units.mk0 x hx, rfl⟩)

/-- **The span of $1$ and the periods is closed under multiplication** (the historical sources,
*Disq. Arith.* Art. 345). -/
@[kb "gauss1801" "Art. 345"]
theorem mul_mem_periodSpan {ζ : R} (hζ : ζ ^ p = 1) (H : Subgroup (ZMod p)ˣ) {a b : R}
    (ha : a ∈ periodSpan ζ H) (hb : b ∈ periodSpan ζ H) : a * b ∈ periodSpan ζ H := by
  have h : periodSpan ζ H * periodSpan ζ H ≤ periodSpan ζ H := by
    unfold periodSpan
    rw [Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rw [Set.mul_subset_iff]
    intro x hx y hy
    rw [SetLike.mem_coe]
    rcases hx with rfl | ⟨u, rfl⟩
    · rw [one_mul]; exact Submodule.subset_span hy
    · rcases hy with rfl | ⟨v, rfl⟩
      · rw [mul_one]; exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨u, rfl⟩)
      · rw [periodSum_mul_periodSum hζ]
        exact Submodule.sum_mem _ fun h _ => periodSum_mem_periodSpan ζ H _
  exact h (Submodule.mul_mem_mul ha hb)

/-- **The subring generated by the periods** (*Disq. Arith.* Art. 345): the integer
span of $1$ and the periods of $H$ is a subring of $R$ (from $\zeta^p = 1$ alone). -/
@[kb "gauss1801" "Art. 345"]
noncomputable def periodSubring {ζ : R} (hζ : ζ ^ p = 1) (H : Subgroup (ZMod p)ˣ) : Subring R where
  carrier := periodSpan ζ H
  mul_mem' := mul_mem_periodSpan hζ H
  one_mem' := one_mem_periodSpan ζ H
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  neg_mem' := fun ha => Submodule.neg_mem _ ha

/-! ### Periods indexed by cosets -/

/-- The period attached to a coset $\lambda H$ of $H$ in $(\mathbb{Z}/p)^\times$ (well defined by
`periodSum_mul_of_mem`). -/
noncomputable def cosetPeriod (ζ : R) (H : Subgroup (ZMod p)ˣ) : (ZMod p)ˣ ⧸ H → R :=
  Quotient.lift (fun u : (ZMod p)ˣ => periodSum ζ H (u : ZMod p)) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have := periodSum_mul_of_mem ζ H (a : ZMod p) hab'
    rw [← this]
    congr 1
    rw [← Units.val_mul, mul_inv_cancel_left])

theorem cosetPeriod_mk (ζ : R) (H : Subgroup (ZMod p)ˣ) (u : (ZMod p)ˣ) :
    cosetPeriod ζ H (QuotientGroup.mk u) = periodSum ζ H (u : ZMod p) := rfl

theorem cosetPeriod_eq_out (ζ : R) (H : Subgroup (ZMod p)ˣ) (c : (ZMod p)ˣ ⧸ H) :
    cosetPeriod ζ H c = periodSum ζ H (c.out : ZMod p) := by
  conv_lhs => rw [← QuotientGroup.out_eq' c]
  rfl

/-- **The product of two periods has nonnegative integer coefficients** (the historical sources,
*Disq. Arith.* Art. 345): $\eta(u)\,\eta(v) = a f + \sum_c b_c \eta_c$ with $a, b_c \in \mathbb{N}$, $f = |H|$,
and $c$ running over the cosets of $H$ in $(\mathbb{Z}/p)^\times$ (the $e$ periods). -/
@[kb "gauss1801" "Art. 345"]
theorem periodSum_mul_periodSum_nonneg {ζ : R} (hζ : ζ ^ p = 1) (H : Subgroup (ZMod p)ˣ)
    (u v : (ZMod p)ˣ) :
    ∃ (a : ℕ) (b : (ZMod p)ˣ ⧸ H → ℕ),
      periodSum ζ H (u : ZMod p) * periodSum ζ H (v : ZMod p)
        = (a : R) * (Nat.card H : R) + ∑ c, (b c : R) * cosetPeriod ζ H c := by
  rw [periodSum_mul_periodSum hζ]
  let φ : H → Option ((ZMod p)ˣ ⧸ H) := fun h =>
    if hx : (u : ZMod p) * ((h : (ZMod p)ˣ) : ZMod p) + v = 0 then none
    else some (QuotientGroup.mk (Units.mk0 _ hx))
  let T : Option ((ZMod p)ˣ ⧸ H) → R := fun o => o.elim (Nat.card H : R) (cosetPeriod ζ H)
  have hT : ∀ h : H, periodSum ζ H ((u : ZMod p) * ((h : (ZMod p)ˣ) : ZMod p) + v) = T (φ h) := by
    intro h
    by_cases hx : (u : ZMod p) * ((h : (ZMod p)ˣ) : ZMod p) + v = 0
    · simp [φ, T, hx, periodSum_zero]
    · simp only [φ, T, hx, dif_neg, not_false_eq_true, Option.elim_some]
      rfl
  rw [Finset.sum_congr rfl fun h _ => hT h]
  rw [← Finset.sum_fiberwise Finset.univ φ (fun h => T (φ h))]
  have hfib : ∀ j : Option ((ZMod p)ˣ ⧸ H),
      ∑ i ∈ Finset.univ.filter (fun i => φ i = j), T (φ i)
        = (Finset.univ.filter (fun i => φ i = j)).card • T j := by
    intro j
    rw [Finset.sum_congr rfl (g := fun _ => T j) fun i hi => congrArg T (Finset.mem_filter.mp hi).2]
    simp
  rw [Finset.sum_congr rfl fun j _ => hfib j, Fintype.sum_option]
  refine ⟨(Finset.univ.filter (fun i => φ i = none)).card,
    fun c => (Finset.univ.filter (fun i => φ i = some c)).card, ?_⟩
  simp [T, nsmul_eq_mul]

/-! ### Disjointness of the periods -/

/-- The set of exponents $\{x h : h \in H\}$ occurring in the period of $H$ at $x$: the coset $x H$. -/
noncomputable def periodExponents (H : Subgroup (ZMod p)ˣ) (x : ZMod p) : Finset (ZMod p) :=
  Finset.univ.image fun h : H => x * ((h : (ZMod p)ˣ) : ZMod p)

theorem val_mul_val_inv (H : Subgroup (ZMod p)ˣ) (h : H) :
    ((h : (ZMod p)ˣ) : ZMod p) * (((h⁻¹ : H) : (ZMod p)ˣ) : ZMod p) = 1 := by
  rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
  rfl

/-- **Two periods share no exponents, or are the same coset** (*Disq. Arith.*
Art. 344): the cosets $u H$ and $v H$ of $H$ in $(\mathbb{Z}/p)^\times$ are equal or disjoint. -/
@[kb "gauss1801" "Art. 344"]
theorem periodExponents_eq_or_disjoint (H : Subgroup (ZMod p)ˣ) (u v : (ZMod p)ˣ) :
    periodExponents H (u : ZMod p) = periodExponents H (v : ZMod p) ∨
      Disjoint (periodExponents H (u : ZMod p)) (periodExponents H (v : ZMod p)) := by
  by_cases hc : ∃ h : H, v = u * (h : (ZMod p)ˣ)
  · left
    obtain ⟨h, hv⟩ := hc
    have hv' : (v : ZMod p) = u * ((h : (ZMod p)ˣ) : ZMod p) := by rw [hv]; simp
    have hh := val_mul_val_inv H h
    ext z
    simp only [periodExponents, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨h⁻¹ * a, ?_⟩
      simp only [Subgroup.coe_mul, Units.val_mul]
      rw [hv']
      linear_combination ((u : ZMod p) * ((a : (ZMod p)ˣ) : ZMod p)) * hh
    · rintro ⟨b, rfl⟩
      refine ⟨h * b, ?_⟩
      simp only [Subgroup.coe_mul, Units.val_mul]
      rw [hv']
      ring
  · right
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [periodExponents, Finset.mem_image, Finset.mem_univ, true_and] at hz1 hz2
    obtain ⟨a, ha⟩ := hz1
    obtain ⟨b, hb⟩ := hz2
    apply hc
    refine ⟨a * b⁻¹, Units.ext ?_⟩
    have hbb := val_mul_val_inv H b
    have e1 : (u : ZMod p) * ((a : (ZMod p)ˣ) : ZMod p) = v * ((b : (ZMod p)ˣ) : ZMod p) := by
      rw [ha, hb]
    simp only [Subgroup.coe_mul, Units.val_mul]
    linear_combination (-(((b⁻¹ : H) : (ZMod p)ˣ) : ZMod p)) * e1 + (-(v : ZMod p)) * hbb

/-- The roots of unity occurring in the period of $H$ at $x$. -/
noncomputable def periodRoots (ζ : R) (H : Subgroup (ZMod p)ˣ) (x : ZMod p) : Finset R :=
  (periodExponents H x).image (rootPow ζ)

theorem rootPow_injective {ζ : R} (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (rootPow (p := p) ζ) := by
  intro x y h
  exact ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h)

/-- **Two periods are equal or have no root of unity in common** (*Disq. Arith.*
Art. 344), for $\zeta$ a primitive $p$-th root of unity (the roots $\zeta^k$, $0 \le k < p$, are distinct). -/
@[kb "gauss1801" "Art. 344"]
theorem periodRoots_eq_or_disjoint {ζ : R} (hζ : IsPrimitiveRoot ζ p) (H : Subgroup (ZMod p)ˣ)
    (u v : (ZMod p)ˣ) :
    periodRoots ζ H (u : ZMod p) = periodRoots ζ H (v : ZMod p) ∨
      Disjoint (periodRoots ζ H (u : ZMod p)) (periodRoots ζ H (v : ZMod p)) := by
  unfold periodRoots
  rcases periodExponents_eq_or_disjoint H u v with h | h
  · left; rw [h]
  · right; exact (Finset.disjoint_image (rootPow_injective hζ)).mpr h

/-! ### Partition of the primitive roots -/

/-- **The $e$ periods partition the nonzero exponents** (*Disq. Arith.* Art. 344):
$\sum_{c \in (\mathbb{Z}/p)^\times / H} \eta_c = \sum_{u} \zeta^{u}$ over the units $u$ (a pure reindexing, valid
in any commutative ring). -/
@[kb "gauss1801" "Art. 344"]
theorem sum_cosetPeriod (ζ : R) (H : Subgroup (ZMod p)ˣ) :
    ∑ c, cosetPeriod ζ H c = ∑ u : (ZMod p)ˣ, rootPow ζ (u : ZMod p) := by
  rw [sum_eq_sum_coset H (fun u : (ZMod p)ˣ => rootPow ζ (u : ZMod p))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [cosetPeriod_eq_out]
  unfold periodSum
  simp [Units.val_mul]

theorem sum_units_rootPow (ζ : R) :
    ∑ u : (ZMod p)ˣ, rootPow ζ (u : ZMod p) = ∑ k ∈ Finset.Ico 1 p, ζ ^ k := by
  refine Finset.sum_bij (fun u _ => (u : ZMod p).val) ?_ ?_ ?_ ?_
  · intro u _
    rw [Finset.mem_Ico]
    exact ⟨Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).2 u.ne_zero), ZMod.val_lt _⟩
  · intro a _ b _ h
    exact Units.ext (ZMod.val_injective p h)
  · intro k hk
    rw [Finset.mem_Ico] at hk
    have hk0 : (k : ZMod p) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
    exact ⟨Units.mk0 _ hk0, Finset.mem_univ _, by simp [ZMod.val_cast_of_lt hk.2]⟩
  · intro u _
    rfl

theorem sum_units_rootPow_eq_neg_one [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ p) :
    ∑ u : (ZMod p)ˣ, rootPow ζ (u : ZMod p) = -1 := by
  rw [sum_units_rootPow]
  have h0 := hζ.geom_sum_eq_zero (Fact.out : p.Prime).one_lt
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Fact.out : p.Prime).pos] at h0
  simp only [pow_zero, zero_add] at h0
  linear_combination h0

/-- **The $e$ periods of $f$ terms partition the primitive $p$-th roots of unity** (the historical sources,
Art. 344): their sum is $\sum_{k=1}^{p-1} \zeta^k = -1$ for $\zeta$ a primitive $p$-th root of unity in a domain. -/
@[kb "gauss1801" "Art. 344"]
theorem sum_cosetPeriod_eq_neg_one [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ p)
    (H : Subgroup (ZMod p)ˣ) : ∑ c, cosetPeriod ζ H c = -1 := by
  rw [sum_cosetPeriod, sum_units_rootPow_eq_neg_one hζ]

theorem periodSum_top [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ p) {x : ZMod p} (hx : x ≠ 0) :
    periodSum ζ ⊤ x = -1 := by
  rw [← sum_units_rootPow_eq_neg_one hζ]
  unfold periodSum
  exact Fintype.sum_equiv ((Subgroup.topEquiv.toEquiv).trans (Equiv.mulLeft (Units.mk0 x hx))) _ _
    fun h => by simp

end Basics

section GaussNotation

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime]

/-- **Gauss's period $(f, \lambda)$** (*Disq. Arith.* Art. 343): for $h$ a unit modulo $p$
(Gauss: $h = g^e$ for a primitive root $g$), $f$ a number of terms and $\lambda$ a residue modulo $p$,
$\sum_{j=0}^{f-1} \zeta^{\lambda h^{j}}$. (Gauss's index $j$ already starts at $0$.) -/
noncomputable def gaussPeriod (ζ : R) (f : ℕ) (h : (ZMod p)ˣ) (lam : ZMod p) : R :=
  ∑ j ∈ Finset.range f, rootPow ζ (lam * ((h ^ j : (ZMod p)ˣ) : ZMod p))

theorem gaussPeriod_eq_periodSum (ζ : R) {f : ℕ} {h : (ZMod p)ˣ} (hf : orderOf h = f)
    (lam : ZMod p) : gaussPeriod ζ f h lam = periodSum ζ (Subgroup.zpowers h) lam := by
  subst hf
  unfold gaussPeriod periodSum
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => rootPow ζ (lam * ((h ^ j : (ZMod p)ˣ) : ZMod p))) (orderOf h)]
  exact Fintype.sum_equiv (finEquivZPowers (isOfFinOrder_of_finite h)) _ _
    (fun j => by simp [finEquivZPowers_apply])

/-- $g$ is a primitive root modulo $p$: it generates the cyclic group $(\mathbb{Z}/p)^\times$ of order $p - 1$. -/
def IsPrimitiveRootModulo (g : (ZMod p)ˣ) : Prop := orderOf g = p - 1

theorem orderOf_pow_primitiveRoot {g : (ZMod p)ˣ} (hg : IsPrimitiveRootModulo g) {e f : ℕ}
    (hef : e * f = p - 1) : orderOf (g ^ e) = f := by
  have hp := (Fact.out : p.Prime).two_le
  have he : e ≠ 0 := by
    rintro rfl
    omega
  rw [orderOf_pow_of_dvd he (by rw [hg, ← hef]; exact dvd_mul_right e f), hg, ← hef]
  exact Nat.mul_div_cancel_left f (Nat.pos_of_ne_zero he)

theorem zpowers_eq_top_of_primitiveRoot {g : (ZMod p)ˣ} (hg : IsPrimitiveRootModulo g) :
    Subgroup.zpowers g = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, hg, Nat.card_eq_fintype_card, ZMod.card_units]

/-- **Gauss's period depends only on the subgroup, not on $g$** (Art. 343): if $g, g'$ are primitive roots modulo
$p$ and $p - 1 = e f$, then $g^e$ and $g'^e$ generate the same subgroup of $(\mathbb{Z}/p)^\times$. -/
theorem zpowers_pow_eq {g g' : (ZMod p)ˣ} (hg : IsPrimitiveRootModulo g)
    (hg' : IsPrimitiveRootModulo g') {e f : ℕ} (hef : e * f = p - 1) :
    Subgroup.zpowers (g ^ e) = Subgroup.zpowers (g' ^ e) := by
  have hmem : g' ∈ Subgroup.zpowers g := by
    rw [zpowers_eq_top_of_primitiveRoot hg]; exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hle : Subgroup.zpowers (g' ^ e) ≤ Subgroup.zpowers (g ^ e) := by
    rw [Subgroup.zpowers_le]
    have : g' ^ e = (g ^ e) ^ k := by
      rw [← hk, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_pow_primitiveRoot hg hef,
    orderOf_pow_primitiveRoot hg' hef]

/-- **$\langle g^e \rangle$ is the unique subgroup of order $f$** (*Disq. Arith.*
Art. 343): any subgroup of $(\mathbb{Z}/p)^\times$ with $f$ elements is generated by $g^e$ (Mathlib's uniqueness of
subgroups of a given order in a cyclic group). -/
theorem eq_zpowers_of_card_eq {g : (ZMod p)ˣ} (hg : IsPrimitiveRootModulo g) {e f : ℕ}
    (hef : e * f = p - 1) (K : Subgroup (ZMod p)ˣ) (hK : Nat.card K = f) :
    K = Subgroup.zpowers (g ^ e) := by
  rw [IsCyclic.subgroup_eq_iff_card_eq, hK, Nat.card_zpowers, orderOf_pow_primitiveRoot hg hef]

/-- **Independence of the primitive root** (*Disq. Arith.* Art. 343): the period
$(f, \lambda)$ is the same whether computed with $h = g^e$ or $h = g'^e$ for primitive roots $g, g'$,
$p - 1 = e f$. -/
@[kb "gauss1801" "Art. 343"]
theorem gaussPeriod_eq_of_primitiveRoots (ζ : R) {g g' : (ZMod p)ˣ} (hg : IsPrimitiveRootModulo g)
    (hg' : IsPrimitiveRootModulo g') {e f : ℕ} (hef : e * f = p - 1) (lam : ZMod p) :
    gaussPeriod ζ f (g ^ e) lam = gaussPeriod ζ f (g' ^ e) lam := by
  rw [gaussPeriod_eq_periodSum ζ (orderOf_pow_primitiveRoot hg hef),
    gaussPeriod_eq_periodSum ζ (orderOf_pow_primitiveRoot hg' hef), zpowers_pow_eq hg hg' hef]

/-- **The period depends only on the coset of $\lambda$ modulo the subgroup $H$ of order $f$** (Art. 343):
$(f, \lambda h^{j}) = (f, \lambda)$. -/
@[kb "gauss1801" "Art. 343"]
theorem gaussPeriod_mul_pow (ζ : R) {f : ℕ} {h : (ZMod p)ˣ} (hf : orderOf h = f)
    (lam : ZMod p) (j : ℕ) :
    gaussPeriod ζ f h (lam * ((h ^ j : (ZMod p)ˣ) : ZMod p)) = gaussPeriod ζ f h lam := by
  rw [gaussPeriod_eq_periodSum ζ hf, gaussPeriod_eq_periodSum ζ hf]
  exact periodSum_mul_of_mem ζ _ lam (Subgroup.pow_mem _ (Subgroup.mem_zpowers h) j)

/-- **Product of two periods** (*Disq. Arith.* Art. 345):
$(f, \lambda)(f, \mu) = \sum_{j=0}^{f-1} (f, \lambda h^{j} + \mu)$, where $(f, 0) = f$ (here `periodSum` at $0$ is
`Nat.card`, see `periodSum_zero`). Stated for `gaussPeriod`, with $h$ of order $f$ and $\zeta^p = 1$. -/
@[kb "gauss1801" "Art. 345"]
theorem gaussPeriod_mul_gaussPeriod {ζ : R} (hζ : ζ ^ p = 1) {f : ℕ} {h : (ZMod p)ˣ}
    (hf : orderOf h = f) (lam mu : ZMod p) :
    gaussPeriod ζ f h lam * gaussPeriod ζ f h mu
      = ∑ j ∈ Finset.range f, gaussPeriod ζ f h (lam * ((h ^ j : (ZMod p)ˣ) : ZMod p) + mu) := by
  have key : ∀ x, gaussPeriod ζ f h x = periodSum ζ (Subgroup.zpowers h) x :=
    gaussPeriod_eq_periodSum ζ hf
  simp only [key]
  rw [periodSum_mul_periodSum hζ]
  subst hf
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => periodSum ζ (Subgroup.zpowers h) (lam * ((h ^ j : (ZMod p)ˣ) : ZMod p) + mu))
    (orderOf h)]
  exact (Fintype.sum_equiv (finEquivZPowers (isOfFinOrder_of_finite h)) _ _
    (fun j => by simp [finEquivZPowers_apply])).symm

end GaussNotation

section Tower

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime]

/-- **The periods of $\gamma$ terms inside the period of $\beta\gamma$ terms** (the historical sources,
*Disq. Arith.* Art. 342, 350). For subgroups $H, H'$ of $(\mathbb{Z}/p)^\times$ (in Gauss's use $H \le H'$, of
orders $\gamma$ and $\beta\gamma$) and $x \in \mathbb{Z}/p$, this sends the coset $u K$ of $K = H \cap H'$ in
$H'$ to the period $\eta_H(x u)$ of $H$ (well defined, by `periodSum_mul_of_mem`). -/
noncomputable def quotPeriod (ζ : R) (H H' : Subgroup (ZMod p)ˣ) (x : ZMod p) :
    H' ⧸ H.subgroupOf H' → R :=
  Quotient.lift (fun u : H' => periodSum ζ H (x * ((u : (ZMod p)ˣ) : ZMod p))) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ H.subgroupOf H' := QuotientGroup.leftRel_apply.mp hab
    have hmem : (((a⁻¹ * b : H') : (ZMod p)ˣ)) ∈ H := hab'
    have := periodSum_mul_of_mem ζ H (x * ((a : (ZMod p)ˣ) : ZMod p)) hmem
    rw [← this]
    congr 1
    rw [mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel_left])

theorem quotPeriod_mk (ζ : R) (H H' : Subgroup (ZMod p)ˣ) (x : ZMod p) (u : H') :
    quotPeriod ζ H H' x (QuotientGroup.mk u) = periodSum ζ H (x * ((u : (ZMod p)ˣ) : ZMod p)) :=
  rfl

theorem quotPeriod_eq_out (ζ : R) (H H' : Subgroup (ZMod p)ˣ) (x : ZMod p)
    (c : H' ⧸ H.subgroupOf H') :
    quotPeriod ζ H H' x c = periodSum ζ H (x * (((c.out : H') : (ZMod p)ˣ) : ZMod p)) := by
  conv_lhs => rw [← QuotientGroup.out_eq' c]
  rfl

/-- **The period of $\beta\gamma$ terms is the sum of the $\beta$ periods of $\gamma$ terms it contains**
(Art. 343, and Art. 342 and 350): for subgroups $H \le H'$ of
$(\mathbb{Z}/p)^\times$ (of orders $\gamma$ and $\beta\gamma$),
$\sum_{h' \in H'} \zeta^{x h'} = \sum_{c \in H'/H} \sum_{h \in H} \zeta^{x \tilde c h}$, with $\tilde c$ a
representative of $c$ (`quotPeriod`). -/
@[kb "gauss1801" "Art. 343"]
theorem periodSum_eq_sum_quotPeriod (ζ : R) {H H' : Subgroup (ZMod p)ˣ} (hle : H ≤ H')
    (x : ZMod p) :
    periodSum ζ H' x = ∑ c : H' ⧸ H.subgroupOf H', quotPeriod ζ H H' x c := by
  unfold periodSum
  rw [sum_eq_sum_coset (H.subgroupOf H') (fun h : H' => rootPow ζ (x * ((h : (ZMod p)ˣ) : ZMod p)))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [quotPeriod_eq_out]
  unfold periodSum
  refine Fintype.sum_equiv (Subgroup.subgroupOfEquivOfLe hle).toEquiv _ _ fun k => ?_
  show rootPow ζ (x * (((c.out * (k : H') : H') : (ZMod p)ˣ) : ZMod p))
    = rootPow ζ (x * (((c.out : H') : (ZMod p)ˣ) : ZMod p) * ((k : (ZMod p)ˣ) : ZMod p))
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [mul_assoc]

/-- **The polynomial of the tower** (*Disq. Arith.* Art. 350): the monic polynomial
of degree $\beta$ whose roots are the $\beta$ periods of $\gamma$ terms contained in the period of $\beta\gamma$
terms at $x$, $\prod_{c \in H'/H} (X - \eta_c)$ (`towerPoly_monic`, `towerPoly_natDegree`). -/
@[kb "gauss1801" "Art. 350"]
noncomputable def towerPoly (ζ : R) (H H' : Subgroup (ZMod p)ˣ) (x : ZMod p) : Polynomial R :=
  ∏ c : H' ⧸ H.subgroupOf H', (Polynomial.X - Polynomial.C (quotPeriod ζ H H' x c))

theorem towerPoly_monic (ζ : R) (H H' : Subgroup (ZMod p)ˣ) (x : ZMod p) :
    (towerPoly ζ H H' x).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem towerPoly_natDegree (ζ : R) (H H' : Subgroup (ZMod p)ˣ) (x : ZMod p) [Nontrivial R] :
    (towerPoly ζ H H' x).natDegree = Nat.card (H' ⧸ H.subgroupOf H') := by
  unfold towerPoly
  rw [Polynomial.natDegree_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _]
  simp [Nat.card_eq_fintype_card]

/-! #### The group ring and the invariance argument -/

/-- The integral group ring of the additive group $\mathbb{Z}/p$ (the "generic" root of unity lives here). -/
abbrev GroupRing (p : ℕ) := AddMonoidAlgebra ℤ (ZMod p)

/-- The generic $p$-th root of unity: the basis element at $1 \in \mathbb{Z}/p$. -/
noncomputable def genericRoot (p : ℕ) : GroupRing p := AddMonoidAlgebra.single 1 1

theorem genericRoot_pow (n : ℕ) :
    genericRoot p ^ n = AddMonoidAlgebra.single (n : ZMod p) 1 := by
  induction n with
  | zero => simp [genericRoot, AddMonoidAlgebra.one_def]
  | succ n ih =>
    rw [pow_succ, ih, genericRoot, AddMonoidAlgebra.single_mul_single]
    simp [Nat.cast_succ]

theorem genericRoot_pow_prime : genericRoot p ^ p = 1 := by
  rw [genericRoot_pow, ZMod.natCast_self, AddMonoidAlgebra.one_def]

theorem rootPow_genericRoot (x : ZMod p) :
    rootPow (genericRoot p) x = AddMonoidAlgebra.single x 1 := by
  rw [rootPow, genericRoot_pow, ZMod.natCast_zmod_val]

/-- The evaluation homomorphism from the group ring: $\mathrm{single}_x 1 \mapsto \zeta^x$. -/
noncomputable def evalRoot {ζ : R} (hζ : ζ ^ p = 1) : GroupRing p →ₐ[ℤ] R :=
  AddMonoidAlgebra.lift ℤ R (ZMod p)
    { toFun := fun x => rootPow ζ (Multiplicative.toAdd x)
      map_one' := rootPow_zero ζ
      map_mul' := fun x y => rootPow_add hζ _ _ }

theorem evalRoot_single {ζ : R} (hζ : ζ ^ p = 1) (x : ZMod p) :
    evalRoot hζ (AddMonoidAlgebra.single x 1) = rootPow ζ x := by
  simp [evalRoot, AddMonoidAlgebra.lift_single]

theorem evalRoot_rootPow {ζ : R} (hζ : ζ ^ p = 1) (x : ZMod p) :
    evalRoot hζ (rootPow (genericRoot p) x) = rootPow ζ x := by
  rw [rootPow_genericRoot, evalRoot_single]

theorem evalRoot_periodSum {ζ : R} (hζ : ζ ^ p = 1) (H : Subgroup (ZMod p)ˣ) (x : ZMod p) :
    evalRoot hζ (periodSum (genericRoot p) H x) = periodSum ζ H x := by
  unfold periodSum
  rw [map_sum]
  exact Finset.sum_congr rfl fun h _ => evalRoot_rootPow hζ _

theorem evalRoot_quotPeriod {ζ : R} (hζ : ζ ^ p = 1) (H H' : Subgroup (ZMod p)ˣ) (x : ZMod p)
    (c : H' ⧸ H.subgroupOf H') :
    evalRoot hζ (quotPeriod (genericRoot p) H H' x c) = quotPeriod ζ H H' x c := by
  induction c using QuotientGroup.induction_on with
  | H u => exact evalRoot_periodSum hζ H _

/-- The substitution $\zeta^{k} \mapsto \zeta^{m k}$ (multiplier $m$) on the group ring. -/
noncomputable def multiplier (m : ZMod p) : GroupRing p →ₐ[ℤ] GroupRing p :=
  AddMonoidAlgebra.lift ℤ (GroupRing p) (ZMod p)
    { toFun := fun x => AddMonoidAlgebra.single (m * Multiplicative.toAdd x) 1
      map_one' := by simp [AddMonoidAlgebra.one_def]
      map_mul' := fun x y => by
        simp [AddMonoidAlgebra.single_mul_single, mul_add] }

theorem multiplier_single (m x : ZMod p) (c : ℤ) :
    multiplier m (AddMonoidAlgebra.single x c) = AddMonoidAlgebra.single (m * x) c := by
  simp [multiplier, AddMonoidAlgebra.lift_single, AddMonoidAlgebra.smul_single']

theorem multiplier_periodSum (m : ZMod p) (H : Subgroup (ZMod p)ˣ) (x : ZMod p) :
    multiplier m (periodSum (genericRoot p) H x) = periodSum (genericRoot p) H (m * x) := by
  unfold periodSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [rootPow_genericRoot, rootPow_genericRoot, multiplier_single, mul_assoc]

theorem coeff_multiplier {m : ZMod p} (hm : m ≠ 0) (a : GroupRing p) (x : ZMod p) :
    (multiplier m a).coeff (m * x) = a.coeff x := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [map_add, AddMonoidAlgebra.coeff_add, ha, hb]
  | single y c =>
    rw [multiplier_single]
    simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hm]

/-- An element of the group ring fixed by the multipliers of $H'$ lies in the integer span of $1$ and the periods
of $H'$ (it is constant on the orbits $\{0\}$ and $x H'$). -/
theorem mem_periodSpan_of_fixed (H' : Subgroup (ZMod p)ˣ) (a : GroupRing p)
    (hfix : ∀ m : H', multiplier (((m : (ZMod p)ˣ) : ZMod p)) a = a) :
    a ∈ periodSpan (genericRoot p) H' := by
  have hconst : ∀ (m : H') (x : ZMod p), a.coeff (((m : (ZMod p)ˣ) : ZMod p) * x) = a.coeff x := by
    intro m x
    have := coeff_multiplier (Units.ne_zero (m : (ZMod p)ˣ)) a x
    rwa [hfix m] at this
  have hdecomp : a = ∑ x : ZMod p, AddMonoidAlgebra.single x (a.coeff x) := by
    conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single a]
    exact Finsupp.sum_fintype _ _ fun x => AddMonoidAlgebra.single_zero x
  rw [hdecomp, sum_zmod_eq, sum_eq_sum_coset H'
    (fun u : (ZMod p)ˣ => AddMonoidAlgebra.single (u : ZMod p) (a.coeff (u : ZMod p)))]
  refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun c _ => ?_)
  · have : (AddMonoidAlgebra.single (0 : ZMod p) (a.coeff 0) : GroupRing p) = (a.coeff 0) • 1 := by
      rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.smul_single']
      simp
    rw [this]
    exact Submodule.smul_mem _ _ (one_mem_periodSpan _ _)
  · have hc : ∑ k : H', AddMonoidAlgebra.single (((c.out * (k : (ZMod p)ˣ) : (ZMod p)ˣ)) : ZMod p)
          (a.coeff (((c.out * (k : (ZMod p)ˣ) : (ZMod p)ˣ)) : ZMod p))
        = (a.coeff (c.out : ZMod p)) • periodSum (genericRoot p) H' (c.out : ZMod p) := by
      unfold periodSum
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [rootPow_genericRoot, AddMonoidAlgebra.smul_single', mul_one, Units.val_mul]
      have := hconst k (c.out : ZMod p)
      rw [mul_comm ((k : (ZMod p)ˣ) : ZMod p)] at this
      rw [this]
    rw [hc]
    exact Submodule.smul_mem _ _ (periodSum_mem_periodSpan _ _ _)

theorem towerPoly_map_multiplier (H H' : Subgroup (ZMod p)ˣ) (x : ZMod p) (m : H') :
    (towerPoly (genericRoot p) H H' x).map
        (multiplier (((m : (ZMod p)ˣ) : ZMod p)) : GroupRing p →+* GroupRing p)
      = towerPoly (genericRoot p) H H' x := by
  unfold towerPoly
  rw [Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [← Equiv.prod_comp (MulAction.toPerm m)
    (fun c => Polynomial.X - Polynomial.C (quotPeriod (genericRoot p) H H' x c))]
  refine Finset.prod_congr rfl fun c _ => ?_
  congr 2
  induction c using QuotientGroup.induction_on with
  | H u =>
    show multiplier _ (periodSum _ H _) = periodSum _ H _
    rw [multiplier_periodSum]
    congr 1
    simp only [smul_eq_mul, Subgroup.coe_mul, Units.val_mul]
    ring

/-- **The tower (*Disq. Arith.* Art. 342, 350-351).** Let $H \le H'$ be subgroups of
$(\mathbb{Z}/p)^\times$ (orders $\gamma$ and $\beta\gamma$, so $p - 1 = \alpha\beta\gamma$ with $\alpha$ the index
of $H'$), $x \in \mathbb{Z}/p$, and $\zeta^p = 1$. The monic polynomial of degree $\beta$ with the $\beta$ periods of
$\gamma$ terms in the period of $\beta\gamma$ terms at $x$ as roots (`towerPoly`) has every coefficient in the
integer span of $1$ and the $\alpha$ periods of $\beta\gamma$ terms (`periodSpan`). Proved without assuming
$\zeta$ primitive, by transport from the integral group ring, where coefficients fixed by the multipliers in $H'$
are integer combinations of orbit sums. -/
@[kb "gauss1801" "Art. 350"]
theorem towerPoly_coeff_mem_periodSpan {ζ : R} (hζ : ζ ^ p = 1) (H H' : Subgroup (ZMod p)ˣ)
    (x : ZMod p) (i : ℕ) : (towerPoly ζ H H' x).coeff i ∈ periodSpan ζ H' := by
  have hmap : towerPoly ζ H H' x
      = (towerPoly (genericRoot p) H H' x).map (evalRoot hζ : GroupRing p →+* R) := by
    unfold towerPoly
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun c _ => ?_
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rw [← evalRoot_quotPeriod hζ]
    rfl
  have hfix : (towerPoly (genericRoot p) H H' x).coeff i ∈ periodSpan (genericRoot p) H' := by
    refine mem_periodSpan_of_fixed H' _ fun m => ?_
    have := congrArg (fun P => P.coeff i) (towerPoly_map_multiplier H H' x m)
    simpa [Polynomial.coeff_map] using this
  have hle : (periodSpan (genericRoot p) H').map (evalRoot hζ).toLinearMap ≤ periodSpan ζ H' := by
    unfold periodSpan
    rw [Submodule.map_span_le]
    intro g hg
    rcases hg with rfl | ⟨u, rfl⟩
    · simp only [AlgHom.toLinearMap_apply, map_one]
      exact one_mem_periodSpan ζ H'
    · simp only [AlgHom.toLinearMap_apply]
      rw [evalRoot_periodSum]
      exact periodSum_mem_periodSpan ζ H' _
  rw [hmap, Polynomial.coeff_map]
  exact hle (Submodule.mem_map_of_mem hfix)

/-- **The case $\alpha = 1$ (Art. 351)**: for $H' = (\mathbb{Z}/p)^\times$ (the period of all $p - 1$ terms, which is
$-1$) the coefficients of `towerPoly` are integers. Here $\zeta$ is a primitive $p$-th root of unity in a domain. -/
@[kb "gauss1801" "Art. 351"]
theorem towerPoly_coeff_int [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ p)
    (H : Subgroup (ZMod p)ˣ) (x : ZMod p) (i : ℕ) :
    ∃ n : ℤ, (towerPoly ζ H ⊤ x).coeff i = n := by
  have hζ' : ζ ^ p = 1 := hζ.pow_eq_one
  have hmem := towerPoly_coeff_mem_periodSpan hζ' H ⊤ x i
  have hle : periodSpan ζ (⊤ : Subgroup (ZMod p)ˣ) ≤ Submodule.span ℤ {(1 : R)} := by
    unfold periodSpan
    rw [Submodule.span_le]
    intro g hg
    rcases hg with rfl | ⟨u, rfl⟩
    · exact Submodule.subset_span rfl
    · show periodSum ζ ⊤ (u : ZMod p) ∈ _
      rw [periodSum_top hζ u.ne_zero]
      exact Submodule.neg_mem _ (Submodule.subset_span rfl)
  obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp (hle hmem)
  exact ⟨n, by rw [← hn]; simp⟩

end Tower
