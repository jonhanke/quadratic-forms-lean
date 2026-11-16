import QuadFormsKB.Historical.Gauss.Periods
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The decomposition $4\Phi_p = Y^2 \mp p Z^2$ (Disquisitiones Arithmeticae, Art. 357)

the historical sources (Gauss, *Disq. Arith.* Art. 357; promised in Art. 124).

Let $p$ be an odd prime, $\zeta$ a primitive $p$-th root of unity in a field $K$ of characteristic zero,
$z = \prod_{a \text{ residue}} (X - \zeta^{a})$ and $z' = \prod_{a \text{ nonresidue}} (X - \zeta^{a})$, the products
running over the units of $\mathbb{Z}/p$ that are (respectively are not) squares. Proved, unconditionally:

* `gauss_cyclotomic_decomposition`: there are $Y, Z \in \mathbb{Z}[X]$ and $s \in K$ with $s^2 = p^* =
  (-1)^{(p-1)/2} p$, $2 z = Y + s Z$, $2 z' = Y - s Z$, and $4 \Phi_p = Y^2 - p^* Z^2$ in $\mathbb{Z}[X]$.
* `gauss_four_cyclotomic`: the integral identity $4\Phi_p = Y^2 - p^* Z^2$ with no field in the statement.
* Concrete checks for $p = 5$ and $p = 7$ (`four_cyclotomic_five`, `four_cyclotomic_seven`).

Route: coefficients of `towerPoly` (with the trivial subgroup and the subgroup of squares) lie in
$\mathbb{Z} + \mathbb{Z}\eta_0 + \mathbb{Z}\eta_1$ (`towerPoly_coeff_mem_periodSpan`, in the group ring); the
multiplier of a nonresidue exchanges $\eta_0, \eta_1$ and $z, z'$; $\eta_0 + \eta_1 = -1$ and
$(\eta_0 - \eta_1)^2 = p^*$ (quadratic Gauss sum, Mathlib's `gaussSum_sq`).

Not proved: the leading terms $Y = 2X^m + X^{m-1} + \dots$, $Z = X^{m-1} + \dots$ ($m = (p-1)/2$) of the historical sources
statement. (The degrees and the signs of $Y, Z$ are not pinned down by `gauss_cyclotomic_decomposition`: it asserts
existence only, and $(Y, Z)$ is unique only up to the sign of $(s, Z)$.)
-/

namespace QuadFormsKB.Historical.Gauss

open scoped Classical
open Polynomial

section Squares

variable {p : ℕ} [Fact p.Prime]

/-- The subgroup of squares (quadratic residues) of $(\mathbb{Z}/p)^\times$. -/
def squaresSubgroup (p : ℕ) [Fact p.Prime] : Subgroup (ZMod p)ˣ :=
  (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range

theorem mem_squaresSubgroup {u : (ZMod p)ˣ} : u ∈ squaresSubgroup p ↔ IsSquare u := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, by simp [pow_two]⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, by simp [pow_two, hr]⟩

theorem isSquare_val_iff (u : (ZMod p)ˣ) : IsSquare (u : ZMod p) ↔ IsSquare u := by
  constructor
  · rintro ⟨r, hr⟩
    have hu : IsUnit (r * r) := hr ▸ u.isUnit
    obtain ⟨r', rfl⟩ := (IsUnit.mul_iff.mp hu).1
    exact ⟨r', Units.ext (by simpa using hr)⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, by simp⟩

theorem exists_nonsquare_unit (hp : p ≠ 2) : ∃ a : (ZMod p)ˣ, ¬ IsSquare a := by
  have hc : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hc
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha ⟨0, by simp⟩
  refine ⟨Units.mk0 a ha0, fun h => ha ?_⟩
  exact (isSquare_val_iff _).mpr h

theorem squares_cover {a : (ZMod p)ˣ} (ha : ¬ IsSquare a) (u : (ZMod p)ˣ) :
    u ∈ squaresSubgroup p ∨ ∃ h ∈ squaresSubgroup p, u = a * h := by
  by_cases hu : IsSquare u
  · exact Or.inl (mem_squaresSubgroup.mpr hu)
  · right
    refine ⟨a⁻¹ * u, ?_, (mul_inv_cancel_left a u).symm⟩
    rw [mem_squaresSubgroup]
    have h1 : quadraticChar (ZMod p) (u : ZMod p) = -1 :=
      quadraticChar_neg_one_iff_not_isSquare.mpr (fun h => hu ((isSquare_val_iff u).mp h))
    have h2 : quadraticChar (ZMod p) (a : ZMod p) = -1 :=
      quadraticChar_neg_one_iff_not_isSquare.mpr (fun h => ha ((isSquare_val_iff a).mp h))
    have h3 : quadraticChar (ZMod p) ((u : ZMod p) * (a : ZMod p)) = 1 := by
      rw [map_mul, h1, h2]; norm_num
    have h4 : IsSquare ((u : ZMod p) * (a : ZMod p)) :=
      (quadraticChar_one_iff_isSquare (mul_ne_zero u.ne_zero a.ne_zero)).mp h3
    have h5 : IsSquare (u * a) := by
      rw [← isSquare_val_iff, Units.val_mul]; exact h4
    obtain ⟨r, hr⟩ := h5
    refine ⟨a⁻¹ * r, ?_⟩
    rw [mul_mul_mul_comm, ← hr, mul_comm u a, ← mul_assoc, inv_mul_cancel_right]

theorem mul_not_mem_squares {a : (ZMod p)ˣ} (ha : ¬ IsSquare a) {h : (ZMod p)ˣ}
    (hh : h ∈ squaresSubgroup p) : a * h ∉ squaresSubgroup p := by
  intro hm
  apply ha
  rw [← mem_squaresSubgroup]
  have := Subgroup.mul_mem _ hm (Subgroup.inv_mem _ hh)
  simpa using this

/-- Splitting a product over the units into residues and nonresidues, the nonresidues being $a h$ with $h$ a
residue, for a fixed nonresidue $a$. -/
theorem prod_units_split {M : Type*} [CommMonoid M] (F : (ZMod p)ˣ → M) {a : (ZMod p)ˣ}
    (ha : ¬ IsSquare a) :
    ∏ u, F u = (∏ h : squaresSubgroup p, F h) * ∏ h : squaresSubgroup p, F (a * h) := by
  have e1 : ∏ u ∈ Finset.univ.filter (fun u : (ZMod p)ˣ => u ∈ squaresSubgroup p), F u
      = ∏ h : squaresSubgroup p, F h :=
    Finset.prod_subtype _ (fun x => by simp) F
  have e2 : ∏ u ∈ Finset.univ.filter (fun u : (ZMod p)ˣ => ¬ u ∈ squaresSubgroup p), F u
      = ∏ h : squaresSubgroup p, F (a * h) := by
    symm
    refine Finset.prod_bij (fun (h : squaresSubgroup p) _ => a * (h : (ZMod p)ˣ)) ?_ ?_ ?_ ?_
    · intro h _
      simpa using mul_not_mem_squares ha h.2
    · intro h _ h' _ hh
      exact Subtype.ext (mul_left_cancel hh)
    · intro b hb
      have hb' : b ∉ squaresSubgroup p := by simpa using hb
      rcases squares_cover ha b with h | ⟨h, hh, rfl⟩
      · exact absurd h hb'
      · exact ⟨⟨h, hh⟩, Finset.mem_univ _, rfl⟩
    · intro h _
      rfl
  rw [← e1, ← e2, Finset.prod_filter_mul_prod_filter_not]

/-- Additive version of `prod_units_split`. -/
theorem sum_units_split {M : Type*} [AddCommMonoid M] (F : (ZMod p)ˣ → M) {a : (ZMod p)ˣ}
    (ha : ¬ IsSquare a) :
    ∑ u, F u = (∑ h : squaresSubgroup p, F h) + ∑ h : squaresSubgroup p, F (a * h) := by
  have e1 : ∑ u ∈ Finset.univ.filter (fun u : (ZMod p)ˣ => u ∈ squaresSubgroup p), F u
      = ∑ h : squaresSubgroup p, F h :=
    Finset.sum_subtype _ (fun x => by simp) F
  have e2 : ∑ u ∈ Finset.univ.filter (fun u : (ZMod p)ˣ => ¬ u ∈ squaresSubgroup p), F u
      = ∑ h : squaresSubgroup p, F (a * h) := by
    symm
    refine Finset.sum_bij (fun (h : squaresSubgroup p) _ => a * (h : (ZMod p)ˣ)) ?_ ?_ ?_ ?_
    · intro h _
      simpa using mul_not_mem_squares ha h.2
    · intro h _ h' _ hh
      exact Subtype.ext (mul_left_cancel hh)
    · intro b hb
      have hb' : b ∉ squaresSubgroup p := by simpa using hb
      rcases squares_cover ha b with h | ⟨h, hh, rfl⟩
      · exact absurd h hb'
      · exact ⟨⟨h, hh⟩, Finset.mem_univ _, rfl⟩
    · intro h _
      rfl
  rw [← e1, ← e2, Finset.sum_filter_add_sum_filter_not]

theorem prod_filter_isSquare {M : Type*} [CommMonoid M] (F : (ZMod p)ˣ → M) :
    ∏ u ∈ Finset.univ.filter (fun u : (ZMod p)ˣ => IsSquare u), F u
      = ∏ h : squaresSubgroup p, F h :=
  Finset.prod_subtype _ (fun x => by simp [mem_squaresSubgroup]) F

theorem prod_filter_not_isSquare {M : Type*} [CommMonoid M] (F : (ZMod p)ˣ → M) {a : (ZMod p)ˣ}
    (ha : ¬ IsSquare a) :
    ∏ u ∈ Finset.univ.filter (fun u : (ZMod p)ˣ => ¬ IsSquare u), F u
      = ∏ h : squaresSubgroup p, F (a * h) := by
  symm
  refine Finset.prod_bij (fun (h : squaresSubgroup p) _ => a * (h : (ZMod p)ˣ)) ?_ ?_ ?_ ?_
  · intro h _
    simpa [mem_squaresSubgroup] using mul_not_mem_squares ha h.2
  · intro h _ h' _ hh
    exact Subtype.ext (mul_left_cancel hh)
  · intro b hb
    have hb' : ¬ IsSquare b := by simpa using hb
    rcases squares_cover ha b with h | ⟨h, hh, rfl⟩
    · exact absurd (mem_squaresSubgroup.mp h) hb'
    · exact ⟨⟨h, hh⟩, Finset.mem_univ _, rfl⟩
  · intro h _
    rfl

end Squares

section Generic

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime]

/-- `towerPoly` for the trivial subgroup is the product of $X - \zeta^{x h}$ over $h \in H'$. -/
theorem towerPoly_bot_eq_prod (ζ : R) (H' : Subgroup (ZMod p)ˣ) (x : ZMod p) :
    towerPoly ζ ⊥ H' x
      = ∏ h : H', (X - C (rootPow ζ (x * ((h : (ZMod p)ˣ) : ZMod p)))) := by
  unfold towerPoly
  refine Finset.prod_bij (fun c _ => c.out) ?_ ?_ ?_ ?_
  · intros; exact Finset.mem_univ _
  · intro c _ d _ h
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d, h]
  · intro u _
    let q : H' ⧸ (⊥ : Subgroup (ZMod p)ˣ).subgroupOf H' := QuotientGroup.mk u
    refine ⟨q, Finset.mem_univ _, ?_⟩
    have h0 : (QuotientGroup.mk q.out : H' ⧸ (⊥ : Subgroup (ZMod p)ˣ).subgroupOf H')
        = QuotientGroup.mk u := QuotientGroup.out_eq' q
    have h1 := QuotientGroup.eq.mp h0
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at h1
    have h2 : q.out⁻¹ * u = 1 :=
      Subtype.ext (by simpa using h1)
    exact inv_mul_eq_one.mp h2
  · intro c _
    rw [quotPeriod_eq_out]
    simp [periodSum]
    rw [show ((default : (⊥ : Subgroup (ZMod p)ˣ)) : (ZMod p)ˣ) = 1 from
      Subgroup.mem_bot.mp (default : (⊥ : Subgroup (ZMod p)ˣ)).2]
    simp

theorem towerPoly_eval {ζ : R} (hζ : ζ ^ p = 1) (H H' : Subgroup (ZMod p)ˣ) (x : ZMod p) :
    towerPoly ζ H H' x
      = (towerPoly (genericRoot p) H H' x).map (evalRoot hζ : GroupRing p →+* R) := by
  unfold towerPoly
  rw [Polynomial.map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [← evalRoot_quotPeriod hζ]
  rfl

theorem towerPoly_map_multiplier_shift (H H' : Subgroup (ZMod p)ˣ) (x m : ZMod p) :
    (towerPoly (genericRoot p) H H' x).map (multiplier m : GroupRing p →+* GroupRing p)
      = towerPoly (genericRoot p) H H' (m * x) := by
  unfold towerPoly
  rw [Polynomial.map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  congr 2
  induction c using QuotientGroup.induction_on with
  | H u =>
    show multiplier m (periodSum _ H _) = periodSum _ H _
    rw [multiplier_periodSum, mul_assoc]

/-- An element of the integer span of $1$ and the periods of $H'$ is an integer combination of $1$, the period at
$1$ and the period at $a$, provided every unit is in $H'$ or in $a H'$. -/
theorem exists_abc {ζ : R} {H' : Subgroup (ZMod p)ˣ} {a : (ZMod p)ˣ}
    (hcov : ∀ u : (ZMod p)ˣ, u ∈ H' ∨ ∃ h ∈ H', u = a * h) {x : R}
    (hx : x ∈ periodSpan ζ H') :
    ∃ A B C : ℤ, x = A • (1 : R) + B • periodSum ζ H' 1 + C • periodSum ζ H' (a : ZMod p) := by
  unfold periodSpan at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨u, rfl⟩
    · exact ⟨1, 0, 0, by simp⟩
    · rcases hcov u with hu | ⟨h, hh, rfl⟩
      · refine ⟨0, 1, 0, ?_⟩
        have := periodSum_mul_of_mem ζ H' 1 hu
        rw [one_mul] at this
        simp [this]
      · refine ⟨0, 0, 1, ?_⟩
        have := periodSum_mul_of_mem ζ H' (a : ZMod p) hh
        simp [Units.val_mul, this]
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, B, C, rfl⟩ := hx
    obtain ⟨A', B', C', rfl⟩ := hy
    refine ⟨A + A', B + B', C + C', ?_⟩
    simp only [add_smul]
    abel
  | smul c x _ hx =>
    obtain ⟨A, B, C, rfl⟩ := hx
    refine ⟨c * A, c * B, c * C, ?_⟩
    simp only [smul_add, smul_smul]

/-- **Coefficients of the two polynomials $z, z'$** (a step towards the historical sources): let $H'$ be a
subgroup of $(\mathbb{Z}/p)^\times$, $a$ a unit such that every unit lies in $H'$ or in $a H'$ and $a^2 \in H'$.
Then the coefficients of `towerPoly ζ ⊥ H' 1` and `towerPoly ζ ⊥ H' a` are $A_i + B_i \eta_0 + C_i \eta_1$ and
$A_i + B_i \eta_1 + C_i \eta_0$ with the same integers $A_i, B_i, C_i$, where $\eta_0, \eta_1$ are the periods of
$H'$ at $1$ and $a$. -/
theorem towerPoly_bot_coeff_conjugate {ζ : R} (hζ : ζ ^ p = 1) (H' : Subgroup (ZMod p)ˣ)
    (a : (ZMod p)ˣ) (hcov : ∀ u : (ZMod p)ˣ, u ∈ H' ∨ ∃ h ∈ H', u = a * h) (ha2 : a * a ∈ H') :
    ∃ A B C : ℕ → ℤ, ∀ i,
      (towerPoly ζ ⊥ H' 1).coeff i
          = A i • (1 : R) + B i • periodSum ζ H' 1 + C i • periodSum ζ H' (a : ZMod p) ∧
      (towerPoly ζ ⊥ H' (a : ZMod p)).coeff i
          = A i • (1 : R) + B i • periodSum ζ H' (a : ZMod p) + C i • periodSum ζ H' 1 := by
  have hfix : ∀ i, (towerPoly (genericRoot p) ⊥ H' 1).coeff i ∈ periodSpan (genericRoot p) H' := by
    intro i
    refine mem_periodSpan_of_fixed H' _ fun m => ?_
    have := congrArg (fun P => P.coeff i) (towerPoly_map_multiplier ⊥ H' 1 m)
    simpa [Polynomial.coeff_map] using this
  have hab := fun i => exists_abc (ζ := genericRoot p) hcov (hfix i)
  choose A B C hABC using hab
  refine ⟨A, B, C, fun i => ⟨?_, ?_⟩⟩
  · rw [towerPoly_eval hζ, Polynomial.coeff_map, hABC i]
    simp [map_add, evalRoot_periodSum]
  · have hm : multiplier (a : ZMod p) (periodSum (genericRoot p) H' (a : ZMod p))
        = periodSum (genericRoot p) H' 1 := by
      rw [multiplier_periodSum]
      have := periodSum_mul_of_mem (genericRoot p) H' 1 ha2
      rw [one_mul] at this
      rw [← this]
      simp [Units.val_mul]
    have hm' : multiplier (a : ZMod p) (periodSum (genericRoot p) H' 1)
        = periodSum (genericRoot p) H' (a : ZMod p) := by
      rw [multiplier_periodSum, mul_one]
    rw [towerPoly_eval hζ, ← mul_one (a : ZMod p), ← towerPoly_map_multiplier_shift,
      Polynomial.coeff_map, Polynomial.coeff_map, hABC i]
    simp [hm, hm', evalRoot_periodSum]

end Generic

section Main

variable {K : Type*} [Field K] [CharZero K] {p : ℕ} [Fact p.Prime]

/-- The product of $X - \zeta^u$ over all units $u$ is $\Phi_p$. -/
theorem prod_units_eq_cyclotomic {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    ∏ u : (ZMod p)ˣ, (X - C (rootPow ζ (u : ZMod p))) = cyclotomic p K := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ]
  refine Finset.prod_bij (fun u _ => rootPow ζ (u : ZMod p)) ?_ ?_ ?_ ?_
  · intro u _
    rw [mem_primitiveRoots hp, rootPow, hζ.pow_iff_coprime hp]
    exact ZMod.val_coe_unit_coprime u
  · intro u _ v _ h
    exact Units.ext (ZMod.val_injective p
      (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))
  · intro μ hμ
    rw [mem_primitiveRoots hp] at hμ
    obtain ⟨k, hk, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    have hcop : Nat.Coprime k p := (hζ.pow_iff_coprime hp k).mp hμ
    refine ⟨ZMod.unitOfCoprime k hcop, Finset.mem_univ _, ?_⟩
    simp [rootPow, ZMod.val_cast_of_lt hk]
  · intro u _
    rfl

variable (K) in
/-- The quadratic character of $\mathbb{Z}/p$ with values in $K$. -/
noncomputable def quadraticCharK (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) K :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom K)

theorem quadraticCharK_of_isSquare {u : (ZMod p)ˣ} (hu : IsSquare u) :
    quadraticCharK K p (u : ZMod p) = 1 := by
  have := (quadraticChar_one_iff_isSquare u.ne_zero).mpr ((isSquare_val_iff u).mpr hu)
  simp [quadraticCharK, this]

theorem quadraticCharK_of_not_isSquare {u : (ZMod p)ˣ} (hu : ¬ IsSquare u) :
    quadraticCharK K p (u : ZMod p) = -1 := by
  have := quadraticChar_neg_one_iff_not_isSquare.mpr (fun h => hu ((isSquare_val_iff u).mp h))
  simp [quadraticCharK, this]

/-- **The quadratic Gauss sum** in terms of periods (Art. 356): with $a$ a nonresidue,
$\sum_x \left(\tfrac{x}{p}\right) \zeta^x = \eta_0 - \eta_1$, where $\eta_0, \eta_1$ are the periods of the
subgroup of squares at $1$ and at $a$. -/
theorem gaussSum_quadratic_eq {ζ : K} (hζ : ζ ^ p = 1) {a : (ZMod p)ˣ} (ha : ¬ IsSquare a) :
    gaussSum (quadraticCharK K p) (AddChar.zmodChar p hζ)
      = periodSum ζ (squaresSubgroup p) 1 - periodSum ζ (squaresSubgroup p) (a : ZMod p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  unfold gaussSum
  have h0 := sum_zmod_eq (p := p)
    (fun x : ZMod p => quadraticCharK K p x * AddChar.zmodChar p hζ x)
  have hsplit := sum_units_split (p := p)
    (fun u : (ZMod p)ˣ => quadraticCharK K p (u : ZMod p) * AddChar.zmodChar p hζ (u : ZMod p)) ha
  have e1 : ∑ h : squaresSubgroup p, quadraticCharK K p (((h : (ZMod p)ˣ)) : ZMod p)
        * AddChar.zmodChar p hζ (((h : (ZMod p)ˣ)) : ZMod p)
      = periodSum ζ (squaresSubgroup p) 1 := by
    unfold periodSum
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [quadraticCharK_of_isSquare (mem_squaresSubgroup.mp h.2), one_mul, one_mul]
    rfl
  have e2 : ∑ h : squaresSubgroup p, quadraticCharK K p (((a * (h : (ZMod p)ˣ) : (ZMod p)ˣ)) : ZMod p)
        * AddChar.zmodChar p hζ (((a * (h : (ZMod p)ˣ) : (ZMod p)ˣ)) : ZMod p)
      = - periodSum ζ (squaresSubgroup p) (a : ZMod p) := by
    unfold periodSum
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [quadraticCharK_of_not_isSquare (fun hs => mul_not_mem_squares ha h.2
      (mem_squaresSubgroup.mpr hs)), Units.val_mul]
    rw [neg_one_mul]
    rfl
  rw [h0, hsplit, e1, e2, MulChar.map_zero]
  simp [sub_eq_add_neg]

/-- The two periods of the subgroup of squares sum to $-1$. -/
theorem periodSum_squares_add {ζ : K} (hζ : IsPrimitiveRoot ζ p) {a : (ZMod p)ˣ}
    (ha : ¬ IsSquare a) :
    periodSum ζ (squaresSubgroup p) 1 + periodSum ζ (squaresSubgroup p) (a : ZMod p) = -1 := by
  have h := sum_units_rootPow_eq_neg_one hζ
  rw [sum_units_split (fun u : (ZMod p)ˣ => rootPow ζ (u : ZMod p)) ha] at h
  have e1 : ∑ h : squaresSubgroup p, rootPow ζ (((h : (ZMod p)ˣ)) : ZMod p)
      = periodSum ζ (squaresSubgroup p) 1 := by
    unfold periodSum; simp
  have e2 : ∑ h : squaresSubgroup p, rootPow ζ (((a * (h : (ZMod p)ˣ) : (ZMod p)ˣ)) : ZMod p)
      = periodSum ζ (squaresSubgroup p) (a : ZMod p) := by
    unfold periodSum; simp [Units.val_mul]
  rw [e1, e2] at h
  exact h

/-- **The quadratic Gauss sum squared** (Art. 356, with Mathlib's `gaussSum_sq`):
$(\eta_0 - \eta_1)^2 = (-1)^{(p-1)/2} p = p^*$ for $p$ an odd prime. -/
theorem periodSum_squares_sub_sq (hp : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p) {a : (ZMod p)ˣ}
    (ha : ¬ IsSquare a) :
    (periodSum ζ (squaresSubgroup p) 1 - periodSum ζ (squaresSubgroup p) (a : ZMod p)) ^ 2
      = (((-1) ^ ((p - 1) / 2) * p : ℤ) : K) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hc : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hodd : p % 2 = 1 := (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp
  have hψ : (AddChar.zmodChar p hζ.pow_eq_one).IsPrimitive :=
    AddChar.zmodChar_primitive_of_primitive_root p hζ
  have hχ1 : quadraticCharK K p ≠ 1 := by
    intro h
    have h' := congrArg (fun χ : MulChar (ZMod p) K => χ (a : ZMod p)) h
    simp only [MulChar.one_apply_coe, quadraticCharK_of_not_isSquare ha] at h'
    exact absurd h' (by norm_num)
  have hquad : (quadraticCharK K p).IsQuadratic :=
    MulChar.IsQuadratic.comp (quadraticChar_isQuadratic (ZMod p)) _
  have h := gaussSum_sq hχ1 hquad hψ
  rw [gaussSum_quadratic_eq hζ.pow_eq_one ha] at h
  rw [h]
  have h1 : quadraticChar (ZMod p) (-1) = (-1) ^ (p / 2) := by
    rw [quadraticChar_neg_one hc, ZMod.card, ZMod.χ₄_eq_neg_one_pow hodd]
  have hdiv : p / 2 = (p - 1) / 2 := by omega
  simp [quadraticCharK, h1, hdiv, ZMod.card]

/-- **Gauss's decomposition of the cyclotomic polynomial** (*Disq. Arith.* Art. 357,
promised in Art. 124). Let $p$ be an odd prime and $\zeta$ a primitive $p$-th root of unity in a field $K$ of
characteristic zero. Let $z = \prod_{a \text{ residue}} (X - \zeta^a)$ and $z' = \prod_{a \text{ nonresidue}}
(X - \zeta^a)$ (the products over the units $a$ of $\mathbb{Z}/p$ that are, respectively are not, squares).
Then there are integer polynomials $Y, Z \in \mathbb{Z}[X]$ and $s \in K$ with $s^2 = p^* = (-1)^{(p-1)/2} p$,
$2z = Y + s Z$, $2z' = Y - s Z$ (in $K[X]$, $Y, Z$ mapped to $K[X]$), and
$4\Phi_p = Y^2 - p^* Z^2$ in $\mathbb{Z}[X]$ (so $4 \Phi_p = Y^2 \mp p Z^2$, upper sign for $p \equiv 1 \bmod 4$).
Unconditional. Not included (differs from the historical sources statement): the leading terms $Y = 2X^m + X^{m-1} + \dots$,
$Z = X^{m-1} + \dots$ with $m = (p-1)/2$; here $s = \eta_0 - \eta_1$ is the quadratic Gauss sum. -/
@[kb "gauss1801" "Art. 357"]
theorem gauss_cyclotomic_decomposition (hp : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    ∃ (Y Z : ℤ[X]) (s : K),
      s ^ 2 = (((-1) ^ ((p - 1) / 2) * p : ℤ) : K) ∧
      2 * (∏ u ∈ Finset.univ.filter (fun u : (ZMod p)ˣ => IsSquare u),
            (X - C (ζ ^ (u : ZMod p).val)))
        = Y.map (Int.castRingHom K) + C s * Z.map (Int.castRingHom K) ∧
      2 * (∏ u ∈ Finset.univ.filter (fun u : (ZMod p)ˣ => ¬ IsSquare u),
            (X - C (ζ ^ (u : ZMod p).val)))
        = Y.map (Int.castRingHom K) - C s * Z.map (Int.castRingHom K) ∧
      4 * cyclotomic p ℤ = Y ^ 2 - C (((-1) ^ ((p - 1) / 2) * p : ℤ)) * Z ^ 2 := by
  obtain ⟨a, ha⟩ := exists_nonsquare_unit hp
  have hζ1 := hζ.pow_eq_one
  have hcov := squares_cover ha
  have ha2 : a * a ∈ squaresSubgroup p := mem_squaresSubgroup.mpr ⟨a, rfl⟩
  obtain ⟨A, B, D, hABD⟩ := towerPoly_bot_coeff_conjugate hζ1 (squaresSubgroup p) a hcov ha2
  have hsum := periodSum_squares_add hζ ha
  have hs := periodSum_squares_sub_sq hp hζ ha
  set η0 := periodSum ζ (squaresSubgroup p) 1 with hη0
  set η1 := periodSum ζ (squaresSubgroup p) (a : ZMod p) with hη1
  have hz : ∏ u ∈ Finset.univ.filter (fun u : (ZMod p)ˣ => IsSquare u),
      (X - C (ζ ^ (u : ZMod p).val)) = towerPoly ζ ⊥ (squaresSubgroup p) 1 := by
    rw [prod_filter_isSquare (fun u : (ZMod p)ˣ => (X - C (ζ ^ (u : ZMod p).val))),
      towerPoly_bot_eq_prod]
    refine Finset.prod_congr rfl fun h _ => ?_
    simp [rootPow]
  have hz' : ∏ u ∈ Finset.univ.filter (fun u : (ZMod p)ˣ => ¬ IsSquare u),
      (X - C (ζ ^ (u : ZMod p).val)) = towerPoly ζ ⊥ (squaresSubgroup p) (a : ZMod p) := by
    rw [prod_filter_not_isSquare (fun u : (ZMod p)ˣ => (X - C (ζ ^ (u : ZMod p).val))) ha,
      towerPoly_bot_eq_prod]
    refine Finset.prod_congr rfl fun h _ => ?_
    simp [rootPow, Units.val_mul]
  have hzz : towerPoly ζ ⊥ (squaresSubgroup p) 1 * towerPoly ζ ⊥ (squaresSubgroup p) (a : ZMod p)
      = cyclotomic p K := by
    have := prod_units_split (p := p) (fun u : (ZMod p)ˣ => X - C (rootPow ζ (u : ZMod p))) ha
    rw [prod_units_eq_cyclotomic hζ] at this
    rw [this, towerPoly_bot_eq_prod, towerPoly_bot_eq_prod]
    congr 1
    refine Finset.prod_congr rfl fun h _ => ?_
    simp
  set N := Nat.card (squaresSubgroup p ⧸ (⊥ : Subgroup (ZMod p)ˣ).subgroupOf (squaresSubgroup p))
    with hN
  have hdeg0 : (towerPoly ζ ⊥ (squaresSubgroup p) 1).natDegree = N := towerPoly_natDegree _ _ _ _
  have hdeg1 : (towerPoly ζ ⊥ (squaresSubgroup p) (a : ZMod p)).natDegree = N :=
    towerPoly_natDegree _ _ _ _
  let f : ℤ →+* K := Int.castRingHom K
  let Y : ℤ[X] := ∑ i ∈ Finset.range (N + 1), monomial i (2 * A i - B i - D i)
  let Z : ℤ[X] := ∑ i ∈ Finset.range (N + 1), monomial i (B i - D i)
  have hmapY : Y.map f = ∑ i ∈ Finset.range (N + 1), monomial i (((2 * A i - B i - D i : ℤ)) : K) := by
    simp only [Y, Polynomial.map_sum, Polynomial.map_monomial]
    rfl
  have hmapZ : Z.map f = ∑ i ∈ Finset.range (N + 1), monomial i (((B i - D i : ℤ)) : K) := by
    simp only [Z, Polynomial.map_sum, Polynomial.map_monomial]
    rfl
  have two : (2 : K[X]) = C 2 := (map_ofNat C 2).symm
  have term : ∀ (c y w : K) (i : ℕ), 2 * c = y + (η0 - η1) * w →
      2 * monomial i c = monomial i y + C (η0 - η1) * monomial i w := by
    intro c y w i h
    rw [two, C_mul_monomial, C_mul_monomial, ← map_add, h]
  have term' : ∀ (c y w : K) (i : ℕ), 2 * c = y - (η0 - η1) * w →
      2 * monomial i c = monomial i y - C (η0 - η1) * monomial i w := by
    intro c y w i h
    rw [two, C_mul_monomial, C_mul_monomial, ← map_sub, h]
  have e0 : 2 * towerPoly ζ ⊥ (squaresSubgroup p) 1
      = Y.map f + C (η0 - η1) * Z.map f := by
    conv_lhs => rw [as_sum_range' (towerPoly ζ ⊥ (squaresSubgroup p) 1) (N + 1) (by omega)]
    rw [hmapY, hmapZ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => term _ _ _ i ?_
    rw [(hABD i).1]
    simp only [zsmul_eq_mul, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, mul_one]
    linear_combination ((B i : K) + (D i : K)) * hsum
  have e1 : 2 * towerPoly ζ ⊥ (squaresSubgroup p) (a : ZMod p)
      = Y.map f - C (η0 - η1) * Z.map f := by
    conv_lhs => rw [as_sum_range' (towerPoly ζ ⊥ (squaresSubgroup p) (a : ZMod p)) (N + 1)
      (by omega)]
    rw [hmapY, hmapZ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => term' _ _ _ i ?_
    rw [(hABD i).2]
    simp only [zsmul_eq_mul, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, mul_one]
    linear_combination ((B i : K) + (D i : K)) * hsum
  refine ⟨Y, Z, η0 - η1, hs, ?_, ?_, ?_⟩
  · rw [hz, e0]
  · rw [hz', e1]
  · apply Polynomial.map_injective f (RingHom.injective_int _)
    have h4 : (4 : K[X]) * cyclotomic p K
        = (2 * towerPoly ζ ⊥ (squaresSubgroup p) 1)
          * (2 * towerPoly ζ ⊥ (squaresSubgroup p) (a : ZMod p)) := by
      rw [← hzz]; ring
    have hC : (C (((-1) ^ ((p - 1) / 2) * p : ℤ)) : ℤ[X]).map f = C (η0 - η1) ^ 2 := by
      rw [Polynomial.map_C, eq_intCast, ← hs, C_pow]
    have h4' : ((4 : ℤ[X]) * cyclotomic p ℤ).map f = 4 * cyclotomic p K := by
      rw [Polynomial.map_mul, map_cyclotomic]
      norm_num
    rw [h4', h4, e0, e1, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_pow, hC]
    ring

/-- **The integral identity $4\Phi_p = Y^2 - p^* Z^2$** (*Disq. Arith.* Art. 357):
for every odd prime $p$ there are $Y, Z \in \mathbb{Z}[X]$ with $4\Phi_p = Y^2 - (-1)^{(p-1)/2} p Z^2$, where
$\Phi_p = $ `cyclotomic p ℤ`. This is `gauss_cyclotomic_decomposition` over $\mathbb{C}$, with the field
forgotten. Unconditional. -/
@[kb "gauss1801" "Art. 357"]
theorem gauss_four_cyclotomic (hp : p ≠ 2) :
    ∃ Y Z : ℤ[X], 4 * cyclotomic p ℤ = Y ^ 2 - C (((-1) ^ ((p - 1) / 2) * p : ℤ)) * Z ^ 2 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨Y, Z, _, -, -, -, h⟩ := gauss_cyclotomic_decomposition (K := ℂ) hp
    (Complex.isPrimitiveRoot_exp p (NeZero.ne p))
  exact ⟨Y, Z, h⟩

end Main

/-! ### Concrete checks -/

/-- $p = 5$: $4\Phi_5 = (2X^2 + X + 2)^2 - 5X^2$. -/
theorem four_cyclotomic_five :
    4 * cyclotomic 5 ℤ = (2 * X ^ 2 + X + 2 : ℤ[X]) ^ 2 - 5 * X ^ 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [cyclotomic_prime ℤ 5]
  simp [Finset.sum_range_succ]
  ring

/-- $p = 7$: $4\Phi_7 = (2X^3 + X^2 - X - 2)^2 + 7(X^2 + X)^2$. -/
theorem four_cyclotomic_seven :
    4 * cyclotomic 7 ℤ = (2 * X ^ 3 + X ^ 2 - X - 2 : ℤ[X]) ^ 2 + 7 * (X ^ 2 + X) ^ 2 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [cyclotomic_prime ℤ 7]
  simp [Finset.sum_range_succ]
  ring

end QuadFormsKB.Historical.Gauss
