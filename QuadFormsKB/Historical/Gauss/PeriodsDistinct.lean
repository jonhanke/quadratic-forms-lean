import QuadFormsKB.Historical.Gauss.Periods
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.PowerBasis

/-!
# Distinct Gaussian periods (Disquisitiones Arithmeticae, Art. 346)

the historical sources (*Disq. Arith.* Art. 346). Proved here, unconditionally: for a prime $p$, a primitive
$p$-th root of unity $\zeta$ in a field $K$ of characteristic zero, and a subgroup $H$ of $(\mathbb{Z}/p)^\times$,
the periods of distinct cosets of $H$ are distinct (`periodSum_eq_iff`, `cosetPeriod_injective`,
`card_range_cosetPeriod`: there are exactly $e = [(\mathbb{Z}/p)^\times : H]$ distinct periods).
The route is Gauss's: the cyclotomic polynomial is irreducible over $\mathbb{Q}$ (`linearIndependent_rootPow`).

Not proved here (remains part of a recorded loose end): the other claims of namely that each period
is a rational polynomial of degree at most $e - 1$ in any other, that it generates the degree-$e$ subfield
(the fixed field of $H$), and the irreducible integer polynomial of degree $e$.
-/

namespace QuadFormsKB.Historical.Gauss

open scoped Classical

section PeriodsDistinct

variable {K : Type*} [Field K] [CharZero K] {p : ℕ} [Fact p.Prime]

/-- **The roots $\zeta^1, \dots, \zeta^{p-1}$ are linearly independent over $\mathbb{Q}$** (the input of
the historical sources, *Disq. Arith.* Art. 346): for $\zeta$ a primitive $p$-th root of unity in a field of
characteristic zero, the family $u \mapsto \zeta^{u}$ indexed by the units $u$ modulo $p$ is $\mathbb{Q}$-linearly
independent. They are $\zeta$ times the power basis $1, \zeta, \dots, \zeta^{p-2}$, since the minimal polynomial of
$\zeta$ is the cyclotomic polynomial, irreducible of degree $p - 1$. -/
theorem linearIndependent_rootPow {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    LinearIndependent ℚ (fun w : (ZMod p)ˣ => ζ ^ (w : ZMod p).val) := by
  have hp : p.Prime := Fact.out
  have hdeg : (minpoly ℚ ζ).natDegree = p - 1 := by
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ hp.pos, Polynomial.natDegree_cyclotomic,
      Nat.totient_prime hp]
  have hli := linearIndependent_pow (K := ℚ) ζ
  have hval : ∀ w : (ZMod p)ˣ, 1 ≤ (w : ZMod p).val :=
    fun w => Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).2 w.ne_zero)
  let e : (ZMod p)ˣ → Fin (minpoly ℚ ζ).natDegree := fun w =>
    ⟨(w : ZMod p).val - 1, by
      have := ZMod.val_lt (w : ZMod p)
      have := hval w
      omega⟩
  have he : Function.Injective e := by
    intro a b h
    have h1 := congrArg Fin.val h
    simp only [e] at h1
    have := hval a
    have := hval b
    exact Units.ext (ZMod.val_injective p (by omega))
  rw [Fintype.linearIndependent_iff]
  intro g hg w
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hsum : ∑ i, g i • ζ ^ ((e i : Fin _) : ℕ) = 0 := by
    apply mul_left_cancel₀ hζ0
    rw [mul_zero, Finset.mul_sum, ← hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def]
    have : ζ ^ (i : ZMod p).val = ζ * ζ ^ ((i : ZMod p).val - 1) := by
      rw [← pow_succ']
      congr 1
      have := hval i
      omega
    rw [this]
    show ζ * (algebraMap ℚ K (g i) * ζ ^ ((i : ZMod p).val - 1)) = _
    ring
  exact Fintype.linearIndependent_iff.1 (hli.comp e he) g hsum w

private theorem finset_eq_of_sum_eq {ι : Type*} [Fintype ι] {f : ι → K}
    (hf : LinearIndependent ℚ f) {S T : Finset ι} (h : ∑ w ∈ S, f w = ∑ w ∈ T, f w) : S = T := by
  have key := Fintype.linearIndependent_iff.1 hf
    (fun w => (if w ∈ S then (1 : ℚ) else 0) - if w ∈ T then 1 else 0) (by
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_mem, Finset.univ_inter]
      rw [h, sub_self])
  ext w
  have := key w
  by_cases a : w ∈ S <;> by_cases b : w ∈ T <;> simp_all

/-- The exponents of the coset $u H$, as a finset of units. -/
private noncomputable def cosetUnits (H : Subgroup (ZMod p)ˣ) (u : (ZMod p)ˣ) : Finset (ZMod p)ˣ :=
  Finset.univ.image fun h : H => u * (h : (ZMod p)ˣ)

private theorem periodSum_eq_sum_cosetUnits (ζ : K) (H : Subgroup (ZMod p)ˣ) (u : (ZMod p)ˣ) :
    periodSum ζ H (u : ZMod p) = ∑ w ∈ cosetUnits H u, ζ ^ (w : ZMod p).val := by
  unfold periodSum cosetUnits
  rw [Finset.sum_image]
  · simp [rootPow, Units.val_mul]
  · intro a _ b _ h
    exact Subtype.ext (mul_left_cancel h)

/-- **Periods of distinct cosets are distinct** (*Disq. Arith.* Art. 346): for $p$ a
prime, $\zeta$ a primitive $p$-th root of unity in a field of characteristic zero, $H$ a subgroup of
$(\mathbb{Z}/p)^\times$ and $u, v$ units, $\eta_H(u) = \eta_H(v)$ if and only if $u^{-1} v \in H$, that is, $u$ and
$v$ lie in the same coset of $H$. Gauss's proof (irreducibility of $\Phi_p$: otherwise a polynomial of lower degree
would vanish at $\zeta$) is `linearIndependent_rootPow`; the difference of the two periods of distinct, hence
disjoint, cosets is a nonzero $\pm 1$ combination of $\zeta^1, \dots, \zeta^{p-1}$. Only this first claim of
is formalized (the fixed-field and degree-$e$ polynomial statements are not). -/
@[kb "gauss1801" "Art. 346"]
theorem periodSum_eq_iff {ζ : K} (hζ : IsPrimitiveRoot ζ p) (H : Subgroup (ZMod p)ˣ)
    (u v : (ZMod p)ˣ) :
    periodSum ζ H (u : ZMod p) = periodSum ζ H (v : ZMod p) ↔ u⁻¹ * v ∈ H := by
  constructor
  · intro h
    rw [periodSum_eq_sum_cosetUnits, periodSum_eq_sum_cosetUnits] at h
    have hS := finset_eq_of_sum_eq (linearIndependent_rootPow hζ) h
    have hv : v ∈ cosetUnits H v := Finset.mem_image.2 ⟨1, Finset.mem_univ _, by simp⟩
    rw [← hS] at hv
    obtain ⟨a, _, ha⟩ := Finset.mem_image.1 hv
    have : u⁻¹ * v = (a : (ZMod p)ˣ) := by rw [← ha]; simp
    rw [this]
    exact a.2
  · intro h
    have := periodSum_mul_of_mem ζ H (u : ZMod p) h
    rw [← this, ← Units.val_mul, mul_inv_cancel_left]

/-- **The period map on cosets is injective** (*Disq. Arith.* Art. 346): distinct cosets
of $H$ in $(\mathbb{Z}/p)^\times$ have distinct periods, for $\zeta$ a primitive $p$-th root of unity in a field
of characteristic zero. -/
@[kb "gauss1801" "Art. 346"]
theorem cosetPeriod_injective {ζ : K} (hζ : IsPrimitiveRoot ζ p) (H : Subgroup (ZMod p)ˣ) :
    Function.Injective (cosetPeriod ζ H) := by
  intro a b
  induction a using QuotientGroup.induction_on with
  | H u =>
    induction b using QuotientGroup.induction_on with
    | H v =>
      intro h
      rw [cosetPeriod_mk, cosetPeriod_mk, periodSum_eq_iff hζ] at h
      exact QuotientGroup.eq.mpr h

/-- **There are exactly $e$ distinct periods** (*Disq. Arith.* Art. 346): the set of
values of the periods of $H$ has $e = [(\mathbb{Z}/p)^\times : H]$ elements. -/
@[kb "gauss1801" "Art. 346"]
theorem card_range_cosetPeriod {ζ : K} (hζ : IsPrimitiveRoot ζ p) (H : Subgroup (ZMod p)ˣ) :
    Nat.card (Set.range (cosetPeriod ζ H)) = H.index :=
  (Nat.card_congr (Equiv.ofInjective _ (cosetPeriod_injective hζ H))).symm

end PeriodsDistinct

end QuadFormsKB.Historical.Gauss
