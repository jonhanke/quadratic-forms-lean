/-
# Cassels, Chapter 9, §8: representation by individual forms (Theorem 8.1)

**Layer:** integer-valued forms `f : QuadForm ℤ n` with $\det H \ne 0$; representations over $\mathbb Z_p$ = `ℤ_[p]`
and over $\mathbb R$.

**Proves** Theorem 8.1 (`exists_sq_mul_represents`): for every $M > 1$ there is $m$ prime to $M$ such that $am^2$ is
represented by $f$ over $\mathbb Z$ whenever $a$ is represented by $f$ over every $\mathbb Z_p$ and over $\mathbb R$.

*Proof (Cassels'):* let $f_1, \dots, f_h$ represent the classes of the genus (finitely many, `genusClasses_finite`); by
Theorem 1.4 (`sameGenus_iff_semiEquiv`) each $f_j$ is equivalent to $f$ over $\mathbb Z^{(P)}$, $P$ the primes dividing
$M$, so $m_j^2 f_j(\mathbf x) = f(T_j\mathbf x)$ with $T_j$ integral and $m_j$ prime to $M$ (8.1); put $m = \prod m_j$
(8.2). By Theorem 1.3 (`exists_sameGenus_represents`) $a = f_j(\mathbf b)$ for some $j$ and $\mathbf b \in \mathbb Z^n$
(8.3), so $m^2a = f((m/m_j)T_j\mathbf b)$ (8.4).
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec4
import QuadFormsKB.Literature.Cassels.Ch9Sec5
import QuadFormsKB.Literature.Cassels.Ch9Sec7

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

variable {n : ℕ}

/-- If `p` divides the denominator of `c` then `c` is not a `p`-adic integer. -/
theorem one_lt_norm_of_dvd_den (p : ℕ) [Fact p.Prime] (c : ℚ) (h : p ∣ c.den) :
    1 < ‖(c : ℚ_[p])‖ := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hc : c ≠ 0 := by
    rintro rfl
    simp at h
    exact absurd h (by have := (Fact.out : p.Prime).one_lt; omega)
  have hnum : ¬ (p : ℤ) ∣ c.num := by
    intro hd
    have h1 : p ∣ c.num.natAbs := Int.natCast_dvd.mp hd
    have := Nat.eq_one_of_dvd_coprimes (c.reduced) h1 h
    omega
  have hv : padicValRat p c < 0 := by
    rw [padicValRat, padicValInt.eq_zero_of_not_dvd hnum]
    have := one_le_padicValNat_of_dvd (p := p) c.den_nz h
    omega
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hc]
  have h2 : (1 : ℝ) < ((p : ℝ)) ^ (-padicValRat p c) :=
    one_lt_zpow₀ (by exact_mod_cast hp) (by omega)
  push_cast
  exact h2

/-- If `c` is a `p`-adic integer for every prime `p ∣ M` then its denominator is prime to `M`. -/
theorem isCoprime_den_of_norm_le_one {M : ℤ} (c : ℚ)
    (h : ∀ (p : ℕ) [Fact p.Prime], (p : ℤ) ∣ M → ‖(c : ℚ_[p])‖ ≤ 1) : IsCoprime (c.den : ℤ) M := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  change Nat.Coprime (c.den : ℤ).natAbs M.natAbs
  rw [Int.natAbs_natCast]
  refine (Nat.coprime_of_dvd fun p hp hpd hpM => ?_)
  have := Fact.mk hp
  have := h p (Int.natCast_dvd.mpr hpM)
  have := one_lt_norm_of_dvd_den p c hpd
  linarith

/-- Homogeneity over any commutative ring: `Q(k x) = k² Q(x)`. -/
theorem evalIn_const_smul (K : Type*) [CommRing K] (Q : QuadForm ℤ n) (k : K) (x : Fin n → K) :
    Q.evalIn K (k • x) = k ^ 2 * Q.evalIn K x := by
  simp only [QuadForm.evalIn_eq_dotProduct]
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_smul, smul_eq_mul]
  ring

/-- Homogeneity: `Q(k x) = k² Q(x)` for integer vectors. -/
theorem eval_const_smul (Q : QuadForm ℤ n) (k : ℤ) (x : Fin n → ℤ) :
    Q.eval (k • x) = k ^ 2 * Q.eval x :=
  evalIn_const_smul ℤ Q k x

/-- The rational value at an integer vector is the integer value. -/
theorem evalIn_rat_intCast (Q : QuadForm ℤ n) (z : Fin n → ℤ) :
    Q.evalIn ℚ (fun i => (z i : ℚ)) = (Q.eval z : ℚ) := by
  simp [QuadForm.evalIn, apply_ite]

/-- The rational form of an integral form evaluates as the integral form. -/
theorem evalIn_map_rat_self (Q : QuadForm ℤ n) (x : Fin n → ℚ) :
    (Q.map (Int.castRingHom ℚ)).evalIn ℚ x = Q.evalIn ℚ x := by
  simp [QuadForm.map, QuadForm.evalIn]

/-- Semi-equivalence yields an integral matrix `T` and `m` prime to `M` with `f(T y) = m² g(y)`. -/
theorem exists_integral_of_semiEquiv (f g : QuadForm ℤ n) {M : ℤ} (hM : M ≠ 0) (h : SemiEquiv g f) :
    ∃ m : ℤ, IsCoprime m M ∧ ∃ T : Matrix (Fin n) (Fin n) ℤ, ∀ y, f.eval (T *ᵥ y) = m ^ 2 * g.eval y := by
  obtain ⟨S, hS⟩ := h ((M.natAbs.primeFactors).subtype Nat.Prime)
  set c : Fin n → Fin n → ℚ := fun i j => ((S.val i j : intAway _) : ℚ) with hcdef
  have hc : ∀ i j, IsCoprime ((c i j).den : ℤ) M := fun i j =>
    isCoprime_den_of_norm_le_one _ (fun p _ hpM => (S.val i j).2 ⟨p, Fact.out⟩
      (Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr
        ⟨Fact.out, Int.natCast_dvd.mp hpM, Int.natAbs_ne_zero.mpr hM⟩)))
  set m : ℤ := ∏ i, ∏ j, ((c i j).den : ℤ) with hm
  refine ⟨m, IsCoprime.prod_left fun i _ => IsCoprime.prod_left fun j _ => hc i j, ?_⟩
  have hdvd : ∀ i j, ((c i j).den : ℤ) ∣ m := fun i j =>
    (Finset.dvd_prod_of_mem (fun j => ((c i j).den : ℤ)) (Finset.mem_univ j)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ j, ((c i j).den : ℤ)) (Finset.mem_univ i))
  choose q hq using hdvd
  have hT : ∀ i j, ((q i j * (c i j).num : ℤ) : ℚ) = m * c i j := by
    intro i j
    have h1 : c i j * ((c i j).den : ℚ) = ((c i j).num : ℚ) := Rat.mul_den_eq_num _
    have hm' : (m : ℚ) = ((c i j).den : ℚ) * q i j := by exact_mod_cast hq i j
    push_cast
    rw [← h1, hm']
    ring
  refine ⟨Matrix.of fun i j => q i j * (c i j).num, fun y => ?_⟩
  apply Int.cast_injective (α := ℚ)
  have e3 : (fun i => ((((Matrix.of fun i j => q i j * (c i j).num) *ᵥ y) i : ℤ) : ℚ)) =
      (m : ℚ) • ((S.val.map (intAway _).subtype) *ᵥ (fun i => (y i : ℚ))) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, Matrix.map_apply,
      smul_eq_mul, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    have := hT i j
    push_cast at this
    rw [this]
    simp [hcdef]
    ring
  rw [← evalIn_rat_intCast, e3, evalIn_const_smul]
  have := hS (fun i => (y i : ℚ))
  rw [evalIn_map_rat_self, evalIn_map_rat_self, evalIn_rat_intCast] at this
  rw [this]
  push_cast
  rfl

/-- **Cassels, Theorem 8.1** (Ch. 9, p. 157): *let $f$ be a regular integral form and let $M > 1$ be any integer. Then
there is an integer $m$ prime to $M$ with the following property: let $a \in \mathbb Z$ and suppose that $a$ is
represented by $f$ over every $\mathbb Z_p$ (including $p = \infty$). Then $am^2$ is represented by $f$ over
$\mathbb Z$.* ($f$ integer-valued.) -/
@[kb "cassels1978" "Ch. 9, Thm. 8.1, p. 157"]
theorem exists_sq_mul_represents (f : QuadForm ℤ n) (hf : f.hessian.det ≠ 0) {M : ℤ} (hM : 1 < M) :
    ∃ m : ℤ, IsCoprime m M ∧ ∀ a : ℤ, (∃ x : Fin n → ℝ, f.evalIn ℝ x = a) →
      (∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin n → ℤ_[p], (f.map (Int.castRingHom ℤ_[p])).eval x = a) →
      ∃ x : Fin n → ℤ, f.eval x = a * m ^ 2 := by
  classical
  have hM0 : M ≠ 0 := by omega
  have hfin := genusClasses_finite hf
  have key : ∀ c ∈ genusClasses f, ∃ m : ℤ, IsCoprime m M ∧ ∃ T : Matrix (Fin n) (Fin n) ℤ,
      ∀ y, f.eval (T *ᵥ y) = m ^ 2 * c.out.eval y := by
    intro c hc
    have hc' : classOf c.out ∈ genusClasses f := by
      have : classOf c.out = c := Quotient.out_eq c
      rwa [this]
    have hg := classOf_mem_genusClasses_iff.mp hc'
    exact exists_integral_of_semiEquiv f c.out hM0
      ((sameGenus_iff_semiEquiv _ _ (hg.hessian_det_eq ▸ hf)).mp hg.symm)
  obtain ⟨m, hmc, T, hT⟩ : ∃ (m : QClass n → ℤ) (hm : ∀ c ∈ genusClasses f, IsCoprime (m c) M)
      (T : QClass n → Matrix (Fin n) (Fin n) ℤ),
      ∀ c ∈ genusClasses f, ∀ y, f.eval (T c *ᵥ y) = m c ^ 2 * c.out.eval y := by
    choose! m hm T hT using key
    exact ⟨m, hm, T, hT⟩
  let F := hfin.toFinset
  refine ⟨∏ c ∈ F, m c, IsCoprime.prod_left fun c hc => hmc c (hfin.mem_toFinset.mp hc), ?_⟩
  intro a hreal hloc
  by_cases ha : a = 0
  · exact ⟨0, by simp [ha, QuadForm.evalIn]⟩
  obtain ⟨f', hg, x, hx⟩ := exists_sameGenus_represents f hf ha hreal hloc
  have hcm : classOf f' ∈ genusClasses f := classOf_mem_genusClasses_iff.mpr hg
  set c := classOf f' with hcdef
  have hcF : c ∈ F := hfin.mem_toFinset.mpr hcm
  have hout : IntEquiv c.out f' := by
    have : classOf c.out = classOf f' := Quotient.out_eq c
    exact classOf_eq_classOf_iff.mp this
  obtain ⟨g, hgx⟩ := hout
  refine ⟨(∏ d ∈ F.erase c, m d) • (T c *ᵥ (g.val *ᵥ x)), ?_⟩
  rw [eval_const_smul, hT c hcm, hgx, hx, ← Finset.mul_prod_erase F m hcF]
  ring

end QuadFormsKB.Siegel
