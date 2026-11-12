/-
# Shimura 2004, Theorem 11.1 (i): the totally definite case

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Theorem 11.1 (i), printed
p. 101.

**Setting.** $F$ is a number field, $V = F^n$ with `Q : QuadForm F n` totally positive definite
(`Lattices.IsTotallyPosDef`: $\sigma(\varphi[x]) > 0$ for every embedding $\sigma$ and $x \ne 0$; then $F$ is totally
real when $n > 0$), and $\Lambda$ any $\mathcal O_F$-lattice in $V$ (`Lat F n`), not necessarily integral.

**Proves** (unconditional; standard axioms only)
* `finite_solutions_of_totallyPosDef`: $\{x \in \Lambda \mid \varphi[x] = m\}$ is finite for every $m \in F$.
  *Proof:* choose $0 < k \in \mathbb Z$ with $k\varphi$ having coefficients in $\mathcal O_F$ and $0 \ne d \in
  \mathcal O_F$ with $d\Lambda \subseteq \mathcal O_F^n$ (`Lattices.exists_global_bounds`); then $x \mapsto dx$ embeds
  the set into $\{y \in \mathcal O_F^n \mid k\varphi[y] = kd^2m\}$, finite by the library's `Tamagawa.finite_repSet`
  ($k\varphi$ is integral on $\mathcal O_F^n$ and still totally positive definite).
* `theorem_11_1_i_definite`: **Theorem 11.1 (i)** in the totally definite case: the set
  $\{k \in \Lambda \mid \varphi[k] = \varphi[h]\}$ is a finite union of orbits $k_i\Gamma(\Lambda)$ (indeed finite).
  Shimura's theorem is for every nondegenerate $\varphi$; the indefinite case (infinitely many solutions, finitely
  many orbits) is not covered here (`Theorem11_1_i` in `Diophantine.lean` states the general case).
-/
import QuadFormsKB.Literature.Shimura2004.HGenus
import QuadFormsKB.Lattices.ClassFinite
import QuadFormsKB.Tamagawa.RepMass
import Mathlib.RingTheory.Algebraic.Integral
import QuadFormsKB.Citation

open NumberField Matrix
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- Every element of a number field has a positive integer multiple in $\mathcal O_F$. -/
theorem exists_nat_mul_mem_integers (z : F) : ∃ k : ℕ, 0 < k ∧ (k : F) * z ∈ (algebraMap (𝓞 F) F).range := by
  obtain ⟨y, hy0, hy⟩ := IsAlgebraic.exists_integral_multiple
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z))
  refine ⟨y.natAbs ^ 2, pow_pos (Int.natAbs_pos.2 hy0) 2, ?_⟩
  have hc : ((y.natAbs ^ 2 : ℕ) : F) = (y : F) * y := by
    have h1 := congrArg (fun t : ℤ => (t : F)) (Int.natAbs_sq y)
    simp only [Int.cast_pow, Int.cast_natCast] at h1
    rw [Nat.cast_pow, h1, sq]
  have hint : IsIntegral ℤ (((y.natAbs ^ 2 : ℕ) : F) * z) := by
    rw [hc, mul_assoc, ← zsmul_eq_mul]
    have h2 : IsIntegral ℤ (algebraMap ℤ F y) := isIntegral_algebraMap
    rw [algebraMap_int_eq, eq_intCast] at h2
    simpa [zsmul_eq_mul] using h2.mul hy
  exact ⟨⟨_, hint⟩, rfl⟩

/-- A positive integer $k$ with $k\,c_{ij} \in \mathcal O_F$ for all coefficients of $Q$. -/
theorem exists_nat_smul_coeff_integral (Q : QuadForm F n) :
    ∃ k : ℕ, 0 < k ∧ ∀ i j, (k : F) * Q.coeff i j ∈ (algebraMap (𝓞 F) F).range := by
  classical
  choose k hk0 hk using fun p : Fin n × Fin n => exists_nat_mul_mem_integers (Q.coeff p.1 p.2)
  refine ⟨∏ p, k p, Finset.prod_pos fun p _ => hk0 p, fun i j => ?_⟩
  have hsplit : (∏ p, k p : ℕ) = (∏ p ∈ Finset.univ.erase (i, j), k p) * k (i, j) :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm
  rw [hsplit, Nat.cast_mul, mul_assoc]
  exact (algebraMap (𝓞 F) F).range.mul_mem ⟨_, map_natCast _ _⟩ (hk (i, j))

/-- If all coefficients of $Q$ lie in $\mathcal O_F$, then $Q$ is integral on $\mathcal O_F^n$. -/
theorem isIntegral_intVec_of_coeff {Q : QuadForm F n} (hQ : ∀ i j, Q.coeff i j ∈ (algebraMap (𝓞 F) F).range) :
    IsIntegral Q (intVec : Submodule (𝓞 F) (Fin n → F)) := by
  intro x hx
  unfold QuadForm.evalIn
  refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
  split_ifs
  · simp only [Algebra.algebraMap_self, RingHom.id_apply]
    exact Subring.mul_mem _ (Subring.mul_mem _ (hQ i j) (hx i)) (hx j)
  · exact Subring.zero_mem _

/-- **Finiteness of the solutions** of $\varphi[x] = m$ in any lattice $\Lambda$ for a totally positive definite
form over a number field. -/
theorem finite_solutions_of_totallyPosDef {Q : QuadForm F n} (hQ : Lattices.IsTotallyPosDef Q) (Λ : Lat F n)
    (m : F) : {x : Fin n → F | x ∈ Λ.1 ∧ Q.eval x = m}.Finite := by
  obtain ⟨k, hk0, hk⟩ := exists_nat_smul_coeff_integral Q
  obtain ⟨d, hd0, -, hdΛ⟩ := exists_global_bounds Λ.2
  set Q' : QuadForm F n := (k : F) • Q with hQ'
  have hQ'int : IsIntegral Q' (intVec : Submodule (𝓞 F) (Fin n → F)) :=
    isIntegral_intVec_of_coeff fun i j => by
      simpa [hQ', QuadForm.smul_coeff] using hk i j
  have hQ'eval : ∀ x, Q'.eval x = (k : F) * Q.eval x := fun x => ClassFin.evalIn_smul_form Q (k : F) x
  have hQ'pd : Lattices.IsTotallyPosDef Q' := by
    intro x hx σ
    rw [hQ'eval, map_mul, map_natCast]
    exact mul_pos (Nat.cast_pos.mpr hk0) (hQ x hx σ)
  have hfin := finite_repSet hQ'pd (intVec_isLattice (F := F) (n := n)) hQ'int ((k : F) * ((d : F) ^ 2 * m))
  have hd0' : (d : F) ≠ 0 := by
    intro h; exact hd0 (by exact_mod_cast h)
  let f : {x : Fin n → F | x ∈ Λ.1 ∧ Q.eval x = m} →
      {v : Fin n → F // v ∈ (intVec : Submodule (𝓞 F) (Fin n → F)) ∧ Q'.eval v = (k : F) * ((d : F) ^ 2 * m)} :=
    fun x => ⟨d • x.1, hdΛ _ x.2.1, by
      rw [hQ'eval, show d • x.1 = (d : F) • x.1 from (algebraMap_smul F d x.1).symm, ClassFin.eval_smul,
        x.2.2]⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : d • x.1 = d • y.1 := congrArg Subtype.val hxy
    rw [← algebraMap_smul F d x.1, ← algebraMap_smul F d y.1] at h1
    exact Subtype.ext (smul_right_injective _ hd0' h1)
  have : Finite {x : Fin n → F | x ∈ Λ.1 ∧ Q.eval x = m} := Finite.of_injective f hf
  exact Set.toFinite _

/-- **Theorem 11.1 (i)**, totally definite case (Shimura 2004, p. 101): for a number field $F$, a totally positive
definite $\varphi$ on $V = F^n$, any $\mathcal O_F$-lattice $\Lambda$ and $h \in V$, the set
$\{x \in \Lambda \mid \varphi[x] = \varphi[h]\}$ is the union of finitely many orbits $k\,\Gamma(\Lambda)$,
$k \in \Lambda$ (with $\Gamma(\Lambda) = \{\gamma\in SO^\varphi(V) \mid \Lambda\gamma = \Lambda\}$, acting on the left
here). Shimura assumes $\varphi[h] \ne 0$ and $h \in \Lambda$; neither is needed in the definite case. -/
@[kb "shimura2004" "Thm. 11.1 (i), p. 101 (totally definite case)"]
theorem theorem_11_1_i_definite {Q : QuadForm F n} (hQ : Lattices.IsTotallyPosDef Q) (Λ : Lat F n)
    (h : Fin n → F) :
    ∃ ks : Finset (Fin n → F), (∀ k ∈ ks, k ∈ Λ.1) ∧
      {x | x ∈ Λ.1 ∧ Q.eval x = Q.eval h} =
        {x | ∃ k ∈ ks, ∃ γ ∈ gammaLat Q Λ, x = (γ : GL (Fin n) F).val *ᵥ k} := by
  classical
  set S := {x : Fin n → F | x ∈ Λ.1 ∧ Q.eval x = Q.eval h}
  have hS : S.Finite := finite_solutions_of_totallyPosDef hQ Λ (Q.eval h)
  refine ⟨hS.toFinset, fun k hk => ((Set.Finite.mem_toFinset hS).1 hk).1, ?_⟩
  ext x
  constructor
  · intro hx
    exact ⟨x, (Set.Finite.mem_toFinset hS).2 hx, 1, (gammaLat Q Λ).one_mem, by simp⟩
  · rintro ⟨k, hk, γ, hγ, rfl⟩
    have hkS := (Set.Finite.mem_toFinset hS).1 hk
    refine ⟨?_, ?_⟩
    · have hmem : glImage (γ : GL (Fin n) F) Λ.1 = Λ.1 := hγ.2
      rw [← hmem]
      exact mulVec_mem_glImage hkS.1
    · rw [eval_mulVec_of_mem Q γ.2]
      exact hkS.2

end QuadFormsKB.Shimura2004
