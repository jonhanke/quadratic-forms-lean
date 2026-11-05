/-
# Conway–Sloane, Ch. 15, §9.2, p. 389: Theorem 15 (b) fails in dimension 2

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.2, p. 389
(`conwaysloane1999`), remark after Theorem 15.

**Proves** `theorem15b_fails_dim_two`: for $f = x^2 + y^2$ and $L = \mathbb Z^2$ there is no lattice $M$ in the genus of
$L$ with $[L : L \cap M] = 3$ (the prime $3$ is prime to $2d = 2$).
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorems
import QuadFormsKB.Literature.Cassels.Ch11Sec4Thm

open NumberField IsDedekindDomain Matrix

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices Tamagawa.SiegelSpace

namespace Thm15Binary

/-- The values of $x^2 + y^2$ over $\mathbb Q$. -/
theorem csQ_one_eval (x : Fin 2 → ℚ) : (csQ (1 : Matrix (Fin 2) (Fin 2) ℤ)).evalIn ℚ x = x 0 ^ 2 + x 1 ^ 2 := by
  rw [QuadForm.evalIn_eq_dotProduct]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Cassels.Ch8Ex2.gramForm, QuadForm.map]
  ring

/-- $x^2 + y^2$ is nondegenerate. -/
theorem csQ_one_nondeg : (csQ (1 : Matrix (Fin 2) (Fin 2) ℤ)).Nondegenerate :=
  csQ_nondegenerate (by simp) (by simp)

/-- An element of $\mathcal O_{\mathbb Q}$ is the integer it corresponds to. -/
theorem intEquiv_alg (x : 𝓞 ℚ) :
    algebraMap (𝓞 ℚ) ℚ x = ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) x : ℤ) : ℚ) := by
  have : x = ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) x : ℤ) : 𝓞 ℚ) := by
    exact ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm_apply_apply x).symm.trans
      (map_intCast ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm) _)
  conv_lhs => rw [this]
  simp

/-- The vectors of $\mathbb Z^2 \subseteq \mathbb Q^2$ are the integer vectors. -/
theorem mem_stdLat_iff (y : Fin 2 → ℚ) :
    y ∈ (stdLat : Lat ℚ 2).1 ↔ ∃ a : Fin 2 → ℤ, ∀ i, y i = (a i : ℚ) := by
  change y ∈ (intVec : Submodule (𝓞 ℚ) (Fin 2 → ℚ)) ↔ _
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := mem_intVec_iff_exists.mp hy
    exact ⟨fun i => Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) (x i), fun i => intEquiv_alg _⟩
  · rintro ⟨a, ha⟩
    refine mem_intVec_iff_exists.mpr ⟨fun i => (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm (a i), funext fun i => ?_⟩
    simp [ha]

/-- $x^2 + y^2$ is integral on $\mathbb Z^2$. -/
theorem isIntegral_std : IsIntegral (csQ (1 : Matrix (Fin 2) (Fin 2) ℤ)) (stdLat : Lat ℚ 2).1 := by
  intro x hx
  obtain ⟨a, ha⟩ := (mem_stdLat_iff x).mp hx
  refine ⟨(Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm (a 0 ^ 2 + a 1 ^ 2), ?_⟩
  rw [csQ_one_eval, ha, ha]
  simp

end Thm15Binary

open Thm15Binary in
/-- **Conway–Sloane, §9.2, p. 389: Theorem 15 (b) needs $n \ge 3$.**  Theorem 15 (b) says that for a lattice $L$ in
dimension $n \ge 3$ and a natural number $r$ prime to $2d$, there is a lattice $M$ in the genus of $L$ with
$[L : L \cap M] = [M : L \cap M] = r$ (so that the spinor operator $\Delta(r)$ is defined; for $n \ge 3$ this is
`casselsAct_exists`).  In dimension $2$ it fails: for $f = x^2 + y^2$ (Gram matrix the identity, $d = 1$, so
$2d = 2$) and $L = \mathbb Z^2$, there is no lattice $M$ in the genus of $L$ with $[L : L \cap M] = 3$, although $3$
is prime to $2d$.  (Equivalently, by `casselsI_comm`, none with $[M : L \cap M] = 3$.)  This reflects
Conway–Sloane §3.5: for binary forms not every sequence of unit square classes gives a spinor operator.

*Proof.* Lattices in one genus have the same determinant, so also $[M : L \cap M] = 3$; and $M$ is integral for $f$.
As $M \ne L \cap M$ (index $3$) there is $y \in M \setminus L$, and $w = 3y \in L \cap M$ is an integer vector with
$w_0^2 + w_1^2 = 9 f(y) \equiv 0 \pmod 3$.  Since $-1$ is not a square modulo $3$, $3 \mid w_0, w_1$, so
$y \in \mathbb Z^2 = L$, a contradiction. -/
@[kb "conwaysloane1999" "Ch. 15, §9.2, p. 389 (Thm. 15 (b) fails in dimension 2)"]
theorem theorem15b_fails_dim_two :
    ¬ ∃ M : Lat ℚ 2, SameGenus (csQ (1 : Matrix (Fin 2) (Fin 2) ℤ)) (stdLat : Lat ℚ 2).1 M.1 ∧
      casselsI (stdLat : Lat ℚ 2) M = 3 := by
  rintro ⟨M, hg, hI⟩
  have hdet : latIndex (stdLat : Lat ℚ 2) = latIndex M := latIndex_eq_of_sameGenus_of_nondeg _ csQ_one_nondeg hg
  have hI' : casselsI M stdLat = 3 := (casselsI_comm hdet.symm).trans hI
  have hint := SameGenus.isIntegral _ isIntegral_std hg
  -- some y ∈ M not in L
  obtain ⟨y, hyM, hyL⟩ : ∃ y ∈ M.1, y ∉ (stdLat : Lat ℚ 2).1 := by
    by_contra hcon
    push Not at hcon
    have hle : M.1 ≤ (stdLat : Lat ℚ 2).1 := hcon
    have : casselsI M stdLat = 1 := by
      unfold casselsI
      rw [inf_eq_left.mpr hle]
      exact AddSubgroup.relIndex_self _
    omega
  have h3 : (3 : ℕ) • y ∈ (M.1 ⊓ (stdLat : Lat ℚ 2).1) := by
    have := relIndex_nsmul_mem_aux (H := (M.1 ⊓ (stdLat : Lat ℚ 2).1).toAddSubgroup) (K := M.1.toAddSubgroup)
      (x := y) hyM
    have e : (M.1 ⊓ (stdLat : Lat ℚ 2).1).toAddSubgroup.relIndex M.1.toAddSubgroup = 3 := hI'
    rw [e] at this
    exact this
  obtain ⟨a, ha⟩ := (mem_stdLat_iff _).mp h3.2
  obtain ⟨q, hq⟩ := hint y hyM
  rw [csQ_one_eval, intEquiv_alg] at hq
  have ha' : ∀ i, 3 * y i = (a i : ℚ) := fun i => by simpa using ha i
  have hsum : a 0 ^ 2 + a 1 ^ 2 = 9 * Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) q := by
    have : ((a 0 ^ 2 + a 1 ^ 2 : ℤ) : ℚ) = ((9 * Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) q : ℤ) : ℚ) := by
      push_cast
      rw [← ha' 0, ← ha' 1, hq]; ring
    exact_mod_cast this
  have hdv : ∀ i, (3 : ℤ) ∣ a i := by
    have h0 : (a 0 ^ 2 + a 1 ^ 2) % 3 = 0 := by omega
    have key : ∀ u v : ℤ, (u ^ 2 + v ^ 2) % 3 = 0 → 3 ∣ u ∧ 3 ∣ v := by
      intro u v h
      have hu : u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2 := by omega
      have hv : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2 := by omega
      rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;>
        simp [pow_two, Int.add_emod, Int.mul_emod, hu, hv] at h <;> omega
    intro i
    fin_cases i
    · exact (key _ _ h0).1
    · exact (key _ _ h0).2
  apply hyL
  refine (mem_stdLat_iff y).mpr ⟨fun i => (hdv i).choose, fun i => ?_⟩
  have := (hdv i).choose_spec
  have h' : (a i : ℚ) = 3 * (((hdv i).choose : ℤ) : ℚ) := by exact_mod_cast this
  linarith [ha' i]

end QuadFormsKB.ConwaySloane
