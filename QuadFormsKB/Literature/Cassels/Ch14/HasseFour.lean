/-
# Cassels, Chapter 14, §7: the case $n = 4$ of the strong Hasse principle from the weak one

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §7, pp. 353–354 (14.r13).

Cassels removes Dirichlet's theorem on primes in arithmetic progressions from the proof of the case $n = 4$ of the
strong Hasse principle (Ch. 6, §5): *let $f$ be a regular rational form in $4$ variables which is isotropic over every
$\mathbb Q_p$ (including $p = \infty$). Then $f$ is isotropic over $\mathbb Q$.* His argument:

1. over each $\mathbb Q_p$, $f \cong g_p \perp H$ with $g_p$ binary and $H$ a hyperbolic plane, so $d(g_p) = -d(f)$ and
   $\prod_p c_p(g_p) = 1$;
2. by Lemma 5.1 (`exists_rat_form_of_local`) there is a rational binary $g$ with $g \cong g_p$ over every $\mathbb Q_p$;
3. the six-variable form $h = f \perp (-g)$ is, over every $\mathbb Q_p$, the sum of three hyperbolic planes, hence so
   over $\mathbb Q$ by the weak Hasse principle (`WeakHassePrinciple`, Ch. 6, Thm. 1.2);
4. so $h = \sum_{j=1}^3 \varphi_j \psi_j$ for rational linear forms $\varphi_j, \psi_j$; a non-zero rational solution
   $(a_1, \dots, a_4)$ of the three equations $\varphi_j(a_1, \dots, a_4, 0, 0) = 0$ gives
   $f(a_1, \dots, a_4) = h(a_1, \dots, a_4, 0, 0) = 0$.

`isotropic_four_of_weakHasse` is this reduction, with the weak Hasse principle in six variables as a named hypothesis
(`WeakHassePrinciple 6`); `weakHassePrinciple` discharges it with the library's weak Hasse principle
(`isometric_of_everywhere`, Ch. 6, Thm. 1.2), giving `isotropic_four_of_everywhere`.

*Remark.* In this library the weak principle is proved from the strong one (`isometric_of_everywhere` uses
`hasseMinkowski` in every dimension), and Lemma 5.1 from `Prescribed.exists_rat_prescribed_hilbert`, which uses
Dirichlet's theorem; so the unconditional corollary does not reproduce Cassels' point (a proof without Dirichlet's
theorem), only his reduction.
-/
import QuadFormsKB.Literature.Cassels.Ch14.Existence
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Literature.Cassels.Ch14.ExistenceImage
import QuadFormsKB.Literature.Cassels.Ch14.HasseFourSplit
import QuadFormsKB.Literature.Cassels.Ch14.HasseFourHasse
import QuadFormsKB.Literature.Cassels.Ch14.HasseFourLinear

namespace QuadFormsKB.Composition

open QuadForm RatPlace Siegel

/-- **The weak Hasse principle in $n$ variables** (Cassels, Ch. 6, Theorem 1.2, p. 76; in Ch. 14, §7, p. 354, "in the
formulation that an element of the global Witt group which is everywhere locally trivial must be trivial"): two
nondegenerate rational forms in $n$ variables which are equivalent over $\mathbb R$ and over every $\mathbb Q_p$ are
equivalent over $\mathbb Q$. A named hypothesis of `isotropic_four_of_weakHasse`; proved in the library as
`isometric_of_everywhere` (`weakHassePrinciple`). -/
structure WeakHassePrinciple (n : ℕ) : Prop where
  /-- Everywhere locally equivalent nondegenerate rational forms are equivalent over $\mathbb Q$. -/
  isometric : ∀ Q R : RatQF n, Q.Nondegenerate → R.Nondegenerate →
    (Everywhere fun K _ _ => Q.IsometricIn K R) → Q.IsometricIn ℚ R

/-- **The weak Hasse principle holds** (Cassels, Ch. 6, Theorem 1.2, p. 76; `isometric_of_everywhere`). -/
theorem weakHassePrinciple (n : ℕ) : WeakHassePrinciple n :=
  ⟨fun Q R hQ hR h => isometric_of_everywhere Q R hQ hR h⟩

/-- Evaluating a rational form over $K$ is evaluating its base change to $K$. -/
theorem evalIn_eq_map_eval {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ} (R : QuadForm ℚ n) (y : Fin n → K) :
    R.evalIn K y = (R.map (algebraMap ℚ K)).eval y := by
  simp [QuadForm.evalIn, QuadForm.map]

/-- Isometry over $K$ of rational forms is isometry of their base changes to $K$. -/
theorem isometricIn_iff_map {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ} (Q Q' : QuadForm ℚ n) :
    Q.IsometricIn K Q' ↔ (Q.map (algebraMap ℚ K)).IsometricIn K (Q'.map (algebraMap ℚ K)) := by
  simp only [QuadForm.IsometricIn, evalIn_eq_map_eval]

/-- Isotropy over $K$ of a rational form is isotropy of its base change to $K$. -/
theorem isotropicIn_iff_map {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ} (Q : QuadForm ℚ n) :
    Q.IsotropicIn K ↔ (Q.map (algebraMap ℚ K)).IsotropicIn K := by
  simp only [QuadForm.IsotropicIn, evalIn_eq_map_eval]

/-- Base change of a rational diagonal form is the diagonal form of the cast entries. -/
theorem map_diag_cast {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ} (a : Fin n → ℚ) :
    (diag a).map (algebraMap ℚ K) = diag (fun i => algebraMap ℚ K (a i)) :=
  map_diag _ a

/-- Isotropy over $K$ of a rational diagonal form, as isotropy of the diagonal $K$-form of the cast entries. -/
theorem isotropicIn_diag_cast (K : Type) [Field K] [CharZero K] {n : ℕ} (a : Fin n → ℚ) :
    (diag a).IsotropicIn K ↔ (diag (fun i => (a i : K))).IsotropicIn K := by
  rw [isotropicIn_iff_map, map_diag_cast]
  simp

/-- A diagonal rational form with non-zero entries is nondegenerate. -/
theorem diag_nondeg {n : ℕ} (v : Fin n → ℚ) (hv : ∀ i, v i ≠ 0) : (diag v).Nondegenerate := by
  unfold QuadForm.Nondegenerate QuadForm.hessian
  simp only [diag, Matrix.diagonal_transpose, Matrix.diagonal_add, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by
    have := hv i
    simpa [two_mul] using this

/-- The local isometry $\langle a, -c \rangle \cong \langle 1, -1, 1, -1, 1, -1 \rangle$ over $K$ (Cassels, Ch. 14, §7,
step 3): $\langle a \rangle \cong \langle b_0, b_1, 1, -1 \rangle$ and $G \cong \langle c \rangle$ over $\mathbb Q$,
$G \cong \langle b_0, b_1 \rangle$ over $K$. -/
theorem local_iso (a : Fin 4 → ℚ) (c : Fin 2 → ℚ) (G : QuadForm ℚ 2) (hGc : G.IsometricIn ℚ (diag c))
    {K : Type} [Field K] [CharZero K] {b₀ b₁ : K} (h₀ : b₀ ≠ 0) (h₁ : b₁ ≠ 0)
    (hA : (diag (fun i => (a i : K))).IsometricIn K (diag ![b₀, b₁, 1, -1]))
    (hG : (G.map (Rat.castHom K)).IsometricIn K (diag ![b₀, b₁])) :
    (diag (Fin.append a (-c))).IsometricIn K (diag (![1, -1, 1, -1, 1, -1] : Fin 6 → ℚ)) := by
  rw [isometricIn_iff_map, map_diag_cast, map_diag_cast]
  have hGK := isometricIn_map_base K hGc
  rw [map_diag_cast] at hGK
  have e : algebraMap ℚ K = Rat.castHom K := Subsingleton.elim _ _
  rw [e] at hGK
  have hcK : (diag fun i => (c i : K)).IsometricIn K (diag ![b₀, b₁]) :=
    QuadForm.isometricIn_trans _ (QuadForm.isometricIn_symm _ hGK) hG
  have hn := diag_neg_isometric hcK
  have hneg : (-(![b₀, b₁] : Fin 2 → K)) = ![-b₀, -b₁] := by
    ext i; fin_cases i <;> simp
  rw [hneg] at hn
  have h6 := diag_append_isometric hA hn
  have hap : Fin.append ![b₀, b₁, 1, -1] ![-b₀, -b₁] = (![b₀, b₁, 1, -1, -b₀, -b₁] : Fin 6 → K) := by
    ext i; fin_cases i <;> rfl
  rw [hap] at h6
  have e1 : (fun i => algebraMap ℚ K (Fin.append a (-c) i)) =
      Fin.append (fun i => (a i : K)) (-(fun i => (c i : K))) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Fin.append_left, Fin.append_right]
  have e2 : (fun i => algebraMap ℚ K ((![1, -1, 1, -1, 1, -1] : Fin 6 → ℚ) i)) =
      (![1, -1, 1, -1, 1, -1] : Fin 6 → K) := by
    funext i; fin_cases i <;> simp
  rw [e1, e2]
  exact QuadForm.isometricIn_trans _ h6 (diag_six_hyperbolic h₀ h₁)

/-- **Cassels, Ch. 14, §7** (pp. 353–354): *the case $n = 4$ of the strong Hasse principle follows from the weak Hasse
principle* (and Lemma 5.1): a nondegenerate rational quaternary form which is isotropic over $\mathbb R$ and over every
$\mathbb Q_p$ is isotropic over $\mathbb Q$, assuming the weak Hasse principle for forms in $6$ variables. -/
@[kb "cassels1978" "Ch. 14, §7, pp. 353–354 (n = 4 of the strong Hasse principle from the weak one)"]
theorem isotropic_four_of_weakHasse (hW : WeakHassePrinciple 6) (Q : RatQF 4) (hQ : Q.Nondegenerate)
    (hloc : Everywhere fun K _ _ => Q.IsotropicIn K) : Q.IsotropicIn ℚ := by
  classical
  -- (0) diagonalize over ℚ
  obtain ⟨a, ha, hQa⟩ := FieldGen.exists_isometric_diag Q hQ
  have hlocK : ∀ (K : Type) [Field K] [CharZero K], Q.IsotropicIn K → (diag a).IsotropicIn K :=
    fun K _ _ h => (FieldGen.isotropicIn_iff_of_isometricIn K (FieldGen.isometricIn_of_base K hQa)).mp h
  have hlocP : ∀ (p : ℕ) [Fact p.Prime], (diag a).IsotropicIn ℚ_[p] := fun p _ =>
    hlocK ℚ_[p] (hloc (.finite ⟨p, Fact.out⟩))
  have hlocR : (diag a).IsotropicIn ℝ := hlocK ℝ (hloc .infinite)
  have haK : ∀ (K : Type) [Field K] [CharZero K] (i : Fin 4), (a i : K) ≠ 0 := fun K _ _ i =>
    Rat.cast_ne_zero.mpr (ha i)
  -- (1) split at every place
  have hP : ∀ (p : ℕ) [Fact p.Prime], ∃ b₀ b₁ : ℚ_[p], b₀ ≠ 0 ∧ b₁ ≠ 0 ∧
      b₀ * b₁ = -((a 0 : ℚ_[p]) * a 1 * a 2 * a 3) ∧
      (diag (fun i => (a i : ℚ_[p]))).IsometricIn ℚ_[p] (diag ![b₀, b₁, 1, -1]) := fun p _ =>
    exists_split_diag_four (haK ℚ_[p]) ((isotropicIn_diag_cast ℚ_[p] a).mp (hlocP p))
  have hR : ∃ b₀ b₁ : ℝ, b₀ ≠ 0 ∧ b₁ ≠ 0 ∧ b₀ * b₁ = -((a 0 : ℝ) * a 1 * a 2 * a 3) ∧
      (diag (fun i => (a i : ℝ))).IsometricIn ℝ (diag ![b₀, b₁, 1, -1]) :=
    exists_split_diag_four (haK ℝ) ((isotropicIn_diag_cast ℝ a).mp hlocR)
  choose b₀ b₁ hb₀ hb₁ hbb hbiso using hP
  obtain ⟨β₀, β₁, hβ₀, hβ₁, hββ, hβiso⟩ := hR
  -- (2) the local binary forms
  have hD : (4 * (a 0 * a 1 * a 2 * a 3) : ℚ) ≠ 0 := by
    have := ha 0; have := ha 1; have := ha 2; have := ha 3
    positivity
  have hdet : ∀ (K : Type) [Field K] [CharZero K] (x y : K), x * y = -((a 0 : K) * a 1 * a 2 * a 3) →
      -(diag ![x, y]).hessian.det = ((4 * (a 0 * a 1 * a 2 * a 3) : ℚ) : K) := by
    intro K _ _ x y h
    rw [Binary.hessian_det_two]
    simp [diag]
    linear_combination (-4 : K) * h
  have hsp : ∀ (p : ℕ) [Fact p.Prime], hasseC (diag ![b₀ p, b₁ p]) = splitSign a (.finite ⟨p, Fact.out⟩) := by
    intro p _
    rw [hasseC_split_padic p (haK ℚ_[p]) (hb₀ p) (hb₁ p) (hbb p) (hbiso p)]
    simp [splitSign]
  have hsr : hasseC (diag ![β₀, β₁]) = splitSign a .infinite := by
    rw [hasseC_split_real (haK ℝ) hβ₀ hβ₁ hββ hβiso]
    simp [splitSign]
  obtain ⟨hfin0, hprod0⟩ := splitSign_finite_prod a ha
  have hat : ∀ p : Nat.Primes, hasseAt (fun p _ => diag ![b₀ p, b₁ p]) p = splitSign a (.finite p) := by
    intro p
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    exact hsp p
  -- (3) Lemma 5.1
  obtain ⟨G, hGD, hGp, hGinf⟩ := exists_rat_form_of_local (4 * (a 0 * a 1 * a 2 * a 3)) hD
    (fun p _ => diag ![b₀ p, b₁ p]) (fun p _ => hdet ℚ_[p] _ _ (hbb p)) (diag ![β₀, β₁])
    (hdet ℝ _ _ hββ)
    (by simp only [hat]; exact hfin0) (by simp only [hat, hsr]; exact hprod0)
  have hGnd : G.Nondegenerate := nondeg_of_det hD hGD
  obtain ⟨c, hc, hGc⟩ := FieldGen.exists_isometric_diag G hGnd
  -- (4) the six-variable forms
  have hnd1 : (diag (Fin.append a (-c))).Nondegenerate := by
    refine diag_nondeg _ fun i => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using ha j
    · simpa using hc j
  have hnd2 : (diag (![1, -1, 1, -1, 1, -1] : Fin 6 → ℚ)).Nondegenerate :=
    diag_nondeg _ fun i => by fin_cases i <;> simp
  have hiso6 := hW.isometric _ _ hnd1 hnd2 (by
    intro v
    cases v with
    | infinite =>
      exact local_iso a c G hGc hβ₀ hβ₁ hβiso (by
        have := (isometricGL_iff_isometricIn _ _).mp hGinf
        simpa using this)
    | finite p =>
      have : Fact (p : ℕ).Prime := ⟨p.2⟩
      exact local_iso a c G hGc (hb₀ p) (hb₁ p) (hbiso p) (by
        have := (isometricGL_iff_isometricIn _ _).mp (hGp p)
        simpa using this))
  -- (5) conclude
  have hiso : (diag a).IsotropicIn ℚ := isotropic_of_isometric_hyp_three hiso6
  exact (FieldGen.isotropicIn_iff_of_isometricIn ℚ hQa).mpr hiso

/-- **Cassels, Ch. 14, §7, unconditionally** (pp. 353–354): `isotropic_four_of_weakHasse` with the weak Hasse
principle discharged (`weakHassePrinciple`). -/
@[kb "cassels1978" "Ch. 14, §7, pp. 353–354"]
theorem isotropic_four_of_everywhere (Q : RatQF 4) (hQ : Q.Nondegenerate)
    (hloc : Everywhere fun K _ _ => Q.IsotropicIn K) : Q.IsotropicIn ℚ :=
  isotropic_four_of_weakHasse (weakHassePrinciple 6) Q hQ hloc

end QuadFormsKB.Composition
