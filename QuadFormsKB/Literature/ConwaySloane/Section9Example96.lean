/-
# Conway–Sloane, Ch. 15, §9.6: the example with two spinor genera

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.6, pp. 392–393
(`conwaysloane1999`): the form
$$f = \begin{pmatrix} 2 & 1 & 0\\ 1 & 2 & 0\\ 0 & 0 & 18\end{pmatrix}$$
(Watson, p. 115). The book computes the automorphous numbers: at $3$, list (I) is $\{2 = u_-, 3/2 = 3u_-,
18 = 9u_-\}$, "so the $3$-adically automorphous numbers are $\{u_+, 3u_+\}$"; at $2$ they are the units; and concludes
that $(u_-)_3$ is not in the spinor kernel, "and therefore the genus of $f$ contains two distinct spinor genera".

**Layer.** $f$ = `csQ A96` over $\mathbb Q$, the lattice $\mathbb Z^3$ (`stdLat`), Conway–Sloane's set $\Pi$ =
`primeSet (2 det H)` $= \{2, 3\}$ (as in `Section9Final2.lean`).

**Proves**
* `theta3_le` (unconditional): every $3$-adically automorphous number is in $\langle 3\rangle\mathbb Q_3^{\times 2}$
  (the reverse inclusion of the algorithm at $p = 3$, `algorithm_odd_upper`, with the orthogonal basis
  $e_0, e_1 - \tfrac12e_0, e_2$ of $\mathbb Z_3^3$, $Q$-values $2, 3/2, 18$);
* `rootNorm_two_odd` (unconditional): every $2$-adic root vector has a norm of odd order ($2\cdot$unit up to
  squares);
* `theta2_even` (unconditional): every $2$-adically automorphous number has even order. At $2$, $f$ is
  $E \perp \langle 2\cdot 9\rangle$ with $E = \begin{pmatrix}2&1\\1&2\end{pmatrix}$ even unimodular, so this is the
  glue lemma `Glue.exists_sq_valued_wallDet_glue` with Wall's formula (`even_log_of_wallCore`). (Formerly derived from
  the named statement `Theorem18Dyadic`.)
* `example96_two_spinorGenera` (**unconditional**): the genus of $f$ contains a lattice $M$ not in the spinor genus of
  $\mathbb Z^3$, and (`example96_two_classes`) no isometry maps $\mathbb Z^3$ onto $M$ (the genus has more than one
  class).

The $2$-adic upper bound is genuinely needed: if $2\cdot$unit were $2$-adically automorphous, $\Delta_2$ of it would
put $(u_-)_3$ in the spinor kernel ($2$ is a non-residue mod $3$), and the genus would be one spinor genus.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9RootNorms
import QuadFormsKB.Literature.ConwaySloane.Section9DyadicUpper
import QuadFormsKB.Literature.ConwaySloane.Section9TwoSpinorGenera
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem16
import QuadFormsKB.Literature.ConwaySloane.Section9Main
import QuadFormsKB.Literature.ConwaySloane.Section9DyadicEven
import QuadFormsKB.Literature.ConwaySloane.Section9DyadicGlue

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- The form of the example (Conway–Sloane §9.6, p. 392; Watson p. 115). -/
def A96 : Matrix (Fin 3) (Fin 3) ℤ := !![2, 1, 0; 1, 2, 0; 0, 0, 18]

theorem A96_symm : A96ᵀ = A96 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem A96_det : A96.det = 54 := by
  simp [A96, Matrix.det_fin_three]

theorem A96_hessian : (Cassels.Ch8Ex2.gramForm A96).hessian = !![4, 2, 0; 2, 4, 0; 0, 0, 36] := by
  rw [hessian_csForm A96_symm]
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem A96_hessian_det : (Cassels.Ch8Ex2.gramForm A96).hessian.det = 432 := by
  rw [A96_hessian]; simp [Matrix.det_fin_three]

theorem A96_nondeg : (csQ A96).Nondegenerate := csQ_nondegenerate A96_symm (by rw [A96_det]; norm_num)

/-- The place of $\mathbb Q$ above $3$. -/
def v3 : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨3, Nat.prime_three⟩

theorem primeOf_v3 : primeOf v3 = 3 :=
  congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨3, Nat.prime_three⟩)

/-- Conway–Sloane's $\Pi$ (without $-1$) for the example: the primes dividing $2\det H = 864 = 2^5\cdot 3^3$. -/
abbrev P96 : Finset (HeightOneSpectrum (𝓞 ℚ)) := primeSet (2 * (Cassels.Ch8Ex2.gramForm A96).hessian.det)

theorem mem_P96_iff {v : HeightOneSpectrum (𝓞 ℚ)} : v ∈ P96 ↔ primeOf v = 2 ∨ primeOf v = 3 := by
  show v ∈ primeSet _ ↔ _
  rw [primeSet, Finset.mem_preimage, Nat.mem_primeFactors, A96_hessian_det]
  have hp := Rat.HeightOneSpectrum.prime_natGenerator v
  constructor
  · rintro ⟨-, hd, -⟩
    have h864 : primeOf v ∣ 2 ^ 5 * 3 ^ 3 := by simpa using hd
    rcases (Nat.Prime.dvd_mul hp).mp h864 with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))
  · rintro (h | h) <;> refine ⟨hp, ?_, by norm_num⟩ <;> simp only [primeOf] at h <;> rw [h] <;> norm_num

theorem v3_mem : v3 ∈ P96 := mem_P96_iff.mpr (Or.inr primeOf_v3)

/-- The prime $3$ as an element of $\Pi$. -/
def q3 : P96 := ⟨v3, v3_mem⟩

/-! ### Valuations at $3$ -/

local notation "F3" => v3.adicCompletion ℚ

theorem natGenerator_v3 : Rat.HeightOneSpectrum.natGenerator v3 = 3 := primeOf_v3

theorem algebraMap_natGenUnit_v3 : algebraMap ℚ F3 ((natGenUnit v3 : ℚˣ) : ℚ) = 3 := by
  simp only [natGenUnit, Units.val_mk0, natGenerator_v3, map_natCast]; norm_num

theorem valued_v3_three : Valued.v (3 : F3) = exp (-1 : ℤ) := by
  have := valued_natGenUnit_self v3
  rwa [algebraMap_natGenUnit_v3] at this

theorem valued_v3_two : Valued.v (2 : F3) = 1 := by
  have := valued_intCast_eq_one v3 2 (by rw [natGenerator_v3]; norm_num)
  simpa using this

theorem two_not_mem_v3 : (2 : 𝓞 ℚ) ∉ v3.asIdeal := by
  rw [two_mem_iff_natGenerator, natGenerator_v3]; norm_num

/-- $-1$ is not a square in $\mathbb Q_3$. -/
theorem not_isSquare_neg_one_padic_three : ¬ IsSquare (-1 : ℚ_[3]) := by
  rintro ⟨y, hy⟩
  have hn : ‖y‖ = 1 := by
    have h := congrArg norm hy
    rw [norm_neg, norm_one, norm_mul] at h
    nlinarith [norm_nonneg y]
  let z : ℤ_[3] := ⟨y, hn.le⟩
  have hz : z * z = -1 := Subtype.ext (by show y * y = -1; exact hy.symm)
  have h := congrArg PadicInt.toZMod hz
  rw [map_mul, map_neg, map_one] at h
  revert h
  generalize PadicInt.toZMod z = w
  revert w
  decide

theorem not_isSquare_neg_one_v3 : ¬ IsSquare (-1 : F3) := by
  rintro ⟨y, hy⟩
  have hp3 : ((Rat.HeightOneSpectrum.primesEquiv v3 : Nat.Primes) : ℕ) = 3 := primeOf_v3
  have key : ∀ (p : Nat.Primes), (p : ℕ) = 3 → ¬ IsSquare (-1 : ℚ_[p]) := by
    rintro ⟨p, hp⟩ (rfl : p = 3)
    exact not_isSquare_neg_one_padic_three
  refine key _ hp3 ⟨Rat.HeightOneSpectrum.adicCompletion.padicEquiv v3 y, ?_⟩
  rw [← map_mul, ← hy, map_neg, map_one]

/-- An element of odd order is not a square. -/
theorem not_isSquare_of_valued_eq_exp_odd {K : Type*} [Field K] [Valued K ℤᵐ⁰] {x : K} {k : ℤ}
    (hx : Valued.v x = exp (2 * k + 1)) : ¬ IsSquare x := by
  rintro ⟨y, rfl⟩
  have hy : Valued.v y ≠ 0 := by
    intro h; rw [map_mul, h, zero_mul] at hx; exact exp_ne_zero hx.symm
  rw [map_mul, ← exp_log hy, ← exp_add] at hx
  have := exp_injective hx
  omega

/-! ### The $3$-adic upper bound -/

/-- The change of basis $e_0$, $e_1 - \tfrac12 e_0$, $e_2$ (orthogonal for $f$, invertible over $\mathbb Z_3$). -/
def T96 : GL (Fin 3) ℚ :=
  ⟨!![1, -1/2, 0; 0, 1, 0; 0, 0, 1], !![1, 1/2, 0; 0, 1, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem csQ_A96_hessian : (csQ A96).hessian = !![4, 2, 0; 2, 4, 0; 0, 0, 36] := by
  rw [csQ, QuadForm.hessian_map, A96_hessian]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem T96_gram : T96.valᵀ * (csQ A96).hessian * T96.val = Matrix.diagonal ![4, 3, 36] := by
  rw [csQ_A96_hessian]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [T96, Matrix.mul_apply, Fin.sum_univ_three]

/-- The basis $\gamma$ of $\mathbb Z_3^3$. -/
def γ96 : GL (Fin 3) F3 := GeneralLinearGroup.map (algebraMap ℚ F3) T96

theorem locGram_γ96 : locGram (csQ A96) v3 γ96 = (Matrix.diagonal ![4, 3, 36]).map (algebraMap ℚ F3) := by
  rw [← T96_gram]
  unfold locGram
  rw [γ96, glMap_val, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

theorem hγ96 : loc v3 (stdLat : Lat ℚ 3).1 = locAct v3 γ96 (std v3) := by
  have hT : ∀ i j, T96.val i j ∈ locSub v3 := by
    intro i j
    rw [mem_locSub]
    fin_cases i <;> fin_cases j <;> simp [T96, valued_v3_two]
  have hdet : T96.val.det = 1 ∨ T96.val.det = -1 := Or.inl (by simp [T96, Matrix.det_fin_three])
  have h := loc_latOf_eq_std v3 T96 hT hdet
  rw [latOf, loc_glImage, loc_intVec] at h
  exact (loc_intVec v3).trans h.symm

theorem horth96 : ∀ k l, k ≠ l → locGram (csQ A96) v3 γ96 k l = 0 := by
  intro k l hkl
  rw [locGram_γ96, Matrix.map_apply, Matrix.diagonal_apply_ne _ hkl, map_zero]

/-- The values $Q(b_k) = 2, 3/2, 18$ of the orthogonal basis (the book's list (I) at $p = 3$). -/
theorem Qb96 (k : Fin 3) :
    (csQ A96).evalIn F3 (γ96.val *ᵥ Pi.single k 1) = algebraMap ℚ F3 (![2, 3/2, 18] k) := by
  rw [evalIn_basis_eq, locGram_γ96, Matrix.map_apply, Matrix.diagonal_apply_eq]
  rw [show (2 : F3) = algebraMap ℚ F3 2 by simp, ← map_div₀]
  congr 1
  fin_cases k <;> norm_num

theorem sqClass_primeUnit_q3 : SqClass.mk (primeUnit P96 q3) = sqClassOf (3 : F3) := by
  rw [sqClassOf_of_ne_zero (three_ne_zero)]
  congr 1
  refine Units.ext ?_
  show algebraMap ℚ F3 ((natGenUnit v3 : ℚˣ) : ℚ) = 3
  exact algebraMap_natGenUnit_v3

theorem mem_zpowers_of_rat (r s : ℚ) (hs : s ≠ 0) (h : r = s ^ 2 ∨ r = 3 * s ^ 2) :
    sqClassOf (algebraMap ℚ F3 r) ∈ Subgroup.zpowers (SqClass.mk (primeUnit P96 q3)) := by
  have hs' : algebraMap ℚ F3 s ≠ 0 := (map_ne_zero _).mpr hs
  rcases h with rfl | rfl
  · rw [map_pow, (sqClassOf_eq_one_iff (pow_ne_zero 2 hs')).mpr ⟨_, sq _⟩]
    exact Subgroup.one_mem _
  · rw [map_mul, map_pow, map_ofNat, sqClassOf_mul three_ne_zero (pow_ne_zero 2 hs'),
      (sqClassOf_eq_one_iff (pow_ne_zero 2 hs')).mpr ⟨_, sq _⟩, mul_one, ← sqClass_primeUnit_q3]
    exact Subgroup.mem_zpowers _

/-- **The $3$-adically automorphous numbers** of the example (§9.6, p. 392: "so the $3$-adically automorphous numbers
are $\{u_+, 3u_+\}$"; here the inclusion $\subseteq$, the one the example needs): every element of
$\theta(O^+(\mathbb Z_3^3))$ lies in $\langle 3\rangle\mathbb Q_3^{\times 2}$. Unconditional (Theorem 18 at odd $p$). -/
@[kb "conwaysloane1999" "Ch. 15, §9.6, p. 392 (example: the 3-adically automorphous numbers)"]
theorem theta3_le (A : F3ˣ) (hA : A ∈ localSpinorNormGroup (csQ A96) A96_nondeg v3 stdLat) :
    SqClass.mk A ∈ Subgroup.zpowers (SqClass.mk (primeUnit P96 q3)) := by
  refine algorithm_odd_upper A96_nondeg two_not_mem_v3 stdLat hγ96 horth96 _ ?_ ?_ hA
  · intro k l
    rw [Qb96, Qb96, ← map_mul]
    fin_cases k <;> fin_cases l
    · exact mem_zpowers_of_rat _ 2 (by norm_num) (Or.inl (by norm_num))
    · exact mem_zpowers_of_rat _ 1 (by norm_num) (Or.inr (by norm_num))
    · exact mem_zpowers_of_rat _ 6 (by norm_num) (Or.inl (by norm_num))
    · exact mem_zpowers_of_rat _ 1 (by norm_num) (Or.inr (by norm_num))
    · exact mem_zpowers_of_rat _ (3/2) (by norm_num) (Or.inl (by norm_num))
    · exact mem_zpowers_of_rat _ 3 (by norm_num) (Or.inr (by norm_num))
    · exact mem_zpowers_of_rat _ 6 (by norm_num) (Or.inl (by norm_num))
    · exact mem_zpowers_of_rat _ 3 (by norm_num) (Or.inr (by norm_num))
    · exact mem_zpowers_of_rat _ 18 (by norm_num) (Or.inl (by norm_num))
  · rintro ⟨k, l, hkl, heq⟩
    exfalso
    rw [Qb96, Qb96] at heq
    have v0 : Valued.v (algebraMap ℚ F3 2) = exp (0 : ℤ) := by rw [map_ofNat, valued_v3_two]; rfl
    have v1 : Valued.v (algebraMap ℚ F3 (3/2)) = exp (-1 : ℤ) := by
      rw [map_div₀, map_ofNat, map_ofNat, map_div₀, valued_v3_three, valued_v3_two, div_one]
    have v2' : Valued.v (algebraMap ℚ F3 18) = exp (-2 : ℤ) := by
      rw [show (18 : ℚ) = 2 * 3 ^ 2 by norm_num, map_mul, map_pow, map_ofNat, map_ofNat, map_mul, map_pow,
        valued_v3_two, valued_v3_three, one_mul, ← WithZero.exp_nsmul]
      rfl
    fin_cases k <;> fin_cases l <;> simp_all [exp_injective.eq_iff, eq_comm (a := (1 : ℤᵐ⁰))]

/-! ### The $2$-adic root vectors -/

section Two

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F2" => v.adicCompletion ℚ

theorem valued_two_of_primeOf (hv : primeOf v = 2) : Valued.v (2 : F2) = exp (-1 : ℤ) := by
  have := valued_natGenerator (v := v)
  rw [show Rat.HeightOneSpectrum.natGenerator v = 2 from hv] at this
  simpa using this

theorem valued_nine_of_primeOf (hv : primeOf v = 2) : Valued.v (9 : F2) = 1 := by
  have := valued_intCast_eq_one v 9 (by rw [show Rat.HeightOneSpectrum.natGenerator v = 2 from hv]; norm_num)
  simpa using this

theorem csQ_A96_eval (x : Fin 3 → F2) :
    (csQ A96).evalIn F2 x = 2 * (x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2) + 2 * 9 * x 2 ^ 2 := by
  have h := two_mul_evalIn_locGram (Q := csQ A96) (v := v) 1 x
  simp only [Units.val_one, one_mulVec] at h
  have hG : ∀ k l, locGram (csQ A96) v 1 k l = (((Cassels.Ch8Ex2.gramForm A96).hessian k l : ℤ) : F2) :=
    fun k l => locGram_one_int v _ k l
  rw [dotProduct, Fin.sum_univ_three] at h
  simp only [mulVec, dotProduct, Fin.sum_univ_three, hG, A96_hessian] at h
  norm_num at h
  have h2 : (2 : F2) ≠ 0 := two_ne_zero
  apply mul_left_cancel₀ h2
  rw [h]; ring

theorem csQ_A96_bil (x : Fin 3 → F2) (j : Fin 3) :
    x ⬝ᵥ (locGram (csQ A96) v 1 *ᵥ Pi.single j 1) = ![4 * x 0 + 2 * x 1, 2 * x 0 + 4 * x 1, 36 * x 2] j := by
  have hG : ∀ k l, locGram (csQ A96) v 1 k l = (((Cassels.Ch8Ex2.gramForm A96).hessian k l : ℤ) : F2) :=
    fun k l => locGram_one_int v _ k l
  fin_cases j <;>
    simp [dotProduct, mulVec, Fin.sum_univ_three, hG, A96_hessian, Pi.single_apply] <;> ring

/-- **The $2$-adic root vectors of the example have norms of odd order** (norm $2\cdot$unit up to squares; the book's
lists (I) $= \{18 = 2u_1\}$ and (II) $= \{2u_1, 2u_3, 2u_5, 2u_7\}$, p. 392). Unconditional. -/
theorem rootNorm_two_odd (hv : primeOf v = 2) {x : Fin 3 → F2} (hx : IsRootVector (csQ A96) stdLat v x) :
    ∃ k : ℤ, Valued.v ((csQ A96).evalIn F2 x) = exp (2 * k + 1) := by
  have hγ : loc v (stdLat : Lat ℚ 3).1 = locAct v 1 (std v) := by rw [locAct_one]; exact loc_intVec v
  have hx' : IsRootVector (csQ A96) stdLat v ((1 : GL (Fin 3) F2).val *ᵥ x) := by simpa using hx
  have ineq : ∀ i j, Valued.v (![4 * x 0 + 2 * x 1, 2 * x 0 + 4 * x 1, 36 * x 2] j) * Valued.v (x i) ≤
      Valued.v ((csQ A96).evalIn F2 x) := fun i j => by
    have := rootVector_ineq_gen stdLat hγ hx' i j
    simp only [Units.val_one, one_mulVec] at this
    rwa [csQ_A96_bil] at this
  have hQ0 : (csQ A96).evalIn F2 x ≠ 0 := hx.1
  have v2 := valued_two_of_primeOf hv
  have v9 := valued_nine_of_primeOf hv
  set a := x 0
  set b := x 1
  set c := x 2
  set M := max (max (Valued.v a) (Valued.v b)) (Valued.v c) with hM
  have ha : Valued.v a ≤ M := le_max_of_le_left (le_max_left _ _)
  have hb : Valued.v b ≤ M := le_max_of_le_left (le_max_right _ _)
  have hc : Valued.v c ≤ M := le_max_right _ _
  have hM0 : M ≠ 0 := by
    intro h0
    apply hQ0
    have : a = 0 ∧ b = 0 ∧ c = 0 := by
      refine ⟨?_, ?_, ?_⟩ <;> rw [← Valuation.zero_iff Valued.v] <;> exact le_antisymm (h0 ▸ by assumption) zero_le
    rw [csQ_A96_eval]
    simp [a, b, c] at this ⊢
    simp [this]
  have hQ : (csQ A96).evalIn F2 x = 2 * (a ^ 2 + a * b + b ^ 2) + 2 * 9 * c ^ 2 := csQ_A96_eval x
  -- the target value
  set T := exp (-1 : ℤ) * M ^ 2 with hT
  have hT0 : T ≠ 0 := mul_ne_zero exp_ne_zero (pow_ne_zero 2 hM0)
  have hpos : (0 : ℤᵐ⁰) < M := zero_lt_iff.mpr hM0
  -- upper bound
  have hup1 : Valued.v (2 * (a ^ 2 + a * b + b ^ 2)) ≤ T := by
    rw [map_mul, v2]
    refine mul_le_mul_right ?_ _
    refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
    · rw [map_pow, sq, sq]; exact mul_le_mul' ha ha
    · rw [map_mul, sq]; exact mul_le_mul' ha hb
    · rw [map_pow, sq, sq]; exact mul_le_mul' hb hb
  have hc2 : Valued.v (2 * 9 * c ^ 2) = exp (-1 : ℤ) * Valued.v c ^ 2 := by
    rw [map_mul, map_mul, v2, v9, mul_one, map_pow]
  have hup : Valued.v ((csQ A96).evalIn F2 x) ≤ T := by
    rw [hQ]
    refine Valuation.map_add_le _ hup1 ?_
    rw [hc2]; exact mul_le_mul_right (pow_le_pow_left₀ zero_le hc 2) _
  -- lower bound
  have hlow : T ≤ Valued.v ((csQ A96).evalIn F2 x) := by
    by_cases hbM : Valued.v b = M
    · have h0 := ineq 1 0
      rw [show x 1 = b from rfl, hbM] at h0
      have e : Valued.v (4 * a + 2 * b) = exp (-1 : ℤ) * M := by
        have h4 : Valued.v (4 * a) < Valued.v (2 * b) := by
          rw [map_mul, map_mul, v2, hbM, show (4 : F2) = 2 * 2 by norm_num, map_mul, v2, ← exp_add]
          exact (mul_le_mul_right ha _).trans_lt (mul_lt_mul_of_pos_right (by rw [exp_lt_exp]; norm_num) hpos)
        rw [Valuation.map_add_eq_of_lt_right _ h4, map_mul, v2, hbM]
      simp only [Matrix.cons_val_zero] at h0
      rw [e] at h0
      rw [hT, sq, ← mul_assoc]; exact h0
    · by_cases haM : Valued.v a = M
      · have h1 := ineq 0 1
        rw [haM] at h1
        have e : Valued.v (2 * a + 4 * b) = exp (-1 : ℤ) * M := by
          have h4 : Valued.v (4 * b) < Valued.v (2 * a) := by
            rw [map_mul, map_mul, v2, haM, show (4 : F2) = 2 * 2 by norm_num, map_mul, v2, ← exp_add]
            exact (mul_le_mul_right hb _).trans_lt (mul_lt_mul_of_pos_right (by rw [exp_lt_exp]; norm_num) hpos)
          rw [Valuation.map_add_eq_of_lt_left _ h4, map_mul, v2, haM]
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
        rw [e] at h1
        rw [hT, sq, ← mul_assoc]; exact h1
      · -- both `a`, `b` small: then `c` is large and the last term dominates
        have haM' : Valued.v a < M := lt_of_le_of_ne ha haM
        have hbM' : Valued.v b < M := lt_of_le_of_ne hb hbM
        have hcM : Valued.v c = M := by
          refine le_antisymm hc ?_
          by_contra hlt
          push Not at hlt
          have hMM : M < M := by
            calc M = max (max (Valued.v a) (Valued.v b)) (Valued.v c) := hM
              _ < M := max_lt (max_lt haM' hbM') hlt
          exact lt_irrefl _ hMM
        have hsmall : Valued.v (2 * (a ^ 2 + a * b + b ^ 2)) < T := by
          rw [map_mul, v2]
          refine mul_lt_mul_of_pos_left ?_ (zero_lt_iff.mpr exp_ne_zero)
          refine Valuation.map_add_lt _ (Valuation.map_add_lt _ ?_ ?_) ?_
          · rw [map_pow, sq, sq]; exact mul_lt_mul'' haM' haM' zero_le zero_le
          · rw [map_mul, sq]; exact mul_lt_mul'' haM' hbM' zero_le zero_le
          · rw [map_pow, sq, sq]; exact mul_lt_mul'' hbM' hbM' zero_le zero_le
        have hbig : Valued.v (2 * 9 * c ^ 2) = T := by rw [hc2, hcM]
        rw [hQ, Valuation.map_add_eq_of_lt_right _ (hbig ▸ hsmall), hbig]
  have hval : Valued.v ((csQ A96).evalIn F2 x) = T := le_antisymm hup hlow
  refine ⟨WithZero.log M - 1, ?_⟩
  rw [hval, hT, ← exp_log hM0, ← WithZero.exp_nsmul, ← exp_add, log_exp]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

end Two

/-! ### An improper automorph from a coordinate swap -/

/-- **A coordinate swap as an improper integral automorph**: if the Gram matrix $A$ is invariant under exchanging the
coordinates $i_0 \ne i_1$, the permutation matrix of the transposition is an isometry of $(\mathbb Q^n, A)$ of
determinant $-1$ mapping $\mathbb Z^n$ onto itself. -/
theorem exists_improper_swap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : Aᵀ = A) (i0 i1 : Fin n) (h01 : i0 ≠ i1)
    (hsw : ∀ i j, A (Equiv.swap i0 i1 i) (Equiv.swap i0 i1 j) = A i j) :
    ∃ α : orthGroup (csQ A) ℚ, ((α : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det = -1 ∧
      glImage (α : GL (Fin n) ℚ) (stdLat : Lat ℚ n).1 = (stdLat : Lat ℚ n).1 := by
  set σ : Equiv.Perm (Fin n) := Equiv.swap i0 i1 with hσ
  have hσσ : σ * σ = 1 := Equiv.swap_mul_self i0 i1
  have hPP : ∀ (R : Type) [CommRing R], σ.permMatrix R * σ.permMatrix R = 1 := fun R _ => by
    rw [← Matrix.permMatrix_mul, hσσ, Matrix.permMatrix_one]
  let Pz : GL (Fin n) (𝓞 ℚ) := ⟨σ.permMatrix (𝓞 ℚ), σ.permMatrix (𝓞 ℚ), hPP _, hPP _⟩
  set g : GL (Fin n) ℚ := Matrix.GeneralLinearGroup.map (algebraMap (𝓞 ℚ) ℚ) Pz with hg
  have hgval : g.val = σ.permMatrix ℚ := by
    ext i j
    show (σ.permMatrix (𝓞 ℚ)).map (algebraMap (𝓞 ℚ) ℚ) i j = σ.permMatrix ℚ i j
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq]
    split_ifs <;> simp
  have hσinv : σ⁻¹ = σ := by rw [hσ, Equiv.swap_inv]
  have horth : g ∈ orthGroup (csQ A) ℚ := by
    show g.valᵀ * (csQ A).hessian.map (algebraMap ℚ ℚ) * g.val = (csQ A).hessian.map (algebraMap ℚ ℚ)
    rw [hgval, Matrix.transpose_permMatrix, hσinv]
    simp only [Equiv.Perm.permMatrix]
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    simp only [Matrix.submatrix_apply, id, Matrix.map_apply, csQ, QuadForm.hessian_map,
      hessian_csForm hA, Matrix.smul_apply, smul_eq_mul]
    rw [show σ.symm j = σ j from by rw [hσ, Equiv.symm_swap], hsw]
  refine ⟨⟨g, horth⟩, ?_, ?_⟩
  · show g.val.det = -1
    rw [hgval, Matrix.det_permutation, hσ, Equiv.Perm.sign_swap h01]
    simp
  · exact glImage_map_intVec Pz


/-! ### The example: two spinor genera -/

/-- The form of the example is positive definite, so not indefinite (Cassels' $j = 1$). -/
theorem not_isIndefinite_A96 : ¬ IsIndefinite (csQ A96) := by
  rintro ⟨w, y, hy0, hy⟩
  have hw : w.IsReal := IsTotallyReal.isReal w
  let ψ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hy' : 2 * (y 0 ^ 2 + y 0 * y 1 + y 1 ^ 2) + 18 * y 2 ^ 2 = 0 := by
    rw [← hy]
    simp [QuadForm.evalIn, csQ, QuadForm.map, Cassels.Ch8Ex2.gramForm, A96, Fin.sum_univ_three]
    ring
  have h0 := congrArg ψ hy'
  simp only [map_add, map_mul, map_pow, map_ofNat, map_zero] at h0
  set a := ψ (y 0)
  set b := ψ (y 1)
  set c := ψ (y 2)
  have ha : a = 0 := by nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hb : b = 0 := by nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hc : c = 0 := by nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b, sq_nonneg c]
  apply hy0
  funext i
  fin_cases i
  · show y 0 = 0; exact ψ.injective (by rw [map_zero]; exact ha)
  · show y 1 = 0; exact ψ.injective (by rw [map_zero]; exact hb)
  · show y 2 = 0; exact ψ.injective (by rw [map_zero]; exact hc)

theorem casselsJ_A96 : casselsJ (csQ A96) = 1 := by
  simp [casselsJ, not_isIndefinite_A96]

/-- The square class of $3$ has order dividing $2$, so $\langle 3\rangle\mathbb Q_3^{\times2}/\mathbb Q_3^{\times 2}$
has the two elements $1$ and the class of $3$. -/
theorem mem_zpowers_q3 {c : SqClass (q3.1.adicCompletion ℚ)}
    (hc : c ∈ Subgroup.zpowers (SqClass.mk (primeUnit P96 q3))) :
    c = 1 ∨ c = SqClass.mk (primeUnit P96 q3) := by
  obtain ⟨k, rfl⟩ := hc
  have hsq : (SqClass.mk (primeUnit P96 q3)) ^ (2 : ℤ) = 1 := by
    have h1 := (SqClass.mk_eq_one_iff (primeUnit P96 q3 ^ 2)).mpr ⟨_, rfl⟩
    rw [zpow_ofNat]
    rw [show SqClass.mk (primeUnit P96 q3 ^ 2) = SqClass.mk (primeUnit P96 q3) ^ 2 from
      map_pow (sqClassHom _) _ 2] at h1
    exact h1
  have hk : k = 2 * (k / 2) + k % 2 := by omega
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    show SqClass.mk (primeUnit P96 q3) ^ k = 1
    rw [hk, h, add_zero, _root_.zpow_mul, hsq, _root_.one_zpow]
  · right
    show SqClass.mk (primeUnit P96 q3) ^ k = _
    rw [hk, h, _root_.zpow_add, _root_.zpow_mul, hsq, _root_.one_zpow, one_mul, zpow_one]

theorem primeOf_eq_two_of_ne_q3 (p : P96) (hpq : p ≠ q3) : primeOf p.1 = 2 := by
  rcases mem_P96_iff.mp p.2 with h | h
  · exact h
  · exfalso
    apply hpq
    apply Subtype.ext
    show p.1 = v3
    exact primeOf_injective (h.trans primeOf_v3.symm)

/-- **The $2$-adically automorphous numbers of $f$ have even order** (unconditional): $f = E \perp \langle 18\rangle$
at $2$ with $E$ even unimodular, so the glue lemma applies. -/
@[kb "conwaysloane1999" "Ch. 15, §9.6, p. 392 (example: p = 2, the automorphous numbers are units)"]
theorem theta2_even (v : HeightOneSpectrum (𝓞 ℚ)) (hp2 : primeOf v = 2)
    (A : (v.adicCompletion ℚ)ˣ) (hA : A ∈ localSpinorNormGroup (csQ A96) A96_nondeg v stdLat) :
    ∃ k : ℤ, Valued.v (A : v.adicCompletion ℚ) = exp (2 * k) := by
  have hv2 := valued_two_of_primeOf hp2
  have hE : (A96.submatrix Fin.castSucc Fin.castSucc).det = 3 := by
    rw [Matrix.det_fin_two]; decide
  refine even_log_of_wallCore A96_symm (by rw [A96_det]; norm_num) hv2
    (fun S hS hSA hdet m P R hf => Glue.exists_sq_valued_wallDet_glue (n := 2) A96 9 A96_symm
      (by decide) (by decide) (by simpa using valued_nine_of_primeOf hp2) ?_ (by decide) hv2 S hS hSA hdet hf) A hA
  rw [hE]
  have := valued_intCast_eq_one v 3 (by rw [show Rat.HeightOneSpectrum.natGenerator v = 2 from hp2]; norm_num)
  simpa using this

open scoped Classical in
/-- $(u_-)_3$: the family with $-1$ (a non-residue mod $3$) at $3$ and $1$ at $2$ is not in the spinor kernel. -/
theorem mulSingle_neg_one_not_mem :
    (Pi.mulSingle q3 (-1) : CasselsR P96) ∉ casselsST (csQ A96) A96_nondeg stdLat P96 := by
  classical
  refine not_mem_casselsST_of_qClass (csQ A96) A96_nondeg stdLat P96 (by norm_num) q3
    (fun A hA => theta3_le A hA) ?_ ?_ ?_ ?_
  · -- the prime `2`: automorphous numbers have even order
    intro p hpq A hA
    obtain ⟨k, hk⟩ := theta2_even p.1 (primeOf_eq_two_of_ne_q3 p hpq) A hA
    have hord : ordP P96 p A = -k * 2 := by
      rw [ordP, hk, log_exp]; ring
    have e : casselsDiag P96 (natGenUnit p.1 ^ ordP P96 p A) q3 =
        (casselsDiag P96 (natGenUnit p.1 ^ (-k)) q3) ^ 2 := by
      rw [hord, _root_.zpow_mul, map_zpow, Pi.pow_apply]
      exact zpow_ofNat _ 2
    rw [e, (SqClass.mk_eq_one_iff _).mpr ⟨_, rfl⟩]
    exact Subgroup.one_mem _
  · rw [casselsJ_A96, map_one, Pi.one_apply]
    exact Subgroup.one_mem _
  · intro p
    by_cases hp : p = q3
    · subst hp; simp
    · rw [Pi.mulSingle_eq_of_ne hp]; simp
  · rw [Pi.mulSingle_eq_same]
    intro hmem
    rcases mem_zpowers_q3 hmem with h | h
    · apply not_isSquare_neg_one_v3
      rw [← sqClassOf_eq_one_iff (by norm_num : (-1 : F3) ≠ 0), sqClassOf_of_ne_zero (by norm_num),
        show Units.mk0 (-1 : F3) (by norm_num) = -1 from Units.ext (by simp)]
      exact h
    · have h' : sqClassOf (-1 : F3) = sqClassOf (3 : F3) := by
        rw [sqClassOf_of_ne_zero (by norm_num), show Units.mk0 (-1 : F3) (by norm_num) = -1 from Units.ext (by simp)]
        exact h.trans sqClass_primeUnit_q3
      have hm : sqClassOf ((-1 : F3) * 3⁻¹) = 1 := by
        rw [sqClassOf_mul (by norm_num) (by norm_num), h', ← sqClassOf_mul (by norm_num) (by norm_num),
          mul_inv_cancel₀ three_ne_zero, sqClassOf_one]
      refine not_isSquare_of_valued_eq_exp_odd (k := 0) ?_ ((sqClassOf_eq_one_iff (by norm_num)).mp hm)
      rw [map_mul, map_inv₀, Valuation.map_neg, map_one, valued_v3_three, one_mul, ← WithZero.exp_neg]
      norm_num

/-- **Conway–Sloane §9.6, the example** (p. 393): *the genus of $f$ contains two distinct spinor genera*. Here: the
genus of $\mathbb Z^3$ (with the form $f$) contains a lattice $M$ not in its (proper) spinor genus. **Unconditional**:
the $3$-adic bound is `theta3_le`, the $2$-adic one ("$2\cdot$unit is not $2$-adically automorphous") is `theta2_even`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.6, p. 393 (example: two spinor genera)"]
theorem example96_two_spinorGenera :
    ∃ M : Lat ℚ 3, SameGenus (csQ A96) (stdLat : Lat ℚ 3).1 M.1 ∧
      ¬ SameProperSpinorGenus (csQ A96) stdLat M :=
  exists_not_sameProperSpinorGenus (csQ A96) A96_nondeg stdLat P96 (by norm_num)
    (casselsCond_std (by norm_num) _ A96_nondeg P96 (primeSet_spec A96_symm (by rw [A96_det]; norm_num)))
    mulSingle_neg_one_not_mem

/-- **The genus of the §9.6 form has more than one class**: the lattice $M$ of `example96_two_spinorGenera` is not
the image of $\mathbb Z^3$ under any isometry of $(\mathbb Q^3, f)$ (the swap of the first two coordinates is an
improper integral automorph). **Unconditional.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.6, p. 393 (example: two spinor genera, hence more than one class)"]
theorem example96_two_classes :
    ∃ M : Lat ℚ 3, SameGenus (csQ A96) (stdLat : Lat ℚ 3).1 M.1 ∧
      ∀ σ : orthGroup (csQ A96) ℚ, glImage (σ : GL (Fin 3) ℚ) (stdLat : Lat ℚ 3).1 ≠ M.1 := by
  obtain ⟨M, hM, hnot⟩ := example96_two_spinorGenera
  obtain ⟨α, hdet, hαL⟩ := exists_improper_swap A96 A96_symm 0 1 (by decide)
    (fun i j => by fin_cases i <;> fin_cases j <;> decide)
  exact ⟨M, hM, not_isometric_of_not_sameProperSpinorGenus (csQ A96) A96_nondeg stdLat hnot hdet hαL⟩

end QuadFormsKB.ConwaySloane
