/-
# Cassels, Ch. 11, Example 9: the genus of $x^2 + xy + 7y^2 + 3(z^2 + zt + t^2)$ has more than one spinor genus

J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 11, Example 9, p. 253 (`cassels1978`).

**Layer.** $f = x_0^2 + x_0x_1 + 7x_1^2 + 3(x_2^2 + x_2x_3 + x_3^2)$ (`ex9f`) on $\mathbb Z^4$ (`stdLat`), with Hessian
$A_9 = \begin{pmatrix}2&1\\1&14\end{pmatrix} \perp \begin{pmatrix}6&3\\3&6\end{pmatrix}$ of determinant $729 = 3^6$.
Cassels' group $G = R/ST$ of (3.15) for $P = \{2, 3\}$ (`P96`).

**Route.** $2f$ is the Conway–Sloane form `csQ A9` ($= x^{\mathsf T}A_9x$), and rescaling does not change the local
spinor norm groups (`localSpinorNormGroup_smul`).
* At $3$: the basis $e_0,\ e_1 - \tfrac12e_0,\ e_2,\ e_3 - \tfrac12e_2$ of $\mathbb Z_3^4$ is orthogonal with
  $Q$-values $2,\ 27/2,\ 6,\ 9/2$ (for $2f$), of pairwise distinct $3$-adic orders $0, 3, 1, 2$ and with all pairwise
  products in $\mathbb Q^{\times2} \cup 3\mathbb Q^{\times2}$; so $\theta(\Lambda_3) \subseteq \langle 3\rangle\mathbb Q_3^{\times2}$
  (`algorithm_odd_upper`).
* At $2$: $A_9$ is even unimodular ($\det = 729$ odd, even diagonal), so every $\theta(\Lambda_2)$ element has even order
  (Wall's formula `even_log_of_wallCore` and the core lemma `EvenUnimodular.exists_sq_valued_wallDet`).
* The form is positive definite ($j = 1$), and the family $-1$ at $3$, $1$ at $2$ is not in $ST$
  (`not_mem_casselsST_of_qClass`), hence $G \ne 1$ and $g^+ > 1$ (`one_lt_properSpinorGenusNumber_of_not_mem`).
-/
import QuadFormsKB.Literature.Cassels.Ch11Ex9_530
import QuadFormsKB.Literature.Cassels.Ch11Ex7Spinor530
import QuadFormsKB.Literature.Cassels.Ch11SpinorGeneraCount530
import QuadFormsKB.Literature.ConwaySloane.Section9Example96
import QuadFormsKB.Literature.ConwaySloane.Section9EvenUnimodular
import QuadFormsKB.Literature.ConwaySloane.Section9TwoSpinorGenera
import QuadFormsKB.Literature.ConwaySloane.Section9Group

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11Ex4

open QuadFormsKB QuadFormsKB.Lattices QuadFormsKB.ConwaySloane

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- The rational form of Example 9: $f$ of `ex9f` over $\mathbb Q$. -/
abbrev ex9Q : QuadForm ℚ 4 := ex9f.map (Int.castRingHom ℚ)

/-- The Hessian $A_9$ of `ex9f`. -/
def A9 : Matrix (Fin 4) (Fin 4) ℤ := !![2, 1, 0, 0; 1, 14, 0, 0; 0, 0, 6, 3; 0, 0, 3, 6]

theorem A9_symm : A9ᵀ = A9 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem A9_det : A9.det = 729 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, A9, Matrix.det_fin_three, Matrix.submatrix]
  rfl

theorem hessian_ex9f : ex9f.hessian = A9 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [QuadForm.hessian, ex9f, QuadForm.ofUpper, A9]

theorem hessian_det_ex9f : ex9f.hessian.det = 729 := by rw [hessian_ex9f, A9_det]

theorem ex9Q_nondeg : ex9Q.Nondegenerate :=
  Lattices.nondegenerate_map_of_det_ne_zero ex9f (by rw [hessian_det_ex9f]; norm_num)

/-- Helper: values of $f$ over a field of characteristic $0$ containing $\mathbb Q$ (here $\mathbb Q$). -/
theorem evalIn_ex9Q (x : Fin 4 → ℚ) :
    ex9Q.evalIn ℚ x = x 0 ^ 2 + x 0 * x 1 + 7 * x 1 ^ 2 + 3 * (x 2 ^ 2 + x 2 * x 3 + x 3 ^ 2) := by
  simp [QuadForm.evalIn, Fin.sum_univ_four, ex9f, QuadForm.ofUpper, QuadForm.map]
  ring

theorem A9_nondeg : (csQ A9).Nondegenerate := csQ_nondegenerate A9_symm (by rw [A9_det]; norm_num)

/-- **The form of Conway–Sloane type is twice the form of Example 9**: `csQ A9` $= 2f$ over $\mathbb Q$. -/
theorem csQ_A9_eq : csQ A9 = (2 : ℚ) • ex9Q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [csQ, Cassels.Ch8Ex2.gramForm, A9, ex9Q, QuadForm.map, ex9f, QuadForm.ofUpper] <;> norm_num

theorem localSpinorNormGroup_congr9 {Q Q' : QuadForm ℚ 4} (e : Q = Q') (hQ : Q.Nondegenerate)
    (hQ' : Q'.Nondegenerate) (v : HeightOneSpectrum (𝓞 ℚ)) (L : Lat ℚ 4) :
    localSpinorNormGroup Q hQ v L = localSpinorNormGroup Q' hQ' v L := by
  subst e; rfl

/-- $\theta(\Lambda_v)$ of Example 9 equals that of `csQ A9`. Arguments: `v` the prime, `u` the unit. -/
theorem mem_theta_ex9_iff (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ) :
    u ∈ localSpinorNormGroup ex9Q ex9Q_nondeg v stdLat ↔
      u ∈ localSpinorNormGroup (csQ A9) A9_nondeg v stdLat := by
  have hQ' : ((2 : ℚ) • ex9Q).Nondegenerate := by rw [← csQ_A9_eq]; exact A9_nondeg
  rw [localSpinorNormGroup_congr9 csQ_A9_eq A9_nondeg hQ' v stdLat,
    localSpinorNormGroup_smul ex9Q_nondeg two_ne_zero hQ' v stdLat]

/-! ### The $3$-adic upper bound -/

local notation "F3" => v3.adicCompletion ℚ

/-- The change of basis $e_0$, $e_1 - \tfrac12e_0$, $e_2$, $e_3 - \tfrac12e_2$ (orthogonal for $f$, invertible over
$\mathbb Z_3$). -/
def T9 : GL (Fin 4) ℚ :=
  ⟨!![1, -1/2, 0, 0; 0, 1, 0, 0; 0, 0, 1, -1/2; 0, 0, 0, 1], !![1, 1/2, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1/2; 0, 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_four],
    by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_four]⟩

theorem csQ_A9_hessian : (csQ A9).hessian = !![4, 2, 0, 0; 2, 28, 0, 0; 0, 0, 12, 6; 0, 0, 6, 12] := by
  rw [csQ, QuadForm.hessian_map, hessian_csForm A9_symm]
  ext i j; fin_cases i <;> fin_cases j <;> simp [A9]

theorem T9_gram : T9.valᵀ * (csQ A9).hessian * T9.val = Matrix.diagonal ![4, 27, 12, 9] := by
  rw [csQ_A9_hessian]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [T9, Matrix.mul_apply, Fin.sum_univ_four]

/-- The basis $\gamma$ of $\mathbb Z_3^4$. -/
def γ9 : GL (Fin 4) F3 := GeneralLinearGroup.map (algebraMap ℚ F3) T9

theorem locGram_γ9 : locGram (csQ A9) v3 γ9 = (Matrix.diagonal ![4, 27, 12, 9]).map (algebraMap ℚ F3) := by
  rw [← T9_gram]
  unfold locGram
  rw [γ9, glMap_val, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

theorem hγ9 : loc v3 (stdLat : Lat ℚ 4).1 = locAct v3 γ9 (std v3) := by
  have hT : ∀ i j, T9.val i j ∈ locSub v3 := by
    intro i j
    rw [mem_locSub]
    fin_cases i <;> fin_cases j <;> simp [T9, valued_v3_two]
  have hdet : T9.val.det = 1 ∨ T9.val.det = -1 :=
    Or.inl (by simp [T9, Matrix.det_succ_row_zero, Fin.sum_univ_succ])
  have h := loc_latOf_eq_std v3 T9 hT hdet
  rw [latOf, loc_glImage, loc_intVec] at h
  exact (loc_intVec v3).trans h.symm

theorem horth9 : ∀ k l, k ≠ l → locGram (csQ A9) v3 γ9 k l = 0 := by
  intro k l hkl
  rw [locGram_γ9, Matrix.map_apply, Matrix.diagonal_apply_ne _ hkl, map_zero]

/-- The values $Q(b_k) = 2, 27/2, 6, 9/2$ of the orthogonal basis (for $2f$). -/
theorem Qb9 (k : Fin 4) :
    (csQ A9).evalIn F3 (γ9.val *ᵥ Pi.single k 1) = algebraMap ℚ F3 (![2, 27/2, 6, 9/2] k) := by
  rw [evalIn_basis_eq, locGram_γ9, Matrix.map_apply, Matrix.diagonal_apply_eq]
  rw [show (2 : F3) = algebraMap ℚ F3 2 by simp, ← map_div₀]
  congr 1
  fin_cases k <;> norm_num

/-- **The $3$-adically automorphous numbers of Example 9**: every element of $\theta(\Lambda_3)$ (for $2f$) lies in
$\langle 3\rangle\mathbb Q_3^{\times 2}$. Unconditional (Theorem 18 at odd $p$, `algorithm_odd_upper`). -/
theorem theta3_le9 (A : F3ˣ) (hA : A ∈ localSpinorNormGroup (csQ A9) A9_nondeg v3 stdLat) :
    SqClass.mk A ∈ Subgroup.zpowers (SqClass.mk (primeUnit P96 q3)) := by
  refine algorithm_odd_upper A9_nondeg two_not_mem_v3 stdLat hγ9 horth9 _ ?_ ?_ hA
  · intro k l
    rw [Qb9, Qb9, ← map_mul]
    fin_cases k <;> fin_cases l
    · exact mem_zpowers_of_rat _ 2 (by norm_num) (Or.inl (by norm_num))
    · exact mem_zpowers_of_rat _ 3 (by norm_num) (Or.inr (by norm_num))
    · exact mem_zpowers_of_rat _ 2 (by norm_num) (Or.inr (by norm_num))
    · exact mem_zpowers_of_rat _ 3 (by norm_num) (Or.inl (by norm_num))
    · exact mem_zpowers_of_rat _ 3 (by norm_num) (Or.inr (by norm_num))
    · exact mem_zpowers_of_rat _ (27/2) (by norm_num) (Or.inl (by norm_num))
    · exact mem_zpowers_of_rat _ 9 (by norm_num) (Or.inl (by norm_num))
    · exact mem_zpowers_of_rat _ (9/2) (by norm_num) (Or.inr (by norm_num))
    · exact mem_zpowers_of_rat _ 2 (by norm_num) (Or.inr (by norm_num))
    · exact mem_zpowers_of_rat _ 9 (by norm_num) (Or.inl (by norm_num))
    · exact mem_zpowers_of_rat _ 6 (by norm_num) (Or.inl (by norm_num))
    · exact mem_zpowers_of_rat _ 3 (by norm_num) (Or.inr (by norm_num))
    · exact mem_zpowers_of_rat _ 3 (by norm_num) (Or.inl (by norm_num))
    · exact mem_zpowers_of_rat _ (9/2) (by norm_num) (Or.inr (by norm_num))
    · exact mem_zpowers_of_rat _ 3 (by norm_num) (Or.inr (by norm_num))
    · exact mem_zpowers_of_rat _ (9/2) (by norm_num) (Or.inl (by norm_num))
  · rintro ⟨k, l, hkl, heq⟩
    exfalso
    rw [Qb9, Qb9] at heq
    have v0 : Valued.v (algebraMap ℚ F3 2) = exp (0 : ℤ) := by rw [map_ofNat, valued_v3_two]; rfl
    have v1 : Valued.v (algebraMap ℚ F3 (27/2)) = exp (-3 : ℤ) := by
      rw [map_div₀, map_ofNat, map_ofNat, map_div₀, valued_v3_two, div_one,
        show (27 : F3) = 3 ^ 3 by norm_num, map_pow, valued_v3_three, ← WithZero.exp_nsmul]
      rfl
    have v2 : Valued.v (algebraMap ℚ F3 6) = exp (-1 : ℤ) := by
      rw [show (6 : ℚ) = 2 * 3 by norm_num, map_mul, map_ofNat, map_ofNat, map_mul, valued_v3_two, valued_v3_three,
        one_mul]
    have v3' : Valued.v (algebraMap ℚ F3 (9/2)) = exp (-2 : ℤ) := by
      rw [map_div₀, map_ofNat, map_ofNat, map_div₀, valued_v3_two, div_one,
        show (9 : F3) = 3 ^ 2 by norm_num, map_pow, valued_v3_three, ← WithZero.exp_nsmul]
      rfl
    fin_cases k <;> fin_cases l <;> simp_all [exp_injective.eq_iff, eq_comm (a := (1 : ℤᵐ⁰))]

/-! ### The $2$-adic upper bound -/

/-- **The $2$-adically automorphous numbers of Example 9 have even order** (unconditional): at $2$ the form is even
unimodular, so Wall's formula and the core lemma `EvenUnimodular.exists_sq_valued_wallDet` apply. -/
theorem theta2_even9 (v : HeightOneSpectrum (𝓞 ℚ)) (hp2 : primeOf v = 2)
    (A : (v.adicCompletion ℚ)ˣ) (hA : A ∈ localSpinorNormGroup (csQ A9) A9_nondeg v stdLat) :
    ∃ k : ℤ, Valued.v (A : v.adicCompletion ℚ) = exp (2 * k) := by
  have hv2 := valued_two_of_primeOf hp2
  have hdetv : Valued.v ((A9.det : ℤ) : v.adicCompletion ℚ) = 1 := by
    rw [A9_det]
    have := valued_intCast_eq_one v 729 (by rw [show Rat.HeightOneSpectrum.natGenerator v = 2 from hp2]; norm_num)
    simpa using this
  refine even_log_of_wallCore A9_symm (by rw [A9_det]; norm_num) hv2
    (fun S hS hSA hdet m P R hf => EvenUnimodular.exists_sq_valued_wallDet A9 A9_symm hdetv
      (fun i => by fin_cases i <;> decide) S hS hSA hf) A hA

/-! ### Positive definiteness and the condition (3.7) -/

theorem not_isIndefinite_ex9Q : ¬ IsIndefinite ex9Q := by
  rintro ⟨w, y, hy0, hy⟩
  have hw : w.IsReal := IsTotallyReal.isReal w
  let ψ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hy' : y 0 ^ 2 + y 0 * y 1 + 7 * y 1 ^ 2 + 3 * (y 2 ^ 2 + y 2 * y 3 + y 3 ^ 2) = 0 := by
    rw [← hy]
    simp [QuadForm.evalIn, QuadForm.map, ex9f, QuadForm.ofUpper, Fin.sum_univ_four]
    ring
  have h0 := congrArg ψ hy'
  simp only [map_add, map_mul, map_pow, map_ofNat, map_zero] at h0
  set a := ψ (y 0)
  set b := ψ (y 1)
  set c := ψ (y 2)
  set d := ψ (y 3)
  have e1 : (2 * a + b) ^ 2 = 0 := by nlinarith [sq_nonneg (2 * a + b), sq_nonneg b, sq_nonneg (2 * c + d), sq_nonneg d]
  have e2 : b ^ 2 = 0 := by nlinarith [sq_nonneg (2 * a + b), sq_nonneg b, sq_nonneg (2 * c + d), sq_nonneg d]
  have e3 : (2 * c + d) ^ 2 = 0 := by nlinarith [sq_nonneg (2 * a + b), sq_nonneg b, sq_nonneg (2 * c + d), sq_nonneg d]
  have e4 : d ^ 2 = 0 := by nlinarith [sq_nonneg (2 * a + b), sq_nonneg b, sq_nonneg (2 * c + d), sq_nonneg d]
  have hb : b = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp e2
  have hd : d = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp e4
  have ha : a = 0 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.mp e1
    rw [hb] at this; linarith
  have hc : c = 0 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.mp e3
    rw [hd] at this; linarith
  apply hy0
  funext i
  fin_cases i
  · show y 0 = 0; exact ψ.injective (by rw [map_zero]; exact ha)
  · show y 1 = 0; exact ψ.injective (by rw [map_zero]; exact hb)
  · show y 2 = 0; exact ψ.injective (by rw [map_zero]; exact hc)
  · show y 3 = 0; exact ψ.injective (by rw [map_zero]; exact hd)

theorem casselsJ_ex9Q : casselsJ ex9Q = 1 := by
  simp [casselsJ, not_isIndefinite_ex9Q]

/-- Cassels' condition (3.7) for $P = \{2, 3\}$ (`P96`): away from $2, 3$ the lattice is unimodular (Lemma 3.3). -/
theorem ex9_cond :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ P96 → ∀ u : (v.adicCompletion ℚ)ˣ,
      u ∈ localSpinorNormGroup ex9Q ex9Q_nondeg v stdLat ↔ IsUnitSqClass v (SqClass.mk u) := by
  refine casselsCond_std (by norm_num) ex9f ex9Q_nondeg P96 fun v hv hd => hv ?_
  rw [hessian_det_ex9f] at hd
  have hp := Rat.HeightOneSpectrum.prime_natGenerator v
  have hd' : primeOf v ∣ 2 * 3 ^ 6 := by
    have : ((primeOf v : ℕ) : ℤ) ∣ ((2 * 3 ^ 6 : ℕ) : ℤ) := by simpa using hd
    exact_mod_cast this
  rcases (Nat.Prime.dvd_mul hp).mp hd' with h | h
  · exact mem_P96_iff.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
  · exact mem_P96_iff.mpr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)))

/-- Helper: the vectors of $\mathbb Z^4 \subseteq \mathbb Q^4$ are the integer vectors. -/
theorem mem_stdLat_iff9 (y : Fin 4 → ℚ) :
    y ∈ (stdLat : Lat ℚ 4).1 ↔ ∃ a : Fin 4 → ℤ, ∀ i, y i = (a i : ℚ) := by
  have intEquiv_alg : ∀ x : 𝓞 ℚ, algebraMap (𝓞 ℚ) ℚ x = ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) x : ℤ) : ℚ) := by
    intro x
    have : x = ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) x : ℤ) : 𝓞 ℚ) := by
      exact ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm_apply_apply x).symm.trans
        (map_intCast ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm) _)
    conv_lhs => rw [this]
    simp
  change y ∈ (intVec : Submodule (𝓞 ℚ) (Fin 4 → ℚ)) ↔ _
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := mem_intVec_iff_exists.mp hy
    exact ⟨fun i => Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) (x i), fun i => intEquiv_alg _⟩
  · rintro ⟨a, ha⟩
    refine mem_intVec_iff_exists.mpr ⟨fun i => (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm (a i), funext fun i => ?_⟩
    simp [ha]

/-- The lattice $\mathbb Z^4$ is integral for $f$. -/
theorem isIntegral_ex9Q : IsIntegral ex9Q (stdLat : Lat ℚ 4).1 := by
  intro x hx
  obtain ⟨a, ha⟩ := (mem_stdLat_iff9 x).mp hx
  refine ⟨(Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm (ex9f.eval a), ?_⟩
  have h : ex9Q.evalIn ℚ x = ((ex9f.eval a : ℤ) : ℚ) := by
    rw [evalIn_ex9Q, eval_ex9f]
    simp [ha]
  rw [h]
  simp

open scoped Classical in
/-- **The family $-1$ at $3$, $1$ at $2$ is not in $ST$** for Example 9. -/
theorem ex9_mulSingle_not_mem :
    (Pi.mulSingle q3 (-1) : CasselsR P96) ∉ casselsST ex9Q ex9Q_nondeg stdLat P96 := by
  classical
  refine not_mem_casselsST_of_qClass ex9Q ex9Q_nondeg stdLat P96 (by norm_num) q3
    (fun A hA => theta3_le9 A ((mem_theta_ex9_iff _ A).mp hA)) ?_ ?_ ?_ ?_
  · intro p hpq A hA
    obtain ⟨k, hk⟩ := theta2_even9 p.1 (primeOf_eq_two_of_ne_q3 p hpq) A ((mem_theta_ex9_iff _ A).mp hA)
    have hord : ordP P96 p A = -k * 2 := by
      rw [ordP, hk, log_exp]; ring
    have e : casselsDiag P96 (natGenUnit p.1 ^ ordP P96 p A) q3 =
        (casselsDiag P96 (natGenUnit p.1 ^ (-k)) q3) ^ 2 := by
      rw [hord, _root_.zpow_mul, map_zpow, Pi.pow_apply]
      exact zpow_ofNat _ 2
    rw [e, (SqClass.mk_eq_one_iff _).mpr ⟨_, rfl⟩]
    exact Subgroup.one_mem _
  · rw [casselsJ_ex9Q, map_one, Pi.one_apply]
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

/-- **Cassels, Ch. 11, Example 9** (p. 253), the spinor part: *the genus of
$f = x^2 + xy + 7y^2 + 3(z^2 + zt + t^2)$ contains more than one proper spinor genus*. Unconditional: $P = \{2, 3\}$
satisfies (3.7) (`ex9_cond`), the class of the family $(-1 \text{ at } 3, 1 \text{ at } 2)$ in $G = R/ST$ is nontrivial
(`ex9_mulSingle_not_mem`: $\theta(\Lambda_3) \subseteq \langle 3\rangle\mathbb Q_3^{\times2}$ by `theta3_le9`, the
$\theta(\Lambda_2)$ have even order by `theta2_even9`, $f$ is definite), and Theorem 3.1 gives $g^+ = |G| > 1$. -/
@[kb "cassels1978" "Ch. 11, Ex. 9, p. 253 (more than one spinor genus; proved)"]
theorem ex9_moreThanOneSpinorGenus :
    1 < Lattices.properSpinorGenusNumber (ex9f.map (Int.castRingHom ℚ)) (Lattices.stdLat : Lattices.Lat ℚ 4) :=
  one_lt_properSpinorGenusNumber_of_not_mem ex9Q ex9Q_nondeg stdLat P96 (by norm_num) ex9_cond isIntegral_ex9Q _
    ex9_mulSingle_not_mem

/-- **Cassels, Ch. 11, Example 9** (p. 253), the remaining open part as a smaller named statement: *every form in the
genus of $f$ = `ex9f` is integrally equivalent to $f$, to `ex9f₂` or to `ex9f₃`* ("determine all the classes in the
genus"; the three representatives are a reconstruction found by computer, see `Ex9Statement`). Field `classes`: for a
form `h` in the genus of $f$ (`SameGenus ex9f h`), `h` is equivalent to one of the three. *Not proved:* this is the
classification of a genus of positive definite quaternary forms of determinant $729$, which needs quaternary reduction
theory with a large finite check, or a mass computation. Everything else in `Ex9Statement` is proved
(`ex9Statement_of_classes`). -/
@[kb "cassels1978" "Ch. 11, Ex. 9, p. 253 (the classes of the genus; reconstruction, open)"]
structure Ex9Classes : Prop where
  /-- Every form of the genus of `ex9f` is equivalent to `ex9f`, `ex9f₂` or `ex9f₃`. -/
  classes : ∀ h : QuadForm ℤ 4, Siegel.SameGenus ex9f h →
    Siegel.IntEquiv ex9f h ∨ Siegel.IntEquiv ex9f₂ h ∨ Siegel.IntEquiv ex9f₃ h

/-- **Cassels, Ch. 11, Example 9** (p. 253), conditional only on the classification `Ex9Classes`: the named statement
`Ex9Statement` follows, all its other fields (more than one spinor genus, the genus memberships and the three
inequivalences) being proved here unconditionally. Argument `h`: the classification. -/
@[kb "cassels1978" "Ch. 11, Ex. 9, p. 253 (from the classification of the genus)"]
theorem ex9Statement_of_classes (h : Ex9Classes) : Ex9Statement where
  moreThanOneSpinorGenus := ex9_moreThanOneSpinorGenus
  sameGenus₂ := ex9_sameGenus₂
  sameGenus₃ := ex9_sameGenus₃
  not_equiv₁₂ := ex9_not_equiv₁₂
  not_equiv₁₃ := ex9_not_equiv₁₃
  not_equiv₂₃ := ex9_not_equiv₂₃
  classes := h.classes

end QuadFormsKB.Cassels.Ch11Ex4
