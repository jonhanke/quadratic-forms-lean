/-
# Conway–Sloane, Ch. 15, §9.7, (44): the forms attaining $d_0$

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.7, pp. 395–396
(`conwaysloane1999`), proof of Corollary 22: "for $n \ge 4$ the smallest determinant (for an indefinite form with more
than one class in its genus) is that of the form
$$\begin{pmatrix}2&3\\3&2\end{pmatrix} \oplus 5^2\begin{pmatrix}2&3\\3&2\end{pmatrix} \oplus \cdots \oplus
5^{2m}\begin{pmatrix}2&3\\3&2\end{pmatrix} \oplus 5^{2m+2}(2),$$
omitting the final term if $n$ is even. This determinant is $5^{\binom n2}$ if $n$ is even, $2\cdot5^{\binom n2}$ if $n$
is odd (44)."

**Formalization.** `A44 n` is the Gram matrix in $n$ variables (0-based indices): $A_{ij} = 25^{\lfloor i/2\rfloor}\cdot
(2 \text{ if } i = j, 3 \text{ otherwise})$ when $\lfloor i/2\rfloor = \lfloor j/2\rfloor$, and $0$ otherwise. For even $n$
these are the $n/2$ binary blocks $5^{2k}\begin{pmatrix}2&3\\3&2\end{pmatrix}$; for odd $n$ the last index has no
partner and gives the final term $5^{2m+2}(2)$. (The book's determinant is up to sign: $\det A_n = (-1)^{\lfloor n/2\rfloor}
\cdot 5^{\binom n2}\cdot 2^{n \bmod 2}$.)

**Proves**
* `T44_gram`: the change of basis $b_{2k} = e_{2k}$, $b_{2k+1} = e_{2k+1} - \tfrac32 e_{2k}$ (unipotent) diagonalizes
  the form over $\mathbb Q$ with $Q(b_i) = 25^{\lfloor i/2\rfloor}\cdot 2$ ($i$ even), $-\tfrac52\cdot25^{\lfloor i/2\rfloor}$
  ($i$ odd);
* `natAbs_det_A44` (**(44)**): $\lvert\det A_n\rvert = 5^{\binom n2}\cdot2^{n \bmod 2}$;
* `theta5_le` (unconditional): the $5$-adically automorphous numbers lie in $\langle 5\rangle\mathbb Q_5^{\times2}$
  (list (I) has unit parts $2$, $-\tfrac12$, non-residues mod $5$, and distinct orders; `algorithm_odd_upper`);
* `rootNorm44_two_odd` (unconditional): the $2$-adic root vectors have norms of odd order;
* `theta2_even44` (unconditional): the $2$-adically automorphous numbers have even order (for even $n$ the form is
  even unimodular at $2$, `even_log_of_evenUnimodular`; for odd $n$ it is $E \perp \langle 2\cdot 25^k\rangle$, the glue
  lemma `Glue.exists_sq_valued_wallDet_glue`; formerly derived from the named statement `Theorem18Dyadic`);
* `forms44_two_spinorGenera`, `forms44_two_classes` (**unconditional**, $n \ge 3$): the genus
  contains a lattice outside the spinor genus of $\mathbb Z^n$, not isometric to $\mathbb Z^n$; so the forms (44) have
  more than one class in their genus and attain the bound $d_0$ of Corollary 22 for $n \ge 4$ (the bound itself is
  `corollary22_uncond`). The obstruction is $(2)_5$: $\Delta_5(2)$ is not in the spinor kernel. The $2$-adic upper
  bound is needed: $\Delta_2(2u)$ would put $(2)_5$ in the kernel ($2$ is a non-residue mod $5$).
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Example96
import QuadFormsKB.Literature.Cassels.Ch9Sec8Int

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

/-- **The Gram matrix of (44)** in $n$ variables (see the module docstring). -/
def A44 (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if i.1 / 2 = j.1 / 2 then 25 ^ (i.1 / 2) * (if i = j then 2 else 3) else 0

theorem A44_symm (n : ℕ) : (A44 n)ᵀ = A44 n := by
  ext i j
  simp only [transpose_apply, A44]
  by_cases hij : i = j
  · subst hij; rfl
  · have h' : j ≠ i := Ne.symm hij
    by_cases h : j.1 / 2 = i.1 / 2
    · simp only [h, hij, h', ↓reduceIte]
    · simp only [h, Ne.symm h, ↓reduceIte]

/-- The diagonal values $Q(b_i)$ of the orthogonal basis. -/
def r44 (i : ℕ) : ℚ := 25 ^ (i / 2) * (if i % 2 = 0 then 2 else -5/2)

/-- The change of basis $b_{2k} = e_{2k}$, $b_{2k+1} = e_{2k+1} - \tfrac32e_{2k}$, as a matrix (columns $b_i$). -/
def T44 (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := fun k i =>
  if k = i then 1 else if i.1 % 2 = 1 ∧ k.1 + 1 = i.1 then -3/2 else 0

/-- Column sums against $T$: $\sum_k T_{ki}f_k = f_i - \tfrac32f_{i-1}$ ($i$ odd), $f_i$ ($i$ even). -/
theorem sum_T44 {n : ℕ} (f : Fin n → ℚ) (i : Fin n) :
    ∑ k, T44 n k i * f k = f i + if h : i.1 % 2 = 1 then -3/2 * f ⟨i.1 - 1, by omega⟩ else 0 := by
  have hsplit : ∀ k, T44 n k i * f k =
      (if k = i then f k else 0) + (if i.1 % 2 = 1 ∧ k.1 + 1 = i.1 then -3/2 * f k else 0) := by
    intro k
    unfold T44
    by_cases hk : k = i
    · subst hk; simp
    · have : ¬ (k.1 = i.1) := fun h => hk (Fin.ext h)
      simp only [hk, if_false, zero_add]
      split_ifs <;> ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _)]
  congr 1
  by_cases hi : i.1 % 2 = 1
  · rw [dif_pos hi]
    rw [Finset.sum_eq_single ⟨i.1 - 1, by omega⟩]
    · rw [if_pos ⟨hi, by simp; omega⟩]
    · intro k _ hk
      rw [if_neg]
      rintro ⟨-, h⟩
      exact hk (Fin.ext (by simp; omega))
    · simp
  · rw [dif_neg hi]
    exact Finset.sum_eq_zero fun k _ => by rw [if_neg (fun h => hi h.1)]

/-- The Hessian $H = 2A$ of the form of (44), over $\mathbb Q$. -/
theorem hessian_A44 (n : ℕ) (k l : Fin n) :
    (csQ (A44 n)).hessian k l = 2 * (if k.1 / 2 = l.1 / 2 then 25 ^ (k.1 / 2) * (if k = l then 2 else 3) else 0) := by
  rw [csQ, QuadForm.hessian_map, hessian_csForm (A44_symm n)]
  simp only [Matrix.map_apply, Matrix.smul_apply, A44, smul_eq_mul, eq_intCast, Int.cast_mul, Int.cast_ofNat]
  split_ifs <;> push_cast <;> ring

/-- **The orthogonal basis**: $T^{t}HT = \mathrm{diag}(2Q(b_i))$ with $Q(b_i) = $ `r44 i`. -/
theorem T44_gram (n : ℕ) :
    (T44 n)ᵀ * (csQ (A44 n)).hessian * T44 n = Matrix.diagonal fun i => 2 * r44 i.1 := by
  ext i j
  have hHT : ∀ k, ((csQ (A44 n)).hessian * T44 n) k j = (csQ (A44 n)).hessian k j +
      if h : j.1 % 2 = 1 then -3/2 * (csQ (A44 n)).hessian k ⟨j.1 - 1, by omega⟩ else 0 := by
    intro k
    rw [Matrix.mul_apply]
    simp_rw [mul_comm ((csQ (A44 n)).hessian k _)]
    exact sum_T44 _ j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp_rw [transpose_apply]
  rw [sum_T44 (fun k => ((csQ (A44 n)).hessian * T44 n) k j) i]
  simp only [hHT, hessian_A44, diagonal_apply, r44]
  obtain ⟨a, ha⟩ := i
  obtain ⟨b, hb⟩ := j
  simp only [Fin.mk.injEq]
  have key : ∀ c d : ℕ, c = d → (25 : ℚ) ^ c = 25 ^ d := fun c d h => by rw [h]
  split_ifs <;> first
    | (exfalso; omega)
    | (rw [key ((a - 1) / 2) (a / 2) (by omega)] <;> ring)
    | ring
    | (rw [key ((b - 1) / 2) (b / 2) (by omega)]; ring)
    | (rw [key ((a - 1) / 2) (b / 2) (by omega)]; ring)
    | (rw [key (a / 2) (b / 2) (by omega)]; ring)
    | (rw [key ((a - 1) / 2) (a / 2) (by omega), key (a / 2) (b / 2) (by omega)]; ring)
    | skip

theorem det_T44 (n : ℕ) : (T44 n).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · exact Finset.prod_eq_one fun i _ => by simp [T44]
  · intro i j hij
    have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
    have hv : ¬ (i.1 + 1 = j.1) := by
      have := Fin.lt_def.mp hij
      simp only [id] at this
      omega
    simp [T44, hne, hv]

theorem r44_mul_succ (n : ℕ) : r44 n * r44 (n + 1) = -5 * 25 ^ n := by
  unfold r44
  have hsum : (25 : ℚ) ^ (n / 2) * 25 ^ ((n + 1) / 2) = 25 ^ n := by
    rw [← pow_add]; congr 1; omega
  rcases Nat.even_or_odd n with he | ho
  · have h1 : n % 2 = 0 := Nat.even_iff.mp he
    have h2 : ¬ (n + 1) % 2 = 0 := by omega
    simp only [h1, h2, ↓reduceIte]
    calc (25 : ℚ) ^ (n / 2) * 2 * (25 ^ ((n + 1) / 2) * (-5 / 2))
        = -5 * (25 ^ (n / 2) * 25 ^ ((n + 1) / 2)) := by ring
      _ = -5 * 25 ^ n := by rw [hsum]
  · have h1 : ¬ n % 2 = 0 := by have := Nat.odd_iff.mp ho; omega
    have h2 : (n + 1) % 2 = 0 := by have := Nat.odd_iff.mp ho; omega
    simp only [h1, h2, ↓reduceIte]
    calc (25 : ℚ) ^ (n / 2) * (-5 / 2) * (25 ^ ((n + 1) / 2) * 2)
        = -5 * (25 ^ (n / 2) * 25 ^ ((n + 1) / 2)) := by ring
      _ = -5 * 25 ^ n := by rw [hsum]

theorem abs_prod_r44 (n : ℕ) :
    |∏ i ∈ Finset.range n, r44 i| = 5 ^ n.choose 2 * 2 ^ (n % 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp
    · simp [r44]
    · rw [Finset.prod_range_succ, Finset.prod_range_succ, mul_assoc, r44_mul_succ, abs_mul, ih n (by omega),
        abs_mul, abs_neg, abs_pow]
      have hc : (n + 2).choose 2 = n.choose 2 + 2 * n + 1 := by
        simp [Nat.choose_succ_succ, Nat.choose_one_right]; ring
      rw [hc, show (n + 2) % 2 = n % 2 by omega, pow_add, pow_add, pow_mul]
      norm_num
      ring

/-- $\det A_n = \prod_i Q(b_i)$ (over $\mathbb Q$). -/
theorem det_A44_eq_prod (n : ℕ) : ((A44 n).det : ℚ) = ∏ i : Fin n, r44 i.1 := by
  have h := congrArg Matrix.det (T44_gram n)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_T44, one_mul, mul_one, Matrix.det_diagonal,
    csQ, QuadForm.hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hessian_det_csForm (A44_symm n),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at h
  have h2 : (2 : ℚ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  exact mul_left_cancel₀ h2 h

/-- **Conway–Sloane (44)** (§9.7, p. 396): the determinant of the form is $5^{\binom n2}$ if $n$ is even and
$2\cdot5^{\binom n2}$ if $n$ is odd (in absolute value; the sign is $(-1)^{\lfloor n/2\rfloor}$). -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, (44), p. 396"]
theorem natAbs_det_A44 (n : ℕ) : (A44 n).det.natAbs = 5 ^ n.choose 2 * 2 ^ (n % 2) := by
  have h := abs_prod_r44 n
  rw [← Fin.prod_univ_eq_prod_range, ← det_A44_eq_prod] at h
  have : ((A44 n).det.natAbs : ℚ) = ((5 ^ n.choose 2 * 2 ^ (n % 2) : ℕ) : ℚ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, h]; push_cast; ring
  exact_mod_cast this


/-! ### The $5$-adic upper bound -/

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- The place of $\mathbb Q$ above $5$. -/
def v5 : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨5, by norm_num⟩

theorem natGenerator_v5 : Rat.HeightOneSpectrum.natGenerator v5 = 5 :=
  congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨5, by norm_num⟩)

local notation "F5" => v5.adicCompletion ℚ

theorem algebraMap_natGenUnit_v5 : algebraMap ℚ F5 ((natGenUnit v5 : ℚˣ) : ℚ) = 5 := by
  simp only [natGenUnit, Units.val_mk0, natGenerator_v5, map_natCast]; norm_num

theorem valued_v5_five : Valued.v (5 : F5) = exp (-1 : ℤ) := by
  have := valued_natGenUnit_self v5
  rwa [algebraMap_natGenUnit_v5] at this

theorem valued_v5_two : Valued.v (2 : F5) = 1 := by
  have := valued_intCast_eq_one v5 2 (by rw [natGenerator_v5]; norm_num)
  simpa using this

theorem two_not_mem_v5 : (2 : 𝓞 ℚ) ∉ v5.asIdeal := by
  rw [two_mem_iff_natGenerator, natGenerator_v5]; norm_num

/-- $-1$ is a square in $\mathbb Q_5$ ($-1/4 \equiv 1 \bmod 5$). -/
theorem isSquare_neg_one_v5 : IsSquare (-1 : F5) := by
  have h4 : Valued.v (4 : F5) = 1 := by
    rw [show (4 : F5) = 2 * 2 by norm_num, map_mul, valued_v5_two, one_mul]
  have hsq : IsSquare (-1 / 4 : F5) := by
    apply HN.isSquare_of_valued_sub_one_lt v5
    rw [show (-1 / 4 : F5) - 1 = -(5 / 4) by ring, Valuation.map_neg, map_div₀, valued_v5_five, h4, div_one,
      ← exp_zero]
    exact exp_lt_exp.mpr (by norm_num)
  obtain ⟨y, hy⟩ := hsq
  exact ⟨2 * y, by rw [show (2 * y) * (2 * y) = 4 * (y * y) by ring, ← hy]; ring⟩

local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- $2$ is not a square in $\mathbb Q_5$. -/
theorem not_isSquare_two_padic_five : ¬ IsSquare (2 : ℚ_[5]) := by
  rintro ⟨y, hy⟩
  have hn : ‖y‖ = 1 := by
    have h := congrArg norm hy
    rw [norm_mul] at h
    have h2 : ‖(2 : ℚ_[5])‖ = 1 := by
      have := (Padic.norm_natCast_eq_one_iff (p := 5) (n := 2)).mpr (by norm_num)
      simpa using this
    nlinarith [norm_nonneg y]
  let z : ℤ_[5] := ⟨y, hn.le⟩
  have hz : z * z = 2 := Subtype.ext (by show y * y = 2; exact hy.symm)
  have h := congrArg PadicInt.toZMod hz
  rw [map_mul, map_ofNat] at h
  revert h
  generalize PadicInt.toZMod z = w
  revert w
  decide

theorem not_isSquare_two_v5 : ¬ IsSquare (2 : F5) := by
  rintro ⟨y, hy⟩
  have hp5 : ((Rat.HeightOneSpectrum.primesEquiv v5 : Nat.Primes) : ℕ) = 5 := natGenerator_v5
  have key : ∀ (p : Nat.Primes), (p : ℕ) = 5 → ¬ IsSquare (2 : ℚ_[p]) := by
    rintro ⟨p, hp⟩ (rfl : p = 5)
    exact not_isSquare_two_padic_five
  refine key _ hp5 ⟨Rat.HeightOneSpectrum.adicCompletion.padicEquiv v5 y, ?_⟩
  rw [← map_mul, ← hy, map_ofNat]

/-- The orthogonal basis $T$ as an element of $\mathrm{GL}_n(\mathbb Q)$. -/
def T44GL (n : ℕ) : GL (Fin n) ℚ := Matrix.nonsingInvUnit (T44 n) (by rw [det_T44]; exact isUnit_one)

/-- The basis $\gamma$ of $\mathbb Z_5^n$. -/
def γ44 (n : ℕ) : GL (Fin n) F5 := GeneralLinearGroup.map (algebraMap ℚ F5) (T44GL n)

theorem locGram_γ44 (n : ℕ) :
    locGram (csQ (A44 n)) v5 (γ44 n) = (Matrix.diagonal fun i : Fin n => 2 * r44 i.1).map (algebraMap ℚ F5) := by
  rw [← T44_gram]
  unfold locGram
  rw [γ44, glMap_val, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rfl

theorem hγ44 (n : ℕ) : loc v5 (stdLat : Lat ℚ n).1 = locAct v5 (γ44 n) (std v5) := by
  have hT : ∀ i j, (T44GL n).val i j ∈ locSub v5 := by
    intro i j
    rw [mem_locSub]
    show Valued.v (algebraMap ℚ F5 (T44 n i j)) ≤ 1
    unfold T44
    split_ifs
    · simp
    · rw [map_div₀, map_neg, map_ofNat, map_ofNat, map_div₀, Valuation.map_neg, valued_v5_two, div_one]
      have := valued_intCast_eq_one v5 3 (by rw [natGenerator_v5]; norm_num)
      simp only [Int.cast_ofNat] at this
      rw [this]
    · simp
  have hdet : (T44GL n).val.det = 1 ∨ (T44GL n).val.det = -1 := Or.inl (det_T44 n)
  have h := loc_latOf_eq_std v5 (T44GL n) hT hdet
  rw [latOf, loc_glImage, loc_intVec] at h
  exact (loc_intVec v5).trans h.symm

theorem horth44 (n : ℕ) : ∀ k l, k ≠ l → locGram (csQ (A44 n)) v5 (γ44 n) k l = 0 := by
  intro k l hkl
  rw [locGram_γ44, Matrix.map_apply, Matrix.diagonal_apply_ne _ hkl, map_zero]

theorem Qb44 (n : ℕ) (k : Fin n) :
    (csQ (A44 n)).evalIn F5 ((γ44 n).val *ᵥ Pi.single k 1) = algebraMap ℚ F5 (r44 k.1) := by
  rw [evalIn_basis_eq, locGram_γ44, Matrix.map_apply, Matrix.diagonal_apply_eq, map_mul, map_ofNat]
  field_simp

theorem valued_r44 (i : ℕ) : Valued.v (algebraMap ℚ F5 (r44 i)) = exp (-(i : ℤ)) := by
  have h25 : Valued.v (algebraMap ℚ F5 25) = exp (-2 : ℤ) := by
    rw [show (25 : ℚ) = 5 ^ 2 by norm_num, map_pow, map_ofNat, map_pow, valued_v5_five, ← WithZero.exp_nsmul]
    rfl
  unfold r44
  rw [map_mul, map_mul, map_pow, map_pow, h25, ← WithZero.exp_nsmul]
  split_ifs with h
  · rw [map_ofNat, valued_v5_two, mul_one]
    congr 1; simp only [nsmul_eq_mul]; push_cast; omega
  · rw [map_div₀, map_neg, map_ofNat, map_ofNat, map_div₀, Valuation.map_neg, valued_v5_five, valued_v5_two,
      div_one, ← exp_add]
    congr 1; simp only [nsmul_eq_mul]; push_cast; omega


/-- Conway–Sloane's $\Pi$ (without $-1$) for the forms (44): the primes dividing $2\det H$. -/
abbrev P44 (n : ℕ) : Finset (HeightOneSpectrum (𝓞 ℚ)) := primeSet (2 * (Cassels.Ch8Ex2.gramForm (A44 n)).hessian.det)

theorem natAbs_two_hessian_det_A44 (n : ℕ) :
    (2 * (Cassels.Ch8Ex2.gramForm (A44 n)).hessian.det).natAbs = 2 ^ (n + 1 + n % 2) * 5 ^ n.choose 2 := by
  rw [hessian_det_csForm (A44_symm n), Int.natAbs_mul, Int.natAbs_mul, natAbs_det_A44, Int.natAbs_pow]
  simp only [Int.reduceAbs, Nat.cast_ofNat]
  ring

theorem mem_P44 {n : ℕ} {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∈ P44 n) : primeOf v = 2 ∨ primeOf v = 5 := by
  have hv' : v ∈ primeSet (2 * (Cassels.Ch8Ex2.gramForm (A44 n)).hessian.det) := hv
  rw [primeSet, Finset.mem_preimage, Nat.mem_primeFactors, natAbs_two_hessian_det_A44] at hv'
  obtain ⟨hp, hd, -⟩ := hv'
  rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h))

theorem v5_mem_P44 {n : ℕ} (hn : 2 ≤ n) : v5 ∈ P44 n := by
  show v5 ∈ primeSet _
  rw [primeSet, Finset.mem_preimage, Nat.mem_primeFactors, natAbs_two_hessian_det_A44, natGenerator_v5]
  refine ⟨by norm_num, Dvd.dvd.mul_left (dvd_pow_self 5 ?_) _, by positivity⟩
  have : 1 ≤ n.choose 2 := Nat.choose_pos hn
  omega

/-- The prime $5$ as an element of $\Pi$. -/
def q5 {n : ℕ} (hn : 2 ≤ n) : P44 n := ⟨v5, v5_mem_P44 hn⟩

theorem sqClass_primeUnit_q5 {n : ℕ} (hn : 2 ≤ n) : SqClass.mk (primeUnit (P44 n) (q5 hn)) = sqClassOf (5 : F5) := by
  rw [sqClassOf_of_ne_zero (by norm_num)]
  congr 1
  refine Units.ext ?_
  show algebraMap ℚ F5 ((natGenUnit v5 : ℚˣ) : ℚ) = 5
  exact algebraMap_natGenUnit_v5

theorem mem_zpowers_five {n : ℕ} (hn : 2 ≤ n) (r s : ℚ) (hs : s ≠ 0) (h : r = s ^ 2 ∨ r = -5 * s ^ 2) :
    sqClassOf (algebraMap ℚ F5 r) ∈ Subgroup.zpowers (SqClass.mk (primeUnit (P44 n) (q5 hn))) := by
  have hs' : algebraMap ℚ F5 s ≠ 0 := (map_ne_zero _).mpr hs
  rcases h with rfl | rfl
  · rw [map_pow, (sqClassOf_eq_one_iff (pow_ne_zero 2 hs')).mpr ⟨_, sq _⟩]
    exact Subgroup.one_mem _
  · have hm1 : sqClassOf (-1 : F5) = 1 := (sqClassOf_eq_one_iff (by norm_num)).mpr isSquare_neg_one_v5
    rw [map_mul, map_pow, map_neg, map_ofNat, sqClassOf_mul (by norm_num) (pow_ne_zero 2 hs'),
      (sqClassOf_eq_one_iff (pow_ne_zero 2 hs')).mpr ⟨_, sq _⟩, mul_one,
      show (-5 : F5) = -1 * 5 by ring, sqClassOf_mul (by norm_num) (by norm_num), hm1, one_mul,
      ← sqClass_primeUnit_q5 hn]
    exact Subgroup.mem_zpowers _

theorem r44_mul_r44 (k l : ℕ) :
    r44 k * r44 l = (2 * 5 ^ (k / 2 + l / 2)) ^ 2 ∨ r44 k * r44 l = -5 * (5 ^ (k / 2 + l / 2)) ^ 2 ∨
      r44 k * r44 l = (5 / 2 * 5 ^ (k / 2 + l / 2)) ^ 2 := by
  unfold r44
  have h25 : ∀ a b : ℕ, (25 : ℚ) ^ a * 25 ^ b = (5 ^ (a + b)) ^ 2 := fun a b => by
    rw [← pow_add, ← pow_mul, show (25 : ℚ) = 5 ^ 2 by norm_num, ← pow_mul]; ring_nf
  split_ifs with hk hl hl
  · left
    calc (25 : ℚ) ^ (k / 2) * 2 * (25 ^ (l / 2) * 2) = 4 * (25 ^ (k / 2) * 25 ^ (l / 2)) := by ring
      _ = _ := by rw [h25]; ring
  · right; left
    calc (25 : ℚ) ^ (k / 2) * 2 * (25 ^ (l / 2) * (-5 / 2)) = -5 * (25 ^ (k / 2) * 25 ^ (l / 2)) := by ring
      _ = _ := by rw [h25]
  · right; left
    calc (25 : ℚ) ^ (k / 2) * (-5 / 2) * (25 ^ (l / 2) * 2) = -5 * (25 ^ (k / 2) * 25 ^ (l / 2)) := by ring
      _ = _ := by rw [h25]
  · right; right
    calc (25 : ℚ) ^ (k / 2) * (-5 / 2) * (25 ^ (l / 2) * (-5 / 2)) = 25 / 4 * (25 ^ (k / 2) * 25 ^ (l / 2)) := by
          ring
      _ = _ := by rw [h25]; ring

/-- **The $5$-adically automorphous numbers of (44)** lie in $\langle 5\rangle\mathbb Q_5^{\times 2}$: list (I) is
$2\cdot 25^k$, $-\tfrac52\cdot25^k$ (the unit parts $2$, $-\tfrac12$ are non-residues mod $5$, the orders $0, 1, \dots,
n-1$ distinct), so the products of pairs have square unit parts. Unconditional (Theorem 18 at odd $p$). -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, (44), p. 396 (the 5-adically automorphous numbers)"]
theorem theta5_le {n : ℕ} (hn : 2 ≤ n) (A : F5ˣ) (hA : A ∈ localSpinorNormGroup (csQ (A44 n))
    (csQ_nondegenerate (A44_symm n) (by intro h; have := natAbs_det_A44 n; rw [h] at this; simp at this))
    v5 stdLat) :
    SqClass.mk A ∈ Subgroup.zpowers (SqClass.mk (primeUnit (P44 n) (q5 hn))) := by
  refine algorithm_odd_upper _ two_not_mem_v5 stdLat (hγ44 n) (horth44 n) _ ?_ ?_ hA
  · intro k l
    rw [Qb44, Qb44, ← map_mul]
    have h5 : (5 : ℚ) ^ (k.1 / 2 + l.1 / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
    rcases r44_mul_r44 k.1 l.1 with h | h | h
    · exact mem_zpowers_five hn _ _ (mul_ne_zero two_ne_zero h5) (Or.inl h)
    · exact mem_zpowers_five hn _ _ h5 (Or.inr h)
    · exact mem_zpowers_five hn _ _ (mul_ne_zero (by norm_num) h5) (Or.inl h)
  · rintro ⟨k, l, hkl, heq⟩
    exfalso
    rw [Qb44, Qb44, valued_r44, valued_r44] at heq
    have := exp_injective heq
    exact hkl (Fin.ext (by omega))


/-! ### The $2$-adic root vectors of (44) -/

section Two44

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F2" => v.adicCompletion ℚ

theorem valued_intCast_le_one_F2 (z : ℤ) : Valued.v ((z : ℤ) : F2) ≤ 1 := valued_intCast_le_one' v z

theorem valued_odd_F2 (hv : primeOf v = 2) (z : ℤ) (hz : ¬ (2 : ℤ) ∣ z) : Valued.v ((z : ℤ) : F2) = 1 :=
  valued_intCast_eq_one v z (by rw [show Rat.HeightOneSpectrum.natGenerator v = 2 from hv]; exact_mod_cast hz)

/-- Every coefficient of the form of (44) (in the upper-triangular convention of `QuadForm`) is even. -/
theorem coeff_A44_even (n : ℕ) (i j : Fin n) :
    ∃ z : ℤ, (Cassels.Ch8Ex2.gramForm (A44 n)).coeff i j = 2 * z := by
  have hs : A44 n j i = A44 n i j := congrFun (congrFun (A44_symm n) i) j
  simp only [Cassels.Ch8Ex2.gramForm, Matrix.of_apply]
  by_cases hij : i < j
  · rw [if_pos hij, hs]; exact ⟨A44 n i j, by ring⟩
  · rw [if_neg hij]
    by_cases he : i = j
    · subst he
      rw [if_pos rfl]
      exact ⟨25 ^ (i.1 / 2), by simp [A44]; ring⟩
    · rw [if_neg he]; exact ⟨0, by ring⟩

/-- The value as a double sum of the terms $t_{ij} = c_{ij}x_ix_j$ ($i \le j$). -/
theorem evalIn_A44 (n : ℕ) (x : Fin n → F2) :
    (csQ (A44 n)).evalIn F2 x = ∑ i, ∑ j, if i ≤ j then
      (((Cassels.Ch8Ex2.gramForm (A44 n)).coeff i j : ℤ) : F2) * x i * x j else 0 := by
  simp only [QuadForm.evalIn, csQ, QuadForm.map, Matrix.map_apply, eq_intCast, map_intCast]

/-- An index of a binary block has a partner; only the last index of an odd $n$ has none. -/
theorem eq_last_of_no_partner {n : ℕ} (i : Fin n) (h : ∀ j : Fin n, j ≠ i → j.1 / 2 ≠ i.1 / 2) :
    i.1 + 1 = n ∧ i.1 % 2 = 0 := by
  by_cases hi : i.1 % 2 = 1
  · exact absurd (show (i.1 - 1) / 2 = i.1 / 2 by omega)
      (h ⟨i.1 - 1, by omega⟩ (fun e => by have := congrArg Fin.val e; simp at this; omega))
  · refine ⟨?_, by omega⟩
    by_contra hn
    exact h ⟨i.1 + 1, by omega⟩ (fun e => by have := congrArg Fin.val e; simp at this) (by simp; omega)

/-- **The $2$-adic root vectors of (44) have norms of odd order** ($2\cdot$unit up to squares: the book's list (II)
for the type II blocks, and $q x = 2\cdot 25^{m+1}$ for the last term when $n$ is odd). Unconditional. -/
theorem rootNorm44_two_odd {n : ℕ} (hv : primeOf v = 2) {x : Fin n → F2}
    (hx : IsRootVector (csQ (A44 n)) stdLat v x) :
    ∃ k : ℤ, Valued.v ((csQ (A44 n)).evalIn F2 x) = exp (2 * k + 1) := by
  have hγ : loc v (stdLat : Lat ℚ n).1 = locAct v 1 (std v) := by rw [locAct_one]; exact loc_intVec v
  have hx' : IsRootVector (csQ (A44 n)) stdLat v ((1 : GL (Fin n) F2).val *ᵥ x) := by simpa using hx
  have ineq : ∀ i j, Valued.v (x ⬝ᵥ (locGram (csQ (A44 n)) v 1 *ᵥ Pi.single j 1)) * Valued.v (x i) ≤
      Valued.v ((csQ (A44 n)).evalIn F2 x) := fun i j => by
    have := rootVector_ineq_gen stdLat hγ hx' i j
    simpa only [Units.val_one, one_mulVec] using this
  have hQ0 : (csQ (A44 n)).evalIn F2 x ≠ 0 := hx.1
  have v2 : Valued.v (2 : F2) = exp (-1 : ℤ) := valued_two_of_primeOf hv
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso; apply hQ0; simp [QuadForm.evalIn]
    · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => Valued.v (x i)) hne
  set M := Valued.v (x i0) with hM
  have hle : ∀ i, Valued.v (x i) ≤ M := fun i => hi0 i (Finset.mem_univ _)
  have hM0 : M ≠ 0 := by
    intro h0
    apply hQ0
    have hx0 : x = 0 := funext fun i => (Valuation.zero_iff _).mp (le_antisymm (h0 ▸ hle i) zero_le)
    simp [hx0, QuadForm.evalIn]
  have hpos : (0 : ℤᵐ⁰) < M := zero_lt_iff.mpr hM0
  set T := exp (-1 : ℤ) * M ^ 2 with hT
  -- the terms of the value
  have hterm : ∀ i j, Valued.v (if i ≤ j then
      (((Cassels.Ch8Ex2.gramForm (A44 n)).coeff i j : ℤ) : F2) * x i * x j else 0) ≤
        exp (-1 : ℤ) * (Valued.v (x i) * Valued.v (x j)) := by
    intro i j
    split_ifs
    · obtain ⟨z, hz⟩ := coeff_A44_even n i j
      rw [hz, Int.cast_mul, Int.cast_ofNat, map_mul, map_mul, map_mul, v2, mul_assoc, mul_assoc]
      exact mul_le_mul_right (by simpa using mul_le_mul_left (valued_intCast_le_one_F2 z) _) _
    · simp
  -- upper bound
  have hup : Valued.v ((csQ (A44 n)).evalIn F2 x) ≤ T := by
    rw [evalIn_A44]
    refine Valuation.map_sum_le _ fun i _ => Valuation.map_sum_le _ fun j _ => (hterm i j).trans ?_
    rw [hT, sq]
    exact mul_le_mul_right (mul_le_mul' (hle i) (hle j)) _
  -- lower bound
  have hlow : T ≤ Valued.v ((csQ (A44 n)).evalIn F2 x) := by
    by_cases hA : ∃ i, Valued.v (x i) = M ∧ ∃ j : Fin n, j ≠ i ∧ j.1 / 2 = i.1 / 2
    · obtain ⟨i, hiM, j, hji, hb⟩ := hA
      have h := ineq i j
      have hsum : x ⬝ᵥ (locGram (csQ (A44 n)) v 1 *ᵥ Pi.single j 1) =
          2 * (25 : F2) ^ (j.1 / 2) * (3 * x i + 2 * x j) := by
        have hG : ∀ k l, locGram (csQ (A44 n)) v 1 k l = (((Cassels.Ch8Ex2.gramForm (A44 n)).hessian k l : ℤ) : F2) :=
          fun k l => locGram_one_int v _ k l
        simp only [dotProduct, mulVec, hG, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, if_true, hessian_csForm (A44_symm n), Matrix.smul_apply, smul_eq_mul, A44]
        rw [Fintype.sum_eq_add i j (Ne.symm hji)]
        · simp only [hb, if_true, if_neg (Ne.symm hji), Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
          ring
        · intro k ⟨hki, hkj⟩
          rw [if_neg]; · simp
          intro hk
          have : k.1 / 2 = i.1 / 2 := hk.trans hb
          -- `k` is in the block of `i` and `j`, which has only these two indices
          have hk1 : k.1 ≠ i.1 := fun e => hki (Fin.ext e)
          have hk2 : k.1 ≠ j.1 := fun e => hkj (Fin.ext e)
          have hij : i.1 ≠ j.1 := fun e => hji (Fin.ext e.symm)
          omega
      have hv3 : Valued.v (3 * x i + 2 * x j) = M := by
        have h3 : Valued.v (3 * x i) = M := by
          rw [map_mul, show (3 : F2) = ((3 : ℤ) : F2) by norm_num, valued_odd_F2 hv 3 (by norm_num), one_mul, hiM]
        have h2 : Valued.v (2 * x j) < Valued.v (3 * x i) := by
          rw [h3, map_mul, v2]
          calc exp (-1 : ℤ) * Valued.v (x j) ≤ exp (-1 : ℤ) * M := mul_le_mul_right (hle j) _
            _ < 1 * M := mul_lt_mul_of_pos_right (by rw [← exp_zero, exp_lt_exp]; norm_num) hpos
            _ = M := one_mul M
        rw [Valuation.map_add_eq_of_lt_left _ h2, h3]
      have h25 : Valued.v ((25 : F2) ^ (j.1 / 2)) = 1 := by
        rw [map_pow, show (25 : F2) = ((25 : ℤ) : F2) by norm_num, valued_odd_F2 hv 25 (by norm_num), one_pow]
      rw [hsum, map_mul, map_mul, v2, h25, mul_one, hv3, hiM] at h
      rw [hT, sq, ← mul_assoc]
      exact h
    · push Not at hA
      -- only the last index (of odd `n`) attains `M`, and it has no partner
      have hnp : ∀ j : Fin n, j ≠ i0 → j.1 / 2 ≠ i0.1 / 2 := hA i0 rfl
      obtain ⟨hl1, hl2⟩ := eq_last_of_no_partner i0 hnp
      have hlt : ∀ i, i ≠ i0 → Valued.v (x i) < M := by
        intro i hi
        refine lt_of_le_of_ne (hle i) fun hiM => ?_
        obtain ⟨h1, -⟩ := eq_last_of_no_partner i (hA i hiM)
        exact hi (Fin.ext (by omega))
      rw [evalIn_A44]
      -- split off the term `(i0, i0)`
      set t : Fin n → Fin n → F2 := fun i j => if i ≤ j then
        (((Cassels.Ch8Ex2.gramForm (A44 n)).coeff i j : ℤ) : F2) * x i * x j else 0 with ht
      have hsplit : ∑ i, ∑ j, t i j = t i0 i0 + ∑ i, ∑ j, (if i = i0 ∧ j = i0 then 0 else t i j) := by
        have : ∀ i j, t i j = (if i = i0 ∧ j = i0 then t i0 i0 else 0) + (if i = i0 ∧ j = i0 then 0 else t i j) := by
          intro i j
          by_cases h : i = i0 ∧ j = i0
          · obtain ⟨rfl, rfl⟩ := h; simp
          · simp [h]
        rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => this i j))]
        simp only [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single i0 (fun i _ hi => by simp [hi]) (by simp)]
        rw [Finset.sum_eq_single i0 (fun j _ hj => by simp [hj]) (by simp)]
        simp
      have hdiag : Valued.v (t i0 i0) = T := by
        have hc : (Cassels.Ch8Ex2.gramForm (A44 n)).coeff i0 i0 = 2 * 25 ^ (i0.1 / 2) := by
          simp [Cassels.Ch8Ex2.gramForm, A44]; ring
        simp only [ht, le_refl, ↓reduceIte, hc, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, map_mul, map_pow]
        rw [show (25 : F2) = ((25 : ℤ) : F2) by norm_num, valued_odd_F2 hv 25 (by norm_num), v2, one_pow,
          mul_one, hT, sq, mul_assoc]
      have hrest : Valued.v (∑ i, ∑ j, (if i = i0 ∧ j = i0 then 0 else t i j)) < T := by
        have hT0 : T ≠ 0 := mul_ne_zero exp_ne_zero (pow_ne_zero 2 hM0)
        refine Valuation.map_sum_lt _ hT0 fun i _ => Valuation.map_sum_lt _ hT0 fun j _ => ?_
        split_ifs with hij
        · simp only [map_zero]; exact zero_lt_iff.mpr hT0
        · by_cases hi : i = i0
          · have hj : j ≠ i0 := fun e => hij ⟨hi, e⟩
            -- the last index is the largest: `i0 ≤ j` fails
            have hnle : ¬ i ≤ j := fun h => by
              have h1 := Fin.le_def.mp h
              have h2 : j.1 < n := j.2
              rw [hi] at h1
              exact hj (Fin.ext (by omega))
            simp only [ht, hnle, ↓reduceIte, map_zero]
            exact zero_lt_iff.mpr hT0
          · by_cases hj : j = i0
            · -- `i < i0` and `i0` has no partner: the coefficient vanishes
              have hcoeff : (Cassels.Ch8Ex2.gramForm (A44 n)).coeff i j = 0 := by
                simp only [Cassels.Ch8Ex2.gramForm, Matrix.of_apply, A44]
                have hb : i.1 / 2 ≠ j.1 / 2 := by rw [hj]; exact hnp i hi
                have hij' : i ≠ j := by rw [hj]; exact hi
                simp [hb, Ne.symm hb, hij']
              simp only [ht, hcoeff, Int.cast_zero, zero_mul, ite_self, map_zero]
              exact zero_lt_iff.mpr hT0
            · refine (hterm i j).trans_lt ?_
              rw [hT, sq]
              refine mul_lt_mul_of_pos_left ?_ (zero_lt_iff.mpr exp_ne_zero)
              calc Valued.v (x i) * Valued.v (x j) ≤ Valued.v (x i) * M := mul_le_mul_right (hle j) _
                _ < M * M := mul_lt_mul_of_pos_right (hlt i hi) hpos
      rw [hsplit, Valuation.map_add_eq_of_lt_left _ (hdiag ▸ hrest), hdiag]
  have hval : Valued.v ((csQ (A44 n)).evalIn F2 x) = T := le_antisymm hup hlow
  refine ⟨WithZero.log M - 1, ?_⟩
  rw [hval, hT, ← exp_log hM0, ← WithZero.exp_nsmul, ← exp_add, log_exp]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

end Two44


/-! ### The forms (44) have more than one spinor genus -/

theorem A44_det_ne_zero (n : ℕ) : (A44 n).det ≠ 0 := by
  intro h; have := natAbs_det_A44 n; rw [h] at this; simp at this

theorem A44_nondeg (n : ℕ) : (csQ (A44 n)).Nondegenerate := csQ_nondegenerate (A44_symm n) (A44_det_ne_zero n)

theorem coeff_A44_00 {n : ℕ} (hn : 2 ≤ n) :
    (Cassels.Ch8Ex2.gramForm (A44 n)).coeff ⟨0, by omega⟩ ⟨0, by omega⟩ = 2 := by
  simp [Cassels.Ch8Ex2.gramForm, A44]

/-- The form of (44) is indefinite ($n \ge 2$): $f(e_0) = 2$, $f(e_0 - e_1) = -2$. -/
theorem isIndefinite_A44 {n : ℕ} (hn : 2 ≤ n) : IsIndefinite (csQ (A44 n)) := by
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have hc : ∀ i j : Fin n, (Cassels.Ch8Ex2.gramForm (A44 n)).coeff i j =
      if i < j then A44 n i j + A44 n j i else if i = j then A44 n i i else 0 := fun i j => rfl
  let x : Fin n → ℝ := Pi.single i0 1 - Pi.single i1 1
  let y : Fin n → ℝ := Pi.single i0 1
  have hy : (Cassels.Ch8Ex2.gramForm (A44 n)).evalIn ℝ y = 2 := by
    rw [QuadForm.evalIn, Finset.sum_eq_single i0, Finset.sum_eq_single i0]
    · simp [y, hc, A44, i0]
    · intro b _ hb; simp [y, Pi.single_apply, hb]
    · simp
    · intro b _ hb; exact Finset.sum_eq_zero fun c _ => by simp [y, Pi.single_apply, hb]
    · simp
  have hx : (Cassels.Ch8Ex2.gramForm (A44 n)).evalIn ℝ x = -2 := by
    have hxv : ∀ k, x k = (if k = i0 then 1 else 0) - (if k = i1 then 1 else 0) := fun k => by
      simp [x, Pi.single_apply]
    rw [QuadForm.evalIn, Fintype.sum_eq_add i0 i1 h01]
    · rw [Fintype.sum_eq_add i0 i1 h01, Fintype.sum_eq_add i0 i1 h01]
      · simp only [hxv, hc, A44, i0, i1, Fin.mk_lt_mk, Fin.mk.injEq, le_refl, if_true]
        norm_num
      · intro k ⟨hk0, hk1⟩; simp [hxv, hk0, hk1]
      · intro k ⟨hk0, hk1⟩; simp [hxv, hk0, hk1]
    · intro k ⟨hk0, hk1⟩
      exact Finset.sum_eq_zero fun c _ => by simp [hxv, hk0, hk1]
  exact isIndefinite_of_neg_pos _ x y (by rw [hx]; norm_num) (by rw [hy]; norm_num)

theorem casselsJ_A44 {n : ℕ} (hn : 2 ≤ n) : casselsJ (csQ (A44 n)) = -1 := by
  simp [casselsJ, isIndefinite_A44 hn]

theorem mem_zpowers_q5 {n : ℕ} (hn : 2 ≤ n) {c : SqClass ((q5 hn).1.adicCompletion ℚ)}
    (hc : c ∈ Subgroup.zpowers (SqClass.mk (primeUnit (P44 n) (q5 hn)))) :
    c = 1 ∨ c = SqClass.mk (primeUnit (P44 n) (q5 hn)) := by
  obtain ⟨k, rfl⟩ := hc
  have hsq : (SqClass.mk (primeUnit (P44 n) (q5 hn))) ^ (2 : ℤ) = 1 := by
    have h1 := (SqClass.mk_eq_one_iff (primeUnit (P44 n) (q5 hn) ^ 2)).mpr ⟨_, rfl⟩
    rw [zpow_ofNat]
    rw [show SqClass.mk (primeUnit (P44 n) (q5 hn) ^ 2) = SqClass.mk (primeUnit (P44 n) (q5 hn)) ^ 2 from
      map_pow (sqClassHom _) _ 2] at h1
    exact h1
  have hk : k = 2 * (k / 2) + k % 2 := by omega
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    show SqClass.mk (primeUnit (P44 n) (q5 hn)) ^ k = 1
    rw [hk, h, add_zero, _root_.zpow_mul, hsq, _root_.one_zpow]
  · right
    show SqClass.mk (primeUnit (P44 n) (q5 hn)) ^ k = _
    rw [hk, h, _root_.zpow_add, _root_.zpow_mul, hsq, _root_.one_zpow, one_mul, zpow_one]

theorem A44_even_diag (n : ℕ) (i : Fin n) : Even (A44 n i i) := by
  simp only [A44, if_true]
  exact ⟨25 ^ (i.1 / 2), by ring⟩

theorem valued_det_A44_even {v : HeightOneSpectrum (𝓞 ℚ)} (hp2 : primeOf v = 2) {n : ℕ} (hn : n % 2 = 0) :
    Valued.v (((A44 n).det : ℤ) : v.adicCompletion ℚ) = 1 := by
  refine valued_intCast_eq_one v _ ?_
  rw [show ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by rw [show
    Rat.HeightOneSpectrum.natGenerator v = 2 from hp2], Int.natCast_dvd, natAbs_det_A44, hn, pow_zero, mul_one]
  intro h
  have := (Nat.prime_two.dvd_of_dvd_pow h)
  norm_num at this

theorem A44_last (k : ℕ) (i : Fin (2 * k + 1)) (hi : i ≠ Fin.last (2 * k)) : A44 (2 * k + 1) i (Fin.last (2 * k)) = 0 := by
  have hi' : i.1 < 2 * k := lt_of_le_of_ne (Nat.lt_succ_iff.mp i.2) (fun h => hi (Fin.ext h))
  simp only [A44, Fin.val_last]
  rw [if_neg]
  omega

theorem A44_last_last (k : ℕ) : A44 (2 * k + 1) (Fin.last (2 * k)) (Fin.last (2 * k)) = 2 * 25 ^ k := by
  simp only [A44, Fin.val_last, if_true]
  rw [show 2 * k / 2 = k by omega]
  ring

theorem A44_submatrix (k : ℕ) : (A44 (2 * k + 1)).submatrix Fin.castSucc Fin.castSucc = A44 (2 * k) := by
  ext i j
  simp only [submatrix_apply, A44, Fin.coe_castSucc, Fin.castSucc_inj]

/-- **The $2$-adically automorphous numbers of the forms (44) have even order** (unconditional, every $n$). -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, (44), p. 396 (p = 2: the automorphous numbers have even order)"]
theorem theta2_even44 {n : ℕ} (v : HeightOneSpectrum (𝓞 ℚ)) (hp2 : primeOf v = 2)
    (A : (v.adicCompletion ℚ)ˣ) (hA : A ∈ localSpinorNormGroup (csQ (A44 n)) (A44_nondeg n) v stdLat) :
    ∃ k : ℤ, Valued.v (A : v.adicCompletion ℚ) = exp (2 * k) := by
  have hv2 := valued_two_of_primeOf hp2
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · exact even_log_of_evenUnimodular (A44_symm _) (A44_det_ne_zero _) hv2
      (valued_det_A44_even hp2 (by omega)) (A44_even_diag _) A hA
  · refine even_log_of_wallCore (A44_symm _) (A44_det_ne_zero _) hv2
      (fun S hS hSA hdet m P R hf => Glue.exists_sq_valued_wallDet_glue (n := 2 * k) (A44 (2 * k + 1)) (25 ^ k)
        (A44_symm _) (A44_last k) (A44_last_last k) ?_ ?_ (A44_even_diag _) hv2 S hS hSA hdet hf) A hA
    · refine valued_intCast_eq_one v _ ?_
      rw [show Rat.HeightOneSpectrum.natGenerator v = 2 from hp2]
      intro h
      have h' : (2 : ℤ) ∣ 25 := Int.Prime.dvd_pow' (by norm_num) h
      norm_num at h'
    · rw [A44_submatrix]
      exact valued_det_A44_even hp2 (by omega)

open scoped Classical in
/-- $(2)_5$ ($2$ is a non-residue mod $5$) is not in the spinor kernel of the forms (44), $n \ge 3$. -/
theorem mulSingle_two_not_mem {n : ℕ} (hn : 3 ≤ n) :
    (Pi.mulSingle (q5 (Nat.le_of_succ_le hn))
      (Units.mk0 (2 : (q5 (Nat.le_of_succ_le hn)).1.adicCompletion ℚ) two_ne_zero) : CasselsR (P44 n)) ∉
      casselsST (csQ (A44 n)) (A44_nondeg n) stdLat (P44 n) := by
  classical
  have hn2 : 2 ≤ n := Nat.le_of_succ_le hn
  refine not_mem_casselsST_of_qClass (csQ (A44 n)) (A44_nondeg n) stdLat (P44 n) hn (q5 hn2)
    (fun A hA => theta5_le hn2 A hA) ?_ ?_ ?_ ?_
  · intro p hpq A hA
    have hp2 : primeOf p.1 = 2 := by
      rcases mem_P44 p.2 with h | h
      · exact h
      · exfalso; apply hpq; apply Subtype.ext
        show p.1 = v5
        exact primeOf_injective (h.trans natGenerator_v5.symm)
    obtain ⟨k, hk⟩ := theta2_even44 p.1 hp2 A hA
    have hord : ordP (P44 n) p A = -k * 2 := by
      rw [ordP, hk, log_exp]; ring
    have e : casselsDiag (P44 n) (natGenUnit p.1 ^ ordP (P44 n) p A) (q5 hn2) =
        (casselsDiag (P44 n) (natGenUnit p.1 ^ (-k)) (q5 hn2)) ^ 2 := by
      rw [hord, _root_.zpow_mul, map_zpow, Pi.pow_apply]
      exact zpow_ofNat _ 2
    rw [e, (SqClass.mk_eq_one_iff _).mpr ⟨_, rfl⟩]
    exact Subgroup.one_mem _
  · rw [casselsJ_A44 hn2]
    have h1 : SqClass.mk (casselsDiag (P44 n) (-1 : ℚˣ) (q5 hn2)) = 1 := by
      have hval : ((casselsDiag (P44 n) (-1 : ℚˣ) (q5 hn2) : ((q5 hn2).1.adicCompletion ℚ)ˣ) :
          (q5 hn2).1.adicCompletion ℚ) = -1 := by
        rw [casselsDiag_apply]; simp
      obtain ⟨y, hy⟩ := isSquare_neg_one_v5
      have hy0 : y ≠ 0 := by rintro rfl; simp at hy
      exact (SqClass.mk_eq_one_iff _).mpr ⟨Units.mk0 y hy0, Units.ext (by rw [hval, Units.val_pow_eq_pow_val]; exact (sq y).trans hy.symm)⟩
    rw [h1]
    exact Subgroup.one_mem _
  · intro p
    by_cases hp : p = q5 hn2
    · subst hp
      simp only [Pi.mulSingle_eq_same]
      show Valued.v (2 : F5) = 1
      exact valued_v5_two
    · rw [Pi.mulSingle_eq_of_ne hp]; simp
  · rw [Pi.mulSingle_eq_same]
    intro hmem
    rcases mem_zpowers_q5 hn2 hmem with h | h
    · apply not_isSquare_two_v5
      rw [← sqClassOf_eq_one_iff (two_ne_zero : (2 : F5) ≠ 0), sqClassOf_of_ne_zero two_ne_zero]
      exact h
    · have h' : sqClassOf (2 : F5) = sqClassOf (5 : F5) := by
        rw [sqClassOf_of_ne_zero two_ne_zero]
        exact h.trans (sqClass_primeUnit_q5 hn2)
      have hm : sqClassOf ((2 : F5) * 5⁻¹) = 1 := by
        rw [sqClassOf_mul two_ne_zero (by norm_num), h', ← sqClassOf_mul (by norm_num) (by norm_num),
          mul_inv_cancel₀ (by norm_num : (5 : F5) ≠ 0), sqClassOf_one]
      refine not_isSquare_of_valued_eq_exp_odd (k := 0) ?_ ((sqClassOf_eq_one_iff (by norm_num)).mp hm)
      rw [map_mul, map_inv₀, valued_v5_two, valued_v5_five, one_mul, ← WithZero.exp_neg]
      norm_num

/-- **The forms (44) have more than one spinor genus** (Conway–Sloane §9.7, p. 396: they attain $d_0$, so their
genus contains more than one class): for $n \ge 3$ the genus of $\mathbb Z^n$ with the form (44) contains a lattice
$M$ not in its (proper) spinor genus. **Unconditional**: the $5$-adic bound is `theta5_le`, the $2$-adic one ("no
$2$-adically automorphous number has odd order") is `theta2_even44`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, (44), p. 396 (the forms attaining d₀ have two spinor genera)"]
theorem forms44_two_spinorGenera {n : ℕ} (hn : 3 ≤ n) :
    ∃ M : Lat ℚ n, SameGenus (csQ (A44 n)) (stdLat : Lat ℚ n).1 M.1 ∧
      ¬ SameProperSpinorGenus (csQ (A44 n)) stdLat M :=
  exists_not_sameProperSpinorGenus (csQ (A44 n)) (A44_nondeg n) stdLat (P44 n) hn
    (casselsCond_std (by omega) _ (A44_nondeg n) (P44 n) (primeSet_spec (A44_symm n) (A44_det_ne_zero n)))
    (mulSingle_two_not_mem hn)


theorem A44_swap {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    A44 n (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ i) (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ j) =
      A44 n i j := by
  have hdiv : ∀ k : Fin n, (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ k).1 / 2 = k.1 / 2 := by
    intro k
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1; simp
    · subst h2; simp
    · rfl
  simp only [A44, hdiv, (Equiv.swap _ _).injective.eq_iff]

/-- **The forms (44) have more than one class in their genus** ($n \ge 3$; Conway–Sloane §9.7, p. 396: they attain
$d_0$ of Corollary 22): the lattice $M$ of `forms44_two_spinorGenera` is not the image of $\mathbb Z^n$ under any
isometry (the swap of the first two coordinates is an improper integral automorph). **Unconditional.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, (44), p. 396 (the forms attaining d₀ have more than one class)"]
theorem forms44_two_classes {n : ℕ} (hn : 3 ≤ n) :
    ∃ M : Lat ℚ n, SameGenus (csQ (A44 n)) (stdLat : Lat ℚ n).1 M.1 ∧
      ∀ σ : orthGroup (csQ (A44 n)) ℚ, glImage (σ : GL (Fin n) ℚ) (stdLat : Lat ℚ n).1 ≠ M.1 := by
  obtain ⟨M, hM, hnot⟩ := forms44_two_spinorGenera hn
  obtain ⟨α, hdet, hαL⟩ := exists_improper_swap (A44 n) (A44_symm n) ⟨0, by omega⟩ ⟨1, by omega⟩
    (by simp [Fin.ext_iff]) (A44_swap (by omega))
  exact ⟨M, hM, not_isometric_of_not_sameProperSpinorGenus (csQ (A44 n)) (A44_nondeg n) stdLat hnot hdet hαL⟩

end QuadFormsKB.ConwaySloane
