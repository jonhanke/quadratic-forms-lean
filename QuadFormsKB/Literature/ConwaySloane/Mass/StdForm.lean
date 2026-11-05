/-
# Conway–Sloane 1988, §7: the standard $p$-mass and the standard mass as a value of (2)

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`). The form has an integral symmetric Gram matrix $A$ (`LocalDensity.ofMatrixZ A` has Hessian
$2A$), $d = \det A$, $s = \lceil n/2 \rceil$, $D = (-1)^s d$.

**Proves (all unconditional).**
* `pMassDensity_eq_stdP` (§7.r1, p. 266): for an odd prime $p \nmid d$, the counting $p$-mass $m_p(f)$ of §12
  (`pMassDensity`) is $\mathrm{std}_p(f)$ (`stdP`, (6)). Route: $\alpha_p = $ the library's self-density of the unimodular
  form over $\mathfrak o_v \cong \mathbb Z_p$ (via Hanke's $\beta_p = \tfrac12\alpha_p$ and $|2|_p = 1$), whose value is
  `DVR.localDensityForm_self_odd/even`. The library's character `chiDisc` is checked to be the Legendre symbol
  $\bigl(\tfrac{(-1)^{\lfloor n/2\rfloor}d}{p}\bigr)$ (`chiDisc_eq`; $\det H = 2^n d$ is divided by $2^n$), which for $n = 2s$
  is $\epsilon = (D/p)$ of (6). Requires $n \ge 1$ (for $n = 0$ the statement is false: $\mathrm{std}_p$ has a factor $2$).
* `stdMass_eq_tprod` (p. 266): for $n \ge 3$ and $d \ne 0$, $\prod_p 2\,\mathrm{std}_p$ converges (to
  $\prod_{i<s}\zeta(2i)\cdot\zeta_D(s)$, `hasProd_two_stdP`) and
  $\mathrm{std}(f) = 2\pi^{-n(n+1)/4}\prod_j\Gamma(j/2)\prod_p 2\,\mathrm{std}_p(f)$: the standard mass is the value of (2)
  when every $p$-mass takes its standard value. (At $p \mid 2d$ the Euler factor of $\zeta_D$ is $1$ as $\chi_D(p) = 0$; this
  is exactly (6) with $\epsilon = 0$.)
* `mass_eq_stdMass_mul` (§9, the working form of (2)): for $n \ge 3$ and $A$ positive definite,
  $m(f) = \mathrm{std}(f)\prod_{p \mid 2d} m_p(f)/\mathrm{std}_p(f)$.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.Density
import QuadFormsKB.Literature.ConwaySloane.Mass.StandardMass
import QuadFormsKB.Literature.ConwaySloane.Mass.PMass
import QuadFormsKB.Tamagawa.Classical.TernaryReg

open QuadFormsKB IsDedekindDomain NumberField Filter Real Finset

noncomputable section
namespace QuadFormsKB.ConwaySloane.Mass

variable {n : ℕ}

theorem hasProd_zeta_even {i : ℕ} (hi : 1 ≤ i) :
    HasProd (fun p : Nat.Primes => (1 - (((p : ℕ) : ℝ) ^ (2 * i))⁻¹)⁻¹) (riemannZeta (2 * (i : ℂ))).re := by
  have hs : 1 < (2 * (i : ℂ)).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im]
    have : (1 : ℝ) ≤ i := by exact_mod_cast hi
    linarith
  have h := _root_.riemannZeta_eulerProduct_hasProd hs
  have hterm : ∀ p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-(2 * (i : ℂ))))⁻¹ =
      (((1 - (((p : ℕ) : ℝ) ^ (2 * i))⁻¹)⁻¹ : ℝ) : ℂ) := fun p => by
    rw [show (2 * (i : ℂ)) = ((2 * i : ℕ) : ℂ) by push_cast; ring, Complex.cpow_neg, Complex.cpow_natCast]
    push_cast
    rfl
  simp_rw [hterm] at h
  unfold HasProd at h ⊢
  have h2 := (Complex.continuous_re.tendsto _).comp h
  refine h2.congr fun s => ?_
  simp only [Function.comp]
  rw [← Complex.ofReal_prod, Complex.ofReal_re]

theorem prod_range_Icc (m : ℕ) (f : ℕ → ℝ) : ∏ i ∈ range m, f (i + 1) = ∏ i ∈ Icc 1 m, f i := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.prod_range_succ, ih, Finset.prod_Icc_succ_top (by omega)]

theorem eps_eq {q : ℕ} (hq : q.Prime) (n : ℕ) (D : ℤ) :
    (if Odd n ∨ q = 2 then (0 : ℤ) else jacobiSym D q) = if n % 2 = 0 then chiD D q else 0 := by
  unfold chiD
  by_cases hn : n % 2 = 0
  · have hodd : ¬ Odd n := by rw [Nat.not_odd_iff_even]; exact Nat.even_iff.mpr hn
    by_cases h2 : q % 2 = 0
    · have : q = 2 := (Nat.Prime.eq_one_or_self_of_dvd hq 2 (Nat.dvd_of_mod_eq_zero h2)).resolve_left (by omega) |>.symm
      simp [hn, h2, this]
    · have : q ≠ 2 := fun h => h2 (by omega)
      simp [hn, h2, this, hodd]
  · have : Odd n := Nat.odd_iff.mpr (by omega)
    simp [hn, this]

theorem two_stdP_real {q : ℕ} (hq : q.Prime) (n : ℕ) (d : ℤ) :
    2 * (stdP q n d : ℝ) = (∏ i ∈ Icc 1 ((n + 1) / 2 - 1), (1 - ((q : ℝ) ^ (2 * i))⁻¹)⁻¹) *
      (if n % 2 = 0 then
        (1 - (chiD ((-1) ^ ((n + 1) / 2) * d) q : ℝ) * (q : ℝ) ^ (-(((n + 1) / 2 : ℕ) : ℝ)))⁻¹ else 1) := by
  have hp0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hX : (∏ i ∈ range ((n + 1) / 2 - 1), (1 - ((q : ℝ) ^ (2 * (i + 1)))⁻¹)) =
      (∏ i ∈ Icc 1 ((n + 1) / 2 - 1), (1 - ((q : ℝ) ^ (2 * i))⁻¹)⁻¹)⁻¹ := by
    rw [Finset.prod_inv_distrib, inv_inv]
    exact prod_range_Icc _ (fun i => 1 - ((q : ℝ) ^ (2 * i))⁻¹)
  have hlow : ((lowerProd (q : ℕ) ((n + 1) / 2 - 1) : ℚ) : ℝ) =
      (∏ i ∈ Icc 1 ((n + 1) / 2 - 1), (1 - ((q : ℝ) ^ (2 * i))⁻¹)⁻¹)⁻¹ := by
    rw [← hX]; unfold lowerProd; push_cast; rfl
  have hrp : ((q : ℝ) ^ (-(((n + 1) / 2 : ℕ) : ℝ))) = (((q : ℝ) ^ ((n + 1) / 2)))⁻¹ := by
    rw [Real.rpow_neg hp0.le, Real.rpow_natCast]
  unfold stdP
  simp only []
  rw [eps_eq hq]
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos hn, hrp]
    push_cast
    rw [hlow]
    field_simp
  · rw [if_neg hn, if_neg hn]
    push_cast
    rw [hlow]
    field_simp
    ring

/-- $\prod_p 2\,\mathrm{std}_p(f) = \prod_{i=1}^{s-1}\zeta(2i)\cdot\zeta_D(s)$ ($\zeta_D$ only for $n$ even), as a `HasProd`;
combine Euler products of $\zeta(2i)$ and (8). -/
@[kb "conwaysloane1988" "§7 (6)-(8), p. 266"]
theorem hasProd_two_stdP {n : ℕ} (hn : 3 ≤ n) {d : ℤ} (hd : d ≠ 0) :
    HasProd (fun p : Nat.Primes => 2 * (stdP p n d : ℝ))
      ((∏ i ∈ Icc 1 ((n + 1) / 2 - 1), (riemannZeta (2 * (i : ℂ))).re) *
        (if n % 2 = 0 then zetaD ((-1) ^ ((n + 1) / 2) * d) (((n + 1) / 2 : ℕ) : ℝ) else 1)) := by
  have h1 : HasProd (fun p : Nat.Primes => ∏ i ∈ Icc 1 ((n + 1) / 2 - 1), (1 - (((p : ℕ) : ℝ) ^ (2 * i))⁻¹)⁻¹)
      (∏ i ∈ Icc 1 ((n + 1) / 2 - 1), (riemannZeta (2 * (i : ℂ))).re) :=
    hasProd_prod fun i hi => hasProd_zeta_even (Finset.mem_Icc.mp hi).1
  have h2 : HasProd (fun p : Nat.Primes => if n % 2 = 0 then
        (1 - (chiD ((-1) ^ ((n + 1) / 2) * d) p : ℝ) * ((p : ℕ) : ℝ) ^ (-(((n + 1) / 2 : ℕ) : ℝ)))⁻¹ else 1)
      (if n % 2 = 0 then zetaD ((-1) ^ ((n + 1) / 2) * d) (((n + 1) / 2 : ℕ) : ℝ) else 1) := by
    by_cases he : n % 2 = 0
    · simp only [if_pos he]
      have hD : ((-1 : ℤ) ^ ((n + 1) / 2) * d) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hd
      have hs : (1 : ℝ) < (((n + 1) / 2 : ℕ) : ℝ) := by
        have : 2 ≤ (n + 1) / 2 := by omega
        exact_mod_cast this
      exact eulerProduct_zetaD hD hs
    · simp only [if_neg he]
      exact hasProd_one
  have h := h1.mul h2
  convert h using 1
  funext p
  exact two_stdP_real p.2 n d

section Part1

open QuadFormsKB.Tamagawa Hanke2011Structure Tamagawa.RatBridge

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝔬" => v.adicCompletionIntegers ℚ

theorem pv_eq_two_of_two_mem (h : (2 : 𝓞 ℚ) ∈ v.asIdeal) : pv v = 2 := by
  have h' := (RatHeadline3.intCast_mem_iff v 2).mp (by exact_mod_cast h)
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) Nat.prime_two).mp
    (by exact_mod_cast h')

theorem not_dvd_two (hp2 : pv v ≠ 2) : ¬ LocalDensity.NF.π v ∣ (2 : 𝔬) := fun h =>
  hp2 (pv_eq_two_of_two_mem v (by
    rwa [← map_ofNat (LocalDensity.NF.ι v), LocalDensity.NF.π_dvd_ι_iff] at h))

theorem norm_two_completion (hp2 : pv v ≠ 2) : ‖(2 : v.adicCompletion ℚ)‖ = 1 := by
  have := norm_coe_of_pow_dvd v (x := (2 : 𝔬)) (e := 0) (by simp) (by simpa using not_dvd_two v hp2)
  have e : (((2 : 𝔬) : v.adicCompletion ℚ)) = 2 := by norm_cast
  rw [e] at this
  simpa using this

theorem nondegenerate_up {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (hdet : A.det ≠ 0) :
    (up (LocalDensity.ofMatrixZ A)).Nondegenerate := by
  unfold QuadForm.Nondegenerate
  rw [QuadForm.hessian_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    hessian_det_ofMatrixZ hA]
  exact (map_ne_zero_iff _ (algebraMap ℤ (𝓞 ℚ)).injective_int).mpr (mul_ne_zero (pow_ne_zero _ two_ne_zero) hdet)

/-- For odd $p$: $\alpha_p(A)$ is the library's self-density of the form over $\mathfrak o_v \cong \mathbb Z_p$. -/
@[kb "conwaysloane1988" "§12, p. 281"]
theorem alphaP_eq_localDensityForm (hp2 : pv v ≠ 2) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (hdet : A.det ≠ 0) :
    alphaP (pv v) A = LocalDensity.DVR.localDensityForm (LocalDensity.NF.Qp v (up (LocalDensity.ofMatrixZ A)))
      (LocalDensity.NF.Qp v (up (LocalDensity.ofMatrixZ A))) (LocalDensity.NF.π v) := by
  have h1 := Hanke2005.hankeBeta_gramV v (up (LocalDensity.ofMatrixZ A)) (nondegenerate_up hA hdet)
  have h2 := localBeta_ofMatrixZ v hA hdet
  unfold localBeta at h2
  rw [h1, norm_two_completion v hp2, one_pow, one_mul] at h2
  rw [LocalDensity.NF.siegelDensity, if_pos rfl, LocalDensity.NF.localDensityForm_eq_completion] at h2
  linarith

theorem hessian_det_up {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) :
    (up (LocalDensity.ofMatrixZ A)).hessian.det = (((2 : ℤ) ^ n * A.det : ℤ) : 𝓞 ℚ) := by
  rw [QuadForm.hessian_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det, hessian_det_ofMatrixZ hA]
  simp

theorem two_res_ne_zero (hp2 : pv v ≠ 2) : (2 : IsLocalRing.ResidueField 𝔬) ≠ 0 := by
  have h := (LocalDensity.DVR.residue_eq_zero_iff_dvd (LocalDensity.NF.irreducible_π v) (a := (2 : 𝔬))).not.mpr
    (not_dvd_two v hp2)
  rw [show (2 : IsLocalRing.ResidueField 𝔬) = IsLocalRing.residue 𝔬 2 from (map_ofNat _ 2).symm]
  exact h

theorem not_dvd_hessian_det (hp2 : pv v ≠ 2) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (hpd : ¬ ((pv v : ℕ) : ℤ) ∣ A.det) :
    ¬ LocalDensity.NF.π v ∣ (LocalDensity.NF.Qp v (up (LocalDensity.ofMatrixZ A))).hessian.det := by
  apply LocalDensity.NF.π_not_dvd_det
  rw [hessian_det_up hA, RatHeadline3.intCast_mem_iff]
  intro h
  have hp := Rat.HeightOneSpectrum.prime_natGenerator v
  have hpz : Prime ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpz.dvd_or_dvd h with h1 | h1
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by
      have := hpz.dvd_of_dvd_pow h1
      exact Nat.prime_two)).mp (by exact_mod_cast hpz.dvd_of_dvd_pow h1))
  · exact hpd h1

/-- The library's discriminant character is the Legendre symbol of $(-1)^{\lfloor n/2\rfloor}\det A$ (the Gram
determinant, not $\det H$). -/
@[kb "conwaysloane1988" "(6), p. 266 (epsilon = (D/p))"]
theorem chiDisc_eq (hp2 : pv v ≠ 2) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) :
    LocalDensity.DVR.chiDisc (LocalDensity.NF.Qp v (up (LocalDensity.ofMatrixZ A))) =
      legendreSym (pv v) ((-1) ^ (n / 2) * A.det) := by
  have hF : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have h := Tamagawa.Classical.charNF_intCast_eq_legendreSym' v (((-1) ^ (n / 2) * A.det : ℤ))
  refine Eq.trans ?_ h
  unfold LocalDensity.DVR.chiDisc Siegel.charNF LocalDensity.DVR.resGramDet
  rw [LocalDensity.NF.det_hessian_Qp, hessian_det_up hA]
  congr 1
  have h2 := two_res_ne_zero v hp2
  push_cast
  simp only [map_mul, map_pow, map_neg, map_one, map_intCast, map_ofNat]
  field_simp

theorem one_sub_inv_pow_pos {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) :
    0 < 1 - (((p : ℝ)) ^ k)⁻¹ := by
  have h1 : (1 : ℝ) < (p : ℝ) ^ k := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact one_lt_pow₀ this hk
  have : ((p : ℝ) ^ k)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  linarith

theorem one_sub_chi_pos {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) (D : ℤ) :
    0 < 1 - (chiD D p : ℝ) * (((p : ℝ)) ^ m)⁻¹ := by
  have h1 : (1 : ℝ) < (p : ℝ) ^ m := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact one_lt_pow₀ this hm
  have h2 : ((p : ℝ) ^ m)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  have h3 : 0 < ((p : ℝ) ^ m)⁻¹ := by positivity
  have h4 := abs_chiD_le_one D p
  have h5 : (chiD D p : ℝ) * ((p : ℝ) ^ m)⁻¹ ≤ ((p : ℝ) ^ m)⁻¹ := by
    have := (abs_le.mp h4).2
    nlinarith
  linarith

theorem pMassDensity_eq_stdP_aux (hp2 : pv v ≠ 2) {A : Matrix (Fin n) (Fin n) ℤ} (hn : 1 ≤ n)
    (hA : A.IsSymm) (hdet : A.det ≠ 0) (hpd : ¬ ((pv v : ℕ) : ℤ) ∣ A.det) :
    pMassDensity (pv v) A = (stdP (pv v) n A.det : ℝ) := by
  have hp : (pv v).Prime := (Rat.HeightOneSpectrum.primesEquiv v).2
  have hval : padicValInt (pv v) A.det = 0 := by
    haveI : Fact (pv v).Prime := ⟨hp⟩
    exact padicValInt.eq_zero_of_not_dvd hpd
  have hα := alphaP_eq_localDensityForm v hp2 hA hdet
  have hπ := LocalDensity.NF.irreducible_π v
  have h2 := not_dvd_two v hp2
  have hdh := not_dvd_hessian_det v hp2 hA hpd
  have hq : ((LocalDensity.DVR.q 𝔬 : ℕ) : ℝ) = (pv v : ℝ) := by rw [q_eq]
  have hchi := chiDisc_eq v hp2 hA
  have key := two_stdP_real hp n A.det
  have hp0 : (0 : ℝ) < (pv v : ℝ) := by exact_mod_cast hp.pos
  have hodd : (pv v) % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  unfold pMassDensity
  rw [hval]
  simp only [Nat.cast_zero, zero_mul, zero_div, Real.rpow_zero]
  have hprodpos : ∀ M : ℕ, 0 < ∏ i ∈ Icc 1 M, (1 - (((pv v : ℕ) : ℝ) ^ (2 * i))⁻¹) :=
    fun M => Finset.prod_pos fun i hi => one_sub_inv_pow_pos hp (by have := (Finset.mem_Icc.mp hi).1; omega)
  have hinvprod : ∀ M : ℕ, (∏ i ∈ Icc 1 M, (1 - (((pv v : ℕ) : ℝ) ^ (2 * i))⁻¹)⁻¹) =
      (∏ i ∈ Icc 1 M, (1 - (((pv v : ℕ) : ℝ) ^ (2 * i))⁻¹))⁻¹ := fun M => by rw [Finset.prod_inv_distrib]
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hm : 1 ≤ m := by omega
    have hev : (2 * m) % 2 = 0 := by omega
    rw [LocalDensity.DVR.localDensityForm_self_even (LocalDensity.NF.π v) m hm _ hπ h2 hdh, hq, hchi] at hα
    rw [if_pos hev, hinvprod, show (2 * m + 1) / 2 - 1 = m - 1 by omega,
      show (2 * m + 1) / 2 = m by omega] at key
    have hcd : (legendreSym (pv v) ((-1) ^ (2 * m / 2) * A.det) : ℤ) = chiD ((-1) ^ m * A.det) (pv v) := by
      haveI : Fact (pv v).Prime := ⟨hp⟩
      rw [jacobiSym.legendreSym.to_jacobiSym, show 2 * m / 2 = m by omega]
      unfold chiD
      rw [if_neg (by omega)]
    rw [hcd] at hα
    have hrp : ((pv v : ℝ) ^ (-((m : ℕ) : ℝ))) = (((pv v : ℝ) ^ m))⁻¹ := by
      rw [Real.rpow_neg hp0.le, Real.rpow_natCast]
    rw [hrp] at key
    have e := prod_range_Icc (m - 1) (fun i => 1 - (((pv v : ℕ) : ℝ) ^ (2 * i))⁻¹)
    rw [e] at hα
    have P := hprodpos (m - 1)
    have X := one_sub_chi_pos hp (by omega : m ≠ 0) ((-1) ^ m * A.det)
    have hs : (stdP (pv v) (2 * m) A.det : ℝ) = (1 / 2) * ((∏ i ∈ Icc 1 (m - 1), (1 - (((pv v : ℕ) : ℝ) ^ (2 * i))⁻¹))⁻¹ *
        (1 - ((chiD ((-1) ^ m * A.det) (pv v) : ℤ) : ℝ) * (((pv v : ℕ) : ℝ) ^ m)⁻¹)⁻¹) := by linarith
    rw [hα, hs]
    field_simp
  · have hev : ¬ ((2 * m + 1) % 2 = 0) := by omega
    rw [LocalDensity.DVR.localDensityForm_self_odd (LocalDensity.NF.π v) m _ hπ h2 hdh, hq] at hα
    rw [if_neg hev, hinvprod, show (2 * m + 1 + 1) / 2 - 1 = m by omega] at key
    have e := prod_range_Icc m (fun i => 1 - (((pv v : ℕ) : ℝ) ^ (2 * i))⁻¹)
    rw [e] at hα
    have P := hprodpos m
    have hs : (stdP (pv v) (2 * m + 1) A.det : ℝ) =
        (1 / 2) * (∏ i ∈ Icc 1 m, (1 - (((pv v : ℕ) : ℝ) ^ (2 * i))⁻¹))⁻¹ := by linarith
    rw [hα, hs]
    field_simp

end Part1

/-- **§7.r1** (p. 266): for an odd prime $p \nmid \det A$ ($n \ge 1$, $A$ symmetric, $\det A \ne 0$) the $p$-mass
$m_p(f) = p^{s(n+1)/2}/\alpha_p(f)$ of §12 equals the standard $p$-mass $\mathrm{std}_p(f)$ of (6). -/
@[kb "conwaysloane1988" "§7.r1, p. 266"]
theorem pMassDensity_eq_stdP {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n)
    {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (hdet : A.det ≠ 0) (hpd : ¬ (p : ℤ) ∣ A.det) :
    pMassDensity p A = (stdP p n A.det : ℝ) := by
  obtain ⟨v, rfl⟩ : ∃ v : HeightOneSpectrum (𝓞 ℚ), pv v = p :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩, congrArg Subtype.val
      (Equiv.apply_symm_apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (⟨p, hp⟩ : Nat.Primes))⟩
  exact pMassDensity_eq_stdP_aux v hp2 hn hA hdet hpd

/-- $\mathrm{std}_p > 0$ for every prime $p$ and $n \ge 1$. -/
@[kb "conwaysloane1988" "(6), p. 266"]
theorem stdP_pos {q : ℕ} (hq : q.Prime) {n : ℕ} (hn : 1 ≤ n) (d : ℤ) : 0 < (stdP q n d : ℝ) := by
  have key := two_stdP_real hq n d
  have hp0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have h1 : 0 < ∏ i ∈ Icc 1 ((n + 1) / 2 - 1), (1 - ((q : ℝ) ^ (2 * i))⁻¹)⁻¹ :=
    Finset.prod_pos fun i hi => inv_pos.mpr (one_sub_inv_pow_pos hq (by have := (Finset.mem_Icc.mp hi).1; omega))
  have h2 : 0 < (if n % 2 = 0 then
        (1 - (chiD ((-1) ^ ((n + 1) / 2) * d) q : ℝ) * (q : ℝ) ^ (-(((n + 1) / 2 : ℕ) : ℝ)))⁻¹ else 1 : ℝ) := by
    split_ifs with h
    · rw [Real.rpow_neg hp0.le, Real.rpow_natCast]
      exact inv_pos.mpr (one_sub_chi_pos hq (by omega) _)
    · exact one_pos
  have := mul_pos h1 h2
  linarith

/-- **The standard mass is the value of (2) when every $p$-mass is standard** (p. 266): for $n \ge 3$, $d \ne 0$,
$\prod_p 2\,\mathrm{std}_p(f)$ is multipliable and
$\mathrm{std}(f) = 2\pi^{-n(n+1)/4}\prod_{j=1}^n\Gamma(j/2)\prod_p 2\,\mathrm{std}_p(f)$. -/
@[kb "conwaysloane1988" "§7 (7) and (2), p. 266"]
theorem stdMass_eq_tprod {n : ℕ} (hn : 3 ≤ n) {d : ℤ} (hd : d ≠ 0) :
    Multipliable (fun p : Nat.Primes => 2 * (stdP p n d : ℝ)) ∧
    stdMass n d = 2 * π ^ (-((n : ℝ) * (n + 1) / 4)) * (∏ j ∈ Finset.Icc 1 n, Real.Gamma ((j : ℝ) / 2)) *
      ∏' p : Nat.Primes, 2 * (stdP p n d : ℝ) := by
  have h := hasProd_two_stdP hn hd
  refine ⟨h.multipliable, ?_⟩
  rw [h.tprod_eq]
  simp only [stdMass, neg_div]
  ring

/-- **The working form of (2)** (§9): for $n \ge 3$ and $A$ symmetric positive definite,
$m(f) = \mathrm{std}(f)\prod_{p \mid 2\det A}\bigl(m_p(f)/\mathrm{std}_p(f)\bigr)$. -/
@[kb "conwaysloane1988" "§9, p. 270 (working form of (2))"]
theorem mass_eq_stdMass_mul {n : ℕ} (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (hQ : IntQF.PosDef (LocalDensity.ofMatrixZ A)) :
    Siegel.mass (LocalDensity.ofMatrixZ A) = stdMass n A.det *
      ∏ p ∈ (2 * A.det).natAbs.primeFactors, (pMassDensity p A / (stdP p n A.det : ℝ)) := by
  have hdpos := det_pos_of_posDef hA hQ
  have hd : A.det ≠ 0 := hdpos.ne'
  obtain ⟨hmul, hpos, hmass⟩ := mass_formula_two hn hA hQ
  obtain ⟨-, hstdEq⟩ := stdMass_eq_tprod hn hd
  have hstd := hasProd_two_stdP hn hd
  set d := A.det
  let r : Nat.Primes → ℝ := fun p => pMassDensity p A / (stdP p n d : ℝ)
  let S : Finset Nat.Primes := (2 * d).natAbs.primeFactors.subtype Nat.Prime
  have hr : HasProd r (∏ p ∈ S, r p) := by
    refine hasProd_prod_of_ne_finset_one fun p hp => ?_
    have hp' : ¬ ((p : ℕ) ∈ (2 * d).natAbs.primeFactors) := fun hmem => hp (Finset.mem_subtype.mpr hmem)
    have h2 : (p : ℕ) ≠ 2 := by
      intro h2
      apply hp'
      rw [Nat.mem_primeFactors]
      refine ⟨p.2, ?_, by simpa using hd⟩
      rw [h2]
      exact Int.natAbs_dvd_natAbs.mpr ⟨d, rfl⟩
    have hpd : ¬ ((p : ℕ) : ℤ) ∣ d := by
      intro h
      apply hp'
      rw [Nat.mem_primeFactors]
      refine ⟨p.2, ?_, by simpa using hd⟩
      exact Int.natCast_dvd.mp (h.mul_left 2 |>.trans (by rw [mul_comm]))
    simp only [r]
    rw [pMassDensity_eq_stdP p.2 h2 (by omega) hA hd hpd]
    exact div_self (stdP_pos p.2 (by omega) d).ne'
  have hprod := hstd.mul hr
  have hfun : (fun p : Nat.Primes => 2 * (stdP p n d : ℝ) * r p) = fun p : Nat.Primes => 2 * pMassDensity p A := by
    funext p
    have := (stdP_pos p.2 (by omega : 1 ≤ n) d).ne'
    simp only [r]
    field_simp
  simp only [hfun] at hprod
  have hS : ∏ p ∈ S, r p = ∏ p ∈ (2 * d).natAbs.primeFactors, (pMassDensity p A / (stdP p n d : ℝ)) := by
    exact Finset.prod_subtype_of_mem (p := Nat.Prime) (fun q : ℕ => pMassDensity q A / (stdP q n d : ℝ))
      (fun q hq => (Nat.mem_primeFactors.mp hq).1)
  rw [hmass, hprod.tprod_eq, hstdEq, hstd.tprod_eq, hS]
  ring

end QuadFormsKB.ConwaySloane.Mass
