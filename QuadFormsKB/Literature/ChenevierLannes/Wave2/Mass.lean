/-
# Chenevier–Lannes: the mass of $X_n$ for $n = 8, 16, 24$

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §1.1, p. 1 (the Minkowski–Siegel–Smith mass formula, cited), and
the mass formula of Conway–Sloane 1988 (`conwaysloane1988`, (2), p. 263), proved unconditionally in this library
(`ConwaySloane.Mass.mass_eq_stdMass_mul`). Printed page numbers.

**Layer.** An even unimodular lattice $L$ is recorded by its integral form $Q = q_L$ (`EvenUnimodular.lean`); its norm
form $x \mapsto x \cdot x = 2Q(x)$ is `LocalDensity.ofMatrixZ Q.hessian = 2 • Q` (`ofMatrixZ_hessian`), the form whose
Gram matrix is the Hessian $H$ of $Q$. The mass formula of the library is stated for forms `ofMatrixZ A`. The mass
`Siegel.mass (2 • Q)` is $\sum 1/|O(L')|$ over the classes $L'$ of the genus of $2Q$, and $O(2Q) = O(Q)$
(`Binary.aut_smul`).

**Proves** (all unconditional):
- `alphaTwo_hessian_eight`, `alphaTwo_hessian_sixteen`, `alphaTwo_hessian_twentyFour`: the $2$-adic density
  $\alpha_2(H)$ of the Gram matrix of an even unimodular lattice of dimension $8, 16, 24$
  (`ConwaySloane.Mass.Two.Base.alphaP_evenUnimodular`);
- `mass_two_smul_eq`: the working form of the mass formula for an even unimodular lattice: only the prime $2$ enters;
- `mass_two_smul_eight`: $\mathrm{Mass} = 1/696729600$ ($= 1/|W(E_8)|$) for $n = 8$;
- `mass_two_smul_sixteen`: $\mathrm{Mass} = 691/277667181515243520000$ for $n = 16$;
- `mass_two_smul_twentyFour`: $\mathrm{Mass} = 1027637932586061520960267/129477933340026851560636148613120000000$ for
  $n = 24$.
These are the classical values $\frac{|B_{n/2}|}{n}\prod_{j=1}^{n/2-1}\frac{|B_{2j}|}{4j}$ of the Minkowski–Siegel–Smith
mass formula for even unimodular lattices.
-/
import QuadFormsKB.Literature.ChenevierLannes.Classification
import QuadFormsKB.Literature.ConwaySloane.Mass.StdForm
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicBase
import QuadFormsKB.Literature.ConwaySloane.Mass.StandardMass
import QuadFormsKB.Binary.SiegelNonPrimitive

open Matrix Real

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.ConwaySloane.Mass

variable {n : ℕ}

/-! ### The norm form $2Q$ -/

/-- The norm form $2Q$ of a positive definite form is positive definite. -/
theorem posDef_two_smul {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) : IntQF.PosDef ((2 : ℤ) • Q) := by
  intro x hx
  rw [Binary.eval_smul]
  have := hQ x hx
  omega

/-- The Hessian of an integral form has even diagonal ($H_{ii} = 2a_{ii}$). -/
theorem evenDiag_hessian (Q : QuadForm ℤ n) : Two.EvenDiag Q.hessian := fun i => by
  unfold QuadForm.hessian
  simp only [Matrix.add_apply, Matrix.transpose_apply]
  exact ⟨Q.coeff i i, by ring⟩

/-- **The working form of the mass formula for an even unimodular lattice**: since $\det H = 1$, only the prime $2$
enters, and
$$\mathrm{Mass}(2Q) = \mathrm{std}(n, 1)\,\frac{1}{\alpha_2(H)\,\mathrm{std}_2(n, 1)}.$$
From `ConwaySloane.Mass.mass_eq_stdMass_mul` (Conway–Sloane (2), unconditional). -/
theorem mass_two_smul_eq {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) (hn : 3 ≤ n) :
    Siegel.mass ((2 : ℤ) • Q) = stdMass n 1 * ((alphaP 2 Q.hessian)⁻¹ / (stdP 2 n 1 : ℝ)) := by
  have hA : Q.hessian.IsSymm := hessian_isSymm Q
  have hpd : IntQF.PosDef (LocalDensity.ofMatrixZ Q.hessian) := by
    rw [ofMatrixZ_hessian]; exact posDef_two_smul hQ.posDef
  have h := mass_eq_stdMass_mul hn hA hpd
  rw [ofMatrixZ_hessian] at h
  rw [h, hQ.det_one]
  have hpf : (2 * (1 : ℤ)).natAbs.primeFactors = {2} := by
    rw [show (2 * (1 : ℤ)).natAbs = 2 by norm_num, Nat.Prime.primeFactors Nat.prime_two]
  rw [hpf, Finset.prod_singleton]
  unfold pMassDensity
  rw [hQ.det_one]
  simp

/-! ### The $2$-adic densities -/

/-- $\alpha_2(H) = 2^8 \cdot 2\,(1 - 2^{-4})\prod_{i=1}^{3}(1 - 2^{-2i})$ for an even unimodular lattice of dimension $8$. -/
theorem alphaTwo_hessian_eight {Q : QuadForm ℤ 8} (hQ : IsEvenUnimodular Q) :
    alphaP 2 Q.hessian = (2 : ℝ) ^ 8 * (2 * (1 - ((2 : ℝ) ^ 4)⁻¹) *
      ∏ i ∈ Finset.range 3, (1 - ((2 : ℝ) ^ (2 * (i + 1)))⁻¹)) := by
  have h := Two.Base.alphaP_evenUnimodular (n := 8) (j := 3) (k := 0) rfl (hessian_isSymm Q)
    (evenDiag_hessian Q) (by rw [hQ.det_one]; norm_num)
  rw [h]
  norm_num

/-- $\alpha_2(H)$ for an even unimodular lattice of dimension $16$. -/
theorem alphaTwo_hessian_sixteen {Q : QuadForm ℤ 16} (hQ : IsEvenUnimodular Q) :
    alphaP 2 Q.hessian = (2 : ℝ) ^ 16 * (2 * (1 - ((2 : ℝ) ^ 8)⁻¹) *
      ∏ i ∈ Finset.range 7, (1 - ((2 : ℝ) ^ (2 * (i + 1)))⁻¹)) := by
  have h := Two.Base.alphaP_evenUnimodular (n := 16) (j := 7) (k := 0) rfl (hessian_isSymm Q)
    (evenDiag_hessian Q) (by rw [hQ.det_one]; norm_num)
  rw [h]
  norm_num

/-- $\alpha_2(H)$ for an even unimodular lattice of dimension $24$. -/
theorem alphaTwo_hessian_twentyFour {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q) :
    alphaP 2 Q.hessian = (2 : ℝ) ^ 24 * (2 * (1 - ((2 : ℝ) ^ 12)⁻¹) *
      ∏ i ∈ Finset.range 11, (1 - ((2 : ℝ) ^ (2 * (i + 1)))⁻¹)) := by
  have h := Two.Base.alphaP_evenUnimodular (n := 24) (j := 11) (k := 0) rfl (hessian_isSymm Q)
    (evenDiag_hessian Q) (by rw [hQ.det_one]; norm_num)
  rw [h]
  norm_num

/-! ### The values of $\zeta$ needed -/

/-- $B_8 = -1/30$. -/
theorem bernoulli_eight_val : bernoulli 8 = -1 / 30 := by
  have h3 : bernoulli' 3 = 0 := bernoulli'_eq_zero_of_odd ⟨1, rfl⟩ (by norm_num)
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd ⟨2, rfl⟩ (by norm_num)
  have h7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd ⟨3, rfl⟩ (by norm_num)
  have h6 : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    simp [Finset.sum_range_succ, Nat.choose, h3, h5, bernoulli'_two, bernoulli'_four]
    norm_num
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, h3, h5, h7, bernoulli'_two, bernoulli'_four, h6]
  norm_num

/-- $B_{12} = -691/2730$. -/
theorem bernoulli_twelve_val : bernoulli 12 = -691 / 2730 := by
  have h3 : bernoulli' 3 = 0 := bernoulli'_eq_zero_of_odd ⟨1, rfl⟩ (by norm_num)
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd ⟨2, rfl⟩ (by norm_num)
  have h7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd ⟨3, rfl⟩ (by norm_num)
  have h9 : bernoulli' 9 = 0 := bernoulli'_eq_zero_of_odd ⟨4, rfl⟩ (by norm_num)
  have h11 : bernoulli' 11 = 0 := bernoulli'_eq_zero_of_odd ⟨5, rfl⟩ (by norm_num)
  have h6 : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    simp [Finset.sum_range_succ, Nat.choose, h3, h5, bernoulli'_two, bernoulli'_four]
    norm_num
  have h8 : bernoulli' 8 = -1 / 30 := by
    rw [bernoulli'_def]
    simp [Finset.sum_range_succ, Nat.choose, h3, h5, h7, bernoulli'_two, bernoulli'_four, h6]
    norm_num
  have h10 : bernoulli' 10 = 5 / 66 := by
    rw [bernoulli'_def]
    simp [Finset.sum_range_succ, Nat.choose, h3, h5, h7, h9, bernoulli'_two, bernoulli'_four, h6, h8]
    norm_num
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, h3, h5, h7, h9, h11, bernoulli'_two, bernoulli'_four, h6, h8, h10]
  norm_num

/-- $\zeta_1(8) = (1 - 2^{-8})\,\zeta(8) = \tfrac{255}{256}\cdot\tfrac{\pi^8}{9450}$. -/
theorem zetaD_one_eight : zetaD 1 8 = 255 / 256 * (π ^ 8 / 9450) := by
  have h := zetaD_one_even (k := 4) (by norm_num)
  rw [show ((2 * 4 : ℕ) : ℝ) = 8 by norm_num, show 2 * 4 = 8 by norm_num, bernoulli_eight_val] at h
  rw [h]
  have h2 : (2 : ℝ) ^ (-(8 : ℝ)) = 1 / 256 := by
    rw [Real.rpow_neg (by norm_num), show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [h2]
  simp [Nat.factorial]
  ring

/-- $\zeta_1(12) = (1 - 2^{-12})\,\zeta(12) = \tfrac{4095}{4096}\cdot\tfrac{691\pi^{12}}{638512875}$. -/
theorem zetaD_one_twelve : zetaD 1 12 = 4095 / 4096 * (691 * π ^ 12 / 638512875) := by
  have h := zetaD_one_even (k := 6) (by norm_num)
  rw [show ((2 * 6 : ℕ) : ℝ) = 12 by norm_num, show 2 * 6 = 12 by norm_num, bernoulli_twelve_val] at h
  rw [h]
  have h2 : (2 : ℝ) ^ (-(12 : ℝ)) = 1 / 4096 := by
    rw [Real.rpow_neg (by norm_num), show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [h2]
  simp [Nat.factorial]
  ring

/-! ### The masses -/

/-- **The mass of the genus of $E_8$** is $1/696729600$: for every even unimodular lattice of dimension $8$, the mass
of the genus of its norm form $2Q$ is $1/696729600$ ($= 1/|W(E_8)|$). Unconditional (Conway–Sloane's formula (2), with
$\zeta_1(4) = \pi^4/96$). -/
@[kb "chenevierlannes2019" "§1.1, p. 1 (the Minkowski–Siegel–Smith mass formula, n = 8)"]
theorem mass_two_smul_eight {Q : QuadForm ℤ 8} (hQ : IsEvenUnimodular Q) :
    Siegel.mass ((2 : ℤ) • Q) = 1 / 696729600 := by
  rw [mass_two_smul_eq hQ (by norm_num), alphaTwo_hessian_eight hQ, stdMass_table_8,
    show ((-1 : ℤ) ^ 4 * 1) = 1 by norm_num, zetaD_one_four]
  have hs : (stdP 2 8 1 : ℝ) = 1 / (2 * (3 / 4) * (15 / 16) * (63 / 64)) := by
    norm_num [stdP, lowerProd, Finset.prod_range_succ]
  rw [hs]
  have hpi : (π : ℝ) ^ 4 ≠ 0 := by positivity
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  field_simp
  norm_num

/-- **The mass of the genus of $E_8 \oplus E_8$** (dimension $16$) is $691/277667181515243520000$. Unconditional. -/
@[kb "chenevierlannes2019" "§1.1, p. 1 (the Minkowski–Siegel–Smith mass formula, n = 16)"]
theorem mass_two_smul_sixteen {Q : QuadForm ℤ 16} (hQ : IsEvenUnimodular Q) :
    Siegel.mass ((2 : ℤ) • Q) = 691 / 277667181515243520000 := by
  rw [mass_two_smul_eq hQ (by norm_num), alphaTwo_hessian_sixteen hQ, stdMass_table_16,
    show ((-1 : ℤ) ^ 8 * 1) = 1 by norm_num, zetaD_one_eight]
  have hs : (stdP 2 16 1 : ℝ) = 1 / (2 * ∏ i ∈ Finset.range 7, (1 - ((2 : ℝ) ^ (2 * (i + 1)))⁻¹)) := by
    norm_num [stdP, lowerProd]
  rw [hs]
  have hpi : (π : ℝ) ^ 8 ≠ 0 := by positivity
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  field_simp
  norm_num

/-- **The mass of the genus of the Niemeier lattices** (dimension $24$) is
$1027637932586061520960267/129477933340026851560636148613120000000$. Unconditional. -/
@[kb "chenevierlannes2019" "§1.1, p. 1 (the Minkowski–Siegel–Smith mass formula, n = 24)"]
theorem mass_two_smul_twentyFour {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q) :
    Siegel.mass ((2 : ℤ) • Q) = 1027637932586061520960267 / 129477933340026851560636148613120000000 := by
  rw [mass_two_smul_eq hQ (by norm_num), alphaTwo_hessian_twentyFour hQ, stdMass_table_24,
    show ((-1 : ℤ) ^ 12 * 1) = 1 by norm_num, zetaD_one_twelve]
  have hs : (stdP 2 24 1 : ℝ) = 1 / (2 * ∏ i ∈ Finset.range 11, (1 - ((2 : ℝ) ^ (2 * (i + 1)))⁻¹)) := by
    norm_num [stdP, lowerProd]
  rw [hs]
  have hpi : (π : ℝ) ^ 12 ≠ 0 := by positivity
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  field_simp
  norm_num

end QuadFormsKB.ChenevierLannes
