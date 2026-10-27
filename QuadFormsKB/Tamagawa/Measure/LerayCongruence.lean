import QuadFormsKB.Tamagawa.Measure.LerayPadic
import QuadFormsKB.LocalDensity.FormDensityStab
import QuadFormsKB.Tamagawa.AlphaLawIndex

/-!
# Volumes of principal congruence subgroups for the gauge-form measure

$F_v$ any completion of a number field at a finite place (dyadic included), $Q_0$ a nondegenerate form over
$\mathcal O_F$ in $n$ variables, $Q = Q_0\otimes\mathfrak o_v$, $H$ its Hessian, $\pi^d \,\|\, \det H$, $q = N(v)$.
$\mu_v$ = `muLoc v Q₀ 1`, which is Weil's gauge-form measure $|dX/d\Phi|_v$ (`lerayApprox_eventually_eq`).

**Main theorem** (`muLoc_congSub_eq`): for $K_m = O(V)(F_v)\cap(1+\pi^mM_n(\mathfrak o_v))$ and $2d+1 \le j \le m$,
$$\mu_v(K_m) = q^{-(m+j)\,n(n-1)/2}\cdot\#\{Z \in M_n(\mathfrak o_v/\pi^j) : D_1Z \equiv 0 \bmod \pi^j\},$$
$D_1$ = the differential of $X\mapsto Q\circ X$ at $X = 1$ (the `formD Q 1`): $Z \mapsto (B_Q(e_i, Z_i),
B_Q(e_i,Z_l)+B_Q(Z_i,e_l))$, i.e. the coefficients of $Z^{\mathsf T}H + HZ$. So the gauge-form volume of a small
congruence subgroup is a *linear* count: the Lie algebra $\mathfrak{so}(Q)$ measured against $dX/d\Phi$.

*Proof.* Put $X = 1 + \pi^mZ$; then $Q\circ X = Q + \pi^m\tilde G(Z)$ with $\tilde G(Z) = D_1Z + \pi^m(Q\circ Z)$
(`formF_one_add`). So $(1+\pi^mM_n(\mathfrak o))\cap\Phi^{-1}(Q+\mathfrak p^{m+j})$ is the disjoint union of the boxes
$1 + \pi^m(\tilde Z + \pi^jM_n(\mathfrak o))$ over the solutions $Z$ of $\tilde G \equiv 0 \bmod \pi^j$
(`volM_ballOne_inter_thick`), and the Leray quotient at level $m+j$ is $\#S_j/q^{(m+j)n(n-1)/2}$. The map $\tilde G$
satisfies $\tilde G(Z + cW) = \tilde G(Z) + c\,D_{1+\pi^mZ}W + c^2\pi^m(Q\circ W)$, and $D_{1+\pi^m Z}$ has image
$\supseteq\pi^dR^{N}$ at every solution (`formD_surj`), so the counting Hensel lemma (`card_sol_succ_gen`, the
`card_sol_succ` with an arbitrary quadratic term) makes the quotients constant for $j \ge 2d+1$; the
`lerayApprox_ballOne_eventually` identifies the constant with $\mu_v(K_m)$; for $j \le m$ the term $\pi^m(Q\circ Z)$
vanishes mod $\pi^j$.

Sources: A. Weil, *Adeles and Algebraic Groups* (1982), §2.2 (gauge forms; volumes by counting mod $\mathfrak p^k$)
[unverified]; Siegel 1935, Hilfssatz 13 (stabilization) [unverified]; the counting Hensel lemma is the
(`FormDensityHensel.lean`, a multivariable form of Hanke 2004, Lemma 3.2).
-/

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Matrix

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ι κ : Type*}
variable [Finite (IsLocalRing.ResidueField R)] [Fintype ι] [Fintype κ]

/-- **Counting Hensel lemma, general quadratic term** (`card_sol_succ` with $c^2F(w)$ replaced by $c^2E(w)$ for an
arbitrary $E$; the proof is unchanged). If $F(\vec x + c\vec w) = F(\vec x) + c\,D_{\vec x}\vec w + c^2E(\vec w)$ with
$D_{\vec x}$ linear, $K \ge 2d+1$, and the image of $D_{\vec x}$ contains $\pi^dR^\kappa$ at every solution mod
$\pi^K$, then $\#S_{K+1}\,q^{|\kappa|} = q^{|\iota|}\,\#S_K$. -/
@[kb "siegel1935" "Hilfssatz 13 [unverified]"]
theorem card_sol_succ_gen (π : R) (hπ : Irreducible π) (F E : (ι → R) → (κ → R))
    (D : (ι → R) → (ι → R) →ₗ[R] (κ → R))
    (hF : ∀ x w (c : R), F (x + c • w) = F x + c • D x w + c ^ 2 • E w) (t : κ → R) (d K : ℕ)
    (hK : 2 * d + 1 ≤ K)
    (hD : ∀ x, (∀ j, π ^ K ∣ F x j - t j) → ∀ c, ∃ w, D x w = π ^ d • c) :
    Nat.card {x : ι → R ⧸ Ideal.span {π ^ (K + 1)} // ∀ j, π ^ (K + 1) ∣ F (liftI π (K + 1) x) j - t j} *
        q R ^ Fintype.card κ =
      q R ^ Fintype.card ι *
        Nat.card {x : ι → R ⧸ Ideal.span {π ^ K} // ∀ j, π ^ K ∣ F (liftI π K x) j - t j} := by
  classical
  have hπ0 := hπ.ne_zero
  set Sol : ℕ → (ι → R) → Prop := fun N x => ∀ j, π ^ N ∣ F x j - t j with hSol
  have hSolShift : ∀ N x y, Sol N x → Sol N (x + π ^ N • y) := by
    intro N x y hx j
    rw [hF]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show F x j + π ^ N * D x y j + (π ^ N) ^ 2 * E y j - t j =
      (F x j - t j) + π ^ N * (D x y j + π ^ N * E y j) by ring]
    exact dvd_add (hx j) (dvd_mul_right _ _)
  set a := K - d with ha
  have hKa : K = a + d := by omega
  set P : (ι → R) → Prop := fun x => ∃ y, Sol K (x + π ^ a • y) with hPdef
  have hP : ∀ x y, P x → P (x + π ^ a • y) := by
    rintro x y ⟨y', hy'⟩
    refine ⟨y' - y, ?_⟩
    convert hy' using 1
    funext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hKP : ∀ x, Sol K x → P x := fun x hx => ⟨0, by simpa using hx⟩
  have hK1K : ∀ x, Sol (K + 1) x → Sol K x := fun x hx j => (pow_dvd_pow π (Nat.le_succ K)).trans (hx j)
  obtain ⟨eK⟩ := fiberSigma π hπ0 a d K hKa.symm P (Sol K) hP hKP (hSolShift K)
  obtain ⟨eK1⟩ := fiberSigma π hπ0 a (d + 1) (K + 1) (by omega) P (Sol (K + 1)) hP
    (fun x hx => hKP x (hK1K x hx)) (hSolShift (K + 1))
  have := finite_vec (ι := ι) π hπ a
  have := finite_vec (ι := ι) π hπ d
  have := finite_vec (ι := ι) π hπ (d + 1)
  -- the per-class identity
  have hclass : ∀ c : {c : ι → R ⧸ Ideal.span {π ^ a} // P (liftI π a c)},
      Nat.card {y : ι → R ⧸ Ideal.span {π ^ (d + 1)} //
          Sol (K + 1) (liftI π a c.1 + π ^ a • liftI π (d + 1) y)} * q R ^ Fintype.card κ =
        q R ^ Fintype.card ι * Nat.card {y : ι → R ⧸ Ideal.span {π ^ d} //
          Sol K (liftI π a c.1 + π ^ a • liftI π d y)} := by
    rintro ⟨c, y0, hy0⟩
    set x0 := liftI π a c + π ^ a • y0 with hx0
    choose τ hτ using hy0
    obtain ⟨w0, hw0⟩ := hD x0 (fun j => ⟨τ j, hτ j⟩) τ
    have hexp : ∀ v : ι → R, liftI π a c + π ^ a • v = x0 + π ^ a • (v - y0) := by
      intro v; funext i; simp only [hx0, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    have hFexp : ∀ (v : ι → R) (j : κ), F (liftI π a c + π ^ a • v) j - t j =
        π ^ K * τ j + π ^ a * D x0 (v - y0) j + (π ^ a) ^ 2 * E (v - y0) j := by
      intro v j
      rw [hexp, hF]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination hτ j
    have hpow : ∀ e, π ^ (a + e) = π ^ a * π ^ e := fun e => pow_add π a e
    -- the condition mod π^K
    have hcondK : ∀ v : ι → R, Sol K (liftI π a c + π ^ a • v) ↔
        (fun u => ∀ j, π ^ d ∣ D x0 u j) (v - y0) := by
      intro v
      simp only [hSol, hFexp]
      refine forall_congr' fun j => ?_
      rw [add_assoc, dvd_add_right (dvd_mul_right _ _), dvd_add_left
        ((pow_dvd_pow π (by omega : K ≤ 2 * a)).trans (by rw [pow_mul']; exact dvd_mul_right _ _)),
        hKa, hpow, mul_dvd_mul_iff_left (pow_ne_zero _ hπ0)]
    have hcondK1 : ∀ v : ι → R, Sol (K + 1) (liftI π a c + π ^ a • v) ↔
        (fun u => ∀ j, π ^ (d + 1) ∣ D x0 u j) (v - (y0 - w0)) := by
      intro v
      simp only [hSol, hFexp]
      refine forall_congr' fun j => ?_
      have hsplit : π ^ K * τ j + π ^ a * D x0 (v - y0) j = π ^ a * D x0 (v - (y0 - w0)) j := by
        rw [show v - (y0 - w0) = (v - y0) + w0 by abel, map_add, hw0, hKa, pow_add]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [dvd_add_left ((pow_dvd_pow π (by omega : K + 1 ≤ 2 * a)).trans
        (by rw [pow_mul']; exact dvd_mul_right _ _)), hsplit,
        show K + 1 = a + (d + 1) by omega, hpow, mul_dvd_mul_iff_left (pow_ne_zero _ hπ0)]
    have hstab : ∀ e, ∀ x y : ι → R, (∀ j, π ^ e ∣ D x0 x j) → ∀ j, π ^ e ∣ D x0 (x + π ^ e • y) j := by
      intro e x y hx j
      rw [map_add, map_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact dvd_add (hx j) (dvd_mul_right _ _)
    obtain ⟨sK⟩ := shiftEquiv π d (fun u => ∀ j, π ^ d ∣ D x0 u j) (hstab d) y0
    obtain ⟨sK1⟩ := shiftEquiv π (d + 1) (fun u => ∀ j, π ^ (d + 1) ∣ D x0 u j) (hstab (d + 1)) (y0 - w0)
    rw [Nat.card_congr ((Equiv.subtypeEquivRight fun y => hcondK1 _).trans sK1),
      Nat.card_congr ((Equiv.subtypeEquivRight fun y => hcondK _).trans sK)]
    have hA := card_succ_of_shift (ι := ι) π hπ d (fun u => ∀ j, π ^ d ∣ D x0 u j) (hstab d)
    have hB := card_ker_succ π hπ d (D x0) (hD x0 (fun j => ⟨τ j, hτ j⟩))
    rw [← hB, hA, mul_comm]
  -- sum over the classes
  have : ∀ c : {c : ι → R ⧸ Ideal.span {π ^ a} // P (liftI π a c)},
      Finite {y : ι → R ⧸ Ideal.span {π ^ (d + 1)} //
        Sol (K + 1) (liftI π a c.1 + π ^ a • liftI π (d + 1) y)} := fun _ => inferInstance
  have : ∀ c : {c : ι → R ⧸ Ideal.span {π ^ a} // P (liftI π a c)},
      Finite {y : ι → R ⧸ Ideal.span {π ^ d} // Sol K (liftI π a c.1 + π ^ a • liftI π d y)} :=
    fun _ => inferInstance
  have : Fintype {c : ι → R ⧸ Ideal.span {π ^ a} // P (liftI π a c)} := Fintype.ofFinite _
  rw [Nat.card_congr eK1, Nat.card_congr eK, Nat.card_sigma, Nat.card_sigma, Finset.sum_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => hclass c

end QuadFormsKB.LocalDensity.DVR

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The differential `formD Q x` is additive in the base point `x`. -/
theorem formD_add_base (Q : QuadForm R n) (x y : Fin n × Fin n → R) :
    formD Q (x + y) = formD Q x + formD Q y := by
  refine LinearMap.ext fun w => funext fun p => ?_
  simp only [formD, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Pi.add_apply]
  have hc : ∀ i, DVR.col (toMat (x + y)) i = DVR.col (toMat x) i + DVR.col (toMat y) i := fun i => rfl
  split_ifs <;> simp only [hc, bil, add_dotProduct, mulVec_add, dotProduct_add]
  ring

/-- The differential `formD Q x` is homogeneous in the base point `x`. -/
theorem formD_smul_base (Q : QuadForm R n) (c : R) (x : Fin n × Fin n → R) :
    formD Q (c • x) = c • formD Q x := by
  refine LinearMap.ext fun w => funext fun p => ?_
  simp only [formD, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, Pi.smul_apply]
  have hc : ∀ i, DVR.col (toMat (c • x)) i = c • DVR.col (toMat x) i := fun i => rfl
  split_ifs <;> simp only [hc, bil, smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

end QuadFormsKB.LocalDensity.DVR

open IsDedekindDomain NumberField MeasureTheory Filter Topology WithZero Matrix
open scoped ENNReal NNReal

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.LerayPadic

open QuadFormsKB.Analysis QuadFormsKB.LocalDensity QuadFormsKB.LocalZeta QuadFormsKB.Lattices
open QuadFormsKB.LocalDensity.DVR (formF formD UpperIdx liftI redI toMat)

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "πv" => LocalDensity.NF.π v

variable (Q₀ : QuadForm (𝓞 F) n)

local notation "Qo" => NF.Qp v Q₀

/-! ### The map $Z \mapsto \tilde G(Z) = (Q\circ(1+\pi^mZ) - Q)/\pi^m$ -/

/-- The identity matrix as a vector indexed by `Fin n × Fin n`. -/
def oneVec : Fin n × Fin n → 𝔬 := fun p => if p.1 = p.2 then 1 else 0

theorem toMat_oneVec : toMat (oneVec v (n := n)) = 1 := by
  ext i j; simp [toMat, oneVec, Matrix.one_apply]

theorem formF_oneVec (p : UpperIdx n) : formF (Qo) (oneVec v) p = (Qo).coeff p.1.1 p.1.2 := by
  simp only [formF, toMat_oneVec, QuadForm.compMat_one]

/-- $\tilde G_m(Z) = D_1Z + \pi^m\,(Q\circ Z)$, so that $Q\circ(1+\pi^mZ) = Q + \pi^m\tilde G_m(Z)$. -/
def gTilde (m : ℕ) (z : Fin n × Fin n → 𝔬) : UpperIdx n → 𝔬 :=
  formD (Qo) (oneVec v) z + πv ^ m • formF (Qo) z

theorem formF_one_add (m : ℕ) (z : Fin n × Fin n → 𝔬) :
    formF (Qo) (oneVec v + πv ^ m • z) = formF (Qo) (oneVec v) + πv ^ m • gTilde v Q₀ m z := by
  rw [DVR.formF_add_smul]
  funext p
  simp only [gTilde, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Taylor expansion of $\tilde G_m$:** $\tilde G_m(Z + cW) = \tilde G_m(Z) + c\,D_{1+\pi^mZ}W + c^2\pi^m(Q\circ W)$. -/
theorem gTilde_add_smul (m : ℕ) (z w : Fin n × Fin n → 𝔬) (c : 𝔬) :
    gTilde v Q₀ m (z + c • w) = gTilde v Q₀ m z + c • formD (Qo) (oneVec v + πv ^ m • z) w +
      c ^ 2 • (πv ^ m • formF (Qo) w) := by
  rw [DVR.formD_add_base, DVR.formD_smul_base]
  funext p
  simp only [gTilde, DVR.formF_add_smul, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    LinearMap.add_apply, LinearMap.smul_apply]
  ring

/-- Solutions of $\tilde G_m \equiv 0 \bmod \pi^j$ are stable under $Z \mapsto Z + \pi^jW$. -/
theorem gTilde_shift (m j : ℕ) {z z' : Fin n × Fin n → 𝔬} (h : ∀ p, πv ^ j ∣ z' p - z p) :
    (∀ p, πv ^ j ∣ gTilde v Q₀ m z' p) ↔ ∀ p, πv ^ j ∣ gTilde v Q₀ m z p := by
  choose w hw using h
  have hz : z' = z + πv ^ j • w := by
    funext p; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; rw [← hw p]; ring
  have key : ∀ p, gTilde v Q₀ m z' p = gTilde v Q₀ m z p + πv ^ j *
      (formD (Qo) (oneVec v + πv ^ m • z) w p + πv ^ j * (πv ^ m * formF (Qo) w p)) := by
    intro p
    rw [hz, gTilde_add_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine forall_congr' fun p => ?_
  rw [key, dvd_add_left (dvd_mul_right _ _)]

/-- The solutions of $\tilde G_m \equiv 0 \bmod \pi^j$ in $M_n(\mathfrak o_v/\pi^j)$. -/
abbrev solG (m j : ℕ) : Type :=
  {z : Fin n × Fin n → RQ v j // ∀ p, πv ^ j ∣ gTilde v Q₀ m (liftI πv j z) p}

instance (m j : ℕ) : Finite (solG v Q₀ m j) := by
  have := DVR.finite_vec (ι := Fin n × Fin n) πv (NF.irreducible_π v) j
  infer_instance

/-- **Stabilization of the solution counts of $\tilde G_m$** (for $\pi^d \,\|\, \det H$ and $j \ge 2d+1$):
$\#S_{j+1}\,q^{n(n+1)/2} = q^{n^2}\,\#S_j$. -/
theorem card_solG_succ (m d j : ℕ) (hd : πv ^ d ∣ (Qo).hessian.det) (hd' : ¬ πv ^ (d + 1) ∣ (Qo).hessian.det)
    (hj : 2 * d + 1 ≤ j) :
    Nat.card (solG v Q₀ m (j + 1)) * DVR.q 𝔬 ^ (n * (n + 1) / 2) = DVR.q 𝔬 ^ (n * n) * Nat.card (solG v Q₀ m j) := by
  have hπ := NF.irreducible_π v
  have h := DVR.card_sol_succ_gen πv hπ (gTilde v Q₀ m) (fun w => πv ^ m • formF (Qo) w)
    (fun z => formD (Qo) (oneVec v + πv ^ m • z)) (gTilde_add_smul v Q₀ m) 0 d j hj ?_
  · rw [DVR.card_upperIdx, Fintype.card_prod, Fintype.card_fin] at h
    simpa only [Pi.zero_apply, sub_zero] using h
  · intro z hz c
    refine DVR.formD_surj (Qo) (Qo) πv hπ d (m + j) hd hd' (by omega) _ (fun p => ?_) c
    rw [formF_one_add, Pi.add_apply, formF_oneVec]
    simp only [Pi.smul_apply, smul_eq_mul, add_sub_cancel_left, pow_add]
    exact mul_dvd_mul_left _ (by simpa using hz p)

/-! ### The boxes $1 + \pi^m(\tilde Z + \pi^jM_n(\mathfrak o_v))$ -/

/-- The point $1 + \pi^mZ$ of $M_n(F_v)$. -/
def ptM (m : ℕ) (z : Fin n × Fin n → 𝔬) : Matrix (Fin n) (Fin n) Fv :=
  (toMat (oneVec v + πv ^ m • z)).map (algebraMap 𝔬 Fv)

theorem ptM_apply (m : ℕ) (z : Fin n × Fin n → 𝔬) (i l : Fin n) :
    ptM v m z i l = (1 : Matrix (Fin n) (Fin n) Fv) i l + ((πv : Fv)) ^ m * (z (i, l) : Fv) := by
  simp only [ptM, toMat, Matrix.map_apply, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, oneVec,
    Matrix.one_apply]
  split_ifs <;> simp

/-- The box $\{X : X \equiv Y \bmod \pi^k\}$ in $M_n(F_v)$. -/
def boxM (k : ℕ) (Y : Matrix (Fin n) (Fin n) Fv) : Set (Matrix (Fin n) (Fin n) Fv) :=
  {X | ∀ i l, Valued.v (X i l - Y i l) ≤ exp (-(k : ℤ))}

theorem measurableSet_boxM (k : ℕ) (Y : Matrix (Fin n) (Fin n) Fv) : MeasurableSet (boxM v k Y) := by
  have : boxM v k Y = ⋂ i, ⋂ l, (fun X : Matrix (Fin n) (Fin n) Fv => X i l + -Y i l) ⁻¹'
      (latticeV v (k : ℤ) : Set Fv) := by
    ext X; simp [boxM, mem_latticeV, sub_eq_add_neg]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun l =>
    (measurableSet_latticeV v k).preimage ((continuous_id.matrix_elem i l).add continuous_const).measurable

theorem volM_boxM (k : ℕ) (Y : Matrix (Fin n) (Fin n) Fv) :
    volM v (boxM v k Y) = haarV v (latticeV v (k : ℤ)) ^ (n * n) := by
  have hpre : (fun Y' : Fin n → Fin n → Fv => (Matrix.of Y')ᵀ) ⁻¹' boxM v k Y =
      Set.univ.pi fun l => Set.univ.pi fun i =>
        (fun z : Fv => z + -Y i l) ⁻¹' (latticeV v (k : ℤ) : Set Fv) := by
    ext Y'
    simp only [Set.mem_preimage, boxM, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
      SetLike.mem_coe, mem_latticeV, Matrix.transpose_apply, Matrix.of_apply, ← sub_eq_add_neg]
    exact ⟨fun h l i => h i l, fun h i l => h l i⟩
  rw [volM, Measure.map_apply (measurable_ofT v) (measurableSet_boxM v k Y), hpre, Measure.pi_pi]
  simp only [Measure.pi_pi, measure_preimage_add_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul]

theorem valued_coe_mul_pi_pow_le (m j : ℕ) (x : 𝔬) :
    Valued.v (((πv : Fv)) ^ m * (x : Fv)) ≤ exp (-((m + j : ℕ) : ℤ)) ↔ πv ^ j ∣ x := by
  have h1 : ((πv : Fv)) ^ m * (x : Fv) = ((πv ^ m * x : 𝔬) : Fv) := by push_cast; ring
  rw [h1, ← NF.mem_span_π_pow, Ideal.mem_span_singleton, pow_add,
    mul_dvd_mul_iff_left (pow_ne_zero _ (NF.irreducible_π v).ne_zero)]

theorem ptM_mem_thick_iff (m j : ℕ) (z : Fin n × Fin n → 𝔬) :
    ptM v m z ∈ thick v Q₀ (m + j) ↔ ∀ p, πv ^ j ∣ gTilde v Q₀ m z p := by
  have hc : ∀ i l, ((QV v Q₀).compMat (ptM v m z)).coeff i l - (QV v Q₀).coeff i l =
      algebraMap 𝔬 Fv (((Qo).compMat (toMat (oneVec v + πv ^ m • z))).coeff i l - (Qo).coeff i l) := by
    intro i l
    rw [ptM, QuadForm.map_compMat, map_sub]
    rfl
  constructor
  · intro h p
    have := h p.1.1 p.1.2
    rw [hc] at this
    have e : ((Qo).compMat (toMat (oneVec v + πv ^ m • z))).coeff p.1.1 p.1.2 - (Qo).coeff p.1.1 p.1.2 =
        πv ^ m * gTilde v Q₀ m z p := by
      change formF (Qo) (oneVec v + πv ^ m • z) p - _ = _
      rw [formF_one_add, Pi.add_apply, formF_oneVec, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
    rw [e] at this
    rw [← valued_coe_mul_pi_pow_le v m j]
    simpa [map_mul] using this
  · intro h i l
    rw [hc]
    by_cases hil : i ≤ l
    · have e : ((Qo).compMat (toMat (oneVec v + πv ^ m • z))).coeff i l - (Qo).coeff i l =
          πv ^ m * gTilde v Q₀ m z ⟨(i, l), hil⟩ := by
        change formF (Qo) (oneVec v + πv ^ m • z) ⟨(i, l), hil⟩ - _ = _
        rw [formF_one_add, Pi.add_apply, formF_oneVec, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
      rw [e]
      have := (valued_coe_mul_pi_pow_le v m j _).mpr (h ⟨(i, l), hil⟩)
      simpa [map_mul] using this
    · rw [((Qo).compMat _).upper (show id l < id i from not_le.mp hil), (Qo).upper (show id l < id i from
        not_le.mp hil), sub_zero, map_zero, Valuation.map_zero]
      exact zero_le

theorem ptM_mem_boxM_iff (m j : ℕ) (z z' : Fin n × Fin n → 𝔬) :
    ptM v m z' ∈ boxM v (m + j) (ptM v m z) ↔ ∀ p, πv ^ j ∣ z' p - z p := by
  have e : ∀ i l, ptM v m z' i l - ptM v m z i l = ((πv : Fv)) ^ m * ((z' (i, l) - z (i, l) : 𝔬) : Fv) := by
    intro i l; rw [ptM_apply, ptM_apply]; push_cast; ring
  simp only [boxM, Set.mem_ofPred_eq, e, valued_coe_mul_pi_pow_le]
  exact ⟨fun h p => h p.1 p.2, fun h i l => h (i, l)⟩

theorem ptM_mem_ballOne (m : ℕ) (z : Fin n × Fin n → 𝔬) : ptM v m z ∈ ballOne v m := by
  intro i l
  rw [ptM_apply, add_sub_cancel_left]
  have := (valued_coe_mul_pi_pow_le v m 0 (z (i, l))).mpr (by simp)
  simpa using this

theorem exists_ptM {m : ℕ} {X : Matrix (Fin n) (Fin n) Fv} (hX : X ∈ ballOne v m) : ∃ z, X = ptM v m z := by
  have hπ0 : ((πv : Fv)) ≠ 0 := by
    intro h; have := NF.valued_π v; rw [h, Valuation.map_zero] at this; exact WithZero.zero_ne_coe this
  have hint : ∀ i l, Valued.v ((((πv : Fv)) ^ m)⁻¹ * (X i l - (1 : Matrix (Fin n) (Fin n) Fv) i l)) ≤ 1 := by
    intro i l
    rw [map_mul, map_inv₀, map_pow, NF.valued_π]
    have h := hX i l
    calc (exp (-1 : ℤ) ^ m)⁻¹ * Valued.v (X i l - (1 : Matrix (Fin n) (Fin n) Fv) i l)
        ≤ (exp (-1 : ℤ) ^ m)⁻¹ * exp (-(m : ℤ)) := mul_le_mul_right h _
      _ = 1 := by rw [← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_add]; simp
  refine ⟨fun p => ⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hint p.1 p.2)⟩, ?_⟩
  ext i l
  rw [ptM_apply]
  simp only
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hπ0), one_mul, add_sub_cancel]

theorem boxM_subset_ballOne (m j : ℕ) (z : Fin n × Fin n → 𝔬) : boxM v (m + j) (ptM v m z) ⊆ ballOne v m := by
  intro X hX i l
  have h1 := hX i l
  have h2 := ptM_mem_ballOne v m z i l
  have h1' : Valued.v (X i l - ptM v m z i l) ≤ exp (-(m : ℤ)) :=
    h1.trans (by rw [exp_le_exp]; push_cast; omega)
  calc Valued.v (X i l - (1 : Matrix (Fin n) (Fin n) Fv) i l)
      = Valued.v ((X i l - ptM v m z i l) + (ptM v m z i l - (1 : Matrix (Fin n) (Fin n) Fv) i l)) := by ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ ≤ _ := max_le h1' h2

/-! ### The volume of $(1+\pi^mM_n(\mathfrak o_v)) \cap \Phi^{-1}(Q_0 + \mathfrak p^{m+j})$ -/

theorem liftI_sub_dvd (j : ℕ) (z : Fin n × Fin n → 𝔬) (p : Fin n × Fin n) :
    πv ^ j ∣ z p - liftI πv j (redI πv j z) p := by
  obtain ⟨w, hw⟩ := DVR.liftI_redI πv j z
  rw [hw]
  exact ⟨-w p, by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring⟩

open Classical in
theorem ballOne_inter_thick_eq (m j : ℕ) [Fintype (RQ v j)] :
    ballOne v m ∩ thick v Q₀ (m + j) = ⋃ z ∈ (Finset.univ.filter fun z : Fin n × Fin n → RQ v j =>
      ∀ p, πv ^ j ∣ gTilde v Q₀ m (liftI πv j z) p), boxM v (m + j) (ptM v m (liftI πv j z)) := by
  ext X
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]
  constructor
  · rintro ⟨hX, hT⟩
    obtain ⟨z, rfl⟩ := exists_ptM v hX
    refine ⟨redI πv j z, ?_, (ptM_mem_boxM_iff v m j _ _).mpr fun p => liftI_sub_dvd v j z p⟩
    exact (gTilde_shift v Q₀ m j fun p => by
      have := liftI_sub_dvd v j z p
      rw [show liftI πv j (redI πv j z) p - z p = -(z p - liftI πv j (redI πv j z) p) by ring]
      exact (dvd_neg).mpr this).mpr ((ptM_mem_thick_iff v Q₀ m j z).mp hT)
  · rintro ⟨z, hz, hX⟩
    have hb := boxM_subset_ballOne v m j _ hX
    refine ⟨hb, ?_⟩
    obtain ⟨z', rfl⟩ := exists_ptM v hb
    exact (ptM_mem_thick_iff v Q₀ m j z').mpr
      ((gTilde_shift v Q₀ m j ((ptM_mem_boxM_iff v m j _ _).mp hX)).mpr hz)

theorem boxM_ptM_disjoint (m j : ℕ) {z z' : Fin n × Fin n → RQ v j} (h : z ≠ z') :
    Disjoint (boxM v (m + j) (ptM v m (liftI πv j z))) (boxM v (m + j) (ptM v m (liftI πv j z'))) := by
  rw [Set.disjoint_left]
  intro X h1 h2
  obtain ⟨y, rfl⟩ := exists_ptM v (boxM_subset_ballOne v m j _ h1)
  have e1 := (ptM_mem_boxM_iff v m j _ _).mp h1
  have e2 := (ptM_mem_boxM_iff v m j _ _).mp h2
  apply h
  rw [← DVR.redI_liftI πv j z, ← DVR.redI_liftI πv j z', DVR.redI_eq_iff]
  intro p
  have := dvd_sub (e2 p) (e1 p)
  rwa [show y p - liftI πv j z' p - (y p - liftI πv j z p) = liftI πv j z p - liftI πv j z' p by ring] at this

/-- **The volume of the congruence set near $1$:** $\mathrm{vol}((1+\pi^mM_n(\mathfrak o_v))\cap
\Phi^{-1}(Q_0+\mathfrak p^{m+j})) = \#S_j\cdot\mathrm{vol}(\mathfrak p^{m+j})^{n^2}$, $S_j$ the solutions of
$\tilde G_m \equiv 0 \bmod \pi^j$ (`solG`). -/
theorem volM_ballOne_inter_thick (m j : ℕ) :
    volM v (ballOne v m ∩ thick v Q₀ (m + j)) =
      (Nat.card (solG v Q₀ m j) : ℝ≥0∞) * haarV v (latticeV v ((m + j : ℕ) : ℤ)) ^ (n * n) := by
  classical
  have := DVR.finite_quot_pow πv (NF.irreducible_π v) j
  let _ : Fintype (RQ v j) := Fintype.ofFinite _
  rw [ballOne_inter_thick_eq v Q₀ m j, measure_biUnion_finset]
  · simp only [volM_boxM, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  · intro z _ z' _ h
    exact boxM_ptM_disjoint v m j h
  · intro z _; exact measurableSet_boxM v _ _

/-- **The Leray quotient of $1 + \pi^mM_n(\mathfrak o_v)$ at level $m+j$** is $\#S_j/q^{(m+j)\,n(n-1)/2}$. -/
theorem lerayApprox_ballOne_add (m j : ℕ) :
    lerayApprox v Q₀ (ballOne v m) (m + j) = (Nat.card (solG v Q₀ m j) : ℝ≥0∞) /
      (DVR.q 𝔬 : ℝ≥0∞) ^ ((m + j) * (n * (n - 1) / 2)) := by
  have hq0 : (DVR.q 𝔬 : ℝ≥0∞) ≠ 0 := by exact_mod_cast (q_pos v).ne'
  have hqt : (DVR.q 𝔬 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  set k := m + j
  set a := (DVR.q 𝔬 : ℝ≥0∞) ^ (k * (n * (n + 1) / 2))
  set b := (DVR.q 𝔬 : ℝ≥0∞) ^ (k * (n * (n - 1) / 2))
  set c := (Nat.card (solG v Q₀ m j) : ℝ≥0∞)
  have hab : ((DVR.q 𝔬 : ℝ≥0∞) ^ k)⁻¹ ^ (n * n) = (a * b)⁻¹ := by
    have : a * b = ((DVR.q 𝔬 : ℝ≥0∞) ^ k) ^ (n * n) := by
      rw [← pow_add, ← mul_add, two_mul_choose, pow_mul]
    rw [this, ← ENNReal.inv_pow]
  rw [lerayApprox, volM_ballOne_inter_thick, haarV_latticeV_nat, hab,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ hq0)) (Or.inl (ENNReal.pow_ne_top hqt))]
  calc a * (c * (a⁻¹ * b⁻¹)) = (a * a⁻¹) * (c * b⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt), one_mul,
      div_eq_mul_inv]

/-- The Leray quotients of $1+\pi^mM_n(\mathfrak o_v)$ are constant from level $m + 2d + 1$ on. -/
theorem lerayApprox_ballOne_add_succ (m d j : ℕ) (hd : πv ^ d ∣ (Qo).hessian.det)
    (hd' : ¬ πv ^ (d + 1) ∣ (Qo).hessian.det) (hj : 2 * d + 1 ≤ j) :
    lerayApprox v Q₀ (ballOne v m) (m + (j + 1)) = lerayApprox v Q₀ (ballOne v m) (m + j) := by
  have hq0 : (DVR.q 𝔬 : ℝ≥0∞) ≠ 0 := by exact_mod_cast (q_pos v).ne'
  have hqt : (DVR.q 𝔬 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h := card_solG_succ v Q₀ m d j hd hd' hj
  set e := n * (n - 1) / 2
  have hnn : n * n = n * (n + 1) / 2 + e := (two_mul_choose n).symm
  rw [hnn, pow_add] at h
  have hcard : Nat.card (solG v Q₀ m (j + 1)) = DVR.q 𝔬 ^ e * Nat.card (solG v Q₀ m j) := by
    have hpos : 0 < DVR.q 𝔬 ^ (n * (n + 1) / 2) := pow_pos (q_pos v) _
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h]; ring
  rw [lerayApprox_ballOne_add, lerayApprox_ballOne_add, hcard, Nat.cast_mul, Nat.cast_pow,
    show (m + (j + 1)) * e = e + (m + j) * e by ring, pow_add, ENNReal.mul_div_mul_left _ _
      (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt)]

theorem lerayApprox_ballOne_add_eq (m d j : ℕ) (hd : πv ^ d ∣ (Qo).hessian.det)
    (hd' : ¬ πv ^ (d + 1) ∣ (Qo).hessian.det) (hj : 2 * d + 1 ≤ j) (i : ℕ) :
    lerayApprox v Q₀ (ballOne v m) (m + (j + i)) = lerayApprox v Q₀ (ballOne v m) (m + j) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show j + (i + 1) = (j + i) + 1 by ring, lerayApprox_ballOne_add_succ v Q₀ m d (j + i) hd hd' (by omega), ih]

/-- **The gauge-form volume of a principal congruence subgroup** (every finite place, dyadic included; $Q_0$
nondegenerate, $\pi^d \,\|\, \det H$, $j \ge 2d+1$): $\mu_v(K_m) = \#S_j/q^{(m+j)\,n(n-1)/2}$. -/
theorem muLoc_congSub_eq_card_solG (hQ : Q₀.Nondegenerate) (m : ℕ) (hm : 1 ≤ m) (d j : ℕ)
    (hd : πv ^ d ∣ (Qo).hessian.det) (hd' : ¬ πv ^ (d + 1) ∣ (Qo).hessian.det) (hj : 2 * d + 1 ≤ j) :
    Measure.muLoc v Q₀ 1 (congSub v Q₀ m hm : Set _) = (Nat.card (solG v Q₀ m j) : ℝ≥0∞) /
      (DVR.q 𝔬 : ℝ≥0∞) ^ ((m + j) * (n * (n - 1) / 2)) := by
  obtain ⟨K, hK⟩ := (lerayApprox_ballOne_eventually v Q₀ hQ m hm).exists_forall_of_atTop
  rw [← hK (m + (j + K)) (by omega), lerayApprox_ballOne_add_eq v Q₀ m d j hd hd' hj K,
    lerayApprox_ballOne_add]

/-- For $j \le m$ the solutions of $\tilde G_m \equiv 0 \bmod \pi^j$ are those of the linear congruence
$D_1Z \equiv 0 \bmod \pi^j$. -/
theorem solG_iff_of_le (m j : ℕ) (hjm : j ≤ m) (z : Fin n × Fin n → 𝔬) :
    (∀ p, πv ^ j ∣ gTilde v Q₀ m z p) ↔ ∀ p, πv ^ j ∣ formD (Qo) (oneVec v) z p := by
  refine forall_congr' fun p => ?_
  simp only [gTilde, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [dvd_add_left (dvd_mul_of_dvd_left (pow_dvd_pow _ hjm) _)]

/-- **$\mu_v(K_m)$ as a linear count** ($2d+1 \le j \le m$): $\mu_v(K_m) = q^{-(m+j)\,n(n-1)/2}\,
\#\{Z \in M_n(\mathfrak o_v/\pi^j) : D_1Z \equiv 0\}$, $D_1$ the differential of $X \mapsto Q\circ X$ at $1$, whose
kernel is the Lie algebra $\mathfrak{so}(Q)$. -/
@[kb "weil1982" "§2.2 (gauge-form measures; volumes by counting mod p^k) [unverified]"]
theorem muLoc_congSub_eq (hQ : Q₀.Nondegenerate) (m : ℕ) (hm : 1 ≤ m) (d j : ℕ)
    (hd : πv ^ d ∣ (Qo).hessian.det) (hd' : ¬ πv ^ (d + 1) ∣ (Qo).hessian.det) (hj : 2 * d + 1 ≤ j)
    (hjm : j ≤ m) :
    Measure.muLoc v Q₀ 1 (congSub v Q₀ m hm : Set _) =
      (Nat.card {z : Fin n × Fin n → RQ v j // ∀ p, πv ^ j ∣ formD (Qo) (oneVec v) (liftI πv j z) p} : ℝ≥0∞) /
        (DVR.q 𝔬 : ℝ≥0∞) ^ ((m + j) * (n * (n - 1) / 2)) := by
  rw [muLoc_congSub_eq_card_solG v Q₀ hQ m hm d j hd hd' hj,
    Nat.card_congr (Equiv.subtypeEquivRight (p := fun z : Fin n × Fin n → RQ v j =>
      ∀ p, πv ^ j ∣ gTilde v Q₀ m (liftI πv j z) p) (q := fun z : Fin n × Fin n → RQ v j =>
      ∀ p, πv ^ j ∣ formD (Qo) (oneVec v) (liftI πv j z) p) fun z => solG_iff_of_le v Q₀ m j hjm _)]

end QuadFormsKB.Tamagawa.Measure.LerayPadic

/-! ### Linear congruence counts over $R/\pi^j$ -/

namespace QuadFormsKB.LocalDensity.DVR

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The chosen lift $R/\pi^j \to R$ (the scalar version of `liftI`). -/
noncomputable abbrev lift1 (π : R) (j : ℕ) (x : R ⧸ Ideal.span {π ^ j}) : R :=
  Function.surjInv Ideal.Quotient.mk_surjective x

theorem mk_lift1 (π : R) (j : ℕ) (x : R ⧸ Ideal.span {π ^ j}) : Ideal.Quotient.mk _ (lift1 π j x) = x :=
  Function.surjInv_eq _ x

theorem dvd_mul_iff_of_mk_eq (π : R) (j : ℕ) (h : R) {a b : R}
    (hab : Ideal.Quotient.mk (Ideal.span {π ^ j}) a = Ideal.Quotient.mk _ b) :
    π ^ j ∣ h * a ↔ π ^ j ∣ h * b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hab
  obtain ⟨c, hc⟩ := hab
  have : h * a = h * b + π ^ j * (h * c) := by linear_combination h * hc
  rw [this, dvd_add_left (dvd_mul_right _ _)]

variable [Finite (IsLocalRing.ResidueField R)]

/-- $\#\{x \in R/\pi^j : \pi^j \mid hx\} = q^e$ for $\pi^e \,\|\, h$, $e \le j$. -/
theorem card_dvd_mul_lift1 (π : R) (hπ : Irreducible π) {h : R} {e j : ℕ} (he : π ^ e ∣ h)
    (he' : ¬ π ^ (e + 1) ∣ h) (hej : e ≤ j) :
    Nat.card {x : R ⧸ Ideal.span {π ^ j} // π ^ j ∣ h * lift1 π j x} = q R ^ e := by
  set P : Matrix (Fin 1) (Fin 1) R := !![h]
  have hdet : P.det = h := by simp [P]
  have h0 : h ≠ 0 := fun h0 => he' (h0 ▸ dvd_zero _)
  obtain ⟨u, hu, huu⟩ := dvr_exact hπ he he'
  have hc : P.det ∣ π ^ j := by
    rw [hdet, hu]
    refine ⟨π ^ (j - e) * ↑huu.unit⁻¹, ?_⟩
    rw [show π ^ e * u * (π ^ (j - e) * ↑huu.unit⁻¹) = π ^ (e + (j - e)) * (u * ↑huu.unit⁻¹) by ring,
      IsUnit.mul_val_inv, mul_one, Nat.add_sub_cancel' hej]
  have h1 := QuadFormsKB.Tamagawa.card_ker_redMat hπ P (QuadFormsKB.Tamagawa.exists_mulVec_eq_smul P hc)
  rw [QuadFormsKB.Tamagawa.card_quot_range hπ P (by rw [hdet]; exact h0), hdet,
    QuadFormsKB.Tamagawa.card_quot_span_eq hπ he he'] at h1
  rw [← h1]
  have hmem : ∀ z : Fin 1 → R ⧸ Ideal.span {π ^ j},
      z ∈ (QuadFormsKB.Tamagawa.redMat π j P).ker ↔ π ^ j ∣ h * lift1 π j (z 0) := by
    intro z
    rw [AddMonoidHom.mem_ker, QuadFormsKB.Tamagawa.redMat_apply]
    constructor
    · intro hz
      have := congrFun hz 0
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.map_apply, P, Matrix.of_apply,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Pi.zero_apply] at this
      rw [← mk_lift1 π j (z 0), ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
      exact this
    · intro hz
      funext i
      fin_cases i
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.map_apply, P, Matrix.of_apply,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Pi.zero_apply]
      rw [← mk_lift1 π j (z 0), ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact hz
  exact Nat.card_congr
    { toFun := fun x => ⟨fun _ => x.1, (hmem _).mpr x.2⟩
      invFun := fun z => ⟨z.1 0, (hmem _).mp z.2⟩
      left_inv := fun x => rfl
      right_inv := fun z => by
        apply Subtype.ext; funext i; fin_cases i; rfl }

/-- $\#\{(x, y) \in (R/\pi^j)^2 : \pi^j \mid hx + h'y\} = q^e\,q^j$ for $\pi^e \,\|\, h$, $h \mid h'$, $e \le j$. -/
theorem card_dvd_add_lift1 (π : R) (hπ : Irreducible π) {h h' : R} (hh : h ∣ h') {e j : ℕ} (he : π ^ e ∣ h)
    (he' : ¬ π ^ (e + 1) ∣ h) (hej : e ≤ j) :
    Nat.card {p : (R ⧸ Ideal.span {π ^ j}) × (R ⧸ Ideal.span {π ^ j}) //
      π ^ j ∣ h * lift1 π j p.1 + h' * lift1 π j p.2} = q R ^ e * q R ^ j := by
  obtain ⟨c, rfl⟩ := hh
  have key : ∀ x y : R ⧸ Ideal.span {π ^ j}, (π ^ j ∣ h * lift1 π j x + h * c * lift1 π j y ↔
      π ^ j ∣ h * lift1 π j (x + Ideal.Quotient.mk _ c * y)) := by
    intro x y
    rw [show h * lift1 π j x + h * c * lift1 π j y = h * (lift1 π j x + c * lift1 π j y) by ring]
    refine dvd_mul_iff_of_mk_eq π j h ?_
    rw [map_add, map_mul, mk_lift1, mk_lift1, mk_lift1]
  have e : {p : (R ⧸ Ideal.span {π ^ j}) × (R ⧸ Ideal.span {π ^ j}) //
      π ^ j ∣ h * lift1 π j p.1 + h * c * lift1 π j p.2} ≃
      {x : R ⧸ Ideal.span {π ^ j} // π ^ j ∣ h * lift1 π j x} × (R ⧸ Ideal.span {π ^ j}) :=
    { toFun := fun p => (⟨p.1.1 + Ideal.Quotient.mk _ c * p.1.2, (key _ _).mp p.2⟩, p.1.2)
      invFun := fun t => ⟨(t.1.1 - Ideal.Quotient.mk _ c * t.2, t.2), (key _ _).mpr (by simpa using t.1.2)⟩
      left_inv := fun p => by apply Subtype.ext; simp
      right_inv := fun t => by ext <;> simp }
  have := finite_quot_pow π hπ j
  rw [Nat.card_congr e, Nat.card_prod, card_dvd_mul_lift1 π hπ he he' hej, card_quot_pow π hπ]

/-- The symmetric form: $\#\{(x,y) : \pi^j \mid hx + h'y\} = q^{\min(e,e')}\,q^j$ for $\pi^e \,\|\, h$,
$\pi^{e'} \,\|\, h'$, $e, e' \le j$. -/
theorem card_dvd_add_lift1' (π : R) (hπ : Irreducible π) {h h' : R} {e e' j : ℕ} (he : π ^ e ∣ h)
    (he' : ¬ π ^ (e + 1) ∣ h) (hf : π ^ e' ∣ h') (hf' : ¬ π ^ (e' + 1) ∣ h') (hej : e ≤ j) (hfj : e' ≤ j) :
    Nat.card {p : (R ⧸ Ideal.span {π ^ j}) × (R ⧸ Ideal.span {π ^ j}) //
      π ^ j ∣ h * lift1 π j p.1 + h' * lift1 π j p.2} = q R ^ min e e' * q R ^ j := by
  obtain ⟨u, hu, huu⟩ := dvr_exact hπ he he'
  obtain ⟨u', hu', huu'⟩ := dvr_exact hπ hf hf'
  rcases le_total e e' with hle | hle
  · have hdvd : h ∣ h' := ⟨π ^ (e' - e) * u' * ↑huu.unit⁻¹, by
      rw [hu, hu', show π ^ e * u * (π ^ (e' - e) * u' * ↑huu.unit⁻¹) =
        π ^ (e + (e' - e)) * u' * (u * ↑huu.unit⁻¹) by ring, IsUnit.mul_val_inv, mul_one,
        Nat.add_sub_cancel' hle]⟩
    rw [min_eq_left hle, card_dvd_add_lift1 π hπ hdvd he he' hej]
  · have hdvd : h' ∣ h := ⟨π ^ (e - e') * u * ↑huu'.unit⁻¹, by
      rw [hu, hu', show π ^ e' * u' * (π ^ (e - e') * u * ↑huu'.unit⁻¹) =
        π ^ (e' + (e - e')) * u * (u' * ↑huu'.unit⁻¹) by ring, IsUnit.mul_val_inv, mul_one,
        Nat.add_sub_cancel' hle]⟩
    rw [min_eq_right hle, ← card_dvd_add_lift1 π hπ hdvd hf hf' hfj]
    exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.prodComm _ _) fun p => by
      simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, add_comm])

end QuadFormsKB.LocalDensity.DVR

/-! ### The count for a diagonal ternary form -/

namespace QuadFormsKB.Tamagawa.Measure.LerayPadic

open QuadFormsKB.Analysis QuadFormsKB.LocalDensity QuadFormsKB.LocalZeta QuadFormsKB.Lattices
open QuadFormsKB.LocalDensity.DVR (formF formD UpperIdx liftI redI toMat lift1)

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "πv" => LocalDensity.NF.π v

theorem forall_upperIdx_three (P : UpperIdx 3 → Prop) :
    (∀ p, P p) ↔ (P ⟨(0, 0), le_rfl⟩ ∧ P ⟨(1, 1), le_rfl⟩ ∧ P ⟨(2, 2), le_rfl⟩) ∧
      (P ⟨(0, 1), by decide⟩ ∧ P ⟨(0, 2), by decide⟩ ∧ P ⟨(1, 2), by decide⟩) := by
  constructor
  · intro h; exact ⟨⟨h _, h _, h _⟩, h _, h _, h _⟩
  · rintro ⟨⟨h00, h11, h22⟩, h01, h02, h12⟩ ⟨⟨i, l⟩, hil⟩
    fin_cases i <;> fin_cases l <;> first | assumption | exact absurd hil (by decide)

/-- $D_1$ for a diagonal Hessian $\mathrm{diag}(h_0,h_1,h_2)$: $(D_1Z)_{ii} = h_iZ_{ii}$,
$(D_1Z)_{il} = h_iZ_{il} + h_lZ_{li}$ ($i < l$). -/
theorem formD_oneVec_diag (Q : QuadForm 𝔬 3) (h : Fin 3 → 𝔬) (hH : Q.hessian = Matrix.diagonal h)
    (w : Fin 3 × Fin 3 → 𝔬) (i l : Fin 3) (hil : i ≤ l) :
    formD Q (oneVec v) w ⟨(i, l), hil⟩ = if i = l then h i * w (i, i) else h i * w (i, l) + h l * w (l, i) := by
  fin_cases i <;> fin_cases l <;>
  first
  | exact absurd hil (by decide)
  | (simp [formD, DVR.bil, DVR.col, toMat, oneVec, hH, Matrix.mulVec, dotProduct,
      Matrix.diagonal_apply]; try ring)

/-- The block decomposition $M_3(A) \cong A^3 \times (A^2)^3$ (diagonal entries; the pairs $(Z_{il}, Z_{li})$). -/
def blockEquiv (A : Type*) : (Fin 3 × Fin 3 → A) ≃ (A × A × A) × ((A × A) × (A × A) × (A × A)) where
  toFun z := ((z (0, 0), z (1, 1), z (2, 2)), ((z (0, 1), z (1, 0)), (z (0, 2), z (2, 0)), (z (1, 2), z (2, 1))))
  invFun t := fun p => match p with
    | (0, 0) => t.1.1 | (1, 1) => t.1.2.1 | (2, 2) => t.1.2.2
    | (0, 1) => t.2.1.1 | (1, 0) => t.2.1.2 | (0, 2) => t.2.2.1.1 | (2, 0) => t.2.2.1.2
    | (1, 2) => t.2.2.2.1 | (2, 1) => t.2.2.2.2
  left_inv z := by
    funext ⟨i, l⟩
    fin_cases i <;> fin_cases l <;> rfl
  right_inv t := rfl

/-- **The kernel of $D_1 \bmod \pi^j$ for a diagonal ternary form** $\mathrm{diag}(h_0,h_1,h_2)$ with
$\pi^{e_i} \,\|\, h_i$, $e_i \le j$: it has $q^{e_0+e_1+e_2}\cdot\prod_{i<l}q^{\min(e_i,e_l)}q^j$ elements. -/
theorem card_kerD_diag3 (Q : QuadForm 𝔬 3) (h : Fin 3 → 𝔬) (hH : Q.hessian = Matrix.diagonal h) (j : ℕ)
    (e : Fin 3 → ℕ) (he : ∀ i, πv ^ e i ∣ h i) (he' : ∀ i, ¬ πv ^ (e i + 1) ∣ h i) (hej : ∀ i, e i ≤ j) :
    Nat.card {z : Fin 3 × Fin 3 → RQ v j // ∀ p, πv ^ j ∣ formD Q (oneVec v) (liftI πv j z) p} =
      (DVR.q 𝔬 ^ e 0 * DVR.q 𝔬 ^ e 1 * DVR.q 𝔬 ^ e 2) *
        ((DVR.q 𝔬 ^ min (e 0) (e 1) * DVR.q 𝔬 ^ j) * (DVR.q 𝔬 ^ min (e 0) (e 2) * DVR.q 𝔬 ^ j) *
          (DVR.q 𝔬 ^ min (e 1) (e 2) * DVR.q 𝔬 ^ j)) := by
  have hπ := NF.irreducible_π v
  set C1 := fun i : Fin 3 => {x : RQ v j // πv ^ j ∣ h i * lift1 πv j x}
  set C2 := fun i l : Fin 3 => {p : RQ v j × RQ v j // πv ^ j ∣ h i * lift1 πv j p.1 + h l * lift1 πv j p.2}
  have e1 : {z : Fin 3 × Fin 3 → RQ v j // ∀ p, πv ^ j ∣ formD Q (oneVec v) (liftI πv j z) p} ≃
      (C1 0 × C1 1 × C1 2) × (C2 0 1 × C2 0 2 × C2 1 2) := by
    refine (Equiv.subtypeEquiv (blockEquiv _) fun z => ?_).trans
      ((Equiv.subtypeProdEquivProd).trans (Equiv.prodCongr
        ((Equiv.subtypeProdEquivProd).trans (Equiv.prodCongr (Equiv.refl _) Equiv.subtypeProdEquivProd))
        ((Equiv.subtypeProdEquivProd).trans (Equiv.prodCongr (Equiv.refl _) Equiv.subtypeProdEquivProd))))
    rw [forall_upperIdx_three]
    simp only [formD_oneVec_diag v Q h hH, blockEquiv, Equiv.coe_fn_mk, ite_true, Fin.reduceEq, ite_false]
    rfl
  rw [Nat.card_congr e1]
  simp only [Nat.card_prod, C1, C2]
  rw [DVR.card_dvd_mul_lift1 πv hπ (he 0) (he' 0) (hej 0), DVR.card_dvd_mul_lift1 πv hπ (he 1) (he' 1) (hej 1),
    DVR.card_dvd_mul_lift1 πv hπ (he 2) (he' 2) (hej 2),
    DVR.card_dvd_add_lift1' πv hπ (he 0) (he' 0) (he 1) (he' 1) (hej 0) (hej 1),
    DVR.card_dvd_add_lift1' πv hπ (he 0) (he' 0) (he 2) (he' 2) (hej 0) (hej 2),
    DVR.card_dvd_add_lift1' πv hπ (he 1) (he' 1) (he 2) (he' 2) (hej 1) (hej 2)]
  ring

end QuadFormsKB.Tamagawa.Measure.LerayPadic
