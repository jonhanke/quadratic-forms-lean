/-
# The rank of an even unimodular positive definite lattice is divisible by 8

**Layer:** classical, over $\mathbb Z$, $\mathbb R$, $\mathbb C$.

Let $S \in M_{2k}(\mathbb Z)$ be symmetric, positive definite, with even diagonal and $\det S = 1$ (an even unimodular
positive definite lattice of rank $N = 2k$). Then $4 \mid k$, i.e. $8 \mid N$ (`four_dvd_of_evenUnimodular`).

*Proof* (the classical theta-function argument, genus $1$). Write $E(a)$ for the $1\times1$ matrix with entry $a$ and
$\phi(a) = -(a+1)^{-1}$. Theta inversion (`thetaG_neg_inv`) and integrality of the translation $a \mapsto a + 1$
(`thetaG_add_int`) give, for $\operatorname{Im} a > 0$,
$$\Theta_S(E(\phi(a))) = \big(-i(a+1)\big)^k\,\Theta_S(E(a)).$$
Applying this three times, $\phi^3 = \mathrm{id}$ and $(a+1)\cdot\frac{a}{a+1}\cdot\frac{-1}{a} = -1$, so
$\Theta_S(E(a)) = \big((-i)^3\cdot(-1)\big)^k\,\Theta_S(E(a)) = (-i)^k\,\Theta_S(E(a))$. At $a = i$ one has
$\Theta_S(E(i)) = \sum_X e^{-\pi X^{\mathsf T}SX}$, a sum of positive reals with $X = 0$ term $1$, so it is nonzero; hence
$(-i)^k = 1$ and $4 \mid k$.

Consequently the hypothesis $4 \mid k$ of `thetaG_sp` is automatic (`thetaG_sp'`), and with `spZGeneration`
(SpZGen.lean) the transformation law holds unconditionally (`thetaG_sp_uncond`).

Sources: Serre, *A Course in Arithmetic* (1973), Ch. VII, §6.1, Thm. 2 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Genus.SpZGen

open Matrix Complex
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

/-- The $1\times1$ complex matrix with entry $a$. -/
def oneMat (a : ℂ) : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => a

lemma oneMat_add_one (a : ℂ) : oneMat a + cZ (1 : Matrix (Fin 1) (Fin 1) ℤ) = oneMat (a + 1) := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi hj
  simp [oneMat, cZ]

lemma oneMat_neg_inv (a : ℂ) : -(oneMat a)⁻¹ = oneMat (-a⁻¹) := by
  rw [Matrix.inv_subsingleton]
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  subst hij
  simp [oneMat]

lemma oneMat_det_smul (a : ℂ) : det ((-I) • oneMat a) = -I * a := by
  rw [Matrix.det_unique]
  simp [oneMat]

lemma oneMat_I_mem : oneMat I ∈ siegelH 1 := by
  refine ⟨?_, ?_⟩
  · ext i j; simp [oneMat]
  · have : (oneMat I).map Complex.im = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      ext i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst hi hj
      simp [oneMat]
    rw [this]; exact PosDef.one

section
variable {k : ℕ} {S : Matrix (Fin (2 * k)) (Fin (2 * k)) ℤ}

/-- One step of the order-three argument. -/
lemma thetaG_phi_step (hSsymm : Sᵀ = S) (hSeven : ∀ i, Even (S i i))
    (hS : (S.map ((↑) : ℤ → ℝ)).PosDef) (hdet : S.det = 1) {a : ℂ} (ha : oneMat a ∈ siegelH 1) :
    oneMat (-(a + 1)⁻¹) ∈ siegelH 1 ∧
      thetaG (S.map ((↑) : ℤ → ℝ)) (oneMat (-(a + 1)⁻¹)) =
        (-I * (a + 1)) ^ k * thetaG (S.map ((↑) : ℤ → ℝ)) (oneMat a) := by
  have hB : (1 : Matrix (Fin 1) (Fin 1) ℤ)ᵀ = 1 := transpose_one
  have h1 : oneMat (a + 1) ∈ siegelH 1 := by
    have := (thetaLawAt_spNZ (g := 1) (S := S) hSsymm hSeven 1 hB) (oneMat a) ha
    have e : actG (spNZ 1 hB) (oneMat a) = oneMat a + cZ 1 := by
      simp [actG, spC_spNZ]
    rw [e, oneMat_add_one] at this
    exact this.2.1
  have h2 := thetaG_neg_inv k hSsymm hS hdet h1
  have h3 := thetaG_add_int hSsymm hSeven hB (oneMat a)
  rw [oneMat_add_one] at h3
  rw [oneMat_neg_inv, oneMat_det_smul] at h2
  refine ⟨?_, ?_⟩
  · have := neg_inv_mem_siegelH h1
    rwa [← oneMat_neg_inv]
  · rw [h2, h3]

lemma thetaG_phi_fixed (hSsymm : Sᵀ = S) (hSeven : ∀ i, Even (S i i))
    (hS : (S.map ((↑) : ℤ → ℝ)).PosDef) (hdet : S.det = 1) {a : ℂ} (ha : oneMat a ∈ siegelH 1)
    (h0 : a ≠ 0) (h1 : a + 1 ≠ 0) :
    thetaG (S.map ((↑) : ℤ → ℝ)) (oneMat a) = (-I) ^ k * thetaG (S.map ((↑) : ℤ → ℝ)) (oneMat a) := by
  obtain ⟨m1, e1⟩ := thetaG_phi_step hSsymm hSeven hS hdet ha
  obtain ⟨m2, e2⟩ := thetaG_phi_step hSsymm hSeven hS hdet m1
  obtain ⟨-, e3⟩ := thetaG_phi_step hSsymm hSeven hS hdet m2
  have hb1 : -(a + 1)⁻¹ + 1 = a * (a + 1)⁻¹ := by field_simp; ring
  have hb1' : -(a + 1)⁻¹ + 1 ≠ 0 := by
    rw [hb1]; exact mul_ne_zero h0 (inv_ne_zero h1)
  have hb2 : -(-(a + 1)⁻¹ + 1)⁻¹ = -((a + 1) * a⁻¹) := by
    rw [hb1, mul_inv, inv_inv]; ring
  have hb3 : -(-(a + 1)⁻¹ + 1)⁻¹ + 1 = -a⁻¹ := by
    rw [hb2]; field_simp; ring
  have hv : -(-(-(a + 1)⁻¹ + 1)⁻¹ + 1)⁻¹ = a := by
    rw [hb3]; simp
  have hf : (-I * (a + 1)) * (-I * (-(a + 1)⁻¹ + 1)) * (-I * (-(-(a + 1)⁻¹ + 1)⁻¹ + 1)) = -I := by
    rw [hb3, hb1]
    have : (-I) ^ 3 = I := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ]; simp
    calc (-I * (a + 1)) * (-I * (a * (a + 1)⁻¹)) * (-I * -a⁻¹)
        = (-I) ^ 3 * ((a + 1) * (a * (a + 1)⁻¹) * (-a⁻¹)) := by ring
      _ = -I := by
        rw [this]
        have : (a + 1) * (a * (a + 1)⁻¹) * (-a⁻¹) = -1 := by field_simp
        rw [this]; ring
  rw [hv] at e3
  set T := thetaG (S.map ((↑) : ℤ → ℝ))
  generalize (-I * (-(-(a + 1)⁻¹ + 1)⁻¹ + 1)) = f3 at e3 hf
  generalize (-I * (-(a + 1)⁻¹ + 1)) = f2 at e2 hf
  generalize (-I * (a + 1)) = f1 at e1 hf
  have key : T (oneMat a) = (f1 * f2 * f3) ^ k * T (oneMat a) := by
    calc T (oneMat a) = f3 ^ k * T (oneMat (-(-(a + 1)⁻¹ + 1)⁻¹)) := e3
      _ = f3 ^ k * (f2 ^ k * T (oneMat (-(a + 1)⁻¹))) := by rw [e2]
      _ = f3 ^ k * (f2 ^ k * (f1 ^ k * T (oneMat a))) := by rw [e1]
      _ = (f1 * f2 * f3) ^ k * T (oneMat a) := by rw [mul_pow, mul_pow]; ring
  rw [hf] at key
  exact key

lemma thetaArg_oneMat_I (X : Matrix (Fin (2 * k)) (Fin 1) ℤ) :
    thetaArg (S.map ((↑) : ℤ → ℝ)) (oneMat I) (cZ X) =
      ((-(π * ∑ i, ∑ j, (X i 0 : ℝ) * S i j * X j 0) : ℝ) : ℂ) := by
  simp [thetaArg, trace, Matrix.mul_apply, oneMat, cR, cZ, Finset.sum_mul, Finset.mul_sum]
  simp only [← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [show ∀ p a : ℂ, p * I * (a * I) = -(p * a) from fun p a => by
    linear_combination (p * a) * Complex.I_mul_I]

lemma thetaG_oneMat_I_ne (hS : (S.map ((↑) : ℤ → ℝ)).PosDef) :
    thetaG (S.map ((↑) : ℤ → ℝ)) (oneMat I) ≠ 0 := by
  have hsum := summable_thetaG hS oneMat_I_mem
  set r : Matrix (Fin (2 * k)) (Fin 1) ℤ → ℝ := fun X => -(π * ∑ i, ∑ j, (X i 0 : ℝ) * S i j * X j 0) with hr
  have hterm : ∀ X, cexp (thetaArg (S.map ((↑) : ℤ → ℝ)) (oneMat I) (cZ X)) = cexp ((r X : ℝ) : ℂ) := fun X => by
    rw [thetaArg_oneMat_I]
  simp only [hterm] at hsum
  have hsum' : Summable fun X => Real.exp (r X) := by
    refine hsum.congr fun X => ?_
    rw [Complex.norm_exp]; simp
  have hre : (thetaG (S.map ((↑) : ℤ → ℝ)) (oneMat I)).re = ∑' X, Real.exp (r X) := by
    unfold thetaG
    simp only [hterm]
    have hs : Summable fun X => cexp ((r X : ℝ) : ℂ) := hsum.of_norm
    rw [Complex.re_tsum hs]
    exact tsum_congr fun X => Complex.exp_ofReal_re _
  have h1 : (1 : ℝ) ≤ ∑' X, Real.exp (r X) := by
    have := hsum'.le_tsum 0 (fun j _ => (Real.exp_pos _).le)
    simpa [hr] using this
  intro h0
  rw [h0] at hre
  simp at hre
  linarith

end

/-- **The rank of an even unimodular positive definite lattice is divisible by 8.** Let
$S \in M_{2k}(\mathbb Z)$ be symmetric, positive definite, with even diagonal and $\det S = 1$. Then $4 \mid k$, i.e. the
rank $N = 2k$ is divisible by $8$.

Hypotheses: `hSsymm` ($S^{\mathsf T} = S$), `hSeven` (every diagonal entry $S_{ii}$ is even), `hS` ($S$, as a real matrix,
is positive definite), `hdet` ($\det S = 1$). Unconditional (uses only `thetaG_neg_inv` and `thetaG_add_int`). -/
@[kb "serre1973" "Ch. VII, §6.1, Thm. 2 (the rank of an even unimodular positive definite lattice is divisible by 8) [unverified]"]
theorem four_dvd_of_evenUnimodular (k : ℕ) {S : Matrix (Fin (2 * k)) (Fin (2 * k)) ℤ} (hSsymm : Sᵀ = S)
    (hSeven : ∀ i, Even (S i i)) (hS : (S.map ((↑) : ℤ → ℝ)).PosDef) (hdet : S.det = 1) : 4 ∣ k := by
  have hI0 : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hI1 : (I : ℂ) + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have h := thetaG_phi_fixed hSsymm hSeven hS hdet oneMat_I_mem hI0 hI1
  have hne := thetaG_oneMat_I_ne hS
  have hpow : (-I : ℂ) ^ k = 1 := by
    have : ((-I) ^ k - 1) * thetaG (S.map ((↑) : ℤ → ℝ)) (oneMat I) = 0 := by
      rw [sub_mul, ← h]; ring
    rcases mul_eq_zero.mp this with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hne
  have h4 : (-I : ℂ) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]; simp
  have hk : k = 4 * (k / 4) + k % 4 := (Nat.div_add_mod k 4).symm
  have hr : (-I : ℂ) ^ (k % 4) = 1 := by
    have := hpow
    rw [hk, pow_add, pow_mul, h4, one_pow, one_mul] at this
    exact this
  have hlt : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  apply Nat.dvd_of_mod_eq_zero
  interval_cases hm : k % 4
  · rfl
  · exfalso
    have := congrArg Complex.re hr
    simp at this
  · exfalso
    rw [show (-I : ℂ) ^ 2 = -1 by rw [neg_sq]; simp] at hr
    norm_num at hr
  · exfalso
    have h3 : (-I : ℂ) ^ 3 = I := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ]; simp
    rw [h3] at hr
    have := congrArg Complex.im hr
    simp at this

/-- **The genus-$g$ theta series of an even unimodular lattice is a Siegel modular form of weight $N/2$**, without
the divisibility hypothesis: `thetaG_sp` with $4 \mid k$ discharged by `four_dvd_of_evenUnimodular`. Let
$S \in M_{2k}(\mathbb Z)$ be symmetric positive definite with even diagonal and $\det S = 1$, and assume the named input
`SpZGeneration g`. Then for every $\gamma \in \mathrm{Sp}_{2g}(\mathbb Z)$ and $Z \in \mathbb H_g$: $\det(CZ + D) \ne 0$,
$\gamma\langle Z\rangle \in \mathbb H_g$ and $\Theta_S(\gamma\langle Z\rangle) = \det(CZ + D)^k\,\Theta_S(Z)$. -/
@[kb "freitag1983" "Ch. I, Anhang (the theta series of an even unimodular lattice is a modular form of weight $m/2$ for $\\mathrm{Sp}_n(\\mathbb Z)$) [unverified]"]
theorem thetaG_sp' {g : ℕ} (hgen : SpZGeneration g) (k : ℕ) {S : Matrix (Fin (2 * k)) (Fin (2 * k)) ℤ}
    (hSsymm : Sᵀ = S) (hSeven : ∀ i, Even (S i i)) (hS : (S.map ((↑) : ℤ → ℝ)).PosDef) (hdet : S.det = 1)
    (γ : SpZ g) {Z : Matrix (Fin g) (Fin g) ℂ} (hZ : Z ∈ siegelH g) :
    IsUnit (jG γ Z).det ∧ actG γ Z ∈ siegelH g ∧
      thetaG (S.map ((↑) : ℤ → ℝ)) (actG γ Z) = (jG γ Z).det ^ k * thetaG (S.map ((↑) : ℤ → ℝ)) Z :=
  thetaG_sp hgen k hSsymm hSeven hS hdet (four_dvd_of_evenUnimodular k hSsymm hSeven hS hdet) γ hZ

/-- **The genus-$g$ theta series of an even unimodular lattice is a Siegel modular form of weight $N/2$**
(unconditional). Let $S \in M_{2k}(\mathbb Z)$ be symmetric, positive definite, with even diagonal and $\det S = 1$
($N = 2k$). Then for every $\gamma = \begin{pmatrix}A&B\\C&D\end{pmatrix} \in \mathrm{Sp}_{2g}(\mathbb Z)$ and
$Z \in \mathbb H_g$: $\det(CZ + D) \ne 0$, $\gamma\langle Z\rangle = (AZ + B)(CZ + D)^{-1} \in \mathbb H_g$ and
$$\Theta_S(\gamma\langle Z\rangle) = \det(CZ + D)^k\,\Theta_S(Z).$$
This is `thetaG_sp'` with the named input `SpZGeneration g` discharged by `spZGeneration`. -/
@[kb "freitag1983" "Ch. I, Anhang (the theta series of an even unimodular lattice is a modular form of weight $m/2$ for $\\mathrm{Sp}_n(\\mathbb Z)$) [unverified]"]
theorem thetaG_sp_uncond {g : ℕ} (k : ℕ) {S : Matrix (Fin (2 * k)) (Fin (2 * k)) ℤ}
    (hSsymm : Sᵀ = S) (hSeven : ∀ i, Even (S i i)) (hS : (S.map ((↑) : ℤ → ℝ)).PosDef) (hdet : S.det = 1)
    (γ : SpZ g) {Z : Matrix (Fin g) (Fin g) ℂ} (hZ : Z ∈ siegelH g) :
    IsUnit (jG γ Z).det ∧ actG γ Z ∈ siegelH g ∧
      thetaG (S.map ((↑) : ℤ → ℝ)) (actG γ Z) = (jG γ Z).det ^ k * thetaG (S.map ((↑) : ℤ → ℝ)) Z :=
  thetaG_sp' (spZGeneration g) k hSsymm hSeven hS hdet γ hZ

end QuadFormsKB.WeilRep.Genus
