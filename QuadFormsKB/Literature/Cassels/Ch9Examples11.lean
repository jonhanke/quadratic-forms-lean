/-
# Cassels, Chapter 9, Example 12 (iv) and Example 13: the orbit formula, the prime 2, properly versus improperly primitive

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 9, *Examples*, Ex. 12 (iv) and Ex. 13, pp. 164-165.
This file builds on `Ch9Examples10.lean` (Example 12 (i)-(iii) and the definitions `ImpMat`, `ProMat`, `theta`, `psi`,
`Emap`, `transport`, `hcl`, `hClasses`, `hPro`, `hImp`).

**Conventions.** Indices are $0$-based (Cassels' $x_1, x_2$ are $x_0, x_1$). A binary form is its Gram matrix
$H = \begin{pmatrix} a & b \\ b & c\end{pmatrix}$ (classical convention: integral means $a, b, c \in \mathbb Z$, primitive
means $\gcd(a, b, c) = 1$, determinant $ac - b^{2}$). *Properly primitive* means primitive with $a$ or $c$ odd, *improperly
primitive* means primitive with $a$ and $c$ both even (then $b$ is odd). `hClasses m` is Cassels' $h(m)$ (all proper
classes of primitive forms of determinant $m$), `hPro m` and `hImp m` count the properly and improperly primitive ones.

**Proves**
* `ex13_i` (**Ex. 13 (i)**): for $d \equiv 3 \pmod 4$, $h_{\mathrm{pro}}(d) = 3\, h_{\mathrm{imp}}(d)$ in the exceptional cases
  ($d \equiv 3 \bmod 8$ and ($d > 3$, or $d < 0$ with every solution of $t^2 + du^2 = 4$ having $t$ even)) and
  $h_{\mathrm{pro}}(d) = h_{\mathrm{imp}}(d)$ otherwise; the map $\psi$ sends a properly primitive form to the improperly
  primitive form on the sublattice of index $2$ where it is even, and its fibres have $1$ or $3$ elements;
* `ex12_iv_orbits` (**Ex. 12 (iv)**, every $d \ne 0$ and every prime $p$): $h(d p^2)$ is the number of pairs (class of
  determinant $d$, orbit of the proper automorphs on the non-vanishing lines). Explicit consequences, with
  $N = p - (-d/p)$: `ex12_iv_square` ($d = -k^2$: $h(dp^2) = N h(d)$, only the automorphs $\pm I$),
  `ex12_iv_one` ($d = 1$: $2 h(p^2) = N h(1)$), `ex12_iv_three` and `ex12_iv_three_total`
  ($d = 3$: $3 h(3p^2) = N (3 h_{\mathrm{pro}}(3) + h_{\mathrm{imp}}(3)) = 2N h(3)$). For $d < 0$ not a square only the
  orbit formula `ex12_iv_orbits` is given (the automorph group is $\pm 1$ times an infinite cyclic group, Pell equation);
* `ex13_ii` (**Ex. 13 (ii)**, $p = 2$): $h(4d) = 2\, h_{\mathrm{pro}}(d)$ for $d \ge 2$; `ex13_ii_improper`: no improperly
  primitive form has determinant divisible by $4$; `ex13_ii_lattice`: a lattice carrying a properly primitive form of
  determinant $d$ has $2$ sublattices of index $2$ carrying a primitive form of determinant $4d$, an improperly primitive
  one has none.

**Method.** The lines modulo $p$ are the sublattices $C_\rho \mathbb Z^2$ of `Ch9Examples10.lean`; the key tool is the
transport lemma `transport` (equal classes of sublattice forms come from proper automorphs of the form, with
$U C_{\rho'} = C_\rho V$). Orbit sizes are computed from the parametrization of the proper automorphs by $(t, \mu)$ with
$t^2 + d\mu^2 = 4$ (`aut_param`, Cassels Ch. 13 §3) and from `no_fixed_of_param` (eigenvectors of
$\tfrac12(t + \mu J)$, $\mu = \pm 1$, are isotropic, so no non-vanishing line is fixed). Finiteness of the class numbers
is `finite_classes` (from `Ch9Sec3Finite`).

**Errata and updates** (see also `Ch9Examples10.lean`).
* *Update* (Ex. 12 (iv), $-d$ a square): the book calls this case special; for $d = -k^{2}$ the proper automorphs are only
  $\pm I$, so (iii) holds unchanged (`ex12_iv_square`); special treatment is only needed for the Pell equation of the
  other negative $d$.
* *Update* (Ex. 13 (ii)): for $p = 2$ a primitive form of determinant $4d$ is always properly primitive, so only the
  properly primitive forms of determinant $d$ have sublattices of the required kind.
* The formulas were checked numerically (Python, reduced definite forms) for $d \le 59$ and $p \le 13$.
-/

import QuadFormsKB.Literature.Cassels.Ch9Examples10
import QuadFormsKB.Literature.Cassels.Ch9Sec3Finite

open Matrix QuadFormsKB.Siegel.Ch9Ex12

namespace QuadFormsKB.Siegel.Ch9Ex13

/-- Helper: $\det C_\rho = 2$. -/
theorem det_C2 (ρ : Option (ZMod 2)) : (Cρ 2 ρ).det = 2 := by
  have := det_Cρ' (p := 2) ρ
  simpa using this

/-- Helper: a proper automorph-free line move: for $\det U = 1$ and a line `σ`, $U C_\sigma = C_\tau W$ for a line `τ` and $\det W = 1$. -/
theorem sl_line (U : Matrix (Fin 2) (Fin 2) ℤ) (hU : U.det = 1) (σ : Option (ZMod 2)) :
    ∃ (τ : Option (ZMod 2)) (W : Matrix (Fin 2) (Fin 2) ℤ), W.det = 1 ∧ U * Cρ 2 σ = Cρ 2 τ * W := by
  obtain ⟨τ, W, hW, h⟩ := exists_ρ_mul (p := 2) (U * Cρ 2 σ) (by rw [det_mul, hU, det_C2]; simp)
  exact ⟨τ, W, hW, h⟩

/-- Helper: halving a doubled matrix. -/
theorem halfM_two_smul (M : Matrix (Fin 2) (Fin 2) ℤ) : halfM ((2 : ℤ) • M) = M := by
  ext i j
  simp [halfM]

/-- Helper: $C_\rho \operatorname{adj}(C_\rho) = 2 I$. -/
theorem C_mul_adj (ρ : Option (ZMod 2)) : Cρ 2 ρ * (Cρ 2 ρ).adjugate = (2 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [Matrix.mul_adjugate, det_C2]

/-- Helper: $\operatorname{adj}(C_\rho) C_\rho = 2 I$. -/
theorem adj_mul_C (ρ : Option (ZMod 2)) : (Cρ 2 ρ).adjugate * Cρ 2 ρ = (2 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [Matrix.adjugate_mul, det_C2]

/-- Helper: the inverse of a determinant one matrix is its adjugate; transposition/conjugation identity. -/
theorem conj_adj {V : Matrix (Fin 2) (Fin 2) ℤ} (hV : V.det = 1) (H : Matrix (Fin 2) (Fin 2) ℤ) :
    Vᵀ * (V.adjugateᵀ * H * V.adjugate) * V = H := by
  obtain ⟨h1, h2⟩ := adj_mul_self V hV
  calc Vᵀ * (V.adjugateᵀ * H * V.adjugate) * V = (V.adjugate * V)ᵀ * H * (V.adjugate * V) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = H := by rw [h2]; simp

/-- Helper: the other conjugation identity. -/
theorem conj_adj' {V : Matrix (Fin 2) (Fin 2) ℤ} (hV : V.det = 1) (H : Matrix (Fin 2) (Fin 2) ℤ) :
    V.adjugateᵀ * (Vᵀ * H * V) * V.adjugate = H := by
  obtain ⟨h1, h2⟩ := adj_mul_self V hV
  calc V.adjugateᵀ * (Vᵀ * H * V) * V.adjugate = (V * V.adjugate)ᵀ * H * (V * V.adjugate) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = H := by rw [h1]; simp


/-! ### The improperly primitive form attached to a properly primitive one -/

/-- Helper: explicit entries of $\psi(G)$ when $G_{00}$ is even. -/
theorem psi_case0 {G : Matrix (Fin 2) (Fin 2) ℤ} (hs : Gᵀ = G) (h : (2 : ℤ) ∣ G 0 0) :
    psi G = !![G 0 0 / 2, G 0 1; G 0 1, 2 * G 1 1] := by
  unfold psi rhoOf
  rw [if_pos h, gramG_some hs]
  have h0v : (0 : ZMod 2).val = 0 := rfl
  rw [h0v]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [halfM] <;> omega

/-- Helper: explicit entries of $\psi(G)$ when $G_{00}$ is odd and $G_{11}$ is even. -/
theorem psi_caseN {G : Matrix (Fin 2) (Fin 2) ℤ} (hs : Gᵀ = G) (h0 : ¬ (2 : ℤ) ∣ G 0 0) (h1 : (2 : ℤ) ∣ G 1 1) :
    psi G = !![2 * G 0 0, G 0 1; G 0 1, G 1 1 / 2] := by
  unfold psi rhoOf
  rw [if_neg h0, if_pos h1, gramG_none hs]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [halfM] <;> omega

/-- Helper: explicit entries of $\psi(G)$ when $G_{00}$ and $G_{11}$ are both odd. -/
theorem psi_case1 {G : Matrix (Fin 2) (Fin 2) ℤ} (hs : Gᵀ = G) (h0 : ¬ (2 : ℤ) ∣ G 0 0) (h1 : ¬ (2 : ℤ) ∣ G 1 1) :
    psi G = !![(G 0 0 + 2 * G 0 1 + G 1 1) / 2, G 0 1 + G 1 1; G 0 1 + G 1 1, 2 * G 1 1] := by
  unfold psi rhoOf
  rw [if_neg h0, if_neg h1, gramG_some hs]
  have h1v : (1 : ZMod 2).val = 1 := rfl
  rw [h1v]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [halfM] <;> omega

/-- Helper: the attached form is improperly primitive in the sense of its entries: $\psi_{01}$ is odd and
the diagonal entries are even. -/
theorem psi_shape {d : ℤ} (hd : d % 4 = 3) (G : ProMat d) :
    ¬ (2 : ℤ) ∣ (psi G.1.1) 0 1 ∧ (2 : ℤ) ∣ (psi G.1.1) 0 0 ∧ (2 : ℤ) ∣ (psi G.1.1) 1 1 := by
  have hs := G.1.2.1
  have hdet := det_ProMat G
  have hmod : (G.1.1 0 0 * G.1.1 1 1 - G.1.1 0 1 * G.1.1 0 1) % 4 = 3 := by rw [hdet]; exact hd
  obtain ⟨c1, c2, c3⟩ := parity_cases _ _ _ hmod
  by_cases h0 : (2 : ℤ) ∣ G.1.1 0 0
  · have h1 : ¬ (2 : ℤ) ∣ G.1.1 1 1 := fun h => G.2 ⟨h0, h⟩
    obtain ⟨hb, h4⟩ := c1 h0 h1
    rw [psi_case0 hs h0]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.head_cons]
    refine ⟨hb, ?_, ⟨G.1.1 1 1, rfl⟩⟩
    omega
  · by_cases h1 : (2 : ℤ) ∣ G.1.1 1 1
    · obtain ⟨hb, h4⟩ := c2 h0 h1
      rw [psi_caseN hs h0 h1]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.head_cons]
      refine ⟨hb, ⟨G.1.1 0 0, rfl⟩, ?_⟩
      omega
    · obtain ⟨hb, h4⟩ := c3 h0 h1
      rw [psi_case1 hs h0 h1]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.head_cons]
      refine ⟨?_, ?_, ⟨G.1.1 1 1, rfl⟩⟩
      · omega
      · omega

/-- Helper: the attached form is primitive. -/
theorem psi_prim {d : ℤ} (hd : d % 4 = 3) (G : ProMat d) :
    ∀ k : ℤ, (∀ i j, k ∣ (psi G.1.1) i j) → IsUnit k := by
  intro k hk
  have hM : ∀ i j, k ∣ ((Cρ 2 (rhoOf G.1.1))ᵀ * G.1.1 * Cρ 2 (rhoOf G.1.1)) i j := by
    intro i j
    rw [← two_smul_psi G]
    simpa using (hk i j).mul_left 2
  have hid : (Cρ 2 (rhoOf G.1.1)).adjugateᵀ * ((Cρ 2 (rhoOf G.1.1))ᵀ * G.1.1 * Cρ 2 (rhoOf G.1.1)) *
      (Cρ 2 (rhoOf G.1.1)).adjugate = (4 : ℤ) • G.1.1 := by
    have : (Cρ 2 (rhoOf G.1.1)).adjugateᵀ * ((Cρ 2 (rhoOf G.1.1))ᵀ * G.1.1 * Cρ 2 (rhoOf G.1.1)) *
        (Cρ 2 (rhoOf G.1.1)).adjugate =
        (Cρ 2 (rhoOf G.1.1) * (Cρ 2 (rhoOf G.1.1)).adjugate)ᵀ * G.1.1 *
          (Cρ 2 (rhoOf G.1.1) * (Cρ 2 (rhoOf G.1.1)).adjugate) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, C_mul_adj, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul]
    norm_num
  have h4H : ∀ i j, k ∣ 4 * G.1.1 i j := by
    intro i j
    have := dvd_mul3 k (Cρ 2 (rhoOf G.1.1)).adjugateᵀ _ (Cρ 2 (rhoOf G.1.1)).adjugate hM i j
    rw [hid] at this
    simpa using this
  obtain ⟨x, y, z, hxyz⟩ := primMat_bezout G.1
  have hk4 : k ∣ 4 := by
    have : (4 : ℤ) = 4 * G.1.1 0 0 * x + 4 * G.1.1 0 1 * y + 4 * G.1.1 1 1 * z := by linear_combination -4 * hxyz
    rw [this]
    exact dvd_add (dvd_add ((h4H 0 0).mul_right x) ((h4H 0 1).mul_right y)) ((h4H 1 1).mul_right z)
  have hodd : ¬ (2 : ℤ) ∣ k := fun h2 => (psi_shape hd G).1 (h2.trans (hk 0 1))
  exact isUnit_of_dvd_four_odd hk4 hodd

/-- The improperly primitive form of determinant $d$ attached to a properly primitive form $G$ of determinant $d$
($d \equiv 3 \bmod 4$): the Gram matrix $\psi(G) = C_{\rho}^{\mathsf T} G C_{\rho} / 2$ of the unique index-$2$ sublattice on which $G$ is even. -/
def psiImp {d : ℤ} (hd : d % 4 = 3) (G : ProMat d) : ImpMat d :=
  ⟨⟨psi G.1.1, psi_sym G, psi_det G, psi_prim hd G⟩, (psi_shape hd G).2.1, (psi_shape hd G).2.2⟩

/-- Helper: the attached form of `G` is computed from any line on which $G$ is even. -/
theorem psi_of_ev {d : ℤ} (G : ProMat d) {τ : Option (ZMod 2)} (h : Ev G.1.1 τ) :
    psi G.1.1 = halfM ((Cρ 2 τ)ᵀ * G.1.1 * Cρ 2 τ) := by
  have := (ev_iff_rhoOf G.1.2.1 G.2 τ).1 h
  rw [this]; rfl

/-- Helper: the sublattice form $\theta(H, \kappa)$ of an improperly primitive $H$ on a valid line is properly primitive. -/
def thetaPro {d : ℤ} (H : ImpMat d) (κ : Option (ZMod 2)) (hκ : Valid H κ) : ProMat d :=
  ⟨⟨Ch9Ex12.theta H.1.1 κ, theta_sym H κ, theta_det H κ, theta_prim H κ⟩, hκ⟩

/-- Helper: from $G = \theta(H, \kappa)$ one recovers $H$: $\psi(G) = V^{\mathsf T} H V$ with $\det V = 1$,
and $\operatorname{adj}(C_\kappa) = C_\sigma V^{-1}$ where $\sigma$ is the line on which $G$ is even. -/
theorem psi_theta {d : ℤ} (H : ImpMat d) (κ : Option (ZMod 2)) (hκ : Valid H κ) :
    ∃ (σ : Option (ZMod 2)) (V : Matrix (Fin 2) (Fin 2) ℤ), V.det = 1 ∧
      (Cρ 2 κ).adjugate = Cρ 2 σ * V ∧ Ev (thetaPro H κ hκ).1.1 σ ∧
      rhoOf (thetaPro H κ hκ).1.1 = σ ∧
      psi (thetaPro H κ hκ).1.1 = V.adjugateᵀ * H.1.1 * V.adjugate := by
  obtain ⟨σ, V, hV, hA⟩ := exists_ρ_mul (p := 2) (Cρ 2 κ).adjugate (by
    rw [det_adj]; simpa using det_C2 κ)
  have hG : (thetaPro H κ hκ).1.1 = Ch9Ex12.theta H.1.1 κ := rfl
  have h2 : (2 : ℤ) • Ch9Ex12.theta H.1.1 κ = (Cρ 2 κ)ᵀ * H.1.1 * Cρ 2 κ := two_smul_theta H κ
  -- Aᵀ G A = 2 H
  have hAGA : (Cρ 2 κ).adjugateᵀ * ((2 : ℤ) • Ch9Ex12.theta H.1.1 κ) * (Cρ 2 κ).adjugate = (4 : ℤ) • H.1.1 := by
    rw [h2]
    have : (Cρ 2 κ).adjugateᵀ * ((Cρ 2 κ)ᵀ * H.1.1 * Cρ 2 κ) * (Cρ 2 κ).adjugate =
        (Cρ 2 κ * (Cρ 2 κ).adjugate)ᵀ * H.1.1 * (Cρ 2 κ * (Cρ 2 κ).adjugate) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, C_mul_adj, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul]
    norm_num
  have hCG : (Cρ 2 σ)ᵀ * Ch9Ex12.theta H.1.1 κ * Cρ 2 σ = (2 : ℤ) • (V.adjugateᵀ * H.1.1 * V.adjugate) := by
    have h3 : Vᵀ * ((Cρ 2 σ)ᵀ * Ch9Ex12.theta H.1.1 κ * Cρ 2 σ) * V = (2 : ℤ) • H.1.1 := by
      have e : (Cρ 2 κ).adjugateᵀ * ((2 : ℤ) • Ch9Ex12.theta H.1.1 κ) * (Cρ 2 κ).adjugate =
          (2 : ℤ) • (Vᵀ * ((Cρ 2 σ)ᵀ * Ch9Ex12.theta H.1.1 κ * Cρ 2 σ) * V) := by
        rw [hA]
        simp only [Matrix.transpose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      rw [e] at hAGA
      have : (2 : ℤ) • (Vᵀ * ((Cρ 2 σ)ᵀ * Ch9Ex12.theta H.1.1 κ * Cρ 2 σ) * V) = (2 : ℤ) • ((2 : ℤ) • H.1.1) := by
        rw [hAGA, smul_smul]; norm_num
      exact smul_cancel (by norm_num) this
    have h4 : V.adjugateᵀ * (Vᵀ * ((Cρ 2 σ)ᵀ * Ch9Ex12.theta H.1.1 κ * Cρ 2 σ) * V) * V.adjugate =
        V.adjugateᵀ * ((2 : ℤ) • H.1.1) * V.adjugate := by rw [h3]
    rw [conj_adj' hV] at h4
    rw [h4]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  have hev : Ev (thetaPro H κ hκ).1.1 σ := by
    intro i j
    show (2 : ℤ) ∣ ((Cρ 2 σ)ᵀ * (thetaPro H κ hκ).1.1 * Cρ 2 σ) i j
    rw [hG, hCG]
    exact Dvd.intro ((V.adjugateᵀ * H.1.1 * V.adjugate) i j) (by simp)
  refine ⟨σ, V, hV, hA, hev, ((ev_iff_rhoOf (thetaPro H κ hκ).1.2.1 (thetaPro H κ hκ).2 σ).1 hev).symm, ?_⟩
  rw [psi_of_ev _ hev, hG, hCG, halfM_two_smul]

/-- Helper: conjugating a form with even diagonal by any integral matrix keeps the diagonal even. -/
theorem diag_even_conj {G X : Matrix (Fin 2) (Fin 2) ℤ} (hs : Gᵀ = G) (h0 : (2 : ℤ) ∣ G 0 0)
    (h1 : (2 : ℤ) ∣ G 1 1) : (2 : ℤ) ∣ (Xᵀ * G * X) 0 0 ∧ (2 : ℤ) ∣ (Xᵀ * G * X) 1 1 := by
  obtain ⟨α, hα⟩ := h0
  obtain ⟨γ, hγ⟩ := h1
  have h10 : G 1 0 = G 0 1 := by have := congrFun (congrFun hs 0) 1; simpa using this
  constructor
  · refine ⟨α * X 0 0 ^ 2 + G 0 1 * X 0 0 * X 1 0 + γ * X 1 0 ^ 2, ?_⟩
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hα, hγ]; ring
  · refine ⟨α * X 0 1 ^ 2 + G 0 1 * X 0 1 * X 1 1 + γ * X 1 1 ^ 2, ?_⟩
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hα, hγ]; ring

/-- Helper: the attached form respects proper equivalence: if $U^{\mathsf T} G U = G'$ with $\det U = 1$ then
$\psi(G') = W^{\mathsf T} \psi(G) W$ for some $W$ of determinant $1$. -/
theorem psi_conj {d : ℤ} (G G' : ProMat d) (U : Matrix (Fin 2) (Fin 2) ℤ) (hU : U.det = 1)
    (h : Uᵀ * G.1.1 * U = G'.1.1) :
    ∃ W : Matrix (Fin 2) (Fin 2) ℤ, W.det = 1 ∧ psi G'.1.1 = Wᵀ * psi G.1.1 * W ∧
      U * Cρ 2 (rhoOf G'.1.1) = Cρ 2 (rhoOf G.1.1) * W := by
  obtain ⟨τ, W0, hW0, hτ⟩ := sl_line U.adjugate (by rw [det_adj]; exact hU) (rhoOf G.1.1)
  obtain ⟨hUa, hUa'⟩ := adj_mul_self U hU
  obtain ⟨hWa, hWa'⟩ := adj_mul_self W0 hW0
  have hUC : U * Cρ 2 τ = Cρ 2 (rhoOf G.1.1) * W0.adjugate := by
    calc U * Cρ 2 τ = U * (Cρ 2 τ * (W0 * W0.adjugate)) := by rw [hWa, Matrix.mul_one]
      _ = U * (Cρ 2 τ * W0) * W0.adjugate := by simp only [Matrix.mul_assoc]
      _ = U * (U.adjugate * Cρ 2 (rhoOf G.1.1)) * W0.adjugate := by rw [← hτ]
      _ = Cρ 2 (rhoOf G.1.1) * W0.adjugate := by rw [← Matrix.mul_assoc U, hUa, Matrix.one_mul]
  have key : (Cρ 2 τ)ᵀ * G'.1.1 * Cρ 2 τ = (2 : ℤ) • (W0.adjugateᵀ * psi G.1.1 * W0.adjugate) := by
    rw [← h]
    calc (Cρ 2 τ)ᵀ * (Uᵀ * G.1.1 * U) * Cρ 2 τ = (U * Cρ 2 τ)ᵀ * G.1.1 * (U * Cρ 2 τ) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = W0.adjugateᵀ * ((Cρ 2 (rhoOf G.1.1))ᵀ * G.1.1 * Cρ 2 (rhoOf G.1.1)) * W0.adjugate := by
          rw [hUC]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by
          rw [← two_smul_psi G]
          simp only [Matrix.mul_smul, Matrix.smul_mul]
  have hev : Ev G'.1.1 τ := fun i j => by
    show (2 : ℤ) ∣ ((Cρ 2 τ)ᵀ * G'.1.1 * Cρ 2 τ) i j
    rw [key]
    exact Dvd.intro ((W0.adjugateᵀ * psi G.1.1 * W0.adjugate) i j) (by simp)
  have hτ' : τ = rhoOf G'.1.1 := (ev_iff_rhoOf G'.1.2.1 G'.2 τ).1 hev
  refine ⟨W0.adjugate, by rw [det_adj]; exact hW0, ?_, by rw [← hτ']; exact hUC⟩
  rw [psi_of_ev G' hev, key, halfM_two_smul]

/-- Helper: every properly primitive form is properly equivalent to a form $\theta(\psi(G), \kappa)$; moreover
$\kappa$ is a valid line for $\psi(G)$. -/
theorem theta_psi {d : ℤ} (hd : d % 4 = 3) (G : ProMat d) :
    ∃ (κ : Option (ZMod 2)) (hκ : Valid (psiImp hd G) κ) (V : Matrix (Fin 2) (Fin 2) ℤ), V.det = 1 ∧
      G.1.1 = Vᵀ * Ch9Ex12.theta (psiImp hd G).1.1 κ * V := by
  set ρ0 := rhoOf G.1.1 with hρ0
  obtain ⟨κ, V, hV, hA⟩ := exists_ρ_mul (p := 2) (Cρ 2 ρ0).adjugate (by rw [det_adj]; simpa using det_C2 ρ0)
  have hψ : (psiImp hd G).1.1 = psi G.1.1 := rfl
  have h4 : (Cρ 2 ρ0).adjugateᵀ * ((2 : ℤ) • psi G.1.1) * (Cρ 2 ρ0).adjugate = (4 : ℤ) • G.1.1 := by
    rw [two_smul_psi G]
    have : (Cρ 2 ρ0).adjugateᵀ * ((Cρ 2 ρ0)ᵀ * G.1.1 * Cρ 2 ρ0) * (Cρ 2 ρ0).adjugate =
        (Cρ 2 ρ0 * (Cρ 2 ρ0).adjugate)ᵀ * G.1.1 * (Cρ 2 ρ0 * (Cρ 2 ρ0).adjugate) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, C_mul_adj, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul]
    norm_num
  have h5 : Vᵀ * ((Cρ 2 κ)ᵀ * psi G.1.1 * Cρ 2 κ) * V = (2 : ℤ) • G.1.1 := by
    have e : (Cρ 2 ρ0).adjugateᵀ * ((2 : ℤ) • psi G.1.1) * (Cρ 2 ρ0).adjugate =
        (2 : ℤ) • (Vᵀ * ((Cρ 2 κ)ᵀ * psi G.1.1 * Cρ 2 κ) * V) := by
      rw [hA]
      simp only [Matrix.transpose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [e] at h4
    have : (2 : ℤ) • (Vᵀ * ((Cρ 2 κ)ᵀ * psi G.1.1 * Cρ 2 κ) * V) = (2 : ℤ) • ((2 : ℤ) • G.1.1) := by
      rw [h4, smul_smul]; norm_num
    exact smul_cancel (by norm_num) this
  have h6 : (Cρ 2 κ)ᵀ * psi G.1.1 * Cρ 2 κ = (2 : ℤ) • (V.adjugateᵀ * G.1.1 * V.adjugate) := by
    have h7 : V.adjugateᵀ * (Vᵀ * ((Cρ 2 κ)ᵀ * psi G.1.1 * Cρ 2 κ) * V) * V.adjugate =
        V.adjugateᵀ * ((2 : ℤ) • G.1.1) * V.adjugate := by rw [h5]
    rw [conj_adj' hV] at h7
    rw [h7]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  have hθ : Ch9Ex12.theta (psiImp hd G).1.1 κ = V.adjugateᵀ * G.1.1 * V.adjugate := by
    show halfM ((Cρ 2 κ)ᵀ * (psiImp hd G).1.1 * Cρ 2 κ) = _
    rw [hψ, h6, halfM_two_smul]
  have hval : Valid (psiImp hd G) κ := by
    intro hh
    rw [hθ] at hh
    have hs : (V.adjugateᵀ * G.1.1 * V.adjugate)ᵀ = V.adjugateᵀ * G.1.1 * V.adjugate := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, G.1.2.1, Matrix.mul_assoc]
    have := diag_even_conj (X := V) hs hh.1 hh.2
    rw [conj_adj hV] at this
    exact G.2 this
  refine ⟨κ, hval, V, hV, ?_⟩
  rw [hθ, conj_adj hV]

/-! ### The fibres of $\psi$ over a class of improperly primitive forms -/

/-- Helper: the sublattice forms of properly equivalent improperly primitive forms are properly equivalent
(up to the permutation of the lines): if $H_2 = W^{\mathsf T} H_1 W$ then for every line $\kappa$ there is a line
$\kappa'$ with $\theta(H_2, \kappa) = X^{\mathsf T} \theta(H_1, \kappa') X$, $\det X = 1$; and $\kappa'$ is valid for
$H_1$ whenever $\kappa$ is valid for $H_2$. -/
theorem theta_cov {d : ℤ} (H1 H2 : ImpMat d) (W : Matrix (Fin 2) (Fin 2) ℤ) (hW : W.det = 1)
    (h : H2.1.1 = Wᵀ * H1.1.1 * W) (κ : Option (ZMod 2)) :
    ∃ (κ' : Option (ZMod 2)) (X : Matrix (Fin 2) (Fin 2) ℤ), X.det = 1 ∧
      Ch9Ex12.theta H2.1.1 κ = Xᵀ * Ch9Ex12.theta H1.1.1 κ' * X ∧ (Valid H2 κ → Valid H1 κ') := by
  obtain ⟨κ', X, hX, hWC⟩ := sl_line W hW κ
  have e : (2 : ℤ) • Ch9Ex12.theta H2.1.1 κ = (2 : ℤ) • (Xᵀ * Ch9Ex12.theta H1.1.1 κ' * X) := by
    rw [two_smul_theta H2 κ]
    have : (2 : ℤ) • (Xᵀ * Ch9Ex12.theta H1.1.1 κ' * X) = Xᵀ * ((2 : ℤ) • Ch9Ex12.theta H1.1.1 κ') * X := by
      simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [this, two_smul_theta H1 κ', h]
    calc (Cρ 2 κ)ᵀ * (Wᵀ * H1.1.1 * W) * Cρ 2 κ = (W * Cρ 2 κ)ᵀ * H1.1.1 * (W * Cρ 2 κ) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hWC]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have hθ := smul_cancel (by norm_num) e
  refine ⟨κ', X, hX, hθ, fun hv hh => hv ?_⟩
  rw [hθ]
  exact diag_even_conj (theta_sym H1 κ') hh.1 hh.2

/-- Helper: the map $\psi$ on classes. -/
noncomputable def psiBar {d : ℤ} (hd : d % 4 = 3) : Quotient (proSetoid d) → Quotient (impSetoid d) :=
  Quotient.map (psiImp hd) (fun G G' h => by
    obtain ⟨U, hU, hUG⟩ := h
    obtain ⟨W, hW, hWψ, -⟩ := psi_conj G G' U hU hUG
    exact ⟨W, hW, hWψ.symm⟩)

/-- Helper: the class of the form $\theta(H, \kappa)$ for a valid line $\kappa$. -/
def thetaClass {d : ℤ} (H : ImpMat d) (κ : Option (ZMod 2)) (hκ : Valid H κ) : Quotient (proSetoid d) :=
  Quotient.mk _ (thetaPro H κ hκ)

/-- Helper: $\psi$ of a class $\theta(H, \kappa)$ is the class of $H$. -/
theorem psiBar_thetaClass {d : ℤ} (hd : d % 4 = 3) (H : ImpMat d) (κ : Option (ZMod 2)) (hκ : Valid H κ) :
    psiBar hd (thetaClass H κ hκ) = Quotient.mk _ H := by
  obtain ⟨σ, V, hV, -, -, -, hψ⟩ := psi_theta H κ hκ
  apply Quotient.sound
  refine ⟨V, hV, ?_⟩
  show Vᵀ * psi (thetaPro H κ hκ).1.1 * V = H.1.1
  rw [hψ]
  exact conj_adj hV _

/-- Helper: the fibre of $\psi$ over the class of $H$ consists of the classes $\theta(H, \kappa)$, $\kappa$ valid. -/
theorem psiBar_eq_iff {d : ℤ} (hd : d % 4 = 3) (H : ImpMat d) (x : Quotient (proSetoid d)) :
    psiBar hd x = Quotient.mk _ H ↔ ∃ (κ : Option (ZMod 2)) (hκ : Valid H κ), thetaClass H κ hκ = x := by
  constructor
  · induction x using Quotient.inductionOn with
    | _ G =>
      intro hx
      obtain ⟨U, hU, hUe⟩ := Quotient.exact hx
      obtain ⟨κ, hκ, V, hV, hGV⟩ := theta_psi hd G
      have hH : (psiImp hd G).1.1 = U.adjugateᵀ * H.1.1 * U.adjugate := by
        rw [← hUe, conj_adj' hU]
      obtain ⟨κ', X, hX, hθ, hvalid⟩ := theta_cov H (psiImp hd G) U.adjugate (by rw [det_adj]; exact hU) hH κ
      refine ⟨κ', hvalid hκ, Quotient.sound ⟨X * V, by rw [Matrix.det_mul, hX, hV, one_mul], ?_⟩⟩
      show (X * V)ᵀ * Ch9Ex12.theta H.1.1 κ' * (X * V) = G.1.1
      rw [hGV, hθ]
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  · rintro ⟨κ, hκ, rfl⟩
    exact psiBar_thetaClass hd H κ hκ

/-! ### Counting -/

/-- Helper: cardinality of a domain from the cardinalities of the fibres of a map. -/
theorem mk_eq_mul_of_fibres {α β : Type} (f : α → β) (c : Cardinal.{0})
    (h : ∀ b : β, Cardinal.mk {a : α // f a = b} = c) :
    Cardinal.mk α = Cardinal.mk β * c := by
  rw [← Cardinal.mk_congr (Equiv.sigmaFiberEquiv f), Cardinal.mk_sigma]
  simp only [h]
  exact Cardinal.sum_const' _ _

/-- Helper: every improperly primitive form of determinant $d \equiv 3 \bmod 4$ has a valid line. -/
theorem exists_valid {d : ℤ} (hd : d % 4 = 3) (H : ImpMat d) : ∃ κ : Option (ZMod 2), Valid H κ := by
  have : d % 8 = 3 ∨ d % 8 = 7 := by omega
  rcases this with h | h
  · exact ⟨none, valid_three h H none⟩
  · exact (valid_seven h H).exists

/-- Helper: if the classes $\theta(H, \kappa)$ do not depend on the valid line $\kappa$, the fibre of $\psi$ over
the class of $H$ has exactly one element. -/
theorem fibre_one {d : ℤ} (hd : d % 4 = 3) (H : ImpMat d)
    (hconst : ∀ (κ κ' : Option (ZMod 2)) (hκ : Valid H κ) (hκ' : Valid H κ'),
      thetaClass H κ hκ = thetaClass H κ' hκ') :
    Cardinal.mk {x : Quotient (proSetoid d) // psiBar hd x = Quotient.mk _ H} = 1 := by
  obtain ⟨κ0, h0⟩ := exists_valid hd H
  have hne : Nonempty {x : Quotient (proSetoid d) // psiBar hd x = Quotient.mk _ H} :=
    ⟨⟨thetaClass H κ0 h0, psiBar_thetaClass hd H κ0 h0⟩⟩
  have hsub : Subsingleton {x : Quotient (proSetoid d) // psiBar hd x = Quotient.mk _ H} := by
    refine ⟨fun x y => Subtype.ext ?_⟩
    obtain ⟨κ, hκ, hx⟩ := (psiBar_eq_iff hd H x.1).1 x.2
    obtain ⟨κ', hκ', hy⟩ := (psiBar_eq_iff hd H y.1).1 y.2
    rw [← hx, ← hy]
    exact hconst κ κ' hκ hκ'
  exact Cardinal.mk_eq_one _

/-- Helper: if all three lines are valid and the classes $\theta(H, \kappa)$ for different lines are different,
the fibre of $\psi$ over the class of $H$ has exactly three elements. -/
theorem fibre_three {d : ℤ} (hd : d % 4 = 3) (hd8 : d % 8 = 3) (H : ImpMat d)
    (hinj : ∀ (κ κ' : Option (ZMod 2)) (hκ : Valid H κ) (hκ' : Valid H κ'),
      thetaClass H κ hκ = thetaClass H κ' hκ' → κ = κ') :
    Cardinal.mk {x : Quotient (proSetoid d) // psiBar hd x = Quotient.mk _ H} = 3 := by
  let Θ : Option (ZMod 2) → {x : Quotient (proSetoid d) // psiBar hd x = Quotient.mk _ H} :=
    fun κ => ⟨thetaClass H κ (valid_three hd8 H κ), psiBar_thetaClass hd H κ _⟩
  have hbij : Function.Bijective Θ := by
    constructor
    · intro κ κ' h
      exact hinj κ κ' _ _ (congrArg Subtype.val h)
    · intro x
      obtain ⟨κ, hκ, hx⟩ := (psiBar_eq_iff hd H x.1).1 x.2
      exact ⟨κ, Subtype.ext (by simpa [Θ] using hx)⟩
  rw [← Cardinal.mk_congr (Equiv.ofBijective Θ hbij), Cardinal.mk_fintype]
  have : Fintype.card (Option (ZMod 2)) = 3 := by simp
  rw [this]; norm_num

/-! ### Equal classes $\theta(H, \kappa)$ come from integral automorphs of $H$ -/

/-- Helper: if $\theta(H, \kappa)$ and $\theta(H, \kappa')$ are properly equivalent (via $U$) then there is an
integral automorph $Z$ of $H$ of determinant $1$ with $Z C_{\kappa'} = C_\kappa U$ (it carries the sublattice of
$\kappa'$ to that of $\kappa$). -/
theorem autom_of_equiv {d : ℤ} (H : ImpMat d) (κ κ' : Option (ZMod 2)) (hκ : Valid H κ) (hκ' : Valid H κ')
    (U : Matrix (Fin 2) (Fin 2) ℤ) (hU : U.det = 1)
    (hUe : Uᵀ * Ch9Ex12.theta H.1.1 κ * U = Ch9Ex12.theta H.1.1 κ') :
    ∃ Z : Matrix (Fin 2) (Fin 2) ℤ, Z.det = 1 ∧ Zᵀ * H.1.1 * Z = H.1.1 ∧
      Z * Cρ 2 κ' = Cρ 2 κ * U := by
  obtain ⟨σ, V, hV, hA, hev, hrho, hψ⟩ := psi_theta H κ hκ
  obtain ⟨σ', V', hV', hA', hev', hrho', hψ'⟩ := psi_theta H κ' hκ'
  obtain ⟨W, hW, hψW, hUC⟩ := psi_conj (thetaPro H κ hκ) (thetaPro H κ' hκ') U hU hUe
  rw [hrho, hrho'] at hUC
  obtain ⟨hVa, hVa'⟩ := adj_mul_self V hV
  have hCC : Cρ 2 κ * Cρ 2 σ = (2 : ℤ) • V.adjugate := by
    have h1 := C_mul_adj κ
    rw [hA] at h1
    calc Cρ 2 κ * Cρ 2 σ = Cρ 2 κ * Cρ 2 σ * (V * V.adjugate) := by rw [hVa, Matrix.mul_one]
      _ = (Cρ 2 κ * (Cρ 2 σ * V)) * V.adjugate := by simp only [Matrix.mul_assoc]
      _ = (2 : ℤ) • V.adjugate := by rw [h1, Matrix.smul_mul, Matrix.one_mul]
  have hZ2 : (2 : ℤ) • (V.adjugate * W * V') = Cρ 2 κ * U * (Cρ 2 κ').adjugate := by
    rw [hA']
    calc (2 : ℤ) • (V.adjugate * W * V') = ((2 : ℤ) • V.adjugate) * W * V' := by
          simp only [Matrix.smul_mul]
      _ = (Cρ 2 κ * Cρ 2 σ) * W * V' := by rw [hCC]
      _ = Cρ 2 κ * (Cρ 2 σ * W) * V' := by simp only [Matrix.mul_assoc]
      _ = Cρ 2 κ * (U * Cρ 2 σ') * V' := by rw [hUC]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hZC : V.adjugate * W * V' * Cρ 2 κ' = Cρ 2 κ * U := by
    have : (2 : ℤ) • (V.adjugate * W * V' * Cρ 2 κ') = (2 : ℤ) • (Cρ 2 κ * U) := by
      calc (2 : ℤ) • (V.adjugate * W * V' * Cρ 2 κ') = ((2 : ℤ) • (V.adjugate * W * V')) * Cρ 2 κ' := by
            simp only [Matrix.smul_mul]
        _ = Cρ 2 κ * U * ((Cρ 2 κ').adjugate * Cρ 2 κ') := by rw [hZ2]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [adj_mul_C]; simp only [Matrix.mul_smul, Matrix.mul_one]
    exact smul_cancel (by norm_num) this
  refine ⟨V.adjugate * W * V', ?_, ?_, hZC⟩
  · rw [Matrix.det_mul, Matrix.det_mul, det_adj, hV, hW, hV']; simp
  · rw [hψ, hψ'] at hψW
    calc (V.adjugate * W * V')ᵀ * H.1.1 * (V.adjugate * W * V') =
          V'ᵀ * (Wᵀ * (V.adjugateᵀ * H.1.1 * V.adjugate) * W) * V' := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = V'ᵀ * (V'.adjugateᵀ * H.1.1 * V'.adjugate) * V' := by rw [hψW]
      _ = H.1.1 := conj_adj hV' _

/-! ### The proper automorphs of a primitive binary form -/

/-- Helper: parametrization of the proper integral automorphs of a primitive binary form (Cassels, Ch. 13, §3, in
the form used in the proof of `aut_pm_one`): if $U^{\mathsf T} H U = H$, $\det U = 1$ ($H = (a, b; b, c)$ primitive of
determinant $d$) then there is an integer $\mu$ with $U_{00} - U_{11} = \mu b$, $2 U_{01} = \mu c$, $-2 U_{10} = \mu a$
and $(U_{00} + U_{11})^{2} + d \mu^{2} = 4$. -/
theorem aut_param {d : ℤ} (H : PrimMat d) (U : Matrix (Fin 2) (Fin 2) ℤ) (hU : U.det = 1)
    (hUH : Uᵀ * H.1 * U = H.1) :
    ∃ μ : ℤ, U 0 0 - U 1 1 = μ * H.1 0 1 ∧ 2 * U 0 1 = μ * H.1 1 1 ∧ -2 * U 1 0 = μ * H.1 0 0 ∧
      (U 0 0 + U 1 1) ^ 2 + d * μ ^ 2 = 4 := by
  obtain ⟨hs, hd, hpr⟩ := H.2
  have h1 : Uᵀ * H.1 = H.1 * U.adjugate := by
    obtain ⟨hm, -⟩ := adj_mul_self U hU
    calc Uᵀ * H.1 = Uᵀ * H.1 * (U * U.adjugate) := by rw [hm, Matrix.mul_one]
      _ = (Uᵀ * H.1 * U) * U.adjugate := by simp only [Matrix.mul_assoc]
      _ = H.1 * U.adjugate := by rw [hUH]
  obtain ⟨a, b, c, hHe⟩ : ∃ a b c : ℤ, H.1 = !![a, b; b, c] := ⟨_, _, _, sym_eta hs⟩
  rw [hHe] at h1 hd hpr
  rw [hHe]
  have hpr' : ∀ k : ℤ, k ∣ a → k ∣ b → k ∣ c → IsUnit k := fun k h1 h2 h3 => hpr k (by
    intro i j
    fin_cases i <;> fin_cases j <;> simpa)
  obtain ⟨u, v, w, z, hUe⟩ : ∃ u v w z : ℤ, U = !![u, v; w, z] := ⟨_, _, _, _, Matrix.eta_fin_two U⟩
  subst hUe
  rw [Matrix.det_fin_two_of] at hU
  rw [Matrix.det_fin_two_of] at hd
  rw [Matrix.adjugate_fin_two_of] at h1
  have e00 := congrFun (congrFun h1 0) 0
  have e01 := congrFun (congrFun h1 0) 1
  have e11 := congrFun (congrFun h1 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e11
  have E1 : a * (u - z) + 2 * b * w = 0 := by linarith
  have E2 : a * v + c * w = 0 := by linarith
  have E3 : c * (u - z) - 2 * b * v = 0 := by linarith
  obtain ⟨x, y, z', hxyz⟩ := bezout3 a b c hpr'
  set μ : ℤ := -2 * w * x + (u - z) * y + 2 * v * z' with hμ
  have hs' : u - z = μ * b := by
    rw [hμ]; linear_combination (-(u - z)) * hxyz + x * E1 + z' * E3
  have hv' : 2 * v = μ * c := by
    rw [hμ]; linear_combination (-2 * v) * hxyz + 2 * x * E2 - y * E3
  have hw' : -2 * w = μ * a := by
    rw [hμ]; linear_combination (2 * w) * hxyz - y * E1 - 2 * z' * E2
  have key : (u + z) ^ 2 + d * μ ^ 2 = 4 := by
    linear_combination 4 * hU + (u - z + μ * b) * hs' + (2 * w) * hv' - (μ * c) * hw' - μ ^ 2 * hd
  exact ⟨μ, by simpa using hs', by simpa using hv', by simpa using hw', by simpa using key⟩

/-- Helper: a nonzero integer-valued image of ZMod 2: an odd integer is $1$ modulo $2$. -/
theorem cast2_of_odd {x : ℤ} (h : ¬ (2 : ℤ) ∣ x) : (x : ZMod 2) = 1 := by
  have : (x : ZMod 2) = 0 ∨ (x : ZMod 2) = 1 := by
    generalize (x : ZMod 2) = y
    fin_cases y
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases this with h0 | h1
  · exact absurd ((ZMod.intCast_zmod_eq_zero_iff_dvd x 2).1 h0) (by exact_mod_cast h)
  · exact h1

/-- Helper: an even integer is $0$ modulo $2$. -/
theorem cast2_of_even {x : ℤ} (h : (2 : ℤ) ∣ x) : (x : ZMod 2) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).2 (by exact_mod_cast h)

/-- Helper: an integral matrix congruent to the identity modulo $2$ preserves every linear form `evf ρ`. -/
theorem evf_mulVec_of_parity {Z : Matrix (Fin 2) (Fin 2) ℤ} (h01 : (2 : ℤ) ∣ Z 0 1) (h10 : (2 : ℤ) ∣ Z 1 0)
    (h00 : ¬ (2 : ℤ) ∣ Z 0 0) (h11 : ¬ (2 : ℤ) ∣ Z 1 1) (ρ : Option (ZMod 2)) (z : Fin 2 → ℤ) :
    evf ρ (Z *ᵥ z) = evf ρ z := by
  have c00 := cast2_of_odd h00
  have c11 := cast2_of_odd h11
  have c01 := cast2_of_even h01
  have c10 := cast2_of_even h10
  cases ρ with
  | none => simp [evf, Matrix.mulVec, dotProduct, Fin.sum_univ_two, c00, c01]
  | some t => simp [evf, Matrix.mulVec, dotProduct, Fin.sum_univ_two, c00, c01, c10, c11]

/-- Helper: if an integral matrix $Z \equiv I \pmod 2$ carries the sublattice of the line $\kappa'$ to the sublattice
of the line $\kappa$ (as $Z C_{\kappa'} = C_\kappa U$, $\det U = 1$) then $\kappa = \kappa'$. -/
theorem line_eq_of_move {Z U : Matrix (Fin 2) (Fin 2) ℤ} (hU : U.det = 1)
    (hZ : ∀ (ρ : Option (ZMod 2)) (z : Fin 2 → ℤ), evf ρ (Z *ᵥ z) = evf ρ z)
    {κ κ' : Option (ZMod 2)} (h : Z * Cρ 2 κ' = Cρ 2 κ * U) : κ = κ' := by
  obtain ⟨hUa, -⟩ := adj_mul_self U hU
  apply ρ_inj
  intro z
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := (mem_range_Cρ_iff κ z).2 hz
    have hz' : z = Z *ᵥ (Cρ 2 κ' *ᵥ (U.adjugate *ᵥ w)) := by
      rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec w U U.adjugate, hUa, Matrix.one_mulVec]
      exact hw
    rw [hz', hZ]
    exact (mem_range_Cρ_iff κ' _).1 ⟨_, rfl⟩
  · intro hz
    obtain ⟨w, hw⟩ := (mem_range_Cρ_iff κ' z).2 hz
    have : evf κ (Z *ᵥ z) = 0 := by
      rw [hw, Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec]
      exact (mem_range_Cρ_iff κ _).1 ⟨_, rfl⟩
    rw [hZ] at this
    exact this

/-- Helper: if every integral solution $(t, u)$ of $t^{2} + d u^{2} = 4$ has $t$ even and $d \equiv 3 \pmod 8$,
every proper integral automorph of an improperly primitive form of determinant $d$ is congruent to the identity
modulo $2$. -/
theorem aut_even_of_B {d : ℤ} (hd8 : d % 8 = 3) (hB : ∀ t u : ℤ, t ^ 2 + d * u ^ 2 = 4 → (2 : ℤ) ∣ t)
    (H : ImpMat d) (Z : Matrix (Fin 2) (Fin 2) ℤ) (hZ : Z.det = 1) (hZH : Zᵀ * H.1.1 * Z = H.1.1) :
    (2 : ℤ) ∣ Z 0 1 ∧ (2 : ℤ) ∣ Z 1 0 ∧ ¬ (2 : ℤ) ∣ Z 0 0 ∧ ¬ (2 : ℤ) ∣ Z 1 1 := by
  obtain ⟨μ, h1, h2, h3, h4⟩ := aut_param H.1 Z hZ hZH
  obtain ⟨α, hα⟩ := H.2.1
  obtain ⟨γ, hγ⟩ := H.2.2
  obtain ⟨s, hs⟩ := hB _ μ h4
  have hμ : (2 : ℤ) ∣ μ := by
    have hdv : (2 : ℤ) ∣ d * μ ^ 2 := ⟨2 - 2 * s ^ 2, by
        have : d * μ ^ 2 = 4 - (Z 0 0 + Z 1 1) ^ 2 := by linarith
        rw [this, hs]; ring⟩
    rcases Int.prime_two.dvd_or_dvd hdv with h | h
    · omega
    · exact Int.prime_two.dvd_of_dvd_pow h
  obtain ⟨m, hm⟩ := hμ
  have hv : Z 0 1 = 2 * (m * γ) := by
    have := h2
    rw [hγ, hm] at this
    linarith
  have hw : Z 1 0 = -(2 * (m * α)) := by
    have := h3
    rw [hα, hm] at this
    linarith
  have hprod : Z 0 0 * Z 1 1 = 1 + 4 * (-(m * γ) * (m * α)) := by
    rw [Matrix.det_fin_two, hv, hw] at hZ
    linear_combination hZ
  refine ⟨⟨m * γ, hv⟩, ⟨-(m * α), by rw [hw]; ring⟩, ?_, ?_⟩
  · intro h
    have : (2 : ℤ) ∣ Z 0 0 * Z 1 1 := dvd_mul_of_dvd_left h _
    omega
  · intro h
    have : (2 : ℤ) ∣ Z 0 0 * Z 1 1 := dvd_mul_of_dvd_right h _
    omega

/-- Helper (case of Example 13 (i) with $t$ even): the three classes $\theta(H, \kappa)$ are pairwise different. -/
theorem theta_class_inj {d : ℤ} (hd8 : d % 8 = 3) (hB : ∀ t u : ℤ, t ^ 2 + d * u ^ 2 = 4 → (2 : ℤ) ∣ t)
    (H : ImpMat d) (κ κ' : Option (ZMod 2)) (hκ : Valid H κ) (hκ' : Valid H κ')
    (h : thetaClass H κ hκ = thetaClass H κ' hκ') : κ = κ' := by
  obtain ⟨U, hU, hUe⟩ := Quotient.exact h
  obtain ⟨Z, hZ, hZH, hZC⟩ := autom_of_equiv H κ κ' hκ hκ' U hU hUe
  obtain ⟨h01, h10, h00, h11⟩ := aut_even_of_B hd8 hB H Z hZ hZH
  exact line_eq_of_move hU (fun ρ z => evf_mulVec_of_parity h01 h10 h00 h11 ρ z) hZC

/-! ### The case of a solution of $t^{2} + d u^{2} = 4$ with $t$ odd -/

/-- Helper: for $d \equiv 3 \pmod 8$ and a solution $(t, \mu)$ of $t^{2} + d\mu^{2} = 4$ with $t$ odd, an improperly
primitive form $H$ of determinant $d$ has the integral proper automorph
$\begin{pmatrix} s & \gamma\mu \\ -\alpha\mu & r \end{pmatrix}$ ($H = (2\alpha, b; b, 2\gamma)$, $s + r = t$, $s - r = b\mu$),
whose off-diagonal entries are odd and whose trace $t$ is odd. -/
theorem autom_odd {d : ℤ} (hd8 : d % 8 = 3) (H : ImpMat d) (t μ : ℤ) (htm : t ^ 2 + d * μ ^ 2 = 4)
    (ht : ¬ (2 : ℤ) ∣ t) :
    ∃ Y : Matrix (Fin 2) (Fin 2) ℤ, Y.det = 1 ∧ Yᵀ * H.1.1 * Y = H.1.1 ∧
      ¬ (2 : ℤ) ∣ Y 0 1 ∧ ¬ (2 : ℤ) ∣ Y 1 0 ∧ ¬ (2 : ℤ) ∣ (Y 0 0 + Y 1 1) := by
  obtain ⟨α, β, γ, hα, hγ, hβ⟩ := imp_decomp H
  obtain ⟨e, he⟩ := imp_det_eq H hα hγ hβ
  have hαγ : Odd (α * γ) := by
    rw [Int.odd_iff]
    generalize α * γ = n at he
    omega
  obtain ⟨hαo, hγo⟩ := Int.odd_mul.mp hαγ
  have hdet : 4 * α * γ - (2 * β + 1) ^ 2 = d := by
    have h10 : H.1.1 1 0 = H.1.1 0 1 := by have := congrFun (congrFun H.1.2.1 0) 1; simpa using this
    have hd := H.1.2.2.1
    rw [Matrix.det_fin_two, h10, hα, hγ, hβ] at hd
    linarith
  -- μ is odd
  have hμodd : ¬ (2 : ℤ) ∣ μ := by
    intro hμ
    obtain ⟨k, hk⟩ := hμ
    obtain ⟨l, hl⟩ : ∃ l, t = 2 * l + 1 := ⟨(t - 1) / 2, by omega⟩
    rw [hk, hl] at htm
    have h5 : 4 * (l ^ 2 + l + d * k ^ 2) + 1 = 4 := by linear_combination htm
    generalize l ^ 2 + l + d * k ^ 2 = n at h5
    omega
  obtain ⟨k, hk⟩ : ∃ k, μ = 2 * k + 1 := ⟨(μ - 1) / 2, by omega⟩
  have hμo : Odd μ := by rw [Int.odd_iff]; omega
  obtain ⟨l, hl⟩ : ∃ l, t = 2 * l + 1 := ⟨(t - 1) / 2, by omega⟩
  set r : ℤ := l - (2 * β * k + β + k) with hr
  set b : ℤ := 2 * β + 1 with hb
  have ht' : t = 2 * r + b * μ := by rw [hr, hb, hk, hl]; ring
  have hdet1 : (r + b * μ) * r + α * γ * μ ^ 2 = 1 := by
    have h4 : 4 * ((r + b * μ) * r + α * γ * μ ^ 2) = 4 * 1 := by
      rw [← hdet, ht'] at htm
      linear_combination htm
    exact mul_left_cancel₀ (by norm_num) h4
  refine ⟨!![r + b * μ, γ * μ; -(α * μ), r], ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination hdet1
  · rw [sym_eta H.1.2.1, hα, hγ, hβ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (2 * α) * hdet1
    · linear_combination b * hdet1
    · linear_combination b * hdet1
    · linear_combination (2 * γ) * hdet1
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.head_cons]
    intro h
    exact (Int.not_even_iff_odd.2 (hγo.mul hμo)) (even_iff_two_dvd.2 h)
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    intro h
    exact (Int.not_even_iff_odd.2 (hαo.mul hμo).neg) (even_iff_two_dvd.2 h)
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    have : r + b * μ + r = t := by linarith [ht']
    rw [this]; exact ht

/-! ### Moving lines by an automorph -/

/-- Helper: a line is determined by the inclusion of kernels (`z` runs over integer vectors of length $2$). -/
theorem ρ_inj' {ρ ρ' : Option (ZMod 2)} (h : ∀ z, evf ρ z = 0 → evf ρ' z = 0) : ρ = ρ' := by
  cases ρ with
  | none =>
    cases ρ' with
    | none => rfl
    | some t' =>
      have := h ![0, 1] (by simp [evf])
      simp [evf] at this
  | some t =>
    cases ρ' with
    | none =>
      have := h ![1, (t.val : ℤ)] (by simp [evf])
      simp [evf] at this
    | some t' =>
      have := h ![1, (t.val : ℤ)] (by simp [evf])
      simp [evf] at this
      rw [sub_eq_zero.mp this]

/-- Helper: if $Y$ (determinant $1$) maps the kernel of the functional of the line $\kappa$ into the kernel of that
of $\tau$, then $Y C_\kappa = C_\tau W$ with $\det W = 1$. -/
theorem move_of_ker {Y : Matrix (Fin 2) (Fin 2) ℤ} (hY : Y.det = 1) {κ τ : Option (ZMod 2)}
    (h : ∀ z, evf κ z = 0 → evf τ (Y *ᵥ z) = 0) :
    ∃ W : Matrix (Fin 2) (Fin 2) ℤ, W.det = 1 ∧ Y * Cρ 2 κ = Cρ 2 τ * W := by
  obtain ⟨τ0, W, hW, hYW⟩ := exists_ρ_mul (p := 2) (Y * Cρ 2 κ) (by rw [det_mul, hY, det_C2]; simp)
  obtain ⟨hWa, hWa'⟩ := adj_mul_self W hW
  have hτ : τ0 = τ := by
    apply ρ_inj'
    intro z hz
    obtain ⟨w, hw⟩ := (mem_range_Cρ_iff τ0 z).2 hz
    have hz' : z = Y *ᵥ (Cρ 2 κ *ᵥ (W.adjugate *ᵥ w)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hYW, Matrix.mul_assoc, hWa,
        Matrix.mul_one]
      exact hw
    rw [hz']
    exact h _ ((mem_range_Cρ_iff κ _).1 ⟨_, rfl⟩)
  subst hτ
  exact ⟨W, hW, hYW⟩

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
/-- Helper (arithmetic modulo $2$): an integral matrix whose off-diagonal entries and trace are odd, or its
adjugate, carries the kernel of any line $\kappa$ into the kernel of any other line $\kappa'$. -/
theorem parity_move {Y : Matrix (Fin 2) (Fin 2) ℤ} (h01 : ¬ (2 : ℤ) ∣ Y 0 1) (h10 : ¬ (2 : ℤ) ∣ Y 1 0)
    (htr : ¬ (2 : ℤ) ∣ (Y 0 0 + Y 1 1)) {κ κ' : Option (ZMod 2)} (hne : κ ≠ κ') :
    (∀ z, evf κ z = 0 → evf κ' (Y *ᵥ z) = 0) ∨ (∀ z, evf κ z = 0 → evf κ' (Y.adjugate *ᵥ z) = 0) := by
  have c01 := cast2_of_odd h01
  have c10 := cast2_of_odd h10
  have ctr : (Y 0 0 : ZMod 2) + (Y 1 1 : ZMod 2) = 1 := by
    have := cast2_of_odd htr
    push_cast at this
    exact this
  have key : ∀ (κ κ' : Option (ZMod 2)), κ ≠ κ' → ∀ y0 y3 : ZMod 2, y0 + y3 = 1 →
      (∀ x y : ZMod 2, ev2 κ x y = 0 → ev2 κ' (y0 * x + 1 * y) (1 * x + y3 * y) = 0) ∨
      (∀ x y : ZMod 2, ev2 κ x y = 0 → ev2 κ' (y3 * x + (-1) * y) ((-1) * x + y0 * y) = 0) := by
    decide
  have hk := key κ κ' hne (Y 0 0 : ZMod 2) (Y 1 1 : ZMod 2) ctr
  have e1 : ∀ z : Fin 2 → ℤ, evf κ' (Y *ᵥ z) =
      ev2 κ' ((Y 0 0 : ZMod 2) * (z 0 : ZMod 2) + 1 * (z 1 : ZMod 2))
        (1 * (z 0 : ZMod 2) + (Y 1 1 : ZMod 2) * (z 1 : ZMod 2)) := fun z => by
    rw [evf_eq_ev2]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, c01, c10]
  have e2 : ∀ z : Fin 2 → ℤ, evf κ' (Y.adjugate *ᵥ z) =
      ev2 κ' ((Y 1 1 : ZMod 2) * (z 0 : ZMod 2) + (-1) * (z 1 : ZMod 2))
        ((-1) * (z 0 : ZMod 2) + (Y 0 0 : ZMod 2) * (z 1 : ZMod 2)) := fun z => by
    rw [evf_eq_ev2]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.adjugate_fin_two, c01, c10]
  rcases hk with hk | hk
  · left
    intro z hz
    rw [e1]
    exact hk _ _ (by rw [evf_eq_ev2] at hz; exact hz)
  · right
    intro z hz
    rw [e2]
    exact hk _ _ (by rw [evf_eq_ev2] at hz; exact hz)

/-- Helper: an integral proper automorph $A$ of $H$ with $A C_\kappa = C_{\kappa'} W$ ($\det W = 1$) shows that the
sublattice forms $\theta(H, \kappa)$ and $\theta(H, \kappa')$ are properly equivalent. -/
theorem thetaClass_of_move {d : ℤ} (H : ImpMat d) (κ κ' : Option (ZMod 2)) (hκ : Valid H κ) (hκ' : Valid H κ')
    (A W : Matrix (Fin 2) (Fin 2) ℤ) (hW : W.det = 1) (hAH : Aᵀ * H.1.1 * A = H.1.1)
    (hAC : A * Cρ 2 κ = Cρ 2 κ' * W) : thetaClass H κ hκ = thetaClass H κ' hκ' := by
  have e : (2 : ℤ) • Ch9Ex12.theta H.1.1 κ = (2 : ℤ) • (Wᵀ * Ch9Ex12.theta H.1.1 κ' * W) := by
    rw [two_smul_theta H κ]
    have : (2 : ℤ) • (Wᵀ * Ch9Ex12.theta H.1.1 κ' * W) = Wᵀ * ((2 : ℤ) • Ch9Ex12.theta H.1.1 κ') * W := by
      simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [this, two_smul_theta H κ']
    calc (Cρ 2 κ)ᵀ * H.1.1 * Cρ 2 κ = (Cρ 2 κ)ᵀ * (Aᵀ * H.1.1 * A) * Cρ 2 κ := by rw [hAH]
      _ = (A * Cρ 2 κ)ᵀ * H.1.1 * (A * Cρ 2 κ) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hAC]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have hθ := smul_cancel (by norm_num) e
  symm
  apply Quotient.sound
  exact ⟨W, hW, hθ.symm⟩

/-- Helper (case of Example 13 (i) with an odd trace): if $t^{2} + d u^{2} = 4$ has a solution with $t$ odd, the
classes $\theta(H, \kappa)$ do not depend on the line $\kappa$. -/
theorem thetaClass_const_odd {d : ℤ} (hd8 : d % 8 = 3) (hodd : ∃ t u : ℤ, t ^ 2 + d * u ^ 2 = 4 ∧ ¬ (2 : ℤ) ∣ t)
    (H : ImpMat d) (κ κ' : Option (ZMod 2)) (hκ : Valid H κ) (hκ' : Valid H κ') :
    thetaClass H κ hκ = thetaClass H κ' hκ' := by
  by_cases hk : κ = κ'
  · subst hk; rfl
  obtain ⟨t, u, htu, ht⟩ := hodd
  obtain ⟨Y, hY, hYH, h01, h10, htr⟩ := autom_odd hd8 H t u htu ht
  rcases parity_move h01 h10 htr hk with h | h
  · obtain ⟨W, hW, hYW⟩ := move_of_ker hY h
    exact thetaClass_of_move H κ κ' hκ hκ' Y W hW hYH hYW
  · have hYa : Y.adjugate.det = 1 := by rw [det_adj]; exact hY
    obtain ⟨W, hW, hYW⟩ := move_of_ker hYa h
    refine thetaClass_of_move H κ κ' hκ hκ' Y.adjugate W hW ?_ hYW
    have := conj_adj' hY H.1.1
    rwa [hYH] at this

/-! ### The class number identity -/

/-- Helper: class numbers from fibre sizes. -/
theorem hPro_eq_mul {d : ℤ} (hd : d % 4 = 3) (c : ℕ)
    (hfib : ∀ H : ImpMat d, Cardinal.mk {x : Quotient (proSetoid d) // psiBar hd x = Quotient.mk _ H} = c) :
    hPro d = hImp d * c := by
  have h := mk_eq_mul_of_fibres (psiBar hd) (c : Cardinal.{0}) (fun b => by
    induction b using Quotient.inductionOn with
    | _ H => exact hfib H)
  unfold hPro hImp Nat.card
  rw [h, Cardinal.toNat_mul]
  simp

/-- Helper: for $d > 3$ every solution of $t^{2} + d u^{2} = 4$ has $t$ even. -/
theorem even_of_big {d : ℤ} (hd : 3 < d) : ∀ t u : ℤ, t ^ 2 + d * u ^ 2 = 4 → (2 : ℤ) ∣ t := by
  intro t u h
  by_cases hu : u = 0
  · subst hu
    have : t ^ 2 = 2 ^ 2 := by linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with h | h <;> rw [h] <;> simp
  · have h1 : 1 ≤ u ^ 2 := by
      have := sq_pos_of_ne_zero hu
      omega
    have h2 : t ^ 2 ≤ 0 := by nlinarith
    have h3 : t = 0 := by simpa using le_antisymm h2 (sq_nonneg t)
    rw [h3]; exact dvd_zero _

/-- **Cassels, Ch. 9, Example 13 (i)** (p. 165): *properly versus improperly primitive classes.* Let
$d \equiv 3 \pmod 4$, and let $h(d)$ (`hPro d`) and $h'(d)$ (`hImp d`) be the numbers of proper classes
($\mathrm{SL}_2(\mathbb Z)$-classes) of properly primitive and of improperly primitive classically integral binary forms
of determinant $d$ (Gram matrices $\begin{pmatrix} a & b \\ b & c \end{pmatrix}$, $ac - b^{2} = d$; improperly
primitive means primitive with $a$ and $c$ both even, properly primitive means primitive with $a$ or $c$ odd).
Let the exceptional case be: $d \equiv 3 \pmod 8$ and either (a) $d > 3$, or (b) $d < 0$ and every integral solution
$(t, u)$ of $t^{2} + d u^{2} = 4$ has $t$ even. Then $h(d) = 3 h'(d)$ in the exceptional case, and
$h(d) = h'(d)$ otherwise. (Class numbers are `Nat.card`.)
Method: the map $\psi$ sending a properly primitive form to the improperly primitive form on its unique sublattice of
index $2$ on which it is even has fibres of size $1$ (one valid line, or the three sublattices of an improperly
primitive form are permuted by an automorph of odd trace) or $3$ (no such automorph, `theta_class_inj`). -/
@[kb "cassels1978" "Ch. 9, Ex. 13 (i), p. 165"]
theorem ex13_i {d : ℤ} (hd : d % 4 = 3) :
    ((d % 8 = 3 ∧ (3 < d ∨ (d < 0 ∧ ∀ t u : ℤ, t ^ 2 + d * u ^ 2 = 4 → (2 : ℤ) ∣ t))) → hPro d = 3 * hImp d) ∧
    (¬ (d % 8 = 3 ∧ (3 < d ∨ (d < 0 ∧ ∀ t u : ℤ, t ^ 2 + d * u ^ 2 = 4 → (2 : ℤ) ∣ t))) → hPro d = hImp d) := by
  constructor
  · rintro ⟨hd8, h⟩
    have hB : ∀ t u : ℤ, t ^ 2 + d * u ^ 2 = 4 → (2 : ℤ) ∣ t := by
      rcases h with h | ⟨-, h⟩
      · exact even_of_big h
      · exact h
    rw [hPro_eq_mul hd 3 (fun H => by
      have := fibre_three hd hd8 H (fun κ κ' hκ hκ' h' => theta_class_inj hd8 hB H κ κ' hκ hκ' h')
      exact_mod_cast this)]
    ring
  · intro hn
    rw [hPro_eq_mul hd 1 (fun H => by
      have hconst : ∀ (κ κ' : Option (ZMod 2)) (hκ : Valid H κ) (hκ' : Valid H κ'),
          thetaClass H κ hκ = thetaClass H κ' hκ' := by
        have h8 : d % 8 = 3 ∨ d % 8 = 7 := by omega
        rcases h8 with h8 | h8
        · have hodd : ∃ t u : ℤ, t ^ 2 + d * u ^ 2 = 4 ∧ ¬ (2 : ℤ) ∣ t := by
            by_contra hcon
            push_neg at hcon
            apply hn
            refine ⟨h8, ?_⟩
            by_cases hd3 : 3 < d
            · exact Or.inl hd3
            · right
              refine ⟨?_, fun t u htu => hcon t u htu⟩
              by_contra hneg
              have : d = 3 := by omega
              exact absurd (hcon 1 1 (by rw [this]; norm_num)) (by decide)
          exact fun κ κ' hκ hκ' => thetaClass_const_odd h8 hodd H κ κ' hκ hκ'
        · intro κ κ' hκ hκ'
          have := (valid_seven h8 H).unique hκ hκ'
          subst this
          rfl
      have := fibre_one hd H hconst
      exact_mod_cast this)]
    ring

/-! ### Example 12 (iv): the orbit formula for every determinant -/

variable {p : ℕ} [hp : Fact p.Prime]

/-- Helper: two non-vanishing lines `ρ`, `ρ'` of the class `c` (for the representative form $H$ of `c`) are
related when a proper integral automorph $U$ of $H$ carries the sublattice of `ρ'` onto that of `ρ`, i.e.
$U C_{\rho'} = C_{\rho} V$ with $\det V = 1$. -/
def OrbRel (p : ℕ) [Fact p.Prime] {d : ℤ} (c : Quotient (slSetoid d)) (ρ ρ' : Fib p d c) : Prop :=
  ∃ U V : Matrix (Fin 2) (Fin 2) ℤ, U.det = 1 ∧ V.det = 1 ∧
    Uᵀ * (Quotient.out c).1 * U = (Quotient.out c).1 ∧ U * Cρ p ρ'.1 = Cρ p ρ.1 * V

/-- Helper: `OrbRel` is reflexive. -/
theorem orbRel_refl {p : ℕ} [Fact p.Prime] {d : ℤ} (c : Quotient (slSetoid d)) (ρ : Fib p d c) :
    OrbRel p c ρ ρ := ⟨1, 1, by simp, by simp, by simp, by simp⟩

/-- Helper: `OrbRel` is symmetric. -/
theorem orbRel_symm {p : ℕ} [Fact p.Prime] {d : ℤ} {c : Quotient (slSetoid d)} {ρ ρ' : Fib p d c}
    (h : OrbRel p c ρ ρ') : OrbRel p c ρ' ρ := by
  obtain ⟨U, V, hU, hV, hUH, hUC⟩ := h
  obtain ⟨hVa, hVa'⟩ := adj_mul_self V hV
  obtain ⟨hUa, hUa'⟩ := adj_mul_self U hU
  refine ⟨U.adjugate, V.adjugate, by rw [det_adj]; exact hU, by rw [det_adj]; exact hV, ?_, ?_⟩
  · have := conj_adj' hU (Quotient.out c).1
    rwa [hUH] at this
  · calc U.adjugate * Cρ p ρ.1 = U.adjugate * (Cρ p ρ.1 * (V * V.adjugate)) := by rw [hVa, Matrix.mul_one]
      _ = U.adjugate * (Cρ p ρ.1 * V) * V.adjugate := by simp only [Matrix.mul_assoc]
      _ = U.adjugate * (U * Cρ p ρ'.1) * V.adjugate := by rw [hUC]
      _ = Cρ p ρ'.1 * V.adjugate := by rw [← Matrix.mul_assoc U.adjugate, hUa', Matrix.one_mul]

/-- Helper: `OrbRel` is transitive. -/
theorem orbRel_trans {p : ℕ} [Fact p.Prime] {d : ℤ} {c : Quotient (slSetoid d)} {ρ ρ' ρ'' : Fib p d c}
    (h : OrbRel p c ρ ρ') (h' : OrbRel p c ρ' ρ'') : OrbRel p c ρ ρ'' := by
  obtain ⟨U₁, V₁, hU₁, hV₁, hH₁, hC₁⟩ := h
  obtain ⟨U₂, V₂, hU₂, hV₂, hH₂, hC₂⟩ := h'
  refine ⟨U₁ * U₂, V₁ * V₂, by rw [Matrix.det_mul, hU₁, hU₂, one_mul],
    by rw [Matrix.det_mul, hV₁, hV₂, one_mul], ?_, ?_⟩
  · calc (U₁ * U₂)ᵀ * (Quotient.out c).1 * (U₁ * U₂) = U₂ᵀ * (U₁ᵀ * (Quotient.out c).1 * U₁) * U₂ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (Quotient.out c).1 := by rw [hH₁, hH₂]
  · rw [Matrix.mul_assoc, hC₂, ← Matrix.mul_assoc, hC₁, Matrix.mul_assoc]

/-- The setoid on the non-vanishing lines of the class `c` whose classes are the orbits of the group of proper
integral automorphs of the form of `c` (acting by $\rho \mapsto U\rho$, where $U C_\rho = C_{U\rho} V$). -/
def orbSetoid (p : ℕ) [Fact p.Prime] (d : ℤ) (c : Quotient (slSetoid d)) : Setoid (Fib p d c) where
  r := OrbRel p c
  iseqv := ⟨orbRel_refl c, orbRel_symm, orbRel_trans⟩

/-- Helper: the map from pairs (class `c` of determinant `d`, orbit of a non-vanishing line of `c`) to the proper
classes of determinant $d p^{2}$, sending $(c, [\rho])$ to the class of $C_\rho^{\mathsf T} H C_\rho$. -/
noncomputable def orbMap (p : ℕ) [Fact p.Prime] (d : ℤ) :
    (Σ c : Quotient (slSetoid d), Quotient (orbSetoid p d c)) → Quotient (slSetoid (d * (p : ℤ) ^ 2)) :=
  fun x => Quotient.lift (s := orbSetoid p d x.1) (fun ρ => Emap p d ⟨x.1, ρ⟩) (fun ρ ρ' h => by
    have h' : OrbRel p x.1 ρ ρ' := h
    obtain ⟨U, V, hU, hV, hUH, hUC⟩ := h'
    apply Quotient.sound
    refine ⟨V, hV, ?_⟩
    show Vᵀ * ((Cρ p ρ.1)ᵀ * (Quotient.out x.1).1 * Cρ p ρ.1) * V =
      (Cρ p ρ'.1)ᵀ * (Quotient.out x.1).1 * Cρ p ρ'.1
    calc Vᵀ * ((Cρ p ρ.1)ᵀ * (Quotient.out x.1).1 * Cρ p ρ.1) * V
        = (Cρ p ρ.1 * V)ᵀ * (Quotient.out x.1).1 * (Cρ p ρ.1 * V) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (U * Cρ p ρ'.1)ᵀ * (Quotient.out x.1).1 * (U * Cρ p ρ'.1) := by rw [hUC]
      _ = (Cρ p ρ'.1)ᵀ * (Uᵀ * (Quotient.out x.1).1 * U) * Cρ p ρ'.1 := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hUH]) x.2

/-- Helper: `orbMap` is a bijection (for $d \ne 0$ and every prime `p`). -/
theorem orbMap_bijective {d : ℤ} (hd0 : d ≠ 0) : Function.Bijective (orbMap p d) := by
  constructor
  · rintro ⟨c₁, q₁⟩ ⟨c₂, q₂⟩ h
    induction q₁ using Quotient.inductionOn with
    | _ ρ₁ =>
    induction q₂ using Quotient.inductionOn with
    | _ ρ₂ =>
    have h0 : Emap p d ⟨c₁, ρ₁⟩ = Emap p d ⟨c₂, ρ₂⟩ := h
    have h' : SLRel (Eobj c₁ ρ₁).1 (Eobj c₂ ρ₂).1 := Quotient.exact h0
    obtain ⟨V, hV, hVeq⟩ := h'
    obtain ⟨U, hU, hUH, hUC⟩ := transport hd0 (Quotient.out c₁) (Quotient.out c₂) ρ₁.2 V hV hVeq
    have hc : c₁ = c₂ := by
      have : (Quotient.mk _ (Quotient.out c₁) : Quotient (slSetoid d)) = Quotient.mk _ (Quotient.out c₂) :=
        Quotient.sound ⟨U, hU, hUH⟩
      simpa using this
    subst hc
    exact Sigma.ext rfl (heq_of_eq (Quotient.sound ⟨U, V, hU, hV, hUH, hUC⟩))
  · intro y
    obtain ⟨⟨c, ρ⟩, hx⟩ := Emap_surjective (p := p) (d := d) y
    exact ⟨⟨c, Quotient.mk _ ρ⟩, hx⟩

/-- **Cassels, Ch. 9, Example 12 (iv)** (p. 165): *the generalization of (iii) to every determinant.* Let $p$ be
a prime (also $p = 2$ is allowed) and $d \ne 0$ an integer. Let $h(m)$ (`hcl m`) be the number of proper classes of
primitive classically integral binary forms of determinant $m$ (Gram matrices; this is `hClasses` by `hClasses_eq`).
For a class `c` of determinant $d$ with representative Gram matrix $H$, the lines of $\mathbb P^{1}(\mathbb F_p)$ on
which $H$ does not vanish modulo $p$ (type `Fib p d c`) correspond to the sublattices of index $p$ of $\mathbb Z^{2}$
that carry a primitive form of determinant $d p^{2}$; two such lines are in the same *orbit* (`orbSetoid`) when a
proper integral automorph of $H$ carries one sublattice onto the other. Then
$$h(d p^{2}) = \#\Bigl\{(c, \text{orbit of non-vanishing lines of } c)\Bigr\} = \sum_{c} \#\bigl(\mathrm{Aut}^{+}(c) \backslash \{\text{non-vanishing lines of } c\}\bigr),$$
the cardinality of the type of pairs (`Nat.card` of a sigma type; if the number of classes were infinite both sides
would be $0$, in fact the class numbers are finite). When the proper automorphs of every form of determinant $d$ are
$\pm I$ (e.g. $d \ge 2$, $d \ne 3$, `aut_pm_one`; or $d = -k^{2}$, `ex12_iv_square`) every orbit is a single
line and this is Example 12 (iii) (`hcl_mul`, $h(d p^{2}) = N\, h(d)$); for $d = 1$ and $d = 3$ the finite
automorph groups of order $4$ and $6$ (resp. $2$) and for $d < 0$ not a square the infinite cyclic automorph group
(Pell equation $t^{2} + d u^{2} = 4$, `aut_param`) give fewer orbits (see `ex12_iv_one`, `ex12_iv_three`). -/
@[kb "cassels1978" "Ch. 9, Ex. 12 (iv), p. 165"]
theorem ex12_iv_orbits {d : ℤ} (hd0 : d ≠ 0) :
    hcl (d * (p : ℤ) ^ 2) = Nat.card (Σ c : Quotient (slSetoid d), Quotient (orbSetoid p d c)) :=
  (Nat.card_congr (Equiv.ofBijective _ (orbMap_bijective hd0))).symm

/-! ### Example 12 (iv): $-d$ a square -/

/-- Helper: a proper integral automorph of a primitive form with parameter $\mu = 0$ (`aut_param`) is $\pm I$. -/
theorem aut_of_mu_zero {d : ℤ} (H : PrimMat d) (U : Matrix (Fin 2) (Fin 2) ℤ) (hU : U.det = 1)
    (h1 : U 0 0 - U 1 1 = 0 * H.1 0 1) (h2 : 2 * U 0 1 = 0 * H.1 1 1) (h3 : -2 * U 1 0 = 0 * H.1 0 0) :
    U = 1 ∨ U = -1 := by
  have hv : U 0 1 = 0 := by rw [zero_mul] at h2; linarith
  have hw : U 1 0 = 0 := by rw [zero_mul] at h3; linarith
  have h11 : U 1 1 = U 0 0 := by rw [zero_mul] at h1; linarith
  have hu : U 0 0 * U 0 0 = 1 := by
    rw [Matrix.det_fin_two, hv, hw, h11] at hU
    linarith
  have hU' : U = !![U 0 0, U 0 1; U 1 0, U 1 1] := Matrix.eta_fin_two U
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hu with h | h
  · left
    rw [hU', hv, hw, h11, h]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · right
    rw [hU', hv, hw, h11, h]
    ext i j; fin_cases i <;> fin_cases j <;> simp

/-- Helper: a primitive form all of whose parameters $(t, u)$ of proper automorphs ($t^{2} + d u^{2} = 4$,
`aut_param`) have $u = 0$ has only the proper automorphs $\pm I$. -/
theorem aut_pm_one_of_param {d : ℤ} (hB : ∀ t u : ℤ, t ^ 2 + d * u ^ 2 = 4 → u = 0) (H : PrimMat d)
    (U : Matrix (Fin 2) (Fin 2) ℤ) (hU : U.det = 1) (hUH : Uᵀ * H.1 * U = H.1) : U = 1 ∨ U = -1 := by
  obtain ⟨μ, h1, h2, h3, h4⟩ := aut_param H U hU hUH
  have hμ : μ = 0 := hB _ _ h4
  subst hμ
  exact aut_of_mu_zero H U hU h1 h2 h3

/-- Helper: for $d = -k^{2}$ ($k \ge 1$) the only integral solution $(t, u)$ of $t^{2} + d u^{2} = 4$ has $u = 0$
(because $(t - ku)(t + ku) = 4$ has only the factorization $2 \cdot 2$ into factors of equal parity). -/
theorem solutions_neg_square {k : ℤ} (hk : 0 < k) :
    ∀ t u : ℤ, t ^ 2 + (-(k ^ 2)) * u ^ 2 = 4 → u = 0 := by
  intro t u h
  by_contra hu
  have hs : k * u ≠ 0 := mul_ne_zero hk.ne' hu
  have h' : (t - k * u) * (t + k * u) = 4 := by linear_combination h
  generalize k * u = s at hs h'
  obtain ⟨a, ha⟩ : ∃ a, a = t - s := ⟨_, rfl⟩
  rw [← ha] at h'
  have hdvd : a ∣ 4 := ⟨t + s, h'.symm⟩
  have hb1 : a ≤ 4 := Int.le_of_dvd (by norm_num) hdvd
  have hb2 : -a ≤ 4 := Int.le_of_dvd (by norm_num) ((neg_dvd).2 hdvd)
  have hb3 : -4 ≤ a := by linarith
  generalize hb : t + s = b at h'
  have hb' : b = t + s := hb.symm
  have h0 : a ≠ 0 := by
    rintro rfl
    simp at h'
  interval_cases a <;> omega

/-- **Cassels, Ch. 9, Example 12 (iv), the case $-d$ a square** (p. 165): *if $d = -k^{2}$ with $k \ge 1$ the
conclusion of (iii) holds unchanged.* Let $p$ be an odd prime and $k \ge 1$ an integer. Then every primitive
classically integral binary form of determinant $-k^{2}$ has only $\pm I$ as proper integral automorphs (these
forms are isotropic over $\mathbb Q$, so unlike the case $-d$ a non-square there is no Pell unit, because
$(t - ku)(t + ku) = 4$ forces $u = 0$), and therefore
$$h(-k^{2} p^{2}) = \left(p - \left(\frac{k^{2}}{p}\right)\right) h(-k^{2}),$$
that is $h(-k^2p^2) = (p-1)\,h(-k^2)$ if $p \nmid k$ and $h(-k^2p^2) = p\, h(-k^2)$ if $p \mid k$. Here `hClasses m`
is Cassels' $h(m)$ (proper classes of primitive integral binary forms of determinant $m$). -/
@[kb "cassels1978" "Ch. 9, Ex. 12 (iv), p. 165 (-d a square)"]
theorem ex12_iv_square (hp2 : p ≠ 2) {k : ℤ} (hk : 0 < k) :
    (hClasses (-(k ^ 2) * (p : ℤ) ^ 2) : ℤ) = ((p : ℤ) - legendreSym p (k ^ 2)) * (hClasses (-(k ^ 2)) : ℤ) := by
  rw [hClasses_eq, hClasses_eq]
  have hd0 : -(k ^ 2) ≠ 0 := by have := pow_pos hk 2; omega
  have := hcl_mul (p := p) hp2 hd0 fun H U hU h => aut_pm_one_of_param (solutions_neg_square hk) H U hU h
  rw [neg_neg] at this
  exact this

/-! ### Example 12 (iv): orbits of equal size -/

/-- Helper: if every equivalence class of a finite type has the same size `k` then the type has
`k` times as many elements as classes. -/
theorem card_eq_mul_quot {α : Type} [Finite α] (s : Setoid α) (k : ℕ)
    (h : ∀ x : α, Nat.card {y : α // s.r y x} = k) : Nat.card α = Nat.card (Quotient s) * k := by
  have hf := mk_eq_mul_of_fibres (Quotient.mk s) (k : Cardinal.{0}) (fun b => by
    induction b using Quotient.inductionOn with
    | _ x =>
      have e : {a : α // Quotient.mk s a = Quotient.mk s x} ≃ {y : α // s.r y x} :=
        Equiv.subtypeEquivRight fun a => Quotient.eq
      rw [Cardinal.mk_congr e, ← Nat.cast_card, h x])
  unfold Nat.card
  rw [hf, Cardinal.toNat_mul]
  simp

/-- Helper: the non-vanishing property is transported by a proper integral automorph. -/
theorem nv_of_move {d : ℤ} (H : PrimMat d) {ρ ρ₁ : Option (ZMod p)} (hρ : NV H.1 ρ)
    (A W : Matrix (Fin 2) (Fin 2) ℤ) (hAH : Aᵀ * H.1 * A = H.1) (hAC : A * Cρ p ρ = Cρ p ρ₁ * W) :
    NV H.1 ρ₁ := by
  by_contra hn
  have hn' := p_dvd_gram_of_not_nonvan ρ₁ (H.1 0 0) (H.1 0 1) (H.1 1 1) hn
  rw [← sym_eta H.2.1] at hn'
  obtain ⟨-, -, hprim⟩ := phi_primMat H hρ
  apply not_isUnit_p (p := p)
  apply hprim
  intro i j
  have e : (Cρ p ρ)ᵀ * H.1 * Cρ p ρ = Wᵀ * ((Cρ p ρ₁)ᵀ * H.1 * Cρ p ρ₁) * W := by
    calc (Cρ p ρ)ᵀ * H.1 * Cρ p ρ = (Cρ p ρ)ᵀ * (Aᵀ * H.1 * A) * Cρ p ρ := by rw [hAH]
      _ = (A * Cρ p ρ)ᵀ * H.1 * (A * Cρ p ρ) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hAC]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [e]
  exact dvd_mul3 _ _ _ _ hn' i j

/-! ### Example 12 (iv): fixed lines of an automorph -/

/-- Helper: the value $x^{\mathsf T} M x$ of the binary quadratic form with Gram matrix `M` at `x`, written out
in coordinates. -/
def Qf {K : Type*} [CommRing K] (M : Matrix (Fin 2) (Fin 2) K) (x : Fin 2 → K) : K :=
  x 0 * (M 0 0 * x 0 + M 0 1 * x 1) + x 1 * (M 1 0 * x 0 + M 1 1 * x 1)

/-- Helper: substituting $x \mapsto J x$ replaces the Gram matrix `M` by $J^{\mathsf T} M J$. -/
theorem Qf_mulVec {K : Type*} [CommRing K] (M J : Matrix (Fin 2) (Fin 2) K) (x : Fin 2 → K) :
    Qf M (J *ᵥ x) = Qf (Jᵀ * M * J) x := by
  simp [Qf, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Helper: the quadratic form is homogeneous of degree $2$. -/
theorem Qf_smul {K : Type*} [CommRing K] (M : Matrix (Fin 2) (Fin 2) K) (l : K) (x : Fin 2 → K) :
    Qf M (l • x) = l ^ 2 * Qf M x := by
  simp [Qf]
  ring

/-- Helper: if $J^{2} = -1$ and $J$ preserves the form `H` over a field of characteristic not $2$, then `H`
vanishes at every eigenvector $u \ne 0$ of $J$. -/
theorem Qf_zero_of_involution {K : Type*} [Field K] (hK2 : (2 : K) ≠ 0) (J H : Matrix (Fin 2) (Fin 2) K)
    (hJJ : J * J = -1) (hJH : Jᵀ * H * J = H) (u : Fin 2 → K) (hu : u ≠ 0) (l : K)
    (hl : J *ᵥ u = l • u) : Qf H u = 0 := by
  have h1 : Qf H (J *ᵥ u) = Qf H u := by rw [Qf_mulVec, hJH]
  rw [hl, Qf_smul] at h1
  have h3 : (l ^ 2 + 1) • u = 0 := by
    have h4 : J *ᵥ (J *ᵥ u) = -u := by rw [Matrix.mulVec_mulVec, hJJ, Matrix.neg_mulVec, Matrix.one_mulVec]
    rw [hl, Matrix.mulVec_smul, hl, smul_smul] at h4
    rw [add_smul, one_smul, sq, h4, neg_add_cancel]
  have hl2 : l ^ 2 + 1 = 0 := by
    rcases smul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h hu
  have hl3 : l ^ 2 = -1 := by linear_combination hl2
  rw [hl3] at h1
  have h5 : (2 : K) * Qf H u = 0 := by linear_combination (-1 : K) * h1
  exact (mul_eq_zero.mp h5).resolve_left hK2

/-- Helper: $2 \ne 0$ in $\mathbb F_p$ for an odd prime $p$. -/
theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)

/-- Helper: an integral matrix `J` with $J^{2} = -I$ preserving the symmetric matrix `H` fixes no line on which
`H` does not vanish modulo the odd prime $p$: if $J C_\rho = C_\rho W$ then `ρ` is a zero of `H`. -/
theorem not_fixed (hp2 : p ≠ 2) {H J W : Matrix (Fin 2) (Fin 2) ℤ} (hHs : Hᵀ = H)
    (hJJ : J * J = -1) (hJH : Jᵀ * H * J = H) {ρ : Option (ZMod p)} (hρ : NV H ρ)
    (hW : J * Cρ p ρ = Cρ p ρ * W) : False := by
  let φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  have hJJ' : J.map φ * J.map φ = -1 := by
    rw [← Matrix.map_mul, hJJ]
    ext i j; fin_cases i <;> fin_cases j <;> simp [φ]
  have hJH' : (J.map φ)ᵀ * H.map φ * J.map φ = H.map φ := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map φ) hJH
    simpa [Matrix.map_mul, Matrix.transpose_map] using this
  have hW' : J.map φ * (Cρ p ρ).map φ = (Cρ p ρ).map φ * W.map φ := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map φ) hW
    simpa [Matrix.map_mul] using this
  have h10 : H 1 0 = H 0 1 := by have := congrFun (congrFun hHs 0) 1; simpa using this
  have h2 := two_ne_zero_zmod hp2
  have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
  cases ρ with
  | none =>
    have hC : (Cρ p (none : Option (ZMod p))).map φ = !![0, 0; 0, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Cρ, φ, hp0]
    rw [hC] at hW'
    have hl : J.map φ *ᵥ ![0, 1] = (W.map φ 1 1) • ![0, 1] := by
      have h := congrArg (fun M => M *ᵥ ![(0 : ZMod p), 1]) hW'
      simp only [← Matrix.mulVec_mulVec] at h
      have e1 : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ ![0, 1] = ![0, 1] := by
        ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rw [e1] at h
      rw [h]
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
    have hz := Qf_zero_of_involution h2 (J.map φ) (H.map φ) hJJ' hJH' ![0, 1]
      (by intro h; have := congrFun h 1; simp at this) _ hl
    apply hρ
    simpa [Qf, Matrix.map_apply, φ] using hz
  | some t =>
    have hC : (Cρ p (some t)).map φ = !![1, 0; t, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Cρ, φ, -ZMod.natCast_val, -ZMod.intCast_cast, ZMod.natCast_zmod_val]
    rw [hC] at hW'
    have hl : J.map φ *ᵥ ![1, t] = (W.map φ 0 0) • ![1, t] := by
      have h := congrArg (fun M => M *ᵥ ![(1 : ZMod p), 0]) hW'
      simp only [← Matrix.mulVec_mulVec] at h
      have e1 : (!![1, 0; t, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ ![1, 0] = ![1, t] := by
        ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rw [e1] at h
      rw [h]
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply] <;> ring
    have hz := Qf_zero_of_involution h2 (J.map φ) (H.map φ) hJJ' hJH' ![1, t]
      (by intro h; have := congrFun h 0; simp at this) _ hl
    apply hρ
    simp [Qf, Matrix.map_apply, φ, h10] at hz
    linear_combination hz

/-! ### Example 12 (iv): $d = 1$ -/

/-- Helper: the integral matrix $J_H = \begin{pmatrix} b & c \\ -a & -b\end{pmatrix}$ attached to the Gram matrix
$H = \begin{pmatrix} a & b \\ b & c\end{pmatrix}$; for $ac - b^{2} = 1$ it is a proper automorph of $H$ with
$J_H^{2} = -I$ (`autJ_facts`). -/
def autJ (H : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![H 0 1, H 1 1; -H 0 0, -H 0 1]

/-- Helper: for a primitive form of determinant $1$ the matrix `autJ H` has determinant $1$, preserves `H` and
squares to $-I$. -/
theorem autJ_facts (H : PrimMat 1) :
    (autJ H.1).det = 1 ∧ (autJ H.1)ᵀ * H.1 * autJ H.1 = H.1 ∧ autJ H.1 * autJ H.1 = -1 := by
  obtain ⟨hs, hd, -⟩ := H.2
  have h10 : H.1 1 0 = H.1 0 1 := by have := congrFun (congrFun hs 0) 1; simpa using this
  have hD : H.1 0 0 * H.1 1 1 - H.1 0 1 * H.1 0 1 = 1 := by
    rw [Matrix.det_fin_two, h10] at hd; exact hd
  refine ⟨?_, ?_, ?_⟩
  · simp only [autJ, Matrix.det_fin_two_of]
    linear_combination hD
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [autJ, Matrix.mul_apply, Fin.sum_univ_two, h10] <;>
      first
        | linear_combination (H.1 0 0) * hD
        | linear_combination (H.1 0 1) * hD
        | linear_combination (H.1 1 1) * hD
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [autJ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
      first
        | linear_combination (-1 : ℤ) * hD
        | linear_combination (0 : ℤ) * hD

/-- Helper: the proper integral automorphs of a primitive form of determinant $1$ are exactly $\pm I$ and
$\pm J_H$ (the solutions of $t^{2} + \mu^{2} = 4$ are $(\pm 2, 0)$ and $(0, \pm 2)$). -/
theorem aut_one_cases (H : PrimMat 1) (U : Matrix (Fin 2) (Fin 2) ℤ) (hU : U.det = 1)
    (hUH : Uᵀ * H.1 * U = H.1) : U = 1 ∨ U = -1 ∨ U = autJ H.1 ∨ U = -autJ H.1 := by
  obtain ⟨μ, h1, h2, h3, h4⟩ := aut_param H U hU hUH
  have hμ : -2 ≤ μ ∧ μ ≤ 2 := by constructor <;> nlinarith [sq_nonneg (U 0 0 + U 1 1)]
  obtain ⟨hμ1, hμ2⟩ := hμ
  have ht : ∀ t : ℤ, t ^ 2 = 3 → False := by
    intro t ht
    have : -2 ≤ t ∧ t ≤ 2 := by constructor <;> nlinarith
    obtain ⟨a, b⟩ := this
    interval_cases t <;> omega
  interval_cases μ
  · have h5 : (U 0 0 + U 1 1) ^ 2 = 0 := by linarith
    have h6 : U 0 0 + U 1 1 = 0 := by simpa using h5
    right; right; right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [autJ] <;> omega
  · exact (ht (U 0 0 + U 1 1) (by linarith)).elim
  · rcases aut_of_mu_zero H U hU h1 h2 h3 with h | h
    · left; exact h
    · right; left; exact h
  · exact (ht (U 0 0 + U 1 1) (by linarith)).elim
  · have h5 : (U 0 0 + U 1 1) ^ 2 = 0 := by linarith
    have h6 : U 0 0 + U 1 1 = 0 := by simpa using h5
    right; right; left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [autJ] <;> omega

/-- Helper: two lines whose sublattices are related by determinant one matrices coincide. -/
theorem line_unique {ρ ρ' : Option (ZMod p)} {V W : Matrix (Fin 2) (Fin 2) ℤ} (hV : V.det = 1) (hW : W.det = 1)
    (h : Cρ p ρ' * V = Cρ p ρ * W) : ρ' = ρ := by
  obtain ⟨hWa, hWa'⟩ := adj_mul_self W hW
  refine rho_eq_of_mul (U := 1) (V := V * W.adjugate) ?_ (Or.inl rfl) ?_
  · rw [Matrix.det_mul, hV, det_adj, hW, one_mul]
  · rw [Matrix.one_mul]
    calc Cρ p ρ = Cρ p ρ * (W * W.adjugate) := by rw [hWa, Matrix.mul_one]
      _ = (Cρ p ρ * W) * W.adjugate := by rw [Matrix.mul_assoc]
      _ = (Cρ p ρ' * V) * W.adjugate := by rw [← h]
      _ = Cρ p ρ' * (V * W.adjugate) := by rw [Matrix.mul_assoc]

/-- Helper: for a primitive form of determinant $1$ and an odd prime `p` every orbit of the proper automorph group
on the non-vanishing lines has exactly two elements. -/
theorem orbit_card_two (hp2 : p ≠ 2) (c : Quotient (slSetoid 1)) (ρ : Fib p 1 c) :
    Nat.card {ρ' : Fib p 1 c // OrbRel p c ρ' ρ} = 2 := by
  obtain ⟨hJdet, hJH, hJJ⟩ := autJ_facts (Quotient.out c)
  obtain ⟨ρ₁, W, hW, hJC⟩ := exists_ρ_mul (p := p) (autJ (Quotient.out c).1 * Cρ p ρ.1)
    (by rw [Matrix.det_mul, hJdet, det_Cρ', one_mul])
  have hNV : NV (Quotient.out c).1 ρ₁ := nv_of_move (Quotient.out c) ρ.2 _ W hJH hJC
  have hne : (⟨ρ₁, hNV⟩ : Fib p 1 c) ≠ ρ := by
    intro h
    have h' : ρ₁ = ρ.1 := congrArg Subtype.val h
    subst h'
    exact not_fixed hp2 (Quotient.out c).2.1 hJJ hJH ρ.2 hJC
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨ρ, orbRel_refl c ρ⟩, ⟨⟨ρ₁, hNV⟩, ⟨autJ (Quotient.out c).1, W, hJdet, hW, hJH, hJC⟩⟩,
    fun h => hne (congrArg (fun x => x.1) h).symm, ?_⟩
  ext ⟨ρ', hρ'⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  obtain ⟨U, V, hU, hV, hUH, hUC⟩ := hρ'
  rcases aut_one_cases (Quotient.out c) U hU hUH with h | h | h | h
  · left; exact Subtype.ext (Subtype.ext (rho_eq_of_mul hV (Or.inl h) hUC))
  · left; exact Subtype.ext (Subtype.ext (rho_eq_of_mul hV (Or.inr h) hUC))
  · right
    subst h
    exact Subtype.ext (Subtype.ext (line_unique hV hW (hUC.symm.trans hJC)))
  · right
    subst h
    have e : Cρ p ρ'.1 * (-V) = Cρ p ρ₁ * W := by
      rw [Matrix.mul_neg, ← hUC, Matrix.neg_mul, neg_neg, hJC]
    have hV' : (-V).det = 1 := by rw [Matrix.det_neg]; simp [hV]
    exact Subtype.ext (Subtype.ext (line_unique hV' hW e))

/-- **Cassels, Ch. 9, Example 12 (iv), the case $d = 1$** (p. 165): *the generalization of (iii) to $d = 1$.* Let $p$ be an odd
prime. Every primitive classically integral binary form of determinant $1$ has the four proper integral automorphs
$\pm I$, $\pm J$ (with $J^{2} = -I$, `autJ`), so the group acts through $\{1, J\}$ on the $N = p - (-1/p)$
sublattices of index $p$ that carry a primitive form of determinant $p^{2}$, and without fixed point (a fixed line
would be a zero of the form). Hence each orbit has two elements and
$$2\, h(p^{2}) = \left(p - \left(\frac{-1}{p}\right)\right) h(1),$$
i.e. $h(p^{2}) = \tfrac{1}{2}\bigl(p - (-1/p)\bigr) h(1)$. (Here `hClasses m` is Cassels' $h(m)$.) -/
@[kb "cassels1978" "Ch. 9, Ex. 12 (iv), p. 165 (d = 1)"]
theorem ex12_iv_one (hp2 : p ≠ 2) :
    2 * (hClasses ((p : ℤ) ^ 2) : ℤ) = ((p : ℤ) - legendreSym p (-1)) * (hClasses 1 : ℤ) := by
  have h1 := ex12_iv_orbits (p := p) (d := 1) one_ne_zero
  rw [one_mul] at h1
  rw [hClasses_eq, hClasses_eq, h1]
  have hnn : 0 ≤ (p : ℤ) - legendreSym p (-1) := by
    have := legendreSym_le_one (p := p) (-1)
    have := hp.out.one_lt
    omega
  set N : ℕ := ((p : ℤ) - legendreSym p (-1)).toNat with hN
  have hNc : (N : ℤ) = (p : ℤ) - legendreSym p (-1) := Int.toNat_of_nonneg hnn
  have hq : ∀ c : Quotient (slSetoid 1), 2 * Nat.card (Quotient (orbSetoid p 1 c)) = N := fun c => by
    have h2 := card_eq_mul_quot (orbSetoid p 1 c) 2 (fun ρ => orbit_card_two hp2 c ρ)
    have h3 := card_fib hp2 c
    omega
  have hM : ∀ c : Quotient (slSetoid 1), Nat.card (Quotient (orbSetoid p 1 c)) = N / 2 := fun c => by
    have := hq c; omega
  have e : (Σ c : Quotient (slSetoid 1), Quotient (orbSetoid p 1 c)) ≃ Quotient (slSetoid 1) × Fin (N / 2) :=
    (Equiv.sigmaCongrRight fun c => (Finite.equivFin (Quotient (orbSetoid p 1 c))).trans
      (finCongr (hM c))).trans (Equiv.sigmaEquivProd _ _)
  unfold hcl
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fin]
  by_cases h0 : Nat.card (Quotient (slSetoid 1)) = 0
  · rw [h0]; simp
  · have hpos : 0 < Nat.card (Quotient (slSetoid 1)) := Nat.pos_of_ne_zero h0
    obtain ⟨⟨c₀⟩, -⟩ := Nat.card_pos_iff.mp hpos
    have h2N : 2 * (N / 2) = N := by have := hq c₀; omega
    generalize N / 2 = M at h2N ⊢
    have hNM : (N : ℤ) = 2 * M := by exact_mod_cast h2N.symm
    rw [← hNc, hNM]
    push_cast
    ring

/-! ### Example 13 (ii): the prime $2$ -/

/-- Helper: the Gram matrix `H` is *properly primitive in shape*: not both diagonal entries are even. -/
def IsProM (H : Matrix (Fin 2) (Fin 2) ℤ) : Prop := ¬ ((2 : ℤ) ∣ H 0 0 ∧ (2 : ℤ) ∣ H 1 1)

/-- Helper: a line is a non-zero of a primitive form modulo $2$ iff the Gram matrix of its index-$2$ sublattice is
not entirely even. -/
theorem nv_iff_not_ev {d : ℤ} (H : PrimMat d) (ρ : Option (ZMod 2)) : NV H.1 ρ ↔ ¬ Ev H.1 ρ := by
  constructor
  · intro hnv hev
    obtain ⟨-, -, hprim⟩ := phi_primMat H hnv
    have hu := hprim 2 (fun i j => by exact_mod_cast hev i j)
    exact not_isUnit_p (p := 2) (by exact_mod_cast hu)
  · intro hn
    by_contra hnv
    apply hn
    have h := p_dvd_gram_of_not_nonvan ρ (H.1 0 0) (H.1 0 1) (H.1 1 1) hnv
    rw [← sym_eta H.2.1] at h
    intro i j
    exact_mod_cast h i j

/-- Helper: a form with a non-vanishing line modulo $2$ is properly primitive in shape. -/
theorem isProM_of_nv {d : ℤ} (H : PrimMat d) {ρ : Option (ZMod 2)} (hρ : NV H.1 ρ) : IsProM H.1 := by
  rintro ⟨h0, h1⟩
  apply (nv_iff_not_ev H ρ).1 hρ
  rcases option_cases ρ with rfl | rfl | rfl
  · exact (ev_none_iff H.2.1).2 h1
  · exact (ev_zero_iff H.2.1).2 h0
  · exact (ev_one_iff H.2.1).2 (dvd_add h0 h1)

/-- Helper: being properly primitive in shape is invariant under proper equivalence. -/
theorem isProM_of_slRel {H H' : Matrix (Fin 2) (Fin 2) ℤ} (hs' : H'ᵀ = H') (h : SLRel H H')
    (hH : IsProM H) : IsProM H' := by
  rintro ⟨h0, h1⟩
  obtain ⟨U, -, hUH⟩ := SLRel.symm h
  have := diag_even_conj (X := U) hs' h0 h1
  rw [hUH] at this
  exact hH this

/-- Helper: a properly primitive form of determinant $d \ge 2$ has only $\pm I$ as proper integral automorphs
(for $d = 3$ the automorphs of order $3$ exist only for improperly primitive forms). -/
theorem aut_pro_pm_one {d : ℤ} (hd : 2 ≤ d) (H : PrimMat d) (hpro : IsProM H.1) (U : Matrix (Fin 2) (Fin 2) ℤ)
    (hU : U.det = 1) (hUH : Uᵀ * H.1 * U = H.1) : U = 1 ∨ U = -1 := by
  obtain ⟨μ, h1, h2, h3, h4⟩ := aut_param H U hU hUH
  by_cases hμ : μ = 0
  · subst hμ
    exact aut_of_mu_zero H U hU h1 h2 h3
  · exfalso
    have hμ2 : μ ^ 2 ≤ 2 := by nlinarith [sq_nonneg (U 0 0 + U 1 1)]
    have hμ1 : μ = 1 ∨ μ = -1 := by
      have : -1 ≤ μ ∧ μ ≤ 1 := by constructor <;> nlinarith
      omega
    apply hpro
    rcases hμ1 with rfl | rfl
    · exact ⟨⟨-U 1 0, by linarith⟩, ⟨U 0 1, by linarith⟩⟩
    · exact ⟨⟨U 1 0, by linarith⟩, ⟨-U 0 1, by linarith⟩⟩

/-- Helper: injectivity of `Emap` when only the forms with a non-vanishing line need have the automorphs $\pm I$. -/
theorem Emap_injective' {d : ℤ} (hd0 : d ≠ 0)
    (haut : ∀ H : PrimMat d, (∃ ρ : Option (ZMod p), NV H.1 ρ) → ∀ U : Matrix (Fin 2) (Fin 2) ℤ, U.det = 1 →
      Uᵀ * H.1 * U = H.1 → U = 1 ∨ U = -1) : Function.Injective (Emap p d) := by
  rintro ⟨c₁, ρ₁⟩ ⟨c₂, ρ₂⟩ h
  have h' : SLRel (Eobj c₁ ρ₁).1 (Eobj c₂ ρ₂).1 := Quotient.exact h
  obtain ⟨V, hV, hVeq⟩ := h'
  obtain ⟨U, hU, hUH, hUC⟩ := transport hd0 (Quotient.out c₁) (Quotient.out c₂) ρ₁.2 V hV hVeq
  have hc : c₁ = c₂ := by
    have : (Quotient.mk _ (Quotient.out c₁) : Quotient (slSetoid d)) = Quotient.mk _ (Quotient.out c₂) :=
      Quotient.sound ⟨U, hU, hUH⟩
    simpa using this
  subst hc
  have hUpm := haut _ ⟨ρ₁.1, ρ₁.2⟩ U hU hUH
  have := rho_eq_of_mul hV hUpm hUC
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext this))

/-- Helper: the number of non-vanishing lines modulo $2$ of a properly primitive form is $2$. -/
theorem card_nv_two {d : ℤ} (H : PrimMat d) (hpro : IsProM H.1) :
    Nat.card {ρ : Option (ZMod 2) // NV H.1 ρ} = 2 := by
  have e : {ρ : Option (ZMod 2) // NV H.1 ρ} ≃ {ρ : Option (ZMod 2) // ρ ≠ rhoOf H.1} :=
    Equiv.subtypeEquivRight fun ρ => by
      rw [nv_iff_not_ev, ev_iff_rhoOf H.2.1 hpro]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  generalize rhoOf H.1 = r
  revert r
  decide

/-- Helper: an improperly primitive form has no non-vanishing line modulo $2$. -/
theorem card_nv_zero {d : ℤ} (H : PrimMat d) (himp : ¬ IsProM H.1) :
    Nat.card {ρ : Option (ZMod 2) // NV H.1 ρ} = 0 := by
  haveI : IsEmpty {ρ : Option (ZMod 2) // NV H.1 ρ} := ⟨fun ρ => himp (isProM_of_nv H ρ.2)⟩
  exact Nat.card_of_isEmpty

/-- Helper: the number of non-vanishing lines modulo $2$ of a properly primitive form is $2$. -/
theorem card_fib_two {d : ℤ} (c : Quotient (slSetoid d)) (hpro : IsProM (Quotient.out c).1) :
    Nat.card (Fib 2 d c) = 2 := card_nv_two (Quotient.out c) hpro

/-- Helper: the fibres of a map with all fibres of the same non-zero finite size `k`. -/
theorem card_eq_mul_of_fibres {α β : Type} (f : α → β) (k : ℕ) (hk : k ≠ 0)
    (h : ∀ b : β, Nat.card {a : α // f a = b} = k) : Nat.card α = Nat.card β * k := by
  have hf := mk_eq_mul_of_fibres f (k : Cardinal.{0}) (fun b => by
    haveI : Finite {a : α // f a = b} := Nat.finite_of_card_ne_zero (by rw [h b]; exact hk)
    rw [← Nat.cast_card, h b])
  unfold Nat.card
  rw [hf, Cardinal.toNat_mul]
  simp

/-- Helper: the fibre of the first projection of the sigma type of lines over a class `c`. -/
def fibEquiv {d : ℤ} (c : Quotient (slSetoid d)) :
    {x : (Σ c' : Quotient (slSetoid d), Fib 2 d c') // x.1 = c} ≃ Fib 2 d c where
  toFun x := x.2 ▸ x.1.2
  invFun ρ := ⟨⟨c, ρ⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨c', ρ'⟩, h⟩
    subst h
    rfl
  right_inv := fun ρ => rfl

/-- Helper: the number of proper classes of properly primitive forms is the number of classes with a properly
primitive representative. -/
theorem hPro_eq_card {d : ℤ} :
    hPro d = Nat.card {c : Quotient (slSetoid d) // IsProM (Quotient.out c).1} := by
  let f : Quotient (proSetoid d) → Quotient (slSetoid d) := Quotient.map (fun G => G.1) (fun G G' h => h)
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | _ G =>
    induction y using Quotient.inductionOn with
    | _ G' =>
    have h0 : (Quotient.mk _ G.1 : Quotient (slSetoid d)) = Quotient.mk _ G'.1 := hxy
    have h1 : SLRel G.1.1 G'.1.1 := Quotient.exact h0
    exact Quotient.sound h1
  have hrange : ∀ c : Quotient (slSetoid d), c ∈ Set.range f ↔ IsProM (Quotient.out c).1 := by
    intro c
    constructor
    · rintro ⟨x, rfl⟩
      induction x using Quotient.inductionOn with
      | _ G =>
      have h1 : SLRel G.1.1 (Quotient.out (f (Quotient.mk _ G))).1 :=
        Quotient.exact (Quotient.out_eq (f (Quotient.mk _ G))).symm
      exact isProM_of_slRel (Quotient.out (f (Quotient.mk _ G))).2.1 h1 G.2
    · intro h
      exact ⟨Quotient.mk _ ⟨Quotient.out c, h⟩, Quotient.out_eq c⟩
  unfold hPro
  rw [← Nat.card_range_of_injective hf]
  exact Nat.card_congr (Equiv.subtypeEquivRight hrange)

/-- Helper: for $d \ge 2$ the number of proper classes of determinant $4d$ is twice the number of proper classes of
properly primitive forms of determinant $d$. -/
theorem hcl_four {d : ℤ} (hd : 2 ≤ d) : hcl (d * ((2 : ℕ) : ℤ) ^ 2) = 2 * hPro d := by
  have hd0 : d ≠ 0 := by omega
  have hbij : Function.Bijective (Emap 2 d) :=
    ⟨Emap_injective' hd0 (fun H ⟨ρ, hρ⟩ U hU hUH => aut_pro_pm_one hd H (isProM_of_nv H hρ) U hU hUH),
      Emap_surjective⟩
  let g : (Σ c : Quotient (slSetoid d), Fib 2 d c) → {c : Quotient (slSetoid d) // IsProM (Quotient.out c).1} :=
    fun x => ⟨x.1, isProM_of_nv (Quotient.out x.1) x.2.2⟩
  have hg : ∀ b, Nat.card {x : (Σ c : Quotient (slSetoid d), Fib 2 d c) // g x = b} = 2 := by
    intro b
    have e : {x : (Σ c : Quotient (slSetoid d), Fib 2 d c) // g x = b} ≃
        {x : (Σ c : Quotient (slSetoid d), Fib 2 d c) // x.1 = b.1} :=
      Equiv.subtypeEquivRight fun x => by
        constructor
        · intro h; exact congrArg Subtype.val h
        · intro h; exact Subtype.ext h
    rw [Nat.card_congr (e.trans (fibEquiv b.1))]
    exact card_fib_two b.1 b.2
  have h1 := card_eq_mul_of_fibres g 2 (by norm_num) hg
  unfold hcl
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), h1, ← hPro_eq_card]
  ring

/-- Helper: a primitive form of determinant divisible by $4$ is not improperly primitive. -/
theorem imp_empty_four {d : ℤ} : IsEmpty (ImpMat (4 * d)) := by
  refine ⟨fun H => ?_⟩
  obtain ⟨α, β, γ, hα, hγ, hβ⟩ := imp_decomp H
  obtain ⟨e, he⟩ := imp_det_eq H hα hγ hβ
  omega

/-- **Cassels, Ch. 9, Example 13 (ii), class numbers for the prime $2$** (p. 165): *the generalization of Example 12
(iii) to $p = 2$.* Let $d \ge 2$ be an integer, `hClasses m` the number of proper classes of primitive classically
integral binary forms of determinant $m$ (all primitive forms), and `hPro d` (Cassels' $h(d)$ of Example 13) the number
of proper classes of *properly* primitive forms of determinant $d$ (a diagonal entry of the Gram matrix is odd). Then
$$h(4d) = 2\, h_{\mathrm{proper}}(d),$$
i.e. each properly primitive class of determinant $d$ contributes exactly the two sublattices of index $2$ on which the
form does not vanish modulo $2$ (they are inequivalent because the proper automorphs of a properly primitive form of
determinant $d \ge 2$ are $\pm I$, `aut_pro_pm_one`, even for $d = 3$ where the improperly primitive forms have
automorphs of order $3$), and each improperly primitive class contributes none (all its values are even); moreover every
primitive form of determinant $4d$ is properly primitive (`ex13_ii_improper`). Compare Example 12 (iii), where for odd $p$
the number of sublattices is $p - (-d/p)$ for every class. For $d = 1$ and $d < 0$ the orbit formula `ex12_iv_orbits`
(valid for $p = 2$) replaces this. -/
@[kb "cassels1978" "Ch. 9, Ex. 13 (ii), p. 165"]
theorem ex13_ii {d : ℤ} (hd : 2 ≤ d) : hClasses (4 * d) = 2 * hPro d := by
  rw [hClasses_eq]
  have h4 : 4 * d = d * ((2 : ℕ) : ℤ) ^ 2 := by push_cast; ring
  rw [h4]
  exact hcl_four hd

/-- **Cassels, Ch. 9, Example 13 (ii), improperly primitive forms of determinant $4d$** (p. 165): there are no
improperly primitive forms of determinant divisible by $4$: a primitive form of determinant $4d$ always has an odd
diagonal entry, so $h'(4d) = 0$ and every primitive class of determinant $4d$ is a properly primitive one,
$h(4d) = $ `hClasses (4 * d)` (the number of all proper classes). Here `hImp m` is the number of proper classes of
improperly primitive forms of determinant `m` and `hPro m` that of properly primitive forms. -/
@[kb "cassels1978" "Ch. 9, Ex. 13 (ii), p. 165 (improperly primitive)"]
theorem ex13_ii_improper (d : ℤ) : hImp (4 * d) = 0 ∧ hPro (4 * d) = hClasses (4 * d) := by
  haveI : IsEmpty (ImpMat (4 * d)) := imp_empty_four
  refine ⟨?_, ?_⟩
  · haveI : IsEmpty (Quotient (impSetoid (4 * d))) :=
      ⟨fun q => Quotient.inductionOn q fun H => IsEmpty.false H⟩
    exact Nat.card_of_isEmpty
  · rw [hClasses_eq]
    unfold hPro hcl
    let e : ProMat (4 * d) ≃ PrimMat (4 * d) :=
      { toFun := fun G => G.1
        invFun := fun H => ⟨H, fun h => (imp_empty_four (d := d)).false ⟨H, h⟩⟩
        left_inv := fun G => rfl
        right_inv := fun H => rfl }
    exact Nat.card_congr (Quotient.congr e (fun G G' => ⟨fun h => h, fun h => h⟩))

/-! #### The sublattices of index $2$, in lattice terms -/

/-- Helper: the value of $\varphi(x, x)$ on the lattice with Gram matrix $\begin{pmatrix} a & b\\ b & c\end{pmatrix}$ in
the basis `B`. -/
theorem phi_lat {S B : Matrix (Fin 2) (Fin 2) ℚ} {a b c : ℤ} (hH : Bᵀ * S * B = cm !![a, b; b, c])
    (w : Fin 2 → ℤ) :
    phi S (B *ᵥ zc w) (B *ᵥ zc w) = ((a * w 0 ^ 2 + 2 * b * w 0 * w 1 + c * w 1 ^ 2 : ℤ) : ℚ) := by
  rw [phi_mulVec, hH]
  simp [cm, zc, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Helper: a lattice has an odd value $\varphi(x, x)$ iff in a basis with Gram matrix
$\begin{pmatrix} a & b\\ b & c\end{pmatrix}$ not both $a$ and $c$ are even. -/
theorem odd_value_iff {S B : Matrix (Fin 2) (Fin 2) ℚ} {a b c : ℤ} (hH : Bᵀ * S * B = cm !![a, b; b, c]) :
    (∃ x ∈ latOf B, ∃ z : ℤ, ¬ (2 : ℤ) ∣ z ∧ phi S x x = z) ↔ ¬ ((2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ c) := by
  constructor
  · rintro ⟨x, hx, z, hz, hphi⟩ ⟨⟨a', ha⟩, ⟨c', hc⟩⟩
    obtain ⟨w, rfl⟩ := mem_latOf.1 hx
    rw [phi_lat hH] at hphi
    have hz' : z = a * w 0 ^ 2 + 2 * b * w 0 * w 1 + c * w 1 ^ 2 := by
      have := hphi.symm
      exact_mod_cast this
    apply hz
    exact ⟨a' * w 0 ^ 2 + b * w 0 * w 1 + c' * w 1 ^ 2, by rw [hz', ha, hc]; ring⟩
  · intro h
    by_cases ha : (2 : ℤ) ∣ a
    · have hc : ¬ (2 : ℤ) ∣ c := fun hc => h ⟨ha, hc⟩
      refine ⟨B *ᵥ zc ![0, 1], col_mem_latOf B 1 |> fun h => by
        simpa [zc, Pi.single_apply] using h, c, hc, ?_⟩
      rw [phi_lat hH]
      simp
    · refine ⟨B *ᵥ zc ![1, 0], mem_latOf.2 ⟨_, rfl⟩, a, ha, ?_⟩
      rw [phi_lat hH]
      simp

open Classical in
/-- **Cassels, Ch. 9, Example 13 (ii), sublattices of index $2$** (p. 165): *the analogue of Example 12 (ii) for
$p = 2$.* In the setting of `ex12_i` (`S` symmetric and regular), let `Γ` be a lattice on which $\varphi$ induces a
primitive integral form of determinant $d$. Call `Γ` *properly primitive* if $\varphi(x, x)$ is odd for some $x \in \Gamma$,
and *improperly primitive* otherwise (then all $\varphi(x, x)$ are even). The number of lattices $\Lambda \subseteq \Gamma$
on which $\varphi$ induces a primitive integral form of determinant $4d$ is $2$ if `Γ` is properly primitive and $0$ if
`Γ` is improperly primitive. (For odd $p$ it is $p - (-d/p)$, `ex12_ii`; the Legendre symbol is not defined for $p = 2$,
and the count depends on the parity type of the form instead.) -/
@[kb "cassels1978" "Ch. 9, Ex. 13 (ii), p. 165 (lattices)"]
theorem ex13_ii_lattice {S : Matrix (Fin 2) (Fin 2) ℚ} (hS : Sᵀ = S) (hSd : S.det ≠ 0) {d : ℤ}
    {Γ : Submodule ℤ (Fin 2 → ℚ)} (hΓ : IsPrimIntLat S Γ d) :
    (({Λ | Λ ≤ Γ ∧ IsPrimIntLat S Λ (d * 4)} : Set (Submodule ℤ (Fin 2 → ℚ))).ncard : ℕ) =
      if ∃ x ∈ Γ, ∃ z : ℤ, ¬ (2 : ℤ) ∣ z ∧ phi S x x = z then 2 else 0 := by
  obtain ⟨B, a, b, c, hB, rfl, hH, hD, hprim⟩ := gamma_data hS hΓ
  have hd0 : d ≠ 0 := by
    intro h0
    have h1 : (Bᵀ * S * B).det = 0 := by
      rw [hH, cm_det, Matrix.det_fin_two_of]
      have : a * c - b * b = 0 := by rw [h0] at hD; linear_combination hD
      simp [this]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
    exact mul_ne_zero (mul_ne_zero hB hSd) hB h1
  have h4 : d * 4 = d * ((2 : ℕ) : ℤ) ^ 2 := by push_cast; ring
  rw [h4]
  have hset : {Λ | Λ ≤ latOf B ∧ IsPrimIntLat S Λ (d * ((2 : ℕ) : ℤ) ^ 2)} =
      Fl (p := 2) B '' (setOf fun ρ : Option (ZMod 2) => NonVan a b c ρ) := by
    ext Λ
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    rw [Fl_char hB hH hD.symm.symm hd0 hprim Λ]
    constructor
    · rintro ⟨ρ, h1, rfl⟩; exact ⟨ρ, h1, rfl⟩
    · rintro ⟨ρ, h1, rfl⟩; exact ⟨ρ, h1, rfl⟩
  rw [hset, Set.ncard_image_of_injective _ (Fl_injective hB), ← Nat.card_coe_set_eq]
  have hs : (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℤ)ᵀ = !![a, b; b, c] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  let H0 : PrimMat d := ⟨!![a, b; b, c], hs, by rw [Matrix.det_fin_two_of]; linarith, fun m hm => by
    exact hprim m (hm 0 0) (hm 0 1) (hm 1 1)⟩
  have e : (setOf fun ρ : Option (ZMod 2) => NonVan a b c ρ) = {ρ : Option (ZMod 2) | NV H0.1 ρ} := rfl
  rw [e]
  have hcard : Nat.card ({ρ : Option (ZMod 2) | NV H0.1 ρ} : Set (Option (ZMod 2))) =
      Nat.card {ρ : Option (ZMod 2) // NV H0.1 ρ} := rfl
  rw [hcard]
  rw [odd_value_iff hH]
  by_cases hpro : (2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ c
  · rw [if_neg (not_not.mpr hpro)]
    exact card_nv_zero H0 (not_not.mpr hpro)
  · rw [if_pos hpro]
    exact card_nv_two H0 hpro

/-! ### Finiteness of the class numbers and fixed lines -/

/-- Helper: the number of proper classes of primitive binary forms of non-zero determinant $d$ is finite (the
finiteness theorem of Cassels Ch. 9, Thm. 1.1, in the form `finite_reduction_SL`). -/
theorem finite_classes {d : ℤ} (hd0 : d ≠ 0) : Finite (Quotient (slSetoid d)) := by
  obtain ⟨S, hS, hSp, hcov⟩ := finite_reduction_SL 1 d hd0
  let T : Set (Matrix (Fin 2) (Fin 2) ℤ) := S ∩ {F | ∀ k : ℤ, (∀ i j, k ∣ F i j) → IsUnit k}
  have hT : T.Finite := hS.subset Set.inter_subset_left
  haveI : Finite T := hT.to_subtype
  let f : T → Quotient (slSetoid d) := fun F =>
    Quotient.mk _ ⟨F.1, (hSp F.1 F.2.1).1, (hSp F.1 F.2.1).2, F.2.2⟩
  refine Finite.of_surjective f ?_
  intro q
  induction q using Quotient.inductionOn with
  | _ H =>
    obtain ⟨F0, hF0, U, hU, hUF⟩ := hcov H.1 H.2.1 H.2.2.1
    have hconj := conj_adj' hU H.1
    rw [hUF] at hconj
    have hprim : ∀ k : ℤ, (∀ i j, k ∣ F0 i j) → IsUnit k := by
      intro k hk
      apply H.2.2.2 k
      intro i j
      rw [← hconj]
      exact dvd_mul3 k _ _ _ hk i j
    refine ⟨⟨F0, hF0, hprim⟩, ?_⟩
    exact Quotient.sound ⟨U.adjugate, by rw [det_adj]; exact hU, hconj⟩

/-- Helper: the number of proper classes of improperly primitive forms is the number of classes without a properly
primitive representative. -/
theorem hImp_eq_card {d : ℤ} :
    hImp d = Nat.card {c : Quotient (slSetoid d) // ¬ IsProM (Quotient.out c).1} := by
  let f : Quotient (impSetoid d) → Quotient (slSetoid d) := Quotient.map (fun G => G.1) (fun G G' h => h)
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | _ G =>
    induction y using Quotient.inductionOn with
    | _ G' =>
    have h0 : (Quotient.mk _ G.1 : Quotient (slSetoid d)) = Quotient.mk _ G'.1 := hxy
    have h1 : SLRel G.1.1 G'.1.1 := Quotient.exact h0
    exact Quotient.sound h1
  have hrange : ∀ c : Quotient (slSetoid d), c ∈ Set.range f ↔ ¬ IsProM (Quotient.out c).1 := by
    intro c
    constructor
    · rintro ⟨x, rfl⟩
      induction x using Quotient.inductionOn with
      | _ G =>
      intro hpro
      have h1 : SLRel (Quotient.out (f (Quotient.mk _ G))).1 G.1.1 :=
        Quotient.exact (Quotient.out_eq (f (Quotient.mk _ G)))
      exact isProM_of_slRel G.1.2.1 h1 hpro G.2
    · intro h
      exact ⟨Quotient.mk _ ⟨Quotient.out c, not_not.mp h⟩, Quotient.out_eq c⟩
  unfold hImp
  rw [← Nat.card_range_of_injective hf]
  exact Nat.card_congr (Equiv.subtypeEquivRight hrange)

/-- Helper: a line fixed by an integral matrix `Y` (that is, $Y C_\rho = C_\rho W$ for an integral matrix `W`)
gives an eigenvector modulo $p$ at which the form `H` does not vanish. -/
theorem eigen_of_fixed {H Y W : Matrix (Fin 2) (Fin 2) ℤ} {ρ : Option (ZMod p)} (hρ : NV H ρ)
    (hW : Y * Cρ p ρ = Cρ p ρ * W) :
    ∃ (u : Fin 2 → ZMod p) (l : ZMod p),
      (Y 0 0 : ZMod p) * u 0 + (Y 0 1 : ZMod p) * u 1 = l * u 0 ∧
      (Y 1 0 : ZMod p) * u 0 + (Y 1 1 : ZMod p) * u 1 = l * u 1 ∧
      (H 0 0 : ZMod p) * u 0 ^ 2 + 2 * (H 0 1 : ZMod p) * u 0 * u 1 + (H 1 1 : ZMod p) * u 1 ^ 2 ≠ 0 := by
  have key : ∀ i j, (((Y * Cρ p ρ) i j : ℤ) : ZMod p) = (((Cρ p ρ * W) i j : ℤ) : ZMod p) := fun i j => by
    rw [hW]
  have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
  cases ρ with
  | none =>
    have e1 := key 0 1
    have e2 := key 1 1
    simp [Cρ, Matrix.mul_apply, Fin.sum_univ_two, hp0] at e1 e2
    refine ⟨![0, 1], (W 1 1 : ZMod p), ?_, ?_, ?_⟩
    · simpa using e1
    · simpa using e2
    · simpa [NV, NonVan] using hρ
  | some t =>
    have e1 := key 0 0
    have e2 := key 1 0
    simp [Cρ, Matrix.mul_apply, Fin.sum_univ_two, hp0, -ZMod.natCast_val, -ZMod.intCast_cast,
      ZMod.natCast_zmod_val] at e1 e2
    refine ⟨![1, t], (W 0 0 : ZMod p), ?_, ?_, ?_⟩
    · simpa using e1
    · simp
      linear_combination e2
    · simpa [NV, NonVan] using hρ

/-- Helper: **no line on which the form does not vanish is fixed** by a proper automorph of the shape
$Y = \tfrac12(t + \mu J_H)$, $\mu = \pm 1$. Precisely: let `H` be a symmetric integral matrix and `Y` an integral matrix
with $Y_{00} - Y_{11} = \mu H_{01}$, $2 Y_{01} = \mu H_{11}$, $-2 Y_{10} = \mu H_{00}$ and $\mu^{2} = 1$ (the shape
given by `aut_param`). If $Y C_\rho = C_\rho W$ then `H` vanishes on the line `ρ` modulo `p` (eigenvectors of such a `Y`
are isotropic). -/
theorem no_fixed_of_param {H Y W : Matrix (Fin 2) (Fin 2) ℤ} {μ : ℤ} (hμ : μ ^ 2 = 1)
    (h1 : Y 0 0 - Y 1 1 = μ * H 0 1) (h2 : 2 * Y 0 1 = μ * H 1 1) (h3 : -2 * Y 1 0 = μ * H 0 0)
    {ρ : Option (ZMod p)} (hρ : NV H ρ) (hW : Y * Cρ p ρ = Cρ p ρ * W) : False := by
  obtain ⟨u, l, E1, E2, hne⟩ := eigen_of_fixed hρ hW
  have c1 := congrArg (Int.cast : ℤ → ZMod p) h1
  have c2 := congrArg (Int.cast : ℤ → ZMod p) h2
  have c3 := congrArg (Int.cast : ℤ → ZMod p) h3
  have cM := congrArg (Int.cast : ℤ → ZMod p) hμ
  push_cast at c1 c2 c3 cM
  apply hne
  linear_combination (-(μ : ZMod p) * u 0 ^ 2) * c3 + (-2 * (μ : ZMod p) * u 0 * u 1) * c1 +
    (-(μ : ZMod p) * u 1 ^ 2) * c2 +
    (-((H 0 0 : ZMod p) * u 0 ^ 2 + 2 * (H 0 1 : ZMod p) * u 0 * u 1 + (H 1 1 : ZMod p) * u 1 ^ 2)) * cM +
    (2 * (μ : ZMod p) * u 1) * E1 + (-2 * (μ : ZMod p) * u 0) * E2

/-! ### Example 12 (iv): $d = 3$ -/

/-- Helper: the proper automorph $R = \begin{pmatrix} \beta + 1 & \gamma \\ -\alpha & -\beta\end{pmatrix}$ of the
improperly primitive form $\begin{pmatrix} 2\alpha & 2\beta + 1 \\ 2\beta + 1 & 2\gamma\end{pmatrix}$ of determinant $3$
(the matrix $\tfrac12(1 + J_H)$ of order $6$, $R^{3} = -I$; it is the element with $t = \mu = 1$ of `aut_param`). -/
def autR (α β γ : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![β + 1, γ; -α, -β]

/-- Helper: the properties of `autR` for $\alpha\gamma = \beta^{2} + \beta + 1$ (the determinant condition
$4\alpha\gamma - (2\beta+1)^{2} = 3$): determinant $1$, it preserves the form and $R^{2} = R - I$. -/
theorem autR_facts {α β γ : ℤ} (hrel : α * γ = β ^ 2 + β + 1) :
    (autR α β γ).det = 1 ∧
    (autR α β γ)ᵀ * !![2 * α, 2 * β + 1; 2 * β + 1, 2 * γ] * autR α β γ = !![2 * α, 2 * β + 1; 2 * β + 1, 2 * γ] ∧
    autR α β γ * autR α β γ = !![β, γ; -α, -β - 1] := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [autR, Matrix.det_fin_two_of]
    linear_combination hrel
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [autR, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | linear_combination (2 * α) * hrel
        | linear_combination (2 * β + 1) * hrel
        | linear_combination (2 * γ) * hrel
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [autR, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | linear_combination (-1 : ℤ) * hrel
        | linear_combination (0 : ℤ) * hrel

/-- Helper: an improperly primitive form of determinant $3$ is
$\begin{pmatrix} 2\alpha & 2\beta + 1 \\ 2\beta + 1 & 2\gamma\end{pmatrix}$ with $\alpha\gamma = \beta^{2} + \beta + 1$. -/
theorem imp_three_data (H : ImpMat 3) :
    ∃ α β γ : ℤ, α * γ = β ^ 2 + β + 1 ∧ H.1.1 = !![2 * α, 2 * β + 1; 2 * β + 1, 2 * γ] := by
  obtain ⟨α, β, γ, hα, hγ, hβ⟩ := imp_decomp H
  have h10 : H.1.1 1 0 = H.1.1 0 1 := by have := congrFun (congrFun H.1.2.1 0) 1; simpa using this
  have hd := H.1.2.2.1
  rw [Matrix.det_fin_two, h10, hα, hγ, hβ] at hd
  refine ⟨α, β, γ, ?_, ?_⟩
  · have h4 : 4 * (α * γ) = 4 * (β ^ 2 + β + 1) := by linear_combination hd
    exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4
  · rw [sym_eta H.1.2.1, hα, hγ, hβ]

/-- Helper: the proper integral automorphs of an improperly primitive form of determinant $3$ are exactly
$\pm I$, $\pm R$ and $\pm R^{-1}$ (the solutions of $t^{2} + 3\mu^{2} = 4$ are $(\pm 2, 0)$ and $(\pm 1, \pm 1)$). -/
theorem aut_three_cases {α β γ : ℤ} (H : PrimMat 3) (hH : H.1 = !![2 * α, 2 * β + 1; 2 * β + 1, 2 * γ])
    (U : Matrix (Fin 2) (Fin 2) ℤ) (hU : U.det = 1) (hUH : Uᵀ * H.1 * U = H.1) :
    U = 1 ∨ U = -1 ∨ U = autR α β γ ∨ U = -autR α β γ ∨ U = (autR α β γ).adjugate ∨
      U = -(autR α β γ).adjugate := by
  obtain ⟨μ, h1, h2, h3, h4⟩ := aut_param H U hU hUH
  rw [hH] at h1 h2 h3
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h1 h2 h3
  have hμ : -1 ≤ μ ∧ μ ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (U 0 0 + U 1 1)]
  obtain ⟨hμ1, hμ2⟩ := hμ
  have ht : ∀ t : ℤ, t ^ 2 + 3 * 1 ^ 2 = 4 → t = 1 ∨ t = -1 := by
    intro t ht
    have : t ^ 2 = 1 := by linarith
    have h5 : (t - 1) * (t + 1) = 0 := by linear_combination this
    rcases mul_eq_zero.mp h5 with h | h
    · left; linarith
    · right; linarith
  interval_cases μ
  · -- μ = -1
    have h4' : (U 0 0 + U 1 1) ^ 2 + 3 * 1 ^ 2 = 4 := by linarith
    rcases ht _ h4' with h | h
    · right; right; right; right; left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [autR, Matrix.adjugate_fin_two_of] <;> omega
    · right; right; right; left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [autR] <;> omega
  · rcases aut_of_mu_zero H U hU (by simpa using h1) (by simpa using h2) (by simpa using h3) with h | h
    · left; exact h
    · right; left; exact h
  · have h4' : (U 0 0 + U 1 1) ^ 2 + 3 * 1 ^ 2 = 4 := by linarith
    rcases ht _ h4' with h | h
    · right; right; left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [autR] <;> omega
    · right; right; right; right; right
      ext i j
      fin_cases i <;> fin_cases j <;> simp [autR, Matrix.adjugate_fin_two_of] <;> omega

/-- Helper: for $d \ge 2$ and a properly primitive class every orbit of non-vanishing lines is a single line. -/
theorem orbit_card_one {d : ℤ} (hd : 2 ≤ d) (c : Quotient (slSetoid d)) (hpro : IsProM (Quotient.out c).1)
    (ρ : Fib p d c) : Nat.card {ρ' : Fib p d c // OrbRel p c ρ' ρ} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨⟨ρ, orbRel_refl c ρ⟩⟩⟩
  have key : ∀ x : {ρ' : Fib p d c // OrbRel p c ρ' ρ}, x.1 = ρ := by
    rintro ⟨ρ', U, V, hU, hV, hUH, hUC⟩
    exact Subtype.ext (rho_eq_of_mul hV (aut_pro_pm_one hd (Quotient.out c) hpro U hU hUH) hUC)
  exact Subtype.ext ((key a).trans (key b).symm)

/-- Helper: for $d = 3$ and an improperly primitive class every orbit of non-vanishing lines has exactly three
elements (the automorph $R$ of order $3$ on lines acts without fixed points). -/
theorem orbit_card_three (c : Quotient (slSetoid 3)) (himp : ¬ IsProM (Quotient.out c).1)
    (ρ : Fib p 3 c) : Nat.card {ρ' : Fib p 3 c // OrbRel p c ρ' ρ} = 3 := by
  have himp' : (2 : ℤ) ∣ (Quotient.out c).1 0 0 ∧ (2 : ℤ) ∣ (Quotient.out c).1 1 1 := not_not.mp himp
  obtain ⟨α, β, γ, hrel, hH⟩ := imp_three_data (⟨Quotient.out c, himp'⟩ : ImpMat 3)
  change (Quotient.out c).1 = _ at hH
  obtain ⟨hRdet, hRH0, hRR⟩ := autR_facts hrel
  rw [← hH] at hRH0
  set H : PrimMat 3 := Quotient.out c with hHdef
  set R := autR α β γ with hRdef
  have hRiH : R.adjugateᵀ * H.1 * R.adjugate = H.1 := by
    have := conj_adj' hRdet H.1
    rwa [hRH0] at this
  have hRidet : R.adjugate.det = 1 := by rw [det_adj]; exact hRdet
  obtain ⟨hRa, hRa'⟩ := adj_mul_self R hRdet
  -- parameters
  have hp1 : ((1 : ℤ)) ^ 2 = 1 := by norm_num
  have hpm : ((-1 : ℤ)) ^ 2 = 1 := by norm_num
  have hR1 : R 0 0 - R 1 1 = 1 * H.1 0 1 := by rw [hH]; simp [hRdef, autR]; ring
  have hR2 : 2 * R 0 1 = 1 * H.1 1 1 := by rw [hH]; simp [hRdef, autR]
  have hR3 : -2 * R 1 0 = 1 * H.1 0 0 := by rw [hH]; simp [hRdef, autR]
  have hI1 : R.adjugate 0 0 - R.adjugate 1 1 = (-1) * H.1 0 1 := by
    rw [hH]; simp [hRdef, autR, Matrix.adjugate_fin_two_of]; ring
  have hI2 : 2 * R.adjugate 0 1 = (-1) * H.1 1 1 := by
    rw [hH]; simp [hRdef, autR, Matrix.adjugate_fin_two_of]
  have hI3 : -2 * R.adjugate 1 0 = (-1) * H.1 0 0 := by
    rw [hH]; simp [hRdef, autR, Matrix.adjugate_fin_two_of]
  set R2 : Matrix (Fin 2) (Fin 2) ℤ := !![β, γ; -α, -β - 1] with hR2def
  have hS1 : R2 0 0 - R2 1 1 = 1 * H.1 0 1 := by rw [hH]; simp [hR2def]; ring
  have hS2 : 2 * R2 0 1 = 1 * H.1 1 1 := by rw [hH]; simp [hR2def]
  have hS3 : -2 * R2 1 0 = 1 * H.1 0 0 := by rw [hH]; simp [hR2def]
  -- the lines `ρ₁`, `ρ₂`
  obtain ⟨ρ₁, W₁, hW₁, hRC⟩ := exists_ρ_mul (p := p) (R * Cρ p ρ.1)
    (by rw [Matrix.det_mul, hRdet, det_Cρ', one_mul])
  obtain ⟨ρ₂, W₂, hW₂, hRiC⟩ := exists_ρ_mul (p := p) (R.adjugate * Cρ p ρ.1)
    (by rw [Matrix.det_mul, hRidet, det_Cρ', one_mul])
  have hNV₁ : NV H.1 ρ₁ := nv_of_move H ρ.2 R W₁ hRH0 hRC
  have hNV₂ : NV H.1 ρ₂ := nv_of_move H ρ.2 R.adjugate W₂ hRiH hRiC
  have hne₁ : ρ₁ ≠ ρ.1 := by
    intro h
    subst h
    exact no_fixed_of_param (H := H.1) hp1 hR1 hR2 hR3 ρ.2 hRC
  have hne₂ : ρ₂ ≠ ρ.1 := by
    intro h
    subst h
    exact no_fixed_of_param (H := H.1) hpm hI1 hI2 hI3 ρ.2 hRiC
  have hne₁₂ : ρ₁ ≠ ρ₂ := by
    intro h
    subst h
    obtain ⟨hW₂a, hW₂a'⟩ := adj_mul_self W₂ hW₂
    have hC1 : Cρ p ρ₁ = R.adjugate * Cρ p ρ.1 * W₂.adjugate := by
      calc Cρ p ρ₁ = Cρ p ρ₁ * (W₂ * W₂.adjugate) := by rw [hW₂a, Matrix.mul_one]
        _ = (Cρ p ρ₁ * W₂) * W₂.adjugate := by rw [Matrix.mul_assoc]
        _ = _ := by rw [← hRiC]
    have hRC1 : R * Cρ p ρ₁ = Cρ p ρ.1 * W₂.adjugate := by
      rw [hC1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hRa, Matrix.one_mul]
    have hfix : R2 * Cρ p ρ.1 = Cρ p ρ.1 * (W₂.adjugate * W₁) := by
      rw [← hRR, Matrix.mul_assoc, hRC, ← Matrix.mul_assoc, hRC1, Matrix.mul_assoc]
    exact no_fixed_of_param (H := H.1) hp1 hS1 hS2 hS3 ρ.2 hfix
  rw [← Set.ncard_univ, Set.ncard_eq_three]
  refine ⟨⟨ρ, orbRel_refl c ρ⟩, ⟨⟨ρ₁, hNV₁⟩, ⟨R, W₁, hRdet, hW₁, hRH0, hRC⟩⟩,
    ⟨⟨ρ₂, hNV₂⟩, ⟨R.adjugate, W₂, hRidet, hW₂, hRiH, hRiC⟩⟩, ?_, ?_, ?_, ?_⟩
  · intro h; exact hne₁ (congrArg (fun x => x.1.1) h).symm
  · intro h; exact hne₂ (congrArg (fun x => x.1.1) h).symm
  · intro h; exact hne₁₂ (congrArg (fun x => x.1.1) h)
  · ext ⟨ρ', hρ'⟩
    simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
    obtain ⟨U, V, hU, hV, hUH, hUC⟩ := hρ'
    have hne : ∀ {A : Matrix (Fin 2) (Fin 2) ℤ} {Wa : Matrix (Fin 2) (Fin 2) ℤ} {ρa : Option (ZMod p)},
        Wa.det = 1 → A * Cρ p ρ.1 = Cρ p ρa * Wa → (U = A ∨ U = -A) → ρ'.1 = ρa := by
      intro A Wa ρa hWa hAC hUA
      rcases hUA with rfl | rfl
      · exact line_unique hV hWa (hUC.symm.trans hAC)
      · have e : Cρ p ρ'.1 * (-V) = Cρ p ρa * Wa := by
          rw [Matrix.mul_neg, ← hUC, Matrix.neg_mul, neg_neg, hAC]
        exact line_unique (by rw [Matrix.det_neg]; simp [hV]) hWa e
    rcases aut_three_cases H hH U hU hUH with h | h | h | h | h | h
    · left; exact Subtype.ext (Subtype.ext (rho_eq_of_mul hV (Or.inl h) hUC))
    · left; exact Subtype.ext (Subtype.ext (rho_eq_of_mul hV (Or.inr h) hUC))
    · right; left; exact Subtype.ext (Subtype.ext (hne hW₁ hRC (Or.inl h)))
    · right; left; exact Subtype.ext (Subtype.ext (hne hW₁ hRC (Or.inr h)))
    · right; right; exact Subtype.ext (Subtype.ext (hne hW₂ hRiC (Or.inl h)))
    · right; right; exact Subtype.ext (Subtype.ext (hne hW₂ hRiC (Or.inr h)))

/-- Helper: the number of classes is the number of properly primitive classes plus that of improperly primitive
classes. -/
theorem hcl_split {d : ℤ} (hd0 : d ≠ 0) : hcl d = hPro d + hImp d := by
  haveI := finite_classes hd0
  classical
  rw [hPro_eq_card, hImp_eq_card]
  unfold hcl
  rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl (fun c : Quotient (slSetoid d) => IsProM (Quotient.out c).1))]

/-- **Cassels, Ch. 9, Example 12 (iv), the case $d = 3$** (p. 165): *the generalization of (iii) to $d = 3$.* Let $p$ be
an odd prime. A primitive binary form of determinant $3$ is either properly primitive (then its proper automorphs
are $\pm I$, `aut_pro_pm_one`, and each of its $N = p - (-3/p)$ non-vanishing sublattices of index $p$ is an orbit) or
improperly primitive (then its proper automorphs form the cyclic group of order $6$ generated by
$R = \tfrac12(1 + J)$, `autR`, which acts on the $N$ non-vanishing sublattices through the quotient of order $3$
without fixed point, `no_fixed_of_param`, so that every orbit has three elements). Hence, with `hPro 3` and `hImp 3` the
numbers of proper classes of properly and of improperly primitive forms of determinant $3$,
$$3\, h(3 p^{2}) = \left(p - \left(\frac{-3}{p}\right)\right)\bigl(3\, h_{\mathrm{pro}}(3) + h_{\mathrm{imp}}(3)\bigr),$$
i.e. $h(3p^{2}) = N\, h_{\mathrm{pro}}(3) + \tfrac{N}{3}\, h_{\mathrm{imp}}(3)$ (so $3 \mid N h_{\mathrm{imp}}(3)$; in fact $3 \mid N$ whenever
there is an improperly primitive class). Here `hClasses m` is Cassels' $h(m)$. (The class numbers are finite,
`finite_classes`.) -/
@[kb "cassels1978" "Ch. 9, Ex. 12 (iv), p. 165 (d = 3)"]
theorem ex12_iv_three (hp2 : p ≠ 2) :
    3 * (hClasses (3 * (p : ℤ) ^ 2) : ℤ) = ((p : ℤ) - legendreSym p (-3)) * (3 * hPro 3 + hImp 3) := by
  have h1 := ex12_iv_orbits (p := p) (d := 3) (by norm_num)
  rw [hClasses_eq, h1]
  haveI hfin := finite_classes (d := 3) (by norm_num)
  haveI : Fintype (Quotient (slSetoid 3)) := Fintype.ofFinite _
  classical
  have hnn : 0 ≤ (p : ℤ) - legendreSym p (-3) := by
    have := legendreSym_le_one (p := p) (-3)
    have := hp.out.one_lt
    omega
  set N : ℕ := ((p : ℤ) - legendreSym p (-3)).toNat with hN
  have hNc : (N : ℤ) = (p : ℤ) - legendreSym p (-3) := Int.toNat_of_nonneg hnn
  have hpro : ∀ c : Quotient (slSetoid 3), IsProM (Quotient.out c).1 →
      Nat.card (Quotient (orbSetoid p 3 c)) = N := fun c hc => by
    have h2 := card_eq_mul_quot (orbSetoid p 3 c) 1 (fun ρ => orbit_card_one (by norm_num) c hc ρ)
    have h3 := card_fib hp2 c
    omega
  have himp : ∀ c : Quotient (slSetoid 3), ¬ IsProM (Quotient.out c).1 →
      3 * Nat.card (Quotient (orbSetoid p 3 c)) = N := fun c hc => by
    have h2 := card_eq_mul_quot (orbSetoid p 3 c) 3 (fun ρ => orbit_card_three c hc ρ)
    have h3 := card_fib hp2 c
    omega
  have hsum : 3 * Nat.card (Σ c : Quotient (slSetoid 3), Quotient (orbSetoid p 3 c)) =
      3 * N * hPro 3 + N * hImp 3 := by
    rw [Nat.card_sigma, Finset.mul_sum]
    have hterm : ∀ c ∈ (Finset.univ : Finset (Quotient (slSetoid 3))),
        3 * Nat.card (Quotient (orbSetoid p 3 c)) = if IsProM (Quotient.out c).1 then 3 * N else N := by
      intro c _
      by_cases hc : IsProM (Quotient.out c).1
      · rw [if_pos hc, hpro c hc]
      · rw [if_neg hc, himp c hc]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul,
      smul_eq_mul, hPro_eq_card, hImp_eq_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Fintype.card_subtype]
    ring
  have hsum' := congrArg (Nat.cast : ℕ → ℤ) hsum
  push_cast at hsum'
  rw [← hNc]
  linear_combination hsum'

/-- **Cassels, Ch. 9, Example 12 (iv), the case $d = 3$, in terms of $h(3)$** (p. 165): since the numbers of properly
and improperly primitive classes of determinant $3$ coincide (Example 13 (i), `ex13_i`; $3$ is not exceptional) one has
$h(3) = 2 h_{\mathrm{pro}}(3)$, and `ex12_iv_three` becomes
$$3\, h(3 p^{2}) = 2 \left(p - \left(\frac{-3}{p}\right)\right) h(3),$$
that is $h(3p^2) = \tfrac{2}{3}\, N\, h(3)$ for odd primes $p$, in contrast with $h(d p^{2}) = N\, h(d)$ of (iii) for
$d \ge 2$, $d \ne 3$. -/
@[kb "cassels1978" "Ch. 9, Ex. 12 (iv), p. 165 (d = 3, total)"]
theorem ex12_iv_three_total (hp2 : p ≠ 2) :
    3 * (hClasses (3 * (p : ℤ) ^ 2) : ℤ) = 2 * ((p : ℤ) - legendreSym p (-3)) * (hClasses 3 : ℤ) := by
  have h := ex12_iv_three (p := p) hp2
  have hpi : hPro 3 = hImp 3 := by
    refine (ex13_i (d := 3) (by norm_num)).2 ?_
    rintro ⟨-, h | ⟨h, -⟩⟩ <;> omega
  have hs := hcl_split (d := 3) (by norm_num)
  rw [hClasses_eq 3, hs, hpi]
  rw [hpi] at h
  push_cast
  linear_combination h

end QuadFormsKB.Siegel.Ch9Ex13
