/-
# The algebra of the window, $y = r(1+\eta)$ in $D_E$

**Layer:** any field $K$, $E = K[\delta]$ = `QE d`, $D_E = (a,b)_E$ = `DE a b d` (as in `GnatSO4`).

* `pureE η` $= \eta_0i + \eta_1j + \eta_2k$ for $\eta\in E^3$, `imvE x` the pure coordinates of $x\in D_E$, `starV η` $=\sigma\circ\eta$.
* **`coe_mul_one_add`**: $x = x_0(1 + \operatorname{pureE}(x_0^{-1}\operatorname{imvE}x))$ when $x_0 = \operatorname{re}x$ is a unit.
* **`mul_sig_star_eq`**: for $y = r(1+p)$, $p = \operatorname{pureE}\eta$: $y\,x\,\sigma(\bar y) = r\sigma(r)\cdot W_\eta(x)$ with
  $W_\eta(x) = (1+p)\,x\,(1 - \sigma(p))$, and $W_\eta(x) = x + D_\eta(x) + Q_\eta(x)$ (`Wmap_eq`) with the linear part
  $D_\eta(x) = px - x\sigma(p)$ and the quadratic part $Q_\eta(x) = -px\sigma(p)$.
* **`coords_Dmap_emb`**: the coordinates of $D_\eta(e_j)$ for the basis $e_j$ of $V_0$ (`emb (Pi.single j 1)`):
  $D_\eta(1) = 2\delta\eta''$ and $D_\eta(\delta e) = \delta[\eta', e] + d(\eta''e + e\eta'')$ ($\eta = \eta' + \delta\eta''$).
* **`sum_conj_emb`**: $\sum_j e_j^{-1}ze_j = 4\operatorname{re}(z)$ over the basis $1,\delta i,\delta j,\delta k$ of $V_0$ (so $y$ is
  recovered from $\varphi_y$ up to a scalar: `gammaV_phiLin`).

Source: Weil 1982, §3.7, pp. 64-65 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSO4

open Quaternion Matrix
open scoped QuadraticAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Quat.Gnat

variable {K : Type*} [Field K] {a b d : K}

/-- $\eta_0 i + \eta_1 j + \eta_2 k\in D_E$. -/
def pureE (η : Fin 3 → QE d) : DE a b d := ⟨0, η 0, η 1, η 2⟩

/-- The pure coordinates of $x\in D_E$. -/
def imvE (x : DE a b d) : Fin 3 → QE d := ![x.imI, x.imJ, x.imK]

/-- $\sigma\circ\eta$. -/
def starV (η : Fin 3 → QE d) : Fin 3 → QE d := fun l => star (η l)

@[simp] theorem re_pureE (η : Fin 3 → QE d) : (pureE η : DE a b d).re = 0 := rfl
@[simp] theorem imI_pureE (η : Fin 3 → QE d) : (pureE η : DE a b d).imI = η 0 := rfl
@[simp] theorem imJ_pureE (η : Fin 3 → QE d) : (pureE η : DE a b d).imJ = η 1 := rfl
@[simp] theorem imK_pureE (η : Fin 3 → QE d) : (pureE η : DE a b d).imK = η 2 := rfl

theorem imvE_pureE (η : Fin 3 → QE d) : imvE (pureE η : DE a b d) = η := by
  funext l; fin_cases l <;> rfl

theorem pureE_add (η η' : Fin 3 → QE d) : (pureE (η + η') : DE a b d) = pureE η + pureE η' := by
  ext <;> simp [pureE]

theorem pureE_smul (r : QE d) (η : Fin 3 → QE d) : (pureE (r • η) : DE a b d) = (r : DE a b d) * pureE η := by
  ext <;> simp [pureE]

theorem sig_pureE (η : Fin 3 → QE d) : sig (pureE η : DE a b d) = pureE (starV η) := by
  ext <;> simp [pureE, starV, sig]

theorem star_pureE (η : Fin 3 → QE d) : star (pureE η : DE a b d) = -pureE η := by
  ext <;> simp [pureE]

theorem sig_coe (r : QE d) : sig (r : DE a b d) = ((star r : QE d) : DE a b d) := by
  ext <;> simp [sig]

/-- **$x = x_0 + \operatorname{pureE}(\operatorname{imvE}x)$.** -/
theorem eq_re_add_pureE (x : DE a b d) : x = (x.re : DE a b d) + pureE (imvE x) := by
  ext <;> simp [pureE, imvE]

/-- **$x = x_0(1 + \operatorname{pureE}(x_0^{-1}\operatorname{imvE}x))$** for a unit $x_0 = \operatorname{re}x$. -/
theorem coe_mul_one_add (x : DE a b d) {r : QE d} (hr : x.re * r = 1) :
    x = (x.re : DE a b d) * (1 + pureE (r • imvE x)) := by
  rw [mul_add, mul_one, pureE_smul, ← mul_assoc, ← QuaternionAlgebra.coe_mul, hr, QuaternionAlgebra.coe_one,
    one_mul]
  exact eq_re_add_pureE x

/-- $W_\eta(x) = (1+p)x(1-\sigma(p))$, $p = \operatorname{pureE}\eta$. -/
def Wmap (η : Fin 3 → QE d) (x : DE a b d) : DE a b d := (1 + pureE η) * x * (1 - pureE (starV η))

/-- The linear part $D_\eta(x) = px - x\sigma(p)$. -/
def Dmap (η : Fin 3 → QE d) (x : DE a b d) : DE a b d := pureE η * x - x * pureE (starV η)

/-- The quadratic part $Q_\eta(x) = -px\sigma(p)$. -/
def Qmap (η : Fin 3 → QE d) (x : DE a b d) : DE a b d := -(pureE η * x * pureE (starV η))

theorem Wmap_eq (η : Fin 3 → QE d) (x : DE a b d) : Wmap η x = x + Dmap η x + Qmap η x := by
  unfold Wmap Dmap Qmap; noncomm_ring

/-- **$y\,x\,\sigma(\bar y) = r\sigma(r)\,W_\eta(x)$** for $y = r(1+\operatorname{pureE}\eta)$. -/
theorem mul_sig_star_eq (r : QE d) (η : Fin 3 → QE d) (x : DE a b d) :
    ((r : DE a b d) * (1 + pureE η)) * x * sig (star ((r : DE a b d) * (1 + pureE η))) =
      ((r * star r : QE d) : DE a b d) * Wmap η x := by
  have hs : sig (star (1 + pureE η : DE a b d)) = 1 - pureE (starV η) := by
    ext <;> simp [sig, pureE, starV]
  rw [star_mul, QuaternionAlgebra.star_coe, sig_mul, sig_coe, hs, QuaternionAlgebra.coe_mul]
  unfold Wmap
  set R : DE a b d := (r : DE a b d)
  set R' : DE a b d := ((star r : QE d) : DE a b d)
  calc R * (1 + pureE η) * x * ((1 - pureE (starV η)) * R') =
      R * ((1 + pureE η) * x * (1 - pureE (starV η)) * R') := by noncomm_ring
    _ = R * (R' * ((1 + pureE η) * x * (1 - pureE (starV η)))) := by
      rw [← QuaternionAlgebra.coe_commutes]
    _ = _ := by noncomm_ring

theorem nrdE_coe (r : QE d) : nrdE (r : DE a b d) = r ^ 2 := by
  simp [nrdE]

theorem nrdE_one_add_pureE (η : Fin 3 → QE d) :
    nrdE (1 + pureE η : DE a b d) = 1 + nrdE (pureE η : DE a b d) := by
  simp [nrdE, pureE]; ring

/-- **Products**: $(1+p)(1+p') = (1+\varepsilon) + \operatorname{pureE}(\eta + \eta' + \chi)$ with $\varepsilon = \operatorname{re}(pp')$,
$\chi = \operatorname{imvE}(pp')$. -/
theorem one_add_mul_one_add (η η' : Fin 3 → QE d) :
    (1 + pureE η : DE a b d) * (1 + pureE η') =
      ((1 + (pureE η * pureE η' : DE a b d).re : QE d) : DE a b d) +
        pureE (η + η' + imvE (pureE η * pureE η' : DE a b d)) := by
  rw [pureE_add, pureE_add, add_mul, one_mul, mul_add, mul_one]
  have := eq_re_add_pureE (pureE η * pureE η' : DE a b d)
  rw [QuaternionAlgebra.coe_add, QuaternionAlgebra.coe_one]
  nth_rw 1 [this]
  abel

/-- **Products in coordinates**: for $x = r(1+p)\cdot r'(1+p')$, $\operatorname{re}x = rr'(1+\varepsilon)$ and
$\operatorname{imvE}x = rr'(\eta + \eta' + \chi)$. -/
theorem re_imvE_mul (r r' : QE d) (η η' : Fin 3 → QE d) :
    (((r : DE a b d) * (1 + pureE η)) * ((r' : DE a b d) * (1 + pureE η'))).re =
        r * r' * (1 + (pureE η * pureE η' : DE a b d).re) ∧
      imvE (((r : DE a b d) * (1 + pureE η)) * ((r' : DE a b d) * (1 + pureE η'))) =
        (r * r') • (η + η' + imvE (pureE η * pureE η' : DE a b d)) := by
  have e : ((r : DE a b d) * (1 + pureE η)) * ((r' : DE a b d) * (1 + pureE η')) =
      ((r * r' : QE d) : DE a b d) * ((1 + pureE η) * (1 + pureE η')) := by
    rw [QuaternionAlgebra.coe_mul]
    have h1 : (1 + pureE η : DE a b d) * (r' : DE a b d) = (r' : DE a b d) * (1 + pureE η) :=
      (QuaternionAlgebra.coe_commutes _ _).symm
    calc (r : DE a b d) * (1 + pureE η) * ((r' : DE a b d) * (1 + pureE η')) =
        (r : DE a b d) * ((1 + pureE η) * (r' : DE a b d)) * (1 + pureE η') := by noncomm_ring
      _ = _ := by rw [h1]; noncomm_ring
  rw [e, one_add_mul_one_add]
  constructor
  · simp [pureE]
  · funext l; fin_cases l <;> simp [imvE, pureE] <;> rfl

theorem re_coe_mul (r : QE d) (x : DE a b d) : ((r : DE a b d) * x).re = r * x.re := by
  rw [QuaternionAlgebra.coe_mul_eq_smul]; rfl

theorem imvE_coe_mul (r : QE d) (x : DE a b d) : imvE ((r : DE a b d) * x) = r • imvE x := by
  rw [QuaternionAlgebra.coe_mul_eq_smul]; funext l; fin_cases l <;> rfl

@[simp] theorem re_one_add_pureE (η : Fin 3 → QE d) : (1 + pureE η : DE a b d).re = 1 := by simp [pureE]

theorem imvE_one_add_pureE (η : Fin 3 → QE d) : imvE (1 + pureE η : DE a b d) = η := by
  funext l; fin_cases l <;> simp [imvE, pureE] <;> rfl

theorem nrdE_eq_re_mul_star (x : DE a b d) : nrdE x = (x * star x).re := by
  rw [mul_star_eq_nrdE]; rfl

/-! ### The linear part in coordinates -/

/-- The coordinates of $D_\eta(e_j)$ ($e_j$ = `emb (Pi.single j 1)`). Rows $1,2,3$, columns $1,2,3$: the matrix
$[\eta', e_j]$ of `adMat`; row $0$: $2d\,e_j^2\eta''_j$; column $0$: $2\eta''$. -/
def Dco (η : Fin 3 → QE d) : Matrix (Fin 4) (Fin 4) K :=
  !![0, 2 * a * d * (η 0).im, 2 * b * d * (η 1).im, -(2 * a * b * d * (η 2).im);
     2 * (η 0).im, 0, 2 * b * (η 2).re, -(2 * b * (η 1).re);
     2 * (η 1).im, -(2 * a * (η 2).re), 0, 2 * a * (η 0).re;
     2 * (η 2).im, -(2 * (η 1).re), 2 * (η 0).re, 0]

theorem coords_Dmap_emb (η : Fin 3 → QE d) (i j : Fin 4) :
    coords (Dmap η (emb (Pi.single j 1) : DE a b d)) i = Dco (a := a) (b := b) (d := d) η i j := by
  fin_cases i <;> fin_cases j <;>
    simp [Dmap, coords, emb, pureE, starV, Dco, Pi.single_apply, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul] <;> ring

/-! ### Recovering $y$ from $\varphi_y$ -/

/-- The weights $c_j$ with $c_je_j = e_j^{-1}$: $1, (ad)^{-1}, (bd)^{-1}, -(abd)^{-1}$. -/
def cW (a b d : K) : Fin 4 → K := ![1, (a * d)⁻¹, (b * d)⁻¹, -(a * b * d)⁻¹]

/-- **$\sum_je_j^{-1}ze_j = 4\operatorname{re}z$** over the basis $e_j$ of $V_0$. -/
theorem sum_conj_emb (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (z : DE a b d) :
    ∑ j : Fin 4, cW a b d j • ((emb (Pi.single j 1) : DE a b d) * z * emb (Pi.single j 1)) =
      (4 : K) • ((z.re : QE d) : DE a b d) := by
  rw [Fin.sum_univ_four]
  ext : 1 <;> simp [cW, emb, Pi.single_apply] <;> ext <;>
    simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> field_simp <;> ring

/-! ### The matrix of $\varphi_y$ for $y = r(1+\operatorname{pureE}\eta)$ -/

theorem coords_coe_algebraMap_mul (c : K) (x : DE a b d) :
    coords (((algebraMap K (QE d) c : QE d) : DE a b d) * x) = c • coords x := by
  rw [coe_algebraMap_mul, coords_smul]

/-- **The entries of $\varphi_y$**: for $y = r(1+\operatorname{pureE}\eta)\in G^\natural$,
$\varphi_y(e_j)_i = \rho\,(\delta_{ij} + D_{ij} + Q_{ij})$ with $\rho = N(r)/\operatorname{nrd}y\in K$. -/
theorem toMatrix_phiLin_eq {y : DE a b d} {r : QE d} {η : Fin 3 → QE d} (hyr : y = (r : DE a b d) * (1 + pureE η))
    (i j : Fin 4) :
    LinearMap.toMatrix' (phiLin y) i j = (nrdK y)⁻¹ * QuadraticAlgebra.norm r *
      ((Pi.single j (1 : K) : Fin 4 → K) i + Dco (a := a) (b := b) (d := d) η i j +
        coords (Qmap η (emb (Pi.single j 1) : DE a b d)) i) := by
  rw [LinearMap.toMatrix'_apply, phiLin_apply, hyr, mul_sig_star_eq, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star,
    coords_coe_algebraMap_mul, ← hyr, Wmap_eq, coords_add, coords_add, coords_emb, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, Pi.add_apply, Pi.add_apply, coords_Dmap_emb]
  ring

/-- $\operatorname{nrd}(r(1+p)) = r^2(1+\operatorname{nrd}p)$. -/
theorem nrdE_coe_mul_one_add (r : QE d) (η : Fin 3 → QE d) :
    nrdE ((r : DE a b d) * (1 + pureE η)) = r ^ 2 * (1 + nrdE (pureE η : DE a b d)) := by
  rw [nrdE_mul, nrdE_coe, nrdE_one_add_pureE]

/-- **$\rho^2N(1+\operatorname{nrd}p) = 1$** for $\rho = N(r)/\operatorname{nrd}y$, $y = r(1+p)\in G^\natural$. -/
theorem rho_sq_mul_norm {y : (DE a b d)ˣ} (hy : y ∈ Gnat a b d) {r : QE d} {η : Fin 3 → QE d}
    (hyr : (y : DE a b d) = (r : DE a b d) * (1 + pureE η)) :
    ((nrdK (y : DE a b d))⁻¹ * QuadraticAlgebra.norm r) ^ 2 *
      QuadraticAlgebra.norm (1 + nrdE (pureE η : DE a b d)) = 1 := by
  have h0 := nrdK_ne_zero hy
  have h1 : algebraMap K (QE d) (nrdK (y : DE a b d)) = r ^ 2 * (1 + nrdE (pureE η : DE a b d)) := by
    rw [← nrdE_eq_nrdK hy, hyr, nrdE_coe_mul_one_add]
  have h2 := congrArg QuadraticAlgebra.norm h1
  rw [QuadraticAlgebra.norm_algebraMap, map_mul, map_pow] at h2
  rw [mul_pow, inv_pow, mul_assoc, ← h2]
  field_simp

/-! ### Recovering $y$ from $\varphi_y$ -/

/-- $\Gamma(g) = \sum_jc_j\,g(e_j)e_j$ for a matrix $g$ on $V_0$. -/
def gammaV (g : Matrix (Fin 4) (Fin 4) K) : DE a b d :=
  ∑ j : Fin 4, cW a b d j • ((emb (fun i => g i j) : DE a b d) * emb (Pi.single j 1))

/-- **$\Gamma(\varphi_y) = 4\operatorname{nrd}(y)^{-1}\,y\,\sigma(\operatorname{re}y)$.** -/
theorem gammaV_phiLin (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (y : DE a b d) :
    gammaV (LinearMap.toMatrix' (phiLin y)) =
      (4 * (nrdK y)⁻¹) • (y * ((star y.re : QE d) : DE a b d)) := by
  have hcol : ∀ j : Fin 4, (fun i => LinearMap.toMatrix' (phiLin y) i j) = phiLin y (Pi.single j 1) := by
    intro j; funext i; rw [LinearMap.toMatrix'_apply]
  unfold gammaV
  simp_rw [hcol, emb_phiLin h2, smul_mul_assoc, smul_comm (cW a b d _) (nrdK y)⁻¹, ← Finset.smul_sum]
  have e : ∀ j : Fin 4, cW a b d j • (y * emb (Pi.single j 1) * sig (star y) * (emb (Pi.single j 1) : DE a b d)) =
      y * (cW a b d j • ((emb (Pi.single j 1) : DE a b d) * sig (star y) * emb (Pi.single j 1))) := by
    intro j; rw [mul_smul_comm]; noncomm_ring
  simp_rw [e, ← Finset.mul_sum, sum_conj_emb ha hb hd]
  have hre : (sig (star y)).re = star y.re := by
    rw [re_sig, QuaternionAlgebra.re_star, zero_mul, add_zero]
  rw [hre, mul_smul_comm, smul_smul, mul_comm]

/-- **$\varphi_{\lambda x} = (N(\lambda)/\lambda^2)\,\varphi_x$** for a scalar $\lambda\in E$ with $\lambda^2\in K$. -/
theorem phiLin_coe_mul (l : QE d) (x : DE a b d) (hl : (l ^ 2).im = 0) :
    phiLin ((l : DE a b d) * x) = ((l ^ 2).re⁻¹ * QuadraticAlgebra.norm l) • phiLin x := by
  refine LinearMap.ext fun w => ?_
  rw [phiLin_apply, LinearMap.smul_apply, phiLin_apply, smul_smul]
  have hs : (l : DE a b d) * x * emb w * sig (star ((l : DE a b d) * x)) =
      ((l * star l : QE d) : DE a b d) * (x * emb w * sig (star x)) := by
    rw [star_mul, QuaternionAlgebra.star_coe, sig_mul, sig_coe, QuaternionAlgebra.coe_mul]
    calc (l : DE a b d) * x * emb w * (sig (star x) * ((star l : QE d) : DE a b d)) =
        (l : DE a b d) * ((x * emb w * sig (star x)) * ((star l : QE d) : DE a b d)) := by noncomm_ring
      _ = (l : DE a b d) * (((star l : QE d) : DE a b d) * (x * emb w * sig (star x))) := by
        rw [← QuaternionAlgebra.coe_commutes]
      _ = _ := by noncomm_ring
  have hn : nrdK ((l : DE a b d) * x) = (l ^ 2).re * nrdK x := by
    unfold nrdK; rw [nrdE_mul, nrdE_coe, re_mul_of_im_eq_zero hl]
  rw [hs, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, coords_coe_algebraMap_mul, smul_smul, hn, mul_inv]
  ring_nf

/-- **$\Gamma(G) = 4 + \sum_jc_j(G e_j - e_j)e_j$.** -/
theorem gammaV_eq_four_add (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (G : Matrix (Fin 4) (Fin 4) K) :
    gammaV G = (4 : K) • (1 : DE a b d) +
      ∑ j : Fin 4, cW a b d j • ((emb (fun i => G i j - (1 : Matrix (Fin 4) (Fin 4) K) i j) : DE a b d) *
        emb (Pi.single j 1)) := by
  have h1 : ∀ j : Fin 4, (fun i => (1 : Matrix (Fin 4) (Fin 4) K) i j) = Pi.single j 1 := by
    intro j; funext i; by_cases h : i = j
    · subst h; simp
    · rw [Matrix.one_apply_ne h, Pi.single_eq_of_ne h]
  have h4 : ∑ j : Fin 4, cW a b d j • ((emb (Pi.single j 1) : DE a b d) * emb (Pi.single j 1)) =
      (4 : K) • (1 : DE a b d) := by
    have := sum_conj_emb ha hb hd (1 : DE a b d)
    simp only [mul_one] at this
    rw [this, QuaternionAlgebra.re_one, QuaternionAlgebra.coe_one]
  unfold gammaV
  rw [← h4, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_add, ← add_mul, ← emb_add]
  congr 3
  funext i; rw [Pi.add_apply, ← h1 j]; ring

end QuadFormsKB.Quat.Gnat
