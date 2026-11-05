/-
# Hanke 2011, §6: the proper mass and the local densities of one genus (Definition 6.1, Theorem 6.2, Corollary 6.3)

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §6, pp. 25–26.

**Setting.** $F$ a number field of degree $d$, $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$ in $n$ variables
(of any signature), $L = \mathcal O_F^n \subseteq (F^n, Q_0)$, so that the local forms $\psi_{\mathfrak p}$ of $L_{\mathfrak p}$ are
$Q_0$ itself in the standard basis, and $\det_H(L) = \det_H(Q_0)$ (`detH_stdLat_comp`), with associated ideal
$I(\det_H L) = \det_H(Q_0)\mathcal O_F$, of norm $N_{F/\mathbb Q}(I(S)) = |N_{F/\mathbb Q}(\det_H Q_0)|$.

* **Definition 6.1** (`massPlus`): the proper mass $\mathrm{Mass}^+(L)$ is Hanke's mass $\mathrm{Mass}(\Lambda,\varphi)$ of
  [Hanke 2005, (5.4)] (`Hanke2005.hankeMass`). For a totally positive definite $Q_0$ it is
  $\sum 1/|SO(M)| = 2\,\mathrm{Mass}(L)$ with the repository's mass $\mathrm{Mass}(L) = \sum1/|O(M)|$ (`massPlus_definite`).
* `constC Q₀` $= C_{\vec\sigma_\infty,n}$ (p. 26), with $r_v = \min(\sigma_{v,+},\sigma_{v,-})$ the Witt index at a real place:
  $C = \prod_{v\ \mathrm{real}}2\cdot2^{-nr_v/2}V(n-r_v)V(r_v)\cdot\prod_{v\ \mathrm{complex}}2^{n(n-3)/2}V(n)$ (`volV_eq_tauR`:
  the paper's $V(r)$ is Hanke 2005's $\tau_{\mathbb R}(SO_r(\mathbb R))$).
* `localBeta v Q₀` $= \beta_{\psi_{\mathfrak p},\mathfrak p}(\psi_{\mathfrak p})$, Hanke's local density of $L_{\mathfrak p}$ in the Gram
  coordinates of $\psi_{\mathfrak p} = \tfrac12H$ (`Hanke2005.hankeBeta`, the convention of [14] used in the proof of Theorem 6.2).
* **Theorem 6.2, for one genus** (`theorem_6_2_genus`), $n \ge 3$, any number field, any signature:
  $$\mathrm{Mass}^+(L) = \frac{2|\Delta_F|^{n(n-1)/4}}{C_{\vec\sigma_\infty,n}}\cdot\frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}
  {N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}\cdot\prod_{\mathfrak p}\beta_{\psi_{\mathfrak p},\mathfrak p}(\psi_{\mathfrak p})^{-1}.$$
  This is the identity displayed at the end of the paper's proof of Theorem 6.2 (p. 26). Theorem 6.2 itself sums it
  over the genera $G \in \mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)$ and identifies the sum with $M^*$ by Lemma 3.7.
* **Corollary 6.3, for one genus** (`cor_6_3_genus`): $F$ totally real, $Q_0$ totally positive definite, $n \ge 3$:
  $$\mathrm{Mass}(L) = \sum_{[M]\in\mathrm{gen}(L)}\frac1{|O(M)|} = \frac{|\Delta_F|^{n(n-1)/4}}{V(n)^{[F:\mathbb Q]}}\cdot
  \frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}{N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}\cdot\prod_{\mathfrak p}\beta_{\psi_{\mathfrak p},\mathfrak p}(\psi_{\mathfrak p})^{-1},$$
  the repository's mass (`Lattices.mass`) in the paper's normalization. With Hanke 2005's Theorem 2.1 and $\tau = 2$
  (`Hanke2005.theorem21_tau_two`) these are **unconditional**.
-/
import QuadFormsKB.Literature.Hanke2011Structure.HessianSquareclass
import QuadFormsKB.Literature.Hanke2011Structure.BinaryGlobal
import QuadFormsKB.Literature.Hanke2005.TheoremTwoOne
import QuadFormsKB.Literature.Hanke2005.MassDefinite

namespace QuadFormsKB.Hanke2011Structure

open NumberField IsDedekindDomain Real QuadFormsKB.Lattices QuadFormsKB.Hanke2005
open scoped ENNReal

noncomputable section

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### Definition 6.1 and the constants -/

/-- **Definition 6.1** (p. 25): the *proper mass* $\mathrm{Mass}^+(L)$ of the lattice $L = \mathcal O_F^n$ on
$(F^n, Q_0)$, the quantity $\mathrm{Mass}(\Lambda,\varphi)$ of Hanke's thesis [14, eq. (5.4), p. 26]
(`Hanke2005.hankeMass`, in the form (5.6)), a sum over the proper classes in the genus. -/
@[kb "hanke2011structure" "Def. 6.1, p. 25"]
def massPlus (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) : ℝ≥0∞ := hankeMass Q₀ hQ

/-- **$\mathrm{Mass}^+ = 2\,\mathrm{Mass}$ for a totally definite lattice** (used in the proof of Corollary 6.3: "we can replace the
proper mass by the mass because $\mathrm{Mass}^+(G) = 2\mathrm{Mass}(G)$"), with $\mathrm{Mass}$ the repository's `Lattices.mass`. -/
@[kb "hanke2011structure" "Cor. 6.3, proof, p. 27 (Mass⁺ = 2 Mass)"]
theorem massPlus_definite [IsTotallyReal F] (hn : 1 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) :
    massPlus Q₀ hQ = ENNReal.ofReal (2 * mass (Q₀.map (algebraMap (𝓞 F) F)) (Tamagawa.stdLat F n)) :=
  hankeMass_definite_eq_two_mul_mass hn Q₀ hQ hpd

/-- **The paper's $V(r)$ is Hanke 2005's $\tau_{\mathbb R}(SO_r(\mathbb R))$** (`tauR`). -/
theorem volV_eq_tauR (r : ℕ) : volV r = tauR r := by
  unfold volV tauR
  have e : ∏ i ∈ Finset.Icc 1 r, (Gamma ((i : ℝ) / 2))⁻¹ = ∏ l ∈ Finset.range r, (Gamma (((l : ℝ) + 1) / 2))⁻¹ := by
    rw [show Finset.Icc 1 r = Finset.Ico 1 (r + 1) from rfl, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine Finset.prod_congr rfl fun l _ => ?_
    push_cast; ring_nf
  rw [e]

open Classical in
/-- **The archimedean constant** $C_{\vec\sigma_\infty,n}$ of Theorem 6.2 (p. 26) for the signature vector of $Q_0$:
$$C_{\vec\sigma_\infty,n} = \prod_{v\ \mathrm{real}}2\cdot2^{-nr_v/2}\,V(n - r_v)\,V(r_v)\cdot
  \prod_{v\ \mathrm{complex}}2^{n(n-3)/2}\,V(n),\qquad r_v = \min(\sigma_{v,+},\sigma_{v,-}),$$
($r_v$ the Witt index of $Q_0$ at $v$, `Hanke2005.rAt`), the product of Hanke 2005's volumes $\mathrm{vol}_C(C_v)$ of the
normal forms (`volCReal`, `volCComplex`). -/
@[kb "hanke2011structure" "Thm. 6.2, p. 26 (C_{σ,n})"]
def constC (Q₀ : QuadForm (𝓞 F) n) : ℝ :=
  ∏ w : InfinitePlace F, if w.IsReal then volCReal (n - rAt Q₀ w) (rAt Q₀ w) else volCComplex n

open Classical in
theorem constC_pos (Q₀ : QuadForm (𝓞 F) n) : 0 < constC Q₀ := by
  unfold constC
  refine Finset.prod_pos fun w _ => ?_
  split_ifs
  · unfold volCReal
    have := tauR_pos (n - rAt Q₀ w); have := tauR_pos (rAt Q₀ w); positivity
  · unfold volCComplex
    have := tauR_pos n; positivity

open Classical in
/-- **$C_{\vec\sigma_\infty,n} = V(n)^{[F:\mathbb Q]}$ for a totally definite signature** (Corollary 6.3, proof). -/
@[kb "hanke2011structure" "Cor. 6.3, proof, p. 27 (C = V(n)^[F:Q])"]
theorem constC_definite [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) :
    constC Q₀ = volV n ^ Module.finrank ℚ F := by
  unfold constC
  have hw : ∀ w : InfinitePlace F, (if w.IsReal then volCReal (n - rAt Q₀ w) (rAt Q₀ w) else volCComplex n) =
      tauR n := fun w => by
    rw [ite_eq_left_iff.mpr (fun h => absurd (IsTotallyReal.isReal w) h), rAt_eq_zero Q₀ hQ hpd, Nat.sub_zero, volCReal_zero]
  rw [Finset.prod_congr rfl fun w _ => hw w, Finset.prod_const, Finset.card_univ, volV_eq_tauR,
    ← Fintype.card_congr embPlaceH, AlgHom.card]

/-- **The local density** $\beta_{\psi_{\mathfrak p},\mathfrak p}(\psi_{\mathfrak p})$ of $L_{\mathfrak p} = \mathcal O_{\mathfrak p}^n$ with the Gram
matrix $\psi_{\mathfrak p} = \tfrac12H_{Q_0}$ (Hanke's convention [14], `Hanke2005.hankeBeta`; proof of Theorem 6.2, p. 26). -/
@[kb "hanke2011structure" "Thm. 6.2, proof, p. 26 (β_{ψ_p,p}(ψ_p))"]
def localBeta (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) : ℝ :=
  hankeBeta v (std v) (gramOf v (LocalDensity.NF.Qp v Q₀))

/-! ### The archimedean volumes and the norm of the determinant -/

open Classical in
/-- $\prod_v\mathrm{vol}_C(C_v) = |N_{F/\mathbb Q}(\det_H Q_0/2^n)|^{-(n+1)/2}\,C_{\vec\sigma_\infty,n}$ (any signature). -/
theorem prod_volCAt_eq (Q₀ : QuadForm (𝓞 F) n) :
    ∏ w, volCAt Q₀ w =
      |(Algebra.norm ℚ ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det / 2 ^ n) : ℝ)| ^ (-((n : ℝ) + 1) / 2) *
        constC Q₀ := by
  unfold volCAt constC
  rw [Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ (fun w _ => by positivity),
    InfinitePlace.prod_eq_abs_norm, Rat.cast_abs]

theorem abs_norm_div_two_pow (x : F) :
    |(Algebra.norm ℚ (x / 2 ^ n) : ℝ)| = |(Algebra.norm ℚ x : ℝ)| / (2 : ℝ) ^ (n * Module.finrank ℚ F) := by
  have e : x / 2 ^ n = x * algebraMap ℚ F ((2 ^ n)⁻¹) := by
    rw [map_inv₀, map_pow, map_ofNat, div_eq_mul_inv]
  rw [e, map_mul, Algebra.norm_algebraMap]
  push_cast
  rw [abs_mul, abs_pow, abs_inv, abs_pow, abs_two, inv_pow, ← pow_mul, div_eq_mul_inv]

/-- $|N_{F/\mathbb Q}(\det_H Q_0)| > 0$ for $Q_0$ nondegenerate. -/
theorem abs_norm_hessian_pos (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    0 < |(Algebra.norm ℚ ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) : ℝ)| := by
  have h : (Q₀.map (algebraMap (𝓞 F) F)).hessian.det ≠ 0 := by
    rw [QuadForm.hessian_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ
  have : Algebra.norm ℚ ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) ≠ 0 := Algebra.norm_ne_zero_iff.mpr h
  positivity

/-! ### Theorem 6.2 and Corollary 6.3 for one genus -/

/-- **Theorem 6.2 for one genus** (p. 25–26; the identity at the end of its proof): for $n \ge 3$, every number field $F$
and every nondegenerate $Q_0$ over $\mathcal O_F$ (any signature), with $L = \mathcal O_F^n$, $S = \det_H(L)$,
$N_{F/\mathbb Q}(I(S)) = |N_{F/\mathbb Q}(\det_H Q_0)|$ and $N_{F/\mathbb Q}(2\mathcal O_F) = 2^{[F:\mathbb Q]}$,
$$\mathrm{Mass}^+(L) = \frac{2|\Delta_F|^{n(n-1)/4}}{C_{\vec\sigma_\infty,n}}\cdot\frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}
{N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}\cdot\prod_{\mathfrak p}\beta_{\psi_{\mathfrak p},\mathfrak p}(\psi_{\mathfrak p})^{-1}.$$
(The two factors are kept separate as extended nonnegative reals; the first is positive.) Proved from Hanke 2005's
Theorem 2.1 with $\tau = 2$ (`theorem21_tau_two`; the paper cites [14, (5.7)]) and the product formula
$\prod_v|x|_v^{m_v} = |N_{F/\mathbb Q}(x)|$. -/
@[kb "hanke2011structure" "Thm. 6.2, pp. 25–26 (one genus; the last display of the proof)"]
theorem theorem_6_2_genus (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    massPlus Q₀ hQ =
      ENNReal.ofReal (2 * |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) / constC Q₀ *
        |(Algebra.norm ℚ ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) : ℝ)| ^ (((n : ℝ) + 1) / 2) /
        ((2 : ℝ) ^ Module.finrank ℚ F) ^ ((n : ℝ) * (n + 1) / 2)) *
      ENNReal.ofReal (∏' v, localBeta v Q₀)⁻¹ := by
  set d := Module.finrank ℚ F
  set D := |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4)
  set N := |(Algebra.norm ℚ ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) : ℝ)|
  set P := ∏' v, localBeta v Q₀
  have hD : 0 ≤ D := by positivity
  have hN : 0 < N := abs_norm_hessian_pos Q₀ hQ
  have hC := constC_pos Q₀
  have hV : ∏ w, volCAt Q₀ w = (N / (2 : ℝ) ^ (n * d)) ^ (-((n : ℝ) + 1) / 2) * constC Q₀ := by
    rw [prod_volCAt_eq, abs_norm_div_two_pow]
  have hVpos : 0 < ∏ w, volCAt Q₀ w := by rw [hV]; positivity
  unfold massPlus hankeMass
  rw [theorem21_tau_two Q₀ hQ hn, ENNReal.ofReal_mul hD, ← mul_assoc, ENNReal.div_eq_inv_mul,
    ← ENNReal.ofReal_inv_of_pos hVpos, ← mul_assoc]
  congr 1
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h2 : (0 : ℝ) < 2 ^ (n * d) := by positivity
  have e1 : ((2 : ℝ) ^ (n * d)) ^ (((n : ℝ) + 1) / 2) = ((2 : ℝ) ^ d) ^ ((n : ℝ) * (n + 1) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
    congr 1; push_cast; ring
  have key : (N / 2 ^ (n * d)) ^ (-((n : ℝ) + 1) / 2) =
      ((2 : ℝ) ^ d) ^ ((n : ℝ) * (n + 1) / 2) / N ^ (((n : ℝ) + 1) / 2) := by
    rw [show -((n : ℝ) + 1) / 2 = -(((n : ℝ) + 1) / 2) by ring, Real.rpow_neg (by positivity),
      Real.div_rpow hN.le h2.le, e1, inv_div]
  rw [hV, key]
  have hNp : 0 < N ^ (((n : ℝ) + 1) / 2) := Real.rpow_pos_of_pos hN _
  have h2p : 0 < ((2 : ℝ) ^ d) ^ ((n : ℝ) * (n + 1) / 2) := by positivity
  field_simp

/-- **Corollary 6.3 for one genus** (p. 26): for $F$ totally real, $Q_0$ totally positive definite over $\mathcal O_F$
in $n \ge 3$ variables and $L = \mathcal O_F^n$ with $S = \det_H(L)$,
$$\sum_{[M]\in\mathrm{gen}(L)}\frac1{|O(M)|} = \frac{|\Delta_F|^{n(n-1)/4}}{V(n)^{[F:\mathbb Q]}}\cdot
\frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}{N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}\cdot
\prod_{\mathfrak p}\beta_{\psi_{\mathfrak p},\mathfrak p}(\psi_{\mathfrak p})^{-1}$$
(the left side is the repository's `Lattices.mass`; the product of the inverse local densities is positive). Summed
over the genera of $\mathrm{Cls}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)$ this is Corollary 6.3. -/
@[kb "hanke2011structure" "Cor. 6.3, p. 26 (one genus)"]
theorem cor_6_3_genus [IsTotallyReal F] (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) :
    mass (Q₀.map (algebraMap (𝓞 F) F)) (Tamagawa.stdLat F n) =
      |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) / volV n ^ Module.finrank ℚ F *
        |(Algebra.norm ℚ ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) : ℝ)| ^ (((n : ℝ) + 1) / 2) /
        ((2 : ℝ) ^ Module.finrank ℚ F) ^ ((n : ℝ) * (n + 1) / 2) * (∏' v, localBeta v Q₀)⁻¹ ∧
      0 < (∏' v, localBeta v Q₀)⁻¹ := by
  have h := theorem_6_2_genus hn Q₀ hQ
  rw [massPlus_definite (by omega) Q₀ hQ hpd, constC_definite Q₀ hQ hpd] at h
  set K := |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) / volV n ^ Module.finrank ℚ F *
    |(Algebra.norm ℚ ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) : ℝ)| ^ (((n : ℝ) + 1) / 2) /
    ((2 : ℝ) ^ Module.finrank ℚ F) ^ ((n : ℝ) * (n + 1) / 2)
  have hK : 0 < K := by
    have := abs_norm_hessian_pos Q₀ hQ
    have hv : 0 < volV n := by rw [volV_eq_tauR]; exact tauR_pos n
    have hd : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
    positivity
  have hm := mass_pos hpd (Tamagawa.stdLat F n) (HilbertModular.isIntegral_stdLat Q₀)
  have hK2 : 2 * |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) / volV n ^ Module.finrank ℚ F *
      |(Algebra.norm ℚ ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) : ℝ)| ^ (((n : ℝ) + 1) / 2) /
      ((2 : ℝ) ^ Module.finrank ℚ F) ^ ((n : ℝ) * (n + 1) / 2) = 2 * K := by
    simp only [K]; ring
  rw [hK2] at h
  -- the inverse product is positive, else the right side would vanish
  have hP : 0 < (∏' v, localBeta v Q₀)⁻¹ := by
    by_contra hle
    push Not at hle
    rw [ENNReal.ofReal_of_nonpos hle, mul_zero, ENNReal.ofReal_eq_zero] at h
    linarith
  rw [← ENNReal.ofReal_mul (by positivity)] at h
  have h' := (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).mp h
  exact ⟨by linarith, hP⟩

end

end QuadFormsKB.Hanke2011Structure
