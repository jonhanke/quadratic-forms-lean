/-
# The Siegel–Weil formula over $\mathbb Q$ in Mathlib's modular forms

**Setting.** $Q$ a positive definite integral quadratic form (`IntQF n`, Hanke's convention $Q(x) = \sum_{i\le j}q_{ij}x_ix_j$) in
$n = 2k \ge 4$ variables, $H$ its Hessian (Gram matrix of $2Q$), $N = |\det H|$, the genus $\mathrm{Gen}(Q)$ of forms equivalent to $Q$
over $\mathbb R$ and every $\mathbb Z_p$, its $\mathrm{GL}_n(\mathbb Z)$-classes $[Q']$, $\mathrm{Mass}(Q) = \sum_{[Q']}|\mathrm{Aut}(Q')|^{-1}$,
the genus theta series
$$\Theta_{\mathrm{Gen}(Q)}(\tau) = \mathrm{Mass}(Q)^{-1}\sum_{[Q']\in\mathrm{Gen}(Q)}\frac{\Theta_{Q'}(\tau)}{|\mathrm{Aut}(Q')|},\qquad
  \Theta_{Q'}(\tau) = \sum_{x\in\mathbb Z^n}e^{2\pi iQ'(x)\tau}$$
(`Siegel.thetaGen`), the theta character $\chi_Q(d) = \big(\tfrac{(-1)^k\det H}{d}\big)$ (`Siegel.thetaChi`, a Jacobi symbol at an odd
positive representative of $d$ modulo $N$), and the Eisenstein coefficients $a_E(m) = \beta_\infty(m)\prod_p\beta_p(m)$ (`Siegel.aE`,
Siegel's product of local densities, Hanke 2004 (5.3)).

**Main results.**
* `thetaGenMFk`: $\Theta_{\mathrm{Gen}(Q)}$ as a Mathlib `ModularForm (Gamma1 N) k` (`thetaGenMFk_apply`); its $q$-coefficients are the
  genus averages of the representation numbers (`qExpansion_thetaGenMFk_coeff`);
* `thetaGenMFk_slash_gamma0`: $\Theta_{\mathrm{Gen}(Q)}\,|_k\,\gamma = \chi_Q(d)\,\Theta_{\mathrm{Gen}(Q)}$ for
  $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(N)$ ($d = \gamma_{11}$, 0-based), i.e. $\Theta_{\mathrm{Gen}(Q)} \in M_k(\Gamma_0(N), \chi_Q)$
  (Mathlib has no spaces of modular forms with a character; a form on $\Gamma_1(N)$ with this law is the standard encoding);
* **`siegelWeil_rat`**: all of this together with the Siegel–Weil identity in $q$-expansion form,
  $$\Theta_{\mathrm{Gen}(Q)} = E_Q := 1 + \sum_{m\ge1}a_E(m)\,q^m,\qquad q = e^{2\pi i\tau},$$
  every even $n \ge 4$, unconditional. The coefficient identity is Siegel's formula over $\mathbb Z$
  (`Tamagawa.RatBridge.siegelFormula_int_even`, from `siegelFormulaAt_rat_even`).

The comparison with the Hilbert-modular Eisenstein series of the genus at $F = \mathbb Q$ (`HilbertModular.eisQ`, built from the cusp
values) is `siegelWeil_rat_eisQ` in `RatModularEis.lean` when present.

Sources: Siegel, Ann. Math. 36 (1935), Hauptsatz [unverified]; Hanke 2004, (4.5), (5.3), pp. 366–368; Weil, Acta Math. 113 (1965),
Ch. IV [unverified].
-/
import QuadFormsKB.Siegel.GenusEisenstein.ThetaGen
import QuadFormsKB.Siegel.ThetaSplitOf
import QuadFormsKB.Tamagawa.RatBridge

open Complex Filter Topology ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups Real

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Siegel.GenusEis

local notation "Γ₁" => CongruenceSubgroup.Gamma1
local notation "Γ₀" => CongruenceSubgroup.Gamma0

variable {n : ℕ} {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k)

include hn in
lemma even_of_eq_two_mul : Even n := ⟨k, by omega⟩

/-- **$\Theta_{\mathrm{Gen}(Q)}$ as a modular form of weight $k$ for $\Gamma_1(|\det H|)$** ($n = 2k$; `thetaGenMF` is the case $k = 2$). -/
@[kb "hanke2004" "(4.5), p. 366 (genus theta series), weight n/2 [unverified]"]
noncomputable def thetaGenMFk : ModularForm (Γ₁ Q.hessian.det.natAbs) k :=
  (mass Q)⁻¹ • ∑ c ∈ (genusFinite hQ).finite_classes.toFinset.attach, ((c.1.autCard : ℝ))⁻¹ •
    thetaMFGamma1 ((sameGenus_out_of_mem ((Set.Finite.mem_toFinset _).mp c.2)).posDef hQ) hn
      (natAbs_det_pos hQ)
      (isThetaLevel_natAbs_det_genus hQ (even_of_eq_two_mul hn) _
        (sameGenus_out_of_mem ((Set.Finite.mem_toFinset _).mp c.2)))

lemma modularForm_sum_apply_k {N : ℕ} {ι : Type*} (s : Finset ι) (F : ι → ModularForm (Γ₁ N) k) (τ : ℍ) :
    (∑ i ∈ s, F i) τ = ∑ i ∈ s, F i τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

theorem thetaGenMFk_apply (τ : ℍ) : thetaGenMFk hQ hn τ = thetaGen Q τ := by
  rw [thetaGenMFk, thetaGen_eq_sum (genusFinite hQ)]
  simp only [IsSMulApply.smul_apply, real_smul]
  rw [modularForm_sum_apply_k]
  simp only [IsSMulApply.smul_apply, real_smul]
  push_cast
  congr 1
  rw [← Finset.sum_attach (genusFinite hQ).finite_classes.toFinset
    (fun c => ((c.autCard : ℂ))⁻¹ * theta c.out τ)]
  rfl

/-- **The $q$-coefficients of $\Theta_{\mathrm{Gen}(Q)}$ are the genus averages $r_{\mathrm{Gen}}(m)$** (weight $k$). -/
theorem qExpansion_thetaGenMFk_coeff (m : ℕ) :
    (UpperHalfPlane.qExpansion 1 (thetaGenMFk hQ hn)).coeff m = (genusRepAvg Q m : ℂ) := by
  refine (ModularFormClass.qExpansion_coeff_unique (k := k) (c := fun j => (genusRepAvg Q j : ℂ)) one_pos
    (one_mem_strictPeriods_Gamma1 _) (f := thetaGenMFk hQ hn) (fun τ => ?_) m).symm
  rw [thetaGenMFk_apply]
  convert hasSum_thetaGen hQ (genusFinite hQ) (z := (τ : ℂ)) τ.im_pos using 2 with j
  rw [Function.Periodic.qParam, smul_eq_mul, ← Complex.exp_nat_mul]
  congr 2; push_cast; ring

include hQ in
/-- The theta character is a genus invariant: $\chi_{Q'} = \chi_Q$ for $Q'$ in the genus of $Q$ (it depends only on $\det H$). -/
lemma thetaChi_genus {Q' : IntQF n} (h : SameGenus Q Q') (N : ℕ) (d : ℤ) :
    thetaChi Q' k N d = thetaChi Q k N d := by
  simp only [thetaChi, thetaDisc, SameGenus.det_hessian_eq hQ h]

/-- **$\Theta_{\mathrm{Gen}(Q)} \in M_k(\Gamma_0(N), \chi_Q)$**, $N = |\det H|$: for $\gamma \in \Gamma_0(N)$,
$\Theta_{\mathrm{Gen}(Q)}\,|_k\,\gamma = \chi_Q(\gamma_{11})\,\Theta_{\mathrm{Gen}(Q)}$ (each $\Theta_{Q'}$ obeys this law with the same character,
`thetaH_slash_gamma0`, `thetaChi_genus`). -/
@[kb "hanke2004" "§4, p. 364 (theta series in M_k(Γ₀(N), χ_Q)), genus theta series [unverified]"]
theorem thetaGenMFk_slash_gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Γ₀ Q.hessian.det.natAbs) :
    (⇑(thetaGenMFk hQ hn)) ∣[(k : ℤ)] γ =
      (thetaChi Q k Q.hessian.det.natAbs (γ 1 1) : ℂ) • ⇑(thetaGenMFk hQ hn) := by
  classical
  funext τ
  rw [SL_slash_apply, Pi.smul_apply, thetaGenMFk_apply, thetaGenMFk_apply, thetaGen_eq_sum (genusFinite hQ),
    thetaGen_eq_sum (genusFinite hQ), smul_eq_mul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hc' := sameGenus_out_of_mem ((Set.Finite.mem_toFinset _).mp hc)
  have h := congrFun (thetaH_slash_gamma0 (hc'.posDef hQ) hn (natAbs_det_pos hQ)
    (isThetaLevel_natAbs_det_genus hQ (even_of_eq_two_mul hn) _ hc') hγ) τ
  rw [SL_slash_apply, Pi.smul_apply, smul_eq_mul, thetaChi_genus hQ hc'] at h
  simp only [thetaH] at h
  linear_combination ((((mass Q)⁻¹ : ℝ) : ℂ) * (((c.autCard : ℝ))⁻¹ : ℂ)) * h

/-- **The Siegel–Weil formula over $\mathbb Q$ in Mathlib's modular forms**, every even $n = 2k \ge 4$, unconditional. For $Q$ a
positive definite integral quadratic form in $n = 2k$ variables with Hessian $H$ and $N = |\det H|$, there is $g$ in Mathlib's
`ModularForm (Gamma1 N) k` with
1. $g(\tau) = \Theta_{\mathrm{Gen}(Q)}(\tau)$ for every $\tau \in \mathbb H$ (the genus theta series);
2. $g\,|_k\,\gamma = \chi_Q(\gamma_{11})\,g$ for every $\gamma \in \Gamma_0(N)$ (so $g \in M_k(\Gamma_0(N), \chi_Q)$, $\chi_Q$ the theta character);
3. $g = E_Q = 1 + \sum_{m\ge1}a_E(m)q^m$: the $q$-expansion of $g$ (Mathlib's `qExpansion` with period $1$) has constant term $1$ and
   $m$-th coefficient $a_E(m) = \beta_\infty(m)\prod_p\beta_p(m)$, the $m$-th coefficient of Siegel's Eisenstein series of the genus, for
   every $m \ge 1$. -/
@[kb "siegel1935" "Hauptsatz as an identity of modular forms over ℚ: θ_Gen ∈ M_k(Γ₀(N), χ_Q) equals the genus Eisenstein series, every even n ≥ 4 [unverified]; hanke2004 (5.3), p. 368"]
theorem siegelWeil_rat (hQ : Q.PosDef) (hn : n = 2 * k) (hk : 2 ≤ k) :
    ∃ g : ModularForm (Γ₁ Q.hessian.det.natAbs) k,
      (∀ τ : ℍ, g τ = thetaGen Q τ) ∧
      (∀ γ ∈ Γ₀ Q.hessian.det.natAbs,
        (⇑g) ∣[(k : ℤ)] γ = (thetaChi Q k Q.hessian.det.natAbs (γ 1 1) : ℂ) • ⇑g) ∧
      (UpperHalfPlane.qExpansion 1 g).coeff 0 = 1 ∧
      ∀ m : ℕ, 1 ≤ m → (UpperHalfPlane.qExpansion 1 g).coeff m = (aE Q m : ℂ) := by
  refine ⟨thetaGenMFk hQ hn, thetaGenMFk_apply hQ hn, fun γ hγ => thetaGenMFk_slash_gamma0 hQ hn hγ, ?_, fun m hm => ?_⟩
  · rw [qExpansion_thetaGenMFk_coeff, Nat.cast_zero, genusRepAvg_zero hQ (genusFinite hQ), Complex.ofReal_one]
  · rw [qExpansion_thetaGenMFk_coeff,
      (QuadFormsKB.Tamagawa.RatBridge.siegelFormula_int_even (by omega) (even_of_eq_two_mul hn) Q hQ).genusRepAvg_eq
        m (by exact_mod_cast hm)]

end QuadFormsKB.Siegel.GenusEis
