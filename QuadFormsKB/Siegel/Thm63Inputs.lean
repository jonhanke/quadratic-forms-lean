/-
# Theorem 6.3 ($n = 4$) from the cited inputs only

`thm_6_3` (Hanke 2004, Thm 6.3, p. 381) takes four hypotheses besides the local data: Siegel's formula
(`SiegelFormula`), the theta decomposition (`ThetaSplit`), the cusp bound (4.8) (`CuspBound`), and the global lower bound
for $a_E(T')$ (`hglob`). This file discharges the last two:
- `CuspBound c (1/2) C` with $C = \sum_i|\gamma_i|$ from the cited input `EigenformDecompDeligne N χ`
  (`cuspBound_of_eigenformDecomp`, `Siegel/EigenformBound.lean`), once the cusp part $c$ of `ThetaSplit` is known to be
  the coefficient sequence of some $g \in S_2(\Gamma_0(N), \chi)$ (`hcusp`; $\theta_Q - \theta_{\mathrm{Gen}(Q)}$
  is a cusp form, supplies it);
- `hglob` with $\Lambda = \hat\Lambda_4(S, T')$ (`lambdaHat4`) from Siegel's formula (`hglob_four`,
  `Siegel/GlobalLowerBound.lean`), positive under local conditions (`lambdaHat4_pos`).

So Thm 6.3 for $n = 4$ holds with only the inputs `SiegelFormula`, `EigenformDecompDeligne`, `ThetaSplit` and the link
`hcusp` between the last two (`thm_6_3_of_inputs`).

**The final assembly** (`thm_6_3_quaternary`) discharges the remaining links:
- `ThetaSplit` and `hcusp` from part A (`Siegel/ThetaSplitOf.lean`): $g = \Theta_Q - \Theta_{\mathrm{Gen}(Q)}$
  (`thetaGenCusp`) at the level $N = |\det H|$, a level of every form in the genus (`isThetaLevel_natAbs_det_genus`;
  $\det H$ is a genus invariant), with the character $\chi_Q$ = `chiQuat` (the canonical `chiCharLevel` modulo $N_Q$,
  lifted to modulus $|\det H|$ and cast to $\mathbb{C}$; `isCuspFormWithChar_chiQuat`), and $c(m) = b(m)$ by uniqueness of
  $q$-expansions (`qCoeff_thetaGenCusp`);
- $C'_p(T') > 0$ at the bad isotropic $p \in S$ from the $p$-stability of $T'$ (`localConstC'_pos_of_isotropic`; Hanke p. 370,
  "Lemma 3.8 tells us that $C_\mathfrak{p} > 0$", here without a normal form, via $\mathbb{Z}_p$).
What is left are exactly the cited inputs `SiegelFormula Q`, `EigenformDecompDeligne |det H| χ_Q` and `GenusFinite Q`.

**`GenusFinite` discharged**: `GenusFinite Q` is now proved for every positive definite $Q$ (`genusFinite`,
`Siegel/GenusFinite.lean`, Hermite reduction), so `thm_6_3_quaternary'` needs only `SiegelFormula Q` and
`EigenformDecompDeligne |det H| χ_Q`.
-/
import QuadFormsKB.Siegel.GlobalLowerBound
import QuadFormsKB.Siegel.EigenformBound
import QuadFormsKB.Siegel.ThetaSplitOf
import QuadFormsKB.Siegel.GenusFinite
import QuadFormsKB.LocalDensity.BridgeExplicit
import QuadFormsKB.LocalDensity.DVRLowerBounds

open ModularForm
open scoped MatrixGroups

namespace QuadFormsKB.Siegel

open LocalDensity

open Classical in
/-- **Theorem 6.3 from the cited inputs** (Hanke 2004, Thm 6.3, p. 381; proof p. 382: Thm 5.7(b) and (4.8)). Let $Q$ be
a positive definite integral quaternary form, $\chi(p) = \left(\frac{\det H}{p}\right)$. Assume
- `hSF`: Siegel's formula (`SiegelFormula`, cited);
- `hED`: the eigenform decomposition (4.7) with Deligne's bound in $S_2(\Gamma_0(N), \chi)$ (`EigenformDecompDeligne`,
  cited);
- `hTS`: the theta decomposition $r_Q(m) = a_E(m) + c(m)$ (`ThetaSplit`), and `hcusp`: $c(m)$, $m \ge 1$, are the
  coefficients of some $g \in S_2(\Gamma_0(N), \chi)$ ($g = \theta_Q - \theta_{\mathrm{Gen}(Q)}$).

Then there is a constant $C \ge 0$ (namely $\sum_i|\gamma_i|$ for the $\gamma_i$ of (4.7) for $g$) such that for every
$m = T'(m')^2$, $m' = \prod_{p \in S}p^{\nu_p}$, $\nu_p \ge 1$, with $T' \ge 1$ $p$-stable at $p \in S$, $\mathrm{ord}_p(T') \le 1$ at
good $p \in S$, $T'$ locally represented at every $p \mid 2\det H$, and $C'_p(T') > 0$ at the bad isotropic $p \in S$:
$Q$ represents $m$ whenever
$$\frac{\sqrt{(m)_{\mathrm{Iso}}}}{\tau((m)_{\mathrm{Iso}})}\prod_{\substack{p \mid m\ \mathrm{good}\\ \chi(p) = -1}}\frac{p-1}{p+1}
  \;>\; \frac{C}{\hat\Lambda_4(S, T')}\,\tau((m)_{\mathrm{Aniso}})\sqrt{(m)_{\mathrm{Aniso}}},$$
with the explicit $\hat\Lambda_4(S, T') = 6D^{-1/2}(T')_{\mathrm{Aniso}}\prod_{p \mid 2\det H}\beta_p(T')\prod C'_p(T')$
(`lambdaHat4`). *Differences from the paper:* as in `thm_6_3`; the constant $\hat\Lambda_4$ is for the given $T'$ (Hanke takes
the minimum over $B_{\mathbb T}$) and uses $1/\zeta(2)$ in place of $1/L(2,\chi)$ (see `Siegel/GlobalLowerBound.lean`). -/
@[kb "hanke2004" "Thm 6.3, p. 381 (from the cited inputs)"]
theorem thm_6_3_of_inputs (Q : IntQF 4) (hQ : IntQF.PosDef Q) (hSF : SiegelFormula Q)
    {N : ℕ} {χ : DirichletCharacter ℂ N} (hED : EigenformDecompDeligne N χ)
    {aH c : ℕ → ℝ} (hTS : ThetaSplit Q aH c)
    (hcusp : ∃ g : CuspForm (CongruenceSubgroup.Gamma1 N) 2, IsCuspFormWithChar χ g ∧
      ∀ m : ℕ, 1 ≤ m → (c m : ℂ) = qCoeff g m) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {S : Finset ℕ}, (∀ p ∈ S, p.Prime) → ∀ (S₀ : Finset (Fin 4)) {T : ℕ}, 0 < T →
        (∀ p ∈ S, IsPStable Q S₀ p T) → (∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) →
        (∀ p ∈ badPrimes Q, IsLocallyRepresentedAt Q p T) →
        (∀ p ∈ S, IsIsotropicPrime Q p → ¬ IsGoodPrime Q p → 0 < localConstC' Q p T) →
        ∀ (ν : ℕ → ℕ), (∀ p ∈ S, 1 ≤ ν p) → ∀ {m : ℕ}, m = T * (∏ p ∈ S, p ^ ν p) ^ 2 →
        C / lambdaHat4 Q S T * divCount (anisoPart Q m) * √(anisoPart Q m : ℝ) <
          √(isoPart Q m : ℝ) / divCount (isoPart Q m) *
            ∏ p ∈ m.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
              ((p : ℝ) - 1) / ((p : ℝ) + 1) →
        IntQF.Represents Q m := by
  obtain ⟨g, hg, hc⟩ := hcusp
  obtain ⟨C, hC0, hCB⟩ := exists_cuspBound_of_eigenformDecomp hED hg hc
  refine ⟨C, hC0, fun {S} hS S₀ {T} hT hst hT2 hloc hCp ν hν {m} hm hbound => ?_⟩
  exact thm_6_3 Q hQ hSF hTS hCB hS S₀ hT hst hT2 ν hν (lambdaHat4_pos Q hQ S hT hloc hCp)
    (hglob_four Q hQ hSF hS hT) hm hbound

/-! ### $C'_p(T') > 0$ at isotropic primes, without a normal form -/

/-- **$C_p(T') > 0$ at isotropic primes, for any nondegenerate $Q$** (Hanke 2004, p. 370: "Lemma 3.8 tells us that
$C_\mathfrak{p} > 0$"): for $n \ge 3$, $Q$ isotropic over $\mathbb{Q}_p$ and $T' \ne 0$ $p$-stable. Unlike `localConstC_pos`, $Q$
need not be in local normal form: the statement is transported to $\mathbb{Z}_p$ (`localConstC_eq_padic`) and the DVR
version `DVR.localConstC_pos` (via the corrected Lemma 3.8 over $\mathbb{Z}_p$) is applied. -/
@[kb "hanke2004" "Proof of Thm 5.4, p. 370 (C_p > 0, any Q)"]
theorem localConstC_pos_of_isotropic {n : ℕ} (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (p : ℕ)
    [Fact p.Prime] (S₀ : Finset (Fin n)) (hiso : Q.IsotropicIn ℚ_[p]) (T : ℤ) (hT0 : T ≠ 0)
    (hT : IsPStable Q S₀ p T) : 0 < localConstC Q p T := by
  have hQp : (Q.map (Int.castRingHom ℤ_[p])).Nondegenerate := by
    unfold QuadForm.Nondegenerate at hQ ⊢
    have : (Q.map (Int.castRingHom ℤ_[p])).hessian = Q.hessian.map (Int.castRingHom ℤ_[p]) := by
      ext i j; simp [QuadForm.hessian, QuadForm.map]
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]
    exact_mod_cast hQ
  rw [localConstC_eq_padic]
  exact DVR.localConstC_pos ℚ_[p] _ hQp hn (p : ℤ_[p]) PadicInt.irreducible_p two_ne_zero S₀
    ((isotropicIn_iff_padic Q p).1 hiso) (T : ℤ_[p]) (by exact_mod_cast hT0)
    ((isPStable_iff_padic Q S₀ p T).1 hT)

/-- **$C'_p(T') = \min\{1, C_p(T')\} > 0$ at isotropic primes** (any nondegenerate $Q$, $n \ge 3$, $T' \ne 0$ $p$-stable). -/
theorem localConstC'_pos_of_isotropic {n : ℕ} (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (p : ℕ)
    [Fact p.Prime] (S₀ : Finset (Fin n)) (hiso : Q.IsotropicIn ℚ_[p]) (T : ℤ) (hT0 : T ≠ 0)
    (hT : IsPStable Q S₀ p T) : 0 < localConstC' Q p T :=
  lt_min one_pos (localConstC_pos_of_isotropic Q hQ hn p S₀ hiso T hT0 hT)

/-! ### The level $|\det H|$ and the character $\chi_Q$ modulo it -/

/-- For even $n$, the level $N_Q$ divides $|\det H|$ (`isLevel_natAbs_det`). -/
theorem level_dvd_natAbs_det {n : ℕ} {Q : IntQF n} (hQ : Q.PosDef) (hn : Even n) :
    level Q ∣ Q.hessian.det.natAbs :=
  (isLevel_iff_level_dvd hQ.nondegenerate).1 (isLevel_natAbs_det Q hn)

theorem natAbs_det_pos {n : ℕ} {Q : IntQF n} (hQ : Q.PosDef) : 0 < Q.hessian.det.natAbs :=
  Int.natAbs_pos.2 hQ.nondegenerate

/-- **$|\det H|$ is a level of every form in the genus** ($n$ even, $Q$ positive definite): $\det H' = \det H$ for $Q'$ in the
genus (`SameGenus.det_hessian_eq`) and $|\det H'|$ is a level of $Q'$ (`isLevel_natAbs_det`). -/
theorem isThetaLevel_natAbs_det_genus {n : ℕ} {Q : IntQF n} (hQ : Q.PosDef) (hn : Even n) :
    ∀ Q', SameGenus Q Q' → IsThetaLevel Q' Q.hessian.det.natAbs := fun Q' h => by
  rw [SameGenus.det_hessian_eq hQ h]
  exact (isLevel_iff_isThetaLevel (h.posDef hQ).nondegenerate).1 (isLevel_natAbs_det Q' hn)

/-- **The character $\chi_Q$ of a quaternary form, as a complex Dirichlet character modulo $|\det H|$** (Hanke 2004, §4,
p. 364; for $n = 4$, $\chi_Q(d) = \left(\frac{\det H}{d}\right)$): the canonical character `chiCharLevel` modulo the level $N_Q$,
lifted to the modulus $|\det H|$ (a multiple of $N_Q$, `level_dvd_natAbs_det`; Mathlib's `DirichletCharacter.changeLevel`)
and composed with $\mathbb{Z} \hookrightarrow \mathbb{C}$. This is the character of $S_2(\Gamma_0(|\det H|), \chi_Q)$ in which
$\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$ lies (`isCuspFormWithChar_chiQuat`). -/
@[kb "hanke2004" "§4, p. 364 (the character χ, n = 4, as a character mod |det H|) [unverified]"]
noncomputable def chiQuat {Q : IntQF 4} (hQ : Q.PosDef) : DirichletCharacter ℂ Q.hessian.det.natAbs :=
  (DirichletCharacter.changeLevel (level_dvd_natAbs_det hQ (by decide))
    (chiCharLevel hQ (k := 2) rfl)).ringHomComp (Int.castRingHom ℂ)

/-- **Bridge `thetaChi` = `chiQuat`:** for $\gcd(d, |\det H|) = 1$, the multiplier $\chi_Q(d)$ of $\Theta_Q$ on
$\Gamma_0(|\det H|)$ (`thetaChi`) is `chiQuat` at $d \bmod |\det H|$. -/
theorem thetaChi_eq_chiQuat {Q : IntQF 4} (hQ : Q.PosDef) {d : ℤ} (hd : IsCoprime d Q.hessian.det.natAbs) :
    (thetaChi Q 2 Q.hessian.det.natAbs d : ℂ) = chiQuat hQ (d : ZMod Q.hessian.det.natAbs) := by
  have hN := (isThetaLevel_natAbs_det_genus hQ (by decide)) Q (SameGenus.refl Q)
  rw [thetaChi_eq_chiCharLevel hQ (k := 2) rfl (natAbs_det_pos hQ) hN hd, chiQuat, MulChar.ringHomComp_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hd]
  rfl

/-- **$\Theta_Q - \Theta_{\mathrm{Gen}(Q)} \in S_2(\Gamma_0(|\det H|), \chi_Q)$** in the sense of `IsCuspFormWithChar` (Hanke 2004,
(4.3)–(4.5), $n = 4$): `thetaGenCusp` at the level $|\det H|$ transforms with `chiQuat` under $\Gamma_0(|\det H|)$. -/
theorem isCuspFormWithChar_chiQuat {Q : IntQF 4} (hQ : Q.PosDef) (hF : GenusFinite Q) :
    IsCuspFormWithChar (chiQuat hQ)
      (thetaGenCusp hQ hF (k := 2) rfl (natAbs_det_pos hQ) (isThetaLevel_natAbs_det_genus hQ (by decide))) := by
  intro γ hγ
  rw [thetaGenCusp_slash_gamma0 hQ hF rfl _ _ hγ]
  congr 1
  apply thetaChi_eq_chiQuat
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
  obtain ⟨c0, hc0⟩ := hγ
  refine ⟨γ 0 0, -(γ 0 1) * c0, ?_⟩
  have h := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at h
  linear_combination h + (γ 0 1 : ℤ) * hc0

lemma one_mem_strictPeriods_Gamma1 (N : ℕ) :
    (1 : ℝ) ∈ (((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  simp

/-- **The $q$-coefficients of $\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$ are $c(m) = r_Q(m) - a_E(m)$** (`genusCuspCoeff`), by
uniqueness of $q$-expansions (Mathlib's `ModularFormClass.qExpansion_coeff_unique`) applied to `hasSum_genusCuspCoeff`. -/
theorem qCoeff_thetaGenCusp {Q : IntQF 4} (hQ : Q.PosDef) (hF : GenusFinite Q) (m : ℕ) :
    (genusCuspCoeff Q m : ℂ) =
      qCoeff (thetaGenCusp hQ hF (k := 2) rfl (natAbs_det_pos hQ)
        (isThetaLevel_natAbs_det_genus hQ (by decide))) m := by
  rw [qCoeff]
  refine ModularFormClass.qExpansion_coeff_unique (k := 2) (c := fun j => (genusCuspCoeff Q j : ℂ)) one_pos
    (one_mem_strictPeriods_Gamma1 _)
    (f := thetaGenCusp hQ hF (k := 2) rfl (natAbs_det_pos hQ) (isThetaLevel_natAbs_det_genus hQ (by decide)))
    (fun τ => ?_) m
  convert hasSum_genusCuspCoeff hQ hF (k := 2) rfl (natAbs_det_pos hQ)
    (isThetaLevel_natAbs_det_genus hQ (by decide)) τ using 2 with j
  rw [Function.Periodic.qParam, smul_eq_mul, ← Complex.exp_nat_mul]
  congr 2; push_cast; ring

/-! ### Theorem 6.3 for quaternary forms, modulo the cited inputs only -/

open Classical in
/-- **Theorem 6.3** (Hanke 2004, Thm 6.3, p. 381; proof p. 382: Thm 5.7(b) and (4.8) with $k = 2$), **assembled from the
cited inputs only.** Let $Q$ be a positive definite integral quaternary form with Hessian $H$, $\chi(p) = \left(\frac{\det H}{p}\right)$.
The only hypotheses besides $Q$ are the three **cited inputs**:
- `hSF : SiegelFormula Q` (Siegel's formula, Hanke (5.3));
- `hED : EigenformDecompDeligne |det H| χ_Q` (the eigenform decomposition (4.7) of $S_2(\Gamma_0(N), \chi_Q)$, Atkin–Lehner/Li,
  with Deligne's bound), at the level $N = |\det H|$ and the character $\chi_Q$ = `chiQuat hQ`;
- `hGF : GenusFinite Q` (finiteness of the class number of the genus).

Then there is a constant $C \ge 0$ (namely $\sum_i|\gamma_i|$ for the $\gamma_i$ of (4.7) for
$g = \Theta_Q - \Theta_{\mathrm{Gen}(Q)}$) such that for every finite set $S$ of primes, $\nu_p \ge 1$ ($p \in S$), and $T' \ge 1$
with $T'$ $p$-stable at every $p \in S$, $\mathrm{ord}_p(T') \le 1$ at good $p \in S$, and $T'$ locally represented at every
$p \mid 2\det H$: $Q$ represents $m = T'(m')^2$, $m' = \prod_{p \in S}p^{\nu_p}$, whenever
$$\frac{\sqrt{(m)_{\mathrm{Iso}}}}{\tau((m)_{\mathrm{Iso}})}\prod_{\substack{p \mid m\ \mathrm{good}\\ \chi(p) = -1}}\frac{p-1}{p+1}
  \;>\; \frac{C}{\hat\Lambda_4(S, T')}\,\tau((m)_{\mathrm{Aniso}})\sqrt{(m)_{\mathrm{Aniso}}},$$
with the explicit $\hat\Lambda_4(S, T') = 6D^{-1/2}(T')_{\mathrm{Aniso}}\prod_{p \mid 2\det H}\beta_p(T')\prod_{p \in S\cap\mathrm{Iso},\
p\ \mathrm{bad}}C'_p(T') > 0$ (`lambdaHat4`, `lambdaHat4_pos`; $D = \det H/2^4$).

*Hypotheses on $m$ vs. the paper:* Hanke's "locally represented $m$" is formalized through the decomposition
$m = T'(m')^2$ of Thm 5.7(b): $p$-stability of $T'$ at $p \in S$ (Def. 3.6; it includes local representation at $p \in S$) and
local representation of $T'$ at the bad primes $p \mid 2\det H$. The set $S_0$ in `IsPStable` does not enter its definition.

*Differences from the printed statement:*
- "sufficiently large $m$ with a priori bounded divisibility at the anisotropic primes" is not formalized; it is what makes
  the explicit threshold eventually hold;
- "good" (`IsGoodPrime`: $p$ odd, $p \nmid \det H$) in place of $p \nmid N$, so the product runs over a subset of the paper's and
  the threshold is no stronger;
- $\hat\Lambda_4$ is for the given $T'$ (Hanke takes the minimum over $B_{\mathbb T}$), and uses $1/\zeta(2)$ in place of
  $1/L(2,\chi)$ (`Siegel/GlobalLowerBound.lean`), a constant smaller by at most a bounded factor;
- (4.7) is used at the level $|\det H|$ (a multiple of Hanke's $N = N_Q$, and a level of every form in the genus), with
  $\chi_Q$ lifted to that modulus; the constant $C = \sum_i|\gamma_i|$ is for that decomposition;
- *Erratum (candidate):* the printed proof says "(4.8) with $k = n/2 = 4$"; it is $k = n/2 = 2$ (see `thm_6_3`). -/
@[kb "hanke2004" "Thm 6.3, p. 381 (modulo Siegel's formula, (4.7) + Deligne, finiteness of the genus)"]
theorem thm_6_3_quaternary (Q : IntQF 4) (hQ : IntQF.PosDef Q) (hSF : SiegelFormula Q)
    (hED : EigenformDecompDeligne Q.hessian.det.natAbs (chiQuat hQ)) (hGF : GenusFinite Q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {S : Finset ℕ}, (∀ p ∈ S, p.Prime) → ∀ (S₀ : Finset (Fin 4)) {T : ℕ}, 0 < T →
        (∀ p ∈ S, IsPStable Q S₀ p T) → (∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) →
        (∀ p ∈ badPrimes Q, IsLocallyRepresentedAt Q p T) →
        ∀ (ν : ℕ → ℕ), (∀ p ∈ S, 1 ≤ ν p) → ∀ {m : ℕ}, m = T * (∏ p ∈ S, p ^ ν p) ^ 2 →
        C / lambdaHat4 Q S T * divCount (anisoPart Q m) * √(anisoPart Q m : ℝ) <
          √(isoPart Q m : ℝ) / divCount (isoPart Q m) *
            ∏ p ∈ m.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
              ((p : ℝ) - 1) / ((p : ℝ) + 1) →
        IntQF.Represents Q m := by
  have hcusp : ∃ g : CuspForm (CongruenceSubgroup.Gamma1 Q.hessian.det.natAbs) 2,
      IsCuspFormWithChar (chiQuat hQ) g ∧ ∀ m : ℕ, 1 ≤ m → (genusCuspCoeff Q m : ℂ) = qCoeff g m :=
    ⟨_, isCuspFormWithChar_chiQuat hQ hGF, fun m _ => qCoeff_thetaGenCusp hQ hGF m⟩
  obtain ⟨C, hC0, h⟩ := thm_6_3_of_inputs Q hQ hSF hED (thetaSplit_genusCuspCoeff Q) hcusp
  refine ⟨C, hC0, fun {S} hS S₀ {T} hT hst hT2 hloc ν hν {m} hm hb =>
    h hS S₀ hT hst hT2 hloc (fun p hp hI _ => ?_) ν hν hm hb⟩
  obtain ⟨hpP, hiso⟩ := hI
  have := Fact.mk hpP
  exact localConstC'_pos_of_isotropic Q hQ.nondegenerate (by norm_num) p S₀ hiso T
    (by exact_mod_cast hT.ne') (hst p hp)

open Classical in
/-- **Theorem 6.3 for quaternary forms, modulo Siegel's formula and (4.7) + Deligne only** (Hanke 2004, Thm 6.3, p. 381).
The same statement as `thm_6_3_quaternary`, with the input `GenusFinite Q` removed: it is proved for every positive
definite form (`genusFinite`, Hermite reduction). The only hypotheses besides $Q$ positive definite are the two
**cited inputs**
- `hSF : SiegelFormula Q` (Siegel's formula, Hanke (5.3));
- `hED : EigenformDecompDeligne |det H| χ_Q` (the eigenform decomposition (4.7) of $S_2(\Gamma_0(|\det H|), \chi_Q)$ with
  Deligne's bound; $\chi_Q$ = `chiQuat hQ`).

Conclusion, hypotheses on $m = T'(m')^2$, and differences from the printed statement: as in `thm_6_3_quaternary`. -/
@[kb "hanke2004" "Thm 6.3, p. 381 (modulo Siegel's formula and (4.7) + Deligne)"]
theorem thm_6_3_quaternary' (Q : IntQF 4) (hQ : IntQF.PosDef Q) (hSF : SiegelFormula Q)
    (hED : EigenformDecompDeligne Q.hessian.det.natAbs (chiQuat hQ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {S : Finset ℕ}, (∀ p ∈ S, p.Prime) → ∀ (S₀ : Finset (Fin 4)) {T : ℕ}, 0 < T →
        (∀ p ∈ S, IsPStable Q S₀ p T) → (∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) →
        (∀ p ∈ badPrimes Q, IsLocallyRepresentedAt Q p T) →
        ∀ (ν : ℕ → ℕ), (∀ p ∈ S, 1 ≤ ν p) → ∀ {m : ℕ}, m = T * (∏ p ∈ S, p ^ ν p) ^ 2 →
        C / lambdaHat4 Q S T * divCount (anisoPart Q m) * √(anisoPart Q m : ℝ) <
          √(isoPart Q m : ℝ) / divCount (isoPart Q m) *
            ∏ p ∈ m.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
              ((p : ℝ) - 1) / ((p : ℝ) + 1) →
        IntQF.Represents Q m :=
  thm_6_3_quaternary Q hQ hSF hED (genusFinite hQ)

end QuadFormsKB.Siegel
