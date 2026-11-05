/-
# Hanke 2005, (3.3) at non-dyadic places with $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$: from the Jordan shape

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

At a non-dyadic place $\mathfrak p$ a maximal lattice has the Jordan shape $L_\mathfrak p\cong U\perp\pi W$ with $U=\langle u_0,\dots,u_{a-1}\rangle$,
$u_i$ units, $W$ unimodular of rank $b$ and $\overline W$ anisotropic, so $b\le2$ (O'Meara 91:2, §92). This file proves
$$\beta_\mathfrak p(L,L)=\beta(U)\,q^{b(b+1)/2}\,\beta(W)\qquad(\texttt{density\_oddShape})$$
for such a shape (the product formula `localDensityForm_unitSum`, the scaling `localDensityForm_smul_pi`, and the unimodular
closed forms of `Tamagawa/OrthFq.lean`), then the three closed forms
* $b=1$ (then $n=a+1$ is even, $t_\mathfrak p=2$, $\mathfrak p$ ramified in $K$): $\alpha=2q\prod_{i=1}^{m-1}(1-q^{-2i})$;
* $b=2$, $a=2k$: $\alpha=2q^2(q+1)(1-\varepsilon q^{-k})\prod_{i=1}^{k-1}(1-q^{-2i})$, $\varepsilon=\chi_U=\pm1$ ($t=2$ for $\varepsilon=1$, $t=4$ for $\varepsilon=-1$);
* $b=2$, $a=2k+1$: $\alpha=2q^2(q+1)\prod_{i=1}^{k}(1-q^{-2i})$ ($t=3$),
and matches each with $[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\,\xi=q^b\,\xi$ (`siegelDensity_oddRamified`). The only named input is the
classification of the shape and of the local Witt type (`OddMaximalShape`); the density computation is proved.
-/
import QuadFormsKB.Literature.Hanke2005.DensityOddSplit
import QuadFormsKB.Literature.Hanke2005.DensityOddProduct
import QuadFormsKB.Tamagawa.OrbitalEuler

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Tamagawa QuadFormsKB.Lattices QuadForm

section Generic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **$\det H(\langle u\rangle\perp T)=2^a\prod_iu_i\cdot\det H(T)$.** -/
theorem det_hessian_unitSum {b : ℕ} (T : QuadForm R b) :
    ∀ (a : ℕ) (u : Fin a → R), (unitSum T a u).hessian.det = 2 ^ a * (∏ i, u i) * T.hessian.det
  | 0, u => by simp [unitSum]
  | a + 1, u => by
    show (splitForm (u 0) (unitSum T a (Fin.tail u))).hessian.det = _
    rw [det_hessian_splitForm, det_hessian_unitSum T a (Fin.tail u), Fin.prod_univ_succ, pow_succ]
    simp only [Fin.tail]
    ring

/-- **The density of a maximal lattice of odd Jordan shape** ($\pi\nmid2$, $u_i$ units, $W$ unimodular, $T=\pi W$):
$\beta(\langle u\rangle\perp\pi W,\cdot)=\beta(\langle u\rangle)\,q^{b(b+1)/2}\,\beta(W)$. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (density of U ⊥ πW at an odd place)"]
theorem density_oddShape [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    {a b : ℕ} (u : Fin a → R) (hu : ∀ i, IsUnit (u i)) (W T : QuadForm R b) (hW : IsUnit W.hessian.det)
    (hT : ∀ i j, T.coeff i j = π * W.coeff i j) :
    localDensityForm (unitSum T a u) (unitSum T a u) π =
      localDensityForm (QuadForm.diag u) (QuadForm.diag u) π *
        ((q R : ℝ) ^ (b * (b + 1) / 2) * localDensityForm W W π) := by
  have hWn : W.Nondegenerate := hW.ne_zero
  have hH : T.hessian = π • W.hessian := by ext i j; simp [hessian, hT]; ring
  have hTn : T.Nondegenerate := by
    rw [QuadForm.Nondegenerate, hH, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hWn
  rw [localDensityForm_unitSum hπ h2 T hTn (fun i j => ⟨_, hT i j⟩) a u hu,
    localDensityForm_smul_pi hπ hWn hT]

/-- The character of a unimodular form is $\pm1$. -/
theorem chiDisc_pm [Fintype (IsLocalRing.ResidueField R)] [DecidableEq (IsLocalRing.ResidueField R)] {n : ℕ}
    {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (Q : QuadForm R n) (hdet : ¬ π ∣ Q.hessian.det) :
    chiDisc Q = 1 ∨ chiDisc Q = -1 := by
  have h2F : (2 : IsLocalRing.ResidueField R) ≠ 0 := by
    have := res_ne_zero hπ h2
    rwa [map_ofNat] at this
  have hd := res_ne_zero hπ hdet
  unfold chiDisc resGramDet
  exact quadraticChar_dichotomy (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
    (div_ne_zero hd (pow_ne_zero _ h2F)))

end Generic

variable {F : Type} [Field F] [NumberField F]

/-- **The Jordan shape and the local Witt type of a maximal lattice at an odd place** (a **named input**; O'Meara 91:2 and
§92 for the shape, §§63, 92 for the Witt type; Hanke thesis §3, p. 8). For $\mathfrak p\nmid2$ with
$[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\ne1$ and $\Lambda=\mathcal O_F^n$ maximal (with Shimura's hypothesis), the local form
$Q_\mathfrak p$ is $\mathrm{GL}_n(\mathfrak o_\mathfrak p)$-equivalent to $\langle u_0,\dots,u_{a-1}\rangle\perp\pi W$ (`unitSum T a u`, with
$T=\pi W$), $a+b=n$, the $u_i$ units, $W$ a unimodular form in $b$ variables with $b\in\{1,2\}$ and $\overline W$ anisotropic (for
$b=2$ this is $\chi(-\det \overline W)=-1$, i.e. `chiDisc W = -1`), and the local data are as follows.
* $b=1$ and $n$ even (`even_of_shimuraDetHyp` shows that $n$ is even): $t_\mathfrak p=2$ and $\mathfrak p$ is ramified in $K=F(\sqrt\delta)$.
* $b=2$: $\mathfrak p$ is unramified in $K$ (only meaningful for even $n$); for $a$ even, $t_\mathfrak p=2$ if the character of $U$ is $+1$
  and $t_\mathfrak p=4$ if it is $-1$; for $a$ odd, $t_\mathfrak p=3$.

Field: `shape`. Mathematical content: the anisotropic kernel of $\langle u\rangle\perp\pi W$ is the sum of the anisotropic kernels of the
residue forms of the two Jordan components (a Springer-type theorem). -/
@[kb "omeara1963" "91:2, §92, §63 (Jordan shape U ⊥ πW of a maximal lattice at an odd place and its Witt type); Hanke thesis §3, p. 8"]
structure OddMaximalShape (F : Type) [Field F] [NumberField F] : Prop where
  /-- The shape of the local form and the Witt data. -/
  shape : ∀ {n : ℕ}, 3 ≤ n → ∀ Q₀ : QuadForm (𝓞 F) n, Q₀.Nondegenerate → StdIsMaximal Q₀ → ShimuraDetHyp Q₀ →
    ∀ v : HeightOneSpectrum (𝓞 F), IsUnit (2 : v.adicCompletionIntegers F) → dualIndexAt v Q₀ ≠ 1 →
      ∃ (a b : ℕ) (h : b + a = n) (u : Fin a → v.adicCompletionIntegers F)
        (W T : QuadForm (v.adicCompletionIntegers F) b),
        (∀ i, IsUnit (u i)) ∧ IsUnit W.hessian.det ∧ (∀ i j, T.coeff i j = NF.π v * W.coeff i j) ∧
        (b = 1 ∨ b = 2) ∧ (b = 2 → chiDisc W = -1) ∧
        IsGLEquiv (NF.Qp v Q₀) (h ▸ unitSum T a u) ∧
        (b = 1 → Even n → anisoDim v Q₀ = 2 ∧ IsRamifiedAt v Q₀) ∧
        (b = 2 → ¬ IsRamifiedAt v Q₀ ∧
          (Even a → (chiDisc (QuadForm.diag u) = 1 → anisoDim v Q₀ = 2) ∧
            (chiDisc (QuadForm.diag u) = -1 → anisoDim v Q₀ = 4)) ∧
          (Odd a → anisoDim v Q₀ = 3))

/-- **Shimura's hypothesis forces an even valuation of the determinant** (odd $n$, $\mathfrak p\nmid2$): if $n$ is odd and
$[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]=q^b$, then $b$ is even. *Proof:* $|\det H/2^n\cdot c^2|=1$ gives $|c|^2=q^b$, and
$|c|$ is an integral power of $q$. -/
@[kb "hanke2005crelle" "abstract, p. 1; §3, p. 7 (Shimura's condition on det φ for odd n, valuation parity)"]
theorem even_of_shimuraDetHyp (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)
    (hdet : ShimuraDetHyp Q₀) (h2 : IsUnit (2 : v.adicCompletionIntegers F)) {b : ℕ}
    (hdual : dualIndexAt v Q₀ = (normQ v) ^ b) (hodd : Odd n) : Even b := by
  obtain ⟨c, hc0, hc⟩ := hdet hodd v
  set D := (NF.Qp v Q₀).hessian.det with hDdef
  have key : algebraMap F (v.adicCompletion F) ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) = (D : v.adicCompletion F) := by
    rw [hDdef, hessian_det_cast v Q₀]
    have : (Q₀.map (algebraMap (𝓞 F) F)).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
      ext i j; simp [QuadForm.hessian, QuadForm.map]
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have h2n : ‖(2 : v.adicCompletion F)‖ = 1 := by
    have := norm_coe_unit v h2
    have e : (((2 : v.adicCompletionIntegers F)) : v.adicCompletion F) = 2 :=
      map_ofNat (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) 2
    rwa [e] at this
  have hDn : ‖(D : v.adicCompletion F)‖ = ((normQ v) ^ b)⁻¹ := by
    unfold dualIndexAt at hdual
    rw [← hDdef] at hdual
    rw [← inv_inv ‖(D : v.adicCompletion F)‖, hdual]
  rw [map_div₀, map_pow, map_ofNat, key, norm_mul, norm_div, norm_pow, h2n, norm_pow, hDn] at hc
  simp only [one_pow, div_one] at hc
  have hq0 : 0 < normQ v := lt_trans zero_lt_one (one_lt_normQ v)
  have hcz := QuadFormsKB.LocalZeta.norm_eq_absNorm_pow v hc0
  have hA : normQ v = (Ideal.absNorm v.asIdeal : ℝ) := by
    rw [← DensitySD.q_eq v, NF.q_completion]
  rw [hcz, ← hA] at hc
  set z := WithZero.log (Valued.v c) with hz
  have hc' : (normQ v) ^ (2 * z) = (normQ v) ^ (b : ℤ) := by
    have hb : (normQ v) ^ b ≠ 0 := pow_ne_zero _ hq0.ne'
    have h3 : ((normQ v) ^ z) ^ 2 = (normQ v) ^ b := by
      have : ((normQ v) ^ b)⁻¹ * ((normQ v) ^ z) ^ 2 = 1 := hc
      field_simp at this
      linarith
    rw [two_mul, zpow_add₀ hq0.ne', zpow_natCast, ← h3]
    ring
  have := zpow_right_injective₀ hq0 (one_lt_normQ v).ne' hc'
  exact ⟨b / 2, by omega⟩

/-- **(a) The Jordan shape of a maximal lattice at an odd place** (a **named input**; O'Meara 91:2 and §92 for the shape; Hanke thesis
§3, p. 8). For $\mathfrak p\nmid2$ with $[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\ne1$ and $\Lambda=\mathcal O_F^n$ maximal, $Q_\mathfrak p$ is
$\mathrm{GL}_n(\mathfrak o_\mathfrak p)$-equivalent to $\langle u_0,\dots,u_{a-1}\rangle\perp\pi W$ (`unitSum T a u`, $T=\pi W$), $a+b=n$, $u_i$ units, $W$
unimodular in $b\in\{1,2\}$ variables with $\overline W$ anisotropic (for $b=2$: `chiDisc W = -1`). Field: `shape`. -/
@[kb "omeara1963" "91:2, §92 (Jordan shape U ⊥ πW of a maximal lattice at an odd place); Hanke thesis §3, p. 8"]
structure OddMaximalJordan (F : Type) [Field F] [NumberField F] : Prop where
  /-- The shape of the local form. -/
  shape : ∀ {n : ℕ}, 3 ≤ n → ∀ Q₀ : QuadForm (𝓞 F) n, Q₀.Nondegenerate → StdIsMaximal Q₀ → ShimuraDetHyp Q₀ →
    ∀ v : HeightOneSpectrum (𝓞 F), IsUnit (2 : v.adicCompletionIntegers F) → dualIndexAt v Q₀ ≠ 1 →
      ∃ (a b : ℕ) (h : b + a = n) (u : Fin a → v.adicCompletionIntegers F)
        (W T : QuadForm (v.adicCompletionIntegers F) b),
        (∀ i, IsUnit (u i)) ∧ IsUnit W.hessian.det ∧ (∀ i j, T.coeff i j = NF.π v * W.coeff i j) ∧
        (b = 1 ∨ b = 2) ∧ (b = 2 → chiDisc W = -1) ∧
        (∃ w : Fin b → v.adicCompletionIntegers F,
          W = QuadForm.diag w ∧ T = QuadForm.diag fun j => NF.π v * w j) ∧
        IsGLEquiv (NF.Qp v Q₀) (h ▸ unitSum T a u)

/-- **(b) The Witt type of $\langle u\rangle\perp\pi W$ over $F_\mathfrak p$ for $b=2$** (a **named input**; a Springer-type theorem, O'Meara §63, §92:
the anisotropic kernel of $\langle u\rangle\perp\pi W$ is the sum of the anisotropic kernels of the residue forms of the two Jordan
components). For $\mathfrak p\nmid2$ and $Q_\mathfrak p\cong\langle u\rangle\perp\pi W$ as above with $b=2$ ($\overline W$ an anisotropic plane): for $a$ even,
$t_\mathfrak p=2$ or $4$ according as the character $\chi_U$ of $\langle u\rangle$ is $+1$ or $-1$; for $a$ odd, $t_\mathfrak p=3$.
(The ramification data and the case $b=1$ are proved: `not_ramified_of_two`, `not_isSquare_and_ramified_of_odd`.) Field: `witt`. -/
@[kb "omeara1963" "§63, §92 (anisotropic kernel of an orthogonal sum of Jordan components); Hanke thesis §3, p. 8"]
structure OddWittType (F : Type) [Field F] [NumberField F] : Prop where
  /-- The anisotropic dimension of the shape with $b=2$. -/
  witt : ∀ {n : ℕ} (Q₀ : QuadForm (𝓞 F) n), Q₀.Nondegenerate → ∀ v : HeightOneSpectrum (𝓞 F),
    IsUnit (2 : v.adicCompletionIntegers F) →
    ∀ (a : ℕ) (h : 2 + a = n) (u : Fin a → v.adicCompletionIntegers F)
      (W T : QuadForm (v.adicCompletionIntegers F) 2),
      (∀ i, IsUnit (u i)) → IsUnit W.hessian.det → (∀ i j, T.coeff i j = NF.π v * W.coeff i j) →
      chiDisc W = -1 →
      (∃ w : Fin 2 → v.adicCompletionIntegers F,
        W = QuadForm.diag w ∧ T = QuadForm.diag fun j => NF.π v * w j) →
      IsGLEquiv (NF.Qp v Q₀) (h ▸ unitSum T a u) →
        (Even a → (chiDisc (QuadForm.diag u) = 1 → anisoDim v Q₀ = 2) ∧
          (chiDisc (QuadForm.diag u) = -1 → anisoDim v Q₀ = 4)) ∧
        (Odd a → anisoDim v Q₀ = 3)

section DetShape

variable (v : HeightOneSpectrum (𝓞 F))

/-- **The Hessian determinant of the Jordan shape is $\pi^b$ times a unit:** if $Q\simeq\langle u\rangle\perp\pi W$ ($u_i$ and
$\det H(W)$ units, $2$ a unit) over $\mathfrak o_\mathfrak p$, then $\det H(Q)=\pi^bw$ with $w$ a unit. -/
@[kb "hanke2005crelle" "(3.4), p. 8 (det of the Jordan shape)"]
theorem det_shape {a b : ℕ} (h2 : IsUnit (2 : v.adicCompletionIntegers F)) (u : Fin a → v.adicCompletionIntegers F)
    (hu : ∀ i, IsUnit (u i)) (W T : QuadForm (v.adicCompletionIntegers F) b) (hW : IsUnit W.hessian.det)
    (hT : ∀ i j, T.coeff i j = NF.π v * W.coeff i j) (Q : QuadForm (v.adicCompletionIntegers F) (b + a))
    (hQ : IsGLEquiv Q (unitSum T a u)) :
    ∃ w : v.adicCompletionIntegers F, IsUnit w ∧ Q.hessian.det = NF.π v ^ b * w := by
  obtain ⟨U, hU, hUe⟩ := hQ
  have hH := DVR.hessian_eq_of_eval hUe
  have hD : (unitSum T a u).hessian.det = U.det * Q.hessian.det * U.det := by
    rw [hH, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hTH : T.hessian = NF.π v • W.hessian := by ext i j; simp [hessian, hT]; ring
  have hwu : IsUnit (2 ^ a * (∏ i, u i) * W.hessian.det) :=
    ((h2.pow a).mul (Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun i _ => hu i))).mul hW
  obtain ⟨c, hc⟩ := (hU.mul hU).exists_left_inv
  have hcu : IsUnit c := ⟨⟨c, U.det * U.det, hc, by rw [mul_comm]; exact hc⟩, rfl⟩
  refine ⟨(2 ^ a * (∏ i, u i) * W.hessian.det) * c, hwu.mul hcu, ?_⟩
  have e : (unitSum T a u).hessian.det = NF.π v ^ b * (2 ^ a * (∏ i, u i) * W.hessian.det) := by
    rw [det_hessian_unitSum, hTH, Matrix.det_smul, Fintype.card_fin]; ring
  calc Q.hessian.det = Q.hessian.det * (U.det * U.det) * c := by
        rw [mul_assoc, mul_comm (U.det * U.det) c, hc, mul_one]
    _ = (unitSum T a u).hessian.det * c := by rw [hD]; ring
    _ = _ := by rw [e]; ring

end DetShape

section RamData

variable (v : HeightOneSpectrum (𝓞 F))

/-- A norm in $F_\mathfrak p$ squared is never an odd power of $q$. -/
theorem norm_sq_ne_zpow_odd {e : ℤ} (he : Odd e) {r : v.adicCompletion F} (hr : r ≠ 0) :
    ‖r‖ ^ 2 ≠ (normQ v) ^ e := by
  intro h
  have hq0 : 0 < normQ v := lt_trans zero_lt_one (one_lt_normQ v)
  have hA : normQ v = (Ideal.absNorm v.asIdeal : ℝ) := by
    rw [← DensitySD.q_eq v, NF.q_completion]
  have hcz := QuadFormsKB.LocalZeta.norm_eq_absNorm_pow v hr
  rw [hcz, ← hA, ← zpow_natCast, ← _root_.zpow_mul] at h
  have := zpow_right_injective₀ hq0 (one_lt_normQ v).ne' h
  obtain ⟨k, hk⟩ := he
  omega

theorem algebraMap_discK_eq {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) :
    algebraMap F (v.adicCompletion F) (discK Q₀) =
      (-1) ^ (n / 2) * (((NF.Qp v Q₀).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ n := by
  have key : algebraMap F (v.adicCompletion F) ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) =
      (((NF.Qp v Q₀).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F) := by
    rw [hessian_det_cast v Q₀]
    have : (Q₀.map (algebraMap (𝓞 F) F)).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
      ext i j; simp [QuadForm.hessian, QuadForm.map]
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  simp only [discK, map_mul, map_div₀, map_pow, map_neg, map_one, map_ofNat, key]
  ring

/-- **Odd determinant valuation: $t_\mathfrak p=2$-type data.** If $\det H(Q_\mathfrak p)=\pi^bw$ with $b$ odd, $w$ a unit and $\mathfrak p\nmid2$,
then $\delta$ is not a square in $F_\mathfrak p$ and $\mathfrak p$ is ramified in $K=F(\sqrt\delta)$. -/
@[kb "hanke2005crelle" "§3, p. 8 (odd valuation of det: δ non-square and ramified)"]
theorem not_isSquare_and_ramified_of_odd {n b : ℕ} (Q₀ : QuadForm (𝓞 F) n) (h2 : IsUnit (2 : v.adicCompletionIntegers F))
    (hb : Odd b) {w : v.adicCompletionIntegers F} (hw : IsUnit w)
    (hD : (NF.Qp v Q₀).hessian.det = NF.π v ^ b * w) :
    ¬ IsSquare (algebraMap F (v.adicCompletion F) (discK Q₀)) ∧ IsRamifiedAt v Q₀ := by
  have hπ := NF.irreducible_π v
  have hq := DensitySD.q_eq v
  have hq0 : 0 < normQ v := lt_trans zero_lt_one (one_lt_normQ v)
  have h2n : ‖(2 : v.adicCompletion F)‖ = 1 := by
    have := norm_coe_unit v h2
    have e : (((2 : v.adicCompletionIntegers F)) : v.adicCompletion F) = 2 :=
      map_ofNat (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) 2
    rwa [e] at this
  have hnorm : ‖(((NF.Qp v Q₀).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖ =
      ((normQ v) ^ b)⁻¹ := by
    rw [← hq]
    exact norm_coe_of_pow_dvd v ⟨_, hD⟩ (by
      rw [hD, pow_succ]
      intro hd
      exact hπ.not_isUnit (isUnit_of_dvd_unit ((mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).1 hd) hw))
  have hx : ‖algebraMap F (v.adicCompletion F) (discK Q₀)‖ = ((normQ v) ^ b)⁻¹ := by
    rw [algebraMap_discK_eq, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow, h2n,
      one_pow, div_one, hnorm]
  have hqb : ((normQ v) ^ b)⁻¹ = (normQ v) ^ (-(b : ℤ)) := by rw [_root_.zpow_neg, zpow_natCast]
  have hbz : (normQ v) ^ (b : ℤ) = (normQ v) ^ b := zpow_natCast _ _
  have hbo : Odd (b : ℤ) := by exact_mod_cast hb
  have hx0 : algebraMap F (v.adicCompletion F) (discK Q₀) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hx
    exact (inv_ne_zero (pow_ne_zero _ hq0.ne')) hx.symm
  refine ⟨?_, ?_⟩
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by rintro rfl; exact hx0 (by simpa using hr)
    have : ‖r‖ ^ 2 = (normQ v) ^ (-(b : ℤ)) := by
      rw [← hqb, ← hx, hr, norm_mul, sq]
    exact norm_sq_ne_zpow_odd v (by simpa using hbo.neg) hr0 this
  · rintro ⟨c, hc0, y, hy, hxc⟩
    have h1 : ‖(1 + 4 * (y : v.adicCompletion F))‖ = 1 := by
      have e : (1 + 4 * (y : v.adicCompletion F)) = ((1 + 4 * y : v.adicCompletionIntegers F) : v.adicCompletion F) := by
        push_cast; rfl
      rw [e]; exact norm_coe_unit v hy
    rw [← hxc, norm_mul, norm_pow, hx] at h1
    have : ‖c‖ ^ 2 = (normQ v) ^ (b : ℤ) := by
      rw [hbz]
      have hb0 : (normQ v ^ b) ≠ 0 := pow_ne_zero _ hq0.ne'
      field_simp at h1
      linarith
    exact norm_sq_ne_zpow_odd v hbo hc0 this

/-- **Determinant valuation $2$: unramified.** If $\det H(Q_\mathfrak p)=\pi^2w$ with $w$ a unit and $\mathfrak p\nmid2$, then $\mathfrak p$ is
unramified in $K=F(\sqrt\delta)$ ($\delta\,c^2$ is a unit with $c=2^n/\pi$). -/
@[kb "hanke2005crelle" "§3, p. 8 (even valuation of det: unramified)"]
theorem not_ramified_of_two {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (h2 : IsUnit (2 : v.adicCompletionIntegers F))
    {w : v.adicCompletionIntegers F} (hw : IsUnit w) (hD : (NF.Qp v Q₀).hessian.det = NF.π v ^ 2 * w) :
    ¬ IsRamifiedAt v Q₀ := by
  have hπ := NF.irreducible_π v
  unfold IsRamifiedAt
  rw [not_not, algebraMap_discK_eq, hD]
  unfold IsUnramSqrt
  obtain ⟨w2, hw2⟩ : ∃ w2 : v.adicCompletionIntegers F, 2 * w2 = 1 := ⟨((h2.unit⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F), by simp⟩
  have hz : IsUnit ((-1 : v.adicCompletionIntegers F) ^ (n / 2) * w * 2 ^ n) :=
    ((isUnit_one.neg.pow _).mul hw).mul (h2.pow n)
  have hπ0 : ((NF.π v : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    intro h0
    exact hπ.ne_zero (Subtype.ext h0)
  have h2F : (2 : v.adicCompletion F) ≠ 0 := two_ne_zero
  have hid : 1 + 4 * (((-1 : v.adicCompletionIntegers F) ^ (n / 2) * w * 2 ^ n - 1) * w2 ^ 2) =
      (-1 : v.adicCompletionIntegers F) ^ (n / 2) * w * 2 ^ n := by
    linear_combination (((-1 : v.adicCompletionIntegers F) ^ (n / 2) * w * 2 ^ n - 1) * (2 * w2 + 1)) * hw2
  refine ⟨2 ^ n / ((NF.π v : v.adicCompletionIntegers F) : v.adicCompletion F),
    div_ne_zero (pow_ne_zero _ h2F) hπ0,
    ((-1 : v.adicCompletionIntegers F) ^ (n / 2) * w * 2 ^ n - 1) * w2 ^ 2, by rw [hid]; exact hz, ?_⟩
  have hcast := congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) hid
  push_cast at hcast ⊢
  have h2c : ((2 : v.adicCompletionIntegers F) : v.adicCompletion F) = 2 :=
    map_ofNat (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) 2
  have h4c : ((4 : v.adicCompletionIntegers F) : v.adicCompletion F) = 4 :=
    map_ofNat (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) 4
  rw [h2c, h4c] at hcast
  rw [h2c]
  rw [hcast]
  field_simp

end RamData

/-- **The two parts give the combined shape-and-type input.** -/
@[kb "omeara1963" "91:2, §63, §92 (Jordan shape and Witt type; combination)"]
theorem oddMaximalShape_of_split (I₁ : OddMaximalJordan F) (I₂ : OddWittType F) : OddMaximalShape F := by
  refine ⟨fun {n} hn Q₀ hQ hmax hdet v h2 h1 => ?_⟩
  obtain ⟨a, b, h, u, W, T, hu, hW, hT, hb, hχ, hd, he⟩ := I₁.shape hn Q₀ hQ hmax hdet v h2 h1
  subst h
  obtain ⟨w, hw, hD⟩ := det_shape v h2 u hu W T hW hT (NF.Qp v Q₀) he
  refine ⟨a, b, rfl, u, W, T, hu, hW, hT, hb, hχ, he, fun hb1 hev => ?_, fun hb2 => ?_⟩
  · subst hb1
    obtain ⟨hns, hram⟩ := not_isSquare_and_ramified_of_odd v Q₀ h2 odd_one hw (by simpa using hD)
    exact ⟨(anisoDim_eq_two_iff v Q₀ hQ hev).2 hns, hram⟩
  · subst hb2
    refine ⟨not_ramified_of_two v Q₀ h2 hw hD, ?_⟩
    exact I₂.witt Q₀ hQ v h2 a rfl u W T hu hW hT (hχ rfl) hd he

open DensitySD in
/-- **Siegel's density at a non-dyadic place with $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$** from the Jordan shape:
$\alpha_\mathfrak p=[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\,\xi$. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (non-dyadic places with Λ̃_p ≠ Λ_p; from the Jordan shape)"]
theorem siegelDensity_oddRamified (I : OddMaximalShape F) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀)
    (h2 : IsUnit (2 : v.adicCompletionIntegers F)) (h1 : dualIndexAt v Q₀ ≠ 1) :
    NF.siegelDensity v Q₀ Q₀ = dualIndexAt v Q₀ * xiAt v Q₀ := by
  obtain ⟨a, b, h, u, W, T, hu, hW, hT, hb, hχW, hequiv, hb1, hb2⟩ := I.shape hn Q₀ hQ hmax hdet v h2 h1
  subst h
  have hπ := NF.irreducible_π v
  have hπ2 := not_dvd_two v h2
  have hq := q_eq v
  have hq0 : 0 < normQ v := lt_trans zero_lt_one (one_lt_normQ v)
  obtain ⟨U, hU, hUe⟩ := hequiv
  have hiso : Siegel.IsometricGL (NF.Qp v Q₀) (unitSum T a u) :=
    ⟨Matrix.nonsingInvUnit U hU, fun x => (hUe x).symm⟩
  have hβ : DVR.localDensityForm (NF.Qp v Q₀) (NF.Qp v Q₀) (NF.π v) =
      DVR.localDensityForm (unitSum T a u) (unitSum T a u) (NF.π v) :=
    (DVR.localDensityForm_congr_left hiso (NF.Qp v Q₀) (NF.π v)).trans
      (DVR.localDensityForm_congr_right (unitSum T a u) hiso (NF.π v))
  -- the dual index is q^b
  obtain ⟨w, hwc, hD2⟩ := det_shape v h2 u hu W T hW hT (NF.Qp v Q₀) ⟨U, hU, hUe⟩
  set D := (NF.Qp v Q₀).hessian.det with hDdef
  have hnorm : ‖((D : v.adicCompletionIntegers F) : v.adicCompletion F)‖ = ((DVR.q (v.adicCompletionIntegers F) : ℝ) ^ b)⁻¹ :=
    norm_coe_of_pow_dvd v ⟨_, hD2⟩ (by
      rw [hD2, pow_succ]
      intro hd
      exact hπ.not_isUnit (isUnit_of_dvd_unit ((mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).1 hd) hwc))
  have hdual : dualIndexAt v Q₀ = (normQ v) ^ b := by
    unfold dualIndexAt
    rw [← hDdef, hnorm, inv_inv, hq]
  have hdiagU : ¬ NF.π v ∣ (QuadForm.diag u).hessian.det := by
    rw [det_hessian_diag]
    exact DVR.dvr_not_dvd_of_isUnit hπ
      ((h2.pow a).mul (Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun i _ => hu i)))
  have hWnd : ¬ NF.π v ∣ W.hessian.det := DVR.dvr_not_dvd_of_isUnit hπ hW
  rw [hdual, NF.siegelDensity, if_pos rfl, NF.localDensityForm_eq_completion, hβ,
    density_oddShape hπ hπ2 u hu W T hW hT, hq]
  unfold xiAt
  rw [eq_false h1]
  rcases hb with rfl | rfl
  · have hev : Even (1 + a) := by
      by_contra hne
      rw [Nat.not_even_iff_odd] at hne
      have := even_of_shimuraDetHyp v Q₀ hdet h2 (b := 1) (by rw [hdual, pow_one]) hne
      exact Nat.not_even_one this
    obtain ⟨ht, hram⟩ := hb1 rfl hev
    obtain ⟨m, hm⟩ := hev
    obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 1 := ⟨m - 1, by omega⟩
    have hd := localDensityForm_self_odd (NF.π v) k (QuadForm.diag u) hπ hπ2 hdiagU
    have hw1 := localDensityForm_self_odd (NF.π v) 0 W hπ hπ2 hWnd
    rw [hd, hw1]
    simp only [hq]
    rw [ht]
    simp only [xiShimura]
    rw [if_pos hram]
    have hm' : (1 + (2 * k + 1)) / 2 - 1 = k := by omega
    rw [hm', ppow_eq hq0]
    norm_num
    ring
  · obtain ⟨hram, hEven, hOdd⟩ := hb2 rfl
    have hχ := hχW rfl
    have hw2 := localDensityForm_self_even (NF.π v) 1 le_rfl W hπ hπ2 hWnd
    rw [hχ] at hw2
    rw [hw2]
    simp only [hq]
    rcases Nat.even_or_odd' a with ⟨k, rfl | rfl⟩
    · obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
      have hd := localDensityForm_self_even (NF.π v) (l + 1) (by omega) (QuadForm.diag u) hπ hπ2 hdiagU
      rw [hd]
      simp only [hq]
      have hm' : (2 + 2 * (l + 1)) / 2 = l + 2 := by omega
      have hy : normQ v ^ (l + 2) = normQ v ^ (l + 1) * normQ v := by ring
      have hy2 : normQ v ^ (2 * (l + 1)) = (normQ v ^ (l + 1)) ^ 2 := by ring
      have hP : ppow (normQ v) (l + 1) = (∏ i ∈ Finset.range l, (1 - ((normQ v) ^ (2 * (i + 1)))⁻¹)) *
          (1 - ((normQ v ^ (l + 1)) ^ 2)⁻¹) := by
        rw [ppow_eq hq0, Finset.prod_range_succ, hy2]
      have hr : normQ v ^ (1 - ((l + 2 : ℕ) : ℝ)) = (normQ v ^ (l + 1))⁻¹ := by
        rw [Real.rpow_sub hq0, Real.rpow_one, Real.rpow_natCast, hy]
        field_simp
      have hyp : 0 < normQ v ^ (l + 1) := pow_pos hq0 _
      rcases chiDisc_pm hπ hπ2 (QuadForm.diag u) hdiagU with he | he
      · rw [(hEven (even_two_mul _)).1 he]
        simp only [xiShimura, hm', hram, if_false, ite_false]
        rw [show l + 2 - 1 = l + 1 from rfl, hP, hr, he]
        simp only [Nat.add_sub_cancel, Finset.range_zero, Finset.prod_empty, mul_one]
        norm_num
        generalize (∏ i ∈ Finset.range l, (1 - ((normQ v) ^ (2 * (i + 1)))⁻¹)) = P
        generalize normQ v ^ (l + 1) = y at *
        generalize normQ v = x at *
        field_simp
        ring
      · rw [(hEven (even_two_mul _)).2 he]
        simp only [xiShimura, hm']
        have hlt := inv_lt_one_of_one_lt₀ (one_lt_pow₀ (one_lt_normQ v) (by omega : l + 1 ≠ 0))
        have hne : 1 - (normQ v ^ (l + 1))⁻¹ ≠ 0 := sub_ne_zero.2 (ne_of_gt hlt)
        have hy1 : 1 < normQ v ^ (l + 1) := one_lt_pow₀ (one_lt_normQ v) (by omega : l + 1 ≠ 0)
        have hne2 : normQ v ^ (l + 1) - 1 ≠ 0 := sub_ne_zero.2 hy1.ne'
        have hne3 : -1 + normQ v ^ (l + 1) ≠ 0 := by intro h; apply hne2; linarith
        have hne' : 1 - normQ v ^ (1 - ((l + 2 : ℕ) : ℝ)) ≠ 0 := by rw [hr]; exact hne
        rw [show l + 2 - 1 = l + 1 from rfl, hP, he]
        rw [hr] at hne' ⊢
        simp only [Nat.add_sub_cancel, Finset.range_zero, Finset.prod_empty, mul_one]
        norm_num
        generalize (∏ i ∈ Finset.range l, (1 - ((normQ v) ^ (2 * (i + 1)))⁻¹)) = P
        generalize normQ v ^ (l + 1) = y at *
        generalize normQ v = x at *
        field_simp
        ring
    · have hd := localDensityForm_self_odd (NF.π v) k (QuadForm.diag u) hπ hπ2 hdiagU
      rw [hd]
      simp only [hq]
      have ht := hOdd (odd_two_mul_add_one k)
      have hm' : (2 + (2 * k + 1)) / 2 = k + 1 := by omega
      rw [ht]
      simp only [xiShimura, hm', Nat.add_sub_cancel, ppow_eq hq0]
      norm_num
      generalize (∏ i ∈ Finset.range k, (1 - ((normQ v) ^ (2 * (i + 1)))⁻¹)) = P
      generalize normQ v = x at *
      field_simp
      ring

/-- **(3.3) at a non-dyadic place with $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$, from the Jordan shape** (Hanke thesis,
(3.3), p. 8): `ShimuraDensityOddRamified F` follows from `OddMaximalShape F`. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (non-dyadic places with Λ̃_p ≠ Λ_p; from the Jordan shape)"]
theorem shimuraDensityOddRamified_of_shape (I : OddMaximalShape F) : ShimuraDensityOddRamified F := by
  refine ⟨fun {n} hn Q₀ hQ hmax hdet v h2 h1 => ?_⟩
  rw [hankeBeta_gramV v Q₀ hQ, siegelDensity_oddRamified I v hn Q₀ hQ hmax hdet h2 h1]
  unfold shimuraBetaRHS
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, norm_pow]
  have ha : 0 < ‖(2 : v.adicCompletion F)‖ := norm_pos_iff.mpr two_ne_zero
  generalize ‖(2 : v.adicCompletion F)‖ = a at *
  have hN : ((n * (n - 1) / 2 : ℕ) : ℝ) = (n : ℝ) * (n - 1) / 2 := by
    have hev : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
    rw [Nat.cast_div hev (by norm_num)]
    rcases n with _ | n
    · simp
    · push_cast; simp
  have e : (a ^ n) ^ (((n : ℝ) + 1) / 2) * (a ^ n)⁻¹ = a ^ (n * (n - 1) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast a (n * (n - 1) / 2), hN, ← Real.rpow_mul ha.le,
      ← Real.rpow_neg (by positivity), ← Real.rpow_add ha]
    congr 1; ring
  rw [e]; ring

end QuadFormsKB.Hanke2005
