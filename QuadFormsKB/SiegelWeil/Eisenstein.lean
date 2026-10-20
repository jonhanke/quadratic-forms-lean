/-
# The degree-one Siegel Eisenstein series attached to the Weil representation

**Layer:** global over a number field $F$, built from the local sections of `SiegelWeil/Sections.lean`.

**Conventions.** $B = \{\begin{pmatrix}a&b\\0&a^{-1}\end{pmatrix}\}$ the upper Borel subgroup (`borel`); $B(F)\backslash\mathrm{SL}_2(F)$ is the
quotient by the relation $\gamma \sim \gamma'$ iff $\gamma'\gamma^{-1} \in B(F)$ (`BQuot`, Mathlib's `rightRel`). $Q = \sum_{i<n}a_ix_i^2$,
$a_i \in F^\times$, $n = 2m$ (0-based); at a finite place $v$ the lattice section $f_v(g, s) = (\omega_v(g)\mathbf 1_{L_v})(0)\|g\|_v^{-(s-s_0)}$
(`secS`), $s_0 = m - 1$; $\gamma_v$ is the image of $\gamma$ in $\mathrm{SL}_2(F_v)$.

**Results (proved).**
* `bruhatEquiv` (**the Bruhat decomposition**): $\{\ast\}\sqcup F \simeq B(F)\backslash\mathrm{SL}_2(F)$, $\ast \mapsto B$,
  $\beta \mapsto B\,wn(\beta)$; the inverse reads off the bottom row $(c : d)$ ($\ast$ if $c = 0$, $d/c$ otherwise).
* `hasFiniteMulSupport_secS`: for $\gamma \in \mathrm{SL}_2(F)$ and $a_i \in \mathcal O_F$ (as `unitsOfInt`), $f_v(\gamma_v, s) = 1$ for all
  but finitely many $v$ (good places where $\gamma$ is integral: `weilRepV_oneS_of_good`, $\|\gamma_v\|_v = 1$); so the finite
  part $f_f(\gamma, s) = \prod_vf_v(\gamma_v, s)$ (`finSec`) is a finite product.
* `finSec_borel`: $f_f(n(\beta)m(t)\gamma, s) = \big(\prod_v\chi_{V,v}(t)|t|_v^{s+1}\big)f_f(\gamma, s)$.
* **`globalSec_borel`** (**left $B(F)$-invariance of the global section**): for an archimedean section $f_\infty$ with
  $f_\infty(n(\beta)m(t)\gamma) = \chi_{V,\infty}(t)|t|_\infty^{s+1}f_\infty(\gamma)$, the product $f(\gamma) = f_\infty(\gamma)f_f(\gamma, s)$ satisfies
  $f(b\gamma) = f(\gamma)$ for $b \in B(F)$: Hilbert reciprocity $\prod_u\chi_{V,u}(t) = 1$ (`chiV_prod_eq_one`) and the product
  formula $\prod_u|t|_u = 1$ (`prod_modulus_eq_one`). Hence
* **`eisenstein`**: $E(s) = \sum_{\gamma \in B(F)\backslash\mathrm{SL}_2(F)}f(\gamma)$ is well defined, and
  `eisenstein_eq_bruhat`: $E(s) = f(1) + \sum_{\beta\in F}f(wn(\beta))$ when the second sum converges ($f(1) = f_\infty(1)$, `finSec_one`).
* **`whittakerEuler_eq_siegel`** (**the Siegel product**, $F$ totally real, $Q$ totally positive, $n \ge 4$, $t$ totally
  positive in $\mathcal O_F$): with $W_\infty(t, z) = \gamma_{V,\infty}c_{B,\infty}\prod_wy_w^{m/2}\int_{\mathbb R}\mathcal G_w(z_w + b)e(-t_wb)\,db$
  and $\prod_vW_v(t) = C_fP$ (`hasProd_whittakerV`, $P = \prod_v\beta_v(t)$),
  $$W_\infty(t, z)\cdot C_f\,P = |d_F|^{-(n-1)/2}\prod_{w\mid\infty}y_w^{m/2}\beta_w(t)e(t_wz_w)\cdot\prod_{v<\infty}\beta_v(t).$$
  This is the right-hand side of the classical identity $a_E(t) = |d_F|^{-(n-1)/2}\beta_\infty(t)\prod_\mathfrak p\beta_\mathfrak p(t)$.

**Cited, not formalized:** absolute convergence of $E(g, s)$ for
$\operatorname{Re}s > 1$ (Godement; Weil 1965), and the **unfolding** $E_t(g, s) = \int_{\mathbb A}f(wn(b)g, s)\psi(-tb)\,db =
\prod_{v\le\infty}W_v(t, g_v, s)$ for $t \in F^\times$ (Bruhat, `eisenstein_eq_bruhat`, then $F\backslash\mathbb A$-unfolding and
factorization of the adelic integral; Weil 1965; Kudla 2008, §1). The repo has no integration over $F\backslash\mathbb A_F$; no
hypothesis structure is introduced for these, and no theorem here depends on them.

Sources: Weil, Acta Math. 113 (1965) [unverified]; Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1
[unverified]; Bump (1997), §3.7 (Eisenstein series on $\mathrm{GL}_2$ and the Bruhat decomposition) [unverified];
Garrett (1990) [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.SiegelWeil.GlobalWhittaker
import QuadFormsKB.SiegelWeil.ArchWhittaker
import QuadFormsKB.Weil.ArchTheta

open IsDedekindDomain NumberField MeasureTheory Filter
open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData
open scoped MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil

/-! ### The Borel subgroup and the Bruhat decomposition -/

section Bruhat

variable (k : Type*) [Field k]

/-- **The Borel subgroup** $B(k) = \{g \in \mathrm{SL}_2(k) : g_{10} = 0\}$ (upper triangular; 0-based entries). -/
def borel : Subgroup SL(2, k) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hg, hh]
  one_mem' := by simp
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp [hg]

/-- $B(k)\backslash\mathrm{SL}_2(k)$: classes $B\gamma$ ($\gamma \sim \gamma'$ iff $\gamma'\gamma^{-1} \in B$). -/
abbrev BQuot : Type _ := Quotient (QuotientGroup.rightRel (borel k))

variable {k}

open scoped Classical in
/-- The invariant of $B\gamma$: $\ast$ if $c = 0$, $d/c$ if $c \ne 0$ ($(c, d)$ the bottom row). -/
def bruhatInv (g : SL(2, k)) : Unit ⊕ k :=
  if (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 then Sum.inl () else
    Sum.inr ((g : Matrix (Fin 2) (Fin 2) k) 1 1 / (g : Matrix (Fin 2) (Fin 2) k) 1 0)

/-- The representatives $1$ and $wn(\beta)$. -/
def bruhatRep : Unit ⊕ k → SL(2, k)
  | Sum.inl _ => 1
  | Sum.inr β => wMat * nMat β

lemma bruhatInv_mul_left {b : SL(2, k)} (hb : b ∈ borel k) (g : SL(2, k)) :
    bruhatInv (b * g) = bruhatInv g := by
  have hb' : (b : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := hb
  have hd : (b : Matrix (Fin 2) (Fin 2) k) 1 1 ≠ 0 := d_ne_zero_of_c_eq_zero hb'
  have e10 : ((b * g : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 =
      (b : Matrix (Fin 2) (Fin 2) k) 1 1 * (g : Matrix (Fin 2) (Fin 2) k) 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hb']
  have e11 : ((b * g : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 1 =
      (b : Matrix (Fin 2) (Fin 2) k) 1 1 * (g : Matrix (Fin 2) (Fin 2) k) 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hb']
  unfold bruhatInv
  rw [e10, e11]
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · simp [hc]
  · rw [if_neg (mul_ne_zero hd hc), if_neg hc, mul_div_mul_left _ _ hd]

lemma bruhatInv_rep (x : Unit ⊕ k) : bruhatInv (bruhatRep x) = x := by
  rcases x with ⟨⟩ | β
  · simp [bruhatInv, bruhatRep]
  · simp [bruhatInv, bruhatRep, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

lemma exists_borel_mul_rep (g : SL(2, k)) : ∃ b ∈ borel k, g = b * bruhatRep (bruhatInv g) := by
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · refine ⟨g, hc, ?_⟩
    simp [bruhatInv, hc, bruhatRep]
  · refine ⟨nMat ((g : Matrix (Fin 2) (Fin 2) k) 0 0 / g 1 0) * mMat (Units.mk0 _ (unit_ne_zero_aux hc)), ?_, ?_⟩
    · show ((nMat _ * mMat _ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    · simp only [bruhatInv, if_neg hc, bruhatRep]
      rw [← mul_assoc]
      exact eq_cell_of_c_ne_zero g hc

/-- **The Bruhat decomposition** $\mathrm{SL}_2(k) = B \sqcup BwN$: $\{\ast\}\sqcup k \simeq B(k)\backslash\mathrm{SL}_2(k)$,
$\ast \mapsto B$, $\beta \mapsto B\,w\,n(\beta)$. -/
@[kb "bump1997" "§3.7 (the Bruhat decomposition of $\\mathrm{GL}_2$) [unverified]"]
def bruhatEquiv : Unit ⊕ k ≃ BQuot k where
  toFun x := Quotient.mk _ (bruhatRep x)
  invFun := Quotient.lift bruhatInv fun g g' h => by
    have h' : QuotientGroup.rightRel (borel k) g g' := h
    rw [QuotientGroup.rightRel_apply] at h'
    have := bruhatInv_mul_left h' g
    rw [inv_mul_cancel_right] at this
    exact this.symm
  left_inv x := bruhatInv_rep x
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨b, hb, hg⟩ := exists_borel_mul_rep g
      apply Quotient.sound
      show QuotientGroup.rightRel (borel k) (bruhatRep (bruhatInv g)) g
      rw [QuotientGroup.rightRel_apply]
      have e : g * (bruhatRep (bruhatInv g))⁻¹ = b := by
        rw [mul_inv_eq_iff_eq_mul]; exact hg
      rw [e]; exact hb

end Bruhat

/-! ### The finite part of the global section -/

section Global

variable {F : Type} [Field F] [NumberField F] {m : ℕ} (a : Fin (2 * m) → Fˣ)

/-- The image $\gamma_v$ of $\gamma \in \mathrm{SL}_2(F)$ in $\mathrm{SL}_2(F_v)$. -/
abbrev locSL (v : HeightOneSpectrum (𝓞 F)) : SL(2, F) →* SL(2, v.adicCompletion F) :=
  Matrix.SpecialLinearGroup.map (algebraMap F (v.adicCompletion F))

lemma locSL_apply (v : HeightOneSpectrum (𝓞 F)) (γ : SL(2, F)) (i j : Fin 2) :
    ((locSL v γ : SL(2, v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j =
      algebraMap F _ ((γ : Matrix (Fin 2) (Fin 2) F) i j) := rfl

lemma locSL_nMat (v : HeightOneSpectrum (𝓞 F)) (β : F) : locSL v (nMat β) = nMat (algebraMap F _ β) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [locSL_apply]

lemma locSL_mMat (v : HeightOneSpectrum (𝓞 F)) (t : Fˣ) :
    locSL v (mMat t) = mMat (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom t) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [locSL_apply]

/-- **The finite part of the global lattice section** at $\gamma \in \mathrm{SL}_2(F)$:
$f_f(\gamma, s) = \prod_{v<\infty}f_v(\gamma_v, s)$, $f_v$ = `secS` for $\varphi_v = \mathbf 1_{\mathcal O_v^{2m}}$ (a finite product,
`hasFiniteMulSupport_secS`). -/
@[kb "kudla2008" "§1 (the standard section $\\Phi(s) = \\otimes_v\\Phi_v(s)$) [unverified]"]
def finSec (γ : SL(2, F)) (s : ℂ) : ℂ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), secS v (aV a v) (oneS v m) (locSL v γ) s

/-- The finite places where $V$ or $\gamma$ is not good: $v \mid \mathfrak d_F$, $v \mid 2$, $v(a_i) \ne 0$, or an entry
of $\gamma$ is not $v$-integral. -/
def badPlaces (γ : SL(2, F)) : Set (HeightOneSpectrum (𝓞 F)) :=
  {v | (diffExp v : ℤ) ≠ 0} ∪ HeightOneSpectrum.Support (𝓞 F) (K := F) (2 : F)⁻¹ ∪
    (⋃ i, (HeightOneSpectrum.Support (𝓞 F) (K := F) (a i : F) ∪
      HeightOneSpectrum.Support (𝓞 F) (K := F) ((a i : F)⁻¹))) ∪
    ⋃ i, ⋃ j, HeightOneSpectrum.Support (𝓞 F) (K := F) ((γ : Matrix (Fin 2) (Fin 2) F) i j)

lemma badPlaces_finite (γ : SL(2, F)) : (badPlaces a γ).Finite := by
  have h1 := finite_support_diffExp (F := F)
  have h2 := HeightOneSpectrum.Support.finite (𝓞 F) ((2 : F)⁻¹)
  have h3 := Set.finite_iUnion fun i : Fin (2 * m) =>
    (HeightOneSpectrum.Support.finite (𝓞 F) (a i : F)).union (HeightOneSpectrum.Support.finite (𝓞 F) ((a i : F)⁻¹))
  have h4 := Set.finite_iUnion fun i : Fin 2 => Set.finite_iUnion fun j : Fin 2 =>
    HeightOneSpectrum.Support.finite (𝓞 F) ((γ : Matrix (Fin 2) (Fin 2) F) i j)
  exact ((h1.union h2).union h3).union h4

lemma valued_eq_one_of_not_mem {v : HeightOneSpectrum (𝓞 F)} {x : F} (hx : x ≠ 0)
    (h1 : v ∉ HeightOneSpectrum.Support (𝓞 F) x) (h2 : v ∉ HeightOneSpectrum.Support (𝓞 F) x⁻¹) :
    Valued.v (algebraMap F (v.adicCompletion F) x) = 1 := by
  have e1 := valued_le_one_of_not_mem_support h1
  have e2 := valued_le_one_of_not_mem_support h2
  rw [map_inv₀, map_inv₀] at e2
  have hne : Valued.v (algebraMap F (v.adicCompletion F) x) ≠ 0 := by simp [hx]
  exact le_antisymm e1 (by
    by_contra h; push Not at h
    have := one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hne, h⟩
    exact absurd e2 (not_le.mpr this))

lemma isGoodV_of_not_bad {γ : SL(2, F)} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badPlaces a γ) :
    IsGoodV v (aV a v) := by
  simp only [badPlaces, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists, not_not] at hv
  obtain ⟨⟨⟨hd, h2⟩, hai⟩, -⟩ := hv
  refine ⟨by exact_mod_cast hd, ?_, fun i => ?_⟩
  · have h2' : v ∉ HeightOneSpectrum.Support (𝓞 F) (K := F) (2 : F) := by
      show ¬ (1 < v.valuation F (2 : F))
      rw [not_lt]
      have := v.valuation_le_one (K := F) (2 : 𝓞 F)
      exact this
    have := valued_eq_one_of_not_mem (x := (2 : F)) two_ne_zero h2' h2
    rwa [map_ofNat] at this
  · exact valued_eq_one_of_not_mem (a i).ne_zero (hai i).1 (hai i).2

lemma locSL_int_of_not_bad {γ : SL(2, F)} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badPlaces a γ) (i j : Fin 2) :
    Valued.v (((locSL v γ : SL(2, v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ 1 := by
  simp only [badPlaces, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hv
  rw [locSL_apply]
  exact valued_le_one_of_not_mem_support (hv.2 i j)

lemma htV_eq_one_of_int {v : HeightOneSpectrum (𝓞 F)} (g : SL(2, v.adicCompletion F))
    (hg : ∀ i j, Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ 1) : htV v g = 1 := by
  have hn : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1 := fun i j =>
    (Valued.toNormedField.norm_le_one_iff).mpr (hg i j)
  refine le_antisymm (max_le (hn 1 0) (hn 1 1)) ?_
  have hdet := det_eq g
  have h1 : (1 : ℝ) ≤ max (‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0‖ *
      ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1‖)
      (‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1‖ *
        ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0‖) := by
    have := IsUltrametricDist.norm_add_le_max ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 * g 1 1)
      (-((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 * g 1 0))
    rw [← sub_eq_add_neg, hdet, norm_one, norm_neg, norm_mul, norm_mul] at this
    exact this
  refine h1.trans (max_le ?_ ?_)
  · exact (mul_le_of_le_one_left (norm_nonneg _) (hn 0 0)).trans (le_max_right _ _)
  · exact (mul_le_of_le_one_left (norm_nonneg _) (hn 0 1)).trans (le_max_left _ _)

/-- **At almost every place the local factor is $1$**: if $v \notin$ `badPlaces`, then $f_v(\gamma_v, s) = 1$
($\mathbf 1_{L_v}$ is $\mathrm{SL}_2(\mathcal O_v)$-fixed at a good place, `weilRepV_oneS_of_good`, and $\|\gamma_v\|_v = 1$). -/
theorem secS_eq_one_of_not_bad {γ : SL(2, F)} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badPlaces a γ) (s : ℂ) :
    secS v (aV a v) (oneS v m) (locSL v γ) s = 1 := by
  have hg := isGoodV_of_not_bad a hv
  have hint := locSL_int_of_not_bad a hv
  unfold secS secV sec
  rw [show weilRep (isModel_V v) (a := aV a v) (RingHom.id _) (locSL v γ) (oneS v m) =
    weilRepV v (aV a v) (locSL v γ) (oneS v m) from rfl, weilRepV_oneS_of_good v (aV a v) hg _ hint,
    htV_eq_one_of_int _ hint]
  simp [oneV, ptensor, ballIndV]

lemma hasFiniteMulSupport_secS (γ : SL(2, F)) (s : ℂ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => secS v (aV a v) (oneS v m) (locSL v γ) s :=
  (badPlaces_finite a γ).subset fun v hv => by
    by_contra h; exact hv (secS_eq_one_of_not_bad a h s)

/-- $f_f(1, s) = 1$. -/
@[simp] lemma finSec_one (s : ℂ) : finSec a 1 s = 1 := by
  simp [finSec, map_one]

/-! ### The Borel law of the finite section and the global $B(F)$-invariance -/

/-- The local Borel factor $\chi_{V,v}(t)\,|t|_v^{s+1}$. -/
def borelFactorV (t : Fˣ) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  (localDataV v).chiV (aV a v) (algebraMap F _ (t : F)) *
    ((‖algebraMap F (v.adicCompletion F) (t : F)‖ : ℝ) : ℂ) ^ (s + 1)

lemma norm_algebraMap_eq_modK (v : HeightOneSpectrum (𝓞 F)) (t : Fˣ) :
    ‖algebraMap F (v.adicCompletion F) (t : F)‖ =
      Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) (t : F)) :=
  (modK_eq_norm v ((map_ne_zero _).mpr t.ne_zero)).symm

lemma hasFiniteMulSupport_normPow (t : Fˣ) (s : ℂ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((‖algebraMap F (v.adicCompletion F) (t : F)‖ : ℝ) : ℂ) ^ (s + 1) :=
  (hasFiniteMulSupport_modK t.ne_zero).subset fun v hv h' => hv (by
    simp only at h' ⊢; rw [norm_algebraMap_eq_modK, h']; simp)

lemma hasFiniteMulSupport_borelFactorV (t : Fˣ) (s : ℂ) :
    Function.HasFiniteMulSupport (borelFactorV a t s) :=
  (hasFiniteMulSupport_chiV a t).mul (hasFiniteMulSupport_normPow t s)

/-- **The Borel law of the finite section**: $f_f(n(\beta)m(t)\gamma, s) = \big(\prod_v\chi_{V,v}(t)|t|_v^{s+1}\big)\,f_f(\gamma, s)$
(place by place, `secS_borel`). -/
theorem finSec_borel (β : F) (t : Fˣ) (γ : SL(2, F)) (s : ℂ) :
    finSec a (nMat β * mMat t * γ) s = (∏ᶠ v, borelFactorV a t s v) * finSec a γ s := by
  unfold finSec
  rw [← finprod_mul_distrib (hasFiniteMulSupport_borelFactorV a t s) (hasFiniteMulSupport_secS a γ s)]
  congr 1; funext v
  rw [map_mul, map_mul, locSL_nMat, locSL_mMat, secS_borel]
  rfl

lemma finprod_ofReal_cpow {f : HeightOneSpectrum (𝓞 F) → ℝ} (hf : Function.HasFiniteMulSupport f)
    (h0 : ∀ v, 0 ≤ f v) (w : ℂ) : ∏ᶠ v, ((f v : ℝ) : ℂ) ^ w = ((∏ᶠ v, f v : ℝ) : ℂ) ^ w := by
  classical
  have hf' : (Function.mulSupport f).Finite := hf
  have hsub : Function.mulSupport (fun v => ((f v : ℝ) : ℂ) ^ w) ⊆ hf'.toFinset := fun v hv =>
    hf'.mem_toFinset.mpr fun h => hv (by simp only; rw [h]; simp)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub,
    finprod_eq_prod_of_mulSupport_subset _ (fun v hv => hf'.mem_toFinset.mpr hv)]
  induction hf'.toFinset using Finset.induction_on with
  | empty => simp
  | insert u S hu ih =>
    rw [Finset.prod_insert hu, Finset.prod_insert hu, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (h0 u) (Finset.prod_nonneg fun v _ => h0 v)]

/-- **An archimedean section** for $\mathrm{SL}_2(F)$: a function $f_\infty$ with
$f_\infty(n(\beta)m(t)\gamma) = \chi_{V,\infty}(t)\,|t|_\infty^{s+1}f_\infty(\gamma)$ for $\beta \in F$, $t \in F^\times$, where
$\chi_{V,\infty}$ and $|t|_\infty = |N_{F/\mathbb Q}(t)|$ are those of the archimedean model `localDataInf`. Example: $\gamma \mapsto
f_\infty(\gamma g_\infty, s)$ for a section of $I_\infty(s, \chi_V)$ and a fixed $g_\infty$ (at $s = s_0$:
$f_\infty(\gamma g_z) = \prod_wy_w^{m/2}(c_wz_w + d_w)^{-m}$, from `omegaG_inf_gOrb`). -/
def IsArchSection (fInf : SL(2, F) → ℂ) (s : ℂ) : Prop :=
  ∀ (β : F) (t : Fˣ) (γ : SL(2, F)), fInf (nMat β * mMat t * γ) =
    (localDataInf (F := F)).chiV (aInf a) (mixedEmbedding F (t : F)) *
      ((mixedEmbedding.norm (mixedEmbedding F (t : F)) : ℝ) : ℂ) ^ (s + 1) * fInf γ

/-- **The global section** $f(\gamma, s) = f_\infty(\gamma)\,f_f(\gamma, s)$ on $\mathrm{SL}_2(F)$. -/
def globalSec (fInf : SL(2, F) → ℂ) (s : ℂ) (γ : SL(2, F)) : ℂ := fInf γ * finSec a γ s

/-- **The global Borel factor is $1$**: $\chi_{V,\infty}(t)|t|_\infty^{s+1}\prod_v\chi_{V,v}(t)|t|_v^{s+1} = 1$ for $t \in F^\times$
(Hilbert reciprocity `chiV_prod_eq_one` and the product formula `prod_modulus_eq_one`). -/
theorem borelFactor_prod_eq_one (t : Fˣ) (s : ℂ) :
    (localDataInf (F := F)).chiV (aInf a) (mixedEmbedding F (t : F)) *
      ((mixedEmbedding.norm (mixedEmbedding F (t : F)) : ℝ) : ℂ) ^ (s + 1) * ∏ᶠ v, borelFactorV a t s v = 1 := by
  unfold borelFactorV
  rw [finprod_mul_distrib (hasFiniteMulSupport_chiV a t) (hasFiniteMulSupport_normPow t s)]
  have hχ := chiV_prod_eq_one a t
  have hn := prod_modulus_eq_one t.ne_zero
  have hfin : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖algebraMap F (v.adicCompletion F) (t : F)‖ :=
    (hasFiniteMulSupport_modK t.ne_zero).subset fun v hv h' => hv (by
      simp only at h' ⊢; rw [norm_algebraMap_eq_modK]; exact h')
  rw [finprod_ofReal_cpow hfin (fun v => norm_nonneg _)]
  have hprod : mixedEmbedding.norm (mixedEmbedding F (t : F)) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) (t : F)‖ = 1 := by
    rw [← hn]; congr 1; congr 1; funext v; exact norm_algebraMap_eq_modK v t
  have hpow : ((mixedEmbedding.norm (mixedEmbedding F (t : F)) : ℝ) : ℂ) ^ (s + 1) *
      ((∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) (t : F)‖ : ℝ) : ℂ) ^ (s + 1) = 1 := by
    rw [← Complex.mul_cpow_ofReal_nonneg (mixedEmbedding.norm_nonneg _)
      (finprod_nonneg fun v => norm_nonneg _), ← Complex.ofReal_mul, hprod, Complex.ofReal_one, Complex.one_cpow]
  linear_combination ((((mixedEmbedding.norm (mixedEmbedding F (t : F)) : ℝ) : ℂ) ^ (s + 1) *
      ((∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) (t : F)‖ : ℝ) : ℂ) ^ (s + 1))) * hχ +
    hpow

/-- **The global section is left $B(F)$-invariant**: $f(b\gamma, s) = f(\gamma, s)$ for $b \in B(F)$, so it descends to
$B(F)\backslash\mathrm{SL}_2(F)$. -/
@[kb "kudla2008" "§1 (the Eisenstein series $E(g, s, \\Phi) = \\sum_{\\gamma\\in P(F)\\backslash G(F)}\\Phi(\\gamma g, s)$) [unverified]"]
theorem globalSec_borel {fInf : SL(2, F) → ℂ} {s : ℂ} (hInf : IsArchSection a fInf s) {b : SL(2, F)}
    (hb : b ∈ borel F) (γ : SL(2, F)) : globalSec a fInf s (b * γ) = globalSec a fInf s γ := by
  have hb' : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hb
  set u : Fˣ := Units.mk0 _ (a_ne_zero_of_c_eq_zero hb')
  set x : F := (b : Matrix (Fin 2) (Fin 2) F) 0 1 / (b : Matrix (Fin 2) (Fin 2) F) 0 0
  have hbe : b = nMat ((u : F) ^ 2 * x) * mMat u := by
    rw [← mMat_nMat]; exact eq_cell_of_c_eq_zero b hb'
  unfold globalSec
  rw [hbe, hInf, finSec_borel]
  have := borelFactor_prod_eq_one a u s
  linear_combination (fInf γ * finSec a γ s) * this

/-- **The Siegel Eisenstein series** $E(s) = \sum_{\gamma\in B(F)\backslash\mathrm{SL}_2(F)}f(\gamma, s)$, $f = f_\infty\cdot f_f$
(`tsum`; it is $0$ if the series does not converge). With $f_\infty(\gamma) = f_\infty(\gamma g_\infty, s)$ this is
$E((g_\infty, 1), s, \Phi)$ for $\Phi_f = \bigotimes_v\mathbf 1_{L_v}$; absolute convergence for $\operatorname{Re}s > 1$ is cited
(Godement; Weil 1965), not formalized. -/
@[kb "kudla2008" "§1 [unverified]; Weil (1965) [unverified]"]
def eisenstein {fInf : SL(2, F) → ℂ} {s : ℂ} (hInf : IsArchSection a fInf s) : ℂ :=
  ∑' q : BQuot F, Quotient.lift (globalSec a fInf s) (fun g g' h => by
    have h' : QuotientGroup.rightRel (borel F) g g' := h
    rw [QuotientGroup.rightRel_apply] at h'
    have := globalSec_borel a hInf h' g
    rw [inv_mul_cancel_right] at this
    exact this.symm) q

/-- **The Bruhat expansion** $E(s) = f(1, s) + \sum_{\beta\in F}f(wn(\beta), s)$ (when the sum over $\beta$ converges);
$f(1, s) = f_\infty(1)$. -/
@[kb "bump1997" "§3.7 [unverified]"]
theorem eisenstein_eq_bruhat {fInf : SL(2, F) → ℂ} {s : ℂ} (hInf : IsArchSection a fInf s)
    (hsum : Summable fun β : F => globalSec a fInf s (wMat * nMat β)) :
    eisenstein a hInf = fInf 1 + ∑' β : F, globalSec a fInf s (wMat * nMat β) := by
  unfold eisenstein
  rw [← (bruhatEquiv (k := F)).tsum_eq]
  have hval : ∀ x : Unit ⊕ F, Quotient.lift (s := QuotientGroup.rightRel (borel F)) (globalSec a fInf s)
      (fun g g' h => by
        have h' : QuotientGroup.rightRel (borel F) g g' := h
        rw [QuotientGroup.rightRel_apply] at h'
        have := globalSec_borel a hInf h' g
        rw [inv_mul_cancel_right] at this
        exact this.symm) (bruhatEquiv (k := F) x) = globalSec a fInf s (bruhatRep x) := fun x => rfl
  simp only [hval]
  have h1 : HasSum (fun x : Unit ⊕ F => globalSec a fInf s (bruhatRep x))
      (fInf 1 + ∑' β : F, globalSec a fInf s (wMat * nMat β)) := by
    refine HasSum.sum ?_ hsum.hasSum
    have : (fun u : Unit => globalSec a fInf s (bruhatRep (Sum.inl u))) = fun _ => fInf 1 := by
      funext u; simp [bruhatRep, globalSec]
    simp only [Function.comp_def, this]
    simp
  exact h1.tsum_eq

end Global

/-! ### The Siegel product of the local Whittaker integrals -/

section Siegel

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {m : ℕ}

local notation "RP" => {w : InfinitePlace F // InfinitePlace.IsReal w}

/-- $\sigma_w$ of `ArchTheta` is the real embedding `Siegel.realEmb` of `Siegel/NFMainTerm.lean`. -/
lemma ew_eq_realEmb (w : RP) (x : F) : ew w x = Siegel.realEmb w x := by
  simp [ew, Siegel.realEmb, mixedEmbedding]

/-- **The archimedean Whittaker factor over $F_\infty$** ($F$ totally real), for $Q = \sum_ib_ix_i^2$ and $z \in \mathbb H^d$:
$$W_\infty(t, z) = \gamma_{V,\infty}\,c_{B,\infty}\prod_{w}y_w^{m/2}\int_{\mathbb R}\mathcal G_w(z_w + x)\,e(-\sigma_w(t)x)\,dx,$$
$\mathcal G_w$ the Gaussian integral of $\sigma_w(Q)$ (`gaussQ`), $\gamma_{V,\infty}$, $c_{B,\infty}$ those of `localDataInf`: the integral over
$F_\infty$ of $f_\infty(wn(x)g_z)\psi_\infty(-tx)$, which is the product of the one-place integrals. -/
def archWhittakerInf (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (z : RP → ℂ) (t : F) : ℂ :=
  (localDataInf (F := F)).gammaV (aInf (unitsOfInt b hb)) * (localDataInf (F := F)).cB (aInf (unitsOfInt b hb)) *
    ∏ w : RP, ((z w).im : ℂ) ^ ((m : ℂ) / 2) *
      ∫ x : ℝ, gaussQ (fun i => ew w (b i : F)) (z w + x) * Complex.exp (-2 * Real.pi * Complex.I * ew w t * x)

/-- **Item 4, the Siegel product** ($F$ totally real; $Q = \sum_{i<n}b_ix_i^2$ totally positive, $b_i \in \mathcal O_F$; $n = 2m \ge 4$;
$t \in \mathcal O_F$ totally positive; $z \in \mathbb H^d$). If Siegel's product of local densities converges,
$\prod_v\beta_v(Q, t) = P$, then the local Whittaker integrals have the Euler product $\prod_vW_v(t) = C_f\,P$ and
$$W_\infty(t, z)\cdot\prod_{v<\infty}W_v(t) = |d_F|^{-(n-1)/2}\cdot\prod_{w\mid\infty}y_w^{m/2}\beta_w(t)\,e^{2\pi i\sigma_w(t)z_w}\cdot\prod_{v<\infty}\beta_v(t),$$
$\beta_w(t)$ the archimedean density of $\sigma_w(Q)$ (`Siegel.betaInfR`, $= \frac{\pi^m}{\Gamma(m)}D_w^{-1/2}\sigma_w(t)^{m-1}$). This is the
right-hand side of the classical $a_E(t) = |d_F|^{-(n-1)/2}\beta_\infty(t)\prod_\mathfrak p\beta_\mathfrak p(t)$ (Siegel 1935; Weil 1965); the
left-hand side is the $t$-th Fourier coefficient of $E$ once the unfolding (cited, not formalized) is granted. -/
@[kb "weil1965" "Ch. II–IV (Siegel's formula: the Fourier coefficients of the Eisenstein series) [unverified]; Siegel (1935) [unverified]"]
theorem whittakerEuler_eq_siegel (hm : 2 ≤ m) (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hpos : ∀ (w : RP) i, 0 < ew w (b i : F)) (t : 𝓞 F) (ht : t ≠ 0) (htpos : ∀ w : RP, 0 < ew w (t : F))
    (z : RP → ℂ) (hz : ∀ w, 0 < (z w).im) {P : ℝ}
    (hP : HasProd (fun v : HeightOneSpectrum (𝓞 F) => LocalDensity.NF.localDensity v (QuadForm.diag b) t) P) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
        whittakerV v (aOfInt v b hb) ((LocalDensity.NF.ι v t : v.adicCompletionIntegers F) : v.adicCompletion F))
      (constFin (unitsOfInt b hb) * P) ∧
    archWhittakerInf b hb z t * (constFin (unitsOfInt b hb) * P) =
      (((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * m - 1) : ℝ) : ℂ) *
        (∏ w : RP, ((z w).im : ℂ) ^ ((m : ℂ) / 2) *
          ((Siegel.betaInfR (QuadForm.diag fun i => ew w (b i : F)) (ew w (t : F)) : ℝ) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * ew w (t : F) * z w)) * P := by
  refine ⟨hasProd_whittakerV (by omega) b hb t ht hP, ?_⟩
  have hw : ∀ w : RP, ∫ x : ℝ, gaussQ (fun i => ew w (b i : F)) (z w + x) *
      Complex.exp (-2 * Real.pi * Complex.I * ew w (t : F) * x) =
      ((Siegel.betaInfR (QuadForm.diag fun i => ew w (b i : F)) (ew w (t : F)) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ew w (t : F) * z w) := by
    intro w
    rw [archWhittaker_eq _ hm (hpos w) (hz w), if_pos (htpos w)]
  have hc := globalConst_eq (unitsOfInt b hb)
  unfold archWhittakerInf
  simp only [hw, ← mul_assoc]
  rw [← hc]
  ring

/-- **The archimedean factor is the repo's $\beta_w$ over $F$** (`Siegel.betaInfAt`, Hanke (5.3)/(5.5) over $F$). -/
lemma betaInfR_ew_eq_betaInfAt (b : Fin (2 * m) → 𝓞 F) (w : RP) (t : F) :
    Siegel.betaInfR (QuadForm.diag fun i => ew w (b i : F)) (ew w t) = Siegel.betaInfAt (QuadForm.diag b) w t := by
  rw [Siegel.betaInfAt_eq_betaInfR, ew_eq_realEmb]
  congr 1
  unfold Siegel.realForm QuadForm.map QuadForm.diag
  congr 1
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.map_apply]
  split_ifs with h
  · subst h; simp [ew_eq_realEmb]
  · simp

end Siegel

end QuadFormsKB.SiegelWeil
