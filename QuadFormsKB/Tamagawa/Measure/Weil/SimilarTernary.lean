import QuadFormsKB.Tamagawa.Measure.Weil.SimilarGlobal
import QuadFormsKB.Tamagawa.Measure.Weil.SplitSL1Headline
import QuadFormsKB.Tamagawa.TernaryReduction

/-!
# $\tau(SO(V)) = 2$ for every ternary quadratic space over every number field

**Layer:** a number field $F$ (any signature, complex places allowed, any class number); $Q_0$ any nondegenerate ternary
quadratic form over $\mathcal O_F$ (the space $V = (F^3, Q_0)$; every ternary quadratic space over $F$ has such an integral
model after scaling).

Every such form is similar over $F$ to a pure quaternion form $\langle -a,-b,ab\rangle$, $a, b \in \mathcal O_F\setminus 0$:
integral diagonalization $Q_0\circ G = \langle e_0,e_1,e_2\rangle$ (`LatChange.exists_compMat_eq_diag`) and
$e_0e_1e_2\cdot\langle e_0,e_1,e_2\rangle\circ\mathrm{diag}(1,1,e_0e_1) = \langle -a,-b,ab\rangle$
(`LatChange.smul_diag_compMat_eq_pureFormO`). The covolume of $SO(V)(F)$ for Weil's Tamagawa measure is invariant under
$Q \mapsto c\,(Q\circ G)$ (`covolume_muTam_simForm`), and for $\langle -a,-b,ab\rangle$ it is known for every quaternion
algebra (`covolume_muTam_pureForm_unconditional`).

**Proves** (unconditional):
* **`covolume_muTam_ternary`**: $\mathrm{covol}(SO(V)(F), SO(V)(\mathbb A), \mu_{\mathrm{Tam}}) = 2$
  (with Weil's complex normalization of `muTam`);
* **`covolume_muTamWeil_ternary`**: $\tau(SO(V)) = 2$ in Weil's normalization `muTamWeil`;
* **`tamagawaNumberTwoAdelic_ternary_of_totallyReal`**: `TamagawaNumberTwoAdelic Q₀` for every nondegenerate ternary
  $Q_0$ over a totally real field, every signature.

Source: Weil 1982, §3.7(a), pp. 62–63 (every ternary space is similar to $(D^0, \mathrm{nrd})$), Thm 3.7.1 ($m = 3$),
p. 65; Thm 2.3.1, pp. 21–22 (product formula).
-/

open MeasureTheory NumberField NumberField.InfinitePlace Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.QuatZeta

variable {F : Type} [Field F] [NumberField F]

/-- The covolume depends only on the form (the nondegeneracy proof is irrelevant). -/
theorem covolume_muTam_congr {n : ℕ} {Q Q' : QuadForm (𝓞 F) n} (h : Q = Q') (hQ : Q.Nondegenerate)
    (hQ' : Q'.Nondegenerate) :
    covolume (GammaSOAdele Q) (SOAdele Q) (muTam Q hQ fun _ => 1) =
      covolume (GammaSOAdele Q') (SOAdele Q') (muTam Q' hQ' fun _ => 1) := by
  subst h; rfl

/-- **Every nondegenerate ternary form over $\mathcal O_F$ has the covolume of a pure quaternion form**: there are
$a, b \in \mathcal O_F\setminus 0$ with $\mathrm{covol}(Q_0) = \mathrm{covol}(\langle -a,-b,ab\rangle)$. -/
theorem exists_covolume_muTam_eq_pureForm (Q₀ : QuadForm (𝓞 F) 3) (hQ : Q₀.Nondegenerate) :
    ∃ a b : 𝓞 F, ∃ (ha : a ≠ 0) (hb : b ≠ 0),
      covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) =
        covolume (GammaSOAdele (pureFormO a b)) (SOAdele (pureFormO a b))
          (muTam (pureFormO a b) (nondegenerate_pureFormO a b ha hb) fun _ => 1) := by
  obtain ⟨G, hG, e, he, hGe⟩ := LatChange.exists_compMat_eq_diag Q₀ hQ
  have h1 : (1 : 𝓞 F) ≠ 0 := one_ne_zero
  -- step 1: Q₀ ~ ⟨e₀, e₁, e₂⟩
  have hD : simForm Q₀ 1 G = QuadForm.diag e := by
    rw [← hGe]; ext i j; simp [simForm, QuadForm.smul_coeff]
  have hQD : (QuadForm.diag e).Nondegenerate := hD ▸ nondegenerate_simForm hQ h1 hG
  have s1 := covolume_muTam_simForm (by norm_num) (by norm_num) hQ h1 hG
  rw [covolume_muTam_congr hD _ hQD] at s1
  -- step 2: ⟨e₀, e₁, e₂⟩ ~ ⟨-a, -b, ab⟩
  set cv : Fin 3 → 𝓞 F := ![1, 1, e 0 * e 1]
  have hcv : (diagonal cv).det ≠ 0 := by
    rw [det_diagonal, Fin.prod_univ_three]
    simp [cv, he 0, he 1]
  have hc' : e 0 * e 1 * e 2 ≠ 0 := mul_ne_zero (mul_ne_zero (he 0) (he 1)) (he 2)
  have hP : simForm (QuadForm.diag e) (e 0 * e 1 * e 2) (diagonal cv) =
      pureFormO (-(e 0 ^ 2 * e 1 * e 2)) (-(e 0 * e 1 ^ 2 * e 2)) := LatChange.smul_diag_compMat_eq_pureFormO e
  have ha : -(e 0 ^ 2 * e 1 * e 2) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (he 0)) (he 1)) (he 2))
  have hb : -(e 0 * e 1 ^ 2 * e 2) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (he 0) (pow_ne_zero _ (he 1))) (he 2))
  have s2 := covolume_muTam_simForm (by norm_num) (by norm_num) hQD hc' hcv
  rw [covolume_muTam_congr hP _ (nondegenerate_pureFormO _ _ ha hb)] at s2
  exact ⟨_, _, ha, hb, s1.symm.trans s2.symm⟩

/-- **The covolume of $SO(V)(F)$ for `muTam` is $2$ for every nondegenerate ternary form over $\mathcal O_F$,
over every number field** (unconditional; every signature, split or division quaternion algebra). -/
@[kb "weil1982" "§3.7(a), pp. 62–63; Thm 3.7.1 (m = 3), p. 65; Thm 2.3.1, pp. 21–22"]
theorem covolume_muTam_ternary (Q₀ : QuadForm (𝓞 F) 3) (hQ : Q₀.Nondegenerate) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 2 := by
  obtain ⟨a, b, ha, hb, h⟩ := exists_covolume_muTam_eq_pureForm Q₀ hQ
  rw [h, covolume_muTam_pureForm_unconditional a b ha hb]

/-- **$\tau(SO(V)) = 2$ for every ternary quadratic space over every number field**, in Weil's normalization
`muTamWeil` (unconditional). -/
@[kb "weil1982" "§3.7(a), pp. 62–63; Thm 3.7.1 (m = 3), p. 65; Thm 2.3.1, pp. 21–22"]
theorem covolume_muTamWeil_ternary (Q₀ : QuadForm (𝓞 F) 3) (hQ : Q₀.Nondegenerate) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTamWeil Q₀ hQ) = 2 := by
  rw [muTamWeil_eq_muTam]
  exact covolume_muTam_ternary Q₀ hQ

/-- **`TamagawaNumberTwoAdelic` for every nondegenerate ternary form over a totally real field**, every signature
(unconditional). -/
@[kb "weil1982" "§3.7(a), pp. 62–63; Thm 3.7.1 (m = 3), p. 65"]
theorem tamagawaNumberTwoAdelic_ternary_of_totallyReal [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) 3)
    (hQ : Q₀.Nondegenerate) : TamagawaNumberTwoAdelic Q₀ hQ := by
  rw [TamagawaNumberTwoAdelic]
  exact covolume_muTam_ternary Q₀ hQ

end QuadFormsKB.Tamagawa.Measure.Weil
