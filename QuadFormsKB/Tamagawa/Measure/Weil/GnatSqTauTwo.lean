import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqGeneral
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqAnyD
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqGlobal
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarTernary
import QuadFormsKB.Tamagawa.Measure.Weil.GnatTamagawa

/-!
# $\tau(SO(V)) = 2$ for the square model and for every quaternary form with square discriminant

**Layer:** a number field $F$ (any signature, complex places allowed, any class number); $a, b \in \mathcal O_F \setminus 0$;
$Q_0$ any nondegenerate quaternary quadratic form over $\mathcal O_F$ whose discriminant is a square in $F$.

**Proves** (unconditional):
* **`covolume_muTam_qSq_any`**: for the norm form $\langle 1,-a,-b,ab\rangle$ of $\mathbb H[F,a,b]$ (division algebra or
  $M_2(F)$), $\mathrm{covol}(SO(V)(F), SO(V)(\mathbb A), \mu_{\mathrm{Tam}}) = 2$. Transport along the isomorphism
  $\Phi$ = `sqPEquiv` carrying $\mu_P$ to $\mu_{\mathrm{Tam}}$ and the global points onto the global points, together with
  $\mathrm{vol}(P(F)\backslash P(\mathbb A)) = 2$.
* **`covolume_muTam_quaternary_of_isSquare`**: the same for every nondegenerate quaternary form over $\mathcal O_F$ whose
  Hessian determinant is a square in $F$. Integral diagonalization $Q_0\circ G = \langle e_0,e_1,e_2,e_3\rangle$, the
  similarity $e_0\langle e_0,\dots,e_3\rangle = \langle 1,e_0e_1,e_0e_2,e_0e_3\rangle\circ\mathrm{diag}(e_0,1,1,1)$, the change of lattice
  $\langle 1,c_0,c_1,c_2\rangle\circ\mathrm{diag}(1,c_1c_2,c_0c_2,c_0c_1c_2) = \langle 1,-a'd',-b'd',a'b'd'\rangle$ with
  $a' = -c_2c_1$, $b' = -c_2c_0$, $d' = c_0c_1c_2$, and $d' = t^2$ gives
  $\langle 1,-a'd',-b'd',a'b'd'\rangle = \langle 1,-a',-b',a'b'\rangle\circ\mathrm{diag}(1,t,t,t)$. Every step preserves the
  covolume (`covolume_muTam_simForm`).
* `tamagawaNumberTwoAdelic_qSq_any`, `tamagawaNumberTwoAdelic_quaternary_of_isSquare`: the same, as `TamagawaNumberTwoAdelic`.

Source: Weil 1982, §3.7, Thm 3.7.1 ($m = 4$, square discriminant), p. 65; Thm 2.3.1, pp. 21–22.
-/

open MeasureTheory Measure Set Function Topology NumberField NumberField.InfinitePlace Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F]

/-- **$\tau(SO(\langle1,-a,-b,ab\rangle)) = 2$ for every quaternion algebra $\mathbb H[F,a,b]$ over every number field**
(unconditional; division algebra or $M_2(F)$, every signature). -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65; Thm 2.3.1, pp. 21–22 [unverified page]"]
theorem covolume_muTam_qSq_any {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) (hQ : (qSq a b).Nondegenerate) :
    covolume (GammaSOAdele (qSq a b)) (SOAdele (qSq a b)) (muTam (qSq a b) hQ fun _ => 1) = 2 := by
  have := (gnatSqO ha hb).isHaarMeasure_muP (muSq ha hb)
  rw [covolume_eq_of_continuousMulEquiv _ _ (sqPEquiv ha hb) (map_gamP_sqPEquiv ha hb) _ _
    (map_muP_sqPEquiv_eq_muTam_any ha hb hQ)]
  exact covolume_gnatSq_any ha hb

/-- **`TamagawaNumberTwoAdelic` for the norm form $\langle1,-a,-b,ab\rangle$ over every number field** (unconditional). -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65; Thm 2.3.1, pp. 21–22 [unverified page]"]
theorem tamagawaNumberTwoAdelic_qSq_any {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) (hQ : (qSq a b).Nondegenerate) :
    TamagawaNumberTwoAdelic (qSq a b) hQ :=
  covolume_muTam_qSq_any ha hb hQ

/-! ### Bookkeeping for the reduction to the square model -/

section Reduction

/-- The Hessian of a diagonal form is $\mathrm{diag}(2e_i)$. -/
private theorem hessian_diag_eq {n : ℕ} (e : Fin n → 𝓞 F) :
    (QuadForm.diag e).hessian = diagonal fun i => 2 * e i := by
  unfold QuadForm.hessian QuadForm.diag
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, two_mul]

/-- $1\cdot Q = Q$. -/
private theorem one_smul_form {n : ℕ} (Q : QuadForm (𝓞 F) n) : (1 : 𝓞 F) • Q = Q := by
  ext i j; simp [QuadForm.smul_coeff]

/-- A diagonal quaternary form with nonzero coefficients is nondegenerate. -/
private theorem nondegenerate_diag_four {f : Fin 4 → 𝓞 F} (hf : ∀ i, f i ≠ 0) : (QuadForm.diag f).Nondegenerate := by
  rw [QuadForm.Nondegenerate, hessian_diag_eq, det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero two_ne_zero (hf i)

/-- Scalar multiples of diagonal forms. -/
private theorem smul_diag_eq {n : ℕ} (c : 𝓞 F) (e : Fin n → 𝓞 F) :
    c • QuadForm.diag e = QuadForm.diag fun i => c * e i := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [QuadForm.smul_coeff, QuadForm.diag]
  · simp [QuadForm.smul_coeff, QuadForm.diag, diagonal_apply_ne _ hij]

/-- The covolume is unchanged along a similarity $Q' = c\,(Q\circ G)$ of quaternary forms. -/
private theorem covolume_muTam_of_simForm_eq {Q Q' : QuadForm (𝓞 F) 4} {c : 𝓞 F} {G : Matrix (Fin 4) (Fin 4) (𝓞 F)}
    (hQ : Q.Nondegenerate) (hc : c ≠ 0) (hG : G.det ≠ 0) (h : simForm Q c G = Q') (hQ' : Q'.Nondegenerate) :
    covolume (GammaSOAdele Q') (SOAdele Q') (muTam Q' hQ' fun _ => 1) =
      covolume (GammaSOAdele Q) (SOAdele Q) (muTam Q hQ fun _ => 1) := by
  subst h
  exact covolume_muTam_simForm (by norm_num) (by norm_num) hQ hc hG

private theorem det_diagonal_ne_zero {f : Fin 4 → 𝓞 F} (hf : ∀ i, f i ≠ 0) : (diagonal f).det ≠ 0 := by
  rw [det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => hf i

/-- $\langle 1,c_0,c_1,c_2\rangle\circ\mathrm{diag}(1,c_1c_2,c_0c_2,c_0c_1c_2) = \langle 1,-a'd',-b'd',a'b'd'\rangle$ with
$a' = -c_2c_1$, $b' = -c_2c_0$, $d' = c_0c_1c_2$. -/
private theorem diag_one_compMat_eq_qNS (c₀ c₁ c₂ : 𝓞 F) :
    (QuadForm.diag ![1, c₀, c₁, c₂]).compMat (diagonal ![1, c₁ * c₂, c₀ * c₂, c₀ * c₁ * c₂]) =
      qNS (-(c₂ * c₁)) (-(c₂ * c₀)) (c₀ * c₁ * c₂) := by
  rw [diag_compMat_diagonal, qNS]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

/-- If $d' = t\cdot t$ then $\langle 1,-a',-b',a'b'\rangle\circ\mathrm{diag}(1,t,t,t) = \langle 1,-a'd',-b'd',a'b'd'\rangle$. -/
private theorem qSq_compMat_eq_qNS (a b t d : 𝓞 F) (ht : t * t = d) :
    (qSq a b).compMat (diagonal ![1, t, t, t]) = qNS a b d := by
  rw [qSq, diag_compMat_diagonal, qNS]
  congr 1
  funext i
  fin_cases i <;> simp <;> rw [← ht] <;> ring

end Reduction

set_option maxHeartbeats 1600000 in
/-- **$\tau(SO(V)) = 2$ for every quaternary quadratic space with square discriminant, over every number field**
(unconditional; every signature, any class number, any quaternion algebra). $Q_0$ is any nondegenerate quaternary form over
$\mathcal O_F$ whose Hessian determinant is a square in $F$ (so $V = (F^4, Q_0)$ is, up to similarity, the norm form of a
quaternion algebra). -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4, square discriminant), p. 65; Thm 2.3.1, pp. 21–22 [unverified page]"]
theorem covolume_muTam_quaternary_of_isSquare (Q₀ : QuadForm (𝓞 F) 4) (hQ : Q₀.Nondegenerate)
    (hsq : IsSquare ((algebraMap (𝓞 F) F) Q₀.hessian.det)) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 2 := by
  obtain ⟨G, hG, e, he, hGe⟩ := LatChange.exists_compMat_eq_diag Q₀ hQ
  have h1 : (1 : 𝓞 F) ≠ 0 := one_ne_zero
  -- step 1: `Q₀ ~ ⟨e₀, e₁, e₂, e₃⟩`
  have hD : simForm Q₀ 1 G = QuadForm.diag e := by
    rw [← hGe]; ext i j; simp [simForm, QuadForm.smul_coeff]
  have hQD : (QuadForm.diag e).Nondegenerate := nondegenerate_diag_four he
  have s1 := covolume_muTam_of_simForm_eq hQ h1 hG hD hQD
  -- the discriminant: `e₀e₁e₂e₃ = u * u`
  obtain ⟨s, hs⟩ := hsq
  have hdet : (16 : 𝓞 F) * (e 0 * e 1 * e 2 * e 3) = G.det ^ 2 * Q₀.hessian.det := by
    have h := congrArg (fun Q : QuadForm (𝓞 F) 4 => Q.hessian.det) hGe
    simp only [hessian_diag_eq, det_diagonal, QuadForm.hessian_compMat, det_mul, det_transpose,
      Fin.prod_univ_four] at h
    linear_combination -h
  set g : F := algebraMap (𝓞 F) F G.det
  obtain ⟨u, hu⟩ : ∃ u : F, ((e 0 * e 1 * e 2 * e 3 : 𝓞 F) : F) = u * u := by
    refine ⟨g * s / 4, ?_⟩
    have := congrArg (algebraMap (𝓞 F) F) hdet
    simp only [map_mul, map_pow, map_ofNat] at this
    rw [hs] at this
    have h16 : (16 : F) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h16
    push_cast
    field_simp
    linear_combination this
  -- step 2: `⟨e⟩ ~ ⟨1, e₀e₁, e₀e₂, e₀e₃⟩`
  set c₀ : 𝓞 F := e 0 * e 1
  set c₁ : 𝓞 F := e 0 * e 2
  set c₂ : 𝓞 F := e 0 * e 3
  have hc₀ : c₀ ≠ 0 := mul_ne_zero (he 0) (he 1)
  have hc₁ : c₁ ≠ 0 := mul_ne_zero (he 0) (he 2)
  have hc₂ : c₂ ≠ 0 := mul_ne_zero (he 0) (he 3)
  have hfne : ∀ i, (![1, c₀, c₁, c₂] : Fin 4 → 𝓞 F) i ≠ 0 := by
    intro i; fin_cases i <;> simp [hc₀, hc₁, hc₂]
  have hQf : (QuadForm.diag ![1, c₀, c₁, c₂]).Nondegenerate := nondegenerate_diag_four hfne
  set Gid : Matrix (Fin 4) (Fin 4) (𝓞 F) := diagonal fun _ => 1
  have hGid : Gid.det ≠ 0 := det_diagonal_ne_zero fun _ => one_ne_zero
  set G2 : Matrix (Fin 4) (Fin 4) (𝓞 F) := diagonal ![e 0, 1, 1, 1]
  have hG2 : G2.det ≠ 0 := det_diagonal_ne_zero fun i => by fin_cases i <;> simp [he 0]
  have hs2a : simForm (QuadForm.diag e) (e 0) Gid = QuadForm.diag fun i => e 0 * (1 * 1 * e i) := by
    rw [simForm, diag_compMat_diagonal, smul_diag_eq]
  have hs2b : simForm (QuadForm.diag ![1, c₀, c₁, c₂]) 1 G2 = QuadForm.diag fun i => e 0 * (1 * 1 * e i) := by
    rw [simForm, diag_compMat_diagonal, smul_diag_eq]
    congr 1
    funext i
    fin_cases i <;> simp [c₀, c₁, c₂, G2] <;> ring
  have hQ2 : (QuadForm.diag fun i => e 0 * (1 * 1 * e i)).Nondegenerate :=
    nondegenerate_diag_four fun i => mul_ne_zero (he 0) (by simpa using he i)
  have s2a := covolume_muTam_of_simForm_eq hQD (he 0) hGid hs2a hQ2
  have s2b := covolume_muTam_of_simForm_eq hQf h1 hG2 hs2b hQ2
  -- step 3: `⟨1, c⟩ ~ qNS a' b' d'`
  set a' : 𝓞 F := -(c₂ * c₁)
  set b' : 𝓞 F := -(c₂ * c₀)
  set d' : 𝓞 F := c₀ * c₁ * c₂
  have ha0 : a' ≠ 0 := neg_ne_zero.2 (mul_ne_zero hc₂ hc₁)
  have hb0 : b' ≠ 0 := neg_ne_zero.2 (mul_ne_zero hc₂ hc₀)
  have hd0 : d' ≠ 0 := mul_ne_zero (mul_ne_zero hc₀ hc₁) hc₂
  set G3 : Matrix (Fin 4) (Fin 4) (𝓞 F) := diagonal ![1, c₁ * c₂, c₀ * c₂, c₀ * c₁ * c₂]
  have hG3 : G3.det ≠ 0 := det_diagonal_ne_zero fun i => by
    fin_cases i <;> simp [G3, hc₀, hc₁, hc₂]
  have hs3 : simForm (QuadForm.diag ![1, c₀, c₁, c₂]) 1 G3 = qNS a' b' d' := by
    rw [simForm, one_smul_form]; exact diag_one_compMat_eq_qNS c₀ c₁ c₂
  have hQns : (qNS a' b' d').Nondegenerate := by
    refine nondegenerate_diag_four fun i => ?_
    fin_cases i <;> simp [mul_ne_zero, ha0, hb0, hd0, d'] <;> simp_all
  have s3 := covolume_muTam_of_simForm_eq hQf h1 hG3 hs3 hQns
  -- step 4: `qSq a' b' ∘ diag(1,t,t,t) = qNS a' b' d'`, `d' = t²`
  have hd : ((d' : 𝓞 F) : F) = (e 0 * u) * (e 0 * u) := by
    have : ((d' : 𝓞 F) : F) = (e 0 : F) * (e 0) * (((e 0 * e 1 * e 2 * e 3 : 𝓞 F) : F)) := by
      simp only [d', c₀, c₁, c₂]; push_cast; ring
    rw [this, hu]; ring
  have hti : IsIntegral ℤ (e 0 * u) := IsIntegral.of_pow two_pos (by
    rw [sq, ← hd]; exact d'.isIntegral_coe)
  set t' : 𝓞 F := ⟨(e 0 : F) * u, hti⟩
  have ht' : t' * t' = d' := RingOfIntegers.coe_injective (by
    change (e 0 * u) * (e 0 * u) = (d' : F); rw [hd])
  have ht0 : t' ≠ 0 := by
    intro h0; rw [h0, mul_zero] at ht'; exact hd0 ht'.symm
  set H : Matrix (Fin 4) (Fin 4) (𝓞 F) := diagonal ![1, t', t', t']
  have hH : H.det ≠ 0 := det_diagonal_ne_zero fun i => by fin_cases i <;> simp [H, ht0]
  have hQsq : (qSq a' b').Nondegenerate := nondegenerate_diag_four fun i => by
    fin_cases i <;> simp [ha0, hb0, mul_ne_zero]
  have hs4 : simForm (qSq a' b') 1 H = qNS a' b' d' := by
    rw [simForm, one_smul_form]; exact qSq_compMat_eq_qNS a' b' t' d' ht'
  have s4 := covolume_muTam_of_simForm_eq hQsq h1 hH hs4 hQns
  -- assemble
  have hfinal := covolume_muTam_qSq_any ha0 hb0 hQsq
  rw [← s1, ← s2a, s2b, ← s3, s4]
  exact hfinal

/-- **`TamagawaNumberTwoAdelic` for every nondegenerate quaternary form with square discriminant over every number
field** (unconditional). -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4, square discriminant), p. 65; Thm 2.3.1, pp. 21–22 [unverified page]"]
theorem tamagawaNumberTwoAdelic_quaternary_of_isSquare (Q₀ : QuadForm (𝓞 F) 4) (hQ : Q₀.Nondegenerate)
    (hsq : IsSquare ((algebraMap (𝓞 F) F) Q₀.hessian.det)) : TamagawaNumberTwoAdelic Q₀ hQ :=
  covolume_muTam_quaternary_of_isSquare Q₀ hQ hsq

end QuadFormsKB.Tamagawa.Measure.Weil
