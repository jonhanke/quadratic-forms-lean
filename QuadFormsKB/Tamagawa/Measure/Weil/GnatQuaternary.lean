import QuadFormsKB.Tamagawa.Measure.Weil.GnatSiegelTotallyReal
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarTernary

/-!
# $\tau(SO(V)) = 2$ for every quaternary quadratic space over every number field

**Layer:** a number field $F$ (any signature, complex places allowed, any class number); $Q_0$ any nondegenerate
quaternary quadratic form over $\mathcal O_F$ (the space $V = (F^4, Q_0)$; every quaternary quadratic space over $F$ has
such an integral model after scaling). The quaternion algebras that occur may be division algebras or split
($V$ isotropic is allowed).

**Reduction to the two models** (Weil 1982, §3.7, pp. 63–65). Integral diagonalization
$Q_0\circ G = \langle e_0,e_1,e_2,e_3\rangle$ (`LatChange.exists_compMat_eq_diag`). With $c_i = e_0e_{i+1}$ ($i = 0, 1, 2$),
$$e_0\cdot\langle e_0,e_1,e_2,e_3\rangle = \langle1,c_0,c_1,c_2\rangle\circ\mathrm{diag}(e_0,1,1,1),\qquad
\langle1,c_0,c_1,c_2\rangle\circ\mathrm{diag}(1,c_1c_2,c_0c_2,c_0c_1c_2) = \langle1,-ad,-bd,abd\rangle = q_{\mathrm{ns}}(a,b,d)$$
with $a = -c_1c_2$, $b = -c_0c_2$, $d = c_0c_1c_2$ (`qNS`). If $d = t^2$ then $q_{\mathrm{ns}}(a,b,d) = q_{\mathrm{sq}}(a,b)\circ\mathrm{diag}(1,t,t,t)$
(`qSq`, $V\cong(D,\operatorname{nrd})$ for $D = (a,b)_F$); otherwise $K = F(\sqrt d)$ (`quadFieldOf`) and $D_K = (a,b)_K$.
`TamagawaNumberTwoAdelic` is invariant under $Q\mapsto c\,(Q\circ G)$ (`tamagawaNumberTwoAdelic_simForm_iff`, from
`covolume_muTam_simForm`, valid for $n = 4$).

**Proves**
* **`tamagawaNumberTwoAdelic_quaternary`**: Weil's adelic $\tau(SO(V)) = 2$ for every nondegenerate quaternary $Q_0$ over every
  number field, every signature, **conditional only on the named input `GnatTamagawaComparison F`** (the measure comparison
  $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ for the two models). The covolume $2$ for $G^\natural/\mathbb G_m$ is proved for every
  quaternion algebra, division or split (`covolume_gnatSq`, `covolume_gnatBC`, via the `tauSL1EqOne`).
* **`tamagawaNumberTwoAdelic_quaternary_definite`**: the same over every totally real $F$ for every $Q_0$ that is definite at
  every real place (positive definite at some places and negative definite at others is allowed), **unconditionally**
  (the proved comparison `gnatTamagawaComparisonDef`; the finite places are arbitrary, so $V$ may be isotropic at every
  finite place).

Source: Weil 1982, §3.7, Thm 3.7.1 ($m = 4$), pp. 63–65 [unverified page]; Thm 2.3.1.
-/

open MeasureTheory NumberField NumberField.InfinitePlace Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F]

/-! ### Similarity invariance and the models -/

/-- A diagonal form over $\mathcal O_F$ with nonzero entries is nondegenerate. -/
theorem nondegenerate_diag_ringOfIntegers {n : ℕ} {e : Fin n → 𝓞 F} (he : ∀ i, e i ≠ 0) :
    (QuadForm.diag e).Nondegenerate := by
  unfold QuadForm.Nondegenerate QuadForm.hessian QuadForm.diag
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => by
    rw [← two_mul]; exact mul_ne_zero two_ne_zero (he i)

/-- **`TamagawaNumberTwoAdelic` is invariant under similarity** $Q\mapsto c\,(Q\circ G)$ ($c\ne0$, $\det G\ne0$, $n\ne0,2$). -/
theorem tamagawaNumberTwoAdelic_simForm_iff {n : ℕ} (hn0 : n ≠ 0) (hn2 : n ≠ 2) {Q₀ : QuadForm (𝓞 F) n}
    (hQ : Q₀.Nondegenerate) {c : 𝓞 F} (hc : c ≠ 0) {G : Matrix (Fin n) (Fin n) (𝓞 F)} (hG : G.det ≠ 0)
    {Q' : QuadForm (𝓞 F) n} (h : simForm Q₀ c G = Q') (hQ' : Q'.Nondegenerate) :
    TamagawaNumberTwoAdelic Q' hQ' ↔ TamagawaNumberTwoAdelic Q₀ hQ := by
  unfold TamagawaNumberTwoAdelic
  rw [← covolume_muTam_congr h (nondegenerate_simForm hQ hc hG) hQ', covolume_muTam_simForm hn0 hn2 hQ hc hG]

theorem simForm_one {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (G : Matrix (Fin n) (Fin n) (𝓞 F)) :
    simForm Q₀ 1 G = Q₀.compMat G := by
  ext i j; simp [simForm, QuadForm.smul_coeff]

/-- $\langle1,-a,-b,ab\rangle\circ\mathrm{diag}(1,t,t,t) = \langle1,-at^2,-bt^2,abt^2\rangle$. -/
theorem qSq_compMat_eq_qNS (a b t : 𝓞 F) : (qSq a b).compMat (diagonal ![1, t, t, t]) = qNS a b (t * t) := by
  rw [qSq, diag_compMat_diagonal, qNS]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

/-- **The model `qNS a b d` from the two cases**: if the square-discriminant model `qSq a b` and, for every number field
$K\supseteq F$ with an $F$-basis $(1,\delta)$, $\delta^2 = d$, the non-square model have $\tau = 2$, then so does `qNS a b d`
(for $d = t^2$, `qNS a b d = qSq a b ∘ diag(1,t,t,t)`; otherwise $K = F(\sqrt d)$). -/
theorem tamagawaNumberTwoAdelic_qNS_of {a b d : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hd0 : d ≠ 0)
    (hQ : (qNS a b d).Nondegenerate)
    (hsq : ∀ hQ' : (qSq a b).Nondegenerate, TamagawaNumberTwoAdelic (qSq a b) hQ')
    (hns : ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] (bK : Module.Basis (Fin 2) F K)
      (_hb₀ : bK 0 = 1) (_hb₁ : bK 1 * bK 1 = algebraMap F K (d : F)) (α β : 𝓞 K)
      (_hα : (α : K) = algebraMap F K (a : F)) (_hβ : (β : K) = algebraMap F K (b : F)) (_hα0 : α ≠ 0)
      (_hβ0 : β ≠ 0), TamagawaNumberTwoAdelic (qNS a b d) hQ) :
    TamagawaNumberTwoAdelic (qNS a b d) hQ := by
  by_cases hsq' : ∃ t : F, t ^ 2 = (d : F)
  · obtain ⟨t, ht⟩ := hsq'
    have hti : IsIntegral ℤ t := IsIntegral.of_pow two_pos (by rw [ht]; exact d.isIntegral_coe)
    set t' : 𝓞 F := ⟨t, hti⟩
    have ht' : t' * t' = d := RingOfIntegers.coe_injective (by
      change t * t = (d : F); rw [← ht, sq])
    have ht0 : t' ≠ 0 := by
      intro h0; rw [h0, mul_zero] at ht'; exact hd0 ht'.symm
    have hH : (diagonal ![1, t', t', t']).det ≠ 0 := by
      rw [det_diagonal, Fin.prod_univ_four]; simp [ht0]
    have hQsq : (qSq a b).Nondegenerate := nondegenerate_diag_ringOfIntegers fun i => by
      fin_cases i <;> simp [ha0, hb0]
    have h1 : simForm (qSq a b) 1 (diagonal ![1, t', t', t']) = qNS a b d := by
      rw [simForm_one, qSq_compMat_eq_qNS, ht']
    exact (tamagawaNumberTwoAdelic_simForm_iff (by norm_num) (by norm_num) hQsq one_ne_zero hH h1 hQ).2 (hsq hQsq)
  · push Not at hsq'
    have := fact_irreducible_quadPoly (d : F) hsq'
    have := numberField_quadFieldOf (d : F) hsq'
    set K := quadFieldOf (d : F)
    have hαi : IsIntegral ℤ (algebraMap F K (a : F)) := a.isIntegral_coe.algebraMap
    have hβi : IsIntegral ℤ (algebraMap F K (b : F)) := b.isIntegral_coe.algebraMap
    set α : 𝓞 K := ⟨algebraMap F K (a : F), hαi⟩
    set β : 𝓞 K := ⟨algebraMap F K (b : F), hβi⟩
    have hα0 : α ≠ 0 := fun h => ha0 (RingOfIntegers.coe_injective (by
      have h' : algebraMap F K (a : F) = 0 := congrArg Subtype.val h
      rw [map_eq_zero] at h'; simpa using h'))
    have hβ0 : β ≠ 0 := fun h => hb0 (RingOfIntegers.coe_injective (by
      have h' : algebraMap F K (b : F) = 0 := congrArg Subtype.val h
      rw [map_eq_zero] at h'; simpa using h'))
    exact hns K (quadBasis (d : F)) (quadBasis_zero _) (quadBasis_one_sq _) α β rfl rfl hα0 hβ0

/-! ### Every quaternary form is similar to a model -/

/-- **A diagonal quaternary form is similar to a model**: for $e_i\ne0$ and $c_i = e_0e_{i+1}$,
$\tau(\langle e_0,e_1,e_2,e_3\rangle) = 2\iff\tau(q_{\mathrm{ns}}(-c_1c_2, -c_0c_2, c_0c_1c_2)) = 2$. -/
theorem tamagawaNumberTwoAdelic_diag_iff (e : Fin 4 → 𝓞 F) (he : ∀ i, e i ≠ 0)
    (hQe : (QuadForm.diag e).Nondegenerate)
    (hQ' : (qNS (-(e 0 * e 3 * (e 0 * e 2))) (-(e 0 * e 3 * (e 0 * e 1)))
      (e 0 * e 1 * (e 0 * e 2) * (e 0 * e 3))).Nondegenerate) :
    TamagawaNumberTwoAdelic (qNS (-(e 0 * e 3 * (e 0 * e 2))) (-(e 0 * e 3 * (e 0 * e 1)))
      (e 0 * e 1 * (e 0 * e 2) * (e 0 * e 3))) hQ' ↔ TamagawaNumberTwoAdelic (QuadForm.diag e) hQe := by
  set c : Fin 3 → 𝓞 F := ![e 0 * e 1, e 0 * e 2, e 0 * e 3]
  have hc : ∀ i, c i ≠ 0 := fun i => by
    fin_cases i <;> simp [c, he 0, he 1, he 2, he 3]
  set P : QuadForm (𝓞 F) 4 := QuadForm.diag ![1, c 0, c 1, c 2]
  have hP : P.Nondegenerate := nondegenerate_diag_ringOfIntegers fun i => by
    fin_cases i <;> simp [hc 0, hc 1, hc 2]
  -- step 1: `e₀ ⟨e⟩ = P ∘ diag(e₀, 1, 1, 1)`
  have hG1 : (diagonal ![e 0, 1, 1, 1]).det ≠ 0 := by
    rw [det_diagonal, Fin.prod_univ_four]; simp [he 0]
  have h1 : simForm P 1 (diagonal ![e 0, 1, 1, 1]) = simForm (QuadForm.diag e) (e 0) 1 := by
    rw [simForm_one, diag_compMat_diagonal]
    ext i j
    simp only [simForm, QuadForm.smul_coeff, QuadForm.compMat_one]
    by_cases hij : i = j
    · subst hij; fin_cases i <;> simp [QuadForm.diag, c]
    · simp [QuadForm.diag, diagonal_apply_ne _ hij]
  have hG0 : (1 : Matrix (Fin 4) (Fin 4) (𝓞 F)).det ≠ 0 := by rw [det_one]; exact one_ne_zero
  have s1 := tamagawaNumberTwoAdelic_simForm_iff (by norm_num) (by norm_num) hQe (he 0) hG0 rfl
    (nondegenerate_simForm hQe (he 0) hG0)
  have s2 := tamagawaNumberTwoAdelic_simForm_iff (by norm_num) (by norm_num) hP one_ne_zero hG1 h1
    (nondegenerate_simForm hQe (he 0) hG0)
  -- step 2: `P ∘ diag(1, c₁c₂, c₀c₂, c₀c₁c₂) = qNS a b d`
  have hG2 : (diagonal ![1, c 1 * c 2, c 0 * c 2, c 0 * c 1 * c 2]).det ≠ 0 := by
    rw [det_diagonal, Fin.prod_univ_four]; simp [hc 0, hc 1, hc 2]
  have h2 : simForm P 1 (diagonal ![1, c 1 * c 2, c 0 * c 2, c 0 * c 1 * c 2]) =
      qNS (-(e 0 * e 3 * (e 0 * e 2))) (-(e 0 * e 3 * (e 0 * e 1))) (e 0 * e 1 * (e 0 * e 2) * (e 0 * e 3)) := by
    rw [simForm_one, diag_compMat_diagonal, qNS]
    congr 1
    funext i
    fin_cases i <;> simp [c] <;> ring
  have s3 := tamagawaNumberTwoAdelic_simForm_iff (by norm_num) (by norm_num) hP one_ne_zero hG2 h2 hQ'
  rw [s3, ← s2, s1]

/-- **Every nondegenerate quaternary form is similar to a model**: there are $G$ with $\det G\ne0$ and $e_i\ne0$ with
$Q_0\circ G = \langle e_0,\dots,e_3\rangle$, and then $\tau(Q_0) = 2\iff\tau(q_{\mathrm{ns}}(-c_1c_2,-c_0c_2,c_0c_1c_2)) = 2$, $c_i = e_0e_{i+1}$. -/
theorem exists_tamagawaNumberTwoAdelic_iff_qNS (Q₀ : QuadForm (𝓞 F) 4) (hQ : Q₀.Nondegenerate) :
    ∃ G : Matrix (Fin 4) (Fin 4) (𝓞 F), G.det ≠ 0 ∧ ∃ e : Fin 4 → 𝓞 F, (∀ i, e i ≠ 0) ∧
      Q₀.compMat G = QuadForm.diag e ∧
      ∃ hQ' : (qNS (-(e 0 * e 3 * (e 0 * e 2))) (-(e 0 * e 3 * (e 0 * e 1)))
        (e 0 * e 1 * (e 0 * e 2) * (e 0 * e 3))).Nondegenerate,
        (TamagawaNumberTwoAdelic (qNS (-(e 0 * e 3 * (e 0 * e 2))) (-(e 0 * e 3 * (e 0 * e 1)))
          (e 0 * e 1 * (e 0 * e 2) * (e 0 * e 3))) hQ' ↔ TamagawaNumberTwoAdelic Q₀ hQ) := by
  obtain ⟨G, hG, e, he, hGe⟩ := LatChange.exists_compMat_eq_diag Q₀ hQ
  have hD : simForm Q₀ 1 G = QuadForm.diag e := by rw [simForm_one, hGe]
  have hQe : (QuadForm.diag e).Nondegenerate := hD ▸ nondegenerate_simForm hQ one_ne_zero hG
  have hQ' : (qNS (-(e 0 * e 3 * (e 0 * e 2))) (-(e 0 * e 3 * (e 0 * e 1)))
      (e 0 * e 1 * (e 0 * e 2) * (e 0 * e 3))).Nondegenerate :=
    nondegenerate_diag_ringOfIntegers fun i => by
      fin_cases i <;> simp [he 0, he 1, he 2, he 3]
  refine ⟨G, hG, e, he, hGe, hQ', ?_⟩
  rw [tamagawaNumberTwoAdelic_diag_iff e he hQe hQ',
    tamagawaNumberTwoAdelic_simForm_iff (by norm_num) (by norm_num) hQ one_ne_zero hG hD hQe]

/-! ### The headline -/

/-- **Weil's adelic $\tau(SO(V)) = 2$ for every quaternary quadratic space over every number field** (Weil 1982, Thm 3.7.1,
$m = 4$): every nondegenerate $Q_0$ over $\mathcal O_F$, every signature, isotropic or not (the quaternion algebras may be
split), any class number, **conditional only on the named input `GnatTamagawaComparison F`** (Weil's Thm 2.3.1 for
$G^\natural\to SO(V)$ on the two models). The covolume $2$ of $G^\natural/\mathbb G_m$ is proved (`covolume_gnatSq`,
`covolume_gnatBC`, every quaternion algebra). -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), pp. 63-65 [unverified page]; Thm 2.3.1"]
theorem tamagawaNumberTwoAdelic_quaternary (hC : GnatTamagawaComparison F) (Q₀ : QuadForm (𝓞 F) 4)
    (hQ : Q₀.Nondegenerate) : TamagawaNumberTwoAdelic Q₀ hQ := by
  obtain ⟨G, hG, e, he, -, hQ', hiff⟩ := exists_tamagawaNumberTwoAdelic_iff_qNS Q₀ hQ
  have ha0 : -(e 0 * e 3 * (e 0 * e 2)) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (he 0) (he 3)) (mul_ne_zero (he 0) (he 2)))
  have hb0 : -(e 0 * e 3 * (e 0 * e 1)) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (he 0) (he 3)) (mul_ne_zero (he 0) (he 1)))
  have hd0 : e 0 * e 1 * (e 0 * e 2) * (e 0 * e 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (he 0) (he 1)) (mul_ne_zero (he 0) (he 2))) (mul_ne_zero (he 0) (he 3))
  exact hiff.1 (tamagawaNumberTwoAdelic_qNS_of ha0 hb0 hd0 hQ' (fun hQs => tamagawaNumberTwoAdelic_qSq hC ha0 hb0 hQs)
    (fun K _ _ _ bK hb₀ hb₁ α β hα hβ hα0 hβ0 => tamagawaNumberTwoAdelic_qNS hC bK hb₀ hb₁ hα hβ hα0 hβ0 hQ'))

/-! ### The unconditional definite case -/

/-- **$Q_0$ is definite at every real place**: at each real place $w$ of $F$, the values $Q_0(x)$, $x\in F^n\setminus0$, all have
the same strict sign (positive definite at some places and negative definite at others is allowed; nothing is required at
the complex or finite places). Since $F^n$ is dense in $\mathbb R^n$ under $w$, this is the same as $Q_0$ being positive or negative
definite over $\mathbb R$ at $w$. -/
@[kb "omeara1963" "§61A, p. 154 (definite at a real spot)"]
def IsDefiniteAtRealPlaces {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) : Prop :=
  ∀ (w : InfinitePlace F) (hw : w.IsReal) (x y : Fin n → F), x ≠ 0 → y ≠ 0 →
    0 < embedding_of_isReal hw ((Q₀.map (algebraMap (𝓞 F) F)).eval x) *
      embedding_of_isReal hw ((Q₀.map (algebraMap (𝓞 F) F)).eval y)

/-- Over a totally real field, $x$ is totally positive as soon as it is positive at every real place. -/
theorem isTotallyPos_of_forall_isReal [IsTotallyReal F] {x : F}
    (h : ∀ (w : InfinitePlace F) (hw : w.IsReal), 0 < embedding_of_isReal hw x) : IsTotallyPos x := by
  intro σ
  set φ : F →+* ℂ := σ.toRingHom
  have hφ : ComplexEmbedding.IsReal φ := NumberField.IsTotallyReal.complexEmbedding_isReal φ
  have hw : (InfinitePlace.mk φ).IsReal := IsTotallyReal.isReal _
  have h2 : (σ x : ℂ) = ((embedding_of_isReal hw x : ℝ) : ℂ) := by
    rw [embedding_of_isReal_apply, embedding_mk_eq_of_isReal hφ]; rfl
  rw [h2]; exact_mod_cast h _ hw

/-- If $Q_0\circ G = \langle e\rangle$ with $\det G\ne0$ and $Q_0$ is definite at every real place, then $e_0e_i$ is totally
positive. -/
theorem isTotallyPos_mul_of_isDefiniteAtRealPlaces [IsTotallyReal F] {Q₀ : QuadForm (𝓞 F) 4}
    (hdef : IsDefiniteAtRealPlaces Q₀) {G : Matrix (Fin 4) (Fin 4) (𝓞 F)} (hG : G.det ≠ 0) {e : Fin 4 → 𝓞 F}
    (hGe : Q₀.compMat G = QuadForm.diag e) (i : Fin 4) : IsTotallyPos ((e 0 : F) * (e i : F)) := by
  set G' := G.map (algebraMap (𝓞 F) F)
  have hG' : G'.det ≠ 0 := det_map_algebraMap_ne_zero_gnat hG
  have hval : ∀ j : Fin 4, (Q₀.map (algebraMap (𝓞 F) F)).eval (G' *ᵥ Pi.single j 1) = (e j : F) := by
    intro j
    rw [← QuadForm.eval_compMat, QuadForm.map_compMat, hGe, LatChange.eval_single']
    simp [QuadForm.map, QuadForm.diag]
  have hne : ∀ j : Fin 4, G' *ᵥ Pi.single j 1 ≠ 0 := fun j h =>
    (Pi.single_ne_zero_iff.2 one_ne_zero) (Matrix.eq_zero_of_mulVec_eq_zero hG' h)
  refine isTotallyPos_of_forall_isReal fun w hw => ?_
  have := hdef w hw _ _ (hne 0) (hne i)
  rw [hval, hval] at this
  rwa [map_mul]

/-- **Weil's adelic $\tau(SO(V)) = 2$ for every quaternary form definite at every real place, over every totally real field
— unconditional** (any class number; positive definite at some real places and negative definite at others is allowed;
no condition at the finite places, where $V$ may be isotropic). The comparison used is the proved
`gnatTamagawaComparisonDef`. -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), pp. 63-65 [unverified page]; Thm 2.3.1"]
theorem tamagawaNumberTwoAdelic_quaternary_definite [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) 4)
    (hQ : Q₀.Nondegenerate) (hdef : IsDefiniteAtRealPlaces Q₀) : TamagawaNumberTwoAdelic Q₀ hQ := by
  obtain ⟨G, hG, e, he, hGe, hQ', hiff⟩ := exists_tamagawaNumberTwoAdelic_iff_qNS Q₀ hQ
  have hp := isTotallyPos_mul_of_isDefiniteAtRealPlaces hdef hG hGe
  have hna : IsTotallyPos (-(((-(e 0 * e 3 * (e 0 * e 2))) : 𝓞 F) : F)) := by
    have : (-(((-(e 0 * e 3 * (e 0 * e 2))) : 𝓞 F) : F)) = ((e 0 : F) * e 3) * ((e 0 : F) * e 2) := by
      push_cast; ring
    rw [this]; exact LatChange.isTotallyPos_mul (hp 3) (hp 2)
  have hnb : IsTotallyPos (-(((-(e 0 * e 3 * (e 0 * e 1))) : 𝓞 F) : F)) := by
    have : (-(((-(e 0 * e 3 * (e 0 * e 1))) : 𝓞 F) : F)) = ((e 0 : F) * e 3) * ((e 0 : F) * e 1) := by
      push_cast; ring
    rw [this]; exact LatChange.isTotallyPos_mul (hp 3) (hp 1)
  have hdpos : IsTotallyPos (((e 0 * e 1 * (e 0 * e 2) * (e 0 * e 3)) : 𝓞 F) : F) := by
    have : (((e 0 * e 1 * (e 0 * e 2) * (e 0 * e 3)) : 𝓞 F) : F) =
        ((e 0 : F) * e 1) * ((e 0 : F) * e 2) * ((e 0 : F) * e 3) := by push_cast; ring
    rw [this]; exact LatChange.isTotallyPos_mul (LatChange.isTotallyPos_mul (hp 1) (hp 2)) (hp 3)
  have ha0 : -(e 0 * e 3 * (e 0 * e 2)) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (he 0) (he 3)) (mul_ne_zero (he 0) (he 2)))
  have hb0 : -(e 0 * e 3 * (e 0 * e 1)) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (he 0) (he 3)) (mul_ne_zero (he 0) (he 1)))
  have hd0 : e 0 * e 1 * (e 0 * e 2) * (e 0 * e 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (he 0) (he 1)) (mul_ne_zero (he 0) (he 2))) (mul_ne_zero (he 0) (he 3))
  exact hiff.1 (tamagawaNumberTwoAdelic_qNS_of ha0 hb0 hd0 hQ'
    (fun hQs => tamagawaNumberTwoAdelic_qSq_def (gnatTamagawaComparisonDef F) ha0 hb0 hna hnb hQs)
    (fun K _ _ _ bK hb₀ hb₁ α β hα hβ hα0 hβ0 => tamagawaNumberTwoAdelic_qNS_def (gnatTamagawaComparisonDef F)
      bK hb₀ hb₁ hα hβ hα0 hβ0 hna hnb hdpos hQ'))

end QuadFormsKB.Tamagawa.Measure.Weil
