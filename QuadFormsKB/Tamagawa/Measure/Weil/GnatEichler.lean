/-
# Eichler's norm theorem for every quaternion algebra, and the reduced-norm images of $G^\natural$
Over a number field $F$ (any degree, any signature):
* `representsIn_diag4`: Hasse–Minkowski for $\langle 1, e_0, e_1, e_2\rangle$ — it represents $c \ne 0$ over $F$ as soon as
  $c > 0$ at the real places where the form is positive definite (finite places: rank-5 isotropy,
  `localRankFiveIsotropic`; real places: an indefinite form is universal; complex places: squares).
* **`eichler_norm_theorem_general`**: $\operatorname{nrd}((a,b)_F^\times) = \{c \in F^\times : c > 0$ at the real places
  ramified in $D\}$ — `eichler_norm_theorem'` without the totally definite hypothesis.
* **`Gnat.exists_Gnat_nrdK_eq_iff`**: $\operatorname{nrd}(G^\natural(F)) = \{c \in F^\times : c > 0$ at the real $w$ with
  $a, b <_w 0 <_w d\}$ (any $d$, square or not). The proof needs no field $F(\sqrt d)$:
  the values of $\operatorname{nrd}|_{V_0} = \langle 1,-ad,-bd,abd\rangle$ are reduced norms of elements of $V_0 \cap G^\natural$.
* `Gnat.exists_Gnat_nrdK_eq_finite`: $\operatorname{nrd}(G^\natural(F_v)) = F_v^\times$ at every finite $v$.
* `exists_approx_real`, `exists_signs`: weak approximation at the real places (Mathlib's
  `InfiniteAdeleRing.denseRange_algebraMap`); signs at the real places can be prescribed by an element of $F^\times$.

Sources: Eichler 1938; Vignéras 1980, Ch. III, Thm. 4.1 [unverified]; Voight 2021, Thm. 14.7.4 [unverified];
Weil 1982, §3.3, Lemma 3.3.2 (uses Eichler) [unverified page].
-/
import QuadFormsKB.Tamagawa.LocalRankFive
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSO4

open Quaternion NumberField IsDedekindDomain
open scoped QuadraticAlgebra

noncomputable section

namespace QuadFormsKB.Quat

variable {F : Type} [Field F] [NumberField F]

/-! ### Diagonal quaternary forms `⟨1, e₀, e₁, e₂⟩` over a number field -/

/-- The form `⟨1, e₀, e₁, e₂⟩`. -/
def diag4 (e : Fin 3 → F) : QuadForm F 4 := QuadForm.diag ![1, e 0, e 1, e 2]

/-- `c` is positive at every real place where `⟨1, e₀, e₁, e₂⟩` is positive definite. -/
def PosWhereDefinite (e : Fin 3 → F) (c : F) : Prop :=
  ∀ (w : InfinitePlace F) (hw : w.IsReal),
    (∀ i, 0 < InfinitePlace.embedding_of_isReal hw (e i)) → 0 < InfinitePlace.embedding_of_isReal hw c

theorem evalIn_diag4 (K : Type*) [Field K] [Algebra F K] (e : Fin 3 → F) (v : Fin 4 → K) :
    (diag4 e).evalIn K v = v 0 ^ 2 + algebraMap F K (e 0) * v 1 ^ 2 + algebraMap F K (e 1) * v 2 ^ 2 +
      algebraMap F K (e 2) * v 3 ^ 2 := by
  rw [diag4, QuadForm.evalIn_diag, Fin.sum_univ_four]
  simp

omit [NumberField F] in
theorem algebraMap_completion_real {w : InfinitePlace F} (hw : w.IsReal) (y : F) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap F w.Completion y) =
      InfinitePlace.embedding_of_isReal hw y := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfinitePlace.Completion.algebraMap_apply]
  exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw _

/-- The real-place step: `⟨1, e₀, e₁, e₂⟩` represents `c ≠ 0` over `ℝ` if `c > 0` or some `eᵢ < 0`. -/
theorem representsIn_diag4_real (e : Fin 3 → F) (he : ∀ i, e i ≠ 0) {c : F} (hc : c ≠ 0)
    {w : InfinitePlace F} (hw : w.IsReal)
    (hpos : (∀ i, 0 < InfinitePlace.embedding_of_isReal hw (e i)) → 0 < InfinitePlace.embedding_of_isReal hw c) :
    (diag4 e).RepresentsIn w.Completion c := by
  set σ := InfinitePlace.embedding_of_isReal hw
  set E := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hE : ∀ y : F, E (algebraMap F w.Completion y) = σ y := algebraMap_completion_real hw
  -- a real solution
  obtain ⟨r0, r1, r2, r3, hr⟩ : ∃ r0 r1 r2 r3 : ℝ,
      r0 ^ 2 + σ (e 0) * r1 ^ 2 + σ (e 1) * r2 ^ 2 + σ (e 2) * r3 ^ 2 = σ c := by
    have hσc : σ c ≠ 0 := (map_ne_zero σ).2 hc
    by_cases hp : 0 < σ c
    · exact ⟨Real.sqrt (σ c), 0, 0, 0, by simp [Real.sq_sqrt hp.le]⟩
    · have hneg : σ c < 0 := lt_of_le_of_ne (not_lt.1 hp) hσc
      have : ∃ i, σ (e i) < 0 := by
        by_contra h
        push Not at h
        exact hp (hpos fun i => lt_of_le_of_ne (h i) (Ne.symm ((map_ne_zero σ).2 (he i))))
      obtain ⟨i, hi⟩ := this
      have hq : 0 ≤ σ c / σ (e i) := div_nonneg_of_nonpos hneg.le hi.le
      have hne : σ (e i) ≠ 0 := hi.ne
      fin_cases i
      · have hq' : 0 ≤ σ c / σ (e 0) := hq
        have hne' : σ (e 0) ≠ 0 := hne
        exact ⟨0, Real.sqrt (σ c / σ (e 0)), 0, 0, by rw [Real.sq_sqrt hq']; field_simp; ring⟩
      · have hq' : 0 ≤ σ c / σ (e 1) := hq
        have hne' : σ (e 1) ≠ 0 := hne
        exact ⟨0, 0, Real.sqrt (σ c / σ (e 1)), 0, by rw [Real.sq_sqrt hq']; field_simp; ring⟩
      · have hq' : 0 ≤ σ c / σ (e 2) := hq
        have hne' : σ (e 2) ≠ 0 := hne
        exact ⟨0, 0, 0, Real.sqrt (σ c / σ (e 2)), by rw [Real.sq_sqrt hq']; field_simp; ring⟩
  refine ⟨![E.symm r0, E.symm r1, E.symm r2, E.symm r3], ?_⟩
  apply E.injective
  rw [evalIn_diag4]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, hE, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  exact hr

/-- The complex-place step: everything is a square. -/
theorem representsIn_diag4_complex (e : Fin 3 → F) (c : F) {w : InfinitePlace F} (hw : w.IsComplex) :
    (diag4 e).RepresentsIn w.Completion c := by
  set E := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (E (algebraMap F w.Completion c)) (n := 2) (by norm_num)
  refine ⟨![E.symm s, 0, 0, 0], ?_⟩
  rw [evalIn_diag4]
  apply E.injective
  simp [hs]

/-- The finite-place step: rank-4 forms over `F_v` are universal (rank-5 forms are isotropic). -/
theorem representsIn_diag4_finite (e : Fin 3 → F) (he : ∀ i, e i ≠ 0) {c : F} (hc : c ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) : (diag4 e).RepresentsIn (v.adicCompletion F) c := by
  have hQ : (diag4 e).Nondegenerate := by
    refine QuadForm.nondegenerate_diag fun i => ?_
    fin_cases i <;> simp [he]
  have hc' : ∀ i, (![-c] : Fin 1 → F) i ≠ 0 := fun i => by
    simpa [Subsingleton.elim i 0] using hc
  have hR := QuadForm.nondegenerate_orthSum hQ (QuadForm.nondegenerate_diag hc')
  rw [QuadForm.representsIn_iff_isotropicIn_orthSum (v.adicCompletion F) hQ c]
  set R := QuadForm.orthSum (diag4 e) (QuadForm.diag ![-c])
  have hRv : (R.map (algebraMap F (v.adicCompletion F))).Nondegenerate := by
    unfold QuadForm.Nondegenerate
    have : (R.map (algebraMap F (v.adicCompletion F))).hessian = R.hessian.map (algebraMap F _) := by
      simp [QuadForm.hessian, QuadForm.map, Matrix.transpose_map, Matrix.map_add]
    rw [this, show (R.hessian.map (algebraMap F (v.adicCompletion F))).det = algebraMap F _ R.hessian.det from
      (RingHom.map_det _ _).symm]
    exact (map_ne_zero _).2 hR
  obtain ⟨y, hy0, hy⟩ := (localRankFiveIsotropic F).isotropic v _ hRv
  refine ⟨y, hy0, ?_⟩
  rw [← hy]
  simp [QuadForm.evalIn, QuadForm.map]

/-- **Hasse–Minkowski for `⟨1, e₀, e₁, e₂⟩`:** it represents `c ≠ 0` over `F` iff (only "if" is stated) `c` is
positive at the real places where the form is positive definite. -/
@[kb "omeara1963" "§66, 66:3, p. 189"]
theorem representsIn_diag4 (e : Fin 3 → F) (he : ∀ i, e i ≠ 0) {c : F} (hc : c ≠ 0)
    (hpos : PosWhereDefinite e c) : (diag4 e).RepresentsIn F c := by
  have hQ : (diag4 e).Nondegenerate := by
    refine QuadForm.nondegenerate_diag fun i => ?_
    fin_cases i <;> simp [he]
  rw [represents_iff_everywhere_nf _ hQ c hc]
  intro v
  cases v with
  | infinite w =>
    rcases w.isReal_or_isComplex with hw | hw
    · exact representsIn_diag4_real e he hc hw (hpos w hw)
    · exact representsIn_diag4_complex e c hw
  | finite v => exact representsIn_diag4_finite e he hc v

/-! ### Eichler's norm theorem for every quaternion algebra over every number field -/

/-- `D = (a,b)_F` is **ramified at the real place `w`**: `σ_w(a) < 0` and `σ_w(b) < 0` (`D ⊗_w ℝ ≅ ℍ`). -/
def IsRamifiedReal (a b : F) (w : InfinitePlace F) (hw : w.IsReal) : Prop :=
  InfinitePlace.embedding_of_isReal hw a < 0 ∧ InfinitePlace.embedding_of_isReal hw b < 0

/-- At a real place where `a, b < 0`, the reduced norm of a nonzero quaternion is positive. -/
theorem pos_nrd_of_ramified {a b : F} {w : InfinitePlace F} {hw : w.IsReal} (hram : IsRamifiedReal a b w hw)
    {α : ℍ[F,a,b]} (hα : α ≠ 0) : 0 < InfinitePlace.embedding_of_isReal hw (nrd α) := by
  set σ := InfinitePlace.embedding_of_isReal hw
  obtain ⟨hσa, hσb⟩ := hram
  have hσ : σ (nrd α) = σ α.re ^ 2 + (-σ a) * σ α.imI ^ 2 + (-σ b) * σ α.imJ ^ 2 +
      (σ a * σ b) * σ α.imK ^ 2 := by
    simp only [nrd, map_add, map_sub, map_mul, map_pow]; ring
  rw [hσ]
  have h1 : 0 < -σ a := neg_pos.2 hσa
  have h2 : 0 < -σ b := neg_pos.2 hσb
  have h3 : 0 < σ a * σ b := mul_pos_of_neg_of_neg hσa hσb
  have t0 : 0 ≤ σ α.re ^ 2 := sq_nonneg _
  have t1 : 0 ≤ (-σ a) * σ α.imI ^ 2 := mul_nonneg h1.le (sq_nonneg _)
  have t2 : 0 ≤ (-σ b) * σ α.imJ ^ 2 := mul_nonneg h2.le (sq_nonneg _)
  have t3 : 0 ≤ (σ a * σ b) * σ α.imK ^ 2 := mul_nonneg h3.le (sq_nonneg _)
  by_contra hle
  push Not at hle
  have z0 : σ α.re ^ 2 = 0 := by linarith
  have z1 : (-σ a) * σ α.imI ^ 2 = 0 := by linarith
  have z2 : (-σ b) * σ α.imJ ^ 2 = 0 := by linarith
  have z3 : (σ a * σ b) * σ α.imK ^ 2 = 0 := by linarith
  have hz : ∀ t : F, σ t ^ 2 = 0 → t = 0 := fun t ht =>
    σ.injective (by rw [map_zero]; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ht)
  apply hα
  ext
  · exact hz _ z0
  · exact hz _ ((mul_eq_zero.1 z1).resolve_left h1.ne')
  · exact hz _ ((mul_eq_zero.1 z2).resolve_left h2.ne')
  · exact hz _ ((mul_eq_zero.1 z3).resolve_left h3.ne')

omit [NumberField F] in
theorem nrdForm_eq_diag4 (a b : F) : nrdForm a b = diag4 ![-a, -b, a * b] := by
  simp only [nrdForm, diag4]
  congr 1

/-- **Eichler's norm theorem, general form** (every quaternion algebra `D = (a,b)_F` over every number field `F`):
$$\operatorname{nrd}(D^\times) = \{c \in F^\times : \sigma_w(c) > 0 \text{ at every real place } w \text{ ramified in } D\}.$$
Same proof as the totally definite case (`eichler_norm_theorem'`): Hasse–Minkowski over `F`
(`represents_iff_everywhere_nf`) for `⟨1, −a, −b, ab⟩`, rank-5 isotropy at finite places (`localRankFiveIsotropic`),
and at a real place the form is indefinite unless `D` is ramified there. -/
@[kb "voight2021" "Thm. 14.7.4 [unverified]"]
theorem eichler_norm_theorem_general {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (c : F) :
    (∃ α : ℍ[F,a,b], IsUnit α ∧ nrd α = c) ↔
      c ≠ 0 ∧ ∀ (w : InfinitePlace F) (hw : w.IsReal), IsRamifiedReal a b w hw →
        0 < InfinitePlace.embedding_of_isReal hw c := by
  constructor
  · rintro ⟨α, hu, rfl⟩
    exact ⟨(isUnit_iff_nrd_ne_zero α).1 hu, fun w hw hram => pos_nrd_of_ramified hram hu.ne_zero⟩
  · rintro ⟨hc, hpos⟩
    have he : ∀ i, (![-a, -b, a * b] : Fin 3 → F) i ≠ 0 := fun i => by
      fin_cases i <;> simp [ha, hb]
    have hrep : (nrdForm a b).RepresentsIn F c := by
      rw [nrdForm_eq_diag4]
      refine representsIn_diag4 _ he hc fun w hw hdef => hpos w hw ?_
      have h0 := hdef 0
      have h1 := hdef 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, map_neg] at h0 h1
      exact ⟨neg_pos.1 h0, neg_pos.1 h1⟩
    obtain ⟨α, hα⟩ := (representsIn_nrdForm_iff c).1 hrep
    exact ⟨α, (isUnit_iff_nrd_ne_zero α).2 (hα ▸ hc), hα⟩

/-! ### Weak approximation at the real places -/

/-- **Weak approximation at the real places** (Mathlib's `InfiniteAdeleRing.denseRange_algebraMap`): any family of
real targets `r_w` at the real places is approximated by one `x ∈ F`. -/
@[kb "weil1982" "§2.1 [unverified]"]
theorem exists_approx_real (r : (w : InfinitePlace F) → w.IsReal → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x : F, ∀ (w : InfinitePlace F) (hw : w.IsReal),
      |InfinitePlace.embedding_of_isReal hw x - r w hw| < δ := by
  classical
  set U : Set (InfiniteAdeleRing F) := ⋂ (w : InfinitePlace F), ⋂ (hw : w.IsReal),
    (fun y : InfiniteAdeleRing F => InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (y w)) ⁻¹'
      Metric.ball (r w hw) δ
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun hw => ?_
    exact Metric.isOpen_ball.preimage
      ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous.comp (continuous_apply w))
  set z : InfiniteAdeleRing F := fun w => if hw : w.IsReal then
    (InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hw (r w hw)).choose else 0
  have hz : z ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_preimage, Metric.mem_ball]
    intro w hw
    simp only [z, dif_pos hw]
    rw [(InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hw (r w hw)).choose_spec, dist_self]
    exact hδ
  obtain ⟨x, hx⟩ := (InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open hU ⟨z, hz⟩
  refine ⟨x, fun w hw => ?_⟩
  simp only [U, Set.mem_iInter, Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hx
  have := hx w hw
  rwa [show InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((algebraMap F (InfiniteAdeleRing F) x) w) =
    InfinitePlace.embedding_of_isReal hw x from by
      rw [← algebraMap_completion_real hw x, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]; rfl] at this

/-- **Signs at the real places can be prescribed:** for every choice of signs there is `x ∈ F^×` with
`σ_w(x) > 0` exactly at the chosen real places `w`. -/
@[kb "weil1982" "§2.1 [unverified]"]
theorem exists_signs (P : (w : InfinitePlace F) → w.IsReal → Prop) :
    ∃ x : F, x ≠ 0 ∧ ∀ (w : InfinitePlace F) (hw : w.IsReal),
      (0 < InfinitePlace.embedding_of_isReal hw x ↔ P w hw) := by
  classical
  obtain ⟨x, hx⟩ := exists_approx_real (F := F) (fun w hw => if P w hw then 1 else -1) one_pos
  have hsign : ∀ (w : InfinitePlace F) (hw : w.IsReal),
      (0 < InfinitePlace.embedding_of_isReal hw x ↔ P w hw) := by
    intro w hw
    have h := hx w hw
    by_cases hP : P w hw
    · simp only [hP, if_true, abs_lt] at h
      exact ⟨fun _ => hP, fun _ => by linarith⟩
    · simp only [hP, if_false, abs_lt] at h
      exact ⟨fun h' => by linarith, fun h' => absurd h' hP⟩
  by_cases h0 : x = 0
  · refine ⟨1, one_ne_zero, fun w hw => ?_⟩
    exfalso
    have h := hx w hw
    rw [h0, map_zero, zero_sub, abs_neg] at h
    split_ifs at h <;> simp at h
  · exact ⟨x, h0, hsign⟩

/-! ### The global image of `nrd` on `G^♮`, and local images -/

namespace Gnat

omit [NumberField F] in
theorem V0Form_eq_diag4 (a b d : F) : V0Form a b d = diag4 ![-(a * d), -(b * d), a * b * d] := by
  simp only [V0Form, diag4]
  congr 1

/-- `E → ℝ`, `δ ↦ t`, along a real embedding `σ` with `t² = σ(d)`. -/
def evER (σ : F →+* ℝ) {d : F} (t : ℝ) (ht : t ^ 2 = σ d) : QE d →+* ℝ where
  toFun z := σ z.re + t * σ z.im
  map_one' := by simp
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, map_zero, zero_mul,
      add_zero]
    linear_combination (-(σ z.im * σ w.im)) * ht
  map_zero' := by simp
  map_add' z w := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]; ring

/-- **The global image of `nrd` on `G^♮`** (any `a, b, d ∈ F^×`, `d` a square or not):
$$\operatorname{nrd}(G^\natural(F)) = \{c \in F^\times : \sigma_w(c) > 0 \text{ at every real } w
\text{ with } \sigma_w(a), \sigma_w(b) < 0 < \sigma_w(d)\}.$$
These `w` are exactly the real places of `F` below the real places of `E` at which `D_E` is ramified. `⊇`: the
values of the quaternary form `nrd|_{V_0} = ⟨1, −ad, −bd, abd⟩` are reduced norms of elements of `V_0 ∩ G^♮`, and
Hasse–Minkowski (`representsIn_diag4`) gives every such `c`. `⊆`: at such a place `D_E ⊗ ℝ ≅ ℍ × ℍ`. This is
"Eichler for `D_E`" without passing to the field `k′ = F(√d)`. -/
@[kb "weil1982" "§3.3, Lemma 3.3.2 [unverified]"]
theorem exists_Gnat_nrdK_eq_iff {a b d : F} (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (c : F) :
    (∃ α ∈ Gnat a b d, nrdK (α : DE a b d) = c) ↔
      c ≠ 0 ∧ ∀ (w : InfinitePlace F) (hw : w.IsReal), IsRamifiedReal a b w hw →
        0 < InfinitePlace.embedding_of_isReal hw d → 0 < InfinitePlace.embedding_of_isReal hw c := by
  constructor
  · rintro ⟨α, hα, rfl⟩
    refine ⟨nrdK_ne_zero hα, fun w hw hram hdpos => ?_⟩
    set σ := InfinitePlace.embedding_of_isReal hw
    obtain ⟨hσa, hσb⟩ := hram
    set t := Real.sqrt (σ d)
    have ht : t ^ 2 = σ d := Real.sq_sqrt hdpos.le
    have key : σ (nrdK (α : DE a b d)) = evER σ t ht (nrdE (α : DE a b d)) := by
      rw [nrdE_eq_nrdK hα]; simp [evER]
    have hexp : evER σ t ht (nrdE (α : DE a b d)) =
        (evER σ t ht (α : DE a b d).re) ^ 2 + (-σ a) * (evER σ t ht (α : DE a b d).imI) ^ 2 +
          (-σ b) * (evER σ t ht (α : DE a b d).imJ) ^ 2 +
          (σ a * σ b) * (evER σ t ht (α : DE a b d).imK) ^ 2 := by
      have hA : ∀ r : F, evER σ t ht (algebraMap F (QE d) r) = σ r := fun r => by simp [evER]
      simp only [nrdE, map_add, map_sub, map_mul, map_pow, hA]; ring
    have hnn : 0 ≤ σ (nrdK (α : DE a b d)) := by
      rw [key, hexp]
      have h3 := mul_pos_of_neg_of_neg hσa hσb
      have t0 := sq_nonneg (evER σ t ht (α : DE a b d).re)
      have t1 := mul_nonneg (neg_pos.2 hσa).le (sq_nonneg (evER σ t ht (α : DE a b d).imI))
      have t2 := mul_nonneg (neg_pos.2 hσb).le (sq_nonneg (evER σ t ht (α : DE a b d).imJ))
      have t3 := mul_nonneg h3.le (sq_nonneg (evER σ t ht (α : DE a b d).imK))
      linarith
    exact lt_of_le_of_ne hnn (Ne.symm ((map_ne_zero σ).2 (nrdK_ne_zero hα)))
  · rintro ⟨hc, hpos⟩
    have he : ∀ i, (![-(a * d), -(b * d), a * b * d] : Fin 3 → F) i ≠ 0 := fun i => by
      fin_cases i <;> simp [ha, hb, hd]
    have hrep : (V0Form a b d).RepresentsIn F c := by
      rw [V0Form_eq_diag4]
      refine representsIn_diag4 _ he hc fun w hw hdef => ?_
      set σ := InfinitePlace.embedding_of_isReal hw
      have h0 : 0 < σ (-(a * d)) := hdef 0
      have h1 : 0 < σ (-(b * d)) := hdef 1
      have h2 : 0 < σ (a * b * d) := hdef 2
      simp only [map_neg, map_mul] at h0 h1 h2
      have hp : 0 < (σ a * σ d) * (σ b * σ d) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
      have hσd : 0 < σ d := by
        by_contra hle
        push Not at hle
        have : σ d * (σ a * σ b * σ d) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle h2.le
        nlinarith
      have hσa : σ a < 0 := by
        by_contra hle
        push Not at hle
        nlinarith
      have hσb : σ b < 0 := by
        by_contra hle
        push Not at hle
        nlinarith
      exact hpos w hw ⟨hσa, hσb⟩ hσd
    obtain ⟨v, hv⟩ := hrep
    have hv' : Q4 a b d v = c := by rw [← eval_V0Form]; exact hv
    refine ⟨unitOfNrd (emb v) c hc (by rw [nrdE_emb, hv']), unitOfNrd_mem _ _ _ _, ?_⟩
    exact nrdK_of_nrdE (by rw [coe_unitOfNrd, nrdE_emb, hv'])

/-- **Local image at a finite place: `nrd(G^♮(F_v)) = F_v^×`** (any `a, b, d`), already from `D_v^× ⊂ G^♮(F_v)`
and `exists_nrd_eq_finite'`. -/
@[kb "weil1982" "§3.3, Lemma 3.3.2 [unverified]"]
theorem exists_Gnat_nrdK_eq_finite {a b d : F} (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F))
    {c : v.adicCompletion F} (hc : c ≠ 0) :
    ∃ α ∈ Gnat (algebraMap F (v.adicCompletion F) a) (algebraMap F (v.adicCompletion F) b)
      (algebraMap F (v.adicCompletion F) d),
        nrdK (α : DE (algebraMap F (v.adicCompletion F) a) (algebraMap F (v.adicCompletion F) b)
          (algebraMap F (v.adicCompletion F) d)) = c := by
  obtain ⟨y, hy⟩ := exists_nrd_eq_finite' ha hb v hc
  have hu : IsUnit y := (isUnit_iff_nrd_ne_zero y).2 (hy ▸ hc)
  refine ⟨iotaUnit hu.unit, iotaUnit_mem _, ?_⟩
  rw [coe_iotaUnit, nrdK_of_nrdE (nrdE_iota _), IsUnit.unit_spec, hy]

end Gnat

end QuadFormsKB.Quat
