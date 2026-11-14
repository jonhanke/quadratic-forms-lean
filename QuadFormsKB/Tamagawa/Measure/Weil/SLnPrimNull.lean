import QuadFormsKB.Tamagawa.Measure.Weil.SLnPrim

/-!
# Almost every vector of $\mathbb A_F^n$ is primitive

$F$ a number field, $n = k + 2$. **`muAddVec_compl_primSetN`**: the primitive vectors `primSetN F k` (the image of
$g\mapsto ge_0$ on $\mathrm{SL}_n(\mathbb A_F)$, `SLnPrim.lean`) have full measure in $\mathbb A_F^n$.

*Proof.* A vector which is not primitive either vanishes at some place (then its coordinate $0$ vanishes there: a
countable union of null sets, as for $n = 2$), or its first two coordinates fail to be primitive at infinitely many
places: as every coordinate is integral at almost all places, primitivity of $(y_0, y_1)$ at $v$ implies primitivity of
$y$ at $v$. The latter set is the preimage, under the projection to the first two coordinates, of the null set of
`SL2Prim.lean` (Borel–Cantelli with $\sum_vN(v)^{-2}<\infty$); splitting $\mathbb A^n = \mathbb A^2\times\mathbb A^k$
(`measurePreserving_sumPiEquivProdPi`) it has measure $0\cdot\mu(\mathbb A^k) = 0$.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding
open scoped ENNReal NNReal Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil.SLn

noncomputable section

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

local notation "AF" => FiniteAdeleRing (𝓞 F) F

theorem muAddVec_coord_null (i : Fin (k + 2)) {Z : Set (Adeles F)} (hZ : muAdd F Z = 0) :
    muAddVec F (Fin (k + 2)) {y | y i ∈ Z} = 0 :=
  Measure.pi_eval_preimage_null (fun _ => muAdd F) hZ

/-- Primitivity of the first two coordinates (in the sense of `SL2Section.lean`) and integrality of all coordinates
give primitivity (`IsPrimN`). -/
theorem isPrimN_of_isPrim {v : HeightOneSpectrum (𝓞 F)} {z : Fin (k + 2) → v.adicCompletion F}
    (h2 : IsPrim (valV v) (z 0) (z 1)) (hint : ∀ j, z j ∈ v.adicCompletionIntegers F) :
    IsPrimN (finO v) z := by
  refine ⟨hint, ?_⟩
  obtain ⟨-, -, h⟩ := h2
  rcases h with ⟨h0, hinv⟩ | ⟨h0, hinv⟩
  · exact ⟨0, h0, hinv⟩
  · exact ⟨1, h0, hinv⟩

/-- The splitting $\mathrm{Fin}\,2\oplus\mathrm{Fin}\,k\simeq\mathrm{Fin}(k+2)$. -/
def splitE (k : ℕ) : Fin 2 ⊕ Fin k ≃ Fin (k + 2) := finSumFinEquiv.trans (finCongr (Nat.add_comm 2 k))

theorem splitE_inl_zero : splitE k (Sum.inl 0) = 0 := by ext; simp [splitE]
theorem splitE_inl_one : splitE k (Sum.inl 1) = 1 := by ext; simp [splitE]

/-- The preimage of a null set of $\mathbb A^2$ under $y\mapsto(y_0, y_1)$ is null. -/
theorem muAddVec_pair_null {Z : Set (AdeleSpace F (Fin 2))} (hZ : muAddVec F (Fin 2) Z = 0) :
    muAddVec F (Fin (k + 2)) {y | (fun i : Fin 2 => y (splitE k (Sum.inl i))) ∈ Z} = 0 := by
  set P := MeasurableEquiv.piCongrLeft (fun _ : Fin (k + 2) => Adeles F) (splitE k)
  have hP : MeasurePreserving P (Measure.pi fun _ : Fin 2 ⊕ Fin k => muAdd F) (muAddVec F (Fin (k + 2))) :=
    measurePreserving_piCongrLeft (fun _ : Fin (k + 2) => muAdd F) (splitE k)
  set Q := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin k => Adeles F)
  have hQ : MeasurePreserving Q (Measure.pi fun _ : Fin 2 ⊕ Fin k => muAdd F)
      ((Measure.pi fun _ : Fin 2 => muAdd F).prod (Measure.pi fun _ : Fin k => muAdd F)) :=
    measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin k => muAdd F)
  have hpre : P ⁻¹' {y | (fun i : Fin 2 => y (splitE k (Sum.inl i))) ∈ Z} = Q ⁻¹' (Z ×ˢ Set.univ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true]
    have : (fun i : Fin 2 => P x (splitE k (Sum.inl i))) = (Q x).1 := by
      funext i
      simp [P, Q, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply,
        MeasurableEquiv.sumPiEquivProdPi]
    rw [this]
  rw [← hP.measure_preimage_equiv, hpre, hQ.measure_preimage_equiv, Measure.prod_prod]
  have : (Measure.pi fun _ : Fin 2 => muAdd F) Z = 0 := hZ
  rw [this, zero_mul]

/-- **Almost every vector of $\mathbb A_F^n$ is primitive**: `primSetN F k` is conull for the self-dual measure. -/
@[kb "weil1982" "§2.3, p. 21 (convergence factors; λ_v = 1 for SL_n since ∏(1 − N(v)⁻ⁿ) converges) [unverified page]"]
theorem muAddVec_compl_primSetN : muAddVec F (Fin (k + 2)) (primSetN F k)ᶜ = 0 := by
  set S4 : Set (AdeleSpace F (Fin (k + 2))) :=
    {y | (fun i : Fin 2 => y (splitE k (Sum.inl i))) ∈ boxSet Set.univ nonPrimFin}
  have hcov : (primSetN F k)ᶜ ⊆ (⋃ w, {y : AdeleSpace F (Fin (k + 2)) | y 0 ∈ {a : Adeles F | a.1 ∈
        {x : mixedSpace F | x.1 w = 0}}}) ∪
      (⋃ w, {y : AdeleSpace F (Fin (k + 2)) | y 0 ∈ {a : Adeles F | a.1 ∈ {x : mixedSpace F | x.2 w = 0}}}) ∪
      (⋃ v, {y : AdeleSpace F (Fin (k + 2)) | y 0 ∈ {a : Adeles F | a.2 ∈ {x : AF | x v = 0}}}) ∪
      (⋃ w, {y : AdeleSpace F (Fin (k + 2)) | y 1 ∈ {a : Adeles F | a.1 ∈
        {x : mixedSpace F | x.1 w = 0}}}) ∪
      (⋃ w, {y : AdeleSpace F (Fin (k + 2)) | y 1 ∈ {a : Adeles F | a.1 ∈ {x : mixedSpace F | x.2 w = 0}}}) ∪
      (⋃ v, {y : AdeleSpace F (Fin (k + 2)) | y 1 ∈ {a : Adeles F | a.2 ∈ {x : AF | x v = 0}}}) ∪ S4 := by
    intro y hy
    by_contra hno
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists] at hno
    obtain ⟨⟨⟨⟨⟨⟨hR0, hC0⟩, hV0⟩, hR1⟩, hC1⟩, hV1⟩, h4⟩ := hno
    apply hy
    refine ⟨fun w h => hR0 w (congrFun h 0), fun w h => hC0 w (congrFun h 0),
      fun v h => hV0 v (congrFun h 0), ?_⟩
    -- eventually primitive
    have hprim : ∀ᶠ v in cofinite, IsPrim (valV v) ((y 0).2 v) ((y 1).2 v) := by
      by_contra hn
      apply h4
      show (fun i : Fin 2 => y (splitE k (Sum.inl i))) ∈ boxSet Set.univ nonPrimFin
      rw [mem_boxSet]
      refine ⟨Set.mem_univ _, ?_⟩
      show ¬ ∀ᶠ v in cofinite, IsPrim (valV v) ((y (splitE k (Sum.inl 0))).2 v) ((y (splitE k (Sum.inl 1))).2 v)
      rw [splitE_inl_zero, splitE_inl_one]
      exact hn
    have hint : ∀ᶠ v in cofinite, ∀ j, (y j).2 v ∈ v.adicCompletionIntegers F := by
      simp only [Filter.eventually_all]
      exact fun j => (y j).2.2
    filter_upwards [hprim, hint] with v hv hiv
    exact isPrimN_of_isPrim hv hiv
  refine measure_mono_null hcov (measure_union_null (measure_union_null (measure_union_null
    (measure_union_null (measure_union_null (measure_union_null ?_ ?_) ?_) ?_) ?_) ?_) ?_)
  · exact measure_iUnion_null fun w => muAddVec_coord_null 0 (muAdd_fst_null (selfDualInf_real_eq_zero w))
  · exact measure_iUnion_null fun w => muAddVec_coord_null 0 (muAdd_fst_null (selfDualInf_complex_eq_zero w))
  · exact measure_iUnion_null fun v => muAddVec_coord_null 0 (muAdd_snd_null (muFin_eval_eq_zero v))
  · exact measure_iUnion_null fun w => muAddVec_coord_null 1 (muAdd_fst_null (selfDualInf_real_eq_zero w))
  · exact measure_iUnion_null fun w => muAddVec_coord_null 1 (muAdd_fst_null (selfDualInf_complex_eq_zero w))
  · exact measure_iUnion_null fun v => muAddVec_coord_null 1 (muAdd_snd_null (muFin_eval_eq_zero v))
  · exact muAddVec_pair_null (by rw [muAddVec_boxSet, muFinVec_nonPrimFin, mul_zero])

end

end QuadFormsKB.Tamagawa.Measure.Weil.SLn
