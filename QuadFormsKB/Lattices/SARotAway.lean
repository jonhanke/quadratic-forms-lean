/-
# Strong approximation for rotations away from $\{\infty, \mathfrak p\}$

**Layer:** as `Lattices/SARotations.lean`, with no conditions at one finite prime $\mathfrak p$.

**Defines** `RotApproxAt Q p`: `RotApprox Q` for finite sets $T \not\ni \mathfrak p$, with no integrality asked at
$\mathfrak p$.

**Proves** the versions of O'Meara 104:4 (steps 1a–1c) and of the bridge 104:5 away from $\mathfrak p$:
`pair_approxAt`, `list_approxAt`, `eqPair_approxAt`, `rotApproxAt_of_vecApproxAt_of_correction`,
`approx_of_rotApproxAt` (the proofs of `Lattices/SARotations.lean` with $T$ replaced by $T \setminus \{\mathfrak p\}$ where
needed). The ternary case and the input `StrongApproximationSpinAt F` are in `Lattices/SATernaryAway.lean`.
-/
import QuadFormsKB.Lattices.SAVectorsAway

open NumberField IsDedekindDomain Matrix WithZero Topology Filter
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **Strong approximation for rotations away from a prime $\mathfrak p$** (O'Meara 1973, 104:4 with
$S$ = all finite primes except $\mathfrak p$): as `RotApprox Q`, for finite $T \not\ni \mathfrak p$, with $\sigma \in O(\mathfrak o_\mathfrak q^n)$
asked only at the primes $\mathfrak q \notin T \cup \{\mathfrak p\}$. -/
def RotApproxAt (p : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ (T : Finset (HeightOneSpectrum (𝓞 F))), p ∉ T →
    ∀ (φ : ∀ v : HeightOneSpectrum (𝓞 F), orthGroup Q (v.adicCompletion F)),
    (∀ v ∈ T, φ v ∈ spinorKernel Q (v.adicCompletion F)) →
    ∀ U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Matrix (Fin n) (Fin n) (v.adicCompletion F)),
      (∀ v ∈ T, U v ∈ 𝓝 (omat (φ v))) →
      ∃ σ ∈ spinorKernel Q F, (∀ v ∈ T, omat (orthMap Q (v.adicCompletion F) σ) ∈ U v) ∧
        ∀ v ∉ T, v ≠ p → orthMap Q (v.adicCompletion F) σ ∈ stdStab Q v

/-- **The bridge 104:5 away from $\mathfrak p$:** `RotApproxAt Q p` gives $\gamma \in O'(V)$ with $\gamma^{-1}h$ stabilizing
$L_\mathfrak q$ at every $\mathfrak q \ne \mathfrak p$. -/
theorem approx_of_rotApproxAt {p : HeightOneSpectrum (𝓞 F)} (hR : RotApproxAt Q p) (L : Lat F n) (h : OAf Q)
    (hh : h ∈ spinorKernelAf Q) :
    ∃ γ : orthGroup Q F, γ ∈ spinorKernel Q F ∧ ∀ w, w ≠ p →
      locAct w ((((diagF Q γ)⁻¹ * h) w : orthGroup Q _) : GL (Fin n) _) (loc w L.1) = loc w L.1 := by
  classical
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, h v ∈ stdStab Q v ∧ loc v L.1 = std v :=
    h.2.and (loc_eventually_std L.2)
  set T : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.mp hev).toFinset.erase p
  have hT : ∀ v, v ∉ T → v ≠ p → h v ∈ stdStab Q v ∧ loc v L.1 = std v := by
    intro v hv hvp
    by_contra hc
    exact hv (Finset.mem_erase.mpr ⟨hvp, (Filter.eventually_cofinite.mp hev).mem_toFinset.mpr hc⟩)
  choose U hU hUσ using fun v : HeightOneSpectrum (𝓞 F) =>
    exists_mem_nhds_locAct_eq v ((h v : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F))
      (loc_isLattice v L.2)
  obtain ⟨σ, hσ, hσT, hσT'⟩ := hR T (Finset.notMem_erase p _) (fun v => h v) (fun v _ => hh v) U (fun v _ => hU v)
  refine ⟨σ, hσ, fun v hvp => ?_⟩
  change locAct v ((((diagF Q σ)⁻¹ * h) v : orthGroup Q (v.adicCompletion F)) : GL (Fin n) _) (loc v L.1) = loc v L.1
  have e : ((diagF Q σ)⁻¹ * h) v = (orthMap Q (v.adicCompletion F) σ)⁻¹ * h v := rfl
  rw [e, Subgroup.coe_mul, Subgroup.coe_inv, locAct_mul]
  by_cases hv : v ∈ T
  · rw [← hUσ v _ (hσT v hv), locAct_inv_locAct]
  · obtain ⟨hhv, hL⟩ := hT v hv hvp
    have h1 : locAct v ((h v : orthGroup Q _) : GL (Fin n) _) (std v) = std v := hhv
    have h2 : locAct v ((orthMap Q (v.adicCompletion F) σ : orthGroup Q _) : GL (Fin n) _) (std v) = std v :=
      hσT' v hv hvp
    rw [hL, h1]; exact (locAct_eq_iff.mp h2).symm


section Pair

variable {Q}

theorem pair_approxAt {p : HeightOneSpectrum (𝓞 F)} (hV : VecApproxAt Q p) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hpT : p ∉ T)
    (u w : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F)
    (hu : ∀ v ∈ T, Q.evalIn _ (u v) ≠ 0) (huw : ∀ v ∈ T, Q.evalIn _ (u v) = Q.evalIn _ (w v))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Matrix (Fin n) (Fin n) (v.adicCompletion F)))
    (hU : ∀ v ∈ T, U v ∈ 𝓝 (omat (symm Q _ (u v) * symm Q _ (w v)))) :
    ∃ σ ∈ spinorKernel Q F, (∀ v ∈ T, omat (orthMap Q (v.adicCompletion F) σ) ∈ U v) ∧
      ∀ v ∉ T, v ≠ p → orthMap Q (v.adicCompletion F) σ ∈ stdStab Q v := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · exact ⟨1, Subgroup.one_mem _, by simp, fun v _ _ => by rw [map_one]; exact Subgroup.one_mem _⟩
  choose! c A hA C hC B hBo hAQ hAC hAB using
    fun v (hv : v ∈ T) => pair_local (Q := Q) v (hu v hv) (huw v hv) (hU v hv)
  obtain ⟨u₀, hu₀, -⟩ := exists_vec_approx T u A hA
  obtain ⟨c₀, hc₀, -⟩ := exists_vec_approx T c C hC
  have hQu₀ : Q.evalIn F u₀ ≠ 0 := by
    have h := hAQ v₀ hv₀ _ (hu₀ v₀ hv₀)
    rw [evalIn_locVec] at h
    exact fun h0 => h (by rw [show Q.eval u₀ = 0 from h0, map_zero])
  set w₀ : Fin n → F := omat (symm Q F c₀) *ᵥ u₀ with hw₀
  have hw₀loc : ∀ v : HeightOneSpectrum (𝓞 F),
      locVec v w₀ = omat (symm Q (v.adicCompletion F) (locVec v c₀)) *ᵥ locVec v u₀ := by
    intro v
    rw [hw₀, locVec_mulVec, ← orthMap_val, orthMap_symm_locVec]
  have hw₀B : ∀ v ∈ T, locVec v w₀ ∈ B v := fun v hv => by
    rw [hw₀loc]; exact hAC v hv _ (hu₀ v hv) _ (hc₀ v hv)
  have hQw₀ : Q.evalIn F w₀ = Q.evalIn F u₀ := evalIn_mulVec_of_mem Q (symm Q F c₀).2 u₀
  have hgood := eventually_goodAt Q hQu₀
  set T₁ := (Filter.eventually_cofinite.mp hgood).toFinset
  have hT₁ : ∀ v, v ∉ T₁ → GoodAt Q u₀ v := by
    intro v hv; by_contra hc'; exact hv ((Filter.eventually_cofinite.mp hgood).mem_toFinset.mpr hc')
  choose N hN hNσ using fun v : HeightOneSpectrum (𝓞 F) => exists_mem_nhds_stdStab v Q
  have hloc0 : ∀ v : HeightOneSpectrum (𝓞 F), Q.evalIn (v.adicCompletion F) (locVec v u₀) ≠ 0 := by
    intro v; rw [evalIn_locVec]; exact (map_ne_zero _).mpr hQu₀
  obtain ⟨y, hyQ, hyZ, hystd⟩ := hV u₀ hQu₀ (T ∪ T₁)
    (fun v hv _ => (hT₁ v (fun h => hv (Finset.mem_union_right _ h))).1)
    (fun v => if v ∈ T then locVec v w₀ else locVec v u₀)
    (by
      intro v _
      split_ifs
      · rw [evalIn_locVec]; exact congrArg _ hQw₀
      · rw [evalIn_locVec])
    (fun v => if v ∈ T then B v else {y | omat (symm Q _ (locVec v u₀) * symm Q _ y) ∈ N v})
    (by
      intro v _
      split_ifs with hv
      · exact (hBo v hv).mem_nhds (hw₀B v hv)
      · exact symm_mul_mem_nhds v (hloc0 v) (hN v))
  refine ⟨symm Q F u₀ * symm Q F y,
    eqPairSet_subset_spinorKernel Q F (pair_mem_eqPairSet Q F hQu₀ hyQ.symm), ?_, ?_⟩
  · intro v hv
    have hyB := hyZ v (Finset.mem_union_left _ hv) (fun h => hpT (h ▸ hv))
    simp only [hv, ite_true] at hyB
    rw [map_mul, orthMap_symm_locVec, orthMap_symm_locVec]
    exact hAB v hv _ (hu₀ v hv) _ hyB
  · intro v hv hvp
    by_cases h1 : v ∈ T₁
    · have hyN := hyZ v (Finset.mem_union_right _ h1) hvp
      simp only [hv, ite_false] at hyN
      apply hNσ v
      rw [map_mul, orthMap_symm_locVec, orthMap_symm_locVec]
      exact hyN
    · exact pair_mem_stdStab Q (hT₁ v h1) (hystd v (by simp [hv, h1]) hvp) hyQ

end Pair

theorem list_approxAt {p : HeightOneSpectrum (𝓞 F)} (hV : VecApproxAt Q p) (u₀ : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F)
    (hu₀ : ∀ v, Q.evalIn _ (u₀ v) ≠ 0) :
    ∀ (N : ℕ) (T : Finset (HeightOneSpectrum (𝓞 F))), p ∉ T →
      ∀ (l : ∀ v : HeightOneSpectrum (𝓞 F), List (orthGroup Q (v.adicCompletion F))),
      (∀ v ∈ T, (l v).length ≤ N ∧ ∀ g ∈ l v, g ∈ eqPairSet Q _) →
      ∀ U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Matrix (Fin n) (Fin n) (v.adicCompletion F)),
        (∀ v ∈ T, U v ∈ 𝓝 (omat (l v).prod)) →
        ∃ σ ∈ spinorKernel Q F, (∀ v ∈ T, omat (orthMap Q (v.adicCompletion F) σ) ∈ U v) ∧
          ∀ v ∉ T, v ≠ p → orthMap Q (v.adicCompletion F) σ ∈ stdStab Q v := by
  classical
  intro N
  induction N with
  | zero =>
    intro T hpT l hl U hU
    refine ⟨1, Subgroup.one_mem _, fun v hv => ?_, fun v _ _ => by rw [map_one]; exact Subgroup.one_mem _⟩
    have h0 : l v = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (hl v hv).1)
    have := mem_of_mem_nhds (hU v hv)
    rw [h0, List.prod_nil] at this
    rw [map_one]; exact this
  | succ N ih =>
    intro T hpT l hl U hU
    -- the first factor as a pair
    have hpair : ∀ v ∈ T, ∃ a b : Fin n → v.adicCompletion F, Q.evalIn _ a ≠ 0 ∧ Q.evalIn _ a = Q.evalIn _ b ∧
        (l v).headD 1 = symm Q _ a * symm Q _ b := by
      intro v hv
      rcases hlv : l v with _ | ⟨g, t⟩
      · exact ⟨u₀ v, u₀ v, hu₀ v, rfl, by rw [symm_mul_self]; rfl⟩
      · obtain ⟨a, b, ha, hab, hg⟩ := (hl v hv).2 g (by rw [hlv]; exact List.mem_cons_self)
        exact ⟨a, b, ha, hab, hg⟩
    choose! a b ha hab hhead using hpair
    have hprod : ∀ v : HeightOneSpectrum (𝓞 F), (l v).prod = (l v).headD 1 * (l v).tail.prod := by
      intro v
      rcases l v with _ | ⟨g, t⟩
      · simp
      · simp
    -- split the neighbourhood
    have hsplit : ∀ v ∈ T, ∃ U₁ ∈ 𝓝 (omat (symm Q (v.adicCompletion F) (a v) * symm Q _ (b v))),
        ∃ U₂ ∈ 𝓝 (omat (l v).tail.prod), ∀ x ∈ U₁, ∀ y ∈ U₂, x * y ∈ U v := by
      intro v hv
      have hmem : U v ∈ 𝓝 (omat (symm Q (v.adicCompletion F) (a v) * symm Q _ (b v)) * omat (l v).tail.prod) := by
        rw [← hhead v hv, ← omat_mul, ← hprod]; exact hU v hv
      have hc := (continuous_matmul_joint v).continuousAt
        (x := (omat (symm Q (v.adicCompletion F) (a v) * symm Q _ (b v)), omat (l v).tail.prod))
      obtain ⟨U₁, hU₁, U₂, hU₂, h12⟩ := mem_nhds_prod_iff.mp (hc.preimage_mem_nhds hmem)
      refine ⟨U₁, hU₁, U₂, hU₂, fun x hx y hy => ?_⟩
      have := h12 (Set.mk_mem_prod hx hy)
      simp only [Set.mem_preimage] at this
      exact this
    choose! U₁ hU₁ U₂ hU₂ h12 using hsplit
    obtain ⟨σ₁, hσ₁, hσ₁T, hσ₁T'⟩ := pair_approxAt hV T hpT a b ha hab U₁ hU₁
    obtain ⟨σ₂, hσ₂, hσ₂T, hσ₂T'⟩ := ih T hpT (fun v => (l v).tail)
      (fun v hv => ⟨by rw [List.length_tail]; have := (hl v hv).1; omega,
        fun g hg => (hl v hv).2 g (List.mem_of_mem_tail hg)⟩) U₂ hU₂
    refine ⟨σ₁ * σ₂, Subgroup.mul_mem _ hσ₁ hσ₂, fun v hv => ?_, fun v hv hvp => ?_⟩
    · rw [map_mul, omat_mul]; exact h12 v hv _ (hσ₁T v hv) _ (hσ₂T v hv)
    · rw [map_mul]; exact Subgroup.mul_mem _ (hσ₁T' v hv hvp) (hσ₂T' v hv hvp)


theorem eqPair_approxAt (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {p : HeightOneSpectrum (𝓞 F)} (hV : VecApproxAt Q p)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hpT : p ∉ T) (φ : ∀ v : HeightOneSpectrum (𝓞 F), orthGroup Q (v.adicCompletion F))
    (hφ : ∀ v ∈ T, φ v ∈ eqPairGroup Q (v.adicCompletion F))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Matrix (Fin n) (Fin n) (v.adicCompletion F)))
    (hU : ∀ v ∈ T, U v ∈ 𝓝 (omat (φ v))) :
    ∃ σ ∈ spinorKernel Q F, (∀ v ∈ T, omat (orthMap Q (v.adicCompletion F) σ) ∈ U v) ∧
      ∀ v ∉ T, v ≠ p → orthMap Q (v.adicCompletion F) σ ∈ stdStab Q v := by
  classical
  have hu₀ : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : Fin n → v.adicCompletion F, Q.evalIn _ x ≠ 0 := by
    intro v
    obtain ⟨e, -, he⟩ := exists_orthogonal_basis Q (v.adicCompletion F) hQ
    exact ⟨e ⟨0, hn⟩, he _⟩
  choose u₀ hu₀ using hu₀
  choose! l hl hlprod using fun v (hv : v ∈ T) => exists_list_of_mem_eqPairGroup Q (hφ v hv)
  exact list_approxAt Q hV u₀ hu₀ (T.sup fun v => (l v).length) T hpT l
    (fun v hv => ⟨Finset.le_sup (f := fun v => (l v).length) hv, hl v hv⟩) U
    (fun v hv => by rw [hlprod v hv]; exact hU v hv)


theorem rotApproxAt_of_vecApproxAt_of_correction (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {p : HeightOneSpectrum (𝓞 F)}
    (hV : VecApproxAt Q p)
    (hcorr : ∀ (T : Finset (HeightOneSpectrum (𝓞 F)))
      (φ : ∀ v : HeightOneSpectrum (𝓞 F), orthGroup Q (v.adicCompletion F)),
      (∀ v ∈ T, φ v ∈ spinorKernel Q (v.adicCompletion F)) →
      ∃ g ∈ spinorKernel Q F, (∀ v ∈ T, orthMap Q (v.adicCompletion F) g * φ v ∈
          commutator (↥(orthGroup Q (v.adicCompletion F)))) ∧
        ∀ v ∉ T, orthMap Q (v.adicCompletion F) g ∈
          commutator (↥(orthGroup Q (v.adicCompletion F)))) :
    RotApproxAt Q p := by
  classical
  intro T hpT φ hφ U hU
  obtain ⟨g, hgO, hgT, hgall⟩ := hcorr T φ hφ
  have hgev := (diagF Q g).2
  set T₂ := (Filter.eventually_cofinite.mp hgev).toFinset
  have hT₂ : ∀ v, v ∉ T₂ → orthMap Q (v.adicCompletion F) g ∈ stdStab Q v := by
    intro v hv; by_contra hc; exact hv ((Filter.eventually_cofinite.mp hgev).mem_toFinset.mpr hc)
  choose N hN hNσ using fun v : HeightOneSpectrum (𝓞 F) => exists_mem_nhds_stdStab v Q
  set gv : ∀ v : HeightOneSpectrum (𝓞 F), orthGroup Q (v.adicCompletion F) :=
    fun v => orthMap Q (v.adicCompletion F) g
  have hE : ∀ v : HeightOneSpectrum (𝓞 F), eqPairGroup Q (v.adicCompletion F) =
      commutator (↥(orthGroup Q (v.adicCompletion F))) := fun v => eqPairGroup_eq_commutator Q _ hQ
  have hleft : ∀ (v : HeightOneSpectrum (𝓞 F)) (h : orthGroup Q (v.adicCompletion F))
      {S : Set (Matrix (Fin n) (Fin n) (v.adicCompletion F))}, S ∈ 𝓝 (omat h) →
      {M | omat (gv v)⁻¹ * M ∈ S} ∈ 𝓝 (omat (gv v * h)) := by
    intro v h S hS
    have hc : ContinuousAt (fun M : Matrix (Fin n) (Fin n) (v.adicCompletion F) => omat (gv v)⁻¹ * M)
        (omat (gv v * h)) :=
      continuousAt_matmul_of v (M := fun _ => omat (gv v)⁻¹) (N := fun M => M) continuousAt_const
        continuousAt_id
    refine hc.preimage_mem_nhds ?_
    rw [← omat_mul, inv_mul_cancel_left]; exact hS
  obtain ⟨σ, hσ, hσT, hσT'⟩ := eqPair_approxAt Q hQ hn hV ((T ∪ T₂).erase p) (Finset.notMem_erase p _)
    (fun v => if v ∈ T then gv v * φ v else gv v)
    (by
      intro v _
      rw [hE]
      split_ifs with h
      · exact hgT v h
      · exact hgall v h)
    (fun v => if v ∈ T then {M | omat (gv v)⁻¹ * M ∈ U v} else {M | omat (gv v)⁻¹ * M ∈ N v})
    (by
      intro v _
      split_ifs with h
      · exact hleft v (φ v) (hU v h)
      · have := hleft v 1 (S := N v) (by rw [omat_one]; exact hN v)
        rwa [mul_one] at this)
  refine ⟨g⁻¹ * σ, Subgroup.mul_mem _ (Subgroup.inv_mem _ hgO) hσ, fun v hv => ?_, fun v hv hvp => ?_⟩
  · have h := hσT v (Finset.mem_erase.mpr ⟨fun h => hpT (h ▸ hv), Finset.mem_union_left _ hv⟩)
    simp only [hv, ite_true, Set.mem_ofPred_eq] at h
    rw [map_mul, map_inv, omat_mul]; exact h
  · rw [map_mul, map_inv]
    by_cases h2 : v ∈ T₂
    · have h := hσT v (Finset.mem_erase.mpr ⟨hvp, Finset.mem_union_right _ h2⟩)
      simp only [hv, ite_false, Set.mem_ofPred_eq] at h
      exact hNσ v _ h
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hT₂ v h2)) (hσT' v (by simp [hv, h2]) hvp)

/-- **Step 1 of O'Meara 104:4 away from $\mathfrak p$, $n \ge 4$:** `VecApproxAt Q p` implies `RotApproxAt Q p`. -/
theorem rotApproxAt_of_vecApproxAt_of_four_le (hQ : Q.Nondegenerate) (hn : 4 ≤ n) {p : HeightOneSpectrum (𝓞 F)}
    (hV : VecApproxAt Q p) : RotApproxAt Q p :=
  rotApproxAt_of_vecApproxAt_of_correction Q hQ (by omega) hV fun T φ hφ => exists_correction Q hQ hn T φ hφ

end QuadFormsKB.Lattices
