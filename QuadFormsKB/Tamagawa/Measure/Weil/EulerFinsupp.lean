import Mathlib

/-!
# Euler products over finitely supported exponents
A generic lemma: for nonnegative local terms $a_v(j)$ ($v$ in a countable index set, $j\in\mathbb Z$) with summable
$j\mapsto a_v(j)$, $a_v(0)\ne0$ off a finite set $S_0$, and convergent products,
$$\sum_{e:\iota\to_0\mathbb Z}\prod_va_v(e_v) = \prod_v\sum_{j\in\mathbb Z}a_v(j)$$
(**`tsum_finsupp_ofReal_tprod`**), the sum in $[0,\infty]$. This is the Euler factorisation of a sum over ideals
$\mathfrak b = \prod_v\mathfrak p_v^{e_v}$ into local sums. *Proof.* For a finite $T\supseteq S_0$ the sum over the $e$ supported
in $T$ is $\prod_{v\in T}\sum_ja_v(j)\cdot\prod'_{v\notin T}a_v(0)$ (a finite product of sums); the full sum is the supremum
over $T$, and the right side tends to $\prod_v\sum_ja_v(j)$ because the tail $\prod'_{v\notin T}a_v(0)$ tends to $1$.
-/

open Filter Topology
open scoped ENNReal

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil


/-- Finitely supported exponent vectors with support inside `T`. -/
abbrev SuppIn {ι : Type*} (T : Finset ι) : Type _ := {e : ι →₀ ℤ // (↑e.support : Set ι) ⊆ ↑T}

/-- Splitting off one coordinate: `ℤ × SuppIn T ≃ SuppIn (insert w T)` for `w ∉ T`. -/
def suppInsertEquiv {ι : Type*} [DecidableEq ι] (T : Finset ι) (w : ι) (hw : w ∉ T) :
    ℤ × SuppIn T ≃ SuppIn (insert w T) where
  toFun p := ⟨p.2.1.update w p.1, by
    intro v hv
    have := Finsupp.support_update_subset (f := p.2.1) (a := w) (b := p.1) (by exact_mod_cast hv)
    rcases Finset.mem_insert.1 this with h | h
    · simp [h]
    · exact_mod_cast Finset.mem_insert_of_mem (p.2.2 (by exact_mod_cast h))⟩
  invFun e := (e.1 w, ⟨e.1.erase w, by
    intro v hv
    have hv' : v ∈ (e.1.erase w).support := by exact_mod_cast hv
    rw [Finsupp.support_erase] at hv'
    have := e.2 (by exact_mod_cast Finset.mem_of_mem_erase hv')
    have := Finset.mem_insert.1 (by exact_mod_cast this : v ∈ insert w T)
    rcases this with h | h
    · exact absurd h (Finset.ne_of_mem_erase hv')
    · exact_mod_cast h⟩)
  left_inv p := by
    obtain ⟨j, e, he⟩ := p
    have hew : e w = 0 := by
      by_contra h
      exact hw (by exact_mod_cast he (by simpa using h))
    refine Prod.ext (by simp) (Subtype.ext ?_)
    ext v
    by_cases hv : v = w
    · subst hv; simp [hew]
    · simp [Finsupp.erase_ne hv]
  right_inv e := by
    ext v
    by_cases hv : v = w
    · subst hv; simp
    · simp

/-- The sum over exponent vectors supported in `T` of a product over `T` is the product of the sums. -/
theorem tsum_suppIn_prod {ι : Type*} [DecidableEq ι] (b : ι → ℤ → ℝ≥0∞) (T : Finset ι) :
    ∑' e : SuppIn T, ∏ v ∈ T, b v (e.1 v) = ∏ v ∈ T, ∑' j, b v j := by
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [tsum_eq_single ⟨0, by simp⟩]
    intro e he
    exact absurd (Subtype.ext (by
      ext v
      have := e.2
      by_contra hv
      exact (Finset.notMem_empty v) (by exact_mod_cast this (by simpa using hv)))) he
  | insert w T hw ih =>
    rw [← (suppInsertEquiv T w hw).tsum_eq]
    have key : ∀ p : ℤ × SuppIn T,
        ∏ v ∈ insert w T, b v (((suppInsertEquiv T w hw) p).1 v) = b w p.1 * ∏ v ∈ T, b v (p.2.1 v) := by
      intro p
      rw [Finset.prod_insert hw]
      congr 1
      · simp [suppInsertEquiv]
      · refine Finset.prod_congr rfl fun v hv => ?_
        have : v ≠ w := fun h => hw (h ▸ hv)
        simp [suppInsertEquiv, Finsupp.update_apply, this]
    simp_rw [key]
    rw [ENNReal.tsum_prod (f := fun (j : ℤ) (e : SuppIn T) => b w j * ∏ v ∈ T, b v (e.1 v)),
      Finset.prod_insert hw, ← ih, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun j => ?_
    rw [ENNReal.tsum_mul_left]

/-- Tail of an Euler product: modifying a multipliable product on a finite set. -/
theorem hasProd_tail {ι : Type*} [DecidableEq ι] (a0 : ι → ℝ) (S₀ T : Finset ι) (hST : S₀ ⊆ T) (P : ℝ)
    (hP : HasProd (fun v => if v ∈ S₀ then 1 else a0 v) P) (hC : ∏ v ∈ T, (if v ∈ S₀ then (1 : ℝ) else a0 v) ≠ 0) :
    HasProd (fun v => if v ∈ T then 1 else a0 v) (P / ∏ v ∈ T, (if v ∈ S₀ then (1 : ℝ) else a0 v)) := by
  set g : ι → ℝ := fun v => if v ∈ S₀ then 1 else a0 v with hg
  set C := ∏ v ∈ T, g v with hCdef
  have h1 : Tendsto (fun s : Finset ι => (∏ v ∈ s, g v) / C) atTop (𝓝 (P / C)) :=
    (show Tendsto (fun s : Finset ι => ∏ v ∈ s, g v) atTop (𝓝 P) from hP).div_const C
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop T] with s hs
  have hpt : ∀ v, g v = (if v ∈ T then 1 else a0 v) * (if v ∈ T then g v else 1) := by
    intro v
    by_cases hv : v ∈ T
    · simp [hv]
    · have : v ∉ S₀ := fun h => hv (hST h)
      simp [hv, hg, this]
  have hsub : ∏ v ∈ s, (if v ∈ T then g v else 1) = C := by
    rw [← Finset.prod_subset hs (f := fun v => if v ∈ T then g v else 1)
      (fun v _ hv => by simp [hv])]
    exact Finset.prod_congr rfl fun v hv => by simp [hv]
  have : ∏ v ∈ s, g v = (∏ v ∈ s, (if v ∈ T then 1 else a0 v)) * C := by
    rw [← hsub, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => hpt v
  rw [this]
  field_simp

/-- **The Euler factorisation over finitely supported exponents.** -/
theorem tsum_finsupp_ofReal_tprod {ι : Type*} [Countable ι] [DecidableEq ι] (a : ι → ℤ → ℝ)
    (ha : ∀ v j, 0 ≤ a v j) (hsum : ∀ v, Summable (a v)) (S₀ : Finset ι) (h0 : ∀ v ∉ S₀, a v 0 ≠ 0)
    (hP : Multipliable fun v => if v ∈ S₀ then 1 else a v 0)
    (hP0 : (∏' v, if v ∈ S₀ then 1 else a v 0) ≠ 0)
    (hE : Multipliable fun v => ∑' j, a v j) :
    ∑' e : ι →₀ ℤ, ENNReal.ofReal (∏' v, a v (e v)) = ENNReal.ofReal (∏' v, ∑' j, a v j) := by
  classical
  set g : ι → ℝ := fun v => if v ∈ S₀ then 1 else a v 0 with hg
  set P := ∏' v, g v with hPdef
  set Q := ∏' v, ∑' j, a v j with hQdef
  have hE0 : ∀ v, 0 ≤ ∑' j, a v j := fun v => tsum_nonneg (ha v)
  have hg0 : ∀ T : Finset ι, S₀ ⊆ T → ∏ v ∈ T, g v ≠ 0 := by
    intro T _
    rw [Finset.prod_ne_zero_iff]
    intro v _
    by_cases hv : v ∈ S₀
    · simp [hg, hv]
    · simpa [hg, hv] using h0 v hv
  have hPnn : 0 ≤ P := tprod_nonneg fun v => by
    by_cases hv : v ∈ S₀ <;> simp [hg, hv, ha]
  let R : Finset ι → ℝ := fun T => (∏ v ∈ T, ∑' j, a v j) * (P / ∏ v ∈ T, g v)
  have hR : Tendsto R atTop (𝓝 Q) := by
    have h1 : Tendsto (fun T : Finset ι => ∏ v ∈ T, ∑' j, a v j) atTop (𝓝 Q) := hE.hasProd
    have h2 : Tendsto (fun T : Finset ι => ∏ v ∈ T, g v) atTop (𝓝 P) := hP.hasProd
    have := h1.mul (tendsto_const_nhds (x := P).div h2 hP0)
    simpa [R, div_self hP0] using this
  have hΦ : Tendsto (fun T => ENNReal.ofReal (R T)) atTop (𝓝 (ENNReal.ofReal Q)) :=
    ENNReal.tendsto_ofReal hR
  let G : Finset ι → ℝ≥0∞ := fun T => ∑' e : SuppIn T, ENNReal.ofReal (∏' v, a v (e.1 v))
  have hGmono : ∀ T T' : Finset ι, T ⊆ T' → G T ≤ G T' := by
    intro T T' hT
    exact ENNReal.tsum_comp_le_tsum_of_injective
      (f := fun e : SuppIn T => (⟨e.1, fun v hv => by exact_mod_cast hT (e.2 hv)⟩ : SuppIn T'))
      (fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h))
      (fun e : SuppIn T' => ENNReal.ofReal (∏' v, a v (e.1 v)))
  have hGeq : ∀ T : Finset ι, S₀ ⊆ T → G T = ENNReal.ofReal (R T) := by
    intro T hT
    have hC := hg0 T hT
    have htail := hasProd_tail (fun v => a v 0) S₀ T hT P hP.hasProd hC
    have hfe : ∀ e : SuppIn T, ∏' v, a v (e.1 v) = (∏ v ∈ T, a v (e.1 v)) * (P / ∏ v ∈ T, g v) := by
      intro e
      have hfin : HasProd (fun v => if v ∈ T then a v (e.1 v) else 1) (∏ v ∈ T, a v (e.1 v)) := by
        have : HasProd (fun v => if v ∈ T then a v (e.1 v) else 1)
            (∏ v ∈ T, (if v ∈ T then a v (e.1 v) else 1)) :=
          hasProd_prod_of_ne_finset_one (s := T) (fun v hv => by simp [hv])
        simpa using this
      have := hfin.mul htail
      rw [← this.tprod_eq]
      refine tprod_congr fun v => ?_
      by_cases hv : v ∈ T
      · simp [hv]
      · have : e.1 v = 0 := by
          by_contra h
          exact hv (by exact_mod_cast e.2 (by simpa using h))
        simp [hv, this]
    have hPC : 0 ≤ P / ∏ v ∈ T, g v := by
      have : 0 ≤ ∏ v ∈ T, g v := Finset.prod_nonneg fun v _ => by
        by_cases hv : v ∈ S₀ <;> simp [hg, hv, ha]
      positivity
    have hfin0 : ∀ e : SuppIn T, 0 ≤ ∏ v ∈ T, a v (e.1 v) := fun e => Finset.prod_nonneg fun v _ => ha _ _
    unfold G
    simp_rw [hfe, ENNReal.ofReal_mul (hfin0 _), ENNReal.ofReal_prod_of_nonneg (fun v _ => ha _ _)]
    rw [ENNReal.tsum_mul_right, tsum_suppIn_prod (fun v j => ENNReal.ofReal (a v j)) T]
    simp only [R]
    rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => hE0 v),
      ENNReal.ofReal_prod_of_nonneg (fun v _ => hE0 v)]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (ha v) (hsum v)]
  apply le_antisymm
  · rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    set T : Finset ι := S₀ ∪ s.biUnion (fun e => e.support) with hT
    have hS₀T : S₀ ⊆ T := Finset.subset_union_left
    have hmem : ∀ e ∈ s, (↑e.support : Set ι) ⊆ ↑T := by
      intro e he v hv
      simp only [hT, Finset.coe_union, Finset.coe_biUnion, Set.mem_union, Set.mem_iUnion]
      exact Or.inr ⟨e, by exact_mod_cast he, hv⟩
    have h1 : ∑ e ∈ s, ENNReal.ofReal (∏' v, a v (e v)) ≤ G T := by
      classical
      rw [← Finset.sum_subtype_of_mem (fun e => ENNReal.ofReal (∏' v, a v (e v))) hmem]
      exact ENNReal.sum_le_tsum _
    refine h1.trans ?_
    refine ge_of_tendsto hΦ ?_
    filter_upwards [eventually_ge_atTop T] with T' hT'
    rw [← hGeq T' (hS₀T.trans hT')]
    exact hGmono _ _ hT'
  · refine le_of_tendsto hΦ ?_
    filter_upwards [eventually_ge_atTop S₀] with T hT
    rw [← hGeq T hT]
    exact ENNReal.tsum_comp_le_tsum_of_injective (Subtype.val_injective (p := fun e : ι →₀ ℤ => (↑e.support : Set ι) ⊆ ↑T))
      (fun e : ι →₀ ℤ => ENNReal.ofReal (∏' v, a v (e v)))

end QuadFormsKB.Tamagawa.Measure.Weil

end
