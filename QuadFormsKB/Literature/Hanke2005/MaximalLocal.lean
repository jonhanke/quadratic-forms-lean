/-
# Hanke 2005, §6: maximal lattices locally (input to Theorem 6.3)

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Setting.** $Q_0$ nondegenerate over $\mathcal O_F$, $V = (F^n, Q_0)$, $V_\mathfrak p = (F_\mathfrak p^n, Q_0)$ with the quadratic map
`qv v Q₀` ($x\mapsto Q_0(x)$ over $F_\mathfrak p$, O'Meara's convention), lattices `Submodule 𝔬 (Fin n → Fv)`.

**Proves** `isMaximal_loc` (O'Meara 1963, 82:? and §91A, localization then completion): an $\mathfrak a$-maximal lattice $L$ on $V$ has
  $\mathfrak a_\mathfrak p$-maximal completions $L_\mathfrak p$, $\mathfrak a_\mathfrak p = \mathfrak p^{\mathrm{ord}_\mathfrak p\mathfrak a}\mathfrak o_\mathfrak p$;
-/
import QuadFormsKB.Literature.Hanke2005.Sec6Defs
import QuadFormsKB.Literature.OMeara.Sec91Max
import QuadFormsKB.Literature.OMeara.Sec82Local
import QuadFormsKB.Tamagawa.QuatOrderGlobal

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

section Helpers

/-- Membership in the $\mathcal O_F$-span of the image of an ideal: the image itself. -/
theorem mem_idealSpan_iff {I : Ideal (𝓞 F)} {c : F} :
    c ∈ Submodule.span (𝓞 F) (algebraMap (𝓞 F) F '' (I : Set (𝓞 F))) ↔
      ∃ a ∈ I, algebraMap (𝓞 F) F a = c := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx => obtain ⟨a, ha, rfl⟩ := hx; exact ⟨a, ha, rfl⟩
    | zero => exact ⟨0, I.zero_mem, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, I.add_mem ha hb, map_add _ _ _⟩
    | smul r x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨r * a, I.mul_mem_left r ha, by simp [Algebra.smul_def]⟩
  · rintro ⟨a, ha, rfl⟩
    exact Submodule.subset_span ⟨a, ha, rfl⟩

/-- **Local–global principle for an ideal:** $c \in \mathfrak a$ iff $v_\mathfrak p(c) \le e^{-\mathrm{ord}_\mathfrak p \mathfrak a}$
for every prime $\mathfrak p$. -/
theorem mem_idealSpan_iff_valuation {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) {c : F} :
    c ∈ Submodule.span (𝓞 F) (algebraMap (𝓞 F) F '' (I : Set (𝓞 F))) ↔
      ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F c ≤ WithZero.exp (-(ordIdeal w I : ℤ)) := by
  rw [mem_idealSpan_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩ w
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
    have h := Ideal.iInf_maxPowDividing_eq hI
    have : I ≤ w.maxPowDividing I := h.symm.le.trans (iInf_le _ w)
    exact this ha
  · intro h
    have h1 : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F c ≤ 1 := fun w =>
      (h w).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
    obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (K := F) c h1
    refine ⟨a, ?_, rfl⟩
    rw [← Ideal.iInf_maxPowDividing_eq hI]
    simp only [Submodule.mem_iInf]
    intro w
    have := h w
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem] at this
    exact this

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $Q_0$ at a localized vector. -/
theorem qv_locVec (Q₀ : QuadForm (𝓞 F) n) (x : Fin n → F) :
    qv v Q₀ (locVec v x) =
      algebraMap F Fv (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F)) x) := by
  rw [qv, QuadForm.toQuadraticForm_apply, QuadForm.toQuadraticForm_apply]
  simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.map, map_sum, locVec_apply, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem valued_le_one_of_mem (c : 𝔬) : Valued.v (c : Fv) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp c.2

/-- $y \in \mathfrak p^k\mathfrak o_\mathfrak p$ iff $|y| \le e^{-k}$. -/
theorem mem_pPow_iff (k : ℕ) (y : Fv) :
    y ∈ pPow v k ↔ Valued.v y ≤ WithZero.exp (-(k : ℤ)) := by
  have hπ : Valued.v ((NF.π v : 𝔬) : Fv) = WithZero.exp (-1 : ℤ) := NF.valued_π v
  have hk : Valued.v (((NF.π v : 𝔬) : Fv) ^ k) = WithZero.exp (-(k : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; simp
  have hne : ((NF.π v : 𝔬) : Fv) ^ k ≠ 0 := by
    intro h0; rw [h0, map_zero] at hk; exact WithZero.exp_ne_zero hk.symm
  rw [pPow, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    change Valued.v ((c : Fv) * ((NF.π v : 𝔬) : Fv) ^ k) ≤ _
    rw [map_mul, hk]
    calc Valued.v (c : Fv) * WithZero.exp (-(k : ℤ)) ≤ 1 * WithZero.exp (-(k : ℤ)) :=
          mul_le_mul' (valued_le_one_of_mem v c) le_rfl
      _ = _ := one_mul _
  · intro h
    have hc : Valued.v (y / ((NF.π v : 𝔬) : Fv) ^ k) ≤ 1 := by
      rw [map_div₀, hk]
      exact div_le_one_of_le₀ h zero_le
    refine ⟨⟨y / ((NF.π v : 𝔬) : Fv) ^ k, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hc⟩, ?_⟩
    change y / ((NF.π v : 𝔬) : Fv) ^ k * ((NF.π v : 𝔬) : Fv) ^ k = y
    exact div_mul_cancel₀ y hne

/-- **A form that is small on generators and their polars is small on the span.** -/
theorem span_qv_le (q : QuadraticForm Fv (Fin n → Fv)) (e : WithZero (Multiplicative ℤ))
    (G : Set (Fin n → Fv)) (hG1 : ∀ g ∈ G, Valued.v (q g) ≤ e)
    (hG2 : ∀ g ∈ G, ∀ g' ∈ G, Valued.v (QuadraticMap.polar q g g') ≤ e) :
    ∀ y ∈ Submodule.span 𝔬 G, Valued.v (q y) ≤ e := by
  have hsm : ∀ (c : 𝔬) (y : Fin n → Fv), c • y = (c : Fv) • y := fun c y => rfl
  have hmul : ∀ (c : 𝔬) (t : Fv), Valued.v t ≤ e → Valued.v ((c : Fv) * t) ≤ e := by
    intro c t ht
    rw [map_mul]
    calc Valued.v (c : Fv) * Valued.v t ≤ 1 * e := mul_le_mul' (valued_le_one_of_mem v c) ht
      _ = e := one_mul _
  have s1 : ∀ y ∈ Submodule.span 𝔬 G, ∀ g ∈ G, Valued.v (QuadraticMap.polar q y g) ≤ e := by
    intro y hy g hg
    induction hy using Submodule.span_induction with
    | mem x hx => exact hG2 x hx g hg
    | zero => simp
    | add x y _ _ hx hy => rw [QuadraticMap.polar_add_left]; exact Valuation.map_add_le _ hx hy
    | smul c x _ hx => rw [hsm, QuadraticMap.polar_smul_left]; exact hmul c _ hx
  have s2 : ∀ y ∈ Submodule.span 𝔬 G, ∀ z ∈ Submodule.span 𝔬 G,
      Valued.v (QuadraticMap.polar q y z) ≤ e := by
    intro y hy z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact s1 y hy x hx
    | zero => simp
    | add x x' _ _ hx hx' => rw [QuadraticMap.polar_add_right]; exact Valuation.map_add_le _ hx hx'
    | smul c x _ hx => rw [hsm, QuadraticMap.polar_smul_right]; exact hmul c _ hx
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact hG1 x hx
  | zero => simp
  | add x x' hx hx' ih ih' =>
    rw [QuadraticMap.map_add q x x']
    exact Valuation.map_add_le _ (Valuation.map_add_le _ ih ih') (s2 x hx x' hx')
  | smul c x _ hx =>
    rw [hsm, QuadraticMap.map_smul, smul_eq_mul, mul_assoc]
    exact hmul c _ (hmul c _ hx)

/-- **Part (a), values:** if every value $Q(x)$, $x \in L$, lies in $\mathfrak a$, then $Q(y)$ has
$v_\mathfrak p \le e^{-\mathrm{ord}_\mathfrak p\mathfrak a}$ for every $y \in L_\mathfrak p$. -/
theorem loc_val_le (Q₀ : QuadForm (𝓞 F) n) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥)
    (L : Submodule (𝓞 F) (Fin n → F))
    (hL : ∀ x ∈ L, QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F)) x ∈
      Submodule.span (𝓞 F) (algebraMap (𝓞 F) F '' (I : Set (𝓞 F)))) :
    ∀ y ∈ loc v L, Valued.v (qv v Q₀ y) ≤ WithZero.exp (-(ordIdeal v I : ℤ)) := by
  set QF := QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F)) with hQF
  have hval : ∀ x ∈ L, Valued.v (qv v Q₀ (locVec v x)) ≤ WithZero.exp (-(ordIdeal v I : ℤ)) := by
    intro x hx
    rw [qv_locVec, valued_algebraMap]
    exact (mem_idealSpan_iff_valuation hI).mp (hL x hx) v
  refine span_qv_le v (qv v Q₀) _ (locVec v '' (L : Set (Fin n → F))) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hval x hx
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    have : QuadraticMap.polar (qv v Q₀) (locVec v x) (locVec v x') =
        algebraMap F Fv (QF (x + x') - QF x - QF x') := by
      rw [QuadraticMap.polar, ← map_add, qv_locVec, qv_locVec, qv_locVec, map_sub, map_sub]
    rw [this, valued_algebraMap]
    refine (mem_idealSpan_iff_valuation hI).mp ?_ v
    exact Submodule.sub_mem _ (Submodule.sub_mem _ (hL _ (L.add_mem hx hx')) (hL _ hx)) (hL _ hx')

end Local

end Helpers

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **Maximal lattices complete to maximal lattices.** -/
theorem isMaximal_loc (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (L : Lat F n)
    (hL : letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
      OMeara.IsMaximal (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F)))
        (Submodule.span (𝓞 F) (algebraMap (𝓞 F) F '' (I : Set (𝓞 F)))) L.1) :
    letI : Invertible (2 : Fv) := invertibleOfNonzero two_ne_zero
    OMeara.IsMaximal (qv v Q₀) (pPow v (ordIdeal v I)) (loc v L.1) := by
  classical
  have hI' : I ≠ ⊥ := hI
  obtain ⟨hLlat, hLn, hLmax⟩ := hL
  have hLx : ∀ x ∈ L.1, QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F)) x ∈
      Submodule.span (𝓞 F) (algebraMap (𝓞 F) F '' (I : Set (𝓞 F))) :=
    fun x hx => hLn (Submodule.subset_span ⟨x, hx, rfl⟩)
  unfold OMeara.IsMaximal
  refine ⟨loc_isLattice v L.2, ?_, ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_pPow_iff v _ _).mpr (loc_val_le v Q₀ hI' L.1 hLx y hy)
  · intro N hN hMN hNn
    obtain ⟨Mf, hMf_v, hMf_ne⟩ : ∃ Mf : ∀ w : HeightOneSpectrum (𝓞 F),
        Submodule (w.adicCompletionIntegers F) (Fin n → w.adicCompletion F),
        Mf v = N ∧ ∀ w, w ≠ v → Mf w = loc w L.1 :=
      ⟨Function.update (fun w => loc w L.1) v N, Function.update_self _ _ _,
        fun w hw => Function.update_of_ne hw _ _⟩
    let fam : LocFamily F n :=
      { M := Mf
        isLattice := fun w => by
          rcases eq_or_ne w v with rfl | hw
          · rw [hMf_v]; exact hN
          · rw [hMf_ne w hw]; exact loc_isLattice w L.2
        eventually_std := by
          filter_upwards [loc_eventually_std L.2, Filter.eventually_cofinite_ne v] with w h1 h2
          rw [hMf_ne w h2]; exact h1 }
    have hN'lat : fam.glue.IsLattice F := fam.glue_isLattice
    have hlocN : ∀ w, loc w fam.glue = Mf w := fun w => fam.loc_glue w
    have hLN' : L.1 ≤ fam.glue := by
      refine (le_iff_forall_loc hN'lat).mpr fun w => ?_
      rcases eq_or_ne w v with rfl | hw
      · rw [hlocN, hMf_v]; exact hMN
      · rw [hlocN, hMf_ne w hw]
    have hnorm : ∀ x ∈ fam.glue, QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F)) x ∈
        Submodule.span (𝓞 F) (algebraMap (𝓞 F) F '' (I : Set (𝓞 F))) := by
      intro x hx
      refine (mem_idealSpan_iff_valuation hI').mpr fun w => ?_
      have hxw : locVec w x ∈ Mf w := fam.mem_glue.mp hx w
      have hq : w.valuation F (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F)) x) =
          Valued.v (qv w Q₀ (locVec w x)) := by rw [qv_locVec, valued_algebraMap]
      rw [hq]
      rcases eq_or_ne w v with rfl | hw
      · rw [hMf_v] at hxw
        exact (mem_pPow_iff w _ _).mp (hNn (Submodule.subset_span ⟨_, hxw, rfl⟩))
      · rw [hMf_ne w hw] at hxw
        exact loc_val_le w Q₀ hI' L.1 hLx _ hxw
    have hEq : fam.glue = L.1 := by
      refine hLmax _ hN'lat hLN' ?_
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hnorm x hx
    have := hlocN v
    rw [hEq, hMf_v] at this
    exact this.symm

end Local

end QuadFormsKB.Hanke2005
