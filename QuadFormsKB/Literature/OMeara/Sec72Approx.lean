/-
# O'Meara §72: weak approximation of square classes

The weak approximation step of O'Meara's proof of Theorem 72:1 (p. 204: "Since $\dot F_\mathfrak p^2$ is an open
subset of $\dot F_\mathfrak p$, we can obtain $\alpha_i \in a_i^\mathfrak p \dot F_\mathfrak p^2$ ..."): given nonzero
local elements $c_\mathfrak p$ at finitely many finite spots and at all infinite spots, some $a \in \dot F$ lies in
$c_\mathfrak p \dot F_\mathfrak p^2$ at all of them. The density of $F$ in $\prod_{\mathfrak p} F_\mathfrak p$ is
Mathlib's `AbsoluteValue.denseRange_algebraMap_pi`, as in `NFLocal.exists_global_split_nf`.
-/
import QuadFormsKB.Literature.LocalGlobal.NumberFieldLocal

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type} [Field F] [NumberField F]

private lemma sq_near_one (K : Type) [NormedField K] [CompleteSpace K] (h2 : (2:K) ≠ 0) :
    ∃ δ > 0, ∀ u : K, ‖u - 1‖ < δ → IsSquare u := by
  have hn : 0 < ‖(2:K)‖ := norm_pos_iff.mpr h2
  set n := ‖(2:K)‖ with hn_def
  refine ⟨n^2/8, by positivity, fun u hu => ?_⟩
  set c := u - 1
  let f : K → K := fun y => (c - y^2)/2
  let s := Metric.closedBall (0:K) (n/4)
  have hmaps : Set.MapsTo f s s := by
    intro y hy
    simp only [s, Metric.mem_closedBall, dist_zero_right] at hy ⊢
    simp only [f, norm_div]
    rw [div_le_iff₀ hn]
    calc ‖c - y^2‖ ≤ ‖c‖ + ‖y‖^2 := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_pow]
      _ ≤ n^2/8 + (n/4)^2 := by gcongr
      _ ≤ n/4 * n := by nlinarith
  have hcon : ContractingWith (1/2 : NNReal) (hmaps.restrict f s s) := by
    refine ⟨one_half_lt_one, LipschitzWith.of_dist_le_mul fun y y' => ?_⟩
    have hy := y.2; have hy' := y'.2
    simp only [s, Metric.mem_closedBall, dist_zero_right] at hy hy'
    change dist (f (y:K)) (f y') ≤ ((1/2 : NNReal) : ℝ) * dist (y:K) y'
    simp only [dist_eq_norm, f]
    have : (c - (y:K)^2)/2 - (c - (y':K)^2)/2 = -((y:K) - y') * ((y:K) + y') / 2 := by ring
    rw [this, norm_div, norm_mul, norm_neg, div_le_iff₀ hn]
    have : ‖(y:K) + y'‖ ≤ n/2 := (norm_add_le _ _).trans (by linarith)
    push_cast
    calc ‖(y:K) - y'‖ * ‖(y:K) + y'‖ ≤ ‖(y:K) - y'‖ * (n/2) := by gcongr
      _ = 1/2 * ‖(y:K) - ↑y'‖ * n := by ring
  obtain ⟨y, -, hfix, -⟩ := ContractingWith.exists_fixedPoint' (Metric.isClosed_closedBall.isComplete)
    hmaps hcon (x := 0) (by simp [s]; positivity) (edist_ne_top _ _)
  refine ⟨1 + y, ?_⟩
  have : f y = y := hfix
  simp only [f] at this
  have h2' : (2:K) * y = c - y^2 := by
    have h3 : (2:K) * ((c - y^2)/2) = 2 * y := by rw [this]
    rw [mul_div_cancel₀ _ h2] at h3
    exact h3.symm
  simp only [c] at h2'
  linear_combination -h2'

private lemma local_open_sq (K : Type) [NormedField K] [CompleteSpace K] [Algebra F K]
    (A : AbsoluteValue F ℝ)
    (hcont : Continuous (fun x : WithAbs A => algebraMap F K (WithAbs.equiv A x)))
    (hdense : DenseRange (algebraMap F K)) (c : K) (hc : c ≠ 0) :
    ∃ U : Set (WithAbs A), IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U,
      algebraMap F K (WithAbs.equiv A x) ≠ 0 ∧ IsSquare (algebraMap F K (WithAbs.equiv A x) / c) := by
  have h2 : (2:K) ≠ 0 := by
    have := (algebraMap F K).injective.ne (two_ne_zero : (2:F) ≠ 0)
    rwa [map_ofNat, map_zero] at this
  obtain ⟨δ, hδ, hsq⟩ := sq_near_one K h2
  let V : Set K := {y | ‖y / c - 1‖ < min δ 1}
  have hV : IsOpen V := isOpen_lt (by fun_prop) continuous_const
  have hcV : c ∈ V := by
    simp only [V, Set.mem_setOf_eq, div_self hc, sub_self, norm_zero]; positivity
  refine ⟨(fun x : WithAbs A => algebraMap F K (WithAbs.equiv A x)) ⁻¹' V, hV.preimage hcont, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hdense.exists_mem_open hV ⟨_, hcV⟩
    exact ⟨(WithAbs.equiv A).symm x, by simpa using hx⟩
  · intro x hx
    simp only [Set.mem_preimage, V, Set.mem_setOf_eq] at hx
    refine ⟨?_, hsq _ (hx.trans_le (min_le_left _ _))⟩
    intro h0
    rw [h0, zero_div, zero_sub, norm_neg, norm_one] at hx
    exact absurd (hx.trans_le (min_le_right _ _)) (lt_irrefl _)

/-- The square-class condition at a spot. -/
private def Pl (c : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (cInf : (w : InfinitePlace F) → w.Completion) : NFPlace F → F → Prop
  | .infinite w, a => IsSquare (algebraMap F w.Completion a / cInf w)
  | .finite v, a => IsSquare (algebraMap F (v.adicCompletion F) a / c v)

/-- **Weak approximation of square classes** (O'Meara 1963, §72, proof of 72:1, p. 204): for a finite set $S$ of
finite spots and nonzero $c_v \in F_v$ ($v \in S$), $c_w \in F_w$ ($w$ infinite), there is $a \in \dot F$ with
$a / c_v$ a square in $F_v$ for every $v \in S$ and every infinite $w$. -/
@[kb "omeara1963" "§72, proof of 72:1, p. 204 (weak approximation of square classes)"]
theorem exists_approx_sq (S : Finset (HeightOneSpectrum (𝓞 F)))
    (c : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F) (hc : ∀ v, c v ≠ 0)
    (cInf : (w : InfinitePlace F) → w.Completion) (hcInf : ∀ w, cInf w ≠ 0) :
    ∃ a : F, a ≠ 0 ∧ (∀ v ∈ S, IsSquare (algebraMap F (v.adicCompletion F) a / c v)) ∧
      ∀ w, IsSquare (algebraMap F w.Completion a / cInf w) := by
  classical
  let S' : Finset (NFPlace F) := S.image NFPlace.finite ∪ Finset.univ.image NFPlace.infinite
  let absv : NFPlace F → AbsoluteValue F ℝ := fun v => match v with
    | .infinite w => w.1
    | .finite v => NumberField.HeightOneSpectrum.adicAbv F v
  have hle : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F x) ≤ 1 := by
    intro v x; rw [← FinitePlace.norm_embedding]; exact FinitePlace.norm_le_one F v x
  have hlt : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F x) < 1 ↔ x ∈ v.asIdeal := by
    intro v x; rw [← FinitePlace.norm_embedding]; exact FinitePlace.norm_lt_one_iff_mem F v x
  have hw2 : ∀ w : InfinitePlace F, w 2 = 2 := by
    intro w; rw [← InfinitePlace.norm_embedding_eq, map_ofNat]; norm_num
  have hfi : ∀ (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)), ¬ (NumberField.HeightOneSpectrum.adicAbv F v).IsEquiv w.1 := by
    intro w v h
    have h0 := hle v 2
    rw [map_ofNat] at h0
    have h1 := (h 2 1).mp (by rw [map_one]; exact h0)
    change w 2 ≤ w 1 at h1
    rw [hw2, map_one] at h1; norm_num at h1
  have hpw : Pairwise fun i j : S' => ¬ (absv i).IsEquiv (absv j) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij h
    cases i with
    | infinite w =>
      cases j with
      | infinite w' =>
        have e := InfinitePlace.eq_iff_isEquiv.mpr h
        subst e
        exact hij rfl
      | finite v => exact hfi w v h.symm
    | finite v =>
      cases j with
      | infinite w' => exact hfi w' v h
      | finite v' =>
        have hvv : v ≠ v' := by
          intro e; subst e; exact hij rfl
        have : ¬ v'.asIdeal ≤ v.asIdeal := by
          intro hle'
          exact hvv (HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top hle').symm)
        obtain ⟨y, hy', hy⟩ := SetLike.not_le_iff_exists.mp this
        have h1 := (h 1 (algebraMap (𝓞 F) F y)).mp (by
          rw [map_one]; exact not_lt.mp (fun hh => hy ((hlt v y).mp hh)))
        rw [map_one] at h1
        exact absurd ((hlt v' y).mpr hy') (not_lt.mpr h1)
  have hnt : ∀ i : S', (absv i).IsNontrivial := by
    rintro ⟨i, hi⟩
    cases i with
    | infinite w => exact InfinitePlace.isNontrivial w
    | finite v =>
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
      refine ⟨algebraMap (𝓞 F) F x, by simpa using hx0, ?_⟩
      exact ((hlt v x).mpr hx).ne
  have hdense := AbsoluteValue.denseRange_algebraMap_pi hnt hpw
  have hU : ∀ i : S', ∃ U : Set (WithAbs (absv i)), IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, WithAbs.equiv _ x ≠ 0 ∧ Pl c cInf i (WithAbs.equiv _ x) := by
    rintro ⟨i, hi⟩
    cases i with
    | infinite w =>
      have hd : DenseRange (algebraMap F w.Completion) := by
        have : (algebraMap F w.Completion : F → w.Completion) = (fun x : WithAbs w.1 =>
            InfinitePlace.Completion.ofCompletion (x : UniformSpace.Completion (WithAbs w.1))) ∘
            (WithAbs.equiv w.1).symm := rfl
        rw [this]
        unfold DenseRange
        rw [Function.Surjective.range_comp (WithAbs.equiv w.1).symm.surjective]
        exact InfinitePlace.Completion.denseRange_coe w
      obtain ⟨U, hUo, hUn, hUp⟩ := local_open_sq w.Completion w.1
        (InfinitePlace.Completion.continuous_coe w) hd (cInf w) (hcInf w)
      exact ⟨U, hUo, hUn, fun x hx => ⟨fun h => (hUp x hx).1 (by rw [h, map_zero]), (hUp x hx).2⟩⟩
    | finite v =>
      have hco : Continuous (fun x : WithAbs (NumberField.HeightOneSpectrum.adicAbv F v) =>
          algebraMap F (v.adicCompletion F) (WithAbs.equiv _ x)) := by
        have : Isometry ((FinitePlace.embedding v).comp
            (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv F v)).toRingHom) := by
          apply AddMonoidHomClass.isometry_of_norm
          intro x
          rw [WithAbs.norm_eq_apply_ofAbs]
          exact FinitePlace.norm_embedding v _
        exact this.continuous
      obtain ⟨U, hUo, hUn, hUp⟩ := local_open_sq (v.adicCompletion F)
        (NumberField.HeightOneSpectrum.adicAbv F v) hco
        (HeightOneSpectrum.denseRange_algebraMap F v) (c v) (hc v)
      exact ⟨U, hUo, hUn, fun x hx => ⟨fun h => (hUp x hx).1 (by rw [h, map_zero]), (hUp x hx).2⟩⟩
  choose U hUo hUn hUp using hU
  choose p hp using hUn
  let V : Set (Π i : S', WithAbs (absv i)) := ⋂ i, (fun q => q i) ⁻¹' U i
  have hVo : IsOpen V := isOpen_iInter_of_finite fun i => (hUo i).preimage (by fun_prop)
  have hVn : V.Nonempty := ⟨p, Set.mem_iInter.mpr fun i => hp i⟩
  obtain ⟨x, hx⟩ := hdense.exists_mem_open hVo hVn
  have key : ∀ i : S', x ≠ 0 ∧ Pl c cInf i x := fun i => by
    have := hUp i _ (Set.mem_iInter.mp hx i)
    exact this
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hw0 : (NFPlace.infinite w0) ∈ S' := by simp [S']
  refine ⟨x, (key ⟨_, hw0⟩).1, fun v hv => ?_, fun w => ?_⟩
  · exact (key ⟨NFPlace.finite v, by simp [S', hv]⟩).2
  · exact (key ⟨NFPlace.infinite w, by simp [S']⟩).2

end QuadFormsKB.OMeara
