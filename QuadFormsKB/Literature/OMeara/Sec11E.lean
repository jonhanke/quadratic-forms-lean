/-
# O'Meara §11A–§11F: carrying valuations, 11:4a, 11:6, divisibility of spots, 11:9, 11:11

**Setting.** As in `Sec11A.lean` and `Sec11B.lean`: a valuation on a field $F$ is a Mathlib `AbsoluteValue F ℝ`, and
O'Meara's prime spot (§11D) is its equivalence class under `AbsoluteValue.IsEquiv` (equivalent to O'Meara's "same
topology" `SameTopology` by 11:4, `equivalent_valuations_tfae`). A set of spots is represented by a set of
valuations, each standing for its class.

**Proves**
* `eq_one_of_finite` (§11A, p. 2): a finite field has only the trivial valuation;
* `rpowAbsLeOne`, `rpowAbsLeOne_apply` (§11C, pp. 6–7): $|\ |^{\varrho}$ is a valuation for $0 < \varrho \le 1$;
* `carryAbs` (§11A, p. 3): the valuation carried from $F$ to $F'$ by an isomorphism $\sigma$, which makes $\sigma$
  analytic (`carryAbs_apply_map`); `isTopologicalIso_iff_isEquiv_carryAbs` (§11D, p. 7): the carried spot is the
  unique spot of $F'$ making $\sigma$ topological;
* `sameTopology_of_lt_one_imp` (**11:4a**);
* `topologicalIso_spot` (**11:6**);
* `AbsoluteValue.under`, `SpotDivides` (§11D, p. 7: the spot $\mathfrak P \mid \mathfrak p$ induced on a subfield),
  `under_isEquiv` (the induced spot is well defined), `SetDivides`, `FullyDivides` (§11D, p. 8: $T \mid S$ and
  $T \parallel S$);
* `completeSpace_of_isEquiv` (§11F, p. 9): if $F$ is complete under one valuation of a spot it is complete under every
  valuation of the spot;
* `summable_of_tendsto_zero` (**11:9**): over a complete non-archimedean field every series whose terms tend to $0$
  converges;
* `completeSpace_trivial` (**11:11**): a field is complete at its trivial spot.
-/
import QuadFormsKB.Citation
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Analysis.Normed.Group.Ultra
import QuadFormsKB.Literature.OMeara.Sec11A
import QuadFormsKB.Literature.OMeara.Sec11B

open Filter Topology

namespace QuadFormsKB.OMeara

section Basic

variable {F : Type*} [Field F]

/-- **A finite field has only the trivial valuation** (§11A, p. 2). If $F$ has $q$ elements then
$|\alpha|^{q-1} = |\alpha^{q-1}| = |1| = 1$ for every $\alpha \ne 0$. -/
@[kb "omeara1963" "§11A, p. 2 (a finite field has only the trivial valuation)"]
theorem eq_one_of_finite [Finite F] (v : AbsoluteValue F ℝ) {x : F} (hx : x ≠ 0) : v x = 1 := by
  have := Fintype.ofFinite F
  have h1 : v x ^ (Fintype.card F - 1) = 1 := by
    rw [← map_pow, FiniteField.pow_card_sub_one_eq_one x hx, map_one]
  have hc : Fintype.card F - 1 ≠ 0 := by
    have := Fintype.one_lt_card (α := F); omega
  exact (pow_eq_one_iff_of_nonneg (v.nonneg x) hc).1 h1

/-- **Powers of a valuation** (§11C, pp. 6–7). For a valuation $|\ |$ on $F$ and $0 < \varrho \le 1$ the function
$|\ |^{\varrho}$ is again a valuation (O'Meara proves the triangle law from
$(|\alpha| + |\beta|)^{\varrho} \le |\alpha|^{\varrho} + |\beta|^{\varrho}$). For non-archimedean valuations every
$\varrho > 0$ is allowed (`rpowAbs` of `Sec14A.lean`). -/
@[kb "omeara1963" "§11C, pp. 6–7 (|·|^ρ is a valuation for 0 < ρ ≤ 1)"]
noncomputable def rpowAbsLeOne (v : AbsoluteValue F ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    AbsoluteValue F ℝ where
  toFun x := v x ^ ρ
  map_mul' x y := by simp [map_mul, Real.mul_rpow, v.nonneg]
  nonneg' x := Real.rpow_nonneg (v.nonneg x) _
  eq_zero' x := by
    rw [Real.rpow_eq_zero_iff_of_nonneg (v.nonneg x)]
    simp [hρ.ne']
  add_le' x y := by
    calc v (x + y) ^ ρ ≤ (v x + v y) ^ ρ :=
          Real.rpow_le_rpow (v.nonneg _) (v.add_le x y) hρ.le
      _ ≤ v x ^ ρ + v y ^ ρ :=
          Real.rpow_add_le_add_rpow (v.nonneg x) (v.nonneg y) hρ.le hρ1

/-- The values of `rpowAbsLeOne v hρ hρ1` are $|x|^{\varrho}$. -/
theorem rpowAbsLeOne_apply (v : AbsoluteValue F ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (x : F) :
    rpowAbsLeOne v hρ hρ1 x = v x ^ ρ := rfl

/-- **11:4a.** Let $|\ |_1$ be a non-trivial valuation on $F$ and $|\ |_2$ a valuation with
$|\alpha|_1 < 1 \Rightarrow |\alpha|_2 < 1$ for all $\alpha \in F$. Then $|\ |_2$ is equivalent to $|\ |_1$: the two
valuations define the same topology (O'Meara's definition of equivalence, `SameTopology`). From Mathlib's
`AbsoluteValue.isEquiv_of_lt_one_imp`. -/
@[kb "omeara1963" "§11C, 11:4a, p. 6"]
theorem sameTopology_of_lt_one_imp (v w : AbsoluteValue F ℝ) (hv : v.IsNontrivial)
    (h : ∀ a : F, v a < 1 → w a < 1) : SameTopology v w := by
  rw [SameTopology, ← AbsoluteValue.isEquiv_iff_isHomeomorph]
  exact AbsoluteValue.isEquiv_of_lt_one_imp hv h

/-- **If $F$ is complete at a spot, every valuation of the spot is complete** (§11F, p. 9; O'Meara: "because of the
formula $|\ |^{\varrho} = |\ |_1$ relating equivalent valuations"). -/
@[kb "omeara1963" "§11F, p. 9 (F complete at p: every valuation in p is complete)"]
theorem completeSpace_of_isEquiv {v w : AbsoluteValue F ℝ} (h : v.IsEquiv w)
    [CompleteSpace (WithAbs v)] : CompleteSpace (WithAbs w) := by
  have h' : IsTopologicalIso v w (RingEquiv.refl F) :=
    (AbsoluteValue.isEquiv_iff_isHomeomorph v w).1 h
  exact (completeSpace_iff_of_isTopologicalIso v w _ h').1 ‹_›

end Basic

section Carry

variable {F F' : Type*} [Field F] [Field F']

/-- **Carrying a valuation along an isomorphism** (§11A, p. 3). If $\sigma\colon F \to F'$ is a field isomorphism
and $|\ |$ a valuation on $F$, then $|\beta|' = |\sigma^{-1}\beta|$ is a valuation on $F'$; O'Meara says that
$\sigma$ *carries the valuation from $F$ to $F'$*. It makes $\sigma$ analytic (`carryAbs_apply_map`). -/
@[kb "omeara1963" "§11A, p. 3 (σ carries the valuation from F to F')"]
def carryAbs (σ : F ≃+* F') (v : AbsoluteValue F ℝ) : AbsoluteValue F' ℝ :=
  v.comp (f := σ.symm.toRingHom) σ.symm.injective

/-- Unfolding of `carryAbs`: $|\beta|' = |\sigma^{-1}\beta|$. -/
theorem carryAbs_apply (σ : F ≃+* F') (v : AbsoluteValue F ℝ) (y : F') :
    carryAbs σ v y = v (σ.symm y) := rfl

/-- The carried valuation makes $\sigma$ *analytic*: $|\sigma\alpha|' = |\alpha|$ (§11A, p. 3). -/
theorem carryAbs_apply_map (σ : F ≃+* F') (v : AbsoluteValue F ℝ) (x : F) :
    carryAbs σ v (σ x) = v x := by
  simp [carryAbs_apply]

/-- **The carried spot** (§11D, p. 7). For an isomorphism $\sigma\colon F \to F'$ and a valuation $|\ |$ of the spot
$\mathfrak p$ on $F$, a valuation $w$ of $F'$ makes $\sigma$ topological (`IsTopologicalIso`) if and only if $w$ lies
in the spot of the carried valuation; so the carried spot $\mathfrak p^{\sigma}$ is the unique spot of $F'$ making
$\sigma$ topological. -/
@[kb "omeara1963" "§11D, p. 7 (σ carries the spot p to the unique spot p^σ making σ topological)"]
theorem isTopologicalIso_iff_isEquiv_carryAbs (σ : F ≃+* F') (v : AbsoluteValue F ℝ)
    (w : AbsoluteValue F' ℝ) : IsTopologicalIso v w σ ↔ (carryAbs σ v).IsEquiv w := by
  rw [AbsoluteValue.isEquiv_iff_isHomeomorph]
  let ψ := WithAbs.congr v (carryAbs σ v) σ
  have hiso : Isometry ψ := by
    refine (AddMonoidHomClass.isometry_iff_norm ψ).2 fun x => ?_
    change carryAbs σ v (σ x.ofAbs) = v x.ofAbs
    exact carryAbs_apply_map σ v _
  have hψ : IsHomeomorph ψ :=
    isHomeomorph_iff_isEmbedding_surjective.2 ⟨hiso.isEmbedding, ψ.surjective⟩
  have hcomp : WithAbs.congr v w σ =
      WithAbs.congr (carryAbs σ v) w (RingEquiv.refl F') ∘ ψ := by
    ext x; simp [ψ]
  unfold IsTopologicalIso
  rw [hcomp]
  constructor
  · intro h
    have : WithAbs.congr (carryAbs σ v) w (RingEquiv.refl F') =
        (WithAbs.congr (carryAbs σ v) w (RingEquiv.refl F') ∘ ψ) ∘ hψ.homeomorph.symm := by
      ext x
      have := hψ.homeomorph.apply_symm_apply x
      simp only [Function.comp_apply]
      rw [show ψ (hψ.homeomorph.symm x) = x from this]
    rw [this]
    exact h.comp hψ.homeomorph.symm.isHomeomorph
  · intro h; exact h.comp hψ

/-- **11:6.** Let $F$ and $G$ carry the topologies of the valuations $v$ and $w$, and let $\sigma\colon F \to G$ be
a topological isomorphism. Then $w$ lies in the carried spot $\mathfrak p^{\sigma}$, and for each valuation $v'$ in
the spot of $v$ there is a valuation $w'$ in the spot of $w$ which makes $\sigma$ analytic
($w'(\sigma\alpha) = v'(\alpha)$). -/
@[kb "omeara1963" "§11D, 11:6, p. 7"]
theorem topologicalIso_spot (σ : F ≃+* F') (v : AbsoluteValue F ℝ) (w : AbsoluteValue F' ℝ)
    (h : IsTopologicalIso v w σ) :
    (carryAbs σ v).IsEquiv w ∧
      ∀ v' : AbsoluteValue F ℝ, v'.IsEquiv v →
        ∃ w' : AbsoluteValue F' ℝ, w'.IsEquiv w ∧ ∀ x : F, w' (σ x) = v' x := by
  have h1 := (isTopologicalIso_iff_isEquiv_carryAbs σ v w).1 h
  refine ⟨h1, fun v' hv' => ⟨carryAbs σ v', ?_, fun x => carryAbs_apply_map σ v' x⟩⟩
  have : (carryAbs σ v').IsEquiv (carryAbs σ v) := fun _ _ => hv' _ _
  exact this.trans h1

end Carry

section Divides

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The valuation induced on the subfield $F$ of $E$ by a valuation $w$ of $E$ (§11D, p. 7) is Mathlib's
`AbsoluteValue.under`: the restriction $\alpha \mapsto w(\alpha)$ for $\alpha \in F$. -/
theorem under_apply_eq (w : AbsoluteValue E ℝ) (x : F) :
    w.under F x = w (algebraMap F E x) := rfl

/-- **The induced spot is well defined** (§11D, p. 7): equivalent valuations of $E$ induce equivalent valuations
on $F$, so a spot $\mathfrak P$ of $E$ determines a unique spot $\mathfrak p$ of $F$. -/
@[kb "omeara1963" "§11D, p. 7 (all valuations of F induced from P are equivalent)"]
theorem under_isEquiv {w w' : AbsoluteValue E ℝ} (h : w.IsEquiv w') :
    (w.under F).IsEquiv (w'.under _) := fun _ _ => h _ _

/-- **$\mathfrak P$ divides $\mathfrak p$** (§11D, p. 7): the spot of the valuation $w$ of $E$ induces the spot of
the valuation $v$ of $F$, i.e. the restriction of $w$ to $F$ is equivalent to $v$. O'Meara writes
$\mathfrak P \mid \mathfrak p$. By `spotDivides_congr` this depends only on the spots. -/
@[kb "omeara1963" "§11D, p. 7 (P induces p, P divides p, P | p)"]
def SpotDivides (w : AbsoluteValue E ℝ) (v : AbsoluteValue F ℝ) : Prop :=
  (w.under F).IsEquiv v

/-- `SpotDivides` depends only on the spots of $w$ and $v$. -/
theorem spotDivides_congr {w w' : AbsoluteValue E ℝ} {v v' : AbsoluteValue F ℝ} (hw : w.IsEquiv w')
    (hv : v.IsEquiv v') : SpotDivides w v ↔ SpotDivides w' v' := by
  unfold SpotDivides
  exact ⟨fun h => (under_isEquiv hw).symm.trans (h.trans hv),
    fun h => (under_isEquiv hw).trans (h.trans hv.symm)⟩

/-- **$T$ divides $S$** (§11D, p. 8): for sets of spots $S$ on $F$ and $T$ on $E$ (represented by sets of
valuations), the spot induced on $F$ by each spot of $T$ is in $S$. -/
@[kb "omeara1963" "§11D, p. 8 (T divides S, T | S)"]
def SetDivides (T : Set (AbsoluteValue E ℝ)) (S : Set (AbsoluteValue F ℝ)) : Prop :=
  ∀ w ∈ T, ∃ v ∈ S, SpotDivides w v

/-- **$T$ fully divides $S$** (§11D, p. 8): $T$ is the largest set of spots on $E$ dividing $S$, i.e. a spot of $E$
is in $T$ if and only if it induces a spot of $S$. O'Meara writes $T \parallel S$. -/
@[kb "omeara1963" "§11D, p. 8 (T fully divides S, T || S)"]
def FullyDivides (T : Set (AbsoluteValue E ℝ)) (S : Set (AbsoluteValue F ℝ)) : Prop :=
  ∀ w : AbsoluteValue E ℝ, (∃ w' ∈ T, w'.IsEquiv w) ↔ ∃ v ∈ S, SpotDivides w v

/-- A set of spots that fully divides $S$ divides $S$. -/
theorem FullyDivides.setDivides {T : Set (AbsoluteValue E ℝ)} {S : Set (AbsoluteValue F ℝ)}
    (h : FullyDivides T S) : SetDivides T S := fun w hw => (h w).1 ⟨w, hw, AbsoluteValue.IsEquiv.rfl⟩

end Divides

/-- **11:9 (Example).** Let $K$ be a field with a complete non-archimedean valuation (a complete normed field whose
norm satisfies the strong triangle law). Then every series $\sum_{\nu} a_\nu$ whose terms tend to $0$ converges.
From Mathlib's `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero` (the sum is the limit of the partial sums,
`Summable.tendsto_sum_tsum_nat`). -/
@[kb "omeara1963" "§11F, 11:9, p. 9"]
theorem summable_of_tendsto_zero {K : Type*} [NormedField K] [CompleteSpace K]
    (hna : IsNonarchimedean (norm : K → ℝ)) {a : ℕ → K} (ha : Tendsto a atTop (𝓝 0)) :
    Summable a := by
  have : IsUltrametricDist K := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm hna
  exact NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (by rwa [Nat.cofinite_eq_atTop])

/-- **11:11 (Example).** Every field $F$ is complete at its trivial spot (every Cauchy sequence is eventually
constant). -/
@[kb "omeara1963" "§11F, 11:11, p. 9"]
theorem completeSpace_trivial {F : Type*} [Field F] [DecidablePred fun x : F => x = 0] :
    CompleteSpace (WithAbs (AbsoluteValue.trivial : AbsoluteValue F ℝ)) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu (1/2) (by norm_num)
  have key : ∀ n ≥ N, u n = u N := by
    intro n hn
    by_contra hne
    have := hN n hn N le_rfl
    rw [dist_eq_norm, WithAbs.norm_eq_apply_ofAbs] at this
    have hs : (u n - u N).ofAbs ≠ 0 := fun h =>
      hne (sub_eq_zero.1 (WithAbs.ofAbs_injective _ (by simpa using h)))
    rw [AbsoluteValue.trivial_apply hs] at this
    norm_num at this
  refine ⟨u N, tendsto_atTop_of_eventually_const (i₀ := N) key⟩

end QuadFormsKB.OMeara
