/-
# O'Meara 93:28, sufficiency: the scale gap of a Jordan splitting

**Setting** (as in `Sec93FSuffGood.lean`): $R$ a discrete valuation ring with fraction field $F$, $(V, Q)$ a quadratic
space over $F$, lattices `Submodule R V`; indices are $0$-based.

**Proves** (auxiliary to O'Meara 1963, §93F, proof of 93:28, sufficiency, step 8, p. 276, where the induction must also
decrease the *scale gap* $\mathfrak s_t - \mathfrak s_1$):
* `GapLe Q Ls G`: $\mathfrak p^G \mathfrak s_i \subseteq \mathfrak s_j$ for all components $i, j$ of the splitting `Ls`
  (a bound $G$ for the gap);
* `exists_gapLe`: every Jordan splitting of a finitely generated lattice has some such bound `G`; `gapLe_mono`;
* invariance of `GapLe` whenever the scales are unchanged up to one common factor (`gapLe_of_scale_eq`,
  `gapLe_of_scale_eq_mul`), with the instances used in the reductions of step 2: products (`gapLe_prod`), scaling the
  form (`gapLe_smul_form`), moving by an isometry (`gapLe_latMap`), replacing one component (`gapLe_repl`), passing to a
  subspace (`gapLe_subLatIn`), and re-splitting the same lattice (`gapLe_resplit`);
* `gapLe_tail`: dropping the first component lowers the bound by one.
-/
import QuadFormsKB.Literature.OMeara.Sec93FCore8

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Gap

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {W : Type*} [AddCommGroup W] [Module F W] [Module R W] [IsScalarTower R F W]

/-- **A bound for the scale gap** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 8, p. 276): the components
$L_i$ of the splitting `Ls` satisfy $\mathfrak p^G\,\mathfrak s L_i \subseteq \mathfrak s L_j$ for all $i, j$ (so the
gap $\mathfrak s_t - \mathfrak s_1$ is at most $G$ valuation steps). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
def GapLe (Q : QuadraticForm F V) {t : ℕ} (Ls : Fin t → Submodule R V) (G : ℕ) : Prop :=
  ∀ i j : Fin t, ∀ r ∈ maximalIdeal R ^ G, ∀ x ∈ scale Q (Ls i), r • x ∈ scale Q (Ls j)

/-- A larger exponent is a weaker bound. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem gapLe_mono {Q : QuadraticForm F V} {t : ℕ} {Ls : Fin t → Submodule R V} {G G' : ℕ} (h : GapLe Q Ls G)
    (hGG : G ≤ G') : GapLe Q Ls G' :=
  fun i j r hr x hx => h i j r (Ideal.pow_le_pow_right hGG hr) x hx

/-- **Invariance of the gap bound under a common factor of the scales**: if the scales of `M` for `Q'` are those of
`Ls` for `Q` multiplied by one fractional ideal $J$, the bound `G` carries over. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem gapLe_of_scale_eq_mul {Q : QuadraticForm F V} {Q' : QuadraticForm F W} {t : ℕ} {Ls : Fin t → Submodule R V}
    {M : Fin t → Submodule R W} {G : ℕ} (J : Submodule R F) (hs : ∀ k, scale Q' (M k) = J * scale Q (Ls k))
    (h : GapLe Q Ls G) : GapLe Q' M G := by
  intro i j r hr x hx
  rw [hs i] at hx
  rw [hs j]
  refine Submodule.mul_induction_on hx (fun m hm n hn => ?_) (fun y z hy hz => ?_)
  · rw [← mul_smul_comm]
    exact Submodule.mul_mem_mul hm (h i j r hr n hn)
  · rw [smul_add]; exact add_mem hy hz

/-- **Invariance of the gap bound when the scales are unchanged.** -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem gapLe_of_scale_eq {Q : QuadraticForm F V} {Q' : QuadraticForm F W} {t : ℕ} {Ls : Fin t → Submodule R V}
    {M : Fin t → Submodule R W} {G : ℕ} (hs : ∀ k, scale Q' (M k) = scale Q (Ls k)) (h : GapLe Q Ls G) :
    GapLe Q' M G :=
  gapLe_of_scale_eq_mul 1 (fun k => by rw [hs k, one_mul]) h

/-- Products: adjoining a component `Hs k` of the same scale to every component keeps the bound. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem gapLe_prod {Q : QuadraticForm F V} {Q' : QuadraticForm F W} {t : ℕ} {Ls : Fin t → Submodule R V}
    {Hs : Fin t → Submodule R W} {G : ℕ} (hs : ∀ k, scale (Q.prod Q') ((Ls k).prod (Hs k)) = scale Q (Ls k))
    (h : GapLe Q Ls G) : GapLe (Q.prod Q') (fun k => (Ls k).prod (Hs k)) G :=
  gapLe_of_scale_eq hs h

/-- Scaling the form by $\alpha$ multiplies all scales by $\mathfrak o\alpha$ and keeps the bound. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem gapLe_smul_form {Q : QuadraticForm F V} {t : ℕ} {Ls : Fin t → Submodule R V} {G : ℕ} (α : F)
    (h : GapLe Q Ls G) : GapLe (α • Q) Ls G :=
  gapLe_of_scale_eq_mul (R ∙ α) (fun k => scale_smul_form Q α (Ls k)) h

/-- Moving all components by an isometry $\sigma$ of $(V, Q)$ keeps the bound. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem gapLe_latMap (Q : QuadraticForm F V) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) {K : Submodule R V} {t : ℕ}
    {Ls : Fin t → Submodule R V} (hKle : ∀ k, Ls k ≤ K) {G : ℕ} (h : GapLe Q Ls G) :
    GapLe Q (fun k => latMap σ (Ls k)) G := by
  have hinj : Function.Injective (σ : V →ₗ[F] V) := σ.injective
  have hφ : ∀ z, Q ((σ : V →ₗ[F] V) z) = Q z := fun z => hσ z
  exact gapLe_of_scale_eq (fun k => SuffSub.scale_map Q Q hinj hφ (hKle k)) h

/-- Replacing one component by a modular summand of the same scale keeps the bound. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem gapLe_repl [FiniteDimensional F V] (Q : QuadraticForm F V) {t : ℕ} {Ls : Fin t → Submodule R V}
    {k0 : Fin t} {L' : Submodule R V} (hL'mod : IsModular Q (scale Q (Ls k0)) L') {G : ℕ}
    (h : GapLe Q Ls G) : GapLe Q (Dim4.repl Ls k0 L') G :=
  gapLe_of_scale_eq (Dim4.scale_repl_eq Q hL'mod) h

/-- Passing to a subspace $U$ containing all components keeps the bound. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem gapLe_subLatIn (Q : QuadraticForm F V) {U : Submodule F V} {X : Submodule R V}
    (hX : X ≤ U.restrictScalars R) {t : ℕ} {Ls : Fin t → Submodule R V} (hLs : ∀ k, Ls k ≤ X) {G : ℕ}
    (h : GapLe Q Ls G) : GapLe (SuffSub.QW Q U) (fun k => SuffSub.subLatIn U (Ls k)) G :=
  gapLe_of_scale_eq (fun k => SuffSub.scale_subLatIn Q hX (hLs k)) h

/-- **Re-splitting**: another Jordan splitting of the same finitely generated lattice has the same scales
(O'Meara 91:9), hence the same bound. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem gapLe_resplit {Q : QuadraticForm F V} {t t' : ℕ} {L : Submodule R V} (hfg : L.FG)
    {Ls : Fin t → Submodule R V} {Ks : Fin t' → Submodule R V} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q L Ks) {G : ℕ} (h : GapLe Q Ls G) : GapLe Q Ks G := by
  obtain ⟨ht, hs⟩ := hL.sameJordanType Q hfg hK
  subst ht
  exact gapLe_of_scale_eq (fun k => by
    have := (hs k).1; rw [show Fin.cast rfl k = k from Fin.ext rfl] at this; exact this.symm) h

/-- **Every Jordan splitting of a finitely generated lattice has a gap bound.** The scales are nonzero principal
fractional ideals $\mathfrak o c_i$, and $\mathfrak p^n \subseteq q\,\mathfrak o$ for $n$ the valuation of a denominator
$q$ of $c_i / c_j$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem exists_gapLe (Q : QuadraticForm F V) {L : Submodule R V} (hfg : L.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) : ∃ G, GapLe Q Ls G := by
  have hLk : ∀ i, (Ls i).FG := fun i => FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls i)
  have hgen : ∀ i, ∃ c : F, c ≠ 0 ∧ scale Q (Ls i) = R ∙ c := fun i => by
    obtain ⟨x, -, y, -, h⟩ := exists_scale_eq Q (hLk i)
    exact ⟨bil Q x y, fun h0 => (hL.modular i).1 (by rw [h, h0, span_singleton_eq_bot.mpr rfl]), h⟩
  choose c hc0 hc using hgen
  obtain ⟨ε, hε⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmax : maximalIdeal R = Ideal.span {ε} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ε).1 hε
  have hpair : ∀ i j : Fin t, ∃ n : ℕ, ∀ r ∈ maximalIdeal R ^ n, ∀ x ∈ scale Q (Ls i), r • x ∈ scale Q (Ls j) := by
    intro i j
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := R) (c i / c j)
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      (s := Ideal.span {q}) (by simpa using hq0) hε
    refine ⟨n, fun r hr x hx => ?_⟩
    have hr' : r ∈ Ideal.span {q} := by
      rw [hn, ← Ideal.span_singleton_pow, ← hmax]; exact hr
    obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 hr'
    rw [hc i, Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [hc j, Submodule.mem_span_singleton]
    refine ⟨a' * a * p, ?_⟩
    have hqF : algebraMap R F q ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hq0
    have hcj := hc0 j
    have hci : c i = algebraMap R F p / algebraMap R F q * c j := by
      rw [hpq]; field_simp
    rw [← ha']
    simp only [Algebra.smul_def, map_mul, hci]
    field_simp
  choose n hn using hpair
  refine ⟨Finset.univ.sup fun p : Fin t × Fin t => n p.1 p.2, fun i j r hr x hx => ?_⟩
  exact hn i j r (Ideal.pow_le_pow_right
    (Finset.le_sup (f := fun p : Fin t × Fin t => n p.1 p.2) (Finset.mem_univ (i, j))) hr) x hx

/-- **Dropping the first component lowers the gap bound by one**: for a Jordan splitting, $\mathfrak s_i \subseteq
\mathfrak s_2 \subseteq \mathfrak p\,\mathfrak s_1$ for $i \ge 2$ (O'Meara's numbering). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem gapLe_tail (Q : QuadraticForm F V) {L : Submodule R V} (hfg : L.FG) {m : ℕ}
    {Ls : Fin (m + 2) → Submodule R V} (hL : IsJordanSplitting Q L Ls) {G : ℕ} (hG1 : 1 ≤ G)
    (h : GapLe Q Ls G) : GapLe Q (fun k : Fin (m + 1) => Ls k.succ) (G - 1) := by
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hLk : ∀ i, (Ls i).FG := fun i => FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls i)
  have hgen : ∀ i, ∃ c : F, c ≠ 0 ∧ scale Q (Ls i) = R ∙ c := fun i => by
    obtain ⟨x, -, y, -, h⟩ := exists_scale_eq Q (hLk i)
    exact ⟨bil Q x y, fun h0 => (hL.modular i).1 (by rw [h, h0, span_singleton_eq_bot.mpr rfl]), h⟩
  obtain ⟨c0, -, hc0⟩ := hgen 0
  obtain ⟨c1, -, hc1⟩ := hgen (Fin.succ 0)
  have hlt : scale Q (Ls (Fin.succ 0)) < scale Q (Ls 0) := hL.scale_strictAnti (Fin.succ_pos 0)
  have hmem : c1 ∈ scale Q (Ls 0) := hlt.le (hc1 ▸ Submodule.mem_span_singleton_self c1)
  rw [hc0] at hmem
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  have haM : a ∈ maximalIdeal R := by
    by_contra hna
    have hu : IsUnit a := by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hna
    refine absurd ?_ hlt.not_ge
    rw [hc0, hc1, Submodule.span_singleton_le_iff_mem]
    obtain ⟨u, rfl⟩ := hu
    refine Submodule.mem_span_singleton.2 ⟨↑u⁻¹, ?_⟩
    rw [← ha, smul_smul]
    simp
  intro i j r hr x hx
  have hx1 : x ∈ scale Q (Ls (Fin.succ 0)) :=
    hL.scale_strictAnti.antitone (Fin.succ_le_succ_iff.2 (Fin.zero_le i)) hx
  rw [hc1, Submodule.mem_span_singleton] at hx1
  obtain ⟨b, rfl⟩ := hx1
  have hb : b • c0 ∈ scale Q (Ls 0) := hc0 ▸ Submodule.mem_span_singleton.2 ⟨b, rfl⟩
  have hra : r * a ∈ maximalIdeal R ^ (G' + 1) := by
    rw [pow_succ]; exact Ideal.mul_mem_mul hr haM
  have := h 0 j.succ (r * a) hra (b • c0) hb
  have e : r • b • c1 = (r * a) • b • c0 := by
    rw [← ha, smul_smul, smul_smul, smul_smul]
    congr 1; ring
  rw [e]
  exact this

/-- **A property of the scales that survives a common factor.** `P t s` is a property of the sequence of scales
$\mathfrak s_0, \dots, \mathfrak s_{t-1}$ (`s : Fin t → Submodule R F`, fractional ideals) of a splitting; it is
`ScaleClosed` when it is kept whenever all the scales are multiplied by one fractional ideal $J$. Such properties are
preserved by every reduction of step 2 (adjunctions keep the scales, scaling the form multiplies them all by one
factor). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
def ScaleClosed (P : ∀ t : ℕ, (Fin t → Submodule R F) → Prop) : Prop :=
  ∀ (t : ℕ) (s : Fin t → Submodule R F) (J : Submodule R F), P t s → P t fun k => J * s k

/-- **The gap bound as a property of the scales**: $\mathfrak p^G \mathfrak s_i \subseteq \mathfrak s_j$ for all
components $i, j$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
def gapP (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
    (G : ℕ) : ∀ t : ℕ, (Fin t → Submodule R F) → Prop :=
  fun t s => ∀ i j : Fin t, ∀ r ∈ maximalIdeal R ^ G, ∀ x ∈ s i, r • x ∈ s j

/-- **O'Meara's step 8 configuration cannot occur**: $\mathfrak p\,\mathfrak s_0 \subseteq \mathfrak s_1$ (0-based
indices: the first and second scales of the splitting). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
def firstP (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F] :
    ∀ t : ℕ, (Fin t → Submodule R F) → Prop :=
  fun t s => ∀ i j : Fin t, (i : ℕ) = 0 → (j : ℕ) = 1 → ∀ r ∈ maximalIdeal R, ∀ x ∈ s i, r • x ∈ s j

/-- `GapLe` is the property `gapP` of the sequence of scales. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem gapLe_iff_gapP {Q : QuadraticForm F V} {t : ℕ} {Ls : Fin t → Submodule R V} {G : ℕ} :
    GapLe Q Ls G ↔ gapP R G t (fun k => scale Q (Ls k)) := Iff.rfl

/-- The gap bound is kept when all scales are multiplied by one fractional ideal. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem scaleClosed_gapP (G : ℕ) : ScaleClosed (gapP R (F := F) G) := by
  intro t s J h i j r hr x hx
  refine Submodule.mul_induction_on hx (fun m hm n hn => ?_) (fun y z hy hz => ?_)
  · rw [← mul_smul_comm]
    exact Submodule.mul_mem_mul hm (h i j r hr n hn)
  · rw [smul_add]; exact add_mem hy hz

/-- The condition $\mathfrak p\,\mathfrak s_0 \subseteq \mathfrak s_1$ is kept when all scales are multiplied by one
fractional ideal. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem scaleClosed_firstP : ScaleClosed (firstP R (F := F)) := by
  intro t s J h i j hi hj r hr x hx
  refine Submodule.mul_induction_on hx (fun m hm n hn => ?_) (fun y z hy hz => ?_)
  · rw [← mul_smul_comm]
    exact Submodule.mul_mem_mul hm (h i j hi hj r hr n hn)
  · rw [smul_add]; exact add_mem hy hz

/-- Conjunction of two properties kept under a common factor is kept under a common factor. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem ScaleClosed.and {P P' : ∀ t : ℕ, (Fin t → Submodule R F) → Prop} (h : ScaleClosed P)
    (h' : ScaleClosed P') : ScaleClosed fun t s => P t s ∧ P' t s :=
  fun t s J hs => ⟨h t s J hs.1, h' t s J hs.2⟩

/-- If the scales `s'` are those of `s` multiplied by one fractional ideal $J$, the property carries over. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem ScaleClosed.of_eq_mul {P : ∀ t : ℕ, (Fin t → Submodule R F) → Prop} (hP : ScaleClosed P) {t : ℕ}
    {s s' : Fin t → Submodule R F} (J : Submodule R F) (hs : ∀ k, s' k = J * s k) (h : P t s) : P t s' := by
  have : s' = fun k => J * s k := funext hs
  rw [this]; exact hP t s J h

/-- If the scales `s'` equal those of `s`, the property carries over. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem ScaleClosed.of_eq {P : ∀ t : ℕ, (Fin t → Submodule R F) → Prop} (hP : ScaleClosed P) {t : ℕ}
    {s s' : Fin t → Submodule R F} (hs : ∀ k, s' k = s k) (h : P t s) : P t s' :=
  hP.of_eq_mul 1 (fun k => by rw [hs k, one_mul]) h

end QuadFormsKB.OMeara.Gap
