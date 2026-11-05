/-
# O'Meara 93:28, necessity of (ii), (iii): block bases with norm-generator first vectors

**Setting** (as in `Sec93FMerge.lean`): $R$ a discrete valuation ring with residue field finite and Henselian, $F$ its
fraction field, $(V, Q)$ a quadratic space, $K$ a unimodular lattice with a block base $A(c_1, 0) \perp \cdots \perp
A(c_m, 0)$ (`Merge28.IsBlockBase`).

**Proves** (an auxiliary normalisation, used where `Sec93FNecRepBlocks.lean` needs every $Q(x_k^{(1)})$ to be a norm
generator, while 93:3 only gives blocks $A(c_k, 0)$ with arbitrary $c_k$)
* `exists_normGenerator_blocks`: a unimodular lattice with a block base and norm ideal $\mathfrak o a$ has a block
  base with $\mathfrak o\,Q(x_k^{(1)}) = \mathfrak o a$ for all $k$ (so each $Q(x_k^{(1)})$ is a norm generator).
-/
import QuadFormsKB.Literature.OMeara.Sec93FMerge

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.NecRepDual

open NecBlock Merge28

section Blocks

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- A block: $Q(p_2) = 0$, $B(p_1, p_2) = 1$. -/
def Blk (p : V × V) : Prop := Q p.2 = 0 ∧ bil Q p.1 p.2 = 1

/-- Two pairs are orthogonal. -/
def Perp (p q : V × V) : Prop :=
  bil Q p.1 q.1 = 0 ∧ bil Q p.1 q.2 = 0 ∧ bil Q p.2 q.1 = 0 ∧ bil Q p.2 q.2 = 0

/-- A family of orthogonal blocks. -/
def Blocks {m : ℕ} (z : Fin m → V × V) : Prop :=
  (∀ k, Blk Q (z k)) ∧ ∀ k l, k ≠ l → Perp Q (z k) (z l)

theorem Perp.symm {p q : V × V} (h : Perp Q p q) : Perp Q q p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [bil_comm]; exact h1, by rw [bil_comm]; exact h3, by rw [bil_comm]; exact h2,
    by rw [bil_comm]; exact h4⟩

theorem isBlockBase_iff {K : Submodule R V} {m : ℕ} (x : Fin m → V × V) :
    IsBlockBase Q K x ↔ pairSpan R x = K ∧ Blocks Q x := by
  constructor
  · rintro ⟨hs, h2, h12, h11, h12', h22⟩
    refine ⟨hs, fun k => ⟨h2 k, h12 k⟩, fun k l hkl => ⟨h11 k l hkl, h12' k l hkl, ?_, h22 k l hkl⟩⟩
    rw [bil_comm]; exact h12' l k hkl.symm
  · rintro ⟨hs, hb, hp⟩
    exact ⟨hs, fun k => (hb k).1, fun k => (hb k).2, fun k l h => (hp k l h).1, fun k l h => (hp k l h).2.1,
      fun k l h => (hp k l h).2.2.2⟩

theorem blocks_cons {m : ℕ} (p : V × V) (z : Fin m → V × V) :
    Blocks Q (Fin.cons p z : Fin (m + 1) → V × V) ↔ Blk Q p ∧ Blocks Q z ∧ ∀ k, Perp Q p (z k) := by
  constructor
  · rintro ⟨hb, hp⟩
    refine ⟨by simpa using hb 0, ⟨fun k => by simpa using hb k.succ, fun k l hkl => by
      simpa using hp k.succ l.succ (fun h => hkl (Fin.succ_injective _ h))⟩, fun k => by
      simpa using hp 0 k.succ (Fin.succ_ne_zero k).symm⟩
  · rintro ⟨h0, ⟨hb, hp⟩, hpz⟩
    refine ⟨fun k => ?_, fun k l hkl => ?_⟩
    · refine Fin.cases ?_ (fun k' => ?_) k
      · simpa using h0
      · simpa using hb k'
    · refine Fin.cases (fun hkl => ?_) (fun k' hkl => ?_) k hkl <;>
        refine Fin.cases (fun hkl => ?_) (fun l' hkl => ?_) l hkl
      · exact absurd rfl hkl
      · simpa using hpz l'
      · simpa using (hpz k').symm Q
      · exact by simpa using hp k' l' (fun h => hkl (by rw [h]))

theorem Q_sub' (x y : V) : Q (x - y) = Q x + Q y - 2 * bil Q x y := by
  have h := bil_self Q (x - y)
  rw [bil_sub_left, bil_sub_right, bil_sub_right, bil_comm Q y x, bil_self, bil_self] at h
  linear_combination -h

/-- The elementary move on two blocks $g, h$ with $Q(g_1) = c_0$: $g \mapsto (g_1 - c_0 h_2, g_2 - h_2)$. -/
def mvG (g h : V × V) (c₀ : R) : V × V := (g.1 - c₀ • h.2, g.2 - h.2)

/-- The elementary move on two blocks $g, h$: $h \mapsto (h_1 + g_1, h_2)$. -/
def mvH (g h : V × V) : V × V := (h.1 + g.1, h.2)

theorem move_rel {g h : V × V} {c₀ : R} (hg : Blk Q g) (hh : Blk Q h) (hgh : Perp Q g h)
    (hc : Q g.1 = algebraMap R F c₀) :
    Blk Q (mvG g h c₀) ∧ Blk Q (mvH g h) ∧ Perp Q (mvG g h c₀) (mvH g h) ∧ Q (mvG g h c₀).1 = Q g.1 ∧
      Q (mvH g h).1 = Q h.1 + Q g.1 ∧
      (∀ q, Perp Q g q → Perp Q h q → Perp Q (mvG g h c₀) q ∧ Perp Q (mvH g h) q) := by
  obtain ⟨hg2, hg12⟩ := hg
  obtain ⟨hh2, hh12⟩ := hh
  obtain ⟨p1, p2, p3, p4⟩ := hgh
  have q1 : bil Q g.2 g.1 = 1 := by rw [bil_comm]; exact hg12
  have q2 : bil Q h.2 h.1 = 1 := by rw [bil_comm]; exact hh12
  have r1 : bil Q h.1 g.1 = 0 := by rw [bil_comm]; exact p1
  have r2 : bil Q h.2 g.1 = 0 := by rw [bil_comm]; exact p2
  have r3 : bil Q h.1 g.2 = 0 := by rw [bil_comm]; exact p3
  have r4 : bil Q h.2 g.2 = 0 := by rw [bil_comm]; exact p4
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · show Q (g.2 - h.2) = 0
    rw [Q_sub', hg2, hh2, p4]; ring
  · show bil Q (g.1 - c₀ • h.2) (g.2 - h.2) = 1
    simp only [bil_sub_left, bil_sub_right, bil_rsmul_left, bil_self, hh2, hg12, p2, r4, p4]; ring
  · exact hh2
  · show bil Q (h.1 + g.1) h.2 = 1
    simp only [bil_add_left, hh12, p2]; ring
  · show bil Q (g.1 - c₀ • h.2) (h.1 + g.1) = 0
    simp only [bil_sub_left, bil_add_right, bil_rsmul_left, bil_self, hc, p1, r2, q2, hh12, hg12]; ring
  · show bil Q (g.1 - c₀ • h.2) h.2 = 0
    simp only [bil_sub_left, bil_rsmul_left, bil_self, hh2, p2]; ring
  · show bil Q (g.2 - h.2) (h.1 + g.1) = 0
    simp only [bil_sub_left, bil_add_right, p3, q1, q2, r2, hh12, hg12, hg12]; ring
  · show bil Q (g.2 - h.2) h.2 = 0
    simp only [bil_sub_left, p4, bil_self, hh2]; ring
  · show Q (g.1 - c₀ • h.2) = Q g.1
    rw [Q_sub', Q_rsmul, bil_rsmul_right, hh2, p2]; ring
  · show Q (h.1 + g.1) = Q h.1 + Q g.1
    rw [Q_add, r1]; ring
  · intro q ⟨s1, s2, s3, s4⟩ ⟨t1, t2, t3, t4⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · show bil Q (g.1 - c₀ • h.2) q.1 = 0
      simp only [bil_sub_left, bil_rsmul_left, s1, t3]; ring
    · show bil Q (g.1 - c₀ • h.2) q.2 = 0
      simp only [bil_sub_left, bil_rsmul_left, s2, t4]; ring
    · show bil Q (g.2 - h.2) q.1 = 0
      simp only [bil_sub_left, s3, t3]; ring
    · show bil Q (g.2 - h.2) q.2 = 0
      simp only [bil_sub_left, s4, t4]; ring
    · show bil Q (h.1 + g.1) q.1 = 0
      simp only [bil_add_left, s1, t1]; ring
    · show bil Q (h.1 + g.1) q.2 = 0
      simp only [bil_add_left, s2, t2]; ring
    · exact t3
    · exact t4

theorem mv_span (g h : V × V) (c₀ : R) :
    span R {(mvG g h c₀).1, (mvG g h c₀).2} ⊔ span R {(mvH g h).1, (mvH g h).2} =
      span R {g.1, g.2} ⊔ span R {h.1, h.2} := by
  have key : ∀ (a b c d a' b' c' d' : V),
      a ∈ span R {a', b'} ⊔ span R {c', d'} → b ∈ span R {a', b'} ⊔ span R {c', d'} →
      c ∈ span R {a', b'} ⊔ span R {c', d'} → d ∈ span R {a', b'} ⊔ span R {c', d'} →
      span R {a, b} ⊔ span R {c, d} ≤ span R {a', b'} ⊔ span R {c', d'} := by
    intro a b c d a' b' c' d' ha hb hc hd
    refine sup_le (span_le.2 ?_) (span_le.2 ?_)
    · intro v hv; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl <;> assumption
    · intro v hv; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl <;> assumption
  have m1 : g.1 ∈ span R {g.1, g.2} ⊔ span R {h.1, h.2} := mem_sup_left (subset_span (by simp))
  have m2 : g.2 ∈ span R {g.1, g.2} ⊔ span R {h.1, h.2} := mem_sup_left (subset_span (by simp))
  have m3 : h.1 ∈ span R {g.1, g.2} ⊔ span R {h.1, h.2} := mem_sup_right (subset_span (by simp))
  have m4 : h.2 ∈ span R {g.1, g.2} ⊔ span R {h.1, h.2} := mem_sup_right (subset_span (by simp))
  apply le_antisymm
  · refine key _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
    · exact sub_mem m1 (Submodule.smul_mem _ _ m4)
    · exact sub_mem m2 m4
    · exact add_mem m3 m1
    · exact m4
  · set S := span R {(mvG g h c₀).1, (mvG g h c₀).2} ⊔ span R {(mvH g h).1, (mvH g h).2} with hS
    have n1 : (mvG g h c₀).1 ∈ S := mem_sup_left (subset_span (by simp))
    have n2 : (mvG g h c₀).2 ∈ S := mem_sup_left (subset_span (by simp))
    have n3 : (mvH g h).1 ∈ S := mem_sup_right (subset_span (by simp))
    have n4 : (mvH g h).2 ∈ S := mem_sup_right (subset_span (by simp))
    refine key _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
    · have : g.1 = (mvG g h c₀).1 + c₀ • (mvH g h).2 := by simp [mvG, mvH]
      rw [this]; exact add_mem n1 (Submodule.smul_mem _ _ n4)
    · have : g.2 = (mvG g h c₀).2 + (mvH g h).2 := by simp [mvG, mvH]
      rw [this]; exact add_mem n2 n4
    · have : h.1 = (mvH g h).1 - ((mvG g h c₀).1 + c₀ • (mvH g h).2) := by simp [mvG, mvH]
      rw [this]; exact sub_mem n3 (add_mem n1 (Submodule.smul_mem _ _ n4))
    · exact n4

theorem span_eq_of_unit {u : R} (hu : IsUnit u) (c : F) : R ∙ (algebraMap R F u * c) = R ∙ c := by
  obtain ⟨w, rfl⟩ := hu
  refine span_singleton_eq_span_singleton.mpr ⟨w⁻¹, ?_⟩
  rw [Units.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul]
  simp

/-- One step: after possibly moving, the second block's first vector generates the same ideal as the first's. -/
theorem step_exists {g h : V × V} {c₀ : R} (hg : Blk Q g) (hh : Blk Q h) (hgh : Perp Q g h)
    (hc : Q g.1 = algebraMap R F c₀) (hr : ∃ r : R, Q h.1 = algebraMap R F r * Q g.1) :
    ∃ g1 h1 : V × V, Blk Q g1 ∧ Blk Q h1 ∧ Perp Q g1 h1 ∧ Q g1.1 = Q g.1 ∧ R ∙ Q h1.1 = R ∙ Q g.1 ∧
      span R {g1.1, g1.2} ⊔ span R {h1.1, h1.2} = span R {g.1, g.2} ⊔ span R {h.1, h.2} ∧
      ∀ q, Perp Q g q → Perp Q h q → Perp Q g1 q ∧ Perp Q h1 q := by
  by_cases hgen : R ∙ Q h.1 = R ∙ Q g.1
  · exact ⟨g, h, hg, hh, hgh, rfl, hgen, rfl, fun q a b => ⟨a, b⟩⟩
  · obtain ⟨r, hr⟩ := hr
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := move_rel Q hg hh hgh hc
    have hru : ¬ IsUnit r := fun hu => hgen (by rw [hr]; exact span_eq_of_unit hu _)
    have hr1 : IsUnit (r + 1) := by
      have : (r + 1) + (-r) = 1 := by ring
      rcases isUnit_or_isUnit_of_add_one this with h | h
      · exact h
      · exact absurd (by simpa using h.neg) hru
    refine ⟨mvG g h c₀, mvH g h, b1, b2, b3, b4, ?_, mv_span g h c₀, b6⟩
    rw [b5, hr, ← span_eq_of_unit hr1 (Q g.1)]
    congr 1
    simp only [map_add, map_one]; ring

/-- Perpendicularity of a vector to a pair. -/
def PerpV (v : V) (p : V × V) : Prop := bil Q v p.1 = 0 ∧ bil Q v p.2 = 0

theorem normalize_head : ∀ (m : ℕ) (g : V × V) (c₀ : R) (rest : Fin m → V × V),
    Blocks Q (Fin.cons g rest : Fin (m + 1) → V × V) → Q g.1 = algebraMap R F c₀ →
    (∀ k, ∃ r : R, Q (rest k).1 = algebraMap R F r * Q g.1) →
    ∃ (g' : V × V) (rest' : Fin m → V × V), Blocks Q (Fin.cons g' rest' : Fin (m + 1) → V × V) ∧
      span R {g'.1, g'.2} ⊔ pairSpan R rest' = span R {g.1, g.2} ⊔ pairSpan R rest ∧ Q g'.1 = Q g.1 ∧
      (∀ k, R ∙ Q (rest' k).1 = R ∙ Q g.1) ∧
      ∀ v, PerpV Q v g → (∀ k, PerpV Q v (rest k)) → PerpV Q v g' ∧ ∀ k, PerpV Q v (rest' k) := by
  intro m
  induction m with
  | zero =>
    intro g c₀ rest hb hc hr
    refine ⟨g, rest, hb, rfl, rfl, fun k => k.elim0, fun v h1 _ => ⟨h1, fun k => k.elim0⟩⟩
  | succ m ih =>
    intro g c₀ rest hb hc hr
    obtain ⟨hg, hbr, hperp⟩ := (blocks_cons Q g rest).1 hb
    rw [← Fin.cons_self_tail rest] at hbr hperp hr ⊢
    obtain ⟨hh, hb0, hperp0⟩ := (blocks_cons Q (rest 0) (Fin.tail rest)).1 hbr
    obtain ⟨g1, h1, k1, k2, k3, k4, k5, k6, k7⟩ :=
      step_exists Q hg hh (by simpa using hperp 0) hc (by simpa using hr 0)
    have hperp' : ∀ k, Perp Q g1 (Fin.tail rest k) ∧ Perp Q h1 (Fin.tail rest k) := fun k =>
      k7 _ (by simpa [Fin.tail] using hperp k.succ) (hperp0 k)
    have hb1 : Blocks Q (Fin.cons g1 (Fin.tail rest) : Fin (m + 1) → V × V) :=
      (blocks_cons Q _ _).2 ⟨k1, hb0, fun k => (hperp' k).1⟩
    obtain ⟨g', rest0', hb', hsp, hq, hgen, hv⟩ := ih g1 c₀ (Fin.tail rest) hb1 (by rw [k4]; exact hc)
      (fun k => by
        have := hr k.succ
        simp only [Fin.tail, Fin.cons_succ] at this ⊢
        rw [k4]; exact this)
    -- orthogonality of `h1` to `g'` and `rest0'`
    have hh1 : ∀ w, (PerpV Q w g1 ∧ ∀ k, PerpV Q w (Fin.tail rest k)) → PerpV Q w g' ∧ ∀ k, PerpV Q w (rest0' k) :=
      fun w hw => hv w hw.1 hw.2
    have k3' := k3.symm Q
    have hp1 : PerpV Q h1.1 g1 ∧ ∀ k, PerpV Q h1.1 (Fin.tail rest k) :=
      ⟨⟨k3'.1, k3'.2.1⟩, fun k => ⟨(hperp' k).2.1, (hperp' k).2.2.1⟩⟩
    have hp2 : PerpV Q h1.2 g1 ∧ ∀ k, PerpV Q h1.2 (Fin.tail rest k) :=
      ⟨⟨k3'.2.2.1, k3'.2.2.2⟩, fun k => ⟨(hperp' k).2.2.2.1, (hperp' k).2.2.2.2⟩⟩
    have e1 := hh1 _ hp1
    have e2 := hh1 _ hp2
    have hbg' := (blocks_cons Q g' rest0').1 hb'
    have hh1g' : Perp Q h1 g' := ⟨e1.1.1, e1.1.2, e2.1.1, e2.1.2⟩
    have hh1r : ∀ k, Perp Q h1 (rest0' k) := fun k => ⟨(e1.2 k).1, (e1.2 k).2, (e2.2 k).1, (e2.2 k).2⟩
    refine ⟨g', Fin.cons h1 rest0', ?_, ?_, ?_, ?_, ?_⟩
    · refine (blocks_cons Q _ _).2 ⟨hbg'.1, (blocks_cons Q _ _).2 ⟨k2, hbg'.2.1, hh1r⟩, fun k => ?_⟩
      refine Fin.cases ?_ (fun k' => ?_) k
      · simpa using hh1g'.symm Q
      · simpa using hbg'.2.2 k'
    · rw [pairSpan_cons, pairSpan_cons, ← sup_assoc, sup_comm (span R {g'.1, g'.2}), sup_assoc, hsp,
        ← sup_assoc, sup_comm (span R {h1.1, h1.2}) (span R {g1.1, g1.2}), k6, sup_assoc]
    · rw [hq, k4]
    · intro k
      refine Fin.cases ?_ (fun k' => ?_) k
      · simpa using k5
      · simpa [k4] using hgen k'
    · intro v hvg hvr
      have hvh : PerpV Q v (rest 0) := by simpa using hvr 0
      have hvt : ∀ k, PerpV Q v (Fin.tail rest k) := fun k => by simpa [Fin.tail] using hvr k.succ
      have pv : ∀ (p : V × V), PerpV Q v p ↔ Perp Q p (v, v) := fun p => by
        simp only [PerpV, Perp]
        rw [bil_comm Q p.1 v, bil_comm Q p.2 v]; tauto
      have := k7 (v, v) ((pv g).1 hvg) ((pv (rest 0)).1 hvh)
      have hvg1 : PerpV Q v g1 := (pv g1).2 this.1
      have hvh1 : PerpV Q v h1 := (pv h1).2 this.2
      obtain ⟨u1, u2⟩ := hv v hvg1 hvt
      refine ⟨u1, fun k => ?_⟩
      refine Fin.cases ?_ (fun k' => ?_) k
      · simpa using hvh1
      · simpa using u2 k'

theorem blocks_comp {m : ℕ} {z : Fin m → V × V} (hz : Blocks Q z) (e : Fin m ≃ Fin m) :
    Blocks Q (z ∘ e) :=
  ⟨fun k => hz.1 (e k), fun k l hkl => hz.2 (e k) (e l) (fun h => hkl (e.injective h))⟩

theorem pairSpan_comp {m : ℕ} (z : Fin m → V × V) (e : Fin m ≃ Fin m) : pairSpan R (z ∘ e) = pairSpan R z := by
  unfold pairSpan
  have h1 : Set.range (fun k => ((z ∘ e) k).1) = Set.range (fun k => (z k).1) :=
    e.surjective.range_comp (fun k => (z k).1)
  have h2 : Set.range (fun k => ((z ∘ e) k).2) = Set.range (fun k => (z k).2) :=
    e.surjective.range_comp (fun k => (z k).2)
  rw [h1, h2]

/-- Case A: the first block's `Q (z 0).1` generates the ideal containing all the others. -/
theorem caseA {m : ℕ} (z : Fin (m + 1) → V × V) (hz : Blocks Q z) {c₀ : R}
    (hc : Q (z 0).1 = algebraMap R F c₀) (hr : ∀ k, ∃ r : R, Q (z k).1 = algebraMap R F r * Q (z 0).1) :
    ∃ z' : Fin (m + 1) → V × V, Blocks Q z' ∧ pairSpan R z' = pairSpan R z ∧
      ∀ k, R ∙ Q (z' k).1 = R ∙ Q (z 0).1 := by
  have hz' : Blocks Q (Fin.cons (z 0) (Fin.tail z) : Fin (m + 1) → V × V) := by
    rwa [Fin.cons_self_tail]
  obtain ⟨g', rest', hb, hsp, hq, hgen, -⟩ := normalize_head Q m (z 0) c₀ (Fin.tail z) hz' hc
    (fun k => by simpa [Fin.tail] using hr k.succ)
  refine ⟨Fin.cons g' rest', hb, ?_, ?_⟩
  · rw [pairSpan_cons, hsp, ← pairSpan_cons, Fin.cons_self_tail]
  · intro k
    refine Fin.cases ?_ (fun k' => ?_) k
    · simp [hq]
    · simpa using hgen k'

end Blocks

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Block bases with norm-generator first vectors.** A lattice $K$ of scale $\mathfrak o$ with a block base
$A(c_1, 0) \perp \cdots \perp A(c_m, 0)$ and norm ideal $\mathfrak nK = \mathfrak o a$ has a block base
(of the same lattice) with $\mathfrak o\,Q(x_k^{(1)}) = \mathfrak o a$ for every $k$; each $Q(x_k^{(1)})$ is then a
norm generator of $K$ (it lies in $\mathfrak gK$ since $x_k^{(1)} \in K$). Proof: $\mathfrak nK$ is generated by $2$ and
the $c_k$; in a discrete valuation ring one of these generates it. If it is $2$, replace $x_k^{(1)}$ by
$x_k^{(1)} + \beta_k x_k^{(2)}$; if it is some $c_l$, mix the other blocks with block $l$ (`normalize_head`). -/
theorem exists_normGenerator_blocks {K : Submodule R V} (hKU : scale Q K = 1) {m : ℕ} {x : Fin m → V × V}
    (hx : IsBlockBase Q K x) {a : F} (ha : R ∙ a = normIdeal Q K) :
    ∃ x' : Fin m → V × V, IsBlockBase Q K x' ∧ ∀ k, R ∙ Q (x' k).1 = R ∙ a := by
  obtain ⟨hspan, hbl⟩ := (isBlockBase_iff Q x).1 hx
  have hmem1 : ∀ k, (x k).1 ∈ K := fun k => hspan ▸ subset_span (Or.inl ⟨k, rfl⟩)
  have hmem2 : ∀ k, (x k).2 ∈ K := fun k => hspan ▸ subset_span (Or.inr ⟨k, rfl⟩)
  have h1K : (1 : F) ∈ scale Q K := by rw [hKU]; exact Submodule.mem_one.2 ⟨1, by simp⟩
  have hbilR : ∀ v ∈ K, ∀ w ∈ K, ∃ r : R, bil Q v w = algebraMap R F r := fun v hv w hw => by
    have := bil_mem_scale Q hv hw
    rw [hKU] at this
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 this
    exact ⟨r, hr.symm⟩
  -- the generators of the norm ideal
  set f : Option (Fin m) → F := fun i => i.elim 2 (fun k => Q (x k).1) with hf
  set I : Submodule R F := span R (Set.range f) with hI
  have hfI : ∀ i, f i ∈ I := fun i => subset_span ⟨i, rfl⟩
  have h2I : (2 : F) ∈ I := hfI none
  have hQI : ∀ v ∈ K, Q v ∈ I := by
    intro v hv
    rw [← hspan] at hv
    refine Submodule.span_induction (p := fun v _ => Q v ∈ I) ?_ ?_ ?_ ?_ hv
    · rintro v (⟨k, rfl⟩ | ⟨k, rfl⟩)
      · exact hfI (some k)
      · rw [(hbl.1 k).1]; exact zero_mem _
    · rw [QuadraticMap.map_zero]; exact zero_mem _
    · intro v w hv hw hQv hQw
      have hvK : v ∈ K := hspan ▸ hv
      have hwK : w ∈ K := hspan ▸ hw
      obtain ⟨r, hr⟩ := hbilR v hvK w hwK
      have h2r : 2 * algebraMap R F r ∈ I := by
        have : 2 * algebraMap R F r = r • (2 : F) := by rw [Algebra.smul_def]; ring
        rw [this]; exact Submodule.smul_mem _ _ h2I
      have hsum := add_mem (add_mem hQv hQw) h2r
      rw [Q_add, hr]
      convert hsum using 1
      ring
    · intro r v hv hQv
      rw [Q_rsmul]
      have : algebraMap R F r ^ 2 * Q v = (r ^ 2) • Q v := by rw [Algebra.smul_def]; simp
      rw [this]; exact Submodule.smul_mem _ _ hQv
  have hnI : normIdeal Q K ≤ I := by
    rw [normIdeal_eq_span_normGroup, span_le]
    rintro _ ⟨v, hv, c, hc, rfl⟩
    rw [hKU] at hc
    obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hc
    refine add_mem (hQI v hv) ?_
    have : 2 * algebraMap R F r = r • (2 : F) := by rw [Algebra.smul_def]; ring
    rw [this]; exact Submodule.smul_mem _ _ h2I
  have hfn : ∀ i, f i ∈ normIdeal Q K := by
    intro i
    rcases i with _ | k
    · show (2 : F) ∈ normIdeal Q K
      have h := two_mul_mem_normGroup Q h1K
      rw [mul_one] at h
      exact normGroup_subset_normIdeal Q K h
    · exact normGroup_subset_normIdeal Q K (Q_mem_normGroup Q (hmem1 k))
  have hfa : ∀ i, f i ∈ R ∙ a := fun i => ha ▸ hfn i
  have h2a : (2 : F) ∈ R ∙ a := hfa none
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Submodule.span_singleton_eq_bot.2 rfl] at h2a
    have : (2 : F) = 0 := by simpa using h2a
    exact (isUnit_of_invertible (2 : F)).ne_zero this
  have haI : a ∈ I := hnI (ha ▸ Submodule.mem_span_singleton_self a)
  -- some generator generates
  obtain ⟨c, hcsum⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 haI
  have hu : ∀ i, ∃ u : R, u • a = f i := fun i => Submodule.mem_span_singleton.1 (hfa i)
  choose u hu using hu
  have hone : ∑ i, c i * u i = 1 := by
    have : (∑ i, c i * u i) • a = (1 : R) • a := by
      rw [Finset.sum_smul, one_smul]
      conv_rhs => rw [← hcsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hu i, smul_smul]
    exact smul_left_injective R ha0 this
  have hex : ∃ i, IsUnit (c i * u i) := by
    by_contra hcon
    push Not at hcon
    have : (1 : R) ∈ maximalIdeal R := by
      rw [← hone]
      exact Ideal.sum_mem _ fun i _ => (mem_maximalIdeal _).2 (hcon i)
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
  obtain ⟨i₀, hi₀⟩ := hex
  have hu₀ : IsUnit (u i₀) := isUnit_of_mul_isUnit_right hi₀
  have hgen : R ∙ f i₀ = R ∙ a := by
    rw [← hu i₀, Algebra.smul_def]; exact span_eq_of_unit hu₀ a
  rcases i₀ with _ | l
  · -- the norm ideal is generated by `2`
    have h2gen : R ∙ (2 : F) = R ∙ a := hgen
    have hck : ∀ k, ∃ r : R, Q (x k).1 = algebraMap R F r * 2 := fun k => by
      have : Q (x k).1 ∈ R ∙ (2 : F) := h2gen ▸ hfa (some k)
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
      exact ⟨r, by rw [← hr, Algebra.smul_def]⟩
    choose r hr using hck
    let x' : Fin m → V × V := fun k => ((x k).1 + (1 - r k) • (x k).2, (x k).2)
    have hx2 : ∀ k, bil Q (x k).2 (x k).2 = 0 := fun k => by rw [bil_self]; exact (hbl.1 k).1
    refine ⟨x', ?_, fun k => ?_⟩
    · rw [isBlockBase_iff]
      refine ⟨?_, fun k => ⟨(hbl.1 k).1, ?_⟩, fun k l hkl => ?_⟩
      · apply le_antisymm
        · refine span_le.2 ?_
          rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
          · exact add_mem (hmem1 k) (K.smul_mem _ (hmem2 k))
          · exact hmem2 k
        · rw [← hspan]
          refine span_le.2 ?_
          rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
          · have : (x k).1 = (x' k).1 - (1 - r k) • (x' k).2 := by simp [x']
            show (x k).1 ∈ pairSpan R x'
            rw [this]
            exact sub_mem (subset_span (Or.inl ⟨k, rfl⟩)) (Submodule.smul_mem _ _ (subset_span (Or.inr ⟨k, rfl⟩)))
          · exact subset_span (Or.inr ⟨k, rfl⟩)
      · show bil Q ((x k).1 + (1 - r k) • (x k).2) (x k).2 = 1
        rw [bil_add_left, bil_rsmul_left, hx2, (hbl.1 k).2]; ring
      · obtain ⟨p1, p2, p3, p4⟩ := hbl.2 k l hkl
        refine ⟨?_, ?_, ?_, ?_⟩
        · show bil Q ((x k).1 + (1 - r k) • (x k).2) ((x l).1 + (1 - r l) • (x l).2) = 0
          simp only [bil_add_left, bil_add_right, bil_rsmul_left, bil_rsmul_right, p1, p2, p3, p4]; ring
        · show bil Q ((x k).1 + (1 - r k) • (x k).2) (x l).2 = 0
          simp only [bil_add_left, bil_rsmul_left, p2, p4]; ring
        · show bil Q (x k).2 ((x l).1 + (1 - r l) • (x l).2) = 0
          simp only [bil_add_right, bil_rsmul_right, p3, p4]; ring
        · exact p4
    · show R ∙ Q ((x k).1 + (1 - r k) • (x k).2) = R ∙ a
      rw [Q_add, Q_rsmul, bil_rsmul_right, (hbl.1 k).1, hr k, (hbl.1 k).2]
      rw [← h2gen]
      congr 1
      simp only [map_sub, map_one]; ring
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := l.pos; omega⟩
    have hgl : R ∙ Q (x l).1 = R ∙ a := hgen
    obtain ⟨c₀, hc₀⟩ := hbilR (x l).1 (hmem1 l) (x l).1 (hmem1 l)
    rw [bil_self] at hc₀
    let e : Fin (m' + 1) ≃ Fin (m' + 1) := Equiv.swap 0 l
    have hz : Blocks Q (x ∘ e) := blocks_comp Q hbl e
    have hz0 : (x ∘ e) 0 = x l := by simp [e]
    have hr : ∀ k, ∃ r : R, Q ((x ∘ e) k).1 = algebraMap R F r * Q ((x ∘ e) 0).1 := fun k => by
      have : Q ((x ∘ e) k).1 ∈ R ∙ Q (x l).1 := hgl ▸ hfa (some (e k))
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
      exact ⟨r, by rw [hz0, ← hr, Algebra.smul_def]⟩
    obtain ⟨z', hz', hsp, hg⟩ := caseA Q (x ∘ e) hz (c₀ := c₀) (by rw [hz0]; exact hc₀) hr
    refine ⟨z', ?_, fun k => ?_⟩
    · rw [isBlockBase_iff]; exact ⟨by rw [hsp, pairSpan_comp, hspan], hz'⟩
    · rw [hg k, hz0]; exact hgl

end Main

end QuadFormsKB.OMeara.NecRepDual
