/-
# O'Meara 93:28, necessity, step 1 for a first component with $m$ blocks $A(c, 0)$

**Setting** (as in `Sec93FNecBase.lean`). O'Meara's special case has $FL_1$ $4$-dimensional hyperbolic; his reduction
reaches it by cancelling hyperbolic planes (93:14). Here the computation of `nec_base_disc` is done for a first
component $L_1$ with a base of any number $m$ of blocks $A(c_k, 0)$, by induction on $m$, which makes the cancellation
unnecessary.

**Proves**
* `pairSpan`: the lattice spanned by a family of pairs of vectors;
* `block_disc`: an abstract form of the computation of p. 269: a family of $m$ pairs in a unimodular lattice whose
  matrix is congruent to $A(c_1, 0) \perp \cdots \perp A(c_m, 0)$ (diagonal entries in $\mathfrak g_1$ resp.
  $\mathfrak g_2$, off-diagonal entries $\equiv 1$ resp. $0 \bmod \mathfrak s_2$) spans a lattice with
  $(-1)^m d \cong 1 \bmod \mathfrak f_1$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FNecBase
import QuadFormsKB.Literature.OMeara.Sec93FTransfer

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.NecBlock

open Sat93 Arith28 NecBase Transfer28

section Block

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

variable (R) in
/-- The lattice spanned by the vectors of a family of pairs. -/
def pairSpan {m : ℕ} (z : Fin m → V × V) : Submodule R V :=
  span R (Set.range (fun k => (z k).1) ∪ Set.range (fun k => (z k).2))

/-- The hypotheses on a family of pairs `z` in the computation of p. 269: all vectors in `K₁`,
$Q(z_k^{(1)}) \in \mathfrak g_1$, $Q(z_k^{(2)}) \in \mathfrak g_2$, $B(z_k^{(1)}, z_k^{(2)}) \equiv 1$ and all
cross products $\equiv 0 \bmod \mathfrak s_2$. -/
structure BlockData (K₁ : Submodule R V) (s₂ : Submodule R F) (g₁ g₂ : AddSubgroup F) {m : ℕ}
    (z : Fin m → V × V) : Prop where
  mem₁ : ∀ k, (z k).1 ∈ K₁
  mem₂ : ∀ k, (z k).2 ∈ K₁
  q₁ : ∀ k, Q (z k).1 ∈ g₁
  q₂ : ∀ k, Q (z k).2 ∈ g₂
  b : ∀ k, bil Q (z k).1 (z k).2 - 1 ∈ s₂
  c₁₁ : ∀ k l, k ≠ l → bil Q (z k).1 (z l).1 ∈ s₂
  c₁₂ : ∀ k l, k ≠ l → bil Q (z k).1 (z l).2 ∈ s₂
  c₂₂ : ∀ k l, k ≠ l → bil Q (z k).2 (z l).2 ∈ s₂

/-- `Q (y + v) = Q y - Q v` when `y + v ⊥ v`. -/
theorem Q_add_of_orth {y v : V} (h : bil Q (y + v) v = 0) : Q (y + v) = Q y - Q v := by
  rw [bil_add_left, bil_self] at h
  rw [Q_add]; linear_combination 2 * h

/-- Two orthogonal spans: if every generator of `S` is orthogonal to every generator of `T`. -/
theorem orth_span_span {S T : Set V} (h : ∀ s ∈ S, ∀ t ∈ T, bil Q s t = 0) :
    ∀ x ∈ span R S, ∀ y ∈ span R T, bil Q x y = 0 := by
  intro x hx y hy
  have h1 : ∀ s ∈ S, ∀ y ∈ span R T, bil Q s y = 0 := fun s hs =>
    Uni93.bil_zero_on_span Q (fun t ht => h s hs t ht)
  have h2 : ∀ s ∈ S, bil Q y s = 0 := fun s hs => by rw [bil_comm]; exact h1 s hs y hy
  rw [bil_comm]; exact Uni93.bil_zero_on_span Q h2 x hx

theorem range_pair (a b : V) : Set.range ![a, b] = {a, b} := by
  ext v; simp [eq_comm, or_comm]

end Block

section Induction

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **The computation of O'Meara 1963, p. 269, for $m$ blocks** (by induction on $m$; orthogonalize the remaining
pairs against the first with `exists_orth_pair`). Under the standing hypotheses on $\mathfrak s_2$, $\mathfrak g_1$,
$\mathfrak g_2$ and the ideal $\mathfrak a$ of `key` (which is `sqEquivMod_sq_add_mul` for $\mathfrak a =
\mathfrak f_1$), a family of $m$ pairs with `BlockData` spans a lattice with a base of discriminant $d$,
$(-1)^m d \cong 1 \bmod \mathfrak a$. -/
theorem block_disc {K₁ : Submodule R V} (hK1 : ∀ u ∈ K₁, ∀ v ∈ K₁, ∃ r : R, algebraMap R F r = bil Q u v)
    {s₂ : Submodule R F} (hs₂R : ∀ z ∈ s₂, ∃ r ∈ maximalIdeal R, algebraMap R F r = z)
    {g₁ g₂ : AddSubgroup F} (hg₂₁ : g₂ ≤ g₁) (hsq₂ : ∀ x ∈ g₂, ∀ r : R, algebraMap R F r ^ 2 * x ∈ g₂)
    (h2s : ∀ z ∈ s₂, 2 * z ∈ g₂) (hsg : ∀ z ∈ s₂, ∀ x ∈ g₁, z ^ 2 * x ∈ g₂) {X : Submodule R F}
    (key : ∀ c : R, c ∈ maximalIdeal R → ∀ α ∈ g₁, ∀ β ∈ g₂,
      SqEquivMod X ((1 - algebraMap R F c) ^ 2 + α * β) 1) :
    ∀ (m : ℕ) (z : Fin m → V × V), BlockData Q K₁ s₂ g₁ g₂ z →
      ∃ e : Basis (Fin (2 * m)) R (pairSpan R z),
        SqEquivMod X ((-1) ^ m * (gram Q fun i => (e i : V)).det) 1 := by
  classical
  have hs₂R' : ∀ z ∈ s₂, ∃ r : R, algebraMap R F r = z := fun z hz => by
    obtain ⟨r, -, hr⟩ := hs₂R z hz; exact ⟨r, hr⟩
  -- `a • u ∈ 𝔰₂` for `u ∈ 𝔰₂` and `a` in `𝔬`-valued positions
  have hsmul : ∀ {x y : F}, x ∈ s₂ → (∃ r : R, algebraMap R F r = y) → x * y ∈ s₂ := by
    rintro x y hx ⟨r, rfl⟩
    rw [mul_comm, ← Algebra.smul_def]; exact smul_mem _ _ hx
  intro m
  induction m with
  | zero =>
    intro z _
    have h0 : pairSpan R z = ⊥ := by
      rw [pairSpan, Set.range_eq_empty, Set.range_eq_empty, Set.union_empty, span_empty]
    refine ⟨((Basis.empty (⊥ : Submodule R V) : Basis (Fin 0) R _).map (LinearEquiv.ofEq _ _ h0.symm)).reindex
      (finCongr (by simp)), ?_⟩
    have : IsEmpty (Fin (2 * 0)) := ⟨fun i => absurd i.2 (by simp)⟩
    rw [Matrix.det_isEmpty, pow_zero, one_mul]
    exact SqEquivMod.refl X 1
  | succ m ih =>
    intro z hz
    set p := z 0 with hpdef
    -- the first pair
    obtain ⟨A, hA⟩ := hK1 _ (hz.mem₁ 0) _ (hz.mem₁ 0)
    obtain ⟨Bv, hBv⟩ := hK1 _ (hz.mem₁ 0) _ (hz.mem₂ 0)
    obtain ⟨C, hC⟩ := hK1 _ (hz.mem₂ 0) _ (hz.mem₂ 0)
    rw [bil_self] at hA hC
    obtain ⟨c, hcm, hc⟩ := hs₂R _ (neg_mem (hz.b 0))
    have hbil : bil Q p.1 p.2 = 1 - algebraMap R F c := by rw [hc]; ring
    have hp : SqEquivMod X (bil Q p.1 p.2 ^ 2 - Q p.1 * Q p.2) 1 := by
      have := key c hcm (Q p.1) (hz.q₁ 0) (-Q p.2) (neg_mem (hz.q₂ 0))
      convert this using 1; rw [hbil]; ring
    have hunit : IsUnit (A * C - Bv ^ 2) := by
      obtain ⟨⟨u, hu, hu'⟩, -⟩ := hp
      rw [mul_one] at hu'
      have : A * C - Bv ^ 2 = -u := IsFractionRing.injective R F (by
        rw [map_sub, map_mul, map_pow, map_neg, hA, hC, hBv]; linear_combination -hu')
      rw [this]; exact hu.neg
    have hd2 : (A * C - Bv ^ 2 : R) ≠ 0 := hunit.ne_zero
    have hd2F : Q p.1 * Q p.2 - bil Q p.1 p.2 ^ 2 ≠ 0 := by
      rw [← hA, ← hC, ← hBv, ← map_mul, ← map_pow, ← map_sub]
      exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hd2
    -- orthogonalize the other pairs against the first
    have hne : ∀ k : Fin m, k.succ ≠ 0 := fun k => Fin.succ_ne_zero k
    obtain ⟨r₀, r₁, hr₀, hr₁, ho₀, ho₁⟩ : ∃ r₀ r₁ : Fin m → R, (∀ k, algebraMap R F (r₀ k) ∈ s₂) ∧
        (∀ k, algebraMap R F (r₁ k) ∈ s₂) ∧
        (∀ k, bil Q ((z k.succ).1 + r₀ k • p.1 + r₁ k • p.2) p.1 = 0) ∧
        (∀ k, bil Q ((z k.succ).1 + r₀ k • p.1 + r₁ k • p.2) p.2 = 0) := by
      choose r₀ r₁ h1 h2 h3 h4 using fun k : Fin m => exists_orth_pair Q hA.symm hBv.symm hC.symm hunit
        (hz.c₁₁ k.succ 0 (hne k)) (hz.c₁₂ k.succ 0 (hne k)) hs₂R'
      exact ⟨r₀, r₁, h1, h2, h3, h4⟩
    obtain ⟨r₂, r₃, hr₂, hr₃, ho₂, ho₃⟩ : ∃ r₂ r₃ : Fin m → R, (∀ k, algebraMap R F (r₂ k) ∈ s₂) ∧
        (∀ k, algebraMap R F (r₃ k) ∈ s₂) ∧
        (∀ k, bil Q ((z k.succ).2 + r₂ k • p.1 + r₃ k • p.2) p.1 = 0) ∧
        (∀ k, bil Q ((z k.succ).2 + r₂ k • p.1 + r₃ k • p.2) p.2 = 0) := by
      choose r₂ r₃ h1 h2 h3 h4 using fun k : Fin m => exists_orth_pair Q hA.symm hBv.symm hC.symm hunit
        (by rw [bil_comm]; exact hz.c₁₂ 0 k.succ (hne k).symm) (hz.c₂₂ k.succ 0 (hne k)) hs₂R'
      exact ⟨r₂, r₃, h1, h2, h3, h4⟩
    set w : Fin m → V × V := fun k =>
      ((z k.succ).1 + r₀ k • p.1 + r₁ k • p.2, (z k.succ).2 + r₂ k • p.1 + r₃ k • p.2) with hw
    -- facts about the corrections `a • p₁ + b • p₂`
    have hcorrK : ∀ a b : R, a • p.1 + b • p.2 ∈ K₁ := fun a b =>
      add_mem (smul_mem _ _ (hz.mem₁ 0)) (smul_mem _ _ (hz.mem₂ 0))
    have hcorrB : ∀ a b : R, algebraMap R F a ∈ s₂ → algebraMap R F b ∈ s₂ → ∀ t ∈ K₁,
        bil Q (a • p.1 + b • p.2) t ∈ s₂ := by
      intro a b ha hb t ht
      rw [bil_add_left, bil_rsmul_left, bil_rsmul_left]
      exact add_mem (hsmul ha (hK1 _ (hz.mem₁ 0) _ ht)) (hsmul hb (hK1 _ (hz.mem₂ 0) _ ht))
    have hcorrQ : ∀ a b : R, algebraMap R F a ∈ s₂ → Q (a • p.1 + b • p.2) ∈ g₂ := by
      intro a b ha
      rw [Q_add, ← algebraMap_smul F a p.1, ← algebraMap_smul F b p.2, QuadraticMap.map_smul,
        QuadraticMap.map_smul, bil_smul_left, bil_smul_right]
      refine add_mem (add_mem ?_ ?_) ?_
      · rw [← pow_two]; exact hsg _ ha _ (hz.q₁ 0)
      · have : algebraMap R F a * (algebraMap R F b * bil Q p.1 p.2) ∈ s₂ := by
          refine hsmul ha ?_
          obtain ⟨r, hr⟩ := hK1 _ (hz.mem₁ 0) _ (hz.mem₂ 0)
          exact ⟨b * r, by rw [map_mul, hr]⟩
        exact h2s _ this
      · rw [← pow_two]; exact hsq₂ _ (hz.q₂ 0) b
    have horth : ∀ {y : V} {a b : R}, bil Q (y + a • p.1 + b • p.2) p.1 = 0 →
        bil Q (y + a • p.1 + b • p.2) p.2 = 0 → ∀ a' b' : R, bil Q (y + a • p.1 + b • p.2) (a' • p.1 + b' • p.2) = 0 := by
      intro y a b h1 h2 a' b'
      rw [bil_add_right, bil_rsmul_right, bil_rsmul_right, h1, h2]; ring
    have hassoc : ∀ (y : V) (a b : R), y + a • p.1 + b • p.2 = y + (a • p.1 + b • p.2) := fun y a b => by
      rw [add_assoc]
    -- `B(w, t) = B(y, t) + B(correction, t)`
    have hw1 : ∀ k, (w k).1 = (z k.succ).1 + (r₀ k • p.1 + r₁ k • p.2) := fun k => hassoc _ _ _
    have hw2 : ∀ k, (w k).2 = (z k.succ).2 + (r₂ k • p.1 + r₃ k • p.2) := fun k => hassoc _ _ _
    have hwo1 : ∀ k (a' b' : R), bil Q (w k).1 (a' • p.1 + b' • p.2) = 0 := fun k => horth (ho₀ k) (ho₁ k)
    have hwo2 : ∀ k (a' b' : R), bil Q (w k).2 (a' • p.1 + b' • p.2) = 0 := fun k => horth (ho₂ k) (ho₃ k)
    have hwK1 : ∀ k, (w k).1 ∈ K₁ := fun k => by rw [hw1]; exact add_mem (hz.mem₁ _) (hcorrK _ _)
    have hwK2 : ∀ k, (w k).2 ∈ K₁ := fun k => by rw [hw2]; exact add_mem (hz.mem₂ _) (hcorrK _ _)
    -- `B(w_k^{(i)}, w_l^{(j)}) ≡ B(z_k^{(i)}, z_l^{(j)}) mod 𝔰₂`
    have hcross : ∀ {y y' : V} {a b a' b' : R}, y ∈ K₁ → y' ∈ K₁ → algebraMap R F a ∈ s₂ → algebraMap R F b ∈ s₂ →
        bil Q (y + (a • p.1 + b • p.2)) (a' • p.1 + b' • p.2) = 0 → bil Q y y' ∈ s₂ →
        bil Q (y + (a • p.1 + b • p.2)) (y' + (a' • p.1 + b' • p.2)) ∈ s₂ := by
      intro y y' a b a' b' hy hy' ha hb h0 hyy'
      rw [bil_add_right, h0, add_zero, bil_add_left]
      exact add_mem hyy' (hcorrB a b ha hb y' hy')
    have hwdata : BlockData Q K₁ s₂ g₁ g₂ w := by
      refine ⟨hwK1, hwK2, fun k => ?_, fun k => ?_, fun k => ?_, fun k l hkl => ?_, fun k l hkl => ?_,
        fun k l hkl => ?_⟩
      · rw [hw1, Q_add_of_orth Q (by rw [← hw1]; exact hwo1 k _ _)]
        exact sub_mem (hz.q₁ _) (hg₂₁ (hcorrQ _ _ (hr₀ k)))
      · rw [hw2, Q_add_of_orth Q (by rw [← hw2]; exact hwo2 k _ _)]
        exact sub_mem (hz.q₂ _) (hcorrQ _ _ (hr₂ k))
      · rw [hw1, hw2, bil_add_right, (by rw [← hw1]; exact hwo1 k _ _ :
          bil Q ((z k.succ).1 + (r₀ k • p.1 + r₁ k • p.2)) (r₂ k • p.1 + r₃ k • p.2) = 0), add_zero, bil_add_left]
        have : bil Q (z k.succ).1 (z k.succ).2 + bil Q (r₀ k • p.1 + r₁ k • p.2) (z k.succ).2 - 1 =
            (bil Q (z k.succ).1 (z k.succ).2 - 1) + bil Q (r₀ k • p.1 + r₁ k • p.2) (z k.succ).2 := by ring
        rw [this]
        exact add_mem (hz.b _) (hcorrB _ _ (hr₀ k) (hr₁ k) _ (hz.mem₂ _))
      · rw [hw1, hw1]
        exact hcross (hz.mem₁ _) (hz.mem₁ _) (hr₀ k) (hr₁ k) (by rw [← hw1]; exact hwo1 k _ _)
          (hz.c₁₁ _ _ (fun h => hkl (Fin.succ_injective _ h)))
      · rw [hw1, hw2]
        exact hcross (hz.mem₁ _) (hz.mem₂ _) (hr₀ k) (hr₁ k) (by rw [← hw1]; exact hwo1 k _ _)
          (hz.c₁₂ _ _ (fun h => hkl (Fin.succ_injective _ h)))
      · rw [hw2, hw2]
        exact hcross (hz.mem₂ _) (hz.mem₂ _) (hr₂ k) (hr₃ k) (by rw [← hw2]; exact hwo2 k _ _)
          (hz.c₂₂ _ _ (fun h => hkl (Fin.succ_injective _ h)))
    obtain ⟨e', he'⟩ := ih w hwdata
    -- the binary lattice `P = 𝔬p₁ + 𝔬p₂`
    set P := span R {p.1, p.2} with hPdef
    set U : Matrix (Fin 2) (Fin 2) R := !![A, Bv; Bv, C] with hU
    have hUdet : IsUnit U.det := by rw [hU, Matrix.det_fin_two_of, ← pow_two]; exact hunit
    have hGP : gram Q ![p.1, p.2] = (1 : F) • U.map (algebraMap R F) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [gram, hU, bil_comm Q p.2 p.1]
      all_goals first | exact hA.symm | exact hBv.symm | exact hC.symm
    obtain ⟨hPmod, hPrk⟩ := isModular_span_of_gram Q one_ne_zero hUdet hGP
    have hspanP : span R (Set.range ![p.1, p.2]) = P := by rw [range_pair]
    rw [hspanP] at hPmod hPrk
    have hPfg : P.FG := fg_span (Set.toFinite _)
    have hPreg := hPmod.isRegular Q hPfg
    have hli : LinearIndependent R ![p.1, p.2] := by
      refine linearIndependent_of_det_gram_ne_zero Q ?_
      rw [hGP, one_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hUdet.ne_zero
    let e2 : Basis (Fin 2) R P := (Basis.span hli).map (LinearEquiv.ofEq _ _ hspanP)
    have he2 : ∀ i, (e2 i : V) = ![p.1, p.2] i := fun i => by simp [e2, Basis.span_apply]
    -- `pairSpan z = P ⊥ pairSpan w`
    have hgen : ∀ s ∈ ({p.1, p.2} : Set V), ∀ t ∈ Set.range (fun k => (w k).1) ∪ Set.range (fun k => (w k).2),
        bil Q s t = 0 := by
      intro s hs t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases ht with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> rcases hs with rfl | rfl <;> rw [bil_comm]
      · exact ho₀ k
      · exact ho₁ k
      · exact ho₂ k
      · exact ho₃ k
    have horthP := orth_span_span (R := R) Q hgen
    have hz1 : ∀ k, (z k).1 ∈ pairSpan R z := fun k => subset_span (Or.inl ⟨k, rfl⟩)
    have hz2 : ∀ k, (z k).2 ∈ pairSpan R z := fun k => subset_span (Or.inr ⟨k, rfl⟩)
    have hPle : P ≤ pairSpan R z := by
      rw [hPdef, span_le]; intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · exact hz1 0
      · exact hz2 0
    have hcorr_mem : ∀ a b : R, a • p.1 + b • p.2 ∈ P := fun a b =>
      add_mem (smul_mem _ _ (subset_span (by simp))) (smul_mem _ _ (subset_span (by simp)))
    have hsum : IsOrthSum Q (pairSpan R z) P (pairSpan R w) := by
      refine ⟨horthP, disjoint_of_orth Q hPreg horthP, le_antisymm (sup_le hPle ?_) ?_⟩
      · rw [pairSpan, span_le]
        rintro t (⟨k, rfl⟩ | ⟨k, rfl⟩)
        · change (w k).1 ∈ pairSpan R z
          rw [hw1]; exact add_mem (hz1 _) (hPle (hcorr_mem _ _))
        · change (w k).2 ∈ pairSpan R z
          rw [hw2]; exact add_mem (hz2 _) (hPle (hcorr_mem _ _))
      · rw [pairSpan, span_le]
        have hw1' : ∀ k : Fin m, (w k).1 ∈ pairSpan R w := fun k => subset_span (Or.inl ⟨k, rfl⟩)
        have hw2' : ∀ k : Fin m, (w k).2 ∈ pairSpan R w := fun k => subset_span (Or.inr ⟨k, rfl⟩)
        rintro t (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> refine Fin.cases ?_ (fun k' => ?_) k
        · exact mem_sup_left (subset_span (by simp [hpdef]))
        · have : (z k'.succ).1 = (w k').1 - (r₀ k' • p.1 + r₁ k' • p.2) := by rw [hw1]; abel
          change (z k'.succ).1 ∈ P ⊔ pairSpan R w
          rw [this]; exact sub_mem (mem_sup_right (hw1' k')) (mem_sup_left (hcorr_mem _ _))
        · exact mem_sup_left (subset_span (by simp [hpdef]))
        · have : (z k'.succ).2 = (w k').2 - (r₂ k' • p.1 + r₃ k' • p.2) := by rw [hw2]; abel
          change (z k'.succ).2 ∈ P ⊔ pairSpan R w
          rw [this]; exact sub_mem (mem_sup_right (hw2' k')) (mem_sup_left (hcorr_mem _ _))
    obtain ⟨e, he⟩ := exists_basis_isOrthSum Q hsum e2 e'
    have hdet : (gram Q fun s => (e s : V)).det =
        (Q p.1 * Q p.2 - bil Q p.1 p.2 ^ 2) * (gram Q fun i => (e' i : V)).det := by
      rw [show (fun s => (e s : V)) = Sum.elim (fun i => (e2 i : V)) (fun k => (e' k : V)) from funext he,
        det_gram_sumElim Q hsum.orth _ _ (fun i => (e2 i).2) (fun k => (e' k).2)]
      congr 1
      rw [show (fun i => (e2 i : V)) = ![p.1, p.2] from funext he2, Matrix.det_fin_two]
      simp [gram, bil_self, bil_comm Q p.2 p.1]; ring
    set σ : Fin 2 ⊕ Fin (2 * m) ≃ Fin (2 * (m + 1)) := finSumFinEquiv.trans (finCongr (by ring))
    refine ⟨e.reindex σ, ?_⟩
    rw [show (gram Q fun i => (e.reindex σ i : V)).det = (gram Q fun s => (e s : V)).det by
      simp only [Basis.reindex_apply]
      exact Matrix.det_submatrix_equiv_self σ.symm (gram Q fun s => (e s : V)), hdet]
    have := sqEquivMod_mul_one hp he'
    convert this using 1; ring

/-- $\mathfrak s_2^2\,\mathfrak g(L^{\mathfrak a}) \subseteq \mathfrak g(L^{\mathfrak s_2})$ for $\mathfrak a \supseteq
\mathfrak o$-scaled vectors: if $z \in \mathfrak s_2 \subseteq \mathfrak o$ then $z^2\mathfrak g(L^{\mathfrak o})
\subseteq \mathfrak g(L^{\mathfrak s_2})$ (the vectors $zv$, $v \in L^{\mathfrak o}$, lie in $L^{\mathfrak s_2}$). -/
theorem sq_mul_mem_normGroup_subA {L : Submodule R V} {s₂ : Submodule R F} (hs₂ : s₂ ≤ 1)
    (hsc : s₂ ≤ scale Q (subA Q s₂ L)) {z : F} (hz : z ∈ s₂) {x : F} (hx : x ∈ normGroup Q (subA Q 1 L)) :
    z ^ 2 * x ∈ normGroup Q (subA Q s₂ L) := by
  obtain ⟨v, ⟨hvL, hvB⟩, c, hc, rfl⟩ := hx
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp (hs₂ hz)
  have hzs : ∀ y : F, y ∈ (1 : Submodule R F) → algebraMap R F r * y ∈ s₂ := by
    intro y hy
    obtain ⟨q, rfl⟩ := Submodule.mem_one.mp hy
    rw [mul_comm, ← Algebra.smul_def]; exact smul_mem _ _ hz
  refine ⟨r • v, ⟨smul_mem _ _ hvL, fun l hl => ?_⟩, algebraMap R F r ^ 2 * c, hsc ?_, ?_⟩
  · rw [bil_rsmul_left]; exact hzs _ (hvB l hl)
  · rw [pow_two, mul_assoc]; exact hzs _ (by
      have := scale_subA_le Q 1 L hc
      obtain ⟨q, rfl⟩ := Submodule.mem_one.mp this
      exact Submodule.mem_one.mpr ⟨r * q, by rw [map_mul]⟩)
  · rw [← algebraMap_smul F r v, QuadraticMap.map_smul]; ring

end Induction

section Base

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **93:28, necessity, step 1, condition (i), for a first component with $m$ blocks $A(c_k, 0)$** (O'Meara 1963,
pp. 268–269; O'Meara takes $m = 2$ after cancelling hyperbolic planes). Let $L = L_1 \perp \cdots \perp L_t =
K_1 \perp \cdots \perp K_t$ be two Jordan splittings of the same lattice, $L_1$ unimodular, spanned by pairs
$x_k^{(1)}, x_k^{(2)}$ with $Q(x_k^{(2)}) = 0$, $B(x_k^{(1)}, x_k^{(2)}) = 1$ and the pairs mutually orthogonal (a base
of matrix $A(c_1, 0) \perp \cdots \perp A(c_m, 0)$). Then $dL_1/dK_1 \cong 1 \bmod \mathfrak f_1$. -/
@[kb "omeara1963" "§93F, proof of 93:28, necessity, step 1, pp. 268–269 (condition (i), m blocks)"]
theorem nec_base_disc_blocks (h2 : (2 : R) ≠ 0) {L : Submodule R V} (hfg : L.FG) {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q L Ks)
    (i₀ i₁ : Fin t) (h₀ : i₀.val = 0) (h₁ : i₁.val = 1) {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a)
    (hU : scale Q (Ls i₀) = 1) {m : ℕ} (x : Fin m → V × V) (hspan : pairSpan R x = Ls i₀)
    (hx2 : ∀ k, Q (x k).2 = 0) (hx12 : ∀ k, bil Q (x k).1 (x k).2 = 1)
    (hx11 : ∀ k l, k ≠ l → bil Q (x k).1 (x l).1 = 0) (hx12' : ∀ k l, k ≠ l → bil Q (x k).1 (x l).2 = 0)
    (hx22 : ∀ k l, k ≠ l → bil Q (x k).2 (x l).2 = 0) :
    DiscQuotSqEquivMod Q (jordanChain Ls i₀) (jordanChain Ks i₀) (fIdeal Q L Ls i₀ i₁) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [jordanChain_zero Ls i₀ h₀, jordanChain_zero Ks i₀ h₀]
  have hreg := isRegular_of_isJordanSplitting Q hfg hL
  obtain ⟨hT, hJT⟩ := hL.sameJordanType Q hfg hK
  have hc : ∀ i, Fin.cast hT i = i := fun i => Fin.ext (by simp)
  have hsc : ∀ i, scale Q (Ls i) = scale Q (Ks i) := fun i => by have := (hJT i).1; rwa [hc] at this
  have hrkLK : ∀ i, finrank R (Ls i) = finrank R (Ks i) := fun i => by have := (hJT i).2.1; rwa [hc] at this
  have hK0 : scale Q (Ks i₀) = 1 := (hsc i₀) ▸ hU
  have hKi₁ : Ks i₁ ≤ L := hK.split.iSup_eq ▸ le_iSup Ks i₁
  set s₂ := scale Q (Ks i₁) with hs₂def
  have hs₂lt : s₂ < 1 := hK0 ▸ hK.scale_strictAnti (Fin.lt_def.2 (by omega))
  have hs₂R : ∀ z ∈ s₂, ∃ r ∈ maximalIdeal R, algebraMap R F r = z := fun z hz =>
    exists_max_of_lt_one (scale_fg Q (FG.of_le hfg hKi₁)) (hK.modular i₁).1 hs₂lt hz
  set g₁ := fundNormGroup Q L Ls i₀ with hg₁def
  set g₂ := fundNormGroup Q L Ls i₁ with hg₂def
  have hg₁ : g₁ = normGroup Q (subA Q 1 L) := by rw [hg₁def, ← hU]; rfl
  have hg₂ : g₂ = normGroup Q (subA Q s₂ L) := by rw [hg₂def, hs₂def, ← hsc i₁]; rfl
  have hg₂₁ : g₂ ≤ g₁ := fundNormGroup_antitone Q hL (Fin.le_def.2 (by omega))
  have hs₂sc : s₂ ≤ scale Q (subA Q s₂ L) := by
    have := scale_mono Q (le_fundSub Q hfg hK i₁)
    rwa [fundSub, ← hs₂def] at this
  -- the ideal `𝔣₁` and the key congruence
  have hn : ∀ i, fundNormIdeal Q L Ls i = R ∙ a i := fun i => (ha i).2.symm
  have hf : fIdeal Q L Ls i₀ i₁ = fIdealOf R (R ∙ (1 : F)) g₁ g₂ (R ∙ a i₀) (R ∙ a i₁) := by
    rw [fIdeal, hU, hn, hn, Submodule.one_eq_span]
  have ha0 : ∀ i, a i ≠ 0 := fun i =>
    (ha i).ne_zero Q (isRegular_fundSub Q hfg hreg hL i) (fundSub_ne_bot Q hfg hL i)
  have hgA : ∀ i, ∀ z ∈ fundNormGroup Q L Ls i, z ∈ R ∙ a i := fun i z hz =>
    (ha i).2 ▸ normGroup_subset_normIdeal Q _ hz
  have haS : ∀ i, a i ∈ scale Q (Ls i) := fun i => by
    rw [← scale_fundSub Q hfg hL i]
    exact normIdeal_le_scale Q _ ((ha i).2 ▸ mem_span_singleton_self (a i))
  have hu₀ : 0 ≤ dord hπ (a i₀) := by
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hU ▸ haS i₀)
    rw [← hr]; exact dord_alg_nonneg hπ (by rintro rfl; exact ha0 i₀ (by rw [← hr, map_zero]))
  have hu₁ : 1 ≤ dord hπ (a i₁) := by
    obtain ⟨r, hrm, hr⟩ := hs₂R _ (hsc i₁ ▸ haS i₁)
    rw [← hr]; exact one_le_dord_of_max hπ hrm (hr ▸ ha0 i₁)
  have key : ∀ c : R, c ∈ maximalIdeal R → ∀ α ∈ g₁, ∀ β ∈ g₂,
      SqEquivMod (fIdeal Q L Ls i₀ i₁) ((1 - algebraMap R F c) ^ 2 + α * β) 1 := by
    intro c hcm α hα β hβ
    rw [hf]
    exact sqEquivMod_sq_add_mul hπ h2 (ha0 i₀) (ha0 i₁) (ha i₀).1 (ha i₁).1 (hgA i₀) (hgA i₁) hu₀ hu₁
      (fun z hz r => mul_sq_mem_normGroup Q hz ⟨r, rfl⟩) hcm hα hβ
  -- the standing hypotheses of `block_disc`
  have hsq₂ : ∀ z ∈ g₂, ∀ r : R, algebraMap R F r ^ 2 * z ∈ g₂ := fun z hz r =>
    mul_sq_mem_normGroup Q hz ⟨r, rfl⟩
  have h2s : ∀ z ∈ s₂, 2 * z ∈ g₂ := fun z hz => hg₂ ▸ two_mul_mem_normGroup Q (hs₂sc hz)
  have hsg : ∀ z ∈ s₂, ∀ y ∈ g₁, z ^ 2 * y ∈ g₂ := fun z hz y hy => hg₂ ▸
    sq_mul_mem_normGroup_subA Q hs₂lt.le hs₂sc hz (hg₁ ▸ hy)
  have hKR : ∀ {K : Submodule R V}, scale Q K = 1 → ∀ u ∈ K, ∀ v ∈ K, ∃ r : R, algebraMap R F r = bil Q u v :=
    fun hK1 u hu v hv => Submodule.mem_one.mp (hK1 ▸ bil_mem_scale Q hu hv)
  -- `x` spans `L₁`; project onto `K₁`
  have hLi : Ls i₀ ≤ L := hL.split.iSup_eq ▸ le_iSup Ls i₀
  have hxL1 : ∀ k, (x k).1 ∈ Ls i₀ := fun k => hspan ▸ subset_span (Or.inl ⟨k, rfl⟩)
  have hxL2 : ∀ k, (x k).2 ∈ Ls i₀ := fun k => hspan ▸ subset_span (Or.inr ⟨k, rfl⟩)
  have hdec : ∀ v ∈ L, ∃ y ∈ Ks i₀, ∃ Y ∈ others Ks i₀, y + Y = v := fun v hv =>
    mem_sup.mp ((sup_others Q hK.split i₀).symm ▸ hv)
  choose y₁ hy₁ Y₁ hY₁ hxy₁ using fun k => hdec _ (hLi (hxL1 k))
  choose y₂ hy₂ Y₂ hY₂ hxy₂ using fun k => hdec _ (hLi (hxL2 k))
  have hsub : ∀ {Y : V}, Y ∈ others Ks i₀ → Y ∈ subA Q s₂ L := fun hY => mem_subA_of_others Q hK i₀ i₁ h₀ h₁ hY
  have horth : ∀ {y Y : V}, y ∈ Ks i₀ → Y ∈ others Ks i₀ → bil Q y Y = 0 := fun hy hY =>
    orth_others Q hK.split i₀ hy _ hY
  have hBdec : ∀ {y Y y' Y' : V}, y ∈ Ks i₀ → Y ∈ others Ks i₀ → y' ∈ Ks i₀ → Y' ∈ others Ks i₀ →
      bil Q (y + Y) (y' + Y') = bil Q y y' + bil Q Y Y' := by
    intro y Y y' Y' hy hY hy' hY'
    rw [bil_add_left, bil_add_right, bil_add_right, horth hy hY', bil_comm Q Y y', horth hy' hY]; ring
  have hQdec : ∀ {y Y : V}, y ∈ Ks i₀ → Y ∈ others Ks i₀ → Q (y + Y) = Q y + Q Y := by
    intro y Y hy hY; rw [Q_add, horth hy hY]; ring
  have hYY : ∀ {Y Y' : V}, Y ∈ others Ks i₀ → Y' ∈ others Ks i₀ → bil Q Y Y' ∈ s₂ := fun hY hY' =>
    (hsub hY).2 _ (hsub hY').1
  have hQY : ∀ {Y : V}, Y ∈ others Ks i₀ → Q Y ∈ g₂ := fun hY => hg₂ ▸ Q_mem_normGroup Q (hsub hY)
  have hfs₀ : Ls i₀ ≤ fundSub Q L Ls i₀ := le_fundSub Q hfg hL i₀
  set yy : Fin m → V × V := fun k => (y₁ k, y₂ k) with hyy
  have hyydata : BlockData Q (Ks i₀) s₂ g₁ g₂ yy := by
    refine ⟨hy₁, hy₂, fun k => ?_, fun k => ?_, fun k => ?_, fun k l hkl => ?_, fun k l hkl => ?_,
      fun k l hkl => ?_⟩
    · have h := hQdec (hy₁ k) (hY₁ k); rw [hxy₁ k] at h
      have : Q (y₁ k) = Q (x k).1 - Q (Y₁ k) := by linear_combination -h
      show Q (y₁ k) ∈ g₁; rw [this]
      exact sub_mem (Q_mem_normGroup Q (hfs₀ (hxL1 k))) (hg₂₁ (hQY (hY₁ k)))
    · have h := hQdec (hy₂ k) (hY₂ k); rw [hxy₂ k, hx2 k] at h
      have : Q (y₂ k) = -Q (Y₂ k) := by linear_combination -h
      show Q (y₂ k) ∈ g₂; rw [this]; exact neg_mem (hQY (hY₂ k))
    · have h := hBdec (hy₁ k) (hY₁ k) (hy₂ k) (hY₂ k); rw [hxy₁ k, hxy₂ k, hx12 k] at h
      show bil Q (y₁ k) (y₂ k) - 1 ∈ s₂
      have : bil Q (y₁ k) (y₂ k) - 1 = -bil Q (Y₁ k) (Y₂ k) := by linear_combination -h
      rw [this]; exact neg_mem (hYY (hY₁ k) (hY₂ k))
    · have h := hBdec (hy₁ k) (hY₁ k) (hy₁ l) (hY₁ l); rw [hxy₁ k, hxy₁ l, hx11 k l hkl] at h
      show bil Q (y₁ k) (y₁ l) ∈ s₂
      have : bil Q (y₁ k) (y₁ l) = -bil Q (Y₁ k) (Y₁ l) := by linear_combination -h
      rw [this]; exact neg_mem (hYY (hY₁ k) (hY₁ l))
    · have h := hBdec (hy₁ k) (hY₁ k) (hy₂ l) (hY₂ l); rw [hxy₁ k, hxy₂ l, hx12' k l hkl] at h
      show bil Q (y₁ k) (y₂ l) ∈ s₂
      have : bil Q (y₁ k) (y₂ l) = -bil Q (Y₁ k) (Y₂ l) := by linear_combination -h
      rw [this]; exact neg_mem (hYY (hY₁ k) (hY₂ l))
    · have h := hBdec (hy₂ k) (hY₂ k) (hy₂ l) (hY₂ l); rw [hxy₂ k, hxy₂ l, hx22 k l hkl] at h
      show bil Q (y₂ k) (y₂ l) ∈ s₂
      have : bil Q (y₂ k) (y₂ l) = -bil Q (Y₂ k) (Y₂ l) := by linear_combination -h
      rw [this]; exact neg_mem (hYY (hY₂ k) (hY₂ l))
  have hxdata : BlockData Q (Ls i₀) s₂ g₁ g₂ x := by
    refine ⟨hxL1, hxL2, fun k => Q_mem_normGroup Q (hfs₀ (hxL1 k)), fun k => ?_, fun k => ?_,
      fun k l h => ?_, fun k l h => ?_, fun k l h => ?_⟩
    · rw [hx2]; exact zero_mem _
    · rw [hx12, sub_self]; exact zero_mem _
    · rw [hx11 k l h]; exact zero_mem _
    · rw [hx12' k l h]; exact zero_mem _
    · rw [hx22 k l h]; exact zero_mem _
  obtain ⟨ex, hex⟩ := block_disc Q (hKR hU) hs₂R hg₂₁ hsq₂ h2s hsg key m x hxdata
  obtain ⟨ey, hey⟩ := block_disc Q (hKR hK0) hs₂R hg₂₁ hsq₂ h2s hsg key m yy hyydata
  -- `pairSpan yy = K₁`
  have hyyle : pairSpan R yy ≤ Ks i₀ := by
    rw [pairSpan, span_le]
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact hy₁ k
    · exact hy₂ k
  have heyK : ∀ i, (ey i : V) ∈ Ks i₀ := fun i => hyyle (ey i).2
  choose Uf hUf using fun i j => hKR hK0 _ (heyK i) _ (heyK j)
  set U : Matrix (Fin (2 * m)) (Fin (2 * m)) R := Matrix.of Uf with hUdef
  have hUmap : gram Q (fun i => (ey i : V)) = (1 : F) • U.map (algebraMap R F) := by
    ext i j; simp [gram, hUdef, hUf]
  have hey₀ := hey
  obtain ⟨⟨u, hu, hu'⟩, -⟩ := hey₀
  rw [mul_one] at hu'
  have hUdet : IsUnit U.det := by
    have : U.det = (-1) ^ m * u := IsFractionRing.injective R F (by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← one_smul F (U.map (algebraMap R F)), ← hUmap, map_mul,
        map_pow, map_neg, map_one, ← hu']
      ring_nf
      rw [mul_comm m 2, pow_mul, neg_one_sq, one_pow, mul_one])
    rw [this]; exact (isUnit_neg_one.pow m).mul hu
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      subst h
      have h0 : Ls i₀ = ⊥ := by
        rw [← hspan, pairSpan, Set.range_eq_empty, Set.range_eq_empty, Set.union_empty, span_empty]
      have := (hL.modular i₀).1
      rw [(hL.modular i₀).2.1.symm, h0, scale_bot] at this
      exact this rfl
    · exact h
  have : Nonempty (Fin (2 * m)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨hmod, hrk⟩ := isModular_span_of_gram Q one_ne_zero hUdet hUmap
  rw [span_basis_eq] at hmod hrk
  have hrkL : finrank R (Ls i₀) = 2 * m := by
    rw [← hspan, finrank_eq_card_basis ex, Fintype.card_fin]
  have hKmod : IsModular Q (R ∙ (1 : F)) (Ks i₀) := by
    have := hK.modular i₀; rwa [hK0, Submodule.one_eq_span] at this
  have hKfg : (Ks i₀).FG := FG.of_le hfg (hK.split.iSup_eq ▸ le_iSup Ks i₀)
  have heq : pairSpan R yy = Ks i₀ := eq_of_isModular_of_le Q hyyle hmod hKmod (FG.of_le hKfg hyyle) hKfg
    (by rw [hrk, Fintype.card_fin, ← hrkLK i₀, hrkL])
  refine discQuot_of_bases Q (ex.map (LinearEquiv.ofEq _ _ hspan)) (ey.map (LinearEquiv.ofEq _ _ heq)) ?_
  have hxg : (gram Q fun i => ((ex.map (LinearEquiv.ofEq _ _ hspan)) i : V)) = gram Q fun i => (ex i : V) := by
    ext i j; simp [gram]
  have hyg : (gram Q fun i => ((ey.map (LinearEquiv.ofEq _ _ heq)) i : V)) = gram Q fun i => (ey i : V) := by
    ext i j; simp [gram]
  rw [hxg, hyg]
  have hey0 : (gram Q fun i => (ey i : V)).det ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hu'
    exact hu.ne_zero (IsFractionRing.injective R F (by rw [← hu', map_zero]))
  have hm0 : ((-1 : F)) ^ m ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have := sqEquivMod_mul_one hex (sqEquivMod_inv_one hey)
  convert this using 1
  field_simp

end Base

end QuadFormsKB.OMeara.NecBlock
