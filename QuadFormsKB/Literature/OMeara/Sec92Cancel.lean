/-
# O'Meara §92: the cancellation law over non-dyadic fields (Theorem 92:3)

**Setting** (as in `Sec92.lean`): $R$ a discrete valuation ring with fraction field $F$, $2$ a unit of $R$
(non-dyadic), quadratic spaces $(V, Q)$, $(V', Q')$ over $F$, lattices = `Submodule R V`.

**Proves**
* `exists_orthLat_apply_eq` (the step of 92:3 and 92:4): if $M = \mathfrak ox \perp A = \mathfrak oy \perp B$ with
  $Q(x) = Q(y) \ne 0$, a product $\sigma$ of one or two symmetries in $O(M)$ has $\sigma x = y$, hence $\sigma A = B$;
* `isometricLat_cancel_of_isOrthSum`: if $M = A \perp B = A' \perp B'$ with $A \cong A'$, then $B \cong B'$;
* `isometricLat_cancel` (**Theorem 92:3**, p. 248): if $L \cong K$, $L = L' \perp L''$, $K = K' \perp K''$ and
  $L' \cong K'$, then $L'' \cong K''$. (O'Meara leaves the proof as an exercise "from 92:2"; the proof here splits off
  one vector of an orthogonal base of $L'$ at a time. Only the discrete valuation ring and $2 \in \mathfrak u$ are used.)
-/
import QuadFormsKB.Literature.OMeara.Sec92Sym
import QuadFormsKB.Literature.OMeara.Sec92Jordan

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section NonDyadic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- `2 * z ∈ S` for `z ∈ S` (helper for 92:3). -/
theorem cancel_two_mul_mem {S : Submodule R F} {z : F} (hz : z ∈ S) : 2 * z ∈ S := by
  have := S.smul_mem (2 : R) hz
  rwa [Algebra.smul_def, map_ofNat] at this

/-- A vector `u` of `M` with `2 B(M, u) ⊆ Q(u) o` gives a symmetry in `O(M)` (helper for 92:3). -/
theorem cancel_symm_mem {M : Submodule R V} {u : V} (hu : Q u ≠ 0) (huM : u ∈ M)
    (h : ∀ m ∈ M, 2 * bil Q m u ∈ R ∙ Q u) : symmetry Q u hu ∈ orthLat Q M := by
  refine symmetry_mem_orthLat_of_le Q hu fun m hm => ?_
  obtain ⟨r, hr⟩ := mem_span_singleton.mp (h m hm)
  rw [symmetry_apply]
  have : (2 * bil Q m u / Q u) • u = r • u := by
    rw [← algebraMap_smul F r u]
    congr 1
    rw [← hr, Algebra.smul_def]; field_simp
  rw [this]
  exact M.sub_mem hm (M.smul_mem r huM)

/-- If `M = R z ⊥ C` then `B(z, M) ⊆ Q(z) o` (helper for 92:3). -/
theorem cancel_bil_mem {M C : Submodule R V} {z : V} (hC : IsOrthSum Q M (R ∙ z) C) {m : V}
    (hm : m ∈ M) : bil Q z m ∈ R ∙ Q z := by
  rw [← hC.sup_eq] at hm
  obtain ⟨p, hp, k, hk, rfl⟩ := mem_sup.mp hm
  obtain ⟨r, rfl⟩ := mem_span_singleton.mp hp
  rw [bil_add_right, hC.orth _ (mem_span_singleton_self z) k hk, add_zero, bil_rsmul_right, bil_self]
  exact mem_span_singleton.mpr ⟨r, by rw [Algebra.smul_def]⟩

/-- An element of `O(M)` carrying `x` to `y` carries the complement of `x` into that of `y`
(helper for 92:3). -/
theorem cancel_map_comp {M A B : Submodule R V} {x y : V} (hA : IsOrthSum Q M (R ∙ x) A)
    (hB : IsOrthSum Q M (R ∙ y) B) (hx : Q x ≠ 0) (hy : Q y ≠ 0) {g : V ≃ₗ[F] V}
    (hg : g ∈ orthLat Q M) (hgx : g x = y) {a : V} (ha : a ∈ A) : g a ∈ B := by
  rw [sym4_mem_comp_iff Q hy hB]
  rw [sym4_mem_comp_iff Q hx hA] at ha
  refine ⟨?_, ?_⟩
  · have : g a ∈ latMap g M := Submodule.mem_map_of_mem ha.1
    rwa [hg.2] at this
  · have := sym4_bil_orth Q hg.1 a x
    rw [hgx] at this
    rw [this]; exact ha.2

/-- **Moving one split vector onto another** (the step of 92:3 and 92:4, O'Meara 1963, p. 248): if
$M = \mathfrak ox \perp A$ and $M = \mathfrak oy \perp B$ with $Q(x) = Q(y) \ne 0$ over a non-dyadic field, there is
$\sigma \in O(V)$ with $\sigma M = M$, $\sigma x = y$ and $\sigma A = B$. -/
theorem exists_orthLat_apply_eq (h2 : IsUnit (2 : R)) {M A B : Submodule R V} {x y : V}
    (hA : IsOrthSum Q M (R ∙ x) A) (hB : IsOrthSum Q M (R ∙ y) B) (hQ : Q x = Q y) (hQ0 : Q x ≠ 0) :
    ∃ σ ∈ orthLat Q M, σ x = y ∧ latMap σ A = B := by
  have hxM : x ∈ M := hA.sup_eq ▸ mem_sup_left (mem_span_singleton_self x)
  have hyM : y ∈ M := hB.sup_eq ▸ mem_sup_left (mem_span_singleton_self y)
  have hQy : Q y ≠ 0 := hQ ▸ hQ0
  have hxm : ∀ m ∈ M, bil Q x m ∈ R ∙ Q x := fun m hm => cancel_bil_mem Q hA hm
  have hym : ∀ m ∈ M, bil Q y m ∈ R ∙ Q x := fun m hm => hQ ▸ cancel_bil_mem Q hB hm
  have hxy := hxm y hyM
  have hc : Q x ∈ R ∙ Q x := mem_span_singleton_self _
  have hspanY : R ∙ Q y = R ∙ Q x := by rw [hQ]
  have h4 : IsUnit (4 : R) := by
    have : (4 : R) = 2 * 2 := by norm_num
    rw [this]; exact h2.mul h2
  obtain ⟨u4, hu4⟩ := h4
  have hfin : ∀ σ ∈ orthLat Q M, σ x = y → latMap σ A = B := by
    intro σ hσ hσx
    have hσ' : σ⁻¹ ∈ orthLat Q M := (orthLat Q M).inv_mem hσ
    have hσ'y : σ⁻¹ y = x := (LinearEquiv.symm_apply_eq σ).mpr hσx.symm
    ext b
    simp only [latMap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact cancel_map_comp Q hA hB hQ0 hQy hσ hσx ha
    · intro hb
      exact ⟨σ⁻¹ b, cancel_map_comp Q hB hA hQy hQ0 hσ' hσ'y hb, LinearEquiv.apply_symm_apply σ b⟩
  have hqa : Q (x - y) = 2 * Q x - 2 * bil Q x y := by
    have := Q_add Q x (-y)
    rw [← sub_eq_add_neg, sym4_bil_neg_right, QuadraticMap.map_neg] at this
    rw [this, ← hQ]; ring
  have hqb : Q (x + y) = 2 * Q x + 2 * bil Q x y := by
    rw [Q_add, ← hQ]; ring
  have hqa_mem : Q (x - y) ∈ R ∙ Q x := by
    rw [hqa]; exact sub_mem (cancel_two_mul_mem hc) (cancel_two_mul_mem hxy)
  have hqb_mem : Q (x + y) ∈ R ∙ Q x := by
    rw [hqb]; exact add_mem (cancel_two_mul_mem hc) (cancel_two_mul_mem hxy)
  have hQc : Q x ∈ (R ∙ Q (x - y)) ⊔ (R ∙ Q (x + y)) := by
    have hsum : Q (x - y) + Q (x + y) = 4 * Q x := by rw [hqa, hqb]; ring
    have hmem : 4 * Q x ∈ (R ∙ Q (x - y)) ⊔ (R ∙ Q (x + y)) :=
      hsum ▸ add_mem_sup (mem_span_singleton_self _) (mem_span_singleton_self _)
    have : Q x = (↑u4⁻¹ : R) • (4 * Q x) := by
      rw [Algebra.smul_def, ← mul_assoc, ← map_ofNat (algebraMap R F) 4, ← hu4, ← map_mul,
        Units.inv_mul, map_one, one_mul]
    rw [this]; exact Submodule.smul_mem _ _ hmem
  -- membership of the symmetry of a vector `u` with `R ∙ Q u = R ∙ Q x`
  have hsym : ∀ u ∈ M, ∀ hu : Q u ≠ 0, R ∙ Q u = R ∙ Q x → (∀ m ∈ M, bil Q m u ∈ R ∙ Q x) →
      symmetry Q u hu ∈ orthLat Q M := by
    intro u huM hu hs hb
    refine cancel_symm_mem Q hu huM fun m hm => ?_
    rw [hs]; exact cancel_two_mul_mem (hb m hm)
  have hsymy : symmetry Q y hQy ∈ orthLat Q M :=
    hsym y hyM hQy hspanY fun m hm => by rw [bil_comm]; exact hym m hm
  rcases span_pair_eq (R := R) (Q (x - y)) (Q (x + y)) with h | h
  · rw [h] at hQc
    have hs : R ∙ Q (x - y) = R ∙ Q x := le_antisymm
      ((span_singleton_le_iff_mem _ _).mpr hqa_mem) ((span_singleton_le_iff_mem _ _).mpr hQc)
    have hQa : Q (x - y) ≠ 0 := by
      intro h0
      rw [h0] at hQc
      obtain ⟨r, hr⟩ := mem_span_singleton.mp hQc
      rw [smul_zero] at hr; exact hQ0 hr.symm
    have hmem : x - y ∈ M := M.sub_mem hxM hyM
    have hτ := hsym (x - y) hmem hQa hs fun m hm => by
      rw [bil_sub_right, bil_comm Q m x, bil_comm Q m y]
      exact sub_mem (hxm m hm) (hym m hm)
    have hσx : symmetry Q (x - y) hQa x = y := by
      rw [sym4_symmetry_apply_of_two_bil Q hQa ?_]
      · abel
      · rw [bil_sub_right, bil_self, hqa]; ring
    exact ⟨_, hτ, hσx, hfin _ hτ hσx⟩
  · rw [h] at hQc
    have hs : R ∙ Q (x + y) = R ∙ Q x := le_antisymm
      ((span_singleton_le_iff_mem _ _).mpr hqb_mem) ((span_singleton_le_iff_mem _ _).mpr hQc)
    have hQb : Q (x + y) ≠ 0 := by
      intro h0
      rw [h0] at hQc
      obtain ⟨r, hr⟩ := mem_span_singleton.mp hQc
      rw [smul_zero] at hr; exact hQ0 hr.symm
    have hmem : x + y ∈ M := M.add_mem hxM hyM
    have hτ := hsym (x + y) hmem hQb hs fun m hm => by
      rw [bil_add_right, bil_comm Q m x, bil_comm Q m y]
      exact add_mem (hxm m hm) (hym m hm)
    have hσx : (symmetry Q y hQy * symmetry Q (x + y) hQb) x = y := by
      rw [LinearEquiv.mul_apply, sym4_symmetry_apply_of_two_bil Q hQb ?_]
      · have : x - (x + y) = -y := by abel
        rw [this, map_neg, sym4_symmetry_self Q hQy, neg_neg]
      · rw [bil_add_right, bil_self, hqb]; ring
    exact ⟨_, (orthLat Q M).mul_mem hsymy hτ, hσx, hfin _ ((orthLat Q M).mul_mem hsymy hτ) hσx⟩

/-- Symmetry of `IsOrthSum` (helper for 92:3). -/
theorem cancel_orthSum_comm {L J K : Submodule R V} (h : IsOrthSum Q L J K) : IsOrthSum Q L K J :=
  ⟨fun x hx y hy => by rw [bil_comm]; exact h.orth y hy x hx, h.disjoint.symm, by
    rw [sup_comm]; exact h.sup_eq⟩

/-- Associativity of orthogonal sums: `M = A ⊥ B` and `A = J ⊥ K` give `M = J ⊥ (K ⊔ B)` and
`K ⊔ B = K ⊥ B` (helper for 92:3). -/
theorem cancel_split3 {M A B J K : Submodule R V} (h : IsOrthSum Q M A B) (hA : IsOrthSum Q A J K) :
    IsOrthSum Q M J (K ⊔ B) ∧ IsOrthSum Q (K ⊔ B) K B := by
  have hKA : K ≤ A := hA.sup_eq ▸ le_sup_right
  have hJA : J ≤ A := hA.sup_eq ▸ le_sup_left
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, rfl⟩⟩
  · intro x hx y hy
    obtain ⟨k, hk, b, hb, rfl⟩ := mem_sup.mp hy
    rw [bil_add_right, hA.orth x hx k hk, h.orth x (hJA hx) b hb, add_zero]
  · rw [Submodule.disjoint_def]
    intro z hzJ hz
    obtain ⟨k, hk, b, hb, rfl⟩ := mem_sup.mp hz
    have hbA : b ∈ A := by
      have := A.sub_mem (hJA hzJ) (hKA hk)
      simpa using this
    have hb0 : b = 0 := (Submodule.disjoint_def.mp h.disjoint) b hbA hb
    subst hb0
    simp only [add_zero] at hzJ ⊢
    exact (Submodule.disjoint_def.mp hA.disjoint) k hzJ hk
  · rw [← sup_assoc, hA.sup_eq, h.sup_eq]
  · intro x hx y hy
    exact h.orth x (hKA hx) y hy
  · exact h.disjoint.mono_left hKA

/-- An isometry of `V` carries an orthogonal sum to an orthogonal sum (helper for 92:3). -/
theorem cancel_orthSum_map {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) {L J K : Submodule R V}
    (h : IsOrthSum Q L J K) : IsOrthSum Q (latMap σ L) (latMap σ J) (latMap σ K) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [bil_orth Q hσ]; exact h.orth x hx y hy
  · rw [Submodule.disjoint_def]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hxy ⊢
    have hyx : y = x := σ.injective hxy
    subst hyx
    rw [Submodule.disjoint_def.mp h.disjoint y hx hy, map_zero]
  · rw [← Submodule.map_sup, h.sup_eq]

/-- Restricting an isometry of lattices to sublattices that correspond (helper for 92:3). -/
theorem cancel_iso_restrict {A A₁ : Submodule R V} {A' A₁' : Submodule R V'} (f : A ≃ₗ[R] A')
    (hf : ∀ x : A, Q' (f x : V') = Q (x : V)) (h1 : A₁ ≤ A) (h1' : A₁' ≤ A')
    (h : ∀ a : A, (a : V) ∈ A₁ ↔ (f a : V') ∈ A₁') : IsometricLat Q Q' A₁ A₁' := by
  refine ⟨
    { toFun := fun a => ⟨(f ⟨a, h1 a.2⟩ : V'), (h ⟨a, h1 a.2⟩).mp a.2⟩
      map_add' := fun a b => by
        apply Subtype.ext
        show ((f ((⟨a, h1 a.2⟩ : A) + ⟨b, h1 b.2⟩) : A') : V') = _
        rw [map_add]; rfl
      map_smul' := fun r a => by
        apply Subtype.ext
        show ((f (r • (⟨a, h1 a.2⟩ : A)) : A') : V') = _
        rw [map_smul]; rfl
      invFun := fun b => ⟨(f.symm ⟨b, h1' b.2⟩ : V),
        (h (f.symm ⟨b, h1' b.2⟩)).mpr (by simp)⟩
      left_inv := fun a => by apply Subtype.ext; simp
      right_inv := fun b => by apply Subtype.ext; simp }, fun x => hf _⟩

/-- Transport of a sublattice along an isometry `f : L ≃ K` (helper for 92:3). -/
theorem cancel_image {L : Submodule R V} {K : Submodule R V'} (f : L ≃ₗ[R] K) (S : Submodule R V) :
    ∃ S' : Submodule R V', S' ≤ K ∧ ∀ z : V', z ∈ S' ↔ ∃ a : L, (a : V) ∈ S ∧ (f a : V') = z := by
  refine ⟨(S.comap L.subtype).map (K.subtype ∘ₗ f.toLinearMap), ?_, fun z => ?_⟩
  · rintro _ ⟨a, -, rfl⟩
    exact (f a).2
  · simp only [Submodule.mem_map, Submodule.mem_comap, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, LinearEquiv.coe_coe]

/-- Symmetry of `IsometricLat` (helper for 92:3). -/
theorem cancel_iso_symm {L : Submodule R V} {K : Submodule R V'} (h : IsometricLat Q Q' L K) :
    IsometricLat Q' Q K L := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f.symm, fun y => by
    have := hf (f.symm y)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm⟩

/-- Transitivity of `IsometricLat` across three spaces (helper for 92:3). -/
theorem cancel_iso_trans {V'' : Type*} [AddCommGroup V''] [Module F V''] [Module R V'']
    [IsScalarTower R F V''] {Q'' : QuadraticForm F V''} {L : Submodule R V} {K : Submodule R V'}
    {N : Submodule R V''} (h1 : IsometricLat Q Q' L K) (h2 : IsometricLat Q' Q'' K N) :
    IsometricLat Q Q'' L N := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  exact ⟨f.trans g, fun x => by rw [LinearEquiv.trans_apply, hg, hf]⟩

/-- The induction of 92:3 on the rank of `A` (helper). -/
theorem cancel_aux (h2 : IsUnit (2 : R)) (n : ℕ) :
    ∀ {M A B A' B' : Submodule R V}, M.FG → IsRegular Q M → IsOrthSum Q M A B → IsOrthSum Q M A' B' →
      IsometricLat Q Q A A' → finrank R A = n → IsometricLat Q Q B B' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M A B A' B' hM hreg h h' hAA' hn
  by_cases hA0 : A = ⊥
  · have hA'0 : A' = ⊥ := by
      obtain ⟨g, -⟩ := hAA'
      rw [eq_bot_iff]
      intro z hz
      have : g.symm ⟨z, hz⟩ = 0 := by
        have h0 := (g.symm ⟨z, hz⟩).2
        simp only [hA0, Submodule.mem_bot] at h0
        exact Subtype.ext h0
      have hz0 : (⟨z, hz⟩ : A') = 0 := by
        rw [← g.apply_symm_apply ⟨z, hz⟩, this, map_zero]
      have := congrArg Subtype.val hz0
      simpa using this
    have hB : B = M := by rw [← h.sup_eq, hA0, bot_sup_eq]
    have hB' : B' = M := by rw [← h'.sup_eq, hA'0, bot_sup_eq]
    rw [hB, hB']
    exact ⟨LinearEquiv.refl R _, fun _ => rfl⟩
  have hAfg : A.FG := FG.of_le hM (h.sup_eq ▸ le_sup_left)
  have hAreg : IsRegular Q A := IsOrthSum.isRegular_right Q (cancel_orthSum_comm Q h) hreg
  obtain ⟨e, A₁, heA, hQe, hs, hA, hrk⟩ := sym4_exists_split Q h2 hAfg hAreg hA0
  obtain ⟨g, hg⟩ := hAA'
  obtain ⟨e', he'⟩ : ∃ e' : V, e' = (g ⟨e, heA⟩ : V) := ⟨_, rfl⟩
  have he'A' : e' ∈ A' := he' ▸ (g ⟨e, heA⟩).2
  have hQe' : Q e' = Q e := he' ▸ hg ⟨e, heA⟩
  have hQe'0 : Q e' ≠ 0 := hQe' ▸ hQe
  have hscale' : scale Q A' = R ∙ Q e' := by
    rw [IsometricLat.scale_eq Q Q ⟨g, hg⟩ hAfg, hs, hQe']
  obtain ⟨hmod, -⟩ := sym4_isModular_span_singleton (R := R) Q hQe'0
  obtain ⟨A₁', hA'⟩ := splits_of_isModular_of_scale_eq Q
    ((span_singleton_le_iff_mem _ _).mpr he'A') hmod (fg_span_singleton e') hscale'
  have hiso1 : IsometricLat Q Q A₁ A₁' := by
    have hA₁A : A₁ ≤ A := hA.sup_eq ▸ le_sup_right
    have hA₁A' : A₁' ≤ A' := hA'.sup_eq ▸ le_sup_right
    refine cancel_iso_restrict Q Q g hg hA₁A hA₁A' fun a => ?_
    rw [sym4_mem_comp_iff Q hQe hA, sym4_mem_comp_iff Q hQe'0 hA']
    have hb : bil Q (g a : V) e' = bil Q (a : V) e := by
      rw [he']; exact bil_eq_of_isometricLat Q Q g hg a ⟨e, heA⟩
    rw [hb]
    exact ⟨fun h0 => ⟨(g a).2, h0.2⟩, fun h0 => ⟨a.2, h0.2⟩⟩
  obtain ⟨hM1, hM2⟩ := cancel_split3 Q h hA
  obtain ⟨hM1', hM2'⟩ := cancel_split3 Q h' hA'
  obtain ⟨σ, hσ, -, hσC⟩ := exists_orthLat_apply_eq Q h2 hM1 hM1' hQe'.symm hQe
  have hsplit := cancel_orthSum_map Q hσ.1 hM2
  rw [hσC] at hsplit
  have hC'reg := IsOrthSum.isRegular_right Q hM1' hreg
  have hC'fg : (A₁' ⊔ B').FG := FG.of_le hM (hM1'.sup_eq ▸ le_sup_right)
  have hiso2 : IsometricLat Q Q (latMap σ A₁) A₁' :=
    cancel_iso_trans Q Q (cancel_iso_symm Q Q (isometricLat_latMap Q hσ.1 A₁)) hiso1
  obtain ⟨f, -⟩ := isometricLat_latMap Q hσ.1 A₁
  have hrk2 : finrank R (latMap σ A₁) < n := by
    rw [← f.finrank_eq]; omega
  have := ih _ hrk2 hC'fg hC'reg hsplit hM2' hiso2 rfl
  exact cancel_iso_trans Q Q (isometricLat_latMap Q hσ.1 B) this

/-- **Cancellation inside one lattice** (O'Meara 1963, 92:3, p. 248): over a non-dyadic field, if a regular lattice
$M$ has splittings $M = A \perp B = A' \perp B'$ with $A \cong A'$, then $B \cong B'$. -/
theorem isometricLat_cancel_of_isOrthSum (h2 : IsUnit (2 : R)) {M A B A' B' : Submodule R V} (hM : M.FG)
    (hreg : IsRegular Q M) (h : IsOrthSum Q M A B) (h' : IsOrthSum Q M A' B') (hAA' : IsometricLat Q Q A A') :
    IsometricLat Q Q B B' :=
  cancel_aux Q h2 _ hM hreg h h' hAA' rfl

/-- **Theorem 92:3** (O'Meara 1963, p. 248): let $L$ and $K$ be isometric lattices on regular quadratic spaces $V$ and
$U$ over a non-dyadic local field, with splittings $L = L' \perp L''$ and $K = K' \perp K''$ such that $L' \cong K'$.
Then $L'' \cong K''$. (Only the discrete valuation ring and $2 \in \mathfrak u$ are used; "on regular spaces" enters
through the regularity of $L$.) -/
@[kb "omeara1963" "§92, 92:3, p. 248"]
theorem isometricLat_cancel (h2 : IsUnit (2 : R)) {L L' L'' : Submodule R V} {K K' K'' : Submodule R V'}
    (hLfg : L.FG) (hreg : IsRegular Q L) (hLK : IsometricLat Q Q' L K) (hL : IsOrthSum Q L L' L'')
    (hK : IsOrthSum Q' K K' K'') (h' : IsometricLat Q Q' L' K') : IsometricLat Q Q' L'' K'' := by
  obtain ⟨f, hf⟩ := hLK
  obtain ⟨L'f, hL'f, hmL'⟩ := cancel_image f L'
  obtain ⟨L''f, hL''f, hmL''⟩ := cancel_image f L''
  have hL'L : L' ≤ L := hL.sup_eq ▸ le_sup_left
  have hL''L : L'' ≤ L := hL.sup_eq ▸ le_sup_right
  have hKsplit : IsOrthSum Q' K L'f L''f := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := (hmL' x).mp hx
      obtain ⟨b, hb, rfl⟩ := (hmL'' y).mp hy
      rw [bil_eq_of_isometricLat Q Q' f hf]; exact hL.orth _ ha _ hb
    · rw [Submodule.disjoint_def]
      intro z hz1 hz2
      obtain ⟨a, ha, rfl⟩ := (hmL' z).mp hz1
      obtain ⟨b, hb, hab⟩ := (hmL'' _).mp hz2
      have hba : b = a := f.injective (Subtype.ext hab)
      subst hba
      have hb0 : b = 0 := Subtype.ext (Submodule.disjoint_def.mp hL.disjoint b ha hb)
      simp [hb0]
    · apply le_antisymm
      · exact sup_le hL'f hL''f
      · intro z hz
        have hzL : ((f.symm ⟨z, hz⟩ : L) : V) ∈ L' ⊔ L'' := hL.sup_eq ▸ (f.symm ⟨z, hz⟩).2
        obtain ⟨p, hp, q, hq, hpq⟩ := mem_sup.mp hzL
        have hpL := hL'L hp
        have hqL := hL''L hq
        have hsum : f.symm ⟨z, hz⟩ = ⟨p, hpL⟩ + ⟨q, hqL⟩ := Subtype.ext hpq.symm
        have hz' : z = (f ⟨p, hpL⟩ : V') + (f ⟨q, hqL⟩ : V') := by
          have h3 : (f (f.symm ⟨z, hz⟩) : V') = z := by simp
          rw [← h3, hsum, map_add, Submodule.coe_add]
        rw [hz']
        exact add_mem (mem_sup_left ((hmL' _).mpr ⟨_, hp, rfl⟩))
          (mem_sup_right ((hmL'' _).mpr ⟨_, hq, rfl⟩))
  have hKfg : K.FG := by
    have : Module.Finite R L := Module.Finite.iff_fg.mpr hLfg
    have : Module.Finite R K := Module.Finite.equiv f
    exact Module.Finite.iff_fg.mp this
  have hKreg : IsRegular Q' K := by
    intro x hx h0
    obtain ⟨a, rfl⟩ : ∃ a : L, (f a : V') = x := ⟨f.symm ⟨x, hx⟩, by simp⟩
    have ha : (a : V) = 0 := hreg a a.2 fun y hy => by
      have := h0 (f ⟨y, hy⟩) (f ⟨y, hy⟩).2
      rw [bil_eq_of_isometricLat Q Q' f hf] at this
      exact this
    have : a = 0 := Subtype.ext ha
    simp [this]
  have hi1 : IsometricLat Q Q' L' L'f := cancel_iso_restrict Q Q' f hf hL'L hL'f fun a => by
    rw [hmL']
    constructor
    · intro ha; exact ⟨a, ha, rfl⟩
    · rintro ⟨b, hb, hba⟩
      have : b = a := f.injective (Subtype.ext hba)
      exact this ▸ hb
  have hi2 : IsometricLat Q Q' L'' L''f := cancel_iso_restrict Q Q' f hf hL''L hL''f fun a => by
    rw [hmL'']
    constructor
    · intro ha; exact ⟨a, ha, rfl⟩
    · rintro ⟨b, hb, hba⟩
      have : b = a := f.injective (Subtype.ext hba)
      exact this ▸ hb
  have hiK' : IsometricLat Q' Q' L'f K' := cancel_iso_trans Q' Q (cancel_iso_symm Q Q' hi1) h'
  have := isometricLat_cancel_of_isOrthSum Q' h2 hKfg hKreg hKsplit hK hiK'
  exact cancel_iso_trans Q Q' hi2 this

end NonDyadic

end QuadFormsKB.OMeara
