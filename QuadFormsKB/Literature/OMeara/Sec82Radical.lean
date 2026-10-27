/-
# O'Meara §82D: the radical of a lattice, radical splittings, components (82:7), and 82:9

**Setting.** $R$ is an integral domain with fraction field $F$ (a Dedekind domain where stated), $2 \in F^\times$, and
$(V, Q)$ a quadratic space over $F$ with O'Meara's bilinear form $B$ = `bil Q`. For an $R$-submodule $L$ of $V$ the
*radical* $\operatorname{rad} L = \{x \in L : B(x, L) = 0\}$ is `splitComp Q L L` (`Sec82.lean`: `splitComp Q L J` is
$\{x \in L : B(x, J) = 0\}$), and the radical of the subspace $FL$ is the same construction over $F$,
`splitComp (R := F) Q W W` with `W = span F L`. A lattice is regular when its radical is $0$ (`IsRegular`). A
sublattice $K$ *splits* $L$ (is a component of $L$) when $L = K \perp J$ for some $J$ (`∃ J, IsOrthSum Q L K J`).

**Proves** (O'Meara 1963, §82D–§82E, pp. 225–229):
* `span_splitComp_self` ($\operatorname{rad} FL = F\operatorname{rad} L$), `splitComp_self_eq_inf`
  ($\operatorname{rad} L = L \cap \operatorname{rad} FL$), `isRegular_iff_span` ($L$ regular if and only if $FL$ is),
  `IsOrthSum.splitComp_self` ($\operatorname{rad}(J \perp K) = \operatorname{rad} J \perp \operatorname{rad} K$),
  `IsOrthSum.isRegular_iff` (§82D, p. 225);
* `exists_radical_splitting` (every lattice has a radical splitting $L = K \perp \operatorname{rad} L$),
  `IsOrthSum.isRegular_of_radical` ($K$ is regular), `isometricLat_iff_of_radical` (two lattices with radical
  splittings are isometric if and only if the regular parts and the radicals are) (§82D, p. 226);
* `splits_iff_forall_of_isOrthSplit` (**82:7**);
* `Dedekind.exists_lattice_split_scale_norm` (**82:9**, over a Dedekind domain).
-/
import QuadFormsKB.Literature.OMeara.Sec81Adapted

import QuadFormsKB.Literature.OMeara.Sec93C

open QuadraticMap Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- If $B(x, L) = 0$ then $B(x, FL) = 0$. -/
theorem bil_zero_of_mem_span_F {L : Submodule R V} {x : V} (hx : ∀ z ∈ L, bil Q x z = 0) {z : V}
    (hz : z ∈ span F (L : Set V)) : bil Q x z = 0 := by
  refine span_induction (p := fun z _ => bil Q x z = 0) (fun w hw => hx w hw) (by simp [bil])
    (fun a b _ _ ha hb => by rw [bil_add_right, ha, hb, add_zero])
    (fun c a _ ha => by rw [bil_smul_right, ha, mul_zero]) hz

/-- $x = d^{-1}(d x)$ for a non-zero $d \in R$. -/
theorem eq_inv_smul_smul {d : R} (hd : d ≠ 0) (x : V) : x = (algebraMap R F d)⁻¹ • (d • x) := by
  have hd' : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hd
  rw [← algebraMap_smul F d x, smul_smul, inv_mul_cancel₀ hd', one_smul]

/-- $L$ is regular if and only if its radical is $0$. -/
theorem isRegular_iff_splitComp_eq_bot (L : Submodule R V) : IsRegular Q L ↔ splitComp Q L L = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro x hx
    exact (mem_bot R).mpr (h x hx.1 hx.2)
  · intro h x hx hx0
    have : x ∈ splitComp Q L L := ⟨hx, hx0⟩
    rw [h] at this
    exact (mem_bot R).mp this

/-- **$\operatorname{rad} FL = F\operatorname{rad} L$** (O'Meara 1963, §82D, p. 225). -/
@[kb "omeara1963" "§82D, p. 225 (rad FL = F rad L)"]
theorem span_splitComp_self (L : Submodule R V) :
    span F (splitComp Q L L : Set V) =
      splitComp (R := F) Q (span F (L : Set V)) (span F (L : Set V)) := by
  apply le_antisymm
  · rw [span_le]
    intro x hx
    exact ⟨subset_span hx.1, fun z hz => bil_zero_of_mem_span_F Q (fun w hw => hx.2 w hw) hz⟩
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem_of_mem_span (F := F) hx.1
    have hmem : d • x ∈ splitComp Q L L :=
      ⟨hdx, fun z hz => by rw [bil_rsmul_left, hx.2 z (subset_span hz), mul_zero]⟩
    rw [eq_inv_smul_smul (F := F) hd x]
    exact Submodule.smul_mem _ _ (subset_span hmem)

/-- **$\operatorname{rad} L = L \cap \operatorname{rad} FL$** (O'Meara 1963, §82D, p. 225). -/
@[kb "omeara1963" "§82D, p. 225 (rad L = L ∩ rad FL)"]
theorem splitComp_self_eq_inf (L : Submodule R V) :
    splitComp Q L L =
      L ⊓ (splitComp (R := F) Q (span F (L : Set V)) (span F (L : Set V))).restrictScalars R := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    rw [← span_splitComp_self Q L]
    exact subset_span hx
  · rintro ⟨hxL, hxW⟩
    exact ⟨hxL, fun z hz => hxW.2 z (subset_span hz)⟩

/-- **$L$ is regular if and only if $FL$ is regular** (O'Meara 1963, §82D, p. 225). -/
@[kb "omeara1963" "§82D, p. 225 (L regular iff FL regular)"]
theorem isRegular_iff_span (L : Submodule R V) :
    IsRegular Q L ↔ IsRegular (R := F) Q (span F (L : Set V)) := by
  constructor
  · intro h x hxW hx0
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem_of_mem_span (F := F) hxW
    have h0 : d • x = 0 :=
      h _ hdx fun z hz => by rw [bil_rsmul_left, hx0 z (subset_span hz), mul_zero]
    rw [eq_inv_smul_smul (F := F) hd x, h0, smul_zero]
  · intro h x hx hx0
    exact h x (subset_span hx) fun y hy => bil_zero_of_mem_span_F Q hx0 hy

/-- **$\operatorname{rad}(J \perp K) = (\operatorname{rad} J) \perp (\operatorname{rad} K)$** (O'Meara 1963, §82D,
p. 225). -/
@[kb "omeara1963" "§82D, p. 225 (rad(L ⊥ K) = rad L ⊥ rad K)"]
theorem IsOrthSum.splitComp_self {L J K : Submodule R V} (h : IsOrthSum Q L J K) :
    IsOrthSum Q (splitComp Q L L) (splitComp Q J J) (splitComp Q K K) := by
  have hJL : J ≤ L := h.sup_eq ▸ le_sup_left
  have hKL : K ≤ L := h.sup_eq ▸ le_sup_right
  refine ⟨fun x hx y hy => h.orth x hx.1 y hy.1, ?_, ?_⟩
  · exact h.disjoint.mono (fun x hx => hx.1) (fun x hx => hx.1)
  · apply le_antisymm
    swap
    · intro x hx
      have hxL : x ∈ J ⊔ K := h.sup_eq ▸ hx.1
      obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hxL
      have hj' : j ∈ splitComp Q J J := by
        refine ⟨hj, fun j' hj' => ?_⟩
        have h1 := hx.2 j' (hJL hj')
        rw [bil_add_left, bil_comm Q k j', h.orth j' hj' k hk, add_zero] at h1
        exact h1
      have hk' : k ∈ splitComp Q K K := by
        refine ⟨hk, fun k' hk' => ?_⟩
        have h1 := hx.2 k' (hKL hk')
        rw [bil_add_left, h.orth j hj k' hk', zero_add] at h1
        exact h1
      exact mem_sup.mpr ⟨j, hj', k, hk', rfl⟩
    · refine sup_le ?_ ?_
      · intro x hx
        refine ⟨hJL hx.1, fun z hz => ?_⟩
        rw [← h.sup_eq] at hz
        obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hz
        rw [bil_add_right, hx.2 j hj, h.orth x hx.1 k hk, add_zero]
      · intro x hx
        refine ⟨hKL hx.1, fun z hz => ?_⟩
        rw [← h.sup_eq] at hz
        obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hz
        rw [bil_add_right, bil_comm Q x j, h.orth j hj x hx.1, hx.2 k hk, add_zero]

/-- **$J \perp K$ is regular if and only if $J$ and $K$ are** (O'Meara 1963, §82D, pp. 225–226). -/
@[kb "omeara1963" "§82D, pp. 225–226 (L ⊥ K regular iff L and K regular)"]
theorem IsOrthSum.isRegular_iff {L J K : Submodule R V} (h : IsOrthSum Q L J K) :
    IsRegular Q L ↔ IsRegular Q J ∧ IsRegular Q K := by
  rw [isRegular_iff_splitComp_eq_bot, isRegular_iff_splitComp_eq_bot, isRegular_iff_splitComp_eq_bot,
    ← sup_eq_bot_iff, (IsOrthSum.splitComp_self Q h).sup_eq.symm]

/-- **The regular part of a radical splitting is regular** (O'Meara 1963, §82D, p. 226): if
$L = K \perp \operatorname{rad} L$ then $K$ is regular. -/
@[kb "omeara1963" "§82D, p. 226 (K in a radical splitting is regular)"]
theorem IsOrthSum.isRegular_of_radical {L K : Submodule R V} (h : IsOrthSum Q L K (splitComp Q L L)) :
    IsRegular Q K := by
  intro x hx hx0
  have hxL : x ∈ splitComp Q L L := by
    refine ⟨h.sup_eq ▸ mem_sup_left hx, fun z hz => ?_⟩
    rw [← h.sup_eq] at hz
    obtain ⟨k, hk, r, hr, rfl⟩ := mem_sup.mp hz
    rw [bil_add_right, hx0 k hk, h.orth x hx r hr, add_zero]
  have := h.disjoint.le_bot ⟨hx, hxL⟩
  exact (mem_bot R).mp this

/-- A splitting $L = J \perp K$ gives a linear isomorphism $J \times K \cong L$, $(j, k) \mapsto j + k$. -/
theorem IsOrthSum.exists_prodEquiv {L J K : Submodule R V} (h : IsOrthSum Q L J K) :
    ∃ e : (J × K) ≃ₗ[R] L, ∀ p, (e p : V) = p.1 + p.2 := by
  let ψ : (J × K) →ₗ[R] V := J.subtype.coprod K.subtype
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨j, k⟩ hjk
    have h0 : (j : V) + k = 0 := hjk
    have hj : (j : V) ∈ K := by
      have : (j : V) = -(k : V) := eq_neg_of_add_eq_zero_left h0
      rw [this]; exact K.neg_mem k.2
    have : (j : V) = 0 := (mem_bot R).mp (h.disjoint.le_bot ⟨j.2, hj⟩)
    have hj0 : j = 0 := Subtype.ext this
    have hk0 : k = 0 := Subtype.ext (by simpa [this] using h0)
    simp [hj0, hk0]
  have hrange : LinearMap.range ψ = L := by
    simp only [ψ, LinearMap.range_coprod, Submodule.range_subtype]
    exact h.sup_eq
  refine ⟨(LinearEquiv.ofInjective ψ hinj).trans (LinearEquiv.ofEq _ _ hrange), fun p => ?_⟩
  rfl

/-- $Q(k + r) = Q(k)$ for $k \in L$ and $r \in \operatorname{rad} L$. -/
theorem Q_add_of_mem_radical {L : Submodule R V} {k r : V} (hk : k ∈ L) (hr : r ∈ splitComp Q L L) :
    Q (k + r) = Q k := by
  have hQr : Q r = 0 := by rw [← bil_self]; exact hr.2 r hr.1
  rw [Q_add, bil_comm Q k r, hr.2 k hk, hQr]
  ring

/-- An isometry (a $B$-preserving isomorphism) of lattices maps the radical into the radical. -/
theorem radical_map_mem {L : Submodule R V} {L₁ : Submodule R V'} (f : L ≃ₗ[R] L₁)
    (hfb : ∀ x y : L, bil Q' (f x : V') (f y : V') = bil Q (x : V) (y : V)) {x : V}
    (hx : x ∈ splitComp Q L L) : (f ⟨x, hx.1⟩ : V') ∈ splitComp Q' L₁ L₁ := by
  refine ⟨(f _).2, fun z hz => ?_⟩
  have := hfb ⟨x, hx.1⟩ (f.symm ⟨z, hz⟩)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.trans (hx.2 _ (f.symm _).2)

/-- An isometry of lattices restricts to an isomorphism of the radicals. -/
theorem exists_radical_equiv {L : Submodule R V} {L₁ : Submodule R V'} (f : L ≃ₗ[R] L₁)
    (hfb : ∀ x y : L, bil Q' (f x : V') (f y : V') = bil Q (x : V) (y : V)) :
    ∃ g : splitComp Q L L ≃ₗ[R] splitComp Q' L₁ L₁, ∀ x, (g x : V') = f ⟨x, x.2.1⟩ := by
  have hfb' : ∀ a b : L₁, bil Q (f.symm a : V) (f.symm b : V) = bil Q' (a : V') (b : V') := by
    intro a b
    have := hfb (f.symm a) (f.symm b)
    simpa using this.symm
  let u : splitComp Q L L →ₗ[R] splitComp Q' L₁ L₁ :=
    { toFun := fun x => ⟨(f ⟨x, x.2.1⟩ : V'), radical_map_mem Q Q' f hfb x.2⟩
      map_add' := fun a b => Subtype.ext (congrArg (fun w : L₁ => (w : V'))
        (by rw [← map_add]; rfl : f ⟨((a + b : splitComp Q L L) : V), (a + b).2.1⟩ = f ⟨a, a.2.1⟩ + f ⟨b, b.2.1⟩))
      map_smul' := fun c a => Subtype.ext (congrArg (fun w : L₁ => (w : V'))
        (by rw [← map_smul]; rfl : f ⟨((c • a : splitComp Q L L) : V), (c • a).2.1⟩ = c • f ⟨a, a.2.1⟩)) }
  let v : splitComp Q' L₁ L₁ →ₗ[R] splitComp Q L L :=
    { toFun := fun x => ⟨(f.symm ⟨x, x.2.1⟩ : V), radical_map_mem Q' Q f.symm hfb' x.2⟩
      map_add' := fun a b => Subtype.ext (congrArg (fun w : L => (w : V))
        (by rw [← map_add]; rfl : f.symm ⟨((a + b : splitComp Q' L₁ L₁) : V'), (a + b).2.1⟩ =
          f.symm ⟨a, a.2.1⟩ + f.symm ⟨b, b.2.1⟩))
      map_smul' := fun c a => Subtype.ext (congrArg (fun w : L => (w : V))
        (by rw [← map_smul]; rfl : f.symm ⟨((c • a : splitComp Q' L₁ L₁) : V'), (c • a).2.1⟩ =
          c • f.symm ⟨a, a.2.1⟩)) }
  refine ⟨LinearEquiv.ofLinearMap u v ?_ ?_, fun x => rfl⟩
  · ext x; simp [u, v]
  · ext x; simp [u, v]

/-- **Isometry of lattices with radical splittings** (O'Meara 1963, §82D, p. 226, stated there without proof: "it can
be shown (using a proof somewhat similar to the proof of Proposition 42:8)"). If $L = K \perp \operatorname{rad} L$ and
$L_1 = K_1 \perp \operatorname{rad} L_1$ are radical splittings, then $L \cong L_1$ if and only if $K \cong K_1$ and
$\operatorname{rad} L \cong \operatorname{rad} L_1$. -/
@[kb "omeara1963" "§82D, p. 226 (L ≅ L₁ iff K ≅ K₁ and rad L ≅ rad L₁)"]
theorem isometricLat_iff_of_radical {L K : Submodule R V} {L₁ K₁ : Submodule R V'}
    (h : IsOrthSum Q L K (splitComp Q L L)) (h₁ : IsOrthSum Q' L₁ K₁ (splitComp Q' L₁ L₁)) :
    IsometricLat Q Q' L L₁ ↔
      IsometricLat Q Q' K K₁ ∧ IsometricLat Q Q' (splitComp Q L L) (splitComp Q' L₁ L₁) := by
  have hKL : K ≤ L := h.sup_eq ▸ le_sup_left
  have hK₁ : K₁ ≤ L₁ := h₁.sup_eq ▸ le_sup_left
  obtain ⟨eL, heL⟩ := IsOrthSum.exists_prodEquiv Q h
  obtain ⟨eL1, heL1⟩ := IsOrthSum.exists_prodEquiv Q' h₁
  constructor
  · rintro ⟨F, hF⟩
    have hbil := bil_eq_of_isometricLat Q Q' F hF
    obtain ⟨g, hg⟩ := exists_radical_equiv Q Q' F hbil
    refine ⟨?_, g, fun x => ?_⟩
    · let φ : K →ₗ[R] L := eL.toLinearMap ∘ₗ LinearMap.inl R K (splitComp Q L L)
      let c : K →ₗ[R] K₁ := LinearMap.fst R K₁ (splitComp Q' L₁ L₁) ∘ₗ eL1.symm.toLinearMap ∘ₗ
        F.toLinearMap ∘ₗ φ
      have hφ : ∀ k : K, (φ k : V) = k := by
        intro k
        have := heL (k, 0)
        simpa [φ] using this
      have hdec : ∀ k : K, (F (φ k) : V') =
          (c k : V') + ((eL1.symm (F (φ k))).2 : V') := by
        intro k
        have := heL1 (eL1.symm (F (φ k)))
        rw [LinearEquiv.apply_symm_apply] at this
        exact this
      have hcQ : ∀ k : K, Q' (c k : V') = Q (k : V) := by
        intro k
        have e1 : Q' (F (φ k) : V') = Q' (c k : V') := by
          rw [hdec k]
          exact Q_add_of_mem_radical Q' (hK₁ (c k).2) (eL1.symm (F (φ k))).2.2
        rw [← e1, hF, hφ]
      have hinj : Function.Injective c := by
        rw [injective_iff_map_eq_zero]
        intro k hk0
        have hFk : (F (φ k) : V') ∈ splitComp Q' L₁ L₁ := by
          rw [hdec k, hk0, Submodule.coe_zero, zero_add]
          exact (eL1.symm (F (φ k))).2.2
        have hkρ : (k : V) ∈ splitComp Q L L := by
          refine ⟨hKL k.2, fun z hz => ?_⟩
          have := hbil (φ k) ⟨z, hz⟩
          rw [hφ] at this
          rw [← this]
          exact hFk.2 _ (F ⟨z, hz⟩).2
        have : (k : V) = 0 := (mem_bot R).mp (h.disjoint.le_bot ⟨k.2, hkρ⟩)
        exact Subtype.ext this
      have hsurj : Function.Surjective c := by
        intro k₁
        let l : L := F.symm ⟨k₁, hK₁ k₁.2⟩
        let p := eL.symm l
        have hl' : (l : V) = (p.1 : V) + (p.2 : V) := by
          have := heL p
          rwa [LinearEquiv.apply_symm_apply] at this
        refine ⟨p.1, ?_⟩
        have hlsplit : l = φ p.1 + ⟨(p.2 : V), p.2.2.1⟩ :=
          Subtype.ext (by rw [hl']; exact congrArg (fun w => w + (p.2 : V)) (hφ p.1).symm)
        have hFl : F l = ⟨k₁, hK₁ k₁.2⟩ := F.apply_symm_apply _
        have h1 : (k₁ : V') = (c p.1 : V') + ((eL1.symm (F (φ p.1))).2 : V') +
            (F ⟨(p.2 : V), p.2.2.1⟩ : V') := by
          have e := congrArg (fun w : L₁ => (w : V')) hFl
          simp only at e
          rw [← e, hlsplit, map_add, Submodule.coe_add, hdec p.1]
        have h2 : (F ⟨(p.2 : V), p.2.2.1⟩ : V') ∈ splitComp Q' L₁ L₁ :=
          radical_map_mem Q Q' F hbil p.2.2
        have h3 : ((k₁ - c p.1 : K₁) : V') ∈ splitComp Q' L₁ L₁ := by
          have : ((k₁ - c p.1 : K₁) : V') =
              ((eL1.symm (F (φ p.1))).2 : V') + (F ⟨(p.2 : V), p.2.2.1⟩ : V') := by
            rw [Submodule.coe_sub, h1]; abel
          rw [this]
          exact add_mem (eL1.symm (F (φ p.1))).2.2 h2
        have : ((k₁ - c p.1 : K₁) : V') = 0 := (mem_bot R).mp (h₁.disjoint.le_bot ⟨(k₁ - c p.1).2, h3⟩)
        have h4 : k₁ - c p.1 = 0 := Subtype.ext this
        exact (sub_eq_zero.mp h4).symm
      exact ⟨LinearEquiv.ofBijective c ⟨hinj, hsurj⟩, fun x => hcQ x⟩
    · rw [hg x]
      exact hF ⟨x, x.2.1⟩
  · rintro ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
    refine ⟨eL.symm.trans ((f.prodCongr g).trans eL1), fun x => ?_⟩
    obtain ⟨p, rfl⟩ := eL.surjective x
    have e1 : ((eL.symm.trans ((f.prodCongr g).trans eL1)) (eL p) : V') =
        (f p.1 : V') + (g p.2 : V') := by
      simp [heL1]
    rw [e1, heL, Q_add_of_mem_radical Q' (hK₁ (f p.1).2) (g p.2).2,
      Q_add_of_mem_radical Q (hKL p.1.2) p.2.2]
    exact hf p.1

/-- **Proposition 82:7** (O'Meara 1963, pp. 226–227). Let $K$ be a regular sublattice of the lattice $L$ with a
splitting $K = K_1 \perp \cdots \perp K_r$. Then $K$ is a component of $L$ if and only if each $K_i$ is. (The hypothesis
$K \subseteq L$ is implied by either side and is omitted.) -/
@[kb "omeara1963" "§82D, 82:7, pp. 226–227"]
theorem splits_iff_forall_of_isOrthSplit {L K : Submodule R V} (hK : IsRegular Q K)
    {ι : Type*} [Fintype ι] {Ks : ι → Submodule R V} (hs : IsOrthSplit Q K Ks) :
    (∃ J, IsOrthSum Q L K J) ↔ ∀ i, ∃ J, IsOrthSum Q L (Ks i) J := by
  classical
  have hKi : ∀ i, Ks i ≤ K := fun i => hs.iSup_eq ▸ le_iSup Ks i
  constructor
  · rintro ⟨J, hJ⟩ i
    refine ⟨J ⊔ ⨆ (j) (_ : j ≠ i), Ks j, ?_, ?_, ?_⟩
    · intro x hx y hy
      obtain ⟨j, hj, m, hm, rfl⟩ := mem_sup.mp hy
      rw [bil_add_right, hJ.orth x (hKi i hx) j hj, zero_add, bil_comm]
      exact bil_eq_zero_of_mem_iSup Q (P := fun j => j ≠ i)
        (fun j hj w hw => hs.orth j i hj w hw x hx) hm
    · rw [disjoint_iff, eq_bot_iff]
      rintro x ⟨hx, hx'⟩
      obtain ⟨j, hj, m, hm, hjm⟩ := mem_sup.mp hx'
      have hmK : m ∈ K := (iSup₂_le fun j _ => hKi j : (⨆ (j) (_ : j ≠ i), Ks j) ≤ K) hm
      have hj0 : j = 0 := by
        have hjK : j ∈ K := by
          have : j = x - m := by rw [← hjm]; abel
          rw [this]; exact K.sub_mem (hKi i hx) hmK
        exact (mem_bot R).mp (hJ.disjoint.le_bot ⟨hjK, hj⟩)
      have hxm : x = m := by rw [← hjm, hj0, zero_add]
      have : x ∈ Ks i ⊓ ⨆ (j) (_ : j ≠ i), Ks j := ⟨hx, hxm ▸ hm⟩
      exact (hs.indep i).le_bot this
    · rw [← hJ.sup_eq, ← hs.iSup_eq, iSup_split_single Ks i, sup_left_comm, sup_comm]
  · intro h
    choose J' hJ' using h
    have hKL : K ≤ L := by
      refine hs.iSup_eq ▸ iSup_le fun i => ?_
      exact (hJ' i).sup_eq ▸ le_sup_left
    refine ⟨splitComp Q L K, ⟨?_, ?_, ?_⟩⟩
    · intro x hx y hy
      rw [bil_comm]; exact hy.2 x hx
    · rw [disjoint_iff, eq_bot_iff]
      rintro x ⟨hx, hx'⟩
      exact (mem_bot R).mpr (hK x hx fun z hz => hx'.2 z hz)
    · apply le_antisymm
      · exact sup_le hKL (fun x hx => hx.1)
      · intro x hx
        choose xi hxi yi hyi hsum using fun i => mem_sup.mp ((hJ' i).sup_eq ▸ hx)
        have hsK : ∑ i, xi i ∈ K := sum_mem fun i _ => hKi i (hxi i)
        have hxs : x - ∑ i, xi i ∈ splitComp Q L K := by
          refine ⟨L.sub_mem hx (hKL hsK), fun z hz => ?_⟩
          rw [← hs.iSup_eq] at hz
          rw [bil_comm]
          refine iSup_induction Ks (motive := fun z => bil Q z (x - ∑ i, xi i) = 0) hz
            (fun j z hz => ?_) (by simp [bil]) (fun a b ha hb => by rw [bil_add_left, ha, hb, add_zero])
          have e : bil Q z x = bil Q z (xi j) := by
            rw [← hsum j, bil_add_right, (hJ' j).orth z hz (yi j) (hyi j), add_zero]
          rw [bil_sub_right, bil_sum_right, e, Finset.sum_eq_single j, sub_self]
          · intro i _ hij
            exact hs.orth j i (Ne.symm hij) z hz (xi i) (hxi i)
          · simp
        exact mem_sup.mpr ⟨_, hsK, _, hxs, by abel⟩

end Domain

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Every lattice has a radical splitting** (O'Meara 1963, §82D, p. 226): $L = K \perp \operatorname{rad} L$ for some
$K$ (O'Meara's proof uses Theorem 81:3 with a base of $FL$ whose first vectors span $\operatorname{rad} FL$). -/
@[kb "omeara1963" "§82D, p. 226 (radical splitting L = K ⊥ rad L)"]
theorem exists_radical_splitting [FiniteDimensional F V] {L : Submodule R V} (hL : L.FG) :
    ∃ K, IsOrthSum Q L K (splitComp Q L L) := by
  classical
  let ρ := splitComp Q L L
  let N : Submodule R L := ρ.comap L.subtype
  have : Module.Finite R L := Module.Finite.iff_fg.mpr hL
  have := isTorsionFree_of_fractionRing (R := R) (F := F) (V := V)
  have : Module.IsTorsionFree R (L ⧸ N) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun d q h => ?_
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      by_cases hd : d = 0
      · exact Or.inl hd
      · right
        have h1 : d • x ∈ N := (Submodule.Quotient.mk_eq_zero N).mp (by simpa using h)
        have hd' : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hd
        refine (Submodule.Quotient.mk_eq_zero N).mpr ⟨x.2, fun z hz => ?_⟩
        have h2 : bil Q (d • (x : V)) z = 0 := h1.2 z hz
        rw [bil_rsmul_left] at h2
        exact (mul_eq_zero.mp h2).resolve_left hd'
  have : Module.FinitePresentation R (L ⧸ N) := Module.finitePresentation_of_finite R _
  have : Module.Projective R (L ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective N.mkQ
    (LinearMap.range_eq_top.mpr N.mkQ_surjective)
  have hs' : ∀ m, N.mkQ (s m) = m := fun m => LinearMap.congr_fun hs m
  refine ⟨(LinearMap.range s).map L.subtype, ⟨?_, ?_, ?_⟩⟩
  · rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩ y hy
    rw [bil_comm]; exact hy.2 _ (s m).2
  · rw [disjoint_iff, eq_bot_iff]
    rintro _ ⟨⟨_, ⟨m, rfl⟩, rfl⟩, hxρ⟩
    have h1 : N.mkQ (s m) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hxρ
    rw [hs'] at h1
    simp [h1]
  · apply le_antisymm
    · exact sup_le (by rintro _ ⟨y, -, rfl⟩; exact y.2) (fun x hx => hx.1)
    · intro x hx
      have h1 : (⟨x, hx⟩ : L) - s (N.mkQ ⟨x, hx⟩) ∈ N :=
        (Submodule.Quotient.mk_eq_zero N).mp (by
          rw [← Submodule.mkQ_apply, map_sub, hs']; exact sub_self _)
      refine mem_sup.mpr ⟨(s (N.mkQ ⟨x, hx⟩) : V), ⟨_, ⟨_, rfl⟩, rfl⟩, x - (s (N.mkQ ⟨x, hx⟩) : V), ?_, by abel⟩
      exact h1

/-- **Proposition 82:9** (O'Meara 1963, p. 229), over a Dedekind domain. Let $K$ be a regular non-zero lattice in the
quadratic space $V$. Then there is a lattice $L$ on $V$ which is split by $K$ and has the same scale and norm as $K$. -/
@[kb "omeara1963" "§82E, 82:9, p. 229"]
theorem Dedekind.exists_lattice_split_scale_norm [FiniteDimensional F V] {K : Submodule R V} (hK : K.FG)
    (hKreg : IsRegular Q K) (hK0 : K ≠ ⊥) :
    ∃ L : Submodule R V, L.IsLattice F ∧ (∃ J, IsOrthSum Q L K J) ∧ scale Q L = scale Q K ∧
      normIdeal Q L = normIdeal Q K := by
  classical
  set W : Submodule F V := span F (K : Set V) with hWdef
  have hW : IsRegular (R := F) Q W := (isRegular_iff_span Q K).mp hKreg
  let B : LinearMap.BilinForm F V := QuadraticMap.associated Q
  have hBapp : ∀ x y, B x y = bil Q x y := fun x y => rfl
  have hrefl : B.IsRefl := fun x y h => by
    rw [hBapp] at h ⊢; rw [bil_comm]; exact h
  have hnd : (B.restrict W).Nondegenerate := by
    have key : ∀ x : W, (∀ y : W, B.restrict W x y = 0) → x = 0 := by
      intro x hx
      exact Subtype.ext (hW x x.2 fun y hy => hx ⟨y, hy⟩)
    exact ⟨key, fun x hx => key x fun y => by
      have h := hx y
      show bil Q x y = 0
      rw [bil_comm]; exact h⟩
  have hcompl : IsCompl W (B.orthogonal W) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hnd
  set U : Submodule F V := B.orthogonal W with hUdef
  have hUorth : ∀ x ∈ W, ∀ y ∈ U, bil Q x y = 0 := fun x hx y hy => hy x hx
  -- a non-zero value of `Q` on `K`
  obtain ⟨z, hzK, hzQ⟩ : ∃ z ∈ K, Q z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK0
    refine hx0 (hKreg x hxK fun y hy => ?_)
    have h1 := Q_add Q x y
    rw [hcon _ (K.add_mem hxK hy), hcon x hxK, hcon y hy] at h1
    have h2 : (2 : F) * bil Q x y = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h2).resolve_left (two_ne_zero' F)
  have hc : Q z ∈ normIdeal Q K := Q_mem_normIdeal Q hzK
  -- a basis of the complement
  let b := Module.finBasis F U
  let u : Fin (finrank F U) → V := fun i => (b i : V)
  have hu : ∀ i, u i ∈ U := fun i => (b i).2
  obtain ⟨β, hβ⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) (S := F)
    (Finset.univ : Finset (Fin (finrank F U) × Fin (finrank F U)))
    (fun p => bil Q (u p.1) (u p.2) / Q z)
  set d : R := (β : R) with hd
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero β.2
  have hdK : ∀ i j, algebraMap R F d * algebraMap R F d * bil Q (u i) (u j) ∈ normIdeal Q K := by
    intro i j
    obtain ⟨a, ha⟩ := hβ (i, j) (Finset.mem_univ _)
    have : algebraMap R F d * algebraMap R F d * bil Q (u i) (u j) = (d * a) • Q z := by
      rw [Algebra.smul_def, map_mul, ha, Algebra.smul_def]
      field_simp
    rw [this]
    exact (normIdeal Q K).smul_mem _ hc
  let v : Fin (finrank F U) → V := fun i => d • u i
  let J : Submodule R V := span R (Set.range v)
  have hbv : ∀ i j, bil Q (v i) (v j) = algebraMap R F d * algebraMap R F d * bil Q (u i) (u j) := by
    intro i j
    simp only [v, bil_rsmul_left, bil_rsmul_right]
    ring
  have hJU : ∀ x ∈ J, x ∈ U := by
    intro x hx
    refine span_induction (p := fun x _ => x ∈ U) ?_ U.zero_mem (fun a b _ _ ha hb => U.add_mem ha hb)
      (fun c a _ ha => U.smul_of_tower_mem c ha) hx
    rintro _ ⟨i, rfl⟩
    exact U.smul_of_tower_mem d (hu i)
  have hnJ : normIdeal Q J ≤ normIdeal Q K := by
    rw [normIdeal, span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun R).mp hx
    rw [Q_sum_R]
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    rw [hbv]
    have : algebraMap R F (c i) * algebraMap R F (c j) *
        (algebraMap R F d * algebraMap R F d * bil Q (u i) (u j)) =
        (c i * c j) • (algebraMap R F d * algebraMap R F d * bil Q (u i) (u j)) := by
      rw [Algebra.smul_def, map_mul]
    rw [this]
    exact (normIdeal Q K).smul_mem _ (hdK i j)
  have hsJ : scale Q J ≤ normIdeal Q K := by
    rw [scale_span, span_le]
    rintro _ ⟨p, rfl⟩
    show bil Q (v p.1) (v p.2) ∈ normIdeal Q K
    rw [hbv]
    exact hdK p.1 p.2
  have hKW : ∀ x ∈ K, x ∈ W := fun x hx => subset_span hx
  have horth : ∀ x ∈ K, ∀ y ∈ J, bil Q x y = 0 := fun x hx y hy => hUorth x (hKW x hx) y (hJU y hy)
  have hdisj : Disjoint K J := by
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxK, hxJ⟩
    have : x ∈ W ⊓ U := ⟨hKW x hxK, hJU x hxJ⟩
    rw [hcompl.inf_eq_bot] at this
    exact this
  refine ⟨K ⊔ J, ⟨hK.sup (fg_span (Set.finite_range _)), ?_⟩, ⟨J, horth |> fun ho => ⟨ho, hdisj, rfl⟩⟩, ?_, ?_⟩
  · -- `F (K ⊔ J) = V`
    have hbU : span F (Set.range u) = U := by
      have h1 : Submodule.map U.subtype (span F (Set.range b)) = span F (U.subtype '' Set.range b) :=
        Submodule.map_span _ _
      rw [b.span_eq, Submodule.map_top, Submodule.range_subtype] at h1
      refine Eq.trans ?_ h1.symm
      congr 1
      rw [← Set.range_comp]; rfl
    have hd' : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hd0
    have hUle : U ≤ span F ((K ⊔ J : Submodule R V) : Set V) := by
      rw [← hbU, span_le]
      rintro _ ⟨i, rfl⟩
      have hvi : v i ∈ span F ((K ⊔ J : Submodule R V) : Set V) :=
        subset_span (mem_sup_right (subset_span ⟨i, rfl⟩))
      have : u i = (algebraMap R F d)⁻¹ • v i := eq_inv_smul_smul (F := F) hd0 (u i)
      rw [this]
      exact Submodule.smul_mem _ _ hvi
    have hWle : W ≤ span F ((K ⊔ J : Submodule R V) : Set V) :=
      span_mono (fun x hx => mem_sup_left hx)
    rw [eq_top_iff, ← hcompl.sup_eq_top]
    exact sup_le hWle hUle
  · rw [scale_sup_of_orth Q horth]
    exact sup_eq_left.mpr (hsJ.trans (normIdeal_le_scale Q K))
  · rw [normIdeal_sup_of_orth Q horth]
    exact sup_eq_left.mpr hnJ

end Dedekind

end QuadFormsKB.OMeara
