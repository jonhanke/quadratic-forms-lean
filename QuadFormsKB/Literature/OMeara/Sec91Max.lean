/-
# O'Meara §91A: all $\mathfrak a$-maximal lattices on a space are in one class (Theorem 91:2)

**Setting** (as in `Sec91.lean`): $R$ a Henselian discrete valuation ring with fraction field $F$, $2 \in F^\times$, a
finite-dimensional regular quadratic space $(V, Q)$ over $F$, lattices = `Submodule R V`.

**Proves**
* `IsMaxIn.latMap`: an isometry of $V$ preserving a subspace $W$ carries $\mathfrak a$-maximal lattices on $W$ to
  $\mathfrak a$-maximal lattices on $W$;
* `IsMaxIn.complement`: if $L = J \perp L'$ with $L$ $\mathfrak a$-maximal on $W$ and $J$ regular, then $L'$ is
  $\mathfrak a$-maximal on $W \cap J^\perp$ (O'Meara 1963, §82H, p. 234: components of a maximal lattice are maximal);
* `exists_orth_of_isMaxIn`: two $\mathfrak a$-maximal lattices on a regular subspace $W$ are carried onto each other
  by an isometry of $V$ fixing $W^\perp$;
* `mem_cls_of_isMaximal` (**Theorem 91:2**, p. 240): all $\mathfrak a$-maximal lattices on $V$ are in one class.

*Proof* (O'Meara's proof uses the simultaneous splitting 82:23; here instead): by induction on $\dim W$. If $W$ is
anisotropic the maximal lattice is unique (91:1). Otherwise both lattices split off a hyperbolic plane
$\mathfrak ox_0 + \mathfrak oy$ with $B(x_0, y) = \gamma$, $2\gamma\mathfrak o = \mathfrak a$ (82:20); Witt's extension
theorem moves one plane onto the other, and the complements are maximal on the same subspace $W \cap J^\perp$.
-/
import QuadFormsKB.Literature.OMeara.Sec91MaxA
import QuadFormsKB.Literature.OMeara.Sec91MaxW
import QuadFormsKB.Literature.OMeara.Sec92Jordan
import QuadFormsKB.Literature.OMeara.Sec93C

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- The image of an $R$-submodule under $\sigma$ spans the image of its span. -/
theorem span_latMap (σ : V ≃ₗ[F] V) (L : Submodule R V) :
    span F (latMap σ L : Set V) = (span F (L : Set V)).map (σ : V →ₗ[F] V) := by
  rw [Submodule.map_span]
  rfl

/-- **Isometries preserving $W$ carry maximal lattices on $W$ to maximal lattices on $W$.** -/
theorem IsMaxIn.latMap {a : Submodule R F} {W : Submodule F V} {L : Submodule R V} (hL : IsMaxIn Q a W L)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (hσW : W.map (σ : V →ₗ[F] V) = W) :
    IsMaxIn Q a W (OMeara.latMap σ L) := by
  obtain ⟨hfg, hspan, hn, hmax⟩ := hL
  have hnorm' : ∀ τ ∈ orth Q, ∀ M : Submodule R V, normIdeal Q (OMeara.latMap τ M) = normIdeal Q M := by
    intro τ hσ M
    rw [normIdeal, normIdeal]
    congr 1
    ext c
    simp only [Set.mem_image, SetLike.mem_coe, OMeara.latMap, Submodule.mem_map, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩; exact ⟨m, hm, (hσ m).symm⟩
    · rintro ⟨m, hm, rfl⟩; exact ⟨τ m, ⟨m, hm, rfl⟩, hσ m⟩
  have hnorm := hnorm' σ hσ
  have hσinv : σ⁻¹ ∈ orth Q := (orth Q).inv_mem hσ
  have hσW' : W.map ((σ⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) = W := by
    conv_lhs => rw [← hσW]
    rw [← Submodule.map_comp]
    convert Submodule.map_id W
    ext v; simp
  have hlat : ∀ M : Submodule R V, OMeara.latMap σ⁻¹ (OMeara.latMap σ M) = M := by
    intro M; rw [← latMap_mul, inv_mul_cancel, latMap_one]
  refine ⟨hfg.map _, by rw [span_latMap, hspan, hσW], by rw [hnorm]; exact hn, fun M hMfg hLM hMW hMn => ?_⟩
  have h1 : OMeara.latMap σ⁻¹ M = L := by
    refine hmax _ (hMfg.map _) ?_ ?_ ?_
    · rw [← hlat L]; exact Submodule.map_mono hLM
    · rintro _ ⟨m, hm, rfl⟩
      have : (σ⁻¹ m) ∈ W.map ((σ⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) := ⟨m, hMW hm, rfl⟩
      rw [hσW'] at this; exact this
    · rw [hnorm' _ hσinv]; exact hMn
  rw [← h1, ← latMap_mul, mul_inv_cancel, latMap_one]

/-- $W \cap J^\perp$ for an $F$-subspace $W$ and a lattice $J$. -/
def perpIn (W : Submodule F V) (J : Submodule R V) : Submodule F V where
  carrier := {w | w ∈ W ∧ ∀ j ∈ J, bil Q w j = 0}
  add_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨W.add_mem ha hb, fun j hj => by rw [bil_add_left, ha' j hj, hb' j hj,
    add_zero]⟩
  zero_mem' := ⟨W.zero_mem, fun j _ => by simp [bil]⟩
  smul_mem' := fun c _ ⟨ha, ha'⟩ => ⟨W.smul_mem c ha, fun j hj => by rw [bil_smul_left, ha' j hj, mul_zero]⟩

/-- **Components of a maximal lattice are maximal** (O'Meara 1963, §82H, p. 234): if $L$ is $\mathfrak a$-maximal on
$W$ and $L = J \perp L'$ with $J$ regular, then $L'$ is $\mathfrak a$-maximal on $W \cap J^\perp$. -/
@[kb "omeara1963" "§82H, p. 234 (components of an a-maximal lattice are a-maximal)"]
theorem IsMaxIn.complement {a : Submodule R F} {W : Submodule F V} {L J L' : Submodule R V}
    (hL : IsMaxIn Q a W L) (hs : IsOrthSum Q L J L') (hJ : IsRegular Q J) :
    IsMaxIn Q a (perpIn Q W J) L' := by
  obtain ⟨hfg, hspan, hn, hmax⟩ := hL
  have hJL : J ≤ L := hs.sup_eq ▸ le_sup_left
  have hL'L : L' ≤ L := hs.sup_eq ▸ le_sup_right
  have hLW : ∀ x ∈ L, x ∈ W := fun x hx => hspan ▸ subset_span hx
  have hL'eq : L' = splitComp Q L J := IsOrthSum.eq_splitComp Q hs hJ
  refine ⟨FG.of_le hfg hL'L, ?_, (normIdeal_mono Q hL'L).trans hn, fun M hMfg hL'M hMW hMn => ?_⟩
  · apply le_antisymm
    · rw [span_le]
      intro x hx
      exact ⟨hLW x (hL'L hx), fun j hj => by rw [bil_comm]; exact hs.orth j hj x hx⟩
    · rintro w ⟨hwW, hwJ⟩
      rw [← hspan] at hwW
      obtain ⟨d, hd, hdw⟩ := exists_smul_mem_of_mem_span (R := R) hwW
      rw [← hs.sup_eq] at hdw
      obtain ⟨j, hj, l, hl, hjl⟩ := mem_sup.mp hdw
      have hj0 : j = 0 := hJ j hj fun j' hj' => by
        have h1 : bil Q (d • w) j' = 0 := by rw [bil_rsmul_left, hwJ j' hj', mul_zero]
        rw [← hjl, bil_add_left, bil_comm Q l j', hs.orth j' hj' l hl, add_zero] at h1
        exact h1
      rw [hj0, zero_add] at hjl
      have hd' : algebraMap R F d ≠ 0 := fun h => hd ((IsFractionRing.injective R F) (h.trans (map_zero _).symm))
      have : w = (algebraMap R F d)⁻¹ • (d • w) := by
        rw [← algebraMap_smul F d w, smul_smul, inv_mul_cancel₀ hd', one_smul]
      rw [this]
      exact smul_mem _ _ (subset_span (hjl ▸ hl))
  · -- `J ⊔ M` is a lattice on `W` containing `L` with norm in `a`
    have hJM : ∀ x ∈ J, ∀ y ∈ M, bil Q x y = 0 := fun x hx y hy => by
      rw [bil_comm]; exact (hMW hy).2 x hx
    have hN : J ⊔ M = L := by
      refine hmax _ ((FG.of_le hfg hJL).sup hMfg) ?_ ?_ ?_
      · rw [← hs.sup_eq]; exact sup_le_sup_left hL'M J
      · rintro x hx
        obtain ⟨j, hj, m, hm, rfl⟩ := mem_sup.mp hx
        exact W.add_mem (hLW j (hJL hj)) (hMW hm).1
      · rw [normIdeal_sup_of_orth Q hJM]
        exact sup_le ((normIdeal_mono Q hJL).trans hn) hMn
    apply le_antisymm
    · intro m hm
      rw [hL'eq]
      refine ⟨hN ▸ mem_sup_right hm, fun j hj => ?_⟩
      exact (hMW hm).2 j hj
    · exact hL'M

omit [IsDiscreteValuationRing R] in
/-- A hyperbolic pair spans a regular lattice. -/
theorem isRegular_hyp {x y : V} {γ : F} (hγ : γ ≠ 0) (hQx : Q x = 0) (hQy : Q y = 0) (hxy : bil Q x y = γ) :
    IsRegular Q (span R {x, y}) := by
  intro z hz h0
  obtain ⟨a, b, rfl⟩ := mem_span_pair.mp hz
  have h1 := h0 x (subset_span (by simp))
  have h2 := h0 y (subset_span (by simp))
  rw [bil_add_left, bil_rsmul_left, bil_rsmul_left, bil_self, hQx, bil_comm Q y x, hxy] at h1
  rw [bil_add_left, bil_rsmul_left, bil_rsmul_left, bil_self, hQy, hxy] at h2
  have hb : algebraMap R F b = 0 := by
    have : algebraMap R F b * γ = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_right hγ
  have ha : algebraMap R F a = 0 := by
    have : algebraMap R F a * γ = 0 := by linear_combination h2
    exact (mul_eq_zero.mp this).resolve_right hγ
  have ha' : a = 0 := (IsFractionRing.injective R F) (ha.trans (map_zero _).symm)
  have hb' : b = 0 := (IsFractionRing.injective R F) (hb.trans (map_zero _).symm)
  simp [ha', hb']

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
theorem latMap_span_pair (σ : V ≃ₗ[F] V) (x y : V) :
    OMeara.latMap σ (span R {x, y}) = span R {σ x, σ y} := by
  rw [OMeara.latMap, Submodule.map_span, Set.image_pair]
  rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
/-- An isometry of $V$ carries an orthogonal splitting to an orthogonal splitting. -/
theorem isOrthSum_latMap {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) {L J K : Submodule R V} (h : IsOrthSum Q L J K) :
    IsOrthSum Q (OMeara.latMap σ L) (OMeara.latMap σ J) (OMeara.latMap σ K) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [bil_orth Q hσ]; exact h.orth x hx y hy
  · exact Submodule.disjoint_map (f := ((σ : V →ₗ[F] V).restrictScalars R)) σ.injective h.disjoint
  · rw [OMeara.latMap, OMeara.latMap, OMeara.latMap, ← Submodule.map_sup, h.sup_eq]

/-- Every vector of $W$ is a combination of a hyperbolic pair $x, y$ in $W$ and a vector of $W \cap J^\perp$,
$J = \mathfrak ox + \mathfrak oy$. -/
theorem exists_decomp_hyp {W : Submodule F V} {x y : V} {γ : F} (hγ : γ ≠ 0) (hxW : x ∈ W) (hyW : y ∈ W)
    (hQx : Q x = 0) (hQy : Q y = 0) (hxy : bil Q x y = γ) {z : V} (hz : z ∈ W) :
    ∃ a b : F, z - a • x - b • y ∈ perpIn Q W (span R {x, y}) := by
  refine ⟨bil Q z y / γ, bil Q z x / γ, W.sub_mem (W.sub_mem hz (W.smul_mem _ hxW)) (W.smul_mem _ hyW),
    fun j hj => ?_⟩
  refine bil_eq_zero_of_mem_span Q (z := ![x, y]) (fun i => ?_) (by
    rwa [show Set.range ![x, y] = {x, y} by ext v; simp [eq_comm, or_comm]])
  fin_cases i
  · show bil Q (z - (bil Q z y / γ) • x - (bil Q z x / γ) • y) x = 0
    rw [bil_sub_left, bil_sub_left, bil_smul_left, bil_smul_left, bil_self, hQx, bil_comm Q y x, hxy]
    field_simp; ring
  · show bil Q (z - (bil Q z y / γ) • x - (bil Q z x / γ) • y) y = 0
    rw [bil_sub_left, bil_sub_left, bil_smul_left, bil_smul_left, bil_self, hQy, hxy]
    field_simp; ring

/-- **Two $\mathfrak a$-maximal lattices on a regular subspace $W$ are carried onto each other by an isometry of $V$
fixing $W^\perp$ pointwise and preserving $W$** (the inductive form of 91:2). -/
theorem exists_orth_of_isMaxIn [HenselianLocalRing R] [FiniteDimensional F V]
    (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (n : ℕ) :
    ∀ W : Submodule F V, finrank F W = n → (∀ w ∈ W, (∀ w' ∈ W, bil Q w w' = 0) → w = 0) →
      ∀ L K : Submodule R V, IsMaxIn Q a W L → IsMaxIn Q a W K →
        ∃ σ ∈ orth Q, (∀ v, (∀ w ∈ W, bil Q v w = 0) → σ v = v) ∧ (∀ w ∈ W, σ w ∈ W) ∧
          OMeara.latMap σ L = K := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hn hWreg L K hL hK
  have hLW : ∀ z ∈ L, z ∈ W := fun z hz => hL.2.1 ▸ subset_span hz
  have hKW : ∀ z ∈ K, z ∈ W := fun z hz => hK.2.1 ▸ subset_span hz
  by_cases hiso : ∀ w ∈ W, Q w = 0 → w = 0
  · -- anisotropic: the maximal lattice is unique (91:1)
    refine ⟨1, (orth Q).one_mem, fun v _ => rfl, fun w hw => hw, ?_⟩
    rw [latMap_one]
    ext z
    constructor
    · intro hz
      have hzW := hLW z hz
      exact (mem_iff_of_isMaxIn Q hiso hK hzW).mpr ((mem_iff_of_isMaxIn Q hiso hL hzW).mp hz)
    · intro hz
      have hzW := hKW z hz
      exact (mem_iff_of_isMaxIn Q hiso hL hzW).mpr ((mem_iff_of_isMaxIn Q hiso hK hzW).mp hz)
  push Not at hiso
  obtain ⟨w, hwW, hQw, hw0⟩ := hiso
  have := isTorsionFree_of_fractionRing (R := R) (F := F) (V := V)
  have hiso_lat : ∀ M, IsMaxIn Q a W M → ∃ x ∈ M, x ≠ 0 ∧ Q x = 0 := by
    intro M hM
    obtain ⟨d, hd, hdw⟩ := exists_smul_mem_of_mem_span (R := R) (hM.2.1.symm ▸ hwW : w ∈ span F (M : Set V))
    exact ⟨d • w, hdw, smul_ne_zero hd hw0, by rw [Q_rsmul, hQw, mul_zero]⟩
  obtain ⟨x, hxL, hx0, hQx⟩ := hiso_lat L hL
  obtain ⟨x', hxK, hx0', hQx'⟩ := hiso_lat K hK
  obtain ⟨x₀, hx₀, y, hy, γ, hγ, haγ, hQx₀, hQy, hxy, hsL⟩ :=
    exists_hyperbolic_split_of_isMaxIn Q hWreg hL hxL hx0 hQx
  obtain ⟨x₀', hx₀', y', hy', γ', hγ', haγ', hQx₀', hQy', hxy', hsK⟩ :=
    exists_hyperbolic_split_of_isMaxIn Q hWreg hK hxK hx0' hQx'
  -- normalize `γ' = γ`
  have hiso' := isTorsionFree_of_fractionRing (R := R) (F := F) (V := F)
  obtain ⟨u, hu⟩ := (span_singleton_eq_span_singleton).mp (haγ.symm.trans haγ')
  have hγγ' : γ' = algebraMap R F u * γ := by
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    rw [Units.smul_def, Algebra.smul_def] at hu
    apply mul_left_cancel₀ h2
    linear_combination -hu
  set y'' := (↑u⁻¹ : R) • y' with hy''
  have hxy'' : bil Q x₀' y'' = γ := by
    rw [hy'', bil_rsmul_right, hxy', hγγ', ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  have hQy'' : Q y'' = 0 := by rw [hy'', Q_rsmul, hQy', mul_zero]
  have hJK : span R {x₀', y''} = span R {x₀', y'} := by
    have e : y' = (u : R) • y'' := by rw [hy'', smul_smul, Units.mul_inv, one_smul]
    apply le_antisymm <;> rw [span_le] <;> intro v hv <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv <;> rcases hv with h | h <;> rw [h]
    · exact subset_span (by simp)
    · exact smul_mem _ _ (subset_span (by simp))
    · exact subset_span (by simp)
    · rw [e]; exact smul_mem _ _ (subset_span (by simp))
  -- the Witt step
  obtain ⟨σ₁, hσ₁, hσx, hσy, hσfix, hσW⟩ := exists_orth_map_pair Q hV hWreg (hLW x₀ hx₀) (hLW y hy)
    (hKW _ hx₀') (hKW _ (K.smul_mem _ hy')) hQx₀ hQy hQx₀' hQy'' hγ hxy hxy''
  have hσWeq : W.map (σ₁ : V →ₗ[F] V) = W := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v, hv, rfl⟩; exact hσW v hv
    · exact LinearEquiv.finrank_map_eq σ₁ W
  set JK := span R {x₀', y'} with hJKdef
  have hL₁ := hL.latMap Q hσ₁ hσWeq
  have hsL₁ : IsOrthSum Q (OMeara.latMap σ₁ L) JK (OMeara.latMap σ₁ (splitComp Q L (span R {x₀, y}))) := by
    have := isOrthSum_latMap Q hσ₁ hsL
    rwa [latMap_span_pair, hσx, hσy, hJK] at this
  have hJKreg : IsRegular Q JK := isRegular_hyp Q hγ' hQx₀' hQy' hxy'
  have hL₁' := hL₁.complement Q hsL₁ hJKreg
  have hK' := hK.complement Q hsK hJKreg
  -- the smaller subspace `W' = W ∩ JK^⊥`
  set W' := perpIn Q W JK with hW'
  have hW'W : ∀ v ∈ W', v ∈ W := fun v hv => hv.1
  have hW'lt : finrank F W' < n := by
    rw [← hn]
    refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (fun v hv => hv.1) fun h => ?_)
    have hx₀'W' : x₀' ∈ W' := h ▸ hKW _ hx₀'
    have := hx₀'W'.2 y' (subset_span (by simp))
    rw [hxy'] at this; exact hγ' this
  have hdec : ∀ z ∈ W, ∃ c d : F, z - c • x₀' - d • y' ∈ W' :=
    fun z hz => exists_decomp_hyp Q hγ' (hKW _ hx₀') (hKW _ hy') hQx₀' hQy' hxy' hz
  have hW'reg : ∀ v ∈ W', (∀ v' ∈ W', bil Q v v' = 0) → v = 0 := by
    intro v hv h
    refine hWreg v hv.1 fun z hz => ?_
    obtain ⟨c, d, hcd⟩ := hdec z hz
    have hz' : z = c • x₀' + d • y' + (z - c • x₀' - d • y') := by abel
    rw [hz', bil_add_right, bil_add_right, bil_smul_right, bil_smul_right, hv.2 x₀' (subset_span (by simp)),
      hv.2 y' (subset_span (by simp)), h _ hcd]
    ring
  obtain ⟨τ, hτ, hτfix, hτW', hτL⟩ := ih _ hW'lt W' rfl hW'reg _ _ hL₁' hK'
  -- `τ` fixes `x₀'` and `y'`
  have hfixJ : ∀ j ∈ ({x₀', y'} : Set V), τ j = j := by
    intro j hj
    refine hτfix j fun v hv => ?_
    rw [bil_comm]; exact hv.2 j (subset_span hj)
  have hτJK : OMeara.latMap τ JK = JK := by
    rw [latMap_span_pair, hfixJ x₀' (by simp), hfixJ y' (by simp)]
  refine ⟨τ * σ₁, (orth Q).mul_mem hτ hσ₁, fun v hv => ?_, fun z hz => ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hσfix v hv]
    exact hτfix v fun w hw => hv w hw.1
  · rw [LinearEquiv.mul_apply]
    have hσz := hσW z hz
    obtain ⟨c, d, hcd⟩ := hdec _ hσz
    have : σ₁ z = c • x₀' + d • y' + (σ₁ z - c • x₀' - d • y') := by abel
    rw [this, map_add, map_add, map_smul, map_smul, hfixJ x₀' (by simp), hfixJ y' (by simp)]
    exact W.add_mem (W.add_mem (W.smul_mem _ (hKW _ hx₀')) (W.smul_mem _ (hKW _ hy'))) (hτW' _ hcd).1
  · rw [latMap_mul, ← hsL₁.sup_eq, OMeara.latMap, Submodule.map_sup, ← OMeara.latMap, ← OMeara.latMap, hτJK,
      hτL, hsK.sup_eq]

/-- **Theorem 91:2** (O'Meara 1963, p. 240): if $K$ and $L$ are $\mathfrak a$-maximal lattices on a regular quadratic
space $V$ over a local field, then $\operatorname{cls} K = \operatorname{cls} L$. (The local field enters through 91:1,
i.e. through the Henselian property of $R$.) -/
@[kb "omeara1963" "§91A, 91:2, p. 240"]
theorem cls_eq_of_isMaximal [HenselianLocalRing R] [FiniteDimensional F V]
    (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} {L K : Submodule R V}
    (hL : IsMaximal Q a L) (hK : IsMaximal Q a K) : cls Q K = cls Q L := by
  have hreg : ∀ w ∈ (⊤ : Submodule F V), (∀ w' ∈ (⊤ : Submodule F V), bil Q w w' = 0) → w = 0 :=
    fun w _ h => hV.1 w fun w' => h w' trivial
  obtain ⟨σ, hσ, -, -, hσL⟩ := exists_orth_of_isMaxIn Q hV _ ⊤ rfl hreg L K
    ((isMaxIn_top_iff Q).mpr hL) ((isMaxIn_top_iff Q).mpr hK)
  exact cls_eq_of_mem Q ⟨σ, hσ, hσL.symm⟩

end DVR

end QuadFormsKB.OMeara
