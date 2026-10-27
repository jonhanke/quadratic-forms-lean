/-
# O'Meara §92: classes of lattices and the spaces of the Jordan chains (Corollary 92:2b)

**Setting** (as in `Sec92Space.lean`): $R$ a complete discrete valuation ring with finite residue field, $2$ a unit of
$R$ (non-dyadic), fraction field $F$, a finite-dimensional quadratic space $(V, Q)$ over $F$, lattices =
`Submodule R V`; spaces $FL$ = `span F L`, isometries of spaces = `IsometricLat` over $F$.

**Proves**
* `isometric_cancel_span`: Witt cancellation for orthogonal sums of regular subspaces (O'Meara 1963, 42:16, p. 97):
  $A \perp B \cong C \perp D$ and $A \cong C$ give $B \cong D$;
* `cls_eq_iff_isometric_chain` (**Corollary 92:2b**, p. 248): for lattices of the same Jordan type on $V$ with Jordan
  chains $L_{(1)} \subseteq \cdots \subseteq L_{(t)}$ and $K_{(1)} \subseteq \cdots \subseteq K_{(t)}$,
  $\operatorname{cls} L = \operatorname{cls} K$ if and only if $FL_{(i)} \cong FK_{(i)}$ for every $i$.
-/
import QuadFormsKB.Literature.OMeara.Sec92Space
import QuadFormsKB.Literature.OMeara.Sec91Chain
import QuadFormsKB.Witt.Extension

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Field

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [FiniteDimensional F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- **Witt cancellation for orthogonal sums of subspaces** (O'Meara 1963, 42:16, p. 97): let $A, B \subseteq V$ and
$C, D \subseteq V'$ be subspaces with $B(A, B) = 0$, $B(C, D) = 0$, all four regular. If $A + B \cong C + D$ and
$A \cong C$, then $B \cong D$. -/
@[kb "omeara1963" "§42F, 42:16, p. 97 (Witt cancellation, for orthogonal sums of subspaces)"]
theorem isometric_cancel_span {A B : Submodule F V} {C D : Submodule F V'}
    (hAB : ∀ x ∈ A, ∀ y ∈ B, bil Q x y = 0) (hCD : ∀ x ∈ C, ∀ y ∈ D, bil Q' x y = 0)
    (_hA : IsRegular Q A) (_hB : IsRegular Q B) (hC : IsRegular Q' C) (hD : IsRegular Q' D)
    (h : IsometricLat (R := F) Q Q' (A ⊔ B) (C ⊔ D)) (hAC : IsometricLat (R := F) Q Q' A C) :
    IsometricLat (R := F) Q Q' B D := by
  classical
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := hAC
  -- orthogonal complement of `C` in `C ⊔ D` is `D`
  have hperpD : ∀ x ∈ C ⊔ D, (∀ c ∈ C, bil Q' x c = 0) → x ∈ D := by
    intro x hx hxc
    obtain ⟨c0, hc0, d0, hd0, rfl⟩ := mem_sup.mp hx
    have h0 : c0 = 0 := by
      refine hC c0 hc0 fun c hc => ?_
      have := hxc c hc
      rw [bil_add_left, bil_comm Q' d0 c, hCD c hc d0 hd0, add_zero] at this
      exact this
    rw [h0, zero_add]; exact hd0
  have hdisj : ∀ x ∈ C, x ∈ D → x = 0 := fun x hxC hxD =>
    hC x hxC fun y hy => by rw [bil_comm]; exact hCD y hy x hxD
  let S : Submodule F V' := C ⊔ D
  let QX : QuadraticForm F S := Q'.comp S.subtype
  have hQX : ∀ x : S, QX x = Q' (x : V') := fun x => rfl
  have hbX : ∀ x y : S, bil QX x y = bil Q' (x : V') (y : V') := by
    intro x y
    rw [bil_eq_half, bil_eq_half]; rfl
  have hnd : (QuadraticMap.associated QX).Nondegenerate := by
    have hl : ∀ x : S, (∀ y : S, bil QX x y = 0) → x = 0 := by
      intro x hx
      apply Subtype.ext
      obtain ⟨c0, hc0, d0, hd0, hxe⟩ := mem_sup.mp x.2
      have hc : c0 = 0 := by
        refine hC c0 hc0 fun c hc => ?_
        have := hx ⟨c, mem_sup_left hc⟩
        rw [hbX, ← hxe, bil_add_left, bil_comm Q' d0 c, hCD c hc d0 hd0, add_zero] at this
        exact this
      have hd : d0 = 0 := by
        refine hD d0 hd0 fun d hd => ?_
        have := hx ⟨d, mem_sup_right hd⟩
        rw [hbX, ← hxe, bil_add_left, hCD c0 hc0 d hd, zero_add] at this
        exact this
      rw [← hxe, hc, hd, add_zero]; rfl
    refine ⟨hl, fun x hx => hl x fun y => ?_⟩
    rw [bil_comm]; exact hx y
  -- Witt's extension theorem
  let W : Submodule F S := C.comap S.subtype
  let σ : W →ₗ[F] S := f.toLinearMap ∘ₗ Submodule.inclusion le_sup_left ∘ₗ g.symm.toLinearMap ∘ₗ
    S.subtype.restrict (p := W) (q := C) (fun x hx => hx)
  have hσ : ∀ w : W, σ w = f (Submodule.inclusion le_sup_left (g.symm ⟨(w : V'), w.2⟩)) := fun w => rfl
  have hσQ : ∀ w : W, QX (σ w) = QX (w : S) := by
    intro w
    rw [hσ, hQX, hf, Submodule.coe_inclusion, ← hg, hQX]
    simp
  have hσi : Function.Injective σ := by
    intro w w' hww
    rw [hσ, hσ] at hww
    have := g.symm.injective (Submodule.inclusion_injective le_sup_left (f.injective hww))
    have h3 := congrArg Subtype.val this
    exact Subtype.ext (Subtype.ext h3)
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_extend_of_associated QX hnd σ hσi hσQ
  let T : S ≃ₗ[F] S := ρ.toLinearEquiv
  have hTQ : ∀ z : S, QX (T z) = QX z := fun z => ρ.map_app z
  have hTb : ∀ x y : S, bil Q' ((T x : S) : V') ((T y : S) : V') = bil Q' (x : V') (y : V') := by
    intro x y
    rw [← hbX, ← hbX, bil_eq_half, bil_eq_half]
    have : QX (T x + T y) = QX (x + y) := by rw [← map_add]; exact hTQ _
    rw [this, hTQ, hTQ]
  have hTa : ∀ a : A, T ⟨(g a : V'), mem_sup_left (g a).2⟩ =
      f ⟨(a : V), mem_sup_left a.2⟩ := by
    intro a
    have h1 := hρ ⟨⟨(g a : V'), mem_sup_left (g a).2⟩, (g a).2⟩
    rw [hσ] at h1
    have e : g.symm ⟨(g a : V'), (g a).2⟩ = a := g.symm_apply_apply a
    calc T ⟨(g a : V'), mem_sup_left (g a).2⟩ = f (Submodule.inclusion le_sup_left
        (g.symm ⟨(g a : V'), (g a).2⟩)) := h1
      _ = f ⟨(a : V), mem_sup_left a.2⟩ := by rw [e]; rfl
  let Ψ : ↥(A ⊔ B) ≃ₗ[F] S := f.trans T.symm
  have hΨ : ∀ x, T (Ψ x) = f x := fun x => by simp [Ψ]
  have hΨQ : ∀ x, Q' ((Ψ x : S) : V') = Q (x : V) := by
    intro x
    have h1 := hTQ (Ψ x)
    rw [hΨ] at h1
    calc Q' ((Ψ x : S) : V') = QX (Ψ x) := rfl
      _ = QX (f x) := h1.symm
      _ = Q' (f x) := rfl
      _ = Q (x : V) := hf x
  have hΨa : ∀ a : A, Ψ ⟨(a : V), mem_sup_left a.2⟩ = ⟨(g a : V'), mem_sup_left (g a).2⟩ := by
    intro a
    apply T.injective
    rw [hΨ, hTa]
  have hΨB : ∀ b : B, ((Ψ ⟨(b : V), mem_sup_right b.2⟩ : S) : V') ∈ D := by
    intro b
    refine hperpD _ (Ψ _).2 fun c hc => ?_
    have h1 := hTb (Ψ ⟨(b : V), mem_sup_right b.2⟩) ⟨c, mem_sup_left hc⟩
    rw [hΨ] at h1
    have h2 := hTa (g.symm ⟨c, hc⟩)
    rw [LinearEquiv.apply_symm_apply] at h2
    rw [← h1, h2]
    rw [bil_eq_of_isometricLat (R := F) Q Q' f hf]
    rw [bil_comm]
    exact hAB _ (g.symm ⟨c, hc⟩).2 _ b.2
  -- the isometry `B ≃ D`
  let φ0 : B →ₗ[F] D := LinearMap.codRestrict D
    (S.subtype ∘ₗ Ψ.toLinearMap ∘ₗ Submodule.inclusion (le_sup_right : B ≤ A ⊔ B)) hΨB
  have hφ : ∀ b : B, (φ0 b : V') = ((Ψ ⟨(b : V), mem_sup_right b.2⟩ : S) : V') := fun b => rfl
  have hφi : Function.Injective φ0 := by
    intro b b' hbb
    have h1 : Ψ ⟨(b : V), mem_sup_right b.2⟩ = Ψ ⟨(b' : V), mem_sup_right b'.2⟩ :=
      Subtype.ext (by rw [← hφ, ← hφ, hbb])
    exact Subtype.ext (congrArg Subtype.val (Ψ.injective h1) :)
  have hφs : Function.Surjective φ0 := by
    intro d
    obtain ⟨x, hx⟩ := Ψ.surjective ⟨(d : V'), mem_sup_right d.2⟩
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup.mp x.2
    have hx' : x = ⟨a, mem_sup_left ha⟩ + ⟨b, mem_sup_right hb⟩ := Subtype.ext hab.symm
    have h1 := hΨa ⟨a, ha⟩
    refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
    have h2 : (d : V') = (g ⟨a, ha⟩ : V') + (Ψ ⟨b, mem_sup_right hb⟩ : V') := by
      have := congrArg (fun z : S => (z : V')) hx
      simp only at this
      rw [← this, hx', map_add, h1]; rfl
    have h3 : (g ⟨a, ha⟩ : V') = 0 := by
      refine hdisj _ (g ⟨a, ha⟩).2 ?_
      have : (g ⟨a, ha⟩ : V') = (d : V') - (Ψ ⟨b, mem_sup_right hb⟩ : V') := by rw [h2]; abel
      rw [this]
      exact D.sub_mem d.2 (hΨB ⟨b, hb⟩)
    show (Ψ ⟨b, mem_sup_right hb⟩ : V') = d
    rw [h2, h3, zero_add]
  refine ⟨LinearEquiv.ofBijective φ0 (show Function.Bijective φ0 from ⟨hφi, hφs⟩), fun b => ?_⟩
  show Q' (φ0 b : V') = Q (b : V)
  rw [hφ]
  exact hΨQ ⟨(b : V), mem_sup_right b.2⟩

/-- The orthogonal sum $J \perp K$ is the image of $J \times K$ under $(j, k) \mapsto j + k$. -/
theorem exists_equiv_of_isOrthSum {M J K : Submodule F V} (h : IsOrthSum (R := F) Q M J K) :
    ∃ e : (J × K) ≃ₗ[F] M, ∀ p, (e p : V) = (p.1 : V) + (p.2 : V) := by
  let Φ : (J × K) →ₗ[F] V := J.subtype.coprod K.subtype
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨j, k⟩ hjk
    have hjk' : (j : V) + (k : V) = 0 := hjk
    have hk : (k : V) ∈ J := by
      have : (k : V) = -(j : V) := eq_neg_of_add_eq_zero_right hjk'
      rw [this]; exact J.neg_mem j.2
    have hk0 : (k : V) = 0 := by
      have := h.disjoint.le_bot ⟨hk, k.2⟩
      simpa using this
    have hj0 : (j : V) = 0 := by rw [hk0, add_zero] at hjk'; exact hjk'
    exact Prod.ext (Subtype.ext hj0) (Subtype.ext hk0)
  have hrange : LinearMap.range Φ = M := by
    rw [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype, h.sup_eq]
  refine ⟨(LinearEquiv.ofInjective Φ hinj).trans (LinearEquiv.ofEq _ _ hrange), fun p => rfl⟩

/-- $Q(x + y) = Q(x) + Q(y)$ for orthogonal $x, y$. -/
theorem Q_add_of_orth {x y : V} (hxy : bil Q x y = 0) : Q (x + y) = Q x + Q y := by
  rw [Q_add, hxy]; ring

/-- **Gluing isometries of two-component orthogonal sums of subspaces**: if $M = J \perp K$, $M' = J' \perp K'$,
$J \cong J'$ and $K \cong K'$, then $M \cong M'$. -/
theorem isometricLat_of_isOrthSum {M J K : Submodule F V} {M' J' K' : Submodule F V'}
    (h : IsOrthSum (R := F) Q M J K) (h' : IsOrthSum (R := F) Q' M' J' K')
    (hJ : IsometricLat (R := F) Q Q' J J') (hK : IsometricLat (R := F) Q Q' K K') :
    IsometricLat (R := F) Q Q' M M' := by
  obtain ⟨e, he⟩ := exists_equiv_of_isOrthSum Q h
  obtain ⟨e', he'⟩ := exists_equiv_of_isOrthSum Q' h'
  obtain ⟨fJ, hfJ⟩ := hJ
  obtain ⟨fK, hfK⟩ := hK
  refine ⟨e.symm.trans ((fJ.prodCongr fK).trans e'), fun x => ?_⟩
  obtain ⟨p, rfl⟩ := e.surjective x
  have h1 : e.symm (e p) = p := e.symm_apply_apply p
  show Q' (e' ((fJ.prodCongr fK) (e.symm (e p))) : V') = Q (e p : V)
  rw [h1]
  show Q' (e' (fJ p.1, fK p.2) : V') = Q (e p : V)
  rw [he', he, Q_add_of_orth Q' (h'.orth _ (fJ p.1).2 _ (fK p.2).2),
    Q_add_of_orth Q (h.orth _ p.1.2 _ p.2.2), hfJ, hfK]

/-- Isometry of subspaces is invariant under equalities of the subspaces. -/
theorem isometricLat_congr {M₁ M₂ : Submodule F V} {N₁ N₂ : Submodule F V'} (h1 : M₁ = M₂) (h2 : N₁ = N₂)
    (h : IsometricLat (R := F) Q Q' M₁ N₁) : IsometricLat (R := F) Q Q' M₂ N₂ := by
  subst h1 h2; exact h

end Field

section ChainHelpers

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- An orthogonal sum of two regular lattices is regular. -/
theorem isRegular_of_isOrthSum {M J K : Submodule R V} (h : IsOrthSum Q M J K) (hJ : IsRegular Q J)
    (hK : IsRegular Q K) : IsRegular Q M := by
  intro x hx hxM
  rw [← h.sup_eq] at hx
  obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hx
  have hJM : J ≤ M := h.sup_eq ▸ le_sup_left
  have hKM : K ≤ M := h.sup_eq ▸ le_sup_right
  have hj0 : j = 0 := by
    refine hJ j hj fun y hy => ?_
    have := hxM y (hJM hy)
    rw [bil_add_left, bil_comm Q k y, h.orth y hy k hk, add_zero] at this
    exact this
  have hk0 : k = 0 := by
    refine hK k hk fun y hy => ?_
    have := hxM y (hKM hy)
    rw [bil_add_left, h.orth j hj y hy, zero_add] at this
    exact this
  rw [hj0, hk0, add_zero]

/-- The $F$-span of a regular lattice is a regular subspace. -/
theorem isRegular_span {M : Submodule R V} (hM : IsRegular Q M) :
    IsRegular (R := F) Q (span F (M : Set V)) := by
  have key : ∀ x ∈ span F (M : Set V), ∃ r : R, r ≠ 0 ∧ r • x ∈ M := by
    intro x hx
    refine span_induction (p := fun x _ => ∃ r : R, r ≠ 0 ∧ r • x ∈ M) ?_ ?_ ?_ ?_ hx
    · intro x hx; exact ⟨1, one_ne_zero, by simpa using hx⟩
    · exact ⟨1, one_ne_zero, by simp⟩
    · rintro x y - - ⟨r, hr, hrx⟩ ⟨s, hs, hsy⟩
      refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
      have h1 : (r * s) • x = s • (r • x) := by rw [mul_comm, mul_smul]
      have h2 : (r * s) • y = r • (s • y) := mul_smul _ _ _
      rw [smul_add, h1, h2]
      exact M.add_mem (M.smul_mem s hrx) (M.smul_mem r hsy)
    · rintro c x - ⟨r, hr, hrx⟩
      obtain ⟨⟨a, s⟩, hcs⟩ := IsLocalization.surj (nonZeroDivisors R) c
      refine ⟨r * s, mul_ne_zero hr (nonZeroDivisors.coe_ne_zero s), ?_⟩
      have : (r * (s : R)) • (c • x) = a • (r • x) := by
        rw [← algebraMap_smul F (r * (s : R)), ← algebraMap_smul F a, ← algebraMap_smul F r, smul_smul,
          smul_smul, map_mul]
        congr 1
        simp only at hcs
        linear_combination (algebraMap R F r) * hcs
      rw [this]
      exact M.smul_mem a hrx
  intro x hx hxy
  obtain ⟨r, hr, hrx⟩ := key x hx
  have h0 : r • x = 0 := hM _ hrx fun y hy => by
    rw [bil_rsmul_left, hxy y (subset_span hy), mul_zero]
  rw [← algebraMap_smul F r x] at h0
  exact (smul_eq_zero.mp h0).resolve_left ((map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hr)

/-- The $F$-spans of an orthogonal sum $M = J \perp K$ with $K$ regular form an orthogonal sum of subspaces. -/
theorem isOrthSum_span {M J K : Submodule R V} (h : IsOrthSum Q M J K) (hK : IsRegular Q K) :
    IsOrthSum (R := F) Q (span F (M : Set V)) (span F (J : Set V)) (span F (K : Set V)) := by
  have horth : ∀ x ∈ span F (J : Set V), ∀ y ∈ span F (K : Set V), bil Q x y = 0 := by
    intro x hx y hy
    refine span_induction (p := fun x _ => bil Q x y = 0) ?_ (by simp [bil]) ?_ ?_ hx
    · intro x hx
      refine span_induction (p := fun y _ => bil Q x y = 0) ?_ (by simp [bil]) ?_ ?_ hy
      · intro y hy; exact h.orth x hx y hy
      · intro a b _ _ ha hb; rw [bil_add_right, ha, hb, add_zero]
      · intro c a _ ha; rw [bil_smul_right, ha, mul_zero]
    · intro a b _ _ ha hb; rw [bil_add_left, ha, hb, add_zero]
    · intro c a _ ha; rw [bil_smul_left, ha, mul_zero]
  refine ⟨horth, ?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    exact (mem_bot F).mpr (isRegular_span Q hK x hx2 fun y hy => horth x hx1 y hy)
  · apply le_antisymm
    · have hJM : J ≤ M := h.sup_eq ▸ le_sup_left
      have hKM : K ≤ M := h.sup_eq ▸ le_sup_right
      exact sup_le (span_mono hJM) (span_mono hKM)
    · refine span_le.mpr fun x hx => ?_
      rw [← h.sup_eq] at hx
      obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hx
      exact add_mem (mem_sup_left (subset_span hj)) (mem_sup_right (subset_span hk))

/-- Each Jordan chain $L_{(i)}$ of a Jordan splitting is regular. -/
theorem isRegular_jordanChain {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i : Fin t) : IsRegular Q (jordanChain Ls i) := by
  have hle : ∀ k, Ls k ≤ L := fun k => hL.split.iSup_eq ▸ le_iSup Ls k
  have hreg : ∀ j, IsRegular Q (Ls j) := fun j => (hL.modular j).isRegular Q (FG.of_le hfg (hle j))
  obtain ⟨n, hn⟩ : ∃ n, i.val = n := ⟨_, rfl⟩
  induction n generalizing i with
  | zero => rw [jordanChain_zero Ls i hn]; exact hreg i
  | succ n ih =>
    let i' : Fin t := ⟨n, by omega⟩
    exact isRegular_of_isOrthSum Q (isOrthSum_jordanChain_succ Q hfg hL i' i (by simp [i', hn]))
      (ih i' rfl) (hreg i)

/-- $FL_{(i+1)} = FL_{(i)} \perp FL_{i+1}$ as an orthogonal sum of subspaces. -/
theorem isOrthSum_span_jordanChain_succ {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i j : Fin t) (hij : i.val + 1 = j.val) :
    IsOrthSum (R := F) Q (span F (jordanChain Ls j : Set V)) (span F (jordanChain Ls i : Set V))
      (span F (Ls j : Set V)) := by
  have hle : ∀ k, Ls k ≤ L := fun k => hL.split.iSup_eq ▸ le_iSup Ls k
  exact isOrthSum_span Q (isOrthSum_jordanChain_succ Q hfg hL i j hij)
    ((hL.modular j).isRegular Q (FG.of_le hfg (hle j)))

variable [FiniteDimensional F V]

/-- The component-wise and chain-wise isometry conditions are equivalent (the substance of 92:2b). -/
theorem isometric_span_iff_chain {L K : Submodule R V} (hLfg : L.FG) (hKfg : K.FG) {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q K Ks) :
    (∀ i : Fin t, IsometricLat (R := F) Q Q (span F (Ls i : Set V)) (span F (Ks i : Set V))) ↔
      ∀ i : Fin t, IsometricLat (R := F) Q Q (span F (jordanChain Ls i : Set V))
        (span F (jordanChain Ks i : Set V)) := by
  have hLle : ∀ k, Ls k ≤ L := fun k => hL.split.iSup_eq ▸ le_iSup Ls k
  have hKle : ∀ k, Ks k ≤ K := fun k => hK.split.iSup_eq ▸ le_iSup Ks k
  constructor
  · intro h i
    obtain ⟨n, hn⟩ : ∃ n, i.val = n := ⟨_, rfl⟩
    induction n generalizing i with
    | zero => rw [jordanChain_zero Ls i hn, jordanChain_zero Ks i hn]; exact h i
    | succ n ih =>
      let i' : Fin t := ⟨n, by omega⟩
      have hi : i'.val + 1 = i.val := by simp [i', hn]
      exact isometricLat_of_isOrthSum Q Q (isOrthSum_span_jordanChain_succ Q hLfg hL i' i hi)
        (isOrthSum_span_jordanChain_succ Q hKfg hK i' i hi) (ih i' rfl) (h i)
  · intro h i
    by_cases h0 : i.val = 0
    · have := h i
      rwa [jordanChain_zero Ls i h0, jordanChain_zero Ks i h0] at this
    · let i' : Fin t := ⟨i.val - 1, by omega⟩
      have hi : i'.val + 1 = i.val := by simp [i']; omega
      have hA := isOrthSum_span_jordanChain_succ Q hLfg hL i' i hi
      have hB := isOrthSum_span_jordanChain_succ Q hKfg hK i' i hi
      exact isometric_cancel_span Q Q hA.orth hB.orth
        (isRegular_span Q (isRegular_jordanChain Q hLfg hL i'))
        (isRegular_span Q ((hL.modular i).isRegular Q (FG.of_le hLfg (hLle i))))
        (isRegular_span Q (isRegular_jordanChain Q hKfg hK i'))
        (isRegular_span Q ((hK.modular i).isRegular Q (FG.of_le hKfg (hKle i))))
        (isometricLat_congr Q Q hA.sup_eq.symm hB.sup_eq.symm (h i)) (h i')

end ChainHelpers

section LocalNonDyadic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (ResidueField R)] [DecidableEq (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **Corollary 92:2b** (O'Meara 1963, p. 248): let $L$ and $K$ be lattices of the same Jordan type on a quadratic space
$V$ over a non-dyadic local field, with Jordan splittings $L = L_1 \perp \cdots \perp L_t$, $K = K_1 \perp \cdots \perp
K_t$ and Jordan chains $L_{(i)} = L_1 \perp \cdots \perp L_i$, $K_{(i)} = K_1 \perp \cdots \perp K_i$. Then
$\operatorname{cls} L = \operatorname{cls} K$ if and only if $FL_{(i)} \cong FK_{(i)}$ for $1 \le i \le t$. -/
@[kb "omeara1963" "§92, 92:2b, p. 248"]
theorem cls_eq_iff_isometric_chain (h2 : IsUnit (2 : R)) {L K : Submodule R V} [L.IsLattice F] [K.IsLattice F]
    {t t' : ℕ} {Ls : Fin t → Submodule R V} {Ks : Fin t' → Submodule R V} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q K Ks) (htype : SameJordanType Q Q Ls Ks) :
    cls Q L = cls Q K ↔ ∀ (i : Fin t) (j : Fin t'), (i : ℕ) = j →
      IsometricLat (R := F) Q Q (span F (jordanChain Ls i : Set V)) (span F (jordanChain Ks j : Set V)) := by
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  rw [cls_eq_iff_isometric_span Q h2 hL hK htype]
  obtain ⟨rfl, -⟩ := htype
  have hii : ∀ {P : Fin t → Fin t → Prop}, (∀ i j : Fin t, (i : ℕ) = j → P i j) ↔ ∀ i, P i i := by
    intro P
    exact ⟨fun h i => h i i rfl, fun h i j hij => by rw [Fin.ext hij]; exact h j⟩
  rw [hii, hii]
  exact isometric_span_iff_chain Q hLfg hKfg hL hK

end LocalNonDyadic

end QuadFormsKB.OMeara
