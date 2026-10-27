/-
# O'Meara §91A: the values of a maximal lattice (Example 91:3)

**Setting** (as in `Sec91Max.lean`): $R$ a Henselian discrete valuation ring with fraction field $F$,
$2 \in F^\times$, a finite-dimensional regular quadratic space $(V, Q)$ over $F$, lattices = `Submodule R V`.

**Proves**
* `exists_isMaximal_ge` (O'Meara 1963, 82:18, p. 234): a lattice $K$ on $V$ with $\mathfrak nK \subseteq \mathfrak a$ is
  contained in an $\mathfrak a$-maximal lattice, provided some $\mathfrak a$-maximal lattice exists (so that
  $\mathfrak a$ is a fractional ideal);
* `exists_lattice_of_Q_mem` (82:9, p. 229, for a line): a vector $x$ with $Q(x) \in \mathfrak a \setminus 0$ lies in a
  lattice on $V$ of norm $\subseteq \mathfrak a$;
* `Q_image_eq_of_isMaximal` (**91:3**, p. 240): $Q(L) = Q(V) \cap \mathfrak a$ for an $\mathfrak a$-maximal lattice $L$.
  (O'Meara's further consequences for $\dim V \ge 3$ use 63:18 and are not formalized here.)
-/
import QuadFormsKB.Literature.OMeara.Sec91Max

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- If an $\mathfrak a$-maximal lattice exists on a non-zero space, $\mathfrak a \ne F$. (Otherwise $L$ could be
enlarged by $\pi^{-1}x$, so $L \subseteq \mathfrak p L$ and $L = 0$ by Nakayama.) -/
theorem ne_top_of_isMaximal [Nontrivial V] {a : Submodule R F} {L : Submodule R V}
    (hL : IsMaximal Q a L) : a ≠ ⊤ := by
  intro htop
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : algebraMap R F π ≠ 0 := by
    intro h; exact hπ.ne_zero (IsFractionRing.injective R F (by simpa using h))
  have := hL.1
  have hmem : ∀ x ∈ L, ((algebraMap R F π)⁻¹) • x ∈ L := by
    intro x hx
    have hK : (L ⊔ R ∙ (((algebraMap R F π)⁻¹) • x)).IsLattice F :=
      Submodule.IsLattice.of_le_of_isLattice_of_fg F le_sup_left
        (hL.1.fg.sup (fg_span_singleton _))
    have := hL.2.2 _ hK le_sup_left (by rw [htop]; exact le_top)
    rw [← this]
    exact mem_sup_right (mem_span_singleton_self _)
  have hle : L ≤ maximalIdeal R • L := by
    intro x hx
    have : x = π • (((algebraMap R F π)⁻¹) • x) := by
      rw [← algebraMap_smul F π, smul_smul, mul_inv_cancel₀ hπ0, one_smul]
    rw [this]
    refine Submodule.smul_mem_smul ?_ (hmem x hx)
    rw [mem_maximalIdeal, mem_nonunits_iff]
    exact hπ.not_isUnit
  have hL0 : L = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) L hL.1.fg hle
      (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge
  have htop' : (⊤ : Submodule F V) = ⊥ := by
    rw [← hL.1.span_eq_top, hL0]; simp
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have : v ∈ (⊥ : Submodule F V) := htop' ▸ mem_top
  exact hv (by simpa using this)

/-- On a regular non-zero space an $\mathfrak a$-maximal lattice forces $\mathfrak a = \alpha R$, $\alpha \ne 0$. -/
theorem exists_eq_span_singleton_of_isMaximal (hV : (QuadraticMap.associated Q).Nondegenerate)
    [Nontrivial V] {a : Submodule R F} {L : Submodule R V} (hL : IsMaximal Q a L) :
    ∃ α : F, α ≠ 0 ∧ a = R ∙ α := by
  have hne : a ≠ ⊥ := by
    obtain ⟨x, hx, hQx⟩ := exists_mem_Q_ne_zero Q hV hL.1
    intro h0
    have : Q x ∈ a := hL.2.1 (Q_mem_normIdeal Q hx)
    rw [h0, Submodule.mem_bot] at this
    exact hQx this
  obtain ⟨z, hz⟩ : ∃ z, z ∉ a := by
    by_contra h
    push Not at h
    exact ne_top_of_isMaximal Q hL (eq_top_iff.mpr fun z _ => h z)
  have hle : a ≤ R ∙ z := by
    intro w hw
    obtain ⟨m, -, hm⟩ := exists_maximalIdeal_mul_of_mem_of_notMem hw hz
    exact mem_span_singleton.mpr ⟨m, by rw [Algebra.smul_def, hm]⟩
  exact exists_eq_span_singleton (FG.of_le (fg_span_singleton z) hle) hne

/-- The lattice-like submodule $\{v : 2B(v, K) \subseteq \mathfrak a\}$. -/
def dualLat (a : Submodule R F) (K : Submodule R V) : Submodule R V where
  carrier := {v | ∀ k ∈ K, 2 * bil Q v k ∈ a}
  add_mem' := by
    intro v w hv hw k hk
    have : 2 * bil Q (v + w) k = 2 * bil Q v k + 2 * bil Q w k := by rw [bil_add_left]; ring
    rw [this]; exact add_mem (hv k hk) (hw k hk)
  zero_mem' := by intro k _; simp [bil]
  smul_mem' := by
    intro c v hv k hk
    have : 2 * bil Q (c • v) k = c • (2 * bil Q v k) := by
      rw [bil_rsmul_left, Algebra.smul_def]; ring
    rw [this]; exact a.smul_mem c (hv k hk)

theorem mem_dualLat {a : Submodule R F} {K : Submodule R V} {v : V} :
    v ∈ dualLat Q a K ↔ ∀ k ∈ K, 2 * bil Q v k ∈ a := Iff.rfl

/-- On a regular space, $\{v : 2B(v, K) \subseteq \alpha R\}$ is finitely generated for a lattice $K$. -/
theorem fg_dualLat [FiniteDimensional F V] (hV : (QuadraticMap.associated Q).Nondegenerate)
    {K : Submodule R V} (hK : K.IsLattice F) (α : F) : (dualLat Q (R ∙ α) K).FG := by
  classical
  have := hK
  obtain ⟨b0⟩ := exists_basis (R := R) (F := F) hK.fg
  let b := b0.extendOfIsLattice F
  have hbi : ∀ i, b i = (b0 i : V) := fun i => by simp [b]
  let d := LinearMap.BilinForm.dualBasis (QuadraticMap.associated Q) hV b
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hfgs : (span R (Set.range fun i => ((α / 2) • d i))).FG := fg_span (Set.finite_range _)
  refine FG.of_le hfgs ?_
  intro v hv
  have hcoef : ∀ i, ∃ r : R, d.repr v i = algebraMap R F r * (α / 2) := by
    intro i
    obtain ⟨r, hr⟩ := mem_span_singleton.mp (hv (b0 i : V) (b0 i).2)
    refine ⟨r, ?_⟩
    have hd : d.repr v i = bil Q v (b0 i : V) := by
      rw [← hbi]
      exact LinearMap.BilinForm.dualBasis_repr_apply hV b v i
    rw [hd]
    apply mul_left_cancel₀ h2
    rw [← hr, Algebra.smul_def]
    field_simp
  choose r hr using hcoef
  have hmem : ∑ i, d.repr v i • d i ∈ span R (Set.range fun i => ((α / 2) • d i)) := by
    refine sum_mem fun i _ => ?_
    rw [hr i, mul_smul, algebraMap_smul]
    exact smul_mem _ _ (subset_span ⟨i, rfl⟩)
  rwa [d.sum_repr] at hmem

/-- **Proposition 82:18** (O'Meara 1963, p. 234): if $K$ is a lattice on the regular space $V$ with
$\mathfrak nK \subseteq \mathfrak a$, there is an $\mathfrak a$-maximal lattice $M \supseteq K$. Here $\mathfrak a$ is assumed
to be a fractional ideal, which follows from the existence of one $\mathfrak a$-maximal lattice $L$. -/
@[kb "omeara1963" "§82H, 82:18, p. 234"]
theorem exists_isMaximal_ge [FiniteDimensional F V] (hV : (QuadraticMap.associated Q).Nondegenerate)
    [Nontrivial V] {a : Submodule R F} {L : Submodule R V} (hL : IsMaximal Q a L) {K : Submodule R V}
    (hK : K.IsLattice F) (hnK : normIdeal Q K ≤ a) : ∃ M, K ≤ M ∧ IsMaximal Q a M := by
  classical
  obtain ⟨α, hα, rfl⟩ := exists_eq_span_singleton_of_isMaximal Q hV hL
  have := hK
  set K' := dualLat Q (R ∙ α) K with hK'
  have hKK' : K ≤ K' := by
    intro k hk k' hk'
    exact hnK (two_mul_mem_normIdeal Q (bil_mem_scale Q hk hk'))
  have hfg : K'.FG := fg_dualLat Q hV hK α
  have : Module.Finite R K' := Module.Finite.iff_fg.mpr hfg
  let S : Set (Submodule R K') :=
    {N | K ≤ N.map K'.subtype ∧ normIdeal Q (N.map K'.subtype) ≤ R ∙ α}
  have e : (K.comap K'.subtype).map K'.subtype = K := by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hKK'
  have hS : S.Nonempty := ⟨K.comap K'.subtype, by rw [e], by rw [e]; exact hnK⟩
  obtain ⟨N, hNS, hNmax⟩ :=
    (set_has_maximal_iff_noetherian (R := R) (M := K')).mpr inferInstance S hS
  have hfgM : (N.map K'.subtype).FG := (IsNoetherian.noetherian N).map _
  have hlat : (N.map K'.subtype).IsLattice F :=
    Submodule.IsLattice.of_le_of_isLattice_of_fg F hNS.1 hfgM
  refine ⟨N.map K'.subtype, hNS.1, hlat, hNS.2, ?_⟩
  intro N2 hN2 hMN2 hnN2
  have hKN2 : K ≤ N2 := hNS.1.trans hMN2
  have hN2K' : N2 ≤ K' := by
    intro m hm k hk
    exact hnN2 (two_mul_mem_normIdeal Q (bil_mem_scale Q hm (hKN2 hk)))
  have e2 : (N2.comap K'.subtype).map K'.subtype = N2 := by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hN2K'
  have hle : N ≤ N2.comap K'.subtype := Submodule.map_le_iff_le_comap.mp hMN2
  have hmem : N2.comap K'.subtype ∈ S := ⟨by rw [e2]; exact hKN2, by rw [e2]; exact hnN2⟩
  have heq : N = N2.comap K'.subtype := by
    by_contra hne
    exact hNmax _ hmem (lt_of_le_of_ne hle hne)
  rw [heq, e2]

/-- **82:9 for a line** (O'Meara 1963, p. 229): if $Q(x) \in \mathfrak a$, $Q(x) \ne 0$, and $\mathfrak a$ is a fractional
ideal (there is an $\mathfrak a$-maximal lattice $L$), then $x$ lies in a lattice on $V$ with norm $\subseteq \mathfrak a$
(take $\mathfrak ox \perp cJ$ for a lattice $J$ on $x^\perp$ and a small scalar $c$). -/
@[kb "omeara1963" "§82E, 82:9, p. 229"]
theorem exists_lattice_of_Q_mem [FiniteDimensional F V] (hV : (QuadraticMap.associated Q).Nondegenerate)
    {a : Submodule R F} {L : Submodule R V} (hL : IsMaximal Q a L) {x : V} (hx : Q x ∈ a) (hx0 : Q x ≠ 0) :
    ∃ K : Submodule R V, K.IsLattice F ∧ x ∈ K ∧ normIdeal Q K ≤ a := by
  classical
  have : Nontrivial V := ⟨⟨x, 0, fun h => hx0 (by simp [h])⟩⟩
  obtain ⟨α, hα, rfl⟩ := exists_eq_span_singleton_of_isMaximal Q hV hL
  let U : Submodule F V := LinearMap.ker (QuadraticMap.associated Q x)
  have hU : ∀ v, v ∈ U ↔ bil Q x v = 0 := fun v => LinearMap.mem_ker
  let b := Module.finBasis F U
  let e : Fin (finrank F U) → V := fun i => (b i : V)
  have heU : ∀ i, bil Q x (e i) = 0 := fun i => (hU _).mp (b i).2
  let J0 : Submodule R V := span R (Set.range e)
  have hJ0 : J0.FG := fg_span (Set.finite_range _)
  obtain ⟨β, -, hβ⟩ := exists_mem_span_eq_singleton (R := R) (S := (scale Q J0 : Set F))
    (by rw [span_eq]; exact scale_fg Q hJ0)
  rw [span_eq] at hβ
  -- a scalar `c` with `c^2 β ∈ αR`
  obtain ⟨c, hc0, hcβ⟩ : ∃ c : F, c ≠ 0 ∧ c ^ 2 * β ∈ R ∙ α := by
    by_cases hβ0 : β = 0
    · exact ⟨1, one_ne_zero, by simp [hβ0]⟩
    rcases ValuationRing.isInteger_or_isInteger R (β / α) with ⟨r, hr⟩ | ⟨r, hr⟩
    · refine ⟨1, one_ne_zero, mem_span_singleton.mpr ⟨r, ?_⟩⟩
      rw [Algebra.smul_def, hr]; field_simp
    · refine ⟨algebraMap R F r, ?_, mem_span_singleton.mpr ⟨r, ?_⟩⟩
      · rw [hr]; exact inv_ne_zero (div_ne_zero hβ0 hα)
      · rw [Algebra.smul_def, hr]; field_simp
  let J' : Submodule R V := span R (Set.range fun i => c • e i)
  have hJ'fg : J'.FG := fg_span (Set.finite_range _)
  let K : Submodule R V := (R ∙ x) ⊔ J'
  have hx2 : (2 : F) ≠ 0 := two_ne_zero
  have hspan : span F (K : Set V) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hx' : x ∈ span F (K : Set V) :=
      subset_span (mem_sup_left (mem_span_singleton_self x))
    have he : ∀ i, e i ∈ span F (K : Set V) := by
      intro i
      have h1 : c • e i ∈ span F (K : Set V) :=
        subset_span (mem_sup_right (subset_span ⟨i, rfl⟩))
      have := (span F (K : Set V)).smul_mem c⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
    have hw : v - (bil Q v x / Q x) • x ∈ U := by
      rw [hU, bil_sub_right, bil_smul_right, bil_self, bil_comm Q x v]
      field_simp
      ring
    have h2 := congrArg Subtype.val (b.sum_repr ⟨_, hw⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    have hv : v = (bil Q v x / Q x) • x + ∑ i, (b.repr ⟨_, hw⟩ i) • e i := by
      have h3 : ∑ i, (b.repr ⟨_, hw⟩ i) • e i = v - (bil Q v x / Q x) • x := h2
      rw [h3]; abel
    rw [hv]
    exact add_mem (smul_mem _ _ hx') (sum_mem fun i _ => smul_mem _ _ (he i))
  have hzx : ∀ z ∈ J', bil Q x z = 0 := by
    intro z hz
    refine span_induction (p := fun z _ => bil Q x z = 0) ?_ (by simp [bil]) ?_ ?_ hz
    · rintro _ ⟨i, rfl⟩
      rw [bil_smul_right, heU, mul_zero]
    · intro u w _ _ hu hw; rw [bil_add_right, hu, hw, add_zero]
    · intro r u _ hu; rw [bil_rsmul_right, hu, mul_zero]
  have horth : ∀ y ∈ R ∙ x, ∀ z ∈ J', bil Q y z = 0 := by
    intro y hy z hz
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hy
    rw [bil_rsmul_left, hzx z hz, mul_zero]
  have hnx : normIdeal Q (R ∙ x) ≤ R ∙ α := by
    rw [normIdeal, span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hy
    rw [Q_rsmul]
    have : algebraMap R F r ^ 2 * Q x = (r ^ 2) • Q x := by rw [Algebra.smul_def, map_pow]
    rw [this]
    exact (R ∙ α).smul_mem _ hx
  have hnJ : normIdeal Q J' ≤ R ∙ α := by
    refine (normIdeal_le_scale Q J').trans ?_
    rw [scale_span, span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    have hB : bil Q (e i) (e j) ∈ R ∙ β :=
      hβ ▸ bil_mem_scale Q (subset_span ⟨i, rfl⟩) (subset_span ⟨j, rfl⟩)
    obtain ⟨s, hs⟩ := mem_span_singleton.mp hB
    have : bil Q (c • e i) (c • e j) = s • (c ^ 2 * β) := by
      rw [bil_smul_left, bil_smul_right, ← hs]; simp only [Algebra.smul_def]; ring
    show bil Q (c • e i) (c • e j) ∈ R ∙ α
    rw [this]
    exact smul_mem _ _ hcβ
  refine ⟨K, ⟨?_, hspan⟩, mem_sup_left (mem_span_singleton_self x), ?_⟩
  · exact (fg_span_singleton x).sup hJ'fg
  · rw [normIdeal_sup_of_orth Q horth]
    exact sup_le hnx hnJ

/-- **Example 91:3** (O'Meara 1963, p. 240): if $L$ is an $\mathfrak a$-maximal lattice on a regular quadratic space $V$
over a local field, then $Q(L) = Q(V) \cap \mathfrak a$. -/
@[kb "omeara1963" "§91A, 91:3, p. 240"]
theorem Q_image_eq_of_isMaximal [HenselianLocalRing R] [FiniteDimensional F V]
    (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} {L : Submodule R V}
    (hL : IsMaximal Q a L) : Q '' (L : Set V) = Set.range Q ∩ (a : Set F) := by
  ext y
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, rfl⟩, hL.2.1 (Q_mem_normIdeal Q hl)⟩
  · rintro ⟨⟨x, rfl⟩, hxa⟩
    by_cases h0 : Q x = 0
    · exact ⟨0, L.zero_mem, by simp [h0]⟩
    · have : Nontrivial V := ⟨⟨x, 0, fun h => h0 (by simp [h])⟩⟩
      obtain ⟨K, hK, hxK, hnK⟩ := exists_lattice_of_Q_mem Q hV hL hxa h0
      obtain ⟨M, hKM, hM⟩ := exists_isMaximal_ge Q hV hL hK hnK
      have hcls := cls_eq_of_isMaximal Q hV hL hM
      have hML : M ∈ cls Q L := by rw [← hcls]; exact mem_cls_self Q M
      obtain ⟨σ, hσ, rfl⟩ := hML
      obtain ⟨l, hl, hlx⟩ := Submodule.mem_map.mp (hKM hxK)
      refine ⟨l, hl, ?_⟩
      have h1 : σ l = x := hlx
      rw [← h1]
      exact (hσ l).symm

end DVR

end QuadFormsKB.OMeara
