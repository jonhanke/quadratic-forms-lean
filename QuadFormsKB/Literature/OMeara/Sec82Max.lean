/-
# O'Meara §82H: maximal lattices over a Dedekind domain

**Setting.** $R$ is a Dedekind domain with fraction field $F$, $2 \in F^\times$, and $(V, Q)$ a finite-dimensional
quadratic space over $F$ with O'Meara's bilinear form $B$ = `bil Q`; $V$ is regular when stated
(`(QuadraticMap.associated Q).Nondegenerate`). Lattices, fractional ideals, $\mathfrak aL$ and $\mathfrak a^{-1}$
(`1 / a`) are as in `Sec81.lean`; $\mathfrak a$-maximal lattices on $V$ (`IsMaximal`) and on a subspace $W$
(`IsMaxIn`) are the definitions of `Sec82.lean` and `Sec91MaxA.lean`. The ideal $2\mathfrak a$ is `span R {2} * a`.
A *hyperbolic plane* is a regular isotropic quadratic space of dimension $2$.

Results of §82H already proved over a discrete valuation ring in `Sec91Max*.lean` are proved here for a Dedekind
domain in the namespace `QuadFormsKB.OMeara.Dedekind`.

**Proves** (O'Meara 1963, §82H, pp. 234–237):
* `IsMaximal.ideal_smul` ($\mathfrak bL$ is $\mathfrak b^2\mathfrak a$-maximal) and
  `Dedekind.IsMaxIn.complement` (components of maximal lattices are maximal) (§82H, p. 234);
* `Dedekind.exists_isMaximal_ge` (**82:18**), `exists_isMaximal` (**82:18a**);
* `two_pow_mul_volume_le_one` and `isMaximal_of_squarefree` (**82:19**);
* `Dedekind.exists_binary_split_of_isMaximal` (**82:20**);
* `isMaximal_iff_isModular_of_hyperbolic` (**82:21**), `exists_eq_of_isMaximal_hyperbolic` (**82:21a**);
* `isMaximal_iff_gram_of_principal` (**82:22**);
* `exists_hyperbolic_split_of_isMaximal` (**82:23**).
-/
import QuadFormsKB.Literature.OMeara.Sec82Dual
import QuadFormsKB.Literature.OMeara.Sec82Modular
import QuadFormsKB.Literature.OMeara.Sec91MaxA
import QuadFormsKB.Literature.OMeara.Sec91Max

open QuadraticMap Submodule Module
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- A finitely generated ideal times a lattice is finitely generated. -/
theorem fg_smul_max {b : Submodule R F} (hb : b.FG) {L : Submodule R V} (hL : L.FG) : (b • L).FG := by
  obtain ⟨r, y, hy, -, a, ha, rfl⟩ := exists_adapted (F := F) hL
  rw [smul_adapted]
  exact fg_adapted _ (fun i => hb.mul (ha i).1) y

/-- A non-zero fractional ideal times a lattice on `V` is a lattice on `V`. -/
theorem isLattice_smul_max {b : Submodule R F} (hb : b.FG) (hb0 : b ≠ ⊥) {L : Submodule R V}
    (hL : L.IsLattice F) : (b • L).IsLattice F := by
  refine ⟨fg_smul_max hb hL.fg, ?_⟩
  rw [eq_top_iff, ← hL.span_eq_top, span_le]
  intro l hl
  obtain ⟨γ, hγ, hγ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb0
  have h1 : γ • l ∈ (b • L : Submodule R V) := smul_mem_smul hγ hl
  rw [SetLike.mem_coe, show l = γ⁻¹ • (γ • l) by rw [smul_smul, inv_mul_cancel₀ hγ0, one_smul]]
  exact Submodule.smul_mem _ _ (subset_span h1)

/-- `(1/b) • b • M = M`. -/
theorem inv_smul_smul_max {b : Submodule R F} (hb : b.FG) (hb0 : b ≠ ⊥) (M : Submodule R V) :
    (1 / b) • b • M = M := by
  rw [← mul_smul_submodule, mul_comm, mul_one_div_cancel_of_fg hb hb0, Submodule.one_smul]

/-- `b • (1/b) • M = M`. -/
theorem smul_inv_smul_max {b : Submodule R F} (hb : b.FG) (hb0 : b ≠ ⊥) (M : Submodule R V) :
    b • (1 / b) • M = M := by
  rw [← mul_smul_submodule, mul_one_div_cancel_of_fg hb hb0, Submodule.one_smul]

/-- **Scaling a maximal lattice** (O'Meara 1963, §82H, p. 234): if $L$ is $\mathfrak a$-maximal on $V$ then
$\mathfrak bL$ is $\mathfrak b^2\mathfrak a$-maximal for every fractional ideal $\mathfrak b$ (in particular $\alpha L$
is $\alpha^2\mathfrak a$-maximal, $\mathfrak b = \alpha\mathfrak o$). -/
@[kb "omeara1963" "§82H, p. 234 (bL is b²a-maximal)"]
theorem IsMaximal.ideal_smul {a : Submodule R F} {L : Submodule R V} (hL : IsMaximal Q a L) {b : Submodule R F}
    (hb : b.FG) (hb0 : b ≠ ⊥) : IsMaximal Q (b ^ 2 * a) (b • L) := by
  obtain ⟨hlat, hn, hmax⟩ := hL
  obtain ⟨hif, hin⟩ := one_div_fg hb hb0
  have hinv : b * (1 / b) = 1 := mul_one_div_cancel_of_fg hb hb0
  refine ⟨isLattice_smul_max hb hb0 hlat, ?_, fun K hK hbK hnK => ?_⟩
  · rw [normIdeal_smul Q b hlat.fg]; exact mul_le_mul' le_rfl hn
  · have hK' : ((1 / b) • K).IsLattice F := isLattice_smul_max hif hin hK
    have hLK' : L ≤ (1 / b) • K := by
      rw [← inv_smul_smul_max hb hb0 L]; exact Submodule.smul_mono le_rfl hbK
    have hnK' : normIdeal Q ((1 / b) • K) ≤ a := by
      rw [normIdeal_smul Q (1 / b) hK.fg]
      calc (1 / b) ^ 2 * normIdeal Q K ≤ (1 / b) ^ 2 * (b ^ 2 * a) := mul_le_mul' le_rfl hnK
        _ = a := by rw [← mul_assoc, ← mul_pow, mul_comm (1 / b) b, hinv, one_pow, one_mul]
    have h := hmax _ hK' hLK' hnK'
    calc K = b • (1 / b) • K := (smul_inv_smul_max hb hb0 K).symm
      _ = b • L := by rw [h]

/-- **Components of a maximal lattice are maximal** (O'Meara 1963, §82H, p. 234), over a Dedekind domain: if $L$ is
$\mathfrak a$-maximal on $W$ and $L = J \perp L'$ with $J$ regular, then $L'$ is $\mathfrak a$-maximal on
$W \cap J^\perp$ (`perpIn`). -/
@[kb "omeara1963" "§82H, p. 234 (components of an a-maximal lattice are a-maximal)"]
theorem Dedekind.IsMaxIn.complement {a : Submodule R F} {W : Submodule F V} {L J L' : Submodule R V}
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
  · have hJM : ∀ x ∈ J, ∀ y ∈ M, bil Q x y = 0 := fun x hx y hy => by
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

/-- The submodule `{v | 2 B(v, K) ⊆ a}`. -/
def dualLatMax (a : Submodule R F) (K : Submodule R V) : Submodule R V where
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

/-- A lattice on a regular space is regular. -/
theorem isRegular_of_lattice_max (hV : (QuadraticMap.associated Q).Nondegenerate) {K : Submodule R V}
    (hK : K.IsLattice F) : IsRegular Q K := by
  intro x hx hx0
  have hall : ∀ y, bil Q x y = 0 := by
    intro y
    have hy : y ∈ span F (K : Set V) := by rw [hK.span_eq_top]; trivial
    exact bil_zero_of_mem_span_F Q hx0 hy
  exact hV.1 x fun y => by simpa [bil] using hall y

/-- `{v | 2 B(v, K) ⊆ a}` is finitely generated for a lattice `K` on a regular space and `a` finitely generated. -/
theorem fg_dualLatMax (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    {K : Submodule R V} (hK : K.IsLattice F) : (dualLatMax Q a K).FG := by
  obtain ⟨d, hd, hdint⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors R) ha
  have hd0 : algebraMap R F d ≠ 0 := fun h => nonZeroDivisors.ne_zero hd
    ((IsFractionRing.injective R F) (by simpa using h))
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  set c : F := (2 * algebraMap R F d)⁻¹ with hc
  let f : V →ₗ[R] V := ((c • LinearMap.id : V →ₗ[F] V)).restrictScalars R
  have hreg := isRegular_of_lattice_max Q hV hK
  refine FG.of_le ((dual_fg Q hK.fg hreg).map f) ?_
  intro v hv
  refine Submodule.mem_map.mpr ⟨((2 * algebraMap R F d) • v), ⟨?_, fun k hk => ?_⟩, ?_⟩
  · rw [hK.span_eq_top]; trivial
  · obtain ⟨r, hr⟩ := hdint _ (hv k hk)
    rw [bil_smul_left]
    have : 2 * algebraMap R F d * bil Q v k = d • (2 * bil Q v k) := by
      rw [Algebra.smul_def]; ring
    rw [this, ← hr]
    exact Submodule.mem_one.mpr ⟨r, rfl⟩
  · show c • ((2 * algebraMap R F d) • v) = v
    rw [smul_smul, hc, inv_mul_cancel₀ (mul_ne_zero h2 hd0), one_smul]

/-- **Proposition 82:18** (O'Meara 1963, p. 234). Let $L$ be a lattice on a non-zero regular quadratic space $V$ with
$\mathfrak nL \subseteq \mathfrak a$, $\mathfrak a$ a fractional ideal. Then there is an $\mathfrak a$-maximal lattice
$K$ on $V$ with $K \supseteq L$. (O'Meara counts the finitely many ideals between $\mathfrak vL$ and
$(\tfrac12\mathfrak a)^r$; here the lattices $K \supseteq L$ with $\mathfrak nK \subseteq \mathfrak a$ lie in a fixed
lattice, and $R$ is Noetherian.) -/
@[kb "omeara1963" "§82H, 82:18, p. 234"]
theorem Dedekind.exists_isMaximal_ge (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F}
    (ha : a.FG) {L : Submodule R V} (hL : L.IsLattice F) (hnL : normIdeal Q L ≤ a) :
    ∃ K, L ≤ K ∧ IsMaximal Q a K := by
  classical
  set K' := dualLatMax Q a L with hK'
  have hLK' : L ≤ K' := by
    intro k hk k' hk'
    exact hnL (two_mul_mem_normIdeal Q (bil_mem_scale Q hk hk'))
  have hfg : K'.FG := fg_dualLatMax Q hV ha hL
  have : Module.Finite R K' := Module.Finite.iff_fg.mpr hfg
  let S : Set (Submodule R K') :=
    {N | L ≤ N.map K'.subtype ∧ normIdeal Q (N.map K'.subtype) ≤ a}
  have e : (L.comap K'.subtype).map K'.subtype = L := by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hLK'
  have hS : S.Nonempty := ⟨L.comap K'.subtype, by rw [e], by rw [e]; exact hnL⟩
  obtain ⟨N, hNS, hNmax⟩ :=
    (set_has_maximal_iff_noetherian (R := R) (M := K')).mpr inferInstance S hS
  have hfgM : (N.map K'.subtype).FG := (IsNoetherian.noetherian N).map _
  have hlat : (N.map K'.subtype).IsLattice F :=
    Submodule.IsLattice.of_le_of_isLattice_of_fg F hNS.1 hfgM
  refine ⟨N.map K'.subtype, hNS.1, hlat, hNS.2, ?_⟩
  intro N2 hN2 hMN2 hnN2
  have hKN2 : L ≤ N2 := hNS.1.trans hMN2
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

/-- **Corollary 82:18a** (O'Meara 1963, p. 234): every non-zero regular quadratic space contains an
$\mathfrak a$-maximal lattice for every fractional ideal $\mathfrak a$. -/
@[kb "omeara1963" "§82H, 82:18a, p. 234"]
theorem exists_isMaximal (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) : ∃ L, IsMaximal Q a L := by
  classical
  obtain ⟨α, hα, hα0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha0
  let b := Module.finBasis F V
  obtain ⟨e, he⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R)
    (Finset.univ : Finset (Fin (finrank F V) × Fin (finrank F V)))
    (fun p => bil Q (b p.1) (b p.2) / α)
  have he0 : algebraMap R F (e : R) ≠ 0 := fun h => nonZeroDivisors.ne_zero e.2
    ((IsFractionRing.injective R F) (by simp at h))
  set L0 : Submodule R V := span R (Set.range fun i => (e : R) • b i) with hL0
  have hlat : L0.IsLattice F := by
    refine ⟨fg_span (Set.finite_range _), ?_⟩
    rw [eq_top_iff, ← b.span_eq, span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : (e : R) • b i ∈ span F (L0 : Set V) := subset_span (subset_span ⟨i, rfl⟩)
    have : b i = (algebraMap R F (e : R))⁻¹ • ((e : R) • b i) := by
      rw [← algebraMap_smul F (e : R), smul_smul, inv_mul_cancel₀ he0, one_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ h1
  have hn : normIdeal Q L0 ≤ a := by
    refine (normIdeal_le_scale Q L0).trans ?_
    rw [hL0, scale_span, span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    obtain ⟨r, hr⟩ := he (i, j) (Finset.mem_univ _)
    show bil Q ((e : R) • b i) ((e : R) • b j) ∈ a
    rw [bil_rsmul_left, bil_rsmul_right]
    have h' : algebraMap R F r = algebraMap R F (e : R) * (bil Q (b i) (b j) / α) := by
      rw [hr, Algebra.smul_def]
    have : algebraMap R F (e : R) * (algebraMap R F (e : R) * bil Q (b i) (b j)) =
        ((e : R) * r) • α := by
      rw [Algebra.smul_def, map_mul, h']
      field_simp
    rw [this]
    exact a.smul_mem _ hα
  obtain ⟨K, -, hK⟩ := Dedekind.exists_isMaximal_ge Q hV ha hlat hn
  exact ⟨K, hK⟩

/-- **Proposition 82:19, first part** (O'Meara 1963, p. 234). Let $L$ be a lattice on the $r$-dimensional regular
quadratic space $V$ and $\mathfrak a$ a fractional ideal with $\mathfrak nL \subseteq \mathfrak a$. Then the ideal
$2^r(\mathfrak vL)\mathfrak a^{-r}$ is integral. (The OCR text shows "$2^r(\mathfrak vL) + (\mathfrak a)^r$"; the
quotient is restored from the proof, "$(\mathfrak vL) \subseteq (\mathfrak sL)^r \subseteq (\frac12\mathfrak a)^r$".) -/
@[kb "omeara1963" "§82H, 82:19, p. 234 (2^r vL / a^r is integral)"]
theorem two_pow_mul_volume_le_one {a : Submodule R F}
    (ha : a.FG) (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) (hnL : normIdeal Q L ≤ a) :
    span R {(2 : F) ^ finrank F V} * volume Q L * (1 / a) ^ finrank F V ≤ 1 := by
  have hr : finrank R L = finrank F V := by
    rw [finrank_eq_finrank_span (F := F) L, hL.span_eq_top, finrank_top]
  have h2s : span R {(2 : F)} * scale Q L ≤ a := by
    rw [Submodule.mul_le]
    intro m hm n hn
    obtain ⟨c, rfl⟩ := mem_span_singleton.1 hm
    rw [smul_mul_assoc]
    exact a.smul_mem c (hnL (two_mul_mem_normIdeal Q hn))
  have hv := volume_le_scale_pow Q L
  rw [hr] at hv
  have hp : span R {(2 : F) ^ finrank F V} = (span R {(2 : F)}) ^ finrank F V := by
    rw [span_pow, Set.singleton_pow]
  calc span R {(2 : F) ^ finrank F V} * volume Q L * (1 / a) ^ finrank F V
      ≤ (span R {(2 : F)} * scale Q L) ^ finrank F V * (1 / a) ^ finrank F V := by
        refine mul_le_mul' ?_ le_rfl
        rw [hp, mul_pow]
        exact mul_le_mul' le_rfl hv
    _ ≤ a ^ finrank F V * (1 / a) ^ finrank F V :=
        mul_le_mul' (pow_le_pow_left' h2s _) le_rfl
    _ = 1 := by rw [← mul_pow, mul_one_div_cancel_of_fg ha ha0, one_pow]

/-- **Proposition 82:19, second part** (O'Meara 1963, pp. 234–235). In the situation of
`two_pow_mul_volume_le_one`, if $2^r(\mathfrak vL)\mathfrak a^{-r}$ has no integral square factors (no integral ideal
$\mathfrak b \ne \mathfrak o$ with $\mathfrak b^2$ dividing it, i.e. containing it), then $L$ is
$\mathfrak a$-maximal. -/
@[kb "omeara1963" "§82H, 82:19, pp. 234–235"]
theorem isMaximal_of_squarefree {a : Submodule R F}
    (ha : a.FG) (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) (hnL : normIdeal Q L ≤ a)
    (hsq : ∀ b : Submodule R F, b ≤ 1 → b ≠ ⊥ →
      span R {(2 : F) ^ finrank F V} * volume Q L * (1 / a) ^ finrank F V ≤ b ^ 2 → b = 1) :
    IsMaximal Q a L := by
  refine ⟨hL, hnL, fun K hK hLK hnK => ?_⟩
  have hspan : span F (L : Set V) = span F (K : Set V) := by rw [hL.span_eq_top, hK.span_eq_top]
  obtain ⟨b, hbfg, hb0, hb1, hvol, -, hone⟩ := exists_volume_eq_sq_mul Q hL.fg hK.fg hspan hLK
  have hK1 := two_pow_mul_volume_le_one Q ha ha0 hK hnK
  have hle : span R {(2 : F) ^ finrank F V} * volume Q L * (1 / a) ^ finrank F V ≤ b ^ 2 := by
    calc span R {(2 : F) ^ finrank F V} * volume Q L * (1 / a) ^ finrank F V
        = b ^ 2 * (span R {(2 : F) ^ finrank F V} * volume Q K * (1 / a) ^ finrank F V) := by
          rw [hvol]; ring
      _ ≤ b ^ 2 * 1 := mul_le_mul' le_rfl hK1
      _ = b ^ 2 := mul_one _
  exact (hone (hsq b hb1 hb0 hle)).symm

/-- If `nL ⊆ 2h` then `sL ⊆ h`. -/
theorem scale_le_of_norm_le_max {h : Submodule R F} {L : Submodule R V}
    (hn : normIdeal Q L ≤ span R {(2 : F)} * h) : scale Q L ≤ h := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  rw [scale, span_le]
  rintro _ ⟨l, hl, l', hl', rfl⟩
  have := hn (two_mul_mem_normIdeal Q (bil_mem_scale Q hl hl'))
  obtain ⟨y, hy, hy2⟩ := Submodule.mem_span_singleton_mul.1 this
  have : y = bil Q l l' := mul_left_cancel₀ h2 hy2
  show bil Q l l' ∈ h
  rw [← this]
  exact hy

/-- `coeff L x ⊆ h · coeff L# x` when `nL ⊆ 2h`. -/
theorem coeff_le_mul_coeff_dual_max {h : Submodule R F} (hh : h.FG) (hh0 : h ≠ ⊥) {L : Submodule R V}
    (hn : normIdeal Q L ≤ span R {(2 : F)} * h) (x : V) :
    coeff F L x ≤ h * coeff F (dual Q L) x := by
  have hinv := mul_one_div_cancel_of_fg hh hh0
  have hsc := scale_le_of_norm_le_max Q hn
  have step : coeff F L x * (1 / h) ≤ coeff F (dual Q L) x := by
    rw [Submodule.mul_le]
    intro t ht σ hσ
    have ht' : t • x ∈ L := ht
    show (t * σ) • x ∈ dual Q L
    rw [show (t * σ) • x = σ • (t • x) by rw [smul_smul, mul_comm]]
    refine ⟨Submodule.smul_mem _ _ (subset_span ht'), fun l hl => ?_⟩
    rw [bil_smul_left]
    exact (Submodule.mem_div_iff_forall_mul_mem.1 hσ) _ (hsc (bil_mem_scale Q ht' hl))
  calc coeff F L x = coeff F L x * (h * (1 / h)) := by rw [hinv, mul_one]
    _ = h * (coeff F L x * (1 / h)) := by ring
    _ ≤ h * coeff F (dual Q L) x := mul_le_mul' le_rfl step

/-- `h · coeff L# x ⊆ coeff L x` for an isotropic vector `x` and `L` `2h`-maximal. -/
theorem mul_coeff_dual_le_max (hV : (QuadraticMap.associated Q).Nondegenerate) {h : Submodule R F}
    (hh : h.FG) {L : Submodule R V} (hL : IsMaximal Q (span R {(2 : F)} * h) L) {x : V} (hx0 : x ≠ 0)
    (hQx : Q x = 0) : h * coeff F (dual Q L) x ≤ coeff F L x := by
  obtain ⟨hlat, hn, hmax⟩ := hL
  have hreg := isRegular_of_lattice_max Q hV hlat
  have hcfg : (coeff F (dual Q L) x).FG := coeff_fg (dual_fg Q hlat.fg hreg) hx0
  have hfg : (h * coeff F (dual Q L) x).FG := hh.mul hcfg
  set L' : Submodule R V := L ⊔ (h * coeff F (dual Q L) x) • span R {x} with hL'
  have hL'lat : L'.IsLattice F :=
    Submodule.IsLattice.of_le_of_isLattice_of_fg F (M := L) le_sup_left
      (hlat.fg.sup (fg_smul_max hfg (fg_span_singleton x)))
  have hkey : ∀ r ∈ h * coeff F (dual Q L) x, ∀ l ∈ L, r * bil Q l x ∈ h := by
    intro r hr l hl
    refine Submodule.mul_induction_on hr (fun h₀ hh₀ γ hγ => ?_) (fun u v hu hv => ?_)
    · have hγx : γ • x ∈ dual Q L := hγ
      have h1 := mul_mem_mul hh₀ (hγx.2 l hl)
      rw [mul_one, bil_smul_left] at h1
      rw [bil_comm Q l x]
      have h2 : h₀ * γ * bil Q x l = h₀ * (γ * bil Q x l) := by ring
      rw [h2]; exact h1
    · rw [add_mul]; exact add_mem hu hv
  have hnL' : normIdeal Q L' ≤ span R {(2 : F)} * h := by
    rw [normIdeal, span_le]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨l, hl, w, hw, rfl⟩ := mem_sup.1 hz
    obtain ⟨r, hr, rfl⟩ := (mem_smul_span_singleton_iff' _ _ _).1 hw
    show Q (l + r • x) ∈ _
    rw [Q_add, Q_smul, hQx, mul_zero, add_zero, bil_smul_right]
    refine add_mem (hn (Q_mem_normIdeal Q hl)) ?_
    have := mul_mem_mul (mem_span_singleton_self (2 : F)) (hkey r hr l hl)
    convert this using 1
  have heq := hmax L' hL'lat le_sup_left hnL'
  intro r hr
  have hrx : r • x ∈ L' := mem_sup_right (smul_mem_smul hr (mem_span_singleton_self x))
  rw [heq] at hrx
  exact hrx

/-- For a regular lattice `D` and `0 ≠ x ∈ FD` there is `y ∈ FD` with `B(x, y) = 1` and `B(y, D) ⊆ coeff D x`. -/
theorem exists_dual_vec_max {D : Submodule R V} (hD : D.FG) (hreg : IsRegular Q D) {x : V}
    (hx : x ∈ span F (D : Set V)) (hx0 : x ≠ 0) :
    ∃ y ∈ span F (D : Set V), bil Q x y = 1 ∧ ∀ d ∈ D, bil Q y d ∈ coeff F D x := by
  obtain ⟨n, w, e, c, hw, he, hDeq, hc0, hw0⟩ := exists_adapted_first (F := F) hD hx hx0
  have hdet := (isRegular_adapted_iff Q w hw e fun i => (he i).2).1 (hDeq ▸ hreg)
  obtain ⟨w', hw', hww'⟩ := exists_biorth Q w hdet
  have hspan : span F (Set.range w) = span F (D : Set V) := by
    rw [hDeq]; exact (span_adapted e (fun i => (he i).2) w).symm
  refine ⟨c • w' 0, Submodule.smul_mem _ _ (hspan ▸ hw' 0), ?_, ?_⟩
  · have h1 := hww' 0 0
    rw [hw0, bil_smul_left] at h1
    rw [bil_smul_right]
    simpa using h1
  · intro d hd
    rw [hDeq] at hd
    obtain ⟨γ, hγ, rfl⟩ := (mem_iSup_smul_span_iff_exists e w d).1 hd
    rw [bil_sum_right]
    have h1 : ∑ i, bil Q (c • w' 0) (γ i • w i) = c * γ 0 := by
      simp [biorth_symm Q w w' hww']
      ring
    rw [h1, mem_coeff, show (c * γ 0) • x = γ 0 • w 0 by rw [hw0, smul_smul, mul_comm], hDeq]
    exact mem_iSup_of_mem 0 (smul_mem_smul (hγ 0) (mem_span_singleton_self _))

/-- `b x ⊔ d y` as an adaptation indexed by `Fin 2`. -/
theorem sup_eq_iSup_fin_two_max (b d : Submodule R F) (x y : V) :
    b • span R {x} ⊔ d • span R {y} =
      ⨆ i : Fin 2, (![b, d] i) • span R {(![x, y] : Fin 2 → V) i} := by
  apply le_antisymm
  · exact sup_le (le_iSup (fun i : Fin 2 => (![b, d] i) • span R {(![x, y] : Fin 2 → V) i}) 0)
      (le_iSup (fun i : Fin 2 => (![b, d] i) • span R {(![x, y] : Fin 2 → V) i}) 1)
  · exact iSup_le (Fin.forall_fin_two.2 ⟨le_sup_left, le_sup_right⟩)

/-- `R · (-1) = 𝔬`. -/
theorem span_neg_one_max : span R {(-1 : F)} = 1 := by
  rw [Submodule.one_eq_span]
  apply le_antisymm
  · rw [span_le, Set.singleton_subset_iff]
    exact neg_mem (mem_span_singleton_self 1)
  · rw [span_le, Set.singleton_subset_iff]
    have := neg_mem (mem_span_singleton_self (-1 : F) (R := R))
    rwa [neg_neg] at this

/-- A hyperbolic pair is linearly independent with Gram determinant `-1`. -/
theorem hyp_pair_li_max {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1) :
    LinearIndependent F ![x, y] ∧ (gram Q ![x, y]).det = -1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp [bil] at hxy
  refine ⟨?_, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (bil Q x) hst
    simp [bil_add_right, hx, hxy] at h1
    subst h1
    simp only [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right hx0, rfl⟩
  · rw [Matrix.det_fin_two]
    simp [gram, hx, hy, hxy, bil_comm Q y x]

/-- The binary lattice `b x + d y` of a hyperbolic pair with `b d = h` and scale `⊆ h` is `h`-modular of rank 2. -/
theorem isModular_hyp_max {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1)
    {b d h : Submodule R F} (hb : b.FG) (hb0 : b ≠ ⊥) (hd : d.FG) (hd0 : d ≠ ⊥) (hh : h.FG) (hh0 : h ≠ ⊥)
    (hbd : b * d = h) (hs : scale Q (b • span R {x} ⊔ d • span R {y}) ≤ h) :
    IsModular Q h (b • span R {x} ⊔ d • span R {y}) ∧
      finrank R (b • span R {x} ⊔ d • span R {y} : Submodule R V) = 2 := by
  obtain ⟨hli, hdet⟩ := hyp_pair_li_max Q hx hy hxy
  have hAfg : ∀ i, (![b, d] i).FG ∧ ![b, d] i ≠ ⊥ := Fin.forall_fin_two.2 ⟨⟨hb, hb0⟩, hd, hd0⟩
  rw [sup_eq_iSup_fin_two_max] at hs ⊢
  have hrk : finrank R (⨆ i : Fin 2, (![b, d] i) • span R {(![x, y] : Fin 2 → V) i} : Submodule R V) = 2 := by
    rw [finrank_adapted _ (fun i => (hAfg i).2) _ hli]; simp
  have hvol : volume Q (⨆ i : Fin 2, (![b, d] i) • span R {(![x, y] : Fin 2 → V) i} : Submodule R V) = h ^ 2 := by
    rw [volume_eq_of_adapted Q _ hli _ hAfg, Fin.prod_univ_two, hdet, span_neg_one_max, mul_one]
    show (b * d) ^ 2 = h ^ 2
    rw [hbd]
  refine ⟨isModular_of_volume_eq Q hh hh0 ?_ hs (by rw [hvol, hrk]), hrk⟩
  intro hbot
  rw [hbot] at hrk
  simp at hrk

/-- Core of 82:20: a `2h`-maximal `L` splits as `𝔞_x x + 𝔞_y y` plus a complement for isotropic `x ∈ L`. -/
theorem hyp_split_max (hV : (QuadraticMap.associated Q).Nondegenerate) {h : Submodule R F} (hh : h.FG)
    (hh0 : h ≠ ⊥) {L : Submodule R V} (hL : IsMaximal Q (span R {(2 : F)} * h) L) {x : V} (hxL : x ∈ L)
    (hx0 : x ≠ 0) (hQx : Q x = 0) :
    ∃ y : V, Q y = 0 ∧ bil Q x y = 1 ∧ coeff F L x * coeff F L y = h ∧
      IsModular Q h (coeff F L x • span R {x} ⊔ coeff F L y • span R {y}) ∧
      finrank R (coeff F L x • span R {x} ⊔ coeff F L y • span R {y} : Submodule R V) = 2 ∧
      ∃ K, IsOrthSum Q L (coeff F L x • span R {x} ⊔ coeff F L y • span R {y}) K := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hlat := hL.1
  have hn := hL.2.1
  have hreg := isRegular_of_lattice_max Q hV hlat
  have hLfg := hlat.fg
  have hDfg := dual_fg Q hLfg hreg
  have hregD := isRegular_dual Q hLfg hreg
  have hspanD := span_dual Q hLfg hreg
  have hxD : x ∈ span F (dual Q L : Set V) := by rw [hspanD]; exact subset_span hxL
  have hsc := scale_le_of_norm_le_max Q hn
  have hbx : coeff F L x = h * coeff F (dual Q L) x :=
    le_antisymm (coeff_le_mul_coeff_dual_max Q hh hh0 hn x) (mul_coeff_dual_le_max Q hV hh hL hx0 hQx)
  have hbxfg : (coeff F L x).FG := coeff_fg hLfg hx0
  have hbxne : coeff F L x ≠ ⊥ := coeff_ne_bot (subset_span hxL)
  have hcxfg : (coeff F (dual Q L) x).FG := coeff_fg hDfg hx0
  have hcxne : coeff F (dual Q L) x ≠ ⊥ := coeff_ne_bot hxD
  obtain ⟨hPfg, hPne⟩ := one_div_fg hcxfg hcxne
  have hcinv : coeff F (dual Q L) x * (1 / coeff F (dual Q L) x) = 1 := mul_one_div_cancel_of_fg hcxfg hcxne
  obtain ⟨y₁, hy₁span, hxy₁, hy₁D⟩ := exists_dual_vec_max Q hDfg hregD hxD hx0
  have hPy : ∀ δ ∈ 1 / coeff F (dual Q L) x, δ • y₁ ∈ L := by
    intro δ hδ
    have : δ • y₁ ∈ dual Q (dual Q L) := by
      refine ⟨Submodule.smul_mem _ _ hy₁span, fun d hd => ?_⟩
      rw [bil_smul_left]
      exact (Submodule.mem_div_iff_forall_mul_mem.1 hδ) _ (hy₁D d hd)
    rwa [dual_dual Q hLfg hreg] at this
  have hsq : (1 / coeff F (dual Q L) x) ^ 2 * span R {Q y₁} ≤ span R {(2 : F)} * h := by
    rw [← span_sq_eq_sq (R := R) (1 / coeff F (dual Q L) x), Submodule.mul_le]
    intro m hm n hn'
    obtain ⟨c, rfl⟩ := mem_span_singleton.1 hn'
    rw [mul_smul_comm]
    refine (span R {(2 : F)} * h).smul_mem c ?_
    refine span_induction (p := fun m _ => m * Q y₁ ∈ span R {(2 : F)} * h) ?_ (by simp) ?_ ?_ hm
    · rintro _ ⟨δ, hδ, rfl⟩
      have := hn (Q_mem_normIdeal Q (hPy δ hδ))
      rwa [Q_smul] at this
    · intro u v _ _ hu hv; rw [add_mul]; exact add_mem hu hv
    · intro r u _ hu; rw [smul_mul_assoc]; exact smul_mem _ r hu
  have hS : (1 / coeff F (dual Q L) x) * span R {Q y₁ / 2} ≤ coeff F L x := by
    have e1 : span R {Q y₁ / 2} = span R {Q y₁} * span R {(2 : F)⁻¹} := by
      rw [span_mul_span, Set.singleton_mul_singleton, div_eq_mul_inv]
    have e2 : span R {(2 : F)} * span R {(2 : F)⁻¹} = 1 := by
      rw [span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ h2, ← Submodule.one_eq_span]
    calc (1 / coeff F (dual Q L) x) * span R {Q y₁ / 2}
        = (coeff F (dual Q L) x * (1 / coeff F (dual Q L) x)) *
            ((1 / coeff F (dual Q L) x) * span R {Q y₁ / 2}) := by rw [hcinv, one_mul]
      _ = coeff F (dual Q L) x * ((1 / coeff F (dual Q L) x) ^ 2 * span R {Q y₁}) *
            span R {(2 : F)⁻¹} := by rw [e1]; ring
      _ ≤ coeff F (dual Q L) x * (span R {(2 : F)} * h) * span R {(2 : F)⁻¹} :=
          mul_le_mul' (mul_le_mul' le_rfl hsq) le_rfl
      _ = coeff F (dual Q L) x * h * (span R {(2 : F)} * span R {(2 : F)⁻¹}) := by ring
      _ = coeff F L x := by rw [e2, mul_one, hbx, mul_comm]
  set y : V := y₁ - (Q y₁ / 2) • x with hy
  have hyeq : y = y₁ + (-(Q y₁ / 2)) • x := by rw [hy, neg_smul, sub_eq_add_neg]
  have hQy : Q y = 0 := by
    rw [hyeq, Q_add, Q_smul, hQx, bil_smul_right, bil_comm Q y₁ x, hxy₁]
    field_simp
    ring
  have hxy : bil Q x y = 1 := by
    rw [hyeq, bil_add_right, bil_smul_right, bil_self, hQx, hxy₁]; ring
  have hPy' : ∀ δ ∈ 1 / coeff F (dual Q L) x, δ • y ∈ L := by
    intro δ hδ
    have h1 : (δ * (Q y₁ / 2)) • x ∈ L := hS (mul_mem_mul hδ (mem_span_singleton_self _))
    rw [hy, smul_sub, smul_smul]
    exact L.sub_mem (hPy δ hδ) h1
  have hyspan : y ∈ span F (L : Set V) := by
    rw [hy]
    refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ (subset_span hxL))
    rw [← hspanD]; exact hy₁span
  have hy0 : y ≠ 0 := by rintro h0; rw [h0] at hxy; simp [bil] at hxy
  have hdyfg : (coeff F L y).FG := coeff_fg hLfg hy0
  have hdyne : coeff F L y ≠ ⊥ := coeff_ne_bot hyspan
  have hbd : coeff F L x * coeff F L y ≤ h := by
    rw [Submodule.mul_le]
    intro t ht α hα
    have := hsc (bil_mem_scale Q (show t • x ∈ L from ht) (show α • y ∈ L from hα))
    rwa [bil_smul_left, bil_smul_right, hxy, mul_one] at this
  have hbP : coeff F L x * (1 / coeff F (dual Q L) x) = h := by
    rw [hbx]
    calc h * coeff F (dual Q L) x * (1 / coeff F (dual Q L) x)
        = h * (coeff F (dual Q L) x * (1 / coeff F (dual Q L) x)) := by ring
      _ = h := by rw [hcinv, mul_one]
  have hbdeq : coeff F L x * coeff F L y = h := by
    refine le_antisymm hbd ?_
    rw [← hbP]
    exact mul_le_mul' le_rfl fun δ hδ => hPy' δ hδ
  have hJL : coeff F L x • span R {x} ⊔ coeff F L y • span R {y} ≤ L :=
    sup_le ((coeff_smul_span L x).le.trans inf_le_left) ((coeff_smul_span L y).le.trans inf_le_left)
  have hJfg : (coeff F L x • span R {x} ⊔ coeff F L y • span R {y}).FG :=
    (fg_smul_max hbxfg (fg_span_singleton x)).sup (fg_smul_max hdyfg (fg_span_singleton y))
  obtain ⟨hmod, hrk⟩ := isModular_hyp_max Q hQx hQy hxy hbxfg hbxne hdyfg hdyne hh hh0 hbdeq
    ((scale_mono Q hJL).trans hsc)
  obtain ⟨K, hK⟩ := (Dedekind.splits_iff_of_isModular Q hJL hmod hJfg).mpr
    (fun u hu l hl => hsc (bil_mem_scale Q (hJL hu) hl))
  exact ⟨y, hQy, hxy, hbdeq, hmod, hrk, K, hK⟩

/-- A maximal lattice on a regular space is `2h`-maximal for a fractional ideal `h` (`h = ½ nL`). -/
theorem exists_half_isMaximal_max (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F}
    {L : Submodule R V} (hL : IsMaximal Q a L) {x : V} (hxL : x ∈ L) (hx0 : x ≠ 0) :
    ∃ h : Submodule R F, h.FG ∧ h ≠ ⊥ ∧ IsMaximal Q (span R {(2 : F)} * h) L := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hreg := isRegular_of_lattice_max Q hV hL.1
  have hn0 : normIdeal Q L ≠ ⊥ := by
    intro h0
    apply hx0
    refine hreg x hxL fun l hl => ?_
    have := two_mul_mem_normIdeal Q (bil_mem_scale Q hxL hl)
    rw [h0, Submodule.mem_bot] at this
    exact (mul_eq_zero.1 this).resolve_left h2
  have hnfg : (normIdeal Q L).FG := FG.of_le (scale_fg Q hL.1.fg) (normIdeal_le_scale Q L)
  have e2 : span R {(2 : F)} * span R {(2 : F)⁻¹} = 1 := by
    rw [span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ h2, ← Submodule.one_eq_span]
  have hi0 : span R {(2 : F)⁻¹} ≠ ⊥ := fun h0 => (inv_ne_zero h2) (span_singleton_eq_bot.1 h0)
  refine ⟨span R {(2 : F)⁻¹} * normIdeal Q L, (fg_span_singleton _).mul hnfg, mul_ne_bot' hi0 hn0, ?_⟩
  have heq : span R {(2 : F)} * (span R {(2 : F)⁻¹} * normIdeal Q L) = normIdeal Q L := by
    rw [← mul_assoc, e2, one_mul]
  rw [heq]
  exact ⟨hL.1, le_rfl, fun K hK hLK hnK => hL.2.2 K hK hLK (hnK.trans hL.2.1)⟩

/-- **Proposition 82:20** (O'Meara 1963, p. 235), over a Dedekind domain. Let $L$ be an $\mathfrak a$-maximal lattice
on the regular space $V$ and $x$ an isotropic vector in $L$. Then there is a binary lattice $J$ (of rank $2$) which
splits $L$ and contains $x$. -/
@[kb "omeara1963" "§82H, 82:20, p. 235"]
theorem Dedekind.exists_binary_split_of_isMaximal (hV : (QuadraticMap.associated Q).Nondegenerate)
    {a : Submodule R F} {L : Submodule R V} (hL : IsMaximal Q a L) {x : V} (hxL : x ∈ L) (hx0 : x ≠ 0)
    (hQx : Q x = 0) : ∃ J : Submodule R V, J ≤ L ∧ x ∈ J ∧ finrank R J = 2 ∧ ∃ K, IsOrthSum Q L J K := by
  obtain ⟨h, hh, hh0, hmax⟩ := exists_half_isMaximal_max Q hV hL hxL hx0
  obtain ⟨y, hQy, hxy, hbd, -, hrk, K, hK⟩ := hyp_split_max Q hV hh hh0 hmax hxL hx0 hQx
  refine ⟨_, le_sup_left.trans hK.sup_eq.le, ?_, hrk, K, hK⟩
  have h1 : (1 : F) ∈ coeff F L x := one_le_coeff_iff.2 hxL (Submodule.mem_one.2 ⟨1, map_one _⟩)
  have h2 : (1 : F) • x ∈ coeff F L x • span R {x} := smul_mem_smul h1 (mem_span_singleton_self x)
  rw [one_smul] at h2
  exact mem_sup_left h2

/-- The rank of a lattice on `V` is `dim V`. -/
theorem finrank_lattice_max {L : Submodule R V} (hL : L.IsLattice F) : finrank R L = finrank F V := by
  rw [finrank_eq_finrank_span (F := F) L, hL.span_eq_top, finrank_top]

/-- A lattice on a space with a non-zero isotropic vector contains one. -/
theorem exists_iso_in_lattice_max {L : Submodule R V} (hL : L.IsLattice F)
    (hiso : ∃ v : V, v ≠ 0 ∧ Q v = 0) : ∃ x ∈ L, x ≠ 0 ∧ Q x = 0 := by
  have htf := isTorsionFree_of_fractionRing (R := R) (F := F) (V := V)
  obtain ⟨v, hv0, hQv⟩ := hiso
  obtain ⟨d, hd, hdv⟩ := exists_smul_mem_of_mem_span (S := L)
    (by rw [hL.span_eq_top]; trivial : v ∈ span F (L : Set V))
  exact ⟨d • v, hdv, smul_ne_zero hd hv0, by rw [Q_rsmul, hQv, mul_zero]⟩

/-- If `L = J ⊥ K` and `L`, `J` both have rank 2 then `L = J`. -/
theorem eq_of_isOrthSum_rank_max {L J K : Submodule R V} (h : IsOrthSum Q L J K) (hJ : finrank R J = 2)
    (hL : finrank R L = 2) : L = J := by
  have hrank : finrank R L = finrank R J + finrank R K := by
    rw [← h.sup_eq]; exact finrank_sup_of_disjoint' (F := F) h.disjoint
  have hK0 : K = ⊥ := by
    by_contra hK
    have := one_le_finrank_of_ne_bot (F := F) hK
    omega
  rw [← h.sup_eq, hK0, sup_bot_eq]

/-- **Proposition 82:21** (O'Meara 1963, pp. 235–236). Let $L$ be a lattice on the hyperbolic plane $V$ and
$\mathfrak a$ a fractional ideal. Then $L$ is $2\mathfrak a$-maximal if and only if $L$ is $\mathfrak a$-modular with
$\mathfrak nL \subseteq 2\mathfrak a$. -/
@[kb "omeara1963" "§82H, 82:21, pp. 235–236"]
theorem isMaximal_iff_isModular_of_hyperbolic (hV : (QuadraticMap.associated Q).Nondegenerate)
    (hdim : finrank F V = 2) (hiso : ∃ v : V, v ≠ 0 ∧ Q v = 0) {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥)
    {L : Submodule R V} (hL : L.IsLattice F) :
    IsMaximal Q (span R {2} * a) L ↔ IsModular Q a L ∧ normIdeal Q L ≤ span R {2} * a := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hsp0 : span R {(2 : F)} ≠ ⊥ := fun h0 => h2 (span_singleton_eq_bot.1 h0)
  have ha2fg : (span R {(2 : F)} * a).FG := (fg_span_singleton _).mul ha
  have ha20 : span R {(2 : F)} * a ≠ ⊥ := mul_ne_bot' hsp0 ha0
  have hrk : finrank R L = 2 := by rw [finrank_lattice_max hL, hdim]
  constructor
  · intro hmax
    obtain ⟨x, hxL, hx0, hQx⟩ := exists_iso_in_lattice_max Q hL hiso
    obtain ⟨y, hQy, hxy, hbd, hmod, hrk2, K, hK⟩ := hyp_split_max Q hV ha ha0 hmax hxL hx0 hQx
    have hLJ := eq_of_isOrthSum_rank_max Q hK hrk2 hrk
    refine ⟨?_, hmax.2.1⟩
    rw [hLJ]; exact hmod
  · rintro ⟨hmod, hn⟩
    refine isMaximal_of_squarefree Q ha2fg ha20 hL hn ?_
    intro b hb1 hb0 hle
    have hvol : volume Q L = a ^ 2 := by rw [hmod.2.2, hrk]
    rw [hdim, hvol] at hle
    have hI : span R {(2 : F) ^ 2} * a ^ 2 * (1 / (span R {(2 : F)} * a)) ^ 2 = 1 := by
      have : span R {(2 : F) ^ 2} = span R {(2 : F)} ^ 2 := by rw [span_pow, Set.singleton_pow]
      rw [this, ← mul_pow, ← mul_pow, mul_one_div_cancel_of_fg ha2fg ha20, one_pow]
    rw [hI] at hle
    refine le_antisymm hb1 ?_
    calc (1 : Submodule R F) ≤ b ^ 2 := hle
      _ = b * b := sq b
      _ ≤ b * 1 := mul_le_mul' le_rfl hb1
      _ = b := mul_one b

/-- A quadratic space spanned by a hyperbolic pair is regular. -/
theorem nondeg_of_hyp_max {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1)
    (hspan : span F (Set.range ![x, y]) = ⊤) : (QuadraticMap.associated Q).Nondegenerate := by
  have key : ∀ v : V, (∀ w, bil Q v w = 0) → v = 0 := by
    intro v hv
    obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun F).1
      (hspan ▸ mem_top : v ∈ span F (Set.range ![x, y]))
    rw [Fin.sum_univ_two] at hc
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
    have h1 := hv x
    have h2 := hv y
    rw [← hc, bil_add_left, bil_smul_left, bil_smul_left, bil_self, hx, bil_comm Q y x, hxy] at h1
    rw [← hc, bil_add_left, bil_smul_left, bil_smul_left, bil_self, hy, hxy] at h2
    have hc1 : c 1 = 0 := by simpa using h1
    have hc0 : c 0 = 0 := by simpa using h2
    rw [← hc, hc0, hc1]; simp
  exact ⟨fun v hv => key v fun w => hv w, fun w hw => key w fun v => by rw [bil_comm]; exact hw v⟩

/-- `b • R(c x) = (R c · b) • R x`. -/
theorem smul_span_smul_max (b : Submodule R F) (c : F) (x : V) :
    b • span R {c • x} = (span R {c} * b) • span R {x} := by
  ext v
  rw [mem_smul_span_singleton_iff', mem_smul_span_singleton_iff']
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨c * γ, Submodule.mem_span_singleton_mul.2 ⟨γ, hγ, rfl⟩, by rw [smul_smul, mul_comm]⟩
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_span_singleton_mul.1 hγ
    exact ⟨z, hz, by rw [smul_smul, mul_comm]⟩

/-- Rescaling a pair `b₀ (c₀ x) + d₀ (c₁ y)` with `c₀ c₁ = 1` and `b₀ d₀ = a` to the form `b x + a b⁻¹ y`. -/
theorem rescale_pair_max {a b0 d0 : Submodule R F} (hb0 : b0.FG) (hb00 : b0 ≠ ⊥) (hbd : b0 * d0 = a)
    {c0 c1 : F} (hc : c0 * c1 = 1) (x y : V) :
    (span R {c0} * b0).FG ∧ span R {c0} * b0 ≠ ⊥ ∧
      b0 • span R {c0 • x} ⊔ d0 • span R {c1 • y} =
        (span R {c0} * b0) • span R {x} ⊔ (a * (1 / (span R {c0} * b0))) • span R {y} := by
  have hc0 : c0 ≠ 0 := left_ne_zero_of_mul_eq_one hc
  have hsc : span R {c0} ≠ ⊥ := fun h0 => hc0 (span_singleton_eq_bot.1 h0)
  have hbfg : (span R {c0} * b0).FG := (fg_span_singleton _).mul hb0
  have hbne : span R {c0} * b0 ≠ ⊥ := mul_ne_bot' hsc hb00
  refine ⟨hbfg, hbne, ?_⟩
  have hb1 := mul_one_div_cancel_of_fg hbfg hbne
  have hab : span R {c0} * b0 * (span R {c1} * d0) = a := by
    have : span R {c0} * span R {c1} = 1 := by
      rw [span_mul_span, Set.singleton_mul_singleton, hc, ← Submodule.one_eq_span]
    rw [← hbd]
    calc span R {c0} * b0 * (span R {c1} * d0)
        = (span R {c0} * span R {c1}) * (b0 * d0) := by ring
      _ = b0 * d0 := by rw [this, one_mul]
  have hinv : a * (1 / (span R {c0} * b0)) = span R {c1} * d0 := by
    rw [← hab]
    calc span R {c0} * b0 * (span R {c1} * d0) * (1 / (span R {c0} * b0))
        = (span R {c1} * d0) * (span R {c0} * b0 * (1 / (span R {c0} * b0))) := by ring
      _ = span R {c1} * d0 := by rw [hb1, mul_one]
  rw [hinv, smul_span_smul_max, smul_span_smul_max]

/-- **Corollary 82:21a** (O'Meara 1963, p. 236). Suppose $L$ is a $2\mathfrak a$-maximal lattice on the hyperbolic plane
$V$ and $x$, $y$ span the isotropic lines of $V$ with $B(x, y) = 1$. Then the base $x, y$ is adapted to $L$; in fact
$L = \mathfrak bx + \mathfrak a\mathfrak b^{-1}y$ for a fractional ideal $\mathfrak b$. -/
@[kb "omeara1963" "§82H, 82:21a, p. 236"]
theorem exists_eq_of_isMaximal_hyperbolic {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1)
    (hdim : finrank F V = 2) {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {L : Submodule R V}
    (hL : IsMaximal Q (span R {2} * a) L) :
    ∃ b : Submodule R F, b.FG ∧ b ≠ ⊥ ∧ L = b • span R {x} ⊔ (a * (1 / b)) • span R {y} := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have htf := isTorsionFree_of_fractionRing (R := R) (F := F) (V := V)
  obtain ⟨hli, -⟩ := hyp_pair_li_max Q hx hy hxy
  have hspan : span F (Set.range ![x, y]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [hdim])
  have hV := nondeg_of_hyp_max Q hx hy hxy hspan
  have hx0 : x ≠ 0 := by rintro rfl; simp [bil] at hxy
  have hlat := hL.1
  obtain ⟨d, hd, hdx⟩ := exists_smul_mem_of_mem_span (S := L)
    (by rw [hlat.span_eq_top]; trivial : x ∈ span F (L : Set V))
  have hd' : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hd
  have hx₀L : algebraMap R F d • x ∈ L := by rw [algebraMap_smul]; exact hdx
  have hx₀0 : algebraMap R F d • x ≠ 0 := smul_ne_zero hd' hx0
  have hQx₀ : Q (algebraMap R F d • x) = 0 := by rw [Q_smul, hx, mul_zero]
  obtain ⟨y₀, hQy₀, hxy₀, hbd, hmod, hrk2, K, hK⟩ := hyp_split_max Q hV ha ha0 hL hx₀L hx₀0 hQx₀
  have hLJ := eq_of_isOrthSum_rank_max Q hK hrk2 (by rw [finrank_lattice_max hlat, hdim])
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun F).1
    (hspan ▸ mem_top : y₀ ∈ span F (Set.range ![x, y]))
  rw [Fin.sum_univ_two] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  have hB : bil Q (algebraMap R F d • x) y₀ = algebraMap R F d * c 1 := by
    rw [← hc, bil_add_right, bil_smul_right, bil_smul_right, bil_smul_left, bil_smul_left, bil_self, hx, hxy]
    ring
  have hQ : Q y₀ = 2 * (c 0 * c 1) := by
    rw [← hc, Q_add, Q_smul, Q_smul, hx, hy, bil_smul_left, bil_smul_right, hxy]; ring
  have hcc : algebraMap R F d * c 1 = 1 := hB ▸ hxy₀
  have hc1 : c 1 ≠ 0 := right_ne_zero_of_mul_eq_one hcc
  have hc0 : c 0 = 0 := by
    have h3 : 2 * (c 0 * c 1) = 0 := hQ.symm.trans hQy₀
    exact (mul_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left h2)).resolve_right hc1
  have hy₀ : y₀ = c 1 • y := by rw [← hc, hc0, zero_smul, zero_add]
  obtain ⟨hbfg, hbne, hJeq⟩ := rescale_pair_max (a := a) (b0 := coeff F L (algebraMap R F d • x))
    (d0 := coeff F L y₀) (coeff_fg hlat.fg hx₀0) (coeff_ne_bot (subset_span hx₀L)) hbd hcc x y
  refine ⟨_, hbfg, hbne, ?_⟩
  calc L = coeff F L (algebraMap R F d • x) • span R {algebraMap R F d • x} ⊔
        coeff F L y₀ • span R {y₀} := hLJ
    _ = coeff F L (algebraMap R F d • x) • span R {algebraMap R F d • x} ⊔
        coeff F L y₀ • span R {c 1 • y} := by rw [← hy₀]
    _ = _ := hJeq

/-- A regular space with a non-zero isotropic vector contains an isotropic pair `x, y` with `B(x, y) = 1`. -/
theorem exists_hyp_pair_max (hV : (QuadraticMap.associated Q).Nondegenerate)
    (hiso : ∃ v : V, v ≠ 0 ∧ Q v = 0) : ∃ x y : V, Q x = 0 ∧ Q y = 0 ∧ bil Q x y = 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  obtain ⟨v, hv0, hQv⟩ := hiso
  obtain ⟨w, hw⟩ : ∃ w, bil Q v w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 (hV.1 v fun w => hcon w)
  set B := bil Q v w with hB
  set s : F := Q w / (2 * B) with hs
  have hyp : Q (w - s • v) = 0 := by
    rw [sub_eq_add_neg, ← neg_smul, Q_add, Q_smul, hQv, bil_smul_right, bil_comm Q w v, ← hB, hs]
    field_simp
    ring
  have hvy : bil Q v (w - s • v) = B := by
    rw [bil_sub_right, bil_smul_right, bil_self, hQv, mul_zero, sub_zero]
  refine ⟨v, B⁻¹ • (w - s • v), hQv, ?_, ?_⟩
  · rw [Q_smul, hyp, mul_zero]
  · rw [bil_smul_right, hvy, inv_mul_cancel₀ hw]

/-- `R c • R z = R (c z)`. -/
theorem span_smul_span_singleton_max (c : F) (z : V) : span R {c} • span R {z} = span R {c • z} := by
  have := smul_span_smul_max (R := R) (1 : Submodule R F) c z
  rw [Submodule.one_smul, mul_one] at this
  exact this.symm

/-- Scaling the vectors of a linearly independent pair by non-zero scalars. -/
theorem li_scaled_pair_max {x y : V} (hli : LinearIndependent F ![x, y]) {β γ : F} (hβ : β ≠ 0)
    (hγ : γ ≠ 0) : LinearIndependent F ![β • x, γ • y] := by
  rw [LinearIndependent.pair_iff] at hli ⊢
  intro s t hst
  have := hli (s * β) (t * γ) (by rw [mul_smul, mul_smul]; exact hst)
  exact ⟨(mul_eq_zero.1 this.1).resolve_right hβ, (mul_eq_zero.1 this.2).resolve_right hγ⟩

/-- **Example 82:22** (O'Meara 1963, p. 236). Suppose every fractional ideal is principal and $\alpha \in F^\times$.
A lattice $L$ on the hyperbolic plane $V$ is $2\alpha\mathfrak o$-maximal if and only if
$L \cong \begin{pmatrix} 0 & \alpha \\ \alpha & 0 \end{pmatrix}$, i.e. $L$ has a base with this matrix. Hence any two
$\mathfrak a$-maximal lattices on $V$ are isometric. -/
@[kb "omeara1963" "§82H, 82:22, p. 236"]
theorem isMaximal_iff_gram_of_principal (hP : ∀ a : Submodule R F, a.FG → ∃ α : F, a = span R {α})
    (hV : (QuadraticMap.associated Q).Nondegenerate) (hdim : finrank F V = 2)
    (hiso : ∃ v : V, v ≠ 0 ∧ Q v = 0) {α : F} (hα : α ≠ 0) {L : Submodule R V} (hL : L.IsLattice F) :
    IsMaximal Q (span R {2 * α}) L ↔
      ∃ b : Basis (Fin 2) R L, gram Q (fun i => (b i : V)) = !![0, α; α, 0] := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have ha : (span R {α}).FG := fg_span_singleton α
  have ha0 : span R {α} ≠ ⊥ := fun h0 => hα (span_singleton_eq_bot.1 h0)
  have e2α : span R {(2 : F) * α} = span R {(2 : F)} * span R {α} := by
    rw [span_mul_span, Set.singleton_mul_singleton]
  rw [e2α]
  constructor
  · intro hmax
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_hyp_pair_max Q hV hiso
    obtain ⟨b, hbfg, hb0, hLeq⟩ := exists_eq_of_isMaximal_hyperbolic Q hx hy hxy hdim ha ha0 hmax
    obtain ⟨β, hβ⟩ := hP b hbfg
    have hβ0 : β ≠ 0 := fun h0 => hb0 (by rw [hβ, h0]; simp)
    have e1 : span R {β⁻¹} * b = 1 := by
      rw [hβ, span_mul_span, Set.singleton_mul_singleton, inv_mul_cancel₀ hβ0, ← Submodule.one_eq_span]
    have hb1 := mul_one_div_cancel_of_fg hbfg hb0
    have hinv : 1 / b = span R {β⁻¹} :=
      calc 1 / b = (span R {β⁻¹} * b) * (1 / b) := by rw [e1, one_mul]
        _ = span R {β⁻¹} * (b * (1 / b)) := by ring
        _ = span R {β⁻¹} := by rw [hb1, mul_one]
    have hγ0 : α * β⁻¹ ≠ 0 := mul_ne_zero hα (inv_ne_zero hβ0)
    set v : Fin 2 → V := ![β • x, (α * β⁻¹) • y] with hv
    have hLv : span R (Set.range v) = L := by
      have hr : Set.range v = {β • x, (α * β⁻¹) • y} := by ext w; simp [hv, or_comm]
      rw [hr, Submodule.span_insert, hLeq, hinv, hβ, span_mul_span, Set.singleton_mul_singleton,
        ← span_smul_span_singleton_max, ← span_smul_span_singleton_max]
    have hliF : LinearIndependent F v := li_scaled_pair_max (hyp_pair_li_max Q hx hy hxy).1 hβ0 hγ0
    have hliR : LinearIndependent R v := hliF.restrict_scalars (fun r s h => IsFractionRing.injective R F
      (by simpa [Algebra.smul_def] using h))
    let b' : Basis (Fin 2) R L := (Basis.span hliR).map (LinearEquiv.ofEq _ _ hLv)
    have hb' : ∀ i, ((b' i : L) : V) = v i := fun i => by simp [b']
    refine ⟨b', ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gram, hb', hv, hx, hy, hxy, bil_comm Q y x] <;> field_simp
  · rintro ⟨b, hb⟩
    have h00 := congrFun (congrFun hb 0) 0
    have h01 := congrFun (congrFun hb 0) 1
    have h11 := congrFun (congrFun hb 1) 1
    simp only [gram, Matrix.of_apply] at h00 h01 h11
    simp at h00 h01 h11
    have hx : Q (b 0 : V) = 0 := h00
    have hy : Q (b 1 : V) = 0 := h11
    have hmod : IsModular Q (span R {α}) L := by
      refine (isModular_iff_gram Q b hα).2 ⟨⟨0⟩, !![0, 1; 1, 0], by simp [Matrix.det_fin_two_of], ?_⟩
      rw [hb]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hn : normIdeal Q L ≤ span R {(2 : F)} * span R {α} := by
      rw [normIdeal, span_le]
      rintro _ ⟨l, hl, rfl⟩
      have hl' := congrArg Subtype.val (b.sum_repr ⟨l, hl⟩)
      rw [Fin.sum_univ_two] at hl'
      simp only [Submodule.coe_add, Submodule.coe_smul] at hl'
      show Q l ∈ _
      rw [← hl', Q_add, Q_rsmul, Q_rsmul, hx, hy, bil_rsmul_left, bil_rsmul_right, h01, ← e2α]
      refine mem_span_singleton.2 ⟨b.repr ⟨l, hl⟩ 0 * b.repr ⟨l, hl⟩ 1, ?_⟩
      rw [Algebra.smul_def, map_mul]
      ring
    have := (isMaximal_iff_isModular_of_hyperbolic Q hV hdim hiso ha ha0 hL).2 ⟨hmod, hn⟩
    exact this

/-- Cancellation of `≤` by a fractional ideal. -/
theorem le_of_mul_le_mul_left_max {I J K : Submodule R F} (hI : I.FG) (hI0 : I ≠ ⊥)
    (h : I * J ≤ I * K) : J ≤ K := by
  have h1 := mul_one_div_cancel_of_fg hI hI0
  calc J = (I * (1 / I)) * J := by rw [h1, one_mul]
    _ = (1 / I) * (I * J) := by ring
    _ ≤ (1 / I) * (I * K) := mul_le_mul' le_rfl h
    _ = (I * (1 / I)) * K := by ring
    _ = K := by rw [h1, one_mul]

/-- `J ⊆ I` implies `I⁻¹ ⊆ J⁻¹` for fractional ideals. -/
theorem one_div_antitone_max {I J : Submodule R F} (hI : I.FG) (hI0 : I ≠ ⊥) (hJ : J.FG) (hJ0 : J ≠ ⊥)
    (h : J ≤ I) : 1 / I ≤ 1 / J := by
  have h1 := mul_one_div_cancel_of_fg hI hI0
  have h2 := mul_one_div_cancel_of_fg hJ hJ0
  calc 1 / I = (J * (1 / J)) * (1 / I) := by rw [h2, one_mul]
    _ = (1 / J) * (J * (1 / I)) := by ring
    _ ≤ (1 / J) * (I * (1 / I)) := mul_le_mul' le_rfl (mul_le_mul' h le_rfl)
    _ = 1 / J := by rw [h1, mul_one]

/-- `𝔞_{cv} (cv) = 𝔞_v v`: the lattice `L ∩ Fv` does not depend on the scalar. -/
theorem coeff_smul_span_line_max (M : Submodule R V) (v : V) {c : F} (hc : c ≠ 0) :
    coeff F M (c • v) • span R {c • v} = coeff F M v • span R {v} := by
  rw [coeff_smul_span, coeff_smul_span]
  have : span F {c • v} = span F {v} := Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hc) v
  rw [this]

/-- `𝔞_x 𝔞_y ⊆ 𝔰M` for `B(x, y) = 1`. -/
theorem coeff_mul_le_scale_max (M : Submodule R V) {x y : V} (hxy : bil Q x y = 1) :
    coeff F M x * coeff F M y ≤ scale Q M := by
  rw [Submodule.mul_le]
  intro t ht α hα
  have := bil_mem_scale Q (show t • x ∈ M from ht) (show α • y ∈ M from hα)
  rwa [bil_smul_left, bil_smul_right, hxy, mul_one] at this

/-- The hyperbolic splitting of a `2h`-maximal lattice at an arbitrary isotropic line. -/
theorem hyp_split_line_max (hV : (QuadraticMap.associated Q).Nondegenerate) {h : Submodule R F} (hh : h.FG)
    (hh0 : h ≠ ⊥) {M : Submodule R V} (hM : IsMaximal Q (span R {(2 : F)} * h) M) {x : V} (hx0 : x ≠ 0)
    (hQx : Q x = 0) :
    ∃ y : V, Q y = 0 ∧ bil Q x y = 1 ∧ coeff F M x * coeff F M y = h ∧
      ∃ K', IsOrthSum Q M (coeff F M x • span R {x} ⊔ coeff F M y • span R {y}) K' := by
  have htf := isTorsionFree_of_fractionRing (R := R) (F := F) (V := V)
  obtain ⟨d, hd, hdx⟩ := exists_smul_mem_of_mem_span (S := M)
    (by rw [hM.1.span_eq_top]; trivial : x ∈ span F (M : Set V))
  have hc : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hd
  set c : F := algebraMap R F d with hcdef
  have hxM : c • x ∈ M := by rw [hcdef, algebraMap_smul]; exact hdx
  obtain ⟨y₀, hQy₀, hxy₀, hbd, -, -, K', hK'⟩ := hyp_split_max Q hV hh hh0 hM hxM (smul_ne_zero hc hx0)
    (by rw [Q_smul, hQx, mul_zero])
  have hcx : coeff F M x = span R {c} * coeff F M (c • x) := by
    have := coeff_smul M (c • x) (inv_ne_zero hc)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, inv_inv] at this
    exact this
  have hcy : coeff F M (c • y₀) = span R {c⁻¹} * coeff F M y₀ := coeff_smul M y₀ hc
  refine ⟨c • y₀, by rw [Q_smul, hQy₀, mul_zero], ?_, ?_, K', ?_⟩
  · rw [bil_smul_right, ← hxy₀, bil_smul_left]
  · rw [hcx, hcy]
    calc span R {c} * coeff F M (c • x) * (span R {c⁻¹} * coeff F M y₀)
        = (span R {c} * span R {c⁻¹}) * (coeff F M (c • x) * coeff F M y₀) := by ring
      _ = h := by
        rw [span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ hc, ← Submodule.one_eq_span,
          one_mul, hbd]
  · rw [← coeff_smul_span_line_max M x hc, coeff_smul_span_line_max M y₀ hc]
    exact hK'

/-- The orthogonal complement `{w | B(w, x) = 0 = B(w, y)}` of a pair of vectors. -/
def hypPerp (x y : V) : Submodule F V where
  carrier := {w | bil Q w x = 0 ∧ bil Q w y = 0}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨by rw [bil_add_left, ha1, hb1, add_zero], by rw [bil_add_left, ha2, hb2, add_zero]⟩
  zero_mem' := ⟨by simp [bil], by simp [bil]⟩
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    exact ⟨by rw [bil_smul_left, ha1, mul_zero], by rw [bil_smul_left, ha2, mul_zero]⟩

/-- A hyperbolic pair splits `V` as `span{x, y} ⊥ {x, y}^⊥`. -/
theorem hyp_decomp_max {x y : V} (hQx : Q x = 0) (hQy : Q y = 0) (hxy : bil Q x y = 1) :
    IsOrthSum (R := F) Q ⊤ (span F (Set.range ![x, y])) (hypPerp Q x y) := by
  have hyx : bil Q y x = 1 := by rw [bil_comm]; exact hxy
  have hxx : bil Q x x = 0 := by rw [bil_self, hQx]
  have hyy : bil Q y y = 0 := by rw [bil_self, hQy]
  refine ⟨?_, ?_, ?_⟩
  · intro u hu w hw
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun F).1 hu
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [bil_add_left, bil_smul_left, bil_smul_left, bil_comm Q x w, bil_comm Q y w, hw.1, hw.2]
    ring
  · rw [Submodule.disjoint_def]
    intro z hz hzW
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun F).1 hz
    rw [Fin.sum_univ_two] at hzW ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hzW ⊢
    have h1 := hzW.1
    have h2 := hzW.2
    rw [bil_add_left, bil_smul_left, bil_smul_left, hxx, hyx] at h1
    rw [bil_add_left, bil_smul_left, bil_smul_left, hxy, hyy] at h2
    have hc1 : c 1 = 0 := by simpa using h1
    have hc0 : c 0 = 0 := by simpa using h2
    rw [hc0, hc1]; simp
  · rw [eq_top_iff]
    intro v _
    refine Submodule.mem_sup.2 ⟨bil Q v y • x + bil Q v x • y, add_mem (smul_mem _ _ (subset_span ⟨0, rfl⟩))
      (smul_mem _ _ (subset_span ⟨1, rfl⟩)), v - (bil Q v y • x + bil Q v x • y), ⟨?_, ?_⟩, by abel⟩
    · rw [bil_sub_left, bil_add_left, bil_smul_left, bil_smul_left, hxx, hyx]; ring
    · rw [bil_sub_left, bil_add_left, bil_smul_left, bil_smul_left, hxy, hyy]; ring

/-- If `M = J ⊥ K'` with `J ⊆ U`, `K' ⊆ W` (orthogonal, disjoint), then `M = (M ∩ U) ⊥ (M ∩ W)`. -/
theorem isOrthSum_inf_max {M J K' : Submodule R V} (h : IsOrthSum Q M J K') {U W : Submodule F V}
    (hUW : ∀ u ∈ U, ∀ w ∈ W, bil Q u w = 0) (hdisj : Disjoint U W) (hJU : ∀ j ∈ J, j ∈ U)
    (hKW : ∀ k ∈ K', k ∈ W) :
    IsOrthSum Q M (M ⊓ U.restrictScalars R) (M ⊓ W.restrictScalars R) := by
  refine ⟨fun a ha b hb => hUW a ha.2 b hb.2, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro z hz1 hz2
    exact Submodule.disjoint_def.1 hdisj z hz1.2 hz2.2
  · apply le_antisymm
    · exact sup_le inf_le_left inf_le_left
    · intro m hm
      rw [← h.sup_eq] at hm
      obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.1 hm
      exact add_mem (mem_sup_left ⟨h.sup_eq ▸ mem_sup_left hj, hJU j hj⟩)
        (mem_sup_right ⟨h.sup_eq ▸ mem_sup_right hk, hKW k hk⟩)

/-- Splitting `M = J ⊥ K'` with `J = b x + d y` for a hyperbolic pair gives `M = (M ∩ U) ⊥ (M ∩ W)`. -/
theorem isOrthSum_hyp_max {M J K' : Submodule R V} (h : IsOrthSum Q M J K') {x y : V} (hQx : Q x = 0)
    (hQy : Q y = 0) (hxy : bil Q x y = 1) {b d : Submodule R F} (hb0 : b ≠ ⊥) (hd0 : d ≠ ⊥)
    (hJ : J = b • span R {x} ⊔ d • span R {y}) :
    IsOrthSum Q M (M ⊓ (span F (Set.range ![x, y])).restrictScalars R)
      (M ⊓ (hypPerp Q x y).restrictScalars R) := by
  have hdec := hyp_decomp_max Q hQx hQy hxy
  have hsmul : ∀ (e : Submodule R F) (v : V), v ∈ span F (Set.range ![x, y]) →
      e • span R {v} ≤ (span F (Set.range ![x, y])).restrictScalars R := by
    intro e v hv
    rw [Submodule.smul_le]
    intro α _ n hn
    obtain ⟨r, rfl⟩ := mem_span_singleton.1 hn
    show α • r • v ∈ span F (Set.range ![x, y])
    rw [← algebraMap_smul F r v, smul_smul]
    exact smul_mem _ _ hv
  have hxU : x ∈ span F (Set.range ![x, y]) := subset_span ⟨0, rfl⟩
  have hyU : y ∈ span F (Set.range ![x, y]) := subset_span ⟨1, rfl⟩
  have hspanJ : ∀ (e : Submodule R F) (v : V), e ≠ ⊥ → e • span R {v} ≤ J → v ∈ span F (J : Set V) := by
    intro e v he hle
    obtain ⟨γ, hγ, hγ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot he
    have h1 : γ • v ∈ J := hle (smul_mem_smul hγ (mem_span_singleton_self v))
    rw [show v = γ⁻¹ • (γ • v) by rw [smul_smul, inv_mul_cancel₀ hγ0, one_smul]]
    exact Submodule.smul_mem _ _ (subset_span h1)
  refine isOrthSum_inf_max Q h (fun u hu w hw => hdec.orth u hu w hw) hdec.disjoint ?_ ?_
  · intro j hj
    rw [hJ] at hj
    obtain ⟨j₁, hj₁, j₂, hj₂, rfl⟩ := mem_sup.1 hj
    exact add_mem (hsmul b x hxU hj₁) (hsmul d y hyU hj₂)
  · intro k hk
    have hxJ : x ∈ span F (J : Set V) := hspanJ b x hb0 (by rw [hJ]; exact le_sup_left)
    have hyJ : y ∈ span F (J : Set V) := hspanJ d y hd0 (by rw [hJ]; exact le_sup_right)
    have hk' : ∀ z ∈ J, bil Q k z = 0 := fun z hz => by rw [bil_comm]; exact h.orth z hz k hk
    exact ⟨by rw [bil_comm]; rw [bil_comm]; exact bil_zero_of_mem_span_F Q hk' hxJ,
      by rw [bil_comm]; rw [bil_comm]; exact bil_zero_of_mem_span_F Q hk' hyJ⟩

/-- A non-empty family of submodules of `F` bounded by a finitely generated one has a maximal member. -/
theorem exists_maximal_bounded_max (S : Set (Submodule R F)) (hS : S.Nonempty) {N : Submodule R F}
    (hN : N.FG) (hle : ∀ I ∈ S, I ≤ N) : ∃ I₀ ∈ S, ∀ I ∈ S, I₀ ≤ I → I = I₀ := by
  have : Module.Finite R N := Module.Finite.iff_fg.mpr hN
  let S' : Set (Submodule R N) := {J | J.map N.subtype ∈ S}
  have hS' : S'.Nonempty := by
    obtain ⟨I, hI⟩ := hS
    refine ⟨I.comap N.subtype, ?_⟩
    show (I.comap N.subtype).map N.subtype ∈ S
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr (hle I hI)]
    exact hI
  obtain ⟨J₀, hJ₀, hmax⟩ :=
    (set_has_maximal_iff_noetherian (R := R) (M := N)).mpr inferInstance S' hS'
  refine ⟨J₀.map N.subtype, hJ₀, fun I hI hle' => ?_⟩
  have hmem : I.comap N.subtype ∈ S' := by
    show (I.comap N.subtype).map N.subtype ∈ S
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr (hle I hI)]
    exact hI
  have h1 : J₀ ≤ I.comap N.subtype := Submodule.map_le_iff_le_comap.mp hle'
  have heq : J₀ = I.comap N.subtype := by
    by_contra hne
    exact hmax _ hmem (lt_of_le_of_ne h1 hne)
  rw [heq, Submodule.map_comap_subtype, inf_eq_right.mpr (hle I hI)]

/-- The ratios `𝔟_v 𝔞_v⁻¹` of coefficients of lattices `K`, `L` on `V` lie in a fixed f.g. submodule. -/
theorem rho_le_max {L K : Submodule R V} (hL : L.IsLattice F) (hK : K.IsLattice F) :
    ∃ N : Submodule R F, N.FG ∧ ∀ v : V, v ≠ 0 → coeff F K v * (1 / coeff F L v) ≤ N := by
  obtain ⟨α, hα, hαK⟩ := (fg_iff_exists_smul_le hL K).1 hK.fg
  have hα' : algebraMap R F α ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hα
  refine ⟨span R {(algebraMap R F α)⁻¹}, fg_span_singleton _, fun v hv u hu => ?_⟩
  have hLfg : (coeff F L v).FG := coeff_fg hL.fg hv
  have hLne : coeff F L v ≠ ⊥ := coeff_ne_bot (by rw [hL.span_eq_top]; trivial)
  have hinv := mul_one_div_cancel_of_fg hLfg hLne
  have h1 : span R {algebraMap R F α} * coeff F K v ≤ coeff F L v := by
    rw [Submodule.mul_le]
    intro m hm t ht
    obtain ⟨c, rfl⟩ := mem_span_singleton.1 hm
    show (c • algebraMap R F α * t) • v ∈ L
    have e : (c • algebraMap R F α * t) • v = c • (α • (t • v)) := by
      rw [smul_mul_assoc, smul_assoc, mul_smul, algebraMap_smul]
    rw [e]
    exact L.smul_mem c (hαK _ ht)
  have h2 : algebraMap R F α * u ∈ (1 : Submodule R F) := by
    have : span R {algebraMap R F α} * (coeff F K v * (1 / coeff F L v)) ≤ 1 := by
      calc _ = (span R {algebraMap R F α} * coeff F K v) * (1 / coeff F L v) := by ring
        _ ≤ coeff F L v * (1 / coeff F L v) := mul_le_mul' h1 le_rfl
        _ = 1 := hinv
    exact this (mul_mem_mul (mem_span_singleton_self _) hu)
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 h2
  refine mem_span_singleton.2 ⟨r, ?_⟩
  rw [Algebra.smul_def, hr]
  field_simp

/-- **Proposition 82:23** (O'Meara 1963, pp. 236–237). Let $V$ be an isotropic regular quadratic space and $K$, $L$
maximal lattices on $V$ ($\mathfrak a$- and $\mathfrak b$-maximal; that $\mathfrak a$, $\mathfrak b$ are fractional
ideals is not needed, since an $\mathfrak a$-maximal lattice is $\mathfrak nL$-maximal).
Then there is a splitting $V = U \perp W$ with $U$ a hyperbolic plane such that $L = (L \cap U) \perp (L \cap W)$ and
$K = (K \cap U) \perp (K \cap W)$. -/
@[kb "omeara1963" "§82H, 82:23, pp. 236–237"]
theorem exists_hyperbolic_split_of_isMaximal (hV : (QuadraticMap.associated Q).Nondegenerate)
    (hiso : ∃ v : V, v ≠ 0 ∧ Q v = 0) {a b : Submodule R F} {L K : Submodule R V} (hL : IsMaximal Q a L)
    (hK : IsMaximal Q b K) :
    ∃ U W : Submodule F V, finrank F U = 2 ∧ (∃ u ∈ U, u ≠ 0 ∧ Q u = 0) ∧ IsRegular (R := F) Q U ∧
      IsOrthSum (R := F) Q ⊤ U W ∧
      IsOrthSum Q L (L ⊓ U.restrictScalars R) (L ⊓ W.restrictScalars R) ∧
      IsOrthSum Q K (K ⊓ U.restrictScalars R) (K ⊓ W.restrictScalars R) := by
  have hLlat := hL.1
  have hKlat := hK.1
  obtain ⟨xL, hxL, hxL0, -⟩ := exists_iso_in_lattice_max Q hLlat hiso
  obtain ⟨xK, hxK, hxK0, -⟩ := exists_iso_in_lattice_max Q hKlat hiso
  obtain ⟨hh, hhfg, hh0, hLmax⟩ := exists_half_isMaximal_max Q hV hL hxL hxL0
  obtain ⟨kk, hkfg, hk0, hKmax⟩ := exists_half_isMaximal_max Q hV hK hxK hxK0
  have hcoeffL : ∀ v : V, v ≠ 0 → (coeff F L v).FG ∧ coeff F L v ≠ ⊥ := fun v hv =>
    ⟨coeff_fg hLlat.fg hv, coeff_ne_bot (by rw [hLlat.span_eq_top]; trivial)⟩
  have hcoeffK : ∀ v : V, v ≠ 0 → (coeff F K v).FG ∧ coeff F K v ≠ ⊥ := fun v hv =>
    ⟨coeff_fg hKlat.fg hv, coeff_ne_bot (by rw [hKlat.span_eq_top]; trivial)⟩
  -- choose an isotropic line with maximal `𝔟_x 𝔞_x⁻¹`
  obtain ⟨N, hNfg, hρN⟩ := rho_le_max hLlat hKlat
  let S : Set (Submodule R F) :=
    {I | ∃ v : V, v ≠ 0 ∧ Q v = 0 ∧ I = coeff F K v * (1 / coeff F L v)}
  have hS : S.Nonempty := by
    obtain ⟨v, hv0, hQv⟩ := hiso
    exact ⟨_, v, hv0, hQv, rfl⟩
  obtain ⟨I₀, ⟨x, hx0, hQx, rfl⟩, hmaxI⟩ := exists_maximal_bounded_max S hS hNfg
    (by rintro I ⟨v, hv0, -, rfl⟩; exact hρN v hv0)
  -- the pair `x, y` from `L`, and `z` from `K`
  obtain ⟨y, hQy, hxy, hAxy, K₁, hK₁⟩ := hyp_split_line_max Q hV hhfg hh0 hLmax hx0 hQx
  have hy0 : y ≠ 0 := by rintro rfl; simp [bil] at hxy
  obtain ⟨z, hQz, hyz, hByz, K₂, -⟩ := hyp_split_line_max Q hV hkfg hk0 hKmax hy0 hQy
  have hz0 : z ≠ 0 := by rintro rfl; simp [bil] at hyz
  have hsL : scale Q L ≤ hh := scale_le_of_norm_le_max Q hLmax.2.1
  have hsK : scale Q K ≤ kk := scale_le_of_norm_le_max Q hKmax.2.1
  have h1 : coeff F K x * coeff F K y ≤ kk := (coeff_mul_le_scale_max Q K hxy).trans hsK
  have h2 : coeff F L y * coeff F L z ≤ hh := (coeff_mul_le_scale_max Q L hyz).trans hsL
  have hBxz : coeff F K x ≤ coeff F K z :=
    le_of_mul_le_mul_left_max (hcoeffK y hy0).1 (hcoeffK y hy0).2 (by
      calc coeff F K y * coeff F K x = coeff F K x * coeff F K y := mul_comm _ _
        _ ≤ kk := h1
        _ = coeff F K y * coeff F K z := hByz.symm)
  have hAzx : coeff F L z ≤ coeff F L x :=
    le_of_mul_le_mul_left_max (hcoeffL y hy0).1 (hcoeffL y hy0).2 (by
      calc coeff F L y * coeff F L z ≤ hh := h2
        _ = coeff F L y * coeff F L x := by rw [← hAxy, mul_comm])
  have hinvle := one_div_antitone_max (hcoeffL x hx0).1 (hcoeffL x hx0).2 (hcoeffL z hz0).1
    (hcoeffL z hz0).2 hAzx
  have hρ : coeff F K x * (1 / coeff F L x) ≤ coeff F K z * (1 / coeff F L z) :=
    mul_le_mul' hBxz hinvle
  have heq := hmaxI _ ⟨z, hz0, hQz, rfl⟩ hρ
  obtain ⟨hAzfg, hAzne⟩ := one_div_fg (hcoeffL z hz0).1 (hcoeffL z hz0).2
  have hBzx : coeff F K z ≤ coeff F K x := by
    refine le_of_mul_le_mul_left_max hAzfg hAzne ?_
    calc 1 / coeff F L z * coeff F K z = coeff F K z * (1 / coeff F L z) := mul_comm _ _
      _ = coeff F K x * (1 / coeff F L x) := heq
      _ ≤ coeff F K x * (1 / coeff F L z) := mul_le_mul' le_rfl hinvle
      _ = 1 / coeff F L z * coeff F K x := mul_comm _ _
  have hBxeq : coeff F K x = coeff F K z := le_antisymm hBxz hBzx
  have hBxy : coeff F K x * coeff F K y = kk := by rw [hBxeq, mul_comm, hByz]
  -- splitting of `K` at the pair `x, y`
  have hJKle : coeff F K x • span R {x} ⊔ coeff F K y • span R {y} ≤ K :=
    sup_le ((coeff_smul_span K x).le.trans inf_le_left) ((coeff_smul_span K y).le.trans inf_le_left)
  have hJKfg : (coeff F K x • span R {x} ⊔ coeff F K y • span R {y}).FG :=
    (fg_smul_max (hcoeffK x hx0).1 (fg_span_singleton x)).sup
      (fg_smul_max (hcoeffK y hy0).1 (fg_span_singleton y))
  obtain ⟨hmodK, -⟩ := isModular_hyp_max Q hQx hQy hxy (hcoeffK x hx0).1 (hcoeffK x hx0).2
    (hcoeffK y hy0).1 (hcoeffK y hy0).2 hkfg hk0 hBxy ((scale_mono Q hJKle).trans hsK)
  obtain ⟨K₃, hK₃⟩ := (Dedekind.splits_iff_of_isModular Q hJKle hmodK hJKfg).mpr
    (fun u hu l hl => hsK (bil_mem_scale Q (hJKle hu) hl))
  -- the decomposition of `V`
  have hdec := hyp_decomp_max Q hQx hQy hxy
  have hli := (hyp_pair_li_max Q hQx hQy hxy).1
  refine ⟨span F (Set.range ![x, y]), hypPerp Q x y, ?_, ⟨x, subset_span ⟨0, rfl⟩, hx0, hQx⟩, ?_, hdec,
    isOrthSum_hyp_max Q hK₁ hQx hQy hxy (hcoeffL x hx0).2 (hcoeffL y hy0).2 rfl,
    isOrthSum_hyp_max Q hK₃ hQx hQy hxy (hcoeffK x hx0).2 (hcoeffK y hy0).2 rfl⟩
  · rw [finrank_span_eq_card hli]; simp
  · intro u hu hu0
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun F).1 hu
    rw [Fin.sum_univ_two] at hu0 ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu0 ⊢
    have hyx : bil Q y x = 1 := by rw [bil_comm]; exact hxy
    have hxx : bil Q x x = 0 := by rw [bil_self, hQx]
    have hyy : bil Q y y = 0 := by rw [bil_self, hQy]
    have e1 := hu0 x (subset_span ⟨0, rfl⟩)
    have e2 := hu0 y (subset_span ⟨1, rfl⟩)
    rw [bil_add_left, bil_smul_left, bil_smul_left, hxx, hyx] at e1
    rw [bil_add_left, bil_smul_left, bil_smul_left, hxy, hyy] at e2
    have hc1 : c 1 = 0 := by simpa using e1
    have hc0 : c 0 = 0 := by simpa using e2
    rw [hc0, hc1]; simp

end QuadFormsKB.OMeara
