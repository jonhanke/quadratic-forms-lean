/-
# O'Meara 93:28, sufficiency, steps 4–7 over a general dyadic field: arranging $dK_1 = dL_1$

**Setting** (as in `Sec93FCore8.lean`): $R$ a Henselian discrete valuation ring with finite residue field, fraction
field $F$ of characteristic $0$, $2$ not a unit of $R$, $F$ a local Hilbert field; lattices `Submodule R V`; indices
$0$-based (`Ls 0`, `Ls 1` are O'Meara's $L_1, L_2$). All components have rank $8$ (`Core8`), so $K_1$ contains a
unimodular hyperbolic plane and O'Meara's moves run inside $K$.

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 4–7, pp. 274–275)
* helpers: `exists_alg_of_mem_normGroup` (norm groups of lattices of scale $\subseteq \mathfrak o$ are integral),
  `normGroup_plane_le` ($\mathfrak g\langle A(0,0)\rangle = 2\mathfrak o \subseteq \mathfrak gD$ for unimodular $D$),
  `exists_basis_plane_sum` (a base of $\langle A(0,0)\rangle \perp D$ with discriminant $-dD$);
* `exists_sat_sq`: outside O'Meara's step 8, $K$ has a saturated Jordan splitting $K'$ with $dL_1/dK_1'$ a square of a
  unit and $K_1' = \langle A(0,0)\rangle \perp D'$. In step 5 ($a_1\mathfrak o = 2\mathfrak o$) this holds for the given
  splitting by the Local Square Theorem ($\mathfrak f_1 \subseteq 4\mathfrak p$); in steps 4, 6, 7 one move
  (`CoreMove.move`) with $\gamma\lambda = -f$ (`CoreFactor.exists_factor`) multiplies $dK_1$ by $1 + f$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FCoreMove
import QuadFormsKB.Literature.OMeara.Sec93FCoreFactor

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.CoreGen

section Helpers

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- The norm group of a lattice of scale $\subseteq \mathfrak o$ consists of integers. -/
theorem exists_alg_of_mem_normGroup {M : Submodule R V} (hs : scale Q M ≤ 1) {z : F} (hz : z ∈ normGroup Q M) :
    ∃ r : R, algebraMap R F r = z := by
  obtain ⟨x, hx, c, hc, rfl⟩ := hz
  have h1 : Q x ∈ (1 : Submodule R F) := hs (by rw [← bil_self]; exact bil_mem_scale Q hx hx)
  have h2 : c ∈ (1 : Submodule R F) := hs hc
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp h1
  obtain ⟨d, hd⟩ := Submodule.mem_one.mp h2
  exact ⟨r + 2 * d, by rw [map_add, map_mul, hr, hd, map_ofNat]⟩

/-- **$\mathfrak g\langle A(0,0)\rangle \subseteq \mathfrak gD$** for a unimodular $D$: every element of the norm group of
the plane $\mathfrak ox + \mathfrak oy$ ($Q(x) = Q(y) = 0$, $B(x,y) = 1$, scale $\subseteq \mathfrak o$) lies in
$2\mathfrak o = 2\,\mathfrak sD \subseteq \mathfrak gD$. -/
theorem normGroup_plane_le {x y : V} (hQx : Q x = 0) (hQy : Q y = 0) (hxy : bil Q x y = 1)
    (hP : scale Q (span R {x, y}) ≤ 1) {D : Submodule R V} (hD : scale Q D = 1) :
    normGroup Q (span R {x, y}) ≤ normGroup Q D := by
  rintro _ ⟨z, hz, c, hc, rfl⟩
  obtain ⟨r, s, rfl⟩ := mem_span_pair.mp hz
  have hQz : Q (r • x + s • y) = 2 * (algebraMap R F r * algebraMap R F s) := by
    rw [Q_add, ← algebraMap_smul F r x, ← algebraMap_smul F s y, Q_smul, Q_smul, bil_smul_left, bil_smul_right,
      hQx, hQy, hxy]
    ring
  rw [hQz, ← mul_add]
  refine two_mul_mem_normGroup Q ?_
  rw [hD]
  refine add_mem ?_ (hP hc)
  exact Submodule.mem_one.mpr ⟨r * s, by rw [map_mul]⟩

/-- **A base of $\langle A(0,0)\rangle \perp D$**: if $M = (\mathfrak ox + \mathfrak oy) \perp D$ with $Q(x) = Q(y) = 0$,
$B(x,y) = 1$, then for every base of $D$ there is a base of $M$ (indexed by `Fin 2 ⊕ ι`) with discriminant $-dD$. -/
theorem exists_basis_plane_sum {M D : Submodule R V} {x y : V} (hQx : Q x = 0) (hQy : Q y = 0)
    (hxy : bil Q x y = 1) (h : IsOrthSum Q M (span R {x, y}) D) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bD : Basis ι R D) :
    ∃ e : Basis (Fin 2 ⊕ ι) R M, (gram Q fun i => (e i : V)).det = -(gram Q fun i => (bD i : V)).det := by
  classical
  have hdet : Q x * Q y - bil Q x y ^ 2 ≠ 0 := by rw [hQx, hQy, hxy]; norm_num
  obtain ⟨bP, hbP⟩ := CoreMove.exists_basis_pair (R := R) Q hdet
  obtain ⟨e, he⟩ := Transfer28.exists_basis_isOrthSum Q h bP bD
  refine ⟨e, ?_⟩
  have hfun : (fun s => (e s : V)) = Sum.elim (fun i => (bP i : V)) (fun k => (bD k : V)) := funext he
  rw [hfun, Transfer28.det_gram_sumElim Q h.orth _ _ (fun i => (bP i).2) (fun k => (bD k).2)]
  have hP : (fun i => (bP i : V)) = ![x, y] := funext hbP
  rw [hP, CoreMove.det_gram_pair, hQx, hQy, hxy]
  ring

end Helpers

section Sq

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open Sat93 Suff28 SuffStep SuffMain FundAux FIdealAux

/-- $SqEquivMod\ \{0\}\ (\eta^2)\ 1$ for a unit $\eta$: the ratio is exactly a square of a unit. -/
theorem sqEquivMod_bot_of_eq {z : F} {η : R} (hη : IsUnit η) (hz : z = algebraMap R F η ^ 2) :
    SqEquivMod (⊥ : Submodule R F) z 1 :=
  ⟨⟨η ^ 2, hη.pow 2, by rw [hz, map_pow, mul_one]⟩, η, hη, by rw [hz, one_mul, sub_self]; exact zero_mem _⟩

/-- **Steps 4–7 of the sufficiency: arranging $dK_1 = dL_1$** (O'Meara 1963, §93F, proof of 93:28, sufficiency,
pp. 274–275: "Let us arrange $dK_1 = 1$ … Hence $K_1 \perp K_2$ has a saturated splitting $K_1' \perp K_2'$ in which
$dK_1' = 1$"), in the rank-$8$ situation of `Core8`, outside step 8: either $u_2 = u_1$, $u_2 = u_1 + 1$, or
$\mathfrak s_2 = \mathfrak p$ and $u_2 = u_1 + 2$ (steps 4, 6, 7), or $a_1\mathfrak o = 2\mathfrak o$ and $u_2 > u_1$
. Then $K$ has a saturated Jordan splitting $K'$ with $dL_1/dK_1'$ the square of a unit
(`DiscQuotSqEquivMod` modulo $\{0\}$) and $K_1' = \langle A(0,0)\rangle \perp D'$. Condition (i) gives
$dL_1/dK_1 = \varepsilon^2(1 + f)$ with $f \in \mathfrak f_1$; in step 5, $1 + f$ is a square
(`CoreFactor.fIdeal_le_four_pi`, Local Square Theorem); otherwise $-f = \gamma\lambda$ with $\gamma \in \mathfrak g_2$,
$\lambda \in \mathfrak g_1$ (`CoreFactor.exists_factor`) and the move (`CoreMove.move`) multiplies $dK_1$ by $1 + f$.
Saturation is kept since the move enlarges $\mathfrak gK_2$ and $\mathfrak gD$ only. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 4–7, pp. 274–275 (arranging dK₁ = dL₁)"]
theorem exists_sat_sq (hHil : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R))
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L K : Submodule R V} [L.IsLattice F] [K.IsLattice F] {m : ℕ}
    {Ls Ks : Fin (m + 2) → Submodule R V} {a : Fin (m + 2) → F} (hLs : IsSaturated Q L Ls)
    (hKs : IsSaturated Q K Ks) (hd : ∀ k, finrank R (Ls k) = 8) (hsc : scale Q (Ls 0) = 1)
    (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hC : Cond93 Q L Ls Ks a) {π : R} (hπ : Irreducible π)
    (hcase : (dord hπ (a 1) = dord hπ (a 0) ∨ dord hπ (a 1) = dord hπ (a 0) + 1 ∨
        ∃ τ : F, scale Q (Ls 1) = R ∙ τ ∧ dord hπ τ = 1 ∧ dord hπ (a 1) = dord hπ (a 0) + 2) ∨
      (dord hπ (a 0) = dord hπ (2 : F) ∧ dord hπ (a 0) + 1 ≤ dord hπ (a 1))) :
    ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧ DiscQuotSqEquivMod Q (Ls 0) (Ks' 0) ⊥ ∧
      ∃ x y : V, ∃ D : Submodule R V, Q x = 0 ∧ Q y = 0 ∧ bil Q x y = 1 ∧
        IsOrthSum Q (Ks' 0) (span R {x, y}) D := by
  classical
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hregL := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
  obtain ⟨⟨h0, hTy⟩, haL, -⟩ := id hS
  have hc0 : ∀ k : Fin (m + 2), Fin.cast h0 k = k := fun k => Fin.ext rfl
  have hscK : ∀ k, scale Q (Ks k) = scale Q (Ls k) := fun k => by
    have := (hTy k).2.1; rw [hc0] at this; exact this.symm
  have hrkK : ∀ k, finrank R (Ks k) = 8 := fun k => by
    have := (hTy k).1; rw [hc0] at this; rw [← this]; exact hd k
  have hfund : ∀ k, fundNormGroup Q K Ks k = fundNormGroup Q L Ls k := fun k => by
    have := (hTy k).2.2; rw [hc0] at this; exact this.symm
  have hKle : ∀ k, Ks k ≤ K := fun k => hKs.1.split.iSup_eq ▸ le_iSup Ks k
  have hLle : ∀ k, Ls k ≤ L := fun k => hLs.1.split.iSup_eq ▸ le_iSup Ls k
  have hK0fg : (Ks 0).FG := FG.of_le hKfg (hKle 0)
  have hL0fg : (Ls 0).FG := FG.of_le hLfg (hLle 0)
  have hs0K : scale Q (Ks 0) = 1 := (hscK 0).trans hsc
  have hK0U : IsUnimodular Q (Ks 0) := by have := hKs.1.modular 0; rwa [hs0K] at this
  have hK0reg : IsRegular Q (Ks 0) := hK0U.isRegular Q hK0fg
  have hs1 : scale Q (Ks 1) ≤ 1 := by
    have h := hKs.1.scale_strictAnti (show (0 : Fin (m + 2)) < 1 by simp)
    simp only at h; rw [hs0K] at h; exact h.le
  -- `K₁ = ⟨A(0,0)⟩ ⊥ D` (93:18 (v))
  obtain ⟨x, y, D, hQx, hQy, hxy, hPD⟩ :=
    D18.omeara93_18_v_splitting Q hHil h2p hK0fg hK0U (by rw [hrkK 0]; norm_num)
  have hPle : span R {x, y} ≤ Ks 0 := hPD.sup_eq ▸ le_sup_left
  have hDle : D ≤ Ks 0 := hPD.sup_eq ▸ le_sup_right
  have hDfg : D.FG := FG.of_le hK0fg hDle
  have hPfg : (span R {x, y}).FG := FG.of_le hK0fg hPle
  have hdet2 : Q x * Q y - bil Q x y ^ 2 ≠ 0 := by rw [hQx, hQy, hxy]; norm_num
  obtain ⟨bP, -⟩ := CoreMove.exists_basis_pair (R := R) Q hdet2
  have hrkP : finrank R (span R {x, y}) = 2 := by rw [finrank_eq_card_basis bP]; simp
  have hP0 : span R {x, y} ≠ ⊥ := fun h => by rw [h, finrank_bot] at hrkP; omega
  have hD0 : D ≠ ⊥ := by
    intro h
    have := isOrthSum_finrank Q hPD hK0fg
    rw [h, finrank_bot, hrkP, hrkK 0] at this; omega
  have hDU : IsModular Q 1 D := ((Dedekind.isModular_iff_of_isOrthSum Q hPD hPfg hDfg hP0 hD0).mp hK0U).2
  have hDs : scale Q D = 1 := hDU.2.1
  have hPs : scale Q (span R {x, y}) ≤ 1 := hs0K ▸ scale_mono Q hPle
  -- `𝔤K₁ = 𝔤D`
  have hgK0 : normGroup Q (Ks 0) ≤ normGroup Q D := by
    rw [← hPD.sup_eq, normGroup_sup_of_orth Q hPD.orth]
    exact sup_le (normGroup_plane_le Q hQx hQy hxy hPs hDs) le_rfl
  -- condition (i): `dL₁/dK₁ = ε²(1 + f)`, `f ∈ 𝔣₁`
  obtain ⟨bD⟩ := exists_basis (R := R) (F := F) hDfg
  obtain ⟨e, he⟩ := exists_basis_plane_sum Q hQx hQy hxy hPD bD
  obtain ⟨bL⟩ := exists_basis (R := R) (F := F) hL0fg
  have hdE : (gram Q fun i => (e i : V)).det ≠ 0 := Transfer28.det_gram_ne_zero_of_isRegular Q hK0reg e
  have hL0reg : IsRegular Q (Ls 0) := (hLs.1.modular 0).isRegular Q hL0fg
  have hdL : (gram Q fun i => (bL i : V)).det ≠ 0 := Transfer28.det_gram_ne_zero_of_isRegular Q hL0reg bL
  obtain ⟨h1, -, -⟩ := hC 0 1 (by simp)
  rw [jordanChain_zero Ls 0 rfl, jordanChain_zero Ks 0 rfl] at h1
  obtain ⟨-, ε, hε, hmem⟩ := Transfer28.discQuot_bases Q h1 bL e hdE
  set dL := (gram Q fun i => (bL i : V)).det with hdLdef
  set dE := (gram Q fun i => (e i : V)).det with hdEdef
  set f := fIdeal Q L Ls 0 1 with hfdef
  obtain ⟨εu, rfl⟩ := hε
  have hε0 : algebraMap R F (εu : R) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 εu.ne_zero
  set f0 : F := (dL / dE - 1 * algebraMap R F (εu : R) ^ 2) / algebraMap R F (εu : R) ^ 2 with hf0def
  have hf0 : f0 ∈ f := by
    have : f0 = ((εu⁻¹ : Rˣ) : R) ^ 2 • (dL / dE - 1 * algebraMap R F (εu : R) ^ 2) := by
      rw [Algebra.smul_def, map_pow, map_units_inv, hf0def]; field_simp
    rw [this]; exact f.smul_mem _ hmem
  have hratio : dL / dE = algebraMap R F (εu : R) ^ 2 * (1 + f0) := by
    rw [hf0def]; field_simp; ring
  have h1f0 : 1 + f0 ≠ 0 := by
    intro h; rw [h, mul_zero] at hratio; exact div_ne_zero hdL hdE hratio
  rcases hcase with hcase | ⟨ha2, hu⟩
  · -- steps 4, 6, 7: one move with `γλ = -f₀`
    obtain ⟨γ, hγ, l, hl, hfac⟩ :=
      CoreFactor.exists_factor Q hπ h2p hLfg hregL hLs.1 haL 0 1 (by simp) hsc hcase (neg_mem hf0)
    have hγK : γ ∈ normGroup Q (Ks 1) := by rw [hKs.2 1, hfund 1]; exact hγ
    have hlK : l ∈ normGroup Q D := hgK0 (by rw [hKs.2 0, hfund 0]; exact hl)
    obtain ⟨γ₀, rfl⟩ := exists_alg_of_mem_normGroup Q hs1 hγK
    obtain ⟨l₀, rfl⟩ := exists_alg_of_mem_normGroup Q hDs.le hlK
    obtain ⟨Ks', hJ', hfix, hg1, hscr, x', y', D', hQx', hQy', hxy', hPD', hgD, bD', u, hu, hdet⟩ :=
      CoreMove.move Q hHil h2p hKfg hKs.1 hs0K (by rw [hrkK 0]; norm_num) (by rw [hrkK 1]; norm_num) hPD hQx
        hQy hxy hlK hγK bD
    obtain ⟨e', he'⟩ := exists_basis_plane_sum Q hQx' hQy' hxy' hPD' bD'
    have hfundK : ∀ i, fundNormGroup Q K Ks' i = fundNormGroup Q K Ks i := fun i =>
      fundNormGroup_eq_of_isJordanSplitting hKfg hKs.1 hJ' i i rfl
    refine ⟨Ks', ⟨hJ', fun i => ?_⟩, ?_, x', y', D', hQx', hQy', hxy', hPD'⟩
    · refine le_antisymm (normGroup_le_fundNormGroup Q hKfg hJ' i) ?_
      rw [hfundK i, ← hKs.2 i]
      by_cases hi0 : (i : ℕ) = 0
      · have : i = 0 := Fin.ext hi0
        subst this
        have hD'le : D' ≤ Ks' 0 := hPD'.sup_eq ▸ le_sup_right
        exact hgK0.trans (hgD.trans (normGroup_mono Q hD'le))
      by_cases hi1 : (i : ℕ) = 1
      · have : i = 1 := Fin.ext hi1
        subst this; exact hg1
      · rw [hfix i (by omega)]
    · -- `dL₁ / dK₁' = (ε/u)²`
      have hu0 : algebraMap R F u ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hu.ne_zero
      have hdD : (gram Q fun i => (bD i : V)).det = -dE := by linear_combination he
      have hfac' : 1 - algebraMap R F γ₀ * algebraMap R F l₀ = 1 + f0 := by
        rw [← hfac]; ring
      refine Transfer28.discQuot_of_bases Q bL e' (sqEquivMod_bot_of_eq (η := (εu : R) * ↑hu.unit⁻¹)
        (εu.isUnit.mul (Units.isUnit _)) ?_)
      rw [he', hdet, hfac', hdD, map_mul, map_units_inv, IsUnit.unit_spec]
      have : dL = algebraMap R F (εu : R) ^ 2 * (1 + f0) * dE := by
        rw [← hratio]; field_simp
      rw [show (gram Q fun i => (bL i : V)).det = algebraMap R F (εu : R) ^ 2 * (1 + f0) * dE from this]
      field_simp
  · -- step 5: `𝔣₁ ⊆ 4𝔭`, so `1 + f₀` is a square
    have hle := CoreFactor.fIdeal_le_four_pi Q hπ h2p hLfg hregL hLs.1 haL 0 1 (by simp) hsc ha2 hu
    obtain ⟨μ, hμ, hμe⟩ := CoreFactor.exists_four_mul_of_le Q hπ hle f0 hf0
    obtain ⟨η, hη⟩ := isSquare_one_add_four_mul hμ
    have h4μ : (4 : R) * μ ∈ maximalIdeal R := Ideal.mul_mem_left _ _ hμ
    have hηu : IsUnit η := by
      have h1u : IsUnit (1 + 4 * μ) := by
        have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(4 * μ))
          ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem h4μ))
        rwa [sub_neg_eq_add] at this
      rw [hη] at h1u; exact isUnit_of_mul_isUnit_left h1u
    refine ⟨Ks, hKs, Transfer28.discQuot_of_bases Q bL e (sqEquivMod_bot_of_eq (η := (εu : R) * η)
      (εu.isUnit.mul hηu) ?_), x, y, D, hQx, hQy, hxy, hPD⟩
    rw [show (gram Q fun i => (bL i : V)).det / (gram Q fun i => (e i : V)).det = _ from hratio, hμe]
    have : (1 : F) + 4 * algebraMap R F μ = algebraMap R F η ^ 2 := by
      rw [_root_.sq, ← map_mul, ← hη]; simp [map_ofNat]
    rw [this, map_mul]; ring

/-- **Route (ii)/(iii): $FK_1' \cong FL_1$** (O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 4, 6, 7,
pp. 274–275: "If $\mathfrak w_2 \subset 4\mathfrak w_1^{-1}$, then $\mathfrak f_1 \subset 4a_2\mathfrak w_2^{-1}$ and
condition (ii) holds. Hence in this case we have $FL_1 \cong FK_1$, so $FK_1$ is isotropic"; step 7 with (iii)
instead of (ii)). If $K'$ is any Jordan splitting of $K$ with $dL_1/dK_1'$ the square of a unit and (ii) or (iii)
applies at the first index, then $FK_1'$ contains a totally isotropic subspace of half its dimension (condition (i)–(iii)
hold for $K'$ by `Resplit.cond93_resplit`; then `CoreCases.exists_lagrangian_of_cond` with the modulus $\{0\}$). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 4, 6, 7, pp. 274–275 (condition (ii) or (iii) gives FL₁ ≅ FK₁)"]
theorem route_cond (hHil : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R))
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L K : Submodule R V} [L.IsLattice F] [K.IsLattice F] {m : ℕ}
    {Ls Ks Ks' : Fin (m + 2) → Submodule R V} {a : Fin (m + 2) → F} (hLs : IsSaturated Q L Ls)
    (hKs : IsJordanSplitting Q K Ks) (hKs' : IsJordanSplitting Q K Ks')
    (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hC : Cond93 Q L Ls Ks a)
    (hT : ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls 0 : Set V)) ∧
      finrank R (Ls 0) ≤ 2 * finrank F T)
    (hsq : DiscQuotSqEquivMod Q (Ls 0) (Ks' 0) ⊥)
    (hlt : fIdeal Q L Ls 0 1 < (4 * a 1) • (1 / fundWeight Q L Ls 1) ∨
      fIdeal Q L Ls 0 1 < (4 * a 0) • (1 / fundWeight Q L Ls 0)) :
    ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ks' 0 : Set V)) ∧
      finrank R (Ks' 0) ≤ 2 * finrank F T := by
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hregL := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
  have hL0fg : (Ls 0).FG := FG.of_le hLfg (hLs.1.split.iSup_eq ▸ le_iSup Ls 0)
  have hK0fg : (Ks' 0).FG := FG.of_le hKfg (hKs'.split.iSup_eq ▸ le_iSup Ks' 0)
  have hL0reg : IsRegular Q (Ls 0) := (hLs.1.modular 0).isRegular Q hL0fg
  have hK0reg : IsRegular Q (Ks' 0) := (hKs'.modular 0).isRegular Q hK0fg
  have hC' := Resplit.cond93_resplit Q hHil h2p hQ hLs.1 hKs hKs' hS hC
  have hS' := sameFund_resplit Q hKfg hKs hKs' hS
  obtain ⟨⟨h0, hTy⟩, -, -⟩ := id hS'
  have hc : Fin.cast h0 0 = 0 := Fin.ext (by simp)
  have hrk : finrank R (Ls 0) = finrank R (Ks' 0) := by have := (hTy 0).1; rwa [hc] at this
  have ha0 : ∀ k, a k ≠ 0 := fun k =>
    (hS.2.1 k).ne_zero Q (isRegular_fundSub Q hLfg hregL hLs.1 k) (fundSub_ne_bot Q hLfg hLs.1 k)
  obtain ⟨-, h2, h3⟩ := hC' 0 1 (by simp)
  rw [jordanChain_zero Ls 0 rfl, jordanChain_zero Ks' 0 rfl] at h2 h3
  have hX : ∀ x ∈ (⊥ : Submodule R F), ∃ m ∈ maximalIdeal R, x = 4 * algebraMap R F m := fun x hx =>
    ⟨0, zero_mem _, by rw [(Submodule.mem_bot R).mp hx, map_zero, mul_zero]⟩
  rcases hlt with hlt | hlt
  · exact CoreCases.exists_lagrangian_of_cond Q hL0fg hK0fg hL0reg hK0reg hrk hX hsq (ha0 1) (h2 hlt) hT
  · exact CoreCases.exists_lagrangian_of_cond Q hL0fg hK0fg hL0reg hK0reg hrk hX hsq (ha0 0) (h3 hlt) hT

/-- **O'Meara's case distinction in steps 4–8** (O'Meara 1963, §93F, proof of 93:28, sufficiency, pp. 274–275), with
$\mathfrak s_1 = \mathfrak o$, $u_i = \operatorname{ord} a_i$, $e = \operatorname{ord} 2$: either one of steps 4–7
applies ($u_2 = u_1$; $u_2 = u_1 + 1$; $\mathfrak s_2 = \mathfrak p$ and $u_2 = u_1 + 2$; or $u_1 = e$ and
$u_2 > u_1$), or we are in step 8: $u_1 < e$ (i.e. $a_1\mathfrak o \supsetneq 2\mathfrak o$), $u_2 \ge u_1 + 2$ and
$\mathfrak s_2 \subseteq \mathfrak p^2$. Uses $u_1 \le u_2$ (93:27), $u_1 \le e$ ($2\mathfrak s_1 \subseteq
\mathfrak n_1$) and $u_2 \le u_1 + 2$ when $\mathfrak s_2 = \mathfrak p$ (`CoreFactor.dord_le_add_two`). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 4–8, pp. 274–275 (the case distinction)"]
theorem case_split {π : R} (hπ : Irreducible π) {L : Submodule R V} (hfg : L.FG) {t : ℕ}
    {Ls : Fin (t + 2) → Submodule R V} (hJ : IsJordanSplitting Q L Ls) {a : Fin (t + 2) → F}
    (ha : IsFundNormGenerators Q L Ls a) (hs : scale Q (Ls 0) = 1) :
    ((dord hπ (a 1) = dord hπ (a 0) ∨ dord hπ (a 1) = dord hπ (a 0) + 1 ∨
        ∃ τ : F, scale Q (Ls 1) = R ∙ τ ∧ dord hπ τ = 1 ∧ dord hπ (a 1) = dord hπ (a 0) + 2) ∨
      (dord hπ (a 0) = dord hπ (2 : F) ∧ dord hπ (a 0) + 1 ≤ dord hπ (a 1))) ∨
    (dord hπ (a 0) < dord hπ (2 : F) ∧ dord hπ (a 0) + 2 ≤ dord hπ (a 1) ∧
      ∃ τ : F, scale Q (Ls 1) = R ∙ τ ∧ 2 ≤ dord hπ τ) := by
  have h01 := dord_fundNormGenerator_le Q hπ hfg hJ ha (show (0 : Fin (t + 2)) ≤ 1 by simp [Fin.le_def])
  have hai := fundNormGenerator_ne_zero Q hfg hJ ha 0
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  -- `u₁ ≤ e`: `2 = 2 · 1 ∈ 2𝔰₁ ⊆ 𝔫₁ = a₁𝔬`
  have h2e : dord hπ (a 0) ≤ dord hπ (2 : F) := by
    have h1 : (1 : F) ∈ scale Q (fundSub Q L Ls 0) := by
      rw [scale_fundSub Q hfg hJ 0, hs]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
    have h2 : (2 : F) ∈ R ∙ a 0 := by
      rw [(ha 0).2]
      refine (weight_bounds Q _).2.2.2 ((weight_bounds Q _).2.2.1 ?_)
      simpa using Submodule.smul_mem_pointwise_smul (1 : F) (2 : F) _ h1
    exact (mem_span_iff hπ h2F hai).1 h2
  -- the scale of `L₂`
  have hLle : Ls 1 ≤ L := hJ.split.iSup_eq ▸ le_iSup Ls 1
  obtain ⟨τ, hτ0, hτ⟩ := exists_eq_span_singleton (R := R) (scale_fg Q (FG.of_le hfg hLle)) (hJ.modular 1).1
  have hτ1 : 1 ≤ dord hπ τ := by
    have hlt := hJ.scale_strictAnti (show (0 : Fin (t + 2)) < 1 by simp)
    simp only at hlt
    rw [hs, hτ] at hlt
    by_contra hc
    push Not at hc
    have h1 : (1 : F) ∈ R ∙ τ := (mem_span_iff hπ one_ne_zero hτ0).2 (by rw [CoreFactor.dord_one Q hπ]; omega)
    exact hlt.not_ge (by
      rw [Submodule.one_eq_span, span_singleton_le_iff_mem]; exact h1)
  by_cases hu0 : dord hπ (a 1) = dord hπ (a 0)
  · exact Or.inl (Or.inl (Or.inl hu0))
  by_cases he : dord hπ (a 0) = dord hπ (2 : F)
  · exact Or.inl (Or.inr ⟨he, by omega⟩)
  by_cases hu1 : dord hπ (a 1) = dord hπ (a 0) + 1
  · exact Or.inl (Or.inl (Or.inr (Or.inl hu1)))
  by_cases hτe : dord hπ τ = 1
  · have := CoreFactor.dord_le_add_two Q hπ hfg hJ ha hs hτ hτe
    exact Or.inl (Or.inl (Or.inr (Or.inr ⟨τ, hτ, hτe, by omega⟩)))
  · exact Or.inr ⟨by omega, by omega, τ, hτ, by omega⟩

end Sq

end QuadFormsKB.OMeara.CoreGen
