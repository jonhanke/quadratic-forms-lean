/-
# Hanke 2013, §2.2: discriminant modules

J. Hanke, *Algorithms for computing maximal lattices in bilinear (and quadratic) spaces over number fields*,
Contemp. Math. 587 (2013); source used: arXiv:1208.2481v3 (bib key `hanke2013algorithms`).

**Setting** as in `Duality.lean`: $R$ a Dedekind domain with fraction field $F$ (for a number field, $R = \mathcal O_F$),
$2 \in F^\times$, the bilinear space $(V, B)$ given by $Q = Q_B$ with $B$ = `bil Q`, $\mathfrak a$ an $R$-submodule of
$F$ (a non-zero fractional ideal in the paper) and $L$ an $R$-submodule of $V$.

**Defines** the $\mathfrak a$-discriminant module $D_{\mathfrak a}(L) = L^{\#\mathfrak a}/L$ (`DiscModule`; the
quotient of $L^{\#\mathfrak a}$ by $L \cap L^{\#\mathfrak a}$, which is $L$ when $L$ is $\mathfrak a$-valued) with its
$F/\mathfrak a$-valued bilinear form $\widetilde B$ (`discForm`, **Definition 2.10**), and isotropic submodules
(`IsIsotropicSub`: $\widetilde B(N, N) = 0$).

**Proves** **Lemma 2.11** (`lemma_2_11`, non-degeneracy of $\widetilde B$), **Lemma 2.12** (`lemma_2_12`, an order
isomorphism between the $\mathfrak a$-valued $L' \supseteq L$ and the isotropic submodules of $D_{\mathfrak a}(L)$) and
**Lemma 2.13** (`lemma_2_13`, $|D_{\mathfrak a}(L')| = [L : L']^2|D_{\mathfrak a}(L)|$), unconditionally, together
with the duality of indices $[L'^{\#\mathfrak a} : L^{\#\mathfrak a}] = [L : L']$ used in its proof
(`latIndex_aDual`).
-/
import QuadFormsKB.Literature.Hanke2013Algorithms.Duality

open QuadraticMap Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2013Algorithms

open QuadFormsKB.OMeara

section Defs

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- $L \cap L^{\#\mathfrak a}$ as a submodule of $L^{\#\mathfrak a}$ (it is $L$ when $L$ is $\mathfrak a$-valued,
Lemma 2.2). -/
def latIn (a : Submodule R F) (L : Submodule R V) : Submodule R (aDual Q a L) :=
  L.comap (aDual Q a L).subtype

/-- **The $\mathfrak a$-discriminant module** $D_{\mathfrak a}(L) = L^{\#\mathfrak a}/L$ (Hanke 2013,
Definition 2.10, p. 6), as the quotient of $L^{\#\mathfrak a}$ by `latIn Q a L`. -/
@[kb "hanke2013algorithms" "Definition 2.10, p. 6 (D_a(L) = L^{#a}/L)"]
abbrev DiscModule (a : Submodule R F) (L : Submodule R V) : Type _ :=
  aDual Q a L ⧸ latIn Q a L

/-- The bilinear map $L^{\#\mathfrak a} \times L^{\#\mathfrak a} \to F/\mathfrak a$,
$(x, y) \mapsto B(x, y) + \mathfrak a$. -/
def discPre (a : Submodule R F) (L : Submodule R V) : aDual Q a L →ₗ[R] aDual Q a L →ₗ[R] F ⧸ a :=
  LinearMap.mk₂ R (fun x y => a.mkQ (bil Q (x : V) (y : V)))
    (fun x x' y => by simp only [Submodule.coe_add, bil_add_left, map_add])
    (fun c x y => by rw [Submodule.coe_smul, bil_rsmul_left, ← Algebra.smul_def, map_smul])
    (fun x y y' => by simp only [Submodule.coe_add, bil_add_right, map_add])
    (fun c x y => by rw [Submodule.coe_smul, bil_rsmul_right, ← Algebra.smul_def, map_smul])

theorem discPre_apply (a : Submodule R F) (L : Submodule R V) (x y : aDual Q a L) :
    discPre Q a L x y = a.mkQ (bil Q (x : V) (y : V)) := rfl

theorem latIn_le_ker (a : Submodule R F) (L : Submodule R V) :
    latIn Q a L ≤ LinearMap.ker (discPre Q a L) := by
  intro x hx
  rw [LinearMap.mem_ker]
  ext y
  rw [discPre_apply, LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact bil_mem_of_mem_aDual_left Q y.2 hx

theorem latIn_le_ker_flip (a : Submodule R F) (L : Submodule R V) :
    latIn Q a L ≤ LinearMap.ker (discPre Q a L).flip := by
  intro y hy
  rw [LinearMap.mem_ker]
  ext x
  rw [LinearMap.flip_apply, discPre_apply, LinearMap.zero_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact x.2 _ hy

/-- **The discriminant form** $\widetilde B(x + L, y + L) := B(x, y) + \mathfrak a$ on $D_{\mathfrak a}(L)$, with
values in $F/\mathfrak a$ (Hanke 2013, Definition 2.10, p. 6). -/
@[kb "hanke2013algorithms" "Definition 2.10, p. 6 (the F/a-valued form on D_a(L))"]
def discForm (a : Submodule R F) (L : Submodule R V) :
    DiscModule Q a L →ₗ[R] DiscModule Q a L →ₗ[R] F ⧸ a :=
  (discPre Q a L).liftQ₂ (latIn Q a L) (latIn Q a L) (latIn_le_ker Q a L) (latIn_le_ker_flip Q a L)

@[simp]
theorem discForm_mk (a : Submodule R F) (L : Submodule R V) (x y : aDual Q a L) :
    discForm Q a L (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = a.mkQ (bil Q (x : V) (y : V)) := rfl

/-- **Isotropic submodule** of the discriminant module (Hanke 2013, Lemma 2.12, p. 6): $\widetilde B(N, N) = 0$. -/
@[kb "hanke2013algorithms" "Lemma 2.12, p. 6 (isotropic submodules of D_a(L))"]
def IsIsotropicSub {a : Submodule R F} {L : Submodule R V} (N : Submodule R (DiscModule Q a L)) : Prop :=
  ∀ x ∈ N, ∀ y ∈ N, discForm Q a L x y = 0

/-- The submodule $L'/L$ of $D_{\mathfrak a}(L)$ attached to $L' \supseteq L$. -/
def toDisc (a : Submodule R F) (L L' : Submodule R V) : Submodule R (DiscModule Q a L) :=
  (L'.comap (aDual Q a L).subtype).map (latIn Q a L).mkQ

/-- The submodule of $V$ attached to a submodule $N$ of $D_{\mathfrak a}(L)$: the preimage of $N$ in
$L^{\#\mathfrak a}$. -/
def ofDisc {a : Submodule R F} {L : Submodule R V} (N : Submodule R (DiscModule Q a L)) : Submodule R V :=
  (N.comap (latIn Q a L).mkQ).map (aDual Q a L).subtype

theorem toDisc_ofDisc {a : Submodule R F} {L : Submodule R V} (N : Submodule R (DiscModule Q a L)) :
    toDisc Q a L (ofDisc Q N) = N := by
  rw [toDisc, ofDisc, Submodule.comap_map_eq_of_injective (aDual Q a L).injective_subtype,
    Submodule.map_comap_eq_of_surjective (latIn Q a L).mkQ_surjective]

theorem ofDisc_toDisc {a : Submodule R F} {L L' : Submodule R V} (hval : IsAValued Q a L) (hLL' : L ≤ L')
    (hL' : IsAValued Q a L') : ofDisc Q (toDisc Q a L L') = L' := by
  have h1 : L' ≤ aDual Q a L := ((lemma_2_2 Q).1 hL').trans (aDual_anti Q hLL')
  have h2 : latIn Q a L ≤ L'.comap (aDual Q a L).subtype := Submodule.comap_mono hLL'
  rw [toDisc, ofDisc, Submodule.comap_map_mkQ, sup_eq_right.2 h2, Submodule.map_comap_subtype,
    inf_eq_right.2 h1]

theorem isIsotropicSub_toDisc {a : Submodule R F} {L L' : Submodule R V} (hL' : IsAValued Q a L') :
    IsIsotropicSub Q (toDisc Q a L L') := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, discForm_mk, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact hL' (bil_mem_scale Q hx hy)

theorem le_ofDisc {a : Submodule R F} {L : Submodule R V} (hval : IsAValued Q a L)
    (N : Submodule R (DiscModule Q a L)) : L ≤ ofDisc Q N := by
  intro x hx
  refine ⟨⟨x, (lemma_2_2 Q).1 hval hx⟩, ?_, rfl⟩
  show Submodule.Quotient.mk _ ∈ N
  convert N.zero_mem
  exact (Submodule.Quotient.mk_eq_zero _).2 hx

theorem isAValued_ofDisc {a : Submodule R F} {L : Submodule R V} {N : Submodule R (DiscModule Q a L)}
    (hN : IsIsotropicSub Q N) : IsAValued Q a (ofDisc Q N) := by
  rw [lemma_2_2]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have := hN _ hx _ hy
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, discForm_mk, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at this
  exact this

/-- **Lemma 2.12** (Hanke 2013, p. 6): for an $\mathfrak a$-valued $L$, $L' \mapsto L'/L$ is an inclusion-preserving
bijection (an order isomorphism) between the $\mathfrak a$-valued $R$-modules $L' \supseteq L$ in $V$ and the
isotropic submodules of $(D_{\mathfrak a}(L), \widetilde B)$; its inverse takes $N$ to its preimage in
$L^{\#\mathfrak a}$ (`ofDisc`). The paper states it for $L \subsetneq L'$ and (implicitly non-zero) isotropic
submodules; here $L' = L$ corresponds to $N = 0$ (`lemma_2_12_eq_bot_iff`). No non-degeneracy, lattice or
fractional-ideal hypothesis is needed (each such $L'$ lies in $L^{\#\mathfrak a}$, so it is a lattice when $L$ is a
lattice in a non-degenerate space). -/
@[kb "hanke2013algorithms" "Lemma 2.12, p. 6"]
def lemma_2_12 {a : Submodule R F} {L : Submodule R V} (hval : IsAValued Q a L) :
    {L' : Submodule R V // L ≤ L' ∧ IsAValued Q a L'} ≃o
      {N : Submodule R (DiscModule Q a L) // IsIsotropicSub Q N} :=
  Equiv.toOrderIso
    { toFun := fun L' => ⟨toDisc Q a L L'.1, isIsotropicSub_toDisc Q L'.2.2⟩
      invFun := fun N => ⟨ofDisc Q N.1, le_ofDisc Q hval N.1, isAValued_ofDisc Q N.2⟩
      left_inv := fun L' => Subtype.ext (ofDisc_toDisc Q hval L'.2.1 L'.2.2)
      right_inv := fun N => Subtype.ext (toDisc_ofDisc Q N.1) }
    (fun _ _ h => Submodule.map_mono (Submodule.comap_mono h))
    (fun _ _ h => Submodule.map_mono (Submodule.comap_mono h))

theorem lemma_2_12_apply {a : Submodule R F} {L : Submodule R V} (hval : IsAValued Q a L)
    (L' : {L' : Submodule R V // L ≤ L' ∧ IsAValued Q a L'}) :
    (lemma_2_12 Q hval L').1 = toDisc Q a L L'.1 := rfl

/-- **Lemma 2.12, strict version** (Hanke 2013, p. 6): $L'/L = 0$ if and only if $L' = L$; so the
$\mathfrak a$-valued $L' \supsetneq L$ correspond to the non-zero isotropic submodules. -/
@[kb "hanke2013algorithms" "Lemma 2.12, p. 6 (L ⊊ L' ↔ non-zero submodules)"]
theorem lemma_2_12_eq_bot_iff {a : Submodule R F} {L : Submodule R V} (hval : IsAValued Q a L)
    (L' : {L' : Submodule R V // L ≤ L' ∧ IsAValued Q a L'}) :
    (lemma_2_12 Q hval L').1 = ⊥ ↔ L'.1 = L := by
  rw [lemma_2_12_apply]
  constructor
  · intro h
    have := ofDisc_toDisc Q hval L'.2.1 L'.2.2
    rw [h] at this
    rw [← this]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero (latIn Q a L)).1 ((Submodule.mem_bot R).1 (Submodule.mem_comap.1 hx))
    · exact le_ofDisc Q hval ⊥
  · intro h
    rw [toDisc, h]
    exact Submodule.mkQ_map_self _

end Defs

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **Lemma 2.11** (Hanke 2013, p. 6): for a lattice $L$ in a non-degenerate space and a non-zero fractional ideal
$\mathfrak a$, the form $\widetilde B$ on $D_{\mathfrak a}(L)$ is non-degenerate: if $\widetilde B(x, y) = 0$ for all
$y$ then $x = 0$. (The paper assumes $L$ $\mathfrak a$-valued; this is not needed. *Erratum:* the proof's
"$B(v, L^{\#\mathfrak a}) \in \mathcal O_F$" should read "$B(v, L^{\#\mathfrak a}) \subseteq \mathfrak a$".) -/
@[kb "hanke2013algorithms" "Lemma 2.11, p. 6"]
theorem lemma_2_11 (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) (x : DiscModule Q a L)
    (hx : ∀ y, discForm Q a L x y = 0) : x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [Submodule.Quotient.mk_eq_zero]
    show (v : V) ∈ L
    suffices h : (v : V) ∈ aDual Q a (aDual Q a L) by rwa [lemma_2_4 Q hV ha ha0 hL] at h
    intro w hw
    have := hx (Submodule.Quotient.mk ⟨w, hw⟩)
    rwa [discForm_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

end Dedekind

section Index

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- The index $[M : K] := [M : K \cap M]$ of $R$-submodules of $V$ (Mathlib's `AddSubgroup.relIndex`; it is $0$ when
infinite). -/
abbrev latIndex (K M : Submodule R V) : ℕ :=
  K.toAddSubgroup.relIndex M.toAddSubgroup

theorem card_discModule (a : Submodule R F) (L : Submodule R V) :
    Nat.card (DiscModule Q a L) = latIndex L (aDual Q a L) := rfl

/-- Lemma 2.13 from a given duality of indices $[L'^{\#\mathfrak a} : L^{\#\mathfrak a}] = [L : L']$ (which holds for
lattices in a non-degenerate space, `latIndex_aDual`; see `lemma_2_13`). -/
theorem lemma_2_13_of_index {a : Submodule R F} {L L' : Submodule R V} (hval : IsAValued Q a L) (hLL' : L' ≤ L)
    (hdual : latIndex (aDual Q a L) (aDual Q a L') = latIndex L' L) :
    Nat.card (DiscModule Q a L') = latIndex L' L ^ 2 * Nat.card (DiscModule Q a L) := by
  have h1 : L ≤ aDual Q a L := (lemma_2_2 Q).1 hval
  have h2 : aDual Q a L ≤ aDual Q a L' := aDual_anti Q hLL'
  rw [card_discModule, card_discModule]
  have e1 := AddSubgroup.relIndex_mul_relIndex L'.toAddSubgroup L.toAddSubgroup
    (aDual Q a L').toAddSubgroup hLL' (h1.trans h2)
  have e2 := AddSubgroup.relIndex_mul_relIndex L.toAddSubgroup (aDual Q a L).toAddSubgroup
    (aDual Q a L').toAddSubgroup h1 h2
  simp only [latIndex] at hdual ⊢
  rw [← e1, ← e2, hdual]
  ring

end Index

section IndexDuality

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- An $R$-submodule between two lattices is a lattice. -/
theorem isLattice_of_le_of_le {L' N L : Submodule R V} (hL' : L'.IsLattice F) (hL : L.IsLattice F)
    (h1 : L' ≤ N) (h2 : N ≤ L) : N.IsLattice F := by
  have := hL'
  have : IsNoetherian R L := isNoetherian_of_fg_of_noetherian L hL.fg
  have hfg : (N.comap L.subtype).FG := IsNoetherian.noetherian _
  have hN : N = (N.comap L.subtype).map L.subtype := by
    rw [Submodule.map_comap_subtype, inf_eq_right.2 h2]
  have hfg' : N.FG := by rw [hN]; exact hfg.map _
  exact Submodule.IsLattice.of_le_of_isLattice_of_fg F h1 hfg'

/-- The $\mathfrak a$-dual is strictly order-reversing on lattices in a non-degenerate space. -/
theorem aDual_lt_aDual (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) {M L : Submodule R V} (hM : M.IsLattice F) (hL : L.IsLattice F) (h : M < L) :
    aDual Q a L < aDual Q a M := by
  refine lt_of_le_of_ne (aDual_anti Q h.le) fun he => h.ne ?_
  rw [← lemma_2_4 Q hV ha ha0 hM, ← lemma_2_4 Q hV ha ha0 hL, he]

/-- The $\mathfrak a$-dual reverses covering relations between lattices in a non-degenerate space: if
$M \subsetneq L$ with no submodule strictly in between, then the same holds for
$L^{\#\mathfrak a} \subsetneq M^{\#\mathfrak a}$. -/
theorem aDual_covBy (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) {M L : Submodule R V} (hM : M.IsLattice F) (hL : L.IsLattice F) (h : M ⋖ L) :
    aDual Q a L ⋖ aDual Q a M := by
  refine ⟨aDual_lt_aDual Q hV ha ha0 hM hL h.lt, fun N h1 h2 => ?_⟩
  have hLd := isLattice_aDual Q hV ha ha0 hL
  have hMd := isLattice_aDual Q hV ha ha0 hM
  have hN := isLattice_of_le_of_le hLd hMd h1.le h2.le
  have k1 := aDual_lt_aDual Q hV ha ha0 hLd hN h1
  have k2 := aDual_lt_aDual Q hV ha ha0 hN hMd h2
  rw [lemma_2_4 Q hV ha ha0 hL] at k1
  rw [lemma_2_4 Q hV ha ha0 hM] at k2
  exact h.2 k2 k1

/-- If $r$ maps $L$ into $M$ then $r$ maps $M^{\#\mathfrak a}$ into $L^{\#\mathfrak a}$. -/
theorem smul_mem_aDual_of_smul_le {a : Submodule R F} {M L : Submodule R V} {r : R}
    (hr : ∀ x ∈ L, r • x ∈ M) {v : V} (hv : v ∈ aDual Q a M) : r • v ∈ aDual Q a L := by
  intro y hy
  have h := hv _ (hr y hy)
  rw [bil_rsmul_right] at h
  rwa [bil_rsmul_left]

/-- The subquotient $L/M$ (the quotient of $L$ by $M \cap L$) as an $R$-module. -/
abbrev SubQuot (M L : Submodule R V) : Type _ := L ⧸ M.comap L.subtype

theorem mem_annihilator_subQuot {M L : Submodule R V} {r : R} :
    r ∈ Module.annihilator R (SubQuot M L) ↔ ∀ x ∈ L, r • x ∈ M := by
  rw [Module.mem_annihilator]
  constructor
  · intro h x hx
    have := h (Submodule.Quotient.mk ⟨x, hx⟩)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    exact this
  · intro h q
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact h x.1 x.2

/-- A simple step $M \lessdot L$ between lattices and its dual step $L^{\#\mathfrak a} \lessdot M^{\#\mathfrak a}$
have the same index (both quotients are $\cong R/\mathfrak m$ for the same maximal ideal $\mathfrak m$). -/
theorem latIndex_aDual_of_covBy (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F}
    (ha : a.FG) (ha0 : a ≠ ⊥) {M L : Submodule R V} (hM : M.IsLattice F) (hL : L.IsLattice F) (h : M ⋖ L) :
    latIndex (aDual Q a L) (aDual Q a M) = latIndex M L := by
  have hd := aDual_covBy Q hV ha ha0 hM hL h
  have s1 := (covBy_iff_quot_is_simple h.le).1 h
  have s2 := (covBy_iff_quot_is_simple hd.le).1 hd
  obtain ⟨I, hI, ⟨e1⟩⟩ := isSimpleModule_iff_quot_maximal.1 s1
  obtain ⟨J, hJ, ⟨e2⟩⟩ := isSimpleModule_iff_quot_maximal.1 s2
  have aI : Module.annihilator R (SubQuot M L) = I := by
    rw [e1.annihilator_eq, Ideal.annihilator_quotient]
  have aJ : Module.annihilator R (SubQuot (aDual Q a L) (aDual Q a M)) = J := by
    rw [e2.annihilator_eq, Ideal.annihilator_quotient]
  have hIJ : I ≤ J := by
    intro r hr
    rw [← aI, mem_annihilator_subQuot] at hr
    rw [← aJ, mem_annihilator_subQuot]
    intro v hv
    exact smul_mem_aDual_of_smul_le Q hr hv
  have hIJ' : I = J := hI.eq_of_le hJ.ne_top hIJ
  subst hIJ'
  show Nat.card (SubQuot (aDual Q a L) (aDual Q a M)) = Nat.card (SubQuot M L)
  rw [Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv]

/-- The duality of indices for finite index, by induction along a chain of simple steps. -/
theorem latIndex_aDual_of_ne_zero (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F}
    (ha : a.FG) (ha0 : a ≠ ⊥) : ∀ (k : ℕ) {L L' : Submodule R V}, L.IsLattice F → L'.IsLattice F → L' ≤ L →
      latIndex L' L = k → k ≠ 0 →
      latIndex (aDual Q a L) (aDual Q a L') = latIndex L' L := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro L L' hL hL' hLL' hk hk0
  rcases eq_or_lt_of_le hLL' with h | h
  · subst h
    simp [latIndex, AddSubgroup.relIndex_self]
  · -- a submodule `M` with `L' ≤ M ⋖ L`
    have : Module.Finite R L := Module.Finite.iff_fg.2 hL.fg
    have hK : L'.comap L.subtype ≠ ⊤ := by
      intro hK
      apply h.ne
      apply le_antisymm hLL'
      intro x hx
      have : (⟨x, hx⟩ : L) ∈ L'.comap L.subtype := hK ▸ Submodule.mem_top
      exact this
    obtain ⟨K', hK', hKK'⟩ := (eq_top_or_exists_le_coatom (L'.comap L.subtype)).resolve_left hK
    set M := K'.map L.subtype with hMdef
    have hMK : M.comap L.subtype = K' :=
      Submodule.comap_map_eq_of_injective L.injective_subtype K'
    have hML : M ≤ L := Submodule.map_subtype_le L K'
    have hL'M : L' ≤ M := by
      intro x hx
      exact ⟨⟨x, hLL' hx⟩, hKK' hx, rfl⟩
    have hcov : M ⋖ L := by
      rw [covBy_iff_quot_is_simple hML, hMK, isSimpleModule_iff_isCoatom]
      exact hK'
    have hM := isLattice_of_le_of_le hL' hL hL'M hML
    have hMd := isLattice_aDual Q hV ha ha0 hM
    have e1 := AddSubgroup.relIndex_mul_relIndex L'.toAddSubgroup M.toAddSubgroup L.toAddSubgroup hL'M hML
    have e2 := AddSubgroup.relIndex_mul_relIndex (aDual Q a L).toAddSubgroup (aDual Q a M).toAddSubgroup
      (aDual Q a L').toAddSubgroup (aDual_anti Q hML) (aDual_anti Q hL'M)
    have step := latIndex_aDual_of_covBy Q hV ha ha0 hM hL hcov
    have hstep1 : 1 < latIndex M L := by
      rcases Nat.lt_or_ge 1 (latIndex M L) with h1 | h1
      · exact h1
      · exfalso
        have h0 : latIndex M L ≠ 0 := by
          intro h0
          apply hk0
          rw [← hk]
          simp only [latIndex] at h0 ⊢
          rw [← e1, h0, mul_zero]
        have h1' : latIndex M L = 1 := by omega
        exact hcov.lt.not_ge (AddSubgroup.relIndex_eq_one.1 h1')
    have hlt : latIndex L' M < k := by
      rw [← hk]
      simp only [latIndex] at hstep1 ⊢
      rw [← e1]
      have : L'.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := by
        intro h0; apply hk0; rw [← hk]; simp only [latIndex]; rw [← e1, h0, zero_mul]
      exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero this) hstep1
    have hne : latIndex L' M ≠ 0 := by
      intro h0; apply hk0; rw [← hk]; simp only [latIndex] at h0 ⊢; rw [← e1, h0, zero_mul]
    have ih' := ih _ hlt hM hL' hL'M rfl hne
    simp only [latIndex] at ih' step ⊢
    rw [← e1, ← e2, step, ih', mul_comm]

/-- **Duality of indices** (Hanke 2013, proof of Lemma 2.13, p. 7: "by the non-degeneracy of $B$ we have that
$[L' : L] = [(L')^{\#\mathfrak a} : L^{\#\mathfrak a}]$", read with $L' \subseteq L$): for lattices $L' \subseteq L$ in a
non-degenerate space and a non-zero fractional ideal $\mathfrak a$,
$[L'^{\#\mathfrak a} : L^{\#\mathfrak a}] = [L : L']$ (`AddSubgroup.relIndex`, $0$ when infinite). Proof: the
$\mathfrak a$-dual is an order-reversing involution on lattices (Lemma 2.4), so a chain of simple steps
$L' \subsetneq \dots \subsetneq L$ dualizes to one from $L^{\#\mathfrak a}$ to $L'^{\#\mathfrak a}$, and a step with
quotient $\cong R/\mathfrak m$ dualizes to one with quotient $\cong R/\mathfrak m$; the infinite case follows by
applying the finite case to $L^{\#\mathfrak a} \subseteq L'^{\#\mathfrak a}$. -/
@[kb "hanke2013algorithms" "Lemma 2.13, proof, p. 7 ([L'^{#a} : L^{#a}] = [L : L'])"]
theorem latIndex_aDual (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) {L L' : Submodule R V} (hL : L.IsLattice F) (hL' : L'.IsLattice F) (hLL' : L' ≤ L) :
    latIndex (aDual Q a L) (aDual Q a L') = latIndex L' L := by
  by_cases h0 : latIndex L' L = 0
  · by_contra hne
    rw [h0] at hne
    have hLd := isLattice_aDual Q hV ha ha0 hL
    have hL'd := isLattice_aDual Q hV ha ha0 hL'
    have := latIndex_aDual_of_ne_zero Q hV ha ha0 _ hL'd hLd (aDual_anti Q hLL') rfl hne
    rw [lemma_2_4 Q hV ha ha0 hL, lemma_2_4 Q hV ha ha0 hL'] at this
    exact hne (this.symm.trans h0)
  · exact latIndex_aDual_of_ne_zero Q hV ha ha0 _ hL hL' hLL' rfl h0

/-- **Lemma 2.13** (Hanke 2013, pp. 6–7): for lattices $L' \subseteq L$ in a non-degenerate space, a non-zero
fractional ideal $\mathfrak a$ and $L$ $\mathfrak a$-valued,
$|D_{\mathfrak a}(L')| = [L : L']^2\,|D_{\mathfrak a}(L)|$. Cardinalities and indices are `Nat.card` and
`AddSubgroup.relIndex` (both $0$ when infinite; over a number field they are finite). The proof is the paper's: the
duality of indices $[L'^{\#\mathfrak a} : L^{\#\mathfrak a}] = [L : L']$ (`latIndex_aDual`) and multiplicativity of
indices along $L' \subseteq L \subseteq L^{\#\mathfrak a} \subseteq L'^{\#\mathfrak a}$. *Erratum:* the paper's proof
writes $[L' : L]$ for $[L : L']$ (here $L' \subseteq L$). -/
@[kb "hanke2013algorithms" "Lemma 2.13, pp. 6–7"]
theorem lemma_2_13 (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) {L L' : Submodule R V} (hL : L.IsLattice F) (hL' : L'.IsLattice F) (hval : IsAValued Q a L)
    (hLL' : L' ≤ L) :
    Nat.card (DiscModule Q a L') = latIndex L' L ^ 2 * Nat.card (DiscModule Q a L) :=
  lemma_2_13_of_index Q hval hLL' (latIndex_aDual Q hV ha ha0 hL hL' hLL')

end IndexDuality

end QuadFormsKB.Hanke2013Algorithms
