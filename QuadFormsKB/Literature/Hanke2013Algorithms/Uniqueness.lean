/-
# Hanke 2013, Lemma 3.17: uniqueness of discriminant modules of maximal lattices

J. Hanke, *Algorithms for computing maximal lattices in bilinear (and quadratic) spaces over number fields*,
Contemp. Math. 587 (2013); source used: arXiv:1208.2481v3 (bib key `hanke2013algorithms`), §3.3, p. 14.

**Setting** as in `Duality.lean`: $R$ a Dedekind domain with fraction field $F$, $(V, B)$ a non-degenerate bilinear
space ($B$ = `bil Q`), $\mathfrak a$ a non-zero fractional ideal. For the finiteness of the discriminant modules we
assume that $R/I$ is finite for every non-zero ideal $I$ (true for the ring of integers $\mathcal O_F$ of a number field,
the paper's setting).

**Proves Lemma 3.17** (`lemma_3_17`): for maximal $\mathfrak a$-valued lattices $L_1$, $L_2$ there is an isomorphism
$D_{\mathfrak a}(L_1)\cong D_{\mathfrak a}(L_2)$ of $R$-modules preserving the $F/\mathfrak a$-valued forms $\widetilde B$.

*Proof* (a direct version of the paper's argument, which goes through the Witt group of torsion bilinear modules and
[33, Lemma 1.4]): with $L_0 = L_1\cap L_2$ and $W = L_1^{\#\mathfrak a}\cap L_2^{\#\mathfrak a} = (L_1 + L_2)^{\#\mathfrak a}$, the maps
$\pi_i : W\to D_{\mathfrak a}(L_i)$, $\vec x\mapsto\vec x + L_i$, both have kernel $L_0$ (by maximality: $\vec x\in L_1\cap L_2^{\#\mathfrak a}$
makes $L_2 + R\vec x$ $\mathfrak a$-valued), which is the injectivity of the paper's projections $N\to D_i$ for
$N = \{(\vec x + L_1,\vec x + L_2)\}$. Counting with Lemma 2.13 and the index duality (`latIndex_aDual`):
$[L_1:L_0]^2|D_1| = |D_{\mathfrak a}(L_0)| = [L_1:L_0][L_2:L_0][W:L_0]$ and symmetrically, with $[W:L_0]\le|D_i|$; hence
$[L_1:L_0] = [L_2:L_0]$ and $[W:L_0] = |D_1| = |D_2|$, so the $\pi_i$ are bijective and $\pi_2\circ\pi_1^{-1}$ is the isometry
(both forms are $B(\vec x,\vec x') + \mathfrak a$ on $W$).
-/
import QuadFormsKB.Literature.Hanke2013Algorithms.Maximal
import QuadFormsKB.Literature.OMeara.Sec81Rank

open QuadraticMap Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2013Algorithms

open QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- Finite index of a lattice in a lattice, when $R/I$ is finite for all non-zero ideals $I$. -/
theorem latIndex_ne_zero (hR : ∀ I : Ideal R, I ≠ ⊥ → Finite (R ⧸ I)) {K L : Submodule R V}
    (hK : K.IsLattice F) (hL : L.IsLattice F) : latIndex K L ≠ 0 := by
  obtain ⟨c, hc0, hcK⟩ := exists_smul_le_of_fg (F := F) hL.fg (by rw [hK.span_eq_top]; intro _ _; trivial)
  have : Module.Finite R L := Module.Finite.iff_fg.2 hL.fg
  set I : Ideal R := Ideal.span {c}
  have hI0 : I ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hc0
  have := hR I hI0
  have hfin : Finite (↥L ⧸ I • (⊤ : Submodule R L)) := Submodule.finite_quotient_smul I Module.Finite.fg_top
  set N' : Submodule R L := K.comap L.subtype
  have hle : I • (⊤ : Submodule R L) ≤ N' := by
    rw [Submodule.smul_le]
    intro r hr x _
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    show ((u * c) • (x : V)) ∈ K
    rw [mul_smul]
    exact K.smul_mem u (hcK x x.2)
  have hfin' : Finite (↥L ⧸ N') :=
    Finite.of_surjective (Submodule.mapQ (I • (⊤ : Submodule R L)) N' LinearMap.id hle)
      (fun q => Quotient.inductionOn' q fun x => ⟨Submodule.Quotient.mk x, rfl⟩)
  have hfin'' : Finite (↥L.toAddSubgroup ⧸ K.toAddSubgroup.addSubgroupOf L.toAddSubgroup) := hfin'
  exact AddSubgroup.index_ne_zero_of_finite

/-- The intersection of two lattices is a lattice. -/
theorem isLattice_inf {L₁ L₂ : Submodule R V} (h₁ : L₁.IsLattice F) (h₂ : L₂.IsLattice F) :
    (L₁ ⊓ L₂).IsLattice F := by
  obtain ⟨c, hc0, hc⟩ := exists_smul_le_of_fg (F := F) h₁.fg (by rw [h₂.span_eq_top]; intro _ _; trivial)
  have hcF : algebraMap R F c ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective R F)]; exact hc0
  refine ⟨?_, ?_⟩
  · have : IsNoetherian R L₁ := isNoetherian_of_fg_of_noetherian L₁ h₁.fg
    have hfg : ((L₁ ⊓ L₂).comap L₁.subtype).FG := IsNoetherian.noetherian _
    have hN : L₁ ⊓ L₂ = ((L₁ ⊓ L₂).comap L₁.subtype).map L₁.subtype := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 inf_le_left]
    rw [hN]; exact hfg.map _
  · rw [eq_top_iff, ← h₁.span_eq_top, Submodule.span_le]
    intro x hx
    have hmem : c • x ∈ L₁ ⊓ L₂ := ⟨L₁.smul_mem c hx, hc x hx⟩
    have : x = (algebraMap R F c)⁻¹ • (c • x) := by
      rw [← algebraMap_smul F c x, smul_smul, inv_mul_cancel₀ hcF, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

/-- The sum of two lattices is a lattice. -/
theorem isLattice_sup {L₁ L₂ : Submodule R V} (h₁ : L₁.IsLattice F) (h₂ : L₂.IsLattice F) :
    (L₁ ⊔ L₂).IsLattice F :=
  ⟨h₁.fg.sup h₂.fg, eq_top_iff.2 (h₁.span_eq_top ▸ Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left))⟩

/-- $(L_1 + L_2)^{\#\mathfrak a} = L_1^{\#\mathfrak a}\cap L_2^{\#\mathfrak a}$. -/
theorem aDual_sup (a : Submodule R F) (L₁ L₂ : Submodule R V) :
    aDual Q a (L₁ ⊔ L₂) = aDual Q a L₁ ⊓ aDual Q a L₂ := by
  apply le_antisymm
  · exact le_inf (aDual_anti Q le_sup_left) (aDual_anti Q le_sup_right)
  · rintro v ⟨h₁, h₂⟩ y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    rw [bil_add_right]
    exact add_mem (h₁ y₁ hy₁) (h₂ y₂ hy₂)

/-- By maximality of $L_2$: $L_1\cap L_2^{\#\mathfrak a}\subseteq L_2$ when $L_1$ is $\mathfrak a$-valued. -/
theorem mem_of_mem_aDual_of_isAMaximal {a : Submodule R F} {L₁ L₂ : Submodule R V} (h₁ : IsAValued Q a L₁)
    (h₂ : IsAMaximal Q a L₂) {x : V} (hx₁ : x ∈ L₁) (hx₂ : x ∈ aDual Q a L₂) : x ∈ L₂ := by
  have hxx : ∀ z ∈ span R {x}, bil Q x z ∈ a := by
    intro z hz
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [bil_rsmul_right, ← Algebra.smul_def]
    exact a.smul_mem r (h₁ (bil_mem_scale Q hx₁ hx₁))
  have hval : IsAValued Q a (L₂ ⊔ span R {x}) := by
    rw [lemma_2_2, aDual_sup]
    refine sup_le (le_inf ((lemma_2_2 Q).1 h₂.1) fun y hy z hz => ?_)
      ((Submodule.span_singleton_le_iff_mem _ _).2 ⟨hx₂, hxx⟩)
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [bil_rsmul_right, ← Algebra.smul_def]
    exact a.smul_mem r (bil_mem_of_mem_aDual_left Q hx₂ hy)
  have := h₂.2 _ le_sup_left hval
  rw [← this]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)

/-- The map $W\to D_{\mathfrak a}(L)$, $\vec x\mapsto\vec x + L$, for a submodule $W\subseteq L^{\#\mathfrak a}$. -/
def projTo (a : Submodule R F) (L : Submodule R V) {W : Submodule R V} (hW : W ≤ aDual Q a L) :
    W →ₗ[R] DiscModule Q a L :=
  (latIn Q a L).mkQ ∘ₗ Submodule.inclusion hW

theorem projTo_apply (a : Submodule R F) (L : Submodule R V) {W : Submodule R V} (hW : W ≤ aDual Q a L) (x : W) :
    projTo Q a L hW x = Submodule.Quotient.mk ⟨x, hW x.2⟩ := rfl

theorem ker_projTo (a : Submodule R F) (L : Submodule R V) {W : Submodule R V} (hW : W ≤ aDual Q a L) :
    LinearMap.ker (projTo Q a L hW) = L.comap W.subtype := by
  ext x
  rw [LinearMap.mem_ker, projTo_apply, Submodule.Quotient.mk_eq_zero]
  rfl

/-- `Nat.card` of the image of `projTo` is the index $[W : W\cap L]$. -/
theorem card_range_projTo (a : Submodule R F) (L : Submodule R V) {W : Submodule R V} (hW : W ≤ aDual Q a L) :
    Nat.card (LinearMap.range (projTo Q a L hW)) = latIndex L W := by
  rw [← Nat.card_congr (projTo Q a L hW).quotKerEquivRange.toEquiv, ker_projTo]
  rfl

/-- **Lemma 3.17** (Hanke 2013, p. 14): maximal $\mathfrak a$-valued lattices $L_1$, $L_2$ in a non-degenerate bilinear
space have isomorphic discriminant modules: there is an $R$-linear isomorphism
$e : D_{\mathfrak a}(L_1)\to D_{\mathfrak a}(L_2)$ with $\widetilde B(e(u), e(v)) = \widetilde B(u, v)$. Here $R$ is a Dedekind domain
whose quotients $R/I$ ($I\ne0$) are finite (as for $\mathcal O_F$, $F$ a number field). The proof is a direct version of
the paper's (see the file header); the isomorphism is $\vec x + L_1\mapsto\vec x + L_2$ for
$\vec x\in L_1^{\#\mathfrak a}\cap L_2^{\#\mathfrak a}$. -/
@[kb "hanke2013algorithms" "Lemma 3.17, p. 14"]
theorem lemma_3_17 (hR : ∀ I : Ideal R, I ≠ ⊥ → Finite (R ⧸ I))
    (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥)
    {L₁ L₂ : Submodule R V} (hL₁ : L₁.IsLattice F) (hL₂ : L₂.IsLattice F)
    (h₁ : IsAMaximal Q a L₁) (h₂ : IsAMaximal Q a L₂) :
    ∃ e : DiscModule Q a L₁ ≃ₗ[R] DiscModule Q a L₂,
      ∀ u v, discForm Q a L₂ (e u) (e v) = discForm Q a L₁ u v := by
  set L₀ := L₁ ⊓ L₂ with hL₀def
  set W := aDual Q a L₁ ⊓ aDual Q a L₂ with hWdef
  have hL₀ := isLattice_inf hL₁ hL₂
  have hS := isLattice_sup hL₁ hL₂
  have hW : W = aDual Q a (L₁ ⊔ L₂) := (aDual_sup Q a L₁ L₂).symm
  have hd₁ : L₁ ≤ aDual Q a L₁ := (lemma_2_2 Q).1 h₁.1
  have hd₂ : L₂ ≤ aDual Q a L₂ := (lemma_2_2 Q).1 h₂.1
  have hval₀ : IsAValued Q a L₀ := (lemma_2_2 Q).2 (inf_le_left.trans (hd₁.trans (aDual_anti Q inf_le_left)))
  have hL₀W : L₀ ≤ W := le_inf (inf_le_left.trans hd₁) (inf_le_right.trans hd₂)
  have hWd : W ≤ aDual Q a L₀ := hW ▸ aDual_anti Q (inf_le_left.trans le_sup_left)
  -- the kernels of the two projections are both `L₀`
  have k₁ : L₁.comap W.subtype = L₀.comap W.subtype := by
    ext x
    simp only [Submodule.mem_comap, Submodule.subtype_apply]
    exact ⟨fun h => ⟨h, mem_of_mem_aDual_of_isAMaximal Q h₁.1 h₂ h x.2.2⟩, fun h => h.1⟩
  have k₂ : L₂.comap W.subtype = L₀.comap W.subtype := by
    ext x
    simp only [Submodule.mem_comap, Submodule.subtype_apply]
    exact ⟨fun h => ⟨mem_of_mem_aDual_of_isAMaximal Q h₂.1 h₁ h x.2.1, h⟩, fun h => h.2⟩
  set f₁ := projTo Q a L₁ (inf_le_left : W ≤ aDual Q a L₁)
  set f₂ := projTo Q a L₂ (inf_le_right : W ≤ aDual Q a L₂)
  -- the counting
  set A := latIndex L₀ L₁
  set B := latIndex L₀ L₂
  set w := latIndex L₀ W
  set d₁ := Nat.card (DiscModule Q a L₁)
  set d₂ := Nat.card (DiscModule Q a L₂)
  have e₁ : Nat.card (DiscModule Q a L₀) = A ^ 2 * d₁ := lemma_2_13 Q hV ha ha0 hL₁ hL₀ h₁.1 inf_le_left
  have e₂ : Nat.card (DiscModule Q a L₀) = B ^ 2 * d₂ := lemma_2_13 Q hV ha ha0 hL₂ hL₀ h₂.1 inf_le_right
  have e₃ : Nat.card (DiscModule Q a L₀) = w * (A * B) := by
    rw [card_discModule]
    have m₁ := AddSubgroup.relIndex_mul_relIndex L₀.toAddSubgroup W.toAddSubgroup
      (aDual Q a L₀).toAddSubgroup hL₀W hWd
    have m₂ := latIndex_aDual Q hV ha ha0 hS hL₀ (inf_le_left.trans le_sup_left)
    have m₃ := AddSubgroup.relIndex_mul_relIndex L₀.toAddSubgroup L₁.toAddSubgroup
      (L₁ ⊔ L₂).toAddSubgroup (inf_le_left : L₀ ≤ L₁) (le_sup_left : L₁ ≤ L₁ ⊔ L₂)
    have m₄ : latIndex L₁ (L₁ ⊔ L₂) = B := by
      simp only [latIndex, B, L₀, Submodule.sup_toAddSubgroup]
      rw [AddSubgroup.relIndex_sup_left,
        show (L₁ ⊓ L₂).toAddSubgroup = L₁.toAddSubgroup ⊓ L₂.toAddSubgroup from rfl, AddSubgroup.inf_relIndex_right]
    rw [← hW] at m₂
    simp only [latIndex] at m₂ m₄ ⊢
    rw [← m₁, m₂, ← m₃, m₄]
  have hd₀ : Nat.card (DiscModule Q a L₀) ≠ 0 := by
    rw [card_discModule]; exact latIndex_ne_zero hR hL₀ (isLattice_aDual Q hV ha ha0 hL₀)
  have hA : 0 < A := by rw [e₁] at hd₀; exact Nat.pos_of_ne_zero (fun h => hd₀ (by rw [h]; simp))
  have hB : 0 < B := by rw [e₂] at hd₀; exact Nat.pos_of_ne_zero (fun h => hd₀ (by rw [h]; simp))
  have hd₁0 : 0 < d₁ := by rw [e₁] at hd₀; exact Nat.pos_of_ne_zero (fun h => hd₀ (by rw [h]; simp))
  have hd₂0 : 0 < d₂ := by rw [e₂] at hd₀; exact Nat.pos_of_ne_zero (fun h => hd₀ (by rw [h]; simp))
  have : Finite (DiscModule Q a L₁) := Nat.finite_of_card_ne_zero hd₁0.ne'
  have : Finite (DiscModule Q a L₂) := Nat.finite_of_card_ne_zero hd₂0.ne'
  have r₁ : Nat.card (LinearMap.range f₁) = w := by
    rw [← Nat.card_congr f₁.quotKerEquivRange.toEquiv, ker_projTo, k₁]; rfl
  have r₂ : Nat.card (LinearMap.range f₂) = w := by
    rw [← Nat.card_congr f₂.quotKerEquivRange.toEquiv, ker_projTo, k₂]; rfl
  have hw₁ : w ≤ d₁ := r₁ ▸ Nat.card_le_card_of_injective _ Subtype.val_injective
  have hw₂ : w ≤ d₂ := r₂ ▸ Nat.card_le_card_of_injective _ Subtype.val_injective
  have hAB : A ≤ B := by
    have : A * (A * d₁) ≤ A * (B * d₁) := by
      calc A * (A * d₁) = w * (A * B) := by rw [← e₃, e₁]; ring
        _ ≤ d₁ * (A * B) := Nat.mul_le_mul_right _ hw₁
        _ = A * (B * d₁) := by ring
    exact Nat.le_of_mul_le_mul_right (Nat.le_of_mul_le_mul_left this hA) hd₁0
  have hBA : B ≤ A := by
    have : B * (B * d₂) ≤ B * (A * d₂) := by
      calc B * (B * d₂) = w * (A * B) := by rw [← e₃, e₂]; ring
        _ ≤ d₂ * (A * B) := Nat.mul_le_mul_right _ hw₂
        _ = B * (A * d₂) := by ring
    exact Nat.le_of_mul_le_mul_right (Nat.le_of_mul_le_mul_left this hB) hd₂0
  have hAB' : A = B := le_antisymm hAB hBA
  have hwd₁ : w = d₁ := by
    have : A ^ 2 * w = A ^ 2 * d₁ := by rw [← e₁, e₃, ← hAB']; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hwd₂ : w = d₂ := by
    have : B ^ 2 * w = B ^ 2 * d₂ := by rw [← e₂, e₃, hAB']; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  -- both projections are onto
  have onto : ∀ {L : Submodule R V} (f : W →ₗ[R] DiscModule Q a L), Finite (DiscModule Q a L) →
      Nat.card (LinearMap.range f) = Nat.card (DiscModule Q a L) → Function.Surjective f := by
    intro L f _ hc
    rw [← LinearMap.range_eq_top]
    apply Submodule.toAddSubgroup_injective
    exact (AddSubgroup.card_eq_iff_eq_top _).1 hc
  have hs₁ : Function.Surjective f₁ := onto f₁ inferInstance (r₁.trans hwd₁)
  have hs₂ : Function.Surjective f₂ := onto f₂ inferInstance (r₂.trans hwd₂)
  have hker : LinearMap.ker f₁ = LinearMap.ker f₂ := by rw [ker_projTo, ker_projTo, k₁, k₂]
  let e : DiscModule Q a L₁ ≃ₗ[R] DiscModule Q a L₂ :=
    (f₁.quotKerEquivOfSurjective hs₁).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker).trans (f₂.quotKerEquivOfSurjective hs₂))
  have he : ∀ x : W, e (f₁ x) = f₂ x := by
    intro x
    have hsymm : (f₁.quotKerEquivOfSurjective hs₁).symm (f₁ x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [e, LinearEquiv.trans_apply, hsymm, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
  refine ⟨e, fun u v => ?_⟩
  obtain ⟨x, rfl⟩ := hs₁ u
  obtain ⟨y, rfl⟩ := hs₁ v
  rw [he, he]
  rfl

end QuadFormsKB.Hanke2013Algorithms
