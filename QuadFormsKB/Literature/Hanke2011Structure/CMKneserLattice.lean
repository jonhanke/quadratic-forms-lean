/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelFormsIdeals
import QuadFormsKB.Literature.Hanke2011Structure.CMKneserGroup

/-!
# Paper 6, Lemma 8.3: Kneser's group and proper classes of binary lattices

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Lemma 8.3, p. 34, with the correction "classes" → "proper classes"
(`lemma_8_3_not_proper`, `ClassNumber.lean`).

Let $K$ be a CM field, $F = K^+$, $N = N_{K/F}$, $\sigma$ complex conjugation. An element of Kneser's group
$G(\mathcal O_K)$ (`CMUnits.KneserGroup`) is a class of pairs $(\mathfrak A, a)$, $\mathfrak A \subseteq \mathcal O_K$ a nonzero
ideal, $a \in \mathcal O_F$, $N(\mathfrak A) = a\mathcal O_F$. Its lattice is $(\mathfrak A, a^{-1}N)$: the $\mathcal O_F$-lattice
$\mathfrak A$ (`Binary.Rel.idealLat`) in the binary quadratic space $(K, a^{-1}N)$; it is a rank-one $\mathcal O_K$-module
with $Q(cx) = N(c)Q(x)$, as in Kneser's description.

**Proper isometry** (`IsProperIsometricLat c c' L L'`): an isometry $\tau : (K, cN) \to (K, c'N)$ with $\tau(L) = L'$ and
$\det\tau = c/c'$ (every isometry has $\det\tau = \pm c/c'$; for $c = c'$ this is $\det\tau = 1$, i.e. $\tau \in SO$). In
coordinates, for free lattices, it is the proper ($\mathrm{SL}_2(\mathcal O_F)$-) equivalence of the Gram forms.

* `det_conj`: $\det_F(\sigma) = -1$;
* `isProperIsometricLat_iff`: $(L, cN) \to (L', c'N)$ properly isometric iff $L' = \lambda L$ with $c'N(\lambda) = c$;
* **`lemma_8_3_proper`**: $[(\mathfrak A, a)] = [(\mathfrak B, b)]$ in $G(\mathcal O_K)$ iff $(\mathfrak A, a^{-1}N)$ and
  $(\mathfrak B, b^{-1}N)$ are properly isometric. So $[(\mathfrak A, a)] \mapsto$ the proper class of $(\mathfrak A, a^{-1}N)$ is a
  well-defined injection of $G(\mathcal O_K)$ into the proper classes of binary $\mathcal O_F$-lattices. With plain
  isometry it would not be injective: $(\mathfrak A, a^{-1}N) \cong (\sigma\mathfrak A, a^{-1}N)$ via $\sigma$
  (`Binary.Rel.isometricLattices_ideal_iff`), while $[(\sigma\mathfrak A, a)] = [(\mathfrak A, a)]^{-1}$ (`kmk_mul_kinv`);
  compare `lemma_8_3_not_proper`.

* **Kneser's lattice form of $G(\mathcal O_K)$**: a *Kneser lattice* (`IsKneserLat c L`) is a nonzero finitely generated
  $\mathcal O_F$-lattice $L \subseteq K$ stable under $\mathcal O_K$ on which $cN$ is $\mathcal O_F$-valued and primitive.
  The lattice of every pair is one (`isKneserLat_latOf`), and every Kneser lattice is properly isometric to the lattice
  of a pair (`exists_pair_of_isKneserLat`: clear denominators, $\mathfrak A = bL$, and $N(\mathfrak A) = a\mathcal O_F$ with
  $a = N(b)/c \in \mathcal O_F$ by primitivity). With `lemma_8_3_proper`: **$G(\mathcal O_K)$ is in bijection with the
  proper classes of Kneser lattices**, i.e. the ideal-theoretic and lattice-theoretic descriptions of Kneser's group agree.

*Not formalized* (remaining part of Lemma 8.3): that every primitive binary $\mathcal O_F$-lattice with
$\det_H = \det_H(\mathcal O_K, N)$ and signature locally similar to that of $(\mathcal O_K, N)$ is properly isometric to
some $(\mathfrak A, a^{-1}N)$ (Kneser 1982, p. 407: such a lattice is a module over its even Clifford algebra, the
quadratic $\mathcal O_F$-algebra of discriminant $-S$, which is $\mathcal O_K$), and the computation of $\det_H$ and the
signatures of $(\mathfrak A, a^{-1}N)$.
-/

open NumberField NumberField.IsCMField Module QuadFormsKB.Binary.Rel
open scoped nonZeroDivisors

namespace QuadFormsKB.Hanke2011Structure.CMUnits

set_option linter.unusedSectionVars false

noncomputable section

/-! ### $\det\sigma = -1$ and proper isometries of norm forms -/

section General

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero F] [Algebra.IsQuadraticExtension F E]

/-- **The nontrivial automorphism of a quadratic extension has determinant $-1$** as an $F$-linear map. -/
theorem det_conj : LinearMap.det ((conj F E).toLinearEquiv : E →ₗ[F] E) = -1 := by
  classical
  -- an element with `σ δ = -δ`, `δ ≠ 0`
  obtain ⟨θ, hθ⟩ : ∃ θ : E, conj F E θ ≠ θ := by
    by_contra h
    push Not at h
    exact conj_ne_one F E (AlgEquiv.ext h)
  set δ := θ - conj F E θ with hδ
  have hδσ : conj F E δ = -δ := by rw [hδ, map_sub, conj_conj]; ring
  have hδ0 : δ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  -- `{1, δ}` is a basis
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 := congrArg (conj F E) hst
    rw [map_add, map_smul, map_smul, map_one, hδσ, map_zero] at h2
    have hs : (2 * s) • (1 : E) = 0 := by
      rw [mul_smul, two_smul]
      linear_combination (norm := module) hst + h2
    have hs' : s = 0 := by
      rcases smul_eq_zero.mp hs with h | h
      · exact (mul_eq_zero.mp h).resolve_left two_ne_zero
      · exact absurd h one_ne_zero
    subst hs'
    rw [zero_smul, zero_add] at hst
    exact ⟨rfl, (smul_eq_zero.mp hst).resolve_right hδ0⟩
  have hcard : Fintype.card (Fin 2) = finrank F E := by
    rw [Fintype.card_fin, Algebra.IsQuadraticExtension.finrank_eq_two]
  let b : Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = δ := by simp [b]
  rw [← LinearMap.det_toMatrix b]
  have e0 : conj F E (b 0) = b 0 := by rw [hb0, map_one]
  have e1 : conj F E (b 1) = -(b 1) := by rw [hb1, hδσ]
  have hM : LinearMap.toMatrix b b ((conj F E).toLinearEquiv : E →ₗ[F] E) = !![1, 0; 0, -1] := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    fin_cases i <;> fin_cases j <;>
      simp only [AlgEquiv.toLinearEquiv_apply, LinearEquiv.coe_coe, Fin.zero_eta, Fin.mk_one] <;>
      first
        | (erw [e0]; simp [b.repr_self])
        | (erw [e1]; simp [b.repr_self])
  rw [hM, Matrix.det_fin_two_of]
  ring

/-- **Proper isometry of lattices in $(E, cN)$ and $(E, c'N)$**: an isometry $\tau$ with $\det\tau = c/c'$ mapping $L$
onto $L'$. -/
@[kb "hanke2011structure" "Lemma 8.3, p. 34 (proper classes Cls^{*,+}; §1.3, p. 6)"]
def IsProperIsometricLat {F E : Type*} [Field F] [NumberField F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] (c c' : F) (L L' : Submodule (𝓞 F) E) : Prop :=
  ∃ τ : (c • normForm F E).IsometryEquiv (c' • normForm F E),
    LinearMap.det (τ.toLinearEquiv : E →ₗ[F] E) = c / c' ∧
      L.map (Lattices.IsometryEquiv.toOLinear τ) = L'

end General

section Lattice

variable {F E : Type*} [Field F] [NumberField F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

theorem det_mulEquiv (l : E) (hl : l ≠ 0) :
    LinearMap.det ((mulEquiv (F := F) l hl : E ≃ₗ[F] E) : E →ₗ[F] E) = Algebra.norm F l := by
  rw [Algebra.norm_apply]
  congr 1

/-- **Proper isometries of norm-form lattices**: $(L, cN) \to (L', c'N)$ properly isometric iff $L' = \lambda L$ for some
$\lambda \in E^\times$ with $c'N(\lambda) = c$ (the isometries $x \mapsto \lambda\sigma(x)$ have determinant $-c/c'$). -/
@[kb "hanke2011structure" "Lemma 8.3, p. 34 (proper classes; O'Meara §43C)"]
theorem isProperIsometricLat_iff {c c' : F} (hc : c ≠ 0) (hc' : c' ≠ 0) (L L' : Submodule (𝓞 F) E) :
    IsProperIsometricLat c c' L L' ↔ ∃ l : E, l ≠ 0 ∧ c' * Algebra.norm F l = c ∧ L' = smulLat l L := by
  constructor
  · rintro ⟨τ, hdet, hτ⟩
    have hN : ∀ x, Algebra.norm F (τ x) = (c / c') * Algebra.norm F x := fun x => by
      have := τ.map_app x
      simp only [smul_apply, normForm_apply, smul_eq_mul] at this
      field_simp
      linear_combination this
    have ha : c / c' ≠ 0 := div_ne_zero hc hc'
    set l := τ 1
    have hNl : Algebra.norm F l = c / c' := by rw [hN, map_one, mul_one]
    have hl0 : l ≠ 0 := by
      intro h0; rw [h0, Algebra.norm_eq_zero_iff.mpr rfl] at hNl; exact ha hNl.symm
    have hcl : c' * Algebra.norm F l = c := by rw [hNl]; field_simp
    rcases linear_similitude τ.toLinearEquiv.toLinearMap ha hN with h | h
    · refine ⟨l, hl0, hcl, ?_⟩
      have hm := map_simIso l hl0 hcl false L
      simp only [Bool.false_eq_true, ite_false] at hm
      rw [← hτ, ← hm]
      congr 1
      ext x
      show τ x = simIso l hl0 hcl false x
      rw [simIso_apply]; exact h x
    · exfalso
      have hcomp : (τ.toLinearEquiv : E →ₗ[F] E) =
          ((mulEquiv (F := F) l hl0 : E ≃ₗ[F] E) : E →ₗ[F] E).comp ((conj F E).toLinearEquiv : E →ₗ[F] E) := by
        ext x; exact h x
      rw [hcomp, LinearMap.det_comp, det_mulEquiv, det_conj, hNl] at hdet
      have : c / c' = 0 := by linear_combination -hdet / 2
      exact ha this
  · rintro ⟨l, hl, hcl, rfl⟩
    have hm := map_simIso l hl hcl false L
    simp only [Bool.false_eq_true, ite_false] at hm
    refine ⟨simIso l hl hcl false, ?_, hm⟩
    have e : ((simIso l hl hcl false).toLinearEquiv : E →ₗ[F] E) =
        ((mulEquiv (F := F) l hl : E ≃ₗ[F] E) : E →ₗ[F] E) := by
      ext x; rfl
    rw [e, det_mulEquiv, ← hcl]
    field_simp

end Lattice

/-! ### Lemma 8.3: Kneser's group injects into the proper classes -/

section CM

variable (K : Type) [Field K] [NumberField K] [IsCMField K]

/-- The scale $a^{-1} \in F$ of the lattice $(\mathfrak A, a^{-1}N)$ of a pair $(\mathfrak A, a)$. -/
def scaleOf (s : kneserMonoid K) : maximalRealSubfield K := (algebraMap (OF K) (maximalRealSubfield K) s.1.2)⁻¹

/-- The lattice $\mathfrak A \subseteq K$ of a pair $(\mathfrak A, a)$ (an $\mathcal O_F$-lattice). -/
def latOf (s : kneserMonoid K) : Submodule (OF K) K := idealLat (maximalRealSubfield K) s.1.1

theorem snd_ne_zero (s : kneserMonoid K) : s.1.2 ≠ 0 := by
  intro h
  have h2 := s.2.2
  rw [h, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.relNorm_eq_bot_iff] at h2
  exact s.2.1 h2

theorem scaleOf_ne_zero (s : kneserMonoid K) : scaleOf K s ≠ 0 :=
  inv_ne_zero ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr (snd_ne_zero K s))

theorem algebraMap_nrm (x : 𝓞 K) :
    algebraMap (OF K) (maximalRealSubfield K) (nrm K x) =
      Algebra.norm (maximalRealSubfield K) (algebraMap (𝓞 K) K x) := by
  rw [nrm, Algebra.algebraMap_intNorm (L := K)]

/-- **Lemma 8.3, corrected (proper classes): injectivity and well-definedness** (Hanke 2011, p. 34). For pairs
$s = (\mathfrak A, a)$, $t = (\mathfrak B, b)$ ($N(\mathfrak A) = a\mathcal O_F$, $N(\mathfrak B) = b\mathcal O_F$),
$[s] = [t]$ in Kneser's group $G(\mathcal O_K)$ iff the lattices $(\mathfrak A, a^{-1}N)$ and $(\mathfrak B, b^{-1}N)$ are
properly isometric. -/
@[kb "hanke2011structure" "Lemma 8.3, p. 34 (G(O_K) ↪ proper classes; corrected)"]
theorem lemma_8_3_proper (s t : kneserMonoid K) :
    kmk K s = kmk K t ↔ IsProperIsometricLat (scaleOf K s) (scaleOf K t) (latOf K s) (latOf K t) := by
  rw [isProperIsometricLat_iff (scaleOf_ne_zero K s) (scaleOf_ne_zero K t), kmk_eq_iff]
  have ha := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (OF K) (maximalRealSubfield K))).mpr
    (snd_ne_zero K s)
  have hb := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (OF K) (maximalRealSubfield K))).mpr
    (snd_ne_zero K t)
  constructor
  · rintro ⟨p, ⟨x, hx, rfl⟩, q, ⟨y, hy, rfl⟩, h⟩
    have h1 := congrArg (fun r : kneserMonoid K => r.1.1) h
    have h2 := congrArg (fun r : kneserMonoid K => r.1.2) h
    simp only [Submonoid.coe_mul, Prod.fst_mul, Prod.snd_mul, prin] at h1 h2
    have hy' := algebraMap_ne_zero (E := K) hy
    have hx' := algebraMap_ne_zero (E := K) hx
    refine ⟨algebraMap _ K x / algebraMap _ K y, div_ne_zero hx' hy', ?_, ?_⟩
    · have e := congrArg (algebraMap (OF K) (maximalRealSubfield K)) h2
      rw [map_mul, map_mul, algebraMap_nrm, algebraMap_nrm] at e
      have hNy : Algebra.norm (maximalRealSubfield K) (algebraMap (𝓞 K) K y) ≠ 0 :=
        Algebra.norm_ne_zero_iff.mpr hy'
      have hd : Algebra.norm (maximalRealSubfield K) (algebraMap (𝓞 K) K x / algebraMap (𝓞 K) K y) =
          Algebra.norm (maximalRealSubfield K) (algebraMap (𝓞 K) K x) /
            Algebra.norm (maximalRealSubfield K) (algebraMap (𝓞 K) K y) := by
        rw [eq_div_iff hNy, ← map_mul, div_mul_cancel₀ _ hy']
      unfold scaleOf
      rw [hd]
      field_simp
      linear_combination e
    · unfold latOf
      rw [smulLat_idealLat_iff hy]
      rw [mul_comm, h1, mul_comm]
  · rintro ⟨l, hl, hcl, hL⟩
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) l
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hx0 : x ≠ 0 := by rintro rfl; simp at hl
    refine ⟨prin K x hx0, ⟨x, hx0, rfl⟩, prin K y hy0, ⟨y, hy0, rfl⟩, ?_⟩
    unfold latOf at hL
    rw [smulLat_idealLat_iff hy0] at hL
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · show s.1.1 * Ideal.span {x} = t.1.1 * Ideal.span {y}
      rw [mul_comm, hL, mul_comm]
    · show s.1.2 * nrm K x = t.1.2 * nrm K y
      apply FaithfulSMul.algebraMap_injective (OF K) (maximalRealSubfield K)
      rw [map_mul, map_mul, algebraMap_nrm, algebraMap_nrm]
      have hy' := algebraMap_ne_zero (E := K) hy0
      have hNy : Algebra.norm (maximalRealSubfield K) (algebraMap (𝓞 K) K y) ≠ 0 :=
        Algebra.norm_ne_zero_iff.mpr hy'
      have hd : Algebra.norm (maximalRealSubfield K) (algebraMap (𝓞 K) K x / algebraMap (𝓞 K) K y) =
          Algebra.norm (maximalRealSubfield K) (algebraMap (𝓞 K) K x) /
            Algebra.norm (maximalRealSubfield K) (algebraMap (𝓞 K) K y) := by
        rw [eq_div_iff hNy, ← map_mul, div_mul_cancel₀ _ hy']
      unfold scaleOf at hcl
      rw [hd] at hcl
      field_simp at hcl
      linear_combination hcl

/-! ### Kneser's lattice description: every primitive $\mathcal O_K$-stable lattice is an ideal lattice -/

/-- **A Kneser lattice in $(K, cN)$** (Hanke 2011, Lemma 8.3; Kneser 1982, §6): a nonzero finitely generated
$\mathcal O_F$-lattice $L \subseteq K$ that is an $\mathcal O_K$-module (a rank-one $\mathcal O_K$-module with
$Q(zx) = N(z)Q(x)$ for $Q = cN$), on which $cN$ is $\mathcal O_F$-valued and primitive (its values generate
$\mathcal O_F$). Every rank-one $\mathcal O_K$-module with a norm-compatible form embeds in this way in $K$ (not formalized). -/
@[kb "hanke2011structure" "Lemma 8.3, p. 34 (G(C): primitive lattices that are rank one C-modules)"]
structure IsKneserLat (c : maximalRealSubfield K) (L : Submodule (OF K) K) : Prop where
  ne_bot : L ≠ ⊥
  fg : L.FG
  stable : ∀ z : 𝓞 K, ∀ x ∈ L, algebraMap (𝓞 K) K z * x ∈ L
  integral : ∀ x ∈ L, ∃ r : OF K, c * Algebra.norm (maximalRealSubfield K) x = algebraMap (OF K) _ r
  primitive : Ideal.span {r : OF K | ∃ x ∈ L, c * Algebra.norm (maximalRealSubfield K) x = algebraMap (OF K) _ r} = ⊤

/-- Clearing denominators: some $b \in \mathcal O_K \setminus 0$ has $bL \subseteq \mathcal O_K$. -/
theorem exists_integral_multiple {L : Submodule (OF K) K} (hfg : L.FG) :
    ∃ b : 𝓞 K, b ≠ 0 ∧ ∀ x ∈ L, ∃ z : 𝓞 K, algebraMap (𝓞 K) K z = algebraMap (𝓞 K) K b * x := by
  classical
  obtain ⟨S, hS⟩ := hfg
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset (𝓞 K)⁰ (R := 𝓞 K) (S := K) S
  refine ⟨b, nonZeroDivisors.ne_zero hb, fun x hx => ?_⟩
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz⟩ := hint y hy
    exact ⟨z, by rw [hz, Algebra.smul_def]⟩
  | zero => exact ⟨0, by simp⟩
  | add y y' _ _ h h' =>
    obtain ⟨z, hz⟩ := h
    obtain ⟨z', hz'⟩ := h'
    exact ⟨z + z', by rw [map_add, hz, hz', mul_add]⟩
  | smul r y _ h =>
    obtain ⟨z, hz⟩ := h
    refine ⟨algebraMap (OF K) (𝓞 K) r * z, ?_⟩
    rw [map_mul, hz, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
    ring

/-- **Lemma 8.3 in Kneser's lattice form, surjectivity** (Hanke 2011, p. 34): every Kneser lattice $(L, cN)$
(`IsKneserLat`) is properly isometric to the lattice $(\mathfrak A, a^{-1}N)$ of some pair $(\mathfrak A, a)$ of Kneser's
group. With `lemma_8_3_proper`, $G(\mathcal O_K)$ is in bijection with the proper classes of Kneser lattices. -/
@[kb "hanke2011structure" "Lemma 8.3, p. 34 (lattice form of G(O_K): surjectivity)"]
theorem exists_pair_of_isKneserLat {c : maximalRealSubfield K} (hc : c ≠ 0) {L : Submodule (OF K) K}
    (hL : IsKneserLat K c L) : ∃ s : kneserMonoid K, IsProperIsometricLat c (scaleOf K s) L (latOf K s) := by
  classical
  obtain ⟨b, hb0, hbL⟩ := exists_integral_multiple K hL.fg
  have hb' : algebraMap (𝓞 K) K b ≠ 0 := algebraMap_ne_zero (E := K) hb0
  have hNb : Algebra.norm (maximalRealSubfield K) (algebraMap (𝓞 K) K b) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb'
  -- the ideal `𝔄 = bL`
  let 𝔄 : Ideal (𝓞 K) :=
    { carrier := {z | ∃ x ∈ L, algebraMap (𝓞 K) K z = algebraMap (𝓞 K) K b * x}
      add_mem' := by
        rintro z z' ⟨x, hx, hz⟩ ⟨x', hx', hz'⟩
        exact ⟨x + x', L.add_mem hx hx', by rw [map_add, hz, hz', mul_add]⟩
      zero_mem' := ⟨0, L.zero_mem, by simp⟩
      smul_mem' := by
        rintro w z ⟨x, hx, hz⟩
        refine ⟨algebraMap (𝓞 K) K w * x, hL.stable w x hx, ?_⟩
        rw [smul_eq_mul, map_mul, hz]; ring }
  have hmem𝔄 : ∀ z, z ∈ 𝔄 ↔ ∃ x ∈ L, algebraMap (𝓞 K) K z = algebraMap (𝓞 K) K b * x := fun _ => Iff.rfl
  have hlat : idealLat (maximalRealSubfield K) 𝔄 = smulLat (algebraMap (𝓞 K) K b) L := by
    ext y
    rw [mem_idealLat, mem_smulLat]
    constructor
    · rintro ⟨z, ⟨x, hx, hz⟩, rfl⟩
      exact ⟨x, hx, hz.symm⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz⟩ := hbL x hx
      exact ⟨z, ⟨x, hx, hz⟩, hz⟩
  have h𝔄0 : 𝔄 ≠ ⊥ := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL.ne_bot
    obtain ⟨z, hz⟩ := hbL x hx
    have : z ∈ 𝔄 := ⟨x, hx, hz⟩
    rw [h, Ideal.mem_bot] at this
    rw [this, map_zero] at hz
    exact mul_ne_zero hb' hx0 hz.symm
  -- `a = N(b)/c ∈ 𝒪_F` lies in `N(𝔄)`
  set q : maximalRealSubfield K := Algebra.norm (maximalRealSubfield K) (algebraMap (𝓞 K) K b) / c with hq
  have key : ∀ t ∈ Ideal.span {r : OF K | ∃ x ∈ L, c * Algebra.norm (maximalRealSubfield K) x = algebraMap (OF K) (maximalRealSubfield K) r},
      ∃ u ∈ Ideal.relNorm (OF K) 𝔄, algebraMap (OF K) (maximalRealSubfield K) u = algebraMap (OF K) (maximalRealSubfield K) t * q := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨x, hx, hr⟩ := hr
      obtain ⟨z, hz⟩ := hbL x hx
      refine ⟨nrm K z, ?_, ?_⟩
      · rw [Ideal.relNorm_apply]
        exact Ideal.subset_span ⟨z, ⟨x, hx, hz⟩, rfl⟩
      · rw [algebraMap_nrm, hz, map_mul, ← hr, hq]
        field_simp
    | zero => exact ⟨0, Ideal.zero_mem _, by simp⟩
    | add t t' _ _ h h' =>
      obtain ⟨u, hu, hu'⟩ := h
      obtain ⟨u', hv, hv'⟩ := h'
      exact ⟨u + u', Ideal.add_mem _ hu hv, by rw [map_add, map_add, hu', hv', add_mul]⟩
    | smul w t _ h =>
      obtain ⟨u, hu, hu'⟩ := h
      exact ⟨w * u, Ideal.mul_mem_left _ _ hu, by rw [smul_eq_mul, map_mul, map_mul, hu', mul_assoc]⟩
  obtain ⟨a, ha𝔄, ha⟩ := key 1 (by rw [hL.primitive]; exact Submodule.mem_top)
  rw [map_one, one_mul] at ha
  have hq0 : q ≠ 0 := div_ne_zero hNb hc
  have ha0 : a ≠ 0 := by
    rintro rfl; rw [map_zero] at ha; exact hq0 ha.symm
  have hnorm : Ideal.relNorm (OF K) 𝔄 = Ideal.span {a} := by
    refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).mpr ha𝔄)
    rw [Ideal.relNorm_apply, Ideal.span_le]
    rintro _ ⟨z, ⟨x, hx, hz⟩, rfl⟩
    obtain ⟨r, hr⟩ := hL.integral x hx
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    refine ⟨r, FaithfulSMul.algebraMap_injective (OF K) (maximalRealSubfield K) ?_⟩
    rw [map_mul, ha, ← hr, algebraMap_nrm, hz, map_mul, hq]
    field_simp
  let s : kneserMonoid K := ⟨(𝔄, a), h𝔄0, hnorm⟩
  refine ⟨s, (isProperIsometricLat_iff hc (scaleOf_ne_zero K s) _ _).mpr
    ⟨algebraMap (𝓞 K) K b, hb', ?_, hlat⟩⟩
  show (algebraMap (OF K) (maximalRealSubfield K) a)⁻¹ * Algebra.norm (maximalRealSubfield K) (algebraMap (𝓞 K) K b) = c
  rw [ha, hq]
  field_simp

/-- **The lattice of a pair is a Kneser lattice**: for $(\mathfrak A, a)$ with $N(\mathfrak A) = a\mathcal O_F$, the lattice
$(\mathfrak A, a^{-1}N)$ is a nonzero finitely generated $\mathcal O_K$-stable lattice on which $a^{-1}N$ is $\mathcal O_F$-valued
and primitive. -/
@[kb "hanke2011structure" "Lemma 8.3, p. 34 (lattice form of G(O_K))"]
theorem isKneserLat_latOf (s : kneserMonoid K) : IsKneserLat K (scaleOf K s) (latOf K s) := by
  classical
  have hs0 := s.2.1
  have hsN := s.2.2
  have ha0 := snd_ne_zero K s
  have ha' : algebraMap (OF K) (maximalRealSubfield K) s.1.2 ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr ha0
  -- norms of elements of `𝔄` are multiples of `a`
  have hdiv : ∀ z ∈ s.1.1, ∃ r : OF K, nrm K z = s.1.2 * r := by
    intro z hz
    have : nrm K z ∈ Ideal.relNorm (OF K) s.1.1 := by
      rw [Ideal.relNorm_apply]; exact Ideal.subset_span ⟨z, hz, rfl⟩
    rw [hsN, Ideal.mem_span_singleton] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hs0
    rw [eq_bot_iff]
    intro z hz
    have : algebraMap (𝓞 K) K z ∈ latOf K s := algebraMap_mem_idealLat hz
    rw [h, Submodule.mem_bot] at this
    exact (Submodule.mem_bot _).mpr (FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [this, map_zero]))
  · have hfg : (s.1.1.restrictScalars (OF K)).FG := IsNoetherian.noetherian _
    have : latOf K s = (s.1.1.restrictScalars (OF K)).map
        ((Algebra.linearMap (𝓞 K) K).restrictScalars (OF K)) := by
      ext x
      rw [latOf, mem_idealLat, Submodule.mem_map]
      simp
    rw [this]
    exact hfg.map _
  · intro w x hx
    obtain ⟨z, hz, rfl⟩ := mem_idealLat.mp hx
    rw [← map_mul]
    exact algebraMap_mem_idealLat (Ideal.mul_mem_left _ _ hz)
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_idealLat.mp hx
    obtain ⟨r, hr⟩ := hdiv z hz
    refine ⟨r, ?_⟩
    rw [← algebraMap_nrm, hr, map_mul, scaleOf]
    field_simp
  · -- `a ∈ N(𝔄) = span (N 𝔄)`, so `1 = Σ tᵢ (a⁻¹ N zᵢ)`
    set R := {r : OF K | ∃ x ∈ latOf K s,
      scaleOf K s * Algebra.norm (maximalRealSubfield K) x = algebraMap (OF K) _ r}
    have key : ∀ u ∈ Ideal.relNorm (OF K) s.1.1, ∃ t ∈ Ideal.span R, u = s.1.2 * t := by
      intro u hu
      rw [Ideal.relNorm_apply] at hu
      induction hu using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨z, hz, rfl⟩ := hv
        obtain ⟨r, hr⟩ := hdiv z hz
        refine ⟨r, Ideal.subset_span ⟨algebraMap (𝓞 K) K z, algebraMap_mem_idealLat hz, ?_⟩, hr⟩
        rw [← algebraMap_nrm, hr, map_mul, scaleOf]
        field_simp
      | zero => exact ⟨0, Ideal.zero_mem _, by simp⟩
      | add u u' _ _ h h' =>
        obtain ⟨t, ht, rfl⟩ := h
        obtain ⟨t', ht', rfl⟩ := h'
        exact ⟨t + t', Ideal.add_mem _ ht ht', by ring⟩
      | smul w u _ h =>
        obtain ⟨t, ht, rfl⟩ := h
        exact ⟨w * t, Ideal.mul_mem_left _ _ ht, by rw [smul_eq_mul]; ring⟩
    have haN : s.1.2 ∈ Ideal.relNorm (OF K) s.1.1 := by
      rw [hsN]; exact Ideal.mem_span_singleton_self _
    obtain ⟨t, ht, hat⟩ := key _ haN
    have ht1 : t = 1 := by
      have : s.1.2 * 1 = s.1.2 * t := by rw [mul_one]; exact hat
      exact (mul_left_cancel₀ ha0 this).symm
    rw [ht1] at ht
    exact (Ideal.eq_top_iff_one _).mpr ht

end CM

end

end QuadFormsKB.Hanke2011Structure.CMUnits

#print axioms QuadFormsKB.Hanke2011Structure.CMUnits.det_conj
#print axioms QuadFormsKB.Hanke2011Structure.CMUnits.isProperIsometricLat_iff
#print axioms QuadFormsKB.Hanke2011Structure.CMUnits.lemma_8_3_proper
#print axioms QuadFormsKB.Hanke2011Structure.CMUnits.exists_pair_of_isKneserLat
#print axioms QuadFormsKB.Hanke2011Structure.CMUnits.isKneserLat_latOf
