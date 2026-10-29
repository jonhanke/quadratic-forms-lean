/-
# The presentation of $\mathrm{Sp}_{2g}(k)$ over finite fields with more than $3g$ elements

**Layer:** pure algebra over a field $k$.

**Result** (`siegelPresentation_of_card`, `siegelPresentation_of_fintype`). For every genus $g$ and every field $k$
with more than $3g$ elements (cardinality $\#k > 3g$; in particular every finite field $\mathbb F_q$ with $q > 3g$),
the named input `SiegelPresentation g k` holds: if maps $N$ (on symmetric matrices), $A$ (on $\mathrm{GL}_g(k)$) and an
element $W$ of a monoid $M$ satisfy the relations `SiegelRelations`, there is a monoid homomorphism
$\rho : \mathrm{Sp}_{2g}(k) \to M$ with $\rho(n(B)) = N(B)$, $\rho(m(a)) = A(a)$, $\rho(w) = W$.
This extends `siegelPresentation` (`Weil/Genus/SiegelPres.lean`, infinite fields) to large finite fields.

**Method.** The big-cell proof of `siegelPresentation` uses the infinitude of $k$ only to move a finite list of
elements of $\mathrm{Sp}_{2g}(k)$ simultaneously into the big cell $\Omega = \{\det c \ne 0\}$ by a common $n(T)w$.
Two refinements make it work over a field with more than $3g$ elements:
* the extension lemma (`exists_monoidHom_of_generic3`, a copy of `exists_monoidHom_of_generic`) only needs lists of
  length at most $3$;
* for a list $L$ with $|L| \cdot g < \#k$, along the line $t \mapsto T_1 + t(T_2 - T_1)$ the product of the
  determinants $\det(c_\gamma T + d_\gamma)$, $\gamma \in L$, is a nonzero polynomial in $t$ of degree at most
  $|L| \cdot g$, hence has a non-root in $k$ (`exists_symm_det_ne_list_card`).

The fields with at most $3g$ elements ($g \ge 2$: $\mathbb F_2, \dots$) are not covered; for them the genericity
statement can fail (the big cell has density $\prod_{i=1}^{g}(1 + q^{-i})^{-1} < 1/2$ for $q = 2$, $g \ge 3$) and a
Bruhat-decomposition argument is needed.

Sources: Weil, Acta Math. 111 (1964), §§1–2 [unverified]; Kudla, *Notes on the local theta correspondence* (1996),
§I.1 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Genus.SiegelPres

open Matrix Polynomial

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

universe u v

section Extend

variable {G H : Type*} [Group G] [Group H]

/-- Independence of the choice in $\rho(gz)\rho(z)^{-1}$, using genericity only for lists of length at most $3$. -/
lemma generic3_indep {Ω : Set G} {ρ : G → H}
    (hmul : ∀ x y, x ∈ Ω → y ∈ Ω → x * y ∈ Ω → ρ (x * y) = ρ x * ρ y)
    (hgen : ∀ L : List G, L.length ≤ 3 → ∃ z ∈ Ω, ∀ h ∈ L, h * z ∈ Ω) {g z z' : G}
    (hz : z ∈ Ω) (hgz : g * z ∈ Ω) (hz' : z' ∈ Ω) (hgz' : g * z' ∈ Ω) :
    ρ (g * z) * (ρ z)⁻¹ = ρ (g * z') * (ρ z')⁻¹ := by
  obtain ⟨y, hy, hL⟩ := hgen [z⁻¹, z'⁻¹, g] (by simp)
  have h1 : z⁻¹ * y ∈ Ω := hL _ (by simp)
  have h2 : z'⁻¹ * y ∈ Ω := hL _ (by simp)
  have h3 : g * y ∈ Ω := hL _ (by simp)
  have key : ∀ u, u ∈ Ω → g * u ∈ Ω → u⁻¹ * y ∈ Ω →
      ρ (g * u) * (ρ u)⁻¹ = ρ (g * y) * (ρ y)⁻¹ := by
    intro u hu hgu hv
    have e1 : ρ (u * (u⁻¹ * y)) = ρ u * ρ (u⁻¹ * y) := hmul _ _ hu hv (by simpa using hy)
    have e2 : ρ (g * u * (u⁻¹ * y)) = ρ (g * u) * ρ (u⁻¹ * y) :=
      hmul _ _ hgu hv (by simpa [mul_assoc] using h3)
    simp only [mul_inv_cancel_left, mul_assoc] at e1 e2
    rw [e1, e2]
    group
  rw [key z hz hgz h1, key z' hz' hgz' h2]

/-- **Extension from a $3$-generic subset.** If $\rho : G \to H$ is multiplicative on $\Omega$ (`hmul`:
$\rho(xy) = \rho(x)\rho(y)$ whenever $x, y, xy \in \Omega$) and $\Omega$ is $3$-generic (`hgen`: for every list $L$ of
at most $3$ elements of $G$ there is $z \in \Omega$ with $hz \in \Omega$ for all $h \in L$), then some homomorphism
$\varphi : G \to H$ agrees with $\rho$ on $\Omega$. -/
@[kb "weil1964" "§§1–2 (operators defined on a dense subset of $\\mathrm{Sp}$ and extended) [unverified]"]
theorem exists_monoidHom_of_generic3 (Ω : Set G) (ρ : G → H)
    (hmul : ∀ x y, x ∈ Ω → y ∈ Ω → x * y ∈ Ω → ρ (x * y) = ρ x * ρ y)
    (hgen : ∀ L : List G, L.length ≤ 3 → ∃ z ∈ Ω, ∀ h ∈ L, h * z ∈ Ω) :
    ∃ φ : G →* H, ∀ x ∈ Ω, φ x = ρ x := by
  have hz : ∀ g : G, ∃ z, z ∈ Ω ∧ g * z ∈ Ω := fun g => by
    obtain ⟨z, hz, hL⟩ := hgen [g] (by simp)
    exact ⟨z, hz, hL _ (by simp)⟩
  choose zf hzf hgzf using hz
  let φ : G → H := fun g => ρ (g * zf g) * (ρ (zf g))⁻¹
  have hφ : ∀ g z, z ∈ Ω → g * z ∈ Ω → φ g = ρ (g * z) * (ρ z)⁻¹ := fun g z h1 h2 =>
    generic3_indep hmul hgen (hzf g) (hgzf g) h1 h2
  refine ⟨MonoidHom.mk' φ fun g h => ?_, fun x hx => ?_⟩
  · obtain ⟨z, hz, hL⟩ := hgen [h, g * h] (by simp)
    have h1 : h * z ∈ Ω := hL _ (by simp)
    have h2 : g * h * z ∈ Ω := hL _ (by simp)
    rw [hφ (g * h) z hz h2, hφ h z hz h1, hφ g (h * z) h1 (by simpa [mul_assoc] using h2)]
    simp only [mul_assoc]
    group
  · obtain ⟨z, hz, hL⟩ := hgen [x] (by simp)
    have h1 : x * z ∈ Ω := hL _ (by simp)
    show φ x = ρ x
    rw [hφ x z hz h1, hmul x z hx hz h1]
    group

end Extend

variable {g : ℕ} {k : Type v} [Field k]

/-- Polynomial in `t` of degree at most $g$ evaluating to $\det(A + tB)$. -/
lemma exists_poly_det_le (A B : Matrix (Fin g) (Fin g) k) :
    ∃ p : k[X], p.natDegree ≤ g ∧ ∀ t : k, p.eval t = (A + t • B).det := by
  refine ⟨((X : k[X]) • B.map C + A.map C).det, ?_, fun t => ?_⟩
  · simpa using natDegree_det_X_add_C_le B A
  · have := RingHom.map_det (Polynomial.evalRingHom t) ((X : k[X]) • B.map C + A.map C)
    rw [Polynomial.coe_evalRingHom] at this
    rw [this]
    congr 1
    ext p q
    simp
    ring

/-- Over a field with more than $|S| \cdot g$ elements, finitely many "lines" $t \mapsto A_j + tB_j$ (the list $S$)
each having a point of nonzero determinant have a common point of nonzero determinant. -/
lemma exists_forall_det_ne_card (S : List (Matrix (Fin g) (Fin g) k × Matrix (Fin g) (Fin g) k))
    (hk : ((S.length * g : ℕ) : Cardinal) < Cardinal.mk k)
    (h : ∀ q ∈ S, ∃ t : k, (q.1 + t • q.2).det ≠ 0) :
    ∃ t : k, ∀ q ∈ S, (q.1 + t • q.2).det ≠ 0 := by
  classical
  choose p hpdeg hp using fun q : Matrix (Fin g) (Fin g) k × Matrix (Fin g) (Fin g) k =>
    exists_poly_det_le q.1 q.2
  have hne : (S.map p).prod ≠ 0 := by
    rw [Ne, List.prod_eq_zero_iff, List.mem_map]
    rintro ⟨q, hq, hq0⟩
    obtain ⟨t, ht⟩ := h q hq
    have := hp q t
    rw [hq0, Polynomial.eval_zero] at this
    exact ht this.symm
  have hdeg : (S.map p).prod.natDegree ≤ S.length * g := by
    refine (natDegree_list_prod_le _).trans ?_
    rw [List.map_map]
    refine (List.sum_le_length_nsmul _ g ?_).trans (by simp)
    intro n hn
    rw [List.mem_map] at hn
    obtain ⟨q, -, rfl⟩ := hn
    exact hpdeg q
  obtain ⟨t, ht⟩ := exists_eval_ne_zero_of_natDegree_lt_card _ hne
    (lt_of_le_of_lt (by exact_mod_cast hdeg) hk)
  refine ⟨t, fun q hq h0 => ht ?_⟩
  rw [Polynomial.eval_list_prod]
  apply List.prod_eq_zero
  rw [List.map_map, List.mem_map]
  exact ⟨q, hq, by simp [Function.comp, hp, h0]⟩

/-- **A common symmetric $T$ for a short list of $\gamma$'s.** Over a field $k$ with more than $|L| \cdot g$ elements
(hypothesis `hk`), for a list $L$ of elements of $\mathrm{Sp}_{2g}(k)$ there is a symmetric $T$ with
$\det(c_\gamma T + d_\gamma) \ne 0$ for all $\gamma \in L$, where $c_\gamma = $ `toBlocks₂₁ γ`, $d_\gamma = $ `toBlocks₂₂ γ`. -/
@[kb "kudla1996" "§I.1 (the big cell of $\\mathrm{Sp}_{2g}$) [unverified]"]
theorem exists_symm_det_ne_list_card (L : List (Sp g k))
    (hk : ((L.length * g : ℕ) : Cardinal) < Cardinal.mk k) :
    ∃ T : Matrix (Fin g) (Fin g) k, Tᵀ = T ∧ ∀ γ ∈ L,
      (toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) * T +
        toBlocks₂₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)).det ≠ 0 := by
  induction L with
  | nil => exact ⟨0, transpose_zero, by simp⟩
  | cons γ₀ L ih =>
    have hkL : ((L.length * g : ℕ) : Cardinal) < Cardinal.mk k := by
      refine lt_of_le_of_lt ?_ hk
      exact_mod_cast Nat.mul_le_mul_right g (by simp)
    obtain ⟨T₁, hT₁, h₁⟩ := ih hkL
    obtain ⟨T₂, hT₂, h₂⟩ := exists_symm_det_ne γ₀
    let blk : Sp g k → Matrix (Fin g) (Fin g) k × Matrix (Fin g) (Fin g) k := fun γ =>
      (toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) * T₁ +
        toBlocks₂₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k),
       toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) * (T₂ - T₁))
    have hline : ∀ (γ : Sp g k) (t : k),
        (toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) * (T₁ + t • (T₂ - T₁)) +
          toBlocks₂₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)) = (blk γ).1 + t • (blk γ).2 := by
      intro γ t
      simp only [blk, Matrix.mul_add, Matrix.mul_smul]
      abel
    obtain ⟨t, ht⟩ := exists_forall_det_ne_card ((γ₀ :: L).map blk) (by simpa using hk) (by
      intro q hq
      rw [List.mem_map] at hq
      obtain ⟨γ, hγ, rfl⟩ := hq
      rcases List.mem_cons.1 hγ with rfl | hγL
      · refine ⟨1, ?_⟩
        rw [← hline γ 1, one_smul, add_sub_cancel]
        exact h₂
      · refine ⟨0, ?_⟩
        rw [zero_smul, add_zero]
        exact h₁ γ hγL)
    refine ⟨T₁ + t • (T₂ - T₁), ?_, ?_⟩
    · rw [transpose_add, transpose_smul, transpose_sub, hT₁, hT₂]
    · intro γ hγ
      rw [hline]
      exact ht _ (List.mem_map.2 ⟨γ, hγ, rfl⟩)

/-- **Generic translate into the big cell, short lists.** Over a field $k$ with more than $|L| \cdot g$ elements, for a
list $L$ of elements of $\mathrm{Sp}_{2g}(k)$ there is a symmetric $T$ (`hT : Tᵀ = T`) such that the lower-left block of
$\gamma\,n(T)\,w$ is invertible for every $\gamma \in L$. -/
theorem exists_spN_spW_generic_card (L : List (Sp g k))
    (hk : ((L.length * g : ℕ) : Cardinal) < Cardinal.mk k) :
    ∃ T : Matrix (Fin g) (Fin g) k, ∃ hT : Tᵀ = T, ∀ γ ∈ L,
      (toBlocks₂₁ ((γ * (spN T hT * spW) : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)).det ≠ 0 := by
  obtain ⟨T, hT, h⟩ := exists_symm_det_ne_list_card L hk
  refine ⟨T, hT, fun γ hγ => ?_⟩
  rw [toBlocks₂₁_mul_spN_spW, det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (h γ hγ)

/-- **The presentation of $\mathrm{Sp}_{2g}(k)$ by the Siegel parabolic and $w$, for every field with more than $3g$
elements** (hypothesis `hk`: $3g < \#k$; every genus $g$): the named input `SiegelPresentation g k` holds. Covers every
infinite field and every finite field $\mathbb F_q$ with $q > 3g$. See the module docstring for the method. -/
@[kb "kudla1996" "§I.1 (generators $m(a)$, $n(b)$, $w$ of $\\mathrm{Sp}(W)$ and their relations) [unverified]"]
theorem siegelPresentation_of_card (hk : ((3 * g : ℕ) : Cardinal) < Cardinal.mk k) :
    SiegelPresentation.{u} g k := by
  refine ⟨fun M _ N A W hR => ?_⟩
  have hU := siegelRelations_units hR
  obtain ⟨φ, hφ⟩ := exists_monoidHom_of_generic3 (bigCell (g := g) (k := k))
    (rhoCell (unitsN hR) (unitsA hR) (unitsW hR)) (fun x y hx hy hxy => rhoCell_mul hU hx hy hxy)
    (fun L hL => by
      obtain ⟨T, hT, hL⟩ := exists_spN_spW_generic_card L
        (lt_of_le_of_lt (by exact_mod_cast Nat.mul_le_mul_right g hL) hk)
      exact ⟨spN T hT * spW, spN_spW_mem_bigCell T hT, hL⟩)
  have hW : φ spW = unitsW hR := by rw [hφ _ spW_mem_bigCell, rhoCell_spW hU]
  refine ⟨(Units.coeHom M).comp φ, fun B hB => ?_, fun a => ?_, ?_⟩
  · have h := hφ _ (spN_spW_mem_bigCell B hB)
    rw [rhoCell_spN_spW hU, map_mul, hW] at h
    have h' := mul_right_cancel h
    simp [h', unitsN_val hR hB]
  · have h := hφ _ (spM_spW_mem_bigCell a)
    rw [rhoCell_spM_spW hU, map_mul, hW] at h
    have h' := mul_right_cancel h
    simp [h', unitsA]
  · simp [hW, unitsW]

/-- **The presentation of $\mathrm{Sp}_{2g}(\mathbb F_q)$ for $q > 3g$**: for a finite field $k$ with more than $3g$
elements (hypothesis `hk : 3 * g < Fintype.card k`), the named input `SiegelPresentation g k` holds. -/
@[kb "kudla1996" "§I.1 (generators $m(a)$, $n(b)$, $w$ of $\\mathrm{Sp}(W)$ and their relations) [unverified]"]
theorem siegelPresentation_of_fintype [Fintype k] (hk : 3 * g < Fintype.card k) :
    SiegelPresentation.{u} g k :=
  siegelPresentation_of_card (by rw [Cardinal.mk_fintype]; exact_mod_cast hk)

end QuadFormsKB.WeilRep.Genus
