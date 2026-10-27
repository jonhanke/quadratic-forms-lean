import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.OMeara.Sec58Class
import QuadFormsKB.Witt.Represents

/-!
# O'Meara 58:8: classification by dimension, discriminant and Hasse algebra

O'Meara, *Introduction to Quadratic Forms* (1963), §58, p. 153: over a field in which every regular quinary
space is isotropic, regular quadratic spaces are classified by $\dim V$, $dV$ and $S V$.

The hypothesis on the field is the named condition `QuinaryIsotropic`.  The proof follows the book: the
cases $n \le 3$ are 58:4, and for $n \ge 4$ both spaces represent $1$ (42:11), so both split off
$\langle 1\rangle$, and induction applies.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Class58

open Hasse58 CSA52 Module Quaternions57

universe u

/-! ### Isotropic regular spaces are universal -/

section Universal

variable {F : Type u} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

/-- **A regular isotropic space represents every element** (O'Meara 42:11 direction used in 58:8): if $Q(v) = 0$
with $v \ne 0$ and $V$ is regular, then for every $c \in F$ there is $x$ with $Q(x) = c$. -/
theorem exists_eq_of_isotropic (hQ : (QuadraticMap.associated Q).Nondegenerate) {v : V} (hv : v ≠ 0)
    (h0 : Q v = 0) (c : F) : ∃ x : V, Q x = c := by
  obtain ⟨w, hw⟩ : ∃ w, bil Q v w ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (hQ.1 v h)
  have h2 := two_ne_zero' F
  set s : F := (c - Q w) / (2 * bil Q v w) with hs
  refine ⟨s • v + w, ?_⟩
  have e := two_mul_bil Q (s • v) w
  have hb : bil Q (s • v) w = s * bil Q v w := by
    show QuadraticMap.associated Q (s • v) w = s * QuadraticMap.associated Q v w
    simp
  rw [hb, QuadraticMap.map_smul, h0, smul_zero] at e
  have : Q (s • v + w) = 2 * (s * bil Q v w) + Q w := by linear_combination -e
  rw [this, hs]
  field_simp
  ring

end Universal

/-! ### The condition on the field -/

/-- **Every regular quinary space over $F$ is isotropic** (the hypothesis of O'Meara 58:8): for every
quadratic space $(V, Q)$ over $F$ with $\dim V = 5$ and $V$ regular (the associated bilinear form is
nondegenerate) there is $v \ne 0$ with $Q(v) = 0$.  The spaces range over the universe of $F$. -/
def QuinaryIsotropic (F : Type u) [Field F] [Invertible (2 : F)] : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V),
    finrank F V = 5 → (QuadraticMap.associated Q).Nondegenerate → ∃ v : V, v ≠ 0 ∧ Q v = 0

/-! ### Splitting off $\langle 1\rangle$ -/

section Split

variable {F : Type u} [Field F] [Invertible (2 : F)]

/-- Under `QuinaryIsotropic`, a diagonal form of dimension $n \ge 4$ represents $1$ (the step "$U \perp
\langle -1\rangle$ is isotropic, hence $1 \in Q(U)$" of the proof of 58:8, applied to the first four
coordinates). -/
theorem exists_dg_eq_one (hF : QuinaryIsotropic F) {n : ℕ} (hn : 4 ≤ n) (f : Fin n → Fˣ) :
    ∃ y : Fin n → F, dg f y = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  let h5 : Fin 5 → Fˣ := Fin.snoc (fun i : Fin 4 => f (Fin.castAdd m i)) (-1)
  obtain ⟨x, hx, hx0⟩ := hF (Fin 5 → F) (dg h5) (by simp) (dg_nondegenerate h5)
  rw [dg_apply, Fin.sum_univ_castSucc] at hx0
  simp only [h5, Fin.snoc_castSucc, Fin.snoc_last, Units.val_neg, Units.val_one] at hx0
  let y : Fin (4 + m) → F := Fin.append (fun i : Fin 4 => x (Fin.castSucc i)) 0
  have hy : dg f y = ∑ i : Fin 4, (f (Fin.castAdd m i) : F) * x (Fin.castSucc i) ^ 2 := by
    rw [dg_apply, Fin.sum_univ_add]
    simp [y]
  by_cases hl : x (Fin.last 4) = 0
  · have hyne : y ≠ 0 := by
      intro h
      apply hx
      funext i
      refine Fin.lastCases hl (fun j => ?_) i
      have := congrFun h (Fin.castAdd m j)
      simpa [y] using this
    have hy0 : dg f y = 0 := by rw [hy]; linear_combination hx0 + x (Fin.last 4) * hl
    exact exists_eq_of_isotropic (dg_nondegenerate f) hyne hy0 1
  · refine ⟨(x (Fin.last 4))⁻¹ • y, ?_⟩
    rw [QuadraticMap.map_smul, hy, smul_eq_mul]
    have : ∑ i : Fin 4, (f (Fin.castAdd m i) : F) * x (Fin.castSucc i) ^ 2 = x (Fin.last 4) ^ 2 := by
      linear_combination hx0
    rw [this]
    field_simp

/-- A diagonal form representing $1$ is isometric to $\langle 1\rangle \perp \langle f'_0, \ldots,
f'_{m-1}\rangle$ for some units $f'$ (an orthogonal basis starting with a vector of value $1$,
`QuadForm.exists_orthogonal_basis_cons`). -/
theorem exists_equivalent_cons_one {m : ℕ} (f : Fin (m + 1) → Fˣ) {y : Fin (m + 1) → F}
    (hy : dg f y = 1) :
    ∃ f' : Fin m → Fˣ, (dg f : QuadraticForm F (Fin (m + 1) → F)).Equivalent
      (dg (Fin.cons 1 f' : Fin (m + 1) → Fˣ)) := by
  have hQ := dg_nondegenerate f
  have hyy : QuadraticMap.associated (dg f : QuadraticForm F (Fin (m + 1) → F)) y y ≠ 0 := by
    rw [QuadraticMap.associated_eq_self_apply, hy]; exact one_ne_zero
  obtain ⟨v, hv, hv0⟩ := QuadForm.exists_orthogonal_basis_cons
    ⟨fun a b => QuadraticMap.associated_isSymm F (dg f : QuadraticForm F (Fin (m + 1) → F)) a b⟩ hyy (d := m) (by simp)
  have hX : IsOrthogonalBasis (dg f : QuadraticForm F (Fin (m + 1) → F)) v := by
    rw [LinearMap.isOrthoᵢ_def] at hv
    exact hv
  refine ⟨Fin.tail (vf hQ v hX), ?_⟩
  have h0 : vf hQ v hX 0 = 1 := by
    apply Units.ext
    simp [vf, hv0, hy]
  have : (Fin.cons 1 (Fin.tail (vf hQ v hX)) : Fin (m + 1) → Fˣ) = vf hQ v hX := by
    rw [← h0, Fin.cons_self_tail]
  rw [this]
  exact equivalent_dg_vf hQ v hX

theorem vf_basisFun {n : ℕ} (f : Fin n → Fˣ) :
    vf (dg_nondegenerate f) (Pi.basisFun F (Fin n)) (isOrthogonalBasis_pi f) = f := by
  funext i
  apply Units.ext
  simp only [vf, Units.val_mk0, Pi.basisFun_apply]
  exact dg_single f i

/-- Isometric diagonal forms have the same invariants. -/
theorem sameInv_of_equivalent_dg {n : ℕ} {f g : Fin n → Fˣ}
    (h : (dg f : QuadraticForm F (Fin n → F)).Equivalent (dg g)) : SameInv f g := by
  obtain ⟨e⟩ := h
  have := sameInv_of_equivalent (dg_nondegenerate f) (dg_nondegenerate g) e
    (Pi.basisFun F (Fin n)) (Pi.basisFun F (Fin n)) (isOrthogonalBasis_pi f) (isOrthogonalBasis_pi g)
  rwa [vf_basisFun, vf_basisFun] at this

/-- Removing a common leading value $1$ preserves equal invariants. -/
theorem sameInv_of_cons_one {m : ℕ} {f g : Fin m → Fˣ}
    (h : SameInv (Fin.cons 1 f : Fin (m + 1) → Fˣ) (Fin.cons 1 g : Fin (m + 1) → Fˣ)) :
    SameInv f g := by
  obtain ⟨⟨t, ht⟩, hb⟩ := h
  refine ⟨⟨t, by simpa [Fin.prod_univ_succ] using ht⟩, cls_eq_iff.1 ?_⟩
  have hc := cls_eq_iff.2 hb
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ] at hc
  rwa [cls_hasseAlg_cons_one, cls_hasseAlg_cons_one] at hc

/-- **The classification of diagonal forms under `QuinaryIsotropic`** (the core of 58:8). -/
theorem equivalent_dg_of_sameInv_of_quinaryIsotropic (hF : QuinaryIsotropic F) :
    ∀ (n : ℕ) (f g : Fin n → Fˣ), SameInv f g →
      (dg f : QuadraticForm F (Fin n → F)).Equivalent (dg g)
  | 0, f, g, h => equivalent_dg_of_sameInv_le_three (by norm_num) f g h
  | 1, f, g, h => equivalent_dg_of_sameInv_le_three (by norm_num) f g h
  | 2, f, g, h => equivalent_dg_of_sameInv_le_three (by norm_num) f g h
  | 3, f, g, h => equivalent_dg_of_sameInv_le_three (by norm_num) f g h
  | m + 4, f, g, h => by
    obtain ⟨y, hy⟩ := exists_dg_eq_one hF (by omega) f
    obtain ⟨z, hz⟩ := exists_dg_eq_one hF (by omega) g
    obtain ⟨f', hf'⟩ := exists_equivalent_cons_one (m := m + 3) f hy
    obtain ⟨g', hg'⟩ := exists_equivalent_cons_one (m := m + 3) g hz
    have h' : SameInv f' g' := sameInv_of_cons_one
      (((sameInv_of_equivalent_dg hf').symm.trans h).trans (sameInv_of_equivalent_dg hg'))
    have ih := equivalent_dg_of_sameInv_of_quinaryIsotropic hF (m + 3) f' g' h'
    exact (hf'.trans (equivalent_dg_cons_congr 1 ih)).trans hg'.symm

end Split

/-! ### 58:8 -/

section Main588

variable {F : Type u} [Field F] [Invertible (2 : F)]
variable {V W : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W] {Q : QuadraticForm F V} {Q' : QuadraticForm F W}

/-- **O'Meara 58:8** (1963, p. 153): *let $F$ be a field with the property that every regular quinary space over
it is isotropic.  Then two regular quadratic spaces $U$ and $V$ over $F$ are isometric if and only if
$\dim U = \dim V$, $dU = dV$, $S U \sim S V$.*

**Formalization.**  The field hypothesis is the named condition `QuinaryIsotropic F` (for spaces in the universe
of $F$).  The spaces are $V$ and $W$ here (the book's $U$ and $V$), regular and finite-dimensional over $F$
($2$ invertible), with orthogonal bases $X, Y$ indexed by `Fin n` (so equal dimension $n$ is built in, every
$n \ge 0$ allowed).  As in 58:4 (`isometric_iff_invariants_of_dim_le_three`), the discriminants are
$\prod_i Q(X_i)$ and $\prod_i Q'(Y_i)$ compared modulo squares of $F^\times$, and $S V$, $S W$ are the Hasse
algebras `hasseAlg` of the value lists, compared by `IsBrauerEquivalent`; by 58:2 the right-hand side does not
depend on the bases.

*Proof* (as in the book): $n \le 3$ is 58:4; for $n \ge 4$ the space $\langle a_0,\dots,a_3\rangle \perp
\langle -1\rangle$ is a regular quinary space, hence isotropic, so $V$ represents $1$ (either directly or because
$V$ is then isotropic and regular, `exists_eq_of_isotropic`); likewise $W$; split off $\langle 1\rangle$
(`exists_equivalent_cons_one`), the complements have the same invariants, and induction finishes. -/
@[kb "omeara1963" "§58, 58:8, p. 153"]
theorem isometric_iff_invariants_of_quinaryIsotropic (hF : QuinaryIsotropic F)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) (hQ' : (QuadraticMap.associated Q').Nondegenerate)
    {n : ℕ} (X : Basis (Fin n) F V) (Y : Basis (Fin n) F W) (hX : IsOrthogonalBasis Q X)
    (hY : IsOrthogonalBasis Q' Y) :
    Nonempty (Q.IsometryEquiv Q') ↔
      ((∃ t : Fˣ, ∏ i, Q' (Y i) = (t : F) ^ 2 * ∏ i, Q (X i)) ∧
        IsBrauerEquivalent (hasseAlg (Rev.values hQ X hX)) (hasseAlg (Rev.values hQ' Y hY))) :=
  (equivalent_iff_sameInv hQ hQ' X Y hX hY (equivalent_dg_of_sameInv_of_quinaryIsotropic hF n)).trans
    (sameInv_iff hQ hQ' X Y hX hY)

end Main588

end QuadFormsKB.OMeara.Class58
