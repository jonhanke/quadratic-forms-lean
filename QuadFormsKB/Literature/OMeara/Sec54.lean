/-
# O'Meara §54: the Clifford algebra and the spinor norm (54:4, 54:5, 54:6)

**Setting.** A field $F$ of characteristic $\ne 2$, a finite-dimensional quadratic space $(V, Q)$ over $F$, and
O'Meara's bilinear form $B$ = `bil Q` = `QuadraticMap.associated Q` (so $B(x,x) = Q(x)$). *Regular* means
`(QuadraticMap.associated Q).Nondegenerate`. O'Meara's Clifford algebra $C$ (an algebra compatible with $V$ with the
universal property of §54) is Mathlib's `CliffordAlgebra Q`, with $V \hookrightarrow C$ given by `CliffordAlgebra.ι Q`
and $\iota(x)^2 = Q(x)1$ (`CliffordAlgebra.ι_sq_scalar`).

**Proves**
* `mem_range_algebraMap_of_mem_even_of_commute` (**54:4**): an even element of $C$ commuting with $V$ lies in $F1$;
* `existsUnique_algEquiv_op` (**54:5**): there is exactly one algebra anti-isomorphism of $C$ that is the identity
  on $V$ (regularity is not needed);
* `isSquare_prod_of_prod_symmetry_eq_one` (**54:6**): if $\tau_{u_1}\cdots\tau_{u_r} = 1$ then
  $Q(u_1)\cdots Q(u_r)$ is a square;
* `HasSpinorNorm.eq_mul_sq` (§55, p. 137): the spinor norm is well defined, i.e. two spinor norms of the same
  rotation differ by a nonzero square.

This is the general-field version of `Lattices.isSquare_valProd_of_symmProd_eq_one` (coordinates over a number field).
The proof of 54:6 follows that library proof and not O'Meara's: it shows that an element $g$ with
$\alpha(g)\iota(x) = \iota(x)g$ for all $x$ ($\alpha$ the main involution) is a scalar, using only that $C$ is spanned
by the words in an orthogonal basis (the basis theorem $\dim C = 2^n$, 54:3a, is not used); 54:4 is then the case of an
even element, where $\alpha(g) = g$.
-/
import QuadFormsKB.Literature.OMeara.Sec92Spinor
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading

open CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

/-! Helper lemmas live in the sub-namespace `Cl54` to keep names globally unique. -/
namespace Cl54

section Setup

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

theorem polar_eq_two_mul_bil (x y : V) : QuadraticMap.polar Q x y = 2 * bil Q x y := by
  have h : Q (x + y) = Q x + Q y + 2 * bil Q x y := by
    rw [← bil_self Q (x + y), bil_add_left, bil_add_right, bil_add_right, bil_comm Q y x, bil_self, bil_self]
    ring
  simp only [QuadraticMap.polar]
  rw [h]; ring

/-- The product of the symmetries $\tau_{u_1}\cdots\tau_{u_r}$ of an anisotropic list (the form of the product used
in `HasSpinorNorm`, without `attach`). -/
def symProd (l : List V) (hl : ∀ u ∈ l, Q u ≠ 0) : V ≃ₗ[F] V := (l.pmap (symmetry Q) hl).prod

theorem attach_prod_eq_symProd (l : List V) (hl : ∀ u ∈ l, Q u ≠ 0) :
    (l.attach.map fun u => symmetry Q u.1 (hl u.1 u.2)).prod = symProd Q l hl := by
  rw [symProd, List.pmap_eq_map_attach]

theorem symProd_nil : symProd Q [] (by simp) = 1 := rfl

theorem symProd_cons {x : V} {l : List V} (hl : ∀ u ∈ x :: l, Q u ≠ 0) :
    symProd Q (x :: l) hl = symmetry Q x (hl x List.mem_cons_self) *
      symProd Q l (fun u hu => hl u (List.mem_cons_of_mem x hu)) := by
  simp [symProd, List.pmap]

theorem symProd_append {l l' : List V} (hl : ∀ u ∈ l ++ l', Q u ≠ 0) :
    symProd Q (l ++ l') hl = symProd Q l (fun u hu => hl u (List.mem_append_left _ hu)) *
      symProd Q l' (fun u hu => hl u (List.mem_append_right _ hu)) := by
  simp [symProd, List.pmap_append]

theorem symProd_reverse_right (l : List V) (hl : ∀ u ∈ l, Q u ≠ 0) :
    symProd Q l hl * symProd Q l.reverse (fun u hu => hl u (List.mem_reverse.mp hu)) = 1 := by
  induction l with
  | nil => simp [symProd]
  | cons x l ih =>
    have hl' : ∀ u ∈ l, Q u ≠ 0 := fun u hu => hl u (List.mem_cons_of_mem x hu)
    have hx := hl x List.mem_cons_self
    have h2 : symProd Q (x :: l).reverse (fun u hu => hl u (List.mem_reverse.mp hu)) =
        symProd Q l.reverse (fun u hu => hl' u (List.mem_reverse.mp hu)) * symmetry Q x hx := by
      have := symProd_append Q (l := l.reverse) (l' := [x]) (by
        intro u hu
        exact hl u (List.mem_reverse.mp (by simpa using hu)))
      simp only [List.reverse_cons]
      rw [this]
      congr 1
    rw [h2, symProd_cons Q hl]
    calc symmetry Q x hx * symProd Q l hl' *
          (symProd Q l.reverse (fun u hu => hl' u (List.mem_reverse.mp hu)) * symmetry Q x hx)
        = symmetry Q x hx * (symProd Q l hl' *
          symProd Q l.reverse (fun u hu => hl' u (List.mem_reverse.mp hu))) * symmetry Q x hx := by
          simp only [mul_assoc]
      _ = 1 := by
          rw [ih hl']
          ext y
          simp [symmetry_symmetry]

end Setup

section Words

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- $-\iota(x)\iota(z) = \iota(\tau_x z)\,\iota(x)$ for anisotropic $x$. -/
theorem neg_ι_mul_ι {x : V} (hx : Q x ≠ 0) (z : V) :
    -(ι Q x * ι Q z) = ι Q (symmetry Q x hx z) * ι Q x := by
  rw [symmetry_apply, map_sub, map_smul, sub_mul, smul_mul_assoc, ι_sq_scalar,
    Algebra.smul_def, ← RingHom.map_mul, div_mul_cancel₀ _ hx, ι_mul_ι_comm, polar_eq_two_mul_bil, bil_comm Q z x]
  abel

/-- The Clifford word $\iota(x_1)\cdots\iota(x_r)$. -/
def cw (xs : List V) : CliffordAlgebra Q := (xs.map (ι Q)).prod

/-- **Twisted conjugation by a word:** $\alpha(g)\,\iota(z) = \iota(\tau_{x_1}\cdots\tau_{x_r}z)\,g$ for
$g = \iota(x_1)\cdots\iota(x_r)$. -/
theorem involute_cw_mul_ι (xs : List V) (hxs : ∀ x ∈ xs, Q x ≠ 0) (z : V) :
    involute (cw Q xs) * ι Q z = ι Q (symProd Q xs hxs z) * cw Q xs := by
  induction xs generalizing z with
  | nil => simp [cw, symProd]
  | cons x xs ih =>
    have hx := hxs x List.mem_cons_self
    have ih' := ih (fun y hy => hxs y (List.mem_cons_of_mem x hy))
    simp only [cw, List.map_cons, List.prod_cons, map_mul, involute_ι] at ih' ⊢
    rw [symProd_cons Q hxs, LinearEquiv.mul_apply, mul_assoc, ih', neg_mul, ← mul_assoc, ← neg_mul,
      neg_ι_mul_ι Q hx, mul_assoc]

/-- **The norm of a word:** $g^t g = Q(x_1)\cdots Q(x_r)$. -/
theorem reverse_cw_mul_cw (xs : List V) :
    reverse (cw Q xs) * cw Q xs = algebraMap F _ (xs.map Q).prod := by
  induction xs with
  | nil => simp [cw]
  | cons x xs ih =>
    simp only [cw, List.map_cons, List.prod_cons, reverse.map_mul, reverse_ι] at ih ⊢
    rw [show reverse (List.map (ι Q) xs).prod * ι Q x * (ι Q x * (List.map (ι Q) xs).prod)
        = reverse (List.map (ι Q) xs).prod * (ι Q x * ι Q x) * (List.map (ι Q) xs).prod
        by simp only [mul_assoc], ι_sq_scalar, ← Algebra.commutes, mul_assoc, ih, ← map_mul]

end Words

section Basis

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) {n : ℕ} (e : Module.Basis (Fin n) F V)

/-- $u_j = \iota(e_j)$. -/
abbrev ub (j : Fin n) : CliffordAlgebra Q := ι Q (e j)

/-- The word $u_{j_1}\cdots u_{j_k}$ in the basis vectors. -/
def bw (l : List (Fin n)) : CliffordAlgebra Q := (l.map (ub Q e)).prod

theorem bw_nil : bw Q e [] = (1 : CliffordAlgebra Q) := rfl

theorem bw_cons (i : Fin n) (l : List (Fin n)) : bw Q e (i :: l) = ub Q e i * bw Q e l := rfl

theorem bw_append (l l' : List (Fin n)) : bw Q e (l ++ l') = bw Q e l * bw Q e l' := by
  simp [bw]

/-- **Every element of $C(V)$ is a combination of basis words.** -/
theorem mem_span_bw (g : CliffordAlgebra Q) : g ∈ Submodule.span F (Set.range (bw Q e)) := by
  induction g using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨[], rfl⟩)
  | ι v =>
    rw [← e.sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[i], by simp [bw]⟩)
  | mul a b ha hb =>
    have := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨l, rfl⟩, _, ⟨l', rfl⟩, rfl⟩
    exact ⟨l ++ l', bw_append Q e l l'⟩
  | add a b ha hb => exact Submodule.add_mem _ ha hb

/-- The averaging operator $P_j = \tfrac12(1 + T_j)$, $T_j(z) = Q(e_j)^{-1}u_j\,\alpha(z)\,u_j$. -/
def Pj (j : Fin n) : CliffordAlgebra Q →ₗ[F] CliffordAlgebra Q :=
  (1 / 2 : F) • (LinearMap.id + (Q (e j))⁻¹ •
    (LinearMap.mulLeft F (ub Q e j) ∘ₗ LinearMap.mulRight F (ub Q e j) ∘ₗ
      (involute : CliffordAlgebra Q →ₐ[F] _).toLinearMap))

theorem Pj_apply (j : Fin n) (z : CliffordAlgebra Q) :
    Pj Q e j z = (1 / 2 : F) • (z + (Q (e j))⁻¹ • (ub Q e j * (involute z * ub Q e j))) := by
  rfl

variable (he : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0) (hea : ∀ i, Q (e i) ≠ 0)
include he hea

theorem ub_anticomm {i j : Fin n} (hij : i ≠ j) : ub Q e j * ub Q e i = -(ub Q e i * ub Q e j) := by
  rw [ι_mul_ι_comm, polar_eq_two_mul_bil, he j i hij.symm, mul_zero, map_zero, zero_sub]

/-- $u_j\,w = (-1)^{|l| + \#_j(l)}\,w\,u_j$ for the word $w = u_l$. -/
theorem ub_mul_bw (j : Fin n) (l : List (Fin n)) :
    ub Q e j * bw Q e l = (-1 : F) ^ (l.length + l.count j) • (bw Q e l * ub Q e j) := by
  induction l with
  | nil => simp [bw_nil]
  | cons i l ih =>
    rw [bw_cons, ← mul_assoc]
    by_cases hij : i = j
    · subst hij
      rw [ι_sq_scalar, ih, smul_mul_assoc, mul_assoc, ι_sq_scalar, smul_smul, ← Algebra.commutes]
      simp only [List.length_cons, List.count_cons_self]
      rw [← pow_add, show l.length + 1 + (l.count i + 1) + (l.length + l.count i) =
        2 * (l.length + l.count i + 1) by ring, pow_mul]
      simp
    · rw [ub_anticomm Q e he hea hij, neg_mul, mul_assoc, ih, mul_smul_comm, ← mul_assoc]
      simp only [List.length_cons, List.count_cons, beq_iff_eq, hij, ite_false, add_zero]
      rw [show l.length + 1 + l.count j = l.length + l.count j + 1 by ring, pow_succ, mul_neg_one, neg_smul]

omit he hea in
theorem involute_bw (l : List (Fin n)) : involute (bw Q e l) = (-1 : F) ^ l.length • bw Q e l := by
  induction l with
  | nil => simp [bw_nil]
  | cons i l ih =>
    rw [bw_cons, map_mul, ih, involute_ι, List.length_cons, pow_succ']
    simp

/-- $u_j\,\alpha(u_l)\,u_j = (-1)^{\#_j(l)}Q(e_j)\,u_l$. -/
theorem ub_mul_involute_bw_mul_ub (j : Fin n) (l : List (Fin n)) :
    ub Q e j * (involute (bw Q e l) * ub Q e j) = ((-1 : F) ^ l.count j * Q (e j)) • bw Q e l := by
  rw [involute_bw, smul_mul_assoc, mul_smul_comm, ← mul_assoc, ub_mul_bw Q e he hea, smul_mul_assoc, mul_assoc,
    ι_sq_scalar, ← Algebra.commutes, ← Algebra.smul_def, smul_smul, smul_smul]
  congr 1
  rw [pow_add, show (-1 : F) ^ l.length * ((-1) ^ l.length * (-1) ^ l.count j) =
    ((-1) ^ l.length) ^ 2 * (-1) ^ l.count j by ring, ← pow_mul, mul_comm l.length 2, pow_mul]
  simp

/-- **A word in which every basis vector occurs an even number of times is a scalar.** -/
theorem bw_mem_range_of_even (l : List (Fin n)) (hl : ∀ j, Even (l.count j)) :
    bw Q e l ∈ Set.range (algebraMap F (CliffordAlgebra Q)) := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ m ih =>
    match l, hl with
    | [], _ => exact ⟨1, by simp [bw_nil]⟩
    | i :: l', hl =>
      have hodd : ¬ Even (l'.count i) := by
        have := hl i
        rw [List.count_cons_self, Nat.even_add_one] at this
        exact this
      have hmem : i ∈ l' := List.count_pos_iff.mp (Nat.pos_of_ne_zero fun h0 => hodd (h0 ▸ (⟨0, rfl⟩ : Even 0)))
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hmem
      have hst : ∀ j, Even ((s ++ t).count j) := by
        intro j
        have := hl j
        simp only [List.count_cons, List.count_append, beq_iff_eq] at this ⊢
        by_cases hj : i = j
        · subst hj
          simp only [ite_true] at this
          rw [show s.count i + (t.count i + 1) + 1 = s.count i + t.count i + 2 by ring] at this
          exact (Nat.even_add.mp this).mpr even_two
        · simp only [hj, ite_false, add_zero] at this
          exact this
      obtain ⟨c, hc⟩ := ih (s ++ t).length (by rw [← h]; simp) (s ++ t) hst rfl
      have key : bw Q e (i :: (s ++ i :: t)) =
          ((-1 : F) ^ (s.length + s.count i) * Q (e i)) • bw Q e (s ++ t) := by
        rw [bw_cons, bw_append, bw_cons, ← mul_assoc, ub_mul_bw Q e he hea, smul_mul_assoc, mul_assoc,
          ← mul_assoc (ub Q e i), ι_sq_scalar, ← mul_assoc, ← Algebra.commutes, mul_assoc,
          ← Algebra.smul_def, ← bw_append, smul_smul]
      refine ⟨(-1 : F) ^ (s.length + s.count i) * Q (e i) * c, ?_⟩
      rw [key, ← hc, Algebra.smul_def, ← RingHom.map_mul]

theorem Pj_bw (j : Fin n) (l : List (Fin n)) :
    Pj Q e j (bw Q e l) = if Even (l.count j) then bw Q e l else 0 := by
  rw [Pj_apply, ub_mul_involute_bw_mul_ub Q e he hea, smul_smul, mul_comm ((-1 : F) ^ l.count j),
    inv_mul_cancel_left₀ (hea j)]
  split_ifs with hc
  · rw [hc.neg_one_pow, one_smul, ← two_smul F, smul_smul]
    have : (2 : F) ≠ 0 := two_ne_zero
    field_simp
    simp
  · rw [(Nat.not_even_iff_odd.mp hc).neg_one_pow, neg_one_smul, add_neg_cancel, smul_zero]

theorem Pj_of_twisted {g : CliffordAlgebra Q} (j : Fin n)
    (hg : involute g * ub Q e j = ub Q e j * g) : Pj Q e j g = g := by
  rw [Pj_apply, hg, ← mul_assoc, ι_sq_scalar, ← Algebra.smul_def, smul_smul,
    inv_mul_cancel₀ (hea j), one_smul, ← two_smul F, smul_smul]
  have : (2 : F) ≠ 0 := two_ne_zero
  field_simp
  simp

/-- **The twisted center of $C(V)$ is $F$:** if $\alpha(g)\,\iota(e_j) = \iota(e_j)\,g$ for every vector $e_j$ of an
orthogonal basis of anisotropic vectors, then $g \in F1$. -/
theorem mem_range_algebraMap_of_twisted (g : CliffordAlgebra Q)
    (hg : ∀ j, involute g * ub Q e j = ub Q e j * g) :
    g ∈ Set.range (algebraMap F (CliffordAlgebra Q)) := by
  let S : ℕ → Submodule F (CliffordAlgebra Q) := fun k =>
    Submodule.span F {w | ∃ l : List (Fin n), (∀ j : Fin n, j.val < k → Even (l.count j)) ∧ bw Q e l = w}
  have step : ∀ k ≤ n, g ∈ S k := by
    intro k
    induction k with
    | zero =>
      intro _
      refine Submodule.span_mono ?_ (mem_span_bw Q e g)
      rintro _ ⟨l, rfl⟩
      exact ⟨l, fun j hj => absurd hj (Nat.not_lt_zero _), rfl⟩
    | succ k ih =>
      intro hk
      have hg' := ih (Nat.le_of_succ_le hk)
      rw [← Pj_of_twisted Q e he hea ⟨k, hk⟩ (hg _)]
      have : Pj Q e ⟨k, hk⟩ g ∈ (S k).map (Pj Q e ⟨k, hk⟩) := Submodule.mem_map_of_mem hg'
      rw [Submodule.map_span] at this
      refine Submodule.span_le.mpr ?_ this
      rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, Pj_bw Q e he hea]
      split_ifs with hc
      · refine Submodule.subset_span ⟨l, fun j hj => ?_, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · exact hl j hj
        · have : j = ⟨k, hk⟩ := Fin.ext hj
          rw [this]; exact hc
      · exact Submodule.zero_mem _
  have hn := step n le_rfl
  have hle : S n ≤ LinearMap.range (Algebra.linearMap F (CliffordAlgebra Q)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨c, hc⟩ := bw_mem_range_of_even Q e he hea l fun j => hl j j.2
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hle hn
  exact ⟨c, hc⟩

end Basis

section Regular

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- A regular space has an orthogonal basis of anisotropic vectors. -/
theorem exists_orthogonal_anisotropic_basis (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    ∃ e : Module.Basis (Fin (Module.finrank F V)) F V,
      (∀ i j, i ≠ j → bil Q (e i) (e j) = 0) ∧ ∀ i, Q (e i) ≠ 0 := by
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := (QuadraticMap.associated Q : LinearMap.BilinForm F V)) ⟨fun x y => by simpa using bil_comm Q x y⟩
  refine ⟨e, fun i j hij => he hij, fun i h0 => ?_⟩
  have hzero : ∀ y, bil Q (e i) y = 0 := by
    intro y
    have hy : (QuadraticMap.associated Q : LinearMap.BilinForm F V) (e i) = 0 := by
      refine e.ext fun j => ?_
      by_cases hij : i = j
      · subst hij
        simpa using h0
      · simpa using he hij
    exact congrArg (fun f => f y) hy
  exact e.ne_zero i (hQ.1 _ hzero)

end Regular

end Cl54

section Main

open Cl54

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **Proposition 54:4** (O'Meara 1973, p. 135): an even element of the Clifford algebra of a regular quadratic space
that commutes with every vector of $V$ is a scalar multiple of $1$. -/
@[kb "omeara1963" "§54, 54:4, p. 135"]
theorem mem_range_algebraMap_of_mem_even_of_commute (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {a : CliffordAlgebra Q} (ha : a ∈ CliffordAlgebra.even Q)
    (hc : ∀ x : V, a * CliffordAlgebra.ι Q x = CliffordAlgebra.ι Q x * a) :
    ∃ c : F, a = algebraMap F (CliffordAlgebra Q) c := by
  obtain ⟨e, he, hea⟩ := exists_orthogonal_anisotropic_basis Q hQ
  have hi : involute a = a := involute_eq_of_mem_even ha
  obtain ⟨c, hc'⟩ := mem_range_algebraMap_of_twisted Q e he hea a fun j => by
    rw [hi]; exact hc _
  exact ⟨c, hc'.symm⟩

/-- **Proposition 54:5** (O'Meara 1973, p. 136): the Clifford algebra has exactly one algebra anti-isomorphism
$C \to C$ that is the identity on $V$ (an algebra isomorphism onto the opposite algebra).

*Update (generalization):* regularity of $V$ is not needed (nor is $2$ invertible or finite dimensionality, though both
are in force in this file); existence is
Mathlib's `CliffordAlgebra.reverseOpEquiv` and uniqueness is the universal property. -/
@[kb "omeara1963" "§54, 54:5, p. 136"]
theorem existsUnique_algEquiv_op :
    ∃! f : CliffordAlgebra Q ≃ₐ[F] (CliffordAlgebra Q)ᵐᵒᵖ,
      ∀ x : V, f (CliffordAlgebra.ι Q x) = MulOpposite.op (CliffordAlgebra.ι Q x) := by
  refine ⟨CliffordAlgebra.reverseOpEquiv, fun x => CliffordAlgebra.reverseOp_ι x, ?_⟩
  intro f hf
  refine AlgEquiv.ext fun a => ?_
  have : f.toAlgHom = (CliffordAlgebra.reverseOpEquiv (Q := Q)).toAlgHom := by
    refine CliffordAlgebra.hom_ext (LinearMap.ext fun x => ?_)
    simp [hf x, CliffordAlgebra.reverseOp_ι, CliffordAlgebra.reverseOpEquiv]
  exact congrArg (fun φ : _ →ₐ[F] _ => φ a) this

/-- **Proposition 54:6** (O'Meara 1973, p. 136): in a regular quadratic space, if a product of symmetries
$\tau_{u_1}\cdots\tau_{u_r}$ is the identity, then $Q(u_1)\cdots Q(u_r)$ is a square in $F$.

(Stated with $\tau_{u_i}$ = `symmetry Q u_i`, so each $Q(u_i) \ne 0$.) The proof is not O'Meara's but a variant
(see the file docstring): it uses the main involution twisted center instead of the evenness of $r$; it needs only
that $C$ is spanned by words in an orthogonal basis. -/
@[kb "omeara1963" "§54, 54:6, p. 136"]
theorem isSquare_prod_of_prod_symmetry_eq_one (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (l : List V) (hl : ∀ u ∈ l, Q u ≠ 0)
    (h : (l.attach.map fun u => symmetry Q u.1 (hl u.1 u.2)).prod = 1) :
    IsSquare (l.map Q).prod := by
  rw [attach_prod_eq_symProd Q l hl] at h
  obtain ⟨e, he, hea⟩ := exists_orthogonal_anisotropic_basis Q hQ
  have htw : ∀ j, involute (cw Q l) * ub Q e j = ub Q e j * cw Q l := by
    intro j
    rw [involute_cw_mul_ι Q l hl, h]
    simp
  obtain ⟨c, hc⟩ := mem_range_algebraMap_of_twisted Q e he hea _ htw
  have h' := reverse_cw_mul_cw Q l
  rw [← hc, reverse.commutes, ← map_mul] at h'
  exact ⟨c, ((algebraMap F (CliffordAlgebra Q)).injective h').symm⟩

/-- **The spinor norm is well defined** (O'Meara 1973, §55, p. 137): if a rotation $\sigma$ has spinor norms $c$ and
$d$ (in the sense of `HasSpinorNorm`, each through some factorization into symmetries), then $c = ds^2$ for some
$s \in F^\times$. Proof as in the book: $\tau_{u_1}\cdots\tau_{u_r}\,\tau_{v_s}\cdots\tau_{v_1} = 1$, then 54:6. -/
@[kb "omeara1963" "§55, p. 137 (the spinor norm is well defined)"]
theorem HasSpinorNorm.eq_mul_sq (hQ : (QuadraticMap.associated Q).Nondegenerate) {σ : V ≃ₗ[F] V} {c d : F}
    (hc : HasSpinorNorm Q σ c) (hd : HasSpinorNorm Q σ d) : ∃ s : F, s ≠ 0 ∧ c = d * s ^ 2 := by
  obtain ⟨l, hl, hσ, s, hs, hp⟩ := hc
  obtain ⟨l', hl', hσ', s', hs', hp'⟩ := hd
  rw [attach_prod_eq_symProd Q l hl] at hσ
  rw [attach_prod_eq_symProd Q l' hl'] at hσ'
  have hll : ∀ u ∈ l ++ l'.reverse, Q u ≠ 0 := by
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hl u hu
    · exact hl' u (List.mem_reverse.mp hu)
  have h1 : ((List.attach (l ++ l'.reverse)).map (fun u => symmetry Q u.1 (hll u.1 u.2))).prod = 1 := by
    rw [attach_prod_eq_symProd Q _ hll, symProd_append, ← hσ, hσ']
    exact symProd_reverse_right Q l' hl'
  obtain ⟨r, hr⟩ := isSquare_prod_of_prod_symmetry_eq_one Q hQ _ hll h1
  have hne : ∀ m : List V, (∀ u ∈ m, Q u ≠ 0) → (m.map Q).prod ≠ 0 := fun m hm =>
    List.prod_ne_zero (by
      simp only [List.mem_map]
      rintro ⟨u, hu, h0⟩
      exact hm u hu h0)
  have hc0 : c ≠ 0 := by
    intro h
    have := hne l hl
    rw [hp, h] at this
    simp at this
  have hd0 : d ≠ 0 := by
    intro h
    have := hne l' hl'
    rw [hp', h] at this
    simp at this
  rw [List.map_append, List.prod_append, List.map_reverse, List.prod_reverse, hp, hp'] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp [hc0, hd0, hs, hs'] at hr
  refine ⟨r / (d * s * s'), div_ne_zero hr0 (mul_ne_zero (mul_ne_zero hd0 hs) hs'), ?_⟩
  have hdss : d * s * s' ≠ 0 := mul_ne_zero (mul_ne_zero hd0 hs) hs'
  field_simp
  linear_combination hr

end Main

end QuadFormsKB.OMeara
