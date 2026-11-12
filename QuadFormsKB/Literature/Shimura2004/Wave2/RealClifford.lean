/-
# Shimura 2004, §14.1: the groups $G^0(V)$ and $G^1(V)$ over $\mathbb R$; Theorem 14.2 (i)

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter IV, §14.1 and
Theorem 14.2 (printed p. 139). Page numbers are printed pages.

**Setting and dictionary.** $F = \mathbb R$, $V$ a finite-dimensional real vector space, `Q : QuadraticForm ℝ V`
nondegenerate, $G^+(V)$ = `Cassels.M0 Q`, $\nu$ = `multiplier`. "$\varphi$ definite" means $\varphi[x] > 0$ for all
$x \ne 0$ or $\varphi[x] < 0$ for all $x \ne 0$ (`IsDefinite`).

**Defines** (14.1a) $G^0(V) = \{a \in G^+(V) \mid \nu(a) > 0\}$ (`G0`), as the kernel of the sign of $\nu$ on
$G^+(V)$.

**Proves** (unconditional; standard axioms only)
* Theorem 14.2 (i): $[G^+(V) : G^0(V)] = 1$ or $2$ according as $\varphi$ is definite or indefinite
  (`theorem_14_2_i`), for $V \ne 0$; through Theorem 3.7 (i) and (3.4a), as in Shimura's proof;
* §14.1 (p. 139): $G^0(V) = \mathbb R^\times G^1(V)$, more precisely every $a \in G^0(V)$ is $rb$ with $0 < r \in
  \mathbb R$ and $b \in G^1(V)$ (`exists_pos_mul_of_mem_G0`), so $\tau(G^0(V)) = \tau(G^1(V))$.

**States** (named proposition, not proved) Theorem 14.2 (iii), the connectedness of $G^0(V)$ and $G^1(V)$
(`Theorem14_2_iii`).

**Not covered:** Theorem 14.2 (ii), (iv), and a proof of (iii) (identity component $SO^\varphi_0(V)$, connectedness, maximal compact
subgroups): they need the topology of the real groups (Lemma 8.0 and the connectedness of $SO^\varphi_0$).
-/
import QuadFormsKB.Literature.Shimura2004.CliffordGroups
import Mathlib.Topology.Algebra.Module.ModuleTopology
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

/-- The sign homomorphism $\mathbb R^\times \to \{\pm1\}$. -/
def realSign : ℝˣ →* ℤˣ where
  toFun x := if 0 < (x : ℝ) then 1 else -1
  map_one' := by simp
  map_mul' x y := by
    have hx := x.ne_zero
    have hy := y.ne_zero
    rcases lt_or_gt_of_ne hx with h1 | h1 <;> rcases lt_or_gt_of_ne hy with h2 | h2 <;>
      simp [Units.val_mul, h1, h2, mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg,
        mul_pos, not_lt.2 h1.le, not_lt.2 h2.le]

theorem realSign_eq_one_iff (x : ℝˣ) : realSign x = 1 ↔ 0 < (x : ℝ) := by
  simp only [realSign, MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs with h
  · simp [h]
  · simp [h]

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {Q : QuadraticForm ℝ V}

local notation "A" => CliffordAlgebra Q

instance : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero

/-- $\nu$ restricted to $G^+(V)$. -/
def multiplierM0 (hQ : (QuadraticMap.associated Q).Nondegenerate) : M0 Q →* ℝˣ :=
  (multiplier hQ).comp (Subgroup.inclusion M0_le_homogeneous)

/-- **$G^0(V) = \{a \in G^+(V) \mid \nu(a) > 0\}$** (Shimura (14.1a), p. 139), as a subgroup of $G^+(V)$. -/
@[kb "shimura2004" "(14.1a), p. 139 (G⁰(V) = {a ∈ G⁺(V) | ν(a) > 0})"]
def G0 (hQ : (QuadraticMap.associated Q).Nondegenerate) : Subgroup (M0 Q) :=
  (realSign.comp (multiplierM0 hQ)).ker

theorem mem_G0_iff (hQ : (QuadraticMap.associated Q).Nondegenerate) (a : M0 Q) :
    a ∈ G0 hQ ↔ 0 < (multiplier hQ ⟨a, M0_le_homogeneous a.2⟩ : ℝ) := by
  rw [G0, MonoidHom.mem_ker, MonoidHom.comp_apply, realSign_eq_one_iff]; rfl

variable (Q) in
/-- $\varphi$ is definite: positive definite or negative definite. -/
def IsDefinite : Prop := (∀ x : V, x ≠ 0 → 0 < Q x) ∨ (∀ x : V, x ≠ 0 → Q x < 0)

/-- $(x_1\cdots x_r)(x_1\cdots x_r)^* = \varphi[x_1]\cdots\varphi[x_r]$ (3.4a). -/
theorem prod_mul_reverse_prod (l : List V) :
    (l.map (ι Q)).prod * reverse (l.map (ι Q)).prod = algebraMap ℝ A (l.map Q).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.prod_cons, reverse.map_mul, reverse_ι, mul_assoc, ← mul_assoc _ (reverse _), ih,
      Algebra.commutes, ← mul_assoc, ι_sq_scalar, ← map_mul, List.map_cons, List.prod_cons]

theorem multiplier_pos_of_definite [Nontrivial V] (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hdef : IsDefinite Q) (a : M0 Q) : 0 < (multiplier hQ ⟨a, M0_le_homogeneous a.2⟩ : ℝ) := by
  obtain ⟨l, hl, hev, hal⟩ := (mem_M0_iff_exists_vecProd hQ (a : (CliffordAlgebra Q)ˣ)).1 a.2
  have hν : (multiplier hQ ⟨a, M0_le_homogeneous a.2⟩ : ℝ) = (l.map Q).prod := by
    apply (algebraMap _ (CliffordAlgebra Q)).injective
    rw [algebraMap_multiplier]
    change ((a : (CliffordAlgebra Q)ˣ) : A) * reverse ((a : (CliffordAlgebra Q)ˣ) : A) = _
    rw [hal, prod_mul_reverse_prod]
  rw [hν]
  have hne : ∀ y ∈ l, y ≠ 0 := fun y hy h0 => hl y hy (by rw [h0, QuadraticMap.map_zero])
  rcases hdef with hpos | hneg
  · exact List.prod_pos (fun c hc => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hc
      exact hpos y (hne y hy))
  · have key : ∀ l' : List V, (∀ y ∈ l', Q y < 0) → 0 < (l'.map Q).prod * (-1) ^ l'.length := by
      intro l' h'
      induction l' with
      | nil => simp
      | cons b t ih =>
        rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
        have hb := h' b (by simp)
        have ht := ih (fun y hy => h' y (by simp [hy]))
        nlinarith
    have := key l (fun y hy => hneg y (hne y hy))
    rwa [hev.neg_one_pow, mul_one] at this

/-- An indefinite nondegenerate real form takes a positive and a negative value. -/
theorem exists_pos_neg_of_not_definite (hQ : (QuadraticMap.associated Q).Nondegenerate) (hdef : ¬ IsDefinite Q) :
    (∃ x : V, 0 < Q x) ∧ (∃ y : V, Q y < 0) := by
  simp only [IsDefinite, not_or, not_forall, not_lt, exists_prop] at hdef
  obtain ⟨⟨x, hx0, hx⟩, ⟨y, hy0, hy⟩⟩ := hdef
  -- an isotropic vector `w ≠ 0` gives both signs on `t • w + z`
  have both_of_iso : ∀ w : V, w ≠ 0 → Q w = 0 → (∃ x : V, 0 < Q x) ∧ (∃ y : V, Q y < 0) := by
    intro w hw hw0
    obtain ⟨z, hz⟩ : ∃ z, QuadraticMap.associated Q w z ≠ 0 := by
      by_contra h
      push_neg at h
      exact hw (hQ.1 w h)
    have hp : QuadraticMap.polar Q w z ≠ 0 := by
      rw [QuadraticMap.associated_apply] at hz
      intro h; apply hz; simp [QuadraticMap.polar] at h ⊢; linarith
    set p := QuadraticMap.polar Q w z
    have hval : ∀ t : ℝ, Q (t • w + z) = t * p + Q z := by
      intro t
      rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hw0, QuadraticMap.polar_smul_left]
      simp [p, smul_eq_mul]; ring
    refine ⟨⟨((|Q z| + 1) / p) • w + z, ?_⟩, ⟨(-(|Q z| + 1) / p) • w + z, ?_⟩⟩
    · rw [hval, div_mul_cancel₀ _ hp]; linarith [neg_abs_le (Q z)]
    · rw [hval, div_mul_cancel₀ _ hp]; linarith [le_abs_self (Q z)]
  rcases hx.lt_or_eq with hx' | hx'
  · rcases hy.lt_or_eq with hy' | hy'
    · exact ⟨⟨y, hy'⟩, ⟨x, hx'⟩⟩
    · exact both_of_iso y hy0 hy'.symm
  · exact both_of_iso x hx0 hx'

open Classical in
/-- **Theorem 14.2 (i)** (Shimura 2004, p. 139): for a nondegenerate real form on $V \ne 0$,
$[G^+(V) : G^0(V)] = 1$ or $2$ according as $\varphi$ is definite or indefinite. -/
@[kb "shimura2004" "Thm. 14.2 (i), p. 139 ([G⁺(V) : G⁰(V)] = 1 or 2 as φ is definite or indefinite)"]
theorem theorem_14_2_i [Nontrivial V] (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    (G0 hQ).index = if IsDefinite Q then 1 else 2 := by
  split_ifs with hdef
  · rw [Subgroup.index_eq_one, eq_top_iff]
    intro a _
    exact (mem_G0_iff hQ a).2 (multiplier_pos_of_definite hQ hdef a)
  · obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := exists_pos_neg_of_not_definite hQ hdef
    have hx0 : Q x ≠ 0 := hx.ne'
    have hy0 : Q y ≠ 0 := hy.ne
    -- the element `xy` of `G⁺(V)` has `ν(xy) = φ[x]φ[y] < 0`
    have hxy : vecUnit x hx0 * vecUnit y hy0 ∈ M0 Q := by
      refine (mem_M0_iff_exists_vecProd hQ _).2 ⟨[x, y], ?_, by simp, ?_⟩
      · intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
      · simp [vecUnit]
    have hν : (multiplier hQ ⟨_, M0_le_homogeneous hxy⟩ : ℝ) = Q x * Q y := by
      apply (algebraMap _ (CliffordAlgebra Q)).injective
      rw [algebraMap_multiplier]
      change ι Q x * ι Q y * reverse (ι Q x * ι Q y) = _
      have := prod_mul_reverse_prod (Q := Q) [x, y]
      simpa [mul_assoc] using this
    rw [G0, Subgroup.index_ker]
    have hsurj : Function.Surjective (realSign.comp (multiplierM0 hQ)) := by
      intro s
      rcases Int.units_eq_one_or s with rfl | rfl
      · exact ⟨1, map_one _⟩
      · refine ⟨⟨_, hxy⟩, ?_⟩
        simp only [MonoidHom.comp_apply, realSign, MonoidHom.coe_mk, OneHom.coe_mk]
        have : ¬ (0 < ((multiplierM0 hQ ⟨_, hxy⟩ : ℝˣ) : ℝ)) := by
          change ¬ (0 < (multiplier hQ ⟨_, M0_le_homogeneous hxy⟩ : ℝ))
          rw [hν]; exact not_lt.2 (mul_neg_of_pos_of_neg hx hy).le
        simp [this]
    rw [MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- **$G^0(V) = \mathbb R^\times G^1(V)$** (Shimura, §14.1, p. 139: "It is easy to see that
$G^0(V) = \mathbb R^\times G^1(V)$"): every $a \in G^0(V)$ is $rb$ with $0 < r \in \mathbb R$ and $b \in G^1(V)$
(take $r = \nu(a)^{1/2}$). Hence $\tau(G^0(V)) = \tau(G^1(V))$. -/
@[kb "shimura2004" "§14.1, p. 139 (G⁰(V) = ℝ^× G¹(V))"]
theorem exists_pos_mul_of_mem_G0 (hQ : (QuadraticMap.associated Q).Nondegenerate) {a : M0 Q} (ha : a ∈ G0 hQ) :
    ∃ r : ℝ, 0 < r ∧ ∃ b ∈ spinGroupG1 Q, ((a : (CliffordAlgebra Q)ˣ) : A) = algebraMap ℝ A r * (b : A) := by
  have hpos := (mem_G0_iff hQ a).1 ha
  set m := (multiplier hQ ⟨a, M0_le_homogeneous a.2⟩ : ℝ)
  set r := Real.sqrt m
  have hr : 0 < r := Real.sqrt_pos.2 hpos
  have hrr : r * r = m := Real.mul_self_sqrt hpos.le
  let ru : ℝˣ := Units.mk0 r hr.ne'
  let s : (CliffordAlgebra Q)ˣ := Units.map (algebraMap ℝ A).toMonoidHom ru
  have hs : ((s⁻¹ : (CliffordAlgebra Q)ˣ) : A) = algebraMap ℝ A r⁻¹ := by
    simp [s, ru, map_inv₀]
  have hA := algebraMap_multiplier hQ ⟨a, M0_le_homogeneous a.2⟩
  refine ⟨r, hr, s⁻¹ * a, ⟨(M0 Q).mul_mem ((M0 Q).inv_mem (scalar_mem_M0 ru)) a.2, ?_⟩, ?_⟩
  · -- `(r⁻¹ a)(r⁻¹ a)^* = r⁻² ν(a) = 1`
    show ((s⁻¹ * (a : (CliffordAlgebra Q)ˣ) : (CliffordAlgebra Q)ˣ) : A) *
      reverse ((s⁻¹ * (a : (CliffordAlgebra Q)ˣ) : (CliffordAlgebra Q)ˣ) : A) = 1
    rw [Units.val_mul, hs, reverse.map_mul, reverse.commutes]
    calc algebraMap ℝ A r⁻¹ * ((a : (CliffordAlgebra Q)ˣ) : A) *
          (reverse ((a : (CliffordAlgebra Q)ˣ) : A) * algebraMap ℝ A r⁻¹)
        = algebraMap ℝ A r⁻¹ * (((a : (CliffordAlgebra Q)ˣ) : A) * reverse ((a : (CliffordAlgebra Q)ˣ) : A)) *
            algebraMap ℝ A r⁻¹ := by simp only [mul_assoc]
      _ = algebraMap ℝ A (r⁻¹ * m * r⁻¹) := by rw [← hA, ← map_mul, ← map_mul]
      _ = 1 := by rw [show r⁻¹ * m * r⁻¹ = 1 by rw [← hrr]; field_simp, map_one]
  · rw [Units.val_mul, hs, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hr.ne', map_one, one_mul]

/-- **Theorem 14.2 (iii)** (Shimura 2004, p. 139), *stated, not proved*: for a nondegenerate real form on
$V$, $G^0(V)$ is connected if and only if $G^1(V)$ is connected, which is the case if $\dim V > 2$; if
$\dim V = 2$, then $G^1(V)$ is connected if and only if $\varphi$ is definite. The topology is the natural one:
$A(V)$ is a finite-dimensional real vector space (`moduleTopology ℝ`), $A(V)^\times$ carries the units topology and
$G^+(V)$, $G^0(V)$, $G^1(V)$ the subspace topologies. Shimura's proof uses (ii) (the identity component
$SO^\varphi_0(V)$) and an explicit description of $G^1$ of a plane. -/
@[kb "shimura2004" "Thm. 14.2 (iii), p. 139 (G⁰(V), G¹(V) connected iff dim V > 2 or (dim V = 2, φ definite))"]
def Theorem14_2_iii : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V)
    (hQ : (QuadraticMap.associated Q).Nondegenerate),
    letI : TopologicalSpace (CliffordAlgebra Q) := moduleTopology ℝ (CliffordAlgebra Q)
    (ConnectedSpace (G0 hQ) ↔ ConnectedSpace (spinGroupG1 Q)) ∧
    (2 < finrank ℝ V → ConnectedSpace (spinGroupG1 Q)) ∧
    (finrank ℝ V = 2 → (ConnectedSpace (spinGroupG1 Q) ↔ IsDefinite Q))

end QuadFormsKB.Shimura2004
