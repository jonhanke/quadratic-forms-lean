/-
# Shimura 2004, §3: Clifford groups and spin groups

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (bibliography key `shimura2004`), Chapter I, §3,
printed pp. 20–24. Page numbers in the tags are printed pages.

**Setting and dictionary.** Shimura works with a field $F$ of characteristic $\ne 2$, a finite-dimensional
$F$-vector space $V$ of dimension $n$, and a symmetric bilinear form $\varphi$ with $\varphi[x] = \varphi(x,x)$; here
the quadratic form is `Q : QuadraticForm F V` with $Q(x) = \varphi[x]$, and $\varphi$ is Mathlib's
`QuadraticMap.associated Q`. "$\varphi$ nondegenerate" is `(QuadraticMap.associated Q).Nondegenerate`. The Clifford
algebra $A(V) = A(V,\varphi)$ is Mathlib's `CliffordAlgebra Q` (with $x^2 = \varphi[x]$ for $x \in V$, Shimura's
(2.1)(3)), $A^+(V)$, $A^-(V)$ are `evenOdd Q 0`, `evenOdd Q 1`, the canonical automorphism $a \mapsto a'$ is
`CliffordAlgebra.involute`, and the canonical involution $a \mapsto a^*$ (with $(x_1\cdots x_m)^* = x_m\cdots x_1$) is
`CliffordAlgebra.reverse`. The orthogonal group $O^\varphi(V)$ is O'Meara's `OMeara.orth Q`, $SO^\varphi(V)$ is
`OMeara.orthPlus Q`, and the spinor norm is `OMeara.spinorNormHom` (O'Meara's $\theta$, defined through
factorizations into symmetries).

The objects of §3 that already exist in the library are reused, not redefined:
* Shimura's Clifford group $G(V) = \{a \in A(V)^\times \mid a^{-1}Va = V\}$ (3.1a) is `Cassels.cliffordGroup Q` (the
  units $u$ with $uVu^{-1} \subseteq V$; the two conditions agree, `mem_cliffordGroup_iff`);
* the even Clifford group $G^+(V) = G(V) \cap A^+(V)$ (3.1b) is Cassels' $M_0(V)$ = `Cassels.M0 Q`
  (`mem_M0_iff`).

New here: $G^-(V)$ (`cliffordGroupOdd`), $G'(V) = G^+(V) \cup G^-(V)$ (3.3) as a subgroup
(`homogeneousCliffordGroup`), Shimura's $\tau(a) : x \mapsto a^{-1}xa$ (3.1c) (`tau`), the multiplier
$\nu(a) = aa^*$ (3.4) (`multiplier`) and the spin group $G^1(V) = \{a \in G^+(V) \mid \nu(a) = 1\}$ (3.6)
(`spinGroupG1`).

*Right actions.* Shimura lets linear maps act on the right, $x\tau(a) = a^{-1}xa$, so that $\tau(ab) = \tau(a)\tau(b)$
in his notation. In Lean `tau a` is the linear map $x \mapsto a^{-1}xa$ and composition is the usual one, so
`tau (a * b) = tau b * tau a` (`tau_mul`): the same statement written for left composition. Images and kernels, which
is what the theorems below are about, do not depend on this.

**Proves** (all unconditional; standard axioms only)
* (3.1c) $\tau(a) \in O^\varphi(V)$ for $a \in G(V)$ (`tau_mem_orth`), and $\tau$ is multiplicative (`tau_mul`).
* Lemma 3.3: an anisotropic vector lies in $G^-(V)$ (`vecUnit_mem_cliffordGroupOdd`).
* (3.3), Theorem 3.7 (ii): $G'(V)$ is a subgroup (`homogeneousCliffordGroup`); for $V \ne 0$ the index of $G^+(V)$ in
  $G'(V)$ is $2$ (`index_M0_homogeneous`).
* (3.4), Theorem 3.7 (ii): for nondegenerate $\varphi$, $aa^* \in F^\times$ for $a \in G'(V)$ and
  $\nu : G'(V) \to F^\times$ is a homomorphism (`multiplier`, `algebraMap_multiplier`), with
  $\nu(a^*) = \nu(a') = \nu(a)$ (`reverse_mul_self_eq_multiplier`, `involute_mul_reverse_involute_eq_multiplier`).
* Theorem 3.7 (i): for $V \ne 0$, $G^+(V)$ (resp. $G^-(V)$) is the set of products of an even (resp. odd) number of
  invertible vectors (`mem_M0_iff_exists_vecProd`, `mem_cliffordGroupOdd_iff_exists_vecProd`).
* Theorem 3.6 (iii): $\tau(G^+(V)) = SO^\varphi(V)$ (`tau_mem_orthPlus`, `exists_tau_eq`), the kernel of $\tau$ on
  $G^+(V)$ is $F^\times$ (`tau_eq_one_iff`), and the isomorphism $G^+(V)/F^\times \cong SO^\varphi(V)$
  (`theorem_3_6_iii`).
* (3.5): $a \in A^+(V)$ with $aa^* \in F^\times$ and $aVa^* \subseteq V$ lies in $G^+(V)$ (`mem_M0_of_mul_reverse`).
* (3.6): $F^\times \cap G^1(V) = \{\pm 1\}$ (`algebraMap_mem_spinGroupG1_iff`), $\tau$ is injective on
  $G^1(V)/\{\pm1\}$ (`tau_eq_one_iff_of_mem_spinGroupG1`), and for $V \ne 0$, $G^1(V)$ is Mathlib's `spinGroup Q`
  (`mem_spinGroupG1_iff_mem_spinGroup`).
* (3.7): the spinor norm of $\tau(\xi)$, $\xi \in G^+(V)$, is the square class of $\nu(\xi)$
  (`spinorNormHom_tau`): Shimura's definition of $\sigma$ agrees with O'Meara's.
* (3.7a): $\tau(G^1(V)) = \{\alpha \in SO^\varphi(V) \mid \sigma(\alpha) = 1\}$ (`tau_image_spinGroupG1`), for
  $V \ne 0$.
-/
import QuadFormsKB.Literature.Cassels.Ch10.SpinGroup
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

local notation "A" => CliffordAlgebra Q

/-! ### The Clifford group, its even and odd parts, and `τ` -/

/-- **Shimura's Clifford group** (3.1a): $a \in A(V)^\times$ lies in $G(V)$ if and only if $a^{-1}Va \subseteq V$
(Shimura notes this is equivalent to $a^{-1}Va = V$). The library's `Cassels.cliffordGroup Q` is defined with
$aVa^{-1}$; since it is a group the two agree. -/
@[kb "shimura2004" "(3.1a), p. 20 (the Clifford group G(V) = {a ∈ A(V)^× | a⁻¹Va = V})"]
theorem mem_cliffordGroup_iff (a : (CliffordAlgebra Q)ˣ) :
    a ∈ cliffordGroup Q ↔ ∀ x : V, ∃ y : V, ι Q y = ↑a⁻¹ * ι Q x * ↑a := by
  constructor
  · intro ha x
    obtain ⟨y, hy⟩ := (cliffordGroup Q).inv_mem ha x
    exact ⟨y, by simpa using hy⟩
  · intro h
    have : a⁻¹ ∈ cliffordGroup Q := fun x => by
      obtain ⟨y, hy⟩ := h x
      exact ⟨y, by simpa using hy⟩
    simpa using (cliffordGroup Q).inv_mem this

/-- **The even Clifford group** (3.1b): $G^+(V) = G(V) \cap A^+(V)$ is Cassels' $M_0(V)$ = `Cassels.M0 Q`. -/
@[kb "shimura2004" "(3.1b), p. 20 (the even Clifford group G⁺(V) = G(V) ∩ A⁺(V))"]
theorem mem_M0_iff (a : (CliffordAlgebra Q)ˣ) :
    a ∈ M0 Q ↔ a ∈ cliffordGroup Q ∧ (a : A) ∈ evenOdd Q 0 :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

variable (Q) in
/-- **$G^-(V) = G(V) \cap A^-(V)$** (Shimura (3.1b), p. 20): the odd elements of the Clifford group. -/
@[kb "shimura2004" "(3.1b), p. 20 (G⁻(V) = G(V) ∩ A⁻(V))"]
def cliffordGroupOdd : Set (CliffordAlgebra Q)ˣ :=
  {a | a ∈ cliffordGroup Q ∧ (a : A) ∈ evenOdd Q 1}

/-- **Shimura's $\tau(a)$** (3.1c), p. 20: for $a \in G(V)$, the linear automorphism $x \mapsto a^{-1}xa$ of $V$
(Shimura writes it on the right, $x\tau(a)$). It is Cassels' $T_{a^{-1}}$. -/
@[kb "shimura2004" "(3.1c), p. 20 (τ(a) : x ↦ a⁻¹xa)"]
def tau (a : cliffordGroup Q) : V ≃ₗ[F] V := conjHom a⁻¹

theorem tau_spec (a : cliffordGroup Q) (x : V) :
    ι Q (tau a x) = ((a : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) * ι Q x * (a : (CliffordAlgebra Q)ˣ) := by
  rw [tau, conjHom_spec]
  simp

/-- **$\tau(a) \in O^\varphi(V)$** (Shimura, p. 20: $\varphi[x\tau(a)] = (a^{-1}xa)^2 = x^2 = \varphi[x]$). -/
@[kb "shimura2004" "§3.1, p. 20 (τ(a) belongs to the orthogonal group O^φ)"]
theorem tau_mem_orth (a : cliffordGroup Q) : tau a ∈ orth Q :=
  fun x => conjHom_isometry _ x

/-- **$\tau$ is a homomorphism** (Shimura, p. 20), written for left composition of maps: $x \mapsto (ab)^{-1}x(ab)$
is $\tau(a)$ followed by $\tau(b)$. -/
@[kb "shimura2004" "§3.1, p. 20 (τ gives a homomorphism of G(V) into O^φ; right actions)"]
theorem tau_mul (a b : cliffordGroup Q) : tau (a * b) = tau b * tau a := by
  simp [tau, mul_inv_rev, map_mul]

theorem tau_one : tau (1 : cliffordGroup Q) = 1 := by simp [tau]

theorem tau_inv (a : cliffordGroup Q) : tau a⁻¹ = (tau a)⁻¹ := by simp [tau]

/-- **Lemma 3.3** (p. 21): an invertible vector $x$ ($x^2 = \varphi[x] \ne 0$) lies in $G^-(V)$. -/
@[kb "shimura2004" "Lemma 3.3, p. 21 (x ∈ G⁻(V) if x² ≠ 0)"]
theorem vecUnit_mem_cliffordGroupOdd (x : V) (hx : Q x ≠ 0) : vecUnit x hx ∈ cliffordGroupOdd Q :=
  ⟨vecUnit_mem x hx, ι_mem_evenOdd_one Q x⟩

/-! ### The group `G'(V)` -/

theorem one_mem_evenOdd_zero : (1 : A) ∈ evenOdd Q 0 :=
  one_le_evenOdd_zero Q (Submodule.mem_one.2 ⟨1, by simp⟩)

theorem mul_mem_evenOdd {i j : ZMod 2} {a b : A} (ha : a ∈ evenOdd Q i) (hb : b ∈ evenOdd Q j) :
    a * b ∈ evenOdd Q (i + j) :=
  SetLike.mul_mem_graded ha hb

variable (Q) in
/-- **The group $G'(V) = G^+(V) \cup G^-(V)$** (Shimura (3.3), p. 22; it is a subgroup of $G(V)$ by Theorem 3.7
(ii), p. 23): the homogeneous elements of the Clifford group. Closure under products and inverses is the grading
$A^iA^j \subseteq A^{i+j}$ and the homogeneity of inverses. -/
@[kb "shimura2004" "(3.3), p. 22; Thm. 3.7 (ii), p. 23 (G'(V) = G⁺(V) ∪ G⁻(V) is a subgroup of G(V))"]
def homogeneousCliffordGroup : Subgroup (CliffordAlgebra Q)ˣ where
  carrier := {a | a ∈ cliffordGroup Q ∧ ((a : A) ∈ evenOdd Q 0 ∨ (a : A) ∈ evenOdd Q 1)}
  one_mem' := ⟨(cliffordGroup Q).one_mem, Or.inl one_mem_evenOdd_zero⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(cliffordGroup Q).mul_mem ha hb, ?_⟩
    rw [Units.val_mul]
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
    · exact Or.inl (by simpa using mul_mem_evenOdd ha' hb')
    · exact Or.inr (by simpa using mul_mem_evenOdd ha' hb')
    · exact Or.inr (by simpa using mul_mem_evenOdd ha' hb')
    · exact Or.inl (by simpa [show (1 : ZMod 2) + 1 = 0 from rfl] using mul_mem_evenOdd ha' hb')
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(cliffordGroup Q).inv_mem ha, ?_⟩
    rcases ha' with ha' | ha'
    · exact Or.inl (mem_evenOdd_of_mul_eq_one Q ha' a.mul_inv)
    · exact Or.inr (mem_evenOdd_of_mul_eq_one Q ha' a.mul_inv)

theorem M0_le_homogeneous : M0 Q ≤ homogeneousCliffordGroup Q :=
  fun _ h => ⟨h.2, Or.inl h.1⟩

theorem cliffordGroupOdd_subset_homogeneous : cliffordGroupOdd Q ⊆ homogeneousCliffordGroup Q :=
  fun _ h => ⟨h.1, Or.inr h.2⟩

/-- $G'(V) = G^+(V) \cup G^-(V)$ (Shimura (3.3)). -/
theorem mem_homogeneous_iff (a : (CliffordAlgebra Q)ˣ) :
    a ∈ homogeneousCliffordGroup Q ↔ a ∈ M0 Q ∨ a ∈ cliffordGroupOdd Q := by
  constructor
  · rintro ⟨h, h' | h'⟩
    · exact Or.inl ⟨h', h⟩
    · exact Or.inr ⟨h, h'⟩
  · rintro (h | h)
    · exact M0_le_homogeneous h
    · exact cliffordGroupOdd_subset_homogeneous h

theorem homogeneous_le_cliffordGroup : homogeneousCliffordGroup Q ≤ cliffordGroup Q := fun _ h => h.1

/-- An element of $G^-(V)$ is a vector times an element of $G^+(V)$: $a = x\cdot(x^{-1}a)$. -/
theorem vecUnit_inv_mul_mem_M0 {a : (CliffordAlgebra Q)ˣ} (ha : a ∈ cliffordGroupOdd Q) (x : V) (hx : Q x ≠ 0) :
    (vecUnit x hx)⁻¹ * a ∈ M0 Q := by
  refine ⟨?_, (cliffordGroup Q).mul_mem ((cliffordGroup Q).inv_mem (vecUnit_mem x hx)) ha.1⟩
  have hxi : (((vecUnit x hx)⁻¹ : (CliffordAlgebra Q)ˣ) : A) ∈ evenOdd Q 1 :=
    mem_evenOdd_of_mul_eq_one Q (ι_mem_evenOdd_one Q x) (vecUnit x hx).mul_inv
  simpa [show (1 : ZMod 2) + 1 = 0 from rfl] using mul_mem_evenOdd hxi ha.2

/-- The odd part of the Clifford algebra of the zero space is zero, so if $G^-(V)$ is nonempty then $V \ne 0$. -/
theorem nontrivial_of_mem_cliffordGroupOdd {a : (CliffordAlgebra Q)ˣ} (ha : a ∈ cliffordGroupOdd Q) :
    Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have hι : LinearMap.range (ι Q) = ⊥ := by
    rw [LinearMap.range_eq_bot]
    ext x
    simp [Subsingleton.elim x 0]
  have h0 : evenOdd Q 1 = ⊥ := by
    rw [evenOdd, hι]
    refine le_bot_iff.1 (iSup_le fun i => ?_)
    have hi : (i : ℕ) ≠ 0 := by
      intro h
      have := i.2
      rw [h] at this
      exact absurd this (by decide)
    rw [Submodule.bot_pow hi]
  have := ha.2
  rw [h0, Submodule.mem_bot] at this
  exact a.ne_zero this

/-- **$[G'(V) : G^+(V)] = 2$** (Shimura, Theorem 3.7 (ii), p. 23), for $V \ne 0$ and nondegenerate $\varphi$. -/
@[kb "shimura2004" "Thm. 3.7 (ii), p. 23 ([G'(V) : G⁺(V)] = 2)"]
theorem index_M0_homogeneous [Nontrivial V] (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    ((M0 Q).subgroupOf (homogeneousCliffordGroup Q)).index = 2 := by
  obtain ⟨x, hx⟩ := exists_anisotropic hQ (Q := Q)
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨vecUnit x hx, cliffordGroupOdd_subset_homogeneous (vecUnit_mem_cliffordGroupOdd x hx)⟩, ?_⟩
  rintro ⟨b, hb⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  have hxo : ((vecUnit x hx : (CliffordAlgebra Q)ˣ) : A) ∈ evenOdd Q 1 := ι_mem_evenOdd_one Q x
  have hdisj := (evenOdd_isCompl Q).disjoint
  rw [Submodule.disjoint_def] at hdisj
  rcases hb.2 with hb0 | hb1
  · -- `b` even, `b x` odd
    refine Or.inr ⟨⟨hb0, hb.1⟩, fun h => ?_⟩
    have h1 : ((b * vecUnit x hx : (CliffordAlgebra Q)ˣ) : A) ∈ evenOdd Q 1 := by
      simpa using mul_mem_evenOdd hb0 hxo
    exact (b * vecUnit x hx).ne_zero (hdisj _ h.1 h1)
  · refine Or.inl ⟨⟨?_, (cliffordGroup Q).mul_mem hb.1 (vecUnit_mem x hx)⟩, fun h => ?_⟩
    · simpa [show (1 : ZMod 2) + 1 = 0 from rfl] using mul_mem_evenOdd hb1 hxo
    · exact b.ne_zero (hdisj _ h.1 hb1)

/-! ### The multiplier `ν` -/

/-- For $a \in G^+(V)$, $aa^* \in F^\times$ (Cassels, Ch. 10, Thm. 3.1, Cor. 1); for $a \in G^-(V)$ write
$a = xb$ with $b \in G^+(V)$: $aa^* = x\,bb^*\,x = bb^*\varphi[x]$. -/
theorem exists_mul_reverse_eq (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (a : homogeneousCliffordGroup Q) :
    ∃ c : F, c ≠ 0 ∧ ((a : (CliffordAlgebra Q)ˣ) : A) * reverse ((a : (CliffordAlgebra Q)ˣ) : A) =
      algebraMap F A c := by
  rcases (mem_homogeneous_iff _).1 a.2 with h | h
  · exact M0_mul_reverse hQ ⟨_, h⟩
  · haveI := nontrivial_of_mem_cliffordGroupOdd h
    obtain ⟨x, hx⟩ := exists_anisotropic hQ (Q := Q)
    obtain ⟨c, hc, hb⟩ := M0_mul_reverse hQ ⟨_, vecUnit_inv_mul_mem_M0 h x hx⟩
    refine ⟨c * Q x, mul_ne_zero hc hx, ?_⟩
    have ha : ((a : (CliffordAlgebra Q)ˣ) : A) = ι Q x * (((vecUnit x hx)⁻¹ * a : (CliffordAlgebra Q)ˣ) : A) := by
      rw [Units.val_mul, ← mul_assoc]
      change _ = ((vecUnit x hx * (vecUnit x hx)⁻¹ : (CliffordAlgebra Q)ˣ) : A) * _
      simp
    simp only at hb
    rw [ha, reverse.map_mul, reverse_ι, mul_assoc, ← mul_assoc _ _ (ι Q x), hb, Algebra.commutes,
      ← mul_assoc, ι_sq_scalar, ← map_mul, mul_comm]

/-- **The multiplier** $\nu(a) = aa^*$ (Shimura (3.4), p. 23) on $G'(V)$, as a homomorphism to $F^\times$
(Theorem 3.7 (ii)); nondegenerate $\varphi$. The value is characterized by `algebraMap_multiplier`. -/
@[kb "shimura2004" "(3.4), p. 23; Thm. 3.7 (ii), p. 23 (ν(a) = aa*, a homomorphism G'(V) → F^×)"]
def multiplier (hQ : (QuadraticMap.associated Q).Nondegenerate) : homogeneousCliffordGroup Q →* Fˣ where
  toFun a := Units.mk0 (exists_mul_reverse_eq hQ a).choose (exists_mul_reverse_eq hQ a).choose_spec.1
  map_one' := by
    ext
    apply (algebraMap F A).injective
    simp only [Units.val_mk0, Units.val_one, map_one]
    rw [← (exists_mul_reverse_eq hQ 1).choose_spec.2]
    simp
  map_mul' a b := by
    ext
    apply (algebraMap F A).injective
    simp only [Units.val_mk0, Units.val_mul, map_mul]
    rw [← (exists_mul_reverse_eq hQ a).choose_spec.2, ← (exists_mul_reverse_eq hQ b).choose_spec.2,
      ← (exists_mul_reverse_eq hQ (a * b)).choose_spec.2]
    simp only [Subgroup.coe_mul, Units.val_mul, reverse.map_mul]
    rw [mul_assoc, ← mul_assoc ((b : (CliffordAlgebra Q)ˣ) : A), (exists_mul_reverse_eq hQ b).choose_spec.2,
      ← Algebra.commutes, ← mul_assoc, ← mul_assoc]
    rw [← Algebra.commutes (R := F) _ ((a : (CliffordAlgebra Q)ˣ) : A)]

theorem algebraMap_multiplier (hQ : (QuadraticMap.associated Q).Nondegenerate) (a : homogeneousCliffordGroup Q) :
    algebraMap F A (multiplier hQ a : F) =
      ((a : (CliffordAlgebra Q)ˣ) : A) * reverse ((a : (CliffordAlgebra Q)ˣ) : A) :=
  (exists_mul_reverse_eq hQ a).choose_spec.2.symm

/-- **$\nu(a^*) = \nu(a)$** (Shimura, Theorem 3.7 (ii)): $a^*a = aa^*$, i.e. $a^*(a^*)^* = \nu(a)$. -/
@[kb "shimura2004" "Thm. 3.7 (ii), p. 23 (ν(a*) = ν(a))"]
theorem reverse_mul_self_eq_multiplier (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (a : homogeneousCliffordGroup Q) :
    reverse ((a : (CliffordAlgebra Q)ˣ) : A) * reverse (reverse ((a : (CliffordAlgebra Q)ˣ) : A)) =
      algebraMap F A (multiplier hQ a : F) := by
  rw [reverse_reverse, algebraMap_multiplier]
  exact (inverse_of_mul_reverse Q (Units.ne_zero _) (algebraMap_multiplier hQ a).symm).1.trans
    (algebraMap_multiplier hQ a)

/-- **$\nu(a') = \nu(a)$** (Shimura, Theorem 3.7 (ii)): $a'(a')^* = aa^*$ since $a' = \pm a$ on $G'(V)$. -/
@[kb "shimura2004" "Thm. 3.7 (ii), p. 23 (ν(a') = ν(a))"]
theorem involute_mul_reverse_involute_eq_multiplier (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (a : homogeneousCliffordGroup Q) :
    involute ((a : (CliffordAlgebra Q)ˣ) : A) * reverse (involute ((a : (CliffordAlgebra Q)ˣ) : A)) =
      algebraMap F A (multiplier hQ a : F) := by
  rw [algebraMap_multiplier]
  rcases a.2.2 with h | h
  · rw [involute_eq_of_mem_even h]
  · rw [involute_eq_of_mem_odd h, map_neg, neg_mul_neg]

/-- On $G^+(V)$, $\nu$ is $aa^*$. -/
theorem algebraMap_multiplier_M0 (hQ : (QuadraticMap.associated Q).Nondegenerate) (a : M0 Q) :
    algebraMap F A (multiplier hQ ⟨a, M0_le_homogeneous a.2⟩ : F) =
      ((a : (CliffordAlgebra Q)ˣ) : A) * reverse ((a : (CliffordAlgebra Q)ˣ) : A) :=
  algebraMap_multiplier hQ _

/-- $\nu(x) = \varphi[x]$ for an invertible vector, so (Shimura (3.4a)) $\nu(x_1\cdots x_r) = \varphi[x_1]\cdots
\varphi[x_r]$. -/
@[kb "shimura2004" "(3.4a), p. 23 (ν(x) = φ[x] for x ∈ V ∩ A(V)^×)"]
theorem multiplier_vecUnit (hQ : (QuadraticMap.associated Q).Nondegenerate) (x : V) (hx : Q x ≠ 0) :
    (multiplier hQ ⟨vecUnit x hx, cliffordGroupOdd_subset_homogeneous (vecUnit_mem_cliffordGroupOdd x hx)⟩ : F)
      = Q x := by
  apply (algebraMap F A).injective
  rw [algebraMap_multiplier]
  change ι Q x * reverse (ι Q x) = _
  rw [reverse_ι, ι_sq_scalar]

/-! ### Theorem 3.7 (i): products of invertible vectors -/

/-- The product of a list of anisotropic vectors, as a unit. -/
theorem coe_vecProd_eq_prod (l : List V) (hl : ∀ y ∈ l, Q y ≠ 0) :
    (((vecProd l hl : cliffordGroup Q) : (CliffordAlgebra Q)ˣ) : A) = (l.map (ι Q)).prod := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    rw [coe_vecProd_cons, ih, List.map_cons, List.prod_cons]

/-- **Theorem 3.7 (i)**, even part (p. 23): for nondegenerate $\varphi$ and $V \ne 0$, $a \in G^+(V)$ if and only
if $a$ is a product of an even number of invertible elements of $V$. (For $V = 0$, $G^+(V) = F^\times$ while the only
such product is $1$; Shimura tacitly has $n > 0$ here.) -/
@[kb "shimura2004" "Thm. 3.7 (i), p. 23 (G⁺(V) = products of an even number of invertible vectors)"]
theorem mem_M0_iff_exists_vecProd [Nontrivial V] (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (a : (CliffordAlgebra Q)ˣ) :
    a ∈ M0 Q ↔ ∃ (l : List V) (_ : ∀ y ∈ l, Q y ≠ 0), Even l.length ∧ (a : A) = (l.map (ι Q)).prod := by
  constructor
  · intro ha
    obtain ⟨l, hl, c, hc, hev, -, hu⟩ := exists_eq_smul_vecProd hQ ⟨a, ha⟩
    rw [coe_vecProd_eq_prod] at hu
    simp only at hu
    cases l with
    | cons y l =>
      have hy : Q (c • y) ≠ 0 := by
        rw [QuadraticMap.map_smul]
        exact mul_ne_zero (mul_ne_zero hc hc) (hl y (List.mem_cons_self ..))
      refine ⟨c • y :: l, ?_, by simpa using hev, ?_⟩
      · intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hy
        · exact hl z (List.mem_cons_of_mem _ hz)
      · rw [hu, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, map_smul, smul_mul_assoc]
    | nil =>
      -- `a = c` is a scalar: `c = x · (c Q(x)⁻¹ x)` for an anisotropic `x`
      obtain ⟨x, hx⟩ := exists_anisotropic hQ (Q := Q)
      have hx' : Q ((c * (Q x)⁻¹) • x) ≠ 0 := by
        rw [QuadraticMap.map_smul]
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero hc (inv_ne_zero hx)) (mul_ne_zero hc (inv_ne_zero hx))) hx
      refine ⟨[x, (c * (Q x)⁻¹) • x], ?_, by simp, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hx'
      · rw [hu]
        simp only [List.map_nil, List.prod_nil, List.map_cons, List.prod_cons, mul_one, map_smul,
          mul_smul_comm, ι_sq_scalar, smul_smul]
        rw [Algebra.algebraMap_eq_smul_one, smul_smul, mul_assoc, inv_mul_cancel₀ hx, mul_one]
  · rintro ⟨l, hl, hev, hu⟩
    have h := vecProd_mem_even hl hev
    have hval : a = ((vecProd l hl : cliffordGroup Q) : (CliffordAlgebra Q)ˣ) :=
      Units.ext (by rw [hu, coe_vecProd_eq_prod])
    rw [hval]
    exact ⟨h, (vecProd l hl).2⟩

/-- **Theorem 3.7 (i)**, odd part (p. 23): for nondegenerate $\varphi$ and $V \ne 0$, $a \in G^-(V)$ if and only if
$a$ is a product of an odd number of invertible elements of $V$. -/
@[kb "shimura2004" "Thm. 3.7 (i), p. 23 (G⁻(V) = products of an odd number of invertible vectors)"]
theorem mem_cliffordGroupOdd_iff_exists_vecProd [Nontrivial V] (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (a : (CliffordAlgebra Q)ˣ) :
    a ∈ cliffordGroupOdd Q ↔
      ∃ (l : List V) (_ : ∀ y ∈ l, Q y ≠ 0), Odd l.length ∧ (a : A) = (l.map (ι Q)).prod := by
  constructor
  · intro ha
    obtain ⟨x, hx⟩ := exists_anisotropic hQ (Q := Q)
    obtain ⟨l, hl, hev, hb⟩ := (mem_M0_iff_exists_vecProd hQ _).1 (vecUnit_inv_mul_mem_M0 ha x hx)
    refine ⟨x :: l, ?_, by simpa [Nat.odd_add_one, Nat.not_odd_iff_even] using hev, ?_⟩
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hx
      · exact hl z hz
    · rw [List.map_cons, List.prod_cons, ← hb, Units.val_mul, ← mul_assoc]
      change _ = ((vecUnit x hx * (vecUnit x hx)⁻¹ : (CliffordAlgebra Q)ˣ) : A) * _
      simp
  · rintro ⟨l, hl, hodd, hu⟩
    have hval : a = ((vecProd l hl : cliffordGroup Q) : (CliffordAlgebra Q)ˣ) :=
      Units.ext (by rw [hu, coe_vecProd_eq_prod])
    refine ⟨hval ▸ (vecProd l hl).2, ?_⟩
    have := vecProd_mem_evenOdd l hl
    have hl1 : ((l.length : ℕ) : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.2 hodd
    rw [hl1] at this
    rw [hval]
    exact this

/-! ### Theorem 3.6 (iii): `G⁺(V)/F^× ≅ SO^φ(V)` -/

/-- $\tau(a) \in SO^\varphi(V)$ for $a \in G^+(V)$ (Shimura, Theorem 3.6, p. 22). -/
theorem tau_mem_orthPlus (hQ : (QuadraticMap.associated Q).Nondegenerate) (a : M0 Q) :
    tau (Subgroup.inclusion M0_le a) ∈ orthPlus Q := by
  have h := conjM0_mem_orthPlus hQ a⁻¹
  simpa [tau, conjM0_apply] using h

/-- Every element of $SO^\varphi(V)$ is $\tau(a)$ for some $a \in G^+(V)$ (Shimura, Theorem 3.6 (i), (ii):
$\tau(G^+(V)) = SO^\varphi$). -/
theorem exists_tau_eq (hQ : (QuadraticMap.associated Q).Nondegenerate) {α : V ≃ₗ[F] V} (hα : α ∈ orthPlus Q) :
    ∃ a : M0 Q, tau (Subgroup.inclusion M0_le a) = α := by
  rw [← range_conjM0 hQ] at hα
  obtain ⟨a, ha⟩ := hα
  refine ⟨a⁻¹, ?_⟩
  simpa [tau, conjM0_apply] using ha

/-- The kernel of $\tau$ on $G^+(V)$ is $F^\times$ (Shimura, Theorem 3.6 (iii), proof via Corollary 2.9). -/
theorem tau_eq_one_iff (hQ : (QuadraticMap.associated Q).Nondegenerate) (a : M0 Q) :
    tau (Subgroup.inclusion M0_le a) = 1 ↔
      ((a : (CliffordAlgebra Q)ˣ) : A) ∈ Set.range (algebraMap F A) := by
  rw [← conjM0_eq_one_iff hQ]
  simp only [tau, conjM0_apply, map_inv, inv_eq_one]

/-- **Theorem 3.6 (iii)** (Shimura, p. 22): $\tau$ induces an isomorphism $G^+(V)/F^\times \cong SO^\varphi(V)$, for
nondegenerate $\varphi$. Stated as: the kernel of $a \mapsto \tau(a)$ on $G^+(V)$ is $F^\times$ and its image is
$SO^\varphi(V)$, together with the resulting isomorphism of groups $G^+(V)/\ker \cong SO^\varphi(V)$ (written with
$a \mapsto \tau(a)^{-1} = (x \mapsto axa^{-1})$, which is a homomorphism for left composition). -/
@[kb "shimura2004" "Thm. 3.6 (iii), p. 22 (τ gives G⁺(V)/F^× ≅ SO^φ)"]
theorem theorem_3_6_iii (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    (∀ a : M0 Q, tau (Subgroup.inclusion M0_le a) ∈ orthPlus Q) ∧
    (∀ α ∈ orthPlus Q, ∃ a : M0 Q, tau (Subgroup.inclusion M0_le a) = α) ∧
    (∀ a : M0 Q, tau (Subgroup.inclusion M0_le a) = 1 ↔
      ((a : (CliffordAlgebra Q)ˣ) : A) ∈ Set.range (algebraMap F A)) ∧
    Nonempty ((M0 Q ⧸ (conjM0 (Q := Q)).ker) ≃* orthPlus Q) := by
  refine ⟨tau_mem_orthPlus hQ, fun α hα => exists_tau_eq hQ hα, tau_eq_one_iff hQ, ?_⟩
  exact ⟨(QuotientGroup.quotientKerEquivRange conjM0).trans (MulEquiv.subgroupCongr (range_conjM0 hQ))⟩

/-! ### (3.5), the spin group `G¹(V)` (3.6), the spinor norm (3.7) and (3.7a) -/

/-- **(3.5)** (Shimura, p. 23): if $a \in A^+(V)$, $aa^* \in F^\times$ and $aVa^* \subseteq V$, then
$a \in G^+(V)$ (because $a^{-1} = (aa^*)^{-1}a^*$). -/
@[kb "shimura2004" "(3.5), p. 23 (aa* ∈ F^× and aVa* ⊆ V imply a ∈ G⁺(V))"]
theorem mem_M0_of_mul_reverse {a : A} (ha : a ∈ evenOdd Q 0) {c : F} (hc : c ≠ 0)
    (hac : a * reverse a = algebraMap F A c) (haV : ∀ x : V, ∃ y : V, ι Q y = a * ι Q x * reverse a) :
    ∃ u : (CliffordAlgebra Q)ˣ, (u : A) = a ∧ u ∈ M0 Q := by
  obtain ⟨-, h1, h2⟩ := inverse_of_mul_reverse Q hc hac
  refine ⟨⟨a, c⁻¹ • reverse a, h1, h2⟩, rfl, ha, fun x => ?_⟩
  obtain ⟨y, hy⟩ := haV x
  refine ⟨c⁻¹ • y, ?_⟩
  change ι Q (c⁻¹ • y) = a * ι Q x * (c⁻¹ • reverse a)
  rw [map_smul, hy, mul_smul_comm]

variable (Q) in
/-- **The spin group** $G^1(V) = \{a \in G^+(V) \mid \nu(a) = 1\}$ (Shimura (3.6), p. 23), i.e. the
$a \in G^+(V)$ with $aa^* = 1$. -/
@[kb "shimura2004" "(3.6), p. 23 (the spin group G¹(V) = {a ∈ G⁺(V) | ν(a) = 1})"]
def spinGroupG1 : Subgroup (CliffordAlgebra Q)ˣ where
  carrier := {a | a ∈ M0 Q ∧ (a : A) * reverse (a : A) = 1}
  one_mem' := ⟨(M0 Q).one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(M0 Q).mul_mem ha hb, ?_⟩
    rw [Units.val_mul, reverse.map_mul, mul_assoc, ← mul_assoc (b : A), hb', one_mul, ha']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(M0 Q).inv_mem ha, ?_⟩
    -- `reverse a = a⁻¹`, so `reverse a⁻¹ = a`
    have hr : reverse (a : A) = ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) := by
      calc reverse (a : A) = ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * ((a : A) * reverse (a : A)) := by
            rw [← mul_assoc]; simp
        _ = _ := by rw [ha', mul_one]
    have hr' : reverse ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) = (a : A) := by
      rw [← hr, reverse_reverse]
    rw [hr']
    simp

theorem spinGroupG1_le_M0 : spinGroupG1 Q ≤ M0 Q := fun _ h => h.1

/-- $G^1(V)$ is the kernel of $\nu$ on $G^+(V)$ (Shimura (3.6)). -/
theorem mem_spinGroupG1_iff_multiplier (hQ : (QuadraticMap.associated Q).Nondegenerate) (a : M0 Q) :
    (a : (CliffordAlgebra Q)ˣ) ∈ spinGroupG1 Q ↔ multiplier hQ ⟨a, M0_le_homogeneous a.2⟩ = 1 := by
  rw [Units.ext_iff, Units.val_one, ← (algebraMap F A).injective.eq_iff, algebraMap_multiplier, map_one]
  exact ⟨fun h => h.2, fun h => ⟨a.2, h⟩⟩

/-- **$F^\times \cap G^1(V) = \{\pm 1\}$** (Shimura, p. 23). -/
@[kb "shimura2004" "§3, p. 23 (F^× ∩ G¹(V) = {±1})"]
theorem algebraMap_mem_spinGroupG1_iff (c : Fˣ) :
    Units.map (algebraMap F A).toMonoidHom c ∈ spinGroupG1 Q ↔ c = 1 ∨ c = -1 := by
  have hinj := (algebraMap F A).injective
  constructor
  · rintro ⟨-, h⟩
    change algebraMap F A (c : F) * reverse (algebraMap F A (c : F)) = 1 at h
    rw [reverse.commutes, ← map_mul, ← map_one (algebraMap F A)] at h
    have h' : (c : F) * c = 1 := hinj h
    have : ((c : F) - 1) * ((c : F) + 1) = 0 := by ring_nf; rw [sq, h']; ring
    rcases mul_eq_zero.1 this with h1 | h1
    · left; ext; simpa [sub_eq_zero] using h1
    · right; ext; simpa [eq_neg_iff_add_eq_zero] using h1
  · rintro (rfl | rfl)
    · simpa using (spinGroupG1 Q).one_mem
    · refine ⟨scalar_mem_M0 (-1), ?_⟩
      change algebraMap F A ((-1 : Fˣ) : F) * reverse (algebraMap F A ((-1 : Fˣ) : F)) = 1
      rw [reverse.commutes, ← map_mul]
      simp

/-- **$\tau$ is injective on $G^1(V)/\{\pm1\}$** (Shimura, p. 23): for $a \in G^1(V)$, $\tau(a) = 1$ if and only if
$a = \pm 1$. -/
@[kb "shimura2004" "§3, p. 23 (τ gives an injection of G¹(V)/{±1} into SO^φ)"]
theorem tau_eq_one_iff_of_mem_spinGroupG1 (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {a : (CliffordAlgebra Q)ˣ} (ha : a ∈ spinGroupG1 Q) :
    tau ⟨a, ha.1.2⟩ = 1 ↔ (a : A) = 1 ∨ (a : A) = -1 := by
  have h := tau_eq_one_iff hQ ⟨a, ha.1⟩
  change tau ⟨a, ha.1.2⟩ = 1 ↔ _ at h
  rw [h]
  constructor
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact a.ne_zero (by rw [← hc, map_zero])
    have hmem : Units.map (algebraMap F A).toMonoidHom (Units.mk0 c hc0) ∈ spinGroupG1 Q := by
      have : Units.map (algebraMap F A).toMonoidHom (Units.mk0 c hc0) = a := Units.ext (by simpa using hc)
      rw [this]; exact ha
    rcases (algebraMap_mem_spinGroupG1_iff _).1 hmem with h1 | h1
    · left; rw [← hc]; simpa using congrArg (fun u : Fˣ => algebraMap F A (u : F)) h1
    · right; rw [← hc]; simpa using congrArg (fun u : Fˣ => algebraMap F A (u : F)) h1
  · rintro (h1 | h1)
    · exact ⟨1, by rw [h1, map_one]⟩
    · exact ⟨-1, by rw [h1, map_neg, map_one]⟩

/-- **$G^1(V)$ is Mathlib's spin group** (Shimura (3.6), p. 23): for nondegenerate $\varphi$ on $V \ne 0$, a unit
$a$ lies in $G^1(V)$ if and only if it lies in `spinGroup Q` (the even elements of the Lipschitz group with
$\bar a a = a \bar a = 1$). Via Cassels' description of $\operatorname{Spin}(V)$ (`Cassels.mem_spinGroup_iff`). -/
@[kb "shimura2004" "(3.6), p. 23 (G¹(V) is the spin group)"]
theorem mem_spinGroupG1_iff_mem_spinGroup [Nontrivial V] (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (a : (CliffordAlgebra Q)ˣ) : a ∈ spinGroupG1 Q ↔ (a : A) ∈ spinGroup Q := by
  rw [mem_spinGroup_iff hQ]
  have key : ∀ (h1 : (a : A) * reverse (a : A) = 1), reverse (a : A) = ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) :=
    fun h1 => by
      calc reverse (a : A) = ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * ((a : A) * reverse (a : A)) := by
            rw [← mul_assoc]; simp
        _ = _ := by rw [h1, mul_one]
  constructor
  · rintro ⟨⟨h0, hG⟩, h1⟩
    exact ⟨h0, h1, fun x => by rw [key h1]; exact hG x⟩
  · rintro ⟨h0, h1, hx⟩
    exact ⟨⟨h0, fun x => by rw [← key h1]; exact hx x⟩, h1⟩

/-- Square classes of $c$ and $c^{-1}$ agree. -/
theorem sqClassOf_inv {c : F} (hc : c ≠ 0) : Lattices.sqClassOf c⁻¹ = Lattices.sqClassOf c := by
  have hs : Lattices.sqClassOf (c * c) = 1 := (Sp55.sqClassOf_eq_one_iff' (mul_ne_zero hc hc)).2 ⟨c, rfl⟩
  have h := Sp55.sqClassOf_mul' (inv_ne_zero hc) (mul_ne_zero hc hc)
  rw [show c⁻¹ * (c * c) = c by field_simp, hs, mul_one] at h
  exact h.symm

/-- **The spinor norm via the multiplier** (Shimura (3.7), p. 24): for $\xi \in G^+(V)$, the spinor norm of
$\tau(\xi) \in SO^\varphi(V)$ is the square class of $\nu(\xi)$. So Shimura's $\sigma$ (defined by this formula,
well defined by Theorem 3.6 (iii)) is O'Meara's spinor norm $\theta$ (`OMeara.spinorNormHom`). -/
@[kb "shimura2004" "(3.7), p. 24 (spinor norm σ(τ(ξ)) = ν(ξ)F^{×2})"]
theorem spinorNormHom_tau (hQ : (QuadraticMap.associated Q).Nondegenerate) (ξ : M0 Q) :
    spinorNormHom Q hQ ⟨tau (Subgroup.inclusion M0_le ξ), tau_mem_orthPlus hQ ξ⟩ =
      Lattices.sqClassOf (multiplier hQ ⟨ξ, M0_le_homogeneous ξ.2⟩ : F) := by
  have hξ := algebraMap_multiplier_M0 hQ ξ
  have hξi := algebraMap_multiplier_M0 hQ ξ⁻¹
  have hc := spinorNormHom_conjM0 hQ ξ⁻¹ hξi.symm
  have heq : (⟨tau (Subgroup.inclusion M0_le ξ), tau_mem_orthPlus hQ ξ⟩ : orthPlus Q) =
      ⟨conjM0 ξ⁻¹, conjM0_mem_orthPlus hQ ξ⁻¹⟩ := by
    ext1; simp [tau, conjM0_apply]
  rw [heq, hc]
  have hmul : multiplier hQ ⟨(ξ⁻¹ : M0 Q), M0_le_homogeneous (ξ⁻¹).2⟩ =
      (multiplier hQ ⟨ξ, M0_le_homogeneous ξ.2⟩)⁻¹ := by
    rw [← map_inv]; rfl
  rw [hmul, Units.val_inv_eq_inv_val, sqClassOf_inv (Units.ne_zero _)]

/-- **(3.7a)** (Shimura, p. 24): $\tau(G^1(V)) = \{\alpha \in SO^\varphi(V) \mid \sigma(\alpha) = 1\}$, for
nondegenerate $\varphi$ on $V \ne 0$. The right side is O'Meara's $O'(V)$ = `orthPrime Q`, the kernel of the spinor
norm (`OMeara.ker_spinorNormHom`). -/
@[kb "shimura2004" "(3.7a), p. 24 (τ(G¹(V)) = {α ∈ SO^φ(V) | σ(α) = 1})"]
theorem tau_image_spinGroupG1 [Nontrivial V] (hQ : (QuadraticMap.associated Q).Nondegenerate) (α : V ≃ₗ[F] V) :
    (∃ a : (CliffordAlgebra Q)ˣ, ∃ ha : a ∈ spinGroupG1 Q, tau ⟨a, ha.1.2⟩ = α) ↔
      α ∈ orthPlus Q ∧ HasSpinorNorm Q α 1 := by
  change _ ↔ α ∈ orthPrime Q
  rw [← range_spinConj hQ]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hs : ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) ∈ spinGroup Q :=
      (mem_spinGroupG1_iff_mem_spinGroup hQ _).1 ((spinGroupG1 Q).inv_mem ha)
    refine ⟨⟨_, hs⟩, ?_⟩
    rw [spinConj_eq, conjM0_apply, tau]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rfl
  · rintro ⟨u, rfl⟩
    have hu : spinGroup.toUnits u ∈ spinGroupG1 Q :=
      (mem_spinGroupG1_iff_mem_spinGroup hQ _).2 u.2
    refine ⟨(spinGroup.toUnits u)⁻¹, (spinGroupG1 Q).inv_mem hu, ?_⟩
    rw [spinConj_eq, conjM0_apply, tau]
    congr 1

end QuadFormsKB.Shimura2004
