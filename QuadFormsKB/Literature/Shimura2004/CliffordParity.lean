/-
# Shimura 2004, §3: Theorem 3.6 (i), (ii): the Clifford group in even and odd dimension

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (bibliography key `shimura2004`), Chapter I, Theorem 3.6, printed p. 22.
Notation and dictionary as in `CliffordGroups.lean`: $G(V)$ is `Cassels.cliffordGroup Q`, $G^+(V)$ is `Cassels.M0 Q`,
$G^-(V)$ is `cliffordGroupOdd Q`, $G'(V)$ is `homogeneousCliffordGroup Q`, $\tau(a)$ is `tau a`
($x \mapsto a^{-1}xa$), $O^\varphi(V)$, $SO^\varphi(V)$ are `OMeara.orth Q`, `OMeara.orthPlus Q`, and $n = \dim V$ is
`Module.finrank F V`. The form $\varphi$ is assumed nondegenerate (`hQ`).

**Proves** (all unconditional; standard axioms only)
* Theorem 3.6 (ii), $n$ even and $V \ne 0$: $G(V) = G'(V)$ (`cliffordGroup_le_homogeneous_of_even`),
  $\tau(G(V)) = O^\varphi(V)$ (`exists_tau_eq_of_mem_orth_of_even`), and $\det\tau(a) = -1$ for $a \in G^-(V)$ while
  every $\alpha \in O^\varphi(V)$ with $\det\alpha = -1$ is $\tau(a)$ for some $a \in G^-(V)$
  (`det_tau_of_mem_cliffordGroupOdd_of_even`, `exists_tau_eq_of_det_eq_neg_one_of_even`).
* Theorem 3.6 (i), $n$ odd: $-1 \notin \tau(G(V))$ (`tau_ne_neg_one_of_odd`), $\tau(G(V)) = SO^\varphi(V)$
  (`det_tau_eq_one_of_odd`, `tau_mem_range_iff_of_odd`), and $G(V) = \mathfrak c^\times G^+(V)$ with $\mathfrak c$ the
  centre of $A(V)$ (`exists_central_mul_of_odd`).

**Proof notes.** The key step, for any $n$, is that $a \in G(V)$ with $\det\tau(a) = 1$ equals $w b$ with $b \in G^+(V)$
and $\tau(w) = 1$ (Theorem 3.6 (iii) surjectivity), so $w$ commutes with $V$, hence with all of $A(V)$
(`commute_of_commute_ι`). For $n$ even the centre of $A(V)$ is $F$ (Arizona Winter School Notes, Thm. 3.2.4,
`Cliff324.center_scalar_even`), so $w$ is a scalar and $a$ is even; multiplication by an invertible vector $v$,
$\det\tau(v) = \det(-\text{symmetry}) = (-1)^n\cdot(-1)$, handles $\det\tau(a) = -1$. For $n$ odd the product
$z$ of an orthogonal anisotropic basis is odd, nonzero and central; if $\tau(a) = -1$ then $a^{-1}ya = y'$ for all $y$,
so $z = z' = -z$, a contradiction.
-/
import QuadFormsKB.Literature.Shimura2004.CliffordGroups
import QuadFormsKB.Literature.AWS.NotesClifford
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

local notation "A" => CliffordAlgebra Q

/-! ### Auxiliary facts -/

/-- An element commuting with every vector $\iota(x)$ commutes with all of $A(V)$. -/
theorem commute_of_commute_ι {z : A} (h : ∀ x : V, z * ι Q x = ι Q x * z) (g : A) : z * g = g * z := by
  induction g using CliffordAlgebra.induction with
  | algebraMap r => exact (Algebra.commutes r z).symm
  | ι x => exact h x
  | mul a b ha hb => rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  | add a b ha hb => rw [mul_add, add_mul, ha, hb]

/-- $\tau(w) = 1$ means that $w$ commutes with every vector. -/
theorem comm_of_tau_eq_one {w : cliffordGroup Q} (h : tau w = 1) (x : V) :
    ((w : (CliffordAlgebra Q)ˣ) : A) * ι Q x = ι Q x * ((w : (CliffordAlgebra Q)ˣ) : A) := by
  have h1 := tau_spec w x
  rw [h] at h1
  change ι Q x = _ at h1
  calc ((w : (CliffordAlgebra Q)ˣ) : A) * ι Q x
      = ((w : (CliffordAlgebra Q)ˣ) : A) *
        ((((w : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : A) * ι Q x * ((w : (CliffordAlgebra Q)ˣ) : A)) := by
        rw [← h1]
    _ = ι Q x * ((w : (CliffordAlgebra Q)ˣ) : A) := by
        simp only [← mul_assoc, Units.mul_inv, one_mul]

/-- The determinant of $x \mapsto -x$ is $(-1)^n$. -/
theorem det_neg_equiv : LinearEquiv.det (LinearEquiv.neg F : V ≃ₗ[F] V) = (-1 : Fˣ) ^ finrank F V := by
  apply Units.ext
  rw [LinearEquiv.coe_det, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  have : ((LinearEquiv.neg F : V ≃ₗ[F] V) : V →ₗ[F] V) = (-1 : F) • LinearMap.id := by
    ext x; simp
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]

theorem neg_equiv_mem_orth : (LinearEquiv.neg F : V ≃ₗ[F] V) ∈ orth Q := fun x => by
  simp

/-- Every orthogonal transformation has determinant $\pm 1$ (Cartan–Dieudonné). -/
theorem det_eq_one_or_neg_one (hQ : (QuadraticMap.associated Q).Nondegenerate) {α : V ≃ₗ[F] V}
    (hα : α ∈ orth Q) : LinearEquiv.det α = 1 ∨ LinearEquiv.det α = -1 := by
  obtain ⟨l, hl, hσl, -⟩ := exists_symmetry_prod_eq_length_le Q hQ hα
  have hσl' : α = QuadFormsKB.Cassels.symProd l hl := hσl
  rw [hσl', QuadFormsKB.Cassels.det_symProd]
  rcases Nat.even_or_odd l.length with h | h
  · exact Or.inl h.neg_one_pow
  · exact Or.inr h.neg_one_pow

theorem algebraMap_mem_evenOdd_zero (c : F) : algebraMap F A c ∈ evenOdd Q 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ one_mem_evenOdd_zero

/-- If $\det\tau(y) = 1$, then $y = wb$ with $\tau(w) = 1$ and $b \in G^+(V)$ (Theorem 3.6 (iii), surjectivity). -/
theorem exists_tau_eq_one_mul (hQ : (QuadraticMap.associated Q).Nondegenerate) (y : cliffordGroup Q)
    (h : LinearEquiv.det (tau y) = 1) :
    ∃ w : cliffordGroup Q, tau w = 1 ∧ ∃ b ∈ M0 Q, (y : (CliffordAlgebra Q)ˣ) = (w : (CliffordAlgebra Q)ˣ) * b := by
  obtain ⟨b, hb⟩ := exists_tau_eq hQ (α := tau y) ⟨tau_mem_orth y, MonoidHom.mem_ker.2 h⟩
  refine ⟨y * (Subgroup.inclusion M0_le b)⁻¹, ?_, b, b.2, ?_⟩
  · rw [tau_mul, tau_inv, hb, inv_mul_cancel]
  · simp

/-- For even $n$, an element $y \in G(V)$ with $\det\tau(y) = 1$ is even. -/
theorem mem_evenOdd_zero_of_det_tau_eq_one (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : Even (finrank F V)) (y : cliffordGroup Q) (h : LinearEquiv.det (tau y) = 1) :
    ((y : (CliffordAlgebra Q)ˣ) : A) ∈ evenOdd Q 0 := by
  obtain ⟨w, hw, b, hb, hy⟩ := exists_tau_eq_one_mul hQ y h
  obtain ⟨e, he, hea⟩ := OMeara.Cl54.exists_orthogonal_anisotropic_basis Q hQ
  obtain ⟨c, hc⟩ := AWS.Notes.Cliff324.center_scalar_even Q e he hea hn _ (comm_of_tau_eq_one hw)
  rw [hy, Units.val_mul, hc]
  simpa using mul_mem_evenOdd (algebraMap_mem_evenOdd_zero c) hb.1

/-- $\det\tau(v) = -1$ for an invertible vector $v$ when $n$ is even: $\tau(v) = -\text{symmetry}_v$ up to
inversion. -/
theorem det_tau_vecUnit (hn : Even (finrank F V)) (v : V) (hv : Q v ≠ 0) :
    LinearEquiv.det (tau ⟨vecUnit v hv, vecUnit_mem v hv⟩) = -1 := by
  rw [tau, map_inv, conjHom_vecUnit_eq, map_inv, map_mul, det_neg_equiv, hn.neg_one_pow, det_symmetry]
  simp

/-- For even $n$, an element $y \in G(V)$ with $\det\tau(y) = -1$ is odd. -/
theorem mem_evenOdd_one_of_det_tau_eq_neg_one [Nontrivial V]
    (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : Even (finrank F V)) (y : cliffordGroup Q)
    (h : LinearEquiv.det (tau y) = -1) : ((y : (CliffordAlgebra Q)ˣ) : A) ∈ evenOdd Q 1 := by
  obtain ⟨v, hv⟩ := exists_anisotropic hQ (Q := Q)
  have hd : LinearEquiv.det (tau (y * ⟨vecUnit v hv, vecUnit_mem v hv⟩)) = 1 := by
    rw [tau_mul, map_mul, h, det_tau_vecUnit hn v hv]; simp
  have h0 := mem_evenOdd_zero_of_det_tau_eq_one hQ hn _ hd
  have hxi : (((vecUnit v hv)⁻¹ : (CliffordAlgebra Q)ˣ) : A) ∈ evenOdd Q 1 :=
    mem_evenOdd_of_mul_eq_one Q (ι_mem_evenOdd_one Q v) (vecUnit v hv).mul_inv
  have h0' : (((y : (CliffordAlgebra Q)ˣ) * vecUnit v hv : (CliffordAlgebra Q)ˣ) : A) ∈ evenOdd Q 0 := h0
  have hm := mul_mem_evenOdd h0' hxi
  rw [show (0 : ZMod 2) + 1 = 1 from rfl, ← Units.val_mul, mul_inv_cancel_right] at hm
  exact hm

/-! ### Theorem 3.6 (ii): $n$ even -/

/-- **Theorem 3.6 (ii)** (Shimura, p. 22), $G(V) = G'(V)$: for $n$ even and $V \ne 0$, every element of the Clifford
group is even or odd. -/
@[kb "shimura2004" "Thm. 3.6 (ii), p. 22 (n even: G(V) = G'(V))"]
theorem cliffordGroup_le_homogeneous_of_even [Nontrivial V] (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : Even (finrank F V)) : cliffordGroup Q ≤ homogeneousCliffordGroup Q := by
  intro y hy
  refine ⟨hy, ?_⟩
  rcases det_eq_one_or_neg_one hQ (tau_mem_orth (⟨y, hy⟩ : cliffordGroup Q)) with h | h
  · exact Or.inl (mem_evenOdd_zero_of_det_tau_eq_one hQ hn ⟨y, hy⟩ h)
  · exact Or.inr (mem_evenOdd_one_of_det_tau_eq_neg_one hQ hn ⟨y, hy⟩ h)

/-- **Theorem 3.6 (ii)** (Shimura, p. 22), $\det\tau(a) = -1$ on $G^-(V)$ (for $n$ even and $V \ne 0$; for odd
elements $a$ of $G(V)$ the determinant is $-1$, and $\det\tau = 1$ on $G^+(V)$ by Theorem 3.6 (iii)). -/
@[kb "shimura2004" "Thm. 3.6 (ii), p. 22 (n even: det τ(a) = −1 for a ∈ G⁻(V))"]
theorem det_tau_of_mem_cliffordGroupOdd_of_even [Nontrivial V] (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : Even (finrank F V)) {a : (CliffordAlgebra Q)ˣ} (ha : a ∈ cliffordGroupOdd Q) :
    LinearEquiv.det (tau ⟨a, ha.1⟩) = -1 := by
  rcases det_eq_one_or_neg_one hQ (tau_mem_orth (⟨a, ha.1⟩ : cliffordGroup Q)) with h | h
  · exfalso
    have h0 := mem_evenOdd_zero_of_det_tau_eq_one hQ hn ⟨a, ha.1⟩ h
    have hdisj := (evenOdd_isCompl Q).disjoint
    rw [Submodule.disjoint_def] at hdisj
    exact a.ne_zero (hdisj _ h0 ha.2)
  · exact h

/-- **Theorem 3.6 (ii)** (Shimura, p. 22), converse: for $n$ even and $V \ne 0$, every $\alpha \in O^\varphi(V)$ with
$\det\alpha = -1$ is $\tau(a)$ for some $a \in G^-(V)$. -/
@[kb "shimura2004" "Thm. 3.6 (ii), p. 22 (n even: α ∈ O^φ, det α = −1 is τ(a), a ∈ G⁻(V))"]
theorem exists_tau_eq_of_det_eq_neg_one_of_even [Nontrivial V] (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : Even (finrank F V)) {α : V ≃ₗ[F] V} (hα : α ∈ orth Q) (hd : LinearEquiv.det α = -1) :
    ∃ (a : (CliffordAlgebra Q)ˣ) (ha : a ∈ cliffordGroupOdd Q), tau ⟨a, ha.1⟩ = α := by
  obtain ⟨v, hv⟩ := exists_anisotropic hQ (Q := Q)
  set vg : cliffordGroup Q := ⟨vecUnit v hv, vecUnit_mem v hv⟩ with hvg
  have hδ : (tau vg)⁻¹ * α ∈ orthPlus Q := by
    refine ⟨(orth Q).mul_mem ((orth Q).inv_mem (tau_mem_orth vg)) hα, MonoidHom.mem_ker.2 ?_⟩
    rw [map_mul, map_inv, det_tau_vecUnit hn v hv, hd]
    simp
  obtain ⟨b, hb⟩ := exists_tau_eq hQ hδ
  have hmem : (b : (CliffordAlgebra Q)ˣ) * vecUnit v hv ∈ cliffordGroup Q :=
    (cliffordGroup Q).mul_mem (M0_le b.2) (vecUnit_mem v hv)
  refine ⟨(b : (CliffordAlgebra Q)ˣ) * vecUnit v hv,
    ⟨hmem, by
      have hm := mul_mem_evenOdd b.2.1 (ι_mem_evenOdd_one Q v)
      rw [show (0 : ZMod 2) + 1 = 1 from rfl] at hm
      rw [Units.val_mul]
      exact hm⟩, ?_⟩
  have : (⟨(b : (CliffordAlgebra Q)ˣ) * vecUnit v hv, hmem⟩ : cliffordGroup Q) =
      Subgroup.inclusion M0_le b * vg := rfl
  rw [this, tau_mul, hb, mul_inv_cancel_left]

/-- **Theorem 3.6 (ii)** (Shimura, p. 22), $\tau(G(V)) = O^\varphi(V)$: for $n$ even and $V \ne 0$, every
orthogonal transformation is $\tau(a)$ for some $a \in G(V)$. -/
@[kb "shimura2004" "Thm. 3.6 (ii), p. 22 (n even: τ(G(V)) = O^φ(V))"]
theorem exists_tau_eq_of_mem_orth_of_even [Nontrivial V] (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : Even (finrank F V)) : ∀ α ∈ orth Q, ∃ a : cliffordGroup Q, tau a = α := by
  intro α hα
  rcases det_eq_one_or_neg_one hQ hα with h | h
  · obtain ⟨b, hb⟩ := exists_tau_eq hQ (α := α) ⟨hα, MonoidHom.mem_ker.2 h⟩
    exact ⟨Subgroup.inclusion M0_le b, hb⟩
  · obtain ⟨a, ha, hτ⟩ := exists_tau_eq_of_det_eq_neg_one_of_even hQ hn hα h
    exact ⟨⟨a, ha.1⟩, hτ⟩

/-! ### Theorem 3.6 (i): $n$ odd -/

/-- **Theorem 3.6 (i)** (Shimura, p. 22): for $n$ odd, $-1 \notin \tau(G(V))$, i.e. no $a \in G(V)$ has
$a^{-1}xa = -x$ for all $x \in V$. -/
@[kb "shimura2004" "Thm. 3.6 (i), p. 22 (n odd: −1 ∉ τ(G(V)))"]
theorem tau_ne_neg_one_of_odd (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : Odd (finrank F V))
    (a : cliffordGroup Q) : tau a ≠ LinearEquiv.neg F := by
  intro h
  obtain ⟨e, he, hea⟩ := OMeara.Cl54.exists_orthogonal_anisotropic_basis Q hQ
  have := AWS.Notes.nontrivial_cliffordAlgebra Q
  -- `a⁻¹ y a = involute y` for all `y`
  have hconj : ∀ y : A, ((a : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) * y * ((a : (CliffordAlgebra Q)ˣ) : A)
      = involute y := by
    intro y
    induction y using CliffordAlgebra.induction with
    | algebraMap r =>
      rw [← Algebra.commutes, mul_assoc, Units.inv_mul, mul_one]
      exact (AlgHom.commutes _ r).symm
    | ι x =>
      have h1 := tau_spec a x
      rw [h] at h1
      change ι Q (-x) = _ at h1
      rw [map_neg] at h1
      rw [involute_ι, ← h1]
    | mul p q hp hq =>
      rw [map_mul, ← hp, ← hq]
      simp only [mul_assoc, Units.mul_inv_cancel_left]
    | add p q hp hq => rw [map_add, ← hp, ← hq, mul_add, add_mul]
  -- the product `z` of the basis vectors
  set z : A := OMeara.Cl54.bw Q e (List.finRange (finrank F V)) with hz
  have hcomm : ∀ j, ι Q (e j) * z = z * ι Q (e j) := by
    intro j
    have h1 : ι Q (e j) * z = (-1 : F) ^ ((List.finRange (finrank F V)).length +
        (List.finRange (finrank F V)).count j) • (z * ι Q (e j)) :=
      OMeara.Cl54.ub_mul_bw Q e he hea j (List.finRange (finrank F V))
    rw [h1, List.length_finRange, List.count_eq_one_of_mem (List.nodup_finRange _) (List.mem_finRange j),
      (hn.add_one).neg_one_pow, one_smul]
  have hcx : ∀ x : V, z * ι Q x = ι Q x * z := by
    intro x
    rw [← e.sum_repr x]
    simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    exact Finset.sum_congr rfl fun i _ => by rw [← hcomm i]
  have hza : z * ((a : (CliffordAlgebra Q)ˣ) : A) = ((a : (CliffordAlgebra Q)ˣ) : A) * z :=
    commute_of_commute_ι hcx _
  have hz1 : ((a : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) * z * ((a : (CliffordAlgebra Q)ˣ) : A) = z := by
    rw [mul_assoc, hza, ← mul_assoc, Units.inv_mul, one_mul]
  have hz2 : involute z = -z := by
    rw [hz, OMeara.Cl54.involute_bw, List.length_finRange, hn.neg_one_pow, neg_one_smul]
  have hzz : z = -z := by rw [← hz2, ← hconj, hz1]
  have h2z : (2 : F) • z = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hzz]
    exact add_neg_cancel z
  have hz0 : z = 0 := (smul_eq_zero.mp h2z).resolve_left (Invertible.ne_zero (2 : F))
  obtain ⟨b, hb0, hb⟩ := AWS.Notes.Cliff324.bw_rev_mul Q e hea (List.finRange (finrank F V))
  rw [← hz, hz0, mul_zero] at hb
  exact hb0 ((algebraMap F A).injective (by rw [← hb, map_zero]))

/-- **Theorem 3.6 (i)** (Shimura, p. 22), $\tau(G(V)) \subseteq SO^\varphi(V)$ for $n$ odd: $\det\tau(a) = 1$ for every
$a \in G(V)$. -/
@[kb "shimura2004" "Thm. 3.6 (i), p. 22 (n odd: τ(G(V)) ⊆ SO^φ(V), det τ(a) = 1)"]
theorem det_tau_eq_one_of_odd (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : Odd (finrank F V))
    (a : cliffordGroup Q) : LinearEquiv.det (tau a) = 1 := by
  rcases det_eq_one_or_neg_one hQ (tau_mem_orth a) with h | h
  · exact h
  · exfalso
    have hδ : LinearEquiv.neg F * tau a ∈ orthPlus Q := by
      refine ⟨(orth Q).mul_mem neg_equiv_mem_orth (tau_mem_orth a), MonoidHom.mem_ker.2 ?_⟩
      rw [map_mul, det_neg_equiv, hn.neg_one_pow, h]
      simp
    obtain ⟨b, hb⟩ := exists_tau_eq hQ hδ
    apply tau_ne_neg_one_of_odd hQ hn (a⁻¹ * Subgroup.inclusion M0_le b)
    rw [tau_mul, hb, tau_inv, mul_assoc, mul_inv_cancel, mul_one]

/-- **Theorem 3.6 (i)** (Shimura, p. 22), $\tau(G(V)) = SO^\varphi(V)$ for $n$ odd: $\alpha$ is of the form $\tau(a)$,
$a \in G(V)$, if and only if $\alpha \in SO^\varphi(V)$. -/
@[kb "shimura2004" "Thm. 3.6 (i), p. 22 (n odd: τ(G(V)) = SO^φ(V))"]
theorem tau_mem_range_iff_of_odd (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : Odd (finrank F V))
    (α : V ≃ₗ[F] V) : (∃ a : cliffordGroup Q, tau a = α) ↔ α ∈ orthPlus Q := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨tau_mem_orth a, MonoidHom.mem_ker.2 (det_tau_eq_one_of_odd hQ hn a)⟩
  · intro hα
    obtain ⟨b, hb⟩ := exists_tau_eq hQ hα
    exact ⟨Subgroup.inclusion M0_le b, hb⟩

/-- **Theorem 3.6 (i)** (Shimura, p. 22), $G(V) = \mathfrak c^\times G^+(V)$ for $n$ odd, where $\mathfrak c$ is the
centre of $A(V)$: every $y \in G(V)$ is $y = cb$ with $c$ a unit of $A(V)$ commuting with all of $A(V)$ (equivalently, with
all of $V$) and $b \in G^+(V)$. -/
@[kb "shimura2004" "Thm. 3.6 (i), p. 22 (n odd: G(V) = 𝔠^× G⁺(V), 𝔠 the centre of A(V))"]
theorem exists_central_mul_of_odd (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : Odd (finrank F V))
    {y : (CliffordAlgebra Q)ˣ} (hy : y ∈ cliffordGroup Q) :
    ∃ c : (CliffordAlgebra Q)ˣ, (∀ g : A, (c : A) * g = g * c) ∧ ∃ b ∈ M0 Q, y = c * b := by
  obtain ⟨w, hw, b, hb, hyw⟩ := exists_tau_eq_one_mul hQ ⟨y, hy⟩ (det_tau_eq_one_of_odd hQ hn _)
  exact ⟨w, commute_of_commute_ι (comm_of_tau_eq_one hw), b, hb, hyw⟩

end QuadFormsKB.Shimura2004
