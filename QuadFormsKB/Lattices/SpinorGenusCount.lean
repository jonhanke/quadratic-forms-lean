/-
# The number of spinor genera in a genus

**Layer:** lattices in $(V, Q) = (F^n, Q)$ over a number field $F$, $Q$ nondegenerate; the spinor norm
(`Lattices/SpinorNorm.lean`) and the spinor genus (`Lattices/SpinorGenus.lean`).

**Proves**
* `sq_mem_spinorKernelAf`, `commutator_mem_spinorKernelAf`: squares and commutators of $O(V)(\mathbb A_f)$ lie in
  $O'(V_{\mathbb A_f})$ (componentwise, from $O(V_\mathfrak p)/O'(V_\mathfrak p) \hookrightarrow K_\mathfrak p^\times/K_\mathfrak p^{\times2}
  \times \{\pm1\}$);
* hence $O(V)O'(V_{\mathbb A_f})$ and $J_L := O(V)\,O'(V_{\mathbb A_f})\,O(\hat L)$ (`spnLocGroup`) are **normal** in
  $O(V)(\mathbb A_f)$, and
  $$\{\text{spinor genera in } \mathrm{gen}(L)\} \;\simeq\; O(V)(\mathbb A_f)/J_L \qquad (\texttt{spinorGeneraEquivQuot}),$$
  a quotient **group** that is abelian and of exponent $2$ (`spinorGeneraQuot_mul_self`): the number of spinor genera in
  a genus is the index $[O(V)(\mathbb A_f) : O(V)O'(V_{\mathbb A_f})O(\hat L)]$, a power of $2$ when finite
  (O'Meara 1963, 102:7–102:8 [unverified]; Cassels 1978, Ch. 11 §3 [unverified]).
-/
import QuadFormsKB.Lattices.SpinorGenus
import QuadFormsKB.Lattices.SpinorNorm

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **Squares of adelic isometries lie in $O'(V_{\mathbb A_f})$.** -/
theorem sq_mem_spinorKernelAf (hQ : Q.Nondegenerate) (h : OAf Q) : h ^ 2 ∈ spinorKernelAf Q := fun v =>
  sq_mem_spinorKernel Q (v.adicCompletion F) hQ (h v)

/-- **Commutators of adelic isometries lie in $O'(V_{\mathbb A_f})$.** -/
theorem commutator_mem_spinorKernelAf (hQ : Q.Nondegenerate) (g h : OAf Q) :
    g * h * g⁻¹ * h⁻¹ ∈ spinorKernelAf Q := fun v =>
  commutator_mem_spinorKernel Q (v.adicCompletion F) hQ (g v) (h v)

/-- A subgroup containing $O'(V_{\mathbb A_f})$ is normal (it contains all commutators). -/
theorem normal_of_spinorKernelAf_le (hQ : Q.Nondegenerate) {H : Subgroup (OAf Q)} (hH : spinorKernelAf Q ≤ H) :
    H.Normal where
  conj_mem x hx g := by
    have hc : g * x * g⁻¹ * x⁻¹ ∈ H := hH (commutator_mem_spinorKernelAf Q hQ g x)
    have : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
    rw [this]; exact H.mul_mem hc hx

/-- $J_L = O(V)\,O'(V_{\mathbb A_f})\,O(\hat L)$. -/
@[kb "omeara1963" "102:7 [unverified]"]
def spnLocGroup (L : Lat F n) : Subgroup (OAf Q) := spnGroup Q ⊔ locStab Q L

theorem spnGroup_normal (hQ : Q.Nondegenerate) : (spnGroup Q).Normal :=
  normal_of_spinorKernelAf_le Q hQ (spinorKernelAf_le_spnGroup Q)

theorem spnLocGroup_normal (hQ : Q.Nondegenerate) (L : Lat F n) : (spnLocGroup Q L).Normal :=
  normal_of_spinorKernelAf_le Q hQ ((spinorKernelAf_le_spnGroup Q).trans le_sup_left)

/-- For $N$ normal: $g' \in NgH \iff g^{-1}g' \in N \sqcup H$. -/
theorem doset_rel_iff_of_normal {G : Type*} [Group G] (N H : Subgroup G) [N.Normal] (g g' : G) :
    DoubleCoset.setoid (N : Set G) H g g' ↔ g⁻¹ * g' ∈ N ⊔ H := by
  rw [DoubleCoset.rel_iff, ← SetLike.mem_coe, Subgroup.normal_mul]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨g⁻¹ * a * g, Subgroup.Normal.conj_mem' inferInstance a ha g, b, hb, by group⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨g * a * g⁻¹, Subgroup.Normal.conj_mem inferInstance a ha g, b, hb, ?_⟩
    calc g' = g * (g⁻¹ * g') := by group
      _ = g * a * g⁻¹ * g * b := by rw [← hab]; group

/-- $O(V)O'(V_{\mathbb A_f})\backslash O(V)(\mathbb A_f)/O(\hat L) \simeq O(V)(\mathbb A_f)/J_L$. -/
def dosetEquivQuot (hQ : Q.Nondegenerate) (L : Lat F n) :
    DoubleCoset.Quotient (spnGroup Q : Set (OAf Q)) (locStab Q L) ≃ OAf Q ⧸ spnLocGroup Q L :=
  have := spnGroup_normal Q hQ
  Quotient.congr (Equiv.refl _) fun g g' => by
    rw [Equiv.refl_apply, Equiv.refl_apply, doset_rel_iff_of_normal, QuotientGroup.leftRel_apply]
    rfl

/-- **The spinor genera in $\mathrm{gen}(L)$ form the group $O(V)(\mathbb A_f)/O(V)O'(V_{\mathbb A_f})O(\hat L)$**
(O'Meara 1963, 102:7–102:8 [unverified]): the number of spinor genera in the genus is the index
$[O(V)(\mathbb A_f) : J_L]$. -/
@[kb "omeara1963" "102:7-102:8 [unverified]"]
def spinorGeneraEquivQuot (hQ : Q.Nondegenerate) (L : Lat F n) :
    @AWS.ClassesInGenus (OAf Q) (Lat F n) _ (latAction Q) (spnGroup Q) L ≃ OAf Q ⧸ spnLocGroup Q L :=
  (dosetEquivSpinorGenera Q L).symm.trans (dosetEquivQuot Q hQ L)

instance spnLocGroup_normal' [hQ : Fact Q.Nondegenerate] (L : Lat F n) : (spnLocGroup Q L).Normal :=
  spnLocGroup_normal Q hQ.out L

/-- **The spinor-genus group is an elementary abelian $2$-group**: every element squares to $1$ (O'Meara 1963,
102:8 [unverified]). -/
@[kb "omeara1963" "102:8 [unverified]"]
theorem spinorGeneraQuot_mul_self [hQ : Fact Q.Nondegenerate] (L : Lat F n) (x : OAf Q ⧸ spnLocGroup Q L) :
    x * x = 1 := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← sq]
    exact le_sup_left (a := spnGroup Q) (spinorKernelAf_le_spnGroup Q (sq_mem_spinorKernelAf Q hQ.out g))

/-- The spinor-genus group is abelian. -/
theorem spinorGeneraQuot_comm [hQ : Fact Q.Nondegenerate] (L : Lat F n) (x y : OAf Q ⧸ spnLocGroup Q L) :
    x * y = y * x := by
  induction x using QuotientGroup.induction_on with
  | H g =>
  induction y using QuotientGroup.induction_on with
  | H h =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hc := commutator_mem_spinorKernelAf Q hQ.out h⁻¹ g⁻¹
    have : (g * h)⁻¹ * (h * g) = h⁻¹ * g⁻¹ * h⁻¹⁻¹ * g⁻¹⁻¹ := by group
    rw [this]
    exact le_sup_left (a := spnGroup Q) (spinorKernelAf_le_spnGroup Q hc)

end QuadFormsKB.Lattices
