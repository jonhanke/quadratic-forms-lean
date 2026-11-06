/-
# Cassels, Appendix A, §2: orthogonal decompositions of definite lattices

**Layer:** $V = F^n$ over a number field $F$ (Cassels: $F = \mathbb Q$) with the form `Q : QuadForm F n` and the
bilinear form $B(x, y) = x^{\mathsf T}H_Qy$ = `bil Q x y`, so $B(x, x) = 2Q(x)$; Cassels' $\phi(x, y)$ is
$\tfrac12 B(x, y)$, which does not change orthogonality. Lattices and sublattices are $\mathcal O_F$-submodules of
$F^n$; over $\mathbb Q$ these are exactly the additive subgroups of $\mathbb Q^n$ (`addSubgroupOrderIso`), i.e.
Cassels' sublattices, "free on a number $m \le n$ of generators" (p. 362).

The definitions and Theorem 2.1 are those of O'Meara §105 (`Literature/OMeara/Sec105.lean`), which this file reuses:

| Cassels (App. A, §2) | Lean |
|---|---|
| orthogonal sum $\Gamma_1 \perp \Gamma_2$, conditions (i)–(ii), p. 362 | `LatOrth`, `IsOrthSplitting`, `IsDecomposable` |
| indecomposable lattice, p. 362 | `IsIndecomposable` (non-zero; see below) |
| decomposable / indecomposable vector, (2.1)–(2.2), p. 363 | `IsReducibleVec`, `IsIrr` |
| equivalence of indecomposable vectors, p. 364 | `IndecEquiv` (closure of `IrrRel`) |
| existence of a decomposition, p. 363 | `exists_indecomposable_splitting` |
| Theorem 2.1 (Eichler; Kneser's proof), p. 363 | `thm_2_1` ($F = \mathbb Q$), `indecomposable_splitting_unique` |
| proof of Theorem 2.1, pp. 363–364 | `span_irr`, `existsUnique_mem_of_irr`, `mem_of_rtg`, `mem_splitting_iff_class` |
| example $x_0^2 - 2x_1^2$, p. 363 | `indefinite_not_unique` |

*Deviations.* (1) Cassels calls $\Lambda$ indecomposable if it is not the orthogonal sum of two sublattices
$\ne \Lambda$; read literally this makes the zero lattice indecomposable, and then the uniqueness in Theorem 2.1 fails
(zero summands can be added). Here, as in O'Meara, an indecomposable lattice is non-zero, and the summands of an
orthogonal splitting are non-zero. (2) Cassels' $\Lambda$ is a lattice of full rank $n$; the statements here hold for
every finitely generated $\Lambda$. (3) Cassels proves Theorem 2.1 over $\mathbb Q$; `indecomposable_splitting_unique`
is the generalization to a totally positive definite space over a number field (O'Meara 105:1). (4) The example of
an indecomposable binary lattice on p. 362, $\phi(x_1b_1 + x_2b_2) = x_1^2 + x_1x_2 + x_2^2$ (read from the page image), is
`eisensteinForm_indecomposable` in `AppA/Remaining.lean`.
-/
import QuadFormsKB.Literature.OMeara.Sec106E

open NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-! ### Citations of the O'Meara §105 declarations -/

attribute [kb "cassels1978" "App. A, §2, p. 362 (Γ₁, Γ₂ mutually orthogonal: condition (ii))"] LatOrth
attribute [kb "cassels1978" "App. A, §2, p. 362 (orthogonal sum of sublattices, (i)–(ii); several summands, p. 363)"]
  IsOrthSplitting
attribute [kb "cassels1978" "App. A, §2, p. 362 (Λ the orthogonal sum of two sublattices Γ_j ≠ Λ)"] IsDecomposable
attribute [kb "cassels1978" "App. A, §2, p. 362 (indecomposable lattice; here non-zero)"] IsIndecomposable
attribute [kb "cassels1978" "App. A, §2, (2.1)–(2.2), p. 363 (decomposable vector)"] IsReducibleVec
attribute [kb "cassels1978" "App. A, §2, p. 363 (indecomposable vector)"] IsIrr
attribute [kb "cassels1978" "App. A, §2, p. 363 (a lattice is an orthogonal sum of indecomposable sublattices)"]
  exists_indecomposable_splitting
attribute [kb "cassels1978" "App. A, §2, Thm. 2.1, p. 363 (over a number field, V totally positive definite)"]
  indecomposable_splitting_unique
attribute [kb "cassels1978" "App. A, §2, proof of Thm. 2.1, p. 363 (every b ∈ Λ is a sum of indecomposable vectors)"]
  span_irr
attribute [kb "cassels1978" "App. A, §2, proof of Thm. 2.1, p. 363 (indecomposable b₁, b₂ with φ(b₁, b₂) ≠ 0 lie in the same Γ_j)"]
  mem_of_rtg
attribute [kb "cassels1978" "App. A, §2, proof of Thm. 2.1, p. 364 (the classes generate the summands)"] eq_span_class

/-! ### Sublattices over $\mathbb Q$ are the additive subgroups -/

/-- Every element of $\mathcal O_{\mathbb Q}$ is an integer. -/
theorem exists_intCast_ringOfIntegers_rat (a : 𝓞 ℚ) : ∃ m : ℤ, ((m : ℤ) : 𝓞 ℚ) = a :=
  ⟨Rat.ringOfIntegersEquiv a, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
    (Rat.ringOfIntegersEquiv.symm_apply_apply a)⟩

/-- **Every additive subgroup of $\mathbb Q^n$ is an $\mathcal O_{\mathbb Q}$-submodule:** $a \cdot x \in G$ for
$a \in \mathcal O_{\mathbb Q} = \mathbb Z$ and $x \in G$. -/
theorem smul_mem_addSubgroup {n : ℕ} (G : AddSubgroup (Fin n → ℚ)) (a : 𝓞 ℚ) {x : Fin n → ℚ} (hx : x ∈ G) :
    a • x ∈ G := by
  obtain ⟨m, rfl⟩ := exists_intCast_ringOfIntegers_rat a
  rw [Int.cast_smul_eq_zsmul]
  exact G.zsmul_mem hx m

/-- **Cassels' sublattices are the lattices here** (App. A, §2, p. 362): the additive subgroups of $\mathbb Q^n$ and
the $\mathcal O_{\mathbb Q}$-submodules of $\mathbb Q^n$ are the same subsets, as ordered sets. -/
@[kb "cassels1978" "App. A, §2, p. 362 (a sublattice is any subgroup Γ of Λ)"]
def addSubgroupOrderIso (n : ℕ) : AddSubgroup (Fin n → ℚ) ≃o Submodule (𝓞 ℚ) (Fin n → ℚ) where
  toFun G := { G with smul_mem' := fun a _ hx => smul_mem_addSubgroup G a hx }
  invFun K := K.toAddSubgroup
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

@[simp] theorem mem_addSubgroupOrderIso {n : ℕ} (G : AddSubgroup (Fin n → ℚ)) (x : Fin n → ℚ) :
    x ∈ addSubgroupOrderIso n G ↔ x ∈ G := Iff.rfl

/-! ### Theorem 2.1 over $\mathbb Q$ -/

/-- Over $\mathbb Q$, a positive definite form is totally positive definite. -/
theorem isTotallyPosDef_rat {n : ℕ} {Q : QuadForm ℚ n} (hQ : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < Q.eval x) :
    IsTotallyPosDef Q := by
  intro x hx σ
  have e : σ (Q.eval x) = ((Q.eval x : ℚ) : ℂ) := by
    rw [← eq_ratCast σ.toRingHom (Q.eval x)]; rfl
  rw [e, ← Complex.ofReal_ratCast]
  exact Complex.zero_lt_real.mpr (by exact_mod_cast hQ x hx)

/-- **Cassels, App. A, Theorem 2.1** (Eichler; the proof is Kneser's, 1954): let $\Lambda$ be a lattice in the positive
definite space $\mathbb Q^n$, $Q$. Then the orthogonal decomposition of $\Lambda$ into indecomposable sublattices is
unique: two orthogonal splittings $S, S'$ of $\Lambda$ into indecomposable sublattices have the same set of summands.
(Existence: `exists_indecomposable_splitting`.)

*Update:* the summands must be non-zero (Cassels' definition of "indecomposable" admits the zero lattice), and
$\Lambda$ need only be finitely generated. -/
@[kb "cassels1978" "App. A, §2, Thm. 2.1, p. 363"]
theorem thm_2_1 {n : ℕ} (Q : QuadForm ℚ n) (hQ : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < Q.eval x)
    (L : Submodule (𝓞 ℚ) (Fin n → ℚ)) (hL : L.FG) {S S' : Finset (Submodule (𝓞 ℚ) (Fin n → ℚ))}
    (hS : IsOrthSplitting Q L S) (hSi : ∀ K ∈ S, IsIndecomposable Q K) (hS' : IsOrthSplitting Q L S')
    (hSi' : ∀ K ∈ S', IsIndecomposable Q K) : S = S' :=
  indecomposable_splitting_unique Q (isTotallyPosDef_rat hQ) L hL hS hSi hS' hSi'

/-! ### The equivalence of indecomposable vectors and the proof of Theorem 2.1 -/

section Proof

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **Equivalent indecomposable vectors** (Cassels, App. A, §2, p. 364): $b_1, b_2 \in J$ (the set of indecomposable
vectors of $L$) are equivalent if there is a sequence $c_1 = b_1, c_2, \dots, c_K = b_2$ in $J$ with
$\phi(c_k, c_{k+1}) \ne 0$ for $1 \le k < K$. -/
@[kb "cassels1978" "App. A, §2, p. 364 (equivalence of indecomposable vectors)"]
def IndecEquiv (L : Submodule (𝓞 F) (Fin n → F)) (b₁ b₂ : Fin n → F) : Prop :=
  IsIrr Q L b₁ ∧ Relation.ReflTransGen (IrrRel Q L) b₁ b₂

variable {Q}

theorem irrRel_symm {L : Submodule (𝓞 F) (Fin n → F)} {y z : Fin n → F} (h : IrrRel Q L y z) : IrrRel Q L z y :=
  ⟨h.2.1, h.1, by rw [bil_comm]; exact h.2.2⟩

/-- **"This is an equivalence relation"** (Cassels, App. A, §2, p. 364): `IndecEquiv` is reflexive on $J$,
symmetric and transitive. -/
@[kb "cassels1978" "App. A, §2, p. 364 (this is an equivalence relation)"]
theorem indecEquiv_equivalence (L : Submodule (𝓞 F) (Fin n → F)) :
    (∀ b, IsIrr Q L b → IndecEquiv Q L b b) ∧
      (∀ b₁ b₂, IndecEquiv Q L b₁ b₂ → IndecEquiv Q L b₂ b₁) ∧
      (∀ b₁ b₂ b₃, IndecEquiv Q L b₁ b₂ → IndecEquiv Q L b₂ b₃ → IndecEquiv Q L b₁ b₃) := by
  refine ⟨fun b hb => ⟨hb, Relation.ReflTransGen.refl⟩, fun b₁ b₂ h => ?_, fun b₁ b₂ b₃ h h' => ⟨h.1, h.2.trans h'.2⟩⟩
  refine ⟨irr_of_rtg h.1 h.2, ?_⟩
  have hsymm : ∀ {x y}, Relation.ReflTransGen (IrrRel Q L) x y → Relation.ReflTransGen (IrrRel Q L) y x := by
    intro x y h
    induction h with
    | refl => exact .refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (irrRel_symm hbc) ih
  exact hsymm h.2

/-- **An indecomposable vector lies in precisely one summand** (Cassels, App. A, §2, p. 363: "if $b$ is irreducible,
it must belong to precisely one of the $\Gamma_j$"), $V$ totally positive definite. -/
@[kb "cassels1978" "App. A, §2, proof of Thm. 2.1, p. 363 (an indecomposable b lies in precisely one Γ_j)"]
theorem existsUnique_mem_of_irr (hQ : IsTotallyPosDef Q) {L : Submodule (𝓞 F) (Fin n → F)}
    {S : Finset (Submodule (𝓞 F) (Fin n → F))} (hS : IsOrthSplitting Q L S) {b : Fin n → F} (hb : IsIrr Q L b) :
    ∃! K, K ∈ S ∧ b ∈ K := by
  obtain ⟨K, hK, hbK⟩ := exists_mem_of_irr hS hb
  refine ⟨K, ⟨hK, hbK⟩, fun K' ⟨hK', hbK'⟩ => ?_⟩
  by_contra hne
  have h0 := hS.orth K' hK' K hK hne b hbK' b hbK
  have := trForm_self_pos hQ hb.2.1
  rw [trForm_apply, h0] at this
  simp at this

/-- **The summands are generated by the classes** (Cassels, App. A, §2, p. 364): for an orthogonal splitting $S$ of a
finitely generated $L$ into indecomposable sublattices ($V$ totally positive definite), the summands are exactly the
sublattices $\Lambda_r$ generated by the equivalence classes of indecomposable vectors. -/
@[kb "cassels1978" "App. A, §2, proof of Thm. 2.1, p. 364 (Λ is the orthogonal sum of the Λ_r; the Γ_j are the Λ_r)"]
theorem mem_splitting_iff_class (hQ : IsTotallyPosDef Q) {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.FG)
    {S : Finset (Submodule (𝓞 F) (Fin n → F))} (hS : IsOrthSplitting Q L S) (hSi : ∀ K ∈ S, IsIndecomposable Q K)
    (K : Submodule (𝓞 F) (Fin n → F)) :
    K ∈ S ↔ ∃ b, IsIrr Q L b ∧ K = Submodule.span (𝓞 F) {c | IndecEquiv Q L b c} := by
  have hcl : ∀ b, IsIrr Q L b → {c | IndecEquiv Q L b c} = {c | Relation.ReflTransGen (IrrRel Q L) b c} :=
    fun b hb => Set.ext fun c => ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩
  constructor
  · intro hK
    obtain ⟨b, hb, hbK⟩ := exists_irr_mem hQ hL hS hK
    exact ⟨b, hb, by rw [hcl b hb]; exact eq_span_class hQ hL hS hSi hK hbK hb⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨K, hK, hbK⟩ := exists_mem_of_irr hS hb
    rw [hcl b hb, ← eq_span_class hQ hL hS hSi hK hbK hb]
    exact hK

end Proof

/-! ### The indefinite example $x_0^2 - 2x_1^2$ -/

section Example

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

/-- A lattice $\mathcal O_F v$ spanned by one non-zero vector is indecomposable (for any form). -/
theorem isIndecomposable_span_singleton (Q : QuadForm F n) {v : Fin n → F} (hv : v ≠ 0) :
    IsIndecomposable Q (Submodule.span (𝓞 F) {v}) := by
  refine ⟨by simpa using hv, ?_⟩
  rintro ⟨K₁, K₂, h1, h2, -, hd, hsup⟩
  obtain ⟨x, hx1, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h1
  obtain ⟨y, hy2, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h2
  have hxv : x ∈ Submodule.span (𝓞 F) {v} := hsup ▸ Submodule.mem_sup_left hx1
  have hyv : y ∈ Submodule.span (𝓞 F) {v} := hsup ▸ Submodule.mem_sup_right hy2
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxv
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hyv
  have ha : a ≠ 0 := by rintro rfl; simp at hx0
  have hb : b ≠ 0 := by rintro rfl; simp at hy0
  have h1' : b • a • v ∈ K₁ := K₁.smul_mem b hx1
  have h2' : b • a • v ∈ K₂ := by rw [smul_comm]; exact K₂.smul_mem a hy2
  have h0 := (Submodule.disjoint_def.mp hd) _ h1' h2'
  rw [smul_smul] at h0
  have hab : algebraMap (𝓞 F) F (b * a) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)]
    exact mul_ne_zero hb ha
  have : algebraMap (𝓞 F) F (b * a) • v = 0 := by rw [algebraMap_smul]; exact h0
  exact hv ((smul_eq_zero.mp this).resolve_left hab)

/-- The form $x_0^2 - 2x_1^2$ over $\mathbb Q$ (Cassels, App. A, §2, p. 363; his $x_1^2 - 2x_2^2$). -/
def indefEx : QuadForm ℚ 2 := QuadForm.diag ![1, -2]

/-- The automorph $T = \begin{pmatrix} 3 & 4 \\ 2 & 3 \end{pmatrix}$ of $x_0^2 - 2x_1^2$ maps the basis vectors to
$Te_0 = (3, 2)$ and $Te_1 = (4, 3)$. -/
def indefExT0 : Fin 2 → ℚ := ![3, 2]

/-- $Te_1 = (4, 3)$. -/
def indefExT1 : Fin 2 → ℚ := ![4, 3]

private theorem bil_indefEx (x y : Fin 2 → ℚ) : bil indefEx x y = 2 * (x 0 * y 0) - 4 * (x 1 * y 1) := by
  simp [bil, indefEx, QuadForm.hessian, QuadForm.diag, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.diagonal]
  ring

private theorem latOrth_span_pair {u w : Fin 2 → ℚ} (h : bil indefEx u w = 0) :
    LatOrth indefEx (Submodule.span (𝓞 ℚ) {u}) (Submodule.span (𝓞 ℚ) {w}) := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [← algebraMap_smul ℚ a u, ← algebraMap_smul ℚ b w, bil_smul_left, bil_smul_right, h, mul_zero, mul_zero]

private theorem disjoint_span_pair {u w : Fin 2 → ℚ} (h : u 0 * w 1 - u 1 * w 0 ≠ 0) :
    Disjoint (Submodule.span (𝓞 ℚ) {u}) (Submodule.span (𝓞 ℚ) {w}) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hy
  have e0 := congrFun hb 0
  have e1 := congrFun hb 1
  rw [← algebraMap_smul ℚ a u, ← algebraMap_smul ℚ b w] at e0 e1
  simp only [Pi.smul_apply, smul_eq_mul] at e0 e1
  have ha : (a : ℚ) * (u 0 * w 1 - u 1 * w 0) = 0 := by linear_combination (-w 1) * e0 + w 0 * e1
  have ha' : algebraMap (𝓞 ℚ) ℚ a = 0 := (mul_eq_zero.mp ha).resolve_right h
  rw [← algebraMap_smul ℚ a u, ha', zero_smul]

private theorem splitting_pair {u w : Fin 2 → ℚ} (hu : u ≠ 0) (hw : w ≠ 0) (horth : bil indefEx u w = 0)
    (hdet : u 0 * w 1 - u 1 * w 0 ≠ 0) :
    IsOrthSplitting indefEx (Submodule.span (𝓞 ℚ) {u} ⊔ Submodule.span (𝓞 ℚ) {w})
      ({Submodule.span (𝓞 ℚ) {u}} ∪ {Submodule.span (𝓞 ℚ) {w}}) :=
  splitting_union (latOrth_span_pair horth) (disjoint_span_pair hdet)
    (splitting_single (by simpa using hu)) (splitting_single (by simpa using hw))

/-- **Non-uniqueness for indefinite forms** (Cassels, App. A, §2, p. 363): for $\Lambda = \mathbb Z^2$ with the form
$x_0^2 - 2x_1^2$, both $\{\mathbb Ze_0, \mathbb Ze_1\}$ and $\{\mathbb ZTe_0, \mathbb ZTe_1\}$ (with the automorph
$T = \begin{pmatrix} 3 & 4 \\ 2 & 3 \end{pmatrix}$, $Te_0 = (3, 2)$, $Te_1 = (4, 3)$) are orthogonal splittings of
$\Lambda$ into indecomposable sublattices, and they are different. So Theorem 2.1 fails without definiteness. -/
@[kb "cassels1978" "App. A, §2, p. 363 (example x₁² − 2x₂²: Γ₁ ⊥ Γ₂ and TΓ₁ ⊥ TΓ₂)"]
theorem indefinite_not_unique :
    ∃ S S' : Finset (Submodule (𝓞 ℚ) (Fin 2 → ℚ)),
      IsOrthSplitting indefEx (Submodule.span (𝓞 ℚ) {Pi.single 0 1, Pi.single 1 1}) S ∧
      (∀ K ∈ S, IsIndecomposable indefEx K) ∧
      IsOrthSplitting indefEx (Submodule.span (𝓞 ℚ) {Pi.single 0 1, Pi.single 1 1}) S' ∧
      (∀ K ∈ S', IsIndecomposable indefEx K) ∧ S ≠ S' := by
  set e₀ : Fin 2 → ℚ := Pi.single 0 1
  set e₁ : Fin 2 → ℚ := Pi.single 1 1
  have he₀ : e₀ = ![1, 0] := by ext i; fin_cases i <;> simp [e₀]
  have he₁ : e₁ = ![0, 1] := by ext i; fin_cases i <;> simp [e₁]
  have hL : Submodule.span (𝓞 ℚ) {e₀, e₁} = Submodule.span (𝓞 ℚ) {e₀} ⊔ Submodule.span (𝓞 ℚ) {e₁} := by
    rw [Set.insert_eq, Submodule.span_union]
  have hT0 : indefExT0 = (3 : ℤ) • e₀ + (2 : ℤ) • e₁ := by
    rw [he₀, he₁]; ext i; fin_cases i <;> simp [indefExT0]
  have hT1 : indefExT1 = (4 : ℤ) • e₀ + (3 : ℤ) • e₁ := by
    rw [he₀, he₁]; ext i; fin_cases i <;> simp [indefExT1]
  have hE0 : e₀ = (3 : ℤ) • indefExT0 - (2 : ℤ) • indefExT1 := by
    rw [he₀]; ext i; fin_cases i <;> simp [indefExT0, indefExT1] <;> norm_num
  have hE1 : e₁ = (3 : ℤ) • indefExT1 - (4 : ℤ) • indefExT0 := by
    rw [he₁]; ext i; fin_cases i <;> simp [indefExT0, indefExT1] <;> norm_num
  have hL' : Submodule.span (𝓞 ℚ) {e₀, e₁} =
      Submodule.span (𝓞 ℚ) {indefExT0} ⊔ Submodule.span (𝓞 ℚ) {indefExT1} := by
    rw [← Submodule.span_union, ← Set.insert_eq]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x (rfl | rfl)
      · rw [hE0]
        exact sub_mem (zsmul_mem (Submodule.subset_span (by simp)) _)
          (zsmul_mem (Submodule.subset_span (by simp)) _)
      · rw [hE1]
        exact sub_mem (zsmul_mem (Submodule.subset_span (by simp)) _)
          (zsmul_mem (Submodule.subset_span (by simp)) _)
    · rw [Submodule.span_le]
      rintro x (rfl | rfl)
      · rw [hT0]
        exact add_mem (zsmul_mem (Submodule.subset_span (by simp)) _)
          (zsmul_mem (Submodule.subset_span (by simp)) _)
      · rw [hT1]
        exact add_mem (zsmul_mem (Submodule.subset_span (by simp)) _)
          (zsmul_mem (Submodule.subset_span (by simp)) _)
  have ne₀ : e₀ ≠ 0 := by rw [he₀]; intro h; simpa using congrFun h 0
  have ne₁ : e₁ ≠ 0 := by rw [he₁]; intro h; simpa using congrFun h 1
  have nT0 : indefExT0 ≠ 0 := by intro h; simpa [indefExT0] using congrFun h 0
  have nT1 : indefExT1 ≠ 0 := by intro h; simpa [indefExT1] using congrFun h 0
  refine ⟨{Submodule.span (𝓞 ℚ) {e₀}} ∪ {Submodule.span (𝓞 ℚ) {e₁}},
    {Submodule.span (𝓞 ℚ) {indefExT0}} ∪ {Submodule.span (𝓞 ℚ) {indefExT1}}, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL]
    exact splitting_pair ne₀ ne₁ (by rw [bil_indefEx, he₀, he₁]; simp) (by rw [he₀, he₁]; simp)
  · intro K hK
    rcases Finset.mem_union.mp hK with h | h <;> rw [Finset.mem_singleton.mp h]
    exacts [isIndecomposable_span_singleton _ ne₀, isIndecomposable_span_singleton _ ne₁]
  · rw [hL']
    exact splitting_pair nT0 nT1 (by rw [bil_indefEx]; simp [indefExT0, indefExT1]; norm_num)
      (by simp [indefExT0, indefExT1]; norm_num)
  · intro K hK
    rcases Finset.mem_union.mp hK with h | h <;> rw [Finset.mem_singleton.mp h]
    exacts [isIndecomposable_span_singleton _ nT0, isIndecomposable_span_singleton _ nT1]
  · intro hSS
    have hmem : Submodule.span (𝓞 ℚ) {e₀} ∈
        ({Submodule.span (𝓞 ℚ) {indefExT0}} ∪ {Submodule.span (𝓞 ℚ) {indefExT1}} :
          Finset (Submodule (𝓞 ℚ) (Fin 2 → ℚ))) := by
      rw [← hSS]; simp
    -- `e₀` would be an integer multiple of `(3, 2)` or of `(4, 3)`: impossible in the second coordinate
    have key : ∀ t : Fin 2 → ℚ, t 1 ≠ 0 → Submodule.span (𝓞 ℚ) {e₀} ≠ Submodule.span (𝓞 ℚ) {t} := by
      intro t ht h
      have : t ∈ Submodule.span (𝓞 ℚ) {e₀} := h ▸ Submodule.mem_span_singleton_self t
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp this
      have := congrFun ha 1
      rw [← algebraMap_smul ℚ a e₀, he₀] at this
      simp at this
      exact ht this.symm
    rcases Finset.mem_union.mp hmem with h | h
    · exact key _ (by simp [indefExT0]) (Finset.mem_singleton.mp h)
    · exact key _ (by simp [indefExT1]) (Finset.mem_singleton.mp h)

end Example

end QuadFormsKB.Lattices
