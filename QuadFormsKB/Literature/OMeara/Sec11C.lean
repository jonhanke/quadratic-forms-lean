/-
# O'Meara §11G: normed spaces over complete fields (11:17)

**Setting.** $K$ is a complete non-trivially normed field (a Mathlib `NontriviallyNormedField` with `CompleteSpace`),
$V$ a finite-dimensional $K$-vector space. A *norm* on $V$ in O'Meara's sense (§11G, p. 12) is a Mathlib `Seminorm K V`
$\lVert\ \rVert$ that is definite ($\lVert x\rVert = 0 \Rightarrow x = 0$); its topology is that of
`Seminorm.toSeminormedAddCommGroup`.

**Proves** `norms_equivalent` (**11:17**): any two norms on $V$ induce the same topology, and $V$ is complete under a norm.

**Special case.** O'Meara allows the complete valuation of $K$ to be trivial; we assume it non-trivial (Mathlib's
`NontriviallyNormedField`), the case of interest. For the trivial valuation every norm gives the discrete topology.
The proof uses Mathlib's `LinearMap.continuous_of_finiteDimensional` and `FiniteDimensional.complete` instead of
O'Meara's induction on the dimension.
-/
import QuadFormsKB.Citation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Seminorm.Basic

namespace QuadFormsKB.OMeara

variable {K : Type*} [NontriviallyNormedField K] {V : Type*} [AddCommGroup V] [Module K V]

/-- Type synonym for $V$ carrying the norm $p$ as a Mathlib `NormedAddCommGroup`/`NormedSpace` structure (used to apply
Mathlib's finite-dimensional theory to two different norms on the same space). -/
def NormedBy (_p : Seminorm K V) (_hp : ∀ x, _p x = 0 → x = 0) : Type _ := V

namespace NormedBy
variable (p : Seminorm K V) (hp : ∀ x, p x = 0 → x = 0)

noncomputable instance : SeminormedAddCommGroup (NormedBy p hp) := p.toSeminormedAddCommGroup
noncomputable instance : NormedAddCommGroup (NormedBy p hp) :=
  NormedAddCommGroup.ofSeparation (E := NormedBy p hp) hp
instance : Module K (NormedBy p hp) := (inferInstance : Module K V)
noncomputable instance : NormedSpace K (NormedBy p hp) :=
  { (inferInstance : Module K (NormedBy p hp)) with
    norm_smul_le := fun a x => (map_smul_eq_mul p a x).le }
end NormedBy

/-- The identity of $V$ as a linear map between two normings. -/
def NormedBy.idLM (p : Seminorm K V) (hp : ∀ x, p x = 0 → x = 0) (q : Seminorm K V)
    (hq : ∀ x, q x = 0 → x = 0) : NormedBy p hp →ₗ[K] NormedBy q hq where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **11:17.** Let $K$ be a complete non-trivially normed field and $V$ a finite-dimensional $K$-vector space. Any two
norms $p$, $q$ on $V$ (definite `Seminorm K V`s) induce the same topology on $V$, and $V$ is complete under the
norm $p$ (hence under any norm). -/
@[kb "omeara1963" "§11G, 11:17, p. 12"]
theorem norms_equivalent [CompleteSpace K] [FiniteDimensional K V] (p q : Seminorm K V)
    (hp : ∀ x, p x = 0 → x = 0) (hq : ∀ x, q x = 0 → x = 0) :
    p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace =
      q.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace ∧
    @CompleteSpace V p.toSeminormedAddCommGroup.toUniformSpace := by
  have : FiniteDimensional K (NormedBy p hp) := inferInstanceAs (FiniteDimensional K V)
  have : FiniteDimensional K (NormedBy q hq) := inferInstanceAs (FiniteDimensional K V)
  refine ⟨?_, ?_⟩
  · have h1 := (NormedBy.idLM p hp q hq).continuous_of_finiteDimensional
    have h2 := (NormedBy.idLM q hq p hp).continuous_of_finiteDimensional
    let tp := p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace
    let tq := q.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace
    have h1' : @Continuous V V tp tq id := h1
    have h2' : @Continuous V V tq tp id := h2
    exact le_antisymm (@continuous_id_iff_le V tp tq |>.1 h1') (@continuous_id_iff_le V tq tp |>.1 h2')
  · have : CompleteSpace (NormedBy p hp) := FiniteDimensional.complete K _
    exact this

end QuadFormsKB.OMeara
