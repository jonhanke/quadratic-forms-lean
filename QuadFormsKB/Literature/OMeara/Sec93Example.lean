/-
# O'Meara §93C: the general cancellation law fails over dyadic fields (remark after 93:14a)

**Setting** (as in `Sec82.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$, quadratic
spaces $(V, Q)$, $(V', Q')$ over $F$, lattices = `Submodule R V`.

**Proves** (O'Meara 1963, §93C, p. 258: "The general cancellation law for lattices on quadratic spaces over non-dyadic
fields (Theorem 92:3) does not extend to the dyadic case")
* `isometricLat_hyp_one`: $\langle A(0,0)\rangle \perp \langle 1 \rangle \cong \langle A(1,0)\rangle \perp \langle 1 \rangle$
  (bases $x, y, e$ and $x + e, y, e - y$);
* `not_isometricLat_hyp`: if $2$ is not a unit (the dyadic case), $\langle A(0,0)\rangle \not\cong \langle A(1,0)\rangle$,
  since their norms $2\mathfrak o$ and $\mathfrak o$ differ.
-/
import QuadFormsKB.Literature.OMeara.Sec91Chain

open QuadraticMap Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Field

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- **Isometric lattices have the same norm.** -/
theorem IsometricLat.normIdeal_eq {L : Submodule R V} {K : Submodule R V'} (h : IsometricLat Q Q' L K) :
    normIdeal Q' K = normIdeal Q L := by
  obtain ⟨f, hf⟩ := h
  rw [normIdeal, normIdeal]
  congr 1
  ext c
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, (f.symm ⟨y, hy⟩).2, by rw [← hf]; simp⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, (f ⟨x, hx⟩).2, hf ⟨x, hx⟩⟩

end Field

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- The matrix $A(\alpha, 0) \perp \langle 1 \rangle$, as a $3 \times 3$ matrix. -/
def matA1 (α : F) : Matrix (Fin 3) (Fin 3) F := !![α, 1, 0; 1, 0, 0; 0, 0, 1]

/-- **$\langle A(0,0)\rangle \perp \langle 1\rangle \cong \langle A(1,0)\rangle \perp \langle 1\rangle$** (O'Meara 1963,
§93C, p. 258, by 93:13): a lattice with a base of matrix $A(0,0) \perp \langle 1 \rangle$ is isometric to a lattice with a
base of matrix $A(1,0) \perp \langle 1 \rangle$. -/
@[kb "omeara1963" "§93C, p. 258 (⟨A(0,0)⟩ ⊥ ⟨1⟩ ≅ ⟨A(1,0)⟩ ⊥ ⟨1⟩)"]
theorem isometricLat_hyp_one {L : Submodule R V} {K : Submodule R V'} (b : Basis (Fin 3) R L)
    (hb : gram Q (fun i => (b i : V)) = matA1 0) (b' : Basis (Fin 3) R K)
    (hb' : gram Q' (fun i => (b' i : V')) = matA1 1) : IsometricLat Q Q' L K := by
  let M : Matrix (Fin 3) (Fin 3) R := !![1, 0, 0; 0, 1, -1; 1, 0, 1]
  have hM : IsUnit M.det := by simp [M, Matrix.det_fin_three]
  let e : L ≃ₗ[R] L := Matrix.toLinearEquiv b M hM
  have hg : ∀ i j, bil Q (b i : V) (b j : V) = matA1 0 i j := fun i j => by rw [← hb]; rfl
  have h0 : ((b.map e) 0 : V) = (b 0 : V) + (b 2 : V) := by
    simp [e, M, Matrix.toLinearEquiv_apply, Matrix.toLin_self, Fin.sum_univ_three]
  have h1 : ((b.map e) 1 : V) = (b 1 : V) := by
    simp [e, M, Matrix.toLinearEquiv_apply, Matrix.toLin_self, Fin.sum_univ_three]
  have h2 : ((b.map e) 2 : V) = (b 2 : V) - (b 1 : V) := by
    simp [e, M, Matrix.toLinearEquiv_apply, Matrix.toLin_self, Fin.sum_univ_three, sub_eq_add_neg, add_comm]
  refine isometricLat_of_gram_eq Q Q' (b.map e) b' ?_
  rw [hb']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [gram, Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, h0, h1, h2, bil_add_left,
      bil_add_right, bil_sub_left, bil_sub_right, hg] <;>
    simp [matA1]

/-- **$\langle A(0,0)\rangle \not\cong \langle A(1,0)\rangle$ over a dyadic field** (O'Meara 1963, §93C, p. 258): if $2$
is not a unit of $R$, a binary lattice with matrix $A(0,0)$ is not isometric to one with matrix $A(1,0)$, since
$\mathfrak nA(0,0) = 2\mathfrak o \ne \mathfrak o = \mathfrak nA(1,0)$. -/
@[kb "omeara1963" "§93C, p. 258 (A(0,0) and A(1,0) are not isometric)"]
theorem not_isometricLat_hyp (h2 : ¬ IsUnit (2 : R)) {L : Submodule R V} {K : Submodule R V'}
    (b : Basis (Fin 2) R L) (hb : gram Q (fun i => (b i : V)) = !![0, 1; 1, 0])
    (b' : Basis (Fin 2) R K) (hb' : gram Q' (fun i => (b' i : V')) = !![1, 1; 1, 0]) :
    ¬ IsometricLat Q Q' L K := by
  intro h
  have hn := h.normIdeal_eq Q Q'
  -- `1 ∈ n K`
  have h1 : (1 : F) ∈ normIdeal Q' K := by
    have : Q' (b' 0 : V') = 1 := by
      rw [← bil_self]; simpa [gram] using congrFun (congrFun hb' 0) 0
    rw [← this]; exact Q_mem_normIdeal Q' (b' 0).2
  -- `n L ⊆ 2 o`
  have hg : ∀ i j, bil Q (b i : V) (b j : V) = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j :=
    fun i j => by rw [← hb]; rfl
  have h2 : normIdeal Q L ≤ R ∙ (2 : F) := by
    rw [normIdeal, span_le]
    rintro _ ⟨v, hv, rfl⟩
    have hvb : v = ∑ i, b.repr ⟨v, hv⟩ i • (b i : V) := by
      have := congrArg Subtype.val (b.sum_repr ⟨v, hv⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [SetLike.mem_coe, hvb, Q_sum_R]
    simp only [Fin.sum_univ_two, hg]
    refine mem_span_singleton.mpr ⟨b.repr ⟨v, hv⟩ 0 * b.repr ⟨v, hv⟩ 1, ?_⟩
    simp [Algebra.smul_def]; ring
  rw [hn] at h1
  obtain ⟨r, hr⟩ := mem_span_singleton.mp (h2 h1)
  apply ‹¬ IsUnit (2 : R)›
  refine IsUnit.of_mul_eq_one r ((IsFractionRing.injective R F) ?_)
  rw [map_mul, map_one, map_ofNat, mul_comm, ← hr, Algebra.smul_def]

end Domain

end QuadFormsKB.OMeara
