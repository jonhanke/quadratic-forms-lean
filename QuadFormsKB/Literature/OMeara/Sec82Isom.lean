/-
# O'Meara §82: isometries of lattices, discriminants, classes

**Setting** (as in `Sec82.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$, quadratic
spaces $(V, Q)$, $(V', Q')$ over $F$, O'Meara's bilinear form $B$ = `bil Q`, lattices = `Submodule R V`.

**Proves**
* `Q_sum`: $Q(\sum_i c_i v_i) = \sum_{i,j} c_ic_jB(v_i, v_j)$;
* `bil_eq_of_isometricLat`: an isometry of lattices preserves $B$;
* `isometricLat_of_gram_eq` (O'Meara 1963, 82:1, p. 222): lattices with bases having the same matrix are
  isometric;
* `exists_unit_det_gram` (§82B, p. 222): a change of base multiplies the discriminant by the square of a unit, so
  $dL$ is well defined in $F/\mathfrak u^2$;
* `IsometricLat.sameDisc`: isometric lattices have the same discriminant (`SameDisc`, $dL = dK$ in
  $F/\mathfrak u^2$);
* `mem_cls_of_isometricLat` (§82C, p. 222): isometric lattices on the same space $V$ are in the same class.
-/
import QuadFormsKB.Literature.OMeara.Sec91Type

open QuadraticMap Submodule Module
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Field

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- $Q(\sum_i c_i v_i) = \sum_{i,j} c_ic_jB(v_i, v_j)$. -/
theorem Q_sum {ι : Type*} [Fintype ι] (c : ι → F) (v : ι → V) :
    Q (∑ i, c i • v i) = ∑ i, ∑ j, c i * c j * bil Q (v i) (v j) := by
  rw [← bil_self, bil_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bil_smul_left, bil_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bil_smul_right]; ring

/-- $Q(\sum_i c_i v_i)$ for coefficients $c_i \in R$. -/
theorem Q_sum_R {ι : Type*} [Fintype ι] (c : ι → R) (v : ι → V) :
    Q (∑ i, c i • v i) = ∑ i, ∑ j, algebraMap R F (c i) * algebraMap R F (c j) * bil Q (v i) (v j) := by
  have : (∑ i, c i • v i) = ∑ i, algebraMap R F (c i) • v i := by
    simp only [algebraMap_smul]
  rw [this, Q_sum]

/-- $B(x, y) = \tfrac12(Q(x+y) - Q(x) - Q(y))$. -/
theorem bil_eq_half (x y : V) : bil Q x y = (Q (x + y) - Q x - Q y) / 2 := by
  rw [Q_add]
  have : (2 : F) ≠ 0 := two_ne_zero' F
  field_simp
  ring

/-- **An isometry of lattices preserves $B$.** -/
theorem bil_eq_of_isometricLat {L : Submodule R V} {K : Submodule R V'} (f : L ≃ₗ[R] K)
    (hf : ∀ x : L, Q' (f x : V') = Q (x : V)) (x y : L) :
    bil Q' (f x : V') (f y : V') = bil Q (x : V) (y : V) := by
  rw [bil_eq_half, bil_eq_half, ← hf x, ← hf y]
  have : Q ((x : V) + y) = Q' ((f x : V') + f y) := by
    rw [← Submodule.coe_add, ← hf (x + y), map_add, Submodule.coe_add]
  rw [this]

/-- **Lattices with the same matrix are isometric** (O'Meara 1963, 82:1 (2), p. 222): if bases $b$ of $L$ and $b'$ of
$K$ have the same matrix $(B(b_i, b_j)) = (B'(b'_i, b'_j))$, then $L \cong K$. -/
@[kb "omeara1963" "§82B, 82:1, p. 222"]
theorem isometricLat_of_gram_eq {L : Submodule R V} {K : Submodule R V'} {ι : Type*} [Fintype ι]
    (b : Basis ι R L) (b' : Basis ι R K)
    (h : gram Q (fun i => (b i : V)) = gram Q' (fun i => (b' i : V'))) : IsometricLat Q Q' L K := by
  refine ⟨b.equiv b' (Equiv.refl ι), fun x => ?_⟩
  have hx : (x : V) = ∑ i, b.repr x i • (b i : V) := by
    have := congrArg Subtype.val (b.sum_repr x)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hfx : ((b.equiv b' (Equiv.refl ι)) x : V') = ∑ i, b.repr x i • (b' i : V') := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    simp only [map_smul, Basis.equiv_apply, Equiv.refl_apply, Submodule.coe_sum, Submodule.coe_smul]
  rw [hfx, hx, Q_sum_R, Q_sum_R]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := congrFun (congrFun h i) j
  simp only [gram, Matrix.of_apply] at this
  rw [this]

end Field

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- **Change of base** (O'Meara 1963, §82B, p. 222): for two bases $b$, $b'$ of $L$,
$d(b') = \varepsilon^2 d(b)$ with $\varepsilon$ a unit of $R$. -/
@[kb "omeara1963" "§82B, p. 222 (d(x'₁,…,x'_n) = ε² d(x₁,…,x_n))"]
theorem exists_unit_det_gram {L : Submodule R V} {ι : Type*} [Fintype ι] [DecidableEq ι] (b b' : Basis ι R L) :
    ∃ ε : R, IsUnit ε ∧
      (gram Q fun i => (b' i : V)).det = algebraMap R F ε ^ 2 * (gram Q fun i => (b i : V)).det := by
  let T : Matrix ι ι R := (b.toMatrix b')ᵀ
  have hb' : (fun i => (b' i : V)) = fun i => ∑ j, T i j • (b j : V) := by
    funext i
    have := congrArg Subtype.val (b.sum_repr (b' i))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    rw [← this]
    simp [T, Basis.toMatrix_apply]
  refine ⟨T.det, ?_, ?_⟩
  · have h := b.toMatrix_mul_toMatrix_flip b'
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_one] at this
    simp only [T, Matrix.det_transpose]
    exact IsUnit.of_mul_eq_one _ this
  · rw [hb', gram_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      show (T.map (algebraMap R F)).det = algebraMap R F T.det from (RingHom.map_det _ _).symm]
    ring

/-- **$dL = dK$** (O'Meara 1963, §82B, p. 222): the discriminants of $L$ and $K$ agree in $F/\mathfrak u^2$, i.e.
there are bases $b$ of $L$ and $b'$ of $K$ and a unit $\varepsilon$ with $d(b) = \varepsilon^2 d(b')$. -/
@[kb "omeara1963" "§82B, p. 222 (dL = dK in F/u²)"]
def SameDisc (L : Submodule R V) (K : Submodule R V') : Prop :=
  ∃ b : Basis (Fin (finrank R L)) R L, ∃ b' : Basis (Fin (finrank R K)) R K, ∃ ε : R, IsUnit ε ∧
    (gram Q fun i => (b i : V)).det = algebraMap R F ε ^ 2 * (gram Q' fun i => (b' i : V')).det

/-- `SameDisc` does not depend on the bases: if $dL = dK$ then for all bases $b$, $b'$ the discriminants differ by
the square of a unit. -/
theorem SameDisc.forall {L : Submodule R V} {K : Submodule R V'} (h : SameDisc Q Q' L K)
    (b : Basis (Fin (finrank R L)) R L) (b' : Basis (Fin (finrank R K)) R K) : ∃ ε : R, IsUnit ε ∧
    (gram Q fun i => (b i : V)).det = algebraMap R F ε ^ 2 * (gram Q' fun i => (b' i : V')).det := by
  obtain ⟨c, c', ε, hε, hd⟩ := h
  obtain ⟨u, hu, hu'⟩ := exists_unit_det_gram Q c b
  obtain ⟨v, hv, hv'⟩ := exists_unit_det_gram Q' b' c'
  refine ⟨u * ε * v, hu.mul hε |>.mul hv, ?_⟩
  rw [hu', hd, hv']
  simp only [map_mul]; ring

/-- **Isometric lattices have the same discriminant** (O'Meara 1963, §82B, p. 222). -/
theorem IsometricLat.sameDisc {L : Submodule R V} {K : Submodule R V'} (h : IsometricLat Q Q' L K)
    (hL : L.FG) [IsDiscreteValuationRing R] : SameDisc Q Q' L K := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨b⟩ := exists_basis (R := R) (F := F) hL
  have hrk : finrank R L = finrank R K := f.finrank_eq
  let b' : Basis (Fin (finrank R K)) R K := (b.map f).reindex (finCongr hrk)
  refine ⟨b, b', 1, isUnit_one, ?_⟩
  have : (gram Q' fun i => (b' i : V')) = (gram Q fun i => (b i : V)).submatrix (finCongr hrk).symm
      (finCongr hrk).symm := by
    ext i j
    simp only [gram, Matrix.of_apply, Matrix.submatrix_apply, b', Basis.reindex_apply, Basis.map_apply]
    exact bil_eq_of_isometricLat Q Q' f hf _ _
  rw [this, Matrix.det_submatrix_equiv_self]
  simp

/-- **Isometric lattices on the same space are in the same class** (O'Meara 1963, §82C, p. 222, with §82A): if $L$
and $K$ are lattices on $V$ and $L \cong K$, then $K = \sigma L$ for some $\sigma \in O(V)$ (extend the isometry
$L \to K$ linearly from a base of $L$, which is a base of $V$). -/
@[kb "omeara1963" "§82C, p. 222 (K ≅ L on V gives K ∈ cls L)"]
theorem mem_cls_of_isometricLat [IsDiscreteValuationRing R] {L K : Submodule R V} [L.IsLattice F]
    [K.IsLattice F] (h : IsometricLat Q Q L K) : K ∈ cls Q L := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨b⟩ := exists_basis (R := R) (F := F) (Submodule.IsLattice.fg (A := F) (M := L))
  let b' := b.map f
  let e := b.extendOfIsLattice F
  let e' := b'.extendOfIsLattice F
  let σ : V ≃ₗ[F] V := e.equiv e' (Equiv.refl _)
  have hσb : ∀ i, σ (b i) = f (b i) := by
    intro i
    have h1 : σ (e i) = e' i := by simp [σ, Basis.equiv_apply]
    simpa [e, e', b'] using h1
  refine ⟨σ, fun v => ?_, ?_⟩
  · have hv : v = ∑ i, e.repr v i • e i := (e.sum_repr v).symm
    have hσv : σ v = ∑ i, e.repr v i • e' i := by
      conv_lhs => rw [hv]
      rw [map_sum]
      simp only [map_smul, σ, Basis.equiv_apply, Equiv.refl_apply]
    rw [hσv]
    conv_rhs => rw [hv]
    rw [Q_sum, Q_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : bil Q (e' i) (e' j) = bil Q (e i) (e j) := by
      simp only [e, e', b', Basis.extendOfIsLattice_apply, Basis.map_apply]
      exact bil_eq_of_isometricLat Q Q f hf _ _
    rw [this]
  · -- `σ L = K`
    have hL : L = span R (Set.range fun i => (b i : V)) := (span_basis_eq b).symm
    have hK : K = span R (Set.range fun i => (b' i : V)) := (span_basis_eq b').symm
    rw [latMap, hL, Submodule.map_span, ← Set.range_comp]
    conv_lhs => rw [hK]
    congr 1
    ext x
    simp only [Set.mem_range, Function.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, by rw [hσb]; simp [b']⟩
    · rintro ⟨i, rfl⟩; exact ⟨i, by rw [hσb]; simp [b']⟩

end Domain

end QuadFormsKB.OMeara
