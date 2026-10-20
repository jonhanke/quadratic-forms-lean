/-
# Maximal orders in $M_2(K)$: the split local case

**Layer:** $R$ an integrally closed domain with fraction field $K$ (for the conjugacy statement: a PID).

At a split place $v$ the local quaternion algebra is $D_v \cong M_2(F_v)$ (`Quat.nonempty_algEquiv_matrix_iff`). This
file shows that $M_2(R)$ is a maximal $R$-order of $M_2(K)$.

**Contents.**
* `mul_self_eq_trace_det`: Cayley–Hamilton for $2\times2$ matrices, $x^2 = \operatorname{tr}(x)x - \det(x)$.
* `isInteger_trace_det`: trace and determinant of an element of an order of $M_2(K)$ lie in $R$.
* `matOrder`: $M_2(R) \subseteq M_2(K)$; `isOrder_matOrder`, `isMaximalOrder_matOrder` (if $\mathcal O \supseteq M_2(R)$ is an order
  and $x \in \mathcal O$, then $\operatorname{tr}(xE_{ij}) = x_{ji} \in R$).

Sources: Voight, *Quaternion Algebras* (2021), Example 10.5.2, Cor. 10.5.5, Lemma 15.5.3.
-/
import QuadFormsKB.Tamagawa.QuatOrder
import Mathlib.Algebra.Module.Lattice

open Polynomial Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open IsLocalization Submodule

/-- **Cayley–Hamilton for $2\times2$ matrices:** $x^2 = \operatorname{tr}(x)\,x - \det(x)\cdot 1$. -/
theorem mul_self_eq_trace_det {K : Type*} [Field K] (x : Matrix (Fin 2) (Fin 2) K) :
    x * x = x.trace • x - algebraMap K (Matrix (Fin 2) (Fin 2) K) x.det := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two,
      Matrix.algebraMap_matrix_apply] <;> ring

section Mat

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The order $M_2(R)$** of $M_2(K)$: the matrices with entries in $R$.

Source: Voight 2021, Example 10.5.2. -/
@[kb "voight2021" "Ex. 10.5.2"]
def matOrder (R K : Type*) [CommRing R] [Field K] [Algebra R K] : Subalgebra R (Matrix (Fin 2) (Fin 2) K) :=
  (AlgHom.mapMatrix (Algebra.ofId R K)).range

theorem mem_matOrder {x : Matrix (Fin 2) (Fin 2) K} : x ∈ matOrder R K ↔ ∀ i j, IsInteger R (x i j) := by
  constructor
  · rintro ⟨y, rfl⟩ i j
    exact ⟨y i j, rfl⟩
  · intro h
    choose y hy using h
    exact ⟨Matrix.of y, by ext i j; simp [hy]⟩

theorem single_mem_matOrder (i j : Fin 2) : Matrix.single i j (1 : K) ∈ matOrder R K := by
  rw [mem_matOrder]
  intro k l
  by_cases h : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := h; exact ⟨1, by simp⟩
  · exact ⟨0, by rw [map_zero, Matrix.single_apply]; simp only [not_and] at h ⊢; split_ifs with h' <;> tauto⟩

/-- **$M_2(R)$ is an order.** -/
@[kb "voight2021" "Ex. 10.5.2"]
theorem isOrder_matOrder : IsOrder R K (matOrder R K) where
  fg := by
    have : Subalgebra.toSubmodule (matOrder R K) =
        Submodule.map (AlgHom.mapMatrix (Algebra.ofId R K)).toLinearMap ⊤ := by
      ext x; simp [matOrder]
    rw [this]
    exact (Module.Finite.fg_top).map _
  span := by
    refine eq_top_iff.2 fun x _ => ?_
    rw [Matrix.matrix_eq_sum_single x]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have : Matrix.single i j (x i j) = x i j • Matrix.single i j (1 : K) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_matOrder i j))

variable [IsIntegrallyClosed R]

/-- **Trace and determinant of elements of an order of $M_2(K)$ are integral** ($R$ integrally closed).

Source: Voight 2021, Cor. 10.3.6 (the reduced trace and norm of $M_2(K)$ are $\operatorname{tr}$ and $\det$). -/
@[kb "voight2021" "Cor. 10.3.6"]
theorem isInteger_trace_det {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)} (hO : IsOrder R K O)
    {x : Matrix (Fin 2) (Fin 2) K} (hx : x ∈ O) : IsInteger R x.trace ∧ IsInteger R x.det := by
  have hint := hO.isIntegral hx
  by_cases hs : ∃ c : K, x = algebraMap K (Matrix (Fin 2) (Fin 2) K) c
  · obtain ⟨c, rfl⟩ := hs
    obtain ⟨r, hr⟩ := isInteger_of_isIntegral_algebraMap (R := R) hint
    refine ⟨⟨2 * r, ?_⟩, ⟨r ^ 2, ?_⟩⟩
    · simp [Matrix.trace_fin_two, Matrix.algebraMap_matrix_apply, hr, map_ofNat]; ring
    · simp [Matrix.det_fin_two, Matrix.algebraMap_matrix_apply, hr]; ring
  · push Not at hs
    exact isInteger_of_quadratic (mul_self_eq_trace_det x) hs hint

/-- **$M_2(R)$ is a maximal order** of $M_2(K)$ ($R$ integrally closed): if $\mathcal O \supseteq M_2(R)$ is an order and
$x \in \mathcal O$, then $x E_{ji} \in \mathcal O$, so $x_{ij} = \operatorname{tr}(xE_{ji}) \in R$.

Source: Voight 2021, Cor. 10.5.5 and Lemma 15.5.3 (via discriminants there). -/
@[kb "voight2021" "Cor. 10.5.5"]
theorem isMaximalOrder_matOrder : IsMaximalOrder R K (matOrder R K) := by
  refine ⟨isOrder_matOrder, fun O hO hle => le_antisymm (fun x hx => ?_) hle⟩
  rw [mem_matOrder]
  intro i j
  have := (isInteger_trace_det hO (O.mul_mem hx (hle (single_mem_matOrder j i)))).1
  rw [Matrix.trace_mul_single] at this
  simpa using this

end Mat

section Conj

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- Column `i` of a matrix, as an $R$-linear map $M_2(K) \to K^2$. -/
def colMap (i : Fin 2) : Matrix (Fin 2) (Fin 2) K →ₗ[R] (Fin 2 → K) where
  toFun o := fun r => o r i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The column lattice** $L(\mathcal O) = \mathcal O R^2 \subseteq K^2$ of an order $\mathcal O \subseteq M_2(K)$: the $R$-span of the
columns of the elements of $\mathcal O$. -/
def colLattice (O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)) : Submodule R (Fin 2 → K) :=
  ⨆ i : Fin 2, (Subalgebra.toSubmodule O).map (colMap i)

theorem col_mem_colLattice {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)} {o : Matrix (Fin 2) (Fin 2) K}
    (ho : o ∈ O) (i : Fin 2) : (fun r => o r i) ∈ colLattice O :=
  (le_iSup (fun i => (Subalgebra.toSubmodule O).map (colMap (R := R) i)) i) ⟨o, ho, rfl⟩

/-- $\mathcal O$ stabilizes its column lattice: $x L(\mathcal O) \subseteq L(\mathcal O)$ for $x \in \mathcal O$. -/
theorem mulVec_mem_colLattice {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)} {x : Matrix (Fin 2) (Fin 2) K}
    (hx : x ∈ O) {v : Fin 2 → K} (hv : v ∈ colLattice O) : x *ᵥ v ∈ colLattice O := by
  refine Submodule.iSup_induction (motive := fun v => x *ᵥ v ∈ colLattice O) _ hv ?_ ?_ ?_
  · rintro i v ⟨o, ho, rfl⟩
    have : x *ᵥ (colMap (R := R) i o) = fun r => (x * o) r i := by
      ext r; simp [colMap, Matrix.mulVec, dotProduct, Matrix.mul_apply]; rfl
    rw [this]; exact col_mem_colLattice (O.mul_mem hx ho) i
  · rw [Matrix.mulVec_zero]; exact zero_mem _
  · intro v w hv hw; rw [Matrix.mulVec_add]; exact add_mem hv hw

/-- The column lattice of an order is a lattice (finitely generated, spanning $K^2$). -/
theorem isLattice_colLattice {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)} (hO : IsOrder R K O) :
    IsLattice K (colLattice O) where
  fg := Submodule.fg_iSup _ fun i => hO.fg.map _
  span_eq_top := by
    refine eq_top_iff.2 fun v _ => ?_
    have hv : v = ∑ i : Fin 2, v i • (fun r => (1 : Matrix (Fin 2) (Fin 2) K) r i) := by
      ext r; simp [Matrix.one_apply]
    rw [hv]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (col_mem_colLattice O.one_mem i))

variable [IsPrincipalIdealRing R]

/-- **Every order of $M_2(K)$ is contained in a conjugate of $M_2(R)$** ($R$ a PID): there are $P, Q \in M_2(K)$ with
$PQ = QP = 1$ and $Q\mathcal OP \subseteq M_2(R)$. ($P$ has as columns an $R$-basis of the column lattice $L(\mathcal O)$, which is
free of rank 2; $\mathcal O \subseteq \operatorname{End}_R(L(\mathcal O)) = PM_2(R)P^{-1}$.)

Source: Voight 2021, Lemma 10.5.4 and Cor. 10.5.5. -/
@[kb "voight2021" "Cor. 10.5.5"]
theorem exists_conj_le_matOrder {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)} (hO : IsOrder R K O) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) K, P * Q = 1 ∧ Q * P = 1 ∧ ∀ x ∈ O, Q * x * P ∈ matOrder R K := by
  classical
  have := isLattice_colLattice hO
  set L := colLattice O
  have hrk : Module.finrank R L = 2 := by
    rw [IsLattice.finrank_of_pi K L]; simp
  let b : Module.Basis (Fin 2) R L := Module.finBasisOfFinrankEq R L hrk
  let bK : Module.Basis (Fin 2) K (Fin 2 → K) := b.extendOfIsLattice K
  let std := Pi.basisFun K (Fin 2)
  refine ⟨std.toMatrix bK, bK.toMatrix std, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, fun x hx => ?_⟩
  rw [mem_matOrder]
  intro i j
  have hcol : (fun l => std.toMatrix bK l j) = (b j : Fin 2 → K) := by
    ext l; simp [std, bK, Module.Basis.toMatrix_apply]
  have hentry : (bK.toMatrix std * x * std.toMatrix bK) i j =
      (bK.toMatrix std *ᵥ (x *ᵥ fun l => std.toMatrix bK l j)) i := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [hentry, hcol]
  have hmem : x *ᵥ (b j : Fin 2 → K) ∈ L := mulVec_mem_colLattice hx (b j).2
  have hrepr : bK.toMatrix std *ᵥ (x *ᵥ (b j : Fin 2 → K)) = bK.repr (x *ᵥ (b j : Fin 2 → K)) := by
    conv_lhs => rw [show x *ᵥ (b j : Fin 2 → K) = std.repr (x *ᵥ (b j : Fin 2 → K)) by ext k; simp only [std, Pi.basisFun_repr]]
    exact Module.Basis.toMatrix_mulVec_repr _ _ _
  rw [hrepr]
  -- the coordinates of an element of `L` in `bK` are those in `b`, hence in `R`
  set w : L := ⟨_, hmem⟩
  have hw : (w : Fin 2 → K) = ∑ k, algebraMap R K (b.repr w k) • bK k := by
    have h := congrArg Subtype.val (b.sum_repr w)
    rw [Submodule.coe_sum] at h
    conv_lhs => rw [← h]
    simp [bK, algebraMap_smul]
  refine ⟨b.repr w i, ?_⟩
  change _ = bK.repr (w : Fin 2 → K) i
  rw [hw, bK.repr_sum_self]

end Conj

section ConjMax

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- Conjugation $x \mapsto PxQ$ by a matrix $P$ with inverse $Q$, as a $K$-algebra automorphism of $M_2(K)$. -/
def conjAlgEquiv (P Q : Matrix (Fin 2) (Fin 2) K) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Matrix (Fin 2) (Fin 2) K ≃ₐ[K] Matrix (Fin 2) (Fin 2) K where
  toFun x := P * x * Q
  invFun x := Q * x * P
  left_inv x := by
    simp only [← mul_assoc, hQP, one_mul]; rw [mul_assoc, hQP, mul_one]
  right_inv x := by
    simp only [← mul_assoc, hPQ, one_mul]; rw [mul_assoc, hPQ, mul_one]
  map_mul' x y := by
    simp only [mul_assoc]; rw [← mul_assoc Q P, hQP, one_mul]
  map_add' x y := by simp [mul_add, add_mul]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, mul_one, Matrix.smul_mul, hPQ]

variable [IsPrincipalIdealRing R] [IsIntegrallyClosed R]

/-- **The maximal orders of $M_2(K)$ are the conjugates of $M_2(R)$** ($R$ a PID): every maximal order $\mathcal O$ is
$P M_2(R) P^{-1}$ for some $P \in GL_2(K)$ (here $\mathcal O = \varphi(M_2(R))$, $\varphi = $ `conjAlgEquiv P Q`), and every such
conjugate is maximal (`IsMaximalOrder.map`, `isMaximalOrder_matOrder`).

Source: Voight 2021, Cor. 10.5.5. -/
@[kb "voight2021" "Cor. 10.5.5"]
theorem exists_eq_conj_matOrder {M : Subalgebra R (Matrix (Fin 2) (Fin 2) K)} (hM : IsMaximalOrder R K M) :
    ∃ (P Q : Matrix (Fin 2) (Fin 2) K) (hPQ : P * Q = 1) (hQP : Q * P = 1),
      M = (matOrder R K).map (((conjAlgEquiv P Q hPQ hQP) : _ →ₐ[K] _).restrictScalars R) := by
  obtain ⟨P, Q, hPQ, hQP, h⟩ := exists_conj_le_matOrder hM.1
  refine ⟨P, Q, hPQ, hQP, ?_⟩
  have hmax := (isMaximalOrder_matOrder (R := R) (K := K)).map (conjAlgEquiv P Q hPQ hQP)
  refine (hM.2 _ hmax.1 fun x hx => ⟨Q * x * P, h x hx, ?_⟩).symm
  change P * (Q * x * P) * Q = x
  simp only [← mul_assoc, hPQ, one_mul]; rw [mul_assoc, hPQ, mul_one]

end ConjMax

end QuadFormsKB.QuatOrder
