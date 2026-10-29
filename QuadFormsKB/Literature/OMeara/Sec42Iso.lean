import QuadFormsKB.Literature.OMeara.Sec42
import QuadFormsKB.Literature.OMeara.Sec91Jordan

/-!
# O'Meara §42B, §42D: dual bases, hyperbolic planes, isotropy (42:5, 42:9, 42:11, 42:13)

**Setting** (as in `Sec42.lean`): $F$ a field with $2 \ne 0$, $(V, Q)$ a quadratic space over $F$, $B$ = `bil Q`,
*regular* = `(QuadraticMap.associated Q).Nondegenerate`, `gram Q x` the matrix $(B(x_i, x_j))$.

**Defines** `IsHyperbolicPlane Q` (O'Meara §42D, p. 94): $V$ has the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$
in some base.

**Proves** (O'Meara 1973 printing, Chapter IV, §42, pp. 92–96):
* `gram_dualBasis` (**42:5**): if $V$ is regular with matrix $N$ in a base, its matrix in the dual base (Mathlib's
  `LinearMap.BilinForm.dualBasis`, $B(y_i, x_j) = \delta_{ij}$) is $N^{-1}$;
* `exists_hyp_partner`: an isotropic vector $x \ne 0$ of a regular space has a partner $y$ with $Q(y) = 0$,
  $B(x, y) = 1$ (the first step of the proof of 42:10 and of 42:13 for $r = 1$);
* `isHyperbolicPlane_tfae` (**42:9**): for $\dim V = 2$ the following are equivalent: $V$ is a hyperbolic plane;
  $V$ is isotropic and regular; $dV = -1$ (some base has discriminant $-1$);
* `mem_range_iff_isotropic_prod` (**42:11**): for regular $V$ and $\alpha \in F$, $\alpha \in Q(V)$ iff
  $\langle -\alpha \rangle \perp V$ is isotropic;
* `exists_hyperbolic_partners` (**42:13**): if $x_1, \dots, x_r$ is a base of a subspace $U$ of a regular space with
  $Q(U) = 0$ (equivalently $B(x_i, x_j) = 0$), there are $y_1, \dots, y_r$ with $B(x_i, y_j) = \delta_{ij}$ and
  $B(y_i, y_j) = 0$ (so $Q(y_i) = 0$); then $H_i = Fx_i + Fy_i$ are hyperbolic planes with $x_i \in H_i$ and
  $H_1 \perp \dots \perp H_r$.

**Proof notes.** 42:9 (3) ⇒ (1) is done by solving for isotropic vectors in the given base (the discriminant
$b^2 - ac = 1$ of the binary form is a square), instead of O'Meara's route through 42:4. 42:13 is proved without
induction: the map $v \mapsto (B(x_i, v))_i$ is onto $F^r$ by a dimension count (42:6), giving $z_j$ with
$B(x_i, z_j) = \delta_{ij}$, and $y_j = z_j - \sum_k \tfrac12 B(z_j, z_k)\, x_k$.

**Conventions.** Indices are 0-based; O'Meara's $x_1, x_2$ are `b 0`, `b 1`. In 42:11,
$\langle -\alpha \rangle \perp V$ is the form $(t, x) \mapsto -\alpha t^2 + Q(x)$ on $F \times V$.
-/

open QuadraticMap Submodule Module LinearMap
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Sec42Iso

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)

theorem iv_two_inv_mul_two : (2 : F)⁻¹ * 2 = 1 := inv_mul_cancel₀ iv_two_ne

theorem iv_bil_zero_left (y : V) : bil Q 0 y = 0 := by simp [bil]
theorem iv_bil_zero_right (y : V) : bil Q y 0 = 0 := by simp [bil]

/-- **O'Meara 42:5** (p. 92). Let $V$ be regular with matrix $N$ in the base $x_1, \dots, x_n$, and let
$y_1, \dots, y_n$ be the dual base with respect to $B$ ($B(y_i, x_j) = \delta_{ij}$). Then the matrix $M$ of $V$ in
the dual base is $N^{-1}$. -/
@[kb "omeara1963" "§42B, 42:5, p. 92"]
theorem gram_dualBasis {ι : Type*} [Fintype ι] [DecidableEq ι] (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (b : Basis ι F V) : gram Q (LinearMap.BilinForm.dualBasis (QuadraticMap.associated Q) hQ b) = (gram Q b)⁻¹ := by
  set D := LinearMap.BilinForm.dualBasis (QuadraticMap.associated Q) hQ b
  have key : gram Q D * gram Q b = 1 := by
    ext i j
    have h1 : bil Q (D i) (b j) = if j = i then 1 else 0 :=
      LinearMap.BilinForm.apply_dualBasis_left hQ b i j
    have hb : b j = ∑ k, (D.repr (b j) k) • D k := (D.sum_repr (b j)).symm
    rw [hb, bil_sum_right] at h1
    simp only [bil_smul_right, D, LinearMap.BilinForm.dualBasis_repr_apply] at h1
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [gram, Matrix.of_apply]
    rw [show (if i = j then (1 : F) else 0) = if j = i then 1 else 0 by simp [eq_comm]]
    rw [← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
    congr 1
    exact bil_comm Q _ _
  exact (Matrix.inv_eq_left_inv key).symm

/-- An isotropic vector $x \ne 0$ of a regular space has a partner $y$ with $Q(y) = 0$ and $B(x, y) = 1$
(O'Meara p. 95, proofs of 42:10 and 42:13). -/
theorem exists_hyp_partner (hQ : (QuadraticMap.associated Q).Nondegenerate) {x : V} (hx0 : x ≠ 0)
    (hx : Q x = 0) : ∃ y, Q y = 0 ∧ bil Q x y = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, bil Q x w ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (hQ.1 x h)
  have h1 : bil Q x ((bil Q x w)⁻¹ • w) = 1 := by rw [bil_smul_right]; field_simp
  generalize (bil Q x w)⁻¹ • w = w' at h1
  refine ⟨w' - (Q w' / 2) • x, ?_, ?_⟩
  · rw [sub_eq_add_neg, Q_add, ← neg_smul, Q_smul, hx, bil_smul_right, bil_comm Q w' x, h1]
    linear_combination (-(Q w')) * (iv_two_inv_mul_two (F := F))
  · rw [bil_sub_right, bil_smul_right, bil_self, hx, h1]; ring

/-- **Hyperbolic plane** (O'Meara 1963, §42D, p. 94): $V$ has the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ in one
of its bases, i.e. a base $x, y$ with $Q(x) = Q(y) = 0$ and $B(x, y) = 1$. -/
@[kb "omeara1963" "§42D, p. 94 (hyperbolic plane)"]
def IsHyperbolicPlane : Prop := ∃ b : Basis (Fin 2) F V, gram Q b = !![0, 1; 1, 0]

/-- A hyperbolic pair in a binary space spans it as a hyperbolic plane. -/
theorem isHyperbolicPlane_of_pair (h2 : finrank F V = 2) {x y : V} (hx : Q x = 0) (hy : Q y = 0)
    (hxy : bil Q x y = 1) : IsHyperbolicPlane Q := by
  have hg : gram Q ![x, y] = !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gram, hx, hy, hxy, bil_comm Q y x]
  have hli : LinearIndependent F ![x, y] :=
    linearIndependent_of_det_gram_ne_zero (R := F) Q (by rw [hg]; simp [Matrix.det_fin_two])
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2]), ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank, hg]

theorem iv_Q_comb (e0 e1 : V) (s t : F) :
    Q (s • e0 + t • e1) = s ^ 2 * Q e0 + 2 * s * t * bil Q e0 e1 + t ^ 2 * Q e1 := by
  rw [Q_add, Q_smul, Q_smul, bil_smul_left, bil_smul_right]; ring

theorem iv_bil_comb (e0 e1 : V) (s t s' t' : F) :
    bil Q (s • e0 + t • e1) (s' • e0 + t' • e1) =
      s * s' * Q e0 + (s * t' + t * s') * bil Q e0 e1 + t * t' * Q e1 := by
  simp only [bil_add_left, bil_add_right, bil_smul_left, bil_smul_right, bil_self]
  rw [bil_comm Q e1 e0]; ring

/-- **O'Meara 42:9** (p. 94). For a binary quadratic space $V$ ($\dim V = 2$) the following are equivalent:
(1) $V$ is a hyperbolic plane; (2) $V$ is isotropic (has a vector $x \ne 0$ with $Q(x) = 0$) and regular;
(3) $dV = -1$, i.e. $V$ has a base $x_1, x_2$ with $d(x_1, x_2) = \det(B(x_i, x_j)) = -1$. -/
@[kb "omeara1963" "§42D, 42:9, p. 94"]
theorem isHyperbolicPlane_tfae (h2 : finrank F V = 2) :
    List.TFAE [IsHyperbolicPlane Q,
      (∃ x : V, x ≠ 0 ∧ Q x = 0) ∧ (QuadraticMap.associated Q).Nondegenerate,
      ∃ b : Basis (Fin 2) F V, (gram Q b).det = -1] := by
  tfae_have 1 → 3 := by
    rintro ⟨b, hb⟩
    exact ⟨b, by rw [hb]; simp [Matrix.det_fin_two]⟩
  tfae_have 3 → 1 := by
    rintro ⟨e, he⟩
    have hdet : Q (e 0) * Q (e 1) - bil Q (e 0) (e 1) * bil Q (e 0) (e 1) = -1 := by
      rw [← he, Matrix.det_fin_two]; simp [gram, bil_comm Q (e 1) (e 0)]
    by_cases ha : Q (e 0) = 0
    · refine isHyperbolicPlane_of_pair Q h2 (x := (1 : F) • e 0 + (0 : F) • e 1)
        (y := (-(Q (e 1) / 2)) • e 0 + bil Q (e 0) (e 1) • e 1) ?_ ?_ ?_
      · rw [iv_Q_comb]; linear_combination ha
      · rw [iv_Q_comb, ha]
        linear_combination (-(Q (e 1) * bil Q (e 0) (e 1) ^ 2)) * (iv_two_inv_mul_two (F := F))
      · rw [iv_bil_comb]
        linear_combination (Q (e 1) / 2) * ha - hdet + (-(Q (e 1) * Q (e 0))) * (iv_two_inv_mul_two (F := F))
    · have hk : (-2 * Q (e 0))⁻¹ * (-2 * Q (e 0)) = 1 :=
        inv_mul_cancel₀ (mul_ne_zero (neg_ne_zero.2 iv_two_ne) ha)
      refine isHyperbolicPlane_of_pair Q h2 (x := (1 - bil Q (e 0) (e 1)) • e 0 + Q (e 0) • e 1)
        (y := ((-2 * Q (e 0))⁻¹ * (-1 - bil Q (e 0) (e 1))) • e 0 + ((-2 * Q (e 0))⁻¹ * Q (e 0)) • e 1)
        ?_ ?_ ?_
      · rw [iv_Q_comb]; linear_combination Q (e 0) * hdet
      · rw [iv_Q_comb]; linear_combination ((-2 * Q (e 0))⁻¹) ^ 2 * Q (e 0) * hdet
      · rw [iv_bil_comb]; linear_combination (-2 * Q (e 0))⁻¹ * Q (e 0) * hdet + hk
  tfae_have 1 → 2 := by
    rintro ⟨e, he⟩
    have hg : ∀ i j, bil Q (e i) (e j) = !![(0 : F), 1; 1, 0] i j := fun i j => by
      rw [← he]; rfl
    refine ⟨⟨e 0, e.ne_zero 0, by rw [← bil_self]; simpa using hg 0 0⟩, ?_⟩
    refine (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (B := QuadraticMap.associated Q) e).2 ?_
    have : LinearMap.BilinForm.toMatrix e (QuadraticMap.associated Q) = !![0, 1; 1, 0] := by
      ext i j; rw [LinearMap.BilinForm.toMatrix_apply]; exact hg i j
    rw [this]; simp [Matrix.det_fin_two]
  tfae_have 2 → 1 := by
    rintro ⟨⟨x, hx0, hx⟩, hQ⟩
    obtain ⟨y, hy, hxy⟩ := exists_hyp_partner Q hQ hx0 hx
    exact isHyperbolicPlane_of_pair Q h2 hx hy hxy
  tfae_finish

/-- A regular isotropic space is universal (O'Meara 42:10, p. 95, second sentence). -/
theorem exists_eq_of_isotropic' (hQ : (QuadraticMap.associated Q).Nondegenerate) {x : V} (hx0 : x ≠ 0)
    (hx : Q x = 0) (α : F) : ∃ v, Q v = α := by
  obtain ⟨y, hy, hxy⟩ := exists_hyp_partner Q hQ hx0 hx
  refine ⟨(α / 2) • x + y, ?_⟩
  rw [Q_add, Q_smul, hx, hy, bil_smul_left, hxy]
  field_simp; ring

/-- **O'Meara 42:11** (p. 95). Let $V$ be regular and $\alpha \in F$. Then $\alpha \in Q(V)$ if and only if
$\langle -\alpha \rangle \perp V$ is isotropic, i.e. the form $(t, \vec{x}) \mapsto -\alpha t^2 + Q(\vec{x})$ on
$F \times V$ has a zero $(t, \vec{x}) \ne 0$. -/
@[kb "omeara1963" "§42D, 42:11, p. 95"]
theorem mem_range_iff_isotropic_prod (hQ : (QuadraticMap.associated Q).Nondegenerate) (α : F) :
    (∃ x, Q x = α) ↔ ∃ v : F × V, v ≠ 0 ∧ ((-α) • QuadraticMap.sq (R := F) (A := F)).prod Q v = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(1, x), by simp, ?_⟩
    simp [QuadraticMap.prod_apply, hx]
  · rintro ⟨⟨t, x⟩, hne, h0⟩
    simp only [QuadraticMap.prod_apply, _root_.smul_apply, QuadraticMap.sq_apply, smul_eq_mul] at h0
    by_cases ht : t = 0
    · subst ht
      have hx0 : x ≠ 0 := fun h => hne (by simp [h])
      exact exists_eq_of_isotropic' Q hQ hx0 (by simpa using h0) α
    · refine ⟨t⁻¹ • x, ?_⟩
      rw [Q_smul]
      field_simp
      linear_combination h0

/-- **O'Meara 42:13** (p. 95). Let $V$ be regular and $x_1, \dots, x_r$ a base of a subspace $U$ with $Q(U) = 0$
(equivalently $B(x_i, x_j) = 0$ for all $i, j$). Then there are $y_1, \dots, y_r \in V$ with $B(x_i, y_j) = \delta_{ij}$
and $B(y_i, y_j) = 0$ for all $i, j$; hence the planes $H_i = Fx_i + Fy_i$ are hyperbolic planes containing $x_i$,
pairwise orthogonal, and $H_1 \perp \dots \perp H_r$ is a subspace of $V$. -/
@[kb "omeara1963" "§42D, 42:13, p. 95"]
theorem exists_hyperbolic_partners [FiniteDimensional F V] (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {x : ι → V} (hli : LinearIndependent F x)
    (hiso : ∀ i j, bil Q (x i) (x j) = 0) :
    ∃ y : ι → V, (∀ i j, bil Q (x i) (y j) = if i = j then 1 else 0) ∧ ∀ i j, bil Q (y i) (y j) = 0 := by
  -- Step 1: the map v ↦ (B(x_i, v))_i is onto.
  let φ : V →ₗ[F] (ι → F) := LinearMap.pi fun i => QuadraticMap.associated Q (x i)
  have hker : LinearMap.ker φ =
      LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) (Submodule.span F (Set.range x)) := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro hv n hn
      refine Submodule.span_induction (p := fun n _ => QuadraticMap.associated Q n v = 0) ?_ ?_ ?_ ?_ hn
      · rintro _ ⟨i, rfl⟩; exact congrFun hv i
      · simp
      · intro a b _ _ ha hb; rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      · intro c a _ ha; rw [map_smul, LinearMap.smul_apply, ha, smul_zero]
    · intro hv
      funext i
      exact hv (x i) (Submodule.subset_span ⟨i, rfl⟩)
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    rw [hker, LinearMap.BilinForm.finrank_orthogonal hQ, finrank_span_eq_card hli] at h1
    have h2 : Fintype.card ι ≤ finrank F V := by
      rw [← finrank_span_eq_card hli]; exact Submodule.finrank_le _
    rw [Module.finrank_fintype_fun_eq_card]
    omega
  choose z hz using fun j => hsurj (Pi.single j 1)
  have hxz : ∀ i j, bil Q (x i) (z j) = if i = j then 1 else 0 := fun i j => by
    have := congrFun (hz j) i
    simp only [φ, LinearMap.pi_apply] at this
    show QuadraticMap.associated Q (x i) (z j) = _
    rw [this, Pi.single_apply]
  -- Step 2: correct z_j by a combination of the x_k.
  let c : ι → ι → F := fun j k => bil Q (z j) (z k) / 2
  refine ⟨fun j => z j - ∑ k, c j k • x k, fun i j => ?_, fun i j => ?_⟩
  · simp only [bil_sub_right, bil_sum_right, bil_smul_right, hiso, mul_zero, Finset.sum_const_zero, sub_zero,
      hxz]
  · have hzx : ∀ j k, bil Q (z j) (x k) = if k = j then 1 else 0 := fun j k => by
      rw [bil_comm]; exact hxz k j
    simp only [bil_sub_right, bil_sub_left, bil_sum_right, bil_sum_left, bil_smul_right, bil_smul_left, hiso,
      mul_zero, Finset.sum_const_zero, sub_zero, hzx, hxz, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, c]
    rw [bil_comm Q (z j) (z i)]
    linear_combination (-(bil Q (z i) (z j))) * (iv_two_inv_mul_two (F := F))

end Sec42Iso

end QuadFormsKB.OMeara
