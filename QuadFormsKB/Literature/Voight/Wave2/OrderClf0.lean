/-
# Orders in $(a, b \mid K)$ with a basis containing $1$ are even Clifford algebras (Voight, Proposition 22.4.4)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021, Proposition 22.4.4 (p. 364), 22.4.7 (p. 365),
Corollary 10.3.6 (key `voight2021`).

**Statement** (`exists_algEquiv_evenClf_of_basis`). Let $R$ be an integrally closed domain with fraction field $K$,
$a, b \in K$, and $\mathcal O \subseteq (a, b \mid K)$ an $R$-order (`QuatOrder.IsOrder`) which has an $R$-basis
$1, i, j, k$ containing $1$. Then $\mathcal O \cong$ `EvenClf R a' b' c' u v w` (the even Clifford algebra with the
table (22.3.7)) for some $a', \dots, w \in R$.

Over a principal ideal domain every order has such a basis (`exists_basis_one`, Exercise 22.1), and when
$2, a, b \ne 0$ the resulting form is nondegenerate (`halfDisc_ne_zero`), so (`exists_clf0`, Proposition 22.4.4)
every $R$-order in $(a, b \mid K)$ is $\operatorname{Clf}^0(Q)$ for a nondegenerate $Q$, unique up to similarity
(`exists_unique_clf0`, Main Theorem 22.4.1 for these orders).

**Proof.** The hypotheses of `GoodBasis.exists_algEquiv_evenClf` hold:
* $\operatorname{trd}(x) = 2x_0$ and $\operatorname{nrd}(x)$ lie in $R$ for $x \in \mathcal O$ (Corollary 10.3.6,
  `QuatOrder.isInteger_trd_nrd`), and $x^2 = \operatorname{trd}(x)x - \operatorname{nrd}(x)$ (`QuatOrder.mul_self_eq`);
* the trace of left multiplication on $\mathcal O$ over $R$ is that of $(a, b \mid K)$ over $K$ (an $R$-basis of
  $\mathcal O$ is a $K$-basis of $(a, b \mid K)$), which is $4x_0 = 2\operatorname{trd}(x)$ in the basis $1, i, j, k$.
-/
import QuadFormsKB.Literature.Voight.Wave2.GoodBasis
import QuadFormsKB.Tamagawa.QuatOrder

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Quaternion Matrix

namespace QuadFormsKB.Voight

namespace OrderClf0

open QuadFormsKB.QuatOrder

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [IsIntegrallyClosed R] {a b : K} {O : Subalgebra R ℍ[K,a,b]} (hO : IsOrder R K O)

/-- The reduced trace of an element of an order, as an element of $R$ (Corollary 10.3.6). -/
noncomputable def trdO (x : O) : R := (isInteger_trd_nrd hO x.2).1.choose

/-- The reduced norm of an element of an order, as an element of $R$ (Corollary 10.3.6). -/
noncomputable def nrdO (x : O) : R := (isInteger_trd_nrd hO x.2).2.choose

theorem algebraMap_trdO (x : O) : algebraMap R K (trdO hO x) = trd (x : ℍ[K,a,b]) :=
  (isInteger_trd_nrd hO x.2).1.choose_spec

theorem algebraMap_nrdO (x : O) : algebraMap R K (nrdO hO x) = Quat.nrd (x : ℍ[K,a,b]) :=
  (isInteger_trd_nrd hO x.2).2.choose_spec

/-- The reduced trace $\mathcal O \to R$ is $R$-linear. -/
noncomputable def trdL : O →ₗ[R] R where
  toFun := trdO hO
  map_add' x y := IsFractionRing.injective R K (by
    simp only [map_add, algebraMap_trdO, Subalgebra.coe_add, trd, QuaternionAlgebra.re_add]; ring)
  map_smul' r x := IsFractionRing.injective R K (by
    simp only [map_mul, algebraMap_trdO, Subalgebra.coe_smul, trd, RingHom.id_apply, smul_eq_mul]
    rw [← algebraMap_smul K r (x : ℍ[K,a,b]), QuaternionAlgebra.re_smul, smul_eq_mul]; ring)

theorem mul_self_eq_O (x : O) : x * x = trdL hO x • x - algebraMap R O (nrdO hO x) := by
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_smul, Subalgebra.coe_algebraMap]
  rw [mul_self_eq (x : ℍ[K,a,b]), ← algebraMap_smul K (trdL hO x) (x : ℍ[K,a,b]),
    IsScalarTower.algebraMap_apply R K ℍ[K,a,b], algebraMap_nrdO]
  show trd (x : ℍ[K,a,b]) • (x : ℍ[K,a,b]) - _ = algebraMap R K (trdO hO x) • (x : ℍ[K,a,b]) - _
  rw [algebraMap_trdO]

/-- The trace of left multiplication on $(a, b \mid K)$: $\operatorname{Tr}(L_x) = 4x_0 = 2\operatorname{trd}(x)$. -/
theorem trace_mulLeft_quat (x : ℍ[K,a,b]) :
    LinearMap.trace K ℍ[K,a,b] (LinearMap.mulLeft K x) = 2 * trd x := by
  rw [LinearMap.trace_eq_matrix_trace K (QuaternionAlgebra.basisOneIJK a 0 b), Matrix.trace,
    Fin.sum_univ_four]
  have hb : ∀ j, QuaternionAlgebra.basisOneIJK a 0 b j =
      ⟨(Pi.single j (1 : K) : Fin 4 → K) 0, (Pi.single j (1 : K) : Fin 4 → K) 1,
        (Pi.single j (1 : K) : Fin 4 → K) 2, (Pi.single j (1 : K) : Fin 4 → K) 3⟩ := by
    intro j; rw [QuaternionAlgebra.basisOneIJK, Module.Basis.coe_ofEquivFun]; rfl
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply,
    QuaternionAlgebra.coe_basisOneIJK_repr, hb]
  simp [Pi.single_apply, trd]
  ring

variable (e : Module.Basis (Fin 4) R O)

theorem linearIndependent_coe : LinearIndependent K (fun m => (e m : ℍ[K,a,b])) := by
  rw [← LinearIndependent.iff_fractionRing (R := R)]
  exact e.linearIndependent.map' O.val.toLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)

/-- An $R$-basis of the order is a $K$-basis of $(a, b \mid K)$. -/
noncomputable def basisK : Module.Basis (Fin 4) K ℍ[K,a,b] :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_coe e)
    (by rw [Fintype.card_fin, QuaternionAlgebra.finrank_eq_four])

theorem basisK_apply (m : Fin 4) : basisK e m = (e m : ℍ[K,a,b]) := by
  simp [basisK]

theorem basisK_repr (y : O) (m : Fin 4) :
    (basisK e).repr (y : ℍ[K,a,b]) m = algebraMap R K (e.repr y m) := by
  have hy : (y : ℍ[K,a,b]) = ∑ m, algebraMap R K (e.repr y m) • basisK e m := by
    conv_lhs => rw [← e.sum_repr y]
    simp only [AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, basisK_apply, algebraMap_smul]
  rw [hy, Module.Basis.repr_sum_self]

/-- **The trace of left multiplication on an order** is $2\operatorname{trd}$. -/
theorem trace_mulLeft_O (e : Module.Basis (Fin 4) R O) (x : O) :
    LinearMap.trace R O (LinearMap.mulLeft R x) = 2 * trdL hO x := by
  apply IsFractionRing.injective R K
  rw [map_mul, map_ofNat, show trdL hO x = trdO hO x from rfl, algebraMap_trdO, ← trace_mulLeft_quat,
    LinearMap.trace_eq_matrix_trace R e, LinearMap.trace_eq_matrix_trace K (basisK e), Matrix.trace,
    Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply]
  rw [basisK_apply, ← Subalgebra.coe_mul, basisK_repr]

include hO in
/-- **Proposition 22.4.4 for orders in $(a, b \mid K)$ with a basis containing $1$** (Voight 2021; 22.4.7):
if $R$ is an integrally closed domain with fraction field $K$ and the $R$-order $\mathcal O \subseteq (a, b \mid K)$
has an $R$-basis $e$ with $e_0 = 1$, then $\mathcal O \cong$ `EvenClf R a' b' c' u v w` for some
$a', b', c', u, v, w \in R$ (a good basis exists). -/
@[kb "voight2021" "Proposition 22.4.4, p. 364; 22.4.7, p. 365"]
theorem exists_algEquiv_evenClf_of_basis (he : e 0 = 1) :
    ∃ a' b' c' u v w : R, Nonempty (O ≃ₐ[R] EvenClf R a' b' c' u v w) :=
  GoodBasis.exists_algEquiv_evenClf (trdL hO) (nrdO hO) (mul_self_eq_O hO) (trace_mulLeft_O hO e) e he

/-! ## A basis containing $1$ over a principal ideal domain (Exercise 22.1) -/

section PID

variable [IsPrincipalIdealRing R]

include hO in
/-- **$1$ is primitive in an order**: if $r z \in R\cdot 1$ with $r \ne 0$, then $z \in R \cdot 1$ (since $z \in K$ is
integral over the integrally closed $R$). -/
theorem mem_span_one_of_smul_mem {r : R} (hr : r ≠ 0) {z : O} (h : r • z ∈ R ∙ (1 : O)) :
    z ∈ R ∙ (1 : O) := by
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 h
  have hr' : algebraMap R K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hr
  have hB : algebraMap R K s • (1 : ℍ[K,a,b]) = algebraMap R K r • (z : ℍ[K,a,b]) := by
    have := congrArg Subtype.val hs
    simp only [Subalgebra.coe_smul, Subalgebra.coe_one] at this
    rw [algebraMap_smul, algebraMap_smul]; exact this
  have hzB : (z : ℍ[K,a,b]) = algebraMap K ℍ[K,a,b] (algebraMap R K s / algebraMap R K r) := by
    rw [Algebra.algebraMap_eq_smul_one, div_eq_inv_mul, mul_smul, hB, smul_smul, inv_mul_cancel₀ hr',
      one_smul]
  have hint : IsIntegral R (algebraMap K ℍ[K,a,b] (algebraMap R K s / algebraMap R K r)) :=
    hzB ▸ hO.isIntegral z.2
  obtain ⟨t, ht⟩ := isInteger_of_isIntegral_algebraMap hint
  refine Submodule.mem_span_singleton.2 ⟨t, Subtype.ext ?_⟩
  simp only [Subalgebra.coe_smul, Subalgebra.coe_one]
  rw [hzB, ← ht, ← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one]

include hO in
/-- Every $R$-basis of an order has $4$ elements. -/
theorem card_eq_four {ι : Type*} [Fintype ι] (f : Module.Basis ι R O) : Fintype.card ι = 4 := by
  have hli : LinearIndependent K (fun m => (f m : ℍ[K,a,b])) := by
    rw [← LinearIndependent.iff_fractionRing (R := R)]
    exact f.linearIndependent.map' O.val.toLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  have hsp : ⊤ ≤ Submodule.span K (Set.range fun m => (f m : ℍ[K,a,b])) := by
    rw [← hO.span]
    refine Submodule.span_le.2 fun z hz => ?_
    have hz' : z = ∑ m, algebraMap R K (f.repr ⟨z, hz⟩ m) • (f m : ℍ[K,a,b]) := by
      conv_lhs => rw [show z = ((⟨z, hz⟩ : O) : ℍ[K,a,b]) from rfl, ← f.sum_repr ⟨z, hz⟩]
      simp only [AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, algebraMap_smul]
    rw [SetLike.mem_coe, hz']
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  rw [← QuaternionAlgebra.finrank_eq_four (R := K) a 0 b, Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)]

include hO in
/-- **An order over a principal ideal domain has a basis containing $1$** (Voight, Exercise 22.1, used in the
proof of Proposition 22.4.4): $\mathcal O/R\cdot1$ is torsion-free (`mem_span_one_of_smul_mem`), hence free, so
$\mathcal O = R\cdot 1 \oplus N$ with $N$ free of rank $3$. -/
@[kb "voight2021" "Proposition 22.4.4, p. 364 (Exercise 22.1)"]
theorem exists_basis_one : ∃ e : Module.Basis (Fin 4) R O, e 0 = 1 := by
  classical
  set L : Submodule R O := R ∙ (1 : O)
  haveI : Module.Finite R O :=
    (Module.Finite.iff_fg.2 hO.fg : Module.Finite R (Subalgebra.toSubmodule O))
  haveI : Module.IsTorsionFree R (O ⧸ L) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r q hq => ?_
    obtain ⟨z, rfl⟩ := L.mkQ_surjective q
    by_cases hr : r = 0
    · exact Or.inl hr
    · refine Or.inr ?_
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact mem_span_one_of_smul_mem hO hr hq
  obtain ⟨sec, hsec⟩ := Module.projective_lifting_property L.mkQ LinearMap.id L.mkQ_surjective
  have hsec' : ∀ q, L.mkQ (sec q) = q := fun q => LinearMap.congr_fun hsec q
  have sinj : Function.Injective sec := fun x y h => by
    rw [← hsec' x, ← hsec' y, h]
  set N := LinearMap.range sec
  let bN : Module.Basis (Fin (Module.finrank R (O ⧸ L))) R N :=
    (Module.finBasis R (O ⧸ L)).map (LinearEquiv.ofInjective sec sinj)
  have hli : ∀ (c : R), ∀ x ∈ N, c • (1 : O) + x = 0 → c = 0 := by
    intro c x hx hcx
    obtain ⟨q, rfl⟩ := hx
    have h10 : L.mkQ (1 : O) = 0 :=
      (Submodule.Quotient.mk_eq_zero L).2 (Submodule.mem_span_singleton_self (1 : O))
    have h1 := congrArg L.mkQ hcx
    rw [map_add, map_smul, hsec', map_zero, h10, smul_zero, zero_add] at h1
    rw [h1, map_zero, add_zero] at hcx
    have h3 := congrArg Subtype.val hcx
    simp only [Subalgebra.coe_smul, Subalgebra.coe_one, ZeroMemClass.coe_zero] at h3
    rw [← algebraMap_smul K c (1 : ℍ[K,a,b]), smul_eq_zero] at h3
    exact (map_eq_zero_iff _ (IsFractionRing.injective R K)).1 (h3.resolve_right one_ne_zero)
  have hsp : ∀ z : O, ∃ c : R, z + c • (1 : O) ∈ N := by
    intro z
    have hz : z - sec (L.mkQ z) ∈ L := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hsec', sub_self]
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨-r, ⟨L.mkQ z, by rw [neg_smul, hr]; abel⟩⟩
  let e' := Module.Basis.mkFinCons (1 : O) bN hli hsp
  have hcard : Module.finrank R (O ⧸ L) + 1 = 4 := by
    have := card_eq_four hO e'; rwa [Fintype.card_fin] at this
  refine ⟨e'.reindex (finCongr hcard), ?_⟩
  rw [Module.Basis.reindex_apply]
  simp [e']
end PID

/-! ## Nondegeneracy and Proposition 22.4.4 -/

section Nondeg

variable {a' b' c' u v w : R}

theorem trdL_algebraMap (r : R) : trdL hO (algebraMap R O r) = 2 * r := by
  apply IsFractionRing.injective R K
  show algebraMap R K (trdO hO _) = _
  rw [algebraMap_trdO, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply R K ℍ[K,a,b]]
  simp [trd, QuaternionAlgebra.algebraMap_eq, map_ofNat]

/-- **An isomorphism onto an even Clifford algebra preserves the reduced trace** (uniqueness of the standard
involution, Voight Corollary 3.4.4). -/
theorem trd_map (φ : O ≃ₐ[R] EvenClf R a' b' c' u v w) (x : O) : EvenClf.trd (φ x) = trdL hO x := by
  set y := φ x with hy
  have h1 := EvenClf.sq_sub_trd_mul_add_nrd y
  have h2 : y * y - trdL hO x • y + algebraMap R _ (nrdO hO x) = 0 := by
    have := congrArg φ (mul_self_eq_O hO x)
    rw [map_mul, map_sub, map_smul, AlgEquiv.commutes, ← hy] at this
    rw [this]; abel
  have hd : (EvenClf.trd y - trdL hO x) • y = algebraMap R _ (EvenClf.nrd y - nrdO hO x) := by
    have := congrArg₂ (· - ·) h1 h2
    simp only [sub_self] at this
    rw [map_sub, sub_smul]
    linear_combination (norm := skip) -this
    ext <;> simp <;> ring
  by_contra hne
  have ht : EvenClf.trd y - trdL hO x ≠ 0 := sub_ne_zero.2 hne
  have hi : y.i = 0 := by
    have := congrArg EvenClf.i hd; simp at this; exact this.resolve_left ht
  have hj : y.j = 0 := by
    have := congrArg EvenClf.j hd; simp at this; exact this.resolve_left ht
  have hk : y.k = 0 := by
    have := congrArg EvenClf.k hd; simp at this; exact this.resolve_left ht
  have hys : y = algebraMap R _ y.re := by ext <;> simp [hi, hj, hk]
  have hx : x = algebraMap R O y.re := by
    apply φ.injective; rw [AlgEquiv.commutes, ← hy]; exact hys
  apply hne
  rw [hys, hx, trdL_algebraMap]; simp [EvenClf.trd]

/-- The trace form of $(a, b \mid K)$ in coordinates: $(\operatorname{trd}(v_pv_q)) = C^{\mathsf T}\operatorname{diag}(2, 2a, 2b,
-2ab)\,C$, with $C$ the coordinate matrix of $v$. -/
theorem trdGram_eq (vv : Fin 4 → ℍ[K,a,b]) :
    (Matrix.of fun p q => trd (vv p * vv q)) =
      (Matrix.of fun r p => ![(vv p).re, (vv p).imI, (vv p).imJ, (vv p).imK] r)ᵀ *
        Matrix.diagonal ![2, 2 * a, 2 * b, -(2 * a * b)] *
        Matrix.of fun r p => ![(vv p).re, (vv p).imI, (vv p).imJ, (vv p).imK] r := by
  ext p q
  simp only [Matrix.of_apply, trd, Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply,
    Fin.sum_univ_four, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp
  ring

include hO in
/-- **The even Clifford algebra of an order is nondegenerate**: if $2, a, b \ne 0$ in $K$ and
$\mathcal O \cong$ `EvenClf R a' b' c' u v w`, then the half-discriminant $N \ne 0$ (the discriminant
$-N^2$ of the basis $1, i, j, k$ is, up to a square, that of a $K$-basis of $(a, b \mid K)$, which is nonzero). -/
theorem halfDisc_ne_zero (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (φ : O ≃ₐ[R] EvenClf R a' b' c' u v w) : EvenClf.halfDisc a' b' c' u v w ≠ 0 := by
  intro hN
  set E : Fin 4 → EvenClf R a' b' c' u v w := ![1, EvenClf.ei, EvenClf.ej, EvenClf.ek]
  let g : Module.Basis (Fin 4) R O := EvenClf.basisOneIJK.map φ.symm.toLinearEquiv
  have hg : ∀ p, g p = φ.symm (E p) := fun p => by
    simp only [g, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply]
    congr 1
    rw [EvenClf.basisOneIJK_apply']
    fin_cases p <;> ext <;> simp [E, EvenClf.ei, EvenClf.ej, EvenClf.ek, Pi.single_apply]
  set vv : Fin 4 → ℍ[K,a,b] := fun p => (g p : ℍ[K,a,b])
  -- the trace Gram determinant over K is the image of -N^2 = 0
  have hdet : (Matrix.of fun p q => trd (vv p * vv q)).det = 0 := by
    have hG : (Matrix.of fun p q => trd (vv p * vv q)) =
        (Matrix.of fun p q => EvenClf.trd (E p * E q)).map (algebraMap R K) := by
      ext p q
      simp only [Matrix.of_apply, Matrix.map_apply, vv]
      rw [← Subalgebra.coe_mul, ← algebraMap_trdO hO, ← show trdL hO (g p * g q) = trdO hO _ from rfl,
        ← trd_map hO φ, map_mul, hg, hg, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    rw [hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, EvenClf.det_trd_gram, hN]; simp
  -- but vv is a K-basis
  have hli := linearIndependent_coe g
  let fb := basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Fintype.card_fin, QuaternionAlgebra.finrank_eq_four])
  have hC := (QuaternionAlgebra.basisOneIJK a 0 b).isUnit_det fb
  rw [Module.Basis.det_apply] at hC
  have hCe : (QuaternionAlgebra.basisOneIJK a 0 b).toMatrix fb =
      Matrix.of fun r p => ![(vv p).re, (vv p).imI, (vv p).imJ, (vv p).imK] r := by
    ext r p
    rw [Module.Basis.toMatrix_apply, coe_basisOfLinearIndependentOfCardEqFinrank,
      QuaternionAlgebra.coe_basisOneIJK_repr]
    rfl
  rw [hCe] at hC
  rw [trdGram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    Fin.prod_univ_four] at hdet
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at hdet
  have hC0 := hC.ne_zero
  have : (2 : K) * (2 * a) * (2 * b) * -(2 * a * b) ≠ 0 := by
    simp [h2, ha, hb]
  exact (mul_ne_zero (mul_ne_zero hC0 this) hC0) hdet

include hO in
/-- **Proposition 22.4.4 (Voight 2021) for orders in $(a, b \mid K)$ over a principal ideal domain**: if $R$ is a
principal ideal domain with fraction field $K$, $2 \ne 0$ in $K$, $a, b \in K^\times$ and $\mathcal O \subseteq (a,b \mid K)$
is an $R$-order, then $\mathcal O \cong \operatorname{Clf}^0(Q)$ for a nondegenerate ternary quadratic form $Q$ over $R$
($N = \operatorname{disc} Q \ne 0$). -/
@[kb "voight2021" "Proposition 22.4.4, p. 364"]
theorem exists_clf0 [IsPrincipalIdealRing R] (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ Q : QuadForm R 3, ternaryDisc Q ≠ 0 ∧ Nonempty (O ≃ₐ[R] Clf0 Q) := by
  obtain ⟨e, he⟩ := exists_basis_one hO
  obtain ⟨a', b', c', u, v, w, ⟨φ⟩⟩ := exists_algEquiv_evenClf_of_basis hO e he
  let Q : QuadForm R 3 := QuadForm.ofUpper ![![a', w, v], ![0, b', u], ![0, 0, c']]
  have h00 : Q.coeff 0 0 = a' := by simp [Q, QuadForm.ofUpper]
  have h11 : Q.coeff 1 1 = b' := by simp [Q, QuadForm.ofUpper]
  have h22 : Q.coeff 2 2 = c' := by simp [Q, QuadForm.ofUpper]
  have h12 : Q.coeff 1 2 = u := by simp [Q, QuadForm.ofUpper]
  have h02 : Q.coeff 0 2 = v := by simp [Q, QuadForm.ofUpper]
  have h01 : Q.coeff 0 1 = w := by simp [Q, QuadForm.ofUpper]
  refine ⟨Q, ?_, ⟨φ.trans (EvenClf.congrEquiv h00.symm h11.symm h22.symm h12.symm h02.symm h01.symm)⟩⟩
  rw [ternaryDisc, h00, h11, h22, h12, h02, h01]
  exact halfDisc_ne_zero hO h2 ha hb φ


include hO in
/-- **Main Theorem 22.4.1 for orders in $(a, b \mid K)$** (Voight 2021): let $R$ be a principal ideal domain with
fraction field $K$, $2 \ne 0$ in $K$ and $a, b \in K^\times$. Every $R$-order $\mathcal O \subseteq (a, b \mid K)$ is
isomorphic to $\operatorname{Clf}^0(Q)$ for a nondegenerate ternary form $Q$ over $R$, and $Q$ is unique up to
similarity: if also $\mathcal O \cong \operatorname{Clf}^0(Q')$ with $Q'$ nondegenerate, then $Q$ and $Q'$ are similar.
(Conversely `isQuaternionOrder_clf0` shows that every $\operatorname{Clf}^0(Q)$ with $Q$ nondegenerate is a quaternion
order.) -/
@[kb "voight2021" "Main Theorem 22.4.1, p. 364; Proposition 22.4.4, p. 364; Proposition 22.4.12, p. 366"]
theorem exists_unique_clf0 [IsPrincipalIdealRing R] (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ Q : QuadForm R 3, ternaryDisc Q ≠ 0 ∧ Nonempty (O ≃ₐ[R] Clf0 Q) ∧
      ∀ Q' : QuadForm R 3, ternaryDisc Q' ≠ 0 → Nonempty (O ≃ₐ[R] Clf0 Q') → Similar Q Q' := by
  obtain ⟨Q, hQ, ⟨φ⟩⟩ := exists_clf0 hO h2 ha hb
  exact ⟨Q, hQ, ⟨φ⟩, fun Q' hQ' ⟨ψ⟩ => similar_of_nonempty_clf0_equiv hQ hQ' ⟨φ.symm.trans ψ⟩⟩

end Nondeg

end OrderClf0

end QuadFormsKB.Voight
