/-
# Left ideals of local maximal orders are principal; $\det(x \mapsto x\alpha) = \operatorname{nrd}(\alpha)^2$

**Layer:** $R$ a Henselian DVR with fraction field $K$, $D = (a,b)_K$, $\mathcal O \subset D$ a maximal $R$-order: either the valuation ring of
the division algebra $D$ (ramified case, `valOrder`) or $\varphi^{-1}(M_2(R))$ for an isomorphism $\varphi : D \cong M_2(K)$ (split case).

* `det_mulRight`: the $K$-linear map $x \mapsto x\alpha$ of $D$ has determinant $\operatorname{nrd}(\alpha)^2$ (any field $K$).
* `exists_eq_rTrans_of_valOrder`, `exists_eq_rTrans_of_map_eq_matOrder`: every left ideal $I$ of $\mathcal O$ with
  $\operatorname{nrd}(I) \ne 0$ is $\mathcal O\alpha$ for some $\alpha$ with $\operatorname{nrd}(\alpha) \ne 0$ (as subsets of $D$). Ramified: the
  `exists_eq_span_singleton`. Split: the row space of $I$ is a Hermite lattice $R(\pi^{k-b}, c) + R(0, \pi^b)$ (`exists_eq_hnf`), so $I$ is
  $M_2(R)P$ with $P = \begin{pmatrix}\pi^{k-b} & c\\ 0 & \pi^b\end{pmatrix}$ (`ofRowSpace_hnf`).

Source: Voight, *Quaternion Algebras* (2021), Prop. 16.4.3 / Lemma 16.4.11 (locally principal = invertible lattices over a local
maximal order), Ex. 3.3.3/(4.2.?) for $\det$ of multiplication; locators checked in the author's PDF.
-/
import QuadFormsKB.Tamagawa.QuatUnitsFinite

open Quaternion IsLocalization

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat

/-! ### The determinant of right multiplication -/

section DetMul

variable {K : Type*} [Field K] {a b : K}

/-- **$\det_K(x \mapsto x\alpha) = \operatorname{nrd}(\alpha)^2$** on $D = (a,b)_K$ (direct $4\times4$ computation in the basis $1, i, j, k$). -/
theorem det_mulRight (α : ℍ[K,a,b]) :
    LinearMap.det (LinearMap.mulRight K α) = nrd α ^ 2 := by
  rw [← LinearMap.det_toMatrix (QuaternionAlgebra.basisOneIJK a 0 b), Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, LinearMap.toMatrix_apply,
    QuaternionAlgebra.basisOneIJK, Fin.succAbove, nrd]
  ring

end DetMul

/-! ### Principal left ideals of local maximal orders -/

section LocalPrincipal

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] {a b : K}

theorem idealSet_span_singleton {O : Subalgebra R ℍ[K,a,b]} (y : O) :
    idealSet (Ideal.span {y}) = rTrans (O : Set ℍ[K,a,b]) (y : ℍ[K,a,b]) := by
  ext x
  constructor
  · rintro ⟨hx, hxI⟩
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hxI
    refine ⟨r, r.2, ?_⟩
    have := congrArg Subtype.val hr
    simpa using this
  · rintro ⟨r, hr, rfl⟩
    refine ⟨O.mul_mem hr y.2, Submodule.mem_span_singleton.2 ⟨⟨r, hr⟩, rfl⟩⟩

/-- **Ramified case:** every left ideal of the valuation ring with $\operatorname{nrd}(I) \ne 0$ is $\mathcal O\alpha$. -/
theorem exists_eq_rTrans_of_valOrder [HenselianLocalRing R] (hdiv : ∀ x : ℍ[K,a,b], nrd x = 0 → x = 0)
    (O : Subalgebra R ℍ[K,a,b]) (hO : O = valOrder (R := R) hdiv) (I : Ideal O) (hI : leftNrdIdeal I ≠ ⊥) :
    ∃ α : ℍ[K,a,b], nrd α ≠ 0 ∧ idealSet I = rTrans (O : Set ℍ[K,a,b]) α := by
  subst hO
  obtain ⟨y, rfl⟩ := exists_eq_span_singleton hdiv I
  refine ⟨y, fun h => ?_, idealSet_span_singleton y⟩
  have hy : y = 0 := Subtype.ext (hdiv _ h)
  apply hI
  rw [hy, Ideal.span_singleton_eq_bot.2 rfl, leftNrdIdeal, eq_bot_iff, Ideal.span_le]
  rintro r ⟨x, hx, hr⟩
  rw [(Submodule.mem_bot _).1 hx] at hr
  simp only [ZeroMemClass.coe_zero, SetLike.mem_coe, Submodule.mem_bot] at hr ⊢
  have : algebraMap R K r = 0 := by rw [hr]; simp [nrd]
  exact (map_eq_zero_iff _ (IsFractionRing.injective R K)).1 this

/-- **The Hermite row-space ideal is principal:** the matrices with rows in $R(\pi^a, c) + R(0,\pi^b)$ are exactly $YP$,
$P = \begin{pmatrix}\pi^a & c\\ 0 & \pi^b\end{pmatrix}$. -/
theorem mem_ofRowSpace_hnf {π : R} {a' b' : ℕ} {c : R} {X : Matrix (Fin 2) (Fin 2) R} :
    X ∈ ofRowSpace (hnf π a' b' c) ↔ ∃ Y : Matrix (Fin 2) (Fin 2) R, X = Y * !![π ^ a', c; 0, π ^ b'] := by
  constructor
  · intro hX
    choose r t ht using fun i => mem_hnf.1 (hX i)
    refine ⟨!![r 0, t 0; r 1, t 1], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, congrFun (ht _) 0, congrFun (ht _) 1]
  · rintro ⟨Y, rfl⟩ i
    refine mem_hnf.2 ⟨Y i 0, Y i 1, ?_⟩
    ext j
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The entrywise inclusion $M_2(R) \cong$ `matOrder R K`. -/
def matOrderEquivR : Matrix (Fin 2) (Fin 2) R ≃ₐ[R] matOrder R K :=
  AlgEquiv.ofInjective (AlgHom.mapMatrix (Algebra.ofId R K)) (by
    intro X Y h
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun h i) j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Algebra.ofId_apply] at this
    exact IsFractionRing.injective R K this)

theorem matOrderEquivR_apply (X : Matrix (Fin 2) (Fin 2) R) :
    ((matOrderEquivR (K := K) X : matOrder R K) : Matrix (Fin 2) (Fin 2) K) = X.map (algebraMap R K) := rfl

/-- **Split case:** if $\varphi : D \cong M_2(K)$ maps $\mathcal O$ onto $M_2(R)$, every left ideal $I$ of $\mathcal O$ with $\operatorname{nrd}(I) \ne 0$
is $\mathcal O\alpha$ with $\operatorname{nrd}(\alpha) \ne 0$. -/
theorem exists_eq_rTrans_of_map_eq_matOrder (φ : ℍ[K,a,b] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (O : Subalgebra R ℍ[K,a,b])
    (hφ : O.map ((φ : ℍ[K,a,b] →ₐ[K] _).restrictScalars R) = matOrder R K) (I : Ideal O) (hI : leftNrdIdeal I ≠ ⊥) :
    ∃ α : ℍ[K,a,b], nrd α ≠ 0 ∧ idealSet I = rTrans (O : Set ℍ[K,a,b]) α := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let e1 := (φ.restrictScalars R).subalgebraMap O
  let e2 := Subalgebra.equivOfEq _ _ hφ
  let ψ : O ≃+* Matrix (Fin 2) (Fin 2) R := ((e1.trans e2).trans (matOrderEquivR (K := K)).symm).toRingEquiv
  have hψφ : ∀ x : O, (ψ x).map (algebraMap R K) = φ x := by
    intro x
    rw [← matOrderEquivR_apply]
    change ((matOrderEquivR (K := K) ((matOrderEquivR (K := K)).symm (e2 (e1 x))) : matOrder R K) :
      Matrix (Fin 2) (Fin 2) K) = φ x
    rw [AlgEquiv.apply_symm_apply]; rfl
  have hψ : ∀ x : O, algebraMap R K (ψ x).det = nrd (x : ℍ[K,a,b]) := by
    intro x
    rw [← det_algEquiv φ, ← hψφ, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  set I' := Ideal.comap ψ.symm I
  have hnrd : leftNrdIdeal I = detIdeal (rowSpace I') := by
    rw [leftNrdIdeal_comap ψ (IsFractionRing.injective R K) hψ, matNrdIdeal_eq]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, detIdeal (rowSpace I') = Ideal.span {π ^ k} := by
    rw [← hnrd]
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hπ
    exact ⟨k, hk⟩
  obtain ⟨b', hb', c, hM⟩ := exists_eq_hnf hπ hk
  set P : Matrix (Fin 2) (Fin 2) R := !![π ^ (k - b'), c; 0, π ^ b']
  have hI' : I' = ofRowSpace (hnf π (k - b') b' c) := by rw [← hM, ofRowSpace_rowSpace]
  set α : ℍ[K,a,b] := φ.symm (P.map (algebraMap R K))
  have hdetP : P.det = π ^ k := by
    simp only [P, Matrix.det_fin_two_of]; rw [mul_zero, sub_zero, ← pow_add]; congr 1; omega
  refine ⟨α, ?_, ?_⟩
  · rw [← det_algEquiv φ, AlgEquiv.apply_symm_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdetP]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (pow_ne_zero _ hπ.ne_zero)
  · ext x
    constructor
    · rintro ⟨hxO, hxI⟩
      have h1 : ψ ⟨x, hxO⟩ ∈ I' := by simpa [I'] using hxI
      rw [hI', mem_ofRowSpace_hnf] at h1
      obtain ⟨Y, hY⟩ := h1
      refine ⟨(ψ.symm Y : O), (ψ.symm Y).2, ?_⟩
      apply φ.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, ← hψφ (ψ.symm Y), RingEquiv.apply_symm_apply, ← hψφ ⟨x, hxO⟩, hY,
        Matrix.map_mul]
    · rintro ⟨y, hy, rfl⟩
      set z : O := ψ.symm (ψ ⟨y, hy⟩ * P)
      have hz : y * α = (z : ℍ[K,a,b]) := by
        apply φ.injective
        rw [map_mul, AlgEquiv.apply_symm_apply, ← hψφ z, RingEquiv.apply_symm_apply, Matrix.map_mul, hψφ]
      have hyα : y * α ∈ O := by rw [hz]; exact z.2
      refine ⟨hyα, ?_⟩
      have hz' : (⟨y * α, hyα⟩ : O) = z := Subtype.ext hz
      rw [hz']
      have : ψ z ∈ I' := by
        rw [hI', mem_ofRowSpace_hnf]
        exact ⟨ψ ⟨y, hy⟩, RingEquiv.apply_symm_apply _ _⟩
      simpa [I'] using this

end LocalPrincipal

end QuadFormsKB.QuatOrder
