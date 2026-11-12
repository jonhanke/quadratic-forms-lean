/-
# Discriminants of maximal orders (Voight, Theorem 15.5.5)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Definition 15.2.2 (p. 242),
Lemma 15.2.5, Lemma 15.4.7 (p. 247), Theorem 15.5.5 (p. 249).
-/
import QuadFormsKB.Literature.Voight.Wave2.Statements
import QuadFormsKB.Tamagawa.TernaryLocalNF
import QuadFormsKB.Tamagawa.IdealLocalGlobalNF
import QuadFormsKB.Tamagawa.QuatIdealIndex
import QuadFormsKB.Tamagawa.QuatOrderIdeals
import QuadFormsKB.Tamagawa.LocalRankFive

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain Quaternion

noncomputable section

namespace QuadFormsKB.Voight.Disc

open QuadFormsKB.Quat QuadFormsKB.QuatOrder

/-! ## The discriminant of four quaternions (algebra over a field) -/

section Algebra

variable {K : Type*} [Field K] {a b : K}

/-- **The discriminant of four quaternions** $f_0, \dots, f_3 \in B = (a,b)_K$ (Voight 2021, Definition 15.2.2):
$d(f) = \det(\operatorname{trd}(f_pf_q))_{p,q}$. For $K$ the field of fractions of $\mathbb Z_F$ this is
`MassWave2.trdGramDet`. -/
def gramTrd (f : Fin 4 → ℍ[K,a,b]) : K := (Matrix.of fun p q => trd (f p * f q)).det

theorem trd_add' (x y : ℍ[K,a,b]) : trd (x + y) = trd x + trd y := by simp [trd]; ring

theorem trd_smul' (c : K) (x : ℍ[K,a,b]) : trd (c • x) = c * trd x := by simp [trd]; ring

theorem trd_sum {ι : Type*} (s : Finset ι) (g : ι → ℍ[K,a,b]) : trd (∑ i ∈ s, g i) = ∑ i ∈ s, trd (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [trd]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, trd_add', ih]

/-- **Change of basis** (Voight 2021, Lemma 15.2.5): if $g_q = \sum_p M_{pq} f_p$ then
$d(g) = \det(M)^2\, d(f)$. -/
@[kb "voight2021" "Lemma 15.2.5, p. 242"]
theorem gramTrd_comb (f : Fin 4 → ℍ[K,a,b]) (M : Matrix (Fin 4) (Fin 4) K) :
    gramTrd (fun q => ∑ p, M p q • f p) = M.det ^ 2 * gramTrd f := by
  have h : (Matrix.of fun p q => trd ((∑ r, M r p • f r) * (∑ s, M s q • f s))) =
      M.transpose * (Matrix.of fun p q => trd (f p * f q)) * M := by
    ext p q
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum,
      trd_sum, smul_mul_smul_comm, trd_smul']
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [gramTrd, h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, gramTrd]
  ring

theorem basisOneIJK_apply_eq (n : Fin 4) :
    (QuaternionAlgebra.basisOneIJK a 0 b n : ℍ[K,a,b]) =
      ⟨(Pi.single n (1 : K) : Fin 4 → K) 0, (Pi.single n (1 : K) : Fin 4 → K) 1,
        (Pi.single n (1 : K) : Fin 4 → K) 2, (Pi.single n (1 : K) : Fin 4 → K) 3⟩ := by
  rw [QuaternionAlgebra.basisOneIJK, Module.Basis.coe_ofEquivFun]; rfl

/-- The discriminant of the standard basis $1, i, j, k$: $d = 2 \cdot 2a \cdot 2b \cdot (-2ab) = -16a^2b^2$. -/
theorem gramTrd_basisOneIJK :
    gramTrd (fun q => QuaternionAlgebra.basisOneIJK a 0 b q) = -16 * a ^ 2 * b ^ 2 := by
  have h : (Matrix.of fun p q => trd ((QuaternionAlgebra.basisOneIJK a 0 b p : ℍ[K,a,b]) *
      QuaternionAlgebra.basisOneIJK a 0 b q)) = Matrix.diagonal ![2, 2 * a, 2 * b, -(2 * a * b)] := by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [basisOneIJK_apply_eq, trd, Matrix.diagonal]; ring
  rw [gramTrd, h, Matrix.det_diagonal, Fin.prod_univ_four]
  simp only [Matrix.cons_val]
  ring

/-- **The trace form is nondegenerate** when $2ab \ne 0$: the discriminant of every basis of $B$ is nonzero. -/
theorem gramTrd_ne_zero (h2ab : (2 : K) * a * b ≠ 0) (f : Module.Basis (Fin 4) K ℍ[K,a,b]) :
    gramTrd (fun q => f q) ≠ 0 := by
  set e := QuaternionAlgebra.basisOneIJK a 0 b
  have hf : (fun q => f q) = fun q => ∑ p, (e.toMatrix f) p q • e p := by
    funext q
    simp only [Module.Basis.toMatrix_apply]
    exact (e.sum_repr (f q)).symm
  rw [hf, gramTrd_comb, gramTrd_basisOneIJK]
  have hdet : (e.toMatrix f).det ≠ 0 := by
    have := Module.Basis.toMatrix_mul_toMatrix_flip e f
    intro h0
    have h1 := congrArg Matrix.det this
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have ha : a ≠ 0 := fun h => h2ab (by rw [h]; ring)
  have hb : b ≠ 0 := fun h => h2ab (by rw [h]; ring)
  have h2 : (2 : K) ≠ 0 := fun h => h2ab (by rw [h]; ring)
  have h16 : (16 : K) ≠ 0 := by
    have : (16 : K) = 2 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero _ h2
  exact mul_ne_zero (pow_ne_zero _ hdet) (by
    rw [neg_mul, neg_mul, neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero h16 (pow_ne_zero _ ha)) (pow_ne_zero _ hb))

/-- **The determinant of left multiplication** by $x$ on $B$ is $\operatorname{nrd}(x)^2$. -/
theorem det_mulLeft (x : ℍ[K,a,b]) : LinearMap.det (LinearMap.mulLeft K x) = nrd x ^ 2 := by
  have h : LinearMap.toMatrix (QuaternionAlgebra.basisOneIJK a 0 b) (QuaternionAlgebra.basisOneIJK a 0 b)
      (LinearMap.mulLeft K x) =
      !![x.re, a * x.imI, b * x.imJ, -(a * b * x.imK);
         x.imI, x.re, b * x.imK, -(b * x.imJ);
         x.imJ, -(a * x.imK), x.re, a * x.imI;
         x.imK, -x.imJ, x.imI, x.re] := by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [LinearMap.toMatrix_apply, basisOneIJK_apply_eq]
  rw [← LinearMap.det_toMatrix (QuaternionAlgebra.basisOneIJK a 0 b), h, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove, nrd]
  ring

end Algebra

/-! ## Unimodularity modulo the maximal ideal -/

section Residue

open IsLocalRing

/-- **A Gram matrix that is nondegenerate modulo $\mathfrak m$ has unit determinant**: over a local ring $R$, if
$\sum_p c_p g_{pq} \in \mathfrak m$ for all $q$ forces every $c_p \in \mathfrak m$, then $\det g \in R^\times$. -/
theorem isUnit_det_of_nondeg {R : Type*} [CommRing R] [IsLocalRing R] (g : Matrix (Fin 4) (Fin 4) R)
    (h : ∀ c : Fin 4 → R, (∀ q, ∑ p, c p * g p q ∈ maximalIdeal R) → ∀ p, c p ∈ maximalIdeal R) :
    IsUnit g.det := by
  by_contra hdet
  have h0 : (g.map (residue R)).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, residue_eq_zero_iff, mem_maximalIdeal,
      mem_nonunits_iff]
    exact hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  choose c hc using fun p => residue_surjective (R := R) (w p)
  have hall := h c fun q => by
    rw [← residue_eq_zero_iff, map_sum]
    have := congrFun hw q
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Pi.zero_apply] at this
    simpa [hc] using this
  apply hw0
  funext p
  rw [← hc p, Pi.zero_apply, residue_eq_zero_iff]
  exact hall p

end Residue

/-! ## The discriminant of a local order from a twisted trace pairing -/

section LocalGram

open IsLocalRing IsLocalization

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] {a b : K}

theorem trd_mul_sum (x : ℍ[K,a,b]) (c : Fin 4 → K) (f : Fin 4 → ℍ[K,a,b]) (w : ℍ[K,a,b]) :
    trd (x * (∑ q, c q • f q) * w) = ∑ q, c q * trd (x * f q * w) := by
  rw [Finset.mul_sum, Finset.sum_mul, trd_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, trd_smul']

theorem trd_sum_mul (z : ℍ[K,a,b]) (c : Fin 4 → K) (f : Fin 4 → ℍ[K,a,b]) (w : ℍ[K,a,b]) :
    trd ((∑ p, c p • f p) * z * w) = ∑ p, c p * trd (f p * z * w) := by
  rw [Finset.sum_mul, Finset.sum_mul, trd_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [smul_mul_assoc, smul_mul_assoc, trd_smul']

/-- The Gram matrix of $(x, z) \mapsto \operatorname{trd}(xzw)$ is the trace Gram matrix times the matrix of $z \mapsto zw$;
so its determinant is $d(f)\operatorname{nrd}(w)^2$. -/
theorem det_twisted (f : Module.Basis (Fin 4) K ℍ[K,a,b]) (w : ℍ[K,a,b]) :
    (Matrix.of fun p q => trd (f p * f q * w)).det = gramTrd (fun q => f q) * nrd w ^ 2 := by
  set M := LinearMap.toMatrix f f (LinearMap.mulRight K w)
  have hM : ∀ q, f q * w = ∑ r, M r q • f r := fun q => by
    simp only [M, LinearMap.toMatrix_apply, LinearMap.mulRight_apply]
    exact (f.sum_repr (f q * w)).symm
  have h : (Matrix.of fun p q => trd (f p * f q * w)) = (Matrix.of fun p q => trd (f p * f q)) * M := by
    ext p q
    rw [Matrix.of_apply, Matrix.mul_apply, mul_assoc, hM q, Finset.mul_sum, trd_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_smul_comm, trd_smul', Matrix.of_apply, mul_comm]
  rw [h, Matrix.det_mul, gramTrd, LinearMap.det_toMatrix, QuadFormsKB.QuatOrder.det_mulRight]

variable (O : Subalgebra R ℍ[K,a,b]) (f : Module.Basis (Fin 4) K ℍ[K,a,b])
  (hmem : ∀ x, x ∈ O ↔ ∀ i, IsInteger R (f.repr x i)) {π : R} (hπ : Irreducible π)

include hmem in
theorem basis_mem (i : Fin 4) : f i ∈ O := by
  rw [hmem]
  intro j
  rw [Module.Basis.repr_self]
  by_cases h : i = j
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h]⟩

include hmem hπ in
/-- **Local unimodularity criterion.** Let $f$ be a $K$-basis of $D$ such that $\mathcal O$ consists of the elements with
coordinates in $R$, and $w \in D$. If $\operatorname{trd}(xzw) \in R$ for $x, z \in \mathcal O$, and $x \in \mathcal O$ with
$\operatorname{trd}(xzw) \in \pi R$ for all $z \in \mathcal O$ lies in $\pi\mathcal O$, then $d(f)\operatorname{nrd}(w)^2 \in R^\times$. -/
theorem exists_unit_gramTrd_mul (w : ℍ[K,a,b])
    (hint : ∀ x ∈ O, ∀ z ∈ O, IsInteger R (trd (x * z * w)))
    (hnd : ∀ x ∈ O, (∀ z ∈ O, ∃ r : R, trd (x * z * w) = algebraMap R K (π * r)) →
      ∃ x' ∈ O, x = algebraMap R K π • x') :
    ∃ u : Rˣ, gramTrd (fun q => f q) * nrd w ^ 2 = algebraMap R K u := by
  have hb := basis_mem O f hmem
  choose g hg using fun p q => hint _ (hb p) _ (hb q)
  have hG : (Matrix.of fun p q => trd (f p * f q * w)) = (Matrix.of g).map (algebraMap R K) := by
    ext p q; simp [hg]
  have hunit : IsUnit (Matrix.of g).det := by
    refine isUnit_det_of_nondeg _ fun c hc => ?_
    rw [hπ.maximalIdeal_eq] at hc ⊢
    set x : ℍ[K,a,b] := ∑ p, algebraMap R K (c p) • f p
    have hxr : ∀ i, f.repr x i = algebraMap R K (c i) := fun i => by
      simp only [x, map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [Finset.sum_apply']
      simp [Finsupp.single_apply]
    have hxO : x ∈ O := (hmem x).2 fun i => ⟨c i, (hxr i).symm⟩
    obtain ⟨x', hx'O, hxx'⟩ := hnd x hxO fun z hz => by
      have hz' := (hmem z).1 hz
      choose d hd using hz'
      have hzs : z = ∑ q, algebraMap R K (d q) • f q := by
        conv_lhs => rw [← f.sum_repr z]
        exact Finset.sum_congr rfl fun q _ => by rw [hd q]
      have hcq : ∀ q, ∃ s, ∑ p, c p * g p q = π * s := fun q => by
        obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (hc q)
        exact ⟨s, by rw [mul_comm π, hs]; rfl⟩
      choose s hs using hcq
      refine ⟨∑ q, d q * s q, ?_⟩
      rw [hzs, trd_mul_sum]
      simp only [x, trd_sum_mul, Finset.mul_sum, map_sum, map_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      have := congrArg (algebraMap R K) (hs q)
      simp only [map_sum, map_mul] at this
      rw [← mul_assoc, mul_comm (algebraMap R K π), mul_assoc, ← this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← hg]
    intro p
    obtain ⟨t, ht⟩ := (hmem x').1 hx'O p
    have h1 := hxr p
    rw [hxx', map_smul, Finsupp.smul_apply, smul_eq_mul, ← ht, ← map_mul] at h1
    exact Ideal.mem_span_singleton'.2 ⟨t, by rw [mul_comm]; exact IsFractionRing.injective R K h1⟩
  obtain ⟨u, hu⟩ := hunit
  refine ⟨u, ?_⟩
  rw [← det_twisted, hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← hu]

end LocalGram


/-! ## Split places: $\mathcal O \cong \mathrm M_2(R)$ -/

section Split

open IsLocalRing IsLocalization

variable {K : Type*} [Field K] {a b : K}

theorem nrd_one_add (x : ℍ[K,a,b]) : nrd (1 + x) = 1 + trd x + nrd x := by
  simp [nrd, trd]; ring

/-- **The reduced trace is the matrix trace** under an isomorphism $B \cong \mathrm M_2(K)$. -/
theorem trace_algEquiv (φ : ℍ[K,a,b] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (x : ℍ[K,a,b]) :
    (φ x).trace = trd x := by
  have h1 := det_algEquiv φ (1 + x)
  have h2 := det_algEquiv φ x
  rw [map_add, map_one, nrd_one_add] at h1
  rw [Matrix.det_fin_two] at h1 h2
  rw [Matrix.trace_fin_two]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at h1
  linear_combination h1 - h2

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R K] [IsFractionRing R K]
  (O : Subalgebra R ℍ[K,a,b]) (f : Module.Basis (Fin 4) K ℍ[K,a,b])
  (hmem : ∀ x, x ∈ O ↔ ∀ i, IsInteger R (f.repr x i)) {π : R} (hπ : Irreducible π)

theorem mem_iff_of_map_eq (φ : ℍ[K,a,b] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K)
    (hφ : O.map ((φ : ℍ[K,a,b] →ₐ[K] _).restrictScalars R) = matOrder R K) (x : ℍ[K,a,b]) :
    x ∈ O ↔ ∀ i j, IsInteger R (φ x i j) := by
  rw [← mem_matOrder, ← hφ]
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨x', hx', hxx'⟩
    have : x' = x := φ.injective hxx'
    exact this ▸ hx'

include hmem hπ in
/-- **The discriminant at a split place is a unit** (Voight 2021, Lemma 15.5.3 and Example 15.2.4): if
$\varphi(\mathcal O) = \mathrm M_2(R)$ for an isomorphism $\varphi : B \cong \mathrm M_2(K)$, every $R$-basis of $\mathcal O$ has
discriminant in $R^\times$. -/
@[kb "voight2021" "Lemma 15.5.3, p. 248"]
theorem exists_unit_gramTrd_split (φ : ℍ[K,a,b] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K)
    (hφ : O.map ((φ : ℍ[K,a,b] →ₐ[K] _).restrictScalars R) = matOrder R K) :
    ∃ u : Rˣ, gramTrd (fun q => f q) = algebraMap R K u := by
  have hm := mem_iff_of_map_eq O φ hφ
  obtain ⟨u, hu⟩ := exists_unit_gramTrd_mul O f hmem hπ 1 (fun x hx z hz => by
      rw [mul_one, ← trace_algEquiv φ, Matrix.trace_fin_two]
      have := (hm _).1 (O.mul_mem hx hz)
      obtain ⟨p, hp⟩ := this 0 0
      obtain ⟨q, hq⟩ := this 1 1
      exact ⟨p + q, by rw [map_add, hp, hq]⟩)
    (fun x hx H => by
      have hX := (hm x).1 hx
      have hent : ∀ i j, ∃ r : R, φ x i j = algebraMap R K (π * r) := fun i j => by
        have hz : φ.symm (Matrix.single j i 1) ∈ O := by
          rw [hm]
          intro p q
          rw [AlgEquiv.apply_symm_apply]
          by_cases h : j = p ∧ i = q
          · obtain ⟨rfl, rfl⟩ := h; exact ⟨1, by simp⟩
          · exact ⟨0, by rw [Matrix.single_apply, ite_eq_right_iff.2 (fun h' => absurd h' h), map_zero]⟩
        obtain ⟨r, hr⟩ := H _ hz
        refine ⟨r, ?_⟩
        rw [mul_one, ← trace_algEquiv φ, map_mul, AlgEquiv.apply_symm_apply, Matrix.trace_mul_single] at hr
        simpa using hr
      choose r hr using hent
      refine ⟨φ.symm (Matrix.of fun i j => algebraMap R K (r i j)), ?_, ?_⟩
      · rw [hm, AlgEquiv.apply_symm_apply]
        intro i j; exact ⟨r i j, rfl⟩
      · apply φ.injective
        rw [map_smul, AlgEquiv.apply_symm_apply]
        ext i j
        rw [hr, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, map_mul])
  exact ⟨u, by simpa using hu⟩

end Split

/-! ## Ramified places: the valuation ring of a division algebra -/

section Ramified

open IsLocalRing IsLocalization Polynomial

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {a b : K}

theorem nrd_sub_algebraMap (x : ℍ[K,a,b]) (c : K) :
    nrd (x - algebraMap K ℍ[K,a,b] c) = nrd x - c * trd x + c ^ 2 := by
  simp [nrd, trd, QuaternionAlgebra.algebraMap_eq]; ring

omit [IsDiscreteValuationRing R] in
/-- **Reduced norm in $\mathfrak m$ forces reduced trace in $\mathfrak m$** in a quaternion division algebra over a Henselian
discrete valuation ring (Hensel's lemma for $X^2 - X + \operatorname{nrd}(x)/\operatorname{trd}(x)^2$). -/
theorem trd_mem_of_nrd_mem [ValuationRing R] (hdiv : ∀ x : ℍ[K,a,b], nrd x = 0 → x = 0) {x : ℍ[K,a,b]} {m : R}
    (hm : m ∈ maximalIdeal R) (hx : nrd x = algebraMap R K m) :
    ∃ τ ∈ maximalIdeal R, trd x = algebraMap R K τ := by
  obtain ⟨τ, hτ⟩ := QuadFormsKB.QuatOrder.isInteger_trd_of_nrd (R := R) hdiv ⟨m, hx.symm⟩
  refine ⟨τ, ?_, hτ.symm⟩
  by_contra hτm
  have hτu : IsUnit τ := by
    by_contra h; exact hτm ((mem_maximalIdeal _).2 h)
  obtain ⟨u, rfl⟩ := hτu
  set c : R := m * ((u⁻¹ : Rˣ) : R) ^ 2 with hc
  have hcm : c ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hm
  set f : R[X] := X ^ 2 - X + C c with hf
  have hfm : f.Monic := by
    rw [hf, sub_eq_add_neg]
    refine ((monic_X_pow 2).add_of_left ?_).add_of_left ?_
    · rw [degree_neg, degree_X, degree_X_pow]; norm_num
    · refine lt_of_le_of_lt degree_C_le ?_
      rw [degree_add_eq_left_of_degree_lt (by rw [degree_neg, degree_X, degree_X_pow]; norm_num), degree_X_pow]
      norm_num
  obtain ⟨e, he, -⟩ := HenselianLocalRing.is_henselian f hfm 0 (by simpa [hf] using hcm) (by simp [hf])
  have he' : e ^ 2 - e + c = 0 := by simpa [hf] using he.eq_zero
  -- $x' = u^{-1}x$ has trace $1$ and norm $c$
  set x' : ℍ[K,a,b] := algebraMap R K ((u⁻¹ : Rˣ) : R) • x
  have hu' : algebraMap R K ((u⁻¹ : Rˣ) : R) * algebraMap R K (u : R) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have ht' : trd x' = 1 := by rw [trd_smul', ← hτ, hu']
  have hn' : nrd x' = algebraMap R K c := by rw [nrd_smul, hx, hc, map_mul, map_pow]; ring
  have hprod : (x' - algebraMap K ℍ[K,a,b] (algebraMap R K e)) *
      (x' - algebraMap K ℍ[K,a,b] (1 - algebraMap R K e)) = 0 := by
    rw [QuadFormsKB.QuatOrder.sub_mul_sub_algebraMap, add_sub_cancel, mul_self_eq x', ht', hn', one_smul]
    have : algebraMap R K e * (1 - algebraMap R K e) = algebraMap R K c := by
      have := congrArg (algebraMap R K) he'
      simp only [map_add, map_sub, map_pow, map_zero] at this
      linear_combination -this
    rw [this, map_one, one_mul]; abel
  have hsc : ∀ e' : R, x' = algebraMap K ℍ[K,a,b] (algebraMap R K e') → False := by
    intro e' h
    have h1 : trd x' = 2 * algebraMap R K e' := by rw [h]; simp [trd, QuaternionAlgebra.algebraMap_eq]
    have h2 : nrd x' = algebraMap R K e' ^ 2 := by rw [h]; simp [nrd, QuaternionAlgebra.algebraMap_eq]
    rw [ht'] at h1
    rw [hn', ← map_pow] at h2
    have hc' : e' ^ 2 ∈ maximalIdeal R := IsFractionRing.injective R K h2 ▸ hcm
    have he'm : e' ∈ maximalIdeal R := (maximalIdeal.isMaximal R).isPrime.mem_of_pow_mem 2 hc'
    have h1' : (1 : R) = 2 * e' := IsFractionRing.injective R K (by rw [map_one, map_mul, map_ofNat]; exact h1)
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 (h1' ▸ Ideal.mul_mem_left _ _ he'm))
  have h0 := congrArg nrd hprod
  rw [nrd_mul, show nrd (0 : ℍ[K,a,b]) = 0 by simp [nrd]] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · exact hsc e (sub_eq_zero.1 (hdiv _ h))
  · exact hsc (1 - e) (by rw [map_sub, map_one]; exact sub_eq_zero.1 (hdiv _ h))

end Ramified

section RamifiedOrder

open IsLocalRing IsLocalization

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {a b : K}
  (O : Subalgebra R ℍ[K,a,b]) (hO : ∀ x, x ∈ O ↔ IsInteger R (nrd x)) {π : R} (hπ : Irreducible π)
  {y : ℍ[K,a,b]} (hy : nrd y = algebraMap R K π)

/-- $y^{-1} = \pi^{-1}\bar y$ when $\operatorname{nrd} y = \pi$. -/
abbrev yInv (π : R) (y : ℍ[K,a,b]) : ℍ[K,a,b] := (algebraMap R K π)⁻¹ • star y

include hy hπ in
theorem yInv_mul : yInv π y * y = 1 := by
  have hπ0 : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero
  rw [yInv, smul_mul_assoc, star_mul_eq_nrd, hy, ← QuaternionAlgebra.coe_smul, smul_eq_mul,
    inv_mul_cancel₀ hπ0]; rfl

include hy hπ in
theorem mul_yInv : y * yInv π y = 1 := by
  have hπ0 : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero
  rw [yInv, mul_smul_comm, mul_star_eq_nrd, hy, ← QuaternionAlgebra.coe_smul, smul_eq_mul,
    inv_mul_cancel₀ hπ0]; rfl

include hy hπ in
theorem nrd_yInv : nrd (yInv π y) = (algebraMap R K π)⁻¹ := by
  have hπ0 : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero
  rw [yInv, nrd_smul, nrd_star, hy]; field_simp

include hO hπ hy in
/-- **Division by the uniformizer $y$**: every $x \in \mathcal O$ is $s + wy$ with $s \in R$, $w \in \mathcal O$, provided
every element of $\mathcal O$ has reduced trace in $\mathfrak m$ and $\mathfrak m \ni 2$ and residues are squares. -/
theorem exists_eq_add_mul_y (htr : ∀ t ∈ O, ∃ r : R, trd t = algebraMap R K (π * r)) (h2 : (2 : R) ∈ Ideal.span {π})
    (hsq : ∀ n : R, ∃ s : R, n - s ^ 2 ∈ Ideal.span {π}) {x : ℍ[K,a,b]} (hx : x ∈ O) :
    ∃ s : R, ∃ w ∈ O, x = algebraMap R ℍ[K,a,b] s + w * y := by
  obtain ⟨n, hn⟩ := (hO x).1 hx
  obtain ⟨s, hs⟩ := hsq n
  obtain ⟨r1, hr1⟩ := htr x hx
  set x1 := x - algebraMap R ℍ[K,a,b] s
  have hn1 : nrd x1 = algebraMap R K (n - s * (π * r1) + s ^ 2) := by
    have hx1 : x1 = x - algebraMap K ℍ[K,a,b] (algebraMap R K s) := by
      simp only [x1, ← IsScalarTower.algebraMap_apply]
    rw [hx1, nrd_sub_algebraMap, ← hn, hr1]
    simp only [map_add, map_sub, map_mul, map_pow]
  have hmem : n - s * (π * r1) + s ^ 2 ∈ Ideal.span {π} := by
    have : n - s * (π * r1) + s ^ 2 = (n - s ^ 2) + 2 * s ^ 2 - π * (s * r1) := by ring
    rw [this]
    refine Ideal.sub_mem _ (Ideal.add_mem _ hs (Ideal.mul_mem_right _ _ h2)) (Ideal.mul_mem_right _ _ ?_)
    exact Ideal.mem_span_singleton_self π
  obtain ⟨m1, hm1⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨s, x1 * yInv π y, ?_, ?_⟩
  · rw [hO]
    refine ⟨m1, ?_⟩
    rw [nrd_mul, nrd_yInv hπ hy, hn1, ← hm1, map_mul]
    have hπ0 : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero
    field_simp
  · rw [mul_assoc, yInv_mul hπ hy, mul_one]; simp [x1]

include hO hπ hy in
/-- **$\mathcal O$ has an element of unit reduced trace** (Voight 2021, the unramified quadratic subfield of
Theorem 13.3.11): if $D$ is a division algebra over a Henselian discrete valuation ring with finite residue field, its
valuation ring $\mathcal O$ is an order and $\operatorname{nrd}(y) = \pi$ is a uniformizer, then some $t \in \mathcal O$ has
$\operatorname{trd}(t) \notin \mathfrak m$. (If $2 \in \mathfrak m$ and all traces were in $\mathfrak m$, every residue being a
square would give $\mathcal O = R + Ry + \pi\mathcal O$, so $\mathcal O = R + Ry$ by Nakayama, of rank $\le 2$.) -/
theorem exists_trd_not_mem [Finite (ResidueField R)] (hfg : (Subalgebra.toSubmodule O).FG)
    (hspan : Submodule.span K (O : Set ℍ[K,a,b]) = ⊤) :
    ∃ t ∈ O, ∀ r : R, trd t ≠ algebraMap R K (π * r) := by
  by_contra hall
  push Not at hall
  have h2 : (2 : R) ∈ Ideal.span {π} := by
    obtain ⟨r, hr⟩ := hall 1 O.one_mem
    have : trd (1 : ℍ[K,a,b]) = 2 := by simp [trd]
    rw [this, ← map_ofNat (algebraMap R K) 2] at hr
    exact Ideal.mem_span_singleton'.2 ⟨r, by rw [mul_comm]; exact (IsFractionRing.injective R K hr).symm⟩
  have hmax : maximalIdeal R = Ideal.span {π} := hπ.maximalIdeal_eq
  have hsq : ∀ n : R, ∃ s : R, n - s ^ 2 ∈ Ideal.span {π} := by
    intro n
    have h2k : (2 : ResidueField R) = 0 := by
      rw [← map_ofNat (residue R) 2, residue_eq_zero_iff, hmax]; exact h2
    have : CharP (ResidueField R) 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2k
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq (ResidueField R) 2) (residue R n)
    obtain ⟨s, rfl⟩ := residue_surjective r
    refine ⟨s, ?_⟩
    rw [← hmax, ← residue_eq_zero_iff, map_sub, hr, map_pow, sub_eq_zero, pow_two]
  set N : Submodule R ℍ[K,a,b] := Submodule.span R (Set.range ![1, y])
  have hle : Subalgebra.toSubmodule O ≤ N ⊔ maximalIdeal R • Subalgebra.toSubmodule O := by
    intro x hx
    obtain ⟨s, w, hw, rfl⟩ := exists_eq_add_mul_y O hO hπ hy hall h2 hsq hx
    obtain ⟨s', w', hw', rfl⟩ := exists_eq_add_mul_y O hO hπ hy hall h2 hsq hw
    have hπ0 : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero
    set u0 : ℍ[K,a,b] := (algebraMap R K π)⁻¹ • (y * y)
    have hu0 : u0 ∈ O := by
      rw [hO]; refine ⟨1, ?_⟩
      rw [nrd_smul, nrd_mul, hy, map_one]; field_simp
    have hyy : y * y = π • u0 := by
      rw [← algebraMap_smul K π u0, smul_smul, mul_inv_cancel₀ hπ0, one_smul]
    have : algebraMap R ℍ[K,a,b] s + (algebraMap R ℍ[K,a,b] s' + w' * y) * y =
        (s • (1 : ℍ[K,a,b]) + s' • y) + π • (w' * u0) := by
      rw [add_mul, mul_assoc, hyy, mul_smul_comm, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, add_assoc]
    rw [this]
    refine Submodule.add_mem_sup (N.add_mem (N.smul_mem _ (Submodule.subset_span ⟨0, rfl⟩))
      (N.smul_mem _ (Submodule.subset_span ⟨1, rfl⟩))) ?_
    exact Submodule.smul_mem_smul (hmax ▸ Ideal.mem_span_singleton_self π) (O.mul_mem hw' hu0)
  have hON := Submodule.le_of_le_smul_of_le_jacobson_bot hfg
    (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]) hle
  have htop : (⊤ : Submodule K ℍ[K,a,b]) ≤ Submodule.span K (Set.range ![1, y]) := by
    rw [← hspan, ← Submodule.span_span_of_tower R K (Set.range ![1, y])]
    exact Submodule.span_mono hON
  have h4 := Submodule.finrank_mono htop
  rw [finrank_top, QuaternionAlgebra.finrank_eq_four] at h4
  have h5 := finrank_range_le_card (R := K) ![(1 : ℍ[K,a,b]), y]
  rw [Fintype.card_fin] at h5
  change Module.finrank K (Submodule.span K _) ≤ 2 at h5
  omega

include hO hπ hy in
/-- **The discriminant at a ramified place** (Voight 2021, Theorem 15.5.5, ramified case; cf. Theorem 13.3.11): let $R$ be a
Henselian discrete valuation ring with finite residue field and uniformizer $\pi$, $D = (a,b)_K$ a division algebra,
$\mathcal O = \{x : \operatorname{nrd}x \in R\}$ its valuation ring, an order, and $y \in D$ with $\operatorname{nrd}y = \pi$. Then every
$K$-basis $f$ of $D$ that is an $R$-basis of $\mathcal O$ has $d(f) \in \pi^2R^\times$: $\operatorname{disc}\mathcal O = \mathfrak p^2$,
$\operatorname{discrd}\mathcal O = \mathfrak p$. The proof: the pairing $(x,z) \mapsto \operatorname{trd}(xzy^{-1})$ is integral and
unimodular on $\mathcal O$ (`exists_unit_gramTrd_mul`), and its Gram determinant is $d(f)\,\pi^{-2}$. -/
@[kb "voight2021" "Theorem 15.5.5, p. 249"]
theorem exists_unit_gramTrd_ramified [Finite (ResidueField R)] (hdiv : ∀ x : ℍ[K,a,b], nrd x = 0 → x = 0)
    (hfg : (Subalgebra.toSubmodule O).FG) (hspan : Submodule.span K (O : Set ℍ[K,a,b]) = ⊤)
    (f : Module.Basis (Fin 4) K ℍ[K,a,b]) (hmem : ∀ x, x ∈ O ↔ ∀ i, IsInteger R (f.repr x i)) :
    ∃ u : Rˣ, gramTrd (fun q => f q) = algebraMap R K (π ^ 2 * u) := by
  have hπ0 : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero
  obtain ⟨t, htO, ht⟩ := exists_trd_not_mem O hO hπ hy hfg hspan
  have hmax : maximalIdeal R = Ideal.span {π} := hπ.maximalIdeal_eq
  obtain ⟨u, hu⟩ := exists_unit_gramTrd_mul O f hmem hπ (yInv π y)
    (fun x hx z hz => by
      have hxz := O.mul_mem hx hz
      obtain ⟨n, hn⟩ := (hO _).1 hxz
      obtain ⟨τ, hτ, hτx⟩ := trd_mem_of_nrd_mem (R := R) hdiv (m := n * π) (Ideal.mul_mem_left _ _
        (hmax ▸ Ideal.mem_span_singleton_self π)) (x := x * z * star y)
        (by rw [nrd_mul, nrd_star, hy, ← hn, map_mul])
      rw [hmax] at hτ
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hτ
      refine ⟨r, ?_⟩
      rw [yInv, mul_smul_comm, trd_smul', hτx, map_mul]
      field_simp)
    (fun x hx H => by
      refine ⟨(algebraMap R K π)⁻¹ • x, ?_, by rw [smul_smul, mul_inv_cancel₀ hπ0, one_smul]⟩
      by_contra hx'
      rw [hO, nrd_smul] at hx'
      obtain ⟨n, hn⟩ := (hO x).1 hx
      have hn0 : algebraMap R K n ≠ 0 := by
        intro h0; apply hx'; rw [← hn, h0, mul_zero]; exact ⟨0, map_zero _⟩
      -- $\pi/\operatorname{nrd}x \in R$
      have hc : IsInteger R (algebraMap R K π / algebraMap R K n) := by
        rcases ValuationRing.isInteger_or_isInteger R (algebraMap R K π / algebraMap R K n) with h | h
        · exact h
        · obtain ⟨r, hr⟩ := h
          rw [inv_div] at hr
          by_cases hru : IsUnit r
          · obtain ⟨w, rfl⟩ := hru
            refine ⟨((w⁻¹ : Rˣ) : R), ?_⟩
            rw [← inv_div, ← hr, map_units_inv]
          · exfalso
            have hrm : r ∈ Ideal.span {π} := hmax ▸ (mem_maximalIdeal _).2 hru
            obtain ⟨r', rfl⟩ := Ideal.mem_span_singleton'.1 hrm
            apply hx'
            refine ⟨r', ?_⟩
            rw [← hn, inv_pow, ← div_eq_inv_mul, pow_two, ← div_div, ← hr, map_mul]
            field_simp
      set xinv : ℍ[K,a,b] := (nrd x)⁻¹ • star x
      have hxx : x * xinv = 1 := by
        rw [mul_smul_comm, mul_star_eq_nrd, ← QuaternionAlgebra.coe_smul, smul_eq_mul, ← hn,
          inv_mul_cancel₀ hn0]; rfl
      set z := xinv * t * y
      have hz : z ∈ O := by
        rw [hO]
        obtain ⟨m, hm⟩ := (hO t).1 htO
        obtain ⟨c, hcc⟩ := hc
        refine ⟨c * m, ?_⟩
        rw [nrd_mul, nrd_mul, nrd_smul, nrd_star, hy, map_mul, hcc, hm, ← hn]
        field_simp
      obtain ⟨r, hr⟩ := H z hz
      have : x * z * yInv π y = t := by
        simp only [z]
        rw [← mul_assoc, ← mul_assoc, hxx, one_mul, mul_assoc, mul_yInv hπ hy, mul_one]
      rw [this] at hr
      exact ht r hr)
  refine ⟨u, ?_⟩
  rw [nrd_yInv hπ hy] at hu
  rw [map_mul, ← hu, map_pow]
  field_simp

end RamifiedOrder

/-! ## The global discriminant of a maximal order -/

section Global

open IsLocalRing IsLocalization QuadFormsKB.LocalDensity.NF QuadFormsKB.Quat QuadFormsKB.Voight.MassWave2

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}


theorem mem_ramFin_iff (ha : a ≠ 0) (hb : b ≠ 0) {v : HeightOneSpectrum (𝓞 F)} :
    v ∈ ramFin ha hb ↔ IsRamifiedAt (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b) (NFPlace.finite v) := by
  simp [ramFin]

theorem trd_complHom (v : HeightOneSpectrum (𝓞 F)) (x : QuatF F a b) :
    trd (complHom v a b x) = algebraMap F (v.adicCompletion F) (trd x) := by
  rw [trd, trd, map_mul, map_ofNat]; rfl

instance finite_residueField_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    Finite (ResidueField (v.adicCompletionIntegers F)) := by
  have h := card_quot_π_pow v 1
  rw [pow_one, pow_one, ← (irreducible_π v).maximalIdeal_eq] at h
  have hN : Ideal.absNorm v.asIdeal ≠ 0 :=
    (Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr (mem_nonZeroDivisors_of_ne_zero v.ne_bot)
  exact Nat.finite_of_card_ne_zero (h ▸ hN : Nat.card (ResidueField (v.adicCompletionIntegers F)) ≠ 0)

/-- The integral trace Gram matrix of an $\mathbb Z_F$-basis of an order. -/
theorem exists_int_gram {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O)
    (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) :
    ∃ g : Matrix (Fin 4) (Fin 4) (𝓞 F), ∀ p q,
      algebraMap (𝓞 F) F (g p q) = trd ((e p : QuatF F a b) * (e q : QuatF F a b)) := by
  choose g hg using fun p q => (isInteger_trd_nrd hO (O.mul_mem (e p).2 (e q).2)).1
  exact ⟨Matrix.of g, hg⟩

open Classical in
/-- **The local discriminant of a maximal order** (Voight 2021, Theorem 15.5.5, "only if"; Lemma 15.5.3 at split places):
for a maximal $\mathbb Z_F$-order $\mathcal O$ with $\mathbb Z_F$-basis $e$ and integral trace Gram matrix $g$, at every finite place
$v$, $\iota_v(\det g) = \varpi_v^{2\epsilon_v}u$ with $u \in \mathfrak o_v^\times$, $\epsilon_v = 1$ if $v \in \operatorname{Ram}_f B$ and $0$
otherwise. Number field of any class number; dyadic places included. -/
theorem local_disc (ha : a ≠ 0) (hb : b ≠ 0) {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsMaximalOrder (𝓞 F) F O)
    (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) (g : Matrix (Fin 4) (Fin 4) (𝓞 F))
    (hg : ∀ p q, algebraMap (𝓞 F) F (g p q) = trd ((e p : QuatF F a b) * (e q : QuatF F a b)))
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ u : (v.adicCompletionIntegers F)ˣ, ι v g.det = π v ^ (if v ∈ ramFin ha hb then 2 else 0) * u := by
  classical
  set f := complBasis (v := v) e hO.1
  have hmem := mem_localOrder_iff (v := v) e hO.1
  have hgram : gramTrd (fun q => f q) = algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v g.det) := by
    have : (Matrix.of fun p q => trd (f p * f q)) =
        g.map (((algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)).comp (ι v))) := by
      ext p q
      simp only [Matrix.of_apply, Matrix.map_apply, f, complBasis_apply, complBasisVec, ← map_mul,
        trd_complHom, ← hg, RingHom.comp_apply]
      rfl
    rw [gramTrd, this, ← RingHom.mapMatrix_apply, ← RingHom.map_det, RingHom.comp_apply]
  have hinj : Function.Injective (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) := IsFractionRing.injective _ _
  rcases localOrder_ramified_or_split_nf (v := v) ha hb hO with ⟨hdiv, heq⟩ | ⟨φ, hφ⟩
  · have hram : v ∈ ramFin ha hb := (mem_ramFin_iff ha hb).2 (Gen.isRamifiedAt_finite_iff.2 hdiv)
    have hπ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (π v) ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 (irreducible_π v).ne_zero
    obtain ⟨y, hy⟩ := exists_nrd_eq_finite' (a := algebraMap (𝓞 F) F a) (b := algebraMap (𝓞 F) F b)
      ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 ha)
      ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hb) v hπ0
    have hOv := Gen.isOrder_localOrder_gen v hO.1
    have hO' : ∀ x, x ∈ localOrder (v := v) a b O ↔ IsInteger (v.adicCompletionIntegers F) (nrd x) := by
      intro x; rw [heq]; exact mem_valOrder hdiv
    obtain ⟨u, hu⟩ := exists_unit_gramTrd_ramified (localOrder (v := v) a b O) hO' (irreducible_π v) hy hdiv
      hOv.fg hOv.span f hmem
    refine ⟨u, ?_⟩
    simp only [hram, ↓reduceIte]
    exact hinj (hgram.symm.trans hu)
  · have hnram : v ∉ ramFin ha hb := by
      rw [mem_ramFin_iff, Gen.isRamifiedAt_finite_iff]
      intro hdiv
      have h0 := hdiv (φ.symm (Matrix.single 0 0 1)) (by
        rw [← det_algEquiv φ, AlgEquiv.apply_symm_apply]
        simp [Matrix.det_fin_two])
      have := congrArg φ h0
      rw [AlgEquiv.apply_symm_apply, map_zero] at this
      have h1 := congrFun (congrFun this 0) 0
      simp at h1
    obtain ⟨u, hu⟩ := exists_unit_gramTrd_split (localOrder (v := v) a b O) f hmem (irreducible_π v) φ hφ
    refine ⟨u, ?_⟩
    simp only [hnram, ↓reduceIte, pow_zero, one_mul]
    exact hinj (hgram.symm.trans hu)

open Classical in
theorem map_ι_asIdeal (v w : HeightOneSpectrum (𝓞 F)) :
    Ideal.map (ι v) w.asIdeal = if w = v then Ideal.span {π v} else 1 := by
  rw [map_ι_eq_span v w.ne_bot]
  split_ifs with h
  · subst h
    rw [cI, Associates.count_self (HeightOneSpectrum.associates_irreducible _), pow_one]
  · have hne : Associates.mk v.asIdeal ≠ Associates.mk w.asIdeal := by
      intro h'
      rw [Associates.mk_eq_mk_iff_associated, associated_iff_eq] at h'
      exact h (HeightOneSpectrum.ext h'.symm)
    rw [cI, Associates.count_eq_zero_of_ne v.associates_irreducible w.associates_irreducible hne, pow_zero,
      Ideal.span_singleton_one, Ideal.one_eq_top]

open Classical in
theorem map_ι_ramIdeal_sq (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.map (ι v) ((∏ w ∈ ramFin ha hb, w.asIdeal) ^ 2) =
      Ideal.span {π v ^ (if v ∈ ramFin ha hb then 2 else 0)} := by
  have h1 : Ideal.map (ι v) ((∏ w ∈ ramFin ha hb, w.asIdeal) ^ 2) =
      (∏ w ∈ ramFin ha hb, Ideal.map (ι v) w.asIdeal) ^ 2 := by
    change Ideal.mapHom (ι v) _ = _
    rw [map_pow, map_prod]; rfl
  rw [h1]
  simp_rw [map_ι_asIdeal v]
  rw [Finset.prod_ite_eq']
  split_ifs
  · rw [Ideal.span_singleton_pow]
  · rw [pow_zero, Ideal.span_singleton_one, ← Ideal.one_eq_top, one_pow]

/-- **Voight 2021, Theorem 15.5.5 ("only if"), proved for every number field**: the discriminant of a maximal
$\mathbb Z_F$-order with a $\mathbb Z_F$-basis is $\mathfrak D^2$, $\mathfrak D = \prod_{\mathfrak p \in \operatorname{Ram}_f B}\mathfrak p$, i.e.
`MassWave2.MaximalOrderDiscriminant F` holds unconditionally. This discharges that named input. -/
@[kb "voight2021" "Theorem 15.5.5, p. 249; Lemma 15.4.7, p. 247"]
theorem maximalOrderDiscriminant (F : Type) [Field F] [NumberField F] : MaximalOrderDiscriminant F where
  disc_eq a b ha hb O hO e := by
    classical
    obtain ⟨g, hg⟩ := exists_int_gram hO.1 e
    have hdet : algebraMap (𝓞 F) F g.det = trdGramDet (fun i => (e i : QuatF F a b)) := by
      rw [trdGramDet, RingHom.map_det]
      congr 1
      ext p q
      exact hg p q
    refine ⟨g.det, hdet, ?_⟩
    have : Submodule.IsLattice F (Subalgebra.toSubmodule O) := ⟨hO.1.fg, hO.1.span⟩
    set fb : Module.Basis (Fin 4) F (QuatF F a b) := e.extendOfIsLattice F
    have h2ab : (2 : F) * algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F b ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 ha))
        ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hb)
    have hd0 : g.det ≠ 0 := by
      intro h0
      have := gramTrd_ne_zero h2ab fb
      apply this
      have hfb : (fun q => fb q) = fun q => (e q : QuatF F a b) := by
        funext q; exact Module.Basis.extendOfIsLattice_apply F e q
      rw [hfb, gramTrd]
      rw [← trdGramDet, ← hdet, h0, map_zero]
    apply eq_of_map_eq
    · rw [Ne, Ideal.span_singleton_eq_bot]; exact hd0
    · exact pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun w _ => w.ne_bot)
    · intro v
      rw [map_ι_ramIdeal_sq ha hb v, Ideal.map_span, Set.image_singleton]
      obtain ⟨u, hu⟩ := local_disc ha hb hO e g hg v
      rw [hu, Ideal.span_singleton_mul_right_unit u.isUnit]

end Global

end QuadFormsKB.Voight.Disc
