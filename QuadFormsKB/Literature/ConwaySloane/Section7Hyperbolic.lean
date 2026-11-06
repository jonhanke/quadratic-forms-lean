/-
# Conway–Sloane, Ch. 15, §7, p. 378: same genus iff $f \oplus H \cong g \oplus H$

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7, p. 378
(`conwaysloane1999`). The book states, without proof ("follows from properties of the spinor genus"), that two
integral forms $f, g$ are in the same genus if and only if $f \oplus H$ and $g \oplus H$ are integrally equivalent,
where $H = \begin{pmatrix}0&1\\1&0\end{pmatrix}$ is the hyperbolic plane.

**Layer.** As in `Section9Theorems.lean`: a form is its symmetric integer Gram matrix $A \in M_n(\mathbb Z)$
(classically integral, $f(\vec x) = \vec x^{\mathsf T}A\vec x$), with the library form `Cassels.Ch8Ex2.gramForm A`
(Hessian $2A$), the rational form `csQ A` and the lattice $\Lambda = \mathbb Z^n$ (`stdLat`). The form $f \oplus H$ is the
block sum `Cassels.orthSumMat A !![0, 1; 1, 0]` in the variables $x_0, \dots, x_{n+1}$ (those of $f$ first, then the
hyperbolic pair $x_n, x_{n+1}$; 0-based indices). The genus is `Siegel.SameGenus` (equivalence over every
$\mathbb Z_p$ and over $\mathbb R$), integral equivalence is `Siegel.IntEquiv`.

**Proves**
* `units_mem_localSpinorNormGroup_of_hypPair`: if the lattice $\mathbb Z^m$ of a classically integral form contains a
  hyperbolic pair of basis vectors $e_i, e_j$ ($A_{ii} = A_{jj} = 0$, $A_{ij} = 1$), then at **every** prime $p$
  (including $p = 2$) every $p$-adic unit $u$ is $p$-adically automorphous: $e_i + ue_j$ and $e_i + e_j$ are $p$-adic
  root vectors of norms $2u$ and $2$ (Theorem 18, proved direction, `mem_localSpinorNormGroup_of_rootVectors`). Hence
  every prime is tractable.
* `intEquiv_add_hyperbolic_of_sameGenus`: same genus implies $f \oplus H \cong g \oplus H$ over $\mathbb Z$ (Eichler's
  theorem through `intEquiv_of_sameGenus_of_casselsX_le`: $f \oplus H$ is indefinite of dimension $n + 2 \ge 3$ and
  every prime is tractable, so its genus has one class).
* `sameGenus_of_intEquiv_add_hyperbolic`: the converse, by cancelling $H$ locally (`Section7HyperbolicCancel.lean`:
  O'Meara 93:14 over every $\mathbb Z_p$, Witt over $\mathbb R$).
* **The statement of p. 378** (`sameGenus_iff_intEquiv_add_hyperbolic`), unconditional. Only $\det A \ne 0$ is
  assumed; $\det B = \det A$ follows from either side. For $n = 0$ both sides hold trivially.
-/
import QuadFormsKB.Literature.ConwaySloane.Section7HyperbolicCancel
import QuadFormsKB.Literature.ConwaySloane.Section9Theorems
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices
open Cassels (orthSumMat)

/-! ### A hyperbolic pair makes every unit automorphous -/

section RootVectors

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {m : ℕ} {M : Matrix (Fin m) (Fin m) ℤ} (v : HeightOneSpectrum (𝓞 ℚ))

local notation "Fv" => v.adicCompletion ℚ

theorem hessian_map_csQ (hM : Mᵀ = M) :
    (csQ M).hessian.map (algebraMap ℚ Fv) = (2 : Fv) • M.map (Int.castRingHom Fv) := by
  ext k l
  have h := congrFun (congrFun (hessian_csForm hM) k) l
  have e : (csQ M).hessian.map (algebraMap ℚ Fv) k l =
      (((Cassels.Ch8Ex2.gramForm M).hessian k l : ℤ) : Fv) := by
    simp [csQ, QuadForm.hessian, QuadForm.map]
  rw [e, h]
  simp

variable {v}

theorem qbil_hypPair (hM : Mᵀ = M) {i j : Fin m} (c : Fv) (y : Fin m → Fv) :
    qbil (csQ M) Fv (Pi.single i 1 + c • Pi.single j 1) y =
      2 * ((M.map (Int.castRingHom Fv) *ᵥ y) i + c * (M.map (Int.castRingHom Fv) *ᵥ y) j) := by
  unfold qbil
  rw [hessian_map_csQ v hM, Matrix.smul_mulVec, add_dotProduct, smul_dotProduct, single_dotProduct,
    single_dotProduct]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem evalIn_hypPair (hM : Mᵀ = M) {i j : Fin m} (hii : M i i = 0) (hjj : M j j = 0)
    (h1 : M i j = 1) (c : Fv) : (csQ M).evalIn Fv (Pi.single i 1 + c • Pi.single j 1) = 2 * c := by
  have hji : M j i = 1 := by rw [← h1, ← Matrix.transpose_apply M j i, hM]
  have h := qbil_hypPair hM c (Pi.single i 1 + c • Pi.single j 1) (i := i) (j := j)
  rw [qbil_self] at h
  have e1 : (M.map (Int.castRingHom Fv) *ᵥ (Pi.single i 1 + c • Pi.single j 1)) i = c := by
    simp [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single, hii, h1]
  have e2 : (M.map (Int.castRingHom Fv) *ᵥ (Pi.single i 1 + c • Pi.single j 1)) j = 1 := by
    simp [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single, hjj, hji]
  rw [e1, e2] at h
  have h2 : (2 : Fv) ≠ 0 := two_ne_zero
  apply mul_left_cancel₀ h2
  linear_combination h

theorem valued_mulVec_le_one (y : Fin m → Fv) (hy : ∀ k, Valued.v (y k) ≤ 1) (k : Fin m) :
    Valued.v ((M.map (Int.castRingHom Fv) *ᵥ y) k) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  calc _ ≤ 1 * 1 := mul_le_mul' (by simpa using valued_intCast_le_one' v (M k l)) (hy l)
    _ = 1 := one_mul 1

/-- $e_i + ce_j$ is a $p$-adic root vector for every $p$-adic unit $c$, when $e_i, e_j$ are a hyperbolic pair. -/
theorem isRootVector_hypPair (hM : Mᵀ = M) {i j : Fin m} (hij : i ≠ j) (hii : M i i = 0) (hjj : M j j = 0)
    (h1 : M i j = 1) {c : Fv} (hc : Valued.v c = 1) :
    IsRootVector (csQ M) stdLat v (Pi.single i 1 + c • Pi.single j 1) := by
  have hQz := evalIn_hypPair hM hii hjj h1 c
  have hc0 : c ≠ 0 := fun h => by rw [h, map_zero] at hc; exact zero_ne_one hc
  have hx0 : (csQ M).evalIn Fv (Pi.single i 1 + c • Pi.single j 1) ≠ 0 := by
    rw [hQz]; exact mul_ne_zero two_ne_zero hc0
  refine ⟨hx0, ?_⟩
  have hloc : loc v (stdLat : Lat ℚ m).1 = std v := loc_intVec v
  have hxM : Pi.single i 1 + c • Pi.single j 1 ∈ loc v (stdLat : Lat ℚ m).1 := by
    rw [hloc, mem_std_iff]
    intro k
    by_cases hki : k = i
    · subst hki; simp [hij]
    · by_cases hkj : k = j
      · subst hkj; simp [hki, hc]
      · simp [hki, hkj]
  show locAct v (symm (csQ M) Fv (Pi.single i 1 + c • Pi.single j 1) : GL (Fin m) Fv) (loc v (stdLat : Lat ℚ m).1) =
    loc v (stdLat : Lat ℚ m).1
  refine locAct_symm_eq hxM hx0 fun y hy => ?_
  rw [hloc, mem_std_iff] at hy
  rw [qbil_hypPair hM, hQz, map_mul, map_mul, hc, mul_one]
  refine mul_le_of_le_one_right' ?_
  refine Valuation.map_add_le _ (valued_mulVec_le_one y hy i) ?_
  rw [map_mul, hc, one_mul]
  exact valued_mulVec_le_one y hy j

/-- **A hyperbolic pair makes every unit $p$-adically automorphous** (Conway–Sloane §9.5–9.6, at every prime $p$,
including $p = 2$): if the Gram matrix $M$ of a classically integral form has $M_{ii} = M_{jj} = 0$ and $M_{ij} = 1$
for some $i \ne j$, then every $p$-adic unit $u$ lies in $\theta(O^+(\Lambda_p))$, $\Lambda = \mathbb Z^m$. The root vectors
$e_i + ue_j$ and $e_i + e_j$ have norms $2u$ and $2$, with product $4u \sim u$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (a hyperbolic plane: all units are p-adically automorphous, every p)"]
theorem units_mem_localSpinorNormGroup_of_hypPair (hM : Mᵀ = M) {i j : Fin m} (hij : i ≠ j) (hii : M i i = 0)
    (hjj : M j j = 0) (h1 : M i j = 1) (hQ : (csQ M).Nondegenerate) (u : Fvˣ) (hu : Valued.v (u : Fv) = 1) :
    u ∈ localSpinorNormGroup (csQ M) hQ v stdLat := by
  refine mem_localSpinorNormGroup_of_rootVectors hQ
    [Pi.single i 1 + (u : Fv) • Pi.single j 1, Pi.single i 1 + (1 : Fv) • Pi.single j 1] (by simp) ?_ u ?_
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact isRootVector_hypPair hM hij hii hjj h1 hu
    · exact isRootVector_hypPair hM hij hii hjj h1 (map_one _)
  · simp only [valProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [evalIn_hypPair hM hii hjj h1, evalIn_hypPair hM hii hjj h1,
      show (2 : Fv) * u * (2 * 1) = (u : Fv) * 2 ^ 2 by ring]
    exact (sqClassOf_mul_sq u two_ne_zero).symm

end RootVectors

/-! ### The block sum $f \oplus H$ -/

section Main

variable {n : ℕ}

theorem hyp_transpose {R : Type*} [CommRing R] :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R)ᵀ = !![0, 1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem hyp_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R).map f = !![0, 1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem hypSum_transpose {R : Type*} [CommRing R] {A : Matrix (Fin n) (Fin n) R} (hA : Aᵀ = A) :
    (orthSumMat A !![0, 1; 1, 0])ᵀ = orthSumMat A !![0, 1; 1, 0] := by
  rw [orthSumMat_transpose, hA, hyp_transpose]

/-- $\det(A \oplus H) = -\det A$. -/
theorem det_hypSum (A : Matrix (Fin n) (Fin n) ℤ) : (orthSumMat A !![0, 1; 1, 0]).det = -A.det := by
  rw [det_orthSumMat, Matrix.det_fin_two_of]; ring

theorem transpose_map_of_symm {K : Type*} [CommRing K] (f : ℤ →+* K) {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : Aᵀ = A) : (A.map f)ᵀ = A.map f := by
  rw [← Matrix.transpose_map, hA]

/-- Equivalence over a characteristic-zero domain $K$ passes from $f, g$ to $f \oplus H, g \oplus H$. -/
theorem isometricGL_map_hypSum {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (f : ℤ →+* K)
    {A B : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (h : Siegel.IsometricGL ((Cassels.Ch8Ex2.gramForm A).map f) ((Cassels.Ch8Ex2.gramForm B).map f)) :
    Siegel.IsometricGL ((Cassels.Ch8Ex2.gramForm (orthSumMat A !![0, 1; 1, 0])).map f)
      ((Cassels.Ch8Ex2.gramForm (orthSumMat B !![0, 1; 1, 0])).map f) := by
  have hsA := transpose_map_of_symm f hA
  have hsB := transpose_map_of_symm f hB
  rw [gramForm_map, gramForm_map] at h ⊢
  rw [Cassels.Ex5.map_orthSum, Cassels.Ex5.map_orthSum, hyp_map]
  exact (isometricGL_gramForm_iff (hypSum_transpose hsA) (hypSum_transpose hsB)).2
    (congrIn_orthSumMat ((isometricGL_gramForm_iff hsA hsB).1 h) _)

/-- Same genus passes from $f, g$ to $f \oplus H, g \oplus H$. -/
theorem sameGenus_hypSum {A B : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (h : Siegel.SameGenus (Cassels.Ch8Ex2.gramForm A) (Cassels.Ch8Ex2.gramForm B)) :
    Siegel.SameGenus (Cassels.Ch8Ex2.gramForm (orthSumMat A !![0, 1; 1, 0]))
      (Cassels.Ch8Ex2.gramForm (orthSumMat B !![0, 1; 1, 0])) :=
  ⟨fun p _ => isometricGL_map_hypSum _ hA hB (h.1 p), isometricGL_map_hypSum _ hA hB h.2⟩

/-- $f \oplus H$ is indefinite: $e_n$ is isotropic. -/
theorem isIndefinite_csQ_hypSum (A : Matrix (Fin n) (Fin n) ℤ) :
    IsIndefinite (csQ (orthSumMat A !![0, 1; 1, 0])) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace ℚ))
  refine ⟨w, Pi.single (Fin.natAdd n 0) 1, ?_, ?_⟩
  · intro h
    have := congrFun h (Fin.natAdd n 0)
    simp at this
  · rw [QuadForm.evalIn, Finset.sum_eq_single (Fin.natAdd n 0)]
    · rw [Finset.sum_eq_single (Fin.natAdd n 0)]
      · simp [csQ, QuadForm.map, Cassels.Ch8Ex2.gramForm]
      · intro b _ hb; simp [hb]
      · simp
    · intro b _ hb; exact Finset.sum_eq_zero fun c _ => by simp [Pi.single_apply, hb]
    · simp

/-- **Same genus implies $f \oplus H \cong g \oplus H$** (Conway–Sloane, Ch. 15, §7, p. 378, "follows from
properties of the spinor genus"): $f \oplus H$ and $g \oplus H$ are in the same genus, $f \oplus H$ is indefinite of
dimension $n + 2 \ge 3$, and every prime is tractable because of the hyperbolic plane
(`units_mem_localSpinorNormGroup_of_hypPair`); by Eichler's theorem the genus of $f \oplus H$ has one class. -/
theorem intEquiv_add_hyperbolic_of_sameGenus {A B : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (hdA : A.det ≠ 0) (h : Siegel.SameGenus (Cassels.Ch8Ex2.gramForm A) (Cassels.Ch8Ex2.gramForm B)) :
    Siegel.IntEquiv (Cassels.Ch8Ex2.gramForm (orthSumMat A !![0, 1; 1, 0]))
      (Cassels.Ch8Ex2.gramForm (orthSumMat B !![0, 1; 1, 0])) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : A = B := by ext i; exact i.elim0
    subst this
    exact Siegel.IsometricGL.refl _
  have hsym := hypSum_transpose hA
  have hd : (orthSumMat A !![0, 1; 1, 0]).det ≠ 0 := by rw [det_hypSum]; exact neg_ne_zero.mpr hdA
  have hne : Fin.natAdd n (0 : Fin 2) ≠ Fin.natAdd n 1 := by simp [Fin.ext_iff]
  exact intEquiv_of_sameGenus_of_casselsX_le (by omega) _ (hessian_det_csForm_ne_zero hsym hd)
    (isIndefinite_csQ_hypSum A) _ (primeSet_spec hsym hd)
    (casselsX_le_of_isTractable _ _ _ _ fun q => isTractable_of_units_mem _ _ _ _ q fun u hu =>
      units_mem_localSpinorNormGroup_of_hypPair hsym hne (by simp) (by simp) (by simp) _ u hu)
    _ (sameGenus_hypSum hA hB h)

/-- **$f \oplus H \cong g \oplus H$ implies same genus** (the converse on p. 378): cancel $H$ over every $\mathbb Z_p$
(O'Meara 93:14, `congrIn_cancel_hyp_padic`) and over $\mathbb R$ (Witt, `congrIn_cancel_hyp_real`). -/
theorem sameGenus_of_intEquiv_add_hyperbolic {A B : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (hdA : A.det ≠ 0)
    (h : Siegel.IntEquiv (Cassels.Ch8Ex2.gramForm (orthSumMat A !![0, 1; 1, 0]))
      (Cassels.Ch8Ex2.gramForm (orthSumMat B !![0, 1; 1, 0]))) :
    Siegel.SameGenus (Cassels.Ch8Ex2.gramForm A) (Cassels.Ch8Ex2.gramForm B) := by
  have hs := Siegel.IntEquiv.sameGenus h
  refine ⟨fun p _ => ?_, ?_⟩
  · have h1 := hs.1 p
    have hsA := transpose_map_of_symm (Int.castRingHom ℤ_[p]) hA
    have hsB := transpose_map_of_symm (Int.castRingHom ℤ_[p]) hB
    rw [gramForm_map, gramForm_map, Cassels.Ex5.map_orthSum, Cassels.Ex5.map_orthSum, hyp_map] at h1
    rw [gramForm_map, gramForm_map]
    exact (isometricGL_gramForm_iff hsA hsB).2 (congrIn_cancel_hyp_padic hsA hsB
      ((isometricGL_gramForm_iff (hypSum_transpose hsA) (hypSum_transpose hsB)).1 h1))
  · have h1 := hs.2
    have hsA := transpose_map_of_symm (Int.castRingHom ℝ) hA
    have hsB := transpose_map_of_symm (Int.castRingHom ℝ) hB
    have hdet : (A.map (Int.castRingHom ℝ)).det ≠ 0 := by
      have e := RingHom.map_det (Int.castRingHom ℝ) A
      rw [RingHom.mapMatrix_apply] at e
      rw [← e, eq_intCast]; exact_mod_cast hdA
    rw [gramForm_map, gramForm_map, Cassels.Ex5.map_orthSum, Cassels.Ex5.map_orthSum, hyp_map] at h1
    rw [gramForm_map, gramForm_map]
    exact (isometricGL_gramForm_iff hsA hsB).2 (congrIn_cancel_hyp_real hsA hsB hdet
      ((isometricGL_gramForm_iff (hypSum_transpose hsA) (hypSum_transpose hsB)).1 h1))

/-- **Conway–Sloane, Ch. 15, §7, p. 378**: *two integral forms $f$ and $g$ are in the same genus if and only if
$f \oplus H$ and $g \oplus H$ are integrally equivalent, where $H = \begin{pmatrix}0&1\\1&0\end{pmatrix}$.* Here $f$
and $g$ are given by symmetric integer Gram matrices $A, B \in M_n(\mathbb Z)$ ($f(\vec x) = \vec x^{\mathsf T}A\vec x$,
classically integral) with $\det A \ne 0$, and $f \oplus H$ has Gram matrix
$\begin{pmatrix}A&0\\0&H\end{pmatrix}$ in the variables $x_0, \dots, x_{n+1}$. Unconditional: "same genus $\Rightarrow$"
is Eichler's theorem for the indefinite form $f \oplus H$ (all primes tractable), "$\Leftarrow$" is local
cancellation of $H$. -/
@[kb "conwaysloane1999" "Ch. 15, §7, p. 378 (same genus iff f ⊕ H ≅ g ⊕ H)"]
theorem sameGenus_iff_intEquiv_add_hyperbolic {A B : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (hdA : A.det ≠ 0) :
    Siegel.SameGenus (Cassels.Ch8Ex2.gramForm A) (Cassels.Ch8Ex2.gramForm B) ↔
      Siegel.IntEquiv (Cassels.Ch8Ex2.gramForm (orthSumMat A !![0, 1; 1, 0]))
        (Cassels.Ch8Ex2.gramForm (orthSumMat B !![0, 1; 1, 0])) :=
  ⟨intEquiv_add_hyperbolic_of_sameGenus hA hB hdA, sameGenus_of_intEquiv_add_hyperbolic hA hB hdA⟩

end Main

end QuadFormsKB.ConwaySloane
