/-
# Conway–Sloane 1988, §11, Lemma 3: cancelling $I_1$ inside a genus

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §11, Lemma 3, p. 280: *if $L \oplus I_1$ and $M \oplus I_1$ are in the same genus, then so
are $L$ and $M$, provided they have the same type.* The paper states it without proof (citing Kneser–Puppe 1953); the
library had it as the named statement `Mass.Lemma3Statement` (`GenusLemmas.lean`). This file proves it.

**Conventions** (as in `GenusLemmas.lean`). A positive definite lattice is its integral Gram matrix
`A : Matrix (Fin n) (Fin n) ℤ` with `PosDefGram A`; its form is `LocalDensity.ofMatrixZ A`, $x \mapsto x^{\mathsf T}Ax$
(definitionally `Cassels.Ch8Ex2.gramForm A`); $L \oplus I_1$ is `blockMat A 0 0 oneGram` (definitionally the block sum
`Cassels.orthSumMat A 1`, the variable of $I_1$ last, index $n$). Over $\mathbb Z_p$ the relation is Cassels'
$\mathbb Z_p$-equivalence `Cassels.ZpEquiv` of the Gram matrices over $\mathbb Q_p$: $F \sim G$ iff
$T^{\mathsf T}FT = G$ for some $T \in \mathrm{GL}_n(\mathbb Z_p)$.

**Proof.** Same genus is equivalence over $\mathbb R$ and over every $\mathbb Z_p$.
* Over $\mathbb R$ positive definite forms of the same dimension are equivalent (`Siegel.isometricGL_real_of_posDef`).
* At an odd prime $p$: diagonalize $F = A$ and $G = B$ over $\mathbb Z_p$ ($F \sim \operatorname{diag}(p^{z_i}u_i)$),
  so $F \oplus \langle 1\rangle$ has the diagonal form with one more unit entry $1$ at scale $p^0$. Its $p$-adic symbol
  (`oddSymbolOfDiag`) is that of $F$ with $n_1$ raised by one and the same signs (`oddSymbolOfDiag_append`). By
  Conway–Sloane's Theorem 9 (`theorem9`: $\mathbb Z_p$-equivalence iff equal symbols) applied twice, the symbols of
  $F$, $G$ agree, so $F \sim G$ (`zpEquiv_cancel_one_odd`).
* At $p = 2$: Cassels' Lemma 4.2 (Ch. 8, `zpEquiv_cancel_unit`): $\langle u\rangle + g_1 \sim \langle u\rangle + g_2$
  implies $g_1 \sim g_2$ when $g_1$, $g_2$ are both properly primitive or both not. For a Gram matrix $A$ over
  $\mathbb Z$, "properly primitive at $2$" (some diagonal entry a $2$-adic unit) means exactly "some $A_{ii}$ odd", i.e.
  type I (`isProperlyPrimitive_map_iff`); so the hypothesis "same type" is precisely Cassels' hypothesis. (Without it
  cancellation fails over $\mathbb Z_2$: by Cassels (4.7), $\langle 1\rangle \perp 2x_1x_2 \sim
  \langle 1\rangle \perp (x_1^2 - x_2^2)$ but $2x_1x_2 \not\sim x_1^2 - x_2^2$, `Cassels.not_witt_cancellation`; this
  is why the paper's Lemma 3 assumes the same type.) The summand $\langle 1\rangle$ is moved to the front by
  renaming the variables (`orthSumMat_one_swap`).

**Proves**
* `isometricGL_padic_iff`: for symmetric integral $A$, $B$, `ofMatrixZ A ≅ ofMatrixZ B` over $\mathbb Z_p$ iff
  $A \sim B$ (`Cassels.ZpEquiv` of the images in $\mathbb Q_p$).
* `zpEquiv_cancel_one_odd`: for odd $p$, nonsingular symmetric integral $F$, $G$ over $\mathbb Q_p$:
  $F \oplus \langle 1\rangle \sim G \oplus \langle 1\rangle$ implies $F \sim G$.
* `zpEquiv_cancel_one_two`: the same at $p = 2$ when $F$, $G$ are both properly primitive or both not.
* `lemma3Statement_proof : Mass.Lemma3Statement` (**§11, Lemma 3**, unconditional), and
  `lemma4_of_lemma2`: Lemma 2 alone now gives Lemma 4.

Indices are 0-based.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.ConwaySloane.Section7Hyperbolic
import QuadFormsKB.Literature.ConwaySloane.OddClassification
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicCancel
import QuadFormsKB.Literature.ConwaySloane.Mass.Vines
import QuadFormsKB.Literature.Cassels.Ch9Sec6Four

set_option linter.unusedSectionVars false

open Matrix QuadFormsKB.Cassels QuadFormsKB.Tamagawa.Frames

namespace QuadFormsKB.ConwaySloane.Mass

variable {n : ℕ}

/-! ### Forms over $\mathbb Z_p$ and Gram matrices over $\mathbb Q_p$ -/

section Bridge

variable {p : ℕ} [Fact p.Prime]

theorem map_map_padic (A : Matrix (Fin n) (Fin n) ℤ) :
    (A.map (Int.castRingHom ℤ_[p])).map PadicInt.Coe.ringHom = A.map (Int.castRingHom ℚ_[p]) := by
  ext i j; simp

/-- Congruence over $\mathbb Z_p$ of matrices over $\mathbb Z_p$ is `ZpEquiv` of their images over $\mathbb Q_p$. -/
theorem congrIn_iff_zpEquiv {X Y : Matrix (Fin n) (Fin n) ℤ_[p]} :
    CongrIn ℤ_[p] X Y ↔ ZpEquiv (X.map PadicInt.Coe.ringHom) (Y.map PadicInt.Coe.ringHom) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, by rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]⟩
  · rintro ⟨T, hT⟩
    refine ⟨T, ?_⟩
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul] at hT
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun hT i) j
    simp only [Matrix.map_apply] at this
    exact Subtype.ext this

/-- **The genus condition at $p$ in matrix form**: for symmetric $A$, $B \in M_n(\mathbb Z)$, the forms
$x^{\mathsf T}Ax$ and $x^{\mathsf T}Bx$ are equivalent over $\mathbb Z_p$ iff $A \sim B$ over $\mathbb Z_p$
(`Cassels.ZpEquiv` of the images in $M_n(\mathbb Q_p)$). -/
theorem isometricGL_padic_iff {A B : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hB : Bᵀ = B) :
    Siegel.IsometricGL ((LocalDensity.ofMatrixZ A).map (Int.castRingHom ℤ_[p]))
      ((LocalDensity.ofMatrixZ B).map (Int.castRingHom ℤ_[p])) ↔
    ZpEquiv (A.map (Int.castRingHom ℚ_[p])) (B.map (Int.castRingHom ℚ_[p])) := by
  have e : ∀ C : Matrix (Fin n) (Fin n) ℤ, LocalDensity.ofMatrixZ C = QuadFormsKB.Cassels.Ch8Ex2.gramForm C :=
    fun _ => rfl
  rw [e, e, gramForm_map, gramForm_map,
    isometricGL_gramForm_iff (transpose_map_of_symm _ hA) (transpose_map_of_symm _ hB),
    congrIn_iff_zpEquiv, map_map_padic, map_map_padic]

/-- $\mathbb Z_p$-equivalence passes to block sums: $F \sim G \Rightarrow F \oplus Z \sim G \oplus Z$. -/
theorem zpEquiv_orthSumMat {a b : ℕ} {F G : Matrix (Fin a) (Fin a) ℚ_[p]} (h : ZpEquiv F G)
    (Z : Matrix (Fin b) (Fin b) ℚ_[p]) : ZpEquiv (orthSumMat F Z) (orthSumMat G Z) := by
  obtain ⟨T, hT⟩ := h
  let u : GL (Fin (a + b)) ℤ_[p] :=
    ⟨orthSumMat T.val 1, orthSumMat T⁻¹.val 1,
      by rw [orthSumMat_mul, Units.mul_inv, Matrix.one_mul, orthSumMat_one],
      by rw [orthSumMat_mul, Units.inv_mul, Matrix.one_mul, orthSumMat_one]⟩
  refine ⟨u, ?_⟩
  change ((orthSumMat T.val 1).map PadicInt.Coe.ringHom)ᵀ * orthSumMat F Z *
    (orthSumMat T.val 1).map PadicInt.Coe.ringHom = orthSumMat G Z
  rw [Ex5.map_orthSum, Matrix.map_one _ (map_zero _) (map_one _), orthSumMat_transpose, orthSumMat_mul,
    orthSumMat_mul, hT, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem oneGram_map {K : Type*} [CommRing K] (f : ℤ →+* K) : oneGram.map f = !![(1 : K)] := by
  ext i j; fin_cases i; fin_cases j; simp [oneGram]

end Bridge

/-! ### Odd primes: cancelling $\langle 1\rangle$ via the $p$-adic symbol -/

section Odd

variable {p : ℕ} [Fact p.Prime]

/-- $\operatorname{diag}(p^{z_i}u_i) \oplus \langle 1\rangle$ is the diagonal form with one more entry $p^0\cdot 1$. -/
theorem orthSumMat_diag_one (z : Fin n → ℕ) (u : Fin n → ℚ_[p]) :
    orthSumMat (Matrix.diagonal fun i => (p : ℚ_[p]) ^ z i * u i) !![(1 : ℚ_[p])] =
      Matrix.diagonal fun i => (p : ℚ_[p]) ^ (Fin.append z (fun _ : Fin 1 => 0) i) *
        Fin.append u (fun _ : Fin 1 => (1 : ℚ_[p])) i := by
  ext i j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) j
  · simp [Matrix.diagonal_apply]
  · simp [castAdd_ne_natAdd]
  · simp [(castAdd_ne_natAdd _ _).symm]
  · fin_cases a; fin_cases b; simp

/-- **The symbol of $f \oplus \langle 1\rangle$**: the dimension of the scale-$p^0$ constituent goes up by one, all other
dimensions and all signs are unchanged. -/
theorem oddSymbolOfDiag_append (z : Fin n → ℕ) (u : Fin n → ℚ_[p]) (k : ℕ) :
    oddSymbolOfDiag p (Fin.append z (fun _ : Fin 1 => 0)) (Fin.append u (fun _ : Fin 1 => (1 : ℚ_[p]))) k =
      ⟨(oddSymbolOfDiag p z u k).dim + (if k = 0 then 1 else 0), (oddSymbolOfDiag p z u k).sign⟩ := by
  classical
  have hcard : Fintype.card {i // Fin.append z (fun _ : Fin 1 => 0) i = k} =
      Fintype.card {i // z i = k} + (if k = 0 then 1 else 0) := by
    rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
    simp [eq_comm]
  have hprod : ∏ i : {i // Fin.append z (fun _ : Fin 1 => 0) i = k},
      Fin.append u (fun _ : Fin 1 => (1 : ℚ_[p])) i = ∏ i : {i // z i = k}, u i := by
    rw [← Finset.prod_subtype (Finset.univ.filter fun i => Fin.append z (fun _ : Fin 1 => 0) i = k) (by simp),
      ← Finset.prod_subtype (Finset.univ.filter fun i => z i = k) (by simp), Finset.prod_filter, Finset.prod_filter,
      Fin.prod_univ_add]
    simp
  simp only [oddSymbolOfDiag, hcard, hprod]

theorem oddFactor_ext {x y : OddFactor} (h1 : x.dim = y.dim) (h2 : x.sign = y.sign) : x = y := by
  cases x; cases y; simp_all

theorem orthSumMat_one_transpose {F : Matrix (Fin n) (Fin n) ℚ_[p]} (hF : Fᵀ = F) :
    (orthSumMat F !![(1 : ℚ_[p])])ᵀ = orthSumMat F !![(1 : ℚ_[p])] := by
  rw [orthSumMat_transpose, hF]
  congr 1
  ext i j; fin_cases i; fin_cases j; rfl

theorem det_orthSumMat_one (F : Matrix (Fin n) (Fin n) ℚ_[p]) :
    (orthSumMat F !![(1 : ℚ_[p])]).det = F.det := by
  rw [det_orthSumMat]; simp

theorem isOddSymbolOf_orthSumMat_one {F : Matrix (Fin n) (Fin n) ℚ_[p]} {z : Fin n → ℕ} {u : Fin n → ℚ_[p]}
    (hu : ∀ i, ‖u i‖ = 1) (hFD : ZpEquiv F (Matrix.diagonal fun i => (p : ℚ_[p]) ^ z i * u i)) :
    IsOddSymbolOf p (orthSumMat F !![(1 : ℚ_[p])])
      (oddSymbolOfDiag p (Fin.append z (fun _ : Fin 1 => 0)) (Fin.append u (fun _ : Fin 1 => (1 : ℚ_[p])))) := by
  have hu1 : ∀ i, ‖Fin.append u (fun _ : Fin 1 => (1 : ℚ_[p])) i‖ = 1 := fun i =>
    Fin.addCases (fun a => by simpa using hu a) (fun a => by simp) i
  refine ⟨_, _, hu1, ?_, rfl⟩
  · rw [← orthSumMat_diag_one]; exact zpEquiv_orthSumMat hFD _

/-- **Cancelling $\langle 1\rangle$ over $\mathbb Z_p$, $p$ odd**: for nonsingular symmetric integral $F$, $G$ over
$\mathbb Q_p$, $F \oplus \langle 1\rangle \sim G \oplus \langle 1\rangle$ implies $F \sim G$ (Conway–Sloane's Theorem 9
applied to both pairs). -/
theorem zpEquiv_cancel_one_odd (hp2 : p ≠ 2) {F G : Matrix (Fin n) (Fin n) ℚ_[p]} (hF : Fᵀ = F) (hG : Gᵀ = G)
    (hFd : F.det ≠ 0) (hGd : G.det ≠ 0) (hFi : ∀ i j, ‖F i j‖ ≤ 1) (hGi : ∀ i j, ‖G i j‖ ≤ 1)
    (h : ZpEquiv (orthSumMat F !![(1 : ℚ_[p])]) (orthSumMat G !![(1 : ℚ_[p])])) : ZpEquiv F G := by
  obtain ⟨σ, z, u, hu, hFD, rfl⟩ := exists_isOddSymbolOf hp2 hF hFd hFi
  obtain ⟨τ, z', u', hu', hGD, rfl⟩ := exists_isOddSymbolOf hp2 hG hGd hGi
  have heq := (theorem9 hp2 (orthSumMat_one_transpose hF) (by rw [det_orthSumMat_one]; exact hFd)
    (orthSumMat_one_transpose hG) (by rw [det_orthSumMat_one]; exact hGd)
    (isOddSymbolOf_orthSumMat_one hu hFD) (isOddSymbolOf_orthSumMat_one hu' hGD)).1 h
  refine (theorem9 hp2 hF hFd hG hGd ⟨z, u, hu, hFD, rfl⟩ ⟨z', u', hu', hGD, rfl⟩).2 ?_
  funext k
  have hk := congrFun heq k
  rw [oddSymbolOfDiag_append, oddSymbolOfDiag_append, OddFactor.mk.injEq] at hk
  exact oddFactor_ext (by omega) hk.2

end Odd

/-! ### $p = 2$: cancelling $\langle 1\rangle$ by Cassels' Lemma 4.2 -/

section Two

/-- Moving the summand $\langle c\rangle$ from the end to the front renames the variables. -/
theorem orthSumMat_one_swap {K : Type*} [Zero K] (F : Matrix (Fin n) (Fin n) K) (c : K) :
    orthSumMat !![c] F = (orthSumMat F !![c]).submatrix
      (finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans finSumFinEquiv))
      (finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans finSumFinEquiv)) := by
  ext i j
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  simp only [submatrix_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [Two.orthSumMat_apply', Two.orthSumMat_apply']
  rcases x with x | x <;> rcases y with y | y <;> simp

/-- **Cancelling $\langle 1\rangle$ over $\mathbb Z_2$** (Cassels, Ch. 8, Lemma 4.2 with $u = 1$): if $F$, $G$ are
classically integral, both properly primitive or both not, then $F \oplus \langle 1\rangle \sim G \oplus \langle 1\rangle$
implies $F \sim G$. -/
theorem zpEquiv_cancel_one_two {F G : Matrix (Fin n) (Fin n) ℚ_[2]} (hF : Fᵀ = F) (hG : Gᵀ = G)
    (hFi : IsClassIntegral F) (hGi : IsClassIntegral G) (hpp : IsProperlyPrimitive F ↔ IsProperlyPrimitive G)
    (h : ZpEquiv (orthSumMat F !![(1 : ℚ_[2])]) (orthSumMat G !![(1 : ℚ_[2])])) : ZpEquiv F G := by
  refine zpEquiv_cancel_unit (u := 1) (by simp) hF hG hFi hGi hpp ?_
  rw [orthSumMat_one_swap F, orthSumMat_one_swap G]
  exact Two.zpEquiv_submatrix _ h

theorem norm_intCast_two_eq_one_iff (k : ℤ) : ‖(k : ℚ_[2])‖ = 1 ↔ ¬ (2 : ℤ) ∣ k := by
  have h1 := Padic.norm_int_le_one (p := 2) k
  have h2 : ‖(k : ℚ_[2])‖ < 1 ↔ ((2 : ℕ) : ℤ) ∣ k := Padic.norm_intCast_lt_one_iff
  constructor
  · intro h hd
    have := h2.2 (by exact_mod_cast hd)
    linarith
  · intro h
    exact le_antisymm h1 (not_lt.1 fun hlt => h (by exact_mod_cast h2.1 hlt))

/-- **Properly primitive at $2$ is type I**: the image of an integral Gram matrix $A$ in $M_n(\mathbb Q_2)$ is properly
primitive (some diagonal entry a $2$-adic unit) iff some $A_{ii}$ is odd. -/
theorem isProperlyPrimitive_map_iff (A : Matrix (Fin n) (Fin n) ℤ) :
    IsProperlyPrimitive (A.map (Int.castRingHom ℚ_[2])) ↔ ¬ EvenGram A := by
  constructor
  · rintro ⟨-, j, hj⟩ he
    simp only [Matrix.map_apply, eq_intCast] at hj
    exact (norm_intCast_two_eq_one_iff _).1 hj (even_iff_two_dvd.1 (he j))
  · intro he
    simp only [EvenGram, not_forall] at he
    obtain ⟨j, hj⟩ := he
    have hj' : ‖(A.map (Int.castRingHom ℚ_[2])) j j‖ = 1 := by
      simp only [Matrix.map_apply, eq_intCast]
      exact (norm_intCast_two_eq_one_iff _).2 fun h => hj (even_iff_two_dvd.2 h)
    exact ⟨⟨fun a b => by simp only [Matrix.map_apply, eq_intCast]; exact Padic.norm_int_le_one _, j, j, hj'⟩,
      j, hj'⟩

theorem evenGram_iff_of_gramType_eq {A B : Matrix (Fin n) (Fin n) ℤ} (ht : gramType A = gramType B) :
    EvenGram A ↔ EvenGram B := by
  classical
  unfold gramType at ht
  by_cases hA : EvenGram A <;> by_cases hB : EvenGram B <;> simp_all

end Two

/-! ### Lemma 3 -/

theorem isClassIntegral_map {p : ℕ} [Fact p.Prime] (A : Matrix (Fin n) (Fin n) ℤ) :
    ∀ i j, ‖(A.map (Int.castRingHom ℚ_[p])) i j‖ ≤ 1 := fun i j => by
  simp only [Matrix.map_apply, eq_intCast]; exact Padic.norm_int_le_one _

theorem det_map_ne {p : ℕ} [Fact p.Prime] {A : Matrix (Fin n) (Fin n) ℤ} (hd : A.det ≠ 0) :
    (A.map (Int.castRingHom ℚ_[p])).det ≠ 0 := by
  have e := RingHom.map_det (Int.castRingHom ℚ_[p]) A
  rw [RingHom.mapMatrix_apply] at e
  rw [← e, eq_intCast]; exact_mod_cast hd

/-- **Conway–Sloane 1988, §11, Lemma 3, proved** (it was the named statement `Mass.Lemma3Statement`): for positive
definite integral Gram matrices $A$, $B$ (lattices $L$, $M$) of the same type, if $L \oplus I_1$ and $M \oplus I_1$ are in
the same genus then so are $L$ and $M$. Unconditional: over $\mathbb R$ both are positive definite; at odd $p$ the
$p$-adic symbols (Theorem 9) cancel the unit constituent $\langle 1\rangle$; at $p = 2$ Cassels' Lemma 4.2 cancels
$\langle 1\rangle$, its hypothesis being exactly "same type". -/
@[kb "conwaysloane1988" "§11, Lemma 3, p. 280"]
theorem lemma3Statement_proof : Lemma3Statement where
  imp n A B hA hB h ht := by
    have hsA : (blockMat A 0 0 oneGram)ᵀ = blockMat A 0 0 oneGram := hA.sumOne.1
    have hsB : (blockMat B 0 0 oneGram)ᵀ = blockMat B 0 0 oneGram := hB.sumOne.1
    refine ⟨fun p _ => ?_, ?_⟩
    · have hp := (isometricGL_padic_iff hsA hsB).1 (h.1 p)
      have e : ∀ C : Matrix (Fin n) (Fin n) ℤ, (blockMat C 0 0 oneGram).map (Int.castRingHom ℚ_[p]) =
          orthSumMat (C.map (Int.castRingHom ℚ_[p])) !![(1 : ℚ_[p])] := fun C => by
        rw [← oneGram_map]; exact Ex5.map_orthSum _ C oneGram
      rw [e, e] at hp
      refine (isometricGL_padic_iff hA.1 hB.1).2 ?_
      by_cases hp2 : p = 2
      · subst hp2
        refine zpEquiv_cancel_one_two (transpose_map_of_symm _ hA.1) (transpose_map_of_symm _ hB.1)
          (isClassIntegral_map A) (isClassIntegral_map B) ?_ hp
        rw [isProperlyPrimitive_map_iff, isProperlyPrimitive_map_iff, evenGram_iff_of_gramType_eq ht]
      · exact zpEquiv_cancel_one_odd hp2 (transpose_map_of_symm _ hA.1) (transpose_map_of_symm _ hB.1)
          (det_map_ne hA.det_ne) (det_map_ne hB.det_ne) (isClassIntegral_map A) (isClassIntegral_map B) hp
    · refine Siegel.isometricGL_real_of_posDef ⟨A, hA.1, fun x => LocalDensity.eval_ofMatrixZ A x⟩
        ⟨B, hB.1, fun x => LocalDensity.eval_ofMatrixZ B x⟩ (fun x hx => ?_) (fun x hx => ?_)
      · rw [LocalDensity.eval_ofMatrixZ]; exact hA.pos_int hx
      · rw [LocalDensity.eval_ofMatrixZ]; exact hB.pos_int hx

/-- **Lemma 2 alone gives Lemma 4** (§11, p. 280, "by combining Lemmas 2 and 3"), now that Lemma 3 is proved. -/
@[kb "conwaysloane1988" "§11, Lemma 4 (from Lemma 2 and the proved Lemma 3), p. 280"]
theorem lemma4_of_lemma2 (h2 : Lemma2Statement) : Lemma4Statement :=
  lemma4_of_lemma2_lemma3 h2 lemma3Statement_proof

end QuadFormsKB.ConwaySloane.Mass
