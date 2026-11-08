/-
# Conway–Sloane 1988, §11: properties of the genus (Lemmas 1–4, the discriminant form, determinant $2$)

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §11 "Properties of the genus", pp. 280–281. The paper states Lemmas 1–4 **without proof**
("These results also follow from Kneser & Puppe (1953)"); here they are *named statements* (`Lemma1Statement`, …), never
axioms, and the deductions between them and the easy directions are proved.

**Conventions (book $\to$ Lean).**
* A lattice $L$ is given by its integral Gram matrix $A$ in a basis: `A : Matrix (Fin n) (Fin n) ℤ`, positive definite
  (`PosDefGram A`: $A^{\mathsf T} = A$ and $x^{\mathsf T}Ax > 0$ for rational $x \ne 0$; the paper's lattices are positive definite,
  and for indefinite lattices Lemma 4 is false since it does not see the signature). The corresponding quadratic form is
  `LocalDensity.ofMatrixZ A`, $x \mapsto x^{\mathsf T}Ax$ (Hessian $2A$). Two lattices are in the *same genus* iff
  `Siegel.SameGenus (ofMatrixZ A) (ofMatrixZ B)`; *integrally equivalent* means `Siegel.IntEquiv`.
* The *type* $T$ (`gramType A`) is $1$ (type I, odd: some $A_{ii}$ is odd) or $2$ (type II, even: all $A_{ii}$ even).
* The dual quotient $L^*/L \cong \mathbb Z^n/A\mathbb Z^n$ is `DiscGroup A`. For $y \in \mathbb Z^n$ the vector $v = A^{-1}y$ lies in
  $L^*$ (coordinates in the basis of $L$) and its norm is $v\cdot v = y^{\mathsf T}A^{-1}y \in \mathbb Q$: `dualNorm A y`.
* "An isomorphism $L^*/L \cong M^*/M$ preserving norms mod $T$" is `DiscIso T A B`: an additive isomorphism $\varphi$ of the
  two quotients such that $\mathrm{norm}(\varphi[y]) \equiv \mathrm{norm}([y]) \pmod T$ for all representatives.
* $H$ is `hypGram` $= \begin{pmatrix}0&1\\1&0\end{pmatrix}$, $I_1$ is `oneGram` $= (1)$, and $L \oplus M$ is the block diagonal
  Gram matrix `Tamagawa.Frames.blockMat A 0 0 B` in coordinates `Fin (n + m)`.

**Proves**
* `dualNorm_congr_one`, `dualNorm_congr_even` (§11, remark 1, p. 280): norms of the vectors of a coset $u + L$ are congruent
  mod $1$, and mod $2$ if $L$ is even; `discNorm` is the resulting discriminant form $L^*/L \to \mathbb Q/T\mathbb Z$.
* `Lemma1Statement`, `Lemma2Statement`, `Lemma3Statement`, `Lemma4Statement`: Lemmas 1–4 as named statements.
* `gramType_eq_of_sameGenus`: forms in the same genus have the same type (unconditional; $2$-adic argument).
* `sameGenus_of_lemma4`: the "if" half of Lemma 2 follows from Lemma 4.
* `discSumOne`, `DiscIso.sumOne`: $(L \oplus I_1)^*/(L \oplus I_1) \cong L^*/L$ preserving norms mod $1$ (used for the deduction below).
* `card_discGroup`: $|L^*/L| = |\det A|$ (via Mathlib's `Submodule.natAbs_det_equiv`).
* `lemma4_of_lemma2_lemma3`: Lemma 2 and Lemma 3 together give Lemma 4 ("by combining Lemmas 2 and 3").
* `norm_generator_det_two` (§11, remark 3, p. 281): if $\det L = 2$ and $v_2$ generates $L^*/L$ then $v_2\cdot v_2 \equiv \tfrac12 \pmod 1$;
  `sameGenus_of_det_two` derives, under `Lemma4Statement`, that lattices of determinant $2$ and the same type are in the same genus
  (so there are at most two genera, one for each type).

**Proved elsewhere:** Lemma 1 (`lemma1Statement_proof`, `Section7HyperbolicMass.lean`), Lemma 3
(`lemma3Statement_proof`, `GenusLemma3.lean`, which also gives `lemma4_of_lemma2`), remarks 4 and 5 at the symbol level
(`genera_det_prime`, `genera_det_two_prime`, `GeneraSmallDet.lean`), Lemma 2 (`Gauss2.lemma2Statement_holds`,
`GenusLemma2Local.lean`) and Lemma 4 (`Gauss2.lemma4Statement_holds`); the lemmas as plain theorems and the unconditional
versions of `sameGenus_of_lemma4` and `sameGenus_of_det_two` are in `GenusLemmasHold.lean`.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Siegel.Genus
import QuadFormsKB.LocalDensity.JordanForm
import QuadFormsKB.Tamagawa.BlockForm

open Matrix QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa.Frames

namespace QuadFormsKB.ConwaySloane.Mass

variable {n m : ℕ}

/-! ### Lattices, dual quotient, norms -/

/-- The Gram matrix over $\mathbb Q$. -/
def gramQ (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℚ := A.map (Int.castRingHom ℚ)

/-- **A positive definite integral lattice**, given by its Gram matrix $A$: symmetric with $x^{\mathsf T}Ax > 0$ for all nonzero
rational $x$. -/
def PosDefGram (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  Aᵀ = A ∧ ∀ x : Fin n → ℚ, x ≠ 0 → 0 < x ⬝ᵥ (gramQ A *ᵥ x)

theorem PosDefGram.det_ne {A : Matrix (Fin n) (Fin n) ℤ} (h : PosDefGram A) : A.det ≠ 0 := by
  intro h0
  have hq : (gramQ A).det = 0 := by
    have := RingHom.map_det (Int.castRingHom ℚ) A
    rw [h0, map_zero] at this
    exact this.symm
  obtain ⟨x, hx, hx0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hq
  have := h.2 x hx
  rw [hx0] at this
  simp at this

theorem gramQ_det_ne {A : Matrix (Fin n) (Fin n) ℤ} (hd : A.det ≠ 0) : (gramQ A).det ≠ 0 := by
  have := RingHom.map_det (Int.castRingHom ℚ) A
  intro h
  apply hd
  have h2 : ((A.det : ℤ) : ℚ) = 0 := by rw [← eq_intCast (Int.castRingHom ℚ)]; exact this.trans h
  exact_mod_cast h2

/-- **The sublattice $A\mathbb Z^n = L$ inside $\mathbb Z^n = $ the coordinates of $L^*$** (a vector $y$ stands for
$A^{-1}y \in L^*$, and $y \in A\mathbb Z^n$ iff $A^{-1}y \in L$). -/
def gramLat (A : Matrix (Fin n) (Fin n) ℤ) : AddSubgroup (Fin n → ℤ) := (A.mulVecLin).range.toAddSubgroup

theorem mem_gramLat {A : Matrix (Fin n) (Fin n) ℤ} {w : Fin n → ℤ} : w ∈ gramLat A ↔ ∃ z, A *ᵥ z = w := by
  simp [gramLat, LinearMap.mem_range]

/-- **The dual quotient** $L^*/L \cong \mathbb Z^n/A\mathbb Z^n$. -/
abbrev DiscGroup (A : Matrix (Fin n) (Fin n) ℤ) := (Fin n → ℤ) ⧸ gramLat A

/-- **The norm** $v \cdot v = y^{\mathsf T}A^{-1}y \in \mathbb Q$ of the vector $v = A^{-1}y \in L^*$ (§11, remark 1). -/
@[kb "conwaysloane1988" "§11, remark 1, p. 280"]
noncomputable def dualNorm (A : Matrix (Fin n) (Fin n) ℤ) (y : Fin n → ℤ) : ℚ :=
  (fun i => (y i : ℚ)) ⬝ᵥ ((gramQ A)⁻¹ *ᵥ (fun i => (y i : ℚ)))

theorem cast_mulVec (A : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) :
    (fun i => ((A *ᵥ z) i : ℚ)) = gramQ A *ᵥ (fun i => (z i : ℚ)) := by
  ext i
  simp [gramQ, mulVec, dotProduct]

theorem dualNorm_add_mulVec {A : Matrix (Fin n) (Fin n) ℤ} (hs : Aᵀ = A) (hd : A.det ≠ 0)
    (y z : Fin n → ℤ) :
    dualNorm A (y + A *ᵥ z) = dualNorm A y + 2 * ((y ⬝ᵥ z : ℤ) : ℚ) + ((z ⬝ᵥ (A *ᵥ z) : ℤ) : ℚ) := by
  have hu : IsUnit (gramQ A).det := (gramQ_det_ne hd).isUnit
  have hsq : (gramQ A)ᵀ = gramQ A := by
    unfold gramQ; rw [← Matrix.transpose_map, hs]
  set G := gramQ A with hG
  set Y : Fin n → ℚ := fun i => (y i : ℚ) with hY
  set Z : Fin n → ℚ := fun i => (z i : ℚ) with hZ
  have h1 : (fun i => ((y + A *ᵥ z) i : ℚ)) = Y + G *ᵥ Z := by
    ext i
    have := congrFun (cast_mulVec A z) i
    simp only [Pi.add_apply, Int.cast_add, hY]
    rw [this]
  have hinv : G⁻¹ *ᵥ (G *ᵥ Z) = Z := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have hinv2 : G *ᵥ (G⁻¹ *ᵥ Y) = Y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hcomm : (G *ᵥ Z) ⬝ᵥ (G⁻¹ *ᵥ Y) = Z ⬝ᵥ Y := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsq, hinv2, dotProduct_comm]
  have hyz : ((y ⬝ᵥ z : ℤ) : ℚ) = Y ⬝ᵥ Z := by simp [dotProduct, hY, hZ]
  have hzz : ((z ⬝ᵥ (A *ᵥ z) : ℤ) : ℚ) = Z ⬝ᵥ (G *ᵥ Z) := by
    have := cast_mulVec A z
    simp only [dotProduct, Int.cast_sum, Int.cast_mul]
    rw [hG]
    have h2 := congrFun this
    simp only [hZ] at *
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← h2 i]
  unfold dualNorm
  rw [← hY, ← hG]
  rw [h1, Matrix.mulVec_add, hinv, dotProduct_add, add_dotProduct, add_dotProduct, hcomm, hyz, hzz,
    dotProduct_comm Z Y, dotProduct_comm (G *ᵥ Z) Z]
  ring

theorem exists_eq_mulVec {A : Matrix (Fin n) (Fin n) ℤ} {y y' : Fin n → ℤ}
    (h : (QuotientAddGroup.mk y : DiscGroup A) = QuotientAddGroup.mk y') : ∃ z, y' = y + A *ᵥ z := by
  rw [QuotientAddGroup.eq, mem_gramLat] at h
  obtain ⟨z, hz⟩ := h
  exact ⟨z, by rw [hz]; abel⟩

/-- **Norms in a coset are congruent mod 1** (§11, remark 1, p. 280): if $y \equiv y' \pmod{A\mathbb Z^n}$, i.e. the vectors
$A^{-1}y, A^{-1}y' \in L^*$ lie in the same coset of $L$, then their norms differ by an integer. -/
@[kb "conwaysloane1988" "§11, remark 1, p. 280"]
theorem dualNorm_congr_one {A : Matrix (Fin n) (Fin n) ℤ} (hs : Aᵀ = A) (hd : A.det ≠ 0) {y y' : Fin n → ℤ}
    (h : (QuotientAddGroup.mk y : DiscGroup A) = QuotientAddGroup.mk y') :
    ∃ k : ℤ, dualNorm A y' = dualNorm A y + (1 : ℕ) * k := by
  obtain ⟨z, rfl⟩ := exists_eq_mulVec h
  refine ⟨2 * (y ⬝ᵥ z) + z ⬝ᵥ (A *ᵥ z), ?_⟩
  rw [dualNorm_add_mulVec hs hd]
  push_cast
  ring

/-- Even Gram matrix: all diagonal entries even (type II). -/
def EvenGram (A : Matrix (Fin n) (Fin n) ℤ) : Prop := ∀ i, Even (A i i)

theorem two_dvd_evalIn {R : Type*} [CommRing R] (Q : QuadForm R n) (h : ∀ i j, (2 : R) ∣ Q.coeff i j)
    (K : Type*) [CommRing K] [Algebra R K] (x : Fin n → K) : (2 : K) ∣ Q.evalIn K x := by
  unfold QuadForm.evalIn
  refine Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => ?_
  split_ifs
  · obtain ⟨d, hd⟩ := h i j
    rw [hd, map_mul, map_ofNat]
    exact Dvd.intro (algebraMap R K d * x i * x j) (by ring)
  · exact dvd_zero _

theorem coeff_even {A : Matrix (Fin n) (Fin n) ℤ} (hs : Aᵀ = A) (he : EvenGram A) (i j : Fin n) :
    (2 : ℤ) ∣ (ofMatrixZ A).coeff i j := by
  simp only [ofMatrixZ, Matrix.of_apply]
  split_ifs with h1 h2
  · have : A j i = A i j := by
      have := congrFun (congrFun hs i) j
      simpa using this
    exact ⟨A i j, by rw [this]; ring⟩
  · subst h2; exact (he i).two_dvd
  · exact dvd_zero _

/-- **Norms in a coset of an even lattice are congruent mod 2** (§11, remark 1, p. 280). -/
@[kb "conwaysloane1988" "§11, remark 1, p. 280"]
theorem dualNorm_congr_even {A : Matrix (Fin n) (Fin n) ℤ} (hs : Aᵀ = A) (hd : A.det ≠ 0) (he : EvenGram A)
    {y y' : Fin n → ℤ} (h : (QuotientAddGroup.mk y : DiscGroup A) = QuotientAddGroup.mk y') :
    ∃ k : ℤ, dualNorm A y' = dualNorm A y + (2 : ℕ) * k := by
  obtain ⟨z, rfl⟩ := exists_eq_mulVec h
  obtain ⟨w, hw⟩ := two_dvd_evalIn (ofMatrixZ A) (coeff_even hs he) ℤ z
  have hw' : z ⬝ᵥ (A *ᵥ z) = 2 * w := by rw [← eval_ofMatrixZ]; exact hw
  refine ⟨(y ⬝ᵥ z) + w, ?_⟩
  rw [dualNorm_add_mulVec hs hd, hw']
  push_cast
  ring

/-- **The discriminant form** $L^*/L \to \mathbb Q/T\mathbb Z$, $[y] \mapsto y^{\mathsf T}A^{-1}y \bmod T$, given the proof `hT`
that the norms in a coset are congruent mod $T$ (`dualNorm_congr_one` for $T = 1$; `dualNorm_congr_even` for $T = 2$, $A$ even). -/
@[kb "conwaysloane1988" "§11, remark 1, p. 280"]
noncomputable def discNorm (A : Matrix (Fin n) (Fin n) ℤ) (T : ℕ)
    (hT : ∀ y y' : Fin n → ℤ, (QuotientAddGroup.mk y : DiscGroup A) = QuotientAddGroup.mk y' →
      ∃ k : ℤ, dualNorm A y' = dualNorm A y + (T : ℕ) * k) :
    DiscGroup A → ℚ ⧸ AddSubgroup.zmultiples (T : ℚ) :=
  fun x => Quotient.liftOn' x
    (fun y => (QuotientAddGroup.mk (dualNorm A y) : ℚ ⧸ AddSubgroup.zmultiples (T : ℚ))) (by
      intro a b hab
      have h : (QuotientAddGroup.mk a : DiscGroup A) = QuotientAddGroup.mk b :=
        QuotientAddGroup.eq.2 (QuotientAddGroup.leftRel_apply.1 hab)
      obtain ⟨k, hk⟩ := hT a b h
      show (QuotientAddGroup.mk (dualNorm A a) : ℚ ⧸ AddSubgroup.zmultiples (T : ℚ)) =
        QuotientAddGroup.mk (dualNorm A b)
      rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
      exact ⟨k, by rw [hk]; simp [zsmul_eq_mul]; ring⟩)

theorem discNorm_mk (A : Matrix (Fin n) (Fin n) ℤ) (T : ℕ) (hT) (y : Fin n → ℤ) :
    discNorm A T hT (QuotientAddGroup.mk y) = QuotientAddGroup.mk (dualNorm A y) := rfl

/-! ### Types, isomorphisms of discriminant forms, and the four lemmas -/

open Classical in
/-- **The type** $T$ of a lattice: $2$ if it is even (type II: all $A_{ii}$ even), $1$ otherwise (type I). -/
noncomputable def gramType (A : Matrix (Fin n) (Fin n) ℤ) : ℕ := if EvenGram A then 2 else 1

theorem gramType_eq_one_or_two (A : Matrix (Fin n) (Fin n) ℤ) : gramType A = 1 ∨ gramType A = 2 := by
  unfold gramType; split_ifs <;> simp

/-- **An isomorphism $L^*/L \cong M^*/M$ preserving norms mod $T$**: an additive isomorphism $\varphi$ such that, whenever
$\varphi[y] = [z]$, the norms $z^{\mathsf T}B^{-1}z$ and $y^{\mathsf T}A^{-1}y$ differ by an element of $T\mathbb Z$. -/
def DiscIso (T : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ φ : DiscGroup A ≃+ DiscGroup B, ∀ y z : Fin n → ℤ, φ (QuotientAddGroup.mk y) = QuotientAddGroup.mk z →
    ∃ k : ℤ, dualNorm B z = dualNorm A y + (T : ℕ) * k

/-- $H = \begin{pmatrix}0&1\\1&0\end{pmatrix}$, the hyperbolic plane. -/
def hypGram : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/-- $I_1 = (1)$, the one-dimensional unimodular lattice. -/
def oneGram : Matrix (Fin 1) (Fin 1) ℤ := 1

/-- **Lemma 1** (§11, p. 280), as a named statement (**stated without proof in the paper**; Kneser–Puppe 1953): two (positive
definite integral) lattices $f, g$ with Gram matrices $A, B$ are in the same genus iff $f \oplus H$ and $g \oplus H$ are
integrally equivalent. Lean conventions: see the module docstring. -/
@[kb "conwaysloane1988" "§11, Lemma 1, p. 280"]
structure Lemma1Statement : Prop where
  iff : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ), PosDefGram A → PosDefGram B →
    (SameGenus (ofMatrixZ A) (ofMatrixZ B) ↔
      IntEquiv (ofMatrixZ (blockMat A 0 0 hypGram)) (ofMatrixZ (blockMat B 0 0 hypGram)))

/-- **Lemma 2** (§11, p. 280), as a named statement (**stated without proof in the paper**; Kneser–Puppe 1953): $L$ and $M$
are in the same genus iff they have the same dimension (automatic here) and the same type $T$ and there is an isomorphism
$L^*/L \cong M^*/M$ preserving norms mod $T$. -/
@[kb "conwaysloane1988" "§11, Lemma 2, p. 280"]
structure Lemma2Statement : Prop where
  iff : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ), PosDefGram A → PosDefGram B →
    (SameGenus (ofMatrixZ A) (ofMatrixZ B) ↔ (gramType A = gramType B ∧ DiscIso (gramType A) A B))

/-- **Lemma 3** (§11, p. 280), as a named statement (**stated without proof in the paper**; Kneser–Puppe 1953): if
$L \oplus I_1$ and $M \oplus I_1$ are in the same genus then so are $L$ and $M$, provided they have the same type. -/
@[kb "conwaysloane1988" "§11, Lemma 3, p. 280"]
structure Lemma3Statement : Prop where
  imp : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ), PosDefGram A → PosDefGram B →
    SameGenus (ofMatrixZ (blockMat A 0 0 oneGram)) (ofMatrixZ (blockMat B 0 0 oneGram)) →
    gramType A = gramType B → SameGenus (ofMatrixZ A) (ofMatrixZ B)

/-- **Lemma 4** (§11, p. 280), as a named statement (**stated without proof in the paper**; Kneser–Puppe 1953): $L$ and $M$
are in the same genus iff they have the same dimension (automatic here) and type and there is an isomorphism
$L^*/L \cong M^*/M$ preserving norms mod $1$. -/
@[kb "conwaysloane1988" "§11, Lemma 4, p. 280"]
structure Lemma4Statement : Prop where
  iff : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ), PosDefGram A → PosDefGram B →
    (SameGenus (ofMatrixZ A) (ofMatrixZ B) ↔ (gramType A = gramType B ∧ DiscIso 1 A B))

/-! ### Same genus implies same type -/

theorem even_of_sameGenus {A B : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hAe : EvenGram A)
    (h : SameGenus (ofMatrixZ A) (ofMatrixZ B)) : EvenGram B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := h.1 2
  intro i
  have h1 := hg (Pi.single i 1)
  have hdvd : (2 : ℤ_[2]) ∣ (((ofMatrixZ A).map (Int.castRingHom ℤ_[2])).eval (g.val *ᵥ Pi.single i 1)) := by
    refine two_dvd_evalIn _ (fun a b => ?_) ℤ_[2] _
    have := coeff_even hA hAe a b
    obtain ⟨d, hd⟩ := this
    exact ⟨(d : ℤ_[2]), by simp [QuadForm.map, hd]⟩
  rw [h1] at hdvd
  have hev : ((ofMatrixZ B).map (Int.castRingHom ℤ_[2])).eval (Pi.single i 1) = ((B i i : ℤ) : ℤ_[2]) := by
    have := QuadForm.evalIn_eq_dotProduct ℤ_[2] ((ofMatrixZ B).map (Int.castRingHom ℤ_[2])) (Pi.single i 1)
    refine this.trans ?_
    simp [QuadForm.map, ofMatrixZ]
  rw [hev] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  have h2 := congrArg (PadicInt.toZMod (p := 2)) hc
  simp only [map_intCast, map_mul, map_ofNat] at h2
  have h3 : ((B i i : ℤ) : ZMod 2) = 0 := by
    rw [h2]; have : (2 : ZMod 2) = 0 := rfl
    rw [this]; simp
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
  exact even_iff_two_dvd.2 (by exact_mod_cast h3)

/-- **Forms in the same genus have the same type** (even/odd is a $2$-adic invariant). -/
@[kb "conwaysloane1988" "§11, Lemma 2 (the type T)"]
theorem gramType_eq_of_sameGenus {A B : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (h : SameGenus (ofMatrixZ A) (ofMatrixZ B)) : gramType A = gramType B := by
  classical
  have h1 : EvenGram A → EvenGram B := fun he => even_of_sameGenus hA he h
  have h2 : EvenGram B → EvenGram A := fun he => even_of_sameGenus hB he h.symm
  unfold gramType
  by_cases hAe : EvenGram A
  · rw [if_pos hAe, if_pos (h1 hAe)]
  · rw [if_neg hAe, if_neg (fun hb => hAe (h2 hb))]

/-- **Lemma 4 implies the "if" half of Lemma 2**: same type $T$ and an isomorphism preserving norms mod $T$ (hence mod $1$)
give the same genus. -/
theorem sameGenus_of_lemma4 (h4 : Lemma4Statement) {A B : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A)
    (hB : PosDefGram B) (ht : gramType A = gramType B) (hi : DiscIso (gramType A) A B) :
    SameGenus (ofMatrixZ A) (ofMatrixZ B) := by
  refine (h4.iff n A B hA hB).2 ⟨ht, ?_⟩
  obtain ⟨φ, hφ⟩ := hi
  refine ⟨φ, fun y z hyz => ?_⟩
  obtain ⟨k, hk⟩ := hφ y z hyz
  exact ⟨(gramType A : ℤ) * k, by rw [hk]; push_cast; simp⟩

theorem DiscIso.one {T : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ} (h : DiscIso T A B) : DiscIso 1 A B := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ, fun y z hyz => ?_⟩
  obtain ⟨k, hk⟩ := hφ y z hyz
  exact ⟨(T : ℤ) * k, by rw [hk]; push_cast; simp⟩

/-! ### Adjoining $I_1$ -/

/-- $L \oplus I_1$: the Gram matrix `blockMat A 0 0 oneGram` in `Fin (n + 1)`. -/
noncomputable def sumOne (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  blockMat A 0 0 oneGram

theorem sumOne_mulVec_left {R : Type*} [CommRing R] (P : Matrix (Fin n) (Fin n) R)
    (v : Fin (n + 1) → R) (i : Fin n) :
    (blockMat P 0 0 (1 : Matrix (Fin 1) (Fin 1) R) *ᵥ v) (Fin.castAdd 1 i)
      = (P *ᵥ fun a => v (Fin.castAdd 1 a)) i := by
  simp [mulVec, dotProduct, Fin.sum_univ_add]

theorem sumOne_mulVec_last {R : Type*} [CommRing R] (P : Matrix (Fin n) (Fin n) R)
    (v : Fin (n + 1) → R) :
    (blockMat P 0 0 (1 : Matrix (Fin 1) (Fin 1) R) *ᵥ v) (Fin.natAdd n 0) = v (Fin.natAdd n 0) := by
  simp [mulVec, dotProduct, Fin.sum_univ_add]

theorem sumOne_eq (A : Matrix (Fin n) (Fin n) ℤ) :
    sumOne A = blockMat A 0 0 (1 : Matrix (Fin 1) (Fin 1) ℤ) := rfl

theorem gramQ_sumOne (A : Matrix (Fin n) (Fin n) ℤ) :
    gramQ (sumOne A) = blockMat (gramQ A) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
  unfold gramQ
  rw [sumOne_eq, blockMat_map]
  simp

theorem PosDefGram.sumOne {A : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) : PosDefGram (sumOne A) := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [sumOne_eq, blockMat_transpose]; simp [hA.1]
  · rw [gramQ_sumOne]
    have key : x ⬝ᵥ (blockMat (gramQ A) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ x)
        = (fun a => x (Fin.castAdd 1 a)) ⬝ᵥ (gramQ A *ᵥ fun a => x (Fin.castAdd 1 a))
          + (x (Fin.natAdd n 0)) ^ 2 := by
      simp only [dotProduct, Fin.sum_univ_add, Fin.sum_univ_one, sumOne_mulVec_left, sumOne_mulVec_last]
      simp [sq]
    rw [key]
    by_cases h1 : (fun a => x (Fin.castAdd 1 a)) = 0
    · have hl : x (Fin.natAdd n 0) ≠ 0 := by
        intro h0
        apply hx
        funext i
        refine Fin.addCases (fun a => ?_) (fun b => ?_) i
        · exact congrFun h1 a
        · rw [Fin.fin_one_eq_zero b]; exact h0
      rw [h1]
      simp only [Matrix.mulVec_zero, dotProduct_zero, zero_add]
      positivity
    · have := hA.2 _ h1
      have h2 : 0 ≤ (x (Fin.natAdd n 0)) ^ 2 := sq_nonneg _
      linarith

theorem gramType_sumOne (A : Matrix (Fin n) (Fin n) ℤ) : gramType (sumOne A) = 1 := by
  classical
  unfold gramType
  rw [if_neg]
  intro h
  have := h (Fin.natAdd n 0)
  rw [sumOne_eq] at this
  simp at this

theorem dualNorm_sumOne {A : Matrix (Fin n) (Fin n) ℤ} (hd : A.det ≠ 0) (y : Fin (n + 1) → ℤ) :
    dualNorm (sumOne A) y
      = dualNorm A (fun a => y (Fin.castAdd 1 a)) + ((y (Fin.natAdd n 0) : ℤ) : ℚ) ^ 2 := by
  have hdet : (sumOne A).det ≠ 0 := by
    rw [sumOne_eq, det_blockMat_diag]; simp [hd]
  have hu : IsUnit (gramQ (sumOne A)).det := (gramQ_det_ne hdet).isUnit
  have huA : IsUnit (gramQ A).det := (gramQ_det_ne hd).isUnit
  set Y : Fin (n + 1) → ℚ := fun i => (y i : ℚ) with hY
  set w := (gramQ (sumOne A))⁻¹ *ᵥ Y with hwdef
  have hw : gramQ (sumOne A) *ᵥ w = Y := by
    rw [hwdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  rw [gramQ_sumOne] at hw
  have hfirst : ∀ i : Fin n, (gramQ A *ᵥ fun a => w (Fin.castAdd 1 a)) i = (y (Fin.castAdd 1 i) : ℚ) := fun i => by
    have := congrFun hw (Fin.castAdd 1 i)
    rw [sumOne_mulVec_left] at this
    exact this
  have hlast : w (Fin.natAdd n 0) = (y (Fin.natAdd n 0) : ℚ) := by
    have := congrFun hw (Fin.natAdd n 0)
    rw [sumOne_mulVec_last] at this
    exact this
  have hw1 : (fun a => w (Fin.castAdd 1 a)) = (gramQ A)⁻¹ *ᵥ fun a => (y (Fin.castAdd 1 a) : ℚ) := by
    have : (gramQ A *ᵥ fun a => w (Fin.castAdd 1 a)) = fun a => (y (Fin.castAdd 1 a) : ℚ) := funext hfirst
    rw [← this, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ huA, Matrix.one_mulVec]
  have hsplit : Y ⬝ᵥ w = ∑ i : Fin n, Y (Fin.castAdd 1 i) * w (Fin.castAdd 1 i)
      + Y (Fin.natAdd n 0) * w (Fin.natAdd n 0) := by
    simp [dotProduct, Fin.sum_univ_add]
  show Y ⬝ᵥ w = _
  rw [hsplit, hlast]
  have e : ∑ i : Fin n, Y (Fin.castAdd 1 i) * w (Fin.castAdd 1 i)
      = dualNorm A (fun a => y (Fin.castAdd 1 a)) := by
    unfold dualNorm
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hw1]
  rw [e]
  simp [hY, sq]

/-- Restriction to the first $n$ coordinates. -/
def restr (y : Fin (n + 1) → ℤ) : Fin n → ℤ := fun a => y (Fin.castAdd 1 a)

theorem restr_mulVec (A : Matrix (Fin n) (Fin n) ℤ) (z : Fin (n + 1) → ℤ) :
    restr (sumOne A *ᵥ z) = A *ᵥ restr z := by
  funext i
  rw [sumOne_eq]
  exact sumOne_mulVec_left A z i

/-- Restriction as an additive map. -/
def restrHom : (Fin (n + 1) → ℤ) →+ (Fin n → ℤ) := AddMonoidHom.mk' restr (fun _ _ => rfl)

theorem gramLat_sumOne_le (A : Matrix (Fin n) (Fin n) ℤ) :
    gramLat (sumOne A) ≤ (gramLat A).comap restrHom := by
  intro y hy
  obtain ⟨z, rfl⟩ := mem_gramLat.1 hy
  exact mem_gramLat.2 ⟨restr z, (restr_mulVec A z).symm⟩

/-- **$(L \oplus I_1)^*/(L \oplus I_1) \cong L^*/L$**: forget the last coordinate. -/
noncomputable def discSumOne (A : Matrix (Fin n) (Fin n) ℤ) : DiscGroup (sumOne A) ≃+ DiscGroup A :=
  AddEquiv.ofBijective (QuotientAddGroup.map _ _ restrHom (gramLat_sumOne_le A))
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro q hq
      induction q using QuotientAddGroup.induction_on with
      | H y =>
        rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff, mem_gramLat] at hq
        obtain ⟨z0, hz0⟩ := hq
        rw [QuotientAddGroup.eq_zero_iff, mem_gramLat]
        refine ⟨Fin.append z0 (fun _ => y (Fin.natAdd n 0)), ?_⟩
        funext i
        refine Fin.addCases (fun a => ?_) (fun b => ?_) i
        · have h1 := congrFun (restr_mulVec A (Fin.append z0 (fun _ : Fin 1 => y (Fin.natAdd n 0)))) a
          have h2 : restr (Fin.append z0 (fun _ : Fin 1 => y (Fin.natAdd n 0))) = z0 := by
            funext c; simp [restr]
          rw [h2, hz0] at h1
          exact h1
        · rw [Fin.fin_one_eq_zero b, sumOne_eq]
          rw [sumOne_mulVec_last]
          simp,
     by
      intro q
      induction q using QuotientAddGroup.induction_on with
      | H y0 =>
        refine ⟨QuotientAddGroup.mk (Fin.append y0 (fun _ => 0)), ?_⟩
        rw [QuotientAddGroup.map_mk]
        congr 1
        funext c
        show Fin.append y0 (fun _ : Fin 1 => (0 : ℤ)) (Fin.castAdd 1 c) = y0 c
        simp⟩

theorem discSumOne_mk (A : Matrix (Fin n) (Fin n) ℤ) (y : Fin (n + 1) → ℤ) :
    discSumOne A (QuotientAddGroup.mk y) = QuotientAddGroup.mk (restr y) := rfl

/-- If $L^*/L \cong M^*/M$ preserving norms mod $1$, then $(L \oplus I_1)^*/(L\oplus I_1) \cong (M \oplus I_1)^*/(M \oplus I_1)$
preserving norms mod $1$. -/
theorem DiscIso.sumOne {A B : Matrix (Fin n) (Fin n) ℤ} (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (h : DiscIso 1 A B) : DiscIso 1 (sumOne A) (sumOne B) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨((discSumOne A).trans φ).trans (discSumOne B).symm, fun y z hyz => ?_⟩
  have hz : (discSumOne B) (QuotientAddGroup.mk z) = φ (discSumOne A (QuotientAddGroup.mk y)) := by
    rw [← hyz]; simp
  rw [discSumOne_mk, discSumOne_mk] at hz
  obtain ⟨k, hk⟩ := hφ (restr y) (restr z) hz.symm
  refine ⟨k + ((z (Fin.natAdd n 0)) ^ 2 - (y (Fin.natAdd n 0)) ^ 2), ?_⟩
  rw [dualNorm_sumOne hB, dualNorm_sumOne hA]
  have := hk
  unfold restr at this
  rw [this]
  push_cast
  ring

/-! ### Lemma 2 and Lemma 3 give Lemma 4 -/

/-- **Combining Lemmas 2 and 3** (§11, p. 280: "by combining lemmas 2 and 3 we can strengthen lemma 2"): Lemma 2 and Lemma 3
together imply Lemma 4. For an even lattice one applies Lemma 2 to $L \oplus I_1$ and $M \oplus I_1$ (which are odd and have
the same discriminant form mod $1$ as $L$, $M$) and then Lemma 3. -/
@[kb "conwaysloane1988" "§11, Lemma 4 (from Lemmas 2 and 3), p. 280"]
theorem lemma4_of_lemma2_lemma3 (h2 : Lemma2Statement) (h3 : Lemma3Statement) : Lemma4Statement := by
  refine ⟨fun n A B hA hB => ⟨fun hg => ?_, fun ⟨ht, hi⟩ => ?_⟩⟩
  · obtain ⟨ht, hi⟩ := (h2.iff n A B hA hB).1 hg
    exact ⟨ht, hi.one⟩
  · rcases gramType_eq_one_or_two A with h1 | h1
    · refine (h2.iff n A B hA hB).2 ⟨ht, ?_⟩
      rw [h1]; exact hi
    · have hA' := hA.sumOne
      have hB' := hB.sumOne
      have hg' : SameGenus (ofMatrixZ (sumOne A)) (ofMatrixZ (sumOne B)) := by
        refine (h2.iff (n + 1) _ _ hA' hB').2 ⟨by rw [gramType_sumOne, gramType_sumOne], ?_⟩
        rw [gramType_sumOne]
        exact hi.sumOne hA.det_ne hB.det_ne
      exact h3.imp n A B hA hB hg' ht

/-! ### Determinant $2$ (§11, remark 3, p. 281) -/

theorem gramQ_transpose {A : Matrix (Fin n) (Fin n) ℤ} (hs : Aᵀ = A) : (gramQ A)ᵀ = gramQ A := by
  unfold gramQ; rw [← Matrix.transpose_map, hs]

/-- **Key step of remark 3.** Let $\det A = 2$, $Az = 2y$ (so $v = z/2 = A^{-1}y \in L^*$, and $z = \operatorname{adj}(A)y$ always
works). If $v \cdot v = \tfrac12 y\cdot z$ is an integer, then every $z_j$ is even, i.e. $v \in L$. (Proof: the vectors
$e_i$ ($i \ne j$) and $v$ have the Gram matrix $P^{\mathsf T}GP$, which would be integral with determinant
$\det A\cdot v_j^2 = z_j^2/2$; this is the formalization of "$\langle L, v\rangle$ would be an integral lattice of determinant $\tfrac12$".) -/
theorem even_of_integral_norm {A : Matrix (Fin n) (Fin n) ℤ} (hs : Aᵀ = A) (hdet : A.det = 2)
    {y z : Fin n → ℤ} (hz : A *ᵥ z = 2 • y) {m : ℤ} (hm : ((y ⬝ᵥ z : ℤ) : ℚ) / 2 = m) (j : Fin n) :
    Even (z j) := by
  classical
  have hsq : (gramQ A)ᵀ = gramQ A := gramQ_transpose hs
  set G := gramQ A with hG
  set Y : Fin n → ℚ := fun i => (y i : ℚ) with hY
  set v : Fin n → ℚ := fun i => (z i : ℚ) / 2 with hv
  have hGv : G *ᵥ v = Y := by
    have h1 := cast_mulVec A z
    have e : v = (1 / 2 : ℚ) • (fun i => (z i : ℚ)) := by ext i; simp [hv]; ring
    rw [e, Matrix.mulVec_smul, ← h1, hz]
    ext i
    simp [hY]
  have hvY : v ⬝ᵥ Y = m := by
    rw [← hm]
    simp only [dotProduct, hv, hY, Int.cast_sum, Int.cast_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => by ring
  set P : Matrix (Fin n) (Fin n) ℚ := (1 : Matrix (Fin n) (Fin n) ℚ).updateCol j v with hP
  set N : Matrix (Fin n) (Fin n) ℚ := G.updateCol j Y with hN
  have hPt : Pᵀ = (1 : Matrix (Fin n) (Fin n) ℚ).updateRow j v := by
    rw [hP, ← Matrix.updateRow_transpose, Matrix.transpose_one]
  have hmain : Pᵀ * G * P = N.updateRow j (v ᵥ* N) := by
    rw [Matrix.mul_assoc, hP, Matrix.mul_updateCol, Matrix.mul_one, hGv, hPt, Matrix.updateRow_mul,
      Matrix.one_mul]
  have hvG : ∀ b, (v ᵥ* G) b = Y b := fun b => by
    rw [← Matrix.mulVec_transpose, hsq, hGv]
  have hent : ∀ a b, ∃ t : ℤ, (Pᵀ * G * P) a b = (t : ℚ) := by
    intro a b
    rw [hmain]
    by_cases ha : a = j
    · subst ha
      by_cases hb : b = a
      · subst hb
        refine ⟨m, ?_⟩
        simp only [Matrix.updateRow_self, Matrix.vecMul, hN, Matrix.updateCol_apply, if_true]
        exact hvY
      · refine ⟨y b, ?_⟩
        simp only [Matrix.updateRow_self, Matrix.vecMul, hN, Matrix.updateCol_apply, if_neg hb]
        have := hvG b
        simp only [Matrix.vecMul, hY] at this
        simpa [dotProduct] using this
    · by_cases hb : b = j
      · subst hb
        refine ⟨y a, ?_⟩
        simp [Matrix.updateRow_ne ha, hN, Matrix.updateCol_apply, hY]
      · refine ⟨A a b, ?_⟩
        simp [Matrix.updateRow_ne ha, hN, Matrix.updateCol_apply, hb, hG, gramQ]
  choose M0 hM0 using hent
  let M : Matrix (Fin n) (Fin n) ℤ := Matrix.of M0
  have hM : ∀ a b, (Pᵀ * G * P) a b = (M a b : ℚ) := hM0
  have hMat : Pᵀ * G * P = (M.map (Int.castRingHom ℚ)) := by
    ext a b; simp [hM]
  have hdetP : P.det = v j := by
    rw [hP, ← Matrix.cramer_apply, Matrix.cramer_one]; rfl
  have hdetG : G.det = 2 := by
    have := RingHom.map_det (Int.castRingHom ℚ) A
    rw [hdet] at this
    simpa [hG, gramQ] using this.symm
  have hdet' : (M.det : ℚ) = (v j) ^ 2 * 2 := by
    have h1 := congrArg Matrix.det hMat
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetP, hdetG] at h1
    have h2 : (M.map (Int.castRingHom ℚ)).det = (M.det : ℚ) := by
      have := RingHom.map_det (Int.castRingHom ℚ) M
      simpa using this.symm
    rw [h2] at h1
    rw [← h1]; ring
  have hz2 : ((z j : ℤ) : ℚ) ^ 2 = 2 * (M.det : ℚ) := by
    rw [hdet']; simp only [hv]; ring
  have hz3 : (z j) ^ 2 = 2 * M.det := by exact_mod_cast hz2
  have hdvd : (2 : ℤ) ∣ z j := Int.prime_two.dvd_of_dvd_pow (n := 2) ⟨M.det, hz3⟩
  exact even_iff_two_dvd.2 hdvd

/-- For $\det A = 2$: $2y = Az$ with $z = \operatorname{adj}(A)y$, and the norm is $\tfrac12\, y\cdot z$. -/
theorem exists_half_vector {A : Matrix (Fin n) (Fin n) ℤ} (hs : Aᵀ = A) (hdet : A.det = 2) (y : Fin n → ℤ) :
    ∃ z : Fin n → ℤ, A *ᵥ z = 2 • y ∧ dualNorm A y = ((y ⬝ᵥ z : ℤ) : ℚ) / 2 := by
  classical
  refine ⟨Matrix.adjugate A *ᵥ y, ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i; simp
  · set z := Matrix.adjugate A *ᵥ y with hzdef
    have hz : A *ᵥ z = 2 • y := by
      rw [hzdef, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet, Matrix.smul_mulVec, Matrix.one_mulVec]
      ext i; simp
    have hu : IsUnit (gramQ A).det := (gramQ_det_ne (by rw [hdet]; norm_num)).isUnit
    set G := gramQ A with hG
    set Y : Fin n → ℚ := fun i => (y i : ℚ) with hY
    set v : Fin n → ℚ := fun i => (z i : ℚ) / 2 with hv
    have hGv : G *ᵥ v = Y := by
      have h1 := cast_mulVec A z
      have e : v = (1 / 2 : ℚ) • (fun i => (z i : ℚ)) := by ext i; simp [hv]; ring
      rw [e, Matrix.mulVec_smul, ← h1, hz]
      ext i
      simp [hY]
    have hinv : G⁻¹ *ᵥ Y = v := by
      rw [← hGv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    unfold dualNorm
    rw [← hY, ← hG, hinv]
    simp only [dotProduct, hY, hv, Int.cast_sum, Int.cast_mul, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- A group $\mathbb Z^n/A\mathbb Z^n$ with $\det A \ne \pm1$ is nontrivial. -/
theorem mk_ne_zero_of_generator {A : Matrix (Fin n) (Fin n) ℤ} (hdet : A.det = 2) {y : Fin n → ℤ}
    (hgen : ∀ q : DiscGroup A, ∃ k : ℤ, q = k • (QuotientAddGroup.mk y : DiscGroup A)) :
    (QuotientAddGroup.mk y : DiscGroup A) ≠ 0 := by
  intro h0
  have hall : ∀ i : Fin n, ∃ w : Fin n → ℤ, A *ᵥ w = Pi.single i 1 := fun i => by
    obtain ⟨k, hk⟩ := hgen (QuotientAddGroup.mk (Pi.single i 1))
    rw [h0, smul_zero, QuotientAddGroup.eq_zero_iff, mem_gramLat] at hk
    exact hk
  choose w hw using hall
  have hAW : A * Matrix.of (fun r i => w i r) = 1 := by
    ext r i
    have := congrFun (hw i) r
    simp only [Matrix.mul_apply, Matrix.of_apply]
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm] using this
  have := congrArg Matrix.det hAW
  rw [Matrix.det_mul, hdet, Matrix.det_one] at this
  omega

/-- **§11, remark 3, p. 281.** If $\det L = 2$ and $v_2$ generates $L^*/L$ (here $v_2 = A^{-1}y$ with $[y]$ a generator), then
$v_2\cdot v_2 \equiv \tfrac12 \pmod 1$. (If $v_2\cdot v_2$ were an integer, $\langle L, v_2\rangle$ would be an integral lattice of
determinant $\tfrac12$: `even_of_integral_norm`.) Only the symmetry of $A$ and $\det A = 2$ are needed (not positivity). -/
@[kb "conwaysloane1988" "§11, remark 3, p. 281"]
theorem norm_generator_det_two {A : Matrix (Fin n) (Fin n) ℤ} (hs : Aᵀ = A) (hdet : A.det = 2) {y : Fin n → ℤ}
    (hgen : ∀ q : DiscGroup A, ∃ k : ℤ, q = k • (QuotientAddGroup.mk y : DiscGroup A)) :
    ∃ k : ℤ, dualNorm A y = 1 / 2 + k := by
  have hy := mk_ne_zero_of_generator hdet hgen
  obtain ⟨z, hz, hN⟩ := exists_half_vector hs hdet y
  rcases Int.even_or_odd' (y ⬝ᵥ z) with ⟨t, ht | ht⟩
  · exfalso
    have hm : ((y ⬝ᵥ z : ℤ) : ℚ) / 2 = t := by rw [ht]; push_cast; ring
    have hev := even_of_integral_norm hs hdet hz hm
    choose c hc using fun j => hev j
    apply hy
    rw [QuotientAddGroup.eq_zero_iff, mem_gramLat]
    refine ⟨c, ?_⟩
    funext i
    have h1 := congrFun hz i
    have h2 : (A *ᵥ z) i = 2 * (A *ᵥ c) i := by
      have : z = 2 • c := by funext j; simp [hc j]; ring
      rw [this, Matrix.mulVec_smul]; simp
    rw [h2] at h1
    have h3 : (2 : ℤ) * (A *ᵥ c) i = 2 * y i := by simpa using h1
    omega
  · refine ⟨t, ?_⟩
    rw [hN, ht]; push_cast; ring

/-! ### Lattices of determinant $2$ in the same genus -/

theorem mulVecLin_injective {A : Matrix (Fin n) (Fin n) ℤ} (hd : A.det ≠ 0) :
    Function.Injective A.mulVecLin := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : A *ᵥ x = 0 := hx
  have h2 : A.det • x = 0 := by
    have := congrArg (fun w => Matrix.adjugate A *ᵥ w) h1
    simpa [Matrix.mulVec_mulVec, Matrix.adjugate_mul] using this
  funext i
  have := congrFun h2 i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact (mul_eq_zero.1 this).resolve_left hd

/-- $|L^*/L| = |\det A|$. -/
theorem card_discGroup {A : Matrix (Fin n) (Fin n) ℤ} (hd : A.det ≠ 0) :
    Nat.card (DiscGroup A) = A.det.natAbs := by
  let N : Submodule ℤ (Fin n → ℤ) := LinearMap.range A.mulVecLin
  let e : (Fin n → ℤ) ≃ₗ[ℤ] N := LinearEquiv.ofInjective A.mulVecLin (mulVecLin_injective hd)
  have h := Submodule.natAbs_det_equiv N e
  have h2 : (N.subtype ∘ₗ AddMonoidHom.toIntLinearMap ((e : (Fin n → ℤ) ≃ₗ[ℤ] N) : (Fin n → ℤ) →+ N))
      = Matrix.toLin' A := by
    apply LinearMap.ext
    intro x
    simp [N, e, Matrix.toLin'_apply]
  rw [h2, LinearMap.det_toLin'] at h
  rw [h]
  rfl

open Classical in
/-- The two groups of order $2$ are isomorphic, sending the nonzero element to the nonzero element. -/
noncomputable def orderTwoEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H] (g : G) (h : H) (hg0 : g ≠ 0) (hh0 : h ≠ 0)
    (hG : ∀ r : G, r = 0 ∨ r = g) (hH : ∀ r : H, r = 0 ∨ r = h) : G ≃+ H where
  toFun q := if q = g then h else 0
  invFun q := if q = h then g else 0
  left_inv q := by
    rcases hG q with rfl | rfl
    · simp [hg0.symm, hh0.symm]
    · simp
  right_inv q := by
    rcases hH q with rfl | rfl
    · simp [hg0.symm, hh0.symm]
    · simp
  map_add' a b := by
    have hgg : g + g = 0 := (hG (g + g)).resolve_right (fun e => hg0 (by simpa using e))
    have hhh : h + h = 0 := (hH (h + h)).resolve_right (fun e => hh0 (by simpa using e))
    rcases hG a with rfl | rfl <;> rcases hG b with rfl | rfl
    · simp [hg0.symm]
    · simp [hg0.symm]
    · simp [hg0.symm]
    · simp [hgg, hhh, hg0.symm]

theorem two_elements {G : Type*} [AddCommGroup G] (h : Nat.card G = 2) :
    ∃ g : G, g ≠ 0 ∧ ∀ r : G, r = 0 ∨ r = g := by
  obtain ⟨g, hg, huniq⟩ := (Nat.card_eq_two_iff' (0 : G)).1 h
  exact ⟨g, hg, fun r => by
    by_cases hr : r = 0
    · exact Or.inl hr
    · exact Or.inr (huniq r hr)⟩

/-- Two lattices of determinant $2$ have isomorphic discriminant groups, via an isomorphism preserving norms mod $1$
(by `norm_generator_det_two`: the generator has norm $\tfrac12$ in both). -/
theorem discIso_one_det_two {A B : Matrix (Fin n) (Fin n) ℤ} (hsA : Aᵀ = A) (hsB : Bᵀ = B)
    (hA : A.det = 2) (hB : B.det = 2) : DiscIso 1 A B := by
  have cA : Nat.card (DiscGroup A) = 2 := by rw [card_discGroup (by rw [hA]; norm_num), hA]; rfl
  have cB : Nat.card (DiscGroup B) = 2 := by rw [card_discGroup (by rw [hB]; norm_num), hB]; rfl
  obtain ⟨gA, hgA0, hgA⟩ := two_elements cA
  obtain ⟨gB, hgB0, hgB⟩ := two_elements cB
  obtain ⟨yA, rfl⟩ := QuotientAddGroup.mk_surjective gA
  obtain ⟨yB, rfl⟩ := QuotientAddGroup.mk_surjective gB
  have genA : ∀ q : DiscGroup A, ∃ k : ℤ, q = k • (QuotientAddGroup.mk yA : DiscGroup A) := fun q => by
    rcases hgA q with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  have genB : ∀ q : DiscGroup B, ∃ k : ℤ, q = k • (QuotientAddGroup.mk yB : DiscGroup B) := fun q => by
    rcases hgB q with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  obtain ⟨kA, hkA⟩ := norm_generator_det_two hsA hA genA
  obtain ⟨kB, hkB⟩ := norm_generator_det_two hsB hB genB
  have hdA : A.det ≠ 0 := by rw [hA]; norm_num
  have hdB : B.det ≠ 0 := by rw [hB]; norm_num
  have zeroA : ∀ y : Fin n → ℤ, (QuotientAddGroup.mk y : DiscGroup A) = 0 → ∃ k : ℤ, dualNorm A y = k := by
    intro y hy
    obtain ⟨k, hk⟩ := dualNorm_congr_one hsA hdA (y := 0) (y' := y) (by rw [hy]; simp)
    exact ⟨k, by rw [hk]; simp [dualNorm]⟩
  have zeroB : ∀ y : Fin n → ℤ, (QuotientAddGroup.mk y : DiscGroup B) = 0 → ∃ k : ℤ, dualNorm B y = k := by
    intro y hy
    obtain ⟨k, hk⟩ := dualNorm_congr_one hsB hdB (y := 0) (y' := y) (by rw [hy]; simp)
    exact ⟨k, by rw [hk]; simp [dualNorm]⟩
  refine ⟨orderTwoEquiv _ _ hgA0 hgB0 hgA hgB, fun y z hyz => ?_⟩
  rcases hgA (QuotientAddGroup.mk y) with h0 | h1
  · have hz : (QuotientAddGroup.mk z : DiscGroup B) = 0 := by
      rw [← hyz, h0]; exact map_zero _
    obtain ⟨k1, hk1⟩ := zeroA y h0
    obtain ⟨k2, hk2⟩ := zeroB z hz
    exact ⟨k2 - k1, by rw [hk1, hk2]; push_cast; ring⟩
  · have hz : (QuotientAddGroup.mk z : DiscGroup B) = QuotientAddGroup.mk yB := by
      rw [← hyz, h1]
      simp [orderTwoEquiv]
    obtain ⟨k1, hk1⟩ := dualNorm_congr_one hsA hdA (y := yA) (y' := y) h1.symm
    obtain ⟨k3, hk3⟩ := dualNorm_congr_one hsB hdB (y := yB) (y' := z) hz.symm
    exact ⟨k3 + kB - k1 - kA, by rw [hk1, hk3, hkA, hkB]; push_cast; ring⟩

/-- **§11, remark 3 (consequence).** Under Lemma 4, lattices of determinant $2$ (and the same dimension) are in the same genus as
soon as they have the same type; so there are at most two genera of determinant $2$, one for each type $T \in \{1, 2\}$. -/
@[kb "conwaysloane1988" "§11, remark 3, p. 281"]
theorem sameGenus_of_det_two (h4 : Lemma4Statement) {A B : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A)
    (hB : PosDefGram B) (dA : A.det = 2) (dB : B.det = 2) (ht : gramType A = gramType B) :
    SameGenus (ofMatrixZ A) (ofMatrixZ B) :=
  (h4.iff n A B hA hB).2 ⟨ht, discIso_one_det_two hA.1 hB.1 dA dB⟩

end QuadFormsKB.ConwaySloane.Mass

