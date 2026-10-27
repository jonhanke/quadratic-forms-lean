/-
# Split forms $\langle a\rangle \perp Q'$ and the stabilizer of a vector

**Layer:** coordinates. For a form $Q'$ in $n$ variables and a scalar $a$, the **split form**
$Q = \langle a\rangle \perp Q'$ in $n+1$ variables is $Q(x_0, x') = a x_0^2 + Q'(x')$, $x' = (x_1, \dots, x_n)$
(`splitForm`). The vector $e_0 = (1, 0, \dots, 0)$ has $Q(e_0) = a$ and $e_0^\perp = \{x_0 = 0\} \cong F^n$ carries $Q'$.

**Defines**
* `cornerMat c A` $= \begin{pmatrix} c & 0 \\ 0 & A\end{pmatrix}$ (indices $0$ and $1, \dots, n$; Lean's `Fin.cons`);
* `blockGL : GL_n(R) →* GL_{n+1}(R)`, $g \mapsto \mathrm{diag}(1, g)$, and its restriction
  `orthEmb R : O(Q')(R) →* O(Q)(R)` for every $F$-algebra $R$;
* `orthEmbAf : O(Q')(𝔸_f) →* O(Q)(𝔸_f)`, the same embedding on the finite adelic orthogonal groups (it maps
  $O(Q')(\mathfrak o_\mathfrak p)$ into $O(Q)(\mathfrak o_\mathfrak p)$).

**Proves**
* `hessian_splitForm`, `evalIn_splitForm`, `det_cornerMat`: $H_Q = \mathrm{diag}(2a, H_{Q'})$,
  $Q(t, x') = a t^2 + Q'(x')$, $\det H_Q = 2a\det H_{Q'}$;
* `exists_orthEmb_eq` (**the stabilizer of $e_0$**, over any field $K \supseteq F$ with $2a \ne 0$): every
  $\gamma \in O(Q)(K)$ with $\gamma e_0 = e_0$ is $\mathrm{diag}(1, g)$ with $g \in O(Q')(K)$. So
  $\mathrm{Stab}_{O(Q)}(e_0) = O(Q')$, i.e. $O(e_0^\perp)$ (Weil 1982, §3.4 [unverified]);
* `exists_orthGroup_mulVec_eq` (**Witt transitivity**): for $Q$ nondegenerate and $Q(v) = a \ne 0$ there is
  $\gamma \in O(Q)(F)$ with $\gamma e_0 = v$ (Witt's theorem, `QuadraticForm.exists_isometryEquiv_apply_eq_of_nondegenerate`);
* `orthEmbAf_diagF`, `mem_stdStab_orthEmb_iff`, `comap_orthEmbAf_locStab_intVec`: the adelic embedding is compatible
  with the rational points and $\mathrm{diag}(1, g)$ preserves $\mathfrak o_\mathfrak p^{n+1}$ iff $g$ preserves $\mathfrak o_\mathfrak p^n$;
  so the preimage of $O(\hat{\mathcal O}_F^{n+1})$ is $O(\hat{\mathcal O}_F^n)$.

Indices are $0$-based: the split-off coordinate is $x_0$, and $Q'$ sees $x_1, \dots, x_n$ as its $x_0, \dots, x_{n-1}$.
-/
import QuadFormsKB.Tamagawa.MassFormula
import QuadFormsKB.Witt.Bridge
import QuadFormsKB.Witt.Extension

open NumberField IsDedekindDomain Matrix
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices

/-! ### Corner matrices -/

section Corner

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **The corner matrix** $\mathrm{diag}(c, A) = \begin{pmatrix} c & 0 \\ 0 & A \end{pmatrix}$, $(n+1)\times(n+1)$, with
$c$ in position $(0, 0)$ and $A$ in rows and columns $1, \dots, n$. -/
def cornerMat (c : R) (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases c (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => A i' j') j) i

@[simp] theorem cornerMat_zero_zero (c : R) (A : Matrix (Fin n) (Fin n) R) : cornerMat c A 0 0 = c := rfl
@[simp] theorem cornerMat_zero_succ (c : R) (A : Matrix (Fin n) (Fin n) R) (j : Fin n) :
    cornerMat c A 0 j.succ = 0 := rfl
@[simp] theorem cornerMat_succ_zero (c : R) (A : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    cornerMat c A i.succ 0 = 0 := rfl
@[simp] theorem cornerMat_succ_succ (c : R) (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    cornerMat c A i.succ j.succ = A i j := rfl

theorem cornerMat_mul (c d : R) (A B : Matrix (Fin n) (Fin n) R) :
    cornerMat c A * cornerMat d B = cornerMat (c * d) (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem cornerMat_one : cornerMat (1 : R) (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem cornerMat_add (c d : R) (A B : Matrix (Fin n) (Fin n) R) :
    cornerMat c A + cornerMat d B = cornerMat (c + d) (A + B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem cornerMat_transpose (c : R) (A : Matrix (Fin n) (Fin n) R) :
    (cornerMat c A)ᵀ = cornerMat c Aᵀ := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem cornerMat_map {S : Type*} [CommRing S] (f : R →+* S) (c : R) (A : Matrix (Fin n) (Fin n) R) :
    (cornerMat c A).map f = cornerMat (f c) (A.map f) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem cornerMat_mulVec (c : R) (A : Matrix (Fin n) (Fin n) R) (t : R) (x : Fin n → R) :
    cornerMat c A *ᵥ (Fin.cons t x : Fin (n + 1) → R) = Fin.cons (c * t) (A *ᵥ x) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [mulVec, dotProduct, Fin.sum_univ_succ]

theorem det_cornerMat (c : R) (A : Matrix (Fin n) (Fin n) R) : (cornerMat c A).det = c * A.det := by
  rw [det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, cornerMat_zero_zero, cornerMat_zero_succ, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  congr 1

theorem cornerMat_injective_right {c d : R} {A B : Matrix (Fin n) (Fin n) R}
    (h : cornerMat c A = cornerMat d B) : A = B := by
  ext i j
  have := congrFun (congrFun h i.succ) j.succ
  simpa using this

/-- $g \mapsto \mathrm{diag}(1, g)$ as a monoid homomorphism of matrix rings. -/
def blockHom : Matrix (Fin n) (Fin n) R →* Matrix (Fin (n + 1)) (Fin (n + 1)) R where
  toFun g := cornerMat 1 g
  map_one' := cornerMat_one
  map_mul' a b := by rw [cornerMat_mul, one_mul]

/-- **The block embedding** $\mathrm{GL}_n(R) \to \mathrm{GL}_{n+1}(R)$, $g \mapsto \mathrm{diag}(1, g)$. -/
def blockGL : GL (Fin n) R →* GL (Fin (n + 1)) R := Units.map blockHom

@[simp] theorem blockGL_val (g : GL (Fin n) R) : ((blockGL g : GL (Fin (n + 1)) R) : Matrix _ _ R) =
    cornerMat 1 g.val := rfl

/-- $e_0 = (1, 0, \dots, 0)$. -/
abbrev e₀ : Fin (n + 1) → R := Fin.cons 1 0

theorem blockGL_mulVec_e₀ (g : GL (Fin n) R) : (blockGL g).val *ᵥ (e₀ : Fin (n + 1) → R) = e₀ := by
  rw [blockGL_val, cornerMat_mulVec, one_mul, mulVec_zero]

theorem e₀_eq_single : (e₀ : Fin (n + 1) → R) = Pi.single 0 1 := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [Fin.succ_ne_zero]

end Corner

/-! ### The split form -/

section Split

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **The split form** $\langle a\rangle \perp Q'$: $Q(x_0, x_1, \dots, x_n) = a x_0^2 + Q'(x_1, \dots, x_n)$
(coefficient matrix `cornerMat a Q'.coeff`). -/
@[kb "omeara1963" "§42A, p. 88 (orthogonal sum)"]
def splitForm (a : R) (Q' : QuadForm R n) : QuadForm R (n + 1) where
  coeff := cornerMat a Q'.coeff
  upper := by
    intro i j hij
    simp only [id] at hij
    refine Fin.cases (fun h => absurd h (Fin.not_lt_zero _)) (fun i h => ?_) i hij
    refine Fin.cases (by simp) (fun j hj => ?_) j h
    simp only [cornerMat_succ_succ]
    exact Q'.upper (Fin.succ_lt_succ_iff.mp hj)

theorem splitForm_coeff (a : R) (Q' : QuadForm R n) : (splitForm a Q').coeff = cornerMat a Q'.coeff := rfl

theorem hessian_splitForm (a : R) (Q' : QuadForm R n) :
    (splitForm a Q').hessian = cornerMat (2 * a) Q'.hessian := by
  rw [QuadForm.hessian, splitForm_coeff, cornerMat_transpose, cornerMat_add, two_mul, QuadForm.hessian]

theorem map_splitForm {S : Type*} [CommRing S] (f : R →+* S) (a : R) (Q' : QuadForm R n) :
    (splitForm a Q').map f = splitForm (f a) (Q'.map f) := by
  ext i j
  simp only [QuadForm.map, splitForm_coeff, cornerMat_map]

theorem evalIn_splitForm (K : Type*) [CommRing K] [Algebra R K] (a : R) (Q' : QuadForm R n) (t : K)
    (x : Fin n → K) :
    (splitForm a Q').evalIn K (Fin.cons t x) = algebraMap R K a * t * t + Q'.evalIn K x := by
  rw [QuadForm.evalIn_eq_dotProduct, QuadForm.evalIn_eq_dotProduct, splitForm_coeff, cornerMat_map,
    cornerMat_mulVec]
  change Matrix.vecCons t x ⬝ᵥ Matrix.vecCons _ _ = _
  rw [cons_dotProduct_cons]
  ring

theorem evalIn_splitForm_e₀ (K : Type*) [CommRing K] [Algebra R K] (a : R) (Q' : QuadForm R n) :
    (splitForm a Q').evalIn K (e₀ : Fin (n + 1) → K) = algebraMap R K a := by
  rw [evalIn_splitForm]
  simp [QuadForm.evalIn]

theorem det_hessian_splitForm (a : R) (Q' : QuadForm R n) :
    (splitForm a Q').hessian.det = 2 * a * Q'.hessian.det := by
  rw [hessian_splitForm, det_cornerMat]

end Split

/-! ### The orthogonal groups: $O(Q') \hookrightarrow O(Q)$ and the stabilizer of $e_0$ -/

section Orth

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (m : F) (Q' : QuadForm F n)

local notation "QS" => splitForm m Q'

theorem hessian_map_splitForm (R : Type*) [CommRing R] [Algebra F R] :
    (QS).hessian.map (algebraMap F R) = cornerMat (algebraMap F R (2 * m)) (Q'.hessian.map (algebraMap F R)) := by
  rw [hessian_splitForm, cornerMat_map]

/-- **The embedding $O(Q')(R) \to O(Q)(R)$**, $g \mapsto \mathrm{diag}(1, g)$, for an $F$-algebra $R$
($Q = \langle m\rangle \perp Q'$). Its image fixes $e_0$ (`orthEmb_mulVec_e₀`), and over a field it is the whole
stabilizer of $e_0$ (`exists_orthEmb_eq`). -/
def orthEmb (R : Type*) [CommRing R] [Algebra F R] : orthGroup Q' R →* orthGroup QS R where
  toFun g := ⟨blockGL (g : GL (Fin n) R), by
    rw [mem_orthGroup, hessian_map_splitForm, blockGL_val, cornerMat_transpose, cornerMat_mul, cornerMat_mul,
      (mem_orthGroup Q').mp g.2]
    simp⟩
  map_one' := by ext1; simp
  map_mul' a b := by ext1; simp

@[simp] theorem orthEmb_val (R : Type*) [CommRing R] [Algebra F R] (g : orthGroup Q' R) :
    (orthEmb m Q' R g : GL (Fin (n + 1)) R).val = cornerMat 1 (g : GL (Fin n) R).val := rfl

theorem orthEmb_injective (R : Type*) [CommRing R] [Algebra F R] : Function.Injective (orthEmb m Q' R) := by
  intro a b h
  apply Subtype.ext; apply Units.ext
  have := congrArg (fun g : orthGroup QS R => (g : GL (Fin (n + 1)) R).val) h
  simp only [orthEmb_val] at this
  exact cornerMat_injective_right this

theorem orthEmb_mulVec_e₀ (R : Type*) [CommRing R] [Algebra F R] (g : orthGroup Q' R) :
    (orthEmb m Q' R g : GL (Fin (n + 1)) R).val *ᵥ (e₀ : Fin (n + 1) → R) = e₀ :=
  blockGL_mulVec_e₀ _

/-- **The stabilizer of $e_0$ is $O(Q')$:** over a field $K \supseteq F$ with $2m \ne 0$ in $K$, every
$\gamma \in O(Q)(K)$ fixing $e_0$ is $\mathrm{diag}(1, g)$ with $g \in O(Q')(K)$. *Proof:* the column $\gamma e_0 = e_0$
is given; the row: $e_0^{\mathsf T}H\gamma = (\gamma e_0)^{\mathsf T}H\gamma = e_0^{\mathsf T}H$ and $e_0^{\mathsf T}H = 2m\,e_0^{\mathsf T}$, so
$e_0^{\mathsf T}\gamma = e_0^{\mathsf T}$. Then $\gamma^{\mathsf T}H\gamma = H$ restricts to $g^{\mathsf T}H'g = H'$. -/
@[kb "weil1982" "§3.4 (stabilizer of a vector) [unverified]"]
theorem exists_orthEmb_eq (K : Type*) [Field K] [Algebra F K] (hm : algebraMap F K (2 * m) ≠ 0)
    (γ : orthGroup QS K) (hγ : (γ : GL (Fin (n + 1)) K).val *ᵥ (e₀ : Fin (n + 1) → K) = e₀) :
    ∃ g : orthGroup Q' K, orthEmb m Q' K g = γ := by
  set A := (γ : GL (Fin (n + 1)) K).val with hA
  have hγo := (mem_orthGroup QS).mp γ.2
  rw [hessian_map_splitForm] at hγo
  change Aᵀ * _ * A = _ at hγo
  set c := algebraMap F K (2 * m)
  set H' := Q'.hessian.map (algebraMap F K)
  -- the column
  have hcol : ∀ i, A i 0 = (e₀ : Fin (n + 1) → K) i := by
    intro i
    have := congrFun hγ i
    rw [e₀_eq_single, mulVec_single_one] at this
    rw [e₀_eq_single]; exact this
  -- the row
  have hrow : ∀ j, A 0 j = (e₀ : Fin (n + 1) → K) j := by
    have h1 : Pi.single 0 1 ᵥ* (Aᵀ * cornerMat c H' * A) = Pi.single 0 1 ᵥ* cornerMat c H' := by rw [hγo]
    rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_transpose, ← e₀_eq_single, hγ, e₀_eq_single] at h1
    have h2 : Pi.single (0 : Fin (n + 1)) (1 : K) ᵥ* cornerMat c H' = c • Pi.single 0 1 := by
      rw [single_one_vecMul]
      ext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [Matrix.row]
    rw [h2, smul_vecMul, single_one_vecMul] at h1
    intro j
    have := congrFun h1 j
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.row] at this
    rw [e₀_eq_single]
    exact mul_left_cancel₀ hm this
  set g := A.submatrix Fin.succ Fin.succ
  have hAg : A = cornerMat 1 g := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hcol 0
    · simpa [Fin.succ_ne_zero] using hrow j.succ
    · simpa [Fin.succ_ne_zero] using hcol i.succ
    · rfl
  have hdet : g.det ≠ 0 := by
    have := (γ : GL (Fin (n + 1)) K).isUnit.map Matrix.detMonoidHom
    have h := this.ne_zero
    rw [Matrix.coe_detMonoidHom, ← hA, hAg, det_cornerMat, one_mul] at h
    exact h
  let gGL := Matrix.GeneralLinearGroup.mkOfDetNeZero g hdet
  have hgo : gGL ∈ orthGroup Q' K := by
    rw [mem_orthGroup]
    have : gGL.val = g := rfl
    rw [this]
    rw [hAg, cornerMat_transpose, cornerMat_mul, cornerMat_mul] at hγo
    exact cornerMat_injective_right hγo
  refine ⟨⟨gGL, hgo⟩, ?_⟩
  apply Subtype.ext; apply Units.ext
  rw [orthEmb_val]
  exact hAg.symm

/-- **Witt transitivity on $\{v : Q(v) = m\}$:** for $Q = \langle m\rangle \perp Q'$ nondegenerate and $m \ne 0$, every
$v \in F^{n+1}$ with $Q(v) = m$ is $\gamma e_0$ for some $\gamma \in O(Q)(F)$ (Witt's theorem,
`QuadraticForm.exists_isometryEquiv_apply_eq_of_nondegenerate`; O'Meara 42:17, p. 98). -/
@[kb "omeara1963" "§42F, 42:17, p. 98 (Witt's theorem); cassels1978 Ch. 2, Lemma 4.2, Cor. 1, p. 20"]
theorem exists_orthGroup_mulVec_eq (hQ : (QS).Nondegenerate) (hm : m ≠ 0) {v : Fin (n + 1) → F}
    (hv : (QS).eval v = m) :
    ∃ γ : orthGroup QS F, (γ : GL (Fin (n + 1)) F).val *ᵥ (e₀ : Fin (n + 1) → F) = v := by
  have hnd := QuadForm.nondegenerate_polarBilin_toQuadraticFormIn (K := F) hQ
  have h0 : (QS).toQuadraticFormIn F (e₀ : Fin (n + 1) → F) = m := by
    rw [QuadForm.toQuadraticFormIn_apply, evalIn_splitForm_e₀]; rfl
  have h1 : (QS).toQuadraticFormIn F v = m := by
    rw [QuadForm.toQuadraticFormIn_apply]; exact hv
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_apply_eq_of_nondegenerate _ hnd hm h0 h1
  set M := LinearMap.toMatrix' ρ.toLinearEquiv.toLinearMap
  have hdet : M.det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact (LinearEquiv.isUnit_det' ρ.toLinearEquiv).ne_zero
  let γ := Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet
  have hγ : γ ∈ orthGroup QS F := by
    refine mem_orthGroup_of_eval QS fun z => ?_
    have : γ.val *ᵥ z = ρ z := LinearMap.toMatrix'_mulVec _ z
    rw [this]
    have := ρ.map_app z
    rw [QuadForm.toQuadraticFormIn_apply, QuadForm.toQuadraticFormIn_apply] at this
    exact this
  refine ⟨⟨γ, hγ⟩, ?_⟩
  show γ.val *ᵥ _ = v
  rw [show γ.val *ᵥ (e₀ : Fin (n + 1) → F) = ρ e₀ from LinearMap.toMatrix'_mulVec _ _, ← hρ]

end Orth

/-! ### The adelic embedding $O(Q')(\mathbb A_f) \to O(Q)(\mathbb A_f)$ -/

section Adelic

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (m : F) (Q' : QuadForm F n)

local notation "QS" => splitForm m Q'

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

theorem mem_std_cons {t : Fv} {x : Fin n → Fv} :
    (Fin.cons t x : Fin (n + 1) → Fv) ∈ std v ↔ Valued.v t ≤ 1 ∧ x ∈ std v := by
  simp only [mem_ball, neg_zero, WithZero.exp_zero]
  constructor
  · intro h
    exact ⟨h 0, fun i => h i.succ⟩
  · rintro ⟨h0, h⟩ i
    refine Fin.cases h0 (fun i => h i) i

theorem mem_locAct_blockGL_std {g : GL (Fin n) Fv} {t : Fv} {x : Fin n → Fv} :
    (Fin.cons t x : Fin (n + 1) → Fv) ∈ locAct v (blockGL g) (std v) ↔
      Valued.v t ≤ 1 ∧ x ∈ locAct v g (std v) := by
  simp only [mem_locAct]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← Fin.cons_self_tail y, mem_std_cons] at hy
    rw [← Fin.cons_self_tail y, blockGL_val, cornerMat_mulVec, one_mul] at hyx
    have h0 := congrFun hyx 0
    have h1 : g.val *ᵥ Fin.tail y = x := funext fun i => congrFun hyx i.succ
    simp only [Fin.cons_zero] at h0
    exact ⟨h0 ▸ hy.1, Fin.tail y, hy.2, h1⟩
  · rintro ⟨ht, z, hz, hzx⟩
    refine ⟨Fin.cons t z, (mem_std_cons v).mpr ⟨ht, hz⟩, ?_⟩
    rw [blockGL_val, cornerMat_mulVec, one_mul, hzx]

/-- **$\mathrm{diag}(1, g)$ preserves $\mathfrak o_\mathfrak p^{n+1}$ iff $g$ preserves $\mathfrak o_\mathfrak p^n$.** -/
theorem locAct_blockGL_std_iff (g : GL (Fin n) Fv) :
    locAct v (blockGL g) (std v) = std v ↔ locAct v g (std v) = std v := by
  constructor
  · intro h
    ext x
    have := congrArg (fun M => (Fin.cons 0 x : Fin (n + 1) → Fv) ∈ M) h
    simp only [eq_iff_iff] at this
    rw [mem_locAct_blockGL_std, mem_std_cons] at this
    simpa using this
  · intro h
    ext y
    rw [← Fin.cons_self_tail y, mem_locAct_blockGL_std, mem_std_cons, h]

theorem mem_stdStab_orthEmb_iff (g : orthGroup Q' Fv) :
    orthEmb m Q' Fv g ∈ stdStab QS v ↔ g ∈ stdStab Q' v :=
  locAct_blockGL_std_iff v (g : GL (Fin n) Fv)

variable {v}

/-- **The adelic embedding** $O(Q')(\mathbb A_f) \to O(Q)(\mathbb A_f)$, $(h_\mathfrak p) \mapsto (\mathrm{diag}(1, h_\mathfrak p))$
(restricted: $\mathrm{diag}(1, h_\mathfrak p) \in O(Q)(\mathfrak o_\mathfrak p)$ whenever $h_\mathfrak p \in O(Q')(\mathfrak o_\mathfrak p)$). Its
image fixes $e_0$ at every prime. -/
def orthEmbAf : OAf Q' →* OAf QS where
  toFun h := ⟨fun v => orthEmb m Q' (v.adicCompletion F) (h v), by
    filter_upwards [h.2] with v hv
    exact (mem_stdStab_orthEmb_iff m Q' v _).mpr hv⟩
  map_one' := by ext v : 1; exact map_one (orthEmb m Q' _)
  map_mul' a b := by ext v : 1; exact map_mul (orthEmb m Q' _) _ _

theorem orthEmbAf_apply (h : OAf Q') (v : HeightOneSpectrum (𝓞 F)) :
    (orthEmbAf m Q' h) v = orthEmb m Q' (v.adicCompletion F) (h v) := rfl

theorem orthEmbAf_injective : Function.Injective (orthEmbAf m Q') := by
  intro a b h
  ext v : 1
  exact orthEmb_injective m Q' _ (congrArg (fun x : OAf QS => x v) h)

/-- **Compatibility with the rational points:** $\iota_{\mathbb A}(\mathrm{diag}_F(\gamma)) = \mathrm{diag}_F(\iota(\gamma))$. -/
theorem orthEmbAf_diagF (γ : orthGroup Q' F) :
    orthEmbAf m Q' (diagF Q' γ) = diagF QS (orthEmb m Q' F γ) := by
  ext v : 1
  apply Subtype.ext; apply Units.ext
  show cornerMat 1 ((γ : GL (Fin n) F).val.map (algebraMap F (v.adicCompletion F))) =
    (cornerMat 1 (γ : GL (Fin n) F).val).map (algebraMap F (v.adicCompletion F))
  rw [cornerMat_map, map_one]

/-- **The preimage of $O(\hat{\mathcal O}_F^{n+1})$ is $O(\hat{\mathcal O}_F^n)$.** -/
theorem comap_orthEmbAf_locStab_intVec :
    (locStab QS (stdLat F (n + 1))).comap (orthEmbAf m Q') = locStab Q' (stdLat F n) := by
  ext h
  rw [Subgroup.mem_comap, mem_locStab_intVec, mem_locStab_intVec]
  exact forall_congr' fun v => mem_stdStab_orthEmb_iff m Q' v (h v)

end Adelic

end QuadFormsKB.Tamagawa
