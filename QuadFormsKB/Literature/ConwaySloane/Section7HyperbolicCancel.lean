/-
# Conway–Sloane, Ch. 15, §7, p. 378: cancelling the hyperbolic plane locally

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7, p. 378
(`conwaysloane1999`); O. T. O'Meara, *Introduction to Quadratic Forms*, §93C, 93:14 (`omeara1963`).

**Layer.** Symmetric matrices $X$ over a commutative ring $K$ (the Gram matrices of Conway–Sloane's forms
$f(\vec x) = \vec x^{\mathsf T}X\vec x$, `Cassels.Ch8Ex2.gramForm X`), the hyperbolic plane
$H = \begin{pmatrix}0&1\\1&0\end{pmatrix}$, the block sum $X \oplus H$ (`Cassels.orthSumMat X H`, the variables of $X$
first: $x_0, \dots, x_{n-1}$ for $X$ and $x_n, x_{n+1}$ for $H$), and congruence over $K$ (`CongrIn K X Y`:
$g^{\mathsf T}Xg = Y$ for some $g \in \mathrm{GL}_n(K)$).

**Proves**
* `congrIn_orthSumMat`: $X \sim Y$ over $K$ implies $X \oplus Z \sim Y \oplus Z$.
* `congrIn_cancel_hyp_padic`: over $\mathbb Z_p$, every prime $p$ including $p = 2$, $X \oplus H \sim Y \oplus H$
  implies $X \sim Y$. This is O'Meara's 93:14 (cancellation of a unimodular hyperbolic plane over a discrete valuation
  ring, `OMeara.isometricLat_of_cancel_hyperbolic`), applied to the lattice $\mathbb Z_p^{n+2}$ with its two splittings
  $J \perp K$ and $\sigma J \perp \sigma K$, $J$ spanned by $e_n, e_{n+1}$, $K$ by $e_0, \dots, e_{n-1}$, and
  $\sigma$ the given congruence.
* `congrIn_cancel_hyp_real`: over $\mathbb R$, for $\det X \ne 0$, $X \oplus H \sim Y \oplus H$ implies $X \sim Y$
  (Witt cancellation, `QuadraticForm.equivalent_of_prod_equivalent_prod_of_nondegenerate`).
-/
import QuadFormsKB.Literature.ConwaySloane.Theorem11
import QuadFormsKB.Literature.Cassels.Ch8.LatticeBridge
import QuadFormsKB.Literature.OMeara.Sec93C
import QuadFormsKB.Witt.Bridge

open Matrix Submodule

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Cassels (orthSumMat)

variable {n : ℕ}

/-! ### Block sums of matrices -/

section Blocks

variable {R : Type*} [CommRing R] {a b : ℕ}

@[simp] theorem orthSumMat_castAdd_castAdd (F : Matrix (Fin a) (Fin a) R) (G : Matrix (Fin b) (Fin b) R)
    (i j : Fin a) : orthSumMat F G (Fin.castAdd b i) (Fin.castAdd b j) = F i j := by
  simp [orthSumMat, Matrix.reindex_apply]

@[simp] theorem orthSumMat_castAdd_natAdd (F : Matrix (Fin a) (Fin a) R) (G : Matrix (Fin b) (Fin b) R)
    (i : Fin a) (j : Fin b) : orthSumMat F G (Fin.castAdd b i) (Fin.natAdd a j) = 0 := by
  simp [orthSumMat, Matrix.reindex_apply]

@[simp] theorem orthSumMat_natAdd_castAdd (F : Matrix (Fin a) (Fin a) R) (G : Matrix (Fin b) (Fin b) R)
    (i : Fin b) (j : Fin a) : orthSumMat F G (Fin.natAdd a i) (Fin.castAdd b j) = 0 := by
  simp [orthSumMat, Matrix.reindex_apply]

@[simp] theorem orthSumMat_natAdd_natAdd (F : Matrix (Fin a) (Fin a) R) (G : Matrix (Fin b) (Fin b) R)
    (i j : Fin b) : orthSumMat F G (Fin.natAdd a i) (Fin.natAdd a j) = G i j := by
  simp [orthSumMat, Matrix.reindex_apply]

theorem orthSumMat_mul (F F' : Matrix (Fin a) (Fin a) R) (G G' : Matrix (Fin b) (Fin b) R) :
    orthSumMat F G * orthSumMat F' G' = orthSumMat (F * F') (G * G') := by
  rw [Cassels.dyadic_orthSumMat_eq, Cassels.dyadic_orthSumMat_eq, Cassels.dyadic_orthSumMat_eq,
    ← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective, Matrix.fromBlocks_multiply]
  simp

theorem orthSumMat_one : orthSumMat (1 : Matrix (Fin a) (Fin a) R) (1 : Matrix (Fin b) (Fin b) R) = 1 := by
  rw [Cassels.dyadic_orthSumMat_eq, Matrix.fromBlocks_one]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.one_apply]

theorem det_orthSumMat (F : Matrix (Fin a) (Fin a) R) (G : Matrix (Fin b) (Fin b) R) :
    (orthSumMat F G).det = F.det * G.det := by
  rw [Cassels.dyadic_orthSumMat_eq, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

/-- **Congruence passes to block sums**: if $g^{\mathsf T}Xg = Y$ with $g \in \mathrm{GL}_a(R)$ then
$(g \oplus 1)^{\mathsf T}(X \oplus Z)(g \oplus 1) = Y \oplus Z$. -/
theorem congrIn_orthSumMat {X Y : Matrix (Fin a) (Fin a) R} (h : CongrIn R X Y) (Z : Matrix (Fin b) (Fin b) R) :
    CongrIn R (orthSumMat X Z) (orthSumMat Y Z) := by
  obtain ⟨g, hg⟩ := h
  let u : GL (Fin (a + b)) R :=
    ⟨orthSumMat g.val 1, orthSumMat g⁻¹.val 1,
      by rw [orthSumMat_mul, Units.mul_inv, Matrix.one_mul, orthSumMat_one],
      by rw [orthSumMat_mul, Units.inv_mul, Matrix.one_mul, orthSumMat_one]⟩
  refine ⟨u, ?_⟩
  change (orthSumMat g.val 1)ᵀ * orthSumMat X Z * orthSumMat g.val 1 = orthSumMat Y Z
  rw [orthSumMat_transpose, orthSumMat_mul, orthSumMat_mul, hg, Matrix.transpose_one, Matrix.one_mul,
    Matrix.mul_one]

end Blocks

/-! ### Cancellation over $\mathbb Z_p$ (O'Meara 93:14) -/

section Padic

variable {p : ℕ} [Fact p.Prime]

open Cassels (qfForm zpLat qf)

theorem castAdd_ne_natAdd_two (i : Fin n) (j : Fin 2) : Fin.castAdd 2 i ≠ Fin.natAdd n j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

/-- Helper: the embedding $\mathbb Z_p^n \to \mathbb Q_p^{n+2}$ into the first $n$ coordinates
($y \mapsto (y_0, \dots, y_{n-1}, 0, 0)$). -/
def headEmb (p n : ℕ) [Fact p.Prime] : (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] (Fin (n + 2) → ℚ_[p]) where
  toFun y := Fin.append (fun i => (y i : ℚ_[p])) 0
  map_add' y z := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp
  map_smul' c y := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [Algebra.smul_def]

@[simp] theorem headEmb_castAdd (y : Fin n → ℤ_[p]) (i : Fin n) :
    headEmb p n y (Fin.castAdd 2 i) = (y i : ℚ_[p]) := by
  simp [headEmb]

@[simp] theorem headEmb_natAdd (y : Fin n → ℤ_[p]) (j : Fin 2) : headEmb p n y (Fin.natAdd n j) = 0 := by
  simp [headEmb]

theorem headEmb_injective : Function.Injective (headEmb p n) := by
  intro y z h
  funext i
  have := congrFun h (Fin.castAdd 2 i)
  simp only [headEmb_castAdd] at this
  exact Subtype.ext this

/-- Helper: the hyperbolic basis vectors $e_n, e_{n+1}$ of $\mathbb Q_p^{n+2}$. -/
abbrev hypVec (p n : ℕ) [Fact p.Prime] (j : Fin 2) : Fin (n + 2) → ℚ_[p] := Pi.single (Fin.natAdd n j) 1

/-- Helper: the block sum $X \oplus H$ over $\mathbb Q_p$ of a matrix $X$ over $\mathbb Z_p$. -/
abbrev hypSumQ (X : Matrix (Fin n) (Fin n) ℤ_[p]) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ_[p] :=
  orthSumMat (X.map PadicInt.Coe.ringHom) !![0, 1; 1, 0]

theorem hypSumQ_transpose {X : Matrix (Fin n) (Fin n) ℤ_[p]} (hX : Xᵀ = X) : (hypSumQ X)ᵀ = hypSumQ X := by
  rw [hypSumQ, orthSumMat_transpose, ← Matrix.transpose_map, hX]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem hypSumQ_mulVec_headEmb (X : Matrix (Fin n) (Fin n) ℤ_[p]) (y : Fin n → ℤ_[p]) :
    hypSumQ X *ᵥ headEmb p n y = headEmb p n (X *ᵥ y) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add]

theorem dotProduct_headEmb (y z : Fin n → ℤ_[p]) :
    headEmb p n y ⬝ᵥ headEmb p n z = ((y ⬝ᵥ z : ℤ_[p]) : ℚ_[p]) := by
  simp [dotProduct, Fin.sum_univ_add]

theorem qf_headEmb (X : Matrix (Fin n) (Fin n) ℤ_[p]) (y : Fin n → ℤ_[p]) :
    qf (hypSumQ X) (headEmb p n y) = ((y ⬝ᵥ (X *ᵥ y) : ℤ_[p]) : ℚ_[p]) := by
  rw [qf, hypSumQ_mulVec_headEmb, dotProduct_headEmb]

theorem castAdd_eq_zero_of_mem_span {x : Fin (n + 2) → ℚ_[p]}
    (hx : x ∈ span ℤ_[p] {hypVec p n 0, hypVec p n 1}) (i : Fin n) : x (Fin.castAdd 2 i) = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact Pi.single_eq_of_ne (castAdd_ne_natAdd_two i 0) _
    · exact Pi.single_eq_of_ne (castAdd_ne_natAdd_two i 1) _
  | zero => rfl
  | add y z _ _ hy hz => simp [hy, hz]
  | smul c y _ hy => simp [hy]

theorem qf_hypVec (X : Matrix (Fin n) (Fin n) ℤ_[p]) (j : Fin 2) : qf (hypSumQ X) (hypVec p n j) = 0 := by
  have : qf (hypSumQ X) (hypVec p n j) = hypSumQ X (Fin.natAdd n j) (Fin.natAdd n j) := by
    simp [qf, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [this, hypSumQ, orthSumMat_natAdd_natAdd]
  fin_cases j <;> rfl

theorem bil_hypVec {X : Matrix (Fin n) (Fin n) ℤ_[p]} (hX : Xᵀ = X) :
    OMeara.bil (qfForm (hypSumQ X)) (hypVec p n 0) (hypVec p n 1) = 1 := by
  rw [Cassels.bil_qfForm (hypSumQ_transpose hX)]
  have : hypVec p n 0 ⬝ᵥ (hypSumQ X *ᵥ hypVec p n 1) = hypSumQ X (Fin.natAdd n 0) (Fin.natAdd n 1) := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [this, hypSumQ, orthSumMat_natAdd_natAdd]
  rfl

theorem mem_zpLat_iff_exists {x : Fin (n + 2) → ℚ_[p]} :
    x ∈ zpLat p (n + 2) ↔ ∃ y : Fin (n + 2) → ℤ_[p], x = fun k => (y k : ℚ_[p]) := by
  rw [Cassels.mem_zpLat]
  constructor
  · intro h; exact ⟨fun k => ⟨x k, h k⟩, rfl⟩
  · rintro ⟨y, rfl⟩ k; exact PadicInt.norm_le_one (y k)

/-- **The splitting $\mathbb Z_p^{n+2} = J \perp K$** for $X \oplus H$: $J = \mathbb Z_pe_n + \mathbb Z_pe_{n+1}$ (the
hyperbolic plane) and $K = \mathbb Z_pe_0 + \dots + \mathbb Z_pe_{n-1}$. -/
theorem isOrthSum_hypSumQ {X : Matrix (Fin n) (Fin n) ℤ_[p]} (hX : Xᵀ = X) :
    OMeara.IsOrthSum (qfForm (hypSumQ X)) (zpLat p (n + 2)) (span ℤ_[p] {hypVec p n 0, hypVec p n 1})
      (LinearMap.range (headEmb p n)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x hx _ ⟨w, rfl⟩
    rw [Cassels.bil_qfForm (hypSumQ_transpose hX), hypSumQ_mulVec_headEmb]
    simp [dotProduct, Fin.sum_univ_add, castAdd_eq_zero_of_mem_span hx]
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨w, rfl⟩
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · exact castAdd_eq_zero_of_mem_span hx i
    · simp
  · apply le_antisymm
    · refine sup_le (span_le.2 ?_) ?_
      · rintro _ (rfl | rfl)
        · rw [SetLike.mem_coe, Cassels.mem_zpLat]; intro k; simp [Pi.single_apply]; split_ifs <;> simp
        · rw [SetLike.mem_coe, Cassels.mem_zpLat]; intro k
          simp [Pi.single_apply]; split_ifs <;> simp
      · rintro _ ⟨w, rfl⟩
        rw [Cassels.mem_zpLat]; intro k
        refine Fin.addCases (fun i => ?_) (fun j => ?_) k
        · simp only [headEmb_castAdd]; exact PadicInt.norm_le_one _
        · simp
    · intro x hx
      obtain ⟨y, rfl⟩ := mem_zpLat_iff_exists.mp hx
      refine Submodule.mem_sup.2 ⟨y (Fin.natAdd n 0) • hypVec p n 0 + y (Fin.natAdd n 1) • hypVec p n 1,
        add_mem (smul_mem _ _ (subset_span (by simp))) (smul_mem _ _ (subset_span (by simp))),
        headEmb p n (fun i => y (Fin.castAdd 2 i)), ⟨_, rfl⟩, ?_⟩
      funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · simp [castAdd_ne_natAdd_two]
      · fin_cases j <;> simp [Algebra.smul_def]

theorem bil_of_isometry {m : ℕ} {Q Q' : QuadraticForm ℚ_[p] (Fin m → ℚ_[p])}
    {σ : (Fin m → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin m → ℚ_[p])} (hσ : ∀ x, Q (σ x) = Q' x) (x y : Fin m → ℚ_[p]) :
    OMeara.bil Q (σ x) (σ y) = OMeara.bil Q' x y := by
  rw [OMeara.bil_eq_half, OMeara.bil_eq_half, ← map_add, hσ, hσ, hσ]

/-- An isometry $\sigma : (V, Q') \to (V, Q)$ carries an orthogonal splitting for $Q'$ to one for $Q$. -/
theorem isOrthSum_latMap_of_isometry {m : ℕ} {Q Q' : QuadraticForm ℚ_[p] (Fin m → ℚ_[p])}
    (σ : (Fin m → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin m → ℚ_[p])) (hσ : ∀ x, Q (σ x) = Q' x)
    {L J K : Submodule ℤ_[p] (Fin m → ℚ_[p])} (h : OMeara.IsOrthSum Q' L J K) :
    OMeara.IsOrthSum Q (OMeara.latMap σ L) (OMeara.latMap σ J) (OMeara.latMap σ K) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [bil_of_isometry hσ]; exact h.orth x hx y hy
  · exact Submodule.disjoint_map (f := ((σ : (Fin m → ℚ_[p]) →ₗ[ℚ_[p]] (Fin m → ℚ_[p])).restrictScalars ℤ_[p]))
      σ.injective h.disjoint
  · rw [OMeara.latMap, OMeara.latMap, OMeara.latMap, ← Submodule.map_sup, h.sup_eq]

/-- **Cancellation of the hyperbolic plane over $\mathbb Z_p$** (every prime $p$, including $p = 2$; O'Meara 93:14):
for symmetric $X, Y \in M_n(\mathbb Z_p)$, if $X \oplus H$ and $Y \oplus H$ are congruent over $\mathbb Z_p$, with
$H = \begin{pmatrix}0&1\\1&0\end{pmatrix}$, then so are $X$ and $Y$. -/
@[kb "omeara1963" "§93C, 93:14, p. 256 (applied to Z_p^(n+2) = H ⊥ K for Conway–Sloane Ch. 15, §7, p. 378)"]
theorem congrIn_cancel_hyp_padic {X Y : Matrix (Fin n) (Fin n) ℤ_[p]} (hX : Xᵀ = X) (hY : Yᵀ = Y)
    (h : CongrIn ℤ_[p] (orthSumMat X !![0, 1; 1, 0]) (orthSumMat Y !![0, 1; 1, 0])) : CongrIn ℤ_[p] X Y := by
  obtain ⟨T, hT⟩ := h
  set c := (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) with hc
  have hmap : ∀ Z : Matrix (Fin n) (Fin n) ℤ_[p], (orthSumMat Z !![0, 1; 1, 0]).map c = hypSumQ Z := by
    intro Z
    rw [Cassels.Ex5.map_orthSum]
    congr 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [c]
  set Tq := T.val.map c with hTqdef
  set Ti := (T⁻¹).val.map c with hTidef
  have h1 : Tq * Ti = 1 := by
    rw [hTqdef, hTidef, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero c) (map_one c)]
  have h2 : Ti * Tq = 1 := by
    rw [hTqdef, hTidef, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero c) (map_one c)]
  let σ : (Fin (n + 2) → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin (n + 2) → ℚ_[p]) :=
    LinearEquiv.ofLinearMap (Matrix.mulVecLin Tq) (Matrix.mulVecLin Ti)
      (LinearMap.ext fun x => by simp [Matrix.mulVec_mulVec, h1])
      (LinearMap.ext fun x => by simp [Matrix.mulVec_mulVec, h2])
  have hσ : ∀ x, σ x = Tq *ᵥ x := fun x => rfl
  have hTq : Tqᵀ * hypSumQ X * Tq = hypSumQ Y := by
    rw [← hmap, ← hmap, ← hT, hTqdef, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hiso : ∀ x, qfForm (hypSumQ X) (σ x) = qfForm (hypSumQ Y) x := by
    intro x
    rw [Cassels.qfForm_apply, Cassels.qfForm_apply, hσ, Cassels.qf, Cassels.qf, ← hTq, dotProduct_transpose_mul]
  -- `σ` preserves the lattice `ℤ_p^{n+2}`
  have hint : ∀ (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ_[p]) (x : Fin (n + 2) → ℚ_[p]),
      x ∈ zpLat p (n + 2) → A.map c *ᵥ x ∈ zpLat p (n + 2) := by
    intro A x hx
    obtain ⟨y, rfl⟩ := mem_zpLat_iff_exists.mp hx
    refine mem_zpLat_iff_exists.mpr ⟨A *ᵥ y, ?_⟩
    funext k
    exact (RingHom.map_mulVec c A y k).symm
  have hL : OMeara.latMap σ (zpLat p (n + 2)) = zpLat p (n + 2) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hint T.val y hy
    · intro hx
      refine ⟨Ti *ᵥ x, hint (T⁻¹).val x hx, ?_⟩
      change Tq *ᵥ (Ti *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  -- the two splittings of `ℤ_p^{n+2}` for `X ⊕ H`
  have hA := isOrthSum_hypSumQ (p := p) hX
  have hB' := isOrthSum_latMap_of_isometry σ hiso (isOrthSum_hypSumQ (p := p) hY)
  rw [hL] at hB'
  have hJ' : OMeara.latMap σ (span ℤ_[p] {hypVec p n 0, hypVec p n 1}) =
      span ℤ_[p] {σ (hypVec p n 0), σ (hypVec p n 1)} := by
    rw [OMeara.latMap, Submodule.map_span, Set.image_pair]; rfl
  rw [hJ'] at hB'
  have hq : ∀ (Z : Matrix (Fin n) (Fin n) ℤ_[p]) (j : Fin 2), qfForm (hypSumQ Z) (hypVec p n j) = 0 :=
    fun Z j => by rw [Cassels.qfForm_apply]; exact qf_hypVec Z j
  obtain ⟨f, hf⟩ := OMeara.isometricLat_of_cancel_hyperbolic (qfForm (hypSumQ X)) hA hB' rfl rfl (hq X 0) (hq X 1)
    (bil_hypVec hX) (by rw [hiso]; exact hq Y 0) (by rw [hiso]; exact hq Y 1)
    (by rw [bil_of_isometry hiso]; exact bil_hypVec hY)
  -- back from the lattice `K` to coordinates
  let g := (Submodule.equivMapOfInjective ((σ : (Fin (n + 2) → ℚ_[p]) →ₗ[ℚ_[p]] (Fin (n + 2) → ℚ_[p])).restrictScalars
    ℤ_[p]) σ.injective (LinearMap.range (headEmb p n))).symm
  have hg : ∀ z, σ (g z : Fin (n + 2) → ℚ_[p]) = z := fun z =>
    Submodule.map_equivMapOfInjective_symm_apply _ _ _ z
  have hgQ : ∀ z, qfForm (hypSumQ Y) (g z : Fin (n + 2) → ℚ_[p]) = qfForm (hypSumQ X) (z : Fin (n + 2) → ℚ_[p]) :=
    fun z => by rw [← hiso, hg]
  let e := LinearEquiv.ofInjective (headEmb p n) headEmb_injective
  let ψ := e.trans ((f.trans g).trans e.symm)
  have hψ : ∀ y, headEmb p n (ψ y) = (g (f (e y)) : Fin (n + 2) → ℚ_[p]) := by
    intro y
    have := congrArg Subtype.val (e.apply_symm_apply (g (f (e y))))
    rw [LinearEquiv.ofInjective_apply] at this
    exact this
  have key : ∀ y, ψ y ⬝ᵥ (Y *ᵥ ψ y) = y ⬝ᵥ (X *ᵥ y) := by
    intro y
    have h3 := hgQ (f (e y))
    rw [hf, ← hψ, Cassels.qfForm_apply, Cassels.qfForm_apply, LinearEquiv.ofInjective_apply, qf_headEmb,
      qf_headEmb] at h3
    exact Subtype.ext h3
  set G := LinearMap.toMatrix' (ψ : (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] (Fin n → ℤ_[p])) with hGdef
  have hG : ∀ y, G *ᵥ y = ψ y := fun y => by rw [hGdef, LinearMap.toMatrix'_mulVec]; rfl
  have hdet : IsUnit G.det := by rw [hGdef, LinearMap.det_toMatrix']; exact LinearEquiv.isUnit_det' ψ
  have hiso2 : Siegel.IsometricGL (Cassels.Ch8Ex2.gramForm Y) (Cassels.Ch8Ex2.gramForm X) :=
    ⟨Matrix.nonsingInvUnit G hdet, fun y => by
      change (Cassels.Ch8Ex2.gramForm Y).eval (G *ᵥ y) = (Cassels.Ch8Ex2.gramForm X).eval y
      rw [eval_gramForm, eval_gramForm, hG, key]⟩
  exact ((isometricGL_gramForm_iff hY hX).1 hiso2).symm

end Padic

/-! ### Cancellation over $\mathbb R$ (Witt) -/

section Real

/-- The form of a block sum is the orthogonal sum of the forms (`QuadForm.orthSum`, the variables of $F$ first). -/
theorem gramForm_orthSumMat {R : Type*} [CommRing R] {a b : ℕ} (F : Matrix (Fin a) (Fin a) R)
    (G : Matrix (Fin b) (Fin b) R) :
    Cassels.Ch8Ex2.gramForm (orthSumMat F G) =
      QuadForm.orthSum (Cassels.Ch8Ex2.gramForm F) (Cassels.Ch8Ex2.gramForm G) := by
  have c1 : ∀ i j : Fin a, Fin.castAdd b i < Fin.castAdd b j ↔ i < j := fun i j => by
    simp only [Fin.lt_def, Fin.val_castAdd]
  have c2 : ∀ i j : Fin a, Fin.castAdd b i ≤ Fin.castAdd b j ↔ i ≤ j := fun i j => by
    simp only [Fin.le_iff_val_le_val, Fin.val_castAdd]
  have c3 : ∀ i j : Fin b, Fin.natAdd a i < Fin.natAdd a j ↔ i < j := fun i j => by
    simp only [Fin.lt_def, Fin.val_natAdd]; omega
  have c4 : ∀ i j : Fin b, Fin.natAdd a i ≤ Fin.natAdd a j ↔ i ≤ j := fun i j => by
    simp only [Fin.le_iff_val_le_val, Fin.val_natAdd]; omega
  have c5 : ∀ (i : Fin a) (j : Fin b), Fin.natAdd a j ≤ Fin.castAdd b i ↔ False := fun i j => by
    simp only [Fin.le_def, Fin.val_natAdd, Fin.val_castAdd, iff_false, not_le]; omega
  have c6 : ∀ (i : Fin a) (j : Fin b), Fin.castAdd b i < Fin.natAdd a j := fun i j => by
    simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]; omega
  have c7 : ∀ (i : Fin a) (j : Fin b), Fin.natAdd a j ≠ Fin.castAdd b i := fun i j h =>
    lt_irrefl _ (h ▸ c6 i j)
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [Cassels.Ch8Ex2.gramForm, QuadForm.orthSum, QuadForm.ofUpper, Matrix.of_apply, c1, c2,
      Fin.addCases_left, orthSumMat_castAdd_castAdd, Fin.castAdd_inj]
    split_ifs <;> first | rfl | (exfalso; order)
  · simp [Cassels.Ch8Ex2.gramForm, QuadForm.orthSum, QuadForm.ofUpper, c6]
  · simp [Cassels.Ch8Ex2.gramForm, QuadForm.orthSum, QuadForm.ofUpper, c5, c7, not_lt.mpr (c6 j i).le]
  · simp only [Cassels.Ch8Ex2.gramForm, QuadForm.orthSum, QuadForm.ofUpper, Matrix.of_apply, c3, c4,
      Fin.addCases_right, orthSumMat_natAdd_natAdd, Fin.natAdd_inj]
    split_ifs <;> first | rfl | (exfalso; order)

theorem nondegenerate_gramForm_real {k : ℕ} {X : Matrix (Fin k) (Fin k) ℝ} (hX : Xᵀ = X) (hd : X.det ≠ 0) :
    (Cassels.Ch8Ex2.gramForm X).Nondegenerate := by
  unfold QuadForm.Nondegenerate
  rw [Cassels.Ch8Ex2.hessian_gramForm, hX, ← two_smul ℝ X, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero) hd

/-- **Cancellation of the hyperbolic plane over $\mathbb R$** (Witt cancellation): for symmetric
$X, Y \in M_n(\mathbb R)$ with $\det X \ne 0$, if $X \oplus H$ and $Y \oplus H$ are congruent over $\mathbb R$ then so
are $X$ and $Y$. -/
theorem congrIn_cancel_hyp_real {X Y : Matrix (Fin n) (Fin n) ℝ} (hX : Xᵀ = X) (hY : Yᵀ = Y) (hdX : X.det ≠ 0)
    (h : CongrIn ℝ (orthSumMat X !![0, 1; 1, 0]) (orthSumMat Y !![0, 1; 1, 0])) : CongrIn ℝ X Y := by
  have hHs : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = !![0, 1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hsym : ∀ Z : Matrix (Fin n) (Fin n) ℝ, Zᵀ = Z →
      (orthSumMat Z !![0, 1; 1, 0])ᵀ = orthSumMat Z !![0, 1; 1, 0] := fun Z hZ => by
    rw [orthSumMat_transpose, hZ, hHs]
  have hHd : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]; norm_num
  have h1 := (isometricGL_gramForm_iff (hsym X hX) (hsym Y hY)).2 h
  rw [gramForm_orthSumMat, gramForm_orthSumMat, Siegel.isometricGL_iff_isometricIn,
    QuadForm.isometricIn_iff_equivalent] at h1
  obtain ⟨eY⟩ := QuadForm.equivalent_toQuadraticFormIn_orthSum ℝ (Cassels.Ch8Ex2.gramForm Y)
    (Cassels.Ch8Ex2.gramForm (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ))
  obtain ⟨eX⟩ := QuadForm.equivalent_toQuadraticFormIn_orthSum ℝ (Cassels.Ch8Ex2.gramForm X)
    (Cassels.Ch8Ex2.gramForm (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ))
  obtain ⟨g⟩ := h1
  have h2 := QuadraticForm.equivalent_of_prod_equivalent_prod_of_nondegenerate
    (QuadForm.nondegenerate_polarBilin_toQuadraticFormIn ℝ (nondegenerate_gramForm_real hHs hHd))
    (QuadForm.nondegenerate_polarBilin_toQuadraticFormIn ℝ (nondegenerate_gramForm_real hX hdX))
    ⟨(QuadraticMap.IsometryEquiv.prodComm _ _).trans
      (eX.symm.trans (g.symm.trans (eY.trans (QuadraticMap.IsometryEquiv.prodComm _ _))))⟩
  have h4 := (QuadForm.isometricIn_iff_equivalent ℝ (Cassels.Ch8Ex2.gramForm Y) (Cassels.Ch8Ex2.gramForm X)).2 h2
  exact ((isometricGL_gramForm_iff hY hX).1 ((Siegel.isometricGL_iff_isometricIn _ _).2 h4)).symm

end Real

end QuadFormsKB.ConwaySloane
