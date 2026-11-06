/-
# Hanke 2005, Lemma 2.2 at the finite places, with the sign of the exponent corrected

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Lemma 2.2** (thesis, p. 6) as printed: if $\psi' = {}^tA\psi A$ with $A$ invertible, then
$\beta_v(\Lambda,\psi') = |\det A|_v^{\,n+1}\,\beta_v(A\Lambda,\psi)$.

*Erratum (proposed by the formalization, not yet confirmed by the author):* the exponent is $-(n+1)$:
$$\beta_v(\Lambda,{}^tA\psi A) = |\det A|_v^{-(n+1)}\,\beta_v(A\Lambda,\psi)\qquad(\texttt{hankeBeta\_congr}).$$
In the proof, $\lim_{U\to\psi'}\mathrm{vol}_T([A]^{-1}(U))/\mathrm{vol}_T(U)$ is the Jacobian of $[A^{-1}]$, i.e.
$|\det A|_v^{-(n+1)}$ by (2.10), not $|\det A|_v^{n+1}$. The printed version also contradicts Lemma 3.1 (take
$A = c\cdot1_n$, so that $A\Lambda$ has the same stabilizer as $\Lambda$): it would give
$\beta(\Lambda,c^2\psi) = |c|^{n(n+1)}\beta(\Lambda,\psi)$, Lemma 3.1 gives $|c|^{-n(n+1)}$. Counterexample
(`lemma22_printed_false`): $n = 1$, $\psi = 1$, $A = \pi$, $\Lambda = \mathcal O_v$: $\beta_v(\mathcal O_v,\pi^2) = q^2\beta_v(\mathcal O_v,1)$,
while the printed formula gives $q^{-2}\beta_v(\mathcal O_v,1)$, and $\beta_v(\mathcal O_v,1) > 0$. The error does not affect
Theorem 5.1: its first display of Part 1 (p. 17) has the exponents of $|\det\psi|_v$ and $|\det\varphi_v|_v$ flipped in the
same way, and the final formula is the one obtained with the corrected sign.

Lattices: every $\mathfrak o_v$-lattice of full rank in $F_v^n$ is $B\,\mathfrak o_v^n$ for some $B\in\mathrm{GL}_n(F_v)$
(`locAct v B (std v)`), so the lemma is stated for $\Lambda = B\,\mathfrak o_v^n$.
-/
import QuadFormsKB.Literature.Hanke2005.LocalDensity
import QuadFormsKB.Literature.Hanke2005.Jacobians

open IsDedekindDomain NumberField MeasureTheory Filter Topology WithZero Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

section Aux

open QuadFormsKB.Tamagawa.Measure.LerayPadic
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

section HS
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem l22_distrib_eq_norm (u : Fvˣ) : (distribHaarChar Fv u : ℝ) = ‖(u : Fv)‖ := by
  have h := QuadFormsKB.WeilRep.modK_eq_norm v (x := (u : Fv)) u.ne_zero
  rw [QuadFormsKB.Analysis.Weil.modK, dif_neg u.ne_zero] at h
  simpa using h

/-- Haar scaling of a linear automorphism of `Fv^ι`. -/
theorem l22_hs_image (ν : Measure (ι → Fv)) [ν.IsAddHaarMeasure] (M : Matrix ι ι Fv) (hM : M.det ≠ 0)
    (s : Set (ι → Fv)) :
    ν ((fun x => M *ᵥ x) '' s) = ENNReal.ofReal ‖M.det‖ * ν s := by
  classical
  have : ν.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  set g : GL ι Fv := GeneralLinearGroup.mkOfDetNeZero M hM with hg
  have hmap := map_mulVec_eq_glHaarChar_inv ν g
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  let e : (ι → Fv) ≃ₜ (ι → Fv) :=
    { toFun := fun x => M *ᵥ x
      invFun := fun x => M⁻¹ *ᵥ x
      left_inv := fun x => by
        simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
      right_inv := fun x => by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
      continuous_toFun := continuous_const.matrix_mulVec continuous_id
      continuous_invFun := continuous_const.matrix_mulVec continuous_id }
  have hemb := e.measurableEmbedding
  have h1 : ν ((fun x => M *ᵥ x) ⁻¹' ((fun x => M *ᵥ x) '' s)) =
      (glHaarChar Fv ι g)⁻¹ * ν ((fun x => M *ᵥ x) '' s) := by
    have := congrArg (fun μ => μ ((fun x => M *ᵥ x) '' s)) hmap
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
    rw [← this]
    exact (hemb.map_apply ν _).symm
  have hinj : Function.Injective (fun x => M *ᵥ x) := e.injective
  rw [hinj.preimage_image] at h1
  have hchar : (glHaarChar Fv ι g : ℝ≥0∞) = ENNReal.ofReal ‖M.det‖ := by
    rw [glHaarChar_eq_of_field, ← ENNReal.ofReal_coe_nnreal, l22_distrib_eq_norm v]
    simp [hg]
  have hpos : (glHaarChar Fv ι g : ℝ≥0∞) ≠ 0 := by
    rw [hchar]; simpa using hM
  have hne : (glHaarChar Fv ι g : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hc0 : glHaarChar Fv ι g ≠ 0 := by
    intro h; apply hpos; rw [h]; rfl
  rw [ENNReal.coe_inv hc0] at h1
  rw [← hchar, h1, ← mul_assoc, ENNReal.mul_inv_cancel hpos hne, one_mul]


/-- Conjugation `X ↦ g X g⁻¹` preserves `volM` (images of arbitrary sets). -/
theorem l22_vol_conj_image {g : Matrix (Fin n) (Fin n) Fv} (hg : g.det ≠ 0) (A : Set (Matrix (Fin n) (Fin n) Fv)) :
    volM v ((fun X => g * X * g⁻¹) '' A) = volM v A := by
  classical
  have hu : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
  let E : Matrix (Fin n) (Fin n) Fv ≃ₜ+ (Fin n × Fin n → Fv) :=
    { toFun := fun X p => X p.1 p.2
      invFun := fun x a b => x (a, b)
      left_inv := fun X => rfl
      right_inv := fun x => rfl
      map_add' := fun X Y => rfl
      continuous_toFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
      continuous_invFun := continuous_pi fun a => continuous_pi fun b => continuous_apply (a, b) }
  have hν : (volM v : Measure (Matrix (Fin n) (Fin n) Fv)).map E |>.IsAddHaarMeasure :=
    E.isAddHaarMeasure_map _
  have hemb : MeasurableEmbedding E := E.toHomeomorph.measurableEmbedding
  set M : Matrix (Fin n × Fin n) (Fin n × Fin n) Fv := Matrix.kroneckerMap (· * ·) g (g⁻¹)ᵀ with hM
  have hdet : M.det = 1 := by
    rw [hM, Matrix.det_kronecker, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← mul_pow,
      mul_inv_cancel₀ hg, one_pow]
  have hcomm : ∀ X, E (g * X * g⁻¹) = M *ᵥ E X := by
    intro X; funext ⟨a, b⟩
    show (g * X * g⁻¹) a b = (M *ᵥ fun p : Fin n × Fin n => X p.1 p.2) (a, b)
    simp only [hM, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have himg : E '' ((fun X => g * X * g⁻¹) '' A) = (fun x => M *ᵥ x) '' (E '' A) := by
    ext x; simp only [Set.mem_image]
    constructor
    · rintro ⟨_, ⟨X, hX, rfl⟩, rfl⟩; exact ⟨E X, ⟨X, hX, rfl⟩, (hcomm X).symm⟩
    · rintro ⟨_, ⟨X, hX, rfl⟩, rfl⟩; exact ⟨_, ⟨X, hX, rfl⟩, hcomm X⟩
  have key : ∀ B : Set (Matrix (Fin n) (Fin n) Fv), volM v B = ((volM v).map E) (E '' B) := by
    intro B
    rw [hemb.map_apply, E.injective.preimage_image]
  rw [key, key A, himg, l22_hs_image v _ M (by rw [hdet]; exact one_ne_zero), hdet]
  simp

end HS

/-! ### Gram coordinates -/

section Sym

open QuadFormsKB.Analysis
variable {v}

/-- The coordinates `(t_{ik})_{i ≤ k}` of a matrix. -/
def coordsOf (X : Matrix (Fin n) (Fin n) Fv) : UpIdx n → Fv := fun p => X p.1.1 p.1.2

/-- The symmetric matrix with the given upper triangular coordinates. -/
def symOf (t : UpIdx n → Fv) : Matrix (Fin n) (Fin n) Fv := fun i j =>
  if h : i ≤ j then t ⟨(i, j), h⟩ else t ⟨(j, i), (not_le.mp h).le⟩

theorem symOf_transpose (t : UpIdx n → Fv) : (symOf t)ᵀ = symOf t := by
  funext i j
  simp only [Matrix.transpose_apply, symOf]
  by_cases h1 : i ≤ j <;> by_cases h2 : j ≤ i
  · have : i = j := le_antisymm h1 h2
    subst this; simp
  · simp [h1, h2]
  · simp [h1, h2]
  · exact absurd (le_total i j) (by simp [h1, h2])

theorem coordsOf_symOf (t : UpIdx n → Fv) : coordsOf (symOf t) = t := by
  funext p; simp [coordsOf, symOf, p.2]

theorem symOf_coordsOf {X : Matrix (Fin n) (Fin n) Fv} (hX : Xᵀ = X) : symOf (coordsOf X) = X := by
  funext i j
  simp only [symOf, coordsOf]
  by_cases h : i ≤ j
  · simp [h]
  · simp only [h, dite_false]
    have := congrFun (congrFun hX i) j
    simpa using this

theorem symOf_add (t s : UpIdx n → Fv) : symOf (t + s) = symOf t + symOf s := by
  funext i j; simp only [symOf, Matrix.add_apply]; split_ifs <;> rfl

theorem symOf_smul (c : Fv) (t : UpIdx n → Fv) : symOf (c • t) = c • symOf t := by
  funext i j; simp only [symOf, Matrix.smul_apply]; split_ifs <;> rfl

/-- `t ↦ ᵗM t M` in Gram coordinates. -/
def Lc (M : Matrix (Fin n) (Fin n) Fv) : (UpIdx n → Fv) →ₗ[Fv] (UpIdx n → Fv) where
  toFun t := coordsOf (Mᵀ * symOf t * M)
  map_add' t s := by
    funext p; simp [coordsOf, symOf_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c t := by
    funext p; simp [coordsOf, symOf_smul]

theorem Lc_coordsOf (M : Matrix (Fin n) (Fin n) Fv) {X : Matrix (Fin n) (Fin n) Fv} (hX : Xᵀ = X) :
    Lc M (coordsOf X) = coordsOf (Mᵀ * X * M) := by
  show coordsOf (Mᵀ * symOf (coordsOf X) * M) = _
  rw [symOf_coordsOf hX]

theorem Lc_symOf (M : Matrix (Fin n) (Fin n) Fv) (t : UpIdx n → Fv) :
    Lc M t = coordsOf (Mᵀ * symOf t * M) := rfl

theorem symOf_Lc (M : Matrix (Fin n) (Fin n) Fv) (t : UpIdx n → Fv) :
    symOf (Lc M t) = Mᵀ * symOf t * M := by
  rw [Lc_symOf]
  apply symOf_coordsOf
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, symOf_transpose, Matrix.mul_assoc]

theorem Lc_mul (M N : Matrix (Fin n) (Fin n) Fv) (t : UpIdx n → Fv) :
    Lc N (Lc M t) = Lc (M * N) t := by
  rw [Lc_symOf N, symOf_Lc, Lc_symOf (M * N)]
  congr 1
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem Lc_one (t : UpIdx n → Fv) : Lc (1 : Matrix (Fin n) (Fin n) Fv) t = t := by
  rw [Lc_symOf]; simp [coordsOf_symOf]

theorem det_Lc (M : Matrix (Fin n) (Fin n) Fv) : LinearMap.det (Lc M) = M.det ^ (n + 1) := by
  rw [← det_congrSym]
  symm
  refine det_eq_of_intertwine (congrSym M) (LinearEquiv.ofBijective symCoord symCoord_bijective) (Lc M) ?_
  intro t
  show coordsOf ((M)ᵀ * (t : Matrix (Fin n) (Fin n) Fv) * M) = Lc M (coordsOf (t : Matrix (Fin n) (Fin n) Fv))
  rw [Lc_coordsOf M t.2]


theorem vol_Lc (ν : Measure (UpIdx n → Fv)) [ν.IsAddHaarMeasure] (M : Matrix (Fin n) (Fin n) Fv) (hM : M.det ≠ 0)
    (s : Set (UpIdx n → Fv)) :
    ν (Lc M '' s) = ENNReal.ofReal (‖M.det‖ ^ (n + 1)) * ν s := by
  classical
  set M' := LinearMap.toMatrix' (Lc M) with hM'
  have hd : M'.det = M.det ^ (n + 1) := by rw [hM', LinearMap.det_toMatrix', det_Lc]
  have hf : (fun x => M' *ᵥ x) = Lc M := by
    funext x; exact LinearMap.toMatrix'_mulVec _ _
  have := l22_hs_image v ν M' (by rw [hd]; exact pow_ne_zero _ hM) s
  rw [hf, hd, norm_pow] at this
  exact this

variable (v) in
/-- The box `(𝔭^k)^{UpIdx n}` of Gram coordinates. -/
def boxG (k : ℕ) : AddSubgroup (UpIdx n → Fv) :=
  AddSubgroup.pi Set.univ fun _ => latticeV v (k : ℤ)

theorem mem_boxG {k : ℕ} {t : UpIdx n → Fv} : t ∈ boxG v k ↔ ∀ p, Valued.v (t p) ≤ exp (-(k : ℤ)) := by
  simp [boxG, AddSubgroup.mem_pi, mem_latticeV]

variable (v) in
/-- The stabilizer of `𝔬^n` as a set of matrices. -/
def GM : Set (Matrix (Fin n) (Fin n) Fv) := {y | y ∈ intM v ∧ Valued.v y.det = 1}

/-- Gram coordinates of `yᵀ φ y - φ`. -/
def PhiW (φ : Matrix (Fin n) (Fin n) Fv) (y : Matrix (Fin n) (Fin n) Fv) : UpIdx n → Fv :=
  coordsOf (yᵀ * φ * y - φ)

theorem D_symm {φ : Matrix (Fin n) (Fin n) Fv} (hφ : φᵀ = φ) (y : Matrix (Fin n) (Fin n) Fv) :
    (yᵀ * φ * y - φ)ᵀ = yᵀ * φ * y - φ := by
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hφ,
    Matrix.mul_assoc]

theorem symm_entries_iff {D : Matrix (Fin n) (Fin n) Fv} (hD : Dᵀ = D) {k : ℕ} :
    (∀ a b, Valued.v (D a b) ≤ exp (-(k : ℤ))) ↔ coordsOf D ∈ boxG v k := by
  rw [mem_boxG]
  constructor
  · intro h p; exact h _ _
  · intro h a b
    by_cases hab : a ≤ b
    · exact h ⟨(a, b), hab⟩
    · have := h ⟨(b, a), (not_le.mp hab).le⟩
      have e : D b a = D a b := by
        have := congrFun (congrFun hD a) b
        simpa using this
      simp only [coordsOf] at this
      rw [← e]; exact this

theorem gramFiber_std_eq {φ : Matrix (Fin n) (Fin n) Fv} (hφ : φᵀ = φ) (i : ℕ) :
    gramFiber v (std v) φ i = GM v ∩ PhiW φ ⁻¹' ((boxG v i : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv)) := by
  ext x
  simp only [gramFiber, GM, PhiW, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe,
    stabLat_std_iff]
  rw [symm_entries_iff (D_symm hφ x)]

theorem conj_D {b bi y ψ : Matrix (Fin n) (Fin n) Fv} (h1 : b * bi = 1) :
    (b * y * bi)ᵀ * ψ * (b * y * bi) - ψ = biᵀ * (yᵀ * (bᵀ * ψ * b) * y - bᵀ * ψ * b) * bi := by
  have e1 : biᵀ * bᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have e2 : biᵀ * (bᵀ * ψ * b) * bi = ψ := by
    calc biᵀ * (bᵀ * ψ * b) * bi = (biᵀ * bᵀ) * ψ * (b * bi) := by simp only [Matrix.mul_assoc]
      _ = ψ := by rw [e1, h1]; simp
  rw [Matrix.mul_sub, Matrix.sub_mul, e2]
  congr 1
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

theorem mem_map_mv (M : Submodule 𝔬 (Fin n → Fv)) (x : Matrix (Fin n) (Fin n) Fv) (w : Fin n → Fv) :
    w ∈ Submodule.map ((Matrix.mulVecLin x).restrictScalars 𝔬) M ↔ ∃ z ∈ M, x *ᵥ z = w := Iff.rfl

theorem stabLat_locAct (B : GL (Fin n) Fv) (Λ₀ : Submodule 𝔬 (Fin n → Fv)) (x : Matrix (Fin n) (Fin n) Fv) :
    StabLat v (locAct v B Λ₀) x ↔ StabLat v Λ₀ (((B⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) * x * (B : Matrix (Fin n) (Fin n) Fv)) := by
  have hb : ∀ z, (B : Matrix (Fin n) (Fin n) Fv) *ᵥ (((B⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ z) = z :=
    fun z => mulVec_inv_mulVec B z
  have hbi : ∀ z, (((B⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv)) *ᵥ ((B : Matrix (Fin n) (Fin n) Fv) *ᵥ z) = z := by
    intro z; rw [Matrix.mulVec_mulVec]; simp
  unfold StabLat
  constructor
  · intro h
    ext w
    rw [mem_map_mv]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have : x *ᵥ ((B : Matrix (Fin n) (Fin n) Fv) *ᵥ z) ∈ Submodule.map ((Matrix.mulVecLin x).restrictScalars 𝔬) (locAct v B Λ₀) :=
        (mem_map_mv _ _ _).mpr ⟨_, (mem_locAct).mpr ⟨z, hz, rfl⟩, rfl⟩
      rw [h] at this
      obtain ⟨u, hu, hu'⟩ := mem_locAct.mp this
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hu', hbi]
      exact hu
    · intro hw
      have : (B : Matrix (Fin n) (Fin n) Fv) *ᵥ w ∈ Submodule.map ((Matrix.mulVecLin x).restrictScalars 𝔬) (locAct v B Λ₀) := by
        rw [h]; exact mem_locAct.mpr ⟨w, hw, rfl⟩
      obtain ⟨u, hu, hu'⟩ := (mem_map_mv _ _ _).mp this
      obtain ⟨z, hz, hzu⟩ := mem_locAct.mp hu
      refine ⟨z, hz, ?_⟩
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hzu, hu', hbi]
  · intro h
    ext w
    rw [mem_map_mv]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨z, hz, rfl⟩ := mem_locAct.mp hu
      have : (((B⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) * x * (B : Matrix (Fin n) (Fin n) Fv)) *ᵥ z ∈ Λ₀ := by
        rw [← h]; exact (mem_map_mv _ _ _).mpr ⟨z, hz, rfl⟩
      refine mem_locAct.mpr ⟨_, this, ?_⟩
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hb]
    · intro hw
      obtain ⟨z, hz, rfl⟩ := mem_locAct.mp hw
      have : z ∈ Submodule.map ((Matrix.mulVecLin (((B⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) * x * (B : Matrix (Fin n) (Fin n) Fv))).restrictScalars 𝔬) Λ₀ := by
        rw [h]; exact hz
      obtain ⟨u, hu, hu'⟩ := (mem_map_mv _ _ _).mp this
      refine ⟨(B : Matrix (Fin n) (Fin n) Fv) *ᵥ u, mem_locAct.mpr ⟨u, hu, rfl⟩, ?_⟩
      rw [← hu', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hb]


theorem conj_D' {b bi y ψ : Matrix (Fin n) (Fin n) Fv} (h1 : b * bi = 1) (h2 : bi * b = 1) :
    bᵀ * ((b * y * bi)ᵀ * ψ * (b * y * bi) - ψ) * b = yᵀ * (bᵀ * ψ * b) * y - bᵀ * ψ * b := by
  rw [conj_D h1]
  have e1 : bᵀ * biᵀ = 1 := by rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]
  calc bᵀ * (biᵀ * (yᵀ * (bᵀ * ψ * b) * y - bᵀ * ψ * b) * bi) * b
      = (bᵀ * biᵀ) * (yᵀ * (bᵀ * ψ * b) * y - bᵀ * ψ * b) * (bi * b) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [e1, h2]; simp

theorem gramFiber_locAct_eq (B : GL (Fin n) Fv) {ψ : Matrix (Fin n) (Fin n) Fv} (hψ : ψᵀ = ψ) (i : ℕ) :
    gramFiber v (locAct v B (std v)) ψ i =
      (fun y => (B : Matrix (Fin n) (Fin n) Fv) * y * (B : Matrix (Fin n) (Fin n) Fv)⁻¹) ''
        (GM v ∩ PhiW ((B : Matrix (Fin n) (Fin n) Fv)ᵀ * ψ * (B : Matrix (Fin n) (Fin n) Fv)) ⁻¹'
          (Lc (B : Matrix (Fin n) (Fin n) Fv) '' ((boxG v i : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv)))) := by
  set b : Matrix (Fin n) (Fin n) Fv := (B : Matrix (Fin n) (Fin n) Fv) with hb
  have hu : IsUnit b.det := (Matrix.isUnit_iff_isUnit_det _).mp B.isUnit
  have h1 : b * b⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : b⁻¹ * b = 1 := Matrix.nonsing_inv_mul _ hu
  have hcoe : ((B⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) = b⁻¹ := by
    rw [hb]; exact Matrix.coe_units_inv B
  set φ := bᵀ * ψ * b with hφ
  have hφs : φᵀ = φ := by
    rw [hφ, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hψ, Matrix.mul_assoc]
  ext x
  constructor
  · rintro ⟨hst, hent⟩
    rw [stabLat_locAct, hcoe] at hst
    have hy := (stabLat_std_iff v _).mp hst
    have hxe : b * (b⁻¹ * x * b) * b⁻¹ = x := by
      calc b * (b⁻¹ * x * b) * b⁻¹ = (b * b⁻¹) * x * (b * b⁻¹) := by simp only [Matrix.mul_assoc]
        _ = x := by rw [h1]; simp
    refine ⟨b⁻¹ * x * b, ⟨⟨hy.1, hy.2⟩, ?_⟩, hxe⟩
    have hbox : coordsOf (xᵀ * ψ * x - ψ) ∈ boxG v i := (symm_entries_iff (D_symm hψ x)).mp hent
    refine ⟨coordsOf (xᵀ * ψ * x - ψ), hbox, ?_⟩
    rw [Lc_coordsOf b (D_symm hψ x), PhiW]
    congr 1
    conv_lhs => rw [← hxe]
    exact conj_D' h1 h2
  · rintro ⟨y, ⟨hy, t, ht, hLt⟩, rfl⟩
    have hDs := D_symm hφs y
    have hD : yᵀ * φ * y - φ = bᵀ * symOf t * b := by
      have : yᵀ * φ * y - φ = symOf (coordsOf (yᵀ * φ * y - φ)) := (symOf_coordsOf hDs).symm
      rw [this]
      have h3 : coordsOf (yᵀ * φ * y - φ) = Lc b t := hLt.symm
      rw [h3, symOf_Lc]
    refine ⟨?_, ?_⟩
    · rw [stabLat_locAct, hcoe]
      have : b⁻¹ * (b * y * b⁻¹) * b = y := by
        calc b⁻¹ * (b * y * b⁻¹) * b = (b⁻¹ * b) * y * (b⁻¹ * b) := by simp only [Matrix.mul_assoc]
          _ = y := by rw [h2]; simp
      rw [this]
      exact (stabLat_std_iff v _).mpr hy
    · have : (b * y * b⁻¹)ᵀ * ψ * (b * y * b⁻¹) - ψ = symOf t := by
        rw [conj_D h1]
        have hD' : yᵀ * (bᵀ * ψ * b) * y - bᵀ * ψ * b = bᵀ * symOf t * b := hD
        rw [hD']
        have e1 : b⁻¹ᵀ * bᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
        calc b⁻¹ᵀ * (bᵀ * symOf t * b) * b⁻¹ = (b⁻¹ᵀ * bᵀ) * symOf t * (b * b⁻¹) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [e1, h1]; simp
      rw [this]
      refine (symm_entries_iff (symOf_transpose t)).mpr ?_
      rw [coordsOf_symOf]; exact ht

end Sym

section Hensel

open QuadFormsKB.Analysis QuadFormsKB.LocalZeta

/-- **Hensel for an arbitrary perturbation**: a form `T` with all coefficients `≡ Q` mod `π^K` is `Q ∘ g` for an
integral `g ≡ 1` mod `π^(K-d)` (generalizing `core_hensel`, which treats diagonal perturbations). -/
theorem core_hensel' (Q : QuadForm 𝔬 n) {d K : ℕ} (hd : NF.π v ^ d ∣ Q.hessian.det)
    (hd' : ¬ NF.π v ^ (d + 1) ∣ Q.hessian.det) (hK : 2 * d + 1 ≤ K) (T : QuadForm 𝔬 n)
    (hT : ∀ i j, NF.π v ^ K ∣ T.coeff i j - Q.coeff i j) :
    ∃ g : Matrix (Fin n) (Fin n) 𝔬, Q.compMat g = T ∧
      ∀ i j, NF.π v ^ (K - d) ∣ g i j - (1 : Matrix (Fin n) (Fin n) 𝔬) i j := by
  have hπ := NF.irreducible_π v
  have hdetT : NF.π v ^ K ∣ T.hessian.det - Q.hessian.det := by
    have hmap : (Ideal.Quotient.mk (Ideal.span {NF.π v ^ K})).mapMatrix T.hessian =
        (Ideal.Quotient.mk (Ideal.span {NF.π v ^ K})).mapMatrix Q.hessian := by
      ext a b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply]
      have := dvd_add (hT a b) (hT b a)
      convert this using 1
      ring
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det, hmap]
  obtain ⟨u, hu, huu⟩ := DVR.dvr_exact hπ hd hd'
  obtain ⟨s, hs⟩ := hdetT
  have hTdet : T.hessian.det = NF.π v ^ d * (u + NF.π v ^ (K - d) * s) := by
    rw [mul_add, ← mul_assoc, ← pow_add, show d + (K - d) = K by omega, ← hs, ← hu]; ring
  have hdT : NF.π v ^ d ∣ T.hessian.det := ⟨_, hTdet⟩
  have hdT' : ¬ NF.π v ^ (d + 1) ∣ T.hessian.det := by
    intro h
    rw [hTdet, pow_succ] at h
    have h2 := (mul_dvd_mul_iff_left (pow_ne_zero d hπ.ne_zero)).mp h
    apply DVR.dvr_not_dvd_of_isUnit hπ huu
    have : NF.π v ∣ NF.π v ^ (K - d) * s :=
      dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) s
    simpa using dvd_sub h2 this
  have hx : ∀ p : DVR.UpperIdx n, NF.π v ^ K ∣
      DVR.formF Q (fun li : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) 𝔬) li.1 li.2) p - T.coeff p.1.1 p.1.2 := by
    intro p
    have e : DVR.toMat (fun li : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) 𝔬) li.1 li.2) = 1 := rfl
    simp only [DVR.formF, e, QuadForm.compMat_one]
    rw [← neg_sub]
    exact (dvd_neg).mpr (hT p.1.1 p.1.2)
  obtain ⟨y, hy, hyx⟩ := DVR.newton_lift hπ (DVR.formF Q) (DVR.formD Q) (DVR.formF_add_smul Q)
    (fun p : DVR.UpperIdx n => T.coeff p.1.1 p.1.2) d K hK
    (fun x hx' c => DVR.formD_surj Q T (NF.π v) hπ d K hdT hdT' (by omega) x hx' c)
    (fun li : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) 𝔬) li.1 li.2) hx
  refine ⟨DVR.toMat y, QuadForm.ext_upper fun i j hij => ?_, fun i j => hyx (i, j)⟩
  exact congrFun hy ⟨(i, j), hij⟩


theorem l22_hessian_ofUpper (S : Matrix (Fin n) (Fin n) 𝔬) (hS : ∀ x y, S y x = S x y) :
    (QuadForm.ofUpper fun i j => if i = j then S i i else 2 * S i j).hessian = (2 : 𝔬) • S := by
  funext x y
  simp only [QuadForm.hessian, QuadForm.ofUpper, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul]
  rcases lt_trichotomy x y with h | h | h
  · simp [h.le, not_le.mpr h, h.ne, h.ne']
  · subst h; simp; ring
  · simp [h.le, not_le.mpr h, h.ne', h.ne, hS x y]

theorem l22_exists_integral {φ : Matrix (Fin n) (Fin n) Fv} (hφ : φᵀ = φ) (hdet : φ.det ≠ 0) :
    ∃ (a : ℕ) (ψ : Matrix (Fin n) (Fin n) 𝔬), (∀ x y, ψ y x = ψ x y) ∧ ψ.det ≠ 0 ∧
      ψ.map (algebraMap 𝔬 Fv) = (((NF.π v ^ a : 𝔬)) : Fv) • φ := by
  have hsym : ∀ a b, φ b a = φ a b := fun a b => by
    have := congrFun (congrFun hφ a) b
    simpa using this
  have hm : ∀ p : Fin n × Fin n, ∃ m : ℕ, Valued.v (φ p.1 p.2) ≤ exp (m : ℤ) := by
    intro p
    by_cases h0 : Valued.v (φ p.1 p.2) = 0
    · exact ⟨0, by rw [h0]; exact zero_le⟩
    · refine ⟨(WithZero.log (Valued.v (φ p.1 p.2))).toNat, ?_⟩
      conv_lhs => rw [← WithZero.exp_log h0]
      rw [exp_le_exp]; omega
  choose m hm using hm
  set a : ℕ := Finset.univ.sup m with ha
  have hbound : ∀ i j, Valued.v (φ i j) ≤ exp (a : ℤ) := fun i j =>
    (hm (i, j)).trans (by rw [exp_le_exp]; exact_mod_cast Finset.le_sup (f := m) (Finset.mem_univ (i, j)))
  set c : Fv := ((NF.π v ^ a : 𝔬) : Fv) with hcdef
  have hc : Valued.v c = exp (-(a : ℤ)) := core_valued_pow_pi v a
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact WithZero.zero_ne_coe hc
  have hint : ∀ i j, Valued.v (c * φ i j) ≤ 1 := by
    intro i j
    rw [map_mul, hc]
    calc exp (-(a : ℤ)) * Valued.v (φ i j) ≤ exp (-(a : ℤ)) * exp (a : ℤ) := mul_le_mul_right (hbound i j) _
      _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  let ψ : Matrix (Fin n) (Fin n) 𝔬 := fun i j => toO v (c * φ i j) (hint i j)
  have hψ : ψ.map (algebraMap 𝔬 Fv) = c • φ := by
    funext i j; rfl
  have hψsym : ∀ x y, ψ y x = ψ x y := fun x y => Subtype.ext (by
    show c * φ y x = c * φ x y
    rw [hsym])
  refine ⟨a, ψ, hψsym, ?_, hψ⟩
  have hdetψ : (ψ.map (algebraMap 𝔬 Fv)).det ≠ 0 := by
    rw [hψ, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc0) hdet
  intro h0
  apply hdetψ
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]


theorem l22_gram_hensel {φ : Matrix (Fin n) (Fin n) Fv} (hφ : φᵀ = φ) (hdet : φ.det ≠ 0) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ δ : Matrix (Fin n) (Fin n) Fv, δᵀ = δ → (∀ i j, Valued.v (δ i j) ≤ exp (-(K : ℤ))) →
      ∃ g : Matrix (Fin n) (Fin n) Fv, g ∈ intM v ∧ Valued.v g.det = 1 ∧ gᵀ * φ * g = φ + δ := by
  obtain ⟨a, ψ, hψs, hψd, hψ⟩ := l22_exists_integral (v := v) hφ hdet
  have hπ := NF.irreducible_π v
  set Q : QuadForm 𝔬 n := QuadForm.ofUpper fun i j => if i = j then ψ i i else 2 * ψ i j with hQ
  have hQh : Q.hessian = (2 : 𝔬) • ψ := l22_hessian_ofUpper v ψ hψs
  have hQd : Q.hessian.det ≠ 0 := by
    rw [hQh, Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ (NF.two_ne_zero' v)) hψd
  obtain ⟨d, hd, hd'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ hQd
  refine ⟨2 * d + 1, by omega, fun δ hδs hδ => ?_⟩
  set c : Fv := ((NF.π v ^ a : 𝔬) : Fv) with hcdef
  have hc : Valued.v c = exp (-(a : ℤ)) := core_valued_pow_pi v a
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact WithZero.zero_ne_coe hc
  have hz : ∀ i j, Valued.v (c * δ i j) ≤ exp (-((2 * d + 1 : ℕ) : ℤ)) := by
    intro i j
    rw [map_mul, hc]
    calc exp (-(a : ℤ)) * Valued.v (δ i j) ≤ 1 * exp (-((2 * d + 1 : ℕ) : ℤ)) := by
          gcongr
          · exact exp_neg_le_one a
          · exact_mod_cast hδ i j
      _ = _ := one_mul _
  have hz1 : ∀ i j, Valued.v (c * δ i j) ≤ 1 := fun i j => (hz i j).trans (exp_neg_le_one _)
  let z : Matrix (Fin n) (Fin n) 𝔬 := fun i j => toO v (c * δ i j) (hz1 i j)
  have hzF : z.map (algebraMap 𝔬 Fv) = c • δ := by funext i j; rfl
  have hzs : ∀ x y, z y x = z x y := fun x y => Subtype.ext (by
    show c * δ y x = c * δ x y
    have := congrFun (congrFun hδs x) y
    simp only [Matrix.transpose_apply] at this
    rw [this])
  have hzdiv : ∀ i j, NF.π v ^ (2 * d + 1) ∣ z i j := fun i j => by
    rw [core_dvd_iff]; exact hz i j
  set T : QuadForm 𝔬 n := QuadForm.ofUpper fun i j => if i = j then (ψ + z) i i else 2 * (ψ + z) i j with hT
  have hTc : ∀ i j, NF.π v ^ (2 * d + 1) ∣ T.coeff i j - Q.coeff i j := by
    intro i j
    simp only [hT, hQ, QuadForm.ofUpper, Matrix.of_apply]
    split_ifs with h1 h2
    · simp only [Matrix.add_apply, add_sub_cancel_left]; exact hzdiv i i
    · simp only [Matrix.add_apply]
      have : 2 * (ψ i j + z i j) - 2 * ψ i j = 2 * z i j := by ring
      rw [this]; exact dvd_mul_of_dvd_right (hzdiv i j) 2
    · simp
  obtain ⟨g, hg, hgm⟩ := core_hensel' v Q hd hd' le_rfl T hTc
  have hS : ∀ x y, (ψ + z) y x = (ψ + z) x y := fun x y => by
    simp only [Matrix.add_apply, hψs x y, hzs x y]
  have hgram : gᵀ * ψ * g = ψ + z := by
    have h1 := QuadForm.hessian_compMat Q g
    rw [hg, hT, l22_hessian_ofUpper v (ψ + z) hS, hQh, Matrix.mul_smul, Matrix.smul_mul] at h1
    exact (smul_right_injective _ (NF.two_ne_zero' v) h1).symm
  set g' : Matrix (Fin n) (Fin n) Fv := g.map (algebraMap 𝔬 Fv) with hg'
  have hm : 1 ≤ 2 * d + 1 - d := by omega
  have hb : g' ∈ ballOne v (2 * d + 1 - d) := core_g_mem_ballOne v hgm
  refine ⟨g', ballOne_subset_intM v _ hb, valued_det_eq_one v hm hb, ?_⟩
  have h2 : g'ᵀ * (c • φ) * g' = c • (φ + δ) := by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) 𝔬 => M.map (algebraMap 𝔬 Fv)) hgram
    have hadd : (ψ + z).map (algebraMap 𝔬 Fv) = ψ.map (algebraMap 𝔬 Fv) + z.map (algebraMap 𝔬 Fv) :=
      Matrix.map_add _ (fun a b => map_add _ a b) ψ z
    simp only [Matrix.map_mul, Matrix.transpose_map, hadd, hψ, hzF] at this
    rw [hg', smul_add]; exact this
  rw [Matrix.mul_smul, Matrix.smul_mul] at h2
  exact smul_right_injective _ hc0 h2

end Hensel

section Nu
variable {v}

open QuadFormsKB.Analysis

theorem isClosed_boxG (k : ℕ) : IsClosed ((boxG v k : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv)) := by
  show IsClosed (Set.pi Set.univ fun _ : UpIdx n => (latticeV v (k : ℤ) : Set Fv))
  exact isClosed_set_pi fun _ _ => (isCompact_latticeV v _).isClosed

theorem measurableSet_boxG (k : ℕ) : MeasurableSet ((boxG v k : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv)) :=
  (isClosed_boxG (v := v) k).measurableSet

theorem measurableSet_GM : MeasurableSet (GM v : Set (Matrix (Fin n) (Fin n) Fv)) := by
  have h1 : MeasurableSet ((fun y : Matrix (Fin n) (Fin n) Fv => y.det) ⁻¹'
      ((latticeV v 0 : Set Fv) \ (latticeV v 1 : Set Fv))) :=
    ((measurableSet_latticeV v 0).diff (measurableSet_latticeV v 1)).preimage
      (Continuous.matrix_det continuous_id).measurable
  have h2 : GM v = intM v ∩ ((fun y : Matrix (Fin n) (Fin n) Fv => y.det) ⁻¹'
      ((latticeV v 0 : Set Fv) \ (latticeV v 1 : Set Fv))) := by
    ext y
    simp only [GM, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_diff, SetLike.mem_coe,
      mem_latticeV]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h; rw [h]
      refine ⟨by simp, ?_⟩
      exact not_le.mpr (by rw [← exp_zero]; exact exp_lt_exp.mpr (by norm_num))
    · rintro ⟨h0, h1⟩
      simp only [neg_zero, exp_zero] at h0
      have hz0 : y.det ≠ 0 := by intro h; rw [h] at h1; exact h1 (by simp)
      have hvz : Valued.v y.det ≠ 0 := (Valued.v).ne_zero_iff.mpr hz0
      rw [← WithZero.exp_log hvz] at h0 h1 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h0
      rw [WithZero.exp_le_exp] at h1
      rw [WithZero.exp_eq_one]
      omega
  rw [h2]
  exact (measurableSet_intM v).inter h1

theorem continuous_PhiW (φ : Matrix (Fin n) (Fin n) Fv) : Continuous (PhiW φ) := by
  refine continuous_pi fun p => ?_
  show Continuous fun y : Matrix (Fin n) (Fin n) Fv => (yᵀ * φ * y - φ) p.1.1 p.1.2
  exact ((((continuous_id.matrix_transpose).matrix_mul continuous_const).matrix_mul continuous_id).sub
    continuous_const).matrix_elem _ _

variable (v) in
/-- The push-forward of `volM|_{GL_n(𝔬)}` under `y ↦ yᵀ φ y - φ` (in Gram coordinates). -/
def nuM (φ : Matrix (Fin n) (Fin n) Fv) : Measure (UpIdx n → Fv) := ((volM v).restrict (GM v)).map (PhiW φ)

theorem nuM_apply (φ : Matrix (Fin n) (Fin n) Fv) {E : Set (UpIdx n → Fv)} (hE : MeasurableSet E) :
    nuM v φ E = volM v (PhiW φ ⁻¹' E ∩ GM v) := by
  rw [nuM, Measure.map_apply (continuous_PhiW φ).measurable hE,
    Measure.restrict_apply ((continuous_PhiW φ).measurable hE)]

theorem GM_subset_intM : (GM v : Set (Matrix (Fin n) (Fin n) Fv)) ⊆ intM v := fun _ h => h.1

instance isFinite_nuM (φ : Matrix (Fin n) (Fin n) Fv) : IsFiniteMeasure (nuM v φ) := by
  refine ⟨?_⟩
  rw [nuM, Measure.map_apply (continuous_PhiW φ).measurable MeasurableSet.univ, Measure.restrict_apply
    ((continuous_PhiW φ).measurable MeasurableSet.univ)]
  refine lt_of_le_of_lt (measure_mono (Set.inter_subset_right.trans GM_subset_intM)) ?_
  exact (QuadFormsKB.Tamagawa.Measure.isCompact_intMat v).measure_lt_top

theorem transpose_mem_intM {g : Matrix (Fin n) (Fin n) Fv} (hg : g ∈ intM v) : gᵀ ∈ intM v :=
  fun a b => hg b a

theorem Lc_mem_boxG {g : Matrix (Fin n) (Fin n) Fv} (hg : g ∈ intM v) {j : ℕ} {t : UpIdx n → Fv}
    (ht : t ∈ boxG v j) : Lc g t ∈ boxG v j := by
  have hS : ∀ a b, Valued.v (symOf t a b) ≤ exp (-(j : ℤ)) :=
    (symm_entries_iff (symOf_transpose t)).mpr (by rw [coordsOf_symOf]; exact ht)
  have := f2_mul_bound v (transpose_mem_intM hg) hg hS
  rw [mem_boxG]; intro p; exact this _ _

theorem Lc_mem_boxG_iff {g : Matrix (Fin n) (Fin n) Fv} (hg : g ∈ intM v) (hd : Valued.v g.det = 1) {j : ℕ}
    {t : UpIdx n → Fv} : Lc g t ∈ boxG v j ↔ t ∈ boxG v j := by
  refine ⟨fun h => ?_, Lc_mem_boxG hg⟩
  obtain ⟨hgi, hu⟩ := f1_inv_data v hg hd
  have := Lc_mem_boxG hgi h
  rwa [Lc_mul, Matrix.mul_nonsing_inv _ hu, Lc_one] at this

theorem GM_mul_right_iff {g : Matrix (Fin n) (Fin n) Fv} (hg : g ∈ intM v) (hd : Valued.v g.det = 1)
    {y : Matrix (Fin n) (Fin n) Fv} : y * g ∈ GM v ↔ y ∈ GM v := by
  obtain ⟨hgi, hu⟩ := f1_inv_data v hg hd
  simp only [GM, Set.mem_ofPred_eq, Matrix.det_mul, map_mul, hd, mul_one]
  refine and_congr_left fun hdy => ?_
  constructor
  · intro h
    have := core_mul_mem_intM v h hgi
    rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one] at this
  · intro h; exact core_mul_mem_intM v h hg

theorem PhiW_mul {φ : Matrix (Fin n) (Fin n) Fv} (hφ : φᵀ = φ) (y g : Matrix (Fin n) (Fin n) Fv) :
    PhiW φ (y * g) = Lc g (PhiW φ y) + coordsOf (gᵀ * φ * g - φ) := by
  rw [PhiW, PhiW, Lc_coordsOf g (D_symm hφ y)]
  have e : (y * g)ᵀ * φ * (y * g) - φ = gᵀ * (yᵀ * φ * y - φ) * g + (gᵀ * φ * g - φ) := by
    simp only [Matrix.transpose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  rw [e]; rfl

/-- **Local constancy**: translating by a small `w` does not change the `ν`-measure of a box. -/
theorem nuM_translate {φ : Matrix (Fin n) (Fin n) Fv} (hφ : φᵀ = φ) (hdet : φ.det ≠ 0) :
    ∃ K : ℕ, ∀ w ∈ boxG v K, ∀ j : ℕ,
      nuM v φ {u | u - w ∈ ((boxG v j : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv))} =
        nuM v φ ((boxG v j : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv)) := by
  obtain ⟨K, hK1, hK⟩ := l22_gram_hensel v hφ hdet
  refine ⟨K, fun w hw j => ?_⟩
  have hδs := symOf_transpose w
  have hδ : ∀ i j, Valued.v (symOf w i j) ≤ exp (-(K : ℤ)) :=
    (symm_entries_iff hδs).mpr (by rw [coordsOf_symOf]; exact hw)
  obtain ⟨g, hgi, hgd, hgφ⟩ := hK (symOf w) hδs hδ
  have hA : MeasurableSet {u : UpIdx n → Fv | u - w ∈ ((boxG v j : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv))} :=
    (measurableSet_boxG j).preimage (measurable_id.sub_const w)
  rw [nuM_apply φ hA, nuM_apply φ (measurableSet_boxG j)]
  have hpre : (fun y => y * g) ⁻¹' (PhiW φ ⁻¹' {u | u - w ∈ ((boxG v j : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv))} ∩ GM v) =
      PhiW φ ⁻¹' ((boxG v j : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv)) ∩ GM v := by
    ext y
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, SetLike.mem_coe, GM_mul_right_iff hgi hgd]
    refine and_congr_left fun _ => ?_
    rw [PhiW_mul hφ, hgφ, add_sub_cancel_left, coordsOf_symOf, add_sub_cancel_right, Lc_mem_boxG_iff hgi hgd]
  have hmp := measurePreserving_mulRightM v hgi hgd
  rw [← hpre]
  exact (hmp.measure_preimage (((continuous_PhiW φ).measurable hA).inter (measurableSet_GM)).nullMeasurableSet).symm

/-- **Counting by Fubini**: if `S` is a union of cosets of the subgroup `H`, and `ν` gives all the cosets `w + H`
(`w ∈ S`) the same mass as `H`, then `ν(S) μ(H) = ν(H) μ(S)`. -/
theorem counting_fubini (μ ν : Measure (UpIdx n → Fv)) [μ.IsAddLeftInvariant] [IsFiniteMeasure ν]
    (H : AddSubgroup (UpIdx n → Fv)) (hH : MeasurableSet (H : Set (UpIdx n → Fv)))
    (S : Set (UpIdx n → Fv)) (hS : MeasurableSet S) (hSfin : μ S ≠ ⊤)
    (hSH : ∀ u ∈ S, ∀ h ∈ H, u + h ∈ S)
    (hν : ∀ w ∈ S, ν {u | u - w ∈ (H : Set (UpIdx n → Fv))} = ν (H : Set (UpIdx n → Fv))) :
    μ (H : Set (UpIdx n → Fv)) * ν S = ν (H : Set (UpIdx n → Fv)) * μ S := by
  classical
  haveI : IsFiniteMeasure (μ.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hSfin⟩
  set s : Set ((UpIdx n → Fv) × (UpIdx n → Fv)) := {p | p.2 - p.1 ∈ (H : Set (UpIdx n → Fv))} with hs
  have hsm : MeasurableSet s := (measurable_snd.sub measurable_fst) hH
  have h1 := Measure.prod_apply (μ := μ.restrict S) (ν := ν) hsm
  have h2 := Measure.prod_apply_symm (μ := μ.restrict S) (ν := ν) hsm
  have e1 : ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂(μ.restrict S) = ν (H : Set (UpIdx n → Fv)) * μ S := by
    rw [lintegral_congr_ae (g := fun _ => ν (H : Set (UpIdx n → Fv)))]
    · rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]
    · filter_upwards [ae_restrict_mem hS] with x hx
      exact hν x hx
  have e2 : ∫⁻ y, (μ.restrict S) ((fun x => (x, y)) ⁻¹' s) ∂ν = μ (H : Set (UpIdx n → Fv)) * ν S := by
    rw [← lintegral_indicator_const hS]
    refine lintegral_congr fun y => ?_
    have hm : MeasurableSet ((fun x => (x, y)) ⁻¹' s) := measurable_prodMk_right hsm
    rw [Measure.restrict_apply hm]
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy]
      have : (fun x => (x, y)) ⁻¹' s ∩ S = (fun x => x + (-y)) ⁻¹' (H : Set (UpIdx n → Fv)) := by
        ext x
        simp only [hs, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, SetLike.mem_coe]
        constructor
        · rintro ⟨h, -⟩
          have := H.neg_mem h
          simpa [sub_eq_add_neg] using this
        · intro h
          have h' : y - x ∈ H := by
            have := H.neg_mem h
            simpa [sub_eq_add_neg, add_comm] using this
          refine ⟨h', ?_⟩
          have := hSH y hy (x - y) (by simpa [sub_eq_add_neg] using h)
          simpa using this
      rw [this, measure_preimage_add_right]
    · rw [Set.indicator_of_notMem hy]
      have : (fun x => (x, y)) ⁻¹' s ∩ S = ∅ := by
        ext x
        simp only [hs, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, SetLike.mem_coe,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro h hx
        apply hy
        have := hSH x hx (y - x) h
        simpa using this
      rw [this, measure_empty]
  rw [e1] at h1
  rw [e2] at h2
  rw [← h1, ← h2]

theorem mu_box_ne (k : ℕ) :
    (Measure.pi fun _ : UpIdx n => haarV v) ((boxG v k : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv)) ≠ 0 ∧
    (Measure.pi fun _ : UpIdx n => haarV v) ((boxG v k : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv)) ≠ ⊤ := by
  have e : ((boxG v k : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv)) =
      Set.pi Set.univ fun _ : UpIdx n => (latticeV v (k : ℤ) : Set Fv) := rfl
  rw [e, Measure.pi_pi]
  simp only [haarV_latticeV_nat]
  have hq0 : (DVR.q 𝔬 : ℝ≥0∞) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast (DVR.q_pos (R := 𝔬)).ne')
  have hqt : (DVR.q 𝔬 : ℝ≥0∞) ^ k ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  constructor
  · exact Finset.prod_ne_zero_iff.mpr fun _ _ => ENNReal.inv_ne_zero.mpr hqt
  · exact ENNReal.prod_ne_top fun _ _ => ENNReal.inv_ne_top.mpr hq0

theorem continuous_Lc (M : Matrix (Fin n) (Fin n) Fv) : Continuous (Lc M) :=
  LinearMap.continuous_of_finiteDimensional _

theorem boxG_mono {k k' : ℕ} (h : k' ≤ k) :
    ((boxG v k : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv)) ⊆ ((boxG v k' : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv)) := by
  intro t ht
  rw [SetLike.mem_coe, mem_boxG] at ht ⊢
  intro p
  exact (ht p).trans (by rw [exp_le_exp]; omega)

theorem l22_exists_bound (M : Matrix (Fin n) (Fin n) Fv) : ∃ m : ℕ, ∀ a b, Valued.v (M a b) ≤ exp (m : ℤ) := by
  have hm : ∀ p : Fin n × Fin n, ∃ m : ℕ, Valued.v (M p.1 p.2) ≤ exp (m : ℤ) := by
    intro p
    by_cases h0 : Valued.v (M p.1 p.2) = 0
    · exact ⟨0, by rw [h0]; exact zero_le⟩
    · refine ⟨(WithZero.log (Valued.v (M p.1 p.2))).toNat, ?_⟩
      conv_lhs => rw [← WithZero.exp_log h0]
      rw [exp_le_exp]; omega
  choose m hm using hm
  refine ⟨Finset.univ.sup m, fun a b => (hm (a, b)).trans ?_⟩
  rw [exp_le_exp]; exact_mod_cast Finset.le_sup (f := m) (Finset.mem_univ (a, b))

theorem Lc_mem_boxG_of_bound {M : Matrix (Fin n) (Fin n) Fv} {m : ℕ}
    (hM : ∀ a b, Valued.v (M a b) ≤ exp (m : ℤ)) {k : ℕ} {t : UpIdx n → Fv}
    (ht : t ∈ boxG v (k + 2 * m)) : Lc M t ∈ boxG v k := by
  have hS : ∀ a b, Valued.v (symOf t a b) ≤ exp (-((k + 2 * m : ℕ) : ℤ)) :=
    (symm_entries_iff (symOf_transpose t)).mpr (by rw [coordsOf_symOf]; exact ht)
  have hMT : ∀ a b, Valued.v (Mᵀ a b) ≤ exp (m : ℤ) := fun a b => hM b a
  have h1 := valued_mul_apply_le v hMT hS
  have h2 := valued_mul_apply_le v h1 hM
  have e : exp (m : ℤ) * exp (-((k + 2 * m : ℕ) : ℤ)) * exp (m : ℤ) = exp (-(k : ℤ)) := by
    rw [← exp_add, ← exp_add]; congr 1; push_cast; ring
  rw [e] at h2
  rw [mem_boxG]; intro p; exact h2 _ _

/-- **The key identity**: for large `i`, `ν(Lc_M(box i)) = |det M|^{n+1} ν(box i)`. -/
theorem nuM_Lc_box {φ : Matrix (Fin n) (Fin n) Fv} (hφ : φᵀ = φ) (hdet : φ.det ≠ 0)
    {M : Matrix (Fin n) (Fin n) Fv} (hM : M.det ≠ 0) :
    ∃ I : ℕ, ∀ i ≥ I, nuM v φ (Lc M '' ((boxG v i : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv))) =
      ENNReal.ofReal (‖M.det‖ ^ (n + 1)) * nuM v φ ((boxG v i : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv)) := by
  obtain ⟨K, hK⟩ := nuM_translate hφ hdet
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hu
  obtain ⟨m1, hm1⟩ := l22_exists_bound M
  obtain ⟨m2, hm2⟩ := l22_exists_bound M⁻¹
  set m := m1 + m2 with hm
  have hbM : ∀ a b, Valued.v (M a b) ≤ exp (m : ℤ) := fun a b =>
    (hm1 a b).trans (by rw [exp_le_exp]; omega)
  have hbMi : ∀ a b, Valued.v (M⁻¹ a b) ≤ exp (m : ℤ) := fun a b =>
    (hm2 a b).trans (by rw [exp_le_exp]; omega)
  refine ⟨K + 2 * m, fun i hi => ?_⟩
  set μ : Measure (UpIdx n → Fv) := Measure.pi fun _ : UpIdx n => haarV v with hμ
  set Bi : Set (UpIdx n → Fv) := ((boxG v i : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv)) with hBi
  set Bj : Set (UpIdx n → Fv) := ((boxG v (i + 2 * m) : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv)) with hBj
  set S : Set (UpIdx n → Fv) := Lc M '' Bi with hS
  have hL1 : ∀ t, Lc M⁻¹ (Lc M t) = t := fun t => by rw [Lc_mul, h1, Lc_one]
  have hL2 : ∀ s, Lc M (Lc M⁻¹ s) = s := fun s => by rw [Lc_mul, h2, Lc_one]
  have hImg : S = Lc M⁻¹ ⁻¹' Bi := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩; simp only [Set.mem_preimage, hL1]; exact ht
    · intro hs; exact ⟨Lc M⁻¹ s, hs, hL2 s⟩
  have hSm : MeasurableSet S := by
    rw [hImg]; exact ((isClosed_boxG i).preimage (continuous_Lc M⁻¹)).measurableSet
  have hSK : S ⊆ (boxG v K : AddSubgroup (UpIdx n → Fv)) := by
    rintro _ ⟨t, ht, rfl⟩
    have ht' : t ∈ boxG v ((i - 2 * m) + 2 * m) := by
      have : i - 2 * m + 2 * m = i := by omega
      rw [this]; exact ht
    have := Lc_mem_boxG_of_bound hbM ht'
    exact boxG_mono (by omega) this
  have hBjS : Bj ⊆ S := by
    intro s hs
    exact ⟨Lc M⁻¹ s, Lc_mem_boxG_of_bound hbMi (k := i) hs, hL2 s⟩
  have hBiK : Bi ⊆ (boxG v K : AddSubgroup (UpIdx n → Fv)) := boxG_mono (by omega)
  have hvol : μ S = ENNReal.ofReal (‖M.det‖ ^ (n + 1)) * μ Bi := vol_Lc μ M hM Bi
  have hSfin : μ S ≠ ⊤ := by
    rw [hvol]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (mu_box_ne i).2
  have hA := counting_fubini μ (nuM v φ) (boxG v (i + 2 * m)) (measurableSet_boxG _) S hSm hSfin
    (fun u hu h hh => by
      obtain ⟨t, ht, rfl⟩ := hu
      obtain ⟨t', ht', rfl⟩ := hBjS hh
      exact ⟨t + t', (boxG v i).add_mem ht ht', map_add _ _ _⟩)
    (fun w hw => hK w (hSK hw) _)
  have hBfin : μ Bi ≠ ⊤ := (mu_box_ne i).2
  have hB := counting_fubini μ (nuM v φ) (boxG v (i + 2 * m)) (measurableSet_boxG _) Bi (measurableSet_boxG _) hBfin
    (fun u hu h hh => (boxG v i).add_mem hu (boxG_mono (by omega) hh))
    (fun w hw => hK w (hBiK hw) _)
  have hj0 := (mu_box_ne (v := v) (n := n) (i + 2 * m)).1
  have hjt := (mu_box_ne (v := v) (n := n) (i + 2 * m)).2
  rw [hvol] at hA
  refine (ENNReal.mul_right_inj hj0 hjt).mp ?_
  calc μ Bj * nuM v φ S = nuM v φ Bj * (ENNReal.ofReal (‖M.det‖ ^ (n + 1)) * μ Bi) := hA
    _ = ENNReal.ofReal (‖M.det‖ ^ (n + 1)) * (nuM v φ Bj * μ Bi) := by ring
    _ = ENNReal.ofReal (‖M.det‖ ^ (n + 1)) * (μ Bj * nuM v φ Bi) := by rw [hB]
    _ = _ := by ring

theorem measurableSet_Lc_image {M : Matrix (Fin n) (Fin n) Fv} (hM : M.det ≠ 0) (k : ℕ) :
    MeasurableSet (Lc M '' ((boxG v k : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv))) := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hu
  have hImg : Lc M '' ((boxG v k : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv)) =
      Lc M⁻¹ ⁻¹' ((boxG v k : AddSubgroup (UpIdx n → Fv)) : Set (UpIdx n → Fv)) := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩; simp only [Set.mem_preimage, Lc_mul, h1, Lc_one]; exact ht
    · intro hs; exact ⟨Lc M⁻¹ s, hs, by rw [Lc_mul, h2, Lc_one]⟩
  rw [hImg]
  exact ((isClosed_boxG k).preimage (continuous_Lc M⁻¹)).measurableSet

end Nu

section Main
variable {v}

theorem gramRatio_locAct_eventually (B : GL (Fin n) Fv) {ψ : Matrix (Fin n) (Fin n) Fv} (hψ : ψᵀ = ψ)
    (hdet : ψ.det ≠ 0) :
    ∃ I : ℕ, ∀ i ≥ I, gramRatio v (locAct v B (std v)) ψ i =
      ‖(B : Matrix (Fin n) (Fin n) Fv).det‖ ^ (n + 1) *
        gramRatio v (std v) ((B : Matrix (Fin n) (Fin n) Fv)ᵀ * ψ * (B : Matrix (Fin n) (Fin n) Fv)) i := by
  set b : Matrix (Fin n) (Fin n) Fv := (B : Matrix (Fin n) (Fin n) Fv) with hb
  have hbd : b.det ≠ 0 := GeneralLinearGroup.det_ne_zero B
  set φ := bᵀ * ψ * b with hφ
  have hφs : φᵀ = φ := by
    rw [hφ, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hψ, Matrix.mul_assoc]
  have hφd : φ.det ≠ 0 := by
    rw [hφ, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hbd hdet) hbd
  obtain ⟨I, hI⟩ := nuM_Lc_box (v := v) hφs hφd hbd
  refine ⟨I, fun i hi => ?_⟩
  have hvol : volM v (gramFiber v (locAct v B (std v)) ψ i) =
      ENNReal.ofReal (‖b.det‖ ^ (n + 1)) * volM v (gramFiber v (std v) φ i) := by
    rw [gramFiber_locAct_eq B hψ i, l22_vol_conj_image v hbd, gramFiber_std_eq hφs]
    have h := hI i hi
    rw [nuM_apply φ (measurableSet_Lc_image hbd i), nuM_apply φ (measurableSet_boxG i)] at h
    rw [Set.inter_comm (GM v), Set.inter_comm (GM v)]
    exact h
  unfold gramRatio
  rw [hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  ring

theorem hankeBeta_locAct (B : GL (Fin n) Fv) {ψ : Matrix (Fin n) (Fin n) Fv} (hψ : ψᵀ = ψ)
    (hdet : ψ.det ≠ 0) :
    hankeBeta v (locAct v B (std v)) ψ = ‖(B : Matrix (Fin n) (Fin n) Fv).det‖ ^ (n + 1) *
      hankeBeta v (std v) ((B : Matrix (Fin n) (Fin n) Fv)ᵀ * ψ * (B : Matrix (Fin n) (Fin n) Fv)) := by
  set b : Matrix (Fin n) (Fin n) Fv := (B : Matrix (Fin n) (Fin n) Fv) with hb
  have hbd : b.det ≠ 0 := GeneralLinearGroup.det_ne_zero B
  set φ := bᵀ * ψ * b with hφ
  have hφs : φᵀ = φ := by
    rw [hφ, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hψ, Matrix.mul_assoc]
  have hφd : φ.det ≠ 0 := by
    rw [hφ, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hbd hdet) hbd
  obtain ⟨I, hI⟩ := gramRatio_locAct_eventually B hψ hdet
  have h1 := gramRatio_std_eventually_eq v hφs hφd
  have hev : ∀ᶠ i in atTop, gramRatio v (locAct v B (std v)) ψ i =
      ‖b.det‖ ^ (n + 1) * (2 * hankeBeta v (std v) φ) := by
    filter_upwards [eventually_ge_atTop I, h1] with i hi hi1
    rw [hI i hi, hi1]
  have hlim := f2_limUnder_eq_of_eventually_eq hev
  conv_lhs => unfold hankeBeta
  rw [hlim]
  ring

theorem congr_transpose_eq {b ψ : Matrix (Fin n) (Fin n) Fv} (hψ : ψᵀ = ψ) : (bᵀ * ψ * b)ᵀ = bᵀ * ψ * b := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hψ, Matrix.mul_assoc]

theorem congr_det_ne {b ψ : Matrix (Fin n) (Fin n) Fv} (hb : b.det ≠ 0) (hψ : ψ.det ≠ 0) :
    (bᵀ * ψ * b).det ≠ 0 := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero (mul_ne_zero hb hψ) hb

theorem l22_gramRatio_eventually_eq (B : GL (Fin n) Fv) {ψ : Matrix (Fin n) (Fin n) Fv} (hψ : ψᵀ = ψ)
    (hdet : ψ.det ≠ 0) :
    ∀ᶠ i in atTop, gramRatio v (locAct v B (std v)) ψ i = 2 * hankeBeta v (locAct v B (std v)) ψ := by
  have hbd : (B : Matrix (Fin n) (Fin n) Fv).det ≠ 0 := GeneralLinearGroup.det_ne_zero B
  obtain ⟨I, hI⟩ := gramRatio_locAct_eventually B hψ hdet
  have h1 := gramRatio_std_eventually_eq v (congr_transpose_eq (b := (B : Matrix (Fin n) (Fin n) Fv)) hψ)
    (congr_det_ne hbd hdet)
  rw [hankeBeta_locAct B hψ hdet]
  filter_upwards [eventually_ge_atTop I, h1] with i hi hi1
  rw [hI i hi, hi1]; ring

theorem l22_hankeBeta_congr (A B : GL (Fin n) Fv) {ψ : Matrix (Fin n) (Fin n) Fv} (hψ : ψᵀ = ψ) (hdet : ψ.det ≠ 0) :
    hankeBeta v (locAct v B (std v)) ((A : Matrix (Fin n) (Fin n) Fv)ᵀ * ψ * (A : Matrix (Fin n) (Fin n) Fv)) =
      ‖(A : Matrix (Fin n) (Fin n) Fv).det‖ ^ (-((n : ℤ) + 1)) * hankeBeta v (locAct v (A * B) (std v)) ψ := by
  have hAd : (A : Matrix (Fin n) (Fin n) Fv).det ≠ 0 := GeneralLinearGroup.det_ne_zero A
  have hBd : (B : Matrix (Fin n) (Fin n) Fv).det ≠ 0 := GeneralLinearGroup.det_ne_zero B
  have h1 := hankeBeta_locAct B (congr_transpose_eq (b := (A : Matrix (Fin n) (Fin n) Fv)) hψ)
    (congr_det_ne hAd hdet)
  have h2 := hankeBeta_locAct (A * B) hψ hdet
  have e : (B : Matrix (Fin n) (Fin n) Fv)ᵀ * ((A : Matrix (Fin n) (Fin n) Fv)ᵀ * ψ * (A : Matrix (Fin n) (Fin n) Fv)) *
      (B : Matrix (Fin n) (Fin n) Fv) =
      ((A * B : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv)ᵀ * ψ * ((A * B : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) := by
    simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [h1, h2, e, Units.val_mul, Matrix.det_mul, norm_mul, mul_pow]
  have hne : ‖(A : Matrix (Fin n) (Fin n) Fv).det‖ ^ (n + 1) ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr hAd)
  have : -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, _root_.zpow_neg, zpow_natCast]
  field_simp

theorem hankeBeta_std_one_pos : 0 < hankeBeta v (std v) (1 : Matrix (Fin n) (Fin n) Fv) := by
  have h := gramRatio_std_eventually_eq v (Matrix.transpose_one : (1 : Matrix (Fin n) (Fin n) Fv)ᵀ = 1)
    (by rw [Matrix.det_one]; exact one_ne_zero)
  obtain ⟨i, hi, hi1⟩ := (h.and (eventually_ge_atTop 1)).exists
  have hsub : ballOne v i ⊆ gramFiber v (std v) (1 : Matrix (Fin n) (Fin n) Fv) i := by
    intro X hX
    refine ⟨(stabLat_std_iff v X).mpr ⟨ballOne_subset_intM v i hX, valued_det_eq_one v hi1 hX⟩, ?_⟩
    set E : Matrix (Fin n) (Fin n) Fv := X - 1 with hE
    have hEb : ∀ a b, Valued.v (E a b) ≤ exp (-(i : ℤ)) := fun a b => hX a b
    have hEt : ∀ a b, Valued.v (Eᵀ a b) ≤ exp (-(i : ℤ)) := fun a b => hEb b a
    have e : Xᵀ * 1 * X - 1 = Eᵀ + E + Eᵀ * E := by
      have hX' : X = E + 1 := by rw [hE]; abel
      rw [hX']
      simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.mul_one, Matrix.add_mul, Matrix.mul_add,
        Matrix.one_mul]
      abel
    intro a b
    rw [e, Matrix.add_apply, Matrix.add_apply]
    have h3 : Valued.v ((Eᵀ * E) a b) ≤ exp (-(i : ℤ)) := by
      refine (valued_mul_apply_le v hEt hEb a b).trans ?_
      calc exp (-(i : ℤ)) * exp (-(i : ℤ)) ≤ exp (-(i : ℤ)) * 1 := mul_le_mul_right (exp_neg_le_one i) _
        _ = _ := mul_one _
    exact Valuation.map_add_le _ (Valuation.map_add_le _ (hEt a b) (hEb a b)) h3
  have hpos : 0 < gramRatio v (std v) (1 : Matrix (Fin n) (Fin n) Fv) i := by
    unfold gramRatio
    have hq : (0 : ℝ) < (DVR.q 𝔬 : ℝ) := by exact_mod_cast DVR.q_pos (R := 𝔬)
    refine mul_pos (pow_pos hq _) (ENNReal.toReal_pos ?_ ?_)
    · refine ne_of_gt (lt_of_lt_of_le ((isOpen_ballOne v i).measure_pos (volM v) ⟨1, one_mem_ballOne v i⟩)
        (measure_mono hsub))
    · refine (lt_of_le_of_lt (measure_mono (t := intM v) ?_)
        (QuadFormsKB.Tamagawa.Measure.isCompact_intMat v).measure_lt_top).ne
      intro x hx
      exact ((stabLat_std_iff v x).mp hx.1).1
  rw [hi] at hpos
  linarith

theorem l22_printed_false :
    ∃ (A : GL (Fin 1) Fv) (ψ : Matrix (Fin 1) (Fin 1) Fv), ψᵀ = ψ ∧ ψ.det ≠ 0 ∧
      hankeBeta v (std v) ((A : Matrix (Fin 1) (Fin 1) Fv)ᵀ * ψ * (A : Matrix (Fin 1) (Fin 1) Fv)) ≠
        ‖(A : Matrix (Fin 1) (Fin 1) Fv).det‖ ^ (1 + 1) * hankeBeta v (locAct v A (std v)) ψ := by
  set p : Fv := ((NF.π v : 𝔬) : Fv) with hp
  have hpv : Valued.v p = exp (-1 : ℤ) := NF.valued_π v
  have hp0 : p ≠ 0 := by
    intro h; rw [h, map_zero] at hpv; exact WithZero.zero_ne_coe hpv
  let P : Matrix (Fin 1) (Fin 1) Fv := Matrix.of fun _ _ => p
  have hPd : P.det = p := by simp [P, Matrix.det_unique]
  let A : GL (Fin 1) Fv := GeneralLinearGroup.mkOfDetNeZero P (by rw [hPd]; exact hp0)
  have hA : (A : Matrix (Fin 1) (Fin 1) Fv) = P := rfl
  have h1d : (1 : Matrix (Fin 1) (Fin 1) Fv).det ≠ 0 := by rw [Matrix.det_one]; exact one_ne_zero
  refine ⟨A, 1, Matrix.transpose_one, h1d, ?_⟩
  have hY := hankeBeta_locAct A (ψ := (1 : Matrix (Fin 1) (Fin 1) Fv)) Matrix.transpose_one h1d
  rw [hY]
  have hM : (A : Matrix (Fin 1) (Fin 1) Fv)ᵀ * 1 * (A : Matrix (Fin 1) (Fin 1) Fv) =
      (p * p) • (1 : Matrix (Fin 1) (Fin 1) Fv) := by
    funext i j
    fin_cases i; fin_cases j
    simp [hA, P, Matrix.mul_apply]
  have hdA : (A : Matrix (Fin 1) (Fin 1) Fv).det = p := by rw [hA, hPd]
  rw [hM, hdA]
  have hβ : hankeBeta v (std v) ((p * p) • (1 : Matrix (Fin 1) (Fin 1) Fv)) ≠ 0 := by
    have h := hankeBeta_std_smul v (φ := (1 : Matrix (Fin 1) (Fin 1) Fv)) Matrix.transpose_one h1d
      (c := p * p) (mul_ne_zero hp0 hp0)
    have hpos := hankeBeta_std_one_pos (v := v) (n := 1)
    intro h0; rw [h0, mul_zero] at h; linarith
  have hq1 : 1 < DVR.q 𝔬 := by
    have h0 := DVR.q_pos (R := 𝔬)
    have h1 : DVR.q 𝔬 ≠ 1 := by
      rw [NF.q_completion]; intro h; exact v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    omega
  have hnorm : ‖p‖ = ((DVR.q 𝔬 : ℝ) ^ 1)⁻¹ := core_norm_of_valued v (e := 1) (by simpa using hpv)
  have hqr : (1 : ℝ) < (DVR.q 𝔬 : ℝ) := by exact_mod_cast hq1
  have hr1 : ‖p‖ < 1 := by
    rw [hnorm, pow_one]; exact inv_lt_one_of_one_lt₀ hqr
  have hr0 : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  intro h
  set X := hankeBeta v (std v) ((p * p) • (1 : Matrix (Fin 1) (Fin 1) Fv))
  have h2 : (‖p‖ ^ (1 + 1) * ‖p‖ ^ (1 + 1)) * X = 1 * X := by rw [one_mul]; linarith
  have h3 := mul_right_cancel₀ hβ h2
  have h4 : ‖p‖ ^ (1 + 1) * ‖p‖ ^ (1 + 1) < 1 := by
    have : ‖p‖ ^ (1 + 1) < 1 := pow_lt_one₀ hr0.le hr1 (by norm_num)
    have h5 : 0 < ‖p‖ ^ (1 + 1) := pow_pos hr0 _
    nlinarith
  linarith

end Main
end Aux

/-- **The limit defining $\beta_v(\Lambda,\psi)$ exists and is attained** for every lattice $\Lambda = B\,\mathfrak o_v^n$ and every
symmetric nondegenerate $\psi$. -/
theorem gramRatio_eventually_eq (B : GL (Fin n) Fv) {ψ : Matrix (Fin n) (Fin n) Fv} (hψ : ψᵀ = ψ)
    (hdet : ψ.det ≠ 0) :
    ∀ᶠ i in atTop, gramRatio v (locAct v B (std v)) ψ i = 2 * hankeBeta v (locAct v B (std v)) ψ :=
  l22_gramRatio_eventually_eq B hψ hdet

/-- **Lemma 2.2, corrected** (Hanke thesis, p. 6; *erratum*: the printed exponent is $n+1$): for $A, B\in\mathrm{GL}_n(F_v)$ and
$\psi$ symmetric nondegenerate, $\beta_v(B\mathfrak o_v^n,{}^tA\psi A) = |\det A|_v^{-(n+1)}\,\beta_v(AB\mathfrak o_v^n,\psi)$. -/
@[kb "hanke2005crelle" "Lemma 2.2, p. 6 (corrected sign of the exponent)"]
theorem hankeBeta_congr (A B : GL (Fin n) Fv) {ψ : Matrix (Fin n) (Fin n) Fv} (hψ : ψᵀ = ψ) (hdet : ψ.det ≠ 0) :
    hankeBeta v (locAct v B (std v)) ((A : Matrix (Fin n) (Fin n) Fv)ᵀ * ψ * (A : Matrix (Fin n) (Fin n) Fv)) =
      ‖(A : Matrix (Fin n) (Fin n) Fv).det‖ ^ (-((n : ℤ) + 1)) * hankeBeta v (locAct v (A * B) (std v)) ψ :=
  l22_hankeBeta_congr A B hψ hdet

/-- **Lemma 2.2 as printed is false**: for $n = 1$, $\psi = 1$, $A = \varpi$ (a uniformizer), $\Lambda = \mathfrak o_v$,
$\beta_v(\Lambda,{}^tA\psi A)\ne|\det A|_v^{n+1}\beta_v(A\Lambda,\psi)$. -/
@[kb "hanke2005crelle" "Lemma 2.2, p. 6 (the printed exponent fails)"]
theorem lemma22_printed_false :
    ∃ (A : GL (Fin 1) Fv) (ψ : Matrix (Fin 1) (Fin 1) Fv), ψᵀ = ψ ∧ ψ.det ≠ 0 ∧
      hankeBeta v (std v) ((A : Matrix (Fin 1) (Fin 1) Fv)ᵀ * ψ * (A : Matrix (Fin 1) (Fin 1) Fv)) ≠
        ‖(A : Matrix (Fin 1) (Fin 1) Fv).det‖ ^ (1 + 1) * hankeBeta v (locAct v A (std v)) ψ :=
  l22_printed_false (v := v)

end QuadFormsKB.Hanke2005
