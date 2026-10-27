/-
# The orthogonal complement of a frame: anisotropy and the determinant criterion

**Layer:** number fields, linear algebra over $F$. $Q_0$ over $\mathcal O_F$ in $N$ variables, $H = H_{Q_0}$ its Hessian over
$F$ ($Q_0(x) = \tfrac12x^{\mathsf T}Hx$, $B(x,y) = x^{\mathsf T}Hy$ = `bH H x y`), $\Xi = (\xi_0,\dots,\xi_{r-1})$ a frame.

**Defines** `ComplAnisotropic Q₀ Ξ`: the orthogonal complement $W = \Xi^\perp = \{x : B(\xi_j, x) = 0\ \forall j\}$ is
anisotropic ($x\in W$, $Q_0(x) = 0\Rightarrow x = 0$).

**Proves**
* invariance: under a change of basis of the frame (`complAnisotropic_frameMul_iff`) and under $SO(V)(F)$, indeed under
  every isometry of $H$ (`complAnisotropic_mulVec_iff`); so the condition depends only on the $SO(V)(F)$-orbit of the frame;
* `complAnisotropic_complRat`: it passes to the complement $\xi_0^\perp$ of the first vector (the induction step of the frame
  coordinates); `complAnisotropic_zero_iff`: for the empty frame it is `AnisotropicF`;
* `exists_adaptedFrameT_cols`: an adapted frame $g = [X\mid C]$ whose first $r$ columns are $X$;
  `complAnisotropic_iff_of_adapted`: $W$ is anisotropic iff the complement form $Q'$ of $g$ is;
* **`complAnisotropic_iff`** (the criterion, $n' = N - r = 2$): $W$ is anisotropic iff
  $\delta = -\det H_{Q_0}\det H_{T_0}$ (`deltaForms`) is not a square in $F$, for every rational frame of $T_0$.
-/
import QuadFormsKB.Tamagawa.Indefinite.FrameTowerFrame
import QuadFormsKB.Tamagawa.Indefinite.FrameSiegelReduce
import QuadFormsKB.Tamagawa.FrameSiegelReg
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryReduce

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField IsDedekindDomain QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Frames

variable {F : Type} [Field F] [NumberField F]

/-- **The orthogonal complement of the frame $\Xi$ is anisotropic**: every $x\in F^N$ with $B(\xi_j, x) = 0$ for all $j$
and $Q_0(x) = 0$ is $0$. -/
def ComplAnisotropic {N r : ℕ} (Q₀ : QuadForm (𝓞 F) N) (Ξ : Fin r → Fin N → F) : Prop :=
  ∀ x : Fin N → F, (∀ j, bH (Q₀.map (algebraMap (𝓞 F) F)).hessian (Ξ j) x = 0) → qF Q₀ x = 0 → x = 0

private theorem dot_mulVec_left' {m k : ℕ} (A : Matrix (Fin m) (Fin k) F) (a : Fin k → F) (v : Fin m → F) :
    (A *ᵥ a) ⬝ᵥ v = a ⬝ᵥ (Aᵀ *ᵥ v) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]

private theorem bH_mulVec_mulVec {m k : ℕ} (H : Matrix (Fin m) (Fin m) F) (A : Matrix (Fin m) (Fin k) F)
    (a b : Fin k → F) : bH H (A *ᵥ a) (A *ᵥ b) = bH (Aᵀ * H * A) a b := by
  unfold bH
  rw [dot_mulVec_left', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

private theorem bH_frameMul_zero {N r s : ℕ} (H : Matrix (Fin N) (Fin N) F) (Ξ : Fin r → Fin N → F)
    (M : Matrix (Fin r) (Fin s) F) (x : Fin N → F) (h : ∀ l, bH H (Ξ l) x = 0) (j : Fin s) :
    bH H (frameMul Ξ M j) x = 0 := by
  have e : frameMul Ξ M j = ∑ l, M l j • Ξ l := by funext i; simp [frameMul]
  rw [e]
  unfold bH
  rw [sum_dotProduct]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [smul_dotProduct]
  have := h l
  unfold bH at this
  rw [this, smul_zero]

private theorem qF_mulVec_eq {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (γ : Matrix (Fin N) (Fin N) F)
    (hγ : γᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * γ = (Q₀.map (algebraMap (𝓞 F) F)).hessian)
    (y : Fin N → F) : qF Q₀ (γ *ᵥ y) = qF Q₀ y := by
  have h := bH_mulVec_mulVec (Q₀.map (algebraMap (𝓞 F) F)).hessian γ y y
  rw [hγ, ← qH_eq_bH, ← qH_eq_bH, qH_hessian, qH_hessian] at h
  exact mul_left_cancel₀ two_ne_zero h

/-- Invariance under an invertible change of basis of the frame ($\Xi M$ spans the same space). -/
theorem complAnisotropic_frameMul_iff {N r : ℕ} (Q₀ : QuadForm (𝓞 F) N) (Ξ : Fin r → Fin N → F)
    (M : Matrix (Fin r) (Fin r) F) (hM : IsUnit M.det) :
    ComplAnisotropic Q₀ (frameMul Ξ M) ↔ ComplAnisotropic Q₀ Ξ := by
  have hM' : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ hM
  constructor
  · intro h x hx hq
    exact h x (fun j => bH_frameMul_zero _ Ξ M x hx j) hq
  · intro h x hx hq
    refine h x (fun l => ?_) hq
    have := bH_frameMul_zero (Q₀.map (algebraMap (𝓞 F) F)).hessian (frameMul Ξ M) M⁻¹ x hx l
    rwa [frameMul_mul, hM', frameMul_one] at this

/-- Invariance under an isometry $\gamma$ of $H$ (e.g. $\gamma\in SO(V)(F)$). -/
theorem complAnisotropic_mulVec_iff {N r : ℕ} (Q₀ : QuadForm (𝓞 F) N) (Ξ : Fin r → Fin N → F)
    (γ : Matrix (Fin N) (Fin N) F) (hγ : γᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * γ =
      (Q₀.map (algebraMap (𝓞 F) F)).hessian) (hγu : IsUnit γ.det) :
    ComplAnisotropic Q₀ (fun j => γ *ᵥ Ξ j) ↔ ComplAnisotropic Q₀ Ξ := by
  have hinv : γ⁻¹ * γ = 1 := Matrix.nonsing_inv_mul _ hγu
  have hinv' : γ * γ⁻¹ = 1 := Matrix.mul_nonsing_inv _ hγu
  have hb : ∀ a b, bH (Q₀.map (algebraMap (𝓞 F) F)).hessian (γ *ᵥ a) (γ *ᵥ b) =
      bH (Q₀.map (algebraMap (𝓞 F) F)).hessian a b := fun a b => by
    rw [bH_mulVec_mulVec, hγ]
  have hinj : ∀ y, γ *ᵥ y = 0 → y = 0 := fun y hy => by
    have := congrArg (fun z => γ⁻¹ *ᵥ z) hy
    simpa [Matrix.mulVec_mulVec, hinv] using this
  constructor
  · intro h x hx hq
    refine hinj x (h (γ *ᵥ x) (fun j => ?_) ?_)
    · rw [hb]; exact hx j
    · rw [qF_mulVec_eq Q₀ γ hγ]; exact hq
  · intro h x hx hq
    have hxe : x = γ *ᵥ (γ⁻¹ *ᵥ x) := by rw [Matrix.mulVec_mulVec, hinv', one_mulVec]
    rw [hxe]
    have := h (γ⁻¹ *ᵥ x) (fun j => ?_) ?_
    · rw [this, mulVec_zero]
    · have := hx j
      rw [hxe, hb] at this
      exact this
    · rw [hxe, qF_mulVec_eq Q₀ γ hγ] at hq; exact hq

/-- For the empty frame the condition is the anisotropy of $Q_0$. -/
theorem complAnisotropic_zero_iff {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (Ξ : Fin 0 → Fin N → F) :
    ComplAnisotropic Q₀ Ξ ↔ AnisotropicF Q₀ := by
  constructor
  · intro h ξ hξ
    exact h ξ (fun j => j.elim0) hξ
  · intro h x _ hx
    exact h x hx

/-- **The induction step**: if $\Xi^\perp$ is anisotropic, so is the orthogonal complement of the remaining columns
inside $\xi_0^\perp$, in the coordinates of the sphere complement $Q'$. -/
theorem complAnisotropic_complRat {k r : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F} (S : AdelicSphereSetup Q₀ ρ)
    (Ξ : Fin (r + 1) → Fin (k + 1) → F) (hΞ0 : S.ξ.1 = Ξ 0)
    (hperp : ∀ j : Fin r, bH (Q₀.map (algebraMap (𝓞 F) F)).hessian S.ξ.1 (Ξ j.succ) = 0)
    (h : ComplAnisotropic Q₀ Ξ) : ComplAnisotropic S.C.Q' (fun j : Fin r => S.complRat (Ξ j.succ)) := by
  intro x' hx' hq
  have hsymm := witt_hessian_symm (Q₀.map (algebraMap (𝓞 F) F))
  have h0 : bH (Q₀.map (algebraMap (𝓞 F) F)).hessian (Ξ 0) (S.Gc *ᵥ x') = 0 := by
    rw [← hΞ0, bH_comm hsymm]
    unfold bH
    have e : S.Gcᵀ *ᵥ ((Q₀.map (algebraMap (𝓞 F) F)).hessian *ᵥ S.ξ.1) = 0 := by
      rw [Matrix.mulVec_mulVec]; exact S.Gc_hes_ξ
    rw [dot_mulVec_left', e, dotProduct_zero]
  have hj : ∀ j : Fin r, bH (Q₀.map (algebraMap (𝓞 F) F)).hessian (Ξ j.succ) (S.Gc *ᵥ x') = 0 := by
    intro j
    have e := S.Gc_mulVec_complRat (hperp j)
    rw [← e, bH_mulVec_mulVec, S.Gc_hes]
    exact hx' j
  have hq0 : qF Q₀ (S.Gc *ᵥ x') = 0 := by
    have h := bH_mulVec_mulVec (Q₀.map (algebraMap (𝓞 F) F)).hessian S.Gc x' x'
    rw [S.Gc_hes, ← qH_eq_bH, ← qH_eq_bH, qH_hessian, qH_hessian] at h
    have h2 : qF Q₀ (S.Gc *ᵥ x') = qF S.C.Q' x' := mul_left_cancel₀ two_ne_zero h
    rw [h2]; exact hq
  have hx0 := h (S.Gc *ᵥ x') (fun j => by
    refine Fin.cases ?_ (fun j => ?_) j
    · exact h0
    · exact hj j) hq0
  have := congrArg (fun z => S.Lc *ᵥ z) hx0
  simpa [Matrix.mulVec_mulVec, S.Lc_mul_Gc] using this

/-- **An adapted frame with prescribed first columns**: for $X$ with $Q\circ X = T$, $T$ nondegenerate, there is an
adapted frame $g$ ($Q\circ g = T\perp Q'$) whose first $r$ columns are those of $X$. -/
theorem exists_adaptedFrameT_cols {r n' : ℕ} (Q : QuadForm F (r + n')) (T : QuadForm F r) (hT : T.Nondegenerate)
    (X : Matrix (Fin (r + n')) (Fin r) F) (hX : Q.compMat X = T) :
    ∃ fr : AdaptedFrameT Q T, ∀ i a, fr.g.val i (Fin.castAdd n' a) = X i a := by
  classical
  set H := Q.hessian with hH
  have hHT : Xᵀ * H * X = T.hessian := by rw [← hX, QuadForm.hessian_compMat]
  have hdetT : T.hessian.det ≠ 0 := hT
  have hdetT' : IsUnit T.hessian.det := isUnit_iff_ne_zero.mpr hdetT
  let φ : (Fin (r + n') → F) →ₗ[F] (Fin r → F) :=
    { toFun := fun y => (Xᵀ * H) *ᵥ y
      map_add' := fun a b => Matrix.mulVec_add _ _ _
      map_smul' := fun c a => by simp [Matrix.mulVec_smul] }
  have hrange : LinearMap.range φ = ⊤ := by
    refine eq_top_iff.mpr fun c _ => ⟨X *ᵥ (T.hessian⁻¹ *ᵥ c), ?_⟩
    show (Xᵀ * H) *ᵥ (X *ᵥ (T.hessian⁻¹ *ᵥ c)) = c
    simp only [Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc, hHT, Matrix.mul_nonsing_inv _ hdetT', one_mulVec]
  set W := LinearMap.ker φ
  have hW : Module.finrank F W = n' := by
    have := LinearMap.finrank_range_add_finrank_ker φ
    rw [hrange] at this
    simp only [finrank_top, Module.finrank_fin_fun] at this
    change r + Module.finrank F W = r + n' at this
    omega
  let b := Module.finBasisOfFinrankEq F W hW
  let Bm : Matrix (Fin (r + n')) (Fin n') F := Matrix.of fun i k => (b k : Fin (r + n') → F) i
  have hBmW : ∀ y : Fin n' → F, Bm *ᵥ y ∈ W := by
    intro y
    have : Bm *ᵥ y = ∑ k, y k • (b k : Fin (r + n') → F) := by
      funext i; simp [Bm, mulVec, dotProduct, mul_comm]
    rw [this]
    exact W.sum_mem fun k _ => W.smul_mem _ (b k).2
  have hφB : ∀ y, (Xᵀ * H) *ᵥ (Bm *ᵥ y) = 0 := fun y => hBmW y
  have hφB' : ∀ y, Xᵀ *ᵥ (H *ᵥ (Bm *ᵥ y)) = 0 := fun y => by
    have := hφB y
    rwa [← Matrix.mulVec_mulVec] at this
  set Q'' := Q.compMat Bm
  obtain ⟨d₀, hd₀⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F))
    (Finset.univ.image fun p : Fin n' × Fin n' => Q''.coeff p.1 p.2)
  set d : 𝓞 F := (d₀ : 𝓞 F)
  have hd : d ≠ 0 := nonZeroDivisors.coe_ne_zero d₀
  have hdF : (d : F) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (𝓞 F) F)]
    exact fun h => hd (RingOfIntegers.coe_injective h)
  have hint : ∀ i j, ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = (d : F) ^ 2 * Q''.coeff i j := by
    intro i j
    obtain ⟨a, ha⟩ := hd₀ (Q''.coeff i j) (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
    refine ⟨d * a, ?_⟩
    rw [map_mul, ha, Algebra.smul_def, pow_two, ← mul_assoc]
  choose a ha using hint
  let Q'o : QuadForm (𝓞 F) n' := QuadForm.ofUpper a
  have hQ'o : Q'o.map (algebraMap (𝓞 F) F) = Q.compMat ((d : F) • Bm) := by
    refine QuadForm.ext_upper fun i j hij => ?_
    rw [QuadFormsKB.Tamagawa.compMat_smul_coeff]
    simp only [Q'o, QuadForm.map, QuadForm.ofUpper, Matrix.map_apply, Matrix.of_apply, if_pos hij]
    exact ha i j
  let G : Matrix (Fin (r + n')) (Fin (r + n')) F :=
    Matrix.of fun i j => (Fin.append (fun a => X i a) (fun k => (d : F) * Bm i k) : Fin (r + n') → F) j
  have hGv : ∀ x : Fin (r + n') → F, G *ᵥ x =
      X *ᵥ (fun a => x (Fin.castAdd n' a)) + ((d : F) • Bm) *ᵥ (fun k => x (Fin.natAdd r k)) := by
    intro x
    funext i
    simp only [G, mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      Pi.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hGinj : ∀ x, G *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [hGv] at hx
    set u : Fin r → F := fun a => x (Fin.castAdd n' a) with hu_def
    set w : Fin n' → F := fun k => x (Fin.natAdd r k) with hw_def
    have h1 := congrArg (fun y => (Xᵀ * H) *ᵥ y) hx
    have h2 : (Xᵀ * H) *ᵥ (X *ᵥ u) = T.hessian *ᵥ u := by rw [Matrix.mulVec_mulVec, hHT]
    have h3 : (Xᵀ * H) *ᵥ (((d : F) • Bm) *ᵥ w) = 0 := by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, hφB, smul_zero]
    simp only [Matrix.mulVec_add, Matrix.mulVec_zero] at h1
    rw [h2, h3, add_zero] at h1
    have hu : u = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdetT h1
    rw [hu, mulVec_zero, zero_add, Matrix.smul_mulVec] at hx
    have h4 : Bm *ᵥ w = 0 := (smul_eq_zero.mp hx).resolve_left hdF
    have h5 : ∑ k, w k • b k = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul, Submodule.coe_zero]
      rw [← h4]; funext i; simp [Bm, mulVec, dotProduct, mul_comm]
    have h6 := b.linearIndependent
    have h7 : ∀ k, w k = 0 := fun k => (Fintype.linearIndependent_iff.mp h6) _ h5 k
    funext i
    induction i using Fin.addCases with
    | left i => simpa [hu_def] using congrFun hu i
    | right k => simpa [hw_def] using h7 k
  have hdet : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hx0 (hGinj x hx)
  let g : GL (Fin (r + n')) F := Matrix.GeneralLinearGroup.mk'' G hdet
  refine ⟨⟨g, Q'o, ?_⟩, fun i a => ?_⟩
  swap
  · show G i (Fin.castAdd n' a) = X i a
    simp [G, Fin.append_left]
  refine QuadForm.eq_of_eval_eq fun x => ?_
  rw [QuadForm.eval_compMat, show g.val = G from rfl, hGv]
  refine Eq.trans ?_ (evalIn_blockForm F T (Q'o.map (algebraMap (𝓞 F) F)) x).symm
  set u : Fin r → F := fun a => x (Fin.castAdd n' a) with hu_def
  set w : Fin n' → F := fun k => x (Fin.natAdd r k) with hw_def
  have e1 : Q.eval (X *ᵥ u) = T.eval u := by rw [← QuadForm.eval_compMat, hX]
  have e2 : Q.eval (((d : F) • Bm) *ᵥ w) = (Q'o.map (algebraMap (𝓞 F) F)).eval w := by
    rw [← QuadForm.eval_compMat, ← hQ'o]
  have hdot : ∀ v : Fin (r + n') → F, (X *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Xᵀ *ᵥ v) := fun v => dot_mulVec_left' X u v
  have e4 : Xᵀ *ᵥ (H *ᵥ (((d : F) • Bm) *ᵥ w)) = 0 := by
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul, hφB', smul_zero]
  have e3 : (X *ᵥ u) ⬝ᵥ (H *ᵥ (((d : F) • Bm) *ᵥ w)) = 0 := by
    rw [hdot, e4, dotProduct_zero]
  have hp := QuadForm.eval_polar Q (X *ᵥ u) (((d : F) • Bm) *ᵥ w)
  rw [e3] at hp
  show Q.eval (X *ᵥ u + ((d : F) • Bm) *ᵥ w) = T.eval u + (Q'o.map (algebraMap (𝓞 F) F)).eval w
  linear_combination hp + e1 + e2

/-- **$\Xi^\perp$ is anisotropic iff the complement form of an adapted frame is**, when the first columns of the
adapted frame are $\Xi$. -/
theorem complAnisotropic_iff_of_adapted {r n' : ℕ} (Q₀ : QuadForm (𝓞 F) (r + n')) (T₀ : QuadForm (𝓞 F) r)
    (hT : T₀.Nondegenerate) (X : RatFrame Q₀ T₀)
    (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F)))
    (hcols : ∀ i a, fr.g.val i (Fin.castAdd n' a) = X.1 i a) :
    ComplAnisotropic Q₀ (cols X.1) ↔ AnisotropicF fr.Q' := by
  set H := (Q₀.map (algebraMap (𝓞 F) F)).hessian with hHdef
  set g := fr.g.val with hgdef
  have hdetT : (T₀.map (algebraMap (𝓞 F) F)).hessian.det ≠ 0 := witt_nd T₀ hT
  have hg : gᵀ * H * g = blockMat (T₀.map (algebraMap (𝓞 F) F)).hessian 0 0
      (fr.Q'.map (algebraMap (𝓞 F) F)).hessian := by
    rw [hHdef, hgdef, ← QuadForm.hessian_compMat, fr.compMat_eq, QuadFormsKB.Tamagawa.Frames.hessian_blockForm]
  have hgi : ∀ y, g *ᵥ y = 0 → y = 0 := fun y hy => by
    have := congrArg (fun z => (fr.g⁻¹ : GL (Fin (r + n')) F).val *ᵥ z) hy
    simpa [Matrix.mulVec_mulVec, hgdef] using this
  have hgs : ∀ x, g *ᵥ ((fr.g⁻¹ : GL (Fin (r + n')) F).val *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec]
    simp [hgdef]
  -- the perpendicularity condition in the coordinates `y`
  have hperp : ∀ y : Fin (r + n') → F, (∀ j, bH H (cols X.1 j) (g *ᵥ y) = 0) ↔
      (fun a => y (Fin.castAdd n' a)) = 0 := by
    intro y
    have hcol : ∀ j : Fin r, cols X.1 j = g *ᵥ (Pi.single (Fin.castAdd n' j) 1) := by
      intro j; funext i
      simp [cols, ← hcols i j, Matrix.mulVec_single]
    have hb : ∀ j : Fin r, bH H (cols X.1 j) (g *ᵥ y) =
        ((T₀.map (algebraMap (𝓞 F) F)).hessian *ᵥ fun a => y (Fin.castAdd n' a)) j := by
      intro j
      rw [hcol, bH_mulVec_mulVec, hg]
      unfold bH
      rw [single_dotProduct, one_mul]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, blockMat_castAdd_castAdd,
        blockMat_castAdd_natAdd, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    constructor
    · intro h
      refine Matrix.eq_zero_of_mulVec_eq_zero hdetT (funext fun j => ?_)
      rw [← hb]; exact h j
    · intro h j
      rw [hb, h, mulVec_zero]; rfl
  have hq : ∀ y : Fin (r + n') → F, (fun a => y (Fin.castAdd n' a)) = 0 →
      qF Q₀ (g *ᵥ y) = qF fr.Q' (fun k => y (Fin.natAdd r k)) := by
    intro y hu
    have h1 : qF Q₀ (g *ᵥ y) = ((Q₀.map (algebraMap (𝓞 F) F)).compMat g).eval y :=
      (QuadForm.eval_compMat _ _ _).symm
    rw [h1, hgdef, fr.compMat_eq]
    have := QuadFormsKB.Tamagawa.Frames.evalIn_blockForm F (T₀.map (algebraMap (𝓞 F) F))
      (fr.Q'.map (algebraMap (𝓞 F) F)) y
    refine Eq.trans this ?_
    rw [hu]
    have hz : (T₀.map (algebraMap (𝓞 F) F)).evalIn F (0 : Fin r → F) = 0 := by
      simp [QuadForm.evalIn]
    rw [hz, zero_add]
  constructor
  · intro h w hw
    have hu : (fun a => (Fin.append (0 : Fin r → F) w : Fin (r + n') → F) (Fin.castAdd n' a)) = 0 := by
      funext a; simp [Fin.append_left]
    have hw' : (fun k => (Fin.append (0 : Fin r → F) w : Fin (r + n') → F) (Fin.natAdd r k)) = w := by
      funext k; simp [Fin.append_right]
    have := h (g *ᵥ Fin.append (0 : Fin r → F) w) ((hperp _).mpr hu) (by rw [hq _ hu, hw']; exact hw)
    have h0 := hgi _ this
    funext k
    have h1 := congrFun h0 (Fin.natAdd r k)
    simpa [Fin.append_right] using h1
  · intro h x hx hqx
    set y := (fr.g⁻¹ : GL (Fin (r + n')) F).val *ᵥ x with hy
    have hxy : g *ᵥ y = x := hgs x
    rw [← hxy] at hx hqx ⊢
    have hu := (hperp y).mp hx
    have hw := h _ (by rw [← hq y hu]; exact hqx)
    have : y = 0 := by
      funext i
      induction i using Fin.addCases with
      | left i => simpa using congrFun hu i
      | right k => simpa using congrFun hw k
    rw [this, mulVec_zero]

/-- **A binary complement is anisotropic iff $\delta$ is not a square**: for an adapted frame with binary complement $Q'$,
$-\det H_{Q'} = \delta\,(\det g/\det H_{T_0})^2$ (`det_frame_forms`), and `anisotropicF_iff_not_isSquare`. -/
theorem anisotropicF_adapted_iff {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 2)) (T₀ : QuadForm (𝓞 F) r)
    (hT : T₀.Nondegenerate) (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F))) :
    AnisotropicF fr.Q' ↔ ¬ IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀)) := by
  have hdet := det_frame_forms Q₀ T₀ fr
  have ht : algebraMap (𝓞 F) F T₀.hessian.det ≠ 0 := by
    have := witt_nd T₀ hT
    unfold QuadForm.Nondegenerate at this
    rwa [Siegel.hessian_map_NF, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
  have hd : fr.g.val.det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).mp fr.g.isUnit
    exact this.ne_zero
  rw [anisotropicF_iff_not_isSquare]
  simp only [deltaForms, map_neg, map_mul]
  set A := algebraMap (𝓞 F) F Q₀.hessian.det
  set t := algebraMap (𝓞 F) F T₀.hessian.det
  set B := algebraMap (𝓞 F) F fr.Q'.hessian.det
  set d := fr.g.val.det
  refine not_congr ⟨fun ⟨s, hs⟩ => ⟨s * t / d, ?_⟩, fun ⟨s, hs⟩ => ⟨s * d / t, ?_⟩⟩
  · rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hd hd)]
    linear_combination (-t) * hdet + t ^ 2 * hs
  · rw [div_mul_div_comm, eq_div_iff (mul_ne_zero ht ht)]
    linear_combination t * hdet + d ^ 2 * hs

/-- **The criterion** ($n' = N - r = 2$): the orthogonal complement $W$ of a rational frame of $T_0$ is anisotropic iff
$\delta = -\det H_{Q_0}\det H_{T_0}$ is not a square in $F$. In particular the condition does not depend on the frame. -/
@[kb "omeara1963" "63:11 (binary spaces: anisotropic iff −det is not a square) [unverified]"]
theorem complAnisotropic_iff {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 2)) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate)
    (X : RatFrame Q₀ T₀) :
    ComplAnisotropic Q₀ (cols X.1) ↔ ¬ IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀)) := by
  obtain ⟨fr, hfr⟩ := exists_adaptedFrameT_cols _ _ (witt_nd T₀ hT) X.1 X.2
  rw [complAnisotropic_iff_of_adapted Q₀ T₀ hT X fr hfr, anisotropicF_adapted_iff Q₀ T₀ hT fr]

end QuadFormsKB.Tamagawa.Indefinite
