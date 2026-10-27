/-
# Frame coordinates for an arbitrary rational frame

**Layer:** number fields, adeles. `FrameTower.lean` builds the frame coordinates of an orthogonal rational frame. A rational
frame $X$ of a nondegenerate $T_0$ ($Q_0\circ X = T_0$) becomes orthogonal after a change of basis $P$ of $F^r$
($T_0\circ P$ diagonal, `exists_diag_global`), and the frames of $T_0$ and of $T_0\circ P$ correspond by $Y\mapsto YP$, an
$SO(V)(\mathbb A)$-equivariant bijection. This file transports the coordinates along it.

* `frameMul Ξ M`, `frameMulA M Y`: the frame $\Xi M$ (columns $\sum_l M_{lj}\xi_l$), rationally and adelically;
* **`FrameTower.transport`**: a tower for $\Xi$ gives one for $\Xi M$, $M$ invertible (same complement, embedding, measure);
* **`nonempty_frameTower_ratFrame`**: every rational frame of a nondegenerate $T_0$ has frame coordinates ($n'\ge3$).
-/
import QuadFormsKB.Tamagawa.Indefinite.FrameTower
import QuadFormsKB.Tamagawa.Indefinite.FrameClassical
import QuadFormsKB.Tamagawa.FrameDiag

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F] {N r s : ℕ}

/-- The frame $\Xi M$: columns $\sum_l M_{lj}\,\xi_l$. -/
def frameMul (Ξ : Fin r → Fin N → F) (M : Matrix (Fin r) (Fin s) F) : Fin s → Fin N → F :=
  fun j i => ∑ l, M l j * Ξ l i

/-- The adelic frame $YM$: columns $\sum_l M_{lj}\,y_l$. -/
def frameMulA (M : Matrix (Fin r) (Fin s) F) (Y : Fin r → AdeleSpace F (Fin N)) : Fin s → AdeleSpace F (Fin N) :=
  fun j i => ∑ l, diag F (M l j) * Y l i

theorem finAdele_sum_apply {ι : Type*} (s : Finset ι) (f : ι → FiniteAdeleRing (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) : (∑ l ∈ s, f l) v = ∑ l ∈ s, f l v := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

theorem diag_one' : diag F 1 = 1 :=
  Prod.ext (by rw [diag_fst]; exact map_one (NumberField.mixedEmbedding F))
    (by rw [diag_snd]; exact map_one (algebraMap F (FiniteAdeleRing (𝓞 F) F)))

theorem diag_sum {ι : Type*} (s : Finset ι) (f : ι → F) : diag F (∑ l ∈ s, f l) = ∑ l ∈ s, diag F (f l) :=
  map_sum (diag F) f s

theorem mulVec_lin {R : Type*} [CommRing R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (c : Fin r → R)
    (y : Fin r → Fin m → R) (i : Fin m) :
    (A *ᵥ fun k => ∑ l, c l * y l k) i = ∑ l, c l * (A *ᵥ y l) i := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem frameMulA_frameA (Ξ : Fin r → Fin N → F) (M : Matrix (Fin r) (Fin s) F) :
    frameMulA M (frameA Ξ) = frameA (frameMul Ξ M) := by
  funext j i
  simp only [frameMulA, frameA, diagVec_apply, frameMul, diag_sum]
  exact Finset.sum_congr rfl fun l _ => (QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereSetup.diag_mul _ _).symm

/-- $SO(V)(\mathbb A)$ acts linearly: $g(YM) = (gY)M$. -/
theorem smul_frameMulA (Q₀ : QuadForm (𝓞 F) N) (g : SOAdele Q₀) (M : Matrix (Fin r) (Fin s) F)
    (Y : Fin r → AdeleSpace F (Fin N)) : g • frameMulA M Y = frameMulA M (g • Y) := by
  funext j i
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) ?_
  · show (matR Q₀ g w *ᵥ fun k => (frameMulA M Y j k).1.1 w) i = (frameMulA M (g • Y) j i).1.1 w
    simp only [frameMulA, Prod.fst_sum, Finset.sum_apply, Prod.fst_mul, Pi.mul_apply, diag_fst_fst]
    rw [mulVec_lin]
    exact Finset.sum_congr rfl fun l _ => rfl
  · show (matC Q₀ g w *ᵥ fun k => (frameMulA M Y j k).1.2 w) i = (frameMulA M (g • Y) j i).1.2 w
    simp only [frameMulA, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply,
      QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereSetup.diag_fst_snd]
    rw [mulVec_lin]
    exact Finset.sum_congr rfl fun l _ => rfl
  · apply Subtype.ext; funext v
    show (matV Q₀ g v *ᵥ fun k => (frameMulA M Y j k).2 v) i = (frameMulA M (g • Y) j i).2 v
    have : ∀ k, (∑ l, diag F (M l j) * Y l k).2 v = ∑ l, algebraMap F (v.adicCompletion F) (M l j) * (Y l k).2 v := by
      intro k
      rw [Prod.snd_sum, finAdele_sum_apply]
      exact Finset.sum_congr rfl fun l _ => rfl
    rw [show (fun k => (frameMulA M Y j k).2 v) =
      fun k => ∑ l, algebraMap F (v.adicCompletion F) (M l j) * (Y l k).2 v from funext this, mulVec_lin]
    simp only [frameMulA]
    rw [Prod.snd_sum, finAdele_sum_apply]
    exact Finset.sum_congr rfl fun l _ => rfl

theorem frameMulA_mul {t : ℕ} (M : Matrix (Fin r) (Fin s) F) (M' : Matrix (Fin s) (Fin t) F)
    (Y : Fin r → AdeleSpace F (Fin N)) : frameMulA M' (frameMulA M Y) = frameMulA (M * M') Y := by
  funext u i
  simp only [frameMulA, Matrix.mul_apply, diag_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereSetup.diag_mul]
  ring

theorem frameMulA_one (Y : Fin r → AdeleSpace F (Fin N)) : frameMulA (1 : Matrix (Fin r) (Fin r) F) Y = Y := by
  funext j i
  simp only [frameMulA, Matrix.one_apply]
  rw [Finset.sum_eq_single j]
  · simp [diag_one']
  · intro l _ hl; simp [hl]
  · simp

theorem frameMul_mul {t : ℕ} (Ξ : Fin r → Fin N → F) (M : Matrix (Fin r) (Fin s) F) (M' : Matrix (Fin s) (Fin t) F) :
    frameMul (frameMul Ξ M) M' = frameMul Ξ (M * M') := by
  funext u i
  simp only [frameMul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem frameMul_one (Ξ : Fin r → Fin N → F) : frameMul Ξ (1 : Matrix (Fin r) (Fin r) F) = Ξ := by
  funext j i
  simp only [frameMul, Matrix.one_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hl; simp [hl]
  · simp

/-- **Transport of a tower along an invertible change of basis of the frame.** -/
def FrameTower.transport {n' : ℕ} {Q₀ : QuadForm (𝓞 F) N} {hQ : Q₀.Nondegenerate} {Ξ : Fin r → Fin N → F}
    (D : FrameTower Q₀ hQ n' Ξ) (M : Matrix (Fin r) (Fin r) F) (hM : IsUnit M.det) :
    FrameTower Q₀ hQ n' (frameMul Ξ M) where
  Q'' := D.Q''
  hQ'' := D.hQ''
  ιInf := D.ιInf
  ιFin := D.ιFin
  measurable_ιInf := D.measurable_ιInf
  continuous_ιInf := D.continuous_ιInf
  T := D.T
  σ := D.σ
  τ := fun p => frameMulA M (D.τ p)
  C := (D.C.transport (frameMulA M) (fun g Y => (smul_frameMulA _ g M Y).symm)).congr rfl
    (frameMulA_frameA Ξ M)
  sFinite := D.sFinite
  fib := D.fib
  gamma_mem := D.gamma_mem
  stabΓ := fun γ hγ hfix => by
    refine D.stabΓ γ hγ ?_
    have e : frameA Ξ = frameMulA M⁻¹ (frameA (frameMul Ξ M)) := by
      rw [← frameMulA_frameA, frameMulA_mul, Matrix.mul_nonsing_inv _ hM, frameMulA_one]
    rw [e, smul_frameMulA, hfix]
  stab := fun g hfix => by
    refine D.stab g ?_
    have e : frameA Ξ = frameMulA M⁻¹ (frameA (frameMul Ξ M)) := by
      rw [← frameMulA_frameA, frameMulA_mul, Matrix.mul_nonsing_inv _ hM, frameMulA_one]
    rw [e, smul_frameMulA, hfix]
  Cm := D.Cm
  hCR := D.hCR
  hCC := D.hCC
  hCV := D.hCV
  hCH := D.hCH
  hΞC := fun j => by
    have e : frameMul Ξ M j = ∑ l, M l j • Ξ l := by
      funext i; simp [frameMul, Finset.sum_apply]
    rw [e, Matrix.mulVec_sum]
    exact Finset.sum_eq_zero fun l _ => by rw [Matrix.mulVec_smul, D.hΞC l, smul_zero]

theorem FrameTower.transport_Cm {n' : ℕ} {Q₀ : QuadForm (𝓞 F) N} {hQ : Q₀.Nondegenerate} {Ξ : Fin r → Fin N → F}
    (D : FrameTower Q₀ hQ n' Ξ) (M : Matrix (Fin r) (Fin r) F) (hM : IsUnit M.det) :
    (D.transport M hM).Cm = D.Cm ∧ (D.transport M hM).Q'' = D.Q'' :=
  ⟨rfl, rfl⟩

/-- **Every rational frame of a nondegenerate form has frame coordinates** ($n'\ge3$). -/
theorem nonempty_frameTower_ratFrame {n' : ℕ} (hn' : 3 ≤ n') (Q₀ : QuadForm (𝓞 F) (r + n'))
    (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (X : RatFrame Q₀ T₀) :
    Nonempty (FrameTower Q₀ hQ n' (cols X.1)) := by
  obtain ⟨P, dg, hP, hdg, hPd⟩ := QuadFormsKB.Tamagawa.Frames.exists_diag_global T₀ hT
  set f := algebraMap (𝓞 F) F with hf
  set PF : Matrix (Fin r) (Fin r) F := P.map f with hPF
  have hdet : IsUnit PF.det := by
    rw [isUnit_iff_ne_zero, hPF, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hP
  have hG : (Q₀.map f).compMat (X.1 * PF) = (QuadForm.diag dg).map f := by
    rw [← QuadFormsKB.QuadForm.compMat_mul, X.2, hPF, QuadFormsKB.QuadForm.map_compMat, hPd]
  have hcols : frameMul (cols X.1) PF = cols (X.1 * PF) := by
    funext j i
    simp only [frameMul, cols, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hdiag : ∀ i j, i ≠ j →
      bH (Q₀.map f).hessian (cols (X.1 * PF) i) (cols (X.1 * PF) j) = 0 := by
    intro i j hij
    have h1 := congrArg (fun G => QuadForm.hessian G i j) hG
    simp only [QuadFormsKB.QuadForm.hessian_compMat] at h1
    have h2 := QuadFormsKB.QuadForm.transpose_mul_mul_apply (Q₀.map f).hessian (X.1 * PF) i j
    unfold bH
    rw [show (cols (X.1 * PF) i) = fun l => (X.1 * PF) l i from rfl, show (cols (X.1 * PF) j) =
      fun l => (X.1 * PF) l j from rfl, ← h2, h1, QuadFormsKB.QuadForm.hessian_map]
    simp [QuadFormsKB.Tamagawa.Frames.hessian_diag, Matrix.diagonal_apply, hij]
  have hne : ∀ j, qF Q₀ (cols (X.1 * PF) j) ≠ 0 := by
    intro j
    have := QuadFormsKB.Tamagawa.Frames.eval_col_of_compMat (Q₀.map f) hG j
    show (Q₀.map f).eval (fun i => (X.1 * PF) i j) ≠ 0
    rw [this]
    simp only [QuadForm.map, QuadForm.diag, Matrix.map_apply]
    simp only [Matrix.diagonal_apply_eq]
    exact (map_ne_zero_iff f RingOfIntegers.coe_injective).mpr (hdg j)
  obtain ⟨D⟩ := nonempty_frameTower hn' r Q₀ hQ rfl (cols (X.1 * PF)) hdiag hne
  have hinv : IsUnit PF⁻¹.det := Matrix.isUnit_nonsing_inv_det _ hdet
  have e : frameMul (cols (X.1 * PF)) PF⁻¹ = cols X.1 := by
    rw [← hcols, frameMul_mul, Matrix.mul_nonsing_inv _ hdet, frameMul_one]
  exact ⟨e ▸ D.transport PF⁻¹ hinv⟩

end QuadFormsKB.Tamagawa.Indefinite
