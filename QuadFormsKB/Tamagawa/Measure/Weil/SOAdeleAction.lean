import QuadFormsKB.Tamagawa.Measure.Weil.MuTamSO
import QuadFormsKB.Tamagawa.Measure.Weil.AdditiveAdele

/-!
# The action of $SO(V)(\mathbb A)$ on $V_{\mathbb A} = \mathbb A_F^n$

$F$ any number field, $Q_0$ a form over $\mathcal O_F$ in $n$ variables, `SOAdele Q₀` $= G_\infty\times SO(V)(\mathbb A_f)$.
This file defines the natural (matrix) action of $SO(V)(\mathbb A)$ on `AdeleSpace F (Fin n)` $=\mathbb A_F^n$:
* at a real place $w$: $(g\cdot y)_w = g_w\,y_w$ with $g_w\in SO(Q^{\sigma_w})(\mathbb R)$, $y_w\in\mathbb R^n$;
* at a complex place $w$: $(g\cdot y)_w = g_w\,y_w$ with $g_w\in SO(Q^{\tau_w})(\mathbb C)$;
* at a finite place $v$: $(g\cdot y)_v = g_v\,y_v$ with $g_v\in SO(V)(F_v)$; the result is a finite adele because
  $g_v\in SO(\mathfrak o_v^n)$ has integral entries for almost all $v$ (`entries_le_one_of_locAct`).

**Proves:** `instMulAction` (a `MulAction`), `smul_smul_adele` ($g$ is $\mathbb A_F$-linear, so it commutes with the
ideles), `diagSOAdele_smul_diagVec` ($\gamma\cdot\xi = \gamma\xi$ for $\gamma\in SO(V)(F)$, $\xi\in F^n$).
No topology is needed here: the measurability of the orbit maps used in the unfolding comes from the fibration data.
-/

open MeasureTheory Set Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)
local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### The local matrices of an adelic element -/

/-- The matrix of $g$ at a real place $w$. -/
def matR (g : SOAdele Q₀) (w : {w : InfinitePlace F // w.IsReal}) : Matrix (Fin n) (Fin n) ℝ :=
  (ArchSO.incl _ (g.1.1 w)).val

/-- The matrix of $g$ at a complex place $w$. -/
def matC (g : SOAdele Q₀) (w : {w : InfinitePlace F // w.IsComplex}) : Matrix (Fin n) (Fin n) ℂ :=
  (ArchSOC.incl _ (g.1.2 w)).val

/-- The matrix of $g$ at a finite place $v$. -/
def matV (g : SOAdele Q₀) (v : HeightOneSpectrum (𝓞 F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
  (((g.2 : OAf QF) v : orthGroup QF (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F)).val

theorem matR_mul (g h : SOAdele Q₀) (w) : matR Q₀ (g * h) w = matR Q₀ g w * matR Q₀ h w := by
  simp [matR, map_mul]

theorem matC_mul (g h : SOAdele Q₀) (w) : matC Q₀ (g * h) w = matC Q₀ g w * matC Q₀ h w := by
  simp [matC, map_mul]

theorem matV_mul (g h : SOAdele Q₀) (v) : matV Q₀ (g * h) v = matV Q₀ g v * matV Q₀ h v := by
  simp [matV]

@[simp] theorem matR_one (w) : matR Q₀ 1 w = 1 := by simp [matR]
@[simp] theorem matC_one (w) : matC Q₀ 1 w = 1 := by simp [matC]
@[simp] theorem matV_one (v) : matV Q₀ 1 v = 1 := by simp [matV]

/-- For almost all $v$ the finite component $g_v$ has entries in $\mathfrak o_v$. -/
theorem eventually_matV_integral (g : SOAdele Q₀) :
    ∀ᶠ v in Filter.cofinite, ∀ i j, matV Q₀ g v i j ∈ v.adicCompletionIntegers F := by
  filter_upwards [(g.2 : OAf QF).2] with v hv i j
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (entries_le_one_of_locAct v hv i j)

/-! ### The action -/

/-- The finite part of $g\cdot y$: $(g_v y_v)_v$, a finite adele vector. -/
def finSMul (g : SOAdele Q₀) (y : Fin n → AF) : Fin n → AF := fun i =>
  ⟨fun v => (matV Q₀ g v *ᵥ fun j => (y j) v) i, by
    have hy : ∀ᶠ v in Filter.cofinite, ∀ j, (y j) v ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.mpr fun j => (y j).2
    filter_upwards [eventually_matV_integral Q₀ g, hy] with v hg hyv
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hg i j) (hyv j)⟩

@[simp] theorem finSMul_apply (g : SOAdele Q₀) (y : Fin n → AF) (i : Fin n) (v : HeightOneSpectrum (𝓞 F)) :
    (finSMul Q₀ g y i) v = (matV Q₀ g v *ᵥ fun j => (y j) v) i := rfl

/-- **The action of $SO(V)(\mathbb A)$ on $\mathbb A_F^n$**, placewise by matrices. -/
def adeleSMul (g : SOAdele Q₀) (y : AdeleSpace F (Fin n)) : AdeleSpace F (Fin n) := fun i =>
  (((fun w => (matR Q₀ g w *ᵥ fun j => (y j).1.1 w) i),
    (fun w => (matC Q₀ g w *ᵥ fun j => (y j).1.2 w) i)),
   finSMul Q₀ g (fun j => (y j).2) i)

theorem adeleSMul_one (y : AdeleSpace F (Fin n)) : adeleSMul Q₀ 1 y = y := by
  funext i
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) ?_
  · simp [adeleSMul]
  · simp [adeleSMul]
  · apply Subtype.ext; funext v
    show (matV Q₀ 1 v *ᵥ fun j => (y j).2 v) i = (y i).2 v
    simp

theorem adeleSMul_mul (g h : SOAdele Q₀) (y : AdeleSpace F (Fin n)) :
    adeleSMul Q₀ (g * h) y = adeleSMul Q₀ g (adeleSMul Q₀ h y) := by
  funext i
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) ?_
  · simp only [adeleSMul, matR_mul, ← Matrix.mulVec_mulVec]
  · simp only [adeleSMul, matC_mul, ← Matrix.mulVec_mulVec]
  · apply Subtype.ext; funext v
    show (matV Q₀ (g * h) v *ᵥ fun j => (y j).2 v) i =
      (matV Q₀ g v *ᵥ fun j => (matV Q₀ h v *ᵥ fun k => (y k).2 v) j) i
    rw [matV_mul, ← Matrix.mulVec_mulVec]

instance instMulAction : MulAction (SOAdele Q₀) (AdeleSpace F (Fin n)) where
  smul := adeleSMul Q₀
  one_smul := adeleSMul_one Q₀
  mul_smul := adeleSMul_mul Q₀

theorem smul_def (g : SOAdele Q₀) (y : AdeleSpace F (Fin n)) : g • y = adeleSMul Q₀ g y := rfl

/-- **$g$ is $\mathbb A_F$-linear**: $g\cdot(a y) = a\,(g\cdot y)$ for $a\in\mathbb A_F$. -/
theorem smul_smul_adele (g : SOAdele Q₀) (a : Adeles F) (y : AdeleSpace F (Fin n)) :
    g • (a • y) = a • (g • y) := by
  funext i
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) ?_
  · show (matR Q₀ g w *ᵥ fun j => a.1.1 w * (y j).1.1 w) i = a.1.1 w * (matR Q₀ g w *ᵥ fun j => (y j).1.1 w) i
    rw [show (fun j => a.1.1 w * (y j).1.1 w) = a.1.1 w • (fun j => (y j).1.1 w) from rfl, Matrix.mulVec_smul]
    rfl
  · show (matC Q₀ g w *ᵥ fun j => a.1.2 w * (y j).1.2 w) i = a.1.2 w * (matC Q₀ g w *ᵥ fun j => (y j).1.2 w) i
    rw [show (fun j => a.1.2 w * (y j).1.2 w) = a.1.2 w • (fun j => (y j).1.2 w) from rfl, Matrix.mulVec_smul]
    rfl
  · apply Subtype.ext; funext v
    show (matV Q₀ g v *ᵥ fun j => a.2 v * (y j).2 v) i = a.2 v * (matV Q₀ g v *ᵥ fun j => (y j).2 v) i
    rw [show (fun j => a.2 v * (y j).2 v) = a.2 v • (fun j => (y j).2 v) from rfl, Matrix.mulVec_smul]
    rfl

/-- The ideles act on $\mathbb A_F^n$ by scalars, commuting with $SO(V)(\mathbb A)$. -/
theorem smul_units_comm (g : SOAdele Q₀) (z : (Adeles F)ˣ) (y : AdeleSpace F (Fin n)) :
    g • (z • y) = z • (g • y) :=
  smul_smul_adele Q₀ g (z : Adeles F) y

/-! ### Rational points -/

/-- **$\gamma\cdot\xi = \gamma\xi$ for $\gamma\in SO(V)(F)$, $\xi\in F^n$** (the diagonal embeddings are compatible
with the action). -/
theorem diagSOAdele_smul_diagVec (γ : soSub QF F) (ξ : Fin n → F) :
    diagSOAdele Q₀ γ • diagVec F (Fin n) ξ =
      diagVec F (Fin n) (((γ : orthGroup QF F) : GL (Fin n) F).val *ᵥ ξ) := by
  set M := ((γ : orthGroup QF F) : GL (Fin n) F).val
  funext i
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) ?_
  · show (matR Q₀ (diagSOAdele Q₀ γ) w *ᵥ fun j => (diag F (ξ j)).1.1 w) i = (diag F ((M *ᵥ ξ) i)).1.1 w
    have hm : matR Q₀ (diagSOAdele Q₀ γ) w = M.map (embedding_of_isReal w.2) := rfl
    rw [hm]; simp only [diag_fst]
    exact (RingHom.map_mulVec _ M ξ i).symm
  · show (matC Q₀ (diagSOAdele Q₀ γ) w *ᵥ fun j => (diag F (ξ j)).1.2 w) i = (diag F ((M *ᵥ ξ) i)).1.2 w
    have hm : matC Q₀ (diagSOAdele Q₀ γ) w = M.map w.1.embedding := rfl
    rw [hm]; simp only [diag_fst]
    exact (RingHom.map_mulVec _ M ξ i).symm
  · apply Subtype.ext; funext v
    show (matV Q₀ (diagSOAdele Q₀ γ) v *ᵥ fun j => (diag F (ξ j)).2 v) i = (diag F ((M *ᵥ ξ) i)).2 v
    have hm : matV Q₀ (diagSOAdele Q₀ γ) v = M.map (algebraMap F (v.adicCompletion F)) := rfl
    rw [hm]; simp only [diag_snd]
    exact (RingHom.map_mulVec _ M ξ i).symm

end QuadFormsKB.Tamagawa.Measure.Weil
