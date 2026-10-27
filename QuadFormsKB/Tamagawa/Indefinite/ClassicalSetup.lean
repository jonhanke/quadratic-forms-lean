/-
# The classical setting over a number field (Siegel's formula for indefinite forms)

**Layer:** number fields; the library's adelic groups (`MuTamSO.lean`, `AdelicSO.lean`, `SOAdeleAction.lean`).

Let $F$ be a number field, $Q_0$ a quadratic form over $\mathcal O_F$ in $n$ variables (any signature), $V = F^n$ with
$Q = Q_0\otimes F$, $L = \mathcal O_F^n$. This file sets up the objects to which the abstract theta unfolding
(`ThetaUnfold.lean`) is applied:
* `VInf F n` $= V_\infty = \prod_{w\ \mathrm{real}}\mathbb R^n\times\prod_{w\ \mathrm{complex}}\mathbb C^n$ with the action of
  $G_\infty$ = `GInfSO Q₀` placewise by matrices (`archSOCAction` is the complex analogue of `archSOAction`);
* the action of $SO(V)(\mathbb A_f)$ = `SOAf Q₀` on $\mathbb A_f^n$ (`finAction`), placewise;
* `archVec`, `finVec`: the archimedean and finite components of an adelic vector, equivariant
  (`archVec_smul`, `finVec_smul`); `ratA`, `ratF`: the embeddings of the rational sphere $T(m)(F) = \{Q = m\}$
  (`RatSphere`), equivariant for $SO(V)(F)$ (`ratA_smul`, `ratF_smul`);
* `latHat` $=\hat L = \prod_v\mathfrak o_v^n$;
* `DC Q₀`: the double cosets $SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)$ (the proper classes in the genus of $L$),
  with representatives `dcRep` (`dcRep_cov`, `dcRep_disj`).

All unconditional, standard axioms only.
-/
import QuadFormsKB.Tamagawa.Indefinite.ArchConj
import QuadFormsKB.Tamagawa.Indefinite.ArchProduct
import QuadFormsKB.Tamagawa.Measure.Weil.SphereOrbitsNF
import QuadFormsKB.Tamagawa.Measure.Weil.FundamentalDomain

open MeasureTheory Matrix MulAction Set NumberField IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
open QuadFormsKB.Tamagawa.Measure.LerayComplex

/-! ### $SO(Q)(\mathbb C)$ acting on $\mathbb C^n$ -/

section Complex

variable {n : ℕ}

/-- **The action of $SO(Q)(\mathbb C)$ on $\mathbb C^n$**: $g\cdot v = gv$. -/
instance archSOCAction (Q : QuadForm ℂ n) : MulAction (ArchSOC Q) (Fin n → ℂ) where
  smul g v := ArchSOC.mat Q g *ᵥ v
  one_smul v := by
    show ArchSOC.mat Q 1 *ᵥ v = v
    rw [show ArchSOC.mat Q 1 = 1 by simp [ArchSOC.mat], one_mulVec]
  mul_smul g h v := by
    show ArchSOC.mat Q (g * h) *ᵥ v = ArchSOC.mat Q g *ᵥ (ArchSOC.mat Q h *ᵥ v)
    rw [ArchSOC.mat_mul, mulVec_mulVec]

theorem archSOC_smul_def (Q : QuadForm ℂ n) (g : ArchSOC Q) (v : Fin n → ℂ) : g • v = ArchSOC.mat Q g *ᵥ v :=
  rfl

theorem continuous_archSOC_smul (Q : QuadForm ℂ n) :
    Continuous fun p : ArchSOC Q × (Fin n → ℂ) => p.1 • p.2 :=
  ((ArchSOC.continuous_mat Q).comp continuous_fst).matrix_mulVec continuous_snd

end Complex

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)
local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### $V_\infty$ and the action of $G_\infty$ -/

variable (F n) in
/-- **$V_\infty = \prod_{w\ \mathrm{real}}\mathbb R^n\times\prod_{w\ \mathrm{complex}}\mathbb C^n$**, on which
$G_\infty$ = `GInfSO Q₀` acts placewise. -/
abbrev VInf : Type := (∀ _w : {w : InfinitePlace F // w.IsReal}, Fin n → ℝ) ×
  (∀ _w : {w : InfinitePlace F // w.IsComplex}, Fin n → ℂ)

theorem continuous_GInf_smul : Continuous fun p : GInfSO Q₀ × VInf F n => p.1 • p.2 := by
  show Continuous fun p : GInfSO Q₀ × VInf F n => ((fun w => p.1.1 w • p.2.1 w), (fun w => p.1.2 w • p.2.2 w))
  refine Continuous.prodMk (continuous_pi fun w => ?_) (continuous_pi fun w => ?_)
  · have h1 : Continuous fun p : GInfSO Q₀ × VInf F n => (p.1.1 w, p.2.1 w) :=
      ((continuous_apply w).comp (continuous_fst.comp continuous_fst)).prodMk
        ((continuous_apply w).comp (continuous_fst.comp continuous_snd))
    exact (continuous_archSO_smul _).comp h1
  · have h1 : Continuous fun p : GInfSO Q₀ × VInf F n => (p.1.2 w, p.2.2 w) :=
      ((continuous_apply w).comp (continuous_snd.comp continuous_fst)).prodMk
        ((continuous_apply w).comp (continuous_snd.comp continuous_snd))
    exact (continuous_archSOC_smul _).comp h1

/-- $a\mapsto\Phi(a^{-1}y)$ is measurable on $G_\infty$ for measurable $\Phi$. -/
theorem measurable_GInf_inv_smul {Φ : VInf F n → ℝ≥0∞} (hΦ : Measurable Φ) (y : VInf F n) :
    Measurable fun a : GInfSO Q₀ => Φ (a⁻¹ • y) :=
  hΦ.comp ((continuous_GInf_smul Q₀).comp ((continuous_inv).prodMk continuous_const)).measurable

/-- The archimedean component of an adelic vector, regrouped by places. -/
def archVec (y : AdeleSpace F (Fin n)) : VInf F n := (fun w j => (y j).1.1 w, fun w j => (y j).1.2 w)

/-- The finite component of an adelic vector. -/
def finVec (y : AdeleSpace F (Fin n)) : Fin n → AF := fun j => (y j).2

theorem archVec_smul (g : SOAdele Q₀) (y : AdeleSpace F (Fin n)) : archVec (g • y) = g.1 • archVec y := rfl

/-! ### $SO(V)(\mathbb A_f)$ acting on $\mathbb A_f^n$ -/

/-- **The action of $SO(V)(\mathbb A_f)$ on $\mathbb A_f^n$**, placewise by matrices. -/
instance finAction : MulAction (SOAf Q₀) (Fin n → AF) where
  smul b z := finSMul Q₀ ((1 : GInfSO Q₀), b) z
  one_smul z := by
    funext i
    apply Subtype.ext; funext v
    show (matV Q₀ 1 v *ᵥ fun j => (z j) v) i = (z i) v
    simp
  mul_smul b b' z := by
    funext i
    apply Subtype.ext; funext v
    show (matV Q₀ (((1 : GInfSO Q₀), b) * ((1 : GInfSO Q₀), b')) v *ᵥ fun j => (z j) v) i =
      (matV Q₀ ((1 : GInfSO Q₀), b) v *ᵥ fun j => (matV Q₀ ((1 : GInfSO Q₀), b') v *ᵥ fun k => (z k) v) j) i
    rw [matV_mul, ← Matrix.mulVec_mulVec]

theorem fin_smul_def (b : SOAf Q₀) (z : Fin n → AF) : b • z = finSMul Q₀ ((1 : GInfSO Q₀), b) z := rfl

theorem finVec_smul (g : SOAdele Q₀) (y : AdeleSpace F (Fin n)) : finVec (g • y) = g.2 • finVec y := rfl

/-! ### The rational sphere in $V_\infty$ and in $\mathbb A_f^n$ -/

/-- The archimedean embedding $T(m)(F)\to V_\infty$, $\eta\mapsto(\sigma_w(\eta))_w$. -/
def ratA (m : F) (η : RatSphere Q₀ m) : VInf F n := archVec (diagVec F (Fin n) η.1)

/-- The finite embedding $T(m)(F)\to\mathbb A_f^n$ (diagonal). -/
def ratF (m : F) (η : RatSphere Q₀ m) : Fin n → AF := finVec (diagVec F (Fin n) η.1)

theorem ratA_smul {m : F} (γ : GammaSOAdele Q₀) (η : RatSphere Q₀ m) :
    ratA Q₀ m (γ • η) = (γ : SOAdele Q₀).1 • ratA Q₀ m η := by
  rw [ratA, ratA, diagVec_smul_ratSphere, archVec_smul]

theorem ratF_smul {m : F} (γ : GammaSOAdele Q₀) (η : RatSphere Q₀ m) :
    ratF Q₀ m (γ • η) = (γ : SOAdele Q₀).2 • ratF Q₀ m η := by
  rw [ratF, ratF, diagVec_smul_ratSphere, finVec_smul]

/-! ### $\hat L$ -/

variable (F n) in
/-- **$\hat L = \prod_v\mathfrak o_v^n\subseteq\mathbb A_f^n$**, the closure of $L = \mathcal O_F^n$. -/
def latHat : Set (Fin n → AF) := {z | ∀ j (v : HeightOneSpectrum (𝓞 F)), (z j) v ∈ v.adicCompletionIntegers F}

/-! ### Double cosets: the proper classes in the genus -/

/-- The relation $b\sim b'$ iff $b' = \gamma b k$ with $\gamma\in SO(V)(F)$, $k\in SO(\hat L)$. -/
def dcSetoid : Setoid (SOAf Q₀) where
  r b b' := ∃ γ ∈ GammaSOAdele Q₀, ∃ k ∈ KSO Q₀, b' = γ.2 * b * k
  iseqv := by
    refine ⟨fun b => ⟨1, (GammaSOAdele Q₀).one_mem, 1, (KSO Q₀).one_mem, by simp⟩, ?_, ?_⟩
    · rintro b b' ⟨γ, hγ, k, hk, rfl⟩
      refine ⟨γ⁻¹, (GammaSOAdele Q₀).inv_mem hγ, k⁻¹, (KSO Q₀).inv_mem hk, ?_⟩
      simp [mul_assoc]
    · rintro b b' b'' ⟨γ, hγ, k, hk, rfl⟩ ⟨γ', hγ', k', hk', rfl⟩
      refine ⟨γ' * γ, (GammaSOAdele Q₀).mul_mem hγ' hγ, k * k', (KSO Q₀).mul_mem hk hk', ?_⟩
      simp [mul_assoc]

/-- **The double cosets** $SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)$, i.e. the proper classes in the genus of
$L$ (`ClassSet.dosetEquivClassesInGenus` for $O$). -/
abbrev DC : Type := Quotient (dcSetoid Q₀)

/-- The double cosets are countable ($SO(V)(\mathbb A_f)/SO(\hat L)$ is countable, `countable_SOAf_quot`). -/
instance countable_DC : Countable (DC Q₀) := by
  have := countable_SOAf_quot Q₀
  let f : SOAf Q₀ ⧸ KSO Q₀ → DC Q₀ := Quotient.lift (fun b : SOAf Q₀ => (⟦b⟧ : DC Q₀)) fun b b' h =>
    Quotient.sound ⟨1, (GammaSOAdele Q₀).one_mem, b⁻¹ * b', QuotientGroup.leftRel_apply.mp h, by simp⟩
  refine Function.Surjective.countable (f := f) ?_
  rintro ⟨b⟩
  exact ⟨QuotientGroup.mk b, rfl⟩

/-- Representatives $\beta_i$ of the double cosets. -/
def dcRep (i : DC Q₀) : SOAf Q₀ := Quotient.out i

theorem dcRep_cov (g : SOAf Q₀) : ∃ i, ∃ γ ∈ GammaSOAdele Q₀, ∃ k ∈ KSO Q₀, g = γ.2 * dcRep Q₀ i * k :=
  ⟨⟦g⟧, Quotient.mk_out (s := dcSetoid Q₀) g⟩

theorem dcRep_disj (i j : DC Q₀) (γ : SOAdele Q₀) (hγ : γ ∈ GammaSOAdele Q₀) (k : SOAf Q₀) (hk : k ∈ KSO Q₀)
    (k' : SOAf Q₀) (hk' : k' ∈ KSO Q₀) (h : γ.2 * dcRep Q₀ i * k = dcRep Q₀ j * k') : i = j := by
  have hrel : (dcSetoid Q₀) (dcRep Q₀ i) (dcRep Q₀ j) :=
    ⟨γ, hγ, k * k'⁻¹, (KSO Q₀).mul_mem hk ((KSO Q₀).inv_mem hk'), by
      rw [← mul_assoc, h, mul_inv_cancel_right]⟩
  rw [← Quotient.out_eq i, ← Quotient.out_eq j]
  exact Quotient.sound hrel

end QuadFormsKB.Tamagawa.Indefinite
