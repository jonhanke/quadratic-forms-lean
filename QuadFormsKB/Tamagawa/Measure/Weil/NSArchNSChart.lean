import QuadFormsKB.Tamagawa.Measure.Weil.NSArchNSGroup
import QuadFormsKB.Tamagawa.Measure.Weil.NSArchDensity8

/-!
# The real chart of the test set at a real place with $E_w = \mathbb C$

**Layer:** $A, B, d$ real, $t\in\mathbb C$ with $t^2 = d$, $\operatorname{Re}t = 0$, $t\ne0$; $N$ = `normForm (A : ℂ) (B : ℂ)`;
$E_8 = (\mathbb R^2)^4 \cong \mathbb C^4$ (`E8`, `eC`).

* **`chartNS A B d t`**: $E_8\to E_8$, $w\mapsto e_{\mathbb C}\bigl((1 + w_{00} + i w_{01})\cdot
  X(\mathrm{gr}(u))\,c(z)\bigr)$ with $u_k = w_{k+1,1}$ (graph chart of $S$) and $z_k = w_{k+1,0}$ (Cayley chart of $S_1(\mathbb R)$)
  (indices 0-based).
* **`chartNS_image`**: $\mathrm{chart}(B^E_\delta) = e_{\mathbb C}(\mathrm{pol}_{\mathbb C}(R_\delta\times\mathrm{ysNS}_\delta))$.
* **`hasStrictFDerivAt_chartNS`**: strict derivative `LNS` at $0$,
  $L(w)_0 = w_0$, $L(w)_i = (w_{i0}, \tfrac{\operatorname{Im}t}{2}w_{i1})$ ($i\ge1$).
* **`det_LNS`**: $|\det L| = \|t\|^3/8$.
-/

open MeasureTheory Measure Set Filter Topology Metric Matrix Complex
open scoped ENNReal NNReal Quaternion ComplexConjugate

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Siegel QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex
  SphereLeray SphereLerayC QuadFormsKB.Tamagawa.Measure.Leray QuadFormsKB.Tamagawa.Measure.OrbitalReal

variable {A B d : ℝ} {t : ℂ} (ht : t ^ 2 = (d : ℂ)) (htre : t.re = 0) (ht0 : t ≠ 0)

/-- **The real chart of the test set**: $\beta = 1 + w_{00} + i w_{01}$, $u_k = w_{k+1,1}$ enters the graph chart,
$z_k = w_{k+1,0}$ the Cayley chart. -/
def chartNS (A B d : ℝ) (t : ℂ) (w : E8) : E8 :=
  eC ((1 + ((w 0 0 : ℂ) + (w 0 1 : ℂ) * Complex.I)) •
    qVec (cayX (A := A) (B := B) t (gr A B d (fun k => w k.succ 1)) *
      qC (vecQ (cay A B (fun k => w k.succ 0)))))

theorem mem_ball_E8 {δ : ℝ} (hδ : 0 < δ) (w : E8) : w ∈ ball (0 : E8) δ ↔ ∀ i j, |w i j| < δ := by
  simp only [mem_ball_zero_iff, pi_norm_lt_iff hδ, Real.norm_eq_abs]

theorem mem_ball_R3 {δ : ℝ} (hδ : 0 < δ) (u : Fin 3 → ℝ) : u ∈ ball (0 : Fin 3 → ℝ) δ ↔ ∀ k, |u k| < δ := by
  simp only [mem_ball_zero_iff, pi_norm_lt_iff hδ, Real.norm_eq_abs]

theorem val_sNS0_mul_realS {y : Sph (nsFormR A B d) 1} (hy : 0 < (y : Fin 4 → ℝ) 0) (h : Sph (normForm A B) 1) :
    ((sNS0 ht y * realS h : SphC (normForm (A : ℂ) (B : ℂ)) 1) : Fin 4 → ℂ) =
      qVec (cayX (A := A) (B := B) t (y : Fin 4 → ℝ) * qC (vecQ (h : Fin 4 → ℝ))) := by
  rw [sphC_mul_val, sNS0_of_pos ht (show 0 < 1 + (y : Fin 4 → ℝ) 0 by linarith), vecQ_sNS ht, vecQ_realS]

/-- **The chart maps the cube onto the (real chart of the) test set.** -/
theorem chartNS_image {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ min (min (radG A B d) (radR A B)) (1 / 2)) :
    chartNS A B d t '' ball 0 δ =
      eC '' (polC (normForm (A : ℂ) (B : ℂ)) 1 '' (rsq δ ×ˢ ysNS ht δ)) := by
  have hG : δ ≤ radG A B d := (hδ'.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hR : δ ≤ radR A B := (hδ'.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hh : δ ≤ 1 / 2 := hδ'.trans (min_le_right _ _)
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_ball_E8 hδ] at hw
    have hu : (fun k => w k.succ 1) ∈ ball (0 : Fin 3 → ℝ) δ := (mem_ball_R3 hδ _).2 fun k => hw _ _
    have hz : (fun k => w k.succ 0) ∈ ball (0 : Fin 3 → ℝ) δ := (mem_ball_R3 hδ _).2 fun k => hw _ _
    set y : Sph (nsFormR A B d) 1 := ⟨gr A B d (fun k => w k.succ 1), eval_gr
      (lt_of_lt_of_le (mem_ball_zero_iff.1 hu) hG)⟩ with hy_def
    have hy : y ∈ grBall A B d δ := (mem_grBall_iff hG y).2 ⟨_, hu, rfl⟩
    set h : Sph (normForm A B) 1 := ⟨cay A B (fun k => w k.succ 0), eval_cay
      (lt_of_lt_of_le (mem_ball_zero_iff.1 hz) hR)⟩ with hh_def
    have hh' : h ∈ cayBall A B δ := (mem_cayBall_iff hR h).2 ⟨_, hz, rfl⟩
    have hre : (1 + ((w 0 0 : ℂ) + (w 0 1 : ℂ) * Complex.I)).re = 1 + w 0 0 := by simp
    have him : (1 + ((w 0 0 : ℂ) + (w 0 1 : ℂ) * Complex.I)).im = w 0 1 := by simp
    have h00 := hw 0 0
    have h01 := hw 0 1
    have hβ0 : (1 + ((w 0 0 : ℂ) + (w 0 1 : ℂ) * Complex.I)) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      rw [hre] at this
      simp at this
      have := (abs_lt.1 h00).1
      linarith
    refine ⟨polC (normForm (A : ℂ) (B : ℂ)) 1 (Units.mk0 _ hβ0, sNS0 ht y * realS h),
      ⟨(Units.mk0 _ hβ0, sNS0 ht y * realS h), ⟨?_, ⟨(y, h), ⟨hy, hh'⟩, rfl⟩⟩, rfl⟩, ?_⟩
    · show |(1 + ((w 0 0 : ℂ) + (w 0 1 : ℂ) * Complex.I)).re - 1| < δ ∧ |(1 + ((w 0 0 : ℂ) + (w 0 1 : ℂ) * Complex.I)).im| < δ
      rw [hre, him]
      exact ⟨by simpa using h00, h01⟩
    · show eC ((1 + ((w 0 0 : ℂ) + (w 0 1 : ℂ) * Complex.I)) • ((sNS0 ht y * realS h : SphC (normForm (A : ℂ) (B : ℂ)) 1) :
        Fin 4 → ℂ)) = _
      rw [val_sNS0_mul_realS ht hy.1]
      rfl
  · rintro ⟨_, ⟨⟨β, x⟩, ⟨hβ, hx⟩, rfl⟩, rfl⟩
    obtain ⟨⟨y, h⟩, ⟨hy, hh'⟩, rfl⟩ := hx
    obtain ⟨u, hu, hyu⟩ := (mem_grBall_iff hG y).1 hy
    obtain ⟨z, hz, hhz⟩ := (mem_cayBall_iff hR h).1 hh'
    rw [mem_ball_R3 hδ] at hu hz
    refine ⟨Fin.cons ![(β : ℂ).re - 1, (β : ℂ).im] (fun k => ![z k, u k]), ?_, ?_⟩
    · rw [mem_ball_E8 hδ]
      intro i j
      refine Fin.cases ?_ (fun k => ?_) i
      · fin_cases j
        · simpa using hβ.1
        · simpa using hβ.2
      · fin_cases j
        · simpa using hz k
        · simpa using hu k
    · have hy0 : 0 < (y : Fin 4 → ℝ) 0 := hy.1
      show chartNS A B d t _ = eC ((β : ℂ) • ((sNS0 ht y * realS h : SphC (normForm (A : ℂ) (B : ℂ)) 1) :
        Fin 4 → ℂ))
      rw [val_sNS0_mul_realS ht hy0, chartNS]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have e1 : (1 + (((((β : ℂ).re - 1 : ℝ) : ℂ)) + (((β : ℂ).im : ℝ) : ℂ) * Complex.I)) = (β : ℂ) := by
        apply Complex.ext <;> simp
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e1, hyu, hhz]

/-! ### Smoothness and derivatives: algebraic preliminaries -/

theorem qVec_mul_vecQ (a b : ℂ) (x y : Fin 4 → ℂ) :
    qVec (vecQ x * vecQ y : ℍ[ℂ,a,b]) = ![x 0 * y 0 + a * x 1 * y 1 + b * x 2 * y 2 - a * b * x 3 * y 3,
      x 0 * y 1 + x 1 * y 0 - b * x 2 * y 3 + b * x 3 * y 2,
      x 0 * y 2 + a * x 1 * y 3 + x 2 * y 0 - a * x 3 * y 1,
      x 0 * y 3 + x 1 * y 2 - x 2 * y 1 + x 3 * y 0] := by
  funext i
  fin_cases i <;> simp [qVec, vecQ]

theorem contDiffAt_qmul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : ℂ) {f g : E → Fin 4 → ℂ} {x : E}
    (hf : ContDiffAt ℝ ⊤ f x) (hg : ContDiffAt ℝ ⊤ g x) :
    ContDiffAt ℝ ⊤ (fun w => qVec (vecQ (f w) * vecQ (g w) : ℍ[ℂ,a,b])) x := by
  simp only [qVec_mul_vecQ]
  have f0 := contDiffAt_pi.1 hf 0
  have f1 := contDiffAt_pi.1 hf 1
  have f2 := contDiffAt_pi.1 hf 2
  have f3 := contDiffAt_pi.1 hf 3
  have g0 := contDiffAt_pi.1 hg 0
  have g1 := contDiffAt_pi.1 hg 1
  have g2 := contDiffAt_pi.1 hg 2
  have g3 := contDiffAt_pi.1 hg 3
  rw [contDiffAt_pi]
  intro i
  fin_cases i <;> simp <;> fun_prop

theorem hasDerivAt_qmul (a b : ℂ) {f g : ℝ → Fin 4 → ℂ} {f' g' : Fin 4 → ℂ} (hf : HasDerivAt f f' 0)
    (hg : HasDerivAt g g' 0) (hf0 : f 0 = ![1, 0, 0, 0]) (hg0 : g 0 = ![1, 0, 0, 0]) :
    HasDerivAt (fun s => qVec (vecQ (f s) * vecQ (g s) : ℍ[ℂ,a,b])) (f' + g') 0 := by
  simp only [qVec_mul_vecQ]
  have f0 := hasDerivAt_pi.1 hf 0
  have f1 := hasDerivAt_pi.1 hf 1
  have f2 := hasDerivAt_pi.1 hf 2
  have f3 := hasDerivAt_pi.1 hf 3
  have g0 := hasDerivAt_pi.1 hg 0
  have g1 := hasDerivAt_pi.1 hg 1
  have g2 := hasDerivAt_pi.1 hg 2
  have g3 := hasDerivAt_pi.1 hg 3
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · refine HasDerivAt.congr_deriv ((((f0.mul g0).add ((f1.const_mul a).mul g1)).add ((f2.const_mul b).mul g2)).sub
      ((f3.const_mul (a * b)).mul g3)) ?_
    simp [hf0, hg0]
  · refine HasDerivAt.congr_deriv ((((f0.mul g1).add (f1.mul g0)).sub ((f2.const_mul b).mul g3)).add ((f3.const_mul b).mul g2)) ?_
    simp [hf0, hg0]
    ring
  · refine HasDerivAt.congr_deriv ((((f0.mul g2).add ((f1.const_mul a).mul g3)).add (f2.mul g0)).sub ((f3.const_mul a).mul g1)) ?_
    simp [hf0, hg0]
    ring
  · refine HasDerivAt.congr_deriv ((((f0.mul g3).add (f1.mul g2)).sub (f2.mul g1)).add (f3.mul g0)) ?_
    simp [hf0, hg0]
    ring

/-- The radial factor $(2(1+y_0))^{-1/2}$ of the Cayley point. -/
def cc (y0 : ℝ) : ℝ := (2 * (1 + y0)) ^ (-(1 / 2 : ℝ))

theorem qVec_cayX (y : Fin 4 → ℝ) :
    qVec (cayX (A := A) (B := B) t y) = ![(cc (y 0) : ℂ) * (1 + (y 0 : ℂ)), (cc (y 0) : ℂ) * (t * (y 1 : ℂ)),
      (cc (y 0) : ℂ) * (t * (y 2 : ℂ)), (cc (y 0) : ℂ) * (t * (y 3 : ℂ))] := by
  funext i
  fin_cases i <;> simp [qVec, cayX, yQ, vecQ, tMatN_mulVec, cc] <;> ring

theorem qVec_gr_cayX (u : Fin 3 → ℝ) :
    qVec (cayX (A := A) (B := B) t (gr A B d u)) =
      ![(cc (Real.sqrt (1 - qPD A B d u)) : ℂ) * (1 + (Real.sqrt (1 - qPD A B d u) : ℂ)),
        (cc (Real.sqrt (1 - qPD A B d u)) : ℂ) * (t * (u 0 : ℂ)),
        (cc (Real.sqrt (1 - qPD A B d u)) : ℂ) * (t * (u 1 : ℂ)),
        (cc (Real.sqrt (1 - qPD A B d u)) : ℂ) * (t * (u 2 : ℂ))] := by
  rw [qVec_cayX]
  rfl

/-- The radial factor $(1 + q(z))^{-1/2}$ of the Cayley point. -/
def rr (A B : ℝ) (z : Fin 3 → ℝ) : ℝ := (1 + qPure A B z) ^ (-(1 / 2 : ℝ))

theorem qVec_qC_cay (z : Fin 3 → ℝ) :
    qVec (qC (vecQ (cay A B z) : ℍ[ℝ,A,B])) =
      ![(rr A B z : ℂ), (rr A B z * z 0 : ℝ), (rr A B z * z 1 : ℝ), (rr A B z * z 2 : ℝ)] := by
  rw [qVec_qC, qVec_vecQ]
  funext i
  fin_cases i <;> simp [cay, rr] <;> first | rfl | (left; rfl)

theorem qPD_smul (s : ℝ) (u : Fin 3 → ℝ) : qPD A B d (s • u) = s ^ 2 * qPD A B d u := by
  simp only [qPD, Pi.smul_apply, smul_eq_mul]; ring

/-- The first factor $X(\mathrm{gr}(u))$ as a vector. -/
def fU (A B d : ℝ) (t : ℂ) (u : Fin 3 → ℝ) : Fin 4 → ℂ := qVec (cayX (A := A) (B := B) t (gr A B d u))

/-- The second factor $c(z)$ as a vector. -/
def gZ (A B : ℝ) (z : Fin 3 → ℝ) : Fin 4 → ℂ := qVec (qC (vecQ (cay A B z) : ℍ[ℝ,A,B]))

/-- The radial parameter $\beta = 1 + w_{00} + i w_{01}$. -/
def betaW (w : E8) : ℂ := 1 + ((w 0 0 : ℂ) + (w 0 1 : ℂ) * Complex.I)

theorem chartNS_eq (w : E8) :
    chartNS A B d t w = eC (betaW w • qVec (vecQ (fU A B d t (fun k => w k.succ 1)) *
      vecQ (gZ A B (fun k => w k.succ 0)) : ℍ[ℂ, (A : ℂ), (B : ℂ)])) := by
  simp only [chartNS, fU, gZ, vecQ_qVec, betaW]

theorem contDiffAt_eC {F : E8 → Fin 4 → ℂ} {x : E8} (hF : ContDiffAt ℝ ⊤ F x) :
    ContDiffAt ℝ ⊤ (fun w => eC (F w)) x := by
  rw [contDiffAt_pi]; intro i; rw [contDiffAt_pi]; intro j
  have hi := contDiffAt_pi.1 hF i
  fin_cases j
  · exact Complex.reCLM.contDiff.contDiffAt.comp x hi
  · exact Complex.imCLM.contDiff.contDiffAt.comp x hi

theorem contDiffAt_ofReal' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ ⊤ f x) : ContDiffAt ℝ ⊤ (fun w => (f w : ℂ)) x :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp x hf

theorem contDiffAt_s0 : ContDiffAt ℝ ⊤
    (fun w : E8 => Real.sqrt (1 - qPD A B d (fun k => w k.succ 1))) 0 := by
  have hq : ContDiffAt ℝ ⊤ (fun w : E8 => 1 - qPD A B d (fun k => w k.succ 1)) 0 := by
    simp only [qPD]; fun_prop
  exact hq.sqrt (by simp [qPD])

theorem contDiffAt_cs : ContDiffAt ℝ ⊤
    (fun w : E8 => cc (Real.sqrt (1 - qPD A B d (fun k => w k.succ 1)))) 0 := by
  have h : ContDiffAt ℝ ⊤ (fun w : E8 => 2 * (1 + Real.sqrt (1 - qPD A B d (fun k => w k.succ 1)))) 0 :=
    contDiffAt_const.mul (contDiffAt_const.add contDiffAt_s0)
  exact h.rpow_const_of_ne (by simp [qPD])

theorem contDiffAt_rr : ContDiffAt ℝ ⊤ (fun w : E8 => rr A B (fun k => w k.succ 0)) 0 := by
  have hq : ContDiffAt ℝ ⊤ (fun w : E8 => 1 + qPure A B (fun k => w k.succ 0)) 0 := by
    simp only [qPure]; fun_prop
  exact hq.rpow_const_of_ne (by simp [qPure])

theorem contDiffAt_fU : ContDiffAt ℝ ⊤ (fun w : E8 => fU A B d t (fun k => w k.succ 1)) 0 := by
  have hs := contDiffAt_ofReal' (contDiffAt_s0 (A := A) (B := B) (d := d))
  have hc := contDiffAt_ofReal' (contDiffAt_cs (A := A) (B := B) (d := d))
  have h0 : ContDiffAt ℝ ⊤ (fun w : E8 => ((w 1 1 : ℝ) : ℂ)) 0 := contDiffAt_ofReal' (by fun_prop)
  have h1 : ContDiffAt ℝ ⊤ (fun w : E8 => ((w 2 1 : ℝ) : ℂ)) 0 := contDiffAt_ofReal' (by fun_prop)
  have h2 : ContDiffAt ℝ ⊤ (fun w : E8 => ((w 3 1 : ℝ) : ℂ)) 0 := contDiffAt_ofReal' (by fun_prop)
  simp only [fU, qVec_gr_cayX]
  rw [contDiffAt_pi]
  intro i
  fin_cases i <;> simp <;> fun_prop

theorem contDiffAt_gZ : ContDiffAt ℝ ⊤ (fun w : E8 => gZ A B (fun k => w k.succ 0)) 0 := by
  have hr := contDiffAt_ofReal' (contDiffAt_rr (A := A) (B := B))
  have hrr := contDiffAt_rr (A := A) (B := B)
  have h0 : ContDiffAt ℝ ⊤ (fun w : E8 => (w 1 0 : ℝ)) 0 := by fun_prop
  have h1 : ContDiffAt ℝ ⊤ (fun w : E8 => (w 2 0 : ℝ)) 0 := by fun_prop
  have h2 : ContDiffAt ℝ ⊤ (fun w : E8 => (w 3 0 : ℝ)) 0 := by fun_prop
  simp only [gZ, qVec_qC_cay]
  rw [contDiffAt_pi]
  intro i
  fin_cases i <;> simp
  · exact hr
  · exact hr.mul (contDiffAt_ofReal' h0)
  · exact hr.mul (contDiffAt_ofReal' h1)
  · exact hr.mul (contDiffAt_ofReal' h2)

theorem contDiffAt_chartNS : ContDiffAt ℝ ⊤ (chartNS A B d t) 0 := by
  have e : chartNS A B d t = fun w => eC (betaW w • qVec (vecQ (fU A B d t (fun k => w k.succ 1)) *
      vecQ (gZ A B (fun k => w k.succ 0)) : ℍ[ℂ, (A : ℂ), (B : ℂ)])) := funext chartNS_eq
  rw [e]
  refine contDiffAt_eC ?_
  have hb : ContDiffAt ℝ ⊤ betaW (0 : E8) := by
    unfold betaW
    have a0 : ContDiffAt ℝ ⊤ (fun w : E8 => ((w 0 0 : ℝ) : ℂ)) 0 := contDiffAt_ofReal' (by fun_prop)
    have a1 : ContDiffAt ℝ ⊤ (fun w : E8 => ((w 0 1 : ℝ) : ℂ)) 0 := contDiffAt_ofReal' (by fun_prop)
    fun_prop
  exact hb.smul (contDiffAt_qmul _ _ contDiffAt_fU contDiffAt_gZ)

theorem cc_one : cc 1 = 1 / 2 := by
  rw [cc, show (2 * (1 + 1 : ℝ)) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

@[simp] theorem qPD_zero : qPD A B d (0 : Fin 3 → ℝ) = 0 := by simp [qPD]

@[simp] theorem qPure_zero : qPure A B (0 : Fin 3 → ℝ) = 0 := by simp [qPure]

theorem hasDerivAt_sline (u : Fin 3 → ℝ) :
    HasDerivAt (fun s : ℝ => Real.sqrt (1 - qPD A B d (s • u))) 0 0 := by
  have hq : HasDerivAt (fun s : ℝ => 1 - qPD A B d (s • u)) 0 0 := by
    have e : (fun s : ℝ => 1 - qPD A B d (s • u)) = fun s => 1 - s ^ 2 * qPD A B d u := by
      funext s; rw [qPD_smul]
    rw [e]
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (qPD A B d u)).const_sub 1
  have h := hq.sqrt (by simp)
  simpa using h

theorem hasDerivAt_cline (u : Fin 3 → ℝ) :
    HasDerivAt (fun s : ℝ => cc (Real.sqrt (1 - qPD A B d (s • u)))) 0 0 := by
  have h := ((hasDerivAt_sline (A := A) (B := B) (d := d) u).const_add 1).const_mul 2
  have h2 := h.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl (by simp))
  exact h2.congr_deriv (by simp)

theorem hasDerivAt_rline (z : Fin 3 → ℝ) : HasDerivAt (fun s : ℝ => rr A B (s • z)) 0 0 := by
  have hq : HasDerivAt (fun s : ℝ => 1 + qPure A B (s • z)) 0 0 := by
    have e : (fun s : ℝ => 1 + qPure A B (s • z)) = fun s => 1 + s ^ 2 * qPure A B z := by
      funext s; rw [qPure_smul]
    rw [e]
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (qPure A B z)).const_add 1
  have h := hq.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl (by simp [qPure]))
  unfold rr
  simpa using h

/-! ### The derivative at $0$ -/

/-- The block matrix of `LNS` on the $i$-th coordinate pair: $1$ for $i=0$, $\mathrm{diag}(1,\operatorname{Im}t/2)$ otherwise. -/
def DNS (t : ℂ) (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℝ :=
  if i = 0 then 1 else Matrix.diagonal ![1, t.im / 2]

/-- **The derivative of the chart at $0$**: $L(w)_0 = w_0$, $L(w)_i = (w_{i0}, \tfrac{\operatorname{Im}t}{2}w_{i1})$ for $i\ge1$. -/
def LNS (t : ℂ) : E8 →L[ℝ] E8 :=
  ContinuousLinearMap.pi fun i => (LinearMap.toContinuousLinearMap (Matrix.toLin' (DNS t i))).comp
    (ContinuousLinearMap.proj i)

theorem LNS_apply (t : ℂ) (w : E8) (i : Fin 4) :
    LNS t w i = if i = 0 then w 0 else ![w i 0, (t.im / 2) * w i 1] := by
  by_cases hi : i = 0
  · subst hi
    simp [LNS, DNS]
  · have hD : DNS t i = Matrix.diagonal ![1, t.im / 2] := by simp [DNS, hi]
    simp only [LNS, hi, ite_false]
    funext j
    fin_cases j <;> simp [hD, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem det_LNS (htre : t.re = 0) : |LinearMap.det (LNS t : E8 →ₗ[ℝ] E8)| = ‖t‖ ^ 3 / 8 := by
  have h : LinearMap.det (LNS t : E8 →ₗ[ℝ] E8) = ∏ i : Fin 4, Matrix.det (DNS t i) := by
    exact (ContinuousLinearMap.det_pi (fun i : Fin 4 =>
      LinearMap.toContinuousLinearMap (Matrix.toLin' (DNS t i)))).trans
      (Finset.prod_congr rfl fun i _ => LinearMap.det_toLin' _)
  rw [h]
  have hn : ‖t‖ = |t.im| := by
    rw [Complex.norm_def, Complex.normSq_apply, htre]
    simp [Real.sqrt_mul_self_eq_abs]
  simp [Fin.prod_univ_succ, DNS, Matrix.det_diagonal, hn, abs_div, abs_pow]
  ring

/-! ### The directional derivative at $0$ -/

theorem hd_f0 {c S : ℝ → ℝ} (hc : HasDerivAt c 0 0) (hS : HasDerivAt S 0 0) (hc0 : c 0 = 1 / 2) (hS0 : S 0 = 1) :
    HasDerivAt (fun s => (c s : ℂ) * (1 + (S s : ℂ))) 0 0 := by
  have := hc.ofReal_comp.mul (hS.ofReal_comp.const_add 1)
  refine this.congr_deriv ?_
  simp [hc0, hS0]

theorem hd_fk {c vv : ℝ → ℝ} {v : ℝ} (hc : HasDerivAt c 0 0) (hv : HasDerivAt vv v 0) (hc0 : c 0 = 1 / 2)
    (hv0 : vv 0 = 0) : HasDerivAt (fun s => (c s : ℂ) * (t * (vv s : ℂ))) (t * v / 2) 0 := by
  have := hc.ofReal_comp.mul (hv.ofReal_comp.const_mul t)
  refine this.congr_deriv ?_
  simp [hc0, hv0]
  ring

theorem hd_g0 {r : ℝ → ℝ} (hr : HasDerivAt r 0 0) : HasDerivAt (fun s => (r s : ℂ)) 0 0 := by
  simpa using hr.ofReal_comp

theorem hd_gk {r vv : ℝ → ℝ} {v : ℝ} (hr : HasDerivAt r 0 0) (hr0 : r 0 = 1) (hv : HasDerivAt vv v 0)
    (hv0 : vv 0 = 0) : HasDerivAt (fun s => ((r s * vv s : ℝ) : ℂ)) (v : ℂ) 0 := by
  have := (hr.mul hv).ofReal_comp
  refine this.congr_deriv ?_
  simp [hr0, hv0]

theorem hasDerivAt_eC {G : ℝ → Fin 4 → ℂ} {G' : Fin 4 → ℂ} (hG : HasDerivAt G G' 0) :
    HasDerivAt (fun s => eC (G s)) (eC G') 0 := by
  rw [hasDerivAt_pi]; intro i; rw [hasDerivAt_pi]; intro j
  have hi := hasDerivAt_pi.1 hG i
  fin_cases j
  · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hi
  · exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hi

theorem hasDerivAt_chartNS_line (htre : t.re = 0) (p : E8) :
    HasDerivAt (fun s : ℝ => chartNS A B d t (s • p)) (LNS t p) 0 := by
  set u : Fin 3 → ℝ := fun k => p k.succ 1 with hu
  set z : Fin 3 → ℝ := fun k => p k.succ 0 with hz
  have hU : ∀ s : ℝ, (fun k : Fin 3 => (s • p) k.succ 1) = s • u := fun s => by funext k; simp [u]
  have hZ : ∀ s : ℝ, (fun k : Fin 3 => (s • p) k.succ 0) = s • z := fun s => by funext k; simp [z]
  have hline : ∀ v : ℝ, HasDerivAt (fun s : ℝ => s * v) v 0 := fun v => by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const v
  have hvu : ∀ k, HasDerivAt (fun s : ℝ => (s • u) k) (u k) 0 := fun k => by simpa using hline (u k)
  have hvz : ∀ k, HasDerivAt (fun s : ℝ => (s • z) k) (z k) 0 := fun k => by simpa using hline (z k)
  have hS0 : Real.sqrt (1 - qPD A B d ((0 : ℝ) • u)) = 1 := by simp
  have hc0 : cc (Real.sqrt (1 - qPD A B d ((0 : ℝ) • u))) = 1 / 2 := by simp [cc_one]
  have hfU : HasDerivAt (fun s : ℝ => fU A B d t (s • u))
      ![0, t * (u 0 : ℂ) / 2, t * (u 1 : ℂ) / 2, t * (u 2 : ℂ) / 2] 0 := by
    simp only [fU, qVec_gr_cayX]
    rw [hasDerivAt_pi]; intro i
    fin_cases i
    · exact hd_f0 (hasDerivAt_cline u) (hasDerivAt_sline u) hc0 hS0
    · exact hd_fk (vv := fun s => (s • u) 0) (hasDerivAt_cline u) (hvu 0) hc0 (by simp)
    · exact hd_fk (vv := fun s => (s • u) 1) (hasDerivAt_cline u) (hvu 1) hc0 (by simp)
    · exact hd_fk (vv := fun s => (s • u) 2) (hasDerivAt_cline u) (hvu 2) hc0 (by simp)
  have hr0 : rr A B ((0 : ℝ) • z) = 1 := by simp [rr]
  have hgZ : HasDerivAt (fun s : ℝ => gZ A B (s • z)) ![0, (z 0 : ℂ), (z 1 : ℂ), (z 2 : ℂ)] 0 := by
    simp only [gZ, qVec_qC_cay]
    rw [hasDerivAt_pi]; intro i
    fin_cases i
    · exact hd_g0 (hasDerivAt_rline z)
    · exact hd_gk (vv := fun s => (s • z) 0) (hasDerivAt_rline z) hr0 (hvz 0) (by simp)
    · exact hd_gk (vv := fun s => (s • z) 1) (hasDerivAt_rline z) hr0 (hvz 1) (by simp)
    · exact hd_gk (vv := fun s => (s • z) 2) (hasDerivAt_rline z) hr0 (hvz 2) (by simp)
  have hf0 : fU A B d t ((0 : ℝ) • u) = ![1, 0, 0, 0] := by
    simp only [fU, qVec_gr_cayX]
    funext i
    fin_cases i <;> simp [cc_one] <;> norm_num
  have hg0 : gZ A B ((0 : ℝ) • z) = ![1, 0, 0, 0] := by
    simp only [gZ, qVec_qC_cay]
    funext i
    fin_cases i <;> simp [rr]
  have hq := hasDerivAt_qmul (A : ℂ) (B : ℂ) hfU hgZ hf0 hg0
  have hβ : HasDerivAt (fun s : ℝ => betaW (s • p)) ((p 0 0 : ℂ) + (p 0 1 : ℂ) * Complex.I) 0 := by
    have h0 := (hline (p 0 0)).ofReal_comp
    have h1 := ((hline (p 0 1)).ofReal_comp).mul_const Complex.I
    have := (h0.add h1).const_add 1
    unfold betaW
    simpa using this
  have hF := hβ.smul hq
  have hE := hasDerivAt_eC hF
  have e : (fun s : ℝ => chartNS A B d t (s • p)) = fun s : ℝ => eC (betaW (s • p) • qVec (vecQ (fU A B d t (s • u)) *
      vecQ (gZ A B (s • z)) : ℍ[ℂ, (A : ℂ), (B : ℂ)])) := by
    funext s; rw [chartNS_eq, hU, hZ]
  rw [e]
  refine hE.congr_deriv ?_
  have hX0 : qVec (vecQ (fU A B d t ((0 : ℝ) • u)) * vecQ (gZ A B ((0 : ℝ) • z)) : ℍ[ℂ, (A : ℂ), (B : ℂ)]) =
      ![1, 0, 0, 0] := by
    rw [hf0, hg0, qVec_mul_vecQ]
    funext i; fin_cases i <;> simp
  have hb0 : betaW ((0 : ℝ) • p) = 1 := by simp [betaW]
  rw [hb0, hX0]
  funext i j
  fin_cases i <;> fin_cases j <;> simp [eC, LNS_apply, hu, hz, htre] <;> ring

/-- **The strict derivative of the chart at $0$ is `LNS`.** -/
theorem hasStrictFDerivAt_chartNS (htre : t.re = 0) :
    HasStrictFDerivAt (chartNS A B d t) (LNS t) 0 := by
  have h := (contDiffAt_chartNS (A := A) (B := B) (d := d) (t := t)).hasStrictFDerivAt (by simp)
  convert h using 1
  refine ContinuousLinearMap.ext fun p => ?_
  have hd : HasFDerivAt (chartNS A B d t) (fderiv ℝ (chartNS A B d t) 0) ((0 : ℝ) • p) := by
    rw [zero_smul]
    exact (contDiffAt_chartNS.differentiableAt (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun r : ℝ => r • p) p 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const p
  have h1 : HasDerivAt (fun r : ℝ => chartNS A B d t (r • p)) (fderiv ℝ (chartNS A B d t) 0 p) 0 := by
    simpa [Function.comp_def] using hd.comp_hasDerivAt (0 : ℝ) hline
  exact (hasDerivAt_chartNS_line htre p).unique h1

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
