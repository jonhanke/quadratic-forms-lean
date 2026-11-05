/-
# Hanke 2005, §4.3: the fibre volume $\mathrm{vol}_C(C_{\mathbb C})$ (statement; proved for $n\ge1$)

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Setting** (§4.3, pp. 13–15). $G_{\mathbb C} = SO_n(\mathbb C)$, realized as $SO(Q)(\mathbb C)$ for the sum of squares
$Q = x_0^2+\dots+x_{n-1}^2$ (`sumSqC`, Gram matrix $1_n$), with the repository's complex Leray measure
`LerayComplex.lerayMeasureC` (real Lebesgue measure $dx\,dy$ on $M_n(\mathbb C)$ and on the coefficient space).
$Z_{\mathbb C} = \{z\in\mathbb R^{n\times n} : {}^tz = -z,\ {}^tzz < 1\}$ (`ZC`), $F_{\mathbb C}(\alpha) = \alpha\cdot0 = -ba^{-1}$
for $\alpha = a + bi$ ((4.3.3)–(4.3.4), `actC_zero`), with fibre $C_{\mathbb C} = SO_n(\mathbb R)$ ((4.3.5)).

**Defines**
* `LIdx n` (the pairs $i > k$), `skewOf`, `lowerOf`: the coordinates $z_{ik}$, $i > k$, of skew matrices;
* `deltaC z` $=\delta(z) = \det(1 - {}^tzz)$ ((4.3.6)–(4.3.7));
* `muZC n`: Shimura's measure $\omega_Z = \delta(z)^{(1-n)/2}\bigwedge_{i>k}dz_{ik}$ ((4.3.9)) on $Z_{\mathbb C}$;
* `FCG`: $F_{\mathbb C}$ on $SO_n(\mathbb C)$ in these coordinates;
* `hankeHaarC n` $= 2^{3n(n-1)/2}\cdot$`lerayMeasureC`: Hanke's $\widetilde\omega_G$ at a complex place. *Normalization:*
  Hanke's local measure is $i\,dz\wedge d\bar z = 2\,dx\,dy$ per coordinate ((2.4)) and Gram coordinates $t_{ij}$, so
  $\widetilde\omega_G = 2^{n^2 - n(n+1)/2}\cdot(dX/dT)_{dx\,dy}$, and the repository's coefficient coordinates
  $c_{ij} = 2t_{ij}$ ($i<j$) contribute $|2|_{\mathbb C}^{n(n-1)/2} = 4^{n(n-1)/2}$; in total $2^{3n(n-1)/2}$ (the same factor
  as in `muArchHanke` at a complex place: $2^{2\cdot n(n-1)/2}$ from $2^{d\,n(n-1)/2}$ times `cxWeil`'s $2^{n(n-1)/2}$).

**Statement** `ArchFibrationComplex n` (the computation of §4.3, pp. 14–15):
$(F_{\mathbb C})_*\widetilde\omega_G = \mathrm{vol}_C(C_{\mathbb C})\,\mu_Z$ with
$\mathrm{vol}_C(C_{\mathbb C}) = 2^{n(n-3)/2}\tau_{\mathbb R}(SO_n(\mathbb R))$ (`volCComplex`). It is the complex analogue of
the real-place theorem `ArchReal.map_FR_hankeHaar`.
**Proved for every $n\ge1$** (`ArchCx.archFibrationComplex`, `ArchVolumeComplex.lean`), following Hanke's
proof: coordinates $X = (1 - iu)Y(1 - i\sigma)$ adapted to $F_{\mathbb C}$, whose Jacobian is computed exactly (Lemma A5), the
weighted Gram co-area formula in $Y$ (which produces $\delta^{(1-n)/2}$), and the Leray limit at the fibre (Lemma A6: only the
restriction to the fibre matters). **False for $n = 0$** (`ArchCx.not_archFibrationComplex_zero`): $SO_0(\mathbb C)$ is a point of
Leray mass $1$ while `volCComplex 0` $= \tfrac12$; all consumers assume $n\ge1$.
*Check* ($n = 2$, by hand): $SO_2(\mathbb C)\ni
\theta = u + iv$, $\widetilde\omega_G = \tfrac18du\,dv$, $F_{\mathbb C} = -\tanh v$, $\omega_Z = d\zeta/(1-\zeta^2)$, so
$(F_{\mathbb C})_*\widetilde\omega_G = 2\pi\cdot\tfrac18\,\omega_Z = \tfrac\pi4\,\omega_Z$, and `volCComplex 2` $= \pi/4$.
-/
import QuadFormsKB.Literature.Hanke2005.SymmetricSpaceC
import QuadFormsKB.Literature.Hanke2005.Archimedean
import QuadFormsKB.Tamagawa.Measure.LerayComplex

open MeasureTheory Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchCx

open QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {n : ℕ}

/-- The index pairs $(i, k)$ with $i > k$ (strictly lower triangular positions). -/
abbrev LIdx (n : ℕ) := {p : Fin n × Fin n // p.2 < p.1}

/-- The skew-symmetric matrix with coordinates $z_{ik} = v_{ik}$ ($i > k$). -/
def skewOf (v : LIdx n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k => if h : k < i then v ⟨(i, k), h⟩ else if h' : i < k then -v ⟨(k, i), h'⟩ else 0

/-- The coordinates $z_{ik}$, $i > k$, of a matrix. -/
def lowerOf (z : Matrix (Fin n) (Fin n) ℝ) : LIdx n → ℝ := fun p => z p.1.1 p.1.2

theorem lowerOf_skewOf (v : LIdx n → ℝ) : lowerOf (skewOf v) = v := by
  funext p; simp [lowerOf, skewOf, p.2]

theorem skewOf_lowerOf {z : Matrix (Fin n) (Fin n) ℝ} (hz : zᵀ = -z) : skewOf (lowerOf z) = z := by
  ext i k
  simp only [skewOf, lowerOf, of_apply]
  have hs : ∀ a b, z b a = -z a b := fun a b => by
    have := congrFun (congrFun hz a) b
    rwa [transpose_apply, Matrix.neg_apply] at this
  split_ifs with h h'
  · rfl
  · rw [hs i k, neg_neg]
  · have hik : i = k := le_antisymm (not_lt.mp h) (not_lt.mp h')
    subst hik
    have := hs i i
    linarith

/-- $\delta(z) = \det(1 - {}^tzz)$ (Hanke thesis, (4.3.6)–(4.3.7), p. 14). -/
@[kb "hanke2005crelle" "(4.3.6)–(4.3.7), p. 14 (δ(z))"]
def deltaC (z : Matrix (Fin n) (Fin n) ℝ) : ℝ := (1 - zᵀ * z).det

/-- **Shimura's invariant measure on $Z_{\mathbb C}$** (Hanke thesis, (4.3.9), p. 14):
$\omega_Z = \delta(z)^{(1-n)/2}\bigwedge_{i>k}dz_{ik}$, as a measure on the coordinates $(z_{ik})_{i>k}$. -/
@[kb "hanke2005crelle" "(4.3.9), p. 14 (ω_Z on Z_C)"]
def muZC (n : ℕ) : Measure (LIdx n → ℝ) :=
  (volume.restrict (skewOf ⁻¹' ZC n)).withDensity fun v => ENNReal.ofReal (deltaC (skewOf v) ^ ((1 - (n : ℝ)) / 2))

/-- The sum of squares $x_0^2+\dots+x_{n-1}^2$ over $\mathbb C$; $SO(Q)(\mathbb C) = SO_n(\mathbb C)$. -/
def sumSqC (n : ℕ) : QuadForm ℂ n := QuadForm.diag fun _ => 1

theorem gramC_sumSqC : gramC (sumSqC n) = 1 := by
  ext i j
  simp only [gramC, sumSqC, QuadForm.hessian, QuadForm.diag, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, diagonal_apply, one_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h; simp; norm_num
  · simp [h, Ne.symm h]

theorem gramDetC_sumSqC_ne_zero : gramDetC (sumSqC n) ≠ 0 := by
  rw [gramDetC, gramC_sumSqC, det_one]; exact one_ne_zero

theorem mat_mem_SOC (g : ArchSOC (sumSqC n)) : ArchSOC.mat _ g ∈ SOC n := by
  have h := ArchSOC.isometry _ g
  rw [gramC_sumSqC, Matrix.mul_one] at h
  exact ⟨h, ArchSOC.det_mat _ g⟩

/-- **$F_{\mathbb C}$ on $SO_n(\mathbb C)$** (Hanke thesis, (4.3.3)–(4.3.4), p. 14): $\alpha = a + bi\mapsto\alpha\cdot0 = -ba^{-1}$,
in the coordinates $z_{ik}$, $i > k$. -/
@[kb "hanke2005crelle" "(4.3.3)–(4.3.4), p. 14 (F_C)"]
def FCG (g : ArchSOC (sumSqC n)) : LIdx n → ℝ := lowerOf (actC (ArchSOC.mat _ g) 0)

theorem FCG_mem (g : ArchSOC (sumSqC n)) : skewOf (FCG g) ∈ ZC n := by
  have hz := (actC_mem (mat_mem_SOC g) zero_mem_ZC).2
  rw [FCG, skewOf_lowerOf hz.1]; exact hz

/-- **Hanke's $\widetilde\omega_G$ at a complex place**, $2^{3n(n-1)/2}\cdot$`lerayMeasureC` (see the module docstring for
the normalization). -/
@[kb "hanke2005crelle" "§2, (2.4), p. 4; Calculation 4.1, pp. 9–10; §4.3, p. 15 (ω̃_G at a complex place)"]
def hankeHaarC (n : ℕ) : Measure (ArchSOC (sumSqC n)) :=
  ENNReal.ofReal ((2 : ℝ) ^ (3 * (n * (n - 1) / 2))) • lerayMeasureC (sumSqC n) gramDetC_sumSqC_ne_zero

/-- **The fibre volume at a complex place** (Hanke thesis, §4.3, pp. 14–15): the push-forward of
Hanke's Haar measure on $SO_n(\mathbb C)$ under $F_{\mathbb C}$ is $\mathrm{vol}_C(C_{\mathbb C})\cdot\omega_Z$,
$\mathrm{vol}_C(C_{\mathbb C}) = 2^{n(n-3)/2}\tau_{\mathbb R}(SO_n(\mathbb R))$ (Hanke's computation with differential forms, using
Lemmas A4–A6 and (4.1.1)). Proved for $n\ge1$ (`ArchCx.archFibrationComplex`); false for $n = 0$
(`ArchCx.not_archFibrationComplex_zero`). -/
@[kb "hanke2005crelle" "§4.3, pp. 14–15 (ω_C and vol_C(C_C))"]
structure ArchFibrationComplex (n : ℕ) : Prop where
  /-- $(F_{\mathbb C})_*\widetilde\omega_G = \mathrm{vol}_C(C_{\mathbb C})\,\omega_Z$. -/
  map_eq : (hankeHaarC n).map FCG = ENNReal.ofReal (volCComplex n) • muZC n

end QuadFormsKB.Hanke2005.ArchCx
