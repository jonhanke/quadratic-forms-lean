/-
# Coordinates for the Fourier coefficients of Siegel modular forms over a totally real field
**Layer:** archimedean, over a totally real number field $F$ of degree $d$ with real places $w$.

**Setting.** $b = (b_j)_{j<d}$ = `HilbertModular.oBasis F`, the real embeddings of a $\mathbb Z$-basis of $\mathcal O_F$ (a basis of $\mathbb R^d$ whose
$\mathbb Z$-span is $\sigma(\mathcal O_F)$). A real symmetric $r\times r$ matrix at every real place, $X = (X_w)_w \in \mathrm{Sym}_r(\mathbb R)^d$, is
written in the coordinates $t = (t_{p,j})$, $p = (i \le i')$ an upper index (`SymIdx r`), $j < d$:
$$(X_w)_{ii'} = \sum_jt_{p,j}\,(b_j)_w\qquad(\texttt{xCoord}, \texttt{xMat}),$$
so that $t \in \mathbb Z^{J}$ ($J = $ `JR F r`) is exactly $X \in \sigma(\mathrm{Sym}_r(\mathcal O_F))$ (`xCoord_add_int`). For $Y = (Y_w)_w$ with $Y_w$
positive definite, $Z(t) = X(t) + iY$ (`zPt`) runs over the horizontal slice of $\mathbb H_r^d$ at height $Y$.

**Definitions.**
* `coeffR f T Y` (**the $T$-th Fourier coefficient at height $Y$**):
  $\displaystyle\int_{t\in(0,1]^J}f\big(X(t) + iY\big)\,e_T\big(-X(t)\big)\,dt$, $e_T(Z) = \exp\big(2\pi i\sum_w\operatorname{tr}(\sigma_w(T_G)Z_w)\big)$ (`eT`).
  For $r = 1$ this is `HilbertModular.coeff` (with the basis `oBasis F`).
* `realMat B` = $(\sigma_w(B))_w$ for $B \in M_r(F)$.

Sources: Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I (Fourier expansions of Siegel modular forms) [unverified]; Garrett,
*Holomorphic Hilbert Modular Forms* (1990), Ch. 1 [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinBigCell
import QuadFormsKB.HilbertModular.EisensteinCoeff
import QuadFormsKB.HilbertModular.QExpansion

open Matrix NumberField IsDedekindDomain MeasureTheory
open QuadFormsKB.HilbertModular
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

variable (F r) in
/-- The index set $J = \{(p, j)\}$ of the real coordinates of $\mathrm{Sym}_r(\mathbb R)^d$: an upper index $p = (i \le i')$ and a basis index
$j < d$. -/
abbrev JR : Type := SymIdx r × Fin (Module.finrank ℚ F)

/-- The $p$-th entry $\sum_jt_{p,j}b_j \in \mathbb R^d$ (one real number per real place). -/
def xCoord (t : JR F r → ℝ) (p : SymIdx r) : InfinitePlace F → ℝ :=
  (oBasis F).equivFun.symm (fun j => t (p, j))

/-- The real symmetric matrix $X_w(t)$ at the real place $w$. -/
def xMat (t : JR F r → ℝ) (w : InfinitePlace F) : Matrix (Fin r) (Fin r) ℝ := symOf fun p => xCoord t p w

/-- The point $Z(t) = X(t) + iY$ of $\mathbb H_r^d$. -/
def zPt (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (t : JR F r → ℝ) : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ :=
  fun w => (xMat t w).map (fun x => (x : ℂ)) + (Y w).map (fun y => (y : ℂ) * Complex.I)

/-- $(\sigma_w(B))_w$ for $B \in M_r(F)$, as complex matrices. -/
def realMat (B : Matrix (Fin r) (Fin r) F) (w : InfinitePlace F) : Matrix (Fin r) (Fin r) ℂ :=
  B.map (fun x => (realEmb F w x : ℂ))

/-- **The $T$-th Fourier coefficient at height $Y$** of $f$ on $\mathbb H_r^d$, over the unit cube of the coordinates $t$:
$c_T(f, Y) = \int_{(0,1]^J}f(X(t) + iY)\,e_T(-X(t))\,dt$. Parameters: `f`, `T` (a form in $r$ variables over $F$, paired through its Gram
matrix $T_G$), `Y` (the height). -/
@[kb "freitag1983" "Ch. I (Fourier coefficients of Siegel modular forms) [unverified]"]
def coeffR (f : (InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) → ℂ) (T : QuadForm F r)
    (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) : ℂ :=
  ∫ t in unitCube (JR F r), f (zPt Y t) * eT T (fun w => -(xMat t w).map (fun x => (x : ℂ)))

/-! ### Basic facts -/

lemma xCoord_add (t s : JR F r → ℝ) (p : SymIdx r) : xCoord (t + s) p = xCoord t p + xCoord s p := by
  unfold xCoord
  rw [← map_add]; rfl

lemma symOf_add {K : Type*} [CommRing K] (u u' : SymIdx r → K) : symOf (u + u') = symOf u + symOf u' := by
  ext i j; simp only [symOf, Matrix.add_apply, of_apply, Pi.add_apply]; split_ifs <;> rfl

lemma xMat_add (t s : JR F r → ℝ) (w : InfinitePlace F) : xMat (t + s) w = xMat t w + xMat s w := by
  unfold xMat
  rw [← symOf_add]
  congr 1; funext p; rw [xCoord_add]; rfl

lemma zPt_add (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (t s : JR F r → ℝ) (w : InfinitePlace F) :
    zPt Y (t + s) w = zPt Y t w + (xMat s w).map (fun x => (x : ℂ)) := by
  unfold zPt
  rw [xMat_add, Matrix.map_add _ (by intros; push_cast; ring)]
  abel

/-- The coordinates of an element of $F$: $\sigma(x) = \sum_jc_j(x)b_j$. -/
def fCoord (x : F) : Fin (Module.finrank ℚ F) → ℝ := (oBasis F).equivFun (realVec x)

/-- The coordinates $t(B)$ of $\sigma(B)$ for $B = \operatorname{symOf}(u)$, $u \in F^{\{i\le i'\}}$. -/
def tOf (u : SymIdx r → F) : JR F r → ℝ := fun q => fCoord (u q.1) q.2

lemma xCoord_tOf (u : SymIdx r → F) (p : SymIdx r) : xCoord (tOf u) p = realVec (u p) := by
  unfold xCoord tOf fCoord
  simp

lemma xMat_tOf (u : SymIdx r → F) (w : InfinitePlace F) :
    (xMat (tOf u) w).map (fun x => (x : ℂ)) = realMat (symOf u) w := by
  ext i j
  simp only [xMat, realMat, symOf, map_apply, of_apply]
  split_ifs <;> simp [xCoord_tOf, realVec]

/-- $\sigma(\mathcal O_F)$ has integral coordinates: for $o \in \mathcal O_F$ there is $n \in \mathbb Z^d$ with $\sigma(o) = \sum_jn_jb_j$. -/
lemma exists_int_fCoord (o : 𝓞 F) : ∃ n : Fin (Module.finrank ℚ F) → ℤ, fCoord (ιO o) = fun j => (n j : ℝ) := by
  have hmem : ιO o ∈ ((1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [Units.val_one]; exact (FractionalIdeal.mem_one_iff _).mpr ⟨o, rfl⟩
  obtain ⟨n, hn⟩ := latElt_surj 1 hmem
  refine ⟨n, ?_⟩
  unfold fCoord
  rw [← hn, ← koecherBasis_symm]
  exact (oBasis F).equivFun.apply_symm_apply _

/-- Conversely, integral coordinates give an element of $\mathcal O_F$. -/
lemma exists_int_of_fCoord (n : Fin (Module.finrank ℚ F) → ℤ) :
    ∃ o : 𝓞 F, (oBasis F).equivFun.symm (fun j => (n j : ℝ)) = realVec (ιO o) := by
  obtain ⟨o, ho⟩ := oElt_mem n
  refine ⟨o, ?_⟩
  rw [ho]
  exact koecherBasis_symm _ n

end QuadFormsKB.SiegelWeil.Forms
