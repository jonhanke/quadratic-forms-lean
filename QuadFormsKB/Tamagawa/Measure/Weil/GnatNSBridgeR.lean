import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSMaps
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSGlobal
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSPlaces
import QuadFormsKB.Tamagawa.Measure.Weil.NSArchSplitR
import QuadFormsKB.Tamagawa.Measure.Weil.NSArchNSGroup

/-!
# The bridge at a real place of $F$: the global archimedean map of the non-square model versus the local maps


**Layer.** `nsR v g` $=\varphi(\Theta^{-1}g_1)_v$ (`GnatNSMaps`) is the matrix of $\varphi_x$, $x = (\Theta^{-1}g_1)_v\in D_E\otimes F_v$,
$F_v=\mathbb R$.

**Step 1 (algebra at one real place).** For $t^2=D$ the ring homomorphism $\psi_t : D_E\to\mathbb H[S,A,B]$, $r+s\delta\mapsto r+ts$
(`psi`; $S=\mathbb R$ or $\mathbb C$) turns $\varphi_x$ into
* ($t\in\mathbb R$, `toMatrix'_phiLin_real`) $\operatorname{nrd}(x)^{-1}\;T^{-1}\,(v\mapsto\psi_t(x)\,v\,\overline{\psi_{-t}(x)})\,T$;
* ($t\in\mathbb C$, $\operatorname{Re}t=0$, `toMatrix'_phiLin_cx`) $\operatorname{nrd}(x)^{-1}\,$`MR t (ψ_t x)`.

**Step 2 (global).** The coordinates of $m=g_1\in(D'\otimes\mathbb A_K)^\times$ at the places $w$ of $K$ over $v$ are $\psi_{\pm t}$ of the
coordinates of $\Theta^{-1}m$ at $v$ (`qVec_psi_deMap_real`, `qVec_psi_deMap_cx`), hence `mat (nsR v g)` is $\operatorname{nrd}^{-1}$ times the
matrix of the local map (`mat_nsR_real`, `mat_nsR_cx`), and for $r=g_{2,v}>0$ it is `phiSplit` / `phiNS` of the normalized sphere points
(`mat_nsR_eq_phiSplit`, `mat_nsR_eq_phiNS`).
-/

open Matrix Quaternion NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Quaternion ComplexConjugate

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Quat.Gnat

/-! ### Step 1: the specialization homomorphism $\psi_t : D_E\to\mathbb H[S,A,B]$ -/

section Psi

variable {R S : Type*} [Field R] [Field S] {A B D : R}

/-- $E=R[\delta]/(\delta^2-D)\to S$, $r+s\delta\mapsto f(r)+t f(s)$, for $t^2=f(D)$. -/
def evQ (f : R →+* S) (t : S) (ht : t ^ 2 = f D) : QE D →+* S where
  toFun z := f z.re + t * f z.im
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, zero_mul, add_zero]
    linear_combination (-(f z.im * f w.im)) * ht
  map_zero' := by simp
  map_add' z w := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]; ring

/-- **$\psi_t : D_E\to\mathbb H[S,A',B']$**, coefficientwise `evQ`. -/
def psi (f : R →+* S) (t : S) (ht : t ^ 2 = f D) {A' B' : S} (hA : f A = A') (hB : f B = B') :
    DE A B D →+* ℍ[S, A', B'] :=
  QuaternionAlgebra.mapRingHom (evQ f t ht) (by simp [evQ, hA]) (map_zero _) (by simp [evQ, hB])

theorem psi_re (f : R →+* S) (t : S) (ht : t ^ 2 = f D) {A' B' : S} (hA : f A = A') (hB : f B = B') (x : DE A B D) :
    (psi f t ht hA hB x).re = f x.re.re + t * f x.re.im := rfl
theorem psi_imI (f : R →+* S) (t : S) (ht : t ^ 2 = f D) {A' B' : S} (hA : f A = A') (hB : f B = B') (x : DE A B D) :
    (psi f t ht hA hB x).imI = f x.imI.re + t * f x.imI.im := rfl
theorem psi_imJ (f : R →+* S) (t : S) (ht : t ^ 2 = f D) {A' B' : S} (hA : f A = A') (hB : f B = B') (x : DE A B D) :
    (psi f t ht hA hB x).imJ = f x.imJ.re + t * f x.imJ.im := rfl
theorem psi_imK (f : R →+* S) (t : S) (ht : t ^ 2 = f D) {A' B' : S} (hA : f A = A') (hB : f B = B') (x : DE A B D) :
    (psi f t ht hA hB x).imK = f x.imK.re + t * f x.imK.im := rfl

theorem psi_star (f : R →+* S) (t : S) (ht : t ^ 2 = f D) {A' B' : S} (hA : f A = A') (hB : f B = B') (x : DE A B D) :
    psi f t ht hA hB (star x) = star (psi f t ht hA hB x) := by
  ext <;> simp [psi_re, psi_imI, psi_imJ, psi_imK] <;> ring

theorem psi_emb (f : R →+* S) (t : S) (ht : t ^ 2 = f D) {A' B' : S} (hA : f A = A') (hB : f B = B') (v : Fin 4 → R) :
    psi f t ht hA hB (emb v) = ⟨f (v 0), t * f (v 1), t * f (v 2), t * f (v 3)⟩ := by
  ext <;> simp [psi_re, psi_imI, psi_imJ, psi_imK, emb]

/-- $\psi_t\circ\sigma=\psi_{-t}$. -/
theorem psi_sig (f : R →+* S) (t : S) (ht : t ^ 2 = f D) (ht' : (-t) ^ 2 = f D) {A' B' : S} (hA : f A = A')
    (hB : f B = B') (y : DE A B D) :
    psi f t ht hA hB (sig y) = psi f (-t) ht' hA hB y := by
  ext <;> simp [psi_re, psi_imI, psi_imJ, psi_imK]

/-- $\psi_t$ of the reduced norm: if $\operatorname{nrd}_E x=r\in R$ then $\psi_t(x)\overline{\psi_t(x)}=f(r)$. -/
theorem psi_mul_star (f : R →+* S) (t : S) (ht : t ^ 2 = f D) {A' B' : S} (hA : f A = A') (hB : f B = B')
    (x : DE A B D) (r : R) (h : nrdE x = algebraMap R (QE D) r) :
    psi f t ht hA hB x * star (psi f t ht hA hB x) = ((f r : S) : ℍ[S, A', B']) := by
  rw [← psi_star, ← map_mul, mul_star_eq_nrdE, h]
  ext <;> simp [psi_re, psi_imI, psi_imJ, psi_imK]

/-- **$\operatorname{nrd}(\psi_t x)=f(r)$** when $\operatorname{nrd}_E x=r\in R$. -/
theorem nrd_psi (f : R →+* S) (t : S) (ht : t ^ 2 = f D) {A' B' : S} (hA : f A = A') (hB : f B = B')
    (x : DE A B D) (r : R) (h : nrdE x = algebraMap R (QE D) r) :
    nrd (psi f t ht hA hB x) = f r := by
  have h1 := psi_mul_star f t ht hA hB x r h
  rw [mul_star_eq_nrd] at h1
  simpa using congrArg QuaternionAlgebra.re h1

end Psi

/-! #### Real specialization -/

section Real

variable {A B D t : ℝ}

/-- $\psi_t : D_E\to\mathbb H[\mathbb R,A,B]$, $r+s\delta\mapsto r+ts$ ($t^2=D$). -/
def psiR (t : ℝ) (ht : t ^ 2 = D) : DE A B D →+* ℍ[ℝ, A, B] := psi (RingHom.id ℝ) t ht rfl rfl

theorem psiR_re (ht : t ^ 2 = D) (x : DE A B D) : (psiR t ht x).re = x.re.re + t * x.re.im := rfl
theorem psiR_imI (ht : t ^ 2 = D) (x : DE A B D) : (psiR t ht x).imI = x.imI.re + t * x.imI.im := rfl
theorem psiR_imJ (ht : t ^ 2 = D) (x : DE A B D) : (psiR t ht x).imJ = x.imJ.re + t * x.imJ.im := rfl
theorem psiR_imK (ht : t ^ 2 = D) (x : DE A B D) : (psiR t ht x).imK = x.imK.re + t * x.imK.im := rfl

theorem neg_sq_eq (ht : t ^ 2 = D) : (-t) ^ 2 = D := (neg_sq t).trans ht

theorem psiR_star (ht : t ^ 2 = D) (x : DE A B D) : psiR t ht (star x) = star (psiR t ht x) :=
  psi_star _ _ _ _ _ x

theorem psiR_sig (ht : t ^ 2 = D) (y : DE A B D) : psiR t ht (sig y) = psiR (-t) (neg_sq_eq ht) y :=
  psi_sig _ _ _ (neg_sq_eq ht) _ _ y

theorem psiR_emb (ht : t ^ 2 = D) (v : Fin 4 → ℝ) :
    psiR t ht (emb v : DE A B D) = vecQ (NSArch.tMat t *ᵥ v) := by
  rw [NSArch.tMat_mulVec]
  ext <;> simp [psiR_re, psiR_imI, psiR_imJ, psiR_imK, emb, vecQ]

theorem coords_eq_psiR (ht0 : t ≠ 0) (ht : t ^ 2 = D) {y : DE A B D} (hy : InV0 y) :
    coords y = NSArch.tInv t *ᵥ qVec (psiR t ht y) := by
  have e := emb_coords (two_ne_zero (α := ℝ)) hy
  conv_rhs => rw [← e]
  rw [psiR_emb, qVec_vecQ, Matrix.mulVec_mulVec, NSArch.tInv_mul_tMat ht0, Matrix.one_mulVec]

/-- **Key identity (real, $E_w=\mathbb R\times\mathbb R$).**
$\varphi_x=\operatorname{nrd}(x)^{-1}\,T^{-1}\,\mathrm{sq}(\psi_t x,\overline{\psi_{-t}x})\,T$ as matrices. -/
theorem toMatrix'_phiLin_real (ht0 : t ≠ 0) (ht : t ^ 2 = D) (x : DE A B D) :
    LinearMap.toMatrix' (phiLin x) =
      (nrdK x)⁻¹ • (NSArch.tInv t * sqMat (psiR t ht x) (star (psiR (-t) (neg_sq_eq ht) x)) * NSArch.tMat t) := by
  have key : ∀ v : Fin 4 → ℝ, phiLin x v = ((nrdK x)⁻¹ • (NSArch.tInv t *
      sqMat (psiR t ht x) (star (psiR (-t) (neg_sq_eq ht) x)) * NSArch.tMat t)) *ᵥ v := by
    intro v
    rw [phiLin_apply, coords_eq_psiR ht0 ht (inV0_conj x _ (inV0_emb v)), map_mul, map_mul, psiR_emb,
      psiR_sig, psiR_star, Matrix.smul_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, sqMat_mulVec]
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [LinearMap.toMatrix'_mulVec, key]

end Real

/-! #### Complex specialization ($E_w=\mathbb C$) -/

section Cx

variable {A B D : ℝ} {t : ℂ}

/-- $\psi_t : D_E\to\mathbb H[\mathbb C,A,B]$, $r+s\delta\mapsto r+ts$ ($t^2=D$, $D$ real). -/
def psiC (t : ℂ) (ht : t ^ 2 = (D : ℂ)) : DE A B D →+* ℍ[ℂ, (A : ℂ), (B : ℂ)] :=
  psi Complex.ofRealHom t ht rfl rfl

theorem psiC_re (ht : t ^ 2 = (D : ℂ)) (x : DE A B D) : (psiC t ht x).re = (x.re.re : ℂ) + t * x.re.im := rfl
theorem psiC_imI (ht : t ^ 2 = (D : ℂ)) (x : DE A B D) : (psiC t ht x).imI = (x.imI.re : ℂ) + t * x.imI.im := rfl
theorem psiC_imJ (ht : t ^ 2 = (D : ℂ)) (x : DE A B D) : (psiC t ht x).imJ = (x.imJ.re : ℂ) + t * x.imJ.im := rfl
theorem psiC_imK (ht : t ^ 2 = (D : ℂ)) (x : DE A B D) : (psiC t ht x).imK = (x.imK.re : ℂ) + t * x.imK.im := rfl

theorem psiC_star (ht : t ^ 2 = (D : ℂ)) (x : DE A B D) : psiC t ht (star x) = star (psiC t ht x) :=
  psi_star _ _ _ _ _ x

/-- $\psi_t\circ\sigma=\bar{\ }\circ\psi_t$ when $\operatorname{Re}t=0$. -/
theorem psiC_sig (ht : t ^ 2 = (D : ℂ)) (htre : t.re = 0) (y : DE A B D) :
    psiC t ht (sig y) = NSArch.conjQ (psiC t ht y) := by
  ext <;> simp [psiC_re, psiC_imI, psiC_imJ, psiC_imK, NSArch.conj_t htre]

theorem psiC_emb (ht : t ^ 2 = (D : ℂ)) (v : Fin 4 → ℝ) :
    psiC t ht (emb v : DE A B D) = vecQ (NSArch.tMatN t *ᵥ (fun i => (v i : ℂ))) := by
  rw [NSArch.tMatN_mulVec]
  ext <;> simp [psiC_re, psiC_imI, psiC_imJ, psiC_imK, emb, vecQ]

theorem coords_eq_psiC (ht0 : t ≠ 0) (ht : t ^ 2 = (D : ℂ)) {y : DE A B D} (hy : InV0 y) :
    (fun i => ((coords y i : ℝ) : ℂ)) = NSArch.tInvN t *ᵥ qVec (psiC t ht y) := by
  have e := emb_coords (two_ne_zero (α := ℝ)) hy
  conv_rhs => rw [← e]
  rw [psiC_emb, qVec_vecQ, Matrix.mulVec_mulVec, NSArch.tInvN_mul_tMatC ht0, Matrix.one_mulVec]

/-- **Key identity (complex, $E_w=\mathbb C$).** $\varphi_x=\operatorname{nrd}(x)^{-1}\,$`MR t (ψ_t x)`. -/
theorem toMatrix'_phiLin_cx (ht0 : t ≠ 0) (htre : t.re = 0) (ht : t ^ 2 = (D : ℂ)) (x : DE A B D) :
    LinearMap.toMatrix' (phiLin x) = (nrdK x)⁻¹ • NSArch.MR t (psiC t ht x) := by
  have key : ∀ v : Fin 4 → ℝ, (fun i => ((phiLin x v i : ℝ) : ℂ)) =
      (((nrdK x)⁻¹ : ℝ) : ℂ) • (NSArch.MC t (psiC t ht x) *ᵥ (fun i => (v i : ℂ))) := by
    intro v
    have h1 : (fun i => ((phiLin x v i : ℝ) : ℂ)) =
        (((nrdK x)⁻¹ : ℝ) : ℂ) • (fun i => ((coords (x * emb v * sig (star x)) i : ℝ) : ℂ)) := by
      funext i; simp [phiLin_apply]
    rw [h1, coords_eq_psiC ht0 ht (inV0_conj x _ (inV0_emb v)), map_mul, map_mul, psiC_emb,
      psiC_sig ht htre, psiC_star, NSArch.MC, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, sqMat_mulVec]
  ext i j
  have h := congrFun (key (Pi.single j 1)) i
  have e : (fun k => ((Pi.single j (1 : ℝ) : Fin 4 → ℝ) k : ℂ)) = Pi.single j 1 := by
    funext k; by_cases hk : k = j <;> simp [hk]
  rw [e, Matrix.mulVec_single_one] at h
  have h2 := congrArg Complex.re h
  rw [LinearMap.toMatrix'_apply]
  simpa [NSArch.MR, Matrix.smul_apply, Pi.single_apply, Complex.re_ofReal_mul] using h2

end Cx

/-! ### Scaling lemmas -/

section Scale

variable {K : Type*} [Field K] {A B : K}

theorem qVec_smul (c : K) (x : ℍ[K,A,B]) : qVec (c • x) = c • qVec x := by
  funext i; fin_cases i <;> simp [qVec]

theorem vecQ_smul (c : K) (v : Fin 4 → K) : (vecQ (c • v) : ℍ[K,A,B]) = c • vecQ v := by
  ext <;> simp [vecQ]

theorem star_smul_quat (c : K) (x : ℍ[K,A,B]) : star (c • x) = c • star x := by
  ext <;> simp

theorem sqMat_smul_smul (c c' : K) (x y : ℍ[K,A,B]) : sqMat (c • x) (c' • y) = (c * c') • sqMat x y := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [sqMat_mulVec, Matrix.smul_mulVec, sqMat_mulVec]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, qVec_smul]
  rw [mul_comm c' c]

end Scale

section ScaleC

variable {A B : ℝ} {t : ℂ}

theorem conjQ_smul_real (c : ℝ) (X : ℍ[ℂ, (A : ℂ), (B : ℂ)]) :
    NSArch.conjQ ((c : ℂ) • X) = (c : ℂ) • NSArch.conjQ X := by
  ext <;> simp

theorem MR_smul_real (c : ℝ) (X : ℍ[ℂ, (A : ℂ), (B : ℂ)]) :
    NSArch.MR t ((c : ℂ) • X) = (c * c) • NSArch.MR t X := by
  have h : NSArch.MC t ((c : ℂ) • X) = ((c : ℂ) * (c : ℂ)) • NSArch.MC t X := by
    rw [NSArch.MC, NSArch.MC, star_smul_quat, conjQ_smul_real, sqMat_smul_smul, Matrix.mul_smul, Matrix.smul_mul]
  ext i j
  simp only [NSArch.MR, h, Matrix.smul_apply, smul_eq_mul, ← Complex.ofReal_mul, Complex.re_ofReal_mul]

theorem eval_normForm_sqrt_inv_cx (Y : ℍ[ℂ, (A : ℂ), (B : ℂ)]) {r : ℝ} (hr : 0 < r) (hY : nrd Y = (r : ℂ)) :
    (NSArch.normForm (A : ℂ) (B : ℂ)).eval ((((Real.sqrt r)⁻¹ : ℝ) : ℂ) • qVec Y) = 1 := by
  rw [NSArch.eval_normForm_smulC, NSArch.eval_normForm_qVec, hY, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    inv_pow, Real.sq_sqrt hr.le, inv_mul_cancel₀ hr.ne', Complex.ofReal_one]

end ScaleC

section ScaleR

variable {A B : ℝ}

theorem eval_normForm_sqrt_inv (Y : ℍ[ℝ, A, B]) {r : ℝ} (hr : 0 < r) (hY : nrd Y = r) :
    (NSArch.normForm A B).eval ((Real.sqrt r)⁻¹ • qVec Y) = 1 := by
  rw [NSArch.eval_normForm_smul, NSArch.eval_normForm_qVec, hY, inv_pow, Real.sq_sqrt hr.le,
    inv_mul_cancel₀ hr.ne']

end ScaleR

/-! ### Step 2: the global map -/

section Global

open IsDedekindDomain QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) {a b d : 𝓞 F}
  (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {A' B' : K} (hA' : A' = algebraMap F K (a : F)) (hB' : B' = algebraMap F K (b : F))
  (hA0 : A' ≠ 0) (hB0 : B' ≠ 0)

/-- **$\Theta(\Theta^{-1}m)=m$ coordinatewise**: `quadBaseChange` of the coordinates of `bcRing m` are the coordinates of `m`. -/
theorem quadBaseChange_bcRing (m : QuatAdele (F := K) A' B') :
    quadBaseChange hb₀ hb₁ (bcRing hb₀ hb₁ hA' hB' m).re = m.re ∧
    quadBaseChange hb₀ hb₁ (bcRing hb₀ hb₁ hA' hB' m).imI = m.imI ∧
    quadBaseChange hb₀ hb₁ (bcRing hb₀ hb₁ hA' hB' m).imJ = m.imJ ∧
    quadBaseChange hb₀ hb₁ (bcRing hb₀ hb₁ hA' hB' m).imK = m.imK := by
  have h : quatBaseChange hb₀ hb₁ (a : F) (b : F) (bcRing hb₀ hb₁ hA' hB' m) =
      quatParamEquiv (diag_eq_of_eq hA') (diag_eq_of_eq hB') m :=
    RingEquiv.apply_symm_apply _ _
  exact ⟨congrArg QuaternionAlgebra.re h, congrArg QuaternionAlgebra.imI h, congrArg QuaternionAlgebra.imJ h,
    congrArg QuaternionAlgebra.imK h⟩

theorem fAtR_adeleMap_real (t : Adeles F) (v : {v : InfinitePlace F // v.IsReal})
    (w : {w : InfinitePlace K // w.IsReal}) (hw : w.1.comap (algebraMap F K) = v.1) :
    fAtR w (adeleMap F K t) = fAtR v t := by
  rw [fAtR_apply, adeleMap_fst_fst, fAtR_apply]
  exact congrArg t.1.1 (Subtype.ext hw)

theorem fAtC_adeleMap_real (t : Adeles F) (v : {v : InfinitePlace F // v.IsReal})
    (w : {w : InfinitePlace K // w.IsComplex}) (hw : w.1.comap (algebraMap F K) = v.1) :
    fAtC w (adeleMap F K t) = ((fAtR v t : ℝ) : ℂ) := by
  have hv : (w.1.comap (algebraMap F K)).IsReal := hw ▸ v.2
  rw [fAtC_apply, adeleMap_fst_snd_of_isReal_comap t w hv, fAtR_apply]
  exact congrArg (fun p => ((t.1.1 p : ℝ) : ℂ)) (Subtype.ext hw)

/-- The coordinates of `Θ z` at a real place $w$ of $K$ over the real place $v$ of $F$: $z_v+\delta_w z'_v$. -/
theorem fAtR_quadBaseChange (z : QuadAdele F (d : F)) (v : {v : InfinitePlace F // v.IsReal})
    (w : {w : InfinitePlace K // w.IsReal}) (hw : w.1.comap (algebraMap F K) = v.1) :
    fAtR w (quadBaseChange hb₀ hb₁ z) = fAtR v z.re + embedding_of_isReal w.2 (bK 1) * fAtR v z.im := by
  rw [quadBaseChange_apply, map_add, map_mul, fAtR_adeleMap_real _ v w hw, fAtR_adeleMap_real _ v w hw, fAtR_diag]

/-- The coordinates of `Θ z` at a complex place $w'$ of $K$ over the real place $v$ of $F$. -/
theorem fAtC_quadBaseChange (z : QuadAdele F (d : F)) (v : {v : InfinitePlace F // v.IsReal})
    (w : {w : InfinitePlace K // w.IsComplex}) (hw : w.1.comap (algebraMap F K) = v.1) :
    fAtC w (quadBaseChange hb₀ hb₁ z) =
      ((fAtR v z.re : ℝ) : ℂ) + w.1.embedding (bK 1) * ((fAtR v z.im : ℝ) : ℂ) := by
  rw [quadBaseChange_apply, map_add, map_mul, fAtC_adeleMap_real _ v w hw, fAtC_adeleMap_real _ v w hw, fAtC_diag]

/-- **The transported element at a real place of $F$:** $x=(\Theta^{-1}g_1)_v\in D_E\otimes F_v$. -/
def nsXR (v : {v : InfinitePlace F // v.IsReal}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) : DEre a b d v :=
  (((nsPairR hb₀ hb₁ hA' hB' hA0 hB0 v g : Gnat _ _ _) : (DEre a b d v)ˣ) : DEre a b d v)

/-- **Real places over $v$:** the coordinates of $m$ at $w$ are $\psi_\delta$ of the coordinates of $\Theta^{-1}m$ at $v$. -/
theorem coord_real (m : QuatAdele (F := K) A' B') (v : {v : InfinitePlace F // v.IsReal})
    (w : {w : InfinitePlace K // w.IsReal}) (hw : w.1.comap (algebraMap F K) = v.1) :
    m.re.1.1 w = fAtR v (bcRing hb₀ hb₁ hA' hB' m).re.re +
        embedding_of_isReal w.2 (bK 1) * fAtR v (bcRing hb₀ hb₁ hA' hB' m).re.im ∧
    m.imI.1.1 w = fAtR v (bcRing hb₀ hb₁ hA' hB' m).imI.re +
        embedding_of_isReal w.2 (bK 1) * fAtR v (bcRing hb₀ hb₁ hA' hB' m).imI.im ∧
    m.imJ.1.1 w = fAtR v (bcRing hb₀ hb₁ hA' hB' m).imJ.re +
        embedding_of_isReal w.2 (bK 1) * fAtR v (bcRing hb₀ hb₁ hA' hB' m).imJ.im ∧
    m.imK.1.1 w = fAtR v (bcRing hb₀ hb₁ hA' hB' m).imK.re +
        embedding_of_isReal w.2 (bK 1) * fAtR v (bcRing hb₀ hb₁ hA' hB' m).imK.im := by
  obtain ⟨h1, h2, h3, h4⟩ := quadBaseChange_bcRing hb₀ hb₁ hA' hB' m
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := fAtR_quadBaseChange hb₀ hb₁ (bcRing hb₀ hb₁ hA' hB' m).re v w hw
    rwa [h1] at this
  · have := fAtR_quadBaseChange hb₀ hb₁ (bcRing hb₀ hb₁ hA' hB' m).imI v w hw
    rwa [h2] at this
  · have := fAtR_quadBaseChange hb₀ hb₁ (bcRing hb₀ hb₁ hA' hB' m).imJ v w hw
    rwa [h3] at this
  · have := fAtR_quadBaseChange hb₀ hb₁ (bcRing hb₀ hb₁ hA' hB' m).imK v w hw
    rwa [h4] at this

/-- **Complex place over a real place:** the coordinates of $m$ at $w'$. -/
theorem coord_cx (m : QuatAdele (F := K) A' B') (v : {v : InfinitePlace F // v.IsReal})
    (w : {w : InfinitePlace K // w.IsComplex}) (hw : w.1.comap (algebraMap F K) = v.1) :
    m.re.1.2 w = ((fAtR v (bcRing hb₀ hb₁ hA' hB' m).re.re : ℝ) : ℂ) +
        w.1.embedding (bK 1) * ((fAtR v (bcRing hb₀ hb₁ hA' hB' m).re.im : ℝ) : ℂ) ∧
    m.imI.1.2 w = ((fAtR v (bcRing hb₀ hb₁ hA' hB' m).imI.re : ℝ) : ℂ) +
        w.1.embedding (bK 1) * ((fAtR v (bcRing hb₀ hb₁ hA' hB' m).imI.im : ℝ) : ℂ) ∧
    m.imJ.1.2 w = ((fAtR v (bcRing hb₀ hb₁ hA' hB' m).imJ.re : ℝ) : ℂ) +
        w.1.embedding (bK 1) * ((fAtR v (bcRing hb₀ hb₁ hA' hB' m).imJ.im : ℝ) : ℂ) ∧
    m.imK.1.2 w = ((fAtR v (bcRing hb₀ hb₁ hA' hB' m).imK.re : ℝ) : ℂ) +
        w.1.embedding (bK 1) * ((fAtR v (bcRing hb₀ hb₁ hA' hB' m).imK.im : ℝ) : ℂ) := by
  obtain ⟨h1, h2, h3, h4⟩ := quadBaseChange_bcRing hb₀ hb₁ hA' hB' m
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := fAtC_quadBaseChange hb₀ hb₁ (bcRing hb₀ hb₁ hA' hB' m).re v w hw
    rwa [h1] at this
  · have := fAtC_quadBaseChange hb₀ hb₁ (bcRing hb₀ hb₁ hA' hB' m).imI v w hw
    rwa [h2] at this
  · have := fAtC_quadBaseChange hb₀ hb₁ (bcRing hb₀ hb₁ hA' hB' m).imJ v w hw
    rwa [h3] at this
  · have := fAtC_quadBaseChange hb₀ hb₁ (bcRing hb₀ hb₁ hA' hB' m).imK v w hw
    rwa [h4] at this

/-- The component at a real place $w$ of $K$ of a unit $m$ of $D'\otimes\mathbb A_K$, as a quaternion over $\mathbb R$
(`unitAtR`, with $D'_w=\mathbb H[\mathbb R,w(A'),w(B')]$). -/
def mUnitR (w : {w : InfinitePlace K // w.IsReal}) (m : (QuatAdele (F := K) A' B')ˣ) :
    ℍ[ℝ, embedding_of_isReal w.2 A', embedding_of_isReal w.2 B'] :=
  ((unitAtR A' B' w m : (ℍ[ℝ, embedding_of_isReal w.2 A', embedding_of_isReal w.2 B'])ˣ) :
    ℍ[ℝ, embedding_of_isReal w.2 A', embedding_of_isReal w.2 B'])

/-- The component at a complex place $w$ of $K$ of a unit $m$ of $D'\otimes\mathbb A_K$ (`unitAtC`). -/
def mUnitC (w : {w : InfinitePlace K // w.IsComplex}) (m : (QuatAdele (F := K) A' B')ˣ) :
    ℍ[ℂ, w.1.embedding A', w.1.embedding B'] :=
  ((unitAtC A' B' w m : (ℍ[ℂ, w.1.embedding A', w.1.embedding B'])ˣ) : ℍ[ℂ, w.1.embedding A', w.1.embedding B'])

/-- **Coordinates at a real place $w$ of $K$ over $v$:** $\psi_{\delta_w}(x)$ has the coordinates of $g_1$ at $w$
(`unitAtR`), where $x=(\Theta^{-1}g_1)_v$ and $\psi_s$ is `psiR`. -/
theorem qVec_psiR_nsXR (v : {v : InfinitePlace F // v.IsReal}) (w : {w : InfinitePlace K // w.IsReal})
    (hw : w.1.comap (algebraMap F K) = v.1) {s : ℝ} (hs : embedding_of_isReal w.2 (bK 1) = s)
    (ht : s ^ 2 = embedding_of_isReal v.2 (d : F)) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    qVec (psiR s ht (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)) =
      qVec (mUnitR w (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1) := by
  obtain ⟨h1, h2, h3, h4⟩ := coord_real hb₀ hb₁ hA' hB'
    (((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1 : (QuatAdele (F := K) A' B')ˣ) : QuatAdele (F := K) A' B')
    v w hw
  subst hs
  funext i
  fin_cases i
  · show (psiR _ ht (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)).re = _
    rw [psiR_re, mUnitR, unitAtR_val]; exact h1.symm
  · show (psiR _ ht (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)).imI = _
    rw [psiR_imI, mUnitR, unitAtR_val]; exact h2.symm
  · show (psiR _ ht (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)).imJ = _
    rw [psiR_imJ, mUnitR, unitAtR_val]; exact h3.symm
  · show (psiR _ ht (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)).imK = _
    rw [psiR_imK, mUnitR, unitAtR_val]; exact h4.symm

/-- **Complex place $w'$ over $v$:** $\psi_{\delta_{w'}}(x)$ has the coordinates of $g_1$ at $w'$ (`unitAtC`). -/
theorem qVec_psiC_nsXR (v : {v : InfinitePlace F // v.IsReal}) (w : {w : InfinitePlace K // w.IsComplex})
    (hw : w.1.comap (algebraMap F K) = v.1) {s : ℂ} (hs : w.1.embedding (bK 1) = s)
    (ht : s ^ 2 = ((embedding_of_isReal v.2 (d : F) : ℝ) : ℂ)) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    qVec (psiC s ht (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)) =
      qVec (mUnitC w (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1) := by
  obtain ⟨h1, h2, h3, h4⟩ := coord_cx hb₀ hb₁ hA' hB'
    (((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1 : (QuatAdele (F := K) A' B')ˣ) : QuatAdele (F := K) A' B')
    v w hw
  subst hs
  funext i
  fin_cases i
  · show (psiC _ ht (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)).re = _
    rw [psiC_re, mUnitC, unitAtC_val]; exact h1.symm
  · show (psiC _ ht (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)).imI = _
    rw [psiC_imI, mUnitC, unitAtC_val]; exact h2.symm
  · show (psiC _ ht (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)).imJ = _
    rw [psiC_imJ, mUnitC, unitAtC_val]; exact h3.symm
  · show (psiC _ ht (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)).imK = _
    rw [psiC_imK, mUnitC, unitAtC_val]; exact h4.symm

/-! #### The matrix of `nsR` -/

variable (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0)

/-- $\operatorname{nrd}_K(x)=g_{2,v}$ for $x=(\Theta^{-1}g_1)_v$. -/
theorem nrdK_nsXR (v : {v : InfinitePlace F // v.IsReal}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    nrdK (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g) =
      fAtR v ((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).2 : Adeles F) :=
  nrdK_deMap (fAtR v) (fAtR_diag v (d : F)) (fAtR_diag v (a : F)) (fAtR_diag v (b : F))
    (nsUnit_nrd hb₀ hb₁ hA' hB' hA0 hB0 g)

theorem nrdE_nsXR (v : {v : InfinitePlace F // v.IsReal}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    nrdE (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g) =
      algebraMap ℝ (QE (embedding_of_isReal v.2 (d : F))) (nrdK (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)) :=
  nrdE_eq_nrdK (nsPairR hb₀ hb₁ hA' hB' hA0 hB0 v g).2

/-- `mat (nsR v g)` is the matrix of $\varphi_x$, $x=(\Theta^{-1}g_1)_v$. -/
theorem mat_nsR_eq_toMatrix (v : {v : InfinitePlace F // v.IsReal}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    ArchSOInst.mat _ (nsR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v g) =
      LinearMap.toMatrix' (phiLin (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)) := by
  change ((nsGLR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v g : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) = _
  rw [nsGLR_apply, coe_phiSO]
  rfl

/-- **The real place with $d_v>0$: `nsR` in terms of the coordinates of $g_1$ at the two places of $K$ over $v$.**
With $t=\delta_{w_1}=-\delta_{w_2}$, $r=g_{2,v}$, $X_i$ the $w_i$-coordinates of $g_1$ (`mUnitR`):
$\varphi_v(g)=r^{-1}\,T^{-1}\,(y\mapsto X_1\,y\,\overline{X_2})\,T$. -/
theorem mat_nsR_real (v : {v : InfinitePlace F // v.IsReal}) (hpos : 0 < embedding_of_isReal v.2 (d : F))
    (w₁ w₂ : {w : InfinitePlace K // w.IsReal}) (h₁ : w₁.1.comap (algebraMap F K) = v.1)
    (h₂ : w₂.1.comap (algebraMap F K) = v.1) {t : ℝ} (ht1 : embedding_of_isReal w₁.2 (bK 1) = t)
    (ht2 : embedding_of_isReal w₂.2 (bK 1) = -t) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    ArchSOInst.mat _ (nsR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v g) =
      (fAtR v ((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).2 : Adeles F))⁻¹ •
        (NSArch.tInv t *
          sqMat (vecQ (qVec (mUnitR w₁ (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1)) :
              ℍ[ℝ, embedding_of_isReal v.2 (a : F), embedding_of_isReal v.2 (b : F)])
            (star (vecQ (qVec (mUnitR w₂ (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1)) :
              ℍ[ℝ, embedding_of_isReal v.2 (a : F), embedding_of_isReal v.2 (b : F)])) *
          NSArch.tMat t) := by
  have ht : t ^ 2 = embedding_of_isReal v.2 (d : F) := ht1 ▸ embedding_of_isReal_delta_sq bK hb₁ v w₁ h₁
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at ht
    exact hpos.ne ht
  rw [← qVec_psiR_nsXR hb₀ hb₁ hA' hB' hA0 hB0 v w₁ h₁ ht1 ht g,
    ← qVec_psiR_nsXR hb₀ hb₁ hA' hB' hA0 hB0 v w₂ h₂ ht2 (neg_sq_eq ht) g, vecQ_qVec, vecQ_qVec,
    mat_nsR_eq_toMatrix hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0, toMatrix'_phiLin_real ht0 ht,
    nrdK_nsXR hb₀ hb₁ hA' hB' hA0 hB0]

/-- **The real place with $d_v<0$: `nsR` in terms of the coordinate of $g_1$ at the complex place $w'$ over $v$.**
With $s=\delta_{w'}$ ($s^2=d_v$, $\operatorname{Re}s=0$), $r=g_{2,v}$, $X$ the $w'$-coordinates of $g_1$ (`mUnitC`):
$\varphi_v(g)=r^{-1}\,$`MR s X`. -/
theorem mat_nsR_cx (v : {v : InfinitePlace F // v.IsReal}) (w : {w : InfinitePlace K // w.IsComplex})
    (hw : w.1.comap (algebraMap F K) = v.1) {s : ℂ} (hs : w.1.embedding (bK 1) = s) (htre : s.re = 0)
    (ht : s ^ 2 = ((embedding_of_isReal v.2 (d : F) : ℝ) : ℂ)) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    ArchSOInst.mat _ (nsR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v g) =
      (fAtR v ((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).2 : Adeles F))⁻¹ •
        NSArch.MR (A := embedding_of_isReal v.2 (a : F)) (B := embedding_of_isReal v.2 (b : F)) s
          (vecQ (qVec (mUnitC w (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1))) := by
  have ht0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at ht
    have h1 : embedding_of_isReal v.2 (d : F) = 0 := Complex.ofReal_eq_zero.1 ht.symm
    exact hd0 ((map_eq_zero _).1 h1)
  rw [← qVec_psiC_nsXR hb₀ hb₁ hA' hB' hA0 hB0 v w hw hs ht g, vecQ_qVec,
    mat_nsR_eq_toMatrix hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0, toMatrix'_phiLin_cx ht0 htre ht,
    nrdK_nsXR hb₀ hb₁ hA' hB' hA0 hB0]

/-! #### Normalization to the sphere: `phiSplit` and `phiNS` -/

open SphereLeray SphereLerayC in
/-- **$d_v>0$:** for $r=g_{2,v}>0$, `nsR v g` is `phiSplit` of the normalized sphere points
$x_i=\sqrt r^{-1}\,\mathrm{qVec}(X_i)$, $X_i$ the $w_i$-coordinates of $g_1$ (`mUnitR`). -/
theorem mat_nsR_eq_phiSplit (v : {v : InfinitePlace F // v.IsReal})
    (w₁ w₂ : {w : InfinitePlace K // w.IsReal}) (h₁ : w₁.1.comap (algebraMap F K) = v.1)
    (h₂ : w₂.1.comap (algebraMap F K) = v.1) {t : ℝ} (ht1 : embedding_of_isReal w₁.2 (bK 1) = t)
    (ht2 : embedding_of_isReal w₂.2 (bK 1) = -t) (ht0 : t ≠ 0) (ht : t ^ 2 = embedding_of_isReal v.2 (d : F))
    (g : (gnatBC bK 0 hb₀ hA0 hB0).G)
    (hr : 0 < fAtR v ((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).2 : Adeles F)) :
    ∃ x₁ x₂ : Sph (NSArch.normForm (embedding_of_isReal v.2 (a : F)) (embedding_of_isReal v.2 (b : F))) 1,
      (x₁ : Fin 4 → ℝ) = (Real.sqrt (fAtR v ((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).2 : Adeles F)))⁻¹ •
        qVec (mUnitR w₁ (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1) ∧
      (x₂ : Fin 4 → ℝ) = (Real.sqrt (fAtR v ((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).2 : Adeles F)))⁻¹ •
        qVec (mUnitR w₂ (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1) ∧
      ArchSOInst.mat _ (nsR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v g) =
        ArchSOInst.mat _ (NSArch.phiSplit ht0 ht (x₁, x₂)) := by
  set u := fAtR v ((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).2 : Adeles F) with hu
  have hpos : 0 < embedding_of_isReal v.2 (d : F) := by rw [← ht]; positivity
  have e1 := qVec_psiR_nsXR hb₀ hb₁ hA' hB' hA0 hB0 v w₁ h₁ ht1 ht g
  have e2 := qVec_psiR_nsXR hb₀ hb₁ hA' hB' hA0 hB0 v w₂ h₂ ht2 (neg_sq_eq ht) g
  have hn1 : nrd (psiR t ht (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)) = u := by
    have := nrd_psi (RingHom.id ℝ) t ht rfl rfl (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g) _
      (nrdE_nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)
    rw [nrdK_nsXR] at this
    exact this
  have hn2 : nrd (psiR (-t) (neg_sq_eq ht) (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)) = u := by
    have := nrd_psi (RingHom.id ℝ) (-t) (neg_sq_eq ht) rfl rfl (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g) _
      (nrdE_nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)
    rw [nrdK_nsXR] at this
    exact this
  let x₁ : Sph (NSArch.normForm (embedding_of_isReal v.2 (a : F)) (embedding_of_isReal v.2 (b : F))) 1 :=
    ⟨(Real.sqrt u)⁻¹ • qVec (psiR t ht (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)), eval_normForm_sqrt_inv _ hr hn1⟩
  let x₂ : Sph (NSArch.normForm (embedding_of_isReal v.2 (a : F)) (embedding_of_isReal v.2 (b : F))) 1 :=
    ⟨(Real.sqrt u)⁻¹ • qVec (psiR (-t) (neg_sq_eq ht) (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)),
      eval_normForm_sqrt_inv _ hr hn2⟩
  have hx₁ : (x₁ : Fin 4 → ℝ) = (Real.sqrt u)⁻¹ • qVec (mUnitR w₁ (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1) :=
    congrArg ((Real.sqrt u)⁻¹ • ·) e1
  have hx₂ : (x₂ : Fin 4 → ℝ) = (Real.sqrt u)⁻¹ • qVec (mUnitR w₂ (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1) :=
    congrArg ((Real.sqrt u)⁻¹ • ·) e2
  refine ⟨x₁, x₂, hx₁, hx₂, ?_⟩
  have hcc : (Real.sqrt u)⁻¹ * (Real.sqrt u)⁻¹ = u⁻¹ := by rw [← mul_inv, Real.mul_self_sqrt hr.le]
  rw [mat_nsR_real hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v hpos w₁ w₂ h₁ h₂ ht1 ht2 g, NSArch.mat_phiSplit, hx₁, hx₂,
    vecQ_smul, vecQ_smul, star_smul_quat, sqMat_smul_smul, Matrix.mul_smul, Matrix.smul_mul, hcc]

open SphereLeray SphereLerayC in
/-- **$d_v<0$:** for $r=g_{2,v}>0$, `nsR v g` is `phiNS` of the normalized sphere point
$x=\sqrt r^{-1}\,\mathrm{qVec}(X)$, $X$ the $w'$-coordinates of $g_1$ (`mUnitC`). -/
theorem mat_nsR_eq_phiNS (v : {v : InfinitePlace F // v.IsReal}) (w : {w : InfinitePlace K // w.IsComplex})
    (hw : w.1.comap (algebraMap F K) = v.1) {s : ℂ} (hs : w.1.embedding (bK 1) = s) (htre : s.re = 0)
    (ht : s ^ 2 = ((embedding_of_isReal v.2 (d : F) : ℝ) : ℂ)) (ht0 : s ≠ 0) (g : (gnatBC bK 0 hb₀ hA0 hB0).G)
    (hr : 0 < fAtR v ((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).2 : Adeles F)) :
    ∃ x : SphC (NSArch.normForm ((embedding_of_isReal v.2 (a : F) : ℝ) : ℂ)
        ((embedding_of_isReal v.2 (b : F) : ℝ) : ℂ)) 1,
      (x : Fin 4 → ℂ) = (((Real.sqrt (fAtR v ((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).2 : Adeles F)))⁻¹ : ℝ) : ℂ) •
        qVec (mUnitC w (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1) ∧
      ArchSOInst.mat _ (nsR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v g) =
        ArchSOInst.mat _ (NSArch.phiNS (A := embedding_of_isReal v.2 (a : F)) (B := embedding_of_isReal v.2 (b : F))
          ht htre ht0 x) := by
  set u := fAtR v ((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).2 : Adeles F) with hu
  have e1 := qVec_psiC_nsXR hb₀ hb₁ hA' hB' hA0 hB0 v w hw hs ht g
  have hn : nrd (psiC s ht (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)) = (u : ℂ) := by
    have := nrd_psi Complex.ofRealHom s ht rfl rfl (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g) _
      (nrdE_nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)
    rw [nrdK_nsXR] at this
    exact this
  let x : SphC (NSArch.normForm ((embedding_of_isReal v.2 (a : F) : ℝ) : ℂ)
      ((embedding_of_isReal v.2 (b : F) : ℝ) : ℂ)) 1 :=
    ⟨(((Real.sqrt u)⁻¹ : ℝ) : ℂ) • qVec (psiC s ht (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)),
      eval_normForm_sqrt_inv_cx _ hr hn⟩
  have hx : (x : Fin 4 → ℂ) = (((Real.sqrt u)⁻¹ : ℝ) : ℂ) •
      qVec (mUnitC w (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1) :=
    congrArg ((((Real.sqrt u)⁻¹ : ℝ) : ℂ) • ·) e1
  refine ⟨x, hx, ?_⟩
  have hcc : (Real.sqrt u)⁻¹ * (Real.sqrt u)⁻¹ = u⁻¹ := by rw [← mul_inv, Real.mul_self_sqrt hr.le]
  rw [mat_nsR_cx hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v w hw hs htre ht g, NSArch.mat_phiNS, hx, vecQ_smul,
    MR_smul_real, hcc]

end Global

/-! ### The forms -/

section Forms

variable {F : Type} [Field F] [NumberField F]

/-- $Q_{\mathrm{ns}}(a,b,d)^{\sigma_v}=\langle1,-a_vd_v,-b_vd_v,a_vb_vd_v\rangle$ = `NSArch.nsFormR`. -/
theorem QRe_qNS (a b d : 𝓞 F) (v : {v : InfinitePlace F // v.IsReal}) :
    QRe (qNS a b d) v = NSArch.nsFormR (embedding_of_isReal v.2 (a : F)) (embedding_of_isReal v.2 (b : F))
      (embedding_of_isReal v.2 (d : F)) := by
  rw [NSArch.nsFormR_eq_diag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qNS, QuadForm.diag, QuadForm.map]

/-- $Q_{\mathrm{sq}}(\alpha,\beta)^{\sigma_w}=\langle1,-\alpha_w,-\beta_w,\alpha_w\beta_w\rangle$ = `NSArch.normForm`. -/
theorem QRe_qSq (α β : 𝓞 F) (w : {w : InfinitePlace F // w.IsReal}) :
    QRe (qSq α β) w = NSArch.normForm (embedding_of_isReal w.2 (α : F)) (embedding_of_isReal w.2 (β : F)) := by
  rw [NSArch.normForm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qSq, QuadForm.diag, QuadForm.map]

end Forms

end QuadFormsKB.Tamagawa.Measure.Weil
