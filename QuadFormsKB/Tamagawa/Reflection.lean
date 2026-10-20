/-
# Reflections and improper isometries

**Layer:** forms `QuadForm A n` over a commutative ring, then a DVR, a field, and a number field with its
completions.

**Defines** `QuadForm.reflMat x w` $= 1 - x w^{\mathsf T}$, i.e. $\tau(y) = y - (w \cdot y)\,x$. When
$H_Q x = Q(x)\,w$ (so $w = H_Qx/Q(x)$ and $w \cdot y = B(x, y)/Q(x)$) this is the **reflection (symmetry) in $x$**,
$\tau_x(y) = y - \frac{B(x,y)}{Q(x)}x$ with $B(x, y) = x^{\mathsf T}H_Q y$ (O'Meara 1963, §42 [unverified]).

**Proves**
* `QuadForm.eval_reflMat`, `QuadForm.compMat_reflMat`: $Q(\tau y) = Q(y)$, i.e. $Q \circ \tau = Q$, over **any**
  commutative ring (no division by $2$ or by $Q(x)$ is needed once $w$ is given);
* `QuadForm.det_reflMat`: $\det\tau = 1 - w\cdot x = -1$ over a domain with $Q(x) \ne 0$;
* `QuadForm.exists_refl_data_field` / `QuadForm.exists_refl_data_dvr`: such $(x, w)$ exist for a nondegenerate
  $Q$ in $n \ge 1$ variables over a field, and over a DVR **with $w$ integral** (take $x$ with $\mathrm{ord}\,Q(x)$
  minimal; then $Q(x) \mid Q(z)$ for all $z$, so $Q(x) \mid B(x, y) = Q(x + y) - Q(x) - Q(y)$). This works at every
  prime, dyadic included;
* number fields (`Lattices` setting, $Q = Q_0 \otimes F$ for $Q_0$ over $\mathcal O_F$): an improper rational
  isometry (`exists_orthGroup_det_neg_one`) and, at every finite $\mathfrak p$, an improper element of
  $O(V)(\mathfrak o_\mathfrak p)$ = `stdStab` (`exists_stdStab_det_neg_one`). Hence $[O : SO] = 2$ for $O(V)(F)$ and for
  $O(\mathfrak o_\mathfrak p^n)$, and $O(V)(\mathbb A_f) = SO(V)(\mathbb A_f)\cdot O(\hat{\mathcal O}_F^n)$ (`MassFormula.lean`).
**Depends on** `FormDensitySelf.lean` (`compMat`, `eq_of_eval_eq`), `Lattices/FreeBridge.lean`.
-/
import QuadFormsKB.LocalDensity.FormDensitySelf
import QuadFormsKB.LocalDensity.NFBridge
import QuadFormsKB.Lattices.Forms
import QuadFormsKB.Lattices.FreeBridge

open Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.QuadForm

variable {A : Type*} [CommRing A] {n : ℕ}

/-- **The reflection matrix** $\tau = 1 - x w^{\mathsf T}$, $\tau y = y - (w\cdot y)\,x$. With $H_Q x = Q(x)\,w$ it is the
symmetry of $(A^n, Q)$ in the vector $x$ (O'Meara 1963, §42 [unverified]). -/
@[kb "omeara1963" "§42 (symmetries) [unverified]"]
def reflMat (x w : Fin n → A) : Matrix (Fin n) (Fin n) A := 1 - vecMulVec x w

theorem reflMat_mulVec (x w y : Fin n → A) : reflMat x w *ᵥ y = y - (w ⬝ᵥ y) • x := by
  rw [reflMat, sub_mulVec, one_mulVec]
  congr 1
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem hessian_transpose (Q : QuadForm A n) : Q.hessianᵀ = Q.hessian := by
  simp [hessian, add_comm]

/-- **The reflection preserves $Q$:** if $H_Q x = Q(x)\,w$ then $Q(\tau y) = Q(y)$ for every $y$. *Proof:*
$Q(y - cx) = Q(y) - c\,B(x, y) + c^2Q(x)$ and $B(x, y) = (H_Qx)\cdot y = Q(x)\,(w\cdot y) = Q(x)\,c$. -/
@[kb "omeara1963" "§42 [unverified]"]
theorem eval_reflMat (Q : QuadForm A n) {x w : Fin n → A} (hw : Q.hessian *ᵥ x = Q.eval x • w)
    (y : Fin n → A) : Q.eval (reflMat x w *ᵥ y) = Q.eval y := by
  rw [reflMat_mulVec]
  set c := w ⬝ᵥ y
  have hB : y ⬝ᵥ (Q.hessian *ᵥ x) = Q.eval x * c := by
    rw [hw, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  have hpol := eval_polar Q y (-(c • x))
  have hsm : Q.eval (-(c • x)) = c ^ 2 * Q.eval x := by
    rw [eval_eq_dotProduct', eval_eq_dotProduct']
    simp only [mulVec_neg, mulVec_smul, dotProduct_neg, neg_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    ring
  rw [sub_eq_add_neg]
  have : Q.eval (y + -(c • x)) = Q.eval y + Q.eval (-(c • x)) + y ⬝ᵥ (Q.hessian *ᵥ -(c • x)) := by
    rw [← hpol]; ring
  rw [this, hsm, mulVec_neg, mulVec_smul, dotProduct_neg, dotProduct_smul, hB, smul_eq_mul]
  ring

/-- **$Q \circ \tau = Q$** for the reflection data $H_Q x = Q(x)\,w$. -/
theorem compMat_reflMat (Q : QuadForm A n) {x w : Fin n → A} (hw : Q.hessian *ᵥ x = Q.eval x • w) :
    Q.compMat (reflMat x w) = Q :=
  eq_of_eval_eq fun y => by rw [eval_compMat, eval_reflMat Q hw]

/-- **The reflection is improper:** $\det\tau = 1 - w\cdot x = -1$, since $Q(x)(w\cdot x) = x^{\mathsf T}H_Qx = 2Q(x)$
(over a domain, $Q(x) \ne 0$). -/
@[kb "omeara1963" "§42 [unverified]"]
theorem det_reflMat [IsDomain A] (Q : QuadForm A n) {x w : Fin n → A}
    (hw : Q.hessian *ᵥ x = Q.eval x • w) (hx : Q.eval x ≠ 0) : (reflMat x w).det = -1 := by
  have hwx : w ⬝ᵥ x = 2 := by
    have h := dotProduct_hessian_self Q x
    rw [hw, dotProduct_smul, smul_eq_mul, dotProduct_comm] at h
    have : Q.eval x * (w ⬝ᵥ x - 2) = 0 := by rw [mul_sub, h]; ring
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hx
    · exact sub_eq_zero.mp h'
  have : reflMat x w = 1 - replicateCol Unit x * replicateRow Unit w := by
    rw [reflMat, vecMulVec_eq Unit]
  rw [this, det_one_sub_mul_comm, det_unique, Matrix.sub_apply, Matrix.one_apply_eq,
    replicateRow_mul_replicateCol_apply, hwx]
  norm_num

/-- A nondegenerate form in $n \ge 1$ variables takes a nonzero value: otherwise $x^{\mathsf T}H_Q y = 0$ for all
$x, y$ (polarization), so $H_Q = 0$. -/
theorem exists_eval_ne_zero [Nontrivial A] (Q : QuadForm A n) (hQ : Q.Nondegenerate) (hn : 0 < n) :
    ∃ x, Q.eval x ≠ 0 := by
  by_contra h
  push Not at h
  apply hQ
  have hH : Q.hessian = 0 := by
    ext i j
    have := eval_polar Q (Pi.single i 1) (Pi.single j 1)
    rw [h, h, h, mulVec_single_one, single_one_dotProduct] at this
    simpa using this.symm
  rw [hH]
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact det_zero

/-- **Reflection data over a field:** a nondegenerate $Q$ in $n \ge 1$ variables has $x$ with $Q(x) \ne 0$, and
$w = Q(x)^{-1}H_Qx$. -/
theorem exists_refl_data_field {K : Type*} [Field K] (Q : QuadForm K n) (hQ : Q.Nondegenerate) (hn : 0 < n) :
    ∃ x w : Fin n → K, Q.eval x ≠ 0 ∧ Q.hessian *ᵥ x = Q.eval x • w := by
  obtain ⟨x, hx⟩ := exists_eval_ne_zero Q hQ hn
  exact ⟨x, (Q.eval x)⁻¹ • (Q.hessian *ᵥ x), hx, by rw [smul_smul, mul_inv_cancel₀ hx, one_smul]⟩

/-- **Reflection data over a DVR, with $w$ integral:** choose $x$ with $Q(x) \ne 0$ of minimal valuation; then $Q(x)$
divides every value of $Q$, hence every $B(x, e_j) = Q(x + e_j) - Q(x) - Q(e_j) = (H_Qx)_j$. Valid at every prime,
dyadic included (O'Meara 1963, 91:? [unverified]: every lattice has a symmetry). -/
theorem exists_refl_data_dvr {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (Q : QuadForm R n) (hQ : Q.Nondegenerate) (hn : 0 < n) :
    ∃ x w : Fin n → R, Q.eval x ≠ 0 ∧ Q.hessian *ᵥ x = Q.eval x • w := by
  classical
  set S : Set (Fin n → R) := {x | Q.eval x ≠ 0}
  have hS : S.Nonempty := exists_eval_ne_zero Q hQ hn
  let f : (Fin n → R) → ℕ∞ := fun x => IsDiscreteValuationRing.addVal R (Q.eval x)
  set x := Function.argminOn f S hS
  have hx : x ∈ S := Function.argminOn_mem f S hS
  have hdvd : ∀ z, Q.eval x ∣ Q.eval z := by
    intro z
    by_cases hz : Q.eval z = 0
    · rw [hz]; exact dvd_zero _
    · rw [← IsDiscreteValuationRing.addVal_le_iff_dvd]
      exact Function.argminOn_le f S hz
  have hcol : ∀ j, Q.eval x ∣ (Q.hessian *ᵥ x) j := by
    intro j
    have h := eval_polar Q (Pi.single j 1) x
    rw [single_one_dotProduct] at h
    rw [← h]
    exact dvd_sub (dvd_sub (hdvd _) (hdvd _)) (hdvd _)
  choose w hw using hcol
  exact ⟨x, w, hx, by ext j; rw [Pi.smul_apply, smul_eq_mul, ← hw j]⟩

end QuadFormsKB.QuadForm

namespace QuadFormsKB.Tamagawa

open NumberField IsDedekindDomain Lattices

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

/-- **An improper rational isometry:** for a nondegenerate $Q$ on $F^n$, $n \ge 1$, some $\gamma \in O(V)(F)$ has
$\det\gamma = -1$ (a reflection in an anisotropic vector). So $[O(V)(F) : SO(V)(F)] = 2$. -/
@[kb "omeara1963" "§42–43 [unverified]"]
theorem exists_orthGroup_det_neg_one (Q : QuadForm F n) (hQ : Q.Nondegenerate) (hn : 0 < n) :
    ∃ γ : orthGroup Q F, (γ : GL (Fin n) F).val.det = -1 := by
  obtain ⟨x, w, hx, hw⟩ := QuadForm.exists_refl_data_field Q hQ hn
  have hdet := QuadForm.det_reflMat Q hw hx
  let γ : GL (Fin n) F := Matrix.nonsingInvUnit (QuadForm.reflMat x w) (by rw [hdet]; exact isUnit_one.neg)
  exact ⟨⟨γ, mem_orthGroup_of_eval Q fun z => QuadForm.eval_reflMat Q hw z⟩, hdet⟩

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- Values of $Q_0 \otimes F$ on $\mathfrak o_\mathfrak p^n$ are the values of $Q_0 \otimes \mathfrak o_\mathfrak p$. -/
theorem evalIn_coe_o (Q₀ : QuadForm (𝓞 F) n) (y : Fin n → 𝔬) :
    (Q₀.map (algebraMap (𝓞 F) F)).evalIn Fv (fun i => (y i : Fv)) =
      (((LocalDensity.NF.Qp v Q₀).eval y : 𝔬) : Fv) := by
  rw [evalIn_eq_eval_map]
  have e : (Q₀.map (algebraMap (𝓞 F) F)).map (algebraMap F Fv) =
      (LocalDensity.NF.Qp v Q₀).map (algebraMap 𝔬 Fv) := by
    rw [QuadForm.map_map, QuadForm.map_map]
    congr 1
  rw [e]
  exact eval_map_comp (algebraMap 𝔬 Fv) _ y

/-- **An improper local isometry of $\mathfrak o_\mathfrak p^n$** at **every** finite prime $\mathfrak p$ (dyadic included):
for $Q_0$ over $\mathcal O_F$ nondegenerate, $n \ge 1$, the group $O(V)(\mathfrak o_\mathfrak p)$ (`stdStab`, the stabilizer of
$\mathfrak o_\mathfrak p^n$ in $O(V)(F_\mathfrak p)$, $V = (F^n, Q_0 \otimes F)$) contains an element of determinant $-1$: the
reflection in a vector $x \in \mathfrak o_\mathfrak p^n$ with $\mathrm{ord}\,Q(x)$ minimal (`QuadForm.exists_refl_data_dvr`). -/
@[kb "omeara1963" "§91–92 (symmetries of lattices) [unverified]"]
theorem exists_stdStab_det_neg_one (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hn : 0 < n) :
    ∃ g : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv, g ∈ stdStab (Q₀.map (algebraMap (𝓞 F) F)) v ∧
      (g : GL (Fin n) Fv).val.det = -1 := by
  set Q := Q₀.map (algebraMap (𝓞 F) F)
  obtain ⟨x, w, hx, hw⟩ := QuadForm.exists_refl_data_dvr (LocalDensity.NF.Qp v Q₀)
    (LocalDensity.NF.nondegenerate_Qp v hQ) hn
  have hdet := QuadForm.det_reflMat _ hw hx
  let P₀ : GL (Fin n) 𝔬 := Matrix.nonsingInvUnit (QuadForm.reflMat x w) (by rw [hdet]; exact isUnit_one.neg)
  let g : GL (Fin n) Fv := Matrix.GeneralLinearGroup.map (algebraMap 𝔬 Fv) P₀
  have hgval : g.val = (QuadForm.reflMat x w).map (algebraMap 𝔬 Fv) := rfl
  have hmem : g ∈ orthGroup Q Fv := by
    refine mem_orthGroup_of_evalIn Q fun z => ?_
    refine evalIn_eq_of_evalIn_o v (A := fun z => Q.evalIn Fv (g.val *ᵥ z)) (B := Q.evalIn Fv)
      (fun c y => by simp only [mulVec_smul]; exact evalIn_smul' Q c _) (fun c y => evalIn_smul' Q c y)
      (fun y => ?_) z
    have e1 : g.val *ᵥ (fun i => (y i : Fv)) = fun i => ((QuadForm.reflMat x w *ᵥ y) i : Fv) := by
      funext i
      rw [hgval]
      exact (RingHom.map_mulVec (algebraMap 𝔬 Fv) _ y i).symm
    rw [e1, evalIn_coe_o v, evalIn_coe_o v, QuadForm.eval_reflMat _ hw]
  refine ⟨⟨g, hmem⟩, locAct_map_std v P₀, ?_⟩
  show g.val.det = -1
  rw [hgval, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet]
  simp

end QuadFormsKB.Tamagawa
