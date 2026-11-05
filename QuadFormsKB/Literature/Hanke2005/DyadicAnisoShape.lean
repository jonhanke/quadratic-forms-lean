/-
# The anisotropic maximal kernel at a dyadic place: its shapes

Continuation of `DyadicAnisoKernel.lean`. $R$ is a complete discrete valuation ring with finite residue field $\mathbb F$,
uniformizer $\pi \mid 2$ and $2 \ne 0$; $Q$ is anisotropic on $R^n$, $\overline W\subseteq\mathbb F^n$ its residue zero space
($n - 2 \le \dim\overline W \le 2$, `le_finrank_resZeroSub_add_two`, `finrank_resZeroSub_le_two`).

* `exists_shape_top`: if $\dim\overline W = m$ and $n = m+2$, then $Q\simeq M\perp T$ with $T$ a unimodular binary form,
  $\bar T$ anisotropic, and every value of $M$ divisible by $\pi$.
* `exists_shape_bottom`: if $\dim\overline W = 2$, $n = m + 2$, and $\pi^2\mid Q(x)\Rightarrow\pi\mid x$ (maximality), then
  $Q\simeq M\perp\pi S$ with $S$ unimodular binary and $\bar S$ anisotropic.

These are the lattice shapes of Shimura 1999, §3.2 ($t = 3$: $\mathfrak g\zeta + \mathfrak r\omega$; $t = 4$:
$\mathfrak O = \mathfrak r + \mathfrak r\omega$) and of Gan–Hanke–Yu 2001, (6.5), (6.10), obtained here without the
classification of the anisotropic spaces: only the norm inequality and Chevalley–Warning over $\mathbb F$ are used.
-/
import QuadFormsKB.Literature.Hanke2005.DyadicAnisoKernel

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadForm

section Shape

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Finite (IsLocalRing.ResidueField R)]

local notation "𝔽" => IsLocalRing.ResidueField R
local notation "res" => IsLocalRing.residue R

variable {π : R} (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0)

include hπ h2 in
/-- **A binary form with anisotropic residue form has a unit cross coefficient** (residue characteristic $2$: otherwise
$\bar T = \bar a x^2 + \bar c y^2$ vanishes at $(t, \bar a)$ with $t^2 = \bar a\bar c$, or at $(1,0)$ if $\bar a = 0$). -/
theorem not_dvd_coeff01_of_aniso (T : QuadForm R 2) (haniso : ∀ s : Fin 2 → R, π ∣ T.eval s → ∀ i, π ∣ s i) :
    ¬ π ∣ T.coeff 0 1 := by
  intro hb
  have h2F : (2 : 𝔽) = 0 := by rw [← map_ofNat res 2, res_eq_zero_iff' hπ]; exact h2
  have hb' : res (T.coeff 0 1) = 0 := (res_eq_zero_iff' hπ _).2 hb
  by_cases ha : π ∣ T.coeff 0 0
  · have h := haniso ![1, 0] (by rw [Tamagawa.eval_binary]; simpa using ha) 0
    exact hπ.not_isUnit (isUnit_of_dvd_one (by simpa using h))
  · obtain ⟨t, ht⟩ := (Tamagawa.sq_bijective_of_two_eq_zero h2F).2 (res (T.coeff 0 0) * res (T.coeff 1 1))
    obtain ⟨t', rfl⟩ := IsLocalRing.residue_surjective t
    have ht' : res t' ^ 2 = res (T.coeff 0 0) * res (T.coeff 1 1) := ht
    have h := haniso ![t', T.coeff 0 0] ?_ 1
    · exact ha (by simpa using h)
    · rw [← res_eq_zero_iff' hπ, Tamagawa.eval_binary]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_mul, hb']
      linear_combination (res (T.coeff 0 0)) * ht' + (res (T.coeff 0 0)) ^ 2 * res (T.coeff 1 1) * h2F

include hπ h2 in
/-- A binary form with anisotropic residue form is unimodular. -/
theorem isUnit_det_of_aniso (T : QuadForm R 2) (haniso : ∀ s : Fin 2 → R, π ∣ T.eval s → ∀ i, π ∣ s i) :
    IsUnit T.hessian.det :=
  Tamagawa.isUnit_det_hessian_binary hπ h2 T (not_dvd_coeff01_of_aniso hπ h2 T haniso)

omit [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Finite (IsLocalRing.ResidueField R)] in
theorem inv_mulVec_cancel {n : ℕ} {U : Matrix (Fin n) (Fin n) R} (hU : IsUnit U.det) (x : Fin n → R) :
    U⁻¹ *ᵥ (U *ᵥ x) = x := by
  rw [mulVec_mulVec, nonsing_inv_mul _ hU, one_mulVec]

/-- Anisotropy is invariant under $\mathrm{GL}_n(R)$. -/
theorem aniso_of_isGLEquiv {n : ℕ} {Q Q' : QuadForm R n} (h : DVR.IsGLEquiv Q Q')
    (han : ∀ x, Q.eval x = 0 → x = 0) : ∀ x, Q'.eval x = 0 → x = 0 := by
  obtain ⟨U, hU, hUe⟩ := h
  intro x hx
  rw [hUe] at hx
  rw [← inv_mulVec_cancel hU x, han _ hx, mulVec_zero]

/-- The maximality condition $\pi^2\mid Q(x)\Rightarrow\pi\mid x$ is invariant under $\mathrm{GL}_n(R)$. -/
theorem hmax_of_isGLEquiv {n : ℕ} {Q Q' : QuadForm R n} (h : DVR.IsGLEquiv Q Q')
    (hmax : ∀ x : Fin n → R, π ^ 2 ∣ Q.eval x → ∀ i, π ∣ x i) :
    ∀ x : Fin n → R, π ^ 2 ∣ Q'.eval x → ∀ i, π ∣ x i := by
  obtain ⟨U, hU, hUe⟩ := h
  intro x hx i
  rw [hUe] at hx
  have hd := hmax _ hx
  rw [← inv_mulVec_cancel hU x]
  simp only [mulVec, dotProduct]
  exact Finset.dvd_sum fun l _ => dvd_mul_of_dvd_right (hd l) _

theorem eval_orthSum_append {m k : ℕ} (A : QuadForm R m) (B : QuadForm R k) (y : Fin m → R) (t : Fin k → R) :
    (orthSum A B).eval (Fin.append y t) = A.eval y + B.eval t := by
  rw [QuadForm.eval, evalIn_orthSum]
  simp [QuadForm.eval]

include hπ h2 h20 in
/-- **The top shape:** if $\dim\overline W = m$ for $Q$ of rank $m+2$, then $Q\simeq M\perp T$ with $T$ unimodular binary,
$\bar T$ anisotropic, and every value of $M$ divisible by $\pi$ (a complement of $\overline W$ lifts to $T$; the residue zero
space of $M\perp T$ has dimension $\ge m$ and meets the $T$-coordinates trivially, so it is the $M$-coordinate space). -/
@[kb "omeara1963" "§91C, 91:9 (a unimodular component splits off); Shimura 1999, Lemma 3.8 (proof)"]
theorem exists_shape_top {m : ℕ} (Q : QuadForm R (m + 2)) (han : ∀ x, Q.eval x = 0 → x = 0)
    (hs : Module.finrank 𝔽 (resZeroSub hπ h2 h20 Q han) = m) :
    ∃ (M : QuadForm R m) (T : QuadForm R 2), IsUnit T.hessian.det ∧
      (∀ s : Fin 2 → R, π ∣ T.eval s → ∀ i, π ∣ s i) ∧ (∀ y, π ∣ M.eval y) ∧ DVR.IsGLEquiv Q (orthSum M T) := by
  classical
  set W := resZeroSub hπ h2 h20 Q han with hW
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  have hdim := Submodule.finrank_add_eq_of_isCompl hC
  rw [Module.finrank_fin_fun] at hdim
  have hC2 : Module.finrank 𝔽 C = 2 := by omega
  set b := Module.finBasisOfFinrankEq 𝔽 C hC2 with hb
  set c : Fin 2 → Fin (m + 2) → 𝔽 := fun j => (b j : Fin (m + 2) → 𝔽) with hc
  choose x hx using fun j => res_surj_vec (c j)
  set X : Matrix (Fin (m + 2)) (Fin 2) R := colMat x with hX
  set T := Q.compMat X with hT
  have hTaniso : ∀ s : Fin 2 → R, π ∣ T.eval s → ∀ i, π ∣ s i := by
    intro s hs i
    rw [hT, eval_compMat, hX, colMat_mulVec, ← res_eq_zero_iff' hπ, ← eval_map_res] at hs
    have e : (fun l => res ((∑ j, s j • x j) l)) = ∑ j, res (s j) • c j := by
      funext l; simp [Finset.sum_apply, ← hx]
    rw [e] at hs
    have hmemC : (∑ j, res (s j) • c j) ∈ C := C.sum_mem fun j _ => C.smul_mem _ (b j).2
    have h0 : (∑ j, res (s j) • c j) = 0 := (Submodule.disjoint_def.mp hC.disjoint) _ hs hmemC
    have hli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have := hli (fun j => res (s j)) (Subtype.ext (by simpa [hc] using h0)) i
    exact (res_eq_zero_iff' hπ _).1 this
  have hTu : IsUnit T.hessian.det := isUnit_det_of_aniso hπ h2 T hTaniso
  obtain ⟨M, hM⟩ := exists_split_unimodular Q X (by rw [← hessian_compMat]; exact hTu)
  refine ⟨M, T, hTu, hTaniso, ?_, hM⟩
  -- the residue zero space of `Q₂ = M ⊥ T`
  set Q₂ := orthSum M T with hQ₂
  have han₂ := aniso_of_isGLEquiv hM han
  set W₂ := resZeroSub hπ h2 h20 Q₂ han₂ with hW₂
  have hge : m + 2 ≤ Module.finrank 𝔽 W₂ + 2 := le_finrank_resZeroSub_add_two hπ h2 h20 Q₂ han₂
  -- elements of `W₂` vanish on the `T`-coordinates
  have hTdet : ((T.map res).hessian).det ≠ 0 := by
    rw [hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hTu.map res).ne_zero
  have hvan : ∀ w ∈ W₂, (fun j => w (Fin.natAdd m j)) = 0 := by
    intro w hw
    apply Matrix.eq_zero_of_mulVec_eq_zero hTdet
    funext j
    have h1 := resPolar_eq_zero hπ h2 h20 Q₂ han₂ hw (Fin.append 0 (Pi.single j 1))
    have h3 := bil_orthSum 𝔽 M T w (Fin.append 0 (Pi.single j 1))
    have e1 : (Q₂.map res).hessian = Q₂.hessian.map (algebraMap R 𝔽) := hessian_map _ _
    rw [e1] at h1
    rw [h1] at h3
    simp only [Fin.append_left, Fin.append_right, mulVec_zero, dotProduct_zero, zero_add] at h3
    have e2 : T.hessian.map (algebraMap R 𝔽) = (T.map res).hessian := (hessian_map _ _).symm
    rw [e2, Hanke2005.dot_hessian_comm, single_dotProduct_one] at h3
    exact h3.symm
  -- the projection to the `M`-coordinates is bijective
  let pM : W₂ →ₗ[𝔽] (Fin m → 𝔽) :=
    { toFun := fun w a => (w : Fin (m + 2) → 𝔽) (Fin.castAdd 2 a)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective pM := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    apply Subtype.ext
    funext i
    refine Fin.addCases (fun a => ?_) (fun j => ?_) i
    · exact congrFun hw a
    · exact congrFun (hvan w w.2) j
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fin_fun] at hle
  have hsurj : Function.Surjective pM :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [Module.finrank_fin_fun]; omega)).1 hinj
  intro y
  obtain ⟨w, hw⟩ := hsurj (fun a => res (y a))
  have hwe : (w : Fin (m + 2) → 𝔽) = fun i => res ((Fin.append y 0 : Fin (m + 2) → R) i) := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun j => ?_) i
    · exact (congrFun hw a).trans (by simp)
    · simpa using congrFun (hvan w w.2) j
  have h0 := w.2
  rw [mem_resZeroSub, hwe, eval_map_res, eval_orthSum_append, res_eq_zero_iff' hπ] at h0
  simpa [QuadForm.eval, QuadForm.evalIn] using h0

include hπ h2 h20 in
/-- **The bottom shape:** if $\dim\overline W = 2$ for $Q$ of rank $m+2$ with $\pi^2\mid Q(x)\Rightarrow\pi\mid x$, then
$Q\simeq M\perp\pi S$ with $S$ unimodular binary and $\bar S$ anisotropic (a basis of $\overline W$ lifts to a $\pi$-modular
plane, which splits off). -/
@[kb "omeara1963" "§91C, 91:9 (a modular component splits off); Shimura 1999, §3.2 (t = 3, 4)"]
theorem exists_shape_bottom {m : ℕ} (Q : QuadForm R (m + 2)) (han : ∀ x, Q.eval x = 0 → x = 0)
    (hmax : ∀ x : Fin (m + 2) → R, π ^ 2 ∣ Q.eval x → ∀ i, π ∣ x i)
    (hs : Module.finrank 𝔽 (resZeroSub hπ h2 h20 Q han) = 2) :
    ∃ (M : QuadForm R m) (S : QuadForm R 2), IsUnit S.hessian.det ∧
      (∀ s : Fin 2 → R, π ∣ S.eval s → ∀ i, π ∣ s i) ∧ DVR.IsGLEquiv Q (orthSum M (π • S)) := by
  classical
  set W := resZeroSub hπ h2 h20 Q han with hW
  set b := Module.finBasisOfFinrankEq 𝔽 W hs with hb
  set c : Fin 2 → Fin (m + 2) → 𝔽 := fun j => (b j : Fin (m + 2) → 𝔽) with hc
  have hcW : ∀ j, c j ∈ W := fun j => (b j).2
  choose w hw using fun j => res_surj_vec (c j)
  set X : Matrix (Fin (m + 2)) (Fin 2) R := colMat w with hX
  have hwQ : ∀ j, π ∣ Q.eval (w j) := by
    intro j
    rw [← res_eq_zero_iff' hπ, ← eval_map_res, hw j]
    exact hcW j
  have hSdvd : ∀ z, π ∣ (Q.compMat X).eval z := by
    intro z
    rw [eval_compMat, hX, colMat_mulVec, ← res_eq_zero_iff' hπ, ← eval_map_res]
    have e : (fun i => res ((∑ j, z j • w j) i)) = ∑ j, res (z j) • c j := by
      funext i
      simp [Finset.sum_apply, ← hw]
    rw [e]
    exact W.sum_mem fun j _ => W.smul_mem _ (hcW j)
  obtain ⟨S, hS⟩ := exists_eq_smul_of_dvd_eval hπ.ne_zero _ hSdvd
  have hSaniso : ∀ s : Fin 2 → R, π ∣ S.eval s → ∀ i, π ∣ s i := by
    intro s hs i
    have h2z : π ^ 2 ∣ Q.eval (X *ᵥ s) := by
      rw [← eval_compMat, hS, eval_smul_form, pow_two]
      exact mul_dvd_mul_left π hs
    have hx := hmax _ h2z
    have e : (∑ j, res (s j) • c j) = 0 := by
      funext l
      have := (res_eq_zero_iff' hπ _).2 (hx l)
      rw [hX, colMat_mulVec] at this
      simpa [Finset.sum_apply, ← hw] using this
    have hli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have := hli (fun j => res (s j)) (Subtype.ext (by simpa [hc] using e)) i
    exact (res_eq_zero_iff' hπ _).1 this
  have hSu := isUnit_det_of_aniso hπ h2 S hSaniso
  have hG : Xᵀ * Q.hessian * X = π • S.hessian := by
    rw [← hessian_compMat, hS]
    ext i j; simp [QuadForm.hessian]; ring
  have hYd : ∀ j l, π ∣ (Xᵀ * Q.hessian) j l := by
    intro j l
    have := pi_dvd_polar_of_aniso hπ h2 h20 Q han (hwQ j) (Pi.single l 1)
    convert this using 1
    simp [Matrix.mul_apply, dotProduct, mulVec, hX, colMat, Pi.single_apply]
  choose Y hY using hYd
  obtain ⟨M, hM⟩ := exists_split_scaled Q X hπ.ne_zero S.hessian hSu hG (Matrix.of Y)
    (by ext j l; simp [hY j l])
  exact ⟨M, S, hSu, hSaniso, by rw [← hS]; exact hM⟩

end Shape

end QuadFormsKB.Hanke2005
