/-
# Local adapted bases of a maximal order and the local trace-zero form

**Layer:** $F$ a number field (any class number), $D = (a,b)_F$, $\mathcal O$ an order, $v$ a finite place, $\mathcal O_v$ its completion.

A **local adapted basis** (`LTZ v O`) is an $\mathfrak o_v$-basis $E_0, \dots, E_3$ of $\mathcal O_v$ whose last three vectors are pure
($\operatorname{re} = 0$). It exists at every place (`LTZ.exists`: from a local frame, subtracting multiples of the vector whose reduced
trace has minimal valuation; no global basis of $\mathcal O$). For such a basis:
* $E_1, E_2, E_3$ is an $\mathfrak o_v$-basis of $\mathcal O_v^0$ (`LTZ.mem_Ov0_iff`), so with $P$ their $i,j,k$-coordinates,
  $(\mathcal O^0)_v = P\,\mathfrak o_v^3$ (`LTZ.loc_eq`, using `mem_loc_pureSub_iff`);
* $\det(\text{coordinates of }E) = \operatorname{re}(E_0)\det P$ (`LTZ.det_coordV`);
* the local form $T = \langle -a,-b,ab\rangle\circ P$ is integral (`LTZ.formT`, with `LTZ.map_formT`).

Source: Voight 2021, §§9.5, 22.1 [unverified locators]. Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.TernaryLocalNF

open NumberField IsDedekindDomain Matrix Quaternion WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity.NF IsLocalization
  QuadFormsKB.QuatZeta

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **A local adapted basis** of an order at $v$: an $F_v$-basis $E$ of $D_v$ whose $\mathfrak o_v$-span is $\mathcal O_v$, with
$E_1, E_2, E_3$ pure.

Fields:
- `E`: the four vectors;
- `li`: they are linearly independent over $F_v$;
- `mem_iff`: $y \in \mathcal O_v$ iff $y = \sum_ic_iE_i$ with $c_i \in \mathfrak o_v$;
- `re_succ`: $\operatorname{re}E_{l+1} = 0$. -/
structure LTZ (O : Subalgebra (𝓞 F) (QuatF F a b)) where
  E : Fin 4 → QuatV v a b
  li : LinearIndependent Fv E
  mem_iff : ∀ y, y ∈ localOrder (v := v) a b O ↔ ∃ c : Fin 4 → 𝔬, y = ∑ i, (c i : Fv) • E i
  re_succ : ∀ l : Fin 3, (E l.succ).re = 0

variable {v} {O : Subalgebra (𝓞 F) (QuatF F a b)}

namespace LTZ

variable (L : LTZ v O)

theorem mem (i : Fin 4) : L.E i ∈ localOrder (v := v) a b O :=
  (L.mem_iff _).2 ⟨fun j => if j = i then 1 else 0, by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    show L.E i = (((if i = i then (1 : 𝔬) else 0 : 𝔬)) : Fv) • L.E i
    rw [if_pos rfl, OneMemClass.coe_one, one_smul]⟩

/-- The adapted basis as an $F_v$-basis. -/
def basis : Module.Basis (Fin 4) Fv (QuatV v a b) :=
  basisOfLinearIndependentOfCardEqFinrank L.li (by rw [Fintype.card_fin, QuaternionAlgebra.finrank_eq_four])

@[simp] theorem basis_apply (i : Fin 4) : L.basis i = L.E i := by
  rw [basis, coe_basisOfLinearIndependentOfCardEqFinrank]

theorem re_sum (c : Fin 4 → Fv) : (∑ i, c i • L.E i).re = c 0 * (L.E 0).re := by
  have h1 := L.re_succ 0; have h2 := L.re_succ 1; have h3 := L.re_succ 2
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h1 h2 h3
  rw [Fin.sum_univ_four]
  simp only [QuaternionAlgebra.re_add, QuaternionAlgebra.re_smul, smul_eq_mul, h1, h2]
  rw [show (3 : Fin 4) = (2 : Fin 3).succ from rfl, L.re_succ 2]; ring

theorem re_zero : (L.E 0).re ≠ 0 := by
  obtain ⟨c, hc⟩ := (L.mem_iff 1).1 (Subalgebra.one_mem _)
  have h := congrArg QuaternionAlgebra.re hc
  rw [L.re_sum, QuaternionAlgebra.re_one] at h
  intro h0; rw [h0, mul_zero] at h; exact one_ne_zero h

/-- **$E_1, E_2, E_3$ span $\mathcal O_v^0$ over $\mathfrak o_v$.** -/
theorem mem_Ov0_iff (z : QuatV v a b) : z ∈ Ov0NF v O ↔ ∃ c : Fin 3 → 𝔬, z = ∑ l, (c l : Fv) • L.E l.succ := by
  constructor
  · rintro ⟨hz, hz0⟩
    obtain ⟨c, rfl⟩ := (L.mem_iff z).1 hz
    have h0 : (c 0 : Fv) = 0 := by
      rw [L.re_sum] at hz0
      exact (mul_eq_zero.1 hz0).resolve_right L.re_zero
    refine ⟨fun l => c l.succ, ?_⟩
    rw [Fin.sum_univ_succ, h0, zero_smul, zero_add]
  · rintro ⟨c, rfl⟩
    refine ⟨(L.mem_iff _).2 ⟨Fin.cons 0 c, ?_⟩, ?_⟩
    · rw [Fin.sum_univ_succ (n := 3)]; simp <;> rfl
    · simp only [Fin.sum_univ_three, QuaternionAlgebra.re_add, QuaternionAlgebra.re_smul, smul_eq_mul, L.re_succ,
        mul_zero, add_zero]

/-- The matrix $P$ of $i, j, k$-coordinates of $E_1, E_2, E_3$ (column $l$ = coordinates of $E_{l+1}$). -/
def Pm : Matrix (Fin 3) (Fin 3) Fv := Matrix.of fun r l => imv (L.E l.succ) r

theorem pure_Pm_mulVec (y : Fin 3 → Fv) : (Quat.pure (L.Pm *ᵥ y) : QuatV v a b) = ∑ l, y l • L.E l.succ := by
  have h1 : L.Pm *ᵥ y = ∑ l, y l • imv (L.E l.succ) := by
    ext r; simp [Pm, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [h1]
  simp only [Fin.sum_univ_three, pure_add, pure_smul, pure_imv (L.re_succ _)]

theorem det_Pm_ne_zero : L.Pm.det ≠ 0 := by
  intro h0
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hs : ∑ l, y l • L.E l.succ = 0 := by
    rw [← L.pure_Pm_mulVec, hy]; ext <;> simp [Quat.pure]
  have hli' := L.li.comp Fin.succ (Fin.succ_injective _)
  exact hy0 (funext ((Fintype.linearIndependent_iff.1 hli') y hs))

/-- $P$ as an element of $\mathrm{GL}_3(F_v)$. -/
def PG : GL (Fin 3) Fv := ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 L.det_Pm_ne_zero)).unit

@[simp] theorem PG_val : (L.PG : Matrix (Fin 3) (Fin 3) Fv) = L.Pm := rfl

theorem isInteger_iff_le_one'' (x : Fv) : IsInteger 𝔬 x ↔ Valued.v x ≤ 1 := isInteger_iff_le_one' v x

/-- **$(\mathcal O^0)_v = P\,\mathfrak o_v^3$.** -/
theorem loc_eq (hO : IsOrder (𝓞 F) F O) : loc v (pureSub O) = locAct v L.PG (std v) := by
  ext y
  rw [mem_loc_pureSub_iff hO, L.mem_Ov0_iff, mem_locAct]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun l => (c l : Fv), fun l => ?_, ?_⟩
    · change Valued.v (c l : Fv) ≤ exp (-(0 : ℤ))
      rw [neg_zero, exp_zero]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (c l).2
    · rw [PG_val]
      apply (show Function.Injective (Quat.pure : (Fin 3 → Fv) → QuatV v a b) from fun x y h => by
        have := congrArg imv h; simpa using this)
      rw [L.pure_Pm_mulVec, hc]
  · rintro ⟨c, hc, rfl⟩
    have hci : ∀ l, IsInteger 𝔬 (c l) := fun l => (isInteger_iff_le_one' v _).2 (by
      have := hc l; simpa using this)
    choose d hd using hci
    refine ⟨d, ?_⟩
    rw [PG_val, L.pure_Pm_mulVec]
    exact Finset.sum_congr rfl fun l _ => by rw [← hd l]; rfl

/-- The coordinate matrix of $E$ in $1, i, j, k$. -/
def coordV : Matrix (Fin 4) (Fin 4) Fv :=
  Matrix.of fun r i => ![(L.E i).re, (L.E i).imI, (L.E i).imJ, (L.E i).imK] r

/-- **$\det(\text{coordinates of }E) = \operatorname{re}(E_0)\det P$.** -/
theorem det_coordV : L.coordV.det = (L.E 0).re * L.Pm.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hz : ∀ j : Fin 3, L.coordV 0 j.succ = 0 := fun j => by
    simp [coordV, L.re_succ j]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
  have hsub : L.coordV.submatrix Fin.succ (Fin.succAbove 0) = L.Pm := by
    ext r l; fin_cases r <;> rfl
  rw [hsub]; rfl

/-! ### The local form -/

/-- $\langle -a,-b,ab\rangle$ over $F_v$. -/
abbrev QV (v : HeightOneSpectrum (𝓞 F)) (a b : 𝓞 F) : QuadForm (v.adicCompletion F) 3 :=
  pureForm (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v a))
    (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v b))

theorem eval_QV_Pm (y : Fin 3 → Fv) : ((QV v a b).compMat L.Pm).eval y = nrd (∑ l, y l • L.E l.succ) := by
  rw [QuadForm.eval_compMat, ← nrd_pure, L.pure_Pm_mulVec]

theorem coeff_integral (hO : IsOrder (𝓞 F) F O) (i j : Fin 3) :
    IsInteger 𝔬 (((QV v a b).compMat L.Pm).coeff i j) := by
  have hOv := Gen.isOrder_localOrder_gen v hO
  have hcol : ∀ i : Fin 3, (fun l => L.Pm l i) = L.Pm *ᵥ Pi.single i 1 := fun i => by
    ext l; simp [mulVec_single]
  have hnrd : ∀ z ∈ localOrder (v := v) a b O, IsInteger 𝔬 (nrd z) := fun z hz => (isInteger_trd_nrd hOv hz).2
  have hval : ∀ y : Fin 3 → 𝔬, IsInteger 𝔬 (((QV v a b).compMat L.Pm).eval (fun l => (y l : Fv))) := by
    intro y
    rw [L.eval_QV_Pm]
    exact hnrd _ ((L.mem_iff _).2 ⟨Fin.cons 0 y, by rw [Fin.sum_univ_succ (n := 3)]; simp <;> rfl⟩)
  rw [QuadForm.compMat_coeff]
  split_ifs with hle heq
  · subst heq
    have := hval (Pi.single i 1)
    rw [QuadForm.eval_compMat] at this
    convert this using 2
    rw [hcol]; congr 1; ext l; simp [Pi.single_apply]; split_ifs <;> simp
  · -- the polar value
    have h1 := hval (Pi.single i 1 + Pi.single j 1)
    have h2 := hval (Pi.single i 1)
    have h3 := hval (Pi.single j 1)
    have e : (fun l => L.Pm l i) ⬝ᵥ ((QV v a b).hessian *ᵥ fun l => L.Pm l j) =
        ((QV v a b).compMat L.Pm).eval (fun l => ((Pi.single i 1 + Pi.single j 1 : Fin 3 → 𝔬) l : Fv)) -
        ((QV v a b).compMat L.Pm).eval (fun l => ((Pi.single i 1 : Fin 3 → 𝔬) l : Fv)) -
        ((QV v a b).compMat L.Pm).eval (fun l => ((Pi.single j 1 : Fin 3 → 𝔬) l : Fv)) := by
      have hsplit : (fun l => ((Pi.single i 1 + Pi.single j 1 : Fin 3 → 𝔬) l : Fv)) =
          (fun l => ((Pi.single i 1 : Fin 3 → 𝔬) l : Fv)) + (fun l => ((Pi.single j 1 : Fin 3 → 𝔬) l : Fv)) := by
        funext l; simp
      have hcol' : ∀ k : Fin 3, (L.Pm *ᵥ fun l => ((Pi.single k 1 : Fin 3 → 𝔬) l : Fv)) = fun l => L.Pm l k := by
        intro k; funext l
        simp only [mulVec, dotProduct, Pi.single_apply]
        rw [Finset.sum_eq_single k (fun x _ hx => by simp [hx]) (by simp)]
        simp
      rw [hsplit, QuadForm.eval_compMat, QuadForm.eval_compMat, QuadForm.eval_compMat, mulVec_add,
        QuadForm.eval_polar, hcol', hcol']
    rw [e]
    obtain ⟨c1, hc1⟩ := h1; obtain ⟨c2, hc2⟩ := h2; obtain ⟨c3, hc3⟩ := h3
    exact ⟨c1 - c2 - c3, by rw [map_sub, map_sub, hc1, hc2, hc3]⟩
  · exact ⟨0, by simp⟩

/-- **The local form of $\mathcal O_v^0$** in the basis $E_1, E_2, E_3$: an integral ternary form over $\mathfrak o_v$. -/
def formT (hO : IsOrder (𝓞 F) F O) : QuadForm 𝔬 3 :=
  QuadForm.ofUpper fun i j => (L.coeff_integral hO i j).choose

theorem map_formT (hO : IsOrder (𝓞 F) F O) :
    (L.formT hO).map (algebraMap 𝔬 Fv) = (QV v a b).compMat L.Pm := by
  refine QuadForm.ext (Matrix.ext fun i j => ?_)
  simp only [formT, QuadForm.map, QuadForm.ofUpper, Matrix.map_apply, Matrix.of_apply]
  split_ifs with h
  · exact (L.coeff_integral hO i j).choose_spec
  · rw [map_zero]
    exact (((QV v a b).compMat L.Pm).upper (by simpa using h)).symm

theorem _root_.QuadFormsKB.QuatOrder.eval_smul_vec_nf {A : Type*} [CommRing A] {n : ℕ} (Q : QuadForm A n) (c : A)
    (x : Fin n → A) : Q.eval (c • x) = c ^ 2 * Q.eval x := by
  simp only [QuadForm.eval, QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-! ### Coordinates of $\mathcal O_v^0$ -/

/-- $\psi(w) = \sum_lw_lE_{l+1}$. -/
def psi (w : Fin 3 → Fv) : QuatV v a b := ∑ l, w l • L.E l.succ

theorem psi_eq (w : Fin 3 → Fv) : L.psi w = Quat.pure (L.Pm *ᵥ w) := (L.pure_Pm_mulVec w).symm

theorem re_psi (w : Fin 3 → Fv) : (L.psi w).re = 0 := by rw [psi_eq]; rfl

theorem psi_injective : Function.Injective L.psi := by
  intro w w' h
  have hli' := L.li.comp Fin.succ (Fin.succ_injective _)
  have h2 : ∑ l, (w l - w' l) • L.E l.succ = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]; exact sub_eq_zero.2 h
  funext l
  exact sub_eq_zero.1 ((Fintype.linearIndependent_iff.1 hli') _ h2 l)

theorem psi_zero : L.psi 0 = 0 := by simp [psi]

theorem nrd_psi (w : Fin 3 → Fv) : nrd (L.psi w) = ((QV v a b).compMat L.Pm).eval w := (L.eval_QV_Pm w).symm

theorem psi_mem_Ov0_iff (w : Fin 3 → Fv) : L.psi w ∈ Ov0NF v O ↔ ∀ l, IsInteger 𝔬 (w l) := by
  rw [L.mem_Ov0_iff]
  constructor
  · rintro ⟨c, hc⟩ l
    have := L.psi_injective (show L.psi w = L.psi (fun l => (c l : Fv)) from hc)
    exact ⟨c l, by rw [this]; rfl⟩
  · intro h
    choose c hc using h
    exact ⟨c, Finset.sum_congr rfl fun l _ => by rw [← hc l]; rfl⟩

theorem eval_formT_coe (hO : IsOrder (𝓞 F) F O) (z : Fin 3 → 𝔬) :
    algebraMap 𝔬 Fv ((L.formT hO).eval z) = nrd (L.psi fun l => algebraMap 𝔬 Fv (z l)) := by
  rw [nrd_psi, ← L.map_formT hO, LocalDensity.DVR.eval_map_comp']

/-- The reduced trace of $E_0$ is integral: $|2\operatorname{re}E_0|_v \le 1$. -/
theorem norm_two_mul_re_le (hO : IsOrder (𝓞 F) F O) : ‖(2 : Fv) * (L.E 0).re‖ ≤ 1 := by
  obtain ⟨t, ht⟩ := (isInteger_trd_nrd (Gen.isOrder_localOrder_gen v hO) (L.mem 0)).1
  rw [trd] at ht
  rw [← ht]
  exact (Valued.toNormedField.norm_le_one_iff).mpr ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp t.2)

/-- If $y = \sum c_iE_i \in \mathcal O_v$ has $\operatorname{re}y = 1/2$ then $|2\operatorname{re}E_0|_v \ge 1$. -/
theorem one_le_norm_two_mul_re {y : QuatV v a b} (hy : y ∈ localOrder (v := v) a b O) (hre : y.re = 1 / 2) :
    1 ≤ ‖(2 : Fv) * (L.E 0).re‖ := by
  obtain ⟨c, rfl⟩ := (L.mem_iff y).1 hy
  rw [L.re_sum] at hre
  have h1 : (c 0 : Fv) * ((2 : Fv) * (L.E 0).re) = 1 := by
    have h2 : (2 : Fv) ≠ 0 := two_ne_zero_Fv v
    linear_combination (2 : Fv) * hre
  have hle : ‖((c 0 : 𝔬) : Fv)‖ ≤ 1 :=
    (Valued.toNormedField.norm_le_one_iff).mpr ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (c 0).2)
  have h2 := congrArg norm h1
  rw [norm_mul, norm_one] at h2
  nlinarith [norm_nonneg ((c 0 : 𝔬) : Fv), norm_nonneg ((2 : Fv) * (L.E 0).re)]

/-- $\det H_T = 8(ab\det P)^2$ in $F_v$. -/
theorem det_hessian_formT (hO : IsOrder (𝓞 F) F O) :
    algebraMap 𝔬 Fv (L.formT hO).hessian.det =
      8 * (algebraMap 𝔬 Fv (ι v a) * algebraMap 𝔬 Fv (ι v b) * L.Pm.det) ^ 2 := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← QuadForm.hessian_map, L.map_formT hO,
    QuadForm.hessian_compMat, det_mul, det_mul, det_transpose]
  have hH : (QV v a b).hessian = Matrix.diagonal ![-2 * algebraMap 𝔬 Fv (ι v a), -2 * algebraMap 𝔬 Fv (ι v b),
      2 * (algebraMap 𝔬 Fv (ι v a) * algebraMap 𝔬 Fv (ι v b))] := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [QuadForm.hessian, pureForm, QuadForm.diag, Matrix.diagonal] <;> ring
  rw [hH, det_diagonal, Fin.prod_univ_three]
  simp
  ring

/-! ### Ramified places: anisotropy and maximality -/

section Ram

variable (hdiv : ∀ x : QuatV v a b, nrd x = 0 → x = 0)
  (heq : localOrder (v := v) a b O = valOrder (R := v.adicCompletionIntegers F) hdiv)

include hdiv in
theorem formT_aniso (hO : IsOrder (𝓞 F) F O) (z : Fin 3 → 𝔬) (hz : (L.formT hO).eval z = 0) : z = 0 := by
  have h := L.eval_formT_coe hO z
  rw [hz, map_zero] at h
  have h0 := hdiv _ h.symm
  have : (fun l => algebraMap 𝔬 Fv (z l)) = 0 := L.psi_injective (by rw [h0, L.psi_zero])
  funext i
  exact IsFractionRing.injective 𝔬 Fv (by simpa using congrFun this i)

include heq in
/-- **Maximality of $\mathcal O_v^0$ at a ramified place:** $Q(Py) \in \mathfrak o_v \Rightarrow y \in \mathfrak o_v^3$. -/
theorem isInteger_of_eval (y : Fin 3 → Fv) (hy : IsInteger 𝔬 (((QV v a b).compMat L.Pm).eval y)) :
    ∀ i, IsInteger 𝔬 (y i) := by
  rw [← L.nrd_psi] at hy
  have hmem : L.psi y ∈ Ov0NF v O := by
    rw [mem_Ov0NF, heq, mem_valOrder]; exact ⟨hy, L.re_psi y⟩
  exact (L.psi_mem_Ov0_iff y).1 hmem

include heq in
/-- **Maximality in DVR form:** $\varpi^2 \mid T(z) \Rightarrow \varpi \mid z$. -/
theorem hmax_ram (hO : IsOrder (𝓞 F) F O) :
    ∀ z : Fin 3 → 𝔬, π v ^ 2 ∣ (L.formT hO).eval z → ∀ i, π v ∣ z i := by
  have hπ := irreducible_π v
  have hπF : algebraMap 𝔬 Fv (π v) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hπ.ne_zero
  intro z hz
  obtain ⟨c, hc⟩ := hz
  set x : Fin 3 → Fv := fun j => algebraMap 𝔬 Fv (z j) with hx
  have hint : IsInteger 𝔬 (((QV v a b).compMat L.Pm).eval ((algebraMap 𝔬 Fv (π v))⁻¹ • x)) := by
    rw [eval_smul_vec_nf, ← L.nrd_psi, hx, ← L.eval_formT_coe hO, hc]
    refine ⟨c, ?_⟩
    rw [map_mul, map_pow]
    field_simp
  have hy := L.isInteger_of_eval hdiv heq _ hint
  intro i
  obtain ⟨d, hd⟩ := hy i
  refine ⟨d, IsFractionRing.injective 𝔬 Fv ?_⟩
  rw [map_mul, hd]
  simp only [hx, Pi.smul_apply, smul_eq_mul]
  field_simp

end Ram

/-- **The discriminant of $T$ in DVR form:** $\varpi^{2i}\det H_T = 8\varpi^{2j}w^2$, $w$ a unit. -/
theorem hdisc (hO : IsOrder (𝓞 F) F O) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ (i j : ℕ) (w : 𝔬), IsUnit w ∧ π v ^ (2 * i) * (L.formT hO).hessian.det = 8 * π v ^ (2 * j) * w ^ 2 := by
  have hπ := irreducible_π v
  set r : Fv := algebraMap 𝔬 Fv (ι v a) * algebraMap 𝔬 Fv (ι v b) * L.Pm.det with hr
  have hr0 : r ≠ 0 := mul_ne_zero (mul_ne_zero
    ((map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v ha))
    ((map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v hb))) L.det_Pm_ne_zero
  have hdetF := L.det_hessian_formT hO
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝔬) r
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hxy
    exact hr0 hxy.symm
  obtain ⟨m₁, w₁, rfl, hw₁⟩ : ∃ m w, x = π v ^ m * w ∧ IsUnit w := by
    obtain ⟨m, hm, hm'⟩ := LocalDensity.DVR.exists_pow_dvd_not_dvd (π v) hπ hx0
    obtain ⟨w, hw, hwu⟩ := LocalDensity.DVR.dvr_exact hπ hm hm'
    exact ⟨m, w, hw, hwu⟩
  obtain ⟨m₂, w₂, rfl, hw₂⟩ : ∃ m w, y = π v ^ m * w ∧ IsUnit w := by
    obtain ⟨m, hm, hm'⟩ := LocalDensity.DVR.exists_pow_dvd_not_dvd (π v) hπ hy0
    obtain ⟨w, hw, hwu⟩ := LocalDensity.DVR.dvr_exact hπ hm hm'
    exact ⟨m, w, hw, hwu⟩
  refine ⟨m₂, m₁, w₁ * ↑hw₂.unit⁻¹, hw₁.mul (Units.isUnit _), ?_⟩
  have hyF : algebraMap 𝔬 Fv (π v ^ m₂ * w₂) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hy0
  have key : (L.formT hO).hessian.det * (π v ^ m₂ * w₂) ^ 2 = 8 * (π v ^ m₁ * w₁) ^ 2 := by
    apply IsFractionRing.injective 𝔬 Fv
    rw [map_mul, hdetF, ← hr]
    simp only [map_mul, map_pow, map_ofNat]
    rw [← hxy]
    simp only [map_mul, map_pow] at hyF ⊢
    field_simp
    rw [div_eq_iff hyF]; ring
  have hinv : w₂ * ↑hw₂.unit⁻¹ = 1 := hw₂.mul_val_inv
  calc π v ^ (2 * m₂) * (L.formT hO).hessian.det
      = π v ^ (2 * m₂) * (L.formT hO).hessian.det * (w₂ * ↑hw₂.unit⁻¹) ^ 2 := by rw [hinv]; ring
    _ = ((L.formT hO).hessian.det * (π v ^ m₂ * w₂) ^ 2) * (↑hw₂.unit⁻¹) ^ 2 := by ring
    _ = 8 * π v ^ (2 * m₁) * (w₁ * ↑hw₂.unit⁻¹) ^ 2 := by rw [key]; ring

end LTZ

/-! ### Independence of the local volume from the basis -/

/-- The coordinate matrix of a family in $D_v$ ($1, i, j, k$). -/
def coordQ (E : Fin 4 → QuatV v a b) : Matrix (Fin 4) (Fin 4) Fv :=
  Matrix.of fun r i => ![(E i).re, (E i).imI, (E i).imJ, (E i).imK] r

theorem LTZ.coordV_eq (L : LTZ v O) : L.coordV = coordQ L.E := rfl

theorem coordQ_sum (E : Fin 4 → QuatV v a b) (c : Fin 4 → Fv) (r : Fin 4) :
    ![(∑ i, c i • E i).re, (∑ i, c i • E i).imI, (∑ i, c i • E i).imJ, (∑ i, c i • E i).imK] r =
      ∑ i, coordQ E r i * c i := by
  fin_cases r <;> simp [coordQ, Fin.sum_univ_four, mul_comm]

theorem coordQ_smul_complHom (f : Fin 4 → QuatF F a b) (c : Fin 4 → Fv) :
    coordQ (fun i => c i • complHom v a b (f i)) = (coordMat f).map (algebraMap F Fv) * Matrix.diagonal c := by
  refine Matrix.ext fun r i => ?_
  rw [Matrix.mul_diagonal]
  fin_cases r
  · show (c i • complHom v a b (f i)).re = algebraMap F Fv (f i).re * c i
    rw [QuaternionAlgebra.re_smul, smul_eq_mul, complHom_re, mul_comm]
  · show (c i • complHom v a b (f i)).imI = algebraMap F Fv (f i).imI * c i
    rw [QuaternionAlgebra.imI_smul, smul_eq_mul, complHom_imI, mul_comm]
  · show (c i • complHom v a b (f i)).imJ = algebraMap F Fv (f i).imJ * c i
    rw [QuaternionAlgebra.imJ_smul, smul_eq_mul, complHom_imJ, mul_comm]
  · show (c i • complHom v a b (f i)).imK = algebraMap F Fv (f i).imK * c i
    rw [QuaternionAlgebra.imK_smul, smul_eq_mul, complHom_imK, mul_comm]

theorem det_coordQ_ne_zero {E : Fin 4 → QuatV v a b} (hli : LinearIndependent Fv E) : (coordQ E).det ≠ 0 := by
  let fb := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, QuaternionAlgebra.finrank_eq_four])
  have h := (QuaternionAlgebra.basisOneIJK (algebraMap 𝔬 Fv (ι v a)) 0 (algebraMap 𝔬 Fv (ι v b))).isUnit_det fb
  rw [Module.Basis.det_apply] at h
  have hC : (QuaternionAlgebra.basisOneIJK (algebraMap 𝔬 Fv (ι v a)) 0 (algebraMap 𝔬 Fv (ι v b))).toMatrix fb =
      coordQ E := by
    ext r i
    rw [Module.Basis.toMatrix_apply, coe_basisOfLinearIndependentOfCardEqFinrank, QuaternionAlgebra.coe_basisOneIJK_repr]
    rfl
  rw [hC] at h
  exact h.ne_zero

/-- **The local covolume does not depend on the $\mathfrak o_v$-basis:** two linearly independent families with the same
$\mathfrak o_v$-span have coordinate determinants of equal absolute value. -/
theorem norm_det_coordQ_eq {Λ : Set (QuatV v a b)} {E E' : Fin 4 → QuatV v a b}
    (hE : ∀ y, y ∈ Λ ↔ ∃ c : Fin 4 → 𝔬, y = ∑ i, (c i : Fv) • E i)
    (hE' : ∀ y, y ∈ Λ ↔ ∃ c : Fin 4 → 𝔬, y = ∑ i, (c i : Fv) • E' i)
    (hli : LinearIndependent Fv E) : ‖(coordQ E).det‖ = ‖(coordQ E').det‖ := by
  have hmemE : ∀ i, E i ∈ Λ := fun i => (hE _).2 ⟨fun j => if j = i then 1 else 0, by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    show E i = (((if i = i then (1 : 𝔬) else 0 : 𝔬)) : Fv) • E i
    rw [if_pos rfl, OneMemClass.coe_one, one_smul]⟩
  have hmemE' : ∀ i, E' i ∈ Λ := fun i => (hE' _).2 ⟨fun j => if j = i then 1 else 0, by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    show E' i = (((if i = i then (1 : 𝔬) else 0 : 𝔬)) : Fv) • E' i
    rw [if_pos rfl, OneMemClass.coe_one, one_smul]⟩
  choose U hU using fun j => (hE _).1 (hmemE' j)
  choose V hV using fun j => (hE' _).1 (hmemE j)
  set Um : Matrix (Fin 4) (Fin 4) 𝔬 := Matrix.of fun i j => U j i
  set Vm : Matrix (Fin 4) (Fin 4) 𝔬 := Matrix.of fun i j => V j i
  have hc1 : coordQ E' = coordQ E * Um.map (algebraMap 𝔬 Fv) := by
    refine Matrix.ext fun r j => ?_
    rw [Matrix.mul_apply]
    have := coordQ_sum E (fun i => (U j i : Fv)) r
    rw [← hU j] at this
    simp only [Um, Matrix.map_apply, Matrix.of_apply]
    exact this
  have hc2 : coordQ E = coordQ E' * Vm.map (algebraMap 𝔬 Fv) := by
    refine Matrix.ext fun r j => ?_
    rw [Matrix.mul_apply]
    have := coordQ_sum E' (fun i => (V j i : Fv)) r
    rw [← hV j] at this
    simp only [Vm, Matrix.map_apply, Matrix.of_apply]
    exact this
  have hdet := det_coordQ_ne_zero hli
  have hUV : (Um * Vm).map (algebraMap 𝔬 Fv) = 1 := by
    have h3 : coordQ E * (Um * Vm).map (algebraMap 𝔬 Fv) = coordQ E * 1 := by
      rw [Matrix.map_mul, ← Matrix.mul_assoc, ← hc1, ← hc2, Matrix.mul_one]
    have hu : IsUnit (coordQ E).det := isUnit_iff_ne_zero.2 hdet
    have := congrArg (fun M => (coordQ E)⁻¹ * M) h3
    simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hu] using this
  have hdetUV : Um.det * Vm.det = 1 := by
    apply IsFractionRing.injective 𝔬 Fv
    rw [map_mul, map_one, RingHom.map_det, RingHom.map_det, ← det_mul, ← map_mul, RingHom.mapMatrix_apply, hUV, det_one]
  have hUu : IsUnit Um.det := IsUnit.of_mul_eq_one _ hdetUV
  have hnU : ‖algebraMap 𝔬 Fv Um.det‖ = 1 := by
    have := norm_coe_of_pow_dvd v (x := Um.det) (e := 0) (by simp)
      (by simpa using LocalDensity.DVR.dvr_not_dvd_of_isUnit (irreducible_π v) hUu)
    rwa [pow_zero, inv_one] at this
  rw [hc1, det_mul, norm_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hnU, mul_one]

namespace LTZ

variable (L : LTZ v O)

/-! ### Existence -/

variable (v) in
/-- **Local adapted bases exist at every place** (any order): start from a local frame $f$, let $f_{i_0}$ have reduced trace of minimal
valuation and replace every other $f_j$ by $f_j - (t_j/t_{i_0})f_{i_0}$ ($t = \operatorname{re}f$). -/
theorem _root_.QuadFormsKB.QuatOrder.LTZ.exists (hO : IsOrder (𝓞 F) F O) : Nonempty (LTZ v O) := by
  classical
  obtain ⟨L⟩ := LocFrame.exists (v := v) hO
  set t : Fin 4 → F := fun i => (L.fb i).re
  have hall : ∃ i, t i ≠ 0 := by
    by_contra h
    push Not at h
    have h1 : complHom v a b (1 : QuatF F a b) ∈ localOrder (v := v) a b O := mem_localOrder_of_mem a b O.one_mem
    rw [L.complHom_eq_sum] at h1
    have := congrArg QuaternionAlgebra.re (show complHom v a b (1 : QuatF F a b) =
      ∑ i, algebraMap F Fv (L.fb.repr 1 i) • L.cvec i from L.complHom_eq_sum 1)
    rw [map_one, QuaternionAlgebra.re_one, Fin.sum_univ_four] at this
    simp only [QuaternionAlgebra.re_add, QuaternionAlgebra.re_smul, smul_eq_mul, LocFrame.cvec, complHom_re] at this
    simp only [t] at h
    rw [h 0, h 1, h 2, h 3] at this
    simp at this
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 4)) (fun i => v.valuation F (t i))
    Finset.univ_nonempty
  have ht0 : t i₀ ≠ 0 := by
    obtain ⟨j, hj⟩ := hall
    intro h0
    have := hmax j (Finset.mem_univ _)
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hj this
  set s : Fin 4 → Fv := fun j => algebraMap F Fv (t j / t i₀)
  have hs : ∀ j, Valued.v (s j) ≤ 1 := fun j => by
    simp only [s]
    rw [valued_algebraMap, map_div₀, div_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 ht0))]
    exact hmax j (Finset.mem_univ _)
  set so : Fin 4 → 𝔬 := fun j => ⟨s j, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hs j)⟩
  have hso : ∀ j, ((so j : 𝔬) : Fv) = s j := fun j => rfl
  have hret : ∀ j, (L.cvec j).re = algebraMap F Fv (t j) := fun j => complHom_re a b (L.fb j)
  set E : Fin 4 → QuatV v a b := Fin.cons (L.cvec i₀) fun l => L.cvec (i₀.succAbove l) - s (i₀.succAbove l) • L.cvec i₀
  have hE0 : E 0 = L.cvec i₀ := rfl
  have hEs : ∀ l, E l.succ = L.cvec (i₀.succAbove l) - s (i₀.succAbove l) • L.cvec i₀ := fun l => rfl
  have hEmem : ∀ i, E i ∈ localOrder (v := v) a b O := by
    intro i
    refine Fin.cases ?_ (fun l => ?_) i
    · rw [hE0]; exact mem_localOrder_of_mem a b (L.mem _)
    · rw [hEs, ← hso]
      exact Subalgebra.sub_mem _ (mem_localOrder_of_mem a b (L.mem _))
        (Subalgebra.smul_mem _ (mem_localOrder_of_mem a b (L.mem _)) (so (i₀.succAbove l)))
  -- every `cvec j` is an integral combination of `E`
  have hcvec : ∀ j, ∃ c : Fin 4 → 𝔬, L.cvec j = ∑ i, (c i : Fv) • E i := by
    intro j
    by_cases hj : j = i₀
    · subst hj
      refine ⟨Pi.single 0 1, ?_⟩
      rw [Finset.sum_eq_single 0 (fun i _ hi => by simp [hi]) (by simp)]
      simp [hE0]
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj
      refine ⟨Pi.single 0 (so (i₀.succAbove l)) + Pi.single l.succ 1, ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Pi.add_apply, Pi.single_apply, Fin.succ_ne_zero, if_false, add_zero, zero_add, if_true,
        Fin.succ_inj]
      rw [Finset.sum_eq_single l (fun k _ hk => by simp [hk]) (by simp)]
      simp only [if_true, hE0, hEs, OneMemClass.coe_one, one_smul,
        show (0 : Fin 4) ≠ l.succ from (Fin.succ_ne_zero l).symm, if_false, add_zero, hso]
      rw [sub_eq_add_neg]
      abel
  refine ⟨⟨E, ?_, fun y => ?_, fun l => ?_⟩⟩
  · -- linear independence from spanning
    apply linearIndependent_of_top_le_span_of_card_eq_finrank _ (by rw [Fintype.card_fin, QuaternionAlgebra.finrank_eq_four])
    refine L.top_le_span_cvec.trans (Submodule.span_le.2 ?_)
    rintro _ ⟨j, rfl⟩
    obtain ⟨c, hc⟩ := hcvec j
    rw [hc]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · constructor
    · intro hy
      have hd := (L.mem_localOrder_iff y).1 hy
      choose d hd using hd
      have hy' : y = ∑ j, (d j : Fv) • L.cvec j := by
        conv_lhs => rw [← L.cb.sum_repr y]
        exact Finset.sum_congr rfl fun j _ => by rw [LocFrame.cb_apply, ← hd j]; rfl
      choose c hc using hcvec
      refine ⟨fun i => ∑ j, d j * c j i, ?_⟩
      rw [hy']
      simp_rw [hc, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_smul]
      congr 1
    · rintro ⟨c, rfl⟩
      exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (hEmem i) (c i)
  · rw [hEs, QuaternionAlgebra.re_sub, QuaternionAlgebra.re_smul, smul_eq_mul, hret, hret]
    simp only [s, ← map_mul]
    rw [div_mul_cancel₀ _ ht0, sub_self]

end LTZ

end QuadFormsKB.QuatOrder
