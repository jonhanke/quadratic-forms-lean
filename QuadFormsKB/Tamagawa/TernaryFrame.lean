/-
# The ternary lattice $\mathcal O^0$ of a maximal order: frames, local conjugation maps, local stabilizers

**Layer:** $F$ a number field with $\mathcal O_F$ a PID, $D = (a,b)_F$ ($a, b \in \mathcal O_F\setminus0$), $\mathcal O \subseteq D$ an
$\mathcal O_F$-order, and a **trace-zero frame** of $\mathcal O$: an $\mathcal O_F$-basis $e_0, \dots, e_3$ of $\mathcal O$ with
$\operatorname{re}e_1 = \operatorname{re}e_2 = \operatorname{re}e_3 = 0 \ne \operatorname{re}e_0$ (`TZFrame`). Then $e_1, e_2, e_3$ is an
$\mathcal O_F$-basis of $\mathcal O^0 = \{x \in \mathcal O : \operatorname{trd}x = 0\}$, and in these coordinates the reduced norm on
$\mathcal O^0$ is the ternary form $Q_{\mathcal O^0} = \langle -a,-b,ab\rangle\circ P$ (`TZFrame.QF`), $P$ the matrix of
$i,j,k$-coordinates of $e_1, e_2, e_3$.

**Defines/proves** at each finite place $v$:
* the conjugation maps $c_v : D_v^\times \to SO(Q_{\mathcal O^0})(F_v)$ and $c : D^\times \to SO(Q_{\mathcal O^0})(F)$ (`cvv`, `cv0`), compatible
  with the diagonal embedding (`orthMap_cv0`);
* $\mathcal O_v^0 = \mathfrak o_v$-span of the $e_l$ $= \{z \in \mathcal O_v : \operatorname{re}z = 0\}$ (`mem_Ov0_iff`), the image of
  $\mathfrak o_v^3$ (`psiv_mem_Ov0_iff`);
* $c_v(x) \in O(\mathfrak o_v^3)$ iff conjugation by $x$ preserves $\mathcal O_v^0$ (`cvv_mem_stdStab_iff`);
* $K'_v = c_v(\mathcal O_v^\times)$ (`Kv`), contained in $SO(\mathfrak o_v^3)$ (`Kv_le_stdStab`, `Kv_le_soSub`), and
  $c_v(x) \in K'_v \iff x \in F_v^\times\mathcal O_v^\times$ (`cvv_mem_Kv_iff`).

Source: Voight 2021, §§10.4, 13.3, 17.7 (normalizers), 22.1 (the ternary lattice $\mathcal O^0$); Weil 1982, §3.7(a).
-/
import QuadFormsKB.Tamagawa.TernaryConj
import QuadFormsKB.Tamagawa.QuatEichlerMass

open NumberField IsDedekindDomain Matrix Quaternion WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity.NF IsLocalization

/-- The central unit $r \in K^\times \subseteq ((\alpha,\beta)_K)^\times$. -/
def qScalar {K : Type*} [Field K] {α β : K} (r : K) (hr : r ≠ 0) : (ℍ[K,α,β])ˣ :=
  Units.map (algebraMap K ℍ[K,α,β]).toMonoidHom (Units.mk0 r hr)

@[simp] theorem coe_qScalar {K : Type*} [Field K] {α β : K} (r : K) (hr : r ≠ 0) :
    ((qScalar (α := α) (β := β) r hr : (ℍ[K,α,β])ˣ) : ℍ[K,α,β]) = algebraMap K ℍ[K,α,β] r := rfl

theorem qScalar_inv {K : Type*} [Field K] {α β : K} (r : K) (hr : r ≠ 0) :
    (qScalar (α := α) (β := β) r hr)⁻¹ = qScalar r⁻¹ (inv_ne_zero hr) := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  rw [Units.val_mul, coe_qScalar, coe_qScalar, ← map_mul, mul_inv_cancel₀ hr, map_one, Units.val_one]

/-! ### Trace-zero frames -/

section Frame

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

/-- **A trace-zero frame** of an order $\mathcal O$: an $\mathcal O_F$-basis $e_0, \dots, e_3$ of $\mathcal O$ with $e_1, e_2, e_3$ pure
($\operatorname{re} = 0$, i.e. $\operatorname{trd} = 0$) and $\operatorname{re}e_0 \ne 0$.

Fields:
- `isOrder`: $\mathcal O$ is an $\mathcal O_F$-order of $D$;
- `e`: the basis;
- `re_succ`: $\operatorname{re}e_{l+1} = 0$ for $l = 0, 1, 2$;
- `re_zero`: $\operatorname{re}e_0 \ne 0$. -/
structure TZFrame (O : Subalgebra (𝓞 F) (QuatF F a b)) where
  isOrder : IsOrder (𝓞 F) F O
  e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)
  re_succ : ∀ l : Fin 3, (e l.succ : QuatF F a b).re = 0
  re_zero : (e 0 : QuatF F a b).re ≠ 0

variable (fr : TZFrame O)

/-- The matrix $P$ of $i, j, k$-coordinates of $e_1, e_2, e_3$ (column $l$ = coordinates of $e_{l+1}$). -/
def TZFrame.Pm : Matrix (Fin 3) (Fin 3) F := Matrix.of fun r l => imv (fr.e l.succ : QuatF F a b) r

theorem sum_pure (y : Fin 3 → F) (c : Fin 3 → Fin 3 → F) :
    (Quat.pure (∑ l, y l • c l) : QuatF F a b) = ∑ l, y l • (Quat.pure (c l) : QuatF F a b) := by
  simp only [Fin.sum_univ_three, pure_add, pure_smul]

theorem TZFrame.psiP_eq (y : Fin 3 → F) :
    (psiP fr.Pm y : QuatF F a b) = ∑ l, y l • (fr.e l.succ : QuatF F a b) := by
  have h1 : fr.Pm *ᵥ y = ∑ l, y l • (fun r => fr.Pm r l) := by
    ext r; simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [psiP, h1, sum_pure]
  refine Finset.sum_congr rfl fun l _ => ?_
  have : (fun r => fr.Pm r l) = imv (fr.e l.succ : QuatF F a b) := rfl
  rw [this, pure_imv (fr.re_succ l)]

theorem TZFrame.det_Pm_ne_zero : fr.Pm.det ≠ 0 := by
  intro h0
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hli : LinearIndependent F fun i => (fr.e i : QuatF F a b) := by
    have : Submodule.IsLattice F (Subalgebra.toSubmodule O) := ⟨fr.isOrder.fg, fr.isOrder.span⟩
    have h : ⇑(fr.e.extendOfIsLattice F) = fun i => (fr.e i : QuatF F a b) :=
      funext fun i => Module.Basis.extendOfIsLattice_apply F fr.e i
    rw [← h]; exact (fr.e.extendOfIsLattice F).linearIndependent
  have hs : ∑ l, y l • (fr.e l.succ : QuatF F a b) = 0 := by
    rw [← fr.psiP_eq, psiP, hy]; ext <;> simp [Quat.pure]
  have hli' := hli.comp Fin.succ (Fin.succ_injective _)
  have := (Fintype.linearIndependent_iff.1 hli') y hs
  exact hy0 (funext this)

/-- $P$ as an element of $GL_3(F)$. -/
def TZFrame.PG : GL (Fin 3) F := ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 fr.det_Pm_ne_zero)).unit

@[simp] theorem TZFrame.PG_val : (fr.PG : Matrix (Fin 3) (Fin 3) F) = fr.Pm := rfl

/-- **The ternary form of $\mathcal O^0$** in the coordinates $e_1, e_2, e_3$: $Q_{\mathcal O^0} = \langle -a,-b,ab\rangle\circ P$, so
$Q_{\mathcal O^0}(y) = \operatorname{nrd}(\sum_l y_le_{l+1})$ (`TZFrame.eval_QF`). -/
def TZFrame.QF : QuadForm F 3 := (pureForm (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b)).compMat fr.Pm

theorem TZFrame.eval_QF (y : Fin 3 → F) : fr.QF.eval y = nrd (∑ l, y l • (fr.e l.succ : QuatF F a b)) := by
  rw [← fr.psiP_eq, nrd_psiP]; rfl

end Frame

/-! ### The local conjugation maps -/

section LocalMaps

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)} (fr : TZFrame O)
  (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem isInteger_iff_le_one' (x : Fv) : IsInteger 𝔬 x ↔ Valued.v x ≤ 1 := by
  constructor
  · rintro ⟨c, hc⟩; rw [← hc]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 c.2
  · intro h; exact ⟨⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h⟩, rfl⟩

/-- $P$ over $F_v$. -/
def TZFrame.PGv : GL (Fin 3) Fv := Matrix.GeneralLinearGroup.map (algebraMap F Fv) fr.PG

theorem TZFrame.PGv_val : (fr.PGv v : Matrix (Fin 3) (Fin 3) Fv) = fr.Pm.map (algebraMap F Fv) := rfl

theorem pureForm_map (K : Type*) [Field K] [Algebra F K] (a' b' : F) :
    (pureForm a' b').map (algebraMap F K) = pureForm (algebraMap F K a') (algebraMap F K b') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pureForm, QuadForm.diag, QuadForm.map]

theorem TZFrame.hessian_QF_map :
    fr.QF.hessian.map (algebraMap F Fv) =
      ((pureForm (algebraMap 𝔬 Fv (ι v a)) (algebraMap 𝔬 Fv (ι v b))).compMat
        (fr.PGv v : Matrix (Fin 3) (Fin 3) Fv)).hessian := by
  rw [← QuadForm.hessian_map, TZFrame.QF, ← QuadForm.map_compMat, pureForm_map, TZFrame.PGv_val]
  rfl

theorem TZFrame.hessian_QF_map_self :
    fr.QF.hessian.map (algebraMap F F) =
      ((pureForm (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b)).compMat (fr.PG : Matrix (Fin 3) (Fin 3) F)).hessian := by
  simp [TZFrame.QF]

theorem two_ne_zero_Fv : (2 : Fv) ≠ 0 := two_ne_zero_of_algebra (F := F) Fv

/-- **The local conjugation map** $c_v : D_v^\times \to O(Q_{\mathcal O^0})(F_v)$, $c_v(x) = P^{-1}\,\mathrm{conj}(x)\,P$. -/
def TZFrame.cvv : (QuatV v a b)ˣ →* orthGroup fr.QF Fv where
  toFun x := ⟨cvHom (fr.PGv v) x, by
    rw [mem_orthGroup, fr.hessian_QF_map v]
    exact cvHom_hessian (two_ne_zero_Fv v) _ x⟩
  map_one' := by ext1; exact map_one _
  map_mul' x y := by ext1; exact map_mul _ _ _

@[simp] theorem TZFrame.cvv_coe (x : (QuatV v a b)ˣ) :
    ((fr.cvv v x : orthGroup fr.QF Fv) : GL (Fin 3) Fv) = cvHom (fr.PGv v) x := rfl

theorem TZFrame.cvv_mem_soSub (x : (QuatV v a b)ˣ) : fr.cvv v x ∈ soSub fr.QF Fv := det_cvHom _ x

/-- **The global conjugation map** $c : D^\times \to O(Q_{\mathcal O^0})(F)$. -/
def TZFrame.cv0 : (QuatF F a b)ˣ →* orthGroup fr.QF F where
  toFun x := ⟨cvHom fr.PG x, by
    rw [mem_orthGroup, fr.hessian_QF_map_self]
    exact cvHom_hessian two_ne_zero _ x⟩
  map_one' := by ext1; exact map_one _
  map_mul' x y := by ext1; exact map_mul _ _ _

@[simp] theorem TZFrame.cv0_coe (x : (QuatF F a b)ˣ) :
    ((fr.cv0 x : orthGroup fr.QF F) : GL (Fin 3) F) = cvHom fr.PG x := rfl

/-- The completion map on units. -/
def complUnits : (QuatF F a b)ˣ →* (QuatV v a b)ˣ := Units.map (complHom v a b).toMonoidHom

@[simp] theorem coe_complUnits (x : (QuatF F a b)ˣ) :
    ((complUnits v x : (QuatV v a b)ˣ) : QuatV v a b) = complHom v a b (x : QuatF F a b) := rfl

theorem complHom_pure (y : Fin 3 → F) :
    complHom v a b (Quat.pure y : QuatF F a b) = Quat.pure (fun r => algebraMap F Fv (y r)) := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · rw [complHom_re]; simp [Quat.pure]
  · rw [complHom_imI]; simp [Quat.pure]
  · rw [complHom_imJ]; simp [Quat.pure]
  · rw [complHom_imK]; simp [Quat.pure]

theorem imv_complHom (z : QuatF F a b) : imv (complHom v a b z) = fun r => algebraMap F Fv (imv z r) := by
  funext r; fin_cases r <;> rfl

theorem toMatrix'_conjLin_complUnits (x : (QuatF F a b)ˣ) :
    LinearMap.toMatrix' (conjLin (complUnits v x)) = (LinearMap.toMatrix' (conjLin x)).map (algebraMap F Fv) := by
  ext i j
  rw [LinearMap.toMatrix'_apply, Matrix.map_apply, LinearMap.toMatrix'_apply, conjLin_apply, conjLin_apply]
  have hs : (Quat.pure (Pi.single j 1) : QuatV v a b) = complHom v a b (Quat.pure (Pi.single j 1)) := by
    rw [complHom_pure]; congr 1; funext r; by_cases h : r = j <;> simp [Pi.single_apply, h]
  rw [hs, coe_complUnits, ← map_inv, coe_complUnits, ← map_mul, ← map_mul, imv_complHom]

/-- **Compatibility with the diagonal embedding:** $\iota_v(c(\beta)) = c_v(\iota_v\beta)$. -/
theorem TZFrame.orthMap_cv0 (x : (QuatF F a b)ˣ) :
    orthMap fr.QF Fv (fr.cv0 x) = fr.cvv v (complUnits v x) := by
  ext1
  apply Units.ext
  rw [orthMap_val]
  change (cvHom fr.PG x : Matrix (Fin 3) (Fin 3) F).map (algebraMap F Fv) = (cvHom (fr.PGv v) (complUnits v x) : Matrix _ _ Fv)
  rw [cvHom_val, cvHom_val, Matrix.map_mul, Matrix.map_mul, toMatrix'_conjLin_complUnits]
  rfl

end LocalMaps

/-! ### The local lattice $\mathcal O_v^0$ -/

section LocalLattice

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) (QuatF F a b)} (fr : TZFrame O) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The local ternary lattice** $\mathcal O_v^0 = \mathfrak o_ve_1 + \mathfrak o_ve_2 + \mathfrak o_ve_3 \subseteq D_v$. -/
def TZFrame.Ov0 : Submodule 𝔬 (QuatV v a b) :=
  Submodule.span 𝔬 (Set.range fun l : Fin 3 => complHom v a b (fr.e l.succ : QuatF F a b))

/-- The coordinate map $\psi_v : F_v^3 \to D_v^0$, $y \mapsto \sum_ly_le_{l+1}$. -/
def TZFrame.psiv (y : Fin 3 → Fv) : QuatV v a b := psiP (fr.PGv v : Matrix (Fin 3) (Fin 3) Fv) y

theorem TZFrame.psiv_eq (y : Fin 3 → Fv) :
    fr.psiv v y = ∑ l, y l • complHom v a b (fr.e l.succ : QuatF F a b) := by
  have h1 : (fr.PGv v : Matrix (Fin 3) (Fin 3) Fv) *ᵥ y = ∑ l, y l • (fun r => algebraMap F Fv (fr.Pm r l)) := by
    ext r; simp [mulVec, dotProduct, Finset.sum_apply, mul_comm, TZFrame.PGv_val]
  rw [TZFrame.psiv, psiP, h1]
  simp only [Fin.sum_univ_three, pure_add, pure_smul]
  have hc : ∀ l : Fin 3, (Quat.pure (fun r => algebraMap F Fv (fr.Pm r l)) : QuatV v a b) =
      complHom v a b (fr.e l.succ : QuatF F a b) := by
    intro l
    rw [← complHom_pure]
    congr 1
    exact pure_imv (fr.re_succ l)
  rw [hc, hc, hc]

theorem TZFrame.re_complHom_e_succ (l : Fin 3) : (complHom v a b (fr.e l.succ : QuatF F a b)).re = 0 := by
  rw [complHom_re, fr.re_succ l, map_zero]

theorem TZFrame.re_complHom_e_zero : (complHom v a b (fr.e 0 : QuatF F a b)).re ≠ 0 := by
  rw [complHom_re]; exact (map_ne_zero _).2 fr.re_zero

/-- The re-part of an element in terms of its coordinates in the completed basis. -/
theorem TZFrame.re_eq_repr (z : QuatV v a b) :
    z.re = (complBasis (v := v) fr.e fr.isOrder).repr z 0 * (complHom v a b (fr.e 0 : QuatF F a b)).re := by
  conv_lhs => rw [← (complBasis (v := v) fr.e fr.isOrder).sum_repr z]
  rw [Fin.sum_univ_four]
  simp only [QuaternionAlgebra.re_add, QuaternionAlgebra.re_smul, complBasis_apply, complBasisVec, smul_eq_mul]
  have h1 := fr.re_complHom_e_succ v 0
  have h2 := fr.re_complHom_e_succ v 1
  have h3 := fr.re_complHom_e_succ v 2
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h1 h2 h3
  have h3' : (complHom v a b (fr.e 3 : QuatF F a b)).re = 0 := h3
  rw [h1, h2, h3']; ring

/-- **$\mathcal O_v^0$ by coordinates:** $z \in \mathcal O_v^0$ iff its $e_0$-coordinate vanishes and the others are integral. -/
theorem TZFrame.mem_Ov0_iff_repr (z : QuatV v a b) :
    z ∈ fr.Ov0 v ↔ (complBasis (v := v) fr.e fr.isOrder).repr z 0 = 0 ∧
      ∀ l : Fin 3, IsInteger 𝔬 ((complBasis (v := v) fr.e fr.isOrder).repr z l.succ) := by
  set B := complBasis (v := v) fr.e fr.isOrder
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, rfl⟩ := hz
      dsimp only
      have hB : complHom v a b (fr.e l.succ : QuatF F a b) = B l.succ := by rw [complBasis_apply]; rfl
      rw [hB, Module.Basis.repr_self]
      refine ⟨by simp [Finsupp.single_apply, Fin.succ_ne_zero], fun m => ?_⟩
      by_cases h : l = m
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Finsupp.single_apply, (Fin.succ_injective _).ne h]⟩
    | zero => exact ⟨by simp, fun m => ⟨0, by simp⟩⟩
    | add y z _ _ hy hz =>
      refine ⟨by rw [map_add, Finsupp.add_apply, hy.1, hz.1, add_zero], fun m => ?_⟩
      obtain ⟨p, hp⟩ := hy.2 m; obtain ⟨q, hq⟩ := hz.2 m
      exact ⟨p + q, by rw [map_add, hp, hq, map_add, Finsupp.add_apply]⟩
    | smul c y _ hy =>
      refine ⟨?_, fun m => ?_⟩
      · rw [← algebraMap_smul Fv c y, map_smul, Finsupp.smul_apply, hy.1, smul_zero]
      · obtain ⟨p, hp⟩ := hy.2 m
        refine ⟨c * p, ?_⟩
        rw [← algebraMap_smul Fv c y, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hp]
  · rintro ⟨h0, h⟩
    choose c hc using h
    rw [← B.sum_repr z, Fin.sum_univ_succ, h0, zero_smul, zero_add]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [← hc l, algebraMap_smul, complBasis_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

/-- **$\mathcal O_v^0$ is the trace-zero part of $\mathcal O_v$.** -/
theorem TZFrame.mem_Ov0_iff (z : QuatV v a b) : z ∈ fr.Ov0 v ↔ z ∈ localOrder (v := v) a b O ∧ z.re = 0 := by
  rw [fr.mem_Ov0_iff_repr, mem_localOrder_iff fr.e fr.isOrder, fr.re_eq_repr,
    mul_eq_zero, or_iff_left (fr.re_complHom_e_zero v)]
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨fun i => ?_, h0⟩
    refine Fin.cases ?_ (fun l => h l) i
    rw [h0]; exact ⟨0, by simp⟩
  · rintro ⟨h, h0⟩
    exact ⟨h0, fun l => h l.succ⟩

theorem TZFrame.Ov0_le : ∀ z ∈ fr.Ov0 v, z ∈ localOrder (v := v) a b O := fun z hz => ((fr.mem_Ov0_iff v z).1 hz).1

theorem TZFrame.repr_psiv (y : Fin 3 → Fv) :
    (complBasis (v := v) fr.e fr.isOrder).repr (fr.psiv v y) = Finsupp.equivFunOnFinite.symm (Fin.cons 0 y) := by
  apply (complBasis (v := v) fr.e fr.isOrder).repr.symm.injective
  rw [LinearEquiv.symm_apply_apply, Module.Basis.repr_symm_apply, fr.psiv_eq, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype _ _ (fun i => by simp)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, complBasis_apply, complBasisVec, add_zero,
    Finsupp.coe_equivFunOnFinite_symm, Fin.cons_zero, Fin.cons_succ, zero_smul, zero_add]

/-- **$\psi_v$ maps $\mathfrak o_v^3$ onto $\mathcal O_v^0$:** $y \in \mathfrak o_v^3$ iff $\psi_v(y) \in \mathcal O_v^0$. -/
theorem TZFrame.psiv_mem_Ov0_iff (y : Fin 3 → Fv) : fr.psiv v y ∈ fr.Ov0 v ↔ y ∈ std (n := 3) v := by
  rw [fr.mem_Ov0_iff_repr, fr.repr_psiv]
  simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.cons_zero, Fin.cons_succ, true_and]
  change (∀ l, IsInteger 𝔬 (y l)) ↔ ∀ i, Valued.v (y i) ≤ exp (-(0 : ℤ))
  simp only [neg_zero, WithZero.exp_zero]
  exact forall_congr' fun l => isInteger_iff_le_one' v (y l)

theorem TZFrame.exists_psiv_eq {z : QuatV v a b} (hz : z.re = 0) : ∃ y, fr.psiv v y = z := by
  refine ⟨((fr.PGv v)⁻¹ : GL (Fin 3) Fv).val *ᵥ imv z, ?_⟩
  rw [TZFrame.psiv, psiP, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, pure_imv hz]

theorem TZFrame.psiv_cvv (x : (QuatV v a b)ˣ) (y : Fin 3 → Fv) :
    fr.psiv v (((fr.cvv v x : orthGroup fr.QF Fv) : GL (Fin 3) Fv).val *ᵥ y) =
      (x : QuatV v a b) * fr.psiv v y * ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) :=
  psiP_cvHom (fr.PGv v) x y

/-- Conjugation preserving $\mathcal O_v^0$ (one direction). -/
def ConjPres (S : Submodule 𝔬 (QuatV v a b)) (x : (QuatV v a b)ˣ) : Prop :=
  ∀ z ∈ S, (x : QuatV v a b) * z * ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) ∈ S

theorem TZFrame.cvv_mulVec_mem_std_iff (x : (QuatV v a b)ˣ) :
    (∀ y ∈ std (n := 3) v, ((fr.cvv v x : orthGroup fr.QF Fv) : GL (Fin 3) Fv).val *ᵥ y ∈ std (n := 3) v) ↔
      ConjPres v (fr.Ov0 v) x := by
  constructor
  · intro h z hz
    obtain ⟨y, rfl⟩ := fr.exists_psiv_eq v ((fr.mem_Ov0_iff v z).1 hz).2
    rw [← fr.psiv_cvv, fr.psiv_mem_Ov0_iff]
    exact h y ((fr.psiv_mem_Ov0_iff v y).1 hz)
  · intro h y hy
    rw [← fr.psiv_mem_Ov0_iff, fr.psiv_cvv]
    exact h _ ((fr.psiv_mem_Ov0_iff v y).2 hy)

/-- **$c_v(x)$ stabilizes $\mathfrak o_v^3$ iff conjugation by $x$ preserves $\mathcal O_v^0$** (both ways). -/
theorem TZFrame.cvv_mem_stdStab_iff (x : (QuatV v a b)ˣ) :
    fr.cvv v x ∈ stdStab fr.QF v ↔ ConjPres v (fr.Ov0 v) x ∧ ConjPres v (fr.Ov0 v) x⁻¹ := by
  rw [← fr.cvv_mulVec_mem_std_iff, ← fr.cvv_mulVec_mem_std_iff]
  change locAct v _ (std v) = std v ↔ _
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · rw [← h]; exact ⟨y, hy, rfl⟩
    · have h' := (locAct_eq_iff (v := v)).1 h
      rw [h']
      refine ⟨y, hy, ?_⟩
      rw [map_inv]; rfl
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩; exact h1 y hy
    · intro y hy
      refine ⟨_, h2 y hy, ?_⟩
      change ((fr.cvv v x : orthGroup fr.QF Fv) : GL (Fin 3) Fv).val *ᵥ
        (((fr.cvv v x⁻¹ : orthGroup fr.QF Fv) : GL (Fin 3) Fv).val *ᵥ y) = y
      rw [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, ← map_mul, mul_inv_cancel, map_one]
      simp

/-! ### The subgroup $K'_v = c_v(\mathcal O_v^\times)$ -/

/-- The unit group $\mathcal O_v^\times$ as a subgroup of $D_v^\times$. -/
def unitsOv : Subgroup (QuatV v a b)ˣ where
  carrier := {x | (x : QuatV v a b) ∈ localOrder (v := v) a b O ∧ ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) ∈ localOrder (v := v) a b O}
  mul_mem' {x y} hx hy := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact Subalgebra.mul_mem _ hx.1 hy.1
    · rw [_root_.mul_inv_rev, Units.val_mul]; exact Subalgebra.mul_mem _ hy.2 hx.2
  one_mem' := ⟨by rw [Units.val_one]; exact Subalgebra.one_mem _, by rw [inv_one, Units.val_one]; exact Subalgebra.one_mem _⟩
  inv_mem' {x} hx := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

theorem mem_unitsOv {x : (QuatV v a b)ˣ} :
    x ∈ unitsOv (O := O) v ↔ (x : QuatV v a b) ∈ localOrder (v := v) a b O ∧
      ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) ∈ localOrder (v := v) a b O := Iff.rfl

/-- **$K'_v = c_v(\mathcal O_v^\times)$.** -/
def TZFrame.Kv : Subgroup (orthGroup fr.QF Fv) := (unitsOv (O := O) v).map (fr.cvv v)

theorem conjPres_of_mem_unitsOv {x : (QuatV v a b)ˣ} (hx : x ∈ unitsOv (O := O) v) : ConjPres v (fr.Ov0 v) x := by
  intro z hz
  rw [fr.mem_Ov0_iff] at hz ⊢
  refine ⟨Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hx.1 hz.1) hx.2, ?_⟩
  -- the trace is invariant under conjugation
  have h := congrArg QuaternionAlgebra.re (show (x : QuatV v a b) * z * ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) =
      (x : QuatV v a b) * z * ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) from rfl)
  have hz0 : z = Quat.pure (imv z) := (pure_imv hz.2).symm
  rw [hz0]
  exact re_conj x (imv z)

theorem TZFrame.Kv_le_stdStab : fr.Kv v ≤ stdStab fr.QF v := by
  rintro _ ⟨x, hx, rfl⟩
  rw [fr.cvv_mem_stdStab_iff]
  exact ⟨conjPres_of_mem_unitsOv fr v hx, conjPres_of_mem_unitsOv fr v ((unitsOv v).inv_mem hx)⟩

theorem TZFrame.Kv_le_soSub : fr.Kv v ≤ soSub fr.QF Fv := by
  rintro _ ⟨x, -, rfl⟩
  exact fr.cvv_mem_soSub v x

theorem algebraMap_mem_localOrder (c : 𝔬) : algebraMap Fv (QuatV v a b) (c : Fv) ∈ localOrder (v := v) a b O := by
  have : algebraMap Fv (QuatV v a b) (c : Fv) = algebraMap 𝔬 (QuatV v a b) c := rfl
  rw [this]; exact Subalgebra.algebraMap_mem _ c

/-- **$c_v(x) \in K'_v$ iff $x \in F_v^\times\mathcal O_v^\times$** ($a \ne 0$). -/
theorem TZFrame.cvv_mem_Kv_iff (ha : a ≠ 0) (x : (QuatV v a b)ˣ) :
    fr.cvv v x ∈ fr.Kv v ↔ ∃ (r : Fv) (u : (QuatV v a b)ˣ), u ∈ unitsOv (O := O) v ∧
      (x : QuatV v a b) = algebraMap Fv (QuatV v a b) r * u := by
  have ha' : algebraMap 𝔬 Fv (ι v a) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v ha)
  constructor
  · rintro ⟨u, hu, hxu⟩
    have h : cvHom (fr.PGv v) x = cvHom (fr.PGv v) u := by
      have := congrArg (fun g : orthGroup fr.QF Fv => (g : GL (Fin 3) Fv)) hxu
      exact this.symm
    obtain ⟨r, hr⟩ := (cvHom_eq_iff (two_ne_zero_Fv v) ha' _ x u).1 h
    exact ⟨r, u, hu, hr⟩
  · rintro ⟨r, u, hu, hx⟩
    refine ⟨u, hu, ?_⟩
    ext1
    exact ((cvHom_eq_iff (two_ne_zero_Fv v) ha' _ x u).2 ⟨r, hx⟩).symm

end LocalLattice

end QuadFormsKB.QuatOrder
