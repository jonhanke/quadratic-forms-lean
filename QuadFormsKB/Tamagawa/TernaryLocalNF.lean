/-
# The trace-zero lattice of a maximal order, locally, for every class number

**Layer:** $F$ a number field (any class number), $D = (a,b)_F$ with $a, b \in \mathcal O_F\setminus0$, $\mathcal O \subseteq D$ an order,
$L = $ `pureLat hO` the trace-zero lattice $\mathcal O^0$ in the coordinates $i, j, k$, $Q = \langle -a,-b,ab\rangle$
over $F$ (`QP a b`), $v$ a finite place. No basis of $\mathcal O$, of $\mathcal O^0$ or of an ideal is chosen; coordinates are always $i, j, k$
(`TernaryConj` with $P = 1$).

**The completion of the trace-zero lattice.**
`Ov0NF v O` $= \{z \in \mathcal O_v : \operatorname{re}z = 0\}$, and **`mem_loc_pureSub_iff`**:
$y \in L_v$ iff $y_1i + y_2j + y_3k \in \mathcal O_v$
(completion commutes with the kernel of the reduced trace; the elementary argument with a local frame and the trace of minimal valuation,
`Ov0NF_eq_span`).

**The local conjugation maps.** The maps $c_v : D_v^\times \to O(Q)(F_v)$ (`cvvNF`), $c_v(x) \in O(L_v)$ iff
conjugation by $x$ preserves $\mathcal O_v^0$
(`cvvNF_stab_iff`), $K'_v = c_v(\mathcal O_v^\times)$ (`KvNF`), contained in $SO(L_v)$; split places: $SO(L_v)\cap c_v(D_v^\times) = K'_v$
(`mem_KvNF_of_stab_split`); ramified places: every $c_v(x)$ stabilizes $L_v$ and $c_v(x) \in K'_v$ iff $\operatorname{ord}_v\operatorname{nrd}x$ is even.

Source: Voight 2021, §§9.5, 13.3, 22.1; Weil 1982, §3.7(a). Port of `TernaryFrame`/`TernaryLocalStab` without frames.
-/
import QuadFormsKB.Tamagawa.TernaryIndex
import QuadFormsKB.Tamagawa.OrderNormFormNF
import QuadFormsKB.Tamagawa.QuatClassFiniteNF
import QuadFormsKB.Tamagawa.IdealIndexNF
import QuadFormsKB.Tamagawa.MassSOLatNF

open NumberField IsDedekindDomain Matrix Quaternion WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity.NF IsLocalization
  QuadFormsKB.QuatZeta

/-! ### The completion of the trace-zero lattice -/

section E2

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The local trace-zero lattice** $\mathcal O_v^0 = \{z \in \mathcal O_v : \operatorname{re}z = 0\}$. -/
def Ov0NF (O : Subalgebra (𝓞 F) (QuatF F a b)) : Submodule 𝔬 (QuatV v a b) where
  carrier := {z | z ∈ localOrder (v := v) a b O ∧ z.re = 0}
  add_mem' := fun ⟨hx, hx0⟩ ⟨hy, hy0⟩ => ⟨Subalgebra.add_mem _ hx hy, by simp [hx0, hy0]⟩
  zero_mem' := ⟨Subalgebra.zero_mem _, rfl⟩
  smul_mem' := fun c x ⟨hx, hx0⟩ => ⟨Subalgebra.smul_mem _ hx c, by
    rw [← algebraMap_smul Fv c x]; simp [hx0]⟩

variable {v}

theorem mem_Ov0NF {O : Subalgebra (𝓞 F) (QuatF F a b)} {z : QuatV v a b} :
    z ∈ Ov0NF v O ↔ z ∈ localOrder (v := v) a b O ∧ z.re = 0 := Iff.rfl

theorem complHom_pureTup {x : QuatF F a b} (hx : x.re = 0) :
    complHom v a b x = Quat.pure (locVec v (pureTup a b x)) := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · rw [complHom_re, hx, map_zero]; rfl
  · rw [complHom_imI]; rfl
  · rw [complHom_imJ]; rfl
  · rw [complHom_imK]; rfl

theorem imv_complHom_eq_locVec (x : QuatF F a b) : imv (complHom v a b x) = locVec v (pureTup a b x) := by
  funext i; fin_cases i <;> rfl

/-- The coordinates $(z_1, z_2, z_3)$ of $z \in D_v$, as an $\mathfrak o_v$-linear map. -/
def imvL : QuatV v a b →ₗ[𝔬] (Fin 3 → Fv) where
  toFun := imv
  map_add' := imv_add
  map_smul' c z := by
    rw [← algebraMap_smul Fv c z, imv_smul]; rfl

theorem span_complHom_traceZero_le (O : Subalgebra (𝓞 F) (QuatF F a b)) :
    Submodule.span 𝔬 (complHom v a b '' (traceZeroSub O : Set (QuatF F a b))) ≤ Ov0NF v O := by
  rw [Submodule.span_le]
  rintro _ ⟨x, ⟨hxO, hx0⟩, rfl⟩
  exact ⟨mem_localOrder_of_mem a b hxO, by rw [complHom_re, hx0, map_zero]⟩

/-- **The key inclusion:** every trace-zero element of $\mathcal O_v$ is an $\mathfrak o_v$-combination of images of
trace-zero elements of $\mathcal O$. *Proof:* write $z = \sum c_kE_k$ in a local frame ($E_k = \iota(f_k)$, $c_k \in \mathfrak o_v$),
$t_k = \operatorname{re}f_k$; if $t_{k_0}$ has minimal valuation then $s_k = t_k/t_{k_0}$ is $v$-integral, $s_k = n_k/d_k$ with
$d_k \notin \mathfrak p_v$, $\sum c_ks_k = 0$, and $z = \sum_k(c_k/d_k)\,\iota(d_kf_k - n_kf_{k_0})$ with $d_kf_k - n_kf_{k_0} \in \mathcal O^0$. -/
theorem Ov0NF_le_span {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O) :
    Ov0NF v O ≤ Submodule.span 𝔬 (complHom v a b '' (traceZeroSub O : Set (QuatF F a b))) := by
  classical
  intro z ⟨hz, hz0⟩
  set S := Submodule.span 𝔬 (complHom v a b '' (traceZeroSub O : Set (QuatF F a b)))
  obtain ⟨L⟩ := LocFrame.exists (v := v) hO
  have hc := (L.mem_localOrder_iff z).1 hz
  choose c hc using hc
  have hzsum : z = ∑ i, (c i : Fv) • L.cvec i := by
    conv_lhs => rw [← L.cb.sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LocFrame.cb_apply, ← hc i]; rfl
  set t : Fin 4 → F := fun i => (L.fb i).re
  have hre : ∑ i, (c i : Fv) * algebraMap F Fv (t i) = 0 := by
    have := congrArg QuaternionAlgebra.re hzsum
    simp only [Fin.sum_univ_four, QuaternionAlgebra.re_add, QuaternionAlgebra.re_smul, smul_eq_mul] at this
    rw [Fin.sum_univ_four, hz0.symm.trans this]
    simp only [LocFrame.cvec, complHom_re, t]
  by_cases hall : ∀ i, t i = 0
  · rw [hzsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [show ((c i : Fv)) • L.cvec i = c i • L.cvec i from algebraMap_smul Fv (c i) _]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨L.fb i, ⟨L.mem i, hall i⟩, rfl⟩)
  push Not at hall
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 4)) (fun i => v.valuation F (t i))
    Finset.univ_nonempty
  have ht0 : t i₀ ≠ 0 := by
    obtain ⟨j, hj⟩ := hall
    intro h0
    have := hmax j (Finset.mem_univ _)
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hj this
  have hs : ∀ i, v.valuation F (t i / t i₀) ≤ 1 := fun i => by
    rw [map_div₀, div_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 ht0))]
    exact hmax i (Finset.mem_univ _)
  choose n d hnd using fun i => HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (t i / t i₀) (hs i)
  -- the trace-zero elements `w i = d i • f i - n i • f i₀`
  set w : Fin 4 → QuatF F a b := fun i => (d i : 𝓞 F) • L.fb i - n i • L.fb i₀
  have hd0 : ∀ i, algebraMap (𝓞 F) F (d i : 𝓞 F) ≠ 0 := fun i h =>
    (d i).2 (by rw [(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).1 h]; exact v.asIdeal.zero_mem)
  have hnd' : ∀ i, algebraMap (𝓞 F) F (n i) = algebraMap (𝓞 F) F (d i : 𝓞 F) * (t i / t i₀) := fun i => by
    rw [← hnd i]; ring
  have hw : ∀ i, w i ∈ traceZeroSub O := fun i => by
    refine ⟨O.sub_mem (O.smul_mem (L.mem i) _) (O.smul_mem (L.mem i₀) _), ?_⟩
    simp only [w, QuaternionAlgebra.re_sub]
    rw [← algebraMap_smul F (d i : 𝓞 F), ← algebraMap_smul F (n i), QuaternionAlgebra.re_smul,
      QuaternionAlgebra.re_smul, smul_eq_mul, smul_eq_mul, hnd' i]
    change _ * t i - _ * (t i / t i₀) * t i₀ = 0
    field_simp; ring
  -- `d i` is a unit in `𝔬`
  have hdu : ∀ i, IsUnit (ι v (d i : 𝓞 F)) := fun i => Gen.isUnit_ι_of_not_mem (d i).2
  have hcw : ∀ i, complHom v a b (w i) = algebraMap 𝔬 Fv (ι v (d i : 𝓞 F)) • L.cvec i -
      algebraMap 𝔬 Fv (ι v (n i)) • L.cvec i₀ := fun i => by
    simp only [w, map_sub, complHom_int_smul, LocFrame.cvec]
    rw [show ∀ (r : 𝔬) (y : QuatV v a b), algebraMap 𝔬 Fv r • y = r • y from fun r y => algebraMap_smul Fv r y,
      show ∀ (r : 𝔬) (y : QuatV v a b), algebraMap 𝔬 Fv r • y = r • y from fun r y => algebraMap_smul Fv r y]
  -- the relation `∑ c i * s i = 0`
  have hrel : ∑ i, (c i : Fv) * (algebraMap 𝔬 Fv (ι v (n i)) / algebraMap 𝔬 Fv (ι v (d i : 𝓞 F))) = 0 := by
    have ht0' : algebraMap F Fv (t i₀) ≠ 0 := (map_ne_zero _).2 ht0
    have e : ∀ i, algebraMap 𝔬 Fv (ι v (n i)) / algebraMap 𝔬 Fv (ι v (d i : 𝓞 F)) =
        algebraMap F Fv (t i) / algebraMap F Fv (t i₀) := fun i => by
      have h1 : algebraMap 𝔬 Fv (ι v (n i)) = algebraMap F Fv (algebraMap (𝓞 F) F (n i)) := rfl
      have h2 : algebraMap 𝔬 Fv (ι v (d i : 𝓞 F)) = algebraMap F Fv (algebraMap (𝓞 F) F (d i : 𝓞 F)) := rfl
      have h3 : algebraMap F Fv (algebraMap (𝓞 F) F (d i : 𝓞 F)) ≠ 0 := (map_ne_zero _).2 (hd0 i)
      rw [h1, h2, hnd' i, map_mul, map_div₀]
      field_simp
    simp_rw [e, ← mul_div_assoc, ← Finset.sum_div, hre, zero_div]
  -- rewrite `z`
  have hz' : z = ∑ i, ((c i : Fv) / algebraMap 𝔬 Fv (ι v (d i : 𝓞 F))) • complHom v a b (w i) := by
    have hdF : ∀ i, algebraMap 𝔬 Fv (ι v (d i : 𝓞 F)) ≠ 0 := fun i =>
      (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (hdu i).ne_zero
    simp_rw [hcw, smul_sub, smul_smul]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    have e1 : ∀ i, (c i : Fv) / algebraMap 𝔬 Fv (ι v (d i : 𝓞 F)) * algebraMap 𝔬 Fv (ι v (d i : 𝓞 F)) = c i :=
      fun i => div_mul_cancel₀ _ (hdF i)
    have e2 : ∑ i, (c i : Fv) / algebraMap 𝔬 Fv (ι v (d i : 𝓞 F)) * algebraMap 𝔬 Fv (ι v (n i)) = 0 := by
      rw [← hrel]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    simp_rw [e1, e2, zero_smul, sub_zero]
    exact hzsum
  rw [hz']
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨u, hu⟩ := hdu i
  have : ((c i : Fv) / algebraMap 𝔬 Fv (ι v (d i : 𝓞 F))) = algebraMap 𝔬 Fv (c i * (u⁻¹ : 𝔬ˣ)) := by
    rw [map_mul, ← hu, div_eq_mul_inv]
    congr 1
    rw [eq_comm]
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  rw [this, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w i, hw i, rfl⟩)

theorem Ov0NF_eq_span {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O) :
    Ov0NF v O = Submodule.span 𝔬 (complHom v a b '' (traceZeroSub O : Set (QuatF F a b))) :=
  le_antisymm (Ov0NF_le_span hO) (span_complHom_traceZero_le O)

/-- **The completion of the trace-zero lattice is the trace-zero part of the completion**:
$y \in (\mathcal O^0)_v$ iff $y_1i + y_2j + y_3k \in \mathcal O_v$. -/
@[kb "voight2021" "Lemma 9.5.3 (completion of lattices); §22.1 (the ternary lattice O⁰)"]
theorem mem_loc_pureSub_iff {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O) (y : Fin 3 → Fv) :
    y ∈ loc v (pureSub O) ↔ (Quat.pure y : QuatV v a b) ∈ Ov0NF v O := by
  have hloc : loc v (pureSub O) = (Ov0NF v O).map (imvL (v := v) (a := a) (b := b)) := by
    rw [Ov0NF_eq_span hO, Submodule.map_span, loc]
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨complHom v a b x, ⟨x, hx, rfl⟩, imv_complHom_eq_locVec x⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨pureTup a b x, ⟨x, hx, rfl⟩, (imv_complHom_eq_locVec x).symm⟩
  rw [hloc]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have : (Quat.pure (imv z) : QuatV v a b) = z := pure_imv hz.2
    change (Quat.pure (imv z) : QuatV v a b) ∈ _
    rw [this]; exact hz
  · intro h
    exact ⟨_, h, by funext i; fin_cases i <;> rfl⟩

end E2

/-! ### The local conjugation maps and $K'_v$ -/

/-- **The ternary form** $Q = \langle -a,-b,ab\rangle$ over $F$ (`pureFormO` over $F$). -/
abbrev QP {F : Type} [Field F] [NumberField F] (a b : 𝓞 F) : QuadForm F 3 := (pureFormO a b).map (algebraMap (𝓞 F) F)

section E3

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}
  (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem hessian_QP_map :
    (QP a b).hessian.map (algebraMap F Fv) =
      ((pureForm (algebraMap 𝔬 Fv (ι v a)) (algebraMap 𝔬 Fv (ι v b))).compMat
        ((1 : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv)).hessian := by
  rw [← QuadForm.hessian_map, QP, map_pureFormO, pureForm_map, Units.val_one, QuadForm.compMat_one]
  rfl

theorem hessian_QP_map_self :
    (QP a b).hessian.map (algebraMap F F) =
      ((pureForm (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b)).compMat
        ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).hessian := by
  rw [Units.val_one, QuadForm.compMat_one, QP, map_pureFormO]
  ext i j; simp

/-- **The local conjugation map** $c_v : D_v^\times \to O(Q)(F_v)$, $c_v(x)y = $ the coordinates of $x\,(y_1i+y_2j+y_3k)\,x^{-1}$. -/
def cvvNF : (QuatV v a b)ˣ →* orthGroup (QP a b) Fv where
  toFun x := ⟨cvHom 1 x, by
    rw [mem_orthGroup, hessian_QP_map v]
    exact cvHom_hessian (two_ne_zero_Fv v) _ x⟩
  map_one' := by ext1; exact map_one _
  map_mul' x y := by ext1; exact map_mul _ _ _

@[simp] theorem cvvNF_coe (x : (QuatV v a b)ˣ) :
    ((cvvNF v x : orthGroup (QP a b) Fv) : GL (Fin 3) Fv) = cvHom 1 x := rfl

theorem cvvNF_mem_soSub (x : (QuatV v a b)ˣ) : cvvNF v x ∈ soSub (QP a b) Fv := det_cvHom _ x

/-- **The global conjugation map** $c : D^\times \to O(Q)(F)$. -/
def cv0NF : (QuatF F a b)ˣ →* orthGroup (QP a b) F where
  toFun x := ⟨cvHom 1 x, by
    rw [mem_orthGroup, hessian_QP_map_self]
    exact cvHom_hessian two_ne_zero _ x⟩
  map_one' := by ext1; exact map_one _
  map_mul' x y := by ext1; exact map_mul _ _ _

@[simp] theorem cv0NF_coe (x : (QuatF F a b)ˣ) :
    ((cv0NF x : orthGroup (QP a b) F) : GL (Fin 3) F) = cvHom 1 x := rfl

/-- **Compatibility with the diagonal embedding:** $\iota_v(c(\beta)) = c_v(\iota_v\beta)$. -/
theorem orthMap_cv0NF (x : (QuatF F a b)ˣ) :
    orthMap (QP a b) Fv (cv0NF x) = cvvNF v (complUnits v x) := by
  ext1
  apply Units.ext
  rw [orthMap_val]
  change (cvHom (1 : GL (Fin 3) F) x : Matrix (Fin 3) (Fin 3) F).map (algebraMap F Fv) =
    (cvHom (1 : GL (Fin 3) Fv) (complUnits v x) : Matrix _ _ Fv)
  rw [cvHom_val, cvHom_val, Matrix.map_mul, Matrix.map_mul, toMatrix'_conjLin_complUnits]
  simp

theorem pure_cvvNF_mulVec (x : (QuatV v a b)ˣ) (y : Fin 3 → Fv) :
    (Quat.pure (((cvvNF v x : orthGroup (QP a b) Fv) : GL (Fin 3) Fv).val *ᵥ y) : QuatV v a b) =
      (x : QuatV v a b) * Quat.pure y * ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) := by
  have h := psiP_cvHom (1 : GL (Fin 3) Fv) x y
  simp only [psiP, Units.val_one, one_mulVec] at h
  exact h

theorem cvvNF_mulVec_mem_iff (hO : IsOrder (𝓞 F) F O) (x : (QuatV v a b)ˣ) :
    (∀ y ∈ loc v (pureSub O), ((cvvNF v x : orthGroup (QP a b) Fv) : GL (Fin 3) Fv).val *ᵥ y ∈ loc v (pureSub O)) ↔
      ConjPres v (Ov0NF v O) x := by
  constructor
  · intro h z hz
    have hz0 : (Quat.pure (imv z) : QuatV v a b) = z := pure_imv hz.2
    have hy : imv z ∈ loc v (pureSub O) := (mem_loc_pureSub_iff hO _).2 (by rw [hz0]; exact hz)
    have := (mem_loc_pureSub_iff hO _).1 (h _ hy)
    rwa [pure_cvvNF_mulVec, hz0] at this
  · intro h y hy
    rw [mem_loc_pureSub_iff hO, pure_cvvNF_mulVec]
    exact h _ ((mem_loc_pureSub_iff hO y).1 hy)

/-- **$c_v(x)$ stabilizes $L_v$ iff conjugation by $x$ preserves $\mathcal O_v^0$** (both ways). -/
theorem cvvNF_stab_iff (hO : IsOrder (𝓞 F) F O) (x : (QuatV v a b)ˣ) :
    locAct v ((cvvNF v x : orthGroup (QP a b) Fv) : GL (Fin 3) Fv) (loc v (pureSub O)) = loc v (pureSub O) ↔
      ConjPres v (Ov0NF v O) x ∧ ConjPres v (Ov0NF v O) x⁻¹ := by
  rw [← cvvNF_mulVec_mem_iff v hO, ← cvvNF_mulVec_mem_iff v hO]
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
      change ((cvvNF v x : orthGroup (QP a b) Fv) : GL (Fin 3) Fv).val *ᵥ
        (((cvvNF v x⁻¹ : orthGroup (QP a b) Fv) : GL (Fin 3) Fv).val *ᵥ y) = y
      rw [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, ← map_mul, mul_inv_cancel, map_one]
      simp

/-- **$K'_v = c_v(\mathcal O_v^\times)$.** -/
def KvNF (O : Subalgebra (𝓞 F) (QuatF F a b)) : Subgroup (orthGroup (QP a b) Fv) := (unitsOv (O := O) v).map (cvvNF v)

theorem conjPres_of_mem_unitsOv_nf {x : (QuatV v a b)ˣ} (hx : x ∈ unitsOv (O := O) v) : ConjPres v (Ov0NF v O) x := by
  intro z hz
  refine ⟨Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hx.1 hz.1) hx.2, ?_⟩
  have hz0 : z = Quat.pure (imv z) := (pure_imv hz.2).symm
  rw [hz0]
  exact re_conj x (imv z)

theorem KvNF_le_stab (hO : IsOrder (𝓞 F) F O) {g : orthGroup (QP a b) Fv} (hg : g ∈ KvNF v O) :
    locAct v (g : GL (Fin 3) Fv) (loc v (pureSub O)) = loc v (pureSub O) := by
  obtain ⟨x, hx, rfl⟩ := hg
  exact (cvvNF_stab_iff v hO x).2 ⟨conjPres_of_mem_unitsOv_nf v hx,
    conjPres_of_mem_unitsOv_nf v ((unitsOv v).inv_mem hx)⟩

theorem KvNF_le_soSub : KvNF v O ≤ soSub (QP a b) Fv := by
  rintro _ ⟨x, -, rfl⟩
  exact cvvNF_mem_soSub v x

/-- **$c_v(x) \in K'_v$ iff $x \in F_v^\times\mathcal O_v^\times$** ($a \ne 0$). -/
theorem cvvNF_mem_KvNF_iff (ha : a ≠ 0) (x : (QuatV v a b)ˣ) :
    cvvNF v x ∈ KvNF v O ↔ ∃ (r : Fv) (u : (QuatV v a b)ˣ), u ∈ unitsOv (O := O) v ∧
      (x : QuatV v a b) = algebraMap Fv (QuatV v a b) r * u := by
  have ha' : algebraMap 𝔬 Fv (ι v a) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v ha)
  constructor
  · rintro ⟨u, hu, hxu⟩
    have h : cvHom (1 : GL (Fin 3) Fv) x = cvHom 1 u := by
      have := congrArg (fun g : orthGroup (QP a b) Fv => (g : GL (Fin 3) Fv)) hxu
      exact this.symm
    obtain ⟨r, hr⟩ := (cvHom_eq_iff (two_ne_zero_Fv v) ha' _ x u).1 h
    exact ⟨r, u, hu, hr⟩
  · rintro ⟨r, u, hu, hx⟩
    refine ⟨u, hu, ?_⟩
    ext1
    exact ((cvHom_eq_iff (two_ne_zero_Fv v) ha' _ x u).2 ⟨r, hx⟩).symm

theorem cvvNF_scalar (ha : a ≠ 0) {r : Fv} (hr : r ≠ 0) : cvvNF (a := a) (b := b) v (qScalar r hr) = 1 := by
  have ha' : algebraMap 𝔬 Fv (ι v a) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v ha)
  ext1
  exact (cvHom_eq_one_iff (two_ne_zero_Fv v) ha' _ _).2 ⟨r, rfl⟩

theorem exists_cvvNF_eq (ha : a ≠ 0) (hb : b ≠ 0) (g : orthGroup (QP a b) Fv) (hg : g ∈ soSub (QP a b) Fv) :
    ∃ y : (QuatV v a b)ˣ, cvvNF v y = g := by
  have hmem := (mem_orthGroup (QP a b)).1 g.2
  rw [hessian_QP_map v] at hmem
  have ha' : algebraMap 𝔬 Fv (ι v a) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v ha)
  have hb' : algebraMap 𝔬 Fv (ι v b) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v hb)
  obtain ⟨α, hα⟩ := exists_cvHom_eq (two_ne_zero_Fv v) ha' hb' 1 _ hmem hg
  exact ⟨α, Subtype.ext hα⟩

/-! #### Split places -/

section Split

variable (φ : QuatV v a b ≃ₐ[v.adicCompletion F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
  (hφ : (localOrder (v := v) a b O).map ((φ : QuatV v a b →ₐ[v.adicCompletion F] _).restrictScalars
    (v.adicCompletionIntegers F)) = matOrder (v.adicCompletionIntegers F) (v.adicCompletion F))

include hφ in
theorem mem_localOrder_iff_split_nf (z : QuatV v a b) : z ∈ localOrder (v := v) a b O ↔ φ z ∈ matOrder 𝔬 Fv := by
  rw [← hφ]
  constructor
  · intro hz; exact ⟨z, hz, rfl⟩
  · rintro ⟨w, hw, hwz⟩
    have : w = z := φ.injective hwz
    rwa [← this]

theorem trd_eq_trace_nf (z : QuatV v a b) : trd z = (φ z).trace := by
  have h1 := det_algEquiv φ (1 + z)
  rw [map_add, map_one] at h1
  have h2 := det_algEquiv φ z
  have h3 : nrd (1 + z) = 1 + trd z + nrd z := by
    simp only [nrd, trd, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
      QuaternionAlgebra.imK_add, QuaternionAlgebra.re_one, QuaternionAlgebra.imI_one, QuaternionAlgebra.imJ_one,
      QuaternionAlgebra.imK_one]
    ring
  have h4 : (1 + φ z).det = 1 + (φ z).trace + (φ z).det := by
    rw [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]; simp; ring
  rw [h3, h4, h2] at h1
  linear_combination h1.symm

theorem re_eq_zero_iff_trace_nf (z : QuatV v a b) : z.re = 0 ↔ (φ z).trace = 0 := by
  rw [← trd_eq_trace_nf v φ, trd]
  constructor
  · intro h; rw [h, mul_zero]
  · intro h; exact (mul_eq_zero.1 h).resolve_left two_ne_zero

include hφ in
theorem E12_mem_nf : E12 v φ ∈ Ov0NF v O := by
  rw [mem_Ov0NF, mem_localOrder_iff_split_nf v φ hφ, re_eq_zero_iff_trace_nf v φ, E12, AlgEquiv.apply_symm_apply]
  exact ⟨single_mem_matOrder 0 1, by simp [Matrix.trace_fin_two]⟩

include hφ in
theorem E21_mem_nf : E21 v φ ∈ Ov0NF v O := by
  rw [mem_Ov0NF, mem_localOrder_iff_split_nf v φ hφ, re_eq_zero_iff_trace_nf v φ, E21, AlgEquiv.apply_symm_apply]
  exact ⟨single_mem_matOrder 1 0, by simp [Matrix.trace_fin_two]⟩

include hφ in
theorem exists_decomp_nf {w : QuatV v a b} (hw : w ∈ localOrder (v := v) a b O) :
    ∃ c : Fin 2 → Fin 2 → 𝔬, w = (c 0 0 : Fv) • (E12 v φ * E21 v φ) + (c 0 1 : Fv) • E12 v φ +
      (c 1 0 : Fv) • E21 v φ + (c 1 1 : Fv) • (E21 v φ * E12 v φ) := by
  have hm := (mem_matOrder).1 ((mem_localOrder_iff_split_nf v φ hφ w).1 hw)
  choose c hc using hm
  refine ⟨c, φ.injective ?_⟩
  simp only [map_add, map_smul, map_mul, E12, E21, AlgEquiv.apply_symm_apply]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single_mul_single_same, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, hc,
      Matrix.mul_apply, Fin.sum_univ_two] <;> exact (hc _ _).symm

theorem conj_smul_nf (x : (QuatV v a b)ˣ) (c : Fv) (z : QuatV v a b) :
    (x : QuatV v a b) * (c • z) * ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) =
      c • ((x : QuatV v a b) * z * ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b)) := by
  rw [mul_smul_comm, smul_mul_assoc]

theorem conj_mul_nf (x : (QuatV v a b)ˣ) (y z : QuatV v a b) :
    (x : QuatV v a b) * (y * z) * ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) =
      ((x : QuatV v a b) * y * ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b)) *
        ((x : QuatV v a b) * z * ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b)) := by
  simp only [mul_assoc, Units.inv_mul_cancel_left]

include hφ in
/-- **At a split place, preserving $\mathcal O_v^0$ means preserving $\mathcal O_v$.** -/
theorem conj_mem_localOrder_of_conjPres_nf {x : (QuatV v a b)ˣ} (hx : ConjPres v (Ov0NF v O) x)
    {w : QuatV v a b} (hw : w ∈ localOrder (v := v) a b O) :
    (x : QuatV v a b) * w * ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) ∈ localOrder (v := v) a b O := by
  obtain ⟨c, rfl⟩ := exists_decomp_nf v φ hφ hw
  have h12 := (hx _ (E12_mem_nf v φ hφ)).1
  have h21 := (hx _ (E21_mem_nf v φ hφ)).1
  simp only [mul_add, add_mul, conj_smul_nf, conj_mul_nf]
  have hsm : ∀ (d : 𝔬) {z : QuatV v a b}, z ∈ localOrder (v := v) a b O → (d : Fv) • z ∈ localOrder (v := v) a b O :=
    fun d z hz => by
      rw [show (d : Fv) • z = d • z from (algebraMap_smul Fv d z).symm]
      exact Subalgebra.smul_mem _ hz d
  refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _ ?_ ?_) ?_) ?_
  · exact hsm _ (Subalgebra.mul_mem _ h12 h21)
  · exact hsm _ h12
  · exact hsm _ h21
  · exact hsm _ (Subalgebra.mul_mem _ h21 h12)

include hφ in
/-- **At a split place, $SO(L_v) \cap c_v(D_v^\times) = c_v(\mathcal O_v^\times)$.** -/
theorem mem_KvNF_of_stab_split (hO : IsOrder (𝓞 F) F O) (ha : a ≠ 0) (x : (QuatV v a b)ˣ)
    (hx : locAct v ((cvvNF v x : orthGroup (QP a b) Fv) : GL (Fin 3) Fv) (loc v (pureSub O)) = loc v (pureSub O)) :
    cvvNF v x ∈ KvNF v O := by
  have hpres := ((cvvNF_stab_iff v hO x).1 hx).1
  set X := matUnit v φ x
  have hX : ∀ E ∈ matOrder 𝔬 Fv, X.val * E * (X⁻¹).val ∈ matOrder 𝔬 Fv := by
    intro E hE
    have hE' : φ.symm E ∈ localOrder (v := v) a b O := by
      rw [mem_localOrder_iff_split_nf v φ hφ, AlgEquiv.apply_symm_apply]; exact hE
    have := conj_mem_localOrder_of_conjPres_nf v φ hφ hpres hE'
    rw [mem_localOrder_iff_split_nf v φ hφ, map_mul, map_mul, AlgEquiv.apply_symm_apply] at this
    exact this
  obtain ⟨r, hr, h1, h2⟩ := exists_scalar_mul_unit_of_conj v X hX
  set u : (QuatV v a b)ˣ := qScalar r⁻¹ (inv_ne_zero hr) * x
  have hu : u ∈ unitsOv (O := O) v := by
    refine ⟨?_, ?_⟩
    · rw [mem_localOrder_iff_split_nf v φ hφ]
      have hu' : (u : QuatV v a b) = algebraMap Fv (QuatV v a b) r⁻¹ * x := by rw [Units.val_mul, coe_qScalar]
      rw [hu', map_mul, AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
      exact h1
    · rw [mem_localOrder_iff_split_nf v φ hφ]
      have hXi : (X⁻¹).val = φ ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) := rfl
      have hui : ((u⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) =
          ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) * algebraMap Fv (QuatV v a b) r := by
        simp only [u, _root_.mul_inv_rev, Units.val_mul, qScalar_inv, coe_qScalar, inv_inv]
      rw [hui, map_mul, AlgEquiv.commutes, ← hXi, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one]
      exact h2
  rw [cvvNF_mem_KvNF_iff v ha]
  refine ⟨r, u, hu, ?_⟩
  simp only [u, Units.val_mul, coe_qScalar, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hr, map_one, one_mul]

end Split

/-! #### Ramified places -/

section Ramified

variable (hdiv : ∀ x : QuatV v a b, nrd x = 0 → x = 0)
  (heq : localOrder (v := v) a b O = valOrder (R := v.adicCompletionIntegers F) hdiv)

include heq in
theorem conjPres_ramified_nf (x : (QuatV v a b)ˣ) : ConjPres v (Ov0NF v O) x := by
  intro z hz
  rw [mem_Ov0NF, heq] at hz ⊢
  refine ⟨?_, ?_⟩
  · rw [mem_valOrder, nrd_mul, nrd_mul, mul_comm, ← mul_assoc, ← nrd_mul, Units.inv_mul, nrd_one, one_mul]
    exact hz.1
  · have hz0 : z = Quat.pure (imv z) := (pure_imv hz.2).symm
    rw [hz0]; exact re_conj x (imv z)

include heq in
/-- **At a ramified place every $c_v(x)$ stabilizes $L_v$.** -/
theorem cvvNF_stab_ramified (hO : IsOrder (𝓞 F) F O) (x : (QuatV v a b)ˣ) :
    locAct v ((cvvNF v x : orthGroup (QP a b) Fv) : GL (Fin 3) Fv) (loc v (pureSub O)) = loc v (pureSub O) :=
  (cvvNF_stab_iff v hO x).2 ⟨conjPres_ramified_nf v hdiv heq x, conjPres_ramified_nf v hdiv heq x⁻¹⟩

include heq in
theorem mem_unitsOv_ramified_iff_nf (u : (QuatV v a b)ˣ) :
    u ∈ unitsOv (O := O) v ↔ Valued.v (nrd (u : QuatV v a b)) = 1 := by
  change (u : QuatV v a b) ∈ localOrder (v := v) a b O ∧
    ((u⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) ∈ localOrder (v := v) a b O ↔ _
  rw [heq, mem_valOrder, mem_valOrder, inv_eq, nrd_smul, nrd_star, isInteger_iff_le_one,
    isInteger_iff_le_one]
  have hn := nrd_units_ne_zero u
  rw [show (nrd (u : QuatV v a b))⁻¹ ^ 2 * nrd (u : QuatV v a b) = (nrd (u : QuatV v a b))⁻¹ by
    field_simp]
  rw [map_inv₀]
  constructor
  · rintro ⟨h1, h2⟩
    have hpos : 0 < Valued.v (nrd (u : QuatV v a b)) := zero_lt_iff.2 ((map_ne_zero _).2 hn)
    exact le_antisymm h1 ((inv_le_one₀ hpos).1 h2)
  · intro h; rw [h]; simp

include heq in
/-- **At a ramified place, $c_v(x) \in K'_v$ iff $\operatorname{nrd}x$ has even valuation.** -/
theorem cvvNF_mem_KvNF_iff_even (ha : a ≠ 0) (x : (QuatV v a b)ˣ) (k : ℤ)
    (hk : Valued.v (nrd (x : QuatV v a b)) = exp k) : cvvNF v x ∈ KvNF v O ↔ Even k := by
  rw [cvvNF_mem_KvNF_iff v ha]
  constructor
  · rintro ⟨r, u, hu, hx⟩
    have hu1 := (mem_unitsOv_ramified_iff_nf v hdiv heq u).1 hu
    have hr : r ≠ 0 := by
      rintro rfl
      exact x.ne_zero (by rw [hx, map_zero, zero_mul])
    obtain ⟨m, hm⟩ := exists_valued_eq_exp v hr
    rw [hx, nrd_mul, map_mul, hu1] at hk
    have : nrd (algebraMap Fv (QuatV v a b) r) = r ^ 2 := by
      simp [nrd, QuaternionAlgebra.algebraMap_eq]; try ring
    rw [this, mul_one, map_pow, hm, ← WithZero.exp_nsmul, WithZero.exp_inj] at hk
    exact ⟨m, by rw [← hk]; simp; ring⟩
  · rintro ⟨m, rfl⟩
    set r : Fv := algebraMap F Fv (unifF v ^ (-m))
    have hr : r ≠ 0 := by
      intro h0
      have := valued_unifF_zpow v (-m)
      rw [show algebraMap F Fv (unifF v ^ (-m)) = r from rfl, h0, map_zero] at this
      exact WithZero.exp_ne_zero this.symm
    set u : (QuatV v a b)ˣ := qScalar r⁻¹ (inv_ne_zero hr) * x
    have hu : u ∈ unitsOv (O := O) v := by
      rw [mem_unitsOv_ramified_iff_nf v hdiv heq]
      have : nrd (algebraMap Fv (QuatV v a b) r⁻¹) = r⁻¹ ^ 2 := by
        simp [nrd, QuaternionAlgebra.algebraMap_eq]; try ring
      simp only [u, Units.val_mul, coe_qScalar, nrd_mul, this, map_mul, map_pow, map_inv₀, hk]
      have hvr : Valued.v r = exp m := by
        rw [valued_unifF_zpow]; simp
      rw [hvr, ← WithZero.exp_neg, ← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.exp_eq_one]
      simp; ring
    refine ⟨r, u, hu, ?_⟩
    simp only [u, Units.val_mul, coe_qScalar, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hr, map_one, one_mul]

end Ramified

/-- An element of reduced norm of valuation $e^{-1}$ exists. -/
theorem exists_nrd_odd_nf (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x : (QuatV v a b)ˣ, Valued.v (nrd (x : QuatV v a b)) = exp (-1 : ℤ) := by
  have ha' : algebraMap (𝓞 F) F a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
  have hb' : algebraMap (𝓞 F) F b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb
  have hc : algebraMap F Fv (unifF v) ≠ 0 := (map_ne_zero _).2 (unifF_ne_zero v)
  obtain ⟨y, hy⟩ := exists_nrd_eq_finite' ha' hb' v hc
  have hy0 : nrd y ≠ 0 := by rw [hy]; exact hc
  refine ⟨((isUnit_iff_nrd_ne_zero y).2 hy0).unit, ?_⟩
  change Valued.v (nrd y) = _
  rw [hy, valued_algebraMap, valuation_unifF]

/-- Every quaternion becomes integral after multiplying by a power of $\varpi_v$ (no basis: a local frame). -/
theorem exists_pi_pow_mul_mem_localOrder (hO : IsOrder (𝓞 F) F O) (z : QuatV v a b) :
    ∃ N : ℕ, algebraMap Fv (QuatV v a b) (algebraMap 𝔬 Fv (π v) ^ N) * z ∈ localOrder (v := v) a b O := by
  classical
  obtain ⟨L⟩ := LocFrame.exists (v := v) hO
  have hN := fun i => exists_pow_mul_isInteger_π (v := v) (L.cb.repr z i)
  choose N hN using hN
  set M := Finset.univ.sup N
  refine ⟨M, (L.mem_localOrder_iff _).2 fun i => ?_⟩
  rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hle : N i ≤ M := Finset.le_sup (f := N) (Finset.mem_univ i)
  rw [show algebraMap 𝔬 Fv (π v) ^ M = algebraMap 𝔬 Fv (π v) ^ (M - N i) * algebraMap 𝔬 Fv (π v) ^ N i by
    rw [← pow_add]; congr 1; omega, mul_assoc]
  obtain ⟨c, hc⟩ := hN i
  refine ⟨π v ^ (M - N i) * c, ?_⟩
  rw [map_mul, map_pow, hc]

/-- **The bad set of an element of $SO(Q)(\mathbb A_f)$ is finite:** $h_v \in K'_v$ for almost all $v$ ($\mathcal O$ maximal). -/
theorem finite_not_mem_KvNF (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {h : OAf (QP a b)}
    (hh : h ∈ soAf (QP a b)) : {w | h w ∉ KvNF w O}.Finite := by
  have h1 : {w | h w ∉ stdStab (QP a b) w}.Finite := h.2
  have h2 : (↑(ramFin ha hb) : Set (HeightOneSpectrum (𝓞 F))).Finite := Finset.finite_toSet _
  have h3 : {w : HeightOneSpectrum (𝓞 F) | ¬ loc w (pureSub O) = std w}.Finite :=
    Filter.eventually_cofinite.mp (loc_eventually_std (pureLat hO.1).2)
  refine ((h1.union h2).union h3).subset fun w hw => ?_
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Finset.mem_coe] at hcon
  obtain ⟨⟨hstd, hram⟩, hloc⟩ := hcon
  apply hw
  obtain ⟨y, hy⟩ := exists_cvvNF_eq w ha hb (h w) (hh w)
  have hφ : ∃ φ : QuatV w a b ≃ₐ[w.adicCompletion F] Matrix (Fin 2) (Fin 2) (w.adicCompletion F),
      (localOrder (v := w) a b O).map ((φ : QuatV w a b →ₐ[w.adicCompletion F] _).restrictScalars
        (w.adicCompletionIntegers F)) = matOrder (w.adicCompletionIntegers F) (w.adicCompletion F) := by
    rcases localOrder_ramified_or_split_nf (v := w) ha hb hO with ⟨hd, -⟩ | h'
    · exfalso; apply hram
      rw [Gen.mem_ramFin]
      intro x hx
      exact (isUnit_iff_nrd_ne_zero x).2 fun h0 => hx (hd x h0)
    · exact h'
  obtain ⟨φ, hφ⟩ := hφ
  rw [← hy]
  refine mem_KvNF_of_stab_split w φ hφ hO.1 ha y ?_
  rw [hy, hloc]
  exact hstd

end E3

end QuadFormsKB.QuatOrder
