/-
# Trace-zero frames exist; the integral form of $\mathcal O^0$; $\tau(\langle -a,-b,ab\rangle) = \tau(\mathcal O^0)$

**Layer:** $F$ a number field with $\mathcal O_F$ a PID, $D = (a,b)_F$, $\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$ an order.

**Proves**
* `exists_TZFrame`: $\mathcal O$ has a trace-zero frame (Smith normal form of the trace-zero submodule $\mathcal O^0 \le \mathcal O$,
  which is saturated, so a basis of $\mathcal O$ extends a basis of $\mathcal O^0$);
* `TZFrame.exists_Q0`: the ternary form $Q_{\mathcal O^0}$ is integral (a `QuadForm (𝓞 F) 3`);
* `TZFrame.tauSO_pureFormO_eq`: $\tau(SO(\langle -a,-b,ab\rangle)) = \tau(SO(Q_{\mathcal O^0}))$ (the lattice independence:
  $\mathcal O_F\langle i,j,k\rangle \subseteq \mathcal O^0$).

Source: Voight 2021, §22.1 (the ternary lattice $\mathcal O^0$); Weil 1982, §2.2.1, p. 14.
-/
import QuadFormsKB.Tamagawa.TernaryIndex

open NumberField IsDedekindDomain Matrix Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.QuadForm QuadFormsKB.QuatZeta
  IsLocalization

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) (QuatF F a b)}

theorem algebraMap_int_quatF (c : 𝓞 F) :
    algebraMap (𝓞 F) (QuatF F a b) c = ((algebraMap (𝓞 F) F c : F) : QuatF F a b) := rfl

theorem coe_smul_quatF (c : 𝓞 F) (x : Subalgebra.toSubmodule O) :
    ((c • x : Subalgebra.toSubmodule O) : QuatF F a b) = (algebraMap (𝓞 F) F c) • (x : QuatF F a b) := by
  rw [Submodule.coe_smul, Algebra.smul_def, algebraMap_int_quatF, QuaternionAlgebra.coe_mul_eq_smul]

/-- The trace-zero submodule of $\mathcal O$ (as a submodule of $\mathcal O$ viewed as a module). -/
def tzSub (O : Subalgebra (𝓞 F) (QuatF F a b)) : Submodule (𝓞 F) (Subalgebra.toSubmodule O) where
  carrier := {x | (x : QuatF F a b).re = 0}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, Submodule.coe_add, QuaternionAlgebra.re_add] at *; rw [hx, hy, add_zero]
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq] at *
    rw [coe_smul_quatF, QuaternionAlgebra.re_smul, hx, smul_zero]

theorem mem_tzSub {x : Subalgebra.toSubmodule O} : x ∈ tzSub O ↔ (x : QuatF F a b).re = 0 := Iff.rfl

/-- **Trace-zero frames exist** ($\mathcal O_F$ a PID, $\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$). -/
theorem exists_TZFrame (hO : IsOrder (𝓞 F) F O) (hstd : stdOrder F a b ≤ O) : Nonempty (TZFrame O) := by
  classical
  obtain ⟨bas⟩ := exists_basis_order hO
  obtain ⟨n, snf⟩ := (tzSub O).smithNormalForm bas
  haveI := Module.Finite.of_basis snf.bN
  -- elements of N have trace zero, and the bM (f i) do
  have hfz : ∀ i : Fin n, ((snf.bM (snf.f i) : Subalgebra.toSubmodule O) : QuatF F a b).re = 0 := by
    intro i
    have h1 : ((snf.bN i : tzSub O) : Subalgebra.toSubmodule O) ∈ tzSub O := (snf.bN i).2
    rw [snf.snf, mem_tzSub, coe_smul_quatF, QuaternionAlgebra.re_smul, smul_eq_mul] at h1
    have ha0 : snf.a i ≠ 0 := by
      intro h0
      have := snf.snf i
      rw [h0, zero_smul] at this
      exact snf.bN.ne_zero i (Subtype.ext this)
    exact (mul_eq_zero.1 h1).resolve_left ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha0)
  -- 1 is not of trace zero, so not every basis vector has zero real part
  have hone : ¬ ∀ j : Fin 4, ((snf.bM j : Subalgebra.toSubmodule O) : QuatF F a b).re = 0 := by
    intro hT
    have h1 : (⟨1, O.one_mem⟩ : Subalgebra.toSubmodule O) = ∑ j, snf.bM.repr ⟨1, O.one_mem⟩ j • snf.bM j :=
      (snf.bM.sum_repr _).symm
    have h2 := congrArg (fun x : Subalgebra.toSubmodule O => (x : QuatF F a b).re) h1
    simp only [Fin.sum_univ_four, Submodule.coe_add, coe_smul_quatF, QuaternionAlgebra.re_add,
      QuaternionAlgebra.re_smul, hT, smul_zero, add_zero] at h2
    simp at h2
  -- n = 3
  have hn3 : n ≤ 3 := by
    by_contra h
    have hn4 : n = 4 := by
      have := Fintype.card_le_of_embedding snf.f
      simp only [Fintype.card_fin] at this; omega
    subst hn4
    have hsurj : Function.Surjective snf.f := ((Fintype.bijective_iff_injective_and_card _).2
      ⟨snf.f.injective, by simp⟩).2
    exact hone fun j => by obtain ⟨i, rfl⟩ := hsurj j; exact hfz i
  have hn3' : 3 ≤ n := by
    have hi : (⟨qi, hstd (qi_mem_stdOrder a b)⟩ : Subalgebra.toSubmodule O) ∈ tzSub O := by
      simp [mem_tzSub, qi]
    have hj : (⟨qj, hstd (qj_mem_stdOrder a b)⟩ : Subalgebra.toSubmodule O) ∈ tzSub O := by
      simp [mem_tzSub, qj]
    have hk : (⟨qk, hstd (qk_mem_stdOrder a b)⟩ : Subalgebra.toSubmodule O) ∈ tzSub O := by
      simp [mem_tzSub, qk]
    let v3 : Fin 3 → tzSub O := ![⟨_, hi⟩, ⟨_, hj⟩, ⟨_, hk⟩]
    have hli' : LinearIndependent (𝓞 F)
        (((Subalgebra.toSubmodule O).subtype.comp (tzSub O).subtype) ∘ v3) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      simp only [Fin.sum_univ_three, Function.comp_apply, LinearMap.coe_comp, Submodule.coe_subtype, v3,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Algebra.smul_def,
        algebraMap_int_quatF] at hc
      have e1 := congrArg QuaternionAlgebra.imI hc
      have e2 := congrArg QuaternionAlgebra.imJ hc
      have e3 := congrArg QuaternionAlgebra.imK hc
      simp [qi, qj, qk] at e1 e2 e3
      fin_cases i
      · exact e1
      · exact e2
      · exact e3
    have hli : LinearIndependent (𝓞 F) v3 := hli'.of_comp _
    have := hli.fintype_card_le_finrank
    rw [Module.finrank_eq_card_basis snf.bN, Fintype.card_fin, Fintype.card_fin] at this
    exact this
  have hn : n = 3 := le_antisymm hn3 hn3'
  subst hn
  -- the remaining index
  have hcomp : ((Finset.univ.map snf.f)ᶜ).card = 1 := by
    rw [Finset.card_compl, Finset.card_map, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  obtain ⟨i0, hi0⟩ := Finset.card_eq_one.1 hcomp
  have hmem0 : ∀ j, j ∈ (Finset.univ.map snf.f)ᶜ ↔ j = i0 := fun j => by rw [hi0, Finset.mem_singleton]
  have hi0' : i0 ∉ Set.range snf.f := by
    have := (hmem0 i0).2 rfl
    simpa [Finset.mem_compl] using this
  have hre0 : ((snf.bM i0 : Subalgebra.toSubmodule O) : QuatF F a b).re ≠ 0 := by
    intro h0
    refine hone fun j => ?_
    by_cases hj : j ∈ Set.range snf.f
    · obtain ⟨i, rfl⟩ := hj; exact hfz i
    · have : j ∈ (Finset.univ.map snf.f)ᶜ := by simpa [Finset.mem_compl] using hj
      rw [(hmem0 j).1 this]; exact h0
  -- reindex
  let g : Fin 4 → Fin 4 := Fin.cons i0 (fun l : Fin 3 => snf.f l)
  have hg : Function.Bijective g := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨Fin.cons_injective_iff.2 ⟨hi0', snf.f.injective⟩, rfl⟩
  let e := snf.bM.reindex (Equiv.ofBijective g hg).symm
  have he : ∀ k, e k = snf.bM (g k) := fun k => by simp [e]
  exact ⟨⟨hO, e, fun l => by rw [he]; exact hfz l, by rw [he]; exact hre0⟩⟩

/-- **The ternary norm form of $\mathcal O^0$ is integral.** -/
theorem TZFrame.exists_Q0 (fr : TZFrame O) : ∃ Q₀ : QuadForm (𝓞 F) 3, Q₀.map (algebraMap (𝓞 F) F) = fr.QF := by
  have key : ∀ y : Fin 3 → F, (∀ l, IsInteger (𝓞 F) (y l)) → IsInteger (𝓞 F) (fr.QF.eval y) := by
    intro y hy
    choose c hc using hy
    rw [fr.eval_QF]
    have : ∑ l, y l • (fr.e l.succ : QuatF F a b) ∈ O :=
      Subalgebra.sum_mem _ fun l _ => by
        rw [← hc l, algebraMap_smul]; exact Subalgebra.smul_mem _ (fr.e l.succ).2 _
    exact (isInteger_trd_nrd fr.isOrder this).2
  have hsingle : ∀ l k, IsInteger (𝓞 F) ((Pi.single k (1 : F) : Fin 3 → F) l) := by
    intro l k; by_cases h : l = k
    · subst h; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [h]⟩
  have hint : ∀ i j, IsInteger (𝓞 F) (fr.QF.coeff i j) := by
    intro i j
    by_cases hij : i ≤ j
    · rcases hij.lt_or_eq with hlt | rfl
      · rw [coeff_eq_polar fr.QF hlt]
        obtain ⟨u, hu⟩ := key (Pi.single i 1 + Pi.single j 1) fun l => by
          obtain ⟨p, hp⟩ := hsingle l i; obtain ⟨q, hq⟩ := hsingle l j
          exact ⟨p + q, by simp only [map_add, hp, hq, Pi.add_apply]⟩
        obtain ⟨v, hv⟩ := key (Pi.single i 1) (fun l => hsingle l i)
        obtain ⟨w, hw⟩ := key (Pi.single j 1) (fun l => hsingle l j)
        exact ⟨u - v - w, by rw [map_sub, map_sub, hu, hv, hw]⟩
      · rw [← eval_single]; exact key _ fun l => hsingle l i
    · exact ⟨0, by rw [map_zero, fr.QF.upper (not_le.1 hij)]⟩
  exact exists_map_eq_of_isInteger fr.QF hint

/-- **$\tau(\langle -a,-b,ab\rangle) = \tau(Q_{\mathcal O^0})$** ($\mathcal O_F\langle i,j,k\rangle \subseteq \mathcal O^0$). -/
theorem TZFrame.tauSO_pureFormO_eq (fr : TZFrame O) (hstd : stdOrder F a b ≤ O)
    (hpd : IsTotallyPosDef ((pureFormO a b).map (algebraMap (𝓞 F) F))) (Q₀ : QuadForm (𝓞 F) 3)
    (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) : tauSO (pureFormO a b) = tauSO Q₀ := by
  classical
  -- coordinates of i, j, k in the frame
  let qv : Fin 3 → QuatF F a b := ![qi, qj, qk]
  have hqO : ∀ m, qv m ∈ O := by
    intro m; fin_cases m
    · exact hstd (qi_mem_stdOrder a b)
    · exact hstd (qj_mem_stdOrder a b)
    · exact hstd (qk_mem_stdOrder a b)
  have hqre : ∀ m, (qv m).re = 0 := by intro m; fin_cases m <;> simp [qv, qi, qj, qk]
  let G : Matrix (Fin 3) (Fin 3) (𝓞 F) := Matrix.of fun l m => fr.e.repr ⟨qv m, hqO m⟩ l.succ
  have hsum : ∀ m, ∑ l, algebraMap (𝓞 F) F (G l m) • (fr.e l.succ : QuatF F a b) = qv m := by
    intro m
    have h := congrArg Subtype.val (fr.e.sum_repr ⟨qv m, hqO m⟩)
    rw [Submodule.coe_sum, Fin.sum_univ_succ] at h
    have h0 : fr.e.repr ⟨qv m, hqO m⟩ 0 = 0 := by
      have h2 := congrArg QuaternionAlgebra.re h
      simp only [Fin.sum_univ_three, Submodule.coe_add, coe_smul_quatF, QuaternionAlgebra.re_add,
        QuaternionAlgebra.re_smul, fr.re_succ, smul_zero, add_zero, hqre, smul_eq_mul, mul_zero] at h2
      exact (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).1
        ((mul_eq_zero.1 h2).resolve_right fr.re_zero)
    rw [h0, zero_smul, ZeroMemClass.coe_zero, zero_add] at h
    refine Eq.trans ?_ h
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [algebraMap_smul]; rfl
  have hval : ∀ y : Fin 3 → F, (Q₀.compMat G).evalIn F y = (pureFormO a b).evalIn F y := by
    intro y
    have e1 : (Q₀.compMat G).evalIn F y = ((Q₀.compMat G).map (algebraMap (𝓞 F) F)).eval y := by
      simp [QuadForm.evalIn, QuadForm.map]
    rw [e1, ← map_compMat, hQ, eval_compMat, fr.eval_QF]
    have e2 : (pureFormO a b).evalIn F y = ((pureFormO a b).map (algebraMap (𝓞 F) F)).eval y := by
      simp [QuadForm.evalIn, QuadForm.map]
    rw [e2, map_pureFormO, ← nrd_pure]
    congr 1
    have : ∑ l, (G.map (algebraMap (𝓞 F) F) *ᵥ y) l • (fr.e l.succ : QuatF F a b) = ∑ m, y m • qv m := by
      simp only [mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← hsum m, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul, mul_comm]
    rw [this]
    ext <;> simp [qv, Quat.pure, Fin.sum_univ_three, qi, qj, qk]
  have hQG : Q₀.compMat G = pureFormO a b := eq_of_evalIn_eq hval
  have hG : G.det ≠ 0 := by
    intro h0
    have h0' : (G.map (algebraMap (𝓞 F) F)).det = 0 := by
      rw [show G.map (algebraMap (𝓞 F) F) = (algebraMap (𝓞 F) F).mapMatrix G from rfl, ← RingHom.map_det, h0,
        map_zero]
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0'
    have hs : ∑ m, y m • qv m = 0 := by
      have : ∑ l, (G.map (algebraMap (𝓞 F) F) *ᵥ y) l • (fr.e l.succ : QuatF F a b) = ∑ m, y m • qv m := by
        simp only [mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← hsum m, Finset.smul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [smul_smul, mul_comm]
      rw [← this, hy]; simp
    apply hy0
    funext m
    have e1 := congrArg QuaternionAlgebra.imI hs
    have e2 := congrArg QuaternionAlgebra.imJ hs
    have e3 := congrArg QuaternionAlgebra.imK hs
    simp [qv, Fin.sum_univ_three, qi, qj, qk] at e1 e2 e3
    fin_cases m
    · exact e1
    · exact e2
    · exact e3
  -- definiteness of Q₀
  set Gm := G.map (algebraMap (𝓞 F) F)
  have hGm : Gm.det ≠ 0 := by
    rw [show Gm = (algebraMap (𝓞 F) F).mapMatrix G from rfl, ← RingHom.map_det]
    exact fun h => hG ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).1 h)
  have hpdQ : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)) := by
    have h1 : (pureFormO a b).map (algebraMap (𝓞 F) F) = (Q₀.map (algebraMap (𝓞 F) F)).compMat Gm := by
      rw [← hQG, map_compMat]
    have h2 : Q₀.map (algebraMap (𝓞 F) F) = ((pureFormO a b).map (algebraMap (𝓞 F) F)).compMat Gm⁻¹ := by
      rw [h1, compMat_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit hGm), compMat_one]
    rw [h2]
    exact LatChange.isTotallyPosDef_compMat_of_det hpd (by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hGm)
  have hnd : Q₀.Nondegenerate := nondegenerate_of_map hpdQ.nondegenerate
  have := LatChange.tauSO_smul_compMat (by norm_num) (by norm_num) Q₀ hnd hpdQ one_ne_zero G hG
    (by rw [one_smul_form', hQG]; exact hpd)
  rw [one_smul_form', hQG] at this
  exact this

end QuadFormsKB.QuatOrder
