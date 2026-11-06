/-
# Hanke 2005, §3: Witt index of an even unimodular lattice at a dyadic place

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

At a dyadic place, an orthogonal sum of $r$ binary forms $a_ix^2 + b_ixy + c_iy^2$ with $b_i$ units (an even unimodular
lattice, O'Meara 93:15) has Witt index at least $r - 1$ over $F_\mathfrak p$ (`wittIndex_pairSum`), so its anisotropic
kernel has dimension at most $2$. *Proof:* an isotropic binary block is a hyperbolic plane; two anisotropic blocks have
discriminants $b_i^2(1-4t_i)$ with $1-4t_i$ non-squares, whose product is a square (Artin–Schreier, `as_add_of_not`), and
their sum is isotropic (`DVR.isotropicIn_of_isLocalLevel_zero`), hence hyperbolic (`even_disc_of_anisoDim`); induct.
-/
import QuadFormsKB.Literature.Hanke2005.WittDiag
import QuadFormsKB.LocalDensity.NFBridge
import QuadFormsKB.LocalDensity.DyadicArf

open NumberField IsDedekindDomain QuadraticMap QuadraticForm

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

namespace SelfDualD

local notation "res" => IsLocalRing.residue 𝔬

/-- The Mathlib form over $F_\mathfrak p$ of a form over $\mathfrak o$ (base change). -/
def FQ {n : ℕ} (Q : QuadForm 𝔬 n) : QuadraticForm Fv (Fin n → Fv) :=
  (Q.map (algebraMap 𝔬 Fv)).toQuadraticForm

theorem FQ_apply {n : ℕ} (Q : QuadForm 𝔬 n) (x : Fin n → Fv) : FQ v Q x = Q.evalIn Fv x := by
  unfold FQ
  rw [QuadForm.toQuadraticForm_apply]
  simp [QuadForm.evalIn, QuadForm.map]

theorem hessian_det_map {n : ℕ} (Q : QuadForm 𝔬 n) :
    (Q.map (algebraMap 𝔬 Fv)).hessian.det = algebraMap 𝔬 Fv Q.hessian.det := by
  have : (Q.map (algebraMap 𝔬 Fv)).hessian = Q.hessian.map (algebraMap 𝔬 Fv) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [this]
  exact (RingHom.map_det _ _).symm

theorem hessian_det_map_ne_zero {n : ℕ} (Q : QuadForm 𝔬 n) (hQ : Q.hessian.det ≠ 0) :
    (Q.map (algebraMap 𝔬 Fv)).hessian.det ≠ 0 := by
  rw [hessian_det_map]
  exact (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hQ

/-- A form over $\mathfrak o$ with nonzero Hessian determinant has zero quadratic radical over $F_\mathfrak p$. -/
theorem radical_FQ {n : ℕ} (Q : QuadForm 𝔬 n) (hQ : Q.hessian.det ≠ 0) : (FQ v Q).radical = ⊥ := by
  have hdet : ((Q.map (algebraMap 𝔬 Fv)).hessian).det ≠ 0 := hessian_det_map_ne_zero v Q hQ
  have hnd := QuadForm.nondegenerate_polarBilin_toQuadraticFormIn (K := Fv)
    (Q := Q.map (algebraMap 𝔬 Fv)) hdet
  have e : (Q.map (algebraMap 𝔬 Fv)).toQuadraticFormIn Fv = (Q.map (algebraMap 𝔬 Fv)).toQuadraticForm := by
    unfold QuadForm.toQuadraticFormIn
    congr 1
  rw [e] at hnd
  exact radical_eq_bot_of_nondegenerate _ hnd

/-- The binary block $ax^2 + bxy + cy^2$ over $F_\mathfrak p$. -/
def blk (B : 𝔬 × 𝔬 × 𝔬) : QuadraticForm Fv (Fin 2 → Fv) :=
  FQ v (DVR.binForm B.1 B.2.1 B.2.2)

theorem blk_apply (B : 𝔬 × 𝔬 × 𝔬) (x : Fin 2 → Fv) :
    blk v B x = algebraMap 𝔬 Fv B.1 * x 0 ^ 2 + algebraMap 𝔬 Fv B.2.1 * x 0 * x 1 +
      algebraMap 𝔬 Fv B.2.2 * x 1 ^ 2 := by
  rw [blk, FQ_apply]
  simp [QuadForm.evalIn, Fin.sum_univ_two, DVR.binForm]
  ring

/-- The orthogonal sum of the blocks, over $F_\mathfrak p$. -/
def PS {r : ℕ} (A : Fin r → 𝔬 × 𝔬 × 𝔬) : QuadraticForm Fv (Fin (r * 2) → Fv) :=
  FQ v (DVR.pairSumForm A)

theorem hπ2_of (h2 : ¬ IsUnit (2 : 𝔬)) : NF.π v ∣ 2 := by
  have hπ := NF.irreducible_π v
  have h : (2 : 𝔬) ∈ IsLocalRing.maximalIdeal 𝔬 := (IsLocalRing.mem_maximalIdeal _).2 h2
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at h
  exact h

theorem isUnit_blk_det (hπ2 : NF.π v ∣ 2) (B : 𝔬 × 𝔬 × 𝔬) (hb : IsUnit B.2.1) :
    IsUnit (4 * B.1 * B.2.2 - B.2.1 ^ 2) := by
  have hπ := NF.irreducible_π v
  refine DVR.dvr_isUnit_of_not_dvd hπ fun hd => ?_
  have h4 : NF.π v ∣ 4 * B.1 * B.2.2 := by
    have : NF.π v ∣ 4 := by rw [show (4 : 𝔬) = 2 * 2 by norm_num]; exact hπ2.mul_right _
    exact (this.mul_right _).mul_right _
  have : NF.π v ∣ B.2.1 ^ 2 := by
    have := dvd_sub h4 hd
    simpa using this
  exact hπ.not_isUnit (isUnit_of_dvd_unit this (hb.pow 2))

theorem radical_blk (hπ2 : NF.π v ∣ 2) (B : 𝔬 × 𝔬 × 𝔬) (hb : IsUnit B.2.1) : (blk v B).radical = ⊥ := by
  refine radical_FQ v _ ?_
  rw [DVR.det_hessian_binForm]
  exact (isUnit_blk_det v hπ2 B hb).ne_zero

/-- **Isotropy of a vector gives Witt index $\ge 1$.** -/
theorem one_le_wittIndex_of_isotropic {V : Type} [AddCommGroup V] [Module Fv V] [FiniteDimensional Fv V]
    (Q : QuadraticForm Fv V) (hQ : Q.radical = ⊥) (x : V) (hx : x ≠ 0) (hx0 : Q x = 0) :
    1 ≤ wittIndex Q := by
  obtain ⟨U, _, _, _, Qa, ha, ⟨e⟩⟩ := wittIndex_spec Q hQ
  by_contra h
  have h0 : wittIndex Q = 0 := by omega
  have key : ∀ w : ℕ, w = 0 → ∀ e : Q.IsometryEquiv ((hyperbolicSpace Fv w).prod Qa), False := by
    rintro w rfl e
    have e' := e.trans (Witt.hyperbolicSpaceZeroProd Qa)
    have h1 : e' x = 0 := ha _ (by rw [e'.map_app, hx0])
    exact hx (e'.injective (h1.trans (map_zero e').symm))
  exact key _ h0 e

theorem two_mul_wittIndex_le {V : Type} [AddCommGroup V] [Module Fv V] [FiniteDimensional Fv V]
    (Q : QuadraticForm Fv V) (hQ : Q.radical = ⊥) : 2 * wittIndex Q ≤ Module.finrank Fv V := by
  obtain ⟨U, _, _, _, Qa, ha, ⟨e⟩⟩ := wittIndex_spec Q hQ
  have hdim' := e.toLinearEquiv.finrank_eq
  simp [Module.finrank_prod, Module.finrank_pi_fintype] at hdim'
  omega

/-- **Full Witt index gives a hyperbolic space.** -/
theorem equiv_hyp_of_full {V : Type} [AddCommGroup V] [Module Fv V] [FiniteDimensional Fv V]
    (Q : QuadraticForm Fv V) (hQ : Q.radical = ⊥) (h : 2 * wittIndex Q = Module.finrank Fv V) :
    Q.Equivalent (hyperbolicSpace Fv (wittIndex Q)) := by
  obtain ⟨U, _, _, _, Qa, ha, ⟨e⟩⟩ := wittIndex_spec Q hQ
  have hdim' := e.toLinearEquiv.finrank_eq
  simp [Module.finrank_prod, Module.finrank_pi_fintype] at hdim'
  have hU : Module.finrank Fv U = 0 := by omega
  have : Subsingleton U := Module.finrank_zero_iff.1 hU
  let _ : Unique U := uniqueOfSubsingleton 0
  exact ⟨e.trans { toLinearEquiv := LinearEquiv.prodUnique
                   map_app' := fun x => by simp [Subsingleton.elim x.2 0] }⟩

/-- **A binary block with an isotropic vector is a hyperbolic plane.** -/
theorem blk_equiv_hyp (hπ2 : NF.π v ∣ 2) (B : 𝔬 × 𝔬 × 𝔬) (hb : IsUnit B.2.1)
    (hiso : ∃ x : Fin 2 → Fv, x ≠ 0 ∧ blk v B x = 0) :
    (blk v B).Equivalent (hyperbolicSpace Fv 1) := by
  obtain ⟨x, hx, hx0⟩ := hiso
  have hrad := radical_blk v hπ2 B hb
  have h1 := one_le_wittIndex_of_isotropic v _ hrad x hx hx0
  have h2 := two_mul_wittIndex_le v _ hrad
  rw [Module.finrank_fin_fun] at h2
  have hw : wittIndex (blk v B) = 1 := by omega
  have := equiv_hyp_of_full v _ hrad (by rw [Module.finrank_fin_fun]; omega)
  rwa [hw] at this

/-- Commutativity of the orthogonal sum. -/
def prodComm {V₁ V₂ : Type} [AddCommGroup V₁] [Module Fv V₁] [AddCommGroup V₂] [Module Fv V₂]
    (Q₁ : QuadraticForm Fv V₁) (Q₂ : QuadraticForm Fv V₂) : (Q₁.prod Q₂).IsometryEquiv (Q₂.prod Q₁) where
  toLinearEquiv := LinearEquiv.prodComm Fv V₁ V₂
  map_app' x := by simp [add_comm]

theorem PS_one (A : Fin 1 → 𝔬 × 𝔬 × 𝔬) : (PS v A).Equivalent (blk v (A 0)) := by
  let e : Fin 2 ≃ Fin (1 * 2) := finCongr (by norm_num)
  have hp : ∀ j : Fin 2, DVR.pidx (0 : Fin 1) j = e j := fun j => Fin.ext (by simp [e])
  refine ⟨{ toLinearEquiv := LinearEquiv.funCongrLeft Fv Fv e
            map_app' := fun x => ?_ }⟩
  rw [blk_apply, PS, FQ_apply, DVR.evalIn_pairSumForm, Fin.sum_univ_one, hp, hp]
  rfl

theorem PS_cons {r : ℕ} (A : Fin (r + 1) → 𝔬 × 𝔬 × 𝔬) :
    (PS v A).Equivalent ((blk v (A 0)).prod (PS v (fun i : Fin r => A i.succ))) := by
  let c : Fin (2 + r * 2) ≃ Fin ((r + 1) * 2) := finCongr (by ring)
  let L : (Fin ((r + 1) * 2) → Fv) ≃ₗ[Fv] (Fin 2 → Fv) × (Fin (r * 2) → Fv) :=
    (LinearEquiv.funCongrLeft Fv Fv c).trans (QuadForm.finAddLinearEquiv Fv 2 (r * 2))
  refine ⟨{ toLinearEquiv := L, map_app' := fun x => ?_ }⟩
  have h0 : ∀ j : Fin 2, DVR.pidx (0 : Fin (r + 1)) j = c (Fin.castAdd (r * 2) j) :=
    fun j => Fin.ext (by simp [c])
  have h1 : ∀ (i : Fin r) (j : Fin 2), DVR.pidx i.succ j = c (Fin.natAdd 2 (DVR.pidx i j)) :=
    fun i j => Fin.ext (by simp [c]; ring)
  have hL1 : ∀ j, (L.toLinearMap.toFun x).1 j = x (DVR.pidx 0 j) := fun j => by rw [h0]; rfl
  have hL2 : ∀ k, (L.toLinearMap.toFun x).2 k = x (c (Fin.natAdd 2 k)) := fun k => rfl
  rw [QuadraticMap.prod_apply, blk_apply, PS, PS, FQ_apply, FQ_apply, DVR.evalIn_pairSumForm,
    DVR.evalIn_pairSumForm, Fin.sum_univ_succ]
  simp only [hL1, hL2, ← h1]

theorem PS_two (f g : 𝔬 × 𝔬 × 𝔬) : (PS v ![f, g]).Equivalent ((blk v f).prod (blk v g)) :=
  ⟨(PS_cons v ![f, g]).some.trans
    ((QuadraticMap.IsometryEquiv.refl _).prod (PS_one v (fun i : Fin 1 => ![f, g] i.succ)).some)⟩

theorem isotropic_of_isSquare_disc (a b c : 𝔬)
    (h : IsSquare (algebraMap 𝔬 Fv (b ^ 2 - 4 * a * c))) :
    ∃ x : Fin 2 → Fv, x ≠ 0 ∧ blk v (a, b, c) x = 0 := by
  obtain ⟨s, hs0⟩ := h
  have hs : algebraMap 𝔬 Fv b ^ 2 - 4 * algebraMap 𝔬 Fv a * algebraMap 𝔬 Fv c = s * s := by
    rw [← hs0, map_sub, map_mul, map_mul, map_pow, map_ofNat]
  have h2 : (2 : Fv) ≠ 0 := two_ne_zero
  by_cases ha : algebraMap 𝔬 Fv a = 0
  · refine ⟨![1, 0], ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp at this
    · rw [blk_apply]
      simp [ha]
  · refine ⟨![s - algebraMap 𝔬 Fv b, 2 * algebraMap 𝔬 Fv a], ?_, ?_⟩
    · intro h
      have h' := congrFun h 1
      simp only [Matrix.cons_val_one, Pi.zero_apply] at h'
      exact ha ((mul_eq_zero.1 h').resolve_left h2)
    · rw [blk_apply]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (-(algebraMap 𝔬 Fv a)) * hs

theorem disc1 (hπ2 : NF.π v ∣ 2) (f : 𝔬 × 𝔬 × 𝔬) (hf : IsUnit f.2.1) :
    ∃ T : 𝔬, f.2.1 ^ 2 - 4 * f.1 * f.2.2 = f.2.1 ^ 2 * (1 - 4 * T) ∧
      res T = res f.1 * res f.2.2 / res f.2.1 ^ 2 := by
  have hπ := NF.irreducible_π v
  obtain ⟨T, hT, hr⟩ := DVR.pairSum_disc_eq hπ hπ2 (![f] : Fin 1 → 𝔬 × 𝔬 × 𝔬)
    (fun i => by
      fin_cases i
      exact fun h => hπ.not_isUnit (isUnit_of_dvd_unit h hf))
  refine ⟨T, ?_, ?_⟩
  · rw [DVR.det_hessian_pairSumForm] at hT
    simp at hT
    linear_combination hT
  · simpa using hr

theorem disc2 (hπ2 : NF.π v ∣ 2) (f g : 𝔬 × 𝔬 × 𝔬) (hf : IsUnit f.2.1) (hg : IsUnit g.2.1) :
    ∃ T : 𝔬, (-1 : 𝔬) ^ 2 * (DVR.pairSumForm ![f, g]).hessian.det = (f.2.1 * g.2.1) ^ 2 * (1 - 4 * T) ∧
      res T = res f.1 * res f.2.2 / res f.2.1 ^ 2 + res g.1 * res g.2.2 / res g.2.1 ^ 2 := by
  have hπ := NF.irreducible_π v
  obtain ⟨T, hT, hr⟩ := DVR.pairSum_disc_eq hπ hπ2 (![f, g] : Fin 2 → 𝔬 × 𝔬 × 𝔬)
    (fun i => by
      fin_cases i
      · exact fun h => hπ.not_isUnit (isUnit_of_dvd_unit h hf)
      · exact fun h => hπ.not_isUnit (isUnit_of_dvd_unit h hg))
  refine ⟨T, ?_, ?_⟩
  · simpa [Fin.prod_univ_two] using hT
  · simpa [Fin.sum_univ_two] using hr

theorem not_AS_of_aniso (hπ2 : NF.π v ∣ 2) (B : 𝔬 × 𝔬 × 𝔬) (hb : IsUnit B.2.1)
    (hB : ¬ ∃ x : Fin 2 → Fv, x ≠ 0 ∧ blk v B x = 0) :
    ¬ ∃ z : IsLocalRing.ResidueField 𝔬, z ^ 2 + z = res B.1 * res B.2.2 / res B.2.1 ^ 2 := by
  have hπ := NF.irreducible_π v
  obtain ⟨T, hT, hr⟩ := disc1 v hπ2 B hb
  rintro ⟨z, hz⟩
  have hsq : IsSquare (1 - 4 * T) :=
    (DVR.isSquare_one_sub_four_mul_iff hπ hπ2 (NF.two_ne_zero' v) T).2 ⟨z, by rw [hr]; exact hz⟩
  obtain ⟨s, hs⟩ := hsq
  have hsq' : IsSquare (algebraMap 𝔬 Fv (B.2.1 ^ 2 - 4 * B.1 * B.2.2)) := by
    refine ⟨algebraMap 𝔬 Fv (B.2.1 * s), ?_⟩
    have : B.2.1 ^ 2 - 4 * B.1 * B.2.2 = B.2.1 * s * (B.2.1 * s) := by
      rw [hT, hs]; ring
    rw [this, map_mul]
  exact hB (isotropic_of_isSquare_disc v B.1 B.2.1 B.2.2 hsq')

theorem PS_two_hyp (hπ2 : NF.π v ∣ 2) (f g : 𝔬 × 𝔬 × 𝔬) (hf : IsUnit f.2.1) (hg : IsUnit g.2.1)
    (hfa : ¬ ∃ x : Fin 2 → Fv, x ≠ 0 ∧ blk v f x = 0) (hga : ¬ ∃ x : Fin 2 → Fv, x ≠ 0 ∧ blk v g x = 0) :
    (PS v ![f, g]).Equivalent (hyperbolicSpace Fv 2) := by
  have hπ := NF.irreducible_π v
  have hL := DVR.isLocalLevel_zero_pairSumForm (![f, g] : Fin 2 → 𝔬 × 𝔬 × 𝔬) hπ hπ2
    (fun i => by
      fin_cases i
      · exact fun h => hπ.not_isUnit (isUnit_of_dvd_unit h hf)
      · exact fun h => hπ.not_isUnit (isUnit_of_dvd_unit h hg))
  have hdetu : IsUnit (DVR.pairSumForm ![f, g]).hessian.det := by
    rw [DVR.det_hessian_pairSumForm, Fin.prod_univ_two]
    exact (isUnit_blk_det v hπ2 f hf).mul (isUnit_blk_det v hπ2 g hg)
  have hrad : (PS v ![f, g]).radical = ⊥ := radical_FQ v _ hdetu.ne_zero
  obtain ⟨x, hx, hx0⟩ := DVR.isotropicIn_of_isLocalLevel_zero Fv (DVR.pairSumForm ![f, g]) hπ
    (NF.two_ne_zero' v) hL (by norm_num : 3 ≤ 2 * 2)
  have h1 : 1 ≤ wittIndex (PS v ![f, g]) :=
    one_le_wittIndex_of_isotropic v _ hrad x hx (by rw [PS, FQ_apply]; exact hx0)
  have h2 := two_mul_wittIndex_le v _ hrad
  rw [Module.finrank_fin_fun] at h2
  -- the discriminant is a square
  obtain ⟨T1, hT1, hr1⟩ := disc1 v hπ2 f hf
  obtain ⟨T2, hT2, hr2⟩ := disc1 v hπ2 g hg
  have hnf := not_AS_of_aniso v hπ2 f hf hfa
  have hng := not_AS_of_aniso v hπ2 g hg hga
  have := DVR.charP_residueField_two hπ hπ2
  obtain ⟨z, hz⟩ := DVR.as_add_of_not hnf hng
  obtain ⟨T, hT, hr⟩ := disc2 v hπ2 f g hf hg
  have hsq : IsSquare ((-1 : 𝔬) ^ 2 * (DVR.pairSumForm ![f, g]).hessian.det) := by
    obtain ⟨s, hs⟩ := (DVR.isSquare_one_sub_four_mul_iff hπ hπ2 (NF.two_ne_zero' v) T).2
      ⟨z, by rw [hr]; exact hz⟩
    exact ⟨(f.2.1 * g.2.1) * s, by rw [hT, hs]; ring⟩
  have hw : wittIndex (PS v ![f, g]) ≠ 1 := by
    intro hw1
    have hQnd : ((DVR.pairSumForm ![f, g]).map (algebraMap 𝔬 Fv)).Nondegenerate :=
      hessian_det_map_ne_zero v _ hdetu.ne_zero
    have hd := (even_disc_of_anisoDim (two_ne_zero : (2 : Fv) ≠ 0) _ hQnd ⟨2, by norm_num⟩).2.1
    refine hd (by change 2 * 2 - 2 * wittIndex (PS v ![f, g]) = 2; omega) ?_
    have := hsq.map (algebraMap 𝔬 Fv)
    rw [map_mul, map_pow, map_neg, map_one, ← hessian_det_map] at this
    simpa using this
  have hw2 : wittIndex (PS v ![f, g]) = 2 := by omega
  have := equiv_hyp_of_full v _ hrad (by rw [Module.finrank_fin_fun]; omega)
  rwa [hw2] at this

/-- **Key lemma: two unimodular blocks sum to a hyperbolic plane plus a unimodular block.** -/
theorem two_blocks (hπ2 : NF.π v ∣ 2) (f g : 𝔬 × 𝔬 × 𝔬) (hf : IsUnit f.2.1) (hg : IsUnit g.2.1) :
    ∃ C : 𝔬 × 𝔬 × 𝔬, IsUnit C.2.1 ∧
      ((blk v f).prod (blk v g)).Equivalent ((hyperbolicSpace Fv 1).prod (blk v C)) := by
  by_cases hfi : ∃ x : Fin 2 → Fv, x ≠ 0 ∧ blk v f x = 0
  · exact ⟨g, hg, ⟨(blk_equiv_hyp v hπ2 f hf hfi).some.prod (QuadraticMap.IsometryEquiv.refl _)⟩⟩
  by_cases hgi : ∃ x : Fin 2 → Fv, x ≠ 0 ∧ blk v g x = 0
  · exact ⟨f, hf, ⟨((QuadraticMap.IsometryEquiv.refl _).prod
      (blk_equiv_hyp v hπ2 g hg hgi).some).trans (prodComm v _ _)⟩⟩
  · have hB0 : ∃ x : Fin 2 → Fv, x ≠ 0 ∧ blk v ((0 : 𝔬), (1 : 𝔬), (0 : 𝔬)) x = 0 := by
      refine ⟨![1, 0], ?_, ?_⟩
      · intro h
        have := congrFun h 0
        simp at this
      · rw [blk_apply]
        simp
    refine ⟨((0 : 𝔬), (1 : 𝔬), (0 : 𝔬)), isUnit_one, ?_⟩
    have e1 : ((blk v f).prod (blk v g)).Equivalent (hyperbolicSpace Fv 2) :=
      (PS_two v f g).symm.trans (PS_two_hyp v hπ2 f g hf hg hfi hgi)
    have e2 := hyperbolicSpace_prod_equiv (K := Fv) 1 1
    have e3 := blk_equiv_hyp v hπ2 _ isUnit_one hB0
    exact e1.trans (e2.symm.trans ⟨(QuadraticMap.IsometryEquiv.refl _).prod e3.some.symm⟩)

theorem PS_equiv (hπ2 : NF.π v ∣ 2) : ∀ (r : ℕ) (A : Fin (r + 1) → 𝔬 × 𝔬 × 𝔬), (∀ i, IsUnit (A i).2.1) →
    ∃ B : 𝔬 × 𝔬 × 𝔬, IsUnit B.2.1 ∧ (PS v A).Equivalent ((hyperbolicSpace Fv r).prod (blk v B)) := by
  intro r
  induction r with
  | zero =>
    intro A hA
    exact ⟨A 0, hA 0, ⟨(PS_one v A).some.trans (Witt.hyperbolicSpaceZeroProd _).symm⟩⟩
  | succ r ih =>
    intro A hA
    obtain ⟨B, hB, ⟨e⟩⟩ := ih (fun i => A i.succ) (fun i => hA _)
    obtain ⟨C, hC, ⟨e2⟩⟩ := two_blocks v hπ2 (A 0) B (hA 0) hB
    refine ⟨C, hC, ⟨(PS_cons v A).some.trans ?_⟩⟩
    exact ((QuadraticMap.IsometryEquiv.refl _).prod e).trans
      ((Witt.prodAssoc _ _ _).symm.trans
        (((prodComm v _ _).prod (QuadraticMap.IsometryEquiv.refl _)).trans
          ((Witt.prodAssoc _ _ _).trans
            (((QuadraticMap.IsometryEquiv.refl _).prod e2).trans
              ((Witt.prodAssoc _ _ _).symm.trans
                ((hyperbolicSpace_prod_equiv (K := Fv) r 1).some.prod
                  (QuadraticMap.IsometryEquiv.refl _)))))))

end SelfDualD

/-- **Sums of unimodular binary blocks at a dyadic place have Witt index $\ge r - 1$** (O'Meara 93:15, 93:11). -/
theorem wittIndex_pairSum (h2 : ¬ IsUnit (2 : 𝔬)) : ∀ (r : ℕ) (A : Fin r → 𝔬 × 𝔬 × 𝔬), (∀ i, IsUnit (A i).2.1) →
    r - 1 ≤ wittIndex ((DVR.pairSumForm A).map (algebraMap 𝔬 Fv)).toQuadraticForm := by
  intro r A hA
  have hπ2 := SelfDualD.hπ2_of v h2
  cases r with
  | zero => simp
  | succ s =>
    obtain ⟨B, hB, ⟨e⟩⟩ := SelfDualD.PS_equiv v hπ2 s A hA
    have hrad : ((hyperbolicSpace Fv s).prod (SelfDualD.blk v B)).radical = ⊥ :=
      radical_prod_eq_bot (nondegenerate_hyperbolicSpace Fv s) (SelfDualD.radical_blk v hπ2 B hB)
    have h1 := wittIndex_eq_of_equivalent (⟨e.symm⟩ : ((hyperbolicSpace Fv s).prod (SelfDualD.blk v B)).Equivalent
      (SelfDualD.PS v A)) hrad
    have h3 := wittIndex_hyperbolic_prod s (SelfDualD.blk v B) (SelfDualD.radical_blk v hπ2 B hB)
    change s + 1 - 1 ≤ wittIndex (SelfDualD.PS v A)
    omega

end QuadFormsKB.Hanke2005
