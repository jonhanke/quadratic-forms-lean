/-
# $(D\otimes F_\infty)^\times/F_\infty^\times \cong SO(D^0)(F_\infty)$ (archimedean part)

**Layer:** $F$ a number field, $a, b \in \mathcal O_F \setminus 0$, $Q_0$ = `QuatZeta.pureFormO a b`;
$D\otimes F_\infty$ = `QuatInf` (over Mathlib's `mixedSpace F`), and $G_\infty = \prod_{w\ \mathrm{real}}SO(Q^{\sigma_w})(\mathbb R)
\times\prod_{w\ \mathrm{complex}}SO(Q^{\tau_w})(\mathbb C)$ = `GInfSO Q₀` (any signature).

**Defines/proves**
* `projR`, `projC`: the ring homomorphisms $D\otimes F_\infty \to D\otimes_{F,\sigma_w}\mathbb R$, $D\otimes_{F,\tau_w}\mathbb C$;
* `conjInf a b : (D\otimes F_\infty)^\times \to G_\infty$, $\alpha\mapsto(c(\alpha_w))_w$; **`continuous_conjInf`**;
* **`conjInf_surjective`** (over $\mathbb R$ and $\mathbb C$ at each place) and **`conjInf_eq_one_iff`** (kernel
  $F_\infty^\times$, the central scalars).

Source: Weil 1982, §3.7(a), p. 63.
-/
import QuadFormsKB.Tamagawa.Measure.Weil.PDAdelic

open Matrix Quaternion NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.QuatZeta QuadFormsKB.Siegel
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F]

/-! ### Conjugation over a field with a ring homomorphism from $F$ -/

section RingHom

variable {K : Type*} [Field K] (ρ : F →+* K)

theorem pureForm_map_ringHom (A B : F) : (pureForm A B).map ρ = pureForm (ρ A) (ρ B) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pureForm, QuadForm.diag, QuadForm.map]

theorem two_ne_zero_ringHom (ρ : F →+* K) : (2 : K) ≠ 0 := by
  intro h
  have h' : ρ 2 = 0 := by rw [map_ofNat]; exact h
  exact two_ne_zero (α := F) ((map_eq_zero ρ).1 h')

/-- Conjugation by $\alpha \in (D\otimes_{F,\rho}K)^\times$ preserves the hessian of $Q^\rho$ and has determinant 1. -/
theorem conjGL_hessian_map (Q : QuadForm F 3) {A B : F} (hQ : Q = pureForm A B) (α : (ℍ[K, ρ A, ρ B])ˣ) :
    ((conjGL α : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ * (Q.map ρ).hessian *
        ((conjGL α : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (Q.map ρ).hessian ∧
      ((conjGL α : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  subst hQ
  rw [pureForm_map_ringHom]
  have := (mem_SO_iff_hessian (two_ne_zero_ringHom ρ)).1 (conjGL_mem α)
  exact ⟨this.2, this.1⟩

/-- Conversely, an element preserving the hessian of $Q^\rho$ with determinant 1 is a conjugation. -/
theorem exists_conjGL_eq (Q : QuadForm F 3) {A B : F} (hQ : Q = pureForm A B) (hA : A ≠ 0) (hB : B ≠ 0)
    (g : GL (Fin 3) K) (hg : (g : Matrix (Fin 3) (Fin 3) K)ᵀ * (Q.map ρ).hessian * g = (Q.map ρ).hessian)
    (hdet : (g : Matrix (Fin 3) (Fin 3) K).det = 1) : ∃ α : (ℍ[K, ρ A, ρ B])ˣ, conjGL α = g := by
  subst hQ
  rw [pureForm_map_ringHom] at hg
  have hmem : g ∈ SO (pureForm (ρ A) (ρ B)) := (mem_SO_iff_hessian (two_ne_zero_ringHom ρ)).2 ⟨hdet, hg⟩
  obtain ⟨α, hα⟩ := conjSO_surjective (two_ne_zero_ringHom ρ) ((map_ne_zero ρ).2 hA) ((map_ne_zero ρ).2 hB)
    ⟨g, hmem⟩
  exact ⟨α, congrArg Subtype.val hα⟩

/-- The kernel of conjugation is the centre. -/
theorem conjGL_eq_one_iff {A B : F} (hA : A ≠ 0) (α : (ℍ[K, ρ A, ρ B])ˣ) :
    conjGL α = 1 ↔ α ∈ centerUnits (ρ A) (ρ B) := by
  rw [← ker_conjSO (two_ne_zero_ringHom ρ) ((map_ne_zero ρ).2 hA), MonoidHom.mem_ker]
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg Subtype.val h

end RingHom

/-! ### Projections of $D\otimes F_\infty$ to the places -/

variable (A B : F)

/-- $D\otimes F_\infty \to D\otimes_{F,\sigma_w}\mathbb R$ at a real place. -/
def projR (w : {w : InfinitePlace F // w.IsReal}) :
    QuatInf A B →+* ℍ[ℝ, embedding_of_isReal w.2 A, embedding_of_isReal w.2 B] :=
  QuaternionAlgebra.mapRingHom ((Pi.evalRingHom _ w).comp (RingHom.fst _ _)) (mixedEmbedding_apply_isReal F A w)
    (map_zero _) (mixedEmbedding_apply_isReal F B w)

/-- $D\otimes F_\infty \to D\otimes_{F,\tau_w}\mathbb C$ at a complex place. -/
def projC (w : {w : InfinitePlace F // w.IsComplex}) :
    QuatInf A B →+* ℍ[ℂ, w.1.embedding A, w.1.embedding B] :=
  QuaternionAlgebra.mapRingHom ((Pi.evalRingHom _ w).comp (RingHom.snd _ _)) (mixedEmbedding_apply_isComplex F A w)
    (map_zero _) (mixedEmbedding_apply_isComplex F B w)

@[simp] theorem projR_re (w) (x : QuatInf A B) : (projR A B w x).re = x.re.1 w := rfl
@[simp] theorem projR_imI (w) (x : QuatInf A B) : (projR A B w x).imI = x.imI.1 w := rfl
@[simp] theorem projR_imJ (w) (x : QuatInf A B) : (projR A B w x).imJ = x.imJ.1 w := rfl
@[simp] theorem projR_imK (w) (x : QuatInf A B) : (projR A B w x).imK = x.imK.1 w := rfl
@[simp] theorem projC_re (w) (x : QuatInf A B) : (projC A B w x).re = x.re.2 w := rfl
@[simp] theorem projC_imI (w) (x : QuatInf A B) : (projC A B w x).imI = x.imI.2 w := rfl
@[simp] theorem projC_imJ (w) (x : QuatInf A B) : (projC A B w x).imJ = x.imJ.2 w := rfl
@[simp] theorem projC_imK (w) (x : QuatInf A B) : (projC A B w x).imK = x.imK.2 w := rfl

theorem quatInf_ext {x y : QuatInf A B} (hR : ∀ w, projR A B w x = projR A B w y)
    (hC : ∀ w, projC A B w x = projC A B w y) : x = y := by
  have e : ∀ s t : mixedSpace F, (∀ w, s.1 w = t.1 w) → (∀ w, s.2 w = t.2 w) → s = t :=
    fun s t h1 h2 => Prod.ext (funext h1) (funext h2)
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · exact e _ _ (fun w => congrArg QuaternionAlgebra.re (hR w)) (fun w => congrArg QuaternionAlgebra.re (hC w))
  · exact e _ _ (fun w => congrArg QuaternionAlgebra.imI (hR w)) (fun w => congrArg QuaternionAlgebra.imI (hC w))
  · exact e _ _ (fun w => congrArg QuaternionAlgebra.imJ (hR w)) (fun w => congrArg QuaternionAlgebra.imJ (hC w))
  · exact e _ _ (fun w => congrArg QuaternionAlgebra.imK (hR w)) (fun w => congrArg QuaternionAlgebra.imK (hC w))

/-! ### The archimedean map -/

variable (a b : 𝓞 F)

local notation "Q₀" => pureFormO a b
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (pureFormO a b)

/-- The real component $(D\otimes F_\infty)^\times \to SO(Q^{\sigma_w})(\mathbb R)$. -/
def conjR (w : {w : InfinitePlace F // w.IsReal}) : (QuatInf (a : F) (b : F))ˣ →* ArchSO (QRe Q₀ w) where
  toFun α := (⟨conjGL (Units.map (projR (a : F) (b : F) w).toMonoidHom α), by
    rw [mem_soReal_iff]
    exact conjGL_hessian_map _ QF (hQF a b) _⟩ : soReal (QRe Q₀ w))
  map_one' := archSO_ext (by simp only [map_one]; exact congrArg Subtype.val (map_one conjSO))
  map_mul' α β := archSO_ext (by simp only [map_mul]; exact congrArg Subtype.val (map_mul conjSO _ _))

theorem conjR_incl (w : {w : InfinitePlace F // w.IsReal}) (α : (QuatInf (a : F) (b : F))ˣ) :
    ArchSO.incl _ (conjR a b w α) = conjGL (Units.map (projR (a : F) (b : F) w).toMonoidHom α) := rfl

theorem archSOC_ext {Q : QuadForm ℂ 3} {g h : ArchSOC Q} (e : ArchSOC.incl Q g = ArchSOC.incl Q h) : g = h :=
  Subtype.ext e

/-- The complex component $(D\otimes F_\infty)^\times \to SO(Q^{\tau_w})(\mathbb C)$. -/
def conjC (w : {w : InfinitePlace F // w.IsComplex}) : (QuatInf (a : F) (b : F))ˣ →* ArchSOC (QCx Q₀ w) where
  toFun α := (⟨conjGL (Units.map (projC (a : F) (b : F) w).toMonoidHom α), by
    rw [mem_soC_iff, gramC]
    obtain ⟨h1, h2⟩ := conjGL_hessian_map _ QF (hQF a b) (Units.map (projC (a : F) (b : F) w).toMonoidHom α)
    refine ⟨?_, h2⟩
    rw [Matrix.mul_smul, Matrix.smul_mul, h1]⟩ : soC (QCx Q₀ w))
  map_one' := archSOC_ext (by simp only [map_one]; exact congrArg Subtype.val (map_one conjSO))
  map_mul' α β := archSOC_ext (by simp only [map_mul]; exact congrArg Subtype.val (map_mul conjSO _ _))

theorem conjC_incl (w : {w : InfinitePlace F // w.IsComplex}) (α : (QuatInf (a : F) (b : F))ˣ) :
    ArchSOC.incl _ (conjC a b w α) = conjGL (Units.map (projC (a : F) (b : F) w).toMonoidHom α) := rfl

/-- **$(D\otimes F_\infty)^\times \to G_\infty$**, $\alpha \mapsto (y\mapsto\alpha_w y\alpha_w^{-1})_w$. -/
@[kb "weil1982" "§3.7(a), p. 63"]
def conjInf : (QuatInf (a : F) (b : F))ˣ →* GInfSO Q₀ :=
  (MonoidHom.pi fun w => conjR a b w).prod (MonoidHom.pi fun w => conjC a b w)

/-- **`conjInf` is continuous.** -/
theorem continuous_conjInf : Continuous (conjInf a b) := by
  have hc : ∀ (f : QuatInf (a : F) (b : F) → mixedSpace F), Continuous f →
      Continuous fun α : (QuatInf (a : F) (b : F))ˣ => f α := fun f hf => hf.comp Units.continuous_val
  have hc' : ∀ (f : QuatInf (a : F) (b : F) → mixedSpace F), Continuous f →
      Continuous fun α : (QuatInf (a : F) (b : F))ˣ => f ↑α⁻¹ := fun f hf => hf.comp Units.continuous_coe_inv
  refine Continuous.prodMk (continuous_pi fun w => ?_) (continuous_pi fun w => ?_)
  · refine Continuous.subtype_mk ?_ _
    refine continuous_conjGL_comp _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact (continuous_apply w).comp (continuous_fst.comp (hc _ (continuous_ire _ _)))
    · exact (continuous_apply w).comp (continuous_fst.comp (hc _ (continuous_iimI _ _)))
    · exact (continuous_apply w).comp (continuous_fst.comp (hc _ (continuous_iimJ _ _)))
    · exact (continuous_apply w).comp (continuous_fst.comp (hc _ (continuous_iimK _ _)))
    all_goals simp only [← map_inv]
    · exact (continuous_apply w).comp (continuous_fst.comp (hc' _ (continuous_ire _ _)))
    · exact (continuous_apply w).comp (continuous_fst.comp (hc' _ (continuous_iimI _ _)))
    · exact (continuous_apply w).comp (continuous_fst.comp (hc' _ (continuous_iimJ _ _)))
    · exact (continuous_apply w).comp (continuous_fst.comp (hc' _ (continuous_iimK _ _)))
  · refine Continuous.subtype_mk ?_ _
    refine continuous_conjGL_comp _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact (continuous_apply w).comp (continuous_snd.comp (hc _ (continuous_ire _ _)))
    · exact (continuous_apply w).comp (continuous_snd.comp (hc _ (continuous_iimI _ _)))
    · exact (continuous_apply w).comp (continuous_snd.comp (hc _ (continuous_iimJ _ _)))
    · exact (continuous_apply w).comp (continuous_snd.comp (hc _ (continuous_iimK _ _)))
    all_goals simp only [← map_inv]
    · exact (continuous_apply w).comp (continuous_snd.comp (hc' _ (continuous_ire _ _)))
    · exact (continuous_apply w).comp (continuous_snd.comp (hc' _ (continuous_iimI _ _)))
    · exact (continuous_apply w).comp (continuous_snd.comp (hc' _ (continuous_iimJ _ _)))
    · exact (continuous_apply w).comp (continuous_snd.comp (hc' _ (continuous_iimK _ _)))

/-- **$(D\otimes F_\infty)^\times \to G_\infty$ is surjective** ($a, b \ne 0$; over $\mathbb R$ and $\mathbb C$). -/
@[kb "weil1982" "§3.7(a), p. 63"]
theorem conjInf_surjective (ha : a ≠ 0) (hb : b ≠ 0) : Function.Surjective (conjInf a b) := by
  intro g
  have hA : (a : F) ≠ 0 := by exact_mod_cast ha
  have hB : (b : F) ≠ 0 := by exact_mod_cast hb
  have hR : ∀ w : {w : InfinitePlace F // w.IsReal},
      ∃ β : (ℍ[ℝ, embedding_of_isReal w.2 (a : F), embedding_of_isReal w.2 (b : F)])ˣ,
        conjGL β = ArchSO.incl _ (g.1 w) := fun w => by
    have hm := (mem_soReal_iff _ _).1 (show ArchSO.incl _ (g.1 w) ∈ soReal (QRe Q₀ w) from (g.1 w).2)
    exact exists_conjGL_eq (embedding_of_isReal w.2) QF (hQF a b) hA hB _ hm.1 hm.2
  have hC : ∀ w : {w : InfinitePlace F // w.IsComplex},
      ∃ β : (ℍ[ℂ, w.1.embedding (a : F), w.1.embedding (b : F)])ˣ, conjGL β = ArchSOC.incl _ (g.2 w) := fun w => by
    have hm := (mem_soC_iff _ _).1 (ArchSOC.incl_mem _ (g.2 w))
    rw [gramC] at hm
    have h1 : ((ArchSOC.incl _ (g.2 w) : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)ᵀ * (QCx Q₀ w).hessian *
        ((ArchSOC.incl _ (g.2 w) : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) = (QCx Q₀ w).hessian := by
      have := congrArg ((2 : ℂ) • ·) hm.1
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul] at this
      norm_num at this
      exact this
    exact exists_conjGL_eq w.1.embedding QF (hQF a b) hA hB _ h1 hm.2
  choose βR hβR using hR
  choose βC hβC using hC
  let x : QuatInf (a : F) (b : F) :=
    ⟨((fun w => (βR w).val.re), (fun w => (βC w).val.re)),
     ((fun w => (βR w).val.imI), (fun w => (βC w).val.imI)),
     ((fun w => (βR w).val.imJ), (fun w => (βC w).val.imJ)),
     ((fun w => (βR w).val.imK), (fun w => (βC w).val.imK))⟩
  let y : QuatInf (a : F) (b : F) :=
    ⟨((fun w => ((βR w)⁻¹).val.re),
        (fun w => ((βC w)⁻¹).val.re)),
     ((fun w => ((βR w)⁻¹).val.imI),
        (fun w => ((βC w)⁻¹).val.imI)),
     ((fun w => ((βR w)⁻¹).val.imJ),
        (fun w => ((βC w)⁻¹).val.imJ)),
     ((fun w => ((βR w)⁻¹).val.imK),
        (fun w => ((βC w)⁻¹).val.imK))⟩
  have hxR : ∀ w, projR _ _ w x = βR w := fun w => QuaternionAlgebra.ext rfl rfl rfl rfl
  have hxC : ∀ w, projC _ _ w x = βC w := fun w => QuaternionAlgebra.ext rfl rfl rfl rfl
  have hyR : ∀ w, projR _ _ w y = ((βR w)⁻¹).val :=
    fun w => QuaternionAlgebra.ext rfl rfl rfl rfl
  have hyC : ∀ w, projC _ _ w y = ((βC w)⁻¹).val :=
    fun w => QuaternionAlgebra.ext rfl rfl rfl rfl
  have hxy : x * y = 1 := quatInf_ext _ _ (fun w => by rw [map_mul, map_one, hxR, hyR, Units.mul_inv])
    (fun w => by rw [map_mul, map_one, hxC, hyC, Units.mul_inv])
  have hyx : y * x = 1 := quatInf_ext _ _ (fun w => by rw [map_mul, map_one, hxR, hyR, Units.inv_mul])
    (fun w => by rw [map_mul, map_one, hxC, hyC, Units.inv_mul])
  refine ⟨⟨x, y, hxy, hyx⟩, Prod.ext (funext fun w => archSO_ext ?_) (funext fun w => archSOC_ext ?_)⟩
  · change conjGL (Units.map (projR (a : F) (b : F) w).toMonoidHom ⟨x, y, hxy, hyx⟩) = _
    rw [show Units.map (projR (a : F) (b : F) w).toMonoidHom ⟨x, y, hxy, hyx⟩ = βR w from Units.ext (hxR w), hβR]
  · change conjGL (Units.map (projC (a : F) (b : F) w).toMonoidHom ⟨x, y, hxy, hyx⟩) = _
    rw [show Units.map (projC (a : F) (b : F) w).toMonoidHom ⟨x, y, hxy, hyx⟩ = βC w from Units.ext (hxC w), hβC]

/-- The central scalars $F_\infty^\times \to (D\otimes F_\infty)^\times$. -/
def infScalar (A B : F) : (mixedSpace F)ˣ →* (QuatInf A B)ˣ :=
  Units.map (algebraMap (mixedSpace F) (QuatInf A B)).toMonoidHom

/-- **The kernel of $(D\otimes F_\infty)^\times \to G_\infty$ is $F_\infty^\times$.** -/
theorem conjInf_eq_one_iff (ha : a ≠ 0) (α : (QuatInf (a : F) (b : F))ˣ) :
    conjInf a b α = 1 ↔ α ∈ (infScalar (a : F) (b : F)).range := by
  have hA : (a : F) ≠ 0 := by exact_mod_cast ha
  constructor
  · intro h
    have hv : ∀ (β : (QuatInf (a : F) (b : F))ˣ), conjInf a b β = 1 →
        (β : QuatInf (a : F) (b : F)).imI = 0 ∧ (β : QuatInf (a : F) (b : F)).imJ = 0 ∧
          (β : QuatInf (a : F) (b : F)).imK = 0 := by
      intro β hβ
      have hRw : ∀ w, Units.map (projR (a : F) (b : F) w).toMonoidHom β ∈ centerUnits _ _ := fun w =>
        (conjGL_eq_one_iff _ hA _).1 (congrArg (fun g : GInfSO Q₀ => ArchSO.incl _ (g.1 w)) hβ)
      have hCw : ∀ w, Units.map (projC (a : F) (b : F) w).toMonoidHom β ∈ centerUnits _ _ := fun w =>
        (conjGL_eq_one_iff _ hA _).1 (congrArg (fun g : GInfSO Q₀ => ArchSOC.incl _ (g.2 w)) hβ)
      choose rR hrR using fun w => mem_centerUnits.1 (hRw w)
      choose rC hrC using fun w => mem_centerUnits.1 (hCw w)
      refine ⟨Prod.ext (funext fun w => ?_) (funext fun w => ?_), Prod.ext (funext fun w => ?_)
        (funext fun w => ?_), Prod.ext (funext fun w => ?_) (funext fun w => ?_)⟩
      · exact congrArg QuaternionAlgebra.imI (hrR w)
      · exact congrArg QuaternionAlgebra.imI (hrC w)
      · exact congrArg QuaternionAlgebra.imJ (hrR w)
      · exact congrArg QuaternionAlgebra.imJ (hrC w)
      · exact congrArg QuaternionAlgebra.imK (hrR w)
      · exact congrArg QuaternionAlgebra.imK (hrC w)
    obtain ⟨hI, hJ, hK⟩ := hv α h
    obtain ⟨hI', hJ', hK'⟩ := hv α⁻¹ (by rw [map_inv, h, inv_one])
    have hre : ∀ β γ : QuatInf (a : F) (b : F), β.imI = 0 → β.imJ = 0 → β.imK = 0 → γ.imI = 0 → γ.imJ = 0 →
        γ.imK = 0 → (β * γ).re = β.re * γ.re := by
      intro β γ h1 h2 h3 h4 h5 h6
      simp [QuaternionAlgebra.re_mul, h1, h2, h3, h4, h5, h6]
    have m1 : (α : QuatInf (a : F) (b : F)).re * ((α⁻¹ : (QuatInf (a : F) (b : F))ˣ) : QuatInf (a : F) (b : F)).re
        = 1 := by
      rw [← hre _ _ hI hJ hK hI' hJ' hK', Units.mul_inv]; rfl
    have m2 : ((α⁻¹ : (QuatInf (a : F) (b : F))ˣ) : QuatInf (a : F) (b : F)).re * (α : QuatInf (a : F) (b : F)).re
        = 1 := by rw [mul_comm, m1]
    refine ⟨⟨_, _, m1, m2⟩, Units.ext ?_⟩
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · rfl
    · exact hI.symm
    · exact hJ.symm
    · exact hK.symm
  · rintro ⟨c, rfl⟩
    refine Prod.ext (funext fun w => archSO_ext ?_) (funext fun w => archSOC_ext ?_)
    · refine (conjGL_eq_one_iff _ hA _).2 (mem_centerUnits.2 ⟨(c : mixedSpace F).1 w, ?_⟩)
      refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> rfl
    · refine (conjGL_eq_one_iff _ hA _).2 (mem_centerUnits.2 ⟨(c : mixedSpace F).2 w, ?_⟩)
      refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> rfl

end QuadFormsKB.Tamagawa.Measure.Weil
