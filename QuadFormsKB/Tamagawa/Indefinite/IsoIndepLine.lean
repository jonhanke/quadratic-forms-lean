/-
# The norm-one measures do not depend on the isotropic vector

**Layer:** number fields. $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $N = r + 2$ variables (any signature),
$T_0$ nondegenerate of rank $r$, $\Xi$ a rational frame of $T_0$ with isotropic complement (`hiso`), the chosen frame
data
`isoTower` with complement form $Q''$ (binary, isotropic).

**Proves**
* `covolume_restrict_Ioc_eq_Ico` (abstract): in a commutative group with a left-invariant measure $\nu$, a countable subgroup
  $\Lambda$ with an exact measurable fundamental domain, and a homomorphism $L$ to $(\mathbb R, +)$, trivial on $\Lambda$ and
  taking the value $1$,
  $$\operatorname{covol}(\Lambda, \nu|_{L^{-1}(-1,0]}) = \operatorname{covol}(\Lambda, \nu|_{L^{-1}[0,1)});$$
* `covolume_map_isoConjOf`: the covolume of $\Gamma'\cap H_X$ for a measure transported by $h\mapsto a\,\iota_D(h)\,a^{-1}$
  ($a\,\Xi_\infty = X$) is the covolume of $\{h : a\,\iota_D(h)\,a^{-1}\in\Gamma'\}$ in $SO(Q''_D)(F_\infty)$ (any frame data `D`,
  as in `covolume_isoStabAt`);
* **`repMeasureIsoOf_isoTower_vec`**: for the frame data and **every** isotropic vector $u$ of $Q''$,
  `repMeasureIsoOf … isoTower hu i = repMeasureIso … i`. On the same isotropic line the characters agree
  (`isoChar_smul`); on the other line $\chi_u = \chi_e^{-1}$ (`isoChar_other_line`), the shell $\{0\le\log|\chi_u|_\infty<1\}$ is
  $\{-1<\log|\chi_e|_\infty\le0\}$, and the covolumes agree by the abstract lemma ($|\chi_e|_\infty = 1$ on the level
  groups).
-/
import QuadFormsKB.Tamagawa.Indefinite.StabCompareIsoChoice
import QuadFormsKB.Tamagawa.Indefinite.IsoDictionary
import QuadFormsKB.Tamagawa.Indefinite.IsoHyps

open MeasureTheory Measure Set MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames

/-! ### The abstract lemma: shifting the shell by one period -/

section Abstract

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]

/-- On a $\Lambda$-invariant set, two exact measurable fundamental domains have the same measure. -/
theorem measure_inter_eq_of_exact (ν : Measure H) [ν.IsMulLeftInvariant] (Λ : Subgroup H) [Countable Λ]
    {E E' : Set H} (hEm : MeasurableSet E) (hE : ∀ h : H, ∃! γ : Λ, γ • h ∈ E) (hEm' : MeasurableSet E')
    (hE' : ∀ h : H, ∃! γ : Λ, γ • h ∈ E') {A : Set H} (hA : ∀ (γ : Λ) (h : H), γ • h ∈ A ↔ h ∈ A) :
    ν (E ∩ A) = ν (E' ∩ A) := by
  haveI := measurableConstSMul_subgroup Λ
  haveI := smulInvariantMeasure_subgroup Λ ν
  haveI := smulInvariantMeasure_restrict Λ ν hA
  have h1 := (IsFundamentalDomain.mk' (μ := ν.restrict A) hEm.nullMeasurableSet hE).measure_eq
    (IsFundamentalDomain.mk' (μ := ν.restrict A) hEm'.nullMeasurableSet hE')
  rwa [Measure.restrict_apply hEm, Measure.restrict_apply hEm'] at h1

/-- **The covolume of a shell does not depend on its position** (abstract form): in a commutative group with a left-invariant
measure $\nu$, a countable subgroup $\Lambda$ with an exact measurable fundamental domain $E$, and a measurable homomorphism
$L : H\to(\mathbb R, +)$ trivial on $\Lambda$ with $L(s) = 1$ for some $s$,
$\operatorname{covol}(\Lambda, \nu|_{L^{-1}(-1,0]}) = \operatorname{covol}(\Lambda, \nu|_{L^{-1}[0,1)})$.
*Proof.* Both are $\nu(E\cap\cdot)$; split off $L^{-1}\{0\}$; $E\cap L^{-1}(0,1)$ is the right translate by $s$ of
$Es^{-1}\cap L^{-1}(-1,0)$, $\nu$ is right invariant ($H$ is commutative) and $Es^{-1}$ is another exact fundamental domain. -/
theorem covolume_restrict_Ioc_eq_Ico (hcomm : ∀ a b : H, a * b = b * a) (ν : Measure H) [ν.IsMulLeftInvariant]
    (Λ : Subgroup H) [Countable Λ] {E : Set H} (hEm : MeasurableSet E) (hE : ∀ h : H, ∃! γ : Λ, γ • h ∈ E)
    (L : H → ℝ) (hLm : Measurable L) (hL : ∀ a b, L (a * b) = L a + L b) (hLΛ : ∀ γ : Λ, L γ = 0) {s : H}
    (hs : L s = 1) :
    covolume Λ H (ν.restrict (L ⁻¹' Ioc (-1) 0)) = covolume Λ H (ν.restrict (L ⁻¹' Ico 0 1)) := by
  haveI := measurableConstSMul_subgroup Λ
  haveI := smulInvariantMeasure_subgroup Λ ν
  have hinv : ∀ (I : Set ℝ) (γ : Λ) (h : H), γ • h ∈ L ⁻¹' I ↔ h ∈ L ⁻¹' I := fun I γ h => by
    simp only [Set.mem_preimage, Subgroup.smul_def, smul_eq_mul, hL, hLΛ, zero_add]
  have hcov : ∀ I : Set ℝ, covolume Λ H (ν.restrict (L ⁻¹' I)) = ν (E ∩ L ⁻¹' I) := fun I => by
    haveI := smulInvariantMeasure_restrict Λ ν (hinv I)
    rw [(IsFundamentalDomain.mk' (μ := ν.restrict (L ⁻¹' I)) hEm.nullMeasurableSet hE).covolume_eq_volume,
      Measure.restrict_apply hEm]
  rw [hcov, hcov]
  -- the translated fundamental domain
  set E' : Set H := (fun x => x * s) ⁻¹' E with hE'def
  have hEm' : MeasurableSet E' := hEm.preimage (measurable_mul_const s)
  have hE' : ∀ h : H, ∃! γ : Λ, γ • h ∈ E' := fun h => by
    obtain ⟨γ, hγ, huniq⟩ := hE (h * s)
    refine ⟨γ, ?_, fun γ' hγ' => huniq γ' ?_⟩
    · show (γ : H) * h * s ∈ E
      rw [mul_assoc]; exact hγ
    · have : (γ' : H) * h * s ∈ E := hγ'
      show (γ' : H) * (h * s) ∈ E
      rwa [← mul_assoc]
  -- right translation by `s` preserves `ν`
  have hright : ∀ B : Set H, ν ((fun x => x * s) ⁻¹' B) = ν B := fun B => by
    rw [show (fun x : H => x * s) = (fun x => s * x) from funext fun x => hcomm x s]
    exact measure_preimage_mul ν s B
  have hshift : (fun x => x * s) ⁻¹' (E ∩ L ⁻¹' Ioo 0 1) = E' ∩ L ⁻¹' Ioo (-1) 0 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ioo, hL, hs, hE'def]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
  have hmid : ν (E ∩ L ⁻¹' Ioo (-1) 0) = ν (E ∩ L ⁻¹' Ioo 0 1) := by
    rw [← hright (E ∩ L ⁻¹' Ioo 0 1), hshift]
    exact measure_inter_eq_of_exact ν Λ hEm hE hEm' hE' (hinv _)
  have hm : ∀ I : Set ℝ, MeasurableSet I → MeasurableSet (E ∩ L ⁻¹' I) := fun I hI => hEm.inter (hLm hI)
  have e1 : E ∩ L ⁻¹' Ioc (-1) 0 = (E ∩ L ⁻¹' Ioo (-1) 0) ∪ (E ∩ L ⁻¹' {0}) := by
    rw [← Set.inter_union_distrib_left, ← Set.preimage_union, Set.Ioo_union_right (by norm_num)]
  have e2 : E ∩ L ⁻¹' Ico 0 1 = (E ∩ L ⁻¹' Ioo 0 1) ∪ (E ∩ L ⁻¹' {0}) := by
    rw [← Set.inter_union_distrib_left, ← Set.preimage_union, Set.Ioo_union_left (by norm_num)]
  have d1 : Disjoint (E ∩ L ⁻¹' Ioo (-1) 0) (E ∩ L ⁻¹' {0}) :=
    ((Set.disjoint_singleton_right.2 (fun h => (Set.mem_Ioo.1 h).2.ne rfl)).preimage L).mono
      Set.inter_subset_right Set.inter_subset_right
  have d2 : Disjoint (E ∩ L ⁻¹' Ioo 0 1) (E ∩ L ⁻¹' {0}) :=
    ((Set.disjoint_singleton_right.2 (fun h => (Set.mem_Ioo.1 h).1.ne rfl)).preimage L).mono
      Set.inter_subset_right Set.inter_subset_right
  rw [e1, e2, measure_union d1 (hm _ (measurableSet_singleton 0)),
    measure_union d2 (hm _ (measurableSet_singleton 0)), hmid]

end Abstract

/-! ### Transport of the covolume to $SO(Q''_D)(F_\infty)$, any frame data -/

section Transport

variable {F : Type} [Field F] [NumberField F] {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 2)) (hQ : Q₀.Nondegenerate)
  (T₀ : QuadForm (𝓞 F) r) (Ξ : RatFrame Q₀ T₀) (D : FrameTowerAlg Q₀ hQ 2 (cols Ξ.1))

/-- **Transport of a stabilizer covolume** to $SO(Q''_D)(F_\infty)$ (any frame data `D`, any measure $\mu$): for $X = a\,\Xi_\infty$
and a countable subgroup $\Gamma'\le G_\infty$, the covolume of $\Gamma'\cap H_X$ for $\mu$ carried by $h\mapsto a\,\iota_D(h)\,a^{-1}$
is the covolume of $\{h : a\,\iota_D(h)\,a^{-1}\in\Gamma'\}$ for $\mu$ (as in `covolume_isoStabAt`). -/
theorem covolume_map_isoConjOf (Γ' : Subgroup (GInfSO Q₀)) [Countable Γ'] (a : GInfSO Q₀)
    {X : Fin r → VInf F (r + 2)} (hX : a • ratAT Q₀ T₀ Ξ = X) (μ : Measure (GInfSO D.Q''))
    [SMulInvariantMeasure (Γ'.comap ((MulAut.conj a).toMonoidHom.comp D.ιInf)) (GInfSO D.Q'') μ] :
    covolume (stabArith Γ' X) (stabilizer (GInfSO Q₀) X) (μ.map (isoConjOf Q₀ hQ T₀ Ξ D a hX)) =
      covolume (Γ'.comap ((MulAut.conj a).toMonoidHom.comp D.ιInf)) (GInfSO D.Q'') μ := by
  subst hX
  have hconj : (isoConjOf Q₀ hQ T₀ Ξ D a rfl : GInfSO D.Q'' → stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ)) =
      D.conjInf Q₀ hQ T₀ Ξ a := rfl
  rw [hconj]
  set φ0 := D.conjInf Q₀ hQ T₀ Ξ a with hφ0
  have hbij : Function.Bijective φ0 := by
    refine ⟨fun h h' e => D.ιInf_injective Q₀ hQ T₀ Ξ ?_, fun s => ?_⟩
    · have := congrArg (fun z : stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ) => a⁻¹ * (z : GInfSO Q₀) * a) e
      simpa [hφ0, FrameTowerAlg.conjInf_apply, mul_assoc] using this
    · obtain ⟨h, hh⟩ := D.stab_ιInf Q₀ hQ T₀ Ξ (a⁻¹ * s * a) (by
        rw [mul_smul, mul_smul, s.2, inv_smul_smul])
      exact ⟨h, Subtype.ext (by simp [hφ0, FrameTowerAlg.conjInf_apply, hh, mul_assoc])⟩
  set φ : GInfSO D.Q'' ≃* stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ) := MulEquiv.ofBijective φ0 hbij with hφ
  have hφm : Measurable φ := D.measurable_conjInf Q₀ hQ T₀ Ξ a
  have hφm' : Measurable φ.symm := by
    have hME := D.measurableEmbedding_ιInf Q₀ hQ T₀ Ξ
    have hrange : ∀ s : stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ), a⁻¹ * s * a ∈ Set.range D.ιInf := fun s =>
      D.stab_ιInf Q₀ hQ T₀ Ξ _ (by rw [mul_smul, mul_smul, s.2, inv_smul_smul])
    have hm : Measurable fun s : stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ) =>
        (⟨a⁻¹ * s * a, hrange s⟩ : Set.range D.ιInf) :=
      (((measurable_const_mul a⁻¹).comp measurable_subtype_coe).mul_const a).subtype_mk
    have heq : (φ.symm : stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ) → GInfSO D.Q'') =
        fun s : stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ) =>
          hME.equivRange.symm ⟨a⁻¹ * (s : GInfSO Q₀) * a, hrange s⟩ := by
      funext s
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      have h1 := congrArg Subtype.val (hME.equivRange.apply_symm_apply ⟨a⁻¹ * s * a, hrange s⟩)
      simp only [MeasurableEmbedding.equivRange_apply] at h1
      show (s : GInfSO Q₀) = a * D.ιInf _ * a⁻¹
      rw [h1]; group
    rw [heq]
    exact hME.equivRange.symm.measurable.comp hm
  have hΓ : (Γ'.comap ((MulAut.conj a).toMonoidHom.comp D.ιInf)).map φ.toMonoidHom =
      stabArith Γ' (a • ratAT Q₀ T₀ Ξ) := by
    ext s
    constructor
    · rintro ⟨h, hh, rfl⟩
      show ((φ h : stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ)) : GInfSO Q₀) ∈ Γ'
      exact hh
    · intro hs
      obtain ⟨h, rfl⟩ := hbij.2 s
      exact ⟨h, hs, rfl⟩
  haveI : Countable (stabArith Γ' (a • ratAT Q₀ T₀ Ξ)) := by
    refine Function.Injective.countable (f := fun γ : stabArith Γ' (a • ratAT Q₀ T₀ Ξ) =>
      (⟨((γ : stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ)) : GInfSO Q₀), Subgroup.mem_subgroupOf.mp γ.2⟩ : Γ'))
      fun γ γ' h => ?_
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  haveI : Countable (Γ'.comap ((MulAut.conj a).toMonoidHom.comp D.ιInf)) := by
    refine Function.Injective.countable (f := fun h : Γ'.comap ((MulAut.conj a).toMonoidHom.comp D.ιInf) =>
      (⟨_, h.2⟩ : Γ')) fun h h' e => ?_
    apply Subtype.ext
    apply D.ιInf_injective Q₀ hQ T₀ Ξ
    have := congrArg Subtype.val e
    simpa using this
  haveI := measurableMul_subgroup (stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ))
  haveI : SMulInvariantMeasure (stabArith Γ' (a • ratAT Q₀ T₀ Ξ)) (stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ))
      (μ.map φ) :=
    smulInvariantMeasure_map_of_equiv φ hφm _ _ hΓ _
  exact (covolume_restrict_eq_of_map _ _ φ hφm hφm' hΓ _ _ rfl).symm

end Transport

/-! ### Two isotropic vectors of a binary form -/

section Lines

variable {F : Type} [Field F] [NumberField F]

/-- Two nonzero vectors of $F^2$ with vanishing determinant are proportional. -/
theorem exists_smul_of_det_eq_zero {e u : Fin 2 → F} (he : e ≠ 0) (hu : u ≠ 0)
    (h : e 0 * u 1 - e 1 * u 0 = 0) : ∃ t : F, t ≠ 0 ∧ u = t • e := by
  by_cases h0 : e 0 = 0
  · have h1 : e 1 ≠ 0 := fun h1 => he (funext fun i => by fin_cases i <;> simp [h0, h1])
    have hu0 : u 0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.1 h).resolve_left h1
    have hu1 : u 1 ≠ 0 := fun hu1 => hu (funext fun i => by fin_cases i <;> simp [hu0, hu1])
    refine ⟨u 1 / e 1, div_ne_zero hu1 h1, funext fun i => ?_⟩
    fin_cases i
    · simp [h0, hu0]
    · simp [h1]
  · have hu0 : u 0 ≠ 0 := by
      intro hu0
      rw [hu0, mul_zero, sub_zero] at h
      have hu1 : u 1 = 0 := (mul_eq_zero.1 h).resolve_left h0
      exact hu (funext fun i => by fin_cases i <;> simp [hu0, hu1])
    refine ⟨u 0 / e 0, div_ne_zero hu0 h0, funext fun i => ?_⟩
    fin_cases i
    · simp [h0]
    · show u 1 = u 0 / e 0 * e 1
      rw [div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination h

/-- $|\chi_e|_\infty$ only depends on the archimedean character $\chi_e$ on $G_\infty$. -/
theorem isoNormInf_eq_of_isoCharInf {Q Q' : QuadForm (𝓞 F) 2} {hQ : Q.Nondegenerate} {hQ' : Q'.Nondegenerate}
    {e e' : Fin 2 → F} {he : IsIsoVec Q e} {he' : IsIsoVec Q' e'} {a : GInfSO Q} {a' : GInfSO Q'}
    (h : isoCharInf hQ he a = isoCharInf hQ' he' a') : isoNormInf Q hQ he a = isoNormInf Q' hQ' he' a' := by
  unfold isoNormInf
  congr 1
  apply Units.ext
  rw [isoChar_val, isoChar_val]
  exact Prod.ext h (by simp only [map_one])

variable (Q : QuadForm (𝓞 F) 2) (hQ : Q.Nondegenerate) {e : Fin 2 → F} (he : IsIsoVec Q e)

/-- **The shell of the other isotropic line**: if $e, u$ span different isotropic lines, then
$\{0\le\log|\chi_u|_\infty<1\} = \{-1<\log|\chi_e|_\infty\le0\}$. -/
theorem isoShellInf_other_line {u : Fin 2 → F} (hu : IsIsoVec Q u) (hdet : e 0 * u 1 - e 1 * u 0 ≠ 0) :
    isoShellInf Q hQ hu = (fun a => Real.log (isoNormInf Q hQ he a)) ⁻¹' Ioc (-1) 0 := by
  ext a
  have hn : isoNormInf Q hQ hu a = (isoNormInf Q hQ he a)⁻¹ := by
    unfold isoNormInf
    rw [isoChar_other_line hQ he hu hdet, ideleNorm_inv]
  simp only [isoShellInf, Set.mem_preimage, Set.mem_Ico, Set.mem_Ioc, hn, Real.log_inv]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

end Lines

/-! ### The frame data with an arbitrary isotropic vector -/

section Tower

variable {F : Type} [Field F] [NumberField F] {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 2)) (hQ : Q₀.Nondegenerate)
  (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (hiso : IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀)))
  (Ξ : RatFrame Q₀ T₀)

local notation "𝔇" => isoTower Q₀ hQ T₀ hT Ξ
local notation "𝔢" => isIsoVec_isoVec Q₀ hQ T₀ hT hiso Ξ

/-- $|\chi_u|_\infty = 1$ on the level groups, for every isotropic vector $u$ (product formula; $\chi_u$ is a unit at
every
finite place of the orbit stabilizers, `isoCharV_unit_orbitStab`). -/
theorem isoNormInf_levelGroup_orbitStab {u : Fin 2 → F} (hu : IsIsoVec (𝔇).Q'' u) (b : SOAf Q₀)
    (γ : levelGroup (GammaSOAdele (𝔇).Q'') (orbitStab (𝔇).ιFin (KSO Q₀) b) 1) :
    isoNormInf (𝔇).Q'' (𝔇).hQ'' hu γ = 1 :=
  isoNormInf_levelGroup (𝔇).Q'' (𝔇).hQ'' hu (orbitStab (𝔇).ιFin (KSO Q₀) b)
    (fun x hx => isoNormFin_eq_one_of_units _ _ hu x (isoCharV_unit_orbitStab Q₀ hQ T₀ Ξ 𝔇 hu b x hx)) 1 γ

/-- The level groups preserve the shell of every isotropic vector $u$. -/
theorem smulInvariantMeasure_isoStabBaseOf {u : Fin 2 → F} (hu : IsIsoVec (𝔇).Q'' u) (b : SOAf Q₀) :
    SMulInvariantMeasure (levelGroup (GammaSOAdele (𝔇).Q'') (orbitStab (𝔇).ιFin (KSO Q₀) b) 1) (GInfSO (𝔇).Q'')
      (isoStabBaseOf Q₀ hQ T₀ hT Ξ 𝔇 hu) := by
  haveI := measurableConstSMul_subgroup (levelGroup (GammaSOAdele (𝔇).Q'') (orbitStab (𝔇).ιFin (KSO Q₀) b) 1)
  haveI := smulInvariantMeasure_subgroup (levelGroup (GammaSOAdele (𝔇).Q'') (orbitStab (𝔇).ιFin (KSO Q₀) b) 1)
    (muArchTamSO (𝔇).Q'' (𝔇).hQ'')
  haveI : SMulInvariantMeasure (levelGroup (GammaSOAdele (𝔇).Q'') (orbitStab (𝔇).ιFin (KSO Q₀) b) 1)
      (GInfSO (𝔇).Q'') ((muArchTamSO (𝔇).Q'' (𝔇).hQ'').restrict (isoShellInf (𝔇).Q'' (𝔇).hQ'' hu)) :=
    smulInvariantMeasure_restrict _ _ fun γ a => by
      show Real.log (isoNormInf _ _ hu ((γ : GInfSO (𝔇).Q'') * a)) ∈ Ico 0 1 ↔ Real.log (isoNormInf _ _ hu a) ∈ Ico 0 1
      rw [isoNormInf_mul, isoNormInf_levelGroup_orbitStab Q₀ hQ T₀ hT Ξ hu b γ, one_mul]
  exact smulInvariantMeasure_smul' _ _

set_option maxHeartbeats 1600000 in
include hiso in
/-- **A term of $\rho^1$ for an arbitrary isotropic vector**, transported to $SO(Q'')(F_\infty)$: at $X = \gamma\,\Xi$ the covolume of
$\Gamma_{i,X}$ for `isoStabMeasureOf isoTower hu X` is the covolume of the level group $\Gamma_{U_b}$,
$b = b_i^{-1}\gamma_f$, for
`isoStabBaseOf isoTower hu`. -/
theorem covolume_isoStabMeasureOf_isoTower (i : DC Q₀) (γ : GammaSOAdele Q₀) {u : Fin 2 → F}
    (hu : IsIsoVec (𝔇).Q'' u) :
    covolume (stabArith (unitGroup Q₀ i) (ratAT Q₀ T₀ (γ • Ξ))) (stabilizer (GInfSO Q₀) (ratAT Q₀ T₀ (γ • Ξ)))
        (isoStabMeasureOf Q₀ hQ T₀ hT Ξ 𝔇 hu (ratAT Q₀ T₀ (γ • Ξ))) =
      covolume (levelGroup (GammaSOAdele (𝔇).Q'') (orbitStab (𝔇).ιFin (KSO Q₀)
        ((dcRep Q₀ i)⁻¹ * (γ : SOAdele Q₀).2)) 1) (GInfSO (𝔇).Q'') (isoStabBaseOf Q₀ hQ T₀ hT Ξ 𝔇 hu) := by
  have hX : ∃ a : GInfSO Q₀, a • ratAT Q₀ T₀ Ξ = ratAT Q₀ T₀ (γ • Ξ) :=
    ⟨(γ : SOAdele Q₀).1, (ratAT_smul Q₀ T₀ γ Ξ).symm⟩
  rw [isoStabMeasureOf, dif_pos hX]
  have hcomap := comap_unitGroup_eq Q₀ hQ T₀ hT hiso Ξ i γ hX.choose hX.choose_spec
  haveI := countable_GammaSOAdele Q₀
  haveI : Countable (unitGroup Q₀ i) := countable_levelGroup (Γ := GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i)
  haveI hinv' : SMulInvariantMeasure ((unitGroup Q₀ i).comap ((MulAut.conj hX.choose).toMonoidHom.comp (𝔇).ιInf))
      (GInfSO (𝔇).Q'') (isoStabBaseOf Q₀ hQ T₀ hT Ξ 𝔇 hu) := by
    rw [hcomap]
    exact smulInvariantMeasure_isoStabBaseOf Q₀ hQ T₀ hT Ξ hu _
  rw [covolume_map_isoConjOf Q₀ hQ T₀ Ξ 𝔇 (unitGroup Q₀ i) hX.choose hX.choose_spec]
  rw [show covolume ((unitGroup Q₀ i).comap ((MulAut.conj hX.choose).toMonoidHom.comp (𝔇).ιInf)) (GInfSO (𝔇).Q'')
      (isoStabBaseOf Q₀ hQ T₀ hT Ξ 𝔇 hu) = covolume (levelGroup (GammaSOAdele (𝔇).Q'') (orbitStab (𝔇).ιFin (KSO Q₀)
        ((dcRep Q₀ i)⁻¹ * (γ : SOAdele Q₀).2)) 1) (GInfSO (𝔇).Q'') (isoStabBaseOf Q₀ hQ T₀ hT Ξ 𝔇 hu) by
    rw [hcomap]]

include hiso in
/-- **The covolumes of the two shells agree** on $SO(Q'')(F_\infty)$ for the level groups: for every isotropic vector
$u$ of
$Q''$, the covolume of $\Gamma_{U_b}$ for `isoStabBaseOf isoTower hu` is the one for the vector. -/
theorem covolume_isoStabBaseOf_isoTower (b : SOAf Q₀) {u : Fin 2 → F} (hu : IsIsoVec (𝔇).Q'' u) :
    covolume (levelGroup (GammaSOAdele (𝔇).Q'') (orbitStab (𝔇).ιFin (KSO Q₀) b) 1) (GInfSO (𝔇).Q'')
        (isoStabBaseOf Q₀ hQ T₀ hT Ξ 𝔇 hu) =
      covolume (levelGroup (GammaSOAdele (𝔇).Q'') (orbitStab (𝔇).ιFin (KSO Q₀) b) 1) (GInfSO (𝔇).Q'')
        (isoStabBaseOf Q₀ hQ T₀ hT Ξ 𝔇 𝔢) := by
  set e := isoVec Q₀ hQ T₀ hT hiso Ξ with he_def
  by_cases hdet : e 0 * u 1 - e 1 * u 0 = 0
  · -- the same line: the same character
    obtain ⟨t, ht, rfl⟩ := exists_smul_of_det_eq_zero (𝔢).1 hu.1 hdet
    have hS : isoShellInf (𝔇).Q'' (𝔇).hQ'' hu = isoShellInf (𝔇).Q'' (𝔇).hQ'' 𝔢 := by
      ext a
      simp only [isoShellInf, isoNormInf, Set.mem_preimage]
      rw [isoChar_smul (𝔇).hQ'' 𝔢 ht]
    unfold isoStabBaseOf
    rw [hS]
  · -- the other line
    haveI := countable_GammaSOAdele (𝔇).Q''
    haveI : DiscreteTopology (levelGroup (GammaSOAdele (𝔇).Q'') (orbitStab (𝔇).ιFin (KSO Q₀) b) 1) :=
      discreteTopology_levelGroup_orbitStab Q₀ hQ T₀ hT Ξ b 1
    haveI := countable_levelGroup (Γ := GammaSOAdele (𝔇).Q'') (orbitStab (𝔇).ιFin (KSO Q₀) b) 1
    obtain ⟨E, hEm, hE⟩ := exists_measurableSet_forall_existsUnique_smul_mem
      (levelGroup (GammaSOAdele (𝔇).Q'') (orbitStab (𝔇).ιFin (KSO Q₀) b) 1)
    obtain ⟨s, hs⟩ := exists_isoNormInf_eq (𝔇).Q'' (𝔇).hQ'' 𝔢 (Real.exp_pos 1)
    have key := covolume_restrict_Ioc_eq_Ico (mul_comm_GInfSO_iso (𝔇).Q'' (𝔇).hQ'' 𝔢)
      (isoFrameLamOf Q₀ hQ T₀ hT Ξ 𝔇 • muArchTamSO (𝔇).Q'' (𝔇).hQ'')
      (levelGroup (GammaSOAdele (𝔇).Q'') (orbitStab (𝔇).ιFin (KSO Q₀) b) 1) hEm hE
      (fun a => Real.log (isoNormInf (𝔇).Q'' (𝔇).hQ'' 𝔢 a))
      (Real.measurable_log.comp (measurable_isoNormInf (𝔇).Q'' (𝔇).hQ'' 𝔢))
      (fun a a' => by
        rw [isoNormInf_mul, Real.log_mul (isoNormInf_pos _ _ _ a).ne' (isoNormInf_pos _ _ _ a').ne'])
      (fun γ => by
        show Real.log (isoNormInf _ _ 𝔢 γ) = 0
        rw [isoNormInf_levelGroup_orbitStab Q₀ hQ T₀ hT Ξ 𝔢 b γ, Real.log_one])
      (s := s) (by rw [hs, Real.log_exp])
    unfold isoStabBaseOf
    rw [isoShellInf_other_line (𝔇).Q'' (𝔇).hQ'' 𝔢 hu hdet, ← Measure.restrict_smul, key, Measure.restrict_smul]
    rfl

set_option maxHeartbeats 1600000 in
include hiso in
/-- **The measures of representations do not depend on the isotropic vector**: for the frame data `isoTower` and every
isotropic vector $u$ of its complement form, `repMeasureIsoOf … isoTower hu i` is the `repMeasureIso … i`. -/
theorem repMeasureIsoOf_isoTower_vec {u : Fin 2 → F} (hu : IsIsoVec (𝔇).Q'' u) (i : DC Q₀) :
    repMeasureIsoOf Q₀ hQ T₀ hT Ξ 𝔇 hu i = repMeasureIso Q₀ hQ T₀ hT hiso Ξ i := by
  rw [← repMeasureIsoOf_isoTower Q₀ hQ T₀ hT Ξ hiso i]
  unfold repMeasureIsoOf repMeasureOf
  refine tsum_congr fun q => ?_
  have hterm : ∀ X : Fin r → VInf F (r + 2), (∃ γ : GammaSOAdele Q₀, ratAT Q₀ T₀ (γ • Ξ) = X) →
      covolume (stabArith (unitGroup Q₀ i) X) (stabilizer (GInfSO Q₀) X) (isoStabMeasureOf Q₀ hQ T₀ hT Ξ 𝔇 hu X) =
        covolume (stabArith (unitGroup Q₀ i) X) (stabilizer (GInfSO Q₀) X)
          (isoStabMeasureOf Q₀ hQ T₀ hT Ξ 𝔇 𝔢 X) := by
    rintro X ⟨γ, rfl⟩
    rw [covolume_isoStabMeasureOf_isoTower Q₀ hQ T₀ hT hiso Ξ i γ hu,
      covolume_isoStabMeasureOf_isoTower Q₀ hQ T₀ hT hiso Ξ i γ 𝔢,
      covolume_isoStabBaseOf_isoTower Q₀ hQ T₀ hT hiso Ξ _ hu]
  obtain ⟨γ, hγ, -⟩ := exists_gamma_of_rep Q₀ hQ T₀ hT Ξ i (q.out : repsT Q₀ T₀ i)
  exact hterm _ ⟨γ, hγ⟩

end Tower

end QuadFormsKB.Tamagawa.Indefinite
