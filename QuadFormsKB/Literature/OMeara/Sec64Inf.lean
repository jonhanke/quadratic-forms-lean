/-
# O'Meara §64 (local part, infinite spots): $E_\mathfrak P \supseteq F_\mathfrak p$ at archimedean spots

**Setting.** $E/F$ is an extension of number fields. An infinite spot $\mathfrak p$ of $F$ is a Mathlib
`InfinitePlace F` with completion `v.Completion` ($\mathbb R$ or $\mathbb C$); $\mathfrak P \mid \mathfrak p$ is
Mathlib's `w.LiesOver v`, and `w.Completion` is a `v.Completion`-algebra by Mathlib's scoped instance
(`NumberField.LiesOver`).

**Defines** `InfSpotsOver E v` (the infinite spots $\mathfrak P \mid \mathfrak p$) and `localNormInf v w`: the local norm
$N_{\mathfrak P|\mathfrak p}\colon E_\mathfrak P \to F_\mathfrak p$ (§15B, p. 32) at an infinite spot.

**Proves** `prod_localNormInf_eq_norm` (**15:3** at an infinite spot, for Mathlib's completions):
$\prod_{\mathfrak P|\mathfrak p} N_{\mathfrak P|\mathfrak p}(y) = N_{E/F}(y)$.
-/
import QuadFormsKB.Literature.OMeara.Sec64Local

open NumberField InfinitePlace

open scoped NumberField.LiesOver

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]
variable (v : InfinitePlace F)

/-- The infinite spots $\mathfrak P$ of $E$ with $\mathfrak P \mid \mathfrak p$. -/
abbrev InfSpotsOver : Type _ := {w : InfinitePlace E // w.LiesOver v}

instance (w : InfSpotsOver E v) : w.1.LiesOver v := w.2

noncomputable instance : Fintype (InfSpotsOver E v) := Fintype.ofFinite _

noncomputable instance : DecidableEq (InfSpotsOver E v) := Classical.decEq _

omit [NumberField F] in
lemma norm_two_completion (u : InfinitePlace F) : ‖(2 : u.Completion)‖ = 2 := by
  have := (AddMonoidHomClass.isometry_iff_norm (InfinitePlace.Completion.extensionEmbedding u)).1
    (InfinitePlace.Completion.isometry_extensionEmbedding u) 2
  rw [← this, map_ofNat]
  norm_num

/-- The completion at an infinite spot is a nontrivially normed field ($\lVert 2\rVert = 2$). -/
noncomputable instance (u : InfinitePlace F) : NontriviallyNormedField u.Completion :=
  .ofNormNeOne ⟨2, fun h => by have := norm_two_completion u; rw [h, norm_zero] at this; norm_num at this,
    by rw [norm_two_completion]; norm_num⟩

instance (w : InfinitePlace E) : IsScalarTower F E w.Completion := .of_algebraMap_eq fun c => by
  apply (InfinitePlace.Completion.equiv w).injective
  change (algebraMap F w.Completion c).toCompletion =
    (algebraMap E w.Completion (algebraMap F E c)).toCompletion
  rw [InfinitePlace.Completion.algebraMap_toCompletion, InfinitePlace.Completion.algebraMap_toCompletion,
    ← IsScalarTower.algebraMap_apply]

instance (w : InfinitePlace E) [w.LiesOver v] : FiniteDimensional v.Completion w.Completion := by
  refine Module.finite_of_finrank_pos ?_
  rw [← InfinitePlace.inertiaDeg_eq_finrank]
  rcases w.isUnramified_or_isRamified F with h | h
  · rw [InfinitePlace.inertiaDeg_eq_one ⟨inferInstance, h⟩]; norm_num
  · rw [InfinitePlace.inertiaDeg_eq_two ⟨inferInstance, h⟩]; norm_num

/-- **The local norm** $N_{\mathfrak P|\mathfrak p}\colon E_\mathfrak P \to F_\mathfrak p$ at an infinite spot (O'Meara
1963, §15B, p. 32, used in §64, p. 173). -/
@[kb "omeara1963" "§64, p. 173 (the norm map N_{𝔓|𝔭} : E_𝔓 → F_𝔭 of §15B at an infinite spot)"]
def localNormInf (w : InfinitePlace E) [w.LiesOver v] : w.Completion →* v.Completion :=
  Algebra.norm v.Completion

lemma localNormInf_apply (w : InfinitePlace E) [w.LiesOver v] (y : w.Completion) :
    localNormInf E v w y = Algebra.norm v.Completion y := rfl

/-- $\sum_{\mathfrak P|\mathfrak p} [E_\mathfrak P : F_\mathfrak p] = [E : F]$ at an infinite spot. -/
lemma sum_finrank_infSpotsOver :
    ∑ w : InfSpotsOver E v, Module.finrank v.Completion w.1.Completion = Module.finrank F E := by
  classical
  rw [← InfinitePlace.sum_inertiaDeg_eq_finrank F E v,
    ← Finset.sum_coe_sort (InfinitePlace.placesOver E v).toFinset]
  refine Fintype.sum_equiv (Equiv.subtypeEquivRight (p := fun w : InfinitePlace E => w.LiesOver v)
    (fun w => by rw [Set.mem_toFinset]; rfl)) _ _ fun w => ?_
  simp only [Equiv.subtypeEquivRight_apply_coe]
  rw [InfinitePlace.inertiaDeg_eq_finrank]

/-- **Weak approximation at the infinite spots over $\mathfrak p$:** $E$ is dense in $\prod_{\mathfrak P|\mathfrak p}
E_\mathfrak P$. -/
theorem denseRange_algebraMap_infSpotsOver :
    DenseRange (algebraMap E ((w : InfSpotsOver E v) → w.1.Completion)) := by
  have h1 := InfinitePlace.denseRange_algebraMap_pi E
  let ψ : ((w : InfinitePlace E) → WithAbs w.1) → ((w : InfSpotsOver E v) → w.1.Completion) :=
    fun x (w : InfSpotsOver E v) => (x w.1 : w.1.Completion)
  have hψc : Continuous ψ := continuous_pi fun w =>
    (InfinitePlace.Completion.continuous_coe w.1).comp (continuous_apply w.1)
  have hψd : DenseRange ψ := by
    have hd : DenseRange (fun (x : (w : InfSpotsOver E v) → WithAbs (w : InfinitePlace E).1)
        (w : InfSpotsOver E v) => (x w : (w : InfinitePlace E).Completion)) :=
      DenseRange.piMap fun (w : InfSpotsOver E v) => InfinitePlace.Completion.denseRange_coe w.1
    refine hd.mono ?_
    rintro _ ⟨x, rfl⟩
    classical
    exact ⟨fun u => if h : u.LiesOver v then x ⟨u, h⟩ else 0, by
      funext w; simp [ψ, w.2]⟩
  refine (hψd.comp h1 hψc).mono ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨y, rfl⟩

open scoped TensorProduct

/-- $F_\mathfrak p \otimes_F E \to \prod_{\mathfrak P|\mathfrak p} E_\mathfrak P$ is onto at an infinite spot. -/
theorem tensorToPi_infSpotsOver_surjective :
    Function.Surjective (tensorToPi (K := v.Completion) (F := F) (E := E)
      (fun w : InfSpotsOver E v => w.1.Completion)) := by
  let Φ := (tensorToPi (K := v.Completion) (F := F) (E := E)
      (fun w : InfSpotsOver E v => w.1.Completion)).toLinearMap
  change Function.Surjective Φ
  have hc : IsClosed (Φ.range : Set ((w : InfSpotsOver E v) → w.1.Completion)) :=
    Submodule.closed_of_finiteDimensional Φ.range
  have hd : DenseRange Φ := by
    refine (denseRange_algebraMap_infSpotsOver E v).mono ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨(1 : v.Completion) ⊗ₜ y, tensorToPi_one_tmul _ y⟩
  rw [← Set.range_eq_univ, ← Φ.coe_range, ← hc.closure_eq]
  exact hd.closure_range

/-- **O'Meara 15:3 at an infinite spot:** $\prod_{\mathfrak P|\mathfrak p} N_{\mathfrak P|\mathfrak p}(y) =
N_{E/F}(y)$ for $y \in E$ (equality in $F_\mathfrak p$). -/
@[kb "omeara1963" "§15B, 15:3 (2), p. 32 (at an infinite spot, for Mathlib's completions)"]
theorem prod_localNormInf_eq_norm (y : E) :
    ∏ w : InfSpotsOver E v, localNormInf E v w.1 (algebraMap E w.1.Completion y) =
      algebraMap F v.Completion (Algebra.norm F y) :=
  prod_norm_eq_of_surjective (fun w : InfSpotsOver E v => w.1.Completion)
    (tensorToPi_infSpotsOver_surjective E v) (sum_finrank_infSpotsOver E v) y

end QuadFormsKB.OMeara
