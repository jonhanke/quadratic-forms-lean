/-
# O'Meara §102A: all lattices in a genus have the same volume

**Layer:** $V = F^n$ over a number field $F$, `Q : QuadForm F n`, lattices `Lat F n`, $S$ = all finite spots; the
completion $\mathfrak a_\mathfrak p$ of a fractional ideal is `locFrac v 𝔞` (`Sec104LocalMod.lean`).

**Proves** (O'Meara 1973)
* `eq_of_forall_locFrac_eq`: an $\mathcal O_F$-submodule of $F$ that is finitely generated is determined by its
  completions $\mathfrak a_\mathfrak p$ at the finite spots (via the local–global principle for lattices on $F^1$,
  `loc_injective`);
* **`omeara102_r18_holds`** (§102A, p. 299, "All lattices in the same genus have the same volume"): the named
  statement `OMeara102_r18 Q` holds, unconditionally. O'Meara's proof: $(\mathfrak vK)_\mathfrak p = \mathfrak vK_\mathfrak p
  = \mathfrak v(\sigma_\mathfrak pL_\mathfrak p) = \mathfrak vL_\mathfrak p = (\mathfrak vL)_\mathfrak p$ for every $\mathfrak p$
  (82:12 and §82K at the completion, `volume_loc`).
-/
import QuadFormsKB.Literature.OMeara.Sec104Bridge
import QuadFormsKB.Literature.OMeara.Sec104LocalMod

open NumberField IsDedekindDomain Matrix Submodule
open QuadFormsKB.OMeara.QIn (glEquiv map_orthGroup)

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

section Ideals

/-- The $\mathcal O_F$-linear embedding $F \to F^1$, $x \mapsto (x)$. -/
def lineEmb : F →ₗ[𝓞 F] (Fin 1 → F) := LinearMap.pi fun _ => LinearMap.id

theorem lineEmb_apply (x : F) (i : Fin 1) : lineEmb x i = x := rfl

theorem lineEmb_injective : Function.Injective (lineEmb (F := F)) := fun x y h => by
  simpa [lineEmb_apply] using congrFun h 0

/-- A non-zero finitely generated $\mathcal O_F$-submodule $\mathfrak a$ of $F$ is a lattice on $F^1$ (under
`lineEmb`). -/
theorem isLattice_map_lineEmb {a : Submodule (𝓞 F) F} (hfg : a.FG) (h0 : a ≠ ⊥) :
    (a.map (lineEmb (F := F))).IsLattice F := by
  refine ⟨hfg.map _, ?_⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  rw [eq_top_iff]
  intro y _
  have hxm : lineEmb x ∈ Submodule.span F ((a.map (lineEmb (F := F)) : Set (Fin 1 → F))) :=
    Submodule.subset_span ⟨x, hx, rfl⟩
  have : y = (y 0 / x) • lineEmb x := by
    funext i
    fin_cases i
    simp [lineEmb_apply, hx0]
  rw [this]
  exact Submodule.smul_mem _ _ hxm

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- The completion of the line lattice $\mathfrak a$ on $F^1$ is the line lattice $\mathfrak a_\mathfrak p$ on
$F_\mathfrak p^1$. -/
theorem loc_map_lineEmb (a : Submodule (𝓞 F) F) :
    loc v (a.map (lineEmb (F := F))) =
      (locFrac v a).map (LinearMap.pi fun _ => (LinearMap.id : Fv →ₗ[𝔬] Fv)) := by
  rw [loc, locFrac, Submodule.map_span, ← Set.image_comp, Submodule.map_coe, ← Set.image_comp]
  congr 1

/-- **A finitely generated $\mathcal O_F$-submodule of $F$ is determined by its completions** (O'Meara 1973, §81E,
p. 217, for fractional ideals): if $\mathfrak a_\mathfrak p = \mathfrak b_\mathfrak p$ at every finite spot then
$\mathfrak a = \mathfrak b$. -/
@[kb "omeara1963" "§81E, p. 217 (a fractional ideal is determined by its completions)"]
theorem eq_of_forall_locFrac_eq {a b : Submodule (𝓞 F) F} (ha : a.FG) (hb : b.FG)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), locFrac v a = locFrac v b) : a = b := by
  obtain ⟨v₀⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := inferInstance
  by_cases ha0 : a = ⊥
  · by_contra hab
    have hb0 : b ≠ ⊥ := fun hb0 => hab (ha0.trans hb0.symm)
    have := locFrac_ne_bot v₀ hb0
    rw [← h v₀, ha0] at this
    exact this (by simp [locFrac])
  by_cases hb0 : b = ⊥
  · exfalso
    have := locFrac_ne_bot v₀ ha0
    rw [h v₀, hb0] at this
    exact this (by simp [locFrac])
  have hinj := loc_injective (isLattice_map_lineEmb ha ha0) (isLattice_map_lineEmb hb hb0)
    (fun v => by rw [loc_map_lineEmb, loc_map_lineEmb, h v])
  exact Submodule.map_injective_of_injective lineEmb_injective hinj

end Ideals

/-- **102.r18: all lattices in a genus have the same volume** (O'Meara 1973, §102A, p. 299): the named statement
`OMeara102_r18 Q` holds for every form $Q$ on $F^n$ over a number field $F$. *Proof* (O'Meara's): for $K \in
\operatorname{gen}L$ and every finite spot $\mathfrak p$, $K_\mathfrak p = \sigma_\mathfrak pL_\mathfrak p$ with
$\sigma_\mathfrak p \in O(V_\mathfrak p)$, so $(\mathfrak vK)_\mathfrak p = \mathfrak vK_\mathfrak p = \mathfrak vL_\mathfrak p
= (\mathfrak vL)_\mathfrak p$ (82:12, `volume_latMap`; §82K at the completion, `volume_loc`); a fractional ideal is
determined by its completions (`eq_of_forall_locFrac_eq`). Unconditional. -/
@[kb "omeara1963" "§102A, p. 299 (all lattices in a genus have the same volume)"]
theorem omeara102_r18_holds (Q : QuadForm F n) : OMeara102_r18 Q := by
  refine ⟨fun L K hLK => ?_⟩
  unfold genusVolume
  apply eq_of_forall_locFrac_eq (OMeara.volume_fg _ L.2.fg) (OMeara.volume_fg _ K.2.fg)
  intro v
  rw [← volume_loc v Q L.2, ← volume_loc v Q K.2]
  obtain ⟨g, hg, he⟩ := hLK v
  have hσ : glEquiv (v.adicCompletion F) g ∈ OMeara.orth (qk Q (v.adicCompletion F)) := by
    rw [← map_orthGroup Q (v.adicCompletion F)]
    exact ⟨g, hg, rfl⟩
  rw [qk_eq_toQuadraticForm_map] at hσ
  rw [← he, locAct_eq_latMap, OMeara.volume_latMap _ hσ]

end QuadFormsKB.Lattices
