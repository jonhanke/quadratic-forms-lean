/-
# Norms and maximal lattices at the completions

**Layer:** $V = F^n$ over a number field $F$, `Q : QuadForm F n`, lattices on $F^n$; at a finite spot $\mathfrak p$ =
`v` the local form `Qv` = `QuadForm.toQuadraticForm (Q.map (algebraMap F F_𝔭))`, the completion `loc v L` and the
completion `locFrac v 𝔞` of a fractional ideal (`Sec104LocalMod.lean`).

**Proves** (O'Meara 1973, §82K and §91A, at the completion)
* `normIdeal_loc`: $\mathfrak nL_\mathfrak p = (\mathfrak nL)_\mathfrak p$;
* `mem_of_forall_locFrac`, `le_of_forall_locFrac_le`: membership in and inclusion of fractional ideals are local;
* `isMaximal_loc_locFrac`: if $L$ is $\mathfrak a$-maximal then $L_\mathfrak p$ is $\mathfrak a_\mathfrak p$-maximal;
* `isMaximal_of_forall_loc`: if every $L_\mathfrak p$ is $\mathfrak a_\mathfrak p$-maximal then $L$ is
  $\mathfrak a$-maximal (maximality is a local property);
* `IsMaximal.latMap'`: an isometry carries $\mathfrak a$-maximal lattices to $\mathfrak a$-maximal lattices.
-/
import QuadFormsKB.Literature.OMeara.Sec102Volume
import QuadFormsKB.Literature.OMeara.Sec91MaxA

open NumberField IsDedekindDomain Matrix Submodule

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

section Ideals

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem algebraMap_mem_locFrac {a : Submodule (𝓞 F) F} {x : F} (hx : x ∈ a) : algebraMap F Fv x ∈ locFrac v a :=
  subset_span ⟨x, hx, rfl⟩

theorem locFrac_mono {a b : Submodule (𝓞 F) F} (h : a ≤ b) : locFrac v a ≤ locFrac v b :=
  span_mono (Set.image_mono h)

variable {v}

/-- **Membership in a fractional ideal is local** (O'Meara 1973, §81E, p. 217): for a non-zero finitely generated
$\mathcal O_F$-submodule $\mathfrak a \subseteq F$, $x \in \mathfrak a$ as soon as $x \in \mathfrak a_\mathfrak p$ at every
finite spot. -/
theorem mem_of_forall_locFrac {a : Submodule (𝓞 F) F} (ha : a.FG) (ha0 : a ≠ ⊥) {x : F}
    (h : ∀ w : HeightOneSpectrum (𝓞 F), algebraMap F (w.adicCompletion F) x ∈ locFrac w a) : x ∈ a := by
  have hlat := isLattice_map_lineEmb ha ha0
  have : lineEmb x ∈ a.map (lineEmb (F := F)) := by
    rw [mem_iff_forall_loc hlat]
    intro w
    rw [loc_map_lineEmb]
    refine ⟨_, h w, ?_⟩
    funext i
    simp [locVec_apply, lineEmb_apply]
  obtain ⟨y, hy, hxy⟩ := this
  rwa [← lineEmb_injective hxy]

/-- **Inclusion of fractional ideals is local.** -/
theorem le_of_forall_locFrac_le {a b : Submodule (𝓞 F) F} (hb : b.FG) (hb0 : b ≠ ⊥)
    (h : ∀ w : HeightOneSpectrum (𝓞 F), locFrac w a ≤ locFrac w b) : a ≤ b := fun _ hx =>
  mem_of_forall_locFrac hb hb0 fun w => h w (algebraMap_mem_locFrac w hx)

end Ideals

variable (Q : QuadForm F n) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "Qv" => QuadForm.toQuadraticForm (QuadForm.map (algebraMap F (v.adicCompletion F)) Q)

/-- $2\,\mathfrak s_\mathfrak p \subseteq \mathfrak n_\mathfrak p$ for the completed ideals of a lattice:
if $c \in (\mathfrak sL)_\mathfrak p$ then $2c \in (\mathfrak nL)_\mathfrak p$. -/
theorem two_mul_mem_locFrac_normIdeal {L : Submodule (𝓞 F) (Fin n → F)} {c : Fv}
    (hc : c ∈ locFrac v (OMeara.scale Q.toQuadraticForm L)) :
    2 * c ∈ locFrac v (OMeara.normIdeal Q.toQuadraticForm L) := by
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    have := algebraMap_mem_locFrac v (OMeara.two_mul_mem_normIdeal Q.toQuadraticForm hy)
    rwa [map_mul, map_ofNat] at this
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [Algebra.smul_def, mul_left_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ r hx

/-- **$\mathfrak nL_\mathfrak p = (\mathfrak nL)_\mathfrak p$** (O'Meara 1973, §82K, p. 238, at the completion): the norm of
the completion of an $\mathcal O_F$-submodule $L \subseteq F^n$ is the completion of its norm. -/
@[kb "omeara1963" "§82K, p. 238 (nL_p = (nL)_p, at the completion)"]
theorem normIdeal_loc (L : Submodule (𝓞 F) (Fin n → F)) :
    OMeara.normIdeal Qv (loc v L) = locFrac v (OMeara.normIdeal Q.toQuadraticForm L) := by
  apply le_antisymm
  · rw [OMeara.normIdeal, span_le]
    rintro _ ⟨y, hy, rfl⟩
    change y ∈ span 𝔬 _ at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      rw [SetLike.mem_coe, locForm_locVec]
      exact algebraMap_mem_locFrac v (OMeara.Q_mem_normIdeal _ hx)
    | zero => simp
    | add x y hx hy ihx ihy =>
      rw [SetLike.mem_coe, OMeara.Q_add]
      refine add_mem (add_mem ihx ?_) ihy
      apply two_mul_mem_locFrac_normIdeal
      rw [← scale_loc]
      exact OMeara.bil_mem_scale _ hx hy
    | smul r x _ ih =>
      rw [SetLike.mem_coe, ← algebraMap_smul Fv r x, QuadraticMap.map_smul, smul_eq_mul, ← map_mul,
        ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ ih
  · rw [OMeara.normIdeal, locFrac_span, span_le]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [← locForm_locVec]
    exact OMeara.Q_mem_normIdeal _ (locVec_mem_loc v hx)

/-- **An $\mathfrak a$-maximal lattice is $\mathfrak a_\mathfrak p$-maximal at every completion** (O'Meara 1973, §82K,
p. 239, and §91A): for a non-zero finitely generated $\mathcal O_F$-submodule $\mathfrak a \subseteq F$, if the lattice
$L$ on $F^n$ is $\mathfrak a$-maximal for $Q$, then $L_\mathfrak p$ is $\mathfrak a_\mathfrak p$-maximal for
$Q_\mathfrak p$. *Proof:* a lattice $N \supseteq L_\mathfrak p$ with $\mathfrak nN \subseteq \mathfrak a_\mathfrak p$ glues
with the $L_\mathfrak q$, $\mathfrak q \ne \mathfrak p$, to a global lattice $M \supseteq L$ with $\mathfrak nM \subseteq
\mathfrak a$ (the norm condition is local, `mem_of_forall_locFrac`); maximality gives $M = L$, so $N = L_\mathfrak p$. -/
@[kb "omeara1963" "§82K, p. 239 (L a-maximal ⟹ L_p a_p-maximal, at the completion)"]
theorem isMaximal_loc_locFrac {a : Submodule (𝓞 F) F} (ha : a.FG) (ha0 : a ≠ ⊥) {L : Lat F n}
    (hL : OMeara.IsMaximal Q.toQuadraticForm a L.1) : OMeara.IsMaximal Qv (locFrac v a) (loc v L.1) := by
  classical
  obtain ⟨-, hLn, hLmax⟩ := hL
  refine ⟨loc_isLattice v L.2, ?_, ?_⟩
  · rw [normIdeal_loc]; exact locFrac_mono v hLn
  intro N hN hMN hNn
  let Mf : ∀ w : HeightOneSpectrum (𝓞 F), Submodule (w.adicCompletionIntegers F) (Fin n → w.adicCompletion F) :=
    fun w => if h : w = v then h ▸ N else loc w L.1
  have hMf_v : Mf v = N := by simp [Mf]
  have hMf_ne : ∀ w, w ≠ v → Mf w = loc w L.1 := fun w hw => by simp [Mf, hw]
  let fam : LocFamily F n :=
    { M := Mf
      isLattice := fun w => by
        rcases eq_or_ne w v with rfl | hw
        · rw [hMf_v]; exact hN
        · rw [hMf_ne w hw]; exact loc_isLattice w L.2
      eventually_std := by
        filter_upwards [loc_eventually_std L.2, Filter.eventually_cofinite_ne v] with w h1 h2
        rw [hMf_ne w h2]; exact h1 }
  have hGlat : fam.glue.IsLattice F := fam.glue_isLattice
  have hlocG : ∀ w, loc w fam.glue = Mf w := fun w => fam.loc_glue w
  have hLG : L.1 ≤ fam.glue := by
    refine (le_iff_forall_loc hGlat).mpr fun w => ?_
    rcases eq_or_ne w v with rfl | hw
    · rw [hlocG, hMf_v]; exact hMN
    · rw [hlocG, hMf_ne w hw]
  have hGn : OMeara.normIdeal Q.toQuadraticForm fam.glue ≤ a := by
    rw [OMeara.normIdeal, span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine mem_of_forall_locFrac ha ha0 fun w => ?_
    have hxw : locVec w x ∈ Mf w := fam.mem_glue.mp hx w
    rw [← locForm_locVec]
    rcases eq_or_ne w v with rfl | hw
    · rw [hMf_v] at hxw
      exact hNn (OMeara.Q_mem_normIdeal _ hxw)
    · rw [hMf_ne w hw] at hxw
      have h1 := OMeara.Q_mem_normIdeal (QuadForm.toQuadraticForm (Q.map (algebraMap F (w.adicCompletion F)))) hxw
      rw [normIdeal_loc] at h1
      exact locFrac_mono w hLn h1
  have hEq : fam.glue = L.1 := hLmax _ hGlat hLG hGn
  have := hlocG v
  rw [hEq, hMf_v] at this
  exact this.symm

/-- **Maximality is local** (O'Meara 1973, §82K, p. 239, at the completion): if $L$ is a lattice on $F^n$ and every
completion $L_\mathfrak p$ is $\mathfrak a_\mathfrak p$-maximal for $Q_\mathfrak p$, where $\mathfrak a$ is a non-zero
finitely generated $\mathcal O_F$-submodule of $F$, then $L$ is $\mathfrak a$-maximal for $Q$. -/
@[kb "omeara1963" "§82K, p. 239 (L is a-maximal iff every L_p is a_p-maximal, at the completion)"]
theorem isMaximal_of_forall_loc {a : Submodule (𝓞 F) F} (ha : a.FG) (ha0 : a ≠ ⊥) {L : Lat F n}
    (h : ∀ w : HeightOneSpectrum (𝓞 F),
      OMeara.IsMaximal (QuadForm.toQuadraticForm (Q.map (algebraMap F (w.adicCompletion F)))) (locFrac w a)
        (loc w L.1)) :
    OMeara.IsMaximal Q.toQuadraticForm a L.1 := by
  have hn : OMeara.normIdeal Q.toQuadraticForm L.1 ≤ a :=
    le_of_forall_locFrac_le ha ha0 fun w => by rw [← normIdeal_loc]; exact (h w).2.1
  refine ⟨L.2, hn, fun K hK hLK hKn => ?_⟩
  apply loc_injective hK L.2
  intro w
  refine (h w).2.2 _ (loc_isLattice w hK) (loc_mono w hLK) ?_
  rw [normIdeal_loc]; exact locFrac_mono w hKn

end QuadFormsKB.Lattices

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **An isometry carries $\mathfrak a$-maximal lattices to $\mathfrak a$-maximal lattices** (O'Meara 1973, §82H,
p. 234): if $L$ is $\mathfrak a$-maximal on $V$ and $\sigma \in O(V)$ then $\sigma L$ is $\mathfrak a$-maximal. -/
theorem IsMaximal.latMap' {a : Submodule R F} {L : Submodule R V} (hL : IsMaximal Q a L) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ orth Q) : IsMaximal Q a (latMap σ L) := by
  have h := ((isMaxIn_top_iff Q).mpr hL).latMap Q hσ (by simp)
  exact (isMaxIn_top_iff Q).mp h

end QuadFormsKB.OMeara
