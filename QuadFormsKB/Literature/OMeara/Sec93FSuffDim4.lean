/-
# O'Meara 93:28, sufficiency, step 2: reduction of the good situation to dimension $4$

**Setting** (as in `Sec93FSuffGood.lean`): $R$ a Henselian discrete valuation ring with finite residue field and
fraction field $F$ of characteristic $0$, $2$ not a unit of $R$, $(V, Q)$ a regular quadratic space, lattices
`Submodule R V`; indices are $0$-based.

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 2, p. 272: "By Example 93:18 we know that each $L_i$
(or $K_i$) is of the form $\langle\xi A(0,0)\rangle \perp \cdots \perp \langle\xi A(0,0)\rangle \perp L_i'$ with
$\dim L_i' = 4$. By making suitable cancellations to the $L_i$ and $K_i$ we see that we can assume that
$\dim L_i = \dim K_i = 4$")
* `GoodSuff4`: the sufficiency for good lattices all of whose components have rank $4$;
* `goodSuff_of_goodSuff4`: `GoodSuff4` implies `GoodSuff`, by induction on the total excess rank $\sum_k
  (\operatorname{rank} L_k - 4)$. Each step (`step_plane`) splits a hyperbolic plane $P = \mathfrak ox + \mathfrak oy$ off
  a component of rank $\ge 5$ of $L$ (`exists_plane_split`, from 93:18 (v) after scaling) and off the same component of
  $K$, moves the plane of $K$ onto that of $L$ by Witt's theorem (`exists_orth_plane`), and passes to $(FP)^\perp$
  with the new Jordan splittings, which have the same fundamental invariants and still satisfy conditions
  (i)–(iii) (`sameFund_repl`, `cond93_repl`), are saturated (`isSaturated_repl`) and still hyperbolic
  (`hyp_descent`);
* the supporting lemmas: a totally isotropic subspace has at most half the dimension
  (`two_finrank_le_of_isotropic`, `two_finrank_le_rank`), the orthogonal complement of a hyperbolic pair in a hyperbolic
  space is hyperbolic (`exists_isotropic_perp_pair`).
-/
import QuadFormsKB.Literature.OMeara.Sec93FSuffMain
import QuadFormsKB.Literature.OMeara.Sec93D18Five
import QuadFormsKB.Literature.OMeara.Sec93FSuffResplit

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Dim4

section Abstract

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {U : Type*} [AddCommGroup U] [Module F U] [FiniteDimensional F U]

/-- A totally isotropic subspace of a nonsingular quadratic space has at most half its dimension. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem two_finrank_le_of_isotropic (Q : QuadraticForm F U) (hQ : (polarBilin Q).Nondegenerate)
    (T : Submodule F U) (hT : ∀ x ∈ T, Q x = 0) : 2 * finrank F T ≤ finrank F U := by
  set B := polarBilin Q with hB
  have hrefl : B.IsRefl := fun x y h => by
    have : polar Q x y = 0 := h
    show polar Q y x = 0
    rw [QuadraticMap.polar_comm]; exact this
  have hle : T ≤ LinearMap.BilinForm.orthogonal B T := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    show polar Q y x = 0
    rw [QuadraticMap.polar, hT (y + x) (add_mem hy hx), hT y hy, hT x hx]; simp
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal hQ T
  have h3 : finrank F T ≤ finrank F U := Submodule.finrank_le T
  omega

/-- **Passing to the complement of a hyperbolic pair** (Witt): if $x, y$ are isotropic with $B(x,y) \ne 0$ in a
nonsingular space and $T$ is totally isotropic, there is a totally isotropic $T'$ orthogonal to $x$ and $y$ with
$\dim T \le \dim T' + 1$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem exists_isotropic_perp_pair (Q : QuadraticForm F U) (hQ : (polarBilin Q).Nondegenerate) {x y : U}
    (hx : Q x = 0) (hxy : polar Q x y ≠ 0) (T : Submodule F U) (hT : ∀ z ∈ T, Q z = 0) :
    ∃ T' : Submodule F U, (∀ z ∈ T', Q z = 0) ∧ (∀ z ∈ T', polar Q z x = 0 ∧ polar Q z y = 0) ∧
      finrank F T ≤ finrank F T' + 1 := by
  by_cases hT0 : T = ⊥
  · exact ⟨⊥, fun z hz => by rw [(Submodule.mem_bot F).1 hz]; simp, fun z hz => by
      rw [(Submodule.mem_bot F).1 hz]; simp, by subst hT0; simp⟩
  obtain ⟨t, htT, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT0
  have hx0 : x ≠ 0 := fun h => hxy (by rw [h]; simp)
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_apply_eq_of_isotropic Q (QuadraticForm.radical_eq_bot_of_nondegenerate Q hQ)
    hx0 ht0 hx (hT t htT)
  set y' : U := ρ y with hy'
  let f : U →ₗ[F] F := (polarBilin Q).flip y'
  have hf : ∀ s, f s = polar Q s y' := fun s => rfl
  let g : T →ₗ[F] F := f.domRestrict T
  set T0 : Submodule F U := (LinearMap.ker g).map T.subtype with hT0def
  have hrk : finrank F (LinearMap.range g) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range g)
    simpa using this
  have hfin : finrank F (LinearMap.range g) + finrank F (LinearMap.ker g) = finrank F T :=
    LinearMap.finrank_range_add_finrank_ker g
  have hT0rk : finrank F T0 = finrank F (LinearMap.ker g) := Submodule.finrank_map_subtype_eq _ _
  let T' : Submodule F U := T0.map ρ.symm.toLinearEquiv.toLinearMap
  have hT'rk : finrank F T' = finrank F T0 :=
    LinearEquiv.finrank_map_eq ρ.symm.toLinearEquiv T0
  have hw : ∀ w ∈ T0, w ∈ T ∧ polar Q w y' = 0 := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨s.2, ?_⟩
    have := LinearMap.mem_ker.1 hs
    simpa [g, hf] using this
  have hxt : ρ.symm t = x := by rw [← hρ]; exact ρ.symm_apply_apply x
  have hyy : ρ.symm y' = y := ρ.symm_apply_apply y
  have hmem : ∀ z ∈ T', ∃ w ∈ T0, ρ.symm w = z := by
    rintro _ ⟨w, hw0, rfl⟩; exact ⟨w, hw0, rfl⟩
  refine ⟨T', ?_, ?_, by omega⟩
  · intro z hz
    obtain ⟨w, hw0, rfl⟩ := hmem z hz
    rw [ρ.symm.map_app]; exact hT w (hw w hw0).1
  · intro z hz
    obtain ⟨w, hw0, rfl⟩ := hmem z hz
    refine ⟨?_, ?_⟩
    · rw [← hxt, ρ.symm.polar_map]
      have hwT := (hw w hw0).1
      rw [QuadraticMap.polar, hT (w + t) (add_mem hwT htT), hT w hwT, hT t htT]; simp
    · rw [← hyy, ρ.symm.polar_map]; exact (hw w hw0).2

end Abstract

section Remove

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- If $z$ is orthogonal to every $X_k$ then $z$ is orthogonal to $\bigvee_k X_k$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem orth_iSup {ι : Type*} {Xs : ι → Submodule R V} {z : V} (h : ∀ k, ∀ y ∈ Xs k, bil Q y z = 0) {x : V}
    (hx : x ∈ ⨆ k, Xs k) : bil Q x z = 0 := by
  refine Submodule.iSup_induction _ (motive := fun x => bil Q x z = 0) hx (fun j y hy => h j y hy) (by simp [bil])
    (fun x y hx hy => by rw [bil_add_left, hx, hy, add_zero])

/-- The splitting with the component `k0` replaced by `L'`. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
def repl {t : ℕ} (Ls : Fin t → Submodule R V) (k0 : Fin t) (L' : Submodule R V) : Fin t → Submodule R V :=
  Function.update Ls k0 L'

/-- The replaced splitting agrees with the original one away from `k0`. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem repl_of_ne {t : ℕ} (Ls : Fin t → Submodule R V) {k0 k : Fin t} (L' : Submodule R V) (h : k ≠ k0) :
    repl Ls k0 L' k = Ls k := Function.update_of_ne h _ _

/-- The replaced splitting has the component $L'$ at `k0`. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem repl_self {t : ℕ} (Ls : Fin t → Submodule R V) (k0 : Fin t) (L' : Submodule R V) :
    repl Ls k0 L' k0 = L' := Function.update_self _ _ _

/-- Every component of the replaced splitting lies in the corresponding component of the original one. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem repl_le {t : ℕ} {Ls : Fin t → Submodule R V} {k0 : Fin t} {P L' : Submodule R V}
    (hPL : IsOrthSum Q (Ls k0) P L') (k : Fin t) : repl Ls k0 L' k ≤ Ls k := by
  by_cases h : k = k0
  · subst h; rw [repl_self, ← hPL.sup_eq]; exact le_sup_right
  · rw [repl_of_ne Ls L' h]

/-- Removing a summand from one component of an orthogonal splitting is still an orthogonal splitting. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem isOrthSplit_repl {t : ℕ} {L : Submodule R V} {Ls : Fin t → Submodule R V} (hL : IsOrthSplit Q L Ls)
    {k0 : Fin t} {P L' : Submodule R V} (hPL : IsOrthSum Q (Ls k0) P L') :
    IsOrthSplit Q (⨆ k, repl Ls k0 L' k) (repl Ls k0 L') where
  orth i j hij x hx y hy := hL.orth i j hij x (repl_le Q hPL i hx) y (repl_le Q hPL j hy)
  indep := hL.indep.mono (fun k => repl_le Q hPL k)
  iSup_eq := rfl

/-- $L = P \perp L^*$ where $L^*$ is the lattice with the component `k0` replaced by $L'$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem isOrthSum_plane {t : ℕ} {L : Submodule R V} {Ls : Fin t → Submodule R V} (hL : IsOrthSplit Q L Ls)
    {k0 : Fin t} {P L' : Submodule R V} (hPL : IsOrthSum Q (Ls k0) P L') (hPreg : IsRegular Q P) :
    IsOrthSum Q L P (⨆ k, repl Ls k0 L' k) := by
  have hPk : P ≤ Ls k0 := hPL.sup_eq ▸ le_sup_left
  have horth : ∀ z ∈ P, ∀ x ∈ ⨆ k, repl Ls k0 L' k, bil Q x z = 0 := by
    intro z hz x hx
    refine orth_iSup Q (fun k y hy => ?_) hx
    by_cases h : k = k0
    · subst h; rw [repl_self] at hy; rw [bil_comm]; exact hPL.orth z hz y hy
    · rw [repl_of_ne Ls L' h] at hy; exact hL.orth k k0 h y hy z (hPk hz)
  refine ⟨fun x hx y hy => by rw [bil_comm]; exact horth x hx y hy, ?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    exact (mem_bot R).mpr (hPreg x hx1 fun y hy => horth y hy x hx2)
  · apply le_antisymm
    · refine sup_le ?_ (iSup_le fun k => (repl_le Q hPL k).trans (hL.iSup_eq ▸ le_iSup Ls k))
      exact hPk.trans (hL.iSup_eq ▸ le_iSup Ls k0)
    · rw [← hL.iSup_eq]
      refine iSup_le fun k => ?_
      by_cases h : k = k0
      · rw [h]
        refine (le_of_eq hPL.sup_eq.symm).trans (sup_le_sup_left ?_ _)
        have := le_iSup (repl Ls k0 L') k0
        rwa [repl_self] at this
      · refine le_sup_of_le_right ?_
        have := le_iSup (repl Ls k0 L') k
        rwa [repl_of_ne Ls L' h] at this

end Remove

section Plane

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- $P = \mathfrak o x + \mathfrak o y$ is a *hyperbolic plane of scale $\mathfrak s$*: $Q(x) = Q(y) = 0$ and
$B(x, y) \ne 0$ generates $\mathfrak s$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
def IsPlane (P : Submodule R V) (s : Submodule R F) : Prop :=
  ∃ x y : V, Q x = 0 ∧ Q y = 0 ∧ P = span R {x, y} ∧ R ∙ bil Q x y = s ∧ bil Q x y ≠ 0

variable {Q}

/-- The span of $x, y$ with $Q(x) = Q(y) = 0$ and $B(x,y) = \alpha \ne 0$ is a hyperbolic plane of scale $\mathfrak o\alpha$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem isPlane_span {x y : V} {α : F} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = α) (hα : α ≠ 0) :
    IsPlane Q (span R {x, y}) (R ∙ α) := ⟨x, y, hx, hy, rfl, by rw [hxy], by rw [hxy]; exact hα⟩

/-- A hyperbolic plane is finitely generated. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem IsPlane.fg {P : Submodule R V} {s : Submodule R F} (h : IsPlane Q P s) : P.FG := by
  obtain ⟨x, y, -, -, rfl, -, -⟩ := h
  exact Submodule.fg_span (Set.toFinite _)

/-- A hyperbolic plane is regular: $B(x,y) \ne 0$ makes the matrix $\begin{pmatrix}0&\alpha\\ \alpha&0\end{pmatrix}$ invertible. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem IsPlane.regular {P : Submodule R V} {s : Submodule R F} (h : IsPlane Q P s) : IsRegular Q P := by
  obtain ⟨x, y, hx, hy, rfl, -, hne⟩ := h
  intro p hp h0
  obtain ⟨r, u, rfl⟩ := Submodule.mem_span_pair.mp hp
  have h1 := h0 x (Submodule.subset_span (by simp))
  have h2 := h0 y (Submodule.subset_span (by simp))
  simp only [bil_add_left, bil_rsmul_left, bil_self, hx, hy, mul_zero, zero_add, add_zero] at h1 h2
  have hxy : bil Q y x = bil Q x y := bil_comm Q y x
  rw [hxy] at h1
  have hr : r = 0 := by
    have := (mul_eq_zero.1 h2).resolve_right hne
    exact (map_eq_zero_iff _ (IsFractionRing.injective R F)).1 this
  have hu : u = 0 := by
    have := (mul_eq_zero.1 h1).resolve_right hne
    exact (map_eq_zero_iff _ (IsFractionRing.injective R F)).1 this
  rw [hr, hu]; simp

/-- The norm group of $P^{\mathfrak a}$ for a hyperbolic plane lies in $2\mathfrak a$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem IsPlane.normGroup_subA_le {P : Submodule R V} {s : Submodule R F} (h : IsPlane Q P s)
    (a : Submodule R F) : ∀ z ∈ normGroup Q (subA Q a P), z ∈ (2 : F) • a := by
  obtain ⟨x, y, hx, hy, rfl, -, -⟩ := h
  rintro _ ⟨p, hp, c, hc, rfl⟩
  have hpa := hp.2
  obtain ⟨r, u, rfl⟩ := Submodule.mem_span_pair.mp hp.1
  have h2 : bil Q (r • x + u • y) y ∈ a := hpa y (Submodule.subset_span (by simp))
  have hca : c ∈ a := scale_subA_le Q a _ hc
  have hbp : bil Q (r • x + u • y) y = algebraMap R F r * bil Q x y := by
    have hyy : bil Q y y = 0 := by rw [bil_self, hy]
    have hxx : bil Q x x = 0 := by rw [bil_self, hx]
    simp only [bil_add_left, bil_rsmul_left, hyy]; ring
  have hQp : Q (r • x + u • y) = 2 * algebraMap R F r * algebraMap R F u * bil Q x y := by
    have hxx : bil Q x x = 0 := by rw [bil_self, hx]
    have hyy : bil Q y y = 0 := by rw [bil_self, hy]
    refine (bil_self Q (r • x + u • y)).symm.trans ?_
    simp only [bil_add_left, bil_add_right, bil_rsmul_left, bil_rsmul_right, hxx, hyy, bil_comm Q y x]
    ring
  refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨u • bil Q (r • x + u • y) y + c, ?_, ?_⟩
  · exact add_mem (a.smul_mem u h2) hca
  · rw [hQp, hbp, smul_eq_mul, Algebra.smul_def]; ring

/-- A hyperbolic plane has rank $2$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem IsPlane.finrank_eq {P : Submodule R V} {s : Submodule R F} (h : IsPlane Q P s) : finrank R P = 2 := by
  obtain ⟨x, y, hx, hy, rfl, -, hne⟩ := h
  have hxx : bil Q x x = 0 := by rw [bil_self, hx]
  have hyy : bil Q y y = 0 := by rw [bil_self, hy]
  have hdet : (gram Q ![x, y]).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [gram, hxx, hyy, bil_comm Q y x, hne]
  have hli : LinearIndependent R ![x, y] := linearIndependent_of_det_gram_ne_zero (R := R) Q hdet
  have hrange : (Set.range ![x, y] : Set V) = {x, y} := by
    ext z; simp [eq_comm, or_comm]
  have := finrank_span_eq_card hli
  rw [hrange] at this
  simpa using this

end Plane

section Fund

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- Replacing a modular component by a modular summand of the same scale does not change the scales. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem scale_repl_eq {t : ℕ} {Ls : Fin t → Submodule R V} {k0 : Fin t} {L' : Submodule R V}
    (hL'mod : IsModular Q (scale Q (Ls k0)) L') (k : Fin t) : scale Q (repl Ls k0 L' k) = scale Q (Ls k) := by
  by_cases h : k = k0
  · subst h; rw [repl_self]; exact hL'mod.2.1
  · rw [repl_of_ne Ls L' h]

/-- Replacing the component `k0` of a Jordan splitting by a modular summand $L'$ of the same scale gives a Jordan splitting of $L^*$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem isJordanSplitting_repl {t : ℕ} {L : Submodule R V} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) {k0 : Fin t} {P L' : Submodule R V} (hPL : IsOrthSum Q (Ls k0) P L')
    (hL'mod : IsModular Q (scale Q (Ls k0)) L') :
    IsJordanSplitting Q (⨆ k, repl Ls k0 L' k) (repl Ls k0 L') := by
  have hsc := scale_repl_eq Q hL'mod
  refine ⟨isOrthSplit_repl Q hL.split hPL, fun k => ?_, ?_⟩
  · rw [hsc k]
    by_cases h : k = k0
    · subst h; rw [repl_self]; exact hL'mod
    · rw [repl_of_ne Ls L' h]; exact hL.modular k
  · have : (fun k => scale Q (repl Ls k0 L' k)) = fun k => scale Q (Ls k) := funext hsc
    rw [this]; exact hL.scale_strictAnti

/-- **The fundamental norm groups do not change when a hyperbolic plane is removed** (O'Meara 1963, p. 272, "by making
suitable cancellations"): $\mathfrak g((L^*)^{\mathfrak s_k}) = \mathfrak g(L^{\mathfrak s_k})$ for $L = P \perp L^*$
because $\mathfrak g(P^{\mathfrak s_k}) \subseteq 2\mathfrak s_k \subseteq \mathfrak g(L_k^*)$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem fundNormGroup_repl {t : ℕ} {L P L' : Submodule R V} {Ls : Fin t → Submodule R V} {k0 : Fin t}
    {s0 : Submodule R F} (hLfg : L.FG) (hL : IsJordanSplitting Q L Ls) (hPL : IsOrthSum Q (Ls k0) P L')
    (hP : IsPlane Q P s0) (hL'mod : IsModular Q (scale Q (Ls k0)) L') (k : Fin t) :
    fundNormGroup Q (⨆ j, repl Ls k0 L' j) (repl Ls k0 L') k = fundNormGroup Q L Ls k := by
  have hsum := isOrthSum_plane Q hL.split hPL hP.regular
  have hJ := isJordanSplitting_repl Q hL hPL hL'mod
  have hLsfg : (⨆ j, repl Ls k0 L' j).FG := FG.of_le hLfg (hsum.sup_eq ▸ le_sup_right)
  have hsc := scale_repl_eq Q hL'mod k
  have hle : repl Ls k0 L' k ≤ subA Q (scale Q (Ls k)) (⨆ j, repl Ls k0 L' j) := by
    have := le_fundSub Q hLsfg hJ k
    simpa only [fundSub, hsc] using this
  unfold fundNormGroup fundSub
  rw [hsc]
  conv_rhs => rw [← hsum.sup_eq]
  rw [NecMerge.normGroup_subA_sup Q hsum.orth]
  symm
  refine sup_eq_right.mpr fun z hz => ?_
  obtain ⟨c, hc, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (hP.normGroup_subA_le _ z hz)
  have : (2 : F) * c ∈ normGroup Q (repl Ls k0 L' k) := two_mul_mem_normGroup Q (hsc ▸ hc)
  exact normGroup_mono Q hle (by simpa using this)

end Fund

section Cond

open Suff28

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- $\mathfrak g(P \perp L') = \mathfrak g(L')$ for a hyperbolic plane $P$ and $L'$ of the same scale, since $\mathfrak gP \subseteq 2\mathfrak s \subseteq \mathfrak gL'$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem normGroup_split_plane {M P L' : Submodule R V} {s0 : Submodule R F} (hPL : IsOrthSum Q M P L')
    (hP : IsPlane Q P s0) (hL'mod : IsModular Q (scale Q M) L') : normGroup Q M = normGroup Q L' := by
  have hPa : subA Q (scale Q M) P = P :=
    NecMerge.subA_eq_self Q (scale_mono Q (hPL.sup_eq ▸ le_sup_left))
  rw [← hPL.sup_eq, normGroup_sup_of_orth Q hPL.orth]
  refine sup_eq_right.mpr fun z hz => ?_
  rw [← hPa] at hz
  obtain ⟨c, hc, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (hP.normGroup_subA_le _ z hz)
  have : (2 : F) * c ∈ normGroup Q L' := two_mul_mem_normGroup Q (hL'mod.2.1 ▸ hc)
  simpa using this

/-- A saturated splitting stays saturated after removing a hyperbolic plane from one component. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem isSaturated_repl {t : ℕ} {L P L' : Submodule R V} {Ls : Fin t → Submodule R V} {k0 : Fin t}
    {s0 : Submodule R F} (hLfg : L.FG) (hL : IsSaturated Q L Ls) (hPL : IsOrthSum Q (Ls k0) P L')
    (hP : IsPlane Q P s0) (hL'mod : IsModular Q (scale Q (Ls k0)) L') :
    IsSaturated Q (⨆ j, repl Ls k0 L' j) (repl Ls k0 L') := by
  refine ⟨isJordanSplitting_repl Q hL.1 hPL hL'mod, fun k => ?_⟩
  rw [fundNormGroup_repl Q hLfg hL.1 hPL hP hL'mod k, ← hL.2 k]
  by_cases h : k = k0
  · subst h; rw [repl_self]; exact (normGroup_split_plane Q hPL hP hL'mod).symm
  · rw [repl_of_ne Ls L' h]

/-- $\operatorname{rank}(J \perp K) = \operatorname{rank} J + \operatorname{rank} K$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem finrank_isOrthSum {M P N : Submodule R V} (h : IsOrthSum Q M P N) :
    finrank R M = finrank R P + finrank R N := by
  rw [← h.sup_eq]; exact finrank_sup_of_disjoint' (F := F) h.disjoint

section Henselian

variable [HenselianLocalRing R] [Finite (ResidueField R)]

/-- **Same fundamental invariants after removing the common plane** $P$ from the components `k0` of $L$ and $K$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem sameFund_repl {t : ℕ} {L K P L' K' : Submodule R V} {Ls Ks : Fin t → Submodule R V} {k0 : Fin t}
    {s0 : Submodule R F} {a : Fin t → F} (hLfg : L.FG) (hKfg : K.FG) (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q K Ks) (hPL : IsOrthSum Q (Ls k0) P L') (hPK : IsOrthSum Q (Ks k0) P K')
    (hP : IsPlane Q P s0) (hL'mod : IsModular Q (scale Q (Ls k0)) L')
    (hK'mod : IsModular Q (scale Q (Ks k0)) K') (hS : SameFundamentalInvariants Q Q L K Ls Ks a) :
    SameFundamentalInvariants Q Q (⨆ j, repl Ls k0 L' j) (⨆ j, repl Ks k0 K' j) (repl Ls k0 L')
      (repl Ks k0 K') a := by
  obtain ⟨⟨h0, hT⟩, haL, haK⟩ := hS
  have hc : ∀ k : Fin t, Fin.cast h0 k = k := fun k => Fin.ext rfl
  have hsc : scale Q (Ls k0) = scale Q (Ks k0) := by have := (hT k0).2.1; rwa [hc] at this
  refine ⟨⟨rfl, fun k => ⟨?_, ?_, ?_⟩⟩, fun k => ?_, fun k => ?_⟩
  · rw [show Fin.cast rfl k = k from Fin.ext rfl]
    by_cases h : k = k0
    · subst h
      rw [repl_self, repl_self]
      have e1 := finrank_isOrthSum Q hPL
      have e2 := finrank_isOrthSum Q hPK
      have := (hT k).1; rw [hc] at this
      omega
    · rw [repl_of_ne Ls L' h, repl_of_ne Ks K' h]; have := (hT k).1; rwa [hc] at this
  · rw [show Fin.cast rfl k = k from Fin.ext rfl]
    rw [scale_repl_eq Q hL'mod, scale_repl_eq Q hK'mod]; have := (hT k).2.1; rwa [hc] at this
  · rw [show Fin.cast rfl k = k from Fin.ext rfl]
    rw [fundNormGroup_repl Q hLfg hL hPL hP hL'mod, fundNormGroup_repl Q hKfg hK hPK hP hK'mod]
    have := (hT k).2.2; rwa [hc] at this
  · exact isNormGenerator_fundSub_of_eq Q Q (fundNormGroup_repl Q hLfg hL hPL hP hL'mod k) (haL k)
  · exact isNormGenerator_fundSub_of_eq Q Q (fundNormGroup_repl Q hKfg hK hPK hP hK'mod k) (haK k)

/-- Symmetry of $L = J \perp K$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem isOrthSum_symm {M J K : Submodule R V} (h : IsOrthSum Q M J K) : IsOrthSum Q M K J :=
  ⟨fun x hx y hy => by rw [bil_comm]; exact h.orth y hy x hx, h.disjoint.symm, by rw [sup_comm]; exact h.sup_eq⟩

/-- The lattice $L^*$ with the plane removed is finitely generated. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem fg_repl {t : ℕ} {L P L' : Submodule R V} {Ls : Fin t → Submodule R V} {k0 : Fin t}
    {s0 : Submodule R F} (hLfg : L.FG) (hL : IsJordanSplitting Q L Ls) (hPL : IsOrthSum Q (Ls k0) P L')
    (hP : IsPlane Q P s0) : (⨆ j, repl Ls k0 L' j).FG :=
  FG.of_le hLfg ((isOrthSum_plane Q hL.split hPL hP.regular).sup_eq ▸ le_sup_right)

/-- The ideals $\mathfrak f_{ij}$ do not change when a hyperbolic plane is removed. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem fIdeal_repl {t : ℕ} {L P L' : Submodule R V} {Ls : Fin t → Submodule R V} {k0 : Fin t}
    {s0 : Submodule R F} (hLfg : L.FG) (hL : IsJordanSplitting Q L Ls) (hPL : IsOrthSum Q (Ls k0) P L')
    (hP : IsPlane Q P s0) (hL'mod : IsModular Q (scale Q (Ls k0)) L') (i j : Fin t) :
    fIdeal Q (⨆ k, repl Ls k0 L' k) (repl Ls k0 L') i j = fIdeal Q L Ls i j := by
  simp only [fIdeal, fIdeal_fundNormIdeal_eq_span, fundNormGroup_repl Q hLfg hL hPL hP hL'mod,
    scale_repl_eq Q hL'mod]

/-- The fundamental weights do not change when a hyperbolic plane is removed. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem fundWeight_repl {t : ℕ} {L P L' : Submodule R V} {Ls : Fin t → Submodule R V} {k0 : Fin t}
    {s0 : Submodule R F} (hLfg : L.FG) (hL : IsJordanSplitting Q L Ls) (hPL : IsOrthSum Q (Ls k0) P L')
    (hP : IsPlane Q P s0) (hL'mod : IsModular Q (scale Q (Ls k0)) L') (k : Fin t) :
    fundWeight Q (⨆ j, repl Ls k0 L' j) (repl Ls k0 L') k = fundWeight Q L Ls k := by
  have hJ := isJordanSplitting_repl Q hL hPL hL'mod
  have hLsfg := fg_repl Q hLfg hL hPL hP
  unfold fundWeight
  refine weight_congr Q Q (fundNormGroup_repl Q hLfg hL hPL hP hL'mod k) ?_
  rw [scale_fundSub Q hLsfg hJ k, scale_fundSub Q hLfg hL k, scale_repl_eq Q hL'mod k]

/-- Jordan chains below the index `k0` are unchanged. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem chain_repl_lt {t : ℕ} {Ls : Fin t → Submodule R V} {k0 : Fin t} {L' : Submodule R V} {i : Fin t}
    (h : i < k0) : jordanChain (repl Ls k0 L') i = jordanChain Ls i := by
  unfold jordanChain
  refine iSup_congr fun j => iSup_congr fun hj => ?_
  rw [repl_of_ne Ls L' (ne_of_lt (lt_of_le_of_lt hj h))]

/-- For $i \ge k_0$: $L_{(i)} = P \perp L^*_{(i)}$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem chain_repl_ge {t : ℕ} {L : Submodule R V} {Ls : Fin t → Submodule R V} (hL : IsOrthSplit Q L Ls)
    {k0 : Fin t} {P L' : Submodule R V} (hPL : IsOrthSum Q (Ls k0) P L') (hPreg : IsRegular Q P) {i : Fin t}
    (h : k0 ≤ i) : IsOrthSum Q (jordanChain Ls i) P (jordanChain (repl Ls k0 L') i) := by
  have hPk : P ≤ Ls k0 := hPL.sup_eq ▸ le_sup_left
  have horth : ∀ z ∈ P, ∀ x ∈ jordanChain (repl Ls k0 L') i, bil Q x z = 0 := by
    intro z hz x hx
    refine bil_eq_zero_of_mem_iSup Q (P := fun j => j ≤ i) (fun j _ y hy => ?_) hx
    by_cases hj : j = k0
    · subst hj; rw [repl_self] at hy; rw [bil_comm]; exact hPL.orth z hz y hy
    · rw [repl_of_ne Ls L' hj] at hy; exact hL.orth j k0 hj y hy z (hPk hz)
  refine ⟨fun x hx y hy => by rw [bil_comm]; exact horth x hx y hy, ?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    exact (mem_bot R).mpr (hPreg x hx1 fun y hy => horth y hy x hx2)
  · apply le_antisymm
    · refine sup_le (hPk.trans (le_iSup₂_of_le k0 h le_rfl)) (iSup₂_le fun j hj => ?_)
      exact (repl_le Q hPL j).trans (le_iSup₂_of_le j hj le_rfl)
    · refine iSup₂_le fun j hj => ?_
      by_cases hjk : j = k0
      · subst hjk
        refine (le_of_eq hPL.sup_eq.symm).trans (sup_le_sup_left ?_ _)
        have : repl Ls j L' j ≤ jordanChain (repl Ls j L') i := le_iSup₂_of_le j hj le_rfl
        rwa [repl_self] at this
      · refine le_sup_of_le_right ?_
        have : repl Ls k0 L' j ≤ jordanChain (repl Ls k0 L') i := le_iSup₂_of_le j hj le_rfl
        rwa [repl_of_ne Ls L' hjk] at this

/-- Conditions (i)–(iii) of 93:28 for the chains survive removing the common plane $P$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem chain_transfer {t : ℕ} {L K P L' K' : Submodule R V} {Ls Ks : Fin t → Submodule R V} {k0 : Fin t}
    {s0 : Submodule R F} (hLfg : L.FG) (hKfg : K.FG) (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q K Ks) (hPL : IsOrthSum Q (Ls k0) P L') (hPK : IsOrthSum Q (Ks k0) P K')
    (hP : IsPlane Q P s0) (hL'mod : IsModular Q (scale Q (Ls k0)) L')
    (hK'mod : IsModular Q (scale Q (Ks k0)) K') (i : Fin t) (X : Submodule R F) {c : F} (hc : c ≠ 0) :
    (DiscQuotSqEquivMod Q (jordanChain Ls i) (jordanChain Ks i) X ↔
        DiscQuotSqEquivMod Q (jordanChain (repl Ls k0 L') i) (jordanChain (repl Ks k0 K') i) X) ∧
      (SpanRepresents Q (jordanChain Ls i) (jordanChain Ks i) c ↔
        SpanRepresents Q (jordanChain (repl Ls k0 L') i) (jordanChain (repl Ks k0 K') i) c) := by
  by_cases h : i < k0
  · rw [chain_repl_lt h, chain_repl_lt h]; exact ⟨Iff.rfl, Iff.rfl⟩
  · have h' : k0 ≤ i := not_lt.1 h
    have hM := isOrthSum_symm Q (chain_repl_ge Q hL.split hPL hP.regular h')
    have hN := isOrthSum_symm Q (chain_repl_ge Q hK.split hPK hP.regular h')
    have hJL := isJordanSplitting_repl Q hL hPL hL'mod
    have hJK := isJordanSplitting_repl Q hK hPK hK'mod
    have hLsfg := fg_repl Q hLfg hL hPL hP
    have hKsfg := fg_repl Q hKfg hK hPK hP
    have hMfg : (jordanChain (repl Ls k0 L') i).FG :=
      FG.of_le hLsfg (NecI.jordanChain_le hJL.split i)
    have hNfg : (jordanChain (repl Ks k0 K') i).FG :=
      FG.of_le hKsfg (NecI.jordanChain_le hJK.split i)
    have hMreg := isRegular_jordanChain Q hLsfg hJL i
    have hNreg := isRegular_jordanChain Q hKsfg hJK i
    have hiso : IsometricLat Q Q P P := ⟨LinearEquiv.refl R _, fun x => rfl⟩
    exact ⟨Transfer28.discQuot_isOrthSum_iff Q hM hN hiso hMfg hNfg hP.fg hNreg hP.regular hP.regular,
      RepTransfer.spanRepresents_iff_of_orthSum Q hM hN hMreg hNreg hP.regular hP.fg hiso hc⟩

/-- **Conditions (i)–(iii) for the lattices with the plane removed** (O'Meara 1963, p. 272). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem cond93_repl {t : ℕ} {L K P L' K' : Submodule R V} {Ls Ks : Fin t → Submodule R V} {k0 : Fin t}
    {s0 : Submodule R F} {a : Fin t → F} (hLfg : L.FG) (hKfg : K.FG) (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q K Ks) (hPL : IsOrthSum Q (Ls k0) P L') (hPK : IsOrthSum Q (Ks k0) P K')
    (hP : IsPlane Q P s0) (hL'mod : IsModular Q (scale Q (Ls k0)) L')
    (hK'mod : IsModular Q (scale Q (Ks k0)) K') (ha0 : ∀ k, a k ≠ 0) (hC : Cond93 Q L Ls Ks a) :
    Cond93 Q (⨆ j, repl Ls k0 L' j) (repl Ls k0 L') (repl Ks k0 K') a := by
  intro i j hij
  obtain ⟨h1, h2, h3⟩ := hC i j hij
  rw [fIdeal_repl Q hLfg hL hPL hP hL'mod, fundWeight_repl Q hLfg hL hPL hP hL'mod j,
    fundWeight_repl Q hLfg hL hPL hP hL'mod i]
  exact ⟨(chain_transfer Q hLfg hKfg hL hK hPL hPK hP hL'mod hK'mod i (fIdeal Q L Ls i j) (ha0 j)).1.1 h1,
    fun h => (chain_transfer Q hLfg hKfg hL hK hPL hPK hP hL'mod hK'mod i (fIdeal Q L Ls i j) (ha0 j)).2.1 (h2 h),
    fun h => (chain_transfer Q hLfg hKfg hL hK hPL hPK hP hL'mod hK'mod i (fIdeal Q L Ls i j) (ha0 i)).2.1 (h3 h)⟩

end Henselian

end Cond

section Move

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **Witt: two hyperbolic planes with the same $B(x,y)$ are conjugate** (O'Meara 42:17, p. 98). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem exists_orth_plane (hQ : (QuadraticMap.associated Q).Nondegenerate) {x y x' y' : V} {α : F}
    (hx : Q x = 0) (hy : Q y = 0) (hx' : Q x' = 0) (hy' : Q y' = 0) (hxy : bil Q x y = α)
    (hxy' : bil Q x' y' = α) (hα : α ≠ 0) :
    ∃ σ ∈ orth Q, latMap σ (span R {x', y'}) = (span R {x, y} : Submodule R V) := by
  have hdet : ∀ {u v : V}, Q u = 0 → Q v = 0 → bil Q u v = α → (gram Q ![u, v]).det ≠ 0 := by
    intro u v hu hv huv
    have huu : bil Q u u = 0 := by rw [bil_self, hu]
    have hvv : bil Q v v = 0 := by rw [bil_self, hv]
    rw [Matrix.det_fin_two]
    simp [gram, huu, hvv, bil_comm Q v u, huv, hα]
  have hG : ∀ {u v : V}, Q u = 0 → Q v = 0 → bil Q u v = α → gram Q ![u, v] = Matrix.of ![![0, α], ![α, 0]] := by
    intro u v hu hv huv
    have huu : bil Q u u = 0 := by rw [bil_self, hu]
    have hvv : bil Q v v = 0 := by rw [bil_self, hv]
    ext i j; fin_cases i <;> fin_cases j <;> simp [gram, huu, hvv, bil_comm Q v u, huv]
  have hrange : ∀ u v : V, (Set.range ![u, v] : Set V) = {u, v} := by
    intro u v; ext z; simp [eq_comm, or_comm]
  have hli : LinearIndependent R ![x, y] := linearIndependent_of_det_gram_ne_zero (R := R) Q (hdet hx hy hxy)
  have hli' : LinearIndependent R ![x', y'] := linearIndependent_of_det_gram_ne_zero (R := R) Q (hdet hx' hy' hxy')
  set A : Submodule R V := span R {x', y'} with hA
  set B : Submodule R V := span R {x, y} with hB
  have eA : span R (Set.range ![x', y']) = A := by rw [hrange]
  have eB : span R (Set.range ![x, y]) = B := by rw [hrange]
  let b : Basis (Fin 2) R A := (Basis.span hli').map (LinearEquiv.ofEq _ _ eA)
  let b' : Basis (Fin 2) R B := (Basis.span hli).map (LinearEquiv.ofEq _ _ eB)
  have hb : ∀ i, (b i : V) = ![x', y'] i := fun i => by
    simp [b, Basis.span_apply]
  have hb' : ∀ i, (b' i : V) = ![x, y] i := fun i => by
    simp [b', Basis.span_apply]
  have hiso : IsometricLat Q Q A B := by
    refine isometricLat_of_gram_eq Q Q b b' ?_
    have e1 : (fun i => (b i : V)) = ![x', y'] := funext hb
    have e2 : (fun i => (b' i : V)) = ![x, y] := funext hb'
    rw [e1, e2, hG hx' hy' hxy', hG hx hy hxy]
  have hAfg : A.FG := (isPlane_span (R := R) hx' hy' hxy' hα).fg
  have hAreg : IsRegular Q A := (isPlane_span (R := R) hx' hy' hxy' hα).regular
  exact SuffWitt.exists_orth_latMap_eq Q hQ hAfg hAreg hiso

end Move

section Hyp

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **A hyperbolic space stays hyperbolic after removing a plane** (Witt): if $M = P \perp M'$, $P = \mathfrak ox + \mathfrak oy$
with $Q(x) = Q(y) = 0$, $B(x, y) = \alpha \ne 0$, and $FM$ contains a totally isotropic $T$ with
$\operatorname{rank} M \le 2\dim T$, then $FM'$ contains a totally isotropic $T'$ with $\operatorname{rank} M' \le
2\dim T'$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem hyp_descent {M M' : Submodule R V} {x y : V} {α : F} (hMreg : IsRegular Q M) (hMfg : M.FG)
    (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = α) (hα : α ≠ 0)
    (hOS : IsOrthSum Q M (span R {x, y}) M') (hrank : finrank R M' + 2 = finrank R M)
    (T : Submodule F V) (hT : ∀ z ∈ T, Q z = 0) (hTM : ∀ z ∈ T, z ∈ span F (M : Set V))
    (hrk : finrank R M ≤ 2 * finrank F T) :
    ∃ T' : Submodule F V, (∀ z ∈ T', Q z = 0) ∧ (∀ z ∈ T', z ∈ span F (M' : Set V)) ∧
      finrank R M' ≤ 2 * finrank F T' := by
  classical
  set U : Submodule F V := span F (M : Set V) with hU
  have hxP : x ∈ (span R {x, y} : Submodule R V) := subset_span (by simp)
  have hyP : y ∈ (span R {x, y} : Submodule R V) := subset_span (by simp)
  have hxM : x ∈ M := hOS.sup_eq ▸ mem_sup_left hxP
  have hyM : y ∈ M := hOS.sup_eq ▸ mem_sup_left hyP
  have hxU : x ∈ U := subset_span hxM
  have hyU : y ∈ U := subset_span hyM
  have hnd : (polarBilin (D18.subQ Q M)).Nondegenerate := RepTransfer.nondegenerate_subQ Q hMreg
  let xU : D18.spanF F M := ⟨x, hxU⟩
  let yU : D18.spanF F M := ⟨y, hyU⟩
  have hQx : D18.subQ Q M xU = 0 := hx
  have hpol : polar (D18.subQ Q M) xU yU ≠ 0 := by
    have : polar (D18.subQ Q M) xU yU = polar Q x y := rfl
    rw [this, RepTransfer.polar_eq_two_bil, hxy]; exact mul_ne_zero (two_ne_zero' F) hα
  let TU : Submodule F (D18.spanF F M) := T.comap (D18.spanF F M).subtype
  have hTU : ∀ z ∈ TU, D18.subQ Q M z = 0 := fun z hz => hT _ hz
  obtain ⟨T', hT'0, hT'perp, hrk'⟩ := exists_isotropic_perp_pair (D18.subQ Q M) hnd hQx hpol TU hTU
  have hfinTU : finrank F TU = finrank F T := by
    have h1 := Submodule.finrank_map_subtype_eq (D18.spanF F M) TU
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr (fun z hz => hTM z hz)] at h1
    exact h1.symm
  have hfinT'' : finrank F (T'.map (D18.spanF F M).subtype) = finrank F T' :=
    Submodule.finrank_map_subtype_eq (D18.spanF F M) T'
  refine ⟨T'.map (D18.spanF F M).subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩; exact hT'0 w hw
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨hwx, hwy⟩ := hT'perp w hw
    have h2 : (2 : F) ≠ 0 := two_ne_zero' F
    have bx : bil Q (w : V) x = 0 := by
      have : polar Q (w : V) x = 0 := hwx
      rw [RepTransfer.polar_eq_two_bil] at this; exact (mul_eq_zero.1 this).resolve_left h2
    have by' : bil Q (w : V) y = 0 := by
      have : polar Q (w : V) y = 0 := hwy
      rw [RepTransfer.polar_eq_two_bil] at this; exact (mul_eq_zero.1 this).resolve_left h2
    have hsup : span F (M : Set V) ≤ span F (span R {x, y} : Set V) ⊔ span F (M' : Set V) := by
      refine span_le.mpr fun v hv => ?_
      rw [← hOS.sup_eq] at hv
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp hv
      exact add_mem (mem_sup_left (subset_span ha)) (mem_sup_right (subset_span hb))
    obtain ⟨p, hp, m, hm, hpm⟩ := mem_sup.mp (hsup w.2)
    have horth : ∀ q ∈ (span R {x, y} : Submodule R V), ∀ m ∈ span F (M' : Set V), bil Q m q = 0 := by
      intro q hq m hm
      refine span_induction (p := fun m _ => bil Q m q = 0) (fun v hv => ?_) (by simp [bil])
        (fun a b _ _ ha hb => by rw [bil_add_left, ha, hb, add_zero])
        (fun c a _ ha => by rw [bil_smul_left, ha, mul_zero]) hm
      rw [bil_comm]; exact hOS.orth q hq v hv
    rw [Submodule.span_span_of_tower R F ({x, y} : Set V)] at hp
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hp
    have hxx : bil Q x x = 0 := by rw [bil_self, hx]
    have hyy : bil Q y y = 0 := by rw [bil_self, hy]
    have mx := horth x hxP m hm
    have my := horth y hyP m hm
    have e1 : bil Q (w : V) x = b * α := by
      rw [← hpm, bil_add_left, mx, bil_add_left, bil_smul_left, bil_smul_left, hxx, bil_comm Q y x, hxy]; ring
    have e2 : bil Q (w : V) y = a * α := by
      rw [← hpm, bil_add_left, my, bil_add_left, bil_smul_left, bil_smul_left, hyy, hxy]; ring
    have hb : b = 0 := (mul_eq_zero.1 (e1.symm.trans bx)).resolve_right hα
    have ha : a = 0 := (mul_eq_zero.1 (e2.symm.trans by')).resolve_right hα
    rw [ha, hb, zero_smul, zero_smul, zero_add, zero_add] at hpm
    show (w : V) ∈ span F (M' : Set V)
    rw [← hpm]; exact hm
  · rw [hfinT'']
    have := hrk
    omega

end Hyp

section Split

open QuadFormsKB.PadicClass

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- An orthogonal sum for the form $cQ$ is one for $Q$ ($c \ne 0$). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem isOrthSum_of_smul {c : F} (hc : c ≠ 0) {M J K : Submodule R V} (h : IsOrthSum (c • Q) M J K) :
    IsOrthSum Q M J K := by
  refine ⟨fun x hx y hy => ?_, h.disjoint, h.sup_eq⟩
  have := h.orth x hx y hy
  rw [bil_smul] at this
  exact (mul_eq_zero.1 this).resolve_left hc

/-- $\operatorname{rank}(J \perp K) = \operatorname{rank} J + \operatorname{rank} K$ (version for the Henselian setting). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem finrank_isOrthSum' {M P N : Submodule R V} (h : IsOrthSum Q M P N) :
    finrank R M = finrank R P + finrank R N := by
  rw [← h.sup_eq]; exact finrank_sup_of_disjoint' (F := F) h.disjoint

/-- **Splitting off a hyperbolic plane** (O'Meara 1963, §93F, p. 272, via 93:18 (v), p. 261): an $\mathfrak a$-modular
lattice $M$ of rank $\ge 5$, $\mathfrak a = \mathfrak o\alpha$, is $M = P \perp M'$ with $P = \mathfrak ox + \mathfrak oy$,
$Q(x) = Q(y) = 0$, $B(x, y) = \alpha$ (scale $\mathfrak a$), and $M'$ is $\mathfrak a$-modular of rank $\operatorname{rank} M - 2$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem exists_plane_split (hHil : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {M : Submodule R V}
    (hfg : M.FG) {α : F} (hα : α ≠ 0) (hM : IsModular Q (R ∙ α) M) (hrk : 5 ≤ finrank R M) :
    ∃ x y : V, ∃ M' : Submodule R V, Q x = 0 ∧ Q y = 0 ∧ bil Q x y = α ∧ IsOrthSum Q M (span R {x, y}) M' ∧
      IsModular Q (R ∙ α) M' ∧ M'.FG ∧ finrank R M' + 2 = finrank R M := by
  have hU := isUnimodular_smul_of_isModular Q hα hfg hM
  obtain ⟨x, y, K, hx, hy, hxy, hK⟩ := D18.omeara93_18_v_splitting (α⁻¹ • Q) hHil h2p hfg hU hrk
  have hQx : Q x = 0 := by
    simp only [smul_apply, smul_eq_mul] at hx
    exact (mul_eq_zero.1 hx).resolve_left (inv_ne_zero hα)
  have hQy : Q y = 0 := by
    simp only [smul_apply, smul_eq_mul] at hy
    exact (mul_eq_zero.1 hy).resolve_left (inv_ne_zero hα)
  have hbil : bil Q x y = α := by
    rw [bil_smul] at hxy
    field_simp at hxy
    exact hxy
  have hOS : IsOrthSum Q M (span R {x, y}) K := isOrthSum_of_smul Q (inv_ne_zero hα) hK
  have hPl : IsPlane Q (span R {x, y}) (R ∙ α) := ⟨x, y, hQx, hQy, rfl, by rw [hbil], by rw [hbil]; exact hα⟩
  have hKfg : K.FG := FG.of_le hfg (hOS.sup_eq ▸ le_sup_right)
  have hrank := finrank_isOrthSum' Q hOS
  rw [hPl.finrank_eq] at hrank
  have hP0 : span R {x, y} ≠ ⊥ := fun h => by
    have := hPl.finrank_eq; rw [h] at this; simp at this
  have hK0 : K ≠ ⊥ := fun h => by rw [h] at hrank; simp at hrank; omega
  refine ⟨x, y, K, hQx, hQy, hbil, hOS, ((Dedekind.isModular_iff_of_isOrthSum Q hOS hPl.fg hKfg hP0 hK0).1 hM).2, hKfg, by omega⟩

end Split

section Helpers

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- An orthogonal sum is moved to an orthogonal sum by $\sigma \in O(V)$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem isOrthSum_latMap {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) {M J K : Submodule R V} (h : IsOrthSum Q M J K) :
    IsOrthSum Q (latMap σ M) (latMap σ J) (latMap σ K) := by
  have hb : ∀ x y, bil Q (σ x) (σ y) = bil Q x y := fun x y => by
    rw [bil_eq_half, bil_eq_half, ← map_add, hσ, hσ, hσ]
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (hb x y).trans (h.orth x hx y hy)
  · rw [disjoint_iff, ← Submodule.map_inf ((σ : V →ₗ[F] V).restrictScalars R) σ.injective, h.disjoint.eq_bot, Submodule.map_bot]
  · rw [← Submodule.map_sup, h.sup_eq]

/-- Removing the plane $P$ lowers the total rank by $\operatorname{rank} P$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem sum_finrank_repl {t : ℕ} {Ls : Fin t → Submodule R V} {k0 : Fin t} {P L' : Submodule R V}
    (hPL : IsOrthSum Q (Ls k0) P L') :
    ∑ k, finrank R (repl Ls k0 L' k) + finrank R P = ∑ k, finrank R (Ls k) := by
  rw [← Finset.add_sum_erase Finset.univ (fun k => finrank R (repl Ls k0 L' k)) (Finset.mem_univ k0),
    ← Finset.add_sum_erase Finset.univ (fun k => finrank R (Ls k)) (Finset.mem_univ k0),
    repl_self, finrank_isOrthSum Q hPL]
  have : ∑ k ∈ Finset.univ.erase k0, finrank R (repl Ls k0 L' k) = ∑ k ∈ Finset.univ.erase k0, finrank R (Ls k) :=
    Finset.sum_congr rfl fun k hk => by
      rw [repl_of_ne Ls L' (Finset.ne_of_mem_erase hk)]
  rw [this]; ring

/-- **Hyperbolic spaces on a subspace.** -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem hyp_to_sub {W : Submodule F V} {X : Submodule R V} (hX : X ≤ W.restrictScalars R) {T : Submodule F V}
    (hT0 : ∀ z ∈ T, Q z = 0) (hTX : ∀ z ∈ T, z ∈ span F (X : Set V)) (hrk : finrank R X ≤ 2 * finrank F T) :
    ∃ T' : Submodule F W, (∀ z ∈ T', SuffSub.QW Q W z = 0) ∧
      (∀ z ∈ T', z ∈ span F ((SuffSub.subLatIn W X : Submodule R W) : Set W)) ∧
      finrank R (SuffSub.subLatIn W X) ≤ 2 * finrank F T' := by
  have hTW : ∀ z ∈ T, z ∈ W := fun z hz => by
    have : span F (X : Set V) ≤ W := span_le.mpr fun v hv => hX hv
    exact this (hTX z hz)
  refine ⟨T.comap W.subtype, fun z hz => hT0 _ hz, fun z hz => ?_, ?_⟩
  · have himg : W.subtype '' ((SuffSub.subLatIn W X : Submodule R W) : Set W) = (X : Set V) := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro hy; exact ⟨⟨y, hX hy⟩, hy, rfl⟩
    have h1 : (z : V) ∈ span F (X : Set V) := hTX _ hz
    rw [← himg, ← Submodule.map_span] at h1
    obtain ⟨s, hs, hsz⟩ := h1
    have : s = z := Subtype.ext hsz
    rwa [this] at hs
  · rw [SuffSub.finrank_subLatIn (X := X) hX le_rfl]
    have h1 := Submodule.finrank_map_subtype_eq W (T.comap W.subtype)
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr (fun z hz => hTW z hz)] at h1
    rw [← h1]; exact hrk

/-- A regular lattice $M$ has $2\dim T \le \operatorname{rank} M$ for every totally isotropic $T \subseteq FM$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem two_finrank_le_rank {M : Submodule R V} (hfg : M.FG) (hreg : IsRegular Q M) (T : Submodule F V)
    (hT : ∀ z ∈ T, Q z = 0) (hTM : ∀ z ∈ T, z ∈ span F (M : Set V)) : 2 * finrank F T ≤ finrank R M := by
  have hnd := RepTransfer.nondegenerate_subQ Q hreg
  let TU : Submodule F (D18.spanF F M) := T.comap (D18.spanF F M).subtype
  have h1 := two_finrank_le_of_isotropic (D18.subQ Q M) hnd TU (fun z hz => hT _ hz)
  have h2 : finrank F TU = finrank F T := by
    have h := Submodule.finrank_map_subtype_eq (D18.spanF F M) TU
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr (fun z hz => hTM z hz)] at h
    exact h.symm
  rw [h2, NecBlocks.finrank_spanF_of_isRegular Q hfg hreg] at h1
  exact h1

end Helpers

section Main

universe u v

open Sat93 Adjoin28 NecI Suff28 SuffRed SuffGood SuffStep SuffMain PadicClass

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] (F : Type u) [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

/-- **The sufficiency in 93:28 for good lattices of dimension exactly $4$** (O'Meara 1963, p. 272, "we can assume that
$\dim L_i = \dim K_i = 4$"): `GoodSuff` with the extra hypothesis that every component $L_k$ has rank $4$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (all dimensions 4)"]
def GoodSuff4 (t : ℕ) : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (Ls Ks : Fin t → Submodule R V) (a : Fin t → F),
      IsSaturated Q L Ls → IsSaturated Q K Ks → (∀ k, 3 ≤ finrank R (Ls k)) → (∀ k, finrank R (Ls k) = 4) →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      (∀ k : Fin t, (k : ℕ) = 0 → scale Q (Ls k) = 1) →
      SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a → IsometricLat Q Q L K

/-- `GoodSuff` for the lattices whose total excess rank $\sum_k \operatorname{rank} L_k$ is at most $4t + N$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
def GoodSuffBd (t N : ℕ) : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (Ls Ks : Fin t → Submodule R V) (a : Fin t → F),
      IsSaturated Q L Ls → IsSaturated Q K Ks → (∀ k, 3 ≤ finrank R (Ls k)) →
      ∑ k, finrank R (Ls k) ≤ 4 * t + N →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      (∀ k : Fin t, (k : ℕ) = 0 → scale Q (Ls k) = 1) →
      SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a → IsometricLat Q Q L K

variable {R F}

/-- **The plane-removal step** (O'Meara 1963, p. 272: "By making suitable cancellations to the $L_i$ and $K_i$ we see
that we can assume that $\dim L_i = \dim K_i = 4$"): in a good situation with a component of rank $\ge 5$, split a
hyperbolic plane $P$ off $L_{k_0}$ and (after Witt) off $K_{k_0}$, pass to $P^\perp$ and apply the induction
hypothesis. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (cancelling a hyperbolic plane)"]
theorem step_plane (hHil : LocalHilbertField F) {t N : ℕ} (ih : GoodSuffBd.{u, v} R F t N)
    {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (h2p : ¬ IsUnit (2 : R)) (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (L K : Submodule R V) [hLl : L.IsLattice F] [hKl : K.IsLattice F] (Ls Ks : Fin t → Submodule R V)
    (a : Fin t → F) (hLs : IsSaturated Q L Ls) (hKs : IsSaturated Q K Ks) (hd : ∀ k, 3 ≤ finrank R (Ls k))
    (hT : ∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
      finrank R (Ls k) ≤ 2 * finrank F T)
    (hsc : ∀ k : Fin t, (k : ℕ) = 0 → scale Q (Ls k) = 1) (hS : SameFundamentalInvariants Q Q L K Ls Ks a)
    (hC : Cond93 Q L Ls Ks a) (hbd : ∑ k, finrank R (Ls k) ≤ 4 * t + N + 1) (k0 : Fin t)
    (hk0 : 5 ≤ finrank R (Ls k0)) : IsometricLat Q Q L K := by
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hLle : ∀ k, Ls k ≤ L := fun k => hLs.1.split.iSup_eq ▸ le_iSup Ls k
  have hKle : ∀ k, Ks k ≤ K := fun k => hKs.1.split.iSup_eq ▸ le_iSup Ks k
  have hregL := isRegular_of_lattice_max Q hQ hLl
  have ha0 : ∀ k, a k ≠ 0 := fun k =>
    (hS.2.1 k).ne_zero Q (isRegular_fundSub Q hLfg hregL hLs.1 k) (fundSub_ne_bot Q hLfg hLs.1 k)
  have hk0fg : (Ls k0).FG := FG.of_le hLfg (hLle k0)
  have hKk0fg : (Ks k0).FG := FG.of_le hKfg (hKle k0)
  obtain ⟨x₀, -, y₀, -, hxy₀⟩ := exists_scale_eq Q hk0fg
  have hne : scale Q (Ls k0) ≠ ⊥ := (hLs.1.modular k0).1
  have hα : bil Q x₀ y₀ ≠ 0 := fun h => hne (by rw [hxy₀, h, span_singleton_eq_bot.mpr rfl])
  set α := bil Q x₀ y₀ with hαdef
  have hLmod : IsModular Q (R ∙ α) (Ls k0) := by rw [← hxy₀]; exact hLs.1.modular k0
  obtain ⟨⟨h0, hTy⟩, -, -⟩ := id hS
  have hc0 : Fin.cast h0 k0 = k0 := Fin.ext rfl
  have hscK : scale Q (Ks k0) = R ∙ α := by
    have := (hTy k0).2.1; rw [hc0] at this; rw [← this, hxy₀]
  have hKmod : IsModular Q (R ∙ α) (Ks k0) := by rw [← hscK]; exact hKs.1.modular k0
  have hrkK : finrank R (Ls k0) = finrank R (Ks k0) := by have := (hTy k0).1; rwa [hc0] at this
  obtain ⟨x, y, L', hx, hy, hxy, hOSL, hL'mod', hL'fg, hrkL⟩ := exists_plane_split Q hHil h2p hk0fg hα hLmod hk0
  obtain ⟨x', y', K', hx', hy', hxy', hOSK, hK'mod', hK'fg, hrkK'⟩ :=
    exists_plane_split Q hHil h2p hKk0fg hα hKmod (hrkK ▸ hk0)
  obtain ⟨σ, hσ, hσP⟩ := exists_orth_plane (R := R) Q hQ hx hy hx' hy' hxy hxy' hα
  have hinj : Function.Injective (σ : V →ₗ[F] V) := σ.injective
  have hφ : ∀ z, Q ((σ : V →ₗ[F] V) z) = Q z := fun z => hσ z
  -- move `K`
  haveI : (latMap σ K).IsLattice F := SuffSub.isLattice_latMap
  have hK₁fg : (latMap σ K).FG := Submodule.IsLattice.fg (A := F)
  have hKs₁ : IsSaturated Q (latMap σ K) (fun k => latMap σ (Ks k)) :=
    SuffSub.isSaturated_latMap Q hσ hKle hKfg hKs
  have hS₁ : SameFundamentalInvariants Q Q L (latMap σ K) Ls (fun k => latMap σ (Ks k)) a :=
    sameFund_moveK Q hσ hKle hS
  have hchfg : ∀ {X : Submodule R V} {Xs : Fin t → Submodule R V}, X.FG → (∀ k, Xs k ≤ X) →
      ∀ i, (jordanChain Xs i).FG := fun hX hle i => FG.of_le hX (iSup₂_le fun j _ => hle j)
  have hC₁ : Cond93 Q L Ls (fun k => latMap σ (Ks k)) a :=
    cond93_congr_right Q (hchfg hLfg hLle) (hchfg hKfg hKle)
      (fun i => by rw [← SuffSub.jordanChain_latMap]; exact isometricLat_latMap Q hσ _) hC
  have hOSK₁ : IsOrthSum Q ((fun k => latMap σ (Ks k)) k0) (span R {x, y}) (latMap σ K') := by
    have := isOrthSum_latMap Q hσ hOSK
    rwa [hσP] at this
  have hK₁'fg : (latMap σ K').FG := hK'fg.map _
  have hscK₁ : scale Q (latMap σ (Ks k0)) = R ∙ α := by
    rw [SuffSub.scale_map Q Q hinj hφ (hKle k0), hscK]
  have hK₁'mod : IsModular Q (scale Q ((fun k => latMap σ (Ks k)) k0)) (latMap σ K') := by
    show IsModular Q (scale Q (latMap σ (Ks k0))) (latMap σ K')
    rw [hscK₁]
    exact IsometricLat.isModular Q Q (adj_isometricLat_trans Q Q Q ⟨LinearEquiv.refl R _, fun x => rfl⟩
      (isometricLat_latMap Q hσ K')) hK'fg hK'mod'
  have hPl : IsPlane Q (span R {x, y}) (R ∙ α) := isPlane_span hx hy hxy hα
  have hL'mod : IsModular Q (scale Q (Ls k0)) L' := by rw [hxy₀]; exact hL'mod'
  have hsumL := isOrthSum_plane Q hLs.1.split hOSL hPl.regular
  have hsumK := isOrthSum_plane Q hKs₁.1.split hOSK₁ hPl.regular
  have hLs' := isSaturated_repl Q hLfg hLs hOSL hPl hL'mod
  have hKs' := isSaturated_repl Q hK₁fg hKs₁ hOSK₁ hPl hK₁'mod
  have hS' := sameFund_repl Q hLfg hK₁fg hLs.1 hKs₁.1 hOSL hOSK₁ hPl hL'mod hK₁'mod hS₁
  have hC' := cond93_repl Q hLfg hK₁fg hLs.1 hKs₁.1 hOSL hOSK₁ hPl hL'mod hK₁'mod ha0 hC₁
  have hLsfg := fg_repl Q hLfg hLs.1 hOSL hPl
  have hKsfg := fg_repl Q hK₁fg hKs₁.1 hOSK₁ hPl
  -- restrict to `W = P^⊥`
  have hspL := span_eq_perpF Q hPl.regular hsumL
  have hspK := span_eq_perpF Q hPl.regular hsumK
  set W := perpF Q (span R {x, y} : Submodule R V) with hW
  have hLW : (⨆ k, repl Ls k0 L' k) ≤ W.restrictScalars R := fun z hz => hspL ▸ subset_span hz
  have hKW : (⨆ k, repl (fun k => latMap σ (Ks k)) k0 (latMap σ K') k) ≤ W.restrictScalars R :=
    fun z hz => hspK ▸ subset_span hz
  have hLWl := SuffSub.isLattice_subLatIn hLW hLsfg hspL
  have hKWl := SuffSub.isLattice_subLatIn hKW hKsfg hspK
  have hQW : (QuadraticMap.associated (SuffSub.QW Q W)).Nondegenerate :=
    SuffSub.nondegenerate_QW Q hQ (span_sup_perpF Q hPl.regular hsumL) fun w hw u hu => perpF_orth_span Q hw hu
  have hsLs : ∀ k, repl Ls k0 L' k ≤ ⨆ k, repl Ls k0 L' k := fun k => le_iSup (repl Ls k0 L') k
  have hsKs : ∀ k, repl (fun k => latMap σ (Ks k)) k0 (latMap σ K') k ≤
      ⨆ k, repl (fun k => latMap σ (Ks k)) k0 (latMap σ K') k :=
    fun k => le_iSup (repl (fun k => latMap σ (Ks k)) k0 (latMap σ K')) k
  have hSatL := SuffSub.isSaturated_subLatIn Q hLW hsLs hLsfg hLs'
  have hSatK := SuffSub.isSaturated_subLatIn Q hKW hsKs hKsfg hKs'
  have hSW := (SuffSub.sameFundamentalInvariants_subLatIn Q hLW hKW hsLs hsKs _).mp hS'
  have hCW := (SuffSub.cond93_subLatIn Q hLW hKW hsLs hsKs hLsfg hKsfg _).mp hC'
  -- the hypotheses of the induction hypothesis
  have hrkP : finrank R (span R {x, y} : Submodule R V) = 2 := hPl.finrank_eq
  have hsum := sum_finrank_repl Q hOSL
  have hd' : ∀ k, 3 ≤ finrank R (SuffSub.subLatIn W (repl Ls k0 L' k)) := fun k => by
    rw [SuffSub.finrank_subLatIn (X := ⨆ k, repl Ls k0 L' k) hLW (hsLs k)]
    by_cases h : k = k0
    · subst h; rw [repl_self]; omega
    · rw [repl_of_ne Ls L' h]; exact hd k
  have hHyp : ∀ k, ∃ T : Submodule F V, (∀ z ∈ T, Q z = 0) ∧ (∀ z ∈ T, z ∈ span F (repl Ls k0 L' k : Set V)) ∧
      finrank R (repl Ls k0 L' k) ≤ 2 * finrank F T := fun k => by
    by_cases h : k = k0
    · subst h
      obtain ⟨T, hT0, hTM, hrk⟩ := hT k
      have hMreg : IsRegular Q (Ls k) := (hLs.1.modular k).isRegular Q hk0fg
      obtain ⟨T', h1, h2, h3⟩ := hyp_descent Q hMreg hk0fg hx hy hxy hα hOSL hrkL T hT0 hTM hrk
      exact ⟨T', h1, by rw [repl_self]; exact h2, by rw [repl_self]; exact h3⟩
    · rw [repl_of_ne Ls L' h]; exact hT k
  have hT' : ∀ k, ∃ T : Submodule F W, (∀ z ∈ T, SuffSub.QW Q W z = 0) ∧
      (∀ z ∈ T, z ∈ span F ((SuffSub.subLatIn W (repl Ls k0 L' k) : Submodule R W) : Set W)) ∧
      finrank R (SuffSub.subLatIn W (repl Ls k0 L' k)) ≤ 2 * finrank F T := fun k => by
    obtain ⟨T, h1, h2, h3⟩ := hHyp k
    exact hyp_to_sub Q ((hsLs k).trans hLW) h1 h2 h3
  have hsc' : ∀ k : Fin t, (k : ℕ) = 0 → scale (SuffSub.QW Q W) (SuffSub.subLatIn W (repl Ls k0 L' k)) = 1 :=
    fun k hk => by
      rw [SuffSub.scale_subLatIn Q hLW (hsLs k), scale_repl_eq Q hL'mod]; exact hsc k hk
  have hbd' : ∑ k, finrank R (SuffSub.subLatIn W (repl Ls k0 L' k)) ≤ 4 * t + N := by
    have : ∀ k, finrank R (SuffSub.subLatIn W (repl Ls k0 L' k)) = finrank R (repl Ls k0 L' k) := fun k =>
      SuffSub.finrank_subLatIn (X := ⨆ k, repl Ls k0 L' k) hLW (hsLs k)
    simp only [this]
    omega
  haveI := hLWl
  haveI := hKWl
  have hisoW := ih (SuffSub.QW Q W) h2p hQW _ _ _ _ a hSatL hSatK hd' hbd' hT' hsc' hSW hCW
  have hiso := (SuffSub.isometricLat_subLatIn Q hLW hKW).mpr hisoW
  have hLK₁ := isometricLat_of_tail Q hPl.fg hLsfg hsumL hsumK hiso
  exact adj_isometricLat_trans Q Q Q hLK₁ (adj_isometricLat_symm Q Q (isometricLat_latMap Q hσ K))


/-- `GoodSuff4` gives the case $N = 0$ of `GoodSuffBd`: ranks are even (hyperbolic) and $\ge 3$, so $\ge 4$, and total excess $0$ forces all ranks to be $4$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem goodSuffBd_zero {t : ℕ} (h4 : GoodSuff4.{u, v} R F t) : GoodSuffBd.{u, v} R F t 0 := by
  intro V _ _ _ _ _ Q h2p hQ L K _ _ Ls Ks a hLs hKs hd hbd hT hsc hS hC
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hLle : ∀ k, Ls k ≤ L := fun k => hLs.1.split.iSup_eq ▸ le_iSup Ls k
  have hrk4 : ∀ k, 4 ≤ finrank R (Ls k) := fun k => by
    obtain ⟨T, hT0, hTM, hrk⟩ := hT k
    have hfg : (Ls k).FG := FG.of_le hLfg (hLle k)
    have hreg : IsRegular Q (Ls k) := (hLs.1.modular k).isRegular Q hfg
    have := two_finrank_le_rank Q hfg hreg T hT0 hTM
    have := hd k
    omega
  have h4' : ∀ k, finrank R (Ls k) = 4 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨k, hk⟩ := hcon
    have : 4 * t < ∑ k, finrank R (Ls k) := by
      calc 4 * t = ∑ _k : Fin t, 4 := by simp [mul_comm]
        _ < ∑ k, finrank R (Ls k) :=
          Finset.sum_lt_sum (fun k _ => hrk4 k) ⟨k, Finset.mem_univ _, lt_of_le_of_ne (hrk4 k) (Ne.symm hk)⟩
    omega
  exact h4 Q h2p hQ L K Ls Ks a hLs hKs hd h4' hT hsc hS hC

/-- The case $N+1$ of `GoodSuffBd` from the case $N$: if some component has rank $\ge 5$, remove a plane (`step_plane`). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem goodSuffBd_succ (hHil : LocalHilbertField F) {t N : ℕ} (ih : GoodSuffBd.{u, v} R F t N) :
    GoodSuffBd.{u, v} R F t (N + 1) := by
  intro V _ _ _ _ _ Q h2p hQ L K _ _ Ls Ks a hLs hKs hd hbd hT hsc hS hC
  by_cases hle : ∑ k, finrank R (Ls k) ≤ 4 * t + N
  · exact ih Q h2p hQ L K Ls Ks a hLs hKs hd hle hT hsc hS hC
  · have : ∃ k0, 5 ≤ finrank R (Ls k0) := by
      by_contra hcon
      push_neg at hcon
      have : ∑ k, finrank R (Ls k) ≤ 4 * t :=
        calc ∑ k, finrank R (Ls k) ≤ ∑ _k : Fin t, 4 := Finset.sum_le_sum fun k _ => by have := hcon k; omega
          _ = 4 * t := by simp [mul_comm]
      omega
    obtain ⟨k0, hk0⟩ := this
    exact step_plane hHil ih Q h2p hQ L K Ls Ks a hLs hKs hd hT hsc hS hC (by omega) k0 hk0

/-- **Reduction of the good situation to dimension exactly $4$** (O'Meara 1963, §93F, proof of 93:28, sufficiency,
step 2, p. 272: "By Example 93:18 we know that each $L_i$ (or $K_i$) is of the form $\langle\xi A(0,0)\rangle \perp \cdots
\perp \langle\xi A(0,0)\rangle \perp L_i'$ with $\dim L_i' = 4$. By making suitable cancellations to the $L_i$ and
$K_i$ we see that we can assume that $\dim L_i = \dim K_i = 4$"): the sufficiency for good lattices of dimension $4$
implies it for all good lattices. The cancelled hyperbolic planes are split off one at a time (`step_plane`), by
induction on the total excess rank. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (reduction to dimension 4)"]
theorem goodSuff_of_goodSuff4 (hHil : LocalHilbertField F) {t : ℕ} (h4 : GoodSuff4.{u, v} R F t) :
    GoodSuff.{u, v} R F t := by
  have hall : ∀ N, GoodSuffBd.{u, v} R F t N := fun N => by
    induction N with
    | zero => exact goodSuffBd_zero h4
    | succ N ih => exact goodSuffBd_succ hHil ih
  intro V _ _ _ _ _ Q h2p hQ L K _ _ Ls Ks a hLs hKs hd hT hsc hS hC
  exact hall (∑ k, finrank R (Ls k)) Q h2p hQ L K Ls Ks a hLs hKs hd (by omega) hT hsc hS hC

end Main

end QuadFormsKB.OMeara.Dim4
