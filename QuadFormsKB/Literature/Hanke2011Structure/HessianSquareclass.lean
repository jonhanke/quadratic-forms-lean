/-
# Hanke 2011, §2: the Hessian determinant squareclass of a lattice (Definition 2.1, Lemma 2.10)

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §2, pp. 7 and 11.

For a quadratic space $(F^n, Q)$ over a number field $F$ with $\det_H(Q) \ne 0$ and a lattice $L \subseteq F^n$
(an `Lattices.Lat F n`: a finitely generated $\mathcal O_F$-submodule spanning $F^n$, not necessarily free):

* `localHessDet Q v γ` $= \det_H(Q)\det(\gamma)^2 \in F_{\mathfrak p}^\times$, the Hessian determinant of the local form
  $Q_{\mathfrak p} = Q\circ\gamma$ of $L_{\mathfrak p} = \gamma\,\mathcal O_{\mathfrak p}^n$ in the basis given by the columns of
  $\gamma$ (`det_hessian_localForm`); its class in $\mathrm{SqCl}(F_{\mathfrak p}^\times, \mathcal O_{\mathfrak p}^\times)$ does not depend on
  the basis (`localHessDet_congr`).
* **Definition 2.1** (`detH`): the *Hessian determinant squareclass* $\det_H(L) \in \mathrm{SqCl}(\mathbb A_{F,f}^\times, U_f)$
  with components $\det_H(L)_{\mathfrak p} = \det_H(Q_{\mathfrak p})$ (`detH_comp`); $\operatorname{ord}_{\mathfrak p}(\det_H(L)) = 0$ for
  almost all $\mathfrak p$ (part of the construction, Lemma 2.2).
* **Lemma 2.10** (`lemma_2_10`): for $n \ge 1$, $S \in \mathrm{SqCl}(\mathbb A_{F,f}^\times, U_f)$ is $\det_H(L)$ for some
  nondegenerate rank $n$ quadratic $\mathcal O_F$-lattice $L$ iff $S$ is globally rational.

*Clarification* (Lemma 2.10): the paper writes "Given $n \in \mathbb N$"; its $\mathbb N$ is the positive integers
(§1.3). For $n = 0$ the only Hessian determinant is the empty determinant $1$, so the hypothesis $n \ge 1$ is needed.
The paper's proof uses the Hasse principle to find a space with $\det_H = \alpha$; a diagonal form suffices
(`exists_form_detH`), and the lattice is glued from local lattices (O'Meara 81:14, `LocFamily.glue`).
-/
import QuadFormsKB.Literature.Hanke2011Structure.AdelicSquareclasses
import QuadFormsKB.Literature.Cassels.Ch11Sec4Thm
import QuadFormsKB.LocalDensity.FormDensity

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField WithZero Matrix QuadFormsKB.Lattices

noncomputable section

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### Hessians of composite and mapped forms -/

theorem QuadForm.hessian_map' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (Q : QuadForm R n) :
    (Q.map f).hessian = Q.hessian.map f := by
  unfold QuadForm.hessian QuadForm.map
  simp [Matrix.map_add, Matrix.transpose_map]

/-- $\det_H(Q\circ X) = \det(X)^2\det_H(Q)$. -/
theorem det_hessian_compMat {A : Type*} [CommRing A] (Q : QuadForm A n) (X : Matrix (Fin n) (Fin n) A) :
    (Q.compMat X).hessian.det = X.det ^ 2 * Q.hessian.det := by
  rw [QuadForm.hessian_compMat, det_mul, det_mul, det_transpose]
  ring

/-! ### The local Hessian determinant -/

section Local

variable (Q : QuadForm F n) (hQ : Q.hessian.det ≠ 0) (v : HeightOneSpectrum (𝓞 F))

/-- **The local form** $Q_{\mathfrak p} = Q\circ\gamma$ of the local lattice $\gamma\,\mathcal O_{\mathfrak p}^n$ in the basis given by
the columns of $\gamma \in \mathrm{GL}_n(F_{\mathfrak p})$. -/
def localForm (γ : GL (Fin n) (v.adicCompletion F)) : QuadForm (v.adicCompletion F) n :=
  (Q.map (algebraMap F (v.adicCompletion F))).compMat γ.val

include hQ in
theorem localHessDet_ne_zero (γ : GL (Fin n) (v.adicCompletion F)) :
    algebraMap F (v.adicCompletion F) Q.hessian.det * γ.val.det ^ 2 ≠ 0 :=
  mul_ne_zero ((map_ne_zero _).mpr hQ) (pow_ne_zero _ (γ.isUnit.map detMonoidHom).ne_zero)

/-- **The local Hessian determinant** $\det_H(Q_{\mathfrak p}) = \det_H(Q)\det(\gamma)^2 \in F_{\mathfrak p}^\times$ for the local
basis $\gamma$. -/
def localHessDet (γ : GL (Fin n) (v.adicCompletion F)) : (v.adicCompletion F)ˣ :=
  Units.mk0 _ (localHessDet_ne_zero Q hQ v γ)

/-- `localHessDet` is the Hessian determinant of the local form `localForm`. -/
theorem det_hessian_localForm (γ : GL (Fin n) (v.adicCompletion F)) :
    (localForm Q v γ).hessian.det = (localHessDet Q hQ v γ : v.adicCompletion F) := by
  rw [localForm, det_hessian_compMat, QuadForm.hessian_map',
    show (Q.hessian.map (algebraMap F (v.adicCompletion F))).det = algebraMap F _ Q.hessian.det from
      (RingHom.map_det _ _).symm, localHessDet, Units.val_mk0]
  ring

/-- **Independence of the local basis:** two bases of the same local lattice give the same class in
$\mathrm{SqCl}(F_{\mathfrak p}^\times, \mathcal O_{\mathfrak p}^\times)$ (Definition 2.1: "$S_{\mathfrak p}$ does not depend on this choice of
generators"). -/
@[kb "hanke2011structure" "Def. 2.1, p. 7 (independence of the generators)"]
theorem localHessDet_congr {γ γ' : GL (Fin n) (v.adicCompletion F)}
    (h : locAct v γ (std v) = locAct v γ' (std v)) :
    (SqCl.mk (localHessDet Q hQ v γ) : LocalSqCl v) = SqCl.mk (localHessDet Q hQ v γ') := by
  have hstd : locAct v (γ⁻¹ * γ') (std v) = std v := by rw [locAct_mul, ← h, locAct_inv_locAct]
  obtain ⟨P, hP⟩ := exists_gl_o_of_locAct_eq v hstd
  have hu : IsUnit P.val.det := P.isUnit.map detMonoidHom
  let u : (v.adicCompletion F)ˣ := Units.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)).toMonoidHom
    hu.unit
  have hu_mem : u ∈ localUnits v := ⟨hu.unit, rfl⟩
  have hdet : γ'.val.det = γ.val.det * (u : v.adicCompletion F) := by
    have e : (u : v.adicCompletion F) = (γ⁻¹ * γ').val.det := by
      rw [← hP]
      change algebraMap _ _ P.val.det = _
      rw [RingHom.map_det]
      rfl
    rw [e, ← det_mul, ← Units.val_mul, mul_inv_cancel_left]
  have he : localHessDet Q hQ v γ' = localHessDet Q hQ v γ * u ^ 2 := by
    apply Units.ext
    simp only [localHessDet, Units.val_mk0, Units.val_mul, Units.val_pow_eq_pow_val, hdet]
    ring
  rw [he, map_mul, SqCl.mk_sq_of_mem hu_mem, mul_one]

/-- With the identity basis, `localHessDet` is $\det_H(Q)$. -/
theorem localHessDet_one :
    (localHessDet Q hQ v 1 : v.adicCompletion F) = algebraMap F (v.adicCompletion F) Q.hessian.det := by
  simp [localHessDet]

/-- $\det_H(Q)$ is a unit of $\mathcal O_{\mathfrak p}$ for almost all $\mathfrak p$. -/
theorem eventually_algebraMap_mem_localUnits {x : F} (hx : x ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      Units.mk0 (algebraMap F (w.adicCompletion F) x) ((map_ne_zero _).mpr hx) ∈ localUnits w := by
  filter_upwards [eventually_valuation_le_one x, eventually_valuation_le_one x⁻¹] with w h1 h2
  rw [mem_localUnits_iff, Units.val_mk0, valued_algebraMap]
  rw [map_inv₀] at h2
  have h0 : w.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  exact le_antisymm h1 (by
    by_contra hlt
    push Not at hlt
    have := one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr h0, hlt⟩
    exact absurd h2 (not_le.mpr this))

end Local

/-! ### Definition 2.1 -/

section Global

variable (Q : QuadForm F n) (hQ : Q.hessian.det ≠ 0)

/-- A chosen basis $\gamma_{\mathfrak p}$ of the local lattice: $L_{\mathfrak p} = \gamma_{\mathfrak p}\,\mathcal O_{\mathfrak p}^n$. -/
def locBasis (v : HeightOneSpectrum (𝓞 F)) (L : Lat F n) : GL (Fin n) (v.adicCompletion F) :=
  (exists_locAct_std_model v L).choose

theorem locBasis_spec (v : HeightOneSpectrum (𝓞 F)) (L : Lat F n) :
    loc v L.1 = locAct v (locBasis v L) (std v) :=
  (exists_locAct_std_model v L).choose_spec

theorem eventually_localHessDet_mem (L : Lat F n) :
    ∀ᶠ v in Filter.cofinite, (SqCl.mk (localHessDet Q hQ v (locBasis v L)) : LocalSqCl v) ∈ localUnitSqCl F v := by
  filter_upwards [loc_eventually_std L.2, eventually_algebraMap_mem_localUnits hQ] with v hv hu
  have h1 : locAct v (locBasis v L) (std v) = locAct v 1 (std v) := by
    rw [← locBasis_spec, hv, locAct_one]
  rw [localHessDet_congr Q hQ v h1]
  refine mk_mem_localUnitSqCl ?_
  convert hu using 1
  exact Units.ext (localHessDet_one Q hQ v)

/-- **Definition 2.1** (p. 7): the (non-archimedean) *Hessian determinant squareclass*
$\det_H(L) \in \mathrm{SqCl}(\mathbb A_{F,f}^\times, U_f)$ of a lattice $L$ on the nondegenerate space $(F^n, Q)$: the
squareclass with $\det_H(L)_{\mathfrak p} = \det_H(Q_{\mathfrak p})$, where $Q_{\mathfrak p}$ is the form of $L_{\mathfrak p}$ in a basis of
$L_{\mathfrak p}$ as a free $\mathcal O_{\mathfrak p}$-module (`detH_comp`). -/
@[kb "hanke2011structure" "Def. 2.1, p. 7"]
def detH (L : Lat F n) : AdelicSqCl F :=
  AdelicSqCl.ofLocal (fun v => SqCl.mk (localHessDet Q hQ v (locBasis v L))) (eventually_localHessDet_mem Q hQ L)

/-- **The components of $\det_H(L)$**: for every basis $\gamma$ of $L_{\mathfrak p}$,
$\det_H(L)_{\mathfrak p} = \det_H(Q\circ\gamma)$ (modulo $(\mathcal O_{\mathfrak p}^\times)^2$). -/
@[kb "hanke2011structure" "Def. 2.1, p. 7 (components)"]
theorem detH_comp (L : Lat F n) (v : HeightOneSpectrum (𝓞 F)) {γ : GL (Fin n) (v.adicCompletion F)}
    (hγ : loc v L.1 = locAct v γ (std v)) :
    AdelicSqCl.comp v (detH Q hQ L) = SqCl.mk (localHessDet Q hQ v γ) := by
  rw [detH, AdelicSqCl.comp_ofLocal]
  exact localHessDet_congr Q hQ v ((locBasis_spec v L).symm.trans hγ)

/-- **$\det_H(L)$ is globally rational** (first half of the proof of Lemma 2.10): $\rho_f(\det_H L) = \Delta(\det_H Q)$. -/
theorem detH_isGloballyRational (L : Lat F n) : IsGloballyRational (detH Q hQ L) := by
  rw [isGloballyRational_iff]
  refine ⟨Units.mk0 _ hQ, fun v => ?_⟩
  rw [detH_comp Q hQ L v (locBasis_spec v L), rhoLocal_mk]
  have he : localHessDet Q hQ v (locBasis v L) =
      unitsToLocal v (Units.mk0 _ hQ) * (Units.map detMonoidHom (locBasis v L)) ^ 2 := by
    apply Units.ext
    simp [localHessDet, unitsToLocal]
  rw [he, map_mul, SqCl.mk_sq_of_mem (Subgroup.mem_top _), mul_one]

end Global

/-! ### Lemma 2.10 -/

theorem unitsToLocal_val (v : HeightOneSpectrum (𝓞 F)) (α : Fˣ) :
    (unitsToLocal v α : v.adicCompletion F) = algebraMap F (v.adicCompletion F) α := rfl

/-- A diagonal form with prescribed Hessian determinant $\alpha$ ($n \ge 1$):
$Q = \frac{\alpha}2x_0^2 + \frac12(x_1^2 + \dots + x_{n-1}^2)$, with Hessian $\mathrm{diag}(\alpha, 1, \dots, 1)$. -/
theorem exists_form_detH (hn : 1 ≤ n) (α : F) : ∃ Q : QuadForm F n, Q.hessian.det = α := by
  refine ⟨QuadForm.diag fun i => if i = ⟨0, hn⟩ then α / 2 else 1 / 2, ?_⟩
  have hH : (QuadForm.diag fun i : Fin n => if i = ⟨0, hn⟩ then α / 2 else 1 / 2).hessian =
      Matrix.diagonal fun i => if i = ⟨0, hn⟩ then α else 1 := by
    unfold QuadForm.hessian QuadForm.diag
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.diagonal_apply_eq]
      split_ifs <;> ring
    · simp [Matrix.diagonal_apply_ne _ hij]
  rw [hH, Matrix.det_diagonal]
  simp

/-- The diagonal matrix $\mathrm{diag}(\beta, 1, \dots, 1)$ ($n \ge 1$). -/
def diagFirst (hn : 1 ≤ n) {K : Type*} [Field K] (β : Kˣ) : GL (Fin n) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal fun i : Fin n => if i = (⟨0, hn⟩ : Fin n) then (β : K) else 1) (by
    rw [Matrix.det_diagonal]
    simp)

theorem det_diagFirst (hn : 1 ≤ n) {K : Type*} [Field K] (β : Kˣ) : (diagFirst hn β).val.det = β := by
  change (Matrix.diagonal fun i : Fin n => if i = (⟨0, hn⟩ : Fin n) then (β : K) else 1).det = β
  rw [Matrix.det_diagonal]
  simp

theorem diagFirst_one (hn : 1 ≤ n) {K : Type*} [Field K] : diagFirst hn (1 : Kˣ) = 1 := by
  apply Units.ext
  change (Matrix.diagonal fun i : Fin n => if i = (⟨0, hn⟩ : Fin n) then ((1 : Kˣ) : K) else 1) = 1
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply]

/-- Equal squareclasses differ by a square: $\bar a = \bar b$ in $\mathrm{SqCl}(G,H)$ gives $b = a c^2$ with $c \in H$. -/
theorem SqCl.exists_eq_mul_sq {G : Type*} [CommGroup G] {H : Subgroup G} {a b : G}
    (h : (SqCl.mk a : SqCl G H) = SqCl.mk b) : ∃ c ∈ H, b = a * c ^ 2 := by
  obtain ⟨c, hc, hce⟩ := QuotientGroup.eq.mp h
  refine ⟨c, hc, ?_⟩
  have hce' : c ^ 2 = a⁻¹ * b := hce
  rw [hce', mul_inv_cancel_left]

theorem SqCl.mk_mul_sq {G : Type*} [CommGroup G] {H : Subgroup G} (a : G) {c : G} (hc : c ∈ H) :
    (SqCl.mk (a * c ^ 2) : SqCl G H) = SqCl.mk a := by
  rw [map_mul, SqCl.mk_sq_of_mem hc, mul_one]

/-- The local lattices $\mathrm{diag}(\beta_{\mathfrak p}, 1, \dots, 1)\,\mathcal O_{\mathfrak p}^n$, almost all standard. -/
def diagFamily (hn : 1 ≤ n) (β : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hβ : ∀ᶠ v in Filter.cofinite, β v = 1) : LocFamily F n where
  M v := locAct v (diagFirst hn (β v)) (std v)
  isLattice v := locAct_isLattice _ (isLattice_of_bounds v le_rfl le_rfl)
  eventually_std := by
    filter_upwards [hβ] with v hv
    rw [hv, diagFirst_one, locAct_one]

/-- If $\rho_{\mathfrak p}(S_{\mathfrak p}) = \alpha$ and both $S_{\mathfrak p}$ and $\alpha$ are unit classes, then $S_{\mathfrak p} = \alpha$
in $\mathrm{SqCl}(F_{\mathfrak p}^\times, \mathcal O_{\mathfrak p}^\times)$ (a unit which is a square is the square of a unit). -/
theorem localSqCl_eq_of_rho {v : HeightOneSpectrum (𝓞 F)} {x a : (v.adicCompletion F)ˣ}
    (hx : x ∈ localUnits v) (ha : a ∈ localUnits v)
    (h : rhoLocal v (SqCl.mk x) = SqCl.mk a) : (SqCl.mk x : LocalSqCl v) = SqCl.mk a := by
  rw [rhoLocal_mk] at h
  obtain ⟨c, -, hc⟩ := SqCl.exists_eq_mul_sq h
  have hc2 : c ^ 2 ∈ localUnits v := by
    have : c ^ 2 = x⁻¹ * a := by rw [hc, inv_mul_cancel_left]
    rw [this]
    exact (localUnits v).mul_mem ((localUnits v).inv_mem hx) ha
  rw [hc, SqCl.mk_mul_sq x (sq_mem_localUnits v hc2)]

/-- **Lemma 2.10** (Classifying Hessian squareclasses, p. 11): for $n \ge 1$, a non-archimedean squareclass
$S \in \mathrm{SqCl}(\mathbb A_{F,f}^\times, U_f)$ is the Hessian determinant squareclass $\det_H(L)$ of some nondegenerate rank
$n$ quadratic $\mathcal O_F$-lattice $L$ (on some space $(F^n, Q)$, not necessarily $\mathcal O_F$-valued) iff $S$ is
globally rational. -/
@[kb "hanke2011structure" "Lemma 2.10, p. 11"]
theorem lemma_2_10 (hn : 1 ≤ n) (S : AdelicSqCl F) :
    (∃ (Q : QuadForm F n) (hQ : Q.hessian.det ≠ 0) (L : Lat F n), detH Q hQ L = S) ↔ IsGloballyRational S := by
  constructor
  · rintro ⟨Q, hQ, L, rfl⟩
    exact detH_isGloballyRational Q hQ L
  intro hS
  obtain ⟨α, hα⟩ := (isGloballyRational_iff S).mp hS
  obtain ⟨Q, hQα⟩ := exists_form_detH hn (α : F)
  have hQ : Q.hessian.det ≠ 0 := by rw [hQα]; exact α.ne_zero
  -- local square roots: at each prime choose `β` with `S_𝔭 = α β²`, and `β = 1` where `S_𝔭 = α` already
  have hroot : ∀ v : HeightOneSpectrum (𝓞 F), ∃ β : (v.adicCompletion F)ˣ,
      AdelicSqCl.comp v S = SqCl.mk (unitsToLocal v α * β ^ 2) ∧
        (AdelicSqCl.comp v S = SqCl.mk (unitsToLocal v α) → β = 1) := by
    intro v
    by_cases h1 : AdelicSqCl.comp v S = SqCl.mk (unitsToLocal v α)
    · exact ⟨1, by rw [one_pow, mul_one, h1], fun _ => rfl⟩
    · obtain ⟨s, hs⟩ := SqCl.mk_surjective (AdelicSqCl.comp v S)
      have h2 := hα v
      rw [← hs, rhoLocal_mk] at h2
      obtain ⟨b, -, hb⟩ := SqCl.exists_eq_mul_sq h2
      refine ⟨b⁻¹, ?_, fun h => absurd h h1⟩
      rw [← hs, hb, inv_pow, mul_inv_cancel_right]
  choose β hβ hβ1 using hroot
  -- the set of primes where `S_𝔭 ≠ α` is finite
  have hfin : ∀ᶠ v in Filter.cofinite, AdelicSqCl.comp v S = SqCl.mk (unitsToLocal v α) := by
    obtain ⟨x, rfl⟩ := SqCl.mk_surjective S
    filter_upwards [eventually_ideleComp_mem_localUnits x, eventually_algebraMap_mem_localUnits α.ne_zero]
      with v hx ha
    have ha' : unitsToLocal v α ∈ localUnits v := by
      convert ha using 1
      exact Units.ext rfl
    have h2 := hα v
    rw [AdelicSqCl.comp_mk] at h2 ⊢
    exact localSqCl_eq_of_rho hx ha' h2
  have hβev : ∀ᶠ v in Filter.cofinite, β v = 1 := by
    filter_upwards [hfin] with v hv
    exact hβ1 v hv
  let M : LocFamily F n := diagFamily hn β hβev
  refine ⟨Q, hQ, ⟨M.glue, M.glue_isLattice⟩, AdelicSqCl.ext fun v => ?_⟩
  have hloc : loc v M.glue = locAct v (diagFirst hn (β v)) (std v) := M.loc_glue v
  rw [detH_comp Q hQ ⟨M.glue, M.glue_isLattice⟩ v hloc, hβ v]
  refine congrArg SqCl.mk (Units.ext ?_)
  rw [localHessDet, Units.val_mk0, det_diagFirst, hQα, Units.val_mul, Units.val_pow_eq_pow_val, unitsToLocal_val]

end

end QuadFormsKB.Hanke2011Structure
