/-
# Hanke 2011, §1.3 and §3: local genera at the primes of a number field

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §1.3, p. 6 ($\mathrm{Gen}^*_{\mathfrak p}(S,\varepsilon;n)$), and §3.

For a prime $\mathfrak p$ of a number field $F$ (`v`), with completion $F_{\mathfrak p}$ and valuation ring $\mathcal O_{\mathfrak p}$:

* `LocGenus v n`: the *local genera* of $\mathcal O_{\mathfrak p}$-valued quadratic forms in $n$ variables, i.e. the classes of
  forms $T$ over $\mathcal O_{\mathfrak p}$ (coefficients in $\mathcal O_{\mathfrak p}$) under $T \sim T\circ g$, $g \in \mathrm{GL}_n(\mathcal O_{\mathfrak p})$
  (`Siegel.IsometricGL`); equivalently, the isometry classes of $\mathcal O_{\mathfrak p}$-valued lattices
  $L_{\mathfrak p} = \gamma\mathcal O_{\mathfrak p}^n$ in quadratic spaces over $F_{\mathfrak p}$ (the form of $L_{\mathfrak p}$ in a basis).
* Their invariants, well defined on classes: nondegeneracy (`LocGenus.Nondeg`), the Hessian determinant squareclass
  $\det_H(G_{\mathfrak p}) \in \mathrm{SqCl}(F_{\mathfrak p}^\times,\mathcal O_{\mathfrak p}^\times)$ (`LocGenus.det`), primitivity
  (`LocGenus.Prim`: the coefficients generate $\mathcal O_{\mathfrak p}$), the Hasse invariant
  $c_{\mathfrak p}(G_{\mathfrak p}) = \prod_{i<j}(a_i,a_j)_{\mathfrak p}$ of a diagonalization over $F_{\mathfrak p}$ (`LocGenus.hasse`, Cassels'
  `Composition.hasseC`), and Hanke's local density $\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})$ in Gram coordinates
  (`LocGenus.beta`, `Hanke2005.hankeBeta`).
* `LocGenus.IsGenStar S ε`: $G_{\mathfrak p} \in \mathrm{Gen}^*_{\mathfrak p}(S_{\mathfrak p},\varepsilon;n)$ (nondegenerate, primitive,
  $\det_H = S_{\mathfrak p}$, $c_{\mathfrak p} = \varepsilon$).
-/
import QuadFormsKB.Literature.Hanke2011Structure.GlobalMass
import QuadFormsKB.Literature.Hanke2011Structure.LocalGenera
import QuadFormsKB.Literature.Cassels.Ch14.Existence
import QuadFormsKB.Literature.LocalGlobal.HasseIsometryNF
import QuadFormsKB.LocalDensity.FormDensitySelf
import QuadFormsKB.Tamagawa.RatBridge

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField Matrix QuadFormsKB.Siegel QuadFormsKB.Lattices

noncomputable section

/-! ### Coefficients, values and isometries over a commutative ring -/

section Ring

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The value of a form whose coefficients all lie in the ideal $I$ lies in $I$. -/
theorem eval_mem_of_coeff_mem (Q : QuadForm R n) (I : Ideal R) (h : ∀ i j, Q.coeff i j ∈ I) (x : Fin n → R) :
    Q.eval x ∈ I := by
  rw [QuadForm.eval_eq_dotProduct' Q x]
  unfold dotProduct Matrix.mulVec dotProduct
  exact I.sum_mem fun i _ => I.mul_mem_left _ (I.sum_mem fun j _ => I.mul_mem_right _ (h i j))

/-- The coefficients of a form are values and differences of values: $c_{ii} = Q(e_i)$,
$c_{ij} = Q(e_i + e_j) - Q(e_i) - Q(e_j)$ ($i < j$), $c_{ij} = 0$ ($i > j$). -/
theorem coeff_mem_of_eval_mem (Q : QuadForm R n) (I : Ideal R) (h : ∀ x, Q.eval x ∈ I) (i j : Fin n) :
    Q.coeff i j ∈ I := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · have key : Q.coeff i j =
        Q.eval (Pi.single i 1 + Pi.single j 1) - Q.eval (Pi.single i 1) - Q.eval (Pi.single j 1) := by
      rw [QuadForm.eval_polar, Matrix.mulVec_single_one, single_one_dotProduct]
      have hz : Q.coeff j i = 0 := Q.upper (show id i < id j from hij)
      simp [QuadForm.hessian, hz]
    rw [key]
    exact I.sub_mem (I.sub_mem (h _) (h _)) (h _)
  · rw [← QuadForm.eval_single]; exact h _
  · rw [Q.upper (show id j < id i from hij)]; exact I.zero_mem

/-- If $Q \cong Q'$ and all coefficients of $Q$ lie in the ideal $I$, so do those of $Q'$. -/
theorem coeff_mem_of_isometricGL {Q Q' : QuadForm R n} (I : Ideal R) (hiso : IsometricGL Q Q')
    (h : ∀ i j, Q.coeff i j ∈ I) (i j : Fin n) : Q'.coeff i j ∈ I := by
  obtain ⟨g, hg⟩ := hiso
  refine coeff_mem_of_eval_mem Q' I (fun x => ?_) i j
  rw [← hg]
  exact eval_mem_of_coeff_mem Q I h _

/-- $Q \cong Q'$ over $R$ iff $Q' = Q\circ g$ for some $g \in \mathrm{GL}_n(R)$. -/
theorem isometricGL_iff_compMat {Q Q' : QuadForm R n} :
    IsometricGL Q Q' ↔ ∃ g : GL (Fin n) R, Q' = Q.compMat g.val := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, QuadForm.eq_of_eval_eq fun x => by rw [QuadForm.eval_compMat, hg]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, fun x => by rw [QuadForm.eval_compMat]⟩

/-- The span of the coefficients is an invariant of $\mathrm{GL}_n(R)$-equivalence. -/
theorem isPrimitiveForm_of_isometricGL {Q Q' : QuadForm R n} (hiso : IsometricGL Q Q') (h : IsPrimitiveForm Q) :
    IsPrimitiveForm Q' := by
  unfold IsPrimitiveForm at h ⊢
  rw [eq_top_iff, ← h, Ideal.span_le]
  rintro _ ⟨⟨i, j⟩, rfl⟩
  exact coeff_mem_of_isometricGL _ hiso.symm (fun a b => Ideal.subset_span (Set.mem_range.mpr ⟨(a, b), rfl⟩)) i j

end Ring

/-! ### Local genera -/

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $\mathrm{GL}_n(\mathcal O_{\mathfrak p})$-equivalence of $\mathcal O_{\mathfrak p}$-valued forms. -/
def locSetoid : Setoid (QuadForm 𝔬 n) where
  r := IsometricGL
  iseqv := ⟨fun T => IsometricGL.refl T, fun h => IsometricGL.symm h, fun h h' => IsometricGL.trans h h'⟩

/-- **The local genera** of $\mathcal O_{\mathfrak p}$-valued quadratic forms in $n$ variables (§1.3, p. 6): classes of forms over
$\mathcal O_{\mathfrak p}$ under $\mathrm{GL}_n(\mathcal O_{\mathfrak p})$-equivalence. -/
@[kb "hanke2011structure" "§1.3, p. 6 (local genera G_p)"]
abbrev LocGenus : Type := Quotient (locSetoid v n)

variable {v n}

/-- The class of a form. -/
def LocGenus.mk (T : QuadForm 𝔬 n) : LocGenus v n := Quotient.mk (locSetoid v n) T

theorem LocGenus.mk_eq_mk {T T' : QuadForm 𝔬 n} : LocGenus.mk T = LocGenus.mk T' ↔ IsometricGL T T' :=
  Quotient.eq (r := locSetoid v n)

/-! #### The Hessian determinant -/

theorem det_hessian_of_isometricGL {T T' : QuadForm 𝔬 n} (h : IsometricGL T T') :
    ∃ u : 𝔬ˣ, T'.hessian.det = (u : 𝔬) ^ 2 * T.hessian.det := by
  obtain ⟨g, rfl⟩ := isometricGL_iff_compMat.mp h
  refine ⟨Units.map detMonoidHom g, ?_⟩
  rw [det_hessian_compMat]
  rfl

/-- Nondegeneracy of a form over $\mathcal O_{\mathfrak p}$: $\det_H(T) \ne 0$. -/
theorem nondeg_of_isometricGL {T T' : QuadForm 𝔬 n} (h : IsometricGL T T') (hT : T.hessian.det ≠ 0) :
    T'.hessian.det ≠ 0 := by
  obtain ⟨u, hu⟩ := det_hessian_of_isometricGL h
  rw [hu]
  exact mul_ne_zero (pow_ne_zero _ u.ne_zero) hT

open Classical in
/-- The Hessian determinant squareclass of a form over $\mathcal O_{\mathfrak p}$ (the trivial class if $\det_H = 0$). -/
def detSqForm (T : QuadForm 𝔬 n) : LocalSqCl v :=
  if h : algebraMap 𝔬 Fv T.hessian.det ≠ 0 then SqCl.mk (Units.mk0 _ h) else 1

theorem algebraMap_ne_zero_iff {x : 𝔬} : algebraMap 𝔬 Fv x ≠ 0 ↔ x ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv))

theorem detSqForm_of_ne {T : QuadForm 𝔬 n} (h : algebraMap 𝔬 Fv T.hessian.det ≠ 0) :
    detSqForm T = SqCl.mk (Units.mk0 _ h) := by
  classical
  unfold detSqForm
  exact dite_eq_left h

theorem detSqForm_of_isometricGL {T T' : QuadForm 𝔬 n} (h : IsometricGL T T') : detSqForm T = detSqForm T' := by
  classical
  obtain ⟨u, hu⟩ := det_hessian_of_isometricGL h
  unfold detSqForm
  by_cases hT : algebraMap 𝔬 Fv T.hessian.det ≠ 0
  · have hT' : algebraMap 𝔬 Fv T'.hessian.det ≠ 0 := by
      rw [algebraMap_ne_zero_iff] at hT ⊢
      exact nondeg_of_isometricGL h hT
    rw [dite_eq_left hT, dite_eq_left hT']
    have hu' : (Units.map (algebraMap 𝔬 Fv).toMonoidHom u) ∈ localUnits v := ⟨u, rfl⟩
    have e : Units.mk0 _ hT' = Units.mk0 _ hT * (Units.map (algebraMap 𝔬 Fv).toMonoidHom u) ^ 2 := by
      apply Units.ext
      rw [Units.val_mk0, Units.val_mul, Units.val_mk0, Units.val_pow_eq_pow_val, hu, map_mul, map_pow, mul_comm]
      rfl
    rw [e, map_mul, SqCl.mk_sq_of_mem hu', mul_one]
  · have hT' : ¬ algebraMap 𝔬 Fv T'.hessian.det ≠ 0 := by
      rw [algebraMap_ne_zero_iff] at hT ⊢
      push Not at hT ⊢
      rw [hu, hT, mul_zero]
    rw [dite_eq_right hT, dite_eq_right hT']

/-! #### The Hasse invariant -/

/-- **Isometry invariance of the Hasse–Minkowski invariant over $F_{\mathfrak p}$** (every prime, dyadic included):
Cassels' $c(g) = \prod_{i<j}(a_i,a_j)$ (`Composition.hasseC`, from a chosen diagonalization) is the same for isometric
forms. -/
theorem hasseC_eq_of_isometricIn {g g' : QuadForm Fv n} (h : g.IsometricIn Fv g') :
    Composition.hasseC g = Composition.hasseC g' := by
  classical
  have hK := HasseIsoNF.localHilbertField_adicCompletion v
  by_cases hg : g.Nondegenerate
  · have hg' : g'.Nondegenerate := by
      obtain ⟨P, hP, hx⟩ := h
      have e : g' = g.compMat P := QuadForm.eq_of_eval_eq fun x => by
        rw [QuadForm.eval_compMat]
        have := hx x
        simp only [QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply] at this
        rw [QuadForm.eval, QuadForm.eval]
        exact this.symm
      unfold QuadForm.Nondegenerate at hg ⊢
      rw [e, det_hessian_compMat]
      exact mul_ne_zero (pow_ne_zero _ ((Matrix.isUnit_iff_isUnit_det P).mp
        ((Matrix.isUnit_iff_isUnit_det P).mpr hP) |>.ne_zero)) hg
    unfold Composition.hasseC
    simp only [hg, hg', ↓reduceDIte]
    obtain ⟨ha0, haiso⟩ := Classical.choose_spec (FieldGen.exists_isometric_diag g hg)
    obtain ⟨hb0, hbiso⟩ := Classical.choose_spec (FieldGen.exists_isometric_diag g' hg')
    exact PadicClass.hasseVec_eq_of_isometric hK n _ _ ha0 hb0
      (QuadForm.isometricIn_trans _ (QuadForm.isometricIn_symm _ haiso)
        (QuadForm.isometricIn_trans _ h hbiso))
  · have hg' : ¬ g'.Nondegenerate := by
      intro hg'
      apply hg
      obtain ⟨P, hP, hx⟩ := QuadForm.isometricIn_symm _ h
      have e : g = g'.compMat P := QuadForm.eq_of_eval_eq fun x => by
        rw [QuadForm.eval_compMat]
        have := hx x
        simp only [QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply] at this
        rw [QuadForm.eval, QuadForm.eval]
        exact this.symm
      unfold QuadForm.Nondegenerate at hg' ⊢
      rw [e, det_hessian_compMat]
      exact mul_ne_zero (pow_ne_zero _ hP.ne_zero) hg'
    unfold Composition.hasseC
    simp only [hg, hg', ↓reduceDIte]

/-- The Hasse invariant $c_{\mathfrak p}(T)$ of a form over $\mathcal O_{\mathfrak p}$, computed over $F_{\mathfrak p}$. -/
def hasseForm (T : QuadForm 𝔬 n) : ℤ := Composition.hasseC (T.map (algebraMap 𝔬 Fv))

theorem hasseForm_of_isometricGL {T T' : QuadForm 𝔬 n} (h : IsometricGL T T') : hasseForm T = hasseForm T' := by
  unfold hasseForm
  apply hasseC_eq_of_isometricIn
  rw [← isometricGL_iff_isometricIn]
  exact Tamagawa.RatBridge.isometricGL_map_hom (algebraMap 𝔬 Fv) h

/-! #### Hanke's local density -/

/-- Hanke's local density $\beta(\mathcal O_{\mathfrak p}^n, \tfrac12H_T)$ of a form over $\mathcal O_{\mathfrak p}$ (Gram coordinates). -/
def betaForm (T : QuadForm 𝔬 n) : ℝ := Hanke2005.hankeBeta v (std v) (Hanke2005.gramOf v T)

theorem betaForm_of_isometricGL {T T' : QuadForm 𝔬 n} (h : IsometricGL T T') : betaForm T = betaForm T' := by
  obtain ⟨g, rfl⟩ := isometricGL_iff_compMat.mp h
  unfold betaForm
  have e : Hanke2005.gramOf v (T.compMat g.val) =
      (g.val.map (algebraMap 𝔬 Fv))ᵀ * Hanke2005.gramOf v T * g.val.map (algebraMap 𝔬 Fv) := by
    unfold Hanke2005.gramOf
    rw [QuadForm.hessian_compMat, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [e, Hanke2005.hankeBeta_std_congr_unit v _ (g.isUnit.map detMonoidHom)]

/-! #### The invariants of a local genus -/

/-- **Nondegeneracy** of a local genus. -/
def LocGenus.Nondeg (G : LocGenus v n) : Prop :=
  Quotient.liftOn G (fun T => T.hessian.det ≠ 0) fun _ _ h => propext ⟨nondeg_of_isometricGL h,
    nondeg_of_isometricGL (IsometricGL.symm h)⟩

/-- **Primitivity** of a local genus: the coefficients of a representative generate $\mathcal O_{\mathfrak p}$. -/
def LocGenus.Prim (G : LocGenus v n) : Prop :=
  Quotient.liftOn G (fun T => IsPrimitiveForm T) fun _ _ h => propext ⟨isPrimitiveForm_of_isometricGL h,
    isPrimitiveForm_of_isometricGL (IsometricGL.symm h)⟩

/-- **The Hessian determinant squareclass** $\det_H(G_{\mathfrak p}) \in \mathrm{SqCl}(F_{\mathfrak p}^\times,\mathcal O_{\mathfrak p}^\times)$. -/
def LocGenus.det (G : LocGenus v n) : LocalSqCl v :=
  Quotient.liftOn G detSqForm fun _ _ h => detSqForm_of_isometricGL h

/-- **The Hasse invariant** $c_{\mathfrak p}(G_{\mathfrak p})$ (Serre's convention, $\prod_{i<j}(a_i,a_j)_{\mathfrak p}$). -/
def LocGenus.hasse (G : LocGenus v n) : ℤ :=
  Quotient.liftOn G hasseForm fun _ _ h => hasseForm_of_isometricGL h

/-- **Hanke's local density** $\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})$ (Gram coordinates). -/
def LocGenus.beta (G : LocGenus v n) : ℝ :=
  Quotient.liftOn G betaForm fun _ _ h => betaForm_of_isometricGL h

@[simp] theorem LocGenus.nondeg_mk (T : QuadForm 𝔬 n) : (LocGenus.mk T).Nondeg ↔ T.hessian.det ≠ 0 := Iff.rfl
@[simp] theorem LocGenus.prim_mk (T : QuadForm 𝔬 n) : (LocGenus.mk T).Prim ↔ IsPrimitiveForm T := Iff.rfl
@[simp] theorem LocGenus.det_mk (T : QuadForm 𝔬 n) : (LocGenus.mk T).det = detSqForm T := rfl
@[simp] theorem LocGenus.hasse_mk (T : QuadForm 𝔬 n) : (LocGenus.mk T).hasse = hasseForm T := rfl
@[simp] theorem LocGenus.beta_mk (T : QuadForm 𝔬 n) : (LocGenus.mk T).beta = betaForm T := rfl

/-- **$G_{\mathfrak p} \in \mathrm{Gen}^*_{\mathfrak p}(S_{\mathfrak p},\varepsilon;n)$** (§1.3, p. 6): $G_{\mathfrak p}$ is a nondegenerate
primitive local genus with $\det_H(G_{\mathfrak p}) = S_{\mathfrak p}$ and $c_{\mathfrak p}(G_{\mathfrak p}) = \varepsilon$. -/
@[kb "hanke2011structure" "§1.3, p. 6 (Gen*_p(S, ε; n))"]
def LocGenus.IsGenStar (S : LocalSqCl v) (ε : ℤ) (G : LocGenus v n) : Prop :=
  G.Nondeg ∧ G.Prim ∧ G.det = S ∧ G.hasse = ε

end

end QuadFormsKB.Hanke2011Structure
