/-
# From O'Meara's local lattice theory to the library's matrix groups

**Layer:** a number field $F$, a finite spot $\mathfrak p$ = `v`, the completion $F_\mathfrak p$ = `v.adicCompletion F`,
the space $V_\mathfrak p = F_\mathfrak p^n$ with the Mathlib form `qk Q F_𝔭` ($x \mapsto Q(x)$, O'Meara's $Q$ on
$V_\mathfrak p$ with $B(x, x) = Q(x)$, `Lattices/SpinorNorm.lean`), and the localization $L_\mathfrak p$ = `loc v L.1`.

The local results of Chapter IX (91:2, 91:8, 92:5, 93:20, 93:29, ...) are proved for O'Meara's objects: isometries
$\sigma \in O(V)$ as linear equivalences (`OMeara.orth`), classes `OMeara.cls`, spinor norms `OMeara.HasSpinorNorm`.
The global theory of the library (genus, spinor genus, strong approximation) uses matrices: `orthGroup Q F_𝔭`,
`locStabV`, `spinorNorm`. The comparison of the two groups, `QIn.glEquiv` with `QIn.map_orthGroup` and
`QIn.glEquiv_symmProd`, is in `Sec95Input.lean`; this file adds lattices, determinants and spinor norms.

**Proves**
* `qk_eq_toQuadraticForm_map`: `qk Q K` is the form `QuadForm.toQuadraticForm (Q.map (algebraMap F K))` used in
  `Sec104LocalMod.lean` and `Hanke2005`;
* `locAct_eq_latMap`, `det_eq_glEquiv`: the matrix $g$ moves lattices and has determinant as the linear map
  $\sigma = $ `glEquiv g` does;
* `spinorNorm_eq_of_hasSpinorNorm`: if $\sigma$ = `glEquiv g` has O'Meara spinor norm $c$, then
  $\theta(g) = c\,F_\mathfrak p^{\times 2}$;
* `spinorNormsContainUnits_of_omeara`: O'Meara's local statement "$\theta(O^+(L_\mathfrak p)) \supseteq \mathfrak u$"
  (the conclusion of 91:8, 92:5, 93:20) gives the hypothesis `SpinorNormsContainUnits` of 102:9 (`Sec104Nine.lean`);
* `exists_locAct_eq_of_mem_cls`: O'Meara's local isometry of lattices ($K_\mathfrak p \in \operatorname{cls}L_\mathfrak p$)
  gives the local condition of `SameGenus`.
-/
import QuadFormsKB.Literature.OMeara.Sec104Nine
import QuadFormsKB.Literature.OMeara.Sec95Input

open NumberField IsDedekindDomain Matrix
open QuadFormsKB.OMeara.QIn (glEquiv glEquiv_apply glEquiv_symmProd map_orthGroup)

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

section General

variable (K : Type) [Field K] [Algebra F K] [CharZero K]

/-- The two descriptions of the form $x \mapsto Q(x)$ on $K^n$ agree: `qk Q K` (`Q.toQuadraticFormIn K`) is
`QuadForm.toQuadraticForm (Q.map (algebraMap F K))`. -/
theorem qk_eq_toQuadraticForm_map : qk Q K = QuadForm.toQuadraticForm (Q.map (algebraMap F K)) := by
  ext x
  rw [qk_apply, QuadForm.toQuadraticForm_apply, eval_map_eq]

/-- Every O'Meara isometry $\sigma \in O(V_K)$ (`OMeara.orth (qk Q K)`) is `glEquiv g` for a matrix $g$ of the
library's orthogonal group `orthGroup Q K`. -/
theorem exists_orthGroup_glEquiv_eq {σ : (Fin n → K) ≃ₗ[K] (Fin n → K)} (hσ : σ ∈ OMeara.orth (qk Q K)) :
    ∃ g : orthGroup Q K, glEquiv K (g : GL (Fin n) K) = σ := by
  rw [← map_orthGroup Q K] at hσ
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hσ
  exact ⟨⟨g, hg⟩, rfl⟩

/-- The determinant of the matrix $g$ is the determinant of the linear map `glEquiv g`. -/
theorem det_eq_glEquiv (g : GL (Fin n) K) :
    (g : Matrix (Fin n) (Fin n) K).det = LinearMap.det ((glEquiv K g : (Fin n → K) ≃ₗ[K] (Fin n → K)) :
      (Fin n → K) →ₗ[K] (Fin n → K)) := by
  have e : ((glEquiv K g : (Fin n → K) ≃ₗ[K] (Fin n → K)) : (Fin n → K) →ₗ[K] (Fin n → K)) =
      Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) := by
    refine LinearMap.ext fun x => ?_
    rw [LinearEquiv.coe_coe, glEquiv_apply, Matrix.toLin'_apply]
  rw [e, LinearMap.det_toLin']

/-- **The spinor norms agree**: if `glEquiv g` has O'Meara spinor norm $c \ne 0$ (`OMeara.HasSpinorNorm`), then the
library spinor norm of $g$ is the class $c\,K^{\times 2}$. -/
theorem spinorNorm_eq_of_hasSpinorNorm (hQ : Q.Nondegenerate) {g : orthGroup Q K} {c : K} (hc0 : c ≠ 0)
    (h : OMeara.HasSpinorNorm (qk Q K) (glEquiv K (g : GL (Fin n) K)) c) :
    spinorNorm Q K g = sqClassOf c := by
  obtain ⟨l, hl, hσl, s, hs0, hprod⟩ := h
  have hlQ : ∀ x ∈ l, Q.evalIn K x ≠ 0 := fun x hx => by rw [← qk_apply]; exact hl x hx
  have heq : g = symmProd Q K l := by
    apply Subtype.ext
    apply (glEquiv K).injective
    rw [hσl, glEquiv_symmProd Q K l hlQ]
    exact OMeara.Cl54.attach_prod_eq_symProd (qk Q K) l hl
  have hv : valProd Q K l = c * s ^ 2 := by
    rw [← hprod, valProd]
    congr 1
    exact List.map_congr_left fun x _ => (qk_apply Q K x).symm
  rw [heq, spinorNorm_symmProd Q K hQ l hlQ, hv, sqClassOf_mul hc0 (pow_ne_zero 2 hs0),
    (sqClassOf_eq_one_iff (pow_ne_zero 2 hs0)).mpr ⟨s, sq s⟩, mul_one]

end General

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- The matrix $g$ moves the localization as the linear map `glEquiv g` does: `locAct` is O'Meara's `latMap`. -/
theorem locAct_eq_latMap (g : GL (Fin n) Fv) (M : Submodule 𝔬 (Fin n → Fv)) :
    locAct v g M = OMeara.latMap (glEquiv Fv g) M := by
  ext x
  simp only [locAct, OMeara.latMap, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply,
    LinearEquiv.coe_coe, glEquiv_apply]

/-- **O'Meara's local isometry of lattices gives the local condition of the genus**: if $K_\mathfrak p \in
\operatorname{cls}L_\mathfrak p$ in O'Meara's sense (`OMeara.cls` for the form `qk Q F_𝔭`), then some
$g \in O(V_\mathfrak p)$ (`orthGroup`) has $gL_\mathfrak p = K_\mathfrak p$ (`locAct`). -/
theorem exists_locAct_eq_of_mem_cls {L K : Submodule (𝓞 F) (Fin n → F)}
    (h : loc v K ∈ OMeara.cls (qk Q Fv) (loc v L)) :
    ∃ g : orthGroup Q Fv, locAct v (g : GL (Fin n) Fv) (loc v L) = loc v K := by
  obtain ⟨σ, hσ, hK⟩ := h
  obtain ⟨g, hg⟩ := exists_orthGroup_glEquiv_eq Q Fv hσ
  exact ⟨g, by rw [hK, locAct_eq_latMap, hg]⟩

/-- **O'Meara's "$\theta(O^+(L_\mathfrak p)) \supseteq \mathfrak u_\mathfrak p$" gives `SpinorNormsContainUnits`** (O'Meara
1973, §102B, hypothesis of 102:9, p. 304): if every unit $\varepsilon$ of $\mathfrak o_\mathfrak p$ is the O'Meara spinor
norm of some rotation $\sigma \in O^+(L_\mathfrak p)$ (`OMeara.orthLatPlus` of `loc v L.1` for the form `qk Q F_𝔭`;
this is the conclusion of 91:8, 92:5 and 93:20), then `SpinorNormsContainUnits Q v L`. -/
@[kb "omeara1963" "§102B, 102:9, p. 304 (hypothesis θ(O⁺(L_𝔭)) ⊇ 𝔲_𝔭, from the local theory)"]
theorem spinorNormsContainUnits_of_omeara (hQ : Q.Nondegenerate) (L : Lat F n)
    (h : ∀ ε : 𝔬, IsUnit ε → ∃ σ ∈ OMeara.orthLatPlus (qk Q Fv) (loc v L.1),
        OMeara.HasSpinorNorm (qk Q Fv) σ (algebraMap 𝔬 Fv ε)) :
    SpinorNormsContainUnits Q v L := by
  intro u hu
  let ε : 𝔬 := ⟨u, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hu.le⟩
  have hε : IsUnit ε := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]; exact hu
  obtain ⟨σ, hσ, hsn⟩ := h ε hε
  have hσL := (Subgroup.mem_inf.mp hσ).1
  have hσP := (Subgroup.mem_inf.mp hσ).2
  obtain ⟨g, hg⟩ := exists_orthGroup_glEquiv_eq Q Fv hσL.1
  have hu0 : u ≠ 0 := by rintro rfl; rw [map_zero] at hu; exact zero_ne_one hu
  refine ⟨g, ?_, ?_, ?_⟩
  · change locAct v (g : GL (Fin n) Fv) (loc v L.1) = loc v L.1
    rw [locAct_eq_latMap, hg]; exact hσL.2
  · have hdet := congrArg Units.val (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hσP).2)
    rw [LinearEquiv.coe_det, Units.val_one] at hdet
    exact Units.ext (by rw [detHom_val, Units.val_one, det_eq_glEquiv, hg]; exact hdet)
  · exact spinorNorm_eq_of_hasSpinorNorm Q Fv hQ hu0 (by rw [hg]; exact hsn)

end Local

end QuadFormsKB.Lattices
