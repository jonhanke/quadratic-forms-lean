/-
# Shimura 2004, Theorem 10.5 at the completions of $F^n$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Theorem 10.5 (printed p. 96),
used at every finite prime in the proof of Theorem 11.6 (p. 104).

**Setting.** $F$ a number field, $V = F^n$ with `Q : QuadForm F n`, $L$ a $\mathfrak g$-maximal lattice
(`IsGMaximal`); at a finite prime $v$ the completed form $\varphi_v$ =
`QuadForm.toQuadraticForm (Q.map (algebraMap F F_v))` on $F_v^n$ and the completed lattice $L_v$ = `loc v L.1`.

**Theorem 10.5.** `LocalTheorem10_5`: the book's Theorem 10.5 (`Theorem10_5`, `Diophantine.lean`, stated for every
finite-dimensional space over the completion of a number field), as a named structure; proved
(`localTheorem10_5_holds`, from `theorem10_5_holds` in `Theorem105.lean`).

**Proves** (unconditional; standard axioms only)
* `exists_locStab_mulVec_eq`: Theorem 10.5 in the coordinates of $F_v^n$: if $n > 2$, $\varphi$ is nondegenerate and
  satisfies (9.2), $L$ is $\mathfrak g$-maximal, and $x, y \in F_v^n$ have $\varphi_v[x] = \varphi_v[y] \ne 0$ and
  $\varphi_v(x, L_v) = \varphi_v(y, L_v)$, then $y = cx$ for some $c \in SO^\varphi(V)(F_v)$ with $cL_v = L_v$.

**Bridges used (all proved):** $L_v$ is $\mathfrak g_v$-maximal (`Lattices.isMaximal_loc_locFrac` with
`locFrac_one`); (9.2) gives (8.1) for $\varphi_v$ (the Gram matrix of any basis is ${}^tP\,G\,P$ with $G$ the Gram
matrix $\tfrac12(C + {}^tC)$ of the standard basis); the isometry $\gamma\in O^+(L_v)$ of Theorem 10.5 is the
matrix of a linear map of $F_v^n$.
-/
import QuadFormsKB.Literature.Shimura2004.Fundamental.Basic
import QuadFormsKB.Literature.Shimura2004.Fundamental.Theorem105
import QuadFormsKB.Literature.Hanke2005.MaximalSimilitude
import QuadFormsKB.Citation

open NumberField IsDedekindDomain Matrix Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa

/-- **Cited input: Shimura's Theorem 10.5** (Shimura 2004, p. 96; `Theorem10_5`), the local transitivity theorem
for a $\mathfrak g$-maximal lattice: at the completion $F_v$ of a number field, for $(V, \varphi)$ nondegenerate of
dimension $n > 1$ satisfying (8.1) and $L$ $\mathfrak g$-maximal, $\varphi[h] = \varphi[k] \ne 0$ and
$\varphi(h, L) = \varphi(k, L)$ imply $k = \gamma h$ with $\gamma \in SO^\varphi(V)$, $\gamma L = L$ (outside the
exceptional case $n = 2$, $V$ hyperbolic, $\varphi[h] \in 4\varphi(h, L)^2\mathfrak p$). Formerly a cited input; now
proved (`localTheorem10_5_holds`). -/
@[kb "shimura2004" "Thm. 10.5, p. 96 (as a named structure; proved)"]
structure LocalTheorem10_5 : Prop where
  holds : Theorem10_5

/-- **Theorem 10.5, proved** (`theorem10_5_holds`, `Theorem105.lean`). -/
@[kb "shimura2004" "Thm. 10.5, p. 96 (proved)"]
theorem localTheorem10_5_holds : LocalTheorem10_5 := ⟨theorem10_5_holds⟩

attribute [local instance] invTwo

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "Qv" => QuadForm.toQuadraticForm (QuadForm.map (algebraMap F (v.adicCompletion F)) Q)

/-- $\varphi_v(x, y) = \tfrac12\,{}^tx\,H y$ at the completion ($H$ the Hessian of $Q$). -/
theorem bil_locForm_eq (x y : Fin n → Fv) :
    OMeara.bil Qv x y = (x ⬝ᵥ (Q.hessian.map (algebraMap F Fv) *ᵥ y)) / 2 := by
  rw [OMeara.bil_eq_half, QuadForm.toQuadraticForm_apply, QuadForm.toQuadraticForm_apply,
    QuadForm.toQuadraticForm_apply, eval_map_eq, eval_map_eq, eval_map_eq, QuadForm.polar_eq_hessian]

/-- **(9.2) gives (8.1) at every completion**: for $n$ odd, the Gram matrix of $\varphi_v$ in every basis of
$F_v^n$ has determinant a unit of $\mathfrak g_v$ times a nonzero square. -/
theorem cond81_of_cond92 (hQ : Q.Nondegenerate) (h92 : Cond92 Q) :
    Cond81 (v.adicCompletionIntegers F) Qv := by
  classical
  intro hodd b
  have hfr : finrank Fv (Fin n → Fv) = n := Module.finrank_fin_fun Fv
  obtain ⟨u, c, hc, huc⟩ := h92 (by rwa [hfr] at hodd) v
  -- reindex `b` by `Fin n`
  let b' : Basis (Fin n) Fv (Fin n → Fv) := b.reindex (finCongr hfr)
  let P : Matrix (Fin n) (Fin n) Fv := (Pi.basisFun Fv (Fin n)).toMatrix b'
  let G : Matrix (Fin n) (Fin n) Fv := (1 / 2 : Fv) • Q.hessian.map (algebraMap F Fv)
  have hgram : OMeara.gram Qv b' = Pᵀ * G * P := by
    ext i j
    simp only [OMeara.gram, Matrix.of_apply, bil_locForm_eq, P, G, Matrix.mul_apply, Matrix.transpose_apply,
      Basis.toMatrix_apply, Pi.basisFun_repr, Matrix.smul_apply, smul_eq_mul, dotProduct, Matrix.mulVec,
      Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hdetG : G.det = algebraMap F Fv (((1 / 2 : F) • Q.hessian).det) := by
    have hG : G = (((1 / 2 : F) • Q.hessian)).map (algebraMap F Fv) := by
      ext i j
      simp only [G, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_div₀, map_one, map_ofNat]
    rw [hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hP : P.det ≠ 0 := by
    have hPP := (Pi.basisFun Fv (Fin n)).toMatrix_mul_toMatrix_flip b'
    intro h0
    have := congrArg Matrix.det hPP
    rw [det_mul, det_one] at this
    change P.det * _ = 1 at this
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  refine ⟨u, P.det * c, mul_ne_zero hP hc, ?_⟩
  have hre : (OMeara.gram Qv b).det = (OMeara.gram Qv b').det := by
    have : OMeara.gram Qv b' = (OMeara.gram Qv b).reindex (finCongr hfr) (finCongr hfr) := by
      ext i j; simp [OMeara.gram, b']
    rw [this, Matrix.det_reindex_self]
  rw [hre, hgram, det_mul, det_mul, det_transpose, hdetG, huc]
  change _ = ((u : v.adicCompletionIntegers F) : Fv) * _
  ring

/-- **Theorem 10.5 at the completion $F_v$ of $F^n$** (Shimura 2004, p. 96, as used in the proof of Theorem 11.6,
p. 104), unconditional (Theorem 10.5 is proved, `localTheorem10_5_holds`): if $n > 2$, $\varphi$ is nondegenerate and satisfies
(9.2), $L$ is a $\mathfrak g$-maximal lattice of $F^n$ and $x, y \in F_v^n$ satisfy $\varphi_v[x] = \varphi_v[y] \ne
0$ and $\varphi_v(x, L_v) = \varphi_v(y, L_v)$, then $y = c\,x$ for some $c \in SO^\varphi(V)(F_v)$ with
$c L_v = L_v$. -/
@[kb "shimura2004" "Thm. 10.5, p. 96 (at the completions of F^n, for a 𝔤-maximal lattice of F^n)"]
theorem exists_locStab_mulVec_eq (hQ : Q.Nondegenerate) (hn : 2 < n)
    (h92 : Cond92 Q) {L : Lat F n} (hL : IsGMaximal Q L) {x y : Fin n → Fv}
    (hxy : Q.evalIn Fv x = Q.evalIn Fv y) (hx : Q.evalIn Fv x ≠ 0)
    (hφ : phiIdeal Qv x (loc v L.1) = phiIdeal Qv y (loc v L.1)) :
    ∃ c : orthGroup Q Fv, (c : GL (Fin n) Fv).val.det = 1 ∧ locAct v (c : GL (Fin n) Fv) (loc v L.1) = loc v L.1 ∧
      (c : GL (Fin n) Fv).val *ᵥ x = y := by
  classical
  have hQv : ∀ z, Qv z = Q.evalIn Fv z := fun z => by
    rw [QuadForm.toQuadraticForm_apply, eval_map_eq]
  have hnd : (QuadraticMap.associated Qv).Nondegenerate := by
    have hmap : (Q.map (algebraMap F Fv)).Nondegenerate := by
      rw [QuadForm.Nondegenerate, hessian_map_eq, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero _).2 hQ
    exact QuadraticMap.nondegenerate_associated_iff.mpr
      (QuadraticMap.nondegenerate_polar_iff.mp (Hanke2005.polar_nondeg_toQuadraticForm _ hmap))
  have hfr : finrank Fv (Fin n → Fv) = n := Module.finrank_fin_fun Fv
  have hmax : OMeara.IsMaximal Qv 1 (loc v L.1) := by
    have h1 : (1 : Submodule (𝓞 F) F).FG := ⟨{1}, by simp [Submodule.one_eq_span]⟩
    have h0 : (1 : Submodule (𝓞 F) F) ≠ ⊥ := by
      intro h
      have : (1 : F) ∈ (1 : Submodule (𝓞 F) F) := Submodule.mem_one.2 ⟨1, map_one _⟩
      rw [h, Submodule.mem_bot] at this
      exact one_ne_zero this
    have := isMaximal_loc_locFrac Q v (a := 1) h1 h0 hL
    rwa [locFrac_one] at this
  obtain ⟨hne, -⟩ := localTheorem10_5_holds.holds F v (Fin n → Fv) (invTwo Fv) Qv hnd (by omega) (cond81_of_cond92 Q v hQ h92)
    (loc v L.1) hmax x y (by rw [hQv, hQv, hxy]) (by rw [hQv]; exact hx) hφ
  obtain ⟨γ, ⟨⟨hγo, hγL⟩, hγd⟩, hγxy⟩ := hne (fun he => by obtain ⟨h1, -⟩ := he; omega)
  -- the matrix of `γ`
  let g : GL (Fin n) Fv := ⟨LinearMap.toMatrix' (γ : (Fin n → Fv) →ₗ[Fv] (Fin n → Fv)),
    LinearMap.toMatrix' (γ.symm : (Fin n → Fv) →ₗ[Fv] (Fin n → Fv)),
    by rw [← LinearMap.toMatrix'_comp]; simp,
    by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hg : ∀ z, g.val *ᵥ z = γ z := fun z => by
    change LinearMap.toMatrix' (γ : (Fin n → Fv) →ₗ[Fv] (Fin n → Fv)) *ᵥ z = γ z
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have hgo : g ∈ orthGroup Q Fv := mem_orthGroup_of_evalIn Q fun z => by
    rw [hg, ← hQv, ← hQv]; exact hγo z
  refine ⟨⟨g, hgo⟩, ?_, ?_, ?_⟩
  · change (LinearMap.toMatrix' (γ : (Fin n → Fv) →ₗ[Fv] (Fin n → Fv))).det = 1
    rw [LinearMap.det_toMatrix', ← LinearEquiv.coe_det]
    have : LinearEquiv.det γ = 1 := hγd.2
    rw [this, Units.val_one]
  · change locAct v g (loc v L.1) = loc v L.1
    conv_rhs => rw [← hγL]
    ext z
    simp only [locAct, OMeara.latMap, Submodule.mem_map, LinearMap.coe_restrictScalars,
      Matrix.mulVecLin_apply, LinearEquiv.coe_coe, hg]
  · change g.val *ᵥ x = y
    rw [hg]; exact hγxy

end Local

end QuadFormsKB.Shimura2004
