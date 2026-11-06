/-
# Hanke 2011, Lemma 3.7: global genera and tuples of local genera

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §3, Lemma 3.7, p. 13.

**Part A: the localization map.** For a quadratic space $(F^n, Q)$ over a number field $F$ and an $\mathcal O_F$-valued
lattice $L$ (`Lattices.IsIntegral Q L`), the local form $Q\circ\gamma$ of $L_{\mathfrak p} = \gamma\,\mathcal O_{\mathfrak p}^n$ has
coefficients in $\mathcal O_{\mathfrak p}$ (`localForm_coeff_integral`); its class `locGenusOf Q L hL v` is a local genus
(`LocGenus v n`) independent of the basis (`locGenusOf_eq`). The family $(\mathrm{locGenusOf}\ Q\ L\ \mathfrak p)_{\mathfrak p}$ is the
paper's localization map $\lambda : L \mapsto (L_{\mathfrak p})_f$ (proof of Lemma 3.7).

* **Comparison with the repository's genus** (`sameGenus_iff_locGenusOf`): two lattices on the same space are in the
  same genus (`Lattices.SameGenus`: locally isometric at every prime) iff their local genera agree at every prime.

**Part B: the invariants and the inclusion $\mathrm{Gen}^* \subseteq \mathrm{Gen}^*_f$.** The local genera of $L$ are
nondegenerate with $\det_H = \det_H(L)_{\mathfrak p}$ (`det_locGenusOf`), their Hasse invariants are Serre's
$\varepsilon_{\mathfrak p}$ of a diagonalization of $Q$ over $F$ (`hasse_locGenusOf`), and their product is
$\varepsilon_\infty = \prod_{v\mid\infty}c_v((\vec\sigma_\infty)_v)$ (`finprod_hasse_locGenusOf`, Hilbert reciprocity).
`GenStar` and `GenStarF` are the paper's $\mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)$ (as the image of the
localization map) and $\mathrm{Gen}^*_f(S,\varepsilon_\infty,\vec c_{\mathbb S};n)$; `genStar_subset_genStarF`. The reverse
inclusion and Lemma 3.7 itself are in `Lemma37Exist.lean` (`lemma_3_7`).

*Erratum* (Lemma 3.7, missing hypothesis; proposed by the formalization, not yet confirmed by the author): "$S$ globally rational" is not
enough. If $\rho_f(S) = \Delta(\alpha)$ ($\alpha \in F^\times$, unique up to squares), every form with $\det_H(L) = S$ has
determinant $\equiv \alpha$ modulo squares, so its sign at a real place $w$ is that of $\alpha$; when it differs from
$(-1)^{\sigma_{w,-}}$, $\mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n) = \emptyset$ while $\mathrm{Gen}^*_f$ need not be empty.
Example: $F = \mathbb Q$, $n = 3$, $S = 8$, $\vec\sigma_\infty = (0,3)$: no negative definite form has $\det_H \equiv 8$, but
the local genera of $x^2 - y^2 - z^2$ ($c_2 = (-1,-1)_2 = -1$, $c_p = 1$ for $p$ odd) lie in $\mathrm{Gen}^*_f(8, -1; 3)$. With
the hypothesis "$(-1)^{\sigma_{w,-}}\alpha$ is a square at every real $w$" the lemma holds (`lemma_3_7`).
-/
import QuadFormsKB.Literature.Hanke2011Structure.LocalGeneraNF
import QuadFormsKB.Literature.Hanke2011Structure.Signatures
import QuadFormsKB.Literature.OMeara.Sec72

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField Matrix QuadFormsKB.Siegel QuadFormsKB.Lattices

noncomputable section

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### Forms with integral coefficients -/

/-- A form whose values at $e_i$ and $e_i + e_j$ lie in the additive subgroup $S$ has its coefficients in $S$. -/
theorem coeff_mem_of_eval_single_mem {R : Type*} [CommRing R] (Q : QuadForm R n) (S : AddSubgroup R)
    (h1 : ∀ i, Q.eval (Pi.single i 1) ∈ S) (h2 : ∀ i j, Q.eval (Pi.single i 1 + Pi.single j 1) ∈ S)
    (i j : Fin n) : Q.coeff i j ∈ S := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · have key : Q.coeff i j =
        Q.eval (Pi.single i 1 + Pi.single j 1) - Q.eval (Pi.single i 1) - Q.eval (Pi.single j 1) := by
      rw [QuadForm.eval_polar, Matrix.mulVec_single_one, single_one_dotProduct]
      have hz : Q.coeff j i = 0 := Q.upper (show id i < id j from hij)
      simp [QuadForm.hessian, hz]
    rw [key]
    exact S.sub_mem (S.sub_mem (h2 i j) (h1 i)) (h1 j)
  · rw [← QuadForm.eval_single]; exact h1 i
  · rw [Q.upper (show id j < id i from hij)]; exact S.zero_mem

/-- Over a domain in which $2 \ne 0$, a form is determined by its Hessian. -/
theorem QuadForm.eq_of_hessian_eq {R : Type*} [CommRing R] [IsDomain R] (h2 : (2 : R) ≠ 0) {Q Q' : QuadForm R n}
    (h : Q.hessian = Q'.hessian) : Q = Q' := by
  apply QuadForm.ext
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · have e1 := congrFun (congrFun h i) j
    simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply] at e1
    rwa [Q.upper (show id i < id j from hij), Q'.upper (show id i < id j from hij), add_zero, add_zero] at e1
  · have e1 := congrFun (congrFun h i) i
    simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply, ← two_mul] at e1
    exact mul_left_cancel₀ h2 e1
  · rw [Q.upper (show id j < id i from hij), Q'.upper (show id j < id i from hij)]

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **An $F_{\mathfrak p}$-form with coefficients in $\mathcal O_{\mathfrak p}$, as a form over $\mathcal O_{\mathfrak p}$.** -/
def QuadForm.toO (q : QuadForm Fv n) (h : ∀ i j, q.coeff i j ∈ v.adicCompletionIntegers F) : QuadForm 𝔬 n where
  coeff := Matrix.of fun i j => ⟨q.coeff i j, h i j⟩
  upper := fun _ _ hij => Subtype.ext (q.upper hij)

theorem QuadForm.map_toO (q : QuadForm Fv n) (h : ∀ i j, q.coeff i j ∈ v.adicCompletionIntegers F) :
    (QuadForm.toO v q h).map (algebraMap 𝔬 Fv) = q :=
  QuadForm.ext (by ext i j; rfl)

theorem QuadForm.map_injective_O : Function.Injective (fun T : QuadForm 𝔬 n => T.map (algebraMap 𝔬 Fv)) :=
  fun _ _ h => LocalDensity.NF.map_injective (IsFractionRing.injective 𝔬 Fv) h

/-- **The local forms of an $\mathcal O_F$-valued lattice are $\mathcal O_{\mathfrak p}$-valued**: if $L$ is integral for $Q$ and
$L_{\mathfrak p} = \gamma\,\mathcal O_{\mathfrak p}^n$, then $Q\circ\gamma$ has coefficients in $\mathcal O_{\mathfrak p}$. -/
theorem localForm_coeff_integral (Q : QuadForm F n) (L : Lat F n) (hL : IsIntegral Q L.1)
    {γ : GL (Fin n) Fv} (hγ : loc v L.1 = locAct v γ (std v)) (i j : Fin n) :
    (localForm Q v γ).coeff i j ∈ v.adicCompletionIntegers F := by
  have hval : ∀ x ∈ std v, (localForm Q v γ).eval x ∈ (v.adicCompletionIntegers F).toSubring.toAddSubgroup := by
    intro x hx
    have hmem : γ.val *ᵥ x ∈ loc v L.1 := by rw [hγ]; exact ⟨x, hx, rfl⟩
    have h := valued_evalIn_loc_le_one Q v hL hmem
    rw [localForm, QuadForm.eval_compMat]
    have e : (Q.map (algebraMap F Fv)).eval (γ.val *ᵥ x) = Q.evalIn Fv (γ.val *ᵥ x) := by
      unfold QuadForm.eval QuadForm.evalIn QuadForm.map
      simp
    rw [e]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h
  have hstd : ∀ k : Fin n, (Pi.single k 1 : Fin n → Fv) ∈ std v := fun k => single_one_mem_std v k
  exact coeff_mem_of_eval_single_mem _ _ (fun k => hval _ (hstd k))
    (fun k l => hval _ ((std v).add_mem (hstd k) (hstd l))) i j

/-- **The local genus of $L_{\mathfrak p}$** for an $\mathcal O_F$-valued lattice $L$ on $(F^n, Q)$: the class of the local form
$Q\circ\gamma$ in a basis $\gamma$ of $L_{\mathfrak p}$ (the paper's $L_{\mathfrak p}$ in the localization map $\lambda$ of the proof of
Lemma 3.7). -/
@[kb "hanke2011structure" "Lemma 3.7, proof, p. 13 (the localization map λ)"]
def locGenusOf (Q : QuadForm F n) (L : Lat F n) (hL : IsIntegral Q L.1) : LocGenus v n :=
  LocGenus.mk (QuadForm.toO v (localForm Q v (locBasis v L))
    (localForm_coeff_integral v Q L hL (locBasis_spec v L)))

/-- **Independence of the basis:** any basis $\gamma$ of $L_{\mathfrak p}$ gives the same local genus. -/
theorem locGenusOf_eq (Q : QuadForm F n) (L : Lat F n) (hL : IsIntegral Q L.1) {γ : GL (Fin n) Fv}
    (hγ : loc v L.1 = locAct v γ (std v)) :
    locGenusOf v Q L hL = LocGenus.mk (QuadForm.toO v (localForm Q v γ) (localForm_coeff_integral v Q L hL hγ)) := by
  unfold locGenusOf
  rw [LocGenus.mk_eq_mk, isometricGL_iff_compMat]
  have hstd : locAct v ((locBasis v L)⁻¹ * γ) (std v) = std v := by
    rw [locAct_mul, ← hγ, locBasis_spec, locAct_inv_locAct]
  obtain ⟨P, hP⟩ := exists_gl_o_of_locAct_eq v hstd
  refine ⟨P, QuadForm.map_injective_O v ?_⟩
  simp only
  rw [QuadForm.map_toO, ← QuadForm.map_compMat, QuadForm.map_toO]
  have e : P.val.map (algebraMap 𝔬 Fv) = ((locBasis v L)⁻¹ * γ).val := by
    rw [← hP]; rfl
  rw [e, localForm, localForm, QuadForm.compMat_mul, ← Units.val_mul, mul_inv_cancel_left]

/-- A matrix $g$ with ${}^tgHg = H$ preserves the form: $Q\circ g = Q$ over $F_{\mathfrak p}$. -/
theorem compMat_eq_of_mem_orthGroup (Q : QuadForm F n) {g : GL (Fin n) Fv} (hg : g ∈ orthGroup Q Fv) :
    (Q.map (algebraMap F Fv)).compMat g.val = Q.map (algebraMap F Fv) := by
  apply QuadForm.eq_of_hessian_eq (two_ne_zero)
  rw [QuadForm.hessian_compMat, QuadForm.hessian_map']
  exact hg

/-- Conversely, $Q\circ g = Q$ gives $g \in O(Q)(F_{\mathfrak p})$. -/
theorem mem_orthGroup_of_compMat_eq (Q : QuadForm F n) {g : GL (Fin n) Fv}
    (hg : (Q.map (algebraMap F Fv)).compMat g.val = Q.map (algebraMap F Fv)) : g ∈ orthGroup Q Fv := by
  have h := congrArg QuadForm.hessian hg
  rw [QuadForm.hessian_compMat, QuadForm.hessian_map'] at h
  exact h

/-- **Comparison with the repository's genus.** Two $\mathcal O_F$-valued lattices $L$, $M$ on the same space $(F^n,Q)$ are in
the same genus (`Lattices.SameGenus`: $g_{\mathfrak p}L_{\mathfrak p} = M_{\mathfrak p}$ for some $g_{\mathfrak p} \in O(Q)(F_{\mathfrak p})$, at every
prime) iff they have the same local genus at every prime. -/
@[kb "hanke2011structure" "Lemma 3.7, proof, p. 13 (genera are determined by their localizations)"]
theorem sameGenus_iff_locGenusOf (Q : QuadForm F n) (L M : Lat F n) (hL : IsIntegral Q L.1)
    (hM : IsIntegral Q M.1) :
    Lattices.SameGenus Q L.1 M.1 ↔ ∀ w : HeightOneSpectrum (𝓞 F), locGenusOf w Q L hL = locGenusOf w Q M hM := by
  constructor
  · intro h w
    obtain ⟨g, hg, hgL⟩ := h w
    have hM' : loc w M.1 = locAct w (g * locBasis w L) (std w) := by
      rw [locAct_mul, ← locBasis_spec, hgL]
    rw [locGenusOf_eq w Q M hM hM']
    unfold locGenusOf
    congr 1
    apply QuadForm.map_injective_O w
    simp only
    rw [QuadForm.map_toO, QuadForm.map_toO, localForm, localForm, Units.val_mul, ← QuadForm.compMat_mul,
      compMat_eq_of_mem_orthGroup w Q hg]
  · intro h w
    have hw := h w
    unfold locGenusOf at hw
    rw [LocGenus.mk_eq_mk, isometricGL_iff_compMat] at hw
    obtain ⟨P, hP⟩ := hw
    set P' : GL (Fin n) (w.adicCompletion F) := Matrix.GeneralLinearGroup.map (algebraMap _ _) P with hP'
    have hform : localForm Q w (locBasis w M) = localForm Q w (locBasis w L * P') := by
      have e := congrArg (QuadForm.map (algebraMap (w.adicCompletionIntegers F) (w.adicCompletion F))) hP
      rw [QuadForm.map_toO, ← QuadForm.map_compMat, QuadForm.map_toO] at e
      rw [e, localForm, localForm, Units.val_mul, ← QuadForm.compMat_mul]
      rfl
    -- the isometry `γ_M P'⁻¹ γ_L⁻¹` maps `L_𝔭` onto `M_𝔭`
    set g : GL (Fin n) (w.adicCompletion F) := locBasis w M * P'⁻¹ * (locBasis w L)⁻¹ with hg
    refine ⟨g, mem_orthGroup_of_compMat_eq w Q ?_, ?_⟩
    · have e1 : localForm Q w (locBasis w L) = (Q.map (algebraMap F (w.adicCompletion F))).compMat
          (locBasis w M * P'⁻¹).val := by
        have := congrArg (fun T => T.compMat (P'⁻¹).val) hform
        simp only [localForm, QuadForm.compMat_mul, ← Units.val_mul, mul_inv_cancel_right] at this
        rw [localForm, this]
      have e2 : (Q.map (algebraMap F (w.adicCompletion F))).compMat g.val =
          ((Q.map (algebraMap F (w.adicCompletion F))).compMat (locBasis w M * P'⁻¹).val).compMat
            (locBasis w L)⁻¹.val := by
        rw [QuadForm.compMat_mul, hg, Units.val_mul]
      rw [e2, ← e1, localForm, QuadForm.compMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        QuadForm.compMat_one]
    · rw [locBasis_spec w L, ← locAct_mul, hg, inv_mul_cancel_right, locAct_mul, hP', ← map_inv,
        Lattices.locAct_map_std, ← locBasis_spec]

end Local

/-! ### Part B: the invariants of the local genera of a lattice -/

/-- The diagonal sign vector of signature $(\sigma_+,\sigma_-)$: $1$ at the indices $< \sigma_+$, $-1$ after. -/
def sigVec (K : Type*) [Field K] {m : ℕ} (p : SigPair m) : Fin m → K := fun i => if (i : ℕ) < p.1.1 then 1 else -1

theorem sigVec_ne_zero (K : Type*) [Field K] {m : ℕ} (p : SigPair m) (i : Fin m) : sigVec K p i ≠ 0 := by
  unfold sigVec; split_ifs <;> simp

theorem sum_range_not_lt (m : ℕ) : ∀ N : ℕ, (∑ i ∈ Finset.range N, if i < m then 0 else 1) = N - m
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_range_succ, sum_range_not_lt m N]
    split_ifs with h <;> omega

/-- **The Hasse invariant of a real space of signature $(\sigma_+,\sigma_-)$** (Serre's convention) is
$(-1)^{\sigma_-(\sigma_--1)/2}$ (`hasseReal`). -/
theorem hasseSerre_sigVec (w : InfinitePlace F) (hw : w.IsReal) (p : SigPair n) :
    (NFPlace.infinite w).hasseSerre (sigVec F p) = hasseReal p.1.2 := by
  let φ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have e : (NFPlace.infinite w).hasseSerre (sigVec F p) =
      PadicClass.hasseVec (fun i => algebraMap F w.Completion (sigVec F p i)) := rfl
  rw [e, ← HasseIsoNF.hasseVec_ringEquiv φ]
  have hv : (fun i => φ (algebraMap F w.Completion (sigVec F p i))) = sigVec ℝ p := by
    funext i
    unfold sigVec
    split_ifs
    · rw [map_one, map_one]
    · rw [map_neg, map_one, map_neg, map_one]
  rw [hv, HasseIsoNF.hasseVec_real_eq _ (sigVec_ne_zero ℝ p)]
  have hc : HasseIsoNF.negCountR (sigVec ℝ p) = p.1.2 := by
    unfold HasseIsoNF.negCountR sigVec
    have : (∑ i : Fin n, if (if (i : ℕ) < p.1.1 then (1 : ℝ) else -1) < 0 then 1 else 0) =
        ∑ i : Fin n, if (i : ℕ) < p.1.1 then 0 else 1 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> norm_num at *
    rw [this, Fin.sum_univ_eq_sum_range (fun i => if i < p.1.1 then 0 else 1) n, sum_range_not_lt]
    have := p.2
    omega
  have h2 := HasseIsoNF.two_negPairsR_add (sigVec ℝ p)
  rw [hc] at h2
  have key : p.1.2 * (p.1.2 - 1) = 2 * HasseIsoNF.negPairsR (sigVec ℝ p) := by
    rcases Nat.eq_zero_or_pos p.1.2 with h0 | hpos
    · rw [h0] at h2 ⊢
      simp at h2
      omega
    · have e1 : p.1.2 * (p.1.2 - 1) + p.1.2 = p.1.2 ^ 2 := by
        rw [sq, ← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos]
      omega
  unfold hasseReal
  rw [key, Nat.mul_div_cancel_left _ (by norm_num)]

/-- **$Q$ has the signature vector $\vec\sigma_\infty$** (Remark 3.2): at every real place $w$, $Q \cong
\langle 1^{\sigma_{w,+}}, (-1)^{\sigma_{w,-}}\rangle$ over $F_w$. -/
def HasSignature (Q : QuadForm F n) (σ : SignatureVector F n) : Prop :=
  ∀ w : {w : InfinitePlace F // w.IsReal}, (Q.map (algebraMap F w.1.Completion)).IsometricIn w.1.Completion
    ((QuadForm.diag (sigVec F (σ w))).map (algebraMap F w.1.Completion))

/-- Cassels' Hasse invariant of a diagonal form over $F_{\mathfrak p}$ is $\prod_{i<j}(b_i,b_j)$. -/
theorem hasseC_diag (v : HeightOneSpectrum (𝓞 F)) (b : Fin n → v.adicCompletion F) (hb : ∀ i, b i ≠ 0) :
    Composition.hasseC (QuadForm.diag b) = PadicClass.hasseVec b := by
  classical
  have hnd : (QuadForm.diag b).Nondegenerate := OMeara.nondegenerate_diag b hb
  unfold Composition.hasseC
  simp only [hnd, ↓reduceDIte]
  obtain ⟨hc0, hciso⟩ := Classical.choose_spec (FieldGen.exists_isometric_diag (QuadForm.diag b) hnd)
  exact PadicClass.hasseVec_eq_of_isometric (HasseIsoNF.localHilbertField_adicCompletion v) n _ _ hc0 hb
    (QuadForm.isometricIn_symm _ hciso)

/-- **The local form of $L_{\mathfrak p}$ is isometric over $F_{\mathfrak p}$ to $Q$.** -/
theorem localForm_isometricIn (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm F n) (γ : GL (Fin n) (v.adicCompletion F)) :
    (Q.map (algebraMap F (v.adicCompletion F))).IsometricIn (v.adicCompletion F) (localForm Q v γ) := by
  refine ⟨γ.val, (Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit, fun x => ?_⟩
  unfold localForm
  simp only [QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply]
  have := (QuadForm.eval_compMat (Q.map (algebraMap F (v.adicCompletion F))) γ.val x).symm
  simpa [QuadForm.eval, QuadForm.evalIn] using this

/-- **The Hasse invariant of the local genus of $L_{\mathfrak p}$** is Serre's $\varepsilon_{\mathfrak p}$ of a diagonalization of
$Q$ over $F$. -/
theorem hasse_locGenusOf (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm F n) (L : Lat F n) (hL : IsIntegral Q L.1)
    (a : Fin n → F) (ha : ∀ i, a i ≠ 0) (hQa : Q.IsometricIn F (QuadForm.diag a)) :
    (locGenusOf v Q L hL).hasse = (NFPlace.finite v).hasseSerre a := by
  unfold locGenusOf
  rw [LocGenus.hasse_mk, hasseForm, QuadForm.map_toO]
  have h1 := hasseC_eq_of_isometricIn (v := v) (localForm_isometricIn v Q (locBasis v L))
  have h2 : (Q.map (algebraMap F (v.adicCompletion F))).IsometricIn (v.adicCompletion F)
      (QuadForm.diag fun i => algebraMap F (v.adicCompletion F) (a i)) := by
    rw [← OMeara.map_diag']
    exact OMeara.isometricIn_map_of_isometricIn _ (FieldGen.isometricIn_of_base _ hQa)
  rw [← h1, hasseC_eq_of_isometricIn (v := v) h2, hasseC_diag v _ (fun i => (map_ne_zero _).mpr (ha i))]
  rfl

/-- **The local genus of $L_{\mathfrak p}$ is nondegenerate, with $\det_H = \det_H(L)_{\mathfrak p}$.** -/
theorem det_locGenusOf (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm F n) (hQ : Q.hessian.det ≠ 0) (L : Lat F n)
    (hL : IsIntegral Q L.1) :
    (locGenusOf v Q L hL).Nondeg ∧ (locGenusOf v Q L hL).det = AdelicSqCl.comp v (detH Q hQ L) := by
  classical
  unfold locGenusOf
  rw [LocGenus.nondeg_mk, LocGenus.det_mk, detH_comp Q hQ L v (locBasis_spec v L)]
  set T := QuadForm.toO v (localForm Q v (locBasis v L)) (localForm_coeff_integral v Q L hL (locBasis_spec v L))
  have hdet : algebraMap _ (v.adicCompletion F) T.hessian.det = (localHessDet Q hQ v (locBasis v L) : _) := by
    rw [← det_hessian_localForm Q hQ v, ← QuadForm.map_toO v (localForm Q v (locBasis v L))
      (localForm_coeff_integral v Q L hL (locBasis_spec v L)), QuadForm.hessian_map', ← RingHom.mapMatrix_apply,
      ← RingHom.map_det]
  have hne : algebraMap _ (v.adicCompletion F) T.hessian.det ≠ 0 := by
    rw [hdet]; exact Units.ne_zero _
  refine ⟨(algebraMap_ne_zero_iff (v := v)).mp hne, ?_⟩
  unfold detSqForm
  rw [dite_eq_left hne]
  congr 1
  exact Units.ext hdet

/-- Isometry over $K$ of two $F$-forms is isometry of their base changes. -/
theorem isometricIn_map_iff {K : Type*} [Field K] [Algebra F K] (Q Q' : QuadForm F n) :
    (Q.map (algebraMap F K)).IsometricIn K (Q'.map (algebraMap F K)) ↔ Q.IsometricIn K Q' := by
  unfold QuadForm.IsometricIn
  simp only [OMeara.evalIn_map_algebraMap]

/-- **The product formula for the local genera of a lattice** (proof of Lemma 3.7): for $L$ on $(F^n,Q)$ with $Q$ of
signature $\vec\sigma_\infty$, $c_{\mathfrak p}(L_{\mathfrak p}) = 1$ for almost all $\mathfrak p$ and
$\prod_{\mathfrak p}c_{\mathfrak p}(L_{\mathfrak p}) = \prod_{v\mid\infty}c_v((\vec\sigma_\infty)_v) = \varepsilon_\infty$ (Hilbert reciprocity). -/
@[kb "hanke2011structure" "Lemma 3.7, proof, p. 14 (∏_p c_p(V) = ∏_{v|∞} c_v(V))"]
theorem finprod_hasse_locGenusOf (Q : QuadForm F n) (hQ : Q.hessian.det ≠ 0) (L : Lat F n) (hL : IsIntegral Q L.1)
    (σ : SignatureVector F n) (hσ : HasSignature Q σ) :
    (Function.mulSupport fun v => (locGenusOf v Q L hL).hasse).Finite ∧
      ∏ᶠ v, (locGenusOf v Q L hL).hasse = epsInf σ := by
  classical
  obtain ⟨a, ha, hQa⟩ := FieldGen.exists_isometric_diag Q hQ
  have hv : ∀ v, (locGenusOf v Q L hL).hasse = (NFPlace.finite v).hasseSerre a :=
    fun v => hasse_locGenusOf v Q L hL a ha hQa
  obtain ⟨hsupp, hprod⟩ := NFPlace.hasseSerre_product_formula a ha
  rw [OMeara.finprod_nfPlace _ hsupp] at hprod
  -- the infinite places give `ε∞`
  have hinf : ∏ w : InfinitePlace F, (NFPlace.infinite w).hasseSerre a = epsInf σ := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => w.IsReal)]
    have hc : ∏ w : {w : InfinitePlace F // ¬ w.IsReal}, (NFPlace.infinite w.1).hasseSerre a = 1 := by
      refine Finset.prod_eq_one fun w _ => ?_
      have hw : w.1.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp w.2
      unfold NFPlace.hasseSerre
      refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
      split_ifs
      · exact HasseIsoNF.hilbertSymbol_complex_place hw _ _
      · rfl
    rw [hc, mul_one]
    unfold epsInf
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← hasseSerre_sigVec w.1 w.2 (σ w)]
    refine NFPlace.hasseSerre_isometric (NFPlace.infinite w.1) a _ ha (sigVec_ne_zero F _) ?_
    show (QuadForm.diag a).IsometricIn w.1.Completion (QuadForm.diag (sigVec F (σ w)))
    have h1 : (QuadForm.diag a).IsometricIn w.1.Completion Q :=
      QuadForm.isometricIn_symm _ (FieldGen.isometricIn_of_base _ hQa)
    have h2 := (isometricIn_map_iff Q _).mp (hσ w)
    exact QuadForm.isometricIn_trans _ h1 h2
  rw [hinf] at hprod
  have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 F), (NFPlace.finite v).hasseSerre a = epsInf σ := by
    rcases epsInf_mem σ with h | h <;> rw [h] at hprod ⊢ <;> linarith
  refine ⟨?_, ?_⟩
  · have : (Function.mulSupport fun v => (locGenusOf v Q L hL).hasse) ⊆
        NFPlace.finite ⁻¹' Function.mulSupport (fun v : NFPlace F => v.hasseSerre a) := fun v hv' => by
      simpa [Function.mem_mulSupport, hv] using hv'
    exact (Set.Finite.preimage (fun _ _ _ _ h => NFPlace.finite.inj h) hsupp).subset this
  · simp only [hv]
    exact hfin

/-! ### $\mathrm{Gen}^*$ and $\mathrm{Gen}^*_f$ -/

variable (F n) in
/-- A tuple of local genera, one at each prime of $F$. -/
abbrev LocTuple : Type := ∀ v : HeightOneSpectrum (𝓞 F), LocGenus v n

/-- **$\mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)$** (§1.3, p. 6), as the image of the localization map: the tuples of
local genera $(L_{\mathfrak p})_{\mathfrak p}$ of primitive $\mathcal O_F$-valued lattices $L$ on nondegenerate spaces $(F^n, Q)$ of
signature $\vec\sigma_\infty$, with $\det_H(L) = S$ and $c_{\mathfrak p}(L_{\mathfrak p}) = (\vec c_{\mathbb S})_{\mathfrak p}$ for $\mathfrak p \in \mathbb S$.
(A genus of lattices with fixed signature is determined by its local genera, `sameGenus_iff_locGenusOf`.) -/
@[kb "hanke2011structure" "§1.3, p. 6 (Gen*(S, σ, c; n))"]
def GenStar (S : AdelicSqCl F) (σ : SignatureVector F n) (𝕊 : Set (HeightOneSpectrum (𝓞 F)))
    (c : HeightOneSpectrum (𝓞 F) → ℤ) : Set (LocTuple F n) :=
  {t | ∃ (Q : QuadForm F n) (hQ : Q.hessian.det ≠ 0) (L : Lat F n) (hL : IsIntegral Q L.1),
    HasSignature Q σ ∧ detH Q hQ L = S ∧ (∀ v, (locGenusOf v Q L hL).Prim) ∧
      (∀ v ∈ 𝕊, (locGenusOf v Q L hL).hasse = c v) ∧ (fun v => locGenusOf v Q L hL) = t}

/-- **$\mathrm{Gen}^*_f(S,\varepsilon_\infty,\vec c_{\mathbb S};n)$** (§1.3, p. 6): the tuples $(G_{\mathfrak p})_{\mathfrak p}$ of nondegenerate
primitive local genera with $\det_H(G_{\mathfrak p}) = S_{\mathfrak p}$, $c_{\mathfrak p}(G_{\mathfrak p}) = (\vec c_{\mathbb S})_{\mathfrak p}$ for
$\mathfrak p \in \mathbb S$, $c_{\mathfrak p}(G_{\mathfrak p}) = 1$ for almost all $\mathfrak p$, and $\prod_{\mathfrak p}c_{\mathfrak p}(G_{\mathfrak p}) = \varepsilon_\infty$. -/
@[kb "hanke2011structure" "§1.3, p. 6 (Gen*_f(S, ε∞, c; n))"]
def GenStarF (S : AdelicSqCl F) (ε : ℤ) (𝕊 : Set (HeightOneSpectrum (𝓞 F))) (c : HeightOneSpectrum (𝓞 F) → ℤ) :
    Set (LocTuple F n) :=
  {t | (∀ v, (t v).Nondeg ∧ (t v).Prim ∧ (t v).det = AdelicSqCl.comp v S) ∧ (∀ v ∈ 𝕊, (t v).hasse = c v) ∧
    (Function.mulSupport fun v => (t v).hasse).Finite ∧ ∏ᶠ v, (t v).hasse = ε}

/-- **Lemma 3.7, the localization map** (p. 13): the tuple of local genera of a lattice in
$\mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)$ lies in $\mathrm{Gen}^*_f(S,\varepsilon_\infty,\vec c_{\mathbb S};n)$,
$\varepsilon_\infty = \prod_{v\mid\infty}c_v((\vec\sigma_\infty)_v)$. -/
@[kb "hanke2011structure" "Lemma 3.7, p. 13 (the map λ : Gen* → Gen*_f)"]
theorem genStar_subset_genStarF (S : AdelicSqCl F) (σ : SignatureVector F n) (𝕊 : Set (HeightOneSpectrum (𝓞 F)))
    (c : HeightOneSpectrum (𝓞 F) → ℤ) : GenStar S σ 𝕊 c ⊆ GenStarF S (epsInf σ) 𝕊 c := by
  rintro t ⟨Q, hQ, L, hL, hσ, hS, hprim, hc, rfl⟩
  obtain ⟨hfin, hprod⟩ := finprod_hasse_locGenusOf Q hQ L hL σ hσ
  refine ⟨fun v => ⟨(det_locGenusOf v Q hQ L hL).1, hprim v, ?_⟩, hc, hfin, hprod⟩
  rw [(det_locGenusOf v Q hQ L hL).2, hS]

end

end QuadFormsKB.Hanke2011Structure
