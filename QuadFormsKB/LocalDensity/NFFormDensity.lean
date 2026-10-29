/-
# Densities of forms by forms at every prime of a number field, and of lattices
**Layer:** DVR (equivalence invariance) and number field ($Q, T$ = `QuadForm (𝓞 F) n`, `QuadForm (𝓞 F) r`, a finite
prime $\mathfrak p$ = `v`).

**Proves**
* **Invariance under equivalence** over a DVR: $A_{\pi^k}(Q, T)$ and $\beta_\pi(Q, T)$ depend only on the
  $\mathrm{GL}_n(R)$-class of $Q$ and the $\mathrm{GL}_r(R)$-class of $T$ (`DVR.repCountForm_congr_left`,
  `DVR.repCountForm_congr_right`): $X \mapsto gX$ and $X \mapsto Xh$.
* Over $\mathcal O_F$: `NF.repCountForm v Q T k` $= A_{\mathfrak p^k}(Q, T)$ (matrices over $\mathcal O_F/\mathfrak p^k$) and
  `NF.localDensityForm v Q T` $= \beta_\mathfrak p(Q, T) = \lim_k A_{\mathfrak p^k}/N\mathfrak p^{k(nr - r(r+1)/2)}$ agree with the
  DVR objects at the completion $\mathfrak o_\mathfrak p$ (`repCountForm_eq_completion`, `localDensityForm_eq_completion`);
  stabilization for $k \ge 2\,\mathrm{ord}_\mathfrak p \det H_T + 1$ and existence of the limit at **every** $\mathfrak p$,
  dyadic included (`repCountForm_succ`, `localDensityForm_eventually_eq`); the self-density
  (`localDensityForm_self_eventually_eq`); the bridge $\beta_\mathfrak p(Q, \langle m\rangle) = \beta_\mathfrak p(m)$
  (`localDensityForm_unary`).
* **Genus invariance:** forms in the same genus (`Lattices.FormSameGenus`) have the same densities at every
  $\mathfrak p$, in either argument (`localDensityForm_formSameGenus_left/right`).
* **Lattices:** for integral free lattices $L = \gamma\mathcal O_F^n \subset (F^n, Q)$ and
  $M = \delta\mathcal O_F^r \subset (F^r, Q')$,
  `latDensity` $\beta_\mathfrak p(L, M)$ is the density of their Gram forms; it depends only on the genera of $L$ and $M$
  (`latDensity_sameGenus_left/right`), in particular not on the bases. Free lattices are the locally free case;
  for a non-free $L$ the same definition applies to a basis of the free $\mathfrak o_\mathfrak p$-module $L_\mathfrak p$ (not
  formalized).
**Depends on** `FormDensitySelf.lean`, `NFLocal.lean`, `NFLocalGeneral.lean` (`NF.det_hessian_Qp`),
`Lattices/FreeBridge.lean`.
-/
import QuadFormsKB.LocalDensity.FormDensitySelf
import QuadFormsKB.LocalDensity.NFLocal
import QuadFormsKB.LocalDensity.NFLocalGeneral
import QuadFormsKB.Lattices.FreeBridge

open NumberField IsDedekindDomain Filter Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.LocalDensity

open QuadForm

/-! ### Invariance under equivalence over a DVR -/

namespace DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n r : ℕ}

theorem compMat_eq_of_isometricGL {A : Type*} [CommRing A] {Q Q' : QuadForm A n}
    {g : GL (Fin n) A} (hg : ∀ x, Q.eval (g.val *ᵥ x) = Q'.eval x) : Q.compMat g.val = Q' :=
  eq_of_eval_eq fun y => by rw [eval_compMat, hg]

/-- **$A_{\pi^k}(Q, T)$ depends only on the $\mathrm{GL}_n(R)$-class of $Q$**: if $Q' = Q \circ g$ then $X \mapsto gX$ is a
bijection of representations. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem repCountForm_congr_left {Q Q' : QuadForm R n} (h : Siegel.IsometricGL Q Q') (T : QuadForm R r)
    (π : R) (k : ℕ) : repCountForm Q T π k = repCountForm Q' T π k := by
  obtain ⟨g, hg⟩ := h
  set f := Ideal.Quotient.mk (Ideal.span {π ^ k})
  set gb := GeneralLinearGroup.map f g
  have hQ' : Q'.map f = (Q.map f).compMat gb.val := by
    rw [← compMat_eq_of_isometricGL hg, ← map_compMat]; rfl
  unfold repCountForm
  refine Nat.card_congr (Equiv.subtypeEquiv
    { toFun := fun X => gb⁻¹.val * X
      invFun := fun Y => gb.val * Y
      left_inv := fun X => by dsimp only; rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul]
      right_inv := fun Y => by dsimp only; rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul] } fun X => ?_)
  show _ ↔ (Q'.map f).compMat (gb⁻¹.val * X) = _
  rw [hQ', compMat_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

/-- **$A_{\pi^k}(Q, T)$ depends only on the $\mathrm{GL}_r(R)$-class of $T$**: if $T' = T \circ h$ then $X \mapsto Xh$ is a
bijection of representations. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem repCountForm_congr_right (Q : QuadForm R n) {T T' : QuadForm R r} (h : Siegel.IsometricGL T T')
    (π : R) (k : ℕ) : repCountForm Q T π k = repCountForm Q T' π k := by
  obtain ⟨g, hg⟩ := h
  set f := Ideal.Quotient.mk (Ideal.span {π ^ k})
  set gb := GeneralLinearGroup.map f g
  have hT' : T'.map f = (T.map f).compMat gb.val := by
    rw [← compMat_eq_of_isometricGL hg, ← map_compMat]; rfl
  unfold repCountForm
  refine Nat.card_congr (Equiv.subtypeEquiv
    { toFun := fun X => X * gb.val
      invFun := fun Y => Y * gb⁻¹.val
      left_inv := fun X => by dsimp only; rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.mul_one]
      right_inv := fun Y => by dsimp only; rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.mul_one] } fun X => ?_)
  show _ ↔ (Q.map f).compMat (X * gb.val) = T'.map f
  rw [hT', ← compMat_mul]
  constructor
  · intro hX; rw [hX]
  · intro hX
    have := congrArg (fun S => S.compMat gb⁻¹.val) hX
    simp only [compMat_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one, compMat_one] at this
    exact this

theorem localDensityForm_congr_left {Q Q' : QuadForm R n} (h : Siegel.IsometricGL Q Q')
    (T : QuadForm R r) (π : R) : localDensityForm Q T π = localDensityForm Q' T π := by
  simp only [localDensityForm, repCountForm_congr_left h T π]

theorem localDensityForm_congr_right (Q : QuadForm R n) {T T' : QuadForm R r}
    (h : Siegel.IsometricGL T T') (π : R) : localDensityForm Q T π = localDensityForm Q T' π := by
  simp only [localDensityForm, repCountForm_congr_right Q h π]

end DVR

/-! ### Over $\mathcal O_F$ at a finite prime -/

namespace NF

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n r : ℕ}

local notation "𝔬" => v.adicCompletionIntegers F
local notation "N𝔭" => (Ideal.absNorm v.asIdeal : ℝ)

/-- **$A_{\mathfrak p^k}(Q, T)$ over $\mathcal O_F$:** the number of $X \in M_{n\times r}(\mathcal O_F/\mathfrak p^k)$ with
$Q \circ X = T$ as quadratic forms over $\mathcal O_F/\mathfrak p^k$ (Siegel 1935; Kitaoka 1993, §5.6 [unverified]). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
def repCountForm (Q : QuadForm (𝓞 F) n) (T : QuadForm (𝓞 F) r) (k : ℕ) : ℕ :=
  Nat.card {X : Matrix (Fin n) (Fin r) (𝓞 F ⧸ v.asIdeal ^ k) //
    (Q.map (Ideal.Quotient.mk _)).compMat X = T.map (Ideal.Quotient.mk _)}

/-- **$\beta_\mathfrak p(Q, T)$ over $\mathcal O_F$** $= \lim_k A_{\mathfrak p^k}(Q, T)/N\mathfrak p^{k(nr - r(r+1)/2)}$ (Siegel 1935; Kitaoka
1993, §5.6 [unverified]); no factor $\tfrac12$ (that is `siegelDensity`). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
def localDensityForm (Q : QuadForm (𝓞 F) n) (T : QuadForm (𝓞 F) r) : ℝ :=
  limUnder atTop fun k : ℕ => (repCountForm v Q T k : ℝ) / N𝔭 ^ (k * (n * r - r * (r + 1) / 2))

/-- **Siegel's normalization** $\alpha_\mathfrak p(Q, T) = \varepsilon\,\beta_\mathfrak p(Q, T)$, $\varepsilon = \tfrac12$ if $n = r$, else $1$
[unverified]. For $T = Q$ it is $\mathrm{vol}(SO(L_\mathfrak p))$ (`Tamagawa.volSO_eq`). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
def siegelDensity (Q : QuadForm (𝓞 F) n) (T : QuadForm (𝓞 F) r) : ℝ :=
  (if n = r then (1 / 2 : ℝ) else 1) * localDensityForm v Q T

theorem map_injective {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B} (hf : Function.Injective f)
    {S S' : QuadForm A r} (h : S.map f = S'.map f) : S = S' := by
  ext i j
  exact hf (by simpa [QuadForm.map] using congrArg (fun U : QuadForm B r => U.coeff i j) h)

theorem map_mk_quotEquiv (k : ℕ) (S : QuadForm (𝓞 F) r) :
    (S.map (Ideal.Quotient.mk (v.asIdeal ^ k))).map (quotEquiv v k).toRingHom =
      (Qp v S).map (Ideal.Quotient.mk _) := by
  ext i j
  simp [QuadForm.map]

/-- **Counts over $\mathcal O_F/\mathfrak p^k$ equal counts over $\mathfrak o_\mathfrak p/\varpi^k$:**
$A_{\mathfrak p^k}(Q, T) = A_{\varpi^k}(Q \otimes \mathfrak o_\mathfrak p, T \otimes \mathfrak o_\mathfrak p)$. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem repCountForm_eq_completion (Q : QuadForm (𝓞 F) n) (T : QuadForm (𝓞 F) r) (k : ℕ) :
    repCountForm v Q T k = DVR.repCountForm (Qp v Q) (Qp v T) (π v) k := by
  unfold repCountForm DVR.repCountForm
  let φ := quotEquiv v k
  refine Nat.card_congr (Equiv.subtypeEquiv
    { toFun := fun X => X.map φ.toRingHom
      invFun := fun Y => Y.map φ.symm.toRingHom
      left_inv := fun X => by ext i j; simp
      right_inv := fun Y => by ext i j; simp } fun X => ?_)
  show _ ↔ ((Qp v Q).map (Ideal.Quotient.mk _)).compMat (X.map φ.toRingHom) = _
  rw [← map_mk_quotEquiv v k Q, ← map_mk_quotEquiv v k T, map_compMat]
  exact ⟨fun h => by rw [h], fun h => map_injective φ.injective h⟩

theorem localDensityForm_eq_completion (Q : QuadForm (𝓞 F) n) (T : QuadForm (𝓞 F) r) :
    localDensityForm v Q T = DVR.localDensityForm (Qp v Q) (Qp v T) (π v) := by
  simp only [localDensityForm, DVR.localDensityForm, repCountForm_eq_completion, q_completion]

/-- **Stabilization over $\mathcal O_F$** (Siegel 1935, Hilfssatz 13 [unverified]): if $\det H_T \in \mathfrak p^d \setminus
\mathfrak p^{d+1}$ and $k \ge 2d + 1$, then $A_{\mathfrak p^{k+1}}(Q, T)\, N\mathfrak p^{r(r+1)/2} = N\mathfrak p^{nr} A_{\mathfrak p^k}(Q, T)$. Every
finite prime, dyadic included. -/
@[kb "siegel1935" "Hilfssatz 13 [unverified]"]
theorem repCountForm_succ (Q : QuadForm (𝓞 F) n) (T : QuadForm (𝓞 F) r) (d k : ℕ)
    (hd : T.hessian.det ∈ v.asIdeal ^ d) (hd' : T.hessian.det ∉ v.asIdeal ^ (d + 1)) (hk : 2 * d + 1 ≤ k) :
    repCountForm v Q T (k + 1) * Ideal.absNorm v.asIdeal ^ (r * (r + 1) / 2) =
      Ideal.absNorm v.asIdeal ^ (n * r) * repCountForm v Q T k := by
  rw [repCountForm_eq_completion, repCountForm_eq_completion, ← q_completion]
  exact DVR.repCountForm_succ (Qp v Q) (Qp v T) (π v) (irreducible_π v) d k
    (by rw [det_hessian_Qp, π_pow_dvd_ι_iff]; exact hd)
    (by rw [det_hessian_Qp, π_pow_dvd_ι_iff]; exact hd') hk

/-- **Existence of $\beta_\mathfrak p(Q, T)$** for nondegenerate $T$ and $r \le n$, at every finite prime $\mathfrak p$ of $F$
(Siegel 1935; Kitaoka 1993, §5.6 [unverified]). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_eventually_eq (Q : QuadForm (𝓞 F) n) (T : QuadForm (𝓞 F) r) (hT : T.Nondegenerate)
    (hrn : r ≤ n) :
    ∀ᶠ k in atTop, (repCountForm v Q T k : ℝ) / N𝔭 ^ (k * (n * r - r * (r + 1) / 2)) =
      localDensityForm v Q T := by
  have h := DVR.localDensityForm_eventually_eq (Qp v Q) (Qp v T) (nondegenerate_Qp v hT) (π v)
    (irreducible_π v) hrn
  simpa only [← repCountForm_eq_completion, q_completion, ← localDensityForm_eq_completion] using h

/-- **Existence of the self-density** $\beta_\mathfrak p(Q, Q)$ for nondegenerate $Q$ (exponent $n(n-1)/2$). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_self_eventually_eq (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) :
    ∀ᶠ k in atTop, (repCountForm v Q Q k : ℝ) / N𝔭 ^ (k * (n * (n - 1) / 2)) = localDensityForm v Q Q := by
  have h := localDensityForm_eventually_eq v Q Q hQ le_rfl
  simpa only [DVR.self_exp] using h

theorem Qp_unaryForm (m : 𝓞 F) : Qp v (DVR.unary m) = DVR.unary (ι v m) := by
  ext i j
  simp [QuadForm.map, DVR.unary, QuadForm.diag, Matrix.diagonal_apply]

/-- **The bridge to densities of numbers over $\mathcal O_F$:** $\beta_\mathfrak p(Q, \langle m\rangle) = \beta_\mathfrak p(Q, m)$
(`NF.localDensity`). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_unary (Q : QuadForm (𝓞 F) n) (m : 𝓞 F) :
    localDensityForm v Q (DVR.unary m) = localDensity v Q m := by
  rw [localDensityForm_eq_completion, Qp_unaryForm, DVR.localDensityForm_unary, localDensity_eq_completion]

/-- **Densities are genus invariants in $Q$:** if $Q \sim Q'$ (same genus over $\mathcal O_F$) then
$\beta_\mathfrak p(Q, T) = \beta_\mathfrak p(Q', T)$ for every $\mathfrak p$. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_formSameGenus_left {Q Q' : QuadForm (𝓞 F) n} (h : Lattices.FormSameGenus Q Q')
    (T : QuadForm (𝓞 F) r) : localDensityForm v Q T = localDensityForm v Q' T := by
  rw [localDensityForm_eq_completion, localDensityForm_eq_completion]
  exact DVR.localDensityForm_congr_left (h.1 v) _ _

/-- **Densities are genus invariants in $T$.** -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_formSameGenus_right (Q : QuadForm (𝓞 F) n) {T T' : QuadForm (𝓞 F) r}
    (h : Lattices.FormSameGenus T T') : localDensityForm v Q T = localDensityForm v Q T' := by
  rw [localDensityForm_eq_completion, localDensityForm_eq_completion]
  exact DVR.localDensityForm_congr_right _ (h.1 v) _

/-! ### Densities of lattices -/

open Lattices in
/-- **The local density of lattices** $\beta_\mathfrak p(L, M)$ for integral free lattices $L = \gamma\mathcal O_F^n$ in
$(F^n, Q)$ and $M = \delta\mathcal O_F^r$ in $(F^r, Q')$: the density of their Gram forms
(`Lattices.gramZ`). It depends only on the genera of $L$ and $M$ (`latDensity_sameGenus_left/right`). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
def latDensity (Q : QuadForm F n) (Q' : QuadForm F r) (γ : GL (Fin n) F) (hγ : IsIntegral Q (latOf γ))
    (δ : GL (Fin r) F) (hδ : IsIntegral Q' (latOf δ)) : ℝ :=
  localDensityForm v (gramZ Q γ hγ) (gramZ Q' δ hδ)

open Lattices in
/-- **$\beta_\mathfrak p(L, M)$ depends only on the genus of $L$** (in particular not on the basis $\gamma$). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem latDensity_sameGenus_left (Q : QuadForm F n) (Q' : QuadForm F r) {γ γ' : GL (Fin n) F}
    (hγ : IsIntegral Q (latOf γ)) (hγ' : IsIntegral Q (latOf γ')) (h : SameGenus Q (latOf γ) (latOf γ'))
    (δ : GL (Fin r) F) (hδ : IsIntegral Q' (latOf δ)) :
    latDensity v Q Q' γ hγ δ hδ = latDensity v Q Q' γ' hγ' δ hδ :=
  localDensityForm_formSameGenus_left v ((sameGenus_latOf_iff Q γ γ' hγ hγ').mp h) _

open Lattices in
/-- **$\beta_\mathfrak p(L, M)$ depends only on the genus of $M$.** -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem latDensity_sameGenus_right (Q : QuadForm F n) (Q' : QuadForm F r) (γ : GL (Fin n) F)
    (hγ : IsIntegral Q (latOf γ)) {δ δ' : GL (Fin r) F} (hδ : IsIntegral Q' (latOf δ))
    (hδ' : IsIntegral Q' (latOf δ')) (h : SameGenus Q' (latOf δ) (latOf δ')) :
    latDensity v Q Q' γ hγ δ hδ = latDensity v Q Q' γ hγ δ' hδ' :=
  localDensityForm_formSameGenus_right v _ ((sameGenus_latOf_iff Q' δ δ' hδ hδ').mp h)

open Lattices in
/-- **Basis independence:** two bases of the same free lattice give the same density. -/
theorem latDensity_basis_indep (Q : QuadForm F n) (Q' : QuadForm F r) {γ γ' : GL (Fin n) F}
    (hγ : IsIntegral Q (latOf γ)) (hγ' : IsIntegral Q (latOf γ')) (h : latOf γ = latOf γ')
    (δ : GL (Fin r) F) (hδ : IsIntegral Q' (latOf δ)) :
    latDensity v Q Q' γ hγ δ hδ = latDensity v Q Q' γ' hγ' δ hδ :=
  latDensity_sameGenus_left v Q Q' hγ hγ' (h ▸ SameGenus.refl Q _) δ hδ

end NF

end QuadFormsKB.LocalDensity
