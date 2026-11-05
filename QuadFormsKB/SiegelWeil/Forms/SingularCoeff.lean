/-
# The degenerate Fourier coefficients: Siegel's $\Phi$-operator induction
**Layer:** global over a totally real number field $F$ whose ring of integers $\mathcal O_F$ is a principal ideal domain (class
number one, `NumberField.classNumber_eq_one_iff`); analysis on $\mathbb H_r^d$ and linear algebra, no arithmetic input.

**Setting.** A *family of Fourier expansions*: for every degree $r \ge 0$ a coefficient function $c_r$ on the forms $T$ in $r$ variables over
$F$. Degree $0$ is allowed: the unique form in $0$ variables has Gram determinant $1$ (the empty determinant), so it counts as
nonsingular. The new variable of Siegel's $\Phi$ operator is the first one (index $0$), `extZero` (`FourierPhi.lean`).

**Results.**
* `coeff_eq_zero_of_singular`: if $c(T[U]) = c(T)$ for $U \in \mathrm{SL}_{r+1}(\mathcal O_F)$ and $c$ vanishes on every `extZero T'`, then
  $c(T) = 0$ for every singular $T$ (`exists_SL_int_compMat_eq_extZero`).
* **`coeff_family_eq_zero`** (the coefficient form of Siegel's argument): a family $(c_r)_{r\ge0}$ with (a) $c_r(T[U]) = c_r(T)$ for
  $U \in \mathrm{SL}_r(\mathcal O_F)$, (b) $c_{r+1}(\mathrm{extZero}\,T') = c_r(T')$, (c) $c_r(T) = 0$ whenever $\det T_G \ne 0$, all for $r \le R$, is identically $0$ in the degrees $r \le R$.
* `coeff_phi_eq`: for an absolutely convergent expansion $f_{r+1} = \sum_Tc_{r+1}(T)e_T$ supported on totally positive semidefinite $T$
  with $\Phi f_{r+1} = f_r = \sum_{T'}c_r(T')e_{T'}$, (b) holds (`tendsto_phi`, `fourier_coeff_unique`).
* **`family_eq_of_coeff_full_rank`** (**the Siegel–Weil assembly principle**): two families of functions $f_r$, $g_r$ on $\mathbb H_r^d$
  ($0 \le r \le R$; `IsPhiFamily R`), each with absolutely convergent Fourier expansions supported on totally positive semidefinite forms, invariant under
  $Z \mapsto U\cdot Z$ for $U \in \mathrm{SL}_r(\mathcal O_F)$ and compatible with $\Phi$ ($f_{r+1}(Z \oplus it) \to f_r(Z)$, $t \to \infty$), whose
  Fourier coefficients agree at every nonsingular $T$ (every degree, $r = 0$ included), are equal in every degree.
* **`eq_thetaGenR_of_coeff_full_rank`**: the case $g_r = \theta^{(r)}_{\mathrm{gen}(L)}$ (`ThetaR.lean`, `ThetaPhi.lean`, `FourierPhi.lean`): a family
  $f_r$ as above whose nonsingular coefficients are Siegel's $\mathrm{repMassT}(L, T)/\mathrm{Mass}(L)$ is the genus theta series in
  every degree.

In the Siegel–Weil formula this is applied to $f_r(Z) = \det(\operatorname{Im}Z)^{-m/2}E^{(r)}(g_Z, s_0, \Phi)$: the nonsingular coefficients
come from the unfolding (`EisensteinUnfold.lean`) and the local Whittaker integrals; invariance is `eisensteinR_actU`
(`EisensteinSLInv.lean`); the Fourier expansion of $E$ and $\Phi E^{(r+1)} = E^{(r)}$ are the remaining Eisenstein-side inputs.

Sources: Siegel, *Einführung in die Theorie der Modulfunktionen n-ten Grades*, Math. Ann. 116 (1939) (the operator $\Phi$)
[unverified]; Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I (degenerate Fourier coefficients) [unverified]; Weil,
*Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.SingularRadical

open Matrix NumberField Complex Filter Topology
open QuadFormsKB.HilbertModular

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- $U \in \mathrm{SL}_r(\mathcal O_F)$, as a matrix over $F$: $U$ and $U^{-1}$ integral, $\det U = 1$. -/
def IsSLIntMat {r : ℕ} (U : Matrix (Fin r) (Fin r) F) : Prop := IsIntegralMat U ∧ IsIntegralMat U⁻¹ ∧ U.det = 1

/-- **Singular coefficients vanish** once $c$ is $\mathrm{SL}_{r+1}(\mathcal O_F)$-invariant and zero on forms without the variable $0$. -/
theorem coeff_eq_zero_of_singular [IsPrincipalIdealRing (𝓞 F)] {r : ℕ} {c : QuadForm F (r + 1) → ℂ}
    (hinv : ∀ U, IsSLIntMat U → ∀ T, c (T.compMat U) = c T) (hext : ∀ T', c (extZero T') = 0)
    {T : QuadForm F (r + 1)} (hT : (gramT T).det = 0) : c T = 0 := by
  obtain ⟨U, h1, h2, h3, h4⟩ := exists_SL_int_compMat_eq_extZero T hT
  rw [← hinv U ⟨h1, h2, h3⟩ T, h4, hext]

/-- **The coefficient form of Siegel's argument** (up to the degree $R$): an $\mathrm{SL}_r(\mathcal O_F)$-invariant, $\Phi$-compatible
family of coefficient functions vanishing at every nonsingular form vanishes identically in every degree $r \le R$. -/
theorem coeff_family_eq_zero [IsPrincipalIdealRing (𝓞 F)] (R : ℕ) (c : ∀ r : ℕ, QuadForm F r → ℂ)
    (hinv : ∀ r ≤ R, ∀ U, IsSLIntMat U → ∀ T : QuadForm F r, c r (T.compMat U) = c r T)
    (hphi : ∀ r, r + 1 ≤ R → ∀ T' : QuadForm F r, c (r + 1) (extZero T') = c r T')
    (hfull : ∀ r ≤ R, ∀ T : QuadForm F r, (gramT T).det ≠ 0 → c r T = 0) :
    ∀ r ≤ R, ∀ T : QuadForm F r, c r T = 0 := by
  intro r
  induction r with
  | zero => intro _ T; exact hfull 0 (Nat.zero_le _) T (by simp)
  | succ r ih =>
    intro hr T
    by_cases hT : (gramT T).det = 0
    · exact coeff_eq_zero_of_singular (hinv (r + 1) hr) (fun T' => by rw [hphi r hr, ih (by omega)]) hT
    · exact hfull _ hr T hT

/-! ### From functions to coefficients -/

/-- **$\Phi$ at the level of coefficients**: if $f_{r+1} = \sum_Tc(T)e_T$ (absolutely, $c$ supported on totally positive semidefinite $T$)
and $f_{r+1}(Z \oplus it) \to \sum_{T'}c'(T')e_{T'}(Z)$ (absolutely convergent), then $c(\mathrm{extZero}\,T') = c'(T')$. -/
theorem coeff_phi_eq {r : ℕ} {c : QuadForm F (r + 1) → ℂ} {c' : QuadForm F r → ℂ}
    (hc : ∀ Z ∈ siegelHF F (r + 1), Summable fun T => ‖c T * eT T Z‖)
    (hpsd : ∀ T, c T ≠ 0 → IsTotPSD T)
    (hc' : ∀ Z ∈ siegelHF F r, Summable fun T => ‖c' T * eT T Z‖)
    (hphi : ∀ Z ∈ siegelHF F r, Tendsto (fun t : ℝ => ∑' T, c T * eT T (blockZ Z t)) atTop
      (𝓝 (∑' T', c' T' * eT T' Z)))
    (T' : QuadForm F r) : c (extZero T') = c' T' := by
  have hext : ∀ (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (T' : QuadForm F r),
      eT (extZero T') (blockZ Z 1) = eT T' Z := by
    intro Z T'
    have h0 : gramT (extZero T') 0 0 = 0 := by simp [gramT, QuadForm.hessian, extZero]
    rw [eT_blockZ_form, h0, tailForm_extZero]
    simp
  have hs : ∀ Z ∈ siegelHF F r, Summable fun T' : QuadForm F r => ‖c (extZero T') * eT T' Z‖ := by
    intro Z hZ
    have := (hc _ (blockZ_mem hZ one_pos)).comp_injective extZero_injective
    refine this.congr fun T' => ?_
    simp only [Function.comp_apply, hext]
  have h := fourier_coeff_unique (a := fun T' => c (extZero T')) hs hc' fun Z hZ =>
    tendsto_nhds_unique (tendsto_phi hc hpsd hZ) (hphi Z hZ)
  exact congrFun h T'

/-- **A $\Phi$-family up to the degree $R$**: for every $r \le R$, absolute convergence of $f_r = \sum_Ta_r(T)e_T$ on $\mathbb H_r^d$
(`summable`, `hasSum`), support of $a_r$ on totally positive semidefinite forms (`psd`), invariance of $f_r$ under $Z \mapsto U\cdot Z$ for
$U \in \mathrm{SL}_r(\mathcal O_F)$ (`inv`), and Siegel's $\Phi$ for $r + 1 \le R$: $f_{r+1}(Z \oplus it) \to f_r(Z)$ as $t \to \infty$, the new
variable having index $0$ (`phi`). -/
structure IsPhiFamily (R : ℕ) (a : ∀ r : ℕ, QuadForm F r → ℂ)
    (f : ∀ r : ℕ, (InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) → ℂ) : Prop where
  summable : ∀ r ≤ R, ∀ Z ∈ siegelHF F r, Summable fun T => ‖a r T * eT T Z‖
  hasSum : ∀ r ≤ R, ∀ Z ∈ siegelHF F r, HasSum (fun T => a r T * eT T Z) (f r Z)
  psd : ∀ r ≤ R, ∀ T, a r T ≠ 0 → IsTotPSD T
  inv : ∀ r ≤ R, ∀ U : Matrix (Fin r) (Fin r) F, IsSLIntMat U → ∀ Z ∈ siegelHF F r, f r (actU U Z) = f r Z
  phi : ∀ r, r + 1 ≤ R → ∀ Z ∈ siegelHF F r, Tendsto (fun t : ℝ => f (r + 1) (blockZ Z t)) atTop (𝓝 (f r Z))

lemma IsPhiFamily.coeff_inv {R : ℕ} {a : ∀ r : ℕ, QuadForm F r → ℂ}
    {f : ∀ r : ℕ, (InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) → ℂ}
    (h : IsPhiFamily R a f) {r : ℕ} (hr : r ≤ R) (U : Matrix (Fin r) (Fin r) F) (hU : IsSLIntMat U) (T : QuadForm F r) :
    a r (T.compMat U) = a r T :=
  coeff_compMat_eq (h.summable r hr) (h.hasSum r hr) (by rw [hU.2.2]; exact one_ne_zero) (h.inv r hr U hU) T

lemma IsPhiFamily.coeff_phi {R : ℕ} {a : ∀ r : ℕ, QuadForm F r → ℂ}
    {f : ∀ r : ℕ, (InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) → ℂ}
    (h : IsPhiFamily R a f) {r : ℕ} (hr : r + 1 ≤ R) (T' : QuadForm F r) : a (r + 1) (extZero T') = a r T' := by
  have hr' : r ≤ R := by omega
  refine coeff_phi_eq (h.summable (r + 1) hr) (h.psd (r + 1) hr) (h.summable r hr') (fun Z hZ => ?_) T'
  rw [(h.hasSum r hr' Z hZ).tsum_eq]
  refine (h.phi r hr Z hZ).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact ((h.hasSum (r + 1) hr _ (blockZ_mem hZ ht)).tsum_eq).symm

/-- **The Siegel–Weil assembly principle** ($\mathcal O_F$ a principal ideal domain): two $\Phi$-families up to the degree $R$ whose
coefficients agree at every nonsingular form (in every degree $r \le R$, $r = 0$ included) are equal on $\mathbb H_r^d$ for every $r \le R$. -/
@[kb "freitag1983" "Ch. I (a Siegel modular form is determined by its Φ-images and its nonsingular Fourier coefficients) [unverified]"]
theorem family_eq_of_coeff_full_rank [IsPrincipalIdealRing (𝓞 F)] {R : ℕ} {a b : ∀ r : ℕ, QuadForm F r → ℂ}
    {f g : ∀ r : ℕ, (InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) → ℂ} (hf : IsPhiFamily R a f) (hg : IsPhiFamily R b g)
    (hfull : ∀ r ≤ R, ∀ T : QuadForm F r, (gramT T).det ≠ 0 → a r T = b r T) :
    ∀ r ≤ R, ∀ Z ∈ siegelHF F r, f r Z = g r Z := by
  have h0 := coeff_family_eq_zero R (fun r T => a r T - b r T)
    (fun r hr U hU T => by simp only [hf.coeff_inv hr U hU, hg.coeff_inv hr U hU])
    (fun r hr T' => by simp only [hf.coeff_phi hr, hg.coeff_phi hr])
    (fun r hr T hT => by simp only [hfull r hr T hT, sub_self])
  intro r hr Z hZ
  have hab : a r = b r := funext fun T => sub_eq_zero.mp (h0 r hr T)
  rw [← (hf.hasSum r hr Z hZ).tsum_eq, ← (hg.hasSum r hr Z hZ).tsum_eq, hab]

/-! ### The genus theta series is a $\Phi$-family -/

section Theta

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Frames

variable {n : ℕ}

/-- $Q[X]$ is totally positive semidefinite for $Q$ totally positive definite. -/
lemma isTotPSD_compMat {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) {r : ℕ} (X : Matrix (Fin n) (Fin r) F) :
    IsTotPSD (Q.compMat X) := by
  intro v
  rw [gramT_compMat]
  set φ := realEmb F v
  have e : (Xᵀ * gramT Q * X).map φ = (X.map φ)ᴴ * (gramT Q).map φ * X.map φ := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.transpose_map]
    exact Matrix.map_mul.trans (by rw [Matrix.map_mul])
  rw [e]
  exact (posDef_gramT hQ v).posSemidef.conjTranspose_mul_mul_same _

/-- Siegel's weighted representation numbers vanish off the totally positive semidefinite forms. -/
lemma isTotPSD_of_repMassT_ne_zero {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (L : Lat F n) {r : ℕ}
    {T : QuadForm F r} (h : repMassT Q L T ≠ 0) : IsTotPSD T := by
  by_contra hT
  apply h
  unfold repMassT
  refine finsum_mem_eq_zero_of_forall_eq_zero fun c _ => ?_
  rw [latClass_repCountT_eq]
  have : repCountT Q c.out T = 0 := by
    unfold repCountT
    rw [Nat.card_eq_zero]
    left
    exact ⟨fun X => hT (X.2.2 ▸ isTotPSD_compMat hQ X.1)⟩
  simp [this]

/-- **The genus theta series is a $\Phi$-family** (up to every degree $R$), with coefficients $\mathrm{repMassT}(L, T)/\mathrm{Mass}(L)$. -/
theorem isPhiFamily_thetaGenR {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (L : Lat F n) (hLi : IsIntegral Q L.1) (R : ℕ) :
    IsPhiFamily R (fun _ T => ((repMassT Q L T / mass Q L : ℝ) : ℂ)) (fun r => thetaGenR (r := r) Q L) where
  summable _ _ Z hZ := summable_norm_thetaGenR_coeff hQ L hLi hZ
  hasSum _ _ Z hZ := hasSum_thetaGenR hQ L hLi hZ
  psd _ _ T hT := isTotPSD_of_repMassT_ne_zero hQ L fun h => hT (by simp [h])
  inv _ _ U hU Z _ := by
    have hdet : U.det ≠ 0 := by rw [hU.2.2]; exact one_ne_zero
    exact thetaGenR_actU Q L hU.1 hU.2.1 hdet Z
  phi _ _ Z hZ := tendsto_thetaGenR_blockZ hQ L hLi hZ

/-- **A $\Phi$-family with Siegel's nonsingular coefficients is the genus theta series** ($\mathcal O_F$ a principal ideal domain): if
$f_r = \sum_Ta_r(T)e_T$ is a $\Phi$-family up to the degree $R$ (`IsPhiFamily`) and $a_r(T) = \mathrm{repMassT}(L, T)/\mathrm{Mass}(L)$ for
every $T$ with $\det T_G \ne 0$ (every $r \le R$, $r = 0$ included), then $f_r = \theta^{(r)}_{\mathrm{gen}(L)}$ on $\mathbb H_r^d$ for every
$r \le R$. For the Siegel–Weil formula, $f_r = \det(\operatorname{Im}Z)^{-m/2}E^{(r)}(g_Z, s_0, \Phi)$ normalized by the Weil constants. -/
@[kb "weil1965" "Ch. II–IV (the Siegel–Weil formula by comparison of Fourier coefficients and induction on the degree) [unverified]"]
theorem eq_thetaGenR_of_coeff_full_rank [IsPrincipalIdealRing (𝓞 F)] {Q : QuadForm F n} (hQ : IsTotallyPosDef Q)
    (L : Lat F n) (hLi : IsIntegral Q L.1) {R : ℕ} {a : ∀ r : ℕ, QuadForm F r → ℂ}
    {f : ∀ r : ℕ, (InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) → ℂ} (hf : IsPhiFamily R a f)
    (hfull : ∀ r ≤ R, ∀ T : QuadForm F r, (gramT T).det ≠ 0 → a r T = ((repMassT Q L T / mass Q L : ℝ) : ℂ)) :
    ∀ r ≤ R, ∀ Z ∈ siegelHF F r, f r Z = thetaGenR Q L Z :=
  family_eq_of_coeff_full_rank hf (isPhiFamily_thetaGenR hQ L hLi R) hfull

end Theta

end QuadFormsKB.SiegelWeil.Forms
