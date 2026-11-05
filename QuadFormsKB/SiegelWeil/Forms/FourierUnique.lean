/-
# Uniqueness of Fourier coefficients on $\mathbb H_r^d$
**Layer:** global over a totally real number field $F$ ($d = [F:\mathbb Q]$ real places); analysis on $\mathbb H_r^d$ (no arithmetic input).

**Setting.** For a form $T$ in $r$ variables over $F$ (`QuadForm F r`, upper-triangular coefficients) and $Z = (Z_v)_v \in \mathbb H_r^d$
(`siegelHF`), $e_T(Z) = \exp\big(2\pi i\sum_v\operatorname{tr}(\sigma_v(T_G)Z_v)\big)$ (`eT`, $T_G = \tfrac12H_T$ the Gram matrix), as in
`ThetaR.lean`.

**Results.**
* `gramT_injective`: $T \mapsto T_G$ is injective (upper-triangular coefficients, characteristic $0$);
* `exists_generic_direction`: there are real symmetric $D = (D_v)_v$ (upper coordinates $\delta$) such that
  $T \mapsto \lambda_T = \sum_v\operatorname{tr}(\sigma_v(T_G)D_v)$ is injective on all forms $T$: the bad $\delta$ lie in countably many proper
  hyperplanes $\{\delta : \sum_v\operatorname{tr}(\sigma_v(G)D_v) = 0\}$, $G = T_G - T'_G \ne 0$, a Lebesgue null set;
* **`fourier_coeff_unique`**: if $\sum_Ta(T)e_T(Z)$ and $\sum_Tb(T)e_T(Z)$ converge absolutely and agree for every $Z \in \mathbb H_r^d$,
  then $a = b$; **`eq_of_hasSum_eT`** is the same with `HasSum` to a common function $f$. So the coefficients of the expansions of
  `thetaGenR` (`hasSum_thetaGenR`) are *the* Fourier coefficients of the function, and two such functions are equal iff their
  coefficients are.
* `summable_norm_repCountT_eT`, `summable_norm_thetaGenR_coeff`: the expansions $\theta_M = \sum_Tr_M(T)e_T$ and
  $\theta_{\mathrm{gen}(L)} = \sum_T\frac{\mathrm{repMassT}(L,T)}{\mathrm{Mass}(L)}e_T$ converge absolutely in $T$;
* **`thetaGenR_coeff_unique`**: any absolutely convergent expansion $\theta_{\mathrm{gen}(L)} = \sum_Tb(T)e_T$ has
  $b(T) = \mathrm{repMassT}(L,T)/\mathrm{Mass}(L)$; **`eq_thetaGenR_of_coeff`**: conversely a function with such an expansion and these
  coefficients is $\theta_{\mathrm{gen}(L)}$ (the form in which $E(g_Z, s_0, \Phi) = \theta_{\mathrm{gen}}(Z)$ follows from the equality of
  all Fourier coefficients).

*Proof.* On the real line $t \mapsto Z_0 + tD$ ($Z_0 = (iI)_v$, $D$ generic), $e_T(Z_0 + tD) = e_T(Z_0)e^{2\pi i\lambda_Tt}$ with pairwise
distinct $\lambda_T$, and Bohr's mean value (`coeff_eq_zero_of_tsum_exp_eq_zero`) gives $(a(T) - b(T))e_T(Z_0) = 0$.

Source: the uniqueness of Fourier expansions of Siegel modular forms, e.g. Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I
[unverified]; the proof here by a generic real line and Bohr's mean value is chosen to avoid integration over a torus.
-/
import QuadFormsKB.SiegelWeil.Forms.ThetaR
import QuadFormsKB.SiegelWeil.Forms.ArchDetBound
import QuadFormsKB.SiegelWeil.Forms.FourierUniqueBohr
import QuadFormsKB.Tamagawa.Measure.Weil.AdditiveAdele

open Matrix NumberField Complex MeasureTheory
open QuadFormsKB.HilbertModular QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.WeilRep.Genus

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {r : ℕ}

/-- Forms in $r$ variables over a number field form a countable set ($F \cong \mathbb Q^d$ is countable). -/
instance countable_quadForm : Countable (QuadForm F r) := by
  have : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  have : Countable (Fin r → Fin r → F) := inferInstance
  exact Function.Injective.countable (f := fun (T : QuadForm F r) (i j : Fin r) => T.coeff i j)
    fun T T' h => QuadForm.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)

/-- The Gram matrix determines the form: $T \mapsto T_G = \tfrac12(C + C^{\mathsf T})$ is injective on upper-triangular $C$. -/
lemma gramT_injective : Function.Injective (gramT : QuadForm F r → Matrix (Fin r) (Fin r) F) := by
  intro T T' h
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [gramT, QuadForm.hessian, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul] at hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have h1 : T.coeff j i = 0 := T.upper hlt
    have h2 : T'.coeff j i = 0 := T'.upper hlt
    rw [h1, h2] at hij
    linear_combination 2 * hij
  · subst heq; linear_combination hij
  · have h1 : T.coeff i j = 0 := T.upper hgt
    have h2 : T'.coeff i j = 0 := T'.upper hgt
    rw [h1, h2]

/-- The real linear functional $\delta \mapsto \sum_v\sum_{i,j}\sigma_v(G_{ij})\,\mathrm{symU}(\delta_v)_{ji}$. -/
def ellD (G : Matrix (Fin r) (Fin r) F) : (InfinitePlace F → UIdx r → ℝ) →ₗ[ℝ] ℝ where
  toFun δ := ∑ v, ∑ i, ∑ j, realEmb F v (G i j) * symU (δ v) j i
  map_add' δ δ' := by
    simp only [Pi.add_apply, ArchR.symU_add, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c δ := by
    simp only [Pi.smul_apply, ArchR.symU_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

lemma ellD_sub (G G' : Matrix (Fin r) (Fin r) F) (δ : InfinitePlace F → UIdx r → ℝ) :
    ellD (G - G') δ = ellD G δ - ellD G' δ := by
  simp only [ellD, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

/-- For a nonzero symmetric $G$ the functional `ellD G` is nonzero (evaluate at $\delta_v$ = the upper coordinates of $\sigma_v(G)$). -/
lemma ellD_ne_zero {G : Matrix (Fin r) (Fin r) F} (hG : Gᵀ = G) (hG0 : G ≠ 0) : ellD G ≠ 0 := by
  intro h0
  obtain ⟨i0, j0, hij⟩ : ∃ i j, G i j ≠ 0 := by
    by_contra hc; simp only [not_exists, not_not] at hc; exact hG0 (Matrix.ext hc)
  set δ : InfinitePlace F → UIdx r → ℝ := fun v p => realEmb F v (G p.1.1 p.1.2) with hδ
  have hsym : ∀ v, symU (δ v) = G.map (realEmb F v) := by
    intro v
    refine ArchR.symU_upper (A := G.map (realEmb F v)) ?_
    rw [← Matrix.transpose_map, hG]
  have hval : ellD G δ = ∑ v, ∑ i, ∑ j, realEmb F v (G i j) ^ 2 := by
    simp only [ellD, LinearMap.coe_mk, AddHom.coe_mk, hsym, Matrix.map_apply]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : G j i = G i j := by simpa using congrFun (congrFun hG i) j
    rw [this, sq]
  have hpos : 0 < ellD G δ := by
    rw [hval]
    obtain ⟨v0⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hv : 0 < realEmb F v0 (G i0 j0) ^ 2 := by
      have : realEmb F v0 (G i0 j0) ≠ 0 := (map_ne_zero _).mpr hij
      positivity
    refine lt_of_lt_of_le hv ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun v => ∑ i, ∑ j, realEmb F v (G i j) ^ 2)
      (fun v _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ v0))
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, realEmb F v0 (G i j) ^ 2)
      (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i0))
    exact Finset.single_le_sum (f := fun j => realEmb F v0 (G i0 j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j0)
  rw [h0] at hpos
  simp at hpos

/-- **A generic real direction:** there is $\delta$ with $T \mapsto \sum_v\operatorname{tr}(\sigma_v(T_G)\,\mathrm{symU}(\delta_v))$ injective. -/
theorem exists_generic_direction :
    ∃ δ : InfinitePlace F → UIdx r → ℝ, Function.Injective fun T : QuadForm F r => ellD (gramT T) δ := by
  set S := {p : QuadForm F r × QuadForm F r // p.1 ≠ p.2}
  set Bad : Set (InfinitePlace F → UIdx r → ℝ) :=
    ⋃ p : S, (LinearMap.ker (ellD (gramT p.1.1 - gramT p.1.2)) : Set _) with hBad
  have hne : ∀ p : S, gramT p.1.1 - gramT p.1.2 ≠ 0 := fun p h =>
    p.2 (gramT_injective (sub_eq_zero.mp h))
  have hsymm : ∀ p : S, (gramT p.1.1 - gramT p.1.2)ᵀ = gramT p.1.1 - gramT p.1.2 := fun p => by
    rw [Matrix.transpose_sub, gramT_transpose, gramT_transpose]
  have hnull : volume Bad = 0 := by
    refine measure_iUnion_null fun p => ?_
    refine Measure.addHaar_submodule _ _ ?_
    intro htop
    exact ellD_ne_zero (hsymm p) (hne p) (LinearMap.ker_eq_top.mp htop)
  have hex : (Badᶜ).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hc
    rw [hc] at hnull
    exact (Measure.measure_univ_pos.mpr (NeZero.ne (volume : Measure (InfinitePlace F → UIdx r → ℝ)))).ne' hnull
  obtain ⟨δ, hδ⟩ := hex
  refine ⟨δ, fun T T' hTT => ?_⟩
  by_contra hne'
  apply hδ
  refine Set.mem_iUnion.mpr ⟨⟨(T, T'), hne'⟩, ?_⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  rw [ellD_sub]
  exact sub_eq_zero.mpr hTT

/-- **Uniqueness of Fourier coefficients on $\mathbb H_r^d$.** -/
@[kb "freitag1983" "Ch. I (uniqueness of the Fourier expansion) [unverified]"]
theorem fourier_coeff_unique {a b : QuadForm F r → ℂ}
    (ha : ∀ Z ∈ siegelHF F r, Summable fun T => ‖a T * eT T Z‖)
    (hb : ∀ Z ∈ siegelHF F r, Summable fun T => ‖b T * eT T Z‖)
    (h : ∀ Z ∈ siegelHF F r, ∑' T, a T * eT T Z = ∑' T, b T * eT T Z) : a = b := by
  obtain ⟨δ, hδ⟩ := exists_generic_direction (F := F) (r := r)
  set Z0 : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ := fun _ => I • (1 : Matrix (Fin r) (Fin r) ℂ) with hZ0
  set Zt : ℝ → InfinitePlace F → Matrix (Fin r) (Fin r) ℂ :=
    fun t v => Z0 v + (t : ℂ) • cR (symU (δ v)) with hZt
  have hmem : ∀ t, Zt t ∈ siegelHF F r := by
    intro t v
    refine ⟨?_, ?_⟩
    · simp only [hZt, hZ0, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one]
      rw [← Matrix.transpose_map, ArchR.symU_transpose]
    · have : (Zt t v).map Complex.im = 1 := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp [hZt, hZ0]
        · simp [hZt, hZ0, hij]
      rw [this]; exact Matrix.PosDef.one
  have h0mem : Z0 ∈ siegelHF F r := by simpa [hZt] using hmem 0
  have htr : ∀ T : QuadForm F r, ∀ t : ℝ,
      trPair T (Zt t) = trPair T Z0 + (t : ℂ) * (ellD (gramT T) δ : ℂ) := by
    intro T t
    simp only [trPair, hZt, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, ellD, LinearMap.coe_mk, AddHom.coe_mk]
    push_cast
    rw [Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have heT : ∀ T : QuadForm F r, ∀ t : ℝ, eT T (Zt t) =
      eT T Z0 * cexp (2 * Real.pi * I * ((ellD (gramT T) δ : ℝ) * t)) := by
    intro T t
    rw [eT, eT, htr, ← Complex.exp_add]
    congr 1; ring
  funext T
  set c : QuadForm F r → ℂ := fun T => (a T - b T) * eT T Z0 with hc
  have hcs : Summable fun T => ‖c T‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun T => ?_) ((ha Z0 h0mem).add (hb Z0 h0mem))
    simp only [hc, sub_mul]
    exact norm_sub_le _ _
  have hzero : ∀ t : ℝ, ∑' T, c T * cexp (2 * Real.pi * I * ((ellD (gramT T) δ : ℝ) * t)) = 0 := by
    intro t
    have e1 := h (Zt t) (hmem t)
    have hsa := (ha (Zt t) (hmem t)).of_norm
    have hsb := (hb (Zt t) (hmem t)).of_norm
    have : ∑' T, (a T * eT T (Zt t) - b T * eT T (Zt t)) = 0 := by
      rw [hsa.tsum_sub hsb, e1, sub_self]
    rw [← this]
    refine tsum_congr fun T => ?_
    rw [heT, hc]; ring
  have := coeff_eq_zero_of_tsum_exp_eq_zero c hcs (fun T => ellD (gramT T) δ) hδ hzero T
  simp only [hc, mul_eq_zero, Complex.exp_ne_zero, or_false, eT] at this
  exact sub_eq_zero.mp this

/-- **Uniqueness of Fourier coefficients**, `HasSum` form: two absolutely convergent expansions of the same function on
$\mathbb H_r^d$ have the same coefficients. -/
theorem eq_of_hasSum_eT {a b : QuadForm F r → ℂ} {f : (InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) → ℂ}
    (ha : ∀ Z ∈ siegelHF F r, Summable fun T => ‖a T * eT T Z‖)
    (hb : ∀ Z ∈ siegelHF F r, Summable fun T => ‖b T * eT T Z‖)
    (hfa : ∀ Z ∈ siegelHF F r, HasSum (fun T => a T * eT T Z) (f Z))
    (hfb : ∀ Z ∈ siegelHF F r, HasSum (fun T => b T * eT T Z) (f Z)) : a = b :=
  fourier_coeff_unique ha hb fun Z hZ => (hfa Z hZ).tsum_eq.trans (hfb Z hZ).tsum_eq.symm

/-! ### The genus theta series: its coefficients are the Fourier coefficients -/

section Theta

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Frames

variable {n : ℕ}

/-- The Fourier expansion of $\theta_M$ converges absolutely in $T$: $\sum_Tr_M(T)|e_T(Z)| = \sum_{X\in M^r}|e_{Q[X]}(Z)| < \infty$. -/
lemma summable_norm_repCountT_eT {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (M : Lat F n)
    {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) :
    Summable fun T : QuadForm F r => ‖(repCountT Q M T : ℂ) * eT T Z‖ := by
  have hs := summable_norm_thetaRTerm hQ M.2 hZ
  have h := hs.hasSum.tsum_fiberwise (fun X : frames M.1 r => Q.compMat X.1)
  refine h.summable.congr fun T => ?_
  have e1 : (∑' b : (fun X : frames M.1 r => Q.compMat X.1) ⁻¹' {T}, ‖eT (Q.compMat b.1.1) Z‖) =
      ∑' _ : (fun X : frames M.1 r => Q.compMat X.1) ⁻¹' {T}, ‖eT T Z‖ :=
    tsum_congr fun b => by rw [show Q.compMat b.1.1 = T from b.2]
  rw [e1, tsum_const, nsmul_eq_mul, norm_mul, Complex.norm_natCast]
  congr 2
  exact Nat.card_congr
    { toFun := fun X => ⟨X.1.1, X.1.2, X.2⟩
      invFun := fun X => ⟨⟨X.1, X.2.1⟩, X.2.2⟩
      left_inv := fun X => rfl
      right_inv := fun X => rfl }

/-- The Fourier expansion of the genus average $\theta_{\mathrm{gen}(L)}$ (`hasSum_thetaGenR`) converges absolutely in $T$. -/
lemma summable_norm_thetaGenR_coeff {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (L : Lat F n) (hLi : IsIntegral Q L.1)
    {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) :
    Summable fun T : QuadForm F r => ‖((repMassT Q L T / mass Q L : ℝ) : ℂ) * eT T Z‖ := by
  have hfin := genusClasses_finite hQ L hLi
  have hsum : Summable fun T : QuadForm F r => ∑ c ∈ hfin.toFinset,
      ‖((mass Q L : ℝ) : ℂ)⁻¹ * ((LatClass.autCard Q c : ℂ))⁻¹‖ * ‖(repCountT Q c.out T : ℂ) * eT T Z‖ :=
    summable_sum fun c _ => (summable_norm_repCountT_eT hQ c.out hZ).mul_left _
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun T => ?_) hsum
  have e : ((repMassT Q L T / mass Q L : ℝ) : ℂ) * eT T Z = ∑ c ∈ hfin.toFinset,
      ((mass Q L : ℝ) : ℂ)⁻¹ * ((LatClass.autCard Q c : ℂ))⁻¹ * ((repCountT Q c.out T : ℂ) * eT T Z) := by
    rw [repMassT, finsum_mem_eq_finite_toFinset_sum _ hfin]
    push_cast
    rw [Finset.sum_div, Finset.sum_mul, Finset.sum_congr rfl fun c _ => by rw [latClass_repCountT_eq]]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [e]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))
  rw [norm_mul]

/-- **The coefficients of the genus theta series are its Fourier coefficients** (uniqueness): if $\theta_{\mathrm{gen}(L)}(Z) =
\sum_Tb(T)e_T(Z)$ absolutely for every $Z \in \mathbb H_r^d$, then $b(T) = \mathrm{repMassT}(L, T)/\mathrm{Mass}(L)$ for every $T$. So any
function on $\mathbb H_r^d$ with an absolutely convergent expansion $\sum_Tb(T)e_T$ equals $\theta_{\mathrm{gen}(L)}$ iff its coefficients are
Siegel's averaged representation numbers. -/
@[kb "siegel1935" "§1 (Fourier coefficients of the genus average) [unverified]"]
theorem thetaGenR_coeff_unique {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (L : Lat F n) (hLi : IsIntegral Q L.1)
    {b : QuadForm F r → ℂ} (hb : ∀ Z ∈ siegelHF F r, Summable fun T => ‖b T * eT T Z‖)
    (hbθ : ∀ Z ∈ siegelHF F r, HasSum (fun T => b T * eT T Z) (thetaGenR Q L Z)) :
    b = fun T => ((repMassT Q L T / mass Q L : ℝ) : ℂ) :=
  eq_of_hasSum_eT hb (fun _ hZ => summable_norm_thetaGenR_coeff hQ L hLi hZ) hbθ
    (fun _ hZ => hasSum_thetaGenR hQ L hLi hZ)

/-- **Equality with the genus theta series from the coefficients:** a function $f$ on $\mathbb H_r^d$ with absolutely convergent expansion
$\sum_Tb(T)e_T$ and $b(T) = \mathrm{repMassT}(L, T)/\mathrm{Mass}(L)$ for every $T$ is $\theta_{\mathrm{gen}(L)}$ (the converse of
`thetaGenR_coeff_unique`; the form in which the Siegel–Weil identity $E = \theta_{\mathrm{gen}}$ follows from equality of all coefficients). -/
theorem eq_thetaGenR_of_coeff {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (L : Lat F n) (hLi : IsIntegral Q L.1)
    {b : QuadForm F r → ℂ} {f : (InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) → ℂ}
    (hbf : ∀ Z ∈ siegelHF F r, HasSum (fun T => b T * eT T Z) (f Z))
    (hcoeff : ∀ T, b T = ((repMassT Q L T / mass Q L : ℝ) : ℂ)) :
    ∀ Z ∈ siegelHF F r, f Z = thetaGenR Q L Z := by
  intro Z hZ
  have h := hbf Z hZ
  simp_rw [hcoeff] at h
  exact h.unique (hasSum_thetaGenR hQ L hLi hZ)

end Theta

end QuadFormsKB.SiegelWeil.Forms
