/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Structure.LocalGeneraNF
import QuadFormsKB.Literature.Hanke2011Structure.HasseScaling
import QuadFormsKB.Literature.Hanke2011Structure.Lemma37
import QuadFormsKB.Tamagawa.TernaryLocalFactorNF
import QuadFormsKB.Literature.Hanke2005.Lemma62

/-!
# Paper 6, Remark 4.18 (removing primitivity), corrected, as a local identity

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Rem. 4.18, p. 21.

The remark: dropping the primitivity condition in the total mass multiplies the formal Dirichlet series by
$\zeta_F(ns + \frac{n(n-1)}2)$, "from the scale invariance of the mass", the $ns$ because scaling by $c$ multiplies the
determinant by $c^n$. The paper's argument is local: every nondegenerate $\mathcal O_{\mathfrak p}$-valued form is
$\varpi^j$ times a primitive one, for a unique $j \ge 0$, and one compares the local densities.

Let $\mathfrak p$ be a finite prime of a number field $F$, $\varpi = $ `NF.π v` a uniformizer of
$\mathcal O_{\mathfrak p}$, $q = N\mathfrak p$, $[\varpi] \in \mathrm{SqCl}(F_{\mathfrak p}^\times,\mathcal O_{\mathfrak p}^\times)$ its class
(`piSq`), $n \ge 1$. For $S \in \mathrm{SqCl}(F_{\mathfrak p}^\times,\mathcal O_{\mathfrak p}^\times)$ let
$$M_{\mathfrak p}(S) = \sum_{G\ \text{nondegenerate},\ \det_H G = S}\beta(G)^{-1},\qquad
  M^*_{\mathfrak p}(S) = \sum_{G\ \text{nondegenerate, primitive},\ \det_H G = S}\beta(G)^{-1}$$
(`massAll`, `massPrim`; sums over the local genera of $\mathcal O_{\mathfrak p}$-valued forms in $n$ variables, $\beta$ =
`LocGenus.beta`), and $B_{\mathfrak p}$, $B^*_{\mathfrak p}$ the same sums weighted by the Hasse invariant $c_{\mathfrak p}(G)$
(`massAllB`, `massPrimB`). Then (`remark_4_18_A`, `remark_4_18_B_odd`), if the genera of determinant $S$ are finitely
many:
$$M_{\mathfrak p}(S) = \sum_{j\ge0} q^{-j\,n(n+1)/2}\,M^*_{\mathfrak p}\bigl(S\,[\varpi]^{-jn}\bigr),\qquad
  B_{\mathfrak p}(S) = \sum_{j\ge0}\bigl((\varpi,\varpi)_{\mathfrak p}^{\,n(n-1)/2}\bigr)^j q^{-j\,n(n+1)/2}\,B^*_{\mathfrak p}\bigl(S\,[\varpi]^{-jn}\bigr)
  \quad(n\text{ odd}).$$
As formal squareclass series (§4) the first says that the local factor of the non-primitive series is the primitive
one times $\sum_j (q^{-(ns + n(n+1)/2)})^j = (1 - N\mathfrak p^{-(ns + n(n+1)/2)})^{-1}$, the Euler factor at $\mathfrak p$ of
$\zeta_F(ns + \frac{n(n+1)}2)$.

*Erratum* (proposed by the formalization): the shift is
$\frac{n(n+1)}2$, not $\frac{n(n-1)}2$ ($\beta(\varpi^jG) = q^{jn(n+1)/2}\beta(G)$, `beta_smul_pow`; the paper's
$\frac{n(n-1)}2$ is the archimedean variation, which is not part of the non-archimedean mass $M^*$ of Def. 3.5). For
the Hasse-weighted part the factor is twisted: for $n \equiv 3 \pmod 4$ by $(\varpi,\varpi)_{\mathfrak p} =
(-1,\varpi)_{\mathfrak p}$ (`hasse_smul_pow_odd`, from Lemma 5.10), so the global factor is an $L$-function of a quadratic
character rather than $\zeta_F$; for $n \equiv 1 \pmod 4$ there is no twist.

Indices are 0-based.
-/

open IsDedekindDomain NumberField Matrix

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB.Siegel QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm

noncomputable section

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

namespace Rem418

/-! ### Scaling a form by $\varpi^j$ -/

theorem hessian_smul (c : 𝔬) (T : QuadForm 𝔬 n) : (c • T).hessian = c • T.hessian := by
  ext a b; simp [QuadForm.hessian, smul_coeff]; ring

theorem pi_ne_zero : NF.π v ≠ 0 := (NF.irreducible_π v).ne_zero

theorem algebraMap_pi_ne_zero : algebraMap 𝔬 Fv (NF.π v) ≠ 0 :=
  (algebraMap_ne_zero_iff (v := v)).2 (pi_ne_zero v)

/-- The class $[\varpi] \in \mathrm{SqCl}(F_{\mathfrak p}^\times,\mathcal O_{\mathfrak p}^\times)$ of the uniformizer `NF.π v`. -/
def piSq : LocalSqCl v := SqCl.mk (Units.mk0 _ (algebraMap_pi_ne_zero v))

theorem det_smul_pow (T : QuadForm 𝔬 n) (hT : T.hessian.det ≠ 0) (j : ℕ) :
    detSqForm (NF.π v ^ j • T) = piSq v ^ (j * n) * detSqForm T := by
  have hT' : algebraMap 𝔬 Fv T.hessian.det ≠ 0 := (algebraMap_ne_zero_iff (v := v)).2 hT
  have hdet : (NF.π v ^ j • T).hessian.det = (NF.π v) ^ (j * n) * T.hessian.det := by
    rw [hessian_smul, det_smul, Fintype.card_fin, ← pow_mul]
  have h2 : algebraMap 𝔬 Fv (NF.π v ^ j • T).hessian.det ≠ 0 := by
    rw [hdet, map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero _ (algebraMap_pi_ne_zero v)) hT'
  have e : Units.mk0 _ h2 = (Units.mk0 _ (algebraMap_pi_ne_zero v)) ^ (j * n) * Units.mk0 _ hT' := by
    ext; simp [hdet]
  rw [detSqForm_of_ne h2, detSqForm_of_ne hT', e, map_mul, map_pow, piSq]

/-- **The local density under scaling** (Hanke 2005, Lemma 3.1): $\beta(\varpi^jG) = q^{jn(n+1)/2}\beta(G)$. -/
theorem betaForm_smul_pow (T : QuadForm 𝔬 n) (hT : T.hessian.det ≠ 0) (j : ℕ) :
    betaForm (NF.π v ^ j • T) = ((DVR.q 𝔬 : ℝ) ^ (n * (n + 1) / 2)) ^ j * betaForm T := by
  set c : Fv := algebraMap 𝔬 Fv (NF.π v ^ j)
  have hc : c ≠ 0 := by
    simp only [c, map_pow]; exact pow_ne_zero _ (algebraMap_pi_ne_zero v)
  have hgram : Hanke2005.gramOf v (NF.π v ^ j • T) = c • Hanke2005.gramOf v T := by
    unfold Hanke2005.gramOf
    rw [hessian_smul]
    ext a b
    simp [c, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hsym : (Hanke2005.gramOf v T)ᵀ = Hanke2005.gramOf v T := Hanke2005.gramOf_transpose v T
  have hdet : (Hanke2005.gramOf v T).det ≠ 0 := by
    unfold Hanke2005.gramOf
    rw [det_smul, show (T.hessian.map (algebraMap 𝔬 Fv)).det = algebraMap 𝔬 Fv T.hessian.det from
      (RingHom.map_det _ _).symm]
    exact mul_ne_zero (pow_ne_zero _ (one_div_ne_zero two_ne_zero)) ((algebraMap_ne_zero_iff (v := v)).2 hT)
  have key := Hanke2005.hankeBeta_std_smul v hsym hdet hc
  have hnorm : ‖c‖ = ((DVR.q 𝔬 : ℝ)⁻¹) ^ j := by
    simp only [c, map_pow, norm_pow, QuatOrder.norm_pi]
  have hq : (0 : ℝ) < DVR.q 𝔬 := by
    have := DVR.q_pos (R := 𝔬); exact_mod_cast this
  unfold betaForm
  rw [hgram]
  rw [hnorm] at key
  have hpos : (0 : ℝ) < (((DVR.q 𝔬 : ℝ)⁻¹) ^ j) ^ (n * (n + 1) / 2) := by positivity
  have : Hanke2005.hankeBeta v (std v) (c • Hanke2005.gramOf v T) =
      Hanke2005.hankeBeta v (std v) (Hanke2005.gramOf v T) /
        (((DVR.q 𝔬 : ℝ)⁻¹) ^ j) ^ (n * (n + 1) / 2) := by
    rw [key]; field_simp
  rw [this, inv_pow, inv_pow, div_eq_mul_inv, inv_inv, ← pow_mul, ← pow_mul, mul_comm j]
  ring

/-! ### The content of a form: $T = \varpi^j T'$ with $T'$ primitive -/

/-- The ideal generated by the coefficients of $T$. -/
def coeffIdeal (T : QuadForm 𝔬 n) : Ideal 𝔬 := Ideal.span (Set.range fun p : Fin n × Fin n => T.coeff p.1 p.2)

theorem coeff_mem_coeffIdeal (T : QuadForm 𝔬 n) (i j : Fin n) : T.coeff i j ∈ coeffIdeal v T :=
  Ideal.subset_span ⟨(i, j), rfl⟩

theorem coeffIdeal_le_iff (T : QuadForm 𝔬 n) (I : Ideal 𝔬) : coeffIdeal v T ≤ I ↔ ∀ i j, T.coeff i j ∈ I := by
  refine ⟨fun h i j => h (coeff_mem_coeffIdeal v T i j), fun h => Ideal.span_le.2 ?_⟩
  rintro _ ⟨⟨i, j⟩, rfl⟩; exact h i j

theorem coeffIdeal_of_isometricGL {T T' : QuadForm 𝔬 n} (h : IsometricGL T T') : coeffIdeal v T = coeffIdeal v T' :=
  le_antisymm
    ((coeffIdeal_le_iff v T _).2 fun i j =>
      coeff_mem_of_isometricGL _ (IsometricGL.symm h) (fun a b => coeff_mem_coeffIdeal v T' a b) i j)
    ((coeffIdeal_le_iff v T' _).2 fun i j =>
      coeff_mem_of_isometricGL _ h (fun a b => coeff_mem_coeffIdeal v T a b) i j)

theorem coeffIdeal_smul (c : 𝔬) (T : QuadForm 𝔬 n) :
    coeffIdeal v (c • T) = Ideal.span {c} * coeffIdeal v T := by
  unfold coeffIdeal
  refine le_antisymm (Ideal.span_le.2 ?_) ?_
  · rintro _ ⟨⟨i, j⟩, rfl⟩
    simp only [smul_coeff, Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self c) (Ideal.subset_span ⟨(i, j), rfl⟩)
  · rw [Ideal.span_singleton_mul_le_iff]
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      exact Ideal.subset_span ⟨p, by simp [smul_coeff]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ a hx

theorem coeffIdeal_eq_top_iff (T : QuadForm 𝔬 n) : coeffIdeal v T = ⊤ ↔ IsPrimitiveForm T := Iff.rfl

theorem coeffIdeal_smul_pow_prim {T : QuadForm 𝔬 n} (hT : IsPrimitiveForm T) (j : ℕ) :
    coeffIdeal v (NF.π v ^ j • T) = Ideal.span {NF.π v ^ j} := by
  rw [coeffIdeal_smul, (coeffIdeal_eq_top_iff v T).2 hT, Ideal.mul_top]

theorem pow_eq_of_span_eq {j k : ℕ} (h : Ideal.span {NF.π v ^ j} = Ideal.span {NF.π v ^ k}) : j = k := by
  have hπ := NF.irreducible_π v
  rw [Ideal.span_singleton_eq_span_singleton] at h
  have := h.dvd
  have h2 := h.symm.dvd
  rcases lt_trichotomy j k with hjk | hjk | hjk
  · exfalso
    obtain ⟨u, hu⟩ := h2
    have : NF.π v ^ j * (NF.π v ^ (k - j) * u) = NF.π v ^ j * 1 := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hjk.le, ← hu, mul_one]
    have h1 := mul_left_cancel₀ (pow_ne_zero j hπ.ne_zero) this
    have hk : 0 < k - j := Nat.sub_pos_of_lt hjk
    exact hπ.not_isUnit (isUnit_of_dvd_one ⟨NF.π v ^ (k - j - 1) * u, by
      rw [← h1, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hk]⟩)
  · exact hjk
  · exfalso
    obtain ⟨u, hu⟩ := this
    have : NF.π v ^ k * (NF.π v ^ (j - k) * u) = NF.π v ^ k * 1 := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hjk.le, ← hu, mul_one]
    have h1 := mul_left_cancel₀ (pow_ne_zero k hπ.ne_zero) this
    have hk : 0 < j - k := Nat.sub_pos_of_lt hjk
    exact hπ.not_isUnit (isUnit_of_dvd_one ⟨NF.π v ^ (j - k - 1) * u, by
      rw [← h1, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hk]⟩)

theorem coeffIdeal_ne_bot (hn : n ≠ 0) {T : QuadForm 𝔬 n} (hT : T.hessian.det ≠ 0) : coeffIdeal v T ≠ ⊥ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  intro h
  apply hT
  have h0 : ∀ i j, T.coeff i j = 0 := fun i j => by
    have := coeff_mem_coeffIdeal v T i j
    rwa [h, Ideal.mem_bot] at this
  have : T.hessian = 0 := by ext a b; simp [QuadForm.hessian, h0]
  rw [this, det_zero]

/-- **Existence of the content**: a nondegenerate form over $\mathcal O_{\mathfrak p}$ is $\varpi^j$ times a primitive form. -/
theorem exists_smul_prim (hn : n ≠ 0) {T : QuadForm 𝔬 n} (hT : T.hessian.det ≠ 0) :
    ∃ (j : ℕ) (T' : QuadForm 𝔬 n), IsPrimitiveForm T' ∧ T = NF.π v ^ j • T' := by
  classical
  have hπ := NF.irreducible_π v
  obtain ⟨j, hj⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible (coeffIdeal_ne_bot v hn hT) hπ
  have hdvd : ∀ a b, NF.π v ^ j ∣ T.coeff a b := fun a b => by
    have := coeff_mem_coeffIdeal v T a b
    rw [hj, Ideal.mem_span_singleton] at this; exact this
  let c : Fin n → Fin n → 𝔬 := fun a b => if a ≤ b then Classical.choose (hdvd a b) else 0
  have hc : ∀ a b, T.coeff a b = NF.π v ^ j * c a b := fun a b => by
    by_cases hab : a ≤ b
    · simp only [c]; rw [if_pos hab]; exact Classical.choose_spec (hdvd a b)
    · simp only [c, mul_zero]; rw [if_neg hab]; simp only [mul_zero]; exact T.upper (lt_of_not_ge hab)
  let T' : QuadForm 𝔬 n := ⟨Matrix.of c, fun a b hab => by
    simp only [Matrix.of_apply, c]; exact if_neg (not_le.2 (by simpa using hab))⟩
  have hTeq : T = NF.π v ^ j • T' := QuadForm.ext (by ext a b; simp [T', smul_coeff, hc a b])
  refine ⟨j, T', ?_, hTeq⟩
  by_contra hprim
  have hle : coeffIdeal v T' ≤ IsLocalRing.maximalIdeal 𝔬 := IsLocalRing.le_maximalIdeal hprim
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπ] at hle
  have h1 : coeffIdeal v T ≤ Ideal.span {NF.π v ^ (j + 1)} := by
    rw [hTeq, coeffIdeal_smul, pow_succ, ← Ideal.span_singleton_mul_span_singleton]
    exact Ideal.mul_mono_right hle
  rw [hj] at h1
  have := pow_eq_of_span_eq v (le_antisymm h1 (Ideal.span_singleton_le_span_singleton.2
    (pow_dvd_pow _ (Nat.le_succ j))))
  omega

/-- **Uniqueness of the content**: if $\varpi^jA \simeq \varpi^kB$ with $A$, $B$ primitive, then $j = k$ and $A \simeq B$. -/
theorem smul_prim_unique {A B : QuadForm 𝔬 n} (hA : IsPrimitiveForm A) (hB : IsPrimitiveForm B) {j k : ℕ}
    (h : IsometricGL (NF.π v ^ j • A) (NF.π v ^ k • B)) : j = k ∧ IsometricGL A B := by
  have hjk : j = k := by
    have := coeffIdeal_of_isometricGL v h
    rw [coeffIdeal_smul_pow_prim v hA, coeffIdeal_smul_pow_prim v hB] at this
    exact pow_eq_of_span_eq v this
  subst hjk
  refine ⟨rfl, ?_⟩
  obtain ⟨g, hg⟩ := (isometricGL_iff_compMat).1 h
  refine (isometricGL_iff_compMat).2 ⟨g, ?_⟩
  rw [Tamagawa.compMat_smul_form] at hg
  have hne : NF.π v ^ j ≠ 0 := pow_ne_zero _ (pi_ne_zero v)
  refine QuadForm.ext (Matrix.ext fun a b => ?_)
  have := congrArg (fun Q : QuadForm 𝔬 n => Q.coeff a b) hg
  simp only [smul_coeff, Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hne this

theorem isometricGL_smul (c : 𝔬) {A B : QuadForm 𝔬 n} (h : IsometricGL A B) : IsometricGL (c • A) (c • B) := by
  obtain ⟨g, hg⟩ := (isometricGL_iff_compMat).1 h
  exact (isometricGL_iff_compMat).2 ⟨g, by rw [hg, Tamagawa.compMat_smul_form]⟩

/-! ### Scaling of local genera -/

/-- The local genus $\varpi^jG$. -/
def smulPow (j : ℕ) (G : LocGenus v n) : LocGenus v n :=
  Quotient.liftOn G (fun T => LocGenus.mk (NF.π v ^ j • T)) fun _ _ h =>
    (LocGenus.mk_eq_mk).2 (isometricGL_smul v _ h)

@[simp] theorem smulPow_mk (j : ℕ) (T : QuadForm 𝔬 n) : smulPow v j (LocGenus.mk T) = LocGenus.mk (NF.π v ^ j • T) :=
  rfl

/-! ### The Hasse invariant under scaling ($n$ odd) -/

theorem evalIn_smul_self (c : Fv) (g : QuadForm Fv n) (x : Fin n → Fv) :
    (c • g).evalIn Fv x = c * g.evalIn Fv x := by
  simp only [QuadForm.evalIn, smul_coeff, Matrix.smul_apply, smul_eq_mul, Algebra.algebraMap_self,
    RingHom.id_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem isometricIn_smul (c : Fv) {g g' : QuadForm Fv n} (h : g.IsometricIn Fv g') :
    (c • g).IsometricIn Fv (c • g') := by
  obtain ⟨P, hP, hx⟩ := h
  exact ⟨P, hP, fun x => by rw [evalIn_smul_self, evalIn_smul_self, hx]⟩

theorem map_smul_form (c : 𝔬) (T : QuadForm 𝔬 n) :
    (c • T).map (algebraMap 𝔬 Fv) = algebraMap 𝔬 Fv c • T.map (algebraMap 𝔬 Fv) :=
  QuadForm.ext (Matrix.ext fun a b => by simp [QuadForm.map, smul_coeff])

theorem smul_diag (c : Fv) (a : Fin n → Fv) : c • QuadForm.diag a = QuadForm.diag (fun i => c * a i) :=
  QuadForm.ext (Matrix.ext fun i j => by
    simp only [smul_coeff, Matrix.smul_apply, smul_eq_mul, QuadForm.diag]
    by_cases h : i = j <;> simp [h])

theorem hilbert_pow_even (a b : Fv) {m : ℕ} (hm : Even m) : hilbertSymbol Fv a b ^ m = 1 := by
  obtain ⟨k, rfl⟩ := hm
  have h2 : hilbertSymbol Fv a b ^ 2 = 1 := by unfold hilbertSymbol; split_ifs <;> norm_num
  rw [← two_mul, pow_mul, h2, one_pow]

/-- **The Hasse invariant under scaling, $n$ odd** (Lemma 5.10): $c(\varpi^jG) = (\varpi^j,\varpi^j)^{n(n-1)/2}\,c(G)$. -/
theorem hasseForm_smul_pow_odd (hn : Odd n) (T : QuadForm 𝔬 n) (hT : T.hessian.det ≠ 0) (j : ℕ) :
    hasseForm (NF.π v ^ j • T) =
      hilbertSymbol Fv (algebraMap 𝔬 Fv (NF.π v ^ j)) (algebraMap 𝔬 Fv (NF.π v ^ j)) ^ (n * (n - 1) / 2) *
        hasseForm T := by
  set c : Fv := algebraMap 𝔬 Fv (NF.π v ^ j)
  have hc : c ≠ 0 := by simp only [c, map_pow]; exact pow_ne_zero _ (algebraMap_pi_ne_zero v)
  set g : QuadForm Fv n := T.map (algebraMap 𝔬 Fv)
  have hg : g.Nondegenerate := by
    unfold QuadForm.Nondegenerate
    have : g.hessian = T.hessian.map (algebraMap 𝔬 Fv) := by
      ext a b; simp [g, QuadForm.hessian, QuadForm.map]
    rw [this, show (T.hessian.map (algebraMap 𝔬 Fv)).det = algebraMap 𝔬 Fv T.hessian.det from
      (RingHom.map_det _ _).symm]
    exact (algebraMap_ne_zero_iff (v := v)).2 hT
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag g hg
  have hca : ∀ i, c * a i ≠ 0 := fun i => mul_ne_zero hc (ha i)
  unfold hasseForm
  rw [map_smul_form, hasseC_eq_of_isometricIn (isometricIn_smul v c hiso), smul_diag,
    hasseC_eq_of_isometricIn hiso, hasseC_diag v _ hca, hasseC_diag v _ ha]
  show hasseLocal _ (fun i => c * a i) = _ * hasseLocal _ a
  rw [lemma_5_10_finite v hc a ha, hilbert_pow_even v c (∏ i, a i) (Nat.Odd.sub_odd hn odd_one), mul_one]

/-! ### The local sums with and without primitivity -/

variable (n)

/-- The nondegenerate local genera of $\det_H = S$ (no primitivity condition). -/
def allGen (S : LocalSqCl v) : Set (LocGenus v n) := {G | G.Nondeg ∧ G.det = S}

/-- The nondegenerate primitive local genera $G'$ with $[\varpi]^{jn}\det_H(G') = S$, i.e. of determinant
$S[\varpi]^{-jn}$ (`primShift_eq`). -/
def primShift (j : ℕ) (S : LocalSqCl v) : Set (LocGenus v n) :=
  {G | G.Nondeg ∧ G.Prim ∧ piSq v ^ (j * n) * G.det = S}

theorem primShift_eq (j : ℕ) (S : LocalSqCl v) :
    primShift v n j S = {G | G.Nondeg ∧ G.Prim ∧ G.det = S * (piSq v ^ (j * n))⁻¹} := by
  ext G
  simp only [primShift, Set.mem_ofPred_eq]
  rw [eq_mul_inv_iff_mul_eq, mul_comm]

/-- **$M_{\mathfrak p}(S)$**: the local mass sum $\sum_G\beta(G)^{-1}$ over all nondegenerate local genera $G$ of
$\det_H = S$ (no primitivity condition). -/
@[kb "hanke2011structure" "Rem. 4.18, p. 21 (the local mass without primitivity)"]
def massAll (S : LocalSqCl v) : ℝ := ∑ᶠ G ∈ allGen v n S, (G.beta)⁻¹

/-- **$M^*_{\mathfrak p}(S[\varpi]^{-jn})$**: the primitive local mass sum at the shifted class. -/
def massPrimShift (j : ℕ) (S : LocalSqCl v) : ℝ := ∑ᶠ G ∈ primShift v n j S, (G.beta)⁻¹

/-- **$B_{\mathfrak p}(S)$**: the Hasse-weighted local mass sum $\sum_Gc_{\mathfrak p}(G)\beta(G)^{-1}$ over all nondegenerate
local genera $G$ of $\det_H = S$. -/
@[kb "hanke2011structure" "Rem. 4.18, p. 21 (the Hasse-weighted local mass without primitivity)"]
def massAllB (S : LocalSqCl v) : ℝ := ∑ᶠ G ∈ allGen v n S, (G.hasse : ℝ) * (G.beta)⁻¹

/-- **$B^*_{\mathfrak p}(S[\varpi]^{-jn})$**: the Hasse-weighted primitive local mass sum at the shifted class. -/
def massPrimShiftB (j : ℕ) (S : LocalSqCl v) : ℝ := ∑ᶠ G ∈ primShift v n j S, (G.hasse : ℝ) * (G.beta)⁻¹

variable {n}

theorem smulPow_mem_allGen {j : ℕ} {S : LocalSqCl v} {G : LocGenus v n} (hG : G ∈ primShift v n j S) :
    smulPow v j G ∈ allGen v n S := by
  induction G using Quotient.inductionOn with
  | h T =>
    obtain ⟨hN, -, hd⟩ := hG
    change T.hessian.det ≠ 0 at hN
    change piSq v ^ (j * n) * detSqForm T = S at hd
    refine ⟨?_, ?_⟩
    · change (NF.π v ^ j • T).hessian.det ≠ 0
      rw [hessian_smul, det_smul]
      exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (pi_ne_zero v))) hN
    · change detSqForm (NF.π v ^ j • T) = S
      rw [det_smul_pow v T hN, hd]

theorem smulPow_inj {j k : ℕ} {S S' : LocalSqCl v} {G G' : LocGenus v n} (hG : G ∈ primShift v n j S)
    (hG' : G' ∈ primShift v n k S') (h : smulPow v j G = smulPow v k G') : j = k ∧ G = G' := by
  induction G using Quotient.inductionOn with
  | h A =>
  induction G' using Quotient.inductionOn with
  | h B =>
    obtain ⟨hjk, hAB⟩ := smul_prim_unique v hG.2.1 hG'.2.1 ((LocGenus.mk_eq_mk).1 h)
    exact ⟨hjk, (LocGenus.mk_eq_mk).2 hAB⟩

theorem exists_mem_image_of_allGen (hn : n ≠ 0) {S : LocalSqCl v} {G : LocGenus v n} (hG : G ∈ allGen v n S) :
    ∃ j, G ∈ smulPow v j '' primShift v n j S := by
  induction G using Quotient.inductionOn with
  | h T =>
    obtain ⟨hN, hd⟩ := hG
    change T.hessian.det ≠ 0 at hN
    change detSqForm T = S at hd
    obtain ⟨j, T', hT', rfl⟩ := exists_smul_prim v hn hN
    have hN' : T'.hessian.det ≠ 0 := by
      intro h0; apply hN; rw [hessian_smul, det_smul, h0, mul_zero]
    refine ⟨j, LocGenus.mk T', ⟨hN', hT', ?_⟩, rfl⟩
    change piSq v ^ (j * n) * detSqForm T' = S
    rw [← det_smul_pow v T' hN' j, hd]

theorem beta_smulPow {G : LocGenus v n} (hG : G.Nondeg) (j : ℕ) :
    (smulPow v j G).beta = ((DVR.q 𝔬 : ℝ) ^ (n * (n + 1) / 2)) ^ j * G.beta := by
  induction G using Quotient.inductionOn with
  | h T => exact betaForm_smul_pow v T hG j

theorem hasse_smulPow_odd (hn : Odd n) {G : LocGenus v n} (hG : G.Nondeg) (j : ℕ) :
    (smulPow v j G).hasse =
      hilbertSymbol Fv (algebraMap 𝔬 Fv (NF.π v ^ j)) (algebraMap 𝔬 Fv (NF.π v ^ j)) ^ (n * (n - 1) / 2) *
        G.hasse := by
  induction G using Quotient.inductionOn with
  | h T => exact hasseForm_smul_pow_odd v hn T hG j

theorem primShift_finite {S : LocalSqCl v} (hfin : (allGen v n S).Finite) (j : ℕ) :
    (primShift v n j S).Finite :=
  Set.Finite.of_finite_image (hfin.subset (by rintro _ ⟨G, hG, rfl⟩; exact smulPow_mem_allGen v hG))
    fun G hG G' hG' h => (smulPow_inj v hG hG' h).2

/-- **The decomposition by content**: for $n \ge 1$ and finitely many nondegenerate local genera of $\det_H = S$, a sum
over them is the sum over $j \ge 0$ of the sums over the primitive genera $G'$ of $\det_H = S[\varpi]^{-jn}$ of the values
at $\varpi^jG'$. -/
theorem finsum_allGen (hn : n ≠ 0) {S : LocalSqCl v} (hfin : (allGen v n S).Finite) (f : LocGenus v n → ℝ) :
    ∑ᶠ G ∈ allGen v n S, f G = ∑ᶠ j : ℕ, ∑ᶠ G ∈ primShift v n j S, f (smulPow v j G) := by
  classical
  set P : ℕ → Set (LocGenus v n) := fun j => smulPow v j '' primShift v n j S with hP
  have hPsub : ∀ j, P j ⊆ allGen v n S := by
    rintro j _ ⟨G, hG, rfl⟩; exact smulPow_mem_allGen v hG
  have hdisj : ∀ j k, j ≠ k → Disjoint (P j) (P k) := by
    intro j k hjk
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨G, hG, rfl⟩ ⟨G', hG', h⟩
    exact hjk (smulPow_inj v hG hG' h.symm).1
  -- the exponent of a genus
  let g : LocGenus v n → ℕ := fun G => if h : ∃ j, G ∈ P j then Nat.find h else 0
  have hg : ∀ j, ∀ G ∈ P j, g G = j := by
    intro j G hG
    have hex : ∃ j, G ∈ P j := ⟨j, hG⟩
    simp only [g, dif_pos hex]
    by_contra hne
    exact Set.disjoint_left.1 (hdisj _ _ hne) (Nat.find_spec hex) hG
  set J : Set ℕ := {j | (P j).Nonempty} with hJdef
  have hJ : J.Finite := by
    refine (hfin.image g).subset ?_
    rintro j ⟨G, hG⟩
    exact ⟨G, hPsub j hG, hg j G hG⟩
  have hU : allGen v n S = ⋃ j ∈ J, P j := by
    ext G
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨fun hG => ?_, fun ⟨j, _, hG⟩ => hPsub j hG⟩
    obtain ⟨j, hj⟩ := exists_mem_image_of_allGen v hn hG
    exact ⟨j, ⟨G, hj⟩, hj⟩
  have hpd : J.PairwiseDisjoint P := fun j _ k _ hjk => hdisj j k hjk
  rw [hU, finsum_mem_biUnion hpd hJ (fun j _ => hfin.subset (hPsub j))]
  have himg : ∀ j, ∑ᶠ G ∈ P j, f G = ∑ᶠ G ∈ primShift v n j S, f (smulPow v j G) := fun j =>
    finsum_mem_image fun G hG G' hG' h => (smulPow_inj v hG hG' h).2
  simp_rw [himg]
  refine (finsum_mem_inter_support_eq (fun j => ∑ᶠ G ∈ primShift v n j S, f (smulPow v j G)) J Set.univ ?_).trans
    (finsum_mem_univ _)
  ext j
  simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Function.mem_support, and_iff_right_iff_imp]
  intro hne
  by_contra hj
  apply hne
  refine finsum_mem_of_eqOn_zero fun G hG => ?_
  exact absurd ⟨_, Set.mem_image_of_mem _ hG⟩ hj

/-- **Remark 4.18, corrected, for the local factor of $M$** (Hanke 2011, p. 21). Let $\mathfrak p$ be a finite prime of a
number field $F$, $q = N\mathfrak p$, $n \ge 1$, and $S \in \mathrm{SqCl}(F_{\mathfrak p}^\times,\mathcal O_{\mathfrak p}^\times)$ such that
there are finitely many nondegenerate local genera of $\det_H = S$. Then
$$M_{\mathfrak p}(S) = \sum_{j\ge0}\bigl(q^{n(n+1)/2}\bigr)^{-j}\,M^*_{\mathfrak p}\bigl(S[\varpi]^{-jn}\bigr),$$
the sum over all nondegenerate local genera (`massAll`) against the primitive sums at the shifted classes
(`massPrimShift`, `primShift_eq`). As squareclass series this multiplies the local factor by
$\sum_j N\mathfrak p^{-j(ns + n(n+1)/2)}$, the factor at $\mathfrak p$ of $\zeta_F(ns + \frac{n(n+1)}2)$. *Erratum:* the paper's
shift $\frac{n(n-1)}2$ should be $\frac{n(n+1)}2$. -/
@[kb "hanke2011structure" "Rem. 4.18, p. 21 (removing primitivity, local factor of M; corrected shift)"]
theorem remark_4_18_A (hn : n ≠ 0) {S : LocalSqCl v} (hfin : (allGen v n S).Finite) :
    massAll v n S = ∑ᶠ j : ℕ, (((DVR.q 𝔬 : ℝ) ^ (n * (n + 1) / 2)) ^ j)⁻¹ * massPrimShift v n j S := by
  unfold massAll massPrimShift
  rw [finsum_allGen v hn hfin]
  refine finsum_congr fun j => ?_
  rw [mul_finsum_mem]
  refine finsum_mem_congr rfl fun G hG => ?_
  rw [beta_smulPow v hG.1, mul_inv]

/-- **Remark 4.18, corrected, for the Hasse-weighted local factor, $n$ odd** (Hanke 2011, p. 21). With the hypotheses of
`remark_4_18_A` and $n$ odd,
$$B_{\mathfrak p}(S) = \sum_{j\ge0}(\varpi^j,\varpi^j)_{\mathfrak p}^{\,n(n-1)/2}\bigl(q^{n(n+1)/2}\bigr)^{-j}\,
  B^*_{\mathfrak p}\bigl(S[\varpi]^{-jn}\bigr)$$
(`massAllB`, `massPrimShiftB`), since $c_{\mathfrak p}(\varpi^jG) = (\varpi^j,\varpi^j)^{n(n-1)/2}c_{\mathfrak p}(G)$ (Lemma 5.10).
*Erratum:* besides the shift $\frac{n(n+1)}2$, for $n \equiv 3 \pmod 4$ the factor is twisted by
$(\varpi^j,\varpi^j)_{\mathfrak p} = (-1,\varpi)_{\mathfrak p}^j$, so the $B^*$ part is not multiplied by $\zeta_F$. -/
@[kb "hanke2011structure" "Rem. 4.18, p. 21 (removing primitivity, Hasse-weighted local factor, n odd; corrected)"]
theorem remark_4_18_B_odd (hn : Odd n) {S : LocalSqCl v} (hfin : (allGen v n S).Finite) :
    massAllB v n S = ∑ᶠ j : ℕ,
      ((hilbertSymbol Fv (algebraMap 𝔬 Fv (NF.π v ^ j)) (algebraMap 𝔬 Fv (NF.π v ^ j)) ^ (n * (n - 1) / 2) : ℤ) : ℝ) *
        (((DVR.q 𝔬 : ℝ) ^ (n * (n + 1) / 2)) ^ j)⁻¹ * massPrimShiftB v n j S := by
  have hn0 : n ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hn)
  unfold massAllB massPrimShiftB
  rw [finsum_allGen v hn0 hfin]
  refine finsum_congr fun j => ?_
  rw [mul_finsum_mem]
  refine finsum_mem_congr rfl fun G hG => ?_
  rw [beta_smulPow v hG.1, hasse_smulPow_odd v hn hG.1, mul_inv]
  push_cast
  ring

end Rem418

end

end QuadFormsKB.Hanke2011Structure
