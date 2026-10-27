/-
# Local counts for frames of corank one

**Layer:** number fields, adeles. $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $r + 1$ variables,
$T_0$ nondegenerate of rank $r$, $\Xi$ a rational frame of $T_0$, and $D$ a frame tower of corank $n' = 1$ with
complementary form $Q'' = \langle c\rangle$. Then $SO(Q'')$ is trivial at every place.

**Proves**
* `locCount` $n_v$, the number of $SO(L_v)$-orbits of integral frames of $T_0$ at $v$; `locCount_eq_one`: $n_v = 1$ away
  from the exceptional places `towerBad`;
* `frameLocFactor_mul_aSO`: the local identity $f_v\,a''_v = n_v\,a_v$ (every orbit stabilizer is the whole trivial group,
  of measure $a''_v$);
* `mulSupport_locCount_subset`, `tsum_one_finOrbit`: the number of orbits of integral adelic frames is
  $\prod_vn_v$ (a finite product);
* rank one: `mulSupport_aSO_rankOne_finite`, `tprod_aSO_rankOne`, the product formula
  $\prod_va_v(\langle c\rangle) = \prod_{w\mid\infty}|2c|_w$ (normalized absolute values);
* `det_adapted_sq`: $\det(g)^2\det H_{Q_0} = \det H_{T_0}\det H_{Q''}$ for the adapted frame $g = [\Xi\mid C]$.
-/
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefiniteNF
import QuadFormsKB.Tamagawa.Measure.Weil.RankOneAdelic

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity

variable {F : Type} [Field F] [NumberField F] {r : ℕ}

/-! ### Rank one: the local factors and the product formula -/

/-- In one variable the local special orthogonal group is trivial. -/
theorem subsingleton_SOv (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm (𝓞 F) 1) : Subsingleton (SOv v Q) := by
  have key : ∀ x : SOv v Q, x = 1 := fun x => Subtype.ext (Subtype.ext (gl_one_eq_one _ x.2))
  exact ⟨fun a b => by rw [key a, key b]⟩

/-- A nondegenerate form $\langle c\rangle$ has $c \ne 0$. -/
theorem coeff_ne_zero_of_nondegenerate_one (Q : QuadForm (𝓞 F) 1) (hQ : Q.Nondegenerate) : Q.coeff 0 0 ≠ 0 := by
  intro h0; apply hQ; rw [TauSOOne.hessian_det_rankOne, h0, mul_zero]

/-- For $Q = \langle c\rangle$ the real local factor $a_v$ is $N(\mathfrak p^{v_\mathfrak p(2c)})$. -/
theorem aSO_rankOne_eq (Q : QuadForm (𝓞 F) 1) (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) :
    aSO Q v = (Ideal.absNorm (v.maxPowDividing (Ideal.span {2 * Q.coeff 0 0})) : ℝ) := by
  have hsd := TauSOOne.siegelDensity_rankOne_maxPow Q (coeff_ne_zero_of_nondegenerate_one Q hQ) v
  unfold aSO
  rw [muLocSO_soStabSO, div_one, ENNReal.toReal_ofReal, hsd]
  rw [hsd]; positivity

/-- **The local factors $a_v(\langle c\rangle)$ are $1$ outside the finite set of primes dividing $2c$**:
the support of the product is finite. -/
theorem mulSupport_aSO_rankOne_finite (Q : QuadForm (𝓞 F) 1) (hQ : Q.Nondegenerate) :
    (Function.mulSupport (aSO Q)).Finite := by
  refine (finite_badPrimes Q hQ).subset fun v hv => ?_
  by_contra hvb
  apply hv
  rw [aSO_rankOne_eq Q hQ, ← TauSOOne.siegelDensity_rankOne_maxPow Q (coeff_ne_zero_of_nondegenerate_one Q hQ)]
  exact RankOne.siegelDensity_rankOne_good Q hQ v hvb

open Classical in
/-- $\prod_v a_v(\langle c\rangle) = \prod_{w\mid\infty}|2c|_w$ (normalized absolute values): the product formula for
$2c$. -/
theorem tprod_aSO_rankOne (Q : QuadForm (𝓞 F) 1) (hQ : Q.Nondegenerate) :
    ∏' v, aSO Q v = (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w (algebraMap (𝓞 F) F Q.hessian.det)|) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w (algebraMap (𝓞 F) F Q.hessian.det)‖ ^ 2 := by
  have hdet := TauSOOne.hessian_det_rankOne Q
  have hc := coeff_ne_zero_of_nondegenerate_one Q hQ
  have hx : (2 * Q.coeff 0 0 : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero hc
  have hS : ∀ v : HeightOneSpectrum (𝓞 F), (2 * Q.coeff 0 0 : 𝓞 F) ∈ v.asIdeal →
      v ∈ (finite_badPrimes Q hQ).toFinset := fun v hv => by
    rw [Set.Finite.mem_toFinset]
    show 2 * Q.hessian.det ∈ v.asIdeal
    rw [hdet]; exact Ideal.mul_mem_left _ _ hv
  rw [tprod_eq_prod (s := (finite_badPrimes Q hQ).toFinset) (fun v hv => by
      have hb : v ∉ badPrimes Q := fun h => hv ((Set.Finite.mem_toFinset _).mpr h)
      rw [aSO_rankOne_eq Q hQ, ← TauSOOne.siegelDensity_rankOne_maxPow Q hc]
      exact RankOne.siegelDensity_rankOne_good Q hQ v hb),
    Finset.prod_congr rfl fun v _ => aSO_rankOne_eq Q hQ v,
    TauSOOne.prod_maxPow_eq hx _ hS]
  have h := prod_embeddings_eq (fun d => d) (((2 * Q.coeff 0 0 : 𝓞 F)) : F)
  rw [h, hdet]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [← InfinitePlace.norm_embedding_of_isReal w.2, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [← InfinitePlace.norm_embedding_eq]

/-! ### The local counts for a tower of corank one -/

section Tower

variable (Q₀ : QuadForm (𝓞 F) (r + 1)) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (Ξ : RatFrame Q₀ T₀)
  (D : FrameTower Q₀ hQ 1 (cols Ξ.1)) (hT : T₀.Nondegenerate)

/-- The number $n_v$ of local orbits (the $SO(L_v)$-orbits of integral frames of $T_0$ at $v$). -/
def locCount (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  Nat.card (LocOrbit v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT))

/-- At a place outside the exceptional set there is exactly one local orbit: $n_v = 1$. -/
theorem locCount_eq_one (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ towerBad Q₀ hQ T₀ Ξ D hT) :
    locCount Q₀ hQ T₀ Ξ D hT v = 1 := by
  have hs := good_subsingleton Q₀ hQ T₀ Ξ D hT v hv le_rfl
  have hn : Nonempty (LocOrbit v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT)) :=
    ⟨Quotient.mk _ ⟨locBase v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT),
      ⟨1, by rw [soMat_one, Matrix.one_mul]⟩, good_base_int Q₀ hQ T₀ Ξ D hT v hv⟩⟩
  unfold locCount
  exact Nat.card_unique

/-- **The local identity with trivial $SO(L''_v)$:** $f_v\,a''_v = n_v\,a_v$. -/
theorem frameLocFactor_mul_aSO (v : HeightOneSpectrum (𝓞 F)) :
    frameLocFactor Q₀ hQ T₀ Ξ D hT v * aSO D.Q'' v = (locCount Q₀ hQ T₀ Ξ D hT v : ℝ) * aSO Q₀ v := by
  have hfin := finite_locOrbit v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT) hQ hT le_rfl
  have hsub := subsingleton_SOv v D.Q''
  have hof := ofReal_frameLocFactor Q₀ hQ T₀ Ξ D hT le_rfl v
  have hset : ∀ o : LocOrbit v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT),
      (locOrbitStab v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT) o : Set (SOv v D.Q'')) =
        (soStabSO v D.Q'' : Set (SOv v D.Q'')) := fun o => by
    rw [Set.eq_univ_of_forall (s := (locOrbitStab v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT) o : Set (SOv v D.Q'')))
        (fun x => by rw [Subsingleton.elim x 1]; exact one_mem _),
      Set.eq_univ_of_forall (s := (soStabSO v D.Q'' : Set (SOv v D.Q'')))
        (fun x => by rw [Subsingleton.elim x 1]; exact one_mem _)]
  have hsum : locOrbitSum v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT) =
      (locCount Q₀ hQ T₀ Ξ D hT v : ℝ≥0∞) * ENNReal.ofReal (aSO Q₀ v / aSO D.Q'' v) := by
    unfold locOrbitSum
    haveI := Fintype.ofFinite (LocOrbit v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT))
    rw [tsum_congr fun o => by
      show _ / muLocSO v D.Q'' 1 (locOrbitStab v Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT) o : Set (SOv v D.Q'')) = _
      rw [hset o]]
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ofReal_aSO Q₀ v, ← ofReal_aSO D.Q'' v,
      ← ENNReal.ofReal_div_of_pos (aSO_pos D.Q'' D.hQ'' v)]
    unfold locCount
    rw [Nat.card_eq_fintype_card]
  rw [hsum, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hof
  have h2 := (ENNReal.ofReal_eq_ofReal_iff (frameLocFactor_nonneg Q₀ hQ T₀ Ξ D hT v)
    (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (aSO_pos Q₀ hQ v).le (aSO_pos D.Q'' D.hQ'' v).le))).mp hof
  have hp := (aSO_pos D.Q'' D.hQ'' v).ne'
  rw [h2]
  field_simp

/-- The local counts are $1$ outside the exceptional places: finite support of the product. -/
theorem mulSupport_locCount_subset :
    Function.mulSupport (fun v => (locCount Q₀ hQ T₀ Ξ D hT v : ℝ)) ⊆ (towerBad Q₀ hQ T₀ Ξ D hT : Set _) := by
  intro v hv
  by_contra hb
  exact hv (by simp [locCount_eq_one Q₀ hQ T₀ Ξ D hT v hb])

/-- **The number of orbits of integral adelic frames is the product of the local counts.** -/
theorem tsum_one_finOrbit :
    ∑' _O : FinOrbit Q₀ T₀ Ξ, (1 : ℝ≥0∞) = ENNReal.ofReal (∏' v, (locCount Q₀ hQ T₀ Ξ D hT v : ℝ)) := by
  classical
  have : ∀ v : towerBad Q₀ hQ T₀ Ξ D hT, Finite (LocOrbit v.1 Q₀ T₀ (towerAdapted Q₀ hQ T₀ Ξ D hT)) :=
    fun v => finite_locOrbit v.1 Q₀ T₀ _ hQ hT le_rfl
  have e := Equiv.ofBijective _ (finOrbitMap_bijective Q₀ hQ T₀ Ξ D hT le_rfl)
  haveI : Finite (FinOrbit Q₀ T₀ Ξ) := Finite.of_equiv _ e.symm
  haveI := Fintype.ofFinite (FinOrbit Q₀ T₀ Ξ)
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card,
    Nat.card_congr e, Nat.card_pi,
    tprod_eq_prod (s := towerBad Q₀ hQ T₀ Ξ D hT) (fun v hv => by
      rw [locCount_eq_one Q₀ hQ T₀ Ξ D hT v hv]; simp),
    ← Nat.cast_prod, ENNReal.ofReal_natCast, ← Finset.prod_coe_sort (towerBad Q₀ hQ T₀ Ξ D hT)]
  rfl

/-- **$\det(g)^2\det H_{Q_0} = \det H_{T_0}\det H_{Q''}$** for the adapted frame $g = [\Xi\mid C]$. -/
theorem det_adapted_sq :
    (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det ^ 2 * algebraMap (𝓞 F) F Q₀.hessian.det =
      algebraMap (𝓞 F) F T₀.hessian.det * algebraMap (𝓞 F) F D.Q''.hessian.det := by
  have e : ∀ {m : ℕ} (Q : QuadForm (𝓞 F) m),
      (Q.map (algebraMap (𝓞 F) F)).hessian.det = algebraMap (𝓞 F) F Q.hessian.det := fun Q => by
    rw [QuadFormsKB.Siegel.hessian_map_NF, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have h := congrArg Matrix.det (gram_adaptedMat Q₀ hQ T₀ Ξ D)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_hessian_blockForm, e, e, e] at h
  rw [towerAdapted_g_val]
  linear_combination h

open Classical in
/-- **The product formula behind the corank-one headlines**: for convergence factors $\lambda_v\ne0$ with
$\prod_vf_v/\lambda_v$ convergent ($f_v$ = `frameLocFactor`),
$$\prod_{w\mid\infty}|\det H_{Q_0}|_w^{-1}\cdot\prod_v\frac{f_v}{\lambda_v}\cdot\prod_va''_v = \prod_v\frac{\beta_v(L,T_0)}{\lambda_v},$$
from $f_v = \beta_v|\det g|_v^2|\det H_{T_0}|_v^{-1}$, $\prod_va''_v = \prod_w|\det H_{Q''}|_w$ (`tprod_aSO_rankOne`), the product
formula for $\det g$, $\det H_{T_0}$ and $\det(g)^2\det H_{Q_0} = \det H_{T_0}\det H_{Q''}$ (`det_adapted_sq`). -/
theorem densityIdentity_corankOne (lam : HeightOneSpectrum (𝓞 F) → ℝ) (hlam : ∀ v, lam v ≠ 0)
    (hm : Multipliable fun v => frameLocFactor Q₀ hQ T₀ Ξ D hT v / lam v) :
    ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w (algebraMap (𝓞 F) F Q₀.hessian.det)|⁻¹) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w (algebraMap (𝓞 F) F Q₀.hessian.det)‖ ^ 2)⁻¹) *
      ((∏' v, frameLocFactor Q₀ hQ T₀ Ξ D hT v / lam v) * ∏' v, aSO D.Q'' v) =
    ∏' v, NF.localDensityForm v Q₀ T₀ / lam v := by
  set G := (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det with hGdef
  set h := algebraMap (𝓞 F) F T₀.hessian.det with hhdef
  set q := algebraMap (𝓞 F) F Q₀.hessian.det with hqdef
  set e := algebraMap (𝓞 F) F D.Q''.hessian.det with hedef
  have hG : G ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
  have hh : h ≠ 0 := algebraMap_det_ne_zero T₀ hT
  have hq : q ≠ 0 := algebraMap_det_ne_zero Q₀ hQ
  have he : e ≠ 0 := algebraMap_det_ne_zero D.Q'' D.hQ''
  have hrel : G ^ 2 * q = h * e := det_adapted_sq Q₀ hQ T₀ Ξ D hT
  -- the finite parts
  have hGv : ∀ v : HeightOneSpectrum (𝓞 F), ‖σV v G‖ ≠ 0 := fun v => norm_ne_zero_iff.2 ((map_ne_zero _).2 hG)
  have hhv : ∀ v : HeightOneSpectrum (𝓞 F), ‖σV v h‖ ≠ 0 := fun v => norm_ne_zero_iff.2 ((map_ne_zero _).2 hh)
  have hfG := mulSupport_finite_norm (F := F) hG
  have hfh := mulSupport_finite_norm (F := F) hh
  set u : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖σV v G‖ ^ 2 * ‖σV v h‖⁻¹ with hu
  have hufin : (Function.mulSupport u).Finite := by
    refine (hfG.union hfh).subset fun v hv => ?_
    by_contra hcon
    apply hv
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hcon
    show ‖σV v G‖ ^ 2 * ‖σV v h‖⁻¹ = 1
    rw [hcon.1, hcon.2]; norm_num
  have huinvfin : (Function.mulSupport fun v => (u v)⁻¹).Finite := hufin.subset fun v hv => by
    intro h1; apply hv; show (u v)⁻¹ = 1; rw [show u v = 1 from h1, inv_one]
  have hu0 : ∀ v, u v ≠ 0 := fun v => mul_ne_zero (pow_ne_zero _ (hGv v)) (inv_ne_zero (hhv v))
  have hfu : ∀ v, frameLocFactor Q₀ hQ T₀ Ξ D hT v / lam v = NF.localDensityForm v Q₀ T₀ / lam v * u v := by
    intro v
    simp only [frameLocFactor, hu, ← hGdef, ← hhdef, pow_one]
    field_simp
  have hmβ : Multipliable fun v => NF.localDensityForm v Q₀ T₀ / lam v := by
    have : (fun v => NF.localDensityForm v Q₀ T₀ / lam v) =
        fun v => frameLocFactor Q₀ hQ T₀ Ξ D hT v / lam v * (u v)⁻¹ := by
      funext v; rw [hfu, mul_assoc, mul_inv_cancel₀ (hu0 v), mul_one]
    rw [this]
    exact hm.mul (multipliable_of_hasFiniteMulSupport huinvfin)
  have hprod : ∏' v, frameLocFactor Q₀ hQ T₀ Ξ D hT v / lam v =
      (∏' v, NF.localDensityForm v Q₀ T₀ / lam v) * ∏' v, u v := by
    rw [tprod_congr hfu]
    exact hmβ.tprod_mul (multipliable_of_hasFiniteMulSupport hufin)
  have hpow2 : (Function.mulSupport fun v => ‖σV v G‖ ^ 2).Finite := hfG.subset fun v hv => by
    intro h1; apply hv; show ‖σV v G‖ ^ 2 = 1; rw [show ‖σV v G‖ = 1 from h1, one_pow]
  have hinvh : (Function.mulSupport fun v => ‖σV v h‖⁻¹).Finite := hfh.subset fun v hv => by
    intro h1; apply hv; show ‖σV v h‖⁻¹ = 1; rw [show ‖σV v h‖ = 1 from h1, inv_one]
  have hUval : ∏' v, u v = (∏' v, ‖σV v G‖) ^ 2 * (∏' v, ‖σV v h‖)⁻¹ := by
    rw [tprod_eq_finprod hufin, tprod_eq_finprod hfG, tprod_eq_finprod hfh, finprod_mul_distrib hpow2 hinvh,
      finprod_inv_distrib, finprod_pow hfG]
  -- the archimedean parts and the product formula
  have hPG := prod_places_mul_tprod (F := F) hG
  have hPh := prod_places_mul_tprod (F := F) hh
  set Gs := (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w G|) *
    ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w G‖ ^ 2 with hGs
  set Hs := (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w h|) *
    ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w h‖ ^ 2 with hHs
  set Qs := (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w q|) *
    ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w q‖ ^ 2 with hQs
  set Es := (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w e|) *
    ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w e‖ ^ 2 with hEs
  have hGne : Gs ≠ 0 := left_ne_zero_of_mul_eq_one hPG
  have hHne : Hs ≠ 0 := left_ne_zero_of_mul_eq_one hPh
  have hQne : Qs ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => abs_ne_zero.2 ((map_ne_zero _).2 hq))
    (Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (norm_ne_zero_iff.2 ((map_ne_zero _).2 hq)))
  have hA : ∏' v, ‖σV v G‖ = Gs⁻¹ := eq_inv_of_mul_eq_one_right hPG
  have hB : ∏' v, ‖σV v h‖ = Hs⁻¹ := eq_inv_of_mul_eq_one_right hPh
  have hE : ∏' v, aSO D.Q'' v = Es := tprod_aSO_rankOne D.Q'' D.hQ''
  have hrelInf : Gs ^ 2 * Qs = Hs * Es := by
    have hR : ∀ w : {w : InfinitePlace F // w.IsReal}, |σR w G| ^ 2 * |σR w q| = |σR w h| * |σR w e| := by
      intro w
      have := congrArg (fun x => |σR w x|) hrel
      simpa [map_mul, map_pow, abs_mul, abs_pow] using this
    have hC : ∀ w : {w : InfinitePlace F // w.IsComplex},
        (‖σC w G‖ ^ 2) ^ 2 * ‖σC w q‖ ^ 2 = ‖σC w h‖ ^ 2 * ‖σC w e‖ ^ 2 := by
      intro w
      have := congrArg (fun x => ‖σC w x‖ ^ 2) hrel
      simp only [map_mul, map_pow, norm_mul, norm_pow, mul_pow] at this
      rw [← this]
    rw [hGs, hQs, hHs, hEs, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
    calc (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w G| ^ 2) *
          (∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w G‖ ^ 2) ^ 2) *
          ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w q|) *
            ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w q‖ ^ 2)
        = (∏ w : {w : InfinitePlace F // w.IsReal}, (|σR w G| ^ 2 * |σR w q|)) *
          ∏ w : {w : InfinitePlace F // w.IsComplex}, ((‖σC w G‖ ^ 2) ^ 2 * ‖σC w q‖ ^ 2) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]; ring
      _ = (∏ w : {w : InfinitePlace F // w.IsReal}, (|σR w h| * |σR w e|)) *
          ∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w h‖ ^ 2 * ‖σC w e‖ ^ 2) := by
          rw [Finset.prod_congr rfl fun w _ => hR w, Finset.prod_congr rfl fun w _ => hC w]
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]; ring
  have hQinv : (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w q|⁻¹) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w q‖ ^ 2)⁻¹ = Qs⁻¹ := by
    rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib, hQs, mul_inv]
  rw [hQinv, hprod, hUval, hA, hB, hE]
  have hEs : Es = Gs ^ 2 * Qs / Hs := by rw [hrelInf]; field_simp
  rw [hEs]
  field_simp

end Tower

end QuadFormsKB.Tamagawa.Indefinite
