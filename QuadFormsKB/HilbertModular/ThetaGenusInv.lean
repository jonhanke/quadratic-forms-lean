/-
# Theta series over $F$: the cusp data of $\theta_Q$ are genus invariants, prime by prime

Let $F$ be totally real and $Q, Q'$ forms over $\mathcal{O}_F$ in the same genus (`FormSameGenus`: equivalent over every
$\mathfrak o_\mathfrak p$ and every $\mathbb{R}$). This file shows that $\theta_Q$ and $\theta_{Q'}$ have **the same constant term at every
cusp** and hence the same character on $\Gamma_0(\mathfrak N)$, so that $\theta_Q - \theta_{Q'}$ is a cusp form.

**Local to global, prime by prime** (`FormSameGenus.isometricGL_quot`). For every nonzero ideal $I$ there is
$\bar g \in \mathrm{GL}_n(\mathcal{O}_F/I)$ with $\bar Q(\bar g x) = \bar Q'(x)$. *Proof:* for each prime $\mathfrak p^e \,\|\, I$ reduce the local
isometry $g_\mathfrak p \in \mathrm{GL}_n(\mathfrak o_\mathfrak p)$ along $\mathfrak o_\mathfrak p \to \mathfrak o_\mathfrak p/\varpi^e \cong \mathcal{O}_F/\mathfrak p^e$
(`LocalDensity.NF.quotEquiv`), and glue by the Chinese remainder theorem
$\mathcal{O}_F/I \cong \prod_{\mathfrak p^e\|I}\mathcal{O}_F/\mathfrak p^e$ (Mathlib's `IsDedekindDomain.quotientEquivPiFactors`, `IsometricGL.piRing`).

**Consequences.**
* `gaussSumF_eq_of_formSameGenus`: $G_Q(a, 0, c) = G_{Q'}(a, 0, c)$ (substitute $r \mapsto \bar g r$ in $(\mathcal{O}_F/c)^n$);
* `associated_det_hessian`: $\det H' = w\det H$ with $w \in \mathcal{O}_F^\times$ (modulo $\det H'$ and $\det H$);
* `prod_sqrt_det_gramF_eq`: $\prod_v\sqrt{\det\sigma_v(A_{Q'})} = \prod_v\sqrt{\det\sigma_v(A_Q)}$ for totally positive definite forms
  ($N(w) = 1$ as $w \gg 0$);
* `thetaCuspConst_eq`, `thetaMultF_eq`, `thetaMultG_eq`: the theta constants at every cusp agree;
* **`tendsto_thetaQ_slash_genus`**: $\lim\theta_Q\,|_k\,A = \lim\theta_{Q'}\,|_k\,A$ for every $A \in \mathrm{SL}_2(F)$, and
  `exists_tendsto_thetaQ_slash`: the limit exists at every cusp (`tendsto_thetaQ_slash`);
* **`thetaCharF_eq_of_formSameGenus`**: $\chi_Q = \chi_{Q'}$ for a common level $\mathfrak N$;
* `thetaQ_mem_modularFormChar'`: $\theta_Q \in M_k(\Gamma_0(\mathfrak N), \chi_Q)$ for **every** degree $d \ge 1$ (the cusp condition
  from the explicit limits, no Koecher);
* **`thetaQ_sub_mem_cuspFormChar`**: $\theta_Q - \theta_{Q'} \in S_k(\Gamma_0(\mathfrak N), \chi_Q)$.

Over $\mathbb{Q}$ this is `Siegel.ThetaCuspidal` (`SameGenus.isometricGL_zmod`, `SameGenus.gaussSum_eq`, `SameGenus.det_hessian_eq`).

Sources: Iwaniec, *Topics in Classical Automorphic Forms*, §10.4 (Gauss sums and the genus) [unverified]; Cassels,
*Rational Quadratic Forms*, Ch. 9 §1 (genus and congruences) [unverified]; Shimura (1973), §2 [unverified].
-/
import QuadFormsKB.HilbertModular.CuspClasses
import QuadFormsKB.HilbertModular.CuspValues
import QuadFormsKB.Lattices.Forms
import QuadFormsKB.LocalDensity.NFBridge
import QuadFormsKB.Siegel.ThetaCuspidal

open Matrix NumberField Complex Filter Topology IsDedekindDomain
open scoped MatrixGroups ModularForm nonZeroDivisors

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Siegel (IsometricGL)

/-! ### Equivalences over a product of rings, for any base ring -/

section Pi

variable {n : ℕ} {R : Type*} [CommRing R]

/-- **Equivalences glue over a product of rings** (any base ring $R$; the $\mathbb{Z}$-version is `Siegel.IsometricGL.pi`): if
$Q \sim Q'$ over every $T_i$ (via $f_i : R \to T_i$) then $Q \sim Q'$ over $\prod_iT_i$. -/
theorem IsometricGL.piRing {ι : Type*} {T : ι → Type*} [∀ i, CommRing (T i)] (f : ∀ i, R →+* T i)
    {Q Q' : QuadForm R n} (h : ∀ i, IsometricGL (Q.map (f i)) (Q'.map (f i))) :
    IsometricGL (Q.map (RingHom.pi f)) (Q'.map (RingHom.pi f)) := by
  choose g hg using h
  set G : Matrix (Fin n) (Fin n) (∀ i, T i) := Matrix.of fun a b i => (g i).val a b with hG
  set Gi : Matrix (Fin n) (Fin n) (∀ i, T i) := Matrix.of fun a b i => (g i)⁻¹.val a b with hGi
  have hmap : ∀ (M : ∀ j, Matrix (Fin n) (Fin n) (T j)) (i : ι),
      (Matrix.of fun a b j => M j a b : Matrix (Fin n) (Fin n) (∀ i, T i)).map (Pi.evalRingHom T i) =
        M i := fun M i => by ext a b; rfl
  have hinj : ∀ M M' : Matrix (Fin n) (Fin n) (∀ i, T i),
      (∀ i, M.map (Pi.evalRingHom T i) = M'.map (Pi.evalRingHom T i)) → M = M' := by
    intro M M' hM
    ext a b i
    have := congrFun (congrFun (hM i) a) b
    simpa using this
  have h1 : G * Gi = 1 := hinj _ _ fun i => by
    rw [Matrix.map_mul, hG, hGi, hmap (fun j => (g j).val), hmap (fun j => (g j)⁻¹.val),
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : Gi * G = 1 := hinj _ _ fun i => by
    rw [Matrix.map_mul, hG, hGi, hmap (fun j => (g j).val), hmap (fun j => (g j)⁻¹.val),
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨G, Gi, h1, h2⟩, fun x => ?_⟩
  change (Q.map (RingHom.pi f)).eval (G *ᵥ x) = _
  funext i
  have e1 := Siegel.map_eval_eq (Pi.evalRingHom T i) (Q.map (RingHom.pi f)) (G *ᵥ x)
  have e2 := Siegel.map_eval_eq (Pi.evalRingHom T i) (Q'.map (RingHom.pi f)) x
  rw [Lattices.QuadForm.map_map] at e1 e2
  have hc : (Pi.evalRingHom T i).comp (RingHom.pi f) = f i := by ext; rfl
  rw [hc] at e1 e2
  have e3 : (fun a => Pi.evalRingHom T i ((G *ᵥ x) a)) =
      (g i).val *ᵥ (fun a => Pi.evalRingHom T i (x a)) := by
    funext a
    rw [RingHom.map_mulVec, hG, hmap (fun j => (g j).val)]; rfl
  refine e1.trans (Eq.trans ?_ e2.symm)
  rw [e3]
  exact hg i _

end Pi

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-! ### From the genus to equivalence modulo an ideal (prime by prime) -/

/-- **Local equivalence reduces modulo $\mathfrak p^e$**: an equivalence over $\mathfrak o_\mathfrak p$ gives one over
$\mathcal{O}_F/\mathfrak p^e$, through $\mathfrak o_\mathfrak p \to \mathfrak o_\mathfrak p/\varpi^e \cong \mathcal{O}_F/\mathfrak p^e$. -/
theorem isometricGL_quot_pow {Q Q' : QuadForm (𝓞 F) n} (v : HeightOneSpectrum (𝓞 F)) (e : ℕ)
    (h : IsometricGL (Q.map (algebraMap (𝓞 F) (v.adicCompletionIntegers F)))
      (Q'.map (algebraMap (𝓞 F) (v.adicCompletionIntegers F)))) :
    IsometricGL (Q.map (Ideal.Quotient.mk (v.asIdeal ^ e))) (Q'.map (Ideal.Quotient.mk (v.asIdeal ^ e))) := by
  set g : v.adicCompletionIntegers F →+* 𝓞 F ⧸ v.asIdeal ^ e :=
    (LocalDensity.NF.quotEquiv v e).symm.toRingHom.comp (Ideal.Quotient.mk _) with hg
  have hgs : Function.Surjective g :=
    (LocalDensity.NF.quotEquiv v e).symm.surjective.comp Ideal.Quotient.mk_surjective
  have hcomp : g.comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) = Ideal.Quotient.mk _ := by
    ext a
    simp only [hg, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [RingEquiv.symm_apply_eq, LocalDensity.NF.quotEquiv_mk]
  have := h.map_of_surjective g hgs
  rwa [Lattices.QuadForm.map_map, Lattices.QuadForm.map_map, hcomp] at this

/-- **Forms in one genus are equivalent modulo every nonzero ideal** $I$ of $\mathcal{O}_F$: there is
$\bar g \in \mathrm{GL}_n(\mathcal{O}_F/I)$ with $\bar Q(\bar gx) = \bar Q'(x)$. *Proof:* prime by prime (`isometricGL_quot_pow`) and the
Chinese remainder theorem (`IsDedekindDomain.quotientEquivPiFactors`, `IsometricGL.piRing`). -/
@[kb "cassels1978" "Ch. 9, §1 (genus and congruences), over 𝓞_F [unverified]"]
theorem _root_.QuadFormsKB.Lattices.FormSameGenus.isometricGL_quot {Q Q' : QuadForm (𝓞 F) n} (h : Lattices.FormSameGenus Q Q')
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    IsometricGL (Q.map (Ideal.Quotient.mk I)) (Q'.map (Ideal.Quotient.mk I)) := by
  classical
  set fac := UniqueFactorizationMonoid.factors I
  have hprime : ∀ P ∈ fac, P.IsPrime ∧ P ≠ ⊥ := by
    intro P hP
    have hp := UniqueFactorizationMonoid.prime_of_factor P hP
    exact ⟨(Ideal.prime_iff_isPrime hp.ne_zero).mp hp, hp.ne_zero⟩
  set vP : fac.toFinset → HeightOneSpectrum (𝓞 F) := fun P =>
    ⟨P.1, (hprime P.1 (Multiset.mem_toFinset.mp P.2)).1, (hprime P.1 (Multiset.mem_toFinset.mp P.2)).2⟩
  have hloc : ∀ P : fac.toFinset, IsometricGL (Q.map (Ideal.Quotient.mk ((P : Ideal (𝓞 F)) ^ fac.count (P : Ideal (𝓞 F)))))
      (Q'.map (Ideal.Quotient.mk ((P : Ideal (𝓞 F)) ^ fac.count (P : Ideal (𝓞 F))))) := fun P =>
    isometricGL_quot_pow (vP P) (fac.count (P : Ideal (𝓞 F))) (h.1 (vP P))
  have hpi := IsometricGL.piRing (fun P : fac.toFinset =>
    Ideal.Quotient.mk ((P : Ideal (𝓞 F)) ^ fac.count (P : Ideal (𝓞 F)))) hloc
  set e := IsDedekindDomain.quotientEquivPiFactors hI
  have := hpi.map_of_surjective e.symm.toRingHom e.symm.surjective
  have hcomp : e.symm.toRingHom.comp (RingHom.pi fun P : fac.toFinset =>
      Ideal.Quotient.mk ((P : Ideal (𝓞 F)) ^ fac.count (P : Ideal (𝓞 F)))) = Ideal.Quotient.mk I := by
    ext a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [RingEquiv.symm_apply_eq]
    funext P
    rw [IsDedekindDomain.quotientEquivPiFactors_mk]
    rfl
  rwa [Lattices.QuadForm.map_map, Lattices.QuadForm.map_map, hcomp] at this

/-! ### Gauss sums are genus invariants -/

/-- $e(\operatorname{Tr}(y/c))$ for $y, c \in \mathcal{O}_F$. -/
noncomputable def eTrO (y c : 𝓞 F) : ℂ :=
  cexp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (algebraMap (𝓞 F) F y / algebraMap (𝓞 F) F c) : ℚ) : ℂ))

/-- $e(\operatorname{Tr}(y/c))$ depends only on $y \bmod c$. -/
lemma eTrO_congr {c y y' : 𝓞 F} (hc : c ≠ 0)
    (h : Ideal.Quotient.mk (Ideal.span {c}) y = Ideal.Quotient.mk (Ideal.span {c}) y') :
    eTrO y c = eTrO y' c := by
  obtain ⟨t, rfl⟩ := exists_eq_add_mul_of_mk_eq h
  have hc' : algebraMap (𝓞 F) F c ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective (𝓞 F) F).ne hc
  have : algebraMap (𝓞 F) F (y' + c * t) / algebraMap (𝓞 F) F c =
      algebraMap (𝓞 F) F y' / algebraMap (𝓞 F) F c + algebraMap (𝓞 F) F t := by
    rw [map_add, map_mul]; field_simp
  rw [eTrO, eTrO, this, cexp_trace_add_of_mem (algebraMap_mem_invDifferent t)]

lemma gsTermF_zero_eq (Q : QuadForm (𝓞 F) n) (a c : 𝓞 F) (x : Fin n → 𝓞 F) :
    gsTermF Q a c 0 x = eTrO (a * Q.eval x) c := by
  rw [gsTermF, eTrO, qv_vecO, zero_dotProduct, add_zero, map_mul]

/-- **The Gauss sum $G_Q(a, 0, c)$ through the reduction $\bar Q$ of $Q$ modulo $c$**:
$G_Q(a, 0, c) = \sum_{r\in(\mathcal{O}_F/c)^n}e\big(\operatorname{Tr}(a\,\widetilde{\bar Q(r)}/c)\big)$ for any lift $\tilde{\ }$. -/
lemma gaussSumF_zero_eq_sum_map (Q : QuadForm (𝓞 F) n) (a : 𝓞 F) {c : 𝓞 F} (hc : c ≠ 0)
    [Fintype (𝓞 F ⧸ Ideal.span {c})] :
    gaussSumF Q a c 0 = ∑ r : Fin n → 𝓞 F ⧸ Ideal.span {c},
      eTrO (a * qlift ((Q.map (Ideal.Quotient.mk (Ideal.span {c}))).eval r)) c := by
  rw [gaussSumF_eq_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [gsTermF_zero_eq]
  refine eTrO_congr hc ?_
  rw [map_mul, map_mul, mk_qlift, Siegel.map_eval_eq]
  simp only [mk_qlift]

/-- **Equivalent forms modulo $c$ have equal Gauss sums**: substitute $r \mapsto \bar gr$. -/
theorem gaussSumF_eq_of_isometricGL {Q Q' : QuadForm (𝓞 F) n} {c : 𝓞 F} (hc : c ≠ 0)
    (h : IsometricGL (Q.map (Ideal.Quotient.mk (Ideal.span {c})))
      (Q'.map (Ideal.Quotient.mk (Ideal.span {c})))) (a : 𝓞 F) :
    gaussSumF Q a c 0 = gaussSumF Q' a c 0 := by
  have := finite_quot_span hc
  letI := Fintype.ofFinite (𝓞 F ⧸ Ideal.span {c})
  classical
  obtain ⟨g, hg⟩ := h
  rw [gaussSumF_zero_eq_sum_map Q a hc, gaussSumF_zero_eq_sum_map Q' a hc]
  let e : (Fin n → 𝓞 F ⧸ Ideal.span {c}) ≃ (Fin n → 𝓞 F ⧸ Ideal.span {c}) :=
    { toFun := fun r => g.val *ᵥ r
      invFun := fun r => (g⁻¹).val *ᵥ r
      left_inv := fun r => by
        simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      right_inv := fun r => by
        simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] }
  exact (Fintype.sum_equiv e _ _ fun r => by simp only [e, Equiv.coe_fn_mk, hg]).symm

/-- **Gauss sums are genus invariants** over $\mathcal{O}_F$: $G_Q(a, 0, c) = G_{Q'}(a, 0, c)$ for $Q'$ in the genus of $Q$,
all $a \in \mathcal{O}_F$ and $c \ne 0$. The proof is local, prime by prime (`FormSameGenus.isometricGL_quot`). -/
@[kb "iwaniec1997" "§10.4, Gauss sums of a genus (over 𝓞_F) [unverified]"]
theorem gaussSumF_eq_of_formSameGenus {Q Q' : QuadForm (𝓞 F) n} (h : Lattices.FormSameGenus Q Q')
    (a : 𝓞 F) {c : 𝓞 F} (hc : c ≠ 0) :
    gaussSumF Q a c 0 = gaussSumF Q' a c 0 :=
  gaussSumF_eq_of_isometricGL hc (h.isometricGL_quot (by simpa using hc)) a

/-! ### The determinant -/

/-- $\det H$ is a genus invariant up to a unit: modulo $c$, $\det H' = \det(\bar g)^2\det H$ with $\bar g$ invertible. -/
lemma det_hessian_dvd {Q Q' : QuadForm (𝓞 F) n} (h : Lattices.FormSameGenus Q Q')
    (hD' : Q'.hessian.det ≠ 0) : Q'.hessian.det ∣ Q.hessian.det := by
  set I := Ideal.span {Q'.hessian.det}
  obtain ⟨g, hg⟩ := (h.isometricGL_quot (I := I) (by simpa [I] using hD')).hessian_eq
  have hd := congrArg Matrix.det hg
  have e : ∀ M : Matrix (Fin n) (Fin n) (𝓞 F), (M.map (Ideal.Quotient.mk I)).det =
      Ideal.Quotient.mk I M.det := fun M => by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [Siegel.hessian_map, Siegel.hessian_map, det_mul, det_mul, det_transpose, e, e] at hd
  have h0 : Ideal.Quotient.mk I Q'.hessian.det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span rfl)
  rw [h0] at hd
  have hu : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  have : Ideal.Quotient.mk I Q.hessian.det = 0 := by
    have h2 : g.val.det * (Ideal.Quotient.mk I Q.hessian.det * g.val.det) = 0 := by
      rw [← mul_assoc]; exact hd
    have h3 := hu.mul_right_eq_zero.mp h2
    exact (hu.mul_left_eq_zero).mp h3
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp this)

/-- **The determinant of the Hessian is a genus invariant up to a unit**: $\det H' = w\det H$, $w \in \mathcal{O}_F^\times$. -/
theorem associated_det_hessian {Q Q' : QuadForm (𝓞 F) n} (h : Lattices.FormSameGenus Q Q')
    (hD : Q.hessian.det ≠ 0) (hD' : Q'.hessian.det ≠ 0) : Associated Q.hessian.det Q'.hessian.det :=
  associated_of_dvd_dvd (det_hessian_dvd h.symm hD) (det_hessian_dvd h hD')

lemma det_hessian_ne_zero {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) : Q.hessian.det ≠ 0 := by
  intro h
  apply hessF_det_ne_zero hQ
  rw [hessF, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]

lemma det_gramF_map (Q : QuadForm (𝓞 F) n) (v : InfinitePlace F) :
    ((gramF Q).map (realEmb F v)).det =
      realEmb F v ((1 / 2 : F) ^ n * algebraMap (𝓞 F) F Q.hessian.det) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, gramF_eq, det_smul, Fintype.card_fin, hessF,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det]

/-- **The archimedean factor of the theta constants is a genus invariant**: for totally positive definite $Q, Q'$ in one
genus, $\prod_v\sqrt{\det\sigma_v(A_{Q'})} = \prod_v\sqrt{\det\sigma_v(A_Q)}$. *Proof:* $\det H' = w\det H$ with $w$ a unit
(`associated_det_hessian`), $\sigma_v(w) > 0$ (both determinants are), so $N(w) = |N(w)| = 1$. -/
theorem prod_sqrt_det_gramF_eq {Q Q' : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q))
    (hQ' : IsTotPosGram (gramF Q')) (h : Lattices.FormSameGenus Q Q') :
    ∏ v, Real.sqrt ((gramF Q').map (realEmb F v)).det = ∏ v, Real.sqrt ((gramF Q).map (realEmb F v)).det := by
  obtain ⟨u, hu⟩ := associated_det_hessian h (det_hessian_ne_zero hQ) (det_hessian_ne_zero hQ')
  have hx : ∀ v, 0 < ((gramF Q).map (realEmb F v)).det := fun v => (hQ v).det_pos
  have hx' : ∀ v, 0 < ((gramF Q').map (realEmb F v)).det := fun v => (hQ' v).det_pos
  have hrel : ∀ v, ((gramF Q').map (realEmb F v)).det =
      ((gramF Q).map (realEmb F v)).det * realEmb F v (u : F) := by
    intro v
    rw [det_gramF_map, det_gramF_map, ← hu, map_mul, map_mul, map_mul, map_mul, mul_assoc]
  have hupos : ∀ v, 0 < realEmb F v (u : F) := fun v => by
    have := hx' v; rw [hrel v] at this; exact pos_of_mul_pos_right this (hx v).le
  have hN : ∏ v, Real.sqrt (realEmb F v (u : F)) = 1 := by
    have hsq : (∏ v, Real.sqrt (realEmb F v (u : F))) ^ 2 = 1 := by
      rw [← Finset.prod_pow]
      simp_rw [Real.sq_sqrt (hupos _).le]
      have h1 := abs_unitNorm u
      rw [unitNorm, abs_of_pos (Finset.prod_pos fun v _ => hupos v)] at h1
      exact h1
    have hnn : 0 ≤ ∏ v, Real.sqrt (realEmb F v (u : F)) := Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _
    nlinarith [sq_nonneg (∏ v, Real.sqrt (realEmb F v (u : F)) - 1)]
  simp_rw [hrel, Real.sqrt_mul (hx _).le]
  rw [Finset.prod_mul_distrib, hN, mul_one]

/-! ### The theta constants at every cusp are genus invariants -/

/-- The constant of `tendsto_thetaQ_slash` is a genus invariant. -/
theorem thetaCuspConst_eq {Q Q' : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q))
    (hQ' : IsTotPosGram (gramF Q')) (h : Lattices.FormSameGenus Q Q') (k : ℕ) (D c : 𝓞 F) :
    thetaCuspConst Q' k D c = thetaCuspConst Q k D c := by
  rw [thetaCuspConst, thetaCuspConst, prod_sqrt_det_gramF_eq hQ hQ' h]

/-- The theta multiplier $M_Q(a, c)$ is a genus invariant. -/
theorem thetaMultF_eq {Q Q' : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q))
    (hQ' : IsTotPosGram (gramF Q')) (h : Lattices.FormSameGenus Q Q') (k : ℕ) (a : 𝓞 F) {c : 𝓞 F}
    (hc : c ≠ 0) : thetaMultF Q' k a c = thetaMultF Q k a c := by
  rw [thetaMultF, thetaMultF, prod_sqrt_det_gramF_eq hQ hQ' h, gaussSumF_eq_of_formSameGenus h a hc]

/-- The multiplier $m_Q(\gamma)$ on $\Gamma_0(\mathfrak N)$ is a genus invariant. -/
theorem thetaMultG_eq {Q Q' : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q))
    (hQ' : IsTotPosGram (gramF Q')) (h : Lattices.FormSameGenus Q Q') (k : ℕ) (γ : SL(2, 𝓞 F)) :
    thetaMultG Q' k γ = thetaMultG Q k γ := by
  unfold thetaMultG
  split_ifs with hc
  · rfl
  · exact thetaMultF_eq hQ hQ' h k _ hc

/-! ### Limits at every cusp -/

/-- A common denominator of the first column of $A \in \mathrm{SL}_2(F)$: $D \ne 0$ in $\mathcal{O}_F$ with $DA_{00}, DA_{10} \in \mathcal{O}_F$. -/
lemma exists_cuspDenom (A : SL(2, F)) : ∃ D : 𝓞 F, D ≠ 0 ∧ ∃ a c : 𝓞 F,
    algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F D * A 0 0 ∧
      algebraMap (𝓞 F) F c = algebraMap (𝓞 F) F D * A 1 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (𝓞 F)⁰ ({A 0 0, A 1 0} : Finset F)
  obtain ⟨a, ha⟩ := hb (A 0 0) (by simp)
  obtain ⟨c, hc⟩ := hb (A 1 0) (by simp)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, a, c, ?_, ?_⟩
  · rw [ha, Algebra.smul_def]
  · rw [hc, Algebra.smul_def]

/-- **The constant term of $\theta_Q$ at the cusp $A\infty$** (rank $n = 2k$), as an explicit value: $N(A_{00})^k$ if $A_{10} = 0$, else
$K_Q\prod_v(\frac{-i}{2\sigma_v(c)\sigma_v(D)})^kG_Q(a, 0, c)$ for the common denominator $D$ chosen by `exists_cuspDenom` (`tendsto_thetaQ_slash`). -/
noncomputable def thetaCuspVal (Q : QuadForm (𝓞 F) n) (k : ℕ) (A : SL(2, F)) : ℂ :=
  haveI := Classical.propDecidable
  if A 1 0 = 0 then (∏ v, (realEmb F v (A 0 0) : ℂ)) ^ (k : ℤ) else
    thetaCuspConst Q k (exists_cuspDenom A).choose
        (exists_cuspDenom A).choose_spec.2.choose_spec.choose *
      gaussSumF Q (exists_cuspDenom A).choose_spec.2.choose
        (exists_cuspDenom A).choose_spec.2.choose_spec.choose 0

/-- **$\theta_Q$ has a constant term at every cusp** (`tendsto_thetaQ_slash`, `tendsto_thetaQ_slash_of_c_eq_zero`). -/
theorem tendsto_thetaQ_slash_thetaCuspVal {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) (A : SL(2, F)) :
    Tendsto (thetaQ Q ∣[(k : ℤ)] slHom (realEmb F) A) atImInftyPi (𝓝 (thetaCuspVal Q k A)) := by
  classical
  unfold thetaCuspVal
  split_ifs with hc
  · exact tendsto_thetaQ_slash_of_c_eq_zero hQ k A hc
  · obtain ⟨hD, hspec⟩ := (exists_cuspDenom A).choose_spec
    obtain ⟨ha, hc'⟩ := hspec.choose_spec.choose_spec
    exact tendsto_thetaQ_slash hQ hn A hc hD ha hc'

theorem hasCuspLimits_thetaQ {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) : HasCuspLimits (thetaQ Q) k :=
  fun A => ⟨_, tendsto_thetaQ_slash_thetaCuspVal hQ hn A⟩

/-- **The constant terms of $\theta_Q$ at every cusp are genus invariants**: $\mathrm{cv}(\theta_{Q'}, A) = \mathrm{cv}(\theta_Q, A)$
for every $A \in \mathrm{SL}_2(F)$. -/
@[kb "iwaniec1997" "§10.4, the constant terms of θ_Q at the cusps depend only on the genus [unverified]"]
theorem thetaCuspVal_eq_of_formSameGenus {Q Q' : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q))
    (hQ' : IsTotPosGram (gramF Q')) (h : Lattices.FormSameGenus Q Q') (k : ℕ) (A : SL(2, F)) :
    thetaCuspVal Q' k A = thetaCuspVal Q k A := by
  classical
  unfold thetaCuspVal
  split_ifs with hc
  · rfl
  · obtain ⟨hD, hspec⟩ := (exists_cuspDenom A).choose_spec
    obtain ⟨ha, hc'⟩ := hspec.choose_spec.choose_spec
    have hcF : algebraMap (𝓞 F) F (exists_cuspDenom A).choose_spec.2.choose_spec.choose ≠ 0 := by
      rw [hc']
      exact mul_ne_zero ((map_ne_zero_iff _ algebraMap_O_injective).mpr hD) hc
    have hc0 : (exists_cuspDenom A).choose_spec.2.choose_spec.choose ≠ 0 := fun h0 => hcF (by rw [h0, map_zero])
    rw [thetaCuspConst_eq hQ hQ' h, gaussSumF_eq_of_formSameGenus h _ hc0]

/-- **$\theta_Q$ and $\theta_{Q'}$ have the same constant term at every cusp** (for $Q'$ in the genus of $Q$). -/
@[kb "iwaniec1997" "§10.4 [unverified]"]
theorem cuspVal_thetaQ_eq_of_formSameGenus {Q Q' : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q))
    (hQ' : IsTotPosGram (gramF Q')) (h : Lattices.FormSameGenus Q Q') {k : ℕ} (hn : n = 2 * k)
    (A : SL(2, F)) : cuspVal (thetaQ Q') k A = cuspVal (thetaQ Q) k A := by
  rw [cuspVal_eq_of_tendsto (tendsto_thetaQ_slash_thetaCuspVal hQ' hn A),
    cuspVal_eq_of_tendsto (tendsto_thetaQ_slash_thetaCuspVal hQ hn A),
    thetaCuspVal_eq_of_formSameGenus hQ hQ' h]

/-! ### The character and cuspidality -/

/-- **The theta character is a genus invariant**: $\chi_{Q'} = \chi_Q$ on $\mathcal{O}_F/\mathfrak N$ for a common level $\mathfrak N$
(both are the multiplier $m(\gamma)$, which is a genus invariant, `thetaMultG_eq`). -/
@[kb "shimura1973" "§2, the character of θ depends only on the genus [unverified]"]
theorem thetaCharF_eq_of_formSameGenus {Q Q' : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q))
    (hQ' : IsTotPosGram (gramF Q')) (h : Lattices.FormSameGenus Q Q') {k : ℕ} (hn : n = 2 * k)
    {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (hlev' : IsThetaLevelF Q' 𝔑) (h𝔑 : 𝔑 ≠ ⊥) :
    thetaCharF hQ' hn hlev' h𝔑 = thetaCharF hQ hn hlev h𝔑 := by
  refine MulChar.ext fun u => ?_
  simp only [thetaCharF, MulChar.ofUnitHom_coe, thetaCharHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Units.val_mk0]
  exact thetaMultG_eq hQ hQ' h k _

/-- **$\theta_Q \in M_k(\Gamma_0(\mathfrak N), \chi_Q)$ for every totally real $F$**, including $F = \mathbb{Q}$ ($d = 1$): the cusp
condition comes from the explicit constant terms (`hasCuspLimits_thetaQ`), not from Koecher's principle as in
`thetaQ_mem_modularFormChar` ($d \ge 2$). -/
@[kb "shimura1973" "§2, θ_Q ∈ M_k(Γ₀(𝔑), χ_Q) [unverified]"]
theorem thetaQ_mem_modularFormChar' {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥) :
    thetaQ Q ∈ modularFormChar 𝔑 (thetaCharF hQ hn hlev h𝔑) k := by
  refine ⟨⟨?_, isHolomorphic_thetaQ hQ, fun A => ?_⟩,
    fun γ hγ => thetaQ_slash_gamma0_char hQ hn hlev h𝔑 hγ⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    obtain ⟨hγ0, hγ1⟩ := (mem_Gamma1R 𝔑).mp hγ
    rw [thetaQ_slash_gamma0_char hQ hn hlev h𝔑 hγ0, hγ1, MulChar.map_one, one_smul]
  · exact (tendsto_thetaQ_slash_thetaCuspVal hQ hn A).isBigO_one ℝ

/-- **$\theta_{Q'} - \theta_Q$ is a cusp form** for $Q'$ in the genus of $Q$: it lies in $S_k(\Gamma_0(\mathfrak N), \chi_Q)$ for every
common level $\mathfrak N \ne 0$ (`cuspFormChar`). Over $\mathbb{Q}$: `Siegel.thetaCuspDiff`. -/
@[kb "iwaniec1997" "§10.4, θ_Q − θ_Q' is a cusp form for Q' in the genus of Q [unverified]"]
theorem thetaQ_sub_mem_cuspFormChar {Q Q' : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q))
    (hQ' : IsTotPosGram (gramF Q')) (h : Lattices.FormSameGenus Q Q') {k : ℕ} (hn : n = 2 * k)
    {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (hlev' : IsThetaLevelF Q' 𝔑) (h𝔑 : 𝔑 ≠ ⊥) :
    thetaQ Q' - thetaQ Q ∈ cuspFormChar 𝔑 (thetaCharF hQ hn hlev h𝔑) k := by
  have h1 := thetaQ_mem_modularFormChar' hQ hn hlev h𝔑
  have h2 := thetaQ_mem_modularFormChar' hQ' hn hlev' h𝔑
  rw [thetaCharF_eq_of_formSameGenus hQ hQ' h hn hlev hlev' h𝔑] at h2
  have hsub := (modularFormChar 𝔑 (thetaCharF hQ hn hlev h𝔑) k).sub_mem h2 h1
  refine ⟨⟨hsub.1.1, hsub.1.2.1, fun A => ?_⟩, hsub⟩
  have t1 := tendsto_thetaQ_slash_thetaCuspVal hQ' hn A
  rw [thetaCuspVal_eq_of_formSameGenus hQ hQ' h] at t1
  exact isZeroAtImInftyPi_sub t1 (tendsto_thetaQ_slash_thetaCuspVal hQ hn A)

/-! ### The level is a genus invariant -/

/-- $Q^\#(y) = \frac12(\operatorname{alg}\det H)^{-1}\,y^{\mathsf T}\operatorname{adj}(H)y$. -/
lemma qDual_eq_adj {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) (y : Fin n → F) :
    qDual Q y = (1 / 2 : F) * (algebraMap (𝓞 F) F Q.hessian.det)⁻¹ *
      (y ⬝ᵥ (Q.hessian.adjugate.map (algebraMap (𝓞 F) F)) *ᵥ y) := by
  rw [qDual_eq hQ, Matrix.inv_def, hessF, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    ← RingHom.map_adjugate, RingHom.mapMatrix_apply, Ring.inverse_eq_inv', smul_mulVec,
    dotProduct_smul, smul_eq_mul, mul_assoc]

lemma dotProduct_mul_mul_transpose (A B : Matrix (Fin n) (Fin n) F) (y : Fin n → F) :
    y ⬝ᵥ (A * B * Aᵀ) *ᵥ y = (Aᵀ *ᵥ y) ⬝ᵥ B *ᵥ (Aᵀ *ᵥ y) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, mulVec_transpose,
    dotProduct_mulVec]

/-- **The theta level is a genus invariant**: if $\mathfrak N$ is a level of $Q$ (`IsThetaLevelF`) and $Q'$ is in the genus of
$Q$ (both totally positive definite), then $\mathfrak N$ is a level of $Q'$.

*Proof:* let $c = 2\det(H)\,\delta$ with $0 \ne \delta \in \mathfrak d$. Modulo $c$, $H' \equiv P^{\mathsf T}HP$ with $P$ invertible modulo $c$
(`FormSameGenus.isometricGL_quot`), so $\operatorname{adj}H' = \operatorname{adj}(P)\operatorname{adj}(H)\operatorname{adj}(P)^{\mathsf T} + cE$ with $E$
integral, and $\det H' = w\det H$, $w \in \mathcal{O}_F^\times$ (`associated_det_hessian`). Hence
$Q'^\#(y) = w^{-1}\big(Q^\#(\operatorname{adj}(P)^{\mathsf T}y) + \delta\,y^{\mathsf T}Ey\big)$, and for $\nu \in \mathfrak N$, $y \in (\mathfrak d^{-1})^n$ both
$\nu Q^\#(\operatorname{adj}(P)^{\mathsf T}y)$ and $\nu\delta\,y^{\mathsf T}Ey$ lie in $\mathfrak d^{-1}$ ($\delta\mathfrak d^{-1} \subseteq \mathcal{O}_F$). -/
@[kb "shimura1973" "§2, the level of a theta series depends only on the genus [unverified]"]
theorem isThetaLevelF_of_formSameGenus {Q Q' : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q))
    (hQ' : IsTotPosGram (gramF Q')) (h : Lattices.FormSameGenus Q Q') {𝔑 : Ideal (𝓞 F)}
    (hlev : IsThetaLevelF Q 𝔑) : IsThetaLevelF Q' 𝔑 := by
  have hD := det_hessian_ne_zero hQ
  obtain ⟨u, hu⟩ := associated_det_hessian h hD (det_hessian_ne_zero hQ')
  obtain ⟨δ, hδ, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  set D := Q.hessian.det with hDdef
  set c : 𝓞 F := 2 * D * δ with hcdef
  have h2 : (2 : 𝓞 F) ≠ 0 := two_ne_zero
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero h2 hD) hδ0
  set mk := Ideal.Quotient.mk (Ideal.span {c})
  obtain ⟨g, hg⟩ := (h.isometricGL_quot (I := Ideal.span {c}) (by simpa using hc)).hessian_eq
  rw [Siegel.hessian_map, Siegel.hessian_map] at hg
  choose P hP using fun i j => Ideal.Quotient.mk_surjective (g.val i j)
  set Pm : Matrix (Fin n) (Fin n) (𝓞 F) := Matrix.of P with hPmdef
  have hPm : Pm.map mk = g.val := by ext i j; simp [Pm, hP, mk]
  set R := Pmᵀ * Q.hessian * Pm with hRdef
  have hR : R.map mk = Q'.hessian.map mk := by
    rw [hRdef, Matrix.map_mul, Matrix.map_mul, transpose_map, hPm]; exact hg
  have hadj : (Q'.hessian.adjugate).map mk = R.adjugate.map mk := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, RingHom.map_adjugate,
      RingHom.map_adjugate, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hR]
  choose E hE using fun i j => exists_eq_add_mul_of_mk_eq (congrFun (congrFun hadj i) j)
  have hRadj : R.adjugate = Pm.adjugate * Q.hessian.adjugate * Pm.adjugateᵀ := by
    rw [hRdef, adjugate_mul_distrib, adjugate_mul_distrib, adjugate_transpose, mul_assoc]
  set alg := algebraMap (𝓞 F) F
  have hDF : alg D ≠ 0 := (map_ne_zero_iff _ algebraMap_O_injective).mpr hD
  have huF : alg (u : 𝓞 F) ≠ 0 := (map_ne_zero_iff _ algebraMap_O_injective).mpr u.ne_zero
  have hD' : Q'.hessian.det = D * u := hu.symm
  intro ν hν y hy
  set A := Pm.adjugate.map alg
  set z := Aᵀ *ᵥ y
  have hz : ∀ i, z i ∈ invDifferent F := by
    intro i
    simp only [z, mulVec, dotProduct, transpose_apply]
    exact Submodule.sum_mem _ fun j _ => by
      simp only [A, Matrix.map_apply]; exact algebraMap_mul_mem_invDifferent _ (hy j)
  set T₂ := y ⬝ᵥ (Matrix.of E).map alg *ᵥ y
  have hkey : y ⬝ᵥ (Q'.hessian.adjugate.map alg) *ᵥ y =
      z ⬝ᵥ (Q.hessian.adjugate.map alg) *ᵥ z + alg c * T₂ := by
    have hm0 : Q'.hessian.adjugate = R.adjugate + c • Matrix.of E := by
      ext i j; rw [hE i j]; simp
    have hm : Q'.hessian.adjugate.map alg =
        A * Q.hessian.adjugate.map alg * Aᵀ + alg c • (Matrix.of E).map alg := by
      rw [hm0, Matrix.map_add _ (map_add alg), hRadj, Matrix.map_mul, Matrix.map_mul, transpose_map,
        Matrix.map_smul _ c (fun a => by rw [smul_eq_mul, map_mul, Algebra.smul_def])]
      congr 1
    rw [hm, add_mulVec, dotProduct_add, dotProduct_mul_mul_transpose, smul_mulVec, dotProduct_smul,
      smul_eq_mul]
  have hq' : qDual Q' y = (alg (u : 𝓞 F))⁻¹ * (qDual Q z + alg δ * T₂) := by
    rw [qDual_eq_adj hQ', hkey, qDual_eq_adj hQ z, hD', map_mul]
    simp only [alg, hcdef, map_mul, map_ofNat, ← hDdef] at hDF huF ⊢
    field_simp
  have hinv : (alg (u : 𝓞 F))⁻¹ = alg ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) :=
    (eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])).symm
  rw [hq', hinv]
  rw [show alg ν * (alg ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (qDual Q z + alg δ * T₂)) =
    alg ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (alg ν * qDual Q z) +
      alg ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (alg ν * (alg δ * T₂)) by ring]
  refine Submodule.add_mem _ (algebraMap_mul_mem_invDifferent _ (hlev ν hν z hz))
    (algebraMap_mul_mem_invDifferent _ (algebraMap_mul_mem_invDifferent _ ?_))
  -- `δ yᵀEy ∈ 𝔡⁻¹`
  simp only [T₂, dotProduct, mulVec, Finset.mul_sum]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp (mul_mem_one_of_mem_differentIdeal hδ (hy i))
  rw [show alg δ * (y i * ((Matrix.of E).map alg i j * y j)) =
    (alg δ * y i) * (alg (E i j) * y j) by simp [Matrix.map_apply]; ring, ← hr]
  exact algebraMap_mul_mem_invDifferent _ (algebraMap_mul_mem_invDifferent _ (hy j))

end QuadFormsKB.HilbertModular
