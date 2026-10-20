import QuadFormsKB.Tamagawa.BinaryCMAssembly

/-!
# The constants of the CM extension $E = F(\sqrt{-D})$

**Layer:** $F$ totally real, $E = F(\theta)$ with $\theta^2 = -D$ and $D \gg 0$ (`SqrtData`), $n = [F:\mathbb Q]$.

**Proves**
* `regulator_eq_of_ringEquiv`: isomorphic number fields have the same regulator (a fundamental system is carried to one; the regulator matrices
  agree after reindexing the places by `comap`);
* `isTotallyComplex_of_sqrtData`: $E$ is totally complex ($\sigma(\theta)^2 = -\sigma(D) < 0$ at a real place); hence $E$ is a CM field
  (Mathlib's `IsCMField.ofCMExtension`) with $E^+ \cong F$;
* `conj_eq_complexConj'`, `indexRealUnits_mul_index_conjQuotGroup'`: $Q_E\cdot[\mu_E : \{u/\sigma u\}] = 2$ (Mathlib's
  `IsCMField.indexRealUnits_mul_eq`, transported from $E^+$ to $F$);
* **`regulator_eq_cm`**: $2R_E = 2^{n-1}\,[\mu_E : \{u/\sigma u\}]\,R_F$, i.e. $R_E = 2^{n-2}\,\mathrm{idx}\,R_F$ (Mathlib's
  `IsCMField.regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv`).

Source: Washington 1997, Ch. 4, Prop. 4.16 and Thm. 4.12 [unverified locator].

-/

open NumberField NumberField.InfinitePlace NumberField.Units Matrix IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.BinaryCM

/-! ### The regulator is an isomorphism invariant -/

section RegIso

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

/-- The infinite places of $L$ and of $K$ correspond along $f : K \simeq L$ (`comap`). -/
def placeEquiv (f : K ≃+* L) : InfinitePlace L ≃ InfinitePlace K where
  toFun w := w.comap (f : K →+* L)
  invFun w := w.comap (f.symm : L →+* K)
  left_inv w := by
    show w.comap ((f : K →+* L).comp (f.symm : L →+* K)) = w
    rw [show (f : K →+* L).comp (f.symm : L →+* K) = RingHom.id L by ext; simp, comap_id]
  right_inv w := by
    show w.comap ((f.symm : L →+* K).comp (f : K →+* L)) = w
    rw [show (f.symm : L →+* K).comp (f : K →+* L) = RingHom.id K by ext; simp, comap_id]

theorem placeEquiv_apply (f : K ≃+* L) (w : InfinitePlace L) (x : K) : placeEquiv f w x = w (f x) := rfl

theorem mult_placeEquiv (f : K ≃+* L) (w : InfinitePlace L) : mult (placeEquiv f w) = mult w := by
  simp only [mult]
  rw [show placeEquiv f w = w.comap (f : K →+* L) from rfl, isReal_comap_iff f]

theorem rank_eq_of_ringEquiv (f : K ≃+* L) : Units.rank L = Units.rank K := by
  unfold Units.rank; rw [Fintype.card_congr (placeEquiv f)]

/-- The units of $\mathcal O_K$ and $\mathcal O_L$ correspond along $f$. -/
def unitsEquiv (f : K ≃+* L) : (𝓞 K)ˣ ≃* (𝓞 L)ˣ := Units.mapEquiv (RingOfIntegers.mapRingEquiv f).toMulEquiv

theorem coe_unitsEquiv (f : K ≃+* L) (u : (𝓞 K)ˣ) : ((unitsEquiv f u : 𝓞 L) : L) = f ((u : 𝓞 K) : K) := rfl

/-- **Isomorphic number fields have the same regulator.** -/
theorem regulator_eq_of_ringEquiv (f : K ≃+* L) : regulator L = regulator K := by
  classical
  set P := placeEquiv f
  have hr : Units.rank L = Units.rank K := rank_eq_of_ringEquiv f
  set u : Fin (Units.rank L) → (𝓞 L)ˣ := fun i => unitsEquiv f (fundSystem K (finCongr hr i)) with hu
  -- the regulator of the transported family
  have h1 : regOfFamily u = regulator K := by
    obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
    have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = Units.rank K := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Units.rank]
    let eK : {w : InfinitePlace K // w ≠ w₀} ≃ Fin (Units.rank K) := Fintype.equivFinOfCardEq hcard
    let sub : {w : InfinitePlace L // w ≠ P.symm w₀} ≃ {w : InfinitePlace K // w ≠ w₀} :=
      P.subtypeEquiv fun w => by rw [not_iff_not, Equiv.eq_symm_apply]
    let eL : {w : InfinitePlace L // w ≠ P.symm w₀} ≃ Fin (Units.rank L) := (sub.trans eK).trans (finCongr hr.symm)
    rw [regOfFamily_eq_det u (P.symm w₀) eL, regulator_eq_det K w₀ eK, ← Matrix.det_submatrix_equiv_self sub]
    congr 2
    ext i w
    simp only [Matrix.submatrix_apply, Matrix.of_apply, hu, eL, Equiv.trans_apply, finCongr_apply,
      Fin.cast_cast, Fin.cast_eq_self, coe_unitsEquiv]
    rw [← mult_placeEquiv f w.1]
    rfl
  -- the transported family generates the units with the torsion
  have h2 : Subgroup.closure (Set.range u) ⊔ torsion L = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (unitsEquiv f).symm x ∈ Subgroup.closure (Set.range (fundSystem K)) ⊔ torsion K := by
      rw [closure_fundSystem_sup_torsion_eq_top]; trivial
    have hle : Subgroup.closure (Set.range (fundSystem K)) ⊔ torsion K ≤
        (Subgroup.closure (Set.range u) ⊔ torsion L).comap (unitsEquiv f).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [Subgroup.closure_le]
        rintro _ ⟨j, rfl⟩
        refine Subgroup.mem_sup_left (Subgroup.subset_closure ⟨finCongr hr.symm j, ?_⟩)
        simp [hu]
      · intro y hy
        exact Subgroup.mem_sup_right (MonoidHom.isOfFinOrder _ hy)
    have := hle hx
    simpa using this
  have h3 := regOfFamily_div_regulator u
  rw [h2, Subgroup.index_top, Nat.cast_one, div_eq_one_iff_eq (regulator_ne_zero L), h1] at h3
  exact h3.symm

end RegIso

/-! ### $E$ is a CM field -/

section CM

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

variable {D : 𝓞 F} (S : SqrtData D E)

open Lattices QuadForm QuadFormsKB.HilbertModular Binary.Rel BinaryNormOne

local notation "QD" => formF (diagForm1 D)

include S in
/-- **$E = F(\sqrt{-D})$ is totally complex** for $D \gg 0$ ($\langle1,D\rangle$ totally positive definite): at a real place $w$ of $E$,
$\sigma_w(\theta)^2 = -\sigma_w(D) < 0$. -/
theorem isTotallyComplex_of_sqrtData [IsTotallyReal F] (hpd : IsTotallyPosDef QD) : IsTotallyComplex E := by
  refine ⟨fun w => ?_⟩
  by_contra hc
  have hr : w.IsReal := not_isComplex_iff_isReal.mp hc
  set w' := w.comap (algebraMap F E)
  have hr' : w'.IsReal := hr.comap _
  have hpos : 0 < realEmb F w' (algebraMap (𝓞 F) F D) := by
    have h := realEmb_det_hessian_pos hpd w'
    rw [hessian_det_diagForm1, map_mul, map_mul, map_ofNat, map_ofNat] at h
    linarith
  have e1 : ((realEmb F w' (algebraMap (𝓞 F) F D) : ℝ) : ℂ) =
      w.embedding (algebraMap F E (algebraMap (𝓞 F) F D)) := by
    rw [show ((realEmb F w' (algebraMap (𝓞 F) F D) : ℝ) : ℂ) = w'.embedding (algebraMap (𝓞 F) F D) from
      embedding_of_isReal_apply _ _, comap_embedding_of_isReal _ hr']
    rfl
  have e2 := congrArg w.embedding S.sq
  rw [map_pow, map_neg, ← e1, ← embedding_of_isReal_apply hr] at e2
  have e3 : (embedding_of_isReal hr S.θ) ^ 2 = -(realEmb F w' (algebraMap (𝓞 F) F D)) := by exact_mod_cast e2
  nlinarith [sq_nonneg (embedding_of_isReal hr S.θ)]

include S in
/-- **$E$ is a CM field** (Mathlib's `IsCMField.ofCMExtension`). -/
theorem isCMField_of_sqrtData [IsTotallyReal F] (hpd : IsTotallyPosDef QD) : IsCMField E := by
  have := isTotallyComplex_of_sqrtData S hpd
  exact IsCMField.ofCMExtension F E

variable [IsTotallyReal F] [IsCMField E]

/-- The nontrivial automorphism of $E/F$ is complex conjugation (it fixes $F \cong E^+$). -/
theorem conj_eq_complexConj' (x : E) : conj F E x = IsCMField.complexConj E x := by
  have hfix : ∀ y : F, IsCMField.complexConj E (algebraMap F E y) = algebraMap F E y := fun y => by
    rw [← CMExtension.equivMaximalRealSubfield_apply F E y]
    exact IsCMField.complexConj_apply_eq_self E _
  let σ : E ≃ₐ[F] E := { (IsCMField.complexConj E).toRingEquiv with commutes' := hfix }
  have hσ : σ ≠ 1 := fun h => IsCMField.complexConj_ne_one E (AlgEquiv.ext fun y => by
    have := congrArg (fun τ : E ≃ₐ[F] E => τ y) h
    simpa [σ] using this)
  rcases eq_one_or_eq_conj (F := F) (E := E) σ with h | h
  · exact absurd h hσ
  · rw [← h]; rfl

/-- Our $u \mapsto u/\sigma u$ is Mathlib's `IsCMField.unitsMulComplexConjInv`. -/
theorem unitsMulConjInv_eq' : unitsMulConjInv F E = IsCMField.unitsMulComplexConjInv E := by
  ext u
  have h : conjUnits F E u = IsCMField.unitsComplexConj E u := by
    ext
    show ((conjO F E (u : 𝓞 E) : 𝓞 E) : E) = _
    rw [show ((conjO F E (u : 𝓞 E) : 𝓞 E) : E) = conj F E ((u : 𝓞 E) : E) from rfl, conj_eq_complexConj']
    rfl
  simp only [coe_unitsMulConjInv, IsCMField.unitsMulComplexConjInv_apply, h]

/-- **$Q_E\cdot[\mu_E : \{u/\sigma u\}] = 2$** for $E/F$ (Mathlib's `IsCMField.indexRealUnits_mul_eq`). -/
@[kb "washington1997" "Ch. 4, Thm. 4.12 [unverified locator]"]
theorem indexRealUnits_mul_index_conjQuotGroup' :
    IsCMField.indexRealUnits E * (conjQuotGroup F E).index = 2 := by
  rw [conjQuotGroup, unitsMulConjInv_eq']
  exact IsCMField.indexRealUnits_mul_eq E

/-- **The regulator of the CM extension:** $2R_E = 2^{n-1}\,[\mu_E : \{u/\sigma u\}]\,R_F$, $n = [F:\mathbb Q]$ (Mathlib's
`regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv` for $E/E^+$, $R_{E^+} = R_F$, and $Q_E\,\mathrm{idx} = 2$). -/
@[kb "washington1997" "Ch. 4, Prop. 4.16 [unverified locator]"]
theorem regulator_eq_cm :
    2 * regulator E = 2 ^ (Module.finrank ℚ F - 1) * (conjQuotGroup F E).index * regulator F := by
  have hdeg := Algebra.IsQuadraticExtension.finrank_eq_two F E
  have h1 := IsCMField.regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv E
  rw [regulator_eq_of_ringEquiv (CMExtension.equivMaximalRealSubfield F E)] at h1
  have hrank : Units.rank E = Module.finrank ℚ F - 1 := by
    rw [Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_top (E := E),
      nrComplexPlaces_top (F := F) (E := E) hdeg, zero_add]
  have hQ : (IsCMField.indexRealUnits E : ℝ) * (conjQuotGroup F E).index = 2 := by
    exact_mod_cast indexRealUnits_mul_index_conjQuotGroup' (F := F) (E := E)
  have hQ0 : (IsCMField.indexRealUnits E : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hQ; norm_num at hQ
  rw [div_eq_iff (regulator_pos F).ne', hrank] at h1
  rw [h1]
  field_simp
  linear_combination (-regulator F) * hQ

end CM

/-! ### The assembly, given the discriminant relation -/

section Assembly

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

variable {D : 𝓞 F} (S : SqrtData D E)

open Lattices QuadForm Binary.Rel BinaryNormOne Loc

local notation "QD" => QuadFormsKB.HilbertModular.formF (diagForm1 D)

/-- **The mass formula of $\langle1,D\rangle$ from the discriminant relation** ($F$ totally real, $Q = \langle1,D\rangle$ totally positive definite,
$T$ the ramified primes, $U \supseteq T$ containing every $\mathfrak p \mid 2D$): if $|d_E|\,\bigl(\prod_{\mathfrak p\in U}N\mathfrak p^{c_\mathfrak p}\bigr)^2 =
4^n|d_F|^2|N_{F/\mathbb Q}D|$, then $\mathrm{Mass}(\mathcal O_F^2)\,S^{\mathrm{reg}}_2(Q,1) = 1$.
*Proof:* `mass_mul_siegelProduct2Reg_eq`, `mass_latE`, the residues $\rho_F = 2^nh_FR_F/(2\sqrt{|d_F|})$, $\rho_E = (2\pi)^nh_ER_E/(w_E\sqrt{|d_E|})$,
and `regulator_eq_cm`; what is left is $\mathrm{idx}\,P\,R_F\sqrt{|d_E|}/(4R_E|d_F|\sqrt{|N D|}) = P\sqrt{|d_E|}/(2^n|d_F|\sqrt{|ND|}) = 1$. -/
theorem massFormula_of_discr [IsTotallyReal F] (hpd : IsTotallyPosDef QD) {T : Finset (HeightOneSpectrum (𝓞 F))}
    (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) {U : Finset (HeightOneSpectrum (𝓞 F))} (hTU : T ⊆ U)
    (hU : ∀ v ∉ U, (2 * D : 𝓞 F) ∉ v.asIdeal)
    (hdisc : |(NumberField.discr E : ℝ)| * (∏ v ∈ U, (qv v : ℝ) ^ cv S v) ^ 2 =
      4 ^ Module.finrank ℚ F * |(NumberField.discr F : ℝ)| ^ 2 * |(Algebra.norm ℚ (algebraMap (𝓞 F) F D) : ℝ)|) :
    mass QD (stdLat F 2) * siegelProduct2Reg (diagForm1 D) 1 = 1 := by
  have := isTotallyComplex_of_sqrtData S hpd
  have := isCMField_of_sqrtData S hpd
  have hdeg := Algebra.IsQuadraticExtension.finrank_eq_two F E
  rw [mass_mul_siegelProduct2Reg_eq S hpd hT hTU hU, mass_latE S hpd hT, dedekindZeta_residue_def,
    dedekindZeta_residue_def, nrRealPlaces_base (F := F), nrComplexPlaces_base (F := F),
    nrRealPlaces_top (E := E), nrComplexPlaces_top (F := F) (E := E) hdeg, torsionOrder_eq_two (F := F)]
  have hR := regulator_eq_cm (F := F) (E := E)
  set n := Module.finrank ℚ F with hn
  have hn1 : 1 ≤ n := Module.finrank_pos
  set P := ∏ v ∈ U, (qv v : ℝ) ^ cv S v with hP
  set dF := |(NumberField.discr F : ℝ)| with hdF
  set dE := |(NumberField.discr E : ℝ)| with hdE
  set N := |(Algebra.norm ℚ (algebraMap (𝓞 F) F D) : ℝ)| with hN
  have hdF0 : 0 < dF := abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero F))
  have hdE0 : 0 < dE := abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero E))
  have hN0 : 0 < N := by
    refine abs_pos.mpr ?_
    have hD0 : algebraMap (𝓞 F) F D ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr S.D_ne
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hD0)
  have hP0 : 0 < P := Finset.prod_pos fun v _ => pow_pos (by exact_mod_cast qv_pos v) _
  -- the square roots
  have hsq : Real.sqrt dE * P = 2 ^ n * dF * Real.sqrt N := by
    have h1 : (Real.sqrt dE * P) ^ 2 = (2 ^ n * dF * Real.sqrt N) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hdE0.le, Real.sq_sqrt hN0.le, hdisc, ← pow_mul,
        show (2 : ℝ) ^ (n * 2) = 4 ^ n by rw [pow_mul']; norm_num]
    exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp h1
  have hhF : (0 : ℝ) < classNumber F := by exact_mod_cast classNumber_pos F
  have hhE : (0 : ℝ) < classNumber E := by exact_mod_cast classNumber_pos E
  have hwE : (0 : ℝ) < torsionOrder E := by exact_mod_cast torsionOrder_pos E
  have hRF := regulator_pos F
  have hRE := regulator_pos E
  have hidx : (0 : ℝ) < (conjQuotGroup F E).index := by
    have h2 := indexRealUnits_mul_index_conjQuotGroup' (F := F) (E := E)
    have : (conjQuotGroup F E).index ≠ 0 := fun h0 => by rw [h0, mul_zero] at h2; norm_num at h2
    exact_mod_cast Nat.pos_of_ne_zero this
  have h2n : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [Real.rpow_neg hdF0.le, Real.rpow_neg hN0.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have hsF : 0 < Real.sqrt dF := Real.sqrt_pos.mpr hdF0
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsE : 0 < Real.sqrt dE := Real.sqrt_pos.mpr hdE0
  have hsF2 : Real.sqrt dF ^ 2 = dF := Real.sq_sqrt hdF0.le
  simp only [Nat.cast_ofNat]
  field_simp
  rw [h2n] at hsq
  linear_combination ((conjQuotGroup F E).index * Real.pi ^ n * regulator F * 2 ^ T.card * 2 ^ n) * hsq -
    (Real.pi ^ n * Real.sqrt N * regulator E * 2 ^ T.card * 2 ^ n * 4) * hsF2 -
    (2 * 2 ^ T.card * 2 ^ n * Real.pi ^ n * dF * Real.sqrt N) * hR
end Assembly

end QuadFormsKB.Tamagawa.BinaryCM
