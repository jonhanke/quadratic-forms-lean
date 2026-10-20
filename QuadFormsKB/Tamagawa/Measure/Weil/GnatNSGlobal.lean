/-
# Non-square discriminant: the adelic isomorphism $\Phi : P\cong SO(\langle1,-ad,-bd,abd\rangle)(\mathbb A_F)$ and the global points


**Layer:** as `GnatNSMaps`.

**Defines/proves**
* `mkAdeleOf`, `mkQQ`, `mkQQUnit`: elements and units of $D_E\otimes\mathbb A_F$ from local components; `qq_ext`, `qqUnits_ext`;
* `bcUnitsEquiv`, `nrdUnit_eq_of_bcHom` (converse of `bcHom_nrd`);
* **`nsAdele_surjective`**, **`ker_nsAdele`** (kernel = the centre $Z$), **`nsPEquiv : (gnatBC …).P ≃ₜ* SOAdele (qNS a b d)`**,
  **`map_gamP_nsPEquiv`** ($\Phi(\pi(\Gamma)) = $ `GammaSOAdele`).

Source: Weil 1982, §3.7, pp. 64–65 [unverified]; §1.3 [unverified].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSMaps

open Matrix Quaternion NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain Topology
  Filter
open scoped RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Quat.Gnat QuadFormsKB.Lattices QuadFormsKB.Siegel
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

/-- **Multiplicativity of $x\mapsto\operatorname{re}(x\bar x)$** on a quaternion algebra over a commutative ring. -/
theorem re_mul_star_mul {R : Type*} [CommRing R] {c₁ c₃ : R} (x y : ℍ[R, c₁, 0, c₃]) :
    ((x * y) * star (x * y)).re = (x * star x).re * (y * star y).re := by
  set n := (y * star y).re with hn
  have hy : y * star y = (n : ℍ[R, c₁, 0, c₃]) := QuaternionAlgebra.mul_star_eq_coe y
  calc ((x * y) * star (x * y)).re = (x * (y * star y) * star x).re := by rw [star_mul]; simp only [mul_assoc]
    _ = (((n : R) : ℍ[R, c₁, 0, c₃]) * (x * star x)).re := by
        rw [hy, ← QuaternionAlgebra.coe_commutes, mul_assoc]
    _ = _ := by simp [QuaternionAlgebra.re_mul, mul_comm]

/-! ### Assembling adeles and elements of $D_E\otimes\mathbb A_F$ from local components -/

section Assemble

variable {F : Type} [Field F] [NumberField F]

/-- An adele with prescribed components (integral at almost all finite places). -/
def mkAdeleOf (xR : ∀ w : {w : InfinitePlace F // w.IsReal}, ℝ) (xC : ∀ w : {w : InfinitePlace F // w.IsComplex}, ℂ)
    (xf : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) (h : ∀ᶠ v in cofinite, xf v ∈ v.adicCompletionIntegers F) :
    Adeles F :=
  ((xR, xC), mkAF xf h)

@[simp] theorem fAt_mkAdeleOf (xR xC xf h) (v : HeightOneSpectrum (𝓞 F)) : fAt v (mkAdeleOf (F := F) xR xC xf h) = xf v :=
  rfl
@[simp] theorem fAtR_mkAdeleOf (xR xC xf h) (w : {w : InfinitePlace F // w.IsReal}) :
    fAtR w (mkAdeleOf (F := F) xR xC xf h) = xR w := rfl
@[simp] theorem fAtC_mkAdeleOf (xR xC xf h) (w : {w : InfinitePlace F // w.IsComplex}) :
    fAtC w (mkAdeleOf (F := F) xR xC xf h) = xC w := rfl

variable {a b d : 𝓞 F}

local notation "QQ" => QuatQuadAdele F (d : F) (a : F) (b : F)

/-- The local component maps at the three kinds of places. -/
abbrev dV (v : HeightOneSpectrum (𝓞 F)) : QQ →+* DEr (v.adicCompletion F) a b d :=
  deMap (fAt v) (fAt_diag v (d : F)) (fAt_diag v (a : F)) (fAt_diag v (b : F))
abbrev dR (w : {w : InfinitePlace F // w.IsReal}) : QQ →+* DEre a b d w :=
  deMap (fAtR w) (fAtR_diag w (d : F)) (fAtR_diag w (a : F)) (fAtR_diag w (b : F))
abbrev dC (w : {w : InfinitePlace F // w.IsComplex}) : QQ →+* DEcx a b d w :=
  deMap (fAtC w) (fAtC_diag w (d : F)) (fAtC_diag w (a : F)) (fAtC_diag w (b : F))

theorem quadAdele_ext {z z' : QuadAdele F (d : F)}
    (hR : ∀ w, fAtR w z.re = fAtR w z'.re ∧ fAtR w z.im = fAtR w z'.im)
    (hC : ∀ w, fAtC w z.re = fAtC w z'.re ∧ fAtC w z.im = fAtC w z'.im)
    (hv : ∀ v, fAt v z.re = fAt v z'.re ∧ fAt v z.im = fAt v z'.im) : z = z' :=
  QuadraticAlgebra.ext (adeles_ext (fun w => (hR w).1) (fun w => (hC w).1) (fun v => (hv v).1))
    (adeles_ext (fun w => (hR w).2) (fun w => (hC w).2) (fun v => (hv v).2))

/-- **An element of $D_E\otimes\mathbb A_F$ is determined by its local components.** -/
theorem qq_ext {x y : QQ} (hv : ∀ v, dV (a := a) (b := b) (d := d) v x = dV v y) (hR : ∀ w, dR w x = dR w y)
    (hC : ∀ w, dC w x = dC w y) : x = y := by
  have key : ∀ (c : QQ → QuadAdele F (d : F)) (cv : ∀ v, DEr (v.adicCompletion F) a b d → QE (algebraMap F
      (v.adicCompletion F) (d : F))) (cR : ∀ w, DEre a b d w → QE (embedding_of_isReal w.2 (d : F)))
      (cC : ∀ w, DEcx a b d w → QE (w.1.embedding (d : F))),
      (∀ v z, cv v (dV v z) = qeMap (fAt v) (fAt_diag v (d : F)) (c z)) →
      (∀ w z, cR w (dR w z) = qeMap (fAtR w) (fAtR_diag w (d : F)) (c z)) →
      (∀ w z, cC w (dC w z) = qeMap (fAtC w) (fAtC_diag w (d : F)) (c z)) → c x = c y := by
    intro c cv cR cC ev eR eC
    refine quadAdele_ext (fun w => ?_) (fun w => ?_) (fun v => ?_)
    · have := congrArg (cR w) (hR w); rw [eR, eR] at this
      exact ⟨congrArg QuadraticAlgebra.re this, congrArg QuadraticAlgebra.im this⟩
    · have := congrArg (cC w) (hC w); rw [eC, eC] at this
      exact ⟨congrArg QuadraticAlgebra.re this, congrArg QuadraticAlgebra.im this⟩
    · have := congrArg (cv v) (hv v); rw [ev, ev] at this
      exact ⟨congrArg QuadraticAlgebra.re this, congrArg QuadraticAlgebra.im this⟩
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · exact key (fun z => z.re) (fun _ z => z.re) (fun _ z => z.re) (fun _ z => z.re) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl)
  · exact key (fun z => z.imI) (fun _ z => z.imI) (fun _ z => z.imI) (fun _ z => z.imI) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl)
  · exact key (fun z => z.imJ) (fun _ z => z.imJ) (fun _ z => z.imJ) (fun _ z => z.imJ) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl)
  · exact key (fun z => z.imK) (fun _ z => z.imK) (fun _ z => z.imK) (fun _ z => z.imK) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl)

theorem qqUnits_ext {x y : QQˣ}
    (hv : ∀ v, Units.map (dV (a := a) (b := b) (d := d) v).toMonoidHom x = Units.map (dV v).toMonoidHom y)
    (hR : ∀ w, Units.map (dR w).toMonoidHom x = Units.map (dR w).toMonoidHom y)
    (hC : ∀ w, Units.map (dC w).toMonoidHom x = Units.map (dC w).toMonoidHom y) : x = y :=
  Units.ext (qq_ext (fun v => congrArg Units.val (hv v)) (fun w => congrArg Units.val (hR w))
    (fun w => congrArg Units.val (hC w)))

/-- An element of $E\otimes\mathbb A_F$ from local components. -/
def mkQuadOf (zR : ∀ w : {w : InfinitePlace F // w.IsReal}, QE (embedding_of_isReal w.2 (d : F)))
    (zC : ∀ w : {w : InfinitePlace F // w.IsComplex}, QE (w.1.embedding (d : F)))
    (zf : ∀ v : HeightOneSpectrum (𝓞 F), QE (algebraMap F (v.adicCompletion F) (d : F)))
    (h : ∀ᶠ v in cofinite, QEInt (v.adicCompletionIntegers F).toSubring (zf v)) : QuadAdele F (d : F) :=
  ⟨mkAdeleOf (fun w => (zR w).re) (fun w => (zC w).re) (fun v => (zf v).re) (by filter_upwards [h] with v hv; exact hv.1),
   mkAdeleOf (fun w => (zR w).im) (fun w => (zC w).im) (fun v => (zf v).im) (by filter_upwards [h] with v hv; exact hv.2)⟩

/-- An element of $D_E\otimes\mathbb A_F$ from local components, integral at almost all places. -/
def mkQQ (yR : ∀ w : {w : InfinitePlace F // w.IsReal}, DEre a b d w)
    (yC : ∀ w : {w : InfinitePlace F // w.IsComplex}, DEcx a b d w)
    (yf : ∀ v : HeightOneSpectrum (𝓞 F), DEr (v.adicCompletion F) a b d)
    (h : ∀ᶠ v in cofinite, DEInt (v.adicCompletionIntegers F).toSubring (yf v)) : QQ :=
  ⟨mkQuadOf (fun w => (yR w).re) (fun w => (yC w).re) (fun v => (yf v).re) (by filter_upwards [h] with v hv; exact hv.1),
   mkQuadOf (fun w => (yR w).imI) (fun w => (yC w).imI) (fun v => (yf v).imI)
     (by filter_upwards [h] with v hv; exact hv.2.1),
   mkQuadOf (fun w => (yR w).imJ) (fun w => (yC w).imJ) (fun v => (yf v).imJ)
     (by filter_upwards [h] with v hv; exact hv.2.2.1),
   mkQuadOf (fun w => (yR w).imK) (fun w => (yC w).imK) (fun v => (yf v).imK)
     (by filter_upwards [h] with v hv; exact hv.2.2.2)⟩

theorem dV_mkQQ (yR yC yf h) (v : HeightOneSpectrum (𝓞 F)) : dV v (mkQQ (a := a) (b := b) (d := d) yR yC yf h) = yf v :=
  QuaternionAlgebra.ext (QuadraticAlgebra.ext rfl rfl) (QuadraticAlgebra.ext rfl rfl) (QuadraticAlgebra.ext rfl rfl)
    (QuadraticAlgebra.ext rfl rfl)
theorem dR_mkQQ (yR yC yf h) (w : {w : InfinitePlace F // w.IsReal}) :
    dR w (mkQQ (a := a) (b := b) (d := d) yR yC yf h) = yR w :=
  QuaternionAlgebra.ext (QuadraticAlgebra.ext rfl rfl) (QuadraticAlgebra.ext rfl rfl) (QuadraticAlgebra.ext rfl rfl)
    (QuadraticAlgebra.ext rfl rfl)
theorem dC_mkQQ (yR yC yf h) (w : {w : InfinitePlace F // w.IsComplex}) :
    dC w (mkQQ (a := a) (b := b) (d := d) yR yC yf h) = yC w :=
  QuaternionAlgebra.ext (QuadraticAlgebra.ext rfl rfl) (QuadraticAlgebra.ext rfl rfl) (QuadraticAlgebra.ext rfl rfl)
    (QuadraticAlgebra.ext rfl rfl)

/-- A unit of $D_E\otimes\mathbb A_F$ from local units, in $\Lambda_E^\times$ at almost all places. -/
def mkQQUnit (yR : ∀ w : {w : InfinitePlace F // w.IsReal}, (DEre a b d w)ˣ)
    (yC : ∀ w : {w : InfinitePlace F // w.IsComplex}, (DEcx a b d w)ˣ)
    (yf : ∀ v : HeightOneSpectrum (𝓞 F), DEK (v.adicCompletion F) a b d)
    (h : ∀ᶠ v in cofinite, yf v ∈ lamEUnits v a b d) : QQˣ :=
  have h1 : ∀ᶠ v in cofinite, DEInt (v.adicCompletionIntegers F).toSubring ((yf v : DEK (v.adicCompletion F) a b d) :
      DEr (v.adicCompletion F) a b d) := by filter_upwards [h] with v hv; exact hv.1
  have h2 : ∀ᶠ v in cofinite, DEInt (v.adicCompletionIntegers F).toSubring (((yf v)⁻¹ : DEK (v.adicCompletion F) a b d) :
      DEr (v.adicCompletion F) a b d) := by filter_upwards [h] with v hv; exact hv.2
  ⟨mkQQ (fun w => yR w) (fun w => yC w) (fun v => yf v) h1,
   mkQQ (fun w => ((yR w)⁻¹ : (DEre a b d w)ˣ)) (fun w => ((yC w)⁻¹ : (DEcx a b d w)ˣ))
     (fun v => (((yf v)⁻¹ : DEK (v.adicCompletion F) a b d) : DEr (v.adicCompletion F) a b d)) h2,
   qq_ext (fun v => by rw [map_mul, map_one, dV_mkQQ, dV_mkQQ, Units.mul_inv])
     (fun w => by rw [map_mul, map_one, dR_mkQQ, dR_mkQQ, Units.mul_inv])
     (fun w => by rw [map_mul, map_one, dC_mkQQ, dC_mkQQ, Units.mul_inv]),
   qq_ext (fun v => by rw [map_mul, map_one, dV_mkQQ, dV_mkQQ, Units.inv_mul])
     (fun w => by rw [map_mul, map_one, dR_mkQQ, dR_mkQQ, Units.inv_mul])
     (fun w => by rw [map_mul, map_one, dC_mkQQ, dC_mkQQ, Units.inv_mul])⟩

theorem dV_mkQQUnit (yR yC yf h) (v : HeightOneSpectrum (𝓞 F)) :
    Units.map (dV v).toMonoidHom (mkQQUnit (a := a) (b := b) (d := d) yR yC yf h) = yf v :=
  Units.ext (dV_mkQQ _ _ _ (by filter_upwards [h] with v hv; exact hv.1) v)
theorem dR_mkQQUnit (yR yC yf h) (w : {w : InfinitePlace F // w.IsReal}) :
    Units.map (dR w).toMonoidHom (mkQQUnit (a := a) (b := b) (d := d) yR yC yf h) = yR w :=
  Units.ext (dR_mkQQ _ _ _ (by filter_upwards [h] with v hv; exact hv.1) w)
theorem dC_mkQQUnit (yR yC yf h) (w : {w : InfinitePlace F // w.IsComplex}) :
    Units.map (dC w).toMonoidHom (mkQQUnit (a := a) (b := b) (d := d) yR yC yf h) = yC w :=
  Units.ext (dC_mkQQ _ _ _ (by filter_upwards [h] with v hv; exact hv.1) w)

end Assemble

/-! ### Norms through the base change -/

section BCNorm

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) {d : F} (hb₁ : bK 1 * bK 1 = algebraMap F K d)
  {a b : F} {A' B' : K} (hA' : A' = algebraMap F K a) (hB' : B' = algebraMap F K b)

theorem quadBaseChange_bcHom_nrd (m : (QuatAdele (F := K) A' B')ˣ) :
    quadBaseChange hb₀ hb₁ (((bcHom hb₀ hb₁ hA' hB' m : (QuatQuadAdele F d a b)ˣ) : QuatQuadAdele F d a b) *
      star ((bcHom hb₀ hb₁ hA' hB' m : (QuatQuadAdele F d a b)ˣ) : QuatQuadAdele F d a b)).re =
      ((m : QuatAdele (F := K) A' B') * star (m : QuatAdele (F := K) A' B')).re := by
  have e1 : (bcHom hb₀ hb₁ hA' hB' m : QuatQuadAdele F d a b) = bcRing hb₀ hb₁ hA' hB' (m : QuatAdele (F := K) A' B') :=
    rfl
  rw [e1, ← bcRing_star, ← map_mul]
  change (quatBaseChange hb₀ hb₁ a b ((quatBaseChange hb₀ hb₁ a b).symm
    (quatParamEquiv (diag_eq_of_eq hA') (diag_eq_of_eq hB')
      ((m : QuatAdele (F := K) A' B') * star (m : QuatAdele (F := K) A' B'))))).re = _
  rw [RingEquiv.apply_symm_apply, quatParamEquiv_re]

/-- **Converse of `bcHom_nrd`.** -/
theorem nrdUnit_eq_of_bcHom (m : (QuatAdele (F := K) A' B')ˣ) (u : (Adeles F)ˣ)
    (h : (((bcHom hb₀ hb₁ hA' hB' m : (QuatQuadAdele F d a b)ˣ) : QuatQuadAdele F d a b) *
      star ((bcHom hb₀ hb₁ hA' hB' m : (QuatQuadAdele F d a b)ˣ) : QuatQuadAdele F d a b)).re =
      (⟨(u : Adeles F), 0⟩ : QuadAdele F d)) : nrdUnit m = adeleUnitsMap F K u := by
  apply Units.ext
  rw [nrdUnit_val, ← quadBaseChange_bcHom_nrd hb₀ hb₁ hA' hB' m, h, quadBaseChange_apply, map_zero, mul_zero, add_zero]
  rfl

/-- $\Theta^{-1}$ on units as a multiplicative equivalence. -/
def bcUnitsEquiv : (QuatAdele (F := K) A' B')ˣ ≃* (QuatQuadAdele F d a b)ˣ :=
  Units.mapEquiv (RingEquiv.ofBijective _ (bcRing_bijective hb₀ hb₁ hA' hB')).toMulEquiv

theorem bcUnitsEquiv_apply (m : (QuatAdele (F := K) A' B')ˣ) : bcUnitsEquiv hb₀ hb₁ hA' hB' m = bcHom hb₀ hb₁ hA' hB' m :=
  rfl

/-- $\Theta^{-1}$ of the scalar $\iota(c)$ is the scalar $c$. -/
theorem bcHom_quatScalar (c : (Adeles F)ˣ) :
    ((bcHom hb₀ hb₁ hA' hB' (quatScalar A' B' (adeleUnitsMap F K c)) : (QuatQuadAdele F d a b)ˣ) :
      QuatQuadAdele F d a b) = (((⟨(c : Adeles F), 0⟩ : QuadAdele F d)) : QuatQuadAdele F d a b) := by
  apply (quatBaseChange hb₀ hb₁ a b).injective
  change quatBaseChange hb₀ hb₁ a b ((quatBaseChange hb₀ hb₁ a b).symm
    (quatParamEquiv (diag_eq_of_eq hA') (diag_eq_of_eq hB') _)) = _
  rw [RingEquiv.apply_symm_apply]
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · simp only [quatParamEquiv_re, quatBaseChange_re, QuaternionAlgebra.re_coe]
    rw [quadBaseChange_apply, map_zero, mul_zero, add_zero]
    rfl
  · change (0 : Adeles K) = quadBaseChange hb₀ hb₁ 0; rw [map_zero]
  · change (0 : Adeles K) = quadBaseChange hb₀ hb₁ 0; rw [map_zero]
  · change (0 : Adeles K) = quadBaseChange hb₀ hb₁ 0; rw [map_zero]

end BCNorm

/-! ### The global map -/

section Global

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) {a b d : 𝓞 F} (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {A' B' : K} (hA' : A' = algebraMap F K (a : F)) (hB' : B' = algebraMap F K (b : F)) (hA0 : A' ≠ 0) (hB0 : B' ≠ 0)
  (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0) (hd0 : (d : F) ≠ 0)

local notation "Q₀" => qNS a b d
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qNS a b d)
local notation "MQ" => (QuatQuadAdele F (d : F) (a : F) (b : F))ˣ

/-- **$G^\natural(\mathbb A_F)\to SO(V)(\mathbb A_F)$** for the non-square model. -/
@[kb "weil1982" "§3.7, pp. 64–65 [unverified]"]
def nsAdele : (gnatBC bK 0 hb₀ hA0 hB0).G →* SOAdele Q₀ :=
  (nsInf hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0).prod (nsFin hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0)

theorem continuous_nsAdele : Continuous (nsAdele hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0) :=
  (continuous_nsInf hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0).prodMk (continuous_nsFin hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0)

theorem scalarK_mem_scalarsG {L : Type*} [Field L] {A B D : L} (r : Lˣ) :
    (⟨Units.map (algebraMap L (DE A B D)).toMonoidHom r, scalar_mem_Gnat r⟩ : Gnat A B D) ∈ scalarsG A B D :=
  ⟨(r : L), rfl⟩

include hb0 in
/-- Local lifts at a finite place, in $\Lambda_E^\times$ at good places. -/
theorem exists_nsPairV_lift (g : SOAf Q₀) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ α : GnK (v.adicCompletion F) a b d,
      (nsSOK (v.adicCompletion F) a b d ha0 hd0 α : orthGroup QF (v.adicCompletion F)) = (g : OAf QF) v ∧
      ((Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
        Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1 ∧
        Valued.v (algebraMap F (v.adicCompletion F) (d : F)) = 1 ∧ (g : OAf QF) v ∈ stdStab QF v) →
        (α : DEK (v.adicCompletion F) a b d) ∈ lamEUnits v a b d) := by
  obtain ⟨α, hα⟩ := nsSOK_surjective (K := v.adicCompletion F) ha0 hb0 hd0
    (⟨(g : OAf QF) v, g.2 v⟩ : soSub QF (v.adicCompletion F))
  have hα' : (nsSOK (v.adicCompletion F) a b d ha0 hd0 α : orthGroup QF (v.adicCompletion F)) = (g : OAf QF) v :=
    congrArg Subtype.val hα
  by_cases hS : Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (d : F)) = 1 ∧ (g : OAf QF) v ∈ stdStab QF v
  · obtain ⟨h2, hav, hbv, hdv, hst⟩ := hS
    obtain ⟨r, hr⟩ := exists_smul_mem_lamEUnits v ha0 hd0 h2 hav hbv hdv α (by rw [hα']; exact hst)
    refine ⟨⟨_, scalar_mem_Gnat r⟩ * α, ?_, fun _ => by rw [Subgroup.coe_mul]; exact hr⟩
    rw [map_mul, (nsSOK_eq_one_iff ha0 hd0 _).2 (scalarK_mem_scalarsG r), one_mul, hα']
  · exact ⟨α, hα', fun h => absurd h hS⟩

include ha0 hb0 hd0 in
theorem eventually_good_ns (g : SOAf Q₀) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (2 : v.adicCompletion F) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (d : F)) = 1 ∧ (g : OAf QF) v ∈ stdStab QF v := by
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (2 : v.adicCompletion F) = 1 := by
    filter_upwards [eventually_valued_eq_one (two_ne_zero : (2 : F) ≠ 0)] with v hv
    rwa [map_ofNat] at hv
  filter_upwards [h2, eventually_valued_eq_one ha0, eventually_valued_eq_one hb0, eventually_valued_eq_one hd0,
    (g : OAf QF).2] with v h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

include hb0 in
theorem exists_nsPairR_lift (w : {w : InfinitePlace F // w.IsReal}) (g : ArchSO (QRe Q₀ w)) :
    ∃ α : Gnat (embedding_of_isReal w.2 (a : F)) (embedding_of_isReal w.2 (b : F)) (embedding_of_isReal w.2 (d : F)),
      (phiSO (two_ne_zero_of_ringHom (embedding_of_isReal w.2)) ((map_ne_zero _).2 ha0) ((map_ne_zero _).2 hd0) α :
        GL (Fin 4) ℝ) = ArchSO.incl _ g := by
  have hm := (mem_soReal_iff _ _).1 (show ArchSO.incl _ g ∈ soReal (QRe Q₀ w) from g.2)
  rw [show (QRe Q₀ w).hessian = (QF).hessian.map (embedding_of_isReal w.2) from hessian_map_NF _ _] at hm
  exact exists_phiSO_eq_qNS (embedding_of_isReal w.2) a b d ha0 hb0 hd0 _
    (by convert hm.1 using 3) (by convert hm.2 using 2)

include hb0 in
theorem exists_nsPairC_lift (w : {w : InfinitePlace F // w.IsComplex}) (g : ArchSOC (QCx Q₀ w)) :
    ∃ α : Gnat (w.1.embedding (a : F)) (w.1.embedding (b : F)) (w.1.embedding (d : F)),
      (phiSO (two_ne_zero_of_ringHom w.1.embedding) ((map_ne_zero _).2 ha0) ((map_ne_zero _).2 hd0) α :
        GL (Fin 4) ℂ) = ArchSOC.incl _ g := by
  have hm := (mem_soC_iff _ _).1 (ArchSOC.incl_mem _ g)
  rw [gramC] at hm
  have h1 : ((ArchSOC.incl _ g : GL (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ)ᵀ * (QCx Q₀ w).hessian *
      ((ArchSOC.incl _ g : GL (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ) = (QCx Q₀ w).hessian := by
    have := congrArg ((2 : ℂ) • ·) hm.1
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul] at this
    norm_num at this
    exact this
  rw [show (QCx Q₀ w).hessian = (QF).hessian.map w.1.embedding from hessian_map_NF _ _] at h1
  exact exists_phiSO_eq_qNS w.1.embedding a b d ha0 hb0 hd0 _ (by convert h1 using 3) (by convert hm.2 using 2)

/-- The local norm of a component is the component of the global norm. -/
theorem nrdE_dV_eq (x : MQ) (v : HeightOneSpectrum (𝓞 F)) :
    nrdE (dV (a := a) (b := b) (d := d) v (x : QuatQuadAdele F (d : F) (a : F) (b : F))) =
      qeMap (fAt v) (fAt_diag v (d : F)) ((x : QuatQuadAdele F (d : F) (a : F) (b : F)) *
        star (x : QuatQuadAdele F (d : F) (a : F) (b : F))).re := nrdE_deMap _ _ _ _ _

include hb0 in
/-- **$G^\natural(\mathbb A_F)\to SO(V)(\mathbb A_F)$ is surjective** (non-square model). -/
@[kb "weil1982" "§3.7, pp. 64–65 [unverified]"]
theorem nsAdele_surjective : Function.Surjective (nsAdele hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0) := by
  rintro ⟨gI, gf⟩
  choose αF hαF hαFS using fun v => exists_nsPairV_lift (a := a) (b := b) (d := d) ha0 hb0 hd0 gf v
  choose αR hαR using fun w => exists_nsPairR_lift (a := a) (b := b) (d := d) ha0 hb0 hd0 w (gI.1 w)
  choose αC hαC using fun w => exists_nsPairC_lift (a := a) (b := b) (d := d) ha0 hb0 hd0 w (gI.2 w)
  have hev : ∀ᶠ v in cofinite, (αF v : DEK (v.adicCompletion F) a b d) ∈ lamEUnits v a b d := by
    filter_upwards [eventually_good_ns ha0 hb0 hd0 gf] with v hv
    exact hαFS v hv
  set m' : MQ := mkQQUnit (fun w => (αR w : (DEre a b d w)ˣ)) (fun w => (αC w : (DEcx a b d w)ˣ))
    (fun v => (αF v : DEK (v.adicCompletion F) a b d)) hev with hm'
  have hV : ∀ v, Units.map (dV v).toMonoidHom m' = (αF v : DEK (v.adicCompletion F) a b d) := fun v =>
    dV_mkQQUnit _ _ _ _ v
  have hR : ∀ w, Units.map (dR w).toMonoidHom m' = (αR w : (DEre a b d w)ˣ) := fun w => dR_mkQQUnit _ _ _ _ w
  have hC : ∀ w, Units.map (dC w).toMonoidHom m' = (αC w : (DEcx a b d w)ˣ) := fun w => dC_mkQQUnit _ _ _ _ w
  -- the norm of m' is an idele
  have hloc : ∀ x : MQ, (∀ v, Units.map (dV (a := a) (b := b) (d := d) v).toMonoidHom x ∈ Gnat _ _ _) →
      (∀ w, Units.map (dR (a := a) (b := b) (d := d) w).toMonoidHom x ∈ Gnat _ _ _) →
      (∀ w, Units.map (dC (a := a) (b := b) (d := d) w).toMonoidHom x ∈ Gnat _ _ _) →
      ((x : QuatQuadAdele F (d : F) (a : F) (b : F)) * star (x : QuatQuadAdele F (d : F) (a : F) (b : F))).re.im = 0 := by
    intro x hxv hxR hxC
    refine adeles_ext (fun w => ?_) (fun w => ?_) (fun v => ?_)
    · have h := nrdE_deMap (fAtR w) (fAtR_diag w (d : F)) (fAtR_diag w (a : F)) (fAtR_diag w (b : F))
        (x : QuatQuadAdele F (d : F) (a : F) (b : F))
      have := congrArg QuadraticAlgebra.im h
      rw [qeMap_im] at this
      rw [← this, map_zero]; exact hxR w
    · have h := nrdE_deMap (fAtC w) (fAtC_diag w (d : F)) (fAtC_diag w (a : F)) (fAtC_diag w (b : F))
        (x : QuatQuadAdele F (d : F) (a : F) (b : F))
      have := congrArg QuadraticAlgebra.im h
      rw [qeMap_im] at this
      rw [← this, map_zero]; exact hxC w
    · have := congrArg QuadraticAlgebra.im (nrdE_dV_eq x v)
      rw [qeMap_im] at this
      rw [← this, map_zero]; exact hxv v
  have hm'G : ∀ v, Units.map (dV (a := a) (b := b) (d := d) v).toMonoidHom m' ∈ Gnat _ _ _ := fun v => by
    rw [hV]; exact (αF v).2
  have hm'GR : ∀ w, Units.map (dR (a := a) (b := b) (d := d) w).toMonoidHom m' ∈ Gnat _ _ _ := fun w => by
    rw [hR]; exact (αR w).2
  have hm'GC : ∀ w, Units.map (dC (a := a) (b := b) (d := d) w).toMonoidHom m' ∈ Gnat _ _ _ := fun w => by
    rw [hC]; exact (αC w).2
  have hz := hloc m' hm'G hm'GR hm'GC
  have hz' := hloc m'⁻¹ (fun v => by rw [map_inv]; exact (Gnat _ _ _).inv_mem (hm'G v))
    (fun w => by rw [map_inv]; exact (Gnat _ _ _).inv_mem (hm'GR w))
    (fun w => by rw [map_inv]; exact (Gnat _ _ _).inv_mem (hm'GC w))
  set z := ((m' : QuatQuadAdele F (d : F) (a : F) (b : F)) * star (m' : QuatQuadAdele F (d : F) (a : F) (b : F))).re
  set z' := (((m'⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)) *
    star ((m'⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F))).re
  have hzz : z * z' = 1 := by
    rw [← re_mul_star_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, star_one, mul_one]
    rfl
  set u : (Adeles F)ˣ := ⟨z.re, z'.re, by
      have := congrArg QuadraticAlgebra.re hzz
      simpa [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_one, hz'] using this, by
      have := congrArg QuadraticAlgebra.re hzz
      rw [mul_comm]; simpa [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_one, hz'] using this⟩ with hu
  have hzu : z = (⟨(u : Adeles F), 0⟩ : QuadAdele F (d : F)) := QuadraticAlgebra.ext rfl hz
  set m := (bcUnitsEquiv hb₀ hb₁ hA' hB').symm m' with hm
  have hbm : bcHom hb₀ hb₁ hA' hB' m = m' := by
    rw [← bcUnitsEquiv_apply, hm, MulEquiv.apply_symm_apply]
  have hnrd : nrdUnit m = adeleUnitsMap F K u := nrdUnit_eq_of_bcHom hb₀ hb₁ hA' hB' m u (by rw [hbm]; exact hzu)
  let g : (gnatBC bK 0 hb₀ hA0 hB0).G := ⟨(m, u), hnrd⟩
  have hgU : nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g = m' := hbm
  refine ⟨g, Prod.ext (Prod.ext (funext fun w => archSO_ext ?_) (funext fun w => archSOC_ext' ?_)) ?_⟩
  · change ArchSO.incl _ (nsR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w g) = _
    have hp : nsPairR hb₀ hb₁ hA' hB' hA0 hB0 w g = αR w := Subtype.ext (by
      change Units.map (dR w).toMonoidHom (nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g) = _
      rw [hgU, hR])
    rw [nsR_incl, nsGLR_apply, hp, hαR w]
  · change ArchSOC.incl _ (nsC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w g) = _
    have hp : nsPairC hb₀ hb₁ hA' hB' hA0 hB0 w g = αC w := Subtype.ext (by
      change Units.map (dC w).toMonoidHom (nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g) = _
      rw [hgU, hC])
    rw [nsC_incl, nsGLC_apply, hp, hαC w]
  · ext v : 2
    change ((nsFin hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 g : SOAf Q₀) : OAf QF) v = _
    have hp : nsPairV hb₀ hb₁ hA' hB' hA0 hB0 v g = αF v := Subtype.ext (by
      change Units.map (dV v).toMonoidHom (nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g) = _
      rw [hgU, hV])
    rw [nsFin_apply, hp, hαF v]

theorem coe_eq_of_scalar {L : Type*} [Field L] {A B D : L} {y : DE A B D} {r : L}
    (h : y = ((algebraMap L (QE D) r : QE D) : DE A B D)) : y = (((⟨y.re.re, 0⟩ : QE D)) : DE A B D) := by
  rw [h]; rfl

theorem deMap_coe {L : Type*} [Field L] (f : Adeles F →+* L) {td ta tb : L} (hd : f (diagRing F (d : F)) = td)
    (ha : f (diagRing F (a : F)) = ta) (hb : f (diagRing F (b : F)) = tb) (z : QuadAdele F (d : F)) :
    deMap f hd ha hb ((z : QuadAdele F (d : F)) : QuatQuadAdele F (d : F) (a : F) (b : F)) =
      ((qeMap f hd z : QE td) : DE ta tb td) :=
  QuaternionAlgebra.ext rfl (map_zero _) (map_zero _) (map_zero _)

/-- A unit of $D_E\otimes\mathbb A_F$ all of whose local components are scalars of $F_v$ is a scalar idele. -/
theorem eq_coe_of_local_scalar (x : MQ)
    (hv : ∀ v, ∃ r, dV (a := a) (b := b) (d := d) v (x : QuatQuadAdele F (d : F) (a : F) (b : F)) =
      ((algebraMap (v.adicCompletion F) (QE (algebraMap F (v.adicCompletion F) (d : F))) r : QE _) : DE _ _ _))
    (hR : ∀ w, ∃ r, dR (a := a) (b := b) (d := d) w (x : QuatQuadAdele F (d : F) (a : F) (b : F)) =
      ((algebraMap ℝ (QE (embedding_of_isReal w.2 (d : F))) r : QE _) : DE _ _ _))
    (hC : ∀ w, ∃ r, dC (a := a) (b := b) (d := d) w (x : QuatQuadAdele F (d : F) (a : F) (b : F)) =
      ((algebraMap ℂ (QE (w.1.embedding (d : F))) r : QE _) : DE _ _ _)) :
    (x : QuatQuadAdele F (d : F) (a : F) (b : F)) =
      (((⟨(x : QuatQuadAdele F (d : F) (a : F) (b : F)).re.re, 0⟩ : QuadAdele F (d : F))) :
        QuatQuadAdele F (d : F) (a : F) (b : F)) := by
  refine qq_ext (fun v => ?_) (fun w => ?_) (fun w => ?_)
  · obtain ⟨r, hr⟩ := hv v
    rw [coe_eq_of_scalar hr, deMap_coe]
    rfl
  · obtain ⟨r, hr⟩ := hR w
    rw [coe_eq_of_scalar hr, deMap_coe]
    rfl
  · obtain ⟨r, hr⟩ := hC w
    rw [coe_eq_of_scalar hr, deMap_coe]
    rfl

theorem nsUnit_zHom (c : (Adeles F)ˣ) :
    ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 ((gnatBC bK 0 hb₀ hA0 hB0).zHom c) : MQ) :
      QuatQuadAdele F (d : F) (a : F) (b : F)) = (((⟨(c : Adeles F), 0⟩ : QuadAdele F (d : F))) :
        QuatQuadAdele F (d : F) (a : F) (b : F)) :=
  bcHom_quatScalar hb₀ hb₁ hA' hB' c

/-- **The kernel of $G^\natural(\mathbb A_F)\to SO(V)(\mathbb A_F)$ is the centre $Z$** (non-square model). -/
@[kb "weil1982" "§3.7, pp. 64–65 [unverified]"]
theorem nsAdele_eq_one_iff (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    nsAdele hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 g = 1 ↔ g ∈ (gnatBC bK 0 hb₀ hA0 hB0).zHom.range := by
  constructor
  · intro h
    have hv : ∀ v, nsPairV hb₀ hb₁ hA' hB' hA0 hB0 v g ∈ scalarsG _ _ _ := fun v => by
      rw [← nsSOK_eq_one_iff ha0 hd0]
      apply Subtype.ext
      exact congrArg (fun x : SOAdele Q₀ => ((x.2 : SOAf Q₀) : OAf QF) v) h
    have hR : ∀ w, nsPairR hb₀ hb₁ hA' hB' hA0 hB0 w g ∈ scalarsG _ _ _ := fun w => by
      rw [← phiSO_val_eq_one_iff (embedding_of_isReal w.2) a (b : F) d ha0 hd0, ← nsGLR_apply hb₀ hb₁ hA' hB' hA0 hB0,
        ← nsR_incl]
      exact congrArg (fun x : SOAdele Q₀ => ArchSO.incl _ (x.1.1 w)) h
    have hC : ∀ w, nsPairC hb₀ hb₁ hA' hB' hA0 hB0 w g ∈ scalarsG _ _ _ := fun w => by
      rw [← phiSO_val_eq_one_iff w.1.embedding a (b : F) d ha0 hd0, ← nsGLC_apply hb₀ hb₁ hA' hB' hA0 hB0,
        ← nsC_incl]
      exact congrArg (fun x : SOAdele Q₀ => ArchSOC.incl _ (x.1.2 w)) h
    set m' := nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g with hm'
    have e1 := eq_coe_of_local_scalar m' (fun v => hv v) (fun w => hR w) (fun w => hC w)
    have e2 := eq_coe_of_local_scalar m'⁻¹ (fun v => by
        obtain ⟨r, hr⟩ := (scalarsG _ _ _).inv_mem (hv v)
        exact ⟨r, hr⟩) (fun w => by
        obtain ⟨r, hr⟩ := (scalarsG _ _ _).inv_mem (hR w)
        exact ⟨r, hr⟩) (fun w => by
        obtain ⟨r, hr⟩ := (scalarsG _ _ _).inv_mem (hC w)
        exact ⟨r, hr⟩)
    set c := (m' : QuatQuadAdele F (d : F) (a : F) (b : F)).re.re
    set c' := ((m'⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)).re.re
    have hcc : c * c' = 1 := by
      have h1 : (m' : QuatQuadAdele F (d : F) (a : F) (b : F)) * ((m'⁻¹ : MQ) :
          QuatQuadAdele F (d : F) (a : F) (b : F)) = 1 := Units.mul_inv _
      rw [e1, e2, ← QuaternionAlgebra.coe_mul] at h1
      have := congrArg (fun z : QuatQuadAdele F (d : F) (a : F) (b : F) => z.re.re) h1
      simpa [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_one] using this
    set cu : (Adeles F)ˣ := ⟨c, c', hcc, by rw [mul_comm]; exact hcc⟩
    refine ⟨cu, (gnatBC bK 0 hb₀ hA0 hB0).fst_injective ?_⟩
    apply bcHom_injective hb₀ hb₁ hA' hB'
    apply Units.ext
    change ((bcHom hb₀ hb₁ hA' hB' (quatScalar A' B' (adeleUnitsMap F K cu)) : MQ) :
      QuatQuadAdele F (d : F) (a : F) (b : F)) = (m' : QuatQuadAdele F (d : F) (a : F) (b : F))
    rw [bcHom_quatScalar, e1]
  · rintro ⟨c, rfl⟩
    have hU := nsUnit_zHom hb₀ hb₁ hA' hB' hA0 hB0 c
    refine Prod.ext (Prod.ext (funext fun w => archSO_ext ?_) (funext fun w => archSOC_ext' ?_)) ?_
    · have h1 : (phiSO (two_ne_zero_of_ringHom (embedding_of_isReal w.2)) ((map_ne_zero _).2 ha0)
          ((map_ne_zero _).2 hd0) (nsPairR hb₀ hb₁ hA' hB' hA0 hB0 w ((gnatBC bK 0 hb₀ hA0 hB0).zHom c)) :
            GL (Fin 4) ℝ) = 1 := by
        refine (phiSO_val_eq_one_iff (embedding_of_isReal w.2) a (b : F) d ha0 hd0 _).2 ⟨(c : Adeles F).1.1 w, ?_⟩
        rw [nsPairR_val, hU, deMap_coe]
        rfl
      change ArchSO.incl _ (nsR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w _) = ArchSO.incl _ 1
      rw [nsR_incl, nsGLR_apply, h1]
      exact (map_one _).symm
    · have h1 : (phiSO (two_ne_zero_of_ringHom w.1.embedding) ((map_ne_zero _).2 ha0)
          ((map_ne_zero _).2 hd0) (nsPairC hb₀ hb₁ hA' hB' hA0 hB0 w ((gnatBC bK 0 hb₀ hA0 hB0).zHom c)) :
            GL (Fin 4) ℂ) = 1 := by
        refine (phiSO_val_eq_one_iff w.1.embedding a (b : F) d ha0 hd0 _).2 ⟨(c : Adeles F).1.2 w, ?_⟩
        rw [nsPairC_val, hU, deMap_coe]
        rfl
      change ArchSOC.incl _ (nsC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w _) = ArchSOC.incl _ 1
      rw [nsC_incl, nsGLC_apply, h1]
      exact (map_one _).symm
    · ext v : 2
      change ((nsFin hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 _ : SOAf Q₀) : OAf QF) v = ((1 : SOAf Q₀) : OAf QF) v
      rw [nsFin_apply]
      have h1 : nsSOK (v.adicCompletion F) a b d ha0 hd0
          (nsPairV hb₀ hb₁ hA' hB' hA0 hB0 v ((gnatBC bK 0 hb₀ hA0 hB0).zHom c)) = 1 :=
        (nsSOK_eq_one_iff ha0 hd0 _).2 ⟨(c : Adeles F).2 v, by rw [nsPairV_val, hU, deMap_coe]; rfl⟩
      rw [h1]
      rfl

theorem ker_nsAdele : (nsAdele hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0).ker = (gnatBC bK 0 hb₀ hA0 hB0).zHom.range := by
  ext g; exact (MonoidHom.mem_ker).trans (nsAdele_eq_one_iff hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 g)

include hb0 in
theorem isOpenMap_nsAdele : IsOpenMap (nsAdele hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0) :=
  MonoidHom.isOpenMap_of_sigmaCompact _ (nsAdele_surjective hb₀ hb₁ hA' hB' hA0 hB0 ha0 hb0 hd0)
    (continuous_nsAdele hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0)

include hb0 in
/-- The group isomorphism $P\cong SO(V)(\mathbb A_F)$ (non-square model). -/
def nsPMulEquiv : (gnatBC bK 0 hb₀ hA0 hB0).P ≃* SOAdele Q₀ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_nsAdele hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (nsAdele_surjective hb₀ hb₁ hA' hB' hA0 hB0 ha0 hb0 hd0))

theorem continuous_nsPMulEquiv : Continuous (nsPMulEquiv hb₀ hb₁ hA' hB' hA0 hB0 ha0 hb0 hd0) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_nsAdele hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0)

theorem isOpenMap_nsPMulEquiv : IsOpenMap (nsPMulEquiv hb₀ hb₁ hA' hB' hA0 hB0 ha0 hb0 hd0) := by
  intro U hU
  have hpre : IsOpen ((QuotientGroup.mk : (gnatBC bK 0 hb₀ hA0 hB0).G → (gnatBC bK 0 hb₀ hA0 hB0).P) ⁻¹' U) :=
    hU.preimage (QuotientGroup.isQuotientMap_mk _).continuous
  have himg : (nsPMulEquiv hb₀ hb₁ hA' hB' hA0 hB0 ha0 hb0 hd0) '' U =
      (nsAdele hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0) ''
        ((QuotientGroup.mk : (gnatBC bK 0 hb₀ hA0 hB0).G → (gnatBC bK 0 hb₀ hA0 hB0).P) ⁻¹' U) := by
    ext g
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective u
      exact ⟨α, hu, rfl⟩
    · rintro ⟨α, hα, rfl⟩
      exact ⟨_, hα, rfl⟩
  rw [himg]
  exact isOpenMap_nsAdele hb₀ hb₁ hA' hB' hA0 hB0 ha0 hb0 hd0 _ hpre

/-- **The adelic isomorphism $\Phi : P = G^\natural(\mathbb A_F)/\mathbb A_F^\times\cong SO(\langle1,-ad,-bd,abd\rangle)(\mathbb A_F)$** (non-square model,
$G^\natural\subset(D'\otimes\mathbb A_K)^\times$, $K = F(\delta)$, $\delta^2 = d$; any number field, any signature). -/
@[kb "weil1982" "§3.7, pp. 64–65 [unverified]"]
def nsPEquiv : (gnatBC bK 0 hb₀ hA0 hB0).P ≃ₜ* SOAdele Q₀ :=
  { nsPMulEquiv hb₀ hb₁ hA' hB' hA0 hB0 ha0 hb0 hd0 with
    continuous_toFun := continuous_nsPMulEquiv hb₀ hb₁ hA' hB' hA0 hB0 ha0 hb0 hd0
    continuous_invFun := ((nsPMulEquiv hb₀ hb₁ hA' hB' hA0 hB0 ha0 hb0 hd0).toEquiv.toHomeomorphOfContinuousOpen
      (continuous_nsPMulEquiv hb₀ hb₁ hA' hB' hA0 hB0 ha0 hb0 hd0)
      (isOpenMap_nsPMulEquiv hb₀ hb₁ hA' hB' hA0 hB0 ha0 hb0 hd0)).symm.continuous }

theorem nsPEquiv_mk (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    nsPEquiv hb₀ hb₁ hA' hB' hA0 hB0 ha0 hb0 hd0 ((gnatBC bK 0 hb₀ hA0 hB0).π g) =
      nsAdele hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 g := rfl

end Global

/-! ### Base change of $D_E$ along a field homomorphism, and the matrix of $\varphi$ -/

section Field

variable {K L : Type*} [Field K] [Field L] (f : K →+* L) {A B D : K}

/-- $E\otimes_KL$: coordinatewise $f$. -/
def qeField : QE D →+* QE (f D) where
  toFun z := ⟨f z.re, f z.im⟩
  map_one' := QuadraticAlgebra.ext (by simp [QuadraticAlgebra.re_one]) (by simp [QuadraticAlgebra.im_one])
  map_mul' z w := QuadraticAlgebra.ext (by simp) (by simp)
  map_zero' := QuadraticAlgebra.ext (by simp) (by simp)
  map_add' z w := QuadraticAlgebra.ext (by simp) (by simp)

/-- $D_E\otimes_KL$: coordinatewise $f$. -/
def deField : DE A B D →+* DE (f A) (f B) (f D) :=
  QuaternionAlgebra.mapRingHom (qeField f) (QuadraticAlgebra.ext rfl (map_zero f)) (map_zero _)
    (QuadraticAlgebra.ext rfl (map_zero f))

@[simp] theorem qeField_re (z : QE D) : (qeField f z).re = f z.re := rfl
@[simp] theorem qeField_im (z : QE D) : (qeField f z).im = f z.im := rfl
@[simp] theorem deField_re (x : DE A B D) : (deField f x).re = qeField f x.re := rfl
@[simp] theorem deField_imI (x : DE A B D) : (deField f x).imI = qeField f x.imI := rfl
@[simp] theorem deField_imJ (x : DE A B D) : (deField f x).imJ = qeField f x.imJ := rfl
@[simp] theorem deField_imK (x : DE A B D) : (deField f x).imK = qeField f x.imK := rfl

set_option maxHeartbeats 8000000 in
/-- **The matrix of $\varphi$ commutes with base change.** -/
theorem nsMat_map (x y : DE A B D) : nsMat (deField f x) (deField f y) = (nsMat x y).map f := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [nsMat, coords, emb, sig, Pi.single_apply, QuaternionAlgebra.re_mul,
    QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul]

end Field

end QuadFormsKB.Tamagawa.Measure.Weil
