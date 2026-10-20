/-
# Transport of covolumes along $PD^\times \cong SO(D^0)$

**Layer:** $F$ a number field, $a, b \in \mathcal O_F\setminus0$, $Q_0$ = `QuatZeta.pureFormO a b`.

**Defines/proves**
* `quotientContinuousMulEquiv` (generic, Mathlib-only): a continuous open surjective homomorphism $f : G\to H$ with
  kernel $N$ induces $G/N \cong H$ as topological groups;
* $PD^\times(F_\infty) = (D\otimes F_\infty)^\times/F_\infty^\times$ = `PDInf a b` and
  $PD^\times(\mathbb A_f) = (D\otimes\mathbb A_f)^\times/\mathbb A_f^\times$ = `PDFin a b`, with
  **`pdInfEquiv : PDInf a b ≃ₜ* GInfSO Q₀`** and **`pdFinEquiv : PDFin a b ≃ₜ* SOAf Q₀`** (from `conjInf`, `conjFin`);
* `pdSplit : PDAdele a b ≃ₜ* PDInf a b × PDFin a b` and `pdGammaSplit` = the image of $PD^\times(F)$; the product of the
  two isomorphisms carries `pdGammaSplit` onto `GammaSOAdele Q₀` (`map_pdGammaSplit`);
* **`covolume_pd_eq_covolume_muTam`** (`covolume_eq_of_localFactors` applied): for left-invariant
  s-finite measures $\mu_\infty$ on $PD^\times(F_\infty)$ and $\mu_f$ on $PD^\times(\mathbb A_f)$ whose images are
  $r_\infty\cdot$`muArchTamSO` and $r_f\cdot$`muFin` with $r_\infty r_f = 1$ (Weil's product formula, Thm 2.3.1),
  $$\mathrm{covol}(PD^\times(F)\backslash PD^\times(\mathbb A), \mu_\infty\times\mu_f) =
    \mathrm{covol}(SO(V)(F)\backslash SO(V)(\mathbb A), \mu^{\mathrm{Tam}});$$
  **`tamagawaNumberTwoAdelic_iff_covolume_pd`**: hence `TamagawaNumberTwoAdelic Q₀` $\iff$ $\tau(PD^\times) = 2$ for
  any such pair, and **`covolume_pd_eq_two_of_definite`**: for $F$ totally real and $\langle -a,-b,ab\rangle$ totally
  positive definite ($D$ totally definite) the covolume is $2$ (`tamagawaNumberTwoAdelic_ternary`, the lattice
  route; no Fujisaki).

**Not done here (exact gap):** the identification of Weil's quotient Tamagawa
measure on $PD^\times(\mathbb A)$ (from `tamQuat` / `tamIdeles`) as such a pair, i.e. the local ratios $r_v$ and
$\prod_v r_v = 1$. That needs the gauge-form description of `muLocSO` at finite places and a quotient
measure on $(D\otimes\mathbb A)^\times/\mathbb A^\times$.

Source: Weil 1982, §2.3, Thm 2.3.1 (product formula) and §3.7(a), p. 63; §2.4, p. 23 ($\tau(G) = $ covolume).
-/
import QuadFormsKB.Tamagawa.Measure.Weil.PDGlobal
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamSOCorollaries

open MeasureTheory Matrix Quaternion NumberField NumberField.mixedEmbedding IsDedekindDomain Topology
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.QuatZeta

/-! ### Generic: quotient by the kernel of an open map -/

section Generic

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H]

/-- **First isomorphism theorem for topological groups:** a continuous open surjective homomorphism $f$ with kernel
$N$ induces $G/N \cong H$ (quotient topology). -/
def quotientContinuousMulEquiv (f : G →* H) (N : Subgroup G) [N.Normal] (hker : f.ker = N)
    (hsurj : Function.Surjective f) (hcont : Continuous f) (hopen : IsOpenMap f) : G ⧸ N ≃ₜ* H :=
  let e : G ⧸ N ≃* H := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  have hc : Continuous e := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 hcont
  have ho : IsOpenMap e := by
    intro U hU
    have hpre : IsOpen ((QuotientGroup.mk : G → G ⧸ N) ⁻¹' U) :=
      hU.preimage (QuotientGroup.isQuotientMap_mk _).continuous
    have himg : e '' U = f '' ((QuotientGroup.mk : G → G ⧸ N) ⁻¹' U) := by
      ext g
      constructor
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
        exact ⟨x, hu, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨_, hx, rfl⟩
    rw [himg]
    exact hopen _ hpre
  { e with
    continuous_toFun := hc
    continuous_invFun := (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous }

theorem quotientContinuousMulEquiv_mk (f : G →* H) (N : Subgroup G) [N.Normal] (hker : f.ker = N)
    (hsurj : Function.Surjective f) (hcont : Continuous f) (hopen : IsOpenMap f) (x : G) :
    quotientContinuousMulEquiv f N hker hsurj hcont hopen (QuotientGroup.mk x) = f x := rfl

end Generic

variable {F : Type} [Field F] [NumberField F] (a b : 𝓞 F)

local notation "Q₀" => pureFormO a b
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (pureFormO a b)

/-! ### $PD^\times(F_\infty)$ and $PD^\times(\mathbb A_f)$ -/

instance infScalar_range_normal : ((infScalar (a : F) (b : F)).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨c, rfl⟩ := hn
  refine ⟨c, ?_⟩
  have hc : ∀ x : (QuatInf (a : F) (b : F))ˣ, infScalar (a : F) (b : F) c * x = x * infScalar (a : F) (b : F) c :=
    fun x => Units.ext (Algebra.commutes _ _)
  rw [← hc, mul_assoc, mul_inv_cancel, mul_one]

instance finScalar_range_normal : ((finScalar (a : F) (b : F)).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨c, rfl⟩ := hn
  refine ⟨c, ?_⟩
  have hc : ∀ x : (QuatFin (a : F) (b : F))ˣ, finScalar (a : F) (b : F) c * x = x * finScalar (a : F) (b : F) c :=
    fun x => Units.ext (Algebra.commutes _ _)
  rw [← hc, mul_assoc, mul_inv_cancel, mul_one]

/-- $PD^\times(F_\infty) = (D\otimes F_\infty)^\times/F_\infty^\times$. -/
abbrev PDInf : Type := (QuatInf (a : F) (b : F))ˣ ⧸ (infScalar (a : F) (b : F)).range

/-- $PD^\times(\mathbb A_f) = (D\otimes\mathbb A_f)^\times/\mathbb A_f^\times$. -/
abbrev PDFin : Type := (QuatFin (a : F) (b : F))ˣ ⧸ (finScalar (a : F) (b : F)).range

theorem ker_conjInf (ha : a ≠ 0) : (conjInf a b).ker = (infScalar (a : F) (b : F)).range := by
  ext α; exact (MonoidHom.mem_ker).trans (conjInf_eq_one_iff a b ha α)

theorem ker_conjFin (ha : a ≠ 0) : (conjFin a b).ker = (finScalar (a : F) (b : F)).range := by
  ext α; exact (MonoidHom.mem_ker).trans (conjFin_eq_one_iff a b ha α)

/-- **$PD^\times(F_\infty) \cong G_\infty = \prod_w SO(Q^w)(F_w)$** as topological groups. -/
@[kb "weil1982" "§3.7(a), p. 63"]
def pdInfEquiv (ha : a ≠ 0) (hb : b ≠ 0) : PDInf a b ≃ₜ* GInfSO Q₀ :=
  quotientContinuousMulEquiv (conjInf a b) _ (ker_conjInf a b ha) (conjInf_surjective a b ha hb)
    (continuous_conjInf a b)
    (MonoidHom.isOpenMap_of_sigmaCompact _ (conjInf_surjective a b ha hb) (continuous_conjInf a b))

/-- **$PD^\times(\mathbb A_f) \cong SO(V)(\mathbb A_f)$** as topological groups. -/
@[kb "weil1982" "§3.7(a), p. 63"]
def pdFinEquiv (ha : a ≠ 0) (hb : b ≠ 0) : PDFin a b ≃ₜ* SOAf Q₀ :=
  quotientContinuousMulEquiv (conjFin a b) _ (ker_conjFin a b ha) (conjFin_surjective a b ha hb)
    (continuous_conjFin a b)
    (MonoidHom.isOpenMap_of_sigmaCompact _ (conjFin_surjective a b ha hb) (continuous_conjFin a b))

/-- The product isomorphism $PD^\times(F_\infty)\times PD^\times(\mathbb A_f) \cong SO(V)(\mathbb A)$. -/
def pdProdEquiv (ha : a ≠ 0) (hb : b ≠ 0) : PDInf a b × PDFin a b ≃ₜ* SOAdele Q₀ where
  toMulEquiv := (pdInfEquiv a b ha hb).toMulEquiv.prodCongr (pdFinEquiv a b ha hb).toMulEquiv
  continuous_toFun := (pdInfEquiv a b ha hb).continuous.prodMap (pdFinEquiv a b ha hb).continuous
  continuous_invFun := (pdInfEquiv a b ha hb).symm.continuous.prodMap (pdFinEquiv a b ha hb).symm.continuous

/-- $PD^\times(\mathbb A) \cong PD^\times(F_\infty)\times PD^\times(\mathbb A_f)$. -/
def pdSplit (ha : a ≠ 0) (hb : b ≠ 0) : PDAdele a b ≃ₜ* PDInf a b × PDFin a b :=
  (pdAdeleEquiv a b ha hb).trans (pdProdEquiv a b ha hb).symm

/-- $PD^\times(F)$ inside $PD^\times(F_\infty)\times PD^\times(\mathbb A_f)$. -/
def pdGammaSplit (ha : a ≠ 0) (hb : b ≠ 0) : Subgroup (PDInf a b × PDFin a b) :=
  (pdGamma a b).map (pdSplit a b ha hb).toMulEquiv.toMonoidHom

/-- **The product isomorphism carries $PD^\times(F)$ onto $SO(V)(F)$** (`GammaSOAdele`). -/
theorem map_pdGammaSplit (ha : a ≠ 0) (hb : b ≠ 0) :
    (pdGammaSplit a b ha hb).map ((pdInfEquiv a b ha hb).toMulEquiv.prodCongr
      (pdFinEquiv a b ha hb).toMulEquiv).toMonoidHom = GammaSOAdele Q₀ := by
  rw [pdGammaSplit, Subgroup.map_map, ← map_pdGamma a b ha hb]
  congr 1
  refine MonoidHom.ext fun x => ?_
  exact (pdProdEquiv a b ha hb).apply_symm_apply _

/-- $\langle -a,-b,ab\rangle$ over $\mathcal O_F$ is nondegenerate for $a, b \ne 0$. -/
theorem nondegenerate_pureFormO (ha : a ≠ 0) (hb : b ≠ 0) : (Q₀).Nondegenerate := by
  have hA : (a : F) ≠ 0 := by exact_mod_cast ha
  have hB : (b : F) ≠ 0 := by exact_mod_cast hb
  have h := pureForm_nondegenerate (two_ne_zero : (2 : F) ≠ 0) hA hB
  rw [← hQF a b] at h
  unfold QuadForm.Nondegenerate at h ⊢
  rw [QuadForm.hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  intro h0
  exact h (by rw [h0, map_zero])

/-! ### Measures and covolumes -/

instance : MeasurableSpace (PDInf a b) := borel _
instance : BorelSpace (PDInf a b) := ⟨rfl⟩
instance : MeasurableSpace (PDFin a b) := borel _
instance : BorelSpace (PDFin a b) := ⟨rfl⟩

instance countable_pdGammaSplit (ha : a ≠ 0) (hb : b ≠ 0) : Countable (pdGammaSplit a b ha hb) := by
  have h1 : Countable (pdGamma a b) := by
    refine Function.Surjective.countable (f := fun g : quatUnitsSub (a : F) (b : F) =>
      (⟨QuotientGroup.mk' _ g, g, g.2, rfl⟩ : pdGamma a b)) ?_
    rintro ⟨_, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  refine Function.Surjective.countable (f := fun g : pdGamma a b =>
    (⟨pdSplit a b ha hb g, g, g.2, rfl⟩ : pdGammaSplit a b ha hb)) ?_
  rintro ⟨_, g, hg, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

/-- **Transport of the Tamagawa covolume along $PD^\times \cong SO(D^0)$** (`covolume_eq_of_localFactors`).
For left-invariant s-finite measures $\mu_\infty$ on $PD^\times(F_\infty)$ and $\mu_f$ on $PD^\times(\mathbb A_f)$ with
$(c_\infty)_*\mu_\infty = r_\infty\,\mu^{\mathrm{Tam}}_\infty$, $(c_f)_*\mu_f = r_f\,\mu_f$ (`muArchTamSO`, `muFin` with $\lambda_v = 1$) and $r_\infty r_f = 1$ (Weil's product formula), the covolume of $PD^\times(F)$ equals
the covolume of $SO(V)(F)$ for `muTam`. -/
@[kb "weil1982" "§2.3, Thm 2.3.1; §3.7(a), p. 63"]
theorem covolume_pd_eq_covolume_muTam (ha : a ≠ 0) (hb : b ≠ 0) (hQ : (Q₀).Nondegenerate)
    (μI : Measure (PDInf a b)) (μF : Measure (PDFin a b)) [SFinite μI] [SFinite μF] [μI.IsMulLeftInvariant]
    [μF.IsMulLeftInvariant] {rI rF : ℝ≥0∞} (hI : μI.map (pdInfEquiv a b ha hb) = rI • muArchTamSO Q₀ hQ)
    (hF : μF.map (pdFinEquiv a b ha hb) = rF • QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1)) (hr : rI * rF = 1) :
    covolume (pdGammaSplit a b ha hb) (PDInf a b × PDFin a b) (μI.prod μF) =
      covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) :=
  covolume_eq_of_localFactors (pdGammaSplit a b ha hb) (GammaSOAdele Q₀)
    (pdInfEquiv a b ha hb).toMulEquiv (pdFinEquiv a b ha hb).toMulEquiv
    (pdInfEquiv a b ha hb).continuous.measurable (pdInfEquiv a b ha hb).symm.continuous.measurable
    (pdFinEquiv a b ha hb).continuous.measurable (pdFinEquiv a b ha hb).symm.continuous.measurable
    (map_pdGammaSplit a b ha hb) μI μF (muArchTamSO Q₀ hQ) (QuadFormsKB.Tamagawa.Measure.muFin Q₀ fun _ => 1) hI hF hr

/-- **`TamagawaNumberTwoAdelic` for $\langle -a,-b,ab\rangle$ $\iff$ $\tau(PD^\times) = 2$**, for every pair of
measures on $PD^\times(F_\infty)$, $PD^\times(\mathbb A_f)$ satisfying the product formula with the Tamagawa
measure of $SO(V)$. -/
@[kb "weil1982" "§2.3, Thm 2.3.1; §3.7(a), p. 63; Thm 3.2.1, p. 43"]
theorem tamagawaNumberTwoAdelic_iff_covolume_pd (ha : a ≠ 0) (hb : b ≠ 0) (hQ : (Q₀).Nondegenerate)
    (μI : Measure (PDInf a b)) (μF : Measure (PDFin a b)) [SFinite μI] [SFinite μF] [μI.IsMulLeftInvariant]
    [μF.IsMulLeftInvariant] {rI rF : ℝ≥0∞} (hI : μI.map (pdInfEquiv a b ha hb) = rI • muArchTamSO Q₀ hQ)
    (hF : μF.map (pdFinEquiv a b ha hb) = rF • QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1)) (hr : rI * rF = 1) :
    TamagawaNumberTwoAdelic Q₀ hQ ↔
      covolume (pdGammaSplit a b ha hb) (PDInf a b × PDFin a b) (μI.prod μF) = 2 := by
  rw [covolume_pd_eq_covolume_muTam a b ha hb hQ μI μF hI hF hr]
  rfl

/-- **$\tau(PD^\times) = 2$ for totally definite $D$ over a totally real field**, for every pair of measures satisfying
the product formula: by transport from `tamagawaNumberTwoAdelic_ternary` (the lattice route: Siegel's mass
formula for ternary forms), with no Fujisaki and no zeta function of $D$. -/
@[kb "weil1982" "Thm 3.2.1, p. 43; Thm 3.7.1 (m = 3), p. 65"]
theorem covolume_pd_eq_two_of_definite [IsTotallyReal F] (ha : a ≠ 0) (hb : b ≠ 0) (hQ : (Q₀).Nondegenerate)
    (hpd : IsTotallyPosDef (QuadFormsKB.HilbertModular.formF Q₀))
    (μI : Measure (PDInf a b)) (μF : Measure (PDFin a b)) [SFinite μI] [SFinite μF] [μI.IsMulLeftInvariant]
    [μF.IsMulLeftInvariant] {rI rF : ℝ≥0∞} (hI : μI.map (pdInfEquiv a b ha hb) = rI • muArchTamSO Q₀ hQ)
    (hF : μF.map (pdFinEquiv a b ha hb) = rF • QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1)) (hr : rI * rF = 1) :
    covolume (pdGammaSplit a b ha hb) (PDInf a b × PDFin a b) (μI.prod μF) = 2 :=
  (tamagawaNumberTwoAdelic_iff_covolume_pd a b ha hb hQ μI μF hI hF hr).1
    (tamagawaNumberTwoAdelic_ternary Q₀ hQ hpd)

end QuadFormsKB.Tamagawa.Measure.Weil
