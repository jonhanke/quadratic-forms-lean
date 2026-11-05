import QuadFormsKB.Literature.Hanke2005.Cor52Real
import QuadFormsKB.Literature.Hanke2005.HilbertUnitsCompletion
import QuadFormsKB.Tamagawa.BinaryCMLocalType
import QuadFormsKB.Literature.OMeara.Sec91
import QuadFormsKB.Literature.Cassels.Ch11Sec3Local
import QuadFormsKB.Literature.Hanke2005.SpinorIdeleMain
import QuadFormsKB.Tamagawa.Reflection

/-!
# The counterexample to Hanke's Corollary 5.2(ii): local conditions at the finite places

* `isSquare_algebraMap_of_two_mem`: at a place $v\mid2$, a unit $\delta\in\mathcal O_F$ with $x^2=\delta+8w$ is a square in
  $F_v$ (Hensel / the Local Square Theorem $1+4\mathfrak p\subseteq\mathfrak o^{\times2}$, O'Meara 63:1).
-/

open NumberField IsDedekindDomain WithZero

noncomputable section

namespace QuadFormsKB.Hanke2005.Cor52

open QuadFormsKB QuadFormsKB.Lattices

section Dyadic

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "𝔬" => v.adicCompletionIntegers F

theorem iota_mem_maximalIdeal {n : 𝓞 F} (hn : n ∈ v.asIdeal) :
    algebraMap (𝓞 F) 𝔬 n ∈ IsLocalRing.maximalIdeal 𝔬 := by
  rw [QuadFormsKB.Tamagawa.BinaryCM.mem_maximalIdeal_iff_valued (v := v)]
  have h := QuadFormsKB.LocalDensity.NF.valued_ι v n
  rw [h]
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v n).mpr hn

/-- **A unit $\delta$ with $x^2\equiv\delta\pmod{8}$ is a square at every dyadic place** (Local Square Theorem). -/
theorem isSquare_algebraMap_of_two_mem (h2 : (2 : 𝓞 F) ∈ v.asIdeal) (δ x w : 𝓞 F) (hδ : IsUnit δ)
    (h : x ^ 2 = δ + 8 * w) : IsSquare (algebraMap F (v.adicCompletion F) (δ : F)) := by
  have m2 := iota_mem_maximalIdeal v h2
  have hx : algebraMap (𝓞 F) 𝔬 x ^ 2 = algebraMap (𝓞 F) 𝔬 δ + 8 * algebraMap (𝓞 F) 𝔬 w := by
    have := congrArg (algebraMap (𝓞 F) 𝔬) h
    simpa [map_add, map_mul, map_pow, map_ofNat] using this
  have hδ' : IsUnit (algebraMap (𝓞 F) 𝔬 δ) := hδ.map _
  set X := algebraMap (𝓞 F) 𝔬 x
  set D := algebraMap (𝓞 F) 𝔬 δ
  set W := algebraMap (𝓞 F) 𝔬 w
  set T := algebraMap (𝓞 F) 𝔬 2
  have h8 : (8 : 𝔬) = 4 * T := by
    simp only [T, map_ofNat]; norm_num
  have hXu : IsUnit X := by
    by_contra hXn
    have hXm : X ∈ IsLocalRing.maximalIdeal 𝔬 := hXn
    have : D ∈ IsLocalRing.maximalIdeal 𝔬 := by
      have e : D = X ^ 2 - 8 * W := by rw [hx]; ring
      rw [e]
      refine Ideal.sub_mem _ (Ideal.pow_mem_of_mem _ hXm 2 (by norm_num)) ?_
      rw [h8]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ m2)
    exact (IsLocalRing.mem_maximalIdeal _).mp this |> fun h => h hδ'
  obtain ⟨U, hU⟩ := hXu.exists_right_inv
  have hm : -(T * W * U ^ 2) ∈ IsLocalRing.maximalIdeal 𝔬 :=
    Ideal.neg_mem_iff _ |>.mpr (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ m2))
  obtain ⟨S, hS⟩ := QuadFormsKB.OMeara.isSquare_one_add_four_mul hm
  have hD : D = (X * S) ^ 2 := by
    have e1 : D * U ^ 2 = 1 + 4 * (-(T * W * U ^ 2)) := by
      have : D = X ^ 2 - 8 * W := by rw [hx]; ring
      rw [this, h8]
      have hXU : X * U = 1 := hU
      linear_combination (X * U + 1) * hXU
    calc D = D * (X * U) ^ 2 := by rw [hU]; ring
      _ = X ^ 2 * (D * U ^ 2) := by ring
      _ = (X * S) ^ 2 := by rw [e1, hS]; ring
  refine ⟨((X * S : 𝔬) : v.adicCompletion F), ?_⟩
  have := congrArg (fun z : 𝔬 => (z : v.adicCompletion F)) hD
  push_cast at this
  have e : algebraMap F (v.adicCompletion F) (δ : F) = (D : v.adicCompletion F) := rfl
  rw [e, this]
  push_cast
  ring

end Dyadic

section Odd

open QuadFormsKB.Hanke2005.SpinorIdele

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F))

local notation "Q" => Q₀.map (algebraMap (𝓞 F) F)
local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $Q_0$ is integral on $\mathfrak o_v^n$. -/
theorem valued_evalIn_std_le_one {x : Fin n → Fv} (hx : x ∈ std v) : Valued.v ((Q).evalIn Fv x) ≤ 1 := by
  set y : Fin n → 𝔬 := fun i => ⟨x i, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (by
    have := hx i; rwa [neg_zero, WithZero.exp_zero] at this)⟩
  have hxy : x = fun i => ((y i : 𝔬) : Fv) := rfl
  rw [hxy, QuadFormsKB.Tamagawa.evalIn_coe_o v Q₀ y]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp ((LocalDensity.NF.Qp v Q₀).eval y).2

/-- The Gram matrix of $\mathfrak o_v^n$ is the Hessian. -/
theorem locGram_one_det : (locGram (Q) v 1).det = algebraMap (𝓞 F) Fv Q₀.hessian.det := by
  have : locGram (Q) v 1 = Q₀.hessian.map (algebraMap (𝓞 F) Fv) := by
    ext k l
    simp [locGram, QuadForm.hessian_map, IsScalarTower.algebraMap_apply (𝓞 F) F Fv]
  rw [this]
  exact (RingHom.map_det (algebraMap (𝓞 F) Fv) Q₀.hessian).symm

/-- **$\sigma(SO(L_v))\subseteq\mathfrak o_v^\times F_v^{\times2}$ at a non-dyadic place where $\mathfrak o_v^n$ is unimodular**
($n\ge2$, $v\nmid 2\det H$): the other half of O'Meara 92:5 / Cassels Ch. 11 Lemma 3.3. -/
@[kb "cassels1978" "Ch. 11, Lemma 3.3, p. 208 (over F_𝔭, 𝔭 ∤ 2)"]
theorem isUnitSqClass_of_mem_sigmaFin (hn : 2 ≤ n) (hQ : (Q).Nondegenerate) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (hdet : Q₀.hessian.det ∉ v.asIdeal) {c : Fv} (hc : c ≠ 0) (hmem : sqClassOf c ∈ sigmaFin (Q) hQ v) :
    IsUnitSqClass v (sqClassOf c) := by
  have hL : loc v (stdLat : Lat F n).1 = std v := loc_intVec v
  have hγ : loc v (stdLat : Lat F n).1 = locAct v (1 : GL (Fin n) Fv) (std v) := by
    rw [locAct_one]; exact hL
  have hint : ∀ x ∈ loc v (stdLat : Lat F n).1, Valued.v ((Q).evalIn Fv x) ≤ 1 := by
    intro x hx; rw [hL] at hx; exact valued_evalIn_std_le_one Q₀ v hx
  have hdet' : Valued.v (locGram (Q) v 1).det = 1 := by
    rw [locGram_one_det, valued_algebraMap_int, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hdet
  have hmem' : Units.mk0 c hc ∈ localSpinorNormGroup (Q) hQ v stdLat := by
    rw [mem_localSpinorNormGroup]
    rw [mem_sigmaFin] at hmem
    obtain ⟨g, hg, hgc⟩ := hmem
    refine ⟨g, ⟨(locStabV_eq_stdStab (Q) v stdLat hL).mpr hg.1, hg.2⟩, ?_⟩
    rw [hgc, sqClassOf_of_ne_zero hc]
  have := (mem_localSpinorNormGroup_iff_of_unimodular (Q) v hQ h2 hn stdLat 1 hγ
    hint hdet' (Units.mk0 c hc)).mp hmem'
  rwa [← sqClassOf_of_ne_zero hc] at this

end Odd

end QuadFormsKB.Hanke2005.Cor52
