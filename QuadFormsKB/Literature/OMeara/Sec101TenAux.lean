/-
# O'Meara §101B, Example 101:10: local and valuation lemmas

**Layer:** $F$ a number field, $V = F^n$ with `Q : QuadForm F n`; at a finite spot $\mathfrak p$ the completion
$F_\mathfrak p$ = `v.adicCompletion F`, $\mathfrak o_\mathfrak p$ = `v.adicCompletionIntegers F`, O'Meara's form on
$V_\mathfrak p$ = `qk Q F_𝔭`; abstract local fields: a complete discrete valuation ring $R$ with finite residue field
and fraction field $F$, $2 \in R^\times$.

**Proves** (inputs of `Sec101Ten.lean`)
* `OMeara.exists_hasSpinorNorm_unit_of_isUnimodular` (92:5, one direction): a unit of a unimodular lattice over a
  non-dyadic local field has unit spinor norm;
* `OMeara.exists_orthonormal_of_isUnimodular` (from 92:2): if $V$ carries a unimodular lattice and has square
  discriminant, then $V \cong \langle 1, \dots, 1\rangle$;
* `OMeara.exists_div_sq_valuation_eq_one` ($J_F = P_FJ_F^S$): an $a$ with even order at every spot of $S$ is an
  $S$-unit times a square;
* the bridges `hasSpinorNorm_symmProd`, `exists_hasSpinorNorm_orthMap` (one global spinor norm localizes),
  `glEquiv_orthMap_mem_orthLat`, `det_glEquiv_eq_neg_one`, `isUnimodular_std` ($\mathfrak o_\mathfrak p^n$ is
  unimodular where the matrix of the standard base is), `std_eq_matLat`, and `exists_local_improper` (Example 92:8 at
  such a spot).
-/
import QuadFormsKB.Literature.OMeara.Sec101Named
import QuadFormsKB.Literature.OMeara.Sec104Bridge
import QuadFormsKB.Literature.OMeara.Sec104LocalMod
import QuadFormsKB.Literature.OMeara.Sec92Gap
import QuadFormsKB.Literature.OMeara.Sec92SpinorUnits
import QuadFormsKB.Literature.OMeara.Sec92Class
import QuadFormsKB.Literature.OMeara.Sec65Rest
import QuadFormsKB.Literature.OMeara.Sec101BD
import QuadFormsKB.Lattices.SACorrection
import QuadFormsKB.Tamagawa.Reflection
import QuadFormsKB.LocalDensity.NFBridge
import QuadFormsKB.Literature.OMeara.Sec41Extra
import QuadFormsKB.Literature.OMeara.Sec65D
import QuadFormsKB.Literature.Cassels.Ch11Sec3
import QuadFormsKB.Literature.Hanke2011Structure.Lemma37Exist
import QuadFormsKB.Tamagawa.GeneralFactor
import QuadFormsKB.Tamagawa.ArchTestFn
import QuadFormsKB.Literature.OMeara.Sec82Classes
import QuadFormsKB.Literature.OMeara.Sec82Dual
import QuadFormsKB.Tamagawa.ArchTestFn

open NumberField IsDedekindDomain
open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section UnimodularLocal

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Units of a unimodular lattice have unit spinor norm** (O'Meara 1973, §92, 92:5, p. 249, the inclusion
$\theta(O(L)) \subseteq \mathfrak u\dot F^2$): over a non-dyadic local field, every $\sigma \in O(L)$, $L$ unimodular,
has O'Meara spinor norm $\varepsilon$ for some unit $\varepsilon$ (92:4 factors $\sigma$ into symmetries of $L$). -/
@[kb "omeara1963" "§92, 92:5, p. 249 (θ(O(L)) ⊆ 𝔲F² for unimodular L)"]
theorem exists_hasSpinorNorm_unit_of_isUnimodular (h2 : IsUnit (2 : R)) [FiniteDimensional F V]
    (hV : (QuadraticMap.associated Q).Nondegenerate) (hn : 1 ≤ finrank F V)
    {L : Submodule R V} (hL : L.IsLattice F) (hU : IsUnimodular Q L) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ orthLat Q L) : ∃ ε : R, IsUnit ε ∧ HasSpinorNorm Q σ (algebraMap R F ε) := by
  have hmod : IsModular Q (R ∙ (1 : F)) L := by
    have : (R ∙ (1 : F)) = 1 := (Submodule.one_eq_span).symm
    rw [this]; exact hU
  obtain ⟨l, -, hl, hσl⟩ := exists_symmetry_list Q h2 hV hn hL hσ
  have hQl : ∀ u ∈ l, Q u ≠ 0 := fun u hu => (hl u hu).1
  have hnorm : ∀ u ∈ l, ∃ t : F, t ≠ 0 ∧ ∃ ε : R, IsUnit ε ∧
      Q u = t ^ 2 * 1 * algebraMap R F ε := fun u hu => by
    obtain ⟨hu', hτ⟩ := hl u hu
    exact exists_Q_eq_of_symmetry_mem Q h2 hL hmod hu' hτ
  obtain ⟨t, ht, ε, hε, hprod⟩ := prod_Q_of_forall Q l hnorm
  refine ⟨ε, hε, l, hQl, ?_, t, ht, ?_⟩
  · rw [hσl]
    congr 1
    have : (l.attach.map fun u => symmetry Q u.1 (hQl u.1 u.2)) =
        l.attach.map fun u => symmetryOrOne Q u.1 :=
      List.map_congr_left fun u _ => (sym4_symmetryOrOne_of_ne Q _).symm
    rw [this]
    simp
  · rw [hprod]; ring

end UnimodularLocal

section OrthonormalLocal

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (ResidueField R)] [DecidableEq (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **A space with a unimodular lattice and square discriminant is $\langle 1, \dots, 1\rangle$** (O'Meara 1973,
§92, 92:2, p. 247, as used in 101:10): over a non-dyadic local field, if $V$ carries a unimodular lattice and the
discriminant of some base $f$ of $V$ is a square, then $V$ has an orthogonal base with all $Q(e_i) = 1$. -/
@[kb "omeara1963" "§92, 92:2, p. 247 (unimodular L ≅ ⟨1, …, 1, ε⟩)"]
theorem exists_orthonormal_of_isUnimodular (h2 : IsUnit (2 : R)) [FiniteDimensional F V]
    {L : Submodule R V} (hL : L.IsLattice F) (hU : IsUnimodular Q L) {m : ℕ} (f : Basis (Fin m) F V)
    (hf : IsSquare (gram Q f).det) :
    ∃ (k : ℕ) (e : Basis (Fin k) F V), (∀ i j, i ≠ j → bil Q (e i) (e j) = 0) ∧ ∀ i, Q (e i) = 1 := by
  classical
  have := hL
  obtain ⟨ε, hε, b, hb⟩ := exists_basis_diag_of_isUnimodular Q h2 hL.fg hU
  let e0 : Basis (Fin (finrank R L)) F V := b.extendOfIsLattice F
  have he0 : ∀ i, e0 i = (b i : V) := fun i => Basis.extendOfIsLattice_apply F b i
  have hm : m = finrank R L := by
    have h1 := Module.finrank_eq_card_basis f
    have h2' := Module.finrank_eq_card_basis e0
    simp only [Fintype.card_fin] at h1 h2'
    omega
  subst hm
  obtain ⟨α, hα0, hα⟩ := det_gram_basis_change Q f e0
  have hpos : 0 < finrank R L := by
    rcases Nat.eq_zero_or_pos (finrank R L) with h0 | h0
    · exfalso
      have hsc : scale Q L = ⊥ := by
        rw [← span_basis_eq b, scale_span, span_eq_bot]
        rintro _ ⟨p, rfl⟩; exact Fin.elim0 (h0 ▸ p.1)
      exact hU.1 (hU.2.1.symm.trans hsc)
    · exact h0
  let i0 : Fin (finrank R L) := ⟨finrank R L - 1, by omega⟩
  have hiff : ∀ i : Fin (finrank R L), i.val + 1 = finrank R L ↔ i = i0 := fun i => by
    rw [Fin.ext_iff]; simp only [i0]; omega
  have hgram : gram Q e0 = Matrix.diagonal fun i => if i = i0 then algebraMap R F ε else 1 := by
    ext i j
    simp only [gram, Matrix.of_apply, he0, hb, Matrix.diagonal_apply, hiff]
  have hdet : (gram Q e0).det = algebraMap R F ε := by
    rw [hgram, Matrix.det_diagonal, Finset.prod_ite_eq' Finset.univ i0]
    simp
  obtain ⟨t, ht⟩ := hf
  have hsq : algebraMap R F ε = (α * t) ^ 2 := by rw [← hdet, hα, ht]; ring
  have hε0 : algebraMap R F ε ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hε.ne_zero
  obtain ⟨s, hsdef⟩ : ∃ s, s = α * t := ⟨_, rfl⟩
  rw [← hsdef] at hsq
  have hs0 : s ≠ 0 := by
    rintro h
    exact hε0 (by rw [hsq, h]; ring)
  let y : Fin (finrank R L) → V := fun i => if i = i0 then s⁻¹ • (b i : V) else (b i : V)
  have hbil : ∀ i j, bil Q (y i) (y j) = if i = j then 1 else 0 := by
    intro i j
    have hbij := hb i j
    simp only [hiff] at hbij
    by_cases hij : i = j
    · subst hij
      simp only [y, ite_true]
      by_cases hi : i = i0
      · subst hi
        simp only [ite_true] at hbij ⊢
        rw [bil_rsmul_left, bil_rsmul_right, hbij, hsq]
        simp only [Algebra.algebraMap_self, RingHom.id_apply]
        field_simp
      · simp only [hi, ite_false] at hbij ⊢
        exact hbij
    · simp only [hij, ite_false] at hbij ⊢
      simp only [y]
      split_ifs <;> simp [bil_rsmul_left, hbij]
  have hQy : ∀ i, Q (y i) = 1 := fun i => by rw [← bil_self, hbil]; simp
  have horth : ∀ i j, i ≠ j → bil Q (y i) (y j) = 0 := fun i j h => by rw [hbil]; simp [h]
  have hli : LinearIndependent F y :=
    linearIndependent_of_orth (R := F) Q horth (fun i => by rw [hQy]; exact one_ne_zero)
  have hcard : Fintype.card (Fin (finrank R L)) = finrank F V := by
    rw [Module.finrank_eq_card_basis e0]
  have : Nonempty (Fin (finrank R L)) := ⟨i0⟩
  let e := basisOfLinearIndependentOfCardEqFinrank hli hcard
  refine ⟨finrank R L, e, fun i j h => ?_, fun i => ?_⟩
  · simp only [e, coe_basisOfLinearIndependentOfCardEqFinrank]; exact horth i j h
  · simp only [e, coe_basisOfLinearIndependentOfCardEqFinrank]; exact hQy i

end OrthonormalLocal

section Valuations

open WithZero

variable {F : Type} [Field F] [NumberField F]

theorem exists_unif_valuation {S : Set (HeightOneSpectrum (𝓞 F))} (hS : SConventions S)
    {p : HeightOneSpectrum (𝓞 F)} (hp : p ∈ S) :
    ∃ c : F, c ≠ 0 ∧ p.valuation F c = exp (-1 : ℤ) ∧ ∀ w ∈ S, w ≠ p → w.valuation F c = 1 := by
  have hmem : ∀ w, w ∉ hS.cofinite.toFinset ↔ w ∈ S := fun w => by simp
  obtain ⟨c, hcp, hcp2, hcw⟩ := exists_uniformizer hS p ((hmem p).mpr hp)
  have hc0 : c ≠ 0 := by rintro rfl; exact hcp2 (zero_mem _)
  refine ⟨(c : F), by exact_mod_cast hc0, ?_, fun w hw hwp => ?_⟩
  · rw [HeightOneSpectrum.valuation_of_algebraMap]
    have hle1 : p.intValuation c ≤ exp (-((1 : ℕ) : ℤ)) :=
      (p.intValuation_le_pow_iff_mem _ 1).mpr (by simpa using hcp)
    have hnle2 : ¬ p.intValuation c ≤ exp (-((2 : ℕ) : ℤ)) := fun h =>
      hcp2 ((p.intValuation_le_pow_iff_mem _ 2).mp h)
    have hne : p.intValuation c ≠ 0 := p.intValuation_ne_zero _ hc0
    rw [← exp_log hne] at hle1 hnle2 ⊢
    rw [exp_le_exp] at hle1 hnle2
    rw [exp_inj]
    push_cast at hle1 hnle2
    omega
  · rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hcw w ((hmem w).mpr hw) hwp

theorem exists_div_sq_valuation_eq_one_aux {S : Set (HeightOneSpectrum (𝓞 F))} (hS : SConventions S)
    {W : Set (HeightOneSpectrum (𝓞 F))} (hWS : W ⊆ S) (P : Finset (HeightOneSpectrum (𝓞 F))) :
    ∀ a : F, a ≠ 0 → (∀ v ∈ W, v ∉ P → v.valuation F a = 1) →
      (∀ v ∈ W, ∃ k : ℤ, v.valuation F a = exp (2 * k)) →
      ∃ β : F, β ≠ 0 ∧ ∀ v ∈ W, v.valuation F (a / β ^ 2) = 1 := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro a _ h1 _
    exact ⟨1, one_ne_zero, fun v hv => by simpa using h1 v hv (Finset.notMem_empty v)⟩
  | insert p P hpP ih =>
    intro a ha h1 heven
    by_cases hpW : p ∈ W
    · obtain ⟨k, hk⟩ := heven p hpW
      obtain ⟨c, hc0, hcp, hcw⟩ := exists_unif_valuation hS (hWS hpW)
      set u : F := c ^ k with hu
      have hu0 : u ≠ 0 := zpow_ne_zero _ hc0
      have hup : p.valuation F u = exp (-k) := by
        rw [hu, map_zpow₀, hcp, ← exp_zsmul]; congr 1; simp
      have huw : ∀ w ∈ S, w ≠ p → w.valuation F u = 1 := fun w hw hwp => by
        rw [hu, map_zpow₀, hcw w hw hwp, one_zpow]
      set a' := a * u ^ 2 with ha'
      have ha'0 : a' ≠ 0 := mul_ne_zero ha (pow_ne_zero _ hu0)
      have ha'p : p.valuation F a' = 1 := by
        rw [ha', map_mul, map_pow, hk, hup, ← exp_nsmul, ← exp_add]
        rw [← exp_zero]; congr 1; simp
      have ha'w : ∀ w ∈ W, w ≠ p → w.valuation F a' = w.valuation F a := fun w hw hwp => by
        rw [ha', map_mul, map_pow, huw w (hWS hw) hwp, one_pow, mul_one]
      obtain ⟨β', hβ'0, hβ'⟩ := ih a' ha'0 (fun v hv hvP => by
          by_cases hvp : v = p
          · subst hvp; exact ha'p
          · rw [ha'w v hv hvp]
            exact h1 v hv (by simp [hvp, hvP]))
        (fun v hv => by
          by_cases hvp : v = p
          · subst hvp; exact ⟨0, by rw [ha'p]; simp⟩
          · rw [ha'w v hv hvp]; exact heven v hv)
      refine ⟨β' * u⁻¹, mul_ne_zero hβ'0 (inv_ne_zero hu0), fun v hv => ?_⟩
      have e : a / (β' * u⁻¹) ^ 2 = a' / β' ^ 2 := by
        rw [ha']; field_simp
      rw [e]; exact hβ' v hv
    · exact ih a ha (fun v hv hvP => h1 v hv (by
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h => hpW (h ▸ hv), hvP⟩)) heven

/-- **$J_F = P_FJ_F^S$ turns even orders into units** (O'Meara 1973, §101B, p. 293, a step of 101:10): if $a \ne 0$
has even order at every spot of $W \subseteq S$, then $a/\beta^2$ is a unit at every spot of $W$ for some
$\beta \ne 0$. -/
@[kb "omeara1963" "§101B, 101:10, p. 293 (a/β² is a W-unit)"]
theorem exists_div_sq_valuation_eq_one {S : Set (HeightOneSpectrum (𝓞 F))} (hS : SConventions S)
    {W : Set (HeightOneSpectrum (𝓞 F))} (hWS : W ⊆ S) {a : F} (ha : a ≠ 0)
    (heven : ∀ v ∈ W, ∃ k : ℤ, v.valuation F a = exp (2 * k)) :
    ∃ β : F, β ≠ 0 ∧ ∀ v ∈ W, v.valuation F (a / β ^ 2) = 1 := by
  classical
  have hfin := Tamagawa.finite_valuation_ne_one ha
  exact exists_div_sq_valuation_eq_one_aux hS hWS hfin.toFinset a ha
    (fun v _ hvP => by by_contra h; exact hvP (hfin.mem_toFinset.mpr h)) heven


end Valuations

end QuadFormsKB.OMeara

namespace QuadFormsKB.Lattices

open OMeara.QIn (glEquiv glEquiv_apply glEquiv_symmProd map_orthGroup)

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-! ### Spinor norms of localized isometries in O'Meara's terms -/

section Bridge

/-- A product of symmetries $\tau_{x_1}\cdots\tau_{x_r}$ (`symmProd`) has O'Meara spinor norm
$Q(x_1)\cdots Q(x_r)$ (`valProd`). -/
theorem hasSpinorNorm_symmProd (K : Type) [Field K] [Algebra F K] [CharZero K] (xs : List (Fin n → K))
    (hxs : ∀ x ∈ xs, Q.evalIn K x ≠ 0) :
    OMeara.HasSpinorNorm (qk Q K) (glEquiv K ((symmProd Q K xs : orthGroup Q K) : GL (Fin n) K))
      (valProd Q K xs) := by
  have hl : ∀ u ∈ xs, qk Q K u ≠ 0 := fun u hu => by rw [qk_apply]; exact hxs u hu
  refine ⟨xs, hl, ?_, 1, one_ne_zero, ?_⟩
  · rw [glEquiv_symmProd Q K xs hxs]
    exact (OMeara.Cl54.attach_prod_eq_symProd (qk Q K) xs hl).symm
  · rw [one_pow, mul_one, valProd]
    congr 1
    exact List.map_congr_left fun x _ => qk_apply Q K x

/-- **One global spinor norm for all localizations**: for $\sigma \in O(V)$ there is $a \in F^\times$ such that at every
finite spot $\mathfrak p$ the localization $\sigma_\mathfrak p$ has O'Meara spinor norm $a$ (O'Meara 1973, §101A: the
spinor norm of $\sigma$, computed from one factorization into symmetries of $V$, localizes). -/
theorem exists_hasSpinorNorm_orthMap (hQ : Q.Nondegenerate) (σ : orthGroup Q F) :
    ∃ a : F, a ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 F),
      OMeara.HasSpinorNorm (qk Q (v.adicCompletion F))
        (glEquiv (v.adicCompletion F) ((orthMap Q (v.adicCompletion F) σ : orthGroup Q _) : GL (Fin n) _))
        (algebraMap F (v.adicCompletion F) a) := by
  obtain ⟨xs, hxs, rfl⟩ := exists_symmProd_eq Q F hQ σ
  refine ⟨valProd Q F xs, valProd_ne_zero Q F hxs, fun v => ?_⟩
  have hxs' : ∀ y ∈ xs.map (locVec v), Q.evalIn (v.adicCompletion F) y ≠ 0 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    rw [evalIn_locVec]
    exact (map_ne_zero _).mpr (hxs x hx)
  rw [orthMap_symmProd, ← valProd_map_locVec]
  exact hasSpinorNorm_symmProd Q _ _ hxs'

/-- The determinant of `glEquiv g` is $-1$ when the matrix $g$ has determinant $-1$. -/
theorem det_glEquiv_eq_neg_one (K : Type) [Field K] [Algebra F K] [CharZero K] {g : GL (Fin n) K}
    (h : (g : Matrix (Fin n) (Fin n) K).det = -1) : LinearEquiv.det (glEquiv K g) = -1 := by
  ext
  rw [LinearEquiv.coe_det, Units.val_neg, Units.val_one, ← det_eq_glEquiv, h]

end Bridge

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- If $\sigma L = L$ globally, then $\sigma_\mathfrak p \in O(L_\mathfrak p)$ in O'Meara's sense. -/
theorem glEquiv_orthMap_mem_orthLat {σ : orthGroup Q F} {L : Submodule (𝓞 F) (Fin n → F)}
    (hσ : glImage (σ : GL (Fin n) F) L = L) :
    glEquiv Fv ((orthMap Q Fv σ : orthGroup Q Fv) : GL (Fin n) Fv) ∈ OMeara.orthLat (qk Q Fv) (loc v L) := by
  refine ⟨?_, ?_⟩
  · rw [← map_orthGroup Q Fv]
    exact Subgroup.mem_map.mpr ⟨_, (orthMap Q Fv σ).2, rfl⟩
  · rw [← locAct_eq_latMap]
    have := loc_glImage v (σ : GL (Fin n) F) L
    rw [hσ] at this
    exact this.symm

/-- If $a = \varepsilon s^2$ in $F_\mathfrak p$ with $\varepsilon$ a unit, then $\operatorname{ord}_\mathfrak p a$ is
even. -/
theorem exists_valuation_eq_exp_two_mul {a : F} {ε : 𝔬} (hε : IsUnit ε) {s : Fv} (hs : s ≠ 0)
    (h : algebraMap F Fv a = algebraMap 𝔬 Fv ε * s ^ 2) : ∃ k : ℤ, v.valuation F a = WithZero.exp (2 * k) := by
  have hε1 : Valued.v (algebraMap 𝔬 Fv ε) = 1 :=
    (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hε
  have hs0 : Valued.v s ≠ 0 := (map_ne_zero _).mpr hs
  refine ⟨WithZero.log (Valued.v s), ?_⟩
  rw [← valued_algebraMap, h, map_mul, hε1, one_mul, map_pow, ← WithZero.exp_log hs0, ← WithZero.exp_nsmul]
  congr 1

/-- A unit of $\mathfrak o_\mathfrak p$ which is a square in $F_\mathfrak p$ is a square in $\mathfrak o_\mathfrak p$. -/
theorem isSquare_of_isSquare_algebraMap {Δ : 𝔬} (hΔ : IsUnit Δ) (h : IsSquare (algebraMap 𝔬 Fv Δ)) :
    IsSquare Δ := by
  obtain ⟨t, ht⟩ := h
  have hΔ1 : Valued.v (algebraMap 𝔬 Fv Δ) = 1 :=
    (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hΔ
  have ht1 : Valued.v t ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have : (1 : WithZero (Multiplicative ℤ)) < Valued.v t * Valued.v t :=
      one_lt_mul_of_lt_of_le' hlt hlt.le
    rw [← map_mul, ← ht, hΔ1] at this
    exact lt_irrefl _ this
  refine ⟨⟨t, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ht1⟩, ?_⟩
  exact Subtype.ext ht

/-- **The standard lattice $\mathfrak o_\mathfrak p^n$ is O'Meara's free lattice $\langle\,\cdot\,\rangle$** spanned by the
standard base (`OMeara.matLat`). -/
theorem std_eq_matLat : (std v : Submodule 𝔬 (Fin n → Fv)) = OMeara.matLat 𝔬 (Fin n) := by
  apply le_antisymm
  · intro x hx
    have hx' : x = ∑ i, (⟨x i, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr
        (by simpa using hx i)⟩ : 𝔬) • (Pi.single i 1 : Fin n → Fv) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
    rw [hx']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [OMeara.matLat, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact single_one_mem_std v i

/-- The O'Meara matrix of the standard base of $F_\mathfrak p^n$ is the image of the matrix of the standard base of $F^n$
(for the form $Q$, `qk`). -/
theorem gram_qk_single :
    OMeara.gram (qk Q Fv) (fun i => (Pi.single i 1 : Fin n → Fv)) =
      (OMeara.gram Q.toQuadraticForm (fun i => (Pi.single i 1 : Fin n → F))).map (algebraMap F Fv) := by
  rw [qk_eq_toQuadraticForm_map, ← gram_locVec]
  simp only [locVec_single, map_one]

/-- **$\mathfrak o_\mathfrak p^n$ is unimodular** when $\mathfrak p$ is non-dyadic... (any $\mathfrak p$) at which every
non-zero entry and the determinant of the matrix $G$ of the standard base are units. -/
theorem isUnimodular_std (hn : 0 < n)
    (hG : ∀ i j, OMeara.gram Q.toQuadraticForm (fun i => (Pi.single i 1 : Fin n → F)) i j ≠ 0 →
      v.valuation F (OMeara.gram Q.toQuadraticForm (fun i => (Pi.single i 1 : Fin n → F)) i j) = 1)
    (hd : v.valuation F (OMeara.gram Q.toQuadraticForm (fun i => (Pi.single i 1 : Fin n → F))).det = 1) :
    OMeara.IsUnimodular (qk Q Fv) (std v : Submodule 𝔬 (Fin n → Fv)) := by
  classical
  set G := OMeara.gram Q.toQuadraticForm (fun i => (Pi.single i 1 : Fin n → F)) with hGdef
  have hmem : ∀ i j, algebraMap F Fv (G i j) ∈ v.adicCompletionIntegers F := fun i j => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]
    by_cases h0 : G i j = 0
    · rw [h0, map_zero]; exact zero_le
    · rw [hG i j h0]
  let U : Matrix (Fin n) (Fin n) 𝔬 := fun i j => ⟨algebraMap F Fv (G i j), hmem i j⟩
  have hU : U.map (algebraMap 𝔬 Fv) = G.map (algebraMap F Fv) := rfl
  let b0 := Basis.span (OMeara.linearIndependent_single 𝔬 (F := Fv) (ι := Fin n))
  let b : Basis (Fin n) 𝔬 (std v : Submodule 𝔬 (Fin n → Fv)) :=
    b0.map (LinearEquiv.ofEq _ _ (std_eq_matLat v).symm)
  have hb : ∀ i, (b i : Fin n → Fv) = Pi.single i 1 := fun i => by
    simp only [b, Basis.map_apply]
    exact congrArg Subtype.val (Basis.span_apply _ i)
  rw [OMeara.isUnimodular_iff_gram (qk Q Fv) b]
  refine ⟨⟨⟨0, hn⟩⟩, U, ?_, ?_⟩
  · rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have : ((U.det : 𝔬) : Fv) = (G.map (algebraMap F Fv)).det := by
      rw [← hU]
      exact RingHom.map_det (algebraMap 𝔬 Fv) U
    rw [this, show (G.map (algebraMap F Fv)).det = algebraMap F Fv G.det from (RingHom.map_det _ G).symm,
      valued_algebraMap, hd]
  · rw [hU, ← gram_qk_single]
    simp only [hb]

end Local

/-! ### The local lattices of Example 92:8 at a spot where $V$ has an orthonormal base -/

section LocalLattice

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem nondegenerate_qk (hQ : Q.Nondegenerate) : (QuadraticMap.associated (qk Q Fv)).Nondegenerate :=
  QuadraticMap.nondegenerate_associated_iff.mpr
    (QuadraticMap.nondegenerate_polar_iff.mp (QuadForm.nondegenerate_polarBilin_toQuadraticFormIn Fv hQ))

/-- **Example 92:8 at a non-dyadic spot with $\mathfrak o_\mathfrak p^n$ unimodular and square discriminant**: for even
$n \ge 2$ and a unit $\varepsilon$ there is a lattice $M$ on $V_\mathfrak p$ such that every improper
$\sigma \in O(M)$ has spinor norm in $\varepsilon F_\mathfrak p^{\times 2}$. (By 92:2 $\mathfrak o_\mathfrak p^n \cong
\langle 1, \dots, 1\rangle$, `exists_orthonormal_of_isUnimodular`, so 92:8 applies.) -/
theorem exists_local_improper (hQ : Q.Nondegenerate) (hn : 2 ≤ n) (hev : Even n) (h2 : IsUnit (2 : 𝔬))
    (hU : OMeara.IsUnimodular (qk Q Fv) (std v : Submodule 𝔬 (Fin n → Fv)))
    (hsq : IsSquare (OMeara.gram (qk Q Fv) (fun i => (Pi.single i 1 : Fin n → Fv))).det) {ε : 𝔬}
    (hε : IsUnit ε) :
    ∃ M : Submodule 𝔬 (Fin n → Fv), M.IsLattice Fv ∧
      ∀ σ ∈ OMeara.orthLat (qk Q Fv) M, LinearEquiv.det σ = -1 → ∀ c : Fv,
        OMeara.HasSpinorNorm (qk Q Fv) σ c → ∃ s : Fv, s ≠ 0 ∧ c = algebraMap 𝔬 Fv ε * s ^ 2 := by
  have hstd : (std v : Submodule 𝔬 (Fin n → Fv)).IsLattice Fv := isLattice_of_bounds v le_rfl le_rfl
  have hf : IsSquare (OMeara.gram (qk Q Fv) (Pi.basisFun Fv (Fin n))).det := by
    rw [OMeara.basisFun_coe]; exact hsq
  obtain ⟨k, e, he, hQe⟩ := OMeara.exists_orthonormal_of_isUnimodular (qk Q Fv) h2 hstd hU
    (Pi.basisFun Fv (Fin n)) hf
  have hfr : Module.finrank Fv (Fin n → Fv) = n := Module.finrank_fin_fun Fv
  obtain ⟨M, hM, -, hMimp⟩ := OMeara.exists_lattice_improper_spinorNorm (qk Q Fv) h2 (nondegenerate_qk Q v hQ) e
    he hQe (by rw [hfr]; exact hev) (by omega) hε
  exact ⟨M, hM, hMimp⟩

end LocalLattice

end QuadFormsKB.Lattices
