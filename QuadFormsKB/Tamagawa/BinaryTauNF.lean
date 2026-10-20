import QuadFormsKB.Tamagawa.BinaryCMDiscr
import QuadFormsKB.Tamagawa.SiegelRank3NF

/-!
# $\tau^{\mathrm{reg}}(SO_2) = 2$ and rank-3 Siegel over every totally real field

**Layer:** $F$ a totally real number field (any class number).

**Proves (unconditional)**
* **`massFormula_diagForm1_nf`**: for every $D \in \mathcal O_F$ with $\langle1,D\rangle$ totally positive definite,
  $\mathrm{Mass}(\mathcal O_F^2,\langle1,D\rangle)\cdot S^{\mathrm{reg}}_2(\langle1,D\rangle,1) = 1$ — the mass formula of the order $\mathcal O_F[\sqrt{-D}]$ with
  Siegel's local factors at the number $1$;
* **`binaryTamagawaTwoRegDiag_nf`**, **`binaryTamagawaTwoReg_nf`**: $\tau^{\mathrm{reg}}(SO(Q')) = 2$ for every totally positive definite
  binary $Q'$ over $\mathcal O_F$;
* **`siegelFormulaAt3_nf_uncond`**: Siegel's formula in rank $3$ over $F$ for every totally positive definite ternary $Q_0$ and every
  totally positive $m$; **`siegelFormulaAt3_natural_nf_uncond`**: the natural-order reading, given only `NaturalOrderEulerOne (chiTern Q₀ m)`.

*Proof of the mass formula:* $E = F(\sqrt{-D})$ (`exists_sqrtExt_of_not_isSquare`), and `massFormula_of_discr` (the mass of $\mathcal O_E$,
The local factors, the regulator relation) with the discriminant relation `discr_relation` (conductor and different).

Source: Siegel 1935, Hauptsatz; Weil 1982, Thm. 3.7.1 (τ = 2) [unverified locators]; Shimura 2010, §4 [unverified].

-/

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices NFEuler RegProd LocalDensity QuadForm QuadFormsKB.HilbertModular Binary.Rel BinaryNormOne BinaryCM

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- **The mass formula of $\mathcal O_F[\sqrt{-D}]$ over every totally real field** (unconditional): for $\langle1,D\rangle$ totally positive
definite, $\mathrm{Mass}(\mathcal O_F^2,\langle1,D\rangle)\cdot S^{\mathrm{reg}}_2(\langle1,D\rangle, 1) = 1$. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (mass formula of a binary norm form), over a totally real field [unverified]"]
theorem massFormula_diagForm1_nf (D : 𝓞 F) (hpd : IsTotallyPosDef (formF (diagForm1 D))) :
    mass (formF (diagForm1 D)) (stdLat F 2) * siegelProduct2Reg (diagForm1 D) 1 = 1 := by
  classical
  have hQ := nondegenerate_of_isTotallyPosDef hpd
  have hD : D ≠ 0 := by
    intro h; apply hQ; rw [hessian_det_diagForm1, h, mul_zero]
  have hsq : ¬ IsSquare (algebraMap (𝓞 F) F (-D)) := by
    rintro ⟨r, hr⟩
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h := congrArg (realEmb F w) hr
    have hd := realEmb_det_hessian_pos hpd w
    rw [hessian_det_diagForm1, map_mul, map_mul, map_ofNat, map_ofNat] at hd
    rw [map_neg, map_neg, map_mul] at h
    nlinarith [mul_self_nonneg (realEmb F w r)]
  obtain ⟨E, _, _, _, _, s, hs, hsc⟩ := exists_sqrtExt_of_not_isSquare hsq
  let S : SqrtData D E := ⟨s, by rw [hs, map_neg, map_neg], hsc, hD⟩
  set T := (finite_ramified (F := F) (E := E)).toFinset
  have hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0 := fun 𝔭 => Set.Finite.mem_toFinset _
  have hD2 : (2 * D : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero hD
  set U := T ∪ (Siegel.finite_mem_asIdeal hD2).toFinset
  have hU : ∀ v ∉ U, (2 * D : 𝓞 F) ∉ v.asIdeal := fun v hv h =>
    hv (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h))
  exact massFormula_of_discr S hpd hT Finset.subset_union_left hU (discr_relation (S := S) hU)

/-- **$\tau^{\mathrm{reg}}(SO_2) = 2$ over every totally real field** (the representatives $\langle1,D\rangle$; unconditional). -/
@[kb "weil1982" "Thm. 3.7.1 (τ = 2), rank 2 with convergence factors, over a totally real field [unverified]"]
theorem binaryTamagawaTwoRegDiag_nf : BinaryTamagawaTwoRegDiag F :=
  binaryTamagawaTwoRegDiag_iff_massFormula.mpr massFormula_diagForm1_nf

/-- **$\tau^{\mathrm{reg}}(SO(Q')) = 2$ for every totally positive definite binary form over a totally real field** (unconditional). -/
@[kb "weil1982" "Thm. 3.7.1 (τ = 2), rank 2 with convergence factors, over a totally real field [unverified]"]
theorem binaryTamagawaTwoReg_nf : BinaryTamagawaTwoReg F :=
  binaryTamagawaTwoRegDiag_nf.toReg

/-- **Rank-3 Siegel over every totally real field** (unconditional): for every totally positive definite ternary $Q_0$ over $\mathcal O_F$
and every totally positive $m$, `SiegelFormulaAt3 Q₀ m` (`siegelFormulaAt3_nf` with `binaryTamagawaTwoRegDiag_nf`). -/
@[kb "siegel1935" "Hauptsatz, n = 3, over a totally real field (regularized product) [unverified]"]
theorem siegelFormulaAt3_nf_uncond (Q₀ : QuadForm (𝓞 F) 3) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt3 Q₀ m :=
  siegelFormulaAt3_nf binaryTamagawaTwoRegDiag_nf Q₀ hpd hm

/-- **The natural-order reading over $F$**, with the single named input `NaturalOrderEulerOne (chiTern Q₀ m)`. -/
@[kb "hanke2004" "(5.3), p. 368 (n = 3, natural order), over a totally real field"]
theorem siegelFormulaAt3_natural_nf_uncond (Q₀ : QuadForm (𝓞 F) 3) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (hN : NaturalOrderEulerOne (chiTern Q₀ m)) :
    HasProd (fun v => NF.localDensity v Q₀ m) (regProd (chiTern Q₀ m) 1 fun v => NF.localDensity v Q₀ m)
        (normOrder F) ∧
      SiegelFormulaAt3 Q₀ m :=
  siegelFormulaAt3_natural_nf binaryTamagawaTwoRegDiag_nf Q₀ hpd hm hN

end QuadFormsKB.Tamagawa
