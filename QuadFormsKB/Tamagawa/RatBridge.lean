/-
# The lattice route over $\mathbb Q$: the bridge from forms over $\mathbb Z$ to lattices over $\mathcal O_{\mathbb Q}$

**Layer.** The rank-4 Siegel formula over $\mathbb Q$ (`Siegel.GenusEis.siegelFormula_quaternary`) is stated for integral
quadratic forms `Q : QuadForm ℤ N` with Hanke's objects: $\mathrm{GL}_N(\mathbb Z)$-classes in the genus (`Siegel.genusClasses`,
`Siegel.SameGenus`: equivalence over every $\mathbb Z_p$ and over $\mathbb R$), $\mathrm{Mass}(Q) = \sum 1/|\mathrm{Aut}(Q')|$
(`Siegel.mass`), $\sum r_{Q'}(m)/|\mathrm{Aut}(Q')|$ (`Siegel.genusRepSum`) and $a_E(m) = \beta_\infty(m)\prod_p\beta_p(m)$
(`Siegel.aE`, $\beta_p$ by counting modulo $p^k$). The lattice route works with lattices in $(F^N, Q_0)$ for
`Q₀ : QuadForm (𝓞 F) N`: the classes of lattices in the genus of $\mathcal O_F^N$ (`Lattices.genusClasses`), `Lattices.mass`,
`Tamagawa.repMass`, and `siegelProduct` with $\beta_\mathfrak p$ = `NF.localDensity` and the archimedean factors
`archRepDensity`. This file proves that **at $F = \mathbb Q$ the two dictionaries agree term by term** (with
$\mathcal O_{\mathbb Q} \cong \mathbb Z$, Mathlib's `Rat.ringOfIntegersEquiv`):

| ℤ-side | 𝓞_ℚ-side (lattices) | Lean |
|---|---|---|
| $\mathrm{GL}_N(\mathbb Z)$-classes in $\mathrm{gen}(Q)$ | classes of lattices in $\mathrm{gen}(\mathbb Z^N)$ in $(\mathbb Q^N, Q)$ | `bijOn_latClass_rat` |
| $|\mathrm{Aut}(Q')|$ | $|O(M)|$ | `card_autLat_latOf`, `autCard_eq_zForm` |
| $r_{Q'}(m)$ | $r_M(m)$ | `repCount_latOf`, `repCount_eq_zForm` |
| `Siegel.mass Q` | `Lattices.mass` | `mass_rat` |
| `Siegel.genusRepSum Q m` | `repMass` | `repMass_rat` |
| `Siegel.aE Q m` | `siegelProduct` | `siegelProduct_up` |
| `Siegel.SiegelFormula Q` | `SiegelFormulaAt` for every $m \ge 1$ | `siegelFormula_iff_siegelFormulaAt` |

The genus comparison is the only global input: a form $Q'$ in the genus of $Q$ is $\mathbb Q$-equivalent to $Q$ (Hasse–Minkowski,
`isometric_of_everywhere`, proved in the repository), so $Q'$ is the Gram form of a lattice $\gamma\mathbb Z^N$ in the space of $Q$.
Everything else is local (prime by prime: $\mathfrak o_{(p)} \cong \mathbb Z_p$, $\mathcal O_{\mathbb Q}/\mathfrak p^k \cong \mathbb Z/p^k$) or a
change of basis.
**Consequences** (`Consequences` section). Rank-4 `SiegelFormulaAt` over $\mathbb Q$ is a theorem (`siegelFormulaAt_rat_four`, from
`siegelFormula_quaternary`), which is what the Weil route lacked at $F = \mathbb Q$ (the rank-4 formula needs $[F:\mathbb Q] \ge 2$). Hence:
* `ternaryTamagawaTwo_iff_quaternary_rat`: `TernaryTamagawaTwo ℚ ↔ QuaternaryTamagawaTwo ℚ` (the step both ways; `TauFour`'s `_of_siegel` forms);
* `tamagawaNumberTwo_rat_all_ranks`: $\tau(SO) = 2$ over $\mathbb Q$ in every rank $N \ge 3$, given `TernaryTamagawaTwo ℚ` and
  `OddRankOrbitalLocalIdentities ℚ`;
* `siegelFormulaAt_rat_even` (unconditional) and `siegelFormulaAt_rat_all_ranks` (odd $N$ on the same two inputs): Siegel's formula over
  $\mathbb Q$ in every rank $N \ge 4$, the form; `siegelFormula_int_even`, `siegelFormula_int_all_ranks`: the same in Hanke's form
  `Siegel.SiegelFormula` for positive definite forms over $\mathbb Z$.
-/
import QuadFormsKB.Siegel.Tartakowsky
import QuadFormsKB.Siegel.SiegelQuaternary

open NumberField Matrix IsDedekindDomain
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.RatBridge

open QuadFormsKB.Lattices QuadFormsKB.HilbertModular

variable {n : ℕ}

/-! ### $\mathcal O_{\mathbb Q} = \mathbb Z$ -/

/-- $\mathcal O_{\mathbb Q} \cong \mathbb Z$ (Mathlib). -/
abbrev eZ : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv

/-- The integral form $Q \otimes \mathcal O_{\mathbb Q}$ (`Siegel.toOQ`). -/
abbrev up (Q : QuadForm ℤ n) : QuadForm (𝓞 ℚ) n := Siegel.toOQ Q

/-- A form over $\mathcal O_{\mathbb Q}$ as a form over $\mathbb Z$. -/
abbrev down (Q₀ : QuadForm (𝓞 ℚ) n) : QuadForm ℤ n := Q₀.map (eZ : 𝓞 ℚ →+* ℤ)

theorem castOQ_eq_symm : (Int.castRingHom (𝓞 ℚ)) = (eZ.symm : ℤ →+* 𝓞 ℚ) := RingHom.ext_int _ _

theorem toOQ_eq_cast : Lattices.toOQ = Int.castRingHom (𝓞 ℚ) := RingHom.ext_int _ _

theorem up_down (Q₀ : QuadForm (𝓞 ℚ) n) : up (down Q₀) = Q₀ := by
  rw [up, Siegel.toOQ, down, QuadForm.map_map, castOQ_eq_symm]
  ext i j
  simp [QuadForm.map]

theorem down_up (Q : QuadForm ℤ n) : down (up Q) = Q := by
  rw [up, Siegel.toOQ, down, QuadForm.map_map]
  ext i j
  simp [QuadForm.map]

theorem down_map_eval (Q₀ : QuadForm (𝓞 ℚ) n) (x : Fin n → 𝓞 ℚ) :
    (down Q₀).eval (fun i => eZ (x i)) = eZ (Q₀.eval x) :=
  eval_map_comp (eZ : 𝓞 ℚ →+* ℤ) Q₀ x

theorem eZ_symm_apply (k : ℤ) : eZ.symm k = (k : 𝓞 ℚ) := eq_intCast eZ.symm k

theorem formF_up (Q : QuadForm ℤ n) : formF (up Q) = Q.map (Int.castRingHom ℚ) := by
  rw [formF, up, Siegel.toOQ, QuadForm.map_map]
  congr 1

/-- **Positive definiteness, two ways:** $Q$ is positive definite over $\mathbb Z$ iff $Q \otimes \mathbb Q$ is totally positive definite. -/
theorem isTotallyPosDef_up_iff (Q : QuadForm ℤ n) : IsTotallyPosDef (formF (up Q)) ↔ IntQF.PosDef Q := by
  refine ⟨fun h x hx => ?_, Siegel.isTotallyPosDef_toOQ⟩
  have hx' : (fun i => (x i : ℚ)) ≠ 0 := by
    intro h0; apply hx; funext i; simpa using congrFun h0 i
  have h1 := h _ hx' (Rat.castHom ℂ).toRatAlgHom
  rw [Siegel.formF_toOQ_eval, Siegel.evalIn_intCast] at h1
  have h2 : (0 : ℂ) < (((Q.eval x : ℤ) : ℝ) : ℂ) := by simpa using h1
  exact_mod_cast Complex.zero_lt_real.mp h2

theorem posDef_down {Q₀ : QuadForm (𝓞 ℚ) n} (h : IsTotallyPosDef (formF Q₀)) : IntQF.PosDef (down Q₀) := by
  rw [← isTotallyPosDef_up_iff, up_down]; exact h

/-- A totally positive $m \in \mathcal O_{\mathbb Q}$ is a positive integer. -/
theorem exists_int_of_pos {m : 𝓞 ℚ} (hm : ∀ v : InfinitePlace ℚ, 0 < realEmb ℚ v (algebraMap (𝓞 ℚ) ℚ m)) :
    ∃ k : ℤ, 1 ≤ k ∧ (k : 𝓞 ℚ) = m := by
  refine ⟨eZ m, ?_, ?_⟩
  · have h1 := hm Rat.infinitePlace
    have e : realEmb ℚ Rat.infinitePlace (algebraMap (𝓞 ℚ) ℚ m) = ((eZ m : ℤ) : ℝ) := by
      have hm' : algebraMap (𝓞 ℚ) ℚ m = ((eZ m : ℤ) : ℚ) := by
        conv_lhs => rw [← eZ.symm_apply_apply m, eZ_symm_apply]
        simp
      rw [hm', map_intCast]
    rw [e] at h1
    exact_mod_cast h1
  · rw [← eZ_symm_apply, eZ.symm_apply_apply]

/-! ### The local side: `siegelProduct` is Hanke's `aE` -/

/-- **The Euler products agree:** $\prod_{\mathfrak p}\beta_{\mathfrak p}(Q\otimes\mathcal O_{\mathbb Q}, m) = \prod_p\beta_p(Q, m)$, prime by prime
(`NF.localDensity_rat`: $\mathcal O_{\mathbb Q}/\mathfrak p^k \cong \mathbb Z/p^k$) and reindexed by $\mathfrak p \mapsto p$ (`primesEquiv`). -/
theorem eulerProductNF_up (Q : QuadForm ℤ n) (m : ℤ) :
    Siegel.eulerProductNF (up Q) (m : 𝓞 ℚ) = Siegel.eulerProduct Q m := by
  unfold Siegel.eulerProductNF Siegel.eulerProduct
  simp only [Siegel.eulerFactorNF, Siegel.eulerFactor, LocalDensity.NF.localDensity_rat]
  exact (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).tprod_eq
    (fun p : Nat.Primes => LocalDensity.localDensity Q p m)

theorem realEmb_intCast_pos {m : ℤ} (hm : 1 ≤ m) :
    ∀ v : InfinitePlace ℚ, 0 < realEmb ℚ v (algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)) := fun v => by
  rw [map_intCast, map_intCast]; exact_mod_cast hm

/-- **The Siegel product over $\mathbb Q$ is Hanke's (5.3)** (`Siegel.aE`): for $Q$ positive definite over $\mathbb Z$ in $n \ge 1$ variables and an
integer $m \ge 1$,
$$S(\mathbb Z^n, m) = |d_{\mathbb Q}|^{-(n-1)/2}\prod_\sigma\beta_\sigma(m)\prod_\mathfrak p\beta_\mathfrak p(m) = \beta_\infty(m)\prod_p\beta_p(m) = a_E(m).$$
Factor by factor: $|d_{\mathbb Q}| = 1$ (`discrFactor_rat`), the one real place (`siegelProduct_eq_discr_mul_aENF`, `betaInfNF_rat`), and the
Euler products (`eulerProductNF_up`). -/
@[kb "hanke2004" "(5.3), p. 368 (F = ℚ: siegelProduct = a_E(m))"]
theorem siegelProduct_up (Q : QuadForm ℤ n) (hQ : IntQF.PosDef Q) (hn : 1 ≤ n) {m : ℤ} (hm : 1 ≤ m) :
    siegelProduct (up Q) (m : 𝓞 ℚ) = Siegel.aE Q m := by
  have hpd := (isTotallyPosDef_up_iff Q).mpr hQ
  rw [siegelProduct_eq_discr_mul_aENF (isTotPosGram_Q₀ hpd) hn (realEmb_intCast_pos hm), discrFactor_rat,
    one_mul, Siegel.aENF, eulerProductNF_up]
  exact Siegel.aEWithNF_rat Q m _

/-! ### Free lattices: automorphisms and representation numbers are those of the Gram form (any $F$) -/

section FreeLat

variable {F : Type} [Field F] [NumberField F] (QF : QuadForm F n)

theorem gramZ_eval_mulVec (γ : GL (Fin n) F) (h : IsIntegral QF (latOf γ)) (P₀ : GL (Fin n) (𝓞 F))
    (hP : ∀ x, (gramZ QF γ h).eval (P₀.val *ᵥ x) = (gramZ QF γ h).eval x) (y : Fin n → F) :
    QF.eval (γ.val *ᵥ ((GeneralLinearGroup.map (algebraMap (𝓞 F) F) P₀).val *ᵥ y)) = QF.eval (γ.val *ᵥ y) := by
  let A : QuadForm F n :=
    gramFormF QF.toQuadraticForm (fun j => (γ * GeneralLinearGroup.map (algebraMap (𝓞 F) F) P₀).val *ᵥ Pi.single j 1)
  let B : QuadForm F n := gramFormF QF.toQuadraticForm (fun j => γ.val *ᵥ Pi.single j 1)
  have hA : ∀ z, A.eval z = QF.eval (γ.val *ᵥ ((GeneralLinearGroup.map (algebraMap (𝓞 F) F) P₀).val *ᵥ z)) := by
    intro z; rw [eval_gramFormF_col, Units.val_mul, mulVec_mulVec]
  have hB : ∀ z, B.eval z = QF.eval (γ.val *ᵥ z) := fun z => eval_gramFormF_col QF γ z
  rw [← hA, ← hB]
  refine eval_eq_of_eval_int (fun x => ?_) y
  rw [hA, hB]
  have e : (GeneralLinearGroup.map (algebraMap (𝓞 F) F) P₀).val *ᵥ intCoe x = intCoe (P₀.val *ᵥ x) :=
    map_mulVec_intCoe _ x
  rw [e, ← algebraMap_eval_gramZ QF γ h, ← algebraMap_eval_gramZ QF γ h, hP x]

/-- **$|O(\gamma\mathcal O_F^n)| = |\mathrm{Aut}(Q_\gamma)|$**: $\rho \mapsto \gamma^{-1}\rho\gamma$ is a bijection from the automorphisms of the
free lattice $\gamma\mathcal O_F^n$ in $(F^n, Q)$ onto the $\mathrm{GL}_n(\mathcal O_F)$-automorphisms of its Gram form (`gramZ`). -/
theorem card_autLat_latOf (γ : GL (Fin n) F) (h : IsIntegral QF (latOf γ)) :
    Nat.card (autLat QF (latOf γ)) = Nat.card (Siegel.aut (gramZ QF γ h)) := by
  classical
  set G := gramZ QF γ h
  set ι := GeneralLinearGroup.map (R := 𝓞 F) (S := F) (n := Fin n) (algebraMap (𝓞 F) F)
  let Φ : Siegel.aut G → autLat QF (latOf γ) := fun P =>
    ⟨⟨γ * ι P.1 * γ⁻¹, mem_orthGroup_of_eval QF fun z => by
        rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec,
          gramZ_eval_mulVec QF γ h P.1 P.2, mulVec_inv_mulVec]⟩, by
      change glImage (γ * ι P.1 * γ⁻¹) (latOf γ) = latOf γ
      rw [latOf, ← glImage_mul, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, glImage_mul,
        glImage_map_intVec]⟩
  have hι : Function.Injective ι := by
    intro a b hab
    refine Units.ext (Matrix.ext fun i j => IsFractionRing.injective (𝓞 F) F ?_)
    have := congrArg (fun g : GL (Fin n) F => g.val i j) hab
    simpa [ι] using this
  have hinj : Function.Injective Φ := by
    intro P P' hPP
    have h1 : γ * ι P.1 * γ⁻¹ = γ * ι P'.1 * γ⁻¹ :=
      congrArg (fun x : autLat QF (latOf γ) => ((x.1 : orthGroup QF F) : GL (Fin n) F)) hPP
    have h2 : ι P.1 = ι P'.1 := by simpa using h1
    exact Subtype.ext (hι h2)
  have hsurj : Function.Surjective Φ := by
    rintro ⟨⟨ρ, hρ⟩, hρL⟩
    have hP : glImage (γ⁻¹ * ρ * γ) intVec = intVec := by
      rw [glImage_mul, glImage_mul]
      change glImage γ⁻¹ (glImage ρ (latOf γ)) = intVec
      rw [show glImage ρ (latOf γ) = latOf γ from hρL, latOf, ← glImage_mul, inv_mul_cancel, glImage_one]
    obtain ⟨P₀, hP₀⟩ := exists_gl_int_of_glImage_eq hP
    have hmem : P₀ ∈ Siegel.aut G := by
      intro x
      refine IsFractionRing.injective (𝓞 F) F ?_
      rw [algebraMap_eval_gramZ, algebraMap_eval_gramZ, ← map_mulVec_intCoe]
      have e : P₀.val.map (algebraMap (𝓞 F) F) = (γ⁻¹ * ρ * γ).val := congrArg Units.val hP₀
      rw [e, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_inv_mulVec]
      exact evalIn_mulVec_of_mem QF hρ _
    refine ⟨⟨P₀, hmem⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    change γ * ι P₀ * γ⁻¹ = ρ
    rw [show ι P₀ = γ⁻¹ * ρ * γ from hP₀]
    group
  exact (Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)).symm

/-- **$r_{\gamma\mathcal O_F^n}(m) = r_{Q_\gamma}(m)$**: $x \mapsto \gamma x$ is a bijection from the representations of $m$ by the Gram form
onto the vectors of norm $m$ in the free lattice. -/
theorem repCount_latOf (γ : GL (Fin n) F) (h : IsIntegral QF (latOf γ)) (m : 𝓞 F) :
    repCount QF ⟨latOf γ, latOf_isLattice γ⟩ (algebraMap (𝓞 F) F m) =
      Nat.card {x : Fin n → 𝓞 F // (gramZ QF γ h).eval x = m} := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨γ.val *ᵥ intCoe x.1, mulVec_mem_glImage (intCoe_mem _), by
      rw [← algebraMap_eval_gramZ QF γ h, x.2]⟩) ⟨fun x y hxy => ?_, fun v => ?_⟩)
  · have h1 : γ.val *ᵥ intCoe x.1 = γ.val *ᵥ intCoe y.1 := congrArg Subtype.val hxy
    have h2 : intCoe x.1 = intCoe y.1 := by
      have := congrArg (fun w => (γ⁻¹).val *ᵥ w) h1
      simpa [mulVec_mulVec, ← Units.val_mul] using this
    exact Subtype.ext (funext fun i => IsFractionRing.injective (𝓞 F) F (congrFun h2 i))
  · obtain ⟨w, hw, hwv⟩ := mem_glImage.mp v.2.1
    obtain ⟨x, rfl⟩ := mem_intVec_iff_exists.mp hw
    refine ⟨⟨x, IsFractionRing.injective (𝓞 F) F ?_⟩, Subtype.ext hwv⟩
    rw [algebraMap_eval_gramZ, hwv, v.2.2]

end FreeLat

/-! ### Change of coefficient ring: $\mathcal O_{\mathbb Q} \cong \mathbb Z$ -/

theorem mem_aut_map {A B : Type*} [CommRing A] [CommRing B] (φ : A ≃+* B) {Q : QuadForm A n}
    {g : GL (Fin n) A} (hg : g ∈ Siegel.aut Q) :
    GeneralLinearGroup.map (φ : A →+* B) g ∈ Siegel.aut (Q.map (φ : A →+* B)) := by
  intro y
  have hy : y = fun i => φ ((fun i => φ.symm (y i)) i) := by funext i; simp
  rw [hy]
  have e : (GeneralLinearGroup.map (φ : A →+* B) g).val *ᵥ (fun i => φ ((fun i => φ.symm (y i)) i)) =
      fun i => φ ((g.val *ᵥ fun i => φ.symm (y i)) i) := by
    funext i
    exact (RingHom.map_mulVec (φ : A →+* B) g.val _ i).symm
  rw [e]
  exact (eval_map_comp (φ : A →+* B) Q _).trans ((congrArg φ (hg _)).trans (eval_map_comp (φ : A →+* B) Q _).symm)

theorem card_aut_map_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (φ : A ≃+* B) (Q : QuadForm A n) :
    Nat.card (Siegel.aut (Q.map (φ : A →+* B))) = Nat.card (Siegel.aut Q) := by
  have hQ : (Q.map (φ : A →+* B)).map (φ.symm : B →+* A) = Q := by
    rw [QuadForm.map_map]; ext i j; simp [QuadForm.map]
  symm
  refine Nat.card_congr
    { toFun := fun g => ⟨GeneralLinearGroup.map (φ : A →+* B) g.1, mem_aut_map φ g.2⟩
      invFun := fun g => ⟨GeneralLinearGroup.map (φ.symm : B →+* A) g.1, by
        have := mem_aut_map φ.symm g.2; rwa [hQ] at this⟩
      left_inv := fun g => by
        apply Subtype.ext; apply Units.ext; ext i j; simp
      right_inv := fun g => by
        apply Subtype.ext; apply Units.ext; ext i j; simp }

theorem repNum_down (Q₀ : QuadForm (𝓞 ℚ) n) (m : ℤ) :
    Siegel.repNum (down Q₀) m = Nat.card {x : Fin n → 𝓞 ℚ // Q₀.eval x = (m : 𝓞 ℚ)} := by
  refine Nat.card_congr ((Equiv.piCongrRight fun _ => eZ.toEquiv).subtypeEquiv fun x => ?_).symm
  change Q₀.eval x = (m : 𝓞 ℚ) ↔ (down Q₀).eval (fun i => eZ (x i)) = m
  rw [down_map_eval, ← eZ_symm_apply]
  exact ⟨fun h => by rw [h, eZ.apply_symm_apply], fun h => by rw [← h, eZ.symm_apply_apply]⟩

theorem intEquiv_down_iff {Q₁ Q₂ : QuadForm (𝓞 ℚ) n} :
    Siegel.IntEquiv (down Q₁) (down Q₂) ↔ Siegel.IsometricGL Q₁ Q₂ :=
  isometricGL_map_ringEquiv eZ Q₁ Q₂

/-! ### Siegel's genus over $\mathbb Z$ is the lattice genus of $\mathcal O_{\mathbb Q}^n$ -/

/-- Equivalence of integral forms over a ring $A$ survives any ring map $A \to B$ (the identity of forms is coefficientwise). -/
theorem isometricGL_map_hom {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {Q Q' : QuadForm A n}
    (h : Siegel.IsometricGL Q Q') : Siegel.IsometricGL (Q.map f) (Q'.map f) := by
  obtain ⟨g, hg⟩ := h
  have hc : Q.compMat g.val = Q' := QuadForm.ext_eval fun x => by rw [QuadForm.eval_compMat, hg]
  refine ⟨Units.map (RingHom.mapMatrix (m := Fin n) f).toMonoidHom g, fun x => ?_⟩
  change (Q.map f).eval (g.val.map f *ᵥ x) = _
  rw [← QuadForm.eval_compMat, QuadForm.map_compMat, hc]

theorem isometricIn_rat_of_isometricGL {K : Type} [Field K] [CharZero K] {Q Q' : QuadForm ℤ n}
    (h : Siegel.IsometricGL (Q.map (Int.castRingHom K)) (Q'.map (Int.castRingHom K))) :
    (Q.map (Int.castRingHom ℚ)).IsometricIn K (Q'.map (Int.castRingHom ℚ)) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g.val, (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit, fun x => ?_⟩
  rw [evalIn_eq_eval_map, evalIn_eq_eval_map, QuadForm.map_map, QuadForm.map_map,
    RingHom.ext_int ((algebraMap ℚ K).comp (Int.castRingHom ℚ)) (Int.castRingHom K)]
  exact hg x

/-- **Forms in one genus over $\mathbb Z$ are equivalent over $\mathbb Q$** (Hasse–Minkowski, `isometric_of_everywhere`). -/
theorem isometricIn_rat_of_sameGenus {Q Q' : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (hg : Siegel.SameGenus Q Q') :
    (Q.map (Int.castRingHom ℚ)).IsometricIn ℚ (Q'.map (Int.castRingHom ℚ)) := by
  have hnd : ∀ R : QuadForm ℤ n, IntQF.PosDef R → (R.map (Int.castRingHom ℚ)).Nondegenerate := fun R hR => by
    have := ((isTotallyPosDef_up_iff R).mpr hR).nondegenerate
    rwa [formF_up] at this
  refine isometric_of_everywhere _ _ (hnd Q hQ) (hnd Q' (Siegel.SameGenus.posDef hQ hg)) fun v => ?_
  cases v with
  | infinite => exact isometricIn_rat_of_isometricGL hg.2
  | finite p =>
    have : Fact p.1.Prime := ⟨p.2⟩
    have h1 := isometricGL_map_hom (PadicInt.Coe.ringHom (p := p.1)) (hg.1 p.1)
    rw [QuadForm.map_map, QuadForm.map_map,
      RingHom.ext_int ((PadicInt.Coe.ringHom (p := p.1)).comp (Int.castRingHom ℤ_[p.1])) (Int.castRingHom ℚ_[p.1])]
      at h1
    exact isometricIn_rat_of_isometricGL h1

/-! ### The class bijection over $\mathbb Q$ -/

section Classes

variable (Q : QuadForm ℤ n)

theorem evalIn_map_rat (R : QuadForm ℤ n) (y : Fin n → ℚ) :
    (R.map (Int.castRingHom ℚ)).evalIn ℚ y = R.evalIn ℚ y := by
  simp [QuadForm.evalIn, QuadForm.map]

theorem evalIn_intCoe_rat (R : QuadForm ℤ n) (x : Fin n → 𝓞 ℚ) :
    R.evalIn ℚ (intCoe x) = algebraMap (𝓞 ℚ) ℚ ((up R).eval x) :=
  (Siegel.formF_toOQ_eval R _).symm.trans (eval_map_comp _ (up R) x)

open Classical in
/-- **The integral form of a lattice** $M$ in $(\mathbb Q^n, Q)$: the Gram form over $\mathbb Z$ of a basis $\gamma$ of $M$ (`gramZ`, then
$\mathcal O_{\mathbb Q} \to \mathbb Z$); junk value $Q$ if $M$ is not free and integral (never the case in the genus of $\mathbb Z^n$). -/
noncomputable def zForm (M : Lat ℚ n) : QuadForm ℤ n :=
  if h : ∃ γ : GL (Fin n) ℚ, M.1 = latOf γ ∧ IsIntegral (formF (up Q)) (latOf γ) then
    down (gramZ (formF (up Q)) h.choose h.choose_spec.2) else Q

theorem intEquiv_down_gramZ_iff (γ δ : GL (Fin n) ℚ) (hγ : IsIntegral (formF (up Q)) (latOf γ))
    (hδ : IsIntegral (formF (up Q)) (latOf δ)) :
    Siegel.IntEquiv (down (gramZ (formF (up Q)) γ hγ)) (down (gramZ (formF (up Q)) δ hδ)) ↔
      IsIsometric (formF (up Q)) (latOf δ) (latOf γ) := by
  rw [intEquiv_down_iff, isIsometric_latOf_iff]

theorem zForm_intEquiv (M : Lat ℚ n) (γ : GL (Fin n) ℚ) (hM : M.1 = latOf γ)
    (h : IsIntegral (formF (up Q)) (latOf γ)) :
    Siegel.IntEquiv (zForm Q M) (down (gramZ (formF (up Q)) γ h)) := by
  have hex : ∃ γ : GL (Fin n) ℚ, M.1 = latOf γ ∧ IsIntegral (formF (up Q)) (latOf γ) := ⟨γ, hM, h⟩
  rw [zForm, dite_eq_left_of_eq_true (eq_true hex)]
  refine (intEquiv_down_gramZ_iff Q _ _ _ _).mpr ?_
  rw [← hM, ← hex.choose_spec.1]
  exact IsIsometric.refl _ _

theorem exists_free_of_sameGenus (M : Lat ℚ n) (hM : Lattices.SameGenus (formF (up Q)) intVec M.1) :
    ∃ γ : GL (Fin n) ℚ, M.1 = latOf γ ∧ IsIntegral (formF (up Q)) (latOf γ) := by
  obtain ⟨γ, hγ⟩ := exists_latOf_of_isPrincipalIdealRing M
  exact ⟨γ, hγ, hγ ▸ Lattices.SameGenus.isIntegral _ (isIntegral_stdLat (up Q)) hM⟩

/-- The Gram form of a free lattice in the genus of $\mathbb Z^n$ is in Siegel's genus of $Q$ (`formSameGenus_gramZ`,
`formSameGenus_rat_iff`). -/
theorem sameGenus_down_gramZ (γ : GL (Fin n) ℚ) (hs : Lattices.SameGenus (formF (up Q)) intVec (latOf γ))
    (h : IsIntegral (formF (up Q)) (latOf γ)) : Siegel.SameGenus Q (down (gramZ (formF (up Q)) γ h)) := by
  rw [← formSameGenus_rat_iff]
  have e1 : Q.map Lattices.toOQ = up Q := by rw [toOQ_eq_cast]
  have e2 : (down (gramZ (formF (up Q)) γ h)).map Lattices.toOQ = gramZ (formF (up Q)) γ h := by
    rw [toOQ_eq_cast]; exact up_down _
  rw [e1, e2]
  exact formSameGenus_gramZ (up Q) hs h

/-- **Every form in Siegel's genus of $Q$ is the Gram form of a lattice in the genus of $\mathbb Z^n$** in $(\mathbb Q^n, Q)$
(Hasse–Minkowski gives $Q' = Q\circ\gamma$ over $\mathbb Q$; then $\gamma\mathbb Z^n$). -/
theorem exists_latOf_of_sameGenus (hQ : IntQF.PosDef Q) {Q' : QuadForm ℤ n} (hg : Siegel.SameGenus Q Q') :
    ∃ (γ : GL (Fin n) ℚ) (h : IsIntegral (formF (up Q)) (latOf γ)),
      Lattices.SameGenus (formF (up Q)) intVec (latOf γ) ∧ down (gramZ (formF (up Q)) γ h) = Q' := by
  obtain ⟨P, hP, hPe⟩ := isometricIn_rat_of_sameGenus hQ hg
  set γ : GL (Fin n) ℚ := ((Matrix.isUnit_iff_isUnit_det P).mpr hP).unit
  have hγP : γ.val = P := rfl
  have hval : ∀ x : Fin n → 𝓞 ℚ,
      (formF (up Q)).eval (γ.val *ᵥ intCoe x) = algebraMap (𝓞 ℚ) ℚ ((up Q').eval x) := by
    intro x
    have := hPe (intCoe x)
    rw [evalIn_map_rat, evalIn_map_rat] at this
    rw [Siegel.formF_toOQ_eval, hγP, this, evalIn_intCoe_rat]
  have hint : IsIntegral (formF (up Q)) (latOf γ) := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := mem_glImage.mp hy
    obtain ⟨x, rfl⟩ := mem_intVec_iff_exists.mp hw
    exact ⟨(up Q').eval x, (hval x).symm⟩
  have hG : gramZ (formF (up Q)) γ hint = up Q' :=
    QuadForm.ext_eval fun x => IsFractionRing.injective (𝓞 ℚ) ℚ (by rw [algebraMap_eval_gramZ, hval])
  refine ⟨γ, hint, ?_, by rw [hG, down_up]⟩
  have h1 := (sameGenus_latOf_iff (formF (up Q)) 1 γ (isIntegral_latOf_one (up Q)) hint).mpr (by
    rw [gramZ_one, hG]
    have e : ∀ R : QuadForm ℤ n, R.map Lattices.toOQ = up R := fun R => by rw [toOQ_eq_cast]
    rw [← e, ← e]
    exact (formSameGenus_rat_iff Q Q').mpr hg)
  rwa [latOf_one] at h1

theorem autCard_eq_card (c : LatClass (formF (up Q))) :
    LatClass.autCard (formF (up Q)) c = Nat.card (autLat (formF (up Q)) c.out.1) := by
  conv_lhs => rw [← Quotient.out_eq c]
  rfl

theorem repCountClass_eq (c : LatClass (formF (up Q))) (m : ℚ) :
    LatClass.repCount (formF (up Q)) c m = repCount (formF (up Q)) c.out m := by
  conv_lhs => rw [← Quotient.out_eq c]
  rfl

/-- **The class map** $\mathrm{cls}(M) \mapsto [\text{Gram form of } M]$ is a bijection from the classes of lattices in the genus of $\mathbb Z^n$ in
$(\mathbb Q^n, Q)$ onto Siegel's $\mathrm{GL}_n(\mathbb Z)$-classes in the genus of $Q$. -/
@[kb "omeara1963" "§§82, 102 (classes of lattices = classes of forms, F = ℚ) [unverified]"]
theorem bijOn_latClass_rat (hQ : IntQF.PosDef Q) :
    Set.BijOn (fun c : LatClass (formF (up Q)) => Siegel.classOf (zForm Q c.out))
      (genusClasses (formF (up Q)) (stdLat ℚ n)) (Siegel.genusClasses Q) := by
  have hfree : ∀ c ∈ genusClasses (formF (up Q)) (stdLat ℚ n), ∃ γ : GL (Fin n) ℚ,
      c.out.1 = latOf γ ∧ IsIntegral (formF (up Q)) (latOf γ) ∧
        Lattices.SameGenus (formF (up Q)) intVec (latOf γ) := fun c hc => by
    have hs := sameGenus_out hc
    obtain ⟨γ, hγ, hi⟩ := exists_free_of_sameGenus Q c.out hs
    exact ⟨γ, hγ, hi, hγ ▸ hs⟩
  refine ⟨fun c hc => ?_, fun c hc c' hc' hcc => ?_, fun d hd => ?_⟩
  · obtain ⟨γ, hγ, hi, hs⟩ := hfree c hc
    refine Siegel.classOf_mem_genusClasses_iff.mpr ?_
    exact (sameGenus_down_gramZ Q γ hs hi).trans (Siegel.IntEquiv.sameGenus (zForm_intEquiv Q _ γ hγ hi).symm)
  · obtain ⟨γ, hγ, hi, -⟩ := hfree c hc
    obtain ⟨γ', hγ', hi', -⟩ := hfree c' hc'
    have h1 : Siegel.IntEquiv (zForm Q c.out) (zForm Q c'.out) := Siegel.classOf_eq_classOf_iff.mp hcc
    have h2 : Siegel.IntEquiv (down (gramZ (formF (up Q)) γ hi)) (down (gramZ (formF (up Q)) γ' hi')) :=
      Siegel.IsometricGL.trans (Siegel.IsometricGL.symm (zForm_intEquiv Q _ γ hγ hi))
        (Siegel.IsometricGL.trans h1 (zForm_intEquiv Q _ γ' hγ' hi'))
    have h3 := (intEquiv_down_gramZ_iff Q γ γ' hi hi').mp h2
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    refine Quotient.sound ?_
    change IsIsometric (formF (up Q)) c.out.1 c'.out.1
    rw [hγ, hγ']
    exact IsIsometric.symm _ h3
  · obtain ⟨Q', rfl, hg⟩ := hd
    obtain ⟨γ, hi, hs, hQ'⟩ := exists_latOf_of_sameGenus Q hQ hg
    set M : Lat ℚ n := ⟨latOf γ, latOf_isLattice γ⟩
    have hc : (Quotient.mk _ M : LatClass (formF (up Q))) ∈ genusClasses (formF (up Q)) (stdLat ℚ n) :=
      ⟨M, rfl, hs⟩
    refine ⟨_, hc, ?_⟩
    obtain ⟨γ', hγ', hi', -⟩ := hfree _ hc
    have hiso : IsIsometric (formF (up Q)) (latOf γ') (latOf γ) := by
      rw [← hγ']
      exact Quotient.exact (Quotient.out_eq (Quotient.mk (latSetoid (formF (up Q))) M))
    refine Siegel.classOf_eq_classOf_iff.mpr ?_
    refine Siegel.IsometricGL.trans (zForm_intEquiv Q _ γ' hγ' hi') ?_
    rw [← hQ']
    exact (intEquiv_down_gramZ_iff Q γ' γ hi' hi).mpr (IsIsometric.symm _ hiso)

end Classes

/-! ### Mass, weighted representation numbers and Siegel's formula: the two dictionaries agree -/

section Dictionary

variable (Q : QuadForm ℤ n)

theorem autCard_eq_zForm {c : LatClass (formF (up Q))} (hc : c ∈ genusClasses (formF (up Q)) (stdLat ℚ n)) :
    LatClass.autCard (formF (up Q)) c = (Siegel.classOf (zForm Q c.out)).autCard := by
  have hs := sameGenus_out hc
  obtain ⟨γ, hγ, hi⟩ := exists_free_of_sameGenus Q c.out hs
  rw [autCard_eq_card, Siegel.QClass.autCard_classOf, hγ, card_autLat_latOf _ γ hi,
    Siegel.card_aut_eq_of_intEquiv (zForm_intEquiv Q _ γ hγ hi)]
  exact (card_aut_map_ringEquiv eZ _).symm

theorem repCount_eq_zForm {c : LatClass (formF (up Q))} (hc : c ∈ genusClasses (formF (up Q)) (stdLat ℚ n))
    (m : ℤ) : LatClass.repCount (formF (up Q)) c (m : ℚ) = (Siegel.classOf (zForm Q c.out)).repNum m := by
  have hs := sameGenus_out hc
  obtain ⟨γ, hγ, hi⟩ := exists_free_of_sameGenus Q c.out hs
  have hc' : c.out = ⟨latOf γ, latOf_isLattice γ⟩ := Subtype.ext hγ
  rw [repCountClass_eq, Siegel.QClass.repNum_classOf, hc', ← map_intCast (algebraMap (𝓞 ℚ) ℚ) m,
    repCount_latOf _ γ hi, Siegel.repNum_eq_of_intEquiv (zForm_intEquiv Q _ γ rfl hi), repNum_down]

/-- **$\mathrm{Mass}(Q) = \mathrm{Mass}(\mathbb Z^n)$**: Hanke's mass over $\mathrm{GL}_n(\mathbb Z)$-classes of forms in the genus of $Q$ is the mass of
the genus of $\mathbb Z^n$ in $(\mathbb Q^n, Q)$. -/
@[kb "hanke2004" "(4.5), p. 366 (Mass(Q) as a lattice mass over 𝓞_ℚ)"]
theorem mass_rat (hQ : IntQF.PosDef Q) :
    Siegel.mass Q = Lattices.mass (formF (up Q)) (stdLat ℚ n) := by
  symm
  refine finsum_mem_eq_of_bijOn _ (bijOn_latClass_rat Q hQ) fun c hc => ?_
  rw [autCard_eq_zForm Q hc]

/-- **$\sum_{[Q']} r_{Q'}(m)/|\mathrm{Aut}(Q')| = \mathrm{repMass}(\mathbb Z^n, m)$** (Hanke's `genusRepSum` is `repMass` at $F = \mathbb Q$). -/
@[kb "hanke2004" "(4.5), p. 366 (numerator as a lattice sum over 𝓞_ℚ)"]
theorem repMass_rat (hQ : IntQF.PosDef Q) (m : ℤ) :
    Siegel.genusRepSum Q m = repMass (formF (up Q)) (stdLat ℚ n) (m : ℚ) := by
  symm
  refine finsum_mem_eq_of_bijOn _ (bijOn_latClass_rat Q hQ) fun c hc => ?_
  rw [autCard_eq_zForm Q hc, repCount_eq_zForm Q hc]

/-- **Hanke's Siegel formula is the `SiegelFormulaAt` one, number by number** ($F = \mathbb Q$): for $Q$ positive definite over $\mathbb Z$ in $n \ge 1$ variables,
`Siegel.SiegelFormula Q` ($r_{\mathrm{Gen}(Q)}(m) = a_E(m)$ for all $m \ge 1$) holds iff `SiegelFormulaAt` holds for $Q \otimes \mathcal O_{\mathbb Q}$ at
every integer $m \ge 1$ (`mass_rat`, `repMass_rat`, `siegelProduct_up`). -/
@[kb "siegel1935" "Hauptsatz over ℚ: Hanke's (5.3) form ⟺ SiegelFormulaAt [unverified]"]
theorem siegelFormula_iff_siegelFormulaAt (hQ : IntQF.PosDef Q) (hn : 1 ≤ n) :
    Siegel.SiegelFormula Q ↔ ∀ m : ℤ, 1 ≤ m → SiegelFormulaAt (up Q) (m : 𝓞 ℚ) := by
  have hpd := (isTotallyPosDef_up_iff Q).mpr hQ
  have hpos : 0 < Lattices.mass (formF (up Q)) (stdLat ℚ n) := mass_pos hpd _ (isIntegral_stdLat (up Q))
  have key : ∀ m : ℤ, 1 ≤ m → (Siegel.genusRepAvg Q m = Siegel.aE Q m ↔ SiegelFormulaAt (up Q) (m : 𝓞 ℚ)) := by
    intro m hm
    rw [Siegel.genusRepAvg, mass_rat Q hQ, repMass_rat Q hQ, div_eq_iff hpos.ne', ← siegelProduct_up Q hQ hn hm]
    constructor
    · intro h; exact ⟨by rw [map_intCast, h, mul_comm]⟩
    · intro h; have := h.repMass_eq; rw [map_intCast] at this; rw [mul_comm]; exact this
  exact ⟨fun h m hm => (key m hm).mp (h.genusRepAvg_eq m hm), fun h => ⟨fun m hm => (key m hm).mpr (h m hm)⟩⟩

/-- **The Siegel formula over $\mathbb Q$ from Hanke's**: for $Q_0$ totally positive definite over $\mathcal O_{\mathbb Q}$ in $n \ge 1$ variables with
`Siegel.SiegelFormula` for $Q_0$ read over $\mathbb Z$, `SiegelFormulaAt Q₀ m` holds for every totally positive $m$. -/
theorem siegelFormulaAt_of_siegelFormula {Q₀ : QuadForm (𝓞 ℚ) n} (hpd : IsTotallyPosDef (formF Q₀)) (hn : 1 ≤ n)
    (hS : Siegel.SiegelFormula (down Q₀)) {m : 𝓞 ℚ}
    (hm : ∀ v : InfinitePlace ℚ, 0 < realEmb ℚ v (algebraMap (𝓞 ℚ) ℚ m)) : SiegelFormulaAt Q₀ m := by
  obtain ⟨k, hk, rfl⟩ := exists_int_of_pos hm
  have h := (siegelFormula_iff_siegelFormulaAt (down Q₀) (posDef_down hpd) hn).mp hS k hk
  rwa [up_down] at h

/-- **The input `SiegelFormulaAt` in rank 4 over $\mathbb Q$ is a theorem** (`siegelFormula_quaternary` through the bridge): for every
totally positive definite quaternary $Q_0$ over $\mathcal O_{\mathbb Q}$ and every totally positive $m$,
$\mathrm{repMass}(\mathbb Z^4, m) = \mathrm{Mass}(\mathbb Z^4)\cdot S(\mathbb Z^4, m)$. This is the case $F = \mathbb Q$ that
`HilbertModular.siegelFormulaAt_of_pid_four` ($[F:\mathbb Q] \ge 2$) leaves out. -/
@[kb "siegel1935" "Hauptsatz, n = 4, over ℚ in the SiegelFormulaAt form [unverified]"]
theorem siegelFormulaAt_rat_four {Q₀ : QuadForm (𝓞 ℚ) 4} (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 ℚ}
    (hm : ∀ v : InfinitePlace ℚ, 0 < realEmb ℚ v (algebraMap (𝓞 ℚ) ℚ m)) : SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_of_siegelFormula hpd (by norm_num)
    (Siegel.GenusEis.siegelFormula_quaternary (posDef_down hpd)) hm

end Dictionary

/-! ### Consequences over $\mathbb Q$: $\tau(SO_3) = 2 \iff \tau(SO_4) = 2$, and Siegel's formula in every rank -/

section Consequences

open LatChange

/-- **$\tau(SO_4) = 2$ from $\tau(SO_3) = 2$ over $\mathbb Q$ for split lattices** $\langle m_0\rangle\perp Q_0'$ (the step with rank-4 Siegel
from `siegelFormulaAt_rat_four`). -/
@[kb "weil1982" "Thm. 3.7.1 (m = 4), p. 65, over ℚ via siegelFormulaAt_rat_four"]
theorem tamagawaNumberTwo_four_of_three_rat {m₀ : 𝓞 ℚ} (hm : ∀ v, 0 < realEmb ℚ v (algebraMap (𝓞 ℚ) ℚ m₀))
    (Q₀' : QuadForm (𝓞 ℚ) 3) (hpd : IsTotallyPosDef ((splitForm m₀ Q₀').map (algebraMap (𝓞 ℚ) ℚ)))
    (hLi : IsIntegral ((splitForm m₀ Q₀').map (algebraMap (𝓞 ℚ) ℚ)) (stdLat ℚ 4).1) (hτ : TamagawaNumberTwo Q₀') :
    TamagawaNumberTwo (splitForm m₀ Q₀') :=
  tamagawaNumberTwo_four_of_three_of_siegel hm Q₀' hpd hLi (siegelFormulaAt_rat_four hpd hm) hτ

/-- **$\tau(SO_4) = 2$ over $\mathbb Q$ from $\tau(SO_3) = 2$ over $\mathbb Q$**: `TernaryTamagawaTwo ℚ → QuaternaryTamagawaTwo ℚ` (split reduction
`tamagawaNumberTwo_of_split`, then `tamagawaNumberTwo_four_of_three_rat`). The $F = \mathbb Q$ case of `quaternaryTamagawaTwo_of_ternary`. -/
@[kb "weil1982" "Thm. 3.7.1 (m = 4 from m = 3), p. 65, over ℚ"]
theorem quaternaryTamagawaTwo_rat (hT : TernaryTamagawaTwo ℚ) : QuaternaryTamagawaTwo ℚ := by
  refine ⟨fun Q₀ hpd => tamagawaNumberTwo_of_split (n := 3) (by norm_num) (fun m₀ Q₀' hm hpds => ?_) Q₀ hpd⟩
  have hpd' : IsTotallyPosDef (formF Q₀') :=
    isTotallyPosDef_of_splitForm (m := algebraMap (𝓞 ℚ) ℚ m₀) (Q' := Q₀'.map (algebraMap (𝓞 ℚ) ℚ))
      (by rw [← map_splitForm]; exact hpds)
  exact tamagawaNumberTwo_four_of_three_rat hm Q₀' hpds (isIntegral_std _)
    (hT.tau_eq_two Q₀' (nondegenerate_of_map hpd'.nondegenerate) hpd' (isIntegral_std Q₀'))

/-- **$\tau(SO_3) = 2$ over $\mathbb Q$ from $\tau(SO_4) = 2$ over $\mathbb Q$** (`tamagawaNumberTwo_three_of_four_of_siegel` with $m_0 = 1$ and
rank-4 Siegel from `siegelFormulaAt_rat_four`). -/
@[kb "weil1982" "Thm. 3.7.1 (m = 3 from m = 4), p. 65, over ℚ"]
theorem ternaryTamagawaTwo_rat (h4 : QuaternaryTamagawaTwo ℚ) : TernaryTamagawaTwo ℚ := by
  refine ⟨fun Q₀' _ hpd' _ => ?_⟩
  have hpd : IsTotallyPosDef ((splitForm 1 Q₀').map (algebraMap (𝓞 ℚ) ℚ)) := by
    rw [map_splitForm_alg, map_one]; exact isTotallyPosDef_splitForm_one hpd'
  have h1 : ∀ v, 0 < realEmb ℚ v (algebraMap (𝓞 ℚ) ℚ 1) := fun v => by simp
  exact tamagawaNumberTwo_three_of_four_of_siegel h1 Q₀' hpd (isIntegral_std _) (siegelFormulaAt_rat_four hpd h1)
    (h4.tau_eq_two _ hpd)

/-- **The base cases of Weil's Theorem 3.7.1 are equivalent over $\mathbb Q$**: `TernaryTamagawaTwo ℚ ↔ QuaternaryTamagawaTwo ℚ`. (Over $F$ of
degree $\ge 2$ this is `LatChange.ternaryTamagawaTwo_iff_four_all`; over $\mathbb Q$ the rank-4 Siegel formula is `siegelFormula_quaternary`.) -/
@[kb "weil1982" "Thm. 3.7.1, p. 65 (m = 3 ⟺ m = 4), over ℚ"]
theorem ternaryTamagawaTwo_iff_quaternary_rat : TernaryTamagawaTwo ℚ ↔ QuaternaryTamagawaTwo ℚ :=
  ⟨quaternaryTamagawaTwo_rat, ternaryTamagawaTwo_rat⟩

/-- **$\tau(SO) = 2$ over $\mathbb Q$ in every rank $N \ge 3$**, given `TernaryTamagawaTwo ℚ` and the odd-rank local identities (the $F = \mathbb Q$
case of `tamagawaNumberTwo_all_ranks`, whose rank-4 step needs $[F:\mathbb Q] \ge 2$). -/
@[kb "weil1982" "Thm. 4.5.1, p. 109 and Thm. 3.7.1, p. 65 (τ(SO) = 2, m ≥ 3), over ℚ"]
theorem tamagawaNumberTwo_rat_all_ranks (hT : TernaryTamagawaTwo ℚ) (hloc : OddRankOrbitalLocalIdentities ℚ) {N : ℕ}
    (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 ℚ) N) (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ := by
  rcases Nat.lt_or_ge N 4 with h | h
  · obtain rfl : N = 3 := by omega
    exact hT.tau_eq_two Q₀ (nondegenerate_of_map hpd.nondegenerate) hpd (isIntegral_std Q₀)
  · exact tamagawaNumberTwo_of_four (quaternaryTamagawaTwo_rat hT) hloc h Q₀ hpd

/-- **Siegel's formula over $\mathbb Q$ in even rank $N \ge 4$, unconditionally** (the form): $N = 4$ by `siegelFormula_quaternary` through the bridge
(`siegelFormulaAt_rat_four`), $N \ge 6$ by Hilbert modular forms over $\mathbb Q$ (`HilbertModular.siegelFormulaAt_of_pid`). -/
@[kb "siegel1935" "Hauptsatz (numbers) over ℚ, every even rank ≥ 4 [unverified]"]
theorem siegelFormulaAt_rat_even {N : ℕ} (hN : 4 ≤ N) (he : Even N) (Q₀ : QuadForm (𝓞 ℚ) N)
    (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 ℚ} (hm : ∀ v, 0 < realEmb ℚ v (algebraMap (𝓞 ℚ) ℚ m)) :
    SiegelFormulaAt Q₀ m := by
  obtain ⟨k, hk⟩ := he
  by_cases h4 : N = 4
  · subst h4; exact siegelFormulaAt_rat_four hpd hm
  · exact HilbertModular.siegelFormulaAt_of_pid hpd (k := k) (by omega) (by omega) hm

/-- **Siegel's formula over $\mathbb Q$ in every rank $N \ge 4$** (the form, `SiegelFormulaAt`): even $N$ unconditional
(`siegelFormulaAt_rat_even`); odd $N \ge 5$ given `TernaryTamagawaTwo ℚ` and `OddRankOrbitalLocalIdentities ℚ` (`siegelFormulaAt_rat` with
`quaternaryTamagawaTwo_rat`). -/
@[kb "siegel1935" "Hauptsatz (numbers) over ℚ, every rank ≥ 4 [unverified]"]
theorem siegelFormulaAt_rat_all_ranks (hT : TernaryTamagawaTwo ℚ) (hloc : OddRankOrbitalLocalIdentities ℚ) {N : ℕ}
    (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 ℚ) N) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 ℚ}
    (hm : ∀ v, 0 < realEmb ℚ v (algebraMap (𝓞 ℚ) ℚ m)) : SiegelFormulaAt Q₀ m := by
  rcases Nat.even_or_odd N with he | ho
  · exact siegelFormulaAt_rat_even hN he Q₀ hpd hm
  · exact siegelFormulaAt_rat (quaternaryTamagawaTwo_rat hT) hloc (by obtain ⟨k, hk⟩ := ho; omega) Q₀ hpd hm

/-- **Hanke's Siegel formula over $\mathbb Z$ in every even rank $N \ge 4$, unconditionally**: `Siegel.SiegelFormula Q`
($r_{\mathrm{Gen}(Q)}(m) = a_E(m)$, Hanke (5.3)) for every positive definite integral $Q$ in $N$ variables. -/
@[kb "siegel1935" "Hauptsatz, every even rank ≥ 4, Hanke's (5.3) form over ℤ [unverified]"]
theorem siegelFormula_int_even {N : ℕ} (hN : 4 ≤ N) (he : Even N) (Q : QuadForm ℤ N) (hQ : IntQF.PosDef Q) :
    Siegel.SiegelFormula Q :=
  (siegelFormula_iff_siegelFormulaAt Q hQ (by omega)).mpr fun _ hm =>
    siegelFormulaAt_rat_even hN he _ ((isTotallyPosDef_up_iff Q).mpr hQ) (realEmb_intCast_pos hm)

/-- **Hanke's Siegel formula over $\mathbb Z$ in every rank $N \ge 4$**: `Siegel.SiegelFormula Q` for every positive definite integral $Q$ in
$N \ge 4$ variables; even $N$ unconditional, odd $N$ given `TernaryTamagawaTwo ℚ` and `OddRankOrbitalLocalIdentities ℚ`. -/
@[kb "siegel1935" "Hauptsatz, every rank ≥ 4, Hanke's (5.3) form over ℤ [unverified]"]
theorem siegelFormula_int_all_ranks (hT : TernaryTamagawaTwo ℚ) (hloc : OddRankOrbitalLocalIdentities ℚ) {N : ℕ}
    (hN : 4 ≤ N) (Q : QuadForm ℤ N) (hQ : IntQF.PosDef Q) : Siegel.SiegelFormula Q :=
  (siegelFormula_iff_siegelFormulaAt Q hQ (by omega)).mpr fun _ hm =>
    siegelFormulaAt_rat_all_ranks hT hloc hN _ ((isTotallyPosDef_up_iff Q).mpr hQ) (realEmb_intCast_pos hm)

end Consequences

end QuadFormsKB.Tamagawa.RatBridge
