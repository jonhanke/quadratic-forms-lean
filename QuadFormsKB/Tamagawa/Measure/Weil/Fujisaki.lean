import QuadFormsKB.Tamagawa.Measure.Weil.QuatTamagawaGlobal

/-!
# Fujisaki's lemma: $\mathbb H_{\mathbb A}^1/\mathbb H^\times$ is compact for a quaternion division algebra


$F$ is any number field and $\mathbb H = \mathbb H[F,a,b]$ is a quaternion **division** algebra over $F$, expressed by the
Mathlib-level hypothesis `hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ` (every nonzero element is invertible; equivalently the
norm form is anisotropic over $F$). There is no restriction on the signature at the infinite places.

* **Abstract Fujisaki lemma** (`exists_isCompact_units_mul_mem`, Mathlib-only hypotheses). Let $R$ be a Hausdorff
  topological ring, $d : D\to R$ a ring map from a division ring-like $D$ (every nonzero element a unit) with discrete
  image in the sense that $d^{-1}(K)$ is finite for every compact $K$, and $H\le R^\times$ a closed subgroup containing
  $d(D^\times)$. If there are compact $K_1, K_2\subseteq R$ with $x\,d(\xi)\in K_1$ and $d(\xi)\,x\in K_2$ for some
  $\xi\ne0$, for every $x\in H$ (two-sided Minkowski), then $H = d(D^\times)\cdot C$ for a compact $C\subseteq H$.
  *Proof* (Fujisaki 1958; Weil): for $x\in H$ take $\eta\ne0$ with $x^{-1}d(\eta)\in K_1$ and $\xi\ne0$ with
  $d(\xi)x\in K_2$. Then $d(\xi\eta) = (d(\xi)x)(x^{-1}d(\eta))\in K_2K_1$, so $\xi\eta$ lies in the finite set
  $S = d^{-1}(K_2K_1)$. With $v = d(\eta)^{-1}x$: $v^{-1}\in K_1$ and $v = d((\xi\eta)^{-1})\,(d(\xi)x)\in\bigcup_{\zeta\in S}
  d(\zeta^{-1})K_2 =: K_3$. So $v$ lies in $\{v : v\in K_3,\ v^{-1}\in K_1\}\cap H$, which is compact in the units topology
  (`Units.isClosedEmbedding_embedProduct`).
* **Quaternions.** $K_1$ is given by `exists_isCompact_forall_quat_mul_mem`
  (left Minkowski, $\|\operatorname{nrd}x\|\le1$);
  $K_2 = \overline{K_1}$ is obtained from it through the anti-involution $x\mapsto\bar x$ (`quatStarUnit`,
  `nrdUnit_quatStarUnit`). Finiteness of $d^{-1}(K)$ is discreteness of $\mathbb H$ in $\mathbb A_F^4$
  (`finite_quatDiagRing_preimage`). An anisotropic norm form gives `hdiv` (`isUnit_of_nrd_ne_zero`).
  **`exists_isCompact_quatOne_mul_mem`**: $\mathbb H_{\mathbb A}^1 = \mathbb H^\times\cdot C$ with $C$ compact;
  **`compactSpace_quatClassOne`**: $\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1$ is compact.
* **Consequences for the quotient measure.** For every Haar measure $\mu$ on $(\mathbb H\otimes\mathbb A)^\times$
  the quotient measure `muQuatClass μ` is finite and nonzero (`muQuatClass_univ_lt_top`, `muQuatClass_univ_ne_zero`,
  `isFiniteMeasure_muQuatClass`); in particular for the canonical Tamagawa measure (`muQuatClassTam_univ_lt_top`,
  `muQuatClassTam_univ_ne_zero`).
* **The commutative analogue** ($A = F$): **`exists_isCompact_ideleOne_mul_mem`**, **`compactSpace_ideleClassOne`**
  ($F^\times\backslash\mathbb A_F^1$ compact), `muIdeleClass_univ_lt_top`, `muIdeleClass_univ_ne_zero`, from
  `exists_isCompact_forall_idele_smul_mem`.

**Prior formalization (cited, not imported).** Fujisaki's lemma for an arbitrary finite-dimensional division algebra
over a number field is formalized in the FLT project (K. Buzzard et al., `FLT/DivisionAlgebra/Finiteness.lean`,
theorem `compact_quotient` with `D_discrete` and `units_cocompact`; commit a9efe58, Apache-2.0).
This file is a lean rewrite on the library's own measures and Minkowski
theorem; no FLT code is used or copied. The structure of the argument (two-sided Minkowski, finiteness of
$D\cap K_2K_1$, closed embedding of the units) is the classical one of Fujisaki and Weil and is shared with FLT.
The Mathlib lemmas doing the heavy lifting are `Units.isClosedEmbedding_embedProduct`,
`AddMonoidHom.tendsto_coe_cofinite_of_isDiscrete`, `IsCompact.mul`, `Set.Finite.isCompact_biUnion` and
`MeasureTheory.IsFundamentalDomain.measure_eq_tsum` / `measure_ne_zero`.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Pointwise Quaternion

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

/-! ### The abstract Fujisaki lemma -/

section Abstract

variable {R D : Type*} [Ring R] [TopologicalSpace R] [ContinuousMul R] [T2Space R] [Ring D]

/-- **Abstract Fujisaki lemma.** Let $d : D\to R$ be a ring map into a Hausdorff topological ring with every nonzero
element of $D$ a unit and $d^{-1}(K)$ finite for compact $K$, and let $H\le R^\times$ be a closed subgroup containing
$d(D^\times)$. If two compact sets $K_1, K_2$ satisfy the two-sided Minkowski property ($x\,d(\xi)\in K_1$,
$d(\xi')\,x\in K_2$ for some $\xi,\xi'\ne0$, for every $x\in H$), then $H = d(D^\times)\cdot C$ for a compact
$C\subseteq H$. Rewritten (not imported) after FLT's `compact_quotient` (`FLT/DivisionAlgebra/Finiteness.lean`). -/
@[kb "weil1982" "Fujisaki's lemma (A_𝔸^1/A^× compact) [unverified locator]; FLT compact_quotient (cited)"]
theorem exists_isCompact_units_mul_mem (d : D →+* R) (hdiv : ∀ ξ : D, ξ ≠ 0 → IsUnit ξ)
    (hfin : ∀ K : Set R, IsCompact K → {ζ : D | d ζ ∈ K}.Finite)
    (H : Subgroup Rˣ) (hH : IsClosed (H : Set Rˣ)) (hDH : ∀ γ : Dˣ, Units.map d.toMonoidHom γ ∈ H)
    {K₁ K₂ : Set R} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hL : ∀ x ∈ H, ∃ ξ : D, ξ ≠ 0 ∧ (x : R) * d ξ ∈ K₁)
    (hR : ∀ x ∈ H, ∃ ξ : D, ξ ≠ 0 ∧ d ξ * (x : R) ∈ K₂) :
    ∃ C : Set Rˣ, IsCompact C ∧ C ⊆ H ∧ ∀ x ∈ H, ∃ γ : Dˣ, (Units.map d.toMonoidHom γ)⁻¹ * x ∈ C := by
  set S : Set D := {ζ | d ζ ∈ K₂ * K₁}
  have hS : S.Finite := hfin _ (hK₂.mul hK₁)
  set K₃ : Set R := ⋃ ζ ∈ S, (fun z => d (Ring.inverse ζ) * z) '' K₂
  have hK₃ : IsCompact K₃ :=
    hS.isCompact_biUnion fun ζ _ => hK₂.image (continuous_const.mul continuous_id)
  refine ⟨(Units.embedProduct R ⁻¹' (K₃ ×ˢ (MulOpposite.op '' K₁))) ∩ H, ?_, inter_subset_right,
    fun x hx => ?_⟩
  · exact (Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hK₃.prod (hK₁.image MulOpposite.continuous_op))).inter_right hH
  obtain ⟨η, hη0, hη⟩ := hL x⁻¹ (H.inv_mem hx)
  obtain ⟨ξ, hξ0, hξ⟩ := hR x hx
  set γ : Dˣ := (hdiv η hη0).unit
  have hγ : (γ : D) = η := IsUnit.unit_spec _
  have hξη0 : ξ * η ≠ 0 := by
    intro h
    apply hη0
    have := congrArg (fun z => Ring.inverse ξ * z) h
    simpa only [← mul_assoc, Ring.inverse_mul_cancel _ (hdiv ξ hξ0), one_mul, mul_zero] using this
  have hS' : ξ * η ∈ S := by
    change d (ξ * η) ∈ K₂ * K₁
    refine ⟨d ξ * x, hξ, ((x⁻¹ : Rˣ) : R) * d η, hη, ?_⟩
    change (d ξ * x) * (((x⁻¹ : Rˣ) : R) * d η) = d (ξ * η)
    rw [map_mul, mul_assoc, ← mul_assoc (x : R), Units.mul_inv, one_mul]
  have hγinv : ((γ⁻¹ : Dˣ) : D) = Ring.inverse (ξ * η) * ξ := by
    calc ((γ⁻¹ : Dˣ) : D) = (Ring.inverse (ξ * η) * (ξ * η)) * ((γ⁻¹ : Dˣ) : D) := by
          rw [Ring.inverse_mul_cancel _ (hdiv _ hξη0), one_mul]
      _ = Ring.inverse (ξ * η) * ξ := by
          rw [mul_assoc, mul_assoc, ← hγ, Units.mul_inv, mul_one]
  refine ⟨γ, ⟨⟨?_, ?_⟩, H.mul_mem (H.inv_mem (hDH γ)) hx⟩⟩
  · refine mem_biUnion hS' ⟨d ξ * x, hξ, ?_⟩
    change d (Ring.inverse (ξ * η)) * (d ξ * x) = d ((γ⁻¹ : Dˣ) : D) * (x : R)
    rw [hγinv, map_mul, mul_assoc]
  · refine ⟨((x⁻¹ : Rˣ) : R) * d η, hη, ?_⟩
    change _ = MulOpposite.op (((((Units.map d.toMonoidHom γ)⁻¹ * x)⁻¹ : Rˣ) : R))
    rw [mul_inv_rev, inv_inv]
    change MulOpposite.op (((x⁻¹ : Rˣ) : R) * d η) = MulOpposite.op (((x⁻¹ : Rˣ) : R) * d (γ : D))
    rw [hγ]

/-- An injective additive map with discrete image meets every compact set in a finite set. -/
theorem finite_preimage_isCompact_of_discrete {A G : Type*} [AddGroup A] [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T2Space G] (f : A →+ G) (hf : Function.Injective f)
    (hd : DiscreteTopology f.range) {K : Set G} (hK : IsCompact K) : {ζ : A | f ζ ∈ K}.Finite := by
  have ht := AddMonoidHom.tendsto_coe_cofinite_of_isDiscrete hf (isDiscrete_iff_discreteTopology.mpr hd)
  have := ht hK.compl_mem_cocompact
  rw [Filter.mem_map, mem_cofinite, ← preimage_compl, compl_compl] at this
  exact this

end Abstract

variable {F : Type} [Field F] [NumberField F]

set_option synthInstance.maxHeartbeats 400000

/-! ### Quaternions -/

section Quaternion

variable (a b : F)

omit [NumberField F] in
/-- **Anisotropic norm form ⇒ division algebra**: if $\operatorname{nrd}\xi = \xi\bar\xi\ne0$ for every $\xi\ne0$, then
every nonzero $\xi$ is a unit, with $\xi^{-1} = \operatorname{nrd}(\xi)^{-1}\bar\xi$. This supplies `hdiv` below. -/
theorem isUnit_of_nrd_ne_zero (haniso : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → (ξ * star ξ).re ≠ 0) :
    ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ := by
  intro ξ hξ
  have hc : ξ * star ξ = ((ξ * star ξ).re : ℍ[F,a,b]) := QuaternionAlgebra.mul_star_eq_coe ξ
  have hc' : star ξ * ξ = ((ξ * star ξ).re : ℍ[F,a,b]) := by rw [star_comm_self']; exact hc
  generalize hN : (ξ * star ξ).re = N at hc hc'
  have hn : N ≠ 0 := hN ▸ haniso ξ hξ
  have h1 : ξ * (N⁻¹ • star ξ) = 1 := by
    rw [mul_smul_comm, hc, QuaternionAlgebra.smul_coe, inv_mul_cancel₀ hn, QuaternionAlgebra.coe_one]
  have h2 : (N⁻¹ • star ξ) * ξ = 1 := by
    rw [smul_mul_assoc, hc', QuaternionAlgebra.smul_coe, inv_mul_cancel₀ hn, QuaternionAlgebra.coe_one]
  exact ⟨⟨ξ, _, h1, h2⟩, rfl⟩

/-- **$\mathbb H$ is discrete in $\mathbb H_{\mathbb A}$**: it meets every compact set in a finite set. -/
theorem finite_quatDiagRing_preimage {K : Set (QuatAdele a b)} (hK : IsCompact K) :
    {ζ : ℍ[F,a,b] | quatDiagRing a b ζ ∈ K}.Finite := by
  have h := finite_preimage_isCompact_of_discrete (diagQuat a b) (diagQuat_injective a b)
    (discreteTopology_diagQuat a b) (hK.image (continuous_quatCoord a b))
  refine h.subset fun ζ hζ => ⟨quatDiagRing a b ζ, hζ, ?_⟩
  exact quatCoord_quatDiagRing a b ζ

/-- Quaternion conjugation is continuous on $\mathbb H_{\mathbb A}$. -/
theorem continuous_star_quat : Continuous (star : QuatAdele a b → QuatAdele a b) := by
  refine (continuous_quat_iff a b).mpr ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
      QuaternionAlgebra.imK_star]
  · exact (continuous_re a b).add (continuous_const.mul (continuous_imI a b))
  · exact (continuous_imI a b).neg
  · exact (continuous_imJ a b).neg
  · exact (continuous_imK a b).neg

variable {a b}

/-- The conjugate $\bar x$ of a unit, as a unit. -/
def quatStarUnit (x : (QuatAdele a b)ˣ) : (QuatAdele a b)ˣ where
  val := star (x : QuatAdele a b)
  inv := star ((x⁻¹ : (QuatAdele a b)ˣ) : QuatAdele a b)
  val_inv := by rw [← star_mul, Units.inv_mul, star_one]
  inv_val := by rw [← star_mul, Units.mul_inv, star_one]

theorem nrdUnit_quatStarUnit (x : (QuatAdele a b)ˣ) : nrdUnit (quatStarUnit x) = nrdUnit x := by
  refine Units.ext ?_
  rw [nrdUnit_val, nrdUnit_val]
  change (star (x : QuatAdele a b) * star (star (x : QuatAdele a b))).re = _
  rw [star_star, star_comm_self']

theorem quatStarUnit_mem_quatOne {x : (QuatAdele a b)ˣ} (hx : x ∈ quatOne a b) : quatStarUnit x ∈ quatOne a b := by
  rw [mem_quatOne, nrdUnit_quatStarUnit]; exact (mem_quatOne a b).mp hx

variable (a b)

/-- Left Minkowski on $\mathbb H_{\mathbb A}^1$ inside $\mathbb H_{\mathbb A}$. -/
theorem exists_isCompact_forall_quatOne_mul_mem :
    ∃ K : Set (QuatAdele a b), IsCompact K ∧
      ∀ x ∈ quatOne a b, ∃ ξ : ℍ[F,a,b], ξ ≠ 0 ∧ (x : QuatAdele a b) * quatDiagRing a b ξ ∈ K := by
  obtain ⟨K, hK, hKx⟩ := exists_isCompact_forall_quat_mul_mem (a := a) (b := b) (1 : ℝ)
  refine ⟨quatCoord a b ⁻¹' K, (isClosedEmbedding_quatCoord a b).isCompact_preimage hK, fun x hx => ?_⟩
  obtain ⟨ξ, hξ, hmem⟩ := hKx x ((mem_quatOne a b).mp hx).le
  exact ⟨ξ, hξ, hmem⟩

/-- Right Minkowski on $\mathbb H_{\mathbb A}^1$, through conjugation. -/
theorem exists_isCompact_forall_quatOne_mul_mem' :
    ∃ K : Set (QuatAdele a b), IsCompact K ∧
      ∀ x ∈ quatOne a b, ∃ ξ : ℍ[F,a,b], ξ ≠ 0 ∧ quatDiagRing a b ξ * (x : QuatAdele a b) ∈ K := by
  obtain ⟨K, hK, hKx⟩ := exists_isCompact_forall_quatOne_mul_mem a b
  refine ⟨star '' K, hK.image (continuous_star_quat a b), fun x hx => ?_⟩
  obtain ⟨ξ, hξ, hmem⟩ := hKx (quatStarUnit x) (quatStarUnit_mem_quatOne hx)
  refine ⟨star ξ, star_ne_zero.mpr hξ, _, hmem, ?_⟩
  change star (star (x : QuatAdele a b) * quatDiagRing a b ξ) = _
  rw [star_mul, star_star, quatDiagRing_star]

/-- **Fujisaki's lemma for a quaternion division algebra** (any number field, any signature):
$\mathbb H_{\mathbb A}^1 = \mathbb H^\times\cdot C$ for a compact $C\subseteq\mathbb H_{\mathbb A}^1$. Rewritten on the library's
Minkowski theorem, citing FLT's `compact_quotient` (`FLT/DivisionAlgebra/Finiteness.lean`, not imported) and
Fujisaki (1958). -/
@[kb "weil1982" "Fujisaki's lemma, D_𝔸^1/D^× compact [unverified locator]; FLT compact_quotient (cited)"]
theorem exists_isCompact_quatOne_mul_mem (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) :
    ∃ C : Set (quatOne a b), IsCompact C ∧ ∀ x : quatOne a b, ∃ γ ∈ quatUnitsOne a b, γ⁻¹ * x ∈ C := by
  obtain ⟨K₁, hK₁, hL⟩ := exists_isCompact_forall_quatOne_mul_mem a b
  obtain ⟨K₂, hK₂, hR⟩ := exists_isCompact_forall_quatOne_mul_mem' a b
  have hDH : ∀ γ : (ℍ[F,a,b])ˣ, Units.map (quatDiagRing a b).toMonoidHom γ ∈ quatOne a b :=
    fun γ => quatUnitsSub_le_quatOne a b ⟨γ, rfl⟩
  obtain ⟨C, hC, -, hCx⟩ := exists_isCompact_units_mul_mem (quatDiagRing a b) hdiv
    (fun K hK => finite_quatDiagRing_preimage a b hK) (quatOne a b) (isClosed_quatOne a b) hDH hK₁ hK₂ hL hR
  refine ⟨Subtype.val ⁻¹' C, (isClosed_quatOne a b).isClosedEmbedding_subtypeVal.isCompact_preimage hC,
    fun x => ?_⟩
  obtain ⟨γ, hγ⟩ := hCx x x.2
  exact ⟨⟨_, hDH γ⟩, Subgroup.mem_subgroupOf.mpr ⟨γ, rfl⟩, hγ⟩

/-- **$\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1$ is compact** for a quaternion division algebra (Fujisaki). -/
@[kb "weil1982" "Fujisaki's lemma, D_𝔸^1/D^× compact [unverified locator]; FLT compact_quotient (cited)"]
theorem compactSpace_quatClassOne (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) : CompactSpace (QuatClassOne a b) := by
  obtain ⟨C, hC, hCx⟩ := exists_isCompact_quatOne_mul_mem a b hdiv
  refine ⟨?_⟩
  have : quatClassMk a b '' C = univ := by
    refine eq_univ_of_forall fun q => ?_
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    obtain ⟨γ, hγ, hmem⟩ := hCx x
    exact ⟨γ⁻¹ * x, hmem, Quotient.sound ⟨⟨γ⁻¹, inv_mem hγ⟩, rfl⟩⟩
  rw [← this]
  exact hC.image continuous_quotient_mk'

variable {a b}

/-- **The quotient measure is finite** (Fujisaki), for every Haar measure on $(\mathbb H\otimes\mathbb A)^\times$. -/
@[kb "weil1982" "Fujisaki's lemma ⇒ vol(D^×\\D_𝔸^1) < ∞ [unverified locator]"]
theorem muQuatClass_univ_lt_top (μ : Measure (QuatAdele a b)ˣ) [μ.IsHaarMeasure]
    (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) : muQuatClass μ univ < ∞ := by
  obtain ⟨C, hC, hCx⟩ := exists_isCompact_quatOne_mul_mem a b hdiv
  obtain ⟨D, hD⟩ := exists_isFundamentalDomain_quatOne a b (muQuatOne μ)
  rw [muQuatClass_univ μ hD]
  refine lt_of_le_of_lt ?_ (hC.measure_lt_top (μ := muQuatOne μ))
  rw [hD.measure_eq_tsum C]
  calc muQuatOne μ D ≤ muQuatOne μ (⋃ g : quatUnitsOne a b, g • C ∩ D) := by
        refine measure_mono fun x hx => ?_
        obtain ⟨γ, hγ, hmem⟩ := hCx x
        refine mem_iUnion.mpr ⟨⟨γ, hγ⟩, ?_, hx⟩
        rw [mem_smul_set_iff_inv_smul_mem]
        exact hmem
    _ ≤ ∑' g : quatUnitsOne a b, muQuatOne μ (g • C ∩ D) := measure_iUnion_le _

/-- **The quotient measure is nonzero.** -/
theorem muQuatClass_univ_ne_zero (μ : Measure (QuatAdele a b)ˣ) [μ.IsHaarMeasure] : muQuatClass μ univ ≠ 0 := by
  obtain ⟨D, hD⟩ := exists_isFundamentalDomain_quatOne a b (muQuatOne μ)
  rw [muQuatClass_univ μ hD]
  exact hD.measure_ne_zero (NeZero.ne _)

theorem isFiniteMeasure_muQuatClass (μ : Measure (QuatAdele a b)ˣ) [μ.IsHaarMeasure]
    (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) : IsFiniteMeasure (muQuatClass μ) :=
  ⟨muQuatClass_univ_lt_top μ hdiv⟩

variable (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
  (ha0 : a ≠ 0) (hb0 : b ≠ 0)

include ha hb ha0 hb0 in
/-- **$\operatorname{vol}(\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1) < \infty$ for the canonical Tamagawa measure**
(Fujisaki). -/
@[kb "weil1982" "Fujisaki's lemma ⇒ vol(D^×\\D_𝔸^1) < ∞ [unverified locator]"]
theorem muQuatClassTam_univ_lt_top (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) :
    muQuatClassTam ha hb ha0 hb0 univ < ∞ := by
  have := isHaarMeasure_tamQuat ha hb ha0 hb0
  exact muQuatClass_univ_lt_top (tamQuat a b) hdiv

include ha hb ha0 hb0 in
/-- **$\operatorname{vol}(\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1) > 0$ for the canonical Tamagawa measure.** -/
theorem muQuatClassTam_univ_ne_zero : muQuatClassTam ha hb ha0 hb0 univ ≠ 0 := by
  have := isHaarMeasure_tamQuat ha hb ha0 hb0
  exact muQuatClass_univ_ne_zero (tamQuat a b)

include ha hb ha0 hb0 in
/-- The canonical quotient measure on $\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1$ is a finite measure. -/
theorem isFiniteMeasure_muQuatClassTam (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) :
    IsFiniteMeasure (muQuatClassTam ha hb ha0 hb0) :=
  ⟨muQuatClassTam_univ_lt_top ha hb ha0 hb0 hdiv⟩

end Quaternion

/-! ### The commutative analogue: $F^\times\backslash\mathbb A_F^1$ is compact -/

section Idele

variable (F)

/-- **$F^\times\backslash\mathbb A_F^1$ is compact, explicit form**: $\mathbb A_F^1 = F^\times\cdot C$ with $C$ compact
(the abstract Fujisaki lemma with $D = F$; Minkowski for ideles). -/
@[kb "weil1982" "compactness of 𝔸^1/F^× [unverified locator]"]
theorem exists_isCompact_ideleOne_mul_mem :
    ∃ C : Set (ideleOne F), IsCompact C ∧ ∀ x : ideleOne F, ∃ γ ∈ diagUnitsOne F, γ⁻¹ * x ∈ C := by
  obtain ⟨K, hK, hKx⟩ := exists_isCompact_forall_idele_smul_mem (F := F) 1
  have hL : ∀ x ∈ ideleOne F, ∃ ξ : F, ξ ≠ 0 ∧ (x : Adeles F) * diagRing F ξ ∈ K := fun x hx => by
    obtain ⟨ξ, hξ, hmem⟩ := hKx x ((mem_ideleOne).mp hx).le
    exact ⟨ξ, hξ, hmem⟩
  have hR : ∀ x ∈ ideleOne F, ∃ ξ : F, ξ ≠ 0 ∧ diagRing F ξ * (x : Adeles F) ∈ K := fun x hx => by
    obtain ⟨ξ, hξ, hmem⟩ := hL x hx
    exact ⟨ξ, hξ, by rwa [mul_comm]⟩
  have hDH : ∀ γ : Fˣ, Units.map (diagRing F).toMonoidHom γ ∈ ideleOne F :=
    fun γ => diagUnitsSub_le_ideleOne ⟨γ, rfl⟩
  have hfin : ∀ K' : Set (Adeles F), IsCompact K' → {ζ : F | diagRing F ζ ∈ K'}.Finite := fun K' hK' =>
    finite_preimage_isCompact_of_discrete (diag F) diag_injective discreteTopology_diagSub hK'
  obtain ⟨C, hC, -, hCx⟩ := exists_isCompact_units_mul_mem (diagRing F) (fun ξ hξ => hξ.isUnit) hfin
    (ideleOne F) isClosed_ideleOne hDH hK hK hL hR
  refine ⟨Subtype.val ⁻¹' C, isClosed_ideleOne.isClosedEmbedding_subtypeVal.isCompact_preimage hC,
    fun x => ?_⟩
  obtain ⟨γ, hγ⟩ := hCx x x.2
  exact ⟨⟨_, hDH γ⟩, Subgroup.mem_subgroupOf.mpr ⟨γ, rfl⟩, hγ⟩

/-- **$F^\times\backslash\mathbb A_F^1$ is compact.** -/
@[kb "weil1982" "compactness of 𝔸^1/F^× [unverified locator]"]
theorem compactSpace_ideleClassOne : CompactSpace (IdeleClassOne F) := by
  obtain ⟨C, hC, hCx⟩ := exists_isCompact_ideleOne_mul_mem F
  refine ⟨?_⟩
  have : ideleClassMk F '' C = univ := by
    refine eq_univ_of_forall fun q => ?_
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    obtain ⟨γ, hγ, hmem⟩ := hCx x
    exact ⟨γ⁻¹ * x, hmem, Quotient.sound ⟨⟨γ⁻¹, inv_mem hγ⟩, rfl⟩⟩
  rw [← this]
  exact hC.image continuous_quotient_mk'

/-- **$\operatorname{vol}(F^\times\backslash\mathbb A_F^1) < \infty$** for the canonical measure. -/
theorem muIdeleClass_univ_lt_top : muIdeleClass F univ < ∞ := by
  obtain ⟨C, hC, hCx⟩ := exists_isCompact_ideleOne_mul_mem F
  have hD := isFundamentalDomain_ideleClassFD (F := F)
  rw [muIdeleClass_univ hD]
  refine lt_of_le_of_lt ?_ (hC.measure_lt_top (μ := muIdeleOne F))
  rw [hD.measure_eq_tsum C]
  calc muIdeleOne F (ideleClassFD F) ≤ muIdeleOne F (⋃ g : diagUnitsOne F, g • C ∩ ideleClassFD F) := by
        refine measure_mono fun x hx => ?_
        obtain ⟨γ, hγ, hmem⟩ := hCx x
        refine mem_iUnion.mpr ⟨⟨γ, hγ⟩, ?_, hx⟩
        rw [mem_smul_set_iff_inv_smul_mem]
        exact hmem
    _ ≤ ∑' g : diagUnitsOne F, muIdeleOne F (g • C ∩ ideleClassFD F) := measure_iUnion_le _

/-- **$\operatorname{vol}(F^\times\backslash\mathbb A_F^1) > 0$.** -/
theorem muIdeleClass_univ_ne_zero : muIdeleClass F univ ≠ 0 := by
  have hD := isFundamentalDomain_ideleClassFD (F := F)
  rw [muIdeleClass_univ hD]
  exact hD.measure_ne_zero (NeZero.ne _)

instance isFiniteMeasure_muIdeleClass : IsFiniteMeasure (muIdeleClass F) := ⟨muIdeleClass_univ_lt_top F⟩

end Idele

end

end QuadFormsKB.Tamagawa.Measure.Weil
