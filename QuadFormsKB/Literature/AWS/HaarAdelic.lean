/-
# Hanke, AWS 2009 notes, §4.6: the Haar measure on $O(V_\mathbb{A})$ and the integral over $O(V)\backslash O(V_\mathbb{A})$

J. Hanke, *Quadratic Forms and Automorphic Forms* (bibkey `hanke2011aws`), §4.5–§4.6 (pp. 61–64).
This file **constructs** the measure $dh_\mathbb{A}$ on $G = O(V_\mathbb{A})$ used in the notes and the
integral over $O(V)\backslash O(V_\mathbb{A})$, discharging the input `QuotientIntegralInputs`
(`AWS/Unfolding.lean`) for the adelic orthogonal group of a positive definite form.

**Setting.** $H \in M_n(\mathbb{Q})$ symmetric with $H$ positive definite over $\mathbb{R}$;
$G = O(V_\mathbb{A}) = O(V)(\mathbb{R}) \times \prod'_p O(V)(\mathbb{Q}_p)$ (`OA H`) with the product of
the topology of $O(V)(\mathbb{R}) \subseteq \mathrm{GL}_n(\mathbb{R})$ and the restricted product topology
(Mathlib's `RestrictedProduct` topology, for the open subgroups $O(V)(\mathbb{Z}_p)$); the Borel
σ-algebra; $\Gamma = O(V)$ embedded diagonally (`ratPoints H`); $K = K_\mathbb{A}$ (`KA H`).

**Results.**
- `isOpen_KA`, `isCompact_KA`: $K_\mathbb{A}$ is a compact open subgroup of $G$ (compactness uses that
  $O(V)(\mathbb{R})$ is compact, i.e. $H$ positive definite, `isCompact_orthGroup_real`).
- `haarOA`: the left Haar measure on $G$ normalized by $\mu(K_\mathbb{A}) = 1$ (the notes' normalization,
  p. 61: "giving the adelic stabilizer $\mathrm{Stab}_\mathbb{A}(L)$ volume $1$"), `haarOA_KA`.
- `countable_ratPoints`: $O(V)$ is countable.
- `quotientIntegralInputsOA`: given representatives $\alpha_i$ of the finitely many double cosets
  $O(V)\alpha_iK_\mathbb{A}$ with finite $O(V)\cap\alpha_iK_\mathbb{A}\alpha_i^{-1}$, the integral
  $I(F) = \sum_i |\Gamma_i|^{-1}\int_{K_\mathbb{A}} F(\alpha_i h)\,dh$ (`dosetIntegral`) satisfies Weil's
  formula for `haarOA` (`AWS/QuotientIntegral.lean`); this is a term of `QuotientIntegralInputs`.
-/
import QuadFormsKB.Literature.AWS.HaarLocal
import QuadFormsKB.Literature.AWS.HaarInfty
import QuadFormsKB.Literature.AWS.QuotientIntegral

open MeasureTheory Matrix

namespace QuadFormsKB.AWS

variable {n : ℕ}

/-- The local stabilizers $O(V)(\mathbb{Z}_p)$ are open (`isOpen_intStab`); needed for the restricted
product topology on $O(V_{\mathbb{A}_f})$ to be a group topology. -/
instance factIsOpenIntStab (H : Matrix (Fin n) (Fin n) ℚ) :
    Fact (∀ p : PrimeIdx, IsOpen (intStab H (p : ℕ) : Set (orthGroup H ℚ_[(p : ℕ)]))) :=
  ⟨fun p => isOpen_intStab H p⟩

/-- The Borel σ-algebra on $O(V_\mathbb{A})$. -/
noncomputable instance measurableSpaceOA (H : Matrix (Fin n) (Fin n) ℚ) : MeasurableSpace (OA H) :=
  borel _

instance borelSpaceOA (H : Matrix (Fin n) (Fin n) ℚ) : BorelSpace (OA H) := ⟨rfl⟩

/-- $K_\mathbb{A} = O(V)(\mathbb{R}) \times \prod_p O(V)(\mathbb{Z}_p)$ as a set. -/
theorem coe_KA (H : Matrix (Fin n) (Fin n) ℚ) :
    (KA H : Set (OA H)) = Set.univ ×ˢ {f : OAf H | ∀ p : PrimeIdx, f.1 p ∈ intStab H (p : ℕ)} := by
  ext x
  simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_ofPred_eq]
  rfl

/-- **$K_\mathbb{A}$ is open** in $O(V_\mathbb{A})$. -/
theorem isOpen_KA (H : Matrix (Fin n) (Fin n) ℚ) : IsOpen (KA H : Set (OA H)) := by
  rw [coe_KA]
  exact isOpen_univ.prod (RestrictedProduct.isOpen_forall_mem fun p => isOpen_intStab H p)

/-- $\prod_p O(V)(\mathbb{Z}_p)$ is compact in $O(V_{\mathbb{A}_f})$ (Tychonoff). -/
theorem isCompact_intPoints (H : Matrix (Fin n) (Fin n) ℚ) :
    IsCompact {f : OAf H | ∀ p : PrimeIdx, f.1 p ∈ intStab H (p : ℕ)} := by
  have e := RestrictedProduct.range_structureMap (R := fun p : PrimeIdx => orthGroup H ℚ_[(p : ℕ)])
    (A := fun p => (intStab H (p : ℕ) : Set (orthGroup H ℚ_[(p : ℕ)]))) (𝓕 := Filter.cofinite)
  have : ∀ p : PrimeIdx, CompactSpace (intStab H (p : ℕ) : Set (orthGroup H ℚ_[(p : ℕ)])) :=
    fun p => isCompact_iff_compactSpace.mp (isCompact_intStab H p)
  have hc := isCompact_range (RestrictedProduct.isEmbedding_structureMap (R := fun p : PrimeIdx =>
    orthGroup H ℚ_[(p : ℕ)]) (A := fun p => (intStab H (p : ℕ) : Set (orthGroup H ℚ_[(p : ℕ)])))
    (𝓕 := Filter.cofinite)).continuous
  rw [e] at hc
  exact hc

/-- **$K_\mathbb{A}$ is compact** for $H$ positive definite over $\mathbb{R}$. -/
theorem isCompact_KA (H : Matrix (Fin n) (Fin n) ℚ) (hH : (H.map (algebraMap ℚ ℝ)).PosDef) :
    IsCompact (KA H : Set (OA H)) := by
  rw [coe_KA]
  exact (isCompact_orthGroup_real H hH).prod (isCompact_intPoints H)

/-- $K_\mathbb{A}$ as a compact set with nonempty interior. -/
def KApos (H : Matrix (Fin n) (Fin n) ℚ) (hH : (H.map (algebraMap ℚ ℝ)).PosDef) :
    TopologicalSpace.PositiveCompacts (OA H) where
  carrier := KA H
  isCompact' := isCompact_KA H hH
  interior_nonempty' := by
    rw [(isOpen_KA H).interior_eq]
    exact ⟨1, (KA H).one_mem⟩

/-- **The Haar measure $dh_\mathbb{A}$ on $O(V_\mathbb{A})$** (§4.5, p. 61): the left Haar measure
normalized by $\mu(K_\mathbb{A}) = 1$, for $H$ positive definite over $\mathbb{R}$. -/
@[kb "hanke2011aws" "§4.5, p. 61"]
noncomputable def haarOA (H : Matrix (Fin n) (Fin n) ℚ) (hH : (H.map (algebraMap ℚ ℝ)).PosDef) :
    Measure (OA H) :=
  Measure.haarMeasure (KApos H hH)

instance (H : Matrix (Fin n) (Fin n) ℚ) (hH : (H.map (algebraMap ℚ ℝ)).PosDef) :
    (haarOA H hH).IsMulLeftInvariant :=
  Measure.isMulLeftInvariant_haarMeasure _

/-- **The normalization** $\mathrm{vol}(K_\mathbb{A}) = 1$ (p. 61). -/
@[kb "hanke2011aws" "§4.5, p. 61"]
theorem haarOA_KA (H : Matrix (Fin n) (Fin n) ℚ) (hH : (H.map (algebraMap ℚ ℝ)).PosDef) :
    haarOA H hH (KA H) = 1 :=
  Measure.haarMeasure_self

/-- $\mathrm{GL}_n(\mathbb{Q})$ is countable. -/
theorem countable_GL_rat : Countable (GL (Fin n) ℚ) := by
  have : Countable (Matrix (Fin n) (Fin n) ℚ) := inferInstanceAs (Countable (Fin n → Fin n → ℚ))
  exact Function.Injective.countable (f := fun g : GL (Fin n) ℚ => g.val) Units.val_injective

/-- **The rational points $O(V) \le O(V_\mathbb{A})$ form a countable group.** -/
instance countable_ratPoints (H : Matrix (Fin n) (Fin n) ℚ) : Countable (ratPoints H) := by
  have := countable_GL_rat (n := n)
  exact (Set.countable_range (diag H)).to_subtype

/-- **Discharge of `QuotientIntegralInputs` for $O(V)\backslash O(V_\mathbb{A})$** (§4.6, (4.4)–(4.13)):
for $H$ positive definite over $\mathbb{R}$ and representatives $\alpha_i$ ($i \in I$, $I$ finite) of the
double cosets $O(V)\alpha_iK_\mathbb{A}$ (`hcov`, `hdisj`) with each
$O(V)\cap\alpha_iK_\mathbb{A}\alpha_i^{-1}$ finite (`hfin`), the integral
$I(F) = \sum_i |O(V)\cap\alpha_iK_\mathbb{A}\alpha_i^{-1}|^{-1}\int_{K_\mathbb{A}}F(\alpha_ih)\,dh$
satisfies Weil's formula for the Haar measure `haarOA` with $\mathrm{vol}(K_\mathbb{A}) = 1$. -/
noncomputable def quotientIntegralInputsOA (H : Matrix (Fin n) (Fin n) ℚ)
    (hH : (H.map (algebraMap ℚ ℝ)).PosDef) {ι : Type*} [Fintype ι] (α : ι → OA H)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints H) (KA H))
    (hdisj : ∀ i j, DoubleCoset.mk (ratPoints H) (KA H) (α i) =
      DoubleCoset.mk (ratPoints H) (KA H) (α j) → i = j)
    (hfin : ∀ i, Finite (ratPoints H ⊓ conjSub (α i) (KA H) : Subgroup (OA H))) :
    QuotientIntegralInputs (ratPoints H) (KA H) (haarOA H hH) :=
  QuotientIntegralInputs.ofDoubleCosets inferInstance (isOpen_KA H).measurableSet (haarOA_KA H hH)
    α hcov hdisj hfin

/-- **Weil's formula on $O(V)\backslash O(V_\mathbb{A})$** (§4.6; Weil, *L'intégration dans les groupes
topologiques*, §9): with the hypotheses of `quotientIntegralInputsOA`, for every
$dh_\mathbb{A}$-integrable $f : O(V_\mathbb{A}) \to \mathbb{C}$,
$$\sum_i \frac{1}{|O(V)\cap\alpha_iK_\mathbb{A}\alpha_i^{-1}|}\int_{K_\mathbb{A}}\sum_{\gamma\in O(V)}
f(\gamma\alpha_ih)\,dh = \int_{O(V_\mathbb{A})} f(h)\,dh .$$ -/
@[kb "hanke2011aws" "§4.6, (4.4)-(4.13), pp. 63-64"]
theorem weil_OA (H : Matrix (Fin n) (Fin n) ℚ)
    (hH : (H.map (algebraMap ℚ ℝ)).PosDef) {ι : Type*} [Fintype ι] (α : ι → OA H)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints H) (KA H))
    (hdisj : ∀ i j, DoubleCoset.mk (ratPoints H) (KA H) (α i) =
      DoubleCoset.mk (ratPoints H) (KA H) (α j) → i = j)
    (hfin : ∀ i, Finite (ratPoints H ⊓ conjSub (α i) (KA H) : Subgroup (OA H)))
    (f : OA H → ℂ) (hf : Integrable f (haarOA H hH)) :
    dosetIntegral (ratPoints H) (KA H) (haarOA H hH) α (fun g => ∑' γ : ratPoints H, f (γ * g)) =
      ∫ g, f g ∂haarOA H hH :=
  weil_dosetIntegral (isOpen_KA H).measurableSet α hcov hdisj hfin f hf

end QuadFormsKB.AWS
