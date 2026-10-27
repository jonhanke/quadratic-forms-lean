import QuadFormsKB.Tamagawa.Measure.Weil.GnatBaseChange
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamSOCorollaries
import QuadFormsKB.Tamagawa.RankFourFromTau

/-!
# Reduction to a named input: $\tau(SO_4) = 2$ and `RankFourUnitSiegel F` from Weil's measure comparison for $G^\natural$


**Layer:** $F$ a number field (totally real for the lattice corollaries), quaternary forms over $\mathcal O_F$, `muTam`,
The quotient measures (`GnatSquare.lean`, `GnatBaseChange.lean`).

The covolume theorems proved $\operatorname{vol}(P(F)\backslash P(\mathbb A),\mu_P) = 2$ for $P = G^\natural/\mathbb G_m$ with Weil's quotient measure, in both
discriminant cases (`covolume_gnatSq`, `covolume_gnatBC`). The remaining step is the identification of $(P,\pi(\Gamma),\mu_P)$ with
$(SO(V)(\mathbb A), SO(V)(F), \mu_{\mathrm{Tam}})$. It is **not** proved here; it is the named input

* **`GnatTamagawaComparison F`**: for the two explicit models, the norm forms
  $q_{\mathrm{sq}}(a,b) = \langle1,-a,-b,ab\rangle$ ($E = F\times F$, $V = (D,\operatorname{nrd})$, `qSq`) and
  $q_{\mathrm{ns}}(a,b,d) = \langle1,-ad,-bd,abd\rangle$ ($E = K = F(\sqrt d)$, $V = V_0\subset D_E$, `qNS`; `V0Form` with integral
  coefficients), there is an isomorphism of topological groups $\Phi : P\cong SO(V)(\mathbb A)$ carrying $\pi(\Gamma)$ onto $SO(V)(F)$ and
  $\mu_P$ onto `muTam`. Its content is (i) the adelic form of the $SO(V)\cong G^\natural/\mathbb G_m$ (`pdAdeleEquiv` analogue:
  continuity, integrality at almost all places, open mapping) and (ii) Weil's Thm 2.3.1 for the isogeny-free quotient
  $G^\natural\to SO(V)$: local ratios $r_v$ of the two Haar measures with $\prod_v r_v = 1$ (the generic transport
  `covolume_eq_of_localFactors`). It mentions no Tamagawa number, no covolume and no Siegel formula, so it is not equivalent to
  any conclusion below; it holds for every quaternion algebra (split or not) and every $d$.

From it, with `covolume_gnatSq`, `covolume_gnatBC` (no Fujisaki, no zeta function of $D$, no CFT):
* `tamagawaNumberTwoAdelic_qSq`, `tamagawaNumberTwoAdelic_qNS`: Weil's adelic $\tau(SO(V)) = 2$ for the two model forms (division $D$);
* **`quaternaryTamagawaTwo_of_gnatComparison`** ($F$ totally real, any class number): $\tau(SO_4) = 2$ for every totally positive definite
  quaternary form over $\mathcal O_F$ (`TamagawaNumberTwo`); every such form is, up to change of lattice, a model form
  (with integral scaling; for non-square $d$ the field $K = F[X]/(X^2-d)$ is constructed, `quadFieldOf`);
* **`rankFourUnitSiegel_of_gnatComparison`**: `RankFourUnitSiegel F` (route 2: `rankFourUnitSiegel_of_quaternary`);
* consumers: `tamagawaNumberTwo_all_ranks_of_gnatComparison`, `massFormula_all_ranks_of_gnatComparison`,
  `siegelFormulaAt_all_ranks_of_gnatComparison`, `tamagawaNumberTwoAdelic_quaternary_of_gnatComparison`.
-/

open MeasureTheory Measure Set Function Topology NumberField NumberField.InfinitePlace Matrix
open scoped ENNReal NNReal Quaternion ComplexOrder

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.HilbertModular

noncomputable section

variable {F : Type} [Field F] [NumberField F]

/-! ### The model forms and the input -/

/-- The norm form $\langle1,-a,-b,ab\rangle$ of the standard order of $\mathbb H[F,a,b]$ (square discriminant). -/
def qSq (a b : 𝓞 F) : QuadForm (𝓞 F) 4 := QuadForm.diag ![1, -a, -b, a * b]

/-- The $V_0$-form $\langle1,-ad,-bd,abd\rangle$ with integral coefficients (discriminant $d$ up to squares). -/
def qNS (a b d : 𝓞 F) : QuadForm (𝓞 F) 4 := QuadForm.diag ![1, -(a * d), -(b * d), a * b * d]

variable (F) in
/-- **Input (named): Weil's measure comparison for $G^\natural\to SO(V)$, $m = 4$** (Weil 1982, Thm 2.3.1 and §3.7, pp. 64–65
[unverified page]).

Fields:
- `square`: for $a, b\in\mathcal O_F\setminus0$ ($D = \mathbb H[F,a,b]$, $E = F\times F$) and the norm form `qSq a b`: an isomorphism
  $\Phi : P\cong SO(\langle1,-a,-b,ab\rangle)(\mathbb A)$ of topological groups with $\Phi(\pi(\Gamma)) = SO(F)$ and $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$;
- `nonsquare`: for $a, b, d\in\mathcal O_F\setminus0$, every number field $K\supseteq F$ with an $F$-basis $(1,\delta)$, $\delta^2 = d$, and
  $\alpha = a$, $\beta = b$ in $\mathcal O_K$ ($D' = \mathbb H[K,a,b] = D_E$): the same for `gnatBCO` and `qNS a b d`.

*Hypothesis hygiene.* A statement about two explicit Haar measures on two explicit groups (local ratios and the adelic
isomorphism); no covolume, Tamagawa number or representation number occurs. Not equivalent to `TamagawaNumberTwoAdelic`,
`QuaternaryTamagawaTwo` or `RankFourUnitSiegel`, which are derived from it together with the proved covolume $2$. -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, ∏ r_v = 1) and §3.7, pp. 64-65 (SO_4 via G^♮) [unverified page]"]
structure GnatTamagawaComparison : Prop where
  square : ∀ (a b : 𝓞 F) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hQ : (qSq a b).Nondegenerate),
    ∃ Φ : (gnatSqO ha0 hb0).P ≃ₜ* SOAdele (qSq a b),
      (gnatSqO ha0 hb0).gamP.map Φ.toMulEquiv.toMonoidHom = GammaSOAdele (qSq a b) ∧
      ((gnatSqO ha0 hb0).muP (muSq ha0 hb0)).map Φ = muTam (qSq a b) hQ (fun _ => 1)
  nonsquare : ∀ (a b d : 𝓞 F) (K : Type) [Field K] [NumberField K] [Algebra F K]
    (bK : Module.Basis (Fin 2) F K) (hb₀ : bK 0 = 1) (_hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
    (α β : 𝓞 K) (_hα : (α : K) = algebraMap F K (a : F)) (_hβ : (β : K) = algebraMap F K (b : F))
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (hQ : (qNS a b d).Nondegenerate),
    ∃ Φ : (gnatBCO bK 0 hb₀ hα0 hβ0).P ≃ₜ* SOAdele (qNS a b d),
      (gnatBCO bK 0 hb₀ hα0 hβ0).gamP.map Φ.toMulEquiv.toMonoidHom = GammaSOAdele (qNS a b d) ∧
      ((gnatBCO bK 0 hb₀ hα0 hβ0).muP (muBC bK 0 hb₀ hα0 hβ0)).map Φ = muTam (qNS a b d) hQ (fun _ => 1)

/-! ### Weil's adelic $\tau = 2$ for the model forms -/

/-- Transport of the covolume along a measure-preserving isomorphism matching the lattices. -/
theorem covolume_eq_of_continuousMulEquiv {G G' : Type*} [Group G] [Group G'] [TopologicalSpace G]
    [TopologicalSpace G'] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G']
    [MeasurableMul G] [MeasurableMul G']
    (Γ : Subgroup G) (Γ' : Subgroup G') [Countable Γ] (Φ : G ≃ₜ* G') (hΓ : Γ.map Φ.toMulEquiv.toMonoidHom = Γ')
    (μ : Measure G) (μ' : Measure G') [μ.IsMulLeftInvariant] [μ'.IsMulLeftInvariant] (hμ : μ.map Φ = μ') :
    covolume Γ' G' μ' = covolume Γ G μ :=
  (covolume_eq_of_map Γ Γ' Φ.toMulEquiv Φ.continuous.measurable Φ.symm.continuous.measurable hΓ μ μ' hμ).symm

/-- **Weil's adelic $\tau(SO(\langle1,-a,-b,ab\rangle)) = 2$** for a quaternion division algebra $\mathbb H[F,a,b]$, given the input. -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65; Thm 2.3.1"]
theorem tamagawaNumberTwoAdelic_qSq (hC : GnatTamagawaComparison F) {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ) (hQ : (qSq a b).Nondegenerate) :
    TamagawaNumberTwoAdelic (qSq a b) hQ := by
  obtain ⟨Φ, hΓ, hμ⟩ := hC.square a b ha0 hb0 hQ
  have := (gnatSqO ha0 hb0).isHaarMeasure_muP (muSq ha0 hb0)
  unfold TamagawaNumberTwoAdelic
  rw [covolume_eq_of_continuousMulEquiv _ _ Φ hΓ _ _ hμ, covolume_gnatSq ha0 hb0 hdiv]

/-- **Weil's adelic $\tau(SO(\langle1,-ad,-bd,abd\rangle)) = 2$** for $K = F(\sqrt d)$ and a quaternion division algebra
$\mathbb H[K,a,b]$, given the input. -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65; Thm 2.3.1"]
theorem tamagawaNumberTwoAdelic_qNS (hC : GnatTamagawaComparison F) {a b d : 𝓞 F} {K : Type} [Field K]
    [NumberField K] [Algebra F K] (bK : Module.Basis (Fin 2) F K) (hb₀ : bK 0 = 1)
    (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F)) {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F))
    (hβ : (β : K) = algebraMap F K (b : F)) (hα0 : α ≠ 0) (hβ0 : β ≠ 0)
    (hdiv : ∀ ξ : ℍ[K,(α : K),(β : K)], ξ ≠ 0 → IsUnit ξ) (hQ : (qNS a b d).Nondegenerate) :
    TamagawaNumberTwoAdelic (qNS a b d) hQ := by
  obtain ⟨Φ, hΓ, hμ⟩ := hC.nonsquare a b d K bK hb₀ hb₁ α β hα hβ hα0 hβ0 hQ
  have := (gnatBCO bK 0 hb₀ hα0 hβ0).isHaarMeasure_muP (muBC bK 0 hb₀ hα0 hβ0)
  unfold TamagawaNumberTwoAdelic
  rw [covolume_eq_of_continuousMulEquiv _ _ Φ hΓ _ _ hμ, covolume_gnatBC bK 0 hb₀ hα0 hβ0 hdiv]

/-! ### Positivity bookkeeping -/

theorem emb_pos_of_isTotallyPos {x : F} (h : IsTotallyPos x) (w : InfinitePlace F) (hw : w.IsReal) :
    0 < embedding_of_isReal hw x := by
  have h1 := h w.embedding.toRatAlgHom
  have h2 : (w.embedding.toRatAlgHom x : ℂ) = ((embedding_of_isReal hw x : ℝ) : ℂ) :=
    (embedding_of_isReal_apply hw x).symm
  rw [h2] at h1
  exact_mod_cast h1

theorem emb_neg_of_isTotallyPos_neg {x : F} (h : IsTotallyPos (-x)) (w : InfinitePlace F) (hw : w.IsReal) :
    embedding_of_isReal hw x < 0 := by
  have := emb_pos_of_isTotallyPos h w hw
  rw [map_neg] at this; linarith

/-- The real embedding of $K$ at $w$ restricted to $F$ is the real embedding at $w|_F$. -/
theorem embedding_of_isReal_algebraMap {K : Type} [Field K] [Algebra F K] (w : InfinitePlace K) (hw : w.IsReal)
    (x : F) : embedding_of_isReal hw (algebraMap F K x) =
      embedding_of_isReal (IsReal.comap (algebraMap F K) hw) x := by
  apply Complex.ofReal_injective
  rw [embedding_of_isReal_apply, embedding_of_isReal_apply,
    comap_embedding_of_isReal (algebraMap F K) (IsReal.comap (algebraMap F K) hw)]
  rfl

/-- Entries of a totally positive definite diagonal form are totally positive. -/
theorem isTotallyPos_of_diag {n : ℕ} {e : Fin n → 𝓞 F} (hpd : IsTotallyPosDef (formF (QuadForm.diag e)))
    (i : Fin n) : IsTotallyPos (e i : F) := by
  have := hpd (Pi.single i 1) (by simp)
  rw [LatChange.eval_single'] at this
  simpa [QuadForm.map, QuadForm.diag] using this

/-- $\langle e_i\rangle\circ\operatorname{diag}(c_i) = \langle c_i^2e_i\rangle$. -/
theorem diag_compMat_diagonal {n : ℕ} {A : Type*} [CommRing A] (e c : Fin n → A) :
    (QuadForm.diag e).compMat (diagonal c) = QuadForm.diag fun i => c i * c i * e i := by
  ext i j
  rw [LatChange.compMat_diagonal_coeff]
  by_cases hij : i = j
  · subst hij; simp [QuadForm.diag]
  · simp [QuadForm.diag, diagonal_apply_ne _ hij]

theorem tamagawaNumberTwo_of_compMat {Q₀ : QuadForm (𝓞 F) 4} (hQ₀ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (formF Q₀)) {G : Matrix (Fin 4) (Fin 4) (𝓞 F)} (hG : G.det ≠ 0)
    (h : TamagawaNumberTwo (Q₀.compMat G)) : TamagawaNumberTwo Q₀ := by
  unfold TamagawaNumberTwo at h ⊢
  rwa [LatChange.tauSO_compMat_nf (by norm_num) (by norm_num) Q₀ hQ₀ hpd G hG] at h

/-! ### The quadratic field $F(\sqrt d)$ -/

section QuadField

variable (d : F) (hd : ∀ t : F, t ^ 2 ≠ d)

/-- $X^2 - d$. -/
abbrev quadPoly : Polynomial F := Polynomial.X ^ 2 - Polynomial.C d

include hd in
theorem irreducible_quadPoly : Irreducible (quadPoly d) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two hd

/-- $K = F[X]/(X^2 - d)$. -/
abbrev quadFieldOf : Type := AdjoinRoot (quadPoly d)

include hd in
theorem fact_irreducible_quadPoly : Fact (Irreducible (quadPoly d)) := ⟨irreducible_quadPoly d hd⟩

theorem quadPoly_ne_zero : quadPoly d ≠ 0 := Polynomial.X_pow_sub_C_ne_zero two_pos d

theorem natDegree_quadPoly : (quadPoly d).natDegree = 2 := Polynomial.natDegree_X_pow_sub_C

/-- The basis $(1,\sqrt d)$ of $F(\sqrt d)$ over $F$. -/
def quadBasis : Module.Basis (Fin 2) F (quadFieldOf d) :=
  (AdjoinRoot.powerBasis (quadPoly_ne_zero d)).basis.reindex (finCongr (natDegree_quadPoly d))

theorem quadBasis_apply (i : Fin 2) : quadBasis d i = AdjoinRoot.root (quadPoly d) ^ (i : ℕ) := by
  rw [quadBasis, Module.Basis.reindex_apply, PowerBasis.coe_basis]
  rfl

theorem quadBasis_zero : quadBasis d 0 = 1 := by rw [quadBasis_apply]; rfl

theorem root_sq : AdjoinRoot.root (quadPoly d) * AdjoinRoot.root (quadPoly d) =
    algebraMap F (quadFieldOf d) d := by
  have h := AdjoinRoot.eval₂_root (quadPoly d)
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
  rw [← sq, sub_eq_zero.1 h]; rfl

theorem quadBasis_one_sq : quadBasis d 1 * quadBasis d 1 = algebraMap F (quadFieldOf d) d := by
  simp only [quadBasis_apply, Fin.val_one, pow_one]; exact root_sq d

include hd in
theorem numberField_quadFieldOf : @NumberField (quadFieldOf d) (@AdjoinRoot.instField F _ _ (fact_irreducible_quadPoly d hd)) := by
  let := fact_irreducible_quadPoly d hd
  have : Module.Finite F (quadFieldOf d) := (AdjoinRoot.powerBasis (quadPoly_ne_zero d)).finite
  exact NumberField.of_module_finite F (quadFieldOf d)

end QuadField

section QuadFieldReal

variable (d : F) [Fact (Irreducible (quadPoly d))]

/-- A complex number whose square is real and positive is real. -/
theorem im_eq_zero_of_sq_pos {z : ℂ} (h : 0 < z ^ 2) : z.im = 0 := by
  rw [Complex.lt_def] at h
  obtain ⟨hre, him⟩ := h
  simp only [Complex.zero_re, Complex.zero_im, sq, Complex.mul_re, Complex.mul_im] at hre him
  have h1 : z.re * z.im = 0 := by linarith
  rcases mul_eq_zero.1 h1 with h0 | h0
  · rw [h0] at hre; nlinarith [sq_nonneg z.im]
  · exact h0

/-- **$F(\sqrt d)$ is totally real** for $F$ totally real and $d$ totally positive. -/
theorem isTotallyReal_quadFieldOf [IsTotallyReal F] (hdpos : IsTotallyPos d) : IsTotallyReal (quadFieldOf d) := by
  refine ⟨fun w => ?_⟩
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  set φ := w.embedding
  set σ : F →+* ℂ := φ.comp (algebraMap F (quadFieldOf d))
  have hσ : ComplexEmbedding.conjugate σ = σ :=
    ComplexEmbedding.isReal_iff.mp (NumberField.IsTotallyReal.complexEmbedding_isReal σ)
  have hroot : (starRingEnd ℂ) (φ (AdjoinRoot.root (quadPoly d))) = φ (AdjoinRoot.root (quadPoly d)) := by
    have hsq : φ (AdjoinRoot.root (quadPoly d)) ^ 2 = σ d := by
      rw [sq, ← map_mul, root_sq]; rfl
    have hpos : 0 < σ d := hdpos σ.toRatAlgHom
    rw [← hsq] at hpos
    exact Complex.conj_eq_iff_im.2 (im_eq_zero_of_sq_pos hpos)
  have hext : ((starRingEnd ℂ).comp φ).comp (AdjoinRoot.mk (quadPoly d)) = φ.comp (AdjoinRoot.mk (quadPoly d)) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · have := congrArg (fun ψ : F →+* ℂ => ψ c) hσ
      simp only [ComplexEmbedding.conjugate_coe_eq] at this
      simpa [σ] using this
    · simpa using hroot
  refine RingHom.ext fun x => ?_
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  have := congrArg (fun ψ : Polynomial F →+* ℂ => ψ p) hext
  simpa [ComplexEmbedding.conjugate_coe_eq] using this

end QuadFieldReal

/-! ### $\tau(SO_4) = 2$ and `RankFourUnitSiegel F` from the input -/

section Reduction

open QuadForm LatChange

variable [IsTotallyReal F]

theorem tamagawaNumberTwo_compMat_of {Q₀ : QuadForm (𝓞 F) 4} (hQ₀ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (formF Q₀)) {G : Matrix (Fin 4) (Fin 4) (𝓞 F)} (hG : G.det ≠ 0)
    (h : TamagawaNumberTwo Q₀) : TamagawaNumberTwo (Q₀.compMat G) := by
  unfold TamagawaNumberTwo at h ⊢
  rwa [LatChange.tauSO_compMat_nf (by norm_num) (by norm_num) Q₀ hQ₀ hpd G hG]

theorem det_map_algebraMap_ne_zero_gnat {G : Matrix (Fin 4) (Fin 4) (𝓞 F)} (hG : G.det ≠ 0) :
    (G.map (algebraMap (𝓞 F) F)).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hG

/-- **$\tau(SO_4) = 2$ over every totally real field (any class number), given Weil's measure comparison for $G^\natural$**:
`GnatTamagawaComparison F → QuaternaryTamagawaTwo F`.

*Proof.* By `quaternaryTamagawaTwo_of_diag_nf` it suffices to treat $\langle1,b_1,b_2,b_3\rangle$ ($b_i\gg0$). With
$a = -b_2b_3$, $b = -b_1b_3$, $d = b_1b_2b_3$ (scaled by squares), $\langle1,b_1,b_2,b_3\rangle\circ\operatorname{diag}(1,b_2b_3,b_1b_3,b_1b_2b_3)
= \langle1,-ad,-bd,abd\rangle$ (`qNS`), and $\tau$ is invariant under change of lattice (`tauSO_compMat_nf`). If $d = t^2$ then
$\langle1,-ad,-bd,abd\rangle = \langle1,-a,-b,ab\rangle\circ\operatorname{diag}(1,t,t,t)$ and `tamagawaNumberTwoAdelic_qSq` applies ($D = (a,b)_F$ totally
definite, hence division); otherwise $K = F(\sqrt d)$ is a totally real number field (`isTotallyReal_quadFieldOf`), $D' = (a,b)_K$ is
totally definite and `tamagawaNumberTwoAdelic_qNS` applies. Finally `tamagawaNumberTwoAdelic_iff` (definite case). -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65"]
theorem quaternaryTamagawaTwo_of_gnatComparison (hC : GnatTamagawaComparison F) : QuaternaryTamagawaTwo F := by
  refine quaternaryTamagawaTwo_of_diag_nf fun c hc hpd => ?_
  set e : Fin 4 → 𝓞 F := Fin.cons 1 c
  have hpos : ∀ i, IsTotallyPos (e i : F) := isTotallyPos_of_diag hpd
  have hp1 : IsTotallyPos (c 0 : F) := hpos 1
  have hp2 : IsTotallyPos (c 1 : F) := hpos 2
  have hp3 : IsTotallyPos (c 2 : F) := hpos 3
  set a' : 𝓞 F := -(c 2 * c 1)
  set b' : 𝓞 F := -(c 2 * c 0)
  set d' : 𝓞 F := c 0 * c 1 * c 2
  have hna : IsTotallyPos (-(a' : F)) := by
    have : (-(a' : F)) = (c 2 : F) * c 1 := by simp only [a']; push_cast; ring
    rw [this]; exact isTotallyPos_mul hp3 hp2
  have hnb : IsTotallyPos (-(b' : F)) := by
    have : (-(b' : F)) = (c 2 : F) * c 0 := by simp only [b']; push_cast; ring
    rw [this]; exact isTotallyPos_mul hp3 hp1
  have hdpos : IsTotallyPos (d' : F) := by
    have : (d' : F) = (c 0 : F) * c 1 * c 2 := by simp only [d']; push_cast; ring
    rw [this]; exact isTotallyPos_mul (isTotallyPos_mul hp1 hp2) hp3
  have ha0 : a' ≠ 0 := neg_ne_zero.2 (mul_ne_zero (hc 2) (hc 1))
  have hb0 : b' ≠ 0 := neg_ne_zero.2 (mul_ne_zero (hc 2) (hc 0))
  -- the change of lattice to `qNS a' b' d'`
  set G : Matrix (Fin 4) (Fin 4) (𝓞 F) := diagonal ![1, c 1 * c 2, c 0 * c 2, c 0 * c 1 * c 2]
  have hG : G.det ≠ 0 := by
    rw [det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    fin_cases i <;> simp [hc 0, hc 1, hc 2]
  have hqG : (QuadForm.diag e).compMat G = qNS a' b' d' := by
    rw [diag_compMat_diagonal, qNS]
    congr 1
    funext i
    have h1 : (Fin.cons 1 c : Fin 4 → 𝓞 F) 1 = c 0 := rfl
    have h2 : (Fin.cons 1 c : Fin 4 → 𝓞 F) 2 = c 1 := rfl
    have h3 : (Fin.cons 1 c : Fin 4 → 𝓞 F) 3 = c 2 := rfl
    fin_cases i <;> simp [e, a', b', d', h1, h2, h3] <;> ring
  have hQe : (QuadForm.diag e).Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hQns : (qNS a' b' d').Nondegenerate := hqG ▸ nondegenerate_compMat_of_det hQe hG
  have hpdns : IsTotallyPosDef (formF (qNS a' b' d')) := by
    rw [← hqG, formF, ← map_compMat]
    exact isTotallyPosDef_compMat_of_det hpd (det_map_algebraMap_ne_zero_gnat hG)
  apply tamagawaNumberTwo_of_compMat hQe hpd hG
  rw [hqG]
  by_cases hsq : ∃ t : F, t ^ 2 = (d' : F)
  · -- square discriminant: `qNS a' b' d' = qSq a' b' ∘ diag(1,t,t,t)`
    obtain ⟨t, ht⟩ := hsq
    have hti : IsIntegral ℤ t := IsIntegral.of_pow two_pos (by rw [ht]; exact d'.isIntegral_coe)
    set t' : 𝓞 F := ⟨t, hti⟩
    have ht' : t' * t' = d' := RingOfIntegers.coe_injective (by
      change t * t = (d' : F); rw [← ht, sq])
    set H : Matrix (Fin 4) (Fin 4) (𝓞 F) := diagonal ![1, t', t', t']
    have ht0 : t' ≠ 0 := by
      intro h0; rw [h0, mul_zero] at ht'
      exact (mul_ne_zero (mul_ne_zero (hc 0) (hc 1)) (hc 2)) ht'.symm
    have hH : H.det ≠ 0 := by
      rw [det_diagonal]
      refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      fin_cases i <;> simp [ht0]
    have hqH : (qSq a' b').compMat H = qNS a' b' d' := by
      rw [qSq, diag_compMat_diagonal, qNS]
      congr 1
      funext i
      fin_cases i <;> simp <;> rw [← ht'] <;> ring
    have hpdsq : IsTotallyPosDef (formF (qSq a' b')) := by
      rw [← hqH, formF, ← map_compMat] at hpdns
      exact isTotallyPosDef_of_compMat (det_map_algebraMap_ne_zero_gnat hH) hpdns
    have hQsq : (qSq a' b').Nondegenerate := nondegenerate_of_map hpdsq.nondegenerate
    rw [← hqH]
    refine tamagawaNumberTwo_compMat_of hQsq hpdsq hH ?_
    have hdiv := hdiv_of_totallyNeg (F := F) (a := (a' : F)) (b := (b' : F))
      (fun w hw => emb_neg_of_isTotallyPos_neg hna w hw) (fun w hw => emb_neg_of_isTotallyPos_neg hnb w hw)
    exact (tamagawaNumberTwoAdelic_iff (qSq a' b') hQsq (by norm_num) hpdsq (isIntegral_std _)).1
      (tamagawaNumberTwoAdelic_qSq hC ha0 hb0 hdiv hQsq)
  · -- non-square discriminant: `K = F(√d')`
    push_neg at hsq
    have := fact_irreducible_quadPoly (d' : F) hsq
    have := numberField_quadFieldOf (d' : F) hsq
    have := isTotallyReal_quadFieldOf (d' : F) hdpos
    set K := quadFieldOf (d' : F)
    have hαi : IsIntegral ℤ (algebraMap F K (a' : F)) := a'.isIntegral_coe.algebraMap
    have hβi : IsIntegral ℤ (algebraMap F K (b' : F)) := b'.isIntegral_coe.algebraMap
    set α : 𝓞 K := ⟨algebraMap F K (a' : F), hαi⟩
    set β : 𝓞 K := ⟨algebraMap F K (b' : F), hβi⟩
    have hα0 : α ≠ 0 := fun h => ha0 (RingOfIntegers.coe_injective (by
      have h' : algebraMap F K (a' : F) = 0 := congrArg Subtype.val h
      rw [map_eq_zero] at h'; simpa using h'))
    have hβ0 : β ≠ 0 := fun h => hb0 (RingOfIntegers.coe_injective (by
      have h' : algebraMap F K (b' : F) = 0 := congrArg Subtype.val h
      rw [map_eq_zero] at h'; simpa using h'))
    have hdiv : ∀ ξ : ℍ[K,(α : K),(β : K)], ξ ≠ 0 → IsUnit ξ := by
      refine hdiv_of_totallyNeg (fun w hw => ?_) (fun w hw => ?_)
      · change embedding_of_isReal hw (algebraMap F K (a' : F)) < 0
        rw [embedding_of_isReal_algebraMap]; exact emb_neg_of_isTotallyPos_neg hna _ _
      · change embedding_of_isReal hw (algebraMap F K (b' : F)) < 0
        rw [embedding_of_isReal_algebraMap]; exact emb_neg_of_isTotallyPos_neg hnb _ _
    exact (tamagawaNumberTwoAdelic_iff (qNS a' b' d') hQns (by norm_num) hpdns (isIntegral_std _)).1
      (tamagawaNumberTwoAdelic_qNS hC (quadBasis (d' : F)) (quadBasis_zero _) (quadBasis_one_sq _)
        (α := α) (β := β) rfl rfl hα0 hβ0 hdiv hQns)

/-- **`RankFourUnitSiegel F` for every totally real field (any class number), given Weil's measure comparison for $G^\natural$**
(route 2: $\tau(SO_4) = 2$ ⇒ rank-4 Siegel, `rankFourUnitSiegel_of_quaternary`). -/
@[kb "weil1982" "§4.5, p. 100 (Siegel from τ = 2); §3.7, Thm 3.7.1 (m = 4)"]
theorem rankFourUnitSiegel_of_gnatComparison (hC : GnatTamagawaComparison F) : RankFourUnitSiegel F :=
  rankFourUnitSiegel_of_quaternary (quaternaryTamagawaTwo_of_gnatComparison hC)

/-- **$\tau = 2$ in every rank $N\ge4$ over every totally real field**, given `GnatTamagawaComparison F`. -/
@[kb "weil1982" "Thm 3.7.1, Thm 4.5.1, p. 109; any class number, given the measure comparison"]
theorem tamagawaNumberTwo_all_ranks_of_gnatComparison (hC : GnatTamagawaComparison F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_all_ranks_nf (rankFourUnitSiegel_of_gnatComparison hC) hN Q₀ hpd

/-- **The mass formula in every rank $N\ge4$ over every totally real field**, given `GnatTamagawaComparison F`. -/
@[kb "weil1982" "Thm 4.5.1, p. 109; any class number, given the measure comparison"]
theorem massFormula_all_ranks_of_gnatComparison (hC : GnatTamagawaComparison F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : MassFormulaHolds Q₀ :=
  massFormula_all_ranks_nf (rankFourUnitSiegel_of_gnatComparison hC) hN Q₀ hpd

/-- **Siegel's formula for numbers in every rank $N\ge5$ over every totally real field**, given `GnatTamagawaComparison F`. -/
@[kb "weil1982" "§4.5, p. 100; Thm 4.5.1, p. 109; any class number, given the measure comparison"]
theorem siegelFormulaAt_all_ranks_of_gnatComparison (hC : GnatTamagawaComparison F) {n : ℕ} (hn : 4 ≤ n)
    (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v, 0 < HilbertModular.realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_all_ranks_nf (rankFourUnitSiegel_of_gnatComparison hC) hn Q₀ hpd hm

/-- **Weil's adelic $\tau(SO(V)) = 2$ for every totally positive definite quaternary form over every totally real field**, given
`GnatTamagawaComparison F`. -/
@[kb "weil1982" "Thm 3.7.1 (m = 4), p. 65; §2.4, p. 23; given the measure comparison"]
theorem tamagawaNumberTwoAdelic_quaternary_of_gnatComparison (hC : GnatTamagawaComparison F)
    (Q₀ : QuadForm (𝓞 F) 4) (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (formF Q₀)) :
    TamagawaNumberTwoAdelic Q₀ hQ :=
  (tamagawaNumberTwoAdelic_iff Q₀ hQ (by norm_num) hpd (LatChange.isIntegral_std Q₀)).2
    ((quaternaryTamagawaTwo_of_gnatComparison hC).tau_eq_two Q₀ hpd)

end Reduction

end

end QuadFormsKB.Tamagawa.Measure.Weil
