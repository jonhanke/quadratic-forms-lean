/-
# O'Meara 1973, Example 102:10 (i): the idèle condition over $\mathbb Q$

**Layer:** idèles of a number field $F$ and the spinor norm group $D = \theta(O^+(V))$.

**Proves**
* `exists_principal_mul_unitIdele`: if $\mathcal o_F$ is a PID then $J_F = P_F J_F^S$ for $S$ = all finite spots;
* `spinorNormGroup_eq_top_of_isotropic_real`: for $n \ge 3$, if $V_w$ is isotropic at every real place then $D = F^\times$;
* `idele_condition_rat`: over $F = \mathbb Q$, for a regular indefinite $V$ with $\dim V \ge 3$, $J_F = P_D J_F^S$
  with $S$ all finite spots (the hypothesis of 104:9).
-/
import QuadFormsKB.Literature.OMeara.Sec102To104
import QuadFormsKB.Literature.OMeara.Sec101BD
import QuadFormsKB.Lattices.SpinorGlobal

open NumberField IsDedekindDomain Matrix WithZero QuadFormsKB.OMeara

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **$J_F = P_F J_F^S$ when the class number is one** (O'Meara 1973, §102B, Example 102:10 (i), p. 304; cf. §65A):
if $\mathfrak o_F$ is a principal ideal domain, then for $S$ the set of all finite spots every idèle
`i` $\in J_F$ is $i = (\alpha)\,j$ with $\alpha \in F^\times$ (`IdeleGroup.unitEmbedding`, the principal idèle) and
$j \in J_F^S$ (`sIdeles Set.univ`: $\lvert j_\mathfrak p\rvert_\mathfrak p = 1$ at every finite spot $\mathfrak p$).
The hypothesis `[IsPrincipalIdealRing (𝓞 F)]` says every ideal of $\mathfrak o_F$ is principal. *Proof:* $i$ has
$\lvert i_\mathfrak p\rvert \ne 1$ at finitely many $\mathfrak p$; take $\alpha = \prod \pi_\mathfrak p^{\operatorname{ord}_\mathfrak p i_\mathfrak p}$
with $\pi_\mathfrak p$ a generator of $\mathfrak p$. -/
@[kb "omeara1963" "§102B, 102:10 (i), p. 304 (J_F = P_F J_F^S when the class number is 1)"]
theorem exists_principal_mul_unitIdele [IsPrincipalIdealRing (𝓞 F)] (i : IdeleGroup (𝓞 F) F) :
    ∃ α : Fˣ, ∃ j ∈ OMeara.sIdeles (Set.univ : Set (HeightOneSpectrum (𝓞 F))),
      i = IdeleGroup.unitEmbedding (𝓞 F) F α * j := by
  classical
  have hne : ∀ v, ideleAt i v ≠ 0 := fun v h => by
    have : ideleAt (i * i⁻¹) v = 1 := by rw [mul_inv_cancel]; rfl
    rw [ideleAt_mul, ideleAt_inv, h, zero_mul] at this
    exact zero_ne_one this
  have hfin : {v | Valued.v (ideleAt i v) ≠ 1}.Finite := by
    have h1 := (i : AdeleRing (𝓞 F) F).2.eventually
    have h2 := ((i⁻¹ : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F).2.eventually
    refine Filter.eventually_cofinite.mp ?_
    filter_upwards [h1, h2] with v hv1 hv2
    have ha : Valued.v (ideleAt i v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hv1
    have hb : Valued.v (ideleAt i⁻¹ v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hv2
    have hmul : Valued.v (ideleAt i v) * Valued.v (ideleAt i⁻¹ v) = 1 := by
      rw [← map_mul, ← ideleAt_mul, mul_inv_cancel, ideleAt_one, map_one]
    refine le_antisymm ha ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := hmul.symm
      _ ≤ Valued.v (ideleAt i v) * 1 := mul_le_mul' le_rfl hb
      _ = _ := mul_one _
  set S := hfin.toFinset
  let m : HeightOneSpectrum (𝓞 F) → ℤ := fun v => log (Valued.v (ideleAt i v))
  have hm : ∀ v, Valued.v (ideleAt i v) = exp (m v) := fun v =>
    (exp_log ((map_ne_zero _).mpr (hne v))).symm
  have hm0 : ∀ v ∉ S, m v = 0 := by
    intro v hv
    have : Valued.v (ideleAt i v) = 1 := by simpa [S] using hv
    simp only [m, this, log_one]
  let p : HeightOneSpectrum (𝓞 F) → ℕ := fun v => (-m v).toNat
  let q : HeightOneSpectrum (𝓞 F) → ℕ := fun v => (m v).toNat
  set a₀ : 𝓞 F := ∏ w ∈ S, primeGen w ^ p w
  set b₀ : 𝓞 F := ∏ w ∈ S, primeGen w ^ q w
  have ha₀ : a₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (primeGen_ne_zero w)
  have hb₀ : b₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (primeGen_ne_zero w)
  have hfa : algebraMap (𝓞 F) F a₀ ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr ha₀
  have hfb : algebraMap (𝓞 F) F b₀ ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hb₀
  let α : Fˣ := Units.mk0 (algebraMap (𝓞 F) F a₀ / algebraMap (𝓞 F) F b₀) (div_ne_zero hfa hfb)
  have hkey : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap F (v.adicCompletion F) (α : F)) = exp (m v) := by
    intro v
    show Valued.v (algebraMap F (v.adicCompletion F)
      (algebraMap (𝓞 F) F a₀ / algebraMap (𝓞 F) F b₀)) = _
    rw [map_div₀, map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    by_cases hv : v ∈ S
    · rw [valued_prod_primeGen_of_mem v p hv, valued_prod_primeGen_of_mem v q hv, ← exp_sub]
      congr 1
      simp only [p, q]
      omega
    · rw [valued_prod_primeGen_of_not_mem v p hv, valued_prod_primeGen_of_not_mem v q hv, hm0 v hv]
      simp
  refine ⟨α, (IdeleGroup.unitEmbedding (𝓞 F) F α)⁻¹ * i, fun v _ => ?_, by simp⟩
  rw [ideleAt_mul, ideleAt_inv, map_mul, map_inv₀]
  have h : ideleAt (IdeleGroup.unitEmbedding (𝓞 F) F α) v = algebraMap F (v.adicCompletion F) (α : F) := rfl
  rw [h, hkey, hm]
  exact inv_mul_cancel₀ exp_ne_zero

/-- **$D = F^\times$ when $V$ is isotropic at all real places** (O'Meara 1973, §101B, 101:8, p. 291, in the case with
no anisotropic real place): for $Q$ nondegenerate in $n \ge 3$ variables, if $Q$ is isotropic over $F_w$ at every real
place $w$ of $F$ (`h`), then the spinor norm group $D = \theta(O^+(V))$ (`spinorNormGroup Q hQ`) is all of
$F^\times$. -/
@[kb "omeara1963" "§101B, 101:8, p. 291 (D = F^× if V is isotropic at all real spots)"]
theorem spinorNormGroup_eq_top_of_isotropic_real (Q : QuadForm F n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (h : ∀ w : InfinitePlace F, w.IsReal → Q.IsotropicIn w.Completion) :
    spinorNormGroup Q hQ = ⊤ := by
  rw [spinorNormGroup_eq_posAtAnisoReal Q hQ hn, eq_top_iff]
  intro α _ w hw hi
  exact absurd (h w hw) hi

/-- **O'Meara 1973, Example 102:10 (i), p. 304: the idèle condition over $\mathbb Q$.** For $F = \mathbb Q$, a
nondegenerate form `Q` (`hQ`) in $n \ge 3$ variables (`hn`) which is indefinite (`hind`: isotropic at the infinite
place of $\mathbb Q$), and $S$ = all finite spots, every idèle is $i = \alpha\, j$ with $\alpha \in D = \theta(O^+(V))$
(`spinorNormGroup Q hQ`, as a principal idèle) and $j \in J_{\mathbb Q}^S$ (`sIdeles Set.univ`). I.e.
$J_{\mathbb Q} = P_D J_{\mathbb Q}^S$, the hypothesis of 104:9 (`OMeara104_9`). *Proof:* $\mathbb Z$ is a PID, so
$J = P J^S$ (`exists_principal_mul_unitIdele`), and $D = \mathbb Q^\times$ (`spinorNormGroup_eq_top_of_isotropic_real`,
the unique infinite place being real). -/
@[kb "omeara1963" "§102B, 102:10 (i), p. 304"]
theorem idele_condition_rat {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (hind : IsIndefinite Q) :
    ∀ i : IdeleGroup (𝓞 ℚ) ℚ, ∃ α ∈ spinorNormGroup Q hQ,
      ∃ j ∈ OMeara.sIdeles (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))),
        i = IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ α * j := by
  have : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom
      Rat.ringOfIntegersEquiv.symm.surjective
  obtain ⟨w₀, hw₀⟩ := hind
  have hD : spinorNormGroup Q hQ = ⊤ :=
    spinorNormGroup_eq_top_of_isotropic_real Q hQ hn fun w _ => by
      rwa [Subsingleton.elim w w₀]
  intro i
  obtain ⟨α, j, hj, hij⟩ := exists_principal_mul_unitIdele i
  exact ⟨α, by rw [hD]; trivial, j, hj, hij⟩

end QuadFormsKB.Lattices
