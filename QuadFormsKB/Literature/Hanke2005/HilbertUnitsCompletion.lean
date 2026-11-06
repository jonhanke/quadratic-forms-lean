import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.SquareClassDuality
import QuadFormsKB.Lattices.SpinorLocal

/-!
# Hilbert symbols of local units against global units, for completion units

At a non-dyadic finite place $v$ of a number field $F$, the Hilbert symbol
$(u, d)_v$ equals $1$ whenever $u \in F_v$ is a **local** unit ($|u|_v = 1$) and $d \in F$ has
$v(d) = 1$. This extends `SqDual.hilbert_units_nondyadic` (both arguments in $F$) to a first
argument in the completion $F_v$, by density of $F$ in $F_v$ and the fact that $1 + \varepsilon$
is a square in $F_v$ for $|\varepsilon|_v < 1$ (Hensel; $2$ a unit).

Corollary: if the square class of $c \in F_v^\times$ contains a unit of $\mathfrak o_v$
(`Lattices.IsUnitSqClass`), then $(c, d)_v = 1$.
-/

open NumberField IsDedekindDomain QuadFormsKB.Lattices

namespace QuadFormsKB.Hanke2005.SpinorIdele

variable {F : Type} [Field F] [NumberField F]

/-- **Hensel step in the completion:** at a non-dyadic finite place $v$, every $1 + \varepsilon$ with
$\varepsilon \in F_v$, $\|\varepsilon\| < 1$, is a square in $F_v$. (Same Newton/contraction argument as
`NFLocal.isSquare_of_valuation_sub_one_lt_nf`, which treats $\varepsilon \in F$.) -/
theorem isSquare_one_add_of_norm_lt_one (v : HeightOneSpectrum (𝓞 F))
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    ∀ e : v.adicCompletion F, ‖e‖ < 1 → IsSquare (1 + e) := by
  set K := v.adicCompletion F
  intro e hr
  have hv : ∀ x : F, Valued.v (algebraMap F K x) = v.valuation F x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have hn2 : ‖(2:K)‖ = 1 := by
    rw [Valued.toNormedField.norm_eq_one_iff]
    have : (2:K) = algebraMap F K (algebraMap (𝓞 F) F 2) := by rw [map_ofNat, map_ofNat]
    rw [this, hv, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr h2
  have h2K : (2:K) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn2; exact zero_ne_one hn2
  set r := ‖e‖ with hrdef
  have hr0 : 0 ≤ r := norm_nonneg _
  let f : K → K := fun y => (e - y^2)/2
  let s := Metric.closedBall (0:K) r
  have hmaps : Set.MapsTo f s s := by
    intro y hy
    simp only [s, Metric.mem_closedBall, dist_zero_right] at hy ⊢
    simp only [f, norm_div, hn2, div_one]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ?_)
    rw [norm_neg, norm_pow]
    have := mul_le_mul hy hy (norm_nonneg y) hr0
    nlinarith
  have hcon : ContractingWith ‖e‖₊ (hmaps.restrict f s s) := by
    refine ⟨hr, LipschitzWith.of_dist_le_mul fun y y' => ?_⟩
    have hy := y.2; have hy' := y'.2
    simp only [s, Metric.mem_closedBall, dist_zero_right] at hy hy'
    change dist (f (y:K)) (f y') ≤ (‖e‖₊ : ℝ) * dist (y:K) y'
    simp only [f, coe_nnnorm]
    rw [dist_eq_norm, dist_eq_norm]
    have : (e - (y:K)^2)/2 - (e - (y':K)^2)/2 = -((y:K) - y') * ((y:K) + y') / 2 := by ring
    rw [this, norm_div, norm_mul, norm_neg, hn2, div_one]
    have : ‖(y:K) + y'‖ ≤ r := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy hy')
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  obtain ⟨y, -, hfix, -⟩ := ContractingWith.exists_fixedPoint' (Metric.isClosed_closedBall.isComplete)
    hmaps hcon (x := 0) (by simp [s, hr0]) (edist_ne_top _ _)
  refine ⟨1 + y, ?_⟩
  have : f y = y := hfix
  simp only [f] at this
  have h2' : (2:K) * y = e - y^2 := by
    have h3 : (2:K) * ((e - y^2)/2) = 2 * y := by rw [this]
    rw [mul_div_cancel₀ _ h2K] at h3
    exact h3.symm
  linear_combination -h2'

/-- **Hilbert symbol of a completion unit against a global unit is $1$** (non-dyadic $v$): if
$v(d) = 1$ for $d \in F$ and $u \in F_v$ has $|u|_v = 1$, then $(u, d)_{F_v} = 1$.

*Proof.* By density pick $a \in F$ with $|u - a|_v < 1$; then $v(a) = 1$ and $u = a(1 + \varepsilon)$ with
$|\varepsilon| < 1$, so $u/a$ is a square (`isSquare_one_add_of_norm_lt_one`). Hence
$(u, d) = (a, d) = 1$ by `SqDual.hilbert_units_nondyadic`. -/
@[kb "omeara1963" "§63B, 63:12, p. 166"]
theorem hilbertSymbol_unit_of_valuation_one (v : HeightOneSpectrum (𝓞 F))
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (d : F) (hd : v.valuation F d = 1)
    (u : v.adicCompletion F) (hu : Valued.v u = 1) :
    hilbertSymbol (v.adicCompletion F) u (algebraMap F (v.adicCompletion F) d) = 1 := by
  have hv : ∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  obtain ⟨a, hda⟩ := Metric.denseRange_iff.mp (HeightOneSpectrum.denseRange_algebraMap F v) u 1 one_pos
  have ha : Valued.v (algebraMap F (v.adicCompletion F) a - u) < 1 := by
    rw [← Valued.toNormedField.norm_lt_one_iff, ← dist_eq_norm, dist_comm]; exact hda
  have ha1' : Valued.v (algebraMap F (v.adicCompletion F) a) = 1 := by
    have := Valuation.map_eq_of_sub_lt Valued.v (x := u) (y := algebraMap F (v.adicCompletion F) a) (by rwa [hu])
    rw [this, hu]
  have ha1 : v.valuation F a = 1 := by rw [← hv]; exact ha1'
  have ha0 : algebraMap F (v.adicCompletion F) a ≠ 0 := by
    intro h; rw [h, map_zero] at ha1'; exact zero_ne_one ha1'
  have hw : ‖u / algebraMap F (v.adicCompletion F) a - 1‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff, show u / algebraMap F (v.adicCompletion F) a - 1 = (u - algebraMap F (v.adicCompletion F) a) / algebraMap F (v.adicCompletion F) a by
      field_simp, map_div₀, ha1', div_one, ← Valuation.map_neg Valued.v, neg_sub]
    exact ha
  obtain ⟨s, hs⟩ := isSquare_one_add_of_norm_lt_one v h2 _ hw
  have hs0 : s ≠ 0 := by
    rintro rfl
    have hu0 : u / algebraMap F (v.adicCompletion F) a = 0 := by
      rw [mul_zero] at hs; linear_combination hs
    rw [div_eq_zero_iff] at hu0
    rcases hu0 with h | h
    · rw [h, map_zero] at hu; exact zero_ne_one hu
    · exact ha0 h
  have hu' : u = algebraMap F (v.adicCompletion F) a * s ^ 2 := by
    rw [sq, ← hs]; field_simp; ring
  rw [hu', HN.hilbertSymbol_mul_sq_left (v.adicCompletion F) _ _ s hs0]
  exact SqDual.hilbert_units_nondyadic v h2 a d ha1 hd

/-- **Corollary (unit square classes):** if the square class of $c \in F_v^\times$ contains a unit of
$\mathfrak o_v$ (`Lattices.IsUnitSqClass`), then $(c, d)_{F_v} = 1$ for every $d \in F$ with $v(d) = 1$
(non-dyadic $v$). Uses that the Hilbert symbol depends only on the square class of its first argument. -/
@[kb "omeara1963" "§63B, 63:12, p. 166"]
theorem hilbertSymbol_unitSqClass (v : HeightOneSpectrum (𝓞 F))
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (d : F) (hd : v.valuation F d = 1)
    (c : v.adicCompletion F) (hc : c ≠ 0)
    (hcl : Lattices.IsUnitSqClass v (sqClassOf c)) :
    hilbertSymbol (v.adicCompletion F) c (algebraMap F (v.adicCompletion F) d) = 1 := by
  obtain ⟨u, hu, hcu⟩ := hcl
  have hu0 : u ≠ 0 := by
    rintro rfl; rw [map_zero] at hu; exact zero_ne_one hu
  have hsq : sqClassOf (c * u) = 1 := by
    rw [sqClassOf_mul hc hu0, hcu, SqClass.mul_self]
  obtain ⟨r, hr⟩ := (sqClassOf_eq_one_iff (mul_ne_zero hc hu0)).mp hsq
  have hr0 : r ≠ 0 := by
    rintro rfl; rw [mul_zero] at hr; exact mul_ne_zero hc hu0 hr
  have hcu' : c = u * (r / u) ^ 2 := by
    have : c = r ^ 2 / u := by rw [eq_div_iff hu0]; linear_combination hr
    rw [this]; field_simp
  rw [hcu', HN.hilbertSymbol_mul_sq_left _ _ _ (r / u) (div_ne_zero hr0 hu0)]
  exact hilbertSymbol_unit_of_valuation_one v h2 d hd u hu

end QuadFormsKB.Hanke2005.SpinorIdele
