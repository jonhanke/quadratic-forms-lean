/-
# O'Meara §13: non-archimedean valuations, residue class fields (13:2, 13:4, 13:5, 13:7)

**Setting.** $F$ is a field with a non-archimedean valuation $v$ (a Mathlib `AbsoluteValue F ℝ` together with
`hv : IsNonarchimedean v`). O'Meara's integers $\mathfrak o(\mathfrak p)$, maximal ideal $\mathfrak m(\mathfrak p)$ and
*residue class field* (§13A, pp. 20–21) are:
* `integers v hv` $= \{a : |a| \le 1\}$, a subring of $F$;
* `maximalIdealOf v hv` $= \{a \in \mathfrak o : |a| < 1\}$, an ideal of `integers v hv`;
* `IsResidueClassField v hv H φ`: a field $H$ with a surjective ring homomorphism $\varphi\colon\mathfrak o \to H$ with
  kernel $\mathfrak m$ (O'Meara's "composite object $(\varphi, H)$").
Completions are those of `Sec11B.lean` (`IsCompletion`); the valuation of a completion is its norm, viewed as an
`AbsoluteValue` by `NormedField.toAbsoluteValue`.

**Proves**
* `residue_char` (**13:2**): if $\operatorname{char} F = p \ne 0$ then every residue class field of $F$ has
  characteristic $p$;
* `valueGroup_completion` (**13:4**, part (1)): the value group of a completion equals that of $F$ (every non-zero
  value of the completion is a value of a non-zero element of $F$); parts (2), (3) are consequences about indices and
  are not stated;
* `residue_completion` (**13:5**, part (1)): a residue class field of the completion is, via the natural map, a residue
  class field of $F$ (so $F(\mathfrak p) = F_{\mathfrak p}(\mathfrak p)$); part (2) is not proved;
* `monic_factor_integral` (**13:7**): a monic divisor of a monic polynomial with integral coefficients has integral
  coefficients. This is a generalization of O'Meara's statement about monic *irreducible factors*; the proof is O'Meara's
  (multiplicativity of the Gauss norm, Mathlib's `Polynomial.gaussNorm_mul`).

**Not here.** 13:1 and 13:3 are notation/examples; 13:6 ($ef \le n$) is not proved.
-/
import QuadFormsKB.Citation
import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.Algebra.CharP.Basic
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import QuadFormsKB.Literature.OMeara.Sec11A
import QuadFormsKB.Literature.OMeara.Sec11B

open Polynomial

namespace QuadFormsKB.OMeara

universe u
variable {F : Type u} [Field F] (v : AbsoluteValue F ℝ) (hv : IsNonarchimedean v)

/-- The *ring of integers* $\mathfrak o(\mathfrak p) = \{a \in F : |a| \le 1\}$ of $F$ at the non-archimedean
valuation $v$ (the valuation ring of $v$). The subring axioms use the strong triangle law `hv`. -/
@[kb "omeara1963" "§13A, definition of the integers o(p), p. 20"]
def integers : Subring F where
  carrier := {a | v a ≤ 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_mul] at *
    nlinarith [v.nonneg a, v.nonneg b]
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    exact (hv a b).trans (max_le ha hb)
  neg_mem' := by
    intro a ha
    simpa using ha

/-- The *maximal ideal* $\mathfrak m(\mathfrak p) = \{a \in F : |a| < 1\}$ of the ring of integers `integers v hv`,
as an ideal of that ring. -/
@[kb "omeara1963" "§13A, definition of the maximal ideal m(p), p. 20"]
def maximalIdealOf : Ideal (integers v hv) where
  carrier := {a | v (a : F) < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    exact lt_of_le_of_lt (hv a b) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul, Subring.coe_mul, map_mul] at *
    have hc : v (c : F) ≤ 1 := c.2
    calc v (c : F) * v (x : F) ≤ 1 * v (x : F) := by gcongr
      _ < 1 := by simpa using hx

/-- O'Meara's *residue class field* of $F$ at $v$ (§13A, p. 21): the field $H$ together with a ring homomorphism
$\varphi\colon\mathfrak o \to H$ of the ring of integers onto $H$ with kernel $\mathfrak m$. Any two are isomorphic;
the quotient $\mathfrak o/\mathfrak m$ is one. -/
@[kb "omeara1963" "§13A, definition of a residue class field, p. 21"]
def IsResidueClassField (H : Type*) [Field H] (φ : integers v hv →+* H) : Prop :=
  Function.Surjective φ ∧ RingHom.ker φ = maximalIdealOf v hv

/-- **13:2.** If $F$ has characteristic $p \ne 0$ (`CharP F p`) then every residue class field $H$ of $F$ at the
non-archimedean valuation $v$ has characteristic $p$ (O'Meara: $\chi(\bar F(\mathfrak p)) = \chi(F)$ whenever
$\chi(F) \ne 0$). -/
@[kb "omeara1963" "§13A, 13:2, p. 21"]
theorem residue_char {p : ℕ} (hp : p ≠ 0) [CharP F p] {H : Type*} [Field H] (φ : integers v hv →+* H)
    (h : IsResidueClassField v hv H φ) : CharP H p := by
  have hprime : p.Prime := (CharP.char_is_prime_or_zero F p).resolve_right hp
  rw [CharP.charP_iff_prime_eq_zero hprime]
  have hmem : ((p : integers v hv)) ∈ RingHom.ker φ := by
    rw [h.2]
    show v (((p : integers v hv) : F)) < 1
    simp
  have := hmem
  rw [RingHom.mem_ker] at this
  simpa using this


section Completion

variable {E : Type*} [NormedField E] {ι : F →+* E}

include hv

/-- A completion of a non-archimedean valued field is non-archimedean (its norm satisfies the strong triangle law);
by 11:1 it suffices that the natural integers have norm $\le 1$. -/
theorem IsCompletion.isNonarchimedean_of (h : IsCompletion v E ι) :
    IsNonarchimedean (NormedField.toAbsoluteValue E) := by
  refine (isNonarchimedean_iff_natCast_bounded _).2 ⟨1, fun n => ?_⟩
  have : (n : E) = ι (n : F) := by simp
  show ‖(n : E)‖ ≤ 1
  rw [this, h.norm_eq]
  exact hv.apply_natCast_le_one (by simp) (map_one v)

/-- **13:4 (1).** Let $E$ be a completion of the non-archimedean valued field $(F, v)$. Every non-zero $y \in E$ has
$\lVert y\rVert = |x|_v$ for some non-zero $x \in F$; that is, the value groups $|F|$ and $|E|$ coincide (the inclusion
$|F| \subseteq |E|$ is `IsCompletion.norm_eq`). Proof: approximate $y$ by $x$ with $|y - x| < |y|$ and apply the
Principle of Domination. -/
@[kb "omeara1963" "§13B, 13:4 (1), p. 22"]
theorem valueGroup_completion (h : IsCompletion v E ι) {y : E} (hy : y ≠ 0) :
    ∃ x : F, x ≠ 0 ∧ v x = ‖y‖ := by
  have hna := h.isNonarchimedean_of v hv
  have hpos : 0 < ‖y‖ := norm_pos_iff.2 hy
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.1 h.dense y ‖y‖ hpos
  rw [dist_eq_norm] at hx
  refine ⟨x, ?_, ?_⟩
  · intro h0
    rw [h0] at hx
    simp at hx
  · rw [← h.norm_eq]
    have hna' : IsNonarchimedean (norm : E → ℝ) := hna
    have hlt : ‖ι x - y‖ < ‖y‖ := by rw [norm_sub_rev]; exact hx
    have := hna'.add_eq_left_of_lt (f := (norm : E → ℝ)) (fun x => norm_neg x) (a := ι x - y)
      (b := y) hlt
    simpa using this

/-- The natural ring homomorphism from the integers of `F` to the integers of a completion. -/
def integersMap (h : IsCompletion v E ι) :
    integers v hv →+* integers (NormedField.toAbsoluteValue E) (h.isNonarchimedean_of v hv) where
  toFun a := ⟨ι a, by
    show ‖ι a‖ ≤ 1
    rw [h.norm_eq]; exact a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

/-- **13:5 (1).** Let $E$ be a completion of the non-archimedean valued field $(F, v)$ and $(\varphi, H)$ a residue
class field of $E$. Then $(\varphi\circ\iota|_{\mathfrak o_F}, H)$ is a residue class field of $F$: the residue class
fields of $F$ and of $F_{\mathfrak p}$ coincide. -/
@[kb "omeara1963" "§13B, 13:5 (1), p. 23"]
theorem residue_completion (h : IsCompletion v E ι) {H : Type*} [Field H]
    (φ : integers (NormedField.toAbsoluteValue E) (h.isNonarchimedean_of v hv) →+* H)
    (hφ : IsResidueClassField _ (h.isNonarchimedean_of v hv) H φ) :
    IsResidueClassField v hv H (φ.comp (integersMap v hv h)) := by
  have hna := h.isNonarchimedean_of v hv
  have hna' : IsNonarchimedean (norm : E → ℝ) := hna
  refine ⟨fun t => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hφ.1 t
    obtain ⟨x, hx⟩ := Metric.denseRange_iff.1 h.dense (y : E) 1 one_pos
    rw [dist_eq_norm] at hx
    have hy1 : ‖(y : E)‖ ≤ 1 := y.2
    have hxi : v x ≤ 1 := by
      rw [← h.norm_eq]
      have := hna' (y : E) (ι x - y)
      calc ‖ι x‖ = ‖(y : E) + (ι x - y)‖ := by simp
        _ ≤ max ‖(y : E)‖ ‖ι x - (y : E)‖ := by
            have := hna' (y : E) (ι x - y)
            simpa using this
        _ ≤ 1 := by
            refine max_le hy1 ?_
            rw [norm_sub_rev]; exact hx.le
    refine ⟨⟨x, hxi⟩, ?_⟩
    have hker : y - integersMap v hv h ⟨x, hxi⟩ ∈ RingHom.ker φ := by
      rw [hφ.2]
      show ‖((y - integersMap v hv h ⟨x, hxi⟩ : integers (NormedField.toAbsoluteValue E) hna) : E)‖ < 1
      simpa [integersMap] using hx
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hker
    simpa [hker] using hy
  · ext a
    have : (φ.comp (integersMap v hv h)) a = 0 ↔ integersMap v hv h a ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker]; rfl
    rw [RingHom.mem_ker, this, hφ.2]
    show ‖ι a‖ < 1 ↔ v (a : F) < 1
    rw [h.norm_eq]

end Completion


omit hv in
/-- **13:7 (generalized).** Let $v$ be a non-archimedean valuation of $F$, $f \in F[x]$ a monic polynomial with all
coefficients integral ($|a_i| \le 1$), and $g \in F[x]$ a monic divisor of $f$. Then all coefficients of $g$ are
integral. O'Meara states it for the monic irreducible factors of $f$; every monic divisor is covered. -/
@[kb "omeara1963" "§13C, 13:7, p. 26"]
theorem monic_factor_integral (hv : IsNonarchimedean v) {f g : F[X]} (hf : f.Monic) (hg : g.Monic)
    (hdvd : g ∣ f) (hint : ∀ i, v (f.coeff i) ≤ 1) : ∀ i, v (g.coeff i) ≤ 1 := by
  obtain ⟨h, rfl⟩ := hdvd
  have hh : h.Monic := Monic.of_mul_monic_left hg hf
  have key : ∀ q : F[X], q.Monic → 1 ≤ q.gaussNorm v 1 := by
    intro q hq
    have := q.le_gaussNorm v (c := 1) zero_le_one q.natDegree
    simpa [hq.coeff_natDegree] using this
  have hmul := Polynomial.gaussNorm_mul hv (c := 1) one_pos g h
  obtain ⟨j, hj⟩ := (g * h).exists_eq_gaussNorm v 1
  have hG : (g * h).gaussNorm v 1 ≤ 1 := by
    rw [hj]; simpa using hint j
  have hgn : g.gaussNorm v 1 ≤ 1 := by
    have h1 := key h hh
    have h0 : 0 ≤ g.gaussNorm v 1 := g.gaussNorm_nonneg v zero_le_one
    rw [hmul] at hG
    nlinarith
  intro i
  have := g.le_gaussNorm v (c := 1) zero_le_one i
  simp at this
  exact this.trans hgn

end QuadFormsKB.OMeara
