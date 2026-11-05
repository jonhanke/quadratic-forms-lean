/-
# Hanke 2011, §6 over $\mathbb Q$: total masses of primitive ternary forms as sums over genera

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §6, Corollaries 6.3 and 6.4, for $F = \mathbb Q$, $n = 3$, positive
definite forms; this is the input that paper 7 (Hanke, *Explicit formulas for masses of ternary quadratic lattices of
varying determinant over number fields*, `hanke2011ternary`, namespace `Hanke2011Ternary`) takes from paper 6.

* `cor_6_3_rat` (**Corollary 6.3 for one genus over $\mathbb Q$**, $n = 3$): for a positive definite integral ternary form
  $Q$ with Hessian determinant $N$,
  $$\mathrm{Mass}(Q) = \sum_{[Q']\in\mathrm{Gen}(Q)}\frac1{|\mathrm{Aut}(Q')|} = \frac{N^2}{64\pi^2}\prod_p\beta_{Q,p}(Q)^{-1},$$
  ($V(3) = \pi^2$, `volV_three`; $\beta_{Q,p}$ = `localBeta`, Hanke's densities in Gram coordinates), from `cor_6_3_genus`.
* `IsPrimitiveForm` is a genus invariant (`SameGenus.isPrimitiveForm`); the classes of
  $\mathrm{Cls}^*(N;3)$ (`primitiveTernaryClasses N`) are finite in number (`primitiveTernaryClasses_finite`) and fall into
  the genera `primitiveTernaryGenera N`.
* `tmass3star_eq_sum_genera`: $\mathrm{TMass}^*_3(N) = \frac{N^2}{64\pi^2}\sum_{G}\prod_p\beta_{G,p}(G)^{-1}$, the sum over the
  genera $G$ of primitive positive definite integral ternary forms with $\det_H = N$ (`genusInvDensity`); this is the
  totally definite case of Theorem 6.2/Corollary 6.3 summed over genera (the sum over $\mathrm{Gen}^*$ in (15)).
* **Payoff for paper 7.** `TernaryGenusDensityFormula` (**named input**): for every $N \ge 1$,
  $\sum_{G}\prod_p\beta_{G,p}(G)^{-1} = 2\zeta(2)\,\big(A^*_3(N) + B^*_3(N)\big)$, with paper 7's $A^*_3(N)$, $B^*_3(N)$
  (`globalA`, `globalB`). It mentions no classes, automorphism groups or masses; it is paper 6's Lemma 3.7 and
  Theorem 4.8 ($M^* = \frac12\beta^{-1}_{3,f}(A^* + B^*)$ with the true local data, $\varepsilon_\infty = 1$), Remark 4.14
  ($\beta^{-1}_{3,f} = 4\zeta(2)$), and paper 7's identification of the true local data with its local models.
  `primitiveMassLocalFormula_of_genus` derives paper 7's named input `PrimitiveMassLocalFormula` from it, so paper 7's
  Corollary 8.2 and Theorem 1.1 hold under this narrower input (`cor_8_2_primitive_of_genus`, `theorem_1_1_of_genus`).
-/
import QuadFormsKB.Literature.Hanke2011Structure.LocalGeneraNF
import QuadFormsKB.Literature.Hanke2011Ternary.Scaling
import QuadFormsKB.Tamagawa.RatBridge
import QuadFormsKB.Siegel.GenusFinite

namespace QuadFormsKB.Hanke2011Structure

open NumberField Real QuadFormsKB.Siegel

noncomputable section

/-! ### Corollary 6.3 over $\mathbb Q$ -/

/-- $V(3) = \tfrac12\pi^3\Gamma(\tfrac12)^{-1}\Gamma(1)^{-1}\Gamma(\tfrac32)^{-1} = \pi^2$. -/
theorem volV_three : volV 3 = π ^ 2 := by
  have hs : sqrt π ≠ 0 := (sqrt_pos.mpr pi_pos).ne'
  have hI : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  have h32 : Gamma ((3 : ℝ) / 2) = sqrt π / 2 := by
    rw [show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num, Gamma_add_one (by norm_num), Gamma_one_half_eq]
    ring
  simp only [volV, hI, Finset.prod_insert (by decide : (1 : ℕ) ∉ ({2, 3} : Finset ℕ)),
    Finset.prod_insert (by decide : (2 : ℕ) ∉ ({3} : Finset ℕ)), Finset.prod_singleton, Nat.cast_one,
    Nat.cast_ofNat]
  rw [show ((3 : ℝ) * (3 + 1)) / 4 = 3 by norm_num, Gamma_one_half_eq, show (2 : ℝ) / 2 = 1 by norm_num,
    Gamma_one, h32]
  have hsq : sqrt π * sqrt π = π := mul_self_sqrt pi_pos.le
  have key : (sqrt π)⁻¹ * (1⁻¹ * (sqrt π / 2)⁻¹) = 2 / π := by
    rw [inv_one, one_mul, inv_div, inv_mul_eq_div, div_div, hsq]
  rw [key, show (π : ℝ) ^ (3 : ℝ) = π ^ (3 : ℕ) by exact_mod_cast rpow_natCast π 3]
  field_simp

/-- The inverse product $\prod_p\beta_{Q,p}(Q)^{-1}$ of Hanke's local densities of an integral form $Q$ (Gram coordinates). -/
def invDensityProd {n : ℕ} (Q : QuadForm ℤ n) : ℝ := (∏' v, localBeta v (Tamagawa.RatBridge.up Q))⁻¹

theorem hessian_det_formF_up {n : ℕ} (Q : QuadForm ℤ n) :
    (HilbertModular.formF (Tamagawa.RatBridge.up Q)).hessian.det = (Q.hessian.det : ℚ) := by
  rw [Tamagawa.RatBridge.formF_up, QuadForm.hessian_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

/-- **Corollary 6.3 for one genus, $F = \mathbb Q$, $n = 3$** (p. 26): for a positive definite integral ternary form $Q$,
$$\mathrm{Mass}(Q) = \sum_{[Q']\in\mathrm{Gen}(Q)}\frac1{|\mathrm{Aut}(Q')|} = \frac{(\det_H Q)^2}{64\pi^2}\prod_p\beta_{Q,p}(Q)^{-1}$$
($|\Delta_{\mathbb Q}| = 1$, $V(3) = \pi^2$, $N(2\mathbb Z)^{n(n+1)/2} = 2^6$, $N(I(S))^{(n+1)/2} = (\det_H Q)^2$), and the product of
the inverse local densities is positive. -/
@[kb "hanke2011structure" "Cor. 6.3, p. 26 (F = Q, n = 3, one genus)"]
theorem cor_6_3_rat {Q : QuadForm ℤ 3} (hQ : IntQF.PosDef Q) :
    Siegel.mass Q = (Q.hessian.det : ℝ) ^ 2 / (64 * π ^ 2) * invDensityProd Q ∧ 0 < invDensityProd Q := by
  have hpd := (Tamagawa.RatBridge.isTotallyPosDef_up_iff Q).mpr hQ
  have hnd : (Tamagawa.RatBridge.up Q).Nondegenerate := by
    have h := Siegel.det_hessian_pos hQ
    unfold QuadForm.Nondegenerate
    rw [QuadForm.hessian_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ (algebraMap ℤ (𝓞 ℚ)).injective_int).mpr h.ne'
  obtain ⟨h, hP⟩ := cor_6_3_genus (F := ℚ) le_rfl (Tamagawa.RatBridge.up Q) hnd hpd
  refine ⟨?_, hP⟩
  rw [Tamagawa.RatBridge.mass_rat Q hQ]
  have hD : (0 : ℝ) < Q.hessian.det := by exact_mod_cast Siegel.det_hessian_pos hQ
  rw [h, hessian_det_formF_up, Algebra.norm_self, MonoidHom.id_apply, Rat.cast_intCast, discr_rat,
    Module.finrank_self, volV_three, abs_of_pos hD, Int.cast_one, abs_one, Real.one_rpow,
    show (((3 : ℕ) : ℝ) + 1) / 2 = (2 : ℕ) by norm_num, rpow_natCast,
    show ((3 : ℕ) : ℝ) * ((3 : ℕ) + 1) / 2 = (6 : ℕ) by norm_num, rpow_natCast]
  unfold invDensityProd
  ring

/-! ### Primitivity is a genus invariant -/

theorem isPrimitiveForm_iff_forall_prime (Q : QuadForm ℤ 3) :
    Hanke2011Ternary.IsPrimitiveForm Q ↔ ∀ p : ℕ, p.Prime → ∃ i j, ¬ (p : ℤ) ∣ Q.coeff i j := by
  constructor
  · intro h p hp
    by_contra hall
    push Not at hall
    have := h p hall
    rw [Int.isUnit_iff] at this
    rcases this with h1 | h1 <;> [exact hp.one_lt.ne' (by exact_mod_cast h1); omega]
  · intro h d hd
    by_contra hu
    have hd1 : d.natAbs ≠ 1 := fun h1 => hu (Int.isUnit_iff_natAbs_eq.mpr h1)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
    obtain ⟨i, j, hij⟩ := h p hp
    exact hij ((Int.natCast_dvd.mpr hpd).trans (hd i j))

/-- **Primitivity is a genus invariant**: if $Q$ and $Q'$ are $\mathbb Z_p$-equivalent for every $p$ and $Q$ is
primitive, so is $Q'$ (a prime dividing all coefficients of $Q'$ divides all values of $Q'$ over $\mathbb Z_p$, hence all
values and coefficients of $Q$). -/
theorem sameGenus_isPrimitiveForm {Q Q' : QuadForm ℤ 3} (h : SameGenus Q Q')
    (hQ : Hanke2011Ternary.IsPrimitiveForm Q) : Hanke2011Ternary.IsPrimitiveForm Q' := by
  rw [isPrimitiveForm_iff_forall_prime] at hQ ⊢
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  by_contra hall
  push Not at hall
  obtain ⟨i, j, hij⟩ := hQ p hp
  apply hij
  have hmem : ∀ k : ℤ, (k : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] ↔ (p : ℤ) ∣ k := fun k => by
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_int_lt_one_iff_dvd]
  have h' := coeff_mem_of_isometricGL (IsLocalRing.maximalIdeal ℤ_[p]) (h.1 p).symm
    (fun a b => (hmem _).mpr (hall a b)) i j
  exact (hmem _).mp h'

/-! ### The classes and genera of $\mathrm{Cls}^*(N;3)$ -/

/-- The defining properties of $\mathrm{Cls}^*(N;3)$: positive definite, primitive, $\det_H = N$. -/
def IsPrimTernary (N : ℕ) (Q : QuadForm ℤ 3) : Prop :=
  IntQF.PosDef Q ∧ Hanke2011Ternary.IsPrimitiveForm Q ∧ Q.hessian.det = N

theorem sameGenus_isPrimTernary {N : ℕ} {Q Q' : QuadForm ℤ 3} (h : SameGenus Q Q') (hQ : IsPrimTernary N Q) :
    IsPrimTernary N Q' :=
  ⟨h.posDef hQ.1, sameGenus_isPrimitiveForm h hQ.2.1, (SameGenus.det_hessian_eq hQ.1 h).symm.trans hQ.2.2⟩

theorem mem_primitiveTernaryClasses_iff {N : ℕ} {c : QClass 3} :
    c ∈ Hanke2011Ternary.primitiveTernaryClasses N ↔ IsPrimTernary N c.out := by
  constructor
  · rintro ⟨Q, rfl, h1, h2, h3⟩
    have he : IntEquiv Q (classOf Q).out := classOf_eq_classOf_iff.mp (Quotient.out_eq _).symm
    exact sameGenus_isPrimTernary he.sameGenus ⟨h1, h2, h3⟩
  · intro h
    exact ⟨c.out, Quotient.out_eq c, h.1, h.2.1, h.2.2⟩

/-- **$\mathrm{Cls}^*(N;3)$ is finite** (Hermite reduction, `exists_intEquiv_hessian_bounded`). -/
theorem primitiveTernaryClasses_finite (N : ℕ) : (Hanke2011Ternary.primitiveTernaryClasses N).Finite := by
  refine ((finite_setOf_hessian_bounded (n := 3) (Hermite.entryBound 3 N)).image classOf).subset ?_
  rintro c ⟨Q, rfl, hQ, -, hdet⟩
  obtain ⟨Q3, he, hb⟩ := exists_intEquiv_hessian_bounded hQ
  refine ⟨Q3, fun i j => ?_, (classOf_eq_classOf_iff.mpr he).symm⟩
  have := hb i j
  rwa [hdet] at this

/-- **The genera of $\mathrm{Cls}^*(N;3)$**: the sets of classes $\mathrm{Gen}(Q)$ of the forms $Q$ of $\mathrm{Cls}^*(N;3)$
(the paper's $\mathrm{Gen}^*(S,\vec\sigma_\infty;n)$ for $F = \mathbb Q$, $S = N$, $\vec\sigma_\infty = (3,0)$, $n = 3$). -/
@[kb "hanke2011structure" "§1.3, p. 6 (Gen*(S, σ, c; n)), F = Q, n = 3, positive definite"]
def primitiveTernaryGenera (N : ℕ) : Set (Set (QClass 3)) :=
  (fun c : QClass 3 => genusClasses c.out) '' Hanke2011Ternary.primitiveTernaryClasses N

open Classical in
/-- **The inverse local density product of a genus** $G \in \mathrm{Gen}^*(N;3)$: $\prod_p\beta_{G,p}(G)^{-1}$, computed from a
representative form (`invDensityProd`; it does not depend on the representative, `genusInvDensity_eq`). -/
@[kb "hanke2011structure" "Def. 3.4, p. 12 (∏_p β_{G,p}(G)⁻¹), F = Q, n = 3"]
def genusInvDensity (N : ℕ) (G : Set (QClass 3)) : ℝ :=
  if h : ∃ Q : QuadForm ℤ 3, IsPrimTernary N Q ∧ genusClasses Q = G then invDensityProd h.choose else 0

theorem genusInvDensity_eq {N : ℕ} {Q : QuadForm ℤ 3} (hQ : IsPrimTernary N Q) :
    genusInvDensity N (genusClasses Q) = invDensityProd Q := by
  classical
  have hex : ∃ Q' : QuadForm ℤ 3, IsPrimTernary N Q' ∧ genusClasses Q' = genusClasses Q := ⟨Q, hQ, rfl⟩
  rw [genusInvDensity, dite_eq_left hex]
  obtain ⟨hQ', hG⟩ := hex.choose_spec
  -- equal genera have equal masses and determinants, hence equal density products
  have hm : Siegel.mass hex.choose = Siegel.mass Q := by unfold Siegel.mass; rw [hG]
  obtain ⟨h1, -⟩ := cor_6_3_rat hQ'.1
  obtain ⟨h2, -⟩ := cor_6_3_rat hQ.1
  rw [h1, h2, hQ'.2.2, hQ.2.2] at hm
  have hN : (N : ℝ) ≠ 0 := by
    have := Siegel.det_hessian_pos hQ.1
    rw [hQ.2.2] at this
    exact_mod_cast this.ne'
  have hc : (N : ℝ) ^ 2 / (64 * π ^ 2) ≠ 0 := by positivity
  push_cast at hm
  exact mul_left_cancel₀ hc hm

/-- **The total primitive mass as a sum over genera** ($F = \mathbb Q$, $n = 3$; Theorem 6.2/Corollary 6.3 summed over
the genera of $\mathrm{Cls}^*(N;3)$):
$$\mathrm{TMass}^*_3(N) = \frac{N^2}{64\pi^2}\sum_{G\in\mathrm{Gen}^*(N;3)}\prod_p\beta_{G,p}(G)^{-1}.$$ -/
@[kb "hanke2011structure" "Thm. 6.2 and Cor. 6.3, pp. 25–26 (F = Q, n = 3, positive definite)"]
theorem tmass3star_eq_sum_genera (N : ℕ) :
    ((Hanke2011Ternary.TMass3star N : ℚ) : ℝ) =
      (N : ℝ) ^ 2 / (64 * π ^ 2) * ∑ᶠ G ∈ primitiveTernaryGenera N, genusInvDensity N G := by
  classical
  have hP := primitiveTernaryClasses_finite N
  have hGs : (primitiveTernaryGenera N).Finite := hP.image _
  set g : QClass 3 → Set (QClass 3) := fun c => genusClasses c.out with hg
  -- the left side as a finite sum over classes
  have hL : ((Hanke2011Ternary.TMass3star N : ℚ) : ℝ) = ∑ c ∈ hP.toFinset, ((c.autCard : ℝ))⁻¹ := by
    unfold Hanke2011Ternary.TMass3star
    rw [finsum_mem_eq_finite_toFinset_sum _ hP]
    push_cast
    rfl
  rw [hL, finsum_mem_eq_finite_toFinset_sum _ hGs, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := hGs.toFinset) (fun c hc => by
    rw [Set.Finite.mem_toFinset] at hc ⊢; exact ⟨c, hc, rfl⟩)]
  refine Finset.sum_congr rfl fun G hG => ?_
  rw [Set.Finite.mem_toFinset] at hG
  obtain ⟨c0, hc0, rfl⟩ := hG
  have hc0' := mem_primitiveTernaryClasses_iff.mp hc0
  -- the fibre over `Gen(c₀)` is the set of classes of the genus
  have hfib : (hP.toFinset.filter fun c => g c = g c0) = (genusFinite hc0'.1).finite_classes.toFinset := by
    ext c
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨-, hc⟩
      have : c ∈ g c := by
        have h0 := classOf_self_mem_genusClasses c.out
        rwa [show classOf c.out = c from Quotient.out_eq c] at h0
      rw [hc] at this
      exact this
    · intro hc
      obtain ⟨Q', rfl, hs⟩ := hc
      have he : IntEquiv Q' (classOf Q').out := classOf_eq_classOf_iff.mp (Quotient.out_eq _).symm
      have hs' : SameGenus c0.out (classOf Q').out := hs.trans he.sameGenus
      refine ⟨mem_primitiveTernaryClasses_iff.mpr (sameGenus_isPrimTernary hs' hc0'), ?_⟩
      exact (genusClasses_eq_of_sameGenus hs').symm
  rw [hfib, ← mass_eq_sum (genusFinite hc0'.1), (cor_6_3_rat hc0'.1).1, hc0'.2.2, genusInvDensity_eq hc0']
  push_cast
  rfl

/-! ### The payoff for paper 7 -/

/-- **Named input: the genus sum of paper 6 for primitive positive definite ternary forms over $\mathbb Q$.** For every
$N \ge 1$,
$$\sum_{G\in\mathrm{Gen}^*(N;3)}\prod_p\beta_{G,p}(G)^{-1} = 2\zeta(2)\,\big(A^*_3(N) + B^*_3(N)\big),\qquad 2\zeta(2) = \frac{\pi^2}3,$$
with paper 7's $A^*_3(N)$, $B^*_3(N)$ (`Hanke2011Ternary.globalA`, `Hanke2011Ternary.globalB`). Field: `sum_eq`.

This combines (cited, not proved here): paper 6, Lemma 3.7 (the genera of $\mathrm{Gen}^*(N;3)$ correspond to the tuples
of local genera $\mathrm{Gen}^*_f(N, \varepsilon_\infty = 1; 3)$, by the Hasse principle and O'Meara 81:14), Theorem 4.8 with
the true local data ($M^*(N) = \frac12\beta^{-1}_{3,f}(\widetilde N)(A^*(N) + B^*(N))$, proved here for abstract local data,
`LocalGenusData.theorem_4_8_mass`) and Remark 4.14 ($\beta^{-1}_{3,f} = 4\zeta(2)$ for every normalized class; paper 7,
Theorem 7.1), and paper 7's identification of the true local data $A^*_p$, $B^*_p$ with its local models (Lemma 2.3 and
Table 5.3). It mentions no classes, automorphism groups or masses, so it is not the conclusion
`Hanke2011Ternary.PrimitiveMassLocalFormula`; the mass formula part (paper 6, Corollaries 6.3 and 6.4) is proved
(`tmass3star_eq_sum_genera`). -/
@[kb "hanke2011structure" "Lemma 3.7, p. 13, Thm. 4.8, p. 17, Rem. 4.14, p. 20; hanke2011ternary §§2–7"]
structure TernaryGenusDensityFormula : Prop where
  /-- $\sum_G\prod_p\beta_{G,p}(G)^{-1} = 2\zeta(2)(A^*_3(N) + B^*_3(N))$ for $N \ge 1$. -/
  sum_eq : ∀ N : ℕ, N ≠ 0 → ∑ᶠ G ∈ primitiveTernaryGenera N, genusInvDensity N G =
    2 * (π ^ 2 / 6) * ((Hanke2011Ternary.globalA N + Hanke2011Ternary.globalB N : ℚ) : ℝ)

/-- **Paper 7's named input `PrimitiveMassLocalFormula` follows from `TernaryGenusDensityFormula`** (paper 6's
Corollaries 6.3 and 6.4 for $F = \mathbb Q$, $n = 3$ are proved: `tmass3star_eq_sum_genera`). -/
@[kb "hanke2011structure" "Cor. 6.4, p. 26 (F = Q, n = 3)"]
theorem primitiveMassLocalFormula_of_genus (H : TernaryGenusDensityFormula) :
    Hanke2011Ternary.PrimitiveMassLocalFormula := by
  refine ⟨fun N hN => ?_⟩
  rw [tmass3star_eq_sum_genera, H.sum_eq N hN]
  ring

/-- **Paper 7, Corollary 8.2 (primitive part), under `TernaryGenusDensityFormula`.** -/
@[kb "hanke2011ternary" "§8, Cor. 8.2, p. 27 (primitive part), via paper 6 Cor. 6.3–6.4"]
theorem cor_8_2_primitive_of_genus (H : TernaryGenusDensityFormula) :
    Hanke2011Ternary.DMass3star = (1 / 48 : ℚ) • (Hanke2011Ternary.twoPowNegS *
      ((Hanke2011Ternary.zetaShiftZ 1 (-1) * Hanke2011Ternary.zetaShiftZ 2 (-1) -
        Hanke2011Ternary.zetaShiftZ 2 (-2) * Hanke2011Ternary.zetaShiftZ 1 0) *
          Hanke2011Ternary.zetaShiftInv 3 0)) :=
  Hanke2011Ternary.cor_8_2_primitive (primitiveMassLocalFormula_of_genus H)

/-- **Paper 7, Theorem 1.1, under `TernaryGenusDensityFormula`.** -/
@[kb "hanke2011ternary" "§1, Thm. 1.1, p. 2, via paper 6 Cor. 6.3–6.4"]
theorem theorem_1_1_of_genus (H : TernaryGenusDensityFormula) :
    (∀ m : ℕ, m ≠ 0 → Hanke2011Ternary.TMass3 (2 * m) = (1 / 48) *
      ∑ ab ∈ (m.divisors ×ˢ m.divisors).filter (fun ab => ab.1 * ab.2 ^ 2 = m),
        ((ab.1 : ℚ) * ab.2 - (ab.2 : ℚ) ^ 2)) ∧
    (∀ N : ℕ, ¬ 2 ∣ N → Hanke2011Ternary.TMass3 N = 0) :=
  Hanke2011Ternary.theorem_1_1 (primitiveMassLocalFormula_of_genus H)

end

end QuadFormsKB.Hanke2011Structure
