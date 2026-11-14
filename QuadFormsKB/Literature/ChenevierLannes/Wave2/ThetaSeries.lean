/-
# Chenevier–Lannes: theta series of even unimodular lattices of dimension 8, 16, 24

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §2.3, Proposition-Definition 2.3.3 (c), p. 35, and the proofs of
Corollaries 2.3.5 and 2.3.6, p. 36 ($\vartheta_L = E_4$ for $n = 8$, $\vartheta_L = E_8$ for $n = 16$, so
$|R(L)| = 240, 480$ and $h(L) = 30$); §1.1, p. 2, and Table 1.1 ($|R(L)| = 24\,h(L)$ for $n = 24$). Printed page numbers.

**Layer.** The theta series of a positive definite even unimodular form in $n = 2k$ variables, $4 \mid k$, is a level-one
modular form of weight $k$ (`Siegel.thetaMF`) with $q$-expansion coefficients $r_Q(m)$ (`Siegel.qExpansion_thetaMF_coeff`);
Mathlib's normalized Eisenstein series `E` of weight $k$ has coefficients $1$ and $-\frac{2k}{B_k}\sigma_{k-1}(m)$
(`EisensteinSeries.E_qExpansion_coeff`). The root set $R(L)$ is the set of $x$ with $q_L(x) = Q(x) = 1$, so
$|R(L)| = r_Q(1)$.

**Proves** (all unconditional; $m \ge 1$):
- `repNum_eq_eisenstein`: for $k < 12$ (so $k \in \{4, 8\}$), $\vartheta_L = E_k$ (Sturm's bound: no cusp forms);
- `repNum_eight` ($n = 8$): $r_L(m) = 240\,\sigma_3(m)$; `card_rootSet_eight`: $|R(L)| = 240$;
  `coxeterNumber_eight`: $h(L) = 30$;
- `repNum_sixteen` ($n = 16$): $r_L(m) = 480\,\sigma_7(m)$; `card_rootSet_sixteen`: $|R(L)| = 480$;
  `coxeterNumber_sixteen`: $h(L) = 30$;
- `repNum_twentyFour` ($n = 24$): $r_L(m) = \frac{65520}{691}\sigma_{11}(m) + \bigl(|R(L)| - \frac{65520}{691}\bigr)\tau(m)$
  (Cassels' `Lattices.repNum_rank24`, with the Eisenstein coefficient made explicit).

*Proof differs from the book's in one point:* the book gets $\vartheta_L = E_4, E_8$ from $\dim M_4 = \dim M_8 = 1$;
here from Sturm's bound (Mathlib's `ModularForm.sturm_bound_levelOne_nat`), which is the same fact.
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave2.Mass
import QuadFormsKB.Literature.Cassels.AppBSec5

open Matrix ModularForm EisensteinSeries
open UpperHalfPlane hiding I
open scoped MatrixGroups ArithmeticFunction.sigma

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Lattices

variable {n : ℕ}

/-- **$\vartheta_L = E_k$ in weight $k < 12$**: for a positive definite form $Q$ in $n = 2k$ variables with $\det H = 1$,
$4 \mid k$ and $k < 12$, the $q$-expansion coefficients $r_Q(m)$ are those of the normalized Eisenstein series $E_k$
($\vartheta_Q - E_k$ is a modular form of weight $k < 12$ with vanishing constant term, hence $0$ by Sturm's bound). -/
theorem repNum_eq_eisenstein {k : ℕ} (hn : n = 2 * k) (hk : 4 ∣ k) (hk3 : 3 ≤ k) (hk12 : k < 12)
    {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (hdet : Q.hessian.det = 1) (m : ℕ) :
    (repNum Q m : ℂ) = (qExpansion 1 (E hk3)).coeff m := by
  have hev : Even k := by obtain ⟨j, rfl⟩ := hk; exact ⟨2 * j, by ring⟩
  set G := thetaMF hQ hdet hn hk with hG
  have hGc : ∀ m : ℕ, (qExpansion 1 G).coeff m = repNum Q m := fun m => qExpansion_thetaMF_coeff hQ hdet hn hk m
  have hsub0 : ∀ m : ℕ, (qExpansion 1 (⇑G - ⇑(E hk3))).coeff m =
      (qExpansion 1 G).coeff m - (qExpansion 1 (E hk3)).coeff m := by
    intro m
    rw [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL, map_sub]
  have hsub : ∀ m : ℕ, (qExpansion 1 ⇑(G - E hk3)).coeff m =
      (qExpansion 1 G).coeff m - (qExpansion 1 (E hk3)).coeff m := hsub0
  have hF : G - E hk3 = 0 := by
    apply sturm_bound_levelOne_nat
    refine lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _) (PowerSeries.nat_le_order _ (k / 12 + 1) ?_)
    intro i hi
    have hi0 : i = 0 := by
      have : k / 12 = 0 := Nat.div_eq_of_lt hk12
      omega
    subst hi0
    rw [hsub, hGc, E_qExpansion_coeff_zero (k := k) _ hev, Nat.cast_zero, repNum_zero_of_posDef hQ]
    simp
  have := hsub m
  rw [hF, show ⇑(0 : ModularForm 𝒮ℒ (k : ℤ)) = 0 from rfl, qExpansion_zero, hGc] at this
  simp only [map_zero] at this
  linear_combination -this

/-- $B_4 = -1/30$. -/
theorem bernoulli_four_val : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

/-- **$\vartheta_L = E_4$ for $n = 8$** (Chenevier–Lannes, proof of Corollary 2.3.5, p. 36): for every even unimodular
lattice $L$ of dimension $8$ and $m \ge 1$, $r_L(m) = 240\,\sigma_3(m)$. Unconditional (directly from the theta series,
without Mordell's theorem). -/
@[kb "chenevierlannes2019" "proof of Cor. 2.3.5, p. 36 (θ_L = E_4)"]
theorem repNum_eight {Q : QuadForm ℤ 8} (hQ : IsEvenUnimodular Q) {m : ℕ} (hm : 1 ≤ m) :
    repNum Q m = 240 * σ 3 m := by
  have h := repNum_eq_eisenstein (k := 4) rfl (dvd_refl 4) (by norm_num) (by norm_num) hQ.posDef hQ.det_one m
  rw [E_qExpansion_coeff (k := 4) _ ⟨2, rfl⟩, if_neg (by omega), bernoulli_four_val] at h
  have : (repNum Q m : ℂ) = ((240 * σ 3 m : ℕ) : ℂ) := by
    rw [h]; push_cast; norm_num
  exact_mod_cast this

/-- **$\vartheta_L = E_8$ for $n = 16$** (Chenevier–Lannes, proof of Corollary 2.3.6, p. 36): for every even unimodular
lattice $L$ of dimension $16$ and $m \ge 1$, $r_L(m) = 480\,\sigma_7(m)$. Unconditional (directly from the theta series,
without Witt's theorem). -/
@[kb "chenevierlannes2019" "proof of Cor. 2.3.6, p. 36 (θ_L = E_8)"]
theorem repNum_sixteen {Q : QuadForm ℤ 16} (hQ : IsEvenUnimodular Q) {m : ℕ} (hm : 1 ≤ m) :
    repNum Q m = 480 * σ 7 m := by
  have h := repNum_eq_eisenstein (k := 8) rfl ⟨2, rfl⟩ (by norm_num) (by norm_num) hQ.posDef hQ.det_one m
  rw [E_qExpansion_coeff (k := 8) _ ⟨4, rfl⟩, if_neg (by omega), bernoulli_eight_val] at h
  have : (repNum Q m : ℂ) = ((480 * σ 7 m : ℕ) : ℂ) := by
    rw [h]; push_cast; norm_num
  exact_mod_cast this

/-- $|R(L)| = r_Q(1)$: the root set is the set of representations of $1$. -/
theorem ncard_rootSet (Q : QuadForm ℤ n) : (rootSet Q).ncard = repNum Q 1 := by
  rw [repNum, Nat.card_coe_set_eq]
  rfl

/-- **$|R(L)| = 240$ for $n = 8$** (Chenevier–Lannes, proof of Corollary 2.3.5, p. 36). Unconditional. -/
@[kb "chenevierlannes2019" "proof of Cor. 2.3.5, p. 36 (|R(L)| = 240)"]
theorem card_rootSet_eight {Q : QuadForm ℤ 8} (hQ : IsEvenUnimodular Q) : (rootSet Q).ncard = 240 := by
  rw [ncard_rootSet]
  simpa [ArithmeticFunction.sigma_apply] using repNum_eight hQ (m := 1) le_rfl

/-- **$|R(L)| = 480$ for $n = 16$** (Chenevier–Lannes, proof of Corollary 2.3.6, p. 36). Unconditional. -/
@[kb "chenevierlannes2019" "proof of Cor. 2.3.6, p. 36 (|R(L)| = 480)"]
theorem card_rootSet_sixteen {Q : QuadForm ℤ 16} (hQ : IsEvenUnimodular Q) : (rootSet Q).ncard = 480 := by
  rw [ncard_rootSet]
  simpa [ArithmeticFunction.sigma_apply] using repNum_sixteen hQ (m := 1) le_rfl

/-- **$h(L) = 30$ for $n = 8$** (Chenevier–Lannes, proof of Corollary 2.3.5, p. 36, with Proposition-Definition 2.3.3 (c),
p. 35: $|R(L)| = n\,h(L)$). Unconditional. -/
@[kb "chenevierlannes2019" "proof of Cor. 2.3.5, p. 36 (h(L) = 30)"]
theorem coxeterNumber_eight {Q : QuadForm ℤ 8} (hQ : IsEvenUnimodular Q) : coxeterNumber Q = 30 := by
  have h : repNum Q 1 = 240 := by rw [← ncard_rootSet]; exact card_rootSet_eight hQ
  rw [coxeterNumber, h]
  norm_num

/-- **$h(L) = 30$ for $n = 16$** (Chenevier–Lannes, proof of Corollary 2.3.6, p. 36). Unconditional. -/
@[kb "chenevierlannes2019" "proof of Cor. 2.3.6, p. 36 (h(L) = 30)"]
theorem coxeterNumber_sixteen {Q : QuadForm ℤ 16} (hQ : IsEvenUnimodular Q) : coxeterNumber Q = 30 := by
  have h : repNum Q 1 = 480 := by rw [← ncard_rootSet]; exact card_rootSet_sixteen hQ
  rw [coxeterNumber, h]
  norm_num

/-- **The theta series of a Niemeier lattice** (Chenevier–Lannes, §1.1, p. 2, and the proof of Proposition-Definition
2.3.3, p. 35, for $n = 24$: $\vartheta_L = E_{12} + (|R(L)| - \frac{65520}{691})\Delta$): for every even unimodular
lattice of dimension $24$ and $m \ge 1$,
$$r_L(m) = \tfrac{65520}{691}\,\sigma_{11}(m) + \bigl(|R(L)| - \tfrac{65520}{691}\bigr)\,\tau(m),$$
with $\tau$ Ramanujan's function (`Lattices.ramanujanTau`). Unconditional (Cassels' `Lattices.repNum_rank24`). -/
@[kb "chenevierlannes2019" "§1.1, p. 2; Prop.-Def. 2.3.3, p. 35 (θ_L for n = 24)"]
theorem repNum_twentyFour {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q) {m : ℕ} (hm : 1 ≤ m) :
    (repNum Q m : ℂ) = 65520 / 691 * σ 11 m + ((rootSet Q).ncard - 65520 / 691) * ramanujanTau m := by
  have h := repNum_rank24 hQ.posDef hQ.det_one hm
  rw [E_qExpansion_coeff (k := 12) _ ⟨6, rfl⟩, E_qExpansion_coeff (k := 12) _ ⟨6, rfl⟩, if_neg (by omega),
    if_neg one_ne_zero, bernoulli_twelve_val] at h
  rw [h, ncard_rootSet]
  simp [ArithmeticFunction.sigma_apply]
  ring

end QuadFormsKB.ChenevierLannes
