/-
# Global residue systems for the local coset sums (for the singular series)

**Layer:** local at a finite place $v$ of a number field $F$, with global input from $\mathcal O_F$.

**Setting.** $F_v$ is the completion of $F$ at $v$, $|\cdot|_v$ its valuation (`Valued.v`), $c \in \mathcal O_F\setminus\{0\}$,
$e = v_{\mathfrak p}(c\mathcal O_F)$ (`ordI`).

**Results.**
* `valued_algebraMap_int_eq`: $|c|_v = \exp(-e)$ (that is, $q_v^{-e}$).
* `valued_algebraMap_int_le_iff`: for $o \in \mathcal O_F$, $|o|_v \le \exp(-k)$ iff $o \in \mathfrak p^k$.
* `exists_int_approx`: every $y \in F_v$ with $|y|_v \le 1$ is within $\exp(-k)$ of an element of $\mathcal O_F$.
* `resRho` (**the residue system**): $x \in \mathcal O_F/\mathfrak p^{e} \mapsto \tilde x / c \in F_v$, with
  `resRho_le`: $|\rho(x)|_v \le \exp(e)$, and `resRho_unique`: every $y \in F_v$ with $|y|_v \le \exp(e)$ is
  $\equiv \rho(x) \pmod{\mathcal O_v}$ for a unique $x$, i.e.
  $$ \{y \in F_v : |y|_v \le \exp(e)\}/\mathcal O_v \;\cong\; \tfrac1c\,\mathcal O_F/\mathfrak p^e \mathcal O_F. $$
* `resRho_int_of_not_dvd`: if $e = 0$ then $o/c \in \mathcal O_v$ for all $o \in \mathcal O_F$.
-/
import QuadFormsKB.SiegelWeil.Forms.SingularSeriesRLocal
import QuadFormsKB.SiegelWeil.SingularSeriesNF

open IsDedekindDomain NumberField WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

open QuadFormsKB.SiegelWeil.SingularNF

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "ιO" => algebraMap (𝓞 F) F

variable (v : HeightOneSpectrum (𝓞 F))

/-- The completion valuation of an element of $F$ is the global valuation. -/
lemma valued_algebraMap_eq (z : F) :
    Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) (K := F) v z

/-- **The $v$-adic absolute value of a nonzero integer**: $|c|_v = \exp(-v_{\mathfrak p}(c\mathcal O_F))$. -/
theorem valued_algebraMap_int_eq (c : 𝓞 F) (hc : c ≠ 0) :
    Valued.v (algebraMap F (v.adicCompletion F) (ιO c)) =
      exp (-(ordI v (Ideal.span {c}) : ℤ)) := by
  rw [valued_algebraMap_eq, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg v hc]
  rfl

/-- For $o \in \mathcal O_F$: $|o|_v \le \exp(-k)$ iff $o \in \mathfrak p^k$. -/
theorem valued_algebraMap_int_le_iff (o : 𝓞 F) (k : ℕ) :
    Valued.v (algebraMap F (v.adicCompletion F) (ιO o)) ≤ exp (-(k : ℤ)) ↔ o ∈ v.asIdeal ^ k := by
  rw [valued_algebraMap_eq, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_le_pow_iff_dvd, Ideal.dvd_span_singleton]

/-- **Integral approximation**: every $y \in F_v$ with $|y|_v \le 1$ is within $\exp(-k)$ of an element of $\mathcal O_F$. -/
theorem exists_int_approx (y : v.adicCompletion F) (hy : Valued.v y ≤ 1) (k : ℕ) :
    ∃ o : 𝓞 F, Valued.v (y - algebraMap F (v.adicCompletion F) (ιO o)) ≤ exp (-(k : ℤ)) := by
  obtain ⟨y0, hy0⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective (K := F) v (exp (-(k : ℤ)))
  have hy00 : (Valued.v y0 : ℤᵐ⁰) ≠ 0 := by rw [hy0]; exact exp_ne_zero
  have hr0 : (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).restrict y0 ≠ 0 := by simpa using hy00
  set γ := Units.mk0 _ hr0
  have hU : {z : v.adicCompletion F | Valued.v (z - y) < exp (-(k : ℤ))} ∈ nhds y := by
    rw [Valued.mem_nhds]
    refine ⟨γ, fun z hz => ?_⟩
    have hz' : (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).restrict (z - y) <
        (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).restrict y0 := hz
    rw [Valuation.restrict_lt_iff, hy0] at hz'
    exact hz'
  have hd : DenseRange (algebraMap F (v.adicCompletion F)) := HeightOneSpectrum.denseRange_algebraMap F v
  obtain ⟨_, hz, z, rfl⟩ := mem_closure_iff_nhds.mp (by rw [hd.closure_range]; trivial) _ hU
  have hzy : Valued.v (y - algebraMap F (v.adicCompletion F) z) < exp (-(k : ℤ)) := by
    rw [Valuation.map_sub_swap]; exact hz
  have hzle : Valued.v (algebraMap F (v.adicCompletion F) z) ≤ 1 := by
    have : algebraMap F (v.adicCompletion F) z = y - (y - algebraMap F (v.adicCompletion F) z) := by ring
    rw [this]
    refine (Valuation.map_sub _ _ _).trans (max_le hy ?_)
    exact hzy.le.trans (exp_le_one_iff.mpr (by simp))
  rw [valued_algebraMap_eq] at hzle
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer (R := 𝓞 F) (K := F) v hzle
    (Units.mk0 (exp (-(k : ℤ))) exp_ne_zero)
  refine ⟨a, ?_⟩
  have h1 : y - algebraMap F (v.adicCompletion F) (ιO a) =
      (y - algebraMap F (v.adicCompletion F) z) + (algebraMap F (v.adicCompletion F) z -
        algebraMap F (v.adicCompletion F) (ιO a)) := by ring
  rw [h1]
  refine (Valuation.map_add _ _ _).trans (max_le hzy.le ?_)
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) z - algebraMap F (v.adicCompletion F) (ιO a)) <
      exp (-(k : ℤ)) := by
    rw [← map_sub, valued_algebraMap_eq, Valuation.map_sub_swap]
    exact ha
  exact h2.le

/-- $\mathcal O_F/\mathfrak p^k$ is finite. -/
instance instFintypeQuotPow (k : ℕ) : Fintype (𝓞 F ⧸ v.asIdeal ^ k) :=
  haveI : Finite (𝓞 F ⧸ v.asIdeal ^ k) :=
    finite_quot (pow_ne_zero k v.ne_bot)
  Fintype.ofFinite _

/-- **The residue system** $x \mapsto \tilde x/c \in F_v$ for $x \in \mathcal O_F/\mathfrak p^{e}$, $e = v_{\mathfrak p}(c)$. -/
def resRho (c : 𝓞 F) (v : HeightOneSpectrum (𝓞 F))
    (x : 𝓞 F ⧸ v.asIdeal ^ ordI v (Ideal.span {c})) :
    v.adicCompletion F :=
  algebraMap F (v.adicCompletion F) (ιO (Quotient.out x) / ιO c)

/-- Integers have $|o|_v \le 1$. -/
lemma valued_int_le_one (o : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (ιO o)) ≤ 1 := by
  have := (valued_algebraMap_int_le_iff v o 0).mpr (by simp)
  simpa using this

/-- $|o/c|_v = |o|_v \exp(e)$. -/
lemma valued_div_int (c : 𝓞 F) (hc : c ≠ 0) (o : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (ιO o / ιO c)) =
      Valued.v (algebraMap F (v.adicCompletion F) (ιO o)) *
        exp (ordI v (Ideal.span {c}) : ℤ) := by
  rw [map_div₀, map_div₀, div_eq_mul_inv, valued_algebraMap_int_eq v c hc, ← exp_neg, neg_neg]

/-- $|\rho(x)|_v \le \exp(e)$. -/
theorem resRho_le {c : 𝓞 F} (hc : c ≠ 0) (x : 𝓞 F ⧸ v.asIdeal ^ ordI v (Ideal.span {c})) :
    Valued.v (resRho c v x) ≤ exp (ordI v (Ideal.span {c}) : ℤ) := by
  unfold resRho
  rw [valued_div_int v c hc]
  calc _ ≤ 1 * exp (ordI v (Ideal.span {c}) : ℤ) :=
        mul_le_mul' (valued_int_le_one v _) le_rfl
    _ = _ := one_mul _

/-- If $c$ is a unit at $v$ ($e = 0$) then $o/c \in \mathcal O_v$. -/
theorem resRho_int_of_not_dvd {c : 𝓞 F} (hc : c ≠ 0)
    (he : ordI v (Ideal.span {c}) = 0) (o : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (ιO o / ιO c)) ≤ 1 := by
  rw [valued_div_int v c hc, he]
  simpa using valued_int_le_one v o

/-- Lifting through the quotient. -/
lemma mk_out_sub_mem (e : ℕ) (x : 𝓞 F ⧸ v.asIdeal ^ e) (o : 𝓞 F) (h : Ideal.Quotient.mk _ o = x) :
    o - Quotient.out x ∈ v.asIdeal ^ e := by
  rw [← Ideal.Quotient.eq, h]
  exact (Ideal.Quotient.mk_out x).symm

/-- **Residue system**: every $y \in F_v$ with $|y|_v \le \exp(e)$ is $\equiv \rho(x) \pmod{\mathcal O_v}$ for a unique $x$. -/
theorem resRho_unique {c : 𝓞 F} (hc : c ≠ 0) :
    ∀ y : v.adicCompletion F, Valued.v y ≤ exp (ordI v (Ideal.span {c}) : ℤ) →
      ∃! x, Valued.v (y - resRho c v x) ≤ 1 := by
  intro y hy
  have hvc : Valued.v (algebraMap F (v.adicCompletion F) (ιO c)) = exp (-(ordI v (Ideal.span {c}) : ℤ)) :=
    valued_algebraMap_int_eq v c hc
  have hc'0 : algebraMap F (v.adicCompletion F) (ιO c) ≠ 0 := by
    intro h; rw [h, map_zero] at hvc; exact exp_ne_zero hvc.symm
  have hdiv : ∀ a : v.adicCompletion F, Valued.v a ≤ exp (-(ordI v (Ideal.span {c}) : ℤ)) →
      Valued.v (a / algebraMap F (v.adicCompletion F) (ιO c)) ≤ 1 := by
    intro a ha
    rw [map_div₀, hvc]
    exact (div_le_one₀ (zero_lt_iff.mpr exp_ne_zero)).mpr ha
  refine existsUnique_of_exists_of_unique ?_ ?_
  · -- existence
    have ht : Valued.v (y * algebraMap F (v.adicCompletion F) (ιO c)) ≤ 1 := by
      rw [map_mul, hvc]
      calc _ ≤ exp (ordI v (Ideal.span {c}) : ℤ) * exp (-(ordI v (Ideal.span {c}) : ℤ)) :=
            mul_le_mul' hy le_rfl
        _ = 1 := by rw [← exp_add]; simp
    obtain ⟨o, ho⟩ := exists_int_approx v (y * algebraMap F (v.adicCompletion F) (ιO c)) ht
      (ordI v (Ideal.span {c}))
    refine ⟨Ideal.Quotient.mk _ o, ?_⟩
    have hm := (valued_algebraMap_int_le_iff v _ (ordI v (Ideal.span {c}))).mpr
      (mk_out_sub_mem v _ _ o rfl)
    have key : y - resRho c v (Ideal.Quotient.mk _ o) =
        ((y * algebraMap F (v.adicCompletion F) (ιO c) - algebraMap F (v.adicCompletion F) (ιO o)) +
          algebraMap F (v.adicCompletion F)
            (ιO (o - Quotient.out (Ideal.Quotient.mk (v.asIdeal ^ ordI v (Ideal.span {c})) o)))) /
          algebraMap F (v.adicCompletion F) (ιO c) := by
      unfold resRho
      simp only [map_div₀, map_sub]
      field_simp
      ring
    rw [key]
    exact hdiv _ ((Valuation.map_add _ _ _).trans (max_le ho hm))
  · intro x x' hx hx'
    have h1 : algebraMap F (v.adicCompletion F) (ιO (Quotient.out x - Quotient.out x')) /
        algebraMap F (v.adicCompletion F) (ιO c) =
        (y - resRho c v x') - (y - resRho c v x) := by
      unfold resRho
      simp only [map_div₀, map_sub]
      field_simp
      ring
    have h2 : Valued.v (algebraMap F (v.adicCompletion F) (ιO (Quotient.out x - Quotient.out x')) /
        algebraMap F (v.adicCompletion F) (ιO c)) ≤ 1 := by
      rw [h1]
      exact (Valuation.map_sub _ _ _).trans (max_le hx' hx)
    rw [map_div₀, hvc] at h2
    have h3 : Valued.v (algebraMap F (v.adicCompletion F) (ιO (Quotient.out x - Quotient.out x'))) ≤
        exp (-(ordI v (Ideal.span {c}) : ℤ)) :=
      (div_le_one₀ (zero_lt_iff.mpr exp_ne_zero)).mp h2
    have h4 := (valued_algebraMap_int_le_iff v _ _).mp h3
    rw [← Ideal.Quotient.eq] at h4
    simpa using h4

end QuadFormsKB.SiegelWeil.Forms
