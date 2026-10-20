/-
# Hilbert Eisenstein series IV: level $\mathfrak N$ and a character $\chi$, $k \ge 3$

Let $\mathfrak N \ne 0$ be an integral ideal and $\chi$ a character of $(\mathcal{O}_F/\mathfrak N)$ (a `MulChar`, $0$ on non-units).
The **Eisenstein series of level $\mathfrak N$ and character $\chi$** is $E_{k,\chi} = E_{W_\chi,k}$ with
$$W_\chi(c, d) = \chi(d \bmod \mathfrak N)^{-1}\ \text{ if } c \in \mathfrak N,\ d \in \mathcal{O}_F, \qquad W_\chi = 0 \text{ otherwise}
  \qquad (\texttt{chiWeight}),$$
i.e. $E_{k,\chi}(z) = \sum_{(c,d) \in U\backslash(\mathfrak N\times\mathcal{O}_F)}\bar\chi(d)\,N(cz+d)^{-k}$ ($\bar\chi = \chi^{-1}$ on units).

**Parity condition** (`hχ`): $\chi(\varepsilon) = N(\varepsilon)^k$ for every unit $\varepsilon$ ($N(\varepsilon) = \pm1$); this is exactly the
unit equivariance of $W_\chi$ (`isUnitEquivariant_chiWeight`). It is the finite part of the condition that $\chi\,\mathrm{sgn}^k$ be
trivial on units, i.e. that $\chi$ come from a Hecke character of infinity type $\mathrm{sgn}^k$; it contains
$\chi(-1) = (-1)^{dk}$. Without it the series over pairs modulo units is not defined. It holds for the theta character
$\chi_Q$ of an $n = 2k$-ary form, since $\theta_Q(\varepsilon^2z) = \theta_Q(z)$.

**Results** ($k \ge 3$):
* `slashWeight_chiWeight`, `eisChar_slash_gamma0`: $E_{k,\chi}\,|_k\,\gamma = \chi(\gamma_{11})\,E_{k,\chi}$ for
  $\gamma \in \Gamma_0(\mathfrak N) \subseteq \mathrm{SL}_2(\mathcal{O}_F)$ ($\gamma_{11} = d$, 0-based), the convention of `modularFormChar`;
* `eisChar_mem_modularFormChar`: $E_{k,\chi} \in M_k(\Gamma_0(\mathfrak N), \chi)$, for every degree $d \ge 1$;
* `tendsto_eisChar_slash`: at every cusp $A\infty$, $A \in \mathrm{SL}_2(F)$, $E_{k,\chi}|A \to \mathrm{c}_\infty((W_\chi)_A)$; at $\infty$
  ($A = 1$) the constant term is $\sum_{d \in U\backslash(\mathcal{O}_F\setminus0)}\bar\chi(d)N(d)^{-k}$ (`eisConst_chiWeight`).

*Convention:* $\chi$ is applied to the $d$-entry, the same as `modularFormChar` ($f|\gamma = \chi(d)f$); the weight uses
$\chi^{-1}$ because $W(y\gamma^{-1})$ involves $d\,\gamma_{00} \equiv d\,\gamma_{11}^{-1}$.

Sources: Shimura (Duke 1978), (3.4)–(3.5) [unverified]; Garrett (1990), Ch. 3 [unverified]; Freitag (1990), Ch. I §5
[unverified].
-/
import QuadFormsKB.HilbertModular.EisensteinForms

open Complex Matrix NumberField UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-! ### The weight -/

/-- $x = (c, d)$ with $c \in \mathfrak N$ and $d \in \mathcal{O}_F$. -/
def InLevel (𝔑 : Ideal (𝓞 F)) (x : F × F) : Prop :=
  ∃ p : 𝓞 F × 𝓞 F, p.1 ∈ 𝔑 ∧ (algebraMap (𝓞 F) F p.1, algebraMap (𝓞 F) F p.2) = x

open Classical in
/-- **The weight of $E_{k,\chi}$**: $W_\chi(c, d) = \chi(d \bmod \mathfrak N)^{-1}$ for $c \in \mathfrak N$, $d \in \mathcal{O}_F$, and
$0$ otherwise. Parameters: `𝔑` (the level), `χ` (a character of $\mathcal{O}_F/\mathfrak N$). -/
@[kb "shimura1978" "(3.4)–(3.5), Eisenstein series of level 𝔑 with character [unverified]"]
noncomputable def chiWeight (𝔑 : Ideal (𝓞 F)) (χ : MulChar (𝓞 F ⧸ 𝔑) ℂ) (x : F × F) : ℂ :=
  if h : InLevel 𝔑 x then (χ (Ideal.Quotient.mk 𝔑 h.choose.2))⁻¹ else 0

variable {𝔑 : Ideal (𝓞 F)} {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ}

lemma algebraMap_O_injective : Function.Injective (algebraMap (𝓞 F) F) :=
  IsFractionRing.injective (𝓞 F) F

lemma chiWeight_coe {c : 𝓞 F} (hc : c ∈ 𝔑) (d : 𝓞 F) :
    chiWeight 𝔑 χ (algebraMap (𝓞 F) F c, algebraMap (𝓞 F) F d) =
      (χ (Ideal.Quotient.mk 𝔑 d))⁻¹ := by
  have h : InLevel 𝔑 (algebraMap (𝓞 F) F c, algebraMap (𝓞 F) F d) := ⟨(c, d), hc, rfl⟩
  rw [chiWeight, dite_cond_eq_true (eq_true h)]
  have := (Prod.ext_iff.mp h.choose_spec.2).2
  rw [algebraMap_O_injective this]

lemma chiWeight_of_not {x : F × F} (h : ¬ InLevel 𝔑 x) : chiWeight 𝔑 χ x = 0 := by
  rw [chiWeight, dite_cond_eq_false (eq_false h)]

lemma unit_smul_eq (ε : (𝓞 F)ˣ) (a : F) : ε • a = algebraMap (𝓞 F) F (ε : 𝓞 F) * a := by
  rw [Units.smul_def, Algebra.smul_def]

lemma inLevel_smul_iff (ε : (𝓞 F)ˣ) (x : F × F) : InLevel 𝔑 (ε • x) ↔ InLevel 𝔑 x := by
  constructor
  · rintro ⟨p, hp, hpx⟩
    refine ⟨(((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * p.1, ((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * p.2), 𝔑.mul_mem_left _ hp, ?_⟩
    have h1 := (Prod.ext_iff.mp hpx).1
    have h2 := (Prod.ext_iff.mp hpx).2
    simp only [smul_fst, smul_snd] at h1 h2
    ext
    · simp only [map_mul, h1]
      rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    · simp only [map_mul, h2]
      rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  · rintro ⟨p, hp, rfl⟩
    exact ⟨((ε : 𝓞 F) * p.1, (ε : 𝓞 F) * p.2), 𝔑.mul_mem_left _ hp, by ext <;> simp [unit_smul_eq]⟩

lemma toF_apply (γ : SL(2, 𝓞 F)) (i j : Fin 2) : (toF F γ) i j = algebraMap (𝓞 F) F (γ i j) := rfl

lemma inLevel_rowMul {x : F × F} (hx : InLevel 𝔑 x) {γ : SL(2, 𝓞 F)} (hγ : γ ∈ Gamma0R 𝔑) :
    InLevel 𝔑 (rowMul x (toF F γ)) := by
  obtain ⟨p, hp, rfl⟩ := hx
  refine ⟨(p.1 * γ 0 0 + p.2 * γ 1 0, p.1 * γ 0 1 + p.2 * γ 1 1),
    𝔑.add_mem (𝔑.mul_mem_right _ hp) (𝔑.mul_mem_left _ hγ), ?_⟩
  ext <;> simp [rowMul, toF_apply]

/-- $\chi(\gamma_{00})^{-1} = \chi(\gamma_{11})$ on $\Gamma_0(\mathfrak N)$ ($\gamma_{00}\gamma_{11} \equiv 1$). -/
lemma chi_inv_eq_of_gamma0 {γ : SL(2, 𝓞 F)} (hγ : γ ∈ Gamma0R 𝔑) :
    (χ (Ideal.Quotient.mk 𝔑 (γ 0 0)))⁻¹ = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) := by
  have hdet := γ.2
  rw [det_fin_two] at hdet
  have hc : Ideal.Quotient.mk 𝔑 (γ 1 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hγ
  have h1 : Ideal.Quotient.mk 𝔑 (γ 0 0) * Ideal.Quotient.mk 𝔑 (γ 1 1) = 1 := by
    have := congrArg (Ideal.Quotient.mk 𝔑) hdet
    simpa only [map_sub, map_mul, hc, mul_zero, sub_zero, map_one] using this
  have h2 : χ (Ideal.Quotient.mk 𝔑 (γ 0 0)) * χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) = 1 := by
    rw [← map_mul, h1, map_one]
  exact inv_eq_of_mul_eq_one_right h2

/-- **The $\Gamma_0(\mathfrak N)$-law of the weight**: $W_\chi(y\gamma^{-1}) = \chi(\gamma_{11})W_\chi(y)$ for
$\gamma \in \Gamma_0(\mathfrak N)$. -/
theorem slashWeight_chiWeight {γ : SL(2, 𝓞 F)} (hγ : γ ∈ Gamma0R 𝔑) :
    slashWeight (chiWeight 𝔑 χ) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • chiWeight 𝔑 χ := by
  funext y
  simp only [slashWeight, Pi.smul_apply, smul_eq_mul]
  have hγ' : γ⁻¹ ∈ Gamma0R 𝔑 := (Gamma0R 𝔑).inv_mem hγ
  have hinv : (toF F γ)⁻¹ = toF F γ⁻¹ := (map_inv (toF F) γ).symm
  by_cases hy : InLevel 𝔑 y
  · obtain ⟨p, hp, rfl⟩ := hy
    rw [chiWeight_coe hp, hinv]
    have hrow : rowMul (algebraMap (𝓞 F) F p.1, algebraMap (𝓞 F) F p.2) (toF F γ⁻¹) =
        (algebraMap (𝓞 F) F (p.1 * γ⁻¹ 0 0 + p.2 * γ⁻¹ 1 0),
          algebraMap (𝓞 F) F (p.1 * γ⁻¹ 0 1 + p.2 * γ⁻¹ 1 1)) := by
      ext <;> simp [rowMul, toF_apply]
    rw [hrow, chiWeight_coe (𝔑.add_mem (𝔑.mul_mem_right _ hp) (𝔑.mul_mem_left _ hγ'))]
    have hpc : Ideal.Quotient.mk 𝔑 p.1 = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
    have h11 : γ⁻¹ 1 1 = γ 0 0 := by simp [SpecialLinearGroup.coe_inv, adjugate_fin_two]
    rw [map_add, map_mul, map_mul, hpc, zero_mul, zero_add, h11, map_mul, mul_inv,
      chi_inv_eq_of_gamma0 hγ, mul_comm]
  · have hy' : ¬ InLevel 𝔑 (rowMul y (toF F γ)⁻¹) := by
      intro h
      apply hy
      have := inLevel_rowMul h hγ
      rwa [rowMul_inv_rowMul] at this
    rw [chiWeight_of_not hy, chiWeight_of_not hy', mul_zero]

/-- **Parity**: $W_\chi$ is unit-equivariant of weight $k$ iff (here: if) $\chi(\varepsilon) = N(\varepsilon)^k$ for all units. -/
theorem isUnitEquivariant_chiWeight {k : ℤ}
    (hχ : ∀ ε : (𝓞 F)ˣ, χ (Ideal.Quotient.mk 𝔑 (ε : 𝓞 F)) = ((unitNorm ε : ℝ) : ℂ) ^ k) :
    IsUnitEquivariant (chiWeight 𝔑 χ) k := by
  intro ε x
  by_cases hx : InLevel 𝔑 x
  · obtain ⟨p, hp, rfl⟩ := hx
    have : ε • (algebraMap (𝓞 F) F p.1, algebraMap (𝓞 F) F p.2) =
        (algebraMap (𝓞 F) F ((ε : 𝓞 F) * p.1), algebraMap (𝓞 F) F ((ε : 𝓞 F) * p.2)) := by
      ext <;> simp [unit_smul_eq]
    rw [this, chiWeight_coe (𝔑.mul_mem_left _ hp), chiWeight_coe hp, map_mul, map_mul, mul_inv, hχ]
    -- `N(ε)^k` is its own inverse
    have hu : (((unitNorm ε : ℝ) : ℂ) ^ k)⁻¹ = ((unitNorm ε : ℝ) : ℂ) ^ k := by
      have hsq : ((unitNorm ε : ℝ) : ℂ) * ((unitNorm ε : ℝ) : ℂ) = 1 := by
        rw [← ofReal_mul, ← sq, ← sq_abs, abs_unitNorm]; simp
      rw [← _root_.inv_zpow, inv_eq_of_mul_eq_one_right hsq]
    rw [hu]
  · rw [chiWeight_of_not hx, chiWeight_of_not ((inLevel_smul_iff ε x).not.mpr hx), mul_zero]

lemma norm_chi_inv_le (h𝔑 : 𝔑 ≠ ⊥) (a : 𝓞 F ⧸ 𝔑) : ‖(χ a)⁻¹‖ ≤ 1 := by
  have := Ideal.finiteQuotientOfFreeOfNeBot 𝔑 h𝔑
  by_cases h : IsUnit a
  · have hn : ‖χ a‖ = 1 := by
      refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.card_pos (α := (𝓞 F ⧸ 𝔑)ˣ)).ne').mp ?_
      rw [← norm_pow, ← h.unit_spec, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one',
        Units.val_one, map_one, norm_one]
    rw [norm_inv, hn, inv_one]
  · rw [χ.map_nonunit h, _root_.inv_zero, norm_zero]; exact zero_le_one

/-- **$W_\chi$ is admissible** (`EisWeight`): supported on $\mathcal{O}_F^2$, bounded by $1$, unit-equivariant under the parity
condition. -/
theorem eisWeight_chiWeight (h𝔑 : 𝔑 ≠ ⊥) {k : ℤ}
    (hχ : ∀ ε : (𝓞 F)ˣ, χ (Ideal.Quotient.mk 𝔑 (ε : 𝓞 F)) = ((unitNorm ε : ℝ) : ℂ) ^ k) :
    EisWeight (chiWeight 𝔑 χ) k := by
  refine ⟨isUnitEquivariant_chiWeight hχ, ⟨1, fun x hx => ?_⟩, ⟨1, fun x => ?_⟩⟩
  · by_cases h : InLevel 𝔑 x
    · obtain ⟨p, -, rfl⟩ := h
      exact ⟨(FractionalIdeal.mem_one_iff _).mpr ⟨p.1, rfl⟩,
        (FractionalIdeal.mem_one_iff _).mpr ⟨p.2, rfl⟩⟩
    · exact absurd (chiWeight_of_not h) hx
  · by_cases h : InLevel 𝔑 x
    · obtain ⟨p, hp, rfl⟩ := h
      rw [chiWeight_coe hp]; exact norm_chi_inv_le h𝔑 _
    · rw [chiWeight_of_not h, norm_zero]; exact zero_le_one

/-- **$W_\chi$ has level $\mathfrak N$**: invariant under $\Gamma(\mathfrak N)$ (where $\gamma_{11} \equiv 1$). -/
theorem hasLevel_chiWeight : HasLevel (chiWeight 𝔑 χ) 𝔑 := by
  rintro _ ⟨γ, hγ, rfl⟩
  have h1 := (mem_Gamma1R 𝔑).mp (GammaFullR_le_Gamma1R 𝔑 hγ)
  rw [slashWeight_chiWeight h1.1, h1.2, map_one, one_smul]

/-! ### The Eisenstein series -/

/-- **The Hilbert Eisenstein series of parallel weight $k$, level $\mathfrak N$ and character $\chi$**:
$$E_{k,\chi}(z) = \sum_{(c,d) \in U\backslash(\mathfrak N\times\mathcal{O}_F)}\chi(d)^{-1}\,N(cz + d)^{-k}.$$ -/
@[kb "shimura1978" "(3.4)–(3.5), E_k(z; χ) for Γ₀(𝔑) [unverified]"]
noncomputable def eisChar (𝔑 : Ideal (𝓞 F)) (χ : MulChar (𝓞 F ⧸ 𝔑) ℂ) (k : ℤ) :
    (InfinitePlace F → ℍ) → ℂ :=
  eisSeries (chiWeight 𝔑 χ) k

/-- **The $\Gamma_0(\mathfrak N)$-law**: $E_{k,\chi}\,|_k\,\gamma = \chi(\gamma_{11})\,E_{k,\chi}$ for $\gamma \in \Gamma_0(\mathfrak N)$
(no convergence hypothesis needed). -/
@[kb "shimura1978" "§3, transformation law of E_k(z; χ) under Γ₀(𝔑) [unverified]"]
theorem eisChar_slash_gamma0 {k : ℤ}
    (hχ : ∀ ε : (𝓞 F)ˣ, χ (Ideal.Quotient.mk 𝔑 (ε : 𝓞 F)) = ((unitNorm ε : ℝ) : ℂ) ^ k)
    {γ : SL(2, 𝓞 F)} (hγ : γ ∈ Gamma0R 𝔑) :
    eisChar 𝔑 χ k ∣[k] slHom (realEmb F) (toF F γ) =
      χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • eisChar 𝔑 χ k :=
  eisSeries_slash_of_weight (isUnitEquivariant_chiWeight hχ) _ (slashWeight_chiWeight hγ)

/-- **$E_{k,\chi} \in M_k(\Gamma_0(\mathfrak N), \chi)$** for $k \ge 3$, $\mathfrak N \ne 0$, $\chi(\varepsilon) = N(\varepsilon)^k$ on units; every
degree $d \ge 1$ (the cusp condition is proved directly from the constant terms, `tendsto_eisSeries_slash`). -/
@[kb "shimura1978" "§3, E_k(z; χ) ∈ M_k(Γ₀(𝔑), χ) [unverified]"]
theorem eisChar_mem_modularFormChar (h𝔑 : 𝔑 ≠ ⊥) {k : ℤ} (hk : 3 ≤ k)
    (hχ : ∀ ε : (𝓞 F)ˣ, χ (Ideal.Quotient.mk 𝔑 (ε : 𝓞 F)) = ((unitNorm ε : ℝ) : ℂ) ^ k) :
    eisChar 𝔑 χ k ∈ modularFormChar 𝔑 χ k := by
  have hW := eisWeight_chiWeight h𝔑 hχ
  refine ⟨⟨?_, isHolomorphic_eisSeries hW hk, fun A => ?_⟩, fun γ hγ => eisChar_slash_gamma0 hχ hγ⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    have h1 := (mem_Gamma1R 𝔑).mp hγ
    rw [eisChar_slash_gamma0 hχ h1.1, h1.2, map_one, one_smul]
  · exact (tendsto_eisSeries_slash hW hk h𝔑 hasLevel_chiWeight A).isBigO_one ℝ

/-- **Constant terms of $E_{k,\chi}$ at every cusp** ($k \ge 3$): for $A \in \mathrm{SL}_2(F)$,
$(E_{k,\chi}\,|_k\,A)(z) \to \mathrm{c}_\infty\big((W_\chi)_A\big) = \sum_{y\in U\backslash F^2,\ y_0 = 0}W_\chi(yA^{-1})N(y_1)^{-k}$. -/
@[kb "freitag1990" "Ch. I §5, constant terms of E_k(z; χ) at the cusps [unverified]"]
theorem tendsto_eisChar_slash (h𝔑 : 𝔑 ≠ ⊥) {k : ℤ} (hk : 3 ≤ k)
    (hχ : ∀ ε : (𝓞 F)ˣ, χ (Ideal.Quotient.mk 𝔑 (ε : 𝓞 F)) = ((unitNorm ε : ℝ) : ℂ) ^ k)
    (A : SL(2, F)) :
    Tendsto (eisChar 𝔑 χ k ∣[k] slHom (realEmb F) A) atImInftyPi
      (𝓝 (eisConst (slashWeight (chiWeight 𝔑 χ) A) k)) :=
  tendsto_eisSeries_slash (eisWeight_chiWeight h𝔑 hχ) hk h𝔑 hasLevel_chiWeight A

end QuadFormsKB.HilbertModular
