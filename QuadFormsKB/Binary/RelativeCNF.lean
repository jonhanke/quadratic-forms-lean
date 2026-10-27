import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelativeLFactor

/-!
# The relative class number formula for a CM extension $E/F$

Let $F$ be a **totally real** number field of degree $d = [F:\mathbb{Q}]$ and $E/F$ a **totally imaginary** quadratic
extension (a CM extension; e.g. $E = F(\sqrt{-\delta})$ with $\delta \gg 0$). Then
$r_1(F) = d$, $r_2(F) = 0$, $r_1(E) = 0$, $r_2(E) = d$ (`nrRealPlaces_base`, …, `nrComplexPlaces_top`) and $w_F = 2$
(`torsionOrder_eq_two`). With $L(s, \chi_{E/F})$ the Euler product of the splitting character (`relLR`,
`RelativeLFactor.lean`) and Mathlib's residues $\rho_K = 2^{r_1}(2\pi)^{r_2}h_KR_K/(w_K\sqrt{|d_K|})$:

**`relativeClassNumberFormula`:**
$$\lim_{s \to 1^+}L(s,\chi_{E/F}) = \frac{(2\pi)^d\,h_E\,R_E\,w_F\,\sqrt{|d_F|}}{2^d\,h_F\,R_F\,w_E\,\sqrt{|d_E|}}
  = \frac{(2\pi)^d\,h_E\,R_E\,\sqrt{|d_F|}}{2^{d-1}\,h_F\,R_F\,w_E\,\sqrt{|d_E|}}
  \quad(\texttt{relativeClassNumberFormula'}).$$

**Hasse's unit index.** For a CM field $K$ with maximal totally real subfield $K^+$ (Mathlib's `IsCMField`,
`maximalRealSubfield`), $Q_K = [\mathcal O_K^\times : \mu_K\mathcal O_{K^+}^\times] \in \{1, 2\}$
(`IsCMField.indexRealUnits`, `indexRealUnits_eq_one_or_two`) and $R_K/R_{K^+} = 2^{d-1}/Q_K$
(`regulator_div_regulator`, from Mathlib's `regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv`). Hence
(**`relativeClassNumberFormula_hasse`**)
$$\lim_{s \to 1^+}L(s,\chi_{K/K^+}) = \frac{(2\pi)^d\,h_K\,\sqrt{|d_{K^+}|}}{Q_K\,w_K\,h_{K^+}\,\sqrt{|d_K|}},
  \qquad\text{i.e.}\qquad h_K^- = \frac{h_K}{h_{K^+}} = \frac{Q_K\,w_K}{(2\pi)^d}\sqrt{\frac{|d_K|}{|d_{K^+}|}}\;L(1,\chi_{K/K^+})$$
(Washington, *Introduction to Cyclotomic Fields*, Ch. 4, Thm. 4.17 for $K = \mathbb{Q}(\zeta_n)$, where the product of the
$L(1,\chi)$ over the odd characters is our $L(1,\chi_{K/K^+})$). Example: $K = \mathbb{Q}(i)$, $d = 1$, $Q = 1$, $w = 4$,
$d_K = -4$ gives $L(1,\chi_{-4}) = 2\pi/(4\cdot 2) = \pi/4$.

**The norm-one torus.** In the setting of Weil's Tamagawa numbers, the norm-one torus $T = R^1_{E/F}\mathbb{G}_m$
(the special orthogonal group $\mathrm{SO}_2$ of the norm form of $E/F$) has Tamagawa number $\tau(T) = 2$ (Ono;
Weil, *Adeles and Algebraic Groups*, §3.5 [unverified locator] for $\mathrm{SO}_2$). The value $L(1,\chi_{E/F}) = \rho_E/\rho_F$ proved here is
exactly the convergence factor of the Tamagawa measure of $T$: $\operatorname{vol}(T(F)\backslash T(\mathbb A)^{(1)}) =
\tau(T)$ is computed from $\rho_E/\rho_F$ and the class number $h_E/h_F$ of $T$, and the formula above is the statement
$\tau(T) = 2$ after Ono's $\tau(T) = [H^1(F,\hat T)]/[\text{Ш}^1(F, T)]$ with $\hat T$ = the sign character. The
lemmas `tendsto_relLR` and `relativeClassNumberFormula` are the inputs for this volume; only the link is documented
here.

All results are unconditional (no cited inputs); the only hypotheses are the conditions "$F$ totally real", "$E$
totally complex", "$[E:F] = 2$" (Mathlib classes / a `finrank` equation).

Sources: Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Ch. 4, Thm. 4.12 (Hasse's unit index
$Q \in \{1,2\}$, $R_K/R_{K^+} = 2^{d-1}/Q$) and Thm. 4.17 (the relative class number formula); Neukirch, *Algebraic
Number Theory*, Ch. VII §5, Cor. 5.11 (residue of $\zeta_K$) [unverified locator]; Shimura, *Arithmetic of Quadratic
Forms*, §§ on relative quadratic extensions [unverified locator].
-/

open NumberField NumberField.InfinitePlace NumberField.Units IsDedekindDomain QuadFormsKB.NFEuler Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

/-! ### Torsion of a totally real field -/

set_option backward.isDefEq.respectTransparency false in
/-- **$w_F = 2$ for a number field with a real place:** the only roots of unity are $\pm 1$ (a primitive $k$-th root of
unity with $k > 2$ forces $r_1 = 0$). -/
theorem torsionOrder_eq_two_of_nrRealPlaces_pos (K : Type) [Field K] [NumberField K]
    (h : 0 < nrRealPlaces K) : torsionOrder K = 2 := by
  classical
  have key : ∀ x : torsion K, (x : (𝓞 K)ˣ) = 1 ∨ (x : (𝓞 K)ˣ) = -1 := by
    intro x
    by_cases! hc : 2 < orderOf (x : (𝓞 K)ˣ)
    · rw [← orderOf_units, ← orderOf_submonoid] at hc
      have := IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc (IsPrimitiveRoot.orderOf (x.1 : K))
      omega
    · interval_cases hi : orderOf (x : (𝓞 K)ˣ)
      · linarith [orderOf_pos_iff.2 ((CommGroup.mem_torsion x.1).1 x.2)]
      · exact Or.intro_left _ (orderOf_eq_one_iff.1 hi)
      · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
        simp [← Units.val_inj, ← Units.val_inj, Units.val_neg, Units.val_one, hi]
  let := Fintype.ofFinite (torsion K)
  rw [torsionOrder, Nat.card_eq_fintype_card]
  refine (Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩)
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  exact key x

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

/-! ### Places of a CM extension -/

section Places

variable [IsTotallyReal F] [IsTotallyComplex E]

theorem finrank_top (hdeg : Module.finrank F E = 2) :
    Module.finrank ℚ E = 2 * Module.finrank ℚ F := by
  rw [← Module.finrank_mul_finrank ℚ F E, hdeg, mul_comm]

/-- $r_1(F) = d$ for totally real $F$, $d = [F:\mathbb{Q}]$. -/
theorem nrRealPlaces_base : nrRealPlaces F = Module.finrank ℚ F := (IsTotallyReal.finrank F).symm

/-- $r_2(F) = 0$ for totally real $F$. -/
theorem nrComplexPlaces_base : nrComplexPlaces F = 0 := IsTotallyReal.nrComplexPlaces_eq_zero F

/-- $r_1(E) = 0$ for totally complex $E$. -/
theorem nrRealPlaces_top : nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E

/-- $r_2(E) = d = [F:\mathbb{Q}]$ for a totally complex quadratic extension $E$ of $F$. -/
theorem nrComplexPlaces_top (hdeg : Module.finrank F E = 2) :
    nrComplexPlaces E = Module.finrank ℚ F := by
  have h := IsTotallyComplex.finrank E
  rw [finrank_top hdeg] at h
  omega

/-- $w_F = 2$ for totally real $F$. -/
theorem torsionOrder_eq_two : torsionOrder F = 2 := by
  refine torsionOrder_eq_two_of_nrRealPlaces_pos F ?_
  rw [nrRealPlaces_base]; exact Module.finrank_pos

end Places

/-! ### The relative class number formula -/

/-- **The relative class number formula** (CM extension $E/F$: $F$ totally real of degree $d$, $E$ totally complex,
$[E:F] = 2$):
$$\lim_{s \to 1^+}L(s,\chi_{E/F}) = \frac{(2\pi)^d\,h_E\,R_E\,w_F\,\sqrt{|d_F|}}{2^d\,h_F\,R_F\,w_E\,\sqrt{|d_E|}},$$
$L$ = `relLR F E` (the Euler product over the primes of $F$), $h$ = `classNumber`, $R$ = `regulator`,
$w$ = `torsionOrder`, $d_K$ = `discr`. *Proof:* `tendsto_relLR` and Mathlib's residue formula with
$(r_1, r_2) = (d, 0)$ for $F$ and $(0, d)$ for $E$. -/
@[kb "washington1997" "Ch. 4, Thm. 4.17 (proof) [unverified locator]"]
theorem relativeClassNumberFormula [IsTotallyReal F] [IsTotallyComplex E] (hdeg : Module.finrank F E = 2) :
    Tendsto (relLR F E) (𝓝[>] 1)
      (𝓝 ((2 * Real.pi) ^ Module.finrank ℚ F * classNumber E * regulator E * torsionOrder F *
          Real.sqrt |(discr F : ℝ)| /
        (2 ^ Module.finrank ℚ F * classNumber F * regulator F * torsionOrder E *
          Real.sqrt |(discr E : ℝ)|))) := by
  convert tendsto_relLR hdeg using 2
  rw [dedekindZeta_residue_def, dedekindZeta_residue_def, nrRealPlaces_base (F := F),
    nrComplexPlaces_base (F := F), nrRealPlaces_top (E := E), nrComplexPlaces_top hdeg]
  have h1 := regulator_pos F
  have h2 : (0 : ℝ) < classNumber F := Nat.cast_pos.mpr (classNumber_pos F)
  have h3 : (0 : ℝ) < torsionOrder F := Nat.cast_pos.mpr (torsionOrder_pos F)
  have h4 : (0 : ℝ) < Real.sqrt |(discr F : ℝ)| :=
    Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero F)))
  have h5 : (0 : ℝ) < torsionOrder E := Nat.cast_pos.mpr (torsionOrder_pos E)
  have h6 : (0 : ℝ) < Real.sqrt |(discr E : ℝ)| :=
    Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero E)))
  field_simp

/-- **The relative class number formula with $w_F = 2$:**
$$\lim_{s \to 1^+}L(s,\chi_{E/F}) = \frac{2\,(2\pi)^d\,h_E\,R_E\,\sqrt{|d_F|}}{2^d\,h_F\,R_F\,w_E\,\sqrt{|d_E|}}.$$ -/
@[kb "washington1997" "Ch. 4, Thm. 4.17 (proof) [unverified locator]"]
theorem relativeClassNumberFormula' [IsTotallyReal F] [IsTotallyComplex E] (hdeg : Module.finrank F E = 2) :
    Tendsto (relLR F E) (𝓝[>] 1)
      (𝓝 (2 * (2 * Real.pi) ^ Module.finrank ℚ F * classNumber E * regulator E * Real.sqrt |(discr F : ℝ)| /
        (2 ^ Module.finrank ℚ F * classNumber F * regulator F * torsionOrder E *
          Real.sqrt |(discr E : ℝ)|))) := by
  convert relativeClassNumberFormula hdeg using 3
  rw [torsionOrder_eq_two (F := F)]; push_cast; ring

/-! ### Hasse's unit index -/

section CM

variable (K : Type) [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => maximalRealSubfield K

/-- $[K : K^+] = 2$ for a CM field $K$. -/
theorem finrank_maximalRealSubfield : Module.finrank K⁺ K = 2 :=
  Algebra.IsQuadraticExtension.finrank_eq_two _ _

/-- **Hasse's unit index** $Q_K = [\mathcal O_K^\times : \mu_K\,\mathcal O_{K^+}^\times]$ is $1$ or $2$ (Mathlib's
`IsCMField.indexRealUnits_eq_one_or_two`; Washington, Thm. 4.12). -/
@[kb "washington1997" "Ch. 4, Thm. 4.12"]
theorem hasseUnitIndex_eq_one_or_two :
    IsCMField.indexRealUnits K = 1 ∨ IsCMField.indexRealUnits K = 2 :=
  IsCMField.indexRealUnits_eq_one_or_two K

/-- **The regulator ratio** $R_K/R_{K^+} = 2^{d-1}/Q_K$, $d = [K^+:\mathbb{Q}]$ (Washington, Prop. 4.16; from Mathlib's
`regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv`, with unit rank $d - 1$). -/
@[kb "washington1997" "Ch. 4, Prop. 4.16 [unverified locator]"]
theorem regulator_div_regulator :
    regulator K / regulator K⁺ =
      2 ^ (Module.finrank ℚ K⁺ - 1) * (IsCMField.indexRealUnits K : ℝ)⁻¹ := by
  rw [IsCMField.regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv]
  congr 2
  rw [Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_top (E := K),
    nrComplexPlaces_top (finrank_maximalRealSubfield K), zero_add]

/-- **The relative class number formula for a CM field, with Hasse's unit index** ($K$ CM, $K^+$ its maximal totally
real subfield, $d = [K^+:\mathbb{Q}]$, $Q_K$ = `IsCMField.indexRealUnits K`):
$$\lim_{s \to 1^+}L(s,\chi_{K/K^+}) = \frac{(2\pi)^d\,h_K\,\sqrt{|d_{K^+}|}}{Q_K\,w_K\,h_{K^+}\,\sqrt{|d_K|}},$$
equivalently $h_K/h_{K^+} = Q_Kw_K(2\pi)^{-d}\sqrt{|d_K/d_{K^+}|}\,L(1,\chi_{K/K^+})$ (Washington, Thm. 4.17). -/
@[kb "washington1997" "Ch. 4, Thm. 4.17 [unverified locator]"]
theorem relativeClassNumberFormula_hasse :
    Tendsto (relLR K⁺ K) (𝓝[>] 1)
      (𝓝 ((2 * Real.pi) ^ Module.finrank ℚ K⁺ * classNumber K * Real.sqrt |(discr K⁺ : ℝ)| /
        (IsCMField.indexRealUnits K * torsionOrder K * classNumber K⁺ * Real.sqrt |(discr K : ℝ)|))) := by
  convert relativeClassNumberFormula' (finrank_maximalRealSubfield K) using 2
  have hR := regulator_div_regulator K
  have h1 := regulator_pos K⁺
  have hQ : (0 : ℝ) < IsCMField.indexRealUnits K := by
    rcases hasseUnitIndex_eq_one_or_two K with h | h <;> rw [h] <;> norm_num
  have hd : 1 ≤ Module.finrank ℚ K⁺ := Module.finrank_pos
  have hRK : regulator K = regulator K⁺ * (2 ^ (Module.finrank ℚ K⁺ - 1) * (IsCMField.indexRealUnits K : ℝ)⁻¹) := by
    rw [← hR]; field_simp
  rw [hRK]
  have h2 : (0 : ℝ) < classNumber K⁺ := Nat.cast_pos.mpr (classNumber_pos _)
  have h5 : (0 : ℝ) < torsionOrder K := Nat.cast_pos.mpr (torsionOrder_pos K)
  have h4 : (0 : ℝ) < Real.sqrt |(discr K⁺ : ℝ)| :=
    Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero _)))
  have h6 : (0 : ℝ) < Real.sqrt |(discr K : ℝ)| :=
    Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K)))
  have hpow : (2 : ℝ) ^ Module.finrank ℚ K⁺ = 2 * 2 ^ (Module.finrank ℚ K⁺ - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpow]
  field_simp

end CM

end QuadFormsKB.Binary.Rel
