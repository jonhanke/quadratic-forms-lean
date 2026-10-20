/-
# Weight 2: an Eisenstein series with prescribed constant terms at every cusp

$F$ totally real of degree $d \ge 2$, $\mathfrak N \ne 0$, $f : \mathbb{H}^d \to \mathbb{C}$ with constant terms $\mathrm{cv}_2(f, A)$ at every cusp
(`HasCuspLimits f 2`) and $f\,|_2\,\gamma = \chi(\gamma_{11})f$ on $\Gamma_0(\mathfrak N)$. The weight $W_f$ (`eisGenWeight`, supported on
reduced vectors) is not periodic, so the weight-2 series $E_2(\cdot; W)$ (Hecke's trick, `IntWeight` only) does not apply to it.
We write the constant terms of $W_f$ through **finitely many periodic weights**.

**Periodic extension** (`perExt`). Fix a class $C$ with integral ideal $\mathfrak b = \mathfrak b_C$ (`repIdeal`). For $y \in F^2$ put
$\Phi_C(y) = \varphi_f(x)$ if some $x$ with $\mathfrak b(x) = \mathfrak b$ satisfies $y \equiv x \pmod{\mathfrak N\mathfrak b}$ (a *witness*, `IsPerWit`),
and $\Phi_C(y) = 0$ otherwise. It is well defined by the congruence lemma (`exists_gammaFullR_rowMul`) and the
$\Gamma(\mathfrak N)$-invariance of $\varphi_f$; it is unit equivariant, periodic modulo $\mathfrak N\mathfrak b$, supported on $\mathfrak b^2$, bounded,
and $\Phi_C(y\gamma^{-1}) = \chi(\gamma_{11})\Phi_C(y)$ for $\gamma \in \Gamma_0(\mathfrak N)$; $\Phi_C = \varphi_f$ on $\{\mathfrak b(y) = \mathfrak b\}$.

**Cut weights** (`eisWt2`). For an integral ideal $\mathfrak d \ne 0$, $\Phi_{C,\mathfrak d}(y) = [\mathfrak b(y) \subseteq \mathfrak b\mathfrak d]\,\Phi_C(y)$: an integral
weight of level $\mathfrak N\mathfrak b\mathfrak d$ (`intWeight_eisWt2`) with the same $\Gamma_0(\mathfrak N)$-law.

**Möbius inversion** (`hasSum_moebius`). If $\mathfrak b(y) = \mathfrak b\mathfrak c$ ($y \in \mathfrak b^2$, $y \ne 0$), then
$y \in (\mathfrak b\mathfrak d_S)^2 \iff \mathfrak d_S \mid \mathfrak c$, so $\sum_S(-1)^{|S|}\Phi_{C,\mathfrak d_S}(y) = [\mathfrak b(y) = \mathfrak b]\,\varphi_f(y)$ and, summing
over $C$, $= W_f(y)$. Interchanging with the constant-term sum $\mathrm c(W_A) = \sum_{t\in U\backslash F^\times}W(tx_A)N(t)^{-2}$ (Fubini,
`summable_moebius_family`: the pairs $(S, t)$ inject into pairs of ideals $(\mathfrak d_S, \mathfrak e)$ with $\mathfrak b(tx_A) = \mathfrak b\mathfrak d_S\mathfrak e$,
and $\sum_{\mathfrak d,\mathfrak e}N(\mathfrak d\mathfrak e)^{-2} = \zeta_F(2)^2$-type bound):
$$\sum_C\sum_S(-1)^{|S|}\,\mathrm c\big((\Phi_{C,\mathfrak d_S})_A\big) = \mathrm c((W_f)_A) = \mathrm{cv}_2(f, A).$$

**Ray classes** (`RayClass.lean`). If $\kappa(\mathfrak d) = \kappa(\mathfrak d')$ then $\mathfrak d = \lambda\mathfrak d'$ with $(\lambda - 1)\mathfrak d' \subseteq \mathfrak N$, so
$\Phi_{C,\mathfrak d}(y) = \Phi_{C,\mathfrak d'}(\lambda^{-1}y)$ (`eisWt2_eq_scale`) and $\mathrm c((\Phi_{C,\mathfrak d})_A) = N(\lambda)^{-2}\mathrm c((\Phi_{C,\mathfrak d'})_A)$
(`eisConst_scaleWeight`). Grouping $S$ by the finitely many keys $r$ (with a fixed ideal $\mathfrak d_r$ of key $r$):
$$E_f^{(2)} = \sum_C\sum_ra_r\,E_2(\cdot; \Phi_{C,\mathfrak d_r}),\qquad a_r = \sum_{S:\ \kappa(\mathfrak d_S) = r}(-1)^{|S|}N(\lambda_S)^{-2}$$
(`eisGen2`, `eisGen2Coeff`), a **finite** combination of weight-2 series of periodic weights, and its constant term at $A\infty$ is
$\sum_C\sum_ra_r\,\mathrm c((\Phi_{C,\mathfrak d_r})_A) = \mathrm{cv}_2(f, A)$ (`tendsto_eisGen2_slash`, with `tendsto_eis2_slash`).

**Main results** ($d \ge 2$): `eisGen2_mem_modularFormChar` ($E_f^{(2)} \in M_2(\Gamma_0(\mathfrak N), \chi)$) and
**`sub_eisGen2_mem_cuspFormChar`**: $f - E_f^{(2)} \in S_2(\Gamma_0(\mathfrak N), \chi)$ for $f \in M_2(\Gamma_0(\mathfrak N), \chi)$ with constant terms at all
cusps. Holomorphy and the absence of a non-holomorphic correction term hold for every integral weight when $d \ge 2$ (`tendsto_heckeSeries_two`, `isHolomorphic_eis2`).

Sources: Hecke, *Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik*,
Abh. Math. Sem. Hamburg 5 (1927) [unverified]; Shimura (Duke 1978), §3 and Prop. 3.4 [unverified]; Freitag (1990), Ch. I §5
[unverified]; over $\mathbb{Q}$: `Siegel.GenusEis` (Möbius coefficients `moebCoeff`).
-/
import QuadFormsKB.HilbertModular.EisensteinGenus
import QuadFormsKB.HilbertModular.EisensteinWeight2Cusps
import QuadFormsKB.HilbertModular.IdealMoebius
import QuadFormsKB.HilbertModular.RayClass

open Complex Matrix NumberField UpperHalfPlane Filter Topology IsDedekindDomain
open scoped MatrixGroups ModularForm nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

/-! ### Fractional-ideal helpers -/

lemma fi_zero_mem (I : FI) : (0 : F) ∈ I := by
  rw [← FractionalIdeal.mem_coe]; exact Submodule.zero_mem _

lemma fi_mul_mem_O {I : FI} (r : 𝓞 F) {z : F} (h : z ∈ I) : algebraMap (𝓞 F) F r * z ∈ I := by
  rw [← FractionalIdeal.mem_coe] at *; rw [← Algebra.smul_def]; exact Submodule.smul_mem _ r h

/-- $\mathfrak b(\alpha, \gamma) \subseteq I \iff \alpha, \gamma \in I$. -/
lemma cuspIdeal_le_iff {α γ : F} {I : FI} : cuspIdeal α γ ≤ I ↔ α ∈ I ∧ γ ∈ I := by
  constructor
  · intro h; exact ⟨h (mem_cuspIdeal_fst _ _), h (mem_cuspIdeal_snd _ _)⟩
  · rintro ⟨h1, h2⟩ z hz
    obtain ⟨r, s, rfl⟩ := mem_cuspIdeal_iff.mp hz
    rw [Algebra.smul_def, Algebra.smul_def]
    exact fi_add_mem (fi_mul_mem_O r h1) (fi_mul_mem_O s h2)

lemma coeIdeal_le_one' (𝔞 : Ideal (𝓞 F)) : (𝔞 : FI) ≤ 1 := FractionalIdeal.coeIdeal_le_one

lemma mul_coeIdeal_le_right (𝔞 : Ideal (𝓞 F)) (I : FI) : (𝔞 : FI) * I ≤ I := by
  calc (𝔞 : FI) * I ≤ 1 * I := mul_le_mul_left (coeIdeal_le_one' 𝔞) I
    _ = I := one_mul I

/-- **Integral quotient**: if $J \subseteq I$ for an integral $I \ne 0$, then $J = I\mathfrak e$ for an integral ideal $\mathfrak e$. -/
lemma exists_eq_coeIdeal_mul_of_le {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) {J : FI} (h : J ≤ (I : FI)) :
    ∃ 𝔢 : Ideal (𝓞 F), J = (I : FI) * (𝔢 : FI) := by
  have hI' : (I : FI) ≠ 0 := coeIdeal_ne_zero' hI
  have hle : (I : FI)⁻¹ * J ≤ 1 := by
    calc (I : FI)⁻¹ * J ≤ (I : FI)⁻¹ * (I : FI) := mul_le_mul_right h _
      _ = 1 := inv_mul_cancel₀ hI'
  obtain ⟨𝔢, h𝔢⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  refine ⟨𝔢, ?_⟩
  rw [h𝔢, ← mul_assoc, mul_inv_cancel₀ hI', one_mul]

/-! ### $\varphi_f$ is $\Gamma(\mathfrak N)$-invariant -/

section Phi

variable {f : (InfinitePlace F → ℍ) → ℂ} {k : ℤ} {𝔑 : Ideal (𝓞 F)} {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ}

lemma phiF_rowMul_gammaFull (hf : HasCuspLimits f k)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[k] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    {γ : SL(2, 𝓞 F)} (hγ : γ ∈ GammaFullR 𝔑) (x : F × F) :
    phiF f k (rowMul x (toF F γ)) = phiF f k x := by
  by_cases hx : x.1 ≠ 0 ∨ x.2 ≠ 0
  · have hγ' : γ⁻¹ ∈ GammaFullR 𝔑 := Subgroup.inv_mem _ hγ
    obtain ⟨h0, h1⟩ := mk_one_of_gammaFullR hγ'
    have := phiF_rowMul_inv hf (hfχ _ h0) hx
    rwa [map_inv, inv_inv, h1, MulChar.map_one, one_mul] at this
  · push Not at hx
    have : x = 0 := Prod.ext hx.1 hx.2
    subst this
    congr 1
    ext <;> simp

end Phi

/-! ### The periodic extension of $\varphi_f$ on $\mathfrak b^2$ -/

section PerExt

variable (𝔑 𝔟 : Ideal (𝓞 F))

/-- **A witness** for $y$: a vector $x$ with $\mathfrak b(x) = \mathfrak b$ and $y \equiv x \pmod{\mathfrak N\mathfrak b}$ (coordinatewise). -/
def IsPerWit (y x : F × F) : Prop :=
  cuspIdeal x.1 x.2 = (𝔟 : FI) ∧ y.1 - x.1 ∈ (𝔑 : FI) * (𝔟 : FI) ∧ y.2 - x.2 ∈ (𝔑 : FI) * (𝔟 : FI)

variable (f : (InfinitePlace F → ℍ) → ℂ) (k : ℤ)

open Classical in
/-- **The periodic extension of $\varphi_f$** from $\{x : \mathfrak b(x) = \mathfrak b\}$ to $F^2$: $\Phi(y) = \varphi_f(x)$ for a witness $x$ of $y$
(`IsPerWit`), and $0$ if there is none. Parameters: `𝔑` (level), `𝔟` (the ideal), `f`, `k` (weight). -/
@[kb "hecke1927" "Eisenstein series of level 𝔑: weights periodic modulo 𝔑𝔟 [unverified]"]
noncomputable def perExt (y : F × F) : ℂ :=
  if h : ∃ x, IsPerWit 𝔑 𝔟 y x then phiF f k h.choose else 0

variable {𝔑 𝔟 f k}

lemma perExt_of_not {y : F × F} (h : ¬ ∃ x, IsPerWit 𝔑 𝔟 y x) : perExt 𝔑 𝔟 f k y = 0 := by
  classical
  rw [perExt, dif_neg h]

variable {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ}

/-- **Well-definedness**: $\Phi(y) = \varphi_f(x)$ for every witness $x$ of $y$. -/
lemma perExt_eq_of_wit (hf : HasCuspLimits f k)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[k] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (h𝔟 : 𝔟 ≠ ⊥) {y x : F × F} (hw : IsPerWit 𝔑 𝔟 y x) : perExt 𝔑 𝔟 f k y = phiF f k x := by
  classical
  have hex : ∃ x, IsPerWit 𝔑 𝔟 y x := ⟨x, hw⟩
  rw [perExt, dif_pos hex]
  obtain ⟨c1, c2, c3⟩ := hex.choose_spec
  obtain ⟨d1, d2, d3⟩ := hw
  have hx : x.1 ≠ 0 ∨ x.2 ≠ 0 := ne_zero_of_cuspIdeal_eq h𝔟 d1
  have e1 : hex.choose.1 - x.1 ∈ (𝔑 : FI) * cuspIdeal x.1 x.2 := by
    rw [d1, show hex.choose.1 - x.1 = (y.1 - x.1) - (y.1 - hex.choose.1) by ring]
    exact fi_sub_mem d2 c2
  have e2 : hex.choose.2 - x.2 ∈ (𝔑 : FI) * cuspIdeal x.1 x.2 := by
    rw [d1, show hex.choose.2 - x.2 = (y.2 - x.2) - (y.2 - hex.choose.2) by ring]
    exact fi_sub_mem d3 c3
  obtain ⟨γ, hγ, hγx⟩ := exists_gammaFullR_rowMul 𝔑 hx (c1.trans d1.symm) e1 e2
  rw [← hγx, phiF_rowMul_gammaFull hf hfχ hγ]

lemma isPerWit_self {y : F × F} (hy : cuspIdeal y.1 y.2 = (𝔟 : FI)) : IsPerWit 𝔑 𝔟 y y := by
  refine ⟨hy, ?_, ?_⟩ <;> rw [sub_self] <;> exact fi_zero_mem _

/-- $\Phi = \varphi_f$ on the vectors with ideal $\mathfrak b$. -/
lemma perExt_eq_phiF (hf : HasCuspLimits f k)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[k] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (h𝔟 : 𝔟 ≠ ⊥) {y : F × F} (hy : cuspIdeal y.1 y.2 = (𝔟 : FI)) : perExt 𝔑 𝔟 f k y = phiF f k y :=
  perExt_eq_of_wit hf hfχ h𝔟 (isPerWit_self hy)

/-- Witnesses are stable under adding $m \in (\mathfrak N\mathfrak b)^2$. -/
lemma isPerWit_add {y x : F × F} (hw : IsPerWit 𝔑 𝔟 y x) {m₁ m₂ : F}
    (h₁ : m₁ ∈ (𝔑 : FI) * (𝔟 : FI)) (h₂ : m₂ ∈ (𝔑 : FI) * (𝔟 : FI)) :
    IsPerWit 𝔑 𝔟 (y.1 + m₁, y.2 + m₂) x := by
  obtain ⟨d1, d2, d3⟩ := hw
  refine ⟨d1, ?_, ?_⟩
  · rw [show (y.1 + m₁) - x.1 = (y.1 - x.1) + m₁ by ring]; exact fi_add_mem d2 h₁
  · rw [show (y.2 + m₂) - x.2 = (y.2 - x.2) + m₂ by ring]; exact fi_add_mem d3 h₂

/-- **Periodicity modulo $\mathfrak N\mathfrak b$.** -/
lemma perExt_add (hf : HasCuspLimits f k)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[k] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (h𝔟 : 𝔟 ≠ ⊥) (y : F × F) {m₁ m₂ : F}
    (h₁ : m₁ ∈ (𝔑 : FI) * (𝔟 : FI)) (h₂ : m₂ ∈ (𝔑 : FI) * (𝔟 : FI)) :
    perExt 𝔑 𝔟 f k (y.1 + m₁, y.2 + m₂) = perExt 𝔑 𝔟 f k y := by
  by_cases h : ∃ x, IsPerWit 𝔑 𝔟 y x
  · obtain ⟨x, hx⟩ := h
    rw [perExt_eq_of_wit hf hfχ h𝔟 hx, perExt_eq_of_wit hf hfχ h𝔟 (isPerWit_add hx h₁ h₂)]
  · have h' : ¬ ∃ x, IsPerWit 𝔑 𝔟 (y.1 + m₁, y.2 + m₂) x := by
      rintro ⟨x, hx⟩
      apply h
      refine ⟨x, ?_⟩
      have := isPerWit_add hx (fi_neg_mem h₁) (fi_neg_mem h₂)
      simpa using this
    rw [perExt_of_not h, perExt_of_not h']

/-- Witnesses force $y \in \mathfrak b^2$. -/
lemma mem_of_isPerWit {y x : F × F} (hw : IsPerWit 𝔑 𝔟 y x) : y.1 ∈ (𝔟 : FI) ∧ y.2 ∈ (𝔟 : FI) := by
  obtain ⟨d1, d2, d3⟩ := hw
  have hN : (𝔑 : FI) * (𝔟 : FI) ≤ (𝔟 : FI) := mul_coeIdeal_le_right 𝔑 _
  have hx1 : x.1 ∈ (𝔟 : FI) := d1 ▸ mem_cuspIdeal_fst _ _
  have hx2 : x.2 ∈ (𝔟 : FI) := d1 ▸ mem_cuspIdeal_snd _ _
  refine ⟨?_, ?_⟩
  · rw [show y.1 = x.1 + (y.1 - x.1) by ring]; exact fi_add_mem hx1 (hN d2)
  · rw [show y.2 = x.2 + (y.2 - x.2) by ring]; exact fi_add_mem hx2 (hN d3)

lemma perExt_ne_zero_mem {y : F × F} (h : perExt 𝔑 𝔟 f k y ≠ 0) :
    y.1 ∈ (𝔟 : FI) ∧ y.2 ∈ (𝔟 : FI) := by
  by_cases hw : ∃ x, IsPerWit 𝔑 𝔟 y x
  · exact mem_of_isPerWit hw.choose_spec
  · exact absurd (perExt_of_not hw) h

lemma isPerWit_unit_smul {y x : F × F} (hw : IsPerWit 𝔑 𝔟 y x) (ε : (𝓞 F)ˣ) :
    IsPerWit 𝔑 𝔟 (ε • y) (ε • x) := by
  obtain ⟨d1, d2, d3⟩ := hw
  refine ⟨by rw [cuspIdeal_unit_smul]; exact d1, ?_, ?_⟩
  · rw [smul_fst, smul_fst, ← mul_sub]; exact fi_mul_mem_O _ d2
  · rw [smul_snd, smul_snd, ← mul_sub]; exact fi_mul_mem_O _ d3

/-- **Unit equivariance**: $\Phi(\varepsilon y) = N(\varepsilon)^k\Phi(y)$. -/
lemma isUnitEquivariant_perExt (hf : HasCuspLimits f k)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[k] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (h𝔟 : 𝔟 ≠ ⊥) : IsUnitEquivariant (perExt 𝔑 𝔟 f k) k := by
  intro ε y
  by_cases h : ∃ x, IsPerWit 𝔑 𝔟 y x
  · obtain ⟨x, hx⟩ := h
    rw [perExt_eq_of_wit hf hfχ h𝔟 hx, perExt_eq_of_wit hf hfχ h𝔟 (isPerWit_unit_smul hx ε)]
    have hε : ((ε : 𝓞 F) : F) ≠ 0 := (map_ne_zero_iff _ algebraMap_O_injective).mpr ε.ne_zero
    have hx0 : x.1 ≠ 0 ∨ x.2 ≠ 0 := ne_zero_of_cuspIdeal_eq h𝔟 hx.1
    have := phiF_smul hf hx0 hε
    rw [prod_realEmb_unit] at this
    exact this
  · have h' : ¬ ∃ x, IsPerWit 𝔑 𝔟 (ε • y) x := by
      rintro ⟨x, hx⟩
      apply h
      refine ⟨ε⁻¹ • x, ?_⟩
      have := isPerWit_unit_smul hx ε⁻¹
      rwa [inv_smul_smul] at this
    rw [perExt_of_not h, perExt_of_not h', mul_zero]

lemma isPerWit_rowMul {y x : F × F} (hw : IsPerWit 𝔑 𝔟 y x) (g : SL(2, 𝓞 F)) :
    IsPerWit 𝔑 𝔟 (rowMul y (toF F g)) (rowMul x (toF F g)) := by
  obtain ⟨d1, d2, d3⟩ := hw
  have hT : ∀ i j, toF F g i j = algebraMap (𝓞 F) F (g i j) := fun i j => rfl
  refine ⟨by rw [cuspIdeal_rowMul]; exact d1, ?_, ?_⟩
  · rw [rowMul_fst, rowMul_fst, show y.1 * toF F g 0 0 + y.2 * toF F g 1 0 - (x.1 * toF F g 0 0 + x.2 * toF F g 1 0)
      = toF F g 0 0 * (y.1 - x.1) + toF F g 1 0 * (y.2 - x.2) by ring, hT, hT]
    exact fi_add_mem (fi_mul_mem_O _ d2) (fi_mul_mem_O _ d3)
  · rw [rowMul_snd, rowMul_snd, show y.1 * toF F g 0 1 + y.2 * toF F g 1 1 - (x.1 * toF F g 0 1 + x.2 * toF F g 1 1)
      = toF F g 0 1 * (y.1 - x.1) + toF F g 1 1 * (y.2 - x.2) by ring, hT, hT]
    exact fi_add_mem (fi_mul_mem_O _ d2) (fi_mul_mem_O _ d3)

/-- **The $\Gamma_0(\mathfrak N)$-law**: $\Phi(y\gamma^{-1}) = \chi(\gamma_{11})\Phi(y)$. -/
lemma slashWeight_perExt (hf : HasCuspLimits f k)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[k] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (h𝔟 : 𝔟 ≠ ⊥) {γ : SL(2, 𝓞 F)} (hγ : γ ∈ Gamma0R 𝔑) :
    slashWeight (perExt 𝔑 𝔟 f k) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • perExt 𝔑 𝔟 f k := by
  funext y
  rw [slashWeight, Pi.smul_apply, smul_eq_mul]
  have hinv : (toF F γ)⁻¹ = toF F γ⁻¹ := (map_inv _ _).symm
  by_cases h : ∃ x, IsPerWit 𝔑 𝔟 y x
  · obtain ⟨x, hx⟩ := h
    have hw := isPerWit_rowMul hx γ⁻¹
    rw [hinv, perExt_eq_of_wit hf hfχ h𝔟 hw, perExt_eq_of_wit hf hfχ h𝔟 hx, ← hinv,
      phiF_rowMul_inv hf (hfχ γ hγ) (ne_zero_of_cuspIdeal_eq h𝔟 hx.1)]
  · have h' : ¬ ∃ x, IsPerWit 𝔑 𝔟 (rowMul y (toF F γ)⁻¹) x := by
      rintro ⟨x, hx⟩
      apply h
      refine ⟨rowMul x (toF F γ), ?_⟩
      have := isPerWit_rowMul hx γ
      rwa [← rowMul_mul, inv_mul_cancel, rowMul_one] at this
    rw [perExt_of_not h, perExt_of_not h', mul_zero]

/-- $\Phi$ takes finitely many values. -/
lemma finite_range_perExt (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f k)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[k] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (h𝔟 : 𝔟 ≠ ⊥) : (Set.range (perExt 𝔑 𝔟 f k)).Finite := by
  have hfin := finite_image_of_invariant h𝔑 h𝔟 (phiF f k) fun γ hγ x => phiF_rowMul_gammaFull hf hfχ hγ x
  refine (hfin.union (Set.finite_singleton 0)).subset ?_
  rintro _ ⟨y, rfl⟩
  by_cases h : ∃ x, IsPerWit 𝔑 𝔟 y x
  · obtain ⟨x, hx⟩ := h
    exact Or.inl ⟨x, hx.1, (perExt_eq_of_wit hf hfχ h𝔟 hx).symm⟩
  · exact Or.inr (by rw [perExt_of_not h]; rfl)

end PerExt

/-! ### Cut weights $\Phi_{C,\mathfrak d}$ -/

section Cut

open Classical in
/-- **Cutting a weight to $I^2$**: $V_I(y) = V(y)$ if $\mathfrak b(y) \subseteq I$ (i.e. $y_0, y_1 \in I$), else $0$. -/
noncomputable def cutWeight (V : F × F → ℂ) (I : FI) (y : F × F) : ℂ :=
  if cuspIdeal y.1 y.2 ≤ I then V y else 0

lemma cutWeight_of_le {V : F × F → ℂ} {I : FI} {y : F × F} (h : cuspIdeal y.1 y.2 ≤ I) :
    cutWeight V I y = V y := by
  classical
  rw [cutWeight, if_pos h]

lemma cutWeight_of_not_le {V : F × F → ℂ} {I : FI} {y : F × F} (h : ¬ cuspIdeal y.1 y.2 ≤ I) :
    cutWeight V I y = 0 := by
  classical
  rw [cutWeight, if_neg h]

lemma IsUnitEquivariant.cutWeight {V : F × F → ℂ} {k : ℤ} (hV : IsUnitEquivariant V k) (I : FI) :
    IsUnitEquivariant (cutWeight V I) k := by
  intro ε y
  by_cases h : cuspIdeal y.1 y.2 ≤ I
  · rw [cutWeight_of_le h, cutWeight_of_le (by rwa [cuspIdeal_unit_smul]), hV]
  · rw [cutWeight_of_not_le h, cutWeight_of_not_le (by rwa [cuspIdeal_unit_smul]), mul_zero]

lemma slashWeight_cutWeight (V : F × F → ℂ) (I : FI) (g : SL(2, 𝓞 F)) :
    slashWeight (cutWeight V I) (toF F g) = cutWeight (slashWeight V (toF F g)) I := by
  funext y
  have hinv : (toF F g)⁻¹ = toF F g⁻¹ := (map_inv _ _).symm
  have hid : cuspIdeal (rowMul y (toF F g)⁻¹).1 (rowMul y (toF F g)⁻¹).2 = cuspIdeal y.1 y.2 := by
    rw [hinv, cuspIdeal_rowMul]
  simp only [slashWeight]
  by_cases h : cuspIdeal y.1 y.2 ≤ I
  · rw [cutWeight_of_le h, cutWeight_of_le (by rwa [hid])]; rfl
  · rw [cutWeight_of_not_le h, cutWeight_of_not_le (by rwa [hid])]

variable (f : (InfinitePlace F → ℍ) → ℂ) (𝔑 : Ideal (𝓞 F))

/-- **The weight $\Phi_{C,\mathfrak d}$**: the periodic extension $\Phi_C$ of $\varphi_f$ for $\mathfrak b = \mathfrak b_C$ (`repIdeal C`), cut to
$(\mathfrak b\mathfrak d)^2$. Parameters: `f`, `𝔑` (level), `C` (ideal class), `𝔡` (integral ideal). -/
@[kb "hecke1927" "weights of level 𝔑𝔟𝔡 for the Eisenstein series at the cusps of class C [unverified]"]
noncomputable def eisWt2 (C : ClassGroup (𝓞 F)) (𝔡 : Ideal (𝓞 F)) : F × F → ℂ :=
  cutWeight (perExt 𝔑 (repIdeal C) f 2) ((repIdeal C * 𝔡 : Ideal (𝓞 F)) : FI)

variable {f 𝔑} {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ}

lemma mem_coeIdeal_of_mem {𝔞 : Ideal (𝓞 F)} {m : 𝓞 F} (hm : m ∈ 𝔞) : algebraMap (𝓞 F) F m ∈ (𝔞 : FI) :=
  (FractionalIdeal.mem_coeIdeal _).mpr ⟨m, hm, rfl⟩

lemma cuspIdeal_add_le_iff {I : FI} {y : F × F} {m₁ m₂ : F} (h₁ : m₁ ∈ I) (h₂ : m₂ ∈ I) :
    cuspIdeal (y.1 + m₁) (y.2 + m₂) ≤ I ↔ cuspIdeal y.1 y.2 ≤ I := by
  rw [cuspIdeal_le_iff, cuspIdeal_le_iff]
  constructor
  · rintro ⟨a, b⟩
    refine ⟨?_, ?_⟩
    · have := fi_sub_mem a h₁; rwa [add_sub_cancel_right] at this
    · have := fi_sub_mem b h₂; rwa [add_sub_cancel_right] at this
  · rintro ⟨a, b⟩; exact ⟨fi_add_mem a h₁, fi_add_mem b h₂⟩

/-- **$\Phi_{C,\mathfrak d}$ is an integral weight** of weight 2 and level $\mathfrak N\mathfrak b_C\mathfrak d$. -/
theorem intWeight_eisWt2 (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) {𝔡 : Ideal (𝓞 F)} (h𝔡 : 𝔡 ≠ ⊥) :
    IntWeight (eisWt2 f 𝔑 C 𝔡) 2 (𝔑 * repIdeal C * 𝔡) := by
  have h𝔟 := repIdeal_ne_bot C
  set 𝔟 := repIdeal C
  refine ⟨(isUnitEquivariant_perExt hf hfχ h𝔟).cutWeight _, fun y hy => ?_, fun y m₁ m₂ hm₁ hm₂ => ?_, ?_, ?_⟩
  · have hy' : perExt 𝔑 𝔟 f 2 y ≠ 0 := by
      by_cases h : cuspIdeal y.1 y.2 ≤ ((𝔟 * 𝔡 : Ideal (𝓞 F)) : FI)
      · rwa [eisWt2, cutWeight_of_le h] at hy
      · exact absurd (cutWeight_of_not_le h) hy
    obtain ⟨h1, h2⟩ := perExt_ne_zero_mem hy'
    obtain ⟨a, ha⟩ := exists_of_mem_coeIdeal h1
    obtain ⟨b, hb⟩ := exists_of_mem_coeIdeal h2
    exact ⟨(a, b), by rw [ha, hb]⟩
  · have hle1 : 𝔑 * 𝔟 * 𝔡 ≤ 𝔑 * 𝔟 := Ideal.mul_le_left
    have hle2 : 𝔑 * 𝔟 * 𝔡 ≤ 𝔟 * 𝔡 := by rw [mul_assoc]; exact Ideal.mul_le_right
    have n1 : ∀ {m}, m ∈ 𝔑 * 𝔟 * 𝔡 → algebraMap (𝓞 F) F m ∈ (𝔑 : FI) * (𝔟 : FI) := fun hm => by
      rw [← FractionalIdeal.coeIdeal_mul]; exact mem_coeIdeal_of_mem (hle1 hm)
    have n2 : ∀ {m}, m ∈ 𝔑 * 𝔟 * 𝔡 → algebraMap (𝓞 F) F m ∈ ((𝔟 * 𝔡 : Ideal (𝓞 F)) : FI) :=
      fun hm => mem_coeIdeal_of_mem (hle2 hm)
    simp only [eisWt2]
    set y₁ : F × F := (y.1 + algebraMap (𝓞 F) F m₁, y.2 + algebraMap (𝓞 F) F m₂)
    have hiff : cuspIdeal y₁.1 y₁.2 ≤ ((𝔟 * 𝔡 : Ideal (𝓞 F)) : FI) ↔
        cuspIdeal y.1 y.2 ≤ ((𝔟 * 𝔡 : Ideal (𝓞 F)) : FI) := cuspIdeal_add_le_iff (n2 hm₁) (n2 hm₂)
    by_cases h : cuspIdeal y.1 y.2 ≤ ((𝔟 * 𝔡 : Ideal (𝓞 F)) : FI)
    · rw [cutWeight_of_le h, cutWeight_of_le (hiff.mpr h)]
      exact perExt_add hf hfχ h𝔟 y (n1 hm₁) (n1 hm₂)
    · rw [cutWeight_of_not_le h, cutWeight_of_not_le (fun h' => h (hiff.mp h'))]
  · obtain ⟨B, hB⟩ := ((finite_range_perExt h𝔑 hf hfχ h𝔟).image (‖·‖)).bddAbove
    refine ⟨max B 0, fun y => ?_⟩
    by_cases h : cuspIdeal y.1 y.2 ≤ ((𝔟 * 𝔡 : Ideal (𝓞 F)) : FI)
    · rw [eisWt2, cutWeight_of_le h]; exact (hB ⟨_, ⟨y, rfl⟩, rfl⟩).trans (le_max_left _ _)
    · rw [eisWt2, cutWeight_of_not_le h, norm_zero]; exact le_max_right _ _
  · exact mul_ne_zero (mul_ne_zero h𝔑 h𝔟) h𝔡

/-- **The $\Gamma_0(\mathfrak N)$-law of $\Phi_{C,\mathfrak d}$**: $(\Phi_{C,\mathfrak d})_\gamma = \chi(\gamma_{11})\Phi_{C,\mathfrak d}$. -/
theorem slashWeight_eisWt2 (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) (𝔡 : Ideal (𝓞 F)) {γ : SL(2, 𝓞 F)} (hγ : γ ∈ Gamma0R 𝔑) :
    slashWeight (eisWt2 f 𝔑 C 𝔡) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • eisWt2 f 𝔑 C 𝔡 := by
  rw [eisWt2, slashWeight_cutWeight, slashWeight_perExt hf hfχ (repIdeal_ne_bot C) hγ]
  funext y
  by_cases h : cuspIdeal y.1 y.2 ≤ ((repIdeal C * 𝔡 : Ideal (𝓞 F)) : FI)
  · simp only [Pi.smul_apply, cutWeight_of_le h]
  · simp only [Pi.smul_apply, cutWeight_of_not_le h, smul_zero]

/-- **Scaling between ideals of one ray class**: if $\mathfrak d = \lambda\mathfrak d'$ and $(\lambda - 1)\mathfrak d' \subseteq \mathfrak N$, then
$\Phi_{C,\mathfrak d}(y) = \Phi_{C,\mathfrak d'}(\lambda^{-1}y)$, i.e. $\Phi_{C,\mathfrak d}$ = `scaleWeight` $\Phi_{C,\mathfrak d'}\ \lambda$. -/
theorem eisWt2_eq_scale (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) {𝔡 𝔡' : Ideal (𝓞 F)} {l : F} (hl : l ≠ 0)
    (he : (𝔡 : FI) = FractionalIdeal.spanSingleton (𝓞 F)⁰ l * (𝔡' : FI))
    (hcong : FractionalIdeal.spanSingleton (𝓞 F)⁰ (l - 1) * (𝔡' : FI) ≤ (𝔑 : FI)) :
    eisWt2 f 𝔑 C 𝔡 = scaleWeight (eisWt2 f 𝔑 C 𝔡') (Units.mk0 l hl) := by
  funext y
  set 𝔟 := repIdeal C
  set y' := (scaleEquiv (Units.mk0 l hl)).symm y
  have hy : y = (l * y'.1, l * y'.2) := by
    have := (Equiv.apply_symm_apply (scaleEquiv (Units.mk0 l hl)) y).symm
    rw [this]; rfl
  have hl' : FractionalIdeal.spanSingleton (𝓞 F)⁰ l ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  have hcut : cuspIdeal y.1 y.2 ≤ ((𝔟 * 𝔡 : Ideal (𝓞 F)) : FI) ↔
      cuspIdeal y'.1 y'.2 ≤ ((𝔟 * 𝔡' : Ideal (𝓞 F)) : FI) := by
    have key : (𝔟 : FI) * (FractionalIdeal.spanSingleton (𝓞 F)⁰ l * (𝔡' : FI)) =
        ((𝔟 : FI) * (𝔡' : FI)) * FractionalIdeal.spanSingleton (𝓞 F)⁰ l := by ring
    rw [hy, cuspIdeal_smul, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul, he, key,
      mul_comm (FractionalIdeal.spanSingleton (𝓞 F)⁰ l) (cuspIdeal _ _)]
    constructor
    · intro h; exact fi_le_of_mul_le hl' h
    · intro h; exact mul_le_mul_left h _
  simp only [HilbertModular.scaleWeight, eisWt2]
  by_cases h : cuspIdeal y'.1 y'.2 ≤ ((𝔟 * 𝔡' : Ideal (𝓞 F)) : FI)
  · rw [cutWeight_of_le (hcut.mpr h), cutWeight_of_le h]
    -- `y = y' + (λ - 1)y'` with `(λ - 1)y' ∈ 𝔑𝔟`
    have hm : ∀ z ∈ ((𝔟 * 𝔡' : Ideal (𝓞 F)) : FI), (l - 1) * z ∈ (𝔑 : FI) * (𝔟 : FI) := by
      intro z hz
      rw [← FractionalIdeal.spanSingleton_le_iff_mem, map_mul]
      calc FractionalIdeal.spanSingleton (𝓞 F)⁰ (l - 1) * FractionalIdeal.spanSingleton (𝓞 F)⁰ z
          ≤ FractionalIdeal.spanSingleton (𝓞 F)⁰ (l - 1) * ((𝔟 : FI) * (𝔡' : FI)) := by
            refine mul_le_mul_right ?_ _
            rw [FractionalIdeal.spanSingleton_le_iff_mem, ← FractionalIdeal.coeIdeal_mul]; exact hz
        _ = (FractionalIdeal.spanSingleton (𝓞 F)⁰ (l - 1) * (𝔡' : FI)) * (𝔟 : FI) := by ring
        _ ≤ (𝔑 : FI) * (𝔟 : FI) := mul_le_mul_left hcong _
    obtain ⟨h1, h2⟩ := cuspIdeal_le_iff.mp h
    have e : y = (y'.1 + (l - 1) * y'.1, y'.2 + (l - 1) * y'.2) := by
      rw [hy]; ext <;> ring
    rw [e, perExt_add hf hfχ (repIdeal_ne_bot C) y' (hm _ h1) (hm _ h2)]
  · rw [cutWeight_of_not_le (fun h' => h (hcut.mp h')), cutWeight_of_not_le h]

end Cut

/-! ### Constant terms: Möbius inversion and Fubini -/

section ConstTerm

/-- $\prod_v|\sigma_v(t)| = |N_{F/\mathbb{Q}}(t)|$ ($F$ totally real). -/
lemma absNorm_eq_abs_norm (t : F) : absNorm t = (((|Algebra.norm ℚ t| : ℚ)) : ℝ) := by
  have h := InfinitePlace.prod_eq_abs_norm t
  have hm : ∀ v : InfinitePlace F, v.mult = 1 := fun v => mult_eq_one_of_totallyReal v
  simp only [hm, pow_one] at h
  rw [absNorm]; simp_rw [abs_realEmb]; exact h

/-- $N(\mathfrak b(tx)) = |N(t)|\,N(\mathfrak b(x))$. -/
lemma absNorm_cuspIdeal_smul (t : F) (x : F × F) :
    ((FractionalIdeal.absNorm (cuspIdeal (t * x.1) (t * x.2)) : ℚ) : ℝ) =
      absNorm t * ((FractionalIdeal.absNorm (cuspIdeal x.1 x.2) : ℚ) : ℝ) := by
  rw [cuspIdeal_smul, map_mul, FractionalIdeal.absNorm_span_singleton, absNorm_eq_abs_norm]; push_cast; ring

lemma norm_prod_realEmb_zpow (t : F) :
    ‖(∏ v, (realEmb F v t : ℂ)) ^ (-(2 : ℤ))‖ = (absNorm t ^ 2)⁻¹ := by
  rw [norm_zpow, norm_prod]
  simp_rw [Complex.norm_real, Real.norm_eq_abs]
  rw [← absNorm, _root_.zpow_neg, zpow_ofNat]

lemma prod_realEmb_zero_zpow : (∏ v, (realEmb F v 0 : ℂ)) ^ (-(2 : ℤ)) = 0 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simp), _root_.zero_zpow _ (by norm_num)]

lemma smul_ne_zero_vec {x : F × F} (hx : x.1 ≠ 0 ∨ x.2 ≠ 0) {t : F} (ht : t ≠ 0) :
    t * x.1 ≠ 0 ∨ t * x.2 ≠ 0 :=
  hx.imp (mul_ne_zero ht) (mul_ne_zero ht)

variable {f : (InfinitePlace F → ℍ) → ℂ} {𝔑 : Ideal (𝓞 F)} {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ}

variable (f) in
open Classical in
/-- **The part of $\varphi_f$ on the vectors with ideal $\mathfrak b_C$**: $[\mathfrak b(y) = \mathfrak b_C]\,\varphi_f(y)$. Summed over $C$ it is
The $W_f$ (`sum_redPart`). -/
noncomputable def redPart (C : ClassGroup (𝓞 F)) (y : F × F) : ℂ :=
  if cuspIdeal y.1 y.2 = ((repIdeal C : Ideal (𝓞 F)) : FI) then phiF f 2 y else 0

/-- **Möbius inversion for the cut weights**: for $y \ne 0$,
$\sum_S(-1)^{|S|}\Phi_{C,\mathfrak d_S}(y) = [\mathfrak b(y) = \mathfrak b_C]\,\varphi_f(y)$. -/
@[kb "hecke1927" "Möbius inversion over ideals for Eisenstein weights [unverified]"]
theorem hasSum_moebius_eisWt2 (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) {y : F × F} (hy : y.1 ≠ 0 ∨ y.2 ≠ 0) :
    HasSum (fun S : Finset (HeightOneSpectrum (𝓞 F)) =>
      (-1 : ℂ) ^ S.card * eisWt2 f 𝔑 C (sqfIdeal S) y) (redPart f C y) := by
  classical
  set 𝔟 := repIdeal C
  have h𝔟 := repIdeal_ne_bot C
  by_cases hle : cuspIdeal y.1 y.2 ≤ (𝔟 : FI)
  · obtain ⟨𝔠, h𝔠⟩ := exists_eq_coeIdeal_mul_of_le h𝔟 hle
    have h𝔠0 : 𝔠 ≠ ⊥ := by
      rintro rfl; apply cuspIdeal_ne_zero hy; rw [h𝔠, FractionalIdeal.coeIdeal_bot, mul_zero]
    have hterm : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (-1 : ℂ) ^ S.card * eisWt2 f 𝔑 C (sqfIdeal S) y =
        if sqfIdeal S ∣ 𝔠 then (-1 : ℂ) ^ S.card * perExt 𝔑 𝔟 f 2 y else 0 := by
      intro S
      have hiff : cuspIdeal y.1 y.2 ≤ ((𝔟 * sqfIdeal S : Ideal (𝓞 F)) : FI) ↔ sqfIdeal S ∣ 𝔠 := by
        rw [h𝔠, FractionalIdeal.coeIdeal_mul, Ideal.dvd_iff_le]
        constructor
        · intro h
          refine (FractionalIdeal.coeIdeal_le_coeIdeal F).mp (fi_le_of_mul_le (coeIdeal_ne_zero' h𝔟) ?_)
          rwa [mul_comm (𝔠 : FI), mul_comm (sqfIdeal S : FI)]
        · intro h; exact mul_le_mul_right ((FractionalIdeal.coeIdeal_le_coeIdeal F).mpr h) _
      by_cases hd : sqfIdeal S ∣ 𝔠
      · rw [if_pos hd, eisWt2, cutWeight_of_le (hiff.mpr hd)]
      · rw [if_neg hd, eisWt2, cutWeight_of_not_le (fun h => hd (hiff.mp h)), mul_zero]
    rw [show (fun S : Finset (HeightOneSpectrum (𝓞 F)) => (-1 : ℂ) ^ S.card * eisWt2 f 𝔑 C (sqfIdeal S) y) =
      fun S => if sqfIdeal S ∣ 𝔠 then (-1 : ℂ) ^ S.card * perExt 𝔑 𝔟 f 2 y else 0 from funext hterm]
    convert hasSum_moebius h𝔠0 (perExt 𝔑 𝔟 f 2 y) using 1
    have htop : 𝔠 = ⊤ ↔ cuspIdeal y.1 y.2 = (𝔟 : FI) := by
      rw [h𝔠]; constructor
      · rintro rfl; rw [FractionalIdeal.coeIdeal_top, mul_one]
      · intro h
        apply (FractionalIdeal.coeIdeal_inj (K := F)).mp
        rw [FractionalIdeal.coeIdeal_top]
        exact mul_left_cancel₀ (coeIdeal_ne_zero' h𝔟) (by rw [h, mul_one])
    rw [redPart]
    by_cases h : cuspIdeal y.1 y.2 = (𝔟 : FI)
    · rw [if_pos h, if_pos (htop.mpr h), perExt_eq_phiF hf hfχ h𝔟 h]
    · rw [if_neg h, if_neg (fun h' => h (htop.mp h'))]
  · have h0 : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (-1 : ℂ) ^ S.card * eisWt2 f 𝔑 C (sqfIdeal S) y = 0 := by
      intro S
      rw [eisWt2, cutWeight_of_not_le, mul_zero]
      intro h
      exact hle (h.trans ((FractionalIdeal.coeIdeal_le_coeIdeal F).mpr Ideal.mul_le_left))
    simp only [h0]
    rw [redPart, if_neg (fun h => hle h.le)]
    exact hasSum_zero

lemma cuspClass_eq_of_cuspIdeal_eq {y : F × F} (hy : y.1 ≠ 0 ∨ y.2 ≠ 0) {C : ClassGroup (𝓞 F)}
    (h : cuspIdeal y.1 y.2 = ((repIdeal C : Ideal (𝓞 F)) : FI)) : cuspClass y.1 y.2 = C := by
  rw [cuspClass_eq hy, ← cuspClass_eq_mk0 C]
  congr 1
  exact Units.ext h

/-- **Summing over the classes gives $W_f$**: $\sum_C[\mathfrak b(y) = \mathfrak b_C]\varphi_f(y) = W_f(y)$ for $y \ne 0$. -/
lemma sum_redPart {y : F × F} (hy : y.1 ≠ 0 ∨ y.2 ≠ 0) :
    ∑ C : ClassGroup (𝓞 F), redPart f C y = eisGenWeight f 2 y := by
  classical
  by_cases hred : IsRedVec y
  · rw [Finset.sum_eq_single (cuspClass y.1 y.2), eisGenWeight_of_red hred, redPart, if_pos hred.2]
    · intro C _ hC
      rw [redPart, if_neg]
      intro h
      exact hC (cuspClass_eq_of_cuspIdeal_eq hy h).symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [eisGenWeight_of_not_red hred]
    refine Finset.sum_eq_zero fun C _ => ?_
    rw [redPart, if_neg]
    intro h
    exact hred ⟨hy, by rw [cuspClass_eq_of_cuspIdeal_eq hy h]; exact h⟩

/-- **The double family is summable** (Fubini for the Möbius sum): for $x \ne 0$,
$(S, t) \mapsto (-1)^{|S|}\Phi_{C,\mathfrak d_S}(tx)N(t)^{-2}$ is summable over finite sets of primes $S$ and $t \in U\backslash F$. *Proof:* it
is bounded by $B\,|N(t)|^{-2}$ on the pairs with $\mathfrak b(tx) \subseteq \mathfrak b_C\mathfrak d_S$; writing $\mathfrak b(tx) = \mathfrak b_C\mathfrak d_S\mathfrak e$,
$(S, t) \mapsto (S, \mathfrak e)$ is injective and $|N(t)|^{-2} = K\,N(\mathfrak d_S)^{-2}N(\mathfrak e)^{-2}$, and
$\sum_{S,\mathfrak e}N(\mathfrak d_S)^{-2}N(\mathfrak e)^{-2} < \infty$ ($\zeta_F(2)$). -/
theorem summable_moebius_family (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) {x : F × F} (hx : x.1 ≠ 0 ∨ x.2 ≠ 0) :
    Summable (fun p : Finset (HeightOneSpectrum (𝓞 F)) × UOrbitF F =>
      (-1 : ℂ) ^ p.1.card * eisWt2 f 𝔑 C (sqfIdeal p.1) (p.2.out * x.1, p.2.out * x.2) *
        (∏ v, (realEmb F v p.2.out : ℂ)) ^ (-(2 : ℤ))) := by
  classical
  set 𝔟 := repIdeal C
  have h𝔟 := repIdeal_ne_bot C
  obtain ⟨B, hB⟩ := ((finite_range_perExt h𝔑 hf hfχ h𝔟).image (‖·‖)).bddAbove
  have hW : ∀ 𝔡 y, ‖eisWt2 f 𝔑 C 𝔡 y‖ ≤ max B 0 := by
    intro 𝔡 y
    by_cases h : cuspIdeal y.1 y.2 ≤ ((𝔟 * 𝔡 : Ideal (𝓞 F)) : FI)
    · rw [eisWt2, cutWeight_of_le h]; exact (hB ⟨_, ⟨y, rfl⟩, rfl⟩).trans (le_max_left _ _)
    · rw [eisWt2, cutWeight_of_not_le h, norm_zero]; exact le_max_right _ _
  set P : Set (Finset (HeightOneSpectrum (𝓞 F)) × UOrbitF F) := {p | p.2.out ≠ 0 ∧
    cuspIdeal (p.2.out * x.1) (p.2.out * x.2) ≤ ((𝔟 * sqfIdeal p.1 : Ideal (𝓞 F)) : FI)}
  have hex : ∀ p ∈ P, ∃ 𝔢 : Ideal (𝓞 F), cuspIdeal (p.2.out * x.1) (p.2.out * x.2) =
      ((𝔟 * sqfIdeal p.1 : Ideal (𝓞 F)) : FI) * (𝔢 : FI) :=
    fun p hp => exists_eq_coeIdeal_mul_of_le (mul_ne_zero h𝔟 (sqfIdeal_ne_bot _)) hp.2
  choose! E hE using hex
  set ι : P → Finset (HeightOneSpectrum (𝓞 F)) × Ideal (𝓞 F) := fun p => (p.1.1, E p.1)
  have hIx : cuspIdeal x.1 x.2 ≠ 0 := cuspIdeal_ne_zero hx
  have hι : Function.Injective ι := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hpq
    simp only [ι] at h1 h2
    have hc : cuspIdeal (p.2.out * x.1) (p.2.out * x.2) = cuspIdeal (q.2.out * x.1) (q.2.out * x.2) := by
      rw [hE p hp, hE q hq, h1, h2]
    rw [cuspIdeal_smul, cuspIdeal_smul] at hc
    obtain ⟨ε, hε⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp (mul_right_cancel₀ hIx hc)
    have h3 : p.2 = q.2 := by
      rw [← Quotient.out_eq p.2, ← Quotient.out_eq q.2]
      exact (Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨ε, hε⟩))).symm
    exact Subtype.ext (Prod.ext h1 h3)
  set a : ℝ := ((FractionalIdeal.absNorm (cuspIdeal x.1 x.2) : ℚ) : ℝ)
  have ha : a ≠ 0 := by
    simp only [a, ne_eq, Rat.cast_eq_zero, FractionalIdeal.absNorm_eq_zero_iff]; exact hIx
  set K : ℝ := (a / (Ideal.absNorm 𝔟 : ℝ)) ^ 2
  set h : Finset (HeightOneSpectrum (𝓞 F)) × Ideal (𝓞 F) → ℝ := fun q =>
    (Ideal.absNorm (sqfIdeal q.1) : ℝ) ^ (-(2 : ℝ)) * (Ideal.absNorm q.2 : ℝ) ^ (-(2 : ℝ))
  have hh : Summable h := by
    have h1 : Summable fun S : Finset (HeightOneSpectrum (𝓞 F)) =>
        (Ideal.absNorm (sqfIdeal S) : ℝ) ^ (-(2 : ℝ)) := summable_absNorm_sqfIdeal one_lt_two
    have h2 : Summable fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℝ) ^ (-(2 : ℝ)) :=
      QuadFormsKB.NFEuler.summable_absNorm_rpow one_lt_two
    exact Summable.mul_of_nonneg h1 h2 (fun S => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hHP : ∀ p : P, (absNorm p.1.2.out ^ 2)⁻¹ = K * h (ι p) := by
    rintro ⟨p, hp0, hp⟩
    simp only [ι, h, K]
    have e := congrArg (fun I => ((FractionalIdeal.absNorm I : ℚ) : ℝ)) (hE p ⟨hp0, hp⟩)
    rw [absNorm_cuspIdeal_smul, FractionalIdeal.coeIdeal_mul, map_mul, map_mul,
      FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.coeIdeal_absNorm] at e
    push_cast at e
    set A := absNorm p.2.out
    set n1 := (Ideal.absNorm 𝔟 : ℝ)
    set n2 := (Ideal.absNorm (sqfIdeal p.1) : ℝ)
    set n3 := (Ideal.absNorm (E p) : ℝ)
    have hA : A ≠ 0 := (absNorm_pos hp0).ne'
    have hprod : n1 * n2 * n3 ≠ 0 := by rw [← e]; exact mul_ne_zero hA ha
    have hn1 : n1 ≠ 0 := fun h0 => hprod (by rw [h0]; ring)
    have hn2 : n2 ≠ 0 := fun h0 => hprod (by rw [h0]; ring)
    have hn3 : n3 ≠ 0 := fun h0 => hprod (by rw [h0]; ring)
    have hn2' : 0 ≤ n2 := Nat.cast_nonneg _
    have hn3' : 0 ≤ n3 := Nat.cast_nonneg _
    rw [Real.rpow_neg hn2', Real.rpow_neg hn3', Real.rpow_two, Real.rpow_two]
    have hA' : A = n1 * n2 * n3 / a := by field_simp; linarith [e]
    rw [hA']
    field_simp
  set H : Finset (HeightOneSpectrum (𝓞 F)) × UOrbitF F → ℝ := P.indicator fun p => (absNorm p.2.out ^ 2)⁻¹
  have hHs : Summable H := by
    refine summable_subtype_iff_indicator.mp ?_
    exact ((hh.comp_injective hι).mul_left K).congr fun p => (hHP p).symm
  refine Summable.of_norm_bounded (hHs.mul_left (max B 0)) fun p => ?_
  by_cases hp : p ∈ P
  · rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_prod_realEmb_zpow]
    simp only [H, Set.indicator_of_mem hp]
    exact mul_le_mul_of_nonneg_right (hW _ _) (by positivity)
  · simp only [H, Set.indicator_of_notMem hp, mul_zero]
    by_cases ht : p.2.out = 0
    · rw [ht, prod_realEmb_zero_zpow, mul_zero, norm_zero]
    · have hp' : ¬ cuspIdeal (p.2.out * x.1) (p.2.out * x.2) ≤
          ((𝔟 * sqfIdeal p.1 : Ideal (𝓞 F)) : FI) := fun h' => hp ⟨ht, h'⟩
      rw [eisWt2, cutWeight_of_not_le (y := (p.2.out * x.1, p.2.out * x.2)) hp', mul_zero, zero_mul, norm_zero]

/-- The constant term at $A\infty$ as a sum over $t \in U\backslash F$ of $W(t\,x_A)N(t)^{-2}$, $x_A = (-A_{10}, A_{00})$. -/
lemma eisConst_slash_eq {W : F × F → ℂ} (hW : IsUnitEquivariant W 2) (A : SL(2, F)) :
    eisConst (slashWeight W A) 2 = ∑' t : UOrbitF F,
      W (t.out * (-(A 1 0)), t.out * A 0 0) * (∏ v, (realEmb F v t.out : ℂ)) ^ (-(2 : ℤ)) := by
  rw [eisConst_slashWeight hW]; simp only [mul_neg]

/-- For each $t$: $\sum_S(-1)^{|S|}\Phi_{C,\mathfrak d_S}(tx)N(t)^{-2} = [\mathfrak b(tx) = \mathfrak b_C]\varphi_f(tx)N(t)^{-2}$. -/
lemma hasSum_moebius_col (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) {x : F × F} (hx : x.1 ≠ 0 ∨ x.2 ≠ 0) (t : UOrbitF F) :
    HasSum (fun S : Finset (HeightOneSpectrum (𝓞 F)) =>
      (-1 : ℂ) ^ S.card * eisWt2 f 𝔑 C (sqfIdeal S) (t.out * x.1, t.out * x.2) *
        (∏ v, (realEmb F v t.out : ℂ)) ^ (-(2 : ℤ)))
      (redPart f C (t.out * x.1, t.out * x.2) * (∏ v, (realEmb F v t.out : ℂ)) ^ (-(2 : ℤ))) := by
  by_cases ht : t.out = 0
  · simp only [ht, prod_realEmb_zero_zpow, mul_zero]; exact hasSum_zero
  · exact (hasSum_moebius_eisWt2 hf hfχ C (smul_ne_zero_vec hx ht)).mul_right _

lemma summable_redPart_col (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) {x : F × F} (hx : x.1 ≠ 0 ∨ x.2 ≠ 0) :
    Summable fun t : UOrbitF F =>
      redPart f C (t.out * x.1, t.out * x.2) * (∏ v, (realEmb F v t.out : ℂ)) ^ (-(2 : ℤ)) := by
  have hs := (summable_moebius_family h𝔑 hf hfχ C hx).comp_injective Prod.swap_injective
  exact hs.prod.congr fun t => (hasSum_moebius_col hf hfχ C hx t).tsum_eq

/-- **Fubini for the Möbius sum of constant terms**:
$\sum_S(-1)^{|S|}\,\mathrm c((\Phi_{C,\mathfrak d_S})_A) = \sum_{t\in U\backslash F}[\mathfrak b(tx_A) = \mathfrak b_C]\varphi_f(tx_A)N(t)^{-2}$. -/
theorem hasSum_moebius_eisConst (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) (A : SL(2, F)) :
    HasSum (fun S : Finset (HeightOneSpectrum (𝓞 F)) =>
      (-1 : ℂ) ^ S.card * eisConst (slashWeight (eisWt2 f 𝔑 C (sqfIdeal S)) A) 2)
      (∑' t : UOrbitF F, redPart f C (t.out * (-(A 1 0)), t.out * A 0 0) *
        (∏ v, (realEmb F v t.out : ℂ)) ^ (-(2 : ℤ))) := by
  have hx : (-(A 1 0), A 0 0).1 ≠ 0 ∨ (-(A 1 0), A 0 0).2 ≠ 0 := col_ne_zero A
  have hs := summable_moebius_family h𝔑 hf hfχ C hx
  have hrow : ∀ S : Finset (HeightOneSpectrum (𝓞 F)),
      (-1 : ℂ) ^ S.card * eisConst (slashWeight (eisWt2 f 𝔑 C (sqfIdeal S)) A) 2 =
        ∑' t : UOrbitF F, (-1 : ℂ) ^ S.card * eisWt2 f 𝔑 C (sqfIdeal S) (t.out * (-(A 1 0)), t.out * A 0 0) *
          (∏ v, (realEmb F v t.out : ℂ)) ^ (-(2 : ℤ)) := by
    intro S
    rw [eisConst_slash_eq (intWeight_eisWt2 h𝔑 hf hfχ C (sqfIdeal_ne_bot S)).unit A, ← tsum_mul_left]
    exact tsum_congr fun t => by ring
  rw [funext hrow]
  have h1 := hs.prod.hasSum
  rw [← Summable.tsum_comm (f := fun S t => (-1 : ℂ) ^ S.card *
    eisWt2 f 𝔑 C (sqfIdeal S) (t.out * (-(A 1 0)), t.out * A 0 0) *
      (∏ v, (realEmb F v (t : UOrbitF F).out : ℂ)) ^ (-(2 : ℤ))) hs] at h1
  convert h1 using 1
  exact tsum_congr fun t => ((hasSum_moebius_col hf hfχ C hx t).tsum_eq).symm

/-- **The Möbius sums of the constant terms recover the constant terms of $f$**: for every $A \in \mathrm{SL}_2(F)$,
$$\sum_{C\in\mathrm{Cl}_F}\sum_S(-1)^{|S|}\,\mathrm c\big((\Phi_{C,\mathfrak d_S})_A\big) = \mathrm{cv}_2(f, A).$$ -/
@[kb "hecke1927" "constant terms of the weight-2 Eisenstein series via Möbius inversion [unverified]"]
theorem sum_tsum_moebius_eisConst (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (A : SL(2, F)) :
    ∑ C : ClassGroup (𝓞 F), ∑' S : Finset (HeightOneSpectrum (𝓞 F)),
      (-1 : ℂ) ^ S.card * eisConst (slashWeight (eisWt2 f 𝔑 C (sqfIdeal S)) A) 2 = cuspVal f 2 A := by
  have hx : (-(A 1 0), A 0 0).1 ≠ 0 ∨ (-(A 1 0), A 0 0).2 ≠ 0 := col_ne_zero A
  rw [Finset.sum_congr rfl fun C _ => (hasSum_moebius_eisConst h𝔑 hf hfχ C A).tsum_eq,
    ← Summable.tsum_finsetSum fun C _ => summable_redPart_col h𝔑 hf hfχ C hx,
    ← eisConst_eisGenWeight hf A, eisConst_slash_eq (isUnitEquivariant_eisGenWeight hf) A]
  refine tsum_congr fun t => ?_
  rw [← Finset.sum_mul]
  by_cases ht : t.out = 0
  · simp only [ht, prod_realEmb_zero_zpow, mul_zero]
  · rw [sum_redPart (smul_ne_zero_vec hx ht)]

end ConstTerm

/-! ### Grouping by ray classes: finitely many periodic weights -/

section Ray

variable (𝔑 : Ideal (𝓞 F))

/-- The type of ray-class keys modulo $\mathfrak N$ (`rayKey`): $\mathrm{Cl}_F \times \mathcal{O}_F/\mathfrak N\mathfrak a_0$, finite for $\mathfrak N \ne 0$. -/
abbrev RayKeyT := ClassGroup (𝓞 F) × (𝓞 F ⧸ (𝔑 * repProd))

open Classical in
/-- **A fixed squarefree ideal of each key** $r$ (some $\mathfrak d_S$ with $\kappa(\mathfrak d_S) = r$; junk value $\mathcal{O}_F$ if there is none). -/
noncomputable def keyRep (r : RayKeyT 𝔑) : Ideal (𝓞 F) :=
  if h : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), rayKey 𝔑 (sqfIdeal S) = r then sqfIdeal h.choose else ⊤

lemma keyRep_ne_bot (r : RayKeyT 𝔑) : keyRep 𝔑 r ≠ ⊥ := by
  classical
  rw [keyRep]; split_ifs
  · exact sqfIdeal_ne_bot _
  · exact top_ne_bot

lemma rayKey_keyRep (S : Finset (HeightOneSpectrum (𝓞 F))) :
    rayKey 𝔑 (keyRep 𝔑 (rayKey 𝔑 (sqfIdeal S))) = rayKey 𝔑 (sqfIdeal S) := by
  classical
  have h : ∃ T : Finset (HeightOneSpectrum (𝓞 F)), rayKey 𝔑 (sqfIdeal T) = rayKey 𝔑 (sqfIdeal S) := ⟨S, rfl⟩
  rw [keyRep, dif_pos h]; exact h.choose_spec

lemma exists_keyScale (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ l : F, l ≠ 0 ∧ (sqfIdeal S : FI) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ l * (keyRep 𝔑 (rayKey 𝔑 (sqfIdeal S)) : FI) ∧
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (l - 1) * (keyRep 𝔑 (rayKey 𝔑 (sqfIdeal S)) : FI) ≤ (𝔑 : FI) :=
  exists_scale_of_rayKey_eq (sqfIdeal_ne_bot S) (keyRep_ne_bot 𝔑 _) (rayKey_keyRep 𝔑 S).symm

/-- **The scalar $\lambda_S$** with $\mathfrak d_S = \lambda_S\,\mathfrak d_{\kappa(\mathfrak d_S)}$ and $(\lambda_S - 1)\mathfrak d_{\kappa(\mathfrak d_S)} \subseteq \mathfrak N$. -/
noncomputable def keyScale (S : Finset (HeightOneSpectrum (𝓞 F))) : F := (exists_keyScale 𝔑 S).choose

lemma keyScale_ne_zero (S : Finset (HeightOneSpectrum (𝓞 F))) : keyScale 𝔑 S ≠ 0 :=
  (exists_keyScale 𝔑 S).choose_spec.1

open Classical in
/-- **The coefficient of the key $r$**: $a_r = \sum_{S:\ \kappa(\mathfrak d_S) = r}(-1)^{|S|}N(\lambda_S)^{-2}$, $N(\lambda) = \prod_v\sigma_v(\lambda)$
(a Möbius sum over a ray class; it does not depend on $f$). -/
@[kb "hecke1927" "coefficients of the Eisenstein series of level 𝔑: Möbius sums over ray classes [unverified]"]
noncomputable def eisGen2Coeff (r : RayKeyT 𝔑) : ℂ :=
  ∑' S : Finset (HeightOneSpectrum (𝓞 F)), if rayKey 𝔑 (sqfIdeal S) = r then
    (-1 : ℂ) ^ S.card * (∏ v, (realEmb F v (keyScale 𝔑 S) : ℂ)) ^ (-(2 : ℤ)) else 0

variable {𝔑} {f : (InfinitePlace F → ℍ) → ℂ} {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ}

lemma slashWeight_scaleWeight (V : F × F → ℂ) (t : Fˣ) (A : SL(2, F)) :
    slashWeight (scaleWeight V t) A = scaleWeight (slashWeight V A) t := by
  funext y
  simp only [slashWeight, HilbertModular.scaleWeight]
  congr 1
  ext <;> simp [scaleEquiv, rowMul] <;> ring

/-- **Constant terms within a ray class**: $\mathrm c((\Phi_{C,\mathfrak d_S})_A) = N(\lambda_S)^{-2}\,\mathrm c((\Phi_{C,\mathfrak d_r})_A)$, $r = \kappa(\mathfrak d_S)$. -/
theorem eisConst_eisWt2_sqf (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (A : SL(2, F)) :
    eisConst (slashWeight (eisWt2 f 𝔑 C (sqfIdeal S)) A) 2 =
      (∏ v, (realEmb F v (keyScale 𝔑 S) : ℂ)) ^ (-(2 : ℤ)) *
        eisConst (slashWeight (eisWt2 f 𝔑 C (keyRep 𝔑 (rayKey 𝔑 (sqfIdeal S)))) A) 2 := by
  obtain ⟨hl, he, hc⟩ := (exists_keyScale 𝔑 S).choose_spec
  rw [eisWt2_eq_scale hf hfχ C hl he hc, slashWeight_scaleWeight,
    eisConst_scaleWeight ((intWeight_eisWt2 h𝔑 hf hfχ C (keyRep_ne_bot 𝔑 _)).unit.slashWeight A)]
  rfl

/-- **Grouping the Möbius sum by ray classes**: for each class $C$,
$\sum_S(-1)^{|S|}\,\mathrm c((\Phi_{C,\mathfrak d_S})_A) = \sum_ra_r\,\mathrm c((\Phi_{C,\mathfrak d_r})_A)$, a finite sum. -/
theorem tsum_moebius_eq_sum_keys [Fintype (RayKeyT 𝔑)] (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) (A : SL(2, F)) :
    ∑' S : Finset (HeightOneSpectrum (𝓞 F)), (-1 : ℂ) ^ S.card * eisConst (slashWeight (eisWt2 f 𝔑 C (sqfIdeal S)) A) 2 =
      ∑ r : RayKeyT 𝔑, eisGen2Coeff 𝔑 r * eisConst (slashWeight (eisWt2 f 𝔑 C (keyRep 𝔑 r)) A) 2 := by
  classical
  set g : Finset (HeightOneSpectrum (𝓞 F)) → ℂ := fun S =>
    (-1 : ℂ) ^ S.card * eisConst (slashWeight (eisWt2 f 𝔑 C (sqfIdeal S)) A) 2
  have hg : Summable g := (hasSum_moebius_eisConst h𝔑 hf hfχ C A).summable
  have hsplit : ∀ S, g S = ∑ r : RayKeyT 𝔑, if rayKey 𝔑 (sqfIdeal S) = r then g S else 0 := by
    intro S; rw [Finset.sum_ite_eq]; simp
  have hsum : ∀ r ∈ (Finset.univ : Finset (RayKeyT 𝔑)),
      Summable fun S => if rayKey 𝔑 (sqfIdeal S) = r then g S else 0 := by
    intro r _
    refine (hg.indicator {S | rayKey 𝔑 (sqfIdeal S) = r}).congr fun S => ?_
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [tsum_congr hsplit, Summable.tsum_finsetSum hsum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [eisGen2Coeff, ← tsum_mul_right]
  refine tsum_congr fun S => ?_
  by_cases hS : rayKey 𝔑 (sqfIdeal S) = r
  · rw [if_pos hS, if_pos hS]
    simp only [g]
    rw [eisConst_eisWt2_sqf h𝔑 hf hfχ C S A, hS]
    ring
  · rw [if_neg hS, if_neg hS, zero_mul]

end Ray

/-! ### The Eisenstein series $E^{(2)}_f$ -/

section Main

variable {f : (InfinitePlace F → ℍ) → ℂ} {𝔑 : Ideal (𝓞 F)} {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ}

lemma keyLevel_ne_bot (h𝔑 : 𝔑 ≠ ⊥) (C : ClassGroup (𝓞 F)) (r : RayKeyT 𝔑) :
    𝔑 * repIdeal C * keyRep 𝔑 r ≠ ⊥ :=
  mul_ne_zero (mul_ne_zero h𝔑 (repIdeal_ne_bot C)) (keyRep_ne_bot 𝔑 r)

variable (f 𝔑) in
/-- $E^{(2)}_f$ for a chosen enumeration of the keys (see `eisGen2`). -/
noncomputable def eisGen2' [Fintype (RayKeyT 𝔑)] (h𝔑 : 𝔑 ≠ ⊥) : (InfinitePlace F → ℍ) → ℂ :=
  ∑ C : ClassGroup (𝓞 F), ∑ r : RayKeyT 𝔑,
    eisGen2Coeff 𝔑 r • eis2 (eisWt2 f 𝔑 C (keyRep 𝔑 r)) (𝔑 * repIdeal C * keyRep 𝔑 r) (keyLevel_ne_bot h𝔑 C r)

variable (f 𝔑) in
/-- **The weight-2 Eisenstein series with the constant terms of $f$**:
$$E^{(2)}_f = \sum_{C\in\mathrm{Cl}_F}\sum_{r}a_r\,E_2(\cdot; \Phi_{C,\mathfrak d_r}),$$
a finite combination of the weight-2 series (`eis2`, Hecke's limit) of the **integral** (periodic) weights $\Phi_{C,\mathfrak d_r}$
(`eisWt2`, level $\mathfrak N\mathfrak b_C\mathfrak d_r$), $r$ over the finitely many ray-class keys modulo $\mathfrak N$ (`rayKey`), with the Möbius
coefficients $a_r$ (`eisGen2Coeff`). Parameters: `f`, `𝔑` (level), `h𝔑 : 𝔑 ≠ ⊥`. -/
@[kb "hecke1927" "Eisenstein series of weight 2 and level 𝔑 with prescribed constant terms [unverified]"]
noncomputable def eisGen2 (h𝔑 : 𝔑 ≠ ⊥) : (InfinitePlace F → ℍ) → ℂ :=
  letI := finite_rayKey (F := F) h𝔑
  letI := Fintype.ofFinite (RayKeyT 𝔑)
  eisGen2' f 𝔑 h𝔑

theorem tendsto_eisGen2'_slash [Fintype (RayKeyT 𝔑)] (hd : 2 ≤ Fintype.card (InfinitePlace F)) (h𝔑 : 𝔑 ≠ ⊥)
    (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (A : SL(2, F)) :
    Tendsto (eisGen2' f 𝔑 h𝔑 ∣[(2 : ℤ)] slHom (realEmb F) A) atImInftyPi (𝓝 (cuspVal f 2 A)) := by
  rw [← sum_tsum_moebius_eisConst h𝔑 hf hfχ A,
    Finset.sum_congr rfl fun C _ => tsum_moebius_eq_sum_keys h𝔑 hf hfχ C A]
  have heq : eisGen2' f 𝔑 h𝔑 ∣[(2 : ℤ)] slHom (realEmb F) A = fun z => ∑ C : ClassGroup (𝓞 F),
      ∑ r : RayKeyT 𝔑, eisGen2Coeff 𝔑 r * (eis2 (eisWt2 f 𝔑 C (keyRep 𝔑 r)) (𝔑 * repIdeal C * keyRep 𝔑 r)
        (keyLevel_ne_bot h𝔑 C r) ∣[(2 : ℤ)] slHom (realEmb F) A) z := by
    funext z
    rw [eisGen2', sum_slash', Finset.sum_apply]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [sum_slash', Finset.sum_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [smul_slash, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  refine tendsto_finsetSum _ fun C _ => tendsto_finsetSum _ fun r _ => ?_
  exact (tendsto_eis2_slash hd (intWeight_eisWt2 h𝔑 hf hfχ C (keyRep_ne_bot 𝔑 r)) A).const_mul _

/-- **$E^{(2)}_f$ has the constant term of $f$ at every cusp** ($d \ge 2$): $(E^{(2)}_f\,|_2\,A)(z) \to \mathrm{cv}_2(f, A)$ for every
$A \in \mathrm{SL}_2(F)$. -/
@[kb "hecke1927" "constant terms of the weight-2 Eisenstein series at every cusp [unverified]"]
theorem tendsto_eisGen2_slash (hd : 2 ≤ Fintype.card (InfinitePlace F)) (h𝔑 : 𝔑 ≠ ⊥)
    (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (A : SL(2, F)) :
    Tendsto (eisGen2 f 𝔑 h𝔑 ∣[(2 : ℤ)] slHom (realEmb F) A) atImInftyPi (𝓝 (cuspVal f 2 A)) := by
  let := finite_rayKey (F := F) h𝔑
  let := Fintype.ofFinite (RayKeyT 𝔑)
  exact tendsto_eisGen2'_slash hd h𝔑 hf hfχ A

/-- Each $E_2(\cdot; \Phi_{C,\mathfrak d})$ lies in $M_2(\Gamma_0(\mathfrak N), \chi)$ ($d \ge 2$). -/
theorem eis2_eisWt2_mem_modularFormChar (hd : 2 ≤ Fintype.card (InfinitePlace F)) (h𝔑 : 𝔑 ≠ ⊥)
    (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) {𝔡 : Ideal (𝓞 F)} (h𝔡 : 𝔡 ≠ ⊥) (h𝔐 : 𝔑 * repIdeal C * 𝔡 ≠ ⊥) :
    eis2 (eisWt2 f 𝔑 C 𝔡) (𝔑 * repIdeal C * 𝔡) h𝔐 ∈ modularFormChar 𝔑 χ 2 := by
  have hW := intWeight_eisWt2 h𝔑 hf hfχ C h𝔡
  have hlaw : ∀ γ ∈ Gamma0R 𝔑, eis2 (eisWt2 f 𝔑 C 𝔡) (𝔑 * repIdeal C * 𝔡) h𝔐 ∣[(2 : ℤ)]
      slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • eis2 (eisWt2 f 𝔑 C 𝔡) _ h𝔐 :=
    fun γ hγ => eis2_slash_of_weight hd hW (toF F γ) (slashWeight_eisWt2 hf hfχ C 𝔡 hγ)
  refine ⟨?_, hlaw⟩
  refine mem_modularFormSpace_of_GammaFull_le hd 𝔑 h𝔑 (GammaFull_le_Gamma1 𝔑) ?_ (isHolomorphic_eis2 hW)
  rintro _ ⟨γ, hγ, rfl⟩
  have h1 := (mem_Gamma1R 𝔑).mp hγ
  rw [hlaw γ h1.1, h1.2, map_one, one_smul]

/-- **$E^{(2)}_f \in M_2(\Gamma_0(\mathfrak N), \chi)$** ($d \ge 2$, $\mathfrak N \ne 0$), for $f$ with constant terms at all cusps and the
$\Gamma_0(\mathfrak N)$-law with character $\chi$. -/
@[kb "shimura1978" "§3, Eisenstein series of weight 2 in M₂(Γ₀(𝔑), χ) [unverified]"]
theorem eisGen2_mem_modularFormChar (hd : 2 ≤ Fintype.card (InfinitePlace F)) (h𝔑 : 𝔑 ≠ ⊥)
    (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f) :
    eisGen2 f 𝔑 h𝔑 ∈ modularFormChar 𝔑 χ 2 := by
  let := finite_rayKey (F := F) h𝔑
  let := Fintype.ofFinite (RayKeyT 𝔑)
  show eisGen2' f 𝔑 h𝔑 ∈ _
  refine Submodule.sum_mem _ fun C _ => Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ ?_
  exact eis2_eisWt2_mem_modularFormChar hd h𝔑 hf hfχ C (keyRep_ne_bot 𝔑 r) _

/-- **Every $f \in M_2(\Gamma_0(\mathfrak N), \chi)$ with constant terms at all cusps is Eisenstein plus cuspidal** ($d \ge 2$):
$$f - E^{(2)}_f \in S_2(\Gamma_0(\mathfrak N), \chi),$$
with $E^{(2)}_f$ (`eisGen2`) a finite combination of weight-2 series of periodic weights. The weight-2 analogue of `sub_eisGen_mem_cuspFormChar` ($k \ge 3$). -/
@[kb "shimura1978" "§3, M₂ = E₂ ⊕ S₂ (Eisenstein part with the same constant terms), [F:ℚ] ≥ 2 [unverified]"]
theorem sub_eisGen2_mem_cuspFormChar (hd : 2 ≤ Fintype.card (InfinitePlace F)) (h𝔑 : 𝔑 ≠ ⊥)
    (hfM : f ∈ modularFormChar 𝔑 χ 2) (hf : HasCuspLimits f 2) :
    f - eisGen2 f 𝔑 h𝔑 ∈ cuspFormChar 𝔑 χ 2 := by
  have hE := eisGen2_mem_modularFormChar hd h𝔑 hf hfM.2
  have hsub := (modularFormChar 𝔑 χ 2).sub_mem hfM hE
  exact ⟨⟨hsub.1.1, hsub.1.2.1, fun A =>
    isZeroAtImInftyPi_sub (tendsto_cuspVal hf A) (tendsto_eisGen2_slash hd h𝔑 hf hfM.2 A)⟩, hsub⟩

end Main

end QuadFormsKB.HilbertModular
