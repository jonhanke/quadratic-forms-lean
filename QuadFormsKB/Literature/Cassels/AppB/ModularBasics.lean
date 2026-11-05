/-
# Cassels, Appendix B, Section 5: basic modular form statements, from Mathlib

Cassels, *Rational Quadratic Forms* (1978), Appendix B (*Analytic methods*), §5 (*Modular forms*), pp. 383-387.

**Formalized (all from Mathlib; no objects are redefined).**
* the Möbius action of $\Gamma = \mathrm{SL}_2(\mathbb Z)$ on the upper half plane, the weight $k$ slash action and
  its cocycle law (5.8)-(5.10);
* the defining properties of modular forms and cusp forms (5.11), for Mathlib's `ModularForm` and `CuspForm`;
* finite dimensionality of the space of modular forms (level one only);
* the Eisenstein series $E_k$ of level one: the sum over coprime pairs (5.12), vanishing for odd $k$, and the Fourier
  series (5.13);
* the decomposition "Eisenstein series plus a cusp form" (level one);
* every cusp form of weight $12$ and level one is a multiple of the discriminant function (5.25), and its product
  formula.

**Conventions.**
* Mathlib's slash action is written `f ∣[k] γ`; for $\gamma\in\mathrm{SL}_2(\mathbb Z)$ it equals Cassels'
  $\phi|_k\gamma$.
* Mathlib's `E hk` (for $3 \le k$) is the *normalised* Eisenstein series, with constant term $1$, that is half of the
  sum over coprime pairs $(c,d)$ (both $(c,d)$ and $(-c,-d)$ occur in that sum). Cassels' $E_k$ is therefore
  `2 • E hk`, with constant term $2$ as in (5.13).
* Mathlib proves finite dimensionality, the Eisenstein decomposition and the structure of cusp forms for level one
  ($\Lambda=\Gamma$, trivial character) only; general finite index subgroups and characters are not covered.
* Cassels prints absolute convergence of (5.12) for $k\ge 4$; it holds already for every integer $k\ge 3$ (and the sum
  vanishes for odd $k$ by the symmetry $(c,d)\mapsto(-c,-d)$). We use $k\ge 3$ as Mathlib does.
* Erratum for (5.13): see `eisenstein_fourier_series` and `eisenstein_all_pairs_fourier_series`.
* Cassels' $q$-variable is written $e^{2\pi i t}$; $t$ is a point of the upper half plane `ℍ`.
-/
import Mathlib
import QuadFormsKB.Citation

open Complex
open UpperHalfPlane hiding I
open ModularForm EisensteinSeries
open scoped MatrixGroups Real Manifold ArithmeticFunction.sigma

namespace QuadFormsKB.Cassels

/-- **Cassels, Appendix B, §5, (5.8)-(5.9) (p. 383).** The action of $\sigma=\begin{pmatrix}a&b\\c&d\end{pmatrix}
\in\mathrm{SL}_2(\mathbb Z)$ on the upper half plane is $t\mapsto (at+b)/(ct+d)$. Arguments: `γ` the matrix,
`t` the point of the upper half plane `ℍ`; the left side is the complex number underlying `γ • t`. -/
@[kb "cassels1978" "App. B, §5, (5.8)-(5.9), p. 383 (Möbius action of SL₂(ℤ) on the upper half plane)"]
theorem modular_action_formula (γ : SL(2, ℤ)) (t : ℍ) :
    ((γ • t : ℍ) : ℂ) =
      ((γ 0 0 : ℂ) * t + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * t + (γ 1 1 : ℂ)) := by
  simpa using UpperHalfPlane.coe_specialLinearGroup_apply γ t

/-- **Cassels, Appendix B, §5, p. 384 (the weight $k$ slash action, formula before (5.10)).**
$(\phi|_k\sigma)(t)=(ct+d)^{-k}\phi(\sigma t)$ for $\sigma=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\mathrm{SL}_2(\mathbb Z)$.
Arguments: `k` the weight (an integer), `φ` a function on `ℍ`, `γ` the matrix, `t` the point. -/
@[kb "cassels1978" "App. B, §5, (5.10), p. 384 (slash action formula)"]
theorem slash_action_formula (k : ℤ) (φ : ℍ → ℂ) (γ : SL(2, ℤ)) (t : ℍ) :
    (φ ∣[k] γ) t = ((γ 1 0 : ℂ) * t + (γ 1 1 : ℂ)) ^ (-k) * φ (γ • t) := by
  rw [ModularForm.SL_slash_apply, mul_comm]
  rfl

/-- **Cassels, Appendix B, §5, (5.10), p. 384.** The slash action is an action: $(\phi|_k\sigma)|_k\tau
=\phi|_k(\sigma\tau)$. Arguments: `k` the weight, `φ` a function on `ℍ`, `γ τ` elements of $\mathrm{SL}_2(\mathbb Z)$. -/
@[kb "cassels1978" "App. B, §5, (5.10), p. 384 (cocycle law for the slash action)"]
theorem slash_action_mul (k : ℤ) (φ : ℍ → ℂ) (γ τ : SL(2, ℤ)) :
    (φ ∣[k] γ) ∣[k] τ = φ ∣[k] (γ * τ) :=
  (SlashAction.slash_mul k γ τ φ).symm

/-- **Cassels, Appendix B, §5, (5.11), p. 384 (modular forms; trivial character $\varepsilon=1$).** A Mathlib modular
form $\phi$ of weight $k$ for a subgroup `Γ` is invariant under the slash action of every element of `Γ`, holomorphic
on the upper half plane, and bounded at every cusp. Arguments: `Γ` the subgroup of $\mathrm{GL}_2(\mathbb R)$ (for
Cassels, a finite index subgroup of $\mathrm{SL}_2(\mathbb Z)$), `k` the weight, `φ` the modular form. Mathlib's
boundedness at a cusp is formulated with the slash action transporting the cusp to infinity, as Cassels describes. -/
@[kb "cassels1978" "App. B, §5, p. 384 (modular forms; ε = 1)"]
theorem modularForm_properties {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (φ : ModularForm Γ k) :
    (∀ γ ∈ Γ, (φ : ℍ → ℂ) ∣[k] γ = φ) ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (φ : ℍ → ℂ) ∧
      ∀ {c : OnePoint ℝ}, IsCusp c Γ → c.IsBoundedAt φ k :=
  ⟨fun γ hγ => φ.slash_action_eq' γ hγ, φ.holo', fun hc => φ.bdd_at_cusps' hc⟩

/-- **Cassels, Appendix B, §5, p. 384 (cusp forms; trivial character $\varepsilon=1$).** A Mathlib cusp form of weight
$k$ for `Γ` is invariant under the slash action of `Γ`, holomorphic, and takes the value $0$ at every cusp. Arguments as
in `modularForm_properties`. -/
@[kb "cassels1978" "App. B, §5, p. 384 (cusp forms; ε = 1)"]
theorem cuspForm_properties {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (φ : CuspForm Γ k) :
    (∀ γ ∈ Γ, (φ : ℍ → ℂ) ∣[k] γ = φ) ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (φ : ℍ → ℂ) ∧
      ∀ {c : OnePoint ℝ}, IsCusp c Γ → c.IsZeroAt φ k :=
  ⟨fun γ hγ => φ.slash_action_eq' γ hγ, φ.holo', fun hc => φ.zero_at_cusps' hc⟩

/-- **Cassels, Appendix B, §5, p. 384 (finite dimensionality; here level one).** The space $M(k,\Gamma)$ of modular
forms of weight $k$ for $\Gamma=\mathrm{SL}_2(\mathbb Z)$ (trivial character) is finite dimensional over $\mathbb C$.
Cassels states this for every finite index subgroup and every character of finite order; Mathlib has level one only.
Argument: `k` the weight (an integer). -/
@[kb "cassels1978" "App. B, §5, p. 384 (finite dimensionality; here level one)"]
theorem modularForm_finiteDimensional (k : ℤ) : FiniteDimensional ℂ (ModularForm 𝒮ℒ k) :=
  inferInstance

/-- **Cassels, Appendix B, §5, (5.12) (pp. 384-385): the Eisenstein series as a sum over coprime pairs.** For
$k\ge 3$ and $t$ in the upper half plane, Cassels' $E_k(t)=\sum_{(c,d)=1}(ct+d)^{-k}$ (sum over all pairs of coprime
integers, so $(c,d)$ and $(-c,-d)$ both occur) equals twice Mathlib's normalised `E hk`. Arguments: `k` the weight,
`hk : 3 ≤ k`, `t` the point. -/
@[kb "cassels1978" "App. B, §5, (5.12), pp. 384-385 (Eisenstein series; Cassels' E_k = 2 * Mathlib's E)"]
theorem eisenstein_two_mul_eq_sum_coprime {k : ℕ} (hk : 3 ≤ k) (t : ℍ) :
    (2 : ℂ) * E hk t =
      ∑' v : gammaSet 1 1 0, ((v.1 0 : ℂ) * t + (v.1 1 : ℂ)) ^ (-(k : ℤ)) := by
  have h : E hk t = (1 / 2 : ℂ) * eisensteinSeries (0 : Fin 2 → ZMod 1) k t := rfl
  rw [h, ← mul_assoc]
  norm_num [eisensteinSeries, eisSummand]

/-- **Cassels, Appendix B, §5, p. 384 (the Eisenstein series vanishes for odd $k$).** For odd $k\ge 3$ the sum over
coprime pairs $(c,d)$ of $(ct+d)^{-k}$ is $0$ (Mathlib: the level one modular form of odd weight is zero, since
$-I\in\mathrm{SL}_2(\mathbb Z)$). Arguments: `k` the odd weight, `hk : 3 ≤ k`, `t` the point. -/
@[kb "cassels1978" "App. B, §5, p. 384 (Eisenstein series vanish for odd k)"]
theorem eisenstein_sum_coprime_odd {k : ℕ} (hk : 3 ≤ k) (hodd : Odd k) (t : ℍ) :
    ∑' v : gammaSet 1 1 0, ((v.1 0 : ℂ) * t + (v.1 1 : ℂ)) ^ (-(k : ℤ)) = 0 := by
  rw [← eisenstein_two_mul_eq_sum_coprime hk t]
  have : E hk = 0 :=
    ModularForm.levelOne_odd_weight_eq_zero (by exact_mod_cast hodd) _
  simp [this]

/-- **Cassels, Appendix B, §5, (5.13) (p. 384): the Fourier series of the Eisenstein series.** For even $k\ge 4$ and
$t$ in the upper half plane,
$$2\,E_k^{\mathrm{Mathlib}}(t) = 2+\frac{2(2\pi i)^k}{(k-1)!\,\zeta(k)}\sum_{n\ge 1}\sigma_{k-1}(n)\,e^{2\pi i n t},$$
where $\sigma_{k-1}(n)=\sum_{d\mid n}d^{k-1}$; by `eisenstein_two_mul_eq_sum_coprime` the left side is Cassels'
$E_k(t)$. Arguments: `k` the even weight, `hk : 3 ≤ k` (so $k\ge 4$), `hk2 : Even k`, 
*Erratum:* as printed, (5.13) has $(2\pi i)^{k/2}$ where $(2\pi i)^{k}$ is correct, and its constant term $2\zeta(k)$
is the constant term of the sum over *all* pairs $(c,d)\ne(0,0)$ (see `eisenstein_all_pairs_fourier_series`), not of
the sum over coprime pairs that (5.12) defines $E_k$ to be. For the coprime sum (5.12) the series is the one displayed
here, $2+\frac{2(2\pi i)^k}{(k-1)!\,\zeta(k)}\sum\sigma_{k-1}(n)e^{2\pi i n t}$. Confirmed by the Mathlib proof
(constant term of the normalised series is $1$; the two sums differ by the factor $\zeta(k)$). -/
@[kb "cassels1978" "App. B, §5, (5.13), p. 384 (Fourier series of E_k)"]
theorem eisenstein_fourier_series {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (t : ℍ) :
    (2 : ℂ) * E hk t =
      2 + 2 * (2 * π * I) ^ k / ((k - 1).factorial * riemannZeta k) *
        ∑' n : ℕ+, (σ (k - 1) n : ℂ) * cexp (2 * π * I * n * t) := by
  have h := EisensteinSeries.q_expansion_riemannZeta hk hk2 t
  have hz : (-2 * π * I) ^ k = (2 * π * I) ^ k := by
    rw [show (-2 * π * I : ℂ) = -(2 * π * I) by ring]
    exact hk2.neg_pow _
  have hs : ∀ n : ℕ+, cexp (2 * π * I * t) ^ (n : ℤ) = cexp (2 * π * I * n * t) := by
    intro n
    rw [← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  simp_rw [hs] at h
  rw [h, hz]
  ring

/-- **Cassels, Appendix B, §5, (5.13) (p. 385), corrected: the Fourier series of the sum over all nonzero pairs.** For
even $k\ge 4$ and $t$ in the upper half plane,
$$G_k(t)=\sum_{(c,d)\ne(0,0)}(ct+d)^{-k}=2\zeta(k)+\frac{2(2\pi i)^k}{(k-1)!}\sum_{r\ge1}\sigma_{k-1}(r)\,e^{2\pi i r t},$$
with $\sigma_{k-1}(r)=\sum_{d\mid r}d^{k-1}$. Arguments: `k` the even weight, `hk : 3 ≤ k` (so $k\ge 4$), `hk2 : Even k`,
`t` the point; the sum runs over the nonzero integer pairs, written as nonzero functions `Fin 2 → ℤ` (index 0 is $c$,
index 1 is $d$).

*Erratum:* the printed formula (5.13) has $(2\pi i)^{k/2}$, which should be $(2\pi i)^{k}$, and its constant term
$2\zeta(k)$ belongs to this sum over all nonzero pairs, not to the sum over coprime pairs that (5.12) defines as $E_k$;
for the coprime sum the series is `eisenstein_fourier_series`. Confirmed by the Mathlib proof, which gives
$G_k=\zeta(k)\cdot(\text{coprime sum})$ and the exponent $k$. -/
@[kb "cassels1978" "App. B, §5, (5.13), p. 385 (corrected: the series over all (c, d) ≠ (0, 0), exponent k)"]
theorem eisenstein_all_pairs_fourier_series {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (t : ℍ) :
    ∑' v : {v : Fin 2 → ℤ // v ≠ 0}, ((v.1 0 : ℂ) * t + (v.1 1 : ℂ)) ^ (-(k : ℤ)) =
      2 * riemannZeta k + 2 * (2 * π * I) ^ k / (k - 1).factorial *
        ∑' n : ℕ+, (σ (k - 1) n : ℂ) * cexp (2 * π * I * n * t) := by
  have h := tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow hk hk2 t
  have hz : (-2 * π * I) ^ k = (2 * π * I) ^ k := by
    rw [show (-2 * π * I : ℂ) = -(2 * π * I) by ring]
    exact hk2.neg_pow _
  have hs : ∀ n : ℕ+, cexp (2 * π * I * t) ^ (n : ℕ) = cexp (2 * π * I * n * t) := by
    intro n
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  simp_rw [hs] at h
  rw [hz] at h
  have hsub : ∑' v : {v : Fin 2 → ℤ // v ≠ 0}, ((v.1 0 : ℂ) * t + (v.1 1 : ℂ)) ^ (-(k : ℤ)) =
      ∑' v : Fin 2 → ℤ, eisSummand k v t := by
    refine tsum_subtype_eq_of_support_subset (s := {v : Fin 2 → ℤ | v ≠ 0})
      (f := fun v => eisSummand k v t) ?_
    intro v hv
    by_contra h0
    simp only [Set.mem_ofPred_eq, not_not] at h0
    apply hv
    subst h0
    simp [eisSummand]
    omega
  rw [hsub, h]
  ring

/-- **Cassels, Appendix B, §5, p. 385 (an Eisenstein series plus a cusp form; here level one).** For even $k\ge 4$,
every modular form $f$ of weight $k$ for $\mathrm{SL}_2(\mathbb Z)$ is uniquely of the form $c\,E_k+g$ with
$c\in\mathbb C$ and $g$ a cusp form, where $E_k$ is Cassels' Eisenstein series (twice Mathlib's `E hk`). Arguments:
`k` the weight, `hk : 3 ≤ k`, `hk2 : Even k`, `f` the modular form; the pair is `(c, g)`. Cassels states this for all
finite index subgroups and several Eisenstein series, one per class of cusps; Mathlib has level one only. -/
@[kb "cassels1978" "App. B, §5, p. 385 (Eisenstein series plus a cusp form; here level one)"]
theorem modularForm_eq_eisenstein_add_cusp {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k)
    (f : ModularForm 𝒮ℒ k) :
    ∃! p : ℂ × CuspForm 𝒮ℒ k,
      f = p.1 • ((2 : ℂ) • E hk) + CuspForm.toModularFormₗ p.2 := by
  have hE0 := EisensteinSeries.E_qExpansion_coeff_zero hk hk2
  -- the constant term of the q-expansion is additive and scalar-linear
  have key : ∀ (c : ℂ) (g : CuspForm 𝒮ℒ k),
      (qExpansion 1 ((c • ((2 : ℂ) • E hk) + CuspForm.toModularFormₗ g : ModularForm 𝒮ℒ k) :
        ℍ → ℂ)).coeff 0 = 2 * c := by
    intro c g
    have hg : (qExpansion 1 (CuspForm.toModularFormₗ g : ModularForm 𝒮ℒ k)).coeff 0 = 0 :=
      (isCuspForm_iff_coeffZero_eq_zero _).mp (CuspForm.isCuspForm_toModularFormₗ g)
    rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL,
      FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
    rw [map_add, PowerSeries.coeff_smul, PowerSeries.coeff_smul, hE0, hg]
    simp [mul_comm]
  obtain ⟨g, hg⟩ := sub_smul_isCuspForm f (E hk) hE0
  refine ⟨((qExpansion 1 f).coeff 0 / 2, g), ?_, ?_⟩
  · show f = _ • _ + _
    have hg' : (CuspForm.toModularFormₗ g : ModularForm 𝒮ℒ k) =
        f - (qExpansion 1 f).coeff 0 • E hk := hg
    rw [hg', smul_smul, show (qExpansion 1 f).coeff 0 / 2 * 2 = (qExpansion 1 f).coeff 0 by ring]
    abel
  · rintro ⟨c', g'⟩ h
    have h' : f = c' • ((2 : ℂ) • E hk) + CuspForm.toModularFormₗ g' := h
    have hc : (qExpansion 1 f).coeff 0 = 2 * c' := by
      have := key c' g'
      rwa [← h'] at this
    have hg' : (CuspForm.toModularFormₗ g : ModularForm 𝒮ℒ k) =
        f - (qExpansion 1 f).coeff 0 • E hk := hg
    have e1 : (CuspForm.toModularFormₗ g' : ModularForm 𝒮ℒ k) =
        f - (2 * c') • E hk := by
      rw [h', smul_smul, mul_comm c' 2]
      abel
    have e2 : g' = g := by
      apply CuspForm.toModularFormₗ_injective
      rw [hg', e1, hc]
    have e3 : c' = (qExpansion 1 f).coeff 0 / 2 := by rw [hc]; ring
    rw [e2, e3]

/-- **Cassels, Appendix B, §5, (5.25) (p. 387): cusp forms of weight $12$ and level one.** Every cusp form $f$ of weight
$12$ for $\mathrm{SL}_2(\mathbb Z)$ is a complex multiple of the discriminant function $\Delta$ (Cassels' $G$ with
$z=e^{2\pi i t}$; see `discriminant_product_formula`). Arguments: `f` the cusp form; `c` the multiple. -/
@[kb "cassels1978" "App. B, §5, (5.25), p. 387 (weight 12 cusp forms are multiples of the discriminant)"]
theorem cuspForm_weight_twelve_eq_smul_discriminant (f : CuspForm 𝒮ℒ 12) :
    ∃ c : ℂ, c • CuspForm.discriminant = f :=
  CuspForm.exists_smul_discriminant_of_weight_eq_twelve f

/-- **Cassels, Appendix B, §5, (5.25) (p. 387): product formula for the discriminant function.** For $t$ in the upper
half plane and $z=e^{2\pi i t}$, $\Delta(t)=z\prod_{m\ge 1}(1-z^m)^{24}$ (Cassels' $G(z)=z\prod(1-z^m)^{24}$; the
infinite product is Mathlib's `tprod`, indexed from $m=1$ via $m\mapsto n+1$). Argument: `t` the point. -/
@[kb "cassels1978" "App. B, §5, (5.25), p. 387 (product formula for the discriminant function)"]
theorem discriminant_product_formula (t : ℍ) :
    ModularForm.discriminant t =
      cexp (2 * π * I * t) * ∏' n : ℕ, (1 - cexp (2 * π * I * t) ^ (n + 1)) ^ 24 := by
  rw [ModularForm.discriminant_eq_q_prod]
  simp [Function.Periodic.qParam, eta_q_eq_pow]

end QuadFormsKB.Cassels
