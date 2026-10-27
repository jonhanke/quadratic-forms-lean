/-
# The mass formula by Weil's induction on the dimension

**Layer:** forms over $\mathcal O_F$, $F$ a totally real number field, with the split form
$Q_0 = \langle m\rangle \perp Q_0'$ (`splitForm`), $m \in \mathcal O_F$, $m \ne 0$; the standard lattices $L = \mathcal O_F^{n+1}$
and $L' = \mathcal O_F^n$; the mass formula in the explicit form $\mathrm{Mass}(L) = 1/\mu_{\mathrm{Tam}}(K_{SO})$
(`massFormula`, `tamagawaK`).

## The argument (Weil, *Adeles and Algebraic Groups*, §§3.4–3.5 [unverified locator]; Siegel 1935/1936; Kneser)
1. **Global reduction** (`repMass_eq_mass_mul`, proved): $\sum_{\mathrm{cls}(M)} r_M(m)/|O(M)| = \mathrm{Mass}(L')\cdot W$,
   $W = \sum_t w(t)$ over the local types $t$ of pairs $(M, e_0)$, $w(t) = \mu(K_0')/\mu(K_t)$.
2. **Siegel's formula for the number $m$** (hypothesis `SiegelFormulaAt`):
   $\sum_{\mathrm{cls}(M)} r_M(m)/|O(M)| = \mathrm{Mass}(L)\cdot|d_F|^{-n/2}\prod_\sigma\beta_\sigma(m)\prod_\mathfrak p\beta_\mathfrak p(L, m)$.
3. **The local identity** (hypothesis `LocalOrbitalIdentity`): $W\cdot\prod_\mathfrak p\alpha_\mathfrak p(L) =
   |N_{F/\mathbb Q}(2m)|^n\prod_\mathfrak p\alpha_\mathfrak p(L')\prod_\mathfrak p\beta_\mathfrak p(L, m)$: Weil's fibration
   $O(V_\mathfrak p) \to \{v : Q(v) = m\}$, $g \mapsto ge_0$, with fibre $O(e_0^\perp)$, prime by prime.
4. **The archimedean identity** (`archVolSO_succ`, proved): $\mathrm{vol}(SO_{n+1}(\mathbb R))\,(2a)^n =
   \mathrm{vol}(SO_n(\mathbb R))\,\beta_\infty(a)$ for the gauge forms in coefficient coordinates; this is the same
   fibration at a real place, and $\prod_\sigma|\sigma(2m)|^n = |N(2m)|^n$ is the product formula's archimedean half.
5. **Induction** (`massFormula_succ`): 1–4 and the mass formula for $L'$ (rank $n$) give the mass formula for $L$
   (rank $n+1$). Consequently $\tau(SO) = 2$ for $Q_0$ (`tamagawaNumberTwo_succ`).

## Hypothesis hygiene
* `SiegelFormulaAt Q₀ m` is about **representation numbers** $r_M(m)$ averaged over the genus. It never determines
  $\mathrm{Mass}(L)$: it is the statement $r_{\mathrm{gen}}(L, m) = (\text{local densities of } m)$ for the *ratio*
  $\mathrm{repMass}/\mathrm{Mass}$, true or false independently of the value of $\mathrm{Mass}(L)$. It is the degree-1 Siegel
  formula, supplied over $\mathbb Q$ for $n+1 = 4$ by `siegelFormula_quaternary` (after the form/lattice bridge)
  and over $F$ by the Hilbert-modular-form argument.
* `LocalOrbitalIdentity Q₀' m` mentions **no global classes and no masses**: only local densities, the norm of $2m$, and
  the sum over $O(Q')(\mathbb A_f)$-orbits of index ratios of compact open subgroups. It is a product of purely local
  statements (one per prime; the identity holds with all factors $1$ at primes $\mathfrak p \nmid 2m\det H$), so it does
  not depend on the class numbers of either genus.
* The induction hypothesis is the mass formula itself, in rank $n$.

Given 1 (proved) and 4 (proved), the three inputs imply the conclusion; none of them alone is equivalent to it.
In particular this file does not use `TamagawaNumberTwo` (which is definitionally the mass formula); instead it
**proves** `TamagawaNumberTwo` for $Q_0$ from the induction (`tamagawaNumberTwo_succ`).

## Scope
* The step needs $L = \mathcal O_F e_0 \perp \mathcal O_F^n$ (a split standard lattice). General genera need the
  invariance of $\mu_{\mathrm{Tam}}$ under change of lattice in a fixed space (not formalized here).
* `tamagawaK` uses Mathlib's unconditional `tprod`, which has the intended value only when the Euler products converge
  absolutely: $n \ge 3$ for the complement ($\prod\alpha_\mathfrak p(L')$) and $n + 1 \ge 4$ for $\prod\beta_\mathfrak p(L, m)$.
  So the step is meaningful from complement rank $3$ on, i.e. it proves the mass formula in rank $n+1 \ge 4$ from rank
  $n \ge 3$.
-/
import QuadFormsKB.Tamagawa.RepMass

open NumberField IsDedekindDomain Matrix MulAction
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices

/-! ### The archimedean identity -/

/-- **The archimedean representation density** $\beta_\infty(a) = \dfrac{\pi^{N/2}}{\Gamma(N/2)}\,a^{(N-2)/2}\,d^{-1/2}$ of
$a > 0$ by a positive definite real form in $N$ variables with Gram determinant $d = \det(H/2)$ (Siegel 1935, §1
[unverified]; Hanke 2004, (5.5), p. 369, there written $\frac{N\omega_N}{2}D^{-1/2}a^{(N-2)/2}$, the same number since
$N\omega_N/2 = \pi^{N/2}/\Gamma(N/2)$). For a form over $F$ and an embedding $\sigma$ it is evaluated at
$a = |\sigma(m)|$, $d = $ `detGram Q₀ σ`; this agrees with `Siegel.betaInfAt` (the real place of $\sigma$). -/
@[kb "siegel1935" "§1 (archimedean density) [unverified]"]
def archRepDensity (N : ℕ) (a d : ℝ) : ℝ :=
  Real.pi ^ ((N : ℝ) / 2) / Real.Gamma ((N : ℝ) / 2) * a ^ (((N : ℝ) - 2) / 2) * d ^ (-(1 / 2 : ℝ))

theorem nat_tri_succ (n : ℕ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  rcases n with _ | k
  · simp
  · rw [show (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) by
      simp only [Nat.add_sub_cancel]; ring, Nat.add_mul_div_left _ _ two_pos]

/-- **The archimedean fibration identity** ($a, d > 0$): with $\mathrm{vol}(SO_N(\mathbb R))$ = `archVolSO N` (gauge form
$dX/dQ$ in coefficient coordinates),
$$\mathrm{vol}\big(SO_{n+1}(\mathbb R), ad\big)\cdot(2a)^n = \mathrm{vol}\big(SO_n(\mathbb R), d\big)\cdot\beta_\infty(a)$$
for $\langle a\rangle \perp A'$ with $\det A' = d$ (so the Gram determinant is $ad$). This is Weil's fibration
$SO_{n+1} \to \{Q(v) = a\}$ at a real place; the factor $(2a)^n$ is the Jacobian of the cross terms
$c_{0j} = B(e_0, y_j) = 2a\,y_{j,0}$ (Weil 1982, §3.4 [unverified]). -/
@[kb "weil1982" "§3.4 (fibration of gauge forms) [unverified]"]
theorem archVolSO_succ (n : ℕ) {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    archVolSO (n + 1) (a * d) * (2 * a) ^ n = archVolSO n d * archRepDensity (n + 1) a (a * d) := by
  unfold archVolSO archRepDensity
  rw [Finset.prod_range_succ, nat_tri_succ, pow_add, Real.mul_rpow ha.le hd.le, Real.mul_rpow ha.le hd.le]
  set P := ∏ j ∈ Finset.range n, Real.pi ^ (((j : ℝ) + 1) / 2) / Real.Gamma (((j : ℝ) + 1) / 2)
  set A := (2 : ℝ) ^ (n * (n - 1) / 2)
  have hA : A ≠ 0 := by positivity
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  push_cast
  have ea : a ^ (-((n : ℝ) + 1 + 1) / 2) * a ^ n = a ^ (((n : ℝ) + 1 - 2) / 2) * a ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ha, ← Real.rpow_add ha]; ring_nf
  have ed : d ^ (-((n : ℝ) + 1 + 1) / 2) = d ^ (-((n : ℝ) + 1) / 2) * d ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hd]; ring_nf
  rw [ed, mul_pow, ← mul_assoc]
  have key : a ^ (-((n : ℝ) + 1 + 1) / 2) * a ^ n = a ^ (((n : ℝ) + 1 - 2) / 2) * a ^ (-(1 / 2 : ℝ)) := ea
  calc 1 / 2 * (A * 2 ^ n)⁻¹ * (a ^ (-((n : ℝ) + 1 + 1) / 2) *
          (d ^ (-((n : ℝ) + 1) / 2) * d ^ (-(1 / 2 : ℝ)))) *
          (P * (Real.pi ^ (((n : ℝ) + 1) / 2) / Real.Gamma (((n : ℝ) + 1) / 2))) * 2 ^ n * a ^ n
        = 1 / 2 * A⁻¹ * d ^ (-((n : ℝ) + 1) / 2) * P *
          (Real.pi ^ (((n : ℝ) + 1) / 2) / Real.Gamma (((n : ℝ) + 1) / 2) *
            (a ^ (-((n : ℝ) + 1 + 1) / 2) * a ^ n) * d ^ (-(1 / 2 : ℝ))) := by
          field_simp
      _ = _ := by rw [key]; ring

/-! ### Number-field data of the split form -/

section NF

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem detGram_splitForm (m : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) (σ : F →ₐ[ℚ] ℂ) :
    detGram (splitForm m Q₀') σ = ‖σ (algebraMap (𝓞 F) F m)‖ * detGram Q₀' σ := by
  unfold detGram
  rw [det_hessian_splitForm, ← norm_mul, ← map_mul]
  congr 2
  simp only [map_mul, map_ofNat]
  field_simp
  ring

theorem detGram_pos {Q₀ : QuadForm (𝓞 F) n} (hQ : Q₀.Nondegenerate) (σ : F →ₐ[ℚ] ℂ) : 0 < detGram Q₀ σ := by
  unfold detGram
  refine norm_pos_iff.mpr ?_
  rw [map_ne_zero σ]
  refine div_ne_zero ?_ (pow_ne_zero _ two_ne_zero)
  exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ

/-- **The norm factor** $|N_{F/\mathbb Q}(2m)| = \prod_{\sigma : F \to \mathbb C}|\sigma(2m)|$, the archimedean half of the
product formula: $\prod_\mathfrak p|2m|_\mathfrak p^{-1} = |N(2m)|$. It is the total fibration constant of the finite
primes (`LocalOrbitalIdentity`). -/
def normTwoM (m : 𝓞 F) : ℝ := ∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F (2 * m))‖

/-- **The archimedean identity over $F$**: $\prod_\sigma\mathrm{vol}(SO_{n+1}(\mathbb R_\sigma))\cdot|N(2m)|^n =
\prod_\sigma\mathrm{vol}(SO_n(\mathbb R_\sigma))\cdot\prod_\sigma\beta_\sigma(m)$ (`archVolSO_succ` at each $\sigma$). -/
theorem archProd_splitForm (m : 𝓞 F) (hm : m ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate) :
    (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (n + 1) (detGram (splitForm m Q₀') σ)) * normTwoM m ^ n =
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀' σ)) *
        ∏ σ : F →ₐ[ℚ] ℂ, archRepDensity (n + 1) ‖σ (algebraMap (𝓞 F) F m)‖ (detGram (splitForm m Q₀') σ) := by
  unfold normTwoM
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun σ _ => ?_
  have ha : 0 < ‖σ (algebraMap (𝓞 F) F m)‖ := by
    refine norm_pos_iff.mpr ?_
    rw [map_ne_zero σ]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hm
  rw [detGram_splitForm, show ‖σ (algebraMap (𝓞 F) F (2 * m))‖ = 2 * ‖σ (algebraMap (𝓞 F) F m)‖ by
    rw [map_mul, map_mul, norm_mul, map_ofNat, map_ofNat]; norm_num]
  exact archVolSO_succ n ha (detGram_pos hQ' σ)

/-! ### The inputs -/

section Inputs

variable {N : ℕ}

local notation "QFof" Q₀ => QuadForm.map (algebraMap (𝓞 F) F) Q₀

/-- **The Siegel product for the number $m$** over $F$ (the local side of Siegel's formula):
$$S(L, m) = |d_F|^{-(N-1)/2}\prod_{\sigma : F 	o \mathbb C}eta_\sigma(m)\prod_\mathfrak peta_\mathfrak p(L, m),$$
$eta_\sigma$ = `archRepDensity N |σ(m)| (detGram Q₀ σ)`, $eta_\mathfrak p$ = `NF.localDensity` ($\mathrm{vol}(\mathfrak o_\mathfrak p) = 1$).
The factor $|d_F|^{-(N-1)/2}$ comes from the self-dual measure on $\mathbb A_F$ ($\mathrm{vol}(\mathfrak o_\mathfrak p) = |\mathfrak d_\mathfrak p|^{1/2}$)
on $V$ (dimension $N$) and on $F$ (dimension $1$) (Weil 1965, *Sur la formule de Siegel* [unverified]; Siegel 1937
for $F \ne \mathbb Q$ [unverified]). *Update:* the repository's `Siegel.aENF` (Hanke's (5.3) transcribed to $F$) has no
discriminant factor; Siegel's formula over $F \ne \mathbb Q$ needs it. For $F$ totally real,
$S = |d_F|^{-(N-1)/2}\,$`aENF` (real places ↔ embeddings; proved as `HilbertModular.siegelProduct_eq_discr_mul_aENF`).

*Warning: meaningful only for $N \ge 4$.* For $N = 3$ the factors $\beta_\mathfrak p = 1 + \chi_m(\mathfrak p)/N\mathfrak p$ are
not unconditionally multipliable, so `tprod` returns its junk value $1$ whenever no $\beta_\mathfrak p$ vanishes
(`siegelProduct_of_not_multipliable`) and the finite factors are dropped. In rank $3$ use `siegelProduct3`
(`Tamagawa/SiegelRank3.lean`, the regularized product). -/
@[kb "siegel1935" "Hauptsatz (local side, over F) [unverified]"]
def siegelProduct (Q₀ : QuadForm (𝓞 F) N) (m : 𝓞 F) : ℝ :=
  |(discr F : ℝ)| ^ (-((N : ℝ) - 1) / 2) *
    (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity N ‖σ (algebraMap (𝓞 F) F m)‖ (detGram Q₀ σ)) *
    ∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.localDensity v Q₀ m

/-- **Input: Siegel's formula for the number $m$** (degree $1$) for the genus of $L = \mathcal O_F^N$ (Siegel 1935,
Hauptsatz [unverified]; over $F$: Siegel 1937 [unverified]; Weil 1965):
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(m)}{|O(M)|} = \mathrm{Mass}(L)\cdot S(L, m).$$

Field:
- `repMass_eq`: `repMass QF L m = mass QF L * siegelProduct Q₀ m`.

*Independence (hypothesis hygiene):* this is the statement that the **genus average** $r_{\mathrm{gen}}(L, m) =
\mathrm{repMass}/\mathrm{Mass}$ equals the product of the local densities **of the number $m$**. It is homogeneous in the
weights $1/|O(M)|$ (scaling all of them leaves it unchanged), so it carries no information about the value of
$\mathrm{Mass}(L)$; the mass formula is not a consequence of it alone. Over $\mathbb Q$ for $N = 4$ it is
`Siegel.siegelFormula_quaternary`, for forms over $\mathbb Z$; bridged to lattices in $\mathbb Q^4$ by `RatBridge.siegelFormulaAt_rat_four`); over $F$ it is the Siegel–Weil formula. Valid for $N \ge 4$ with `tprod` (absolute convergence; $N = 3$ needs a
regularized product), and $N \ge 2$ in Siegel's theorem with his factor $\varepsilon = 1/2$ at $N = 2$.

*Warning: use only for $N \ge 4$.* **False at $N = 1$:** for $Q_0 = \langle a\rangle$ over $\mathbb Z$ (more generally every
represented $m = cs^2$) the Euler factors are $\beta_p(m) = 2p^{v_p(2as)} \ge 2$, so the product is not multipliable, `tprod` is the junk
value $1$, and the literal statement is refuted (`SiegelRankOne.not_siegelFormulaAt_rankOne_int`). The correct rank-one statement carries
Siegel's $\varepsilon = \tfrac12$ at every place: `SiegelRankOne.siegelFormulaOne_self` (at $m = c$), `siegelFormulaOne_sq`
(every $m = cs^2$ over $\mathcal O_F$) and `siegelFormulaOne_int` (every $m \ge 1$ over $\mathbb Z$), all with `siegelProductOne`.
**False at $N = 3$** in general (argued below; use `SiegelFormulaAt3`). For $N = 3$ (with $m$ locally represented everywhere) `siegelProduct` is the junk
value $|d_F|^{-1}\prod_\sigma\beta_\sigma(m)$, so this structure is then a false statement in general (see `SiegelRank3`). The rank-3 statement is `SiegelFormulaAt3` (`Tamagawa/SiegelRank3.lean`). Theorems
taking `SiegelFormulaAt` with complement rank $2$ (total rank $3$), e.g. `massFormula_succ` without a rank guard, are vacuous
there. -/
@[kb "siegel1935" "Hauptsatz [unverified]"]
structure SiegelFormulaAt (Q₀ : QuadForm (𝓞 F) N) (m : 𝓞 F) : Prop where
  repMass_eq : repMass (QFof Q₀) (stdLat F N) (algebraMap (𝓞 F) F m) =
    mass (QFof Q₀) (stdLat F N) * siegelProduct Q₀ m

/-- **Input: Weil's local orbital identity** for $L = \mathcal O_F e_0 \perp \mathcal O_F^n$, $Q(e_0) = m$
(Weil 1982, §3.4 [unverified]; Kitaoka 1993, §6.8 [unverified]):
$$\Big(\sum_{t \in O(Q')(\mathbb A_f)\backslash Y} w(t)\Big)\cdot\prod_\mathfrak p\alpha_\mathfrak p(L, L)
  = |N_{F/\mathbb Q}(2m)|^n\cdot\prod_\mathfrak p\alpha_\mathfrak p(L', L')\cdot\prod_\mathfrak p\beta_\mathfrak p(L, m),$$
$Y = \{M \in \mathrm{gen}(L) : e_0 \in M\}$, $w(t) = \mu(K_0')/\mu(K_t)$ (`typeWeight`), $\alpha_\mathfrak p$ = `NF.siegelDensity`
$= \mathrm{vol}(SO(L_\mathfrak p))$, $\beta_\mathfrak p$ = `NF.localDensity`.

Field:
- `typeSum_eq`: the displayed identity, with the products as `tprod`s over the finite primes.

*Meaning.* Prime by prime it is Weil's fibration $O(V_\mathfrak p) \to X_m(F_\mathfrak p) = \{v : Q(v) = m\}$, $g \mapsto ge_0$,
with fibre $O(e_0^\perp)$ and gauge forms $\omega_G = \omega_X\wedge\omega_H$ up to the constant $|2m|_\mathfrak p^{-n}$ (the
Jacobian of $c_{0j} = B(e_0, y_j) = 2m\,y_{j,0}$ in coefficient coordinates): summing over the $O(L_\mathfrak p)$-orbits on
$\{v \in L_\mathfrak p : Q(v) = m\}$,
$$\beta_\mathfrak p(L, m) = |2m|_\mathfrak p^{\,n}\,\frac{\alpha_\mathfrak p(L)}{\alpha_\mathfrak p(L')}\sum_{t_\mathfrak p} w_\mathfrak p(t_\mathfrak p),$$
and the product formula turns $\prod_\mathfrak p|2m|_\mathfrak p^{-n}$ into $|N(2m)|^n$. At $\mathfrak p \nmid 2m\det H$ there is one local
type, $w_\mathfrak p = 1$, and it reads $\beta_\mathfrak p(L, m)\,\alpha_\mathfrak p(L') = \alpha_\mathfrak p(L)$ (the classical good-prime
values: $1 + \chi(\mathfrak p)N\mathfrak p^{-n/2}$, resp. $1 - \chi N\mathfrak p^{-(n+1)/2}$, times `volSO_good_odd/even`).

*Independence (hypothesis hygiene):* only local densities, index ratios of compact open subgroups of
$O(Q')(\mathbb A_f)$ and $|N(2m)|$ occur; no class, class number, automorphism group or mass. Its truth is decided
prime by prime. It is *not* proved here (the local orbit decomposition at the bad primes and the factorization of
the type sum over the primes are the open part of the Siegel formula for numbers); the archimedean half is proved (`archProd_splitForm`). -/
@[kb "weil1982" "§3.4 (local fibration) [unverified]"]
structure LocalOrbitalIdentity {n : ℕ} (Q₀' : QuadForm (𝓞 F) n) (m : 𝓞 F) : Prop where
  typeSum_eq :
    (∑ᶠ t : orbitRel.Quotient (OAf (QFof Q₀'))
        (CompSet (algebraMap (𝓞 F) F m) (QFof Q₀') (stdLat F (n + 1))),
      typeWeight (algebraMap (𝓞 F) F m) (QFof Q₀') (stdLat F (n + 1)) t) *
      ∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.siegelDensity v (splitForm m Q₀') (splitForm m Q₀') =
    normTwoM m ^ n * (∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.siegelDensity v Q₀' Q₀') *
      ∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.localDensity v (splitForm m Q₀') m

/-- **The mass formula** for the genus of $\mathcal O_F^N$ with the form $Q_0$, in the explicit form
$\mathrm{Mass}(\mathcal O_F^N) = \mu_{\mathrm{Tam}}(K_{SO})^{-1}$ (`massFormula`'s conclusion). -/
def MassFormulaHolds (Q₀ : QuadForm (𝓞 F) N) : Prop :=
  mass (QFof Q₀) (stdLat F N) = (tamagawaK Q₀)⁻¹

end Inputs

/-! ### The induction step -/

section Step

variable {n : ℕ}

theorem map_splitForm_alg (m : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) :
    (splitForm m Q₀').map (algebraMap (𝓞 F) F) =
      splitForm (algebraMap (𝓞 F) F m) (Q₀'.map (algebraMap (𝓞 F) F)) :=
  map_splitForm _ _ _

theorem isTotallyPosDef_of_splitForm {m : F} {Q' : QuadForm F n} (h : IsTotallyPosDef (splitForm m Q')) :
    IsTotallyPosDef Q' := by
  intro x hx
  have h1 : (Fin.cons 0 x : Fin (n + 1) → F) ≠ 0 := by
    intro h0; apply hx; funext i; simpa using congrFun h0 i.succ
  have := h _ h1
  rw [QuadForm.eval, evalIn_splitForm] at this
  simpa using this

theorem isIntegral_of_splitForm {m : F} {Q' : QuadForm F n}
    (h : IsIntegral (splitForm m Q') (stdLat F (n + 1)).1) : IsIntegral Q' (stdLat F n).1 := by
  intro x hx
  have h1 : (Fin.cons 0 x : Fin (n + 1) → F) ∈ (stdLat F (n + 1)).1 := by
    intro i
    refine Fin.cases ⟨0, by simp⟩ (fun i => ?_) i
    simpa using hx i
  have := h _ h1
  rw [evalIn_splitForm] at this
  simpa using this

theorem e₀_mem_intVec : (e₀ : Fin (n + 1) → F) ∈ (stdLat F (n + 1)).1 := by
  intro i
  refine Fin.cases ⟨1, by simp⟩ (fun i => ⟨0, by simp⟩) i

/-- **The type sum is positive**: every weight is a ratio of positive indices, and the type of $\mathcal O_F^{n+1}$ exists. -/
theorem typeSum_pos {m : F} {Q' : QuadForm F n} (hpd : IsTotallyPosDef (splitForm m Q'))
    (hLi : IsIntegral (splitForm m Q') (stdLat F (n + 1)).1) (hm : m ≠ 0) :
    0 < ∑ᶠ t : orbitRel.Quotient (OAf Q') (CompSet m Q' (stdLat F (n + 1))),
      typeWeight m Q' (stdLat F (n + 1)) t := by
  classical
  have := finite_types m Q' (stdLat F (n + 1)) hpd hLi hm
  have : Fintype (orbitRel.Quotient (OAf Q') (CompSet m Q' (stdLat F (n + 1)))) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  have hne : (Finset.univ : Finset (orbitRel.Quotient (OAf Q') (CompSet m Q' (stdLat F (n + 1))))).Nonempty :=
    ⟨Quotient.mk'' ⟨stdLat F (n + 1), SameGenus.refl _ _, e₀_mem_intVec⟩, Finset.mem_univ _⟩
  refine Finset.sum_pos (fun t _ => ?_) hne
  have hK := commensurable_stabilizer_compSet m Q' (stdLat F (n + 1)) t.out
  have h1 : (0 : ℝ) < (stabilizer (OAf Q') t.out).relIndex (locStab Q' (stdLat F n)) := by
    exact_mod_cast Nat.pos_of_ne_zero hK.1.relIndex_ne_zero
  have h2 : (0 : ℝ) < (locStab Q' (stdLat F n)).relIndex (stabilizer (OAf Q') t.out) := by
    exact_mod_cast Nat.pos_of_ne_zero hK.2.relIndex_ne_zero
  exact div_pos h1 h2

theorem nondegenerate_of_map {N : ℕ} {Q₀ : QuadForm (𝓞 F) N}
    (h : (Q₀.map (algebraMap (𝓞 F) F)).Nondegenerate) : Q₀.Nondegenerate := by
  rw [QuadForm.Nondegenerate] at h ⊢
  intro h0
  apply h
  have : (Q₀.map (algebraMap (𝓞 F) F)).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

/-- **Weil's induction step for the mass formula** (Weil 1982, §§3.4–3.5 [unverified locator]; Siegel 1935, 1936
[unverified]; Kneser [unverified]; Kitaoka 1993, §6.8 [unverified]). Let $Q_0 = \langle m\rangle \perp Q_0'$ over
$\mathcal O_F$ ($n+1$ variables, $m \ne 0$), totally positive definite, with $\mathcal O_F^{n+1}$ integral. If
* Siegel's formula holds for the number $m$ and the genus of $\mathcal O_F^{n+1}$ (`SiegelFormulaAt`),
* Weil's local orbital identity holds (`LocalOrbitalIdentity`), and
* the mass formula holds in rank $n$ for $Q_0'$ (the induction hypothesis),

then the mass formula holds in rank $n+1$ for $Q_0$:
$$\mathrm{Mass}(\mathcal O_F^{n+1}, Q_0) = \mu_{\mathrm{Tam}}(K_{SO}(Q_0))^{-1}
  = \frac{|d_F|^{(n+1)n/4}}{\prod_\sigma\mathrm{vol}(SO_{n+1}(\mathbb R_\sigma))\prod_\mathfrak p\alpha_\mathfrak p(Q_0)}.$$
*Proof:* the global reduction (`repMass_eq_mass_mul`) and Siegel give
$\mathrm{Mass}(L)\,S(L, m) = \mathrm{Mass}(L')\,W$; the induction hypothesis, the local identity and the archimedean
identity (`archProd_splitForm`) turn $\mathrm{Mass}(L')\,W$ into $S(L,m)/\mu_{\mathrm{Tam}}(K_{SO}(Q_0))$, and
$S(L, m) \ne 0$ because $W > 0$. -/
@[kb "weil1982" "§4.5, pp. 100-109 (induction on m); Thm. 4.5.1, p. 109"]
theorem massFormula_succ (m : 𝓞 F) (hm : m ≠ 0) (Q₀' : QuadForm (𝓞 F) n)
    (hpd : IsTotallyPosDef ((splitForm m Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral ((splitForm m Q₀').map (algebraMap (𝓞 F) F)) (stdLat F (n + 1)).1)
    (hS : SiegelFormulaAt (splitForm m Q₀') m) (hloc : LocalOrbitalIdentity Q₀' m)
    (hIH : MassFormulaHolds Q₀') : MassFormulaHolds (splitForm m Q₀') := by
  unfold MassFormulaHolds at hIH ⊢
  set QF' := Q₀'.map (algebraMap (𝓞 F) F)
  set mF := algebraMap (𝓞 F) F m
  have hsplit := map_splitForm_alg m Q₀'
  rw [hsplit] at hpd hLi ⊢
  have hS' := hS.repMass_eq
  rw [hsplit] at hS'
  have hmF : mF ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hm
  have hpd' := isTotallyPosDef_of_splitForm hpd
  have hLi' := isIntegral_of_splitForm hLi
  have hQ' : Q₀'.Nondegenerate := nondegenerate_of_map hpd'.nondegenerate
  -- the global reduction
  have hR := repMass_eq_mass_mul mF QF' (stdLat F (n + 1)) hpd hLi hmF hpd' hLi'
  have hW := typeSum_pos hpd hLi hmF
  have hloc' := hloc.typeSum_eq
  set W := ∑ᶠ t : orbitRel.Quotient (OAf QF') (CompSet mF QF' (stdLat F (n + 1))),
    typeWeight mF QF' (stdLat F (n + 1)) t
  -- names for the factors
  set A := ∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.siegelDensity v (splitForm m Q₀') (splitForm m Q₀')
  set A' := ∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.siegelDensity v Q₀' Q₀'
  set B := ∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.localDensity v (splitForm m Q₀') m
  set Pr := ∏ σ : F →ₐ[ℚ] ℂ, archVolSO (n + 1) (detGram (splitForm m Q₀') σ)
  set Pr' := ∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀' σ)
  set ρ := ∏ σ : F →ₐ[ℚ] ℂ, archRepDensity (n + 1) ‖σ mF‖ (detGram (splitForm m Q₀') σ)
  set Nm := normTwoM m
  set δ := |(discr F : ℝ)|
  have hδ : 0 < δ := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
  have harch : Pr * Nm ^ n = Pr' * ρ := archProd_splitForm m hm Q₀' hQ'
  have hT : tamagawaK (splitForm m Q₀') = δ ^ (-(((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) - 1) / 4)) * Pr * A := rfl
  have hT' : tamagawaK Q₀' = δ ^ (-((n : ℝ) * (n - 1) / 4)) * Pr' * A' := rfl
  have hSP : siegelProduct (splitForm m Q₀') m = δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) * ρ * B := rfl
  have hδe : δ ^ (-(((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) - 1) / 4)) =
      δ ^ (-((n : ℝ) * (n - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) := by
    rw [← Real.rpow_add hδ]; push_cast; ring_nf
  -- positivity
  have hmass' := mass_pos hpd' (stdLat F n) hLi'
  rw [hIH] at hmass'
  have hT'pos : 0 < tamagawaK Q₀' := inv_pos.mp hmass'
  have hT'ne : tamagawaK Q₀' ≠ 0 := hT'pos.ne'
  have hRpos : 0 < repMass (splitForm mF QF') (stdLat F (n + 1)) mF := by
    rw [hR, hIH]; exact mul_pos hmass' hW
  have hSne : siegelProduct (splitForm m Q₀') m ≠ 0 := by
    intro h0; rw [hS', h0, mul_zero] at hRpos; exact lt_irrefl _ hRpos
  have hSne' := hSne
  rw [hSP] at hSne'
  have hB : B ≠ 0 := right_ne_zero_of_mul hSne'
  have hρ : ρ ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hSne')
  have hNm : Nm ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun σ _ => norm_ne_zero_iff.mpr ?_
    rw [map_ne_zero σ]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (mul_ne_zero two_ne_zero hm)
  have hT'ne' := hT'ne
  rw [hT'] at hT'ne'
  have hA' : A' ≠ 0 := right_ne_zero_of_mul hT'ne'
  have hPr' : Pr' ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hT'ne')
  have hA : A ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hloc'
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hNm) hA') hB hloc'.symm
  have hPr : Pr ≠ 0 := by
    intro h0; rw [h0, zero_mul] at harch
    exact mul_ne_zero hPr' hρ harch.symm
  -- assemble
  set D' := δ ^ (-((n : ℝ) * (n - 1) / 4))
  set Ds := δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2)
  have hD' : D' ≠ 0 := (Real.rpow_pos_of_pos hδ _).ne'
  have hDs : Ds ≠ 0 := (Real.rpow_pos_of_pos hδ _).ne'
  have e := hS'.symm.trans hR
  rw [hIH] at e
  have key : W * (D' * Ds * Pr * A) = (D' * Pr' * A') * (Ds * ρ * B) := by
    linear_combination (D' * Ds * Pr) * hloc' + (D' * Ds * A' * B) * harch
  rw [hT, hδe]
  rw [hT', hSP] at e
  have hTS : D' * Pr' * A' * (Ds * ρ * B) ≠ 0 := by
    rw [← hSP, ← hT']; exact mul_ne_zero hT'ne hSne
  have hmass : mass (splitForm mF QF') (stdLat F (n + 1)) = W / (D' * Pr' * A' * (Ds * ρ * B)) := by
    rw [eq_div_iff hTS]
    rw [mul_comm (D' * Pr' * A'), ← mul_assoc, e]
    field_simp
  rw [hmass, div_eq_iff hTS, ← key]
  field_simp

/-! ### Consequence: $\tau(SO) = 2$ -/

/-- **The mass formula gives $\tau(SO) = 2$** (and conversely, `massFormula`): $\tau(SO) =
\mu_{\mathrm{Tam}}(K_{SO})\cdot\mathrm{mass}_{SO} = \mu_{\mathrm{Tam}}(K_{SO})\cdot2\,\mathrm{Mass}(L) = 2$
(`mass_SO_eq_two_mul_mass`). -/
theorem tamagawaNumberTwo_of_massFormula {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) (hn : 0 < N)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F N).1) (h : MassFormulaHolds Q₀) :
    TamagawaNumberTwo Q₀ := by
  unfold TamagawaNumberTwo tauSO
  rw [mass_SO_eq_two_mul_mass Q₀ hQ hn hpd hLi]
  unfold MassFormulaHolds at h
  have hpos := mass_pos hpd (stdLat F N) hLi
  rw [h] at hpos ⊢
  have hT : tamagawaK Q₀ ≠ 0 := (inv_pos.mp hpos).ne'
  field_simp

theorem massFormulaHolds_iff_tamagawaNumberTwo {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate)
    (hn : 0 < N) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F N).1) :
    MassFormulaHolds Q₀ ↔ TamagawaNumberTwo Q₀ :=
  ⟨tamagawaNumberTwo_of_massFormula Q₀ hQ hn hpd hLi, fun h => massFormula Q₀ hQ hn hpd hLi h⟩

/-- **$\tau(SO) = 2$ as a consequence of the induction** (the goal: `TamagawaNumberTwo` is now derived, not assumed):
under the hypotheses of `massFormula_succ`, $\tau(SO(V)) = 2$ for $V = (F^{n+1}, \langle m\rangle\perp Q_0')$. -/
@[kb "weil1982" "Thm. 4.5.1, p. 109 (τ(SO) = 2 for m ≥ 3)"]
theorem tamagawaNumberTwo_succ (m : 𝓞 F) (hm : m ≠ 0) (Q₀' : QuadForm (𝓞 F) n)
    (hpd : IsTotallyPosDef ((splitForm m Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral ((splitForm m Q₀').map (algebraMap (𝓞 F) F)) (stdLat F (n + 1)).1)
    (hS : SiegelFormulaAt (splitForm m Q₀') m) (hloc : LocalOrbitalIdentity Q₀' m)
    (hIH : MassFormulaHolds Q₀') : TamagawaNumberTwo (splitForm m Q₀') :=
  tamagawaNumberTwo_of_massFormula _ (nondegenerate_of_map hpd.nondegenerate) (Nat.succ_pos n) hpd hLi
    (massFormula_succ m hm Q₀' hpd hLi hS hloc hIH)

end Step


end NF

end QuadFormsKB.Tamagawa
