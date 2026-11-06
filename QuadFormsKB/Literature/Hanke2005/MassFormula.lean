/-
# Hanke 2005, §3 and §5: Shimura's local factors and the exact mass formula (Theorem 5.1)

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Setting.** $F$ a number field of degree $d$ with discriminant $D_F$ and $r_2$ complex places; $Q_0$ a nondegenerate
quadratic form over $\mathcal O_F$ in $n\ge3$ variables, any signature; $(V,\varphi) = (F^n,Q_0)$, $\Lambda = \mathcal O_F^n$,
$\psi = \tfrac12H_{Q_0}$ (Gram matrix), $H = H_{Q_0}$ (Hessian, $= 2\psi$).

**Local invariants at a finite place $\mathfrak p$** (Hanke §2–§3, p. 6 and p. 8):
* `anisoDim` $t_\mathfrak p = \dim\theta_\mathfrak p = n - 2r_\mathfrak p$, $r_\mathfrak p$ the Witt index of $V_\mathfrak p$
  (`QuadraticForm.wittIndex`): the normal form (2.9) is $\mathbb H^{r}\perp\theta_\mathfrak p$ with $\theta_\mathfrak p$ anisotropic;
* `dualIndexAt` $[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p] = |\det(2\psi)|_\mathfrak p^{-1}$ ((3.4), [Shi, (3.1.9)]), where
  $\widetilde\Lambda_\mathfrak p = \{x : 2\varphi(x,\Lambda_\mathfrak p)\subseteq\mathcal O_\mathfrak p\}$; $\mathfrak p\mid\mathfrak e$ iff
  $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$, i.e. iff this index is $\ne1$;
* $K = F(\sqrt\delta)$, $\delta = (-1)^{n/2}\det\psi$ (`discK`, used for even $n$); `IsUnramSqrt` ($\mathfrak p$ unramified in
  $K$, split included: $\delta c^2 = 1 + 4y$ with $y$ integral), `chiK` (the quadratic character of $K/F$:
  $1$ split, $-1$ inert, $0$ ramified; $\chi$ is trivial when $K = F$, so that $L_F(s,\chi) = \zeta_F(s)$ then);
* `xiShimura` (Hanke's $\xi$, p. 8) and `lambdaHanke` (Hanke's $\lambda_v$, Theorem 5.1, p. 17), $m = \lfloor n/2\rfloor$.

**Named inputs** (cited, not proved):
* `ShimuraMaximalDensity F` — **(3.3)**, Hanke's translation of [Shi, Thm 8.6(3), Prop. 3.9, (3.1.9)]: for a maximal
  lattice and Shimura's hypothesis, $\beta_\mathfrak p(\varphi_\mathfrak p) = |\det(2\cdot1_n)|_\mathfrak p^{(n+1)/2}q^{\kappa n}
  [\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\,\xi$ (here $q^{\kappa n} = |2|_\mathfrak p^{-n}$, $2\mathcal O_\mathfrak p = \mathfrak p^\kappa$).
  *Reading:* the thesis text of (3.3) is not fully legible in the available copy; the form used was checked against the
  local densities of $x_0^2+x_1^2+x_2^2$ and $x_0^2+x_0x_2+x_2^2+x_1^2$ at $2$, the Hurwitz order at $2$ and
  $x_0^2+3x_1^2+3x_2^2$ at $3$ (brute-force counts);
* `ShimuraMaximalTypes F` (**proved**: `shimuraMaximalTypes`, `LocalTypes.lean`) — the local types used implicitly in
  the proof of Theorem 5.1 ([Shi, §3]; O'Meara 1963, §§92–93): at a place where $\widetilde\Lambda_\mathfrak p = \Lambda_\mathfrak p$ a maximal lattice has
  $t_\mathfrak p\le2$ and ($n$ even) $\mathfrak p$ is unramified in $K$; for $n$ even, $t_\mathfrak p = 2$ iff $\delta$ is not a
  square in $F_\mathfrak p$.

**The mass.** Hanke's mass (5.4)–(5.5) is $\sum_{a\in\mathrm{Cl}}\nu(\Gamma_a)$ with $\nu(\Gamma_a) = [\Gamma_a:1]^{-1}$ if $G_a$ is
compact and $[\Gamma_a\cap\{\pm1\}:1]^{-1}\mathrm{vol}(\Gamma_a\backslash Z)$ otherwise, $Z = \prod_{v\in a}Z_v$ the symmetric space of
§4. By (5.6) (Lemma A7 for $F : G_a\to Z$, $\alpha\mapsto\alpha p$, with Lemma A1) this is
$\nu(\Gamma_a) = \tau_a(\Gamma_a\backslash G_a)/\mathrm{vol}_C(C_a)$, and `hankeMass` is the mass in this form, with the volumes
$\mathrm{vol}_C(C_v)$ of §4 (`volCReal`, `volCComplex`, for the normal form (2.9); for the matrix $\psi$ they are multiplied by
$|\det\psi|_v^{-(n+1)/2}$, Lemma 2.2 at the archimedean places). The symmetric spaces $Z_v$, their forms $\omega_Z$ and (5.6)
itself are **not formalized** (the formulas of §4.2 are not legible in the available copy); in the totally definite case
$\nu(\Gamma_a) = 1/|\Gamma_a|$ is proved here (`hankeMass_definite`).

**Theorem 5.1** (`theorem51`): the exact mass, conditional on the two named inputs. *Update (hypothesis):* the theorem
as printed omits Shimura's hypothesis (stated in the abstract and in §3) that for odd $n$ the determinant of $\varphi$ is
locally a unit times a square; it is needed: for the maximal lattice $x_0^2+x_0x_2+x_2^2+x_1^2$ over $\mathbb Z$ (Hanke's
mass $1/12$) the formula gives $1/36$. It is the hypothesis `ShimuraDetHyp`.
-/
import QuadFormsKB.Literature.Hanke2005.TheoremTwoOne
import QuadFormsKB.Literature.Hanke2005.Archimedean
import QuadFormsKB.Witt.Decomposition
import QuadFormsKB.Literature.OMeara.Sec82
import QuadFormsKB.Analysis.NFLFunctions
import QuadFormsKB.Equiv.Mathlib

open MeasureTheory Measure NumberField IsDedekindDomain Filter Real
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### Maximal lattices -/

/-- **$\Lambda = \mathcal O_F^n$ is a maximal lattice** for $\varphi = Q_0\otimes F$ (Hanke thesis, §1, p. 2 and §5, p. 16:
$\varphi(\Lambda)\subseteq\mathcal O_k$ and $\Lambda$ is not properly contained in a lattice $\Lambda'$ with
$\varphi(\Lambda')\subseteq\mathcal O_k$): O'Meara's $\mathcal O_F$-maximal lattice (`OMeara.IsMaximal`, §82H, p. 234). -/
@[kb "hanke2005crelle" "§1, p. 2; §5, p. 16 (maximal lattice)"]
def StdIsMaximal (Q₀ : QuadForm (𝓞 F) n) : Prop :=
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  OMeara.IsMaximal (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F))) (1 : Submodule (𝓞 F) F)
    (stdLat F n).1

/-! ### Local invariants at a finite place -/

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $q = N\mathfrak p = \#(\mathcal O/\mathfrak p)$, as a real number. -/
abbrev normQ : ℝ := (NFEuler.normP v : ℝ)

/-- **$t_\mathfrak p = \dim\theta_\mathfrak p$** (Hanke thesis, (2.9), p. 6): the dimension of the anisotropic kernel of
$(V_\mathfrak p,\varphi_\mathfrak p)$, $n - 2\cdot$(Witt index). -/
@[kb "hanke2005crelle" "(2.9), p. 6; §3, p. 8 (t = dim θ_p)"]
def anisoDim (Q₀ : QuadForm (𝓞 F) n) : ℕ :=
  n - 2 * QuadraticForm.wittIndex (QuadForm.toQuadraticForm (Tamagawa.Measure.LerayPadic.QV v Q₀))

/-- **$[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p] = |\det(2\varphi_\mathfrak p)|_\mathfrak p^{-1}$** (Hanke thesis, (3.4), p. 8,
quoting [Shi, (3.1.9)]), for $\Lambda_\mathfrak p = \mathcal O_\mathfrak p^n$ with matrix $\varphi_\mathfrak p = \psi$, $2\psi = H$. -/
@[kb "hanke2005crelle" "(3.4), p. 8 ([Λ̃_p : Λ_p] = |det(2φ_p)|^{-1}, quoting Shimura 1999, (3.1.9))"]
def dualIndexAt (Q₀ : QuadForm (𝓞 F) n) : ℝ :=
  ‖(((NF.Qp v Q₀).hessian.det : 𝔬) : Fv)‖⁻¹

/-- **$\delta = (-1)^{n/2}\det\psi$**, so that $K = F(\sqrt\delta)$ (Hanke thesis, p. 8 and Theorem 5.1, p. 17; used for even
$n$). -/
@[kb "hanke2005crelle" "§3, p. 8; Theorem 5.1, p. 17 (K = k(√((-1)^{n/2} det φ)))"]
def discK (Q₀ : QuadForm (𝓞 F) n) : F :=
  (-1) ^ (n / 2) * ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det / 2 ^ n)

/-- **$F_\mathfrak p(\sqrt x)/F_\mathfrak p$ is unramified** (split included): $x c^2 = 1 + 4y$ for some $c\ne0$ and $y$ integral
with $1 + 4y$ a unit of $\mathfrak o_\mathfrak p$ (O'Meara 63:3, 63:4). At a dyadic place $1 + 4y$ is automatically a unit; at a
non-dyadic place the condition says that $x$ is a unit times a square.
*Correction (formalization, 2026-10-30):* the first pass omitted "$1 + 4y$ a unit"; without it every $x\ne0$ satisfied the
condition at a non-dyadic place ($4$ is a unit there), so no odd place was ever ramified in $K$. -/
def IsUnramSqrt (x : Fv) : Prop :=
  ∃ c : Fv, c ≠ 0 ∧ ∃ y : 𝔬, IsUnit (1 + 4 * y) ∧ x * c ^ 2 = 1 + 4 * (y : Fv)

/-- **$\mathfrak p$ is ramified in $K = F(\sqrt\delta)$** (Hanke thesis, p. 8). -/
def IsRamifiedAt (Q₀ : QuadForm (𝓞 F) n) : Prop :=
  ¬ IsUnramSqrt v (algebraMap F Fv (discK Q₀))

open Classical in
/-- **The quadratic character $\chi$ of $K/F$** at $\mathfrak p$ (Hanke thesis, Theorem 5.1, p. 17): $1$ if $\mathfrak p$ splits
(or $K = F$), $-1$ if $\mathfrak p$ is inert, $0$ if $\mathfrak p$ ramifies. -/
@[kb "hanke2005crelle" "Theorem 5.1, p. 17 (χ, the Hecke character of K/k)"]
def chiK (Q₀ : QuadForm (𝓞 F) n) : ℝ :=
  if IsSquare (algebraMap F Fv (discK Q₀)) then 1 else if IsRamifiedAt v Q₀ then 0 else -1

end Local

/-- $\prod_{i=1}^k(1-q^{-2i})$. -/
def ppow (q : ℝ) (k : ℕ) : ℝ := ∏ i ∈ Finset.range k, (1 - q ^ (-(2 * ((i : ℝ) + 1))))

open Classical in
/-- **Hanke's $\xi$** (thesis, p. 8; from [Shi, Thm 8.6(3), Prop. 3.9]), $m = \lfloor n/2\rfloor$:
$t = 0$: $(1-q^{-m})\prod_{i=1}^{m-1}(1-q^{-2i})$; $t = 1$: $\prod_{i=1}^m(1-q^{-2i})$; $t = 2$, $\mathfrak p$ unramified in $K$,
$\widetilde\Lambda_\mathfrak p = \Lambda_\mathfrak p$: $(1+q^{-m})\prod_{i=1}^{m-1}$; $t = 2$, unramified, $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$:
$2(1+q)(1+q^{1-m})^{-1}\prod_{i=1}^{m-1}$; $t = 2$, ramified: $2\prod_{i=1}^{m-1}$; $t = 3$: $2(1+q)\prod_{i=1}^{m-1}$;
$t = 4$: $2(1+q)(1-q^{1-m})^{-1}\prod_{i=1}^{m-1}$ (and $0$ for $t\ge5$, which does not occur, $t_\mathfrak p\le4$). -/
@[kb "hanke2005crelle" "(3.3), p. 8 (ξ)"]
def xiShimura (q : ℝ) (n t : ℕ) (ram selfDual : Prop) : ℝ :=
  let m := n / 2
  match t with
  | 0 => (1 - q ^ (-(m : ℝ))) * ppow q (m - 1)
  | 1 => ppow q m
  | 2 => if ram then 2 * ppow q (m - 1) else if selfDual then (1 + q ^ (-(m : ℝ))) * ppow q (m - 1)
      else 2 * (1 + q) * (1 + q ^ (1 - (m : ℝ)))⁻¹ * ppow q (m - 1)
  | 3 => 2 * (1 + q) * ppow q (m - 1)
  | 4 => 2 * (1 + q) * (1 - q ^ (1 - (m : ℝ)))⁻¹ * ppow q (m - 1)
  | _ => 0

open Classical in
/-- **Hanke's $\lambda_v$** (thesis, Theorem 5.1, p. 17) at a place $v\mid\mathfrak e$, $q = Nv$, $m = \lfloor n/2\rfloor$:
$t_v = 1$: $1$; $t_v = 2$, unramified: $2^{-1}(1+q)^{-1}(1+q^{1-m})(1+q^{-m})$; $t_v = 2$, ramified: $2^{-1}$;
$t_v = 3$: $2^{-1}(1+q)^{-1}(1-q^{-2m})$; $t_v = 4$: $2^{-1}(1+q)^{-1}(1-q^{1-m})(1-q^{-m})$ (and $1$ otherwise). -/
@[kb "hanke2005crelle" "Theorem 5.1, p. 17 (λ_v)"]
def lambdaHanke (q : ℝ) (n t : ℕ) (ram : Prop) : ℝ :=
  let m := n / 2
  match t with
  | 2 => if ram then 2⁻¹ else 2⁻¹ * (1 + q)⁻¹ * (1 + q ^ (1 - (m : ℝ))) * (1 + q ^ (-(m : ℝ)))
  | 3 => 2⁻¹ * (1 + q)⁻¹ * (1 - q ^ (-(2 * (m : ℝ))))
  | 4 => 2⁻¹ * (1 + q)⁻¹ * (1 - q ^ (1 - (m : ℝ))) * (1 - q ^ (-(m : ℝ)))
  | _ => 1

section LocalFactors

variable (v : HeightOneSpectrum (𝓞 F))

/-- Hanke's $\xi$ at $\mathfrak p$ for $Q_0$. -/
def xiAt (Q₀ : QuadForm (𝓞 F) n) : ℝ :=
  xiShimura (normQ v) n (anisoDim v Q₀) (IsRamifiedAt v Q₀) (dualIndexAt v Q₀ = 1)

open Classical in
/-- Hanke's $\lambda_v$ at $\mathfrak p$, set to $1$ when $\mathfrak p\nmid\mathfrak e$ (the product in Theorem 5.1 runs over
$v\mid\mathfrak e$). -/
def lambdaAt (Q₀ : QuadForm (𝓞 F) n) : ℝ :=
  if dualIndexAt v Q₀ = 1 then 1 else lambdaHanke (normQ v) n (anisoDim v Q₀) (IsRamifiedAt v Q₀)

end LocalFactors

/-- **Shimura's hypothesis** (Hanke thesis, abstract and §3, p. 7): if $n$ is odd, then at every finite place the
determinant of $\varphi$ is a unit times a square. -/
@[kb "hanke2005crelle" "abstract, p. 1; §3, p. 7 (Shimura's condition on det φ for odd n)"]
def ShimuraDetHyp (Q₀ : QuadForm (𝓞 F) n) : Prop :=
  Odd n → ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : v.adicCompletion F, c ≠ 0 ∧
    ‖algebraMap F (v.adicCompletion F) ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det / 2 ^ n) * c ^ 2‖ = 1

/-! ### The named inputs -/

/-- **(3.3): Shimura's local factor of a maximal lattice** (Hanke thesis, (3.3), p. 8, from [Shi, Thm 8.6(3), Prop. 3.9,
(3.1.9)]) — a **named input**, not proved. For $n\ge3$, $Q_0$ nondegenerate with $\Lambda = \mathcal O_F^n$ maximal and Shimura's
hypothesis, at every finite place
$$\beta_\mathfrak p(\Lambda_\mathfrak p,\psi) = |\det(2\cdot1_n)|_\mathfrak p^{(n+1)/2}\,q^{\kappa n}\,[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\,\xi,
\qquad q^{\kappa n} = |2|_\mathfrak p^{-n}.$$
(Hanke states it for the basis of the normal form (2.9); $\beta_\mathfrak p(\mathcal O_\mathfrak p^n,\cdot)$ does not depend on the basis
of $\Lambda_\mathfrak p$, `hankeBeta_std_congr_unit`.) Not equivalent to Theorem 5.1: it is a statement about one local density.
Field: `beta_eq`. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (quoting Shimura 1999, Thm 8.6(3), Prop. 3.9, (3.1.9))"]
structure ShimuraMaximalDensity (F : Type) [Field F] [NumberField F] : Prop where
  /-- The local factor (3.3). -/
  beta_eq : ∀ {n : ℕ}, 3 ≤ n → ∀ Q₀ : QuadForm (𝓞 F) n, Q₀.Nondegenerate → StdIsMaximal Q₀ → ShimuraDetHyp Q₀ →
    ∀ v : HeightOneSpectrum (𝓞 F),
      hankeBeta v (std v) (gramOf v (NF.Qp v Q₀)) =
        ‖((2 : v.adicCompletion F) • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))).det‖ ^ (((n : ℝ) + 1) / 2) *
          (‖(2 : v.adicCompletion F)‖ ^ n)⁻¹ * dualIndexAt v Q₀ * xiAt v Q₀

/-- **The local types of maximal lattices** used in the proof of Theorem 5.1 (Hanke thesis, pp. 8 and 17–18, implicitly;
[Shi, §3]; O'Meara 1963, §§92–93) — formerly a named input, now **proved** for every number field
(`shimuraMaximalTypes`, `LocalTypes.lean`; the conditional theorems are kept). Fields: `selfDual` (where
$\widetilde\Lambda_\mathfrak p = \Lambda_\mathfrak p$, a maximal lattice has $t_\mathfrak p\le2$ and, for even $n$, $\mathfrak p$ is
unramified in $K$), `even_two_iff` (for even $n$, $t_\mathfrak p = 2$ iff $\delta$ is not a square in $F_\mathfrak p$). -/
@[kb "hanke2005crelle" "§3, p. 8; proof of Theorem 5.1, pp. 17–18 (local types; Shimura 1999, §3)"]
structure ShimuraMaximalTypes (F : Type) [Field F] [NumberField F] : Prop where
  /-- Self-dual places of a maximal lattice. -/
  selfDual : ∀ {n : ℕ}, 3 ≤ n → ∀ Q₀ : QuadForm (𝓞 F) n, Q₀.Nondegenerate → StdIsMaximal Q₀ →
    ∀ v : HeightOneSpectrum (𝓞 F), dualIndexAt v Q₀ = 1 →
      anisoDim v Q₀ ≤ 2 ∧ (Even n → ¬ IsRamifiedAt v Q₀)
  /-- The anisotropic kernel has dimension $2$ iff the discriminant is not a square ($n$ even). -/
  even_two_iff : ∀ {n : ℕ}, 3 ≤ n → Even n → ∀ Q₀ : QuadForm (𝓞 F) n, Q₀.Nondegenerate →
    ∀ v : HeightOneSpectrum (𝓞 F),
      (anisoDim v Q₀ = 2 ↔ ¬ IsSquare (algebraMap F (v.adicCompletion F) (discK Q₀)))

/-! ### The mass -/

open Classical in
/-- $r_v$ at an infinite place (Hanke thesis, (2.9), p. 6; Theorem 5.1, p. 17): the Witt index of $\varphi_v$ at a real place
($\varphi_v\cong\mathrm{diag}[1_q,-1_r]$ or its negative, $q\ge r$, $r = \min$ of the signature), and $0$ at a complex
place. -/
@[kb "hanke2005crelle" "(2.9), p. 6; Theorem 5.1, p. 17 (r_v)"]
def rAt (Q₀ : QuadForm (𝓞 F) n) (w : InfinitePlace F) : ℕ :=
  if h : w.IsReal then
    QuadraticForm.wittIndex (QuadForm.toQuadraticForm
      (Q₀.map ((InfinitePlace.embedding_of_isReal h).comp (algebraMap (𝓞 F) F))))
  else 0

open Classical in
/-- $\mathrm{vol}_C(C_v)$ for the matrix $\psi$: $|\det\psi|_v^{-(n+1)/2}$ times the volume of §4 for the normal form (2.9)
(`volCReal (n - r) r` at a real place, `volCComplex n` at a complex place); $|x|_v = |x|^{m_v}$ normalized. -/
def volCAt (Q₀ : QuadForm (𝓞 F) n) (w : InfinitePlace F) : ℝ :=
  (w ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det / 2 ^ n) ^ w.mult) ^ (-((n : ℝ) + 1) / 2) *
    (if w.IsReal then volCReal (n - rAt Q₀ w) (rAt Q₀ w) else volCComplex n)

/-- **Hanke's mass** (5.4)–(5.5) in the form (5.6), p. 17: $\mathrm{Mass}(\Lambda,\varphi) = \sum_{a\in\mathrm{Cl}}
\tau_a(\Gamma_a\backslash G_a)/\mathrm{vol}_C(C_a)$, $\mathrm{vol}_C(C_a) = \prod_{v\in a}\mathrm{vol}_C(C_v)$ (see the module
docstring). -/
@[kb "hanke2005crelle" "(5.4)–(5.6), pp. 16–17 (the mass, in the form (5.6))"]
def hankeMass (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) : ℝ≥0∞ :=
  (∑' i, covolume (unitGroup Q₀ i) (GInfSO Q₀) (muArchHanke Q₀ hQ)) / ENNReal.ofReal (∏ w, volCAt Q₀ w)

open Classical in
/-- **The right side of Theorem 5.1** (Hanke thesis, pp. 16–17), $m = \lfloor n/2\rfloor$, $d = [F:\mathbb Q]$:
$$2|D_F|^{\lfloor(n-1)^2/4\rfloor}\prod_{j=1}^{\lfloor(n-1)/2\rfloor}\Big(|D_F|^{1/2}\Big(\frac{(2j-1)!}{(2\pi)^{2j}}\Big)^d\zeta_F(2j)\Big)
[\widetilde\Lambda:\Lambda]^{\frac{n-1}2}\prod_{v\mid\mathfrak e}\lambda_v\prod_{v\ \mathrm{real}}b^\varphi_v
\prod_{v\ \mathrm{complex}}\Big(2^{-\frac{(n-1)(n-2)}2}\pi^{\frac{n(n+1)}4}\prod_{j=1}^n\Gamma(j/2)^{-1}\Big)
\times\begin{cases}2^{-\frac{n-1}2d}&2\nmid n\\|D_F|^{1/2}\big((\tfrac n2-1)!(2\pi)^{-n/2}\big)^dL_F(\tfrac n2,\chi)&2\mid n\end{cases}$$
with $[\widetilde\Lambda:\Lambda] = \prod_\mathfrak p[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]$. -/
@[kb "hanke2005crelle" "Theorem 5.1, pp. 16–17 (right side)"]
def theorem51RHS (Q₀ : QuadForm (𝓞 F) n) : ℝ :=
  let d := Module.finrank ℚ F
  let D := |(discr F : ℝ)|
  2 * D ^ ((n - 1) ^ 2 / 4) *
    (∏ j ∈ Finset.range ((n - 1) / 2), (D ^ (1 / 2 : ℝ) *
      ((Nat.factorial (2 * (j + 1) - 1) : ℝ) / (2 * π) ^ (2 * (j + 1))) ^ d *
        NFEuler.dedekindZetaR F (2 * ((j : ℝ) + 1)))) *
    (∏' v, dualIndexAt v Q₀) ^ (((n : ℝ) - 1) / 2) * (∏' v, lambdaAt v Q₀) *
    (∏ w : {w : InfinitePlace F // w.IsReal}, bPhi n (rAt Q₀ w)) *
    ((2 : ℝ) ^ (-(((n : ℝ) - 1) * (n - 2)) / 2) * π ^ ((n : ℝ) * (n + 1) / 4) *
      ∏ l ∈ Finset.range n, (Gamma (((l : ℝ) + 1) / 2))⁻¹) ^ InfinitePlace.nrComplexPlaces F *
    (if Odd n then (2 : ℝ) ^ (-(((n : ℝ) - 1) / 2) * d)
      else D ^ (1 / 2 : ℝ) * ((Nat.factorial (n / 2 - 1) : ℝ) * (2 * π) ^ (-((n : ℝ) / 2))) ^ d *
        NFEuler.LFunctionNF (fun v => chiK v Q₀) ((n : ℝ) / 2))

/-! ### Proof of Theorem 5.1: helper lemmas (local algebra, Euler products, archimedean bookkeeping) -/

theorem nondegenerate_map_inj {R K : Type} [CommRing R] [Field K] (f : R →+* K) (hf : Function.Injective f)
    (Q : QuadForm R n) (hQ : Q.Nondegenerate) : (Q.map f).Nondegenerate := by
  rw [QuadForm.Nondegenerate]
  have : (Q.map f).hessian = Q.hessian.map f := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero_iff _ hf).mpr hQ

theorem two_mul_wittIndex_le_of_nondeg {K : Type} [Field K] (Q : QuadForm K n) (hQ : Q.Nondegenerate) :
    2 * QuadraticForm.wittIndex Q.toQuadraticForm ≤ n := by
  have hnd : (QuadraticMap.polarBilin Q.toQuadraticForm).Nondegenerate := by
    have h := QuadForm.nondegenerate_polarBilin_toQuadraticFormIn (K := K) (Q := Q) hQ
    have e : Q.toQuadraticFormIn K = Q.toQuadraticForm := by
      unfold QuadForm.toQuadraticFormIn
      congr 1
    rw [e] at h; exact h
  have hrad := QuadraticForm.radical_eq_bot_of_nondegenerate _ hnd
  obtain ⟨U, _, _, _, Qa, ha, ⟨e⟩⟩ := QuadraticForm.wittIndex_spec _ hrad
  have := e.toLinearEquiv.finrank_eq
  simp [Module.finrank_prod, Module.finrank_pi_fintype] at this
  omega

theorem two_mul_wittIndex_le (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    2 * QuadraticForm.wittIndex (QuadForm.toQuadraticForm (Tamagawa.Measure.LerayPadic.QV v Q₀)) ≤ n := by
  apply two_mul_wittIndex_le_of_nondeg
  have e : Tamagawa.Measure.LerayPadic.QV v Q₀ = (Q₀.map (algebraMap (𝓞 F) F)).map (algebraMap F (v.adicCompletion F)) := by
    apply QuadForm.ext
    ext i j
    simp [QuadForm.map, NF.Qp]
    rfl
  rw [e]
  exact nondegenerate_map_inj _ (algebraMap F (v.adicCompletion F)).injective _ (Tamagawa.nondegenerate_map Q₀ hQ)

theorem two_mul_rAt_le (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (w : InfinitePlace F) :
    2 * rAt Q₀ w ≤ n := by
  unfold rAt
  split_ifs with h
  · apply two_mul_wittIndex_le_of_nondeg
    refine nondegenerate_map_inj _ ?_ _ hQ
    intro a b hab
    exact RingOfIntegers.coe_injective ((InfinitePlace.embedding_of_isReal h).injective hab)
  · omega

/-- Generic local factor. -/
def xiGen (q : ℝ) (n : ℕ) (χ : ℝ) : ℝ :=
  if Odd n then ppow q (n / 2) else (1 - χ * q ^ (-((n / 2 : ℕ) : ℝ))) * ppow q (n / 2 - 1)

theorem ppow_succ_eq {q : ℝ} (hq : 0 ≤ q) (m : ℕ) (hm : 1 ≤ m) :
    ppow q m = (1 - (q ^ (-((m : ℝ))))^2) * ppow q (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  unfold ppow
  rw [Finset.prod_range_succ, Nat.add_sub_cancel, mul_comm]
  congr 2
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
  congr 1; push_cast; ring

open Classical in
theorem xiGen_eq (q : ℝ) (n t : ℕ) (ram sd sq : Prop) (hq : 2 ≤ q) (hn : 3 ≤ n)
    (hpar : t % 2 = n % 2) (hsd : sd → t ≤ 2 ∧ (Even n → ¬ ram))
    (heven : Even n → (t = 2 ↔ ¬ sq))
    (hpos : 0 < xiShimura q n t ram sd) :
    xiGen q n (if sq then 1 else if ram then 0 else -1) =
      (if sd then 1 else lambdaHanke q n t ram) * xiShimura q n t ram sd := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 < q := by linarith
  have hm1 : 1 ≤ n / 2 := by omega
  have hA : 0 < q ^ (-((n / 2 : ℕ) : ℝ)) := Real.rpow_pos_of_pos hq0 _
  have hB : q ^ (1 - ((n / 2 : ℕ) : ℝ)) = q * q ^ (-((n / 2 : ℕ) : ℝ)) := by
    rw [sub_eq_add_neg, Real.rpow_add hq0, Real.rpow_one]
  have hA2 : q ^ (-(2 * ((n / 2 : ℕ) : ℝ))) = (q ^ (-((n / 2 : ℕ) : ℝ))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; congr 1; push_cast; ring
  have hp := ppow_succ_eq hq0.le (n / 2) hm1
  have hlt : ¬ Even n → True := fun _ => trivial
  by_cases hodd : Odd n
  · have ht : t % 2 = 1 := by rw [hpar]; exact Nat.odd_iff.mp hodd
    have hne : ¬ Even n := Nat.not_even_iff_odd.mpr hodd
    rcases (by omega : t = 1 ∨ t = 3 ∨ 5 ≤ t) with rfl | rfl | h5
    · simp [xiGen, hodd, lambdaHanke, xiShimura]
    · have : ¬ sd := fun h => by have := (hsd h).1; omega
      simp only [xiGen, hodd, ite_true, this, ite_false, lambdaHanke, xiShimura]
      rw [hA2, hp]
      generalize q ^ (-((n / 2 : ℕ) : ℝ)) = A at *
      have : (1 + q) ≠ 0 := by linarith
      field_simp
    · obtain ⟨k, rfl⟩ : ∃ k, t = k + 5 := ⟨t - 5, by omega⟩
      exact absurd hpos (by simp [xiShimura])
  · have hev : Even n := Nat.not_odd_iff_even.mp hodd
    have ht : t % 2 = 0 := by rw [hpar]; exact Nat.even_iff.mp hev
    have hm2 : 2 ≤ n / 2 := by obtain ⟨j, hj⟩ := hev; omega
    have hB1 : q * q ^ (-((n / 2 : ℕ) : ℝ)) < 1 := by
      rw [← hB]
      exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by
        have : (2 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hm2
        linarith)
    have h1q : (1 + q) ≠ 0 := by linarith
    rcases (by omega : t = 0 ∨ t = 2 ∨ t = 4 ∨ 6 ≤ t) with rfl | rfl | rfl | h5
    · have hs : sq := by_contra fun h => by have := (heven hev).mpr h; omega
      simp only [xiGen, hodd, ite_false, hs, ite_true, lambdaHanke, xiShimura]
      split_ifs <;> simp [Real.rpow_neg hq0.le]
    · have hs : ¬ sq := (heven hev).mp rfl
      by_cases hsd' : sd
      · have hr : ¬ ram := (hsd hsd').2 hev
        simp only [xiGen, hodd, ite_false, hs, hr, hsd', ite_true, lambdaHanke, xiShimura]
        generalize q ^ (-((n / 2 : ℕ) : ℝ)) = A at *
        ring
      · by_cases hr : ram
        · simp only [xiGen, hodd, ite_false, hs, hr, hsd', ite_true, lambdaHanke, xiShimura]
          ring
        · simp only [xiGen, hodd, ite_false, hs, hr, hsd', lambdaHanke, xiShimura]
          rw [hB]
          generalize q ^ (-((n / 2 : ℕ) : ℝ)) = A at *
          have : 1 + q * A ≠ 0 := by nlinarith
          field_simp
          ring
    · have hs : sq := by_contra fun h => by have := (heven hev).mpr h; omega
      have hsd' : ¬ sd := fun h => by have := (hsd h).1; omega
      simp only [xiGen, hodd, ite_false, hs, hsd', ite_true, lambdaHanke, xiShimura]
      rw [hB]
      generalize q ^ (-((n / 2 : ℕ) : ℝ)) = A at *
      have : 1 - q * A ≠ 0 := by nlinarith
      have h' : 1 - A * q ≠ 0 := by nlinarith
      field_simp
    · obtain ⟨k, rfl⟩ : ∃ k, t = k + 6 := ⟨t - 6, by omega⟩
      exact absurd hpos (by simp [xiShimura])

theorem dualIndexAt_pos (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    0 < dualIndexAt v Q₀ := by
  unfold dualIndexAt
  have h := NF.nondegenerate_Qp v hQ
  refine inv_pos.mpr (norm_pos_iff.mpr ?_)
  intro h0
  apply h
  exact_mod_cast h0

theorem siegelDensity_eq (I₁ : ShimuraMaximalDensity F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀)
    (v : HeightOneSpectrum (𝓞 F)) :
    NF.siegelDensity v Q₀ Q₀ = dualIndexAt v Q₀ * xiAt v Q₀ := by
  have h := I₁.beta_eq hn Q₀ hQ hmax hdet v
  rw [hankeBeta_gramV v Q₀ hQ] at h
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, norm_pow] at h
  have ha : 0 < ‖(2 : v.adicCompletion F)‖ := norm_pos_iff.mpr two_ne_zero
  generalize ‖(2 : v.adicCompletion F)‖ = a at *
  have hN : ((n * (n - 1) / 2 : ℕ) : ℝ) = (n : ℝ) * (n - 1) / 2 := by
    have hev : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
    rw [Nat.cast_div hev (by norm_num)]
    rcases n with _ | n
    · simp
    · push_cast; simp
  have h1 : (a ^ n) ^ (((n : ℝ) + 1) / 2) * (a ^ n)⁻¹ = a ^ (n * (n - 1) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast a (n * (n - 1) / 2), hN, ← Real.rpow_mul ha.le,
      ← Real.rpow_neg (by positivity), ← Real.rpow_add ha]
    congr 1; ring
  rw [h1] at h
  have hapos : 0 < a ^ (n * (n - 1) / 2) := by positivity
  exact mul_left_cancel₀ hapos.ne' (h.trans (mul_assoc _ _ _))


theorem xiAt_pos (I₁ : ShimuraMaximalDensity F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀)
    (v : HeightOneSpectrum (𝓞 F)) : 0 < xiAt v Q₀ := by
  have h1 := siegelDensity_eq I₁ hn Q₀ hQ hmax hdet v
  have h2 := Tamagawa.siegelDensity_pos v Q₀ hQ
  have h3 := dualIndexAt_pos v Q₀ hQ
  rw [h1] at h2
  exact pos_of_mul_pos_right h2 h3.le

open Classical in
theorem xiGen_local (I₁ : ShimuraMaximalDensity F) (I₂ : ShimuraMaximalTypes F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀)
    (v : HeightOneSpectrum (𝓞 F)) :
    xiGen (normQ v) n (chiK v Q₀) = lambdaAt v Q₀ * xiAt v Q₀ := by
  have hw := two_mul_wittIndex_le v Q₀ hQ
  have hpar : anisoDim v Q₀ % 2 = n % 2 := by unfold anisoDim; omega
  have hpos : 0 < xiAt v Q₀ := xiAt_pos I₁ hn Q₀ hQ hmax hdet v
  have := xiGen_eq (normQ v) n (anisoDim v Q₀) (IsRamifiedAt v Q₀) (dualIndexAt v Q₀ = 1)
    (IsSquare (algebraMap F (v.adicCompletion F) (discK Q₀)))
    (by have := NFEuler.two_le_normP v; unfold normQ; exact_mod_cast this) hn hpar
    (I₂.selfDual hn Q₀ hQ hmax v)
    (fun he => I₂.even_two_iff hn he Q₀ hQ v) hpos
  unfold chiK lambdaAt xiAt
  convert this


theorem abs_chiK_le (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) : |chiK v Q₀| ≤ 1 := by
  unfold chiK
  split_ifs <;> simp

theorem hasProd_ppow (k : ℕ) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => ppow (normQ v) k)
      (∏ i ∈ Finset.range k, (NFEuler.dedekindZetaR F (2 * ((i : ℝ) + 1)))⁻¹) :=
  hasProd_prod fun i _ => NFEuler.hasProd_one_sub_rpow (s := 2 * ((i : ℝ) + 1))
    (by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith)

theorem hasProd_xiGen (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => xiGen (normQ v) n (chiK v Q₀))
      (if Odd n then ∏ i ∈ Finset.range (n / 2), (NFEuler.dedekindZetaR F (2 * ((i : ℝ) + 1)))⁻¹
       else (NFEuler.LFunctionNF (fun v => chiK v Q₀) ((n / 2 : ℕ) : ℝ))⁻¹ *
         ∏ i ∈ Finset.range (n / 2 - 1), (NFEuler.dedekindZetaR F (2 * ((i : ℝ) + 1)))⁻¹) := by
  by_cases hodd : Odd n
  · simp only [xiGen, hodd, ite_true]
    exact hasProd_ppow _
  · simp only [xiGen, hodd, ite_false]
    have hev : Even n := Nat.not_odd_iff_even.mp hodd
    have hm2 : 2 ≤ n / 2 := by obtain ⟨j, hj⟩ := hev; omega
    have hs : (1 : ℝ) < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n / 2)
    have hχ : ∀ v : HeightOneSpectrum (𝓞 F), |chiK v Q₀| ≤ 1 := fun v => abs_chiK_le v Q₀
    have hL := NFEuler.hasProd_LFunctionNF hχ hs
    have hLinv : HasProd (fun v : HeightOneSpectrum (𝓞 F) => 1 - chiK v Q₀ * (normQ v) ^ (-((n / 2 : ℕ) : ℝ)))
        (NFEuler.LFunctionNF (fun v => chiK v Q₀) ((n / 2 : ℕ) : ℝ))⁻¹ := by
      have := hL.inv₀ (NFEuler.LFunctionNF_pos hχ hs).ne'
      convert this using 1
      funext v
      rw [NFEuler.lFactor, inv_inv]
    exact hLinv.mul (hasProd_ppow _)


theorem hessian_det_cast (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) :
    ((((NF.Qp v Q₀).hessian.det : v.adicCompletionIntegers F)) : v.adicCompletion F) =
      FinitePlace.embedding v (algebraMap (𝓞 F) F Q₀.hessian.det) := by
  have h : (NF.Qp v Q₀).hessian = Q₀.hessian.map (NF.ι v) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl


theorem hasFiniteMulSupport_norm_emb {x : 𝓞 F} (hx : x ≠ 0) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖FinitePlace.embedding v (algebraMap (𝓞 F) F x)‖ := by
  have h0 : {v : HeightOneSpectrum (𝓞 F) | x ∈ v.asIdeal}.Finite := by
    have h_span_nezero : Ideal.span {x} ≠ 0 := by simp [hx]
    simp only [← Ideal.dvd_span_singleton]
    exact Ideal.finite_factors h_span_nezero
  refine h0.subset fun v hv => ?_
  by_contra h
  apply hv
  exact (FinitePlace.norm_eq_one_iff_notMem F v x).mpr h

theorem dualIndexAt_eq (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) :
    dualIndexAt v Q₀ = ‖FinitePlace.embedding v (algebraMap (𝓞 F) F Q₀.hessian.det)‖⁻¹ := by
  unfold dualIndexAt
  rw [hessian_det_cast]

theorem hasFiniteMulSupport_dualIndexAt (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => dualIndexAt v Q₀ := by
  simp_rw [dualIndexAt_eq]
  exact (hasFiniteMulSupport_norm_emb hQ).inv

/-- `P0 = ∏_w w(det H)^mult`. -/
theorem tprod_dualIndexAt (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    ∏' v : HeightOneSpectrum (𝓞 F), dualIndexAt v Q₀ =
      ∏ w : InfinitePlace F, w (algebraMap (𝓞 F) F Q₀.hessian.det) ^ w.mult := by
  have h := prod_infinitePlace_mul_tprod_finitePlace (F := F) hQ
  have hfin := hasFiniteMulSupport_norm_emb hQ
  have e1 : ∏' v : HeightOneSpectrum (𝓞 F), dualIndexAt v Q₀ =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), dualIndexAt v Q₀ :=
    tprod_eq_finprod (L := SummationFilter.unconditional _) (hasFiniteMulSupport_dualIndexAt Q₀ hQ)
  have e2 : ∏' v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v (algebraMap (𝓞 F) F Q₀.hessian.det)‖ =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v (algebraMap (𝓞 F) F Q₀.hessian.det)‖ :=
    tprod_eq_finprod (L := SummationFilter.unconditional _) hfin
  rw [e2] at h
  rw [e1]
  simp_rw [dualIndexAt_eq]
  rw [finprod_inv_distrib]
  exact inv_eq_of_mul_eq_one_right (by rw [mul_comm]; exact h)


theorem hessian_det_map (Q₀ : QuadForm (𝓞 F) n) :
    (Q₀.map (algebraMap (𝓞 F) F)).hessian.det = algebraMap (𝓞 F) F Q₀.hessian.det := by
  have : (Q₀.map (algebraMap (𝓞 F) F)).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem hessian_det_F_ne_zero (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    (Q₀.map (algebraMap (𝓞 F) F)).hessian.det / 2 ^ n ≠ 0 := by
  rw [hessian_det_map]
  exact div_ne_zero ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ) (pow_ne_zero _ two_ne_zero)

theorem volCAt_pos (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (w : InfinitePlace F) : 0 < volCAt Q₀ w := by
  unfold volCAt
  have hB : 0 < w ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det / 2 ^ n) ^ w.mult :=
    pow_pos (InfinitePlace.pos_iff.mpr (hessian_det_F_ne_zero Q₀ hQ)) _
  refine mul_pos (Real.rpow_pos_of_pos hB _) ?_
  have := tauR_pos
  split_ifs
  · unfold volCReal; have := tauR_pos (n - rAt Q₀ w); have := tauR_pos (rAt Q₀ w); positivity
  · unfold volCComplex; have := tauR_pos n; positivity

open Classical in
theorem prod_volCAt_inv (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    (∏ w, volCAt Q₀ w)⁻¹ =
      (∏ w : InfinitePlace F, (w ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det / 2 ^ n) ^ w.mult)) ^ (((n : ℝ) + 1) / 2) *
      ((tauR n)⁻¹ ^ Module.finrank ℚ F * (∏ w : {w : InfinitePlace F // w.IsReal}, bPhi n (rAt Q₀ w)) *
        ((2 : ℝ) ^ (-(((n : ℝ) - 1) * (n - 2)) / 2) * π ^ ((n : ℝ) * (n + 1) / 4) *
          ∏ l ∈ Finset.range n, (Gamma (((l : ℝ) + 1) / 2))⁻¹) ^ InfinitePlace.nrComplexPlaces F) := by
  have hBpos : ∀ w : InfinitePlace F, 0 < w ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det / 2 ^ n) ^ w.mult := by
    exact fun w => pow_pos (InfinitePlace.pos_iff.mpr (hessian_det_F_ne_zero Q₀ hQ)) _
  rw [← Finset.prod_inv_distrib]
  have h1 : ∀ w : InfinitePlace F, (volCAt Q₀ w)⁻¹ =
      (w ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det / 2 ^ n) ^ w.mult) ^ (((n : ℝ) + 1) / 2) *
      (if h : w.IsReal then (tauR n)⁻¹ * bPhi n (rAt Q₀ w)
        else (tauR n)⁻¹ ^ 2 * ((2 : ℝ) ^ (-(((n : ℝ) - 1) * (n - 2)) / 2) * π ^ ((n : ℝ) * (n + 1) / 4) *
          ∏ l ∈ Finset.range n, (Gamma (((l : ℝ) + 1) / 2))⁻¹)) := by
    intro w
    unfold volCAt
    rw [mul_inv, neg_div, Real.rpow_neg (hBpos w).le, inv_inv]
    congr 1
    split_ifs with h
    · have hr := two_mul_rAt_le Q₀ hQ w
      have := inv_volCReal (n - rAt Q₀ w) (rAt Q₀ w)
      rwa [Nat.sub_add_cancel (by omega)] at this
    · exact inv_volCComplex n
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, ← Real.finsetProd_rpow _ _ (fun w _ => (hBpos w).le)]
  congr 1
  simp only [dite_eq_ite]
  rw [Finset.prod_ite]
  have e1 : ∏ w ∈ Finset.univ.filter (fun w : InfinitePlace F => w.IsReal), ((tauR n)⁻¹ * bPhi n (rAt Q₀ w)) =
      (tauR n)⁻¹ ^ InfinitePlace.nrRealPlaces F * ∏ w : {w : InfinitePlace F // w.IsReal}, bPhi n (rAt Q₀ w) := by
    rw [Finset.prod_subtype (Finset.univ.filter (fun w : InfinitePlace F => w.IsReal)) (p := fun w => w.IsReal) (F := inferInstance)
      (by simp), Finset.prod_mul_distrib]
    simp [InfinitePlace.nrRealPlaces]
  have e2 : ∏ w ∈ Finset.univ.filter (fun w : InfinitePlace F => ¬ w.IsReal), ((tauR n)⁻¹ ^ 2 * ((2 : ℝ) ^ (-(((n : ℝ) - 1) * (n - 2)) / 2) * π ^ ((n : ℝ) * (n + 1) / 4) *
          ∏ l ∈ Finset.range n, (Gamma (((l : ℝ) + 1) / 2))⁻¹)) =
      ((tauR n)⁻¹ ^ 2) ^ InfinitePlace.nrComplexPlaces F * ((2 : ℝ) ^ (-(((n : ℝ) - 1) * (n - 2)) / 2) * π ^ ((n : ℝ) * (n + 1) / 4) *
          ∏ l ∈ Finset.range n, (Gamma (((l : ℝ) + 1) / 2))⁻¹) ^ InfinitePlace.nrComplexPlaces F := by
    rw [Finset.prod_const, ← mul_pow]
    simp only [InfinitePlace.nrComplexPlaces]
    congr 1
    rw [Fintype.card_subtype]
    congr 1
    ext w
    simp [InfinitePlace.not_isReal_iff_isComplex]
  rw [e1, e2]
  have hd := InfinitePlace.card_add_two_mul_card_eq_rank F
  rw [← hd, pow_add, ← pow_mul, mul_pow]
  ring


theorem prod_infinitePlace_two :
    ∏ w : InfinitePlace F, w (2 : F) ^ w.mult = (2 : ℝ) ^ Module.finrank ℚ F := by
  rw [InfinitePlace.prod_eq_abs_norm]
  have : (2 : F) = algebraMap ℚ F 2 := by rw [map_ofNat]
  rw [this, Algebra.norm_algebraMap]
  push_cast
  rw [abs_of_pos (by positivity)]

theorem prod_B (Q₀ : QuadForm (𝓞 F) n) :
    ∏ w : InfinitePlace F, (w ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det / 2 ^ n) ^ w.mult) =
      (∏ w : InfinitePlace F, w (algebraMap (𝓞 F) F Q₀.hessian.det) ^ w.mult) /
        ((2 : ℝ) ^ Module.finrank ℚ F) ^ n := by
  rw [hessian_det_map]
  simp_rw [map_div₀, map_pow, div_pow]
  rw [Finset.prod_div_distrib, ← prod_infinitePlace_two, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← pow_mul, ← pow_mul, mul_comm]


theorem ppow_pos {q : ℝ} (hq : 1 < q) (k : ℕ) : 0 < ppow q k := by
  unfold ppow
  refine Finset.prod_pos fun i _ => ?_
  have : q ^ (-(2 * ((i : ℝ) + 1))) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hq (by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith)
  linarith

theorem xiGen_pos {q : ℝ} (hq : 1 < q) (hn : 3 ≤ n) {χ : ℝ} (hχ : |χ| ≤ 1) : 0 < xiGen q n χ := by
  unfold xiGen
  split_ifs with h
  · exact ppow_pos hq _
  · refine mul_pos ?_ (ppow_pos hq _)
    have hA : q ^ (-((n / 2 : ℕ) : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hq (by
        have : (1 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n / 2)
        linarith)
    have hA0 : 0 < q ^ (-((n / 2 : ℕ) : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    have := abs_le.mp hχ
    nlinarith

theorem one_lt_normQ (v : HeightOneSpectrum (𝓞 F)) : 1 < normQ v := by
  have := NFEuler.two_le_normP v
  unfold normQ
  have : (2 : ℝ) ≤ (NFEuler.normP v : ℝ) := by exact_mod_cast this
  linarith

theorem lambdaAt_pos (I₁ : ShimuraMaximalDensity F) (I₂ : ShimuraMaximalTypes F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀)
    (v : HeightOneSpectrum (𝓞 F)) : 0 < lambdaAt v Q₀ := by
  have h := xiGen_local I₁ I₂ hn Q₀ hQ hmax hdet v
  have h1 := xiGen_pos (one_lt_normQ v) hn (abs_chiK_le v Q₀)
  have h2 := xiAt_pos I₁ hn Q₀ hQ hmax hdet v
  rw [h] at h1
  exact pos_of_mul_pos_left h1 h2.le

theorem lambdaAt_eq_one_of (Q₀ : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F))
    (h : dualIndexAt v Q₀ = 1) : lambdaAt v Q₀ = 1 := by
  simp [lambdaAt, h]

theorem hasFiniteMulSupport_lambdaAt (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => lambdaAt v Q₀ := by
  refine (hasFiniteMulSupport_dualIndexAt Q₀ hQ).subset fun v hv => ?_
  simp only [Function.mem_mulSupport] at hv ⊢
  exact fun h => hv (lambdaAt_eq_one_of Q₀ v h)

/-- The value of the Euler product of `xiGen`. -/
def xiGenVal (F : Type) [Field F] [NumberField F] (n : ℕ) (χ : HeightOneSpectrum (𝓞 F) → ℝ) : ℝ :=
  if Odd n then ∏ i ∈ Finset.range (n / 2), (NFEuler.dedekindZetaR F (2 * ((i : ℝ) + 1)))⁻¹
  else (NFEuler.LFunctionNF χ ((n / 2 : ℕ) : ℝ))⁻¹ *
         ∏ i ∈ Finset.range (n / 2 - 1), (NFEuler.dedekindZetaR F (2 * ((i : ℝ) + 1)))⁻¹

theorem tprod_inv_lambdaAt (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    ∏' v : HeightOneSpectrum (𝓞 F), (lambdaAt v Q₀)⁻¹ = (∏' v : HeightOneSpectrum (𝓞 F), lambdaAt v Q₀)⁻¹ := by
  have h1 := hasFiniteMulSupport_lambdaAt Q₀ hQ
  have h2 : ∏' v : HeightOneSpectrum (𝓞 F), (lambdaAt v Q₀)⁻¹ = ∏ᶠ v : HeightOneSpectrum (𝓞 F), (lambdaAt v Q₀)⁻¹ :=
    tprod_eq_finprod (L := SummationFilter.unconditional _) (f := fun v => (lambdaAt v Q₀)⁻¹) h1.inv
  rw [tprod_eq_finprod (L := SummationFilter.unconditional _) h1, h2, finprod_inv_distrib]

theorem tprod_siegelDensity_eq (I₁ : ShimuraMaximalDensity F) (I₂ : ShimuraMaximalTypes F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀) :
    ∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v Q₀ Q₀ =
      (∏' v, dualIndexAt v Q₀) * (xiGenVal F n (fun v => chiK v Q₀) * (∏' v, lambdaAt v Q₀)⁻¹) := by
  have hI : HasProd (fun v : HeightOneSpectrum (𝓞 F) => dualIndexAt v Q₀) (∏' v, dualIndexAt v Q₀) :=
    (multipliable_of_hasFiniteMulSupport (hasFiniteMulSupport_dualIndexAt Q₀ hQ)).hasProd
  have hΛ : HasProd (fun v : HeightOneSpectrum (𝓞 F) => (lambdaAt v Q₀)⁻¹) (∏' v, (lambdaAt v Q₀)⁻¹) :=
    (multipliable_of_hasFiniteMulSupport (hasFiniteMulSupport_lambdaAt Q₀ hQ).inv).hasProd
  have hG : HasProd (fun v : HeightOneSpectrum (𝓞 F) => xiGen (normQ v) n (chiK v Q₀)) (xiGenVal F n (fun v => chiK v Q₀)) := by
    unfold xiGenVal; exact hasProd_xiGen hn Q₀
  have hξ := hG.mul hΛ
  have h := hI.mul hξ
  have e : (fun v : HeightOneSpectrum (𝓞 F) => dualIndexAt v Q₀ * (xiGen (normQ v) n (chiK v Q₀) * (lambdaAt v Q₀)⁻¹)) =
      fun v => NF.siegelDensity v Q₀ Q₀ := by
    funext v
    rw [siegelDensity_eq I₁ hn Q₀ hQ hmax hdet v, xiGen_local I₁ I₂ hn Q₀ hQ hmax hdet v,
      mul_comm (lambdaAt v Q₀), mul_assoc, mul_inv_cancel₀ (lambdaAt_pos I₁ I₂ hn Q₀ hQ hmax hdet v).ne', mul_one]
  rw [← e, h.tprod_eq, tprod_inv_lambdaAt Q₀ hQ]


theorem two_part (d n : ℕ) :
    (2 : ℝ) ^ (d * (n * (n - 1) / 2)) / (((2 : ℝ) ^ d) ^ n) ^ (((n : ℝ) + 1) / 2) = ((2 : ℝ) ^ (d * n))⁻¹ := by
  have hN : ((n * (n - 1) / 2 : ℕ) : ℝ) = (n : ℝ) * (n - 1) / 2 := by
    have hev : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
    rw [Nat.cast_div hev (by norm_num)]
    rcases n with _ | n
    · simp
    · push_cast; simp
  have h1 : (((2 : ℝ) ^ d) ^ n) ^ (((n : ℝ) + 1) / 2) = (2 : ℝ) ^ ((d : ℝ) * n * (((n : ℝ) + 1) / 2)) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    push_cast; ring_nf
  have h2 : (2 : ℝ) ^ (d * (n * (n - 1) / 2)) = (2 : ℝ) ^ ((d : ℝ) * ((n : ℝ) * (n - 1) / 2)) := by
    rw [← Real.rpow_natCast]; push_cast; rw [hN]
  have h3 : (2 : ℝ) ^ (d * n) = (2 : ℝ) ^ ((d : ℝ) * n) := by
    rw [← Real.rpow_natCast]; push_cast; rfl
  rw [h1, h2, h3, ← Real.rpow_sub (by norm_num), ← Real.rpow_neg (by norm_num)]
  congr 1; ring


theorem tprod_dualIndexAt_pos (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    0 < ∏' v : HeightOneSpectrum (𝓞 F), dualIndexAt v Q₀ := by
  rw [tprod_dualIndexAt Q₀ hQ]
  exact Finset.prod_pos fun w _ => pow_pos (InfinitePlace.pos_iff.mpr
    ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ)) _

theorem tprod_lambdaAt_pos (I₁ : ShimuraMaximalDensity F) (I₂ : ShimuraMaximalTypes F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀) :
    0 < ∏' v : HeightOneSpectrum (𝓞 F), lambdaAt v Q₀ := by
  have h1 := hasFiniteMulSupport_lambdaAt Q₀ hQ
  rw [tprod_eq_finprod (L := SummationFilter.unconditional _) h1,
    finprod_eq_prod _ h1]
  exact Finset.prod_pos fun v _ => lambdaAt_pos I₁ I₂ hn Q₀ hQ hmax hdet v

open Classical in
theorem rhs_identity (I₁ : ShimuraMaximalDensity F) (I₂ : ShimuraMaximalTypes F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀) :
    theorem51RHS Q₀ =
      2 * (|(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) *
        (((2 : ℝ) ^ (Module.finrank ℚ F * (n * (n - 1) / 2)))⁻¹ * ∏' v, NF.siegelDensity v Q₀ Q₀)⁻¹) /
        ∏ w, volCAt Q₀ w := by
  rw [tprod_siegelDensity_eq I₁ I₂ hn Q₀ hQ hmax hdet, div_eq_mul_inv, prod_volCAt_inv Q₀ hQ, prod_B,
    ← tprod_dualIndexAt Q₀ hQ]
  have hI := tprod_dualIndexAt_pos Q₀ hQ
  have hΛ := tprod_lambdaAt_pos I₁ I₂ hn Q₀ hQ hmax hdet
  have hG : xiGenVal F n (fun v => chiK v Q₀) = if Odd n then ∏ i ∈ Finset.range (n / 2), (NFEuler.dedekindZetaR F (2 * ((i : ℝ) + 1)))⁻¹
  else (NFEuler.LFunctionNF (fun v => chiK v Q₀) ((n / 2 : ℕ) : ℝ))⁻¹ *
         ∏ i ∈ Finset.range (n / 2 - 1), (NFEuler.dedekindZetaR F (2 * ((i : ℝ) + 1)))⁻¹ := rfl
  unfold theorem51RHS
  dsimp only
  rw [hG]
  generalize ∏' v, dualIndexAt v Q₀ = I at *
  generalize ∏' v, lambdaAt v Q₀ = Λ at *
  generalize (∏ w : {w : InfinitePlace F // w.IsReal}, bPhi n (rAt Q₀ w)) = B
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hk1 : 1 ≤ k := by omega
    have hodd : ¬ Odd (2 * (k + 1)) := by
      rw [Nat.not_odd_iff_even]; exact ⟨k + 1, by ring⟩
    simp only [hodd, ite_false]
    have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have e2 : (2 * k + 1) ^ 2 / 4 = k ^ 2 + k := by
      rw [show (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 by ring]; omega
    have e3 : (2 * k + 1) / 2 = k := by omega
    have e4 : (2 * (k + 1)) / 2 = k + 1 := by omega
    have e5 : k + 1 - 1 = k := by omega
    have hL : (((2 * (k + 1) : ℕ) : ℝ)) / 2 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    simp only [e1, e2, e3, e4, e5, hL]
    rw [inv_tauR_even (m := k + 1) (by omega), e5]
    have hD : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
    have hZ : ∀ i : ℕ, 0 < NFEuler.dedekindZetaR F (2 * ((i : ℝ) + 1)) := fun i =>
      lt_of_lt_of_le one_pos (NFEuler.one_le_dedekindZetaR (by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith))
    have hLpos : 0 < NFEuler.LFunctionNF (fun v => chiK v Q₀) ((k + 1 : ℕ) : ℝ) :=
      NFEuler.LFunctionNF_pos (fun v => abs_chiK_le v Q₀) (by
        have : (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ k + 1)
        linarith)
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_pow]
    simp only [Finset.prod_inv_distrib]
    have hX : 0 < (((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * (k + 1))) ^ ((((2 * (k + 1) : ℕ) : ℝ) + 1) / 2) := by
      positivity
    have fI : (I / ((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * (k + 1))) ^ ((((2 * (k + 1) : ℕ) : ℝ) + 1) / 2) =
        I ^ ((((2 * (k + 1) : ℕ) : ℝ) - 1) / 2) * I /
          (((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * (k + 1))) ^ ((((2 * (k + 1) : ℕ) : ℝ) + 1) / 2) := by
      rw [Real.div_rpow hI.le (by positivity)]
      congr 1
      rw [show (((2 * (k + 1) : ℕ) : ℝ) + 1) / 2 = (((2 * (k + 1) : ℕ) : ℝ) - 1) / 2 + 1 by ring,
        Real.rpow_add hI, Real.rpow_one]
    have fD : |(discr F : ℝ)| ^ (((2 * (k + 1) : ℕ) : ℝ) * (((2 * (k + 1) : ℕ) : ℝ) - 1) / 4) =
        |(discr F : ℝ)| ^ (k ^ 2 + k) * (|(discr F : ℝ)| ^ (1 / 2 : ℝ)) ^ k * |(discr F : ℝ)| ^ (1 / 2 : ℝ) := by
      rw [show (((2 * (k + 1) : ℕ) : ℝ) * (((2 * (k + 1) : ℕ) : ℝ) - 1) / 4) =
          ((k ^ 2 + k : ℕ) : ℝ) + (1 / 2) * (k : ℝ) + 1 / 2 by push_cast; ring,
        Real.rpow_add hD, Real.rpow_add hD, Real.rpow_natCast, Real.rpow_mul hD.le, Real.rpow_natCast]
    have h2 := two_part (Module.finrank ℚ F) (2 * (k + 1))
    simp only [e1] at h2
    have ha : (2 : ℝ) ^ (Module.finrank ℚ F * (2 * (k + 1) * (2 * k + 1) / 2)) =
        ((2 : ℝ) ^ (Module.finrank ℚ F * (2 * (k + 1))))⁻¹ *
          (((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * (k + 1))) ^ ((((2 * (k + 1) : ℕ) : ℝ) + 1) / 2) := by
      rw [div_eq_iff hX.ne'] at h2
      exact h2
    have hsq : ((2 : ℝ) ^ (2 * (k + 1))) ^ Module.finrank ℚ F =
        (2 : ℝ) ^ (Module.finrank ℚ F * (2 * (k + 1))) := by
      rw [← pow_mul, mul_comm]
    rw [fD, fI, ha, ← hsq]
    have hZp : 0 < ∏ x ∈ Finset.range k, NFEuler.dedekindZetaR F (2 * ((x : ℝ) + 1)) :=
      Finset.prod_pos fun i _ => hZ i
    generalize (∏ x ∈ Finset.range k, NFEuler.dedekindZetaR F (2 * ((x : ℝ) + 1))) = Zp at *
    generalize (∏ j ∈ Finset.range k, ((Nat.factorial (2 * (j + 1) - 1) : ℝ) / (2 * π) ^ (2 * (j + 1)))) = Fp
    generalize ((((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * (k + 1))) ^ ((((2 * (k + 1) : ℕ) : ℝ) + 1) / 2)) = X at *
    generalize NFEuler.LFunctionNF (fun v => chiK v Q₀) ((k + 1 : ℕ) : ℝ) = L at *
    have h2p : (0 : ℝ) < 2 ^ (2 * (k + 1)) := by positivity
    generalize ((2 : ℝ) ^ (2 * (k + 1))) = T at *
    have hTd : 0 < T ^ Module.finrank ℚ F := by positivity
    field_simp
    ring
  · have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
    have hm1 : 1 ≤ m := by omega
    simp only [hodd, ite_true]
    have e1 : 2 * m + 1 - 1 = 2 * m := by omega
    have e2 : (2 * m) ^ 2 / 4 = m ^ 2 := by
      rw [show (2 * m) ^ 2 = 4 * m ^ 2 by ring]; omega
    have e3 : (2 * m) / 2 = m := by omega
    have e4 : (2 * m + 1) / 2 = m := by omega
    simp only [e1, e2, e3, e4]
    rw [inv_tauR_odd]
    have hD : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
    have hZ : ∀ i : ℕ, 0 < NFEuler.dedekindZetaR F (2 * ((i : ℝ) + 1)) := fun i =>
      lt_of_lt_of_le one_pos (NFEuler.one_le_dedekindZetaR (by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith))
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_pow]
    simp only [Finset.prod_inv_distrib]
    have hX : 0 < (((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * m + 1)) ^ ((((2 * m + 1 : ℕ) : ℝ) + 1) / 2) := by positivity
    have fI : (I / ((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * m + 1)) ^ ((((2 * m + 1 : ℕ) : ℝ) + 1) / 2) =
        I ^ (m + 1) / (((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * m + 1)) ^ ((((2 * m + 1 : ℕ) : ℝ) + 1) / 2) := by
      rw [Real.div_rpow hI.le (by positivity)]
      congr 1
      rw [show (((2 * m + 1 : ℕ) : ℝ) + 1) / 2 = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have fIexp : I ^ ((((2 * m + 1 : ℕ) : ℝ) - 1) / 2) = I ^ m := by
      rw [show (((2 * m + 1 : ℕ) : ℝ) - 1) / 2 = (m : ℝ) by push_cast; ring, Real.rpow_natCast]
    have fD : |(discr F : ℝ)| ^ (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) - 1) / 4) =
        |(discr F : ℝ)| ^ (m ^ 2) * (|(discr F : ℝ)| ^ (1 / 2 : ℝ)) ^ m := by
      rw [show (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) - 1) / 4) = ((m ^ 2 : ℕ) : ℝ) + (1 / 2) * (m : ℝ) by
        push_cast; ring, Real.rpow_add hD, Real.rpow_natCast, Real.rpow_mul hD.le, Real.rpow_natCast]
    have f2 : (2 : ℝ) ^ (-((((2 * m + 1 : ℕ) : ℝ) - 1) / 2) * (Module.finrank ℚ F : ℝ)) =
        ((2 : ℝ) ^ (m * Module.finrank ℚ F))⁻¹ := by
      rw [show -((((2 * m + 1 : ℕ) : ℝ) - 1) / 2) * (Module.finrank ℚ F : ℝ) = -((m * Module.finrank ℚ F : ℕ) : ℝ) by
        push_cast; ring, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    have h2 := two_part (Module.finrank ℚ F) (2 * m + 1)
    simp only [e1] at h2
    have ha : (2 : ℝ) ^ (Module.finrank ℚ F * ((2 * m + 1) * (2 * m) / 2)) =
        ((2 : ℝ) ^ (Module.finrank ℚ F * (2 * m + 1)))⁻¹ *
          (((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * m + 1)) ^ ((((2 * m + 1 : ℕ) : ℝ) + 1) / 2) := by
      rw [div_eq_iff hX.ne'] at h2
      exact h2
    have hsq : ((2 : ℝ) ^ (m + 1)) ^ Module.finrank ℚ F * (2 : ℝ) ^ (m * Module.finrank ℚ F) =
        (2 : ℝ) ^ (Module.finrank ℚ F * (2 * m + 1)) := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [fD, fI, fIexp, f2, ha, ← hsq]
    have hZp : 0 < ∏ x ∈ Finset.range m, NFEuler.dedekindZetaR F (2 * ((x : ℝ) + 1)) :=
      Finset.prod_pos fun i _ => hZ i
    generalize (∏ x ∈ Finset.range m, NFEuler.dedekindZetaR F (2 * ((x : ℝ) + 1))) = Zp at *
    generalize (∏ j ∈ Finset.range m, ((Nat.factorial (2 * (j + 1) - 1) : ℝ) / (2 * π) ^ (2 * (j + 1)))) = Fp
    generalize ((((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * m + 1)) ^ ((((2 * m + 1 : ℕ) : ℝ) + 1) / 2)) = X at *
    have h2p : (0 : ℝ) < 2 ^ (m + 1) := by positivity
    have h2q : (0 : ℝ) < 2 ^ (m * Module.finrank ℚ F) := by positivity
    generalize ((2 : ℝ) ^ (m + 1)) = s at *
    generalize ((2 : ℝ) ^ (m * Module.finrank ℚ F)) = q at *
    field_simp
    ring

/-- **Theorem 5.1** (Hanke thesis, pp. 16–17): for $n\ge3$, a nondegenerate $Q_0$ over $\mathcal O_F$ (any number field, any
signature) for which $\Lambda = \mathcal O_F^n$ is a maximal lattice and Shimura's hypothesis holds, Hanke's mass is the right
side `theorem51RHS`. **Conditional** on the named inputs `ShimuraMaximalDensity F` ((3.3)) and `ShimuraMaximalTypes F`;
$\tau(SO(V)) = 2$ (2.1) and Theorem 2.1 are proved. *Update:* the hypothesis `hdet` (Shimura's) is missing from the
printed statement and is necessary (module docstring). -/
@[kb "hanke2005crelle" "Theorem 5.1, pp. 16–19"]
theorem theorem51 (I₁ : ShimuraMaximalDensity F) (I₂ : ShimuraMaximalTypes F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀) :
    hankeMass Q₀ hQ = ENNReal.ofReal (theorem51RHS Q₀) := by
  have hP := tprod_siegelDensity_pos hn Q₀ hQ
  have hT : 0 < ∏ w, volCAt Q₀ w := Finset.prod_pos fun w _ => volCAt_pos Q₀ hQ w
  unfold hankeMass
  rw [theorem21_tau_two Q₀ hQ hn, tprod_hankeBeta Q₀ hQ (by omega) (by omega), rhs_identity I₁ I₂ hn Q₀ hQ hmax hdet]
  have hX : 0 ≤ |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) *
        (((2 : ℝ) ^ (Module.finrank ℚ F * (n * (n - 1) / 2)))⁻¹ * ∏' v, NF.siegelDensity v Q₀ Q₀)⁻¹ := by
    positivity
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_div_of_pos hT]

end QuadFormsKB.Hanke2005
