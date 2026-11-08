/-
# Watson (1963), Theorem 1 for $n \ge 12$: every genus has at least two classes

G. L. Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963) 549–576,
Theorem 1, first case of (1.1): $c_n \ge 2$, proved in §10 as (10.1). This file assembles the proof for a
Watson-minimal positive definite form $f$ (`IsWatsonMinimal`, the library's version of Watson's reduction, Theorem 2)
in $n \ge 12$ variables, and so discharges `WatsonMinimalTwoClasses` (Cassels, App. A, §3) up to the two named local
inputs below.

**Watson's argument, as formalized.** Suppose the genus of $f$ has one class (`OneClass`). Then $f$ represents over
$\mathbb Z$ every form it represents over all $\mathbb Z_p$ (`OneClass.rep_of_local`). Let $r_p$ be the rank modulo $p$
(`rankModP`); minimality gives $r_p(f) \ge n/2 \ge 6$ for all $p$ (`IsWatsonMinimal.le_two_mul_rankModP`).
* If $r_p(f) \ge 10$ for all $p$, then $f$ represents the perfect form $\Phi_9$ (`phiD 8`) locally, hence globally,
  contradicting Theorem 3 (`not_rep_of_oneClass`).
* Otherwise $r_{p_0}(f) \le 9$ for some $p_0$, and Watson's Lemmas 1, 9, 14 give a quaternary $g$ with
  $f$ in the genus of $g \perp \psi$; with one class, $f \cong g \perp \psi$. *Lemma 12, the bootstrap:* if
  $r_p(f) \ge v + 1$ for all $p$, then $f$ represents the perfect forms $A_5, \Phi_5$ ($v = 5$), $A_6, \Phi_6$ ($v = 6$),
  $E_7$ ($v = 7$), $E_8$ ($v = 8$); each lies in $\psi$ (Lemma 3; $g$ has only $4$ variables), so
  $r_p(\psi) \ge v$ for all $p$ and $r_p(f) \ge r_p(g) + r_p(\psi) \ge v + 2$. From $r \ge 6$ this reaches $r \ge 10$,
  and the first case applies.

**Named inputs** (Watson's local theory, not yet formalized):
* `WatsonLocalProbes`: the local part of Watson's Lemma 2 ((4.12), p. 555) for the forms used: a Watson-minimal $f$
  in $n \ge 12$ variables represents $\varphi$ (in $v \le 9$ variables) over $\mathbb Z_p$ once $r_p(f) \ge v + 1$.
* `WatsonQuaternarySplit`: Watson's Lemma 14 with Lemmas 1, 9, 10 (pp. 553–565): if $r_{p_0}(f) \le 9$, a positive
  quaternary form $g = g(4, p_0^2)$ with $r_p(g) \ge 2$ for all $p$ splits off in the genus of $f$.
-/
import QuadFormsKB.Literature.Watson1963.Descent
import QuadFormsKB.Literature.Watson1963.Primitive
import QuadFormsKB.Literature.Watson1963.ProbeFacts

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms

variable {n : ℕ}

/-! ### The named local inputs -/

/-- **Watson 1963, Lemma 2, local part ((4.12), p. 555), for the perfect forms used in §8** (named input): let $f$ be a
Watson-minimal positive definite form in $n \ge 12$ variables and $p$ a prime. Then over $\mathbb Z_p$, $f$ represents
$A_5$ (`phiA 5`) and $\Phi_5$ (`phiD 4`) if $r_p(f) \ge 6$; $A_6$ and $\Phi_6$ if $r_p(f) \ge 7$; $E_7$ if
$r_p(f) \ge 8$; $E_8$ if $r_p(f) \ge 9$; $\Phi_9$ (`phiD 8`) if $r_p(f) \ge 10$. Watson proves (4.12) for
$p$-adically square-free $f$ and $\varphi$ with $v < \min(r_p(f), n - 2)$; minimal forms are square-free (his
Theorem 2) and these $\varphi$ are square-free. Not proved here: it needs the $p$-adic Jordan decomposition of minimal
forms and the classification of unimodular $\mathbb Z_p$-forms. -/
@[kb "watson1963" "§4, Lemma 2, (4.12), p. 555 (local representations, for the forms of §8)"]
structure WatsonLocalProbes : Prop where
  /-- The local representations, for Watson-minimal positive definite `f` in `n ≥ 12` variables and a prime `p`. -/
  rep : ∀ (n : ℕ) (f : QuadForm ℤ n), IntQF.PosDef f → IsWatsonMinimal f → 12 ≤ n →
    ∀ (p : ℕ) [Fact p.Prime],
      (6 ≤ rankModP p f → RepOver ℤ_[p] f (phiA 5) ∧ RepOver ℤ_[p] f (phiD 4)) ∧
      (7 ≤ rankModP p f → RepOver ℤ_[p] f (phiA 6) ∧ RepOver ℤ_[p] f (phiD 5)) ∧
      (8 ≤ rankModP p f → RepOver ℤ_[p] f formE7) ∧
      (9 ≤ rankModP p f → RepOver ℤ_[p] f formE8) ∧
      (10 ≤ rankModP p f → RepOver ℤ_[p] f (phiD 8))

/-- **Watson 1963, Lemma 14 with Lemmas 1, 9, 10 (pp. 553–565), the case used in (10.1)** (named input): let $f$ be
a Watson-minimal positive definite form in $n \ge 12$ variables with $r_{p_0}(f) \le 9$ for a prime $p_0$. Then
there are a positive definite quaternary form $g$ (Watson's $g(4, p_0^2)$) with $r_p(g) \ge 2$ for every prime $p$,
whose reduction modulo $2$ vanishes on the radical of its polar form (Watson's condition (4.1)), and a form $\psi$ in
$n - 4$ variables, such that $f$ and $g \perp \psi$ are isometric over $\mathbb R$ and over every $\mathbb Z_p$ (same
genus). Not proved here: it needs the existence of a genus with prescribed local components (Watson's Lemma 1, from
Theorems 42, 43 of his book) and the construction of $g(4, p_0^2)$ (Lemma 9). -/
@[kb "watson1963" "§9, Lemma 14, p. 565, with Lemmas 1, 9, 10 (g(4, p²) splits off)"]
structure WatsonQuaternarySplit : Prop where
  /-- The splitting, for Watson-minimal positive definite `f` in `n ≥ 12` variables and a prime `p₀` with
  `rankModP p₀ f ≤ 9`. -/
  split : ∀ (n : ℕ) (f : QuadForm ℤ n), IntQF.PosDef f → IsWatsonMinimal f → 12 ≤ n →
    ∀ (p₀ : ℕ) [Fact p₀.Prime], rankModP p₀ f ≤ 9 →
      ∃ (g : QuadForm ℤ 4) (m : ℕ) (ψ : QuadForm ℤ m), IntQF.PosDef g ∧
        (∀ (p : ℕ) [Fact p.Prime], 2 ≤ rankModP p g) ∧
        (∀ x : Fin 4 → ZMod 2, (∀ z, x ⬝ᵥ (g.hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ z) = 0) →
          g.evalIn (ZMod 2) x = 0) ∧
        (∀ (p : ℕ) [Fact p.Prime], IsoOver ℤ_[p] f (QuadForm.orthSum g ψ)) ∧
        IsoOver ℝ f (QuadForm.orthSum g ψ)

/-! ### The bootstrap of Lemma 12 -/

/-- Helper: the rank modulo $p$ is invariant under integral isometries (in possibly cast numbers of variables). -/
theorem rankModP_eq_of_isoOver (p : ℕ) [Fact p.Prime] {a b : ℕ} {A : QuadForm ℤ a} {B : QuadForm ℤ b}
    (h : IsoOver ℤ A B) : rankModP p A = rankModP p B := by
  obtain rfl := h.dim_eq_int
  exact rankModP_eq_of_intEquiv p h.intEquiv

/-- **The rank inequality of the bootstrap** (Watson 1963, (9.3)): if $f \cong g \perp \psi$ over $\mathbb Z$ with
$r_p(g) \ge 2$ for all $p$ and $g$ satisfying Watson's condition at $2$, then $r_p(f) \ge 2 + r_p(\psi)$. -/
theorem rankModP_bound {k m : ℕ} {f : QuadForm ℤ n} {g : QuadForm ℤ k} {ψ : QuadForm ℤ m}
    (hiso : IsoOver ℤ f (QuadForm.orthSum g ψ)) (hg2 : ∀ (p : ℕ) [Fact p.Prime], 2 ≤ rankModP p g)
    (hgrad : ∀ x : Fin k → ZMod 2, (∀ z, x ⬝ᵥ (g.hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ z) = 0) →
      g.evalIn (ZMod 2) x = 0) (p : ℕ) [Fact p.Prime] : 2 + rankModP p ψ ≤ rankModP p f := by
  rw [rankModP_eq_of_isoOver p hiso]
  have h2 := hg2 p
  have hsum : rankModP p g + rankModP p ψ ≤ rankModP p (QuadForm.orthSum g ψ) := by
    by_cases hp : p = 2
    · subst hp
      exact le_rankModP_orthSum 2 g ψ hgrad
    · exact le_rankModP_orthSum_of_odd p hp g ψ
  omega

/-- **A perfect form represented by $f \cong g \perp \psi$, with $g$ in fewer variables, lies in $\psi$**
(Watson 1963, proof of Lemma 12, from Lemma 3). -/
theorem rep_psi_of_rep {k m v : ℕ} {f : QuadForm ℤ n} {g : QuadForm ℤ k} {ψ : QuadForm ℤ m}
    {φ : QuadForm ℤ v} (hg : IntQF.PosDef g) (hψ : IntQF.PosDef ψ) (hiso : IsoOver ℤ f (QuadForm.orthSum g ψ))
    (hφ : IsPerfectOne φ) (hk : k < v) (hr : Rep f φ) : Rep ψ φ :=
  rep_right_of_perfect hg hψ hφ (hφ.not_rep_of_lt g hk) (Rep.of_isoOver hiso hr)

/-- **Watson 1963, (10.1) for minimal forms, from the named inputs:** a Watson-minimal positive definite form in
$n \ge 12$ variables does not have one class in its genus.

*Update (simplification):* Watson's case $r \ge n - 2$ (with Lemma 13) is not needed for
$n \ge 12$: either $r_p \ge 10$ everywhere (Theorem 3 with $\Phi_9$) or some $r_{p_0} \le 9 \le n - 3$ (Lemma 14). -/
theorem not_oneClass_of_minimal (hL : WatsonLocalProbes) (hS : WatsonQuaternarySplit) {f : QuadForm ℤ n}
    (hn : 12 ≤ n) (hf : IntQF.PosDef f) (hmin : IsWatsonMinimal f) : ¬ OneClass f := by
  intro h1
  have hL' := hL.rep n f hf hmin hn
  -- the first case: r ≥ 10 everywhere
  have key : (∀ (p : ℕ) [Fact p.Prime], 10 ≤ rankModP p f) → False := fun h10 =>
    not_rep_of_oneClass hf h1 (phiD_isPerfectOne 8 (by norm_num)) (by norm_num) phiD8_repOver_formE8
      (h1.rep_of_local hf (phiD_posDef 8 (by norm_num)) fun p _ => (hL' p).2.2.2.2 (h10 p))
  by_cases h10 : ∀ (p : ℕ) [Fact p.Prime], 10 ≤ rankModP p f
  · exact key h10
  push_neg at h10
  obtain ⟨p₀, hp₀, hlt⟩ := h10
  obtain ⟨g, m, ψ, hg, hg2, hgrad, hloc, hreal⟩ := hS.split n f hf hmin hn p₀ (by omega)
  have hiso : IsoOver ℤ f (QuadForm.orthSum g ψ) := h1.isoOver hloc hreal
  have hψ : IntQF.PosDef ψ := (hf.of_isoOver_real hreal).orthSum_right
  have hb := rankModP_bound hiso hg2 hgrad
  have hrep : ∀ {v : ℕ} {φ : QuadForm ℤ v}, IsPerfectOne φ → 4 < v →
      (∀ (p : ℕ) [Fact p.Prime], RepOver ℤ_[p] f φ) → Rep ψ φ := fun hφ hv hl =>
    rep_psi_of_rep hg hψ hiso hφ hv (h1.rep_of_local hf hφ.1 hl)
  -- r ≥ 6 from minimality
  have h6 : ∀ (p : ℕ) [Fact p.Prime], 6 ≤ rankModP p f := fun p _ => by
    have := IsWatsonMinimal.le_two_mul_rankModP p hf hmin
    omega
  -- v = 5
  have h7 : ∀ (p : ℕ) [Fact p.Prime], 7 ≤ rankModP p f := by
    have hA := hrep (phiA_isPerfectOne 5) (by norm_num) fun p _ => ((hL' p).1 (h6 p)).1
    have hD := hrep (phiD_isPerfectOne 4 (by norm_num)) (by norm_num) fun p _ => ((hL' p).1 (h6 p)).2
    intro p _
    have := hb p
    rcases rank_five p with h | h
    · have := rankModP_le_of_rep p hA; omega
    · have := rankModP_le_of_rep p hD; omega
  -- v = 6
  have h8 : ∀ (p : ℕ) [Fact p.Prime], 8 ≤ rankModP p f := by
    have hA := hrep (phiA_isPerfectOne 6) (by norm_num) fun p _ => ((hL' p).2.1 (h7 p)).1
    have hD := hrep (phiD_isPerfectOne 5 (by norm_num)) (by norm_num) fun p _ => ((hL' p).2.1 (h7 p)).2
    intro p _
    have := hb p
    rcases rank_six p with h | h
    · have := rankModP_le_of_rep p hA; omega
    · have := rankModP_le_of_rep p hD; omega
  -- v = 7
  have h9 : ∀ (p : ℕ) [Fact p.Prime], 9 ≤ rankModP p f := by
    have hE := hrep formE7_isPerfectOne (by norm_num) fun p _ => (hL' p).2.2.1 (h8 p)
    intro p _
    have := hb p
    have := rank_formE7 p
    have := rankModP_le_of_rep p hE; omega
  -- v = 8
  have h10' : ∀ (p : ℕ) [Fact p.Prime], 10 ≤ rankModP p f := by
    have hE := hrep formE8_isPerfectOne (by norm_num) fun p _ => (hL' p).2.2.2.1 (h9 p)
    intro p _
    have := hb p
    have := rank_formE8 p
    have := rankModP_le_of_rep p hE; omega
  exact key h10'

/-- **Cassels, App. A, §3, p. 364 (Watson 1963, Theorem 1 for $n \ge 12$), the reduced genera, from Watson's local
theory:** the named inputs `WatsonLocalProbes` and `WatsonQuaternarySplit` imply `WatsonMinimalTwoClasses`.
Arguments: `hL`, `hS` the two named inputs. -/
@[kb "watson1963" "§10, (10.1), p. 567 (c(f) ≥ 2 for n ≥ 12; minimal forms)"]
theorem watsonMinimalTwoClasses_of_local (hL : WatsonLocalProbes) (hS : WatsonQuaternarySplit) :
    WatsonMinimalTwoClasses := by
  refine ⟨fun n hn Q hQ hmin => ?_⟩
  by_contra hlt
  push_neg at hlt
  have h1 : (genusClasses Q).encard ≤ 1 := by
    have h2 : (genusClasses Q).encard < 1 + 1 := by simpa [one_add_one_eq_two] using hlt
    exact Order.le_of_lt_add_one h2
  exact not_oneClass_of_minimal hL hS (by omega) hQ hmin (oneClass_of_encard_le_one h1)

/-- **Watson's theorem, from Watson's local theory:** every genus of positive definite forms in $n > 11$ variables
has at least two classes (Cassels, App. A, §3, p. 364), conditional on the named inputs `WatsonLocalProbes` and
`WatsonQuaternarySplit`. -/
@[kb "watson1963" "Theorem 1, (1.1), p. 549 (c_n ≥ 2 for n ≥ 12)"]
theorem watsonTwoClasses_of_local (hL : WatsonLocalProbes) (hS : WatsonQuaternarySplit) : WatsonTwoClasses :=
  watsonTwoClasses_of_minimal (watsonMinimalTwoClasses_of_local hL hS)

end QuadFormsKB.Watson1963
