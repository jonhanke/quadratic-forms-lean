/-
# Cassels, Appendix A, §3: Watson's "at least two classes for $n > 11$", reduced to Watson-minimal forms

Cassels, *Rational Quadratic Forms* (1978), Appendix A, §3, p. 364, quotes Watson (1975): *every genus of positive
definite forms in $n > 11$ variables has at least $2$ classes* (named statement `WatsonTwoClasses`,
`AppA/Statements.lean`). Cassels gives no proof. Watson's proof has two parts:

1. **Reduction.** Watson's operation (`IsWatsonDerived`, the lattice $\Lambda_p$ of `watsonSub` with the form
   $p^{-1}\phi$) does not increase the number of classes (`encard_genusClasses_le_of_isWatsonDerived`, proved). So it
   suffices to treat, in each genus, one form reached by a chain of operations (`WatsonReach`), and one may take a
   form whose Hessian determinant is minimal among all forms reachable from it (`IsWatsonMinimal`).
2. **The reduced forms.** A case-by-case study of the reduced forms in $n \ge 12$ variables (Watson 1963, 1975),
   exhibiting a second class in each such genus.

**Formalized here.**
* Part 1 completely: `IsWatsonMinimal`; every form reaches a Watson-minimal form (`exists_watsonMinimal`); along a
  chain positive definiteness is kept and the number of classes does not increase (`WatsonReach.posDef`,
  `WatsonReach.encard_genusClasses_le`).
* What minimality gives locally: if $Q$ is Watson-minimal, positive definite, and $Q'$ is derived from $Q$ at $p$ with
  basis matrix $g$ of $\Lambda_p$, then $p^n \le (\det g)^2$ (`IsWatsonMinimal.pow_le_det_sq`), i.e. the index of
  $\Lambda_p$ in $\mathbb Z^n$ is at least $p^{n/2}$; in particular a Watson-minimal positive definite form in
  $n \ge 1$ variables is not $p$ times an integral form for any prime $p$ (`IsWatsonMinimal.not_eq_smul`).
* Part 2 is the named input `WatsonMinimalTwoClasses`: every Watson-minimal positive definite form in $n > 11$
  variables has at least two classes in its genus. It is **not** the conclusion (its hypothesis carries the
  minimality, which is used), and it is implied by Watson's theorem (`watsonMinimalTwoClasses_of_watsonTwoClasses`).
* `watsonTwoClasses_of_minimal`: the named input implies `WatsonTwoClasses`; hence
  `two_le_encard_of_minimal` and `magnus_two_le_of_minimal` (Magnus' $n \ge 35$).

**Not formalized** (the missing lemma): Watson's study of the Watson-minimal genera. Neither the local
classification of the minimal forms (Jordan decompositions at every prime, including $p = 2$) nor the construction of
a second class in each genus is in the library. The book's own sketch for Theorem 3.1 (the lattices
$r\Gamma_8 \perp \Lambda'$ of `encard_genus_ge`) gives two classes only when $r \ge 2$, so for $n \ge 16$ at the very
least, and its local step `WatsonLocalStudy` (bound $16 r \ge n - 6$) is itself a named input.

Variables are $x_0, \dots, x_{n-1}$.
-/
import QuadFormsKB.Literature.Cassels.AppA.WatsonMonotone
import QuadFormsKB.Literature.Cassels.AppB.StatementsAround

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.DefiniteForms

open Siegel

variable {n : ℕ}

/-! ### Chains of Watson operations -/

/-- **Positive definiteness is kept along a chain of Watson operations** (`IsWatsonDerived.posDef` at each step).
Arguments: `h` the chain from `Q` to `Qs`, `hQ` positive definiteness of `Q`. -/
theorem WatsonReach.posDef {Q Qs : QuadForm ℤ n} (h : WatsonReach Q Qs) (hQ : IntQF.PosDef Q) :
    IntQF.PosDef Qs := by
  induction h with
  | refl => exact hQ
  | tail _ hstep ih =>
    obtain ⟨p, hp⟩ := hstep
    exact hp.posDef ih

/-- **Cassels, App. A, §3, p. 365, along a chain:** the genus of the end form of a chain of Watson operations has at
most as many classes as the genus of the start form (`encard_genusClasses_le_of_isWatsonDerived` at each step; no
definiteness needed). Argument: `h` the chain from `Q` to `Qs`. -/
theorem WatsonReach.encard_genusClasses_le {Q Qs : QuadForm ℤ n} (h : WatsonReach Q Qs) :
    (genusClasses Qs).encard ≤ (genusClasses Q).encard := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
    obtain ⟨p, hp⟩ := hstep
    exact (encard_genusClasses_le_of_isWatsonDerived hp).trans ih

/-! ### Watson-minimal forms -/

/-- **Watson-minimal forms** (Watson's reduced forms, Cassels App. A, §3, p. 365): $Q$ in $n$ variables is
*Watson-minimal* if no form reachable from $Q$ by a chain of Watson operations (`WatsonReach`) has a Hessian
determinant of smaller absolute value: $|\det H_Q| \le |\det H_{Q'}|$ for every such $Q'$. Argument: the form `Q`. -/
def IsWatsonMinimal (Q : QuadForm ℤ n) : Prop :=
  ∀ Q' : QuadForm ℤ n, WatsonReach Q Q' → Q.hessian.det.natAbs ≤ Q'.hessian.det.natAbs

/-- **Every form reaches a Watson-minimal form:** take a reachable form whose $|\det H|$ is least (`Nat.find`); every
form reachable from it is reachable from $Q$. Argument: the form `Q`. -/
theorem exists_watsonMinimal (Q : QuadForm ℤ n) : ∃ Qs, WatsonReach Q Qs ∧ IsWatsonMinimal Qs := by
  classical
  have hex : ∃ d : ℕ, ∃ Q' : QuadForm ℤ n, WatsonReach Q Q' ∧ Q'.hessian.det.natAbs = d :=
    ⟨_, Q, Relation.ReflTransGen.refl, rfl⟩
  obtain ⟨Qs, hQs, hd⟩ := Nat.find_spec hex
  refine ⟨Qs, hQs, fun Q' hQ' => ?_⟩
  rw [hd]
  exact Nat.find_min' hex ⟨Q', hQs.trans hQ', rfl⟩

/-- Helper: the Hessian of $cQ$ is $c$ times the Hessian of $Q$. -/
theorem hessian_smul (c : ℤ) (Q : QuadForm ℤ n) : (c • Q).hessian = c • Q.hessian := by
  rw [QuadForm.hessian, QuadForm.hessian, QuadForm.smul_coeff, Matrix.transpose_smul, smul_add]

/-- **Determinant of a derived form:** if $Q(g\vec x) = p\,Q'(\vec x)$ then
$(\det g)^2 \det H_Q = p^n \det H_{Q'}$. Arguments: `g` the basis matrix, `hg` the identity of values. -/
theorem det_sq_mul_det_hessian {Q Q' : QuadForm ℤ n} {p : ℤ} (g : Matrix (Fin n) (Fin n) ℤ)
    (hg : ∀ x, Q.eval (g *ᵥ x) = p * Q'.eval x) :
    g.det ^ 2 * Q.hessian.det = p ^ n * Q'.hessian.det := by
  have h1 : ∀ x, Q.eval (g *ᵥ x) = (p • Q').eval x := by
    intro x
    rw [hg, Siegel.Kneser.eval_smul_form]
  have h2 := (eval_mulVec_eq_iff_hessian Q (p • Q') g).1 h1
  have h3 := congrArg Matrix.det h2
  rw [hessian_smul, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Fintype.card_fin] at h3
  rw [← h3]
  ring

/-- **What Watson-minimality gives at a prime $p$:** if $Q$ is positive definite and Watson-minimal and $Q'$ is derived
from $Q$ at $p$ with basis matrix $g$ of $\Lambda_p$ (`IsWatsonDerived`), then $p^n \le (\det g)^2$; that is, the
index $|\det g|$ of $\Lambda_p$ in $\mathbb Z^n$ is at least $p^{n/2}$ (so the operation does not decrease
$|\det H|$, which it multiplies by $p^n/(\det g)^2$). Arguments: `hQ` positive definiteness, `hmin` minimality, `hp`
primality of `p`, `g` with `hg` the identity $Q(g\vec x) = p\,Q'(\vec x)$, `hrange` the range condition (so that
$Q'$ is derived from $Q$). -/
theorem IsWatsonMinimal.pow_le_det_sq {Q Q' : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (hmin : IsWatsonMinimal Q)
    {p : ℕ} (hp : p.Prime) (g : Matrix (Fin n) (Fin n) ℤ) (hgdet : g.det ≠ 0)
    (hrange : Set.range g.mulVec = (watsonSub Q (p : ℤ) : Set (Fin n → ℤ)))
    (hg : ∀ x, Q.eval (g *ᵥ x) = (p : ℤ) * Q'.eval x) :
    (p : ℤ) ^ n ≤ g.det ^ 2 := by
  have hd : IsWatsonDerived Q p Q' := ⟨hp, g, hgdet, hrange, hg⟩
  have hle := hmin Q' (Relation.ReflTransGen.single ⟨p, hd⟩)
  have hQ' : IntQF.PosDef Q' := hd.posDef hQ
  have hdet := det_sq_mul_det_hessian g hg
  have hD : 0 < |Q.hessian.det| := abs_pos.mpr hQ.nondegenerate
  have hD' : 0 < |Q'.hessian.det| := abs_pos.mpr hQ'.nondegenerate
  have hle' : |Q.hessian.det| ≤ |Q'.hessian.det| := by
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]; exact_mod_cast hle
  have habs := congrArg abs hdet
  rw [abs_mul, abs_mul, abs_pow, abs_pow, sq_abs, abs_of_nonneg (by positivity : (0 : ℤ) ≤ p)] at habs
  -- $(\det g)^2 |D| = p^n |D'| \ge p^n |D|$
  have : (p : ℤ) ^ n * |Q.hessian.det| ≤ g.det ^ 2 * |Q.hessian.det| := by
    rw [habs]
    exact mul_le_mul_of_nonneg_left hle' (by positivity)
  exact le_of_mul_le_mul_right this hD

/-- Helper: for $Q = pR$, $\Lambda_p = \mathbb Z^n$ (the range of the identity matrix). -/
theorem range_one_eq_watsonSub_smul (p : ℤ) (R : QuadForm ℤ n) :
    Set.range (1 : Matrix (Fin n) (Fin n) ℤ).mulVec = (watsonSub (p • R) p : Set (Fin n → ℤ)) := by
  ext c
  simp only [Set.mem_range, one_mulVec, exists_eq, SetLike.mem_coe, true_iff]
  intro b
  rw [Siegel.Kneser.eval_smul_form, Siegel.Kneser.eval_smul_form, ← mul_sub]
  exact dvd_mul_right _ _

/-- Helper: $R$ is derived from $pR$ at the prime $p$, with $g = 1$. -/
theorem isWatsonDerived_smul {p : ℕ} (hp : p.Prime) (R : QuadForm ℤ n) :
    IsWatsonDerived ((p : ℤ) • R) p R :=
  ⟨hp, 1, by simp, range_one_eq_watsonSub_smul _ R, fun x => by rw [one_mulVec, Siegel.Kneser.eval_smul_form]⟩

/-- **A Watson-minimal positive definite form is primitive:** in $n \ge 1$ variables it is not $p$ times an integral
form for any prime $p$ (else $R$ is derived from $Q = pR$ with $g = 1$, and $p^n \le 1$ fails). Arguments: `hQ`
positive definiteness, `hmin` minimality, `hn : 0 < n`, `hp` primality of `p`, `R` the form. -/
theorem IsWatsonMinimal.not_eq_smul {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (hmin : IsWatsonMinimal Q)
    (hn : 0 < n) {p : ℕ} (hp : p.Prime) (R : QuadForm ℤ n) : Q ≠ (p : ℤ) • R := by
  rintro rfl
  have h := hmin.pow_le_det_sq (Q' := R) hQ hp 1 (by simp) (range_one_eq_watsonSub_smul _ R) (fun x => by
    rw [one_mulVec, Siegel.Kneser.eval_smul_form])
  rw [det_one, one_pow] at h
  have h2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have : (2 : ℤ) ^ n ≤ (p : ℤ) ^ n := pow_le_pow_left₀ (by norm_num) h2 n
  have h1 : (2 : ℤ) ≤ 2 ^ n := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  omega

/-! ### The named input and the reduction -/

/-- **Watson's study of the reduced forms** (Watson 1975, quoted by Cassels, App. A, §3, p. 364; named input): every
Watson-minimal (`IsWatsonMinimal`) positive definite integer-valued form $Q$ in $n > 11$ variables has at least two
classes in its genus. This is the part of Watson's proof after the reduction by his operation: a case-by-case study
of the reduced genera (their Jordan decompositions at each prime, where minimality forces the index of $\Lambda_p$ to
be at least $p^{n/2}$, `IsWatsonMinimal.pow_le_det_sq`) and the construction of a second class in each of them. Not
proved here. It is implied by `WatsonTwoClasses` (`watsonMinimalTwoClasses_of_watsonTwoClasses`) and implies it
(`watsonTwoClasses_of_minimal`); it is not definitionally the conclusion, since the minimality hypothesis restricts
the forms and the reduction (`exists_watsonMinimal`, `WatsonReach.encard_genusClasses_le`) is proved. -/
@[kb "cassels1978" "App. A, §3, p. 364 (Watson: the reduced genera in n > 11 variables have at least 2 classes)"]
structure WatsonMinimalTwoClasses : Prop where
  /-- For $n > 11$, a Watson-minimal positive definite $Q$ in $n$ variables has at least two classes in its genus. -/
  two_le : ∀ n : ℕ, 11 < n → ∀ Q : QuadForm ℤ n, IntQF.PosDef Q → IsWatsonMinimal Q →
    (2 : ℕ∞) ≤ (genusClasses Q).encard

/-- **Cassels, App. A, §3, p. 364 (Watson), from the study of the reduced forms:** `WatsonMinimalTwoClasses` implies
`WatsonTwoClasses`. *Proof:* reach a Watson-minimal form (`exists_watsonMinimal`); it is positive definite
(`WatsonReach.posDef`), so its genus has at least two classes, and the genus of $Q$ has at least as many
(`WatsonReach.encard_genusClasses_le`). Argument: `h` the named input. -/
@[kb "cassels1978" "App. A, §3, p. 364 (Watson: every genus in n > 11 variables has at least 2 classes; reduction)"]
theorem watsonTwoClasses_of_minimal (h : WatsonMinimalTwoClasses) : WatsonTwoClasses := by
  refine ⟨fun n hn => le_iInf fun Q => ?_⟩
  obtain ⟨Qs, hr, hm⟩ := exists_watsonMinimal Q.1
  exact (h.two_le n hn Qs (hr.posDef Q.2) hm).trans hr.encard_genusClasses_le

/-- **The named input is implied by Watson's theorem** (so it is exactly what remains): `WatsonTwoClasses` gives
`WatsonMinimalTwoClasses` by forgetting minimality. Argument: `h` Watson's theorem. -/
theorem watsonMinimalTwoClasses_of_watsonTwoClasses (h : WatsonTwoClasses) : WatsonMinimalTwoClasses :=
  ⟨fun _ hn _ hQ _ => h.two_le_encard hn hQ⟩

/-- **From `WatsonMinimalTwoClasses`:** the genus of every positive definite integer-valued form $Q$ in $n > 11$
variables has at least two classes. Arguments: `h` the named input, `hn : 11 < n`, `hQ` positive definiteness. -/
@[kb "cassels1978" "App. A, §3, p. 364 (Watson: every genus in n > 11 variables has at least 2 classes)"]
theorem two_le_encard_of_minimal (h : WatsonMinimalTwoClasses) {Q : QuadForm ℤ n} (hn : 11 < n)
    (hQ : IntQF.PosDef Q) : (2 : ℕ∞) ≤ (genusClasses Q).encard :=
  (watsonTwoClasses_of_minimal h).two_le_encard hn hQ

/-- **From `WatsonMinimalTwoClasses`: the second half of Magnus' statement** (Cassels, App. B, §3, p. 377): every genus
of positive definite forms in $n \ge 35$ variables has at least two classes (`Cassels.WatsonTwoClasses.magnus_two_le`).
Argument: `h` the named input. -/
@[kb "cassels1978" "App. B, §3, p. 377 (every genus with n ≥ 35 has two classes; via Watson, App. A, p. 364)"]
theorem magnus_two_le_of_minimal (h : WatsonMinimalTwoClasses) :
    ∀ (n : ℕ) (Q : QuadForm ℤ n), 35 ≤ n → IntQF.PosDef Q → (2 : ℕ∞) ≤ (genusClasses Q).encard :=
  Cassels.WatsonTwoClasses.magnus_two_le (watsonTwoClasses_of_minimal h)

end QuadFormsKB.DefiniteForms
