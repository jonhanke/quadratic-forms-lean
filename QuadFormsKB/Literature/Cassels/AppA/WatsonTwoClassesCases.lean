/-
# Cassels, Appendix A, §3: two families of genera with at least two classes, in every dimension

Toward the named input `WatsonMinimalTwoClasses` (`AppA/WatsonTwoClasses.lean`): two families of positive definite
genera, in any number of variables, for which a second class is exhibited outright. These are the two classical
mechanisms (Cassels, App. B, §3, p. 377 and App. A, §3, (3.1)-(3.2), p. 365) for getting a second class, made to work
next to an arbitrary positive definite form $N$ in $m$ variables.

* `two_le_encard_genusClasses_sumSq_nine_orthSum`: the genus of $I_9 \perp N$ (`sumSq 9`, the sum of nine squares)
  has at least two classes. The second class is that of $(E_8 \perp I_1) \perp N$: the two forms are isometric over
  $\mathbb R$ and over every $\mathbb Z_p$ (the explicit isometries of `sameGenus_sumSq_e8SumSq`, added orthogonally to
  $N$), and they are not integrally equivalent because they have $18 + r_N(1)$, resp. $2 + r_N(1)$, vectors of value
  $1$ (`repNum_orthSum_one`: a vector of value $1$ of a positive definite orthogonal sum lies in one of the summands).
* `two_le_encard_genusClasses_repE8_two_orthSum`: the genus of $E_8 \perp E_8 \perp N$ (`repE8 2`, the form with
  $E_8$-roots of value $1$) has at least two classes (the case $r = 2$ of `encard_genus_ge`: the second class is
  $\Gamma_{16} \perp N$).

* `two_le_encard_of_sameGenus_sumSq_nine_orthSum`, `two_le_encard_of_sameGenus_repE8_two_orthSum`: the same for every
  form $Q$ in the genus of $I_9 \perp N$, resp. $E_8 \perp E_8 \perp N$; these are the cases of the input
  `WatsonMinimalTwoClasses` that are proved (for them minimality is not needed).

Both families occur in every dimension $n \ge 9$, resp. $n \ge 16$. They do not cover all Watson-minimal genera, so the
input `WatsonMinimalTwoClasses` remains (see `AppA/WatsonTwoClasses.lean`).

Variables are $x_0, \dots, x_{n-1}$; in an orthogonal sum $A \perp B$ the first variables carry $A$.
-/
import QuadFormsKB.Literature.Cassels.AppA.WatsonTwoClasses
import QuadFormsKB.Literature.Cassels.AppB.SumSquaresGenus

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.DefiniteForms

open Siegel

/-! ### Vectors of value $1$ in an orthogonal sum -/

/-- Helper: the value of an orthogonal sum at an integer vector is the sum of the values of its two blocks. -/
theorem eval_orthSum_int {a b : ℕ} (A : QuadForm ℤ a) (B : QuadForm ℤ b) (x : Fin (a + b) → ℤ) :
    (QuadForm.orthSum A B).eval x =
      A.eval (fun i => x (Fin.castAdd b i)) + B.eval (fun j => x (Fin.natAdd a j)) := by
  simpa [QuadForm.eval] using QuadForm.evalIn_orthSum ℤ A B x

/-- Helper: an integral form vanishes at $\vec 0$. -/
theorem eval_zero_int {a : ℕ} (A : QuadForm ℤ a) : A.eval (0 : Fin a → ℤ) = 0 := by
  simp [QuadForm.eval, QuadForm.evalIn]

/-- Helper: a positive definite form is non-negative on integer vectors. -/
theorem posDef_eval_nonneg {a : ℕ} {A : QuadForm ℤ a} (hA : IntQF.PosDef A) (x : Fin a → ℤ) :
    0 ≤ A.eval x := by
  by_cases hx : x = 0
  · rw [hx, eval_zero_int]
  · exact (hA x hx).le

/-- Helper: a positive definite form vanishes only at $\vec 0$. -/
theorem posDef_eq_zero_of_eval {a : ℕ} {A : QuadForm ℤ a} (hA : IntQF.PosDef A) {x : Fin a → ℤ}
    (hx : A.eval x = 0) : x = 0 := by
  by_contra h
  have := hA x h
  omega

/-- **Vectors of value $1$ of a positive definite orthogonal sum:** $r_{A \perp B}(1) = r_A(1) + r_B(1)$ for positive
definite integral forms $A$ (in $a$ variables) and $B$ (in $b$ variables). A vector $(\vec u, \vec v)$ with
$A(\vec u) + B(\vec v) = 1$ has one block of value $0$, hence zero, and the other of value $1$. Arguments: `hA`, `hB`
positive definiteness. -/
theorem repNum_orthSum_one {a b : ℕ} {A : QuadForm ℤ a} {B : QuadForm ℤ b} (hA : IntQF.PosDef A)
    (hB : IntQF.PosDef B) : repNum (QuadForm.orthSum A B) 1 = repNum A 1 + repNum B 1 := by
  classical
  set fA : (Fin a → ℤ) → (Fin (a + b) → ℤ) := fun u => Fin.append u 0 with hfA
  set fB : (Fin b → ℤ) → (Fin (a + b) → ℤ) := fun v => Fin.append 0 v with hfB
  have hinjA : Function.Injective fA := by
    intro u u' h
    funext i
    have := congrFun h (Fin.castAdd b i)
    simpa [hfA] using this
  have hinjB : Function.Injective fB := by
    intro v v' h
    funext j
    have := congrFun h (Fin.natAdd a j)
    simpa [hfB] using this
  have hsplit : repSet (QuadForm.orthSum A B) 1 = fA '' repSet A 1 ∪ fB '' repSet B 1 := by
    ext x
    simp only [repSet, Set.mem_ofPred_eq, Set.mem_union, Set.mem_image]
    constructor
    · intro hx
      rw [eval_orthSum_int] at hx
      have h1 := posDef_eval_nonneg hA (fun i => x (Fin.castAdd b i))
      have h2 := posDef_eval_nonneg hB (fun j => x (Fin.natAdd a j))
      have hrec : x = Fin.append (fun i => x (Fin.castAdd b i)) (fun j => x (Fin.natAdd a j)) := by
        funext k
        refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp
      by_cases hz : A.eval (fun i => x (Fin.castAdd b i)) = 0
      · right
        refine ⟨fun j => x (Fin.natAdd a j), by omega, ?_⟩
        rw [posDef_eq_zero_of_eval hA hz] at hrec
        exact hrec.symm
      · left
        have hz' : B.eval (fun j => x (Fin.natAdd a j)) = 0 := by omega
        refine ⟨fun i => x (Fin.castAdd b i), by omega, ?_⟩
        rw [posDef_eq_zero_of_eval hB hz'] at hrec
        exact hrec.symm
    · rintro (⟨u, hu, rfl⟩ | ⟨v, hv, rfl⟩)
      · rw [eval_orthSum_int]
        have e1 : (fun i => (fA u) (Fin.castAdd b i)) = u := by funext i; simp [hfA]
        have e2 : (fun j => (fA u) (Fin.natAdd a j)) = 0 := by funext j; simp [hfA]
        rw [e1, e2, eval_zero_int, hu, add_zero]
      · rw [eval_orthSum_int]
        have e1 : (fun i => (fB v) (Fin.castAdd b i)) = 0 := by funext i; simp [hfB]
        have e2 : (fun j => (fB v) (Fin.natAdd a j)) = v := by funext j; simp [hfB]
        rw [e1, e2, eval_zero_int, hv, zero_add]
  have hdisj : Disjoint (fA '' repSet A 1) (fB '' repSet B 1) := by
    rw [Set.disjoint_left]
    rintro x ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
    have hu0 : u = 0 := by
      funext i
      have := congrFun he (Fin.castAdd b i)
      simpa [hfA, hfB] using this.symm
    simp only [repSet, Set.mem_ofPred_eq] at hu
    rw [hu0, eval_zero_int] at hu
    omega
  have hfinA : (fA '' repSet A 1).Finite := (IntQF.PosDef.repSet_finite hA 1).image _
  have hfinB : (fB '' repSet B 1).Finite := (IntQF.PosDef.repSet_finite hB 1).image _
  rw [repNum, repNum, repNum, hsplit, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq, Set.ncard_union_eq hdisj hfinA hfinB, Set.ncard_image_of_injective _ hinjA,
    Set.ncard_image_of_injective _ hinjB]

/-- Helper: transporting a form along an equality of variable counts does not change its representation numbers. -/
theorem repNum_cast {a a' : ℕ} (h : a = a') (A : QuadForm ℤ a) (m : ℤ) : repNum (h ▸ A) m = repNum A m := by
  subst h; rfl

/-! ### The genus of $I_9 \perp N$ -/

/-- Helper: $(E_8 \perp I_1) \perp N$ as a form in $9 + m$ variables. -/
def e8SumSqOneOrthSum {m : ℕ} (N : QuadForm ℤ m) : QuadForm ℤ (9 + m) :=
  (show 8 + 1 + m = 9 + m by omega) ▸ QuadForm.orthSum (e8SumSq 1) N

/-- Helper: $I_9 \perp N$ and $(E_8 \perp I_1) \perp N$ are in the same genus (the isometries of
`sameGenus_sumSq_e8SumSq`, over $\mathbb R$ and $\mathbb Z_p$, extended by the identity on $N$). -/
theorem sameGenus_sumSq_nine_orthSum {m : ℕ} (N : QuadForm ℤ m) :
    SameGenus (QuadForm.orthSum (sumSq 9) N) (e8SumSqOneOrthSum N) := by
  have key : ∀ (T : Type) [CommRing T], IsoOver T (e8SumSq 1) (sumSq 9) →
      IsoOver T (QuadForm.orthSum (sumSq 9) N) (e8SumSqOneOrthSum N) := fun T _ h =>
    (h.symm.orthSum (IsoOver.refl N)).trans (IsoOver.cast (show 8 + 1 + m = 9 + m by omega) _)
  refine ⟨fun p _ => ?_, ?_⟩
  · by_cases hp : p = 3
    · subst hp
      exact (key _ (isoOver_nine_of_isUnit_five (by
        simpa using isUnit_natCast_padic_of_prime_ne (p := 3) (q := 5) (by norm_num) (by norm_num)))).isometricGL
    · exact (key _ (isoOver_nine_of_isUnit_three (by
        simpa using isUnit_natCast_padic_of_prime_ne (p := p) (q := 3) Nat.prime_three hp))).isometricGL
  · exact (key _ (isoOver_nine_of_isUnit_three (by simp))).isometricGL

/-- Helper: $E_8 \perp I_k$ is positive definite. -/
theorem posDef_e8SumSq (k : ℕ) : IntQF.PosDef (e8SumSq k) := by
  refine posDef_orthSum ?_ posDef_sumSq
  intro x hx
  rw [e8Gram_eval]
  have := e8_posDef x hx
  omega

/-- **The genus of $I_9 \perp N$ has at least two classes** (unconditional, any positive definite $N$ in $m$
variables; the mechanism of Cassels, App. B, §3, p. 377): $(E_8 \perp I_1) \perp N$ lies in the same genus
(`sameGenus_sumSq_nine_orthSum`) and has $2 + r_N(1)$ vectors of value $1$, against $18 + r_N(1)$ for $I_9 \perp N$
(`repNum_orthSum_one`), so the two classes differ. Arguments: `N` the form in `m` variables, `hN` its positive
definiteness. -/
@[kb "cassels1978" "App. A, §3, p. 364 (a genus containing I₉ ⊥ N has at least 2 classes)"]
theorem two_le_encard_genusClasses_sumSq_nine_orthSum {m : ℕ} (N : QuadForm ℤ m) (hN : IntQF.PosDef N) :
    (2 : ℕ∞) ≤ (genusClasses (QuadForm.orthSum (sumSq 9) N)).encard := by
  set Q := QuadForm.orthSum (sumSq 9) N
  have hsub : ({classOf Q, classOf (e8SumSqOneOrthSum N)} : Set (QClass (9 + m))) ⊆ genusClasses Q := by
    rintro c (rfl | rfl)
    · exact classOf_mem_genusClasses_iff.2 (SameGenus.refl _)
    · exact classOf_mem_genusClasses_iff.2 (sameGenus_sumSq_nine_orthSum N)
  have hne : classOf Q ≠ classOf (e8SumSqOneOrthSum N) := by
    intro he
    have h := repNum_eq_of_intEquiv (classOf_eq_classOf_iff.mp he) 1
    have hc : repNum (e8SumSqOneOrthSum N) 1 = repNum (QuadForm.orthSum (e8SumSq 1) N) 1 :=
      repNum_cast (show 8 + 1 + m = 9 + m by omega) _ 1
    rw [hc, repNum_orthSum_one posDef_sumSq hN,
      repNum_orthSum_one (posDef_e8SumSq 1) hN, repNum_sumSq_one, repNum_e8SumSq_one] at h
    omega
  calc (2 : ℕ∞) = ({classOf Q, classOf (e8SumSqOneOrthSum N)} : Set (QClass (9 + m))).encard := by
        rw [Set.encard_pair hne]
    _ ≤ _ := Set.encard_le_encard hsub

/-! ### The genus of $E_8 \perp E_8 \perp N$ -/

/-- **The genus of $E_8 \perp E_8 \perp N$ has at least two classes** (unconditional, any positive definite $N$ in $m$
variables; Cassels, App. A, §3, (3.1)-(3.2), p. 365, with $r = 2$): the case $r = 2$ of `encard_genus_ge`, the second
class being $\Gamma_{16} \perp N$. Here $E_8 \perp E_8$ is `repE8 2` (the $E_8$ form with roots of value $1$).
Arguments: `N` the form in `m` variables, `hN` its positive definiteness. -/
@[kb "cassels1978" "App. A, §3, p. 365 (a genus containing E₈ ⊥ E₈ ⊥ N has at least 2 classes)"]
theorem two_le_encard_genusClasses_repE8_two_orthSum {m : ℕ} (N : QuadForm ℤ m) (hN : IntQF.PosDef N) :
    (2 : ℕ∞) ≤ (genusClasses (QuadForm.orthSum (repE8 2) N)).encard := by
  have := encard_genus_ge 2 N hN
  norm_num at this
  exact this

/-! ### The cases of the named input that are proved -/

/-- **The case of `WatsonMinimalTwoClasses` for genera containing $I_9 \perp N$** (proved, no minimality needed): if
$Q$ in $n$ variables is in the genus of $I_9 \perp N$ for a positive definite $N$ in $m = n - 9$ variables, its genus
has at least two classes. Arguments: `N`, `hN` the positive definite form, `h : 9 + m = n` the count of variables,
`hQ` the genus relation. -/
@[kb "cassels1978" "App. A, §3, p. 364 (case of the reduced genera: genus contains I₉ ⊥ N)"]
theorem two_le_encard_of_sameGenus_sumSq_nine_orthSum {n m : ℕ} {Q : QuadForm ℤ n} (N : QuadForm ℤ m)
    (hN : IntQF.PosDef N) (h : 9 + m = n) (hQ : SameGenus Q (h ▸ QuadForm.orthSum (sumSq 9) N)) :
    (2 : ℕ∞) ≤ (genusClasses Q).encard := by
  subst h
  rw [genusClasses_eq_of_sameGenus hQ]
  exact two_le_encard_genusClasses_sumSq_nine_orthSum N hN

/-- **The case of `WatsonMinimalTwoClasses` for genera containing $E_8 \perp E_8 \perp N$** (proved, no minimality
needed): if $Q$ in $n$ variables is in the genus of $E_8 \perp E_8 \perp N$ (`repE8 2`) for a positive definite $N$ in
$m = n - 16$ variables, its genus has at least two classes. Arguments: `N`, `hN` the positive definite form,
`h : 8 * 2 + m = n` the count of variables, `hQ` the genus relation. -/
@[kb "cassels1978" "App. A, §3, p. 364 (case of the reduced genera: genus contains E₈ ⊥ E₈ ⊥ N)"]
theorem two_le_encard_of_sameGenus_repE8_two_orthSum {n m : ℕ} {Q : QuadForm ℤ n} (N : QuadForm ℤ m)
    (hN : IntQF.PosDef N) (h : 8 * 2 + m = n) (hQ : SameGenus Q (h ▸ QuadForm.orthSum (repE8 2) N)) :
    (2 : ℕ∞) ≤ (genusClasses Q).encard := by
  subst h
  rw [genusClasses_eq_of_sameGenus hQ]
  exact two_le_encard_genusClasses_repE8_two_orthSum N hN

end QuadFormsKB.DefiniteForms
