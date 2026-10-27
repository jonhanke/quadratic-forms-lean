/-
# Siegel's formula: the mass and the genus average $a_E(m)$

**Defines** the class-number statement `GenusFinite` (finiteness of the set of classes in a genus; formerly a cited
input, now proved for positive definite forms, `genusFinite` in `Siegel/GenusFinite.lean`), the mass $\mathrm{Mass}(Q) = \sum_{[Q'] \in \mathrm{Gen}(Q)} 1/|\mathrm{Aut}(Q')|$ (`mass`) and the genus
average of representation numbers
$$a_E(m) = \frac{\sum_{[Q'] \in \mathrm{Gen}(Q)} r_{Q'}(m)/|\mathrm{Aut}(Q')|}{\sum_{[Q'] \in \mathrm{Gen}(Q)} 1/|\mathrm{Aut}(Q')|}$$
(`genusRepAvg`; Hanke 2004, (4.5), p. 366). Sums are `finsum`s over the set `genusClasses Q` of
$\mathrm{GL}_n(\mathbb{Z})$-classes; they are genuine finite sums under `GenusFinite` (`mass_eq_sum`,
`genusRepSum_eq_sum`).

**Proves** that every form in the genus of a positive definite form is positive definite
(`SameGenus.posDef`), $\mathrm{Mass}(Q) > 0$ (`mass_pos`), the one-class case $a_E(m) = r_Q(m)$
(`genusRepAvg_of_classNumber_one`), and the bridge to the AWS notes' `AWS.mass` (`mass_eq_aws_mass`).

Siegel's formula itself ($a_E(m) = \beta_\infty(m)\prod_p\beta_p(m)$) is **not** stated here.
-/
import QuadFormsKB.Siegel.Genus
import QuadFormsKB.Literature.AWS.FourSquares

open Matrix

namespace QuadFormsKB.Siegel

variable {n : ℕ}

/-- **Input: finiteness of the class number** of the genus of $Q$: the set `genusClasses Q` of
$\mathrm{GL}_n(\mathbb{Z})$-classes in the genus of $Q$ is finite.

Field:
- `finite_classes`: $\{[Q'] : Q' \in \mathrm{Gen}(Q)\}$ is a finite set.

True for every nondegenerate integral form (in particular every positive definite one): Cassels,
*Rational Quadratic Forms*, Ch. 9, Thm. 1.1 (reduction theory) [unverified]; Conway–Sloane,
*SPLAG*, Ch. 15 [unverified]. Defined here as a hypothesis; **proved** for every positive definite
$Q$ by Hermite reduction in `Siegel/GenusFinite.lean` (`genusFinite`). -/
@[kb "cassels1978" "Ch. 9, Thm. 1.1, finiteness of the class number [unverified]"]
structure GenusFinite (Q : QuadForm ℤ n) : Prop where
  finite_classes : (genusClasses Q).Finite

/-- **The mass of the genus of $Q$:**
$$\mathrm{Mass}(Q) = \sum_{[Q'] \in \mathrm{Gen}(Q)} \frac{1}{|\mathrm{Aut}(Q')|},$$
over $\mathrm{GL}_n(\mathbb{Z})$-classes, with $\mathrm{Aut}(Q') \le \mathrm{GL}_n(\mathbb{Z})$ (improper automorphisms included).

*Edge cases:* defined as a `finsum`, so it is $0$ if the genus had infinitely many classes (excluded by
`GenusFinite`); an infinite $\mathrm{Aut}$ would contribute $1/0 = 0$ (excluded for positive definite forms).
*Mass formula conventions:* the Smith–Minkowski–Siegel mass formula is usually stated for this
$\mathrm{GL}$ mass (Conway–Sloane); the $\mathrm{SL}$/proper version differs by a factor $2$ for classes without
improper automorphisms. See also `AWS.mass` (`mass_eq_aws_mass`). -/
@[kb "hanke2004" "(4.5), p. 366 (denominator)"]
noncomputable def mass (Q : QuadForm ℤ n) : ℝ :=
  ∑ᶠ c ∈ genusClasses Q, ((c.autCard : ℝ))⁻¹

/-- **The weighted sum of representation numbers over the genus:**
$\sum_{[Q'] \in \mathrm{Gen}(Q)} r_{Q'}(m)/|\mathrm{Aut}(Q')|$ (a `finsum`, as in `mass`). -/
noncomputable def genusRepSum (Q : QuadForm ℤ n) (m : ℤ) : ℝ :=
  ∑ᶠ c ∈ genusClasses Q, (c.repNum m : ℝ) / c.autCard

/-- **The genus average $a_E(m)$** (Hanke 2004, (4.5), p. 366; Siegel):
$$a_E(m) = \frac{1}{\mathrm{Mass}(Q)} \sum_{[Q'] \in \mathrm{Gen}(Q)} \frac{r_{Q'}(m)}{|\mathrm{Aut}(Q')|},$$
the $1/|\mathrm{Aut}|$-weighted average of $r_{Q'}(m) = \#\{\vec{x} \in \mathbb{Z}^n : Q'(\vec{x}) = m\}$ over the
$\mathrm{GL}_n(\mathbb{Z})$-classes in the genus. Meaningful under `GenusFinite` and for positive definite $Q$
(then $\mathrm{Mass}(Q) > 0$, `mass_pos`); otherwise Lean's conventions ($x/0 = 0$) apply. -/
@[kb "hanke2004" "(4.5), p. 366"]
noncomputable def genusRepAvg (Q : QuadForm ℤ n) (m : ℤ) : ℝ :=
  genusRepSum Q m / mass Q

/-- **`mass` as a finite sum** under `GenusFinite`. -/
theorem mass_eq_sum {Q : QuadForm ℤ n} (hF : GenusFinite Q) :
    mass Q = ∑ c ∈ hF.finite_classes.toFinset, ((c.autCard : ℝ))⁻¹ :=
  finsum_mem_eq_finite_toFinset_sum _ hF.finite_classes

/-- **`genusRepSum` as a finite sum** under `GenusFinite`. -/
theorem genusRepSum_eq_sum {Q : QuadForm ℤ n} (hF : GenusFinite Q) (m : ℤ) :
    genusRepSum Q m = ∑ c ∈ hF.finite_classes.toFinset, (c.repNum m : ℝ) / c.autCard :=
  finsum_mem_eq_finite_toFinset_sum _ hF.finite_classes

theorem eval_map_real (Q : QuadForm ℤ n) (y : Fin n → ℝ) :
    (Q.map (Int.castRingHom ℝ)).eval y = Q.evalIn ℝ y := by
  simp [QuadForm.map, QuadForm.evalIn]

/-- **Positive definiteness is a genus invariant:** if $Q$ is positive definite and $Q'$ is in its genus,
then $Q'$ is positive definite. (Only the real place is used: $Q'(\vec{x}) = Q(g_\infty\vec{x}) > 0$ for
$\vec{x} \ne 0$, by `IntQF.PosDef.evalIn_real_pos`.) -/
theorem SameGenus.posDef {Q Q' : IntQF n} (hQ : Q.PosDef) (h : SameGenus Q Q') : Q'.PosDef := by
  intro x hx
  obtain ⟨g, hg⟩ := h.2
  have h1 := hg (fun i => (x i : ℝ))
  rw [eval_map_real, eval_map_real, evalIn_intCast] at h1
  have hne : g.val *ᵥ (fun i => (x i : ℝ)) ≠ 0 := by
    intro h0
    have : (fun i => (x i : ℝ)) = 0 := by
      have := congrArg (fun v => (g⁻¹).val *ᵥ v) h0
      simpa [mulVec_mulVec, ← Units.val_mul] using this
    exact hx (funext fun i => by have := congrFun this i; simpa using this)
  have := hQ.evalIn_real_pos _ hne
  rw [h1] at this
  exact_mod_cast this

/-- **Every class in the genus of a positive definite form has finitely many automorphisms**, so
$|\mathrm{Aut}(Q')| \ge 1$. -/
theorem autCard_pos_of_mem {Q : IntQF n} (hQ : Q.PosDef) {c : QClass n} (hc : c ∈ genusClasses Q) :
    0 < c.autCard := by
  obtain ⟨Q', rfl, hg⟩ := hc
  exact (hg.posDef hQ).card_aut_pos

/-- **The mass is positive** for positive definite $Q$ with finitely many classes in its genus: the class of
$Q$ contributes $1/|\mathrm{Aut}(Q)| > 0$ and the other terms are $\ge 0$. -/
theorem mass_pos {Q : IntQF n} (hQ : Q.PosDef) (hF : GenusFinite Q) : 0 < mass Q := by
  rw [mass_eq_sum hF]
  have hmem : classOf Q ∈ hF.finite_classes.toFinset :=
    (Set.Finite.mem_toFinset _).mpr (classOf_self_mem_genusClasses Q)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun c _ => by positivity) hmem)
  have := hQ.card_aut_pos
  simp only [QClass.autCard_classOf]
  positivity

/-- **One-class genus:** if $[Q]$ is the only class in its genus (class number one), then
$a_E(m) = r_Q(m)$ (used for the sum of four squares in the AWS notes, `hanke2011aws`, p. 36). -/
theorem genusRepAvg_of_classNumber_one {Q : IntQF n} (hQ : Q.PosDef)
    (h1 : genusClasses Q = {classOf Q}) (m : ℤ) : genusRepAvg Q m = repNum Q m := by
  have ha : (0 : ℝ) < Nat.card (Aut Q) := by exact_mod_cast hQ.card_aut_pos
  simp only [genusRepAvg, genusRepSum, mass, h1, finsum_mem_singleton, QClass.repNum_classOf,
    QClass.autCard_classOf]
  field_simp

/-- **Bridge to `AWS.mass`:** under `GenusFinite`, `mass Q` is the AWS notes' mass
$\sum_i 1/|\mathrm{Aut}(H_i)|$ of the Hessians $H_i$ of any choice of representatives of the classes in the genus
(here `Quotient.out`). -/
theorem mass_eq_aws_mass {Q : QuadForm ℤ n} (hF : GenusFinite Q) :
    mass Q = AWS.mass (fun c : hF.finite_classes.toFinset =>
      (Quotient.out (s := intSetoid n) c.1).hessian) := by
  rw [mass_eq_sum hF, AWS.mass]
  rw [← Finset.sum_coe_sort]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  have hc : c.1 = classOf (Quotient.out (s := intSetoid n) c.1) := (Quotient.out_eq _).symm
  have e : c.1.autCard = Nat.card (Aut (Quotient.out (s := intSetoid n) c.1)) := by
    conv_lhs => rw [hc]
    rfl
  rw [e, ← coe_aut_eq_autZ]
  rfl

/-- **The sum of four squares:** `repNum` of $x_0^2 + x_1^2 + x_2^2 + x_3^2$ is the AWS notes' `r4`. -/
theorem repNum_Q4 (m : ℕ) : repNum AWS.Q4 m = AWS.r4 m := rfl

end QuadFormsKB.Siegel
