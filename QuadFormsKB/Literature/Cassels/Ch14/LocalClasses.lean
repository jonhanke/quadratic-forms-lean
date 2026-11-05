/-
# Cassels, Chapter 14, §3: the local classes $\mathcal G_p$ (Lemmas 3.1–3.4)

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §3, pp. 339–341.

Cassels denotes by $\mathcal G_p$ "the set of equivalence classes of primitive $\mathbb Z_p$-integral forms of
discriminant $D$ for $\mathbb Z_p$-equivalence" ($p \le \infty$, $\mathbb Z_\infty = \mathbb R$) and lists them
(Lemmas 3.1–3.3); Lemma 3.4 is the order of the product $\prod_{p \le \infty} \mathcal G_p$. Here the sets of classes
are `LocalClasses p D` (forms over $\mathbb Z_p$, `IsPrimitiveZp`, discriminant $-\det H = D$, modulo
$\mathrm{GL}_2(\mathbb Z_p)$-equivalence) and `RealClasses D` (forms over $\mathbb R$ of discriminant $D$ modulo
$\mathrm{GL}_2(\mathbb R)$-equivalence); their group structure (by "mimicking the argument of Section 2") is not
formalized, only their orders, which is what Lemma 3.4 and the proof of Theorem 5.1 use. All statements are for every
$D \ne 0$ with $D \equiv 0, 1 \pmod 4$ (Cassels' standing assumption), not only fundamental discriminants (for those,
see `Binary.sameGenus_iff_formChar_eq`).

* Lemma 3.1 ($p$ odd): $|\mathcal G_p| = 1$ if $p \nmid D$ and $2$ if $p \mid D$ (`card_localClasses_odd_of_not_dvd`,
  `card_localClasses_odd_of_dvd`);
* Lemma 3.2 ($p = \infty$): $|\mathcal G_\infty| = 1$ if $D > 0$ and $2$ if $D < 0$ (`card_realClasses`);
* Lemma 3.3 ($p = 2$): $|\mathcal G_2| = 1$ if $D$ is odd or $D = 4d$ with $d \equiv 1 \pmod 4$, $4$ if $D = 4d$
  with $8 \mid d$, and $2$ otherwise (`card_localClasses_two`);
* Lemma 3.4: $\prod_{p \le \infty} |\mathcal G_p| = 2^{\lambda + \mu + \nu}$ (`card_prod_localClasses`).

*Reconstruction.* The scan of Lemma 3.3 (ii) and of the exponents in Lemma 3.4 is garbled; the cases are reconstructed
from the classification (a primitive form over $\mathbb Z_2$ of discriminant $4d$ is equivalent to
$u x^2 - u^{-1} d y^2$, $u$ a unit, and its class is determined by the classes of units it represents modulo $8$):
(ii γ) is "$2 \mid d$ but $2^3 \nmid d$" and (ii δ) is "$2^3 \mid d$"; in Lemma 3.4, $\lambda$ is the number of distinct
odd primes dividing $D$, $\mu = 1$ if $D < 0$ and $0$ if $D > 0$, and $\nu = 0$ if $2 \nmid D$ or $D = 4d$,
$d \equiv 1 \pmod 4$, $\nu = 2$ if $2^5 \mid D$, $\nu = 1$ otherwise.
-/
import QuadFormsKB.Literature.Cassels.Ch14.Existence
import QuadFormsKB.Literature.Cassels.Ch14.LocalClassesAux

namespace QuadFormsKB.Composition

open QuadForm Siegel

/-- **Primitive $\mathbb Z_p$-integral binary forms of discriminant $D$** (Cassels, Ch. 14, §3, p. 339): forms
$g = a x^2 + bxy + cy^2$ over $\mathbb Z_p$, not all of $a, b, c$ divisible by $p$, with $b^2 - 4ac = D$. -/
def LocalPrimForm (p : ℕ) [Fact p.Prime] (D : ℤ) : Type :=
  {g : QuadForm ℤ_[p] 2 // IsPrimitiveZp g ∧ -g.hessian.det = (D : ℤ_[p])}

/-- $\mathbb Z_p$-equivalence ($\mathrm{GL}_2(\mathbb Z_p)$) of primitive local forms. -/
def localSetoid (p : ℕ) [Fact p.Prime] (D : ℤ) : Setoid (LocalPrimForm p D) where
  r f g := IsometricGL f.1 g.1
  iseqv := ⟨fun _ => IsometricGL.refl _, fun h => h.symm, fun h h' => h.trans h'⟩

/-- **The set $\mathcal G_p$ of $\mathbb Z_p$-classes** of primitive $\mathbb Z_p$-integral forms of discriminant $D$
(Cassels, Ch. 14, §3, p. 339). -/
@[kb "cassels1978" "Ch. 14, §3, p. 339 (the set 𝒢_p of ℤ_p-classes)"]
def LocalClasses (p : ℕ) [Fact p.Prime] (D : ℤ) : Type := Quotient (localSetoid p D)

/-- Real binary forms of discriminant $D$ (Cassels' $p = \infty$). -/
def RealForm (D : ℤ) : Type := {g : QuadForm ℝ 2 // -g.hessian.det = (D : ℝ)}

/-- $\mathbb R$-equivalence ($\mathrm{GL}_2(\mathbb R)$) of real binary forms. -/
def realSetoid (D : ℤ) : Setoid (RealForm D) where
  r f g := IsometricGL f.1 g.1
  iseqv := ⟨fun _ => IsometricGL.refl _, fun h => h.symm, fun h h' => h.trans h'⟩

/-- **The set $\mathcal G_\infty$ of real classes** of binary forms of discriminant $D$ (Cassels, Ch. 14, §3,
p. 339, $p = \infty$). -/
@[kb "cassels1978" "Ch. 14, §3, p. 339 (𝒢_∞)"]
def RealClasses (D : ℤ) : Type := Quotient (realSetoid D)

/-! ### Helpers for the local classes -/

section Helpers

variable {p : ℕ} [Fact p.Prime] {D : ℤ}

/-- The diagonal primitive form $u x^2 + e y^2$ ($u$ a unit, $-4ue = D$) as a `LocalPrimForm`. -/
noncomputable def diagForm (u e : ℤ_[p]) (hu : IsUnit u) (h : -4 * u * e = (D : ℤ_[p])) : LocalPrimForm p D :=
  ⟨bq u 0 e, Or.inl (by rw [bq_coeff00]; exact hu), by rw [neg_det_bq, ← h]; ring⟩

/-- Every local class is represented by a diagonal form $u x^2 + e y^2$ with $u$ a unit, as soon as middle
coefficients of forms of discriminant $D$ are even. -/
theorem exists_diagForm
    (hhalf : ∀ b' c' w : ℤ_[p], IsUnit w → b' ^ 2 - 4 * w * c' = (D : ℤ_[p]) → ∃ β, b' = 2 * β)
    (F : LocalPrimForm p D) :
    ∃ (u e : ℤ_[p]) (hu : IsUnit u) (h : -4 * u * e = (D : ℤ_[p])), IsometricGL F.1 (diagForm u e hu h).1 := by
  obtain ⟨v, hv⟩ := exists_unit_value F.2.1
  have hdisc : disc2 F.1 = (D : ℤ_[p]) := by rw [← neg_det_eq_disc2]; exact F.2.2
  obtain ⟨e, h, hiso⟩ := exists_diag_of_unit_value hv hdisc hhalf
  exact ⟨F.1.eval v, e, hv, h, hiso⟩

theorem localClasses_sound {F G : LocalPrimForm p D} (h : IsometricGL F.1 G.1) :
    (Quotient.mk (localSetoid p D) F : LocalClasses p D) = Quotient.mk (localSetoid p D) G :=
  Quotient.sound h

theorem localClasses_exact {F G : LocalPrimForm p D}
    (h : (Quotient.mk (localSetoid p D) F : LocalClasses p D) = Quotient.mk (localSetoid p D) G) :
    IsometricGL F.1 G.1 :=
  Quotient.exact h

theorem localClasses_ind {P : LocalClasses p D → Prop} (h : ∀ F : LocalPrimForm p D, P (Quotient.mk _ F))
    (q : LocalClasses p D) : P q := Quotient.ind h q

end Helpers

/-- **Cassels, Ch. 14, Lemma 3.1 (i)** (p. 339): *let $p$ be an odd prime. If $p \nmid D$ the group $\mathcal G_p$ is
trivial.* -/
@[kb "cassels1978" "Ch. 14, Lemma 3.1 (i), p. 339"]
theorem card_localClasses_odd_of_not_dvd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {D : ℤ} (hD4 : D % 4 = 0 ∨ D % 4 = 1)
    (hpD : ¬ (p : ℤ) ∣ D) : Nat.card (LocalClasses p D) = 1 := by
  have hp2 := hp
  have hDu : IsUnit (D : ℤ_[p]) := Binary.isUnit_intCast_padic hpD
  have hhalf := half_of_isUnit_two (isUnit_two_padic hp2) (D : ℤ_[p])
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun q q' => ?_⟩, ?_⟩
  · induction q using localClasses_ind with | _ F => ?_
    induction q' using localClasses_ind with | _ G => ?_
    obtain ⟨u, e, hu, h, hF⟩ := exists_diagForm hhalf F
    obtain ⟨u', e', hu', h', hG⟩ := exists_diagForm hhalf G
    exact localClasses_sound (hF.trans ((odd_equiv_of_isUnit hp2 hDu hu hu' h h').trans hG.symm))
  · obtain ⟨e, he⟩ := exists_e_of_odd hp2 (D : ℤ_[p]) (isUnit_one (M := ℤ_[p]))
    exact ⟨Quotient.mk _ (diagForm 1 e isUnit_one he)⟩

/-- **Cassels, Ch. 14, Lemma 3.1 (ii)** (p. 339): *let $p$ be an odd prime. If $p \mid D$ there are precisely two
classes* (represented by $x^2 - \tfrac14 D y^2$ and $r x^2 - \tfrac14 r^{-1} D y^2$ with $r$ a unit quadratic
non-residue). For every $D \ne 0$, $D \equiv 0, 1 \pmod 4$. -/
@[kb "cassels1978" "Ch. 14, Lemma 3.1 (ii), p. 339"]
theorem card_localClasses_odd_of_dvd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {D : ℤ} (hD : D ≠ 0)
    (hD4 : D % 4 = 0 ∨ D % 4 = 1) (hpD : (p : ℤ) ∣ D) : Nat.card (LocalClasses p D) = 2 := by
  have hp2 := hp
  have hpD' : (p : ℤ_[p]) ∣ (D : ℤ_[p]) := by
    obtain ⟨c, hc⟩ := hpD
    exact ⟨c, by rw [hc]; push_cast; ring⟩
  have hhalf := half_of_isUnit_two (isUnit_two_padic hp2) (D : ℤ_[p])
  obtain ⟨r, hr⟩ := exists_nonresidue (p := p) hp2
  have hr0 : PadicInt.toZMod r ≠ 0 := fun h => hr (h ▸ IsSquare.zero)
  have hrU : IsUnit r := Kneser.isUnit_of_toZMod_ne_zero hr0
  obtain ⟨e0, he0⟩ := exists_e_of_odd hp2 (D : ℤ_[p]) (isUnit_one (M := ℤ_[p]))
  obtain ⟨e1, he1⟩ := exists_e_of_odd hp2 (D : ℤ_[p]) hrU
  rw [Nat.card_eq_two_iff]
  refine ⟨(Quotient.mk (localSetoid p D) (diagForm 1 e0 isUnit_one he0) : LocalClasses p D),
    (Quotient.mk (localSetoid p D) (diagForm r e1 hrU he1) : LocalClasses p D), ?_, ?_⟩
  · intro hq
    have hq' : IsometricGL (bq 1 0 e0) (bq r 0 e1) := Quotient.exact hq
    obtain ⟨z, hz⟩ := (odd_equiv_iff hp2 hpD' isUnit_one hrU he0 he1).mp hq'
    exact hr ⟨PadicInt.toZMod z, by rw [hz, one_mul, map_pow, sq]⟩
  · ext q
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    induction q using localClasses_ind with | _ F => ?_
    obtain ⟨u, e, hu, h, hF⟩ := exists_diagForm hhalf F
    rcases sq_class_two hp2 hr hu with hz | hz
    · exact Or.inl (localClasses_sound (hF.trans ((odd_equiv_iff hp2 hpD' isUnit_one hu he0 h).mpr hz).symm))
    · exact Or.inr (localClasses_sound (hF.trans ((odd_equiv_iff hp2 hpD' hrU hu he1 h).mpr hz).symm))

/-! ### Helpers for the real classes -/

/-- A nonzero-discriminant real binary form is $\mathrm{GL}_2(\mathbb R)$-equivalent to a diagonal form
$u x^2 + e y^2$ with $u \ne 0$ and $-4ue = D$. -/
theorem real_exists_diag {F : QuadForm ℝ 2} {D : ℝ} (hD : D ≠ 0) (hF : disc2 F = D) :
    ∃ u e : ℝ, u ≠ 0 ∧ -4 * u * e = D ∧ IsometricGL F (bq u 0 e) := by
  have hv : ∃ v : Fin 2 → ℝ, F.eval v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 := hcon ![1, 0]
    have h2 := hcon ![0, 1]
    have h3 := hcon ![1, 1]
    rw [eval_two] at h1 h2 h3
    apply hD
    rw [← hF, disc2]
    have ha : F.coeff 0 0 = 0 := by linarith
    have hc : F.coeff 1 1 = 0 := by linarith
    have hb : F.coeff 0 1 = 0 := by linarith
    rw [ha, hb, hc]; ring
  obtain ⟨v, hv⟩ := hv
  have hu : IsUnit (F.eval v) := hv.isUnit
  obtain ⟨e, he, hiso⟩ := exists_diag_of_unit_value hu hF (half_of_isUnit_two (by simpa using (isUnit_iff_ne_zero.mpr (two_ne_zero : (2:ℝ) ≠ 0))) D)
  exact ⟨F.eval v, e, hv, he, hiso⟩

/-- A diagonal form with positive leading coefficient is equivalent to $x^2 - \tfrac14 D y^2$. -/
theorem real_scale_pos {u e D : ℝ} (hu : 0 < u) (h : -4 * u * e = D) :
    IsometricGL (bq u 0 e) (bq 1 0 (-D / 4)) := by
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have key := isometricGL_scale u e (1 / Real.sqrt u) (Real.sqrt u)
    (isUnit_iff_ne_zero.mpr (by positivity)) (isUnit_iff_ne_zero.mpr hs.ne')
  have h1 : u * (1 / Real.sqrt u) ^ 2 = 1 := by
    rw [div_pow, Real.sq_sqrt hu.le]; field_simp
  have h2 : e * Real.sqrt u ^ 2 = -D / 4 := by
    rw [Real.sq_sqrt hu.le]; linear_combination (-1 / 4) * h
  rwa [h1, h2] at key

/-- A diagonal form with negative leading coefficient is equivalent to $-x^2 + \tfrac14 D y^2$. -/
theorem real_scale_neg {u e D : ℝ} (hu : u < 0) (h : -4 * u * e = D) :
    IsometricGL (bq u 0 e) (bq (-1) 0 (D / 4)) := by
  have hu' : 0 < -u := by linarith
  have hs : 0 < Real.sqrt (-u) := Real.sqrt_pos.mpr hu'
  have key := isometricGL_scale u e (1 / Real.sqrt (-u)) (Real.sqrt (-u))
    (isUnit_iff_ne_zero.mpr (by positivity)) (isUnit_iff_ne_zero.mpr hs.ne')
  have h1 : u * (1 / Real.sqrt (-u)) ^ 2 = -1 := by
    have hne : u ≠ 0 := hu.ne
    rw [div_pow, Real.sq_sqrt hu'.le]; field_simp
  have h2 : e * Real.sqrt (-u) ^ 2 = D / 4 := by
    rw [Real.sq_sqrt hu'.le]; linear_combination (1 / 4) * h
  rwa [h1, h2] at key

/-- Normal form: every real form of nonzero discriminant $D$ is equivalent to $x^2 - \tfrac14 D y^2$ or to
$-x^2 + \tfrac14 D y^2$, and when $D > 0$ always to the first. -/
theorem real_normal_form {D : ℤ} (hD : D ≠ 0) (F : RealForm D) :
    (IsometricGL F.1 (bq 1 0 (-(D : ℝ) / 4))) ∨ ((D : ℝ) < 0 ∧ IsometricGL F.1 (bq (-1) 0 ((D : ℝ) / 4))) := by
  have hD' : (D : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hD
  have hF : disc2 F.1 = (D : ℝ) := by rw [← neg_det_eq_disc2]; exact F.2
  obtain ⟨u, e, hu, h, hiso⟩ := real_exists_diag hD' hF
  rcases lt_or_gt_of_ne hu with hneg | hpos
  · by_cases hDpos : (0 : ℝ) < D
    · -- u < 0 and D > 0 force e > 0; swap the variables
      have he : 0 < e := by nlinarith
      left
      exact hiso.trans ((isometricGL_swap u 0 e).trans
        (real_scale_pos he (by linear_combination h)))
    · right
      exact ⟨lt_of_le_of_ne (not_lt.mp hDpos) hD', hiso.trans (real_scale_neg hneg h)⟩
  · left
    exact hiso.trans (real_scale_pos hpos h)

/-- **Cassels, Ch. 14, Lemma 3.2** (pp. 339–340): *($p = \infty$) if $D > 0$ the group $\mathcal G_\infty$ is trivial;
if $D < 0$ it has two elements, represented by $x^2 - \tfrac14 D y^2$ and $-x^2 + \tfrac14 D y^2$.* -/
@[kb "cassels1978" "Ch. 14, Lemma 3.2, pp. 339–340"]
theorem card_realClasses {D : ℤ} (hD : D ≠ 0) : Nat.card (RealClasses D) = if 0 < D then 1 else 2 := by
  have hD' : (D : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hD
  let Np : RealForm D := ⟨bq 1 0 (-(D : ℝ) / 4), by rw [neg_det_bq]; ring⟩
  let Nm : RealForm D := ⟨bq (-1) 0 ((D : ℝ) / 4), by rw [neg_det_bq]; ring⟩
  by_cases hpos : 0 < D
  · rw [if_pos hpos, Nat.card_eq_one_iff_unique]
    have hDr : (0 : ℝ) < D := Int.cast_pos.mpr hpos
    refine ⟨⟨fun q q' => ?_⟩, ⟨Quotient.mk _ Np⟩⟩
    have key : ∀ q : RealClasses D, q = (Quotient.mk (realSetoid D) Np: RealClasses D) := by
      intro q
      induction q using Quotient.ind with | _ F => ?_
      rcases real_normal_form hD F with h | ⟨hneg, _⟩
      · exact Quotient.sound (show IsometricGL F.1 Np.1 from h)
      · exact absurd hneg (not_lt.mpr hDr.le)
    rw [key q, key q']
  · rw [if_neg hpos, Nat.card_eq_two_iff]
    have hDr : (D : ℝ) < 0 := Int.cast_lt_zero.mpr (lt_of_le_of_ne (not_lt.mp hpos) hD)
    refine ⟨(Quotient.mk (realSetoid D) Np : RealClasses D), (Quotient.mk (realSetoid D) Nm : RealClasses D), ?_, ?_⟩
    · intro hq
      have hq' : IsometricGL (bq 1 0 (-(D : ℝ) / 4)) (bq (-1) 0 ((D : ℝ) / 4)) := Quotient.exact hq
      obtain ⟨g, hg⟩ := hq'
      have h1 := hg ![1, 0]
      rw [vec_eta (g.val.mulVec ![1, 0]), bq_eval, bq_eval] at h1
      nlinarith [sq_nonneg ((g.val.mulVec ![1, 0]) 0), sq_nonneg ((g.val.mulVec ![1, 0]) 1)]
    · ext q
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      induction q using Quotient.ind with | _ F => ?_
      rcases real_normal_form hD F with h | ⟨_, h⟩
      · exact Or.inl (Quotient.sound (show IsometricGL F.1 Np.1 from h))
      · exact Or.inr (Quotient.sound (show IsometricGL F.1 Nm.1 from h))

end QuadFormsKB.Composition
