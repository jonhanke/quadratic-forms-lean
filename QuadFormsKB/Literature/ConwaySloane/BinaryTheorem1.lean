/-
# Conway–Sloane, Ch. 15, §3.1, Theorem 1: proof

**Source.** J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §3.1,
Theorem 1, p. 357 (bibliography key `conwaysloane1999`; quoted there from Edwards, *Fermat's Last Theorem*, p. 325;
printed page = PDF page of the chapter file + 351). The book gives no proof; the proof here is new to the formalization.

**Conventions.** As in `Binary.lean`: $a^{b}c$ is $ax^2 + 2bxy + cy^2$, $d = ac - b^2$, proper equivalence is
$B = MAM^{\mathrm t}$ with $\det M = 1$ (`ProperEquiv`); the sequence (5) is `sequenceOf`, its cycle `cycleSet`
(the forms occurring infinitely often). Indices are $0$-based (the book's own). Lattice vectors are pairs
$u = (u_0, u_1) \in \mathbb{Z}^2$ (fields `u.1`, `u.2`); a properly oriented basis $(u, v)$ "represents" $h$ for $f$
(`Rep f u v h`) if $\det(u, v) = 1$, $h.a = f(u)$, $h.b = f(u, v)$, $h.c = f(v)$.

**Proved (no `sorry`, no `native_decide`).** `theorem1 : Theorem1Statement`, the full statement of Theorem 1, for
definite and indefinite forms:
* (a) ultimate periodicity: definite forms by `definite_cycle` (`BinaryExtra.lean`; negative definite forms through
  `negForm`, `ultimatelyPeriodic_def`); indefinite forms (`ultimatelyPeriodic_indef`): with $T = \lfloor\sqrt{-d}\rfloor$
  (`sqrtBound`), as long as $f_i$ is not reduced in the sense `RedT` ($0 < b \le T < b + |a|,\ b + |c|$, which is the
  book's (12), `redT_iff_isReducedIndef`) the entry $|a_{i+1}|$ strictly decreases (`step_cases`, `exists_redT`), and
  reduced forms stay reduced (`redT_step`); the reduced pairs $(a_i, b_i)$ lie in a finite box. As a by-product, the
  forms of every cycle satisfy (12) (`cycleSet_isReducedIndef`, one half of the book's claim on p. 359).
* (b) "properly equivalent $\Rightarrow$ same cycle". Definite forms (`cycleSet_eq_of_properEquiv_def`): the cycle
  contains the unique reduced form (11) of the class (`exists_reduced_mem_cycleSet`, `reduced_pos_unique`). Indefinite
  forms (`cycleSet_eq_of_properEquiv_indef`), by the box argument for the two linear factors
  $\ell_{1,2}(u) = au_0 + (b \mp s)u_1$ of $a \cdot f$, $s = \sqrt{-d}$: a basis $(u, v)$ of a reduced form is *good*
  ($|\ell_1(v)| < |\ell_1(u)|$, $|\ell_2(u)| < |\ell_2(v)|$, ratios of opposite signs; `Setup.good_of_rep`); no nonzero
  lattice vector lies in the box $|\ell_1| < |\ell_1(u)|$, $|\ell_2| < |\ell_2(v)|$ (`Good.box`); hence two good bases
  with $|\ell_2(u)| \le |\ell_2(u')| < |\ell_2(v)|$ agree up to sign (`Setup.unique`). The bases $(e_n, e_{n+1})$ of
  the sequence ($e_{n+2} = -e_n + k_ne_{n+1}$, `vecSeq`, `rep_vecSeq`) have $|\ell_2(e_n)|$ growing at least like
  $((T+1)/s)^n$ (`Setup.growth`), so every reduced form properly equivalent to a reduced $f$ is a later form of the
  sequence of $f$, or $f$ is a later form of its sequence (`Setup.locate`, `cycleSet_eq_of_reduced`).
  "Same cycle $\Rightarrow$ properly equivalent" is `properEquiv_of_periodic` (`Binary.lean`).

No erratum: the statement holds as printed (including definite forms, where the cycle has one or two forms, (9)–(10)).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.ConwaySloane.Binary
import QuadFormsKB.Literature.ConwaySloane.BinaryExtra

namespace QuadFormsKB

namespace ConwaySloane

namespace Binary

/-! ### Proper equivalence in coordinates -/

theorem properEquiv_of_entries {f g : BinForm} (p q r s : ℤ) (hdet : p * s - q * r = 1)
    (ha : g.a = f.a * p ^ 2 + 2 * f.b * p * q + f.c * q ^ 2)
    (hc : g.c = f.a * r ^ 2 + 2 * f.b * r * s + f.c * s ^ 2)
    (hb : g.b = f.a * p * r + f.b * (p * s + q * r) + f.c * q * s) : ProperEquiv f g := by
  refine ⟨!![p, q; r, s], by simp [Matrix.det_fin_two]; linarith, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BinForm.gram, Matrix.mul_apply, Fin.sum_univ_two, ha, hb, hc] <;> ring

/-! ### Negative definite forms: the sign change $a^{b}c \mapsto (-a)^{b}(-c)$ -/

/- `negForm` ($a^{b}c \mapsto (-a)^{b}(-c)$) is defined in `Table152.lean`. -/

theorem negForm_negForm (f : BinForm) : negForm (negForm f) = f := by
  cases f; simp [negForm]

theorem negForm_injective : Function.Injective negForm := fun f g h => by
  rw [← negForm_negForm f, h, negForm_negForm]

theorem negForm_det (f : BinForm) : (negForm f).det = f.det := by
  simp [negForm, BinForm.det]

theorem stepB_neg (b m d : ℤ) : stepB b (-m) d = stepB b m d := by
  simp [stepB, Int.natAbs_neg]

theorem stepPair_neg (d : ℤ) (p : ℤ × ℤ) :
    stepPair d (-p.1, p.2) = (-(stepPair d p).1, (stepPair d p).2) := by
  simp only [stepPair, Int.ediv_neg, stepB_neg]

theorem pairSeq_neg (d : ℤ) (p : ℤ × ℤ) (n : ℕ) :
    pairSeq d (-p.1, p.2) n = (-(pairSeq d p n).1, (pairSeq d p n).2) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pairSeq_succ, pairSeq_succ, ih, stepPair_neg]

theorem sequenceOf_negForm (f : BinForm) (n : ℕ) :
    sequenceOf (negForm f) n = negForm (sequenceOf f n) := by
  simp only [sequenceOf, formSeq, negForm_det]
  have : ((negForm f).a, (negForm f).b) = (-(f.a, f.b).1, (f.a, f.b).2) := rfl
  rw [this, pairSeq_neg]
  simp only [formAt, negForm, stepPair_neg]

theorem properEquiv_negForm {f g : BinForm} (h : ProperEquiv f g) :
    ProperEquiv (negForm f) (negForm g) := by
  obtain ⟨p, q, r, s, hdet, ha, hc, hb⟩ := equiv_entries h
  refine properEquiv_of_entries p (-q) (-r) s (by linarith) ?_ ?_ ?_ <;>
    simp only [negForm, ha, hb, hc] <;> ring

theorem cycleSet_negForm (f : BinForm) : cycleSet (negForm f) = negForm '' cycleSet f := by
  ext x
  simp only [cycleSet, recurrentSet, Set.mem_ofPred_eq, Set.mem_image, sequenceOf_negForm]
  constructor
  · intro h
    refine ⟨negForm x, fun N => ?_, negForm_negForm x⟩
    obtain ⟨n, hn, e⟩ := h N
    exact ⟨n, hn, by rw [← e, negForm_negForm]⟩
  · rintro ⟨y, hy, rfl⟩ N
    obtain ⟨n, hn, e⟩ := hy N
    exact ⟨n, hn, by rw [e]⟩

theorem ultimatelyPeriodic_of_negForm {f : BinForm} (h : UltimatelyPeriodic (sequenceOf (negForm f))) :
    UltimatelyPeriodic (sequenceOf f) := by
  obtain ⟨N, p, hp, h⟩ := h
  refine ⟨N, p, hp, fun n hn => negForm_injective ?_⟩
  rw [← sequenceOf_negForm, ← sequenceOf_negForm]
  exact h n hn

/-! ### Definite forms -/

theorem pos_seq_facts {f : BinForm} (ha : 0 < f.a) (hd : 0 < f.det) (n : ℕ) :
    0 < (pairSeq f.det (f.a, f.b) n).1 ∧ StepInv f.det (pairSeq f.det (f.a, f.b) n) := by
  have hI0 : StepInv f.det (f.a, f.b) := BinForm.stepInv (not_isSquare_neg_of_pos hd)
  induction n with
  | zero => exact ⟨ha, hI0⟩
  | succ n ih =>
    rw [pairSeq_succ]
    exact ⟨(step_pos_facts hd ih.1 ih.2).1, ih.2.step (not_isSquare_neg_of_pos hd)⟩

/-- Every form of the cycle of a positive definite form has $a > 0$ and $-a < 2b \le a$. -/
theorem cycleSet_pos_range {f : BinForm} (ha : 0 < f.a) (hd : 0 < f.det) {x : BinForm}
    (hx : x ∈ cycleSet f) : 0 < x.a ∧ -x.a < 2 * x.b ∧ 2 * x.b ≤ x.a := by
  obtain ⟨n, hn, rfl⟩ := hx 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := pos_seq_facts ha hd m
  have h2 := step_pos_facts hd h.1 h.2
  simp only [sequenceOf, formSeq, formAt, pairSeq_succ]
  exact h2

theorem cycleSet_eq_of_mem {f x : BinForm} (hf : ¬ IsSquare (-f.det)) (hx : x ∈ cycleSet f) :
    cycleSet x = cycleSet f := by
  obtain ⟨n, -, rfl⟩ := hx 0
  exact cycleSet_sequenceOf hf n

theorem properEquiv_of_mem_cycleSet {f x : BinForm} (hf : ¬ IsSquare (-f.det)) (hx : x ∈ cycleSet f) :
    ProperEquiv f x := by
  obtain ⟨n, -, rfl⟩ := hx 0
  exact (properEquiv_sequenceOf hf n).1

/-- The cycle of a positive definite form contains a reduced form in the sense of (11). -/
theorem exists_reduced_mem_cycleSet {f : BinForm} (ha : 0 < f.a) (hd : 0 < f.det) :
    ∃ x ∈ cycleSet f, IsReducedPos x.a x.b x.c := by
  obtain ⟨-, h | h⟩ := definite_cycle f ha hd
  · obtain ⟨a, b, hc, hb⟩ := h
    have hx : (⟨a, b, a⟩ : BinForm) ∈ cycleSet f := by rw [hc]; rfl
    obtain ⟨h1, h2, h3⟩ := cycleSet_pos_range ha hd hx
    simp only at h1 h2 h3
    refine ⟨_, hx, ?_⟩
    rw [abs_of_pos h1] at hb
    unfold IsReducedPos
    simp only
    omega
  · obtain ⟨a, b, c, -, hc⟩ := h
    have hx : (⟨a, b, c⟩ : BinForm) ∈ cycleSet f := by rw [hc]; simp
    have hy : (⟨c, -b, a⟩ : BinForm) ∈ cycleSet f := by rw [hc]; simp
    obtain ⟨h1, h2, h3⟩ := cycleSet_pos_range ha hd hx
    obtain ⟨h4, h5, h6⟩ := cycleSet_pos_range ha hd hy
    simp only at h1 h2 h3 h4 h5 h6
    by_cases hac : a < c ∨ (a = c ∧ 0 ≤ b)
    · refine ⟨_, hx, ?_⟩
      unfold IsReducedPos
      simp only
      omega
    · refine ⟨_, hy, ?_⟩
      unfold IsReducedPos
      simp only
      omega

theorem pos_of_properEquiv {f g : BinForm} (ha : 0 < f.a) (hd : 0 < f.det) (h : ProperEquiv f g) :
    0 < g.a := by
  obtain ⟨p, q, r, s, hdet, hga, -, -⟩ := equiv_entries h
  simp only [BinForm.det] at hd
  have key : f.a * g.a = (f.a * p + f.b * q) ^ 2 + (f.a * f.c - f.b ^ 2) * q ^ 2 := by
    rw [hga]; ring
  have hpos : 0 < f.a * g.a := by
    by_cases hq : q = 0
    · subst hq
      have hp : p ≠ 0 := by rintro rfl; simp at hdet
      rw [key]
      have : 0 < (f.a * p) ^ 2 := by positivity
      simpa using this
    · have : 0 < q ^ 2 := by positivity
      rw [key]
      nlinarith [sq_nonneg (f.a * p + f.b * q), mul_pos hd this]
  exact pos_of_mul_pos_right hpos ha.le

/-- **Theorem 1 for positive definite forms:** properly equivalent forms have the same cycle. -/
theorem cycleSet_eq_of_properEquiv_pos {f g : BinForm} (ha : 0 < f.a) (hd : 0 < f.det)
    (h : ProperEquiv f g) : cycleSet f = cycleSet g := by
  have hdg : 0 < g.det := h.det_eq ▸ hd
  have hag := pos_of_properEquiv ha hd h
  obtain ⟨x, hx, hxr⟩ := exists_reduced_mem_cycleSet ha hd
  obtain ⟨y, hy, hyr⟩ := exists_reduced_mem_cycleSet hag hdg
  have hf := not_isSquare_neg_of_pos hd
  have hg := not_isSquare_neg_of_pos hdg
  have hxy : x = y := reduced_pos_unique hxr hyr
    ((properEquiv_of_mem_cycleSet hf hx).symm.trans (h.trans (properEquiv_of_mem_cycleSet hg hy)))
  rw [← cycleSet_eq_of_mem hf hx, ← cycleSet_eq_of_mem hg hy, hxy]

/-- **Theorem 1 for definite forms:** properly equivalent forms have the same cycle. -/
theorem cycleSet_eq_of_properEquiv_def {f g : BinForm} (hd : 0 < f.det) (h : ProperEquiv f g) :
    cycleSet f = cycleSet g := by
  have ha : f.a ≠ 0 := by
    rintro h0; simp only [BinForm.det, h0, zero_mul, zero_sub] at hd; nlinarith [sq_nonneg f.b]
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have e := cycleSet_eq_of_properEquiv_pos (f := negForm f) (g := negForm g)
      (by simp [negForm]; exact hneg) (by rw [negForm_det]; exact hd) (properEquiv_negForm h)
    rw [cycleSet_negForm, cycleSet_negForm] at e
    exact (Set.image_injective.2 negForm_injective) e
  · exact cycleSet_eq_of_properEquiv_pos hpos hd h

theorem ultimatelyPeriodic_def {f : BinForm} (hd : 0 < f.det) : UltimatelyPeriodic (sequenceOf f) := by
  have ha : f.a ≠ 0 := by
    rintro h0; simp only [BinForm.det, h0, zero_mul, zero_sub] at hd; nlinarith [sq_nonneg f.b]
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · exact ultimatelyPeriodic_of_negForm
      (definite_cycle (negForm f) (by simp [negForm]; exact hneg) (by rw [negForm_det]; exact hd)).1
  · exact (definite_cycle f hpos hd).1

/-! ### Indefinite forms: the reduced region -/

/-- **Reduced indefinite forms in integer form**: with $T = \lfloor\sqrt{-d}\rfloor$ (`sqrtBound d`), the form
$a^{b}c$ satisfies $0 < b \le T$, $T + 1 \le b + |a|$ and $T + 1 \le b + |c|$. For a form of determinant $d$ with $-d$
not a square this is the book's (12) (`redT_iff_isReducedIndef`). -/
def RedT (T : ℤ) (h : BinForm) : Prop :=
  0 < h.b ∧ h.b ≤ T ∧ T + 1 ≤ h.b + |h.a| ∧ T + 1 ≤ h.b + |h.c|

theorem sqrtBound_facts {d : ℤ} (hd : d < 0) (hsq : ¬ IsSquare (-d)) :
    ((sqrtBound d : ℕ) : ℤ) ^ 2 + d < 0 ∧ 0 < ((sqrtBound d : ℕ) + 1 : ℤ) ^ 2 + d := by
  have h1 := (sqrtBound_iff hd (sqrtBound d)).2 le_rfl
  have h2 : ¬ (((sqrtBound d + 1 : ℕ) : ℤ) ^ 2 + d < 0) := fun h => by
    have := (sqrtBound_iff hd _).1 h; omega
  push_cast at h2
  refine ⟨h1, ?_⟩
  rcases lt_or_eq_of_le (not_lt.1 h2) with h | h
  · exact h
  · exact absurd ⟨(sqrtBound d : ℤ) + 1, by linear_combination h⟩ hsq

theorem stepB_exists_facts {d T B0 A B : ℤ} (hT1 : T ^ 2 + d < 0) (hA : A ≠ 0) (hdvd : A ∣ B0 + B)
    (hB : B ^ 2 + d < 0) (hmax : ∀ y, A ∣ B0 + y → y ^ 2 + d < 0 → y ≤ B)
    (hT2 : 0 < (T + 1) ^ 2 + d) : |B| ≤ T ∧ T + 1 ≤ B + |A| := by
  have hAabs : 0 < |A| := abs_pos.2 hA
  have hBT : |B| ≤ T := by
    by_contra hc
    push Not at hc
    nlinarith [sq_abs B, abs_nonneg B]
  refine ⟨hBT, ?_⟩
  by_contra hc
  push Not at hc
  have hdv : A ∣ B0 + (B + |A|) := by
    have : B0 + (B + |A|) = (B0 + B) + |A| := by ring
    rw [this]
    exact dvd_add hdvd ((dvd_abs A A).2 dvd_rfl)
  have hlo : -T ≤ B := by have := neg_abs_le B; linarith
  have : (B + |A|) ^ 2 + d < 0 := by nlinarith
  have := hmax _ hdv this
  linarith

theorem two_natAbs_le {A B : ℤ} (hA : A ≠ 0) (e1 : B.natAbs ≤ (B + A).natAbs) (e2 : B.natAbs ≤ (B - A).natAbs) :
    2 * B.natAbs ≤ A.natAbs := by
  omega

theorem step_cases {d T B0 A B C : ℤ} (hT0 : 0 ≤ T) (hT1 : T ^ 2 + d < 0) (hT2 : 0 < (T + 1) ^ 2 + d)
    (hsq : ¬ IsSquare (-d)) (hA : A ≠ 0) (hS : IsStepB d B0 A B) (hC : C * A = B ^ 2 + d) :
    RedT T ⟨A, B, C⟩ ∨ |C| < |A| := by
  obtain ⟨hdvd, h1, h2⟩ := hS
  have hAabs : 0 < |A| := abs_pos.2 hA
  have hCA : |C| * |A| = |B ^ 2 + d| := by rw [← abs_mul, hC]
  by_cases hex : ∃ y, A ∣ B0 + y ∧ y ^ 2 + d < 0
  · obtain ⟨hB, hmax⟩ := h1 hex
    obtain ⟨hBT, hBA⟩ := stepB_exists_facts hT1 hA hdvd hB hmax hT2
    by_cases hlt : |C| < |A|
    · exact Or.inr hlt
    · left
      push Not at hlt
      rw [abs_of_neg hB] at hCA
      refine ⟨?_, (show B ≤ T by linarith [le_abs_self B]), (show T + 1 ≤ B + |A| from hBA),
        (show T + 1 ≤ B + |C| by linarith)⟩
      show 0 < B
      by_contra hb
      push Not at hb
      have hA1 : T + 1 ≤ |A| := by linarith
      have : (T + 1) ^ 2 ≤ |C| * |A| := by nlinarith
      nlinarith [sq_nonneg B]
  · right
    have hmin := h2 hex
    have e1 := (hmin (B + A) (by
      have : B0 + (B + A) = (B0 + B) + A := by ring
      rw [this]; exact dvd_add hdvd dvd_rfl)).1
    have e2 := (hmin (B - A) (by
      have : B0 + (B - A) = (B0 + B) - A := by ring
      rw [this]; exact dvd_sub hdvd dvd_rfl)).1
    have hB2n : 2 * B.natAbs ≤ A.natAbs := two_natAbs_le hA e1 e2
    have hB2 : 2 * |B| ≤ |A| := by
      rw [← Int.natCast_natAbs, ← Int.natCast_natAbs]
      exact_mod_cast hB2n
    have hpos : 0 < B ^ 2 + d := by
      rcases lt_trichotomy (B ^ 2 + d) 0 with h | h | h
      · exact absurd ⟨B, hdvd, h⟩ hex
      · exact absurd ⟨B, by linear_combination (-1 : ℤ) * h⟩ hsq
      · exact h
    rw [abs_of_pos hpos] at hCA
    have : 4 * (|C| * |A|) < |A| * |A| := by nlinarith [sq_abs B, abs_nonneg B]
    nlinarith [abs_nonneg C]

theorem redT_step {d T a b c b' c' : ℤ} (hT0 : 0 ≤ T) (hT1 : T ^ 2 + d < 0) (hT2 : 0 < (T + 1) ^ 2 + d)
    (hc0 : c ≠ 0) (hca : c * a = b ^ 2 + d) (hR : RedT T ⟨a, b, c⟩) (hS : IsStepB d b c b')
    (hc' : c' * c = b' ^ 2 + d) : RedT T ⟨c, b', c'⟩ := by
  obtain ⟨hb0, hbT, hab, hcb⟩ := hR
  simp only at hb0 hbT hab hcb
  have hb2 : b ^ 2 + d < 0 := by nlinarith
  have hex : ∃ y, c ∣ b + y ∧ y ^ 2 + d < 0 := ⟨-b, by simp, by simpa using hb2⟩
  obtain ⟨hdvd, h1, -⟩ := hS
  obtain ⟨hB', hmax⟩ := h1 hex
  have hge : -b ≤ b' := hmax (-b) (by simp) (by simpa using hb2)
  obtain ⟨hBT, hBA⟩ := stepB_exists_facts hT1 hc0 hdvd hB' hmax hT2
  have hcabs : 0 < |c| := abs_pos.2 hc0
  have hac : |c| * |a| = -(b ^ 2 + d) := by rw [← abs_mul, hca, abs_of_neg hb2]
  have hcT : |c| ≤ T + b := by
    by_contra hh
    push Not at hh
    have : (T + 1 + b) * (T + 1 - b) ≤ |c| * |a| := by
      apply mul_le_mul (by linarith) (by linarith) (by linarith) (abs_nonneg c)
    nlinarith
  have hbb : |c| ≤ b + b' := by
    have hpos : 0 < b + b' := by
      rcases lt_or_eq_of_le hge with h | h
      · linarith
      · exfalso; rw [← h] at hBA; linarith
    exact Int.le_of_dvd hpos ((abs_dvd c _).2 hdvd)
  have hc'c : |c'| * |c| = -(b' ^ 2 + d) := by rw [← abs_mul, hc', abs_of_neg hB']
  refine ⟨(show 0 < b' by linarith), (show b' ≤ T by linarith [le_abs_self b']),
    (show T + 1 ≤ b' + |c| from hBA), (show T + 1 ≤ b' + |c'| from ?_)⟩
  by_contra hh
  push Not at hh
  have hb'T : b' ≤ T := by linarith [le_abs_self b']
  have : |c'| * |c| ≤ (T - b') * (T + b') := by
    apply mul_le_mul (by linarith) (by linarith) (abs_nonneg c) (by linarith)
  nlinarith

/-- **Reduced forms stay reduced** (Ch. 15, §3.3, p. 359: the forms of the cycles satisfy (12)). -/
theorem redT_formAt_succ {d T : ℤ} (hT0 : 0 ≤ T) (hT1 : T ^ 2 + d < 0) (hT2 : 0 < (T + 1) ^ 2 + d)
    (hsq : ¬ IsSquare (-d)) {q : ℤ × ℤ} (hI : StepInv d q) (hR : RedT T (formAt d q)) :
    RedT T (formAt d (stepPair d q)) := by
  have hc0 := hI.fst_ne hsq
  exact redT_step hT0 hT1 hT2 hc0 (stepPair_fst_mul hI.2) hR
    (by rw [stepPair_snd]; exact isStepB_stepB hc0) (stepPair_fst_mul (hI.step hsq).2)

theorem formAt_step_cases {d T : ℤ} (hT0 : 0 ≤ T) (hT1 : T ^ 2 + d < 0) (hT2 : 0 < (T + 1) ^ 2 + d)
    (hsq : ¬ IsSquare (-d)) {q : ℤ × ℤ} (hI : StepInv d q) :
    RedT T (formAt d (stepPair d q)) ∨ |(stepPair d (stepPair d q)).1| < |(stepPair d q).1| := by
  have hc0 := hI.fst_ne hsq
  exact step_cases hT0 hT1 hT2 hsq hc0 (by rw [stepPair_snd]; exact isStepB_stepB hc0)
    (stepPair_fst_mul (hI.step hsq).2)

/-- **The sequence reaches the reduced region**: $|a_{i+1}| < |a_i|$ as long as the form is not reduced. -/
theorem exists_redT {d T : ℤ} (hT0 : 0 ≤ T) (hT1 : T ^ 2 + d < 0) (hT2 : 0 < (T + 1) ^ 2 + d)
    (hsq : ¬ IsSquare (-d)) {p : ℤ × ℤ} (hI : StepInv d p) :
    ∃ N, ∀ n ≥ N, RedT T (formAt d (pairSeq d p n)) := by
  have key : ∀ m : ℕ, ∀ n, ((pairSeq d p (n + 1)).1).natAbs ≤ m →
      ∃ N, RedT T (formAt d (pairSeq d p N)) := by
    intro m
    induction m with
    | zero =>
      intro n hn
      have := (hI.pairSeq hsq (n + 1)).1
      omega
    | succ m ih =>
      intro n hn
      rcases formAt_step_cases hT0 hT1 hT2 hsq (hI.pairSeq hsq n) with h | h
      · exact ⟨n + 1, by rw [pairSeq_succ]; exact h⟩
      · apply ih (n + 1)
        rw [pairSeq_succ, pairSeq_succ]
        rw [pairSeq_succ] at hn
        rw [← Int.natCast_natAbs, ← Int.natCast_natAbs] at h
        omega
  obtain ⟨N, hN⟩ := key _ 0 le_rfl
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => exact hN
  | succ k ih =>
    rw [← add_assoc, pairSeq_succ]
    exact redT_formAt_succ hT0 hT1 hT2 hsq (hI.pairSeq hsq _) (ih (by omega))

/-- **Part (a) of Theorem 1 for indefinite forms**: the pairs $(a_n, b_n)$ of the reduced region lie in a finite
set, so the sequence is ultimately periodic. -/
theorem ultimatelyPeriodic_indef {f : BinForm} (hd : f.det < 0) (hsq : ¬ IsSquare (-f.det)) :
    UltimatelyPeriodic (sequenceOf f) := by
  set d := f.det with hd_def
  obtain ⟨hT1, hT2⟩ := sqrtBound_facts hd hsq
  set T : ℤ := (sqrtBound d : ℤ) with hT
  have hT0 : 0 ≤ T := by positivity
  have hI := BinForm.stepInv hsq
  obtain ⟨N, hN⟩ := exists_redT hT0 hT1 hT2 hsq hI
  set t : Set (ℤ × ℤ) := ↑(Finset.Icc d (-d) ×ˢ Finset.Icc (1 : ℤ) T) with ht
  have hmem : ∀ n, pairSeq d (f.a, f.b) (N + n) ∈ t := by
    intro n
    have hR := hN (N + n) (by omega)
    have hIn := hI.pairSeq hsq (N + n)
    obtain ⟨hb0, hbT, hab, hcb⟩ := hR
    simp only [formAt] at hb0 hbT hab hcb
    have hmul := stepPair_fst_mul hIn.2
    generalize pairSeq d (f.a, f.b) (N + n) = q at hb0 hbT hab hcb hmul hIn ⊢
    generalize (stepPair d q).1 = c at hcb hmul
    have hb2 : q.2 ^ 2 + d < 0 := by nlinarith
    have hac : |c| * |q.1| = -(q.2 ^ 2 + d) := by rw [← abs_mul, hmul, abs_of_neg hb2]
    have hc1 : 1 ≤ |c| := by linarith
    have : |q.1| ≤ -d := by nlinarith [abs_nonneg q.1, sq_nonneg q.2]
    have h1 := neg_abs_le q.1
    have h2 := le_abs_self q.1
    simp only [ht, Finset.coe_product, Set.mem_prod, Finset.coe_Icc, Set.mem_Icc]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, hbT⟩⟩
  obtain ⟨i, j, hij, he⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun n => pairSeq d (f.a, f.b) (N + n)) hmem (Finset.finite_toSet _)
  refine ⟨N + i, j - i, by omega, ?_⟩
  have hper : pairSeq d (f.a, f.b) (N + i + (j - i)) = pairSeq d (f.a, f.b) (N + i) := by
    rw [show N + i + (j - i) = N + j by omega]; exact he.symm
  exact periodic_of_pairSeq hper

/-- **`RedT` is the book's (12)** for a form of determinant $d < 0$ with $-d$ not a square. -/
theorem redT_iff_isReducedIndef {h : BinForm} (hd : h.det < 0) (hsq : ¬ IsSquare (-h.det)) :
    RedT (sqrtBound h.det : ℤ) h ↔ IsReducedIndef h.a h.b h.c := by
  obtain ⟨hT1, hT2⟩ := sqrtBound_facts hd hsq
  set T : ℤ := (sqrtBound h.det : ℤ)
  have hT0 : 0 ≤ T := by positivity
  have hD : h.b ^ 2 - h.a * h.c = -h.det := by simp only [BinForm.det]; ring
  unfold RedT IsReducedIndef
  rw [hD]
  have ha := abs_nonneg h.a
  have hc := abs_nonneg h.c
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_, ?_, ?_⟩
    · by_contra hc'; push Not at hc'; nlinarith
    · by_contra hc'; push Not at hc'; nlinarith
    · by_contra hc'; push Not at hc'; nlinarith

/-- **The forms of the cycle of an indefinite form satisfy (12)** (Ch. 15, §3.3, p. 359: "the forms of the cycles
of Theorem 1 are precisely those with (12)"; this is the inclusion of the cycles in the set of forms (12)). -/
@[kb "conwaysloane1999" "Ch. 15, §3.3, (12), p. 359"]
theorem cycleSet_isReducedIndef {f : BinForm} (hd : f.det < 0) (hsq : ¬ IsSquare (-f.det)) :
    ∀ x ∈ cycleSet f, IsReducedIndef x.a x.b x.c := by
  intro x hx
  obtain ⟨hT1, hT2⟩ := sqrtBound_facts hd hsq
  obtain ⟨N, hN⟩ := exists_redT (by positivity) hT1 hT2 hsq (BinForm.stepInv hsq)
  obtain ⟨n, hn, rfl⟩ := hx N
  have hdet := (properEquiv_sequenceOf hsq n).2
  rw [← redT_iff_isReducedIndef (hdet ▸ hd) (hdet ▸ hsq), hdet]
  exact hN n hn

/-! ### Indefinite forms: lattice bases and the two linear factors -/

/-- The value $f(u) = au_0^2 + 2bu_0u_1 + cu_1^2$ of $f = a^{b}c$ at $u = (u_0, u_1) \in \mathbb{Z}^2$. -/
def qf (f : BinForm) (u : ℤ × ℤ) : ℤ := f.a * u.1 ^ 2 + 2 * f.b * u.1 * u.2 + f.c * u.2 ^ 2

/-- The bilinear form $f(u, v) = au_0v_0 + b(u_0v_1 + u_1v_0) + cu_1v_1$ of $f = a^{b}c$. -/
def bf (f : BinForm) (u v : ℤ × ℤ) : ℤ := f.a * u.1 * v.1 + f.b * (u.1 * v.2 + u.2 * v.1) + f.c * u.2 * v.2

/-- The determinant $u_0v_1 - u_1v_0$ of the pair $(u, v)$. -/
def det2 (u v : ℤ × ℤ) : ℤ := u.1 * v.2 - u.2 * v.1

/-- The pair $(u, v)$ is a properly oriented basis of $\mathbb{Z}^2$ in which $f$ has the matrix of $h$. -/
def Rep (f : BinForm) (u v : ℤ × ℤ) (h : BinForm) : Prop :=
  det2 u v = 1 ∧ h.a = qf f u ∧ h.b = bf f u v ∧ h.c = qf f v

theorem rep_of_properEquiv {f g : BinForm} (h : ProperEquiv f g) : ∃ u v, Rep f u v g := by
  obtain ⟨p, q, r, s, hdet, ha, hc, hb⟩ := equiv_entries h
  exact ⟨(p, q), (r, s), by simp [det2]; linarith, by simp [qf, ha], by simp [bf, hb], by simp [qf, hc]⟩

theorem rep_self (f : BinForm) : Rep f (1, 0) (0, 1) f := by
  simp [Rep, det2, qf, bf]

theorem rep_eq {f h h' : BinForm} {u v : ℤ × ℤ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (h1 : Rep f u v h)
    (h2 : Rep f (ε * u.1, ε * u.2) (ε * v.1, ε * v.2) h') : h' = h := by
  obtain ⟨-, ha, hb, hc⟩ := h1
  obtain ⟨-, ha', hb', hc'⟩ := h2
  have e : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨a, b, c⟩ := h
  obtain ⟨a', b', c'⟩ := h'
  simp only [qf, bf] at ha hb hc ha' hb' hc'
  simp only [BinForm.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [ha', ha]; linear_combination (f.a * u.1 ^ 2 + 2 * f.b * u.1 * u.2 + f.c * u.2 ^ 2) * e
  · rw [hb', hb]
    linear_combination (f.a * u.1 * v.1 + f.b * (u.1 * v.2 + u.2 * v.1) + f.c * u.2 * v.2) * e
  · rw [hc', hc]; linear_combination (f.a * v.1 ^ 2 + 2 * f.b * v.1 * v.2 + f.c * v.2 ^ 2) * e

/-- The pairs of consecutive basis vectors $(e_n, e_{n+1})$ along the sequence (5) of the form with starting pair
`p`, started at $(e_0, e_1) = (u, v)$: $e_{n+2} = -e_n + k_n e_{n+1}$, $k_n = (b_n + b_{n+1})/a_{n+1}$. -/
def vecSeq (d : ℤ) (p : ℤ × ℤ) (u v : ℤ × ℤ) : ℕ → (ℤ × ℤ) × (ℤ × ℤ)
  | 0 => (u, v)
  | n + 1 =>
    let w := vecSeq d p u v n
    let q := pairSeq d p n
    let k := (q.2 + (stepPair d q).2) / (stepPair d q).1
    (w.2, (-w.1.1 + k * w.2.1, -w.1.2 + k * w.2.2))

theorem vecSeq_succ_fst (d : ℤ) (p u v : ℤ × ℤ) (n : ℕ) :
    (vecSeq d p u v (n + 1)).1 = (vecSeq d p u v n).2 := rfl

theorem rep_vecSeq {f : BinForm} {d : ℤ} {p u v : ℤ × ℤ} (hsq : ¬ IsSquare (-d)) (hI : StepInv d p)
    (h0 : Rep f u v (formAt d p)) (n : ℕ) :
    Rep f (vecSeq d p u v n).1 (vecSeq d p u v n).2 (formAt d (pairSeq d p n)) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    have hq := hI.pairSeq hsq n
    rw [pairSeq_succ]
    simp only [vecSeq]
    generalize vecSeq d p u v n = w at ih ⊢
    generalize pairSeq d p n = q at ih hq ⊢
    obtain ⟨hdet, ha, hb, hc⟩ := ih
    simp only [formAt] at ha hb hc ⊢
    have hq' := hq.step hsq
    have hne := hq.fst_ne hsq
    obtain ⟨k, hk⟩ : ∃ k, k = (q.2 + (stepPair d q).2) / (stepPair d q).1 := ⟨_, rfl⟩
    rw [← hk]
    have hkm : k * (stepPair d q).1 = q.2 + (stepPair d q).2 := by
      rw [hk]; exact Int.ediv_mul_cancel (hq.dvd_sum hsq)
    have m1 := stepPair_fst_mul hq.2
    have m2 := stepPair_fst_mul hq'.2
    generalize stepPair d (stepPair d q) = q'' at m2 ⊢
    generalize stepPair d q = q' at hkm m1 m2 hne hc ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [det2] at hdet ⊢; linear_combination hdet
    · exact hc
    · simp only [bf, qf] at hb hc ⊢
      linear_combination -hkm - hb + k * hc
    · simp only [qf, bf] at ha hb hc ⊢
      apply mul_right_cancel₀ hne
      linear_combination m2 - m1 + q'.1 * ha - 2 * k * q'.1 * hb + k ^ 2 * q'.1 * hc +
        (q.2 - q'.2 - k * q'.1) * hkm

/-! ### Indefinite forms: the box argument -/

/-- The linear factor $\ell_1(u) = au_0 + (b - s)u_1$ of $a \cdot f$, $f = a^{b}c$, where $s = \sqrt{-d}$. -/
noncomputable def l1 (f : BinForm) (s : ℝ) (u : ℤ × ℤ) : ℝ := (f.a : ℝ) * u.1 + ((f.b : ℝ) - s) * u.2

/-- The linear factor $\ell_2(u) = au_0 + (b + s)u_1$ of $a \cdot f$, $f = a^{b}c$, where $s = \sqrt{-d}$. -/
noncomputable def l2 (f : BinForm) (s : ℝ) (u : ℤ × ℤ) : ℝ := (f.a : ℝ) * u.1 + ((f.b : ℝ) + s) * u.2

/-- The data for the box argument: $f = a^{b}c$ anisotropic with $a \ne 0$, $s = \sqrt{b^2 - ac}$ and
$T = \lfloor s \rfloor$, $T < s < T + 1$. -/
structure Setup (f : BinForm) (s : ℝ) (T : ℤ) : Prop where
  /-- The entry $a$ of $f$ is nonzero. -/
  a_ne : f.a ≠ 0
  /-- $s^2 = b^2 - ac = -d$. -/
  sq : s ^ 2 = (f.b : ℝ) ^ 2 - f.a * f.c
  /-- $T \ge 0$. -/
  T_nonneg : 0 ≤ T
  /-- $T < s$. -/
  T_lt : (T : ℝ) < s
  /-- $s < T + 1$. -/
  lt_T : s < T + 1
  /-- $f$ has no nonzero integral zero. -/
  aniso : ∀ u : ℤ × ℤ, qf f u = 0 → u = 0

/-- A pair $(u, v)$ with $|\ell_1(v)| < |\ell_1(u)|$, $|\ell_2(u)| < |\ell_2(v)|$ and the ratios
$\ell_1(v)/\ell_1(u)$, $\ell_2(v)/\ell_2(u)$ of opposite signs. -/
def Good (f : BinForm) (s : ℝ) (u v : ℤ × ℤ) : Prop :=
  |l1 f s v| < |l1 f s u| ∧ |l2 f s u| < |l2 f s v| ∧ l1 f s u * l1 f s v * (l2 f s u * l2 f s v) < 0

/-- The negative $-u$ of a lattice vector. -/
def vneg (u : ℤ × ℤ) : ℤ × ℤ := (-u.1, -u.2)

section Box

variable {f : BinForm} {s : ℝ} {T : ℤ}

theorem Setup.l1_mul_l2 (S : Setup f s T) (u : ℤ × ℤ) :
    l1 f s u * l2 f s u = f.a * (qf f u : ℝ) := by
  simp only [l1, l2, qf]; push_cast; linear_combination (-(u.2 : ℝ) ^ 2) * S.sq

theorem Setup.l1_l2 (S : Setup f s T) (u v : ℤ × ℤ) :
    l1 f s u * l2 f s v = f.a * ((bf f u v : ℝ) + s * det2 u v) := by
  simp only [l1, l2, bf, det2]; push_cast; linear_combination (-(u.2 : ℝ) * v.2) * S.sq

theorem Setup.l1_l2' (S : Setup f s T) (u v : ℤ × ℤ) :
    l1 f s v * l2 f s u = f.a * ((bf f u v : ℝ) - s * det2 u v) := by
  simp only [l1, l2, bf, det2]; push_cast; linear_combination (-(u.2 : ℝ) * v.2) * S.sq

theorem Setup.l1_eq_zero (S : Setup f s T) {w : ℤ × ℤ} (h : l1 f s w = 0) : w = 0 := by
  apply S.aniso
  have e := S.l1_mul_l2 w
  rw [h, zero_mul] at e
  have ha : (f.a : ℝ) ≠ 0 := by exact_mod_cast S.a_ne
  exact_mod_cast (mul_eq_zero.1 e.symm).resolve_left ha

theorem l1_vneg (u : ℤ × ℤ) : l1 f s (vneg u) = -l1 f s u := by simp only [l1, vneg]; push_cast; ring

theorem l2_vneg (u : ℤ × ℤ) : l2 f s (vneg u) = -l2 f s u := by simp only [l2, vneg]; push_cast; ring

theorem Good.vneg {u v : ℤ × ℤ} (h : Good f s u v) : Good f s (vneg u) (vneg v) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [l1_vneg, l1_vneg, abs_neg, abs_neg]; exact h1
  · rw [l2_vneg, l2_vneg, abs_neg, abs_neg]; exact h2
  · rw [l1_vneg, l1_vneg, l2_vneg, l2_vneg]; linarith [h3, show
      -l1 f s u * -l1 f s v * (-l2 f s u * -l2 f s v) = l1 f s u * l1 f s v * (l2 f s u * l2 f s v) by ring]

theorem Good.ne_zero {u v : ℤ × ℤ} (h : Good f s u v) :
    l1 f s u ≠ 0 ∧ l1 f s v ≠ 0 ∧ l2 f s u ≠ 0 ∧ l2 f s v ≠ 0 := by
  have h3 := h.2.2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h0 <;> rw [h0] at h3 <;> simp at h3

/-- **A basis of a reduced form is good.** -/
theorem Setup.good_of_rep (S : Setup f s T) {u v : ℤ × ℤ} {h : BinForm} (hr : Rep f u v h)
    (hR : RedT T h) : Good f s u v := by
  obtain ⟨hdet, ha, hb, hc⟩ := hr
  obtain ⟨hb0, hbT, hab, hcb⟩ := hR
  have e1 := S.l1_mul_l2 u
  have e2 := S.l1_mul_l2 v
  have e3 := S.l1_l2 u v
  have e4 := S.l1_l2' u v
  rw [← ha] at e1
  rw [← hc] at e2
  rw [← hb, hdet] at e3 e4
  push_cast at e3 e4
  have hb0' : (0 : ℝ) < h.b := by exact_mod_cast hb0
  have hbT' : (h.b : ℝ) ≤ T := by exact_mod_cast hbT
  have hab' : (T : ℝ) + 1 ≤ h.b + |(h.a : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hab
  have hcb' : (T : ℝ) + 1 ≤ h.b + |(h.c : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hcb
  have hsb : 0 < s - h.b := by linarith [S.T_lt]
  have h1 : s - h.b < |(h.a : ℝ)| := by linarith [S.lt_T]
  have h2 : s - h.b < |(h.c : ℝ)| := by linarith [S.lt_T]
  have hA : 0 < |(f.a : ℝ)| := abs_pos.2 (by exact_mod_cast S.a_ne)
  have a1 : |l1 f s u| * |l2 f s u| = |(f.a : ℝ)| * |(h.a : ℝ)| := by rw [← abs_mul, e1, abs_mul]
  have a2 : |l1 f s v| * |l2 f s v| = |(f.a : ℝ)| * |(h.c : ℝ)| := by rw [← abs_mul, e2, abs_mul]
  have a4 : |l1 f s v| * |l2 f s u| = |(f.a : ℝ)| * (s - h.b) := by
    rw [← abs_mul, e4, abs_mul, mul_one, abs_of_neg (by linarith : (h.b : ℝ) - s < 0)]; ring
  refine ⟨?_, ?_, ?_⟩
  · apply lt_of_mul_lt_mul_right _ (abs_nonneg (l2 f s u))
    rw [a4, a1]
    exact mul_lt_mul_of_pos_left h1 hA
  · apply lt_of_mul_lt_mul_left _ (abs_nonneg (l1 f s v))
    rw [a4, a2]
    exact mul_lt_mul_of_pos_left h2 hA
  · have : l1 f s u * l1 f s v * (l2 f s u * l2 f s v) = (l1 f s u * l2 f s v) * (l1 f s v * l2 f s u) := by
      ring
    rw [this, e3, e4, mul_one]
    have hA2 : 0 < (f.a : ℝ) ^ 2 := by
      have : (f.a : ℝ) ≠ 0 := by exact_mod_cast S.a_ne
      positivity
    have : (f.a : ℝ) * (h.b + s) * ((f.a : ℝ) * (h.b - s)) = (f.a : ℝ) ^ 2 * ((h.b + s) * (h.b - s)) := by ring
    rw [this]
    exact mul_neg_of_pos_of_neg hA2 (mul_neg_of_pos_of_neg (by linarith) (by linarith))

/-- **Growth of $|\ell_2|$ along good bases of reduced forms**: $(T + 1)|\ell_2(u)| \le s|\ell_2(v)|$. -/
theorem Setup.growth (S : Setup f s T) {u v : ℤ × ℤ} {h : BinForm} (hr : Rep f u v h) (hR : RedT T h) :
    ((T : ℝ) + 1) * |l2 f s u| ≤ s * |l2 f s v| := by
  have hG := S.good_of_rep hr hR
  obtain ⟨hdet, -, hb, hc⟩ := hr
  obtain ⟨hb0, hbT, -, hcb⟩ := hR
  have e2 := S.l1_mul_l2 v
  have e4 := S.l1_l2' u v
  rw [← hc] at e2
  rw [← hb, hdet] at e4
  push_cast at e4
  have hb0' : (0 : ℝ) < h.b := by exact_mod_cast hb0
  have hcb' : (T : ℝ) + 1 ≤ h.b + |(h.c : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hcb
  have hsb : 0 < s - h.b := by
    have : (h.b : ℝ) ≤ T := by exact_mod_cast hbT
    linarith [S.T_lt]
  have hA : 0 < |(f.a : ℝ)| := abs_pos.2 (by exact_mod_cast S.a_ne)
  have a2 : |l1 f s v| * |l2 f s v| = |(f.a : ℝ)| * |(h.c : ℝ)| := by rw [← abs_mul, e2, abs_mul]
  have a4 : |l1 f s v| * |l2 f s u| = |(f.a : ℝ)| * (s - h.b) := by
    rw [← abs_mul, e4, abs_mul, mul_one, abs_of_neg (by linarith : (h.b : ℝ) - s < 0)]; ring
  have hP : 0 < |l1 f s v| := abs_pos.2 hG.ne_zero.2.1
  have key : ((T : ℝ) + 1) * (s - h.b) ≤ s * |(h.c : ℝ)| := by nlinarith [S.lt_T, S.T_lt]
  apply le_of_mul_le_mul_left _ hP
  calc |l1 f s v| * (((T : ℝ) + 1) * |l2 f s u|) = ((T : ℝ) + 1) * (|l1 f s v| * |l2 f s u|) := by ring
    _ = |(f.a : ℝ)| * (((T : ℝ) + 1) * (s - h.b)) := by rw [a4]; ring
    _ ≤ |(f.a : ℝ)| * (s * |(h.c : ℝ)|) := mul_le_mul_of_nonneg_left key hA.le
    _ = |l1 f s v| * (s * |l2 f s v|) := by rw [mul_left_comm, ← a2]; ring

theorem int_cases_real (x : ℤ) : (x : ℝ) = 0 ∨ 1 ≤ (x : ℝ) ^ 2 := by
  rcases eq_or_ne x 0 with h | h
  · left; simp [h]
  · right
    have : 0 < x ^ 2 := by positivity
    have : 1 ≤ x ^ 2 := by omega
    exact_mod_cast this

theorem box_real {α β γ δ x y : ℝ} (hx : x = 0 ∨ 1 ≤ x ^ 2) (hy : y = 0 ∨ 1 ≤ y ^ 2)
    (hxy : x ≠ 0 ∨ y ≠ 0) (hs : α * β * (γ * δ) < 0) (h1 : (x * α + y * β) ^ 2 < α ^ 2)
    (h2 : (x * γ + y * δ) ^ 2 < δ ^ 2) : False := by
  rcases hx with rfl | hx
  · have hy' : 1 ≤ y ^ 2 := hy.resolve_left (hxy.resolve_left (by simp))
    nlinarith [mul_le_mul_of_nonneg_right hy' (sq_nonneg δ)]
  rcases hy with rfl | hy
  · nlinarith [mul_le_mul_of_nonneg_right hx (sq_nonneg α)]
  by_cases hab : 0 ≤ x * y * (α * β)
  · nlinarith [sq_nonneg (y * β), mul_le_mul_of_nonneg_right hx (sq_nonneg α)]
  · push Not at hab
    have hxy2 : 0 < x ^ 2 * y ^ 2 := mul_pos (by linarith) (by linarith)
    have hprod : (x * y * (α * β)) * (x * y * (γ * δ)) < 0 := by
      have : (x * y * (α * β)) * (x * y * (γ * δ)) = (x ^ 2 * y ^ 2) * (α * β * (γ * δ)) := by ring
      rw [this]; exact mul_neg_of_pos_of_neg hxy2 hs
    have hpos : 0 < x * y * (γ * δ) := by
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg_of_nonpos_of_nonpos hab.le hc]
    nlinarith [sq_nonneg (x * γ), mul_le_mul_of_nonneg_right hy (sq_nonneg δ)]

/-- **The box lemma**: for a good basis $(u, v)$ no nonzero lattice vector $w$ has both $|\ell_1(w)| < |\ell_1(u)|$
and $|\ell_2(w)| < |\ell_2(v)|$. -/
theorem Good.box {u v w : ℤ × ℤ} (hd : det2 u v = 1) (hG : Good f s u v) (hw : w ≠ 0)
    (h1 : |l1 f s w| < |l1 f s u|) (h2 : |l2 f s w| < |l2 f s v|) : False := by
  obtain ⟨x, hx⟩ : ∃ x, x = det2 w v := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = det2 u w := ⟨_, rfl⟩
  have ew1 : w.1 = x * u.1 + y * v.1 := by
    have : w.1 * det2 u v = x * u.1 + y * v.1 := by rw [hx, hy]; simp only [det2]; ring
    rwa [hd, mul_one] at this
  have ew2 : w.2 = x * u.2 + y * v.2 := by
    have : w.2 * det2 u v = x * u.2 + y * v.2 := by rw [hx, hy]; simp only [det2]; ring
    rwa [hd, mul_one] at this
  have c1 : l1 f s w = x * l1 f s u + y * l1 f s v := by
    simp only [l1]; rw [ew1, ew2]; push_cast; ring
  have c2 : l2 f s w = x * l2 f s u + y * l2 f s v := by
    simp only [l2]; rw [ew1, ew2]; push_cast; ring
  have hxy : (x : ℝ) ≠ 0 ∨ (y : ℝ) ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨h0, h0'⟩ := hc
    have hx0 : x = 0 := by exact_mod_cast h0
    have hy0 : y = 0 := by exact_mod_cast h0'
    apply hw
    rw [hx0, hy0] at ew1 ew2
    simp only [zero_mul, add_zero] at ew1 ew2
    exact Prod.ext ew1 ew2
  rw [c1] at h1
  rw [c2] at h2
  exact box_real (int_cases_real x) (int_cases_real y) hxy hG.2.2 (sq_lt_sq.2 h1) (sq_lt_sq.2 h2)

theorem unique_real {α β γ δ z : ℝ} (hz : z = 0 ∨ 1 ≤ z ∨ z ≤ -1) (hα : α ≠ 0) (hγ : γ ≠ 0)
    (hβ : β ^ 2 < α ^ 2) (hs : α * β * (γ * δ) < 0)
    (h1 : (z * α + β) ^ 2 < α ^ 2) (h3 : α * (z * α + β) * (γ * (z * γ + δ)) < 0) : z = 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, β = r * α := ⟨β / α, by field_simp⟩
  obtain ⟨t, rfl⟩ : ∃ t, δ = t * γ := ⟨δ / γ, by field_simp⟩
  have hA : 0 < α ^ 2 := by positivity
  have hG : 0 < α ^ 2 * γ ^ 2 := by positivity
  have k1 : r ^ 2 < 1 := by
    have : r ^ 2 * α ^ 2 < 1 * α ^ 2 := by linarith [show (r * α) ^ 2 = r ^ 2 * α ^ 2 by ring]
    exact lt_of_mul_lt_mul_right this hA.le
  have k2 : r * t < 0 := by
    have : α * (r * α) * (γ * (t * γ)) = (α ^ 2 * γ ^ 2) * (r * t) := by ring
    rw [this] at hs
    exact neg_of_mul_neg_right hs hG.le
  have k3 : (z + r) ^ 2 < 1 := by
    have : (z + r) ^ 2 * α ^ 2 < 1 * α ^ 2 := by
      linarith [show (z * α + r * α) ^ 2 = (z + r) ^ 2 * α ^ 2 by ring]
    exact lt_of_mul_lt_mul_right this hA.le
  have k4 : (z + r) * (z + t) < 0 := by
    have : α * (z * α + r * α) * (γ * (z * γ + t * γ)) = (α ^ 2 * γ ^ 2) * ((z + r) * (z + t)) := by ring
    rw [this] at h3
    exact neg_of_mul_neg_right h3 hG.le
  have hr1 : -1 < r ∧ r < 1 := by constructor <;> nlinarith
  rcases hz with h | h | h
  · exact h
  · exfalso
    have hzr : 0 < z + r := by linarith
    have hzt : z + t < 0 := neg_of_mul_neg_right k4 hzr.le
    have ht : t < 0 := by linarith
    have hr : 0 < r := by
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg_of_nonpos_of_nonpos hc ht.le]
    nlinarith
  · exfalso
    have hzr : z + r < 0 := by linarith
    have hzt : 0 < z + t := by
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg_of_nonpos_of_nonpos hzr.le hc]
    have ht : 0 < t := by linarith
    have hr : r < 0 := by
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg hc ht.le]
    nlinarith

theorem Good.unique_snd {u v v' : ℤ × ℤ} (hd : det2 u v = 1) (hd' : det2 u v' = 1)
    (hG : Good f s u v) (hG' : Good f s u v') : v' = v := by
  obtain ⟨x, hx⟩ : ∃ x, x = det2 v' v := ⟨_, rfl⟩
  have ev1 : v'.1 = x * u.1 + v.1 := by
    have : v'.1 * det2 u v = x * u.1 + det2 u v' * v.1 := by rw [hx]; simp only [det2]; ring
    rwa [hd, hd', mul_one, one_mul] at this
  have ev2 : v'.2 = x * u.2 + v.2 := by
    have : v'.2 * det2 u v = x * u.2 + det2 u v' * v.2 := by rw [hx]; simp only [det2]; ring
    rwa [hd, hd', mul_one, one_mul] at this
  have c1 : l1 f s v' = x * l1 f s u + l1 f s v := by
    simp only [l1]; rw [ev1, ev2]; push_cast; ring
  have c2 : l2 f s v' = x * l2 f s u + l2 f s v := by
    simp only [l2]; rw [ev1, ev2]; push_cast; ring
  obtain ⟨hα, -, hγ, -⟩ := hG.ne_zero
  have h1 := sq_lt_sq.2 hG'.1
  have h3 := hG'.2.2
  rw [c1] at h1
  rw [c1, c2] at h3
  have hz : (x : ℝ) = 0 ∨ 1 ≤ (x : ℝ) ∨ (x : ℝ) ≤ -1 := by
    rcases (show x = 0 ∨ 1 ≤ x ∨ x ≤ -1 by omega) with h | h | h
    · left; exact_mod_cast h
    · right; left; exact_mod_cast h
    · right; right; exact_mod_cast h
  have hx0 : (x : ℝ) = 0 := unique_real hz hα hγ (sq_lt_sq.2 hG.1) hG.2.2 h1 h3
  have hx0' : x = 0 := by exact_mod_cast hx0
  rw [hx0', zero_mul, zero_add] at ev1 ev2
  exact Prod.ext ev1 ev2

/-- **Uniqueness of good bases**: if $(u, v)$, $(u', v')$ are good with $|\ell_2(u)| \le |\ell_2(u')| <
|\ell_2(v)|$, then $(u', v') = \pm(u, v)$. -/
theorem Setup.unique (S : Setup f s T) {u v u' v' : ℤ × ℤ} (hd : det2 u v = 1) (hd' : det2 u' v' = 1)
    (hG : Good f s u v) (hG' : Good f s u' v')
    (h1 : |l2 f s u| ≤ |l2 f s u'|) (h2 : |l2 f s u'| < |l2 f s v|) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ u' = (ε * u.1, ε * u.2) ∧ v' = (ε * v.1, ε * v.2) := by
  have hu' : u' ≠ 0 := by rintro rfl; simp [det2] at hd'
  have hu : u ≠ 0 := by rintro rfl; simp [det2] at hd
  have s1 : |l1 f s u| ≤ |l1 f s u'| := by
    by_contra hc
    push Not at hc
    exact Good.box hd hG hu' hc h2
  have s2 : |l1 f s u'| ≤ |l1 f s u| := by
    by_contra hc
    push Not at hc
    exact Good.box hd' hG' hu hc (lt_of_le_of_lt h1 hG'.2.1)
  rcases abs_eq_abs.1 (le_antisymm s2 s1) with h | h
  · have hw := S.l1_eq_zero (w := (u'.1 - u.1, u'.2 - u.2)) (by
      simp only [l1] at h ⊢; push_cast; linarith)
    have huu : u' = u := by
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at hw
      exact Prod.ext (by linarith) (by linarith)
    subst huu
    refine ⟨1, Or.inl rfl, by simp, ?_⟩
    rw [Good.unique_snd hd hd' hG hG']
    simp
  · have hw := S.l1_eq_zero (w := (u'.1 + u.1, u'.2 + u.2)) (by
      simp only [l1] at h ⊢; push_cast; linarith)
    have huu : u' = vneg u := by
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at hw
      exact Prod.ext (by simp only [vneg]; linarith) (by simp only [vneg]; linarith)
    subst huu
    have hd'' : det2 u (vneg v') = 1 := by rw [← hd']; simp only [det2, vneg]; ring
    have hG'' : Good f s u (vneg v') := by
      have := hG'.vneg
      have e : vneg (vneg u) = u := by simp [vneg]
      rwa [e] at this
    have := Good.unique_snd hd hd'' hG hG''
    refine ⟨-1, Or.inr rfl, by simp [vneg], ?_⟩
    have e : v' = vneg (vneg v') := by simp [vneg]
    rw [e, this]
    simp [vneg]

/-- **Locating a reduced basis in a sequence of good bases**: if the consecutive pairs $(w_n, w_{n+1})$ are bases
of the reduced forms $H_n$, and $(u, v)$ is a basis of a reduced form $h$ with $|\ell_2(w_0)| \le |\ell_2(u)|$, then
$h = H_n$ for some $n$. -/
theorem Setup.locate (S : Setup f s T) {W : ℕ → (ℤ × ℤ) × (ℤ × ℤ)} {H : ℕ → BinForm}
    (hW : ∀ n, Rep f (W n).1 (W n).2 (H n)) (hR : ∀ n, RedT T (H n))
    (hnext : ∀ n, (W (n + 1)).1 = (W n).2)
    {u v : ℤ × ℤ} {h : BinForm} (hrep : Rep f u v h) (hRh : RedT T h)
    (h0 : |l2 f s (W 0).1| ≤ |l2 f s u|) : ∃ n, h = H n := by
  classical
  have hG : ∀ n, Good f s (W n).1 (W n).2 := fun n => S.good_of_rep (hW n) (hR n)
  have hs0 : 0 < s := lt_of_le_of_lt (by exact_mod_cast S.T_nonneg) S.T_lt
  set q : ℝ := ((T : ℝ) + 1) / s with hq_def
  have hq : 1 < q := by rw [hq_def, lt_div_iff₀ hs0]; linarith [S.lt_T]
  have hstep : ∀ n, q * |l2 f s (W n).1| ≤ |l2 f s (W (n + 1)).1| := by
    intro n
    have := S.growth (hW n) (hR n)
    rw [hnext, hq_def, div_mul_eq_mul_div, div_le_iff₀ hs0]
    linarith
  have hpow : ∀ n, q ^ n * |l2 f s (W 0).1| ≤ |l2 f s (W n).1| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc q ^ (n + 1) * |l2 f s (W 0).1| = q * (q ^ n * |l2 f s (W 0).1|) := by ring
        _ ≤ q * |l2 f s (W n).1| := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ _ := hstep n
  have hW0 : 0 < |l2 f s (W 0).1| := abs_pos.2 (hG 0).ne_zero.2.2.1
  have ex : ∃ n, |l2 f s u| < |l2 f s (W n).1| := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (|l2 f s u| / |l2 f s (W 0).1|) hq
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hW0] at hn
    exact lt_of_lt_of_le hn (hpow n)
  have hN := Nat.find_spec ex
  have hN0 : Nat.find ex ≠ 0 := by
    intro h0
    rw [h0] at hN
    linarith
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hmin := Nat.find_min ex (show m < Nat.find ex by omega)
  rw [hm, hnext] at hN
  obtain ⟨ε, hε, hu, hv⟩ := S.unique (hW m).1 hrep.1 (hG m) (S.good_of_rep hrep hRh) (not_lt.1 hmin) hN
  refine ⟨m, ?_⟩
  rw [hu, hv] at hrep
  exact rep_eq hε (hW m) hrep

end Box

theorem aniso_of_not_isSquare {F : BinForm} (hsq : ¬ IsSquare (-F.det)) (u : ℤ × ℤ) (h : qf F u = 0) :
    u = 0 := by
  have ha := (BinForm.stepInv hsq).1
  have key : F.a * qf F u = (F.a * u.1 + F.b * u.2) ^ 2 - (-F.det) * u.2 ^ 2 := by
    simp only [qf, BinForm.det]; ring
  rw [h, mul_zero] at key
  by_cases hy : u.2 = 0
  · rw [hy] at key
    have : F.a * u.1 = 0 := by nlinarith [sq_nonneg (F.a * u.1)]
    exact Prod.ext ((mul_eq_zero.1 this).resolve_left ha) hy
  · exfalso
    have hdvd : u.2 ^ 2 ∣ (F.a * u.1 + F.b * u.2) ^ 2 := ⟨-F.det, by linarith⟩
    obtain ⟨t, ht⟩ := (Int.pow_dvd_pow_iff two_ne_zero).1 hdvd
    rw [ht] at key
    apply hsq
    refine ⟨t, ?_⟩
    have : u.2 ^ 2 * (-F.det) = u.2 ^ 2 * (t * t) := by linear_combination key
    exact mul_left_cancel₀ (pow_ne_zero 2 hy) this

theorem setup_of {F : BinForm} (hd : F.det < 0) (hsq : ¬ IsSquare (-F.det)) :
    Setup F (Real.sqrt (-(F.det : ℝ))) (sqrtBound F.det : ℤ) := by
  obtain ⟨hT1, hT2⟩ := sqrtBound_facts hd hsq
  have hT0 : (0 : ℝ) ≤ ((sqrtBound F.det : ℤ) : ℝ) := by positivity
  have hD : (0 : ℝ) ≤ -(F.det : ℝ) := by
    have : (F.det : ℝ) < 0 := by exact_mod_cast hd
    linarith
  have hT1' : (((sqrtBound F.det : ℤ) : ℝ)) ^ 2 + F.det < 0 := by exact_mod_cast hT1
  have hT2' : (0 : ℝ) < (((sqrtBound F.det : ℤ) : ℝ) + 1) ^ 2 + F.det := by exact_mod_cast hT2
  refine ⟨(BinForm.stepInv hsq).1, ?_, by positivity, ?_, ?_, aniso_of_not_isSquare hsq⟩
  · rw [Real.sq_sqrt hD]; simp only [BinForm.det]; push_cast; ring
  · rw [Real.lt_sqrt hT0]; linarith
  · rw [Real.sqrt_lt' (by linarith)]; linarith

/-- **Theorem 1, "properly equivalent $\Rightarrow$ same cycle", for two forms whose sequences are reduced from the
start.** -/
theorem cycleSet_eq_of_reduced {F G : BinForm} (hd : F.det < 0) (hsq : ¬ IsSquare (-F.det))
    (hGd : G.det = F.det) (hRF : ∀ n, RedT (sqrtBound F.det : ℤ) (sequenceOf F n))
    (hRG : ∀ n, RedT (sqrtBound F.det : ℤ) (sequenceOf G n)) (h : ProperEquiv F G) :
    cycleSet F = cycleSet G := by
  have S := setup_of hd hsq
  have hsqG : ¬ IsSquare (-G.det) := hGd ▸ hsq
  -- the sequence of `F`, in its own coordinates
  have hF0 : formAt F.det (F.a, F.b) = F := sequenceOf_zero hsq
  have hG0 : formAt G.det (G.a, G.b) = G := sequenceOf_zero hsqG
  have hWF : ∀ n, Rep F (vecSeq F.det (F.a, F.b) (1, 0) (0, 1) n).1
      (vecSeq F.det (F.a, F.b) (1, 0) (0, 1) n).2 (sequenceOf F n) :=
    rep_vecSeq hsq (BinForm.stepInv hsq) (by rw [hF0]; exact rep_self F)
  -- the sequence of `G`, in the coordinates of `F`
  obtain ⟨u, v, huv⟩ := rep_of_properEquiv h
  have hWG : ∀ n, Rep F (vecSeq G.det (G.a, G.b) u v n).1 (vecSeq G.det (G.a, G.b) u v n).2
      (sequenceOf G n) :=
    rep_vecSeq hsqG (BinForm.stepInv hsqG) (by rw [hG0]; exact huv)
  rcases le_total |l2 F (Real.sqrt (-(F.det : ℝ))) (1, 0)| |l2 F (Real.sqrt (-(F.det : ℝ))) u| with hle | hle
  · obtain ⟨n, hn⟩ := S.locate hWF hRF (fun n => vecSeq_succ_fst _ _ _ _ n) huv
      (by have := hRG 0; rwa [sequenceOf_zero hsqG] at this) hle
    rw [hn, cycleSet_sequenceOf hsq]
  · obtain ⟨n, hn⟩ := S.locate hWG hRG (fun n => vecSeq_succ_fst _ _ _ _ n) (rep_self F)
      (by have := hRF 0; rwa [sequenceOf_zero hsq] at this) hle
    rw [hn, cycleSet_sequenceOf hsqG]

/-- **Theorem 1 for indefinite forms:** properly equivalent forms have the same cycle. -/
theorem cycleSet_eq_of_properEquiv_indef {f g : BinForm} (hd : f.det < 0) (hf : ¬ IsSquare (-f.det))
    (hg : ¬ IsSquare (-g.det)) (h : ProperEquiv f g) : cycleSet f = cycleSet g := by
  have hgd : g.det = f.det := h.det_eq.symm
  obtain ⟨hT1, hT2⟩ := sqrtBound_facts hd hf
  have hT0 : (0 : ℤ) ≤ (sqrtBound f.det : ℤ) := by positivity
  obtain ⟨N, hN⟩ := exists_redT hT0 hT1 hT2 hf (BinForm.stepInv hf)
  obtain ⟨M, hM⟩ := exists_redT hT0 hT1 hT2 hf (BinForm.stepInv hg |> fun h' => by rw [hgd] at h'; exact h')
  have hFd := (properEquiv_sequenceOf hf N).2
  have hGd := (properEquiv_sequenceOf hg M).2
  have hRF : ∀ n, RedT (sqrtBound (sequenceOf f N).det : ℤ) (sequenceOf (sequenceOf f N) n) := by
    intro n
    rw [hFd, sequenceOf_shift hf]
    exact hN (n + N) (by omega)
  have hRG : ∀ n, RedT (sqrtBound (sequenceOf f N).det : ℤ) (sequenceOf (sequenceOf g M) n) := by
    intro n
    rw [hFd, sequenceOf_shift hg]
    have := hM (n + M) (by omega)
    simp only [sequenceOf, formSeq] at this ⊢
    rw [hgd]
    exact this
  have e := cycleSet_eq_of_reduced (hFd ▸ hd) (hFd ▸ hf) (by rw [hFd, hGd, hgd]) hRF hRG
    (((properEquiv_sequenceOf hf N).1.symm.trans h).trans (properEquiv_sequenceOf hg M).1)
  rw [cycleSet_sequenceOf hf, cycleSet_sequenceOf hg] at e
  exact e

/-- **Theorem 1** of Conway–Sloane, Ch. 15, §3.1, p. 357, proved: for forms $f$, $g$ with $-\det$ not a square,
the sequence (5) of $f$ is ultimately periodic, and $f$, $g$ are properly equivalent if and only if they lead to the
same cycle. -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, Thm. 1, p. 357"]
theorem theorem1 : Theorem1Statement := by
  refine ⟨fun f g hf hg => ?_⟩
  have hper : UltimatelyPeriodic (sequenceOf f) := by
    rcases lt_trichotomy f.det 0 with hd | hd | hd
    · exact ultimatelyPeriodic_indef hd hf
    · exact absurd ⟨0, by rw [hd]; simp⟩ hf
    · exact ultimatelyPeriodic_def hd
  refine ⟨hper, fun h => ?_, properEquiv_of_periodic hf hg hper⟩
  rcases lt_trichotomy f.det 0 with hd | hd | hd
  · exact cycleSet_eq_of_properEquiv_indef hd hf hg h
  · exact absurd ⟨0, by rw [hd]; simp⟩ hf
  · exact cycleSet_eq_of_properEquiv_def hd h

end Binary

end ConwaySloane

end QuadFormsKB
